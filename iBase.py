'''
ARM 32-bit image base calculator
- Daniel Chong
'''
import sys
import struct
from capstone import *
from collections import OrderedDict
import binascii
import math
import numpy as np
import matplotlib.pyplot as plt
import instructions as prs
import time

FILE_NAME = ''
FILE_LENGTH = 0
IS_THUMB_MODE = 1
RELATIVE = []
MAX_INSTR_SIZE = 8
MD = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
REGISTER_NAMES = ['r0', 'r1', 'r2', 'r3', 'r4', 'r5', 'r6', 'r7', 'r8', 'r9'
        , 'r10', 'sl', 'r11', 'r12', 'r13', 'r14', 'r15', 'psr', 'lr', 'pc', 'sp', 'ip', 'sb']
NON_PC_REGS = ['r0', 'r1', 'r2', 'r3', 'r4', 'r5', 'r6', 'r7', 'r8', 'r9'
        , 'r10', 'sl', 'r11', 'r12', 'r13', 'r14', 'r15', 'psr', 'lr', 'sp', 'sb']
BRANCH_INSTRUCTIONS = {'b', 'bl', 'blx', 'bx', 'b.w', 'bl.w', 'blx.w', 'bx.w'}
CONDITIONAL_BRANCHES =  {'blgt', 'blvc', 'blcc', 'blhs', 'blmi', 'blne', 'blal',
        'blle', 'blge', 'blvs',
        'blls', 'bllt', 'bllo', 'blcs', 'blhi', 'bleq', 'blpl', 'bgt', 'bvc', 'bcc',
        'bhs', 'bmi', 'bne', 'bal', 'ble', 'bge', 'bvs', 'bls', 'blt', 'blo', 'bcs',
        'bhi', 'beq', 'bpl', 'bxgt', 'bxvc', 'bxcc', 'bxhs', 'bxmi', 'bxne', 'bxal',
        'bxle', 'bxge', 'bxvs', 'bxls', 'bxlt', 'bxlo', 'bxcs', 'bxhi', 'bxeq', 'bxpl',
        'blxgt', 'blxvc', 'blxcc', 'blxhs', 'blxmi', 'blxne', 'blxal', 'blxle', 'blxge',
        'blxvs', 'blxls', 'blxlt', 'blxlo', 'blxcs', 'blxhi', 'blxeq', 'blxpl',
        'cbz', 'cbnz', 'blgt.w', 'blvc.w', 'blcc.w', 'blhs.w', 'blmi.w', 'blne.w', 'blal.w',
        'blle.w', 'blge.w', 'blvs.w', 'blls.w', 'bllt.w', 'bllo.w', 'blcs.w', 'blhi.w', 'bleq.w',
        'blpl.w', 'bgt.w', 'bvc.w', 'bcc.w', 'bhs.w', 'bmi.w', 'bne.w', 'bal.w', 'ble.w', 'bge.w',
        'bvs.w', 'bls.w', 'blt.w', 'blo.w', 'bcs.w', 'bhi.w', 'beq.w', 'bpl.w', 'bxgt.w', 'bxvc.w',
        'bxcc.w', 'bxhs.w', 'bxmi.w', 'bxne.w', 'bxal.w', 'bxle.w', 'bxge.w', 'bxvs.w', 'bxls.w',
        'bxlt.w', 'bxlo.w', 'bxcs.w', 'bxhi.w', 'bxeq.w', 'bxpl.w', 'blxgt.w', 'blxvc.w', 'blxcc.w',
        'blxhs.w', 'blxmi.w', 'blxne.w', 'blxal.w', 'blxle.w', 'blxge.w', 'blxvs.w', 'blxls.w',
        'blxlt.w', 'blxlo.w', 'blxcs.w', 'blxhi.w', 'blxeq.w', 'blxpl.w', 'cbz.w', 'cbnz.w'}

#Record the location of branch instructions in the binary
BRANCHES = {}
MEM_INSTR = []
STARTING_ADDRESS = ''
HEX_DATA = ''
ISR_POINTERS = []

# Takes a hex representation and returns an int
def endian_switch(val):
    tmp = "0x" + val[6] + val[7] + val[4] + val[5] + val[2] + val[3] + val[0] + val[1]
    return(int(tmp,16))

class instr_data(object):
    def __init__(self, instr, op):
        self.instr = instr
        self.op = op

class DisassemblerCore(object):
    def __init__(self, filename):
        global MEM_INSTR
        global BRANCHES
        self.filename = filename
        self.file_data = b''
        self.starting_address = ''
        self.beginning_code = ''
        self.stack_top = ''
        self.isr_num = 0
        self.isr_table_length = 0
        ISR_POINTERS = []
        self.curr_mnemonic = ''
        self.curr_op_str = ''
        self.done = False
        #Keep track of the size of the instruction (can be determined by Capstone)
        self.size = 0
        self.subroutine_branch = []

    def run(self):
        self.load_file()
        for i in range(len(self.file_data)):
            MEM_INSTR.append(0)
        self.disassemble()
        disassembled_instrs = 0
        for i in range(len(MEM_INSTR)):
            if MEM_INSTR[i] != 0:
                disassembled_instrs += 1
        return True

    def load_file(self):
        global HEX_DATA, STARTING_ADDRESS, FILE_LENGTH
        with open(self.filename, 'rb') as f:
            self.file_data = f.read()
        f.close()
        FILE_LENGTH = len(self.file_data)
        HEX_DATA = binascii.hexlify(self.file_data)
        # Stack top stored in first word, starting address in second
        self.stack_top = endian_switch(HEX_DATA[0:8])
        self.starting_address = endian_switch(HEX_DATA[8:16])
        print hex(self.starting_address)
        STARTING_ADDRESS = self.starting_address
        if self.starting_address % 2 != 0:
            IS_THUMB_MODE = 1
        else:
            IS_THUMB_MODE = 0
        index = 16
        while (True):
            address = endian_switch(HEX_DATA[index:index+8])
            index += 8
            if address != 0:
                if ((address % 2 == 0) or
                        (address > self.starting_address + len(self.file_data)) or
                        (address < self.starting_address - len(self.file_data))):
                    #Weird offset because of "index+=8" and self.beginning_code-thumb_mode
                    self.beginning_code = (index-8)/2 + 1
                    break;
            if(address != 0):
                self.isr_num += 1
            if (address != 0) and (address not in ISR_POINTERS):
                ISR_POINTERS.append(address)
            self.isr_table_length += 1

    #Disassemble ONE instruction
    def dasm_single(self, md, code, addr):
        #Keep track of the number of instructions disassembled
        count = 0
        for(address, size, mnemonic, op_str) in md.disasm_lite(code,
                addr):
            count += 1
            self.curr_mnemonic = str(mnemonic)
            self.curr_op_str = str(op_str)
            instr = self.curr_mnemonic + '\t' + self.curr_op_str
            MEM_INSTR[address] = instr_data(self.curr_mnemonic, self.curr_op_str)
            if self.curr_mnemonic in BRANCH_INSTRUCTIONS or self.curr_mnemonic in CONDITIONAL_BRANCHES:
                if self.curr_op_str not in REGISTER_NAMES:
                    RELATIVE.append(int(self.curr_op_str.split('#')[1],16))
        '''dasm_single is given 4 bytes. If Capstone is only able to disassemble 1 2-byte instruction,
           the second 2 bytes of the 4 belong to the next instruction.'''
        if count == 1 and size == 2:
            return False
        else:
            return True

    # https://www.capstone-engine.org/lang_python.html
    def disassemble(self):
        start = (self.beginning_code - 1) * 2
        self.curr_instr = start
        self.curr_addr = self.beginning_code - IS_THUMB_MODE  #offset for thumb
        # Section of code to be disassembled
        code = HEX_DATA[self.curr_instr:self.curr_instr+MAX_INSTR_SIZE].decode('hex')
        prev_addr = 0
        while(self.curr_instr+MAX_INSTR_SIZE < len(HEX_DATA)):
            if self.dasm_single(MD, code, self.curr_addr):
                self.curr_instr += MAX_INSTR_SIZE
                self.curr_addr += 4
            else:
                self.curr_instr += MAX_INSTR_SIZE/2
                self.curr_addr += 2
            code = HEX_DATA[self.curr_instr:self.curr_instr+MAX_INSTR_SIZE].decode('hex')

def stat_filter(data_set):
    front_half = 0
    back_half = 0
    data_set.sort()    
    if len(data_set)%2 == 0:    
        front_half = len(data_set)/2    
        back_half = len(data_set)/2    
    else:    
        front_half = int(float(len(data_set))/2-0.5)    
        back_half = int(float(len(data_set))/2+0.5)    
    Q1 = np.median(data_set[:front_half])    
    Q3 = np.median(data_set[back_half:])    
    IQR = Q3 - Q1    
    upper_limit = Q3 + IQR * 1.5    
    lower_limit = Q1 - IQR * 1.5    

    high = 0
    low = 0

    while(min(data_set) < lower_limit):
        data_set.remove(min(data_set))
        low += 1 
        if len(data_set) == 0:
            break
    while(max(data_set) > upper_limit):
        data_set.remove(max(data_set))
        high += 1
        if len(data_set) == 0:
            break
    if high == 0 and low == 0:
        return True
    else:
        return False

def struc_filter(min_imagebase, max_imagebase):
    potential_bases = []
    test_base = min_imagebase
    while test_base < max_imagebase + 1024:
        bad_base = False
        for i in ISR_POINTERS:
            if i-test_base-1 >= len(MEM_INSTR) or i-test_base-1 < 0:
                bad_base = True
                break
            if MEM_INSTR[i-test_base-1] == 0:
                bad_base = True
                break
        if bad_base == False:
            potential_bases.append(test_base)
        test_base += 1024
    print 'struc filter ', len(potential_bases), potential_bases
    return potential_bases

def find_imagebase(data_set, confirmed_addrs):
    test_imagebase = 0x00000
    iteration = 0
    page_size = 1024
    min_imagebase = (min(confirmed_addrs) - FILE_LENGTH) & ~(page_size-1)
    if min_imagebase < 0:
        min_imagebase = 0
    iteration = min_imagebase/page_size
    max_imagebase = min(confirmed_addrs) & ~(page_size-1)
    tmp = [i - page_size*iteration for i in confirmed_addrs]
    result = ''
    result = stat_filter(tmp+data_set)
    print('range', hex(min_imagebase), hex(max_imagebase))
    while result != True:
        iteration += 1
        print(iteration)
        tmp = [i - page_size*iteration for i in confirmed_addrs]
        result = stat_filter(tmp+data_set)
    print('stat filter', (max_imagebase-min_imagebase)/1024, hex(min_imagebase), hex(max_imagebase), iteration)
    min_imagebase = iteration*page_size
    return struc_filter(min_imagebase, max_imagebase)

def sem_filter(base, ABSOLUTE):
    for j in ABSOLUTE:
        addr = j-base-1
        instr = prs.Instruction(prs.Mnemonic(MEM_INSTR[addr].instr),prs.Operands(MEM_INSTR[addr].op))
        mnemonic_type = instr.mnemonic.mnemonic_type
        op_list = instr.operands._list
        mnemonic_name = str(instr.mnemonic.name)
        if mnemonic_type == mnemonic_type.ARITHMETIC: #Arithmetic
            if op_list[1] in NON_PC_REGS:
                #print 'arithmetic'
                return False
            if len(op_list) > 2:
                if op_list[2] in NON_PC_REGS:
                    return False
        elif mnemonic_type == mnemonic_type.COMPARISON: #Comparison
            for i in op_list:
                if i in NON_PC_REGS:
                    #print 'comp'
                    return False
        elif mnemonic_type == mnemonic_type.BRANCH: #Branch
            if MEM_INSTR[addr].instr in CONDITIONAL_BRANCHES:
                print 'bran'
                return False
            for i in op_list:
                if i in REGISTER_NAMES:
                    #print 'bran'
                    return False
        elif mnemonic_type == mnemonic_type.MODIFY: #Modify
            #special case
            if 'mov' in mnemonic_name and (op_list[1] in NON_PC_REGS):
                #print 'mod'
                return False
            #op_list[1] contains the arguments for the address to load from
            if 'ldr' in mnemonic_name or 'ls' in mnemonic_name or 'eor' in mnemonic_name:
                if op_list[1] in NON_PC_REGS:
                    #print 'mod'
                    return False
        elif mnemonic_type == mnemonic_type.LOAD_STORE: #Load/Store
            #special case
            if 'str' in mnemonic_name and str(op_list[1]).replace('[','').replace(']','').replace('\'','') in NON_PC_REGS:
                #print 'load/store'
                return False
        elif mnemonic_type == mnemonic_type.STACK_CONTROL: #Stack control
            #special case
            if mnemonic_name == 'pop':
                #print 'stack'
                return False
    return True

#0x40000000 is the max number where code can be stored
# Main
def main():
    tmp = False
    if len(sys.argv) > 1:
        FILE_NAME = str(sys.argv[1])
        with open('startup.txt', 'w') as f:
            f.write(FILE_NAME)
            f.close()
    else:
        with open('startup.txt', 'r') as f:
            FILE_NAME = f.readline()
            f.close()
        if len(FILE_NAME) == 0:
            print('No file found')
            return True
    dc = DisassemblerCore(FILE_NAME)
    dc.run()


    RELATIVE.sort()
    stat_filter(RELATIVE)
    ABSOLUTE = ISR_POINTERS 
    ABSOLUTE.append(STARTING_ADDRESS)
    print 'Absolute ' + str(len(ABSOLUTE))
    print 'Relative ' + str(len(RELATIVE))
    potential_bases = find_imagebase(RELATIVE, ABSOLUTE)
    print 'Potential bases'
    for i in potential_bases:
        print hex(i)

    filtered = []
    for i in potential_bases:
        if sem_filter(i, ABSOLUTE) == True:
            filtered.append(i)

    print '\n\nFINAL:'
    for i in filtered:
        print hex(i), MEM_INSTR[STARTING_ADDRESS-i-1].instr, MEM_INSTR[STARTING_ADDRESS-i-1].op

if __name__ == '__main__':
    startTime = time.time()
    main()
    print('Execution time in seconds: ' + str(time.time()-startTime))
