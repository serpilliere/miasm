import os
from argparse import ArgumentParser
from miasm.jitter.csts import PAGE_READ, PAGE_WRITE
from miasm.analysis.machine import Machine
from miasm.jitter.csts import *

from pdb import pm

parser = ArgumentParser(description="x86 32 basic Jitter")
parser.add_argument("filename", help="x86 32 shellcode filename")
parser.add_argument("-j", "--jitter",
                    help="Jitter engine. Possible values are : tcc (default), llvm",
                    default="tcc")
args = parser.parse_args()

def code_sentinelle(jitter):
    jitter.run = False
    jitter.pc = 0
    return True

def exception_memory_breakpoint(jitter):
    jitter.cpu.dump_gpregs()
    print('MEMORY BP', hex(jitter.pc))
    print('READ:')
    for start, stop in jitter.vm.get_memory_read():
        print(hex(start), hex(stop))
    print('WRITE:')
    for start, stop in jitter.vm.get_memory_write():
        print(hex(start), hex(stop))

    jitter.vm.reset_memory_access()
    jitter.vm.set_exception(0)
    return True

jitter = Machine("x86_32").jitter(args.jitter)
jitter.init_stack()

data = open(args.filename, 'rb').read()
run_addr = 0x40000000
jitter.vm.add_memory_page(run_addr, PAGE_READ | PAGE_WRITE, data)

jitter.jit.log_regs = True
jitter.jit.log_mn = True
jitter.push_uint32_t(0x1337beef)

jitter.set_breakpoint(0x1337beef, code_sentinelle)



jitter.exceptions_handler.callbacks[EXCEPT_BREAKPOINT_MEMORY] = []
jitter.add_exception_handler(EXCEPT_BREAKPOINT_MEMORY,
                             exception_memory_breakpoint)
jitter.vm.add_memory_breakpoint(run_addr+0x100, 4, PAGE_READ | PAGE_WRITE)


jitter.init_run(run_addr)
jitter.continue_run()
