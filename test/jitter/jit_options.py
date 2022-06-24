from __future__ import print_function

import pytest

from miasm.analysis.machine import Machine
from miasm.core.locationdb import LocationDB
from miasm.core.utils import decode_hex
from miasm.jitter.csts import PAGE_READ, PAGE_WRITE

# Shellcode
# main:
#       MOV    EAX, 0x10
#       MOV    EBX, 0x1
# loop_main:
#       SUB    EAX, 0x1
#       CMOVZ  ECX, EBX
#       JNZ    loop_main
# loop_end:
#       RET


data = decode_hex("b810000000bb0100000083e8010f44cb75f8c3")
run_addr = 0x40000000
loc_db = LocationDB()


def code_sentinelle(jitter):
    jitter.running = False
    jitter.pc = 0
    return True


def init_jitter(loc_db, jitter_name):
    global data, run_addr
    # Create jitter
    myjit = Machine("x86_32").jitter(loc_db, jitter_name)

    myjit.vm.add_memory_page(run_addr, PAGE_READ | PAGE_WRITE, data)

    # Init jitter
    myjit.init_stack()
    myjit.set_trace_log()
    myjit.push_uint32_t(0x1337beef)

    myjit.add_breakpoint(0x1337beef, code_sentinelle)
    return myjit


def test_max_exec_per_call(jitter_name):
    # Test 'max_exec_per_call'
    print("First run, to jit blocks")
    myjit = init_jitter(loc_db, jitter_name)
    myjit.init_run(run_addr)
    myjit.continue_run()

    assert myjit.running is False
    assert myjit.cpu.EAX == 0x0

    # Let's specify a max_exec_per_call
    # 5: main/loop_main, loop_main
    myjit.jit.options["max_exec_per_call"] = 5

    myjit.first_call = True

    def cb(jitter):
        if jitter.first_call:
            # Avoid breaking on the first pass (before any execution)
            jitter.first_call = False
            return True
        return False

    # Second run
    print("Second run")
    myjit.push_uint32_t(0x1337beef)
    myjit.cpu.EAX = 0
    myjit.init_run(run_addr)
    myjit.exec_cb = cb
    myjit.continue_run()

    assert myjit.running is True
    # Use a '>=' because it's a 'max_...'
    assert myjit.cpu.EAX >= 0xA


def test_maxline(jitter_name):
    # Test 'jit_maxline'
    print("Run instr one by one")
    myjit = init_jitter(loc_db, jitter_name)
    myjit.jit.options["jit_maxline"] = 1
    myjit.jit.options["max_exec_per_call"] = 1

    myjit.counter = 0

    def cb(jitter):
        jitter.counter += 1
        return True

    myjit.init_run(run_addr)
    myjit.exec_cb = cb
    myjit.continue_run()

    assert myjit.running is False
    assert myjit.cpu.EAX == 0x00
    # main(2) + (loop_main(3))*(0x10) + loop_end(1) + 0x1337beef (1)
    assert myjit.counter == 52
