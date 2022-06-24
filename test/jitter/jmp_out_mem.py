import pytest

from miasm.core.utils import decode_hex
from miasm.jitter.csts import PAGE_READ, PAGE_WRITE, EXCEPT_ACCESS_VIOL
from miasm.analysis.machine import Machine
from miasm.core.locationdb import LocationDB


def code_sentinelle(jitter):
    jitter.running = False
    jitter.pc = 0
    return True


def test(jitter_name):
    machine = Machine("x86_32")
    loc_db = LocationDB()
    jitter = machine.jitter(loc_db, jitter_name)

    jitter.init_stack()

    # nop
    # mov eax, 0x42
    # jmp 0x20

    data = decode_hex("90b842000000eb20")

    # Will raise memory error at 0x40000028

    jitter.error_raised = False

    def raise_me(jitter):
        jitter.error_raised = True
        assert jitter.pc == 0x40000028
        return False

    jitter.add_exception_handler(EXCEPT_ACCESS_VIOL, raise_me)

    run_addr = 0x40000000

    jitter.vm.add_memory_page(run_addr, PAGE_READ | PAGE_WRITE, data)

    jitter.set_trace_log()
    jitter.push_uint32_t(0x1337beef)

    jitter.add_breakpoint(0x1337beef, code_sentinelle)

    jitter.init_run(run_addr)
    jitter.continue_run()

    assert jitter.error_raised is True
