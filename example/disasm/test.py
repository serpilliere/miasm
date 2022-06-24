# This file contains automated tests for this module.
# You can use these tests as usage examples.
# To run these, see the 'Testing' section in the README.

import pytest
from pytest_lazyfixture import lazy_fixture


def test_callback():
    from .callback import main

    main()


def test_dis_binary(shellcode_x86_32_dis, out_path):
    from .dis_binary import disassemble

    shellcode_dis_binary, _ = shellcode_x86_32_dis
    disassemble(shellcode_dis_binary, out_path)


def test_lift(shellcode_x86_32_dis, out_path):
    from .dis_binary_lift import lift

    shellcode_dis_binary, _ = shellcode_x86_32_dis
    print("Will disassemble and lift", shellcode_dis_binary)
    lift(shellcode_dis_binary, out_path)


def test_lift_model_call(shellcode_x86_32_dis, out_path):
    from .dis_binary_lift_model_call import lift_model_call

    shellcode_dis_binary, _ = shellcode_x86_32_dis
    print("Will disassemble and lift while modeling calls", shellcode_dis_binary)
    lift_model_call(shellcode_dis_binary, output=out_path)


def test_x8_string(out_path):
    from .dis_x86_string import main

    main(out_path)


@pytest.mark.parametrize("shellcode,address,disassemble_null_starting_blocks", [
    (lazy_fixture("shellcode_demo_aarch64_b"), 0, False),
    (lazy_fixture("shellcode_demo_aarch64_l"), 0, False),
    (lazy_fixture("sample_md5_aarch64l"), 0x400A00, False),
    (lazy_fixture("shellcode_demo_arm2_b"), 0, True),
    (lazy_fixture("shellcode_demo_arm_b"), 0x2c, True),
    (lazy_fixture("shellcode_demo_arm2_l"), 0, True),
    (lazy_fixture("shellcode_demo_arm_l"), 0x2c, True),
    (lazy_fixture("shellcode_demo_armt_b"), 0x2c, True),
    (lazy_fixture("shellcode_demo_armt_l"), 0x2c, True),
    (lazy_fixture("shellcode_mips32_sc_b"), 0, False),
    (lazy_fixture("shellcode_mips32_sc_l"), 0, False),
    (lazy_fixture("shellcode_msp430_sc"), 0, False),
    (lazy_fixture("sample_md5_ppc32b"), 0x1000087C, False),
    (lazy_fixture("sample_test_i386"), "func_iret", False),
    (lazy_fixture("shellcode_x86_32_dead"), 0, False),
    (lazy_fixture("shellcode_x86_32_if_reg"), 0, False),
    (lazy_fixture("shellcode_x86_32_simple"), 0x401000, False),
    (lazy_fixture("shellcode_demo_x86_64"), 0x401000, False),
])
def test_full(shellcode, address, disassemble_null_starting_blocks, out_path):
    from .full import full

    bin, arch = shellcode
    full(bin, architecture=arch, disassemble_null_starting_blocks=disassemble_null_starting_blocks, gen_ir=True,
         simplify=True, def_use=True, ssa=True, propagate_expressions=True, address=address, output=out_path)


def test_single_instruction():
    from .single_instr import main

    main()
