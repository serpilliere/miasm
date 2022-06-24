# This file contains automated tests for this module.
# You can use these tests as usage examples.
# To run these, see the 'Testing' section in the README.

import pytest
from pytest_lazyfixture import lazy_fixture

from .shellcode import shellcode_sample
from .simple import assemble


def test_shellcode_avoid_recompile():
    assert shellcode_sample("x86_32_dead.S", "x86_32", "x86_32_dead.bin", force=True)[1]
    assert not shellcode_sample("x86_32_dead.S", "x86_32", "x86_32_dead.bin", force=False)[1]


@pytest.mark.parametrize("shellcode", [
    lazy_fixture("shellcode_demo_aarch64_b"),
    lazy_fixture("shellcode_demo_aarch64_l"),
    lazy_fixture("shellcode_demo_arm_b"),
    lazy_fixture("shellcode_demo_arm_l"),
    lazy_fixture("shellcode_demo_arm2_b"),
    lazy_fixture("shellcode_demo_arm2_l"),
    lazy_fixture("shellcode_demo_armt_b"),
    lazy_fixture("shellcode_demo_armt_l"),
    lazy_fixture("shellcode_mips32_sc_b"),
    lazy_fixture("shellcode_mips32_sc_l"),
    lazy_fixture("shellcode_msp430_sc"),
    lazy_fixture("shellcode_x86_32_dis"),
    lazy_fixture("shellcode_x86_32_automod"),
    lazy_fixture("shellcode_x86_32_automod2"),
    lazy_fixture("shellcode_x86_32_dead"),
    lazy_fixture("shellcode_x86_32_enc"),
    lazy_fixture("shellcode_x86_32_if_reg"),
    lazy_fixture("shellcode_demo_x86_32"),
    lazy_fixture("shellcode_x86_32_mod"),
    lazy_fixture("shellcode_x86_32_mod_self"),
    lazy_fixture("shellcode_x86_32_pop_esp"),
    lazy_fixture("shellcode_x86_32_repmod"),
    lazy_fixture("shellcode_x86_32_seh"),
    lazy_fixture("shellcode_x86_32_simple"),
    lazy_fixture("shellcode_human"),
    lazy_fixture("shellcode_demo_x86_64"),
])
def test_shellcode_generation(shellcode):
    pass  # we're testing if PyTest can generate it successfully, if we reach this point everything went well


def test_disassemble():
    assemble()
