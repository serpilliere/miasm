# This file contains automated tests for this module.
# You can use these tests as usage examples.
# To run these, see the 'Testing' section in the README.

import pytest
from pytest_lazyfixture import lazy_fixture


@pytest.mark.parametrize("shellcode,variant", [
    (lazy_fixture("shellcode_demo_arm_b"), 'b'),
    (lazy_fixture("shellcode_demo_arm_l"), 'l')
])
def test_asm_sc(shellcode, variant, jitter_name):
    from .arm_sc import arm

    bin_path, _ = shellcode
    arm(["0", bin_path, variant, "-a", "0", "--jitter", jitter_name])


@pytest.mark.parametrize("sample", [
    lazy_fixture("shellcode_x86_32_automod"),
    lazy_fixture("shellcode_x86_32_automod2"),
    lazy_fixture("shellcode_x86_32_enc"),
    lazy_fixture("shellcode_x86_32_mod"),
    lazy_fixture("shellcode_x86_32_mod_self"),
    lazy_fixture("shellcode_x86_32_pop_esp"),
    lazy_fixture("shellcode_x86_32_repmod"),
    lazy_fixture("shellcode_x86_32_simple")
])
def test_sandbox_pe_x86_32(sample, jitter_name):
    from .sandbox_pe_x86_32 import parser, main

    path, _ = sample
    main(parser.parse_args([path, "--jitter", jitter_name]))
