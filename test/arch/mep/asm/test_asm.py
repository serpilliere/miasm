# Toshiba MeP-c4 - Misc unit tests
# Guillaume Valadon <guillaume@valadon.net>

from __future__ import print_function

import pytest

from miasm.core.utils import decode_hex, encode_hex
from miasm.arch.mep.arch import mn_mep


@pytest.mark.parametrize("mn_str,mn_hex", [
    ("ADD R1, 2", "6108"),
    ("JMP 0xC3FA38", "d9c8c3fa"),
    ("SLT3 R0, R8, R10", "08a2"),
    ("SB R9, (R4)", "0948"),
    ("SSARB 3(GP)", "13ec"),
    ("SWCPI C13, (R2+)", "3d20"),
    ("ADD3 R2, SP, 0x1C", "421c"),
    ("SW R7, 0x50(SP)", "4752")
])
def test(mn_str, mn_hex):
    # Disassemble
    mn_bin = decode_hex(mn_hex)
    mn = mn_mep.dis(mn_bin, "b")

    print("dis: %s -> %s" % (mn_hex.rjust(20), str(mn).rjust(20)))
    assert (str(mn) == mn_str)  # disassemble assertion

    # Assemble and return all possible candidates
    instr = mn_mep.fromstring(str(mn), "b")
    instr.mode = "b"
    asm_list = [encode_hex(i).decode() for i in mn_mep.asm(instr)]

    # Print the results
    print("asm: %s -> %s" % (
        mn_str.rjust(20),
        ", ".join(asm_list).rjust(20))
          )
    assert (mn_hex in asm_list)  # assemble assertion
