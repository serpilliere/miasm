from __future__ import print_function

import json
import os.path
import subprocess
import sys

import pytest

from ..examples.asm.shellcode import shellcode_sample
from ..examples.symbol_exec.depgraph import depgraph

# This file tests the 'depgraph' example

if __name__ == '__main__':
    expected_file = sys.argv[1]
    dg = subprocess.Popen([sys.executable] + sys.argv[2:], stdout=subprocess.PIPE)

    stdout, _ = dg.communicate()
    expected = json.load(open(expected_file))
    result = json.loads(stdout.decode())

    assert len(expected) == len(result)

    assert all(r in result for r in expected)
    assert all(r in expected for r in result)


@pytest.mark.parametrize("implicit", [True, False])
@pytest.mark.parametrize("test_nb,target_addr,elements", [
    ("00", "0x40100d", ["EAX"]),
    ("01", "0x401011", ["EAX"]),
    ("02", "0x401018", ["EAX"]),
    ("03", "0x401011", ["EAX"]),
    ("04", "0x401011", ["EAX"]),
    ("05", "0x401016", ["EAX"]),
    ("06", "0x401017", ["EAX"]),
    ("07", "0x401012", ["EAX", "ECX"]),
    ("08", "0x401012", ["ECX"]),
    ("09", "0x40101f", ["EAX", "EBX"]),
    ("10", "0x401025", ["EAX", "EBX"]),
    ("11", "0x401007", ["EBX"]),
])
def test(test_nb, target_addr, elements, implicit):
    architecture = "x86_32"
    func_addr = "0x401000"

    path = os.path.abspath(os.path.dirname(__file__))
    input_file = os.path.join(path, "../examples/samples/" + architecture + "/dg_test_" + test_nb + ".bin")
    json_expected = os.path.join(path, "dg_test_" + test_nb + "_expected.json") if not implicit else os.path.join(path, "dg_test_" + test_nb + "_implicit_expected.json")

    shellcode_sample(architecture + "/dg_test_" + test_nb + ".S", architecture,
                     architecture + "/dg_test_" + test_nb + ".bin", generate_pe=True)

    result = depgraph(input_file, architecture, elements, func_addr, target_addr, implicit=implicit, generate_json=True)

    expected = json.load(open(json_expected))

    assert len(expected) == len(result)
    assert all(r in result for r in expected)
    assert all(r in expected for r in result)
