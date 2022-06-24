import sys

import pytest

from .asm_test import Asm_Test_32


class Test_CPUID(Asm_Test_32):
    """Check for cpuid support (and not for arbitrary returned values)"""
    TXT = '''
    main:
       XOR EAX, EAX
       CPUID
       RET
    '''

    def check(self):
        assert self.myjit.cpu.EAX == 0xa


@pytest.mark.parametrize("case", [Test_CPUID])
def test(case, jitter_name):
    case(jitter_name)
