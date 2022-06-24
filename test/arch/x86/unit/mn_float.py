import pytest

from .asm_test import Asm_Test_32


class Test_FADD(Asm_Test_32):
    TXT = '''
    main:
       ; test float
       PUSH 0
       FLD1
       FLD1
       FADD ST, ST(1)
       FIST  DWORD PTR [ESP]
       POP  EAX
       RET
    '''
    def check(self):
        assert(self.myjit.cpu.EAX == 2)


@pytest.mark.parametrize("case", [Test_FADD])
def test(case, jitter_name):
    case(jitter_name)
