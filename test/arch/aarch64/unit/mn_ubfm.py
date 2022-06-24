import pytest

from .asm_test import AsmTest


class UBFM1(AsmTest):
    TXT = '''
main:
       MOVZ    X0, 0x5600
       UBFM    X0, X0, 8, 15
       RET     LR
    '''

    def check(self):
        assert(self.myjit.cpu.X0 == 0x56)
        pass


class UBFM2(AsmTest):
    TXT = '''
main:
       MOVZ    X0, 0x56
       UBFM    X0, X0, 4, 55
       RET     LR
    '''

    def check(self):
        assert(self.myjit.cpu.X0 == 0x5)
        pass


@pytest.mark.skip("Current SIGABORTs, todo fix")
@pytest.mark.parametrize("case", [UBFM1, UBFM2])
def test(case, jitter_name):
    case(jitter_name)()
