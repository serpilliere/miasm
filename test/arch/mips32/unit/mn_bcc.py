import pytest

from .asm_test import AsmTest


class BCC(AsmTest):
    MYSTRING = "test string"
    TXT = '''
    main:
      ADDIU   A0, V0, mystr
strlen:
      LBU     V0, 0(A0)
      BEQ     V0, ZERO, SKIP
      ADDU    V1, ZERO, ZERO
loop:
      ADDIU   A0, A0, 1
      LBU     V0, 0(A0)
      BNE     V0, ZERO, loop
      ADDIU   V1, V1, 1
SKIP:
      JR      RA
      ADDU    V0, V1, ZERO

    mystr:
    .string "%s"
    ''' % MYSTRING

    def check(self):
        assert(self.myjit.cpu.V0 == len(self.MYSTRING))


@pytest.mark.skip("Python Abort: todo fix")
@pytest.mark.parametrize("case", [BCC])
def test(case, jitter_name):
    case(jitter_name)()
