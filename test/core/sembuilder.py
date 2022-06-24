from miasm.core.sembuilder import SemBuilder
from miasm.core.locationdb import LocationDB
from miasm.expression.expression import *
import miasm.expression.expression as m2


# Test classes
class IR(object):
    def __init__(self, loc_db):
        self.loc_db = loc_db

    IRDst = ExprId("IRDst", 32)

    def get_next_instr(self, _):
        return LocKey(0)

    def get_next_loc_key(self, _):
        return LocKey(0)


class Instr(object):
    mode = 32


# Test
sb = SemBuilder(m2.__dict__)


@sb.parse
def check(Arg1, Arg2, Arg3):
    """Test docstring"""
    Arg1 = Arg2
    value1 = Arg2
    value2 = Arg3 + i32(4) - ExprMem(Arg1, 32)
    Arg3 = Arg3 if Arg2 + value1 else i32(0) + value2
    tmpvar = 'myop'(i32(2))
    Arg2 = ('myopsize%d' % Arg1.size)(tmpvar, Arg1)
    alias = Arg1[:24]

    if not Arg1:
        Arg2 = Arg3
    else:
        alias = {i16(4), i8(5)}


def test():
    a = ExprId('A', 32)
    b = ExprId('B', 32)
    c = ExprId('C', 32)
    loc_db = LocationDB()
    ir = IR(loc_db)
    res = check(ir, "dummy instruction", a, b, c)

    print("Returned:")
    print(res)
    print("DocString:", check.__doc__)

    print("Cur instr:")
    for statement in res[0]:
        print(statement)

    print("Blocks:")
    for irb in res[1]:
        print(irb.loc_key)
        for assignblk in irb:
            for expr in assignblk:
                print(expr)
            print()
