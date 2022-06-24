import pytest

from miasm.expression.expression import ExprInt, ExprId, ExprSlice, ExprMem, \
    ExprCond, ExprCompose, ExprAssign, ExprLoc, LocKey
from miasm.expression.parser import str_to_expr


@pytest.mark.parametrize("expr", [
    ExprInt(0x12, 32),
    ExprId('test', 32),
    ExprLoc(LocKey(12), 32),
    ExprSlice(ExprInt(0x10, 32), 0, 8),
    ExprMem(ExprInt(0x10, 32), 32),
    ExprCond(ExprInt(0x10, 32), ExprInt(0x11, 32), ExprInt(0x12, 32)),
    ExprCompose(ExprInt(0x10, 16), ExprInt(0x11, 8), ExprInt(0x12, 8)),
    ExprInt(0x11, 8) + ExprInt(0x12, 8),
    ExprAssign(ExprId('EAX', 32), ExprInt(0x12, 32)),
])
def test(expr):
    print(expr)
    assert str_to_expr(repr(expr)) == expr
