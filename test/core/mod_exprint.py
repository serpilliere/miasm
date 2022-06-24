from miasm.expression.expression import ExprInt


def test_regular():
    a = ExprInt(5, 3)
    assert int(a) == 0x5

    b = ExprInt(2, 3)
    assert int(b) == 0x2


def test_too_small():
    c = ExprInt(-1, 3)
    assert int(c) == 0x7

    d = ExprInt(-4, 3)
    assert int(d) == 0x4


def test_too_big():
    e = ExprInt(9, 3)
    assert int(e) == 0x1


def test_zero():
    f = ExprInt(0, 64)
    assert int(f) == 0
