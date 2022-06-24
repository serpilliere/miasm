import pytest

from miasm.expression.expression import ExprInt, ExprOp
from miasm.ir.translators.translator import Translator


@pytest.fixture
def translator_smt2():
    return Translator.to_language("smt2")


def test_op_strcst(translator_smt2):
    args = [ExprInt(i, 32) for i in range(9)]

    assert translator_smt2.from_expr(ExprOp('|', *args[:2])) == r'(bvor (_ bv0 32) (_ bv1 32))'
    assert translator_smt2.from_expr(ExprOp('-', *args[:2])) == r'(bvsub (_ bv0 32) (_ bv1 32))'
    assert translator_smt2.from_expr(ExprOp('+', *args[:3])) == r'(bvadd (bvadd (_ bv0 32) (_ bv1 32)) (_ bv2 32))'

    with pytest.raises(NotImplementedError):
        translator_smt2.from_expr(ExprOp('X', *args[:1]))


def test_slice_strcst(translator_smt2):
    args = [ExprInt(i, 32) for i in range(9)]

    assert translator_smt2.from_expr(args[0][1:2]) == r'((_ extract 1 1) (_ bv0 32))'

    with pytest.raises(ValueError):
        args[0].__getitem__(slice(1, 7, 2))
