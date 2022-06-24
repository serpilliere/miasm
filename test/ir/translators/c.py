import pytest

from miasm.expression.expression import ExprInt, ExprOp
from miasm.expression.expression import TOK_EQUAL
from miasm.ir.translators import Translator


@pytest.fixture
def translator():
    return Translator.to_language("C")


def test_unary_to_c(translator):
    args = [ExprInt(i, 32) for i in range(9)]

    # Unary operators
    assert translator.from_expr(ExprOp('parity', *args[:1])) == r'parity(0x0&0xffffffff)'
    assert translator.from_expr(ExprOp('!', *args[:1])) == r'(~ 0x0)&0xffffffff'
    assert translator.from_expr(ExprOp('hex2bcd', *args[:1])) == r'hex2bcd_32(0x0)'
    assert translator.from_expr(ExprOp('fabs', *args[:1])) == r'fabs(0x0)'
    with pytest.raises(NotImplementedError):
        translator.from_expr(ExprOp('X', *args[:1]))


def test_binary_to_c(translator):
    args = [ExprInt(i, 32) for i in range(9)]

    # Binary operators
    assert translator.from_expr(ExprOp(TOK_EQUAL, *args[:2])) == r'(((0x0&0xffffffff) == (0x1&0xffffffff))?1:0)'
    assert translator.from_expr(ExprOp('%', *args[:2])) == r'(((0x0&0xffffffff)%(0x1&0xffffffff))&0xffffffff)'
    assert translator.from_expr(ExprOp('-', *args[:2])) == r'(((0x0&0xffffffff) - (0x1&0xffffffff))&0xffffffff)'
    assert translator.from_expr(ExprOp('cntleadzeros', *args[:1])) == r'cntleadzeros(0x0, 0x20)'
    assert translator.from_expr(ExprOp('x86_cpuid', *args[:2])) == r'x86_cpuid(0x0, 0x1)'
    assert translator.from_expr(ExprOp('fcom0', *args[:2])) == r'fcom0(0x0, 0x1)'
    assert translator.from_expr(ExprOp('fadd', *args[:2])) == r'fadd(0x0, 0x1)'
    assert translator.from_expr(ExprOp('segm', *args[:2])) == r'segm2addr(jitcpu, 0x0, 0x1)'
    assert translator.from_expr(ExprOp('imod', *args[:2])) == r'imod32((struct vm_cpu*)jitcpu->cpu, 0x0, 0x1)'
    assert translator.from_expr(ExprOp('bcdadd', *args[:2])) == r'bcdadd_32(0x0, 0x1)'
    with pytest.raises(NotImplementedError):
        translator.from_expr(ExprOp('X', *args[:2]))


def test_misc_to_c(translator):
    args = [ExprInt(i, 32) for i in range(9)]

    # Other cases
    assert translator.from_expr(ExprOp('+', *args[:3])) == r'(((0x0&0xffffffff)+(0x1&0xffffffff)+(0x2&0xffffffff))&0xffffffff)'
    with pytest.raises(NotImplementedError):
        translator.from_expr(ExprOp('X', *args[:3]))
