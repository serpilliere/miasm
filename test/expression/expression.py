import pytest

from miasm.expression.expression import *
from miasm.expression.expression_helper import *


def test_cmp():
    # Expression comparison
    assert (-ExprInt(1, 64) != -ExprInt(2, 64))
    assert (ExprInt(1, 64) != ExprInt(1, 32))


def test_size():
    # Expression size
    big_cst = ExprInt(1, size=0x1000)
    assert big_cst.size == 0x1000


# Common constants
A = ExprId("A", 32)
B = ExprId("B", 32)
cond1 = ExprId("cond1", 1)
cond2 = ExprId("cond2", 16)
cst1 = ExprInt(1, 32)
cst2 = ExprInt(2, 32)
cst3 = ExprInt(3, 32)
cst4 = ExprInt(4, 32)


@pytest.mark.parametrize("expr", [
    cst1,
    A,
    ExprMem(cst1, 32),
    ExprCond(cond1, cst1, cst2),
    ExprMem(ExprCond(cond1, cst1, cst2), 16),
    ExprCond(cond1,
             ExprCond(cond2, cst3, cst4),
             cst2),
    A + cst1,
    A + ExprCond(cond1, cst1, cst2),
    ExprCond(cond1, cst1, cst2) + ExprCond(cond2, cst3, cst4),
    ExprCompose(A, cst1),
    ExprCompose(ExprCond(cond1, cst1, cst2), A),
    ExprCompose(ExprCond(cond1, cst1, cst2),
                ExprCond(cond2, cst3, cst4)),
    ExprCond(ExprCond(cond1, cst1, cst2), cst3, cst4),
])
def test_possible_values(expr):
    print("*" * 80)
    print(expr)
    sol = possible_values(expr)
    print(sol)
    print("Resulting constraints:")
    for consval in sol:
        print("For value %s" % consval.value)
        for constraint in consval.constraints:
            print("\t%s" % constraint.to_constraint())


@pytest.mark.parametrize("expr", [
    cst1,
    A,
    ExprMem(cst1, 32),
    ExprCond(cond1, cst1, cst2),
    A + cst1,
    ExprCompose(A, cst1),
    A.msb,
    ExprAssign(A, cst1),
])
def test_repr(expr):
    print(repr(expr))
    assert eval(repr(expr)) == expr


def test_assign():
    aff = ExprAssign(A[0:32], cst1)
    assert aff.dst == A[0:32]
    assert aff.src == cst1


def test_mem():
    mem = ExprMem(A, 32)
    assert mem.get_r() == {mem}
    assert mem.get_r(mem_read=True) == {mem, A}


def test_contains():
    C = A + B
    D = C + A

    assert A in A
    assert A in C
    assert B in C
    assert C in C

    assert A in D
    assert B in D
    assert C in D
    assert D in D

    assert C not in A
    assert C not in B

    assert D not in A
    assert D not in B
    assert D not in C


def test_read_write():
    C = A + B
    D = C + A

    assert cst1.get_r(cst_read=True) == {cst1}
    mem1 = ExprMem(A, 32)
    mem2 = ExprMem(mem1 + B, 32)
    assert mem2.get_r() == {mem2}

    assign1 = ExprAssign(A, cst1)
    assert assign1.get_r() == set([])

    assign2 = ExprAssign(mem1, D)
    assert assign2.get_r() == {A, B}
    assert assign2.get_r(mem_read=True) == {A, B}
    assert assign2.get_w() == {mem1}

    assign3 = ExprAssign(mem1, mem2)
    assert assign3.get_r() == {mem2}
    assert assign3.get_r(mem_read=True) == {mem1, mem2, A, B}
    assert assign3.get_w() == {mem1}
