import pytest

from miasm.expression.expression import *
from miasm.ir.ir import AssignBlock
from miasm.expression.simplifications import expr_simp

id_a = ExprId("a", 32)
id_b = ExprId("b", 32)
int0 = ExprInt(0, id_a.size)


def test_assignblock_equality():
    assignblk1 = AssignBlock([ExprAssign(id_a, id_b)])
    assignblk2 = AssignBlock({id_a: id_b})
    assignblk1_bis = AssignBlock([ExprAssign(id_a, id_b)])
    assert assignblk1 == assignblk1_bis
    assert assignblk1 == assignblk2


def test_assignblock_immutable():
    assignblk1 = AssignBlock([ExprAssign(id_a, id_b)])

    with pytest.raises(Exception):
        assignblk1[id_a] = id_a

    with pytest.raises(Exception):
        del assignblk1[id_a]


def test_assignblock_apis():
    assignblk1 = AssignBlock([ExprAssign(id_a, id_b)])
    print(assignblk1)

    assert assignblk1.get_r() == {id_b}
    assert assignblk1.get_w() == {id_a}
    assert assignblk1.get_rw() == {id_a: {id_b}}
    assert list(assignblk1) == [id_a]
    assert dict(assignblk1) == {id_a: id_b}
    assert assignblk1[id_a] == id_b
    assert list(viewitems(assignblk1)) == list(viewitems(assignblk1))
    assert set(assignblk1.items().__iter__()) == set(assignblk1.items())


def test_assignblock_simplify():
    assignblk3 = AssignBlock({id_a: id_b - id_b})
    assert assignblk3[id_a] != int0
    assignblk4 = assignblk3.simplify(expr_simp.to_new_visitor())
    assert assignblk3[id_a] != int0
    assert assignblk4[id_a] == int0
