from miasm.core.interval import *
from random import randint

i1 = interval([(1, 3)])
i2 = interval([(2, 5)])
i3 = interval([(3, 5)])
i4 = interval([(5, 8)])

i5 = interval([(1, 5)])
i6 = interval([(1, 3), (5, 8)])
i7 = interval([(2, 8)])
i8 = interval([(1, 8)])
i9 = interval([(4, 5)])

i10 = interval([(1, 1)])
i11 = interval([(1, 2)])
i12 = interval([(2, 2)])
i13 = interval([(2, 4)])
i14 = interval([(0, 1), (3, 5), (7, 10)])
i15 = interval([(0, 12)])
i16 = interval([(2, 8)])

i_empty = interval()


def test_empty_interval_repr():
    assert(repr(i_empty) == '[]')


def test_interval_constructor_returns_self():
    assert(interval(i1) == i1)


def test_cannon():
    i1.cannon()
    i1.cannon()


def test_compare():
    assert(cmp_interval(i1.intervals[0], i2.intervals[0]) == INT_JOIN)
    assert(cmp_interval(i1.intervals[0], i3.intervals[0]) == INT_JOIN)
    assert(cmp_interval(i1.intervals[0], i4.intervals[0]) == INT_DISJOIN)
    assert(cmp_interval(i2.intervals[0], i3.intervals[0]) == INT_B_IN_A)
    assert(cmp_interval(i3.intervals[0], i2.intervals[0]) == INT_A_IN_B)
    assert(cmp_interval(i1.intervals[0], i1.intervals[0]) == INT_EQ)
    assert(cmp_interval(i1.intervals[0], i9.intervals[0]) == INT_JOIN_AB)
    assert(cmp_interval(i9.intervals[0], i1.intervals[0]) == INT_JOIN_BA)


def test_contains():
    assert((i1 in i2) is False)
    assert((i2 in i1) is False)
    assert((i1 in i3) is False)
    assert((i2 in i3) is False)

    assert(i3 in i2)
    assert((i2 in i3) is False)
    assert(i3 in i14)


def test_canon_list_of_canonized_interval():
    assert(interval.cannon_list(i1.intervals) == i1.intervals)


def test_sum():
    assert(i1 + i2 == i5)
    assert(i1 + i3 == i5)
    assert(i1 + i4 == i6)

    assert(i2 + i3 == i2)
    assert(i2 + i4 == i7)
    assert(i1 + i2 + i4 == i8)


def test_diff():
    assert(i1 - i2 == i10)
    assert(i1 - i3 == i11)
    assert(i1 - i4 == i1)
    assert(i2 - i3 == i12)
    assert(i2 - i4 == i13)
    assert(i8 - i1 == interval([(4, 8)]))
    assert(i8 - i2 == interval([(1, 1), (6, 8)]))

    assert(i10 + i12 == i11)
    assert(i1 - i1 == interval())
    assert(i6 - i6 == interval())
    assert(i6 - i6 - i1 == interval())
    assert(i1 - i10 == interval([(2, 3)]))


def test_and():
    assert(i1 & i1 == i1)
    assert(i1 & i2 == interval([(2, 3)]))
    assert(i1 & i3 == interval([(3, 3)]))
    assert(i3 & i1 == interval([(3, 3)]))
    assert(i1 & i4 == interval([]))
    assert(i4 & i1 == interval([]))
    assert(i1 & i5 == i1)
    assert(i5 & i1 == i1)
    assert(i1 & i6 == i1)
    assert(i5 & i13 == i13)
    assert(i6 & i6 == i6)
    assert(i14 & i15 == i14)
    assert(i15 & i14 == i14)
    assert(i14 & i16 == interval([(3, 5), (7, 8)]))


def test_length():
    assert(i5.length == 5)
    assert(i6.length == 7)
    assert((i1 - i1).length == 0)


def test_equality():
    x1 = [(7, 87), (76, 143), (94, 129), (79, 89), (46, 100)]
    assert(interval(x1) == interval([(7, 143)]))

    x2 = [(11, 16), (35, 74), (18, 114), (91, 188), (3, 75)]
    assert(interval(x2) == interval([(3, 188)]))


def test_hull():
    i1.hull()
    i1.show(dry_run=True)

    assert(i_empty.hull() == (None, None))


def gen_random_interval(l=100):
    r = []
    for j in range(5):
        a = randint(0, l)
        b = a + randint(0, l)
        r.append((a, b))
    return r


def check_add(r1, r2):
    i_sum = interval(r1) + interval(r2)
    for a, b in r1 + r2:
        for i in range(a, b + 1):
            assert(i in i_sum)


def check_sub(r1, r2):
    i1 = interval(r1)
    i2 = interval(r2)
    i_sub = i1 - i2
    for a, b in r1:
        for i in range(a, b + 1):
            if i in i2:
                assert(i not in i_sub)
            else:
                assert(i in i_sub)


def check_and(r1, r2):
    i1 = interval(r1)
    i2 = interval(r2)
    i_and = i1 & i2
    for a, b in r1:
        for i in range(a, b + 1):
            if i in i2:
                assert(i in i_and)
            else:
                assert(i not in i_and)


def test_probabilist():
    for i in range(1000):
        r1 = gen_random_interval()
        r2 = gen_random_interval()
        r3 = gen_random_interval()

        check_add(r1, r2)
        check_sub(r1, r2)
        check_and(r1, r2)

        a = interval(r1)
        b = interval(r2)
        c = interval(r3)
        assert((a & b) - c == a & (b - c) == (a - c) & (b - c))
        assert(a - (b & c) == (a - b) + (a - c))
