# This test demonstrates how to check for possible memory interferences.
# See the 'Testing' section in the README to execute it.

import pytest

from miasm.analysis.data_flow import State
from miasm.expression.expression import *

a32 = ExprId('a', 32)
b32 = ExprId('b', 32)

a64 = ExprId('a', 64)
b64 = ExprId('b', 64)

mem_a32_32 = ExprMem(a32, 32)
mem_b32_32 = ExprMem(b32, 32)

mem_a64_32 = ExprMem(a64, 32)

mem_a32_m1_8 = ExprMem(a32 + ExprInt(-1, 32), 8)
mem_a32_p0_8 = ExprMem(a32, 8)
mem_a32_p1_8 = ExprMem(a32 + ExprInt(1, 32), 8)
mem_a32_p2_8 = ExprMem(a32 + ExprInt(2, 32), 8)
mem_a32_p3_8 = ExprMem(a32 + ExprInt(3, 32), 8)
mem_a32_p4_8 = ExprMem(a32 + ExprInt(4, 32), 8)

mem_a32_m4_32 = ExprMem(a32 + ExprInt(-4, 32), 32)
mem_a32_m3_32 = ExprMem(a32 + ExprInt(-3, 32), 32)
mem_a32_m2_32 = ExprMem(a32 + ExprInt(-2, 32), 32)
mem_a32_m1_32 = ExprMem(a32 + ExprInt(-1, 32), 32)
mem_a32_p0_32 = ExprMem(a32, 32)
mem_a32_p1_32 = ExprMem(a32 + ExprInt(1, 32), 32)
mem_a32_p2_32 = ExprMem(a32 + ExprInt(2, 32), 32)
mem_a32_p3_32 = ExprMem(a32 + ExprInt(3, 32), 32)
mem_a32_p4_32 = ExprMem(a32 + ExprInt(4, 32), 32)

mem_a64_m4_32 = ExprMem(a64 + ExprInt(-4, 64), 32)
mem_a64_m3_32 = ExprMem(a64 + ExprInt(-3, 64), 32)
mem_a64_m2_32 = ExprMem(a64 + ExprInt(-2, 64), 32)
mem_a64_m1_32 = ExprMem(a64 + ExprInt(-1, 64), 32)
mem_a64_p0_32 = ExprMem(a64, 32)
mem_a64_p1_32 = ExprMem(a64 + ExprInt(1, 64), 32)
mem_a64_p2_32 = ExprMem(a64 + ExprInt(2, 64), 32)
mem_a64_p3_32 = ExprMem(a64 + ExprInt(3, 64), 32)
mem_a64_p4_32 = ExprMem(a64 + ExprInt(4, 64), 32)


@pytest.fixture
def state():
    return State()


def commutative(list):
    for e in list:
        dst, src, expected = e

        yield {dst}, src, expected
        yield {src}, dst, expected


@pytest.mark.parametrize("dst,src,expected", commutative([
    (mem_a32_32, mem_b32_32, True)
]))
def test(state, dst, src, expected):
    print("Destinations:", dst)
    print("Source:      ", repr(src))
    assert state.may_interfer(dst, src) == expected


@pytest.mark.parametrize("dst,src,expected", commutative([
    (mem_a32_m1_8, mem_a32_32, False),
    (mem_a32_p0_8, mem_a32_32, True),
    (mem_a32_p1_8, mem_a32_32, True),
    (mem_a32_p2_8, mem_a32_32, True),
    (mem_a32_p3_8, mem_a32_32, True),
    (mem_a32_p4_8, mem_a32_32, False),
]))
def test_8_bits(state, dst, src, expected):
    print("Destinations:", dst)
    print("Source:      ", repr(src))
    assert state.may_interfer(dst, src) == expected


@pytest.mark.parametrize("dst,src,expected", commutative([
    (mem_a32_m4_32, mem_a32_32, False),
    (mem_a32_m3_32, mem_a32_32, True),
    (mem_a32_m2_32, mem_a32_32, True),
    (mem_a32_m1_32, mem_a32_32, True),
    (mem_a32_p0_32, mem_a32_32, True),
    (mem_a32_p1_32, mem_a32_32, True),
    (mem_a32_p2_32, mem_a32_32, True),
    (mem_a32_p3_32, mem_a32_32, True),
    (mem_a32_p4_32, mem_a32_32, False),
]))
def test_32_bits(state, dst, src, expected):
    print("Destinations:", dst)
    print("Source:      ", repr(src))
    assert state.may_interfer(dst, src) == expected


@pytest.mark.parametrize("dst,src,expected", commutative([
    (mem_a64_m4_32, mem_a64_32, False),
    (mem_a64_m3_32, mem_a64_32, True),
    (mem_a64_m2_32, mem_a64_32, True),
    (mem_a64_m1_32, mem_a64_32, True),
    (mem_a64_p0_32, mem_a64_32, True),
    (mem_a64_p1_32, mem_a64_32, True),
    (mem_a64_p2_32, mem_a64_32, True),
    (mem_a64_p3_32, mem_a64_32, True),
    (mem_a64_p4_32, mem_a64_32, False),
]))
def test_32_bits_on_64_bits_addresses(state, dst, src, expected):
    print("Destinations:", dst)
    print("Source:      ", repr(src))
    assert state.may_interfer(dst, src) == expected
