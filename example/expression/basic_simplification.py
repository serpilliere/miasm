from __future__ import print_function

from miasm.expression.expression import *
from miasm.expression.simplifications import expr_simp

# Simple expression simplification demo

a = ExprId('eax', 32)
b = ExprId('ebx', 32)

exprs = [a + b - a,
         ExprInt(0x12, 32) + ExprInt(0x30, 32) - a,
         ExprCompose(a[:8], a[8:16])]


def check(e):
    print('original expression:', e)
    print("simplified:", expr_simp(e))


if __name__ == '__main__':
    for e in exprs:
        check(e)
