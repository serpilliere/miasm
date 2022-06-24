from __future__ import print_function

import random

from miasm.expression.expression import *
from miasm.expression.expression_helper import ExprRandom
from miasm.ir.translators import Translator


class ExprRandom_OpSubRange(ExprRandom):
    operations_by_args_number = {1: ["-"],
                                 2: ["<<", ">>", ],
                                 "2+": ["+", "*", "&", "|", "^"],
                                 }


random.seed(0)

print("[+] Compute a random expression:")
expr = ExprRandom_OpSubRange.get(depth=8)
print("-> %s" % expr)


def test_translate(translator):
    target_lang = translator.__LANG__
    target_expr = translator.from_expr(expr)

    print("[+] Translate in %s:" % target_lang)
    print(target_expr)


def memory(addr, size):
    ret = random.randint(0, (1 << size) - 1)
    print("Memory access: @0x%x -> 0x%x" % (addr, ret))
    return ret


def test_python():
    python = Translator.to_language("python")
    print("Expression:", expr)
    target_expr = python.from_expr(expr)
    print("Target:    ", target_expr)

    for expr_id in expr.get_r(mem_read=True):
        if isinstance(expr_id, ExprId):
            value = random.randint(0, (1 << expr_id.size) - 1)
            print("Declare var: %s = 0x%x" % (expr_id.name, value))
            globals()[expr_id.name] = value

    print("-> 0x%x" % eval(target_expr))


def test_miasm():
    m = Translator.to_language("miasm")
    target_expr = m.from_expr(expr)

    print("[+] Validate the Miasm syntax rebuilding")
    exprRebuild = eval(target_expr)
    assert (expr == exprRebuild)


def test_equality(translator):
    a = ExprId("a", 32)
    b = ExprId("b", 32)
    cst1 = ExprInt(1, 32)
    eq_test = ExprOp("==", a, b + cst1)

    print("Translate to %s:" % translator.__LANG__)
    print(translator.from_expr(eq_test))


if __name__ == '__main__':
    for translator_builder in Translator.available_translators:
        translator = translator_builder()
        test_translate(translator)
        test_equality(translator)

    test_python()
    test_miasm()
