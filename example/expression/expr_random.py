from __future__ import print_function
import string
import random

from miasm.expression.expression_helper import ExprRandom


def test_atomic():
    seed = 0
    random.seed(seed)

    print("- An ID:")
    print(ExprRandom.identifier())
    print("- A number:")
    print(ExprRandom.number())


def test_expressions_with_cache():
    depth = 8
    seed = 0
    random.seed(seed)

    print("- 3 expressions (without cleaning expression cache):")
    for i in range(3):
        print("\t%s\n" % ExprRandom.get(depth=depth, clean=False))


class ExprRandom_NoPerfect_NoReuse_UppercaseIdent(ExprRandom):
    """ExprRandom extension with:
     - perfect tree disabled
     - element reuse disabled
     - identifiers uppercased
     """

    perfect_tree = False
    reuse_element = False
    identifier_charset = string.ascii_uppercase


def test_expressions_custom_generator():
    depth = 8
    seed = 0
    random.seed(seed)

    print("- 3 expressions with a custom generator:")
    for i in range(3):
        print("\t%s\n" % ExprRandom_NoPerfect_NoReuse_UppercaseIdent.get(depth=depth))


if __name__ == '__main__':
    print("Simple expression generator\n")
    test_atomic()
    test_expressions_with_cache()
    test_expressions_custom_generator()
