from miasm.expression.expression import *
from miasm.expression.expression_helper import Variables_Identifier


def test_variables_identifier():
    # Build a complex expression
    cst = ExprInt(0x100, 16)
    eax = ExprId("EAX", 32)
    ebx = ExprId("EBX", 32)
    ax = eax[0:16]
    expr = eax + ebx
    expr = ExprCompose(ax, expr[16:32])
    expr2 = ExprMem((eax + ebx) ^ (eax), size=16)
    expr2 = expr2 | ax | expr2 | cst
    exprf = expr - expr + ExprCompose(expr2, cst)

    # Identify variables
    vi = Variables_Identifier(exprf)

    # Use __str__
    print(vi)

    # Test the result
    new_expr = vi.equation

    # Force replace in the variable dependency order
    for var_id, var_value in reversed(list(viewitems(vi.vars))):
        new_expr = new_expr.replace_expr({var_id: var_value})
    assert new_expr, exprf

    # Test prefix
    vi = Variables_Identifier(exprf, var_prefix="prefix_v")

    # Use __str__
    print(vi)

    # Test the result
    new_expr = vi.equation
    # Force replace in the variable dependency order
    for var_id, var_value in reversed(list(viewitems(vi.vars))):
        new_expr = new_expr.replace_expr({var_id: var_value})
    assert new_expr == exprf

    # Test and identify on an expression already containing identifier
    vi = Variables_Identifier(exprf)
    vi2 = Variables_Identifier(vi.equation)

    # Test the result
    new_expr = vi2.equation
    # Force replace in the variable dependency order
    for var_id, var_value in reversed(list(viewitems(vi2.vars))):
        new_expr = new_expr.replace_expr({var_id: var_value})
    assert new_expr == vi.equation

    # Corner case: each sub var depends on itself
    mem1 = ExprMem(ebx, size=32)
    mem2 = ExprMem(mem1, size=32)
    cst2 = -ExprInt(1, 32)
    expr_mini = ((eax ^ mem2 ^ cst2) & (mem2 ^ (eax + mem2)))[31:32]

    # Build
    vi = Variables_Identifier(expr_mini)
    vi2 = Variables_Identifier(vi.equation)

    # Test the result
    new_expr = vi2.equation
    # Force replace in the variable dependency order
    for var_id, var_value in reversed(list(viewitems(vi2.vars))):
        new_expr = new_expr.replace_expr({var_id: var_value})
    assert new_expr, vi.equation
