# This file contains automated tests for this module.
# You can use these tests as usage examples.
# To run these, see the 'Testing' section in the README.

import os

import pytest

from .basic_simplification import exprs, check as check_basic_simplification
from .expr_c import c_acceses, check as check_expr_c
from .expr_reduce import tests, check as check_expr_reduce

current_path = os.path.dirname(__file__)


def test_access_c(shellcode_human, out_path):
    human_bin, _ = shellcode_human

    from .access_c import access_c
    access_c(human_bin, out_path)


def test_asm_to_ir(out_path):
    from .asm_to_ir import main

    main(out_path)


def test_basic_op():
    from .basic_op import main

    main()


@pytest.mark.parametrize("e", exprs)
def test_basic_simplification(e):
    check_basic_simplification(e)


def test_constant_propagation(out_path):
    input = os.path.join(current_path, "..", "samples", "simple_test.bin")

    from .constant_propagation import constant_propagation
    constant_propagation(input, "0", simplify=True, output=out_path)


def test_export_llvm(out_path):
    import llvmlite

    input = os.path.join(current_path, "..", "samples", "simple_test.bin")

    from .export_llvm import export
    export(input, "x86_32", "0", out_path)


@pytest.mark.parametrize("c_str", c_acceses)
def test_expr_c(c_str):
    check_expr_c(c_str)


def test_grapher():
    from .expr_grapher import main

    main()


@pytest.mark.parametrize("expr_in,result", tests)
def test_reduce(expr_in, result):
    check_expr_reduce(expr_in, result)


def test_read_write():
    from .get_read_write import main

    main()


@pytest.mark.parametrize("symbolic", [True, False])
def test_dataflow(symbolic):
    input = os.path.join(current_path, "..", "samples", "simple_test.bin")

    from .graph_dataflow import dataflow
    dataflow(input, "0", symbolic)


def test_simplification_add():
    from .simplification_add import main

    main()


def test_simplification_tools():
    from .simplification_tools import main

    main()


def test_solve_condition_stp(out_path):
    input = os.path.join(current_path, "..", "samples", "simple_test.bin")

    from .solve_condition_stp import solve
    solve(input, "0", out_path)
