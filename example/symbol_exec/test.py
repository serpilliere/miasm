# This file contains automated tests for this module.
# You can use these tests as usage examples.
# To run these, see the 'Testing' section in the README.

import os

import pytest

current_path = os.path.dirname(__file__)


@pytest.mark.parametrize("strategy", ["branch-cov", "code-cov", "path-cov"])
@pytest.mark.parametrize("jitter_name", ["llvm", "python", "gcc"])
def test_dse_crackme(strategy, jitter_name):
    input = os.path.join(current_path, "..", "samples", "dse_crackme")

    options = type('', (), {})()
    options.jitter = jitter_name
    options.usesegm = False
    options.command_line = False
    options.environment_vars = False
    options.singlestep = False
    options.dumpblocs = False
    options.quiet_function_calls = False
    options.mimic_env = False

    from .dse_crackme import dse
    dse(input, strategy, options)


@pytest.mark.parametrize("strategy", ["branch-cov", "code-cov", "path-cov"])
def test_dse_strategies(strategy):
    input = os.path.join(current_path, "..", "samples", "dse_crackme")

    from .dse_strategies import solve
    solve(input, strategy)
