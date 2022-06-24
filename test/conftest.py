import builtins
import os

import pytest

from miasm.ir.translators import Translator
from .examples.asm.shellcode import shellcode_sample


# PyTest configuration file
# Fixtures created here can be used in all tests

# region CLI

def pytest_addoption(parser):
    for dep in optional_dependencies:
        parser.addoption("--with-%s" % dep, action="store_true", help="Execute as if %s was not an optional dependency: fail tests if %s is missing instead of skipping them" % (dep, dep))


def pytest_configure(config):
    global optional_dependencies

    options = vars(config.option)

    for dep in list(optional_dependencies.keys()):
        if options["with_%s" % dep]:
            del optional_dependencies[dep]


# endregion
# region Shellcode generation


def _run_shellcode(input, arch, output, generate_pe=False, encrypt=None):
    path, _ = shellcode_sample(input, arch, output, generate_pe=generate_pe, encrypt=encrypt)
    yield path, arch

    if os.path.exists(path) and os.environ.get("miasm_keep_shellcodes") is None:
        print("Removing generated file <", path,
              ">. To keep it, create the environment variable 'miasm_keep_shellcodes'.")
        os.remove(path)


@pytest.fixture(scope="session")
def shellcode_demo_aarch64_b():
    for e in _run_shellcode("aarch64_simple.S", "aarch64b", "demo_aarch64_b.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_demo_aarch64_l():
    for e in _run_shellcode("aarch64_simple.S", "aarch64l", "demo_aarch64_l.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_demo_arm_b():
    for e in _run_shellcode("arm_simple.S", "armb", "demo_arm_b.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_demo_arm_l():
    for e in _run_shellcode("arm_simple.S", "arml", "demo_arm_l.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_demo_arm2_b():
    for e in _run_shellcode("arm_sc.S", "armb", "demo_arm2_b.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_demo_arm2_l():
    for e in _run_shellcode("arm_sc.S", "arml", "demo_arm2_l.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_demo_armt_b():
    for e in _run_shellcode("armt.S", "armtb", "demo_armt_b.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_demo_armt_l():
    for e in _run_shellcode("armt.S", "armtl", "demo_armt_l.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_mips32_sc_b():
    for e in _run_shellcode("mips32.S", "mips32b", "mips32_sc_b.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_mips32_sc_l():
    for e in _run_shellcode("mips32.S", "mips32l", "mips32_sc_l.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_msp430_sc():
    for e in _run_shellcode("msp430.S", "msp430", "msp430_sc.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_dis():
    for e in _run_shellcode("test_x86_32_dis.S", "x86_32", "test_x86_32_dis.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_automod():
    for e in _run_shellcode("x86_32_automod.S", "x86_32", "x86_32_automod.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_automod2():
    for e in _run_shellcode("x86_32_automod_2.S", "x86_32", "x86_32_automod_2.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_dead():
    for e in _run_shellcode("x86_32_dead.S", "x86_32", "x86_32_dead.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_enc():
    for e in _run_shellcode("x86_32_enc.S", "x86_32", "enc.bin", generate_pe=True,
                            encrypt=("msgbox_encrypted_start", "msgbox_encrypted_stop")):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_if_reg():
    for e in _run_shellcode("x86_32_if_reg.S", "x86_32", "x86_32_if_reg.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_demo_x86_32():
    for e in _run_shellcode("x86_32_manip_ptr.S", "x86_32", "demo_x86_32.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_mod():
    for e in _run_shellcode("x86_32_mod.S", "x86_32", "x86_32_mod.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_mod_self():
    for e in _run_shellcode("x86_32_mod_self.S", "x86_32", "x86_32_mod_self.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_pop_esp():
    for e in _run_shellcode("x86_32_pop_esp.S", "x86_32", "x86_32_pop_esp.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_repmod():
    for e in _run_shellcode("x86_32_repmod.S", "x86_32", "x86_32_repmod.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_seh():
    for e in _run_shellcode("x86_32_seh.S", "x86_32", "x86_32_seh.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_x86_32_simple():
    for e in _run_shellcode("x86_32_simple.S", "x86_32", "x86_32_simple.bin", generate_pe=True):
        yield e


@pytest.fixture(scope="session")
def shellcode_human():
    for e in _run_shellcode("human.S", "x86_64", "human.bin"):
        yield e


@pytest.fixture(scope="session")
def shellcode_demo_x86_64():
    for e in _run_shellcode("x86_64.S", "x86_64", "demo_x86_64.bin", generate_pe=True):
        yield e


def _current_path():
    return os.path.dirname(__file__)


@pytest.fixture
def sample_md5_aarch64l():
    return os.path.join(_current_path(), "examples", "samples", "md5_aarch64l"), "aarch64l"


@pytest.fixture
def sample_md5_ppc32b():
    return os.path.join(_current_path(), "examples", "samples", "md5_ppc32b"), "ppc32b"


@pytest.fixture
def sample_md5_arm():
    return os.path.join(_current_path(), "examples", "samples", "md5_arm"), "arm"


@pytest.fixture
def sample_box_upx():
    return os.path.join(_current_path(), "examples", "samples", "box_upx.exe"), "x86_32"


@pytest.fixture
def sample_x86_32_sc():
    return os.path.join(_current_path(), "examples", "samples", "x86_32_sc.bin"), "x86_32"


@pytest.fixture
def sample_test_i386():
    return os.path.join(_current_path(), "arch", "x86", "qemu", "test-i386"), "x86_32"


# endregion
# region Jitters

@pytest.fixture(params=[
    pytest.param("gcc", marks=[pytest.mark.jitter_gcc, pytest.mark.jitter]),
    pytest.param("llvm", marks=[pytest.mark.jitter_llvm, pytest.mark.jitter]),
    pytest.param("python", marks=[pytest.mark.jitter_python, pytest.mark.jitter]),
    pytest.param("llvm_rs", marks=[pytest.mark.jitter_llvm_rs, pytest.mark.jitter]),
])
def jitter_name(request):
    """The name of each available Jitter (parameterized)."""
    jitter = request.param  # type: str

    print("Using jitter", jitter)
    print("To skip all tests using this jitter, run with '-m \"not jitter_%s\"'" % jitter)
    print("To skip all tests using any jitter, run with '-m \"not jitter\"'")

    return jitter


# endregion
# region Translators

@pytest.fixture(params=Translator.available_translators)
def translator(request):
    """Provides an available language translator"""
    return request.param()


# endregion
# region Output

@pytest.fixture(scope="function")
def out_path(pytestconfig, request):
    # (Config, Any) -> Path
    """
    The 'test/out' directory, in which the various tests can create their outputs.
    """
    test_root = pytestconfig.rootpath
    out = test_root.joinpath("out")
    out.mkdir(exist_ok=True)

    test_path = request.path.with_suffix('').relative_to(test_root)
    test_out = out.joinpath(test_path)
    test_out.mkdir(exist_ok=True, parents=True)

    print("Files will be generated in", test_out.absolute())

    return test_out


# endregion
# region Optional dependencies
# When PyTest is running, if we try to import something listed in the optional dependencies, we want to skip the test
# instead of failing it.

# (module_name, pip_install_name)
optional_dependencies = {
    "z3": "z3-solver",
    "pycparser": "pycparser",
    "llvmlite": "llvmlite",
}
original_import = builtins.__import__


def import_or_automatically_skip(name, globals=None, locals=None, fromlist=(), level=0):
    def real_import():
        return original_import(name, globals, locals, fromlist, level)

    if name in optional_dependencies:
        try:
            return real_import()
        except ImportError as e:
            trace = "Traceback (most recent first):\n"
            frame = e.__traceback__.tb_frame.f_back
            while frame is not None:
                trace += str(frame) + "\n"
                frame = frame.f_back

            pytest.skip(name + " is not installed, use 'pip install " + optional_dependencies[name] + "'.\n\n" + trace, allow_module_level=True)
    else:
        return real_import()


builtins.__import__ = import_or_automatically_skip

# endregion
