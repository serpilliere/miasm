import os
import sys

import pytest

from miasm.analysis.sandbox import Sandbox_Linux_x86_32, Sandbox_Linux_x86_64, \
    Sandbox_Linux_arml, Sandbox_Linux_aarch64l, Sandbox
from miasm.core.locationdb import LocationDB

#  TEST/OS_DEP/LINUX test_env.py x86_64 test_env.x86_64 -c arg1 -c arg2 --environment-vars TEST=TOTO --mimic-env
#  TEST/OS_DEP/LINUX test_env.py x86_32 test_env.x86_32 -c arg1 -c arg2 --environment-vars TEST=TOTO --mimic-env
#  TEST/OS_DEP/LINUX test_env.py aarch64l test_env.aarch64l -c arg1 -c arg2 --environment-vars TEST=TOTO --mimic-env
#  TEST/OS_DEP/LINUX test_env.py arml test_env.arml -c arg1 -c arg2 --environment-vars TEST=TOTO --mimic-env

current_path = os.path.abspath(os.path.dirname(__file__))


def options(sandbox):
    return sandbox.parser().parse_args(["-c", "arg1", "-c", "arg2", "--environment-vars", "TEST=TOTO", "--mimic-env"])


@pytest.mark.skip(reason="Currently SIGABORT, todo fix")
@pytest.mark.parametrize("sandbox,options,filename", [
    (Sandbox_Linux_x86_64, options(Sandbox_Linux_x86_64), os.path.join(current_path, "test_env.x86_64")),
    (Sandbox_Linux_x86_32, options(Sandbox_Linux_x86_32), os.path.join(current_path, "test_env.x86_32")),
    (Sandbox_Linux_aarch64l, options(Sandbox_Linux_aarch64l), os.path.join(current_path, "test_env.aarch64l")),
    (Sandbox_Linux_arml, options(Sandbox_Linux_arml), os.path.join(current_path, "test_env.arml"))
])
def test(sandbox, options, filename):
    # Create sandbox
    loc_db = LocationDB()
    sb = sandbox(loc_db, filename, options, globals())

    # Run
    sb.run()

    assert (sb.jitter.running is False)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <arch> ..." % sys.argv[0])
        exit(1)

    arch = sys.argv[1]

    if arch == "x86_32":
        sandbox = Sandbox_Linux_x86_32
    elif arch == "x86_64":
        sandbox = Sandbox_Linux_x86_64
    elif arch == "arml":
        sandbox = Sandbox_Linux_arml
    elif arch == "aarch64l":
        sandbox = Sandbox_Linux_aarch64l
    else:
        raise ValueError("Unsupported arch: %s" % arch)

    # Parse arguments
    parser = Sandbox.parser(description="ELF sandboxer")
    parser.add_argument("filename", help="ELF Filename")
    options = parser.parse_args(sys.argv[2:])

    test(sandbox, options, options.filename)
