from __future__ import print_function

from miasm.ir.ir import IRCFG
from .dis_binary import *


def lift_model_call(input, output):
    # type: (str, Path) -> IRCFG
    """
    Disassembles a binary file and lifts it to IR, then returns the IR control flow graph (IRCFG).
    While lifting to IR, we model function calls.
    Look at the differences between the output of 'lift' (dis_binary_lift.py) and this function.
    :param input: The file to disassemble
    :return: Its IRCFG
    """

    # Generate the AsmCFG using dis_binary.py
    machine, mdis, asmcfg = disassemble(input, output)

    # Get a Lifter
    lifter = machine.lifter_model_call(mdis.loc_db)

    # Get the IR of the asmcfg
    ircfg = lifter.new_ircfg_from_asmcfg(asmcfg)

    # Display each IR basic block
    print(ircfg)
    # As with AsmCFGs, they can be accessed individually through ircfg.blocks

    # Output ir control flow graph in a dot file
    output.joinpath("bin_model_call_ir_cfg.dot").write_text(ircfg.dot())

    return ircfg


if __name__ == '__main__':
    lift_model_call(sys.argv[1], Path())
