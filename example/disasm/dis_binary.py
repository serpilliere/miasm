from __future__ import print_function

import sys
from pathlib import Path

from miasm.analysis.binary import Container
from miasm.analysis.machine import Machine
from miasm.core.asmblock import AsmCFG, disasmEngine
from miasm.core.locationdb import LocationDB


def disassemble(input, output):
    # type: (str, Path) -> (Machine, disasmEngine, AsmCFG)
    """
    Disassembles a binary file and returns its assembly control flow graph (AsmCFG).
    :param input: The file to disassemble
    :return: Its ASMCFG, which is also printed
    """
    fdesc = open(input, 'rb')
    loc_db = LocationDB()

    # The Container will provide a *bin_stream*, bytes source for the disasm engine
    # It will provide a view from a PE or an ELF.
    cont = Container.from_stream(fdesc, loc_db)

    # The Machine, instantiated with the detected architecture, will provide tools
    # (disassembler, etc.) to work with this architecture
    machine = Machine(cont.arch)

    # Instantiate a disassembler engine, using the previous bin_stream and its
    # associated location DB. The assembly listing will use the binary symbols
    mdis = machine.dis_engine(cont.bin_stream, loc_db=cont.loc_db)

    # Run a recursive traversal disassembling from the entry point
    # (do not follow sub functions by default)
    addr = cont.entry_point
    asmcfg = mdis.dis_multiblock(addr)

    # Display each basic block
    print(asmcfg)
    # They can be accessed individually through asmcfg.blocks

    # Output control flow graph in a dot file
    output.joinpath("bin_cfg.dot").write_text(asmcfg.dot())

    return machine, mdis, asmcfg


if __name__ == '__main__':
    output = Path()

    disassemble(sys.argv[1], output)
