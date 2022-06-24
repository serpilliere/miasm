import logging
from argparse import ArgumentParser
from collections.abc import Iterable
from pathlib import Path
from typing import Optional, Union, List

from future.utils import viewvalues, viewitems

from miasm.analysis.binary import Container
from miasm.analysis.data_flow import ReachingDefinitions, DiGraphDefUse, load_from_int
from miasm.analysis.machine import Machine
from miasm.analysis.simplifier import IRCFGSimplifierCommon, IRCFGSimplifierSSA
from miasm.analysis.ssa import SSADiGraph
from miasm.core.asmblock import log_asmblock, AsmCFG
from miasm.core.interval import interval
from miasm.core.locationdb import LocationDB
from miasm.ir.ir import AssignBlock

log = logging.getLogger("dis")
console_handler = logging.StreamHandler()
console_handler.setFormatter(logging.Formatter("%(levelname)-5s: %(message)s"))
log.addHandler(console_handler)
log.setLevel(logging.INFO)


def full(filename, address=None, architecture=None, base_address=0, follow_call=False, block_watchdog=None,
         func_watchdog=None, recurse_into_functions=False, verbose=False, gen_ir=False,
         disassemble_null_starting_blocks=False, no_disassemble_ret=False, simplify=False, try_disassemble_all=False,
         generate_image=False, raw_binary=False, def_use=False, ssa=False, propagate_expressions=False, load_ints=False,
         calls_dont_modify_stack=False, output=Path()):
    # type: (str, Union[int, str, List[Union[int, str]], None], Optional[str], int, bool, Optional[int], Optional[int], bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, Path) -> None
    """
    Disassembles a binary file and exports data from it.

    :param filename: The file to disassemble
    :param address: Starting address for the disassembly engine
    :param architecture: Architecture of the given file
    :param follow_call: `True` to follow call instructions
    :param block_watchdog: Maximum number of basic blocks to disassemble
    :param func_watchdog: Maximum number of functions to disassemble
    :param recurse_into_functions: `True` to disassemble functions that were found
    :param verbose: `True` to print more information
    :param gen_ir: `True` to compute the IR representation
    :param disassemble_null_starting_blocks: Disassemble blocks starting with `NULL`
    :param no_disassemble_ret: `True` to only disassemble call destinations
    :param simplify: Apply various simplification rules
    :param base_address: Base address of the input binary
    :param try_disassemble_all: `True` to attempt disassembling the whole binary
    :param generate_image: `True` to display an image representation of the disassembly
    :param raw_binary: `True` to interpret the file as a raw binary (data which is not in an ELF/PE container)
    :param def_use: `True` to dump the def-use graph (after simplification, if they are enabled)
    :param ssa: `True` to generate the SSA form
    :param propagate_expressions: `True` to propagate expressions
    :param load_ints: `True` to load integers from binary in fixed memory lookup
    :param calls_dont_modify_stack: `True` to consider the stack height as unchanged by `call`s
    :param output: The directory in which the generated files will be stored (by default, the current directory)
    """

    if address is None:
        address = []
    if not isinstance(address, Iterable):
        address = [address]

    if verbose:
        log_asmblock.setLevel(logging.DEBUG)

    loc_db = LocationDB()
    log.info('Load binary')

    with open(filename, "rb") as fdesc:
        if raw_binary:
            cont = Container.fallback_container(
                fdesc.read(),
                vm=None, addr=base_address,
                loc_db=loc_db,
            )
        else:
            cont = Container.from_stream(
                fdesc, addr=base_address,
                loc_db=loc_db,
            )

    default_addr = cont.entry_point
    bs = cont.bin_stream
    e = cont.executable
    log.info('ok')

    log.info("import machine...")
    # Use the guessed architecture or the specified one
    arch = architecture if architecture else cont.arch
    if not arch:
        print("Architecture recognition fail. Please specify it in arguments")
        exit(-1)

    # Instance the arch-dependent machine
    machine = Machine(arch)
    mn, dis_engine = machine.mn, machine.dis_engine
    log.info('ok')

    mdis = dis_engine(bs, loc_db=cont.loc_db)
    # configure disasm engine
    mdis.dontdis_retcall = no_disassemble_ret
    mdis.blocs_wd = block_watchdog
    mdis.dont_dis_nulstart_bloc = not disassemble_null_starting_blocks
    mdis.follow_call = follow_call

    todo = []
    addrs = []
    for addr in address:
        if isinstance(addr, int):
            # it's already an int
            addrs.append(addr)
        else:
            try:
                # it's not an int, but it can be converted into one
                addrs.append(int(addr, 0))
            except ValueError:
                # it can't be converted as an int, check if it's a location
                loc_key = mdis.loc_db.get_name_location(addr)
                offset = mdis.loc_db.get_location_offset(loc_key)
                addrs.append(offset)

    if len(addrs) == 0 and default_addr is not None:
        addrs.append(default_addr)
    for ad in addrs:
        todo += [(mdis, None, ad)]

    done = set()
    all_funcs = set()
    all_funcs_blocks = {}

    done_interval = interval()
    finish = False

    entry_points = set()
    # Main disasm loop
    while not finish and todo:
        while not finish and todo:
            mdis, caller, ad = todo.pop(0)
            if ad in done:
                continue
            done.add(ad)
            asmcfg = mdis.dis_multiblock(ad)
            entry_points.add(mdis.loc_db.get_offset_location(ad))

            log.info('func ok %.16x (%d)' % (ad, len(all_funcs)))

            all_funcs.add(ad)
            all_funcs_blocks[ad] = asmcfg
            for block in asmcfg.blocks:
                for l in block.lines:
                    done_interval += interval([(l.offset, l.offset + l.l)])

            if func_watchdog is not None:
                func_watchdog -= 1
            if recurse_into_functions:
                for block in asmcfg.blocks:
                    instr = block.get_subcall_instr()
                    if not instr:
                        continue
                    for dest in instr.getdstflow(mdis.loc_db):
                        if not dest.is_loc():
                            continue
                        offset = mdis.loc_db.get_location_offset(dest.loc_key)
                        todo.append((mdis, instr, offset))

            if func_watchdog is not None and func_watchdog <= 0:
                finish = True

        if try_disassemble_all:
            for a, b in done_interval.intervals:
                if b in done:
                    continue
                log.debug('add func %s' % hex(b))
                todo.append((mdis, None, b))

    # Generate dotty graph
    all_asmcfg = AsmCFG(mdis.loc_db)
    for blocks in viewvalues(all_funcs_blocks):
        all_asmcfg += blocks

    log.info('generate graph file')
    output.joinpath("graph_execflow.dot").write_text(all_asmcfg.dot(offset=True))

    log.info('generate intervals')

    all_lines = []
    total_l = 0

    print(done_interval)
    if generate_image:
        log.info('build img')
        done_interval.show()

    for i, j in done_interval.intervals:
        log.debug((hex(i), "->", hex(j)))

    all_lines.sort(key=lambda x: x.offset)
    output.joinpath("lines.dot").write_text('\n'.join(str(l) for l in all_lines))
    log.info('total lines %s' % total_l)

    if propagate_expressions:
        gen_ir = True


    class LifterDelModCallStack(machine.lifter_model_call):
        def call_effects(self, addr, instr):
            assignblks, extra = super(LifterDelModCallStack, self).call_effects(addr, instr)
            if not calls_dont_modify_stack:
                return assignblks, extra
            out = []
            for assignblk in assignblks:
                dct = dict(assignblk)
                dct = {
                    dst: src for (dst, src) in viewitems(dct) if dst != self.sp
                }
                out.append(AssignBlock(dct, assignblk.instr))
            return out, extra

    # Bonus, generate IR graph
    if gen_ir:
        log.info("Lift and Lift with modeled calls")

        lifter = machine.lifter(mdis.loc_db)
        lifter_model_call = LifterDelModCallStack(mdis.loc_db)

        ircfg = lifter.new_ircfg()
        ircfg_model_call = lifter.new_ircfg()

        head = list(entry_points)[0]

        for ad, asmcfg in viewitems(all_funcs_blocks):
            log.info("generating IR... %x" % ad)
            for block in asmcfg.blocks:
                lifter.add_asmblock_to_ircfg(block, ircfg)
                lifter_model_call.add_asmblock_to_ircfg(block, ircfg_model_call)

        log.info("Print blocks (without analyse)")
        for label, block in viewitems(ircfg.blocks):
            print(block)

        log.info("Gen Graph... %x" % ad)

        log.info("Print blocks (with analyse)")
        for label, block in viewitems(ircfg_model_call.blocks):
            print(block)

        if simplify > 0:
            log.info("Simplify...")
            ircfg_simplifier = IRCFGSimplifierCommon(lifter_model_call)
            ircfg_simplifier.simplify(ircfg_model_call, head)
            log.info("ok...")

        if def_use:
            reachings = ReachingDefinitions(ircfg_model_call)
            output.joinpath("graph_defuse.dot").write_text(DiGraphDefUse(reachings).dot())

        out = ircfg.dot()
        output.joinpath("graph_irflow_raw.dot").write_text(out)
        out = ircfg_model_call.dot()
        output.joinpath("graph_irflow.dot").write_text(out)

        if ssa and not propagate_expressions:
            if len(entry_points) != 1:
                raise RuntimeError("Your graph should have only one head")
            ssa = SSADiGraph(ircfg_model_call)
            ssa.transform(head)
            output.joinpath("ssa.dot").write_text(ircfg_model_call.dot())

    if propagate_expressions:
        def is_addr_ro_variable(bs, addr, size):
            """
            Return True if address at @addr is a read-only variable.
            WARNING: Quick & Dirty

            @addr: integer representing the address of the variable
            @size: size in bits

            """
            try:
                _ = bs.getbytes(addr, size // 8)
            except IOError:
                return False
            return True

        class CustomIRCFGSimplifierSSA(IRCFGSimplifierSSA):
            def do_simplify(self, ssa, head):
                modified = super(CustomIRCFGSimplifierSSA, self).do_simplify(ssa, head)
                if load_ints:
                    modified |= load_from_int(ssa.graph, bs, is_addr_ro_variable)

            def simplify(self, ircfg, head):
                ssa = self.ircfg_to_ssa(ircfg, head)
                ssa = self.do_simplify_loop(ssa, head)
                ircfg = self.ssa_to_unssa(ssa, head)

                ircfg_simplifier = IRCFGSimplifierCommon(self.lifter)
                ircfg_simplifier.deadremoval.add_expr_to_original_expr(ssa.ssa_variable_to_expr)
                ircfg_simplifier.simplify(ircfg, head)
                return ircfg

        head = list(entry_points)[0]
        simplifier = CustomIRCFGSimplifierSSA(lifter_model_call)
        ircfg = simplifier.simplify(ircfg_model_call, head)
        output.joinpath("final.dot").write_text(ircfg.dot())


if __name__ == '__main__':
    parser = ArgumentParser(description="Disassembles a binary")
    parser.add_argument('filename', help="File to disassemble")
    parser.add_argument('address', help="Starting address for disassembly engine",
                        nargs="*")
    parser.add_argument('-m', '--architecture', help="architecture: " + \
                                                     ",".join(Machine.available_machine()))
    parser.add_argument('-f', "--followcall", action="store_true",
                        help="Follow call instructions")
    parser.add_argument('-b', "--blockwatchdog", default=None, type=int,
                        help="Maximum number of basic block to disassemble")
    parser.add_argument('-n', "--funcswatchdog", default=None, type=int,
                        help="Maximum number of function to disassemble")
    parser.add_argument('-r', "--recurfunctions", action="store_true",
                        help="Disassemble founded functions")
    parser.add_argument('-v', "--verbose", action="count", help="Verbose mode",
                        default=0)
    parser.add_argument('-g', "--gen_ir", action="store_true",
                        help="Compute the intermediate representation")
    parser.add_argument('-z', "--dis-nulstart-block", action="store_true",
                        help="Do not disassemble NULL starting block")
    parser.add_argument('-l', "--dontdis-retcall", action="store_true",
                        help="If set, disassemble only call destinations")
    parser.add_argument('-s', "--simplify", action="count",
                        help="Apply simplifications rules (liveness, graph simplification, ...)",
                        default=0)
    parser.add_argument("--base-address", default=0,
                        type=lambda x: int(x, 0),
                        help="Base address of the input binary")
    parser.add_argument('-a', "--try-disasm-all", action="store_true",
                        help="Try to disassemble the whole binary")
    parser.add_argument('-i', "--image", action="store_true",
                        help="Display image representation of disasm")
    parser.add_argument('-c', "--rawbinary", default=False, action="store_true",
                        help="Don't interpret input as ELF/PE/...")
    parser.add_argument('-d', "--defuse", action="store_true",
                        help="Dump the def-use graph in file 'defuse.dot'."
                             "The defuse is dumped after simplifications if -s option is specified")
    parser.add_argument('-p', "--ssa", action="store_true",
                        help="Generate the ssa form in  'ssa.dot'.")
    parser.add_argument('-x', "--propagexpr", action="store_true",
                        help="Do Expression propagation.")
    parser.add_argument('-e', "--loadint", action="store_true",
                        help="Load integers from binary in fixed memory lookup.")
    parser.add_argument('-j', "--calldontmodstack", action="store_true",
                        help="Consider stack high is not modified in subcalls")

    args = parser.parse_args()

    full(args.filename, verbose=args.verbose, raw_binary=args.rawbinary, base_address=args.base_address,
         architecture=args.architecture, no_disassemble_ret=args.dontdis_retcall, block_watchdog=args.blockwatchdog,
         disassemble_null_starting_blocks=not args.dis_nulstart_block, follow_call=args.followcall,
         address=args.address, func_watchdog=args.funcswatchdog, recurse_into_functions=args.recurfunctions,
         try_disassemble_all=args.try_disasm_all, generate_image=args.image, propagate_expressions=args.propagexpr,
         gen_ir=args.gen_ir, calls_dont_modify_stack=args.calldontmodstack, simplify=args.simplify,
         def_use=args.defuse, ssa=args.ssa, load_ints=args.loadint)
