from __future__ import print_function

import json
from typing import Optional, List

from future.utils import viewitems

from miasm.analysis.binary import Container
from miasm.analysis.depgraph import DependencyGraph
from miasm.analysis.machine import Machine
from miasm.core.locationdb import LocationDB
from miasm.expression.expression import ExprMem, ExprId, ExprInt


def depgraph(filename, architecture, target_elements, func_addr, target_addr, rename_args=False, implicit=False, do_not_simplify=False,
             unfollow_mem=False, unfollow_call=False, generate_json=False):
    # type: (str, Optional[str], List[str], str, str, bool, bool, bool, bool, bool, bool) -> Optional[str]
    """
    Disassembles a binary, and analyses the dependencies of one or more expressions at a specific point.
    :param filename: The binary file to analyse
    :param architecture: The architecture of the `filename` (x86_32...)
    :param target_elements: The different expressions you want to analyze (EAX...)
    :param func_addr: The address of the function you want to disassemble
    :param target_addr: The address of the point in time when you want to evaluate the target expressions
    :param rename_args: `True` to rename common arguments (@32[ESP_init] -> Arg1...)
    :param implicit: See DepGraph implicit mode
    :param do_not_simplify: See DepGraph simplification
    :param unfollow_mem: See DepGraph memory following
    :param unfollow_call: See DepGraph call following
    :param generate_json: Generate a JSON of the different constraints on the targeted expressions
    :return: A JSON string if `generate_json is True`, `None` in all other cases
    """
    loc_db = LocationDB()
    # Get architecture
    with open(filename, "rb") as fstream:
        cont = Container.from_stream(fstream, loc_db)

    arch = architecture if architecture else cont.arch
    machine = Machine(arch)

    # Check elements
    elements = set()
    regs = machine.mn.regs.all_regs_ids_byname
    for element in target_elements:
        try:
            elements.add(regs[element])
        except KeyError:
            raise ValueError("Unknown element '%s'" % element)

    mdis = machine.dis_engine(cont.bin_stream, dont_dis_nulstart_bloc=True, loc_db=loc_db)
    lifter = machine.lifter_model_call(loc_db)

    # Common argument forms
    init_ctx = {}
    if rename_args:
        if arch == "x86_32":
            # StdCall example
            for i in range(4):
                e_mem = ExprMem(ExprId("ESP_init", 32) + ExprInt(4 * (i + 1), 32), 32)
                init_ctx[e_mem] = ExprId("arg%d" % i, 32)

    # Disassemble the targeted function
    asmcfg = mdis.dis_multiblock(int(func_addr, 0))
    assert len(asmcfg.blocks), "The generated ASMCFG is empty"
    assert len([block for block in asmcfg.blocks if not block.is_bad()]) > 0, "The generated ASMCFG contains no good blocks, and contains " + str(len(asmcfg.blocks)) + " bad block(s): " + str([block for block in asmcfg.blocks if block.is_bad()])

    # Generate IR
    ircfg = lifter.new_ircfg_from_asmcfg(asmcfg)
    assert len(ircfg.blocks) > 0, "The generated IRCFG is empty"

    # Get the instance
    dg = DependencyGraph(
        ircfg, implicit=implicit,
        apply_simp=not do_not_simplify,
        follow_mem=not unfollow_mem,
        follow_call=not unfollow_call
    )

    # Build information
    target_addr = int(target_addr, 0)
    current_loc_key = next(iter(ircfg.getby_offset(target_addr)))
    assignblk_index = 0
    current_block = ircfg.get_block(current_loc_key)
    for assignblk_index, assignblk in enumerate(current_block):
        if assignblk.instr.offset == target_addr:
            break

    # Enumerate solutions
    json_solutions = []
    for sol_nb, sol in enumerate(dg.get(current_block.loc_key, elements, assignblk_index, set())):
        fname = "sol_%d.dot" % sol_nb
        with open(fname, "w") as fdesc:
            fdesc.write(sol.graph.dot())

        results = sol.emul(lifter, ctx=init_ctx)
        tokens = {str(k): str(v) for k, v in viewitems(results)}
        if not generate_json:
            result = ", ".join("=".join(x) for x in viewitems(tokens))
            print("Solution %d: %s -> %s" % (sol_nb,
                                             result,
                                             fname))
            if sol.has_loop:
                print('\tLoop involved')

        if implicit:
            sat = sol.is_satisfiable
            constraints = {}
            if sat:
                for element in sol.constraints:
                    try:
                        result = '0x%x' % sol.constraints[element].as_long()
                    except AttributeError:
                        result = str(sol.constraints[element])
                    constraints[element] = result
            if generate_json:
                tokens["satisfiability"] = sat
                tokens["constraints"] = {
                    str(k): str(v)
                    for k, v in viewitems(constraints)
                }
            else:
                print("\tSatisfiability: %s %s" % (sat, constraints))

        if generate_json:
            tokens["has_loop"] = sol.has_loop
            json_solutions.append(tokens)

    if generate_json:
        return json.dumps(json_solutions)


if __name__ == '__main__':
    from argparse import ArgumentParser

    parser = ArgumentParser("Dependency grapher")
    parser.add_argument("filename", help="Binary to analyse")
    parser.add_argument("func_addr", help="Function address")
    parser.add_argument("target_addr", help="Address to start")
    parser.add_argument("element", nargs="+", help="Elements to track")
    parser.add_argument("-m", "--architecture",
                        help="Architecture (%s)" % Machine.available_machine())
    parser.add_argument("-i", "--implicit", help="Use implicit tracking",
                        action="store_true")
    parser.add_argument("--unfollow-mem", help="Stop on memory statements",
                        action="store_true")
    parser.add_argument("--unfollow-call", help="Stop on call statements",
                        action="store_true")
    parser.add_argument("--do-not-simplify", help="Do not simplify expressions",
                        action="store_true")
    parser.add_argument("--rename-args",
                        help="Rename common arguments (@32[ESP_init] -> Arg1)",
                        action="store_true")
    parser.add_argument("--json",
                        help="Output solution in JSON",
                        action="store_true")
    args = parser.parse_args()

    json = depgraph(args.filename, args.architecture, args.element, args.func_addr, args.target_addr, args.rename, args.implicit, args.do_not_simplify, args.unfollow_mem, args.unfollow_call, args.json)

    if args.json:
        print(json)
