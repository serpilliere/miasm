"""
Apply simplification passes to an IR cfg
"""

import logging
from miasm2.analysis.ssa import SSADiGraph, UnSSADiGraph, DiGraphLivenessSSA
from miasm2.expression.simplifications import expr_simp
from miasm2.analysis.data_flow import dead_simp, \
    merge_blocks, remove_empty_assignblks, \
    PropagateExprIntThroughExprId, PropagateThroughExprId, \
    PropagateThroughExprMem, del_unused_edges


log = logging.getLogger("simplifier")
console_handler = logging.StreamHandler()
console_handler.setFormatter(logging.Formatter("%(levelname)-5s: %(message)s"))
log.addHandler(console_handler)
log.setLevel(logging.DEBUG)


class IRcfgSimplifier(object):
    """
    Simplify an IRCFG
    This class apply following pass until reaching a fix point:
    - simplify_ircfg
    - do_dead_simp_ircfg
    """

    def __init__(self, ir_arch):
        self.ir_arch = ir_arch
        self.init_passes()

    def init_passes(self):
        """
        Init the arary of simplification passes
        """
        self.passes = [
            self.simplify_ircfg,
            self.do_dead_simp_ircfg,
        ]

    def simplify_ircfg(self, ircfg, _):
        """
        Apply expr_simp on the @ircfg until reaching fix point
        Return True if the graph has been modified

        @ircfg: IRCFG instance to simplify
        """
        log.debug("IRCFG Simplify...")
        has_been_modified = False
        modified = True
        while modified:
            modified = ircfg.simplify(expr_simp)
            has_been_modified |= modified
        log.debug("IRCFG Simplify: %r", has_been_modified)
        return has_been_modified

    def do_dead_simp_ircfg(self, ircfg, head):
        """
        Apply:
        - dead_simp
        - remove_empty_assignblks
        - merge_blocks
        on the @ircfg until reaching fix point
        Return True if the graph has been modified

        @ircfg: IRCFG instance to simplify
        @head: Location instance of the ircfg head
        """
        log.debug("Deads deletion...")
        has_been_modified = False
        modified = True
        while modified:
            modified = dead_simp(self.ir_arch, ircfg)
            modified |= remove_empty_assignblks(ircfg)
            modified |= merge_blocks(ircfg, set([head]))
            has_been_modified |= modified
        log.debug("Deads deletion: %r", has_been_modified)
        return has_been_modified

    def simplify(self, ircfg, head):
        """
        Apply passes until reaching a fix point
        Return True if the graph has been modified

        @ircfg: IRCFG instance to simplify
        @head: Location instance of the ircfg head
        """
        log.debug("Do simplify...")
        has_been_modified = False
        modified = True
        while modified:
            modified = False
            for simplify_pass in self.passes:
                modified |= simplify_pass(ircfg, head)
            has_been_modified |= modified
        log.debug("Do simplify: %r", has_been_modified)
        return has_been_modified


class IRcfgSimplifierSSA(IRcfgSimplifier):
    """
    Simplify an IRCFG.
    The IRCF is first transformed in SSA, then apply transformations passes
    and apply out-of-ssa. Final passes of IRcfgSimplifier are applied

    This class apply following pass until reaching a fix point:
    - propagate_int
    - propagate_mem
    - propagate_expr
    - do_dead_simp_ssa
    """

    def __init__(self, ir_arch):
        super(IRcfgSimplifierSSA, self).__init__(ir_arch)

        self.ir_arch.ssa_var = {}
        self.all_ssa_vars = {}

        self.ssa_forbidden_regs = self.get_forbidden_regs()

        self.propag_int = PropagateExprIntThroughExprId()
        self.propag_expr = PropagateThroughExprId()
        self.propag_mem = PropagateThroughExprMem()

    def get_forbidden_regs(self):
        """
        Return a set of immutable register during SSA transformation
        """
        regs = set(
            [
                self.ir_arch.pc,
                self.ir_arch.IRDst,
                self.ir_arch.arch.regs.exception_flags
            ]
        )
        return regs

    def init_passes(self):
        """
        Init the arary of simplification passes
        """
        self.passes = [
            self.simplify_ssa,
            self.propagate_int,
            self.propagate_mem,
            self.propagate_expr,
            self.do_dead_simp_ssa,
        ]

    def ircfg_to_ssa(self, ircfg, head):
        """
        Apply the SSA transformation to @ircfg using it's @head

        @ircfg: IRCFG instance to simplify
        @head: Location instance of the ircfg head
        """
        ssa = SSADiGraph(ircfg)
        ssa.immutable_ids.update(self.ssa_forbidden_regs)
        ssa.ssa_variable_to_expr.update(self.all_ssa_vars)
        ssa.transform(head)
        self.all_ssa_vars.update(ssa.ssa_variable_to_expr)
        self.ir_arch.ssa_var.update(ssa.ssa_variable_to_expr)
        return ssa

    def ssa_to_unssa(self, ssa, head):
        """
        Apply the out-of-ssa transformation to @ssa using it's @head

        @ssa: SSADiGraph instance
        @head: Location instance of the graph head
        """
        cfg_liveness = DiGraphLivenessSSA(ssa.graph)
        cfg_liveness.init_var_info(self.ir_arch)
        cfg_liveness.compute_liveness()

        UnSSADiGraph(ssa, head, cfg_liveness)
        ircfg = ssa.graph

        ircfg_simplifier = IRcfgSimplifier(self.ir_arch)
        ircfg_simplifier.simplify(ircfg, head)
        return ircfg

    def simplify_ssa(self, ssa, _):
        """
        Apply expr_simp on the @ssa.graph until reaching fix point
        Return True if the graph has been modified

        @ssa: SSADiGraph instance
        """
        log.debug("IRCFG Simplify...")
        has_been_modified = False
        modified = True
        while modified:
            modified = ssa.graph.simplify(expr_simp)
            has_been_modified |= modified
        log.debug("IRCFG Simplify: %r", has_been_modified)
        return has_been_modified

    def propagate_int(self, ssa, head):
        """
        Constant propagation in the @ssa graph
        @head: Location instance of the graph head
        """
        log.debug("Propagate integers...")
        has_been_modified = False
        modified = True
        while modified:
            modified = self.propag_int.propagate(ssa, head)
            modified |= ssa.graph.simplify(expr_simp)
            modified |= del_unused_edges(ssa.graph, set([head]))
            has_been_modified |= modified
        log.debug("Propagate integers: %r", has_been_modified)
        return has_been_modified

    def propagate_mem(self, ssa, head):
        """
        Propagation of expression based on ExprInt/ExprId in the @ssa graph
        @head: Location instance of the graph head
        """
        log.debug("Propagate mem...")
        has_been_modified = False
        modified = True
        while modified:
            modified = self.propag_mem.propagate(ssa, head)
            modified |= ssa.graph.simplify(expr_simp)
            modified |= del_unused_edges(ssa.graph, set([head]))
            has_been_modified |= modified
        log.debug("Propagate mem: %r", has_been_modified)
        return has_been_modified

    def propagate_expr(self, ssa, head):
        """
        Expressions propagation through ExprId in the @ssa graph
        @head: Location instance of the graph head
        """
        index = 0
        log.debug("Propagate expr...")
        has_been_modified = False
        modified = True
        while modified:
            index += 1
            modified = self.propag_expr.propagate(ssa, head, 10000)
            modified |= ssa.graph.simplify(expr_simp)
            modified |= del_unused_edges(ssa.graph, set([head]))
            has_been_modified |= modified
        log.debug("Propagate expr: %r", has_been_modified)
        return has_been_modified

    def do_dead_simp_ssa(self, ssa, head):
        """
        Apply:
        - dead_simp
        - remove_empty_assignblks
        - del_unused_edges
        - merge_blocks
        on the @ircfg until reaching fix point
        Return True if the graph has been modified

        @ircfg: IRCFG instance to simplify
        @head: Location instance of the ircfg head
        """
        log.debug("Deads deletion...")
        has_been_modified = False
        modified = True
        while modified:
            modified = dead_simp(self.ir_arch, ssa.graph)
            modified |= remove_empty_assignblks(ssa.graph)
            modified |= del_unused_edges(ssa.graph, set([head]))
            modified |= merge_blocks(ssa.graph, set([head]))
            has_been_modified |= modified
        log.debug("Deads deletion: %r", has_been_modified)
        return has_been_modified

    def do_simplify(self, ssa, head):
        """
        Apply passes until reaching a fix point
        Return True if the graph has been modified
        """
        log.debug("Do simplify...")
        has_been_modified = False
        modified = True
        while modified:
            modified = False
            for simplify_pass in self.passes:
                modified |= simplify_pass(ssa, head)
            has_been_modified |= modified
        log.debug("Do simplify: %r", has_been_modified)
        return has_been_modified

    def do_simplify_loop(self, ssa, head):
        """
        Apply do_simplify until reaching a fix point
        SSA is updated between each do_simplify
        Return True if the graph has been modified
        """
        modified = True
        while modified:
            modified = self.do_simplify(ssa, head)
            # Update ssa structs
            ssa = self.ircfg_to_ssa(ssa.graph, head)
        return ssa

    def simplify(self, ircfg, head):
        """
        Apply SSA transformation to @ircfg
        Apply passes until reaching a fix point
        Apply out-of-ssa transformation
        Apply post simplification passes

        Return a new simplified IRCFG instance

        @ircfg: IRCFG instance to simplify
        @head: Location instance of the ircfg head
        """
        ssa = self.ircfg_to_ssa(ircfg, head)
        ssa = self.do_simplify_loop(ssa, head)
        ircfg = self.ssa_to_unssa(ssa, head)
        return ircfg
