#-*- coding:utf-8 -*-

#
# Copyright (C) 2013 Fabrice Desclaux
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along
# with this program; if not, write to the Free Software Foundation, Inc.,
# 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
#
from builtins import zip
import warnings

from itertools import chain
from future.utils import viewvalues, viewitems

import miasm.expression.expression as m2_expr
from miasm.expression.expression_helper import get_missing_interval
from miasm.core.asmblock import AsmBlock, AsmBlockBad, AsmConstraint
from miasm.core.graph import DiGraph
from functools import reduce
from miasm_rs import IRBlock
from miasm_rs import AssignBlock

def _expr_loc_to_symb(expr, loc_db):
    if not expr.is_loc():
        return expr
    if loc_db is None:
        name = str(expr)
    else:
        names = loc_db.get_location_names(expr.loc_key)
        if not names:
            name = loc_db.pretty_str(expr.loc_key)
        else:
            # Use only one name for readability
            name = sorted(names)[0]
    return m2_expr.ExprId(name, expr.size)

def slice_rest(expr):
    "Return the completion of the current slice"
    size = expr.arg.size
    if expr.start >= size or expr.stop > size:
        raise ValueError('bad slice rest %s %s %s' %
                         (size, expr.start, expr.stop))

    if expr.start == expr.stop:
        return [(0, size)]

    rest = []
    if expr.start != 0:
        rest.append((0, expr.start))
    if expr.stop < size:
        rest.append((expr.stop, size))

    return rest




class IRCFG(DiGraph):

    """DiGraph for IR instances"""

    def __init__(self, irdst, loc_db, blocks=None, *args, **kwargs):
        """Instantiate a IRCFG
        @loc_db: LocationDB instance
        @blocks: IR blocks
        """
        self.loc_db = loc_db
        if blocks is None:
            blocks = {}
        self._blocks = blocks
        self._irdst = irdst
        super(IRCFG, self).__init__(*args, **kwargs)

    @property
    def IRDst(self):
        return self._irdst

    @property
    def blocks(self):
        return self._blocks

    def add_irblock(self, irblock):
        """
        Add the @irblock to the current IRCFG
        @irblock: IRBlock instance
        """
        self.blocks[irblock.loc_key] = irblock
        self.add_node(irblock.loc_key)

        for dst in self.dst_trackback(irblock):
            if dst.is_int():
                dst_loc_key = self.loc_db.get_or_create_offset_location(int(dst))
                dst = m2_expr.ExprLoc(dst_loc_key, irblock.dst.size)
            if dst.is_loc():
                self.add_uniq_edge(irblock.loc_key, dst.loc_key)

    def node2lines(self, node):
        node_name = self.loc_db.pretty_str(node)
        yield self.DotCellDescription(
            text="%s" % node_name,
            attr={
                'align': 'center',
                'colspan': 2,
                'bgcolor': 'grey',
            }
        )
        if node not in self._blocks:
            yield [self.DotCellDescription(text="NOT PRESENT", attr={'bgcolor': 'red'})]
            return
        for i, assignblk in enumerate(self._blocks[node]):
            for dst, src in viewitems(assignblk):

                new_src = src.visit(lambda expr:_expr_loc_to_symb(expr, self.loc_db))
                new_dst = dst.visit(lambda expr:_expr_loc_to_symb(expr, self.loc_db))
                line = "%s = %s" % (new_dst, new_src)
                if self._dot_offset:
                    yield [self.DotCellDescription(text="%-4d" % i, attr={}),
                           self.DotCellDescription(text=line, attr={})]
                else:
                    yield self.DotCellDescription(text=line, attr={})
            yield self.DotCellDescription(text="", attr={})

    def edge_attr(self, src, dst):
        if src not in self._blocks or dst not in self._blocks:
            return {}
        src_irdst = self._blocks[src].dst
        edge_color = "blue"
        if isinstance(src_irdst, m2_expr.ExprCond):
            src1, src2 = src_irdst.src1, src_irdst.src2
            if src1.is_loc(dst):
                edge_color = "limegreen"
            elif src2.is_loc(dst):
                edge_color = "red"
        return {"color": edge_color}

    def node_attr(self, node):
        if node not in self._blocks:
            return {'style': 'filled', 'fillcolor': 'red'}
        return {}

    def dot(self, offset=False):
        """
        @offset: (optional) if set, add the corresponding line number in each
        node
        """
        self._dot_offset = offset
        return super(IRCFG, self).dot()

    def get_loc_key(self, addr):
        """Transforms an ExprId/ExprInt/loc_key/int into a loc_key
        @addr: an ExprId/ExprInt/loc_key/int"""

        if isinstance(addr, m2_expr.LocKey):
            return addr
        elif isinstance(addr, m2_expr.ExprLoc):
            return addr.loc_key

        try:
            addr = int(addr)
        except (ValueError, TypeError):
            return None

        return self.loc_db.get_offset_location(addr)


    def get_or_create_loc_key(self, addr):
        """Transforms an ExprId/ExprInt/loc_key/int into a loc_key
        If the offset @addr is not in the LocationDB, create it
        @addr: an ExprId/ExprInt/loc_key/int"""

        loc_key = self.get_loc_key(addr)
        if loc_key is not None:
            return loc_key

        return self.loc_db.add_location(offset=int(addr))

    def get_block(self, addr):
        """Returns the irbloc associated to an ExprId/ExprInt/loc_key/int
        @addr: an ExprId/ExprInt/loc_key/int"""

        loc_key = self.get_loc_key(addr)
        if loc_key is None:
            return None
        return self.blocks.get(loc_key, None)

    def getby_offset(self, offset):
        """
        Return the set of loc_keys of irblocks containing @offset
        @offset: address
        """
        out = set()
        for irb in viewvalues(self.blocks):
            for assignblk in irb:
                instr = assignblk.instr
                if instr is None:
                    continue
                if instr.offset <= offset < instr.offset + instr.l:
                    out.add(irb.loc_key)
        return out


    def simplify(self, simplifier):
        """
        Simplify expressions in each irblocks
        @simplifier: ExpressionSimplifier instance
        """
        modified = False
        for loc_key, block in list(viewitems(self.blocks)):
            assignblks = []
            for assignblk in block:
                new_assignblk = assignblk.simplify(simplifier)
                if assignblk != new_assignblk:
                    modified = True
                assignblks.append(new_assignblk)
            self.blocks[loc_key] = IRBlock(self.loc_db, loc_key, assignblks)
        return modified

    def _extract_dst(self, todo, done):
        """
        Naive extraction of @todo destinations
        WARNING: @todo and @done are modified
        """
        out = set()
        while todo:
            dst = todo.pop()
            if dst.is_loc():
                done.add(dst)
            elif dst.is_mem() or dst.is_int():
                done.add(dst)
            elif dst.is_cond():
                todo.add(dst.src1)
                todo.add(dst.src2)
            elif dst.is_id():
                out.add(dst)
            else:
                done.add(dst)
        return out

    def dst_trackback(self, irb):
        """
        Naive backtracking of IRDst
        @irb: irbloc instance
        """
        todo = set([irb.dst])
        done = set()

        for assignblk in reversed(irb):
            if not todo:
                break
            out = self._extract_dst(todo, done)
            found = set()
            follow = set()
            for dst in out:
                if dst in assignblk:
                    follow.add(assignblk[dst])
                    found.add(dst)

            follow.update(out.difference(found))
            todo = follow

        return done


class DiGraphIR(IRCFG):
    """
    DEPRECATED object
    Use IRCFG instead of DiGraphIR
    """

    def __init__(self, *args, **kwargs):
        warnings.warn('DEPRECATION WARNING: use "IRCFG" instead of "DiGraphIR"')
        raise NotImplementedError("Deprecated")


class Lifter(object):
    """
    Intermediate representation object

    Allow native assembly to intermediate representation traduction
    """

    def __init__(self, arch, attrib, loc_db):
        self.pc = arch.getpc(attrib)
        self.sp = arch.getsp(attrib)
        self.arch = arch
        self.attrib = attrib
        self.loc_db = loc_db
        self.IRDst = None

    def get_ir(self, instr):
        raise NotImplementedError("Abstract Method")

    def new_ircfg(self, *args, **kwargs):
        """
        Return a new instance of IRCFG
        """
        return IRCFG(self.IRDst, self.loc_db, *args, **kwargs)

    def new_ircfg_from_asmcfg(self, asmcfg, *args, **kwargs):
        """
        Return a new instance of IRCFG from an @asmcfg
        @asmcfg: AsmCFG instance
        """

        ircfg = IRCFG(self.IRDst, self.loc_db, *args, **kwargs)
        for block in asmcfg.blocks:
            self.add_asmblock_to_ircfg(block, ircfg)
        return ircfg

    def instr2ir(self, instr):
        ir_bloc_cur, extra_irblocks = self.get_ir(instr)
        for index, irb in enumerate(extra_irblocks):
            irs = []
            for assignblk in irb:
                irs.append(AssignBlock(assignblk, instr))
            extra_irblocks[index] = IRBlock(self.loc_db, irb.loc_key, irs)
        assignblk = AssignBlock(ir_bloc_cur, instr)
        return assignblk, extra_irblocks

    def add_instr_to_ircfg(self, instr, ircfg, loc_key=None, gen_pc_updt=False):
        """
        Add the native instruction @instr to the @ircfg
        @instr: instruction instance
        @ircfg: IRCFG instance
        @loc_key: loc_key instance of the instruction destination
        @gen_pc_updt: insert PC update effects between instructions
        """

        if loc_key is None:
            offset = getattr(instr, "offset", None)
            loc_key = self.loc_db.get_or_create_offset_location(offset)
        block = AsmBlock(self.loc_db, loc_key)
        block.lines = [instr]
        self.add_asmblock_to_ircfg(block, ircfg, gen_pc_updt)
        return loc_key

    def gen_pc_update(self, assignments, instr):
        offset = m2_expr.ExprInt(instr.offset, self.pc.size)
        assignments.append(AssignBlock({self.pc:offset}, instr))

    def add_instr_to_current_state(self, instr, block, assignments, ir_blocks_all, gen_pc_updt):
        """
        Add the IR effects of an instruction to the current state.

        Returns a bool:
        * True if the current assignments list must be split
        * False in other cases.

        @instr: native instruction
        @block: native block source
        @assignments: list of current AssignBlocks
        @ir_blocks_all: list of additional effects
        @gen_pc_updt: insert PC update effects between instructions
        """
        if gen_pc_updt is not False:
            self.gen_pc_update(assignments, instr)

        assignblk, ir_blocks_extra = self.instr2ir(instr)
        assignments.append(assignblk)
        ir_blocks_all += ir_blocks_extra
        if ir_blocks_extra:
            return True
        return False

    def add_asmblock_to_ircfg(self, block, ircfg, gen_pc_updt=False):
        """
        Add a native block to the current IR
        @block: native assembly block
        @ircfg: IRCFG instance
        @gen_pc_updt: insert PC update effects between instructions
        """

        loc_key = block.loc_key
        ir_blocks_all = []

        if isinstance(block, AsmBlockBad):
            return ir_blocks_all

        assignments = []
        for instr in block.lines:
            if loc_key is None:
                assignments = []
                loc_key = self.get_loc_key_for_instr(instr)
            split = self.add_instr_to_current_state(
                instr, block, assignments,
                ir_blocks_all, gen_pc_updt
            )
            if split:
                ir_blocks_all.append(IRBlock(self.loc_db, loc_key, assignments))
                loc_key = None
                assignments = []
        if loc_key is not None:
            ir_blocks_all.append(IRBlock(self.loc_db, loc_key, assignments))

        new_ir_blocks_all = self.post_add_asmblock_to_ircfg(block, ircfg, ir_blocks_all)
        for irblock in new_ir_blocks_all:
            ircfg.add_irblock(irblock)
        return new_ir_blocks_all

    def add_block(self, block, gen_pc_updt=False):
        """
        DEPRECATED function
        Use add_asmblock_to_ircfg instead of add_block
        """
        warnings.warn("""DEPRECATION WARNING
        ircfg is now out of Lifter
        Use:
        ircfg = lifter.new_ircfg()
        lifter.add_asmblock_to_ircfg(block, ircfg)
        """)
        raise RuntimeError("API Deprecated")

    def add_bloc(self, block, gen_pc_updt=False):
        """
        DEPRECATED function
        Use add_asmblock_to_ircfg instead of add_bloc
        """
        self.add_block(block, gen_pc_updt)

    def get_next_loc_key(self, instr):
        loc_key = self.loc_db.get_or_create_offset_location(instr.offset + instr.l)
        return loc_key

    def get_loc_key_for_instr(self, instr):
        """Returns the loc_key associated to an instruction
        @instr: current instruction"""
        return self.loc_db.get_or_create_offset_location(instr.offset)

    def gen_loc_key_and_expr(self, size):
        """
        Return a loc_key and it's corresponding ExprLoc
        @size: size of expression
        """
        loc_key = self.loc_db.add_location()
        return loc_key, m2_expr.ExprLoc(loc_key, size)

    def expr_fix_regs_for_mode(self, expr, *args, **kwargs):
        return expr

    def expraff_fix_regs_for_mode(self, expr, *args, **kwargs):
        return expr

    def irbloc_fix_regs_for_mode(self, irblock, *args, **kwargs):
        return irblock

    def is_pc_written(self, block):
        """Return the first Assignblk of the @block in which PC is written
        @block: IRBlock instance"""
        all_pc = viewvalues(self.arch.pc)
        for assignblk in block:
            if assignblk.dst in all_pc:
                return assignblk
        return None

    def set_empty_dst_to_next(self, block, ir_blocks):
        for index, irblock in enumerate(ir_blocks):
            if irblock.dst is not None:
                continue
            next_loc_key = block.get_next()
            if next_loc_key is None:
                loc_key = None
                if block.lines:
                    line = block.lines[-1]
                    if line.offset is not None:
                        loc_key = self.loc_db.get_or_create_offset_location(line.offset + line.l)
                if loc_key is None:
                    loc_key = self.loc_db.add_location()
                block.add_cst(loc_key, AsmConstraint.c_next)
            else:
                loc_key = next_loc_key
            dst = m2_expr.ExprLoc(loc_key, self.pc.size)
            if irblock.assignblks:
                instr = irblock.assignblks[-1].instr
            else:
                instr = None
            assignblk = AssignBlock({self.IRDst: dst}, instr)
            ir_blocks[index] = IRBlock(self.loc_db, irblock.loc_key, list(irblock.assignblks) + [assignblk])

    def post_add_asmblock_to_ircfg(self, block, ircfg, ir_blocks):
        self.set_empty_dst_to_next(block, ir_blocks)

        new_irblocks = []
        for irblock in ir_blocks:
            new_irblock = self.irbloc_fix_regs_for_mode(irblock, self.attrib)
            ircfg.add_irblock(new_irblock)
            new_irblocks.append(new_irblock)
        return new_irblocks


class IntermediateRepresentation(Lifter):
    """
    DEPRECATED object
    Use Lifter instead of IntermediateRepresentation
    """

    def __init__(self, arch, attrib, loc_db):
        warnings.warn('DEPRECATION WARNING: use "Lifter" instead of "IntermediateRepresentation"')
        super(IntermediateRepresentation, self).__init__(arch, attrib, loc_db)


class ir(Lifter):
    """
    DEPRECATED object
    Use Lifter instead of ir
    """

    def __init__(self, loc_key, irs, lines=None):
        warnings.warn('DEPRECATION WARNING: use "Lifter" instead of "ir"')
        super(ir, self).__init__(loc_key, irs, lines)
