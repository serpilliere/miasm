#
# Copyright (C) 2011 EADS France, Fabrice Desclaux <fabrice.desclaux@eads.net>
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
# These module implements Miasm IR components and basic operations related.
# IR components are :
#  - ExprInt
#  - ExprId
#  - ExprLoc
#  - ExprAssign
#  - ExprCond
#  - ExprMem
#  - ExprOp
#  - ExprSlice
#  - ExprCompose
#


from builtins import zip
from builtins import range
import warnings
import itertools
from builtins import int as int_types
from functools import cmp_to_key, total_ordering
from future.utils import viewitems

from miasm.core.locationdb import LocKey
from miasm.core.utils import force_bytes, cmp_elts
from miasm.core.graph import DiGraph
from functools import reduce


from miasm_rs import ExprId, ExprInt, ExprLoc, ExprMem, \
    ExprSlice, ExprCond, ExprCompose, ExprOp, ExprAssign


# Define tokens
TOK_INF = "<"
TOK_INF_SIGNED = TOK_INF + "s"
TOK_INF_UNSIGNED = TOK_INF + "u"
TOK_INF_EQUAL = "<="
TOK_INF_EQUAL_SIGNED = TOK_INF_EQUAL + "s"
TOK_INF_EQUAL_UNSIGNED = TOK_INF_EQUAL + "u"
TOK_EQUAL = "=="
TOK_POS = "pos"
TOK_POS_STRICT = "Spos"

# Hashing constants
EXPRINT = 1
EXPRID = 2
EXPRLOC = 3
EXPRASSIGN = 4
EXPRCOND = 5
EXPRMEM = 6
EXPROP = 7
EXPRSLICE = 8
EXPRCOMPOSE = 9


priorities_list = [
    [ '+' ],
    [ '*', '/', '%'  ],
    [ '**' ],
    [ '-' ],	# Unary '-', associativity with + not handled
]

# dictionary from 'op' to priority, derived from above
priorities = dict((op, prio)
                  for prio, l in enumerate(priorities_list)
                  for op in l)
PRIORITY_MAX = len(priorities_list) - 1

def should_parenthesize_child(child, parent):
    if (isinstance(child, ExprId) or isinstance(child, ExprInt) or
        isinstance(child, ExprCompose) or isinstance(child, ExprMem) or
        isinstance(child, ExprSlice)):
        return False
    elif isinstance(child, ExprOp) and not child.is_infix():
        return False
    elif (isinstance(child, ExprCond) or isinstance(parent, ExprSlice)):
        return True
    elif (isinstance(child, ExprOp) and isinstance(parent, ExprOp)):
        pri_child = priorities.get(child.op, -1)
        pri_parent = priorities.get(parent.op, PRIORITY_MAX + 1)
        return pri_child < pri_parent
    else:
        return True

def str_protected_child(child, parent):
    return ("(%s)" % child) if should_parenthesize_child(child, parent) else str(child)


# Expression display


class DiGraphExpr(DiGraph):

    """Enhanced graph for Expression display
    Expression are displayed as a tree with node and edge labeled
    with only relevant information"""

    def node2str(self, node):
        if isinstance(node, ExprOp):
            return node.op
        elif isinstance(node, ExprId):
            return node.name
        elif isinstance(node, ExprLoc):
            return "%s" % node.loc_key
        elif isinstance(node, ExprMem):
            return "@%d" % node.size
        elif isinstance(node, ExprCompose):
            return "{ %d }" % node.size
        elif isinstance(node, ExprCond):
            return "? %d" % node.size
        elif isinstance(node, ExprSlice):
            return "[%d:%d]" % (node.start, node.stop)
        return str(node)

    def edge2str(self, nfrom, nto):
        if isinstance(nfrom, ExprCompose):
            for i in nfrom.args:
                if i[0] == nto:
                    return "[%s, %s]" % (i[1], i[2])
        elif isinstance(nfrom, ExprCond):
            if nfrom.cond == nto:
                return "?"
            elif nfrom.src1 == nto:
                return "True"
            elif nfrom.src2 == nto:
                return "False"

        return ""

def is_expr(expr):
    return isinstance(
        expr,
        (
            ExprInt, ExprId, ExprMem,
            ExprSlice, ExprCompose, ExprCond,
            ExprLoc, ExprOp
        )
    )

def is_associative(expr):
    "Return True iff current operation is associative"
    return (expr.op in ['+', '*', '^', '&', '|'])

def is_commutative(expr):
    "Return True iff current operation is commutative"
    return (expr.op in ['+', '*', '^', '&', '|'])

def canonize_to_exprloc(locdb, expr):
    """
    If expr is ExprInt, return ExprLoc with corresponding loc_key
    Else, return expr

    @expr: Expr instance
    """
    if expr.is_int():
        loc_key = locdb.get_or_create_offset_location(int(expr))
        ret = ExprLoc(loc_key, expr.size)
        return ret
    return expr

def is_function_call(expr):
    """Returns true if the considered Expr is a function call
    """
    return expr.is_op() and expr.op.startswith('call')



class ExprWalkBase(object):
    """
    Walk through sub-expressions, call @callback on them.
    If @callback returns a non None value, stop walk and return this value
    """

    def __init__(self, callback):
        self.callback = callback

    def visit(self, expr, *args, **kwargs):
        if expr.is_int() or expr.is_id() or expr.is_loc():
            pass
        elif expr.is_assign():
            ret = self.visit(expr.dst, *args, **kwargs)
            if ret:
                return ret
            src = self.visit(expr.src, *args, **kwargs)
            if ret:
                return ret
        elif expr.is_cond():
            ret = self.visit(expr.cond, *args, **kwargs)
            if ret:
                return ret
            ret = self.visit(expr.src1, *args, **kwargs)
            if ret:
                return ret
            ret = self.visit(expr.src2, *args, **kwargs)
            if ret:
                return ret
        elif expr.is_mem():
            ret = self.visit(expr.ptr, *args, **kwargs)
            if ret:
                return ret
        elif expr.is_slice():
            ret = self.visit(expr.arg, *args, **kwargs)
            if ret:
                return ret
        elif expr.is_op():
            for arg in expr.args:
                ret = self.visit(arg, *args, **kwargs)
                if ret:
                    return ret
        elif expr.is_compose():
            for arg in expr.args:
                ret = self.visit(arg, *args, **kwargs)
                if ret:
                    return ret
        else:
            raise TypeError("Visitor can only take Expr")

        ret = self.callback(expr, *args, **kwargs)
        return ret


class ExprWalk(ExprWalkBase):
    """
    Walk through sub-expressions, call @callback on them.
    If @callback returns a non None value, stop walk and return this value
    Use cache mechanism.
    """
    def __init__(self, callback):
        self.cache = set()
        self.callback = callback

    def visit(self, expr, *args, **kwargs):
        if expr in self.cache:
            return None
        ret = super(ExprWalk, self).visit(expr, *args, **kwargs)
        if ret:
            return ret
        self.cache.add(expr)
        return None


class ExprGetR(ExprWalkBase):
    """
    Return ExprId/ExprMem used by a given expression
    """
    def __init__(self, mem_read=False, cst_read=False):
        super(ExprGetR, self).__init__(lambda x:None)
        self.mem_read = mem_read
        self.cst_read = cst_read
        self.elements = set()
        self.cache = dict()

    def get_r_leaves(self, expr):
        if (expr.is_int() or expr.is_loc()) and self.cst_read:
            self.elements.add(expr)
        elif expr.is_mem():
            self.elements.add(expr)
        elif expr.is_id():
            self.elements.add(expr)

    def visit(self, expr, *args, **kwargs):
        cache_key = (expr, self.mem_read, self.cst_read)
        if cache_key in self.cache:
            return self.cache[cache_key]
        ret = self.visit_inner(expr, *args, **kwargs)
        self.cache[cache_key] = ret
        return ret

    def visit_inner(self, expr, *args, **kwargs):
        self.get_r_leaves(expr)
        if expr.is_mem() and not self.mem_read:
            # Don't visit memory sons
            return None

        if expr.is_assign():
            if expr.dst.is_mem() and self.mem_read:
                ret = super(ExprGetR, self).visit(expr.dst, *args, **kwargs)
            if expr.src.is_mem():
                self.elements.add(expr.src)
            self.get_r_leaves(expr.src)
            if expr.src.is_mem() and not self.mem_read:
                return None
            ret = super(ExprGetR, self).visit(expr.src, *args, **kwargs)
            return ret
        ret = super(ExprGetR, self).visit(expr, *args, **kwargs)
        return ret


class ExprVisitorBase(object):
    """
    Rebuild expression by visiting sub-expressions
    """
    def visit(self, expr, *args, **kwargs):
        if expr.is_int() or expr.is_id() or expr.is_loc():
            ret = expr
        elif expr.is_assign():
            dst = self.visit(expr.dst, *args, **kwargs)
            src = self.visit(expr.src, *args, **kwargs)
            ret = ExprAssign(dst, src)
        elif expr.is_cond():
            cond = self.visit(expr.cond, *args, **kwargs)
            src1 = self.visit(expr.src1, *args, **kwargs)
            src2 = self.visit(expr.src2, *args, **kwargs)
            ret = ExprCond(cond, src1, src2)
        elif expr.is_mem():
            ptr = self.visit(expr.ptr, *args, **kwargs)
            ret = ExprMem(ptr, expr.size)
        elif expr.is_slice():
            arg = self.visit(expr.arg, *args, **kwargs)
            ret = ExprSlice(arg, expr.start, expr.stop)
        elif expr.is_op():
            args = [self.visit(arg, *args, **kwargs) for arg in expr.args]
            ret = ExprOp(expr.op, *args)
        elif expr.is_compose():
            args = [self.visit(arg, *args, **kwargs) for arg in expr.args]
            ret = ExprCompose(*args)
        else:
            raise TypeError("Visitor can only take Expr")
        return ret


class ExprVisitorCallbackTopToBottom(ExprVisitorBase):
    """
    Rebuild expression by visiting sub-expressions
    Call @callback on each sub-expression
    if @callback return non None value, replace current node with this value
    Else, continue visit of sub-expressions
    """
    def __init__(self, callback):
        super(ExprVisitorCallbackTopToBottom, self).__init__()
        self.cache = dict()
        self.callback = callback

    def visit(self, expr, *args, **kwargs):
        if expr in self.cache:
            return self.cache[expr]
        ret = self.visit_inner(expr, *args, **kwargs)
        self.cache[expr] = ret
        return ret

    def visit_inner(self, expr, *args, **kwargs):
        ret = self.callback(expr)
        if ret:
            return ret
        ret = super(ExprVisitorCallbackTopToBottom, self).visit(expr, *args, **kwargs)
        return ret


class ExprVisitorCallbackBottomToTop(ExprVisitorBase):
    """
    Rebuild expression by visiting sub-expressions
    Call @callback from leaves to root expressions
    """
    def __init__(self, callback):
        super(ExprVisitorCallbackBottomToTop, self).__init__()
        self.cache = dict()
        self.callback = callback

    def visit(self, expr, *args, **kwargs):
        if expr in self.cache:
            return self.cache[expr]
        ret = self.visit_inner(expr, *args, **kwargs)
        self.cache[expr] = ret
        return ret

    def visit_inner(self, expr, *args, **kwargs):
        ret = super(ExprVisitorCallbackBottomToTop, self).visit(expr, *args, **kwargs)
        ret = self.callback(ret)
        return ret


class ExprVisitorCanonize(ExprVisitorCallbackBottomToTop):
    def __init__(self):
        super(ExprVisitorCanonize, self).__init__(self.canonize)

    def canonize(self, expr):
        if not expr.is_op():
            return expr
        if not expr.is_associative():
            return expr

        # ((a+b) + c) => (a + b + c)
        args = []
        for arg in expr.args:
            if isinstance(arg, ExprOp) and expr.op == arg.op:
                args += arg.args
            else:
                args.append(arg)
        args = canonize_expr_list(args)
        new_expr = ExprOp(expr.op, *args)
        return new_expr


class ExprVisitorContains(ExprWalkBase):
    """
    Visitor to test if a needle is in an Expression
    Cache results
    """
    def __init__(self):
        self.cache = set()
        super(ExprVisitorContains, self).__init__(self.eq_expr)

    def eq_expr(self, expr, needle, *args, **kwargs):
        if expr == needle:
            return True
        return None

    def visit(self, expr, needle,  *args, **kwargs):
        if (expr, needle) in self.cache:
            return None
        ret = super(ExprVisitorContains, self).visit(expr, needle, *args, **kwargs)
        if ret:
            return ret
        self.cache.add((expr, needle))
        return None


    def contains(self, expr, needle):
        return self.visit(expr, needle)


# Expression order for comparison
EXPR_ORDER_DICT = {
    ExprId: 1,
    ExprLoc: 2,
    ExprCond: 3,
    ExprMem: 4,
    ExprOp: 5,
    ExprSlice: 6,
    ExprCompose: 7,
    ExprInt: 8,
}


def compare_exprs_compose(expr1, expr2):
    # Sort by start bit address, then expr, then stop bit address
    ret = cmp_elts(expr1[1], expr2[1])
    if ret:
        return ret
    ret = compare_exprs(expr1[0], expr2[0])
    if ret:
        return ret
    ret = cmp_elts(expr1[2], expr2[2])
    return ret


def compare_expr_list_compose(l1_e, l2_e):
    # Sort by list elements in incremental order, then by list size
    for i in range(min(len(l1_e), len(l2_e))):
        ret = compare_exprs(l1_e[i], l2_e[i])
        if ret:
            return ret
    return cmp_elts(len(l1_e), len(l2_e))


def compare_expr_list(l1_e, l2_e):
    # Sort by list elements in incremental order, then by list size
    for i in range(min(len(l1_e), len(l2_e))):
        ret = compare_exprs(l1_e[i], l2_e[i])
        if ret:
            return ret
    return cmp_elts(len(l1_e), len(l2_e))


def compare_exprs(expr1, expr2):
    """Compare 2 expressions for canonization
    @expr1: Expr
    @expr2: Expr
    0  => ==
    1  => expr1 > expr2
    -1 => expr1 < expr2
    """
    cls1 = expr1.__class__
    cls2 = expr2.__class__
    if cls1 != cls2:
        return cmp_elts(EXPR_ORDER_DICT[cls1], EXPR_ORDER_DICT[cls2])
    if expr1 == expr2:
        return 0
    if cls1 == ExprInt:
        ret = cmp_elts(expr1.size, expr2.size)
        if ret != 0:
            return ret
        return cmp_elts(expr1.arg, expr2.arg)
    elif cls1 == ExprId:
        name1 = force_bytes(expr1.name)
        name2 = force_bytes(expr2.name)
        ret = cmp_elts(name1, name2)
        if ret:
            return ret
        return cmp_elts(expr1.size, expr2.size)
    elif cls1 == ExprLoc:
        ret = cmp_elts(expr1.loc_key, expr2.loc_key)
        if ret:
            return ret
        return cmp_elts(expr1.size, expr2.size)
    elif cls1 == ExprAssign:
        raise NotImplementedError(
            "Comparison from an ExprAssign not yet implemented"
        )
    elif cls2 == ExprCond:
        ret = compare_exprs(expr1.cond, expr2.cond)
        if ret:
            return ret
        ret = compare_exprs(expr1.src1, expr2.src1)
        if ret:
            return ret
        ret = compare_exprs(expr1.src2, expr2.src2)
        return ret
    elif cls1 == ExprMem:
        ret = compare_exprs(expr1.ptr, expr2.ptr)
        if ret:
            return ret
        return cmp_elts(expr1.size, expr2.size)
    elif cls1 == ExprOp:
        if expr1.op != expr2.op:
            return cmp_elts(expr1.op, expr2.op)
        return compare_expr_list(expr1.args, expr2.args)
    elif cls1 == ExprSlice:
        ret = compare_exprs(expr1.arg, expr2.arg)
        if ret:
            return ret
        ret = cmp_elts(expr1.start, expr2.start)
        if ret:
            return ret
        ret = cmp_elts(expr1.stop, expr2.stop)
        return ret
    elif cls1 == ExprCompose:
        return compare_expr_list_compose(expr1.args, expr2.args)
    raise NotImplementedError(
        "Comparison between %r %r not implemented" % (expr1, expr2)
    )


def canonize_expr_list(expr_list):
    return sorted(expr_list, key=cmp_to_key(compare_exprs))


def canonize_expr_list_compose(expr_list):
    return sorted(expr_list, key=cmp_to_key(compare_exprs_compose))

# Generate ExprInt with common size


def ExprInt1(i):
    warnings.warn('DEPRECATION WARNING: use ExprInt(i, 1) instead of '\
                  'ExprInt1(i))')
    return ExprInt(i, 1)


def ExprInt8(i):
    warnings.warn('DEPRECATION WARNING: use ExprInt(i, 8) instead of '\
                  'ExprInt8(i))')
    return ExprInt(i, 8)


def ExprInt16(i):
    warnings.warn('DEPRECATION WARNING: use ExprInt(i, 16) instead of '\
                  'ExprInt16(i))')
    return ExprInt(i, 16)


def ExprInt32(i):
    warnings.warn('DEPRECATION WARNING: use ExprInt(i, 32) instead of '\
                  'ExprInt32(i))')
    return ExprInt(i, 32)


def ExprInt64(i):
    warnings.warn('DEPRECATION WARNING: use ExprInt(i, 64) instead of '\
                  'ExprInt64(i))')
    return ExprInt(i, 64)


def ExprInt_from(expr, i):
    "Generate ExprInt with size equal to expression"
    warnings.warn('DEPRECATION WARNING: use ExprInt(i, expr.size) instead of'\
                  'ExprInt_from(expr, i))')
    return ExprInt(i, expr.size)


def get_expr_ids_visit(expr, ids):
    """Visitor to retrieve ExprId in @expr
    @expr: Expr"""
    if expr.is_id():
        ids.add(expr)
    return expr


def get_expr_locs_visit(expr, locs):
    """Visitor to retrieve ExprLoc in @expr
    @expr: Expr"""
    if expr.is_loc():
        locs.add(expr)
    return expr


def get_expr_ids(expr):
    """Retrieve ExprId in @expr
    @expr: Expr"""
    ids = set()
    expr.visit(lambda x: get_expr_ids_visit(x, ids))
    return ids


def get_expr_locs(expr):
    """Retrieve ExprLoc in @expr
    @expr: Expr"""
    locs = set()
    expr.visit(lambda x: get_expr_locs_visit(x, locs))
    return locs


def test_set(expr, pattern, tks, result):
    """Test if v can correspond to e. If so, update the context in result.
    Otherwise, return False
    @expr : Expr to match
    @pattern : pattern Expr
    @tks : list of ExprId, available jokers
    @result : dictionary of ExprId -> Expr, current context
    """

    if not pattern in tks:
        return expr == pattern
    if pattern in result and result[pattern] != expr:
        return False
    result[pattern] = expr
    return result


def match_expr(expr, pattern, tks, result=None):
    """Try to match the @pattern expression with the pattern @expr with @tks jokers.
    Result is output dictionary with matching joker values.
    @expr : Expr pattern
    @pattern : Targeted Expr to match
    @tks : list of ExprId, available jokers
    @result : dictionary of ExprId -> Expr, output matching context
    """

    if result is None:
        result = {}

    if pattern in tks:
        # pattern is a Joker
        return test_set(expr, pattern, tks, result)

    if expr.is_int():
        return test_set(expr, pattern, tks, result)

    elif expr.is_id():
        return test_set(expr, pattern, tks, result)

    elif expr.is_loc():
        return test_set(expr, pattern, tks, result)

    elif expr.is_op():

        # expr need to be the same operation than pattern
        if not pattern.is_op():
            return False
        if expr.op != pattern.op:
            return False
        if len(expr.args) != len(pattern.args):
            return False

        # Perform permutation only if the current operation is commutative
        if is_commutative(expr):
            permutations = itertools.permutations(expr.args)
        else:
            permutations = [expr.args]

        # For each permutations of arguments
        for permut in permutations:
            good = True
            # We need to use a copy of result to not override it
            myresult = dict(result)
            for sub_expr, sub_pattern in zip(permut, pattern.args):
                ret = match_expr(sub_expr, sub_pattern, tks, myresult)
                # If the current permutation do not match EVERY terms
                if ret is False:
                    good = False
                    break
            if good is True:
                # We found a possibility
                for joker, value in viewitems(myresult):
                    # Updating result in place (to keep pointer in recursion)
                    result[joker] = value
                return result
        return False

    # Recursive tests

    elif expr.is_mem():
        if not pattern.is_mem():
            return False
        if expr.size != pattern.size:
            return False
        return match_expr(expr.ptr, pattern.ptr, tks, result)

    elif expr.is_slice():
        if not pattern.is_slice():
            return False
        if expr.start != pattern.start or expr.stop != pattern.stop:
            return False
        return match_expr(expr.arg, pattern.arg, tks, result)

    elif expr.is_cond():
        if not pattern.is_cond():
            return False
        if match_expr(expr.cond, pattern.cond, tks, result) is False:
            return False
        if match_expr(expr.src1, pattern.src1, tks, result) is False:
            return False
        if match_expr(expr.src2, pattern.src2, tks, result) is False:
            return False
        return result

    elif expr.is_compose():
        if not pattern.is_compose():
            return False
        for sub_expr, sub_pattern in zip(expr.args, pattern.args):
            if  match_expr(sub_expr, sub_pattern, tks, result) is False:
                return False
        return result

    elif expr.is_assign():
        if not pattern.is_assign():
            return False
        if match_expr(expr.src, pattern.src, tks, result) is False:
            return False
        if match_expr(expr.dst, pattern.dst, tks, result) is False:
            return False
        return result

    else:
        raise NotImplementedError("match_expr: Unknown type: %s" % type(expr))


def MatchExpr(expr, pattern, tks, result=None):
    warnings.warn('DEPRECATION WARNING: use match_expr instead of MatchExpr')
    return match_expr(expr, pattern, tks, result)


def get_rw(exprs):
    o_r = set()
    o_w = set()
    for expr in exprs:
        o_r.update(expr.get_r(mem_read=True))
    for expr in exprs:
        o_w.update(expr.get_w())
    return o_r, o_w


def get_list_rw(exprs, mem_read=False, cst_read=True):
    """Return list of read/write reg/cst/mem for each @exprs
    @exprs: list of expressions
    @mem_read: walk though memory accesses
    @cst_read: retrieve constants
    """
    list_rw = []
    # cst_num = 0
    for expr in exprs:
        o_r = set()
        o_w = set()
        # get r/w
        o_r.update(expr.get_r(mem_read=mem_read, cst_read=cst_read))
        if isinstance(expr.dst, ExprMem):
            o_r.update(expr.dst.arg.get_r(mem_read=mem_read, cst_read=cst_read))
        o_w.update(expr.get_w())
        # each cst is indexed
        o_r_rw = set()
        for read in o_r:
            o_r_rw.add(read)
        o_r = o_r_rw
        list_rw.append((o_r, o_w))

    return list_rw


def get_expr_ops(expr):
    """Retrieve operators of an @expr
    @expr: Expr"""
    def visit_getops(expr, out=None):
        if out is None:
            out = set()
        if isinstance(expr, ExprOp):
            out.add(expr.op)
        return expr
    ops = set()
    expr.visit(lambda x: visit_getops(x, ops))
    return ops


def get_expr_mem(expr):
    """Retrieve memory accesses of an @expr
    @expr: Expr"""
    def visit_getmem(expr, out=None):
        if out is None:
            out = set()
        if isinstance(expr, ExprMem):
            out.add(expr)
        return expr
    ops = set()
    expr.visit(lambda x: visit_getmem(x, ops))
    return ops


def _expr_compute_cf(op1, op2):
    """
    Get carry flag of @op1 - @op2
    Ref: x86 cf flag
    @op1: Expression
    @op2: Expression
    """
    res = op1 - op2
    cf = (((op1 ^ op2) ^ res) ^ ((op1 ^ res) & (op1 ^ op2))).msb()
    return cf

def _expr_compute_of(op1, op2):
    """
    Get overflow flag of @op1 - @op2
    Ref: x86 of flag
    @op1: Expression
    @op2: Expression
    """
    res = op1 - op2
    of = (((op1 ^ res) & (op1 ^ op2))).msb()
    return of

def _expr_compute_zf(op1, op2):
    """
    Get zero flag of @op1 - @op2
    @op1: Expression
    @op2: Expression
    """
    res = op1 - op2
    zf = ExprCond(res,
                  ExprInt(0, 1),
                  ExprInt(1, 1))
    return zf


def _expr_compute_nf(op1, op2):
    """
    Get negative (or sign) flag of @op1 - @op2
    @op1: Expression
    @op2: Expression
    """
    res = op1 - op2
    nf = res.msb()
    return nf


def expr_is_equal(op1, op2):
    """
    if op1 == op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    zf = _expr_compute_zf(op1, op2)
    return zf


def expr_is_not_equal(op1, op2):
    """
    if op1 != op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    zf = _expr_compute_zf(op1, op2)
    return ~zf


def expr_is_unsigned_greater(op1, op2):
    """
    UNSIGNED cmp
    if op1 > op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    cf = _expr_compute_cf(op1, op2)
    zf = _expr_compute_zf(op1, op2)
    return ~(cf | zf)


def expr_is_unsigned_greater_or_equal(op1, op2):
    """
    Unsigned cmp
    if op1 >= op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    cf = _expr_compute_cf(op1, op2)
    return ~cf


def expr_is_unsigned_lower(op1, op2):
    """
    Unsigned cmp
    if op1 < op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    cf = _expr_compute_cf(op1, op2)
    return cf


def expr_is_unsigned_lower_or_equal(op1, op2):
    """
    Unsigned cmp
    if op1 <= op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    cf = _expr_compute_cf(op1, op2)
    zf = _expr_compute_zf(op1, op2)
    return cf | zf


def expr_is_signed_greater(op1, op2):
    """
    Signed cmp
    if op1 > op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    nf = _expr_compute_nf(op1, op2)
    of = _expr_compute_of(op1, op2)
    zf = _expr_compute_zf(op1, op2)
    return ~(zf | (nf ^ of))


def expr_is_signed_greater_or_equal(op1, op2):
    """
    Signed cmp
    if op1 > op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    nf = _expr_compute_nf(op1, op2)
    of = _expr_compute_of(op1, op2)
    return ~(nf ^ of)


def expr_is_signed_lower(op1, op2):
    """
    Signed cmp
    if op1 < op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    nf = _expr_compute_nf(op1, op2)
    of = _expr_compute_of(op1, op2)
    return nf ^ of


def expr_is_signed_lower_or_equal(op1, op2):
    """
    Signed cmp
    if op1 <= op2:
       Return ExprInt(1, 1)
    else:
       Return ExprInt(0, 1)
    """

    nf = _expr_compute_nf(op1, op2)
    of = _expr_compute_of(op1, op2)
    zf = _expr_compute_zf(op1, op2)
    return zf | (nf ^ of)

# sign bit | exponent | significand
size_to_IEEE754_info = {
    16: {
        "exponent": 5,
        "significand": 10,
    },
    32: {
        "exponent": 8,
        "significand": 23,
    },
    64: {
        "exponent": 11,
        "significand": 52,
    },
}

def expr_is_NaN(expr):
    """Return 1 or 0 on 1 bit if expr represent a NaN value according to IEEE754
    """
    info = size_to_IEEE754_info[expr.size]
    exponent = expr[info["significand"]: info["significand"] + info["exponent"]]

    # exponent is full of 1s and significand is not NULL
    return ExprCond(exponent - ExprInt(-1, exponent.size),
                    ExprInt(0, 1),
                    ExprCond(expr[:info["significand"]], ExprInt(1, 1),
                             ExprInt(0, 1)))


def expr_is_infinite(expr):
    """Return 1 or 0 on 1 bit if expr represent an infinite value according to
    IEEE754
    """
    info = size_to_IEEE754_info[expr.size]
    exponent = expr[info["significand"]: info["significand"] + info["exponent"]]

    # exponent is full of 1s and significand is NULL
    return ExprCond(exponent - ExprInt(-1, exponent.size),
                    ExprInt(0, 1),
                    ExprCond(expr[:info["significand"]], ExprInt(0, 1),
                             ExprInt(1, 1)))


def expr_is_IEEE754_zero(expr):
    """Return 1 or 0 on 1 bit if expr represent a zero value according to
    IEEE754
    """
    # Sign is the msb
    expr_no_sign = expr[:expr.size - 1]
    return ExprCond(expr_no_sign, ExprInt(0, 1), ExprInt(1, 1))


def expr_is_IEEE754_denormal(expr):
    """Return 1 or 0 on 1 bit if expr represent a denormalized value according
    to IEEE754
    """
    info = size_to_IEEE754_info[expr.size]
    exponent = expr[info["significand"]: info["significand"] + info["exponent"]]
    # exponent is full of 0s
    return ExprCond(exponent, ExprInt(0, 1), ExprInt(1, 1))


def expr_is_qNaN(expr):
    """Return 1 or 0 on 1 bit if expr represent a qNaN (quiet) value according to
    IEEE754
    """
    info = size_to_IEEE754_info[expr.size]
    significand_top = expr[info["significand"]: info["significand"] + 1]
    return expr_is_NaN(expr) & significand_top


def expr_is_sNaN(expr):
    """Return 1 or 0 on 1 bit if expr represent a sNaN (signalling) value according
    to IEEE754
    """
    info = size_to_IEEE754_info[expr.size]
    significand_top = expr[info["significand"]: info["significand"] + 1]
    return expr_is_NaN(expr) & ~significand_top


def expr_is_float_lower(op1, op2):
    """Return 1 on 1 bit if @op1 < @op2, 0 otherwise.
    /!\ Assume @op1 and @op2 are not NaN
    Comparison is the floating point one, defined in IEEE754
    """
    sign1, sign2 = op1.msb(), op2.msb()
    magn1, magn2 = op1[:-1], op2[:-1]
    return ExprCond(sign1 ^ sign2,
                    # Sign different, only the sign matters
                    sign1, # sign1 ? op1 < op2 : op1 >= op2
                    # Sign equals, the result is inversed for negatives
                    sign1 ^ (expr_is_unsigned_lower(magn1, magn2)))


def expr_is_float_equal(op1, op2):
    """Return 1 on 1 bit if @op1 == @op2, 0 otherwise.
    /!\ Assume @op1 and @op2 are not NaN
    Comparison is the floating point one, defined in IEEE754
    """
    sign1, sign2 = op1.msb(), op2.msb()
    magn1, magn2 = op1[:-1], op2[:-1]
    return ExprCond(magn1 ^ magn2,
                    ExprInt(0, 1),
                    ExprCond(magn1,
                             # magn1 == magn2, are the signal equals?
                             ~(sign1 ^ sign2),
                             # Special case: -0.0 == +0.0
                             ExprInt(1, 1))
                    )
