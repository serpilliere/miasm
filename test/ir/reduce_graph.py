"""Regression test module for DependencyGraph"""
from __future__ import print_function

from pathlib import Path

from future.utils import viewitems

from miasm.expression.expression import ExprId, ExprInt, ExprAssign, ExprCond, ExprLoc

from miasm.core.locationdb import LocationDB
from miasm.ir.analysis import LifterModelCall
from miasm.ir.ir import IRBlock, AssignBlock, IRCFG
from miasm.analysis.data_flow import merge_blocks

loc_db = LocationDB()

A = ExprId("a", 32)
B = ExprId("b", 32)
C = ExprId("c", 32)
D = ExprId("d", 32)
R = ExprId("r", 32)

A_INIT = ExprId("a_init", 32)
B_INIT = ExprId("b_init", 32)
C_INIT = ExprId("c_init", 32)
D_INIT = ExprId("d_init", 32)

IRDst = ExprId("IRDst", 32)
PC = ExprId("pc", 32)
SP = ExprId("sp", 32)

CST0 = ExprInt(0x0, 32)
CST1 = ExprInt(0x1, 32)
CST2 = ExprInt(0x2, 32)
CST3 = ExprInt(0x3, 32)
CST22 = ExprInt(0x22, 32)
CST23 = ExprInt(0x23, 32)
CST24 = ExprInt(0x24, 32)
CST33 = ExprInt(0x33, 32)
CST35 = ExprInt(0x35, 32)
CST37 = ExprInt(0x37, 32)

LBL0 = loc_db.add_location("lbl0", 0)
LBL1 = loc_db.add_location("lbl1", 1)
LBL2 = loc_db.add_location("lbl2", 2)
LBL3 = loc_db.add_location("lbl3", 3)
LBL4 = loc_db.add_location("lbl4", 4)
LBL5 = loc_db.add_location("lbl5", 5)
LBL6 = loc_db.add_location("lbl6", 6)


class Regs(object):
    """Fake registers for tests """
    regs_init = {A: A_INIT, B: B_INIT, C: C_INIT, D: D_INIT}
    all_regs_ids = [A, B, C, D, SP, PC, R]


class Arch(object):
    """Fake architecture for tests """
    regs = Regs()

    def getpc(self, attrib):
        return PC

    def getsp(self, attrib):
        return SP


class IRATest(LifterModelCall):
    """Fake IRA class for tests"""

    def __init__(self, loc_db):
        arch = Arch()
        super(IRATest, self).__init__(arch, 32, loc_db)
        self.IRDst = IRDst
        self.ret_reg = R

    def get_out_regs(self, _):
        return {self.ret_reg, self.sp}


def gen_irblock(label, exprs_list):
    """ Returns an IRBlock.
    Used only for tests purpose
    """
    irs = []
    for exprs in exprs_list:
        if isinstance(exprs, AssignBlock):
            irs.append(exprs)
        else:
            irs.append(AssignBlock(exprs))

    irbl = IRBlock(loc_db, label, irs)
    return irbl


IRA = IRATest(loc_db)


def test1(out_path):
    # Input
    G1 = IRA.new_ircfg()

    G1_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(B, C),
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G1_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL2, 32)),
            ]
        ]
    )

    G1_IRB2 = gen_irblock(
        LBL2,
        [
            [
                ExprAssign(A, B),
                ExprAssign(IRDst, C),
            ]
        ]
    )

    for irb in [G1_IRB0, G1_IRB1, G1_IRB2]:
        G1.add_irblock(irb)

    # Result
    G1_RES = IRA.new_ircfg()

    G1_RES_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(B, C),
            ],
            [
                ExprAssign(A, B),
                ExprAssign(IRDst, C),
            ]

        ]
    )

    for irb in [G1_RES_IRB0]:
        G1_RES.add_irblock(irb)

    check(1, G1, G1_RES, out_path)


def test2(out_path):
    # Input

    G2 = IRA.new_ircfg()

    G2_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G2_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(A, C),
                ExprAssign(IRDst, C),
            ]
        ]
    )

    for irb in [G2_IRB0, G2_IRB1]:
        G2.add_irblock(irb)

    # Result
    G2_RES = IRA.new_ircfg()

    G2_RES_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(A, C),
                ExprAssign(IRDst, C),
            ]
        ]
    )

    for irb in [G2_RES_IRB0]:
        G2_RES.add_irblock(irb)

    check(2, G2, G2_RES, out_path)


def test3(out_path):
    # Input

    G3 = IRA.new_ircfg()

    G3_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G3_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(A, C),
                ExprAssign(IRDst, ExprLoc(LBL2, 32)),
            ]
        ]
    )

    G3_IRB2 = gen_irblock(
        LBL2,
        [
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, C),
            ]
        ]
    )

    for irb in [G3_IRB0, G3_IRB1, G3_IRB2]:
        G3.add_irblock(irb)

    # Result
    G3_RES = IRA.new_ircfg()

    G3_RES_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(A, C),
            ],
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, C),
            ]
        ]
    )

    for irb in [G3_RES_IRB0]:
        G3_RES.add_irblock(irb)

    check(3, G3, G3_RES, out_path)


def test4(out_path):
    # Input

    G4 = IRA.new_ircfg()

    G4_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G4_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(A, C),
                ExprAssign(IRDst, ExprLoc(LBL2, 32)),
            ]
        ]
    )

    G4_IRB2 = gen_irblock(
        LBL2,
        [
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    for irb in [G4_IRB0, G4_IRB1, G4_IRB2]:
        G4.add_irblock(irb)

    # Result
    G4_RES = IRA.new_ircfg()

    G4_RES_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G4_RES_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(A, C),
            ],
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    for irb in [G4_RES_IRB0, G4_RES_IRB1]:
        G4_RES.add_irblock(irb)

    check(4, G4, G4_RES, out_path)


def test5(out_path):
    # Input

    G5 = IRA.new_ircfg()

    G5_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G5_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(A, C),
                ExprAssign(IRDst, ExprLoc(LBL2, 32)),
            ]
        ]
    )

    G5_IRB2 = gen_irblock(
        LBL2,
        [
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, ExprCond(C, ExprLoc(LBL1, 32), ExprLoc(LBL3, 32))),
            ]
        ]
    )

    G5_IRB3 = gen_irblock(
        LBL3,
        [
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, C),
            ]
        ]
    )

    for irb in [G5_IRB0, G5_IRB1, G5_IRB2, G5_IRB3]:
        G5.add_irblock(irb)

    # Result
    G5_RES = IRA.new_ircfg()

    G5_RES_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G5_RES_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(A, C),
            ],
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, ExprCond(C, ExprLoc(LBL1, 32), ExprLoc(LBL3, 32))),
            ]
        ]
    )

    G5_RES_IRB3 = gen_irblock(
        LBL3,
        [
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, C),
            ]
        ]
    )

    for irb in [G5_RES_IRB0, G5_RES_IRB1, G5_RES_IRB3]:
        G5_RES.add_irblock(irb)

    check(5, G5, G5_RES, out_path)


def test6(out_path):
    # Input

    G6 = IRA.new_ircfg()

    G6_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprCond(C, ExprLoc(LBL1, 32), ExprLoc(LBL2, 32))),
            ]
        ]
    )

    G6_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL3, 32)),
            ]
        ]
    )

    G6_IRB2 = gen_irblock(
        LBL2,
        [
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, D),
            ]
        ]
    )

    G6_IRB3 = gen_irblock(
        LBL3,
        [
            [
                ExprAssign(A, D),
                ExprAssign(IRDst, ExprLoc(LBL3, 32)),
            ]
        ]
    )

    for irb in [G6_IRB0, G6_IRB1, G6_IRB2, G6_IRB3]:
        G6.add_irblock(irb)

    # Result
    G6_RES = IRA.new_ircfg()

    G6_RES_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprCond(C, ExprLoc(LBL3, 32), ExprLoc(LBL2, 32))),
            ]
        ]
    )

    G6_RES_IRB2 = gen_irblock(
        LBL2,
        [
            [
                ExprAssign(D, A),
                ExprAssign(IRDst, D),
            ]
        ]
    )

    G6_RES_IRB3 = gen_irblock(
        LBL3,
        [
            [
                ExprAssign(A, D),
                ExprAssign(IRDst, ExprLoc(LBL3, 32)),
            ]
        ]
    )

    for irb in [G6_RES_IRB0, G6_RES_IRB2, G6_RES_IRB3]:
        G6_RES.add_irblock(irb)

    check(6, G6, G6_RES, out_path)


def test7(out_path):
    # Input

    G7 = IRA.new_ircfg()

    G7_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(A, C),
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G7_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    for irb in [G7_IRB0, G7_IRB1]:
        G7.add_irblock(irb)

    # Result
    G7_RES = IRA.new_ircfg()

    G7_RES_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(A, C),
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G7_RES_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    for irb in [G7_RES_IRB0, G7_RES_IRB1]:
        G7_RES.add_irblock(irb)

    check(7, G7, G7_RES, out_path)


def test8(out_path):
    # Input

    G8 = IRA.new_ircfg()

    G8_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G8_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(A, C),
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    for irb in [G8_IRB0, G8_IRB1]:
        G8.add_irblock(irb)

    # Result
    G8_RES = IRA.new_ircfg()

    G8_RES_IRB0 = gen_irblock(
        LBL0,
        [
            [
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    G8_RES_IRB1 = gen_irblock(
        LBL1,
        [
            [
                ExprAssign(A, C),
                ExprAssign(IRDst, ExprLoc(LBL1, 32)),
            ]
        ]
    )

    for irb in [G8_RES_IRB0, G8_RES_IRB1]:
        G8_RES.add_irblock(irb)

    check(8, G8, G8_RES, out_path)


def check(i, g_test, g_ref, out_path: Path):
    heads = g_test.heads()
    out_path.joinpath("test_in_%d.dot" % i).write_text(g_test.dot())
    out_path.joinpath("test_ref_%d.dot" % i).write_text(g_ref.dot())
    merge_blocks(g_test, heads)
    out_path.joinpath("test_out_%d.dot" % i).write_text(g_test.dot())

    assert g_test == g_ref
    assert set(g_test.edges()) == set(g_ref.edges())
    print('\t', 'OK')
