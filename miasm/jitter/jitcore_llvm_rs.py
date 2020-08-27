from __future__ import print_function
import os
import importlib
import tempfile
import sysconfig

import miasm.jitter.jitcore as jitcore
import platform

# Rs modules
import miasm_rs
from miasm_rs import LifterX86
from miasm_rs import LocationDB
from miasm_rs import add_explicit_rules
from miasm_rs import ExprRules
from miasm_rs import ExprVisitor

from miasm_rs import JitterX86
from miasm_rs import DisasmEngineX86
from miasm.jitter.csts import *


is_win = platform.system() == "Windows"

class JitCore_LLVM_RS(jitcore.JitCore):
    "JiT management, using LLVM as backend"

    # Architecture dependent libraries
    arch_dependent_libs = {
        "x86": "JitCore_x86",
        "arm": "JitCore_arm",
        "msp430": "JitCore_msp430",
        "mips32": "JitCore_mips32",
        "aarch64": "JitCore_aarch64",
        "ppc32": "JitCore_ppc32",
    }

    def __init__(self, ir_arch, bin_stream):
        super(JitCore_LLVM_RS, self).__init__(ir_arch, bin_stream)
        self.bin_stream = bin_stream

        self.options.update(
            {
                "safe_mode": True,   # Verify each function
                "optimise": True,     # Optimise functions
                "log_func": False,    # Print LLVM functions
                "log_assembly": False,  # Print assembly executed
            }
        )

        opsize = ir_arch.attrib

        # Init rust functions
        loc_db = self.ir_arch.loc_db
        lifter_x86 = LifterX86(loc_db, opsize)

        expr_rules = ExprRules()
        add_explicit_rules(expr_rules)
        expr_simp = ExprVisitor.visit_bottom_up(expr_rules)



        lib_dir = os.path.dirname(os.path.realpath(__file__))
        lib_dir = os.path.join(lib_dir, 'arch')
        ext = ".so"
        if ext is None:
            ext = ".so" if not is_win else ".pyd"
        try:
            jit_lib = os.path.join(
                lib_dir, self.arch_dependent_libs[self.ir_arch.arch.name] + ext
            )
            #libs_to_load.append(jit_lib)
        except KeyError:
            fds

        mod_name = jit_lib
        #mod_name = "miasm.jitter.arch.JitCore_%s" % (myjit.ir_arch.arch.name)
        mod_name = "miasm.jitter.arch.JitCore_%s" % (ir_arch.arch.name)
        mod = importlib.import_module(mod_name)
        regs_offset = mod.get_gpreg_offset_all()

        jitter_x86 = JitterX86(
            lifter_x86,
            expr_simp,
            regs_offset,
            ir_arch.arch.regs.RIP,
            ir_arch.IRDst.size,
            0
        )


        mdis = DisasmEngineX86(loc_db, bin_stream, opsize, True)

        self.expr_simp = expr_simp
        self.jitter = jitter_x86
        self.mdis = mdis
        self.exec_wrapper = self.jitter.execute


    def load(self):
        # Save the current architecture parameters
        self.arch = self.ir_arch.arch
        return


    def add_disassembly_splits(self, *args):
        """The disassembly engine will stop on address in args if they
        are not at the block beginning"""
        self.mdis.split_add(list(args))

    def remove_disassembly_splits(self, *args):
        """The disassembly engine will no longer stop on address in args"""
        self.mdis.split_del(list(args))

    def add_block(self, block):
        """Add a block to JiT and JiT it.
        @block: the block to add
        """

        addr_func = self.jitter.jit(block, self.log_mn)
        # Store a pointer on the function jitted code
        loc_key = block.loc_key
        offset = self.ir_arch.loc_db.get_location_offset(loc_key)
        assert offset is not None
        self.offset_to_jitted_func[offset] = addr_func

        return

    def run_at(self, cpu, offset, stop_offsets):
        """Run from the starting address @offset.
        Execution will stop if:
        - max_exec_per_call option is reached
        - a new, yet unknown, block is reached after the execution of block at
          address @offset
        - an address in @stop_offsets is reached
        @cpu: JitCpu instance
        @offset: starting address (int)
        @stop_offsets: set of address on which the jitter must stop
        """


        if offset is None:
            offset = getattr(cpu, self.ir_arch.pc.name)

        if offset not in self.offset_to_jitted_func:
            # Need to JiT the block
            cur_block = self.disasm_and_jit_block(offset, cpu.vmmngr)
            if cur_block.is_bad():#isinstance(cur_block, AsmBlockBad):
                errno = cur_block.errno
                if errno == 3:#AsmBlockBad.ERROR_IO:
                    print("IOError")
                    cpu.vmmngr.set_exception(EXCEPT_ACCESS_VIOL)
                elif errno == 0:#AsmBlockBad.ERROR_CANNOT_DISASM:
                    cpu.set_exception(EXCEPT_UNK_MNEMO)
                else:
                    raise RuntimeError("Unhandled disasm result %r" % errno)
                return offset

        # Run the block and update cpu/vmmngr state
        #print("exec %x"% offset)
        vmcpu = cpu.vmcpu
        vmmngr = cpu.vmmngr.vmmngr
        stop_offsets = {addr:addr for addr in stop_offsets}
        id_cpu = id(cpu)
        ret = self.jitter.execute(offset, id_cpu, vmcpu, vmmngr, dict(self.offset_to_jitted_func), stop_offsets)
        return ret
