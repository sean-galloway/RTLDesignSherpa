# Verilated -*- Makefile -*-
# DESCRIPTION: Verilator output: Make include file with class lists
#
# This file lists generated Verilated files, for including in higher level makefiles.
# See Vtop.mk for the caller.

### Switches...
# C11 constructs required?  0/1 (always on now)
VM_C11 = 1
# Timing enabled?  0/1
VM_TIMING = 0
# Coverage output mode?  0/1 (from --coverage)
VM_COVERAGE = 0
# Parallel builds?  0/1 (from --output-split)
VM_PARALLEL_BUILDS = 1
# Tracing output mode?  0/1 (from --trace/--trace-fst)
VM_TRACE = 0
# Tracing output mode in VCD format?  0/1 (from --trace)
VM_TRACE_VCD = 0
# Tracing output mode in FST format?  0/1 (from --trace-fst)
VM_TRACE_FST = 0

### Object file lists...
# Generated module classes, fast-path, compile with highest optimization
VM_CLASSES_FAST += \
	Vtop \
	Vtop___024root__DepSet_h84412442__0 \
	Vtop___024root__DepSet_h84412442__1 \
	Vtop___024root__DepSet_h84412442__2 \
	Vtop___024root__DepSet_he8e785bb__0 \
	Vtop___024root__DepSet_he8e785bb__1 \
	Vtop___024root__DepSet_he8e785bb__2 \
	Vtop___024root__DepSet_heccd7ead__0 \
	Vtop___024root__DepSet_h452d2df9__0 \
	Vtop___024root__DepSet_h452d2df9__1 \
	Vtop_stream_regs_pkg__DepSet_h3b4d4869__0 \
	Vtop_sram_controller_unit__pi14__DepSet_h15abab65__0 \
	Vtop_sram_controller_unit__pi14__DepSet_h5ce6f788__0 \
	Vtop_monbus_arbiter__C2__DepSet_h202ea2d6__0 \

# Generated module classes, non-fast-path, compile with low/medium optimization
VM_CLASSES_SLOW += \
	Vtop__ConstPool_0 \
	Vtop___024root__Slow \
	Vtop___024root__DepSet_h84412442__0__Slow \
	Vtop___024root__DepSet_he8e785bb__0__Slow \
	Vtop___024root__DepSet_heccd7ead__0__Slow \
	Vtop___024unit__Slow \
	Vtop___024unit__DepSet_hff17caec__0__Slow \
	Vtop_stream_regs_pkg__Slow \
	Vtop_stream_regs_pkg__DepSet_h3b4d4869__0__Slow \
	Vtop_stream_pkg__Slow \
	Vtop_stream_pkg__DepSet_h801792c1__0__Slow \
	Vtop_sram_controller_unit__pi14__Slow \
	Vtop_sram_controller_unit__pi14__DepSet_h5ce6f788__0__Slow \
	Vtop_monbus_arbiter__C2__Slow \
	Vtop_monbus_arbiter__C2__DepSet_h202ea2d6__0__Slow \
	Vtop_monitor_amba4_pkg__Slow \
	Vtop_monitor_amba4_pkg__DepSet_h09afd2d6__0__Slow \
	Vtop_monitor_common_pkg__Slow \
	Vtop_monitor_common_pkg__DepSet_h8e44846e__0__Slow \

# Generated support classes, fast-path, compile with highest optimization
VM_SUPPORT_FAST += \
	Vtop__Dpi \

# Generated support classes, non-fast-path, compile with low/medium optimization
VM_SUPPORT_SLOW += \
	Vtop__Syms \

# Global classes, need linked once per executable, fast-path, compile with highest optimization
VM_GLOBAL_FAST += \
	verilated \
	verilated_dpi \
	verilated_vpi \
	verilated_threads \

# Global classes, need linked once per executable, non-fast-path, compile with low/medium optimization
VM_GLOBAL_SLOW += \


# Verilated -*- Makefile -*-
