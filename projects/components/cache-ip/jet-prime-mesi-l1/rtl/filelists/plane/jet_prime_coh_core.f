# Filelist for jet_prime_coh_core
# Location: projects/components/cache-ip/jet-prime-mesi-l1/rtl/filelists/plane/jet_prime_coh_core.f
#
# Coherence-core plane for the jet MESI L1 (plane restructure, Task 4):
# the jet control closure (jet_prime_control + jet_prime_mshr + jet_prime_wb_buffer), the
# UNCHANGED common-ip slice (arrays, repl, fill/drain engines), the
# l1_monlite + jet_prime_monlite observers, and the integration glue
# (fill-launch adapter, data-array W-port mux, coh_req drain-collision
# replay, mon_state pseudo-state encoder). Own RTL: the plane itself;
# foreign sources only via their own filelists.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Packages (l1_pkg first; jet_prime_pkg closes it)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f
-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_pkg.f

# jet control closure (the lookup/commit core + its two files; the J4
# response sequencer lives in the CPU plane)
-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_mshr.f
-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_wb_buffer.f
-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_control.f

# Common-ip slice: arrays + replacement + fill/drain engines
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_tag_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_data_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_repl.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_fill.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_drain.f

# MonBus observers (the cache-event monlite + the J7 jet observer)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_monlite.f
-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_monlite.f

# The coherence core plane
$JET_PRIME_ROOT/rtl/plane/jet_prime_coh_core.sv
