# Filelist for jet_cpu_plane
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/plane/jet_cpu_plane.f
#
# CPU plane for the jet MESI L1 (plane restructure, Task 4): the GAXI CPU
# slave frontend, the D-6 request skid (gaxi_fifo_sync), and the J4
# response sequencer (jet_rsp_seq) isolated as a protocol-generation
# boundary. Own RTL: the plane itself; foreign sources only via their own
# filelists.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Packages (l1_pkg first; jet_pkg closes it)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f
-f $JET_ROOT/rtl/filelists/jet_pkg.f

# CPU-facing GAXI slave + the D-6 request skid
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_frontend.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

# J4 response sequencer
-f $JET_ROOT/rtl/filelists/jet_rsp_seq.f

# The CPU plane
$JET_ROOT/rtl/plane/jet_cpu_plane.sv
