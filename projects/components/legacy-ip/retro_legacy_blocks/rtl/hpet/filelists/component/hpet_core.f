# HPET Core Logic File List
# Location: projects/components/retro_legacy_blocks/rtl/hpet/filelists/component/hpet_core.f
# Purpose: HPET timer functionality and core logic

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f

# Core module
$RETRO_ROOT/rtl/hpet/hpet_core.sv
