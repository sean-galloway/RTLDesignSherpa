# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: apb4_rtc.f
# Purpose: Complete file list for APB RTC module
#
# Usage: Source this file in simulation/synthesis tools

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f

# Clock-domain crossing primitives used by rtc_core (GitHub #56). Exactly the
# four it instantiates, and no more - a filelist that carries a module the
# design does not use makes every consumer compile it and hides what the
# block actually depends on. The time-set commit is a FOUR-phase handshake
# (the two domains reset independently, so a toggle protocol's parity cannot
# survive - see docs/markdown/rtl-cdc/cdc.md); the counter->pclk update event
# is a toggle pulse synchronizer; the config/alarm bundle and the read shadow
# are quasi-static multi-bit crossings; the counter domain's reset release is
# synchronized.
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/cdc/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/reset_sync.f

# Layer 2: CMD/RSP to PeakRDL Adapter
-f $REPO_ROOT/projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# Package (must come first)
$RETRO_ROOT/rtl/rtc/rtc_regs.sv/rtc_regs_pkg.sv

# Register file (PeakRDL generated)
$RETRO_ROOT/rtl/rtc/rtc_regs.sv/rtc_regs.sv

# RTC core (time counting logic)
$RETRO_ROOT/rtl/rtc/rtc_core.sv

# Config register wrapper
$RETRO_ROOT/rtl/rtc/rtc_config_regs.sv

# Top-level APB wrapper
$RETRO_ROOT/rtl/rtc/apb4_rtc.sv
