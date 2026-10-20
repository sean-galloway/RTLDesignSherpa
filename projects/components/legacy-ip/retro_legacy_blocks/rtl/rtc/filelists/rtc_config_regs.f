# Filelist for rtc_config_regs
# Location: projects/components/legacy-ip/retro_legacy_blocks/rtl/rtc/filelists/rtc_config_regs.f
#
# Created 2026-10-19 so formal/retro_legacy_blocks/rtc_config_regs builds its flat from this closure
# (make/formal_flat.mk) instead of a hand-listed SRCS.

+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f
$RETRO_ROOT/rtl/rtc/rtc_regs_pkg.sv
$RETRO_ROOT/rtl/rtc/rtc_regs.sv
$RETRO_ROOT/rtl/rtc/rtc_config_regs.sv
