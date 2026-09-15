# ==============================================================================
# Retro Legacy Blocks - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns, so that
#          `make lint-retro_legacy_blocks` has sources to lint.
# Usage:   verilator --lint-only -f filelists/retro_legacy_blocks_all.f
#
# This file `-f` includes each block's OWN top filelist and never hand-lists
# sources. Every block already declares its complete closure; re-listing those
# files here would have to track each block's internal dependencies and would
# rot silently the first time one changed. See vault/handbook/design/filelists.md.
#
# Verified when written: all 55 module-declaring .sv files under rtl/ are
# reachable from the lists below, with no orphans.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

# --- APB peripherals -------------------------------------------------------
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/hpet/filelists/integration/apb4_hpet.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/pic_8259/filelists/apb4_pic_8259.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/pit_8254/filelists/apb4_pit_8254.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/rtc/filelists/apb4_rtc.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/smbus/filelists/apb4_smbus.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/pm_acpi/filelists/apb4_pm_acpi.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/filelists/apb4_ioapic.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/gpio/filelists/apb4_gpio.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/uart_16550/filelists/apb4_uart_16550.f

# --- IOAPIC companions -----------------------------------------------------
# Outside apb4_ioapic's port list and deliberately absent from its filelist
# (they are not part of that block's closure), so they are named here or they
# would be linted by nothing. See RLB-008.
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/filelists/ioapic_boot_intx.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/filelists/ioapic_deliv_merge.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/filelists/ioapic_lowest_pri_arb.f
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/filelists/ioapic_msi_emit.f

# --- Top-level integration (pulls the generated 1to10 crossbar) ------------
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/rlb_top/rlb_top.f
