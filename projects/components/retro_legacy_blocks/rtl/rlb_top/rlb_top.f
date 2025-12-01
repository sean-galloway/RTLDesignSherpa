# RLB Top Integration File List
# Location: projects/components/retro_legacy_blocks/rtl/rlb_top/rlb_top.f
# Purpose: Complete Retro Legacy Block peripheral subsystem with APB crossbar
#
# Address Map (4KB windows from BASE_ADDR 0xFEC00000):
#   Slave 0: HPET         [0xFEC00000 - 0xFEC00FFF]
#   Slave 1: 8259 PIC     [0xFEC01000 - 0xFEC01FFF]
#   Slave 2: 8254 PIT     [0xFEC02000 - 0xFEC02FFF]
#   Slave 3: RTC          [0xFEC03000 - 0xFEC03FFF]
#   Slave 4: SMBus        [0xFEC04000 - 0xFEC04FFF]
#   Slave 5: PM/ACPI      [0xFEC05000 - 0xFEC05FFF]
#   Slave 6: IOAPIC       [0xFEC06000 - 0xFEC06FFF]
#   Slave 7: GPIO         [0xFEC07000 - 0xFEC07FFF]
#   Slave 8: UART 16550   [0xFEC08000 - 0xFEC08FFF]
#   Slave 9: Reserved     [0xFEC09000 - 0xFEC09FFF]

# Include directories for SystemVerilog header files
+incdir+$REPO_ROOT/rtl/amba/includes

# ============================================================================
# APB Infrastructure
# ============================================================================

# GAXI dependencies (FIFO and skid buffer for CDC)
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# APB slave and master modules (core crossbar building blocks)
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_master.sv

# Common arbiter modules
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
$REPO_ROOT/rtl/common/encoder.sv

# ============================================================================
# APB Crossbar (1-to-10 for RLB peripherals)
# ============================================================================
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/apb_xbar/apb_xbar_rlb_1to10.sv

# ============================================================================
# Peripheral Filelists (include all peripheral dependencies)
# ============================================================================

# HPET
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/hpet/filelists/integration/apb_hpet.f

# 8259 PIC
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/pic_8259/filelists/apb_pic_8259.f

# 8254 PIT
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/pit_8254/filelists/apb_pit_8254.f

# RTC
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/rtc/filelists/apb_rtc.f

# SMBus
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/smbus/filelists/apb_smbus.f

# PM/ACPI
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/pm_acpi/filelists/apb_pm_acpi.f

# IOAPIC
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/filelists/apb_ioapic.f

# GPIO
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/gpio/filelists/apb_gpio.f

# UART 16550
-f $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/uart_16550/filelists/apb_uart_16550.f

# ============================================================================
# Top-Level Integration
# ============================================================================
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/rlb_top/rlb_top.sv
