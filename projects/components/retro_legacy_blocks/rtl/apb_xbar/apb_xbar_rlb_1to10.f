# APB Crossbar RLB 1-to-10 File List
# Location: projects/components/retro_legacy_blocks/rtl/apb_xbar/apb_xbar_rlb_1to10.f
# Purpose: 1-to-10 APB crossbar for all Retro Legacy Block peripherals
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

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/apb_master.f
-f $REPO_ROOT/rtl/amba/filelists/apb_slave.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f
-f $REPO_ROOT/rtl/common/filelists/encoder.f

# 1-to-10 crossbar with named ports for RLB peripherals
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/apb_xbar/apb_xbar_rlb_1to10.sv
