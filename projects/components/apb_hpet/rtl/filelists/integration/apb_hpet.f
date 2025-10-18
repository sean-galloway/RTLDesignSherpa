# APB HPET Integration File List
# Location: rtl/amba/components/hpet/filelists/integration/apb_hpet.f
# Purpose: Complete APB-interfaced HPET timer (all components)

# Include component-level file lists (automatically pulls in dependencies)
-f $REPO_ROOT/rtl/amba/components/hpet/filelists/component/hpet_core.f
-f $REPO_ROOT/rtl/amba/components/hpet/filelists/component/hpet_config_regs.f

# APB infrastructure dependencies
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/shared/cdc_handshake.sv
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc.sv
$REPO_ROOT/rtl/amba/adapters/peakrdl_to_cmdrsp.sv

# Top-level integration module
$REPO_ROOT/rtl/amba/components/hpet/apb_hpet.sv
