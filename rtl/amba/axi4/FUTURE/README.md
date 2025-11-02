# FUTURE - HP/LP AXI4 Monitoring Modules

This directory contains High-Performance (HP) and Low-Power (LP) AXI4 monitoring modules that have been moved here for future development.

## Files Moved Here:

### RTL Modules:
- `axi4_master_rd_hp_mon.sv` - High-performance master read monitor
- `axi4_master_rd_lp_mon.sv` - Low-power master read monitor

## Reason for Moving:

These modules were moved to FUTURE because:

1. **Low-Power Module Issues**: The `axi4_master_rd_lp_mon` module had fundamental issues causing infinite loops/deadlocks during simulation, making tests consistently timeout.

2. **Complexity**: The power management features require additional validation and debugging that would delay the core AXI4 monitoring integration.

3. **Focus on Core Features**: Moving these allows the core monitoring functionality to be delivered without being blocked by advanced power management features.

## Future Integration:

To re-integrate these modules:

1. Fix the underlying RTL issues in the low-power module
2. Move files back to `rtl/amba/axi4/`
3. Re-enable test configurations in `val/amba/test_axi4_matrix_integration.py`
4. Restore test functions from `val/amba/FUTURE/lp_hp_test_functions.py`

## Dependencies:

These modules depend on the core monitoring infrastructure which is still active:
- `axi_monitor_base.sv`
- `axi_monitor_filtered.sv`
- `axi_monitor_trans_mgr.sv`
- And other shared monitoring components

The base modules they extend are also active:
- `axi4_master_rd_mon.sv`
- `axi4_master_rd_mon_cg.sv`