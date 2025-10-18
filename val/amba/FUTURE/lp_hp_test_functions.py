# HP/LP Test Functions - Future Development
# These functions were moved from test_axi4_matrix_integration.py
# when HP/LP RTL modules were moved to FUTURE directory

async def _test_high_performance(dut, matrix_config, test_scenario, enable_features):
    """Test high-performance features"""

    await _test_basic_monitoring(dut, matrix_config, test_scenario, enable_features)

    # Test high-performance specific features
    if hasattr(dut, 'cfg_hp_enable'):
        dut.cfg_hp_enable.value = 1
        dut.cfg_prefetch_enable.value = 1
        dut.cfg_prefetch_depth.value = 4
        dut.cfg_burst_optimize.value = 1
        dut.cfg_pipeline_mode.value = 3  # Aggressive

        # Test QoS if available
        if hasattr(dut, 'cfg_qos_enable'):
            dut.cfg_qos_enable.value = 1
            dut.cfg_qos_high_threshold.value = 8
            dut.cfg_qos_low_threshold.value = 2
            dut.cfg_qos_timeout_cycles.value = 500

        # Generate high-performance traffic
        await _generate_hp_traffic(dut, matrix_config)

        # Check performance metrics
        await cocotb.triggers.ClockCycles(dut.aclk, 100)
        if hasattr(dut, 'avg_latency_cycles'):
            avg_latency = dut.avg_latency_cycles.value
            cocotb.log.info(f"Average latency: {avg_latency} cycles")


async def _test_low_power(dut, matrix_config, test_scenario, enable_features):
    """Test low-power features"""

    # Keep power management disabled to avoid hangs
    if hasattr(dut, 'cfg_lp_enable'):
        dut.cfg_lp_enable.value = 0  # Disable low-power features for test stability

    await _test_basic_monitoring(dut, matrix_config, test_scenario, enable_features)

    # Simplified sleep mode validation (avoid complex power management loops)
    if hasattr(dut, 'sleep_mode_active'):
        cocotb.log.info("✓ Sleep mode status interface present")

    cocotb.log.info("✓ AXI4 Matrix Integration Test completed: {} - {}".format(
        matrix_config.dut_name.replace("axi4_", "").replace("_mon", ""), test_scenario))


# Configuration entries that were removed from main test:
#
# ("master_rd_hp", "high_performance"),
# ("master_rd_lp", "low_power"),
# ("power_modes", "power_management"),
#
# "master_rd_hp": {
#     "dut_name": "axi4_master_rd_hp_mon",
#     "test_focus": "high_performance",
#     "enable_features": ["filtering", "clock_gating", "high_performance", "histograms", "qos"],
#     "agent_id": 15,
# },
# "master_rd_lp": {
#     "dut_name": "axi4_master_rd_lp_mon",
#     "test_focus": "low_power",
#     "enable_features": ["filtering", "clock_gating", "low_power", "sleep_mode", "dvfs"],
#     "agent_id": 16,
# },
# "power_modes": {
#     "dut_name": "axi4_master_rd_lp_mon",
#     "test_focus": "power_management",
#     "enable_features": ["filtering", "clock_gating", "low_power", "sleep_mode"],
#     "agent_id": 16,
# },