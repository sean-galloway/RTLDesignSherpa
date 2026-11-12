import ramulator

# The Nexys A7 part (MT47H64M16, 1 Gb x16, 2 KB page) at the board's 100 MHz
# point (CK 200 MHz, CL3, BL4). One x16 device is the whole channel; the frontend
# ticks once per 2 CK (clock_ratio 1 against the memory system's 2 in the configs,
# here both 1), one 8-byte BL4 transaction per tick, the AXI beat rate of the board.
CONFIG = dict(
    dram_class="DDR2",
    org_preset="DDR2_1Gb_x16",
    timing_preset="DDR2_MT47H64M16_400_CL3",
    dram_kwargs={},
    controller_class="GenericDDR",
    fast_ctrl_extra_kwargs=dict(
        refresh_manager=ramulator.refresh_manager.NoRefresh(),
    ),
    frontend_clock_ratio=1,
    stream_cls=8,
)
