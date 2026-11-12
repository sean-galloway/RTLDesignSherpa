"""DDR2 with MR0 BL = 8 (memory-controllers MC-012). One class per module:
codegen derives the module name from the class name."""
from ramulator.dram.ddr2 import DDR2


class DDR2_BL8(DDR2):
    """DDR2 with MR0 BL = 8: two 4n prefetches per column command, nBL = 4 CK.
    Transaction = 8 * channel_width / 8 bytes (16 B on a single x16 device).
    Timings are the DDR2 presets with nBL doubled; nothing else moves."""
    name = "DDR2_BL8"
    internal_prefetch_size = 8


DDR2_BL8.org_presets = dict(DDR2.org_presets)
DDR2_BL8.timing_presets = {k: {**v, "nBL": 4} for k, v in DDR2.timing_presets.items()}
