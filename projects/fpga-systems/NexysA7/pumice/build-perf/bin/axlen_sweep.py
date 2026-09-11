#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board sweep: read bandwidth vs AxLEN, against the Little's-law prediction.

Small-burst reads fall well short of writes on this board (AxLEN 1/2/4 reach
16/31/60% of peak against a 95% write). This measures the shape and compares it
to `min(8 x AxLEN / (read_latency + AxLEN), 0.95)` -- the read generator allows
8 bursts in flight (GEN_MAX_OUTSTANDING), so at a ~49-cycle read latency a
short burst simply cannot keep the pipe full.

Run it before theorising about the read scheduler. Five points inside 2% is
what turned "per-transaction overhead nobody has identified" into PUMICE-030,
which is a LATENCY defect: at LiteDRAM's 24.7 cycles the same budget covers
AxLEN 4 and the shortfall disappears.

    PUMICE_MC_CLK_HZ=75000000 python3 bin/axlen_sweep.py     # from build-perf/
"""
sys.path.insert(0, 'host')
import ddr2_char as dc
from ddr2_char import DDR2CharDriver
import pumice_master as pm
import pumice_char as pc

drv = DDR2CharDriver(port=dc.autodetect_port(115200, 'auto'))
st = pm.SimpleTest(drv, base_addr=0, level_cache='host/level_cache.json')
st.init(do_leveling=True)
cfg = pc.CONFIGS['open_page']
geom = pc.DEFAULT_GEOM
print(f"{'AxLEN':>6} {'rd MB/s':>9} {'%peak':>7} {'lat':>6} {'beats/cyc':>10}  predict(8-outstanding)")
for blen in (1, 2, 4, 8, 16):
    sc = pc.Scenario(name=f"row_major_bl{blen}", family=pc.FAM_ROW_MAJOR,
                     burst_len=blen, txn_count=4000, gap=0)
    r = pc.measure(drv, sc, cfg=cfg, geom=geom, base_addr=0, clk_mhz=75.0, timeout_s=40.0)
    lat = r.rd_avg_latency_cyc
    bpc = r.rd_bytes_per_cycle / 8.0
    pred = min((8*blen)/(lat+blen), 0.95) * 8 * 75
    print(f"{blen:6} {r.rd_bw_mb_s:9.1f} {r.rd_bw_mb_s/6:6.1f}% {lat:6.1f} {bpc:10.3f}  {pred:8.1f}  ok={int(r.ok)}")
