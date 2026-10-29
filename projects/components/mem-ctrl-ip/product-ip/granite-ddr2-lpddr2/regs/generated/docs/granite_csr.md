<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## granite_csr address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0xFF8

<p>Configuration and observation registers for the granite DDR2/LPDDR2 product SKU. Address-for-address derived from pumice_csr.rdl; absent features are reserved rather than removed.</p>

|Offset|       Identifier      |                  Name                 |
|------|-----------------------|---------------------------------------|
| 0x000|          CTRL         |            Control Register           |
| 0x004|         STATUS        |            Status Register            |
| 0x010| TIMINGS_RC_RCD_RP_RAS |    Timings: tRC / tRCD / tRP / tRAS   |
| 0x014|    TIMINGS_RFC_REFI   |         Timings: tRFC / tREFI         |
| 0x018|TIMINGS_RRD_FAW_WTR_CCD|   Timings: tRRD / tFAW / tWTR / tCCD  |
| 0x01C|   TIMINGS_CL_CWL_WR   |    Timings: CL / CWL / tWR / tRFCpb   |
| 0x020|          MR0          |            Mode Register 0            |
| 0x024|          MR1          |            Mode Register 1            |
| 0x028|          MR2          |            Mode Register 2            |
| 0x02C|          MR3          |            Mode Register 3            |
| 0x048|     REFRESH_TUNING    |             Refresh Tuning            |
| 0x04C|        ADDR_MAP       |              Address Map              |
| 0x054|    TIMINGS_RTP_RTW    |          Timings: tRTP / tRTW         |
| 0x058|      INIT_TIMING0     |      Init Timing 0: tINIT / tDLLK     |
| 0x05C|      INIT_TIMING1     |Init Timing 1: tMRD / tRP / tRFC (init)|
| 0x060|       DFI_PHASE       |      DFI Command Phase Placement      |
| 0x064|       PHY_TIMING      | PHY / DFI data timing + memory config |
| 0x068|      SCHED_POLICY     |            Scheduler Policy           |
| 0x06C|      SCHED_WR_WM      |       Scheduler Write Watermarks      |
| 0x070|    PAGE_POLICY_CFG    |           Page Policy Config          |
| 0x074|    PAGE_TIMEOUT_CFG   |          Page Timeout Config          |
| 0x0A0|        CAL_CTRL       |          Calibration Control          |
| 0x0A4|    CAL_ZQ_INTERVAL    |              ZQ Interval              |
| 0x0A8|     CAL_ZQ_TIMING     |           ZQ Post-Grant Hold          |
| 0x0AC|    CAL_TRAIN_TIMING   |            Training Timing            |
| 0x0B0|   CAL_MRR32_DATA[0]   |          MRR32 Captured Data          |
| 0x0B4|   CAL_MRR32_DATA[1]   |          MRR32 Captured Data          |
| 0x0B8|   CAL_MRR32_DATA[2]   |          MRR32 Captured Data          |
| 0x0BC|   CAL_MRR32_DATA[3]   |          MRR32 Captured Data          |
| 0x0E0|   CAL_MRR40_DATA[0]   |          MRR40 Captured Data          |
| 0x0E4|   CAL_MRR40_DATA[1]   |          MRR40 Captured Data          |
| 0x0E8|   CAL_MRR40_DATA[2]   |          MRR40 Captured Data          |
| 0x0EC|   CAL_MRR40_DATA[3]   |          MRR40 Captured Data          |
| 0x0F0|       CAL_STATUS      |           Calibration Status          |
| 0x180|       LP_MR1_OP       |           LPDDR2 MR1 OP Data          |
| 0x184|       LP_MR2_OP       |           LPDDR2 MR2 OP Data          |
| 0x188|       LP_MR3_OP       |           LPDDR2 MR3 OP Data          |
| 0x18C|   STORE_STATS_MERGE   |       Store Stats: Write Merges       |
| 0x190|  STORE_STATS_RD_MERGE |        Store Stats: Read Merges       |
| 0xFF0|           ID          |               Module ID               |
| 0xFF4|         BUILD         |               Build Hash              |

### CTRL register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Init / power / soft-reset request bits</p>

|Bits|     Identifier     |Access|Reset|Name|
|----|--------------------|------|-----|----|
|  0 |     init_start     |  rw  | 0x0 |  — |
|  1 | init_force_restart |  rw  | 0x0 |  — |
| 3:2|      RSVD_3_2      |   r  | 0x0 |  — |
|  4 |  pwr_req_low_power |  rw  | 0x0 |  — |
|  5 |     pwr_req_dpd    |  rw  | 0x0 |  — |
|  6 |   pwr_req_active   |  rw  | 0x0 |  — |
|  7 |pwr_req_self_refresh|  rw  | 0x0 |  — |
|30:8|      RSVD_30_8     |   r  | 0x0 |  — |
| 31 |     soft_reset     |  rw  | 0x0 |  — |

#### init_start field

<p>Write 1 to start init</p>

#### init_force_restart field

<p>Write 1 to force re-init even mid-sequence</p>

#### RSVD_3_2 field

<p>Reserved</p>

#### pwr_req_low_power field

<p>Request power-down state</p>

#### pwr_req_dpd field

<p>Request DPD (LPDDR2 only)</p>

#### pwr_req_active field

<p>Request return to ACTIVE</p>

#### pwr_req_self_refresh field

<p>Request self-refresh</p>

#### RSVD_30_8 field

<p>Reserved</p>

#### soft_reset field

<p>Write 1 to assert internal soft reset (self-clearing)</p>

### STATUS register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>Init / power / version status</p>

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
|  0  |  init_done  |   r  |  —  |  — |
|  1  |  init_error |   r  |  —  |  — |
| 3:2 |   RSVD_3_2  |   r  | 0x0 |  — |
| 7:4 | power_state |   r  |  —  |  — |
|  8  | pasr_active |   r  |  —  |  — |
| 15:9|  RSVD_15_9  |   r  | 0x0 |  — |
|23:16|init_step_dbg|   r  |  —  |  — |
|30:24|  RSVD_30_24 |   r  | 0x0 |  — |
|  31 |version_match|   r  |  —  |  — |

#### init_done field

<p>Init complete</p>

#### init_error field

<p>Init error</p>

#### RSVD_3_2 field

<p>Reserved</p>

#### power_state field

<p>Current power-state FSM state (encoded)</p>

#### pasr_active field

<p>LPDDR2: PASR mask is non-zero</p>

#### RSVD_15_9 field

<p>Reserved</p>

#### init_step_dbg field

<p>Current init step number (for bring-up)</p>

#### RSVD_30_24 field

<p>Reserved</p>

#### version_match field

<p>Build matches expected version</p>

### TIMINGS_RC_RCD_RP_RAS register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>Packed core per-bank JEDEC windows, in MC (controller) cycles.
EVERY JEDEC timing field in this map is a count of cycles to
BLOCK, so a window programmed to N is enforced as N+1 cycles of
command spacing -- the counter is loaded with N on the event and
the gate opens the cycle after it would reach zero. Measured and
bounded tight in formal/pumice/{bank_timer,global_timers}
(a_*_bound_n1). Program the JEDEC value from the part datasheet;
do NOT subtract one to compensate, or the register stops reading
as the part's timing. pumice TASK-034 tracks whether to recover
that cycle -- it is a board measurement, because the empirical
rtw_guard in the host's tRTW derivation was tuned with it
present.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |    tRC   |  rw  | 0x3C|  — |
| 15:8|   tRCD   |  rw  | 0xF |  — |
|23:16|    tRP   |  rw  | 0xF |  — |
|31:24|   tRAS   |  rw  | 0x28|  — |

#### tRC field

<p>tRC -- MC cycles to block; spacing enforced is N+1</p>

#### tRCD field

<p>tRCD -- MC cycles to block; spacing enforced is N+1</p>

#### tRP field

<p>tRP -- MC cycles to block; spacing enforced is N+1</p>

#### tRAS field

<p>tRAS -- MC cycles to block; spacing enforced is N+1</p>

### TIMINGS_RFC_REFI register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>Refresh interval and recovery</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   tRFC   |  rw  | 0x10|  — |
|31:16|   tREFI  |  rw  |0x79E|  — |

#### tRFC field

<p>tRFC (or tRFCab)</p>

#### tREFI field

<p>tREFI</p>

### TIMINGS_RRD_FAW_WTR_CCD register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>Inter-bank + bus turn-around</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |   tRRD   |  rw  | 0x6 |  — |
| 15:8|   tFAW   |  rw  | 0x23|  — |
|23:16|   tWTR   |  rw  | 0x4 |  — |
|31:24|   tCCD   |  rw  | 0x4 |  — |

#### tRRD field

<p>tRRD -- MC cycles to block; spacing enforced is N+1</p>

#### tFAW field

<p>tFAW -- MC cycles; at most 4 ACTs per rank in the window</p>

#### tWTR field

<p>tWTR -- MC cycles to block; spacing enforced is N+1</p>

#### tCCD field

<p>tCCD -- MC cycles to block; spacing enforced is N+1</p>

### TIMINGS_CL_CWL_WR register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

<p>CAS latencies + write recovery + LPDDR2 per-bank tRFC</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |    CL    |  rw  | 0x6 |  — |
| 15:8|    CWL   |  rw  | 0x4 |  — |
|23:16|    tWR   |  rw  | 0xF |  — |
|31:24|  tRFCpb  |  rw  | 0x46|  — |

#### CL field

<p>CAS latency</p>

#### CWL field

<p>CAS write latency</p>

#### tWR field

<p>Write recovery (tWR, from end of burst) -- MC cycles to block; spacing enforced is N+1</p>

#### tRFCpb field

<p>LPDDR2 per-bank tRFC</p>

### MR0 register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>MR0 base value loaded during the init MRS chain (low 16 bits).
Default 0x433 is DDR2 BL8/CL3/tWR3. The init FSM ORs in the DLL
reset bit for the first MR0 load. Runtime-writable so software can
retune the mode register AND sweep the value to defeat an
arbitrary board A-lane mapping on MRS commands: write MRx.VAL then
pulse CTRL.init_force_restart.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|    VAL   |  rw  |0x433|  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### VAL field

<p>MR0 value, DDR2 BL8/CL3/tWR3 default</p>

#### RSVD field

<p>Reserved</p>

### MR1 register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>MR1 value loaded during init (low 16 bits)</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|    VAL   |  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### VAL field

<p>MR1 value</p>

#### RSVD field

<p>Reserved</p>

### MR2 register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

<p>MR2 value loaded during init (low 16 bits)</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|    VAL   |  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### VAL field

<p>MR2 value</p>

#### RSVD field

<p>Reserved</p>

### MR3 register

- Absolute Address: 0x2C
- Base Offset: 0x2C
- Size: 0x4

<p>MR3 value loaded during init (low 16 bits)</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|    VAL   |  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### VAL field

<p>MR3 value</p>

#### RSVD field

<p>Reserved</p>

### REFRESH_TUNING register

- Absolute Address: 0x48
- Base Offset: 0x48
- Size: 0x4

<p>Page-policy override. The refresh fields that lived here (refpb_policy_or, refresh_defer_active, zqcs_freq_hz) were retired 2026-09-09: refresh mode and the JEDEC postpone/pull-in credits are REF_CTRL, and no ZQCS engine consumed the interval. The address is kept so the map does not shift.</p>

| Bits|  Identifier  |Access|Reset|Name|
|-----|--------------|------|-----|----|
| 1:0 |   RSVD_1_0   |   r  | 0x0 |  — |
| 3:2 |page_policy_or|  rw  | 0x0 |  — |
| 15:4|   RSVD_15_4  |   r  | 0x0 |  — |
|31:16|  RSVD_31_16  |   r  | 0x0 |  — |

#### RSVD_1_0 field

<p>Reserved (was refpb_policy_or; see REF_CTRL.mode)</p>

#### page_policy_or field

<p>00=build-time, 01=OPEN, 10=CLOSE, 11=reserved (was HYBRID; maps to build default)</p>

#### RSVD_15_4 field

<p>Reserved (was refresh_defer_active; see REF_CTRL.postpone_limit)</p>

#### RSVD_31_16 field

<p>Reserved (was zqcs_freq_hz; no ZQCS engine)</p>

### ADDR_MAP register

- Absolute Address: 0x4C
- Base Offset: 0x4C
- Size: 0x4

<p>AXI-address -&gt; {rank,row,bank,col} mapping. bank_lsb is where the
bank field sits in the (byte-offset-stripped) word address; the
column fills below (col_lo) and above (col_hi) it, row/rank stack
above. ROW_MAJOR / BANK_INTERLEAVE / XOR_HASH are just settings of
this register (no separate scheme selector). See addr_mapper.sv.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 4:0 | bank_lsb |  rw  | 0xA |  — |
| 7:5 | RSVD_7_5 |   r  | 0x0 |  — |
|  8  |  hash_en |  rw  | 0x0 |  — |
| 15:9| RSVD_15_9|   r  | 0x0 |  — |
|23:16| hash_seed|  rw  | 0x0 |  — |
|31:24|RSVD_31_24|   r  | 0x0 |  — |

#### bank_lsb field

<p>Bank field LSB in the word address (=COL_WIDTH -&gt; ROW_MAJOR)</p>

#### RSVD_7_5 field

<p>Reserved</p>

#### hash_en field

<p>Enable bank XOR-hash: bank ^= fold(row) ^ hash_seed</p>

#### RSVD_15_9 field

<p>Reserved</p>

#### hash_seed field

<p>XOR-hash seed (bank ^= fold(row) ^ seed[BW-1:0])</p>

#### RSVD_31_24 field

<p>Reserved</p>

### TIMINGS_RTP_RTW register

- Absolute Address: 0x54
- Base Offset: 0x54
- Size: 0x4

<p>Read-to-precharge and read-to-write turn-around (JEDEC), in MC
cycles. Previously tRTP was hardcoded (8'd4, 'not yet in CSR map')
and tRTW was tied to tRTP; now both are independent configs.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |   tRTP   |  rw  | 0x4 |  — |
| 15:8|   tRTW   |  rw  | 0x6 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### tRTP field

<p>Read to precharge (tRTP) -- MC cycles to block; spacing enforced is N+1</p>

#### tRTW field

<p>Read to write (tRTW) -- MC cycles to block; spacing enforced is N+1</p>

#### RSVD field

<p>Reserved</p>

### INIT_TIMING0 register

- Absolute Address: 0x58
- Base Offset: 0x58
- Size: 0x4

<p>JEDEC init-sequence waits (MC cycles): CKE/tINIT settle and DLL
lock. Previously hardcoded in init_sequencer.</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0|t_init_wait|  rw  |0x200|  — |
|31:16| t_dll_wait|  rw  |0x100|  — |

#### t_init_wait field

<p>CKE/tINIT settle</p>

#### t_dll_wait field

<p>DLL lock (tDLLK)</p>

### INIT_TIMING1 register

- Absolute Address: 0x5C
- Base Offset: 0x5C
- Size: 0x4

<p>JEDEC init-sequence waits (MC cycles): post-MRS (tMRD),
post-precharge (tRP), post-refresh (tRFC). Previously hardcoded.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |t_mrd_wait|  rw  | 0x8 |  — |
| 15:8| t_rp_wait|  rw  | 0x8 |  — |
|23:16|t_rfc_wait|  rw  | 0x10|  — |
|31:24|   RSVD   |   r  | 0x0 |  — |

#### t_mrd_wait field

<p>tMRD (post mode-reg)</p>

#### t_rp_wait field

<p>tRP (post precharge)</p>

#### t_rfc_wait field

<p>tRFC (post refresh)</p>

#### RSVD field

<p>Reserved</p>

### DFI_PHASE register

- Absolute Address: 0x60
- Base Offset: 0x60
- Size: 0x4

<p>Which DFI sub-phase carries the READ vs WRITE command, to match
the PHY's rdphase/wrphase contract. For the Nexys A7 a7ddrphy
(DDR2/CL3/nphases=2) the on-silicon ILA showed the READ burst is
delivered aligned to rdphase=1 (wrphase=0): issuing RD on phase 0
misaligns the returned burst (1st DFI cycle good, tail corrupt).
Defaults 0/0 preserve the legacy all-on-phase-0 behavior. Fields
are sliced to clog2(DFI_RATE) bits downstream; upper bits ignored
when DFI_RATE &lt; the field width.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 2:0 | rd_phase |  rw  | 0x0 |  — |
| 6:4 | wr_phase |  rw  | 0x0 |  — |
| 8:7 |gear_ratio|   r  | 0x2 |  — |
| 12:9|    bl    |  rw  | 0x8 |  — |
|31:13|   RSVD   |   r  | 0x0 |  — |

#### rd_phase field

<p>READ command DFI sub-phase</p>

#### wr_phase field

<p>WRITE command DFI sub-phase</p>

#### gear_ratio field

<p>gear_ratio = log2(active DFI_RATE). Read-only in granite at log2(GRANITE_DFI_MHZ/GRANITE_ACLK_MHZ) = log2(300/75) = 2; the product frequency plan is the single source of truth.</p>

#### bl field

<p>JEDEC burst length (MR0 device beats): 4/8/16</p>

#### RSVD field

<p>Reserved</p>

### PHY_TIMING register

- Absolute Address: 0x64
- Base Offset: 0x64
- Size: 0x4

<p>t_phy_wrlat: WRITE command -&gt; dfi_wrdata_en. t_rddata_en:
RD command -&gt; dfi_rddata_en window.
t_phy_wrlat resets to 1 because BOTH board host paths program 1,
and the old reset of 0 agreed with neither (TASK-015 plane 0).
t_rddata_en resets to 6 -- what <code>init</code> programs
(pumice_master.SimpleTest: the ILA-validated tuple wrlat=1,
rden=6, rddata_delay=7). pumice_char.ControllerConfig programs 1
with rddata_delay=2 instead, a DIFFERENT valid point on the
measured diagonal rddata_delay = t_rddata_en + 1 (the a7ddrphy
data-vs-valid offset is a fixed 1 cycle). Two host paths
programming two points is pumice ISSUE-015; the reset follows
<code>init</code>, the bring-up authority. Do NOT pin a stale tuple here:
overriding these to 0/6 on 2026-09-21 corrupted data on all four
cells while still reporting healthy bandwidth.
memtype: 0=DDR2, 1=LPDDR2. refresh_burst: 1..8 REFs drained per
request. All hw-readable so they drive the controller core.</p>

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
| 7:0 | t_phy_wrlat |  rw  | 0x1 |  — |
| 15:8| t_rddata_en |  rw  | 0x6 |  — |
|  16 |   memtype   |  rw  | 0x0 |  — |
|19:17|    RSVD0    |   r  | 0x0 |  — |
|23:20|refresh_burst|  rw  | 0x1 |  — |
|31:24|    RSVD1    |   r  | 0x0 |  — |

#### t_phy_wrlat field

<p>t_phy_wrlat (WR cmd -&gt; wrdata_en)</p>

#### t_rddata_en field

<p>t_rddata_en (RD cmd -&gt; rddata_en)</p>

#### memtype field

<p>0=DDR2, 1=LPDDR2</p>

#### RSVD0 field

<p>Reserved</p>

#### refresh_burst field

<p>REFs drained per request (1..8)</p>

#### RSVD1 field

<p>Reserved</p>

### SCHED_POLICY register

- Absolute Address: 0x68
- Base Offset: 0x68
- Size: 0x4

<p>Axis 1 (Rixner FR-FCFS variants). All fields 0 = build default.</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 1:0 | order_mode|  rw  | 0x0 |  — |
| 3:2 |  prio_sub |  rw  | 0x0 |  — |
| 5:4 |  row_sel  |  rw  | 0x0 |  — |
| 7:6 |  col_sel  |  rw  | 0x0 |  — |
| 9:8 |access_pref|  rw  | 0x0 |  — |
|  10 |  RSVD_10  |   r  | 0x0 |  — |
|  11 |   qos_en  |  rw  | 0x0 |  — |
|15:12| RSVD_15_12|   r  | 0x0 |  — |
|23:16| age_thresh|  rw  | 0x0 |  — |
|31:24| RSVD_31_24|   r  | 0x0 |  — |

#### order_mode field

<p>0=build default, 1=in_order, 2=fr_fcfs, 3=age_threshold</p>

#### prio_sub field

<p>Priority sub-policy: 0=default, 1=none, 2=load_over_store, 3=age_boost</p>

#### row_sel field

<p>Row-arbiter select: 0=default(oldest), 1=most_pending, 2=fewest_pending</p>

#### col_sel field

<p>Column-arbiter select: 0=default(oldest), 1=most_pending, 2=fewest_pending</p>

#### access_pref field

<p>Address-arbiter class preference: 0=default, 1=column_first, 2=row_first, 3=precharge_first</p>

#### RSVD_10 field

<p>Reserved (was auto_precharge_en, never consumed: auto-precharge is driven by PAGE_POLICY_CFG.policy_mode -- static_close and the modes 5..7 predictors)</p>

#### qos_en field

<p>1 = factor AxQOS into the pick (highest ready first, age tie-break)</p>

#### RSVD_15_12 field

<p>Reserved</p>

#### age_thresh field

<p>age_threshold mode: age (MC cycles/16) above which a reference is boosted. INERT in granite: the store is built with HAS_AGE=0 (no per-slot ages; pumice TASK-059), so this field has no effect; the pick orders by bank state and class only</p>

#### RSVD_31_24 field

<p>Reserved</p>

### SCHED_WR_WM register

- Absolute Address: 0x6C
- Base Offset: 0x6C
- Size: 0x4

<p>Write-batching drain hysteresis. 0/0 disables it; default
2/1 = ON.</p>
<p>Amortises tWTR/tRTW over a drain instead of paying it per
direction switch. Worth +11.9%..+30.5% bus on the Nexys A7 at
1+1 across gaps 4..15, and never below +0% -- at gap 0 and with
2+2 generators there is no turnaround left to amortise, so it is
a no-op there, not a cost.</p>
<p>Shipped disabled until 2026-09-18 because it corrupted. Three
defects, all fixed (TASK-007): tRFC compression from DFI-side
pacing, tRTW classify-time staleness, and a one-cycle turnaround
seam. Evidence for this default:</p>
<pre><code>210 concurrent runs at open_page      0 failures
4 x full 14-config matrix (1008 cells) 1 mismatched beat
</code></pre>
<p>That one beat was seen once and never reproduced in the 756
cells after it; it is unattributed (BUG-001), NOT a known
batching defect. 2/1 over 8/4 because it wins at gaps 12 and 15,
ties at 4, and a shallower drain parks reads behind a shorter
write run. Still a runtime CSR: this is only the reset value.</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 7:0 | wr_high_wm |  rw  | 0x2 |  — |
| 15:8|  wr_low_wm |  rw  | 0x1 |  — |
|23:16|wr_batch_max|   r  | 0x10|  — |
|31:24|    RSVD    |   r  | 0x0 |  — |

#### wr_high_wm field

<p>Start back-to-back write drain when the write buffer crosses this</p>

#### wr_low_wm field

<p>Stop the drain when occupancy falls to this</p>

#### wr_batch_max field

<p>Maximum consecutive write columns in one batch drain before
the arbiter yields a slot to reads. Read-only in granite at
GRANITE_WR_DATA_BUF_WORDS (=16); the product write-data
staging size is the single source of truth.</p>

#### RSVD field

<p>Reserved</p>

### PAGE_POLICY_CFG register

- Absolute Address: 0x70
- Base Offset: 0x70
- Size: 0x4

<p>Axis 2 mode select + adapt_access counter shape. 0 = build default. Resets to 3 (fixed_open) -- see policy_mode.</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 2:0 |policy_mode|  rw  | 0x3 |  — |
|  3  |   RSVD_3  |   r  | 0x0 |  — |
| 5:4 |  RSVD_5_4 |   r  | 0x0 |  — |
| 9:6 |  RSVD_9_6 |   r  | 0x0 |  — |
|13:10| RSVD_13_10|   r  | 0x0 |  — |
|31:14|    RSVD   |   r  | 0x0 |  — |

#### policy_mode field

<p>0=build default, 1=static_open, 2=static_close, 3=fixed_open. 4/5 RETIRED 2026-09-27 (were adapt_time/adapt_access) and 6/7 RETIRED 2026-09-26 (were rbl_static/rbl_dyn) -- a write of 4..7 falls through to the build default. RESET IS 0. Mode 3 (fixed_open) is the RECOMMENDED default and is measured strictly dominant over open page on the board across every scenario -- +41.2% col_major_interleaved, +8.6..11.6% col_major, and EXACTLY flat on incremental/row_major, with no scenario regressing. The win is the background precharge gated on bank idle (timeout_pre_req_o), not a predictor. Mode 4 was measured to BE fixed_open(tr_min): moving only tr_min moved the result onto the matching fixed point every time, because its mistake counter is dominated by the held-too-long case so TR decayed to the floor and stayed. Mode 5 drove auto-precharge, which costs 4.9x the activations of a background precharge and double the read latency, and AP commits at the column op before it is known whether more same-row requests are coming -- it fights the FR-FCFS reordering that justifies this design. See TASK-013 and TASK-014.</p>

#### RSVD_3 field

<p>Reserved (was policy_scope, 0=per-bank / 1=global decision state). RETIRED 2026-09-27 with adapt_time: the mistake counter was a single GLOBAL register driving all eight per-bank TR registers from one decision, so per-bank scope could not diverge from global and the field selected between two identical behaviours.</p>

#### RSVD_5_4 field

<p>Reserved (was ctr_width; the adapt_access counter is the 2-bit saturating counter of the paper, not selectable)</p>

#### RSVD_9_6 field

<p>Reserved (was ctr_open_max, the adapt_access close threshold). RETIRED 2026-09-27 with mode 5.</p>

#### RSVD_13_10 field

<p>Reserved (was ctr_init, the adapt_access counter init). RETIRED 2026-09-27 with mode 5.</p>

#### RSVD field

<p>Reserved</p>

### PAGE_TIMEOUT_CFG register

- Absolute Address: 0x74
- Base Offset: 0x74
- Size: 0x4

<p>fixed_open idle-timeout register (MC cycles). tr_init is the only live field; the adapt_time clamps and step retired 2026-09-27 with mode 4.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  tr_init |  rw  | 0x2 |  — |
| 15:8| RSVD_15_8|   r  | 0x0 |  — |
|23:16|RSVD_23_16|   r  | 0x0 |  — |
|31:24|RSVD_31_24|   r  | 0x0 |  — |

#### tr_init field

<p>TR init: idle MC cycles a row is held open before the background precharge fires. fixed_open (policy_mode=3) uses this alone. RESET IS 2, the measured optimum, changed from 0 on 2026-09-27 together with policy_mode. tr_init=0 DISABLES the timeout entirely (see f_tr/r_idle in pumice_page_policy.sv) -- it is not a build-default sentinel on this field, so a reset of 0 silently disabled mode 3 and is why these two resets must move together. MEASURED ON THE BOARD 2026-09-27 at 75 MHz BL4 x16 against a 600 MB/s peak, 24 cells over four scenario families, all integrity-clean: TR=1 and TR=2 identical, and TR=2 gives +9.1% col_major (195.2 -&gt; 212.9 MB/s) and +35.1% col_major_interleaved (262.1 -&gt; 354.1), exactly flat on incremental (561.1) and row_major (572.0), with no scenario regressing. The cliff is between 2 and 3 on col_major, which is why 2 and not 4. This change was made and REVERTED on 2026-09-26 because BUG-003 let a short timeout push a rejected pick to the DRAM; BUG-003 was fixed 2026-09-27 and the board run above is post-fix with mismatched=0 on every cell.</p>

#### RSVD_15_8 field

<p>Reserved (was tr_min, the adapt_time TR lower clamp). RETIRED 2026-09-27 with mode 4 -- fixed_open uses tr_init alone. Bit position held so tr_init does not move.</p>

#### RSVD_23_16 field

<p>Reserved (was tr_max, the adapt_time TR upper clamp). RETIRED 2026-09-27 with mode 4.</p>

#### RSVD_31_24 field

<p>Reserved (was tr_step, the adapt_time TR adjustment step). RETIRED 2026-09-27 with mode 4.</p>

### CAL_CTRL register

- Absolute Address: 0xA0
- Base Offset: 0xA0
- Size: 0x4

<p>ZQ + DQ calibration control strobes and enables</p>

| Bits|  Identifier  |Access|Reset|Name|
|-----|--------------|------|-----|----|
|  0  |     zq_en    |  rw  | 0x0 |  — |
|  1  |  zq_defer_en |  rw  | 0x0 |  — |
| 3:2 |   RSVD_3_2   |   r  | 0x0 |  — |
|  4  |   cal_start  |  rw  | 0x0 |  — |
|  5  |   cal_abort  |  rw  | 0x0 |  — |
| 15:6|   RSVD_15_6  |   r  | 0x0 |  — |
|28:16|zq_overdue_max|  rw  | 0x0 |  — |
|31:29|  RSVD_31_29  |   r  | 0x0 |  — |

#### zq_en field

<p>Enable periodic ZQCS/ZQCL</p>

#### zq_defer_en field

<p>Mode-C deferral: hold ZQ under demand</p>

#### RSVD_3_2 field

<p>Reserved</p>

#### cal_start field

<p>Write 1 to start a DQ-cal sequence (self-clearing command)</p>

#### cal_abort field

<p>Write 1 to abort the current DQ-cal sequence</p>

#### RSVD_15_6 field

<p>Reserved</p>

#### zq_overdue_max field

<p>Max ZQ deferral cycles before overdue (0 = no cap)</p>

#### RSVD_31_29 field

<p>Reserved</p>

### CAL_ZQ_INTERVAL register

- Absolute Address: 0xA4
- Base Offset: 0xA4
- Size: 0x4

<p>ZQCS interval in MC cycles, 0 = disabled</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |  rw  | 0x0 |  — |

#### VAL field

<p>ZQCS interval</p>

### CAL_ZQ_TIMING register

- Absolute Address: 0xA8
- Base Offset: 0xA8
- Size: 0x4

<p>Bus-quiet window after a ZQCS/ZQCL MRW grant</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|  t_zqcs  |  rw  | 0x0 |  — |
|31:16|  t_zqcl  |  rw  | 0x0 |  — |

#### t_zqcs field

<p>ZQCS post-grant hold</p>

#### t_zqcl field

<p>ZQCL post-grant hold</p>

### CAL_TRAIN_TIMING register

- Absolute Address: 0xAC
- Base Offset: 0xAC
- Size: 0x4

<p>MRR spacing and readout timeout for DQ calibration</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   t_mrr  |  rw  | 0x2 |  — |
|31:16| t_readout|  rw  | 0x0 |  — |

#### t_mrr field

<p>MRR-to-MRR spacing (MC cycles)</p>

#### t_readout field

<p>MRR issue -&gt; data timeout</p>

## CAL_MRR32_DATA register file

- Absolute Address: 0xB0
- Base Offset: 0xB0
- Size: 0x4
- Array Dimensions: [4]
- Array Stride: 0x4
- Total Size: 0x10

<p>First captured DFI read-data beat for MRR MR32 (pattern A).</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |    VAL   |  — |

### VAL register

- Absolute Address: 0xB0
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>32-bit slice of captured MRR32 data</p>

## CAL_MRR32_DATA register file

- Absolute Address: 0xB4
- Base Offset: 0xB0
- Size: 0x4
- Array Dimensions: [4]
- Array Stride: 0x4
- Total Size: 0x10

<p>First captured DFI read-data beat for MRR MR32 (pattern A).</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |    VAL   |  — |

### VAL register

- Absolute Address: 0xB4
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>32-bit slice of captured MRR32 data</p>

## CAL_MRR32_DATA register file

- Absolute Address: 0xB8
- Base Offset: 0xB0
- Size: 0x4
- Array Dimensions: [4]
- Array Stride: 0x4
- Total Size: 0x10

<p>First captured DFI read-data beat for MRR MR32 (pattern A).</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |    VAL   |  — |

### VAL register

- Absolute Address: 0xB8
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>32-bit slice of captured MRR32 data</p>

## CAL_MRR32_DATA register file

- Absolute Address: 0xBC
- Base Offset: 0xB0
- Size: 0x4
- Array Dimensions: [4]
- Array Stride: 0x4
- Total Size: 0x10

<p>First captured DFI read-data beat for MRR MR32 (pattern A).</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |    VAL   |  — |

### VAL register

- Absolute Address: 0xBC
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>32-bit slice of captured MRR32 data</p>

## CAL_MRR40_DATA register file

- Absolute Address: 0xE0
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [4]
- Array Stride: 0x4
- Total Size: 0x10

<p>First captured DFI read-data beat for MRR MR40 (pattern B).</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |    VAL   |  — |

### VAL register

- Absolute Address: 0xE0
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>32-bit slice of captured MRR40 data</p>

## CAL_MRR40_DATA register file

- Absolute Address: 0xE4
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [4]
- Array Stride: 0x4
- Total Size: 0x10

<p>First captured DFI read-data beat for MRR MR40 (pattern B).</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |    VAL   |  — |

### VAL register

- Absolute Address: 0xE4
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>32-bit slice of captured MRR40 data</p>

## CAL_MRR40_DATA register file

- Absolute Address: 0xE8
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [4]
- Array Stride: 0x4
- Total Size: 0x10

<p>First captured DFI read-data beat for MRR MR40 (pattern B).</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |    VAL   |  — |

### VAL register

- Absolute Address: 0xE8
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>32-bit slice of captured MRR40 data</p>

## CAL_MRR40_DATA register file

- Absolute Address: 0xEC
- Base Offset: 0xE0
- Size: 0x4
- Array Dimensions: [4]
- Array Stride: 0x4
- Total Size: 0x10

<p>First captured DFI read-data beat for MRR MR40 (pattern B).</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |    VAL   |  — |

### VAL register

- Absolute Address: 0xEC
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>32-bit slice of captured MRR40 data</p>

### CAL_STATUS register

- Absolute Address: 0xF0
- Base Offset: 0xF0
- Size: 0x4

<p>Training plane telemetry; sticky done/err, cleared by soft reset</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
|  0  |  zq_busy |   r  |  —  |  — |
|  1  | cal_busy |   r  |  —  |  — |
|  2  | cal_done |   r  |  —  |  — |
|  3  |  cal_err |   r  |  —  |  — |
|  4  |zq_overdue|   r  |  —  |  — |
| 15:5| RSVD_15_5|   r  | 0x0 |  — |
|31:16|zqcs_total|   r  | 0x0 |  — |

#### zq_busy field

<p>ZQ calibration busy</p>

#### cal_busy field

<p>DQ calibration busy</p>

#### cal_done field

<p>DQ calibration done (sticky)</p>

#### cal_err field

<p>DQ calibration error (sticky)</p>

#### zq_overdue field

<p>ZQ interval expired without grant</p>

#### RSVD_15_5 field

<p>Reserved</p>

#### zqcs_total field

<p>ZQCS/ZQCL commands issued since reset</p>

### LP_MR1_OP register

- Absolute Address: 0x180
- Base Offset: 0x180
- Size: 0x4

<p>MRW OP value written to LPDDR2 MR1 (nWR/WC/BT/BL) during init.
JESD209-2F default 0x23 = nWR3/WC0/BT0/BL8.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|    VAL   |  rw  | 0x23|  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### VAL field

<p>LPDDR2 MR1 OP value</p>

#### RSVD field

<p>Reserved</p>

### LP_MR2_OP register

- Absolute Address: 0x184
- Base Offset: 0x184
- Size: 0x4

<p>MRW OP value written to LPDDR2 MR2 (RL/WL) during init.
JESD209-2F default 0x01 = RL3/WL1.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|    VAL   |  rw  | 0x1 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### VAL field

<p>LPDDR2 MR2 OP value</p>

#### RSVD field

<p>Reserved</p>

### LP_MR3_OP register

- Absolute Address: 0x188
- Base Offset: 0x188
- Size: 0x4

<p>MRW OP value written to LPDDR2 MR3 (drive strength) during init.
JESD209-2F default 0x02 = DS 40ohm.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|    VAL   |  rw  | 0x2 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### VAL field

<p>LPDDR2 MR3 OP value</p>

#### RSVD field

<p>Reserved</p>

### STORE_STATS_MERGE register

- Absolute Address: 0x18C
- Base Offset: 0x18C
- Size: 0x4

<p>TASK-006. Writes MERGED into a live, uncommitted write entry of the same
{bank,row,col} in the FIFO store (their strobed bytes land in that entry,
which then owes a second B). Free-running; read as a delta around a run.
0 when STORE_MERGE_EN = 0.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>write merges performed</p>

### STORE_STATS_RD_MERGE register

- Absolute Address: 0x190
- Base Offset: 0x190
- Size: 0x4

<p>TASK-006. Reads COMBINED into a live, unissued read entry of the same
{bank,row,col} in the FIFO store (one DRAM burst, returned twice through
the return ring as a shadow ticket). Free-running; read as a delta around
a run. 0 when STORE_MERGE_EN = 0.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>read merges performed</p>

### ID register

- Absolute Address: 0xFF0
- Base Offset: 0xFF0
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  version |   r  | 0x1 |  — |
| 15:8|  memtype |   r  | 0x0 |  — |
|23:16| n_phases |   r  | 0x2 |  — |
|31:24| module_id|   r  | 0xD2|  — |

#### version field

<p>Build version</p>

#### memtype field

<p>0=DDR2, 1=LPDDR2</p>

#### n_phases field

<p>Gear ratio (1, 2, or 4)</p>

#### module_id field

<p>Fixed 0xD2</p>

### BUILD register

- Absolute Address: 0xFF4
- Base Offset: 0xFF4
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  | 0x0 |  — |

#### VAL field

<p>Build hash word</p>
