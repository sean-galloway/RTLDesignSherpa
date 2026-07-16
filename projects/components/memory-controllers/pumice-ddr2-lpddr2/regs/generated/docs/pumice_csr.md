<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## pumice_csr address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0xFF8

<p>Configuration and observation registers for the DDR2/LPDDR2 controller</p>

|Offset|       Identifier       |                  Name                 |
|------|------------------------|---------------------------------------|
| 0x000|          CTRL          |            Control Register           |
| 0x004|         STATUS         |            Status Register            |
| 0x008|     STATUS_HISTORY     |             Status History            |
| 0x010|  TIMINGS_RC_RCD_RP_RAS |    Timings: tRC / tRCD / tRP / tRAS   |
| 0x014|    TIMINGS_RFC_REFI    |         Timings: tRFC / tREFI         |
| 0x018| TIMINGS_RRD_FAW_WTR_CCD|   Timings: tRRD / tFAW / tWTR / tCCD  |
| 0x01C|    TIMINGS_CL_CWL_WR   |    Timings: CL / CWL / tWR / tRFCpb   |
| 0x020|           MR0          |            Mode Register 0            |
| 0x024|           MR1          |            Mode Register 1            |
| 0x028|           MR2          |            Mode Register 2            |
| 0x02C|           MR3          |            Mode Register 3            |
| 0x030|  PASR_BANK_MASK_RANK0  |         PASR Bank Mask Rank 0         |
| 0x034|   PASR_SEG_MASK_RANK0  |        PASR Segment Mask Rank 0       |
| 0x038|    TEMP_DERATE_RANK0   |       Temperature Derate Rank 0       |
| 0x040|      SCHED_TUNING      |            Scheduler Tuning           |
| 0x044|    PAGE_PRED_TUNING    |         Page Predictor Tuning         |
| 0x048|     REFRESH_TUNING     |             Refresh Tuning            |
| 0x04C|        ADDR_MAP        |              Address Map              |
| 0x050|       INIT_TUNING      |              Init Tuning              |
| 0x054|     TIMINGS_RTP_RTW    |          Timings: tRTP / tRTW         |
| 0x058|      INIT_TIMING0      |      Init Timing 0: tINIT / tDLLK     |
| 0x05C|      INIT_TIMING1      |Init Timing 1: tMRD / tRP / tRFC (init)|
| 0x060|        DFI_PHASE       |      DFI Command Phase Placement      |
| 0x064|       PHY_TIMING       | PHY / DFI data timing + memory config |
| 0x080|     OBS_ROW_HIT[0]     |      Per-Bank Row Hit Observation     |
| 0x084|     OBS_ROW_HIT[1]     |      Per-Bank Row Hit Observation     |
| 0x088|     OBS_ROW_HIT[2]     |      Per-Bank Row Hit Observation     |
| 0x08C|     OBS_ROW_HIT[3]     |      Per-Bank Row Hit Observation     |
| 0x090|     OBS_ROW_HIT[4]     |      Per-Bank Row Hit Observation     |
| 0x094|     OBS_ROW_HIT[5]     |      Per-Bank Row Hit Observation     |
| 0x098|     OBS_ROW_HIT[6]     |      Per-Bank Row Hit Observation     |
| 0x09C|     OBS_ROW_HIT[7]     |      Per-Bank Row Hit Observation     |
| 0x0C0|   OBS_REF_LATENCY[0]   |  Per-Bank Refresh Latency Observation |
| 0x0C4|   OBS_REF_LATENCY[1]   |  Per-Bank Refresh Latency Observation |
| 0x0C8|   OBS_REF_LATENCY[2]   |  Per-Bank Refresh Latency Observation |
| 0x0CC|   OBS_REF_LATENCY[3]   |  Per-Bank Refresh Latency Observation |
| 0x0D0|   OBS_REF_LATENCY[4]   |  Per-Bank Refresh Latency Observation |
| 0x0D4|   OBS_REF_LATENCY[5]   |  Per-Bank Refresh Latency Observation |
| 0x0D8|   OBS_REF_LATENCY[6]   |  Per-Bank Refresh Latency Observation |
| 0x0DC|   OBS_REF_LATENCY[7]   |  Per-Bank Refresh Latency Observation |
| 0x100| OBS_TXN_QUEUE_DEPTH_MAX|                   —                   |
| 0x104| OBS_TXN_QUEUE_DEPTH_AVG|                   —                   |
| 0x108| OBS_REFRESH_PENDING_MAX|                   —                   |
| 0x10C|OBS_REFRESH_DEFER_HIST_0|                   —                   |
| 0x110|OBS_REFRESH_DEFER_HIST_1|                   —                   |
| 0x114|OBS_REFRESH_DEFER_HIST_2|                   —                   |
| 0x118|OBS_REFRESH_DEFER_HIST_3|                   —                   |
| 0x120| OBS_PAGE_PRED_ACCURACY |                   —                   |
| 0x130|  OBS_AXI_R_LATENCY_AVG |                   —                   |
| 0x134|  OBS_AXI_R_LATENCY_P99 |                   —                   |
| 0x138|  OBS_AXI_W_LATENCY_AVG |                   —                   |
| 0x1C0|      OBS_WORDS[0]      |        Observation Word Harvest       |
| 0x1C4|      OBS_WORDS[1]      |        Observation Word Harvest       |
| 0x1C8|      OBS_WORDS[2]      |        Observation Word Harvest       |
| 0x1CC|      OBS_WORDS[3]      |        Observation Word Harvest       |
| 0x1D0|      OBS_WORDS[4]      |        Observation Word Harvest       |
| 0x1D4|      OBS_WORDS[5]      |        Observation Word Harvest       |
| 0x1D8|      OBS_WORDS[6]      |        Observation Word Harvest       |
| 0x1DC|      OBS_WORDS[7]      |        Observation Word Harvest       |
| 0x1E0|      OBS_WORDS[8]      |        Observation Word Harvest       |
| 0xFF0|           ID           |               Module ID               |
| 0xFF4|          BUILD         |               Build Hash              |

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

### STATUS_HISTORY register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Last 8 power-state transitions, 4 bits each. Most recent in [3:0].</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|  history |   r  |  —  |  — |

#### history field

<p>8 x 4-bit power-state history</p>

### TIMINGS_RC_RCD_RP_RAS register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>Packed timing parameters in MC cycles</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |    tRC   |  rw  | 0x3C|  — |
| 15:8|   tRCD   |  rw  | 0xF |  — |
|23:16|    tRP   |  rw  | 0xF |  — |
|31:24|   tRAS   |  rw  | 0x28|  — |

#### tRC field

<p>tRC</p>

#### tRCD field

<p>tRCD</p>

#### tRP field

<p>tRP</p>

#### tRAS field

<p>tRAS</p>

### TIMINGS_RFC_REFI register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>Refresh interval and recovery</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   tRFC   |  rw  | 0xC8|  — |
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

<p>tRRD</p>

#### tFAW field

<p>tFAW</p>

#### tWTR field

<p>tWTR</p>

#### tCCD field

<p>tCCD</p>

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

<p>Write recovery</p>

#### tRFCpb field

<p>LPDDR2 per-bank tRFC</p>

### MR0 register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>MR0 value loaded during init (low 16 bits)</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|    VAL   |  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### VAL field

<p>MR0 value</p>

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

### PASR_BANK_MASK_RANK0 register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

<p>LPDDR2 PASR per-bank mask for rank 0 (MR16). Bit N=1 masks bank N.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|pasr_banks|  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### pasr_banks field

<p>Bank mask</p>

#### RSVD field

<p>Reserved</p>

### PASR_SEG_MASK_RANK0 register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

<p>LPDDR2 PASR segment mask for rank 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0| pasr_segs|  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### pasr_segs field

<p>Segment mask</p>

#### RSVD field

<p>Reserved</p>

### TEMP_DERATE_RANK0 register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

<p>LPDDR2 MR4 temperature class for rank 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 1:0|temp_class|   r  |  —  |  — |
|31:2|   RSVD   |   r  | 0x0 |  — |

#### temp_class field

<p>00 = nominal, 01 = 2x refresh, 10 = 4x refresh</p>

#### RSVD field

<p>Reserved</p>

### SCHED_TUNING register

- Absolute Address: 0x40
- Base Offset: 0x40
- Size: 0x4

<p>Runtime scheduler knobs (effective at next quiet point)</p>

| Bits|     Identifier     |Access|Reset|Name|
|-----|--------------------|------|-----|----|
| 3:0 |  lookahead_active  |  rw  | 0x0 |  — |
|  4  |    force_inorder   |  rw  | 0x0 |  — |
|  5  |    happy_enable    |  rw  | 0x1 |  — |
| 7:6 |      RSVD_7_6      |   r  | 0x0 |  — |
| 15:8|   age_max_runtime  |  rw  | 0x0 |  — |
|23:16|txn_queue_high_water|  rw  | 0x0 |  — |
|27:24|  lookahead_max_obs |   r  |  —  |  — |
|31:28|     RSVD_31_28     |   r  | 0x0 |  — |

#### lookahead_active field

<p>Active lookahead window (0..LOOKAHEAD_DEPTH_MAX). 0 disables.</p>

#### force_inorder field

<p>1 = force first-ready FIFO (disable row-hit reordering)</p>

#### happy_enable field

<p>1 = HAPPY predictor active (only meaningful if synthesized)</p>

#### RSVD_7_6 field

<p>Reserved</p>

#### age_max_runtime field

<p>Runtime AGE_MAX override (0 = use build-time default)</p>

#### txn_queue_high_water field

<p>Backpressure-assertion threshold for txn queue</p>

#### lookahead_max_obs field

<p>Echo of build-time LOOKAHEAD_DEPTH_MAX</p>

#### RSVD_31_28 field

<p>Reserved</p>

### PAGE_PRED_TUNING register

- Absolute Address: 0x44
- Base Offset: 0x44
- Size: 0x4

<p>HAPPY-mode predictor knobs</p>

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
| 15:0|warmup_cycles|  rw  |0x400|  — |
|23:16|  hysteresis |  rw  | 0x2 |  — |
|31:24|     RSVD    |   r  | 0x0 |  — |

#### warmup_cycles field

<p>Warmup cycles</p>

#### hysteresis field

<p>Hysteresis</p>

#### RSVD field

<p>Reserved</p>

### REFRESH_TUNING register

- Absolute Address: 0x48
- Base Offset: 0x48
- Size: 0x4

<p>Refresh policy + ZQCS interval</p>

| Bits|     Identifier     |Access|Reset|Name|
|-----|--------------------|------|-----|----|
| 1:0 |   refpb_policy_or  |  rw  | 0x0 |  — |
| 3:2 |   page_policy_or   |  rw  | 0x0 |  — |
| 7:4 |refresh_defer_active|  rw  | 0x1 |  — |
| 15:8|      RSVD_15_8     |   r  | 0x0 |  — |
|31:16|    zqcs_freq_hz    |  rw  | 0x1 |  — |

#### refpb_policy_or field

<p>00=build-time, 01=RR, 10=OLDEST_FIRST, 11=DARP</p>

#### page_policy_or field

<p>00=build-time, 01=OPEN, 10=CLOSE, 11=HAPPY_HYBRID</p>

#### refresh_defer_active field

<p>Active refresh deferral count (1..REFRESH_DEFER_MAX)</p>

#### RSVD_15_8 field

<p>Reserved</p>

#### zqcs_freq_hz field

<p>Periodic ZQCS interval in Hz (0 = disabled)</p>

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

### INIT_TUNING register

- Absolute Address: 0x50
- Base Offset: 0x50
- Size: 0x4

<p>ZQ retries + per-step init timeout</p>

| Bits|   Identifier  |Access|Reset|Name|
|-----|---------------|------|-----|----|
| 3:0 |   zq_retries  |  rw  | 0x3 |  — |
| 7:4 |    RSVD_7_4   |   r  | 0x0 |  — |
| 15:8|init_timeout_ms|  rw  | 0xA |  — |
|31:16|   RSVD_31_16  |   r  | 0x0 |  — |

#### zq_retries field

<p>ZQ retries (1..8)</p>

#### RSVD_7_4 field

<p>Reserved</p>

#### init_timeout_ms field

<p>Init timeout ms (1..255)</p>

#### RSVD_31_16 field

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

<p>Read to precharge</p>

#### tRTW field

<p>Read to write</p>

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
| 8:7 |gear_ratio|  rw  | 0x2 |  — |
| 12:9|    bl    |  rw  | 0x4 |  — |
|31:13|   RSVD   |   r  | 0x0 |  — |

#### rd_phase field

<p>READ command DFI sub-phase</p>

#### wr_phase field

<p>WRITE command DFI sub-phase</p>

#### gear_ratio field

<p>gear_ratio = log2(active DFI_RATE)</p>

#### bl field

<p>JEDEC burst length (MR0 device beats): 4/8/16</p>

#### RSVD field

<p>Reserved</p>

### PHY_TIMING register

- Absolute Address: 0x64
- Base Offset: 0x64
- Size: 0x4

<p>t_phy_wrlat: WRITE command -&gt; dfi_wrdata_en (0 for a7ddrphy
pre-pull). t_rddata_en: RD command -&gt; dfi_rddata_en window.
memtype: 0=DDR2, 1=LPDDR2. refresh_burst: 1..8 REFs drained per
request. All hw-readable so they drive the controller core.</p>

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
| 7:0 | t_phy_wrlat |  rw  | 0x0 |  — |
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

## OBS_ROW_HIT register file

- Absolute Address: 0x80
- Base Offset: 0x80
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Rolling row-hit count per bank. Reset on read or soft_reset.</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  ROW_HIT |  — |

### ROW_HIT register

- Absolute Address: 0x80
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier| Access |Reset|Name|
|----|----------|--------|-----|----|
|31:0|    VAL   |rw, rclr|  —  |  — |

#### VAL field

<p>Row-hit count</p>

## OBS_ROW_HIT register file

- Absolute Address: 0x84
- Base Offset: 0x80
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Rolling row-hit count per bank. Reset on read or soft_reset.</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  ROW_HIT |  — |

### ROW_HIT register

- Absolute Address: 0x84
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier| Access |Reset|Name|
|----|----------|--------|-----|----|
|31:0|    VAL   |rw, rclr|  —  |  — |

#### VAL field

<p>Row-hit count</p>

## OBS_ROW_HIT register file

- Absolute Address: 0x88
- Base Offset: 0x80
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Rolling row-hit count per bank. Reset on read or soft_reset.</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  ROW_HIT |  — |

### ROW_HIT register

- Absolute Address: 0x88
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier| Access |Reset|Name|
|----|----------|--------|-----|----|
|31:0|    VAL   |rw, rclr|  —  |  — |

#### VAL field

<p>Row-hit count</p>

## OBS_ROW_HIT register file

- Absolute Address: 0x8C
- Base Offset: 0x80
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Rolling row-hit count per bank. Reset on read or soft_reset.</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  ROW_HIT |  — |

### ROW_HIT register

- Absolute Address: 0x8C
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier| Access |Reset|Name|
|----|----------|--------|-----|----|
|31:0|    VAL   |rw, rclr|  —  |  — |

#### VAL field

<p>Row-hit count</p>

## OBS_ROW_HIT register file

- Absolute Address: 0x90
- Base Offset: 0x80
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Rolling row-hit count per bank. Reset on read or soft_reset.</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  ROW_HIT |  — |

### ROW_HIT register

- Absolute Address: 0x90
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier| Access |Reset|Name|
|----|----------|--------|-----|----|
|31:0|    VAL   |rw, rclr|  —  |  — |

#### VAL field

<p>Row-hit count</p>

## OBS_ROW_HIT register file

- Absolute Address: 0x94
- Base Offset: 0x80
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Rolling row-hit count per bank. Reset on read or soft_reset.</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  ROW_HIT |  — |

### ROW_HIT register

- Absolute Address: 0x94
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier| Access |Reset|Name|
|----|----------|--------|-----|----|
|31:0|    VAL   |rw, rclr|  —  |  — |

#### VAL field

<p>Row-hit count</p>

## OBS_ROW_HIT register file

- Absolute Address: 0x98
- Base Offset: 0x80
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Rolling row-hit count per bank. Reset on read or soft_reset.</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  ROW_HIT |  — |

### ROW_HIT register

- Absolute Address: 0x98
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier| Access |Reset|Name|
|----|----------|--------|-----|----|
|31:0|    VAL   |rw, rclr|  —  |  — |

#### VAL field

<p>Row-hit count</p>

## OBS_ROW_HIT register file

- Absolute Address: 0x9C
- Base Offset: 0x80
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Rolling row-hit count per bank. Reset on read or soft_reset.</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  ROW_HIT |  — |

### ROW_HIT register

- Absolute Address: 0x9C
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier| Access |Reset|Name|
|----|----------|--------|-----|----|
|31:0|    VAL   |rw, rclr|  —  |  — |

#### VAL field

<p>Row-hit count</p>

## OBS_REF_LATENCY register file

- Absolute Address: 0xC0
- Base Offset: 0xC0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Average refresh blocking time per bank</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  REF_LAT |  — |

### REF_LAT register

- Absolute Address: 0xC0
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Refresh-blocking cycles</p>

## OBS_REF_LATENCY register file

- Absolute Address: 0xC4
- Base Offset: 0xC0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Average refresh blocking time per bank</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  REF_LAT |  — |

### REF_LAT register

- Absolute Address: 0xC4
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Refresh-blocking cycles</p>

## OBS_REF_LATENCY register file

- Absolute Address: 0xC8
- Base Offset: 0xC0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Average refresh blocking time per bank</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  REF_LAT |  — |

### REF_LAT register

- Absolute Address: 0xC8
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Refresh-blocking cycles</p>

## OBS_REF_LATENCY register file

- Absolute Address: 0xCC
- Base Offset: 0xC0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Average refresh blocking time per bank</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  REF_LAT |  — |

### REF_LAT register

- Absolute Address: 0xCC
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Refresh-blocking cycles</p>

## OBS_REF_LATENCY register file

- Absolute Address: 0xD0
- Base Offset: 0xC0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Average refresh blocking time per bank</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  REF_LAT |  — |

### REF_LAT register

- Absolute Address: 0xD0
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Refresh-blocking cycles</p>

## OBS_REF_LATENCY register file

- Absolute Address: 0xD4
- Base Offset: 0xC0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Average refresh blocking time per bank</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  REF_LAT |  — |

### REF_LAT register

- Absolute Address: 0xD4
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Refresh-blocking cycles</p>

## OBS_REF_LATENCY register file

- Absolute Address: 0xD8
- Base Offset: 0xC0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Average refresh blocking time per bank</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  REF_LAT |  — |

### REF_LAT register

- Absolute Address: 0xD8
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Refresh-blocking cycles</p>

## OBS_REF_LATENCY register file

- Absolute Address: 0xDC
- Base Offset: 0xC0
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Average refresh blocking time per bank</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |  REF_LAT |  — |

### REF_LAT register

- Absolute Address: 0xDC
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Refresh-blocking cycles</p>

### OBS_TXN_QUEUE_DEPTH_MAX register

- Absolute Address: 0x100
- Base Offset: 0x100
- Size: 0x4

<p>Max queue depth observed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Max depth</p>

### OBS_TXN_QUEUE_DEPTH_AVG register

- Absolute Address: 0x104
- Base Offset: 0x104
- Size: 0x4

<p>Time-averaged queue depth</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Avg depth</p>

### OBS_REFRESH_PENDING_MAX register

- Absolute Address: 0x108
- Base Offset: 0x108
- Size: 0x4

<p>Max refresh_pending observed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Max pending</p>

### OBS_REFRESH_DEFER_HIST_0 register

- Absolute Address: 0x10C
- Base Offset: 0x10C
- Size: 0x4

<p>Refresh-deferral histogram bin 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Bin 0 count</p>

### OBS_REFRESH_DEFER_HIST_1 register

- Absolute Address: 0x110
- Base Offset: 0x110
- Size: 0x4

<p>Refresh-deferral histogram bin 1</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Bin 1 count</p>

### OBS_REFRESH_DEFER_HIST_2 register

- Absolute Address: 0x114
- Base Offset: 0x114
- Size: 0x4

<p>Refresh-deferral histogram bin 2</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Bin 2 count</p>

### OBS_REFRESH_DEFER_HIST_3 register

- Absolute Address: 0x118
- Base Offset: 0x118
- Size: 0x4

<p>Refresh-deferral histogram bin 3</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Bin 3 count</p>

### OBS_PAGE_PRED_ACCURACY register

- Absolute Address: 0x120
- Base Offset: 0x120
- Size: 0x4

<p>HAPPY-mode rolling prediction accuracy (%)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Accuracy %</p>

### OBS_AXI_R_LATENCY_AVG register

- Absolute Address: 0x130
- Base Offset: 0x130
- Size: 0x4

<p>Avg AXI read latency (cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Avg cycles</p>

### OBS_AXI_R_LATENCY_P99 register

- Absolute Address: 0x134
- Base Offset: 0x134
- Size: 0x4

<p>99th-pct AXI read latency</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>P99 cycles</p>

### OBS_AXI_W_LATENCY_AVG register

- Absolute Address: 0x138
- Base Offset: 0x138
- Size: 0x4

<p>Avg AXI write latency</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Avg cycles</p>

## OBS_WORDS register file

- Absolute Address: 0x1C0
- Base Offset: 0x1C0
- Size: 0x4
- Array Dimensions: [9]
- Array Stride: 0x4
- Total Size: 0x24

<p>Packed obs_* signals from FUB internals (see csr_obs_layout.md)</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   WORD   |  — |

### WORD register

- Absolute Address: 0x1C0
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Obs word</p>

## OBS_WORDS register file

- Absolute Address: 0x1C4
- Base Offset: 0x1C0
- Size: 0x4
- Array Dimensions: [9]
- Array Stride: 0x4
- Total Size: 0x24

<p>Packed obs_* signals from FUB internals (see csr_obs_layout.md)</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   WORD   |  — |

### WORD register

- Absolute Address: 0x1C4
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Obs word</p>

## OBS_WORDS register file

- Absolute Address: 0x1C8
- Base Offset: 0x1C0
- Size: 0x4
- Array Dimensions: [9]
- Array Stride: 0x4
- Total Size: 0x24

<p>Packed obs_* signals from FUB internals (see csr_obs_layout.md)</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   WORD   |  — |

### WORD register

- Absolute Address: 0x1C8
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Obs word</p>

## OBS_WORDS register file

- Absolute Address: 0x1CC
- Base Offset: 0x1C0
- Size: 0x4
- Array Dimensions: [9]
- Array Stride: 0x4
- Total Size: 0x24

<p>Packed obs_* signals from FUB internals (see csr_obs_layout.md)</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   WORD   |  — |

### WORD register

- Absolute Address: 0x1CC
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Obs word</p>

## OBS_WORDS register file

- Absolute Address: 0x1D0
- Base Offset: 0x1C0
- Size: 0x4
- Array Dimensions: [9]
- Array Stride: 0x4
- Total Size: 0x24

<p>Packed obs_* signals from FUB internals (see csr_obs_layout.md)</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   WORD   |  — |

### WORD register

- Absolute Address: 0x1D0
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Obs word</p>

## OBS_WORDS register file

- Absolute Address: 0x1D4
- Base Offset: 0x1C0
- Size: 0x4
- Array Dimensions: [9]
- Array Stride: 0x4
- Total Size: 0x24

<p>Packed obs_* signals from FUB internals (see csr_obs_layout.md)</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   WORD   |  — |

### WORD register

- Absolute Address: 0x1D4
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Obs word</p>

## OBS_WORDS register file

- Absolute Address: 0x1D8
- Base Offset: 0x1C0
- Size: 0x4
- Array Dimensions: [9]
- Array Stride: 0x4
- Total Size: 0x24

<p>Packed obs_* signals from FUB internals (see csr_obs_layout.md)</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   WORD   |  — |

### WORD register

- Absolute Address: 0x1D8
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Obs word</p>

## OBS_WORDS register file

- Absolute Address: 0x1DC
- Base Offset: 0x1C0
- Size: 0x4
- Array Dimensions: [9]
- Array Stride: 0x4
- Total Size: 0x24

<p>Packed obs_* signals from FUB internals (see csr_obs_layout.md)</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   WORD   |  — |

### WORD register

- Absolute Address: 0x1DC
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Obs word</p>

## OBS_WORDS register file

- Absolute Address: 0x1E0
- Base Offset: 0x1C0
- Size: 0x4
- Array Dimensions: [9]
- Array Stride: 0x4
- Total Size: 0x24

<p>Packed obs_* signals from FUB internals (see csr_obs_layout.md)</p>

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   WORD   |  — |

### WORD register

- Absolute Address: 0x1E0
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Obs word</p>

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
