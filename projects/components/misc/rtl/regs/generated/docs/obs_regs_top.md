<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## obs_regs_top address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0xDC

<p>APB-fronted configuration for the inline performance observer</p>

|Offset|Identifier|           Name           |
|------|----------|--------------------------|
|  0x0 |    OBS   |DMA observer configuration|

## OBS register file

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0xDC

<p>Runtime config for the inline performance-observation block</p>

|Offset|   Identifier   |           Name          |
|------|----------------|-------------------------|
| 0x00 |  AXI_PKT_MASK  |     AXI packet mask     |
| 0x04 |    AXI_MASK1   |        AXI mask1        |
| 0x08 |    AXI_MASK2   |        AXI mask2        |
| 0x0C |    AXI_MASK3   |        AXI mask3        |
| 0x10 |    AXI_MASK4   |        AXI mask4        |
| 0x20 |  AXIS_PKT_MASK |     AXIS packet mask    |
| 0x24 |   AXIS_MASK1   |        AXIS mask1       |
| 0x28 |   AXIS_MASK2   |        AXIS mask2       |
| 0x2C |   AXIS_MASK3   |        AXIS mask3       |
| 0x40 |  CORE_PKT_MASK |     CORE packet mask    |
| 0x44 |   CORE_MASK1   |        CORE mask1       |
| 0x48 |   CORE_MASK2   |        CORE mask2       |
| 0x4C |   CORE_MASK3   |        CORE mask3       |
| 0x60 |    OBS_CTRL    |     Observer control    |
| 0x64 |  OBS_BASE_ADDR |   Observer window base  |
| 0x68 | OBS_LIMIT_ADDR |  Observer window limit  |
| 0x70 |  OBS_STAT_SEL  |     Telemetry select    |
| 0x74 |  OBS_STAT_DATA |      Telemetry data     |
| 0x78 |  OBS_FIFO_STAT |    Monbus FIFO status   |
| 0x7C |   OBS_STICKY   |  Observer sticky status |
| 0x80 | OBS_COMP_STAT0 |     Compressor stats    |
| 0x84 | OBS_COMP_STAT1 |    Compressor stats 2   |
| 0x90 |    MON_CTRL    |   Monitor tap control   |
| 0x94 |   MON_TIMEOUT  |     Monitor timeout     |
| 0x98 |   MON_LATENCY  |Monitor latency threshold|
| 0x9C |   MON_WINDOW   |   Monitor perf window   |
| 0xA0 | ADDR_RANGE_CTRL|   Address range enable  |
| 0xA4 | ADDR_RANGE0_LOW|       Range 0 low       |
| 0xA8 |ADDR_RANGE0_HIGH|       Range 0 high      |
| 0xAC | ADDR_RANGE1_LOW|       Range 1 low       |
| 0xB0 |ADDR_RANGE1_HIGH|       Range 1 high      |
| 0xB4 | ADDR_RANGE2_LOW|       Range 2 low       |
| 0xB8 |ADDR_RANGE2_HIGH|       Range 2 high      |
| 0xBC | ADDR_RANGE3_LOW|       Range 3 low       |
| 0xC0 |ADDR_RANGE3_HIGH|       Range 3 high      |
| 0xD0 |    OBS_CAPS0   |      Capabilities 0     |
| 0xD4 |    OBS_CAPS1   |      Capabilities 1     |
| 0xD8 |    OBS_CAPS2   |      Capabilities 2     |

### AXI_PKT_MASK register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>bit[type]=1 drops that packet type; ERR_SELECT routes err-FIFO vs bulk</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PKT_MASK |  rw  | 0x0 |  — |
|31:16|ERR_SELECT|  rw  | 0x0 |  — |

### AXI_MASK1 register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>Per-event-code drop masks, indexed by event_code[3:0]</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| ERROR_MASK |  rw  | 0x0 |  — |
|31:16|TIMEOUT_MASK|  rw  | 0x0 |  — |

### AXI_MASK2 register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0| COMPL_MASK|  rw  | 0x0 |  — |
|31:16|THRESH_MASK|  rw  | 0x0 |  — |

### AXI_MASK3 register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PERF_MASK|  rw  | 0x0 |  — |
|31:16| ADDR_MASK|  rw  | 0x0 |  — |

### AXI_MASK4 register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|DEBUG_MASK|  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

### AXIS_PKT_MASK register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>bit[type]=1 drops that packet type</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PKT_MASK |  rw  | 0x0 |  — |
|31:16|ERR_SELECT|  rw  | 0x0 |  — |

### AXIS_MASK1 register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| ERROR_MASK |  rw  | 0x0 |  — |
|31:16|TIMEOUT_MASK|  rw  | 0x0 |  — |

### AXIS_MASK2 register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| COMPL_MASK |  rw  | 0x0 |  — |
|31:16|CHANNEL_MASK|  rw  | 0x0 |  — |

### AXIS_MASK3 register

- Absolute Address: 0x2C
- Base Offset: 0x2C
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0|CREDIT_MASK|  rw  | 0x0 |  — |
|31:16|STREAM_MASK|  rw  | 0x0 |  — |

### CORE_PKT_MASK register

- Absolute Address: 0x40
- Base Offset: 0x40
- Size: 0x4

<p>bit[type]=1 drops that packet type</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PKT_MASK |  rw  | 0x0 |  — |
|31:16|ERR_SELECT|  rw  | 0x0 |  — |

### CORE_MASK1 register

- Absolute Address: 0x44
- Base Offset: 0x44
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| ERROR_MASK |  rw  | 0x0 |  — |
|31:16|TIMEOUT_MASK|  rw  | 0x0 |  — |

### CORE_MASK2 register

- Absolute Address: 0x48
- Base Offset: 0x48
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0| COMPL_MASK|  rw  | 0x0 |  — |
|31:16|THRESH_MASK|  rw  | 0x0 |  — |

### CORE_MASK3 register

- Absolute Address: 0x4C
- Base Offset: 0x4C
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PERF_MASK|  rw  | 0x0 |  — |
|31:16|DEBUG_MASK|  rw  | 0x0 |  — |

### OBS_CTRL register

- Absolute Address: 0x60
- Base Offset: 0x60
- Size: 0x4

<p>Monbus group drain + compression</p>

| Bits|   Identifier  |Access|Reset|Name|
|-----|---------------|------|-----|----|
| 15:0|FLUSH_WATERMARK|  rw  | 0x10|  — |
|  16 |  COMPRESS_EN  |  rw  | 0x0 |  — |
|20:17|    FREQ_SEL   |  rw  | 0x0 |  — |
|  21 |  FREQ_SEL_OVR |  rw  | 0x0 |  — |
|31:22|      RSVD     |   r  | 0x0 |  — |

#### FLUSH_WATERMARK field

<p>Bulk-write flush watermark</p>

#### COMPRESS_EN field

<p>1 = compress the monbus write stream. The tally reassembles RAW 3-beat records, so leave 0 unless the consumer decompresses.</p>

#### FREQ_SEL field

<p>counter_freq_invariant LUT index, used only when FREQ_SEL_OVR=1. The LUT is 60+5*i MHz, so 4=80, 6=90, 8=100, 12=120.</p>

#### FREQ_SEL_OVR field

<p>0 = use the build-time index derived from ACLK_MHZ (correct at reset for any build frequency); 1 = use FREQ_SEL instead. Exists so the reset value cannot silently disagree with the actual clock.</p>

### OBS_BASE_ADDR register

- Absolute Address: 0x64
- Base Offset: 0x64
- Size: 0x4

<p>Monbus bulk-write window low bound</p>

|Bits|Identifier|Access| Reset |Name|
|----|----------|------|-------|----|
|31:0|   VALUE  |  rw  |0x40000|  — |

### OBS_LIMIT_ADDR register

- Absolute Address: 0x68
- Base Offset: 0x68
- Size: 0x4

<p>Monbus bulk-write window high bound</p>

|Bits|Identifier|Access| Reset |Name|
|----|----------|------|-------|----|
|31:0|   VALUE  |  rw  |0x7FFFF|  — |

### OBS_STAT_SEL register

- Absolute Address: 0x70
- Base Offset: 0x70
- Size: 0x4

<p>Addresses one telemetry counter for OBS_STAT_DATA</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 7:0 |    TAP    |  rw  | 0x0 |  — |
| 15:8|  CHANNEL  |  rw  | 0x0 |  — |
|23:16|   METRIC  |  rw  | 0x0 |  — |
|  24 |  IS_WRITE |  rw  | 0x0 |  — |
|30:25|    BIN    |  rw  | 0x0 |  — |
|  31 |HIST_METRIC|  rw  | 0x0 |  — |

#### TAP field

<p>Tap index (0..NUM_RD_PORTS-1 for read metrics, 0..NUM_WR_PORTS-1 for write)</p>

#### CHANNEL field

<p>Channel index within the tap; ignored for aggregate metrics</p>

#### METRIC field

<p>Metric id. AGGREGATE (per tap): 0=productive, 1=backpressure, 2=starvation, 3=idle. PER CHANNEL (uses CHANNEL): 4=productive, 5=backpressure, 6=starvation, 7=idle, 8=overflow. HISTOGRAM: 9=bin (NOT YET READABLE - the bin is chosen by the i_hist_bin input port, so BIN here is accepted and ignored and this reads 0), 10=total. Any other value reads 0.</p>

#### IS_WRITE field

<p>0 = read-side metric, 1 = write-side</p>

#### BIN field

<p>Histogram bin index, used when METRIC=9</p>

#### HIST_METRIC field

<p>Which latency metric the histogram reports (e.g. AR-&gt;firstR vs AR-&gt;RLAST). SEPARATE from IS_WRITE, which selects the read- or write-side array -- conflating them makes half the histogram unreachable.</p>

### OBS_STAT_DATA register

- Absolute Address: 0x74
- Base Offset: 0x74
- Size: 0x4

<p>The counter addressed by OBS_STAT_SEL. Reads as 0 for a metric this instance does not build (meters/histograms are parameter-gated).</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### OBS_FIFO_STAT register

- Absolute Address: 0x78
- Base Offset: 0x78
- Size: 0x4

<p>Group err/write FIFO occupancy and full flags</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0| ERR_COUNT |   r  | 0x0 |  — |
|30:16|WRITE_COUNT|   r  | 0x0 |  — |
|  31 |  ANY_FULL |   r  | 0x0 |  — |

#### ANY_FULL field

<p>Either FIFO full</p>

### OBS_STICKY register

- Absolute Address: 0x7C
- Base Offset: 0x7C
- Size: 0x4

<p>Sticky flags. A dropped sample or a blocked tap means the numbers above are INCOMPLETE, so it has to be readable alongside them.</p>

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|  0 |HIST_SAMPLE_LOST|   r  | 0x0 |  — |
|  1 |   TAP_BLOCKED  |   r  | 0x0 |  — |
|31:2|      RSVD      |   r  | 0x0 |  — |

#### HIST_SAMPLE_LOST field

<p>A latency-histogram timestamp was dropped</p>

#### TAP_BLOCKED field

<p>Any tap asserted block_ready (its table filled, so it stopped tracking)</p>

### OBS_COMP_STAT0 register

- Absolute Address: 0x80
- Base Offset: 0x80
- Size: 0x4

<p>monbus_compressor tier hits and CAM misses</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   TIER1  |   r  | 0x0 |  — |
|31:16|   TIER0  |   r  | 0x0 |  — |

### OBS_COMP_STAT1 register

- Absolute Address: 0x84
- Base Offset: 0x84
- Size: 0x4

<p>CAM miss and overflow counters</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| CAM_MISS |   r  | 0x0 |  — |
|31:16| OVERFLOW |   r  | 0x0 |  — |

### MON_CTRL register

- Absolute Address: 0x90
- Base Offset: 0x90
- Size: 0x4

<p>Per-cone runtime enables for the rd/wr monitors. Gated by the build-time cones in OBS_CAPS0.</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|  0 |   ERROR_EN  |  rw  | 0x1 |  — |
|  1 |  TIMEOUT_EN |  rw  | 0x1 |  — |
|  2 |   COMPL_EN  |  rw  | 0x1 |  — |
|  3 | THRESHOLD_EN|  rw  | 0x0 |  — |
|  4 |   PERF_EN   |  rw  | 0x0 |  — |
|  5 |   DEBUG_EN  |  rw  | 0x0 |  — |
|  6 |ADDR_CHECK_EN|  rw  | 0x0 |  — |
|  7 |  MONITOR_EN |  rw  | 0x1 |  — |
|31:8|     RSVD    |   r  | 0x0 |  — |

#### ERROR_EN field

<p>Emit ERROR packets</p>

#### TIMEOUT_EN field

<p>Emit TIMEOUT packets</p>

#### COMPL_EN field

<p>Emit COMPLETION packets</p>

#### THRESHOLD_EN field

<p>Emit THRESHOLD packets</p>

#### PERF_EN field

<p>Emit PERF packets</p>

#### DEBUG_EN field

<p>Emit DEBUG packets</p>

#### ADDR_CHECK_EN field

<p>Enable the address-range checker. Inert unless OBS_CAPS0.N_ADDR_RANGES &gt; 0.</p>

#### MONITOR_EN field

<p>Runtime gate on the per-transaction CAM, ANDed with the build-time
ENABLE_MON_TAPS (OBS_CAPS0.MON_TAPS_ARMED). Clear it to stop the tap
back-pressuring the datapath: an armed tap gates ready as
(block_ready | ~cfg_monitor_enable), so at MAX_TRANSACTIONS the instrument
becomes the bottleneck and reports its own limit as the engine's throughput.</p>

### MON_TIMEOUT register

- Absolute Address: 0x94
- Base Offset: 0x94
- Size: 0x4

<p>Transaction timeout threshold in MICROSECONDS (0 = 0xFFFF, i.e. effectively never)</p>

| Bits|  Identifier  |Access|Reset|Name|
|-----|--------------|------|-----|----|
| 15:0|TIMEOUT_CYCLES|  rw  |0x400|  — |
|31:16|     RSVD     |   r  | 0x0 |  — |

### MON_LATENCY register

- Absolute Address: 0x98
- Base Offset: 0x98
- Size: 0x4

<p>Latency above which a THRESHOLD packet is raised</p>

|Bits|Identifier|Access| Reset|Name|
|----|----------|------|------|----|
|31:0|   VALUE  |  rw  |0xFFFF|  — |

### MON_WINDOW register

- Absolute Address: 0x9C
- Base Offset: 0x9C
- Size: 0x4

<p>Event-driven performance window: pick the start/end events, or drive the triggers by hand</p>

| Bits|   Identifier  |Access|Reset|Name|
|-----|---------------|------|-----|----|
| 2:0 |START_EVENT_SEL|  rw  | 0x0 |  — |
| 6:4 | END_EVENT_SEL |  rw  | 0x0 |  — |
|  8  | START_TRIGGER |  rw  | 0x0 |  — |
|  9  |  END_TRIGGER  |  rw  | 0x0 |  — |
|  10 |  FORCE_CLOSE  |  rw  | 0x0 |  — |
|31:11|      RSVD     |   r  | 0x0 |  — |

#### START_TRIGGER field

<p>Manual window open</p>

#### END_TRIGGER field

<p>Manual window close</p>

#### FORCE_CLOSE field

<p>Force the window shut regardless of the end event</p>

### ADDR_RANGE_CTRL register

- Absolute Address: 0xA0
- Base Offset: 0xA0
- Size: 0x4

<p>bit<i> = 1 arms range i</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 3:0| RANGE_EN |  rw  | 0x0 |  — |
|31:4|   RSVD   |   r  | 0x0 |  — |

### ADDR_RANGE0_LOW register

- Absolute Address: 0xA4
- Base Offset: 0xA4
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### ADDR_RANGE0_HIGH register

- Absolute Address: 0xA8
- Base Offset: 0xA8
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### ADDR_RANGE1_LOW register

- Absolute Address: 0xAC
- Base Offset: 0xAC
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### ADDR_RANGE1_HIGH register

- Absolute Address: 0xB0
- Base Offset: 0xB0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### ADDR_RANGE2_LOW register

- Absolute Address: 0xB4
- Base Offset: 0xB4
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### ADDR_RANGE2_HIGH register

- Absolute Address: 0xB8
- Base Offset: 0xB8
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### ADDR_RANGE3_LOW register

- Absolute Address: 0xBC
- Base Offset: 0xBC
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### ADDR_RANGE3_HIGH register

- Absolute Address: 0xC0
- Base Offset: 0xC0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### OBS_CAPS0 register

- Absolute Address: 0xD0
- Base Offset: 0xD0
- Size: 0x4

<p>Build-time feature bits, packed. Wide single fields on purpose: see the CAPS PACKING note above.
[0] ERROR_CONE  [1] TIMEOUT_CONE [2] COMPL_CONE  [3] THRESHOLD_CONE
[4] PERF_CONE   [5] DEBUG_CONE   [6] MON_TAPS_ARMED [7] BUS_METER
[8] COMPRESSION [9] EGRESS_AXIL  [10] ID_SLICE   [15:12] N_ADDR_RANGES</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### OBS_CAPS1 register

- Absolute Address: 0xD4
- Base Offset: 0xD4
- Size: 0x4

<p>Tap geometry, packed.
[7:0] NUM_RD_PORTS [15:8] NUM_WR_PORTS [23:16] NUM_CHANNELS (per tap) [31:24] CH_BASE</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### OBS_CAPS2 register

- Absolute Address: 0xD8
- Base Offset: 0xD8
- Size: 0x4

<p>Transaction-table sizing, packed.
[15:0] MAX_TRANSACTIONS [23:16] NUM_BANKS [31:24] ADDR_WIDTH</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |
