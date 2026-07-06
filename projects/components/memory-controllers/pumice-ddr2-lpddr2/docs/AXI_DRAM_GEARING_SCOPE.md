# Scope: Generic AXI ↔ DRAM-beat width gearing

**Status:** scoping (not yet implemented)
**Motivation:** the controller currently hard-assumes `AXI_DATA_WIDTH == DRAM_BEAT_WIDTH`
(`axi_intake.sv` has zero references to `DRAM_BEAT_WIDTH`; its write buffer and
`wbuf_ext_rd_data_o` are `[AXI_DATA_WIDTH-1:0]`). Driving the Nexys A7 x16 DDR2
via the LiteDRAM a7ddrphy forces `DRAM_BEAT_WIDTH=32` (2×16) and `DFI_RATE=4`
(the PHY's phase count), which — under the current coupling — would force
`AXI_DATA_WIDTH=32`. Goal: make **AXI width a free parameter** (32/64/128/256/512),
decoupled from the DRAM beat width, "within reason."

---

## 1. Gearing definition

```
GEAR = AXI_DATA_WIDTH / DRAM_BEAT_WIDTH        (down-gear: AXI wider than beat)
```

Constraints (checked with an elaboration assertion):
- `AXI_DATA_WIDTH >= DRAM_BEAT_WIDTH`
- `AXI_DATA_WIDTH % DRAM_BEAT_WIDTH == 0`, and GEAR a power of two
- Recommended `AXI_DATA_WIDTH <= 128` for area-sensitive builds (see §5)

Today's design is exactly `GEAR == 1`. Nexys A7 (beat=32): AXI 32→G1, 64→G2,
128→G4, 256→G8, 512→G16.

`DRAM_BEAT_WIDTH` itself stays = DFI per-phase = 2 × physical DQ width, and
`DFI_DATA_WIDTH = DRAM_BEAT_WIDTH * DFI_RATE`. Gearing does **not** touch the
DFI rate — `DFI_RATE` continues to equal the PHY phase count (4 for a7ddrphy).

### Why generic (not a one-off for this board)

This scaling is primarily for **future DDR* IP**, not just the Nexys A7 bring-up.
Different devices/PHYs pin different `(DRAM_BEAT_WIDTH, DFI_RATE)` points —
DDR2 x16 (beat 32, 4:1), DDR3/DDR4 x8/x16 at higher gears, wide DIMMs, etc. —
while host SoCs want a *fixed, convenient* AXI width (often 64/128/256/512)
independent of whichever DRAM part is attached. Building the AXI↔beat gearbox
into the controller once makes `AXI_DATA_WIDTH` a first-class free parameter for
the whole DDR* family; the a7ddrphy x16 bring-up is simply the **first consumer**
(and the forcing function that surfaced the current `AXI==beat` coupling).

---

## 2. Where the gearing lives — localized to `axi_intake.sv`

Everything below the AXI↔beat seam is **already** parameterized on
`DRAM_BEAT_WIDTH` and validated at beat=32/rate=4: `data_path`,
`wr_beat_sequencer`, `rd_cl_aligner`, `dfi_signal_pack`. The gearbox is
therefore confined to the write-buffer / read-return seam in `axi_intake`
(plus width-decoupling of the wrapper ports). Recommended approach:
**internal gearbox** (makes the controller itself generic).

### Write path (split, on ingest)
- `r_w_buf` / `r_wstrb_buf` change from `[AXI_DATA_WIDTH]` entries to
  `[DRAM_BEAT_WIDTH]` entries (depth `W_BUF_DEPTH * GEAR`; pointer widens by
  `log2(GEAR)`).
- Each accepted AXI W beat is split LSB→MSB into `GEAR` consecutive DRAM-beat
  entries; `wstrb` split into `GEAR × DRAM_STRB_WIDTH` chunks. Write pointer
  advances by `GEAR` per AXI beat.
- Burst-length accounting: `aw_push_len_o` (already in DRAM beats) becomes
  `(awlen+1) * GEAR`. **Composes with** the existing `dram_bl_i` burst-length
  split (also DRAM-beat granularity) — both now speak DRAM beats, so order the
  ×GEAR expansion *before* the dram_bl chunking.
- `wbuf_ext_rd_data_o` becomes `[DRAM_BEAT_WIDTH-1:0]` — this *fixes* today's
  implicit width-equal assumption at the data_path boundary.

### Read path (assemble, on return)
- Actual DRAM reads: `rd_cl_aligner` already emits DRAM-beat-wide `rd_inject`;
  add a `GEAR`-deep assembler that packs `GEAR` DRAM beats → one AXI R beat
  (LSB→MSB), driving `s_axi_rdata[AXI_DATA_WIDTH-1:0]`.
- Forwarded (write-to-read) reads: `fub_axi_rdata` assembles `GEAR` beat-entries
  from `r_w_buf` per AXI beat (mirror of the write split).
- Partial final AXI beat when a DRAM burst isn't a multiple of GEAR: handle via
  `wstrb`/read-lane masking on the last beat.

### Wrapper width decoupling
- `axi_frontend_macro`, `pumice_core_macro`, `pumice_top`: pass an
  explicit `DRAM_BEAT_WIDTH` to `axi_intake`; keep `s_axi_*` at
  `AXI_DATA_WIDTH`; retype `wbuf_ext_rd_data`/`rd_inject_data` nets to
  `DRAM_BEAT_WIDTH`. `DRAM_BEAT_WIDTH` default stays `= AXI_DATA_WIDTH` so
  existing GEAR-1 builds are bit-identical.

---

## 3. Alternative: external AXI dwidth converter (fallback)

Keep the controller internally `AXI==beat` and place the repo's already
**formally-verified** `axi4_dwidth_converter_wr` / `axi4_dwidth_converter_rd`
(`formal/converters/`) in front: host width → beat width. Pros: zero controller
change, reuses proven+formal IP. Cons: the controller is then characterized at
its internal (narrow) width with the converter as a separate DUT; adds AXI
latency and a full AR/AW/W/B/R component. Use this if the internal-gearbox
schedule is too costly, or as an independent cross-check.

---

## 4. DV changes

- `axi_intake` FUB TB: model the split/assemble; add a GEAR dimension
  (AXI ∈ {32,64,128} at beat=32 → GEAR {1,2,4}).
- `core_macro` / `top` TBs: **decouple** `bytes_per_beat`. Today both do
  `bytes_per_beat = axi_data_width // 8` and use it for the DFI MemoryModel —
  wrong when beat≠AXI. Split into `axi_bytes = AXI_DATA_WIDTH//8` (AXI side) and
  `dram_beat_bytes = DRAM_BEAT_WIDTH//8` (DFI side). `DFISlavePHY` already infers
  DFI_RATE from bus width, so it needs only the correct beat size.
- Add GEAR to the FULL matrix; keep GEAR-1 rows for regression parity. Already
  green at beat=32/rate=4: `wr_beat_sequencer`, `rd_cl_aligner`,
  `dfi_signal_pack`, `data_path_macro` (via `DRAM_BEAT_WIDTH_OVERRIDE`).

---

## 5. Resource note (for the HAS/MAS docs)

Area scales with **AXI width**, not beat width. At GEAR=16 (AXI=512, beat=32):
the AXI-side staging registers + `wstrb` (512b/64B), the 16:1 split and 16:1
assemble muxes, and the wider write-buffer pointer all grow. The *stored* bits
are unchanged (same bytes, narrower/deeper entries), but the AXI-side datapath
dominates LUT/FF. **Doc guidance:** 512b is supported and functional, but wastes
resources vs the DRAM bandwidth it can actually sink through a single x16 DFI;
recommend AXI ≤ 128 unless a wide host bus is a hard requirement.

---

## 6. Effort / phasing / risk

| Phase | Work | Rough size |
|-------|------|-----------|
| 1 | `axi_intake` internal gearbox (write split, read assemble, ×GEAR burst-len, decoupled port widths) | 1 FUB, moderate |
| 2 | Propagate explicit `DRAM_BEAT_WIDTH` through frontend/core/top; retype nets | mechanical |
| 3 | DV: decouple TB beat/AXI, add GEAR sweep, re-validate FUB/macro/top at GEAR {1,2,4} | moderate |
| 4 | Char harness consumes it (AXI = user choice, beat=32, rate=4) | small |

**Risks:** (a) ×GEAR vs `dram_bl_i` burst-length split ordering; (b) read
reassembly ordering + partial final AXI beat; (c) narrow/unaligned AXI bursts
(`AxSIZE < full width`) → per-DRAM-beat `wstrb`; (d) `W_BUF_DEPTH` now counts
DRAM beats (document the semantic change).

**On-board target config (a7ddrphy):** AXI = user choice (e.g. 64), beat=32,
DFI_RATE=4, GEAR=2.
