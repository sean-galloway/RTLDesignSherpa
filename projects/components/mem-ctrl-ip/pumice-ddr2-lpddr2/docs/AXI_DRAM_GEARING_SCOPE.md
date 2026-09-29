# Scope: Generic AXI ↔ DRAM-beat width gearing

**Status:** IMPLEMENTED via the external-converter path (`pumice_top_geared`).
See "Implemented" at the bottom. This is family-wide (DDR2/3/4/LPDDR2), not
device-specific. The sections below are retained as the original scoping analysis;
NOTE they predate the controller rearchitecture (they target the retired
`axi_intake.sv`) — read them as design context, not the current code map.

**Premise correction (post-rearchitecture):** the old design coupled
`AXI_DATA_WIDTH == DRAM_BEAT_WIDTH`, so a7ddrphy (beat=32) would have forced
AXI=32. The rearchitected controller instead couples `AXI = DRAM_BEAT_WIDTH ×
DFI_RATE = DW` (one AXI beat == one DFI word == DFI_RATE DRAM beats), so the board
case (beat=32, rate=4) already yields a fine AXI=128 — the original forcing
function is already solved by the rate factor. The remaining, genuinely
family-wide need is decoupling `AXI_DATA_WIDTH` from `DW` so a host SoC can pick a
convenient fixed width (32/64/128/256/512) regardless of the attached DRAM's
`(DRAM_BEAT_WIDTH, DFI_RATE)` point.

**Motivation (original):** make **AXI width a free parameter**, decoupled from the
DRAM beat width, "within reason."

---

## 1. Gearing definition

The controller core is fixed **1:1 at the DFI word**: `DW = DFI_DATA_WIDTH =
DRAM_BEAT_WIDTH × DFI_RATE`, and one core AXI beat == one DFI word. The ONLY
place a host may use a different width is `pumice_top_geared`, which inserts the
repo's formally-verified AXI dwidth converters between the host and the core.

### *** HARD, COMPILE-ENFORCED WIDTH RULE ***

```
HOST_AXI_DATA_WIDTH : DW   MUST be an EXACT POWER-OF-TWO ratio
                          (AXI:DFI = G:1 or 1:G, G ∈ {1,2,4,8,...})
where DW (the DFI word) = DRAM_BEAT_WIDTH × DFI_RATE
```

This is checked by an **elaboration assertion in `pumice_top_geared`** (`initial
assert … $fatal`) that **fails Vivado synthesis / verilator elaboration** — a
bad width pairing is a **compile error**, never a silent broken hybrid. Set the
two DWs together with this rule in mind; nothing else about the datapath is a
width parameter.

**Why the DFI word, and why power-of-two (this is exactly what LiteDRAM does):**
the DFI word is the atomic memory-side transfer, so one AXI beat must be a
*whole* power-of-two number of DFI words (or vice versa). Any other ratio yields
partial words, fractional `CHUNK_BEATS`, and ragged bursts. LiteDRAM enforces
the identical rule: its AXI frontend is 1:1 with its native port
(upstream `litedram/frontend/axi.py`: `assert axi.data_width == port.data_width`) and **all** width
change goes through a dedicated stride converter requiring exact divisibility +
`log2_int(ratio)` (upstream `litedram/frontend/adapter.py`: `LiteDRAMNativePortUp/DownConverter`).

Nexys A7 (beat=32, DFI_RATE=4 → DW=128): host 128→G1 (1:1, converter bypassed),
256→2:1, 512→4:1; a narrower host (64) attaches 1:2 through the converter.

`DRAM_BEAT_WIDTH` = DFI per-phase = 2 × physical DQ width. Gearing does **not**
touch the DFI rate — `DFI_RATE` (the gear) continues to equal the PHY phase
count (4 for a7ddrphy) and is a build-for-max value the runtime `gear_ratio` CSR
selects within; likewise burst length is the runtime `bl` CSR. Only
`HOST_AXI_DATA_WIDTH` and `DW` are compile-time width parameters.

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

---

## Implemented — external formal converter (`pumice_top_geared`)

Chosen approach: §3 (external converter), not the internal gearbox. Rationale:
the controller datapath was freshly stabilized (bank_timer, CAM de-FSM, LPDDR2),
and the repo already has FORMALLY-VERIFIED `axi4_dwidth_converter_wr/_rd`
(`formal/converters/`). Reusing proven+formal IP beats re-verifying a bespoke
gearbox inside the core across GEAR points.

- `rtl/top/pumice_top_geared.sv` — wraps `pumice_top` with a free
  `HOST_AXI_DATA_WIDTH`. Instantiates the wr/rd converters between a host-width
  AXI slave and the DW-width core. `HOST == DW` (GEAR-1) is a `generate` bypass:
  host connects straight to the core, so existing GEAR-1 builds are
  bit-identical (no converter, no added latency).
- Core stays fixed at `DW = DRAM_BEAT_WIDTH × DFI_RATE`; the CAMs / scheduler /
  DFI are untouched. Burst geometry contract at the core side is unchanged
  (`(awlen+1)*DFI_RATE == BL`); the host issues bursts at its width and the
  converter translates them.
- DV: `dv/tb/pumice_top_geared_tb_top.sv` + `dv/tests/top/test_pumice_top_geared.py`
  round-trip a write burst driven at host width back through host-width reads —
  host ∈ {64 (down-gear 2:1), 128 (GEAR-1 bypass), 256 (up-gear 1:2)}, all
  mapping to one DW=128 DRAM burst. `PumiceTopCsrTB` gained a `host_axi_data_width`
  arg (defaults to DW; BFM width only, DFI/golden side stays DW).

**Not chosen (deferred):** the internal gearbox (§2) — would make the core itself
generic but requires width+burst surgery on the intakes re-verified across GEAR
points. Revisit only if the front-end converter's latency/area is unacceptable
for a specific target.
