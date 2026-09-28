# TASK-005: One name per quantity — BYTES_PER_AXI_BEAT / BYTES_PER_DFI_BEAT / DRAM_BL

> Migrated 2026-09-27 from `vault/Tasks/nexysa7/open.md` as **NEXYS-005** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** Medium
**Status:** [ ] Open (2026-08-30)
**Source:** Sean, 2026-08-30 — "can you decide on ONE name instead of 3-4 for
the same thing"; scheme agreed same day.

**Problem:** five names per quantity, and a mismatch between any two of them
fails SILENTLY. Three separate places held a stale BL4 value for six weeks
after the RTL moved to BL8, and none of them complained.

| concept | today | canonical |
|---|---|---|
| one AXI interface transfer | `AXI_DATA_WIDTH`/8, `bytes_per_beat` | `BYTES_PER_AXI_BEAT` |
| one DFI PHASE's data slice | `DRAM_BEAT_WIDTH`/8, `dfi_phase_bytes` | `BYTES_PER_DFI_BEAT` |
| the DQ width (x16 => 2) | `DRAM_DEVICE_WIDTH`/8, `dram_device_bytes` | `BYTES_PER_DEVICE_WORD` |
| JEDEC MR0 burst length | `DRAM_BL`, `BL`, `dram_bl`, `DFI_PHASE.bl`, `BEATS_PER_BURST` | `DRAM_BL` |
| DFI phases per clock | `DFI_RATE` | `DFI_RATE` |

**Everything else derives, one definition each:**

    AXI_BEATS_PER_BURST = DRAM_BL * BYTES_PER_DEVICE_WORD / BYTES_PER_AXI_BEAT
        replaces CHUNK_BEATS, BURST_WORDS, EXP_AXI_BEATS, BURST_LEN_MULTIPLE
    BL_SHIFT / BL_PUMICE  from BYTES_PER_DFI_BEAT / BYTES_PER_DEVICE_WORD
    BYTE_OFFSET_WIDTH     = clog2(BYTES_PER_DEVICE_WORD)
    gear_ratio (CSR)      = log2(DFI_RATE)   -- ALWAYS derived, never typed

**Two rules that are not cosmetic:**

- **`DRAM_BL` is in DEVICE words, not DFI beats.** BL8 on the x16 part is 8
  DQ transfers = 16 bytes = TWO 8-byte DFI beats. Naming it `DFI_BL` would
  read as "8 DFI beats" and be wrong by the device ratio — which is
  `BL_SHIFT`, and getting it wrong is what produced the on-silicon column
  overlap (writes advancing +2 while a BL4 burst spanned +4).
- **`BYTES_PER_DFI_BEAT` is the PHASE slice**, not the full bus word. The bus
  word is `BYTES_PER_DFI_BEAT * DFI_RATE`. DFISlavePHY's `dfi_phase_bytes`
  already uses the phase convention; match it rather than fight it.
- **`gear_ratio` is never hand-written.** It is log2(DFI_RATE); writing the
  rate there overflows `(RATEW'(1) << gear_i)` to 0, every DFI phase reads
  inactive and writes vanish with B=OKAY. That bug cost a full day.

**Scope:** pumice RTL (`CHUNK_BEATS` spans chopper/splitter/ifc), both TB
classes, the harness tests. Behaviour-neutral: land as its own commit and
lean on the 210 (pumice FULL) + 170 (harness macro) regression to prove
bit-identity. Do NOT fold into a functional change.


---
