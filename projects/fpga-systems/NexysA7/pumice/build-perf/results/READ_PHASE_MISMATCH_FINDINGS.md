# DDR2 Board Read Failure — Read De-interleave Regression in the Rearchitected Core

> **CORRECTION (2026-07-14, supersedes the "phase-count mismatch" conclusion below).**
> The `DFI_RATE=2` / 4-phase-PHY setup is **proven-good, not the bug**. Git shows the
> harness (`ddr2_char_top.sv`, the `dfi_v21_flat_to_a7ddrphy` adapter, and the a7ddrphy)
> is **byte-identical to commit `22cd45c8`**, where the board read **clean (0/3072)** at
> `DFI_RATE=2` reading `{p1,p0}`. The **only** change since is the full pumice-core
> rearchitecture. So the `{p1,p0}` 2-of-4-phase read is fine *when the core de-interleaves
> it correctly* — the OLD core did, the rearchitected `rd_intake`/`rd_cmd_cam`/reassembly
> does not. **Do NOT change `DFI_RATE`.** The real fix is restoring the x16 device-word BL4
> read de-interleave in the rearchitected read path (regression of tasks #124/#127, likely
> broken by the FSM-free splitter/aggregator rework #129). The ILA device-word corruption
> below is real and correct; only its *attribution* to the phase count was wrong.

**Date:** 2026-07-14
**Board:** Nexys A7 (xc7a100t), Micron MT47H64M16 x16 DDR2
**Flow:** `flows-ours-uart` (pumice controller + generated a7ddrphy)
**Status:** Root cause confirmed by on-silicon ILA + side-by-side comparison with the proven-good LiteDRAM flow.

---

## 1. Symptom

On the Nexys A7, the pumice DDR2 controller **programs, inits, and writes correctly**, but **reads are corrupt** and A7 read-leveling finds *no passing tap at any bitslip*.

Empirical signature (measured, `/tmp/explore_limits.py`, forcing `apply_taps(bitslip,tap)` then write→read):

```
beats_mismatched == 2 * txn_count   (EXACTLY)
    txn=1 -> 2   txn=2 -> 4   txn=3 -> 6   txn=4 -> 8   txn=8 -> 16
```

- **Identical** for page-hit-packed reads (stride = burst*8, same row) and bank-spread reads (stride = 64 KiB, ACT-separated).
- A single isolated BL4 read loses **2 of its 4 device-words**; at the best bitslip (1) it is 2/4 wrong, at every other bitslip 4/4 wrong — at **every one of the 32 IDELAY taps**.

### What this rules out

| Observation | Conclusion |
|---|---|
| `mism` constant across all 32 IDELAY taps | **Not analog** (DQ/DQS eye / leveling is a red herring) |
| Packed == bank-spread | **Not `tCCD`/read pacing**, not the DFI read aligner |
| Fixed 2-per-read, independent of stream length | **Per-read digital reassembly**, not a stream/CDC effect |
| Writes clean, reads corrupt on the *same* DQ lanes | **Read de-interleave specifically**, not the DQ wiring or writes |

---

## 2. ILA evidence (DFI boundary, fixed-RTL ILA bitstream)

Decoding each 64-bit DFI word as `ph1[63:32] | ph0[31:0]`, each 32-bit phase = two x16 device-words `[31:16] | [15:0]`:

**Write path — `w_dfi_wrdata` (`reports/ila_wr_fixed.csv`): perfect.**
Every word is `a5a03fXX | a5a03fYY`, correctly structured. **Writes are not the problem.**

**Read path — raw `w_dfi_rddata` from the a7ddrphy (`reports/ila_read_fixed.csv`): correct words interleaved with two corruption signatures:**

| Captured beat | Meaning |
|---|---|
| `0x000000000000a5a0` | a beat holding only **one shifted x16 device-word** (`a5a0`) + zeros |
| `0xa5a03f1ca5a03f1c` | **both phases equal** `3f1c`, where the write had `3f18 \| 3f1c` → **phase1 replaced by phase0** |

The corruption is a **device-word (16-bit) ordering/shift within the four device-words of each BL4 read**, alternating beat to beat — exactly consistent with the `2/4` floor and the tap/pacing independence above.

---

## 3. Root cause — nphases=4 PHY driven as nphases=2

The generated a7ddrphy is a **4-phase (nphases=4, 4:1)** PHY. From `flows-ours-uart/bin/README_a7ddrphy.md`:

> **DFI, 4-phase** (`dfi_p0..p3`): DDR2 is 4:1 on Artix-7 (nphases=4, DDR_clk = 4*sys). 32-bit wrdata/phase (`dfi_databits = 2*16` for the x16 part).
> **Drive from our controller at `DFI_RATE=4` via the (4-phase) adapter.**

But the harness drives it at **`DFI_RATE=2`**:

- `rtl/ddr2_char_top.sv`: `localparam int DFI_RATE = 2;`
- `dfi_v21_flat_to_a7ddrphy` instantiated with `.CTRL_PHASES(DFI_RATE)` = 2 → **NOPs phases p2/p3** and, on read return (generate branch `g_rd2`), packs only:

  ```systemverilog
  assign dfi_rddata_flat       = {dfi_p1_rddata, dfi_p0_rddata};        // 2 of 4 phases
  assign dfi_rddata_valid_flat = {dfi_p1_rddata_valid, dfi_p0_rddata_valid};
  ```

### Why this breaks reads but not writes

The a7ddrphy ISERDES de-interleave spreads the read burst across **8 bitslip taps → 4 phases × 2 device-words = 8 device-words (BL8/4-phase)**:

```
OURS  a7ddrphy: dfi_p0_rddata[0]  <= a7ddrphy_bitslip04[0];   // p0 = taps 0,1
LiteDRAM      : main_..._dfi_p2_rddata[0] <= main_..._bitslip04[4];  // p2 = taps 4,5
                => phases p0,p1,p2,p3 use bitslip taps [0,1],[2,3],[4,5],[6,7]
```

- **Writes**: the controller drives `p0,p1` wrdata (p2,p3 NOP). The PHY serializes `p0,p1` → 4 device-words in order → a correct BL4 write. The 2-phase drive maps cleanly onto the first four SERDES slots.
- **Reads**: the PHY captures the return in an **8-slot (BL8/4-phase) window** timed by CL / `rddata_en`. The four real BL4 device-words do **not** land cleanly in `{p0,p1}` — they straddle the 4-phase de-interleave, so reading only `{p1,p0}` picks up a mix of real and stale/other device-words. That is the alternating 16-bit shift and phase-duplication seen on the ILA. No single `bitslip` (a uniform rotate) can fix an *alternating* misorder → the 2/4 floor.

This is the **"broken hybrid"** documented earlier: *DFI_RATE must equal the PHY phase count* — an nphases=4 PHY driven by an nphases=2 controller produces a flat 16-bit (device-word) mismatch on the read de-interleave.

---

## 4. Comparison table — OURS vs LiteDRAM (proven-good on this exact board)

| Aspect | `flows-ours-uart` (fails reads) | `flows-litedram-uart` (memtest PASSES) |
|---|---|---|
| a7ddrphy phase count | nphases=4 (`dfi_p0..p3`, 32b/phase) | nphases=4 (`dfi_p0..p3`, 32b/phase) — same generator |
| Controller DFI rate | **`DFI_RATE=2`** (`ddr2_char_top.sv`) | **nphases=4** (LiteDRAM core drives all 4 phases) |
| Read phases consumed | **only `{p1,p0}`** (adapter `g_rd2`, p2/p3 NOP) | **all 4** (`p0..p3`, full BL8/4-phase de-interleave) |
| SERDES read slots used | taps 0–3 only (of 8) | taps 0–7 (all 8) |
| Writes | correct (2-phase serialize maps cleanly) | correct |
| Reads | **corrupt** (4→2 phase de-interleave mismatch) | correct |
| README requirement | "drive at `DFI_RATE=4`" — **violated** | matched |

The a7ddrphy RTL is effectively identical (same LiteX generator); the **only material difference is that LiteDRAM matches DFI_RATE to the PHY's nphases (=4) and ours does not.**

---

## 5. Fix options

**Recommended — match the controller to the PHY (`DFI_RATE=4`).**
Run pumice / the harness at **`DFI_RATE=4` (nphases=4)** so the adapter drives and reads all four phases, exactly as the README requires and LiteDRAM proves on this board. The pumice DFI layer is already `DFI_RATE`-parameterized; the changes are in the harness config (`ddr2_char_top.sv` `DFI_RATE`, the DFI bus widths `DFI_ADDR_BUS_W`/`DFI_BANK_BUS_W = *4`, and the matching `t_rddata_en`/CL for the 4-phase timing). This is the "DFI_RATE = PHY phase count" invariant.

**Alternative — regenerate the a7ddrphy for nphases=2.**
Prior attempts at regenerating the PHY for nphases=2 *alone* produced a broken hybrid (flat 16/16 mismatch); it must be a full nphases=2 PHY + matching sys2x_dqs clocking (the proven-good LiteDRAM 1:2 baseline). Higher effort/risk than matching to 4.

**Not recommended — patch the 4→2 read de-interleave in the adapter.**
Hand-mapping the BL8/4-phase capture back into a 2-phase read is fragile and timing-dependent; it fights the invariant instead of restoring it.

---

## 6. What this does *not* change

The **FSM-free rewrite of `pumice_dfi_rd_aligner` and `pumice_dfi_wr_serializer`** (stateless delay-line, removes the `tCCD` contiguous-window edge condition) is a **correct and necessary** improvement — verified by FUB `tccd` tests, core-macro 109/109, and confirmed at the ILA boundary (`rddata_en` is now clean 1-wide at the true cadence). It was masked/entangled with this phase-count bug but is orthogonal to it. Keep it.

## 7. Reproduction / probes

```bash
# board (ILA superset bitstream already carries the DFI-boundary probes)
python3 host/capture_read.py --port /dev/ttyUSB2 --trig wr --out reports/ila_wr_fixed.csv
python3 host/capture_read.py --port /dev/ttyUSB2 --trig rd --out reports/ila_read_fixed.csv
python3 /tmp/explore_limits.py     # prints the beats_mismatched == 2*txn signature
```

Decode: 64b DFI word = `ph1[63:32] | ph0[31:0]`; each 32b phase = 2 x16 device-words.
