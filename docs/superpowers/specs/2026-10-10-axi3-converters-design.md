# AXI3 Converters: `axi4_to_axi3` / `axi3_to_axi4` — Design Spec

**Date:** 2026-10-10
**Status:** Design dialogue 2026-10-10 (DE10 campaign + RDS-DV #87), pending written-spec review
**IP:** `projects/components/utility-ip/converters/` (rtl + co-located dv)
**DV dependency:** RDS-DV AXI3 BFMs (sean-galloway/RTLDesignSherpa-DV#87, landed `84f9066`)

## 1. Goal

Add the two AXI↔AXI3 protocol converters to the converters IP so that any AXI4
fabric (Bridge first) can reach an AXI3 endpoint, and AXI3 masters can drive
AXI4 slaves — with the Cyclone V HPS as the motivating endpoint and the DE10
campaign as first customer.

Deliverables: `axi4_to_axi3.sv` and `axi3_to_axi4.sv` (+ `_rd`/`_wr`
submodules, mirroring the `axi4_to_axil4` structure), filelists, lint,
co-located cocotb DV, docs, vault tracking.

## 2. Why

DE10-Standard (Cyclone V SoC): every HPS FPGA-facing port (`f2h_axi_slave`,
`h2f_axi_master`, ACP) is **AXI3** — frozen hard silicon. On the DE10
fabric-comparison campaign the Intel leg gets AXI4↔AXI3 adaptation from
Platform Designer for free; the Bridge leg (and any future non-PD fabric)
needs its own converters. The Intel hard memory controller is the constant;
these converters are the price of reaching it from our fabric.

## 3. Decisions (locked in design dialogue)

1. **Location.** `projects/components/utility-ip/converters/rtl/`, the
   user-assigned home. No `rtl/amba/axi3/` family in this work — converters
   only (the FUB-family mirror stays deferred until a second customer exists).
2. **Module structure** mirrors `axi4_to_axil4`: a top wrapper plus
   `axi4_to_axi3_rd.sv` / `axi4_to_axi3_wr.sv` (and the `_rd`/`_wr` pair for
   the reverse direction). Parameters: `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`,
   `AXI_DATA_WIDTH`, `AXI_USER_WIDTH` — **no data-width conversion**; that is
   the dwidth converter's job (separation of concerns).
3. **`axi4_to_axi3` (downgrade, f2h-facing):**
   - **Burst chopping:** AXI4 `len` ≤ 15 passes through untouched. `len` > 15
     is chopped into ≤16-beat AXI3 bursts by address regeneration (INCR and
     FIXED only — see non-goal 6.3 for WRAP). All chunks of one AXI4
     transaction share the original ARID/AWID: AXI same-ID ordering makes
     response merge a pass-through.
   - **Read merge:** R beats stream through; `RLAST` asserted only on the
     final beat of the final chunk; the completing beat's `RRESP` is the
     worst response seen across the whole transaction (DECERR > SLVERR >
     OKAY); per-beat `RRESP` otherwise passes through.
   - **Write merge:** one AXI4 AW expects exactly one B. B responses from
     chunks 1..n−1 are absorbed; a single B is returned (after the last
     chunk's B) with `BRESP` = worst across chunks. `WID = AWID` on every W
     beat (legal: AXI4 already orders W per AW, so no interleave is created).
   - **Qualifier mapping:** drop `QoS`/`AxREGION`; `AxLOCK` 1→2 bits
     (normal→`00`, exclusive→`10`; locked is never generated); `CACHE`/`PROT`/
     `USER` pass through.
4. **`axi3_to_axi4` (upgrade, h2f-facing):**
   - Bursts pass through (≤16 beats is legal AXI4); no repacking.
   - **WID handling:** AXI4 has no WID and forbids write interleaving. v1
     contract: the converter accepts W beats of one ID until `WLAST`, then the
     next ID (checked by assertion). The known customer (Cyclone V
     `h2f_axi_master`) does not interleave; full interleave support is a
     documented deferral (6.4).
   - **LOCK mapping:** `00`→normal, `10` (exclusive)→1-bit exclusive, `01`
     (locked)→normal + documented note (no known master issues locked; f2h/h2f
     do not support exclusive — flagged in docs).
   - `CACHE`/`PROT`/`USER` pass through.
5. **Verification** is co-located cocotb (`dv/tests/`, `dv/tbclasses/`)
   against the new RDS-DV AXI3 BFMs (`AXI3MasterRead/Write`,
   `AXI3SlaveRead/Write`) plus existing AXI4 BFMs. Development runs use
   `PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src` to shadow the
   installed framework until cocotb-framework ≥ the release containing #87
   (1.2.2) is cut — same shadow pattern already used for cocotb-test fork
   work. Test matrix: loopback equivalence (axi4→axi3→axi4 ≡ identity for
   len ≤ 16), chopping correctness (len 17..64, per-chunk addresses, response
   merge incl. injected per-chunk SLVERR/DECERR), WID/order rules, lock/QoS/
   REGION mapping, multi-outstanding IDs, back-to-back and stall patterns.
6. **Docs:** MAS/HAS update for the converters IP per repo doc flow; the
   AXI3 protocol deltas section reuses the framing already written for
   RDS-DV #87.

## 4. Out of scope

1. AXI3 FUB family (`rtl/amba/axi3` master/slave rd/wr, stubs) — deferred
   until a second customer exists.
2. AXI3 monitor/observer for the obs system — separate task (DE10 seam
   measurement needs it; it is not required for converter correctness).
3. WRAP-burst chopping (`len` > 16) — unsupported in v1, assertion-guarded;
   our DMA engines issue INCR/FIXED only.
4. Write-data interleaving in `axi3_to_axi4` — v1 restricts to one active W
   ID at a time (asserted); h2f does not interleave.
5. Data-width conversion (dwidth converters already exist).
6. APB3 converters — not needed; APB3↔APB4 is tie-offs (`PSTRB='1`,
   `PPROT='0`), and APB3 does not appear in the DE10 topology. The
   `apb3_to_axi4` wrapper idea (over `apb4_to_axi4`) is recorded as a
   vault deferred item only.

## 5. DE10 integration

`leg-bridge` instantiates `axi4_to_axi3` between the Bridge master port and
`f2h_axi_slave` (128-bit data, per-port `ID_WIDTH` to match the HPS port).
`leg-intel` uses Platform Designer adapters for the same seam — the Intel
MC stays constant across legs.

## 6. Risks

| Risk | Mitigation |
|---|---|
| B/R response-merge bug under per-chunk errors | Worst-of merge is centralized in one function per direction; DV injects per-chunk SLVERR/DECERR explicitly |
| Multi-chunk merge relies on AXI same-ID ordering | Guaranteed by the protocol; DV covers with multi-outstanding IDs and stall patterns |
| Exclusive-access semantics mismatch (f2h/h2f don't support exclusive) | Documented; LOCK mapped conservatively; no exclusive traffic in our systems |
| `axi3_to_axi4` v1 interleave restriction bites a future master | Assertion + documented contract; interleave support is a scoped follow-up, not a rewrite |

## 7. Success criteria

- Converter DV green in `projects/components/utility-ip/converters/dv/`
  (loopback, chopping, WID, mapping, stall matrices).
- Filelists + verible lint clean; `bin/check_sv_decl_order.py` clean;
  `bin/check_task_ids.py` clean after vault edits.
- Vault: new `vault/Tasks/utility-ip/` area (converters tasks; deferred items
  incl. `apb3_to_axi4`); GitHub issue on RTLDesignSherpa tracking the work.
- Consumed by DE10 `leg-bridge` bring-up without modification.

## 8. Deferred items recorded in vault

- `apb3_to_axi4` wrapper (20 lines over `apb4_to_axi4`) for retro-legacy
  customers.
- Tag-based chopped-burst overlap (multiple chunks of one AXI4 transaction
  in flight) if the sequential merge ever limits f2h throughput.
- `axi3_monlite` observer for seam measurements.
- Write-interleave support in `axi3_to_axi4`.
