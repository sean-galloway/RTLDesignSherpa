<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Mode Register (`mode_register`)

**Module:** `mode_register.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_mem_cmd_scheduler`
**Status:** implemented (DDR2 + LPDDR2 decode)

## Purpose

Per-rank Mode Register shadow + live decode of MR-derived timing values
for use by the rest of the controller.

On `mr_we_i`, write `mr_data_i` into shadow MR[`mr_index_i`] for
`mr_rank_i` (indices `< MAX_MR_IDX` only). `init_sequencer` drives this
during DRAM bring-up; a CSR/APB hot-update path drives it later.

The `memtype_i` input (`memtype_e`: `MEMTYPE_DDR2` / `MEMTYPE_LPDDR2`)
selects the decode branch for every output. The live decode reads from
rank 0 (multi-rank designs must program matching MR values across ranks;
mixed-per-rank MRs are a TODO).

## Live Decoded Outputs

| Output           | Source (DDR2)    | Source (LPDDR2)                       |
|------------------|------------------|---------------------------------------|
| `cl_o`           | MR0[6:4]         | RL, from the MR2[3:0] RL&WL enum      |
| `cwl_o`          | CL − 1           | WL, from the MR2[3:0] RL&WL enum      |
| `bl_o`           | MR0[2:0]         | MR1[2:0] (4/8; BL16 clips to 8)       |
| `al_o`           | MR1[5:3]         | 0 (not used)                          |
| `drv_strength_o` | MR1[1]           | 0 (informational)                     |
| `odt_o`          | MR1[6,2]         | 0                                     |

For LPDDR2, CL and CWL are **not** independent MR fields — they are both
derived from a single MR2[3:0] "RL & WL" enum per JESD209-2F:

| MR2[3:0] | RL (`cl_o`) | WL (`cwl_o`) |
|----------|-------------|--------------|
| `0001`   | 3           | 1            |
| `0010`   | 4           | 2            |
| `0011`   | 5           | 2            |
| `0100`   | 6           | 3            |
| `0101`   | 7           | 4            |
| `0110`   | 8           | 4            |

(default / illegal codes fall back to RL3/WL1.)

For DDR2, `cl_o` is the raw MR0[6:4] field and `cwl_o` is simply `CL − 1`
(saturating at 0). `bl_o` decodes MR0[2:0] = `010` → BL4, `011` → BL8.

All outputs are strict-flop registered. Consumed by:

- `pumice_cmd_arbiter` / `pumice_mem_cmd_scheduler` — use `cl_o`, `cwl_o`,
  `al_o` to time RD/WR latencies.
- write data path (`pumice_dfi_wr_serializer` via `t_phy_wrlat`) — sized
  against `cwl_o` for the WR-to-wrdata window.
- read data path (`pumice_dfi_rd_aligner` via `t_rddata_en`) — sized
  against `cl_o` for the RD-to-rddata window.
- `dfi_cmd_formatter` — uses `bl_o` to size column commands.

## Burst Length: Fixed per Instance, Parameterized for Family Reuse

A memory controller supports exactly **one** DRAM burst length, chosen at init and
fixed for the life of the instance — the datapath (beat sequencing, prefetch depth,
column-stride math, tWR/tRTP-derived timing windows) is sized around that single
value. pumice does **not** switch BL per transaction; the host/AXI burst is
arbitrary and `axi_intake` splits it into fixed-BL DRAM commands.

`bl_o` is therefore a **build/init constant**, not a per-command control. It is
decoded from the mode register rather than hardcoded so the **same RTL retargets
across the DDR family** — the only thing that changes is the programmed value and
the device/beat widths:

| Family | Burst length | Source          | pumice-beat count (via `bl_dram_beats`)              |
|--------|--------------|-----------------|-----------------------------------------------------|
| DDR2   | BL4 (fixed)  | MR0[2:0]=`010`  | `bl_o >> log2(DRAM_BEAT_WIDTH/DRAM_DEVICE_WIDTH)`    |
| DDR3   | BL8 (fixed)  | MR0[1:0]        | same expression, `bl_o=8`                           |
| DDR4   | BL8 (fixed)  | MR0[1:0]        | same expression, `bl_o=8`                           |

Everything downstream keys off the decoded `bl_o` and the device/beat widths (see
§15 "Narrow-Device (x16) Support"), so no burst-length constants are baked into the
sequencers or the address decode. `BYTE_OFFSET_WIDTH` keys off **device width, not
BL**, so the column granularity is already BL-agnostic.

**BC4 / burst-chop (DDR3/DDR4): out of scope — always issue the full fixed BL (BL8 at the RTL reset; the Nexys A7 board runs BL4).** DDR3 and
DDR4 allow BC4 and BL8-on-the-fly (A12). That is the *only* case where one instance
would see two effective burst lengths per transaction, which would break the
fixed-BL datapath invariant. The design decision is to **not** support BC4: always
transfer the full fixed BL8. Revisit only if a workload demonstrably needs the
partial-burst bandwidth (it usually does not).

## Scope

- `MAX_MR_IDX=17` (indices 0..16) covers both DDR2 (MR0..MR3) and LPDDR2
  (up to MR16). The shadow array is `[NUM_RANKS][MAX_MR_IDX]`.
- **LPDDR2 BL16 clips to BL8** because `bl_o` is 4-bit. A follow-up widens
  `bl_o` to `[4:0]` and updates the 3 downstream macros that consume it.
- `mr_req_o` is tied 0 — no hot MR updates are issued via the scheduler.
  Init does the MR loads directly through this FUB's CSR write port. The
  `mr_req_*` channel is still flopped (all-zero) for port consistency and
  lands when the APB CSR slave provides a write-during-traffic path with a
  quiet-point handshake.

## Tests

Verified by `dv/tests/fub/test_mode_register.py`: `smoke_ddr2`,
`ddr2_cl_sweep`, `reset_values`, `ddr2_bl_sweep`, `ddr2_al_sweep`,
`multi_rank` (plus LPDDR2 RL/WL-enum coverage as the suite is extended for
the `memtype_i` LPDDR2 branch).
