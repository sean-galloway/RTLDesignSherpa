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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Mode Register (`scoria_mode_register`)

**Module:** `scoria_mode_register.sv`
**Location:** `rtl/fub/`
**Category:** register / decode
**Parent:** `scoria_scheduler_layer`
**Status:** landed and sim-verified

## Purpose

`scoria_mode_register` is the per-rank mode-register shadow plus the live decode of MR-derived timing values. The init sequencer writes the shadow during DRAM bring-up; a later CSR/APB hot-update path can write it without re-running init. Downstream consumers read the decoded values rather than polling raw MR bits, so the decode equations are the single place where JEDEC bit fields become controller-internal numbers.

The block is INHERITED from pumice with DDR3-specific additions: shadow sizing widened to cover LPDDR3 MR0..MR16, `wr_o` decoded from MR0[11:9], and `wrlvl_en_o` gated from MR1[7] for DDR3 only.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_RANKS` | int | 1+ | 1 | number of ranks; one MR shadow bank per rank |
| `MAX_MR_IDX` | int | — | 17 | shadow index range 0..16; covers DDR3 MR0..MR3 and LPDDR3 MR0..MR16 |
| `RKW` | int | — | `(NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1` | rank-index width |

: Table 2.19.1: Mode-register build parameters

## Interface

### Clocks, reset, configuration, and write port

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mc_clk` | in | 1 | controller clock |
| `mc_rst_n` | in | 1 | active-low reset |
| `memtype_i` | in | `memtype_e` | `MEMTYPE_DDR3` or `MEMTYPE_LPDDR3` |
| `mr_we_i` | in | 1 | shadow write enable |
| `mr_index_i` | in | 5 | MR index (0..MAX_MR_IDX-1) |
| `mr_data_i` | in | 16 | MR value to write |
| `mr_rank_i` | in | `RKW` | rank index |

: Table 2.19.2: Clocks, configuration, and shadow write port

### Scheduler request channel (v1 unused)

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mr_req_o` | out | 1 | tied low; no hot MR updates issued through the scheduler in v1 |
| `mr_grant_i` | in | 1 | unused |
| `mr_req_index_o` | out | 5 | tied to zero |
| `mr_req_data_o` | out | 16 | tied to zero |
| `mr_req_rank_o` | out | `RKW` | tied to zero |

: Table 2.19.3: Scheduler MR-update request channel

### Live decoded outputs

| Signal | Direction | Width | Description |
|---|---|---|---|
| `cl_o` | out | 4 | CAS read latency |
| `cwl_o` | out | 4 | CAS write latency |
| `bl_o` | out | 4 | burst length |
| `al_o` | out | 4 | additive latency (tied off in scheduler layer for scoria v1) |
| `drv_strength_o` | out | 2 | output drive strength (tied off in scheduler layer) |
| `odt_o` | out | 2 | ODT rule (tied off in scheduler layer) |
| `wr_o` | out | 5 | write recovery, DDR3 MR0[11:9] |
| `wrlvl_en_o` | out | 1 | DRAM is in write-leveling mode (DDR3 MR1[7]) |

: Table 2.19.4: Live decoded outputs

Live decode is taken from rank 0. Multi-rank designs are expected to use matching MR values across ranks.

## Microarchitecture internals

### Shadow array

The shadow is `r_mr_shadow[NUM_RANKS][MAX_MR_IDX]`, a 16-bit array. On `mr_we_i`, if `mr_index_i < MAX_MR_IDX`, `mr_data_i` is written into `r_mr_shadow[mr_rank_i][mr_index_i]`. The init sequencer drives the write port during the MRS chain.

### Live decode equations

Decode is combinational off `r_mr_shadow[0][0]` (MR0), `r_mr_shadow[0][1]` (MR1), and `r_mr_shadow[0][2]` (MR2), then registered to the outputs.

| Output | DDR3 equation | LPDDR3 equation |
|---|---|---|
| `bl_o` | MR0[1:0]: `00/01 -> 8`, `10 -> 4` | MR1[2:0]: `010 -> 4`, `011/100 -> 8` |
| `cl_o` | `MR0[6:4] + 4 + (MR0[2] ? 8 : 0)` | MR2[3:0] enum: `0001->3`, `0010->4`, `0011->5`, `0100->6`, `0101->7`, `0110->8` |
| `cwl_o` | `MR2[5:3] + 5` | write latency from the same MR2[3:0] enum |
| `al_o` | MR1[4:3]: `00->0`, `01->CL-1`, `10->CL-2`, `11->0` | `0` |
| `wr_o` | MR0[11:9] table: `000->16`, `001->5`, `010->6`, `011->7`, `100->8`, `101->10`, `110->12`, `111->14` | `0` |
| `wrlvl_en_o` | `(memtype == DDR3) && MR1[7]` | `0` |

: Table 2.19.5: Live decode equations

A reserved DDR3 MR0 encoding for `cl_o` returns 4, which is not a legal DDR3 CL and is intentionally unusable. LPDDR3 BL16 clips to BL8 because `bl_o` is 4-bit.

### JESD79-3F MR0 field-map note

JESD79-3F section 3.4.2.2 states in prose that "CAS Latency is defined by MR0 (bits A9-A11)", which contradicts the spec's own Figure 9, where A11:A9 holds write recovery. The figure is self-consistent: the values tabulated against A11:A9 are 16/5/6/7/8/10/12, which are write-recovery cycle counts and cannot be CAS latencies. The RTL comment at `scoria_mode_register.sv:126-133` resolves the inconsistency deliberately in favor of the figure: CL at MR0[6:4], WR at MR0[11:9].

## FSM policy

There is no FSM. The block is a shadow RAM plus combinational decode. Writes are single-cycle; all outputs are registered.

## Timing

All decoded outputs are registered on `mc_clk`. A shadow write in cycle N is visible on `cl_o`/`cwl_o`/`bl_o`/etc. in cycle N+1.

## Notes

- **`al_o`, `drv_strength_o`, `odt_o`, and `mr_req_o` are tied off in the scheduler layer** in scoria v1. The ports exist for family compatibility and future multi-rank or ODT-policy work.
- **LPDDR3 BL16 clips to BL8** because `bl_o` is 4-bit. Widening `bl_o` and updating downstream consumers is recorded as a v3 task.
- **Reserved MR0 encodings** return obviously wrong values rather than plausible-looking defaults, so a mis-programmed MR is visible immediately.
