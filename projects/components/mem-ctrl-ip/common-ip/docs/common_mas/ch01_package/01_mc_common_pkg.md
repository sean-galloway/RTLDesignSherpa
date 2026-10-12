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

# Chapter 1: `mc_common_pkg` — the family package

`mc_common_pkg` is the single source of family-shared types for the memory-controller research IPs (pumice DDR2/LPDDR2, scoria DDR3/LPDDR3, andesite DDR4/LPDDR4). The package was extracted on 2026-10-10 during the Phase 2 common-IP reorganization (`includes/mc_common_pkg.sv:17-18`). Its encodings are the family encodings; the design authority is family doc 01 ([01_mem_ctrl_pkg.md](../../01_mem_ctrl_pkg.md)). The plane-stack context is in the family HAS ([common_has_index.md](../../common_has/common_has_index.md)); this chapter documents only the package contents and the rock-side boundary.

## 1.1 Package role

`mc_common_pkg` holds the types that were previously duplicated, near-identically, across `pumice_pkg`, `scoria_pkg`, and `andesite_pkg` (`includes/mc_common_pkg.sv:19-23`). It is imported directly by every common plane and shared FUB in `common-ip/rtl/` (for example, `macro/mc_axi4_plane.sv:178`, `macro/mc_scheduler_plane.sv:26`, `fub/mc_cmd_arbiter.sv:34`, `fub/mc_addr_mapper.sv:55`). The package contains no parameters, no build-time knobs, and no CSR definitions; it is a pure type-and-function package meant to be imported with `::*` at module scope.

## 1.2 `memtype_e`

`memtype_e` is a 3-bit packed enum (`includes/mc_common_pkg.sv:41-48`) whose encoding is owned by family doc 01 Table 1.0. Bit [2] is the LP axis; bits [1:0] form a generation field.

| `memtype_e` | Member | `memtype_e[1:0]` | `memtype_e[2]` LP |
|---|---|---|---|
| 3'b000 | MEMTYPE_DDR2 | 2'b00 (generation 2) | 0 |
| 3'b001 | MEMTYPE_DDR3 | 2'b01 (generation 3) | 0 |
| 3'b010 | MEMTYPE_DDR4 | 2'b10 (generation 4) | 0 |
| 3'b100 | MEMTYPE_LPDDR2 | 2'b00 | 1 |
| 3'b101 | MEMTYPE_LPDDR3 | 2'b01 | 1 |
| 3'b110 | MEMTYPE_LPDDR4 | 2'b10 | 1 |
| 3'b011, 3'b111 | reserved | 2'b11 (generation 5, basalt) | — |

The reserved codes (`3'b011` and `3'b111`) are illegal and must decode as an error rather than alias to a legal member (`includes/mc_common_pkg.sv:36-39`).

## 1.3 Shared type inventory

The package exports the following enums, struct, and helper functions. Every item is used by at least one common plane or FUB.

| Symbol | Kind | File:line | Notes |
|---|---|---|---|
| `memtype_e` | enum | `includes/mc_common_pkg.sv:41-48` | 3-bit, six legal members, two reserved codes |
| `dram_op_e` | enum | `includes/mc_common_pkg.sv:59-78` | 5-bit superset of legacy 4-bit op tables; `OP_MPC = 5'h10` is the LPDDR4 addition |
| `bank_state_e` | enum | `includes/mc_common_pkg.sv:84-92` | bank-machine state |
| `page_policy_e` | enum | `includes/mc_common_pkg.sv:101-105` | open/close plus reserved; pumice's `PAGE_POLICY_HAPPY_HYBRID` (2'h2) was retired 2026-08-25 |
| `decoded_addr_t` | packed struct | `includes/mc_common_pkg.sv:114-119` | rank/bank/row/col, padded to 4/4/18/14 bits |
| `is_column_op` | function | `includes/mc_common_pkg.sv:128-130` | true for RD/RDA/WR/WRA |
| `is_write_op` | function | `includes/mc_common_pkg.sv:132-134` | true for WR/WRA |
| `is_read_op` | function | `includes/mc_common_pkg.sv:136-138` | true for RD/RDA |
| `is_refresh_op` | function | `includes/mc_common_pkg.sv:140-142` | true for REF/REFPB |
| `has_auto_pre` | function | `includes/mc_common_pkg.sv:144-146` | true for RDA/WRA |
| `is_zq_op` | function | `includes/mc_common_pkg.sv:148-150` | true for ZQCS/ZQCL |

### `dram_op_e` encoding

`dram_op_e` is widened to 5 bits so that `OP_MPC` exists once in the family (`includes/mc_common_pkg.sv:21-23`). Values `5'h00` through `5'h0F` are identical to every rock's legacy 4-bit table (`includes/mc_common_pkg.sv:56-57`); the wire-level translation per memtype lives in each rock's DFI command formatter.

| Value | Member | Meaning |
|---|---|---|
| 5'h00 | OP_NOP | no operation |
| 5'h01 | OP_ACT | activate |
| 5'h02 | OP_RD | read |
| 5'h03 | OP_RDA | read with auto-precharge |
| 5'h04 | OP_WR | write |
| 5'h05 | OP_WRA | write with auto-precharge |
| 5'h06 | OP_PRE | precharge |
| 5'h07 | OP_PREA | precharge all banks |
| 5'h08 | OP_REF | all-bank refresh |
| 5'h09 | OP_REFPB | per-bank refresh |
| 5'h0A | OP_MRS | mode register set |
| 5'h0B | OP_ZQCS | ZQ calibration short |
| 5'h0C | OP_ZQCL | ZQ calibration long |
| 5'h0D | OP_SREFE | self-refresh entry |
| 5'h0E | OP_SREFX | self-refresh exit |
| 5'h0F | OP_DPDE | deep-power-down entry |
| 5'h10 | OP_MPC | LPDDR4 multipurpose command; CA-bus encoding per the andesite kmap book |

### `decoded_addr_t` field layout

| Field | Width | Notes |
|---|---|---|
| `rank` | 4 bits | pad to 4; actual width is `$clog2(NUM_RANKS)` |
| `bank` | 4 bits | pad to 4; DDR3 uses 3 |
| `row` | 18 bits | pad to 18; MT41J256M16 uses 15 |
| `col` | 14 bits | pad to 14; MT41J256M16 uses 10 |

## 1.4 Helper-function implementation constraint

Each helper returns a single-line expression (`includes/mc_common_pkg.sv:124-126`). The RTL comment records that multi-line return expressions break yosys' frontend, which is why pumice's formal flow historically had to sv2v-flatten wrappers that imported its package.

## 1.5 What stays rock-side

The three rock packages still exist, but their contents are now thin.

| Rock package | Remaining content | File |
|---|---|---|
| `scoria_pkg` | import/export shim for `mc_common_pkg` only | `research-ip/scoria-ddr3-lpddr3/rtl/includes/scoria_pkg.sv:29-33` |
| `andesite_pkg` | import/export shim for `mc_common_pkg` only | `research-ip/andesite-ddr4-lpddr4/rtl/includes/andesite_pkg.sv:30-34` |
| `pumice_pkg` | import/export shim plus `addr_map_scheme_e` and `odt_rule_e` | `research-ip/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv:28-60` |

`addr_map_scheme_e` is retained only because retired macro/OLD modules still reference the type in regression sentinels (`pumice_pkg.sv:36-40`). `odt_rule_e` is pumice-specific ODT rule select (`pumice_pkg.sv:49-59`).

### Legacy CSR widening argument

The rocks' `PHY_TIMING.memtype` CSR field stays 1-bit wide for Phase 2, with per-rock legacy values (`includes/mc_common_pkg.sv:25-27`; [mc_common_pkg_knobs.md](../../mc_common_pkg_knobs.md)). Pumice maps 0→`MEMTYPE_DDR2` and 1→`MEMTYPE_LPDDR2` at `research-ip/pumice-ddr2-lpddr2/rtl/top/pumice_top.sv:199-207`. Scoria maps 0→`MEMTYPE_DDR3` and 1→`MEMTYPE_LPDDR3` at `research-ip/scoria-ddr3-lpddr3/rtl/top/scoria_top.sv:237-245`. Andesite's CSR rebuild is a follow-up: `andesite_core.sv` currently takes `memtype_i` as a top-level port (`research-ip/andesite-ddr4-lpddr4/rtl/top/andesite_core.sv:90-91`) and no `andesite_top.sv` exists yet, so the legacy cast site is not yet in RTL.

The same config block in pumice and scoria also carries a page-policy cast warning: `REFRESH_TUNING.page_policy_or` uses a software encoding while `page_policy_e` uses OPEN=0/CLOSE=1. The RTL comment records that the old raw cast made software-OPEN run CLOSE and software-CLOSE run HYBRID, corrupting the open_page/reorder config axis (`research-ip/pumice-ddr2-lpddr2/rtl/top/pumice_top.sv:208-212`, `research-ip/scoria-ddr3-lpddr3/rtl/top/scoria_top.sv:246-250`; issue #42). Note that `mc_common_pkg::page_policy_e` retired the HYBRID member in favor of `PAGE_POLICY_RSVD = 2'h3` (`includes/mc_common_pkg.sv:97-105`).

## 1.6 Migration plan reference

The migration that created `mc_common_pkg` is the Phase 2 migration deferred in family doc 01 ([01_mem_ctrl_pkg.md](../../01_mem_ctrl_pkg.md)). The conditions were: execute once, when andesite RTL bring-up starts, with both shipping controllers moving together. The knob inventory ([mc_common_pkg_knobs.md](../../mc_common_pkg_knobs.md)) records what moved, what stayed, the legacy-CSR ruling, and the width-change consequences expected during adoption (e.g., `dram_op_e` re-width 4→5 and `memtype_e` re-width 1→3).

## 1.7 Open question: do the rocks import `mc_common_pkg` directly?

No. As of the Phase 2 extraction, common planes and FUBs import `mc_common_pkg::*` directly, but rock RTL still imports its own rock package (`pumice_pkg::*`, `scoria_pkg::*`, or `andesite_pkg::*`). Each rock package in turn `import`s and `export`s `mc_common_pkg::*` (`research-ip/scoria-ddr3-lpddr3/rtl/includes/scoria_pkg.sv:31-32`, `research-ip/andesite-ddr4-lpddr4/rtl/includes/andesite_pkg.sv:32-33`, `research-ip/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv:30-31`). Therefore `mc_common_pkg` exports every family-shared symbol the rocks need, but the rocks do not source it directly. `pumice_pkg` additionally exports pumice-only symbols (`addr_map_scheme_e`, `odt_rule_e`) that the common package does not and should not carry.

This is a stable, intentional shim: it leaves rock `import` statements untouched while making the common package the single source of family-shared encodings.
