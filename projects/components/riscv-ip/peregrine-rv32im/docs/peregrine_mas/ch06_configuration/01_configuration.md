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

# Parameters, Defines and Filelists

## Parameters

| Parameter | Where | Default | Effect |
|-----------|-------|---------|--------|
| `RESET_ADDR` | core, top | 0x0000_0000 | First fetch address |
| `CACHE_EN` | core | 0 | 0: cacheless (Harvard registered-read ports); 1: inside `peregrine_top` (`dmem_req_pre`, `fencei_req`, the interrupt lock) |
| `MUL_DSP` | core, top, mdu | 0 | 1: one registered DSP multiply (2 stall cycles) instead of 33 |
| `BP_EN` | core, top, bpred | 1 | 0: no predictor storage; predict not taken (merlin's fetch) |
| `BTB_ENTRIES`, `BHT_ENTRIES` | core, top, bpred | 32, 256 | Predictor sizes, powers of two, BHT >= BTB |
| `ICACHE_BYTES`, `ICACHE_LINE` | top | 4096, 64 | I\$ geometry |
| `DC_SETS`, `DC_WAYS`, `DC_LINE` | top | 128, 4, 64 | amber geometry (32 KiB) |
| `AXI_DW` | top, icache, uc_axi, arb | 64 | Fabric data width and amber's `BUS_WIDTH`; 32 or 64 |
| `AXI_IW` | top, icache, uc_axi, arb | 4 | Per-master id width; the fabric id adds the master index |
| `MTIME_DIV` | top, clint | 1 | Clocks per `mtime` tick |

: peregrine parameters

The geometries are the ones peregrine was gated and timed at; other values elaborate but are not regressed.

## Defines

| Define | Effect |
|--------|--------|
| `RISCV_FORMAL_ALTOPS` | `peregrine_mdu` returns riscv-formal's stand-in M results. Set only by `formal/peregrine/riscv-formal`; never in simulation or synthesis |
| `XILINX` | Adds `use_dsp = "yes"` on the `MUL_DSP` product |

: Defines

The predictor tables carry `ram_style = "distributed"`, the I\$ data `ram_style = "block"` and its tags `ram_style = "distributed"`, unconditionally.

## Filelists

| Filelist | Pulls in |
|----------|----------|
| `rtl/filelists/peregrine_pkg.f` | `rv32i_pkg`, `peregrine_pkg` |
| `rtl/filelists/fub/peregrine_fubs.f` | The pipeline registers, hazard unit, CSR file, M unit, predictor |
| `rtl/filelists/fub/peregrine_<block>.f` | One per FUB: `bpred`, `mdu`, `icache`, `clint`, `uc_axi`, `axi4_arb` |
| `rtl/filelists/top/peregrine_core.f` | `reset_defs`, `reset_sync`, the common-rv32i blocks, `kestrel_regfile`, the FUBs, `peregrine_core` |
| `rtl/filelists/top/peregrine_top.f` | `peregrine_core.f`, the I\$, CLINT, uncached port, arbiter, `amber_top.f`, `peregrine_top` |
| `rtl/filelists/peregrine_all.f` | Everything in the area |

: peregrine filelists

The area is registered in `bin/filelists.toml` as `riscv-ip/peregrine-rv32im`.

## Regenerating This Book

The port and parameter tables in both books are generated: run `python3 gen_port_tables.py` in this directory after any change to a module header (the build scripts run it with `--check` and stop if a table is stale). The block diagrams are graphviz sources under each book's `assets/graphviz/`, rendered by `regenerate_all_graphviz.sh` there.

---

**Last Updated:** 2026-11-25
