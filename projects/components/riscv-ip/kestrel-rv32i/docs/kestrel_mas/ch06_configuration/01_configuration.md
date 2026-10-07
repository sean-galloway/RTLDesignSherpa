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

# Parameters, Defines, and Filelists

## Parameters

### kestrel_core

| Parameter | Type | Default | Verified values | Description |
|-----------|------|---------|-----------------|-------------|
| `RESET_ADDR` | `logic [31:0]` | `32'h0000_0000` | `0x0`, `0x100`, `0x8000_0000` | Reset fetch address; the first retired beat's `pc_rdata` equals it (testplan scenario CORE-03) |

: kestrel_core parameters

### kestrel_mem_loader

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `AXIL_ADDR_WIDTH` | int | 18 | AXIL slave address width; bits [17:0] of the map |
| `AXIL_DATA_WIDTH` | int | 32 | One 32-bit word per beat |
| `MEM_WORDS` | int | 16384 | Words per array (64 KB imem + 64 KB dmem) |
| `SKID_DEPTH_AW` / `SKID_DEPTH_W` / `SKID_DEPTH_B` | int | 2 / 2 / 2 | `axil4_slave_wr` skid depths |
| `SKID_DEPTH_AR` / `SKID_DEPTH_R` | int | 2 / 4 | `axil4_slave_rd` skid depths |

: kestrel_mem_loader parameters

Only the default loader parameterization is exercised by the testplans (single build config; recorded as verified, no sweep claimed). `RESET_ADDR` coverage is recorded per value in the core testplan.

## Defines and Includes

| Include | Used by | Purpose |
|---------|---------|---------|
| `reset_defs.svh` (via `-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f`) | `kestrel_core`, `kestrel_regfile`, `kestrel_mem_loader` | `ALWAYS_FF_RST` / `RST_ASSERTED` macros: asynchronous assert, synchronous deassert, active-low |

: Shared defines

No `define` configuration surface exists beyond this; there are no feature ifdefs in the kestrel RTL.

## Filelists

| Filelist | Contents | Needs |
|----------|----------|-------|
| `rtl/filelists/kestrel_pkg.f` | `kestrel_pkg` alone | `$KESTREL_ROOT` |
| `rtl/filelists/fub/kestrel_alu.f` | ALU + package | `$KESTREL_ROOT` |
| `rtl/filelists/fub/kestrel_decode.f` | Decode + package | `$KESTREL_ROOT` |
| `rtl/filelists/fub/kestrel_imm_gen.f` | Immediate generator + package | `$KESTREL_ROOT` |
| `rtl/filelists/fub/kestrel_regfile.f` | Register file + `reset_defs` + package | `$KESTREL_ROOT`, `$REPO_ROOT` |
| `rtl/filelists/fub/kestrel_mem_loader.f` | Loader + `reset_defs` + package + `axil4_slave_wr`/`axil4_slave_rd` closures | `$KESTREL_ROOT`, `$REPO_ROOT` |
| `rtl/filelists/top/kestrel_core.f` | Core top + all core FUB closures | `$KESTREL_ROOT`, `$REPO_ROOT` |
| `rtl/filelists/kestrel_all.f` | Master closure: everything above | `$KESTREL_ROOT`, `$REPO_ROOT` |
| `dv/filelists/kestrel_tb.f` | `kestrel_tb_top` + `kestrel_loader_tb_top` on `kestrel_all.f` | `$KESTREL_ROOT` |

: Filelists (`KESTREL_ROOT` = `projects/components/riscv-ip/kestrel-rv32i`; `REPO_ROOT` = RTLDesignSherpa checkout root)

Compile-order and closure discipline: each list is complete for its module (package, includes, leaf dependencies); `kestrel_all.f` includes everything with `-f` and never hand-lists sources. The filelists are the supported compile interface.

## Regenerating This Document

```bash
# from projects/components/riscv-ip/kestrel-rv32i/docs
./generate_mas_pdf.sh --rev 0.1     # KESTREL_MAS_v0.1.docx / .pdf
./generate_has_pdf.sh --rev 0.1     # KESTREL_HAS_v0.1.docx / .pdf
python3 gen_kestrel_figures.py      # regenerate figures + waveform PNGs
```

`gen_kestrel_figures.py` (this directory) redraws the block/composition figures with matplotlib and renders the wavedrom sources in `kestrel_mas/assets/wavedrom/*.json` via `wavedrom-cli` + `inkscape`; both build scripts only consume the committed PNGs.

---

**Last Updated:** 2026-10-07
