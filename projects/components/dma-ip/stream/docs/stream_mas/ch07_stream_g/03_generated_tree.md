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

# The Generated stream-g Tree and the Board Build

**Generator:** `bin/gen_stream_g.py`
**Status:** Implemented (stream TASK-020)
**Last Updated:** 2026-10-24

---

Above `scheduler_g` the stream-g RTL is STREAM's, so it is derived rather than copied:

| Generated | From | Edits |
|---|---|---|
| `rtl/macro_g/generated/scheduler_group_array_g.sv` | `rtl/macro/scheduler_group_array.sv` | rename; `scheduler` becomes `scheduler_g`; the `seq_*` ports wired; `scheduler_group_array_g_seq.svh` (one `rapids_seq_g`) included in front of the scheduler loop; `$fatal` unless `SHARED_ENGINES` = 1 and `NUM_CHANNELS` is 4, 8 or 16 |
| `rtl/macro_g/generated/stream_core_g.sv` | `rtl/macro/stream_core.sv` | rename; the array becomes `scheduler_group_array_g` |
| `rtl/top_g/generated/stream_g_top_ch8.sv`, `stream_g_top_ch16.sv` | `rtl/top/stream_top_ch8.sv`, `stream_top_ch16.sv` | rename; the core becomes `stream_core_g`; the APB slave's cmd/rsp outputs renamed `host_*` with `stream_g_top_reg_arb.svh` (host + gatling into the one serialized register path) included after them; `stream_g_top_fw.svh` (the firmware load) included before the hwif block, whose FW_* fields it drives |

: Table 7.3.1: Generated files

The register-mailbox master (`seq_reg_*`), the firmware-load bus (`fw_*`) and `seq_restart` are added to
every level's port list after `rst_n` and connected at every instance, so the STREAM files need no
knowledge of them. The product top ties the FW_* read-back fields to 0: STREAM's hwif block has no default
assignment, and an unassigned member would latch. Every edit matches its anchor the expected number of
times or the generator fails; `python3 bin/gen_stream_g.py --check` exits 1 when any generated file is
stale. The filelists are `rtl/filelists/fub_g/`, `macro_g/` and `top_g/`; they pull `rapids_seq_g` and
gatling through rapids' `macro_g/rapids_seq_g.f`, and the firmware include with it.

## The Register Path and the Firmware Load

Two masters share the register command path (the MON-window guard -> `peakrdl_to_cmdrsp` ->
`stream_regs`): the host's APB and the gatling. `rapids_g_reg_arb` (NM = 2) grants one access at a time
and holds the grant until its response: the path is serialized, one agent owns it end to end. The gatling's
address is a 12-bit byte offset in the config window, zero-extended to the APB width (so with a 13-bit map
it cannot reach the MON window; the tests' 12-bit maps have none). The arbiter fragment declares the
`host_*` nets the two APB slave instances connect to, so the generator places it before their generate
block: placed after them, Verilator still resolved the names but Vivado made implicit undriven nets at
the instances, and the first stream-g bitstream had no host register path at all (the Genesys 2 answered
nothing; the Vivado log said `does not have driver`). Every synthesis log is scanned for that line now.

The firmware load is rapids TASK-038's: `FW_CTRL.HOLD` holds the harts and enables `FW_DATA` writes,
`FW_ADDR` advances after each `FW_DATA` write and each `FW_RDATA` read (on the rising edge of the
register's `swmod` / `swacc` level, one flop late), `FW_CTRL.ALG_MAX` caps the selectors, and a
`FW_WRITABLE` = 0 build (a ROM) reads `FW_CTRL.WRITABLE` = 0 and ignores the bus. `FW_CTRL.STREAM_G` = 1
on every stream-g build.

## The Genesys 2 Harness

`projects/fpga-systems/Genesys2/dma-ip/stream/build-perf`: `make <target> STREAM_G=1 [FW_WRITABLE=1]`
builds the harness around `stream_g_top_ch8` (the `STREAM_G` define, reaching Vivado through
`fpga/tcl/create_project.tcl`, lint through `LINT_DEFINES` and the sim-harness tests through
`TEST_STREAM_G`); the harness filelist carries both tops. The bitstream name takes `_g` (`_g_fw`), and
the host reads `BUILD_CONFIG.STREAM_G`. `seq_restart` is tied low in the harness: the harts run from
reset and the firmware polls.
