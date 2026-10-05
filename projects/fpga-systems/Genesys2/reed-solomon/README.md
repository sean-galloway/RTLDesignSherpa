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

# Reed-Solomon on the Nexys A7-100T

The Reed-Solomon codec (`projects/components/ecc-ip/reed-solomon`) on the
board, in a loop that validates both key-equation solvers against each other
and against a reference that never saw the errors.

## The loop (build-loop)

```
UART -> uart_axil_bridge -> bridge_rs_loop_axil (generated 1x3 fabric)
                              |  rs_loop_apb  0x00000000  -> apb4_to_peakrdl -> rs_loop_regs
                              |  rs_regs_apb  0x00010000  -> axi4_intf_master_observer
                              |                            (AXI4 flavours; read-0 stub on AXIS.
                              |                             codec CSRs remain reserved, PRD D9)
                              |  obs_apb      0x00020000  -> axis4_intf_observer on the
                              |                            four AXIS seams (every image)
                                                     |
  axis4_master_pattern_gen (32-bit, one packet per block, LFSR data + CRC-32)
        |                                    \
  rs_encoder_core RS(252,236)                 \  bypass: generator straight to
        |                                      \ the checkers, codec out of loop
  error_injector     (none | exact count | burst | rate | clusters)
        |
        +----> rs_decoder_core KES_ALGO=RIBM   ----> axis4_slave_pattern_check A
        |                                     \
        +----> rs_decoder_core KES_ALGO=EUCLID ----> axis4_slave_pattern_check B
                                                \
                                     comparator: A and B beat for beat, verdict for verdict
```

**The profile is RS(252,236)**, the reference RS(255,239) shortened by three
symbols so that n and k are multiples of the 4-symbol beat. That keeps every
beat full, which the shared AXI-Stream checker needs: it compares whole
32-bit words against its regenerated pattern and would flag the zeroed lane of
a partial beat. Geometry lives in `build-loop/rtl/rs_loop_cfg_pkg.sv` and
nowhere else.

**How the two solvers are validated.** The same corrupted blocks reach both
decoders. Each decoder's output is compared beat by beat against the
generator's regenerated LFSR pattern (the checker's `data_err`), so a
correction is judged by a reference that never saw the errors, not by the
other decoder. The comparator then requires riBM and Euclid to agree beat for
beat and on every block's verdict. Up to t errors per block both decoders
must correct every block with exactly e symbols and no beat may mismatch;
above t both must flag every block uncorrectable and the checkers must have
seen mismatches (the errors reached them); at every e the comparator must be
clean. The checker's CRC-32 is over its regenerated words, so a CRC match is a
delivery check (same number of words as generated), not a data check.
`bin/seq_sweep.py` prints the table for e = 0 .. 2t + 2.

**Board result (Nexys A7 210292BFA3EE, 2026-09-30, 64 blocks per point):**
e = 0 .. 8 every block corrected with exactly e symbols and no mismatching
beat on either decoder; e = 9 .. 18 every block flagged uncorrectable on both
with mismatches seen; riBM and Euclid agreed on every beat and every verdict
at every e, with random ready on the checkers too, and in burst and rate
modes. The fabric's windows were probed on hardware: 0x0 reads the
loop block's identifier, and both expansion windows answer with their
interface observer -- OBS_CAPS at 0x20000 reports the four AXIS seams on every
image, at 0x10000 the codec's four AXI4 master ports on the AXI4 flavours and
a read-0 stub on AXIS. `host_rs_loop.py obs` reads them on the board: the
per-port beat counts are the exact run arithmetic (B blocks x 59 message / 63
codeword beats), they stay exact at e = t, and the AXI4 latency histograms
sum to their timed-transaction totals (`--hist`). Throughput
69.3 cycles per 63-beat block back to back (bypass 59.0), 122.0 under random
ready. Timing met after place and route at 100 MHz, WNS +0.157 ns; 18248
LUTs, 8160 flops, 6 DSPs, no BRAM.

**Why the generator was not given an error-injection mode.** An error in the
generator's data is encoded faithfully and is invisible to the code. Errors
must be injected AFTER the encoder, so the shared `error_injector` is its own block
on the coded stream. Its exact-count mode places exactly e errors per block
at uniformly random distinct positions (selection sampling), which is what
makes the e = t and e = t + 1 expectations sharp.

## The two properties this flow must keep

**Every register is accessed by name.** The host driver, the CLI and all three
sequences go through `UartRegisterMap` over `dv/tbclasses/rs_loop_regs_regmap.py`,
which `make regmap` generates from `rtl/rs_loop_regs.rdl`. There is no offset
anywhere in `host/` or `bin/`. The one place raw addresses appear is
`cocotb_test_uart_windows`, which tests the fabric's address decode itself and
therefore cannot use a register name: the reserved windows hold no registers.
It parses the window bases out of `bridge_rs_loop_axil.toml` rather than
restating them, so a moved window moves in one place.

**Every sequence runs in the sim harness exactly as on the board.**
`cocotb_test_uart_sequences` builds a `SequenceContext` with `board=None` and
the cocotb UART as the transport, then runs `init -> smoke -> sweep` through
the same `SequenceRunner` that `bin/run_smoke.py` drives on the board, with the
same dependency resolution. The sequences are unmodified; the only deviations
are `blocks` and the sweep's `counts`, both runtime parameters, because a
32-bit UART transaction costs about 3000 sim cycles against a block's 63. The
test is mutation-checked: breaking a sequence's expectation fails it.

Without that second test a sequence-layer bug is invisible in simulation, which
is the drift `vault/handbook/fpga/cmn-infra/uart-harness.md` records from
another flow, where the cosim reimplemented the campaigns inline and the shared
runner was never exercised.

## Running it

```bash
source env_python
cd projects/fpga-systems/Genesys2/reed-solomon
make lint                    # verilator + declaration order, whole harness
make sim                     # the host programs over the REAL UART bridge in cocotb
make bitstream               # Vivado (background it); REGEN_BRIDGES=1 to take a new fabric
make program                 # board registry picks the Nexys A7
bin/run_smoke.py             # init, smoke (bypass, clean, e=t, e=t+1)
bin/run_smoke.py --sequences init smoke sweep --blocks 64
build-loop/host/host_rs_loop.py sweep --blocks 64      # the same programs, as a CLI
```

**Board target switch.** Set `RS_TARGET=genesys2` to build for the Digilent
Genesys 2 (xc7k325tffg900-2) instead of the default Nexys A7-100T; the wrapper
derives 100 MHz from the 200 MHz LVDS system clock and everything downstream
is unchanged. The default `nexys_a7_100t` keeps the original image names and
report layout byte-identical.

`make regmap` regenerates the CSR regblock and the by-name regmap from
`build-loop/rtl/rs_loop_regs.rdl` (never hand-edit `rtl/generated/`).

## Layout

| Path | What |
|---|---|
| `bin/` | `rs_env.py` (path anchor), `seq_init.py`, `seq_smoke.py`, `seq_sweep.py`, `run_smoke.py` |
| `rtl/bridges/` | the generated 1x3 AXI-Lite fabric: `configs/bridge_rs_loop_axil.toml` + connectivity CSV, `generated/`, `filelists/`. Shared by this component's builds; `bin/regen_bridges.sh` regenerates, the build PREBUILD checks for drift |
| `build-loop/rtl/` | `rs_loop_cfg_pkg.sv` (the one source of geometry), `rs_loop_regs.rdl`, `rs_loop_harness.sv`, `rs_loop_top.sv`, `generated/rs_loop_regs/` |
| `build-loop/host/` | `rs_loop.py` (driver, by-name registers), `rs_loop_programs.py` (the programs sim and board both run), `host_rs_loop.py` (CLI) |
| `build-loop/dv/` | `tb/rs_loop_uart_tb_top.sv`, `tests/test_rs_loop_uart.py` (8 tests: smoke, windows, sequences, bypass, clean, e=t, e=t+1, throttled), `tbclasses/rs_loop_regs_regmap.py` (generated) |
| `build-loop/fpga/` | `tcl/`, `constraints/rs_loop.xdc`, `bitstream/`, `reports/` |

Handbook: `vault/handbook/fpga/cmn-infra/` (uart-harness, build-flows, sequences, one-source-config).
