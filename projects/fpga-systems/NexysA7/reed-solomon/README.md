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
UART -> uart_axil_bridge -> axil4_to_peakrdl -> rs_loop_regs (PeakRDL, 32 CSRs)
                                                     |
  axis4_master_pattern_gen (32-bit, one packet per block, LFSR data + CRC-32)
        |                                    \
  rs_encoder_core RS(252,236)                 \  bypass: generator straight to
        |                                      \ the checkers, codec out of loop
  rs_error_injector  (none | exact count | burst | rate)
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
decoders. Each decoder's output is checked against the generator's
regenerated LFSR pattern and its running CRC-32, so a correction is judged by
a reference that never saw the errors, not by the other decoder. The
comparator then requires riBM and Euclid to agree beat for beat and on every
block's verdict. Up to t errors per block both decoders must correct every
block with exactly e symbols and both CRCs must match the generator's; above
t both must flag every block uncorrectable (the CRCs then differ by design);
at every e the comparator must be clean. `bin/seq_sweep.py` prints that table
for e = 0 .. 2t + 2.

**Why the generator was not given an error-injection mode.** An error in the
generator's data is encoded faithfully and is invisible to the code. Errors
must be injected AFTER the encoder, so `rs_error_injector` is its own block
on the coded stream. Its exact-count mode places exactly e errors per block
at uniformly random distinct positions (selection sampling), which is what
makes the e = t and e = t + 1 expectations sharp.

## Running it

```bash
source env_python
cd projects/fpga-systems/NexysA7/reed-solomon
make lint                    # verilator + declaration order, whole harness
make sim                     # the host programs over the REAL UART bridge in cocotb
make bitstream               # Vivado (background it: see the handbook)
make program                 # board registry picks the Nexys A7
bin/run_smoke.py             # init, smoke (bypass, clean, e=t, e=t+1)
bin/run_smoke.py --sequences init smoke sweep --blocks 64
build-loop/host/host_rs_loop.py sweep --blocks 64      # the same programs, as a CLI
```

`make regmap` regenerates the CSR regblock and the by-name regmap from
`build-loop/rtl/rs_loop_regs.rdl` (never hand-edit `rtl/generated/`).

## Layout

| Path | What |
|---|---|
| `bin/` | `rs_env.py` (path anchor), `seq_init.py`, `seq_smoke.py`, `seq_sweep.py`, `run_smoke.py` |
| `build-loop/rtl/` | `rs_loop_cfg_pkg.sv` (the one source of geometry), `rs_loop_regs.rdl`, `rs_loop_harness.sv`, `rs_loop_top.sv`, `generated/rs_loop_regs/` |
| `build-loop/host/` | `rs_loop.py` (driver, by-name registers), `rs_loop_programs.py` (the programs sim and board both run), `host_rs_loop.py` (CLI) |
| `build-loop/dv/` | `tb/rs_loop_uart_tb_top.sv`, `tests/test_rs_loop_uart.py`, `tbclasses/rs_loop_regs_regmap.py` (generated) |
| `build-loop/fpga/` | `tcl/`, `constraints/rs_loop.xdc`, `bitstream/`, `reports/` |

Handbook: `vault/handbook/fpga/cmn-infra/` (uart-harness, build-flows, sequences, one-source-config).
