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

# Test Strategy

## Current Status

As of 2026-10-12, Delta has one cocotb suite, `dv/tests/test_delta_axis_flat_2x4_strb_amba5.py`. It runs against the checked-in `--amba5` example through a flattening harness (`dv/tb/`), with RDS-DV AXIS5 BFMs (`enable_parity=True`) on all six ports and the TB class in `dv/tbclasses/delta_axis_amba5_tb.py`. Three tests run at gate, func and full: routing with every check signal verified (random VALID gaps and READY stalls at func and full), TWAKEUP steering, and check-error injection on every flag. The base flavor still has no simulation suite. The plan below remains the target for it.

## Recommended Test Plan

When a testbench is created, it should cover the following areas.

### 1. Routing Coverage

- For every master `m` and every slave `s`, send at least one packet from `m` to `s`.
- Verify that only the target slave receives the packet.
- Verify that `m_axis_tdest[s]` matches the sent `TDEST`.

### 2. Arbitration Fairness

- Have multiple masters send continuous packets to the same slave.
- Verify that each master receives approximately equal bandwidth over time.
- Verify that no master is starved.

### 3. Packet Atomicity

- Have two masters send multi-beat packets to the same slave.
- Verify that slave receives the first packet's beats contiguously up to `TLAST` before any beat of the second packet.

### 4. Backpressure

- Randomly deassert `m_axis_tready[s]`.
- Verify that only the granted master stalls and that no data is lost.

### 5. Reset

- Assert `aresetn` mid-transaction.
- Verify all grants clear and counters reset.

### 6. Rich Flavor

- With `--strb-width`, verify `TSTRB` pass-through.
- With `--amba5`, verify `TWAKEUP` OR-per-slave, the odd-parity check signals (payload `*CHK` carried, `TVALIDCHK`/`TWAKEUPCHK`/`TREADYCHK` generated or checked) and the sticky `*_parity_error` flags. The existing suite already covers this.

### 7. Formal Assertions

- Run with `+define+FORMAL` or equivalent.
- Verify the one-hot grant and TDEST-range assertions never fire.

## Lint and Generation Checks

For the base flavor, which has no testbench yet, verification consists of:

```bash
python3 bin/delta_generator.py --topology flat --masters 4 --slaves 16 \
    --data-width 64 --output-dir rtl/
verilator --lint-only rtl/delta_axis_flat_4x16.sv
```
