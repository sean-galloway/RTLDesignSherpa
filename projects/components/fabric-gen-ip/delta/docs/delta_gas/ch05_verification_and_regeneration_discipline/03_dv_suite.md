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

# DV Suite

The component-level DV suite lives in `dv/tests/` and uses cocotb.

## Test focus areas

A complete Delta DV suite should cover:

| Scenario | What to verify |
|----------|----------------|
| Single-packet routing | A master sends a packet to each slave; `TDEST` selects correctly. |
| Multi-master contention | Two masters target the same slave; arbitration is fair and packet-atomic. |
| Backpressure | Assert `m_axis_tready` low; `s_axis_tready` follows correctly. |
| TLAST handling | Grants release only after `TLAST`. |
| AMBA 5 sidebands | `TWAKEUP` steers by `TDEST`; `TPARITY` passes through with `TDATA`. |
| Out-of-range TDEST | Formal assertion fires; simulation drops the request. |
| Performance counters | Counters increment on `valid && ready && tlast`. |

## Running the suite

```bash
cd projects/components/fabric-gen-ip/delta/dv/tests
make clean-all && make run-all-gate
```

After a generator change, this must pass with zero failures before the regenerated RTL is committed.

## Adding a new test

1. Add a new cocotb test file in `dv/tests/`.
2. Reference the generated module under test.
3. Add the test name to the area regression list.
