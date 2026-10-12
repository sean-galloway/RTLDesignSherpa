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

# Request Decode

Delta uses `TDEST` for routing instead of an address range. This is the fundamental difference between Delta and the APB crossbar generator.

## Request matrix

The generator declares a per-slave request vector:

```systemverilog
logic [NUM_MASTERS-1:0] request_matrix [NUM_SLAVES];
```

Each entry is populated in an `always_comb` block:

```systemverilog
for (int s = 0; s < NUM_SLAVES; s++)
    request_matrix[s] = '0;

for (int m = 0; m < NUM_MASTERS; m++)
    if (s_axis_tvalid[m] && (s_axis_tdest[m] < NUM_SLAVES))
        request_matrix[s_axis_tdest[m]][m] = 1'b1;
```

Only masters with a valid beat and a `TDEST` inside the supported slave range contribute to the request matrix.

## Out-of-range TDEST

The generator includes a formal assertion that flags `TDEST >= NUM_SLAVES`. The behavior in simulation for an out-of-range `TDEST` is undefined; the request is simply dropped. System-level validation must ensure that masters never present an invalid destination.
