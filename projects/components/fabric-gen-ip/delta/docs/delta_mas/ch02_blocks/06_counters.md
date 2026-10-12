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

# Packet Counters

## Purpose

Optional 32-bit packet counters track completed packets at the master boundary and the slave boundary. They are enabled by default and can be disabled with `--no-counters`.

## Implementation

```systemverilog
logic [31:0] pkt_count_master [NUM_MASTERS];
logic [31:0] pkt_count_slave [NUM_SLAVES];

generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_master_counters
        always_ff @(posedge aclk or negedge aresetn) begin
            if (!aresetn)
                pkt_count_master[m] <= '0;
            else if (s_axis_tvalid[m] && s_axis_tready[m] && s_axis_tlast[m])
                pkt_count_master[m] <= pkt_count_master[m] + 1;
        end
    end

    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_slave_counters
        always_ff @(posedge aclk or negedge aresetn) begin
            if (!aresetn)
                pkt_count_slave[s] <= '0;
            else if (m_axis_tvalid[s] && m_axis_tready[s] && m_axis_tlast[s])
                pkt_count_slave[s] <= pkt_count_slave[s] + 1;
        end
    end
endgenerate
```

## Behavior

- A master counter increments when the master completes a packet (last beat accepted).
- A slave counter increments when the slave completes a packet (last beat accepted).
- Counters wrap at 32 bits.
- Counters are not exposed on module ports; they are internal observation points.

## Disabling Counters

Use `--no-counters` to remove the counter logic and save area:

```bash
python3 bin/delta_generator.py --topology flat --masters 4 --slaves 16 \
    --data-width 64 --no-counters --output-dir rtl/
```
