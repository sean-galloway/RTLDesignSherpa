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

# Clocking and Reset

## Clock Domains

| Domain | Clock | Frequency | Components |
|--------|-------|-----------|------------|
| 1 | `hive_c_clk` | 100 MHz (PoC), 150+ MHz (optimized) | VexRiscv core, I/D memories, descriptor generation, control-network master, CDA AXIS master |
| 2 | `serv_clk` | 50-100 MHz | All 16 SERV cores, traffic counters, trigger logic, injection FIFOs, control-network slaves |
| 3 | `delta_clk` | 100 MHz | Delta routers, NI, router configuration registers (Delta-owned; HIVE writes them) |
| 4 | `host_clk` | 50-100 MHz, external | UART, AXI4-Lite slave, command parser |

: Clock domains

`serv_clk` is shared by all 16 monitors — one domain, sixteen instances.
`delta_clk` may be phase-aligned with `hive_c_clk` in the PoC but must not
be assumed synchronous; all crossings use the async FIFOs below regardless.

## CDC Structure

Every crossing is a repo-library dual-clock FIFO or synchronizer; there are
no combinational crossings.

```
hive_c_clk → delta_clk    CDA descriptors:      256-bit × 8 entries
delta_clk → hive_c_clk    PKT_STATUS return:    128-bit × 16 entries (aggregates all SERVs)
serv_clk → delta_clk      Per-SERV injection:   128-bit × 4 entries × 16
delta_clk → serv_clk      Per-SERV config in:   128-bit × 4 entries × 16
host_clk → hive_c_clk     AXIL data:            32-bit × 8 entries; control: dual-flop sync
hive_c_clk → serv_clk     Control commands:     32-bit × 2 entries per SERV (low bandwidth)
serv_clk → hive_c_clk     Status uplink:        32-bit × 4 entries per SERV, round-robin arbitrated
```

: CDC inventory

FIFO depths follow the house rule: ≥ 4 entries minimum to bound
full/empty oscillation; deeper where aggregation justifies it (status return
holds a full round of 16 SERV reports).

## Reset Architecture

**Global reset (`system_rst_n`):** active-low, asynchronous assertion,
synchronous deassertion to each domain. Minimum assertion: 16 cycles of the
slowest clock (`serv_clk`).

**Domain resets**, each synchronized from `system_rst_n`:

| Reset | Domain | Scope | Notes |
|-------|--------|-------|-------|
| `hive_c_rst_n` | hive_c_clk | VexRiscv, memories, control master | Memory init required after reset |
| `serv_rst_n[15:0]` | serv_clk | Individual monitors | Independently controllable: debug, recovery, reconfig |
| `delta_rst_n` | delta_clk | Routers, NI, config logic | Must drain in-flight packets first (asserted by config manager, not the host) |
| `host_rst_n` | host_clk | UART, AXIL slave, parser | Async to HIVE-C; commands require handshake |

: Domain resets

**Reset synchronizer** (all domains, house pattern — async assert, 2-stage
sync release):

```systemverilog
module reset_synchronizer (
    input  logic clk,
    input  logic async_rst_n,
    output logic sync_rst_n
);
    logic [1:0] sync_chain;
    always_ff @(posedge clk or negedge async_rst_n) begin
        if (!async_rst_n) sync_chain <= 2'b00;
        else              sync_chain <= {sync_chain[0], 1'b1};
    end
    assign sync_rst_n = sync_chain[1];
endmodule
```

## Reset Sequencing

Assertion: `system_rst_n` low → all domain resets assert asynchronously →
FSMs to IDLE/RESET → FIFO pointers clear → config registers to reset values.

Deassertion (staged): host interface → HIVE-C → Delta Network → SERV
monitors (last). After deassert, HIVE-C loads firmware, Delta enters
Context 0 (systolic), SERVs enter monitoring mode; system-ready after
~100 cycles of the slowest clock. See Chapter 4.4 for the boot-time
behavior description.

## Soft Reset

The soft-reset register (HAS §4.3) maps to `serv_rst_n[15:0]`,
`delta_rst_n`, control-network reset, and `hive_c_rst_n` respectively. Soft
resets are synchronous to the target domain and re-use the same staged
sequencing; a HIVE-C self-reset (bit 0) is legal but leaves the network
unsupervised until firmware re-initializes — firmware sets a watchdog policy
for it.

## Clock Gating (Optional)

- SERV gating: gate `serv_clk` per monitor when idle; ~5% system power;
  1-2 cycle wake-up. Not in the PoC bring-up plan.
- Router gating: per Delta's own power plan (Delta MAS); HIVE only asserts
  tile-disable via PKT_CONFIG.
- HIVE-C gating: rejected — must stay responsive to interrupts.

---

**Last Updated:** 2026-10-12
