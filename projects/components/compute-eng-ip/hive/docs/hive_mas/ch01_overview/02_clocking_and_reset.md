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
| 2 | `mon_clk` | 100 MHz | The engine monitor: the gatling core and its memory, and the four per-engine peripheral sets (traffic counters, trigger logic, injection FIFOs, control-network slaves) |
| 3 | `delta_clk` | 100 MHz | Delta routers, NI, router configuration registers (Delta-owned; HIVE writes them) |
| 4 | `host_clk` | 50-100 MHz, external | UART, AXI4-Lite slave, command parser |

: Clock domains

`mon_clk` is the one engine-monitor domain: one gatling core and the four
engines' peripherals. (v0.2 named it `serv_clk`, shared by sixteen SERVs.)
gatling's board build closes at 100 MHz on the Nexys A7.
`delta_clk` may be phase-aligned with `hive_c_clk` in the PoC but must not
be assumed synchronous; all crossings use the async FIFOs below regardless.

## CDC Structure

Every crossing is a repo-library dual-clock FIFO or synchronizer; there are
no combinational crossings.

```
hive_c_clk → delta_clk    CDA descriptors:      256-bit × 8 entries
delta_clk → hive_c_clk    PKT_STATUS return:    128-bit × 16 entries (aggregates all four engines' reports)
mon_clk → delta_clk       Per-engine injection: 128-bit × 4 entries × 4
delta_clk → mon_clk       Per-engine config in: 128-bit × 4 entries × 4
host_clk → hive_c_clk     AXIL data:            32-bit × 8 entries; control: dual-flop sync
hive_c_clk → mon_clk      Control commands:     32-bit × 2 entries per engine (low bandwidth)
mon_clk → hive_c_clk      Status uplink:        32-bit × 4 entries per engine, round-robin arbitrated
```

: CDC inventory

FIFO depths follow the house rule: ≥ 4 entries minimum to bound
full/empty oscillation; deeper where aggregation justifies it (status return
holds several rounds of the four engines' reports).

## Reset Architecture

**Global reset (`system_rst_n`):** active-low, asynchronous assertion,
synchronous deassertion to each domain. Minimum assertion: 16 cycles of the
slowest clock.

**Domain resets**, each synchronized from `system_rst_n`:

| Reset | Domain | Scope | Notes |
|-------|--------|-------|-------|
| `hive_c_rst_n` | hive_c_clk | VexRiscv, memories, control master | Memory init required after reset |
| `mon_rst_n` | mon_clk | The engine monitor (gatling and the four peripheral sets) | One reset for the monitor; a single engine's context is held and restarted with gatling's per-context run bit instead (below) |
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

Deassertion (staged): host interface → HIVE-C → Delta Network → engine
monitor (last). After deassert, HIVE-C loads firmware (its own, and the
monitor image into each gatling context's bank), Delta enters Context 0
(systolic), and HIVE-C sets the four run bits so the contexts enter
monitoring mode; system-ready after
~100 cycles of the slowest clock. See Chapter 4.4 for the boot-time
behavior description.

## Soft Reset

The soft-reset register (HAS §4.3) maps to the four gatling context run
bits (a held context waits at its reset address, and its bank can be
reloaded while the other three run), `delta_rst_n`, control-network reset, and `hive_c_rst_n` respectively. Soft
resets are synchronous to the target domain and re-use the same staged
sequencing; a HIVE-C self-reset (bit 0) is legal but leaves the network
unsupervised until firmware re-initializes — firmware sets a watchdog policy
for it.

## Clock Gating (Optional)

- Monitor gating: not per engine. gatling's rotation never skips a context,
  so one clock serves all four; `mon_clk` can only be gated as a whole.
  Not in the PoC bring-up plan.
- Router gating: per Delta's own power plan (Delta MAS); HIVE only asserts
  tile-disable via PKT_CONFIG.
- HIVE-C gating: rejected — must stay responsive to interrupts.

---

**Last Updated:** 2026-11-25
