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

# peregrine_clint

**Module:** `peregrine_clint.sv`

## Responsibility

The core-local interruptor for one hart (PRD P7), in the SiFive layout; the register offsets are in the HAS ("Address Map").

## Parameters

<!-- GEN:params:peregrine_clint -->

| Parameter | Kind | Type | Default | Description |
|----------------|----------|------------|--------------|------------------------------|
| `MTIME_DIV` | parameter | `int` | `1` | CLINT clocks per mtime tick (>= 1) |

: peregrine_clint parameters

<!-- /GEN -->

## Ports

<!-- GEN:ports:peregrine_clint -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Clock |
| `rst_n` | input | `1` | Reset |
| `req_valid` | input | `1` | Register access this cycle |
| `req_addr` | input | `[15:0]` | offset within the CLINT window |
| `req_we` | input | `1` | Write |
| `req_wstrb` | input | `[3:0]` | Byte strobes |
| `req_wdata` | input | `[31:0]` | Write data |
| `rsp_valid` | output | `1` | Response, the cycle after the request |
| `rsp_rdata` | output | `[31:0]` | Read data |
| `irq_software` | output | `1` | msip bit 0 |
| `irq_timer` | output | `1` | mtime >= mtimecmp (registered) |

: peregrine_clint ports

<!-- /GEN -->

## Behavior

- **Port:** one request per cycle, always ready; the response (`rsp_valid`, `rsp_rdata`) is the next cycle for reads and writes alike, the same 1-cycle shape as a D\$ hit, so the wrapper treats the CLINT like amber.
- **`mtime`** increments once every `MTIME_DIV` clocks; resets to 0.
- **`mtimecmp`** resets to all ones, so no timer interrupt is pending out of reset.
- **`irq_timer`** is registered: `mtime >= mtimecmp`, one cycle behind both.
- **`irq_software`** is `msip` bit 0.
- **Writes** take their byte strobes; any other offset reads 0 and ignores writes. A write to one half of `mtime` or `mtimecmp` is not atomic with the other half.

---

**Last Updated:** 2026-11-25
