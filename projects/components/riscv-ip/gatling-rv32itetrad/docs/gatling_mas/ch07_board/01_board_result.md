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


# Board Result

## Nexys A7-100T (2026-10-21)

Build: `projects/fpga-systems/NexysA7/riscv-ip/gatling/build-bram` (gatling_core + gatling_mem_bram + the UART-to-AXI4-Lite bridge), IMPL=explore, from `make clean-all`. Host: `make host-gatling`, the same programs as the UART-equivalence cosim.

| Measure | Value |
|---|---|
| Clock | 100 MHz, worst slack +0.152 ns |
| rv32ui battery | 168/168: 42 images x 4 harts, four different images at once per round |
| CPI per hart | 4.004 / 4.005 / 4.004 / 4.004 |
| Battery throughput | 0.688 IPC (68.8 MIPS): rounds wait for their longest image |
| Peak throughput | 1 IPC, 100 MIPS (four harts of 25) |
| LUTs / registers | 2,281 / 1,742 (whole board top) |
| gatling_core | 1,066 LUTs, 2 RAMB18 (the register files) |
| gatling_mem_bram | 799 LUTs, 16 block RAM tiles (4 x 16 KB) |
| DSPs | 0 |

: Table 7.1: gatling on the Nexys A7-100T

## The worst path

9.4 ns, 10 logic levels: register-file block RAM output -> branch comparator / next-PC and halt logic -> the clock enable of a context's PC register. This is the X stage; F, D and W are each a fraction of it. kestrel's worst path on the same board was 11.6 ns at IMPL=explore and covered the whole instruction.

## Against kestrel

kestrel runs one program at 75 MHz and CPI 1.039: 72.2 MIPS for 1,899 LUTs. gatling runs four at 100 MHz and CPI 4 each: 100 MIPS peak for 2,281 LUTs -- four harts for 20% more logic, and no wait states, hazards or branch penalty to manage. A single program on gatling runs at 25 MIPS, a third of kestrel's: the barrel pays off when there are four things to do (Barrel Model, section 5).
