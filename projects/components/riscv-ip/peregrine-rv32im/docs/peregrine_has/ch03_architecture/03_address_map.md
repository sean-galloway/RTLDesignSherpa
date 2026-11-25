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

# Address Map

The address map applies to `peregrine_top`. The cacheless `peregrine_core` has no map: its data port reaches whatever the integrator attaches.

| Range | Target | Cached | Notes |
|-------|--------|--------|-------|
| 0x0200_0000 - 0x0200_FFFF | CLINT (`peregrine_clint`) | No | Decoded by address bits 31:16 = 0x0200 |
| 0x1000_0000 - 0x1FFF_FFFF | Uncached I/O (`peregrine_uc_axi` to the fabric) | No | Board UART and other MMIO; decoded by bits 31:28 = 0x1 |
| Everything else | RAM through amber | Yes (write-back, write-allocate) | Includes `RESET_ADDR` and the test images at 0x8000_0000 |

: peregrine_top data address map

Instruction fetches are not decoded: every fetch goes through the I\$ and its AXI4 read master, whatever the address.

The I/O window is bounded at 0x1FFF_FFFF (PRD P7, amended 2026-11-24) so that the riscv-tests and riscv-arch-test images, which link at 0x8000_0000, stay cacheable. A `tohost` mailbox in the cacheable image therefore lands in amber; the simulation TBs detect it from the store's RVFI retire, not from the fabric.

## CLINT Registers

Offsets from 0x0200_0000, in the SiFive layout:

| Offset | Register | Notes |
|--------|----------|-------|
| 0x0000 | `msip` | Bit 0 drives the machine software interrupt |
| 0x4000 | `mtimecmp` low | Resets to all ones (no timer interrupt out of reset) |
| 0x4004 | `mtimecmp` high | |
| 0xBFF8 | `mtime` low | Counts once every `MTIME_DIV` clocks; resets to 0 |
| 0xBFFC | `mtime` high | |

: CLINT registers

Writes take their byte strobes. Any other offset reads 0 and ignores writes. A write to one half of `mtime` or `mtimecmp` is not atomic with the other half; use the privileged specification's RV32 update sequence. The timer interrupt is registered: it follows `mtime >= mtimecmp` one cycle later.

---

**Last Updated:** 2026-11-25
