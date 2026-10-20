**[← Back to Genesys2](../)** | **[← FPGA Systems Index](../../index.md)**

# Genesys 2 Bridge Stress Model

Silicon validation of the bridge generator's fabrics with nothing else on the
board: every port of a generated bridge is driven by a stress master or
answered by a stress slave, and every byte, ID, response code and burst shape
is checked at both ends.

- **PRD:** [PRD.md](PRD.md) -- why the existing injectors were not reused as-is, the data contract, the checks, the builds and phases.
- **Status:** the AXI4, AXI3 and AXI5 builds (`build-axi4`, `build-axi3`,
  `build-axi5`) pass on the board -- 27/27 runs each, every profile, three
  seeds, plus a 15-minute soak each -- and in simulation. AXI5 covers NSAID /
  TRACE / MPAM / MECID, poison, IDUNQ, atomics and MTE. `build-xil` puts
  third-party IP on the bridge -- LiteDRAM DDR3 and an AMD/Xilinx BRAM controller as real
  memories, the AXI Traffic Generator and AXI Central DMA as masters, a
  protocol checker on each memory link -- and is in bring-up. It has
  found bridge BUG-018 (width converters vs FIXED / WRAP / narrow / unaligned
  bursts, confirmed in silicon), bridge BUG-019 (unaligned INCR steps across
  several converters), converters BUG-010 (every CSR write lands twice) and
  converters BUG-011 (AXI4-to-AXI3 chopping of an unaligned burst, fixed).
