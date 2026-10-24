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
  several converters), bridge BUG-023 / BUG-024 (two crossbar W-routing
  hangs the BUG-018 fix exposed), converters BUG-010 (every CSR write lands
  twice) and converters BUG-011 (AXI4-to-AXI3 chopping of an unaligned
  burst). All are fixed; every build passes 30/30 on the board with no path
  limits (2026-10-22). `build-mixb` puts every single-beat protocol the
  bridge builds on it at once -- AXI4-Lite, AXI5-Lite, APB4, APB5 and WB4
  masters and slaves beside an AXI4 pair -- and found converters BUG-014
  (an AXI-Lite-to-wide write converter that waited for AWREADY before
  WVALID) and BUG-015 (sub-word bursts into APB misaddressed); fixed, and
  30/30 on the board (2026-10-24).
