**[← Back to Genesys2](../)** | **[← FPGA Systems Index](../../index.md)**

# Genesys 2 Bridge Stress Model

Silicon validation of the bridge generator's fabrics with nothing else on the
board: every port of a generated bridge is driven by a stress master or
answered by a stress slave, and every byte, ID, response code and burst shape
is checked at both ends.

- **PRD:** [PRD.md](PRD.md) -- why the existing injectors were not reused as-is, the data contract, the checks, the builds and phases.
- **Status:** phase 1 (AXI4) passes on the board -- 27/27 runs, every
  profile, three seeds -- and in simulation. It has found bridge BUG-018
  (width converters vs FIXED / WRAP / narrow / unaligned bursts, confirmed in
  silicon) and converters BUG-010 (every CSR write lands twice).
