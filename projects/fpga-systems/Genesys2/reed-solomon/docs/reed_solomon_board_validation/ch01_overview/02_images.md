# Images and Codec Profile

## Image matrix

Four Genesys 2 bitstreams were built and kept in `stable/reports/`:

| Image | Solver | Bitstream | WNS (ns) | Failing endpoints | Notes |
|-------|--------|-----------|----------|-------------------|-------|
| axis_ribm | riBM | `rs_loop_genesys2_axis_ribm.bit` | +1.072 | 0 | Streaming pipe. |
| axis_euclid | Euclid | `rs_loop_genesys2_axis_euclid.bit` | +0.875 | 0 | Streaming pipe. |
| axi4_ribm | riBM | `rs_loop_genesys2_axi4_ribm.bit` | +1.822 | 0 | Memory-to-memory chain. |
| axi4_euclid | Euclid | `rs_loop_genesys2_axi4_euclid.bit` | +1.431 | 0 | Memory-to-memory chain. |

: Table 1.1: Reed-Solomon Genesys 2 image matrix.

All four images are timing-clean at 100 MHz on the `k325t-2`. The WNS values
were read from the four `stable/reports/genesys2_*/timing_summary.txt` files.

## Codec profile

The geometry is frozen in `build-loop/rtl/rs_loop_cfg_pkg.sv`:

- Code: RS(252,236), t=8, m=8.
- Symbols per beat: 4 (S=4), so a 32-bit beat carries four 8-bit symbols.
- Shortened from the natural 255-symbol RS block so that n=252 and k=236 are
  both multiples of the beat size. A full codeword is 63 beats; the message
  is 59 beats.

The shortening was deliberate: it makes the AXIS datapath line-rate at
63 cycles per block and keeps the AXI4 memory alignment clean. The host reads
`PROFILE` to discover the geometry and `TOPOLOGY` to discover which datapath
and solver are loaded.
