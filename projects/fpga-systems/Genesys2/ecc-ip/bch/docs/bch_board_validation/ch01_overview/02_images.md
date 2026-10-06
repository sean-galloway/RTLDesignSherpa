# Images and Codec Profile

## Image matrix

Two Genesys 2 bitstreams were built and kept in `stable/reports/`:

| Flavor | Bitstream | WNS (ns) | Failing endpoints | LUTs | Notes |
|--------|-----------|----------|-------------------|------|-------|
| AXIS | `bch_loop_genesys2_axis.bit` | +0.586 | 0 | 39,953 | Streaming pipe; used for the million-block soak. |
| AXI4 | `bch_loop_genesys2_axi4.bit` | +0.493 | 0 | 47,490 | Memory-to-memory chain; refuses runs that exceed job memory. |

: Table 1.1: BCH Genesys 2 image matrix.

Both images are timing-clean at 100 MHz on the `k325t-2`. The WNS values were
read from `stable/reports/genesys2_axis/timing_summary.txt` and
`stable/reports/genesys2_axi4/timing_summary.txt`.

## Codec profile

The geometry is frozen in `build-loop/rtl/bch_loop_cfg_pkg.sv`:

- Code: BCH(4224,4120), t=8, m=13.
- Shortened from n=8191 so the codeword fits the target block size.
- Parity: 104 bits.
- Beat width: 32 bits (4 symbols per beat).

The AXIS flavour streams a full codeword in `ceil(4224/32) = 132` beats; the
AXI4 flavour moves the same codeword through job memories. The host reads
`PROFILE` to discover the geometry and `TOPOLOGY` to discover which datapath is
loaded, so the same campaign scripts drive both images without a command-line
flag.
