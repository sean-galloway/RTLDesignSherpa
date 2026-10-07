# Purpose and Geometry

This is the BCH(4224,4120) t=8 codec on the Digilent Genesys 2, wrapped in a
UART-controlled loop that runs the same campaigns in cocotb simulation and on
the board. The geometry is frozen in
`build-loop/rtl/bch_loop_cfg_pkg.sv`: GF(2^13), primitive polynomial
`0x201B`, first root `b=1`, `n=4224` shortened from `8191 = 2^13 - 1`,
parity degree `104 = m*t`. The component core defaults to `BITS_PER_BEAT = 8`;
this harness widens the AXI-Stream/AXI4 wrappers to 32-bit beats.

The whole point of the loop is that errors are injected **after** the encoder.
The checker regenerates the expected LFSR pattern independently and compares
it against the decoder's output, so the verdict comes from a reference that
never saw the errors.

The harness directory moved from `NexysA7/` to `Genesys2/` on 2026-10-05.
`BCH_TARGET` still accepts `nexys_a7_100t` as a build option, and since
2026-10-07 the same tree carries a first-class small profile for it (issue
#82): `BCH_PROFILE=small` builds BCH(248,224) t=3 for the A7-100T at 50 MHz
(WNS +7.8 ns, 38% LUT). The Genesys 2 remains the primary target for the full
profile: the k325t-2 has the room and timing margin to hold the full
BCH(4224,4120) loop at 100 MHz with both AXIS and AXI4 flavours, and both
images came out timing-clean on the board build with positive slack.

Two bitstreams are built: `bch_loop_genesys2_axis.bit` and
`bch_loop_genesys2_axi4.bit`. The AXIS flavour is a single streaming pipe; the
AXI4 flavour is a memory-to-memory job chain across four AXI4 memories. The
AXI4 flavour refuses runs whose `GEN_BLOCKS` exceed the job-memory capacity
rather than letting regions wrap, so long soaks belong on the AXIS image. The
host reads `TOPOLOGY` to discover which datapath is loaded, so the same
campaign scripts drive both without a command-line flag.
