# Purpose and Geometry

This is the Genesys 2 board harness for the RS(252,236) t=8 Reed-Solomon
codec. The same loop subjects both key-equation solvers — riBM and Euclid —
to a regenerated LFSR pattern that never saw the injected errors, so a
corrected block is proven against a reference rather than against the other
decoder. You drive the whole thing from a laptop over a 115200-baud UART, and
it reports per-block verdicts, bandwidth meters, and a beat-by-beat
comparator when both solvers are present.

The geometry is frozen in `build-loop/rtl/rs_loop_cfg_pkg.sv`: RS(252,236),
4 symbols/beat, shortened so n and k are multiples of the beat. That package
is the single source of the geometry, the UART baud, and the build identity,
so the clock constant and the register map cannot drift apart.

The harness directory moved from `projects/fpga-systems/NexysA7/reed-solomon/`
to `projects/fpga-systems/Genesys2/reed-solomon/` on 2026-10-05. Set
`RS_TARGET=genesys2` to build for the Kintex-7 XC7K325T-2; the default
`nexys_a7_100t` keeps the original names and report layout byte-identical.
The Genesys 2 image matrix is four bitstreams:
`rs_loop_genesys2_{axis_ribm,axis_euclid,axi4_ribm,axi4_euclid}.bit` — two
integration flavours times two solvers, one solver per bitstream.
