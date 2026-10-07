# pumice DDR2 board characterization — findings (2026-07-08)

Board: Nexys A7 (xc7a100t), MT47H64M16 x16 DDR2, bitstream = timer-fix build
(ddr2_char.bit 2026-07-08 05:08). Harness UART /dev/ttyUSB2. clk 100 MHz.
Host: pumice_char measure() (timer-based bandwidth = hardware w_last-w_first).

## Board is healthy (config, not regression)
- Read leveling finds a clean eye ONLY at **t_phy_wrlat=0** (bitslip 0, taps
  0..11, centred tap 5). The `--char`/`--simple`/`A7Leveling` DEFAULT is
  t_phy_wrlat=4, which breaks the WRITE -> "no passing tap". Board cfg:
  t_phy_wrlat=0, t_rddata_en=6, rd_phase=0, rddata_delay=8, cmd_delay=1.

## Headline throughput result
- **~12.7 MB/s read AND write, ~2% of DDR2 peak (~600 MB/s).**
- **FLAT across everything**: incremental == row_major == col_major ==
  col_major_interleaved (page-penalty 99.8%), CLOSE == OPEN page policy,
  and **bl=1 through bl=64 are all exactly 12.7 MB/s**.
- Burst length giving zero gain => **no intra-burst pipelining/batching**;
  the system moves ~1 AXI beat per ~63 sys cycles regardless.
- Interpretation: consistent with pumice running a fully-serialized close-page
  path (each 8-byte AXI beat -> one x16 BL4 DRAM command -> ACT+CAS+PRE, one
  outstanding, deep return latency ~ rd_lat 3063 cyc). BUT see caveat.

### CAVEAT — generator vs controller not yet separated
The bus-meter util is observation-latency-dominated at these run sizes
(util_reliable=False), so the prod/bp/starv buckets can't cleanly attribute the
12.7 MB/s to pumice vs the axi4_master pattern generator. The timer bandwidth is
real (hardware), but WHICH block caps it is unresolved. **The LiteDRAM drop-in
(same pattern generator + taps) is the definitive test:** if LiteDRAM also caps
~12.7 -> generator; if LiteDRAM >> 12.7 -> pumice. (LiteDRAM did 300 MT/s memtest
on this board, so a large gap is expected.)

## Bugs surfaced
1. **Read engine WEDGES at ~4790 transactions.** All families: rd_done never
   asserts past ~4790 completions (txn 6144/8192 both stop ~4783-4790). Hard
   ceiling on sustained reads. Real bug.
2. **Intermittent data mismatches at scale** (3-11 beats per few thousand txn;
   clean at txn<=1024). Marginal read capture or a scale-dependent path bug.
3. **col_major stride overflow**: stride=16 KB x txn>8192 exceeds the 128 MB
   DRAM -> address alias -> mismatch. Bound col_major txn<=8192 (host-side).

## Config axis appears INERT on this bitstream
- synth_mask_obs=0, lookahead_max_obs=0 (both are echoes of harness-driven
  CTRLR_CAP inputs, which init never sets). page_policy_or / scheme_or writes
  produce identical numbers (12.7, rd_lat 3063.8) -> either the override muxes
  aren't synthesized in this build, or CTRLR_CAP must advertise the capability
  first. Needs: set_controller_cap(cap_lookahead_max, cap_synth_mask=0x3) in
  init + verify the char macro synthesizes the scheme/page/reorder features.

## Code gaps to fix (host)
- Expose t_phy_wrlat in the --char/--simple CLI (or default to 0 for this board);
  pumice_char ControllerConfig.t_phy_wrlat should be 0 for board runs.
- Wire set_controller_cap() into the char init so the config axis is live.
- Guard col_major txn against DRAM-size overflow.

## LiteDRAM reference on the SAME board (pre-built LiteX memtest SoC)
Flashed /tmp/litex_nexys_ddr2/gateware/nexys_ddr2.bit (BIOS UART /dev/ttyUSB2):
- SDRAM: 128 MiB 16-bit @ **300 MT/s CL-3 CWL-2** -> DRAM/PHY peak ~600 MB/s.
- Read leveling OK, Memtest OK (integrity clean).
- **Memspeed (sequential, 2 MiB): Write 25.3 MiB/s, Read 34.0 MiB/s.**

IMPORTANT: that 25-34 MiB/s is the LiteX **VexRiscv CPU/cache-bound `mem_speed`**,
NOT LiteDRAM's controller ceiling (BIOS has no hardware-BIST command in this
build). So it's a CPU-path reference, not a fair controller-vs-controller number.

## Comparison so far
| path | MB/s | notes |
|---|---|---|
| DDR2/PHY peak (this board) | ~600 | 300 MT/s x16, proven by LiteDRAM |
| LiteDRAM, CPU mem_speed | 25-34 | CPU/cache-bound, not controller |
| pumice, pattern-gen (board) | 12.7 | flat across pattern/config/bl |
| pumice, pattern-gen (sim, 0-lat mem) | 51-71 | digital gen+pumice max |

Takeaways:
- Both controllers sit FAR below the 600 MB/s DRAM peak by their measured paths.
- pumice (12.7) is ~2-3x behind LiteDRAM's easy CPU path, and its **flat-vs-
  burst-length** signature is the specific weakness: no intra-burst pipelining /
  batching — each AXI beat is a serialized ACT+CAS+PRE round-trip.
- The DEFINITIVE controller-vs-controller number still needs the apples-to-apples
  harness (our pattern-gen -> LiteDRAM AXI port, same taps): blocked on riscv-gcc
  (no root; distro pkg needs sudo) for the self-init BIOS, then a Vivado build.
  Network is up, so a prebuilt root-free toolchain (xpack riscv-none-elf) is a
  viable fetch.

## #1 fix indicated for pumice
Pipeline/batch beats within an open page + allow multiple outstanding DRAM
commands. The bl=1..64 -> 12.7 flat proves the datapath serializes per-beat.
