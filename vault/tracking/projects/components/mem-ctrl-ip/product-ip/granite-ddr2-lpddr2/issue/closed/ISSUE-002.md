# ISSUE-002: granite "does not come up on the Nexys at 100 MHz" (2026-11-09) -- the host ran the 75 MHz read-path pair; the design was never broken

**Priority:** P1 while open -- the 100 MHz board point is the LiteDRAM comparison the owner asked for (memory-controllers MC-011 step 3 closed the timing).
**Status:** closed 2026-11-09 -- root cause in the host, fixed in the host; the 100 MHz bitstream passes init, write_read and the 128 MB memtest, and the eight-profile characterization ran on it the same morning.
**Owner:** session of 2026-11-09

## What was seen

`make program` then `make run SEQUENCES="init write_read" RUN_ARGS="--controller granite"`
on any granite bitstream built for `GRANITE_SYS_100=1`: the host measures
`clk=100.00MHz`, a7ddrphy read leveling sweeps all 8 bitslips x 32 taps and
finds **no (bitslip, tap) eye**, `init` reports PASS with the leveling
warning, and `write_read` fails **512 / 512 beats mismatched**. The same for
five placements of three designs, including a worktree build believed to be
the 2026-11-02 design that had run at 100 MHz on this board; pumice at 75 MHz,
granite at 75 MHz and LiteDRAM's own 100 MHz bitstream passed on the same
board in the same hour. Filed against the design as "placement / PHY margin
at 400 MT/s"; a day of bitstreams went into the matrix.

## Root cause: the host, not the board and not the RTL

The a7ddrphy's data-versus-valid offset -- `rddata_delay - t_rddata_en`,
the sys cycles between the PHY presenting a read's data and asserting its
valid -- is a property of the **clock plan**: 1 at 50 / 66.67 / 75 MHz,
**0 at 100 MHz (DDR2-400)**. Both values were measured by joint board sweeps
(bring-up 2026-07-21 and pumice ISSUE-012 / ISSUE-015 at 75 MHz; granite
TASK-003's 2026-10-29 entry at 100 MHz: "exactly one clean cell, wrlat 1 /
rden 1 / rddata_delay 1"). The host's defaults were the 75 MHz pair (wrlat 1,
rddata_en 6, rddata_delay 7), and the 100 MHz pair lived in three environment
variables that every 100 MHz run since 2026-10-29 had exported:
`TEST_T_PHY_WRLAT=1 TEST_T_RDDATA_EN=1 TEST_RDDATA_DELAY=1`, plus
`PUMICE_MC_CLK_HZ=100000000` for the JEDEC derivation in the char path. The
2026-11-09 runs did not export them. With the data a whole sys cycle off its
valid, no bitslip and no IDELAY tap can recover it: the sweep probes all 256
cells, finds nothing, and the warning text says "analog read path not
recoverable" -- which is what the matrix then went looking for.

Confirmed on the board at 07:40 the same morning: the committed SKU bitstream
(`ddr2_char_granite_sku100_2026-11-09.bit`, unchanged) under the unchanged host
with the four variables exported -- init PASS, **write_read mismatched=0**,
**memtest PASS 32 / 32 chunks over 128 MB**.

Two further errors in the matrix, recorded so they are not repeated:

- The "source-identical rebuild of c38f80c9e" was not one. `wt_build.sh`
  sourced the MAIN tree's `env_python`, so `REPO_ROOT` and every `$REPO_ROOT`
  in the filelists resolved to HEAD: 566 of the 749 source paths in its build
  log are under `/mnt/data/github/RTLDesignSherpa/`, 183 under the worktree.
  Only the harness top came from c38f80c9e. A worktree build sources the
  worktree's `env_python`, and the build log's path count is the proof
  (`wt_build2.sh`; the true build read 0 main-tree sources, 80 worktree
  sources, WNS +0.004, 39,988 LUT -- it was never needed on the board).
- "The 2026-11-02 host" test drove HEAD RTL with the 2026-11-02 host and
  regmaps, so it tested nothing about the host either.

Nothing in the design, the SKU parameters, the false paths, the timing
budget or the placement was ever implicated. The leads the issue listed (PHY
clock constraints, eye width, write-versus-read split, temperature) were all
downstream of the wrong pair.

## Fix (host, 2026-11-09)

The pair is **derived from the bitstream**, and the environment variables are
overrides for an experiment, not the configuration of a board point:

- `DDR2CharDriver.clk_mhz()` reads `BUILD_CLK_HZ`; `ddr2_char.read_path_offset`
  is the measured table (`>= 90 MHz -> 0, else 1`, unknown clock -> 1);
  `SimpleTest`, `A7Leveling`, `FullCharacterization` and `pumice_char.
  ControllerConfig` default `rddata_delay` to `t_rddata_en + offset`, and
  `ControllerConfig.mc_clk_hz` to the same register (it was a 75 MHz
  constant, so a 100 MHz char run without the export derived tRC 5 where 7
  is needed).
- `A7Leveling.run` sweeps at the derived pair first and, finding no eye, at
  the other offsets (0, 1, 2 above `t_rddata_en`); an eye off the table is
  named with the clock so the table gets extended. The level cache carries
  the pair; a cache from another plan fails its verify and the re-level
  starts from the derived pair.
- The JEDEC timings are derived once from the same clock and written after
  **every** soft reset (`SimpleTest.init`, `reinit_datapath`,
  `A7Leveling._reinit`): the reset reverts the CSRs to the RTL values, which
  are not a configuration (tREFI 1950 = 19.5 us at 100 MHz, 2.5x JEDEC's
  7.8 us; tRTW 6, under the read window). The smoke init and every leveling
  probe used to run on them.
- `[init]` logs the pair, its offset, whether leveling moved it, and the
  timings, so a failing run records what it ran with.
- `_warn_off_diagonal` checks against the plan's offset (it warned, wrongly,
  on every correct 100 MHz write before).

Handbook: `vault/handbook/fpga/cmn-infra/uart-harness.md`, "The read-path
pair follows the clock plan". Unit tests `build-perf/host/test_pumice_master.py`
10 / 10.

## Verification

All on the patched host with nothing in the environment (no `TEST_*`, no
`PUMICE_MC_CLK_HZ`), 2026-11-09:

- `test_pumice_master.py`: 10 passed.
- `ddr2_char_framework/dv/tests`, `make clean-all && make run-all-func`:
  default 226 passed / 2 xfailed (41:42); `CHAR_RESEARCH_CFG=1` 226 passed /
  2 xfailed (47:03). Same counts as before the change; the JEDEC timings are
  now programmed in the smoke and leveling paths and the cocotb loopback
  takes them.
- Board, `make run SEQUENCES="init write_read memtest"`, each ALL PASS with
  `write_read mismatched=0` and `memtest 32/32 chunks clean over 128 MB`:
  - granite sys100 SKU bitstream: `read path: wrlat 1 rddata_en 6
    rddata_delay 6 (offset 0, leveled); jedec tRCD=2 tRP=2 tRAS=5 tRC=7 tWR=4
    tRTP=1 tRRD=2 tFAW=5 tRFC=14 tREFI=780 tCCD=1 tWTR=4 tRTW=20`.
  - granite sys75 SKU bitstream: `rddata_delay 7 (offset 1, leveled); tRAS=4
    tRC=5 tFAW=4 tRFC=11 tREFI=585`.
  - pumice sys75 bitstream: same pair and timings as granite sys75.

The 100 MHz point that yesterday "did not come up" passes on the committed
bitstream with the host deriving the pair from `BUILD_CLK_HZ`.
