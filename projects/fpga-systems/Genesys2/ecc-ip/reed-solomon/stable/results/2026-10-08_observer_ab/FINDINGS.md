# Observer A/B on the Genesys 2 — utility-ip/misc TASK-003 board leg

**Date:** 2026-10-08. **Board:** Genesys 2, JTAG serial 200300B818A0, UART
FT232R serial AU05X8RM (`/dev/ttyUSB0`). **Flow:**
`projects/fpga-systems/Genesys2/ecc-ip/reed-solomon/build-loop`,
`RS_TARGET=genesys2` (default image: riBM, AXIS datapath, RS(252,236),
BUILD_ID 0x52534C50, single decoder — no comparator by construction).

**Question:** does swapping the `axis4_intf_observer`'s private `gen_tap` for
the shared per-port `axis_monitor_lite` core (RTL commit c35c8304b) change any
board-visible per-iteration observer count on ordinary codec traffic?

**Images (both `rs_loop_genesys2.bit`, sha256 in
`identity_newtap.json` / `observer_ab.json` meta):**

| leg | observer RTL | source tree | bitstream sha256 (first 16) |
|---|---|---|---|
| baseline (old tap) | pre-c35c8304b inline `gen_tap` | HEAD with the observer revert staged, built in `/tmp/task003-oldtap` | `4be2a45ceea1e250…` |
| new | `axis_monitor_lite` per port, OUT_DEPTH=16 | main @ 7addbfca0, built from this repo | `b6938f683f66b599…` |

Both built with the committed `make bitstream RS_TARGET=genesys2`
(2026-10-08; ~5 min each). New-image build: WNS +1.168 ns, 0 failing
endpoints, 21,532 slice LUTs (10.57%), 0 BRAM, 13 DSP.

**Method.** The board lock (`/tmp/rds-board-200300B818A0.lock`) was held
across program + campaigns so the two legs could not interleave reprograms.
Pre-program JTAG identity verified: k325t behind
`200300B818A0B` (record: `identity_newtap.json`). The Nexys A7 (`/dev/ttyUSB5`)
and an unrelated Digilent board (`/dev/ttyUSB3`) shared the USB tree and were
not touched; programming pinned the JTAG target by serial. Campaigns, both run
against each programmed image:

- `task003_rs_matrix.py <tag>` (shared matrix script): 8-block clean codec run
  twice — the second run proves the meters clear with the run. Dumps every
  readable AXIS observer metric per seam: buckets 0-3, bytes 11/12, beats 13,
  packets 14, tap_dropped 15, tap_packets 16.
  → `rs_matrix_oldtap.json`, `rs_matrix_newtap.json`.
- `run_observer_ab.py` (this dir): 16-block clean ×2, e=t (8), e=t+1 (9),
  64-block clean, same full metric readout plus OBS_STICKY.TAP_BLOCKED per
  run. → `observer_ab.json`, log in `logs/board_window.txt`.

## The matrix: baseline vs new, 8-block clean runs

Both runs of each image read identically (per-iteration isolation holds).
Per seam, per class — **old tap → new tap**:

| seam | prod | bp | starv | idle | beats | pkts | bytes | tap_dropped | tap_pkts |
|---|---|---|---|---|---|---|---|---|---|
| msg_in | 472 → 472 | 28 → 28 | 140 → 140 | 0 → 0 | 472 → 472 | 8 → 8 | 1888 → 1888 | 0 → 0 | 8 → 8 |
| cw_out | 504 → 504 | 0 → 0 | 136 → 136 | 0 → 0 | 504 → 504 | 8 → 8 | 2016 → 2016 | 0 → 0 | 8 → 8 |
| cw_in  | 504 → 504 | 0 → 0 | 136 → 136 | 0 → 0 | 504 → 504 | 8 → 8 | 2016 → 2016 | 0 → 0 | 8 → 8 |
| msg_out| 472 → 472 | 0 → 0 | 168 → 168 | 0 → 0 | 472 → 472 | 8 → 8 | 1888 → 1888 | 0 → 0 | 8 → 8 |

**Every per-iteration class count is unchanged.** prod == beats on every seam
both images (meter and tap see the same stream); tap_packets == packets both
images; the 136-cycle fill shows up as starvation on the codeword seams on
both, exactly as the MANIFEST records.

## Extended matrix (new image) vs the committed pre-rework baseline

The pre-rework board baseline for these shapes is the MANIFEST's
board-proven arithmetic (Oct images, pre-c35c8304b): 16-block runs read
944/1008 beats, 64-block 3776/4032, 1,144 / 4,168 cycles, 71.5 / 65.1
cyc/block. New image:

| run | cycles | cyc/blk | msg_in beats/pkts | cw_out | cw_in | msg_out | tap_dropped (all seams) | verdict |
|---|---|---|---|---|---|---|---|---|
| clean 16 ×2 | 1144 | 71.5 | 944 / 16 | 1008 / 16 | 1008 / 16 | 944 / 16 | 0 | PASS, both iterations identical |
| e = t = 8, 16 blk | 2087 | 130.4 | 944 / 16 | 1008 / 16 | 1008 / 16 | 944 / 16 | 0 | PASS (all blocks corrected, exactly e symbols) |
| e = t+1 = 9, 16 blk | 2087 | 130.4 | 944 / 16 | 1008 / 16 | 1008 / 16 | 944 / 16 | 0 | PASS (accounting + data_err evidence) |
| clean 64 | 4168 | 65.1 | 3776 / 64 | 4032 / 64 | 4032 / 64 | 3776 / 64 | 0 | PASS |

Every number matches the committed baseline arithmetic to the digit, and the
datapath timing is unmoved (1144 / 4168 cycles — the MANIFEST's own table).

## tap_dropped (observer stat metric 15)

**0 on both images, every seam, every run** — the acceptance "unchanged
except tap_dropped, which must be lower (target ~0)" is met (0 ≤ 0). The
structural reason it cannot do otherwise on this harness: the RS harness
builds the observer with `ENABLE_MON_TAPS = 0` ("the meters, not the monbus"
— the committed comment at rs_loop_harness.sv:980), so the event cones never
arm, no monbus packets are emitted, and there is nothing to drop. The
two-events-per-cycle queue's real effect — the old tap's priority-shedding
`tap_dropped = 11..13` on the all_classes stimulus falling to 0 — is proven
in the observer cocotb suite (12/12 green at gate/func/full from clean, the
RTL leg of this task). Here the board proves the negative: the swap changed
no count the board can see.

OBS_STICKY.TAP_BLOCKED read 0 after every run on the new image (no drop
since clear), as expected.

## Verdict

**ACCEPT.** Per-iteration monbus-visible class counts are identical between
the pre-rework (gen_tap) and post-rework (axis_monitor_lite) bitstreams on
ordinary, e=t, e=t+1, and 64-block traffic; `tap_dropped` is 0 on both;
codec verdicts all pass; datapath cycles match the committed baseline to the
digit. The observer core swap is board-invisible, as intended.

## Operational notes (for the next board session)

- The hw_server Digilent-probe race bit once during programming: the
  readback enumerated the Nexys A7's a100t but not the Genesys 2's k325t, and
  the identity check refused the program (correctly). A re-run re-enumerated
  clean and programmed. The repo's retry path only covers *fully empty*
  device lists (board.py DEVICELESS_READBACK_ATTEMPTS); a partial
  enumeration that is missing exactly the target's device is refused without
  retry. Worth an ISSUE if it keeps costing program attempts.
- Board identification on this machine: `/dev/ttyUSB0` = Genesys 2 UART
  (FT232R AU05X8RM), `/dev/ttyUSB5` = Nexys A7 (210292BFA3EE),
  `/dev/ttyUSB3` = an unrelated Digilent board (210384B2FB17). The Genesys 2
  JTAG enumerates as target `200300B818A0B` (the `…A0` alias has appeared
  and disappeared between reads — another hw_server enumeration quirk).
