# Locking and identity

Two mechanisms, and they are complements rather than alternatives: **a lock
prevents a collision, a readback detects one that happened anyway.**

## The lock

`board_lock.sh` is a command prefix:

```sh
board_lock.sh --board nexys_a7_100t -- make program
```

It resolves the board's JTAG serial through `fpga_board.py serial`, falls back
to the board name when there is none, sanitises the result, and takes a
non-blocking `flock` on `$RDS_BOARD_LOCK_DIR/rds-board-<key>.lock` (default
`/tmp`). On conflict it prints a hint and exits **98**; otherwise it `exec`s the
payload.

**Keyed on the JTAG serial, not the build directory.** Two different build
directories drive the same physical board, so a build-keyed lock lets them
collide while reporting success. Two boards sharing one JTAG chain still get
separate keys, because their serials differ.

The lock is held for the life of the payload: `exec 9>` the lock file, `flock -n 9`,
then `exec` the command. The descriptor survives `exec`, the lock lives on the
open file description, and the kernel releases it when the process dies --
including when it is killed.

A consequence worth knowing: a Python `BoardLock` nested inside a shell-locked
payload would be refused by the kernel, since the tree already holds the lock.
The Python side therefore detects an inherited descriptor and re-locks to prove
ownership; an adopted descriptor is never closed on exit.

## Why a lock is not sufficient

A harness records the sha256 of the bitstream **it** programmed. That describes
the file it sent, not the device that received it. If a board is reprogrammed or
re-enumerates mid-run, the results file carries no error, no timeout and no
mismatch -- it is simply someone else's measurements under your name.

`fuser /dev/ttyUSB*` does not close this gap either: it sees only the UART half
of a board. Measured on this bench, the Genesys 2's JTAG serial appears on
**zero** tty nodes.

## The identity readback

`jtag_readback.tcl` lists the chain read-only. `parse_readback` turns its output
into targets and devices, and is pure, so it is unit-testable without Vivado and
without a board.

`identity_verdict()` returns the check as data and never raises:

| Status | Meaning | Effect on `program` |
| --- | --- | --- |
| `verified` | This board is on the chain with a device behind it | Proceed |
| `wrong` | The chain does not hold this board | **Refuse** |
| `inconclusive` | The chain could not be read | Warn, proceed |
| `unjudged` | This board has no registry serial | Proceed |
| `skipped` | `--no-verify-identity` was passed | Proceed |

**The asymmetry is deliberate.** A proven wrong chain refuses. An inconclusive
readback only warns, because refusing when `hw_server` is unreachable would
break every flow where programming works but the daemon is not running -- and
this sits on thirteen board paths at once. A board with no registry serial is
returned `unjudged` rather than passed; claiming success there would be a
checker that cannot fail.

A wedged `hw_server` is `inconclusive`, not an exception: the readback carries a
240 s timeout, and letting `TimeoutExpired` escape would take `program` down,
converting the warn-only path into the refusal the asymmetry exists to avoid.

## The record

A warning printed to a terminal is indistinguishable from a pass once it
scrolls. So the verdict is written beside the evidence:

```
fpga_board.py program --bitstream top.bit --identity-json run/identity.json
```

```json
{
  "when": "2026-09-30T14:22:05-0700",
  "board": "nexys_a7_100t",
  "expected_serial": "210292BFA3EE",
  "bitstream": "/abs/path/top.bit",
  "bitstream_sha256": "...",
  "programmed": true,
  "identity": {"status": "verified", "detail": "", "chain": {...}}
}
```

Two fields exist for reasons that are easy to miss:

- **`programmed`** -- the record is written on the refusal path too, where the
  sha256 describes a bitstream that never reached the device. Without this flag
  the file reads as "this bitstream is on that board", which is exactly the
  false claim the mechanism exists to prevent. It is also false on a non-zero
  Vivado exit.
- **`identity.status` including `skipped`** -- `--no-verify-identity` still
  writes the file. A missing file is not a statement; it is an absence a harness
  tolerates without noticing.

Without this record a run that could not look writes exactly what a run that
looked and approved writes, and six weeks later nobody can tell which one they
are holding.

## Status

The hardware path is **unexercised**. The parser and the decision logic are
covered by hardware-free tests, deliberately, because opening the hardware
manager to test this would violate the very lock discipline it accompanies. The
first real `make program` on a free board remains the outstanding verification;
see tooling TASK-022.
