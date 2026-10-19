# TASK-028: Two-deep descriptor skid buffer in every scheduler

**Priority:** P2
**Status:** active -- started 2026-10-18
**Owner:** sean galloway

## Why

Owner direction 2026-10-18: with the shared-engine refactor (`SHARED_ENGINES`,
one descriptor engine serving every scheduler of a half), each scheduler always
has a two-deep skid buffer for descriptors, added **in front of** the engine's
per-channel descriptor FIFO (the FIFO stays). It registers the shared 256-bit
descriptor fan-out at each scheduler, and a running channel can hold two more
descriptors -- which absorbs a `desc` for a busy channel at the head of the tile
`desc` intake queue (TASK-027 item 4).

## What to build

1. `rtl/fub/scheduler.sv`: a `gaxi_skid_buffer` (DEPTH 2) on
   `{packet, ext_packet}` between `descriptor_valid/ready` and the FSM, in every
   build (shared or per-channel engines).
2. Channel reset drains it; each entry carries the reset epoch it was written
   in, so a reset too short to drain it cannot run a stale descriptor.
3. `scheduler_idle` stays low while the skid holds a descriptor, so the
   engine and the scheduler never both read idle with work pending.
4. Filelist: `fub/scheduler.f` pulls `gaxi_skid_buffer.f`.

## Done when

- A test shows the skid holding two descriptors behind a running one, and a
  channel reset with descriptors in the skid runs none of them.
- RAPIDS full regression from clean-all green; MAS scheduler chapter updated.

STREAM counterpart: stream TASK-017.
