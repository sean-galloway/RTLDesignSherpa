---
title: A blocking send() deadlocks a DUT that waits for something else first
summary: GAXI/AXIS master send() returns only after the beat is accepted. When the DUT holds ready until a later stimulus arrives (a descriptor, a kick), "send the data, then send the command" hangs forever. Drive the data from a background task and keep an explicit wait for acceptance.
---

# A blocking send() deadlocks a DUT that waits for something else first

**`await master.send(pkt)` completes when the DUT takes the beat.** If the
DUT will not take it until a stimulus the test sends *afterwards* has
arrived, the test never reaches that stimulus. Nothing errors; the cocotb
timeout fires with the DUT sitting in reset-clean idle.

## The failure that taught it

The byte-granular RAPIDS sink (rapids TASK-019) cannot place a stream's
bytes until the scheduler has fetched the descriptor that says where they
go, so `s_axis_tready` stays low until the channel's packet record arrives.
Every beat-era sink test did "stream the packet into the buffer, then send
the descriptor" -- fine on the beats design, which buffered blind. On the
byte design the first `await send()` waited for a `tready` that only the
descriptor would raise. Four TB classes (two macro, two top) had the same
shape; each deadlocked identically. `send()` (RDS-DV `GAXIMaster.send`) is
`_driver_send(sync=True)` followed by a wait on `transmit_coroutine`, so
the blocking is by design, not a bug to fix there.

## The shape

    async def send_axis_packet(self, channel, beats, strbs=None):
        """Return once the packet is IN FLIGHT, not accepted."""
        task = cocotb.start_soon(self._drive_axis_packet(channel, list(beats), strbs))
        self._axis_tasks.append(task)
        await self.wait_clocks(self.clk_name, 1)
        return task

    async def wait_axis_sent(self, timeout_cycles=20000) -> bool:
        for _ in range(timeout_cycles):
            if all(t.done() for t in self._axis_tasks):
                return True
            await self.wait_clocks(self.clk_name, 1)
        return False

The test that needs acceptance itself (a count, an ordering claim) awaits
`wait_axis_sent()` -- explicitly, with a bound, so a DUT that never takes
the data still fails with a reason instead of hanging.

## Rules

- Before writing "send A, then send B", ask what the DUT needs before it
  will accept A. If the answer is B, A goes in the background.
- A background driver must be **bounded and observable**: keep the task
  handles, and give the test a way to wait for them with a timeout.
- The same DUT contract belongs in the block's CLAUDE.md area facts
  ("issue the descriptor first, or stream concurrently"), because the
  next TB author will write "send A, then send B" too.

Related: [[bfm-usage]] (the BFMs' handshake semantics), [[async-output-capture]]
(the mirror case: an output that arrives while you drive).
