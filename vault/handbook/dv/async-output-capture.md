---
title: Capture asynchronous outputs with a background monitor
summary: A test that only looks at an output between stimulus steps misses whatever arrived during them. Run a monitor coroutine for the whole test; a partial capture rate is indistinguishable from an RTL bug.
---

# Capture asynchronous outputs with a background monitor

**If an output can arrive while you are still driving inputs, something must be
watching while you drive them.** Sampling the output between stimulus steps
records a fraction of what the DUT produced, and that fraction reads as a DUT
defect.

## The failure that taught it

The RAPIDS descriptor engine test sent N requests and then went looking for N
descriptors. It found 5 of 12 -- a 42% "success rate" filed against the
descriptor engine. The engine was correct. Descriptors were emitted *during*
the request burst, on cycles when the test was busy driving APB and not
looking. A monitor coroutine running for the whole test took it to 12 of 12.

## The shape

    descriptors = []          # shared; read after the test
    monitor_active = True     # clean shutdown, not a kill

    async def monitor():
        while monitor_active:
            await self.wait_clocks(self.clk_name, 1)
            if int(self.dut.descriptor_valid.value) == 1:
                descriptors.append(int(self.dut.descriptor_packet.value))

    cocotb.start_soon(monitor())
    ...  drive all stimulus  ...
    monitor_active = False
    await self.wait_clocks(self.clk_name, 2)    # let in-flight outputs land

Four things carry the weight: the collection is shared state, the flag gives a
clean shutdown, `start_soon` runs the monitor concurrently instead of
sequentially, and the drain window after the last stimulus lets outputs still
in flight arrive before you assert on the count.

## When

Any interface whose timing is not locked to your stimulus: descriptors,
packets, completions, monbus traffic, and every multi-stage pipeline where
output N does not line up with input N. A strictly synchronous
request/response does not need it.

## The trap underneath

From inside the test, a partial *capture* rate and a partial *emission* rate
look identical. Before filing "only some of them arrive" against the RTL, prove
the observer was watching the whole time -- this is the
[[silent-fallbacks]] shape. And a 70% pass threshold that makes such a test go
green is concealing the defect rather than tolerating it;
`/GLOBAL_REQUIREMENTS.md` 3.3 requires 100%.

Prefer a framework monitor to a hand-rolled loop where one exists -- it already
does this correctly ([[bfm-usage]]).

Related: [[measure-over-the-window]] (sample AT the edge, and window the
metric), [[bfm-usage]], [[silent-fallbacks]].
