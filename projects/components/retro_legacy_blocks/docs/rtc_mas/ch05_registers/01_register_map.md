<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# APB RTC - Register Map

## Overview

The register block is thirteen 32-bit registers at 0x00-0x30, and exactly those thirteen addresses are decoded. Everything else in the 4 KB window — the reserved slots at 0x34-0x3C as much as anything above 0x3F — is dropped: the write is ignored, the read returns 0, and the access answers with PSLVERR. Nothing aliases. 0x40 is not a second RTC_CONFIG and 0x864 does not reach RTC_ALARM_SEC.

A few behaviors worth knowing before you program this thing. The counters advance on the divider rollover edge; the tick is raised on that same edge and marks the new second, and the alarm compare is made against that new second — the time that becomes readable on the tick — so the alarm asserts at the moment the readable time equals the programmed value, never one second later: an alarm set for hh:mm:ss reads back as hh:mm:ss when `alarm_flag` sets. A read reflects a tick about 3-4 pclk cycles after it happens. With clock_select=1 (test mode) the tick rate is pclk/100, not 1 Hz.

The six time registers are answered from a pclk-domain shadow of the counters, never from the counters themselves, and the shadow only ever takes a complete, coherent time. The register file and the counters are on different clocks; every path between them is one of the four crossings described in ch01, and none of them is a raw sample.

## Register Summary

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x00 | RTC_CONFIG | RW | 0x00000000 | Global configuration (enable, hour/BCD/clock mode, time-set) |
| 0x04 | RTC_CONTROL | RW | 0x00000000 | Alarm and interrupt enables |
| 0x08 | RTC_STATUS | RO/W1C | 0x00000000 | Status flags, commit timeout and indicators |
| 0x0C | RTC_SECONDS | RW | 0x00 | Seconds (0-59) |
| 0x10 | RTC_MINUTES | RW | 0x00 | Minutes (0-59) |
| 0x14 | RTC_HOURS | RW | 0x00 | Hours (0-23, or 1-12 + PM in 12-hour mode) |
| 0x18 | RTC_DAY | RW | 0x01 | Day of month (1-31) |
| 0x1C | RTC_MONTH | RW | 0x01 | Month (1-12) |
| 0x20 | RTC_YEAR | RW | 0x00 | Year (0-99, base 2000) |
| 0x24 | RTC_ALARM_SEC | RW | 0x00 | Alarm seconds match value |
| 0x28 | RTC_ALARM_MIN | RW | 0x00 | Alarm minutes match value |
| 0x2C | RTC_ALARM_HOUR | RW | 0x00 | Alarm hours match value |
| 0x30 | RTC_ALARM_MASK | RW | 0x00 | Alarm field match enables |

All registers are 32 bits wide. In each register only the low bits listed below
are implemented; the remaining bits are reserved (read as 0).

---

## RTC_CONFIG (0x00)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | rtc_enable | RW | 0 | Master enable for the RTC (0=disabled, 1=enabled). Reads 0 after a presetn reset, but the counter domain keeps its run state until RTC_CONFIG is written again |
| 1 | hour_mode_12 | RW | 0 | Hour format: 0=24-hour, 1=12-hour (AM/PM) |
| 2 | bcd_mode | RW | 0 | Time format: 0=binary, 1=BCD |
| 3 | clock_select | RW | 0 | Time-counter clock: 0=32.768 kHz, 1=system clock (test). Change only with rtc_enable=0. The mux select is held in a flop under rtc_resetn; a presetn reset cannot switch the counter clock |
| 4 | time_set_mode | RW | 0 | 1=stage a new time (pauses the divider and the counters once the counter domain samples it), 0=normal operation; the 1-to-0 edge commits |
| 31:5 | Reserved | RO | 0 | Reserved |

Note that `hour_mode_12` and the format/clock controls live here, not in
RTC_CONTROL. Out of reset the counters run in **binary** mode; BCD is optional
and is selected by setting `bcd_mode`. The mode bits, like the alarm values,
cross to the counter domain through a three-flop synchronizer and a
two-identical-samples filter, and take effect about five counter clocks after
the write (three for the chain, two for the filter to see the same word twice). The filter rejects a torn word, so one RTC_CONFIG write lands as
the word that was written; but each register write lands on its own, so a
sequence of writes is seen one at a time; change `hour_mode_12` and `bcd_mode`
with the alarm disabled (or the RTC disabled), then enable.

`clock_select` drives a plain combinational clock mux, and the divider target
depends on it too. Change it only with `rtc_enable` low; flipping it while
the RTC runs can produce a runt clock pulse, and a runt on the counter clock
can leave an in-flight commit unacknowledged until `commit_timeout` reports
it. Around an `rtc_resetn` pulse the select flop itself moves the mux twice
(it clears on assert and reloads after release), so the counter domain's
reset release is held until the select has been stable for three pclk; the
counter domain never comes out of reset across a mux switch. That hold is a
one-shot per `rtc_resetn`: a live write of `clock_select` does not touch the
counter reset (it would wipe the time of day, and the mux has already moved
by the time a gate could react), which is why the change-only-with-
`rtc_enable`-low rule stands.

A `presetn` reset keeps the clock. The counter domain holds its run/enable
state and its clock source across a `presetn`-only reset: RTC_CONFIG reads
its reset value afterwards, but the counter domain applies a crossed
configuration — `rtc_enable`, `clock_select`, the hour and BCD mode bits, the
alarm fields and the alarm enable, everything in the crossed bundle — only
after software has written RTC_CONFIG: a config-valid flag, set by any
RTC_CONFIG write and cleared by `presetn`, crosses inside the same 34-bit
bundle as the values it qualifies, and the counter domain loads its held
copy only from a word that two consecutive samples of the synchronizer agree
on and whose own valid bit is set — so the counters keep counting in the
mode they were set in rather than switching encoding under a running count,
and the valid bit can never be seen ahead of the fields it qualifies. One
field is deliberately not held: `time_set_mode`. It is a transient control,
not configuration, and it is taken live from the crossing, so a `presetn`
that lands while a time is being staged releases the divider pause on its
own, with no register write required; the staged time is dropped (no commit
is generated) and the clock simply keeps running. The mux select is held in
a flop under `rtc_resetn`, so `presetn` cannot switch the counter clock.
Until that write timekeeping continues exactly as before: the time is still
correct after a bus reset and `time_valid` remains as it was. The counters
are, however, still formatting the time with the BCD and 12-hour settings
from the hold while RTC_CONFIG reads 0 — the register file and the counter
domain disagree about the format — so do not read the time until RTC_CONFIG
has been re-written. Software re-writes RTC_CONFIG to re-establish its
configuration.

### Setting the time (time_set_mode protocol)

Outside of time-set mode the six time registers mirror the counter shadow, so
a plain write to RTC_SECONDS..RTC_YEAR is overwritten by the live time on the
next update. To set the time:

1. Write RTC_CONFIG with `time_set_mode = 1`, and the desired `hour_mode_12`
   and `bcd_mode`. The six time registers stop mirroring the counter: they
   are staging registers now. Once the counter domain samples the bit —
   about three counter clocks, ~90 us at 32.768 kHz — the divider and the
   counters pause: no tick, no second interrupt, no alarm evaluation, no
   counter advance. `rtc_enable` does not need to be set for the commit to
   land.
2. Write RTC_SECONDS, RTC_MINUTES, RTC_HOURS, RTC_DAY, RTC_MONTH and RTC_YEAR,
   in any order, at any speed. Each write lands in its own register and
   nothing crosses to the counter domain yet, so back-to-back writes cannot
   lose a field and an individual write never loads a partial time. Reading
   a time register in this window returns the staged value.
3. Write RTC_CONFIG with `time_set_mode = 0`. That falling edge is the
   commit: all six bytes cross to the counter domain as one four-phase
   request/acknowledge transfer and load the counters on a single
   counter-clock edge. The load restarts the divider, so the first tick
   after a set comes exactly one divider period after the load — 32768
   counter clocks in production, 100 in `clock_select=1` test mode — the
   same as every steady-state second.

The commit takes about five counter clocks to land — roughly 150 us on a
32.768 kHz crystal — and until the loaded time is visible in the pclk shadow
the six registers keep returning the staged values, so a readback in that
interval shows the time you asked for rather than the pre-commit time;
`RTC_STATUS.pm_indicator` follows bit 7 of the staged hours for as long as
the staged values are the ones being read. Busy low means one of two
things, and `commit_timeout` tells them apart: with `commit_timeout` clear,
the committed time has landed in the counters and is visible in the shadow
(the release requires evidence that the load happened since this commit was
accepted, a load pulse synchronized back into pclk, not merely that the
staged bytes match what the shadow already showed); with `commit_timeout`
set, the commit's window expired and busy was released while the commit is
still held — committing the time the clock
already shows cannot release busy before the load, so a reader polling busy
never sees the time step backwards. A `presetn` pulse while busy is set
clears the register file, so the six time registers read their reset
defaults — not the staged values — until busy clears and the mirror resumes
with the committed time; `RTC_STATUS.time_valid` reads 0 for that window
and is the signpost. There is no separate commit
register; the falling edge was chosen so the published map did not change.

If the counter clock is not running the acknowledge does not arrive. A commit
that is not acknowledged within `COMMIT_TIMEOUT_CYCLES` pclk (a parameter,
default 65535, about 655 us at 100 MHz) sets `RTC_STATUS.commit_timeout`
(sticky, W1C) and releases
the register mirror — the six time registers go back to showing the shadow —
but the transfer is held: its data stays on the request side and it lands,
unchanged, whenever the counter clock returns. `commit_timeout` therefore
means "not acknowledged in time; read the time back to see whether it
landed", not "the time was not set". The report stands while the stall is
outstanding: it clears on W1C, or by itself once the stalled commit finally
completes, so a bit that reads 1 always means a commit is still
unacknowledged. The flag follows the transfer it reports: it is reset by
the synchronized `rtc_resetn` together with the rest of the commit
bookkeeping, not by `presetn`, so a bus reset during a stall leaves the
report standing while the stall is outstanding, and an `rtc_resetn` that
drops the stalled transfer clears the report with it, without a W1C. The
release is by the timeout event of
the transfer that timed out, never by a persisting timeout condition: a
commit issued while a timed-out transfer is still pending keeps its staged
values visible and the commit path busy until it lands, after the pending
one, and does not itself report a timeout unless it also exceeds the window.
That window is the queued commit's own: a watchdog counted from its commit
pulse while it waits to be accepted, so a retry queued behind a link that
never returns (a dead crystal) reports `commit_timeout` again after
`COMMIT_TIMEOUT_CYCLES` and releases busy and the mirror, while staying
queued to land when the clock returns — busy cannot hang and a stall cannot
go unreported however many times software retries. Nothing is delivered
twice. A stall is always reported, though:
`commit_timeout` sets when the in-flight transfer exceeds the window even if
a retry has been queued behind it, and the queued commit keeps busy and its
staged values and lands after the stalled one when the counter clock
returns. Busy never drops while a transfer is pending and inside its own window: a
commit accepted in the very cycle the previous timed-out transfer returns to
idle keeps busy and its staged values until it lands or its own window expires, and no timeout is
reported for a transfer that completed. `commit_timeout` never sets itself:
the bit sets only when a commit issued by software exceeds the window, so a
`presetn` pulse — at any time, including during a stall — cannot produce a
commit_timeout event after release. For the integrator,
`COMMIT_TIMEOUT_CYCLES` must exceed the ten or so counter clocks a commit
needs at the slowest pclk:rtc_clk ratio, about 30500 pclk at 100 MHz against
32.768 kHz; the default is roughly twice that. A value of 0 disables both
watchdogs (the in-flight one and the queued commit's), and then a commit on a
dead counter clock holds busy and the staged values until the clock returns.

The handshake is four-phase rather than a toggle because the two domains
reset independently: a toggle keeps its state as parity on both sides, and a
one-sided reset would fabricate a transfer. The handshake's source side is
reset by `rtc_resetn` alone (synchronized into pclk), never by `presetn`
alone — `rtc_resetn` is synchronized into pclk for that purpose. So a
`presetn` reset alone clears the register file and the bus-side state but
keeps the clock: the counter domain holds its run/enable state and its
clock source, timekeeping continues exactly as before, and the crossed
enable and clock select are applied again only once software has written
RTC_CONFIG. Any commit already in flight lands intact, never as zeros, and
no stale acknowledge can complete a later commit early. Nor does a warm bus
reset abort a commit software issued before it: a queued commit still lands
with the data captured at its commit pulse, so the time can change shortly
after a bus reset because of a request that predates it. The completion
evidence shares the bookkeeping's reset — the destination sides of the
snapshot and tick synchronizers reset only with the synchronized
`rtc_resetn` — so a `presetn` pulse can neither destroy nor fabricate a
snapshot pulse: busy always clears once a commit lands, the register file
never publishes a pre-commit time as the answer to a commit, and `presetn`
release cannot manufacture a `second_tick` or `alarm_flag` event.
An `rtc_resetn` reset alone returns the counters to the reset default and
resets the commit link on both sides, so a commit that was still
unacknowledged when it asserted is dropped and software must re-issue it; a
commit issued after the reset works normally, and a commit that already
landed is not replayed. The bus-side commit bookkeeping — pending, busy and
the timeout event detector — is reset by either `presetn` or the
synchronized `rtc_resetn`, the same term that resets the handshake's source
side, so a commit staged while `rtc_resetn` is held low is dropped cleanly:
busy does not hang, no timeout is reported for it, the counters read the
reset default after release, and software re-issues the commit.

The pause while the time is staged is best effort at the production ratio.
`time_set_mode` reaches the counter domain through the 3-flop config
crossing, so the divider and the counters pause — no `second_tick`, no
second interrupt, no alarm evaluation, no counter advance — only if the bit
is held long enough for the counter clock to sample it, about three counter
clocks (~90 us at 32.768 kHz). A sub-microsecond staging window is not seen
and the clock keeps running until the commit replaces the time. The commit
does not depend on the pause: it brackets the tick, so the counters never
take two updates on consecutive counter clocks, the readable time after the
commit is exactly the committed time, and the first tick after it comes
exactly one divider period after the load, the same as every steady-state
second.

### Reading the time (coherent burst)

Read the time as the burst RTC_SECONDS, RTC_MINUTES, RTC_HOURS, RTC_DAY,
RTC_MONTH, RTC_YEAR — seconds first. A read of RTC_SECONDS returns the live
shadow seconds and, in that same cycle, latches minutes, hours, day, month,
year, `pm_indicator` and `time_valid`, so the reads that follow belong to the
same instant as the seconds value and a tick landing in the middle of the
burst cannot produce a mixed answer. There is nothing to open or close and
nothing times out: the five latched registers simply hold what the most
recent seconds read captured, for as long as it takes, until the next
seconds read replaces it.

RTC_SECONDS itself is never latched, so polling it alone in a tight loop
returns the live seconds every time. Minutes through year always return the
values latched by the most recent seconds read — reading one of them without
a preceding RTC_SECONDS read gives whatever the last seconds read captured,
however long ago, which is why software reads seconds first.
`RTC_STATUS.pm_indicator` and `time_valid` are latched with the five, so the
hours and the PM bit read inside one burst belong to the same second. The
time you read is the time as of the last second boundary, 3-4 pclk after
that boundary.

---

## RTC_CONTROL (0x04)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | alarm_enable | RW | 0 | Enable alarm comparison |
| 1 | alarm_int_enable | RW | 0 | Enable interrupt on alarm match |
| 2 | second_int_enable | RW | 0 | Enable interrupt every second (1 Hz tick) |
| 31:3 | Reserved | RO | 0 | Reserved |

The interrupt outputs are levels: `rtc_alarm_irq` is `alarm_flag AND
alarm_int_enable`, `rtc_second_irq` is `second_tick AND second_int_enable`.
Clearing the flag drops the interrupt.

---

## RTC_STATUS (0x08)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | alarm_flag | W1C | 0 | Alarm triggered; write 1 to clear |
| 1 | second_tick | W1C | 0 | 1 Hz tick occurred; write 1 to clear |
| 2 | time_valid | RO | 0 | Set once the counters have been loaded by a time-set commit or have ticked at least once — a never-programmed RTC reports valid one second after enable, counting from the reset default 2000-01-01. Latched by the RTC_SECONDS read along with minutes through year. Not disturbed by a presetn reset: the counter domain keeps running, so the time and this bit are as they were |
| 3 | pm_indicator | RO | 0 | 12-hour mode: 0=AM, 1=PM. Mirrors RTC_HOURS bit 7; valid in both binary and BCD counting, reads 0 in 24-hour mode. Latched by the RTC_SECONDS read along with minutes through year; while time_set_mode is set it reflects bit 7 of the staged hours |
| 4 | commit_timeout | W1C | 0 | A time-set commit was not acknowledged by the counter domain within COMMIT_TIMEOUT_CYCLES pclk (default 65535; counter clock not running). The transfer is held and lands, unchanged, when the counter clock returns — read the time back to see whether it has. Sets only when a commit issued by software exceeds the window; a presetn pulse cannot produce it after release. Write 1 to clear. The bit reports an outstanding stall: it is cleared by W1C, and it retires itself when the commit that finally lands from that slot completes (a retry that replaced the stalled one included). Reset by the synchronized rtc_resetn with the rest of the commit bookkeeping, not by presetn: a bus reset during a stall leaves the report standing, and an rtc_resetn that drops the stalled transfer clears it |
| others | Reserved | RO | 0 | Reserved |

`alarm_flag` and `second_tick` are sticky flags held in the pclk domain. Each
is set by a single-cycle event: the counter-domain tick and match levels are
one counter clock wide (about 30 us on a real crystal), and they are
synchronized and edge-detected in pclk before they touch the flag, so a wide
source level cannot re-arm a flag one cycle after software cleared it. A W1C
that lands in the same cycle as a new event leaves the flag set — set wins
over clear, so an interrupt is never silently dropped — and the register
mirror follows the flag in the same cycle as the clear, so a read after the
W1C sees the flag low. The synchronizers' destination sides reset with the
synchronized `rtc_resetn`, not `presetn`, so a `presetn` release cannot
manufacture a `second_tick` or `alarm_flag` event — a flag seen after a bus
reset is a tick or a match that actually happened.

---

## RTC_ALARM_HOUR (0x2C)

RTC_ALARM_HOUR is compared as the full byte against RTC_HOURS. In 12-hour
mode that means bit 7 is the PM flag and must be programmed along with the
1-12 hour in bits 6:0: 3 PM is 0x83 in binary and 0x93 in BCD, while 0x03
and 0x13 are 3 AM. In 24-hour mode bit 7 is 0 on both sides.

The alarm values and mask cross to the counter domain as one quasi-static
bundle behind a two-identical-samples filter, and are consumed on a tick.
The filter rejects a torn word, but the three alarm registers are separate
writes and land one at a time, so an alarm reprogrammed while the RTC runs
can match on a partly updated value; program the alarm (and the mode bits)
with `alarm_enable` low, or with the RTC disabled, and then enable.

---

## RTC_ALARM_MASK (0x30)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | sec_match_en | RW | 0 | 1=compare seconds for alarm, 0=don't care |
| 1 | min_match_en | RW | 0 | 1=compare minutes for alarm, 0=don't care |
| 2 | hour_match_en | RW | 0 | 1=compare hours for alarm, 0=don't care |
| 31:3 | Reserved | RO | 0 | Reserved |

The mask bits are active-high *match enables*, not "ignore" bits. Out of reset
all three are 0, so every field is a don't-care and an enabled alarm matches
every second. Set the relevant `*_match_en` bits for the fields that must match.

The alarm is not evaluated while the counter domain sees `time_set_mode`
set — the divider is paused, so there is no tick to evaluate it on — nor
during the few counter clocks of a commit, so a counter paused on the alarm
value mid-programming does not raise the flag. A commit that lands exactly
on the alarm value does not fire the alarm either: alarms fire on a tick, and
the next evaluation compares the following second.

---

## Time Format

Time/date values are stored in binary by default. When `bcd_mode` (RTC_CONFIG
bit 2) is set, the same fields are presented in BCD:

| Field | Binary | BCD |
|-------|--------|-----|
| Seconds | 0-59 | 0x00-0x59 |
| Minutes | 0-59 | 0x00-0x59 |
| Hours (24-hour) | 0-23 | 0x00-0x23 |
| Hours (12-hour) | 1-12, bit 7 = PM | 0x01-0x12, bit 7 = PM |
| Day of month | 1-31 | 0x01-0x31 |
| Month | 1-12 | 0x01-0x12 |
| Year | 0-99 | 0x00-0x99 |

All calendar arithmetic is done in binary internally; BCD exists only at the
register boundary. The days-in-month table is therefore the same in both
formats: 31 for January, March, May, July, August, October and December, 30
for April, June, September and November, and 28 or 29 for February. The year
is two digits with base 2000, and the leap rule is every year divisible by 4
— exact for 2000-2099, since 2000 is a leap year and the century exception
does not arise before 2100. The year wraps 99 to 00 with no century carry.

### 12-hour mode

In 12-hour mode the hour occupies bits 6:0 (1-12, or 0x01-0x12 in BCD) and
bit 7 is the PM flag, in both binary and BCD counting. The sequence is:

| Hours | PM | Next hours | Next PM | Day carry |
|-------|----|------------|---------|-----------|
| 11 | 0 | 12 | 1 | no (11:59:59 AM -> 12:00:00 PM) |
| 11 | 1 | 12 | 0 | yes (11:59:59 PM -> 12:00:00 AM, midnight) |
| 12 | x | 1 | x | no (12:59:59 -> 1:00:00, no toggle) |

AM/PM toggles on the 11 -> 12 transition, 12 -> 1 does not toggle, and the
day carries once per day at 11:59:59 PM -> 12:00:00 AM.
`RTC_STATUS.pm_indicator` mirrors bit 7 and is valid in both formats.

### Out-of-range values

Loading an out-of-range value (day 40, hours 90) is software's
responsibility and software should not do it. The counters accept it and the
arithmetic stays defined — every limit comparison is a greater-or-equal,
never an equality — but the calendar is only meaningful again once the field
wraps. In BCD mode an out-of-range load is clamped to the field's maximum on
the next tick rather than silently rewritten to a wrong digit.

---

## Remaining limitations

None of these is a defect in the block; they are the edges of what it does.

- `clock_select` is a combinational clock mux, so it must be changed with
  `rtc_enable` low.
- The alarm registers land in the counter domain one write at a time;
  program the alarm (or the mode bits) with the alarm (or the RTC)
  disabled, then enable.
- Time-set mode pauses the divider only once the counter domain samples
  it, about three counter clocks; a shorter staging window is not seen and
  the clock keeps running until the commit replaces the time. The commit
  brackets the tick either way, so the counters never take two updates on
  consecutive counter clocks.
- A commit the counter domain does not acknowledge within
  `COMMIT_TIMEOUT_CYCLES` is reported in `RTC_STATUS.commit_timeout`, and
  its data is held and lands unchanged when the counter clock returns; the
  flag means "not acknowledged in time", not "not set", and it releases the
  staged values by that transfer's timeout event, not by a persisting
  condition. A stall is always reported: the flag sets when the in-flight
  transfer exceeds the window even if a retry has been queued behind it,
  and the queued commit keeps busy and its staged values (until its own window expires) and lands after
  the stalled one.
- A commit that lands exactly on the alarm value does not fire the alarm;
  alarms fire on a tick, and the next evaluation compares the following
  second.
- The resets are independent: `presetn` alone keeps the clock — the counter
  domain holds its run/enable state and its clock source, the time and
  `time_valid` are still correct afterwards, and a crossed `rtc_enable` or
  `clock_select` is applied again only once software re-writes RTC_CONFIG
  (`time_set_mode` is the exception: it is not held, so a bus reset during
  staging releases the pause by itself and drops the staged time); the
  `commit_timeout` report survives a bus reset while its stall is
  outstanding;
  a commit in flight lands intact, and a commit queued before the reset
  still lands with the data captured at its commit pulse, so the time can
  change shortly after a bus reset because of a request that predates it.
  `rtc_resetn` alone resets the commit link on both sides and the bus-side
  commit bookkeeping, so a commit staged while it is held low is dropped
  without hanging busy or reporting a timeout, and must be re-issued.
- Out-of-range loads are accepted, not rejected; in BCD mode they are
  clamped to the field maximum on the next tick.
- Clock calibration, battery-backup domain handling, day-of-week and century
  rollover past 2099 are not implemented. In particular the counter domain's
  reset release waits for the clock-select settle one-shot, a pclk flop, so
  an `rtc_resetn` pulse while `pclk` is stopped leaves the counters in reset
  until pclk returns.

The deferred lint items on the shared CDC primitives and the clock mux are
tracked as RLB-010 in `vault/Tasks/RLB/open.md`.

## History

The clock crossings, the atomic time-set commit, the seconds-latched read,
the sticky single-event status flags, the binary-internal calendar, the
12-hour sequencing, the strict decode and the `rtc_resetn` path were all
fixed on 2026-09-09 under GitHub issue #56.

---

## Navigation

**Back to:** [RTC Specification Index](../rtc_mas_index.md)
