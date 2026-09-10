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


# Real-Time Clock (RTC)

**Status:** Implemented; GitHub #56 RTL defects fixed and covered by the
regression suite. Measured: the runner's levels nest (gate = basic, func =
basic + medium, full = all three), so `gate` reports 6/6, `func` 44/44 and
`full` 60/60; the separate short-timeout sweep build (elaborated with
`COMMIT_TIMEOUT_CYCLES = 200`) reports 8/8 - GH56-16, GH56-R8-1..R8-4 and
GH56-R9-1..R9-3, which are the commit-watchdog and queued-slot cases that
need a window short enough to hit inside a test.
**Address:** `0x4000_3000 - 0x4000_3FFF` (4 KB window, 13 registers decoded)

---

## What this block is

A time-of-day counter with one alarm, an APB4 register interface, and two
clock domains. It counts seconds/minutes/hours/day/month/year in binary or
BCD, in 24-hour or 12-hour form, handles leap years for 2000-2099, and raises
two interrupts (per-second tick and alarm match).

## Clocks, resets and the crossings

| Domain | Clock | Reset | Holds |
|---|---|---|---|
| APB | `pclk` | `presetn` | register file, address decode, the read shadow software sees, the sticky status flags |
| Counter | `rtc_clk` (32.768 kHz), or `pclk` when `RTC_CONFIG.clock_select=1` | `rtc_resetn`, release synchronized onto the counter clock by `reset_sync` | divider, the six counters, calendar arithmetic, alarm comparator |

The two resets are independent, and the commit link takes its side from the
counter domain rather than the bus:

| Reset asserted | What resets | What survives |
|---|---|---|
| `presetn` only | register file, read shadow and its fill counter, the wrapper's snapshot latches, the config-valid flag, the alarm and tick status flags | the counter domain **and everything that keeps state across a bus reset**: both ends of the commit handshake, the bookkeeping that tracks it (pending, busy, in-flight, load evidence, the pending watchdog `r_pend_wdog` / `r_pend_wdog_arm` and its two marks `r_pend_expired` / `r_pend_reported`; the flop-by-flop table is in `rtc_core.sv`'s header), the *destination* sides of the snapshot-pulse, **load-pulse** and tick/alarm synchronizers with their edge detectors, **`RTC_STATUS.commit_timeout`** (the one status flag that follows the transfer it reports rather than the register file), the held clock-source select with its settle one-shot, and the applied-configuration hold. A commit in flight **or queued** still lands intact |
| `rtc_resetn` only | counter domain (release synchronized onto the counter clock) **and everything in the "survives presetn" column**, through a reset synchronizer onto pclk | the register file; the shadow refills from the reset counters within a few pclk |
| both | everything, as at power-on | - |

The counter domain's reset **release depends on `pclk`**: the clock-select
settle one-shot runs on `pclk` and gates the counter-domain reset
synchronizer, so the domain leaves reset roughly 7-9 `pclk` edges after
`rtc_resetn` rises - and with `pclk` stopped it never leaves reset at all.
Recovering the counter domain needs both clocks running, not just `rtc_clk`.

A commit staged entirely while `rtc_resetn` is low is **dropped**: it never
sets busy, and it is not delivered when the reset releases. Re-issue it.

The synchronizers that carry *completion evidence* take the same reset as the
bookkeeping they feed. A toggle synchronizer with one side reset is parity: a
bus reset over the commit's load edge would otherwise either destroy the
snapshot pulse (busy stuck, the register file left presenting staged values)
or fabricate one (the pre-commit time published as the commit's answer) -
one per parity. The same applies to the tick/alarm level synchronizer, where
resetting the synchronized copy of a still-high source makes release look
like a fresh edge and manufactures a status flag with no tick behind it. The
sticky flags themselves stay on `presetn`; they are register-file-like, and
clearing them on a bus reset is right. It is only their set evidence that
must not be.

### Configuration survives a bus reset

Every bit the counter domain obeys lives in the register file and resets to
zero there, and a reset default that crosses a domain boundary **is a
command**: `rtc_enable=0` stops the clock, `clock_select=0` flips the mux
under a running domain. So the configuration crosses together with a
config-valid flag that any `RTC_CONFIG` write sets and `presetn` clears; the
counter domain applies the crossed bundle only while that flag is set and
otherwise holds the last configuration it applied. The clock-source select is
additionally held in a flop on the counter domain's reset, because it feeds
the mux that makes that clock.

One field is deliberately **not** held: `time_set_mode`. It is a transient
control, not configuration - held, a bus reset landing while software was
staging a time would pin the divider at zero for good, because the register
file's copy is cleared but the counter domain's is not and the software that
would have cleared it has just been reset. It is taken live from the crossing,
so a bus reset releases the pause on its own with no register write required.

After a bus reset the RTC therefore keeps running exactly as it was,
`RTC_CONFIG` reads its reset value, and **software re-writes `RTC_CONFIG` to
re-establish (or change) the configuration**. Until it does, the counters are
still formatting the time with the BCD/12-hour settings from the hold while
`RTC_CONFIG` reads 0 - the register file and the counter domain disagree about
the format - so **do not read the time until `RTC_CONFIG` has been
re-written**. The combinational-mux
constraint below still applies to genuine software changes of
`clock_select`.

The source side of the handshake - and every flop that tracks it - is
deliberately **not** reset by `presetn`.
Resetting it alone zeroes the held data while the request is already inside
the destination's synchronizer - the destination then loads zeros - and
abandons the destination's acknowledge level, which afterwards satisfies the
next request in about one pclk cycle instead of a real round trip. Both were
measured on this block. `rtc_resetn` may reset it because that reset also
resets the destination: both ends go idle together, so an unacknowledged
commit is simply **dropped and must be re-issued by software**. Retiring a
transfer without both ends agreeing is not something any handshake can do.

The bookkeeping shares that reset rather than the bus reset because it tracks
the same object: with the two split, a commit staged while `rtc_resetn` was
low hung `busy` forever (the handshake holds `src_ready` low through its own
reset, so nothing could complete or time out) and the timeout edge detector
manufactured an event at release. The data a queued commit will carry is
captured at the commit pulse, so a bus reset that clears the register file
cannot turn a queued commit into a delivery of the file's reset values.

Every crossing between them is explicit, and each uses a primitive from
`rtl/cdc` rather than a hand-rolled synchronizer:

| Direction | What crosses | Primitive | Latency |
|---|---|---|---|
| pclk -> counter | config + alarm compare values + the cfg_valid flag (34 bits) | `glitch_free_n_dff_arn` (3 flops) + a two-identical-samples filter on its output | 5 counter clocks (3 chain + 2 filter); `time_set_mode` is not held and arrives in 3 |
| pclk -> counter | the six staged time bytes + the commit event | `cdc_4_phase_handshake` (closed loop, 48 bits, watchdog) | load at ~4-5 counter clocks, full cycle ~7 (~210 us on a 32.768 kHz crystal) |
| counter -> pclk | the coherent time snapshot | `sync_pulse` on the update event, capturing a snapshot register | 3-4 pclk after the counters change |
| counter -> pclk | the same time as a background refresh | `glitch_free_n_dff_arn` (3 flops) + a two-identical-samples filter, gated until the chain has filled | 4-5 pclk after any change |
| counter -> pclk | `second_tick`, `alarm_match` | `glitch_free_n_dff_arn` + edge detect in pclk | 3-4 pclk |

The closed-loop handshake on the write side is what makes the block work at
the REAL clock ratio. The previous design sent a one-`pclk` strobe into a
32.768 kHz domain, where it was captured roughly one time in three thousand,
so the documented way to set the time only worked in `clock_select=1` test
mode (GitHub #56 H7 / round_3 item 1).

It is a **four**-phase handshake, not a two-phase one, because `presetn` and
`rtc_resetn` are separate pins: this block is meant to keep time across an APB
reset. A two-phase handshake stores its transfer state as toggle *parity*,
which is relative, so a one-sided reset fabricates a transfer out of an idle
link. Measured both ways round here: a `presetn`-only pulse committed the
all-zero data that same reset had just cleared (day and month loaded 0), and
an `rtc_resetn`-only pulse replayed the last committed time into the freshly
reset counters. In four-phase the request is a level and `req = 0` *is* idle,
absolutely. `docs/markdown/rtl-cdc/cdc.md` states this as a design rule.

### Required timing constraints

The two multi-bit bundles are bounded datapaths, not false paths. A blanket
`set_false_path` permits unbounded skew between the bits, and skewed bits
defeat both the two-identical-samples filter on the read bundle and the
quasi-static argument for the config bundle. Constrain the counter->pclk read
bundle and the pclk->counter config/alarm bundle with
`set_max_delay -datapath_only` of one destination clock period, from the
source flops to the first synchronizer stage; same for the snapshot registers
into the shadow, and for the single-bit toggles. The four-phase handshake's
own data bus is quasi-static - held for the whole request - so one
destination period covers it too. The exact `set_max_delay` lines are in
`rtc_core.sv`'s header.

### If the counter clock stops

A commit needs the counter clock to complete. If the clock is not running (no
crystal, oscillator fault, or a runt pulse from switching `clock_select`
live), the handshake's watchdog expires after `COMMIT_TIMEOUT_CYCLES` pclk
cycles (parameter on `apb4_rtc`/`rtc_core`, default 65535) and sets
`RTC_STATUS.commit_timeout` (bit 4, sticky, W1C). A value of 0 disables
both watchdogs, the in-flight one and the queued commit's; a commit on a
dead counter clock then holds busy and the staged values, unreported, until
the clock returns.

**The transfer is not thrown away.** `commit_timeout` means "the acknowledge
did not come back inside the window", not "the commit was cancelled": the
request stays pending with its data held, and it lands unchanged - carrying
the time software asked for - whenever the counter clock returns. So a
timed-out commit **may still land later**; read the time back rather than
assuming either outcome. `time_commit_busy` drops on the timeout, so the
register block goes back to mirroring the counter in the meantime.

That release covers the *in-flight* commit. **A queued commit has its own
`COMMIT_TIMEOUT_CYCLES` window counted from its commit pulse; if it is not
accepted within it, `commit_timeout` is reported again and busy is released
while the commit stays queued. A commit accepted within its window inherits
no window of its own to answer for and reports nothing; if a report is
already standing for the slot it does carry the duty to retire it when it
lands.** That is every commit in normal operation,
where the queue drains in about ten counter clocks.

The window exists because a queued commit that is never accepted cannot be
reported any other way: the in-flight watchdog is a level that never dropped,
so its edge detector can never fire a second event, and while the clock is
dead the queued commit is never accepted. Without its own window busy hangs
forever with the staged bytes pinned in the register file and `time_valid`
low - and that hang has two shapes, one where the commit is queued *after*
the first report and one where it is queued *before* it, so the window has no
exceptions. On expiry nothing is cancelled: the request and its data are
kept, it lands when the clock returns, and the flag it raised retires by
itself when the commit that **finally lands from that slot** completes. A
third commit while one is queued replaces the queued data, re-raises busy and
gives itself a fresh window; the queue stays one deep, and the report already
standing for the slot is not orphaned by the replacement - it retires when
that newest word lands.

Cancelling was tried and is wrong. Resetting the source side alone withdraws
the request level but leaves the *destination's* four-phase state - its ack
level, reset only by `rtc_resetn` - behind, and the next request is then
satisfied by that stale ack in about one pclk cycle instead of a real round
trip. Withdrawing a request needs both sides to agree, which is another
handshake; not cancelling is simpler and strictly safer, because the worst
case is a correct time arriving late rather than a link that is no longer
synchronised. One further commit may be queued behind an unacknowledged one;
it is handed over only when the link is idle again, so nothing is delivered
twice.

The `COMMIT_TIMEOUT_CYCLES` floor: a commit needs about ten counter clocks end
to end, so the parameter must exceed `10 x (pclk / counter clock)` - about
30500 cycles at 100 MHz against a 32.768 kHz crystal. The same floor covers a
queued commit's own window, because what it waits on is the in-flight
transfer finishing, which is that same ten counter clocks.

`time_commit_busy` must be read together with `commit_timeout`:

| `busy` | `commit_timeout` | Meaning |
|---|---|---|
| 1 | x | the commit is still outstanding |
| 0 | 0 | the committed time has **landed** in the counters and is visible in the shadow - unless software has already cleared a report by W1C while commits are still held on a dead clock; `time_valid` tells the two apart |
| 0 | 1 | the commit's **window expired**; it has *not* landed, it is still held, and it will land when the counter clock returns |

The landed case is driven by evidence of the load, not by the staged bytes
happening to match what the shadow already showed. A `presetn` pulse while busy is set
clears the register file, so the six time registers read their **reset
defaults** - not the staged values - until busy clears and the mirror resumes
with the committed time; `RTC_STATUS.time_valid` reads 0 for that window and
is the signpost.

A stall is **always reported**, including when a retry is already queued
behind the stalled transfer - that is exactly when software needs to know its
set-time is not getting through. What the queued commit changes is the
release, not the report: `time_commit_busy` stays set through the in-flight
transfer's report (it is cleared by the timeout *event*, never by its level),
so the queued commit keeps its staged values visible - but only until its own
window expires, at which point it makes its own report and releases `busy`
itself.

`commit_timeout` reports an **outstanding** stall: it is retired
automatically when the stalled commit finally completes, as well as by W1C.
Software that needs a latched record must read it while the stall persists.

Note what the timeout does **not** hold. Reporting the timeout also releases
`busy`, so the six time registers stop showing the staged values at that
instant and go back to mirroring the counter. A commit **queued** behind the
stalled one keeps `busy` set - and with it that commit's staged values - only
until its own window runs out; then it reports and releases `busy` in turn,
and the mirror resumes even though the commit is still queued.

## Setting the time

1. Write `RTC_CONFIG.time_set_mode = 1`. The counters stop and the six time
   registers stop mirroring the counter - they are staging registers now.
2. Write `RTC_SECONDS`, `RTC_MINUTES`, `RTC_HOURS`, `RTC_DAY`, `RTC_MONTH`,
   `RTC_YEAR` in any order, at any speed. Nothing crosses to the counter
   domain yet, so back-to-back writes cannot lose a field and a half-written
   batch cannot be loaded.
3. Write `RTC_CONFIG.time_set_mode = 0`. That falling edge is the commit: all
   six bytes cross as one transfer and load the counters on a single counter
   clock edge.

Until the loaded time is visible in the pclk shadow, the six registers keep
returning the STAGED values, so a readback in that window shows the time you
asked for rather than the pre-commit time. There is no commit register: the
falling edge was chosen so the published register map did not change.

## Reading the time

The six time registers are answered from a pclk shadow of the counters, not
from the counters themselves, and the shadow is only ever written with a
complete, coherent time. On top of that there is exactly one rule, with no
window, no timer and no state that can get stuck:

**`RTC_SECONDS` reads the live shadow, and that read latches the other five
registers - plus `pm_indicator` and `time_valid` - at the same instant.**

So read the time as the burst `SECONDS -> MINUTES -> HOURS -> DAY -> MONTH ->
YEAR` and every value in it belongs to one instant, wherever the tick lands.
`RTC_MINUTES`..`RTC_YEAR` always report the time as of the last `RTC_SECONDS`
read: read one of them without ever reading `RTC_SECONDS` and you get the last
latch, which is the price of having no hidden window. Polling `RTC_SECONDS`
alone always tracks the clock, because it is never held.

The alignment is exact rather than approximately right, and it is worth
saying why. The APB bridge holds its request to the register block for two
cycles but captures the read data in the **first**, so: the value returned for
`RTC_SECONDS` is that field's storage during the first request cycle, which
the mirror loaded from the shadow one cycle earlier; the latch strobe is that
same first cycle, edge-detected so the second cannot latch again; and the five
fields load from a one-cycle-delayed copy of the shadow, so they capture that
same earlier cycle. Measured across every pclk alignment of a shadow update
against the request window - including an update landing *inside* the second
request cycle - 16/16 bursts were coherent. The interesting one:

```
t(ns)  req addr  latch | live shadow | delayed copy | read data
2770    1  0x0C    1   |   59:59     |     59       |    59      first request cycle: data captured, five fields latch
2780    1  0x0C    0   |    0:00     |     59       |    59      second cycle: shadow has MOVED, latch already closed
2790    0    -     0   |    0:00     |      0       |     -      delayed copy catches up; the five keep the 59 generation
```

Read latency: one tick plus 3-4 pclk of synchronizer. The time you read is the
time as of the last second boundary, which is what a one-second counter can
mean.

## Status flags and interrupts

`RTC_STATUS.alarm_flag` and `RTC_STATUS.second_tick` are sticky flags in the
pclk domain, set by a SINGLE-cycle event derived from the counter-domain
level, and cleared by writing 1. The counter-domain sources are one counter
clock wide - about 30 us on a real crystal - and edge-detecting them in pclk
is what stops a wide source level from re-arming a flag one cycle after
software cleared it (GitHub #56 round_3 item 2).

**Set wins over a simultaneous clear.** A W1C that lands in the same cycle as
a new tick leaves the flag set: dropping the event would lose an interrupt,
and software sees the flag on its next read.

`RTC_STATUS.time_valid` reports that the counters have been loaded or have
ticked at least once. `RTC_STATUS.pm_indicator` mirrors `RTC_HOURS` bit 7 and
is valid in 12-hour mode for BOTH binary and BCD counting.
`RTC_STATUS.commit_timeout` reports a time-set commit the watchdog found
outstanding (above) - held, not abandoned.

A commit that lands exactly on the alarm value does **not** fire the alarm:
alarms are evaluated on a tick and a commit is not a tick, so setting the
clock to the alarm time arms it for the next time the counter *reaches* that
value, a full second later at the earliest.

**The alarm fires at the tick that makes the readable clock show the alarm
value**, not one tick later: the comparator runs against the time the tick is
about to publish, so software that sees `alarm_flag` and reads the clock sees
the alarm value. `RTC_ALARM_HOUR` is compared against the whole hours byte,
bit 7 included, so in 12-hour mode 3 PM is `0x83` binary / `0x93` BCD and an
alarm hour with bit 7 clear only ever matches an AM hour.

## Address decode

Exactly thirteen addresses are software-visible: `0x000`, `0x004`, `0x008`,
then `0x00C`-`0x030` on a 4-byte stride. Every other address in the 4 KB
window - the reserved slots at `0x034`-`0x03C` as much as anything above
`0x03F` - is dropped: the write is ignored, the read returns zero, and the
access answers with `PSLVERR` through a locally held acknowledge. Nothing
aliases: `0x864` no longer reaches `RTC_ALARM_SEC`.

## Counting semantics

- **Binary or BCD** (`RTC_CONFIG.bcd_mode`). All calendar arithmetic is done
  in binary internally; BCD exists only at the register boundary.
- **12-hour mode** (`RTC_CONFIG.hour_mode_12`): hours run 1-12 with bit 7 as
  the PM flag, in binary AND BCD. AM/PM toggles on the 11 -> 12 transition,
  12 -> 1 does not toggle, and the day carries at 11:59:59 PM -> 12:00:00 AM
  (midnight), once per day.
- **Leap years**: every year divisible by 4 in 2000-2099; February is 29 days
  in those years, 28 otherwise.
- **Out-of-range loads are software's problem.** Loading day 40 or hours 90
  is accepted and the arithmetic stays defined (every comparison is `>=`,
  never `==`), but the calendar is only meaningful again once the field
  wraps. In BCD counting a loaded value of 100 or more has no two-digit
  representation, so the next tick **clamps it to 99** rather than truncating
  the tens digit into a date that looks plausible and is wrong.

## Files

| File | Role |
|---|---|
| `apb4_rtc.sv` | top level: APB4 slave, both clocks, both resets |
| `rtc_config_regs.sv` | decode + PSLVERR, time-set staging/commit, read coherency window, W1C decode |
| `rtc_core.sv` | counters, calendar, alarm, and all four clock crossings |
| `rtc_regs.sv/` | PeakRDL output (`rtc_regs.sv`, `rtc_regs_pkg.sv`) - generated, do not edit |
| `peakrdl/rtc_regs.rdl` | register source of truth |
| `rtc_regmap.py` | generated register map for by-name DV access |
| `rtc_helper.py` | register programming helper |
| `filelists/apb4_rtc.f` | compile closure (APB slave, the CDC primitives, the adapter, this block) |

Regenerate the register block ONLY through the shared tool, and copy the
result into the directory the filelist reads (`rtc_regs.sv/`):

```bash
python3 bin/peakrdl_generate.py \
    projects/components/retro_legacy_blocks/rtl/rtc/peakrdl/rtc_regs.rdl \
    -o <scratch-dir> --no-html --no-markdown \
    --regmap-output <scratch-dir>/rtc_regmap.py
```

then copy `rtl/rtc_regs.sv`, `rtl/rtc_regs_pkg.sv` and `rtc_regmap.py` into
this directory and delete the scratch directory. A second, orphaned copy of
generated output is a live trap.

## Register map

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x000  | RTC_CONFIG | RW | enable, hour mode, BCD mode, clock select, time_set_mode |
| 0x004  | RTC_CONTROL | RW | alarm enable, alarm interrupt enable, second interrupt enable |
| 0x008  | RTC_STATUS | RW | alarm_flag (W1C), second_tick (W1C), time_valid, pm_indicator, commit_timeout (W1C) |
| 0x00C  | RTC_SECONDS | RW | seconds (0-59 / 0x00-0x59) |
| 0x010  | RTC_MINUTES | RW | minutes (0-59 / 0x00-0x59) |
| 0x014  | RTC_HOURS | RW | hours; bit 7 = PM in 12-hour mode |
| 0x018  | RTC_DAY | RW | day of month |
| 0x01C  | RTC_MONTH | RW | month |
| 0x020  | RTC_YEAR | RW | year, base 2000 |
| 0x024  | RTC_ALARM_SEC | RW | alarm seconds |
| 0x028  | RTC_ALARM_MIN | RW | alarm minutes |
| 0x02C  | RTC_ALARM_HOUR | RW | alarm hours |
| 0x030  | RTC_ALARM_MASK | RW | per-field alarm compare enables |

Field detail lives in `peakrdl/rtc_regs.rdl`, which is the source both the
RTL and `rtc_regmap.py` are generated from.

## Known limitations

- `selected_clk` is a plain combinational clock mux. Change
  `RTC_CONFIG.clock_select` only with `rtc_enable` low; switching it while
  the RTC runs can produce a runt clock pulse. A glitchless mux needs a
  device-specific cell that does not belong in portable RTL. A runt pulse can
  also strand a commit that is in flight; that case ends in the watchdog and
  is reported as `RTC_STATUS.commit_timeout` rather than hanging.
- The alarm compare values, the mask and the mode bits cross as ONE
  quasi-static bundle, sampled free-running, so while software is part-way
  through programming it the counter domain can observe an intermediate
  combination for one counter clock (a new alarm second against an old alarm
  minute). **Program `RTC_ALARM_*` and the mask with the alarm disabled and
  enable it last; set the counting format before enabling the RTC.**
- The divider is held at zero for the whole of `time_set_mode` and across the
  commit: no tick, no second interrupt, no alarm evaluation and no counter
  advance while a time is being staged. The hold releases **on** the load
  edge, so the first second after a commit is exactly one divider period -
  measured 100 selected_clk edges in test mode against a 100-edge steady-state
  period - rather than one period plus a hold cycle.
- While a staged time is what software can read, `pm_indicator` is bit 7 of
  the **staged** hours byte and `time_valid` reads 0 - the visible time is not
  yet the running one. Both revert to the counter's values as soon as the
  commit is visible.
- Clock calibration, battery-backup domain handling, day-of-week and century
  rollover past 2099 are not implemented.

## Running the tests

```bash
cd projects/components/retro_legacy_blocks/dv/tests
make clean-all && make run-apb4_rtc-full
```

Always `clean-all` first: a fast pass on a stale `local_sim_build` is a
report about the previous RTL.
