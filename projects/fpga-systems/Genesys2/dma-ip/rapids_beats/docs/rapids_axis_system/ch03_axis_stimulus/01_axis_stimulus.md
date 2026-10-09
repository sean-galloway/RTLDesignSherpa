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

# Stream Stimulus and Checking

STREAM's harness needs memory models. The rapids harness needs those and
two stream endpoints, and the endpoints have to be as deterministic as the
memory models so that a CRC can be predicted in software. Both are
`rtl/amba/shared` blocks, built for this harness and reused by STREAM's
generator since the interleave work.

## The generator: `axis4_master_injector`

An AXIS master with no address channel. Per channel it runs an independent
LFSR seeded with `seed ^ channel` and a CRC-32 over what it emits, the same
LFSR and CRC as `axi4_slave_rd_injector`, so a stream integrity check and
a memory integrity check produce comparable numbers. The LFSR and the CRC
advance only on accepted beats: beat N of channel C is a function of
`(seed ^ C, N)` regardless of how `tready` stalled it, which is what makes
the pattern predictable under backpressure and under the interleaved
schedule.

| Register (harness CSR) | Field | Effect |
|------------------------|-------|--------|
| `GEN_CTRL` | `cfg_gen_start` | arm one run; the actual start comes from GO |
| `GEN_LFSR_SEED` | 32 bits | the base seed; `0xDEADBEEF` is the campaign default, `--base-seed` overrides it for the sink half |
| `GEN_NUM_BEATS` | 32 bits | beats per channel |
| `GEN_BEATS_PPKT` | 32 bits | `tlast` cadence; 0 means one packet per channel |
| `GEN_CH_MASK` | one bit per channel | active channels; 0 means all |
| `GEN_TDEST` | `AXIS_DEST_WIDTH` | the `tdest` value on every beat |
| `GEN_MODE` | `INTERLEAVE` | the channel schedule, below |

: Table 3.1: Generator configuration

Two schedules. **Sequential** finishes one channel's beats, then the next:
each channel's stream is contiguous, and only one sink channel holds data
at a time. **Interleaved** (`GEN_MODE.INTERLEAVE`, `--interleave`, rapids
TASK-018) hands the bus to the next active channel after every accepted
beat, so `tid` changes every beat and every sink channel holds data at once.
A channel's LFSR and CRC still advance only on its own beats, so the
per-channel data, CRCs and packet boundaries are identical under both
schedules and the golden model does not care which ran. The difference is
what the sink column measures: one channel's window under the sequential
schedule, the DUT's aggregate window under the interleaved one (report
Tables 7.5 and 7.5b).

The generator reports per-channel expected CRCs and beat counts, and an
aggregate total, as corroboration. PASS never rests on them.

## The checker: `axis4_slave_pattern_check`

An AXIS slave and a pure sink. Its `tready` is the `ready_en` input, which
the harness exposes as `CHK_CTRL.chk_ready_en`: the campaign's
source-backpressure knob (`--backpressure`, `--suite-bp`) is this bit held
low in a pattern, and it reaches only the source half since the sink's
egress is AXI. Incoming beats are demuxed by `tid` into the matching channel
context, compared beat by beat against the locally regenerated pattern with
the same `seed ^ channel` LFSR, and accumulated into a per-channel CRC-32. A
mismatch sets a sticky `data_error`; the aggregate beat and packet counters
(`CHK_BEATS_TOTAL`, `PKT_COUNT`) are what the host polls for completion of
the source half.

Because the check is local and per beat, it is independent of upstream
stalls and of cross-channel interleave: the source may emit its channels in
any order the scheduler chooses.

## The golden model and PASS

`host/rapids_char_golden.py` runs the same LFSR and CRC in software. For the
sink half, PASS is the write CRC the memory-side checker computed equal to
the model's; for the source half, it is the read CRC the memory-side
generator produced and the checker's egress CRC both equal to the model's.
The generator's own expected CRC and the checker's own count are read as
corroboration and logged, never as the verdict.

## GO

The stream is the one stimulus STREAM's harness does not have to start. In
rapids the kick sequencer's GO does three things within a few `aclk` cycles:
arms the meter windows, fires every staged descriptor kick, and starts the
generator. Nothing on the sink side moves until the generator's first beat
is offered, which is why the ingress window is defined by that beat and not
by GO (Chapter 4).
