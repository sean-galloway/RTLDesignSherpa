# Test Plan: fifo_async

## Module: rtl/common/fifo_async.sv
## Test File: val/common/test_fifo_buffer_async.py
## Current Coverage: TBD (see note under Coverage)

## Module Overview

Asynchronous (CDC) FIFO with independent write and read clock domains. Pointers
cross domains in a one-bit-change encoding selected by `USE_JOHNSON`:

| USE_JOHNSON | Encoding | Pointer width | Converter | Legal DEPTH |
|-------------|----------|---------------|-----------|-------------|
| 0 (default) | Gray | `$clog2(DEPTH)+1` | `gray2bin` (combinational) | power of 2 only |
| 1 | Johnson | `DEPTH` | `johnson2bin` (registered) | any even depth |

`USE_JOHNSON=1` replaces the retired standalone `fifo_async_div2` module. The
Johnson scenarios and depth sweep below were moved here from that module's test
plan and test (`test_fifo_buffer_async_div2.py`) when it was retired, so the
coverage intent is preserved even though the module is gone.

## Scenarios

### Common to both encodings

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| FA-01 | Basic write/read | Single write followed by read across domains | YES | - |
| FA-02 | Fill to full | Write until `wr_full` | YES | - |
| FA-03 | Drain to empty | Read until `rd_empty` | YES | - |
| FA-04 | Simultaneous R/W | Concurrent write and read in different domains | YES | - |
| FA-05 | Write when full | Attempt write to full FIFO | NO | Error path uncovered |
| FA-06 | Read when empty | Attempt read from empty FIFO | NO | Error path uncovered |
| FA-07 | Almost full flag | Verify `wr_almost_full` threshold | YES | - |
| FA-08 | Almost empty flag | Verify `rd_almost_empty` threshold | YES | - |
| FA-09 | REGISTERED=0 (mux) | Combinational read path | YES | - |
| FA-10 | REGISTERED=1 (flop) | Registered read path | YES | - |
| FA-11 | wr_clk faster than rd_clk | 10ns vs 12ns periods | YES | - |
| FA-12 | rd_clk faster than wr_clk | 10ns vs 8ns periods | YES | - |
| FA-13 | Pointer sync latency | Flags settle after N_FLOP_CROSS cycles | PARTIAL | N_FLOP_CROSS not swept |

### Gray encoding (USE_JOHNSON=0)

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| FA-G1 | Power-of-2 depths | DEPTH in {4, 8, 16} | YES | - |
| FA-G2 | Gray pointer wrap | Pointer wraps at 2**(AW+1), MSB distinguishes full/empty | PARTIAL | wrap not directly asserted |
| FA-G3 | Non-power-of-2 rejected | DEPTH=10 must fail elaboration with `$error` | NO | Guard is unverified by any test |

### Johnson encoding (USE_JOHNSON=1) -- moved from fifo_async_div2

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| FA-J1 | Even non-power-of-2 depths | DEPTH in {6, 10, 14} -- the case Gray cannot express | YES | - |
| FA-J2 | Power-of-2 depth under Johnson | DEPTH=4 with Johnson pointers (both encodings legal) | YES | - |
| FA-J3 | Johnson sequence integrity | Pointer cycles 2*WIDTH states, one bit change per step | UNKNOWN | Covered at counter level, not at FIFO level |
| FA-J4 | johnson2bin round trip | Johnson pointer decodes to the correct binary pointer | UNKNOWN | Inferred from data integrity only |
| FA-J5 | Registered converter latency | `johnson2bin` is registered where `gray2bin` is not -- flags are one cycle later than the Gray path | NO | Latency difference between encodings not asserted |

### Reset behavior (both encodings)

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| FA-R1 | Both domains reset together | Standard startup | YES | - |
| FA-R2 | Write domain reset alone | `wr_rst_n` pulsed while read domain runs | NO | See note below |
| FA-R3 | Read domain reset alone | `rd_rst_n` pulsed while write domain runs | NO | See note below |

**Note on FA-R2/FA-R3.** Each domain resets its own pointer *and* its
synchronized copy of the remote pointer from the local reset, so a one-sided
reset should leave that side self-consistent (both pointers zero, reads empty)
rather than desynchronized. This is a deliberate design property and the reason
an async FIFO is preferred over a toggle handshake where domains reset
independently -- see `docs/markdown/RTLAmba/cdc/cdc.md#cdc_2_phase_handshake`
(Reset Considerations). It is currently **argued from the RTL, not verified**.

## Coverage

Coverage numbers were not re-measured after `fifo_async_div2` was folded into
`fifo_async` via `USE_JOHNSON`. The Johnson path previously had its own test and
a passing formal proof (`formal/common/fifo_async_div2/`); both were removed with
the module. Re-measure before trusting any figure here.

## Action Items

1. **FA-G3**: Add a negative elaboration test (Gray + non-power-of-2 DEPTH must
   fail the build). Currently the guard is unverified.
2. **FA-J5**: Assert the flag-latency difference between the registered
   `johnson2bin` and combinational `gray2bin` paths.
3. **FA-R2/R3**: Add one-sided reset tests for both encodings -- this is the
   property that motivated using a FIFO over a toggle handshake, and nothing
   currently checks it.
4. **FA-05/06**: Add full-write and empty-read error-path tests (carried over
   from the same gaps in `fifo_sync_testplan.md`).
5. Restore formal coverage for the Johnson pointer path, either by repointing the
   retired div2 proof at `fifo_async` with `USE_JOHNSON=1` or writing a new one.

## Test Commands

```bash
# Both encodings, functional level
REG_LEVEL=FUNC pytest val/common/test_fifo_buffer_async.py -v

# Johnson only (non-power-of-2 depths)
REG_LEVEL=FULL pytest val/common/test_fifo_buffer_async.py -v -k "-1-"

# With coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_fifo_buffer_async.py -v
```
