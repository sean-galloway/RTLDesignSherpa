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

# Clock Domain Crossing (CDC)

**RTL:** `rtl/cdc/`
**Filelists:** `rtl/amba/filelists/cdc_*.f`
**Status:** Production Ready **for common-clock, common-reset verification.**
Reset behavior across independent domains is argued from the RTL and, for the
2-phase hazard, confirmed on silicon -- but it is **not** covered by the formal
proofs, which drive both domains from one clock and one reset. See
[Verification status](#verification-status) before relying on that badge.

This is the single reference for clock domain crossing in this repository. It
covers every CDC building block, how to choose between them, and the reset
behavior that distinguishes them -- which is the property most likely to bite
you and the least likely to show up in simulation.

| Module | Category | One-line |
|--------|----------|----------|
| [`cdc_synchronizer`](#cdc_synchronizer) | Multi-flop sync | N-stage synchronizer for quasi-static signals |
| [`cdc_open_loop`](#cdc_open_loop) | Open loop | Source holds data + valid, no acknowledge |
| [`cdc_2_phase_handshake`](#cdc_2_phase_handshake) | Closed loop | Toggle (NRZ) valid/ready handshake, faster |
| [`cdc_4_phase_handshake`](#cdc_4_phase_handshake) | Closed loop | Level (RZ) valid/ready handshake, classic |
| [`fifo_async` / `gaxi_fifo_async`](#async-fifo-pointers-gray-and-johnson) | Pointer sync | Streaming data, buffered |

: CDC building blocks at a glance

---

## Choosing a technique

```
Need to cross clock domains with multi-bit data?
|
+-- Is data streaming / continuous?
|   |
|   +-- YES --> Async FIFO (fifo_async or gaxi_fifo_async)
|   |           Sustained 1-per-clock throughput, buffered
|   |
|   +-- NO, occasional transfers -->
|       |
|       +-- Does the source need backpressure (flow control)?
|           |
|           +-- YES --> Closed-loop handshake
|           |           (cdc_2_phase_handshake or cdc_4_phase_handshake)
|           |
|           +-- NO, source can guarantee hold time -->
|               |
|               +-- Open-loop (cdc_open_loop)
|                   Simplest, lowest area, no ack needed
|
Single-bit signal?
|
+-- Level / quasi-static --> cdc_synchronizer or glitch_free_n_dff_arn
+-- Single-cycle pulse   --> sync_pulse
+-- Reset signal          --> reset_sync
```

**Then check the [reset rule](#reset-considerations) before committing to a
handshake.** It eliminates one of the two handshake variants outright in a
common situation, and it is not visible from the port list.

### Quick reference

| Scenario | Module | Why |
|----------|--------|-----|
| Config register update (CPU -> peripheral) | `cdc_open_loop` | Infrequent, no backpressure needed |
| Interrupt signal (1 bit, pulse) | `sync_pulse` | Single-cycle event |
| Status register read (slow -> fast) | `cdc_synchronizer` | Quasi-static level |
| APB slave in different clock domain | `apb_slave_cdc` | Full protocol CDC |
| Monitor packet crossing | `cdc_4_phase_handshake` | Occasional, needs flow control |
| DMA data stream | `fifo_async` | High throughput, continuous |
| AXI channel crossing | `gaxi_skid_buffer_async` | Pipelined, GAXI protocol |
| Reset distribution | `reset_sync` | Async assert, sync deassert |

: CDC technique quick reference by scenario

---

## Reset Considerations

> **DESIGN RULE:** If the two clock domains can be reset **independently**, do
> not use `cdc_2_phase_handshake`. Use `cdc_4_phase_handshake` or an async FIFO.
> A toggle handshake stores transfer state as **parity**, and parity cannot
> survive a one-sided reset.

"Independently" includes cases that are easy to miss: a soft reset that clears a
datapath but not a register block, a per-block reset, separate power domains, or
a reset synchronizer whose deassertion is gated differently on each side.

### Why encoding decides reset behavior

| | 2-phase | 4-phase | Async FIFO |
|---|---|---|---|
| Transfer state | Parity (toggle) -- **relative** | Level -- **absolute** | Pointer position -- **absolute** |
| Idle has a value? | No | Yes (`req=0`) | Yes (pointers equal) |
| One-sided reset from **idle** | **Fabricates a transfer** | Nothing happens | Reads empty |
| One-sided reset **mid-transfer** | Duplicate or lost transfer | Duplicate transfer | Entry may be re-read or dropped |

: How pointer encoding determines reset behavior

The 2-phase protocol signals "a transfer happened" with a *transition*. The
receiver has no absolute reference -- it only knows whether the synchronized
toggle differs from its previous sample:

```systemverilog
assign w_req_event = w_req_sync ^ r_req_sync_d;   // cdc_2_phase_handshake.sv:182
```

That XOR is the entire protocol state. Each side resets its own flops:

| Flop | Domain | Reset by | After reset |
|------|--------|----------|-------------|
| `r_req_tog` | source | `rst_src_n` | `1'b0` (`:190`) |
| `r_ack_sync`, `r_ack_sync_d` | source | `rst_src_n` | `1'b0` (`:173-174`) |
| `r_ack_tog` | destination | `rst_dst_n` | `1'b0` |
| `r_req_sync`, `r_req_sync_d` | destination | `rst_dst_n` | `1'b0` (`:250-251`) |

: 2-phase handshake reset domains per flop

Reset **both** domains together and everything lands at 0 -- parity agrees, no
event. Reset **one** and the ends land at opposite parity, and the XOR reports an
edge no source transfer produced.

Because parity is relative, there is no toggle value meaning "idle". Whatever
`r_req_tog` happens to hold, a freshly cleared destination disagrees with it half
the time. In 4-phase, `req = 0` *is* idle absolutely: a reset destination
observing `req = 0` correctly concludes nothing is pending.

#### Waveform 1.1: 2-Phase Normal Transfer

![2-phase normal transfer](../../assets/WAVES/cdc_2_phase_handshake/cdc2_normal_transfer.png)

**Source:** [cdc2_normal_transfer.json](../../assets/WAVES/cdc_2_phase_handshake/cdc2_normal_transfer.json)

One `src_valid` toggles `r_req_tog` 0 -> 1. Three synchronizer stages later the
destination sees the new value, `w_req_event` pulses for one cycle, `dst_valid`
asserts. Parity now agrees at 1 on both ends.

#### Waveform 1.2: 2-Phase Hazard - Destination Reset Alone

![2-phase asymmetric reset hazard](../../assets/WAVES/cdc_2_phase_handshake/cdc2_asymmetric_reset_hazard.png)

**Source:** [cdc2_asymmetric_reset_hazard.json](../../assets/WAVES/cdc_2_phase_handshake/cdc2_asymmetric_reset_hazard.json)

`rst_dst_n` asserts while `rst_src_n` stays high:

1. The destination clears `r_req_sync` and `r_req_sync_d` to 0.
2. The source is untouched -- `r_req_tog` is still 1.
3. On release the sync chain refills with 1 while `r_req_sync_d` is the freshly
   cleared 0.
4. `w_req_event = 1 ^ 0 = 1` -- a **phantom transfer**. `dst_valid` asserts with
   stale `r_src_data_hold`, for a transfer the source never sent.

Resetting the source alone behaves the same way. The source FSM is also reset to
`S_IDLE` from `S_WAIT_ACK` (`:188-190`), abandoning an in-flight transfer, and a
cleared `r_ack_tog` can present a spurious ack to a source still waiting -- so a
one-sided reset can **lose** a transfer as well as fabricate one.

**Scope of the damage.** The handshake itself re-synchronizes: once
`r_req_sync_d` catches up to `r_req_tog`, parity agrees again. What is permanent
is the **extra item already delivered downstream**. A consumer that samples the
latest value self-heals on the next real transfer; a consumer that counts
transfers, pushes into a FIFO, or pairs responses to requests positionally is
corrupted for the rest of the session.

#### Waveform 1.3: 4-Phase Normal Transfer

![4-phase normal transfer](../../assets/WAVES/cdc_4_phase_handshake/cdc4_normal_transfer.png)

**Source:** [cdc4_normal_transfer.json](../../assets/WAVES/cdc_4_phase_handshake/cdc4_normal_transfer.json)

Four crossings: `r_req_src` rises, `r_ack_dst` rises, `r_req_src` falls,
`r_ack_dst` falls. Both ends finish at the 0 idle level.

#### Waveform 1.4: 4-Phase One-Sided Reset Is Safe

![4-phase one-sided reset is safe](../../assets/WAVES/cdc_4_phase_handshake/cdc4_asymmetric_reset_safe.png)

**Source:** [cdc4_asymmetric_reset_safe.json](../../assets/WAVES/cdc_4_phase_handshake/cdc4_asymmetric_reset_safe.json)

`rst_dst_n` asserts mid-transfer while the source runs:

1. The destination FSM returns to D_IDLE and `r_ack_dst` clears to 0.
2. The source is unaffected, still holding `r_req_src = 1` with data stable.
3. On release the destination re-observes `w_req_sync = 1`, treats it as a fresh
   request, and redoes the transfer.
4. The source sees the ack and completes normally.

Worst case is one transfer **repeated or dropped**, and only for a transfer
genuinely in flight. If the link is idle when the reset lands, the destination
sees `req = 0`, reads it as "nothing pending", and does nothing.

**Caveat -- duplicate delivery.** Step 3 re-delivers a transfer the destination
may already have accepted. If the consumer is not idempotent (a FIFO push, a
counter increment, a command queue), hold it in reset alongside the destination
FSM or drain it afterwards. Level encoding guarantees you never get a transfer
the source did not send; it does not guarantee exactly-once delivery.

### Async FIFO reset behavior

Gray/Johnson pointers are absolute positions, and each domain resets its own
pointer **and its crossed copy of the remote pointer** from the local reset:

```systemverilog
rd_ptr_gray_cross_inst / rd_ptr_gray2bin_inst  -> .rst_n (axi_wr_aresetn)  // local
wr_ptr_gray_cross_inst / wr_ptr_gray2bin_inst  -> .rst_n (axi_rd_aresetn)  // local
```

So a one-sided reset leaves that side self-consistent -- both pointers zero,
reads empty -- rather than desynchronized. There is no parity state to invert, so
nothing can be fabricated. This is a deliberate design property and the reason an
async FIFO is the safe default when reset domains are not shared.

**This covers reset ASSERTION, not reset RELEASE.** Each domain's reset must
still be released synchronously *within that domain* -- which is what
`reset_sync` (async assert, sync deassert) is for. A raw asynchronous release can
violate recovery/removal timing on the pointer flops, and if the two domains
release at sufficiently different times the FIFO can begin operating while one
side's synchronized copy of the remote pointer is still catching up. That window
is benign for an idle FIFO (it reads empty) but not if traffic starts
immediately. Hold traffic off until both domains are out of reset, or gate the
producer on a released-and-settled indication.

### Silicon evidence

This is not theoretical. On the Nexys A7 DDR2 characterization board, an APB CDC
using the 2-phase handshake had its core-side reset pulsed by `CTRL.soft_reset`
while the APB side stayed up. One phantom transfer entered a slave FSM that pairs
responses to requests positionally (`apb_slave.sv` returns whatever response sits
at the head of its skid buffer), and **every register read from then on returned
the previous register's value** -- lagged by ~3 transactions, permanently, until
reprogramming. Writes were unaffected, so it presented as a readback bug rather
than a CDC bug.

Replacing that handshake with `gaxi_fifo_async` fixed it: reads became stable
across `soft_reset`, verified on silicon.

### Safe usage checklist for 2-phase

**This is a hard stop, not a scorecard.** Every condition must hold. Failing any
one of them disqualifies the module -- there is no partial credit and no
mitigation short of changing the crossing or the reset topology.

Use `cdc_2_phase_handshake` only when **all** hold:

- [ ] `rst_src_n` and `rst_dst_n` assert and release together, **or** both derive
      from one reset no subsystem can pulse independently
- [ ] No soft reset, per-block reset, or power-domain reset touches one side alone
- [ ] The consumer correlates responses to requests by tag, not by position

If any box is unchecked, choose a level-encoded or pointer-encoded crossing.

### Recovering an existing design

| Option | Effort | Notes |
|--------|--------|-------|
| Move both domains onto a common reset | Low | Best when the split was accidental |
| Swap to `cdc_4_phase_handshake` | Low | Pin-compatible; level encoding self-recovers |
| Swap to `gaxi_fifo_async` | Medium | Absolute pointers, local-reset robustness, adds buffering |

: Options for recovering a design using 2-phase across independent resets

---

## cdc_synchronizer

Multi-flop synchronizer for **quasi-static** signals. Not a handshake -- there is
no flow control and no guarantee the destination sees every value.

```systemverilog
module cdc_synchronizer #(
    parameter int WIDTH      = 1,   // Bus width to synchronize
    parameter int FLOP_COUNT = 3    // Number of synchronizer stages (2-5)
) (
    input  logic             clk,       // Destination clock
    input  logic             rst_n,     // Asynchronous active-low reset
    input  logic [WIDTH-1:0] async_in,  // Asynchronous input from source domain
    output logic [WIDTH-1:0] sync_out   // Synchronized output in destination domain
);
```

| Parameter | Default | Range | Description |
|-----------|---------|-------|-------------|
| `WIDTH` | 1 | 1+ | Number of bits to synchronize |
| `FLOP_COUNT` | 3 | 2-5 | Synchronizer chain depth |

: cdc_synchronizer parameters

**Usage rules**

- Input must be **quasi-static**: it changes rarely enough, relative to the
  destination clock, that missing a transition is acceptable for the
  application. This is a statistical property, not a hard timing check the
  synchronizer enforces -- it will sample whatever is present. As a sizing rule
  of thumb, allow at least `FLOP_COUNT + 1` destination clocks between
  transitions; change faster than that and the destination can miss transitions
  entirely or sample mid-flight.
- For multi-bit buses, all bits must change simultaneously **or** be Gray coded.
- `FLOP_COUNT=2` for relaxed MTBF, `3` for production (default)
- Do **not** use for pulses (`sync_pulse`) or streaming data (`fifo_async`)

> **Gray-coded input must be REGISTERED in the source domain before it crosses.**
> The single-bit-change guarantee is a property of a registered counter
> sequence, not of the encoding in the abstract. Feeding this module a Gray
> value straight out of combinational logic re-introduces exactly the hazard
> Gray coding exists to remove: the bits arrive with different delays, and the
> synchronizer can latch a transient that was never a real state. Register the
> Gray value, then cross it. The same applies to a Gray value that can *jump*
> rather than increment by one -- multiple bits change and no encoding saves you.

---

## cdc_open_loop

Source holds `valid` + data stable for a stretch window long enough that the
destination cannot miss it. No acknowledge, so the lowest area and latency of the
data-carrying crossings -- at the cost of no backpressure.

| Parameter | Default | Description |
|-----------|---------|-------------|
| `DATA_WIDTH` | 8 | Width of the data bus |
| `STRETCH_CYCLES` | 8 | Source clocks to hold valid+data stable (`AUTO_STRETCH=0`) |
| `SYNC_STAGES` | 2 | Destination synchronizer depth (2-4) |
| `AUTO_STRETCH` | 0 | `0` = use `STRETCH_CYCLES`; `1` = compute from clock frequencies |
| `SRC_CLK_HZ` | 25_000_000 | Source clock frequency (`AUTO_STRETCH=1`) |
| `DST_CLK_HZ` | 100_000_000 | Destination clock frequency (`AUTO_STRETCH=1`) |

: cdc_open_loop parameters

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk_src` / `rst_src_n` | input | 1 | Source domain clock / async reset |
| `src_valid` | input | 1 | Single-cycle pulse: data is valid |
| `src_data` | input | DATA_WIDTH | Data to transfer |
| `src_busy` | output | 1 | High during stretch countdown |
| `clk_dst` / `rst_dst_n` | input | 1 | Destination domain clock / async reset |
| `dst_valid` | output | 1 | Single-cycle pulse: data latched |
| `dst_data` | output | DATA_WIDTH | Latched data, stable until next `dst_valid` |

: cdc_open_loop ports

**The failure mode to watch:** sending a new transfer before the previous one is
sampled. Without an acknowledge the source cannot know the destination latched
the data. Respect `src_busy`, or space transfers by at least
`SYNC_STAGES + 1` destination clocks.

---

## cdc_2_phase_handshake

Toggle (NRZ) closed-loop handshake. Two synchronizer crossings per transfer
instead of four.

> **Read [Reset Considerations](#reset-considerations) before choosing this
> module.** It is pin-compatible with the 4-phase variant but not behaviorally
> equivalent under independent resets.

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `DATA_WIDTH` | int | 8 | Width of the data bus (1+) |
| `SYNC_STAGES` | int | 3 | Synchronizer depth for req/ack (2 or 3) |
| `TIMEOUT_CYCLES` | int | 0 | 0 = disabled; >0 asserts `src_timeout` after stall |

: cdc_2_phase_handshake parameters

### Shared handshake interface

Both handshake modules expose an identical port list, which is why swapping them
is a one-word edit:

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk_src` / `rst_src_n` | input | 1 | Source domain clock / async reset |
| `src_valid` | input | 1 | Source indicates data valid |
| `src_ready` | output | 1 | Handshake ready (asserted when idle) |
| `src_data` | input | DATA_WIDTH | Data from source domain |
| `src_timeout` | output | 1 | Stall timeout (when `TIMEOUT_CYCLES > 0`) |
| `clk_dst` / `rst_dst_n` | input | 1 | Destination domain clock / async reset |
| `dst_valid` | output | 1 | Data valid to receiver |
| `dst_ready` | input | 1 | Receiver ready |
| `dst_data` | output | DATA_WIDTH | Data transferred to destination domain |

: Shared handshake interface ports

### Theory of operation

```
Source FSM
  S_IDLE      src_ready=1. On src_valid: latch data, toggle r_req_tog,
              drop src_ready, go to S_WAIT_ACK.
  S_WAIT_ACK  Wait for ack edge (w_ack_event). On edge: src_ready=1, S_IDLE.

Destination FSM
  D_IDLE        On req edge (w_req_event): copy data into r_dst_data,
                raise dst_valid, go to D_WAIT_READY.
  D_WAIT_READY  Hold dst_valid. On dst_ready: drop dst_valid, toggle
                r_ack_tog, return to D_IDLE.

Edge detection
  event = current_sync_output ^ previous_sync_output
```

### Swapping between variants

| Direction | Consequence |
|-----------|-------------|
| 4-phase -> 2-phase | Gains throughput. **Silently forfeits independent-reset tolerance.** Only safe when both domains share one reset. |
| 2-phase -> 4-phase | Costs roughly two extra synchronizer crossings (~2 x `SYNC_STAGES` clocks, so ~6 at the default of 3), split between the two domains. Always safe. |

: Consequences of swapping handshake variants

---

## cdc_4_phase_handshake

Level (RZ) closed-loop handshake: `req` rises, `ack` rises, `req` falls, `ack`
falls. Slower than 2-phase, and tolerant of independent domain resets.

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `DATA_WIDTH` | int | 8 | Width of the data bus (1 to 1024+) |
| `SYNC_STAGES` | int | 3 | Synchronizer depth for req/ack (2 or 3) |
| `TIMEOUT_CYCLES` | int | 0 | 0 = disabled; >0 asserts `src_timeout` after stall |
| `FAST_PATH` | bit | 0 | 1 = destination fast-path when `dst_ready` already high |

: cdc_4_phase_handshake parameters

Ports are identical to the [shared handshake interface](#shared-handshake-interface).

### Theory of operation

```
Source FSM
  S_IDLE          On src_valid: capture data, r_req_src=1, S_WAIT_ACK.
  S_WAIT_ACK      On synchronized ack: r_req_src=0, S_WAIT_ACK_CLR.
  S_WAIT_ACK_CLR  On ack cleared: src_ready=1, S_IDLE.

Destination FSM
  D_IDLE          On synchronized req: latch data, dst_valid=1, D_WAIT_READY.
  D_WAIT_READY    On dst_ready: r_ack_dst=1, dst_valid=0, D_WAIT_REQ_CLR.
  D_WAIT_REQ_CLR  On req cleared: r_ack_dst=0, D_IDLE.
```

**Data stability guarantee:** data is captured at REQ assertion and held until
ACK completion, so it is stable for the entire crossing regardless of clock
ratio.

**Latency:** four synchronizer crossings per transfer against two for 2-phase.
At the default `SYNC_STAGES=3` that is roughly 12 clocks of round trip against
6 -- counted in the clock domain each crossing lands in, so the wall-clock cost
depends on the src:dst frequency ratio. Treat these as order-of-magnitude, not
budgetable: measure your own configuration.

---

## Async FIFO Pointers (Gray and Johnson)

For streaming data, synchronize the read and write **pointers** of a dual-port
memory rather than the data. Pointers use an encoding where only one bit changes
per increment, so any sample during a transition yields either the old or the new
value -- never a corrupted intermediate. The memory itself needs no CDC.

```
Write Domain:                              Read Domain:
  wr_ptr (binary) ---> bin2gray --->        gray2bin ---> compare with rd_ptr
                        [sync N stages]                   for empty detection

  gray2bin <--- [sync N stages] <--- bin2gray <--- rd_ptr (binary)
  compare with wr_ptr for full detection
```

### Gray vs Johnson encoding

Both `fifo_async` (rtl/cdc) and `gaxi_fifo_async` (rtl/cdc) select the
encoding with a `USE_JOHNSON` parameter:

| `USE_JOHNSON` | Encoding | Pointer width | Converter | Legal DEPTH |
|---------------|----------|---------------|-----------|-------------|
| 0 (default) | Gray | `log2(DEPTH)+1` | `gray2bin` (combinational) | power of 2 only |
| 1 | Johnson | `DEPTH` | `johnson2bin` (combinational) | any depth, odd included |

: Async FIFO pointer encodings

An illegal combination (Gray with a non-power-of-2 depth) fails at
**elaboration** with an explicit `$error`, not at runtime.

#### State walk: why the pointers are different widths

Both encodings guarantee the same CDC-critical property -- exactly one bit
changes per increment -- but they buy it very differently. Walking a 3-bit Gray
counter through its full cycle and putting the equivalent Johnson counter beside
it shows why.

A 3-bit Gray counter has `2**3 = 8` states. To reach the same 8 states a Johnson
counter needs `2N = 8`, i.e. **4 bits** -- it only ever produces `2 x WIDTH`
states, not `2**WIDTH`. The Johnson sequence fills with ones from the LSB, then
flushes them back out with zeros; that is the whole counter
(`counter_johnson.sv:32`: `{counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]}`).

The two "which bit" columns give the **bit POSITION that flipped** (0 = LSB).
They are not counts. The Hamming-distance columns state the count explicitly,
and it is 1 on every row -- that is the property being demonstrated.

| Step | Gray (3-bit) | flips bit# | Ham. dist | Johnson (4-bit) | flips bit# | Ham. dist | Johnson phase |
|------|--------------|-----------|-----------|-----------------|-----------|-----------|---------------|
| 0 | `000` | 0 | 1 | `0000` | 0 | 1 | ones in |
| 1 | `001` | 1 | 1 | `0001` | 1 | 1 | ones in |
| 2 | `011` | 0 | 1 | `0011` | 2 | 1 | ones in |
| 3 | `010` | 2 | 1 | `0111` | 3 | 1 | ones in |
| 4 | `110` | 0 | 1 | `1111` | 0 | 1 | zeros in |
| 5 | `111` | 1 | 1 | `1110` | 1 | 1 | zeros in |
| 6 | `101` | 0 | 1 | `1100` | 2 | 1 | zeros in |
| 7 | `100` | 2 | 1 | `1000` | 3 | 1 | zeros in |
| wrap | -> `000` | 2 | 1 | -> `0000` | 3 | 1 | -- |

: 3-bit Gray vs the equivalent 4-bit Johnson counter, full cycle. "flips bit#" is a bit POSITION; "Ham. dist" is the number of bits that changed, which is 1 everywhere including the wrap.

Every step -- **including the wrap back to state 0** -- flips exactly one bit in
both encodings. Hamming distance 1 is the only property the synchronizer needs,
which is why both are safe to cross.

> **The Johnson wrap is single-bit, and this is easy to get wrong.** A reviewer
> of this document read the earlier "bit changed" column as a bit *count* and
> concluded the Johnson wrap `1000 -> 0000` changed four bits. It changes one
> (bit 3). A twisted-ring counter is specifically constructed so that the
> wrap is a single-bit transition like every other step -- that is what makes
> the `2N` cycle usable as a CDC pointer at all.

The cost difference is in the width, and it compounds:

| States needed (2 x DEPTH) | DEPTH | Gray pointer bits | Johnson pointer bits |
|---------------------------|-------|-------------------|----------------------|
| 8 | 4 | 3 | 4 |
| 16 | 8 | 4 | 8 |
| 32 | 16 | 5 | 16 |
| 64 | 32 | 6 | 32 |
| 128 | 64 | 7 | 64 |

: Pointer width by encoding -- Gray is logarithmic, Johnson is linear

Gray is `log2` in the state count; Johnson is linear. At DEPTH=4 the difference
is one flop; at DEPTH=64 it is 57 flops per pointer, and each pointer is
duplicated per domain and again per synchronizer stage. That is the entire
argument for Gray being the default -- and equally, why Johnson stays viable only
at the modest depths where non-power-of-2 sizing actually matters.

What Johnson buys for that width is the freedom to stop at any even count: its
`2N` progression lands on 6, 10, 14 just as naturally as 8 or 16, whereas Gray's
`2**N` can only land on powers of two.

### Sizing the depth

```
depth >= burst_length * (1 - read_rate / write_rate)
```

where `rate = freq * duty_cycle`. Round up, then apply the encoding's constraint:
Gray rounds to the next power of two; Johnson takes the depth you ask for.
The only elaboration check is `(USE_JOHNSON == 0) && ((DEPTH & (DEPTH-1)) != 0)`,
so Johnson imposes no restriction at all.

> **This formula assumes the reader keeps draining throughout the burst.** It
> sizes for a *sustained rate mismatch*, not for burst isolation. If the reader
> can stall completely -- arbitration loss, a blocked downstream, a paused
> consumer -- then nothing drains during the stall and you need
> `depth >= burst_length` to avoid dropping writes. Between those extremes, size
> for the worst-case drain rate the reader can guarantee, not its average.

One term the formula above leaves out: the full flag does not track the true
fill level instantly. It is derived from a pointer that has been synchronised
into the write domain, so it lags real reads by `N_FLOP_CROSS` write clocks.
Production sizing therefore adds `N_FLOP_CROSS` slots on top of the raw depth --
two for the default synchroniser, three if you have configured a third stage.
The worked example below shows the raw depth only, so that it lines up with the
storage-overhead tables that follow; add the margin before committing to a
number.

**Spreadsheet.** [`docs/fifo_depth_calculator_v2.xlsx`](../../../fifo_depth_calculator_v2.xlsx)
does this whole calculation -- rate-from-duty, raw depth, synchroniser margin,
then the Gray power-of-two and Johnson even-number rounding side by side, with
the slot and percentage saving between them. It carries worked example cases and
a one-page cheat sheet. Note that it deliberately does *not* model clock drift:
crystal tolerance is ppm-level and moves the answer by well under one slot over
any bounded burst, and a divergence large enough to matter is a steady-state
violation whose fix is back-pressure, not a deeper FIFO. To size a worst case,
enter the worst-case frequencies directly -- fastest writer, slowest reader.

**Worked example.** Writer at 100 MHz bursts 100 back-to-back writes; reader
pulls 1 word/clk at 80 MHz:

| Step | Value |
|------|-------|
| Burst duration | 100 / 100 MHz = 1 µs |
| Reads during burst | 1 µs × 80 MHz = 80 |
| Net build-up | 100 − 80 = **20 words** |
| Gray FIFO (power-of-2) | round up to **32** |
| Johnson FIFO (even) | **20** as-is |

: Worked depth-sizing example

Gray adds 12 unused slots, and the nominal overhead scales with data width:

| `DATA_WIDTH` | Gray depth 32 | Johnson depth 20 | Nominal saving |
|--------------|---------------|------------------|----------------|
| 32 b | 1024 b | 640 b | 384 b (38%) |
| 64 b | 2048 b | 1280 b | 768 b (38%) |
| 256 b | 8192 b | 5120 b | 3072 b (38%) |
| 1024 b | 32 768 b | 20 480 b | **12 288 b** (38%) |

: Nominal storage overhead of Gray depth rounding by data width

Those are *nominal* bit counts. Whether they translate into real area depends
entirely on how the array is implemented -- see the walkthrough below, which is
the case most people actually hit.

Add margin for synchronizer latency if you are near the safe depth -- the
backpressure to the writer lags real fill level by `N_FLOP_CROSS` write clocks.

### Walkthrough: is an even-depth FIFO worth it at 512 bits?

This is the question that motivates `USE_JOHNSON`, and the honest answer is
"sometimes" -- the naive 38% figure above is frequently zero in practice. Work it
through.

**Scenario.** A 512-bit streaming path. Writer at 250 MHz bursts 96 words
back-to-back; reader drains 1 word/clk at 200 MHz.

**Step 1 -- required depth.**

```
depth >= 96 * (1 - 200/250) = 96 * 0.2 = 19.2  ->  20 words
```

**Step 2 -- apply the encoding constraint.**

| Encoding | Legal depth | Chosen | Entries wasted |
|----------|-------------|--------|----------------|
| Gray (`USE_JOHNSON=0`) | power of 2 | 32 | 12 |
| Johnson (`USE_JOHNSON=1`) | any even | 20 | 0 |

: 512-bit walkthrough: depth after applying the encoding constraint

**Step 3 -- nominal storage delta.**

| | Depth | Bits |
|---|---|---|
| Gray | 32 x 512 | 16 384 b (2 KiB) |
| Johnson | 20 x 512 | 10 240 b (1.25 KiB) |
| **Delta** | 12 entries | **6 144 b (768 B)** |

: 512-bit walkthrough: nominal storage delta

**Step 4 -- what Johnson costs.** The pointer is `DEPTH` bits wide instead of
`log2(DEPTH)+1`, and it is duplicated per domain and again per synchronizer
stage. With `N_FLOP_CROSS=2`:

| | Gray (depth 32) | Johnson (depth 20) |
|---|---|---|
| Pointer width | 6 b | 20 b |
| Per domain: own binary + encoded pointer | 6 + 6 = 12 | 6 + 20 = 26 |
| Per domain: synchronized remote pointer | 2 x 6 = 12 | 2 x 20 = 40 |
| Per domain: gray->bin converter | 0 (combinational) | 0 (combinational) |
| **Both domains** | **~48 flops** | **~132 flops** |

: 512-bit walkthrough: pointer flop cost

So Johnson costs roughly **+84 flops** to save **6 144 memory bits**. If the
memory is flops, that is a ~73:1 win. If it is not, the trade can invert
completely.

**Step 5 -- the part that decides it: memory granularity.** `MEM_STYLE`
(`FIFO_AUTO` / `FIFO_SRL` / `FIFO_BRAM`) determines whether 12 fewer entries
costs 12 fewer entries of area:

| MEM_STYLE | Granularity | Depth 32 vs 20 | Verdict |
|-----------|-------------|----------------|---------|
| Flop array | 1 entry | 16 384 vs 10 240 flops | **Johnson wins big** -- saving is exactly proportional, and dwarfs the +84 pointer flops |
| `FIFO_SRL` | 32 deep per LUT (SRL32) | Both <= 32, so 512 LUTs either way | **No saving.** Johnson costs +84 flops for nothing |
| `FIFO_BRAM` | 512 deep x 72 b per BRAM | 512-bit width needs ceil(512/72) = 8 BRAMs, and both depths are far under 512 | **No saving.** Same 8 BRAMs either way |

: 512-bit walkthrough: whether the saving is real, by memory style

**Conclusion for this example.** At 512 bits and depth ~20, Johnson is a clear win
*only* if the array is implemented as flops. Under SRL or BRAM the depth rounding
is absorbed by the primitive's own granularity, and choosing Johnson is a pure
loss of +84 flops plus a wider pointer comparator on the critical path.

**When even-depth genuinely pays.**

1. **Flop-based arrays** -- no granularity, saving is proportional. The most
   common real win, and it grows with `DATA_WIDTH`.
2. **The depth is externally constrained, not free to round up.** If you need
   exactly 20 entries to cover a 20-beat burst, a credit limit, or a descriptor
   count, rounding to 32 is not "spare capacity", it is 12 entries of dead
   silicon you provisioned to satisfy an encoding.
3. **Crossing a primitive boundary.** If the rate analysis lands at 33 and Gray
   forces 64, an SRL32-based FIFO goes from 2 primitives per bit to 2 -- no help
   -- but a flop array pays the full 31 entries. Check where your required depth
   sits relative to the primitive's step size, not relative to the next power
   of two.

#### On an ASIC the granularity argument disappears

Everything in Step 5 above is an FPGA argument. SRL32 and BRAM have a fixed step
size, and that step size is what absorbs the rounding and erases Johnson's
advantage. On an ASIC there is no such step: both **register files** and
**compiled SRAM** are generated to a requested word count, and every memory
compiler in common use accepts an even depth. So the depth you compute is the
depth you instantiate, and an odd rounding to the next power of two is pure
wasted silicon rather than something a primitive was going to charge you for
anyway.

**Worked case: a required depth of 36.** Take the same 512-bit path, but with a
rate analysis that lands on 36 entries -- above 32, so Gray must round to 64.

| | Depth | Storage at 512 b |
|---|---|---|
| Gray (power of 2) | 64 | 32 768 b (4 KiB) |
| Johnson (even) | 36 | 18 432 b (2.25 KiB) |
| **Delta** | **28 entries** | **14 336 b (1.75 KiB)** |

: Depth-36 case: storage delta when Gray must round 36 up to 64

Gray pays for 28 entries it will never use -- 44 percent of the array -- because
36 is not a power of two. The pointer cost runs the other way, by the same
accounting as Step 4:

| | Gray (depth 64) | Johnson (depth 36) |
|---|---|---|
| Pointer width | 7 b | 36 b |
| Per domain: own binary + encoded pointer | 7 + 7 = 14 | 7 + 36 = 43 |
| Per domain: synchronized remote pointer | 2 x 7 = 14 | 2 x 36 = 72 |
| Per domain: bin converter | 0 (combinational) | 0 (combinational) |
| **Both domains** | **~56 flops** | **~230 flops** |

: Depth-36 case: pointer flop cost

Johnson costs about **+174 flops** to save **14 336 memory bits** -- roughly an
82:1 return, better than the depth-20 case because the rounding gap is wider.

**Which ASIC memory style.** At depth 36 both are available, and the choice is
about aspect ratio rather than about the encoding:

| Style | Even depth? | Fit at 36 x 512 |
|-------|-------------|-----------------|
| Flop array | Yes, no granularity at all | Works, but 18 432 flops is a lot of area and a synthesis burden |
| Register file | Yes, word count is a compiler argument | Good fit. Shallow and wide is what register files are for |
| Compiled SRAM | Yes, word count is a compiler argument | Works, but 36 words is shallow for SRAM; check the compiler's minimum depth and its area per bit at this aspect ratio |

: Depth-36 case: ASIC memory styles, all of which accept an even depth

The practical answer at this shape is usually a register file: it takes depth 36
directly, it is denser than a flop array, and it avoids the periphery overhead
that makes a 36-word SRAM inefficient. Confirm against your own compiler --
minimum depth, word-count granularity (some compilers step in multiples of 4 or
8 words, which would reintroduce a smaller version of the FPGA problem), and
area per bit at a shallow, wide aspect ratio.

**Rule of thumb.** Compute the required depth first. Then ask what the memory
maps to and what its step size is. Only if the rounding actually crosses a step
boundary -- or there is no step, as with flops, register files, and compiled
SRAM -- does `USE_JOHNSON=1` buy you anything. On an ASIC that condition is
usually met, so Johnson is worth pricing whenever the required depth is not
already a power of two. On an FPGA it usually is not met, and Gray is the
default: narrower pointers, and one less thing to reason about. (Both
converters are combinational -- `gray2bin` and `johnson2bin` alike -- so the
difference is pointer width, not a pipeline stage.)

---

## SDC constraints

Both handshakes need the control toggles constrained as bounded crossings, and
the quasi-static data bus constrained by `set_max_delay`, **not**
`set_false_path`:

```tcl
# 1. Req / Ack single-bit crossings
set_max_delay -datapath_only \
    -from [get_pins u_cdc/r_req_tog_reg/C] \
    -to   [get_pins u_cdc/r_req_sync_reg[0]/D] \
    <dst_period_ns>

set_max_delay -datapath_only \
    -from [get_pins u_cdc/r_ack_tog_reg/C] \
    -to   [get_pins u_cdc/r_ack_sync_reg[0]/D] \
    <src_period_ns>

# 2. Data bus (quasi-static, protected by the handshake)
set_max_delay -datapath_only \
    -from [get_pins u_cdc/r_src_data_hold_reg[*]/C] \
    -to   [get_pins u_cdc/r_dst_data_reg[*]/D] \
    <dst_period_ns>
```

**Why `-datapath_only`, and why not `set_false_path`:**

- `set_false_path` tells the tool to ignore the path entirely. The data bus is
  then free to take arbitrarily long, but the handshake only holds it stable for
  a bounded window -- so the destination can latch a value that has partially
  updated. The crossing is unconstrained, not safe.
- `set_max_delay` **without** `-datapath_only` still includes clock skew and
  clock-uncertainty terms in the calculation. Across asynchronous domains those
  terms are meaningless -- the tool has no defined phase relationship to work
  from -- so you get pessimistic, unfixable violations that tempt people back to
  `set_false_path`.
- `set_max_delay -datapath_only` constrains **only the combinational data-path
  delay** from source register to destination register, which is exactly the
  quantity that must fit inside the handshake's stable window. This is the one
  that expresses the real requirement.

Set the value to the destination clock period (or the source period, for the
ack/return direction) unless you have a specific reason to tighten it.

---

## Common mistakes

**1. Multi-flop synchronizer on a multi-bit bus that changes simultaneously.**
Safe only for single-bit or Gray-coded values. If multiple bits change at once,
different bits may be sampled from different time points, producing a value that
never existed. Fix: handshake or async FIFO.

**2. `set_false_path` on CDC data buses.** It tells the tool to ignore timing
entirely, but the data bus must arrive within a bounded window. Use
`set_max_delay -datapath_only`.

**3. Assuming async FIFO depth 2 is enough.** Depth 2 has one usable entry, and
synchronized pointers lag by `SYNC_STAGES` cycles. Use depth >= 4.

**4. Open-loop transfer before the previous one is sampled.** Without an ack the
first transfer is silently lost. Minimum spacing `SYNC_STAGES + 1` destination
clocks.

**5. Choosing 2-phase for speed without checking the reset domains.** See
[Reset Considerations](#reset-considerations). This one has cost real silicon
debug time.

---

## Verification status

The formal harness at `formal/amba/cdc_handshake/formal_cdc_handshake.sv` wires
the DUT as:

```systemverilog
.clk_src (clk),  .rst_src_n (rst_n),
.clk_dst (clk),  .rst_dst_n (rst_n),
```

Single clock, single reset for both domains. The proof therefore **cannot express
asymmetric reset or asynchronous clocks**. Treat "formally verified" for the
handshakes as scoped to protocol correctness under a common clock and reset.

The reset behavior described in this document is argued from the RTL encoding and
-- for the 2-phase hazard -- confirmed on silicon. It is **not** currently covered
by the formal proof or by a directed test. Extending the harness to independent
clocks and resets would cover it, and would be expected to fail on the 2-phase
variant.

---

## Module reference

| Module | RTL | Filelist | Test |
|--------|-----|----------|------|
| `cdc_synchronizer` | `rtl/cdc/cdc_synchronizer.sv` | `cdc_synchronizer.f` | -- |
| `cdc_open_loop` | `rtl/cdc/cdc_open_loop.sv` | `cdc_open_loop.f` | `val/amba/test_cdc_open_loop.py` |
| `cdc_2_phase_handshake` | `rtl/cdc/cdc_2_phase_handshake.sv` | `cdc_2_phase_handshake.f` | `val/amba/test_cdc_2_phase_handshake.py` |
| `cdc_4_phase_handshake` | `rtl/cdc/cdc_4_phase_handshake.sv` | `cdc_4_phase_handshake.f` | `val/amba/test_cdc_4_phase_handshake.py` |
| `fifo_async` | `rtl/cdc/fifo_async.sv` | `rtl/common/filelists/fifo_async.f` | `val/common/test_fifo_buffer_async.py` |
| `gaxi_fifo_async` | `rtl/cdc/gaxi_fifo_async.sv` | -- | -- |

: CDC module reference

**Protocol-level CDC built on these blocks:** `apb_slave_cdc`,
`apb_slave_cdc_cg`, `apb5_slave_cdc`, `apb5_slave_cdc_cg`,
`gaxi_skid_buffer_async`, `axi4_to_apb_shim`.

**Supporting primitives (rtl/common):** `glitch_free_n_dff_arn`, `bin2gray`,
`gray2bin`, `johnson2bin`, `counter_bingray`, `counter_johnson`, `reset_sync`,
`sync_pulse`.

---

## Navigation

- [Back to CDC Index](README.md)
- [Back to rtl-amba Index](../index.md)
