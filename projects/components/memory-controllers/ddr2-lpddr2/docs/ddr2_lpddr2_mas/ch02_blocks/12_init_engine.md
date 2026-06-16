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

# Init Engine (`init_engine_fub`)

**Module:** `init_engine_fub.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent:** `ddr2_lpddr2_ctrl`
**Status:** Draft v0.1

> Architectural context: HAS §3.5. The HAS flow diagram is in `ddr2_lpddr2_has/assets/mermaid/05_init_engine_flow.png` and is the canonical step-decode reference — this section is the implementation view (ROM organization, step encoding, FSM, bypass path into bank machines, multi-rank MRS loop, sim shortcut).

---

## Purpose

`init_engine_fub` walks the JEDEC cold-boot DRAM initialization sequence — the deterministic recipe of CKE wiggles, RESET_N pulses, MRS writes, ZQ calibration, and PRE/REF settling cycles that must complete before any normal traffic can issue.

The init sequence is **memtype-specific** (DDR2 vs LPDDR2 differ at MRS layout, ZQ flow, and the existence of a RESET_N pin), and **partially multi-rank-aware** (per-rank MRS loads and per-rank ZQ calibration retries). The FUB resolves both via a single microprogram architecture: a small step-table ROM per memtype, a step interpreter FSM, and a bypass path that pushes commands directly into the bank-machine and command-encoder fabric without going through the FR-FCFS scheduler.

The init engine is "above" the scheduler in the controller's command-priority hierarchy. While `init_in_progress` is asserted, the scheduler is gated (per §2.7 Stage 2 `init_mask`); only the init engine drives DRAM commands. Once init completes, control hands to the scheduler and refresh manager for normal operation.

---

## Synthesis Parameters

| Parameter            | Source            | Effect                                                                      |
|----------------------|-------------------|-----------------------------------------------------------------------------|
| `MEMTYPE`            | top               | Picks which step-table ROM is instantiated; tied to `cmd_encoder` MEMTYPE   |
| `NUM_RANKS`          | top               | Per-rank MRS loop count; per-rank ZQ calibration retries                    |
| `SIM_INIT_SCALE`     | top (default 1)   | Divides post-step delays for sim runs (silicon always 1)                    |
| `INIT_ROM_DEPTH`     | derived           | Number of entries in the active step-table ROM (DDR2 ~32, LPDDR2 ~28)        |
| `STEP_PAYLOAD_WIDTH` | derived           | Width of the per-step payload field (carries MRS values, delay counts, etc.) |

---

## Microprogram ROM Organization

The init sequence is encoded as a small ROM of step records. Each step has the same fixed-width encoding regardless of opcode — the opcode field tells the interpreter how to read the payload field.

### Step Record Encoding

| Field          | Width         | Description                                                  |
|----------------|---------------|--------------------------------------------------------------|
| `opcode`       | 3             | One of `SET_CTRL_BITS`, `DELAY`, `MRS_LOAD`, `ISSUE_CMD`, `WAIT_FOR_BIT`, `END` |
| `payload`      | 20            | Opcode-dependent — see decoder table below                   |
| `post_delay`   | 12            | Cycles to wait after the step completes (scaled by `SIM_INIT_SCALE`) |
| `per_rank`     | 1             | When 1, the step iterates over all ranks (only meaningful for `MRS_LOAD` and `ISSUE_CMD`) |

Total per-step width: 36 bits. ROM depth is ~32 for DDR2 and ~28 for LPDDR2; total ROM footprint ~150 bytes per memtype.

### Opcode Decoder

| Opcode           | Payload Interpretation                                                                          |
|------------------|-------------------------------------------------------------------------------------------------|
| `SET_CTRL_BITS`  | `{cke[NR-1:0], odt[NR-1:0], reset_n}` — drive these output-pin states for the duration of the step |
| `DELAY`          | `delay_cycles[19:0]` — explicit delay above and beyond `post_delay`; used for very-long settling delays like tINIT0 (200 µs) |
| `MRS_LOAD`       | `{mr_index[2:0], mr_value[15:0]}` — issue MRS to MR `mr_index` with value `mr_value`. When `per_rank == 1`, iterates over ranks 0 .. NR−1 |
| `ISSUE_CMD`      | `{op[3:0], bank[2:0], row_or_col[13:0]}` — issue raw DRAM command (PREA, REF, ZQCS, ZQCL). When `per_rank`, issues to each rank |
| `WAIT_FOR_BIT`   | `{bit_id[3:0], timeout_us[15:0]}` — poll a status bit (e.g., `dfi_init_complete`); fail to `INIT_ERROR` on timeout |
| `END`            | None — assert `init_done_o`, transition to ACTIVE                                              |

### Memtype Selection

```systemverilog
generate
    if (MEMTYPE == "DDR2") begin : g_rom_ddr2
        init_steps_ddr2_rom #(
            .DEPTH(INIT_ROM_DEPTH)
        ) u_rom (.addr(step_pc_o), .data(step_record_i));
    end
    else begin : g_rom_lpddr2
        init_steps_lpddr2_rom #(
            .DEPTH(INIT_ROM_DEPTH)
        ) u_rom (.addr(step_pc_o), .data(step_record_i));
    end
endgenerate
```

The ROMs live in `rtl/macro/init_steps_ddr2_rom.sv` and `rtl/macro/init_steps_lpddr2_rom.sv`. They are written by hand from JEDEC initialization sequences and are *not* generated — the sequences are deliberate, short, and reviewable.

The choice of separate ROM modules (rather than a single ROM with a memtype-indexed lookup) keeps the unused ROM out of the synthesis pass when `MEMTYPE` is fixed at elaboration. The resulting bit-stream contains only the relevant init recipe.

---

## FSM

The interpreter is a five-state FSM:

| State              | Held while                                                            | Exits via                                                  |
|--------------------|-----------------------------------------------------------------------|------------------------------------------------------------|
| `IDLE`             | `CTRL.init_start` not asserted; controller sits in POST_RESET         | `init_start` rising edge → `FETCH`                         |
| `FETCH`            | One cycle to address the ROM and latch the step record                | Step record valid → `EXECUTE`                              |
| `EXECUTE`          | Step's action being performed (drive ctrl bits, issue command, etc.)   | Action complete → `POST_DELAY` (if `post_delay > 0`) or `FETCH` (next step) |
| `POST_DELAY`       | Down-counter from `post_delay` (scaled by `SIM_INIT_SCALE`)            | Counter == 0 → `FETCH` (next step), or `END` if last        |
| `INIT_ERROR`       | A `WAIT_FOR_BIT` timed out or ZQ retried out — terminal state          | Software writes `CTRL.init_force_restart` → `IDLE`         |

There is no separate state per opcode — the `EXECUTE` state runs a small combinational dispatch on the opcode field. This keeps the FSM minimal and the `init_step_dbg` CSR (per HAS §6.3 STATUS) reports the step PC directly.

---

## Step Execution Detail

### `SET_CTRL_BITS`

Drives the controller's output-pin staging registers:

```
dfi_cke[NR-1:0] = payload[NR-1+NR : NR]
dfi_odt[NR-1:0] = payload[NR-1 : 0]
dfi_reset_n     = payload[NR*2]
```

These outputs route through `power_state_fub` → `odt_ctrl_fub` → `gear_dfi_fub` to the DFI master pins. While init is in progress, the power-state FSM mirrors the init engine's `dfi_cke` instead of its own.

### `DELAY`

Loads a separate `long_delay_cnt` register with `payload[19:0]` and waits in `EXECUTE` until it reaches zero. `SIM_INIT_SCALE > 1` divides the load value at elaboration *and* at run-time CSR write (so the runtime override `INIT_TUNING.init_timeout_ms` honors the scale too). For tINIT0-class delays (200 µs at 200 MHz = 40 K cycles), this counter is 20 bits.

### `MRS_LOAD`

Issues an MRS DRAM command through the bypass-into-encoder path:

```
init_cmd_op_o        = MRS
init_cmd_bank_o      = mr_index           // the bank field encodes the MR index in JEDEC
init_cmd_row_or_col  = mr_value
init_cmd_rank_o      = current_rank       // iterates 0..NR-1 if per_rank
init_cmd_strobe_o    = 1
```

The bank machines see the MRS issue and don't change state (MRS doesn't affect bank state); the command flows through `cmd_encoder` → `gear_dfi` to the DFI master. When `per_rank == 1`, the FSM uses a small `rank_iter` counter and stays in `EXECUTE` across NR cycles, advancing one rank per MC clock. tMRD-class minimum-gap is honored via `post_delay`.

### `ISSUE_CMD`

Generic command issue — same path as MRS_LOAD but with the opcode and bank/column from the payload. Used for PREA (all-bank precharge), REF (initial refresh batches), ZQCL (init-time ZQ calibration long), and ZQCS (init-time ZQ short).

### `WAIT_FOR_BIT`

Polls a controller-internal status signal (`bit_id` is one of: `dfi_init_complete`, `zq_done`, `mrs_ack`, etc.). The interpreter holds `EXECUTE` until the bit asserts. A timeout counter loaded from `payload[19:4]` (in microseconds, scaled appropriately) drives `INIT_ERROR` if the bit doesn't assert in time.

For ZQ calibration specifically, the timeout-retry path consults `INIT_TUNING.zq_retries`:

```
if (timeout AND zq_retry_cnt < zq_retries):
    zq_retry_cnt = zq_retry_cnt + 1
    re-execute ZQ command and re-poll        // back-edge to FETCH on same step
else if (timeout AND retries exhausted):
    → INIT_ERROR
```

### `END`

Asserts `init_done_o` for one cycle (driving the `irq_init_done` IRQ and `STATUS.init_done = 1`), then transitions to `IDLE` for the next init request.

---

## Bypass Path Into Bank Machines

Init commands do not go through the scheduler. Instead, the init engine has a direct path into each bank machine and into the command encoder, via the `init_cmd_if` interface declared in §2.9:

```
init_cmd_op_o      → all bank machines (each watches its own rank/bank match)
init_cmd_rank_o    → cmd_encoder rank-select
init_cmd_bank_o    → cmd_encoder bank-select; bank_machine identity match
init_cmd_row_or_col → cmd_encoder address operand
init_cmd_strobe_o  → all bank machines and cmd_encoder
```

Bank machines treat init commands as if they came from the scheduler — they transition states accordingly (PRE → PRECHARGING, REF → REFRESHING, etc.). The scheduler does not observe these commands' issue; from its point of view, the bus is just "blocked by init."

The command encoder accepts init commands on the bypass path and serializes them onto DFI through the same gear logic as scheduler-issued commands. There is no separate init-mode signal in `cmd_encoder`; the path is symmetric.

---

## Multi-Rank Init Loop

For per-rank steps (`per_rank == 1`), the FSM uses a `rank_iter` counter:

```
EXECUTE state:
    if (per_rank):
        issue command to rank_iter
        rank_iter = (rank_iter + 1) % NR
        if (rank_iter == 0):                  // wrapped, all ranks done
            advance to POST_DELAY / FETCH
        else:
            stay in EXECUTE (next cycle issues to next rank)
    else:
        issue command (rank-agnostic; CS_n[*] = 0)
        advance to POST_DELAY / FETCH
```

This means a `per_rank` MRS_LOAD step takes NR cycles in EXECUTE. For NR=4, eight cycles for an MR0+MR1+MR2+MR3 sequence on 4 ranks — small overhead in the init context (where individual delays run hundreds of microseconds anyway).

The `tMRD` minimum-gap between MRS to the same rank is honored via `post_delay`. The minimum-gap between MRS to *different* ranks is shorter (`tMRD_inter_rank`, typically 0 or 1 cycle) and is absorbed by the natural pipelining of the EXECUTE loop.

---

## SIM_INIT_SCALE — The 200µs → 200 cycles trick

JEDEC init has several multi-hundred-µs delays (tINIT0 = 200 µs, tINIT1 = 500 µs, tINIT3 = 200 µs). At 200 MHz silicon clock, that's 40,000 cycles each — and simulation at cycle-accurate speeds would take minutes per test just for init.

`SIM_INIT_SCALE` divides all delay loads at elaboration:

```
effective_delay = delay_from_rom / SIM_INIT_SCALE
```

Setting `SIM_INIT_SCALE = 10000` reduces tINIT0 from 40 K cycles to 4 cycles in sim. Silicon always uses `SIM_INIT_SCALE = 1`; the scale is parameter-only, not CSR (writing it would corrupt silicon init).

The scale applies to both `DELAY` opcode payloads and `post_delay` fields. The `WAIT_FOR_BIT` timeout is *not* scaled — timing-out on a DFI handshake should still be detected in sim.

---

## Init-in-Progress Gating

While the FSM is anywhere except `IDLE`:

- `init_in_progress_o = 1`
- Scheduler is gated (per §2.7 Stage 2)
- Refresh manager is gated (per §2.11 FSM)
- Power-state FSM mirrors init's `dfi_cke` outputs
- AXI4 slave is *not* gated at the AXI boundary (AXI bursts can accumulate in `aw_buf` / `ar_buf` while init runs); they just can't reach DFI

When `END` executes, `init_in_progress_o` drops, scheduler and refresh resume, and accumulated AXI bursts begin issuing through the normal path.

---

## Interface

### Outputs to Bank Machines (init bypass)

| Signal              | Direction | Width                | Description                                          |
|---------------------|-----------|----------------------|------------------------------------------------------|
| `init_cmd_strobe_o` | output    | 1                    | A new init command is being issued this cycle        |
| `init_cmd_op_o`     | output    | 4                    | DRAM command opcode (same encoding as scheduler issue) |
| `init_cmd_rank_o`   | output    | `$clog2(NR)`         | Target rank                                          |
| `init_cmd_bank_o`   | output    | `$clog2(NB)`         | Target bank / MR index for MRS                       |
| `init_cmd_row_o`    | output    | `ROW_WIDTH`          | Row (for ACT) or MR value (for MRS)                  |
| `init_cmd_col_o`    | output    | `COL_WIDTH`          | Column (for RD/WR; init doesn't normally use)        |

### Outputs to Power-State / ODT / Pins

| Signal              | Direction | Width  | Description                                                |
|---------------------|-----------|--------|------------------------------------------------------------|
| `init_cke_o[NR]`    | output    | NR     | Direct CKE drive during init (`power_state` muxes this in)  |
| `init_odt_o[NR]`    | output    | NR     | Direct ODT drive during init                                |
| `init_reset_n_o`    | output    | 1      | DDR2 RESET_N pin drive (tied 1 for LPDDR2 builds)           |

### Status / IRQ Outputs

| Signal                  | Direction | Width  | Description                                          |
|-------------------------|-----------|--------|------------------------------------------------------|
| `init_in_progress_o`    | output    | 1      | High during any non-IDLE state                       |
| `init_done_o`           | output    | 1      | One-cycle pulse on `END`; drives `irq_init_done`     |
| `init_error_o`          | output    | 1      | Latched on `INIT_ERROR`; drives `irq_init_error`     |
| `init_step_pc_o`        | output    | 8      | Current step PC; drives `STATUS.init_step_dbg`       |

### Inputs from CSR

| Signal                       | Direction | Width  | Source                                          |
|------------------------------|-----------|--------|-------------------------------------------------|
| `cfg_init_start_i`           | input     | 1      | `CTRL.init_start` (rising edge starts)          |
| `cfg_init_force_restart_i`   | input     | 1      | `CTRL.init_force_restart`                       |
| `cfg_zq_retries_i`           | input     | 4      | `INIT_TUNING.zq_retries`                        |
| `cfg_init_timeout_ms_i`      | input     | 8      | `INIT_TUNING.init_timeout_ms`                   |
| `cfg_mr_values_i[4]`         | input     | 16 × 4 | `MR0..MR3` from CSR (override the ROM default)  |

The `MR0..MR3` CSR override path is important — software writes the MR values before asserting `init_start`, and the init engine substitutes them for the ROM-baked defaults during MRS_LOAD steps. This is how the LPDDR2 boot agent picks burst length, CAS latency, etc. without re-ROM-ing the controller.

### Inputs from DFI (status polling)

| Signal                  | Direction | Width  | Source                                          |
|-------------------------|-----------|--------|-------------------------------------------------|
| `dfi_init_complete_i`   | input     | 1      | DFI status sub-interface                        |
| `zq_done_i`             | input     | 1      | Internal: ZQ window expired without error       |
| `mrs_ack_i`             | input     | 1      | Bank machine acknowledges MRS settled            |

---

## CSR Hooks

| CSR field                          | Source                                  | Use case                                |
|------------------------------------|-----------------------------------------|-----------------------------------------|
| `STATUS.init_done` (R)             | Latched `init_done_o`                  | Software polls for init complete         |
| `STATUS.init_error` (R/clear)      | Latched `init_error_o`                  | Software polls for init failure          |
| `STATUS.init_step_dbg` (R)         | `init_step_pc_o`                        | Bring-up: where did init get stuck?     |
| `OBS_INIT_DURATION_MS` (R)         | Total init duration counter             | Telemetry: how long did init take       |

---

## Verification Notes (cocotb test plan)

| Scenario                                                                          | What it proves                                              |
|-----------------------------------------------------------------------------------|-------------------------------------------------------------|
| DDR2 init from cold reset to `init_done`                                          | Full DDR2 step sequence executes                            |
| LPDDR2 init from cold reset to `init_done`                                        | Full LPDDR2 step sequence executes                          |
| Multi-rank init (NR=2): each MRS_LOAD step issues to both ranks                   | Per-rank MRS loop                                           |
| `WAIT_FOR_BIT dfi_init_complete` times out → `INIT_ERROR`                         | Timeout path                                                |
| ZQ calibration fails, retries `zq_retries` times, then `INIT_ERROR`               | ZQ retry logic                                              |
| Software overrides MR0 via CSR; init uses the override, not ROM default          | MR override path                                            |
| `SIM_INIT_SCALE = 10000`: tINIT0 delay completes in 4 cycles instead of 40 K      | Sim shortcut works                                          |
| `init_force_restart` mid-sequence → `IDLE` → restart from step 0                  | Restart path                                                |
| AXI bursts queued during init → no DFI issue until `init_done` asserts            | Init-in-progress gating                                     |
| Scheduler `init_mask` correctly blocks normal traffic during init                 | Cross-FUB integration                                       |
| Init completes; refresh manager's first `wants_refresh` fires after at least tREFI cycles | Refresh handoff timing                              |

---

## Open Questions / Future Work

- **MR4 readback during init.** LPDDR2 requires reading MR4 to detect device temperature class. Currently the init engine doesn't do this — it leaves MR4 readback to the post-init power-state FSM. Could fold it into the init sequence (as a `WAIT_FOR_BIT` or a new `MR_READ` opcode), at the cost of a slightly longer init. Likely worth doing in v2 to remove the post-init MR4 race.
- **Step ROM versioning.** When silicon ships and a new DRAM part requires a tweaked init sequence, the ROM has to change. Should there be a CSR-side "ROM patch" path (writeable RAM that overlays specific ROM entries)? Adds CSR area but enables in-field updates. Punt until a real DRAM-compat issue forces the question.
- **Parallel multi-rank init.** Currently the per-rank loop is serial — NR cycles per per-rank step. Could issue MRS to multiple ranks in parallel (broadcast MRS with CS_n driven on multiple ranks). Saves init cycles at the cost of more cross-rank gate logic. Probably not worth it; init runs once at boot.
- **Soft-reset semantics during init.** If `mc_rst_n` asserts during init, the FUB cleanly returns to IDLE. But if `soft_reset` (CSR write) asserts during init, behavior is currently to also return to IDLE. Should the CSR soft-reset complete the current step first to avoid DRAM in an inconsistent state? Worth a verification scenario to document the current behavior.
