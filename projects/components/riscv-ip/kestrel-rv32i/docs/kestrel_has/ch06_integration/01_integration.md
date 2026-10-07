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

# Integration Guide

## Embedding Recipe (No Loader)

1. **Compile the closure.** Consume `rtl/filelists/kestrel_all.f` (see the filelist table below). It pulls the package, all five FUBs, and the core top.
2. **Provide two memories honoring the contract.** 32-bit-wide, combinational read, per-byte write merge on the data port (`dmem_wstrb`). The fetch port has no strobes — reads only.
3. **Tie the control surface.** One clock, one active-low reset. Set `RESET_ADDR` to the image's entry address.
4. **Observe.** Route the RVFI channel and `halt`/`halt_cause` to your trace fabric; they are the defined observability surface.

## Embedding Recipe (Loader / Board)

1. **Compile the closure.** `kestrel_all.f` includes the loader; it composes the repo's `axil4_slave_wr`/`axil4_slave_rd` leaf slaves through their own filelists.
2. **One clock domain.** `aclk == clk`, `aresetn == rst_n`. The core runs on the loader's `core_rst_n`, not on `rst_n` directly — the loader is the reset sequencer.
3. **Connect an AXIL master** (host CPU, DMA, or debug port) to `s_axil_*` and follow the programming sequence in Chapter 4: reset → stream image → (optional readback) → write `CTRL.run = 1` → run to halt.
4. **Set `RESET_ADDR`** to the image link base; the used address range must fall in the loader window (low 18 bits inside the imem/dmem regions).
5. **Sample before run.** The core fetches `RESET_ADDR` the cycle the `CTRL.run` write commits — arm any RVFI trace capture before issuing it.

## Filelists to Consume

| Filelist | Contents | Environment |
|----------|----------|-------------|
| `rtl/filelists/kestrel_pkg.f` | The package alone (enums, halt causes) | `$KESTREL_ROOT` |
| `rtl/filelists/fub/*.f` | One filelist per FUB (alu, decode, imm_gen, regfile, mem_loader), each a complete closure including the package and shared includes | `$KESTREL_ROOT`, `$REPO_ROOT` (loader pulls `rtl/amba` leaf slaves and `reset_defs.f`) |
| `rtl/filelists/top/kestrel_core.f` | The core top plus its FUB closures | `$KESTREL_ROOT`, `$REPO_ROOT` |
| `rtl/filelists/kestrel_all.f` | Master list: `-f` of everything above; the whole-area compile closure | `$KESTREL_ROOT`, `$REPO_ROOT` |
| `dv/filelists/kestrel_tb.f` | The two simulation TB tops on top of `kestrel_all.f` | `$KESTREL_ROOT` |

: Filelists (`KESTREL_ROOT` = the `kestrel-rv32i` directory; `REPO_ROOT` = the RTLDesignSherpa checkout root)

The filelists are the supported compile interface; do not hand-list sources. Both environment variables are registered by the repo's DV framework (`bin/filelist_registry.py`) and by the simulation Makefiles.

## Verification Hooks

kestrel was built RVFI-first: the retire port is the defined observation channel, present from the first vertical slice.

| Hook | Signals | Use |
|------|---------|-----|
| RVFI retire channel | 17 `rvfi_*` ports | Full-field diff against a golden model per retired beat; the basis of the cocotb harness and riscv-formal |
| Halt observability | `halt`, `halt_cause` | Detect program end, classify the cause, sample the post-halt hold |
| Data-port watch | `dmem_req/addr/wstrb/wdata` | tohost-mailbox watching on the store port; memory-contract checks (rotated strobes, retry addressing) |
| Loader taps | `core_rst_n`, `o_dbg_busy_wr`, `o_dbg_busy_rd` | Load-mode isolation and AXIL backpressure checks |

: Observability hooks

The V&V cross-reference is the six testplans in `dv/testplans/`: `kestrel_core` (18 scenarios, including the 42-test rv32ui battery, spike lockstep, constrained-random fuzz, and coverage closure), `kestrel_mem_loader` (ML-01..ML-09, including the golden battery over AXIL), and per-FUB plans for `kestrel_alu`, `kestrel_decode`, `kestrel_imm_gen`, and `kestrel_regfile`. Independent of simulation, riscv-formal runs 42 bounded-model-checking proofs (37 instruction models + 5 consistency checks) against the RVFI port — 42/42 PASS at depth 6. Regeneration commands are recorded in each testplan.

## Known Limitations

1. **No trap delivery.** All four spec-mandated trap events halt the core instead; recovery requires reset. Real traps arrive at rung 3 (peregrine).
2. **CSR stub is not CSR support.** Reads return zero, writes drop; anything needing real CSR state (trap handlers, counters, feature probing) is out of contract.
3. **No interrupt inputs, no debug mode, no MMU/PMP.**
4. **Cross-word accesses are not atomic** and occupy two cycles; RVWMO is satisfied vacuously, not by ordering hardware.
5. **No store-to-fetch coherence in the core.** Self-modifying code requires a memory system that unifies the ports (the testbench and the loader both do, by construction).
6. **Loader image window.** Core-visible image data is limited to 16 KB per region (word-indexed slots of a 64 KB array), the byte map aliases every `0x4000`, and the module header's `addr[15:2]` wording describes intent — the implemented index slice is `addr[13:0]` on every port, which is the convention this specification documents.
7. **Loader regions are exactly 64 KB + 64 KB.** Images larger than the window, or linked so their active range exceeds the low-18-bit window, will not load correctly.
8. **Power-up memory content is undefined in hardware** (the simulation zero-initializes for determinism); always load an image before run.

---

**Last Updated:** 2026-10-07
