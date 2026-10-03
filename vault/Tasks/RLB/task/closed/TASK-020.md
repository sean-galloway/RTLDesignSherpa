# TASK-020: the rlb_top MAS has the integration story; the remaining chapters and an executed programming model are still open

**Status:** closed 2026-10-03 — all four open items resolved.

**Resolution (2026-10-03):**

1. All six planned chapters written: ch02 01-03 (crossbar, interrupt fabric,
   cascade), ch03 02-03 (APB4 protocol at the boundary, per-block interrupt
   pin reference), ch04 03 (ACPI sleep/wake sequencing).
2. The programming model was executed as firmware-shaped host programs
   (`dv/host/rlb_bringup_programs.py`, board-portable) driven by
   `dv/tests/test_rlb_top_bringup.py` — bring-up runs from the book alone,
   never calling the DV helpers it was transcribed from. Executing it found
   TWO defects in the book itself: `IOWIN` was written 0x010 (actual 0x004
   per ioapic_mas ch05; write completes PSLVERR) and `PIC_STATUS` was written
   0x018 (actual 0x028 per the pic_8259 RDL; 0x018 is OCW2, so the
   init-complete check never passes). Both fixed in the book.
3. Diagrams: `assets/mermaid/rlb_integration_hierarchy` and
   `rlb_interrupt_fabric`, rendered to png through the standard mmdc
   Makefile route and embedded in ch01 architecture and ch02 fabric.
4. hpet README prose now uses `TIMER_CONFIG.timer_32mode` /
   `TIMER_CONFIG.timer_int_enable` per the RDL (direction labels re-expressed
   in the new field's polarity).

**Residual:** board execution of the bring-up program awaits a future FPGA
system target that instantiates rlb_top — none exists today (no rlb
reference under projects/fpga-systems). The program's bus boundary
(`write32`/`read32`) is shaped for a UARTAxiBridge port exactly so that
follow-up is a binding, not a rewrite.

## Why this exists

`rlb_top` is 990 lines, twelve instances, and the only place in the subsystem
where the address map, the interrupt fabric and the 8259 cascade exist. Until
2026-09-30 it had no specification: nine per-block MAS books shipped as PDFs and
the integration level had none. Worse, the two facts a reader most needs -
**which line each block's interrupt lands on**, and **the order the subsystem has
to be brought up in** - lived only in `dv/tbclasses/rlb_top/`. Measured before
the work started:

- `pit_timer_irq`, `uart_irq`, `gpio_irq`: **0** mentions in any `.md`, 3-4 in DV code
- the IOAPIC delivery vector rule: **0** markdown hits, 6 DV-code hits
- only 3 of 9 books had a `ch04_programming` chapter at all

The tenth book (`docs/rlb_top_mas/`) now carries that content. This item is what
the book does **not** yet do.

## What is done

- `docs/rlb_top_mas/` created following the nine-book convention: index, styles
  YAML, README, `ch01`-`ch05`, registered in `generate_mas_pdf.sh`
- The source-to-line routing table written down, with **convention versus
  choice** distinguished: IRQ0/4/8/9 from the published typical-assignment table
  and fixed as `localparam`; IRQ10/11 this subsystem's choice and exposed as
  `IRQ_SMBUS` / `IRQ_GPIO` parameters
- Bring-up order and both 8259 sequences (single and cascaded pair) transcribed
  from the testbench helpers that are known to work
- The five deliberate scope boundaries recorded as such rather than left to look
  like defects: `ioapic_msi_emit` not instantiated, `hpet_timer_irq` unrouted,
  boot-intx map is a board decision, IRQ2 never driven, every block
  `CDC_ENABLE(0)`

## What is still open

1. **The planned-but-unwritten chapters**, listed without links in the index:
   `ch02` 01-03 (crossbar, interrupt fabric and cascade each as their own block
   page), `ch03` 02-03 (APB4 protocol at this boundary, per-block interrupt pin
   reference), `ch04` 03 (ACPI sleep and wake sequencing across blocks).

2. **The programming model has never been executed as firmware.** The sequences
   in `ch04_programming/01_initialization.md` are transcriptions of cocotb
   testbench helpers (`init_pic`, `init_pic_cascade`, `arm_ioapic_pin`). They are
   correct as descriptions of what the DV does, which is NOT the same as proving
   the C in the book compiles and runs. The honest gap: nobody has taken the book
   as their only reference and brought the subsystem up from it.

3. **No diagrams.** Every other book pairs its figures with a pre-rendered
   `.png` under `assets/`. This one is tables only, because an unrendered
   mermaid fence either breaks the LaTeX path or silently vanishes. At minimum
   the integration hierarchy and the interrupt fabric deserve a real diagram
   through the normal `assets/mermaid` + generated `.png` route.

4. **`hpet`'s README still names retired field names** in its E4 epoch-hold
   prose (`TIMER_SIZE`, `TIMER_ENABLE`). The bit *table* was removed during RLB
   TASK-019; the prose was not. Noted then, not filed.

## Acceptance

- The chapters listed in item 1 exist, or the index stops listing them as planned
- A bring-up path exists that was driven from the book rather than from the TB -
  ideally the host-program shape the repo already uses, so it runs in sim and on
  the board
- The hierarchy and fabric diagrams exist as generated `.png` assets
- `hpet`'s README prose matches its current field names

## Evidence and references

- Book: `projects/components/retro_legacy_blocks/docs/rlb_top_mas/`
- RTL: `projects/components/retro_legacy_blocks/rtl/rlb_top/rlb_top.sv`
- The DV helpers the programming chapter came from:
  `dv/tbclasses/rlb_top/rlb_top_tb.py` (`init_pic`, `init_pic_cascade`,
  `arm_ioapic_pin`, `arm_ioapic_for_fabric`)
- Suite: `dv/tests/test_rlb_top.py`, 1 test at `gate`, 7 at `func`, 16 at `full`
- Predecessors: RLB TASK-015 (the fabric), TASK-017 and TASK-018 (per-line and
  per-block routing proof), TASK-019 (the follow-up batch)
