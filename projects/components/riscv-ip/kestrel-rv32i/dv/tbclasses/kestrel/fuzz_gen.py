# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: fuzz_gen
# Purpose: CORE-17 seeded constrained-random RV32I program generator for
#          kestrel_core.  Produces complete programs -- weighted random
#          instruction streams (OP/OP-IMM/LUI/AUIPC, structured forward
#          branches, counted backward loops, jal/jalr calls to generated
#          leaf subroutines, loads/stores of every size at random byte
#          offsets including deliberately misaligned ones) with a
#          zero/random-initialized data section and a `li gp,1; ecall`
#          terminator -- assembles them through the house build flow
#          (as/ld/objcopy + normalize_hex.py) for the rv32ui battery
#          machinery, the golden interpreter diff, and the spike lockstep.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-07

"""Seeded constrained-random RV32I program generator (CORE-17).

Every architectural constraint is enforced by construction, not by
filtering:

* Register contract.  Destinations of random instructions are drawn only
  from ``WREGS`` (x4, x6, x7, x10-x31).  Reserved registers keep the
  stream well-defined and bounded: x1 (ra) is written only by
  jal/jalr call sites, x3 (gp) only by the ``li gp, 1`` terminator, x5
  (t0) only by counted-loop decrements, x8/x9 (s0/s1) only by the
  prologue's ``la`` (they pin the two data-region base pointers).
  Reading any register -- reserved ones included -- is always legal, so
  sources come from the full x0-x31 file.
* Control flow.  Branch and jump targets are assembler labels, so they
  always land on real 4-aligned instruction boundaries (IALIGN halts
  are covered directed by CORE-13, never here).  Backward branches only
  ever close a counted loop (``li x5,N`` ... ``addi x5,x5,-1`` /
  ``bne x5,x0`` or ``bltu x0,x5``), so every loop is statically bounded
  and the dynamic retirement count is deterministic.  Forward branches
  are structured single-sided ifs whose then-block rejoins.  jal/jalr
  target generated leaf subroutines that end in ``ret``; loops never
  nest and subroutines never call, so no unbounded recursion exists.
* Memory.  Loads/stores use only s0/s1 base pointers with 12-bit
  offsets inside a per-base 256-byte window of the 512-byte data
  region, which the generated image initializes word by word (zeros and
  seeded random values) -- no read ever depends on uninitialized
  memory, and every access (aligned or not, including the cross-word
  cases that take kestrel's 2-cycle retry) stays inside the region.
* Instructions.  The random body emits only architecturally
  well-defined RV32I: no SYSTEM ops (the CSR stub would diverge from
  spike), no ebreak, no fences, no reserved encodings.  The fixed
  skeleton around the body (a register-clearing prologue, ``csrw
  mtvec``, and a p-env-style ``tohost`` trap handler) makes spike
  terminate the same way the rv32ui p-env images do: on the DUT the
  core halts on the ecall with gp==1, while spike traps into the
  handler, writes 1 to ``tohost``, and fesvr exits 0.
* Register reset state.  The kestrel core resets every GPR to zero,
  but spike's boot preamble (visible at 0x1000 in its commit log before
  it jumps to the ELF entry) clobbers t0/a0/a1.  Any branch on a
  register that has not been written since reset would therefore take
  different paths on the two goldens -- the rv32ui p-envs avoid this by
  initializing everything they read.  The prologue here zeroes the
  entire x1-x31 file before the random body starts, so every register
  read in the stream has a golden-identical value on both sides.

Determinism: one seed maps to one program (two generations of the same
seed produce byte-identical assembly).  Gate level runs the fixed
five-seed corpus in ``fuzz_seeds_gate.json`` (committed next to this
file); func/full derive their stream counts from the SEED env via
``seeds_for_level`` so an explicit SEED reproduces a failing stream.

Self-test: ``python3 fuzz_gen.py --selftest`` generates the corpus plus
a few extra seeds, assembles each through the real build flow, runs the
golden interpreter on the image (must halt on ecall cause 1 with
gp==1 inside the retirement budget), and spike-locks one stream
(rc==0, exception at the ecall pc) -- all without spending sim time.
"""

import json
import os
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Make the tbclasses package importable when this file is run standalone
# (python3 fuzz_gen.py --selftest from anywhere).
_DV_DIR = str(Path(__file__).resolve().parents[2])
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

# riscv-tests p-env link base: the battery boots the core at LINK_BASE and
# re-keys normalized word images into full core address space.
LINK_BASE = 0x8000_0000

# Data region: 512 bytes, addressed through two 256-byte windows so every
# size-4 access stays inside the region (offset <= WINDOW-4).
DATA_BYTES = 512
WINDOW = 256

# Level grid (CORE-17): gate runs the committed smoke corpus, func and full
# draw fresh deterministic streams from the SEED env.
LEVEL_STREAM_COUNT = {"gate": None, "func": 25, "full": 200}

# Reserved registers (never a random destination):
#   x1 ra  -- call link; x3 gp -- pass code; x5 t0 -- loop counter;
#   x8 s0 / x9 s1 -- data-region base pointers (prologue only).
WREGS = [4, 6, 7] + list(range(10, 32))

ALU_OPS = ["add", "sub", "sll", "slt", "sltu", "xor", "srl", "sra", "or",
           "and"]
ALU_IMM_OPS = ["addi", "slti", "sltiu", "xori", "ori", "andi"]
SHIFT_IMM_OPS = ["slli", "srli", "srai"]
LOAD_OPS = ["lb", "lbu", "lh", "lhu", "lw"]
STORE_OPS = ["sb", "sh", "sw"]
BRANCH_OPS = ["beq", "bne", "blt", "bge", "bltu", "bgeu"]

# Body mnemonics that must never appear in the random stream (SYSTEM, EBREAK,
# FENCE are covered directed; the CSR stub would diverge from spike).
_BANNED_BODY_RE = re.compile(
    r"\b(ecall|ebreak|fence|fence\.i|mret|wfi|sfence|csrrw|csrrs|csrrc|"
    r"csrrwi|csrrsi|csrrci|csrw|csrs|csrc)\b")

_BODY_BEGIN = "# <<< fuzz body begin"
_BODY_END = "# <<< fuzz body end"

_GATE_CORPUS_PATH = Path(__file__).resolve().with_name("fuzz_seeds_gate.json")

# Retirement budget the self-test enforces so a generation bug cannot turn
# a battery run into a timeout: streams retire well under this (typical
# count is 200-2000 insns; loops are capped at 6 trips).
SELFTEST_MAX_INSNS = 20_000

_TOOLCHAIN_DEFAULT = "/mnt/data/tools/xpack-riscv-none-elf-gcc/bin"

_LINKER_SCRIPT = (
    "OUTPUT_ARCH(riscv)\n"
    "ENTRY(_start)\n"
    "SECTIONS\n"
    "{\n"
    f"  . = 0x{LINK_BASE:08x};\n"
    "  .text : { *(.text) }\n"
    "  . = ALIGN(8);\n"
    "  .data : { *(.data) }\n"
    "}\n"
)


class FuzzProgram:
    """One generated program: name, seed, full assembly source."""

    def __init__(self, name, seed, asm):
        self.name = name
        self.seed = seed
        self.asm = asm

    def __repr__(self):
        return f"FuzzProgram({self.name}, seed=0x{self.seed:08x})"


class StreamGenerator:
    """Seeded emitter for one constrained-random RV32I program."""

    def __init__(self, seed):
        self.seed = seed & 0xFFFFFFFF
        self.rng = random.Random(
            f"kestrel-rv32i fuzz-stream {self.seed}")
        self._label = 0
        self.sub_labels = [f"Lfuzz_sub_{i}"
                           for i in range(self.rng.randint(1, 4))]

    # ------------------------------------------------------------------
    # Random draw helpers
    # ------------------------------------------------------------------

    def _dest(self):
        return f"x{self.rng.choice(WREGS)}"

    def _src(self):
        return f"x{self.rng.randrange(32)}"

    def _imm12(self):
        return self.rng.randint(-2048, 2047)

    def _offset(self):
        """Random byte offset inside a 256-byte window; misalignment is
        the common case by construction (the kestrel cross-word retry is
        core behavior, exercised by lw/sw at offsets 1-3)."""
        return self.rng.randint(0, WINDOW - 4)

    def _label_name(self, prefix):
        self._label += 1
        return f"{prefix}_{self._label}"

    # ------------------------------------------------------------------
    # Instruction emitters (destinations come from WREGS only)
    # ------------------------------------------------------------------

    def _emit_op(self, out):
        out.append(f"  {self.rng.choice(ALU_OPS)} {self._dest()}, "
                   f"{self._src()}, {self._src()}")

    def _emit_opimm(self, out):
        if self.rng.random() < 0.45:
            op = self.rng.choice(SHIFT_IMM_OPS)
            out.append(f"  {op} {self._dest()}, {self._src()}, "
                       f"{self.rng.randint(0, 31)}")
        else:
            out.append(f"  {self.rng.choice(ALU_IMM_OPS)} {self._dest()}, "
                       f"{self._src()}, {self._imm12()}")

    def _emit_upper(self, out):
        op = "lui" if self.rng.random() < 0.5 else "auipc"
        out.append(f"  {op} {self._dest()}, "
                   f"{self.rng.randint(0, 0xFFFFF)}")

    def _emit_load(self, out):
        out.append(f"  {self.rng.choice(LOAD_OPS)} {self._dest()}, "
                   f"{self._offset()}({self.rng.choice(('s0', 's1'))})")

    def _emit_store(self, out):
        out.append(f"  {self.rng.choice(STORE_OPS)} {self._src()}, "
                   f"{self._offset()}({self.rng.choice(('s0', 's1'))})")

    # ------------------------------------------------------------------
    # Control structures
    # ------------------------------------------------------------------

    def _emit_if(self, out):
        """Single-sided structured forward branch; the then-block rejoins
        at the label, so both directions are statically bounded."""
        end = self._label_name("Lfuzz_if_end")
        out.append(f"  {self.rng.choice(BRANCH_OPS)} {self._src()}, "
                   f"{self._src()}, {end}")
        for _ in range(self.rng.randint(1, 8)):
            self._emit_simple(out)
        out.append(f"{end}:")

    def _emit_loop(self, out):
        """Counted backward loop on x5: li x5,N ... addi x5,x5,-1 and a
        nonzero test back to the top.  The body cannot write x5 (WREGS
        excludes it), so the trip count is exactly N."""
        top = self._label_name("Lfuzz_loop")
        trip = self.rng.randint(1, 6)
        out.append(f"  li x5, {trip}")
        out.append(f"{top}:")
        for _ in range(self.rng.randint(2, 16)):
            self._emit_simple(out)
        out.append("  addi x5, x5, -1")
        back = "bne x5, x0" if self.rng.random() < 0.7 else "bltu x0, x5"
        out.append(f"  {back}, {top}")

    def _emit_call(self, out):
        target = self.rng.choice(self.sub_labels)
        if self.rng.random() < 0.6:
            out.append(f"  jal ra, {target}")
        else:
            rd = self._dest()
            out.append(f"  la {rd}, {target}")
            out.append(f"  jalr ra, 0({rd})")

    def _emit_simple(self, out):
        """One straight-line slot (no control flow)."""
        self._emit_slot(out, control=False)

    def _emit_slot(self, out, control):
        kinds = [("op", 24), ("opimm", 26), ("upper", 10),
                 ("load", 17), ("store", 13)]
        if control:
            kinds += [("if", 8), ("call", 5), ("loop", 4)]
        total = sum(weight for _, weight in kinds)
        pick = self.rng.randrange(total)
        for kind, weight in kinds:
            if pick < weight:
                break
            pick -= weight
        if kind == "op":
            self._emit_op(out)
        elif kind == "opimm":
            self._emit_opimm(out)
        elif kind == "upper":
            self._emit_upper(out)
        elif kind == "load":
            self._emit_load(out)
        elif kind == "store":
            self._emit_store(out)
        elif kind == "if":
            self._emit_if(out)
        elif kind == "call":
            self._emit_call(out)
        else:                       # loop
            self._emit_loop(out)

    # ------------------------------------------------------------------
    # Regions
    # ------------------------------------------------------------------

    def _gen_body(self):
        out = []
        for _ in range(self.rng.randint(40, 120)):
            self._emit_slot(out, control=True)
        return out

    def _gen_subroutine(self, label):
        out = [f"{label}:"]
        for _ in range(self.rng.randint(3, 12)):
            self._emit_slot(out, control=False)
        out.append("  ret")
        return out

    def _gen_data(self):
        words = []
        for _ in range(DATA_BYTES // 4):
            if self.rng.random() < 0.5:
                words.append("  .word 0x00000000")
            else:
                words.append(f"  .word 0x{self.rng.getrandbits(32):08x}")
        return words

    def generate(self):
        seed = self.seed
        body = self._gen_body()
        subs = [self._gen_subroutine(label) for label in self.sub_labels]
        data = self._gen_data()

        lines = [
            "# kestrel-rv32i CORE-17 constrained-random fuzz stream",
            f"# seed 0x{seed:08x} -- regenerate with fuzz_gen.generate_stream("
            f"0x{seed:08x})",
            "  .text",
            "  .globl _start",
            "_start:",
            # Register reset contract: the core resets all GPRs to zero but
            # spike's boot preamble clobbers t0/a0/a1 before jumping to the
            # ELF entry, so every register the stream may read is zeroed
            # here first (t0/s0/s1 are then re-purposed by the setup below,
            # x5 per loop by its `li`).  Without this a branch on an
            # as-yet-unwritten register takes different paths on the two
            # goldens -- see fuzz_gen module docstring.
        ]
        lines += [f"  li x{reg}, 0" for reg in range(1, 32)]
        lines += [
            # Point mtvec at the tohost handler (spike honors the write;
            # the kestrel CSR stub retires it) and pin the two data-region
            # base pointers.
            "  la t0, _trap_handler",
            "  csrw mtvec, t0",
            "  la s0, _fuzz_data",
            f"  la s1, _fuzz_data + {WINDOW}",
            f"{_BODY_BEGIN} seed 0x{seed:08x} >>>",
        ]
        lines += body
        lines += [
            f"{_BODY_END} seed 0x{seed:08x} >>>",
            # Terminator: gp==1 (riscv-tests pass code), then ecall.  The
            # DUT halts on the ecall; spike traps into the handler below.
            "  li gp, 1",
            "  ecall",
            "",
            "_trap_handler:",
            "  sw gp, tohost, t1",
            "1: j 1b",
            "",
        ]
        for sub in subs:
            lines += sub
            lines.append("")
        lines += [
            "  .data",
            "  .balign 8",
            "  .globl tohost",
            "tohost:",
            "  .word 0",
            "  .globl fromhost",
            "fromhost:",
            "  .word 0",
            "  .globl _fuzz_data",
            "_fuzz_data:",
        ]
        lines += data
        lines.append("")
        return FuzzProgram(f"fuzz_{seed:08x}", seed, "\n".join(lines))


def generate_stream(seed):
    """Generate one program.  Deterministic per seed."""
    return StreamGenerator(seed).generate()


# ---------------------------------------------------------------------------
# Seed selection
# ---------------------------------------------------------------------------

def gate_corpus(path=None):
    """The committed five-seed gate/smoke corpus."""
    corpus = Path(path) if path else _GATE_CORPUS_PATH
    with open(corpus) as fh:
        seeds = json.load(fh)["seeds"]
    if not seeds:
        raise ValueError(f"{corpus}: empty seed corpus")
    return list(seeds)


def seeds_for_level(level, seed_env, corpus_path=None):
    """Stream seeds for a battery level.

    gate  -> the fixed committed corpus (no env involved, always the same
             five streams).
    func  -> LEVEL_STREAM_COUNT[func] distinct seeds drawn from a generator
    full     seeded by (level, SEED env), so an explicit SEED env reproduces
             a failing stream exactly.
    """
    if level == "gate":
        return gate_corpus(corpus_path)
    count = LEVEL_STREAM_COUNT.get(level)
    if count is None:
        raise ValueError(f"unknown fuzz level {level!r}")
    rng = random.Random(f"kestrel-rv32i fuzz {level} {seed_env}")
    seeds, seen = [], set()
    while len(seeds) < count:
        seed = rng.getrandbits(32)
        if seed not in seen:
            seen.add(seed)
            seeds.append(seed)
    return sorted(seeds)


# ---------------------------------------------------------------------------
# Validation (static contract checks on the emitted body)
# ---------------------------------------------------------------------------

def validate_program(program):
    """Static constraint checks; raises AssertionError on violation."""
    asm = program.asm
    begin = asm.index(_BODY_BEGIN)
    end = asm.index(_BODY_END)
    body = asm[begin:end]
    banned = _BANNED_BODY_RE.findall(body)
    assert not banned, f"{program.name}: banned ops in body: {banned}"
    assert "li gp, 1" in asm and "ecall" in asm, \
        f"{program.name}: missing li gp,1 / ecall terminator"
    assert asm.count("tohost:") == 1 and asm.count("_fuzz_data:") == 1, \
        f"{program.name}: data section symbols not unique"
    labels = re.findall(r"^([A-Za-z_][A-Za-z0-9_]*):", asm, re.MULTILINE)
    dupes = {label for label in labels if labels.count(label) > 1}
    assert not dupes, f"{program.name}: duplicate labels {dupes}"
    return True


# ---------------------------------------------------------------------------
# Build flow (as -> ld -> objcopy -O verilog -> normalize_hex.py)
# ---------------------------------------------------------------------------

def toolchain_dir():
    return os.environ.get("RISCV_TOOLCHAIN", _TOOLCHAIN_DEFAULT)


def build_stream(program, out_dir, tools=None):
    """Assemble/link/package one stream through the house build flow.

    Writes <out_dir>/<name>.s, .elf, .hex (word-indexed, base-relative --
    re-key by (LINK_BASE >> 2) for the battery/interpreter address space)
    and returns the FuzzProgram with ``hex_path``/``elf_path`` set.
    """
    tools = Path(tools or toolchain_dir())
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    asm_path = out_dir / f"{program.name}.s"
    ld_path = out_dir / "fuzz_link.ld"
    obj_path = out_dir / f"{program.name}.o"
    elf_path = out_dir / f"{program.name}.elf"
    raw_path = out_dir / f"{program.name}.raw.hex"
    hex_path = out_dir / f"{program.name}.hex"
    normalize = Path(__file__).resolve().parents[2] / "tests" / "programs" / \
        "normalize_hex.py"
    asm_path.write_text(program.asm)
    ld_path.write_text(_LINKER_SCRIPT)

    def _run(cmd):
        subprocess.run([str(c) for c in cmd], check=True,
                       capture_output=True, text=True)

    # zicsr for the prologue's `csrw mtvec` (this xpack gas split CSR ops
    # out of base rv32i; the kestrel CSR stub and spike's RV32I both cover
    # them, matching the rv32ui-p-* images' mtvec writes).
    _run([tools / "riscv-none-elf-as", "-march=rv32i_zicsr_zifencei",
          "-mabi=ilp32", asm_path, "-o", obj_path])
    _run([tools / "riscv-none-elf-ld", "-T", ld_path, obj_path, "-o",
          elf_path])
    _run([tools / "riscv-none-elf-objcopy", "-O", "verilog", elf_path,
          raw_path])
    _run([sys.executable, normalize, raw_path, hex_path,
          "--base", hex(LINK_BASE)])
    for transient in (obj_path, raw_path):
        transient.unlink(missing_ok=True)

    program.hex_path = hex_path
    program.elf_path = elf_path
    return program


def build_streams(seeds, out_dir, tools=None, log=None):
    """Generate + assemble every seed; returns [FuzzProgram] in seed order."""
    programs = []
    for seed in seeds:
        program = generate_stream(seed)
        validate_program(program)
        build_stream(program, out_dir, tools=tools)
        if log:
            log.info(f"built {program.name} ({len(program.asm.splitlines())}"
                     f" asm lines)")
        programs.append(program)
    return programs


# ---------------------------------------------------------------------------
# Self-test: determinism + static constraints + golden run + one spike run
# ---------------------------------------------------------------------------

def _selftest(seed, tools):
    from tbclasses.kestrel.rv32i_interpreter import (RV32IInterpreter,
                                                     load_verilog_hex)
    from tbclasses.kestrel.rv32ui_battery import (lockstep_diff,
                                                  parse_spike_log, read_elf32,
                                                  run_spike)

    program = generate_stream(seed)
    again = generate_stream(seed)
    assert program.asm == again.asm, \
        f"seed 0x{seed:08x}: regeneration not byte-identical"
    validate_program(program)

    with tempfile.TemporaryDirectory(prefix="kestrel_fuzz_selftest_") as tmp:
        build_stream(program, tmp, tools=tools)
        words = {idx + (LINK_BASE >> 2): word
                 for idx, word in load_verilog_hex(program.hex_path).items()}
        assert words, f"{program.name}: empty image"

        # Golden: must halt on the ecall (cause 1) with gp==1, well inside
        # the retirement budget the battery sim also enforces.
        golden = RV32IInterpreter(words, reset_addr=LINK_BASE)
        golden.run(max_insns=SELFTEST_MAX_INSNS)
        assert golden.halt_cause == 1, \
            f"{program.name}: golden halt cause {golden.halt_cause}, want 1"
        gp = next(beat["rd_wdata"] for beat in reversed(golden.trace)
                  if beat["rd_addr"] == 3)
        assert gp == 1, f"{program.name}: gp=={gp}, want 1"
        assert golden.trace[-1]["trap"] == 1, \
            f"{program.name}: final golden beat is not the trap beat"
        detail = (f"golden ok: {len(golden.trace)} beats to "
                  f"ecall halt at 0x{golden.halt_pc:x}")
        spike_detail = "spike check skipped"

        # Spike (cheap enough to run for every self-test stream): rc must be
        # 0 (tohost==1 via the trap handler) and the commit stream must end
        # with the exception at the halt pc, mirroring the battery lockstep.
        if os.environ.get("KESTREL_FUZZ_SELFTEST_SPIKE", "1") != "0":
            log_path = Path(tmp) / f"spike_{program.name}.log"
            rc = run_spike(program.elf_path, log_path)
            assert rc == 0, f"{program.name}: spike rc={rc}, want 0"
            entry, symbols = read_elf32(program.elf_path)
            assert symbols.get("tohost") is not None, \
                f"{program.name}: no tohost symbol"
            records = parse_spike_log(log_path)
            ok, errors, stub_traps, term_trap = lockstep_diff(
                golden.trace, golden.halt_pc, entry, records)
            assert ok, f"{program.name}: spike lockstep: {errors}"
            assert not stub_traps, \
                f"{program.name}: unexpected stub traps {[t.kind for t in stub_traps]}"
            spike_detail = (f"spike ok: rc=0, {len(records)} records, "
                            f"term trap {term_trap}")
        return f"seed 0x{seed:08x} {program.name}: {detail}; {spike_detail}"


def main(argv):
    import argparse
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--selftest", action="store_true",
                        help="generate the corpus + extra seeds, assemble, "
                             "and check each against the golden interpreter "
                             "and spike (no simulator needed)")
    parser.add_argument("--tools", default=None,
                        help=f"toolchain bin dir (default: {toolchain_dir()})")
    parser.add_argument("--dump", type=lambda s: int(s, 0), default=None,
                        help="print the generated assembly for one seed")
    args = parser.parse_args(argv)

    if args.dump is not None:
        print(generate_stream(args.dump).asm)
        return 0
    if args.selftest:
        # The committed gate corpus plus extras that exercise the corners
        # (0/1, 32-bit extremes).
        seeds = gate_corpus() + [0x0, 0x1, 0xFFFFFFFF, 0x80000000]
        for seed in seeds:
            print("SELFTEST " + _selftest(seed, args.tools))
        print(f"SELFTEST PASS ({len(seeds)} streams: corpus + corners)")
        return 0
    parser.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
