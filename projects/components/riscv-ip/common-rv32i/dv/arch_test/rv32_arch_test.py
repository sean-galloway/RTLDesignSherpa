# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rv32_arch_test
# Purpose: riscv-arch-test (RISC-V International's architectural test suite,
#          3.x / RISCOF signature format) for the falcon-suite RV32I cores:
#          builds each rv32i_m/<EXT> test twice (DUT env and the suite's spike
#          reference env), runs both reference models (spike and Sail) and
#          requires their signatures to agree for the golden signature,
#          hands the DUT image to a core's runner, and compares the DUT's
#          signature region word for word.  Core-independent; each core's
#          test file supplies the load / run / read-back.  The extension
#          (I, M) is a parameter; I is the default every RV32I core uses.
#
# Documentation: vault/handbook/dv/riscv-arch-test.md
# Subsystem: riscv-ip/common-rv32i
#
# Author: sean galloway
# Created: 2026-11-22

"""riscv-arch-test signature compare for the RV32I falcon cores.

This is what RISCOF does for a DUT plugin and a spike reference plugin,
inside the repo's cocotb flow:

* the DUT ELF links with ``dut_model/model_test.h`` here (ends on ECALL, which
  every core halts on), the reference ELF with the suite's
  ``riscof-plugins/rv32/spike_simple/env`` (ends on a tohost write); both
  use the spike plugin's ``link.ld``, so the images differ only in the
  halt sequence;
* the golden is spike's ``+signature`` dump at granularity 4, one word per
  line, ``begin_signature`` .. ``end_signature``, and Sail (RISCOF's default
  reference model) must dump the identical signature from the same reference
  ELF -- two independent models, or the test is an error, not a pass;
* the DUT signature is read from the TB memory over the same range after
  the halt, and written as ``DUT-<core>.signature`` next to the reference.

A core that traps on ecall (peregrine: machine-mode traps, no halt) builds
with ``halt="tohost"``: its DUT image IS the reference build, which ends on
the suite env's ``tohost`` store, and ``run_tohost`` runs it to that store
(PRD §5 of peregrine-rv32im).

The vendor tree is a pinned clone (``vendor/`` is git-ignored, like
riscv-tests and riscv-formal): ``ensure_vendor`` checks the commit and says
how to fetch it when it is missing.  Sail is the pinned release binary in
``vendor/sail-riscv``; ``ensure_sail`` checks the version the same way.
"""

import os
import struct
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

VENDOR_REL = Path("vendor") / "riscv-arch-test"
PINNED_TAG = "3.10.0"
PINNED_COMMIT = "fc32e41d49480fd99ba0a192dfff9c3319b44873"
SUITE_REL = Path("riscv-test-suite") / "rv32i_m" / "I" / "src"   # the default extension
REF_ENV_REL = Path("riscof-plugins") / "rv32" / "spike_simple" / "env"
DUT_ENV = Path(__file__).resolve().parent / "dut_model"

# Gate level per extension: I = one ALU op, one load, one store; M = one
# multiply, one signed divide, one unsigned remainder; Zifencei has one test.
GATE_TESTS = ("add-01", "lw-align-01", "sw-align-01")
GATE_TESTS_BY_EXT = {"I": GATE_TESTS, "M": ("mul-01", "div-01", "remu-01"),
                     "Zifencei": ("Fencei",)}

# Extension -> (-march, spike --isa).  M adds the multiply/divide opcodes the
# M tests are built from; I stays rv32i, so an RV32I core's build is unchanged.
# Zifencei (Fencei.S, self-modifying code) adds fence.i (peregrine TASK-001
# stage 4, whose split I$ / write-back D$ it exercises).
EXT_ISA = {"I": ("rv32i", "rv32i"), "M": ("rv32im", "rv32im"),
           "Zifencei": ("rv32i_zifencei", "rv32i_zifencei")}


def suite_rel(ext="I"):
    """riscv-test-suite/rv32i_m/<ext>/src under the vendor clone."""
    if ext not in EXT_ISA:
        raise ValueError(f"unsupported arch-test extension {ext!r}; known {sorted(EXT_ISA)}")
    return Path("riscv-test-suite") / "rv32i_m" / ext / "src"

# Every rv32i_m/I test links at 0x8000_0000 (spike plugin link.ld).
LINK_BASE = 0x8000_0000

_TOOLCHAIN_DEFAULT = "/mnt/data/tools/xpack-riscv-none-elf-gcc/bin"
_SPIKE_DEFAULT = "/mnt/data/tools/spike/bin/spike"

# Sail, the second reference: the riscv/sail-riscv release tarball unpacked
# into vendor/sail-riscv (git-ignored); RV_ARCH_SAIL overrides the binary.
SAIL_REL = Path("vendor") / "sail-riscv" / "bin" / "sail_riscv_sim"
SAIL_VERSION = "0.16"
_SAIL_URL = ("https://github.com/riscv/sail-riscv/releases/download/"
             f"{SAIL_VERSION}/sail-riscv-Linux-x86_64.tar.gz")

# -mno-relax: arch_test.h pads its fixed-length LA() with `.option rvc`
# alignment; with linker relaxation on, the linker shrinks that padding to a
# 16-bit c.nop, an illegal instruction on an RV32I core (and in spike
# --isa=rv32i, where the test then never reaches its halt).
_CFLAGS = ("-mabi=ilp32", "-mno-relax", "-static",
           "-mcmodel=medany", "-fvisibility=hidden", "-nostdlib",
           "-nostartfiles", "-DXLEN=32", "-DTEST_CASE_1=True")


def toolchain():
    return Path(os.environ.get("RISCV_TOOLCHAIN", _TOOLCHAIN_DEFAULT))


def spike():
    return os.environ.get("RV_ARCH_SPIKE", _SPIKE_DEFAULT)


def ensure_sail(repo_root):
    """Path of the pinned Sail binary; raise with the fetch command if it is
    missing or another version."""
    exe = Path(os.environ.get("RV_ARCH_SAIL", Path(repo_root) / SAIL_REL))
    dest = Path(repo_root) / SAIL_REL.parents[1]
    fetch = (f"mkdir -p {dest} && curl -sL {_SAIL_URL} "
             f"| tar xz -C {dest} --strip-components=1")
    if not exe.is_file():
        raise FileNotFoundError(f"Sail not found at {exe}; fetch it: {fetch}")
    proc = subprocess.run([str(exe), "--version"], capture_output=True, text=True,
                          check=False)
    version = proc.stdout.strip()
    if version != SAIL_VERSION:
        raise RuntimeError(f"{exe} is Sail {version or '(unknown)'}, expected "
                           f"{SAIL_VERSION}; re-fetch: {fetch}")
    return exe


def _sail_signature(repo_root, name, ref_elf, sig):
    """Run the reference ELF on Sail (default RV32 config) and return its
    signature words."""
    proc = subprocess.run(
        [str(ensure_sail(repo_root)), "--rv32", "--test-signature", str(sig),
         str(ref_elf)], capture_output=True, text=True, timeout=600, check=False)
    if proc.returncode != 0 or not sig.exists():
        (sig.parent / "sail.log").write_text(proc.stdout + proc.stderr)
        raise RuntimeError(f"{name}: Sail reference failed (rc {proc.returncode}); "
                           f"see {sig.parent / 'sail.log'}")
    return [int(line, 16) for line in sig.read_text().split()]


def ensure_vendor(repo_root):
    """Path of the pinned riscv-arch-test clone; raise with the fetch
    command if it is missing or at another commit."""
    root = Path(repo_root) / VENDOR_REL
    fetch = (f"git clone --depth 1 --branch {PINNED_TAG} "
             f"https://github.com/riscv-non-isa/riscv-arch-test.git {root}")
    if not (root / SUITE_REL).is_dir():
        raise FileNotFoundError(f"riscv-arch-test not found at {root}; fetch it: {fetch}")
    head = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                          capture_output=True, text=True, check=False).stdout.strip()
    if head != PINNED_COMMIT:
        raise RuntimeError(f"{root} is at {head or 'an unknown commit'}, "
                           f"expected {PINNED_TAG} ({PINNED_COMMIT}); re-fetch: {fetch}")
    return root


def discover(repo_root, level, tests=None, ext="I"):
    """Ordered test names (``add-01`` ...) for a level; ``tests`` pins a subset."""
    src = ensure_vendor(repo_root) / suite_rel(ext)
    names = sorted(p.stem for p in src.glob("*.S"))
    if not names:
        raise FileNotFoundError(f"no tests under {src}")
    if tests is not None:
        wanted = set(tests)
        missing = wanted - set(names)
        if missing:
            raise ValueError(f"unknown arch tests: {sorted(missing)}")
        return [n for n in names if n in wanted]
    if level == "gate":
        return [n for n in names if n in GATE_TESTS_BY_EXT[ext]]
    return names


# ---------------------------------------------------------------------------
# ELF reading
# ---------------------------------------------------------------------------

def read_elf(path):
    """(entry, symbols, segments) of a little-endian ELF32.

    ``segments`` is a list of (paddr, bytes, memsz, writable) for each
    PT_LOAD, bytes zero-extended to memsz.
    """
    data = Path(path).read_bytes()
    if data[:4] != b"\x7fELF" or data[4] != 1 or data[5] != 1:
        raise ValueError(f"{path}: not a little-endian ELF32 file")
    (entry,) = struct.unpack_from("<I", data, 0x18)
    (phoff, shoff) = struct.unpack_from("<II", data, 0x1C)
    (phentsize, phnum, shentsize, shnum) = struct.unpack_from("<HHHH", data, 0x2A)

    segments = []
    for i in range(phnum):
        p_type, p_off, _, p_paddr, p_filesz, p_memsz, p_flags, _ = \
            struct.unpack_from("<8I", data, phoff + i * phentsize)
        if p_type != 1 or p_memsz == 0:          # PT_LOAD only
            continue
        body = data[p_off:p_off + p_filesz] + bytes(p_memsz - p_filesz)
        segments.append((p_paddr, body, p_memsz, bool(p_flags & 0x2)))

    sections = [struct.unpack_from("<10I", data, shoff + i * shentsize)
                for i in range(shnum)]
    symbols = {}
    for sh in sections:
        if sh[1] != 2 or sh[9] == 0:              # SHT_SYMTAB
            continue
        str_base = sections[sh[6]][4]
        for e in range(sh[5] // sh[9]):
            st_name, st_value = struct.unpack_from("<II", data, sh[4] + e * sh[9])
            end = data.index(b"\x00", str_base + st_name)
            symbols[data[str_base + st_name:end].decode()] = st_value
    return entry, symbols, segments


def image_words(segments):
    """{word_address: word} over every loadable byte (zeros included)."""
    words = {}
    for paddr, body, _, _ in segments:
        if paddr % 4:
            raise ValueError(f"segment at 0x{paddr:x} is not word aligned")
        body = body + bytes(-len(body) % 4)
        for off in range(0, len(body), 4):
            (w,) = struct.unpack_from("<I", body, off)
            words[(paddr + off) >> 2] = w
    return words


# ---------------------------------------------------------------------------
# Build + reference
# ---------------------------------------------------------------------------

@dataclass
class ArchTest:
    """One built test: the DUT image and the reference signature."""
    name: str
    work_dir: Path
    dut_elf: Path
    ref_elf: Path
    entry: int
    begin: int                   # begin_signature (byte address, DUT image)
    end: int                     # end_signature
    halt_pc: int                 # rvmodel_halt (the ecall the core halts on); 0 for tohost
    words: dict = field(repr=False)          # DUT image {word_address: word}
    rw_words: frozenset = field(repr=False)  # word addresses of writable segments
    ref_signature: list = field(repr=False)  # spike's words (== Sail's)
    tohost: int = 0                          # tohost address (halt="tohost" builds)

    @property
    def sig_words(self):
        return (self.end - self.begin) // 4

    def load_words(self):
        """Non-zero image words only: a TB that zeroed its memory needs no
        more (the image's zeros are already there)."""
        return {a: w for a, w in self.words.items() if w}

    def dirty_words(self):
        """Word addresses this test can leave non-zero: its non-zero image
        words plus every writable word (the only places its stores land).
        Zeroing these restores a zeroed memory before the next test."""
        return {a for a, w in self.words.items() if w} | set(self.rw_words)


def _run(cmd, log):
    proc = subprocess.run([str(c) for c in cmd], capture_output=True, text=True,
                          check=False)
    if proc.returncode != 0:
        Path(log).write_text(proc.stdout + proc.stderr)
        raise RuntimeError(f"{cmd[0]} failed (rc {proc.returncode}); see {log}")
    return proc


def _compile(repo_root, src, env_dir, out, ext="I"):
    vendor = ensure_vendor(repo_root)
    gcc = toolchain() / "riscv-none-elf-gcc"
    _run([gcc, f"-march={EXT_ISA[ext][0]}", *_CFLAGS, "-T", vendor / REF_ENV_REL / "link.ld",
          "-I", env_dir, "-I", vendor / "riscv-test-suite" / "env",
          src, "-o", out], out.with_suffix(".cc.log"))


def build(repo_root, name, work_dir, ext="I", halt="ecall"):
    """Compile ``name`` for the DUT and the reference, run spike and Sail,
    and return the ArchTest.  Raises when either reference fails or the two
    references disagree.

    ``halt="ecall"`` builds the DUT image with dut_model (ends on ECALL);
    ``halt="tohost"`` uses the reference build itself as the DUT image (ends
    on the tohost store), for a core whose ecall traps."""
    if halt not in ("ecall", "tohost"):
        raise ValueError(f"halt must be 'ecall' or 'tohost', got {halt!r}")
    vendor = ensure_vendor(repo_root)
    ensure_sail(repo_root)
    work = Path(work_dir) / name
    work.mkdir(parents=True, exist_ok=True)
    src = vendor / suite_rel(ext) / f"{name}.S"
    ref_elf = work / "ref.elf"
    _compile(repo_root, src, vendor / REF_ENV_REL, ref_elf, ext)
    if halt == "ecall":
        dut_elf = work / "dut.elf"
        _compile(repo_root, src, DUT_ENV, dut_elf, ext)
    else:
        dut_elf = ref_elf

    ref_sig = work / "Reference-spike.signature"
    proc = subprocess.run(
        [spike(), f"--isa={EXT_ISA[ext][1]}", f"+signature={ref_sig}", "+signature-granularity=4",
         str(ref_elf)], capture_output=True, text=True, timeout=120, check=False)
    if proc.returncode != 0 or not ref_sig.exists():
        raise RuntimeError(f"{name}: spike reference failed (rc {proc.returncode}): "
                           f"{proc.stderr.strip()[:200]}")
    ref_words = [int(line, 16) for line in ref_sig.read_text().split()]
    sail_words = _sail_signature(repo_root, name, ref_elf,
                                 work / "Reference-sail.signature")
    if sail_words != ref_words:
        bad = [i for i, (a, b) in enumerate(zip(ref_words, sail_words)) if a != b]
        where = (f"first at word {bad[0]}: spike {ref_words[bad[0]]:08x} "
                 f"sail {sail_words[bad[0]]:08x}" if bad else
                 f"lengths {len(ref_words)} vs {len(sail_words)}")
        raise RuntimeError(f"{name}: the references disagree ({where}); "
                           "the golden signature is undefined")

    entry, symbols, segments = read_elf(dut_elf)
    halt_sym = "rvmodel_halt" if halt == "ecall" else "tohost"
    for sym in ("begin_signature", "end_signature", halt_sym):
        if sym not in symbols:
            raise ValueError(f"{name}: DUT ELF has no {sym}")
    test = ArchTest(name=name, work_dir=work, dut_elf=dut_elf, ref_elf=ref_elf,
                    entry=entry, begin=symbols["begin_signature"],
                    end=symbols["end_signature"],
                    halt_pc=symbols.get("rvmodel_halt", 0),
                    tohost=symbols.get("tohost", 0),
                    words=image_words(segments),
                    rw_words=frozenset(image_words([s for s in segments if s[3]])),
                    ref_signature=ref_words)
    if test.sig_words != len(ref_words):
        raise ValueError(f"{name}: DUT signature region is {test.sig_words} words, "
                         f"spike dumped {len(ref_words)}")
    return test


# ---------------------------------------------------------------------------
# Compare + report
# ---------------------------------------------------------------------------

def compare(test, dut_words, core):
    """Write DUT-<core>.signature and diff it with the reference.

    Returns (ok, detail).  ``dut_words`` is the list read from the TB memory
    over begin_signature .. end_signature.
    """
    sig = test.work_dir / f"DUT-{core}.signature"
    sig.write_text("".join(f"{w:08x}\n" for w in dut_words))
    if len(dut_words) != len(test.ref_signature):
        return False, f"signature length {len(dut_words)} != reference {len(test.ref_signature)}"
    bad = [i for i, (d, r) in enumerate(zip(dut_words, test.ref_signature)) if d != r]
    if not bad:
        return True, f"signature {len(dut_words)} words match"
    first = bad[0]
    return False, (f"{len(bad)} of {len(dut_words)} signature words differ; first at "
                   f"0x{test.begin + 4 * first:08x}: dut {dut_words[first]:08x} "
                   f"ref {test.ref_signature[first]:08x}")


def write_summary(work_dir, core, level, results, ext="I"):
    """results: list of dicts with name, passed, detail (+ optional keys)."""
    passed = sum(r["passed"] for r in results)
    lines = [f"riscv-arch-test {PINNED_TAG} rv32i_m/{ext} on {core} ({level} level): "
             f"{passed}/{len(results)}",
             f"{'test':<20} {'status':<6} detail"]
    lines += [f"{r['name']:<20} {'PASS' if r['passed'] else 'FAIL':<6} {r['detail']}"
              for r in results]
    tag = "" if ext == "I" else f"_{ext}"
    path = Path(work_dir) / f"arch_test_summary_{core}{tag}_{level}.txt"
    path.write_text("\n".join(lines) + "\n")
    return path


# ---------------------------------------------------------------------------
# Runner for a core with one flat TB memory (kestrel, merlin)
# ---------------------------------------------------------------------------

def mem_index(word_address, mem_words, bank=0):
    """TB memory index of a word address: the TBs alias modulo their size;
    ``bank`` offsets a per-context bank (gatling)."""
    return bank * mem_words + (word_address & (mem_words - 1))


def poke(mem, mem_words, words, bank=0):
    """Write {word_address: word} straight into the TB memory array over VPI
    (the clocked backdoor port costs one cycle a word; jal-01 is 440 Ki)."""
    for addr, w in words.items():
        mem[mem_index(addr, mem_words, bank)].value = w


def peek_signature(mem, mem_words, test, bank=0):
    """The DUT's signature region, read from the TB memory."""
    first = test.begin >> 2
    return [int(mem[mem_index(first + i, mem_words, bank)].value)
            for i in range(test.sig_words)]


async def run_flat(dut, tb, core, repo_root, level, work_dir, mem_words,
                   max_cycles, tests=None):
    """Run every test on a single-hart core whose TB top exposes ``mem``.

    ``tb`` provides assert_reset / release_reset / run_to_halt and leaves
    halt_cause and halt_pc behind (KestrelTB, MerlinTB).  Pass is a halt
    with cause 1 on rvmodel_halt AND a signature equal to spike's.
    """
    work_dir = Path(work_dir)
    work_dir.mkdir(parents=True, exist_ok=True)
    names = discover(repo_root, level, tests)
    dut._log.info(f"riscv-arch-test {PINNED_TAG} rv32i_m/I on {core} "
                  f"({level} level): {len(names)} tests")
    await tb.ensure_clock()
    mem = dut.mem
    results = []
    dirty = set()
    for name in names:
        test = build(repo_root, name, work_dir)
        await tb.assert_reset()
        poke(mem, mem_words, {a: 0 for a in dirty})
        poke(mem, mem_words, test.load_words())
        dirty = test.dirty_words()
        await tb.assert_reset()          # let the deposits land before release
        await tb.release_reset()
        res = {"name": name, "passed": False}
        try:
            await tb.run_to_halt(max_cycles=max_cycles)
        except AssertionError as exc:
            res["detail"] = f"no halt: {exc}"
            results.append(res)
            dut._log.info(f"{name}: FAIL {res['detail']}")
            continue
        if tb.halt_cause != 1 or tb.halt_pc != test.halt_pc:
            res["detail"] = (f"halted cause {tb.halt_cause} at 0x{tb.halt_pc:08x}, "
                             f"expected ecall (1) at rvmodel_halt 0x{test.halt_pc:08x}")
        else:
            ok, detail = compare(test, peek_signature(mem, mem_words, test), core)
            res["passed"] = ok
            res["detail"] = f"{detail}; {len(tb.trace)} retired"
        results.append(res)
        dut._log.info(f"{name}: {'PASS' if res['passed'] else 'FAIL'} {res['detail']}")

    failures = [r["name"] for r in results if not r["passed"]]
    summary = write_summary(work_dir, core, level, results)
    dut._log.info(f"riscv-arch-test summary: {len(results) - len(failures)}/"
                  f"{len(results)} passed ({summary})"
                  + (f", failures: {failures}" if failures else ""))
    assert not failures, f"riscv-arch-test failures on {core}: {failures}"
    return results


# ---------------------------------------------------------------------------
# Runner for a core that traps on ecall and halts on tohost (peregrine)
# ---------------------------------------------------------------------------

async def run_tohost(dut, tb, core, repo_root, level, work_dir, mem_words,
                     max_cycles, ext="I", tests=None):
    """Run every rv32i_m/<ext> test on a core with real traps.

    The DUT image is the reference build (``halt="tohost"``).  ``tb``
    provides assert_reset / release_reset / run_to_tohost(tohost,
    max_cycles) (PeregrineTB) and its TB top exposes ``mem``.  Pass is a
    tohost value of 1 AND a signature equal to spike's (== Sail's).
    """
    work_dir = Path(work_dir)
    work_dir.mkdir(parents=True, exist_ok=True)
    names = discover(repo_root, level, tests, ext)
    dut._log.info(f"riscv-arch-test {PINNED_TAG} rv32i_m/{ext} on {core} "
                  f"({level} level): {len(names)} tests")
    await tb.ensure_clock()
    mem = dut.mem
    results = []
    dirty = set()
    for name in names:
        test = build(repo_root, name, work_dir, ext=ext, halt="tohost")
        await tb.assert_reset()
        poke(mem, mem_words, {a: 0 for a in dirty})
        poke(mem, mem_words, test.load_words())
        dirty = test.dirty_words()
        await tb.assert_reset()          # let the deposits land before release
        await tb.release_reset()
        res = {"name": name, "passed": False}
        try:
            value = await tb.run_to_tohost(test.tohost, max_cycles=max_cycles)
        except AssertionError as exc:
            res["detail"] = f"no tohost store: {exc}"
            results.append(res)
            dut._log.info(f"{name}: FAIL {res['detail']}")
            continue
        if value != 1:
            res["detail"] = f"tohost=0x{value:x}, expected 1"
        else:
            ok, detail = compare(test, peek_signature(mem, mem_words, test), core)
            res["passed"] = ok
            res["detail"] = f"{detail}; {len(tb.trace)} retired"
        results.append(res)
        dut._log.info(f"{name}: {'PASS' if res['passed'] else 'FAIL'} {res['detail']}")

    failures = [r["name"] for r in results if not r["passed"]]
    summary = write_summary(work_dir, core, level, results, ext)
    dut._log.info(f"riscv-arch-test summary: {len(results) - len(failures)}/"
                  f"{len(results)} passed ({summary})"
                  + (f", failures: {failures}" if failures else ""))
    assert results, f"riscv-arch-test rv32i_m/{ext} on {core}: nothing ran"
    assert not failures, f"riscv-arch-test failures on {core}: {failures}"
    return results
