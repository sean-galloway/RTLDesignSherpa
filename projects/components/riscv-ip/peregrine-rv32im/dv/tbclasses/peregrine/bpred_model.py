# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: bpred_model
# Purpose: Reference model of peregrine_bpred (BTB + 2-bit BHT) and the
#          retire-trace check that holds peregrine_core's predictions to it.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine branch predictor model.

``BpredModel`` is the predictor's definition (PRD §4.2), written from the
spec rather than the RTL: a direct-mapped BTB (tag, target, unconditional
bit) and a BHT of 2-bit saturating counters.  The unit test drives it in
lock with the RTL cycle by cycle.

``check_trace`` holds a core's retire trace to the model.  The core writes
the predictor once per resolved instruction, as it leaves EX, in program
order, and every such instruction retires (an exception retires as a trap
beat), so the model replays the retire stream, trap beats included.  A lookup happens in IF,
before the older instructions in flight have resolved, so the state a
retired instruction was predicted from is one of a small set:

* every update from instructions at least three older is visible;
* the update from the instruction two older is visible only if IF was held
  while that instruction left EX (an interlock or the M unit);
* the update from the instruction immediately older is never visible --
  unless that instruction redirected the fetch (a mispredict, a trap, an
  mret, a fence.i), in which case this instruction was fetched after it resolved.

The check accepts a prediction that equals the model's under any state in
that set, and fails on anything else.  It also checks each beat's
mispredict flag against its own prediction and resolved outcome.
"""

from dataclasses import dataclass, field

OPC_BRANCH = 0x63
OPC_JAL = 0x6F
OPC_JALR = 0x67
MASK32 = 0xFFFF_FFFF


def _signed(x: int) -> int:
    return x - (1 << 32) if x & 0x8000_0000 else x


@dataclass
class BpredModel:
    """BTB + 2-bit BHT, the peregrine_bpred contract.

    A BHT counter is held as the SET of values it can have.  The BHT is
    LUTRAM with no reset, so after a core reset (between programs in one
    simulation) a counter's value is whatever the last program left:
    ``unknown_counters=True`` starts every counter as {0, 1, 2, 3}, and
    same-direction updates saturate the set down to one value.  With
    ``unknown_counters=False`` (the unit test, one run from power-up) a
    counter is exact, and reading one no update wrote is an error: the RTL
    relies on a conditional BTB entry being installed by the same update
    that writes its counter.
    """
    btb_entries: int = 32
    bht_entries: int = 256
    unknown_counters: bool = False
    btb: dict = field(default_factory=dict)      # index -> (tag, target, uncond)
    bht: dict = field(default_factory=dict)      # index -> frozenset of counter values

    def _btb_idx(self, pc: int) -> int:
        return (pc >> 2) % self.btb_entries

    def _btb_tag(self, pc: int) -> int:
        return pc >> (2 + (self.btb_entries.bit_length() - 1))

    def _bht_idx(self, pc: int) -> int:
        return (pc >> 2) % self.bht_entries

    def copy(self) -> "BpredModel":
        return BpredModel(self.btb_entries, self.bht_entries, self.unknown_counters,
                          dict(self.btb), dict(self.bht))

    def _counter(self, idx: int) -> frozenset:
        if idx in self.bht:
            return self.bht[idx]
        return frozenset(range(4)) if self.unknown_counters else frozenset({0})

    def predict(self, pc: int) -> frozenset:
        """Every (taken, target) a lookup of ``pc`` can give.

        The target is meaningful only when taken (the RTL drives the indexed
        entry's target on a miss; nothing reads it); a miss gives 0.
        """
        entry = self.btb.get(self._btb_idx(pc))
        if entry is None or entry[0] != self._btb_tag(pc):
            return frozenset({(False, 0)})
        _, target, uncond = entry
        if uncond:
            return frozenset({(True, target << 2)})
        idx = self._bht_idx(pc)
        assert self.unknown_counters or idx in self.bht, (
            f"pc 0x{pc:08x}: a conditional BTB hit read a BHT counter no update ever wrote")
        return frozenset((bool(c >> 1), target << 2) for c in self._counter(idx))

    def predict_one(self, pc: int) -> tuple:
        """The single prediction of an exact model (the unit test)."""
        preds = self.predict(pc)
        assert len(preds) == 1, f"pc 0x{pc:08x}: the model is not exact here: {preds}"
        return next(iter(preds))

    def update(self, pc: int, cond: bool, uncond: bool, taken: bool, target: int,
               pred_taken: bool) -> None:
        """One resolved instruction (the RTL's upd_* port).

        A taken conditional branch that does not hit a conditional entry is
        installing it, and writes its counter to weakly not taken (1)
        instead of stepping it: the counter's old value may be one nothing
        wrote.  1 is a zeroed counter after one taken step.
        """
        if cond:
            idx = self._bht_idx(pc)
            entry = self.btb.get(self._btb_idx(pc))
            cond_hit = entry is not None and entry[0] == self._btb_tag(pc) and not entry[2]
            if taken and not cond_hit:
                self.bht[idx] = frozenset({1})
            else:
                self.bht[idx] = frozenset(min(c + 1, 3) if taken else max(c - 1, 0)
                                          for c in self._counter(idx))
        if taken and (cond or uncond):
            self.btb[self._btb_idx(pc)] = (self._btb_tag(pc), (target & MASK32) >> 2, uncond)
        elif not cond and not uncond and pred_taken:
            self.btb.pop(self._btb_idx(pc), None)


# ---------------------------------------------------------------------------
# Retire-trace check
# ---------------------------------------------------------------------------

def resolve(beat: dict) -> dict:
    """Decode a retired beat into its predictor update and outcome."""
    insn = beat["insn"]
    opc = insn & 0x7F
    pc = beat["pc"]
    cond = opc == OPC_BRANCH
    uncond = opc in (OPC_JAL, OPC_JALR)
    if cond:
        f3 = (insn >> 12) & 7
        a, b = beat["rs1_rdata"], beat["rs2_rdata"]
        taken = {0: a == b, 1: a != b, 4: _signed(a) < _signed(b),
                 5: _signed(a) >= _signed(b), 6: a < b, 7: a >= b}[f3]
    else:
        taken = uncond
    target = beat["pc_wdata"] if taken else (pc + 4) & MASK32
    return {"pc": pc, "cond": cond, "uncond": uncond, "taken": taken,
            "target": target, "next": target}


@dataclass
class TraceVerdict:
    beats: int = 0
    control: int = 0
    taken: int = 0
    mispredicts: int = 0
    ambiguous: int = 0           # beats where two allowed states predicted differently
    errors: list = field(default_factory=list)


def check_trace(trace: list, bp_en: bool, btb_entries: int = 32,
                bht_entries: int = 256, max_errors: int = 5,
                unknown_counters: bool = True) -> TraceVerdict:
    """Hold every retired beat's prediction to the model (see the module doc).

    Traces with interrupts are out of scope: an interrupted branch resolved
    in EX, but its retire beat reports the trap target, not its outcome.
    """
    v = TraceVerdict()
    model = BpredModel(btb_entries, bht_entries, unknown_counters)
    # states[j] = model after the updates of beats < j; only the last four
    # are needed (lookups see at most three beats back).
    history = [model.copy()]
    redirected = False           # did the previous beat redirect the fetch?
    for k, beat in enumerate(trace):
        v.beats += 1
        assert not (beat["trap"] and beat["trap_cause"] >> 31), \
            "check_trace does not model interrupted instructions"
        got = (bool(beat["bp_pred_taken"]), beat["bp_pred_target"])
        n = len(history)
        allowed = []
        # history[-1] = through beat k-1, [-2] = through k-2, [-3] = through k-3.
        if redirected:
            allowed.append(history[-1])
        for back in (2, 3):
            if n >= back:
                allowed.append(history[-back])
            elif n >= 1:
                allowed.append(history[0])
        preds = set().union(*(s.predict(beat["pc"]) for s in allowed))
        if not bp_en:
            preds = {(False, 0)}
        if len(preds) > 1:
            v.ambiguous += 1

        def norm(p):
            # A not-taken guess carries no meaningful target.
            return (p[0], p[1] if p[0] else None)

        if norm(got) not in {norm(p) for p in preds} and len(v.errors) < max_errors:
            v.errors.append(f"beat {k} pc=0x{beat['pc']:08x} insn=0x{beat['insn']:08x}: "
                            f"predicted {norm(got)}, model allows {sorted(map(str, {norm(p) for p in preds}))}")

        r = resolve(beat)
        trap = bool(beat["trap"])
        if trap:
            # An exception: the instruction left EX not taken (a control
            # instruction that traps is excluded from the streams).
            r.update({"taken": False, "next": (beat["pc"] + 4) & MASK32})
            assert not (r["cond"] or r["uncond"]), \
                f"beat {k}: a trapping control-flow instruction is not modelled"
        want_mp = (got[0] != r["taken"]) or (r["taken"] and got[1] != r["target"])
        if bool(beat["bp_mispredict"]) != want_mp and len(v.errors) < max_errors:
            v.errors.append(f"beat {k} pc=0x{beat['pc']:08x}: mispredict flag "
                            f"{beat['bp_mispredict']}, prediction {got} against outcome "
                            f"taken={r['taken']} next=0x{r['next']:08x}")
        v.control += int(r["cond"] or r["uncond"])
        v.taken += int(r["taken"])
        v.mispredicts += int(bool(beat["bp_mispredict"]))

        model.update(r["pc"], r["cond"], r["uncond"], r["taken"], r["target"], got[0])
        history.append(model.copy())
        if len(history) > 4:
            history.pop(0)
        insn = beat["insn"]
        is_mret = insn == 0x3020_0073
        is_fencei = (insn & 0x707F) == 0x100F
        redirected = bool(beat["bp_mispredict"]) or trap or is_mret or is_fencei
    return v
