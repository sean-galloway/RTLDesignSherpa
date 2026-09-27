"""A JEDEC legality checker for an issued DRAM command stream.

WHAT IT IS. Give it the commands a controller issued -- each `{cycle, op, bank,
row, col, ap}` -- plus the timing set in MC cycles, and it replays them through a
per-bank state model and every command-to-command minimum, and returns the
violations plus a count of how many times each rule was EVALUATED.

WHY THE EVALUATION COUNTS MATTER. "Zero violations" from a checker that never
armed is the failure mode this repo keeps rediscovering
(feedback_checker_verdict_needs_a_count: four blind checkers, and armed-plus-count
still was not enough once). A rule that fired zero times is a rule that proved
nothing, and the caller can only tell the difference if the checker says so. So
`stats` is part of the result, not a debug aid, and `assert_clean` refuses a
verdict when the rules it names never evaluated.

WHY IT IS NOT IN THE TEST. Three reasons, in order of how much they cost when
ignored: it is the piece that ports to DDR3/LPDDR3 unchanged (it consumes derived
cycle counts and never asks which family produced them); it is shared by the
scheduler layer and the top layer, which must agree about what legal means; and
an oracle written inline next to one stimulus grows to fit that stimulus. The
version this replaces tracked only open-vs-closed per bank -- so a read to a bank
open on the WRONG ROW, which is just as illegal and is what a stale row image
produces, was invisible to it.

WHAT IT DELIBERATELY DOES NOT DO. It does not check data, it does not model the
PHY, and it does not check tREFI (a refresh interval is a MAXIMUM, and a stream
that refreshes too rarely is a correctness question for the refresh engine's own
tests, not a per-command legality question). It checks what a DRAM would reject.
"""

from collections import deque

# Opcodes, as the scheduler encodes them. Auto-precharge arrives either as a
# distinct opcode or as the `ap` flag beside a plain column op; both are handled,
# because the scheduler uses the flag and the DFI formatter uses the opcode.
OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA, OP_PRE, OP_PREA, OP_REF, \
    OP_REFPB, OP_MRS = range(11)

OP_NAMES = {OP_NOP: 'NOP', OP_ACT: 'ACT', OP_RD: 'RD', OP_RDA: 'RDA',
            OP_WR: 'WR', OP_WRA: 'WRA', OP_PRE: 'PRE', OP_PREA: 'PREA',
            OP_REF: 'REF', OP_REFPB: 'REFPB', OP_MRS: 'MRS'}

_READS = (OP_RD, OP_RDA)
_WRITES = (OP_WR, OP_WRA)
_COLS = _READS + _WRITES

# Every rule this checker knows. Named so a caller can require a specific subset
# to have armed rather than trusting that "some checking happened".
STATE_RULES = ('col_on_closed', 'col_on_wrong_row', 'act_on_open',
               'ref_with_open_bank', 'refpb_on_open_bank', 'two_cmds_one_cycle')
TIMING_RULES = ('tRCD', 'tRP', 'tRAS', 'tRC', 'tRTP', 'tWR', 'tRRD', 'tFAW',
                'tCCD', 'tWTR', 'tRTW', 'tRFC')
ALL_RULES = STATE_RULES + TIMING_RULES


def _fmt(c):
    """One command, as it reads in a trail: OP(ap)[row]@cycle."""
    parts = [OP_NAMES.get(c['op'], str(c['op']))]
    if c.get('ap'):
        parts.append("(ap)")
    if c.get('row') is not None:
        parts.append(f"[r0x{c['row']:x}]")
    parts.append(f"@{c['cycle']}")
    return "".join(parts)


class Violation(dict):
    def __str__(self):
        head = (f"{self['rule']} @cyc {self['cycle']} "
                f"{OP_NAMES.get(self['op'], self['op'])} bank={self['bank']}: "
                f"{self['detail']}")
        ctx = self.get('context') or ()
        if not ctx:
            return head
        return (head + f"\n      bank {self['bank']} trail: "
                + " -> ".join(_fmt(x) for x in ctx))


class CmdStreamChecker:
    """Replay an issued command stream and report JEDEC violations.

    ``timings`` is the controller's MC-cycle set -- the dict
    ``pumice_dram_configs.dram_config()`` returns as its second element, keyed
    tRCD/tRP/tRAS/tRC/tWR/tRTP/tRRD/tFAW/tCCD/tWTR/tRTW/tRFC.
    """

    def __init__(self, timings, *, num_banks=8, label="", tfaw_acts=4,
                 bl=4, ck_per_mc=2):
        self.t = dict(timings)
        self.num_banks = num_banks
        self.label = label
        self.tfaw_acts = tfaw_acts          # 4 for x8/x16 DDR2
        # Burst length matters on the auto-precharge path only: JESD79-2F gives
        # the internal precharge point as AL + BL/2 after the column, so BL8
        # pushes it two CK further out than BL4.
        self.bl = bl
        self.ck_per_mc = ck_per_mc

    # ---- internals ---------------------------------------------------------
    def _blank(self):
        # per bank: open row (None == precharged), and the cycle each
        # command-to-command minimum out of this bank becomes satisfiable.
        return dict(row=None, act_cyc=None, last_col=None, last_rd=None,
                    last_wr=None, pre_cyc=None, ok_act=0, ok_col=0, ok_pre=0)

    def check(self, cmds, since=0):
        """Return (violations, stats) for ``cmds[since:]``, REPLAYED FROM 0.

        WHY ``since`` EXISTS, AND WHY SLICING INSTEAD IS WRONG. Bank state is
        carried, not local: the ACT that opened a bank can be hundreds of
        commands and several test phases earlier. Hand this checker only the tail
        of a stream and it starts with every bank idle, so the first column in
        the slice looks like a column to a closed bank -- a false BUG-003 report,
        which is exactly what the matrix produced on its first run. The identical
        mistake had already cost 38 of 39 points in the BUG-003 test's own
        baseline, which is why it gets a paragraph rather than a comment.

        So the replay ALWAYS starts at index 0 and builds true state; ``since``
        gates only what is REPORTED -- violations and armed counts alike.

        ``stats[rule]`` is the EVALUATION count: how many times the rule was
        reached, whether or not it fired. A caller uses it to reject a green
        verdict from a rule that never armed.
        """
        bk = [self._blank() for _ in range(self.num_banks)]
        v, stats = [], {r: 0 for r in ALL_RULES}
        acts = deque()                # ACT cycles, for tFAW
        last_act_any = None           # tRRD
        last_col_any = None           # tCCD
        last_wr_any = None            # tWTR
        last_rd_any = None            # tRTW
        last_ref = None               # tRFC
        seen_cycle = None
        cmds = [dict(x, _idx=i) for i, x in enumerate(cmds)]
        cur = {'c': None}             # the command being replayed

        def reported():
            return cur['c'].get('_idx', 0) >= since

        def arm(rule):
            if reported():
                stats[rule] += 1

        def bad(rule, c, detail):
            if not reported():
                return
            # CARRY THE CONTEXT. A violation names one command, but the question
            # is always "what did this bank just do?", and reconstructing that by
            # hand from a 500-command stream is where triage time goes.
            here = c.get('_idx', 0)
            ctx = [x for x in cmds[max(0, here - 40):here + 1]
                   if x.get('bank') == c.get('bank')][-6:]
            v.append(Violation(rule=rule, cycle=c.get('cycle'), op=c.get('op'),
                               bank=c.get('bank'), row=c.get('row'),
                               col=c.get('col'), detail=detail,
                               label=self.label, context=ctx))

        def gap_at(rule, c, at, prev, need, what):
            """A minimum separation ending at cycle ``at``. Arms even if it passes."""
            if prev is None:
                return
            arm(rule)
            got = at - prev
            if got < need:
                bad(rule, c, f"{what}: {got} cycles, need {need}")

        def gap(rule, c, prev, need, what):
            gap_at(rule, c, c['cycle'], prev, need, what)

        for c in cmds:
            cur['c'] = c
            op = c['op']
            if op in (OP_NOP, OP_MRS):
                continue
            cyc = c['cycle']
            b = c.get('bank', 0)
            ap = bool(c.get('ap')) or op in (OP_RDA, OP_WRA)

            # One command bus: two commands cannot share a cycle.
            arm('two_cmds_one_cycle')
            if seen_cycle is not None and cyc == seen_cycle:
                bad('two_cmds_one_cycle', c, "a second command on this cycle")
            seen_cycle = cyc

            if op == OP_ACT:
                st = bk[b]
                arm('act_on_open')
                if st['row'] is not None:
                    bad('act_on_open', c,
                        f"row 0x{st['row']:x} still open (opened @{st['act_cyc']})")
                gap('tRP', c, st['pre_cyc'], self.t['tRP'], "PRE -> ACT same bank")
                gap('tRC', c, st['act_cyc'], self.t['tRC'], "ACT -> ACT same bank")
                gap('tRRD', c, last_act_any, self.t['tRRD'], "ACT -> ACT any bank")
                gap('tRFC', c, last_ref, self.t['tRFC'], "REF -> ACT")
                # tFAW: at most tfaw_acts ACTs in any tFAW window.
                while acts and cyc - acts[0] >= self.t['tFAW']:
                    acts.popleft()
                arm('tFAW')
                if len(acts) >= self.tfaw_acts:
                    bad('tFAW', c,
                        f"{len(acts) + 1} ACTs within tFAW={self.t['tFAW']} "
                        f"(window opened @{acts[0]})")
                acts.append(cyc)
                st.update(row=c.get('row'), act_cyc=cyc, pre_cyc=None,
                          last_rd=None, last_wr=None, last_col=None)
                last_act_any = cyc

            elif op in _COLS:
                st = bk[b]
                arm('col_on_closed')
                if st['row'] is None:
                    bad('col_on_closed', c, "no open row on this bank")
                else:
                    # WRONG-ROW IS OPT-IN, because the row is NOT on the command
                    # bus for a column op -- a DRAM infers it from the ACT that
                    # opened the bank. A caller that can supply the REQUEST's
                    # intended row (the top level can; the scheduler's output pins
                    # cannot) passes it as `row` and gets the check. A caller that
                    # passes None gets silence, rather than a verdict
                    # manufactured out of a don't-care field.
                    if c.get('row') is not None:
                        arm('col_on_wrong_row')
                        if c['row'] != st['row']:
                            bad('col_on_wrong_row', c,
                                f"bank is open on row 0x{st['row']:x}, command "
                                f"targets row 0x{c['row']:x}")
                    gap('tRCD', c, st['act_cyc'], self.t['tRCD'],
                        "ACT -> column same bank")
                gap('tCCD', c, last_col_any, self.t['tCCD'], "column -> column")
                if op in _READS:
                    gap('tWTR', c, last_wr_any, self.t['tWTR'], "WR -> RD")
                    st['last_rd'] = cyc
                    last_rd_any = cyc
                else:
                    gap('tRTW', c, last_rd_any, self.t['tRTW'], "RD -> WR")
                    st['last_wr'] = cyc
                    last_wr_any = cyc
                st['last_col'] = cyc
                last_col_any = cyc
                if ap:
                    # AUTO-PRECHARGE, per JESD79-2F 3.8.1 (quoted because this
                    # checker got it wrong once and reported 16 violations
                    # against correct RTL):
                    #
                    #   "The DDR2 SDRAM starts an Auto Precharge operation on the
                    #    rising edge which is (AL + BL/2) cycles later than the
                    #    read with AP command IF tRAS(min) and tRTP(min) are
                    #    satisfied. If tRAS(min) is not satisfied at the edge,
                    #    the start point of auto-precharge operation will be
                    #    delayed until tRAS(min) is satisfied."
                    #
                    # So tRAS and tRTP are enforced BY THE DEVICE on this path,
                    # not by the controller: issuing the AP column early is legal
                    # and simply postpones the internal precharge. Flagging it as
                    # a tRAS violation was wrong -- and pumice models the spec
                    # correctly, holding its own row image open until r_ras and
                    # r_preblk expire (bank_timer.sv w_ap_fire). A controller
                    # that delayed the column instead would only lose bandwidth.
                    #
                    # What the model must get right is WHEN the precharge starts,
                    # because tRP runs from there and the next ACT is checked
                    # against it: the later of the burst end and tRAS.
                    burst = max(0, (self.bl // 2 - 2)) // self.ck_per_mc
                    delay = (self.t['tRTP'] if op in _READS else self.t['tWR'])
                    pre_at = max(cyc + delay + burst,
                                 (st['act_cyc'] or 0) + self.t['tRAS'])
                    st.update(row=None, pre_cyc=pre_at)

            elif op in (OP_PRE, OP_PREA):
                targets = range(self.num_banks) if op == OP_PREA else (b,)
                for tb in targets:
                    st = bk[tb]
                    # An explicit PRE to an already-idle bank is LEGAL on DDR2
                    # (it is a no-op), so it is not flagged -- only its timing is.
                    gap('tRAS', c, st['act_cyc'], self.t['tRAS'],
                        f"ACT -> PRE bank {tb}")
                    gap('tRTP', c, st['last_rd'], self.t['tRTP'],
                        f"RD -> PRE bank {tb}")
                    gap('tWR', c, st['last_wr'], self.t['tWR'],
                        f"WR -> PRE bank {tb}")
                    st.update(row=None, pre_cyc=cyc)

            elif op == OP_REF:
                # All-bank refresh needs every bank precharged.
                arm('ref_with_open_bank')
                openb = [i for i, st in enumerate(bk) if st['row'] is not None]
                if openb:
                    bad('ref_with_open_bank', c,
                        f"banks {openb} still open at an all-bank REF")
                for st in bk:
                    st.update(row=None, pre_cyc=cyc, last_rd=None, last_wr=None)
                last_ref = cyc

            elif op == OP_REFPB:
                arm('refpb_on_open_bank')
                if bk[b]['row'] is not None:
                    bad('refpb_on_open_bank', c, "per-bank REF to an open bank")
                bk[b].update(row=None, pre_cyc=cyc, last_rd=None, last_wr=None)
                last_ref = cyc

        return v, stats


def assert_clean(cmds, timings, *, num_banks=8, label="", require=(),
                 min_cmds=1, log=None, since=0, bl=4, ck_per_mc=2):
    """Check ``cmds`` and raise AssertionError on a violation OR a vacuous pass.

    ``require`` names rules that MUST have evaluated at least once. Pass the
    rules the stimulus was built to exercise: a stream that never precharges
    cannot prove anything about tRP, and a green result that does not say so is
    the blind-checker failure this repo has hit four times.
    """
    n_new = len(cmds) - since
    assert n_new >= min_cmds, (
        f"[{label}] only {n_new} commands issued (need >= {min_cmds}); the "
        f"stimulus did not run, so any verdict about it is meaningless.")
    ck = CmdStreamChecker(timings, num_banks=num_banks, label=label,
                          bl=bl, ck_per_mc=ck_per_mc)
    v, stats = ck.check(cmds, since=since)
    armed = {r: n for r, n in stats.items() if n}
    if log is not None:
        log.info("[%s] %d commands, %d rules armed (%s), %d violations", label,
                 n_new, len(armed),
                 " ".join(f"{r}={n}" for r, n in sorted(armed.items())), len(v))
    missing = [r for r in require if not stats.get(r)]
    assert not missing, (
        f"[{label}] VACUOUS: rules {missing} never evaluated over "
        f"{n_new} commands, so their verdict proves nothing. Rules that did "
        f"arm: {sorted(armed)}.")
    assert not v, (
        f"[{label}] {len(v)} JEDEC violations over {n_new} commands; "
        f"first 8:\n  " + "\n  ".join(str(x) for x in v[:8]))
    return stats
