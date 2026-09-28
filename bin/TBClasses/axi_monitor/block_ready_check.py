# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Shared block_ready validation for EVERY axi*_{master,slave}_{rd,wr}_mon wrapper.

THE INVARIANT NOTHING CHECKED
-----------------------------
    every command ADMITTED at the gated handshake must get a table entry

block_ready gates the upstream command handshake:

    fub_axi_arready = w_core_fub_axi_arready & (w_block_ready | ~cfg_monitor_enable)

so a command is only supposed to be admitted when the monitor has room. If that
gate is wrong the command is accepted WITHOUT an entry, and its data beats
arrive later with nothing to match. Unmatched data/resp allocation is
deliberately NOT gated -- a monitor must never stall returning data -- so at a
full table those beats are silently discarded.

The dropped data is a SYMPTOM. The defect is admitting a command that cannot be
tracked: stop the commands correctly and there is no orphaned data to drop.

WHY EVERY WRAPPER NEEDS THIS, NOT JUST ONE
------------------------------------------
All twelve wrappers (axi4 / axi5 / axil4 x master/slave x rd/wr) share
axi_monitor_base and therefore share this gate. The existing suite covers:

    *_cfg.py                 only that a DISABLED monitor forces block_ready high
    test_axi_monitor_trans_mgr  drives unmatched data for IDs it never allocated,
                             i.e. constructs the symptom -- its assertion is
                             occupancy <= depth, which stays true while beats are
                             dropped
    everything else          never saturates

So the suite is green on a monitor that loses a quarter of its bursts under
saturation (harness: observer 4096 vs in-core 3073, identical at 2,000 and
200,000 clocks of drain, so loss and not backlog).

WHAT IS OBSERVED, AND WHY IT IS A PORT
--------------------------------------
The wrappers expose `debug_block_ready` -- the SAME net that gates the command
handshake, brought out so it can be watched directly. It is a port and not a
hierarchical reference because both hierarchy mechanisms fail SILENTLY here:
the sby harness saw `dut.w_block_ready` elaborate as an implicitly-declared
FREE wire, making the gating properties vacuous, and a cocotb probe of an
unresolved path returns None and passes unconditionally.

That distinction matters for a second reason. A test can drive large response
delays and look like it is exercising backpressure while never filling the
table at all. Without watching the block signal there is no way to tell a real
saturation run from a run that simply never got there -- so a green result
means nothing. assert_saturation_reached() closes that hole: no block, no
verdict.

THREE LAYERS, WEAKEST TO STRONGEST
----------------------------------
    1. saturation coverage   debug_block_ready actually went low        (port)
    2. gating contract       blocked + enabled -> no command admitted   (port)
    3. admission invariant   no command admitted while the table is full  (port)

Layer 3 is the documented lossy degrade made countable. axi_monitor_base.sv
accepts untracked commands at the cap deliberately -- lossy-but-honest rather
than the permanent stall a wider BLOCK_MARGIN causes -- so this is a
MEASUREMENT that happens to assert zero, not a claim the RTL forbids it. If a
future change makes the loss real, the number moves off zero here instead of
surfacing as missing packets three layers up.

Layer 2 is the sim twin of the in-RTL ap_block_ready_gating property. Layer 3
is the one that catches THIS defect: the gate faithfully follows block_ready,
but block_ready itself is computed against a stale count, so layers 1 and 2
both pass while commands are admitted with nowhere to go.

THE LITE WRAPPERS INVERT THE CONTRACT
------------------------------------
axi*_{master,slave}_{rd,wr}_monlite (amba/monitor-lite) has NO block_ready and
never gates the command handshake: a command that finds no free entry is
admitted untracked and COUNTED on the `refused_count` port. So the three layers
become, for LiteRefuseCheck:

    1. saturation coverage   occupancy reached the depth and refused_count moved
    2. refuse accounting     every command admitted while the table was full is
                             in refused_count -- none went missing silently
    3. admission invariant   occupancy never exceeded the depth

Layer 2 is the lite's whole promise: it may lose a transaction under pressure
but it must SAY so. A refused_count that lags admitted_while_full means the
lite lost a command and told nobody, which is the same defect the full
monitor's layer 3 exists to catch.

USAGE
-----
    from TBClasses.axi_monitor.block_ready_check import BlockReadyCheck

    chk = BlockReadyCheck(dut, tb.log, depth=MAX_TRANSACTIONS)
    chk.start()
    ...drive traffic that saturates the table...
    chk.stop()
    chk.assert_saturation_reached()        # the run is meaningful
    chk.assert_gating_contract()           # the gate obeys the signal
    chk.assert_no_untracked_admissions()   # the signal is correct

Related: [[AMBA-BLOCKMARGIN]].
"""
from __future__ import annotations

import cocotb
from cocotb.triggers import RisingEdge


class BlockReadyCheck:
    """Watches admissions, occupancy and block_ready -- all through ports.

    Nothing here reaches into the hierarchy. An earlier version walked down to
    the transaction manager for the allocation one-hot; under Verilator's
    --public-flat-rw the path did not resolve, and an unresolved probe returns
    None and passes unconditionally. Every quantity below is a port, so the
    check either binds or refuses to run.

    Channel prefixes still vary across the twelve wrappers (ar/aw,
    fub_axi_/fub_axil_/s_axi_), so the handshake is discovered by trying the
    known names.
    """

    # (valid, ready) candidates for the GATED upstream command handshake.
    #
    # ORDER MATTERS, and getting it wrong does not fail loudly -- it binds to a
    # real handshake that simply is not the gated one, then reports its normal
    # traffic as gating violations. A wrapper has BOTH sides:
    #
    #   master mon:  fub_axi_* upstream (GATED)   m_axi_*   downstream
    #   slave  mon:  s_axi_*   upstream (GATED)   fub_axi_* downstream
    #
    # so `fub_axi_*` is the gated side on a master and the free-running side on
    # a slave. Trying fub_* first bound every slave wrapper to its downstream
    # side and charged it 33 "violations" of a gate that never applied there.
    # s_axi_*/s_axil_* only exists on the slave wrappers, so preferring it is
    # unambiguous.
    _CMD_HANDSHAKES = [
        ("s_axi_arvalid",    "s_axi_arready"),
        ("s_axi_awvalid",    "s_axi_awready"),
        ("s_axil_arvalid",   "s_axil_arready"),
        ("s_axil_awvalid",   "s_axil_awready"),
        ("fub_axi_arvalid",  "fub_axi_arready"),
        ("fub_axi_awvalid",  "fub_axi_awready"),
        ("fub_axil_arvalid", "fub_axil_arready"),
        ("fub_axil_awvalid", "fub_axil_awready"),
    ]

    def __init__(self, dut, log, depth):
        self.dut = dut
        self.log = log
        self.depth = depth
        self.peak_occupancy = 0
        self.admitted_while_full = 0
        self.accepted = 0
        self.block_ready_low_cycles = 0
        self.total_cycles = 0
        self._task = None
        self._stop = False

        self.gating_violations = 0

        self.cmd_valid, self.cmd_ready = self._find_handshake()
        self.cfg_enable = getattr(dut, "cfg_monitor_enable", None)

        # The observability port. Required -- see the module docstring on why
        # this is a port. Falling back to a hierarchical probe would reintroduce
        # exactly the silent-pass failure the port exists to remove.
        self.block_ready = getattr(dut, "debug_block_ready", None)
        if self.block_ready is None:
            raise RuntimeError(
                f"{type(dut).__name__} has no debug_block_ready port. Every "
                "axi*_{master,slave}_{rd,wr}_mon wrapper must bring the gating "
                "net out for observation; without it this check cannot tell a "
                "real saturation run from one that never filled the table, and "
                "would report a meaningless pass.")

        # Occupancy, already a port on every wrapper.
        self.occupancy = getattr(dut, "active_transactions", None)

        if self.cmd_valid is None or self.occupancy is None:
            raise RuntimeError(
                "BlockReadyCheck could not bind: "
                f"handshake={'ok' if self.cmd_valid is not None else 'NOT FOUND'}, "
                f"active_transactions={'ok' if self.occupancy is not None else 'NOT FOUND'}. "
                "Refusing to run -- a check that binds to nothing would pass "
                "unconditionally and hide the very defect it exists to catch.")

    # ---- discovery ------------------------------------------------------
    def _find_handshake(self):
        for v, r in self._CMD_HANDSHAKES:
            sv, sr = getattr(self.dut, v, None), getattr(self.dut, r, None)
            if sv is not None and sr is not None:
                self.log.info(f"BlockReadyCheck: command handshake {v}/{r}")
                return sv, sr
        return None, None

    # ---- sampling -------------------------------------------------------
    async def _sample(self):
        while not self._stop:
            await RisingEdge(self.dut.aclk)
            self.total_cycles += 1
            try:
                admitted = bool(int(self.cmd_valid.value)
                                and int(self.cmd_ready.value))
                blocked = not int(self.block_ready.value)
                occ = int(self.occupancy.value)
                enabled = (self.cfg_enable is None
                           or bool(int(self.cfg_enable.value)))
            except ValueError:
                continue                   # X/Z during reset -- no verdict

            self.peak_occupancy = max(self.peak_occupancy, occ)

            if admitted:
                self.accepted += 1
                # Layer 3: this command cannot get a slot -- the table is
                # already full. Whatever block_ready said, admitting here means
                # the command is untracked and its data will arrive unmatched.
                if enabled and occ >= self.depth:
                    self.admitted_while_full += 1
            if blocked:
                self.block_ready_low_cycles += 1
                # Layer 2: the sim twin of ap_block_ready_gating. A disabled
                # monitor is exempt -- it must never stall the datapath.
                if enabled and admitted:
                    self.gating_violations += 1

    def start(self):
        self._stop = False
        self._task = cocotb.start_soon(self._sample())

    def stop(self):
        self._stop = True

    # ---- the assertions -------------------------------------------------
    def assert_saturation_reached(self, min_cycles=1):
        """Layer 1: a pass means nothing if the table never filled.

        Large response delays LOOK like backpressure without producing any. A
        run that never blocked has not tested blocking, so it gets no verdict
        rather than a free pass.
        """
        assert self.block_ready_low_cycles >= min_cycles, (
            f"debug_block_ready went low on {self.block_ready_low_cycles} "
            f"cycles (needed {min_cycles}) -- the table never saturated, so "
            f"this run says NOTHING about admission under pressure "
            f"({self.accepted} commands over {self.total_cycles} cycles). "
            "Raise the outstanding depth or slow the response side; do not "
            "treat this as a pass.")

    def assert_gating_contract(self):
        """Layer 2: while blocked and enabled, no command may be admitted."""
        assert self.gating_violations == 0, (
            f"{self.gating_violations} command handshakes completed while "
            "debug_block_ready was LOW and the monitor was enabled. The "
            "wrapper gate is broken: "
            "ready = core_ready & (block_ready | ~cfg_monitor_enable) "
            "should make this impossible.")

    def assert_no_untracked_admissions(self, depth=None):
        """Layer 3: no command may be admitted into a full table."""
        depth = depth or self.depth
        assert self.accepted > 0, (
            "no command handshakes observed -- the stimulus never reached the "
            "monitor, so a pass would be meaningless")
        assert self.peak_occupancy <= depth, (
            f"occupancy peaked at {self.peak_occupancy} with only {depth} "
            "entries -- the table overflowed.")
        assert self.admitted_while_full == 0, (
            f"{self.admitted_while_full} of {self.accepted} commands were "
            f"ADMITTED while the table already held {depth}/{depth} entries "
            "(peak "
            f"{self.peak_occupancy}). Those commands cannot be tracked.\n\n"
            "block_ready let them through against a STALE active_count -- a "
            "registered pop-count, one cycle behind. Their data beats arrive "
            "with nothing to match, and unmatched data allocation is not gated "
            "(a monitor must never stall returning data), so the beats are "
            "discarded.\n"
            "BLOCK_MARGIN must cover every allocator that can fire during the "
            "stale cycle -- addr, data and resp, i.e. 3. See "
            "[[amba BUG-030 (was AMBA-BLOCKMARGIN)]].")

    def summary(self) -> str:
        return (f"admitted={self.accepted} peak_occupancy="
                f"{self.peak_occupancy}/{self.depth} "
                f"admitted_while_full={self.admitted_while_full} "
                f"gating_violations={self.gating_violations} "
                f"block_ready_low={self.block_ready_low_cycles}/"
                f"{self.total_cycles} cycles")


class LiteRefuseCheck:
    """The lite wrappers' counterpart of BlockReadyCheck (see the module doc).

    Same discovery, same port-only discipline. Instead of a block signal it
    watches `refused_count`, and its layer 2 is an accounting identity rather
    than a gating rule: commands admitted at full occupancy == refused_count.
    """

    _CMD_HANDSHAKES = BlockReadyCheck._CMD_HANDSHAKES

    def __init__(self, dut, log, depth):
        self.dut = dut
        self.log = log
        self.depth = depth
        self.peak_occupancy = 0
        self.admitted_while_full = 0
        self.accepted = 0
        self.full_cycles = 0
        self.total_cycles = 0
        self.final_refused = None
        self._task = None
        self._stop = False
        self.cmd_valid, self.cmd_ready = self._find_handshake()
        # The matching RESPONSE handshake on the same side (ar->r, aw->b): a
        # bus-level outstanding count that owes nothing to the DUT. When the
        # DUT's occupancy never fills, this says whether the STIMULUS ever put
        # `depth` transactions in flight -- the difference between "the lite
        # never refused" and "the traffic never asked".
        self.rsp_valid, self.rsp_ready = self._find_response()
        self.bus_outstanding = 0
        self.peak_bus_outstanding = 0
        self.completed = 0
        self.cfg_enable = getattr(dut, "cfg_monitor_enable", None)
        self.refused = getattr(dut, "refused_count", None)
        self.occupancy = getattr(dut, "active_transactions", None)
        self.tracked = getattr(dut, "transaction_count", None)
        if self.refused is None:
            raise RuntimeError(
                f"{type(dut).__name__} has no refused_count port. Every "
                "_monlite wrapper brings the refused counter out; without it "
                "a lost command is indistinguishable from one never issued.")
        if self.cmd_valid is None or self.occupancy is None:
            raise RuntimeError(
                "LiteRefuseCheck could not bind: "
                f"handshake={'ok' if self.cmd_valid is not None else 'NOT FOUND'}, "
                f"active_transactions={'ok' if self.occupancy is not None else 'NOT FOUND'}.")
        if getattr(dut, "debug_block_ready", None) is not None:
            raise RuntimeError(
                f"{type(dut).__name__} exposes debug_block_ready -- that is a "
                "full monitor; use BlockReadyCheck. Running the lite check on "
                "it would pass while measuring nothing about the gate.")

    def _find_handshake(self):
        for v, r in self._CMD_HANDSHAKES:
            sv, sr = getattr(self.dut, v, None), getattr(self.dut, r, None)
            if sv is not None and sr is not None:
                self.log.info(f"LiteRefuseCheck: command handshake {v}/{r}")
                self._cmd_names = (v, r)
                return sv, sr
        self._cmd_names = None
        return None, None

    def _find_response(self):
        if not getattr(self, "_cmd_names", None):
            return None, None
        v, r = self._cmd_names
        rv = v.replace("arvalid", "rvalid").replace("awvalid", "bvalid")
        rr = r.replace("arready", "rready").replace("awready", "bready")
        sv, sr = getattr(self.dut, rv, None), getattr(self.dut, rr, None)
        if sv is not None and sr is not None:
            self.log.info(f"LiteRefuseCheck: response handshake {rv}/{rr}")
        return sv, sr

    async def _sample(self):
        while not self._stop:
            await RisingEdge(self.dut.aclk)
            self.total_cycles += 1
            try:
                admitted = bool(int(self.cmd_valid.value)
                                and int(self.cmd_ready.value))
                occ = int(self.occupancy.value)
                enabled = (self.cfg_enable is None
                           or bool(int(self.cfg_enable.value)))
                refused = int(self.refused.value)
            except ValueError:
                continue
            self.final_refused = refused
            self.peak_occupancy = max(self.peak_occupancy, occ)
            if occ >= self.depth:
                self.full_cycles += 1
            if admitted:
                self.accepted += 1
                self.bus_outstanding += 1
                if enabled and occ >= self.depth:
                    self.admitted_while_full += 1
            if self.rsp_valid is not None:
                try:
                    done = bool(int(self.rsp_valid.value) and int(self.rsp_ready.value))
                    last = getattr(self.dut, self._cmd_names[0].replace("arvalid", "rlast").replace("awvalid", "bvalid"), None)
                    if done and (last is None or "bvalid" in self._cmd_names[0].replace("awvalid", "bvalid") or int(last.value)):
                        self.completed += 1
                        self.bus_outstanding -= 1
                except ValueError:
                    pass
            self.peak_bus_outstanding = max(self.peak_bus_outstanding, self.bus_outstanding)

    def start(self):
        self._stop = False
        self._task = cocotb.start_soon(self._sample())

    def stop(self):
        self._stop = True

    def assert_saturation_reached(self, min_cycles=1):
        """Layer 1: the table filled and at least one command was refused."""
        assert self.full_cycles >= min_cycles and (self.final_refused or 0) > 0, (
            f"table full on {self.full_cycles} cycles, refused_count="
            f"{self.final_refused} -- the lite never ran out of entries, so "
            f"this run says NOTHING about admission under pressure "
            f"({self.accepted} commands over {self.total_cycles} cycles; the "
            f"bus itself peaked at {self.peak_bus_outstanding} outstanding, so "
            + ("the STIMULUS never asked for the depth"
               if self.peak_bus_outstanding < self.depth else
               "the traffic did reach the depth and the lite did not fill")
            + "). Raise the outstanding depth or slow the response side; do not "
            "treat this as a pass.")

    def assert_refuse_accounting(self):
        """Layer 2: every admitted command is either tracked or refused.

        Checked as an end-state identity on the ports, not per cycle: the
        occupancy port is a registered pop-count, so a command admitted on the
        cycle a slot is freed reads as "admitted while full" here yet finds
        the slot in the RTL. Once traffic has drained,
            admitted == transaction_count + refused_count + active_transactions
        must hold exactly -- a command missing from all three is one the lite
        lost and told nobody about.
        """
        assert self.tracked is not None, (
            "transaction_count port not found -- cannot close the accounting")
        tracked = int(self.tracked.value)
        live = int(self.occupancy.value)
        assert self.accepted == tracked + (self.final_refused or 0) + live, (
            f"{self.accepted} commands admitted but transaction_count={tracked} "
            f"+ refused_count={self.final_refused} + still live={live} = "
            f"{tracked + (self.final_refused or 0) + live}. "
            + ("The lite LOST commands without counting them."
               if tracked + (self.final_refused or 0) + live < self.accepted else
               "More completions/refusals than commands: a beat or response "
               "was attributed twice."))
        self.log.info(f"LiteRefuseCheck: {self.accepted} admitted = {tracked} "
                      f"completed + {self.final_refused} refused + {live} live; "
                      f"per-cycle admitted_while_full={self.admitted_while_full} "
                      f"(informational: the port count lags the allocator by a cycle)")

    def assert_no_overflow(self, depth=None):
        """Layer 3: the table never held more than its depth."""
        depth = depth or self.depth
        assert self.accepted > 0, (
            "no command handshakes observed -- the stimulus never reached the "
            "monitor, so a pass would be meaningless")
        assert self.peak_occupancy <= depth, (
            f"occupancy peaked at {self.peak_occupancy} with only {depth} "
            "entries -- the table overflowed.")

    def summary(self) -> str:
        return (f"admitted={self.accepted} peak_occupancy="
                f"{self.peak_occupancy}/{self.depth} "
                f"admitted_while_full={self.admitted_while_full} "
                f"refused_count={self.final_refused} "
                f"completed={int(self.tracked.value) if self.tracked is not None else '-'} "
                f"bus_peak_outstanding={self.peak_bus_outstanding} "
                f"full={self.full_cycles}/{self.total_cycles} cycles")
