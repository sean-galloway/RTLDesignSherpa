# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""pumice init sequence -- bring the DDR2 controller up and level the read path.

Every pumice test sequence declares `requires = ("init",)`, so this runs first
or the runner refuses the plan outright. It touches registers only through
`ctx.bus` (a `DDR2CharDriver`), never a port, so the identical sequence runs
against the board and against the cocotb DFI-model sim.
"""

from __future__ import annotations

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

from pumice_master import SimpleTest


class Init(Sequence):
    name = "init"
    description = "soft reset, controller cfg, geometry, read-path leveling"

    def run(self, ctx):
        drv = ctx.bus

        build = drv.build_id()
        if build != drv.BUILD_ID_MAGIC:
            raise RuntimeError(
                f"wrong bitstream: BUILD_ID 0x{build:08X} != "
                f"0x{drv.BUILD_ID_MAGIC:08X} -- reprogram the board")

        # Say what we are actually talking to. BUILD_ID only proves the family;
        # the geometry below is what every later step depends on, and it used to
        # be assumed rather than read. Logged unconditionally so a failing run
        # records the configuration it failed under.
        ctx.say(f"[init] board: {drv.describe_build()}")

        # An expectation is optional -- but when the caller states one, a
        # mismatch is a hard stop. Continuing would characterize a build nobody
        # meant to measure, and the numbers would look plausible.
        expect = ctx.param("expect_build")
        if expect is not None:
            actual = drv.build_info()
            wrong = {k: (v, actual[k]) for k, v in expect.items()
                     if k in actual and actual[k] != v}
            if wrong:
                detail = ", ".join(f"{k}: want {w}, board has {g}"
                                   for k, (w, g) in sorted(wrong.items()))
                raise RuntimeError(f"bitstream does not match expectation -- {detail}")

        # DFI timing is a property of the PHY underneath, not of the sequence.
        # Exposed as params rather than hardcoded so the SAME sequence can be
        # pointed at a different backend -- an unconfigurable sequence is one
        # that only runs where its author happened to be standing.
        #
        # The param that currently earns this is `leveling`: against the cocotb
        # DFI loopback it never converges, so the sim run hangs unless it is
        # turned off. The timing values below are passed through for the same
        # reason in principle, but no measurement yet shows the loopback caring
        # what they are -- do not read the plumbing as evidence that it does.
        test = SimpleTest(
            drv,
            base_addr=ctx.param("base_addr", 0x0),
            level_cache=ctx.param("level_cache"),
            **{k: ctx.param(k) for k in
               ("t_phy_wrlat", "t_rddata_en", "rddata_delay", "rd_phase")
               if ctx.param(k) is not None},
        )
        test.init(do_leveling=ctx.param("leveling", True))

        level = test.level
        if level is not None and not level.ok:
            # Not fatal on its own -- a marginal eye still runs, and the test
            # sequences are the honest verdict. Surface it so a later failure
            # is not mistaken for a controller bug.
            ctx.say(f"[init] WARNING: leveling not clean: {level.notes}")

        # The SimpleTest instance carries the leveled state the test sequences
        # need. Passing it through the result dict is how one sequence hands
        # work to the next without either importing the other.
        return {
            "test": test,
            "levelled": bool(level.ok) if level is not None else None,
            "bitslip": getattr(level, "bitslip", None),
            "rd_tap": getattr(level, "rd_tap", None),
            "rd_window": getattr(level, "rd_window", None),
        }
