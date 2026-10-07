# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Unit tests for the BUG-019 caps-driven legal-set derivation:
#   obs_addrs.filter_legal_by_caps / mon_ctrl_arm / read_caps0  (observer side)
#   stream_monitors.filter_legal_by_build                       (build-mon side)
#   host_obs_matrix.plan_class                                  (row skip/filter)
#
# Pure logic, no UART hardware. The caps words below are REAL values measured
# on the 2026-10-03 build-obs bitstream (obs_board_2026-10-03.txt):
#   master = 0x000042CF, slave = 0x0000424F  (lite taps: no perf/debug cone,
#   err/tmo/compl/threshold built, N_ADDR_RANGES=4).
#
#   source $REPO_ROOT/env_python
#   pytest projects/fpga-systems/Genesys2/dma-ip/stream/bin/tests/test_monbus_legal_caps.py -q

import os
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

# These modules import from bin/ (and bin/TBClasses); mirror test_dump_monbus
# so the imports resolve when pytest runs from anywhere.
_repo_root = HERE.parents[5]  # repo/projects/fpga-systems/Genesys2/dma-ip/stream/bin/tests
sys.path.insert(0, str(_repo_root / "bin"))
sys.path.insert(0, str(_repo_root / "projects/components/utility-ip/converters/bin"))
sys.path.insert(0, str(HERE.parents[1] / "build-obs" / "host"))  # host_obs_matrix
os.environ.setdefault("REPO_ROOT", str(_repo_root))

import obs_addrs as obs                                  # noqa: E402
from stream_monitors import filter_legal_by_build        # noqa: E402
import host_obs_matrix as hom                              # noqa: E402

# Real caps from obs_board_2026-10-03.txt (build-obs, lite taps).
CAPS_MASTER = 0x0000_42CF   # err+tmo+compl+thr, taps, bus_meter, egress_axil, 4 ranges
CAPS_SLAVE = 0x0000_424F    # err+tmo+compl+thr, taps, egress_axil, 4 ranges
# Synthetic words for the corners the current bitstream does not exercise:
CAPS_NORANGES = 0x0000_02CF         # same cones, N_ADDR_RANGES=0
CAPS_FULL_MON = 0x0000_43CF | 0x30  # perf+debug cones built (full-monitor era)

# The obs campaign's candidate set (host_obs_campaign.LEGAL).
OBS_LEGAL = [
    (0x00, 0, 1, 0, "rd_compl"),
    (0x10, 0, 1, 0, "wr_compl"),
    (0x00, 0, 0, 0, "rd_err_slverr"),
    (0x10, 0, 0, 0, "wr_err_slverr"),
    (0x00, 0, 3, 1, "rd_timeout"),
    (0x10, 0, 3, 1, "wr_timeout"),
    (0x00, 0, 4, 7, "rd_perf"),
    (0x10, 0, 4, 7, "wr_perf"),
]


class FakeBridge:
    def __init__(self, value):
        self.value = value
        self.reads = []

    def read(self, addr):
        self.reads.append(addr)
        return self.value


# --------------------------------------------------------------------------
# obs_addrs: caps decode / filter / arm
# --------------------------------------------------------------------------

def test_read_caps0_reads_by_name():
    b = FakeBridge(CAPS_MASTER)
    assert obs.read_caps0(b) == CAPS_MASTER
    assert len(b.reads) == 1


def test_n_addr_ranges():
    assert obs.n_addr_ranges(CAPS_MASTER) == 4
    assert obs.n_addr_ranges(CAPS_NORANGES) == 0


def test_filter_lite_caps_retires_perf_only():
    kept, retired = obs.filter_legal_by_caps(OBS_LEGAL, CAPS_MASTER)
    assert [t[4] for t in kept] == ["rd_compl", "wr_compl", "rd_err_slverr",
                                    "wr_err_slverr", "rd_timeout", "wr_timeout"]
    assert [t[4] for t, _w in retired] == ["rd_perf", "wr_perf"]
    assert all("PERF_CONE" in w for _t, w in retired)


def test_filter_lite_caps_retires_debug():
    legal = OBS_LEGAL + [(0x00, 0, 0xF, 0, "rd_debug"), (0x10, 0, 0xF, 0, "wr_debug")]
    kept, retired = obs.filter_legal_by_caps(legal, CAPS_SLAVE)
    assert "rd_debug" in [t[4] for t, _w in retired]
    assert not any(t[2] == 0xF for t in kept)


def test_filter_drops_addrmatch_when_no_ranges():
    legal = [(0x00, 0, 8, 1, "rd_addrmatch")]
    kept, retired = obs.filter_legal_by_caps(legal, CAPS_NORANGES)
    assert kept == []
    assert [w for _t, w in retired] == [
        f"N_ADDR_RANGES not built (OBS_CAPS0=0x{CAPS_NORANGES:08X})"]


def test_filter_keeps_addrmatch_with_ranges():
    legal = [(0x00, 0, 8, 1, "rd_addrmatch")]
    kept, retired = obs.filter_legal_by_caps(legal, CAPS_MASTER)
    assert [t[4] for t in kept] == ["rd_addrmatch"]
    assert retired == []


def test_filter_full_monitor_keeps_everything():
    kept, retired = obs.filter_legal_by_caps(OBS_LEGAL, CAPS_FULL_MON)
    assert retired == []
    assert len(kept) == len(OBS_LEGAL)


def test_mon_ctrl_arm_matches_the_old_static_word():
    # The campaign used to hardcode 0x9F (err|tmo|compl|thr|perf|mon_en) when
    # every cone existed. arm-what-you-key must reproduce it for that set.
    all_types = [0x0, 0x1, 0x2, 0x3, 0x4]
    assert obs.mon_ctrl_arm(all_types, monitor_en=True) == 0x9F
    assert obs.mon_ctrl_arm(all_types, monitor_en=False) == 0x1F


def test_mon_ctrl_arm_derives_post_lite_word():
    # Post-lite effective set (err|tmo|compl) + MONITOR_EN == 0x87, and the
    # threshold bit that used to flood UNEXPECTED is gone.
    assert obs.mon_ctrl_arm((t[2] for t in OBS_LEGAL if obs.filter_legal_by_caps(
        [t], CAPS_MASTER)[0]), monitor_en=True) == 0x87


def test_mon_ctrl_arm_addrmatch_adds_nothing():
    # AddrMatch rides the range checker, not a cone enable.
    assert obs.mon_ctrl_arm([0x8], monitor_en=True) == 0x80


# --------------------------------------------------------------------------
# host_obs_matrix.plan_class: row skip vs reduced-set run
# --------------------------------------------------------------------------

LITE_CAPS = [CAPS_MASTER, CAPS_SLAVE]


def test_plan_class_skips_perf_row_on_lite():
    kept, reasons, skip = hom.plan_class("perf", LITE_CAPS)
    assert skip is not None and "PERF_CONE" in skip
    # the row's companion completions survive, but the row must still skip
    assert any(t[2] == 0x1 for t in kept)


def test_plan_class_skips_debug_row_on_lite():
    _kept, _reasons, skip = hom.plan_class("debug", LITE_CAPS)
    assert skip is not None and "DEBUG_CONE" in skip


def test_plan_class_addrmatch_runs_reduced_on_lite():
    kept, reasons, skip = hom.plan_class("addrmatch", LITE_CAPS)
    assert skip is None
    assert [t[4] for t in kept] == ["rd_addrmatch", "wr_addrmatch"]
    assert any("DEBUG_CONE" in w for w in reasons)


def test_plan_class_runnable_rows_untouched():
    for name in ("compl", "timeout", "threshold"):
        kept, reasons, skip = hom.plan_class(name, LITE_CAPS)
        assert skip is None, name
        assert reasons == [], name
        assert kept == list(hom.MATRIX[name][1]), name


def test_plan_class_error_row_needs_ranges():
    _kept, _reasons, skip = hom.plan_class("error", [CAPS_NORANGES, CAPS_NORANGES])
    assert skip == "address-range checker not built (N_ADDR_RANGES=0)"


def test_plan_class_stricter_observer_wins():
    # Master without the TIMEOUT cone: the timeout row must skip even though
    # the slave could emit it -- the row bins on BOTH tallies.
    master_no_tmo = CAPS_MASTER & ~obs.CAPS_TIMEOUT_CONE
    _kept, _reasons, skip = hom.plan_class("timeout", [master_no_tmo, CAPS_SLAVE])
    assert skip is not None and "TIMEOUT_CONE" in skip


# --------------------------------------------------------------------------
# stream_monitors.filter_legal_by_build: build-mon side
# --------------------------------------------------------------------------

# host_mon_coverage.STREAM_LEGAL shape.
MON_LEGAL = [
    (9, 0, 0x8, 0x01, "rd_addrmatch"),
    (10, 0, 0x8, 0x01, "wr_addrmatch"),
    (9, 0, 0x1, 0x00, "rd_completion"),
    (10, 0, 0x1, 0x00, "wr_completion"),
    (9, 0, 0x4, 0x07, "rd_perf"),
    (10, 0, 0x4, 0x07, "wr_perf"),
    (48, 4, 0x1, 0x01, "sched_desc_complete"),
    (16, 4, 0x1, 0x40, "desc_loaded"),
]


def test_build_filter_gen_mon_zero_retires_core_tuples():
    kept, retired = filter_legal_by_build(MON_LEGAL, {"gen_mon": 0})
    assert [t[4] for t in kept] == ["rd_addrmatch", "wr_addrmatch",
                                    "rd_completion", "wr_completion"]
    by_label = {t[4]: w for t, w in retired}
    assert "GEN_MON=0" in by_label["sched_desc_complete"]
    assert "perf cone not built (monlite)" in by_label["rd_perf"]


def test_build_filter_gen_mon_one_keeps_core_tuples():
    kept, retired = filter_legal_by_build(MON_LEGAL, {"gen_mon": 1})
    assert "sched_desc_complete" in [t[4] for t in kept]
    assert "desc_loaded" in [t[4] for t in kept]
    # perf is still retired: GEN_MON does not gate the monlite cones
    assert [t[4] for t, _w in retired] == ["rd_perf", "wr_perf"]


def test_build_filter_needs_no_other_build_fields():
    # build_info() returns a dozen fields; the filter must depend only on gen_mon.
    kept, _retired = filter_legal_by_build(MON_LEGAL, {"gen_mon": 0})
    assert len(kept) == 4


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
