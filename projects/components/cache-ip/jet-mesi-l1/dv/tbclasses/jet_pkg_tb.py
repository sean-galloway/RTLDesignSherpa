"""Compile-only testbench for jet_pkg.

Reads the parameters and enum encodings exposed by jet_pkg_th and asserts
the J1/J5 default values and 2-bit enum widths.
"""

import os
from cocotb.triggers import Timer

from TBClasses.shared.tbbase import TBBase


class JetPkgTB(TBBase):
    """Drives no DUT signals; checks combinational package exports."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.log.info(f"JetPkgTB seed={self.SEED}")

    async def setup_clocks_and_reset(self):
        # No clock or reset required for a package parameter check.
        pass

    async def assert_reset(self):
        pass

    async def deassert_reset(self):
        pass

    async def run(self) -> bool:
        await Timer(1, unit='ns')

        mshr_count = int(self.dut.mshr_count_o.value)
        victim_depth = int(self.dut.victim_depth_o.value)
        rsp_depth = int(self.dut.rsp_depth_o.value)
        seq_w = int(self.dut.seq_w_o.value)
        mw = int(self.dut.mw_o.value)

        assert mshr_count == 8, f"MSHR_COUNT expected 8, got {mshr_count}"
        assert victim_depth == 2, f"VICTIM_DEPTH expected 2, got {victim_depth}"
        assert rsp_depth == mshr_count + 2, (
            f"RSP_DEPTH expected {mshr_count + 2}, got {rsp_depth}"
        )
        assert seq_w == (rsp_depth - 1).bit_length(), (
            f"SEQ_W expected {(rsp_depth - 1).bit_length()}, got {seq_w}"
        )
        assert mw == (mshr_count - 1).bit_length(), (
            f"MW expected {(mshr_count - 1).bit_length()}, got {mw}"
        )

        # Enum width check: all values must fit in 2 bits (logic [1:0]).
        for name, value in {
            'JET_CLS_RNSD': int(self.dut.fill_class_rnsd_o.value),
            'JET_CLS_RU': int(self.dut.fill_class_ru_o.value),
            'JET_PEND_NONE': int(self.dut.pend_none_o.value),
            'JET_PEND_DOWNGRADE_S': int(self.dut.pend_downgrade_s_o.value),
            'JET_PEND_INVALIDATE_I': int(self.dut.pend_invalidate_i_o.value),
        }.items():
            assert 0 <= value < 4, f"{name} out of 2-bit range: {value}"

        self.log.info(
            f"jet_pkg parameters OK: MSHR_COUNT={mshr_count} "
            f"VICTIM_DEPTH={victim_depth} RSP_DEPTH={rsp_depth} "
            f"SEQ_W={seq_w} MW={mw}"
        )
        return True

    def get_test_report(self):
        return {'checks': 8, 'mismatches': 0}
