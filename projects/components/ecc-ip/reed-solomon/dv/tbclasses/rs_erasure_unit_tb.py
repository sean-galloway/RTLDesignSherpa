"""
rs_erasure_unit testbench

The unit stands alone: the TB plays the decoder core. Beats with erasure
flags go in the A side, the packed record is captured from o_ab and looped
back into i_ab (held stable through TRANS, which is the core's descriptor's
job in the real system -- the pop hazard is the core test's cover), model
syndromes are driven on i_synd, and every output is checked against
rs_model's erasure intermediates: f and f_over, the t_zero flag, the solver
window (riBM's drop-f crossbar, Euclid's zeroed-low window), and -- after a
COMB over the model solver's Lambda_e -- the combined locator, evaluator
and degree. t_zero blocks skip COMB: the registers already hold Gamma and
GS and are checked directly after TRANS.

Author: RTL Design Sherpa
Created: 2026-10-02
"""

import os
import random

from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase

from projects.components.ecc_ip.reed_solomon.dv.tbclasses.rs_model import RSModel


class RSErasureUnitTB(TBBase):
    CELLS = {'gate': 5, 'func': 9, 'full': 12}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.CELLS:
            self.TEST_LEVEL = 'gate'
        random.seed(self.SEED)
        self.M = int(dut.SYMBOL_WIDTH.value)
        self.PRIM = int(dut.PRIM_POLY.value)
        self.T = int(dut.T_SYMBOLS.value)
        self.N = int(dut.N_SYMBOLS.value)
        self.B = 0
        self.K = self.N - 2 * self.T
        self.S = int(dut.SYMBOLS_PER_BEAT.value)
        self.DEG_W = (2 * self.T).bit_length()   # clog2(2t+1)
        # the DUT's KES_ALGO is a string parameter cocotb cannot read back
        self.KES = os.environ.get('KES_ALGO', 'RIBM').lower()
        self.Q = 1 << self.M
        self.model = RSModel(self.M, self.PRIM, self.T, self.N, self.B)
        self.checks = 0
        self.mismatches = 0
        self.log.info(f"RSErasureUnitTB RS({self.N},{self.K}) t={self.T} m={self.M} "
                      f"prim=0x{self.PRIM:X} kes={self.KES} S={self.S} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        self.rst_n.value = 0
        self.dut.i_rx_fire.value = 0
        self.dut.i_rx_first.value = 0
        self.dut.i_rx_count.value = 0
        self.dut.i_rx_erasure.value = 0
        self.dut.i_ab.value = 0
        self.dut.i_synd.value = 0
        self.dut.i_trans_start.value = 0
        self.dut.i_comb_start.value = 0
        self.dut.i_lambda_e.value = 0
        self.dut.i_deg_e.value = 0
        await self.wait_clocks(self.clk_name, 5)
        self.rst_n.value = 1
        await self.wait_clocks(self.clk_name, 2)

    # -- stimulus --------------------------------------------------------------
    def make_block(self, errors, erasures, corrupt_erasures=True,
                   last_beat_flags=False):
        """(rx, flags): a codeword with `errors` symbol errors and `erasures`
        flagged positions. last_beat_flags forces the flags into the FINAL
        beat (two lanes of it when S > 1): the record must still be complete
        on the block-end edge (the next-value pack)."""
        data = [random.randrange(self.Q) for _ in range(self.K)]
        rx = self.model.encode(data)
        flags = [0] * self.N
        if last_beat_flags and erasures:
            err_pos = random.sample(range(self.N), errors)
            n_flag = min(erasures, self.S if self.S > 1 else 1)
            base = self.N - n_flag
            era_pos = list(range(base, base + n_flag))
            era_pos += random.sample([p for p in range(self.N)
                                      if p not in err_pos and p not in era_pos],
                                     erasures - n_flag)
        else:
            pos = random.sample(range(self.N), errors + erasures)
            err_pos, era_pos = pos[:errors], pos[errors:]
        for p in err_pos:
            rx[p] ^= random.randrange(1, self.Q)
        for p in era_pos:
            flags[p] = 1
            if corrupt_erasures:
                rx[p] ^= random.randrange(1, self.Q)
        return rx, flags

    def pack(self, coeffs):
        v = 0
        for i, c in enumerate(coeffs):
            v |= c << (i * self.M)
        return v

    def unpack(self, value, n_coeffs):
        return [(value >> (i * self.M)) & (self.Q - 1) for i in range(n_coeffs)]

    # -- one block -------------------------------------------------------------
    async def run_block(self, label, rx, flags):
        t2 = 2 * self.T
        er = [i for i, f in enumerate(flags) if f]
        f = len(er)
        syn = self.model.syndromes(rx)
        gamma = self.model.erasure_locator(er)
        gs = self.model.poly_mul_mod(gamma, syn, t2)
        twin = gs[f:]
        t_zero = bool(er) and not any(twin)
        f_over = f > t2

        # A side: the block's beats with their flags
        for b in range(0, self.N, self.S):
            lanes = min(self.S, self.N - b)
            er_bits = 0
            for u in range(lanes):
                if flags[b + u]:
                    er_bits |= 1 << u
            self.dut.i_rx_erasure.value = er_bits
            self.dut.i_rx_count.value = lanes
            self.dut.i_rx_first.value = 1 if b == 0 else 0
            self.dut.i_rx_fire.value = 1
            await RisingEdge(self.clk)
        self.dut.i_rx_fire.value = 0
        self.dut.i_rx_first.value = 0
        self.dut.i_rx_erasure.value = 0
        await RisingEdge(self.clk)

        # loop the record back, held stable (the core's descriptor's role)
        record = int(self.dut.o_ab.value)
        self.dut.i_ab.value = record
        self.dut.i_synd.value = self.pack(syn)

        rec_f = (record >> ((t2 + 1) * self.M)) & ((1 << self.DEG_W) - 1)
        rec_over = (record >> ((t2 + 1) * self.M + self.DEG_W)) & 1
        self.check(f"{label}: record f={rec_f} vs {min(f, t2 + 1)}",
                   rec_f == min(f, t2 + 1))
        self.check(f"{label}: record over={rec_over} vs {int(f_over)}",
                   rec_over == int(f_over))
        if f_over:
            # the core never starts TRANS on f_over; the record check is the cell
            self.dut.i_ab.value = 0
            return

        # TRANS
        self.dut.i_trans_start.value = 1
        await RisingEdge(self.clk)
        self.dut.i_trans_start.value = 0
        done = False
        for _ in range(t2 + 20):
            await RisingEdge(self.clk)
            if int(self.dut.o_trans_done.value) == 1:
                done = True
                break
        self.check(f"{label}: trans_done", done)

        self.check(f"{label}: o_f", int(self.dut.o_f.value) == f)
        self.check(f"{label}: t_zero={int(self.dut.o_t_zero.value)} vs {int(t_zero)}",
                   int(self.dut.o_t_zero.value) == int(t_zero))

        # the solver window
        if self.KES == 'euclid':
            exp_window = [0] * f + twin
        else:
            exp_window = twin + [0] * f
        got_window = self.unpack(int(self.dut.o_kes_synd.value), t2)
        self.check(f"{label}: kes window", got_window == exp_window)

        if t_zero:
            got_lam = self.unpack(int(self.dut.o_lambda_c.value), t2 + 1)
            got_om = self.unpack(int(self.dut.o_omega_c.value), t2)
            self.check(f"{label}: t_zero lambda_c == Gamma", got_lam == gamma)
            self.check(f"{label}: t_zero omega_c == GS", got_om == gs)
            self.check(f"{label}: t_zero deg_c", int(self.dut.o_deg_c.value) == f)
        else:
            if self.KES == 'euclid':
                lam_e, _, _ = self.model.euclid(exp_window, erasure_count=f)
            else:
                lam_e, _ = self.model.ribm(exp_window, erasure_count=f)
            deg_e = self.model.degree(lam_e)
            lam = self.model.poly_mul_mod(gamma, lam_e[:self.T + 1], t2 + 1)
            omega = self.model.poly_mul_mod(lam, syn, t2)
            self.dut.i_lambda_e.value = self.pack(lam_e)
            self.dut.i_deg_e.value = deg_e
            self.dut.i_comb_start.value = 1
            await RisingEdge(self.clk)
            self.dut.i_comb_start.value = 0
            done = False
            for _ in range(self.T + 20):
                await RisingEdge(self.clk)
                if int(self.dut.o_comb_done.value) == 1:
                    done = True
                    break
            self.check(f"{label}: comb_done", done)
            got_lam = self.unpack(int(self.dut.o_lambda_c.value), t2 + 1)
            got_om = self.unpack(int(self.dut.o_omega_c.value), t2)
            self.check(f"{label}: lambda_c == Gamma*Lambda_e", got_lam == lam)
            self.check(f"{label}: omega_c == combined evaluator", got_om == omega)
            self.check(f"{label}: deg_c={int(self.dut.o_deg_c.value)} vs {deg_e + f}",
                       int(self.dut.o_deg_c.value) == deg_e + f)
        self.dut.i_ab.value = 0
        self.dut.i_synd.value = 0

    def check(self, label, ok):
        self.checks += 1
        if not ok:
            self.mismatches += 1
            if self.mismatches < 15:
                self.log.error(f"MISMATCH {label}")
        return ok

    # -- cells -----------------------------------------------------------------
    def cells(self):
        """(label, errors, erasures, last_beat_flags) at and past the
        2e + f = 2t bound, f-only (t_zero), f = 0, f_over, and flags forced
        into the last beat."""
        t, t2 = self.T, 2 * self.T
        c = [("f=0, 1 error", 1, 0, False),
             ("f=1", 0, 1, False),
             ("f=t", 0, t, False),
             ("f=2t (t_zero)", 0, t2, False),
             ("f=2t, last-beat flags", 0, t2, True),
             ("boundary 1e+2t-2", 1, t2 - 2, False),
             ("boundary 2e+2t-4", 2, t2 - 4, False),
             ("boundary t/2e+t", max(1, t // 2), t2 - 2 * max(1, t // 2), False),
             ("past bound 1e+2t", 1, t2, False),
             ("t-1e+2", max(1, t - 1), 2, False),
             ("mixed, last-beat flags", 1, min(t, 4), True),
             ("f_over 2t+1", 0, t2 + 1, False)]
        return c[:self.CELLS[self.TEST_LEVEL]]

    async def run_cells(self):
        for label, e, f, lbf in self.cells():
            rx, flags = self.make_block(e, f, last_beat_flags=lbf)
            await self.run_block(label, rx, flags)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
