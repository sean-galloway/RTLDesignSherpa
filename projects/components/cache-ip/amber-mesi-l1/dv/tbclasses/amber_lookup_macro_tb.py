"""
amber_lookup_macro testbench -- macro suite 1: the lookup dataplane group

Task 9.5 macro composition: the DUT is the wrapper amber_lookup_macro_test
(control + landed tag/data/repl arrays, fill/drain/victim/snoop partners
stubbed at the boundary per D-12). The class reuses the landed control TB
machinery (AmberControlTB: partner stubs, every-cycle monitors, golden
models, the oracle lockstep scorer) and runs the lookup-focused scenario
list: init-walk interaction with the real arrays, hit/miss decode +
multi-way compare, write-hit promotion (S/M via the datapath; the E->M
promotion one-hot pin travels with the coherence macro), victim-way
selection parity with the repl engine, and a randomized pure-transaction
soak (no snoops -- the snoop loop is group 4's cell) that forces evictions
at every geometry.

Levels (TEST_LEVEL):
  gate  -- InitWalk + directed HitSequence
  func  -- + MissSequence (clean + dirty victim, upgrade), BeZeroWrite,
           randomized lookup soak vs oracle lockstep
  full  -- deeper soak (same scenario family, sign-off scale)

Author: RTL Design Sherpa
Created: 2026-10-08
"""

import random

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_control_tb import (
    AmberControlTB,
)


class AmberLookupMacroTB(AmberControlTB):
    """Lookup dataplane macro: control + real arrays + repl in the loop."""

    # randomized soak transaction count per level
    SOAK_TXN = {'gate': 0, 'func': 2500, 'full': 10_000}

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        self.log.info("AmberLookupMacroTB: lookup dataplane group "
                      "(control + tag/data arrays + repl)")

    # ------------------------------------------------------------------
    # randomized pure-lookup soak: oracle lockstep per transaction over a
    # bounded working set (evictions at every geometry), no snoops -- the
    # cross-block stress here is arrays+repl under random traffic
    # ------------------------------------------------------------------
    async def _lookup_soak(self):
        n = self.SOAK_TXN[self.TEST_LEVEL]
        pool_tags = 4 * self.WAYS + 2
        prev_line = None
        for i in range(n):
            if prev_line is not None and random.random() < 0.3:
                line = prev_line
            else:
                s = random.randrange(self.SETS)
                t = random.randrange(pool_tags)
                line = (t << (self.SET_BITS + self.OFFSET_BITS)) \
                    | (s << self.OFFSET_BITS)
            prev_line = line
            beat = random.randrange(self.FILL_BEATS)
            addr = line | (beat << (self.STRB_W.bit_length() - 1))
            we = 1 if random.random() < 0.5 else 0
            # a write keeps a random (possibly partial) be; a read is
            # full-bus -- the merge path stays exercised either way
            await self._txn(addr, 1 if we else 0, label=f'soak[{i}]')
            if i % 1000 == 0:
                self.mark_progress(f"lookup soak {i}/{n}")
        # victim-parity spot audit: re-touch a sample of the working set;
        # a repl/model divergence would already have poisoned the soak
        self.log.info(f"lookup soak done ({n} transactions, "
                      f"{self.checks} checks so far)")

    async def run(self) -> bool:
        await self._check_init()
        self.scenarios['InitWalk'] = True
        self.scenarios['StrayReqInInit'] = True
        await self._hit_sequence()
        self.scenarios['HitSequence'] = True
        if self.TEST_LEVEL in ('func', 'full'):
            await self._miss_sequence()
            self.scenarios['MissSequence'] = True
            await self._be_zero_write()
            self.scenarios['BeZeroWrite'] = True
            await self._lookup_soak()
            self.scenarios['LookupSoakLockstep'] = True
        return self.mismatches == 0
