# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""andesite DRAM operating points: JEDEC nanoseconds -> programmed register values.

One place where a timing set is DERIVED rather than typed, because the
alternative has already cost this family real debugging: pumice's scheduler TB
once clocked at 100 MHz and programmed `t_rcd=3 t_rp=3 t_ras=5 t_rc=8 t_faw=6`
-- a set belonging to no part at no frequency -- and a root-cause writeup was
published against it claiming the board. The mechanism held anyway, but the
claim was false and had to be corrected.

So every number below comes out of two inputs and nothing else: the datasheet
nanoseconds, and the MC clock period. Both are quoted from the HAS design point
(Chapter 2.4), which is the authority for what andesite is built to run on.

THREE QUANTITIES, and keeping them apart is the point
----------------------------------------------------
`ns`        the JEDEC/datasheet figure.
`spacing`   that figure in MC cycles, `ceil(ns / mc_ns)` -- the number of
            cycles that must separate the two commands.
`prog`      what goes in the CSR, which is `spacing - 1`.

That last step is not cosmetic. andesite_csr.rdl states the convention -- "MC
cycles to block; spacing enforced is N+1" -- and it is MEASURED in
dv/tests/fub/test_andesite_bank_timer.py (ACT->RD gap is t_rcd+1) and
test_andesite_global_timers.py (a window programmed to N is ready at index N).
Programming the datasheet cycle count directly would over-space every window by
one cycle; subtracting one twice would violate the part. A test that wants to
assert a spacing asks for `spacing`; a test that wants to drive a port asks for
`prog`.

tREFI is the exception and is marked as such: it is a DEADLINE, not a minimum,
so it floors instead of ceiling and is not off-by-one adjusted.
"""

from math import ceil, floor

# ---------------------------------------------------------------------------
# The Genesys 2 design point, HAS Chapter 2.4.
#
#   2x MT41J256M16 (DDR3-800), 32-bit bus, 8 banks, row 15 / col 10
#   sys (MC) clock 100 MHz  -> 10.0 ns per MC cycle
#   DRAM clock     400 MHz  -> 2.5 ns per CK, i.e. DFI_RATE = 4
#
# Values in nanoseconds, exactly as the HAS table gives them. Where JEDEC
# specifies max(n nCK, t ns) the resolved figure is shown with its workings,
# because at CK = 2.5 ns the nCK term wins for tRRD and tWTR and the ns term
# would silently under-space.
# ---------------------------------------------------------------------------
GENESYS2_DDR3_800 = {
    'name':    'genesys2_ddr3_800',
    'mc_ns':   10.0,      # 100 MHz sys
    'ck_ns':   2.5,       # 400 MHz DRAM clock
    'dfi_rate': 4,
    'dram_bl': 8,         # BL8
    'num_banks': 8,
    'row_width': 15,
    'col_width': 10,
    'ns': {
        'tRCD': 13.1,
        'tRP':  13.1,
        'tWR':  13.1,
        'tRAS': 37.5,
        'tRC':  37.5 + 13.1,          # tRAS + tRP
        'tRFC': 139.0,
        'tFAW': 50.0,
        'tRRD': max(6 * 2.5, 10.0),   # max(6 nCK, 10 ns) -> 15.0, nCK wins
        'tWTR': max(4 * 2.5, 7.5),    # max(4 nCK, 7.5 ns) -> 10.0, nCK wins
        'tRTP': max(4 * 2.5, 7.5),    # DDR3 tRTP, same shape -> 10.0
        'tCCD': 4 * 2.5,              # 4 nCK = one BL8 burst on the DQ bus
    },
    # A deadline, not a minimum: floor, and no N+1 adjustment.
    'tREFI_ns': 7812.5,               # 64 ms / 8192
}


def _spacing(ns, mc_ns):
    """Datasheet ns -> MC cycles of required command spacing (at least 1)."""
    return max(1, int(ceil(ns / mc_ns)))


def dram_config(point=None):
    """Return (spacing, prog, meta) for a named operating point.

    `spacing[k]` is the required separation in MC cycles; `prog[k]` is what to
    write to the CSR (spacing - 1, the N+1 convention); `meta` carries the
    clock, geometry and the point's name so a result can say what it measured.
    """
    cfg = GENESYS2_DDR3_800 if point in (None, 'genesys2_ddr3_800') else None
    if cfg is None:
        raise ValueError(
            f"unknown operating point {point!r}; andesite has exactly one today "
            f"({GENESYS2_DDR3_800['name']}, HAS Chapter 2.4). Add it here with "
            f"its datasheet nanoseconds rather than typing cycle counts into a "
            f"test.")

    mc = cfg['mc_ns']
    spacing = {k: _spacing(v, mc) for k, v in cfg['ns'].items()}
    prog = {k: v - 1 for k, v in spacing.items()}

    # tREFI: a deadline. Floor it, and do not apply the N+1 adjustment -- the
    # refresh engine counts down to a due time rather than blocking a command.
    spacing['tREFI'] = max(1, int(floor(cfg['tREFI_ns'] / mc)))
    prog['tREFI'] = spacing['tREFI']

    meta = {k: cfg[k] for k in ('name', 'mc_ns', 'ck_ns', 'dfi_rate',
                                'dram_bl', 'num_banks', 'row_width',
                                'col_width')}
    meta['ns'] = dict(cfg['ns'])
    meta['tREFI_ns'] = cfg['tREFI_ns']
    return spacing, prog, meta


def describe(point=None):
    """One-line-per-timing table, for a test to log beside its result.

    A passing sim has to be able to prove which config it ran
    (feedback_sim_config_must_be_provable), and "the defaults" is not an
    answer when the defaults are what a bug hides behind.
    """
    spacing, prog, meta = dram_config(point)
    out = [f"operating point {meta['name']}: MC {meta['mc_ns']} ns "
           f"({1000.0 / meta['mc_ns']:.0f} MHz), CK {meta['ck_ns']} ns, "
           f"DFI_RATE {meta['dfi_rate']}, BL{meta['dram_bl']}, "
           f"{meta['num_banks']} banks, row {meta['row_width']} / "
           f"col {meta['col_width']}",
           f"{'timing':8s} {'ns':>8s} {'spacing':>8s} {'programmed':>11s}"]
    for k in meta['ns']:
        out.append(f"{k:8s} {meta['ns'][k]:8.1f} {spacing[k]:8d} "
                   f"{prog[k]:11d}")
    out.append(f"{'tREFI':8s} {meta['tREFI_ns']:8.1f} {spacing['tREFI']:8d} "
               f"{prog['tREFI']:11d}   (deadline: floored, no N+1)")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# The same table, expressed for the DV framework's DFI slave model.
# ---------------------------------------------------------------------------
# `JedecTimings` counts in DRAM CLOCK cycles (tCK), a third unit alongside the
# ns and MC-cycle views above -- so this hands the framework NANOSECONDS and
# lets it do the conversion, rather than adding a conversion of mine for the
# same numbers.
#
# The framework vendors ddr3-1333/1600/1866 but NOT ddr3-800, and its loader
# says why: profiles are vendored "only where a public JEDEC speed bin fixes
# the numbers", otherwise build them with timings_from_params(). So that is
# what this does, from the HAS design point.


def jedec_ns(point=None, *, cl=6, cwl=5):
    """kwargs for `timings_from_params()`: the HAS ns table, in NANOSECONDS.

    Passing nanoseconds rather than a cycle count I computed myself is
    deliberate. The framework requires an explicit unit suffix on every value
    (`_ns` or `_ck`, and it raises listing the offenders if you leave it off),
    and it applies "exactly the same conversion the CSV loader does". So the
    ns -> CK step happens once, in the framework, from the datasheet figure --
    there is no second conversion of mine to disagree with it.

    That leaves exactly one table (`['ns']` above) with two consumers:

        the CONTROLLER's CSRs       <- prog[]    (MC cycles, spacing - 1)
        the DFI SLAVE's JEDEC model <- jedec_ns() (ns, converted by the
                                                   framework to CK cycles)

    If those ever came from different tables the slave would police a part the
    controller was not programmed for, and the disagreement would read as an
    RTL bug.

    CL and CWL default to the DDR3-800 bin: CL 6, and CWL 5 for a 400 MHz
    clock per JESD79-3F's CWL table. They are arguments rather than constants
    because MR0/MR2 are runtime values -- a test that programs a different CL
    must pass the same number here, or the slave models a different part.
    """
    _, _, meta = dram_config(point)
    n = meta['ns']
    return dict(
        tCK_ns=meta['ck_ns'],
        tRCD_ns=n['tRCD'],
        tRP_ns=n['tRP'],
        tRAS_min_ns=n['tRAS'],
        tRC_ns=n['tRC'],
        tWR_ns=n['tWR'],
        tWTR_ns=n['tWTR'],
        tRTP_ns=n['tRTP'],
        tRRD_ns=n['tRRD'],
        tFAW_ns=n['tFAW'],
        tREFI_ns=meta['tREFI_ns'],
        tRFC_ns=n['tRFC'],
        CL=cl,
        CWL=cwl,
        BL=meta['dram_bl'],
    )


if __name__ == "__main__":
    print(describe())
    print()
    print("DFI-slave view (ns in, the framework converts to CK):")
    for k, v in jedec_ns().items():
        print(f"  {k:14s} {v}")
