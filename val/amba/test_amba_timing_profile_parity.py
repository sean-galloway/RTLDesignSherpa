# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_amba_timing_profile_parity
# Purpose: The framework's canonical profiles match AXI_RANDOMIZER_CONFIGS
#
# Subsystem: amba

"""The AMBA timing profiles are defined twice; this proves they agree.

``AXI_RANDOMIZER_CONFIGS`` lives in ``bin/TBClasses/amba/amba_random_configs.py``
and the framework's copy lives in
``CocoTBFramework.components.shared.amba_timing_profiles``. They are duplicated
deliberately: TBClasses DEPENDS on the framework, so the framework importing
TBClasses would invert the dependency and make it unusable standalone.

Duplication without a check is how two definitions drift until 'burst_pause'
means different things depending on which import a testbench reached for. This
file is the check, and it lives HERE because the main repo is the only place
both are importable.

If this fails, one of the two was edited and the other was not. Fix the
framework copy to match ``AXI_RANDOMIZER_CONFIGS`` -- that table is what the
existing testbenches already select from, so it is the authority.
"""
import pytest

from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from CocoTBFramework.components.shared.amba_timing_profiles import (
    AMBA_CHANNELS,
    CANONICAL_PROFILES,
    canonical_names,
)

FAMILIES = ('axi4', 'axi5', 'axil4', 'axil5')


def _family(fam):
    mod = __import__(
        f'CocoTBFramework.components.{fam}.{fam}_timing_config', fromlist=['x'])
    return (getattr(mod, f'get_{fam}_timing_profiles'),
            getattr(mod, f'create_{fam}_timing_from_profile'))


def test_the_two_definitions_name_the_same_profiles():
    assert set(canonical_names()) == set(AXI_RANDOMIZER_CONFIGS)


@pytest.mark.parametrize("profile", sorted(AXI_RANDOMIZER_CONFIGS))
def test_the_two_definitions_carry_the_same_delays(profile):
    amba = AXI_RANDOMIZER_CONFIGS[profile]
    valid, ready = CANONICAL_PROFILES[profile]
    assert valid == amba['master']['valid_delay'], f"{profile} master valid_delay"
    assert ready == amba['slave']['ready_delay'], f"{profile} slave ready_delay"


@pytest.mark.parametrize("fam", FAMILIES)
@pytest.mark.parametrize("profile", sorted(AXI_RANDOMIZER_CONFIGS))
def test_every_family_offers_every_canonical_profile(fam, profile):
    """A profile missing from one family is invisible until a testbench moves
    between families and finds its profile silently replaced by the default."""
    get_profiles, _ = _family(fam)
    assert f'{fam}_{profile}' in get_profiles()


@pytest.mark.parametrize("fam", FAMILIES)
@pytest.mark.parametrize("profile", sorted(AXI_RANDOMIZER_CONFIGS))
def test_every_family_applies_the_canonical_delays_to_all_five_channels(fam, profile):
    """The role-keyed AMBA table expands to per-channel constraints.

    Covering only some channels is not a smaller profile, it is a profile that
    leaves the rest running flat out -- which is what axi4_timing_config's own
    read-only profiles did before the canonical set landed.
    """
    _, create = _family(fam)
    constraints = create(profile)['constraints']
    amba = AXI_RANDOMIZER_CONFIGS[profile]
    for ch in AMBA_CHANNELS:
        assert constraints[f'{ch}_valid_delay'] == amba['master']['valid_delay']
        assert constraints[f'{ch}_ready_delay'] == amba['slave']['ready_delay']


@pytest.mark.parametrize("fam", FAMILIES)
@pytest.mark.parametrize("profile", sorted(AXI_RANDOMIZER_CONFIGS))
def test_bare_and_prefixed_names_agree(fam, profile):
    """'burst_pause' and 'axi4_burst_pause' must be the same profile, so a
    testbench selecting by the AMBA name it has always used keeps working."""
    _, create = _family(fam)
    assert create(profile)['constraints'] == create(f'{fam}_{profile}')['constraints']


@pytest.mark.parametrize("fam", FAMILIES)
def test_family_specific_profiles_survive(fam):
    """The canonical set must not have swallowed a family's own profiles."""
    get_profiles, _ = _family(fam)
    assert f'{fam}_normal' in get_profiles()
