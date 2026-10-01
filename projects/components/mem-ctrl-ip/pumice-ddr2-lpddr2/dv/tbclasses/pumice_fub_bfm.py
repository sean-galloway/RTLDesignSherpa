# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: pumice_fub_bfm
# Purpose: compatibility shim. The implementation moved to the shared
#          framework as `TBClasses.fub_bfm` on 2026-09-30, when scoria's
#          arbiter TB needed the same helpers and a second copy would have
#          started drifting immediately.
#
# Nothing in the module was pumice-specific. This shim exists so pumice's 16
# import sites keep resolving; new TBs should import TBClasses.fub_bfm directly.

"""Deprecated alias for `TBClasses.fub_bfm`. See that module for the docs."""

from TBClasses.fub_bfm import (  # noqa: F401
    DEFAULT_PROFILE,
    fub_consumer,
    fub_producer,
    fub_pulse_producer,
    make_field_config,
    set_profile,
)

__all__ = [
    "DEFAULT_PROFILE",
    "fub_consumer",
    "fub_producer",
    "fub_pulse_producer",
    "make_field_config",
    "set_profile",
]
