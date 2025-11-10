#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Bridge Components - Type-safe sub-module generators

from .arbiter_component import ArbiterComponent
from .address_decode_component import AddressDecodeComponent
from .channel_mux_component import ChannelMuxComponent
from .master_width_adapter import MasterWidthAdapter
from .slave_width_adapter import SlaveWidthAdapter
from .apb_shim_adapter import ApbShimAdapter

__all__ = ['ArbiterComponent', 'AddressDecodeComponent', 'ChannelMuxComponent', 'MasterWidthAdapter', 'SlaveWidthAdapter', 'ApbShimAdapter']
