"""
RAPIDS Components Package

This package contains reusable BFM (Bus Functional Model) components
for RAPIDS (Rapid AXI Programmable In-band Descriptor System) testing.

Components:
- DataMoverBFM: Data engine/DMA simulator for descriptor processing
"""

from .data_mover_bfm import DataMoverBFM

__all__ = ['DataMoverBFM']
