"""GAXI Components package with value masking and coverage hooks"""
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.coverage_hooks import (
    GaxiCoverageHook,
    register_coverage_hooks,
    extract_gaxi_components,
    create_coverage_hook_from_env
)

# Export these classes for convenience
__all__ = [
    'GAXIMaster',
    'GAXISlave',
    'GAXIMonitor',
    'GaxiCoverageHook',
    'register_coverage_hooks',
    'extract_gaxi_components',
    'create_coverage_hook_from_env',
]
