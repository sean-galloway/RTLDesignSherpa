"""GAXI Components package with value masking"""
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor

# Export these classes for convenience
__all__ = ['GAXIMaster', 'GAXISlave', 'GAXIMonitor']
