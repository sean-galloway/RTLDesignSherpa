"""
Data models for WaveDrom generation
"""

from enum import Enum, auto
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Union

class EdgeType(Enum):
    """Types of signal edges to detect"""
    RISING = auto()
    FALLING = auto()
    BOTH = auto()
    ANY_CHANGE = auto()

class ArrowStyle(Enum):
    """WaveDrom arrow styles with visual examples"""
    STRAIGHT = "->"       # A ──→ B    Direct causation
    SPLINE = "~>"         # A ～→ B    Indirect/delayed effect
    BLOCKING = "|=>"      # A ═→ B    Blocking assignment
    NONBLOCKING = "|~>"   # A ═~→ B   Non-blocking assignment
    SETUP = "-|>"         # A ─|→ B   Setup time requirement
    HOLD = "|->"          # A |─→ B   Hold time requirement
    DOUBLE = "->>"        # A ─→→ B   Strong causation
    ASYNC = "~>>"         # A ～→→ B  Asynchronous effect
    WEAK = "-->"          # A ──→ B   Weak dependency
    BIDIRECTIONAL = "<->" # A ←─→ B   Bidirectional relationship

@dataclass
class SignalEvent:
    """Represents a signal event like edge or value change"""
    signal: str
    edge_type: EdgeType
    value: Optional[Union[int, str, dict]] = None
    cycle_offset: int = 0
    
    @staticmethod
    def state_change(signal: str, from_state: str, to_state: str):
        """Create event for state machine transition"""
        return SignalEvent(signal, EdgeType.ANY_CHANGE, {
            'from': from_state,
            'to': to_state
        })
    
    @staticmethod
    def counter_value(signal: str, value: int):
        """Create event for counter reaching specific value"""
        return SignalEvent(signal, EdgeType.ANY_CHANGE, value)
    
    @staticmethod
    def pattern_match(signal: str, pattern: dict):
        """Create event for matching a signal pattern"""
        return SignalEvent(signal, EdgeType.ANY_CHANGE, pattern)

@dataclass
class SignalRelation:
    """Defines a relationship between signal events"""
    cause: SignalEvent
    effect: SignalEvent
    min_cycles: int = 1
    max_cycles: Optional[int] = None
    style: ArrowStyle = ArrowStyle.SPLINE
    debug_info: Optional[dict] = None  # Store debugging metadata
    detected_pairs: List[tuple] = field(default_factory=list)
