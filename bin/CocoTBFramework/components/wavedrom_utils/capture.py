"""
WaveDrom capture utilities for CocoTB simulations

This module provides utilities for capturing waveform data during CocoTB simulations
and efficiently managing the capture process.
"""

import asyncio
from typing import Dict, List, Optional, Callable, Any, Awaitable, Set
from dataclasses import dataclass, field
from enum import Enum
import time

from cocotb.triggers import RisingEdge, FallingEdge, Timer
import cocotb

from .models import SignalEvent, EdgeType
from .generator import WaveDromGenerator
from .container import ScenarioConfig, WaveformContainer


@dataclass
class CaptureConfig:
    """Configuration for waveform capture process"""
    sample_interval_ns: int = 0  # 0 = Every clock cycle
    max_execution_time_s: int = 0  # 0 = No limit
    max_cycles: int = 0  # 0 = No limit
    periodic_checks_interval: int = 50  # Run checks every N cycles
    enable_statistics: bool = True
    periodic_save: bool = False
    save_interval_cycles: int = 1000
    output_format: str = "json"  # "json" or "html"
    debug_level: int = 1  # 0=None, 1=Basic, 2=Detailed, 3=Verbose


class CaptureMode(Enum):
    """Capture modes for waveform data"""
    CONTINUOUS = 1  # Capture continuously until stopped
    TIME_WINDOW = 2  # Capture for a specific time window
    TRIGGER_BASED = 3  # Capture based on trigger conditions
    SCENARIO_BASED = 4  # Capture based on verification scenarios


class WaveformCapture:
    """
    Manages waveform capture during CocoTB simulations
    
    This class provides the ability to capture waveforms in different modes,
    with automatic pausing and resuming, and efficient resource management.
    """
    
    def __init__(self, dut, container: WaveformContainer, config: CaptureConfig = None):
        """
        Initialize the waveform capture
        
        Args:
            dut: Device under test
            container: WaveformContainer instance
            config: Optional capture configuration
        """
        self.dut = dut
        self.container = container
        self.config = config or CaptureConfig()
        self.wave_gen = container.wave_gen
        self.done = False
        self.paused = False
        self.capture_task = None
        self.start_time = None
        self.last_sample_time = None
        self.last_check_cycle = 0
        self.last_save_cycle = 0
        self.trigger_conditions = []
        self.events_detected = set()
        self.cycles_captured = 0
        self._lock = asyncio.Lock()
    
    async def start_capture(self, mode: CaptureMode = CaptureMode.CONTINUOUS, 
                          duration_ns: int = None, trigger: SignalEvent = None):
        """
        Start waveform capture with the specified mode
        
        Args:
            mode: Capture mode
            duration_ns: Duration for TIME_WINDOW mode
            trigger: Trigger event for TRIGGER_BASED mode
        """
        self.done = False
        self.paused = False
        self.start_time = time.time()
        self.last_sample_time = self.start_time
        
        # Configure capture based on mode
        if mode == CaptureMode.TRIGGER_BASED and trigger:
            self.trigger_conditions.append(trigger)
            
        # Start the capture task
        if mode == CaptureMode.SCENARIO_BASED:
            self.capture_task = cocotb.start_soon(self.run_scenario_capture())
        else:
            self.capture_task = cocotb.start_soon(self.run_continuous_capture(duration_ns))
    
    async def stop_capture(self):
        """Stop the capture process"""
        self.done = True
        if self.capture_task:
            await self.capture_task
    
    async def pause_capture(self):
        """Pause the capture process"""
        self.paused = True
    
    async def resume_capture(self):
        """Resume the capture process"""
        self.paused = False
    
    async def run_continuous_capture(self, duration_ns: Optional[int] = None):
        """
        Run continuous waveform capture
        
        Args:
            duration_ns: Optional duration in nanoseconds
        """
        try:
            start_sim_time = cocotb.utils.get_sim_time(units='ns')
            
            while not self.done:
                if self.paused:
                    await Timer(10, units='ns')
                    continue
                
                # Sample waveform
                await self.wave_gen.sample()
                self.cycles_captured += 1
                
                # Check for additional interval between samples if configured
                if self.config.sample_interval_ns > 0:
                    await Timer(self.config.sample_interval_ns, units='ns')
                
                # Run periodic checks
                if (self.cycles_captured - self.last_check_cycle) >= self.config.periodic_checks_interval:
                    await self._run_periodic_checks()
                    self.last_check_cycle = self.cycles_captured
                
                # Check for periodic save
                if self.config.periodic_save and (self.cycles_captured - self.last_save_cycle) >= self.config.save_interval_cycles:
                    self._periodic_save()
                    self.last_save_cycle = self.cycles_captured
                
                # Check time-based termination conditions
                current_time = time.time()
                execution_time = current_time - self.start_time
                
                # Check max execution time
                if self.config.max_execution_time_s > 0 and execution_time > self.config.max_execution_time_s:
                    if self.config.debug_level >= 1:
                        print(f"WaveDrom capture stopped: Max execution time reached ({self.config.max_execution_time_s}s)")
                    self.done = True
                    break
                
                # Check max cycles
                if self.config.max_cycles > 0 and self.cycles_captured >= self.config.max_cycles:
                    if self.config.debug_level >= 1:
                        print(f"WaveDrom capture stopped: Max cycles reached ({self.config.max_cycles})")
                    self.done = True
                    break
                
                # Check duration for TIME_WINDOW mode
                if duration_ns:
                    current_sim_time = cocotb.utils.get_sim_time(units='ns')
                    if (current_sim_time - start_sim_time) >= duration_ns:
                        if self.config.debug_level >= 1:
                            print(f"WaveDrom capture stopped: Duration reached ({duration_ns}ns)")
                        self.done = True
                        break
        
        except Exception as e:
            if self.config.debug_level >= 1:
                print(f"Error in WaveDrom capture: {e}")
            import traceback
            print(traceback.format_exc())
        finally:
            if self.config.debug_level >= 1:
                print(f"WaveDrom capture completed: {self.cycles_captured} cycles captured")
    
    async def run_scenario_capture(self):
        """Run capture based on verification scenarios in the container"""
        try:
            # Run all scenarios in the container
            await self.container.run_all_scenarios(self.dut)
        except Exception as e:
            if self.config.debug_level >= 1:
                print(f"Error running scenarios: {e}")
            import traceback
            print(traceback.format_exc())
        finally:
            self.done = True
    
    async def _run_periodic_checks(self):
        """Run periodic checks on captured data"""
        # Check for trigger conditions
        for trigger in self.trigger_conditions:
            # Look for the trigger event in recent history
            for cycle, signal, value, edge_type in self.wave_gen.event_history[-100:]:
                if (signal == trigger.signal and 
                    edge_type == trigger.edge_type and 
                    (trigger.value is None or value == trigger.value)):
                    
                    trigger_id = f"{trigger.signal}_{trigger.edge_type}_{cycle}"
                    if trigger_id not in self.events_detected:
                        self.wave_gen.add_debug_point(
                            cycle,
                            f"Trigger detected: {trigger.signal} {trigger.edge_type}",
                            {trigger.signal: value}
                        )
                        self.events_detected.add(trigger_id)
        
        # Update capture statistics
        current_time = time.time()
        capture_rate = self.config.periodic_checks_interval / (current_time - self.last_sample_time)
        self.last_sample_time = current_time
        
        # Log statistics if verbose
        if self.config.debug_level >= 2:
            print(f"WaveDrom capture stats: {self.cycles_captured} cycles, " +
                 f"{capture_rate:.1f} cycles/s, {len(self.wave_gen.event_history)} events")
    
    def _periodic_save(self):
        """Save the current waveform state periodically"""
        if not self.config.periodic_save:
            return
            
        try:
            # Generate filename with cycle count
            filename = f"wavedrom_periodic_{self.cycles_captured}"
            
            if self.config.output_format == "html":
                filename += ".html"
            else:
                filename += ".json"
                
            # Generate output
            self.container.generate_wavedrom(filename)
            
            if self.config.debug_level >= 2:
                print(f"Saved periodic waveform to {filename}")
        except Exception as e:
            if self.config.debug_level >= 1:
                print(f"Error saving periodic waveform: {e}")
    
    def get_capture_stats(self) -> Dict[str, Any]:
        """
        Get statistics about the capture process
        
        Returns:
            Dictionary of capture statistics
        """
        current_time = time.time()
        execution_time = current_time - self.start_time if self.start_time else 0
        
        return {
            "cycles_captured": self.cycles_captured,
            "execution_time_s": execution_time,
            "events_detected": len(self.events_detected),
            "event_history_size": len(self.wave_gen.event_history),
            "cycles_per_second": self.cycles_captured / execution_time if execution_time > 0 else 0,
            "paused": self.paused,
            "done": self.done
        }


# Utility functions for creating capture instances

def create_standard_capture(dut, container: WaveformContainer) -> WaveformCapture:
    """
    Create a standard waveform capture instance
    
    Args:
        dut: Device under test
        container: WaveformContainer instance
        
    Returns:
        WaveformCapture instance
    """
    config = CaptureConfig(
        sample_interval_ns=0,  # Every clock cycle
        periodic_checks_interval=50,
        enable_statistics=True,
        debug_level=1
    )
    
    return WaveformCapture(dut, container, config)


def create_debug_capture(dut, container: WaveformContainer) -> WaveformCapture:
    """
    Create a debug waveform capture instance with verbose output
    
    Args:
        dut: Device under test
        container: WaveformContainer instance
        
    Returns:
        WaveformCapture instance
    """
    config = CaptureConfig(
        sample_interval_ns=0,  # Every clock cycle
        periodic_checks_interval=25,
        enable_statistics=True,
        periodic_save=True,
        save_interval_cycles=500,
        debug_level=3
    )
    
    return WaveformCapture(dut, container, config)


def create_performance_capture(dut, container: WaveformContainer, max_cycles: int) -> WaveformCapture:
    """
    Create a performance-optimized waveform capture instance
    
    Args:
        dut: Device under test
        container: WaveformContainer instance
        max_cycles: Maximum number of cycles to capture
        
    Returns:
        WaveformCapture instance
    """
    config = CaptureConfig(
        sample_interval_ns=0,  # Every clock cycle
        max_cycles=max_cycles,
        periodic_checks_interval=100,
        enable_statistics=True,
        periodic_save=False,
        debug_level=1
    )
    
    return WaveformCapture(dut, container, config)
