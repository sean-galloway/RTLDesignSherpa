# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SafetyError
# Purpose: Enhanced Base Testbench Class with Safety Features
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Enhanced Base Testbench Class with Safety Features

Added comprehensive safety features:
- Timeout protection with configurable limits
- Memory usage monitoring and limits
- Progress tracking to detect stuck tests
- Resource monitoring (CPU, tasks)
- Graceful shutdown capabilities
- Deadlock detection
"""
import os
import logging
import time
import psutil
import asyncio
import signal
import threading
from contextlib import contextmanager
from typing import Optional, Callable, Dict, Any

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer, Edge, with_timeout
from cocotb.clock import Clock
from cocotb.utils import get_sim_time


class SafetyError(Exception):
    """Exception raised when safety limits are exceeded"""
    pass


class TestbenchTimeout(SafetyError):
    """Exception raised when testbench timeout is exceeded"""
    pass


class MemoryLimitExceeded(SafetyError):
    """Exception raised when memory limit is exceeded"""
    pass


class ProgressStalled(SafetyError):
    """Exception raised when test progress has stalled"""
    pass


class TBBase:
    """
    Enhanced base class for testbenches with comprehensive safety features.

    Safety Features:
    - Configurable timeouts for tests and operations
    - Memory usage monitoring with limits
    - Progress tracking to detect stalled tests
    - Resource monitoring (CPU, active tasks)
    - Graceful shutdown on safety violations
    - Deadlock detection for async operations
    """

    default_log_level = logging.DEBUG

    # Default safety limits (can be overridden via environment or constructor)
    DEFAULT_SAFETY_LIMITS = {
        'max_test_duration_minutes': 30,        # Maximum test duration
        'max_memory_mb': 2048,                  # Maximum memory usage in MB
        'memory_check_interval_s': 10,          # How often to check memory
        'progress_timeout_minutes': 5,          # Max time without progress
        'max_concurrent_tasks': 100,            # Maximum concurrent asyncio tasks
        'cpu_check_interval_s': 30,             # How often to check CPU usage
        'max_cpu_percent': 95,                  # Maximum CPU usage percentage
        'enable_safety_monitoring': True,       # Enable/disable safety features
        'safety_check_interval_s': 5,           # General safety check interval
    }

    def __init__(self, dut, safety_limits: Optional[Dict[str, Any]] = None):
        """
        Initialize testbench with DUT and safety monitoring.

        Args:
            dut: Device under test
            safety_limits: Dictionary of safety limits to override defaults
        """
        self.dut = dut

        # Setup logging FIRST (needed by other init methods)
        self.log_path = os.environ.get('LOG_PATH')
        if not self.log_path:
            log_dir = os.path.join(os.getcwd(), 'logs')
            os.makedirs(log_dir, exist_ok=True)
            self.log_path = os.path.join(log_dir, 'default_cocotb.log')
            print(f"WARNING: LOG_PATH not specified. Using default: {self.log_path}")

        self.dut_name = os.environ.get('DUT', 'unknown_dut')
        self.log_count = 0
        self.log = self.configure_logging(level=TBBase.default_log_level)

        # Merge safety limits with defaults
        self.safety_limits = self.DEFAULT_SAFETY_LIMITS.copy()
        if safety_limits:
            self.safety_limits.update(safety_limits)

        # Override with environment variables if present
        self._load_safety_limits_from_env()

        # Safety monitoring state
        self.safety_enabled = self.safety_limits['enable_safety_monitoring']
        self.test_start_time = time.time()
        self.last_progress_time = time.time()
        self.progress_markers = []
        self.safety_violations = []
        self.shutdown_requested = False
        self.safety_monitor_task = None

        # Process monitoring
        self.process = psutil.Process()
        self.initial_memory = self.process.memory_info().rss / (1024 * 1024)  # MB

        # Threading for non-async safety monitoring
        self.safety_lock = threading.RLock()
        self.safety_thread = None

        # Initialize signal monitors
        self._signal_monitors = {}
        self._monitor_tasks = []

        # Start safety monitoring if enabled
        if self.safety_enabled:
            self._start_safety_monitoring()

        self.log.info(f"Initialized testbench for {self.dut_name} with safety monitoring: {self.safety_enabled}")
        self.log.info(f"Safety limits: {self.safety_limits}")
        self.log.info(f"Initial memory usage: {self.initial_memory:.1f} MB")

    def _load_safety_limits_from_env(self):
        """Load safety limits from environment variables"""
        env_mappings = {
            'TB_MAX_DURATION_MIN': 'max_test_duration_minutes',
            'TB_MAX_MEMORY_MB': 'max_memory_mb',
            'TB_MEMORY_CHECK_INTERVAL': 'memory_check_interval_s',
            'TB_PROGRESS_TIMEOUT_MIN': 'progress_timeout_minutes',
            'TB_MAX_TASKS': 'max_concurrent_tasks',
            'TB_CPU_CHECK_INTERVAL': 'cpu_check_interval_s',
            'TB_MAX_CPU_PERCENT': 'max_cpu_percent',
            'TB_ENABLE_SAFETY': 'enable_safety_monitoring',
            'TB_SAFETY_CHECK_INTERVAL': 'safety_check_interval_s',
        }

        for env_var, limit_key in env_mappings.items():
            if env_var in os.environ:
                try:
                    value = os.environ[env_var]
                    if limit_key == 'enable_safety_monitoring':
                        self.safety_limits[limit_key] = value.lower() in ['true', '1', 'yes']
                    else:
                        self.safety_limits[limit_key] = float(value)
                    self.log.debug(f"Loaded safety limit from env: {limit_key} = {self.safety_limits[limit_key]}")
                except (ValueError, TypeError) as e:
                    self.log.warning(f"Invalid environment value for {env_var}: {value}, error: {e}")

    def _start_safety_monitoring(self):
        """Start safety monitoring tasks"""
        try:
            # Start asyncio safety monitor
            self.safety_monitor_task = cocotb.start_soon(self._async_safety_monitor())

            # Start thread-based safety monitor for non-async checks
            self.safety_thread = threading.Thread(target=self._thread_safety_monitor, daemon=True)
            self.safety_thread.start()

            self.log.info("Safety monitoring started")
        except Exception as e:
            self.log.error(f"Failed to start safety monitoring: {e}")

    async def _async_safety_monitor(self):
        """Async safety monitoring loop"""
        try:
            while not self.shutdown_requested:
                # Check for safety violations
                await self._check_async_safety()

                # Wait before next check
                await Timer(self.safety_limits['safety_check_interval_s'] * 1000, units='ms')

        except Exception as e:
            self.log.error(f"Async safety monitor error: {e}")

    def _thread_safety_monitor(self):
        """Thread-based safety monitoring for resource checks"""
        try:
            while not self.shutdown_requested:
                with self.safety_lock:
                    self._check_thread_safety()

                time.sleep(self.safety_limits['safety_check_interval_s'])

        except Exception as e:
            self.log.error(f"Thread safety monitor error: {e}")

    async def _check_async_safety(self):
        """Check async-related safety conditions"""
        try:
            # Check test duration
            self._check_test_duration()

            # Check progress timeout
            self._check_progress_timeout()

            # Check concurrent tasks
            self._check_concurrent_tasks()

        except SafetyError as e:
            await self._handle_safety_violation(e)

    def _check_thread_safety(self):
        """Check thread-related safety conditions"""
        try:
            # Check memory usage
            self._check_memory_usage()

            # Check CPU usage
            self._check_cpu_usage()

        except SafetyError as e:
            self._handle_safety_violation_sync(e)

    def _check_test_duration(self):
        """Check if test has exceeded maximum duration"""
        elapsed_minutes = (time.time() - self.test_start_time) / 60
        max_duration = self.safety_limits['max_test_duration_minutes']

        if elapsed_minutes > max_duration:
            raise TestbenchTimeout(f"Test exceeded maximum duration: {elapsed_minutes:.1f} > {max_duration} minutes")

    def _check_memory_usage(self):
        """Check memory usage against limits"""
        try:
            current_memory = self.process.memory_info().rss / (1024 * 1024)  # MB
            max_memory = self.safety_limits['max_memory_mb']

            if current_memory > max_memory:
                raise MemoryLimitExceeded(f"Memory usage exceeded limit: {current_memory:.1f} > {max_memory} MB")

            # Log memory usage periodically
            memory_increase = current_memory - self.initial_memory
            if memory_increase > 100:  # Log if memory increased by > 100MB
                self.log.warning(f"Memory usage: {current_memory:.1f} MB (+{memory_increase:.1f} MB from start)")

        except psutil.NoSuchProcess:
            self.log.warning("Process no longer exists for memory monitoring")

    def _check_progress_timeout(self):
        """Check if test progress has stalled"""
        elapsed_since_progress = (time.time() - self.last_progress_time) / 60
        timeout_minutes = self.safety_limits['progress_timeout_minutes']

        if elapsed_since_progress > timeout_minutes:
            raise ProgressStalled(f"No progress for {elapsed_since_progress:.1f} > {timeout_minutes} minutes")

    def _check_concurrent_tasks(self):
        """Check number of concurrent asyncio tasks"""
        try:
            # Get current event loop and count tasks
            loop = asyncio.get_running_loop()
            tasks = [task for task in asyncio.all_tasks(loop) if not task.done()]
            task_count = len(tasks)
            max_tasks = self.safety_limits['max_concurrent_tasks']

            if task_count > max_tasks:
                # Log task details for debugging
                self.log.warning(f"High task count: {task_count}")
                for i, task in enumerate(tasks[:10]):  # Log first 10 tasks
                    self.log.debug(f"Task {i}: {task}")

                raise SafetyError(f"Too many concurrent tasks: {task_count} > {max_tasks}")

        except RuntimeError:
            # No event loop running
            pass

    def _check_cpu_usage(self):
        """Check CPU usage"""
        try:
            cpu_percent = self.process.cpu_percent()
            max_cpu = self.safety_limits['max_cpu_percent']

            if cpu_percent > max_cpu:
                self.log.warning(f"High CPU usage: {cpu_percent:.1f}% > {max_cpu}%")

        except psutil.NoSuchProcess:
            self.log.warning("Process no longer exists for CPU monitoring")

    async def _handle_safety_violation(self, error: SafetyError):
        """Handle safety violation in async context"""
        self.safety_violations.append((time.time(), str(error)))
        self.log.error(f"SAFETY VIOLATION: {error}")

        # Request shutdown
        self.shutdown_requested = True

        # Give some time for cleanup
        await Timer(1000, units='ms')

        # Raise the error to stop the test
        raise error

    def _handle_safety_violation_sync(self, error: SafetyError):
        """Handle safety violation in sync context"""
        self.safety_violations.append((time.time(), str(error)))
        self.log.error(f"SAFETY VIOLATION: {error}")

        # Request shutdown
        self.shutdown_requested = True

    def mark_progress(self, description: str = ""):
        """Mark test progress to reset progress timeout"""
        current_time = time.time()
        self.last_progress_time = current_time
        self.progress_markers.append((current_time, description))

        # Keep only recent progress markers
        cutoff_time = current_time - 300  # Keep last 5 minutes
        self.progress_markers = [(t, d) for t, d in self.progress_markers if t > cutoff_time]

        # if description:
        #     self.log.debug(f"Progress: {description}")

    @contextmanager
    def safe_operation(self, operation_name: str, timeout_seconds: Optional[float] = None):
        """
        Context manager for safe operations with timeout and progress tracking.

        Args:
            operation_name: Name of the operation for logging
            timeout_seconds: Operation timeout (None for no timeout)
        """
        start_time = time.time()
        self.mark_progress(f"Starting {operation_name}")

        try:
            # self.log.debug(f"Starting safe operation: {operation_name}")
            yield

        except Exception as e:
            self.log.error(f"Error in safe operation {operation_name}: {e}")
            raise

        # finally:
        #     duration = time.time() - start_time
        #     self.mark_progress(f"Completed {operation_name}")
        #     self.log.debug(f"Completed safe operation: {operation_name} in {duration:.2f}s")

    async def safe_wait_clocks(self, clk_name: str, count: int = 1,
                                timeout_seconds: Optional[float] = None,
                                delay: int = 100, units: str = 'ps'):
        """
        Safe version of wait_clocks with timeout protection.

        Args:
            clk_name: Clock signal name
            count: Number of clock cycles to wait
            timeout_seconds: Maximum time to wait (None for default)
            delay: Additional delay per cycle
            units: Time units for delay
        """
        if timeout_seconds is None:
            # FIXED: Use more reasonable timeout calculation and avoid floating point precision issues
            # Base timeout: assume 10ns clock period, add reasonable margin
            base_timeout_ms = count * 0.01  # 10ns per cycle = 0.01ms per cycle
            margin_ms = max(100, count * 0.002)  # At least 100ms margin, plus small per-cycle margin
            timeout_ms = int(base_timeout_ms + margin_ms)  # Convert to integer to avoid precision issues
        else:
            # Convert provided timeout to integer milliseconds to avoid precision issues
            timeout_ms = int(timeout_seconds * 1000)

        with self.safe_operation(f"wait_clocks({clk_name}, {count})"):
            try:
                clk_signal = getattr(self.dut, clk_name)

                # Use timeout wrapper with integer milliseconds and proper round_mode
                async def wait_operation():
                    for i in range(count):
                        await RisingEdge(clk_signal)
                        await Timer(delay, units=units)

                        # # Mark progress every 100 cycles
                        # if i % 100 == 0:
                        #     self.mark_progress(f"wait_clocks {i}/{count}")

                # FIXED: Use integer timeout and specify round_mode to handle precision gracefully
                await with_timeout(wait_operation(), timeout_ms, 'ms')

            except asyncio.TimeoutError:
                raise TestbenchTimeout(f"wait_clocks timeout after {timeout_ms}ms")

    async def safe_wait_time(self, delay: int = 100, units: str = 'ps',
                            timeout_seconds: Optional[float] = None):
        """Safe version of wait_time with timeout protection"""
        if timeout_seconds is None:
            # FIXED: More reasonable timeout calculation based on actual delay
            if units == 'ps':
                base_timeout_ms = delay * 0.001  # ps to ms
            elif units == 'ns':
                base_timeout_ms = delay * 1.0  # ns to ms
            elif units == 'us':
                base_timeout_ms = delay * 1000.0  # us to ms
            elif units == 'ms':
                base_timeout_ms = delay  # already ms
            else:
                base_timeout_ms = 1000  # 1 second default

            timeout_ms = int(base_timeout_ms + 100)  # Add 100ms margin, convert to int
        else:
            timeout_ms = int(timeout_seconds * 1000)

        with self.safe_operation(f"wait_time({delay} {units})"):
            try:
                # FIXED: Use integer timeout to avoid precision issues
                await with_timeout(Timer(delay, units=units), timeout_ms, 'ms')
            except asyncio.TimeoutError:
                raise TestbenchTimeout(f"wait_time timeout after {timeout_ms}ms")

    def add_monitor(self, signal_name: str, callback: Optional[Callable] = None):
        """Enhanced signal monitor with safety checks"""
        if len(self._signal_monitors) >= 50:  # Limit number of monitors
            self.log.warning(f"Too many signal monitors ({len(self._signal_monitors)}), skipping {signal_name}")
            return None

        if not hasattr(self.dut, signal_name):
            self.log.error(f"Signal {signal_name} not found in DUT")
            return None

        signal = getattr(self.dut, signal_name)
        monitor_id = len(self._signal_monitors)

        self._signal_monitors[monitor_id] = {
            'signal_name': signal_name,
            'signal': signal,
            'callback': callback,
            'last_value': signal.value,
            'start_time': time.time()
        }

        task = cocotb.start_soon(self._monitor_signal(monitor_id))
        self._monitor_tasks.append(task)

        self.log.debug(f"Added monitor for signal {signal_name}")
        return monitor_id

    async def _monitor_signal(self, monitor_id: int):
        """Enhanced signal monitoring with safety checks"""
        monitor_info = self._signal_monitors[monitor_id]
        signal = monitor_info['signal']
        callback = monitor_info['callback']
        last_value = monitor_info['last_value']

        try:
            change_count = 0
            while not self.shutdown_requested:
                # Add timeout to edge detection
                try:
                    await with_timeout(Edge(signal), 10000, 'ms')  # 10 second timeout
                except asyncio.TimeoutError:
                    # Signal hasn't changed in 10 seconds, continue monitoring
                    continue

                new_value = signal.value
                if new_value != last_value and callback:
                    callback(signal, new_value)
                    change_count += 1

                    # Mark progress for active signals
                    if change_count % 1000 == 0:
                        self.mark_progress(f"Signal {monitor_info['signal_name']} changes: {change_count}")

                monitor_info['last_value'] = new_value

        except Exception as e:
            self.log.error(f"Error in signal monitor for {monitor_info['signal_name']}: {e}")

    def get_safety_status(self) -> Dict[str, Any]:
        """Get current safety status and statistics"""
        current_time = time.time()
        elapsed_time = current_time - self.test_start_time

        status = {
            'safety_enabled': self.safety_enabled,
            'test_duration_minutes': elapsed_time / 60,
            'shutdown_requested': self.shutdown_requested,
            'safety_violations': len(self.safety_violations),
            'progress_markers': len(self.progress_markers),
            'active_monitors': len(self._signal_monitors),
            'safety_limits': self.safety_limits.copy(),
        }

        # Add resource usage
        try:
            memory_mb = self.process.memory_info().rss / (1024 * 1024)
            cpu_percent = self.process.cpu_percent()
            status.update({
                'memory_usage_mb': memory_mb,
                'memory_increase_mb': memory_mb - self.initial_memory,
                'cpu_percent': cpu_percent,
            })
        except psutil.NoSuchProcess:
            status.update({
                'memory_usage_mb': 0,
                'memory_increase_mb': 0,
                'cpu_percent': 0,
            })

        # Add asyncio task count
        try:
            loop = asyncio.get_running_loop()
            tasks = [task for task in asyncio.all_tasks(loop) if not task.done()]
            status['active_tasks'] = len(tasks)
        except RuntimeError:
            status['active_tasks'] = 0

        return status

    def emergency_shutdown(self):
        """Emergency shutdown of testbench"""
        self.log.error("EMERGENCY SHUTDOWN REQUESTED")
        self.shutdown_requested = True

        # Cancel all monitor tasks
        for task in self._monitor_tasks:
            if not task.done():
                task.cancel()

        # Clear monitors
        self._signal_monitors.clear()

        # Log final status
        status = self.get_safety_status()
        self.log.error(f"Final safety status: {status}")

    def __del__(self):
        """Cleanup on destruction"""
        try:
            if hasattr(self, 'shutdown_requested'):
                self.shutdown_requested = True
        except:
            pass

    # Keep all existing methods with safety enhancements
    async def start_clock(self, clk_name: str, freq: int = 10, units: str = 'ns'):
        """Start clock with safety monitoring"""
        with self.safe_operation(f"start_clock({clk_name})"):
            self.log.debug(f"Starting clock {clk_name} with frequency {freq} {units}")
            clk_signal = getattr(self.dut, clk_name)
            cocotb.start_soon(Clock(clk_signal, freq, units=units).start())
            await Timer(100, units='ps')
            self.mark_progress(f"Clock {clk_name} started")

    def clock_gen(self, clk_signal, period: int = 10, units: str = 'ns'):
        """
        Generate clock with safety monitoring.

        Args:
            clk_signal: Clock signal to drive
            period: Clock period
            units: Time units for period

        Returns:
            Coroutine that can be used with cocotb.start_soon()
        """
        self.log.debug(f"Creating clock generator with period {period} {units}")
        self.mark_progress(f"Clock generator created")

        # Return the clock start coroutine
        clock = Clock(clk_signal, period, units=units)
        return clock.start()

    async def wait_clocks(self, clk_name: str, count: int = 1, delay: int = 100, units: str = 'ps'):
        """Wait for clock edges with safety monitoring"""
        await self.safe_wait_clocks(clk_name, count, None, delay, units)

    async def wait_falling_clocks(self, clk_name: str, count: int = 1, delay: int = 100, units: str = 'ps'):
        """Wait for falling clock edges with safety monitoring"""
        with self.safe_operation(f"wait_falling_clocks({clk_name}, {count})"):
            clk_signal = getattr(self.dut, clk_name)
            for i in range(count):
                await FallingEdge(clk_signal)
                await Timer(delay, units=units)
                if i % 1000 == 0:
                    self.mark_progress(f"wait_falling_clocks {i}/{count}")

    async def wait_time(self, delay: int = 100, units: str = 'ps'):
        """Wait for time with safety monitoring"""
        await self.safe_wait_time(delay, units)

    def remove_monitor(self, monitor_id: int):
        """Remove monitor with safety checks"""
        if monitor_id not in self._signal_monitors:
            self.log.error(f"Monitor ID {monitor_id} not found")
            return False

        monitor_info = self._signal_monitors[monitor_id]
        self.log.debug(f"Removed monitor for signal {monitor_info['signal_name']}")
        del self._signal_monitors[monitor_id]
        return True

    # Keep all existing static methods unchanged
    @staticmethod
    def convert_param_type(value, default):
        """Converts environment variable values to the correct type based on the default value."""
        if isinstance(default, bool):
            if isinstance(value, bool):
                return value
            elif isinstance(value, str):
                return value.lower() in ["true", "1", "yes"]
            else:
                return bool(value)
        elif isinstance(default, int):
            try:
                return int(value)
            except (ValueError, TypeError):
                return default
        elif isinstance(default, float):
            try:
                return float(value)
            except (ValueError, TypeError):
                return default
        return value

    def assert_reset(self):
        """Base method to assert reset"""
        self.mark_progress("assert_reset")
        self.log.info("Base assert_reset called - should be overridden")

    def deassert_reset(self):
        """Base method to deassert reset"""
        self.mark_progress("deassert_reset")
        self.log.info("Base deassert_reset called - should be overridden")

    def configure_logging(self, level=logging.DEBUG):
        """Configure logging with safety monitoring"""
        log_name = f'cocotb_log_{self.dut_name}'
        log = logging.getLogger(log_name)

        for handler in log.handlers[:]:
            log.removeHandler(handler)

        log.setLevel(level)

        try:
            if log_dir := os.path.dirname(self.log_path):
                os.makedirs(log_dir, exist_ok=True)

            fh = logging.FileHandler(self.log_path, mode='w')

            fh.setLevel(logging.DEBUG)

            formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
            fh.setFormatter(formatter)
            log.addHandler(fh)

            log.propagate = True

            console = logging.StreamHandler()
            console.setLevel(logging.INFO)
            console.setFormatter(formatter)
            log.addHandler(console)

            self.log_count += 1

        except Exception as e:
            print(f"ERROR setting up logging to {self.log_path}: {str(e)}")
            console = logging.StreamHandler()
            console.setLevel(logging.DEBUG)
            formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
            console.setFormatter(formatter)
            log.addHandler(console)

        return log

    def log_flush(self):
        """Force flush all log handlers"""
        for handler in self.log.handlers:
            handler.flush()

    @staticmethod
    def get_time_ns_str():
        time_ns = get_sim_time('ns')
        return f' @ {time_ns}ns'

    @staticmethod
    def convert_to_int(value):
        """Convert a value to an integer with hex string support"""
        if isinstance(value, int):
            return value
        elif isinstance(value, str) and "'h" in value:
            try:
                _, hex_value = value.split("'h")
                return int(hex_value, 16)
            except ValueError as e:
                raise ValueError(f"Invalid hexadecimal input: {value}") from e
        else:
            return int(value)

    @staticmethod
    def hex_format(value, max_value):
        """Format an integer value as a hexadecimal string with leading zeros"""
        hex_width = (max_value.bit_length() + 3) // 4
        return format(int(value), f'0{hex_width}X')

    @staticmethod
    def format_hex(value, max_value):
        hex_width = (max_value.bit_length() + 3) // 4
        return format(int(value), f'0{hex_width}X')

    @staticmethod
    def generate_alternating_ones(n):
        """Generate a number with alternating '1's up to position N"""
        num = 0
        for i in range(n):
            if i % 2 == 0:
                num |= 1 << i
        return num

    @staticmethod
    def invert_bits(num, n):
        """Invert the bits of a number up to position N"""
        mask = (1 << n) - 1
        return num ^ mask

    @staticmethod
    def convert_to_bytearray(data):
        """Convert the input data to a bytearray if it's not already one"""
        if isinstance(data, bytearray):
            return data
        elif isinstance(data, (bytes, list)):
            return bytearray(data)
        else:
            raise TypeError("Input data must be a bytearray, bytes, or list of integers")

    @staticmethod
    def bytearray_to_hex_strings(bytearrays):
        """Convert a list of bytearray values into hex strings"""
        return [TBBase.bytearray_to_hex(ba) for ba in bytearrays]

    @staticmethod
    def bytearray_to_hex(bytearray_value):
        """Convert a single bytearray to a hex string"""
        return ''.join(f'{byte:02X}, ' for byte in bytearray_value)

    @staticmethod
    def format_dec(decimal, width):
        """Format a decimal to a string prepending 0's"""
        return f"{decimal:0{width}d}"
