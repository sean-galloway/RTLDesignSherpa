# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TestMetrics
# Purpose: Advanced Monitoring and Debugging Tools for Enhanced GAXI Tests
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Advanced Monitoring and Debugging Tools for Enhanced GAXI Tests

This module provides additional monitoring, profiling, and debugging
capabilities for the enhanced safety features.
"""

import time
import json
import threading
import traceback
import linecache
import gc
import sys
from pathlib import Path
from typing import Dict, List, Any, Optional
from dataclasses import dataclass, asdict
from contextlib import contextmanager
import psutil


@dataclass
class TestMetrics:
    """Structured test metrics for analysis and reporting"""
    test_name: str
    start_time: float
    end_time: Optional[float] = None
    duration_seconds: Optional[float] = None
    memory_peak_mb: float = 0.0
    memory_start_mb: float = 0.0
    transactions_sent: int = 0
    transactions_received: int = 0
    errors: int = 0
    safety_violations: int = 0
    progress_markers: int = 0
    status: str = "running"  # running, completed, failed, timeout
    
    def finalize(self):
        """Finalize metrics when test completes"""
        if self.end_time is None:
            self.end_time = time.time()
        self.duration_seconds = self.end_time - self.start_time
        self.status = "completed" if self.errors == 0 else "failed"


class PerformanceProfiler:
    """
    Performance profiler for GAXI tests with memory tracking,
    CPU monitoring, and execution analysis.
    """
    
    def __init__(self, log=None):
        self.log = log
        self.profiles = {}
        self.current_profile = None
        self.process = psutil.Process()
        
    def start_profile(self, profile_name: str) -> str:
        """Start a new performance profile"""
        profile_id = f"{profile_name}_{int(time.time())}"
        
        self.profiles[profile_id] = {
            'name': profile_name,
            'start_time': time.time(),
            'start_memory': self.process.memory_info().rss / (1024 * 1024),
            'start_cpu_times': self.process.cpu_times(),
            'checkpoints': [],
            'memory_samples': [],
            'cpu_samples': [],
            'active': True
        }
        
        self.current_profile = profile_id
        
        # Start sampling thread
        self._start_sampling_thread(profile_id)
        
        if self.log:
            self.log.info(f"Started performance profile: {profile_name} ({profile_id})")
        
        return profile_id
    
    def add_checkpoint(self, name: str, profile_id: Optional[str] = None):
        """Add a checkpoint to the current or specified profile"""
        if profile_id is None:
            profile_id = self.current_profile
            
        if profile_id not in self.profiles:
            return
            
        profile = self.profiles[profile_id]
        current_time = time.time()
        current_memory = self.process.memory_info().rss / (1024 * 1024)
        
        checkpoint = {
            'name': name,
            'timestamp': current_time,
            'elapsed': current_time - profile['start_time'],
            'memory_mb': current_memory,
            'memory_delta': current_memory - profile['start_memory']
        }
        
        profile['checkpoints'].append(checkpoint)
        
        if self.log:
            self.log.debug(f"Checkpoint {name}: {checkpoint['elapsed']:.2f}s, "
                          f"{checkpoint['memory_mb']:.1f}MB (+{checkpoint['memory_delta']:.1f}MB)")
    
    def end_profile(self, profile_id: Optional[str] = None) -> Dict[str, Any]:
        """End a profile and return analysis"""
        if profile_id is None:
            profile_id = self.current_profile
            
        if profile_id not in self.profiles:
            return {}
            
        profile = self.profiles[profile_id]
        profile['active'] = False
        profile['end_time'] = time.time()
        profile['duration'] = profile['end_time'] - profile['start_time']
        profile['end_memory'] = self.process.memory_info().rss / (1024 * 1024)
        profile['memory_delta'] = profile['end_memory'] - profile['start_memory']
        profile['end_cpu_times'] = self.process.cpu_times()
        
        # Calculate CPU usage
        start_cpu = profile['start_cpu_times']
        end_cpu = profile['end_cpu_times']
        cpu_time_used = (end_cpu.user - start_cpu.user) + (end_cpu.system - start_cpu.system)
        profile['cpu_percent'] = (cpu_time_used / profile['duration']) * 100 if profile['duration'] > 0 else 0
        
        # Analyze memory patterns
        profile['memory_analysis'] = self._analyze_memory_pattern(profile)
        
        if self.log:
            self.log.info(f"Profile {profile['name']} completed: "
                         f"{profile['duration']:.2f}s, "
                         f"memory: {profile['memory_delta']:.1f}MB, "
                         f"CPU: {profile['cpu_percent']:.1f}%")
        
        return profile
    
    def _start_sampling_thread(self, profile_id: str):
        """Start background thread to sample memory and CPU"""
        def sample_resources():
            while profile_id in self.profiles and self.profiles[profile_id]['active']:
                try:
                    current_time = time.time()
                    memory_info = self.process.memory_info()
                    cpu_percent = self.process.cpu_percent()
                    
                    self.profiles[profile_id]['memory_samples'].append({
                        'timestamp': current_time,
                        'memory_mb': memory_info.rss / (1024 * 1024),
                        'memory_vms_mb': memory_info.vms / (1024 * 1024)
                    })
                    
                    self.profiles[profile_id]['cpu_samples'].append({
                        'timestamp': current_time,
                        'cpu_percent': cpu_percent
                    })
                    
                    time.sleep(1)  # Sample every second
                    
                except (psutil.NoSuchProcess, KeyError):
                    break
                except Exception as e:
                    if self.log:
                        self.log.warning(f"Error in resource sampling: {e}")
                    break
        
        thread = threading.Thread(target=sample_resources, daemon=True)
        thread.start()
    
    def _analyze_memory_pattern(self, profile: Dict[str, Any]) -> Dict[str, Any]:
        """Analyze memory usage patterns"""
        samples = profile['memory_samples']
        if len(samples) < 2:
            return {}
        
        memories = [s['memory_mb'] for s in samples]
        peak_memory = max(memories)
        min_memory = min(memories)
        avg_memory = sum(memories) / len(memories)
        
        # Look for memory leaks (consistent upward trend)
        if len(samples) >= 10:
            first_half = memories[:len(memories)//2]
            second_half = memories[len(memories)//2:]
            avg_first = sum(first_half) / len(first_half)
            avg_second = sum(second_half) / len(second_half)
            leak_indicator = avg_second - avg_first
        else:
            leak_indicator = 0
        
        return {
            'peak_memory_mb': peak_memory,
            'min_memory_mb': min_memory,
            'avg_memory_mb': avg_memory,
            'memory_range_mb': peak_memory - min_memory,
            'potential_leak_mb': leak_indicator,
            'sample_count': len(samples)
        }
    
    def get_profile_summary(self, profile_id: str) -> str:
        """Get human-readable profile summary"""
        if profile_id not in self.profiles:
            return "Profile not found"
        
        profile = self.profiles[profile_id]
        
        summary = f"""
Performance Profile: {profile['name']}
Duration: {profile.get('duration', 0):.2f} seconds
Memory Usage: {profile.get('memory_delta', 0):.1f} MB delta
CPU Usage: {profile.get('cpu_percent', 0):.1f}%
Checkpoints: {len(profile['checkpoints'])}
"""
        
        if 'memory_analysis' in profile:
            ma = profile['memory_analysis']
            summary += f"""
Memory Analysis:
  Peak: {ma.get('peak_memory_mb', 0):.1f} MB
  Average: {ma.get('avg_memory_mb', 0):.1f} MB
  Range: {ma.get('memory_range_mb', 0):.1f} MB
  Potential Leak: {ma.get('potential_leak_mb', 0):.1f} MB
"""
        
        return summary


class AdvancedDebugger:
    """
    Advanced debugging tools for GAXI tests including stack trace
    analysis, deadlock detection, and automated issue reporting.
    """
    
    def __init__(self, log=None):
        self.log = log
        self.debug_sessions = {}
        self.stack_traces = []
        self.deadlock_detector = DeadlockDetector(log)
    
    def start_debug_session(self, session_name: str) -> str:
        """Start a new debug session"""
        session_id = f"{session_name}_{int(time.time())}"
        
        self.debug_sessions[session_id] = {
            'name': session_name,
            'start_time': time.time(),
            'stack_traces': [],
            'exceptions': [],
            'warnings': [],
            'active': True
        }
        
        # Install exception hook
        self._install_exception_hook(session_id)
        
        if self.log:
            self.log.info(f"Started debug session: {session_name} ({session_id})")
        
        return session_id
    
    def capture_stack_trace(self, session_id: str, context: str = ""):
        """Capture current stack trace"""
        if session_id not in self.debug_sessions:
            return
        
        stack = traceback.format_stack()
        trace_info = {
            'timestamp': time.time(),
            'context': context,
            'stack': stack,
            'thread_id': threading.current_thread().ident,
            'thread_name': threading.current_thread().name
        }
        
        self.debug_sessions[session_id]['stack_traces'].append(trace_info)
        
        if self.log:
            self.log.debug(f"Captured stack trace for {context} in session {session_id}")
    
    def _install_exception_hook(self, session_id: str):
        """Install exception hook to capture unhandled exceptions"""
        original_excepthook = sys.excepthook
        
        def debug_excepthook(exc_type, exc_value, exc_traceback):
            if session_id in self.debug_sessions:
                exception_info = {
                    'timestamp': time.time(),
                    'type': str(exc_type),
                    'value': str(exc_value),
                    'traceback': traceback.format_exception(exc_type, exc_value, exc_traceback),
                    'thread_id': threading.current_thread().ident
                }
                
                self.debug_sessions[session_id]['exceptions'].append(exception_info)
                
                if self.log:
                    self.log.error(f"Captured exception in debug session {session_id}: {exc_type.__name__}: {exc_value}")
            
            # Call original hook
            original_excepthook(exc_type, exc_value, exc_traceback)
        
        sys.excepthook = debug_excepthook
    
    def analyze_debug_session(self, session_id: str) -> Dict[str, Any]:
        """Analyze a debug session for common issues"""
        if session_id not in self.debug_sessions:
            return {}
        
        session = self.debug_sessions[session_id]
        analysis = {
            'session_name': session['name'],
            'duration': time.time() - session['start_time'],
            'total_stack_traces': len(session['stack_traces']),
            'total_exceptions': len(session['exceptions']),
            'issues_found': []
        }
        
        # Analyze for common patterns
        if len(session['exceptions']) > 0:
            analysis['issues_found'].append({
                'type': 'exceptions',
                'count': len(session['exceptions']),
                'severity': 'high',
                'description': 'Unhandled exceptions detected'
            })
        
        # Look for potential infinite loops (many stack traces from same location)
        stack_locations = {}
        for trace in session['stack_traces']:
            if trace['stack']:
                location = trace['stack'][-2]  # Second to last frame (skip capture call)
                stack_locations[location] = stack_locations.get(location, 0) + 1
        
        for location, count in stack_locations.items():
            if count > 10:  # Same location captured many times
                analysis['issues_found'].append({
                    'type': 'potential_loop',
                    'count': count,
                    'severity': 'medium',
                    'description': f'Potential infinite loop detected: {count} traces from same location',
                    'location': location
                })
        
        return analysis
    
    def generate_debug_report(self, session_id: str, output_path: Optional[str] = None) -> str:
        """Generate comprehensive debug report"""
        if session_id not in self.debug_sessions:
            return "Session not found"
        
        session = self.debug_sessions[session_id]
        analysis = self.analyze_debug_session(session_id)
        
        report = {
            'session_info': {
                'name': session['name'],
                'session_id': session_id,
                'start_time': session['start_time'],
                'duration': analysis['duration']
            },
            'summary': {
                'stack_traces_captured': analysis['total_stack_traces'],
                'exceptions_caught': analysis['total_exceptions'],
                'issues_found': len(analysis['issues_found'])
            },
            'issues': analysis['issues_found'],
            'exceptions': session['exceptions'],
            'deadlock_analysis': self.deadlock_detector.get_analysis()
        }
        
        # Save to file if path provided
        if output_path:
            with open(output_path, 'w') as f:
                json.dump(report, f, indent=2, default=str)
        
        # Generate human-readable summary
        summary = f"""
Debug Report for {session['name']}
=================================
Session ID: {session_id}
Duration: {analysis['duration']:.2f} seconds
Stack Traces: {analysis['total_stack_traces']}
Exceptions: {analysis['total_exceptions']}
Issues Found: {len(analysis['issues_found'])}

Issues:
"""
        for issue in analysis['issues_found']:
            summary += f"- {issue['type']}: {issue['description']} (severity: {issue['severity']})\n"
        
        return summary


class DeadlockDetector:
    """
    Deadlock detector for async operations and thread synchronization.
    """
    
    def __init__(self, log=None):
        self.log = log
        self.monitored_locks = {}
        self.lock_graph = {}
        self.detection_enabled = True
    
    def monitor_lock(self, lock, name: str):
        """Add a lock to monitoring"""
        self.monitored_locks[name] = {
            'lock': lock,
            'acquired_by': None,
            'waiting_threads': [],
            'acquisition_history': []
        }
    
    def detect_potential_deadlocks(self) -> List[Dict[str, Any]]:
        """Detect potential deadlocks in lock acquisition patterns"""
        potential_deadlocks = []
        
        # Simple cycle detection in lock dependency graph
        for lock_name, lock_info in self.monitored_locks.items():
            if self._has_cycle_from_lock(lock_name, set()):
                potential_deadlocks.append({
                    'type': 'cycle_detected',
                    'lock': lock_name,
                    'description': f'Potential deadlock cycle involving {lock_name}'
                })
        
        return potential_deadlocks
    
    def _has_cycle_from_lock(self, lock_name: str, visited: set) -> bool:
        """Check for cycles in lock dependency graph (simplified)"""
        if lock_name in visited:
            return True
        
        visited.add(lock_name)
        
        # Check dependencies (this is a simplified version)
        # In a full implementation, you'd track which locks are held
        # when attempting to acquire other locks
        
        return False
    
    def get_analysis(self) -> Dict[str, Any]:
        """Get deadlock analysis summary"""
        return {
            'monitored_locks': len(self.monitored_locks),
            'potential_deadlocks': self.detect_potential_deadlocks(),
            'detection_enabled': self.detection_enabled
        }


class TestReporter:
    """
    Automated test reporting with metrics collection, trend analysis,
    and issue detection.
    """
    
    def __init__(self, report_dir: str = "test_reports", log=None):
        self.report_dir = Path(report_dir)
        self.report_dir.mkdir(exist_ok=True)
        self.log = log
        self.test_metrics: List[TestMetrics] = []
        self.profiler = PerformanceProfiler(log)
        self.debugger = AdvancedDebugger(log)
    
    def start_test_report(self, test_name: str) -> TestMetrics:
        """Start collecting metrics for a test"""
        metrics = TestMetrics(
            test_name=test_name,
            start_time=time.time(),
            memory_start_mb=psutil.Process().memory_info().rss / (1024 * 1024)
        )
        
        self.test_metrics.append(metrics)
        
        # Start profiling
        profile_id = self.profiler.start_profile(test_name)
        metrics.profile_id = profile_id
        
        # Start debug session
        debug_id = self.debugger.start_debug_session(test_name)
        metrics.debug_id = debug_id
        
        if self.log:
            self.log.info(f"Started test report for: {test_name}")
        
        return metrics
    
    def update_test_metrics(self, metrics: TestMetrics, **updates):
        """Update test metrics with new data"""
        for key, value in updates.items():
            if hasattr(metrics, key):
                setattr(metrics, key, value)
        
        # Update memory peak
        current_memory = psutil.Process().memory_info().rss / (1024 * 1024)
        metrics.memory_peak_mb = max(metrics.memory_peak_mb, current_memory)
    
    def finalize_test_report(self, metrics: TestMetrics) -> Dict[str, Any]:
        """Finalize test report and generate analysis"""
        metrics.finalize()
        
        # End profiling
        if hasattr(metrics, 'profile_id'):
            profile_data = self.profiler.end_profile(metrics.profile_id)
            metrics.profile_data = profile_data
        
        # End debug session
        if hasattr(metrics, 'debug_id'):
            debug_analysis = self.debugger.analyze_debug_session(metrics.debug_id)
            metrics.debug_analysis = debug_analysis
        
        # Generate report
        report = self._generate_test_report(metrics)
        
        # Save to file
        report_file = self.report_dir / f"{metrics.test_name}_{int(metrics.start_time)}.json"
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2, default=str)
        
        if self.log:
            self.log.info(f"Test report saved: {report_file}")
        
        return report
    
    def _generate_test_report(self, metrics: TestMetrics) -> Dict[str, Any]:
        """Generate comprehensive test report"""
        report = {
            'test_info': asdict(metrics),
            'performance': getattr(metrics, 'profile_data', {}),
            'debug_info': getattr(metrics, 'debug_analysis', {}),
            'recommendations': self._generate_recommendations(metrics)
        }
        
        return report
    
    def _generate_recommendations(self, metrics: TestMetrics) -> List[str]:
        """Generate recommendations based on test metrics"""
        recommendations = []
        
        if metrics.duration_seconds and metrics.duration_seconds > 300:  # 5 minutes
            recommendations.append("Consider optimizing test duration or breaking into smaller tests")
        
        if metrics.memory_peak_mb > 1024:  # 1GB
            recommendations.append("High memory usage detected - investigate potential memory leaks")
        
        if metrics.errors > 0:
            recommendations.append(f"Test had {metrics.errors} errors - review error handling")
        
        if metrics.safety_violations > 0:
            recommendations.append(f"Safety violations detected - review safety configuration")
        
        if hasattr(metrics, 'debug_analysis'):
            debug_issues = metrics.debug_analysis.get('issues_found', [])
            if debug_issues:
                recommendations.append(f"Debug analysis found {len(debug_issues)} potential issues")
        
        return recommendations
    
    def generate_trend_report(self, days: int = 7) -> Dict[str, Any]:
        """Generate trend analysis for recent tests"""
        cutoff_time = time.time() - (days * 24 * 3600)
        recent_tests = [m for m in self.test_metrics if m.start_time > cutoff_time]
        
        if not recent_tests:
            return {'message': 'No recent test data available'}
        
        # Calculate trends
        durations = [t.duration_seconds for t in recent_tests if t.duration_seconds]
        memory_peaks = [t.memory_peak_mb for t in recent_tests]
        error_counts = [t.errors for t in recent_tests]
        
        trend_report = {
            'period_days': days,
            'total_tests': len(recent_tests),
            'performance_trends': {
                'avg_duration_seconds': sum(durations) / len(durations) if durations else 0,
                'max_duration_seconds': max(durations) if durations else 0,
                'avg_memory_peak_mb': sum(memory_peaks) / len(memory_peaks) if memory_peaks else 0,
                'max_memory_peak_mb': max(memory_peaks) if memory_peaks else 0,
            },
            'reliability_trends': {
                'total_errors': sum(error_counts),
                'error_rate': sum(error_counts) / len(recent_tests) if recent_tests else 0,
                'successful_tests': len([t for t in recent_tests if t.errors == 0]),
                'success_rate': len([t for t in recent_tests if t.errors == 0]) / len(recent_tests) if recent_tests else 0
            }
        }
        
        return trend_report


# Context manager for easy integration
@contextmanager
def advanced_monitoring(test_name: str, report_dir: str = "test_reports", log=None):
    """
    Context manager for advanced monitoring of tests.
    
    Usage:
        with advanced_monitoring("my_test") as monitor:
            # Your test code here
            monitor.checkpoint("phase_1_complete")
            # More test code
            monitor.checkpoint("phase_2_complete")
    """
    reporter = TestReporter(report_dir, log)
    metrics = reporter.start_test_report(test_name)
    
    class Monitor:
        def __init__(self, reporter, metrics):
            self.reporter = reporter
            self.metrics = metrics
        
        def checkpoint(self, name: str):
            reporter.profiler.add_checkpoint(name, metrics.profile_id)
            reporter.debugger.capture_stack_trace(metrics.debug_id, name)
        
        def update_metrics(self, **kwargs):
            reporter.update_test_metrics(metrics, **kwargs)
        
        def get_status(self):
            return {
                'test_name': metrics.test_name,
                'duration': time.time() - metrics.start_time,
                'memory_current': psutil.Process().memory_info().rss / (1024 * 1024)
            }
    
    monitor = Monitor(reporter, metrics)
    
    try:
        yield monitor
    except Exception as e:
        metrics.errors += 1
        metrics.status = "failed"
        if log:
            log.error(f"Test {test_name} failed with exception: {e}")
        raise
    finally:
        # Update final metrics
        reporter.update_test_metrics(metrics, 
                                   transactions_sent=getattr(monitor, 'transactions_sent', 0),
                                   transactions_received=getattr(monitor, 'transactions_received', 0))
        
        # Generate final report
        report = reporter.finalize_test_report(metrics)
        
        if log:
            log.info(f"Test {test_name} completed: {report['test_info']['status']}")


# Example integration with enhanced TBBase
class MonitoringTBBase:
    """
    Example integration of advanced monitoring with TBBase.
    This shows how to integrate the monitoring tools with your existing testbench.
    """
    
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.reporter = TestReporter(log=self.log)
        self.current_test_metrics = None
    
    def start_monitored_test(self, test_name: str):
        """Start a test with advanced monitoring"""
        self.current_test_metrics = self.reporter.start_test_report(test_name)
        self.mark_progress(f"started_monitored_test_{test_name}")
    
    def monitoring_checkpoint(self, checkpoint_name: str):
        """Add a monitoring checkpoint"""
        if self.current_test_metrics:
            self.reporter.profiler.add_checkpoint(checkpoint_name, 
                                                self.current_test_metrics.profile_id)
            self.mark_progress(f"checkpoint_{checkpoint_name}")
    
    def finalize_monitored_test(self):
        """Finalize the current monitored test"""
        if self.current_test_metrics:
            # Update with safety statistics
            safety_status = self.get_safety_status()
            self.reporter.update_test_metrics(
                self.current_test_metrics,
                safety_violations=safety_status.get('safety_violations', 0),
                progress_markers=safety_status.get('progress_markers', 0)
            )
            
            # Generate final report
            report = self.reporter.finalize_test_report(self.current_test_metrics)
            self.log.info(f"Test monitoring complete: {report['test_info']['test_name']}")
            
            self.current_test_metrics = None
            return report
        
        return None
