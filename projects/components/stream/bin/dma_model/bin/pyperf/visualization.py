# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PerformanceGraphs
# Purpose: STREAM DMA Performance Visualization
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-18

"""
STREAM DMA Performance Visualization

Generates performance graphs for STREAM DMA analysis with separate
read and write path visualizations.
"""

import pandas as pd
import numpy as np
from typing import List, Optional

try:
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


class PerformanceGraphs:
    """Generate performance visualization graphs"""

    def __init__(self, figsize=(12, 6)):
        if not MATPLOTLIB_AVAILABLE:
            raise ImportError("matplotlib is required for visualization")
        self.figsize = figsize

    def plot_combined(self, df: pd.DataFrame, peak_bw: float,
                      title: str = "STREAM Performance", show: bool = False,
                      save_path: Optional[str] = None):
        """
        Plot bandwidth vs channels with both per-channel and total bandwidth.

        Args:
            df: Performance dataframe
            peak_bw: Peak AXI bandwidth
            title: Plot title
            show: Show plot immediately
            save_path: Path to save figure
        """
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=self.figsize)

        channels = df['Channels']
        per_channel_bw = df['BW_per_Channel_GBps']
        total_bw = df['Total_BW_GBps']
        engine_type = df['Engine_Type'].iloc[0] if 'Engine_Type' in df.columns else 'unknown'

        # Left plot: Per-channel bandwidth
        ax1.plot(channels, per_channel_bw, 'o-', linewidth=2, markersize=6,
                 color='#2E86AB', label='Per-Channel BW')
        ax1.grid(True, alpha=0.3)
        ax1.set_xlabel('Number of Channels', fontsize=11)
        ax1.set_ylabel('Bandwidth per Channel (GB/s)', fontsize=11)
        ax1.set_title(f'{title}\nPer-Channel Bandwidth ({engine_type.title()})', fontsize=12, fontweight='bold')
        ax1.legend(fontsize=10)

        # Right plot: Total bandwidth
        ax2.plot(channels, total_bw, 's-', linewidth=2, markersize=6,
                 color='#A23B72', label='Total BW')
        ax2.axhline(y=peak_bw, color='red', linestyle='--', linewidth=1.5,
                    label=f'AXI Peak ({peak_bw:.1f} GB/s)')
        ax2.grid(True, alpha=0.3)
        ax2.set_xlabel('Number of Channels', fontsize=11)
        ax2.set_ylabel('Total Bandwidth (GB/s)', fontsize=11)
        ax2.set_title(f'{title}\nTotal Bandwidth ({engine_type.title()})', fontsize=12, fontweight='bold')
        ax2.legend(fontsize=10)

        plt.tight_layout()

        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')

        if show:
            plt.show()
        else:
            plt.close()

        return fig

    def plot_read_write_separate(self, read_df: pd.DataFrame, write_df: pd.DataFrame,
                                  peak_bw: float, title: str = "STREAM Read vs Write Performance",
                                  show: bool = False, save_path: Optional[str] = None):
        """
        Plot read and write bandwidth on same axes for comparison.

        Args:
            read_df: Read engine performance dataframe
            write_df: Write engine performance dataframe
            peak_bw: Peak AXI bandwidth
            title: Plot title
            show: Show plot immediately
            save_path: Path to save figure
        """
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=self.figsize)

        channels = read_df['Channels']

        # Left plot: Per-channel bandwidth comparison
        ax1.plot(channels, read_df['BW_per_Channel_GBps'], 'o-', linewidth=2,
                 markersize=6, color='#2E86AB', label='Read Path')
        ax1.plot(channels, write_df['BW_per_Channel_GBps'], 's-', linewidth=2,
                 markersize=6, color='#A23B72', label='Write Path')
        ax1.grid(True, alpha=0.3)
        ax1.set_xlabel('Number of Channels', fontsize=11)
        ax1.set_ylabel('Bandwidth per Channel (GB/s)', fontsize=11)
        ax1.set_title(f'{title}\nPer-Channel Bandwidth', fontsize=12, fontweight='bold')
        ax1.legend(fontsize=10)

        # Right plot: Total bandwidth comparison
        ax2.plot(channels, read_df['Total_BW_GBps'], 'o-', linewidth=2,
                 markersize=6, color='#2E86AB', label='Read Path')
        ax2.plot(channels, write_df['Total_BW_GBps'], 's-', linewidth=2,
                 markersize=6, color='#A23B72', label='Write Path')
        ax2.axhline(y=peak_bw, color='red', linestyle='--', linewidth=1.5,
                    label=f'AXI Peak ({peak_bw:.1f} GB/s)')
        ax2.grid(True, alpha=0.3)
        ax2.set_xlabel('Number of Channels', fontsize=11)
        ax2.set_ylabel('Total Bandwidth (GB/s)', fontsize=11)
        ax2.set_title(f'{title}\nTotal Bandwidth', fontsize=12, fontweight='bold')
        ax2.legend(fontsize=10)

        plt.tight_layout()

        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')

        if show:
            plt.show()
        else:
            plt.close()

        return fig

    def plot_mode_comparison(self, results: dict, peak_bw: float,
                             title: str = "STREAM Performance Mode Comparison",
                             show: bool = False, save_path: Optional[str] = None):
        """
        Compare Low, Medium, High performance modes.

        Args:
            results: Dict with keys 'LOW', 'MEDIUM', 'HIGH' containing DMA tables
            peak_bw: Peak AXI bandwidth
            title: Plot title
            show: Show plot immediately
            save_path: Path to save figure
        """
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

        colors = {'LOW': '#E63946', 'MEDIUM': '#F1FAEE', 'HIGH': '#2A9D8F'}
        markers = {'LOW': 'o', 'MEDIUM': 's', 'HIGH': '^'}

        # Left plot: Read bandwidth
        for mode in ['LOW', 'MEDIUM', 'HIGH']:
            if mode in results:
                df = results[mode]
                ax1.plot(df['Channels'], df['Read_BW_GBps'],
                        marker=markers[mode], linestyle='-', linewidth=2,
                        markersize=6, color=colors[mode], label=f'{mode} Mode')

        ax1.axhline(y=peak_bw, color='red', linestyle='--', linewidth=1.5,
                    label=f'AXI Peak ({peak_bw:.1f} GB/s)', alpha=0.7)
        ax1.grid(True, alpha=0.3)
        ax1.set_xlabel('Number of Channels', fontsize=11)
        ax1.set_ylabel('Read Bandwidth (GB/s)', fontsize=11)
        ax1.set_title(f'{title}\nRead Path', fontsize=12, fontweight='bold')
        ax1.legend(fontsize=10)

        # Right plot: Write bandwidth
        for mode in ['LOW', 'MEDIUM', 'HIGH']:
            if mode in results:
                df = results[mode]
                ax2.plot(df['Channels'], df['Write_BW_GBps'],
                        marker=markers[mode], linestyle='-', linewidth=2,
                        markersize=6, color=colors[mode], label=f'{mode} Mode')

        ax2.axhline(y=peak_bw, color='red', linestyle='--', linewidth=1.5,
                    label=f'AXI Peak ({peak_bw:.1f} GB/s)', alpha=0.7)
        ax2.grid(True, alpha=0.3)
        ax2.set_xlabel('Number of Channels', fontsize=11)
        ax2.set_ylabel('Write Bandwidth (GB/s)', fontsize=11)
        ax2.set_title(f'{title}\nWrite Path', fontsize=12, fontweight='bold')
        ax2.legend(fontsize=10)

        plt.tight_layout()

        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')

        if show:
            plt.show()
        else:
            plt.close()

        return fig

    def plot_payload_sweep(self, payload_results: dict, peak_bw: float,
                           engine_type: str = "read",
                           title: str = "STREAM Payload Size Sweep",
                           show: bool = False, save_path: Optional[str] = None):
        """
        Plot performance across different payload sizes.

        Args:
            payload_results: Dict mapping payload size to dataframe
            peak_bw: Peak AXI bandwidth
            engine_type: "read" or "write"
            title: Plot title
            show: Show plot immediately
            save_path: Path to save figure
        """
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=self.figsize)

        # Color map for payloads
        payloads = sorted(payload_results.keys())
        colors = plt.cm.viridis(np.linspace(0, 1, len(payloads)))

        # Left plot: Per-channel bandwidth
        for payload, color in zip(payloads, colors):
            df = payload_results[payload]
            ax1.plot(df['Channels'], df['BW_per_Channel_GBps'],
                    marker='o', linestyle='-', linewidth=1.5,
                    markersize=4, color=color, label=f'{payload}B')

        ax1.grid(True, alpha=0.3)
        ax1.set_xlabel('Number of Channels', fontsize=11)
        ax1.set_ylabel('Bandwidth per Channel (GB/s)', fontsize=11)
        ax1.set_title(f'{title}\nPer-Channel BW ({engine_type.title()})', fontsize=12, fontweight='bold')
        ax1.legend(fontsize=9, title='Payload')

        # Right plot: Total bandwidth
        for payload, color in zip(payloads, colors):
            df = payload_results[payload]
            ax2.plot(df['Channels'], df['Total_BW_GBps'],
                    marker='o', linestyle='-', linewidth=1.5,
                    markersize=4, color=color, label=f'{payload}B')

        ax2.axhline(y=peak_bw, color='red', linestyle='--', linewidth=1.5,
                    label=f'AXI Peak ({peak_bw:.1f} GB/s)', alpha=0.7)
        ax2.grid(True, alpha=0.3)
        ax2.set_xlabel('Number of Channels', fontsize=11)
        ax2.set_ylabel('Total Bandwidth (GB/s)', fontsize=11)
        ax2.set_title(f'{title}\nTotal BW ({engine_type.title()})', fontsize=12, fontweight='bold')
        ax2.legend(fontsize=9, title='Payload')

        plt.tight_layout()

        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')

        if show:
            plt.show()
        else:
            plt.close()

        return fig
