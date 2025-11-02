# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PerformanceGraphs
# Purpose: Visualization classes for AXI4 Performance Analysis
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Visualization classes for AXI4 Performance Analysis
"""
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from typing import Optional, List, Tuple


class PerformanceGraphs:
    """Visualization tools for AXI4 performance analysis"""
    
    def __init__(self, style: str = "whitegrid", figsize: Tuple[int, int] = (14, 6)):
        """
        Initialize graphing environment.
        
        Args:
            style: Seaborn style ('whitegrid', 'darkgrid', 'white', 'dark', 'ticks')
            figsize: Default figure size (width, height)
        """
        sns.set_style(style)
        plt.rcParams['figure.figsize'] = figsize
        
        # Color palette
        self.colors = {
            'primary': '#2E86AB',
            'secondary': '#A23B72',
            'accent': '#F18F01',
            'success': '#06A77D',
            'warning': '#F77F00',
            'danger': '#C1121F'
        }
    
    def plot_bandwidth_scaling(self, df: pd.DataFrame, Bmax: float, 
                               title: str = "Bandwidth Scaling",
                               show: bool = True) -> plt.Figure:
        """
        Plot bandwidth vs channel count.
        
        Args:
            df: DataFrame with 'Channels' and 'Total_BW_GBps' columns
            Bmax: Peak bandwidth for reference line
            title: Plot title
            show: Whether to display plot immediately
        """
        fig, ax = plt.subplots(figsize=(12, 6))
        
        ax.plot(df['Channels'], df['Total_BW_GBps'], 'o-', 
               linewidth=2.5, markersize=6, color=self.colors['primary'],
               label='Achieved Bandwidth')
        
        ax.axhline(y=Bmax, color=self.colors['danger'], linestyle='--', 
                  linewidth=2, alpha=0.6, label=f'Peak: {Bmax:.1f} GB/s')
        
        ax.set_xlabel('Number of Concurrent Channels', fontsize=13, fontweight='bold')
        ax.set_ylabel('Bandwidth (GB/s)', fontsize=13, fontweight='bold')
        ax.set_title(title, fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.legend(fontsize=11)
        ax.set_xlim(left=0)
        ax.set_ylim(bottom=0)
        
        plt.tight_layout()
        if show:
            plt.show()
        return fig
    
    def plot_efficiency(self, df: pd.DataFrame, 
                       title: str = "Efficiency",
                       target: float = 85.0,
                       show: bool = True) -> plt.Figure:
        """
        Plot efficiency vs channel count.
        
        Args:
            df: DataFrame with 'Channels' and 'Efficiency_%' columns
            title: Plot title
            target: Target efficiency line (e.g., 85 for HBM3e)
            show: Whether to display plot immediately
        """
        fig, ax = plt.subplots(figsize=(12, 6))
        
        ax.plot(df['Channels'], df['Efficiency_%'], 'o-', 
               linewidth=2.5, markersize=6, color=self.colors['success'])
        
        ax.axhline(y=target, color=self.colors['warning'], linestyle='--', 
                  linewidth=2, alpha=0.7, label=f'{target}% Target')
        ax.axhline(y=100, color=self.colors['danger'], linestyle='--', 
                  linewidth=1.5, alpha=0.5, label='100% (Peak)')
        
        ax.set_xlabel('Number of Concurrent Channels', fontsize=13, fontweight='bold')
        ax.set_ylabel('Efficiency (%)', fontsize=13, fontweight='bold')
        ax.set_title(title, fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.legend(fontsize=11)
        ax.set_xlim(left=0)
        ax.set_ylim([0, 105])
        
        plt.tight_layout()
        if show:
            plt.show()
        return fig
    
    def plot_combined(self, df: pd.DataFrame, Bmax: float,
                     title: str = "Performance Analysis",
                     target_efficiency: float = 85.0,
                     show: bool = True) -> plt.Figure:
        """
        Plot bandwidth and efficiency side-by-side.
        
        Args:
            df: DataFrame with performance data
            Bmax: Peak bandwidth
            title: Overall title
            target_efficiency: Target efficiency percentage
            show: Whether to display plot immediately
        """
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))
        
        # Bandwidth plot
        ax1.plot(df['Channels'], df['Total_BW_GBps'], 'o-', 
                linewidth=2.5, markersize=6, color=self.colors['primary'])
        ax1.axhline(y=Bmax, color=self.colors['danger'], linestyle='--', 
                   linewidth=2, alpha=0.6, label=f'Peak: {Bmax:.1f} GB/s')
        ax1.set_xlabel('Concurrent Channels', fontsize=13, fontweight='bold')
        ax1.set_ylabel('Bandwidth (GB/s)', fontsize=13, fontweight='bold')
        ax1.set_title('Bandwidth Scaling', fontsize=14, fontweight='bold')
        ax1.grid(True, alpha=0.3)
        ax1.legend(fontsize=11)
        ax1.set_xlim(left=0)
        ax1.set_ylim(bottom=0)
        
        # Efficiency plot
        ax2.plot(df['Channels'], df['Efficiency_%'], 'o-', 
                linewidth=2.5, markersize=6, color=self.colors['success'])
        ax2.axhline(y=target_efficiency, color=self.colors['warning'], 
                   linestyle='--', linewidth=2, alpha=0.7, 
                   label=f'{target_efficiency}% Target')
        ax2.axhline(y=100, color=self.colors['danger'], linestyle='--', 
                   linewidth=1.5, alpha=0.5, label='100%')
        ax2.set_xlabel('Concurrent Channels', fontsize=13, fontweight='bold')
        ax2.set_ylabel('Efficiency (%)', fontsize=13, fontweight='bold')
        ax2.set_title('Efficiency', fontsize=14, fontweight='bold')
        ax2.grid(True, alpha=0.3)
        ax2.legend(fontsize=11)
        ax2.set_xlim(left=0)
        ax2.set_ylim([0, 105])
        
        plt.suptitle(title, fontsize=15, fontweight='bold', y=1.02)
        plt.tight_layout()
        if show:
            plt.show()
        return fig
    
    def plot_pipeline_depth_requirement(self, df: pd.DataFrame,
                                       title: str = "Pipeline Depth to Saturate",
                                       max_depth: int = 20,
                                       show: bool = True) -> plt.Figure:
        """
        Plot minimum pipeline depth needed to saturate vs channel count.
        
        Args:
            df: DataFrame from generate_pipeline_depth_table() with 'Channels' and 'Min_Pipeline_Depth'
            title: Plot title
            max_depth: Maximum depth to show on y-axis
            show: Whether to display plot immediately
        """
        fig, ax = plt.subplots(figsize=(12, 6))
        
        # Filter to achievable depths
        df_achievable = df[df['Achievable'] == True].copy()
        df_achievable = df_achievable[df_achievable['Min_Pipeline_Depth'] <= max_depth]
        
        if not df_achievable.empty:
            ax.plot(df_achievable['Channels'], df_achievable['Min_Pipeline_Depth'], 'o-',
                   linewidth=2.5, markersize=7, color=self.colors['primary'],
                   label='Min Pipeline Depth')
            
            # Add horizontal lines for common depths
            for depth in [1, 2, 4, 8]:
                if depth <= max_depth:
                    ax.axhline(y=depth, color='gray', linestyle=':', alpha=0.3, linewidth=1)
        
        # Mark unachievable region
        df_unachievable = df[df['Achievable'] == False]
        if not df_unachievable.empty:
            ax.axvspan(df_unachievable['Channels'].min(), df_unachievable['Channels'].max(),
                      alpha=0.1, color='red', label='Cannot Saturate')
        
        ax.set_xlabel('Number of Channels', fontsize=13, fontweight='bold')
        ax.set_ylabel('Minimum Pipeline Depth', fontsize=13, fontweight='bold')
        ax.set_title(title, fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.legend(fontsize=11)
        ax.set_xlim(left=0)
        ax.set_ylim([0, max_depth])
        
        # Add text annotation
        if not df_achievable.empty:
            first_sat = df_achievable.iloc[0]
            ax.annotate(f"Depth={first_sat['Min_Pipeline_Depth']:.0f}",
                       xy=(first_sat['Channels'], first_sat['Min_Pipeline_Depth']),
                       xytext=(10, 10), textcoords='offset points',
                       fontsize=10, ha='left',
                       bbox=dict(boxstyle='round,pad=0.5', fc='yellow', alpha=0.5),
                       arrowprops=dict(arrowstyle='->', connectionstyle='arc3,rad=0'))
        
        plt.tight_layout()
        if show:
            plt.show()
        return fig
    
    def plot_pipeline_depth_heatmap(self, performance_obj, 
                                   max_channels: int = 32,
                                   max_depth: int = 10,
                                   title: str = "Efficiency vs Channels & Pipeline Depth",
                                   show: bool = True) -> plt.Figure:
        """
        Create heatmap showing efficiency for different channel counts and pipeline depths.
        
        Args:
            performance_obj: AXI4Performance object
            max_channels: Maximum number of channels
            max_depth: Maximum pipeline depth
            title: Plot title
            show: Whether to display plot immediately
        """
        # Generate efficiency matrix
        efficiency_matrix = np.zeros((max_depth, max_channels))
        
        for depth in range(1, max_depth + 1):
            for channels in range(1, max_channels + 1):
                perf = performance_obj.calculate_channel_bandwidth(channels, pipeline_depth=depth)
                efficiency_matrix[depth-1, channels-1] = perf['efficiency']
        
        # Create heatmap
        fig, ax = plt.subplots(figsize=(14, 8))
        
        im = ax.imshow(efficiency_matrix, cmap='RdYlGn', aspect='auto', 
                      vmin=0, vmax=100, origin='lower',
                      extent=[0.5, max_channels+0.5, 0.5, max_depth+0.5])
        
        # Add colorbar
        cbar = plt.colorbar(im, ax=ax, label='Efficiency (%)')
        
        # Add contour line at saturation (100%)
        contour = ax.contour(range(1, max_channels+1), range(1, max_depth+1), 
                            efficiency_matrix, levels=[99.9], colors='blue', 
                            linewidths=3, linestyles='solid')
        ax.clabel(contour, inline=True, fontsize=10, fmt='Saturated')
        
        ax.set_xlabel('Number of Channels', fontsize=13, fontweight='bold')
        ax.set_ylabel('Pipeline Depth', fontsize=13, fontweight='bold')
        ax.set_title(title, fontsize=14, fontweight='bold')
        ax.set_xticks(range(2, max_channels+1, 2))
        ax.set_yticks(range(1, max_depth+1))
        
        plt.tight_layout()
        if show:
            plt.show()
        return fig
    
    def plot_mixed(self, df: pd.DataFrame, Bmax: float,
                  title: str = "Mixed 50/50 Performance",
                  target_efficiency: float = 85.0,
                  show: bool = True) -> plt.Figure:
        """
        Plot mixed read/write performance.
        
        Args:
            df: DataFrame with 'Read_BW_GBps', 'Write_BW_GBps', 'Combined_BW_GBps'
            Bmax: Peak aggregate bandwidth
            title: Overall title
            target_efficiency: Target efficiency percentage
            show: Whether to display plot immediately
        """
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))
        
        # Bandwidth plot
        ax1.plot(df['Channels'], df['Read_BW_GBps'], 'o-', 
                label='Read BW', linewidth=2.5, markersize=6, 
                color=self.colors['primary'])
        ax1.plot(df['Channels'], df['Write_BW_GBps'], 's-', 
                label='Write BW', linewidth=2.5, markersize=6, 
                color=self.colors['secondary'])
        ax1.plot(df['Channels'], df['Combined_BW_GBps'], '^-', 
                label='Combined BW', linewidth=3, markersize=8, 
                color=self.colors['accent'])
        ax1.axhline(y=Bmax, color=self.colors['danger'], linestyle='--', 
                   linewidth=2, alpha=0.5, label=f'Peak: {Bmax:.1f} GB/s')
        
        ax1.set_xlabel('Concurrent Channels', fontsize=13, fontweight='bold')
        ax1.set_ylabel('Bandwidth (GB/s)', fontsize=13, fontweight='bold')
        ax1.set_title('Bandwidth Scaling', fontsize=14, fontweight='bold')
        ax1.grid(True, alpha=0.3)
        ax1.legend(fontsize=11)
        ax1.set_xlim(left=0)
        ax1.set_ylim(bottom=0)
        
        # Efficiency plot
        ax2.plot(df['Channels'], df['Efficiency_%'], 'o-', 
                linewidth=2.5, markersize=6, color=self.colors['success'])
        ax2.axhline(y=target_efficiency, color=self.colors['warning'], 
                   linestyle='--', linewidth=2, alpha=0.7, 
                   label=f'{target_efficiency}% Target')
        ax2.axhline(y=100, color=self.colors['danger'], linestyle='--', 
                   linewidth=1.5, alpha=0.5, label='100%')
        ax2.set_xlabel('Concurrent Channels', fontsize=13, fontweight='bold')
        ax2.set_ylabel('Efficiency (%)', fontsize=13, fontweight='bold')
        ax2.set_title('Efficiency', fontsize=14, fontweight='bold')
        ax2.grid(True, alpha=0.3)
        ax2.legend(fontsize=11)
        ax2.set_xlim(left=0)
        ax2.set_ylim([0, 105])
        
        plt.suptitle(title, fontsize=15, fontweight='bold', y=1.02)
        plt.tight_layout()
        if show:
            plt.show()
        return fig
    
    def plot_comparison(self, dfs: List[pd.DataFrame], 
                       labels: List[str],
                       Bmax: float,
                       title: str = "Configuration Comparison",
                       show: bool = True) -> plt.Figure:
        """
        Compare multiple configurations.
        
        Args:
            dfs: List of DataFrames to compare
            labels: Labels for each configuration
            Bmax: Peak bandwidth reference
            title: Plot title
            show: Whether to display plot immediately
        """
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))
        
        colors = [self.colors['primary'], self.colors['secondary'], 
                 self.colors['accent'], self.colors['success']]
        
        # Bandwidth comparison
        for i, (df, label) in enumerate(zip(dfs, labels)):
            ax1.plot(df['Channels'], df['Total_BW_GBps'], 'o-', 
                    label=label, linewidth=2.5, markersize=6, 
                    color=colors[i % len(colors)])
        
        ax1.axhline(y=Bmax, color=self.colors['danger'], linestyle='--', 
                   linewidth=2, alpha=0.5, label=f'Peak: {Bmax:.1f} GB/s')
        ax1.set_xlabel('Channels', fontsize=13, fontweight='bold')
        ax1.set_ylabel('Bandwidth (GB/s)', fontsize=13, fontweight='bold')
        ax1.set_title('Bandwidth Comparison', fontsize=14, fontweight='bold')
        ax1.grid(True, alpha=0.3)
        ax1.legend(fontsize=10)
        ax1.set_xlim(left=0)
        
        # Efficiency comparison
        for i, (df, label) in enumerate(zip(dfs, labels)):
            ax2.plot(df['Channels'], df['Efficiency_%'], 'o-', 
                    label=label, linewidth=2.5, markersize=6, 
                    color=colors[i % len(colors)])
        
        ax2.axhline(y=85, color=self.colors['warning'], linestyle='--', 
                   linewidth=2, alpha=0.7, label='85% Target')
        ax2.set_xlabel('Channels', fontsize=13, fontweight='bold')
        ax2.set_ylabel('Efficiency (%)', fontsize=13, fontweight='bold')
        ax2.set_title('Efficiency Comparison', fontsize=14, fontweight='bold')
        ax2.grid(True, alpha=0.3)
        ax2.legend(fontsize=10)
        ax2.set_xlim(left=0)
        ax2.set_ylim([0, 105])
        
        plt.suptitle(title, fontsize=15, fontweight='bold', y=1.02)
        plt.tight_layout()
        if show:
            plt.show()
        return fig
    
    def plot_buffering_requirements(self, df: pd.DataFrame,
                                   title: str = "SRAM Requirements",
                                   show: bool = True) -> plt.Figure:
        """
        Plot SRAM buffering requirements vs channel count.
        
        Args:
            df: DataFrame with 'Total_SRAM_KB' column
            title: Plot title
            show: Whether to display plot immediately
        """
        fig, ax = plt.subplots(figsize=(12, 6))
        
        ax.plot(df['Channels'], df['Total_SRAM_KB'], 'o-', 
               linewidth=2.5, markersize=6, color=self.colors['accent'])
        
        ax.set_xlabel('Number of Concurrent Channels', fontsize=13, fontweight='bold')
        ax.set_ylabel('Total SRAM (KB)', fontsize=13, fontweight='bold')
        ax.set_title(title, fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.set_xlim(left=0)
        ax.set_ylim(bottom=0)
        
        plt.tight_layout()
        if show:
            plt.show()
        return fig
    
    def print_summary(self, df: pd.DataFrame, config_name: str = "Configuration"):
        """
        Print a text summary of performance results.
        
        Args:
            df: Performance DataFrame
            config_name: Name of the configuration
        """
        print("\n" + "="*70)
        print(f"  {config_name.upper()} - PERFORMANCE SUMMARY")
        print("="*70)
        
        # First channel
        first = df.iloc[0]
        print(f"\n  Single Channel Performance:")
        print(f"    Bandwidth:   {first['Total_BW_GBps']:.3f} GB/s")
        print(f"    Efficiency:  {first['Efficiency_%']:.2f}%")
        
        # Saturation point
        saturated = df[df['Saturated'] == True]
        if not saturated.empty:
            sat = saturated.iloc[0]
            print(f"\n  Saturation Point:")
            print(f"    Channels:    {sat['Channels']}")
            print(f"    Bandwidth:   {sat['Total_BW_GBps']:.3f} GB/s")
            print(f"    Efficiency:  {sat['Efficiency_%']:.2f}%")
            if 'Pipeline_Depth' in sat:
                print(f"    Pipeline:    {sat['Pipeline_Depth']} deep")
        
        # Maximum analyzed
        last = df.iloc[-1]
        print(f"\n  At {last['Channels']} Channels:")
        print(f"    Bandwidth:   {last['Total_BW_GBps']:.3f} GB/s")
        print(f"    Efficiency:  {last['Efficiency_%']:.2f}%")
        
        if 'Total_SRAM_KB' in df.columns:
            print(f"    SRAM:        {last['Total_SRAM_KB']:.2f} KB")
        
        print("="*70 + "\n")
