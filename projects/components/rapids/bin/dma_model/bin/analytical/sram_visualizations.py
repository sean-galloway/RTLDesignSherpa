# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: sram_visualizations
# Purpose: SRAM Analysis Visualization
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
SRAM Analysis Visualization

Plotting utilities for SRAM sizing analysis.
All plots are saved to the 'assets/' directory.

Usage:
    from analytical.sram_analysis import analyze_payload_vs_sram
    from analytical.sram_visualization import plot_all_sram_analysis
    
    df = analyze_payload_vs_sram()
    plot_all_sram_analysis(df)  # Saves to assets/
"""

import numpy as np
import pandas as pd
from typing import Optional, Dict, List
import os

try:
    import matplotlib.pyplot as plt
    import seaborn as sns
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


def plot_sram_efficiency(df: pd.DataFrame, 
                        payload_to_plot: Optional[int] = None,
                        save_path: Optional[str] = None):
    """
    Plot SRAM efficiency vs pipeline depth for different modes.
    
    Args:
        df: DataFrame from analyze_payload_vs_sram()
        payload_to_plot: Specific payload to plot (None = all)
        save_path: Path to save figure (in assets/)
    """
    if not MATPLOTLIB_AVAILABLE:
        print("Matplotlib not available. Cannot generate plots.")
        return
    
    if payload_to_plot:
        df = df[df['Payload_Bytes'] == payload_to_plot]
        payloads = [payload_to_plot]
    else:
        payloads = sorted(df['Payload_Bytes'].unique())
    
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    axes = axes.flatten()
    
    colors = {'pingpong': '#2E86AB', 'monolithic': '#F18F01'}
    
    for idx, payload in enumerate(payloads):
        if idx >= 4:
            break
        
        ax = axes[idx]
        subset = df[df['Payload_Bytes'] == payload]
        
        # Plot bandwidth
        ax2 = ax.twinx()
        
        for mode_name, df_col_pp, df_col_mono, color_pp, color_mono in [
            ('Ping-Pong', 'PP_SRAM_KB_per_ch', 'PP_BW_GBps', colors['pingpong'], colors['pingpong']),
            ('Monolithic', 'Mono_SRAM_KB_per_ch', 'Mono_BW_GBps', colors['monolithic'], colors['monolithic'])
        ]:
            if 'Ping-Pong' in mode_name:
                ax.plot(subset['Pipeline_Depth'], subset['PP_SRAM_KB_per_ch'], 
                       'o-', linewidth=2, markersize=6, 
                       color=color_pp, label=f'PP SRAM', alpha=0.7)
                ax2.plot(subset['Pipeline_Depth'], subset['PP_BW_GBps'],
                        's--', linewidth=2, markersize=5,
                        color=color_pp, label=f'PP BW')
            else:
                ax.plot(subset['Pipeline_Depth'], subset['Mono_SRAM_KB_per_ch'],
                       'o-', linewidth=2, markersize=6,
                       color=color_mono, label=f'Mono SRAM', alpha=0.7)
                ax2.plot(subset['Pipeline_Depth'], subset['Mono_BW_GBps'],
                        's--', linewidth=2, markersize=5,
                        color=color_mono, label=f'Mono BW')
        
        ax.set_xlabel('Pipeline Depth', fontsize=11, fontweight='bold')
        ax.set_ylabel('SRAM per Channel (KB)', fontsize=11, fontweight='bold', color='black')
        ax2.set_ylabel('Bandwidth (GB/s)', fontsize=11, fontweight='bold', color='black')
        ax.set_title(f'Payload: {payload} bytes', fontsize=12, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.legend(loc='upper left', fontsize=9)
        ax2.legend(loc='upper right', fontsize=9)
        
        # Highlight 50 GB/s target
        ax2.axhline(y=50, color='red', linestyle=':', linewidth=1.5, alpha=0.5)
    
    plt.suptitle('SRAM Requirements vs Pipeline Depth', 
                fontsize=14, fontweight='bold', y=0.995)
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Saved: {save_path}")
    
    plt.show()


def plot_sram_comparison_heatmap(df: pd.DataFrame,
                                save_path: Optional[str] = None):
    """
    Create heatmap showing which SRAM mode is better.
    
    Args:
        df: DataFrame from analyze_payload_vs_sram()
        save_path: Path to save figure (in assets/)
    """
    if not MATPLOTLIB_AVAILABLE:
        print("Matplotlib not available. Cannot generate plots.")
        return
    
    # Create pivot tables
    payloads = sorted(df['Payload_Bytes'].unique())
    depths = sorted(df['Pipeline_Depth'].unique())
    
    # Create matrices for bandwidth gain
    bw_gain_matrix = np.zeros((len(payloads), len(depths)))
    
    for i, payload in enumerate(payloads):
        for j, depth in enumerate(depths):
            row = df[(df['Payload_Bytes'] == payload) & (df['Pipeline_Depth'] == depth)]
            if not row.empty:
                bw_gain_matrix[i, j] = row.iloc[0]['BW_Gain_%']
    
    fig, ax = plt.subplots(figsize=(12, 8))
    
    # Create heatmap
    im = ax.imshow(bw_gain_matrix, cmap='RdYlGn', aspect='auto',
                   vmin=-5, vmax=max(5, bw_gain_matrix.max()),
                   origin='lower')
    
    # Set ticks
    ax.set_xticks(np.arange(len(depths)))
    ax.set_yticks(np.arange(len(payloads)))
    ax.set_xticklabels(depths)
    ax.set_yticklabels([f'{p}B' for p in payloads])
    
    # Add text annotations
    for i in range(len(payloads)):
        for j in range(len(depths)):
            value = bw_gain_matrix[i, j]
            if abs(value) < 0.1:
                text = "="
                color = "black"
            elif value > 0:
                text = f"+{value:.1f}%"
                color = "black" if value < 10 else "white"
            else:
                text = f"{value:.1f}%"
                color = "black" if abs(value) < 10 else "white"
            
            ax.text(j, i, text, ha="center", va="center", 
                   color=color, fontsize=9, fontweight='bold')
    
    ax.set_xlabel('Pipeline Depth', fontsize=13, fontweight='bold')
    ax.set_ylabel('Payload Size', fontsize=13, fontweight='bold')
    ax.set_title('Monolithic vs Ping-Pong Performance Advantage\n(Positive = Monolithic Better)',
                fontsize=14, fontweight='bold')
    
    # Add colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Bandwidth Advantage (%)', fontsize=11, fontweight='bold')
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Saved: {save_path}")
    
    plt.show()


def plot_sram_cost_benefit(df: pd.DataFrame,
                          target_bw: float = 50.0,
                          save_path: Optional[str] = None):
    """
    Plot SRAM cost vs bandwidth achieved.
    
    Args:
        df: DataFrame from analyze_payload_vs_sram()
        target_bw: Target bandwidth in GB/s
        save_path: Path to save figure (in assets/)
    """
    if not MATPLOTLIB_AVAILABLE:
        print("Matplotlib not available. Cannot generate plots.")
        return
    
    payloads = sorted(df['Payload_Bytes'].unique())
    
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    axes = axes.flatten()
    
    colors = {'pingpong': '#2E86AB', 'monolithic': '#F18F01'}
    
    for idx, payload in enumerate(payloads):
        if idx >= 4:
            break
        
        ax = axes[idx]
        subset = df[df['Payload_Bytes'] == payload]
        
        # Ping-pong: SRAM vs BW
        ax.scatter(subset['PP_Total_SRAM_KB'], subset['PP_BW_GBps'],
                  s=100, alpha=0.6, color=colors['pingpong'],
                  label='Ping-Pong', marker='o')
        
        # Monolithic: SRAM vs BW
        ax.scatter(subset['Mono_Total_SRAM_KB'], subset['Mono_BW_GBps'],
                  s=100, alpha=0.6, color=colors['monolithic'],
                  label='Monolithic', marker='s')
        
        # Connect points by pipeline depth
        for _, row in subset.iterrows():
            ax.plot([row['PP_Total_SRAM_KB'], row['Mono_Total_SRAM_KB']],
                   [row['PP_BW_GBps'], row['Mono_BW_GBps']],
                   'k-', alpha=0.2, linewidth=1)
            
            # Annotate pipeline depth
            ax.annotate(f"d={int(row['Pipeline_Depth'])}", 
                       xy=(row['PP_Total_SRAM_KB'], row['PP_BW_GBps']),
                       xytext=(5, 5), textcoords='offset points',
                       fontsize=8, alpha=0.7)
        
        # Target line
        ax.axhline(y=target_bw, color='red', linestyle='--', 
                  linewidth=2, alpha=0.5, label=f'{target_bw} GB/s target')
        
        ax.set_xlabel('Total SRAM (KB) - 16 channels', fontsize=11, fontweight='bold')
        ax.set_ylabel('Bandwidth (GB/s)', fontsize=11, fontweight='bold')
        ax.set_title(f'Payload: {payload} bytes', fontsize=12, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.legend(fontsize=9)
        ax.set_xlim(left=0)
        ax.set_ylim(bottom=0)
    
    plt.suptitle('SRAM Cost vs Performance Trade-off',
                fontsize=14, fontweight='bold', y=0.995)
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Saved: {save_path}")
    
    plt.show()


def plot_all_sram_analysis(df: pd.DataFrame, output_dir: str = 'assets'):
    """
    Generate all SRAM analysis plots.
    Saves all plots to 'assets/' directory by default.
    
    Args:
        df: DataFrame from analyze_payload_vs_sram()
        output_dir: Directory to save plots (default: 'assets')
    """
    if not MATPLOTLIB_AVAILABLE:
        print("Matplotlib not available. Cannot generate plots.")
        return
    
    # Create output directory if it doesn't exist
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
        print(f"Created directory: {output_dir}/")
    
    print(f"\nGenerating SRAM analysis plots in '{output_dir}/'...")
    
    # 1. Efficiency plots
    print("  1. SRAM efficiency vs pipeline depth...")
    plot_sram_efficiency(df, save_path=os.path.join(output_dir, 'sram_efficiency.png'))
    plt.close()
    
    # 2. Comparison heatmap
    print("  2. Mode comparison heatmap...")
    plot_sram_comparison_heatmap(df, save_path=os.path.join(output_dir, 'sram_comparison_heatmap.png'))
    plt.close()
    
    # 3. Cost-benefit
    print("  3. SRAM cost-benefit analysis...")
    plot_sram_cost_benefit(df, save_path=os.path.join(output_dir, 'sram_cost_benefit.png'))
    plt.close()
    
    print(f"\n✓ All SRAM plots generated successfully in '{output_dir}/'!")


if __name__ == "__main__":
    print("\nGenerating SRAM visualization examples...")
    print("Note: Run sram_analysis.py first to generate the data\n")
    
    try:
        # Try to load existing analysis
        df = pd.read_csv('sram_payload_analysis.csv')
        
        print("Loaded existing analysis data. Generating plots...")
        plot_all_sram_analysis(df)  # Saves to assets/ by default
        
    except FileNotFoundError:
        print("No existing data found. Run sram_analysis.py first to generate data.")
        print("\nExample usage:")
        print("  python analytical/sram_analysis.py")
        print("  python analytical/sram_visualization.py")
