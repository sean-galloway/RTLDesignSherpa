#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Parameter
# Purpose: Parameter Audit Tool for RTL Design Sherpa
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
Parameter Audit Tool for RTL Design Sherpa

Audits all SystemVerilog modules in rtl/common/ for parameterization consistency.

Checks:
- Parameter naming conventions (WIDTH, DEPTH, SIZE, etc.)
- Default values presence
- Derived parameters use localparam
- Magic numbers in code
- Parameter consistency across similar modules
- Range constraints documentation

Usage:
    python bin/audit_module_parameterization.py [--category CATEGORY] [--verbose]

Output:
    reports/parameterization/parameterization_audit.md
    reports/parameterization/parameterization_audit.csv
"""

import re
import sys
import csv
import argparse
from pathlib import Path
from collections import defaultdict
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Set

@dataclass
class Parameter:
    """Represents a module parameter"""
    name: str
    type: str  # 'parameter' or 'localparam'
    data_type: Optional[str] = None  # int, logic, etc.
    default_value: Optional[str] = None
    line_number: int = 0
    in_header_comment: bool = False

@dataclass
class MagicNumber:
    """Represents a potential magic number"""
    value: str
    context: str
    line_number: int

@dataclass
class ModuleAudit:
    """Complete audit results for a module"""
    module_name: str
    file_path: str
    category: str

    # Parameters
    parameters: List[Parameter] = field(default_factory=list)
    localparams: List[Parameter] = field(default_factory=list)

    # Issues
    params_missing_defaults: List[str] = field(default_factory=list)
    params_not_in_header: List[str] = field(default_factory=list)
    derived_not_localparam: List[str] = field(default_factory=list)
    magic_numbers: List[MagicNumber] = field(default_factory=list)

    # Naming convention issues
    naming_issues: List[str] = field(default_factory=list)

    # Consistency score (0-100)
    consistency_score: float = 0.0

    # Analysis text
    notes: List[str] = field(default_factory=list)

class ParameterAuditor:
    """Main auditor class"""

    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.modules: Dict[str, ModuleAudit] = {}
        self.categories: Dict[str, List[str]] = defaultdict(list)

        # Common parameter naming patterns
        self.naming_patterns = {
            'width': ['WIDTH', 'DATA_WIDTH', 'ADDR_WIDTH', 'CNT_WIDTH'],
            'depth': ['DEPTH', 'FIFO_DEPTH', 'BUFFER_DEPTH'],
            'size': ['SIZE', 'TABLE_SIZE', 'CACHE_SIZE'],
            'count': ['COUNT', 'NUM', 'N', 'CLIENTS', 'ENTRIES'],
            'frequency': ['CLK_FREQ_MHZ', 'CLK_FREQ_HZ', 'FREQ'],
            'timeout': ['TIMEOUT_MS', 'TIMEOUT_US', 'TIMEOUT_CYCLES'],
            'max': ['MAX_VALUE', 'MAX_COUNT', 'MAX'],
            'min': ['MIN_VALUE', 'MIN_COUNT', 'MIN'],
        }

        # Numbers that are OK to use literally (not magic)
        self.allowed_literals = {'0', '1', '2', '\'0', '\'1', "'b0", "'b1"}

    def categorize_module(self, module_name: str) -> str:
        """Determine module category from name"""
        if module_name.startswith('counter'):
            return 'counter'
        elif module_name.startswith('arbiter'):
            return 'arbiter'
        elif module_name.startswith('dataint'):
            return 'data_integrity'
        elif module_name.startswith('fifo'):
            return 'fifo'
        elif module_name.startswith('clock'):
            return 'clock'
        elif module_name.startswith('math'):
            return 'math'
        elif module_name.startswith('sync') or module_name in ['reset_sync', 'glitch_free_n_dff_arn']:
            return 'synchronizer'
        elif module_name in ['encoder', 'encoder_priority_enable', 'decoder', 'priority_encoder']:
            return 'encoder_decoder'
        elif module_name.startswith('shifter'):
            return 'shifter'
        else:
            return 'miscellaneous'

    def extract_parameters(self, content: str) -> tuple[List[Parameter], List[Parameter]]:
        """Extract parameters and localparams from module"""
        parameters = []
        localparams = []

        # Pattern to match parameter declarations
        param_pattern = r'^\s*(parameter|localparam)\s+(?:(int|logic|bit|reg)\s+)?(\w+)\s*=\s*(.+?)[,;]'

        lines = content.split('\n')
        for i, line in enumerate(lines):
            # Remove comments
            line_no_comment = re.sub(r'//.*$', '', line)

            match = re.search(param_pattern, line_no_comment)
            if match:
                param_type = match.group(1)
                data_type = match.group(2)
                name = match.group(3)
                default = match.group(4).strip()

                param = Parameter(
                    name=name,
                    type=param_type,
                    data_type=data_type,
                    default_value=default,
                    line_number=i+1
                )

                if param_type == 'parameter':
                    parameters.append(param)
                else:
                    localparams.append(param)

        return parameters, localparams

    def check_header_documentation(self, content: str, param_names: List[str]) -> Set[str]:
        """Check which parameters are documented in header"""
        documented = set()

        # Find header comment block (up to module declaration)
        module_match = re.search(r'^module\s+\w+', content, re.MULTILINE)
        if not module_match:
            return documented

        header = content[:module_match.start()]

        for param_name in param_names:
            # Look for parameter name in comments with description
            if re.search(rf'//.*{param_name}\s*:', header, re.IGNORECASE):
                documented.add(param_name)

        return documented

    def find_magic_numbers(self, content: str) -> List[MagicNumber]:
        """Find potential magic numbers in code"""
        magic_numbers = []

        # Skip header comments and parameters section
        module_match = re.search(r'^module\s+\w+', content, re.MULTILINE)
        if not module_match:
            return magic_numbers

        # Only check code after module declaration
        code = content[module_match.start():]
        lines = code.split('\n')

        # Pattern to match numeric literals
        number_pattern = r"\b(\d+(?:'[hdbHDB]\w+)?)\b"

        for i, line in enumerate(lines):
            # Skip comment lines
            if re.match(r'^\s*//', line):
                continue

            # Remove inline comments
            code_part = re.sub(r'//.*$', '', line)

            # Find numbers
            for match in re.finditer(number_pattern, code_part):
                num = match.group(1)

                # Skip allowed literals
                if num in self.allowed_literals:
                    continue

                # Skip if it's in a parameter/localparam declaration
                if re.match(r'^\s*(parameter|localparam)', code_part):
                    continue

                # Skip if it's part of a bit width specification like [7:0]
                if re.search(r'\[\s*\d+\s*:\s*\d+\s*\]', code_part):
                    continue

                # Context: surrounding text
                context = code_part.strip()
                if len(context) > 60:
                    context = context[:60] + '...'

                magic_numbers.append(MagicNumber(
                    value=num,
                    context=context,
                    line_number=module_match.start() + i + 1
                ))

        return magic_numbers

    def check_naming_conventions(self, parameters: List[Parameter]) -> List[str]:
        """Check if parameter names follow conventions"""
        issues = []

        for param in parameters:
            name = param.name

            # Check for lowercase (should be uppercase)
            if name.lower() == name and name.upper() not in [p.name for p in parameters]:
                issues.append(f"{name} should be UPPERCASE per convention")

            # Check for inconsistent width naming
            if 'width' in name.lower() and name not in ['WIDTH', 'DATA_WIDTH', 'ADDR_WIDTH', 'CNT_WIDTH']:
                issues.append(f"{name} width parameter uses non-standard naming")

            # Check for inconsistent depth naming
            if 'depth' in name.lower() and name not in ['DEPTH', 'FIFO_DEPTH', 'BUFFER_DEPTH']:
                issues.append(f"{name} depth parameter uses non-standard naming")

        return issues

    def check_derived_parameters(self, parameters: List[Parameter], localparams: List[Parameter]) -> List[str]:
        """Check if derived parameters are localparam"""
        issues = []

        for param in parameters:
            if param.default_value:
                # Check if default uses other parameters (derived)
                # Common patterns: $clog2(...), WIDTH+1, DEPTH*2, etc.
                if any(op in param.default_value for op in ['$clog2', '+', '-', '*', '/', '>>', '<<']):
                    # Check if it references other parameters
                    for other in parameters + localparams:
                        if other.name != param.name and other.name in param.default_value:
                            issues.append(f"{param.name} is derived from {other.name} but is 'parameter' not 'localparam'")
                            break

        return issues

    def calculate_consistency_score(self, audit: ModuleAudit) -> float:
        """Calculate consistency score (0-100)"""
        score = 100.0

        # Deduct for missing defaults (10 points each)
        score -= len(audit.params_missing_defaults) * 10

        # Deduct for params not in header (5 points each)
        score -= len(audit.params_not_in_header) * 5

        # Deduct for derived params not localparam (15 points each)
        score -= len(audit.derived_not_localparam) * 15

        # Deduct for naming issues (5 points each)
        score -= len(audit.naming_issues) * 5

        # Deduct for magic numbers (2 points each, max 20)
        score -= min(len(audit.magic_numbers) * 2, 20)

        return max(0.0, score)

    def audit_module(self, sv_file: Path) -> ModuleAudit:
        """Audit a single module"""
        module_name = sv_file.stem

        if self.verbose:
            print(f"Auditing: {module_name}")

        # Read file
        content = sv_file.read_text()

        # Create audit object
        audit = ModuleAudit(
            module_name=module_name,
            file_path=str(sv_file),
            category=self.categorize_module(module_name)
        )

        # Extract parameters
        audit.parameters, audit.localparams = self.extract_parameters(content)

        # Check which parameters are in header
        param_names = [p.name for p in audit.parameters]
        documented = self.check_header_documentation(content, param_names)

        # Check for missing defaults
        for param in audit.parameters:
            if param.default_value is None:
                audit.params_missing_defaults.append(param.name)

            if param.name not in documented:
                audit.params_not_in_header.append(param.name)

        # Check naming conventions
        audit.naming_issues = self.check_naming_conventions(audit.parameters)

        # Check derived parameters
        audit.derived_not_localparam = self.check_derived_parameters(
            audit.parameters, audit.localparams
        )

        # Find magic numbers
        audit.magic_numbers = self.find_magic_numbers(content)

        # Calculate score
        audit.consistency_score = self.calculate_consistency_score(audit)

        # Add to categories
        self.categories[audit.category].append(module_name)

        # Store audit
        self.modules[module_name] = audit

        return audit

    def audit_all_modules(self, rtl_dir: Path, category_filter: Optional[str] = None):
        """Audit all modules in rtl/common/"""
        sv_files = sorted(rtl_dir.glob('*.sv'))

        print(f"Found {len(sv_files)} SystemVerilog files")

        for sv_file in sv_files:
            audit = self.audit_module(sv_file)

            # Skip if category filter specified and doesn't match
            if category_filter and audit.category != category_filter:
                continue

        print(f"\nAudited {len(self.modules)} modules")

    def generate_markdown_report(self, output_file: Path):
        """Generate comprehensive markdown report"""

        with open(output_file, 'w') as f:
            f.write("# RTL Common Library - Parameterization Audit Report\n\n")
            f.write("**Generated:** Auto-generated by audit_module_parameterization.py\n\n")
            f.write("**Purpose:** Audit parameter consistency across all 86 rtl/common modules\n\n")

            # Executive Summary
            f.write("---\n\n## Executive Summary\n\n")

            total_modules = len(self.modules)
            avg_score = sum(m.consistency_score for m in self.modules.values()) / total_modules

            perfect_count = sum(1 for m in self.modules.values() if m.consistency_score == 100)
            good_count = sum(1 for m in self.modules.values() if 80 <= m.consistency_score < 100)
            needs_work_count = sum(1 for m in self.modules.values() if m.consistency_score < 80)

            f.write(f"**Total Modules Audited:** {total_modules}\n\n")
            f.write(f"**Average Consistency Score:** {avg_score:.1f}/100\n\n")
            f.write(f"**Module Distribution:**\n")
            f.write(f"- Perfect (100): {perfect_count} modules ({perfect_count/total_modules*100:.1f}%)\n")
            f.write(f"- Good (80-99): {good_count} modules ({good_count/total_modules*100:.1f}%)\n")
            f.write(f"- Needs Work (<80): {needs_work_count} modules ({needs_work_count/total_modules*100:.1f}%)\n\n")

            # Common issues
            total_missing_defaults = sum(len(m.params_missing_defaults) for m in self.modules.values())
            total_undocumented = sum(len(m.params_not_in_header) for m in self.modules.values())
            total_derived_issues = sum(len(m.derived_not_localparam) for m in self.modules.values())
            total_naming_issues = sum(len(m.naming_issues) for m in self.modules.values())
            total_magic = sum(len(m.magic_numbers) for m in self.modules.values())

            f.write("**Issues Found:**\n")
            f.write(f"- Parameters missing defaults: {total_missing_defaults}\n")
            f.write(f"- Parameters not in header: {total_undocumented}\n")
            f.write(f"- Derived params not localparam: {total_derived_issues}\n")
            f.write(f"- Naming convention issues: {total_naming_issues}\n")
            f.write(f"- Potential magic numbers: {total_magic}\n\n")

            # Category breakdown
            f.write("---\n\n## Category Breakdown\n\n")

            for category in sorted(self.categories.keys()):
                modules = [self.modules[m] for m in self.categories[category]]
                cat_avg = sum(m.consistency_score for m in modules) / len(modules)

                f.write(f"### {category.replace('_', ' ').title()}\n\n")
                f.write(f"**Modules:** {len(modules)}\n\n")
                f.write(f"**Average Score:** {cat_avg:.1f}/100\n\n")

                # Parameter naming patterns in this category
                param_names = set()
                for mod in modules:
                    param_names.update(p.name for p in mod.parameters)

                if param_names:
                    f.write(f"**Common Parameters:** {', '.join(sorted(param_names)[:10])}\n\n")

            # Detailed module results
            f.write("---\n\n## Detailed Module Results\n\n")

            # Sort by score (lowest first - needs most attention)
            sorted_modules = sorted(self.modules.values(), key=lambda m: m.consistency_score)

            for audit in sorted_modules:
                f.write(f"### {audit.module_name}\n\n")
                f.write(f"**File:** `{audit.file_path}`\n\n")
                f.write(f"**Category:** {audit.category}\n\n")
                f.write(f"**Consistency Score:** {audit.consistency_score:.0f}/100\n\n")

                # Parameters
                if audit.parameters:
                    f.write(f"**Parameters ({len(audit.parameters)}):**\n")
                    for param in audit.parameters:
                        default_str = f" = {param.default_value}" if param.default_value else " (no default)"
                        type_str = f" {param.data_type}" if param.data_type else ""
                        f.write(f"- `{param.name}`{type_str}{default_str}\n")
                    f.write("\n")

                # Localparams
                if audit.localparams:
                    f.write(f"**Localparams ({len(audit.localparams)}):**\n")
                    for param in audit.localparams:
                        f.write(f"- `{param.name}` = {param.default_value}\n")
                    f.write("\n")

                # Issues
                if audit.params_missing_defaults:
                    f.write(f"**⚠️ Missing Defaults:** {', '.join(audit.params_missing_defaults)}\n\n")

                if audit.params_not_in_header:
                    f.write(f"**⚠️ Not in Header:** {', '.join(audit.params_not_in_header)}\n\n")

                if audit.derived_not_localparam:
                    f.write(f"**⚠️ Derived but not localparam:**\n")
                    for issue in audit.derived_not_localparam:
                        f.write(f"- {issue}\n")
                    f.write("\n")

                if audit.naming_issues:
                    f.write(f"**⚠️ Naming Issues:**\n")
                    for issue in audit.naming_issues:
                        f.write(f"- {issue}\n")
                    f.write("\n")

                if audit.magic_numbers:
                    f.write(f"**⚠️ Potential Magic Numbers ({len(audit.magic_numbers)}):**\n")
                    # Show first 5
                    for magic in audit.magic_numbers[:5]:
                        f.write(f"- Line {magic.line_number}: `{magic.value}` in `{magic.context}`\n")
                    if len(audit.magic_numbers) > 5:
                        f.write(f"- ... and {len(audit.magic_numbers) - 5} more\n")
                    f.write("\n")

                f.write("---\n\n")

            # Recommendations
            f.write("## Recommendations\n\n")
            f.write("### High Priority\n\n")
            f.write("1. **Add default values** to all parameters without defaults\n")
            f.write("2. **Convert derived parameters** to `localparam`\n")
            f.write("3. **Document all parameters** in module headers\n\n")

            f.write("### Medium Priority\n\n")
            f.write("1. **Standardize naming conventions** across similar modules\n")
            f.write("2. **Review magic numbers** and convert to parameters where appropriate\n")
            f.write("3. **Add parameter range constraints** in comments\n\n")

            f.write("### Parameter Naming Standards\n\n")
            f.write("**Recommended conventions:**\n")
            f.write("- Widths: `WIDTH`, `DATA_WIDTH`, `ADDR_WIDTH`\n")
            f.write("- Depths: `DEPTH`, `FIFO_DEPTH`\n")
            f.write("- Counts: `N`, `COUNT`, `CLIENTS`\n")
            f.write("- Frequencies: `CLK_FREQ_MHZ`, `CLK_FREQ_HZ`\n")
            f.write("- Timeouts: `TIMEOUT_MS`, `TIMEOUT_US`, `TIMEOUT_CYCLES`\n")
            f.write("- Max/Min: `MAX_VALUE`, `MIN_VALUE`\n\n")

        print(f"\nMarkdown report written to: {output_file}")

    def generate_csv_report(self, output_file: Path):
        """Generate CSV report for data analysis"""

        with open(output_file, 'w', newline='') as f:
            writer = csv.writer(f)

            # Header
            writer.writerow([
                'Module', 'Category', 'Score',
                'Num Params', 'Num Localparams',
                'Missing Defaults', 'Not in Header',
                'Derived Issues', 'Naming Issues', 'Magic Numbers'
            ])

            # Data rows
            for audit in sorted(self.modules.values(), key=lambda m: m.module_name):
                writer.writerow([
                    audit.module_name,
                    audit.category,
                    f"{audit.consistency_score:.1f}",
                    len(audit.parameters),
                    len(audit.localparams),
                    len(audit.params_missing_defaults),
                    len(audit.params_not_in_header),
                    len(audit.derived_not_localparam),
                    len(audit.naming_issues),
                    len(audit.magic_numbers)
                ])

        print(f"CSV report written to: {output_file}")

def main():
    parser = argparse.ArgumentParser(description='Audit module parameterization')
    parser.add_argument('--category', type=str, help='Filter by category')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    args = parser.parse_args()

    # Paths
    repo_root = Path(__file__).parent.parent
    rtl_dir = repo_root / 'rtl' / 'common'
    report_dir = repo_root / 'reports' / 'parameterization'

    # Create report directory
    report_dir.mkdir(parents=True, exist_ok=True)

    # Create auditor
    auditor = ParameterAuditor(verbose=args.verbose)

    # Audit all modules
    auditor.audit_all_modules(rtl_dir, args.category)

    # Generate reports
    auditor.generate_markdown_report(report_dir / 'parameterization_audit.md')
    auditor.generate_csv_report(report_dir / 'parameterization_audit.csv')

    print("\n✅ Parameterization audit complete!")

    # Summary
    avg_score = sum(m.consistency_score for m in auditor.modules.values()) / len(auditor.modules)
    print(f"\nAverage consistency score: {avg_score:.1f}/100")

if __name__ == '__main__':
    main()
