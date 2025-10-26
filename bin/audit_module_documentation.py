#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DocStatus
# Purpose: Module Documentation Audit Script
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
Module Documentation Audit Script

Analyzes all SystemVerilog modules in rtl/common/ and checks for:
- Module description
- Parameter documentation
- Port documentation
- Usage notes
- Related modules references
- Test file location

Generates a CSV report and categorizes modules by documentation completeness.
"""

import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple
from dataclasses import dataclass

@dataclass
class DocStatus:
    """Documentation status for a module"""
    module_name: str
    file_path: str
    has_module_desc: bool = False
    has_param_docs: bool = False
    has_port_docs: bool = False
    has_usage_notes: bool = False
    has_related_modules: bool = False
    has_test_ref: bool = False
    param_count: int = 0
    port_count: int = 0
    score: float = 0.0

    def calculate_score(self):
        """Calculate documentation completeness score (0-100)"""
        checks = [
            self.has_module_desc,
            self.has_param_docs if self.param_count > 0 else True,  # N/A if no params
            self.has_port_docs,
            self.has_usage_notes,
            self.has_related_modules,
            self.has_test_ref
        ]
        self.score = (sum(checks) / len(checks)) * 100
        return self.score


class ModuleDocAuditor:
    """Audits SystemVerilog module documentation"""

    def __init__(self, rtl_dir: Path):
        self.rtl_dir = rtl_dir
        self.results: List[DocStatus] = []

    def audit_all(self) -> List[DocStatus]:
        """Audit all .sv files in rtl_dir"""
        sv_files = sorted(self.rtl_dir.glob("*.sv"))

        for sv_file in sv_files:
            # Skip testcode
            if "testcode" in str(sv_file):
                continue

            status = self.audit_file(sv_file)
            if status:
                self.results.append(status)

        return self.results

    def audit_file(self, file_path: Path) -> DocStatus:
        """Audit a single module file"""
        try:
            content = file_path.read_text()
        except Exception as e:
            print(f"Error reading {file_path}: {e}", file=sys.stderr)
            return None

        # Extract module name
        module_match = re.search(r'^\s*module\s+(\w+)', content, re.MULTILINE)
        if not module_match:
            return None

        module_name = module_match.group(1)
        status = DocStatus(module_name=module_name, file_path=str(file_path.relative_to(file_path.parent.parent)))

        # Extract header comment block (before module declaration)
        header_end = module_match.start()
        header = content[:header_end]

        # Count parameters
        param_matches = re.findall(r'parameter\s+(?:int\s+)?(\w+)', content[:module_match.end() + 500])
        status.param_count = len(param_matches)

        # Count ports (rough estimate)
        port_matches = re.findall(r'(?:input|output|inout)\s+', content[module_match.start():module_match.end() + 1000])
        status.port_count = len(port_matches)

        # Check for documentation elements
        status.has_module_desc = self._check_module_description(header)
        status.has_param_docs = self._check_parameter_docs(header, status.param_count)
        status.has_port_docs = self._check_port_docs(header)
        status.has_usage_notes = self._check_usage_notes(header)
        status.has_related_modules = self._check_related_modules(header)
        status.has_test_ref = self._check_test_reference(header, module_name)

        status.calculate_score()
        return status

    def _check_module_description(self, header: str) -> bool:
        """Check if module has a description"""
        patterns = [
            r'//\s*Description:',
            r'//\s*Module:.*\n//\s*Description:',
            r'//.*\bpurpose\b',
            r'//.*\bfunctionality\b'
        ]
        return any(re.search(pattern, header, re.IGNORECASE) for pattern in patterns)

    def _check_parameter_docs(self, header: str, param_count: int) -> bool:
        """Check if parameters are documented"""
        if param_count == 0:
            return True  # N/A

        patterns = [
            r'//\s*Parameters?:',
            r'//\s*-\s*\w+\s*:.*(?:range|default)',
        ]
        return any(re.search(pattern, header, re.IGNORECASE) for pattern in patterns)

    def _check_port_docs(self, header: str) -> bool:
        """Check if ports are documented"""
        patterns = [
            r'//\s*Ports?:',
            r'//\s*(?:Inputs?|Outputs?):',
            r'//\s*-\s*[io]_\w+\s*:',
        ]
        return any(re.search(pattern, header, re.IGNORECASE) for pattern in patterns)

    def _check_usage_notes(self, header: str) -> bool:
        """Check if usage notes are present"""
        patterns = [
            r'//\s*Notes?:',
            r'//\s*Usage:',
            r'//\s*(?:Constraints?|Limitations?):',
        ]
        return any(re.search(pattern, header, re.IGNORECASE) for pattern in patterns)

    def _check_related_modules(self, header: str) -> bool:
        """Check if related modules are referenced"""
        patterns = [
            r'//\s*Related:',
            r'//\s*See also:',
            r'//.*\.sv',  # References to other .sv files
        ]
        return any(re.search(pattern, header, re.IGNORECASE) for pattern in patterns)

    def _check_test_reference(self, header: str, module_name: str) -> bool:
        """Check if test file is referenced"""
        patterns = [
            r'//\s*Test:',
            r'//.*test_' + module_name,
            r'//.*val/common',
        ]
        return any(re.search(pattern, header, re.IGNORECASE) for pattern in patterns)

    def generate_report(self) -> str:
        """Generate markdown report"""
        if not self.results:
            return "No modules found."

        # Sort by score (ascending - worst first)
        sorted_results = sorted(self.results, key=lambda x: x.score)

        # Statistics
        total = len(self.results)
        excellent = sum(1 for r in self.results if r.score >= 90)
        good = sum(1 for r in self.results if 70 <= r.score < 90)
        fair = sum(1 for r in self.results if 50 <= r.score < 70)
        poor = sum(1 for r in self.results if r.score < 50)
        avg_score = sum(r.score for r in self.results) / total

        report = []
        report.append("# Module Documentation Audit Report")
        report.append("")
        report.append(f"**Total Modules:** {total}")
        report.append(f"**Average Score:** {avg_score:.1f}%")
        report.append("")
        report.append("## Summary")
        report.append("")
        report.append("| Category | Count | Percentage |")
        report.append("|----------|-------|------------|")
        report.append(f"| Excellent (90-100%) | {excellent} | {excellent/total*100:.1f}% |")
        report.append(f"| Good (70-89%) | {good} | {good/total*100:.1f}% |")
        report.append(f"| Fair (50-69%) | {fair} | {fair/total*100:.1f}% |")
        report.append(f"| Poor (<50%) | {poor} | {poor/total*100:.1f}% |")
        report.append("")

        # Detailed results
        report.append("## Detailed Results")
        report.append("")
        report.append("| Module | Score | Desc | Params | Ports | Notes | Related | Test |")
        report.append("|--------|-------|------|--------|-------|-------|---------|------|")

        for r in sorted_results:
            desc_mark = "✅" if r.has_module_desc else "❌"
            param_mark = "✅" if r.has_param_docs else ("N/A" if r.param_count == 0 else "❌")
            port_mark = "✅" if r.has_port_docs else "❌"
            notes_mark = "✅" if r.has_usage_notes else "❌"
            related_mark = "✅" if r.has_related_modules else "❌"
            test_mark = "✅" if r.has_test_ref else "❌"

            report.append(f"| {r.module_name} | {r.score:.0f}% | {desc_mark} | {param_mark} | {port_mark} | {notes_mark} | {related_mark} | {test_mark} |")

        report.append("")
        report.append("## Modules Needing Attention (Score < 70%)")
        report.append("")

        needs_attention = [r for r in sorted_results if r.score < 70]
        if needs_attention:
            report.append("| Module | Score | Missing Elements |")
            report.append("|--------|-------|------------------|")

            for r in needs_attention:
                missing = []
                if not r.has_module_desc:
                    missing.append("Description")
                if not r.has_param_docs and r.param_count > 0:
                    missing.append("Param docs")
                if not r.has_port_docs:
                    missing.append("Port docs")
                if not r.has_usage_notes:
                    missing.append("Notes")
                if not r.has_related_modules:
                    missing.append("Related")
                if not r.has_test_ref:
                    missing.append("Test ref")

                report.append(f"| {r.module_name} | {r.score:.0f}% | {', '.join(missing)} |")
        else:
            report.append("**All modules meet minimum documentation standards!**")

        report.append("")
        report.append("## Legend")
        report.append("")
        report.append("- **Desc:** Module description present")
        report.append("- **Params:** Parameters documented (N/A if no parameters)")
        report.append("- **Ports:** Port descriptions present")
        report.append("- **Notes:** Usage notes/constraints documented")
        report.append("- **Related:** References to related modules")
        report.append("- **Test:** Reference to test file location")
        report.append("")

        return "\n".join(report)

    def generate_csv(self) -> str:
        """Generate CSV for detailed analysis"""
        lines = ["Module,Score,HasDesc,HasParamDocs,HasPortDocs,HasNotes,HasRelated,HasTestRef,ParamCount,PortCount"]

        for r in sorted(self.results, key=lambda x: x.module_name):
            lines.append(f"{r.module_name},{r.score:.1f},{r.has_module_desc},{r.has_param_docs},{r.has_port_docs},"
                        f"{r.has_usage_notes},{r.has_related_modules},{r.has_test_ref},{r.param_count},{r.port_count}")

        return "\n".join(lines)


def main():
    """Main entry point"""
    repo_root = Path(__file__).parent.parent
    rtl_dir = repo_root / "rtl" / "common"

    if not rtl_dir.exists():
        print(f"Error: {rtl_dir} not found", file=sys.stderr)
        sys.exit(1)

    print(f"Auditing modules in {rtl_dir}...")

    auditor = ModuleDocAuditor(rtl_dir)
    auditor.audit_all()

    # Generate reports
    report_dir = repo_root / "reports" / "documentation"
    report_dir.mkdir(parents=True, exist_ok=True)

    markdown_report = auditor.generate_report()
    csv_report = auditor.generate_csv()

    # Write reports
    md_path = report_dir / "module_documentation_audit.md"
    csv_path = report_dir / "module_documentation_audit.csv"

    md_path.write_text(markdown_report)
    csv_path.write_text(csv_report)

    print(f"\n✅ Reports generated:")
    print(f"   - {md_path}")
    print(f"   - {csv_path}")
    print(f"\n{markdown_report}")


if __name__ == "__main__":
    main()
