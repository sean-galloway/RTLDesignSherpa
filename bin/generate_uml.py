#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: generate_uml
# Purpose: UML Diagram Generation Tool using py2puml.
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
UML Diagram Generation Tool using py2puml.

Generates PlantUML class diagrams for an entire Python project, each top-level package, 
and each individual Python module (file). Saves .puml files under a 'puml/' directory, 
and optionally renders them to .png and .svg images in 'puml_img/' if PlantUML CLI is available.

Usage:
    python generate_uml.py [project_root] [--base-module NAME]

If no project_root is given, defaults to "./CocoTBFramework". The base module name (for UML naming) 
defaults to the project directory name if not provided.
"""
import os
import sys
import shutil
import subprocess
import argparse

# Ensure py2puml is available
try:
    from py2puml.py2puml import py2puml
except ImportError:
    print("ERROR: py2puml is not installed. Please install py2puml to use this tool.")
    sys.exit(1)

def filter_lines_for_module(lines, modulename):
    """
    Filter py2puml output lines to include only class/enum definitions and relations for the given modulename.
    Excludes relations involving classes from other modules. Used to isolate per-file UML content.
    """
    filtered = []
    including_block = False  # True when inside a class/enum block belonging to modulename
    for line in lines:
        stripped = line.strip()
        if not stripped:
            continue  # skip empty lines

        # Stop if we reached the UML footer or end marker
        if stripped.startswith("footer") or stripped.startswith("@enduml"):
            break

        if not including_block:

            # Check if this line starts a class or enum definition for our modulename
            if stripped.startswith("class ") or stripped.startswith("enum "):
                
                # Extract fully qualified name (FQN) of the class/enum
                keyword = "class " if stripped.startswith("class ") else "enum "
                fqn = stripped[len(keyword):]

                # Remove trailing "{" (if present) and extra spaces
                if fqn.endswith("{"):
                    fqn = fqn[:-1].strip()
                else:
                    # If "{" is on the next line (unlikely with py2puml), take the first token as FQN
                    fqn = fqn.split()[0]

                # Determine the module portion of the FQN (everything up to the last dot)
                module_of_line = fqn.rsplit(".", 1)[0] if "." in fqn else ""
                if module_of_line == modulename:
                    # This definition belongs to the target module (file)
                    including_block = True
                    filtered.append(line)
                    continue

            # If not a class/enum of our module, check if it's a relation line
            if "--" in line:
                # Identify relation arrow type (composition or inheritance)
                if "<|--" in line:
                    sep = "<|--"
                elif "*--" in line:
                    sep = "*--"
                else:
                    sep = "--"
                parts = line.split(sep)
                if len(parts) == 2:
                    src = parts[0].strip()
                    tgt = parts[1].strip()
                    # Clean up any residual arrow symbols 
                    if src.endswith("<|") or src.endswith("*") or src.endswith("o") or src.endswith("x"):
                        src = src[:-1].strip()
                    if tgt.startswith("|"):
                        tgt = tgt[1:].strip()
                    # Determine source and target modules
                    src_mod = src.rsplit(".", 1)[0] if "." in src else ""
                    tgt_mod = tgt.rsplit(".", 1)[0] if "." in tgt else ""
                    if src_mod == modulename and tgt_mod == modulename:
                        filtered.append(line)
                        # (We include the relation only if both sides are in this file's module)
                        continue
            # Other lines (e.g., pragma directives) are skipped at this point
        else:
            # We are inside a class/enum block for our modulename
            filtered.append(line)
            if stripped == "}":
                # End of class/enum definition
                including_block = False
    return filtered

def main():  # sourcery skip: use-next
    # Parse arguments for project root directory and base module name
    parser = argparse.ArgumentParser(description="Generate UML class diagrams from a Python codebase using py2puml.")
    parser.add_argument("root_dir", nargs="?", default="CocoTBFramework",
                        help="Root directory of the Python project (default: 'CocoTBFramework').")
    parser.add_argument("-b", "--base-module", dest="base_module", help="Base Python module name (default: derive from root directory name).")
    args = parser.parse_args()
    root_dir = args.root_dir
    base_module = args.base_module if args.base_module else os.path.basename(os.path.normpath(root_dir))

    # Validate root directory
    if not os.path.isdir(root_dir):
        print(f"ERROR: Directory '{root_dir}' does not exist.")
        sys.exit(1)

    # Prepare output directories
    puml_dir = os.path.join(root_dir, "puml")
    puml_img_dir = os.path.join(root_dir, "puml_img")
    os.makedirs(puml_dir, exist_ok=True)
    os.makedirs(puml_img_dir, exist_ok=True)

    # (Optional) Clean old outputs to remove stale files
    for fname in os.listdir(puml_dir):
        if fname.endswith(".puml"):
            os.remove(os.path.join(puml_dir, fname))

    for fname in os.listdir(puml_img_dir):
        if fname.endswith(".png") or fname.endswith(".svg"):
            os.remove(os.path.join(puml_img_dir, fname))

    # Discover all python files and top-level packages
    top_level_packages = []
    all_py_files = []
    ignore_dirs = {"puml", "puml_img", "__pycache__", ".git", ".hg", ".svn", ".idea", "venv", "env"}

    for root, dirs, files in os.walk(root_dir):
        # Prune ignored directories from traversal
        dirs[:] = [d for d in dirs if d not in ignore_dirs]

        # Record top-level package names (direct subdirs of root)
        if root == root_dir:
            top_level_packages.extend(
                d
                for d in dirs
                if not d.startswith(".") and d not in ignore_dirs
            )
        # Record all .py files
        for fname in files:
            if fname.endswith(".py"):
                full_path = os.path.join(root, fname)
                all_py_files.append(full_path)

    # Generate UML for the entire project
    print(f"Generating UML for entire project '{base_module}'...")
    uml_lines = list(py2puml(root_dir, base_module))

    # Insert directives to hide member details for the full project diagram
    if uml_lines:
        # Find position after any !pragma lines to insert hide commands
        insert_idx = 1
        for idx in range(1, len(uml_lines)):
            if uml_lines[idx].startswith("!"):
                continue
            insert_idx = idx
            break
        uml_lines.insert(insert_idx, "hide members\n")
        uml_lines.insert(insert_idx + 1, "hide circle\n")

    # Write the full project .puml file
    project_puml_path = os.path.join(puml_dir, f"{base_module}.puml")
    with open(project_puml_path, "w", encoding="utf-8") as f:
        f.writelines(uml_lines)

    # Extract a common !pragma line (if any) to reuse in other diagrams for consistency
    pragma_line = None
    for line in uml_lines:
        if line.strip().startswith("!pragma"):
            pragma_line = line
            break

    # Generate UML for each top-level package
    package_uml_outputs = {}  # store lines for reuse in file-level filtering
    for pkg in top_level_packages:
        pkg_path = os.path.join(root_dir, pkg)
        module_name = f"{base_module}.{pkg}"
        print(f"Generating UML for package '{module_name}'...")
        lines = list(py2puml(pkg_path, module_name))
        package_uml_outputs[pkg] = lines
        pkg_puml_path = os.path.join(puml_dir, f"{module_name}.puml")
        with open(pkg_puml_path, "w", encoding="utf-8") as f:
            f.writelines(lines)

    # Generate UML for each individual Python file (module)
    for py_file in all_py_files:
        # Derive the module name from file path
        rel_path = os.path.relpath(py_file, root_dir)
        # Split into module path and base name (without .py)
        mod_parts = rel_path.replace(os.sep, ".").split(".")  # e.g., "subdir.module.py" -> ["subdir","module","py"]
        if not mod_parts:
            continue
        if mod_parts[-1].lower() == "py":
            mod_parts = mod_parts[:-1]  # drop the 'py' extension part

        module_path = base_module
        if mod_parts[0] != base_module:
            # If rel_path doesn't start with base (likely it doesn't, since base_module is just name)
            # simply prepend base and then the rest of path (unless the file is in root_dir directly)
            if rel_path.count(os.sep) == 0:
                # File is directly under root
                module_path = base_module
            # Otherwise, we'll add components later

        # Build module_path properly
        sub_path = rel_path[:-3]  # remove ".py"
        sub_path = sub_path.replace(os.sep, ".")

        # Handle __init__.py: if present, remove the ".__init__" from module path
        if sub_path.endswith(".__init__"):
            sub_path = sub_path[: -len(".__init__")]

        # Compose the full module name
        if sub_path == "":  # this would happen if the file is root __init__.py
            mod_name = base_module
        else:
            mod_name = f"{base_module}.{sub_path}" if base_module not in sub_path else sub_path

        # Determine which package output to filter (top-level package or root)
        # Top-level package is the first segment after base (if any)
        top_pkg = mod_name.split(".", 1)[1] if (mod_name.startswith(base_module + ".") and "." in mod_name) else None
        source_lines = uml_lines  # default to entire project lines
        if top_pkg and top_pkg in package_uml_outputs:
            # Use the precomputed package UML lines for the corresponding top-level package
            source_lines = package_uml_outputs[top_pkg]

        # Filter lines for this module
        filtered_lines = filter_lines_for_module(source_lines, mod_name)
        if not filtered_lines:
            # If no class/enum definitions were found, skip creating a diagram for this file
            continue

        # Assemble the final .puml content for the file
        output_lines = [f"@startuml {mod_name}\n"]
        if pragma_line:
            output_lines.append(pragma_line)  # reuse the same pragma setting if available

        output_lines.extend(filtered_lines)

        # Append footer and enduml if they were present in original output
        footer_line = None
        for line in source_lines:
            if line.strip().startswith("footer"):
                footer_line = line
                break
        if footer_line:
            output_lines.append(footer_line)
        output_lines.append("@enduml\n")

        # Determine output filename (include __init__ in name if applicable)
        file_mod_path = mod_name.replace(base_module + ".", "")  # relative module path
        file_mod_path = file_mod_path if file_mod_path else base_module  # for base __init__.py
        file_name = (base_module + "." + file_mod_path) if file_mod_path != base_module else base_module

        # Use __init__ in filename if modulename was a package (to avoid clash with package diagram)
        if py_file.endswith("__init__.py"):
            file_name += ".__init__"
        file_puml_path = os.path.join(puml_dir, f"{file_name}.puml")
        with open(file_puml_path, "w", encoding="utf-8") as f:
            f.writelines(output_lines)

    # If PlantUML CLI is available, generate images
    if shutil.which("plantuml") is None:
        print("WARNING: PlantUML command-line tool not found. Skipping image generation.")
    else:
        print("PlantUML found. Generating images (PNG and SVG) for all diagrams...")
        # Gather all .puml files
        puml_files = [os.path.join(puml_dir, f) for f in os.listdir(puml_dir) if f.endswith(".puml")]
        # Run PlantUML to produce PNG and SVG outputs
        try:
            # We can call PlantUML for all files at once for efficiency
            subprocess.run(["plantuml", "-tpng", "-tsvg", "-o", puml_img_dir] + puml_files, check=True)
        except subprocess.CalledProcessError as e:
            print(f"WARNING: PlantUML generation failed (exit code {e.returncode}).")

if __name__ == "__main__":
    main()
