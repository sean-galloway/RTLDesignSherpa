#!/usr/bin/env python3
"""
md_to_docx.py — Convert Markdown (single file or expanded index) to DOCX/PDF via Pandoc.

Features:
- --expand-index: parse an index.md and inline linked chapter .md files in order
- --title-page [path]: prepend a title page (auto if no path given)
- --assets-dir (repeatable): added to Pandoc --resource-path
- --pagebreak: insert page breaks between concatenated files
- Emoji mapping for PDF robustness (✅ -> ✓, etc.)
- Force a Unicode-friendly PDF engine (xelatex) by default
- Wavedrom .json "images": render to SVG (python-wavedrom or wavedrom-cli) or degrade to links
- Font controls for XeLaTeX/LuaLaTeX: --mainfont/--monofont/--sansfont/--mathfont
- Embedded Mermaid diagrams: ```mermaid blocks rendered to SVG via mmdc CLI
- Embedded Graphviz diagrams: ```graphviz or ```dot blocks rendered to SVG via dot CLI
- Embedded PlantUML diagrams: ```plantuml blocks rendered to SVG via plantuml CLI

Required tools for diagram rendering (install as needed):
- Mermaid: npm install -g @mermaid-js/mermaid-cli (provides 'mmdc')
- Graphviz: apt install graphviz / brew install graphviz (provides 'dot')
- PlantUML: apt install plantuml / brew install plantuml (provides 'plantuml')
"""

import argparse
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import date

# ---------------------------
# Config / Helpers
# ---------------------------

MD_LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+\.md)(#[^)]+)?\)", re.IGNORECASE)
IMG_JSON_RE = re.compile(r'!\[([^\]]*)\]\(([^)]+\.json)\)')
IMG_RE = re.compile(r'!\[([^\]]*)\]\(([^)]+)\)')

# Fenced code block patterns for embedded diagrams
MERMAID_BLOCK_RE = re.compile(r'```mermaid\s*\n(.*?)\n```', re.DOTALL | re.IGNORECASE)
GRAPHVIZ_BLOCK_RE = re.compile(r'```(?:graphviz|dot)\s*\n(.*?)\n```', re.DOTALL | re.IGNORECASE)
PLANTUML_BLOCK_RE = re.compile(r'```plantuml\s*\n(.*?)\n```', re.DOTALL | re.IGNORECASE)

EMOJI_MAP = {
    "✅": "✓",
    "❌": "✗",
    "➕": "+",
    "➖": "−",
    "⚠️": "⚠",
    "ℹ️": "ℹ",
    "🛠️": "🛠",
    "📌": "",
    "🚧": "",
}

def log(*a, **k):
    if not k.pop("_quiet", False):
        print(*a, **k, file=sys.stderr)

def read_text(p: pathlib.Path) -> str:
    return p.read_text(encoding="utf-8")

def write_text(p: pathlib.Path, s: str):
    p.write_text(s, encoding="utf-8")

def strip_or_map_emoji(s: str) -> str:
    for k, v in EMOJI_MAP.items():
        s = s.replace(k, v)
    return s

def collect_from_index(index_path: pathlib.Path) -> list[pathlib.Path]:
    """
    Scan the index markdown for links to .md files and return them in order.
    Keeps only links that resolve relative to the index folder.
    Ensures index itself is first.
    """
    root = index_path.parent
    content = read_text(index_path)
    links = []
    seen = set()

    # Inline comment include directive support:  <!-- include: path/to/file.md -->
    for inc in re.findall(r'<!--\s*include:\s*([^\s>]+\.md)\s*-->', content, flags=re.IGNORECASE):
        p = (root / inc).resolve()
        if p.exists() and p.suffix.lower() == ".md" and p not in seen:
            links.append(p); seen.add(p)

    for m in MD_LINK_RE.finditer(content):
        rel = m.group(2).strip()
        if "://" in rel or rel.startswith("#"):
            continue
        p = (root / rel).resolve()
        if p.suffix.lower() == ".md" and p.exists() and p not in seen:
            links.append(p); seen.add(p)

    idx = index_path.resolve()
    if idx not in seen:
        links = [idx] + links
    else:
        links = [idx] + [p for p in links if p != idx]
    return links

def rewrite_image_paths_for_file(text: str, source_file: pathlib.Path) -> str:
    """
    Rewrite relative image paths in markdown text to absolute paths.
    This is necessary when concatenating markdown files from different directories.
    """
    def _sub(m):
        alt, path = m.group(1), m.group(2)
        # Skip absolute paths, URLs, and already processed paths
        if path.startswith('/') or '://' in path:
            return m.group(0)
        # Resolve relative path based on source file location
        abs_path = (source_file.parent / path).resolve()
        if abs_path.exists():
            return f"![{alt}]({abs_path.as_posix()})"
        # If file doesn't exist, keep original reference
        return m.group(0)
    return IMG_RE.sub(_sub, text)

def concat_markdown(files: list[pathlib.Path], pagebreak: bool) -> str:
    parts = []
    for i, f in enumerate(files):
        text = read_text(f).rstrip() + "\n"
        # Rewrite relative image paths to absolute paths
        text = rewrite_image_paths_for_file(text, f)
        parts.append(text)
        if pagebreak and i < len(files) - 1:
            parts.append('\n::: {.pagebreak}\n:::\n')
    return "\n".join(parts)

# ---- Wavedrom handling ----

def try_render_wavedrom_python(json_path: pathlib.Path) -> str | None:
    try:
        import wavedrom
        svg = wavedrom.render_file(str(json_path))  # returns SVG string in recent versions
        return svg if isinstance(svg, str) else None
    except Exception:
        return None

def try_render_wavedrom_cli(json_path: pathlib.Path, out_svg: pathlib.Path) -> bool:
    if not shutil.which("wavedrom-cli"):
        return False
    try:
        subprocess.run(
            ["wavedrom-cli", str(json_path), "-s", "-o", str(out_svg)],
            check=True
        )
        return out_svg.exists()
    except subprocess.CalledProcessError:
        return False

def rewrite_wavedrom_images(md_text: str, base_dir: pathlib.Path, tmp_img_dir: pathlib.Path) -> str:
    def _sub(m):
        alt, rel = m.group(1), m.group(2)
        jp = (base_dir / rel).resolve()
        if not jp.exists():
            return f"[{alt or 'diagram (wavedrom)'}]({rel})"
        svg_text = try_render_wavedrom_python(jp)
        if svg_text:
            out_svg = tmp_img_dir / (jp.stem + ".svg")
            write_text(out_svg, svg_text)
            return f"![{alt}]({out_svg.as_posix()})"
        out_svg = tmp_img_dir / (jp.stem + ".svg")
        if try_render_wavedrom_cli(jp, out_svg):
            return f"![{alt}]({out_svg.as_posix()})"
        return f"[{alt or 'diagram (wavedrom)'}]({rel})"
    return IMG_JSON_RE.sub(_sub, md_text)

# ---- Mermaid handling ----

def render_mermaid_block(code: str, tmp_img_dir: pathlib.Path, idx: int, quiet: bool = False) -> str:
    """
    Render a Mermaid diagram code block to PNG.
    Returns markdown image reference or fallback code block.

    Note: PNG is used instead of SVG because SVG output from headless Chrome
    often has font/text rendering issues when fonts aren't installed in the
    headless environment.
    """
    out_png = tmp_img_dir / f"mermaid_{idx}.png"

    # Try mmdc CLI (mermaid-cli from npm)
    mmdc = shutil.which("mmdc")
    if mmdc:
        tmp_mmd = tmp_img_dir / f"mermaid_{idx}.mmd"
        write_text(tmp_mmd, code)

        # Create puppeteer config to disable sandbox (required on Ubuntu 23.10+)
        puppeteer_config = tmp_img_dir / "puppeteer-config.json"
        if not puppeteer_config.exists():
            write_text(puppeteer_config, '{"args": ["--no-sandbox", "--disable-setuid-sandbox"]}')

        try:
            # Use PNG output with high scale for quality, white background for better PDF embedding
            cmd = [mmdc, "-i", str(tmp_mmd), "-o", str(out_png), "-b", "white",
                   "-p", str(puppeteer_config), "-s", "2"]  # scale=2 for higher resolution
            if quiet:
                cmd.append("-q")
            subprocess.run(cmd, check=True, capture_output=True, timeout=30)
            if out_png.exists():
                if not quiet:
                    log(f"  Rendered mermaid_{idx}.png")
                return f"![Mermaid diagram]({out_png.as_posix()})"
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
            if not quiet:
                log(f"  Warning: Mermaid render failed for block {idx}: {e}")

    # Fallback: keep as code block
    if not quiet:
        log(f"  Warning: mmdc not found, keeping mermaid block {idx} as code")
    return f"```\n{code}\n```"

def rewrite_mermaid_blocks(md_text: str, tmp_img_dir: pathlib.Path, quiet: bool = False) -> str:
    """Replace all ```mermaid blocks with rendered SVG images."""
    idx = [0]  # Use list to allow mutation in nested function

    def _sub(m):
        code = m.group(1).strip()
        idx[0] += 1
        return render_mermaid_block(code, tmp_img_dir, idx[0], quiet)

    return MERMAID_BLOCK_RE.sub(_sub, md_text)

# ---- Graphviz handling ----

def render_graphviz_block(code: str, tmp_img_dir: pathlib.Path, idx: int, quiet: bool = False) -> str:
    """
    Render a Graphviz/DOT diagram code block to SVG.
    Returns markdown image reference or fallback code block.
    """
    out_svg = tmp_img_dir / f"graphviz_{idx}.svg"

    # Try dot CLI (from graphviz package)
    dot = shutil.which("dot")
    if dot:
        try:
            result = subprocess.run(
                [dot, "-Tsvg"],
                input=code.encode("utf-8"),
                capture_output=True,
                timeout=30,
                check=True
            )
            out_svg.write_bytes(result.stdout)
            if out_svg.exists():
                if not quiet:
                    log(f"  Rendered graphviz_{idx}.svg")
                return f"![Graphviz diagram]({out_svg.as_posix()})"
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
            if not quiet:
                log(f"  Warning: Graphviz render failed for block {idx}: {e}")

    # Fallback: keep as code block
    if not quiet:
        log(f"  Warning: dot not found, keeping graphviz block {idx} as code")
    return f"```dot\n{code}\n```"

def rewrite_graphviz_blocks(md_text: str, tmp_img_dir: pathlib.Path, quiet: bool = False) -> str:
    """Replace all ```graphviz or ```dot blocks with rendered SVG images."""
    idx = [0]

    def _sub(m):
        code = m.group(1).strip()
        idx[0] += 1
        return render_graphviz_block(code, tmp_img_dir, idx[0], quiet)

    return GRAPHVIZ_BLOCK_RE.sub(_sub, md_text)

# ---- PlantUML handling ----

def render_plantuml_block(code: str, tmp_img_dir: pathlib.Path, idx: int, quiet: bool = False) -> str:
    """
    Render a PlantUML diagram code block to SVG.
    Returns markdown image reference or fallback code block.
    """
    out_svg = tmp_img_dir / f"plantuml_{idx}.svg"
    tmp_puml = tmp_img_dir / f"plantuml_{idx}.puml"

    # Ensure code has @startuml/@enduml wrapper
    code_wrapped = code
    if not code.strip().startswith("@start"):
        code_wrapped = f"@startuml\n{code}\n@enduml"

    write_text(tmp_puml, code_wrapped)

    # Try plantuml CLI
    plantuml = shutil.which("plantuml")
    if plantuml:
        try:
            subprocess.run(
                [plantuml, "-tsvg", "-o", str(tmp_img_dir), str(tmp_puml)],
                capture_output=True,
                timeout=30,
                check=True
            )
            if out_svg.exists():
                if not quiet:
                    log(f"  Rendered plantuml_{idx}.svg")
                return f"![PlantUML diagram]({out_svg.as_posix()})"
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
            if not quiet:
                log(f"  Warning: PlantUML render failed for block {idx}: {e}")

    # Try java -jar plantuml.jar if PLANTUML_JAR env var is set
    import os
    plantuml_jar = os.environ.get("PLANTUML_JAR")
    if plantuml_jar and pathlib.Path(plantuml_jar).exists():
        java = shutil.which("java")
        if java:
            try:
                subprocess.run(
                    [java, "-jar", plantuml_jar, "-tsvg", "-o", str(tmp_img_dir), str(tmp_puml)],
                    capture_output=True,
                    timeout=30,
                    check=True
                )
                if out_svg.exists():
                    if not quiet:
                        log(f"  Rendered plantuml_{idx}.svg (via jar)")
                    return f"![PlantUML diagram]({out_svg.as_posix()})"
            except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
                if not quiet:
                    log(f"  Warning: PlantUML jar render failed for block {idx}: {e}")

    # Fallback: keep as code block
    if not quiet:
        log(f"  Warning: plantuml not found, keeping plantuml block {idx} as code")
    return f"```\n{code}\n```"

def rewrite_plantuml_blocks(md_text: str, tmp_img_dir: pathlib.Path, quiet: bool = False) -> str:
    """Replace all ```plantuml blocks with rendered SVG images."""
    idx = [0]

    def _sub(m):
        code = m.group(1).strip()
        idx[0] += 1
        return render_plantuml_block(code, tmp_img_dir, idx[0], quiet)

    return PLANTUML_BLOCK_RE.sub(_sub, md_text)

# ---- Auto-detection of unfenced diagrams ----

# Patterns that indicate Mermaid diagram content (at start of line or code block)
MERMAID_INDICATORS = [
    r'^graph\s+(TB|BT|LR|RL|TD)\b',      # graph TB, graph LR, etc.
    r'^flowchart\s+(TB|BT|LR|RL|TD)\b',  # flowchart TD, etc.
    r'^sequenceDiagram\b',
    r'^classDiagram\b',
    r'^stateDiagram\b',
    r'^erDiagram\b',
    r'^gantt\b',
    r'^pie\b',
    r'^journey\b',
    r'^gitGraph\b',
]
MERMAID_INDICATOR_RE = re.compile('|'.join(MERMAID_INDICATORS), re.MULTILINE | re.IGNORECASE)

# Patterns for Graphviz/DOT
GRAPHVIZ_INDICATORS = [
    r'^digraph\s+\w*\s*\{',
    r'^graph\s+\w*\s*\{',
    r'^strict\s+(di)?graph\s+',
]
GRAPHVIZ_INDICATOR_RE = re.compile('|'.join(GRAPHVIZ_INDICATORS), re.MULTILINE | re.IGNORECASE)

# Pattern for generic fenced code blocks (``` without language)
GENERIC_CODE_BLOCK_RE = re.compile(r'```\s*\n(.*?)\n```', re.DOTALL)

def detect_and_tag_unfenced_diagrams(md_text: str, quiet: bool = False) -> str:
    """
    Auto-detect unfenced diagram blocks and add appropriate language tags.

    This is a HEURISTIC - it guesses based on content patterns.
    Warnings are emitted for each detection so users know what was auto-tagged.

    Handles:
    1. Generic ``` blocks containing Mermaid/Graphviz syntax
    2. Bare diagram code outside of any code fence (less reliable)
    """
    detections = []

    def _check_and_tag_block(m):
        content = m.group(1).strip()
        first_lines = content[:500]  # Check first 500 chars for indicators

        # Check for Mermaid patterns
        if MERMAID_INDICATOR_RE.search(first_lines):
            # Extract the indicator for logging
            indicator_match = MERMAID_INDICATOR_RE.search(first_lines)
            indicator = indicator_match.group(0) if indicator_match else "mermaid pattern"
            detections.append(('mermaid', indicator, content[:50].replace('\n', ' ')))
            return f"```mermaid\n{content}\n```"

        # Check for Graphviz patterns
        if GRAPHVIZ_INDICATOR_RE.search(first_lines):
            indicator_match = GRAPHVIZ_INDICATOR_RE.search(first_lines)
            indicator = indicator_match.group(0) if indicator_match else "graphviz pattern"
            detections.append(('graphviz', indicator, content[:50].replace('\n', ' ')))
            return f"```graphviz\n{content}\n```"

        # No match - keep as generic code block
        return m.group(0)

    # Process generic code blocks
    result = GENERIC_CODE_BLOCK_RE.sub(_check_and_tag_block, md_text)

    # Log detections
    if detections and not quiet:
        log(f"\n  ⚠️  AUTO-DETECTION: Found {len(detections)} unfenced diagram(s) - tagging as best guess:")
        for dtype, indicator, preview in detections:
            preview_clean = preview[:40] + "..." if len(preview) > 40 else preview
            log(f"      • Detected '{dtype}' (saw '{indicator}'): {preview_clean}")
        log(f"      ℹ️  These were generic ``` blocks. For reliable rendering, use ```mermaid or ```graphviz explicitly.\n")

    return result

def detect_bare_mermaid_lines(md_text: str, quiet: bool = False) -> str:
    """
    Attempt to detect bare Mermaid diagrams that aren't in any code fence.

    This is VERY HEURISTIC and may have false positives.
    Only handles simple cases where a Mermaid keyword starts a line outside code blocks.
    """
    # This is tricky because we need to avoid matching inside existing code blocks
    # For now, we'll do a simple line-by-line scan and look for isolated Mermaid starts

    lines = md_text.split('\n')
    result_lines = []
    in_code_block = False
    i = 0
    detections = 0

    while i < len(lines):
        line = lines[i]

        # Track code block state
        if line.strip().startswith('```'):
            in_code_block = not in_code_block
            result_lines.append(line)
            i += 1
            continue

        # Skip if we're inside a code block
        if in_code_block:
            result_lines.append(line)
            i += 1
            continue

        # Check if this line looks like a bare Mermaid start
        stripped = line.strip()
        if MERMAID_INDICATOR_RE.match(stripped):
            # Found a potential bare Mermaid diagram
            # Collect lines until we hit an empty line or another heading
            diagram_lines = [line]
            j = i + 1
            while j < len(lines):
                next_line = lines[j]
                # Stop conditions: empty line, heading, or new code block
                if (next_line.strip() == '' and j > i + 1) or \
                   next_line.strip().startswith('#') or \
                   next_line.strip().startswith('```'):
                    break
                diagram_lines.append(next_line)
                j += 1

            # Only wrap if we found multiple lines (single line is probably not a diagram)
            if len(diagram_lines) > 1:
                detections += 1
                if not quiet:
                    preview = stripped[:40] + "..." if len(stripped) > 40 else stripped
                    log(f"  ⚠️  AUTO-DETECTION (BARE): Wrapping suspected bare Mermaid at line {i+1}: {preview}")
                result_lines.append('```mermaid')
                result_lines.extend(diagram_lines)
                result_lines.append('```')
                i = j
                continue

        result_lines.append(line)
        i += 1

    if detections > 0 and not quiet:
        log(f"      ℹ️  Wrapped {detections} bare diagram(s). This is a GUESS - verify output is correct.\n")

    return '\n'.join(result_lines)

# ---- Combined diagram rendering ----

def render_embedded_diagrams(md_text: str, tmp_img_dir: pathlib.Path, quiet: bool = False) -> str:
    """
    Render all embedded diagram code blocks (Mermaid, Graphviz, PlantUML) to SVG.

    Processing order:
    1. Auto-detect unfenced diagrams in generic ``` blocks (heuristic)
    2. Attempt to detect bare Mermaid diagrams outside code fences (very heuristic)
    3. Render properly-tagged ```mermaid blocks
    4. Render properly-tagged ```graphviz/```dot blocks
    5. Render properly-tagged ```plantuml blocks
    """
    # Step 1 & 2: Auto-detection (with warnings)
    md_text = detect_and_tag_unfenced_diagrams(md_text, quiet)
    md_text = detect_bare_mermaid_lines(md_text, quiet)

    # Step 3-5: Render tagged blocks
    md_text = rewrite_mermaid_blocks(md_text, tmp_img_dir, quiet)
    md_text = rewrite_graphviz_blocks(md_text, tmp_img_dir, quiet)
    md_text = rewrite_plantuml_blocks(md_text, tmp_img_dir, quiet)
    return md_text

# ---------------------------
# Pandoc runners
# ---------------------------

def build_resource_path(args, input_path: pathlib.Path) -> str:
    paths = [str(pathlib.Path(a).resolve()) for a in args.assets_dir]
    paths.append(str(input_path.resolve().parent))
    seen = set()
    dedup = []
    for p in paths:
        if p not in seen:
            seen.add(p)
            dedup.append(p)
    return ":".join(dedup)

def run_pandoc_docx(md_path: pathlib.Path, out_docx: pathlib.Path, args):
    pandoc = shutil.which("pandoc")
    if not pandoc:
        raise RuntimeError("pandoc not found on PATH")
    cmd = [pandoc, str(md_path), "-o", str(out_docx)]
    if args.reference_doc:
        cmd += ["--reference-doc", args.reference_doc]
    if args.toc:
        cmd += ["--toc"]
    if args.quiet:
        cmd += ["--quiet"]
    cmd += ["--resource-path", build_resource_path(args, pathlib.Path(args.input))]
    cmd += ["-V", "graphics=true"]  # help Pandoc with figures/pagebreaks
    subprocess.run(cmd, check=True)

def run_pandoc_pdf(md_path: pathlib.Path, out_pdf: pathlib.Path, args):
    pandoc = shutil.which("pandoc")
    if not pandoc:
        raise RuntimeError("pandoc not found on PATH")
    engine = args.pdf_engine or "xelatex"
    cmd = [
        pandoc, str(md_path), "-o", str(out_pdf), "-s",
        "--from", "gfm+yaml_metadata_block",
        f"--pdf-engine={engine}",
        "--resource-path", build_resource_path(args, pathlib.Path(args.input)),
    ]
    if args.toc:
        cmd += ["--toc"]
    if args.quiet:
        cmd += ["--quiet"]

    # --- Font controls: sensible defaults for wide Unicode coverage ---
    default_main = "DejaVu Serif"
    default_mono = "DejaVu Sans Mono"
    mainfont = args.mainfont or default_main
    monofont = args.monofont or default_mono
    cmd += ["-V", f"mainfont={mainfont}", "-V", f"monofont={monofont}"]
    if args.sansfont:
        cmd += ["-V", f"sansfont={args.sansfont}"]
    if args.mathfont:
        cmd += ["-V", f"mathfont={args.mathfont}"]

    subprocess.run(cmd, check=True)

# ---------------------------
# Main
# ---------------------------

def parse_args():
    p = argparse.ArgumentParser(
        description="Convert Markdown (single file or expanded index) to DOCX/PDF via Pandoc."
    )
    p.add_argument("input", help="Input Markdown file (index or chapter).")
    p.add_argument("output", help="Output .docx filename (PDF uses same basename).")
    p.add_argument("--reference-doc", help="Path to a DOCX reference (template).")
    p.add_argument("--pdf", action="store_true", help="Also emit a PDF with same basename.")
    p.add_argument("--toc", action="store_true", help="Include a table of contents.")
    p.add_argument("--quiet", action="store_true", help="Reduce Pandoc chatter.")
    p.add_argument("--pagebreak", action="store_true", help="Insert page breaks between concatenated files.")
    p.add_argument("--assets-dir", action="append", default=[],
                help="Add an assets/resource directory (repeatable).")
    p.add_argument("--title-page", nargs="?", const="__AUTO__",
                help="Prepend a title page. If value omitted, auto-generate; otherwise treat as path to a .md file.")
    p.add_argument("--expand-index", action="store_true",
                help="Parse the input index and inline linked chapter .md files in order.")
    p.add_argument("--pdf-engine", default=None,
                help="Override PDF engine (default: xelatex).")
    # Font controls (XeLaTeX/LuaLaTeX)
    p.add_argument("--mainfont", default=None, help="Main text font (e.g., 'DejaVu Serif', 'Noto Serif').")
    p.add_argument("--monofont", default=None, help="Monospace font (e.g., 'DejaVu Sans Mono', 'Noto Sans Mono').")
    p.add_argument("--sansfont", default=None, help="Sans-serif font (optional).")
    p.add_argument("--mathfont", default=None, help="Math font (optional).")
    return p.parse_args()

def make_title_page(auto_token: str, primary_input: pathlib.Path) -> str:
    if auto_token != "__AUTO__":
        tp = pathlib.Path(auto_token)
        return read_text(tp)
    title = primary_input.stem.replace("_", " ").replace("-", " ").title()
    today = date.today().isoformat()
    return f"# {title}\n\n**Generated:** {today}\n\n"

def main():
    args = parse_args()
    in_path = pathlib.Path(args.input).resolve()
    out_docx = pathlib.Path(args.output).with_suffix(".docx")
    out_pdf  = out_docx.with_suffix(".pdf")

    with tempfile.TemporaryDirectory() as td:
        tmp_dir = pathlib.Path(td)
        build_md = tmp_dir / "build.md"
        tmp_imgs = tmp_dir / "gen_images"
        tmp_imgs.mkdir(exist_ok=True)

        # Determine source set
        if args.expand_index:
            files = collect_from_index(in_path)
            if not files:
                files = [in_path]
        else:
            files = [in_path]

        # Build merged markdown
        chunks = []
        if args.title_page:
            chunks.append(make_title_page(args.title_page, in_path))

        merged = concat_markdown(files, args.pagebreak)
        merged = strip_or_map_emoji(merged)
        merged = rewrite_wavedrom_images(merged, in_path.parent, tmp_imgs)
        merged = render_embedded_diagrams(merged, tmp_imgs, args.quiet)

        chunks.append(merged)
        final_md = ("\n".join(chunks)).strip() + "\n"
        write_text(build_md, final_md)

        # Generate DOCX
        run_pandoc_docx(build_md, out_docx, args)

        # Optional PDF
        if args.pdf:
            try:
                run_pandoc_pdf(build_md, out_pdf, args)
            except subprocess.CalledProcessError:
                # Fallback: LibreOffice convert from DOCX, if present
                soffice = shutil.which("soffice")
                if not soffice:
                    raise
                subprocess.run([
                    soffice, "--headless", "--convert-to", "pdf",
                    "--outdir", str(out_pdf.parent), str(out_docx)
                ], check=True)

    if not args.quiet:
        log(f"✓ Wrote {out_docx}")
        if args.pdf:
            log(f"✓ Wrote {out_pdf}")

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)
