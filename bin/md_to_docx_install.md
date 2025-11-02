# Installation Guide for `md_to_docx.py`

This guide walks you through the full installation process to run `md_to_docx.py` successfully.

---

## 1. 🐍 Install Python 3.7+

Ensure you have Python 3.7 or higher installed. Check with:

```bash
python3 --version
```

If it's not installed, download it from: https://www.python.org/downloads/

---

## 2. 📦 Install Required Packages

Create a virtual environment (optional but recommended):

```bash
python3 -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate
```

Install the required Python packages:

```bash
pip install -r requirements.txt
```

If you didn't download `requirements.txt`, you can install manually:

```bash
pip install pyyaml
```

---

## 3. ⚙️ Install Pandoc

This script uses [Pandoc](https://pandoc.org/) to convert Markdown to `.docx` and `.pdf`.

### On Ubuntu/Debian:

```bash
sudo apt install pandoc
```

### On macOS (with Homebrew):

```bash
brew install pandoc
```

### On Windows:

Download and install from:  
https://github.com/jgm/pandoc/releases

Verify installation:

```bash
pandoc --version
```

---

## 4. (Optional) Install LaTeX for PDF Export

To export PDFs using `--pdf`, Pandoc requires a LaTeX engine.

### On Ubuntu/Debian:

```bash
sudo apt install texlive texlive-latex-extra
```

### On macOS:

```bash
brew install --cask mactex
```

### On Windows:

Download and install MikTeX: https://miktex.org/download

---

## ✅ You're Ready!

Now you can run the script:

```bash
python md_to_docx.py input.md -t template.dotx -o output.docx --toc --title-page --pdf --verbose
```