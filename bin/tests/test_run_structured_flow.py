import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "bin"))
_spec = importlib.util.spec_from_file_location("run_structured_flow", ROOT / "bin" / "run_structured_flow.py")
flow = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(flow)


def test_artifact_directories_include_the_source_path():
    output = ROOT / "sim_build/doc-editing-batch"
    common = flow.artifact_dir(ROOT / "docs/markdown/rtl-common/index.md", output)
    amba = flow.artifact_dir(ROOT / "docs/markdown/rtl-amba/index.md", output)
    assert common == output / "docs/markdown/rtl-common/index"
    assert amba == output / "docs/markdown/rtl-amba/index"
    assert common != amba
