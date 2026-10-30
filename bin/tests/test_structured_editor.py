import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
_spec = importlib.util.spec_from_file_location("structured_editor", ROOT / "bin" / "structured_editor.py")
structured_editor = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(structured_editor)
EditError = structured_editor.EditError
apply_edits = structured_editor.apply_edits
select_approved_edits = structured_editor.select_approved_edits


def edit(old, new, edit_id="edit-001"):
    return {"id": edit_id, "old": old, "new": new, "reason": "test edit"}


def test_exact_edit_preserves_unrelated_line_wrapping():
    source = "First line\nwraps here.\n\n**Note:** the value stays\non this line.\n"
    result = apply_edits(source, [edit("**Note:** the", "**Note:** The")])
    assert result == "First line\nwraps here.\n\n**Note:** The value stays\non this line.\n"


def test_no_edits_returns_source_byte_for_byte():
    source = "Unchanged\ntext.\n"
    assert apply_edits(source, []) == source


def test_whitespace_only_reflow_is_rejected():
    with pytest.raises(EditError, match="whitespace-only"):
        apply_edits("A paragraph\nwith wrapping.\n", [edit("paragraph\nwith", "paragraph with")])


def test_wording_edit_cannot_change_line_wrapping():
    with pytest.raises(EditError, match="line wrapping"):
        apply_edits("A small\nparagraph here.\n", [edit("A small\nparagraph", "A tiny paragraph")])


def test_wording_edit_cannot_move_a_line_break_to_another_word():
    with pytest.raises(EditError, match="line wrapping"):
        apply_edits("First line\nwraps here.\n", [edit("First line\nwraps", "First line wraps\nhere")])


@pytest.mark.parametrize(
    ("old", "new"),
    [
        ("tap).\nThat includes", "tap).\nThis includes"),
        ("head's.\n4. **Read", "head's.\n5. **Read"),
        ("input *CHK are\nchecked", "input *CHK signals are\nchecked"),
    ],
)
def test_wording_edit_can_change_words_next_to_a_stationary_line_break(old, new):
    assert apply_edits(old + "\n", [edit(old, new)]) == new + "\n"


def test_old_text_must_be_unique():
    with pytest.raises(EditError, match="exactly once"):
        apply_edits("same\nsame\n", [edit("same", "different")])


def test_multiparagraph_edit_is_rejected():
    with pytest.raises(EditError, match="single paragraph"):
        apply_edits("one\n\ntwo\n", [edit("one\n\ntwo", "changed")])


def test_fenced_code_is_protected():
    source = "Before\n\n```systemverilog\nmodule old;\n```\n\nAfter\n"
    with pytest.raises(EditError, match="code"):
        apply_edits(source, [edit("module old;", "module new;")])


@pytest.mark.parametrize(
    ("source", "old", "new"),
    [
        ("# Heading\n", "# Heading", "# Changed"),
        ("| cell |\n", "| cell |", "| changed |"),
        ("[label](target.md)\n", "[label](target.md)", "[other](target.md)"),
        ("![label](image.png)\n", "![label](image.png)", "![other](image.png)"),
        ("<table>\n<tr>\n</table>\n", "<tr>", "<td>"),
    ],
)
def test_markdown_structures_are_protected(source, old, new):
    with pytest.raises(EditError):
        apply_edits(source, [edit(old, new)])


def test_references_and_navigation_are_protected():
    source = "Body text.\n\n## References\n\nKeep this citation.\n\n## Navigation\n\nKeep this link.\n"
    with pytest.raises(EditError, match="protected"):
        apply_edits(source, [edit("Keep this citation.", "Change this citation.")])


def test_overlapping_edits_are_rejected():
    with pytest.raises(EditError, match="overlap"):
        apply_edits("one two three\n", [
            edit("one two", "ONE TWO", "edit-001"),
            edit("two three", "TWO THREE", "edit-002"),
        ])


def test_final_decisions_select_only_approved_edits():
    edits = [
        edit("first", "FIRST", "edit-001"),
        edit("second", "SECOND", "edit-002"),
    ]
    decisions = [
        {"id": "edit-001", "verdict": "APPROVE"},
        {"id": "edit-002", "verdict": "DISAPPROVE"},
    ]
    selected = select_approved_edits(edits, decisions)
    assert [item["id"] for item in selected] == ["edit-001"]


def test_final_decisions_must_cover_every_edit_exactly_once():
    edits = [edit("first", "FIRST", "edit-001")]
    with pytest.raises(EditError, match="exactly once"):
        select_approved_edits(edits, [])
