import re
from collections import Counter
from itertools import pairwise


def _word_line_positions(text):
    positions = {}
    for line_number, line in enumerate(text.split("\n")):
        for word in re.findall(r"\w+", line):
            positions.setdefault(word, []).append(line_number)
    return positions


def _words_stay_on_their_lines(old, new):
    old_positions = _word_line_positions(old)
    new_positions = _word_line_positions(new)
    for word in old_positions.keys() & new_positions.keys():
        old_lines = Counter(old_positions[word])
        new_lines = Counter(new_positions[word])
        if sum((old_lines & new_lines).values()) != min(len(old_positions[word]), len(new_positions[word])):
            return False
    return True


class EditError(ValueError):
    pass


def _code_spans(text):
    return [
        match.span()
        for match in re.finditer(r"^[ \t]*```.*?^[ \t]*```[ \t]*$", text, re.MULTILINE | re.DOTALL)
    ]


def _protected_sections(text):
    sections = []
    for title in ("References", "Navigation"):
        match = re.search(rf"^## {title}\s*$", text, re.MULTILINE)
        if not match:
            continue
        next_heading = re.search(r"^## ", text[match.end():], re.MULTILINE)
        end = match.end() + next_heading.start() if next_heading else len(text)
        sections.append(text[match.start():end])
    return sections


def _front_matter(text):
    if not text.startswith("---\n"):
        return ""
    end = text.find("\n---\n", 4)
    return text[:end + 5] if end >= 0 else ""


def _protected_parts(text):
    return {
        "code blocks": re.findall(r"^[ \t]*```.*?^[ \t]*```[ \t]*$", text, re.MULTILINE | re.DOTALL),
        "headings": re.findall(r"^#{1,6} .*$", text, re.MULTILINE),
        "tables": re.findall(r"^\|.*$", text, re.MULTILINE),
        "links and images": re.findall(r"!?\[[^]]*\]\([^)]*\)", text),
        "HTML structure": re.findall(r"^\s*</?[^>]+>\s*$", text, re.MULTILINE),
        "references and navigation": _protected_sections(text),
        "front matter": _front_matter(text),
    }


def integrity_errors(original, candidate):
    original_parts = _protected_parts(original)
    candidate_parts = _protected_parts(candidate)
    return [name for name in original_parts if original_parts[name] != candidate_parts[name]]


def _validate_edit(text, edit):
    old = edit["old"]
    new = edit["new"]
    if not old or old == new:
        raise EditError(f"{edit['id']}: old and new text must differ")
    if "\n\n" in old or "\n\n" in new:
        raise EditError(f"{edit['id']}: edit must stay within a single paragraph")
    if old.split() == new.split():
        raise EditError(f"{edit['id']}: whitespace-only reflow is not allowed")
    if old.count("\n") != new.count("\n") or not _words_stay_on_their_lines(old, new):
        raise EditError(f"{edit['id']}: edit changes line wrapping")
    if text.count(old) != 1:
        raise EditError(f"{edit['id']}: old text must occur exactly once")
    start = text.index(old)
    end = start + len(old)
    for code_start, code_end in _code_spans(text):
        if start < code_end and end > code_start:
            raise EditError(f"{edit['id']}: edits inside code blocks are not allowed")
    return start, end


def apply_edits(text, edits):
    ids = [edit["id"] for edit in edits]
    if len(ids) != len(set(ids)):
        raise EditError("edit IDs must be unique")
    spans = []
    for edit in edits:
        start, end = _validate_edit(text, edit)
        spans.append((start, end, edit))
    ordered = sorted(spans, key=lambda item: item[0])
    for previous, current in pairwise(ordered):
        if current[0] < previous[1]:
            raise EditError(f"{previous[2]['id']} and {current[2]['id']} overlap")
    candidate = text
    for start, end, edit in sorted(spans, key=lambda item: item[0], reverse=True):
        candidate = candidate[:start] + edit["new"] + candidate[end:]
    changed_parts = integrity_errors(text, candidate)
    if changed_parts:
        raise EditError("edit changes protected " + ", ".join(changed_parts))
    return candidate


def select_approved_edits(edits, decisions):
    edit_ids = [edit["id"] for edit in edits]
    decision_ids = [decision["id"] for decision in decisions]
    if sorted(edit_ids) != sorted(decision_ids) or len(decision_ids) != len(set(decision_ids)):
        raise EditError("final decisions must cover every edit exactly once")
    if any(decision["verdict"] not in {"APPROVE", "DISAPPROVE"} for decision in decisions):
        raise EditError("final verdicts must be APPROVE or DISAPPROVE")
    approved = {decision["id"] for decision in decisions if decision["verdict"] == "APPROVE"}
    return [edit for edit in edits if edit["id"] in approved]
