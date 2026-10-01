"""Find locals assigned from `<x>.value` that are later used in arithmetic.

cocotb 1.x returns a `BinaryValue`, which supports `>>`, `&`, `+` and friends.
cocotb 2.x returns a `LogicArray`, which does NOT -- so this pattern raises
`TypeError: unsupported operand type(s) for >>` under 2.x. The fix is `int()` at
the ASSIGNMENT, so the arithmetic runs on an int.

Regex cannot see this: the assignment and the use are different statements, so no
line-oriented pattern sees both. Three separate greps missed it (2026-10-01),
including one that reported 0 hits in a file whose own traceback named line 1564.

TRIAGE THE RESULTS -- this over-reports. `.value` is also an Enum member's value
and a dataclass field, and nothing static distinguishes those from a cocotb
handle. Of 10 hits found on first use, 3 were Enum/dataclass and only 7 were real
signal reads. The source line is printed so that triage takes a second.
"""
import ast, sys, pathlib

ARITH = (ast.RShift, ast.LShift, ast.BitAnd, ast.BitOr, ast.Add, ast.Sub, ast.Mult)

class V(ast.NodeVisitor):
    def __init__(self): self.val_names=set(); self.hits=[]
    def visit_Assign(self, n):
        if (isinstance(n.value, ast.Attribute) and n.value.attr == "value"
                and len(n.targets)==1 and isinstance(n.targets[0], ast.Name)):
            self.val_names.add(n.targets[0].id)
        self.generic_visit(n)
    def visit_BinOp(self, n):
        if isinstance(n.op, ARITH):
            for side in (n.left, n.right):
                if isinstance(side, ast.Name) and side.id in self.val_names:
                    self.hits.append((n.lineno, side.id))
                if (isinstance(side, ast.Attribute) and side.attr == "value"):
                    self.hits.append((n.lineno, "<expr>.value"))
        self.generic_visit(n)

total=0
for root in sys.argv[1:]:
    for f in sorted(pathlib.Path(root).rglob("*.py")):
        try: tree = ast.parse(f.read_text())
        except Exception: continue
        v=V(); v.visit(tree)
        if v.hits:
            seen=sorted(set(v.hits))
            lines = f.read_text().splitlines()
            print(f"  {f}: {len(seen)}")
            for ln, nm in seen:
                src = lines[ln - 1].strip() if 0 < ln <= len(lines) else ""
                print(f"      {ln:>5}  {src[:92]}")
            total+=len(seen)
print("TOTAL", total)
