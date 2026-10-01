"""Find locals assigned from `<x>.value` that are later used in arithmetic.

Regex cannot see this: the assignment and the use are different statements, and
three separate greps missed it today. An AST pass tracks the binding instead.
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
            print(f"  {f}: {len(seen)}  lines {[l for l,_ in seen][:6]}")
            total+=len(seen)
print("TOTAL", total)
