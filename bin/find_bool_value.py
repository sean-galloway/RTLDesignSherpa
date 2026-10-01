"""Find `.value` used where a bool is required -- `if sig.value:`, `while ...`,
`and`/`or`/`not`. cocotb 2.x refuses to cast a LogicArray to bool.

Same caveat as find_value_arith.py: `.value` is also an Enum member and a
dataclass field, so TRIAGE the hits. The source line is printed for that.
"""
import ast, sys, pathlib
class V(ast.NodeVisitor):
    def __init__(self): self.names=set(); self.hits=[]
    def visit_Assign(self, n):
        if (isinstance(n.value, ast.Attribute) and n.value.attr=="value"
                and len(n.targets)==1 and isinstance(n.targets[0], ast.Name)):
            self.names.add(n.targets[0].id)
        self.generic_visit(n)
    def _check(self, node, where):
        if isinstance(node, ast.Attribute) and node.attr=="value":
            self.hits.append((node.lineno, where))
        elif isinstance(node, ast.Name) and node.id in self.names:
            self.hits.append((node.lineno, where))
    def visit_If(self, n): self._check(n.test,"if"); self.generic_visit(n)
    def visit_While(self, n): self._check(n.test,"while"); self.generic_visit(n)
    def visit_BoolOp(self, n):
        for v in n.values: self._check(v,"bool-op")
        self.generic_visit(n)
    def visit_UnaryOp(self, n):
        if isinstance(n.op, ast.Not): self._check(n.operand,"not")
        self.generic_visit(n)
tot=0
for root in sys.argv[1:]:
    for f in sorted(pathlib.Path(root).rglob("*.py")):
        try: t=ast.parse(f.read_text())
        except Exception: continue
        v=V(); v.visit(t)
        if v.hits:
            seen=sorted(set(v.hits)); tot+=len(seen)
            print(f"  {f}: {len(seen)}")
print("TOTAL", tot)
