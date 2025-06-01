"""
Flake8 plugin for field configuration usage enforcement.

File: tools/linting/flake8_field_config.py
"""

import ast
import sys
from typing import Generator, Tuple, Type, Any


class FieldConfigVisitor(ast.NodeVisitor):
    """AST visitor for field config usage patterns."""
    
    def __init__(self):
        self.problems = []
    
    def visit_Call(self, node: ast.Call) -> None:
        """Visit function calls."""
        # Check for direct GAXIPacket creation
        if (isinstance(node.func, ast.Name) and 
            node.func.id == 'GAXIPacket'):
            self._check_gaxi_packet_call(node)
        
        # Check for field_config.create_packet() calls
        if (isinstance(node.func, ast.Attribute) and 
            node.func.attr == 'create_packet'):
            self._check_create_packet_call(node)
        
        self.generic_visit(node)
    
    def visit_Assign(self, node: ast.Assign) -> None:
        """Visit assignments."""
        for target in node.targets:
            if isinstance(target, ast.Attribute):
                self._check_hardcoded_field(node, target)
        
        self.generic_visit(node)
    
    def _check_gaxi_packet_call(self, node: ast.Call):
        """Check GAXIPacket creation."""
        # Simple check: if no args or first arg doesn't contain 'field_config'
        if not node.args:
            self.problems.append((
                node.lineno,
                node.col_offset,
                'FC001 Direct GAXIPacket creation without field config',
                type(self)
            ))
        else:
            # Check if field config is used
            first_arg = node.args[0]
            if not self._references_field_config(first_arg):
                self.problems.append((
                    node.lineno,
                    node.col_offset,
                    'FC001 GAXIPacket creation should use field config',
                    type(self)
                ))
    
    def _check_create_packet_call(self, node: ast.Call):
        """Check create_packet() calls."""
        # This is generally OK, but we could add specific checks
        pass
    
    def _check_hardcoded_field(self, node: ast.Assign, target: ast.Attribute):
        """Check for hardcoded field assignments."""
        hardcoded_fields = ['len', 'size', 'burst', 'id', 'addr', 'resp', 'last']
        
        if target.attr in hardcoded_fields:
            # Check if value is hardcoded (literal) vs from field config
            if isinstance(node.value, (ast.Constant, ast.Num)):
                self.problems.append((
                    node.lineno,
                    node.col_offset,
                    f'FC002 Hardcoded field assignment: {target.attr}',
                    type(self)
                ))
    
    def _references_field_config(self, node: ast.AST) -> bool:
        """Check if node references field config."""
        if isinstance(node, ast.Attribute):
            return 'field_config' in ast.dump(node).lower()
        elif isinstance(node, ast.Name):
            return 'field_config' in node.id.lower()
        return False


class FieldConfigChecker:
    """Flake8 checker for field configuration usage."""
    
    name = 'field-config-usage'
    version = '1.0.0'
    
    def __init__(self, tree: ast.AST, filename: str):
        self.tree = tree
        self.filename = filename
    
    def run(self) -> Generator[Tuple[int, int, str, Type[Any]], None, None]:
        """Run the checker."""
        visitor = FieldConfigVisitor()
        visitor.visit(self.tree)
        
        for line, col, msg, check in visitor.problems:
            yield line, col, msg, check
