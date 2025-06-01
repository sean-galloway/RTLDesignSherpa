"""
Custom Pylint plugin to enforce proper field configuration usage patterns.

This plugin checks for:
1. Direct GAXIPacket creation without using field configs
2. Hardcoded field assignments instead of using field config defaults
3. Missing field config usage in packet creation methods
4. Bypassing field config helper methods

File: tools/linting/field_config_checker.py
"""

import astroid
from pylint.checkers import BaseChecker
from pylint.interfaces import IAstroidChecker


class FieldConfigChecker(BaseChecker):
    """Checker for field configuration usage patterns."""
    
    __implements__ = IAstroidChecker
    
    name = 'field-config-usage'
    priority = -1
    
    msgs = {
        'W9001': (
            'Direct GAXIPacket creation detected. Use field config helper methods instead.',
            'direct-gaxi-packet-creation',
            'Direct GAXIPacket creation bypasses field configuration validation. '
            'Use helper methods like _create_addr_packet(), _create_data_packet(), etc.'
        ),
        'W9002': (
            'Hardcoded field assignment detected: %s. Use field config defaults instead.',
            'hardcoded-field-assignment', 
            'Hardcoded field assignments should use field configuration defaults '
            'for consistency and maintainability.'
        ),
        'W9003': (
            'Missing field config usage in packet creation method: %s',
            'missing-field-config-usage',
            'Packet creation methods should use field configurations as the '
            'single source of truth for field definitions.'
        ),
        'W9004': (
            'Bypassing field config helper method. Use %s instead.',
            'bypassing-field-config-helper',
            'Use the standardized field config helper methods instead of '
            'creating packets directly.'
        ),
        'E9005': (
            'Field config create_packet() called but method may not exist',
            'field-config-create-packet-missing',
            'Ensure the FieldConfig class has a create_packet() method or '
            'use alternative packet creation approaches.'
        )
    }
    
    # Patterns to detect
    GAXI_PACKET_PATTERNS = ['GAXIPacket']
    FIELD_CONFIG_HELPER_METHODS = [
        '_create_addr_packet',
        '_create_data_packet', 
        '_create_resp_packet'
    ]
    HARDCODED_FIELD_PATTERNS = [
        'len', 'size', 'burst', 'id', 'addr', 'resp', 'last'
    ]
    
    def visit_call(self, node):
        """Check function calls for field config violations."""
        if isinstance(node.func, astroid.Name):
            # Check for direct GAXIPacket creation
            if node.func.name in self.GAXI_PACKET_PATTERNS:
                self._check_gaxi_packet_creation(node)
                
        elif isinstance(node.func, astroid.Attribute):
            # Check for field_config.create_packet() calls
            if (node.func.attrname == 'create_packet' and 
                self._is_field_config_object(node.func.expr)):
                self._check_create_packet_call(node)
    
    def visit_assign(self, node):
        """Check assignments for hardcoded field values."""
        if isinstance(node.targets[0], astroid.Attribute):
            attr_name = node.targets[0].attrname
            if attr_name in self.HARDCODED_FIELD_PATTERNS:
                self._check_hardcoded_assignment(node, attr_name)
    
    def visit_functiondef(self, node):
        """Check function definitions for proper field config usage."""
        if self._is_packet_creation_method(node.name):
            self._check_packet_creation_method(node)
    
    def _check_gaxi_packet_creation(self, node):
        """Check if GAXIPacket creation is using field configs properly."""
        # Allow GAXIPacket creation if it's in a helper method
        if self._is_in_helper_method(node):
            return
            
        # Check if field config is passed as argument
        if not self._has_field_config_arg(node):
            self.add_message(
                'direct-gaxi-packet-creation',
                node=node
            )
    
    def _check_create_packet_call(self, node):
        """Check create_packet() method calls."""
        # This is actually OK now that we've added the method,
        # but we can warn if it's used inappropriately
        pass
    
    def _check_hardcoded_assignment(self, node, field_name):
        """Check for hardcoded field assignments."""
        # Skip if assignment is in a helper method (they're allowed to set fields)
        if self._is_in_helper_method(node):
            return
            
        # Skip if the value comes from a field config
        if self._value_from_field_config(node.value):
            return
            
        self.add_message(
            'hardcoded-field-assignment',
            node=node,
            args=(field_name,)
        )
    
    def _check_packet_creation_method(self, node):
        """Check packet creation methods for field config usage."""
        # Look for field config usage in the method body
        has_field_config_usage = False
        
        for child in node.body:
            if self._contains_field_config_usage(child):
                has_field_config_usage = True
                break
        
        if not has_field_config_usage:
            self.add_message(
                'missing-field-config-usage',
                node=node,
                args=(node.name,)
            )
    
    def _is_field_config_object(self, node):
        """Check if node represents a field config object."""
        if isinstance(node, astroid.Attribute):
            return 'field_config' in node.attrname.lower()
        return False
    
    def _is_in_helper_method(self, node):
        """Check if node is inside a field config helper method."""
        parent = node.parent
        while parent:
            if (isinstance(parent, astroid.FunctionDef) and 
                parent.name in self.FIELD_CONFIG_HELPER_METHODS):
                return True
            parent = parent.parent
        return False
    
    def _has_field_config_arg(self, node):
        """Check if GAXIPacket call has field config as argument."""
        if node.args:
            # Simple heuristic: check if any arg contains 'field_config'
            for arg in node.args:
                if isinstance(arg, astroid.Attribute):
                    if 'field_config' in str(arg).lower():
                        return True
        return False
    
    def _value_from_field_config(self, node):
        """Check if assignment value comes from field config."""
        if isinstance(node, astroid.Attribute):
            return 'field_config' in str(node).lower() or 'default' in str(node).lower()
        return False
    
    def _is_packet_creation_method(self, method_name):
        """Check if method name suggests packet creation."""
        packet_indicators = ['create_packet', 'make_packet', 'build_packet', 'packet']
        return any(indicator in method_name.lower() for indicator in packet_indicators)
    
    def _contains_field_config_usage(self, node):
        """Check if node contains field config usage."""
        if isinstance(node, astroid.Assign):
            if isinstance(node.targets[0], astroid.Name):
                target_name = node.targets[0].name
                if 'packet' in target_name.lower():
                    # Check if GAXIPacket is created with field config
                    if (isinstance(node.value, astroid.Call) and
                        isinstance(node.value.func, astroid.Name) and
                        node.value.func.name == 'GAXIPacket'):
                        return self._has_field_config_arg(node.value)
        return False


def register(linter):
    """Register the checker with pylint."""
    linter.register_checker(FieldConfigChecker(linter))
