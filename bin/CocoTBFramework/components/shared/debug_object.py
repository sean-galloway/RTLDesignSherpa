# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: debug_object
# Purpose: Returns a dictionary with all attributes of the given object,
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

def get_object_details(obj):
    """
    Returns a dictionary with all attributes of the given object,
    including their types and values.

    Args:
        obj: The object to inspect

    Returns:
        Dictionary with attribute names as keys, and dictionaries containing
        'type' and 'value' as values
    """
    result = {}

    # Get all attributes, including inherited ones
    for attr_name in dir(obj):
        # Skip private attributes (those starting with _)
        if attr_name.startswith('_'):
            continue

        try:
            # Get attribute value
            attr_value = getattr(obj, attr_name)

            # Skip methods and callable objects
            if callable(attr_value):
                continue

            # Store attribute type and value
            result[attr_name] = {
                'type': type(attr_value).__name__,
                'value': attr_value
            }
        except Exception as e:
            # Handle attributes that may raise exceptions when accessed
            result[attr_name] = {
                'type': 'Error',
                'value': f"Error accessing attribute: {str(e)}"
            }

    return result


def print_object_details(obj, log, name="Object", max_value_length=5000):
    """
    Prints formatted details of all attributes of the given object.

    Args:
        obj: The object to inspect
        name: A name to identify the object in the output
        max_value_length: Maximum length for printing attribute values
    """
    details = get_object_details(obj)

    log.debug(f"\n=== {name} Details ===")
    log.debug(f"Class: {type(obj).__name__}")
    log.debug(f"Total attributes: {len(details)}")
    log.debug("-" * 80)

    # Sort by attribute name
    for attr_name, info in sorted(details.items()):
        value_str = str(info['value'])
        if len(value_str) > max_value_length:
            value_str = f"{value_str[:max_value_length]}..."

        log.debug(f"{attr_name}: {info['type']} = {value_str}")

    log.debug("-" * 80)


def print_dict_to_log(name, d, log, prefix=""):
    """Print dictionary to logger with each key on its own line"""
    msg = f"\n=== {name} Details ===\n"
    lines = [f"{prefix}::{key}: {value}" for key, value in d.items()]
    log.debug(f'{msg}' + "\n".join(lines))
