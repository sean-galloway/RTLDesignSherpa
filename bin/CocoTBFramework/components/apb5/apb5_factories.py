# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APB5Factories
# Purpose: Factory functions for creating APB5 BFM components
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""Factory functions for creating APB5 BFM components."""

from typing import Optional, List, Dict, Any, Callable

from ..shared.flex_randomizer import FlexRandomizer
from .apb5_components import APB5Monitor, APB5Slave, APB5Master


def create_apb5_master(
    entity,
    title: str,
    prefix: str,
    clock,
    bus_width: int = 32,
    addr_width: int = 12,
    auser_width: int = 4,
    wuser_width: int = 4,
    ruser_width: int = 4,
    buser_width: int = 4,
    log=None,
    **kwargs
) -> APB5Master:
    """
    Create an APB5 Master BFM.

    Args:
        entity: The DUT entity
        title: Name/title for the master
        prefix: Signal prefix for APB signals
        clock: Clock signal
        bus_width: Data bus width in bits
        addr_width: Address width in bits
        auser_width: PAUSER width in bits
        wuser_width: PWUSER width in bits
        ruser_width: PRUSER width in bits
        buser_width: PBUSER width in bits
        log: Logger instance
        **kwargs: Additional arguments passed to APB5Master

    Returns:
        APB5Master instance
    """
    return APB5Master(
        entity=entity,
        title=title,
        prefix=prefix,
        clock=clock,
        bus_width=bus_width,
        addr_width=addr_width,
        auser_width=auser_width,
        wuser_width=wuser_width,
        ruser_width=ruser_width,
        buser_width=buser_width,
        log=log,
        **kwargs
    )


def create_apb5_slave(
    entity,
    title: str,
    prefix: str,
    clock,
    registers: List[int],
    bus_width: int = 32,
    addr_width: int = 12,
    auser_width: int = 4,
    wuser_width: int = 4,
    ruser_width: int = 4,
    buser_width: int = 4,
    randomizer: Optional[FlexRandomizer] = None,
    log=None,
    error_overflow: bool = False,
    wakeup_generator: Optional[Callable] = None,
    **kwargs
) -> APB5Slave:
    """
    Create an APB5 Slave BFM.

    Args:
        entity: The DUT entity
        title: Name/title for the slave
        prefix: Signal prefix for APB signals
        clock: Clock signal
        registers: Initial register values
        bus_width: Data bus width in bits
        addr_width: Address width in bits
        auser_width: PAUSER width in bits
        wuser_width: PWUSER width in bits
        ruser_width: PRUSER width in bits
        buser_width: PBUSER width in bits
        randomizer: Optional randomizer for delays and user signals
        log: Logger instance
        error_overflow: Whether to generate error on address overflow
        wakeup_generator: Optional function to generate wakeup events
        **kwargs: Additional arguments passed to APB5Slave

    Returns:
        APB5Slave instance
    """
    return APB5Slave(
        entity=entity,
        title=title,
        prefix=prefix,
        clock=clock,
        registers=registers,
        bus_width=bus_width,
        addr_width=addr_width,
        auser_width=auser_width,
        wuser_width=wuser_width,
        ruser_width=ruser_width,
        buser_width=buser_width,
        randomizer=randomizer,
        log=log,
        error_overflow=error_overflow,
        wakeup_generator=wakeup_generator,
        **kwargs
    )


def create_apb5_monitor(
    entity,
    title: str,
    prefix: str,
    clock,
    bus_width: int = 32,
    addr_width: int = 12,
    auser_width: int = 4,
    wuser_width: int = 4,
    ruser_width: int = 4,
    buser_width: int = 4,
    log=None,
    **kwargs
) -> APB5Monitor:
    """
    Create an APB5 Monitor.

    Args:
        entity: The DUT entity
        title: Name/title for the monitor
        prefix: Signal prefix for APB signals
        clock: Clock signal
        bus_width: Data bus width in bits
        addr_width: Address width in bits
        auser_width: PAUSER width in bits
        wuser_width: PWUSER width in bits
        ruser_width: PRUSER width in bits
        buser_width: PBUSER width in bits
        log: Logger instance
        **kwargs: Additional arguments passed to APB5Monitor

    Returns:
        APB5Monitor instance
    """
    return APB5Monitor(
        entity=entity,
        title=title,
        prefix=prefix,
        clock=clock,
        bus_width=bus_width,
        addr_width=addr_width,
        auser_width=auser_width,
        wuser_width=wuser_width,
        ruser_width=ruser_width,
        buser_width=buser_width,
        log=log,
        **kwargs
    )


def create_apb5_randomizer(
    ready_delay_weights: Optional[Dict[str, Any]] = None,
    error_weights: Optional[Dict[str, Any]] = None,
    ruser_width: int = 4,
    buser_width: int = 4,
) -> FlexRandomizer:
    """
    Create a randomizer for APB5 slave responses.

    Args:
        ready_delay_weights: Custom weights for ready delay
        error_weights: Custom weights for error generation
        ruser_width: Width of PRUSER field
        buser_width: Width of PBUSER field

    Returns:
        FlexRandomizer configured for APB5
    """
    config = {}

    if ready_delay_weights is None:
        config['ready'] = ([(0, 1), (2, 5), (6, 10)], [5, 2, 1])
    else:
        config['ready'] = ready_delay_weights

    if error_weights is None:
        config['error'] = ([(0, 0), (1, 1)], [10, 0])
    else:
        config['error'] = error_weights

    config['pruser'] = ([(0, (1 << ruser_width) - 1)], [1])
    config['pbuser'] = ([(0, (1 << buser_width) - 1)], [1])

    return FlexRandomizer(config)
