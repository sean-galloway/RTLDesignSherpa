"""
Predefined signal groups for common protocols
"""

class CommonGroups:
    """Reusable signal groupings for standard protocols"""

    # Basic control signals
    CONTROL = {
        "Control": ["clk", "rst_n", "en"]
    }

    # AXI protocol signals
    AXI_WRITE = {
        "AXI Write": ["awvalid", "awready", "awaddr", "awlen", "awsize",
                      "wvalid", "wready", "wdata", "wstrb", "wlast",
                      "bvalid", "bready", "bresp"]
    }

    AXI_READ = {
        "AXI Read": ["arvalid", "arready", "araddr", "arlen", "arsize",
                    "rvalid", "rready", "rdata", "rresp", "rlast"]
    }

    AXI_LITE = {
        "AXI-Lite": ["awvalid", "awready", "awaddr", "awprot",
                     "wvalid", "wready", "wdata", "wstrb",
                     "bvalid", "bready", "bresp",
                     "arvalid", "arready", "araddr", "arprot",
                     "rvalid", "rready", "rdata", "rresp"]
    }

    # APB protocol signals
    APB = {
        "APB": ["psel", "penable", "paddr", "pwrite", "pwdata", "prdata", "pready", "pslverr"]
    }

    # Basic handshake protocols
    HANDSHAKE = {
        "Handshake": ["valid", "ready"]
    }

    REQ_ACK = {
        "Request-Acknowledge": ["req", "ack"]
    }

    # Memory interface signals
    MEMORY = {
        "Memory": ["addr", "wdata", "rdata", "we", "cs"]
    }

    # Common state machine signals
    STATE_MACHINE = {
        "State Machine": ["state", "next_state", "done", "busy", "error"]
    }

    # SPI protocol signals
    SPI = {
        "SPI": ["sclk", "mosi", "miso", "ss_n"]
    }

    # I2C protocol signals
    I2C = {
        "I2C": ["scl", "sda"]
    }

    # UART protocol signals
    UART = {
        "UART": ["tx", "rx", "tx_en", "rx_en"]
    }

    @staticmethod
    def combine(*groups):
        """
        Combine multiple signal groups into a single dictionary

        Args:
            *groups: Group dictionaries to combine

        Returns:
            Combined dictionary of all groups
        """
        result = {}
        for group in groups:
            result |= group
        return result

    @staticmethod
    def custom(name, signals):
        """
        Create a custom signal group

        Args:
            name: Group name
            signals: List of signal names

        Returns:
            Dictionary with custom group
        """
        return {name: signals}

