# arbiter_fixed_priority

`arbiter_fixed_priority` is a SystemVerilog module located at `rtl/common/arbiter_fixed_priority.sv`. This module implements a fixed-priority arbiter that grants access to a number of clients based on a fixed priority scheme, where lower-indexed clients have higher priority. It is parameterized to be easily scalable for different numbers of clients.

## Code Listing

```verilog
`timescale 1ns / 1ps

// Based on the design from:
// https://chipress.online/?s=fixed_prio_arb
// Tweaks and parameterization have been applied to the original design.

module arbiter_fixed_priority #(
    parameter int CLIENTS = 8 // Parameter to set the number of clients.
) (
    input        [CLIENTS-1:0] i_req,     // Input requests from clients.
    output logic [CLIENTS-1:0] ow_grant   // Output grants for clients.
);

    logic w_found; // Working variable to indicate if a grant has been found.

    // Combinatorial logic to determine which client is granted access.
    always_comb begin
        ow_grant = {CLIENTS{1'b0}}; // Initialize all grants to 0.
        w_found  = 1'b0; // Reset the found flag for each evaluation.
        for (int i = 0; i < CLIENTS; i++) begin // Iterate over the clients.
            if (i_req[i] && !w_found) begin // Check if client i is requesting and no grant has been found yet.
                ow_grant[i] = 1'b1; // Grant access to the current client.
                w_found = 1'b1; // Set the found flag to prevent further grants.
            end
        end
    end

endmodule : arbiter_fixed_priority
```

## Functionality

- **Clients (`CLIENTS`):** The module is parameterized with an integer `CLIENTS` to support a flexible number of clients. The default number of clients is set to 8 but can be configured as needed.

- **Input Requests (`i_req`):** An array of request signals from each client, where the index of the array corresponds to the client ID. A '1' indicates that the client is requesting access.

- **Output Grants (`ow_grant`):** An array of grant signals to each client, where only one client will be granted access at a time based on the fixed priority order.

## Operation

1. All grants are initially set to '0' at the beginning of each cycle.
2. The module checks each client's request signal, starting from client 0 (the highest priority) to `CLIENTS-1` (the lowest priority).
3. The first client (in priority order) that has an active request (`i_req[i]` is '1') and no other client has been granted access yet, will be granted access by setting `ow_grant[i]` to '1'.
4. Once a grant has been given (`w_found` is '1'), no other grants will be issued during that cycle, ensuring only one client is granted access.

## Usage

To use this module, instantiate it in your SystemVerilog design and specify the `CLIENTS` parameter if a number other than the default is needed. Connect the `i_req` signals from your clients to the inputs and route the `ow_grant` outputs to control logic that uses the arbitration result.

```verilog
arbiter_fixed_priority #( .CLIENTS(4) ) arb_inst (
    .i_req(client_requests), // Replace with actual request signals
    .ow_grant(client_grants) // Connect to arbiter-dependent logic
);
```

## Note

Ensure that `timescale` directive (1ns / 1ps) matches the time unit and precision used in your design to ensure proper timing simulation.

---
[Return to Index](index.md)

