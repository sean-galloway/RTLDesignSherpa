`timescale 1ns / 1ps

// a generic parity generator
module dataint_parity #(
    parameter int CHUNKS = 4,  // Number of Chunks to check parity
    parameter int WIDTH  = 32  // Total Width of the Data
) (
    input  logic [ WIDTH-1:0] i_data,         // data in
    input  logic [CHUNKS-1:0] i_parity,       // parity in for checking
    input  logic              i_parity_type,  // 1=even, 0=odd
    output logic [CHUNKS-1:0] ow_parity,
    output logic [CHUNKS-1:0] ow_error        // error indicator, valid only if used for checking
);

    localparam int ChunkSize = WIDTH / CHUNKS;
    localparam int ExtraBits = WIDTH % CHUNKS;

    genvar i;
    generate
        for (i = 0; i < CHUNKS; i++) begin : gen_parity
            // Bounds are calculated statically for each iteration of the loop
            localparam int LowerBound = i * ChunkSize;
            localparam int UpperBound = (i < CHUNKS - 1) ? ((i + 1) * ChunkSize) - 1 : WIDTH - 1;

            // Utilize lower_bound and upper_bound as needed here, for example:
            wire calculated_parity = i_parity_type ? ^i_data[UpperBound:LowerBound] :
                                                    ~^i_data[UpperBound:LowerBound];
            assign ow_parity[i] = calculated_parity;
            assign ow_error[i]  = (calculated_parity != i_parity[i]);
        end
    endgenerate

    // Synopsys translate_off
    // Synopsys translate_on

endmodule : dataint_parity
