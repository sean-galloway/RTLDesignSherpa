 // Code from "Low Power Design Methodologies and Flows"
 module icg(/*AUTOARG*/
   // Outputs
   gclk,
   // Inputs
   en, clk
   );
    input en;
    input clk;
    output gclk;

    reg    en_out;

    always @(en or clk) begin
       if (!clk) begin
          en_out = en;
       end
    end
    assign gclk = en_out && clk;
 endmodule // icg
