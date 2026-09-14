module ioapic_boot_intx (
	irq_in,
	cfg_mask,
	boot_intx_en,
	reroute,
	pic_irq
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_IRQS = 24;
	parameter signed [31:0] NUM_PIC = 8;
	parameter signed [31:0] PIC_IDX_W = 4;
	function automatic signed [PIC_IDX_W - 1:0] sv2v_cast_8F1C4_signed;
		input reg signed [PIC_IDX_W - 1:0] inp;
		sv2v_cast_8F1C4_signed = inp;
	endfunction
	parameter [(NUM_IRQS * PIC_IDX_W) - 1:0] PIC_MAP = {NUM_IRQS {sv2v_cast_8F1C4_signed(NUM_PIC)}};
	input wire [NUM_IRQS - 1:0] irq_in;
	input wire [NUM_IRQS - 1:0] cfg_mask;
	input wire boot_intx_en;
	output wire [NUM_IRQS - 1:0] reroute;
	output reg [NUM_PIC - 1:0] pic_irq;
	assign reroute = (irq_in & cfg_mask) & {NUM_IRQS {boot_intx_en}};
	always @(*) begin
		if (_sv2v_0)
			;
		pic_irq = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] m;
			for (m = 0; m < NUM_PIC; m = m + 1)
				begin : sv2v_autoblock_2
					reg signed [31:0] i;
					for (i = 0; i < NUM_IRQS; i = i + 1)
						if (PIC_MAP[i * PIC_IDX_W+:PIC_IDX_W] == sv2v_cast_8F1C4_signed(m))
							pic_irq[m] = pic_irq[m] | reroute[i];
				end
		end
	end
	initial begin : param_check
		if (NUM_IRQS < 1)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_boot_intx.sv:105:13 - ioapic_boot_intx.param_check.<unnamed_block>\n msg: ", $time, "ioapic_boot_intx: NUM_IRQS must be >= 1, got %0d", NUM_IRQS);
		if (NUM_PIC < 1)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_boot_intx.sv:108:13 - ioapic_boot_intx.param_check.<unnamed_block>\n msg: ", $time, "ioapic_boot_intx: NUM_PIC must be >= 1, got %0d", NUM_PIC);
		if ((1 << PIC_IDX_W) <= NUM_PIC)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_boot_intx.sv:111:13 - ioapic_boot_intx.param_check.<unnamed_block>\n msg: ", $time, "ioapic_boot_intx: PIC_IDX_W=%0d cannot hold NUM_PIC=%0d plus a no-reroute code", PIC_IDX_W, NUM_PIC);
	end
	initial _sv2v_0 = 0;
endmodule
