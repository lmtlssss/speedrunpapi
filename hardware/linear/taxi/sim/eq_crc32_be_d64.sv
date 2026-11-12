module eqbe; logic [63:0] d, dz; logic [31:0] s, a, b, ref_o; logic [2:0] e; logic [31:0] st [0:8]; int bad=0;
  assign st[0]=s;
  for (genvar i=0;i<8;i++) begin: g taxi_lfsr #(.LFSR_W(32),.LFSR_POLY(32'h4c11db7),.LFSR_GALOIS(1),.LFSR_FEED_FORWARD(0),.REVERSE(1),.DATA_W(8),.DATA_IN_EN(1'b1),.DATA_OUT_EN(1'b0)) u(.data_in(d[8*i +: 8]),.state_in(st[i]),.data_out(),.state_out(st[i+1])); end
  assign ref_o = st[8-e];
  always_comb for (int i=0;i<8;i++) dz[8*i +: 8] = (i < 8-e) ? d[8*i +: 8] : 8'd0;
  crc32_be_d64 p(.data_in(dz),.state_in(s),.empty(e),.state_out(a)); crc32_be_d64_lut6 q(.data_in(dz),.state_in(s),.empty(e),.state_out(b));
  initial begin for (int i=0;i<200000;i++) begin d={$urandom,$urandom}; s=$urandom; e=$urandom; if (i<8) begin d='1; s='1; e=i; end #1 if (a!==ref_o || b!==ref_o) bad++; end $display("R %0d",bad); $finish; end
endmodule
