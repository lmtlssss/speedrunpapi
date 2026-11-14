// Single cases on the modules XLS generated for the standard widths.
`timescale 1ns/1ps
module cases;
  reg [31:0] a32, b32, c32; wire [31:0] f32;
  reg [15:0] a16, b16, c16; wire [15:0] fbf, fh;
  reg [7:0] a8, b8, c8; wire [7:0] f43, f52;
  reg [31:0] x; wire [15:0] hz;
  fma_8_23 u32(.a(a32), .b(b32), .c(c32), .out(f32));
  fma_8_7 ubf(.a(a16), .b(b16), .c(c16), .out(fbf));
  fma_5_10 uh(.a(a16), .b(b16), .c(c16), .out(fh));
  fma_4_3 u43(.a(a8), .b(b8), .c(c8), .out(f43));
  fma_5_2 u52(.a(a8), .b(b8), .c(c8), .out(f52));
  fromfixed_rz_5_10_32 uz(.x(x), .out(hz));
  initial begin
    a32 = 32'h7fc00000; b32 = 32'h3f800000; c32 = 32'h3f800000; #1 $display("binary32 fma(qNaN, 1, 1)        = %h", f32);
    a32 = 32'h7f800000; b32 = 32'h00000000; c32 = 32'h3f800000; #1 $display("binary32 fma(inf, 0, 1)         = %h", f32);
    a32 = 32'h7f800000; b32 = 32'h3f800000; c32 = 32'hff800000; #1 $display("binary32 fma(inf, 1, -inf)      = %h", f32);
    a32 = 32'h00000000; b32 = 32'h80000000; c32 = 32'h80000000; #1 $display("binary32 fma(+0, -0, -0)        = %h", f32);
    a32 = 32'h3f800000; b32 = 32'h80000000; c32 = 32'h80000000; #1 $display("binary32 fma(1, -0, -0)         = %h", f32);
    a16 = 16'h7fc0; b16 = 16'h3f80; c16 = 16'h3f80; #1 $display("bfloat16 fma(qNaN, 1, 1)        = %h", fbf);
    a16 = 16'h7e00; b16 = 16'h3c00; c16 = 16'h3c00; #1 $display("binary16 fma(qNaN, 1, 1)        = %h", fh);
    a8 = 8'h7c; b8 = 8'h38; c8 = 8'h38; #1 $display("E4M3 layout fma(qNaN, 1, 1)     = %h", f43);
    a8 = 8'h78; b8 = 8'h00; c8 = 8'h38; #1 $display("E4M3 layout fma(inf, 0, 1)      = %h", f43);
    a8 = 8'h7e; b8 = 8'h3c; c8 = 8'h3c; #1 $display("E5M2 layout fma(qNaN, 1, 1)     = %h", f52);
    x = 32'd100000; #1 $display("binary16 from 100000, toward 0  = %h", hz);
    x = -32'd100000; #1 $display("binary16 from -100000, toward 0 = %h", hz);
    x = 32'd65535; #1 $display("binary16 from 65535, toward 0   = %h", hz);
    $finish;
  end
endmodule
