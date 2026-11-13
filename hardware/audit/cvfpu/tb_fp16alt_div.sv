// Directed test of DIV on FP16ALT (bfloat16) through fpnew_top with the default configuration
// (Features RV64D_Xsflt, Implementation DEFAULT_NOREGS, DivSqrtSel THMULTI).
//
// Vector file, one request per line, hexadecimal:   a b rm result flags
//   a, b     operands, 16-bit patterns (applied NaN-boxed in 64 bits)
//   rm       rounding mode: 0 RNE, 1 RTZ, 2 RDN, 3 RUP, 4 RMM
//   result   expected 16-bit result (expected NaN-boxed in 64 bits)
//   flags    expected status {NV, DZ, OF, UF, NX}
// The file name comes from +vectors=FILE (default fp16alt_div_vectors.txt).
// The test ends with $fatal when a result or a flag word differs.
module tb_fp16alt_div;

  logic                    clk = 1'b0;
  logic                    rst_n = 1'b0;
  logic [2:0][63:0]        operands;
  fpnew_pkg::roundmode_e   rnd_mode;
  logic                    in_valid, in_ready;
  logic [63:0]             result;
  fpnew_pkg::status_t      status;
  logic                    tag, out_valid, busy, early_valid;

  fpnew_top #(
    .Features       ( fpnew_pkg::RV64D_Xsflt    ),
    .Implementation ( fpnew_pkg::DEFAULT_NOREGS ),
    .DivSqrtSel     ( fpnew_pkg::THMULTI        ),
    .TagType        ( logic                     )
  ) dut (
    .clk_i          ( clk                ),
    .rst_ni         ( rst_n              ),
    .operands_i     ( operands           ),
    .rnd_mode_i     ( rnd_mode           ),
    .op_i           ( fpnew_pkg::DIV     ),
    .op_mod_i       ( 1'b0               ),
    .src_fmt_i      ( fpnew_pkg::FP16ALT ),
    .dst_fmt_i      ( fpnew_pkg::FP16ALT ),
    .int_fmt_i      ( fpnew_pkg::INT64   ),
    .vectorial_op_i ( 1'b0               ),
    .tag_i          ( 1'b0               ),
    .simd_mask_i    ( '1                 ),
    .in_valid_i     ( in_valid           ),
    .in_ready_o     ( in_ready           ),
    .flush_i        ( 1'b0               ),
    .result_o       ( result             ),
    .status_o       ( status             ),
    .tag_o          ( tag                ),
    .out_valid_o    ( out_valid          ),
    .out_ready_i    ( 1'b1               ),
    .busy_o         ( busy               ),
    .early_valid_o  ( early_valid        )
  );

  always #5 clk = ~clk;

  string       file;
  int          fd, got, vectors, wrong_value, wrong_flags, waited;
  logic [15:0] a, b, want;
  logic [2:0]  rm;
  logic [4:0]  want_flags;

  initial begin
    if (!$value$plusargs("vectors=%s", file)) file = "fp16alt_div_vectors.txt";
    fd = $fopen(file, "r");
    if (fd == 0) $fatal(1, "cannot open %s", file);
    in_valid = 1'b0;
    operands = '0;
    rnd_mode = fpnew_pkg::RNE;
    repeat (4) @(posedge clk);
    rst_n = 1'b1;
    repeat (2) @(posedge clk);
    vectors = 0; wrong_value = 0; wrong_flags = 0;
    forever begin
      got = $fscanf(fd, "%h %h %h %h %h", a, b, rm, want, want_flags);
      if (got != 5) break;
      @(negedge clk);
      operands[0] = {48'hffff_ffff_ffff, a};
      operands[1] = {48'hffff_ffff_ffff, b};
      operands[2] = '0;
      rnd_mode    = fpnew_pkg::roundmode_e'(rm);
      in_valid    = 1'b1;
      @(posedge clk);
      while (!in_ready) @(posedge clk);          // request taken at this edge
      @(negedge clk);
      in_valid = 1'b0;
      waited = 0;
      while (!out_valid) begin
        @(negedge clk);
        waited++;
        if (waited > 300) $fatal(1, "no result for %h / %h", a, b);
      end
      vectors++;
      if (result !== {48'hffff_ffff_ffff, want}) begin
        wrong_value++;
        if (wrong_value <= 10)
          $display("value: %h / %h rm %0d: result %h, expected %h; flags %b, expected %b", a, b, rm, result[15:0], want, status, want_flags);
      end else if (status !== want_flags) begin
        wrong_flags++;
        if (wrong_flags <= 10)
          $display("flags: %h / %h rm %0d: result %h; flags %b, expected %b", a, b, rm, result[15:0], status, want_flags);
      end
      @(posedge clk);
    end
    $display("%0d vectors, %0d with a wrong result, %0d with the right result and wrong flags", vectors, wrong_value, wrong_flags);
    if (wrong_value != 0 || wrong_flags != 0) $fatal(1, "FP16ALT DIV test failed");
    $display("FP16ALT DIV test passed");
    $finish;
  end

endmodule
