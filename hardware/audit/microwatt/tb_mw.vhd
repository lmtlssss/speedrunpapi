-- Drives Microwatt's fpu.vhdl at its own port, one instruction per line of a vector file.
--
-- A line of the vector file:   K INSN FLAGS FRA FRB FRC
--   K      0 OP_FP_ARITH, 1 OP_FP_CMP, 2 OP_FP_MISC, 3 OP_FP_MOVE, 4 OP_DIV, 5 OP_DIVE, 6 OP_MOD
--          (the decoder's insn_type)
--   INSN   the 32-bit instruction word, hex
--   FLAGS  two hex digits: bit 7 single (is_32bit), 6 is_signed, 5 valid_a, 4 valid_b, 3 valid_c,
--          2 out_cr, 1 rc, 0 oe
--   FRA FRB FRC   the three operand registers, hex, 64 bits (RA and RB for the integer divisions)
-- A line of the result file:   V I W C DATA CR CYCLES XOVS CRDATA CRMASK
--   V valid, I interrupt, W write_enable, C write_cr_enable, DATA write_data, CR one field of
--   write_cr_data, CYCLES clock edges from the request to the answer (9999: no answer),
--   XOVS write_xerc, OV, OV32, SO, then write_cr_data and write_cr_mask whole.
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

library work;
use work.decode_types.all;
use work.common.all;

entity tb_mw is
    generic (
        vecfile : string := "mw.vec";
        outfile : string := "mw.out"
        );
end entity tb_mw;

architecture sim of tb_mw is
    signal clk   : std_ulogic := '0';
    signal rst   : std_ulogic := '1';
    signal e_in  : Execute1ToFPUType := Execute1ToFPUInit;
    signal e_out : FPUToExecute1Type;
    signal w_out : FPUToWritebackType;
    signal done  : boolean := false;
begin
    dut: entity work.fpu
        port map (
            clk => clk,
            rst => rst,
            flush_in => '0',
            e_in => e_in,
            e_out => e_out,
            w_out => w_out
            );

    clock: process
    begin
        while not done loop
            clk <= '0';
            wait for 5 ns;
            clk <= '1';
            wait for 5 ns;
        end loop;
        wait;
    end process;

    stim: process
        file vf    : text open read_mode is vecfile;
        file outf  : text open write_mode is outfile;
        variable l, lo : line;
        variable k     : integer;
        variable insn  : std_ulogic_vector(31 downto 0);
        variable flags : std_ulogic_vector(7 downto 0);
        variable fa, fb, fc : std_ulogic_vector(63 downto 0);
        variable n     : integer;
        variable v     : Execute1ToFPUType;
        variable bits  : std_ulogic_vector(3 downto 0);
        variable xbits : std_ulogic_vector(3 downto 0);
    begin
        for i in 1 to 4 loop
            wait until rising_edge(clk);
        end loop;
        rst <= '0';
        wait until rising_edge(clk);
        wait until rising_edge(clk);
        while not endfile(vf) loop
            readline(vf, l);
            read(l, k);
            hread(l, insn);
            hread(l, flags);
            hread(l, fa);
            hread(l, fb);
            hread(l, fc);
            v := Execute1ToFPUInit;
            v.valid := '1';
            case k is
                when 0 => v.op := OP_FP_ARITH;
                when 1 => v.op := OP_FP_CMP;
                when 2 => v.op := OP_FP_MISC;
                when 4 => v.op := OP_DIV;
                when 5 => v.op := OP_DIVE;
                when 6 => v.op := OP_MOD;
                when others => v.op := OP_FP_MOVE;
            end case;
            v.insn := insn;
            v.oe := flags(0);
            v.single := flags(7);
            v.is_signed := flags(6);
            v.valid_a := flags(5);
            v.valid_b := flags(4);
            v.valid_c := flags(3);
            v.out_cr := flags(2);
            v.rc := flags(1);
            v.fra := fa;
            v.frb := fb;
            v.frc := fc;
            v.frt := "100001";
            v.itag.valid := '1';
            v.itag.tag := 1;
            e_in <= v;
            wait until rising_edge(clk);
            e_in.valid <= '0';
            n := 0;
            loop
                wait until rising_edge(clk);
                n := n + 1;
                exit when w_out.valid = '1' or w_out.interrupt = '1';
                if n > 4000 then
                    n := 9999;
                    exit;
                end if;
            end loop;
            bits := w_out.valid & w_out.interrupt & w_out.write_enable & w_out.write_cr_enable;
            write(lo, bits);
            write(lo, string'(" "));
            hwrite(lo, w_out.write_data);
            write(lo, string'(" "));
            hwrite(lo, w_out.write_cr_data(3 downto 0));
            write(lo, string'(" "));
            write(lo, n);
            write(lo, string'(" "));
            xbits := w_out.write_xerc & w_out.xerc.ov & w_out.xerc.ov32 & w_out.xerc.so;
            write(lo, xbits);
            write(lo, string'(" "));
            hwrite(lo, w_out.write_cr_data);
            write(lo, string'(" "));
            hwrite(lo, w_out.write_cr_mask);
            writeline(outf, lo);
            wait until rising_edge(clk);
        end loop;
        done <= true;
        wait;
    end process;
end architecture sim;
