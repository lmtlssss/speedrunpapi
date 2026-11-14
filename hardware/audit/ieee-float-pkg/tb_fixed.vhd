-- One line in, one line out: an operation of ieee.fixed_pkg on operands of any index range.
--
--   in    op kind lh ll rh rl p1 p2 style ovf A B
--   out   "H L bits" for a fixed-point result with its index range, "I n" for an integer, "C lt eq" for a comparison
--
--   kind 0 ufixed, 1 sfixed; A is (lh downto ll), B is (rh downto rl), both as bit strings
--   style 0 fixed_round, 1 fixed_truncate; ovf 0 fixed_saturate, 1 fixed_wrap
--   op 0 +, 1 -, 2 *, 3 /, 4 divide with p1 guard bits, 5 reciprocal with p1 guard bits, 6 rem, 7 mod,
--      8 resize to (p1 downto p2), 9 to_integer, 10 scalb by p1, 11 unary minus, 12 abs, 13 "<" and "=",
--      14 add_carry with carry in p1
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.fixed_float_types.all;
use ieee.fixed_pkg.all;
library std;
use std.textio.all;

entity tb_fixed is
  generic (
    vecfile : string  := "vectors.txt";
    outfile : string  := "results.txt";
    skip    : natural := 0);
end;

architecture sim of tb_fixed is

  procedure put (lo : inout line; r : ufixed) is
  begin
    write (lo, string'("H "));
    write (lo, r'high);
    write (lo, string'(" "));
    write (lo, r'low);
    write (lo, string'(" "));
    write (lo, to_sulv (r));
  end procedure;

  procedure put (lo : inout line; r : sfixed) is
  begin
    write (lo, string'("H "));
    write (lo, r'high);
    write (lo, string'(" "));
    write (lo, r'low);
    write (lo, string'(" "));
    write (lo, to_sulv (r));
  end procedure;

  procedure flag (lo : inout line; b : boolean) is
  begin
    if b then
      write (lo, string'(" 1"));
    else
      write (lo, string'(" 0"));
    end if;
  end procedure;

  procedure unsigned_op (op, lh, ll, rh, rl, p1, p2 : integer; rs : fixed_round_style_type;
                         os : fixed_overflow_style_type; li, lo : inout line) is
    variable va  : std_ulogic_vector (lh - ll downto 0);
    variable vb  : std_ulogic_vector (rh - rl downto 0);
    variable a   : ufixed (lh downto ll);
    variable b   : ufixed (rh downto rl);
    variable sum : ufixed (maximum (lh, rh) downto minimum (ll, rl));
    variable co  : std_ulogic;
    variable ci  : std_ulogic;
  begin
    read (li, va);
    read (li, vb);
    a := to_ufixed (va, lh, ll);
    b := to_ufixed (vb, rh, rl);
    case op is
      when 0  => put (lo, a + b);
      when 1  => put (lo, a - b);
      when 2  => put (lo, a * b);
      when 3  => put (lo, a / b);
      when 4  => put (lo, divide (a, b, rs, p1));
      when 5  => put (lo, reciprocal (a, rs, p1));
      when 6  => put (lo, a rem b);
      when 7  => put (lo, a mod b);
      when 8  => put (lo, resize (a, p1, p2, os, rs));
      when 9  =>
        write (lo, string'("I "));
        write (lo, to_integer (a, os, rs));
      when 10 => put (lo, scalb (a, p1));
      when 13 =>
        write (lo, string'("C"));
        flag (lo, a < b);
        flag (lo, a = b);
      when others =>
        if p1 = 1 then
          ci := '1';
        else
          ci := '0';
        end if;
        add_carry (a, b, ci, sum, co);
        put (lo, sum);
        flag (lo, co = '1');
    end case;
  end procedure;

  procedure signed_op (op, lh, ll, rh, rl, p1, p2 : integer; rs : fixed_round_style_type;
                       os : fixed_overflow_style_type; li, lo : inout line) is
    variable va : std_ulogic_vector (lh - ll downto 0);
    variable vb : std_ulogic_vector (rh - rl downto 0);
    variable a  : sfixed (lh downto ll);
    variable b  : sfixed (rh downto rl);
  begin
    read (li, va);
    read (li, vb);
    a := to_sfixed (va, lh, ll);
    b := to_sfixed (vb, rh, rl);
    case op is
      when 0  => put (lo, a + b);
      when 1  => put (lo, a - b);
      when 2  => put (lo, a * b);
      when 3  => put (lo, a / b);
      when 4  => put (lo, divide (a, b, rs, p1));
      when 5  => put (lo, reciprocal (a, rs, p1));
      when 6  => put (lo, a rem b);
      when 7  => put (lo, a mod b);
      when 8  => put (lo, resize (a, p1, p2, os, rs));
      when 9  =>
        write (lo, string'("I "));
        write (lo, to_integer (a, os, rs));
      when 10 => put (lo, scalb (a, p1));
      when 11 => put (lo, -a);
      when 12 => put (lo, abs (a));
      when others =>
        write (lo, string'("C"));
        flag (lo, a < b);
        flag (lo, a = b);
    end case;
  end procedure;

begin
  process
    file fi                  : text open read_mode is vecfile;
    file fo                  : text open write_mode is outfile;
    variable lin, lout       : line;
    variable n_op, n_kind    : integer;
    variable n_lh, n_ll      : integer;
    variable n_rh, n_rl      : integer;
    variable n_p1, n_p2      : integer;
    variable n_style, n_ovf  : integer;
    variable rs              : fixed_round_style_type;
    variable os              : fixed_overflow_style_type;
  begin
    for i in 1 to skip loop
      readline (fi, lin);
    end loop;
    while not endfile (fi) loop
      readline (fi, lin);
      read (lin, n_op);
      read (lin, n_kind);
      read (lin, n_lh);
      read (lin, n_ll);
      read (lin, n_rh);
      read (lin, n_rl);
      read (lin, n_p1);
      read (lin, n_p2);
      read (lin, n_style);
      read (lin, n_ovf);
      if n_style = 0 then
        rs := fixed_round;
      else
        rs := fixed_truncate;
      end if;
      if n_ovf = 0 then
        os := fixed_saturate;
      else
        os := fixed_wrap;
      end if;
      if n_kind = 0 then
        unsigned_op (n_op, n_lh, n_ll, n_rh, n_rl, n_p1, n_p2, rs, os, lin, lout);
      else
        signed_op (n_op, n_lh, n_ll, n_rh, n_rl, n_p1, n_p2, rs, os, lin, lout);
      end if;
      writeline (fo, lout);
    end loop;
    wait;
  end process;
end;
