-- One line in, one line out: an operation of ieee.float_pkg on operands of any format.
--
--   in    op style ew fw guard denormalize p1 p2 operands
--   out   the result in binary, or the integer for to_integer
--
-- A call that stops the simulator inside the package ends the run. The generic skip starts the next run behind
-- that line.
--
--   op 0 add, 1 subtract, 2 multiply, 3 divide, 4 sqrt, 5 mac, 6 reciprocal, 13 dividebyp2, 14 scalb by p1:
--        three operands in the format (ew, fw), result in the same format
--      7 resize to the format (p1, p2)
--      8 to_float of a signed number of p1 bits, 12 to_float of an integer (p1 is 32)
--      9 to_signed with p1 bits, 10 to_unsigned with p1 bits, 11 to_integer
--   style 0 round_nearest, 1 round_zero, 2 round_neginf, 3 round_inf
--   Operands are binary strings, sign first.
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.fixed_float_types.all;
use ieee.float_pkg.all;
library std;
use std.textio.all;

entity tb_float_pkg is
  generic (
    vecfile : string  := "vectors.txt";
    outfile : string  := "results.txt";
    skip    : natural := 0);            -- lines of vecfile to pass over first
end;

architecture sim of tb_float_pkg is

  procedure arith (op, ew, fw, guard, p1 : integer; style : round_type; denorm : boolean; li, lo : inout line) is
    variable va, vb, vc : std_ulogic_vector (ew + fw downto 0);
    variable a, b, c, r : float (ew downto -fw);
  begin
    read (li, va);
    read (li, vb);
    read (li, vc);
    a := to_float (va, ew, fw);
    b := to_float (vb, ew, fw);
    c := to_float (vc, ew, fw);
    case op is
      when 0      => r := add (a, b, style, guard, true, denorm);
      when 1      => r := subtract (a, b, style, guard, true, denorm);
      when 2      => r := multiply (a, b, style, guard, true, denorm);
      when 3      => r := divide (a, b, style, guard, true, denorm);
      when 4      => r := sqrt (a, style, guard, true, denorm);
      when 5      => r := mac (a, b, c, style, guard, true, denorm);
      when 6      => r := reciprocal (a, style, guard, true, denorm);
      when 13     => r := dividebyp2 (a, b, style, guard, true, denorm);
      when others => r := scalb (a, p1, style, true, denorm);
    end case;
    write (lo, to_sulv (r));
  end procedure;

  procedure narrow (ew, fw, p1, p2 : integer; style : round_type; denorm : boolean; li, lo : inout line) is
    variable va : std_ulogic_vector (ew + fw downto 0);
    variable r  : float (p1 downto -p2);
  begin
    read (li, va);
    r := resize (to_float (va, ew, fw), p1, p2, style, true, denorm, denorm);
    write (lo, to_sulv (r));
  end procedure;

  procedure from_int (op, ew, fw, p1 : integer; style : round_type; li, lo : inout line) is
    variable va : std_ulogic_vector (p1 - 1 downto 0);
    variable r  : float (ew downto -fw);
  begin
    read (li, va);
    if op = 8 then
      r := to_float (signed (va), ew, fw, style);
    else
      r := to_float (to_integer (signed (va)), ew, fw, style);
    end if;
    write (lo, to_sulv (r));
  end procedure;

  procedure to_int (op, ew, fw, p1 : integer; style : round_type; li, lo : inout line) is
    variable va : std_ulogic_vector (ew + fw downto 0);
    variable a  : float (ew downto -fw);
  begin
    read (li, va);
    a := to_float (va, ew, fw);
    case op is
      when 9      => write (lo, std_ulogic_vector (to_signed (a, p1, style)));
      when 10     => write (lo, std_ulogic_vector (to_unsigned (a, p1, style)));
      when others => write (lo, to_integer (a, style));
    end case;
  end procedure;

begin
  process
    file fi                 : text open read_mode is vecfile;
    file fo                 : text open write_mode is outfile;
    variable lin, lout      : line;
    variable n_op, n_style  : integer;
    variable n_ew, n_fw     : integer;
    variable n_guard, n_den : integer;
    variable n_p1, n_p2     : integer;
    variable rs             : round_type;
  begin
    for i in 1 to skip loop
      readline (fi, lin);
    end loop;
    while not endfile (fi) loop
      readline (fi, lin);
      read (lin, n_op);
      read (lin, n_style);
      read (lin, n_ew);
      read (lin, n_fw);
      read (lin, n_guard);
      read (lin, n_den);
      read (lin, n_p1);
      read (lin, n_p2);
      case n_style is
        when 0      => rs := round_nearest;
        when 1      => rs := round_zero;
        when 2      => rs := round_neginf;
        when others => rs := round_inf;
      end case;
      case n_op is
        when 0 to 6 | 13 | 14 => arith (n_op, n_ew, n_fw, n_guard, n_p1, rs, n_den = 1, lin, lout);
        when 7                => narrow (n_ew, n_fw, n_p1, n_p2, rs, n_den = 1, lin, lout);
        when 8 | 12           => from_int (n_op, n_ew, n_fw, n_p1, rs, lin, lout);
        when others           => to_int (n_op, n_ew, n_fw, n_p1, rs, lin, lout);
      end case;
      writeline (fo, lout);
    end loop;
    wait;
  end process;
end;
