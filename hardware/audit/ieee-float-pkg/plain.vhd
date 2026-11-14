-- Plain calls of ieee.float_pkg with the package's own settings: 3 guard bits, denormal numbers on, and
-- round_nearest unless the call names another style. Each line prints the call, what the package returns and
-- the exactly rounded result, in hex. The last call stops the simulator inside the package as shipped.
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.fixed_float_types.all;
use ieee.float_pkg.all;
library std;
use std.textio.all;

entity plain is
end;

architecture sim of plain is
  subtype v32 is std_ulogic_vector (31 downto 0);
  subtype v64 is std_ulogic_vector (63 downto 0);

  function f32 (bits : v32) return float32 is
  begin
    return to_float (bits, 8, 23);
  end;

  function f64 (bits : v64) return float64 is
  begin
    return to_float (bits, 11, 52);
  end;

  procedure show (what : string; got, exact : std_ulogic_vector) is
    variable lo   : line;
    variable text : string (1 to 44) := (others => ' ');
  begin
    text (1 to what'length) := what;
    write (lo, text);
    hwrite (lo, got);
    write (lo, string'("   exact "));
    hwrite (lo, exact);
    if got /= exact then
      write (lo, string'("   WRONG"));
    end if;
    writeline (output, lo);
  end;

  constant one     : float32 := f32 (x"3F800000");
  constant two     : float32 := f32 (x"40000000");
  constant three   : float32 := f32 (x"40400000");
  constant six     : float32 := f32 (x"40C00000");
  constant largest : float32 := f32 (x"7F7FFFFF");
  constant tiny    : float32 := f32 (x"00000001");      -- the smallest float32, 2.0**-149
begin
  process
  begin
    show ("sqrt (2.0) in float64", to_sulv (sqrt (f64 (x"4000000000000000"))), v64'(x"3FF6A09E667F3BCD"));
    show ("sqrt (14.0)", to_sulv (sqrt (f32 (x"41600000"))), v32'(x"406F7751"));
    show ("sqrt (2.0**-149)", to_sulv (sqrt (tiny)), v32'(x"1A3504F3"));
    show ("mac (-6.0, -1.0, -5.0)", to_sulv (mac (-six, -one, f32 (x"C0A00000"))), v32'(x"3F800000"));
    show ("mac (-5.0, 1.0, 4.0)", to_sulv (mac (f32 (x"C0A00000"), one, f32 (x"40800000"))), v32'(x"BF800000"));
    show ("mac (1.0, 1.0, -infinity)", to_sulv (mac (one, one, f32 (x"FF800000"))), v32'(x"FF800000"));
    show ("mac (1 + 2.0**-23, 1 - 2.0**-23, -1.0)",
          to_sulv (mac (f32 (x"3F800001"), f32 (x"3F7FFFFE"), -one)), v32'(x"A8800000"));
    show ("resize (2.0**-512 in float64, 8, 23)", to_sulv (resize (f64 (x"1FF0000000000000"), 8, 23)), v32'(x"00000000"));
    show ("resize (2.0**600 in float64, 8, 23)", to_sulv (resize (f64 (x"6570000000000000"), 8, 23)), v32'(x"7F800000"));
    show ("resize (2.0**-1074 in float64, 8, 23)", to_sulv (resize (f64 (x"0000000000000001"), 8, 23)), v32'(x"00000000"));
    show ("reciprocal (2.0**127)", to_sulv (reciprocal (f32 (x"7F000000"))), v32'(x"00400000"));
    show ("divide (2.0**-149, 2.0)", to_sulv (divide (tiny, two)), v32'(x"00000000"));
    show ("to_signed (0.50000006, 32)", std_ulogic_vector (to_signed (f32 (x"3F000001"), 32)), v32'(x"00000001"));
    show ("to_unsigned (199.78125, 8)", std_ulogic_vector (to_unsigned (f32 (x"4347C800"), 8)),
          std_ulogic_vector'(x"C8"));
    show ("divide (6.0, 3.0, round_inf)", to_sulv (divide (six, three, round_inf)), v32'(x"40000000"));
    show ("reciprocal (2.0, round_inf)", to_sulv (reciprocal (two, round_inf)), v32'(x"3F000000"));
    show ("add (largest, largest, round_zero)", to_sulv (add (largest, largest, round_zero)), v32'(x"7F7FFFFF"));
    show ("multiply (2.0**-100, 2.0**-100, round_inf)",
          to_sulv (multiply (f32 (x"0D800000"), f32 (x"0D800000"), round_inf)), v32'(x"00000001"));
    show ("add (1.0, -1.0, round_neginf)", to_sulv (add (one, -one, round_neginf)), v32'(x"80000000"));
    show ("to_signed (2.25, 8, round_inf)", std_ulogic_vector (to_signed (f32 (x"40100000"), 8, round_inf)),
          std_ulogic_vector'(x"03"));
    show ("to_float (100000, 5, 10, round_zero)", to_sulv (to_float (100000, 5, 10, round_zero)),
          std_ulogic_vector'(x"7BFF"));
    show ("dividebyp2 (3 * 2.0**-149, 2.0)", to_sulv (dividebyp2 (f32 (x"00000003"), two)), v32'(x"00000002"));
    show ("scalb (1.0, 300)", to_sulv (scalb (one, 300)), v32'(x"7F800000"));
    show ("scalb (+infinity, -10)", to_sulv (scalb (f32 (x"7F800000"), -10)), v32'(x"7F800000"));
    show ("resize (2.0**-650 in float64, 8, 23)", to_sulv (resize (f64 (x"1750000000000000"), 8, 23)), v32'(x"00000000"));
    wait;
  end process;
end;
