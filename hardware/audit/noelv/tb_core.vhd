-- The NOEL-V processor core (GRLIB, lib/gaisler/noelv/core/cpucorenv.vhd) with its caches, bus interface and
-- nanoFPU, running a program from a 64 KiB memory on its AHB master port. Generics as in the reference design
-- designs/noelv-generic, except that every area is cacheable and narrow (32-bit transfers only), which keeps
-- the memory model to one word per transfer.
--   progfile  : one 32-bit word per line, hex, loaded from address 0xC0000000 (the reset vector)
--   cfg       : NOEL-V configuration (1 = GP dual issue, 2 = GP single issue, 0 = HP, 3 = MIN)
--   waits     : wait states the memory inserts in every transfer
-- Every write the program makes is printed as "W address data size cycle"; a write to an address whose
-- bits 15..12 are all ones ends the run.
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_textio.all;
library std;
use std.textio.all;
library grlib;
use grlib.amba.all;
use grlib.stdlib.all;
library gaisler;
use gaisler.noelv.all;
use gaisler.l5nv_shared.all;

entity tb_core is
  generic (
    progfile  : string  := "prog.hex";
    cfg       : integer := 1;
    waits     : integer := 0;
    maxcycles : integer := 20000;
    disas     : integer := 0);
end;

architecture sim of tb_core is
  subtype word32 is std_logic_vector(31 downto 0);
  type mem_t is array (0 to 16383) of word32;

  signal clk    : std_ulogic := '0';
  signal rstn   : std_ulogic := '0';
  signal ahbi   : ahb_mst_in_type;
  signal ahbo   : ahb_mst_out_type;
  signal ahbsi  : ahb_slv_in_type;
  signal ahbso  : ahb_slv_out_vector;
  signal irqo   : nv_irq_out_type;
  signal dbgo   : nv_debug_out_type;
  signal tpo    : nv_full_trace_type;
  signal cnt    : nv_counter_out_type;
  signal pwrd   : std_ulogic;
  signal stop   : boolean := false;

  signal d_act   : std_ulogic := '0';
  signal d_write : std_ulogic := '0';
  signal d_addr  : word32 := (others => '0');
  signal d_size  : std_logic_vector(2 downto 0) := "000";
  signal rdata   : word32 := (others => '0');
  signal wcnt    : integer := 0;
  signal hready  : std_ulogic;
  signal cycle   : integer := 0;
begin
  clk <= not clk after 5 ns when not stop else '0';
  rstn <= '0', '1' after 103 ns;

  u0 : entity gaisler.cpucorenv
    generic map (
      hindex => 0, fabtech => 0, memtech => 0, cached => 16#FFFF#, wbmask => 0, busw => AHBDW, physaddr => 32,
      cmemconf => 2, rfconf => 0, fpuconf => 0, tcmconf => 0, mulconf => 0, intcconf => 0, cfg => cfg,
      disas => disas, scantest => 0, cgen => 0, asyncif => 0)
    port map (
      clk => clk, gclk => clk, rstn => rstn, tsc => l5_tsc_async_none, ahbi => ahbi, ahbo => ahbo,
      ahbsi => ahbsi, ahbso => ahbso, irqi => nv_irq_in_none, irqo => irqo, dbgi => nv_debug_in_none,
      dbgo => dbgo, tpo => tpo, cnt => cnt, pwrd => pwrd);

  ahbso <= (others => ahbs_none);

  bus_p : process (hready, rdata)
    variable m : ahb_mst_in_type;
    variable s : ahb_slv_in_type;
  begin
    m := ahbm_in_none;
    m.hgrant := (others => '1');
    m.hready := hready;
    m.hresp  := "00";
    for i in 0 to AHBDW / 32 - 1 loop
      m.hrdata(32 * i + 31 downto 32 * i) := rdata;
    end loop;
    m.endian := '1';
    ahbi <= m;
    s := ahbs_in_none;
    s.endian := '1';
    ahbsi <= s;
  end process;

  hready <= '1' when wcnt = 0 else '0';

  mem_p : process (clk)
    variable mem    : mem_t := (others => x"00000013");
    variable loaded : boolean := false;
    file f          : text;
    variable l, lo  : line;
    variable w, wd  : word32;
    variable i, idx : integer;
  begin
    if not loaded then
      file_open(f, progfile, read_mode);
      i := 0;
      while not endfile(f) loop
        readline(f, l);
        hread(l, w);
        mem(i) := w;
        i := i + 1;
      end loop;
      file_close(f);
      loaded := true;
    end if;
    if rising_edge(clk) then
      cycle <= cycle + 1;
      if cycle = maxcycles then
        write(lo, string'("T no stop after "));
        write(lo, cycle);
        write(lo, string'(" cycles"));
        writeline(output, lo);
        stop <= true;
      end if;
      -- end of a data phase
      if d_act = '1' and hready = '1' and d_write = '1' then
        idx := to_integer(unsigned(d_addr(15 downto 2)));
        wd  := ahbo.hwdata(31 downto 0);
        case d_size is
          when "000" =>
            i := to_integer(unsigned(d_addr(1 downto 0)));
            mem(idx)(8 * i + 7 downto 8 * i) := wd(8 * i + 7 downto 8 * i);
          when "001" =>
            if d_addr(1) = '0' then
              mem(idx)(15 downto 0) := wd(15 downto 0);
            else
              mem(idx)(31 downto 16) := wd(31 downto 16);
            end if;
          when others =>
            mem(idx) := wd;
        end case;
        write(lo, string'("W "));
        hwrite(lo, d_addr);
        write(lo, string'(" "));
        hwrite(lo, wd);
        write(lo, string'(" "));
        write(lo, to_integer(unsigned(d_size)));
        write(lo, string'(" "));
        write(lo, cycle);
        writeline(output, lo);
        if d_addr(15 downto 12) = "1111" then
          stop <= true;
        end if;
      end if;
      -- address phase
      if hready = '1' then
        if ahbo.htrans(1) = '1' then
          d_act   <= '1';
          d_addr  <= ahbo.haddr;
          d_write <= ahbo.hwrite;
          d_size  <= ahbo.hsize;
          rdata   <= mem(to_integer(unsigned(ahbo.haddr(15 downto 2))));
          wcnt    <= waits;
        else
          d_act   <= '0';
        end if;
      else
        wcnt <= wcnt - 1;
      end if;
    end if;
  end process;
end;
