set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def lut (t i : Nat) : Bool := t.testBit i
def popcount (x : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => popcount x n + (x n).toNat
theorem popcount_le (x : Nat → Bool) : ∀ n, popcount x n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
      have h := popcount_le x n
      have b : (x n).toNat ≤ 1 := Bool.toNat_le _
      show popcount x n + (x n).toNat ≤ n + 1
      omega
def pc (x : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pc x a n + (x (a + n)).toNat
theorem pc_add (x : Nat → Bool) (a m : Nat) : ∀ n, pc x a (m + n) = pc x a m + pc x (a + m) n
  | 0 => rfl
  | n + 1 => by
      have ih := pc_add x a m n
      show pc x a (m + n) + (x (a + (m + n))).toNat = pc x a m + (pc x (a + m) n + (x (a + m + n)).toNat)
      rw [ih, Nat.add_assoc, Nat.add_assoc]
theorem popcount_eq_pc (x : Nat → Bool) : ∀ n, popcount x n = pc x 0 n
  | 0 => rfl
  | n + 1 => by
      have ih := popcount_eq_pc x n
      show popcount x n + (x n).toNat = pc x 0 n + (x (0 + n)).toNat
      rw [ih, Nat.zero_add]
theorem add_eq {a b c d : Nat} (h1 : a = b) (h2 : c = d) : a + c = b + d := by subst h1; subst h2; rfl
theorem of_iff (o : Bool) (p : Prop) [Decidable p] (h : o.toNat = 1 ↔ p) : o = decide p := by
  cases o <;> simp_all
theorem to_iff (o : Bool) (p : Prop) [Decidable p] (h : o = decide p) : o.toNat = 1 ↔ p := by
  subst h; by_cases hp : p <;> simp [hp]

theorem g0 (a b c d e f : Bool) : a.toNat + b.toNat + c.toNat + d.toNat + e.toNat + f.toNat = (lut 7608434000728254870 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat + 32 * f.toNat)).toNat + 2 * (lut 9301929385684532968 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat + 32 * f.toNat)).toNat + 4 * (lut 18368186720584761344 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat + 32 * f.toNat)).toNat := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
def w_n1 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 487).toNat + 2 * (x 488).toNat + 4 * (x 489).toNat + 8 * (x 490).toNat + 16 * (x 491).toNat + 32 * (x 492).toNat)
def w_n2 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 487).toNat + 2 * (x 488).toNat + 4 * (x 489).toNat + 8 * (x 490).toNat + 16 * (x 491).toNat + 32 * (x 492).toNat)
def w_n3 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 487).toNat + 2 * (x 488).toNat + 4 * (x 489).toNat + 8 * (x 490).toNat + 16 * (x 491).toNat + 32 * (x 492).toNat)
theorem u0 (x : Nat → Bool) : (x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat = (w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat := g0 _ _ _ _ _ _ 
theorem e0 (x : Nat → Bool) : (x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat = (w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat := by
  have h := u0 x
  omega
def w_n4 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 493).toNat + 2 * (x 494).toNat + 4 * (x 495).toNat + 8 * (x 496).toNat + 16 * (x 497).toNat + 32 * (x 498).toNat)
def w_n5 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 493).toNat + 2 * (x 494).toNat + 4 * (x 495).toNat + 8 * (x 496).toNat + 16 * (x 497).toNat + 32 * (x 498).toNat)
def w_n6 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 493).toNat + 2 * (x 494).toNat + 4 * (x 495).toNat + 8 * (x 496).toNat + 16 * (x 497).toNat + 32 * (x 498).toNat)
theorem u1 (x : Nat → Bool) : (x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat = (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat := g0 _ _ _ _ _ _ 
theorem e1 (x : Nat → Bool) : (x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat = (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat := by
  have h := u1 x
  omega
def w_n7 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 499).toNat + 2 * (x 500).toNat + 4 * (x 501).toNat + 8 * (x 502).toNat + 16 * (x 503).toNat + 32 * (x 504).toNat)
def w_n8 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 499).toNat + 2 * (x 500).toNat + 4 * (x 501).toNat + 8 * (x 502).toNat + 16 * (x 503).toNat + 32 * (x 504).toNat)
def w_n9 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 499).toNat + 2 * (x 500).toNat + 4 * (x 501).toNat + 8 * (x 502).toNat + 16 * (x 503).toNat + 32 * (x 504).toNat)
theorem u2 (x : Nat → Bool) : (x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat = (w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat := g0 _ _ _ _ _ _ 
theorem e2 (x : Nat → Bool) : (x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat = (w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat := by
  have h := u2 x
  omega
def w_n10 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 505).toNat + 2 * (x 506).toNat + 4 * (x 507).toNat + 8 * (x 508).toNat + 16 * (x 509).toNat + 32 * (x 510).toNat)
def w_n11 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 505).toNat + 2 * (x 506).toNat + 4 * (x 507).toNat + 8 * (x 508).toNat + 16 * (x 509).toNat + 32 * (x 510).toNat)
def w_n12 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 505).toNat + 2 * (x 506).toNat + 4 * (x 507).toNat + 8 * (x 508).toNat + 16 * (x 509).toNat + 32 * (x 510).toNat)
theorem u3 (x : Nat → Bool) : (x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat = (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat := g0 _ _ _ _ _ _ 
theorem e3 (x : Nat → Bool) : (x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat = (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat := by
  have h := u3 x
  omega
def w_n13 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 469).toNat + 2 * (x 470).toNat + 4 * (x 471).toNat + 8 * (x 472).toNat + 16 * (x 473).toNat + 32 * (x 474).toNat)
def w_n14 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 469).toNat + 2 * (x 470).toNat + 4 * (x 471).toNat + 8 * (x 472).toNat + 16 * (x 473).toNat + 32 * (x 474).toNat)
def w_n15 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 469).toNat + 2 * (x 470).toNat + 4 * (x 471).toNat + 8 * (x 472).toNat + 16 * (x 473).toNat + 32 * (x 474).toNat)
theorem u4 (x : Nat → Bool) : (x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat = (w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat := g0 _ _ _ _ _ _ 
theorem e4 (x : Nat → Bool) : (x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat = (w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat := by
  have h := u4 x
  omega
def w_n16 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 463).toNat + 2 * (x 464).toNat + 4 * (x 465).toNat + 8 * (x 466).toNat + 16 * (x 467).toNat + 32 * (x 468).toNat)
def w_n17 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 463).toNat + 2 * (x 464).toNat + 4 * (x 465).toNat + 8 * (x 466).toNat + 16 * (x 467).toNat + 32 * (x 468).toNat)
def w_n18 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 463).toNat + 2 * (x 464).toNat + 4 * (x 465).toNat + 8 * (x 466).toNat + 16 * (x 467).toNat + 32 * (x 468).toNat)
theorem u5 (x : Nat → Bool) : (x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat = (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat := g0 _ _ _ _ _ _ 
theorem e5 (x : Nat → Bool) : (x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat = (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat := by
  have h := u5 x
  omega
def w_n19 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 481).toNat + 2 * (x 482).toNat + 4 * (x 483).toNat + 8 * (x 484).toNat + 16 * (x 485).toNat + 32 * (x 486).toNat)
def w_n20 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 481).toNat + 2 * (x 482).toNat + 4 * (x 483).toNat + 8 * (x 484).toNat + 16 * (x 485).toNat + 32 * (x 486).toNat)
def w_n21 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 481).toNat + 2 * (x 482).toNat + 4 * (x 483).toNat + 8 * (x 484).toNat + 16 * (x 485).toNat + 32 * (x 486).toNat)
theorem u6 (x : Nat → Bool) : (x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat = (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat := g0 _ _ _ _ _ _ 
theorem e6 (x : Nat → Bool) : (x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat = (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat := by
  have h := u6 x
  omega
def w_n22 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 475).toNat + 2 * (x 476).toNat + 4 * (x 477).toNat + 8 * (x 478).toNat + 16 * (x 479).toNat + 32 * (x 480).toNat)
def w_n23 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 475).toNat + 2 * (x 476).toNat + 4 * (x 477).toNat + 8 * (x 478).toNat + 16 * (x 479).toNat + 32 * (x 480).toNat)
def w_n24 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 475).toNat + 2 * (x 476).toNat + 4 * (x 477).toNat + 8 * (x 478).toNat + 16 * (x 479).toNat + 32 * (x 480).toNat)
theorem u7 (x : Nat → Bool) : (x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat = (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat := g0 _ _ _ _ _ _ 
theorem e7 (x : Nat → Bool) : (x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat = (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat := by
  have h := u7 x
  omega
def w_n25 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n1 x).toNat + 2 * (w_n4 x).toNat + 4 * (w_n7 x).toNat + 8 * (w_n10 x).toNat + 16 * (w_n13 x).toNat + 32 * (w_n16 x).toNat)
def w_n26 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n1 x).toNat + 2 * (w_n4 x).toNat + 4 * (w_n7 x).toNat + 8 * (w_n10 x).toNat + 16 * (w_n13 x).toNat + 32 * (w_n16 x).toNat)
def w_n27 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n1 x).toNat + 2 * (w_n4 x).toNat + 4 * (w_n7 x).toNat + 8 * (w_n10 x).toNat + 16 * (w_n13 x).toNat + 32 * (w_n16 x).toNat)
theorem u8 (x : Nat → Bool) : (w_n1 x).toNat + (w_n4 x).toNat + (w_n7 x).toNat + (w_n10 x).toNat + (w_n13 x).toNat + (w_n16 x).toNat = (w_n25 x).toNat + 2 * (w_n26 x).toNat + 4 * (w_n27 x).toNat := g0 _ _ _ _ _ _ 
theorem e8 (x : Nat → Bool) : (w_n1 x).toNat + (w_n4 x).toNat + (w_n7 x).toNat + (w_n10 x).toNat + (w_n13 x).toNat + (w_n16 x).toNat = (w_n25 x).toNat + 2 * (w_n26 x).toNat + 4 * (w_n27 x).toNat := by
  have h := u8 x
  omega
def w_n28 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n2 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n8 x).toNat + 8 * (w_n11 x).toNat + 16 * (w_n14 x).toNat + 32 * (w_n17 x).toNat)
def w_n29 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n2 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n8 x).toNat + 8 * (w_n11 x).toNat + 16 * (w_n14 x).toNat + 32 * (w_n17 x).toNat)
def w_n30 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n2 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n8 x).toNat + 8 * (w_n11 x).toNat + 16 * (w_n14 x).toNat + 32 * (w_n17 x).toNat)
theorem u9 (x : Nat → Bool) : (w_n2 x).toNat + (w_n5 x).toNat + (w_n8 x).toNat + (w_n11 x).toNat + (w_n14 x).toNat + (w_n17 x).toNat = (w_n28 x).toNat + 2 * (w_n29 x).toNat + 4 * (w_n30 x).toNat := g0 _ _ _ _ _ _ 
theorem e9 (x : Nat → Bool) : 2 * (w_n2 x).toNat + 2 * (w_n5 x).toNat + 2 * (w_n8 x).toNat + 2 * (w_n11 x).toNat + 2 * (w_n14 x).toNat + 2 * (w_n17 x).toNat = 2 * (w_n28 x).toNat + 4 * (w_n29 x).toNat + 8 * (w_n30 x).toNat := by
  have h := u9 x
  omega
def w_n31 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n3 x).toNat + 2 * (w_n6 x).toNat + 4 * (w_n9 x).toNat + 8 * (w_n12 x).toNat + 16 * (w_n15 x).toNat + 32 * (w_n18 x).toNat)
def w_n32 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n3 x).toNat + 2 * (w_n6 x).toNat + 4 * (w_n9 x).toNat + 8 * (w_n12 x).toNat + 16 * (w_n15 x).toNat + 32 * (w_n18 x).toNat)
def w_n33 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n3 x).toNat + 2 * (w_n6 x).toNat + 4 * (w_n9 x).toNat + 8 * (w_n12 x).toNat + 16 * (w_n15 x).toNat + 32 * (w_n18 x).toNat)
theorem u10 (x : Nat → Bool) : (w_n3 x).toNat + (w_n6 x).toNat + (w_n9 x).toNat + (w_n12 x).toNat + (w_n15 x).toNat + (w_n18 x).toNat = (w_n31 x).toNat + 2 * (w_n32 x).toNat + 4 * (w_n33 x).toNat := g0 _ _ _ _ _ _ 
theorem e10 (x : Nat → Bool) : 4 * (w_n3 x).toNat + 4 * (w_n6 x).toNat + 4 * (w_n9 x).toNat + 4 * (w_n12 x).toNat + 4 * (w_n15 x).toNat + 4 * (w_n18 x).toNat = 4 * (w_n31 x).toNat + 8 * (w_n32 x).toNat + 16 * (w_n33 x).toNat := by
  have h := u10 x
  omega
def w_n34 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 547).toNat + 2 * (x 548).toNat + 4 * (x 549).toNat + 8 * (x 550).toNat + 16 * (x 551).toNat + 32 * (x 552).toNat)
def w_n35 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 547).toNat + 2 * (x 548).toNat + 4 * (x 549).toNat + 8 * (x 550).toNat + 16 * (x 551).toNat + 32 * (x 552).toNat)
def w_n36 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 547).toNat + 2 * (x 548).toNat + 4 * (x 549).toNat + 8 * (x 550).toNat + 16 * (x 551).toNat + 32 * (x 552).toNat)
theorem u11 (x : Nat → Bool) : (x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat = (w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat := g0 _ _ _ _ _ _ 
theorem e11 (x : Nat → Bool) : (x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat = (w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat := by
  have h := u11 x
  omega
def w_n37 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 553).toNat + 2 * (x 554).toNat + 4 * (x 555).toNat + 8 * (x 556).toNat + 16 * (x 557).toNat + 32 * (x 558).toNat)
def w_n38 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 553).toNat + 2 * (x 554).toNat + 4 * (x 555).toNat + 8 * (x 556).toNat + 16 * (x 557).toNat + 32 * (x 558).toNat)
def w_n39 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 553).toNat + 2 * (x 554).toNat + 4 * (x 555).toNat + 8 * (x 556).toNat + 16 * (x 557).toNat + 32 * (x 558).toNat)
theorem u12 (x : Nat → Bool) : (x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat = (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat := g0 _ _ _ _ _ _ 
theorem e12 (x : Nat → Bool) : (x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat = (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat := by
  have h := u12 x
  omega
def w_n40 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 535).toNat + 2 * (x 536).toNat + 4 * (x 537).toNat + 8 * (x 538).toNat + 16 * (x 539).toNat + 32 * (x 540).toNat)
def w_n41 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 535).toNat + 2 * (x 536).toNat + 4 * (x 537).toNat + 8 * (x 538).toNat + 16 * (x 539).toNat + 32 * (x 540).toNat)
def w_n42 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 535).toNat + 2 * (x 536).toNat + 4 * (x 537).toNat + 8 * (x 538).toNat + 16 * (x 539).toNat + 32 * (x 540).toNat)
theorem u13 (x : Nat → Bool) : (x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat = (w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat := g0 _ _ _ _ _ _ 
theorem e13 (x : Nat → Bool) : (x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat = (w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat := by
  have h := u13 x
  omega
def w_n43 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 541).toNat + 2 * (x 542).toNat + 4 * (x 543).toNat + 8 * (x 544).toNat + 16 * (x 545).toNat + 32 * (x 546).toNat)
def w_n44 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 541).toNat + 2 * (x 542).toNat + 4 * (x 543).toNat + 8 * (x 544).toNat + 16 * (x 545).toNat + 32 * (x 546).toNat)
def w_n45 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 541).toNat + 2 * (x 542).toNat + 4 * (x 543).toNat + 8 * (x 544).toNat + 16 * (x 545).toNat + 32 * (x 546).toNat)
theorem u14 (x : Nat → Bool) : (x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat = (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat := g0 _ _ _ _ _ _ 
theorem e14 (x : Nat → Bool) : (x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat = (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat := by
  have h := u14 x
  omega
def w_n46 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 517).toNat + 2 * (x 518).toNat + 4 * (x 519).toNat + 8 * (x 520).toNat + 16 * (x 521).toNat + 32 * (x 522).toNat)
def w_n47 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 517).toNat + 2 * (x 518).toNat + 4 * (x 519).toNat + 8 * (x 520).toNat + 16 * (x 521).toNat + 32 * (x 522).toNat)
def w_n48 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 517).toNat + 2 * (x 518).toNat + 4 * (x 519).toNat + 8 * (x 520).toNat + 16 * (x 521).toNat + 32 * (x 522).toNat)
theorem u15 (x : Nat → Bool) : (x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat = (w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat := g0 _ _ _ _ _ _ 
theorem e15 (x : Nat → Bool) : (x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat = (w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat := by
  have h := u15 x
  omega
def w_n49 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 511).toNat + 2 * (x 512).toNat + 4 * (x 513).toNat + 8 * (x 514).toNat + 16 * (x 515).toNat + 32 * (x 516).toNat)
def w_n50 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 511).toNat + 2 * (x 512).toNat + 4 * (x 513).toNat + 8 * (x 514).toNat + 16 * (x 515).toNat + 32 * (x 516).toNat)
def w_n51 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 511).toNat + 2 * (x 512).toNat + 4 * (x 513).toNat + 8 * (x 514).toNat + 16 * (x 515).toNat + 32 * (x 516).toNat)
theorem u16 (x : Nat → Bool) : (x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat = (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat := g0 _ _ _ _ _ _ 
theorem e16 (x : Nat → Bool) : (x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat = (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat := by
  have h := u16 x
  omega
def w_n52 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 529).toNat + 2 * (x 530).toNat + 4 * (x 531).toNat + 8 * (x 532).toNat + 16 * (x 533).toNat + 32 * (x 534).toNat)
def w_n53 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 529).toNat + 2 * (x 530).toNat + 4 * (x 531).toNat + 8 * (x 532).toNat + 16 * (x 533).toNat + 32 * (x 534).toNat)
def w_n54 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 529).toNat + 2 * (x 530).toNat + 4 * (x 531).toNat + 8 * (x 532).toNat + 16 * (x 533).toNat + 32 * (x 534).toNat)
theorem u17 (x : Nat → Bool) : (x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat = (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat := g0 _ _ _ _ _ _ 
theorem e17 (x : Nat → Bool) : (x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat = (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat := by
  have h := u17 x
  omega
def w_n55 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 523).toNat + 2 * (x 524).toNat + 4 * (x 525).toNat + 8 * (x 526).toNat + 16 * (x 527).toNat + 32 * (x 528).toNat)
def w_n56 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 523).toNat + 2 * (x 524).toNat + 4 * (x 525).toNat + 8 * (x 526).toNat + 16 * (x 527).toNat + 32 * (x 528).toNat)
def w_n57 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 523).toNat + 2 * (x 524).toNat + 4 * (x 525).toNat + 8 * (x 526).toNat + 16 * (x 527).toNat + 32 * (x 528).toNat)
theorem u18 (x : Nat → Bool) : (x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat = (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat := g0 _ _ _ _ _ _ 
theorem e18 (x : Nat → Bool) : (x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat = (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat := by
  have h := u18 x
  omega
def w_n58 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n34 x).toNat + 2 * (w_n37 x).toNat + 4 * (w_n40 x).toNat + 8 * (w_n43 x).toNat + 16 * (w_n46 x).toNat + 32 * (w_n49 x).toNat)
def w_n59 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n34 x).toNat + 2 * (w_n37 x).toNat + 4 * (w_n40 x).toNat + 8 * (w_n43 x).toNat + 16 * (w_n46 x).toNat + 32 * (w_n49 x).toNat)
def w_n60 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n34 x).toNat + 2 * (w_n37 x).toNat + 4 * (w_n40 x).toNat + 8 * (w_n43 x).toNat + 16 * (w_n46 x).toNat + 32 * (w_n49 x).toNat)
theorem u19 (x : Nat → Bool) : (w_n34 x).toNat + (w_n37 x).toNat + (w_n40 x).toNat + (w_n43 x).toNat + (w_n46 x).toNat + (w_n49 x).toNat = (w_n58 x).toNat + 2 * (w_n59 x).toNat + 4 * (w_n60 x).toNat := g0 _ _ _ _ _ _ 
theorem e19 (x : Nat → Bool) : (w_n34 x).toNat + (w_n37 x).toNat + (w_n40 x).toNat + (w_n43 x).toNat + (w_n46 x).toNat + (w_n49 x).toNat = (w_n58 x).toNat + 2 * (w_n59 x).toNat + 4 * (w_n60 x).toNat := by
  have h := u19 x
  omega
def w_n61 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n35 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n41 x).toNat + 8 * (w_n44 x).toNat + 16 * (w_n47 x).toNat + 32 * (w_n50 x).toNat)
def w_n62 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n35 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n41 x).toNat + 8 * (w_n44 x).toNat + 16 * (w_n47 x).toNat + 32 * (w_n50 x).toNat)
def w_n63 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n35 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n41 x).toNat + 8 * (w_n44 x).toNat + 16 * (w_n47 x).toNat + 32 * (w_n50 x).toNat)
theorem u20 (x : Nat → Bool) : (w_n35 x).toNat + (w_n38 x).toNat + (w_n41 x).toNat + (w_n44 x).toNat + (w_n47 x).toNat + (w_n50 x).toNat = (w_n61 x).toNat + 2 * (w_n62 x).toNat + 4 * (w_n63 x).toNat := g0 _ _ _ _ _ _ 
theorem e20 (x : Nat → Bool) : 2 * (w_n35 x).toNat + 2 * (w_n38 x).toNat + 2 * (w_n41 x).toNat + 2 * (w_n44 x).toNat + 2 * (w_n47 x).toNat + 2 * (w_n50 x).toNat = 2 * (w_n61 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n63 x).toNat := by
  have h := u20 x
  omega
def w_n64 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n36 x).toNat + 2 * (w_n39 x).toNat + 4 * (w_n42 x).toNat + 8 * (w_n45 x).toNat + 16 * (w_n48 x).toNat + 32 * (w_n51 x).toNat)
def w_n65 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n36 x).toNat + 2 * (w_n39 x).toNat + 4 * (w_n42 x).toNat + 8 * (w_n45 x).toNat + 16 * (w_n48 x).toNat + 32 * (w_n51 x).toNat)
def w_n66 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n36 x).toNat + 2 * (w_n39 x).toNat + 4 * (w_n42 x).toNat + 8 * (w_n45 x).toNat + 16 * (w_n48 x).toNat + 32 * (w_n51 x).toNat)
theorem u21 (x : Nat → Bool) : (w_n36 x).toNat + (w_n39 x).toNat + (w_n42 x).toNat + (w_n45 x).toNat + (w_n48 x).toNat + (w_n51 x).toNat = (w_n64 x).toNat + 2 * (w_n65 x).toNat + 4 * (w_n66 x).toNat := g0 _ _ _ _ _ _ 
theorem e21 (x : Nat → Bool) : 4 * (w_n36 x).toNat + 4 * (w_n39 x).toNat + 4 * (w_n42 x).toNat + 4 * (w_n45 x).toNat + 4 * (w_n48 x).toNat + 4 * (w_n51 x).toNat = 4 * (w_n64 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n66 x).toNat := by
  have h := u21 x
  omega
def w_n67 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n19 x).toNat + 2 * (w_n22 x).toNat + 4 * (w_n25 x).toNat + 8 * (w_n52 x).toNat + 16 * (w_n55 x).toNat + 32 * (w_n58 x).toNat)
def w_n68 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n19 x).toNat + 2 * (w_n22 x).toNat + 4 * (w_n25 x).toNat + 8 * (w_n52 x).toNat + 16 * (w_n55 x).toNat + 32 * (w_n58 x).toNat)
def w_n69 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n19 x).toNat + 2 * (w_n22 x).toNat + 4 * (w_n25 x).toNat + 8 * (w_n52 x).toNat + 16 * (w_n55 x).toNat + 32 * (w_n58 x).toNat)
theorem u22 (x : Nat → Bool) : (w_n19 x).toNat + (w_n22 x).toNat + (w_n25 x).toNat + (w_n52 x).toNat + (w_n55 x).toNat + (w_n58 x).toNat = (w_n67 x).toNat + 2 * (w_n68 x).toNat + 4 * (w_n69 x).toNat := g0 _ _ _ _ _ _ 
theorem e22 (x : Nat → Bool) : (w_n19 x).toNat + (w_n22 x).toNat + (w_n25 x).toNat + (w_n52 x).toNat + (w_n55 x).toNat + (w_n58 x).toNat = (w_n67 x).toNat + 2 * (w_n68 x).toNat + 4 * (w_n69 x).toNat := by
  have h := u22 x
  omega
def w_n70 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n20 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n26 x).toNat + 8 * (w_n28 x).toNat + 16 * (w_n53 x).toNat + 32 * (w_n56 x).toNat)
def w_n71 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n20 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n26 x).toNat + 8 * (w_n28 x).toNat + 16 * (w_n53 x).toNat + 32 * (w_n56 x).toNat)
def w_n72 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n20 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n26 x).toNat + 8 * (w_n28 x).toNat + 16 * (w_n53 x).toNat + 32 * (w_n56 x).toNat)
theorem u23 (x : Nat → Bool) : (w_n20 x).toNat + (w_n23 x).toNat + (w_n26 x).toNat + (w_n28 x).toNat + (w_n53 x).toNat + (w_n56 x).toNat = (w_n70 x).toNat + 2 * (w_n71 x).toNat + 4 * (w_n72 x).toNat := g0 _ _ _ _ _ _ 
theorem e23 (x : Nat → Bool) : 2 * (w_n20 x).toNat + 2 * (w_n23 x).toNat + 2 * (w_n26 x).toNat + 2 * (w_n28 x).toNat + 2 * (w_n53 x).toNat + 2 * (w_n56 x).toNat = 2 * (w_n70 x).toNat + 4 * (w_n71 x).toNat + 8 * (w_n72 x).toNat := by
  have h := u23 x
  omega
def w_n73 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n21 x).toNat + 2 * (w_n24 x).toNat + 4 * (w_n27 x).toNat + 8 * (w_n29 x).toNat + 16 * (w_n31 x).toNat + 32 * (w_n54 x).toNat)
def w_n74 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n21 x).toNat + 2 * (w_n24 x).toNat + 4 * (w_n27 x).toNat + 8 * (w_n29 x).toNat + 16 * (w_n31 x).toNat + 32 * (w_n54 x).toNat)
def w_n75 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n21 x).toNat + 2 * (w_n24 x).toNat + 4 * (w_n27 x).toNat + 8 * (w_n29 x).toNat + 16 * (w_n31 x).toNat + 32 * (w_n54 x).toNat)
theorem u24 (x : Nat → Bool) : (w_n21 x).toNat + (w_n24 x).toNat + (w_n27 x).toNat + (w_n29 x).toNat + (w_n31 x).toNat + (w_n54 x).toNat = (w_n73 x).toNat + 2 * (w_n74 x).toNat + 4 * (w_n75 x).toNat := g0 _ _ _ _ _ _ 
theorem e24 (x : Nat → Bool) : 4 * (w_n21 x).toNat + 4 * (w_n24 x).toNat + 4 * (w_n27 x).toNat + 4 * (w_n29 x).toNat + 4 * (w_n31 x).toNat + 4 * (w_n54 x).toNat = 4 * (w_n73 x).toNat + 8 * (w_n74 x).toNat + 16 * (w_n75 x).toNat := by
  have h := u24 x
  omega
def w_n76 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n57 x).toNat + 2 * (w_n60 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n64 x).toNat + 16 * (w_n69 x).toNat + 32 * (w_n71 x).toNat)
def w_n77 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n57 x).toNat + 2 * (w_n60 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n64 x).toNat + 16 * (w_n69 x).toNat + 32 * (w_n71 x).toNat)
def w_n78 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n57 x).toNat + 2 * (w_n60 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n64 x).toNat + 16 * (w_n69 x).toNat + 32 * (w_n71 x).toNat)
theorem u25 (x : Nat → Bool) : (w_n57 x).toNat + (w_n60 x).toNat + (w_n62 x).toNat + (w_n64 x).toNat + (w_n69 x).toNat + (w_n71 x).toNat = (w_n76 x).toNat + 2 * (w_n77 x).toNat + 4 * (w_n78 x).toNat := g0 _ _ _ _ _ _ 
theorem e25 (x : Nat → Bool) : 4 * (w_n57 x).toNat + 4 * (w_n60 x).toNat + 4 * (w_n62 x).toNat + 4 * (w_n64 x).toNat + 4 * (w_n69 x).toNat + 4 * (w_n71 x).toNat = 4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 16 * (w_n78 x).toNat := by
  have h := u25 x
  omega
def w_n79 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n30 x).toNat + 2 * (w_n32 x).toNat + 4 * (w_n63 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n72 x).toNat + 32 * (w_n74 x).toNat)
def w_n80 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n30 x).toNat + 2 * (w_n32 x).toNat + 4 * (w_n63 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n72 x).toNat + 32 * (w_n74 x).toNat)
def w_n81 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n30 x).toNat + 2 * (w_n32 x).toNat + 4 * (w_n63 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n72 x).toNat + 32 * (w_n74 x).toNat)
theorem u26 (x : Nat → Bool) : (w_n30 x).toNat + (w_n32 x).toNat + (w_n63 x).toNat + (w_n65 x).toNat + (w_n72 x).toNat + (w_n74 x).toNat = (w_n79 x).toNat + 2 * (w_n80 x).toNat + 4 * (w_n81 x).toNat := g0 _ _ _ _ _ _ 
theorem e26 (x : Nat → Bool) : 8 * (w_n30 x).toNat + 8 * (w_n32 x).toNat + 8 * (w_n63 x).toNat + 8 * (w_n65 x).toNat + 8 * (w_n72 x).toNat + 8 * (w_n74 x).toNat = 8 * (w_n79 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n81 x).toNat := by
  have h := u26 x
  omega
def w_n82 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 595).toNat + 2 * (x 596).toNat + 4 * (x 597).toNat + 8 * (x 598).toNat + 16 * (x 599).toNat + 32 * (x 600).toNat)
def w_n83 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 595).toNat + 2 * (x 596).toNat + 4 * (x 597).toNat + 8 * (x 598).toNat + 16 * (x 599).toNat + 32 * (x 600).toNat)
def w_n84 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 595).toNat + 2 * (x 596).toNat + 4 * (x 597).toNat + 8 * (x 598).toNat + 16 * (x 599).toNat + 32 * (x 600).toNat)
theorem u27 (x : Nat → Bool) : (x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat = (w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat := g0 _ _ _ _ _ _ 
theorem e27 (x : Nat → Bool) : (x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat = (w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat := by
  have h := u27 x
  omega
def w_n85 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 601).toNat + 2 * (x 602).toNat + 4 * (x 603).toNat + 8 * (x 604).toNat + 16 * (x 605).toNat + 32 * (x 606).toNat)
def w_n86 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 601).toNat + 2 * (x 602).toNat + 4 * (x 603).toNat + 8 * (x 604).toNat + 16 * (x 605).toNat + 32 * (x 606).toNat)
def w_n87 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 601).toNat + 2 * (x 602).toNat + 4 * (x 603).toNat + 8 * (x 604).toNat + 16 * (x 605).toNat + 32 * (x 606).toNat)
theorem u28 (x : Nat → Bool) : (x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat = (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat := g0 _ _ _ _ _ _ 
theorem e28 (x : Nat → Bool) : (x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat = (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat := by
  have h := u28 x
  omega
def w_n88 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 589).toNat + 2 * (x 590).toNat + 4 * (x 591).toNat + 8 * (x 592).toNat + 16 * (x 593).toNat + 32 * (x 594).toNat)
def w_n89 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 589).toNat + 2 * (x 590).toNat + 4 * (x 591).toNat + 8 * (x 592).toNat + 16 * (x 593).toNat + 32 * (x 594).toNat)
def w_n90 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 589).toNat + 2 * (x 590).toNat + 4 * (x 591).toNat + 8 * (x 592).toNat + 16 * (x 593).toNat + 32 * (x 594).toNat)
theorem u29 (x : Nat → Bool) : (x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat = (w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat := g0 _ _ _ _ _ _ 
theorem e29 (x : Nat → Bool) : (x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat = (w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat := by
  have h := u29 x
  omega
def w_n91 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 583).toNat + 2 * (x 584).toNat + 4 * (x 585).toNat + 8 * (x 586).toNat + 16 * (x 587).toNat + 32 * (x 588).toNat)
def w_n92 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 583).toNat + 2 * (x 584).toNat + 4 * (x 585).toNat + 8 * (x 586).toNat + 16 * (x 587).toNat + 32 * (x 588).toNat)
def w_n93 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 583).toNat + 2 * (x 584).toNat + 4 * (x 585).toNat + 8 * (x 586).toNat + 16 * (x 587).toNat + 32 * (x 588).toNat)
theorem u30 (x : Nat → Bool) : (x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat = (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat := g0 _ _ _ _ _ _ 
theorem e30 (x : Nat → Bool) : (x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat = (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat := by
  have h := u30 x
  omega
def w_n94 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 565).toNat + 2 * (x 566).toNat + 4 * (x 567).toNat + 8 * (x 568).toNat + 16 * (x 569).toNat + 32 * (x 570).toNat)
def w_n95 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 565).toNat + 2 * (x 566).toNat + 4 * (x 567).toNat + 8 * (x 568).toNat + 16 * (x 569).toNat + 32 * (x 570).toNat)
def w_n96 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 565).toNat + 2 * (x 566).toNat + 4 * (x 567).toNat + 8 * (x 568).toNat + 16 * (x 569).toNat + 32 * (x 570).toNat)
theorem u31 (x : Nat → Bool) : (x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat = (w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat := g0 _ _ _ _ _ _ 
theorem e31 (x : Nat → Bool) : (x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat = (w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat := by
  have h := u31 x
  omega
def w_n97 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 559).toNat + 2 * (x 560).toNat + 4 * (x 561).toNat + 8 * (x 562).toNat + 16 * (x 563).toNat + 32 * (x 564).toNat)
def w_n98 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 559).toNat + 2 * (x 560).toNat + 4 * (x 561).toNat + 8 * (x 562).toNat + 16 * (x 563).toNat + 32 * (x 564).toNat)
def w_n99 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 559).toNat + 2 * (x 560).toNat + 4 * (x 561).toNat + 8 * (x 562).toNat + 16 * (x 563).toNat + 32 * (x 564).toNat)
theorem u32 (x : Nat → Bool) : (x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat = (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat := g0 _ _ _ _ _ _ 
theorem e32 (x : Nat → Bool) : (x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat = (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat := by
  have h := u32 x
  omega
def w_n100 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 577).toNat + 2 * (x 578).toNat + 4 * (x 579).toNat + 8 * (x 580).toNat + 16 * (x 581).toNat + 32 * (x 582).toNat)
def w_n101 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 577).toNat + 2 * (x 578).toNat + 4 * (x 579).toNat + 8 * (x 580).toNat + 16 * (x 581).toNat + 32 * (x 582).toNat)
def w_n102 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 577).toNat + 2 * (x 578).toNat + 4 * (x 579).toNat + 8 * (x 580).toNat + 16 * (x 581).toNat + 32 * (x 582).toNat)
theorem u33 (x : Nat → Bool) : (x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat = (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat := g0 _ _ _ _ _ _ 
theorem e33 (x : Nat → Bool) : (x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat = (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat := by
  have h := u33 x
  omega
def w_n103 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 571).toNat + 2 * (x 572).toNat + 4 * (x 573).toNat + 8 * (x 574).toNat + 16 * (x 575).toNat + 32 * (x 576).toNat)
def w_n104 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 571).toNat + 2 * (x 572).toNat + 4 * (x 573).toNat + 8 * (x 574).toNat + 16 * (x 575).toNat + 32 * (x 576).toNat)
def w_n105 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 571).toNat + 2 * (x 572).toNat + 4 * (x 573).toNat + 8 * (x 574).toNat + 16 * (x 575).toNat + 32 * (x 576).toNat)
theorem u34 (x : Nat → Bool) : (x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat = (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat := g0 _ _ _ _ _ _ 
theorem e34 (x : Nat → Bool) : (x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat = (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat := by
  have h := u34 x
  omega
def w_n106 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n82 x).toNat + 2 * (w_n85 x).toNat + 4 * (w_n88 x).toNat + 8 * (w_n91 x).toNat + 16 * (w_n94 x).toNat + 32 * (w_n97 x).toNat)
def w_n107 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n82 x).toNat + 2 * (w_n85 x).toNat + 4 * (w_n88 x).toNat + 8 * (w_n91 x).toNat + 16 * (w_n94 x).toNat + 32 * (w_n97 x).toNat)
def w_n108 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n82 x).toNat + 2 * (w_n85 x).toNat + 4 * (w_n88 x).toNat + 8 * (w_n91 x).toNat + 16 * (w_n94 x).toNat + 32 * (w_n97 x).toNat)
theorem u35 (x : Nat → Bool) : (w_n82 x).toNat + (w_n85 x).toNat + (w_n88 x).toNat + (w_n91 x).toNat + (w_n94 x).toNat + (w_n97 x).toNat = (w_n106 x).toNat + 2 * (w_n107 x).toNat + 4 * (w_n108 x).toNat := g0 _ _ _ _ _ _ 
theorem e35 (x : Nat → Bool) : (w_n82 x).toNat + (w_n85 x).toNat + (w_n88 x).toNat + (w_n91 x).toNat + (w_n94 x).toNat + (w_n97 x).toNat = (w_n106 x).toNat + 2 * (w_n107 x).toNat + 4 * (w_n108 x).toNat := by
  have h := u35 x
  omega
def w_n109 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n83 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n89 x).toNat + 8 * (w_n92 x).toNat + 16 * (w_n95 x).toNat + 32 * (w_n98 x).toNat)
def w_n110 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n83 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n89 x).toNat + 8 * (w_n92 x).toNat + 16 * (w_n95 x).toNat + 32 * (w_n98 x).toNat)
def w_n111 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n83 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n89 x).toNat + 8 * (w_n92 x).toNat + 16 * (w_n95 x).toNat + 32 * (w_n98 x).toNat)
theorem u36 (x : Nat → Bool) : (w_n83 x).toNat + (w_n86 x).toNat + (w_n89 x).toNat + (w_n92 x).toNat + (w_n95 x).toNat + (w_n98 x).toNat = (w_n109 x).toNat + 2 * (w_n110 x).toNat + 4 * (w_n111 x).toNat := g0 _ _ _ _ _ _ 
theorem e36 (x : Nat → Bool) : 2 * (w_n83 x).toNat + 2 * (w_n86 x).toNat + 2 * (w_n89 x).toNat + 2 * (w_n92 x).toNat + 2 * (w_n95 x).toNat + 2 * (w_n98 x).toNat = 2 * (w_n109 x).toNat + 4 * (w_n110 x).toNat + 8 * (w_n111 x).toNat := by
  have h := u36 x
  omega
def w_n112 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n84 x).toNat + 2 * (w_n87 x).toNat + 4 * (w_n90 x).toNat + 8 * (w_n93 x).toNat + 16 * (w_n96 x).toNat + 32 * (w_n99 x).toNat)
def w_n113 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n84 x).toNat + 2 * (w_n87 x).toNat + 4 * (w_n90 x).toNat + 8 * (w_n93 x).toNat + 16 * (w_n96 x).toNat + 32 * (w_n99 x).toNat)
def w_n114 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n84 x).toNat + 2 * (w_n87 x).toNat + 4 * (w_n90 x).toNat + 8 * (w_n93 x).toNat + 16 * (w_n96 x).toNat + 32 * (w_n99 x).toNat)
theorem u37 (x : Nat → Bool) : (w_n84 x).toNat + (w_n87 x).toNat + (w_n90 x).toNat + (w_n93 x).toNat + (w_n96 x).toNat + (w_n99 x).toNat = (w_n112 x).toNat + 2 * (w_n113 x).toNat + 4 * (w_n114 x).toNat := g0 _ _ _ _ _ _ 
theorem e37 (x : Nat → Bool) : 4 * (w_n84 x).toNat + 4 * (w_n87 x).toNat + 4 * (w_n90 x).toNat + 4 * (w_n93 x).toNat + 4 * (w_n96 x).toNat + 4 * (w_n99 x).toNat = 4 * (w_n112 x).toNat + 8 * (w_n113 x).toNat + 16 * (w_n114 x).toNat := by
  have h := u37 x
  omega
def w_n115 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 607).toNat + 2 * (x 608).toNat + 4 * (x 609).toNat + 8 * (x 610).toNat + 16 * (x 611).toNat + 32 * (x 612).toNat)
def w_n116 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 607).toNat + 2 * (x 608).toNat + 4 * (x 609).toNat + 8 * (x 610).toNat + 16 * (x 611).toNat + 32 * (x 612).toNat)
def w_n117 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 607).toNat + 2 * (x 608).toNat + 4 * (x 609).toNat + 8 * (x 610).toNat + 16 * (x 611).toNat + 32 * (x 612).toNat)
theorem u38 (x : Nat → Bool) : (x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat = (w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat := g0 _ _ _ _ _ _ 
theorem e38 (x : Nat → Bool) : (x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat = (w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat := by
  have h := u38 x
  omega
def w_n118 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 613).toNat + 2 * (x 614).toNat + 4 * (x 615).toNat + 8 * (x 616).toNat + 16 * (x 617).toNat + 32 * (x 618).toNat)
def w_n119 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 613).toNat + 2 * (x 614).toNat + 4 * (x 615).toNat + 8 * (x 616).toNat + 16 * (x 617).toNat + 32 * (x 618).toNat)
def w_n120 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 613).toNat + 2 * (x 614).toNat + 4 * (x 615).toNat + 8 * (x 616).toNat + 16 * (x 617).toNat + 32 * (x 618).toNat)
theorem u39 (x : Nat → Bool) : (x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat = (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat := g0 _ _ _ _ _ _ 
theorem e39 (x : Nat → Bool) : (x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat = (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat := by
  have h := u39 x
  omega
def w_n121 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 619).toNat + 2 * (x 620).toNat + 4 * (x 621).toNat + 8 * (x 622).toNat + 16 * (x 623).toNat + 32 * (x 624).toNat)
def w_n122 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 619).toNat + 2 * (x 620).toNat + 4 * (x 621).toNat + 8 * (x 622).toNat + 16 * (x 623).toNat + 32 * (x 624).toNat)
def w_n123 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 619).toNat + 2 * (x 620).toNat + 4 * (x 621).toNat + 8 * (x 622).toNat + 16 * (x 623).toNat + 32 * (x 624).toNat)
theorem u40 (x : Nat → Bool) : (x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat = (w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat := g0 _ _ _ _ _ _ 
theorem e40 (x : Nat → Bool) : (x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat = (w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat := by
  have h := u40 x
  omega
def w_n124 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 625).toNat + 2 * (x 626).toNat + 4 * (x 627).toNat + 8 * (x 628).toNat + 16 * (x 629).toNat + 32 * (x 630).toNat)
def w_n125 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 625).toNat + 2 * (x 626).toNat + 4 * (x 627).toNat + 8 * (x 628).toNat + 16 * (x 629).toNat + 32 * (x 630).toNat)
def w_n126 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 625).toNat + 2 * (x 626).toNat + 4 * (x 627).toNat + 8 * (x 628).toNat + 16 * (x 629).toNat + 32 * (x 630).toNat)
theorem u41 (x : Nat → Bool) : (x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat = (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat := g0 _ _ _ _ _ _ 
theorem e41 (x : Nat → Bool) : (x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat = (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat := by
  have h := u41 x
  omega
def w_n127 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 643).toNat + 2 * (x 644).toNat + 4 * (x 645).toNat + 8 * (x 646).toNat + 16 * (x 647).toNat + 32 * (x 648).toNat)
def w_n128 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 643).toNat + 2 * (x 644).toNat + 4 * (x 645).toNat + 8 * (x 646).toNat + 16 * (x 647).toNat + 32 * (x 648).toNat)
def w_n129 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 643).toNat + 2 * (x 644).toNat + 4 * (x 645).toNat + 8 * (x 646).toNat + 16 * (x 647).toNat + 32 * (x 648).toNat)
theorem u42 (x : Nat → Bool) : (x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat = (w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat := g0 _ _ _ _ _ _ 
theorem e42 (x : Nat → Bool) : (x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat = (w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat := by
  have h := u42 x
  omega
def w_n130 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 649).toNat + 2 * (x 650).toNat + 4 * (x 651).toNat + 8 * (x 652).toNat + 16 * (x 653).toNat + 32 * (x 654).toNat)
def w_n131 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 649).toNat + 2 * (x 650).toNat + 4 * (x 651).toNat + 8 * (x 652).toNat + 16 * (x 653).toNat + 32 * (x 654).toNat)
def w_n132 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 649).toNat + 2 * (x 650).toNat + 4 * (x 651).toNat + 8 * (x 652).toNat + 16 * (x 653).toNat + 32 * (x 654).toNat)
theorem u43 (x : Nat → Bool) : (x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat = (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat := g0 _ _ _ _ _ _ 
theorem e43 (x : Nat → Bool) : (x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat = (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat := by
  have h := u43 x
  omega
def w_n133 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 637).toNat + 2 * (x 638).toNat + 4 * (x 639).toNat + 8 * (x 640).toNat + 16 * (x 641).toNat + 32 * (x 642).toNat)
def w_n134 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 637).toNat + 2 * (x 638).toNat + 4 * (x 639).toNat + 8 * (x 640).toNat + 16 * (x 641).toNat + 32 * (x 642).toNat)
def w_n135 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 637).toNat + 2 * (x 638).toNat + 4 * (x 639).toNat + 8 * (x 640).toNat + 16 * (x 641).toNat + 32 * (x 642).toNat)
theorem u44 (x : Nat → Bool) : (x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat = (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat := g0 _ _ _ _ _ _ 
theorem e44 (x : Nat → Bool) : (x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat = (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat := by
  have h := u44 x
  omega
def w_n136 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 631).toNat + 2 * (x 632).toNat + 4 * (x 633).toNat + 8 * (x 634).toNat + 16 * (x 635).toNat + 32 * (x 636).toNat)
def w_n137 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 631).toNat + 2 * (x 632).toNat + 4 * (x 633).toNat + 8 * (x 634).toNat + 16 * (x 635).toNat + 32 * (x 636).toNat)
def w_n138 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 631).toNat + 2 * (x 632).toNat + 4 * (x 633).toNat + 8 * (x 634).toNat + 16 * (x 635).toNat + 32 * (x 636).toNat)
theorem u45 (x : Nat → Bool) : (x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat = (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat := g0 _ _ _ _ _ _ 
theorem e45 (x : Nat → Bool) : (x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat = (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat := by
  have h := u45 x
  omega
def w_n139 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n115 x).toNat + 2 * (w_n118 x).toNat + 4 * (w_n121 x).toNat + 8 * (w_n124 x).toNat + 16 * (w_n127 x).toNat + 32 * (w_n130 x).toNat)
def w_n140 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n115 x).toNat + 2 * (w_n118 x).toNat + 4 * (w_n121 x).toNat + 8 * (w_n124 x).toNat + 16 * (w_n127 x).toNat + 32 * (w_n130 x).toNat)
def w_n141 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n115 x).toNat + 2 * (w_n118 x).toNat + 4 * (w_n121 x).toNat + 8 * (w_n124 x).toNat + 16 * (w_n127 x).toNat + 32 * (w_n130 x).toNat)
theorem u46 (x : Nat → Bool) : (w_n115 x).toNat + (w_n118 x).toNat + (w_n121 x).toNat + (w_n124 x).toNat + (w_n127 x).toNat + (w_n130 x).toNat = (w_n139 x).toNat + 2 * (w_n140 x).toNat + 4 * (w_n141 x).toNat := g0 _ _ _ _ _ _ 
theorem e46 (x : Nat → Bool) : (w_n115 x).toNat + (w_n118 x).toNat + (w_n121 x).toNat + (w_n124 x).toNat + (w_n127 x).toNat + (w_n130 x).toNat = (w_n139 x).toNat + 2 * (w_n140 x).toNat + 4 * (w_n141 x).toNat := by
  have h := u46 x
  omega
def w_n142 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n116 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n122 x).toNat + 8 * (w_n125 x).toNat + 16 * (w_n128 x).toNat + 32 * (w_n131 x).toNat)
def w_n143 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n116 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n122 x).toNat + 8 * (w_n125 x).toNat + 16 * (w_n128 x).toNat + 32 * (w_n131 x).toNat)
def w_n144 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n116 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n122 x).toNat + 8 * (w_n125 x).toNat + 16 * (w_n128 x).toNat + 32 * (w_n131 x).toNat)
theorem u47 (x : Nat → Bool) : (w_n116 x).toNat + (w_n119 x).toNat + (w_n122 x).toNat + (w_n125 x).toNat + (w_n128 x).toNat + (w_n131 x).toNat = (w_n142 x).toNat + 2 * (w_n143 x).toNat + 4 * (w_n144 x).toNat := g0 _ _ _ _ _ _ 
theorem e47 (x : Nat → Bool) : 2 * (w_n116 x).toNat + 2 * (w_n119 x).toNat + 2 * (w_n122 x).toNat + 2 * (w_n125 x).toNat + 2 * (w_n128 x).toNat + 2 * (w_n131 x).toNat = 2 * (w_n142 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n144 x).toNat := by
  have h := u47 x
  omega
def w_n145 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n117 x).toNat + 2 * (w_n120 x).toNat + 4 * (w_n123 x).toNat + 8 * (w_n126 x).toNat + 16 * (w_n129 x).toNat + 32 * (w_n132 x).toNat)
def w_n146 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n117 x).toNat + 2 * (w_n120 x).toNat + 4 * (w_n123 x).toNat + 8 * (w_n126 x).toNat + 16 * (w_n129 x).toNat + 32 * (w_n132 x).toNat)
def w_n147 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n117 x).toNat + 2 * (w_n120 x).toNat + 4 * (w_n123 x).toNat + 8 * (w_n126 x).toNat + 16 * (w_n129 x).toNat + 32 * (w_n132 x).toNat)
theorem u48 (x : Nat → Bool) : (w_n117 x).toNat + (w_n120 x).toNat + (w_n123 x).toNat + (w_n126 x).toNat + (w_n129 x).toNat + (w_n132 x).toNat = (w_n145 x).toNat + 2 * (w_n146 x).toNat + 4 * (w_n147 x).toNat := g0 _ _ _ _ _ _ 
theorem e48 (x : Nat → Bool) : 4 * (w_n117 x).toNat + 4 * (w_n120 x).toNat + 4 * (w_n123 x).toNat + 4 * (w_n126 x).toNat + 4 * (w_n129 x).toNat + 4 * (w_n132 x).toNat = 4 * (w_n145 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n147 x).toNat := by
  have h := u48 x
  omega
def w_n148 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n100 x).toNat + 2 * (w_n103 x).toNat + 4 * (w_n106 x).toNat + 8 * (w_n133 x).toNat + 16 * (w_n136 x).toNat + 32 * (w_n139 x).toNat)
def w_n149 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n100 x).toNat + 2 * (w_n103 x).toNat + 4 * (w_n106 x).toNat + 8 * (w_n133 x).toNat + 16 * (w_n136 x).toNat + 32 * (w_n139 x).toNat)
def w_n150 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n100 x).toNat + 2 * (w_n103 x).toNat + 4 * (w_n106 x).toNat + 8 * (w_n133 x).toNat + 16 * (w_n136 x).toNat + 32 * (w_n139 x).toNat)
theorem u49 (x : Nat → Bool) : (w_n100 x).toNat + (w_n103 x).toNat + (w_n106 x).toNat + (w_n133 x).toNat + (w_n136 x).toNat + (w_n139 x).toNat = (w_n148 x).toNat + 2 * (w_n149 x).toNat + 4 * (w_n150 x).toNat := g0 _ _ _ _ _ _ 
theorem e49 (x : Nat → Bool) : (w_n100 x).toNat + (w_n103 x).toNat + (w_n106 x).toNat + (w_n133 x).toNat + (w_n136 x).toNat + (w_n139 x).toNat = (w_n148 x).toNat + 2 * (w_n149 x).toNat + 4 * (w_n150 x).toNat := by
  have h := u49 x
  omega
def w_n151 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n101 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n107 x).toNat + 8 * (w_n109 x).toNat + 16 * (w_n134 x).toNat + 32 * (w_n137 x).toNat)
def w_n152 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n101 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n107 x).toNat + 8 * (w_n109 x).toNat + 16 * (w_n134 x).toNat + 32 * (w_n137 x).toNat)
def w_n153 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n101 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n107 x).toNat + 8 * (w_n109 x).toNat + 16 * (w_n134 x).toNat + 32 * (w_n137 x).toNat)
theorem u50 (x : Nat → Bool) : (w_n101 x).toNat + (w_n104 x).toNat + (w_n107 x).toNat + (w_n109 x).toNat + (w_n134 x).toNat + (w_n137 x).toNat = (w_n151 x).toNat + 2 * (w_n152 x).toNat + 4 * (w_n153 x).toNat := g0 _ _ _ _ _ _ 
theorem e50 (x : Nat → Bool) : 2 * (w_n101 x).toNat + 2 * (w_n104 x).toNat + 2 * (w_n107 x).toNat + 2 * (w_n109 x).toNat + 2 * (w_n134 x).toNat + 2 * (w_n137 x).toNat = 2 * (w_n151 x).toNat + 4 * (w_n152 x).toNat + 8 * (w_n153 x).toNat := by
  have h := u50 x
  omega
def w_n154 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n102 x).toNat + 2 * (w_n105 x).toNat + 4 * (w_n108 x).toNat + 8 * (w_n110 x).toNat + 16 * (w_n112 x).toNat + 32 * (w_n135 x).toNat)
def w_n155 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n102 x).toNat + 2 * (w_n105 x).toNat + 4 * (w_n108 x).toNat + 8 * (w_n110 x).toNat + 16 * (w_n112 x).toNat + 32 * (w_n135 x).toNat)
def w_n156 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n102 x).toNat + 2 * (w_n105 x).toNat + 4 * (w_n108 x).toNat + 8 * (w_n110 x).toNat + 16 * (w_n112 x).toNat + 32 * (w_n135 x).toNat)
theorem u51 (x : Nat → Bool) : (w_n102 x).toNat + (w_n105 x).toNat + (w_n108 x).toNat + (w_n110 x).toNat + (w_n112 x).toNat + (w_n135 x).toNat = (w_n154 x).toNat + 2 * (w_n155 x).toNat + 4 * (w_n156 x).toNat := g0 _ _ _ _ _ _ 
theorem e51 (x : Nat → Bool) : 4 * (w_n102 x).toNat + 4 * (w_n105 x).toNat + 4 * (w_n108 x).toNat + 4 * (w_n110 x).toNat + 4 * (w_n112 x).toNat + 4 * (w_n135 x).toNat = 4 * (w_n154 x).toNat + 8 * (w_n155 x).toNat + 16 * (w_n156 x).toNat := by
  have h := u51 x
  omega
def w_n157 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n138 x).toNat + 2 * (w_n141 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n145 x).toNat + 16 * (w_n150 x).toNat + 32 * (w_n152 x).toNat)
def w_n158 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n138 x).toNat + 2 * (w_n141 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n145 x).toNat + 16 * (w_n150 x).toNat + 32 * (w_n152 x).toNat)
def w_n159 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n138 x).toNat + 2 * (w_n141 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n145 x).toNat + 16 * (w_n150 x).toNat + 32 * (w_n152 x).toNat)
theorem u52 (x : Nat → Bool) : (w_n138 x).toNat + (w_n141 x).toNat + (w_n143 x).toNat + (w_n145 x).toNat + (w_n150 x).toNat + (w_n152 x).toNat = (w_n157 x).toNat + 2 * (w_n158 x).toNat + 4 * (w_n159 x).toNat := g0 _ _ _ _ _ _ 
theorem e52 (x : Nat → Bool) : 4 * (w_n138 x).toNat + 4 * (w_n141 x).toNat + 4 * (w_n143 x).toNat + 4 * (w_n145 x).toNat + 4 * (w_n150 x).toNat + 4 * (w_n152 x).toNat = 4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat := by
  have h := u52 x
  omega
def w_n160 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n111 x).toNat + 2 * (w_n113 x).toNat + 4 * (w_n144 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n153 x).toNat + 32 * (w_n155 x).toNat)
def w_n161 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n111 x).toNat + 2 * (w_n113 x).toNat + 4 * (w_n144 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n153 x).toNat + 32 * (w_n155 x).toNat)
def w_n162 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n111 x).toNat + 2 * (w_n113 x).toNat + 4 * (w_n144 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n153 x).toNat + 32 * (w_n155 x).toNat)
theorem u53 (x : Nat → Bool) : (w_n111 x).toNat + (w_n113 x).toNat + (w_n144 x).toNat + (w_n146 x).toNat + (w_n153 x).toNat + (w_n155 x).toNat = (w_n160 x).toNat + 2 * (w_n161 x).toNat + 4 * (w_n162 x).toNat := g0 _ _ _ _ _ _ 
theorem e53 (x : Nat → Bool) : 8 * (w_n111 x).toNat + 8 * (w_n113 x).toNat + 8 * (w_n144 x).toNat + 8 * (w_n146 x).toNat + 8 * (w_n153 x).toNat + 8 * (w_n155 x).toNat = 8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat := by
  have h := u53 x
  omega
def w_n163 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n59 x).toNat + 2 * (w_n61 x).toNat + 4 * (w_n68 x).toNat + 8 * (w_n70 x).toNat + 16 * (w_n140 x).toNat + 32 * (w_n142 x).toNat)
def w_n164 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n59 x).toNat + 2 * (w_n61 x).toNat + 4 * (w_n68 x).toNat + 8 * (w_n70 x).toNat + 16 * (w_n140 x).toNat + 32 * (w_n142 x).toNat)
def w_n165 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n59 x).toNat + 2 * (w_n61 x).toNat + 4 * (w_n68 x).toNat + 8 * (w_n70 x).toNat + 16 * (w_n140 x).toNat + 32 * (w_n142 x).toNat)
theorem u54 (x : Nat → Bool) : (w_n59 x).toNat + (w_n61 x).toNat + (w_n68 x).toNat + (w_n70 x).toNat + (w_n140 x).toNat + (w_n142 x).toNat = (w_n163 x).toNat + 2 * (w_n164 x).toNat + 4 * (w_n165 x).toNat := g0 _ _ _ _ _ _ 
theorem e54 (x : Nat → Bool) : 2 * (w_n59 x).toNat + 2 * (w_n61 x).toNat + 2 * (w_n68 x).toNat + 2 * (w_n70 x).toNat + 2 * (w_n140 x).toNat + 2 * (w_n142 x).toNat = 2 * (w_n163 x).toNat + 4 * (w_n164 x).toNat + 8 * (w_n165 x).toNat := by
  have h := u54 x
  omega
def w_n166 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n33 x).toNat + 2 * (w_n66 x).toNat + 4 * (w_n75 x).toNat + 8 * (w_n78 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n114 x).toNat)
def w_n167 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n33 x).toNat + 2 * (w_n66 x).toNat + 4 * (w_n75 x).toNat + 8 * (w_n78 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n114 x).toNat)
def w_n168 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n33 x).toNat + 2 * (w_n66 x).toNat + 4 * (w_n75 x).toNat + 8 * (w_n78 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n114 x).toNat)
theorem u55 (x : Nat → Bool) : (w_n33 x).toNat + (w_n66 x).toNat + (w_n75 x).toNat + (w_n78 x).toNat + (w_n80 x).toNat + (w_n114 x).toNat = (w_n166 x).toNat + 2 * (w_n167 x).toNat + 4 * (w_n168 x).toNat := g0 _ _ _ _ _ _ 
theorem e55 (x : Nat → Bool) : 16 * (w_n33 x).toNat + 16 * (w_n66 x).toNat + 16 * (w_n75 x).toNat + 16 * (w_n78 x).toNat + 16 * (w_n80 x).toNat + 16 * (w_n114 x).toNat = 16 * (w_n166 x).toNat + 32 * (w_n167 x).toNat + 64 * (w_n168 x).toNat := by
  have h := u55 x
  omega
def w_n169 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 739).toNat + 2 * (x 740).toNat + 4 * (x 741).toNat + 8 * (x 742).toNat + 16 * (x 743).toNat + 32 * (x 744).toNat)
def w_n170 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 739).toNat + 2 * (x 740).toNat + 4 * (x 741).toNat + 8 * (x 742).toNat + 16 * (x 743).toNat + 32 * (x 744).toNat)
def w_n171 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 739).toNat + 2 * (x 740).toNat + 4 * (x 741).toNat + 8 * (x 742).toNat + 16 * (x 743).toNat + 32 * (x 744).toNat)
theorem u56 (x : Nat → Bool) : (x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat = (w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat := g0 _ _ _ _ _ _ 
theorem e56 (x : Nat → Bool) : (x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat = (w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat := by
  have h := u56 x
  omega
def w_n172 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 745).toNat + 2 * (x 746).toNat + 4 * (x 747).toNat + 8 * (x 748).toNat + 16 * (x 749).toNat + 32 * (x 750).toNat)
def w_n173 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 745).toNat + 2 * (x 746).toNat + 4 * (x 747).toNat + 8 * (x 748).toNat + 16 * (x 749).toNat + 32 * (x 750).toNat)
def w_n174 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 745).toNat + 2 * (x 746).toNat + 4 * (x 747).toNat + 8 * (x 748).toNat + 16 * (x 749).toNat + 32 * (x 750).toNat)
theorem u57 (x : Nat → Bool) : (x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat = (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat := g0 _ _ _ _ _ _ 
theorem e57 (x : Nat → Bool) : (x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat = (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat := by
  have h := u57 x
  omega
def w_n175 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 733).toNat + 2 * (x 734).toNat + 4 * (x 735).toNat + 8 * (x 736).toNat + 16 * (x 737).toNat + 32 * (x 738).toNat)
def w_n176 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 733).toNat + 2 * (x 734).toNat + 4 * (x 735).toNat + 8 * (x 736).toNat + 16 * (x 737).toNat + 32 * (x 738).toNat)
def w_n177 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 733).toNat + 2 * (x 734).toNat + 4 * (x 735).toNat + 8 * (x 736).toNat + 16 * (x 737).toNat + 32 * (x 738).toNat)
theorem u58 (x : Nat → Bool) : (x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat = (w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat := g0 _ _ _ _ _ _ 
theorem e58 (x : Nat → Bool) : (x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat = (w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat := by
  have h := u58 x
  omega
def w_n178 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 727).toNat + 2 * (x 728).toNat + 4 * (x 729).toNat + 8 * (x 730).toNat + 16 * (x 731).toNat + 32 * (x 732).toNat)
def w_n179 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 727).toNat + 2 * (x 728).toNat + 4 * (x 729).toNat + 8 * (x 730).toNat + 16 * (x 731).toNat + 32 * (x 732).toNat)
def w_n180 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 727).toNat + 2 * (x 728).toNat + 4 * (x 729).toNat + 8 * (x 730).toNat + 16 * (x 731).toNat + 32 * (x 732).toNat)
theorem u59 (x : Nat → Bool) : (x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat = (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat := g0 _ _ _ _ _ _ 
theorem e59 (x : Nat → Bool) : (x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat = (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat := by
  have h := u59 x
  omega
def w_n181 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 709).toNat + 2 * (x 710).toNat + 4 * (x 711).toNat + 8 * (x 712).toNat + 16 * (x 713).toNat + 32 * (x 714).toNat)
def w_n182 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 709).toNat + 2 * (x 710).toNat + 4 * (x 711).toNat + 8 * (x 712).toNat + 16 * (x 713).toNat + 32 * (x 714).toNat)
def w_n183 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 709).toNat + 2 * (x 710).toNat + 4 * (x 711).toNat + 8 * (x 712).toNat + 16 * (x 713).toNat + 32 * (x 714).toNat)
theorem u60 (x : Nat → Bool) : (x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat = (w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat := g0 _ _ _ _ _ _ 
theorem e60 (x : Nat → Bool) : (x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat = (w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat := by
  have h := u60 x
  omega
def w_n184 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 703).toNat + 2 * (x 704).toNat + 4 * (x 705).toNat + 8 * (x 706).toNat + 16 * (x 707).toNat + 32 * (x 708).toNat)
def w_n185 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 703).toNat + 2 * (x 704).toNat + 4 * (x 705).toNat + 8 * (x 706).toNat + 16 * (x 707).toNat + 32 * (x 708).toNat)
def w_n186 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 703).toNat + 2 * (x 704).toNat + 4 * (x 705).toNat + 8 * (x 706).toNat + 16 * (x 707).toNat + 32 * (x 708).toNat)
theorem u61 (x : Nat → Bool) : (x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat = (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat := g0 _ _ _ _ _ _ 
theorem e61 (x : Nat → Bool) : (x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat = (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat := by
  have h := u61 x
  omega
def w_n187 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 721).toNat + 2 * (x 722).toNat + 4 * (x 723).toNat + 8 * (x 724).toNat + 16 * (x 725).toNat + 32 * (x 726).toNat)
def w_n188 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 721).toNat + 2 * (x 722).toNat + 4 * (x 723).toNat + 8 * (x 724).toNat + 16 * (x 725).toNat + 32 * (x 726).toNat)
def w_n189 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 721).toNat + 2 * (x 722).toNat + 4 * (x 723).toNat + 8 * (x 724).toNat + 16 * (x 725).toNat + 32 * (x 726).toNat)
theorem u62 (x : Nat → Bool) : (x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat = (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat := g0 _ _ _ _ _ _ 
theorem e62 (x : Nat → Bool) : (x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat = (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat := by
  have h := u62 x
  omega
def w_n190 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 715).toNat + 2 * (x 716).toNat + 4 * (x 717).toNat + 8 * (x 718).toNat + 16 * (x 719).toNat + 32 * (x 720).toNat)
def w_n191 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 715).toNat + 2 * (x 716).toNat + 4 * (x 717).toNat + 8 * (x 718).toNat + 16 * (x 719).toNat + 32 * (x 720).toNat)
def w_n192 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 715).toNat + 2 * (x 716).toNat + 4 * (x 717).toNat + 8 * (x 718).toNat + 16 * (x 719).toNat + 32 * (x 720).toNat)
theorem u63 (x : Nat → Bool) : (x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat = (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat := g0 _ _ _ _ _ _ 
theorem e63 (x : Nat → Bool) : (x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat = (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat := by
  have h := u63 x
  omega
def w_n193 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n169 x).toNat + 2 * (w_n172 x).toNat + 4 * (w_n175 x).toNat + 8 * (w_n178 x).toNat + 16 * (w_n181 x).toNat + 32 * (w_n184 x).toNat)
def w_n194 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n169 x).toNat + 2 * (w_n172 x).toNat + 4 * (w_n175 x).toNat + 8 * (w_n178 x).toNat + 16 * (w_n181 x).toNat + 32 * (w_n184 x).toNat)
def w_n195 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n169 x).toNat + 2 * (w_n172 x).toNat + 4 * (w_n175 x).toNat + 8 * (w_n178 x).toNat + 16 * (w_n181 x).toNat + 32 * (w_n184 x).toNat)
theorem u64 (x : Nat → Bool) : (w_n169 x).toNat + (w_n172 x).toNat + (w_n175 x).toNat + (w_n178 x).toNat + (w_n181 x).toNat + (w_n184 x).toNat = (w_n193 x).toNat + 2 * (w_n194 x).toNat + 4 * (w_n195 x).toNat := g0 _ _ _ _ _ _ 
theorem e64 (x : Nat → Bool) : (w_n169 x).toNat + (w_n172 x).toNat + (w_n175 x).toNat + (w_n178 x).toNat + (w_n181 x).toNat + (w_n184 x).toNat = (w_n193 x).toNat + 2 * (w_n194 x).toNat + 4 * (w_n195 x).toNat := by
  have h := u64 x
  omega
def w_n196 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n170 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n176 x).toNat + 8 * (w_n179 x).toNat + 16 * (w_n182 x).toNat + 32 * (w_n185 x).toNat)
def w_n197 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n170 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n176 x).toNat + 8 * (w_n179 x).toNat + 16 * (w_n182 x).toNat + 32 * (w_n185 x).toNat)
def w_n198 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n170 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n176 x).toNat + 8 * (w_n179 x).toNat + 16 * (w_n182 x).toNat + 32 * (w_n185 x).toNat)
theorem u65 (x : Nat → Bool) : (w_n170 x).toNat + (w_n173 x).toNat + (w_n176 x).toNat + (w_n179 x).toNat + (w_n182 x).toNat + (w_n185 x).toNat = (w_n196 x).toNat + 2 * (w_n197 x).toNat + 4 * (w_n198 x).toNat := g0 _ _ _ _ _ _ 
theorem e65 (x : Nat → Bool) : 2 * (w_n170 x).toNat + 2 * (w_n173 x).toNat + 2 * (w_n176 x).toNat + 2 * (w_n179 x).toNat + 2 * (w_n182 x).toNat + 2 * (w_n185 x).toNat = 2 * (w_n196 x).toNat + 4 * (w_n197 x).toNat + 8 * (w_n198 x).toNat := by
  have h := u65 x
  omega
def w_n199 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n171 x).toNat + 2 * (w_n174 x).toNat + 4 * (w_n177 x).toNat + 8 * (w_n180 x).toNat + 16 * (w_n183 x).toNat + 32 * (w_n186 x).toNat)
def w_n200 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n171 x).toNat + 2 * (w_n174 x).toNat + 4 * (w_n177 x).toNat + 8 * (w_n180 x).toNat + 16 * (w_n183 x).toNat + 32 * (w_n186 x).toNat)
def w_n201 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n171 x).toNat + 2 * (w_n174 x).toNat + 4 * (w_n177 x).toNat + 8 * (w_n180 x).toNat + 16 * (w_n183 x).toNat + 32 * (w_n186 x).toNat)
theorem u66 (x : Nat → Bool) : (w_n171 x).toNat + (w_n174 x).toNat + (w_n177 x).toNat + (w_n180 x).toNat + (w_n183 x).toNat + (w_n186 x).toNat = (w_n199 x).toNat + 2 * (w_n200 x).toNat + 4 * (w_n201 x).toNat := g0 _ _ _ _ _ _ 
theorem e66 (x : Nat → Bool) : 4 * (w_n171 x).toNat + 4 * (w_n174 x).toNat + 4 * (w_n177 x).toNat + 4 * (w_n180 x).toNat + 4 * (w_n183 x).toNat + 4 * (w_n186 x).toNat = 4 * (w_n199 x).toNat + 8 * (w_n200 x).toNat + 16 * (w_n201 x).toNat := by
  have h := u66 x
  omega
def w_n202 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 667).toNat + 2 * (x 668).toNat + 4 * (x 669).toNat + 8 * (x 670).toNat + 16 * (x 671).toNat + 32 * (x 672).toNat)
def w_n203 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 667).toNat + 2 * (x 668).toNat + 4 * (x 669).toNat + 8 * (x 670).toNat + 16 * (x 671).toNat + 32 * (x 672).toNat)
def w_n204 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 667).toNat + 2 * (x 668).toNat + 4 * (x 669).toNat + 8 * (x 670).toNat + 16 * (x 671).toNat + 32 * (x 672).toNat)
theorem u67 (x : Nat → Bool) : (x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat = (w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat := g0 _ _ _ _ _ _ 
theorem e67 (x : Nat → Bool) : (x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat = (w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat := by
  have h := u67 x
  omega
def w_n205 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 673).toNat + 2 * (x 674).toNat + 4 * (x 675).toNat + 8 * (x 676).toNat + 16 * (x 677).toNat + 32 * (x 678).toNat)
def w_n206 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 673).toNat + 2 * (x 674).toNat + 4 * (x 675).toNat + 8 * (x 676).toNat + 16 * (x 677).toNat + 32 * (x 678).toNat)
def w_n207 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 673).toNat + 2 * (x 674).toNat + 4 * (x 675).toNat + 8 * (x 676).toNat + 16 * (x 677).toNat + 32 * (x 678).toNat)
theorem u68 (x : Nat → Bool) : (x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat = (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat := g0 _ _ _ _ _ _ 
theorem e68 (x : Nat → Bool) : (x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat = (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat := by
  have h := u68 x
  omega
def w_n208 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 661).toNat + 2 * (x 662).toNat + 4 * (x 663).toNat + 8 * (x 664).toNat + 16 * (x 665).toNat + 32 * (x 666).toNat)
def w_n209 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 661).toNat + 2 * (x 662).toNat + 4 * (x 663).toNat + 8 * (x 664).toNat + 16 * (x 665).toNat + 32 * (x 666).toNat)
def w_n210 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 661).toNat + 2 * (x 662).toNat + 4 * (x 663).toNat + 8 * (x 664).toNat + 16 * (x 665).toNat + 32 * (x 666).toNat)
theorem u69 (x : Nat → Bool) : (x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat = (w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat := g0 _ _ _ _ _ _ 
theorem e69 (x : Nat → Bool) : (x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat = (w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat := by
  have h := u69 x
  omega
def w_n211 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 655).toNat + 2 * (x 656).toNat + 4 * (x 657).toNat + 8 * (x 658).toNat + 16 * (x 659).toNat + 32 * (x 660).toNat)
def w_n212 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 655).toNat + 2 * (x 656).toNat + 4 * (x 657).toNat + 8 * (x 658).toNat + 16 * (x 659).toNat + 32 * (x 660).toNat)
def w_n213 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 655).toNat + 2 * (x 656).toNat + 4 * (x 657).toNat + 8 * (x 658).toNat + 16 * (x 659).toNat + 32 * (x 660).toNat)
theorem u70 (x : Nat → Bool) : (x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat = (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat := g0 _ _ _ _ _ _ 
theorem e70 (x : Nat → Bool) : (x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat = (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat := by
  have h := u70 x
  omega
def w_n214 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 679).toNat + 2 * (x 680).toNat + 4 * (x 681).toNat + 8 * (x 682).toNat + 16 * (x 683).toNat + 32 * (x 684).toNat)
def w_n215 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 679).toNat + 2 * (x 680).toNat + 4 * (x 681).toNat + 8 * (x 682).toNat + 16 * (x 683).toNat + 32 * (x 684).toNat)
def w_n216 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 679).toNat + 2 * (x 680).toNat + 4 * (x 681).toNat + 8 * (x 682).toNat + 16 * (x 683).toNat + 32 * (x 684).toNat)
theorem u71 (x : Nat → Bool) : (x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat = (w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat := g0 _ _ _ _ _ _ 
theorem e71 (x : Nat → Bool) : (x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat = (w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat := by
  have h := u71 x
  omega
def w_n217 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 685).toNat + 2 * (x 686).toNat + 4 * (x 687).toNat + 8 * (x 688).toNat + 16 * (x 689).toNat + 32 * (x 690).toNat)
def w_n218 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 685).toNat + 2 * (x 686).toNat + 4 * (x 687).toNat + 8 * (x 688).toNat + 16 * (x 689).toNat + 32 * (x 690).toNat)
def w_n219 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 685).toNat + 2 * (x 686).toNat + 4 * (x 687).toNat + 8 * (x 688).toNat + 16 * (x 689).toNat + 32 * (x 690).toNat)
theorem u72 (x : Nat → Bool) : (x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat = (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat := g0 _ _ _ _ _ _ 
theorem e72 (x : Nat → Bool) : (x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat = (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat := by
  have h := u72 x
  omega
def w_n220 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 691).toNat + 2 * (x 692).toNat + 4 * (x 693).toNat + 8 * (x 694).toNat + 16 * (x 695).toNat + 32 * (x 696).toNat)
def w_n221 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 691).toNat + 2 * (x 692).toNat + 4 * (x 693).toNat + 8 * (x 694).toNat + 16 * (x 695).toNat + 32 * (x 696).toNat)
def w_n222 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 691).toNat + 2 * (x 692).toNat + 4 * (x 693).toNat + 8 * (x 694).toNat + 16 * (x 695).toNat + 32 * (x 696).toNat)
theorem u73 (x : Nat → Bool) : (x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat = (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat := g0 _ _ _ _ _ _ 
theorem e73 (x : Nat → Bool) : (x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat = (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat := by
  have h := u73 x
  omega
def w_n223 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 697).toNat + 2 * (x 698).toNat + 4 * (x 699).toNat + 8 * (x 700).toNat + 16 * (x 701).toNat + 32 * (x 702).toNat)
def w_n224 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 697).toNat + 2 * (x 698).toNat + 4 * (x 699).toNat + 8 * (x 700).toNat + 16 * (x 701).toNat + 32 * (x 702).toNat)
def w_n225 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 697).toNat + 2 * (x 698).toNat + 4 * (x 699).toNat + 8 * (x 700).toNat + 16 * (x 701).toNat + 32 * (x 702).toNat)
theorem u74 (x : Nat → Bool) : (x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat = (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat := g0 _ _ _ _ _ _ 
theorem e74 (x : Nat → Bool) : (x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat = (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat := by
  have h := u74 x
  omega
def w_n226 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n202 x).toNat + 2 * (w_n205 x).toNat + 4 * (w_n208 x).toNat + 8 * (w_n211 x).toNat + 16 * (w_n214 x).toNat + 32 * (w_n217 x).toNat)
def w_n227 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n202 x).toNat + 2 * (w_n205 x).toNat + 4 * (w_n208 x).toNat + 8 * (w_n211 x).toNat + 16 * (w_n214 x).toNat + 32 * (w_n217 x).toNat)
def w_n228 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n202 x).toNat + 2 * (w_n205 x).toNat + 4 * (w_n208 x).toNat + 8 * (w_n211 x).toNat + 16 * (w_n214 x).toNat + 32 * (w_n217 x).toNat)
theorem u75 (x : Nat → Bool) : (w_n202 x).toNat + (w_n205 x).toNat + (w_n208 x).toNat + (w_n211 x).toNat + (w_n214 x).toNat + (w_n217 x).toNat = (w_n226 x).toNat + 2 * (w_n227 x).toNat + 4 * (w_n228 x).toNat := g0 _ _ _ _ _ _ 
theorem e75 (x : Nat → Bool) : (w_n202 x).toNat + (w_n205 x).toNat + (w_n208 x).toNat + (w_n211 x).toNat + (w_n214 x).toNat + (w_n217 x).toNat = (w_n226 x).toNat + 2 * (w_n227 x).toNat + 4 * (w_n228 x).toNat := by
  have h := u75 x
  omega
def w_n229 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n203 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n209 x).toNat + 8 * (w_n212 x).toNat + 16 * (w_n215 x).toNat + 32 * (w_n218 x).toNat)
def w_n230 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n203 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n209 x).toNat + 8 * (w_n212 x).toNat + 16 * (w_n215 x).toNat + 32 * (w_n218 x).toNat)
def w_n231 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n203 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n209 x).toNat + 8 * (w_n212 x).toNat + 16 * (w_n215 x).toNat + 32 * (w_n218 x).toNat)
theorem u76 (x : Nat → Bool) : (w_n203 x).toNat + (w_n206 x).toNat + (w_n209 x).toNat + (w_n212 x).toNat + (w_n215 x).toNat + (w_n218 x).toNat = (w_n229 x).toNat + 2 * (w_n230 x).toNat + 4 * (w_n231 x).toNat := g0 _ _ _ _ _ _ 
theorem e76 (x : Nat → Bool) : 2 * (w_n203 x).toNat + 2 * (w_n206 x).toNat + 2 * (w_n209 x).toNat + 2 * (w_n212 x).toNat + 2 * (w_n215 x).toNat + 2 * (w_n218 x).toNat = 2 * (w_n229 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n231 x).toNat := by
  have h := u76 x
  omega
def w_n232 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n204 x).toNat + 2 * (w_n207 x).toNat + 4 * (w_n210 x).toNat + 8 * (w_n213 x).toNat + 16 * (w_n216 x).toNat + 32 * (w_n219 x).toNat)
def w_n233 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n204 x).toNat + 2 * (w_n207 x).toNat + 4 * (w_n210 x).toNat + 8 * (w_n213 x).toNat + 16 * (w_n216 x).toNat + 32 * (w_n219 x).toNat)
def w_n234 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n204 x).toNat + 2 * (w_n207 x).toNat + 4 * (w_n210 x).toNat + 8 * (w_n213 x).toNat + 16 * (w_n216 x).toNat + 32 * (w_n219 x).toNat)
theorem u77 (x : Nat → Bool) : (w_n204 x).toNat + (w_n207 x).toNat + (w_n210 x).toNat + (w_n213 x).toNat + (w_n216 x).toNat + (w_n219 x).toNat = (w_n232 x).toNat + 2 * (w_n233 x).toNat + 4 * (w_n234 x).toNat := g0 _ _ _ _ _ _ 
theorem e77 (x : Nat → Bool) : 4 * (w_n204 x).toNat + 4 * (w_n207 x).toNat + 4 * (w_n210 x).toNat + 4 * (w_n213 x).toNat + 4 * (w_n216 x).toNat + 4 * (w_n219 x).toNat = 4 * (w_n232 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n234 x).toNat := by
  have h := u77 x
  omega
def w_n235 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n187 x).toNat + 2 * (w_n190 x).toNat + 4 * (w_n193 x).toNat + 8 * (w_n220 x).toNat + 16 * (w_n223 x).toNat + 32 * (w_n226 x).toNat)
def w_n236 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n187 x).toNat + 2 * (w_n190 x).toNat + 4 * (w_n193 x).toNat + 8 * (w_n220 x).toNat + 16 * (w_n223 x).toNat + 32 * (w_n226 x).toNat)
def w_n237 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n187 x).toNat + 2 * (w_n190 x).toNat + 4 * (w_n193 x).toNat + 8 * (w_n220 x).toNat + 16 * (w_n223 x).toNat + 32 * (w_n226 x).toNat)
theorem u78 (x : Nat → Bool) : (w_n187 x).toNat + (w_n190 x).toNat + (w_n193 x).toNat + (w_n220 x).toNat + (w_n223 x).toNat + (w_n226 x).toNat = (w_n235 x).toNat + 2 * (w_n236 x).toNat + 4 * (w_n237 x).toNat := g0 _ _ _ _ _ _ 
theorem e78 (x : Nat → Bool) : (w_n187 x).toNat + (w_n190 x).toNat + (w_n193 x).toNat + (w_n220 x).toNat + (w_n223 x).toNat + (w_n226 x).toNat = (w_n235 x).toNat + 2 * (w_n236 x).toNat + 4 * (w_n237 x).toNat := by
  have h := u78 x
  omega
def w_n238 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n188 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n194 x).toNat + 8 * (w_n196 x).toNat + 16 * (w_n221 x).toNat + 32 * (w_n224 x).toNat)
def w_n239 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n188 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n194 x).toNat + 8 * (w_n196 x).toNat + 16 * (w_n221 x).toNat + 32 * (w_n224 x).toNat)
def w_n240 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n188 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n194 x).toNat + 8 * (w_n196 x).toNat + 16 * (w_n221 x).toNat + 32 * (w_n224 x).toNat)
theorem u79 (x : Nat → Bool) : (w_n188 x).toNat + (w_n191 x).toNat + (w_n194 x).toNat + (w_n196 x).toNat + (w_n221 x).toNat + (w_n224 x).toNat = (w_n238 x).toNat + 2 * (w_n239 x).toNat + 4 * (w_n240 x).toNat := g0 _ _ _ _ _ _ 
theorem e79 (x : Nat → Bool) : 2 * (w_n188 x).toNat + 2 * (w_n191 x).toNat + 2 * (w_n194 x).toNat + 2 * (w_n196 x).toNat + 2 * (w_n221 x).toNat + 2 * (w_n224 x).toNat = 2 * (w_n238 x).toNat + 4 * (w_n239 x).toNat + 8 * (w_n240 x).toNat := by
  have h := u79 x
  omega
def w_n241 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n189 x).toNat + 2 * (w_n192 x).toNat + 4 * (w_n195 x).toNat + 8 * (w_n197 x).toNat + 16 * (w_n199 x).toNat + 32 * (w_n222 x).toNat)
def w_n242 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n189 x).toNat + 2 * (w_n192 x).toNat + 4 * (w_n195 x).toNat + 8 * (w_n197 x).toNat + 16 * (w_n199 x).toNat + 32 * (w_n222 x).toNat)
def w_n243 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n189 x).toNat + 2 * (w_n192 x).toNat + 4 * (w_n195 x).toNat + 8 * (w_n197 x).toNat + 16 * (w_n199 x).toNat + 32 * (w_n222 x).toNat)
theorem u80 (x : Nat → Bool) : (w_n189 x).toNat + (w_n192 x).toNat + (w_n195 x).toNat + (w_n197 x).toNat + (w_n199 x).toNat + (w_n222 x).toNat = (w_n241 x).toNat + 2 * (w_n242 x).toNat + 4 * (w_n243 x).toNat := g0 _ _ _ _ _ _ 
theorem e80 (x : Nat → Bool) : 4 * (w_n189 x).toNat + 4 * (w_n192 x).toNat + 4 * (w_n195 x).toNat + 4 * (w_n197 x).toNat + 4 * (w_n199 x).toNat + 4 * (w_n222 x).toNat = 4 * (w_n241 x).toNat + 8 * (w_n242 x).toNat + 16 * (w_n243 x).toNat := by
  have h := u80 x
  omega
def w_n244 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n225 x).toNat + 2 * (w_n228 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n232 x).toNat + 16 * (w_n237 x).toNat + 32 * (w_n239 x).toNat)
def w_n245 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n225 x).toNat + 2 * (w_n228 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n232 x).toNat + 16 * (w_n237 x).toNat + 32 * (w_n239 x).toNat)
def w_n246 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n225 x).toNat + 2 * (w_n228 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n232 x).toNat + 16 * (w_n237 x).toNat + 32 * (w_n239 x).toNat)
theorem u81 (x : Nat → Bool) : (w_n225 x).toNat + (w_n228 x).toNat + (w_n230 x).toNat + (w_n232 x).toNat + (w_n237 x).toNat + (w_n239 x).toNat = (w_n244 x).toNat + 2 * (w_n245 x).toNat + 4 * (w_n246 x).toNat := g0 _ _ _ _ _ _ 
theorem e81 (x : Nat → Bool) : 4 * (w_n225 x).toNat + 4 * (w_n228 x).toNat + 4 * (w_n230 x).toNat + 4 * (w_n232 x).toNat + 4 * (w_n237 x).toNat + 4 * (w_n239 x).toNat = 4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 16 * (w_n246 x).toNat := by
  have h := u81 x
  omega
def w_n247 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n198 x).toNat + 2 * (w_n200 x).toNat + 4 * (w_n231 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n240 x).toNat + 32 * (w_n242 x).toNat)
def w_n248 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n198 x).toNat + 2 * (w_n200 x).toNat + 4 * (w_n231 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n240 x).toNat + 32 * (w_n242 x).toNat)
def w_n249 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n198 x).toNat + 2 * (w_n200 x).toNat + 4 * (w_n231 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n240 x).toNat + 32 * (w_n242 x).toNat)
theorem u82 (x : Nat → Bool) : (w_n198 x).toNat + (w_n200 x).toNat + (w_n231 x).toNat + (w_n233 x).toNat + (w_n240 x).toNat + (w_n242 x).toNat = (w_n247 x).toNat + 2 * (w_n248 x).toNat + 4 * (w_n249 x).toNat := g0 _ _ _ _ _ _ 
theorem e82 (x : Nat → Bool) : 8 * (w_n198 x).toNat + 8 * (w_n200 x).toNat + 8 * (w_n231 x).toNat + 8 * (w_n233 x).toNat + 8 * (w_n240 x).toNat + 8 * (w_n242 x).toNat = 8 * (w_n247 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n249 x).toNat := by
  have h := u82 x
  omega
def w_n250 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 811).toNat + 2 * (x 812).toNat + 4 * (x 813).toNat + 8 * (x 814).toNat + 16 * (x 815).toNat + 32 * (x 816).toNat)
def w_n251 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 811).toNat + 2 * (x 812).toNat + 4 * (x 813).toNat + 8 * (x 814).toNat + 16 * (x 815).toNat + 32 * (x 816).toNat)
def w_n252 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 811).toNat + 2 * (x 812).toNat + 4 * (x 813).toNat + 8 * (x 814).toNat + 16 * (x 815).toNat + 32 * (x 816).toNat)
theorem u83 (x : Nat → Bool) : (x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat = (w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat := g0 _ _ _ _ _ _ 
theorem e83 (x : Nat → Bool) : (x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat = (w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat := by
  have h := u83 x
  omega
def w_n253 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 817).toNat + 2 * (x 818).toNat + 4 * (x 819).toNat + 8 * (x 820).toNat + 16 * (x 821).toNat + 32 * (x 822).toNat)
def w_n254 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 817).toNat + 2 * (x 818).toNat + 4 * (x 819).toNat + 8 * (x 820).toNat + 16 * (x 821).toNat + 32 * (x 822).toNat)
def w_n255 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 817).toNat + 2 * (x 818).toNat + 4 * (x 819).toNat + 8 * (x 820).toNat + 16 * (x 821).toNat + 32 * (x 822).toNat)
theorem u84 (x : Nat → Bool) : (x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat = (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat := g0 _ _ _ _ _ _ 
theorem e84 (x : Nat → Bool) : (x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat = (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat := by
  have h := u84 x
  omega
def w_n256 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 805).toNat + 2 * (x 806).toNat + 4 * (x 807).toNat + 8 * (x 808).toNat + 16 * (x 809).toNat + 32 * (x 810).toNat)
def w_n257 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 805).toNat + 2 * (x 806).toNat + 4 * (x 807).toNat + 8 * (x 808).toNat + 16 * (x 809).toNat + 32 * (x 810).toNat)
def w_n258 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 805).toNat + 2 * (x 806).toNat + 4 * (x 807).toNat + 8 * (x 808).toNat + 16 * (x 809).toNat + 32 * (x 810).toNat)
theorem u85 (x : Nat → Bool) : (x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat = (w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat := g0 _ _ _ _ _ _ 
theorem e85 (x : Nat → Bool) : (x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat = (w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat := by
  have h := u85 x
  omega
def w_n259 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 799).toNat + 2 * (x 800).toNat + 4 * (x 801).toNat + 8 * (x 802).toNat + 16 * (x 803).toNat + 32 * (x 804).toNat)
def w_n260 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 799).toNat + 2 * (x 800).toNat + 4 * (x 801).toNat + 8 * (x 802).toNat + 16 * (x 803).toNat + 32 * (x 804).toNat)
def w_n261 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 799).toNat + 2 * (x 800).toNat + 4 * (x 801).toNat + 8 * (x 802).toNat + 16 * (x 803).toNat + 32 * (x 804).toNat)
theorem u86 (x : Nat → Bool) : (x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat = (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat := g0 _ _ _ _ _ _ 
theorem e86 (x : Nat → Bool) : (x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat = (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat := by
  have h := u86 x
  omega
def w_n262 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 829).toNat + 2 * (x 830).toNat + 4 * (x 831).toNat + 8 * (x 832).toNat + 16 * (x 833).toNat + 32 * (x 834).toNat)
def w_n263 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 829).toNat + 2 * (x 830).toNat + 4 * (x 831).toNat + 8 * (x 832).toNat + 16 * (x 833).toNat + 32 * (x 834).toNat)
def w_n264 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 829).toNat + 2 * (x 830).toNat + 4 * (x 831).toNat + 8 * (x 832).toNat + 16 * (x 833).toNat + 32 * (x 834).toNat)
theorem u87 (x : Nat → Bool) : (x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat = (w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat := g0 _ _ _ _ _ _ 
theorem e87 (x : Nat → Bool) : (x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat = (w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat := by
  have h := u87 x
  omega
def w_n265 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 823).toNat + 2 * (x 824).toNat + 4 * (x 825).toNat + 8 * (x 826).toNat + 16 * (x 827).toNat + 32 * (x 828).toNat)
def w_n266 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 823).toNat + 2 * (x 824).toNat + 4 * (x 825).toNat + 8 * (x 826).toNat + 16 * (x 827).toNat + 32 * (x 828).toNat)
def w_n267 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 823).toNat + 2 * (x 824).toNat + 4 * (x 825).toNat + 8 * (x 826).toNat + 16 * (x 827).toNat + 32 * (x 828).toNat)
theorem u88 (x : Nat → Bool) : (x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat = (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat := g0 _ _ _ _ _ _ 
theorem e88 (x : Nat → Bool) : (x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat = (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat := by
  have h := u88 x
  omega
def w_n268 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 835).toNat + 2 * (x 836).toNat + 4 * (x 837).toNat + 8 * (x 838).toNat + 16 * (x 839).toNat + 32 * (x 840).toNat)
def w_n269 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 835).toNat + 2 * (x 836).toNat + 4 * (x 837).toNat + 8 * (x 838).toNat + 16 * (x 839).toNat + 32 * (x 840).toNat)
def w_n270 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 835).toNat + 2 * (x 836).toNat + 4 * (x 837).toNat + 8 * (x 838).toNat + 16 * (x 839).toNat + 32 * (x 840).toNat)
theorem u89 (x : Nat → Bool) : (x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat = (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat := g0 _ _ _ _ _ _ 
theorem e89 (x : Nat → Bool) : (x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat = (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat := by
  have h := u89 x
  omega
def w_n271 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 841).toNat + 2 * (x 842).toNat + 4 * (x 843).toNat + 8 * (x 844).toNat + 16 * (x 845).toNat + 32 * (x 846).toNat)
def w_n272 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 841).toNat + 2 * (x 842).toNat + 4 * (x 843).toNat + 8 * (x 844).toNat + 16 * (x 845).toNat + 32 * (x 846).toNat)
def w_n273 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 841).toNat + 2 * (x 842).toNat + 4 * (x 843).toNat + 8 * (x 844).toNat + 16 * (x 845).toNat + 32 * (x 846).toNat)
theorem u90 (x : Nat → Bool) : (x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat = (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat := g0 _ _ _ _ _ _ 
theorem e90 (x : Nat → Bool) : (x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat = (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat := by
  have h := u90 x
  omega
def w_n274 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n250 x).toNat + 2 * (w_n253 x).toNat + 4 * (w_n256 x).toNat + 8 * (w_n259 x).toNat + 16 * (w_n262 x).toNat + 32 * (w_n265 x).toNat)
def w_n275 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n250 x).toNat + 2 * (w_n253 x).toNat + 4 * (w_n256 x).toNat + 8 * (w_n259 x).toNat + 16 * (w_n262 x).toNat + 32 * (w_n265 x).toNat)
def w_n276 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n250 x).toNat + 2 * (w_n253 x).toNat + 4 * (w_n256 x).toNat + 8 * (w_n259 x).toNat + 16 * (w_n262 x).toNat + 32 * (w_n265 x).toNat)
theorem u91 (x : Nat → Bool) : (w_n250 x).toNat + (w_n253 x).toNat + (w_n256 x).toNat + (w_n259 x).toNat + (w_n262 x).toNat + (w_n265 x).toNat = (w_n274 x).toNat + 2 * (w_n275 x).toNat + 4 * (w_n276 x).toNat := g0 _ _ _ _ _ _ 
theorem e91 (x : Nat → Bool) : (w_n250 x).toNat + (w_n253 x).toNat + (w_n256 x).toNat + (w_n259 x).toNat + (w_n262 x).toNat + (w_n265 x).toNat = (w_n274 x).toNat + 2 * (w_n275 x).toNat + 4 * (w_n276 x).toNat := by
  have h := u91 x
  omega
def w_n277 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n251 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n257 x).toNat + 8 * (w_n260 x).toNat + 16 * (w_n263 x).toNat + 32 * (w_n266 x).toNat)
def w_n278 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n251 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n257 x).toNat + 8 * (w_n260 x).toNat + 16 * (w_n263 x).toNat + 32 * (w_n266 x).toNat)
def w_n279 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n251 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n257 x).toNat + 8 * (w_n260 x).toNat + 16 * (w_n263 x).toNat + 32 * (w_n266 x).toNat)
theorem u92 (x : Nat → Bool) : (w_n251 x).toNat + (w_n254 x).toNat + (w_n257 x).toNat + (w_n260 x).toNat + (w_n263 x).toNat + (w_n266 x).toNat = (w_n277 x).toNat + 2 * (w_n278 x).toNat + 4 * (w_n279 x).toNat := g0 _ _ _ _ _ _ 
theorem e92 (x : Nat → Bool) : 2 * (w_n251 x).toNat + 2 * (w_n254 x).toNat + 2 * (w_n257 x).toNat + 2 * (w_n260 x).toNat + 2 * (w_n263 x).toNat + 2 * (w_n266 x).toNat = 2 * (w_n277 x).toNat + 4 * (w_n278 x).toNat + 8 * (w_n279 x).toNat := by
  have h := u92 x
  omega
def w_n280 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n252 x).toNat + 2 * (w_n255 x).toNat + 4 * (w_n258 x).toNat + 8 * (w_n261 x).toNat + 16 * (w_n264 x).toNat + 32 * (w_n267 x).toNat)
def w_n281 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n252 x).toNat + 2 * (w_n255 x).toNat + 4 * (w_n258 x).toNat + 8 * (w_n261 x).toNat + 16 * (w_n264 x).toNat + 32 * (w_n267 x).toNat)
def w_n282 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n252 x).toNat + 2 * (w_n255 x).toNat + 4 * (w_n258 x).toNat + 8 * (w_n261 x).toNat + 16 * (w_n264 x).toNat + 32 * (w_n267 x).toNat)
theorem u93 (x : Nat → Bool) : (w_n252 x).toNat + (w_n255 x).toNat + (w_n258 x).toNat + (w_n261 x).toNat + (w_n264 x).toNat + (w_n267 x).toNat = (w_n280 x).toNat + 2 * (w_n281 x).toNat + 4 * (w_n282 x).toNat := g0 _ _ _ _ _ _ 
theorem e93 (x : Nat → Bool) : 4 * (w_n252 x).toNat + 4 * (w_n255 x).toNat + 4 * (w_n258 x).toNat + 4 * (w_n261 x).toNat + 4 * (w_n264 x).toNat + 4 * (w_n267 x).toNat = 4 * (w_n280 x).toNat + 8 * (w_n281 x).toNat + 16 * (w_n282 x).toNat := by
  have h := u93 x
  omega
def w_n283 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 757).toNat + 2 * (x 758).toNat + 4 * (x 759).toNat + 8 * (x 760).toNat + 16 * (x 761).toNat + 32 * (x 762).toNat)
def w_n284 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 757).toNat + 2 * (x 758).toNat + 4 * (x 759).toNat + 8 * (x 760).toNat + 16 * (x 761).toNat + 32 * (x 762).toNat)
def w_n285 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 757).toNat + 2 * (x 758).toNat + 4 * (x 759).toNat + 8 * (x 760).toNat + 16 * (x 761).toNat + 32 * (x 762).toNat)
theorem u94 (x : Nat → Bool) : (x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat = (w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat := g0 _ _ _ _ _ _ 
theorem e94 (x : Nat → Bool) : (x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat = (w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat := by
  have h := u94 x
  omega
def w_n286 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 751).toNat + 2 * (x 752).toNat + 4 * (x 753).toNat + 8 * (x 754).toNat + 16 * (x 755).toNat + 32 * (x 756).toNat)
def w_n287 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 751).toNat + 2 * (x 752).toNat + 4 * (x 753).toNat + 8 * (x 754).toNat + 16 * (x 755).toNat + 32 * (x 756).toNat)
def w_n288 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 751).toNat + 2 * (x 752).toNat + 4 * (x 753).toNat + 8 * (x 754).toNat + 16 * (x 755).toNat + 32 * (x 756).toNat)
theorem u95 (x : Nat → Bool) : (x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat = (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat := g0 _ _ _ _ _ _ 
theorem e95 (x : Nat → Bool) : (x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat = (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat := by
  have h := u95 x
  omega
def w_n289 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 769).toNat + 2 * (x 770).toNat + 4 * (x 771).toNat + 8 * (x 772).toNat + 16 * (x 773).toNat + 32 * (x 774).toNat)
def w_n290 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 769).toNat + 2 * (x 770).toNat + 4 * (x 771).toNat + 8 * (x 772).toNat + 16 * (x 773).toNat + 32 * (x 774).toNat)
def w_n291 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 769).toNat + 2 * (x 770).toNat + 4 * (x 771).toNat + 8 * (x 772).toNat + 16 * (x 773).toNat + 32 * (x 774).toNat)
theorem u96 (x : Nat → Bool) : (x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat = (w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat := g0 _ _ _ _ _ _ 
theorem e96 (x : Nat → Bool) : (x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat = (w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat := by
  have h := u96 x
  omega
def w_n292 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 763).toNat + 2 * (x 764).toNat + 4 * (x 765).toNat + 8 * (x 766).toNat + 16 * (x 767).toNat + 32 * (x 768).toNat)
def w_n293 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 763).toNat + 2 * (x 764).toNat + 4 * (x 765).toNat + 8 * (x 766).toNat + 16 * (x 767).toNat + 32 * (x 768).toNat)
def w_n294 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 763).toNat + 2 * (x 764).toNat + 4 * (x 765).toNat + 8 * (x 766).toNat + 16 * (x 767).toNat + 32 * (x 768).toNat)
theorem u97 (x : Nat → Bool) : (x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat = (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat := g0 _ _ _ _ _ _ 
theorem e97 (x : Nat → Bool) : (x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat = (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat := by
  have h := u97 x
  omega
def w_n295 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 775).toNat + 2 * (x 776).toNat + 4 * (x 777).toNat + 8 * (x 778).toNat + 16 * (x 779).toNat + 32 * (x 780).toNat)
def w_n296 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 775).toNat + 2 * (x 776).toNat + 4 * (x 777).toNat + 8 * (x 778).toNat + 16 * (x 779).toNat + 32 * (x 780).toNat)
def w_n297 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 775).toNat + 2 * (x 776).toNat + 4 * (x 777).toNat + 8 * (x 778).toNat + 16 * (x 779).toNat + 32 * (x 780).toNat)
theorem u98 (x : Nat → Bool) : (x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat = (w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat := g0 _ _ _ _ _ _ 
theorem e98 (x : Nat → Bool) : (x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat = (w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat := by
  have h := u98 x
  omega
def w_n298 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 781).toNat + 2 * (x 782).toNat + 4 * (x 783).toNat + 8 * (x 784).toNat + 16 * (x 785).toNat + 32 * (x 786).toNat)
def w_n299 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 781).toNat + 2 * (x 782).toNat + 4 * (x 783).toNat + 8 * (x 784).toNat + 16 * (x 785).toNat + 32 * (x 786).toNat)
def w_n300 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 781).toNat + 2 * (x 782).toNat + 4 * (x 783).toNat + 8 * (x 784).toNat + 16 * (x 785).toNat + 32 * (x 786).toNat)
theorem u99 (x : Nat → Bool) : (x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat = (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat := g0 _ _ _ _ _ _ 
theorem e99 (x : Nat → Bool) : (x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat = (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat := by
  have h := u99 x
  omega
def w_n301 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 787).toNat + 2 * (x 788).toNat + 4 * (x 789).toNat + 8 * (x 790).toNat + 16 * (x 791).toNat + 32 * (x 792).toNat)
def w_n302 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 787).toNat + 2 * (x 788).toNat + 4 * (x 789).toNat + 8 * (x 790).toNat + 16 * (x 791).toNat + 32 * (x 792).toNat)
def w_n303 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 787).toNat + 2 * (x 788).toNat + 4 * (x 789).toNat + 8 * (x 790).toNat + 16 * (x 791).toNat + 32 * (x 792).toNat)
theorem u100 (x : Nat → Bool) : (x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat = (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat := g0 _ _ _ _ _ _ 
theorem e100 (x : Nat → Bool) : (x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat = (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat := by
  have h := u100 x
  omega
def w_n304 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 793).toNat + 2 * (x 794).toNat + 4 * (x 795).toNat + 8 * (x 796).toNat + 16 * (x 797).toNat + 32 * (x 798).toNat)
def w_n305 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 793).toNat + 2 * (x 794).toNat + 4 * (x 795).toNat + 8 * (x 796).toNat + 16 * (x 797).toNat + 32 * (x 798).toNat)
def w_n306 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 793).toNat + 2 * (x 794).toNat + 4 * (x 795).toNat + 8 * (x 796).toNat + 16 * (x 797).toNat + 32 * (x 798).toNat)
theorem u101 (x : Nat → Bool) : (x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat = (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat := g0 _ _ _ _ _ _ 
theorem e101 (x : Nat → Bool) : (x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat = (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat := by
  have h := u101 x
  omega
def w_n307 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n283 x).toNat + 2 * (w_n286 x).toNat + 4 * (w_n289 x).toNat + 8 * (w_n292 x).toNat + 16 * (w_n295 x).toNat + 32 * (w_n298 x).toNat)
def w_n308 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n283 x).toNat + 2 * (w_n286 x).toNat + 4 * (w_n289 x).toNat + 8 * (w_n292 x).toNat + 16 * (w_n295 x).toNat + 32 * (w_n298 x).toNat)
def w_n309 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n283 x).toNat + 2 * (w_n286 x).toNat + 4 * (w_n289 x).toNat + 8 * (w_n292 x).toNat + 16 * (w_n295 x).toNat + 32 * (w_n298 x).toNat)
theorem u102 (x : Nat → Bool) : (w_n283 x).toNat + (w_n286 x).toNat + (w_n289 x).toNat + (w_n292 x).toNat + (w_n295 x).toNat + (w_n298 x).toNat = (w_n307 x).toNat + 2 * (w_n308 x).toNat + 4 * (w_n309 x).toNat := g0 _ _ _ _ _ _ 
theorem e102 (x : Nat → Bool) : (w_n283 x).toNat + (w_n286 x).toNat + (w_n289 x).toNat + (w_n292 x).toNat + (w_n295 x).toNat + (w_n298 x).toNat = (w_n307 x).toNat + 2 * (w_n308 x).toNat + 4 * (w_n309 x).toNat := by
  have h := u102 x
  omega
def w_n310 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n284 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n290 x).toNat + 8 * (w_n293 x).toNat + 16 * (w_n296 x).toNat + 32 * (w_n299 x).toNat)
def w_n311 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n284 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n290 x).toNat + 8 * (w_n293 x).toNat + 16 * (w_n296 x).toNat + 32 * (w_n299 x).toNat)
def w_n312 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n284 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n290 x).toNat + 8 * (w_n293 x).toNat + 16 * (w_n296 x).toNat + 32 * (w_n299 x).toNat)
theorem u103 (x : Nat → Bool) : (w_n284 x).toNat + (w_n287 x).toNat + (w_n290 x).toNat + (w_n293 x).toNat + (w_n296 x).toNat + (w_n299 x).toNat = (w_n310 x).toNat + 2 * (w_n311 x).toNat + 4 * (w_n312 x).toNat := g0 _ _ _ _ _ _ 
theorem e103 (x : Nat → Bool) : 2 * (w_n284 x).toNat + 2 * (w_n287 x).toNat + 2 * (w_n290 x).toNat + 2 * (w_n293 x).toNat + 2 * (w_n296 x).toNat + 2 * (w_n299 x).toNat = 2 * (w_n310 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n312 x).toNat := by
  have h := u103 x
  omega
def w_n313 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n285 x).toNat + 2 * (w_n288 x).toNat + 4 * (w_n291 x).toNat + 8 * (w_n294 x).toNat + 16 * (w_n297 x).toNat + 32 * (w_n300 x).toNat)
def w_n314 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n285 x).toNat + 2 * (w_n288 x).toNat + 4 * (w_n291 x).toNat + 8 * (w_n294 x).toNat + 16 * (w_n297 x).toNat + 32 * (w_n300 x).toNat)
def w_n315 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n285 x).toNat + 2 * (w_n288 x).toNat + 4 * (w_n291 x).toNat + 8 * (w_n294 x).toNat + 16 * (w_n297 x).toNat + 32 * (w_n300 x).toNat)
theorem u104 (x : Nat → Bool) : (w_n285 x).toNat + (w_n288 x).toNat + (w_n291 x).toNat + (w_n294 x).toNat + (w_n297 x).toNat + (w_n300 x).toNat = (w_n313 x).toNat + 2 * (w_n314 x).toNat + 4 * (w_n315 x).toNat := g0 _ _ _ _ _ _ 
theorem e104 (x : Nat → Bool) : 4 * (w_n285 x).toNat + 4 * (w_n288 x).toNat + 4 * (w_n291 x).toNat + 4 * (w_n294 x).toNat + 4 * (w_n297 x).toNat + 4 * (w_n300 x).toNat = 4 * (w_n313 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n315 x).toNat := by
  have h := u104 x
  omega
def w_n316 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n268 x).toNat + 2 * (w_n271 x).toNat + 4 * (w_n274 x).toNat + 8 * (w_n301 x).toNat + 16 * (w_n304 x).toNat + 32 * (w_n307 x).toNat)
def w_n317 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n268 x).toNat + 2 * (w_n271 x).toNat + 4 * (w_n274 x).toNat + 8 * (w_n301 x).toNat + 16 * (w_n304 x).toNat + 32 * (w_n307 x).toNat)
def w_n318 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n268 x).toNat + 2 * (w_n271 x).toNat + 4 * (w_n274 x).toNat + 8 * (w_n301 x).toNat + 16 * (w_n304 x).toNat + 32 * (w_n307 x).toNat)
theorem u105 (x : Nat → Bool) : (w_n268 x).toNat + (w_n271 x).toNat + (w_n274 x).toNat + (w_n301 x).toNat + (w_n304 x).toNat + (w_n307 x).toNat = (w_n316 x).toNat + 2 * (w_n317 x).toNat + 4 * (w_n318 x).toNat := g0 _ _ _ _ _ _ 
theorem e105 (x : Nat → Bool) : (w_n268 x).toNat + (w_n271 x).toNat + (w_n274 x).toNat + (w_n301 x).toNat + (w_n304 x).toNat + (w_n307 x).toNat = (w_n316 x).toNat + 2 * (w_n317 x).toNat + 4 * (w_n318 x).toNat := by
  have h := u105 x
  omega
def w_n319 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n269 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n275 x).toNat + 8 * (w_n277 x).toNat + 16 * (w_n302 x).toNat + 32 * (w_n305 x).toNat)
def w_n320 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n269 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n275 x).toNat + 8 * (w_n277 x).toNat + 16 * (w_n302 x).toNat + 32 * (w_n305 x).toNat)
def w_n321 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n269 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n275 x).toNat + 8 * (w_n277 x).toNat + 16 * (w_n302 x).toNat + 32 * (w_n305 x).toNat)
theorem u106 (x : Nat → Bool) : (w_n269 x).toNat + (w_n272 x).toNat + (w_n275 x).toNat + (w_n277 x).toNat + (w_n302 x).toNat + (w_n305 x).toNat = (w_n319 x).toNat + 2 * (w_n320 x).toNat + 4 * (w_n321 x).toNat := g0 _ _ _ _ _ _ 
theorem e106 (x : Nat → Bool) : 2 * (w_n269 x).toNat + 2 * (w_n272 x).toNat + 2 * (w_n275 x).toNat + 2 * (w_n277 x).toNat + 2 * (w_n302 x).toNat + 2 * (w_n305 x).toNat = 2 * (w_n319 x).toNat + 4 * (w_n320 x).toNat + 8 * (w_n321 x).toNat := by
  have h := u106 x
  omega
def w_n322 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n270 x).toNat + 2 * (w_n273 x).toNat + 4 * (w_n276 x).toNat + 8 * (w_n278 x).toNat + 16 * (w_n280 x).toNat + 32 * (w_n303 x).toNat)
def w_n323 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n270 x).toNat + 2 * (w_n273 x).toNat + 4 * (w_n276 x).toNat + 8 * (w_n278 x).toNat + 16 * (w_n280 x).toNat + 32 * (w_n303 x).toNat)
def w_n324 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n270 x).toNat + 2 * (w_n273 x).toNat + 4 * (w_n276 x).toNat + 8 * (w_n278 x).toNat + 16 * (w_n280 x).toNat + 32 * (w_n303 x).toNat)
theorem u107 (x : Nat → Bool) : (w_n270 x).toNat + (w_n273 x).toNat + (w_n276 x).toNat + (w_n278 x).toNat + (w_n280 x).toNat + (w_n303 x).toNat = (w_n322 x).toNat + 2 * (w_n323 x).toNat + 4 * (w_n324 x).toNat := g0 _ _ _ _ _ _ 
theorem e107 (x : Nat → Bool) : 4 * (w_n270 x).toNat + 4 * (w_n273 x).toNat + 4 * (w_n276 x).toNat + 4 * (w_n278 x).toNat + 4 * (w_n280 x).toNat + 4 * (w_n303 x).toNat = 4 * (w_n322 x).toNat + 8 * (w_n323 x).toNat + 16 * (w_n324 x).toNat := by
  have h := u107 x
  omega
def w_n325 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n306 x).toNat + 2 * (w_n309 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n313 x).toNat + 16 * (w_n318 x).toNat + 32 * (w_n320 x).toNat)
def w_n326 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n306 x).toNat + 2 * (w_n309 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n313 x).toNat + 16 * (w_n318 x).toNat + 32 * (w_n320 x).toNat)
def w_n327 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n306 x).toNat + 2 * (w_n309 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n313 x).toNat + 16 * (w_n318 x).toNat + 32 * (w_n320 x).toNat)
theorem u108 (x : Nat → Bool) : (w_n306 x).toNat + (w_n309 x).toNat + (w_n311 x).toNat + (w_n313 x).toNat + (w_n318 x).toNat + (w_n320 x).toNat = (w_n325 x).toNat + 2 * (w_n326 x).toNat + 4 * (w_n327 x).toNat := g0 _ _ _ _ _ _ 
theorem e108 (x : Nat → Bool) : 4 * (w_n306 x).toNat + 4 * (w_n309 x).toNat + 4 * (w_n311 x).toNat + 4 * (w_n313 x).toNat + 4 * (w_n318 x).toNat + 4 * (w_n320 x).toNat = 4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat := by
  have h := u108 x
  omega
def w_n328 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n279 x).toNat + 2 * (w_n281 x).toNat + 4 * (w_n312 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n321 x).toNat + 32 * (w_n323 x).toNat)
def w_n329 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n279 x).toNat + 2 * (w_n281 x).toNat + 4 * (w_n312 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n321 x).toNat + 32 * (w_n323 x).toNat)
def w_n330 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n279 x).toNat + 2 * (w_n281 x).toNat + 4 * (w_n312 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n321 x).toNat + 32 * (w_n323 x).toNat)
theorem u109 (x : Nat → Bool) : (w_n279 x).toNat + (w_n281 x).toNat + (w_n312 x).toNat + (w_n314 x).toNat + (w_n321 x).toNat + (w_n323 x).toNat = (w_n328 x).toNat + 2 * (w_n329 x).toNat + 4 * (w_n330 x).toNat := g0 _ _ _ _ _ _ 
theorem e109 (x : Nat → Bool) : 8 * (w_n279 x).toNat + 8 * (w_n281 x).toNat + 8 * (w_n312 x).toNat + 8 * (w_n314 x).toNat + 8 * (w_n321 x).toNat + 8 * (w_n323 x).toNat = 8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat := by
  have h := u109 x
  omega
def w_n331 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n227 x).toNat + 2 * (w_n229 x).toNat + 4 * (w_n236 x).toNat + 8 * (w_n238 x).toNat + 16 * (w_n308 x).toNat + 32 * (w_n310 x).toNat)
def w_n332 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n227 x).toNat + 2 * (w_n229 x).toNat + 4 * (w_n236 x).toNat + 8 * (w_n238 x).toNat + 16 * (w_n308 x).toNat + 32 * (w_n310 x).toNat)
def w_n333 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n227 x).toNat + 2 * (w_n229 x).toNat + 4 * (w_n236 x).toNat + 8 * (w_n238 x).toNat + 16 * (w_n308 x).toNat + 32 * (w_n310 x).toNat)
theorem u110 (x : Nat → Bool) : (w_n227 x).toNat + (w_n229 x).toNat + (w_n236 x).toNat + (w_n238 x).toNat + (w_n308 x).toNat + (w_n310 x).toNat = (w_n331 x).toNat + 2 * (w_n332 x).toNat + 4 * (w_n333 x).toNat := g0 _ _ _ _ _ _ 
theorem e110 (x : Nat → Bool) : 2 * (w_n227 x).toNat + 2 * (w_n229 x).toNat + 2 * (w_n236 x).toNat + 2 * (w_n238 x).toNat + 2 * (w_n308 x).toNat + 2 * (w_n310 x).toNat = 2 * (w_n331 x).toNat + 4 * (w_n332 x).toNat + 8 * (w_n333 x).toNat := by
  have h := u110 x
  omega
def w_n334 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n201 x).toNat + 2 * (w_n234 x).toNat + 4 * (w_n243 x).toNat + 8 * (w_n246 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n282 x).toNat)
def w_n335 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n201 x).toNat + 2 * (w_n234 x).toNat + 4 * (w_n243 x).toNat + 8 * (w_n246 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n282 x).toNat)
def w_n336 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n201 x).toNat + 2 * (w_n234 x).toNat + 4 * (w_n243 x).toNat + 8 * (w_n246 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n282 x).toNat)
theorem u111 (x : Nat → Bool) : (w_n201 x).toNat + (w_n234 x).toNat + (w_n243 x).toNat + (w_n246 x).toNat + (w_n248 x).toNat + (w_n282 x).toNat = (w_n334 x).toNat + 2 * (w_n335 x).toNat + 4 * (w_n336 x).toNat := g0 _ _ _ _ _ _ 
theorem e111 (x : Nat → Bool) : 16 * (w_n201 x).toNat + 16 * (w_n234 x).toNat + 16 * (w_n243 x).toNat + 16 * (w_n246 x).toNat + 16 * (w_n248 x).toNat + 16 * (w_n282 x).toNat = 16 * (w_n334 x).toNat + 32 * (w_n335 x).toNat + 64 * (w_n336 x).toNat := by
  have h := u111 x
  omega
def w_n337 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n163 x).toNat + 8 * (w_n317 x).toNat + 16 * (w_n319 x).toNat + 32 * (w_n331 x).toNat)
def w_n338 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n163 x).toNat + 8 * (w_n317 x).toNat + 16 * (w_n319 x).toNat + 32 * (w_n331 x).toNat)
def w_n339 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n163 x).toNat + 8 * (w_n317 x).toNat + 16 * (w_n319 x).toNat + 32 * (w_n331 x).toNat)
theorem u112 (x : Nat → Bool) : (w_n149 x).toNat + (w_n151 x).toNat + (w_n163 x).toNat + (w_n317 x).toNat + (w_n319 x).toNat + (w_n331 x).toNat = (w_n337 x).toNat + 2 * (w_n338 x).toNat + 4 * (w_n339 x).toNat := g0 _ _ _ _ _ _ 
theorem e112 (x : Nat → Bool) : 2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 2 * (w_n163 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 2 * (w_n331 x).toNat = 2 * (w_n337 x).toNat + 4 * (w_n338 x).toNat + 8 * (w_n339 x).toNat := by
  have h := u112 x
  omega
def w_n340 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n73 x).toNat + 2 * (w_n76 x).toNat + 4 * (w_n154 x).toNat + 8 * (w_n157 x).toNat + 16 * (w_n164 x).toNat + 32 * (w_n241 x).toNat)
def w_n341 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n73 x).toNat + 2 * (w_n76 x).toNat + 4 * (w_n154 x).toNat + 8 * (w_n157 x).toNat + 16 * (w_n164 x).toNat + 32 * (w_n241 x).toNat)
def w_n342 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n73 x).toNat + 2 * (w_n76 x).toNat + 4 * (w_n154 x).toNat + 8 * (w_n157 x).toNat + 16 * (w_n164 x).toNat + 32 * (w_n241 x).toNat)
theorem u113 (x : Nat → Bool) : (w_n73 x).toNat + (w_n76 x).toNat + (w_n154 x).toNat + (w_n157 x).toNat + (w_n164 x).toNat + (w_n241 x).toNat = (w_n340 x).toNat + 2 * (w_n341 x).toNat + 4 * (w_n342 x).toNat := g0 _ _ _ _ _ _ 
theorem e113 (x : Nat → Bool) : 4 * (w_n73 x).toNat + 4 * (w_n76 x).toNat + 4 * (w_n154 x).toNat + 4 * (w_n157 x).toNat + 4 * (w_n164 x).toNat + 4 * (w_n241 x).toNat = 4 * (w_n340 x).toNat + 8 * (w_n341 x).toNat + 16 * (w_n342 x).toNat := by
  have h := u113 x
  omega
def w_n343 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n244 x).toNat + 2 * (w_n322 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n332 x).toNat + 16 * (w_n338 x).toNat + 32 * (w_n340 x).toNat)
def w_n344 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n244 x).toNat + 2 * (w_n322 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n332 x).toNat + 16 * (w_n338 x).toNat + 32 * (w_n340 x).toNat)
def w_n345 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n244 x).toNat + 2 * (w_n322 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n332 x).toNat + 16 * (w_n338 x).toNat + 32 * (w_n340 x).toNat)
theorem u114 (x : Nat → Bool) : (w_n244 x).toNat + (w_n322 x).toNat + (w_n325 x).toNat + (w_n332 x).toNat + (w_n338 x).toNat + (w_n340 x).toNat = (w_n343 x).toNat + 2 * (w_n344 x).toNat + 4 * (w_n345 x).toNat := g0 _ _ _ _ _ _ 
theorem e114 (x : Nat → Bool) : 4 * (w_n244 x).toNat + 4 * (w_n322 x).toNat + 4 * (w_n325 x).toNat + 4 * (w_n332 x).toNat + 4 * (w_n338 x).toNat + 4 * (w_n340 x).toNat = 4 * (w_n343 x).toNat + 8 * (w_n344 x).toNat + 16 * (w_n345 x).toNat := by
  have h := u114 x
  omega
def w_n346 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n77 x).toNat + 2 * (w_n79 x).toNat + 4 * (w_n158 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n165 x).toNat + 32 * (w_n245 x).toNat)
def w_n347 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n77 x).toNat + 2 * (w_n79 x).toNat + 4 * (w_n158 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n165 x).toNat + 32 * (w_n245 x).toNat)
def w_n348 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n77 x).toNat + 2 * (w_n79 x).toNat + 4 * (w_n158 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n165 x).toNat + 32 * (w_n245 x).toNat)
theorem u115 (x : Nat → Bool) : (w_n77 x).toNat + (w_n79 x).toNat + (w_n158 x).toNat + (w_n160 x).toNat + (w_n165 x).toNat + (w_n245 x).toNat = (w_n346 x).toNat + 2 * (w_n347 x).toNat + 4 * (w_n348 x).toNat := g0 _ _ _ _ _ _ 
theorem e115 (x : Nat → Bool) : 8 * (w_n77 x).toNat + 8 * (w_n79 x).toNat + 8 * (w_n158 x).toNat + 8 * (w_n160 x).toNat + 8 * (w_n165 x).toNat + 8 * (w_n245 x).toNat = 8 * (w_n346 x).toNat + 16 * (w_n347 x).toNat + 32 * (w_n348 x).toNat := by
  have h := u115 x
  omega
def w_n349 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n247 x).toNat + 2 * (w_n326 x).toNat + 4 * (w_n328 x).toNat + 8 * (w_n333 x).toNat + 16 * (w_n339 x).toNat + 32 * (w_n341 x).toNat)
def w_n350 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n247 x).toNat + 2 * (w_n326 x).toNat + 4 * (w_n328 x).toNat + 8 * (w_n333 x).toNat + 16 * (w_n339 x).toNat + 32 * (w_n341 x).toNat)
def w_n351 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n247 x).toNat + 2 * (w_n326 x).toNat + 4 * (w_n328 x).toNat + 8 * (w_n333 x).toNat + 16 * (w_n339 x).toNat + 32 * (w_n341 x).toNat)
theorem u116 (x : Nat → Bool) : (w_n247 x).toNat + (w_n326 x).toNat + (w_n328 x).toNat + (w_n333 x).toNat + (w_n339 x).toNat + (w_n341 x).toNat = (w_n349 x).toNat + 2 * (w_n350 x).toNat + 4 * (w_n351 x).toNat := g0 _ _ _ _ _ _ 
theorem e116 (x : Nat → Bool) : 8 * (w_n247 x).toNat + 8 * (w_n326 x).toNat + 8 * (w_n328 x).toNat + 8 * (w_n333 x).toNat + 8 * (w_n339 x).toNat + 8 * (w_n341 x).toNat = 8 * (w_n349 x).toNat + 16 * (w_n350 x).toNat + 32 * (w_n351 x).toNat := by
  have h := u116 x
  omega
def w_n352 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n147 x).toNat + 2 * (w_n156 x).toNat + 4 * (w_n159 x).toNat + 8 * (w_n161 x).toNat + 16 * (w_n166 x).toNat + 32 * (w_n315 x).toNat)
def w_n353 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n147 x).toNat + 2 * (w_n156 x).toNat + 4 * (w_n159 x).toNat + 8 * (w_n161 x).toNat + 16 * (w_n166 x).toNat + 32 * (w_n315 x).toNat)
def w_n354 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n147 x).toNat + 2 * (w_n156 x).toNat + 4 * (w_n159 x).toNat + 8 * (w_n161 x).toNat + 16 * (w_n166 x).toNat + 32 * (w_n315 x).toNat)
theorem u117 (x : Nat → Bool) : (w_n147 x).toNat + (w_n156 x).toNat + (w_n159 x).toNat + (w_n161 x).toNat + (w_n166 x).toNat + (w_n315 x).toNat = (w_n352 x).toNat + 2 * (w_n353 x).toNat + 4 * (w_n354 x).toNat := g0 _ _ _ _ _ _ 
theorem e117 (x : Nat → Bool) : 16 * (w_n147 x).toNat + 16 * (w_n156 x).toNat + 16 * (w_n159 x).toNat + 16 * (w_n161 x).toNat + 16 * (w_n166 x).toNat + 16 * (w_n315 x).toNat = 16 * (w_n352 x).toNat + 32 * (w_n353 x).toNat + 64 * (w_n354 x).toNat := by
  have h := u117 x
  omega
def w_n355 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n324 x).toNat + 2 * (w_n327 x).toNat + 4 * (w_n329 x).toNat + 8 * (w_n334 x).toNat + 16 * (w_n342 x).toNat + 32 * (w_n345 x).toNat)
def w_n356 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n324 x).toNat + 2 * (w_n327 x).toNat + 4 * (w_n329 x).toNat + 8 * (w_n334 x).toNat + 16 * (w_n342 x).toNat + 32 * (w_n345 x).toNat)
def w_n357 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n324 x).toNat + 2 * (w_n327 x).toNat + 4 * (w_n329 x).toNat + 8 * (w_n334 x).toNat + 16 * (w_n342 x).toNat + 32 * (w_n345 x).toNat)
theorem u118 (x : Nat → Bool) : (w_n324 x).toNat + (w_n327 x).toNat + (w_n329 x).toNat + (w_n334 x).toNat + (w_n342 x).toNat + (w_n345 x).toNat = (w_n355 x).toNat + 2 * (w_n356 x).toNat + 4 * (w_n357 x).toNat := g0 _ _ _ _ _ _ 
theorem e118 (x : Nat → Bool) : 16 * (w_n324 x).toNat + 16 * (w_n327 x).toNat + 16 * (w_n329 x).toNat + 16 * (w_n334 x).toNat + 16 * (w_n342 x).toNat + 16 * (w_n345 x).toNat = 16 * (w_n355 x).toNat + 32 * (w_n356 x).toNat + 64 * (w_n357 x).toNat := by
  have h := u118 x
  omega
def w_n358 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n81 x).toNat + 2 * (w_n162 x).toNat + 4 * (w_n167 x).toNat + 8 * (w_n249 x).toNat + 16 * (w_n330 x).toNat + 32 * (w_n335 x).toNat)
def w_n359 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n81 x).toNat + 2 * (w_n162 x).toNat + 4 * (w_n167 x).toNat + 8 * (w_n249 x).toNat + 16 * (w_n330 x).toNat + 32 * (w_n335 x).toNat)
def w_n360 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n81 x).toNat + 2 * (w_n162 x).toNat + 4 * (w_n167 x).toNat + 8 * (w_n249 x).toNat + 16 * (w_n330 x).toNat + 32 * (w_n335 x).toNat)
theorem u119 (x : Nat → Bool) : (w_n81 x).toNat + (w_n162 x).toNat + (w_n167 x).toNat + (w_n249 x).toNat + (w_n330 x).toNat + (w_n335 x).toNat = (w_n358 x).toNat + 2 * (w_n359 x).toNat + 4 * (w_n360 x).toNat := g0 _ _ _ _ _ _ 
theorem e119 (x : Nat → Bool) : 32 * (w_n81 x).toNat + 32 * (w_n162 x).toNat + 32 * (w_n167 x).toNat + 32 * (w_n249 x).toNat + 32 * (w_n330 x).toNat + 32 * (w_n335 x).toNat = 32 * (w_n358 x).toNat + 64 * (w_n359 x).toNat + 128 * (w_n360 x).toNat := by
  have h := u119 x
  omega
def w_n361 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 871).toNat + 2 * (x 872).toNat + 4 * (x 873).toNat + 8 * (x 874).toNat + 16 * (x 875).toNat + 32 * (x 876).toNat)
def w_n362 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 871).toNat + 2 * (x 872).toNat + 4 * (x 873).toNat + 8 * (x 874).toNat + 16 * (x 875).toNat + 32 * (x 876).toNat)
def w_n363 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 871).toNat + 2 * (x 872).toNat + 4 * (x 873).toNat + 8 * (x 874).toNat + 16 * (x 875).toNat + 32 * (x 876).toNat)
theorem u120 (x : Nat → Bool) : (x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat = (w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat := g0 _ _ _ _ _ _ 
theorem e120 (x : Nat → Bool) : (x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat = (w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat := by
  have h := u120 x
  omega
def w_n364 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 877).toNat + 2 * (x 878).toNat + 4 * (x 879).toNat + 8 * (x 880).toNat + 16 * (x 881).toNat + 32 * (x 882).toNat)
def w_n365 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 877).toNat + 2 * (x 878).toNat + 4 * (x 879).toNat + 8 * (x 880).toNat + 16 * (x 881).toNat + 32 * (x 882).toNat)
def w_n366 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 877).toNat + 2 * (x 878).toNat + 4 * (x 879).toNat + 8 * (x 880).toNat + 16 * (x 881).toNat + 32 * (x 882).toNat)
theorem u121 (x : Nat → Bool) : (x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat = (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat := g0 _ _ _ _ _ _ 
theorem e121 (x : Nat → Bool) : (x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat = (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat := by
  have h := u121 x
  omega
def w_n367 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 883).toNat + 2 * (x 884).toNat + 4 * (x 885).toNat + 8 * (x 886).toNat + 16 * (x 887).toNat + 32 * (x 888).toNat)
def w_n368 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 883).toNat + 2 * (x 884).toNat + 4 * (x 885).toNat + 8 * (x 886).toNat + 16 * (x 887).toNat + 32 * (x 888).toNat)
def w_n369 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 883).toNat + 2 * (x 884).toNat + 4 * (x 885).toNat + 8 * (x 886).toNat + 16 * (x 887).toNat + 32 * (x 888).toNat)
theorem u122 (x : Nat → Bool) : (x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat = (w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat := g0 _ _ _ _ _ _ 
theorem e122 (x : Nat → Bool) : (x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat = (w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat := by
  have h := u122 x
  omega
def w_n370 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 889).toNat + 2 * (x 890).toNat + 4 * (x 891).toNat + 8 * (x 892).toNat + 16 * (x 893).toNat + 32 * (x 894).toNat)
def w_n371 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 889).toNat + 2 * (x 890).toNat + 4 * (x 891).toNat + 8 * (x 892).toNat + 16 * (x 893).toNat + 32 * (x 894).toNat)
def w_n372 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 889).toNat + 2 * (x 890).toNat + 4 * (x 891).toNat + 8 * (x 892).toNat + 16 * (x 893).toNat + 32 * (x 894).toNat)
theorem u123 (x : Nat → Bool) : (x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat = (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat := g0 _ _ _ _ _ _ 
theorem e123 (x : Nat → Bool) : (x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat = (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat := by
  have h := u123 x
  omega
def w_n373 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 859).toNat + 2 * (x 860).toNat + 4 * (x 861).toNat + 8 * (x 862).toNat + 16 * (x 863).toNat + 32 * (x 864).toNat)
def w_n374 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 859).toNat + 2 * (x 860).toNat + 4 * (x 861).toNat + 8 * (x 862).toNat + 16 * (x 863).toNat + 32 * (x 864).toNat)
def w_n375 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 859).toNat + 2 * (x 860).toNat + 4 * (x 861).toNat + 8 * (x 862).toNat + 16 * (x 863).toNat + 32 * (x 864).toNat)
theorem u124 (x : Nat → Bool) : (x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat = (w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat := g0 _ _ _ _ _ _ 
theorem e124 (x : Nat → Bool) : (x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat = (w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat := by
  have h := u124 x
  omega
def w_n376 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 865).toNat + 2 * (x 866).toNat + 4 * (x 867).toNat + 8 * (x 868).toNat + 16 * (x 869).toNat + 32 * (x 870).toNat)
def w_n377 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 865).toNat + 2 * (x 866).toNat + 4 * (x 867).toNat + 8 * (x 868).toNat + 16 * (x 869).toNat + 32 * (x 870).toNat)
def w_n378 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 865).toNat + 2 * (x 866).toNat + 4 * (x 867).toNat + 8 * (x 868).toNat + 16 * (x 869).toNat + 32 * (x 870).toNat)
theorem u125 (x : Nat → Bool) : (x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat = (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat := g0 _ _ _ _ _ _ 
theorem e125 (x : Nat → Bool) : (x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat = (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat := by
  have h := u125 x
  omega
def w_n379 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 847).toNat + 2 * (x 848).toNat + 4 * (x 849).toNat + 8 * (x 850).toNat + 16 * (x 851).toNat + 32 * (x 852).toNat)
def w_n380 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 847).toNat + 2 * (x 848).toNat + 4 * (x 849).toNat + 8 * (x 850).toNat + 16 * (x 851).toNat + 32 * (x 852).toNat)
def w_n381 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 847).toNat + 2 * (x 848).toNat + 4 * (x 849).toNat + 8 * (x 850).toNat + 16 * (x 851).toNat + 32 * (x 852).toNat)
theorem u126 (x : Nat → Bool) : (x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat = (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat := g0 _ _ _ _ _ _ 
theorem e126 (x : Nat → Bool) : (x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat = (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat := by
  have h := u126 x
  omega
def w_n382 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 853).toNat + 2 * (x 854).toNat + 4 * (x 855).toNat + 8 * (x 856).toNat + 16 * (x 857).toNat + 32 * (x 858).toNat)
def w_n383 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 853).toNat + 2 * (x 854).toNat + 4 * (x 855).toNat + 8 * (x 856).toNat + 16 * (x 857).toNat + 32 * (x 858).toNat)
def w_n384 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 853).toNat + 2 * (x 854).toNat + 4 * (x 855).toNat + 8 * (x 856).toNat + 16 * (x 857).toNat + 32 * (x 858).toNat)
theorem u127 (x : Nat → Bool) : (x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat = (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat := g0 _ _ _ _ _ _ 
theorem e127 (x : Nat → Bool) : (x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat = (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat := by
  have h := u127 x
  omega
def w_n385 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n361 x).toNat + 2 * (w_n364 x).toNat + 4 * (w_n367 x).toNat + 8 * (w_n370 x).toNat + 16 * (w_n373 x).toNat + 32 * (w_n376 x).toNat)
def w_n386 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n361 x).toNat + 2 * (w_n364 x).toNat + 4 * (w_n367 x).toNat + 8 * (w_n370 x).toNat + 16 * (w_n373 x).toNat + 32 * (w_n376 x).toNat)
def w_n387 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n361 x).toNat + 2 * (w_n364 x).toNat + 4 * (w_n367 x).toNat + 8 * (w_n370 x).toNat + 16 * (w_n373 x).toNat + 32 * (w_n376 x).toNat)
theorem u128 (x : Nat → Bool) : (w_n361 x).toNat + (w_n364 x).toNat + (w_n367 x).toNat + (w_n370 x).toNat + (w_n373 x).toNat + (w_n376 x).toNat = (w_n385 x).toNat + 2 * (w_n386 x).toNat + 4 * (w_n387 x).toNat := g0 _ _ _ _ _ _ 
theorem e128 (x : Nat → Bool) : (w_n361 x).toNat + (w_n364 x).toNat + (w_n367 x).toNat + (w_n370 x).toNat + (w_n373 x).toNat + (w_n376 x).toNat = (w_n385 x).toNat + 2 * (w_n386 x).toNat + 4 * (w_n387 x).toNat := by
  have h := u128 x
  omega
def w_n388 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n362 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n368 x).toNat + 8 * (w_n371 x).toNat + 16 * (w_n374 x).toNat + 32 * (w_n377 x).toNat)
def w_n389 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n362 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n368 x).toNat + 8 * (w_n371 x).toNat + 16 * (w_n374 x).toNat + 32 * (w_n377 x).toNat)
def w_n390 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n362 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n368 x).toNat + 8 * (w_n371 x).toNat + 16 * (w_n374 x).toNat + 32 * (w_n377 x).toNat)
theorem u129 (x : Nat → Bool) : (w_n362 x).toNat + (w_n365 x).toNat + (w_n368 x).toNat + (w_n371 x).toNat + (w_n374 x).toNat + (w_n377 x).toNat = (w_n388 x).toNat + 2 * (w_n389 x).toNat + 4 * (w_n390 x).toNat := g0 _ _ _ _ _ _ 
theorem e129 (x : Nat → Bool) : 2 * (w_n362 x).toNat + 2 * (w_n365 x).toNat + 2 * (w_n368 x).toNat + 2 * (w_n371 x).toNat + 2 * (w_n374 x).toNat + 2 * (w_n377 x).toNat = 2 * (w_n388 x).toNat + 4 * (w_n389 x).toNat + 8 * (w_n390 x).toNat := by
  have h := u129 x
  omega
def w_n391 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n363 x).toNat + 2 * (w_n366 x).toNat + 4 * (w_n369 x).toNat + 8 * (w_n372 x).toNat + 16 * (w_n375 x).toNat + 32 * (w_n378 x).toNat)
def w_n392 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n363 x).toNat + 2 * (w_n366 x).toNat + 4 * (w_n369 x).toNat + 8 * (w_n372 x).toNat + 16 * (w_n375 x).toNat + 32 * (w_n378 x).toNat)
def w_n393 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n363 x).toNat + 2 * (w_n366 x).toNat + 4 * (w_n369 x).toNat + 8 * (w_n372 x).toNat + 16 * (w_n375 x).toNat + 32 * (w_n378 x).toNat)
theorem u130 (x : Nat → Bool) : (w_n363 x).toNat + (w_n366 x).toNat + (w_n369 x).toNat + (w_n372 x).toNat + (w_n375 x).toNat + (w_n378 x).toNat = (w_n391 x).toNat + 2 * (w_n392 x).toNat + 4 * (w_n393 x).toNat := g0 _ _ _ _ _ _ 
theorem e130 (x : Nat → Bool) : 4 * (w_n363 x).toNat + 4 * (w_n366 x).toNat + 4 * (w_n369 x).toNat + 4 * (w_n372 x).toNat + 4 * (w_n375 x).toNat + 4 * (w_n378 x).toNat = 4 * (w_n391 x).toNat + 8 * (w_n392 x).toNat + 16 * (w_n393 x).toNat := by
  have h := u130 x
  omega
def w_n394 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 937).toNat + 2 * (x 938).toNat + 4 * (x 939).toNat + 8 * (x 940).toNat + 16 * (x 941).toNat + 32 * (x 942).toNat)
def w_n395 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 937).toNat + 2 * (x 938).toNat + 4 * (x 939).toNat + 8 * (x 940).toNat + 16 * (x 941).toNat + 32 * (x 942).toNat)
def w_n396 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 937).toNat + 2 * (x 938).toNat + 4 * (x 939).toNat + 8 * (x 940).toNat + 16 * (x 941).toNat + 32 * (x 942).toNat)
theorem u131 (x : Nat → Bool) : (x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat = (w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat := g0 _ _ _ _ _ _ 
theorem e131 (x : Nat → Bool) : (x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat = (w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat := by
  have h := u131 x
  omega
def w_n397 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 931).toNat + 2 * (x 932).toNat + 4 * (x 933).toNat + 8 * (x 934).toNat + 16 * (x 935).toNat + 32 * (x 936).toNat)
def w_n398 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 931).toNat + 2 * (x 932).toNat + 4 * (x 933).toNat + 8 * (x 934).toNat + 16 * (x 935).toNat + 32 * (x 936).toNat)
def w_n399 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 931).toNat + 2 * (x 932).toNat + 4 * (x 933).toNat + 8 * (x 934).toNat + 16 * (x 935).toNat + 32 * (x 936).toNat)
theorem u132 (x : Nat → Bool) : (x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat = (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat := g0 _ _ _ _ _ _ 
theorem e132 (x : Nat → Bool) : (x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat = (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat := by
  have h := u132 x
  omega
def w_n400 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 925).toNat + 2 * (x 926).toNat + 4 * (x 927).toNat + 8 * (x 928).toNat + 16 * (x 929).toNat + 32 * (x 930).toNat)
def w_n401 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 925).toNat + 2 * (x 926).toNat + 4 * (x 927).toNat + 8 * (x 928).toNat + 16 * (x 929).toNat + 32 * (x 930).toNat)
def w_n402 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 925).toNat + 2 * (x 926).toNat + 4 * (x 927).toNat + 8 * (x 928).toNat + 16 * (x 929).toNat + 32 * (x 930).toNat)
theorem u133 (x : Nat → Bool) : (x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat = (w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat := g0 _ _ _ _ _ _ 
theorem e133 (x : Nat → Bool) : (x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat = (w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat := by
  have h := u133 x
  omega
def w_n403 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 919).toNat + 2 * (x 920).toNat + 4 * (x 921).toNat + 8 * (x 922).toNat + 16 * (x 923).toNat + 32 * (x 924).toNat)
def w_n404 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 919).toNat + 2 * (x 920).toNat + 4 * (x 921).toNat + 8 * (x 922).toNat + 16 * (x 923).toNat + 32 * (x 924).toNat)
def w_n405 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 919).toNat + 2 * (x 920).toNat + 4 * (x 921).toNat + 8 * (x 922).toNat + 16 * (x 923).toNat + 32 * (x 924).toNat)
theorem u134 (x : Nat → Bool) : (x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat = (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat := g0 _ _ _ _ _ _ 
theorem e134 (x : Nat → Bool) : (x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat = (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat := by
  have h := u134 x
  omega
def w_n406 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 901).toNat + 2 * (x 902).toNat + 4 * (x 903).toNat + 8 * (x 904).toNat + 16 * (x 905).toNat + 32 * (x 906).toNat)
def w_n407 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 901).toNat + 2 * (x 902).toNat + 4 * (x 903).toNat + 8 * (x 904).toNat + 16 * (x 905).toNat + 32 * (x 906).toNat)
def w_n408 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 901).toNat + 2 * (x 902).toNat + 4 * (x 903).toNat + 8 * (x 904).toNat + 16 * (x 905).toNat + 32 * (x 906).toNat)
theorem u135 (x : Nat → Bool) : (x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat = (w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat := g0 _ _ _ _ _ _ 
theorem e135 (x : Nat → Bool) : (x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat = (w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat := by
  have h := u135 x
  omega
def w_n409 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 895).toNat + 2 * (x 896).toNat + 4 * (x 897).toNat + 8 * (x 898).toNat + 16 * (x 899).toNat + 32 * (x 900).toNat)
def w_n410 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 895).toNat + 2 * (x 896).toNat + 4 * (x 897).toNat + 8 * (x 898).toNat + 16 * (x 899).toNat + 32 * (x 900).toNat)
def w_n411 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 895).toNat + 2 * (x 896).toNat + 4 * (x 897).toNat + 8 * (x 898).toNat + 16 * (x 899).toNat + 32 * (x 900).toNat)
theorem u136 (x : Nat → Bool) : (x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat = (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat := g0 _ _ _ _ _ _ 
theorem e136 (x : Nat → Bool) : (x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat = (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat := by
  have h := u136 x
  omega
def w_n412 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 913).toNat + 2 * (x 914).toNat + 4 * (x 915).toNat + 8 * (x 916).toNat + 16 * (x 917).toNat + 32 * (x 918).toNat)
def w_n413 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 913).toNat + 2 * (x 914).toNat + 4 * (x 915).toNat + 8 * (x 916).toNat + 16 * (x 917).toNat + 32 * (x 918).toNat)
def w_n414 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 913).toNat + 2 * (x 914).toNat + 4 * (x 915).toNat + 8 * (x 916).toNat + 16 * (x 917).toNat + 32 * (x 918).toNat)
theorem u137 (x : Nat → Bool) : (x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat = (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat := g0 _ _ _ _ _ _ 
theorem e137 (x : Nat → Bool) : (x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat = (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat := by
  have h := u137 x
  omega
def w_n415 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 907).toNat + 2 * (x 908).toNat + 4 * (x 909).toNat + 8 * (x 910).toNat + 16 * (x 911).toNat + 32 * (x 912).toNat)
def w_n416 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 907).toNat + 2 * (x 908).toNat + 4 * (x 909).toNat + 8 * (x 910).toNat + 16 * (x 911).toNat + 32 * (x 912).toNat)
def w_n417 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 907).toNat + 2 * (x 908).toNat + 4 * (x 909).toNat + 8 * (x 910).toNat + 16 * (x 911).toNat + 32 * (x 912).toNat)
theorem u138 (x : Nat → Bool) : (x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat = (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat := g0 _ _ _ _ _ _ 
theorem e138 (x : Nat → Bool) : (x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat = (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat := by
  have h := u138 x
  omega
def w_n418 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n394 x).toNat + 2 * (w_n397 x).toNat + 4 * (w_n400 x).toNat + 8 * (w_n403 x).toNat + 16 * (w_n406 x).toNat + 32 * (w_n409 x).toNat)
def w_n419 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n394 x).toNat + 2 * (w_n397 x).toNat + 4 * (w_n400 x).toNat + 8 * (w_n403 x).toNat + 16 * (w_n406 x).toNat + 32 * (w_n409 x).toNat)
def w_n420 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n394 x).toNat + 2 * (w_n397 x).toNat + 4 * (w_n400 x).toNat + 8 * (w_n403 x).toNat + 16 * (w_n406 x).toNat + 32 * (w_n409 x).toNat)
theorem u139 (x : Nat → Bool) : (w_n394 x).toNat + (w_n397 x).toNat + (w_n400 x).toNat + (w_n403 x).toNat + (w_n406 x).toNat + (w_n409 x).toNat = (w_n418 x).toNat + 2 * (w_n419 x).toNat + 4 * (w_n420 x).toNat := g0 _ _ _ _ _ _ 
theorem e139 (x : Nat → Bool) : (w_n394 x).toNat + (w_n397 x).toNat + (w_n400 x).toNat + (w_n403 x).toNat + (w_n406 x).toNat + (w_n409 x).toNat = (w_n418 x).toNat + 2 * (w_n419 x).toNat + 4 * (w_n420 x).toNat := by
  have h := u139 x
  omega
def w_n421 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n395 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n401 x).toNat + 8 * (w_n404 x).toNat + 16 * (w_n407 x).toNat + 32 * (w_n410 x).toNat)
def w_n422 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n395 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n401 x).toNat + 8 * (w_n404 x).toNat + 16 * (w_n407 x).toNat + 32 * (w_n410 x).toNat)
def w_n423 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n395 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n401 x).toNat + 8 * (w_n404 x).toNat + 16 * (w_n407 x).toNat + 32 * (w_n410 x).toNat)
theorem u140 (x : Nat → Bool) : (w_n395 x).toNat + (w_n398 x).toNat + (w_n401 x).toNat + (w_n404 x).toNat + (w_n407 x).toNat + (w_n410 x).toNat = (w_n421 x).toNat + 2 * (w_n422 x).toNat + 4 * (w_n423 x).toNat := g0 _ _ _ _ _ _ 
theorem e140 (x : Nat → Bool) : 2 * (w_n395 x).toNat + 2 * (w_n398 x).toNat + 2 * (w_n401 x).toNat + 2 * (w_n404 x).toNat + 2 * (w_n407 x).toNat + 2 * (w_n410 x).toNat = 2 * (w_n421 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n423 x).toNat := by
  have h := u140 x
  omega
def w_n424 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n396 x).toNat + 2 * (w_n399 x).toNat + 4 * (w_n402 x).toNat + 8 * (w_n405 x).toNat + 16 * (w_n408 x).toNat + 32 * (w_n411 x).toNat)
def w_n425 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n396 x).toNat + 2 * (w_n399 x).toNat + 4 * (w_n402 x).toNat + 8 * (w_n405 x).toNat + 16 * (w_n408 x).toNat + 32 * (w_n411 x).toNat)
def w_n426 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n396 x).toNat + 2 * (w_n399 x).toNat + 4 * (w_n402 x).toNat + 8 * (w_n405 x).toNat + 16 * (w_n408 x).toNat + 32 * (w_n411 x).toNat)
theorem u141 (x : Nat → Bool) : (w_n396 x).toNat + (w_n399 x).toNat + (w_n402 x).toNat + (w_n405 x).toNat + (w_n408 x).toNat + (w_n411 x).toNat = (w_n424 x).toNat + 2 * (w_n425 x).toNat + 4 * (w_n426 x).toNat := g0 _ _ _ _ _ _ 
theorem e141 (x : Nat → Bool) : 4 * (w_n396 x).toNat + 4 * (w_n399 x).toNat + 4 * (w_n402 x).toNat + 4 * (w_n405 x).toNat + 4 * (w_n408 x).toNat + 4 * (w_n411 x).toNat = 4 * (w_n424 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n426 x).toNat := by
  have h := u141 x
  omega
def w_n427 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n379 x).toNat + 2 * (w_n382 x).toNat + 4 * (w_n385 x).toNat + 8 * (w_n412 x).toNat + 16 * (w_n415 x).toNat + 32 * (w_n418 x).toNat)
def w_n428 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n379 x).toNat + 2 * (w_n382 x).toNat + 4 * (w_n385 x).toNat + 8 * (w_n412 x).toNat + 16 * (w_n415 x).toNat + 32 * (w_n418 x).toNat)
def w_n429 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n379 x).toNat + 2 * (w_n382 x).toNat + 4 * (w_n385 x).toNat + 8 * (w_n412 x).toNat + 16 * (w_n415 x).toNat + 32 * (w_n418 x).toNat)
theorem u142 (x : Nat → Bool) : (w_n379 x).toNat + (w_n382 x).toNat + (w_n385 x).toNat + (w_n412 x).toNat + (w_n415 x).toNat + (w_n418 x).toNat = (w_n427 x).toNat + 2 * (w_n428 x).toNat + 4 * (w_n429 x).toNat := g0 _ _ _ _ _ _ 
theorem e142 (x : Nat → Bool) : (w_n379 x).toNat + (w_n382 x).toNat + (w_n385 x).toNat + (w_n412 x).toNat + (w_n415 x).toNat + (w_n418 x).toNat = (w_n427 x).toNat + 2 * (w_n428 x).toNat + 4 * (w_n429 x).toNat := by
  have h := u142 x
  omega
def w_n430 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n380 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n386 x).toNat + 8 * (w_n388 x).toNat + 16 * (w_n413 x).toNat + 32 * (w_n416 x).toNat)
def w_n431 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n380 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n386 x).toNat + 8 * (w_n388 x).toNat + 16 * (w_n413 x).toNat + 32 * (w_n416 x).toNat)
def w_n432 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n380 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n386 x).toNat + 8 * (w_n388 x).toNat + 16 * (w_n413 x).toNat + 32 * (w_n416 x).toNat)
theorem u143 (x : Nat → Bool) : (w_n380 x).toNat + (w_n383 x).toNat + (w_n386 x).toNat + (w_n388 x).toNat + (w_n413 x).toNat + (w_n416 x).toNat = (w_n430 x).toNat + 2 * (w_n431 x).toNat + 4 * (w_n432 x).toNat := g0 _ _ _ _ _ _ 
theorem e143 (x : Nat → Bool) : 2 * (w_n380 x).toNat + 2 * (w_n383 x).toNat + 2 * (w_n386 x).toNat + 2 * (w_n388 x).toNat + 2 * (w_n413 x).toNat + 2 * (w_n416 x).toNat = 2 * (w_n430 x).toNat + 4 * (w_n431 x).toNat + 8 * (w_n432 x).toNat := by
  have h := u143 x
  omega
def w_n433 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n381 x).toNat + 2 * (w_n384 x).toNat + 4 * (w_n387 x).toNat + 8 * (w_n389 x).toNat + 16 * (w_n391 x).toNat + 32 * (w_n414 x).toNat)
def w_n434 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n381 x).toNat + 2 * (w_n384 x).toNat + 4 * (w_n387 x).toNat + 8 * (w_n389 x).toNat + 16 * (w_n391 x).toNat + 32 * (w_n414 x).toNat)
def w_n435 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n381 x).toNat + 2 * (w_n384 x).toNat + 4 * (w_n387 x).toNat + 8 * (w_n389 x).toNat + 16 * (w_n391 x).toNat + 32 * (w_n414 x).toNat)
theorem u144 (x : Nat → Bool) : (w_n381 x).toNat + (w_n384 x).toNat + (w_n387 x).toNat + (w_n389 x).toNat + (w_n391 x).toNat + (w_n414 x).toNat = (w_n433 x).toNat + 2 * (w_n434 x).toNat + 4 * (w_n435 x).toNat := g0 _ _ _ _ _ _ 
theorem e144 (x : Nat → Bool) : 4 * (w_n381 x).toNat + 4 * (w_n384 x).toNat + 4 * (w_n387 x).toNat + 4 * (w_n389 x).toNat + 4 * (w_n391 x).toNat + 4 * (w_n414 x).toNat = 4 * (w_n433 x).toNat + 8 * (w_n434 x).toNat + 16 * (w_n435 x).toNat := by
  have h := u144 x
  omega
def w_n436 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n417 x).toNat + 2 * (w_n420 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n424 x).toNat + 16 * (w_n429 x).toNat + 32 * (w_n431 x).toNat)
def w_n437 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n417 x).toNat + 2 * (w_n420 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n424 x).toNat + 16 * (w_n429 x).toNat + 32 * (w_n431 x).toNat)
def w_n438 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n417 x).toNat + 2 * (w_n420 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n424 x).toNat + 16 * (w_n429 x).toNat + 32 * (w_n431 x).toNat)
theorem u145 (x : Nat → Bool) : (w_n417 x).toNat + (w_n420 x).toNat + (w_n422 x).toNat + (w_n424 x).toNat + (w_n429 x).toNat + (w_n431 x).toNat = (w_n436 x).toNat + 2 * (w_n437 x).toNat + 4 * (w_n438 x).toNat := g0 _ _ _ _ _ _ 
theorem e145 (x : Nat → Bool) : 4 * (w_n417 x).toNat + 4 * (w_n420 x).toNat + 4 * (w_n422 x).toNat + 4 * (w_n424 x).toNat + 4 * (w_n429 x).toNat + 4 * (w_n431 x).toNat = 4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 16 * (w_n438 x).toNat := by
  have h := u145 x
  omega
def w_n439 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n390 x).toNat + 2 * (w_n392 x).toNat + 4 * (w_n423 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n432 x).toNat + 32 * (w_n434 x).toNat)
def w_n440 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n390 x).toNat + 2 * (w_n392 x).toNat + 4 * (w_n423 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n432 x).toNat + 32 * (w_n434 x).toNat)
def w_n441 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n390 x).toNat + 2 * (w_n392 x).toNat + 4 * (w_n423 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n432 x).toNat + 32 * (w_n434 x).toNat)
theorem u146 (x : Nat → Bool) : (w_n390 x).toNat + (w_n392 x).toNat + (w_n423 x).toNat + (w_n425 x).toNat + (w_n432 x).toNat + (w_n434 x).toNat = (w_n439 x).toNat + 2 * (w_n440 x).toNat + 4 * (w_n441 x).toNat := g0 _ _ _ _ _ _ 
theorem e146 (x : Nat → Bool) : 8 * (w_n390 x).toNat + 8 * (w_n392 x).toNat + 8 * (w_n423 x).toNat + 8 * (w_n425 x).toNat + 8 * (w_n432 x).toNat + 8 * (w_n434 x).toNat = 8 * (w_n439 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n441 x).toNat := by
  have h := u146 x
  omega
def w_n442 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 961).toNat + 2 * (x 962).toNat + 4 * (x 963).toNat + 8 * (x 964).toNat + 16 * (x 965).toNat + 32 * (x 966).toNat)
def w_n443 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 961).toNat + 2 * (x 962).toNat + 4 * (x 963).toNat + 8 * (x 964).toNat + 16 * (x 965).toNat + 32 * (x 966).toNat)
def w_n444 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 961).toNat + 2 * (x 962).toNat + 4 * (x 963).toNat + 8 * (x 964).toNat + 16 * (x 965).toNat + 32 * (x 966).toNat)
theorem u147 (x : Nat → Bool) : (x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat = (w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat := g0 _ _ _ _ _ _ 
theorem e147 (x : Nat → Bool) : (x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat = (w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat := by
  have h := u147 x
  omega
def w_n445 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 955).toNat + 2 * (x 956).toNat + 4 * (x 957).toNat + 8 * (x 958).toNat + 16 * (x 959).toNat + 32 * (x 960).toNat)
def w_n446 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 955).toNat + 2 * (x 956).toNat + 4 * (x 957).toNat + 8 * (x 958).toNat + 16 * (x 959).toNat + 32 * (x 960).toNat)
def w_n447 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 955).toNat + 2 * (x 956).toNat + 4 * (x 957).toNat + 8 * (x 958).toNat + 16 * (x 959).toNat + 32 * (x 960).toNat)
theorem u148 (x : Nat → Bool) : (x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat = (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat := g0 _ _ _ _ _ _ 
theorem e148 (x : Nat → Bool) : (x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat = (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat := by
  have h := u148 x
  omega
def w_n448 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 943).toNat + 2 * (x 944).toNat + 4 * (x 945).toNat + 8 * (x 946).toNat + 16 * (x 947).toNat + 32 * (x 948).toNat)
def w_n449 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 943).toNat + 2 * (x 944).toNat + 4 * (x 945).toNat + 8 * (x 946).toNat + 16 * (x 947).toNat + 32 * (x 948).toNat)
def w_n450 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 943).toNat + 2 * (x 944).toNat + 4 * (x 945).toNat + 8 * (x 946).toNat + 16 * (x 947).toNat + 32 * (x 948).toNat)
theorem u149 (x : Nat → Bool) : (x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat = (w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat := g0 _ _ _ _ _ _ 
theorem e149 (x : Nat → Bool) : (x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat = (w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat := by
  have h := u149 x
  omega
def w_n451 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 949).toNat + 2 * (x 950).toNat + 4 * (x 951).toNat + 8 * (x 952).toNat + 16 * (x 953).toNat + 32 * (x 954).toNat)
def w_n452 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 949).toNat + 2 * (x 950).toNat + 4 * (x 951).toNat + 8 * (x 952).toNat + 16 * (x 953).toNat + 32 * (x 954).toNat)
def w_n453 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 949).toNat + 2 * (x 950).toNat + 4 * (x 951).toNat + 8 * (x 952).toNat + 16 * (x 953).toNat + 32 * (x 954).toNat)
theorem u150 (x : Nat → Bool) : (x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat = (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat := g0 _ _ _ _ _ _ 
theorem e150 (x : Nat → Bool) : (x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat = (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat := by
  have h := u150 x
  omega
def w_n454 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 973).toNat + 2 * (x 974).toNat + 4 * (x 975).toNat + 8 * (x 976).toNat + 16 * (x 977).toNat + 32 * (x 978).toNat)
def w_n455 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 973).toNat + 2 * (x 974).toNat + 4 * (x 975).toNat + 8 * (x 976).toNat + 16 * (x 977).toNat + 32 * (x 978).toNat)
def w_n456 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 973).toNat + 2 * (x 974).toNat + 4 * (x 975).toNat + 8 * (x 976).toNat + 16 * (x 977).toNat + 32 * (x 978).toNat)
theorem u151 (x : Nat → Bool) : (x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat = (w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat := g0 _ _ _ _ _ _ 
theorem e151 (x : Nat → Bool) : (x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat = (w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat := by
  have h := u151 x
  omega
def w_n457 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 967).toNat + 2 * (x 968).toNat + 4 * (x 969).toNat + 8 * (x 970).toNat + 16 * (x 971).toNat + 32 * (x 972).toNat)
def w_n458 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 967).toNat + 2 * (x 968).toNat + 4 * (x 969).toNat + 8 * (x 970).toNat + 16 * (x 971).toNat + 32 * (x 972).toNat)
def w_n459 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 967).toNat + 2 * (x 968).toNat + 4 * (x 969).toNat + 8 * (x 970).toNat + 16 * (x 971).toNat + 32 * (x 972).toNat)
theorem u152 (x : Nat → Bool) : (x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat = (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat := g0 _ _ _ _ _ _ 
theorem e152 (x : Nat → Bool) : (x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat = (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat := by
  have h := u152 x
  omega
def w_n460 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 985).toNat + 2 * (x 986).toNat + 4 * (x 987).toNat + 8 * (x 988).toNat + 16 * (x 989).toNat + 32 * (x 990).toNat)
def w_n461 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 985).toNat + 2 * (x 986).toNat + 4 * (x 987).toNat + 8 * (x 988).toNat + 16 * (x 989).toNat + 32 * (x 990).toNat)
def w_n462 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 985).toNat + 2 * (x 986).toNat + 4 * (x 987).toNat + 8 * (x 988).toNat + 16 * (x 989).toNat + 32 * (x 990).toNat)
theorem u153 (x : Nat → Bool) : (x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat = (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat := g0 _ _ _ _ _ _ 
theorem e153 (x : Nat → Bool) : (x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat = (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat := by
  have h := u153 x
  omega
def w_n463 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 979).toNat + 2 * (x 980).toNat + 4 * (x 981).toNat + 8 * (x 982).toNat + 16 * (x 983).toNat + 32 * (x 984).toNat)
def w_n464 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 979).toNat + 2 * (x 980).toNat + 4 * (x 981).toNat + 8 * (x 982).toNat + 16 * (x 983).toNat + 32 * (x 984).toNat)
def w_n465 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 979).toNat + 2 * (x 980).toNat + 4 * (x 981).toNat + 8 * (x 982).toNat + 16 * (x 983).toNat + 32 * (x 984).toNat)
theorem u154 (x : Nat → Bool) : (x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat = (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat := g0 _ _ _ _ _ _ 
theorem e154 (x : Nat → Bool) : (x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat = (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat := by
  have h := u154 x
  omega
def w_n466 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n442 x).toNat + 2 * (w_n445 x).toNat + 4 * (w_n448 x).toNat + 8 * (w_n451 x).toNat + 16 * (w_n454 x).toNat + 32 * (w_n457 x).toNat)
def w_n467 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n442 x).toNat + 2 * (w_n445 x).toNat + 4 * (w_n448 x).toNat + 8 * (w_n451 x).toNat + 16 * (w_n454 x).toNat + 32 * (w_n457 x).toNat)
def w_n468 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n442 x).toNat + 2 * (w_n445 x).toNat + 4 * (w_n448 x).toNat + 8 * (w_n451 x).toNat + 16 * (w_n454 x).toNat + 32 * (w_n457 x).toNat)
theorem u155 (x : Nat → Bool) : (w_n442 x).toNat + (w_n445 x).toNat + (w_n448 x).toNat + (w_n451 x).toNat + (w_n454 x).toNat + (w_n457 x).toNat = (w_n466 x).toNat + 2 * (w_n467 x).toNat + 4 * (w_n468 x).toNat := g0 _ _ _ _ _ _ 
theorem e155 (x : Nat → Bool) : (w_n442 x).toNat + (w_n445 x).toNat + (w_n448 x).toNat + (w_n451 x).toNat + (w_n454 x).toNat + (w_n457 x).toNat = (w_n466 x).toNat + 2 * (w_n467 x).toNat + 4 * (w_n468 x).toNat := by
  have h := u155 x
  omega
def w_n469 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n443 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n449 x).toNat + 8 * (w_n452 x).toNat + 16 * (w_n455 x).toNat + 32 * (w_n458 x).toNat)
def w_n470 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n443 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n449 x).toNat + 8 * (w_n452 x).toNat + 16 * (w_n455 x).toNat + 32 * (w_n458 x).toNat)
def w_n471 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n443 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n449 x).toNat + 8 * (w_n452 x).toNat + 16 * (w_n455 x).toNat + 32 * (w_n458 x).toNat)
theorem u156 (x : Nat → Bool) : (w_n443 x).toNat + (w_n446 x).toNat + (w_n449 x).toNat + (w_n452 x).toNat + (w_n455 x).toNat + (w_n458 x).toNat = (w_n469 x).toNat + 2 * (w_n470 x).toNat + 4 * (w_n471 x).toNat := g0 _ _ _ _ _ _ 
theorem e156 (x : Nat → Bool) : 2 * (w_n443 x).toNat + 2 * (w_n446 x).toNat + 2 * (w_n449 x).toNat + 2 * (w_n452 x).toNat + 2 * (w_n455 x).toNat + 2 * (w_n458 x).toNat = 2 * (w_n469 x).toNat + 4 * (w_n470 x).toNat + 8 * (w_n471 x).toNat := by
  have h := u156 x
  omega
def w_n472 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n444 x).toNat + 2 * (w_n447 x).toNat + 4 * (w_n450 x).toNat + 8 * (w_n453 x).toNat + 16 * (w_n456 x).toNat + 32 * (w_n459 x).toNat)
def w_n473 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n444 x).toNat + 2 * (w_n447 x).toNat + 4 * (w_n450 x).toNat + 8 * (w_n453 x).toNat + 16 * (w_n456 x).toNat + 32 * (w_n459 x).toNat)
def w_n474 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n444 x).toNat + 2 * (w_n447 x).toNat + 4 * (w_n450 x).toNat + 8 * (w_n453 x).toNat + 16 * (w_n456 x).toNat + 32 * (w_n459 x).toNat)
theorem u157 (x : Nat → Bool) : (w_n444 x).toNat + (w_n447 x).toNat + (w_n450 x).toNat + (w_n453 x).toNat + (w_n456 x).toNat + (w_n459 x).toNat = (w_n472 x).toNat + 2 * (w_n473 x).toNat + 4 * (w_n474 x).toNat := g0 _ _ _ _ _ _ 
theorem e157 (x : Nat → Bool) : 4 * (w_n444 x).toNat + 4 * (w_n447 x).toNat + 4 * (w_n450 x).toNat + 4 * (w_n453 x).toNat + 4 * (w_n456 x).toNat + 4 * (w_n459 x).toNat = 4 * (w_n472 x).toNat + 8 * (w_n473 x).toNat + 16 * (w_n474 x).toNat := by
  have h := u157 x
  omega
def w_n475 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 991).toNat + 2 * (x 992).toNat + 4 * (x 993).toNat + 8 * (x 994).toNat + 16 * (x 995).toNat + 32 * (x 996).toNat)
def w_n476 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 991).toNat + 2 * (x 992).toNat + 4 * (x 993).toNat + 8 * (x 994).toNat + 16 * (x 995).toNat + 32 * (x 996).toNat)
def w_n477 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 991).toNat + 2 * (x 992).toNat + 4 * (x 993).toNat + 8 * (x 994).toNat + 16 * (x 995).toNat + 32 * (x 996).toNat)
theorem u158 (x : Nat → Bool) : (x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat = (w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat := g0 _ _ _ _ _ _ 
theorem e158 (x : Nat → Bool) : (x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat = (w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat := by
  have h := u158 x
  omega
theorem g1 (a b c : Bool) : a.toNat + b.toNat + c.toNat = (lut 150 (a.toNat + 2 * b.toNat + 4 * c.toNat)).toNat + 2 * (lut 232 (a.toNat + 2 * b.toNat + 4 * c.toNat)).toNat := by
  cases a <;> cases b <;> cases c <;> rfl
def w_n478 (x : Nat → Bool) : Bool := lut 150 ((x 997).toNat + 2 * (x 998).toNat + 4 * (x 999).toNat)
def w_n479 (x : Nat → Bool) : Bool := lut 232 ((x 997).toNat + 2 * (x 998).toNat + 4 * (x 999).toNat)
theorem u159 (x : Nat → Bool) : (x 997).toNat + (x 998).toNat + (x 999).toNat = (w_n478 x).toNat + 2 * (w_n479 x).toNat := g1 _ _ _ 
theorem e159 (x : Nat → Bool) : (x 997).toNat + (x 998).toNat + (x 999).toNat = (w_n478 x).toNat + 2 * (w_n479 x).toNat := by
  have h := u159 x
  omega
def w_n480 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat + 16 * (x 4).toNat + 32 * (x 5).toNat)
def w_n481 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat + 16 * (x 4).toNat + 32 * (x 5).toNat)
def w_n482 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat + 16 * (x 4).toNat + 32 * (x 5).toNat)
theorem u160 (x : Nat → Bool) : (x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat = (w_n480 x).toNat + 2 * (w_n481 x).toNat + 4 * (w_n482 x).toNat := g0 _ _ _ _ _ _ 
theorem e160 (x : Nat → Bool) : (x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat = (w_n480 x).toNat + 2 * (w_n481 x).toNat + 4 * (w_n482 x).toNat := by
  have h := u160 x
  omega
theorem g2 (a b : Bool) : a.toNat + b.toNat = (lut 6 (a.toNat + 2 * b.toNat)).toNat + 2 * (lut 8 (a.toNat + 2 * b.toNat)).toNat := by
  cases a <;> cases b <;> rfl
def w_n483 (x : Nat → Bool) : Bool := lut 6 ((w_n480 x).toNat + 2 * (x 6).toNat)
def w_n484 (x : Nat → Bool) : Bool := lut 8 ((w_n480 x).toNat + 2 * (x 6).toNat)
theorem u161 (x : Nat → Bool) : (w_n480 x).toNat + (x 6).toNat = (w_n483 x).toNat + 2 * (w_n484 x).toNat := g2 _ _ 
theorem e161 (x : Nat → Bool) : (w_n480 x).toNat + (x 6).toNat = (w_n483 x).toNat + 2 * (w_n484 x).toNat := by
  have h := u161 x
  omega
def w_n485 (x : Nat → Bool) : Bool := lut 6 ((w_n481 x).toNat + 2 * (w_n484 x).toNat)
def w_n486 (x : Nat → Bool) : Bool := lut 8 ((w_n481 x).toNat + 2 * (w_n484 x).toNat)
theorem u162 (x : Nat → Bool) : (w_n481 x).toNat + (w_n484 x).toNat = (w_n485 x).toNat + 2 * (w_n486 x).toNat := g2 _ _ 
theorem e162 (x : Nat → Bool) : 2 * (w_n481 x).toNat + 2 * (w_n484 x).toNat = 2 * (w_n485 x).toNat + 4 * (w_n486 x).toNat := by
  have h := u162 x
  omega
def w_n487 (x : Nat → Bool) : Bool := lut 6 ((w_n482 x).toNat + 2 * (w_n486 x).toNat)
def w_n488 (x : Nat → Bool) : Bool := lut 8 ((w_n482 x).toNat + 2 * (w_n486 x).toNat)
theorem u163 (x : Nat → Bool) : (w_n482 x).toNat + (w_n486 x).toNat = (w_n487 x).toNat + 2 * (w_n488 x).toNat := g2 _ _ 
theorem e163 (x : Nat → Bool) : 4 * (w_n482 x).toNat + 4 * (w_n486 x).toNat = 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat := by
  have h := u163 x
  omega
def w_n489 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 25).toNat + 2 * (x 26).toNat + 4 * (x 27).toNat + 8 * (x 28).toNat + 16 * (x 29).toNat + 32 * (x 30).toNat)
def w_n490 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 25).toNat + 2 * (x 26).toNat + 4 * (x 27).toNat + 8 * (x 28).toNat + 16 * (x 29).toNat + 32 * (x 30).toNat)
def w_n491 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 25).toNat + 2 * (x 26).toNat + 4 * (x 27).toNat + 8 * (x 28).toNat + 16 * (x 29).toNat + 32 * (x 30).toNat)
theorem u164 (x : Nat → Bool) : (x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat = (w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat := g0 _ _ _ _ _ _ 
theorem e164 (x : Nat → Bool) : (x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat = (w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat := by
  have h := u164 x
  omega
def w_n492 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 19).toNat + 2 * (x 20).toNat + 4 * (x 21).toNat + 8 * (x 22).toNat + 16 * (x 23).toNat + 32 * (x 24).toNat)
def w_n493 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 19).toNat + 2 * (x 20).toNat + 4 * (x 21).toNat + 8 * (x 22).toNat + 16 * (x 23).toNat + 32 * (x 24).toNat)
def w_n494 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 19).toNat + 2 * (x 20).toNat + 4 * (x 21).toNat + 8 * (x 22).toNat + 16 * (x 23).toNat + 32 * (x 24).toNat)
theorem u165 (x : Nat → Bool) : (x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat = (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat := g0 _ _ _ _ _ _ 
theorem e165 (x : Nat → Bool) : (x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat = (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat := by
  have h := u165 x
  omega
def w_n495 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 13).toNat + 2 * (x 14).toNat + 4 * (x 15).toNat + 8 * (x 16).toNat + 16 * (x 17).toNat + 32 * (x 18).toNat)
def w_n496 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 13).toNat + 2 * (x 14).toNat + 4 * (x 15).toNat + 8 * (x 16).toNat + 16 * (x 17).toNat + 32 * (x 18).toNat)
def w_n497 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 13).toNat + 2 * (x 14).toNat + 4 * (x 15).toNat + 8 * (x 16).toNat + 16 * (x 17).toNat + 32 * (x 18).toNat)
theorem u166 (x : Nat → Bool) : (x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat = (w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat := g0 _ _ _ _ _ _ 
theorem e166 (x : Nat → Bool) : (x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat = (w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat := by
  have h := u166 x
  omega
def w_n498 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 7).toNat + 2 * (x 8).toNat + 4 * (x 9).toNat + 8 * (x 10).toNat + 16 * (x 11).toNat + 32 * (x 12).toNat)
def w_n499 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 7).toNat + 2 * (x 8).toNat + 4 * (x 9).toNat + 8 * (x 10).toNat + 16 * (x 11).toNat + 32 * (x 12).toNat)
def w_n500 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 7).toNat + 2 * (x 8).toNat + 4 * (x 9).toNat + 8 * (x 10).toNat + 16 * (x 11).toNat + 32 * (x 12).toNat)
theorem u167 (x : Nat → Bool) : (x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat = (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat := g0 _ _ _ _ _ _ 
theorem e167 (x : Nat → Bool) : (x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat = (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat := by
  have h := u167 x
  omega
def w_n501 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n475 x).toNat + 2 * (w_n478 x).toNat + 4 * (w_n483 x).toNat + 8 * (w_n489 x).toNat + 16 * (w_n492 x).toNat + 32 * (w_n495 x).toNat)
def w_n502 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n475 x).toNat + 2 * (w_n478 x).toNat + 4 * (w_n483 x).toNat + 8 * (w_n489 x).toNat + 16 * (w_n492 x).toNat + 32 * (w_n495 x).toNat)
def w_n503 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n475 x).toNat + 2 * (w_n478 x).toNat + 4 * (w_n483 x).toNat + 8 * (w_n489 x).toNat + 16 * (w_n492 x).toNat + 32 * (w_n495 x).toNat)
theorem u168 (x : Nat → Bool) : (w_n475 x).toNat + (w_n478 x).toNat + (w_n483 x).toNat + (w_n489 x).toNat + (w_n492 x).toNat + (w_n495 x).toNat = (w_n501 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n503 x).toNat := g0 _ _ _ _ _ _ 
theorem e168 (x : Nat → Bool) : (w_n475 x).toNat + (w_n478 x).toNat + (w_n483 x).toNat + (w_n489 x).toNat + (w_n492 x).toNat + (w_n495 x).toNat = (w_n501 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n503 x).toNat := by
  have h := u168 x
  omega
def w_n504 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n476 x).toNat + 2 * (w_n479 x).toNat + 4 * (w_n485 x).toNat + 8 * (w_n490 x).toNat + 16 * (w_n493 x).toNat + 32 * (w_n496 x).toNat)
def w_n505 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n476 x).toNat + 2 * (w_n479 x).toNat + 4 * (w_n485 x).toNat + 8 * (w_n490 x).toNat + 16 * (w_n493 x).toNat + 32 * (w_n496 x).toNat)
def w_n506 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n476 x).toNat + 2 * (w_n479 x).toNat + 4 * (w_n485 x).toNat + 8 * (w_n490 x).toNat + 16 * (w_n493 x).toNat + 32 * (w_n496 x).toNat)
theorem u169 (x : Nat → Bool) : (w_n476 x).toNat + (w_n479 x).toNat + (w_n485 x).toNat + (w_n490 x).toNat + (w_n493 x).toNat + (w_n496 x).toNat = (w_n504 x).toNat + 2 * (w_n505 x).toNat + 4 * (w_n506 x).toNat := g0 _ _ _ _ _ _ 
theorem e169 (x : Nat → Bool) : 2 * (w_n476 x).toNat + 2 * (w_n479 x).toNat + 2 * (w_n485 x).toNat + 2 * (w_n490 x).toNat + 2 * (w_n493 x).toNat + 2 * (w_n496 x).toNat = 2 * (w_n504 x).toNat + 4 * (w_n505 x).toNat + 8 * (w_n506 x).toNat := by
  have h := u169 x
  omega
def w_n507 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n477 x).toNat + 2 * (w_n487 x).toNat + 4 * (w_n491 x).toNat + 8 * (w_n494 x).toNat + 16 * (w_n497 x).toNat + 32 * (w_n500 x).toNat)
def w_n508 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n477 x).toNat + 2 * (w_n487 x).toNat + 4 * (w_n491 x).toNat + 8 * (w_n494 x).toNat + 16 * (w_n497 x).toNat + 32 * (w_n500 x).toNat)
def w_n509 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n477 x).toNat + 2 * (w_n487 x).toNat + 4 * (w_n491 x).toNat + 8 * (w_n494 x).toNat + 16 * (w_n497 x).toNat + 32 * (w_n500 x).toNat)
theorem u170 (x : Nat → Bool) : (w_n477 x).toNat + (w_n487 x).toNat + (w_n491 x).toNat + (w_n494 x).toNat + (w_n497 x).toNat + (w_n500 x).toNat = (w_n507 x).toNat + 2 * (w_n508 x).toNat + 4 * (w_n509 x).toNat := g0 _ _ _ _ _ _ 
theorem e170 (x : Nat → Bool) : 4 * (w_n477 x).toNat + 4 * (w_n487 x).toNat + 4 * (w_n491 x).toNat + 4 * (w_n494 x).toNat + 4 * (w_n497 x).toNat + 4 * (w_n500 x).toNat = 4 * (w_n507 x).toNat + 8 * (w_n508 x).toNat + 16 * (w_n509 x).toNat := by
  have h := u170 x
  omega
def w_n510 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 43).toNat + 2 * (x 44).toNat + 4 * (x 45).toNat + 8 * (x 46).toNat + 16 * (x 47).toNat + 32 * (x 48).toNat)
def w_n511 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 43).toNat + 2 * (x 44).toNat + 4 * (x 45).toNat + 8 * (x 46).toNat + 16 * (x 47).toNat + 32 * (x 48).toNat)
def w_n512 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 43).toNat + 2 * (x 44).toNat + 4 * (x 45).toNat + 8 * (x 46).toNat + 16 * (x 47).toNat + 32 * (x 48).toNat)
theorem u171 (x : Nat → Bool) : (x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat = (w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat := g0 _ _ _ _ _ _ 
theorem e171 (x : Nat → Bool) : (x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat = (w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat := by
  have h := u171 x
  omega
def w_n513 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 49).toNat + 2 * (x 50).toNat + 4 * (x 51).toNat + 8 * (x 52).toNat + 16 * (x 53).toNat + 32 * (x 54).toNat)
def w_n514 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 49).toNat + 2 * (x 50).toNat + 4 * (x 51).toNat + 8 * (x 52).toNat + 16 * (x 53).toNat + 32 * (x 54).toNat)
def w_n515 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 49).toNat + 2 * (x 50).toNat + 4 * (x 51).toNat + 8 * (x 52).toNat + 16 * (x 53).toNat + 32 * (x 54).toNat)
theorem u172 (x : Nat → Bool) : (x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat = (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat := g0 _ _ _ _ _ _ 
theorem e172 (x : Nat → Bool) : (x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat = (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat := by
  have h := u172 x
  omega
def w_n516 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 31).toNat + 2 * (x 32).toNat + 4 * (x 33).toNat + 8 * (x 34).toNat + 16 * (x 35).toNat + 32 * (x 36).toNat)
def w_n517 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 31).toNat + 2 * (x 32).toNat + 4 * (x 33).toNat + 8 * (x 34).toNat + 16 * (x 35).toNat + 32 * (x 36).toNat)
def w_n518 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 31).toNat + 2 * (x 32).toNat + 4 * (x 33).toNat + 8 * (x 34).toNat + 16 * (x 35).toNat + 32 * (x 36).toNat)
theorem u173 (x : Nat → Bool) : (x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat = (w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat := g0 _ _ _ _ _ _ 
theorem e173 (x : Nat → Bool) : (x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat = (w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat := by
  have h := u173 x
  omega
def w_n519 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 37).toNat + 2 * (x 38).toNat + 4 * (x 39).toNat + 8 * (x 40).toNat + 16 * (x 41).toNat + 32 * (x 42).toNat)
def w_n520 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 37).toNat + 2 * (x 38).toNat + 4 * (x 39).toNat + 8 * (x 40).toNat + 16 * (x 41).toNat + 32 * (x 42).toNat)
def w_n521 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 37).toNat + 2 * (x 38).toNat + 4 * (x 39).toNat + 8 * (x 40).toNat + 16 * (x 41).toNat + 32 * (x 42).toNat)
theorem u174 (x : Nat → Bool) : (x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat = (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat := g0 _ _ _ _ _ _ 
theorem e174 (x : Nat → Bool) : (x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat = (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat := by
  have h := u174 x
  omega
def w_n522 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 55).toNat + 2 * (x 56).toNat + 4 * (x 57).toNat + 8 * (x 58).toNat + 16 * (x 59).toNat + 32 * (x 60).toNat)
def w_n523 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 55).toNat + 2 * (x 56).toNat + 4 * (x 57).toNat + 8 * (x 58).toNat + 16 * (x 59).toNat + 32 * (x 60).toNat)
def w_n524 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 55).toNat + 2 * (x 56).toNat + 4 * (x 57).toNat + 8 * (x 58).toNat + 16 * (x 59).toNat + 32 * (x 60).toNat)
theorem u175 (x : Nat → Bool) : (x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat = (w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat := g0 _ _ _ _ _ _ 
theorem e175 (x : Nat → Bool) : (x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat = (w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat := by
  have h := u175 x
  omega
def w_n525 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 61).toNat + 2 * (x 62).toNat + 4 * (x 63).toNat + 8 * (x 64).toNat + 16 * (x 65).toNat + 32 * (x 66).toNat)
def w_n526 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 61).toNat + 2 * (x 62).toNat + 4 * (x 63).toNat + 8 * (x 64).toNat + 16 * (x 65).toNat + 32 * (x 66).toNat)
def w_n527 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 61).toNat + 2 * (x 62).toNat + 4 * (x 63).toNat + 8 * (x 64).toNat + 16 * (x 65).toNat + 32 * (x 66).toNat)
theorem u176 (x : Nat → Bool) : (x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat = (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat := g0 _ _ _ _ _ _ 
theorem e176 (x : Nat → Bool) : (x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat = (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat := by
  have h := u176 x
  omega
def w_n528 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 73).toNat + 2 * (x 74).toNat + 4 * (x 75).toNat + 8 * (x 76).toNat + 16 * (x 77).toNat + 32 * (x 78).toNat)
def w_n529 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 73).toNat + 2 * (x 74).toNat + 4 * (x 75).toNat + 8 * (x 76).toNat + 16 * (x 77).toNat + 32 * (x 78).toNat)
def w_n530 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 73).toNat + 2 * (x 74).toNat + 4 * (x 75).toNat + 8 * (x 76).toNat + 16 * (x 77).toNat + 32 * (x 78).toNat)
theorem u177 (x : Nat → Bool) : (x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat = (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat := g0 _ _ _ _ _ _ 
theorem e177 (x : Nat → Bool) : (x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat = (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat := by
  have h := u177 x
  omega
def w_n531 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 67).toNat + 2 * (x 68).toNat + 4 * (x 69).toNat + 8 * (x 70).toNat + 16 * (x 71).toNat + 32 * (x 72).toNat)
def w_n532 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 67).toNat + 2 * (x 68).toNat + 4 * (x 69).toNat + 8 * (x 70).toNat + 16 * (x 71).toNat + 32 * (x 72).toNat)
def w_n533 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 67).toNat + 2 * (x 68).toNat + 4 * (x 69).toNat + 8 * (x 70).toNat + 16 * (x 71).toNat + 32 * (x 72).toNat)
theorem u178 (x : Nat → Bool) : (x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat = (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat := g0 _ _ _ _ _ _ 
theorem e178 (x : Nat → Bool) : (x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat = (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat := by
  have h := u178 x
  omega
def w_n534 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n510 x).toNat + 2 * (w_n513 x).toNat + 4 * (w_n516 x).toNat + 8 * (w_n519 x).toNat + 16 * (w_n522 x).toNat + 32 * (w_n525 x).toNat)
def w_n535 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n510 x).toNat + 2 * (w_n513 x).toNat + 4 * (w_n516 x).toNat + 8 * (w_n519 x).toNat + 16 * (w_n522 x).toNat + 32 * (w_n525 x).toNat)
def w_n536 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n510 x).toNat + 2 * (w_n513 x).toNat + 4 * (w_n516 x).toNat + 8 * (w_n519 x).toNat + 16 * (w_n522 x).toNat + 32 * (w_n525 x).toNat)
theorem u179 (x : Nat → Bool) : (w_n510 x).toNat + (w_n513 x).toNat + (w_n516 x).toNat + (w_n519 x).toNat + (w_n522 x).toNat + (w_n525 x).toNat = (w_n534 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n536 x).toNat := g0 _ _ _ _ _ _ 
theorem e179 (x : Nat → Bool) : (w_n510 x).toNat + (w_n513 x).toNat + (w_n516 x).toNat + (w_n519 x).toNat + (w_n522 x).toNat + (w_n525 x).toNat = (w_n534 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n536 x).toNat := by
  have h := u179 x
  omega
def w_n537 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n511 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n517 x).toNat + 8 * (w_n520 x).toNat + 16 * (w_n523 x).toNat + 32 * (w_n526 x).toNat)
def w_n538 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n511 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n517 x).toNat + 8 * (w_n520 x).toNat + 16 * (w_n523 x).toNat + 32 * (w_n526 x).toNat)
def w_n539 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n511 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n517 x).toNat + 8 * (w_n520 x).toNat + 16 * (w_n523 x).toNat + 32 * (w_n526 x).toNat)
theorem u180 (x : Nat → Bool) : (w_n511 x).toNat + (w_n514 x).toNat + (w_n517 x).toNat + (w_n520 x).toNat + (w_n523 x).toNat + (w_n526 x).toNat = (w_n537 x).toNat + 2 * (w_n538 x).toNat + 4 * (w_n539 x).toNat := g0 _ _ _ _ _ _ 
theorem e180 (x : Nat → Bool) : 2 * (w_n511 x).toNat + 2 * (w_n514 x).toNat + 2 * (w_n517 x).toNat + 2 * (w_n520 x).toNat + 2 * (w_n523 x).toNat + 2 * (w_n526 x).toNat = 2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 8 * (w_n539 x).toNat := by
  have h := u180 x
  omega
def w_n540 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n512 x).toNat + 2 * (w_n515 x).toNat + 4 * (w_n518 x).toNat + 8 * (w_n521 x).toNat + 16 * (w_n524 x).toNat + 32 * (w_n527 x).toNat)
def w_n541 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n512 x).toNat + 2 * (w_n515 x).toNat + 4 * (w_n518 x).toNat + 8 * (w_n521 x).toNat + 16 * (w_n524 x).toNat + 32 * (w_n527 x).toNat)
def w_n542 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n512 x).toNat + 2 * (w_n515 x).toNat + 4 * (w_n518 x).toNat + 8 * (w_n521 x).toNat + 16 * (w_n524 x).toNat + 32 * (w_n527 x).toNat)
theorem u181 (x : Nat → Bool) : (w_n512 x).toNat + (w_n515 x).toNat + (w_n518 x).toNat + (w_n521 x).toNat + (w_n524 x).toNat + (w_n527 x).toNat = (w_n540 x).toNat + 2 * (w_n541 x).toNat + 4 * (w_n542 x).toNat := g0 _ _ _ _ _ _ 
theorem e181 (x : Nat → Bool) : 4 * (w_n512 x).toNat + 4 * (w_n515 x).toNat + 4 * (w_n518 x).toNat + 4 * (w_n521 x).toNat + 4 * (w_n524 x).toNat + 4 * (w_n527 x).toNat = 4 * (w_n540 x).toNat + 8 * (w_n541 x).toNat + 16 * (w_n542 x).toNat := by
  have h := u181 x
  omega
def w_n543 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n499 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n504 x).toNat + 8 * (w_n529 x).toNat + 16 * (w_n532 x).toNat + 32 * (w_n535 x).toNat)
def w_n544 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n499 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n504 x).toNat + 8 * (w_n529 x).toNat + 16 * (w_n532 x).toNat + 32 * (w_n535 x).toNat)
def w_n545 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n499 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n504 x).toNat + 8 * (w_n529 x).toNat + 16 * (w_n532 x).toNat + 32 * (w_n535 x).toNat)
theorem u182 (x : Nat → Bool) : (w_n499 x).toNat + (w_n502 x).toNat + (w_n504 x).toNat + (w_n529 x).toNat + (w_n532 x).toNat + (w_n535 x).toNat = (w_n543 x).toNat + 2 * (w_n544 x).toNat + 4 * (w_n545 x).toNat := g0 _ _ _ _ _ _ 
theorem e182 (x : Nat → Bool) : 2 * (w_n499 x).toNat + 2 * (w_n502 x).toNat + 2 * (w_n504 x).toNat + 2 * (w_n529 x).toNat + 2 * (w_n532 x).toNat + 2 * (w_n535 x).toNat = 2 * (w_n543 x).toNat + 4 * (w_n544 x).toNat + 8 * (w_n545 x).toNat := by
  have h := u182 x
  omega
def w_n546 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n503 x).toNat + 2 * (w_n505 x).toNat + 4 * (w_n507 x).toNat + 8 * (w_n530 x).toNat + 16 * (w_n533 x).toNat + 32 * (w_n536 x).toNat)
def w_n547 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n503 x).toNat + 2 * (w_n505 x).toNat + 4 * (w_n507 x).toNat + 8 * (w_n530 x).toNat + 16 * (w_n533 x).toNat + 32 * (w_n536 x).toNat)
def w_n548 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n503 x).toNat + 2 * (w_n505 x).toNat + 4 * (w_n507 x).toNat + 8 * (w_n530 x).toNat + 16 * (w_n533 x).toNat + 32 * (w_n536 x).toNat)
theorem u183 (x : Nat → Bool) : (w_n503 x).toNat + (w_n505 x).toNat + (w_n507 x).toNat + (w_n530 x).toNat + (w_n533 x).toNat + (w_n536 x).toNat = (w_n546 x).toNat + 2 * (w_n547 x).toNat + 4 * (w_n548 x).toNat := g0 _ _ _ _ _ _ 
theorem e183 (x : Nat → Bool) : 4 * (w_n503 x).toNat + 4 * (w_n505 x).toNat + 4 * (w_n507 x).toNat + 4 * (w_n530 x).toNat + 4 * (w_n533 x).toNat + 4 * (w_n536 x).toNat = 4 * (w_n546 x).toNat + 8 * (w_n547 x).toNat + 16 * (w_n548 x).toNat := by
  have h := u183 x
  omega
def w_n549 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n488 x).toNat + 2 * (w_n506 x).toNat + 4 * (w_n508 x).toNat + 8 * (w_n539 x).toNat + 16 * (w_n541 x).toNat + 32 * (w_n545 x).toNat)
def w_n550 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n488 x).toNat + 2 * (w_n506 x).toNat + 4 * (w_n508 x).toNat + 8 * (w_n539 x).toNat + 16 * (w_n541 x).toNat + 32 * (w_n545 x).toNat)
def w_n551 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n488 x).toNat + 2 * (w_n506 x).toNat + 4 * (w_n508 x).toNat + 8 * (w_n539 x).toNat + 16 * (w_n541 x).toNat + 32 * (w_n545 x).toNat)
theorem u184 (x : Nat → Bool) : (w_n488 x).toNat + (w_n506 x).toNat + (w_n508 x).toNat + (w_n539 x).toNat + (w_n541 x).toNat + (w_n545 x).toNat = (w_n549 x).toNat + 2 * (w_n550 x).toNat + 4 * (w_n551 x).toNat := g0 _ _ _ _ _ _ 
theorem e184 (x : Nat → Bool) : 8 * (w_n488 x).toNat + 8 * (w_n506 x).toNat + 8 * (w_n508 x).toNat + 8 * (w_n539 x).toNat + 8 * (w_n541 x).toNat + 8 * (w_n545 x).toNat = 8 * (w_n549 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n551 x).toNat := by
  have h := u184 x
  omega
def w_n552 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n460 x).toNat + 2 * (w_n463 x).toNat + 4 * (w_n466 x).toNat + 8 * (w_n498 x).toNat + 16 * (w_n501 x).toNat + 32 * (w_n528 x).toNat)
def w_n553 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n460 x).toNat + 2 * (w_n463 x).toNat + 4 * (w_n466 x).toNat + 8 * (w_n498 x).toNat + 16 * (w_n501 x).toNat + 32 * (w_n528 x).toNat)
def w_n554 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n460 x).toNat + 2 * (w_n463 x).toNat + 4 * (w_n466 x).toNat + 8 * (w_n498 x).toNat + 16 * (w_n501 x).toNat + 32 * (w_n528 x).toNat)
theorem u185 (x : Nat → Bool) : (w_n460 x).toNat + (w_n463 x).toNat + (w_n466 x).toNat + (w_n498 x).toNat + (w_n501 x).toNat + (w_n528 x).toNat = (w_n552 x).toNat + 2 * (w_n553 x).toNat + 4 * (w_n554 x).toNat := g0 _ _ _ _ _ _ 
theorem e185 (x : Nat → Bool) : (w_n460 x).toNat + (w_n463 x).toNat + (w_n466 x).toNat + (w_n498 x).toNat + (w_n501 x).toNat + (w_n528 x).toNat = (w_n552 x).toNat + 2 * (w_n553 x).toNat + 4 * (w_n554 x).toNat := by
  have h := u185 x
  omega
def w_n555 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n461 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n467 x).toNat + 8 * (w_n469 x).toNat + 16 * (w_n537 x).toNat + 32 * (w_n543 x).toNat)
def w_n556 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n461 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n467 x).toNat + 8 * (w_n469 x).toNat + 16 * (w_n537 x).toNat + 32 * (w_n543 x).toNat)
def w_n557 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n461 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n467 x).toNat + 8 * (w_n469 x).toNat + 16 * (w_n537 x).toNat + 32 * (w_n543 x).toNat)
theorem u186 (x : Nat → Bool) : (w_n461 x).toNat + (w_n464 x).toNat + (w_n467 x).toNat + (w_n469 x).toNat + (w_n537 x).toNat + (w_n543 x).toNat = (w_n555 x).toNat + 2 * (w_n556 x).toNat + 4 * (w_n557 x).toNat := g0 _ _ _ _ _ _ 
theorem e186 (x : Nat → Bool) : 2 * (w_n461 x).toNat + 2 * (w_n464 x).toNat + 2 * (w_n467 x).toNat + 2 * (w_n469 x).toNat + 2 * (w_n537 x).toNat + 2 * (w_n543 x).toNat = 2 * (w_n555 x).toNat + 4 * (w_n556 x).toNat + 8 * (w_n557 x).toNat := by
  have h := u186 x
  omega
def w_n558 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n462 x).toNat + 2 * (w_n465 x).toNat + 4 * (w_n468 x).toNat + 8 * (w_n470 x).toNat + 16 * (w_n472 x).toNat + 32 * (w_n538 x).toNat)
def w_n559 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n462 x).toNat + 2 * (w_n465 x).toNat + 4 * (w_n468 x).toNat + 8 * (w_n470 x).toNat + 16 * (w_n472 x).toNat + 32 * (w_n538 x).toNat)
def w_n560 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n462 x).toNat + 2 * (w_n465 x).toNat + 4 * (w_n468 x).toNat + 8 * (w_n470 x).toNat + 16 * (w_n472 x).toNat + 32 * (w_n538 x).toNat)
theorem u187 (x : Nat → Bool) : (w_n462 x).toNat + (w_n465 x).toNat + (w_n468 x).toNat + (w_n470 x).toNat + (w_n472 x).toNat + (w_n538 x).toNat = (w_n558 x).toNat + 2 * (w_n559 x).toNat + 4 * (w_n560 x).toNat := g0 _ _ _ _ _ _ 
theorem e187 (x : Nat → Bool) : 4 * (w_n462 x).toNat + 4 * (w_n465 x).toNat + 4 * (w_n468 x).toNat + 4 * (w_n470 x).toNat + 4 * (w_n472 x).toNat + 4 * (w_n538 x).toNat = 4 * (w_n558 x).toNat + 8 * (w_n559 x).toNat + 16 * (w_n560 x).toNat := by
  have h := u187 x
  omega
def w_n561 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n540 x).toNat + 2 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 8 * (w_n554 x).toNat + 16 * (w_n556 x).toNat + 32 * (w_n558 x).toNat)
def w_n562 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n540 x).toNat + 2 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 8 * (w_n554 x).toNat + 16 * (w_n556 x).toNat + 32 * (w_n558 x).toNat)
def w_n563 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n540 x).toNat + 2 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 8 * (w_n554 x).toNat + 16 * (w_n556 x).toNat + 32 * (w_n558 x).toNat)
theorem u188 (x : Nat → Bool) : (w_n540 x).toNat + (w_n544 x).toNat + (w_n546 x).toNat + (w_n554 x).toNat + (w_n556 x).toNat + (w_n558 x).toNat = (w_n561 x).toNat + 2 * (w_n562 x).toNat + 4 * (w_n563 x).toNat := g0 _ _ _ _ _ _ 
theorem e188 (x : Nat → Bool) : 4 * (w_n540 x).toNat + 4 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 4 * (w_n554 x).toNat + 4 * (w_n556 x).toNat + 4 * (w_n558 x).toNat = 4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 16 * (w_n563 x).toNat := by
  have h := u188 x
  omega
def w_n564 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n471 x).toNat + 2 * (w_n473 x).toNat + 4 * (w_n547 x).toNat + 8 * (w_n549 x).toNat + 16 * (w_n557 x).toNat + 32 * (w_n559 x).toNat)
def w_n565 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n471 x).toNat + 2 * (w_n473 x).toNat + 4 * (w_n547 x).toNat + 8 * (w_n549 x).toNat + 16 * (w_n557 x).toNat + 32 * (w_n559 x).toNat)
def w_n566 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n471 x).toNat + 2 * (w_n473 x).toNat + 4 * (w_n547 x).toNat + 8 * (w_n549 x).toNat + 16 * (w_n557 x).toNat + 32 * (w_n559 x).toNat)
theorem u189 (x : Nat → Bool) : (w_n471 x).toNat + (w_n473 x).toNat + (w_n547 x).toNat + (w_n549 x).toNat + (w_n557 x).toNat + (w_n559 x).toNat = (w_n564 x).toNat + 2 * (w_n565 x).toNat + 4 * (w_n566 x).toNat := g0 _ _ _ _ _ _ 
theorem e189 (x : Nat → Bool) : 8 * (w_n471 x).toNat + 8 * (w_n473 x).toNat + 8 * (w_n547 x).toNat + 8 * (w_n549 x).toNat + 8 * (w_n557 x).toNat + 8 * (w_n559 x).toNat = 8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat := by
  have h := u189 x
  omega
def w_n567 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n474 x).toNat + 2 * (w_n509 x).toNat + 4 * (w_n542 x).toNat + 8 * (w_n548 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n560 x).toNat)
def w_n568 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n474 x).toNat + 2 * (w_n509 x).toNat + 4 * (w_n542 x).toNat + 8 * (w_n548 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n560 x).toNat)
def w_n569 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n474 x).toNat + 2 * (w_n509 x).toNat + 4 * (w_n542 x).toNat + 8 * (w_n548 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n560 x).toNat)
theorem u190 (x : Nat → Bool) : (w_n474 x).toNat + (w_n509 x).toNat + (w_n542 x).toNat + (w_n548 x).toNat + (w_n550 x).toNat + (w_n560 x).toNat = (w_n567 x).toNat + 2 * (w_n568 x).toNat + 4 * (w_n569 x).toNat := g0 _ _ _ _ _ _ 
theorem e190 (x : Nat → Bool) : 16 * (w_n474 x).toNat + 16 * (w_n509 x).toNat + 16 * (w_n542 x).toNat + 16 * (w_n548 x).toNat + 16 * (w_n550 x).toNat + 16 * (w_n560 x).toNat = 16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat := by
  have h := u190 x
  omega
def w_n570 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n419 x).toNat + 2 * (w_n421 x).toNat + 4 * (w_n428 x).toNat + 8 * (w_n430 x).toNat + 16 * (w_n553 x).toNat + 32 * (w_n555 x).toNat)
def w_n571 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n419 x).toNat + 2 * (w_n421 x).toNat + 4 * (w_n428 x).toNat + 8 * (w_n430 x).toNat + 16 * (w_n553 x).toNat + 32 * (w_n555 x).toNat)
def w_n572 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n419 x).toNat + 2 * (w_n421 x).toNat + 4 * (w_n428 x).toNat + 8 * (w_n430 x).toNat + 16 * (w_n553 x).toNat + 32 * (w_n555 x).toNat)
theorem u191 (x : Nat → Bool) : (w_n419 x).toNat + (w_n421 x).toNat + (w_n428 x).toNat + (w_n430 x).toNat + (w_n553 x).toNat + (w_n555 x).toNat = (w_n570 x).toNat + 2 * (w_n571 x).toNat + 4 * (w_n572 x).toNat := g0 _ _ _ _ _ _ 
theorem e191 (x : Nat → Bool) : 2 * (w_n419 x).toNat + 2 * (w_n421 x).toNat + 2 * (w_n428 x).toNat + 2 * (w_n430 x).toNat + 2 * (w_n553 x).toNat + 2 * (w_n555 x).toNat = 2 * (w_n570 x).toNat + 4 * (w_n571 x).toNat + 8 * (w_n572 x).toNat := by
  have h := u191 x
  omega
def w_n573 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n393 x).toNat + 2 * (w_n426 x).toNat + 4 * (w_n435 x).toNat + 8 * (w_n438 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n563 x).toNat)
def w_n574 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n393 x).toNat + 2 * (w_n426 x).toNat + 4 * (w_n435 x).toNat + 8 * (w_n438 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n563 x).toNat)
def w_n575 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n393 x).toNat + 2 * (w_n426 x).toNat + 4 * (w_n435 x).toNat + 8 * (w_n438 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n563 x).toNat)
theorem u192 (x : Nat → Bool) : (w_n393 x).toNat + (w_n426 x).toNat + (w_n435 x).toNat + (w_n438 x).toNat + (w_n440 x).toNat + (w_n563 x).toNat = (w_n573 x).toNat + 2 * (w_n574 x).toNat + 4 * (w_n575 x).toNat := g0 _ _ _ _ _ _ 
theorem e192 (x : Nat → Bool) : 16 * (w_n393 x).toNat + 16 * (w_n426 x).toNat + 16 * (w_n435 x).toNat + 16 * (w_n438 x).toNat + 16 * (w_n440 x).toNat + 16 * (w_n563 x).toNat = 16 * (w_n573 x).toNat + 32 * (w_n574 x).toNat + 64 * (w_n575 x).toNat := by
  have h := u192 x
  omega
def w_n576 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 145).toNat + 2 * (x 146).toNat + 4 * (x 147).toNat + 8 * (x 148).toNat + 16 * (x 149).toNat + 32 * (x 150).toNat)
def w_n577 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 145).toNat + 2 * (x 146).toNat + 4 * (x 147).toNat + 8 * (x 148).toNat + 16 * (x 149).toNat + 32 * (x 150).toNat)
def w_n578 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 145).toNat + 2 * (x 146).toNat + 4 * (x 147).toNat + 8 * (x 148).toNat + 16 * (x 149).toNat + 32 * (x 150).toNat)
theorem u193 (x : Nat → Bool) : (x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat = (w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat := g0 _ _ _ _ _ _ 
theorem e193 (x : Nat → Bool) : (x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat = (w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat := by
  have h := u193 x
  omega
def w_n579 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 139).toNat + 2 * (x 140).toNat + 4 * (x 141).toNat + 8 * (x 142).toNat + 16 * (x 143).toNat + 32 * (x 144).toNat)
def w_n580 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 139).toNat + 2 * (x 140).toNat + 4 * (x 141).toNat + 8 * (x 142).toNat + 16 * (x 143).toNat + 32 * (x 144).toNat)
def w_n581 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 139).toNat + 2 * (x 140).toNat + 4 * (x 141).toNat + 8 * (x 142).toNat + 16 * (x 143).toNat + 32 * (x 144).toNat)
theorem u194 (x : Nat → Bool) : (x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat = (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat := g0 _ _ _ _ _ _ 
theorem e194 (x : Nat → Bool) : (x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat = (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat := by
  have h := u194 x
  omega
def w_n582 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 127).toNat + 2 * (x 128).toNat + 4 * (x 129).toNat + 8 * (x 130).toNat + 16 * (x 131).toNat + 32 * (x 132).toNat)
def w_n583 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 127).toNat + 2 * (x 128).toNat + 4 * (x 129).toNat + 8 * (x 130).toNat + 16 * (x 131).toNat + 32 * (x 132).toNat)
def w_n584 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 127).toNat + 2 * (x 128).toNat + 4 * (x 129).toNat + 8 * (x 130).toNat + 16 * (x 131).toNat + 32 * (x 132).toNat)
theorem u195 (x : Nat → Bool) : (x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat = (w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat := g0 _ _ _ _ _ _ 
theorem e195 (x : Nat → Bool) : (x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat = (w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat := by
  have h := u195 x
  omega
def w_n585 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 133).toNat + 2 * (x 134).toNat + 4 * (x 135).toNat + 8 * (x 136).toNat + 16 * (x 137).toNat + 32 * (x 138).toNat)
def w_n586 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 133).toNat + 2 * (x 134).toNat + 4 * (x 135).toNat + 8 * (x 136).toNat + 16 * (x 137).toNat + 32 * (x 138).toNat)
def w_n587 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 133).toNat + 2 * (x 134).toNat + 4 * (x 135).toNat + 8 * (x 136).toNat + 16 * (x 137).toNat + 32 * (x 138).toNat)
theorem u196 (x : Nat → Bool) : (x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat = (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat := g0 _ _ _ _ _ _ 
theorem e196 (x : Nat → Bool) : (x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat = (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat := by
  have h := u196 x
  omega
def w_n588 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 169).toNat + 2 * (x 170).toNat + 4 * (x 171).toNat + 8 * (x 172).toNat + 16 * (x 173).toNat + 32 * (x 174).toNat)
def w_n589 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 169).toNat + 2 * (x 170).toNat + 4 * (x 171).toNat + 8 * (x 172).toNat + 16 * (x 173).toNat + 32 * (x 174).toNat)
def w_n590 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 169).toNat + 2 * (x 170).toNat + 4 * (x 171).toNat + 8 * (x 172).toNat + 16 * (x 173).toNat + 32 * (x 174).toNat)
theorem u197 (x : Nat → Bool) : (x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat = (w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat := g0 _ _ _ _ _ _ 
theorem e197 (x : Nat → Bool) : (x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat = (w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat := by
  have h := u197 x
  omega
def w_n591 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 163).toNat + 2 * (x 164).toNat + 4 * (x 165).toNat + 8 * (x 166).toNat + 16 * (x 167).toNat + 32 * (x 168).toNat)
def w_n592 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 163).toNat + 2 * (x 164).toNat + 4 * (x 165).toNat + 8 * (x 166).toNat + 16 * (x 167).toNat + 32 * (x 168).toNat)
def w_n593 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 163).toNat + 2 * (x 164).toNat + 4 * (x 165).toNat + 8 * (x 166).toNat + 16 * (x 167).toNat + 32 * (x 168).toNat)
theorem u198 (x : Nat → Bool) : (x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat = (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat := g0 _ _ _ _ _ _ 
theorem e198 (x : Nat → Bool) : (x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat = (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat := by
  have h := u198 x
  omega
def w_n594 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 151).toNat + 2 * (x 152).toNat + 4 * (x 153).toNat + 8 * (x 154).toNat + 16 * (x 155).toNat + 32 * (x 156).toNat)
def w_n595 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 151).toNat + 2 * (x 152).toNat + 4 * (x 153).toNat + 8 * (x 154).toNat + 16 * (x 155).toNat + 32 * (x 156).toNat)
def w_n596 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 151).toNat + 2 * (x 152).toNat + 4 * (x 153).toNat + 8 * (x 154).toNat + 16 * (x 155).toNat + 32 * (x 156).toNat)
theorem u199 (x : Nat → Bool) : (x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat = (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat := g0 _ _ _ _ _ _ 
theorem e199 (x : Nat → Bool) : (x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat = (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat := by
  have h := u199 x
  omega
def w_n597 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 157).toNat + 2 * (x 158).toNat + 4 * (x 159).toNat + 8 * (x 160).toNat + 16 * (x 161).toNat + 32 * (x 162).toNat)
def w_n598 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 157).toNat + 2 * (x 158).toNat + 4 * (x 159).toNat + 8 * (x 160).toNat + 16 * (x 161).toNat + 32 * (x 162).toNat)
def w_n599 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 157).toNat + 2 * (x 158).toNat + 4 * (x 159).toNat + 8 * (x 160).toNat + 16 * (x 161).toNat + 32 * (x 162).toNat)
theorem u200 (x : Nat → Bool) : (x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat = (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat := g0 _ _ _ _ _ _ 
theorem e200 (x : Nat → Bool) : (x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat = (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat := by
  have h := u200 x
  omega
def w_n600 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n576 x).toNat + 2 * (w_n579 x).toNat + 4 * (w_n582 x).toNat + 8 * (w_n585 x).toNat + 16 * (w_n588 x).toNat + 32 * (w_n591 x).toNat)
def w_n601 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n576 x).toNat + 2 * (w_n579 x).toNat + 4 * (w_n582 x).toNat + 8 * (w_n585 x).toNat + 16 * (w_n588 x).toNat + 32 * (w_n591 x).toNat)
def w_n602 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n576 x).toNat + 2 * (w_n579 x).toNat + 4 * (w_n582 x).toNat + 8 * (w_n585 x).toNat + 16 * (w_n588 x).toNat + 32 * (w_n591 x).toNat)
theorem u201 (x : Nat → Bool) : (w_n576 x).toNat + (w_n579 x).toNat + (w_n582 x).toNat + (w_n585 x).toNat + (w_n588 x).toNat + (w_n591 x).toNat = (w_n600 x).toNat + 2 * (w_n601 x).toNat + 4 * (w_n602 x).toNat := g0 _ _ _ _ _ _ 
theorem e201 (x : Nat → Bool) : (w_n576 x).toNat + (w_n579 x).toNat + (w_n582 x).toNat + (w_n585 x).toNat + (w_n588 x).toNat + (w_n591 x).toNat = (w_n600 x).toNat + 2 * (w_n601 x).toNat + 4 * (w_n602 x).toNat := by
  have h := u201 x
  omega
def w_n603 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n577 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n583 x).toNat + 8 * (w_n586 x).toNat + 16 * (w_n589 x).toNat + 32 * (w_n592 x).toNat)
def w_n604 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n577 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n583 x).toNat + 8 * (w_n586 x).toNat + 16 * (w_n589 x).toNat + 32 * (w_n592 x).toNat)
def w_n605 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n577 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n583 x).toNat + 8 * (w_n586 x).toNat + 16 * (w_n589 x).toNat + 32 * (w_n592 x).toNat)
theorem u202 (x : Nat → Bool) : (w_n577 x).toNat + (w_n580 x).toNat + (w_n583 x).toNat + (w_n586 x).toNat + (w_n589 x).toNat + (w_n592 x).toNat = (w_n603 x).toNat + 2 * (w_n604 x).toNat + 4 * (w_n605 x).toNat := g0 _ _ _ _ _ _ 
theorem e202 (x : Nat → Bool) : 2 * (w_n577 x).toNat + 2 * (w_n580 x).toNat + 2 * (w_n583 x).toNat + 2 * (w_n586 x).toNat + 2 * (w_n589 x).toNat + 2 * (w_n592 x).toNat = 2 * (w_n603 x).toNat + 4 * (w_n604 x).toNat + 8 * (w_n605 x).toNat := by
  have h := u202 x
  omega
def w_n606 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n578 x).toNat + 2 * (w_n581 x).toNat + 4 * (w_n584 x).toNat + 8 * (w_n587 x).toNat + 16 * (w_n590 x).toNat + 32 * (w_n593 x).toNat)
def w_n607 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n578 x).toNat + 2 * (w_n581 x).toNat + 4 * (w_n584 x).toNat + 8 * (w_n587 x).toNat + 16 * (w_n590 x).toNat + 32 * (w_n593 x).toNat)
def w_n608 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n578 x).toNat + 2 * (w_n581 x).toNat + 4 * (w_n584 x).toNat + 8 * (w_n587 x).toNat + 16 * (w_n590 x).toNat + 32 * (w_n593 x).toNat)
theorem u203 (x : Nat → Bool) : (w_n578 x).toNat + (w_n581 x).toNat + (w_n584 x).toNat + (w_n587 x).toNat + (w_n590 x).toNat + (w_n593 x).toNat = (w_n606 x).toNat + 2 * (w_n607 x).toNat + 4 * (w_n608 x).toNat := g0 _ _ _ _ _ _ 
theorem e203 (x : Nat → Bool) : 4 * (w_n578 x).toNat + 4 * (w_n581 x).toNat + 4 * (w_n584 x).toNat + 4 * (w_n587 x).toNat + 4 * (w_n590 x).toNat + 4 * (w_n593 x).toNat = 4 * (w_n606 x).toNat + 8 * (w_n607 x).toNat + 16 * (w_n608 x).toNat := by
  have h := u203 x
  omega
def w_n609 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 121).toNat + 2 * (x 122).toNat + 4 * (x 123).toNat + 8 * (x 124).toNat + 16 * (x 125).toNat + 32 * (x 126).toNat)
def w_n610 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 121).toNat + 2 * (x 122).toNat + 4 * (x 123).toNat + 8 * (x 124).toNat + 16 * (x 125).toNat + 32 * (x 126).toNat)
def w_n611 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 121).toNat + 2 * (x 122).toNat + 4 * (x 123).toNat + 8 * (x 124).toNat + 16 * (x 125).toNat + 32 * (x 126).toNat)
theorem u204 (x : Nat → Bool) : (x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat = (w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat := g0 _ _ _ _ _ _ 
theorem e204 (x : Nat → Bool) : (x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat = (w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat := by
  have h := u204 x
  omega
def w_n612 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 115).toNat + 2 * (x 116).toNat + 4 * (x 117).toNat + 8 * (x 118).toNat + 16 * (x 119).toNat + 32 * (x 120).toNat)
def w_n613 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 115).toNat + 2 * (x 116).toNat + 4 * (x 117).toNat + 8 * (x 118).toNat + 16 * (x 119).toNat + 32 * (x 120).toNat)
def w_n614 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 115).toNat + 2 * (x 116).toNat + 4 * (x 117).toNat + 8 * (x 118).toNat + 16 * (x 119).toNat + 32 * (x 120).toNat)
theorem u205 (x : Nat → Bool) : (x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat = (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat := g0 _ _ _ _ _ _ 
theorem e205 (x : Nat → Bool) : (x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat = (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat := by
  have h := u205 x
  omega
def w_n615 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 103).toNat + 2 * (x 104).toNat + 4 * (x 105).toNat + 8 * (x 106).toNat + 16 * (x 107).toNat + 32 * (x 108).toNat)
def w_n616 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 103).toNat + 2 * (x 104).toNat + 4 * (x 105).toNat + 8 * (x 106).toNat + 16 * (x 107).toNat + 32 * (x 108).toNat)
def w_n617 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 103).toNat + 2 * (x 104).toNat + 4 * (x 105).toNat + 8 * (x 106).toNat + 16 * (x 107).toNat + 32 * (x 108).toNat)
theorem u206 (x : Nat → Bool) : (x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat = (w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat := g0 _ _ _ _ _ _ 
theorem e206 (x : Nat → Bool) : (x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat = (w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat := by
  have h := u206 x
  omega
def w_n618 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 109).toNat + 2 * (x 110).toNat + 4 * (x 111).toNat + 8 * (x 112).toNat + 16 * (x 113).toNat + 32 * (x 114).toNat)
def w_n619 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 109).toNat + 2 * (x 110).toNat + 4 * (x 111).toNat + 8 * (x 112).toNat + 16 * (x 113).toNat + 32 * (x 114).toNat)
def w_n620 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 109).toNat + 2 * (x 110).toNat + 4 * (x 111).toNat + 8 * (x 112).toNat + 16 * (x 113).toNat + 32 * (x 114).toNat)
theorem u207 (x : Nat → Bool) : (x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat = (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat := g0 _ _ _ _ _ _ 
theorem e207 (x : Nat → Bool) : (x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat = (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat := by
  have h := u207 x
  omega
def w_n621 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 79).toNat + 2 * (x 80).toNat + 4 * (x 81).toNat + 8 * (x 82).toNat + 16 * (x 83).toNat + 32 * (x 84).toNat)
def w_n622 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 79).toNat + 2 * (x 80).toNat + 4 * (x 81).toNat + 8 * (x 82).toNat + 16 * (x 83).toNat + 32 * (x 84).toNat)
def w_n623 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 79).toNat + 2 * (x 80).toNat + 4 * (x 81).toNat + 8 * (x 82).toNat + 16 * (x 83).toNat + 32 * (x 84).toNat)
theorem u208 (x : Nat → Bool) : (x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat = (w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat := g0 _ _ _ _ _ _ 
theorem e208 (x : Nat → Bool) : (x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat = (w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat := by
  have h := u208 x
  omega
def w_n624 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 85).toNat + 2 * (x 86).toNat + 4 * (x 87).toNat + 8 * (x 88).toNat + 16 * (x 89).toNat + 32 * (x 90).toNat)
def w_n625 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 85).toNat + 2 * (x 86).toNat + 4 * (x 87).toNat + 8 * (x 88).toNat + 16 * (x 89).toNat + 32 * (x 90).toNat)
def w_n626 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 85).toNat + 2 * (x 86).toNat + 4 * (x 87).toNat + 8 * (x 88).toNat + 16 * (x 89).toNat + 32 * (x 90).toNat)
theorem u209 (x : Nat → Bool) : (x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat = (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat := g0 _ _ _ _ _ _ 
theorem e209 (x : Nat → Bool) : (x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat = (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat := by
  have h := u209 x
  omega
def w_n627 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 91).toNat + 2 * (x 92).toNat + 4 * (x 93).toNat + 8 * (x 94).toNat + 16 * (x 95).toNat + 32 * (x 96).toNat)
def w_n628 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 91).toNat + 2 * (x 92).toNat + 4 * (x 93).toNat + 8 * (x 94).toNat + 16 * (x 95).toNat + 32 * (x 96).toNat)
def w_n629 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 91).toNat + 2 * (x 92).toNat + 4 * (x 93).toNat + 8 * (x 94).toNat + 16 * (x 95).toNat + 32 * (x 96).toNat)
theorem u210 (x : Nat → Bool) : (x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat = (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat := g0 _ _ _ _ _ _ 
theorem e210 (x : Nat → Bool) : (x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat = (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat := by
  have h := u210 x
  omega
def w_n630 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 97).toNat + 2 * (x 98).toNat + 4 * (x 99).toNat + 8 * (x 100).toNat + 16 * (x 101).toNat + 32 * (x 102).toNat)
def w_n631 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 97).toNat + 2 * (x 98).toNat + 4 * (x 99).toNat + 8 * (x 100).toNat + 16 * (x 101).toNat + 32 * (x 102).toNat)
def w_n632 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 97).toNat + 2 * (x 98).toNat + 4 * (x 99).toNat + 8 * (x 100).toNat + 16 * (x 101).toNat + 32 * (x 102).toNat)
theorem u211 (x : Nat → Bool) : (x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat = (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat := g0 _ _ _ _ _ _ 
theorem e211 (x : Nat → Bool) : (x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat = (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat := by
  have h := u211 x
  omega
def w_n633 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n609 x).toNat + 2 * (w_n612 x).toNat + 4 * (w_n615 x).toNat + 8 * (w_n618 x).toNat + 16 * (w_n621 x).toNat + 32 * (w_n624 x).toNat)
def w_n634 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n609 x).toNat + 2 * (w_n612 x).toNat + 4 * (w_n615 x).toNat + 8 * (w_n618 x).toNat + 16 * (w_n621 x).toNat + 32 * (w_n624 x).toNat)
def w_n635 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n609 x).toNat + 2 * (w_n612 x).toNat + 4 * (w_n615 x).toNat + 8 * (w_n618 x).toNat + 16 * (w_n621 x).toNat + 32 * (w_n624 x).toNat)
theorem u212 (x : Nat → Bool) : (w_n609 x).toNat + (w_n612 x).toNat + (w_n615 x).toNat + (w_n618 x).toNat + (w_n621 x).toNat + (w_n624 x).toNat = (w_n633 x).toNat + 2 * (w_n634 x).toNat + 4 * (w_n635 x).toNat := g0 _ _ _ _ _ _ 
theorem e212 (x : Nat → Bool) : (w_n609 x).toNat + (w_n612 x).toNat + (w_n615 x).toNat + (w_n618 x).toNat + (w_n621 x).toNat + (w_n624 x).toNat = (w_n633 x).toNat + 2 * (w_n634 x).toNat + 4 * (w_n635 x).toNat := by
  have h := u212 x
  omega
def w_n636 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n610 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n616 x).toNat + 8 * (w_n619 x).toNat + 16 * (w_n622 x).toNat + 32 * (w_n625 x).toNat)
def w_n637 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n610 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n616 x).toNat + 8 * (w_n619 x).toNat + 16 * (w_n622 x).toNat + 32 * (w_n625 x).toNat)
def w_n638 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n610 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n616 x).toNat + 8 * (w_n619 x).toNat + 16 * (w_n622 x).toNat + 32 * (w_n625 x).toNat)
theorem u213 (x : Nat → Bool) : (w_n610 x).toNat + (w_n613 x).toNat + (w_n616 x).toNat + (w_n619 x).toNat + (w_n622 x).toNat + (w_n625 x).toNat = (w_n636 x).toNat + 2 * (w_n637 x).toNat + 4 * (w_n638 x).toNat := g0 _ _ _ _ _ _ 
theorem e213 (x : Nat → Bool) : 2 * (w_n610 x).toNat + 2 * (w_n613 x).toNat + 2 * (w_n616 x).toNat + 2 * (w_n619 x).toNat + 2 * (w_n622 x).toNat + 2 * (w_n625 x).toNat = 2 * (w_n636 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n638 x).toNat := by
  have h := u213 x
  omega
def w_n639 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n611 x).toNat + 2 * (w_n614 x).toNat + 4 * (w_n617 x).toNat + 8 * (w_n620 x).toNat + 16 * (w_n623 x).toNat + 32 * (w_n626 x).toNat)
def w_n640 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n611 x).toNat + 2 * (w_n614 x).toNat + 4 * (w_n617 x).toNat + 8 * (w_n620 x).toNat + 16 * (w_n623 x).toNat + 32 * (w_n626 x).toNat)
def w_n641 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n611 x).toNat + 2 * (w_n614 x).toNat + 4 * (w_n617 x).toNat + 8 * (w_n620 x).toNat + 16 * (w_n623 x).toNat + 32 * (w_n626 x).toNat)
theorem u214 (x : Nat → Bool) : (w_n611 x).toNat + (w_n614 x).toNat + (w_n617 x).toNat + (w_n620 x).toNat + (w_n623 x).toNat + (w_n626 x).toNat = (w_n639 x).toNat + 2 * (w_n640 x).toNat + 4 * (w_n641 x).toNat := g0 _ _ _ _ _ _ 
theorem e214 (x : Nat → Bool) : 4 * (w_n611 x).toNat + 4 * (w_n614 x).toNat + 4 * (w_n617 x).toNat + 4 * (w_n620 x).toNat + 4 * (w_n623 x).toNat + 4 * (w_n626 x).toNat = 4 * (w_n639 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n641 x).toNat := by
  have h := u214 x
  omega
def w_n642 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n594 x).toNat + 2 * (w_n597 x).toNat + 4 * (w_n600 x).toNat + 8 * (w_n627 x).toNat + 16 * (w_n630 x).toNat + 32 * (w_n633 x).toNat)
def w_n643 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n594 x).toNat + 2 * (w_n597 x).toNat + 4 * (w_n600 x).toNat + 8 * (w_n627 x).toNat + 16 * (w_n630 x).toNat + 32 * (w_n633 x).toNat)
def w_n644 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n594 x).toNat + 2 * (w_n597 x).toNat + 4 * (w_n600 x).toNat + 8 * (w_n627 x).toNat + 16 * (w_n630 x).toNat + 32 * (w_n633 x).toNat)
theorem u215 (x : Nat → Bool) : (w_n594 x).toNat + (w_n597 x).toNat + (w_n600 x).toNat + (w_n627 x).toNat + (w_n630 x).toNat + (w_n633 x).toNat = (w_n642 x).toNat + 2 * (w_n643 x).toNat + 4 * (w_n644 x).toNat := g0 _ _ _ _ _ _ 
theorem e215 (x : Nat → Bool) : (w_n594 x).toNat + (w_n597 x).toNat + (w_n600 x).toNat + (w_n627 x).toNat + (w_n630 x).toNat + (w_n633 x).toNat = (w_n642 x).toNat + 2 * (w_n643 x).toNat + 4 * (w_n644 x).toNat := by
  have h := u215 x
  omega
def w_n645 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n595 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n601 x).toNat + 8 * (w_n603 x).toNat + 16 * (w_n628 x).toNat + 32 * (w_n631 x).toNat)
def w_n646 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n595 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n601 x).toNat + 8 * (w_n603 x).toNat + 16 * (w_n628 x).toNat + 32 * (w_n631 x).toNat)
def w_n647 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n595 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n601 x).toNat + 8 * (w_n603 x).toNat + 16 * (w_n628 x).toNat + 32 * (w_n631 x).toNat)
theorem u216 (x : Nat → Bool) : (w_n595 x).toNat + (w_n598 x).toNat + (w_n601 x).toNat + (w_n603 x).toNat + (w_n628 x).toNat + (w_n631 x).toNat = (w_n645 x).toNat + 2 * (w_n646 x).toNat + 4 * (w_n647 x).toNat := g0 _ _ _ _ _ _ 
theorem e216 (x : Nat → Bool) : 2 * (w_n595 x).toNat + 2 * (w_n598 x).toNat + 2 * (w_n601 x).toNat + 2 * (w_n603 x).toNat + 2 * (w_n628 x).toNat + 2 * (w_n631 x).toNat = 2 * (w_n645 x).toNat + 4 * (w_n646 x).toNat + 8 * (w_n647 x).toNat := by
  have h := u216 x
  omega
def w_n648 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n596 x).toNat + 2 * (w_n599 x).toNat + 4 * (w_n602 x).toNat + 8 * (w_n604 x).toNat + 16 * (w_n606 x).toNat + 32 * (w_n629 x).toNat)
def w_n649 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n596 x).toNat + 2 * (w_n599 x).toNat + 4 * (w_n602 x).toNat + 8 * (w_n604 x).toNat + 16 * (w_n606 x).toNat + 32 * (w_n629 x).toNat)
def w_n650 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n596 x).toNat + 2 * (w_n599 x).toNat + 4 * (w_n602 x).toNat + 8 * (w_n604 x).toNat + 16 * (w_n606 x).toNat + 32 * (w_n629 x).toNat)
theorem u217 (x : Nat → Bool) : (w_n596 x).toNat + (w_n599 x).toNat + (w_n602 x).toNat + (w_n604 x).toNat + (w_n606 x).toNat + (w_n629 x).toNat = (w_n648 x).toNat + 2 * (w_n649 x).toNat + 4 * (w_n650 x).toNat := g0 _ _ _ _ _ _ 
theorem e217 (x : Nat → Bool) : 4 * (w_n596 x).toNat + 4 * (w_n599 x).toNat + 4 * (w_n602 x).toNat + 4 * (w_n604 x).toNat + 4 * (w_n606 x).toNat + 4 * (w_n629 x).toNat = 4 * (w_n648 x).toNat + 8 * (w_n649 x).toNat + 16 * (w_n650 x).toNat := by
  have h := u217 x
  omega
def w_n651 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n632 x).toNat + 2 * (w_n635 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n639 x).toNat + 16 * (w_n644 x).toNat + 32 * (w_n646 x).toNat)
def w_n652 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n632 x).toNat + 2 * (w_n635 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n639 x).toNat + 16 * (w_n644 x).toNat + 32 * (w_n646 x).toNat)
def w_n653 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n632 x).toNat + 2 * (w_n635 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n639 x).toNat + 16 * (w_n644 x).toNat + 32 * (w_n646 x).toNat)
theorem u218 (x : Nat → Bool) : (w_n632 x).toNat + (w_n635 x).toNat + (w_n637 x).toNat + (w_n639 x).toNat + (w_n644 x).toNat + (w_n646 x).toNat = (w_n651 x).toNat + 2 * (w_n652 x).toNat + 4 * (w_n653 x).toNat := g0 _ _ _ _ _ _ 
theorem e218 (x : Nat → Bool) : 4 * (w_n632 x).toNat + 4 * (w_n635 x).toNat + 4 * (w_n637 x).toNat + 4 * (w_n639 x).toNat + 4 * (w_n644 x).toNat + 4 * (w_n646 x).toNat = 4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 16 * (w_n653 x).toNat := by
  have h := u218 x
  omega
def w_n654 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n605 x).toNat + 2 * (w_n607 x).toNat + 4 * (w_n638 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n647 x).toNat + 32 * (w_n649 x).toNat)
def w_n655 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n605 x).toNat + 2 * (w_n607 x).toNat + 4 * (w_n638 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n647 x).toNat + 32 * (w_n649 x).toNat)
def w_n656 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n605 x).toNat + 2 * (w_n607 x).toNat + 4 * (w_n638 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n647 x).toNat + 32 * (w_n649 x).toNat)
theorem u219 (x : Nat → Bool) : (w_n605 x).toNat + (w_n607 x).toNat + (w_n638 x).toNat + (w_n640 x).toNat + (w_n647 x).toNat + (w_n649 x).toNat = (w_n654 x).toNat + 2 * (w_n655 x).toNat + 4 * (w_n656 x).toNat := g0 _ _ _ _ _ _ 
theorem e219 (x : Nat → Bool) : 8 * (w_n605 x).toNat + 8 * (w_n607 x).toNat + 8 * (w_n638 x).toNat + 8 * (w_n640 x).toNat + 8 * (w_n647 x).toNat + 8 * (w_n649 x).toNat = 8 * (w_n654 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n656 x).toNat := by
  have h := u219 x
  omega
def w_n657 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 205).toNat + 2 * (x 206).toNat + 4 * (x 207).toNat + 8 * (x 208).toNat + 16 * (x 209).toNat + 32 * (x 210).toNat)
def w_n658 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 205).toNat + 2 * (x 206).toNat + 4 * (x 207).toNat + 8 * (x 208).toNat + 16 * (x 209).toNat + 32 * (x 210).toNat)
def w_n659 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 205).toNat + 2 * (x 206).toNat + 4 * (x 207).toNat + 8 * (x 208).toNat + 16 * (x 209).toNat + 32 * (x 210).toNat)
theorem u220 (x : Nat → Bool) : (x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat = (w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat := g0 _ _ _ _ _ _ 
theorem e220 (x : Nat → Bool) : (x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat = (w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat := by
  have h := u220 x
  omega
def w_n660 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 199).toNat + 2 * (x 200).toNat + 4 * (x 201).toNat + 8 * (x 202).toNat + 16 * (x 203).toNat + 32 * (x 204).toNat)
def w_n661 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 199).toNat + 2 * (x 200).toNat + 4 * (x 201).toNat + 8 * (x 202).toNat + 16 * (x 203).toNat + 32 * (x 204).toNat)
def w_n662 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 199).toNat + 2 * (x 200).toNat + 4 * (x 201).toNat + 8 * (x 202).toNat + 16 * (x 203).toNat + 32 * (x 204).toNat)
theorem u221 (x : Nat → Bool) : (x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat = (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat := g0 _ _ _ _ _ _ 
theorem e221 (x : Nat → Bool) : (x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat = (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat := by
  have h := u221 x
  omega
def w_n663 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 217).toNat + 2 * (x 218).toNat + 4 * (x 219).toNat + 8 * (x 220).toNat + 16 * (x 221).toNat + 32 * (x 222).toNat)
def w_n664 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 217).toNat + 2 * (x 218).toNat + 4 * (x 219).toNat + 8 * (x 220).toNat + 16 * (x 221).toNat + 32 * (x 222).toNat)
def w_n665 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 217).toNat + 2 * (x 218).toNat + 4 * (x 219).toNat + 8 * (x 220).toNat + 16 * (x 221).toNat + 32 * (x 222).toNat)
theorem u222 (x : Nat → Bool) : (x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat = (w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat := g0 _ _ _ _ _ _ 
theorem e222 (x : Nat → Bool) : (x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat = (w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat := by
  have h := u222 x
  omega
def w_n666 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 211).toNat + 2 * (x 212).toNat + 4 * (x 213).toNat + 8 * (x 214).toNat + 16 * (x 215).toNat + 32 * (x 216).toNat)
def w_n667 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 211).toNat + 2 * (x 212).toNat + 4 * (x 213).toNat + 8 * (x 214).toNat + 16 * (x 215).toNat + 32 * (x 216).toNat)
def w_n668 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 211).toNat + 2 * (x 212).toNat + 4 * (x 213).toNat + 8 * (x 214).toNat + 16 * (x 215).toNat + 32 * (x 216).toNat)
theorem u223 (x : Nat → Bool) : (x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat = (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat := g0 _ _ _ _ _ _ 
theorem e223 (x : Nat → Bool) : (x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat = (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat := by
  have h := u223 x
  omega
def w_n669 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 175).toNat + 2 * (x 176).toNat + 4 * (x 177).toNat + 8 * (x 178).toNat + 16 * (x 179).toNat + 32 * (x 180).toNat)
def w_n670 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 175).toNat + 2 * (x 176).toNat + 4 * (x 177).toNat + 8 * (x 178).toNat + 16 * (x 179).toNat + 32 * (x 180).toNat)
def w_n671 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 175).toNat + 2 * (x 176).toNat + 4 * (x 177).toNat + 8 * (x 178).toNat + 16 * (x 179).toNat + 32 * (x 180).toNat)
theorem u224 (x : Nat → Bool) : (x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat = (w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat := g0 _ _ _ _ _ _ 
theorem e224 (x : Nat → Bool) : (x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat = (w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat := by
  have h := u224 x
  omega
def w_n672 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 181).toNat + 2 * (x 182).toNat + 4 * (x 183).toNat + 8 * (x 184).toNat + 16 * (x 185).toNat + 32 * (x 186).toNat)
def w_n673 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 181).toNat + 2 * (x 182).toNat + 4 * (x 183).toNat + 8 * (x 184).toNat + 16 * (x 185).toNat + 32 * (x 186).toNat)
def w_n674 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 181).toNat + 2 * (x 182).toNat + 4 * (x 183).toNat + 8 * (x 184).toNat + 16 * (x 185).toNat + 32 * (x 186).toNat)
theorem u225 (x : Nat → Bool) : (x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat = (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat := g0 _ _ _ _ _ _ 
theorem e225 (x : Nat → Bool) : (x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat = (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat := by
  have h := u225 x
  omega
def w_n675 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 187).toNat + 2 * (x 188).toNat + 4 * (x 189).toNat + 8 * (x 190).toNat + 16 * (x 191).toNat + 32 * (x 192).toNat)
def w_n676 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 187).toNat + 2 * (x 188).toNat + 4 * (x 189).toNat + 8 * (x 190).toNat + 16 * (x 191).toNat + 32 * (x 192).toNat)
def w_n677 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 187).toNat + 2 * (x 188).toNat + 4 * (x 189).toNat + 8 * (x 190).toNat + 16 * (x 191).toNat + 32 * (x 192).toNat)
theorem u226 (x : Nat → Bool) : (x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat = (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat := g0 _ _ _ _ _ _ 
theorem e226 (x : Nat → Bool) : (x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat = (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat := by
  have h := u226 x
  omega
def w_n678 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 193).toNat + 2 * (x 194).toNat + 4 * (x 195).toNat + 8 * (x 196).toNat + 16 * (x 197).toNat + 32 * (x 198).toNat)
def w_n679 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 193).toNat + 2 * (x 194).toNat + 4 * (x 195).toNat + 8 * (x 196).toNat + 16 * (x 197).toNat + 32 * (x 198).toNat)
def w_n680 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 193).toNat + 2 * (x 194).toNat + 4 * (x 195).toNat + 8 * (x 196).toNat + 16 * (x 197).toNat + 32 * (x 198).toNat)
theorem u227 (x : Nat → Bool) : (x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat = (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat := g0 _ _ _ _ _ _ 
theorem e227 (x : Nat → Bool) : (x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat = (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat := by
  have h := u227 x
  omega
def w_n681 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n657 x).toNat + 2 * (w_n660 x).toNat + 4 * (w_n663 x).toNat + 8 * (w_n666 x).toNat + 16 * (w_n669 x).toNat + 32 * (w_n672 x).toNat)
def w_n682 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n657 x).toNat + 2 * (w_n660 x).toNat + 4 * (w_n663 x).toNat + 8 * (w_n666 x).toNat + 16 * (w_n669 x).toNat + 32 * (w_n672 x).toNat)
def w_n683 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n657 x).toNat + 2 * (w_n660 x).toNat + 4 * (w_n663 x).toNat + 8 * (w_n666 x).toNat + 16 * (w_n669 x).toNat + 32 * (w_n672 x).toNat)
theorem u228 (x : Nat → Bool) : (w_n657 x).toNat + (w_n660 x).toNat + (w_n663 x).toNat + (w_n666 x).toNat + (w_n669 x).toNat + (w_n672 x).toNat = (w_n681 x).toNat + 2 * (w_n682 x).toNat + 4 * (w_n683 x).toNat := g0 _ _ _ _ _ _ 
theorem e228 (x : Nat → Bool) : (w_n657 x).toNat + (w_n660 x).toNat + (w_n663 x).toNat + (w_n666 x).toNat + (w_n669 x).toNat + (w_n672 x).toNat = (w_n681 x).toNat + 2 * (w_n682 x).toNat + 4 * (w_n683 x).toNat := by
  have h := u228 x
  omega
def w_n684 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n658 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n664 x).toNat + 8 * (w_n667 x).toNat + 16 * (w_n670 x).toNat + 32 * (w_n673 x).toNat)
def w_n685 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n658 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n664 x).toNat + 8 * (w_n667 x).toNat + 16 * (w_n670 x).toNat + 32 * (w_n673 x).toNat)
def w_n686 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n658 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n664 x).toNat + 8 * (w_n667 x).toNat + 16 * (w_n670 x).toNat + 32 * (w_n673 x).toNat)
theorem u229 (x : Nat → Bool) : (w_n658 x).toNat + (w_n661 x).toNat + (w_n664 x).toNat + (w_n667 x).toNat + (w_n670 x).toNat + (w_n673 x).toNat = (w_n684 x).toNat + 2 * (w_n685 x).toNat + 4 * (w_n686 x).toNat := g0 _ _ _ _ _ _ 
theorem e229 (x : Nat → Bool) : 2 * (w_n658 x).toNat + 2 * (w_n661 x).toNat + 2 * (w_n664 x).toNat + 2 * (w_n667 x).toNat + 2 * (w_n670 x).toNat + 2 * (w_n673 x).toNat = 2 * (w_n684 x).toNat + 4 * (w_n685 x).toNat + 8 * (w_n686 x).toNat := by
  have h := u229 x
  omega
def w_n687 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n659 x).toNat + 2 * (w_n662 x).toNat + 4 * (w_n665 x).toNat + 8 * (w_n668 x).toNat + 16 * (w_n671 x).toNat + 32 * (w_n674 x).toNat)
def w_n688 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n659 x).toNat + 2 * (w_n662 x).toNat + 4 * (w_n665 x).toNat + 8 * (w_n668 x).toNat + 16 * (w_n671 x).toNat + 32 * (w_n674 x).toNat)
def w_n689 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n659 x).toNat + 2 * (w_n662 x).toNat + 4 * (w_n665 x).toNat + 8 * (w_n668 x).toNat + 16 * (w_n671 x).toNat + 32 * (w_n674 x).toNat)
theorem u230 (x : Nat → Bool) : (w_n659 x).toNat + (w_n662 x).toNat + (w_n665 x).toNat + (w_n668 x).toNat + (w_n671 x).toNat + (w_n674 x).toNat = (w_n687 x).toNat + 2 * (w_n688 x).toNat + 4 * (w_n689 x).toNat := g0 _ _ _ _ _ _ 
theorem e230 (x : Nat → Bool) : 4 * (w_n659 x).toNat + 4 * (w_n662 x).toNat + 4 * (w_n665 x).toNat + 4 * (w_n668 x).toNat + 4 * (w_n671 x).toNat + 4 * (w_n674 x).toNat = 4 * (w_n687 x).toNat + 8 * (w_n688 x).toNat + 16 * (w_n689 x).toNat := by
  have h := u230 x
  omega
def w_n690 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 247).toNat + 2 * (x 248).toNat + 4 * (x 249).toNat + 8 * (x 250).toNat + 16 * (x 251).toNat + 32 * (x 252).toNat)
def w_n691 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 247).toNat + 2 * (x 248).toNat + 4 * (x 249).toNat + 8 * (x 250).toNat + 16 * (x 251).toNat + 32 * (x 252).toNat)
def w_n692 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 247).toNat + 2 * (x 248).toNat + 4 * (x 249).toNat + 8 * (x 250).toNat + 16 * (x 251).toNat + 32 * (x 252).toNat)
theorem u231 (x : Nat → Bool) : (x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat = (w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat := g0 _ _ _ _ _ _ 
theorem e231 (x : Nat → Bool) : (x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat = (w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat := by
  have h := u231 x
  omega
def w_n693 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 253).toNat + 2 * (x 254).toNat + 4 * (x 255).toNat + 8 * (x 256).toNat + 16 * (x 257).toNat + 32 * (x 258).toNat)
def w_n694 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 253).toNat + 2 * (x 254).toNat + 4 * (x 255).toNat + 8 * (x 256).toNat + 16 * (x 257).toNat + 32 * (x 258).toNat)
def w_n695 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 253).toNat + 2 * (x 254).toNat + 4 * (x 255).toNat + 8 * (x 256).toNat + 16 * (x 257).toNat + 32 * (x 258).toNat)
theorem u232 (x : Nat → Bool) : (x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat = (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat := g0 _ _ _ _ _ _ 
theorem e232 (x : Nat → Bool) : (x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat = (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat := by
  have h := u232 x
  omega
def w_n696 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 259).toNat + 2 * (x 260).toNat + 4 * (x 261).toNat + 8 * (x 262).toNat + 16 * (x 263).toNat + 32 * (x 264).toNat)
def w_n697 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 259).toNat + 2 * (x 260).toNat + 4 * (x 261).toNat + 8 * (x 262).toNat + 16 * (x 263).toNat + 32 * (x 264).toNat)
def w_n698 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 259).toNat + 2 * (x 260).toNat + 4 * (x 261).toNat + 8 * (x 262).toNat + 16 * (x 263).toNat + 32 * (x 264).toNat)
theorem u233 (x : Nat → Bool) : (x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat = (w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat := g0 _ _ _ _ _ _ 
theorem e233 (x : Nat → Bool) : (x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat = (w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat := by
  have h := u233 x
  omega
def w_n699 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 265).toNat + 2 * (x 266).toNat + 4 * (x 267).toNat + 8 * (x 268).toNat + 16 * (x 269).toNat + 32 * (x 270).toNat)
def w_n700 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 265).toNat + 2 * (x 266).toNat + 4 * (x 267).toNat + 8 * (x 268).toNat + 16 * (x 269).toNat + 32 * (x 270).toNat)
def w_n701 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 265).toNat + 2 * (x 266).toNat + 4 * (x 267).toNat + 8 * (x 268).toNat + 16 * (x 269).toNat + 32 * (x 270).toNat)
theorem u234 (x : Nat → Bool) : (x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat = (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat := g0 _ _ _ _ _ _ 
theorem e234 (x : Nat → Bool) : (x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat = (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat := by
  have h := u234 x
  omega
def w_n702 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 235).toNat + 2 * (x 236).toNat + 4 * (x 237).toNat + 8 * (x 238).toNat + 16 * (x 239).toNat + 32 * (x 240).toNat)
def w_n703 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 235).toNat + 2 * (x 236).toNat + 4 * (x 237).toNat + 8 * (x 238).toNat + 16 * (x 239).toNat + 32 * (x 240).toNat)
def w_n704 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 235).toNat + 2 * (x 236).toNat + 4 * (x 237).toNat + 8 * (x 238).toNat + 16 * (x 239).toNat + 32 * (x 240).toNat)
theorem u235 (x : Nat → Bool) : (x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat = (w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat := g0 _ _ _ _ _ _ 
theorem e235 (x : Nat → Bool) : (x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat = (w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat := by
  have h := u235 x
  omega
def w_n705 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 241).toNat + 2 * (x 242).toNat + 4 * (x 243).toNat + 8 * (x 244).toNat + 16 * (x 245).toNat + 32 * (x 246).toNat)
def w_n706 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 241).toNat + 2 * (x 242).toNat + 4 * (x 243).toNat + 8 * (x 244).toNat + 16 * (x 245).toNat + 32 * (x 246).toNat)
def w_n707 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 241).toNat + 2 * (x 242).toNat + 4 * (x 243).toNat + 8 * (x 244).toNat + 16 * (x 245).toNat + 32 * (x 246).toNat)
theorem u236 (x : Nat → Bool) : (x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat = (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat := g0 _ _ _ _ _ _ 
theorem e236 (x : Nat → Bool) : (x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat = (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat := by
  have h := u236 x
  omega
def w_n708 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 229).toNat + 2 * (x 230).toNat + 4 * (x 231).toNat + 8 * (x 232).toNat + 16 * (x 233).toNat + 32 * (x 234).toNat)
def w_n709 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 229).toNat + 2 * (x 230).toNat + 4 * (x 231).toNat + 8 * (x 232).toNat + 16 * (x 233).toNat + 32 * (x 234).toNat)
def w_n710 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 229).toNat + 2 * (x 230).toNat + 4 * (x 231).toNat + 8 * (x 232).toNat + 16 * (x 233).toNat + 32 * (x 234).toNat)
theorem u237 (x : Nat → Bool) : (x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat = (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat := g0 _ _ _ _ _ _ 
theorem e237 (x : Nat → Bool) : (x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat = (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat := by
  have h := u237 x
  omega
def w_n711 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 223).toNat + 2 * (x 224).toNat + 4 * (x 225).toNat + 8 * (x 226).toNat + 16 * (x 227).toNat + 32 * (x 228).toNat)
def w_n712 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 223).toNat + 2 * (x 224).toNat + 4 * (x 225).toNat + 8 * (x 226).toNat + 16 * (x 227).toNat + 32 * (x 228).toNat)
def w_n713 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 223).toNat + 2 * (x 224).toNat + 4 * (x 225).toNat + 8 * (x 226).toNat + 16 * (x 227).toNat + 32 * (x 228).toNat)
theorem u238 (x : Nat → Bool) : (x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat = (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat := g0 _ _ _ _ _ _ 
theorem e238 (x : Nat → Bool) : (x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat = (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat := by
  have h := u238 x
  omega
def w_n714 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n690 x).toNat + 2 * (w_n693 x).toNat + 4 * (w_n696 x).toNat + 8 * (w_n699 x).toNat + 16 * (w_n702 x).toNat + 32 * (w_n705 x).toNat)
def w_n715 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n690 x).toNat + 2 * (w_n693 x).toNat + 4 * (w_n696 x).toNat + 8 * (w_n699 x).toNat + 16 * (w_n702 x).toNat + 32 * (w_n705 x).toNat)
def w_n716 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n690 x).toNat + 2 * (w_n693 x).toNat + 4 * (w_n696 x).toNat + 8 * (w_n699 x).toNat + 16 * (w_n702 x).toNat + 32 * (w_n705 x).toNat)
theorem u239 (x : Nat → Bool) : (w_n690 x).toNat + (w_n693 x).toNat + (w_n696 x).toNat + (w_n699 x).toNat + (w_n702 x).toNat + (w_n705 x).toNat = (w_n714 x).toNat + 2 * (w_n715 x).toNat + 4 * (w_n716 x).toNat := g0 _ _ _ _ _ _ 
theorem e239 (x : Nat → Bool) : (w_n690 x).toNat + (w_n693 x).toNat + (w_n696 x).toNat + (w_n699 x).toNat + (w_n702 x).toNat + (w_n705 x).toNat = (w_n714 x).toNat + 2 * (w_n715 x).toNat + 4 * (w_n716 x).toNat := by
  have h := u239 x
  omega
def w_n717 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n691 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n697 x).toNat + 8 * (w_n700 x).toNat + 16 * (w_n703 x).toNat + 32 * (w_n706 x).toNat)
def w_n718 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n691 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n697 x).toNat + 8 * (w_n700 x).toNat + 16 * (w_n703 x).toNat + 32 * (w_n706 x).toNat)
def w_n719 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n691 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n697 x).toNat + 8 * (w_n700 x).toNat + 16 * (w_n703 x).toNat + 32 * (w_n706 x).toNat)
theorem u240 (x : Nat → Bool) : (w_n691 x).toNat + (w_n694 x).toNat + (w_n697 x).toNat + (w_n700 x).toNat + (w_n703 x).toNat + (w_n706 x).toNat = (w_n717 x).toNat + 2 * (w_n718 x).toNat + 4 * (w_n719 x).toNat := g0 _ _ _ _ _ _ 
theorem e240 (x : Nat → Bool) : 2 * (w_n691 x).toNat + 2 * (w_n694 x).toNat + 2 * (w_n697 x).toNat + 2 * (w_n700 x).toNat + 2 * (w_n703 x).toNat + 2 * (w_n706 x).toNat = 2 * (w_n717 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n719 x).toNat := by
  have h := u240 x
  omega
def w_n720 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n692 x).toNat + 2 * (w_n695 x).toNat + 4 * (w_n698 x).toNat + 8 * (w_n701 x).toNat + 16 * (w_n704 x).toNat + 32 * (w_n707 x).toNat)
def w_n721 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n692 x).toNat + 2 * (w_n695 x).toNat + 4 * (w_n698 x).toNat + 8 * (w_n701 x).toNat + 16 * (w_n704 x).toNat + 32 * (w_n707 x).toNat)
def w_n722 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n692 x).toNat + 2 * (w_n695 x).toNat + 4 * (w_n698 x).toNat + 8 * (w_n701 x).toNat + 16 * (w_n704 x).toNat + 32 * (w_n707 x).toNat)
theorem u241 (x : Nat → Bool) : (w_n692 x).toNat + (w_n695 x).toNat + (w_n698 x).toNat + (w_n701 x).toNat + (w_n704 x).toNat + (w_n707 x).toNat = (w_n720 x).toNat + 2 * (w_n721 x).toNat + 4 * (w_n722 x).toNat := g0 _ _ _ _ _ _ 
theorem e241 (x : Nat → Bool) : 4 * (w_n692 x).toNat + 4 * (w_n695 x).toNat + 4 * (w_n698 x).toNat + 4 * (w_n701 x).toNat + 4 * (w_n704 x).toNat + 4 * (w_n707 x).toNat = 4 * (w_n720 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n722 x).toNat := by
  have h := u241 x
  omega
def w_n723 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n675 x).toNat + 2 * (w_n678 x).toNat + 4 * (w_n681 x).toNat + 8 * (w_n708 x).toNat + 16 * (w_n711 x).toNat + 32 * (w_n714 x).toNat)
def w_n724 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n675 x).toNat + 2 * (w_n678 x).toNat + 4 * (w_n681 x).toNat + 8 * (w_n708 x).toNat + 16 * (w_n711 x).toNat + 32 * (w_n714 x).toNat)
def w_n725 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n675 x).toNat + 2 * (w_n678 x).toNat + 4 * (w_n681 x).toNat + 8 * (w_n708 x).toNat + 16 * (w_n711 x).toNat + 32 * (w_n714 x).toNat)
theorem u242 (x : Nat → Bool) : (w_n675 x).toNat + (w_n678 x).toNat + (w_n681 x).toNat + (w_n708 x).toNat + (w_n711 x).toNat + (w_n714 x).toNat = (w_n723 x).toNat + 2 * (w_n724 x).toNat + 4 * (w_n725 x).toNat := g0 _ _ _ _ _ _ 
theorem e242 (x : Nat → Bool) : (w_n675 x).toNat + (w_n678 x).toNat + (w_n681 x).toNat + (w_n708 x).toNat + (w_n711 x).toNat + (w_n714 x).toNat = (w_n723 x).toNat + 2 * (w_n724 x).toNat + 4 * (w_n725 x).toNat := by
  have h := u242 x
  omega
def w_n726 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n676 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n682 x).toNat + 8 * (w_n684 x).toNat + 16 * (w_n709 x).toNat + 32 * (w_n712 x).toNat)
def w_n727 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n676 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n682 x).toNat + 8 * (w_n684 x).toNat + 16 * (w_n709 x).toNat + 32 * (w_n712 x).toNat)
def w_n728 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n676 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n682 x).toNat + 8 * (w_n684 x).toNat + 16 * (w_n709 x).toNat + 32 * (w_n712 x).toNat)
theorem u243 (x : Nat → Bool) : (w_n676 x).toNat + (w_n679 x).toNat + (w_n682 x).toNat + (w_n684 x).toNat + (w_n709 x).toNat + (w_n712 x).toNat = (w_n726 x).toNat + 2 * (w_n727 x).toNat + 4 * (w_n728 x).toNat := g0 _ _ _ _ _ _ 
theorem e243 (x : Nat → Bool) : 2 * (w_n676 x).toNat + 2 * (w_n679 x).toNat + 2 * (w_n682 x).toNat + 2 * (w_n684 x).toNat + 2 * (w_n709 x).toNat + 2 * (w_n712 x).toNat = 2 * (w_n726 x).toNat + 4 * (w_n727 x).toNat + 8 * (w_n728 x).toNat := by
  have h := u243 x
  omega
def w_n729 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n677 x).toNat + 2 * (w_n680 x).toNat + 4 * (w_n683 x).toNat + 8 * (w_n685 x).toNat + 16 * (w_n687 x).toNat + 32 * (w_n710 x).toNat)
def w_n730 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n677 x).toNat + 2 * (w_n680 x).toNat + 4 * (w_n683 x).toNat + 8 * (w_n685 x).toNat + 16 * (w_n687 x).toNat + 32 * (w_n710 x).toNat)
def w_n731 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n677 x).toNat + 2 * (w_n680 x).toNat + 4 * (w_n683 x).toNat + 8 * (w_n685 x).toNat + 16 * (w_n687 x).toNat + 32 * (w_n710 x).toNat)
theorem u244 (x : Nat → Bool) : (w_n677 x).toNat + (w_n680 x).toNat + (w_n683 x).toNat + (w_n685 x).toNat + (w_n687 x).toNat + (w_n710 x).toNat = (w_n729 x).toNat + 2 * (w_n730 x).toNat + 4 * (w_n731 x).toNat := g0 _ _ _ _ _ _ 
theorem e244 (x : Nat → Bool) : 4 * (w_n677 x).toNat + 4 * (w_n680 x).toNat + 4 * (w_n683 x).toNat + 4 * (w_n685 x).toNat + 4 * (w_n687 x).toNat + 4 * (w_n710 x).toNat = 4 * (w_n729 x).toNat + 8 * (w_n730 x).toNat + 16 * (w_n731 x).toNat := by
  have h := u244 x
  omega
def w_n732 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n713 x).toNat + 2 * (w_n716 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n720 x).toNat + 16 * (w_n725 x).toNat + 32 * (w_n727 x).toNat)
def w_n733 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n713 x).toNat + 2 * (w_n716 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n720 x).toNat + 16 * (w_n725 x).toNat + 32 * (w_n727 x).toNat)
def w_n734 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n713 x).toNat + 2 * (w_n716 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n720 x).toNat + 16 * (w_n725 x).toNat + 32 * (w_n727 x).toNat)
theorem u245 (x : Nat → Bool) : (w_n713 x).toNat + (w_n716 x).toNat + (w_n718 x).toNat + (w_n720 x).toNat + (w_n725 x).toNat + (w_n727 x).toNat = (w_n732 x).toNat + 2 * (w_n733 x).toNat + 4 * (w_n734 x).toNat := g0 _ _ _ _ _ _ 
theorem e245 (x : Nat → Bool) : 4 * (w_n713 x).toNat + 4 * (w_n716 x).toNat + 4 * (w_n718 x).toNat + 4 * (w_n720 x).toNat + 4 * (w_n725 x).toNat + 4 * (w_n727 x).toNat = 4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat := by
  have h := u245 x
  omega
def w_n735 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n686 x).toNat + 2 * (w_n688 x).toNat + 4 * (w_n719 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n728 x).toNat + 32 * (w_n730 x).toNat)
def w_n736 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n686 x).toNat + 2 * (w_n688 x).toNat + 4 * (w_n719 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n728 x).toNat + 32 * (w_n730 x).toNat)
def w_n737 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n686 x).toNat + 2 * (w_n688 x).toNat + 4 * (w_n719 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n728 x).toNat + 32 * (w_n730 x).toNat)
theorem u246 (x : Nat → Bool) : (w_n686 x).toNat + (w_n688 x).toNat + (w_n719 x).toNat + (w_n721 x).toNat + (w_n728 x).toNat + (w_n730 x).toNat = (w_n735 x).toNat + 2 * (w_n736 x).toNat + 4 * (w_n737 x).toNat := g0 _ _ _ _ _ _ 
theorem e246 (x : Nat → Bool) : 8 * (w_n686 x).toNat + 8 * (w_n688 x).toNat + 8 * (w_n719 x).toNat + 8 * (w_n721 x).toNat + 8 * (w_n728 x).toNat + 8 * (w_n730 x).toNat = 8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat := by
  have h := u246 x
  omega
def w_n738 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n634 x).toNat + 2 * (w_n636 x).toNat + 4 * (w_n643 x).toNat + 8 * (w_n645 x).toNat + 16 * (w_n715 x).toNat + 32 * (w_n717 x).toNat)
def w_n739 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n634 x).toNat + 2 * (w_n636 x).toNat + 4 * (w_n643 x).toNat + 8 * (w_n645 x).toNat + 16 * (w_n715 x).toNat + 32 * (w_n717 x).toNat)
def w_n740 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n634 x).toNat + 2 * (w_n636 x).toNat + 4 * (w_n643 x).toNat + 8 * (w_n645 x).toNat + 16 * (w_n715 x).toNat + 32 * (w_n717 x).toNat)
theorem u247 (x : Nat → Bool) : (w_n634 x).toNat + (w_n636 x).toNat + (w_n643 x).toNat + (w_n645 x).toNat + (w_n715 x).toNat + (w_n717 x).toNat = (w_n738 x).toNat + 2 * (w_n739 x).toNat + 4 * (w_n740 x).toNat := g0 _ _ _ _ _ _ 
theorem e247 (x : Nat → Bool) : 2 * (w_n634 x).toNat + 2 * (w_n636 x).toNat + 2 * (w_n643 x).toNat + 2 * (w_n645 x).toNat + 2 * (w_n715 x).toNat + 2 * (w_n717 x).toNat = 2 * (w_n738 x).toNat + 4 * (w_n739 x).toNat + 8 * (w_n740 x).toNat := by
  have h := u247 x
  omega
def w_n741 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n608 x).toNat + 2 * (w_n641 x).toNat + 4 * (w_n650 x).toNat + 8 * (w_n653 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n689 x).toNat)
def w_n742 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n608 x).toNat + 2 * (w_n641 x).toNat + 4 * (w_n650 x).toNat + 8 * (w_n653 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n689 x).toNat)
def w_n743 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n608 x).toNat + 2 * (w_n641 x).toNat + 4 * (w_n650 x).toNat + 8 * (w_n653 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n689 x).toNat)
theorem u248 (x : Nat → Bool) : (w_n608 x).toNat + (w_n641 x).toNat + (w_n650 x).toNat + (w_n653 x).toNat + (w_n655 x).toNat + (w_n689 x).toNat = (w_n741 x).toNat + 2 * (w_n742 x).toNat + 4 * (w_n743 x).toNat := g0 _ _ _ _ _ _ 
theorem e248 (x : Nat → Bool) : 16 * (w_n608 x).toNat + 16 * (w_n641 x).toNat + 16 * (w_n650 x).toNat + 16 * (w_n653 x).toNat + 16 * (w_n655 x).toNat + 16 * (w_n689 x).toNat = 16 * (w_n741 x).toNat + 32 * (w_n742 x).toNat + 64 * (w_n743 x).toNat := by
  have h := u248 x
  omega
def w_n744 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 361).toNat + 2 * (x 362).toNat + 4 * (x 363).toNat + 8 * (x 364).toNat + 16 * (x 365).toNat + 32 * (x 366).toNat)
def w_n745 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 361).toNat + 2 * (x 362).toNat + 4 * (x 363).toNat + 8 * (x 364).toNat + 16 * (x 365).toNat + 32 * (x 366).toNat)
def w_n746 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 361).toNat + 2 * (x 362).toNat + 4 * (x 363).toNat + 8 * (x 364).toNat + 16 * (x 365).toNat + 32 * (x 366).toNat)
theorem u249 (x : Nat → Bool) : (x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat = (w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat := g0 _ _ _ _ _ _ 
theorem e249 (x : Nat → Bool) : (x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat = (w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat := by
  have h := u249 x
  omega
def w_n747 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 355).toNat + 2 * (x 356).toNat + 4 * (x 357).toNat + 8 * (x 358).toNat + 16 * (x 359).toNat + 32 * (x 360).toNat)
def w_n748 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 355).toNat + 2 * (x 356).toNat + 4 * (x 357).toNat + 8 * (x 358).toNat + 16 * (x 359).toNat + 32 * (x 360).toNat)
def w_n749 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 355).toNat + 2 * (x 356).toNat + 4 * (x 357).toNat + 8 * (x 358).toNat + 16 * (x 359).toNat + 32 * (x 360).toNat)
theorem u250 (x : Nat → Bool) : (x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat = (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat := g0 _ _ _ _ _ _ 
theorem e250 (x : Nat → Bool) : (x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat = (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat := by
  have h := u250 x
  omega
def w_n750 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 349).toNat + 2 * (x 350).toNat + 4 * (x 351).toNat + 8 * (x 352).toNat + 16 * (x 353).toNat + 32 * (x 354).toNat)
def w_n751 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 349).toNat + 2 * (x 350).toNat + 4 * (x 351).toNat + 8 * (x 352).toNat + 16 * (x 353).toNat + 32 * (x 354).toNat)
def w_n752 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 349).toNat + 2 * (x 350).toNat + 4 * (x 351).toNat + 8 * (x 352).toNat + 16 * (x 353).toNat + 32 * (x 354).toNat)
theorem u251 (x : Nat → Bool) : (x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat = (w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat := g0 _ _ _ _ _ _ 
theorem e251 (x : Nat → Bool) : (x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat = (w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat := by
  have h := u251 x
  omega
def w_n753 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 343).toNat + 2 * (x 344).toNat + 4 * (x 345).toNat + 8 * (x 346).toNat + 16 * (x 347).toNat + 32 * (x 348).toNat)
def w_n754 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 343).toNat + 2 * (x 344).toNat + 4 * (x 345).toNat + 8 * (x 346).toNat + 16 * (x 347).toNat + 32 * (x 348).toNat)
def w_n755 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 343).toNat + 2 * (x 344).toNat + 4 * (x 345).toNat + 8 * (x 346).toNat + 16 * (x 347).toNat + 32 * (x 348).toNat)
theorem u252 (x : Nat → Bool) : (x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat = (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat := g0 _ _ _ _ _ _ 
theorem e252 (x : Nat → Bool) : (x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat = (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat := by
  have h := u252 x
  omega
def w_n756 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 337).toNat + 2 * (x 338).toNat + 4 * (x 339).toNat + 8 * (x 340).toNat + 16 * (x 341).toNat + 32 * (x 342).toNat)
def w_n757 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 337).toNat + 2 * (x 338).toNat + 4 * (x 339).toNat + 8 * (x 340).toNat + 16 * (x 341).toNat + 32 * (x 342).toNat)
def w_n758 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 337).toNat + 2 * (x 338).toNat + 4 * (x 339).toNat + 8 * (x 340).toNat + 16 * (x 341).toNat + 32 * (x 342).toNat)
theorem u253 (x : Nat → Bool) : (x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat = (w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat := g0 _ _ _ _ _ _ 
theorem e253 (x : Nat → Bool) : (x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat = (w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat := by
  have h := u253 x
  omega
def w_n759 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 331).toNat + 2 * (x 332).toNat + 4 * (x 333).toNat + 8 * (x 334).toNat + 16 * (x 335).toNat + 32 * (x 336).toNat)
def w_n760 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 331).toNat + 2 * (x 332).toNat + 4 * (x 333).toNat + 8 * (x 334).toNat + 16 * (x 335).toNat + 32 * (x 336).toNat)
def w_n761 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 331).toNat + 2 * (x 332).toNat + 4 * (x 333).toNat + 8 * (x 334).toNat + 16 * (x 335).toNat + 32 * (x 336).toNat)
theorem u254 (x : Nat → Bool) : (x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat = (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat := g0 _ _ _ _ _ _ 
theorem e254 (x : Nat → Bool) : (x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat = (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat := by
  have h := u254 x
  omega
def w_n762 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 325).toNat + 2 * (x 326).toNat + 4 * (x 327).toNat + 8 * (x 328).toNat + 16 * (x 329).toNat + 32 * (x 330).toNat)
def w_n763 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 325).toNat + 2 * (x 326).toNat + 4 * (x 327).toNat + 8 * (x 328).toNat + 16 * (x 329).toNat + 32 * (x 330).toNat)
def w_n764 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 325).toNat + 2 * (x 326).toNat + 4 * (x 327).toNat + 8 * (x 328).toNat + 16 * (x 329).toNat + 32 * (x 330).toNat)
theorem u255 (x : Nat → Bool) : (x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat = (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat := g0 _ _ _ _ _ _ 
theorem e255 (x : Nat → Bool) : (x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat = (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat := by
  have h := u255 x
  omega
def w_n765 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 319).toNat + 2 * (x 320).toNat + 4 * (x 321).toNat + 8 * (x 322).toNat + 16 * (x 323).toNat + 32 * (x 324).toNat)
def w_n766 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 319).toNat + 2 * (x 320).toNat + 4 * (x 321).toNat + 8 * (x 322).toNat + 16 * (x 323).toNat + 32 * (x 324).toNat)
def w_n767 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 319).toNat + 2 * (x 320).toNat + 4 * (x 321).toNat + 8 * (x 322).toNat + 16 * (x 323).toNat + 32 * (x 324).toNat)
theorem u256 (x : Nat → Bool) : (x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat = (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat := g0 _ _ _ _ _ _ 
theorem e256 (x : Nat → Bool) : (x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat = (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat := by
  have h := u256 x
  omega
def w_n768 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n744 x).toNat + 2 * (w_n747 x).toNat + 4 * (w_n750 x).toNat + 8 * (w_n753 x).toNat + 16 * (w_n756 x).toNat + 32 * (w_n759 x).toNat)
def w_n769 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n744 x).toNat + 2 * (w_n747 x).toNat + 4 * (w_n750 x).toNat + 8 * (w_n753 x).toNat + 16 * (w_n756 x).toNat + 32 * (w_n759 x).toNat)
def w_n770 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n744 x).toNat + 2 * (w_n747 x).toNat + 4 * (w_n750 x).toNat + 8 * (w_n753 x).toNat + 16 * (w_n756 x).toNat + 32 * (w_n759 x).toNat)
theorem u257 (x : Nat → Bool) : (w_n744 x).toNat + (w_n747 x).toNat + (w_n750 x).toNat + (w_n753 x).toNat + (w_n756 x).toNat + (w_n759 x).toNat = (w_n768 x).toNat + 2 * (w_n769 x).toNat + 4 * (w_n770 x).toNat := g0 _ _ _ _ _ _ 
theorem e257 (x : Nat → Bool) : (w_n744 x).toNat + (w_n747 x).toNat + (w_n750 x).toNat + (w_n753 x).toNat + (w_n756 x).toNat + (w_n759 x).toNat = (w_n768 x).toNat + 2 * (w_n769 x).toNat + 4 * (w_n770 x).toNat := by
  have h := u257 x
  omega
def w_n771 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n745 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n751 x).toNat + 8 * (w_n754 x).toNat + 16 * (w_n757 x).toNat + 32 * (w_n760 x).toNat)
def w_n772 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n745 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n751 x).toNat + 8 * (w_n754 x).toNat + 16 * (w_n757 x).toNat + 32 * (w_n760 x).toNat)
def w_n773 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n745 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n751 x).toNat + 8 * (w_n754 x).toNat + 16 * (w_n757 x).toNat + 32 * (w_n760 x).toNat)
theorem u258 (x : Nat → Bool) : (w_n745 x).toNat + (w_n748 x).toNat + (w_n751 x).toNat + (w_n754 x).toNat + (w_n757 x).toNat + (w_n760 x).toNat = (w_n771 x).toNat + 2 * (w_n772 x).toNat + 4 * (w_n773 x).toNat := g0 _ _ _ _ _ _ 
theorem e258 (x : Nat → Bool) : 2 * (w_n745 x).toNat + 2 * (w_n748 x).toNat + 2 * (w_n751 x).toNat + 2 * (w_n754 x).toNat + 2 * (w_n757 x).toNat + 2 * (w_n760 x).toNat = 2 * (w_n771 x).toNat + 4 * (w_n772 x).toNat + 8 * (w_n773 x).toNat := by
  have h := u258 x
  omega
def w_n774 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n746 x).toNat + 2 * (w_n749 x).toNat + 4 * (w_n752 x).toNat + 8 * (w_n755 x).toNat + 16 * (w_n758 x).toNat + 32 * (w_n761 x).toNat)
def w_n775 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n746 x).toNat + 2 * (w_n749 x).toNat + 4 * (w_n752 x).toNat + 8 * (w_n755 x).toNat + 16 * (w_n758 x).toNat + 32 * (w_n761 x).toNat)
def w_n776 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n746 x).toNat + 2 * (w_n749 x).toNat + 4 * (w_n752 x).toNat + 8 * (w_n755 x).toNat + 16 * (w_n758 x).toNat + 32 * (w_n761 x).toNat)
theorem u259 (x : Nat → Bool) : (w_n746 x).toNat + (w_n749 x).toNat + (w_n752 x).toNat + (w_n755 x).toNat + (w_n758 x).toNat + (w_n761 x).toNat = (w_n774 x).toNat + 2 * (w_n775 x).toNat + 4 * (w_n776 x).toNat := g0 _ _ _ _ _ _ 
theorem e259 (x : Nat → Bool) : 4 * (w_n746 x).toNat + 4 * (w_n749 x).toNat + 4 * (w_n752 x).toNat + 4 * (w_n755 x).toNat + 4 * (w_n758 x).toNat + 4 * (w_n761 x).toNat = 4 * (w_n774 x).toNat + 8 * (w_n775 x).toNat + 16 * (w_n776 x).toNat := by
  have h := u259 x
  omega
def w_n777 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 313).toNat + 2 * (x 314).toNat + 4 * (x 315).toNat + 8 * (x 316).toNat + 16 * (x 317).toNat + 32 * (x 318).toNat)
def w_n778 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 313).toNat + 2 * (x 314).toNat + 4 * (x 315).toNat + 8 * (x 316).toNat + 16 * (x 317).toNat + 32 * (x 318).toNat)
def w_n779 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 313).toNat + 2 * (x 314).toNat + 4 * (x 315).toNat + 8 * (x 316).toNat + 16 * (x 317).toNat + 32 * (x 318).toNat)
theorem u260 (x : Nat → Bool) : (x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat = (w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat := g0 _ _ _ _ _ _ 
theorem e260 (x : Nat → Bool) : (x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat = (w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat := by
  have h := u260 x
  omega
def w_n780 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 307).toNat + 2 * (x 308).toNat + 4 * (x 309).toNat + 8 * (x 310).toNat + 16 * (x 311).toNat + 32 * (x 312).toNat)
def w_n781 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 307).toNat + 2 * (x 308).toNat + 4 * (x 309).toNat + 8 * (x 310).toNat + 16 * (x 311).toNat + 32 * (x 312).toNat)
def w_n782 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 307).toNat + 2 * (x 308).toNat + 4 * (x 309).toNat + 8 * (x 310).toNat + 16 * (x 311).toNat + 32 * (x 312).toNat)
theorem u261 (x : Nat → Bool) : (x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat = (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat := g0 _ _ _ _ _ _ 
theorem e261 (x : Nat → Bool) : (x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat = (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat := by
  have h := u261 x
  omega
def w_n783 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 295).toNat + 2 * (x 296).toNat + 4 * (x 297).toNat + 8 * (x 298).toNat + 16 * (x 299).toNat + 32 * (x 300).toNat)
def w_n784 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 295).toNat + 2 * (x 296).toNat + 4 * (x 297).toNat + 8 * (x 298).toNat + 16 * (x 299).toNat + 32 * (x 300).toNat)
def w_n785 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 295).toNat + 2 * (x 296).toNat + 4 * (x 297).toNat + 8 * (x 298).toNat + 16 * (x 299).toNat + 32 * (x 300).toNat)
theorem u262 (x : Nat → Bool) : (x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat = (w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat := g0 _ _ _ _ _ _ 
theorem e262 (x : Nat → Bool) : (x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat = (w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat := by
  have h := u262 x
  omega
def w_n786 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 301).toNat + 2 * (x 302).toNat + 4 * (x 303).toNat + 8 * (x 304).toNat + 16 * (x 305).toNat + 32 * (x 306).toNat)
def w_n787 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 301).toNat + 2 * (x 302).toNat + 4 * (x 303).toNat + 8 * (x 304).toNat + 16 * (x 305).toNat + 32 * (x 306).toNat)
def w_n788 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 301).toNat + 2 * (x 302).toNat + 4 * (x 303).toNat + 8 * (x 304).toNat + 16 * (x 305).toNat + 32 * (x 306).toNat)
theorem u263 (x : Nat → Bool) : (x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat = (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat := g0 _ _ _ _ _ _ 
theorem e263 (x : Nat → Bool) : (x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat = (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat := by
  have h := u263 x
  omega
def w_n789 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 271).toNat + 2 * (x 272).toNat + 4 * (x 273).toNat + 8 * (x 274).toNat + 16 * (x 275).toNat + 32 * (x 276).toNat)
def w_n790 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 271).toNat + 2 * (x 272).toNat + 4 * (x 273).toNat + 8 * (x 274).toNat + 16 * (x 275).toNat + 32 * (x 276).toNat)
def w_n791 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 271).toNat + 2 * (x 272).toNat + 4 * (x 273).toNat + 8 * (x 274).toNat + 16 * (x 275).toNat + 32 * (x 276).toNat)
theorem u264 (x : Nat → Bool) : (x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat = (w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat := g0 _ _ _ _ _ _ 
theorem e264 (x : Nat → Bool) : (x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat = (w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat := by
  have h := u264 x
  omega
def w_n792 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 277).toNat + 2 * (x 278).toNat + 4 * (x 279).toNat + 8 * (x 280).toNat + 16 * (x 281).toNat + 32 * (x 282).toNat)
def w_n793 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 277).toNat + 2 * (x 278).toNat + 4 * (x 279).toNat + 8 * (x 280).toNat + 16 * (x 281).toNat + 32 * (x 282).toNat)
def w_n794 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 277).toNat + 2 * (x 278).toNat + 4 * (x 279).toNat + 8 * (x 280).toNat + 16 * (x 281).toNat + 32 * (x 282).toNat)
theorem u265 (x : Nat → Bool) : (x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat = (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat := g0 _ _ _ _ _ _ 
theorem e265 (x : Nat → Bool) : (x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat = (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat := by
  have h := u265 x
  omega
def w_n795 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 289).toNat + 2 * (x 290).toNat + 4 * (x 291).toNat + 8 * (x 292).toNat + 16 * (x 293).toNat + 32 * (x 294).toNat)
def w_n796 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 289).toNat + 2 * (x 290).toNat + 4 * (x 291).toNat + 8 * (x 292).toNat + 16 * (x 293).toNat + 32 * (x 294).toNat)
def w_n797 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 289).toNat + 2 * (x 290).toNat + 4 * (x 291).toNat + 8 * (x 292).toNat + 16 * (x 293).toNat + 32 * (x 294).toNat)
theorem u266 (x : Nat → Bool) : (x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat = (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat := g0 _ _ _ _ _ _ 
theorem e266 (x : Nat → Bool) : (x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat = (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat := by
  have h := u266 x
  omega
def w_n798 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 283).toNat + 2 * (x 284).toNat + 4 * (x 285).toNat + 8 * (x 286).toNat + 16 * (x 287).toNat + 32 * (x 288).toNat)
def w_n799 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 283).toNat + 2 * (x 284).toNat + 4 * (x 285).toNat + 8 * (x 286).toNat + 16 * (x 287).toNat + 32 * (x 288).toNat)
def w_n800 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 283).toNat + 2 * (x 284).toNat + 4 * (x 285).toNat + 8 * (x 286).toNat + 16 * (x 287).toNat + 32 * (x 288).toNat)
theorem u267 (x : Nat → Bool) : (x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat = (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat := g0 _ _ _ _ _ _ 
theorem e267 (x : Nat → Bool) : (x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat = (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat := by
  have h := u267 x
  omega
def w_n801 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n777 x).toNat + 2 * (w_n780 x).toNat + 4 * (w_n783 x).toNat + 8 * (w_n786 x).toNat + 16 * (w_n789 x).toNat + 32 * (w_n792 x).toNat)
def w_n802 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n777 x).toNat + 2 * (w_n780 x).toNat + 4 * (w_n783 x).toNat + 8 * (w_n786 x).toNat + 16 * (w_n789 x).toNat + 32 * (w_n792 x).toNat)
def w_n803 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n777 x).toNat + 2 * (w_n780 x).toNat + 4 * (w_n783 x).toNat + 8 * (w_n786 x).toNat + 16 * (w_n789 x).toNat + 32 * (w_n792 x).toNat)
theorem u268 (x : Nat → Bool) : (w_n777 x).toNat + (w_n780 x).toNat + (w_n783 x).toNat + (w_n786 x).toNat + (w_n789 x).toNat + (w_n792 x).toNat = (w_n801 x).toNat + 2 * (w_n802 x).toNat + 4 * (w_n803 x).toNat := g0 _ _ _ _ _ _ 
theorem e268 (x : Nat → Bool) : (w_n777 x).toNat + (w_n780 x).toNat + (w_n783 x).toNat + (w_n786 x).toNat + (w_n789 x).toNat + (w_n792 x).toNat = (w_n801 x).toNat + 2 * (w_n802 x).toNat + 4 * (w_n803 x).toNat := by
  have h := u268 x
  omega
def w_n804 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n778 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n784 x).toNat + 8 * (w_n787 x).toNat + 16 * (w_n790 x).toNat + 32 * (w_n793 x).toNat)
def w_n805 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n778 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n784 x).toNat + 8 * (w_n787 x).toNat + 16 * (w_n790 x).toNat + 32 * (w_n793 x).toNat)
def w_n806 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n778 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n784 x).toNat + 8 * (w_n787 x).toNat + 16 * (w_n790 x).toNat + 32 * (w_n793 x).toNat)
theorem u269 (x : Nat → Bool) : (w_n778 x).toNat + (w_n781 x).toNat + (w_n784 x).toNat + (w_n787 x).toNat + (w_n790 x).toNat + (w_n793 x).toNat = (w_n804 x).toNat + 2 * (w_n805 x).toNat + 4 * (w_n806 x).toNat := g0 _ _ _ _ _ _ 
theorem e269 (x : Nat → Bool) : 2 * (w_n778 x).toNat + 2 * (w_n781 x).toNat + 2 * (w_n784 x).toNat + 2 * (w_n787 x).toNat + 2 * (w_n790 x).toNat + 2 * (w_n793 x).toNat = 2 * (w_n804 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n806 x).toNat := by
  have h := u269 x
  omega
def w_n807 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n779 x).toNat + 2 * (w_n782 x).toNat + 4 * (w_n785 x).toNat + 8 * (w_n788 x).toNat + 16 * (w_n791 x).toNat + 32 * (w_n794 x).toNat)
def w_n808 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n779 x).toNat + 2 * (w_n782 x).toNat + 4 * (w_n785 x).toNat + 8 * (w_n788 x).toNat + 16 * (w_n791 x).toNat + 32 * (w_n794 x).toNat)
def w_n809 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n779 x).toNat + 2 * (w_n782 x).toNat + 4 * (w_n785 x).toNat + 8 * (w_n788 x).toNat + 16 * (w_n791 x).toNat + 32 * (w_n794 x).toNat)
theorem u270 (x : Nat → Bool) : (w_n779 x).toNat + (w_n782 x).toNat + (w_n785 x).toNat + (w_n788 x).toNat + (w_n791 x).toNat + (w_n794 x).toNat = (w_n807 x).toNat + 2 * (w_n808 x).toNat + 4 * (w_n809 x).toNat := g0 _ _ _ _ _ _ 
theorem e270 (x : Nat → Bool) : 4 * (w_n779 x).toNat + 4 * (w_n782 x).toNat + 4 * (w_n785 x).toNat + 4 * (w_n788 x).toNat + 4 * (w_n791 x).toNat + 4 * (w_n794 x).toNat = 4 * (w_n807 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n809 x).toNat := by
  have h := u270 x
  omega
def w_n810 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n762 x).toNat + 2 * (w_n765 x).toNat + 4 * (w_n768 x).toNat + 8 * (w_n795 x).toNat + 16 * (w_n798 x).toNat + 32 * (w_n801 x).toNat)
def w_n811 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n762 x).toNat + 2 * (w_n765 x).toNat + 4 * (w_n768 x).toNat + 8 * (w_n795 x).toNat + 16 * (w_n798 x).toNat + 32 * (w_n801 x).toNat)
def w_n812 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n762 x).toNat + 2 * (w_n765 x).toNat + 4 * (w_n768 x).toNat + 8 * (w_n795 x).toNat + 16 * (w_n798 x).toNat + 32 * (w_n801 x).toNat)
theorem u271 (x : Nat → Bool) : (w_n762 x).toNat + (w_n765 x).toNat + (w_n768 x).toNat + (w_n795 x).toNat + (w_n798 x).toNat + (w_n801 x).toNat = (w_n810 x).toNat + 2 * (w_n811 x).toNat + 4 * (w_n812 x).toNat := g0 _ _ _ _ _ _ 
theorem e271 (x : Nat → Bool) : (w_n762 x).toNat + (w_n765 x).toNat + (w_n768 x).toNat + (w_n795 x).toNat + (w_n798 x).toNat + (w_n801 x).toNat = (w_n810 x).toNat + 2 * (w_n811 x).toNat + 4 * (w_n812 x).toNat := by
  have h := u271 x
  omega
def w_n813 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n763 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n769 x).toNat + 8 * (w_n771 x).toNat + 16 * (w_n796 x).toNat + 32 * (w_n799 x).toNat)
def w_n814 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n763 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n769 x).toNat + 8 * (w_n771 x).toNat + 16 * (w_n796 x).toNat + 32 * (w_n799 x).toNat)
def w_n815 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n763 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n769 x).toNat + 8 * (w_n771 x).toNat + 16 * (w_n796 x).toNat + 32 * (w_n799 x).toNat)
theorem u272 (x : Nat → Bool) : (w_n763 x).toNat + (w_n766 x).toNat + (w_n769 x).toNat + (w_n771 x).toNat + (w_n796 x).toNat + (w_n799 x).toNat = (w_n813 x).toNat + 2 * (w_n814 x).toNat + 4 * (w_n815 x).toNat := g0 _ _ _ _ _ _ 
theorem e272 (x : Nat → Bool) : 2 * (w_n763 x).toNat + 2 * (w_n766 x).toNat + 2 * (w_n769 x).toNat + 2 * (w_n771 x).toNat + 2 * (w_n796 x).toNat + 2 * (w_n799 x).toNat = 2 * (w_n813 x).toNat + 4 * (w_n814 x).toNat + 8 * (w_n815 x).toNat := by
  have h := u272 x
  omega
def w_n816 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n764 x).toNat + 2 * (w_n767 x).toNat + 4 * (w_n770 x).toNat + 8 * (w_n772 x).toNat + 16 * (w_n774 x).toNat + 32 * (w_n797 x).toNat)
def w_n817 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n764 x).toNat + 2 * (w_n767 x).toNat + 4 * (w_n770 x).toNat + 8 * (w_n772 x).toNat + 16 * (w_n774 x).toNat + 32 * (w_n797 x).toNat)
def w_n818 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n764 x).toNat + 2 * (w_n767 x).toNat + 4 * (w_n770 x).toNat + 8 * (w_n772 x).toNat + 16 * (w_n774 x).toNat + 32 * (w_n797 x).toNat)
theorem u273 (x : Nat → Bool) : (w_n764 x).toNat + (w_n767 x).toNat + (w_n770 x).toNat + (w_n772 x).toNat + (w_n774 x).toNat + (w_n797 x).toNat = (w_n816 x).toNat + 2 * (w_n817 x).toNat + 4 * (w_n818 x).toNat := g0 _ _ _ _ _ _ 
theorem e273 (x : Nat → Bool) : 4 * (w_n764 x).toNat + 4 * (w_n767 x).toNat + 4 * (w_n770 x).toNat + 4 * (w_n772 x).toNat + 4 * (w_n774 x).toNat + 4 * (w_n797 x).toNat = 4 * (w_n816 x).toNat + 8 * (w_n817 x).toNat + 16 * (w_n818 x).toNat := by
  have h := u273 x
  omega
def w_n819 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n800 x).toNat + 2 * (w_n803 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n807 x).toNat + 16 * (w_n812 x).toNat + 32 * (w_n814 x).toNat)
def w_n820 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n800 x).toNat + 2 * (w_n803 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n807 x).toNat + 16 * (w_n812 x).toNat + 32 * (w_n814 x).toNat)
def w_n821 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n800 x).toNat + 2 * (w_n803 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n807 x).toNat + 16 * (w_n812 x).toNat + 32 * (w_n814 x).toNat)
theorem u274 (x : Nat → Bool) : (w_n800 x).toNat + (w_n803 x).toNat + (w_n805 x).toNat + (w_n807 x).toNat + (w_n812 x).toNat + (w_n814 x).toNat = (w_n819 x).toNat + 2 * (w_n820 x).toNat + 4 * (w_n821 x).toNat := g0 _ _ _ _ _ _ 
theorem e274 (x : Nat → Bool) : 4 * (w_n800 x).toNat + 4 * (w_n803 x).toNat + 4 * (w_n805 x).toNat + 4 * (w_n807 x).toNat + 4 * (w_n812 x).toNat + 4 * (w_n814 x).toNat = 4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 16 * (w_n821 x).toNat := by
  have h := u274 x
  omega
def w_n822 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n773 x).toNat + 2 * (w_n775 x).toNat + 4 * (w_n806 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n815 x).toNat + 32 * (w_n817 x).toNat)
def w_n823 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n773 x).toNat + 2 * (w_n775 x).toNat + 4 * (w_n806 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n815 x).toNat + 32 * (w_n817 x).toNat)
def w_n824 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n773 x).toNat + 2 * (w_n775 x).toNat + 4 * (w_n806 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n815 x).toNat + 32 * (w_n817 x).toNat)
theorem u275 (x : Nat → Bool) : (w_n773 x).toNat + (w_n775 x).toNat + (w_n806 x).toNat + (w_n808 x).toNat + (w_n815 x).toNat + (w_n817 x).toNat = (w_n822 x).toNat + 2 * (w_n823 x).toNat + 4 * (w_n824 x).toNat := g0 _ _ _ _ _ _ 
theorem e275 (x : Nat → Bool) : 8 * (w_n773 x).toNat + 8 * (w_n775 x).toNat + 8 * (w_n806 x).toNat + 8 * (w_n808 x).toNat + 8 * (w_n815 x).toNat + 8 * (w_n817 x).toNat = 8 * (w_n822 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n824 x).toNat := by
  have h := u275 x
  omega
def w_n825 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 433).toNat + 2 * (x 434).toNat + 4 * (x 435).toNat + 8 * (x 436).toNat + 16 * (x 437).toNat + 32 * (x 438).toNat)
def w_n826 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 433).toNat + 2 * (x 434).toNat + 4 * (x 435).toNat + 8 * (x 436).toNat + 16 * (x 437).toNat + 32 * (x 438).toNat)
def w_n827 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 433).toNat + 2 * (x 434).toNat + 4 * (x 435).toNat + 8 * (x 436).toNat + 16 * (x 437).toNat + 32 * (x 438).toNat)
theorem u276 (x : Nat → Bool) : (x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat = (w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat := g0 _ _ _ _ _ _ 
theorem e276 (x : Nat → Bool) : (x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat = (w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat := by
  have h := u276 x
  omega
def w_n828 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 427).toNat + 2 * (x 428).toNat + 4 * (x 429).toNat + 8 * (x 430).toNat + 16 * (x 431).toNat + 32 * (x 432).toNat)
def w_n829 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 427).toNat + 2 * (x 428).toNat + 4 * (x 429).toNat + 8 * (x 430).toNat + 16 * (x 431).toNat + 32 * (x 432).toNat)
def w_n830 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 427).toNat + 2 * (x 428).toNat + 4 * (x 429).toNat + 8 * (x 430).toNat + 16 * (x 431).toNat + 32 * (x 432).toNat)
theorem u277 (x : Nat → Bool) : (x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat = (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat := g0 _ _ _ _ _ _ 
theorem e277 (x : Nat → Bool) : (x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat = (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat := by
  have h := u277 x
  omega
def w_n831 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 421).toNat + 2 * (x 422).toNat + 4 * (x 423).toNat + 8 * (x 424).toNat + 16 * (x 425).toNat + 32 * (x 426).toNat)
def w_n832 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 421).toNat + 2 * (x 422).toNat + 4 * (x 423).toNat + 8 * (x 424).toNat + 16 * (x 425).toNat + 32 * (x 426).toNat)
def w_n833 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 421).toNat + 2 * (x 422).toNat + 4 * (x 423).toNat + 8 * (x 424).toNat + 16 * (x 425).toNat + 32 * (x 426).toNat)
theorem u278 (x : Nat → Bool) : (x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat = (w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat := g0 _ _ _ _ _ _ 
theorem e278 (x : Nat → Bool) : (x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat = (w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat := by
  have h := u278 x
  omega
def w_n834 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 415).toNat + 2 * (x 416).toNat + 4 * (x 417).toNat + 8 * (x 418).toNat + 16 * (x 419).toNat + 32 * (x 420).toNat)
def w_n835 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 415).toNat + 2 * (x 416).toNat + 4 * (x 417).toNat + 8 * (x 418).toNat + 16 * (x 419).toNat + 32 * (x 420).toNat)
def w_n836 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 415).toNat + 2 * (x 416).toNat + 4 * (x 417).toNat + 8 * (x 418).toNat + 16 * (x 419).toNat + 32 * (x 420).toNat)
theorem u279 (x : Nat → Bool) : (x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat = (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat := g0 _ _ _ _ _ _ 
theorem e279 (x : Nat → Bool) : (x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat = (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat := by
  have h := u279 x
  omega
def w_n837 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 457).toNat + 2 * (x 458).toNat + 4 * (x 459).toNat + 8 * (x 460).toNat + 16 * (x 461).toNat + 32 * (x 462).toNat)
def w_n838 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 457).toNat + 2 * (x 458).toNat + 4 * (x 459).toNat + 8 * (x 460).toNat + 16 * (x 461).toNat + 32 * (x 462).toNat)
def w_n839 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 457).toNat + 2 * (x 458).toNat + 4 * (x 459).toNat + 8 * (x 460).toNat + 16 * (x 461).toNat + 32 * (x 462).toNat)
theorem u280 (x : Nat → Bool) : (x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat = (w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat := g0 _ _ _ _ _ _ 
theorem e280 (x : Nat → Bool) : (x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat = (w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat := by
  have h := u280 x
  omega
def w_n840 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 451).toNat + 2 * (x 452).toNat + 4 * (x 453).toNat + 8 * (x 454).toNat + 16 * (x 455).toNat + 32 * (x 456).toNat)
def w_n841 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 451).toNat + 2 * (x 452).toNat + 4 * (x 453).toNat + 8 * (x 454).toNat + 16 * (x 455).toNat + 32 * (x 456).toNat)
def w_n842 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 451).toNat + 2 * (x 452).toNat + 4 * (x 453).toNat + 8 * (x 454).toNat + 16 * (x 455).toNat + 32 * (x 456).toNat)
theorem u281 (x : Nat → Bool) : (x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat = (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat := g0 _ _ _ _ _ _ 
theorem e281 (x : Nat → Bool) : (x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat = (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat := by
  have h := u281 x
  omega
def w_n843 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 439).toNat + 2 * (x 440).toNat + 4 * (x 441).toNat + 8 * (x 442).toNat + 16 * (x 443).toNat + 32 * (x 444).toNat)
def w_n844 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 439).toNat + 2 * (x 440).toNat + 4 * (x 441).toNat + 8 * (x 442).toNat + 16 * (x 443).toNat + 32 * (x 444).toNat)
def w_n845 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 439).toNat + 2 * (x 440).toNat + 4 * (x 441).toNat + 8 * (x 442).toNat + 16 * (x 443).toNat + 32 * (x 444).toNat)
theorem u282 (x : Nat → Bool) : (x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat = (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat := g0 _ _ _ _ _ _ 
theorem e282 (x : Nat → Bool) : (x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat = (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat := by
  have h := u282 x
  omega
def w_n846 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 445).toNat + 2 * (x 446).toNat + 4 * (x 447).toNat + 8 * (x 448).toNat + 16 * (x 449).toNat + 32 * (x 450).toNat)
def w_n847 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 445).toNat + 2 * (x 446).toNat + 4 * (x 447).toNat + 8 * (x 448).toNat + 16 * (x 449).toNat + 32 * (x 450).toNat)
def w_n848 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 445).toNat + 2 * (x 446).toNat + 4 * (x 447).toNat + 8 * (x 448).toNat + 16 * (x 449).toNat + 32 * (x 450).toNat)
theorem u283 (x : Nat → Bool) : (x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat = (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat := g0 _ _ _ _ _ _ 
theorem e283 (x : Nat → Bool) : (x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat = (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat := by
  have h := u283 x
  omega
def w_n849 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n825 x).toNat + 2 * (w_n828 x).toNat + 4 * (w_n831 x).toNat + 8 * (w_n834 x).toNat + 16 * (w_n837 x).toNat + 32 * (w_n840 x).toNat)
def w_n850 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n825 x).toNat + 2 * (w_n828 x).toNat + 4 * (w_n831 x).toNat + 8 * (w_n834 x).toNat + 16 * (w_n837 x).toNat + 32 * (w_n840 x).toNat)
def w_n851 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n825 x).toNat + 2 * (w_n828 x).toNat + 4 * (w_n831 x).toNat + 8 * (w_n834 x).toNat + 16 * (w_n837 x).toNat + 32 * (w_n840 x).toNat)
theorem u284 (x : Nat → Bool) : (w_n825 x).toNat + (w_n828 x).toNat + (w_n831 x).toNat + (w_n834 x).toNat + (w_n837 x).toNat + (w_n840 x).toNat = (w_n849 x).toNat + 2 * (w_n850 x).toNat + 4 * (w_n851 x).toNat := g0 _ _ _ _ _ _ 
theorem e284 (x : Nat → Bool) : (w_n825 x).toNat + (w_n828 x).toNat + (w_n831 x).toNat + (w_n834 x).toNat + (w_n837 x).toNat + (w_n840 x).toNat = (w_n849 x).toNat + 2 * (w_n850 x).toNat + 4 * (w_n851 x).toNat := by
  have h := u284 x
  omega
def w_n852 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n826 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n832 x).toNat + 8 * (w_n835 x).toNat + 16 * (w_n838 x).toNat + 32 * (w_n841 x).toNat)
def w_n853 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n826 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n832 x).toNat + 8 * (w_n835 x).toNat + 16 * (w_n838 x).toNat + 32 * (w_n841 x).toNat)
def w_n854 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n826 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n832 x).toNat + 8 * (w_n835 x).toNat + 16 * (w_n838 x).toNat + 32 * (w_n841 x).toNat)
theorem u285 (x : Nat → Bool) : (w_n826 x).toNat + (w_n829 x).toNat + (w_n832 x).toNat + (w_n835 x).toNat + (w_n838 x).toNat + (w_n841 x).toNat = (w_n852 x).toNat + 2 * (w_n853 x).toNat + 4 * (w_n854 x).toNat := g0 _ _ _ _ _ _ 
theorem e285 (x : Nat → Bool) : 2 * (w_n826 x).toNat + 2 * (w_n829 x).toNat + 2 * (w_n832 x).toNat + 2 * (w_n835 x).toNat + 2 * (w_n838 x).toNat + 2 * (w_n841 x).toNat = 2 * (w_n852 x).toNat + 4 * (w_n853 x).toNat + 8 * (w_n854 x).toNat := by
  have h := u285 x
  omega
def w_n855 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n827 x).toNat + 2 * (w_n830 x).toNat + 4 * (w_n833 x).toNat + 8 * (w_n836 x).toNat + 16 * (w_n839 x).toNat + 32 * (w_n842 x).toNat)
def w_n856 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n827 x).toNat + 2 * (w_n830 x).toNat + 4 * (w_n833 x).toNat + 8 * (w_n836 x).toNat + 16 * (w_n839 x).toNat + 32 * (w_n842 x).toNat)
def w_n857 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n827 x).toNat + 2 * (w_n830 x).toNat + 4 * (w_n833 x).toNat + 8 * (w_n836 x).toNat + 16 * (w_n839 x).toNat + 32 * (w_n842 x).toNat)
theorem u286 (x : Nat → Bool) : (w_n827 x).toNat + (w_n830 x).toNat + (w_n833 x).toNat + (w_n836 x).toNat + (w_n839 x).toNat + (w_n842 x).toNat = (w_n855 x).toNat + 2 * (w_n856 x).toNat + 4 * (w_n857 x).toNat := g0 _ _ _ _ _ _ 
theorem e286 (x : Nat → Bool) : 4 * (w_n827 x).toNat + 4 * (w_n830 x).toNat + 4 * (w_n833 x).toNat + 4 * (w_n836 x).toNat + 4 * (w_n839 x).toNat + 4 * (w_n842 x).toNat = 4 * (w_n855 x).toNat + 8 * (w_n856 x).toNat + 16 * (w_n857 x).toNat := by
  have h := u286 x
  omega
def w_n858 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 379).toNat + 2 * (x 380).toNat + 4 * (x 381).toNat + 8 * (x 382).toNat + 16 * (x 383).toNat + 32 * (x 384).toNat)
def w_n859 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 379).toNat + 2 * (x 380).toNat + 4 * (x 381).toNat + 8 * (x 382).toNat + 16 * (x 383).toNat + 32 * (x 384).toNat)
def w_n860 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 379).toNat + 2 * (x 380).toNat + 4 * (x 381).toNat + 8 * (x 382).toNat + 16 * (x 383).toNat + 32 * (x 384).toNat)
theorem u287 (x : Nat → Bool) : (x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat = (w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat := g0 _ _ _ _ _ _ 
theorem e287 (x : Nat → Bool) : (x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat = (w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat := by
  have h := u287 x
  omega
def w_n861 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 385).toNat + 2 * (x 386).toNat + 4 * (x 387).toNat + 8 * (x 388).toNat + 16 * (x 389).toNat + 32 * (x 390).toNat)
def w_n862 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 385).toNat + 2 * (x 386).toNat + 4 * (x 387).toNat + 8 * (x 388).toNat + 16 * (x 389).toNat + 32 * (x 390).toNat)
def w_n863 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 385).toNat + 2 * (x 386).toNat + 4 * (x 387).toNat + 8 * (x 388).toNat + 16 * (x 389).toNat + 32 * (x 390).toNat)
theorem u288 (x : Nat → Bool) : (x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat = (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat := g0 _ _ _ _ _ _ 
theorem e288 (x : Nat → Bool) : (x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat = (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat := by
  have h := u288 x
  omega
def w_n864 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 373).toNat + 2 * (x 374).toNat + 4 * (x 375).toNat + 8 * (x 376).toNat + 16 * (x 377).toNat + 32 * (x 378).toNat)
def w_n865 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 373).toNat + 2 * (x 374).toNat + 4 * (x 375).toNat + 8 * (x 376).toNat + 16 * (x 377).toNat + 32 * (x 378).toNat)
def w_n866 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 373).toNat + 2 * (x 374).toNat + 4 * (x 375).toNat + 8 * (x 376).toNat + 16 * (x 377).toNat + 32 * (x 378).toNat)
theorem u289 (x : Nat → Bool) : (x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat = (w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat := g0 _ _ _ _ _ _ 
theorem e289 (x : Nat → Bool) : (x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat = (w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat := by
  have h := u289 x
  omega
def w_n867 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 367).toNat + 2 * (x 368).toNat + 4 * (x 369).toNat + 8 * (x 370).toNat + 16 * (x 371).toNat + 32 * (x 372).toNat)
def w_n868 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 367).toNat + 2 * (x 368).toNat + 4 * (x 369).toNat + 8 * (x 370).toNat + 16 * (x 371).toNat + 32 * (x 372).toNat)
def w_n869 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 367).toNat + 2 * (x 368).toNat + 4 * (x 369).toNat + 8 * (x 370).toNat + 16 * (x 371).toNat + 32 * (x 372).toNat)
theorem u290 (x : Nat → Bool) : (x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat = (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat := g0 _ _ _ _ _ _ 
theorem e290 (x : Nat → Bool) : (x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat = (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat := by
  have h := u290 x
  omega
def w_n870 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 403).toNat + 2 * (x 404).toNat + 4 * (x 405).toNat + 8 * (x 406).toNat + 16 * (x 407).toNat + 32 * (x 408).toNat)
def w_n871 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 403).toNat + 2 * (x 404).toNat + 4 * (x 405).toNat + 8 * (x 406).toNat + 16 * (x 407).toNat + 32 * (x 408).toNat)
def w_n872 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 403).toNat + 2 * (x 404).toNat + 4 * (x 405).toNat + 8 * (x 406).toNat + 16 * (x 407).toNat + 32 * (x 408).toNat)
theorem u291 (x : Nat → Bool) : (x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat = (w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat := g0 _ _ _ _ _ _ 
theorem e291 (x : Nat → Bool) : (x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat = (w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat := by
  have h := u291 x
  omega
def w_n873 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 409).toNat + 2 * (x 410).toNat + 4 * (x 411).toNat + 8 * (x 412).toNat + 16 * (x 413).toNat + 32 * (x 414).toNat)
def w_n874 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 409).toNat + 2 * (x 410).toNat + 4 * (x 411).toNat + 8 * (x 412).toNat + 16 * (x 413).toNat + 32 * (x 414).toNat)
def w_n875 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 409).toNat + 2 * (x 410).toNat + 4 * (x 411).toNat + 8 * (x 412).toNat + 16 * (x 413).toNat + 32 * (x 414).toNat)
theorem u292 (x : Nat → Bool) : (x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat = (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat := g0 _ _ _ _ _ _ 
theorem e292 (x : Nat → Bool) : (x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat = (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat := by
  have h := u292 x
  omega
def w_n876 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 391).toNat + 2 * (x 392).toNat + 4 * (x 393).toNat + 8 * (x 394).toNat + 16 * (x 395).toNat + 32 * (x 396).toNat)
def w_n877 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 391).toNat + 2 * (x 392).toNat + 4 * (x 393).toNat + 8 * (x 394).toNat + 16 * (x 395).toNat + 32 * (x 396).toNat)
def w_n878 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 391).toNat + 2 * (x 392).toNat + 4 * (x 393).toNat + 8 * (x 394).toNat + 16 * (x 395).toNat + 32 * (x 396).toNat)
theorem u293 (x : Nat → Bool) : (x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat = (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat := g0 _ _ _ _ _ _ 
theorem e293 (x : Nat → Bool) : (x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat = (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat := by
  have h := u293 x
  omega
def w_n879 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((x 397).toNat + 2 * (x 398).toNat + 4 * (x 399).toNat + 8 * (x 400).toNat + 16 * (x 401).toNat + 32 * (x 402).toNat)
def w_n880 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((x 397).toNat + 2 * (x 398).toNat + 4 * (x 399).toNat + 8 * (x 400).toNat + 16 * (x 401).toNat + 32 * (x 402).toNat)
def w_n881 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((x 397).toNat + 2 * (x 398).toNat + 4 * (x 399).toNat + 8 * (x 400).toNat + 16 * (x 401).toNat + 32 * (x 402).toNat)
theorem u294 (x : Nat → Bool) : (x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat = (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat := g0 _ _ _ _ _ _ 
theorem e294 (x : Nat → Bool) : (x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat = (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat := by
  have h := u294 x
  omega
def w_n882 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n858 x).toNat + 2 * (w_n861 x).toNat + 4 * (w_n864 x).toNat + 8 * (w_n867 x).toNat + 16 * (w_n870 x).toNat + 32 * (w_n873 x).toNat)
def w_n883 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n858 x).toNat + 2 * (w_n861 x).toNat + 4 * (w_n864 x).toNat + 8 * (w_n867 x).toNat + 16 * (w_n870 x).toNat + 32 * (w_n873 x).toNat)
def w_n884 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n858 x).toNat + 2 * (w_n861 x).toNat + 4 * (w_n864 x).toNat + 8 * (w_n867 x).toNat + 16 * (w_n870 x).toNat + 32 * (w_n873 x).toNat)
theorem u295 (x : Nat → Bool) : (w_n858 x).toNat + (w_n861 x).toNat + (w_n864 x).toNat + (w_n867 x).toNat + (w_n870 x).toNat + (w_n873 x).toNat = (w_n882 x).toNat + 2 * (w_n883 x).toNat + 4 * (w_n884 x).toNat := g0 _ _ _ _ _ _ 
theorem e295 (x : Nat → Bool) : (w_n858 x).toNat + (w_n861 x).toNat + (w_n864 x).toNat + (w_n867 x).toNat + (w_n870 x).toNat + (w_n873 x).toNat = (w_n882 x).toNat + 2 * (w_n883 x).toNat + 4 * (w_n884 x).toNat := by
  have h := u295 x
  omega
def w_n885 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n859 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n865 x).toNat + 8 * (w_n868 x).toNat + 16 * (w_n871 x).toNat + 32 * (w_n874 x).toNat)
def w_n886 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n859 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n865 x).toNat + 8 * (w_n868 x).toNat + 16 * (w_n871 x).toNat + 32 * (w_n874 x).toNat)
def w_n887 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n859 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n865 x).toNat + 8 * (w_n868 x).toNat + 16 * (w_n871 x).toNat + 32 * (w_n874 x).toNat)
theorem u296 (x : Nat → Bool) : (w_n859 x).toNat + (w_n862 x).toNat + (w_n865 x).toNat + (w_n868 x).toNat + (w_n871 x).toNat + (w_n874 x).toNat = (w_n885 x).toNat + 2 * (w_n886 x).toNat + 4 * (w_n887 x).toNat := g0 _ _ _ _ _ _ 
theorem e296 (x : Nat → Bool) : 2 * (w_n859 x).toNat + 2 * (w_n862 x).toNat + 2 * (w_n865 x).toNat + 2 * (w_n868 x).toNat + 2 * (w_n871 x).toNat + 2 * (w_n874 x).toNat = 2 * (w_n885 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n887 x).toNat := by
  have h := u296 x
  omega
def w_n888 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n860 x).toNat + 2 * (w_n863 x).toNat + 4 * (w_n866 x).toNat + 8 * (w_n869 x).toNat + 16 * (w_n872 x).toNat + 32 * (w_n875 x).toNat)
def w_n889 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n860 x).toNat + 2 * (w_n863 x).toNat + 4 * (w_n866 x).toNat + 8 * (w_n869 x).toNat + 16 * (w_n872 x).toNat + 32 * (w_n875 x).toNat)
def w_n890 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n860 x).toNat + 2 * (w_n863 x).toNat + 4 * (w_n866 x).toNat + 8 * (w_n869 x).toNat + 16 * (w_n872 x).toNat + 32 * (w_n875 x).toNat)
theorem u297 (x : Nat → Bool) : (w_n860 x).toNat + (w_n863 x).toNat + (w_n866 x).toNat + (w_n869 x).toNat + (w_n872 x).toNat + (w_n875 x).toNat = (w_n888 x).toNat + 2 * (w_n889 x).toNat + 4 * (w_n890 x).toNat := g0 _ _ _ _ _ _ 
theorem e297 (x : Nat → Bool) : 4 * (w_n860 x).toNat + 4 * (w_n863 x).toNat + 4 * (w_n866 x).toNat + 4 * (w_n869 x).toNat + 4 * (w_n872 x).toNat + 4 * (w_n875 x).toNat = 4 * (w_n888 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n890 x).toNat := by
  have h := u297 x
  omega
def w_n891 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n843 x).toNat + 2 * (w_n846 x).toNat + 4 * (w_n849 x).toNat + 8 * (w_n876 x).toNat + 16 * (w_n879 x).toNat + 32 * (w_n882 x).toNat)
def w_n892 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n843 x).toNat + 2 * (w_n846 x).toNat + 4 * (w_n849 x).toNat + 8 * (w_n876 x).toNat + 16 * (w_n879 x).toNat + 32 * (w_n882 x).toNat)
def w_n893 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n843 x).toNat + 2 * (w_n846 x).toNat + 4 * (w_n849 x).toNat + 8 * (w_n876 x).toNat + 16 * (w_n879 x).toNat + 32 * (w_n882 x).toNat)
theorem u298 (x : Nat → Bool) : (w_n843 x).toNat + (w_n846 x).toNat + (w_n849 x).toNat + (w_n876 x).toNat + (w_n879 x).toNat + (w_n882 x).toNat = (w_n891 x).toNat + 2 * (w_n892 x).toNat + 4 * (w_n893 x).toNat := g0 _ _ _ _ _ _ 
theorem e298 (x : Nat → Bool) : (w_n843 x).toNat + (w_n846 x).toNat + (w_n849 x).toNat + (w_n876 x).toNat + (w_n879 x).toNat + (w_n882 x).toNat = (w_n891 x).toNat + 2 * (w_n892 x).toNat + 4 * (w_n893 x).toNat := by
  have h := u298 x
  omega
def w_n894 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n844 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n850 x).toNat + 8 * (w_n852 x).toNat + 16 * (w_n877 x).toNat + 32 * (w_n880 x).toNat)
def w_n895 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n844 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n850 x).toNat + 8 * (w_n852 x).toNat + 16 * (w_n877 x).toNat + 32 * (w_n880 x).toNat)
def w_n896 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n844 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n850 x).toNat + 8 * (w_n852 x).toNat + 16 * (w_n877 x).toNat + 32 * (w_n880 x).toNat)
theorem u299 (x : Nat → Bool) : (w_n844 x).toNat + (w_n847 x).toNat + (w_n850 x).toNat + (w_n852 x).toNat + (w_n877 x).toNat + (w_n880 x).toNat = (w_n894 x).toNat + 2 * (w_n895 x).toNat + 4 * (w_n896 x).toNat := g0 _ _ _ _ _ _ 
theorem e299 (x : Nat → Bool) : 2 * (w_n844 x).toNat + 2 * (w_n847 x).toNat + 2 * (w_n850 x).toNat + 2 * (w_n852 x).toNat + 2 * (w_n877 x).toNat + 2 * (w_n880 x).toNat = 2 * (w_n894 x).toNat + 4 * (w_n895 x).toNat + 8 * (w_n896 x).toNat := by
  have h := u299 x
  omega
def w_n897 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n845 x).toNat + 2 * (w_n848 x).toNat + 4 * (w_n851 x).toNat + 8 * (w_n853 x).toNat + 16 * (w_n855 x).toNat + 32 * (w_n878 x).toNat)
def w_n898 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n845 x).toNat + 2 * (w_n848 x).toNat + 4 * (w_n851 x).toNat + 8 * (w_n853 x).toNat + 16 * (w_n855 x).toNat + 32 * (w_n878 x).toNat)
def w_n899 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n845 x).toNat + 2 * (w_n848 x).toNat + 4 * (w_n851 x).toNat + 8 * (w_n853 x).toNat + 16 * (w_n855 x).toNat + 32 * (w_n878 x).toNat)
theorem u300 (x : Nat → Bool) : (w_n845 x).toNat + (w_n848 x).toNat + (w_n851 x).toNat + (w_n853 x).toNat + (w_n855 x).toNat + (w_n878 x).toNat = (w_n897 x).toNat + 2 * (w_n898 x).toNat + 4 * (w_n899 x).toNat := g0 _ _ _ _ _ _ 
theorem e300 (x : Nat → Bool) : 4 * (w_n845 x).toNat + 4 * (w_n848 x).toNat + 4 * (w_n851 x).toNat + 4 * (w_n853 x).toNat + 4 * (w_n855 x).toNat + 4 * (w_n878 x).toNat = 4 * (w_n897 x).toNat + 8 * (w_n898 x).toNat + 16 * (w_n899 x).toNat := by
  have h := u300 x
  omega
def w_n900 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n881 x).toNat + 2 * (w_n884 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n888 x).toNat + 16 * (w_n893 x).toNat + 32 * (w_n895 x).toNat)
def w_n901 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n881 x).toNat + 2 * (w_n884 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n888 x).toNat + 16 * (w_n893 x).toNat + 32 * (w_n895 x).toNat)
def w_n902 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n881 x).toNat + 2 * (w_n884 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n888 x).toNat + 16 * (w_n893 x).toNat + 32 * (w_n895 x).toNat)
theorem u301 (x : Nat → Bool) : (w_n881 x).toNat + (w_n884 x).toNat + (w_n886 x).toNat + (w_n888 x).toNat + (w_n893 x).toNat + (w_n895 x).toNat = (w_n900 x).toNat + 2 * (w_n901 x).toNat + 4 * (w_n902 x).toNat := g0 _ _ _ _ _ _ 
theorem e301 (x : Nat → Bool) : 4 * (w_n881 x).toNat + 4 * (w_n884 x).toNat + 4 * (w_n886 x).toNat + 4 * (w_n888 x).toNat + 4 * (w_n893 x).toNat + 4 * (w_n895 x).toNat = 4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat := by
  have h := u301 x
  omega
def w_n903 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n854 x).toNat + 2 * (w_n856 x).toNat + 4 * (w_n887 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n896 x).toNat + 32 * (w_n898 x).toNat)
def w_n904 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n854 x).toNat + 2 * (w_n856 x).toNat + 4 * (w_n887 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n896 x).toNat + 32 * (w_n898 x).toNat)
def w_n905 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n854 x).toNat + 2 * (w_n856 x).toNat + 4 * (w_n887 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n896 x).toNat + 32 * (w_n898 x).toNat)
theorem u302 (x : Nat → Bool) : (w_n854 x).toNat + (w_n856 x).toNat + (w_n887 x).toNat + (w_n889 x).toNat + (w_n896 x).toNat + (w_n898 x).toNat = (w_n903 x).toNat + 2 * (w_n904 x).toNat + 4 * (w_n905 x).toNat := g0 _ _ _ _ _ _ 
theorem e302 (x : Nat → Bool) : 8 * (w_n854 x).toNat + 8 * (w_n856 x).toNat + 8 * (w_n887 x).toNat + 8 * (w_n889 x).toNat + 8 * (w_n896 x).toNat + 8 * (w_n898 x).toNat = 8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat := by
  have h := u302 x
  omega
def w_n906 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n802 x).toNat + 2 * (w_n804 x).toNat + 4 * (w_n811 x).toNat + 8 * (w_n813 x).toNat + 16 * (w_n883 x).toNat + 32 * (w_n885 x).toNat)
def w_n907 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n802 x).toNat + 2 * (w_n804 x).toNat + 4 * (w_n811 x).toNat + 8 * (w_n813 x).toNat + 16 * (w_n883 x).toNat + 32 * (w_n885 x).toNat)
def w_n908 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n802 x).toNat + 2 * (w_n804 x).toNat + 4 * (w_n811 x).toNat + 8 * (w_n813 x).toNat + 16 * (w_n883 x).toNat + 32 * (w_n885 x).toNat)
theorem u303 (x : Nat → Bool) : (w_n802 x).toNat + (w_n804 x).toNat + (w_n811 x).toNat + (w_n813 x).toNat + (w_n883 x).toNat + (w_n885 x).toNat = (w_n906 x).toNat + 2 * (w_n907 x).toNat + 4 * (w_n908 x).toNat := g0 _ _ _ _ _ _ 
theorem e303 (x : Nat → Bool) : 2 * (w_n802 x).toNat + 2 * (w_n804 x).toNat + 2 * (w_n811 x).toNat + 2 * (w_n813 x).toNat + 2 * (w_n883 x).toNat + 2 * (w_n885 x).toNat = 2 * (w_n906 x).toNat + 4 * (w_n907 x).toNat + 8 * (w_n908 x).toNat := by
  have h := u303 x
  omega
def w_n909 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n776 x).toNat + 2 * (w_n809 x).toNat + 4 * (w_n818 x).toNat + 8 * (w_n821 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n857 x).toNat)
def w_n910 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n776 x).toNat + 2 * (w_n809 x).toNat + 4 * (w_n818 x).toNat + 8 * (w_n821 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n857 x).toNat)
def w_n911 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n776 x).toNat + 2 * (w_n809 x).toNat + 4 * (w_n818 x).toNat + 8 * (w_n821 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n857 x).toNat)
theorem u304 (x : Nat → Bool) : (w_n776 x).toNat + (w_n809 x).toNat + (w_n818 x).toNat + (w_n821 x).toNat + (w_n823 x).toNat + (w_n857 x).toNat = (w_n909 x).toNat + 2 * (w_n910 x).toNat + 4 * (w_n911 x).toNat := g0 _ _ _ _ _ _ 
theorem e304 (x : Nat → Bool) : 16 * (w_n776 x).toNat + 16 * (w_n809 x).toNat + 16 * (w_n818 x).toNat + 16 * (w_n821 x).toNat + 16 * (w_n823 x).toNat + 16 * (w_n857 x).toNat = 16 * (w_n909 x).toNat + 32 * (w_n910 x).toNat + 64 * (w_n911 x).toNat := by
  have h := u304 x
  omega
def w_n912 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n738 x).toNat + 8 * (w_n892 x).toNat + 16 * (w_n894 x).toNat + 32 * (w_n906 x).toNat)
def w_n913 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n738 x).toNat + 8 * (w_n892 x).toNat + 16 * (w_n894 x).toNat + 32 * (w_n906 x).toNat)
def w_n914 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n738 x).toNat + 8 * (w_n892 x).toNat + 16 * (w_n894 x).toNat + 32 * (w_n906 x).toNat)
theorem u305 (x : Nat → Bool) : (w_n724 x).toNat + (w_n726 x).toNat + (w_n738 x).toNat + (w_n892 x).toNat + (w_n894 x).toNat + (w_n906 x).toNat = (w_n912 x).toNat + 2 * (w_n913 x).toNat + 4 * (w_n914 x).toNat := g0 _ _ _ _ _ _ 
theorem e305 (x : Nat → Bool) : 2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 2 * (w_n738 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 2 * (w_n906 x).toNat = 2 * (w_n912 x).toNat + 4 * (w_n913 x).toNat + 8 * (w_n914 x).toNat := by
  have h := u305 x
  omega
def w_n915 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n648 x).toNat + 2 * (w_n651 x).toNat + 4 * (w_n729 x).toNat + 8 * (w_n732 x).toNat + 16 * (w_n739 x).toNat + 32 * (w_n816 x).toNat)
def w_n916 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n648 x).toNat + 2 * (w_n651 x).toNat + 4 * (w_n729 x).toNat + 8 * (w_n732 x).toNat + 16 * (w_n739 x).toNat + 32 * (w_n816 x).toNat)
def w_n917 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n648 x).toNat + 2 * (w_n651 x).toNat + 4 * (w_n729 x).toNat + 8 * (w_n732 x).toNat + 16 * (w_n739 x).toNat + 32 * (w_n816 x).toNat)
theorem u306 (x : Nat → Bool) : (w_n648 x).toNat + (w_n651 x).toNat + (w_n729 x).toNat + (w_n732 x).toNat + (w_n739 x).toNat + (w_n816 x).toNat = (w_n915 x).toNat + 2 * (w_n916 x).toNat + 4 * (w_n917 x).toNat := g0 _ _ _ _ _ _ 
theorem e306 (x : Nat → Bool) : 4 * (w_n648 x).toNat + 4 * (w_n651 x).toNat + 4 * (w_n729 x).toNat + 4 * (w_n732 x).toNat + 4 * (w_n739 x).toNat + 4 * (w_n816 x).toNat = 4 * (w_n915 x).toNat + 8 * (w_n916 x).toNat + 16 * (w_n917 x).toNat := by
  have h := u306 x
  omega
def w_n918 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n819 x).toNat + 2 * (w_n897 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n907 x).toNat + 16 * (w_n913 x).toNat + 32 * (w_n915 x).toNat)
def w_n919 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n819 x).toNat + 2 * (w_n897 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n907 x).toNat + 16 * (w_n913 x).toNat + 32 * (w_n915 x).toNat)
def w_n920 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n819 x).toNat + 2 * (w_n897 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n907 x).toNat + 16 * (w_n913 x).toNat + 32 * (w_n915 x).toNat)
theorem u307 (x : Nat → Bool) : (w_n819 x).toNat + (w_n897 x).toNat + (w_n900 x).toNat + (w_n907 x).toNat + (w_n913 x).toNat + (w_n915 x).toNat = (w_n918 x).toNat + 2 * (w_n919 x).toNat + 4 * (w_n920 x).toNat := g0 _ _ _ _ _ _ 
theorem e307 (x : Nat → Bool) : 4 * (w_n819 x).toNat + 4 * (w_n897 x).toNat + 4 * (w_n900 x).toNat + 4 * (w_n907 x).toNat + 4 * (w_n913 x).toNat + 4 * (w_n915 x).toNat = 4 * (w_n918 x).toNat + 8 * (w_n919 x).toNat + 16 * (w_n920 x).toNat := by
  have h := u307 x
  omega
def w_n921 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n652 x).toNat + 2 * (w_n654 x).toNat + 4 * (w_n733 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n740 x).toNat + 32 * (w_n820 x).toNat)
def w_n922 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n652 x).toNat + 2 * (w_n654 x).toNat + 4 * (w_n733 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n740 x).toNat + 32 * (w_n820 x).toNat)
def w_n923 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n652 x).toNat + 2 * (w_n654 x).toNat + 4 * (w_n733 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n740 x).toNat + 32 * (w_n820 x).toNat)
theorem u308 (x : Nat → Bool) : (w_n652 x).toNat + (w_n654 x).toNat + (w_n733 x).toNat + (w_n735 x).toNat + (w_n740 x).toNat + (w_n820 x).toNat = (w_n921 x).toNat + 2 * (w_n922 x).toNat + 4 * (w_n923 x).toNat := g0 _ _ _ _ _ _ 
theorem e308 (x : Nat → Bool) : 8 * (w_n652 x).toNat + 8 * (w_n654 x).toNat + 8 * (w_n733 x).toNat + 8 * (w_n735 x).toNat + 8 * (w_n740 x).toNat + 8 * (w_n820 x).toNat = 8 * (w_n921 x).toNat + 16 * (w_n922 x).toNat + 32 * (w_n923 x).toNat := by
  have h := u308 x
  omega
def w_n924 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n822 x).toNat + 2 * (w_n901 x).toNat + 4 * (w_n903 x).toNat + 8 * (w_n908 x).toNat + 16 * (w_n914 x).toNat + 32 * (w_n916 x).toNat)
def w_n925 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n822 x).toNat + 2 * (w_n901 x).toNat + 4 * (w_n903 x).toNat + 8 * (w_n908 x).toNat + 16 * (w_n914 x).toNat + 32 * (w_n916 x).toNat)
def w_n926 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n822 x).toNat + 2 * (w_n901 x).toNat + 4 * (w_n903 x).toNat + 8 * (w_n908 x).toNat + 16 * (w_n914 x).toNat + 32 * (w_n916 x).toNat)
theorem u309 (x : Nat → Bool) : (w_n822 x).toNat + (w_n901 x).toNat + (w_n903 x).toNat + (w_n908 x).toNat + (w_n914 x).toNat + (w_n916 x).toNat = (w_n924 x).toNat + 2 * (w_n925 x).toNat + 4 * (w_n926 x).toNat := g0 _ _ _ _ _ _ 
theorem e309 (x : Nat → Bool) : 8 * (w_n822 x).toNat + 8 * (w_n901 x).toNat + 8 * (w_n903 x).toNat + 8 * (w_n908 x).toNat + 8 * (w_n914 x).toNat + 8 * (w_n916 x).toNat = 8 * (w_n924 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n926 x).toNat := by
  have h := u309 x
  omega
def w_n927 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n722 x).toNat + 2 * (w_n731 x).toNat + 4 * (w_n734 x).toNat + 8 * (w_n736 x).toNat + 16 * (w_n741 x).toNat + 32 * (w_n890 x).toNat)
def w_n928 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n722 x).toNat + 2 * (w_n731 x).toNat + 4 * (w_n734 x).toNat + 8 * (w_n736 x).toNat + 16 * (w_n741 x).toNat + 32 * (w_n890 x).toNat)
def w_n929 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n722 x).toNat + 2 * (w_n731 x).toNat + 4 * (w_n734 x).toNat + 8 * (w_n736 x).toNat + 16 * (w_n741 x).toNat + 32 * (w_n890 x).toNat)
theorem u310 (x : Nat → Bool) : (w_n722 x).toNat + (w_n731 x).toNat + (w_n734 x).toNat + (w_n736 x).toNat + (w_n741 x).toNat + (w_n890 x).toNat = (w_n927 x).toNat + 2 * (w_n928 x).toNat + 4 * (w_n929 x).toNat := g0 _ _ _ _ _ _ 
theorem e310 (x : Nat → Bool) : 16 * (w_n722 x).toNat + 16 * (w_n731 x).toNat + 16 * (w_n734 x).toNat + 16 * (w_n736 x).toNat + 16 * (w_n741 x).toNat + 16 * (w_n890 x).toNat = 16 * (w_n927 x).toNat + 32 * (w_n928 x).toNat + 64 * (w_n929 x).toNat := by
  have h := u310 x
  omega
def w_n930 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n899 x).toNat + 2 * (w_n902 x).toNat + 4 * (w_n904 x).toNat + 8 * (w_n909 x).toNat + 16 * (w_n917 x).toNat + 32 * (w_n920 x).toNat)
def w_n931 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n899 x).toNat + 2 * (w_n902 x).toNat + 4 * (w_n904 x).toNat + 8 * (w_n909 x).toNat + 16 * (w_n917 x).toNat + 32 * (w_n920 x).toNat)
def w_n932 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n899 x).toNat + 2 * (w_n902 x).toNat + 4 * (w_n904 x).toNat + 8 * (w_n909 x).toNat + 16 * (w_n917 x).toNat + 32 * (w_n920 x).toNat)
theorem u311 (x : Nat → Bool) : (w_n899 x).toNat + (w_n902 x).toNat + (w_n904 x).toNat + (w_n909 x).toNat + (w_n917 x).toNat + (w_n920 x).toNat = (w_n930 x).toNat + 2 * (w_n931 x).toNat + 4 * (w_n932 x).toNat := g0 _ _ _ _ _ _ 
theorem e311 (x : Nat → Bool) : 16 * (w_n899 x).toNat + 16 * (w_n902 x).toNat + 16 * (w_n904 x).toNat + 16 * (w_n909 x).toNat + 16 * (w_n917 x).toNat + 16 * (w_n920 x).toNat = 16 * (w_n930 x).toNat + 32 * (w_n931 x).toNat + 64 * (w_n932 x).toNat := by
  have h := u311 x
  omega
def w_n933 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n656 x).toNat + 2 * (w_n737 x).toNat + 4 * (w_n742 x).toNat + 8 * (w_n824 x).toNat + 16 * (w_n905 x).toNat + 32 * (w_n910 x).toNat)
def w_n934 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n656 x).toNat + 2 * (w_n737 x).toNat + 4 * (w_n742 x).toNat + 8 * (w_n824 x).toNat + 16 * (w_n905 x).toNat + 32 * (w_n910 x).toNat)
def w_n935 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n656 x).toNat + 2 * (w_n737 x).toNat + 4 * (w_n742 x).toNat + 8 * (w_n824 x).toNat + 16 * (w_n905 x).toNat + 32 * (w_n910 x).toNat)
theorem u312 (x : Nat → Bool) : (w_n656 x).toNat + (w_n737 x).toNat + (w_n742 x).toNat + (w_n824 x).toNat + (w_n905 x).toNat + (w_n910 x).toNat = (w_n933 x).toNat + 2 * (w_n934 x).toNat + 4 * (w_n935 x).toNat := g0 _ _ _ _ _ _ 
theorem e312 (x : Nat → Bool) : 32 * (w_n656 x).toNat + 32 * (w_n737 x).toNat + 32 * (w_n742 x).toNat + 32 * (w_n824 x).toNat + 32 * (w_n905 x).toNat + 32 * (w_n910 x).toNat = 32 * (w_n933 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat := by
  have h := u312 x
  omega
def w_n936 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n427 x).toNat + 2 * (w_n531 x).toNat + 4 * (w_n534 x).toNat + 8 * (w_n552 x).toNat + 16 * (w_n642 x).toNat + 32 * (w_n723 x).toNat)
def w_n937 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n427 x).toNat + 2 * (w_n531 x).toNat + 4 * (w_n534 x).toNat + 8 * (w_n552 x).toNat + 16 * (w_n642 x).toNat + 32 * (w_n723 x).toNat)
def w_n938 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n427 x).toNat + 2 * (w_n531 x).toNat + 4 * (w_n534 x).toNat + 8 * (w_n552 x).toNat + 16 * (w_n642 x).toNat + 32 * (w_n723 x).toNat)
theorem u313 (x : Nat → Bool) : (w_n427 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + (w_n552 x).toNat + (w_n642 x).toNat + (w_n723 x).toNat = (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n938 x).toNat := g0 _ _ _ _ _ _ 
theorem e313 (x : Nat → Bool) : (w_n427 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + (w_n552 x).toNat + (w_n642 x).toNat + (w_n723 x).toNat = (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n938 x).toNat := by
  have h := u313 x
  omega
def w_n939 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n433 x).toNat + 2 * (w_n436 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n571 x).toNat + 16 * (w_n918 x).toNat + 32 * (w_n938 x).toNat)
def w_n940 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n433 x).toNat + 2 * (w_n436 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n571 x).toNat + 16 * (w_n918 x).toNat + 32 * (w_n938 x).toNat)
def w_n941 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n433 x).toNat + 2 * (w_n436 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n571 x).toNat + 16 * (w_n918 x).toNat + 32 * (w_n938 x).toNat)
theorem u314 (x : Nat → Bool) : (w_n433 x).toNat + (w_n436 x).toNat + (w_n561 x).toNat + (w_n571 x).toNat + (w_n918 x).toNat + (w_n938 x).toNat = (w_n939 x).toNat + 2 * (w_n940 x).toNat + 4 * (w_n941 x).toNat := g0 _ _ _ _ _ _ 
theorem e314 (x : Nat → Bool) : 4 * (w_n433 x).toNat + 4 * (w_n436 x).toNat + 4 * (w_n561 x).toNat + 4 * (w_n571 x).toNat + 4 * (w_n918 x).toNat + 4 * (w_n938 x).toNat = 4 * (w_n939 x).toNat + 8 * (w_n940 x).toNat + 16 * (w_n941 x).toNat := by
  have h := u314 x
  omega
def w_n942 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n437 x).toNat + 2 * (w_n439 x).toNat + 4 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n572 x).toNat + 32 * (w_n919 x).toNat)
def w_n943 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n437 x).toNat + 2 * (w_n439 x).toNat + 4 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n572 x).toNat + 32 * (w_n919 x).toNat)
def w_n944 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n437 x).toNat + 2 * (w_n439 x).toNat + 4 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n572 x).toNat + 32 * (w_n919 x).toNat)
theorem u315 (x : Nat → Bool) : (w_n437 x).toNat + (w_n439 x).toNat + (w_n562 x).toNat + (w_n564 x).toNat + (w_n572 x).toNat + (w_n919 x).toNat = (w_n942 x).toNat + 2 * (w_n943 x).toNat + 4 * (w_n944 x).toNat := g0 _ _ _ _ _ _ 
theorem e315 (x : Nat → Bool) : 8 * (w_n437 x).toNat + 8 * (w_n439 x).toNat + 8 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 8 * (w_n572 x).toNat + 8 * (w_n919 x).toNat = 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 32 * (w_n944 x).toNat := by
  have h := u315 x
  omega
def w_n945 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n565 x).toNat + 2 * (w_n567 x).toNat + 4 * (w_n573 x).toNat + 8 * (w_n922 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n927 x).toNat)
def w_n946 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n565 x).toNat + 2 * (w_n567 x).toNat + 4 * (w_n573 x).toNat + 8 * (w_n922 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n927 x).toNat)
def w_n947 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n565 x).toNat + 2 * (w_n567 x).toNat + 4 * (w_n573 x).toNat + 8 * (w_n922 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n927 x).toNat)
theorem u316 (x : Nat → Bool) : (w_n565 x).toNat + (w_n567 x).toNat + (w_n573 x).toNat + (w_n922 x).toNat + (w_n925 x).toNat + (w_n927 x).toNat = (w_n945 x).toNat + 2 * (w_n946 x).toNat + 4 * (w_n947 x).toNat := g0 _ _ _ _ _ _ 
theorem e316 (x : Nat → Bool) : 16 * (w_n565 x).toNat + 16 * (w_n567 x).toNat + 16 * (w_n573 x).toNat + 16 * (w_n922 x).toNat + 16 * (w_n925 x).toNat + 16 * (w_n927 x).toNat = 16 * (w_n945 x).toNat + 32 * (w_n946 x).toNat + 64 * (w_n947 x).toNat := by
  have h := u316 x
  omega
def w_n948 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n441 x).toNat + 2 * (w_n551 x).toNat + 4 * (w_n566 x).toNat + 8 * (w_n568 x).toNat + 16 * (w_n574 x).toNat + 32 * (w_n923 x).toNat)
def w_n949 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n441 x).toNat + 2 * (w_n551 x).toNat + 4 * (w_n566 x).toNat + 8 * (w_n568 x).toNat + 16 * (w_n574 x).toNat + 32 * (w_n923 x).toNat)
def w_n950 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n441 x).toNat + 2 * (w_n551 x).toNat + 4 * (w_n566 x).toNat + 8 * (w_n568 x).toNat + 16 * (w_n574 x).toNat + 32 * (w_n923 x).toNat)
theorem u317 (x : Nat → Bool) : (w_n441 x).toNat + (w_n551 x).toNat + (w_n566 x).toNat + (w_n568 x).toNat + (w_n574 x).toNat + (w_n923 x).toNat = (w_n948 x).toNat + 2 * (w_n949 x).toNat + 4 * (w_n950 x).toNat := g0 _ _ _ _ _ _ 
theorem e317 (x : Nat → Bool) : 32 * (w_n441 x).toNat + 32 * (w_n551 x).toNat + 32 * (w_n566 x).toNat + 32 * (w_n568 x).toNat + 32 * (w_n574 x).toNat + 32 * (w_n923 x).toNat = 32 * (w_n948 x).toNat + 64 * (w_n949 x).toNat + 128 * (w_n950 x).toNat := by
  have h := u317 x
  omega
def w_n951 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n926 x).toNat + 2 * (w_n928 x).toNat + 4 * (w_n931 x).toNat + 8 * (w_n933 x).toNat + 16 * (w_n944 x).toNat + 32 * (w_n946 x).toNat)
def w_n952 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n926 x).toNat + 2 * (w_n928 x).toNat + 4 * (w_n931 x).toNat + 8 * (w_n933 x).toNat + 16 * (w_n944 x).toNat + 32 * (w_n946 x).toNat)
def w_n953 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n926 x).toNat + 2 * (w_n928 x).toNat + 4 * (w_n931 x).toNat + 8 * (w_n933 x).toNat + 16 * (w_n944 x).toNat + 32 * (w_n946 x).toNat)
theorem u318 (x : Nat → Bool) : (w_n926 x).toNat + (w_n928 x).toNat + (w_n931 x).toNat + (w_n933 x).toNat + (w_n944 x).toNat + (w_n946 x).toNat = (w_n951 x).toNat + 2 * (w_n952 x).toNat + 4 * (w_n953 x).toNat := g0 _ _ _ _ _ _ 
theorem e318 (x : Nat → Bool) : 32 * (w_n926 x).toNat + 32 * (w_n928 x).toNat + 32 * (w_n931 x).toNat + 32 * (w_n933 x).toNat + 32 * (w_n944 x).toNat + 32 * (w_n946 x).toNat = 32 * (w_n951 x).toNat + 64 * (w_n952 x).toNat + 128 * (w_n953 x).toNat := by
  have h := u318 x
  omega
def w_n954 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n569 x).toNat + 2 * (w_n575 x).toNat + 4 * (w_n743 x).toNat + 8 * (w_n911 x).toNat + 16 * (w_n929 x).toNat + 32 * (w_n932 x).toNat)
def w_n955 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n569 x).toNat + 2 * (w_n575 x).toNat + 4 * (w_n743 x).toNat + 8 * (w_n911 x).toNat + 16 * (w_n929 x).toNat + 32 * (w_n932 x).toNat)
def w_n956 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n569 x).toNat + 2 * (w_n575 x).toNat + 4 * (w_n743 x).toNat + 8 * (w_n911 x).toNat + 16 * (w_n929 x).toNat + 32 * (w_n932 x).toNat)
theorem u319 (x : Nat → Bool) : (w_n569 x).toNat + (w_n575 x).toNat + (w_n743 x).toNat + (w_n911 x).toNat + (w_n929 x).toNat + (w_n932 x).toNat = (w_n954 x).toNat + 2 * (w_n955 x).toNat + 4 * (w_n956 x).toNat := g0 _ _ _ _ _ _ 
theorem e319 (x : Nat → Bool) : 64 * (w_n569 x).toNat + 64 * (w_n575 x).toNat + 64 * (w_n743 x).toNat + 64 * (w_n911 x).toNat + 64 * (w_n929 x).toNat + 64 * (w_n932 x).toNat = 64 * (w_n954 x).toNat + 128 * (w_n955 x).toNat + 256 * (w_n956 x).toNat := by
  have h := u319 x
  omega
def w_n957 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n67 x).toNat + 2 * (w_n148 x).toNat + 4 * (w_n235 x).toNat + 8 * (w_n316 x).toNat + 16 * (w_n810 x).toNat + 32 * (w_n891 x).toNat)
def w_n958 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n67 x).toNat + 2 * (w_n148 x).toNat + 4 * (w_n235 x).toNat + 8 * (w_n316 x).toNat + 16 * (w_n810 x).toNat + 32 * (w_n891 x).toNat)
def w_n959 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n67 x).toNat + 2 * (w_n148 x).toNat + 4 * (w_n235 x).toNat + 8 * (w_n316 x).toNat + 16 * (w_n810 x).toNat + 32 * (w_n891 x).toNat)
theorem u320 (x : Nat → Bool) : (w_n67 x).toNat + (w_n148 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat = (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat := g0 _ _ _ _ _ _ 
theorem e320 (x : Nat → Bool) : (w_n67 x).toNat + (w_n148 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat = (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat := by
  have h := u320 x
  omega
def w_n960 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n344 x).toNat + 2 * (w_n346 x).toNat + 4 * (w_n349 x).toNat + 8 * (w_n921 x).toNat + 16 * (w_n924 x).toNat + 32 * (w_n940 x).toNat)
def w_n961 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n344 x).toNat + 2 * (w_n346 x).toNat + 4 * (w_n349 x).toNat + 8 * (w_n921 x).toNat + 16 * (w_n924 x).toNat + 32 * (w_n940 x).toNat)
def w_n962 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n344 x).toNat + 2 * (w_n346 x).toNat + 4 * (w_n349 x).toNat + 8 * (w_n921 x).toNat + 16 * (w_n924 x).toNat + 32 * (w_n940 x).toNat)
theorem u321 (x : Nat → Bool) : (w_n344 x).toNat + (w_n346 x).toNat + (w_n349 x).toNat + (w_n921 x).toNat + (w_n924 x).toNat + (w_n940 x).toNat = (w_n960 x).toNat + 2 * (w_n961 x).toNat + 4 * (w_n962 x).toNat := g0 _ _ _ _ _ _ 
theorem e321 (x : Nat → Bool) : 8 * (w_n344 x).toNat + 8 * (w_n346 x).toNat + 8 * (w_n349 x).toNat + 8 * (w_n921 x).toNat + 8 * (w_n924 x).toNat + 8 * (w_n940 x).toNat = 8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat := by
  have h := u321 x
  omega
def w_n963 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n347 x).toNat + 2 * (w_n350 x).toNat + 4 * (w_n352 x).toNat + 8 * (w_n355 x).toNat + 16 * (w_n930 x).toNat + 32 * (w_n941 x).toNat)
def w_n964 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n347 x).toNat + 2 * (w_n350 x).toNat + 4 * (w_n352 x).toNat + 8 * (w_n355 x).toNat + 16 * (w_n930 x).toNat + 32 * (w_n941 x).toNat)
def w_n965 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n347 x).toNat + 2 * (w_n350 x).toNat + 4 * (w_n352 x).toNat + 8 * (w_n355 x).toNat + 16 * (w_n930 x).toNat + 32 * (w_n941 x).toNat)
theorem u322 (x : Nat → Bool) : (w_n347 x).toNat + (w_n350 x).toNat + (w_n352 x).toNat + (w_n355 x).toNat + (w_n930 x).toNat + (w_n941 x).toNat = (w_n963 x).toNat + 2 * (w_n964 x).toNat + 4 * (w_n965 x).toNat := g0 _ _ _ _ _ _ 
theorem e322 (x : Nat → Bool) : 16 * (w_n347 x).toNat + 16 * (w_n350 x).toNat + 16 * (w_n352 x).toNat + 16 * (w_n355 x).toNat + 16 * (w_n930 x).toNat + 16 * (w_n941 x).toNat = 16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 64 * (w_n965 x).toNat := by
  have h := u322 x
  omega
def w_n966 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n348 x).toNat + 2 * (w_n351 x).toNat + 4 * (w_n353 x).toNat + 8 * (w_n356 x).toNat + 16 * (w_n358 x).toNat + 32 * (w_n948 x).toNat)
def w_n967 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n348 x).toNat + 2 * (w_n351 x).toNat + 4 * (w_n353 x).toNat + 8 * (w_n356 x).toNat + 16 * (w_n358 x).toNat + 32 * (w_n948 x).toNat)
def w_n968 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n348 x).toNat + 2 * (w_n351 x).toNat + 4 * (w_n353 x).toNat + 8 * (w_n356 x).toNat + 16 * (w_n358 x).toNat + 32 * (w_n948 x).toNat)
theorem u323 (x : Nat → Bool) : (w_n348 x).toNat + (w_n351 x).toNat + (w_n353 x).toNat + (w_n356 x).toNat + (w_n358 x).toNat + (w_n948 x).toNat = (w_n966 x).toNat + 2 * (w_n967 x).toNat + 4 * (w_n968 x).toNat := g0 _ _ _ _ _ _ 
theorem e323 (x : Nat → Bool) : 32 * (w_n348 x).toNat + 32 * (w_n351 x).toNat + 32 * (w_n353 x).toNat + 32 * (w_n356 x).toNat + 32 * (w_n358 x).toNat + 32 * (w_n948 x).toNat = 32 * (w_n966 x).toNat + 64 * (w_n967 x).toNat + 128 * (w_n968 x).toNat := by
  have h := u323 x
  omega
def w_n969 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n168 x).toNat + 2 * (w_n336 x).toNat + 4 * (w_n354 x).toNat + 8 * (w_n357 x).toNat + 16 * (w_n359 x).toNat + 32 * (w_n934 x).toNat)
def w_n970 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n168 x).toNat + 2 * (w_n336 x).toNat + 4 * (w_n354 x).toNat + 8 * (w_n357 x).toNat + 16 * (w_n359 x).toNat + 32 * (w_n934 x).toNat)
def w_n971 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n168 x).toNat + 2 * (w_n336 x).toNat + 4 * (w_n354 x).toNat + 8 * (w_n357 x).toNat + 16 * (w_n359 x).toNat + 32 * (w_n934 x).toNat)
theorem u324 (x : Nat → Bool) : (w_n168 x).toNat + (w_n336 x).toNat + (w_n354 x).toNat + (w_n357 x).toNat + (w_n359 x).toNat + (w_n934 x).toNat = (w_n969 x).toNat + 2 * (w_n970 x).toNat + 4 * (w_n971 x).toNat := g0 _ _ _ _ _ _ 
theorem e324 (x : Nat → Bool) : 64 * (w_n168 x).toNat + 64 * (w_n336 x).toNat + 64 * (w_n354 x).toNat + 64 * (w_n357 x).toNat + 64 * (w_n359 x).toNat + 64 * (w_n934 x).toNat = 64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat := by
  have h := u324 x
  omega
def w_n972 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n947 x).toNat + 2 * (w_n949 x).toNat + 4 * (w_n952 x).toNat + 8 * (w_n954 x).toNat + 16 * (w_n965 x).toNat + 32 * (w_n967 x).toNat)
def w_n973 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n947 x).toNat + 2 * (w_n949 x).toNat + 4 * (w_n952 x).toNat + 8 * (w_n954 x).toNat + 16 * (w_n965 x).toNat + 32 * (w_n967 x).toNat)
def w_n974 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n947 x).toNat + 2 * (w_n949 x).toNat + 4 * (w_n952 x).toNat + 8 * (w_n954 x).toNat + 16 * (w_n965 x).toNat + 32 * (w_n967 x).toNat)
theorem u325 (x : Nat → Bool) : (w_n947 x).toNat + (w_n949 x).toNat + (w_n952 x).toNat + (w_n954 x).toNat + (w_n965 x).toNat + (w_n967 x).toNat = (w_n972 x).toNat + 2 * (w_n973 x).toNat + 4 * (w_n974 x).toNat := g0 _ _ _ _ _ _ 
theorem e325 (x : Nat → Bool) : 64 * (w_n947 x).toNat + 64 * (w_n949 x).toNat + 64 * (w_n952 x).toNat + 64 * (w_n954 x).toNat + 64 * (w_n965 x).toNat + 64 * (w_n967 x).toNat = 64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat := by
  have h := u325 x
  omega
def w_n975 (x : Nat → Bool) : Bool := lut 7608434000728254870 ((w_n360 x).toNat + 2 * (w_n935 x).toNat + 4 * (w_n950 x).toNat + 8 * (w_n953 x).toNat + 16 * (w_n955 x).toNat + 32 * (w_n968 x).toNat)
def w_n976 (x : Nat → Bool) : Bool := lut 9301929385684532968 ((w_n360 x).toNat + 2 * (w_n935 x).toNat + 4 * (w_n950 x).toNat + 8 * (w_n953 x).toNat + 16 * (w_n955 x).toNat + 32 * (w_n968 x).toNat)
def w_n977 (x : Nat → Bool) : Bool := lut 18368186720584761344 ((w_n360 x).toNat + 2 * (w_n935 x).toNat + 4 * (w_n950 x).toNat + 8 * (w_n953 x).toNat + 16 * (w_n955 x).toNat + 32 * (w_n968 x).toNat)
theorem u326 (x : Nat → Bool) : (w_n360 x).toNat + (w_n935 x).toNat + (w_n950 x).toNat + (w_n953 x).toNat + (w_n955 x).toNat + (w_n968 x).toNat = (w_n975 x).toNat + 2 * (w_n976 x).toNat + 4 * (w_n977 x).toNat := g0 _ _ _ _ _ _ 
theorem e326 (x : Nat → Bool) : 128 * (w_n360 x).toNat + 128 * (w_n935 x).toNat + 128 * (w_n950 x).toNat + 128 * (w_n953 x).toNat + 128 * (w_n955 x).toNat + 128 * (w_n968 x).toNat = 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat := by
  have h := u326 x
  omega
theorem g3 (a b c : Bool) : a.toNat + b.toNat + c.toNat + 1 = (a.toNat + b.toNat + c.toNat + 1) % 2 + 2 * (lut 126 (a.toNat + 2 * b.toNat + 4 * c.toNat)).toNat + 4 * (lut 128 (a.toNat + 2 * b.toNat + 4 * c.toNat)).toNat := by
  cases a <;> cases b <;> cases c <;> rfl
def w_n978 (x : Nat → Bool) : Bool := lut 126 ((x 1000).toNat + 2 * (w_n936 x).toNat + 4 * (w_n957 x).toNat)
def w_n979 (x : Nat → Bool) : Bool := lut 128 ((x 1000).toNat + 2 * (w_n936 x).toNat + 4 * (w_n957 x).toNat)
def r327 (x : Nat → Bool) : Nat := ((x 1000).toNat + (w_n936 x).toNat + (w_n957 x).toNat + 1) % 2
theorem r327_lt (x : Nat → Bool) : r327 x < 2 := Nat.mod_lt _ (by decide)
theorem u327 (x : Nat → Bool) : (x 1000).toNat + (w_n936 x).toNat + (w_n957 x).toNat + 1 = r327 x + 2 * (w_n978 x).toNat + 4 * (w_n979 x).toNat := g3 _ _ _ 
theorem e327 (x : Nat → Bool) : (x 1000).toNat + (w_n936 x).toNat + (w_n957 x).toNat + 1 = 2 * (w_n978 x).toNat + 4 * (w_n979 x).toNat + r327 x := by
  have h := u327 x
  omega
theorem g4 (a b c d e f : Bool) : a.toNat + b.toNat + c.toNat + d.toNat + e.toNat + f.toNat + 1 = (a.toNat + b.toNat + c.toNat + d.toNat + e.toNat + f.toNat + 1) % 2 + 2 * (lut 16753814026744960894 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat + 32 * f.toNat)).toNat + 4 * (lut 18446461400418674816 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat + 32 * f.toNat)).toNat := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
def w_n980 (x : Nat → Bool) : Bool := lut 16753814026744960894 ((w_n337 x).toNat + 2 * (w_n570 x).toNat + 4 * (w_n912 x).toNat + 8 * (w_n937 x).toNat + 16 * (w_n958 x).toNat + 32 * (w_n978 x).toNat)
def w_n981 (x : Nat → Bool) : Bool := lut 18446461400418674816 ((w_n337 x).toNat + 2 * (w_n570 x).toNat + 4 * (w_n912 x).toNat + 8 * (w_n937 x).toNat + 16 * (w_n958 x).toNat + 32 * (w_n978 x).toNat)
def r328 (x : Nat → Bool) : Nat := ((w_n337 x).toNat + (w_n570 x).toNat + (w_n912 x).toNat + (w_n937 x).toNat + (w_n958 x).toNat + (w_n978 x).toNat + 1) % 2
theorem r328_lt (x : Nat → Bool) : r328 x < 2 := Nat.mod_lt _ (by decide)
theorem u328 (x : Nat → Bool) : (w_n337 x).toNat + (w_n570 x).toNat + (w_n912 x).toNat + (w_n937 x).toNat + (w_n958 x).toNat + (w_n978 x).toNat + 1 = r328 x + 2 * (w_n980 x).toNat + 4 * (w_n981 x).toNat := g4 _ _ _ _ _ _ 
theorem e328 (x : Nat → Bool) : 2 * (w_n337 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + 2 * (w_n937 x).toNat + 2 * (w_n958 x).toNat + 2 * (w_n978 x).toNat + 2 = 4 * (w_n980 x).toNat + 8 * (w_n981 x).toNat + 2 * r328 x := by
  have h := u328 x
  omega
theorem g5 (a b c d e : Bool) : a.toNat + b.toNat + c.toNat + d.toNat + e.toNat = (a.toNat + b.toNat + c.toNat + d.toNat + e.toNat) % 2 + 2 * (lut 394165992 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat)).toNat + 4 * (lut 3900735488 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat)).toNat := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
def w_n982 (x : Nat → Bool) : Bool := lut 394165992 ((w_n343 x).toNat + 2 * (w_n939 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n979 x).toNat + 16 * (w_n980 x).toNat)
def w_n983 (x : Nat → Bool) : Bool := lut 3900735488 ((w_n343 x).toNat + 2 * (w_n939 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n979 x).toNat + 16 * (w_n980 x).toNat)
def r329 (x : Nat → Bool) : Nat := ((w_n343 x).toNat + (w_n939 x).toNat + (w_n959 x).toNat + (w_n979 x).toNat + (w_n980 x).toNat) % 2
theorem r329_lt (x : Nat → Bool) : r329 x < 2 := Nat.mod_lt _ (by decide)
theorem u329 (x : Nat → Bool) : (w_n343 x).toNat + (w_n939 x).toNat + (w_n959 x).toNat + (w_n979 x).toNat + (w_n980 x).toNat = r329 x + 2 * (w_n982 x).toNat + 4 * (w_n983 x).toNat := g5 _ _ _ _ _ 
theorem e329 (x : Nat → Bool) : 4 * (w_n343 x).toNat + 4 * (w_n939 x).toNat + 4 * (w_n959 x).toNat + 4 * (w_n979 x).toNat + 4 * (w_n980 x).toNat = 8 * (w_n982 x).toNat + 16 * (w_n983 x).toNat + 4 * r329 x := by
  have h := u329 x
  omega
theorem g6 (a b c d e : Bool) : a.toNat + b.toNat + c.toNat + d.toNat + 2 * e.toNat + 1 = (a.toNat + b.toNat + c.toNat + d.toNat + 2 * e.toNat + 1) % 2 + 2 * (lut 3900774270 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat)).toNat + 4 * (lut 4294895744 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat)).toNat := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
def w_n984 (x : Nat → Bool) : Bool := lut 3900774270 ((w_n942 x).toNat + 2 * (w_n960 x).toNat + 4 * (w_n981 x).toNat + 8 * (w_n982 x).toNat + 16 * (w_n943 x).toNat)
def w_n985 (x : Nat → Bool) : Bool := lut 4294895744 ((w_n942 x).toNat + 2 * (w_n960 x).toNat + 4 * (w_n981 x).toNat + 8 * (w_n982 x).toNat + 16 * (w_n943 x).toNat)
def r330 (x : Nat → Bool) : Nat := ((w_n942 x).toNat + (w_n960 x).toNat + (w_n981 x).toNat + (w_n982 x).toNat + 2 * (w_n943 x).toNat + 1) % 2
theorem r330_lt (x : Nat → Bool) : r330 x < 2 := Nat.mod_lt _ (by decide)
theorem u330 (x : Nat → Bool) : (w_n942 x).toNat + (w_n960 x).toNat + (w_n981 x).toNat + (w_n982 x).toNat + 2 * (w_n943 x).toNat + 1 = r330 x + 2 * (w_n984 x).toNat + 4 * (w_n985 x).toNat := g6 _ _ _ _ _ 
theorem e330 (x : Nat → Bool) : 8 * (w_n942 x).toNat + 8 * (w_n960 x).toNat + 8 * (w_n981 x).toNat + 8 * (w_n982 x).toNat + 16 * (w_n943 x).toNat + 8 = 16 * (w_n984 x).toNat + 32 * (w_n985 x).toNat + 8 * r330 x := by
  have h := u330 x
  omega
theorem g7 (a b c d e f : Bool) : a.toNat + b.toNat + c.toNat + d.toNat + e.toNat + 2 * f.toNat = (a.toNat + b.toNat + c.toNat + d.toNat + e.toNat + 2 * f.toNat) % 2 + 2 * (lut 16753814024973352680 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat + 32 * f.toNat)).toNat + 4 * (lut 18446461400042733568 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat + 32 * f.toNat)).toNat := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
def w_n986 (x : Nat → Bool) : Bool := lut 16753814024973352680 ((w_n945 x).toNat + 2 * (w_n961 x).toNat + 4 * (w_n963 x).toNat + 8 * (w_n983 x).toNat + 16 * (w_n984 x).toNat + 32 * (w_n951 x).toNat)
def w_n987 (x : Nat → Bool) : Bool := lut 18446461400042733568 ((w_n945 x).toNat + 2 * (w_n961 x).toNat + 4 * (w_n963 x).toNat + 8 * (w_n983 x).toNat + 16 * (w_n984 x).toNat + 32 * (w_n951 x).toNat)
def r331 (x : Nat → Bool) : Nat := ((w_n945 x).toNat + (w_n961 x).toNat + (w_n963 x).toNat + (w_n983 x).toNat + (w_n984 x).toNat + 2 * (w_n951 x).toNat) % 2
theorem r331_lt (x : Nat → Bool) : r331 x < 2 := Nat.mod_lt _ (by decide)
theorem u331 (x : Nat → Bool) : (w_n945 x).toNat + (w_n961 x).toNat + (w_n963 x).toNat + (w_n983 x).toNat + (w_n984 x).toNat + 2 * (w_n951 x).toNat = r331 x + 2 * (w_n986 x).toNat + 4 * (w_n987 x).toNat := g7 _ _ _ _ _ _ 
theorem e331 (x : Nat → Bool) : 16 * (w_n945 x).toNat + 16 * (w_n961 x).toNat + 16 * (w_n963 x).toNat + 16 * (w_n983 x).toNat + 16 * (w_n984 x).toNat + 32 * (w_n951 x).toNat = 32 * (w_n986 x).toNat + 64 * (w_n987 x).toNat + 16 * r331 x := by
  have h := u331 x
  omega
def w_n988 (x : Nat → Bool) : Bool := lut 16753814024973352680 ((w_n962 x).toNat + 2 * (w_n964 x).toNat + 4 * (w_n966 x).toNat + 8 * (w_n985 x).toNat + 16 * (w_n986 x).toNat + 32 * (w_n969 x).toNat)
def w_n989 (x : Nat → Bool) : Bool := lut 18446461400042733568 ((w_n962 x).toNat + 2 * (w_n964 x).toNat + 4 * (w_n966 x).toNat + 8 * (w_n985 x).toNat + 16 * (w_n986 x).toNat + 32 * (w_n969 x).toNat)
def r332 (x : Nat → Bool) : Nat := ((w_n962 x).toNat + (w_n964 x).toNat + (w_n966 x).toNat + (w_n985 x).toNat + (w_n986 x).toNat + 2 * (w_n969 x).toNat) % 2
theorem r332_lt (x : Nat → Bool) : r332 x < 2 := Nat.mod_lt _ (by decide)
theorem u332 (x : Nat → Bool) : (w_n962 x).toNat + (w_n964 x).toNat + (w_n966 x).toNat + (w_n985 x).toNat + (w_n986 x).toNat + 2 * (w_n969 x).toNat = r332 x + 2 * (w_n988 x).toNat + 4 * (w_n989 x).toNat := g7 _ _ _ _ _ _ 
theorem e332 (x : Nat → Bool) : 32 * (w_n962 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 32 * (w_n985 x).toNat + 32 * (w_n986 x).toNat + 64 * (w_n969 x).toNat = 64 * (w_n988 x).toNat + 128 * (w_n989 x).toNat + 32 * r332 x := by
  have h := u332 x
  omega
theorem g8 (a b c : Bool) : a.toNat + b.toNat + c.toNat = (a.toNat + b.toNat + c.toNat) % 2 + 2 * (lut 232 (a.toNat + 2 * b.toNat + 4 * c.toNat)).toNat := by
  cases a <;> cases b <;> cases c <;> rfl
def w_n990 (x : Nat → Bool) : Bool := lut 232 ((w_n972 x).toNat + 2 * (w_n987 x).toNat + 4 * (w_n988 x).toNat)
def r333 (x : Nat → Bool) : Nat := ((w_n972 x).toNat + (w_n987 x).toNat + (w_n988 x).toNat) % 2
theorem r333_lt (x : Nat → Bool) : r333 x < 2 := Nat.mod_lt _ (by decide)
theorem u333 (x : Nat → Bool) : (w_n972 x).toNat + (w_n987 x).toNat + (w_n988 x).toNat = r333 x + 2 * (w_n990 x).toNat := g8 _ _ _ 
theorem e333 (x : Nat → Bool) : 64 * (w_n972 x).toNat + 64 * (w_n987 x).toNat + 64 * (w_n988 x).toNat = 128 * (w_n990 x).toNat + 64 * r333 x := by
  have h := u333 x
  omega
def w_n991 (x : Nat → Bool) : Bool := lut 16753814024973352680 ((w_n970 x).toNat + 2 * (w_n973 x).toNat + 4 * (w_n975 x).toNat + 8 * (w_n989 x).toNat + 16 * (w_n990 x).toNat + 32 * (w_n956 x).toNat)
def w_n992 (x : Nat → Bool) : Bool := lut 18446461400042733568 ((w_n970 x).toNat + 2 * (w_n973 x).toNat + 4 * (w_n975 x).toNat + 8 * (w_n989 x).toNat + 16 * (w_n990 x).toNat + 32 * (w_n956 x).toNat)
def r334 (x : Nat → Bool) : Nat := ((w_n970 x).toNat + (w_n973 x).toNat + (w_n975 x).toNat + (w_n989 x).toNat + (w_n990 x).toNat + 2 * (w_n956 x).toNat) % 2
theorem r334_lt (x : Nat → Bool) : r334 x < 2 := Nat.mod_lt _ (by decide)
theorem u334 (x : Nat → Bool) : (w_n970 x).toNat + (w_n973 x).toNat + (w_n975 x).toNat + (w_n989 x).toNat + (w_n990 x).toNat + 2 * (w_n956 x).toNat = r334 x + 2 * (w_n991 x).toNat + 4 * (w_n992 x).toNat := g7 _ _ _ _ _ _ 
theorem e334 (x : Nat → Bool) : 128 * (w_n970 x).toNat + 128 * (w_n973 x).toNat + 128 * (w_n975 x).toNat + 128 * (w_n989 x).toNat + 128 * (w_n990 x).toNat + 256 * (w_n956 x).toNat = 256 * (w_n991 x).toNat + 512 * (w_n992 x).toNat + 128 * r334 x := by
  have h := u334 x
  omega
theorem g9 (a b c d e f : Bool) : lut 18446744073709551336 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat + 32 * f.toNat) = decide (a.toNat + b.toNat + c.toNat + d.toNat + 2 * e.toNat + 2 * f.toNat ≥ 2) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
def w_maj (x : Nat → Bool) : Bool := lut 18446744073709551336 ((w_n971 x).toNat + 2 * (w_n974 x).toNat + 4 * (w_n976 x).toNat + 8 * (w_n991 x).toNat + 16 * (w_n977 x).toNat + 32 * (w_n992 x).toNat)
theorem e335 (x : Nat → Bool) : w_maj x = decide ((w_n971 x).toNat + (w_n974 x).toNat + (w_n976 x).toNat + (w_n991 x).toNat + 2 * (w_n977 x).toNat + 2 * (w_n992 x).toNat ≥ 2) := g9 _ _ _ _ _ _ 
def I_b0 (x : Nat → Bool) : Nat := 0 + (x 1000).toNat
theorem b0 (x : Nat → Bool) : I_b0 x = (x 1000).toNat := by
  unfold I_b0
  omega
def I_t0 (x : Nat → Bool) : Nat := I_b0 x
theorem t0 (x : Nat → Bool) : I_t0 x = (x 1000).toNat := by
  have hs : (I_b0 x) = ((x 1000).toNat) := (b0 x)
  have e1 : (I_b0 x) = I_t0 x := by unfold I_t0; ac_rfl
  have e2 : ((x 1000).toNat) = (x 1000).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s0 (x : Nat → Bool) : I_t0 x = pc x 1000 1 := rfl
def I_b1 (x : Nat → Bool) : Nat := 0 + (x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat
theorem b1 (x : Nat → Bool) : I_b1 x = (x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat := by
  unfold I_b1
  omega
def I_t1 (x : Nat → Bool) : Nat := I_b1 x
theorem t1 (x : Nat → Bool) : I_t1 x = (w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat := by
  have hs : ((I_b1 x) + ((x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat)) = (((x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat) + ((w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat)) := (add_eq (b1 x) (e0 x))
  have e1 : ((I_b1 x) + ((x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat)) = (I_t1 x) + ((x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat) := by unfold I_t1; ac_rfl
  have e2 : (((x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat) + ((w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat)) = ((w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat) + ((x 487).toNat + (x 488).toNat + (x 489).toNat + (x 490).toNat + (x 491).toNat + (x 492).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s1 (x : Nat → Bool) : I_t1 x = pc x 487 6 := rfl
def I_b2 (x : Nat → Bool) : Nat := 0 + (x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat
theorem b2 (x : Nat → Bool) : I_b2 x = (x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat := by
  unfold I_b2
  omega
def I_t2 (x : Nat → Bool) : Nat := I_b2 x
theorem t2 (x : Nat → Bool) : I_t2 x = (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat := by
  have hs : ((I_b2 x) + ((x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat)) = (((x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat) + ((w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat)) := (add_eq (b2 x) (e1 x))
  have e1 : ((I_b2 x) + ((x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat)) = (I_t2 x) + ((x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat) := by unfold I_t2; ac_rfl
  have e2 : (((x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat) + ((w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat)) = ((w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat) + ((x 493).toNat + (x 494).toNat + (x 495).toNat + (x 496).toNat + (x 497).toNat + (x 498).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s2 (x : Nat → Bool) : I_t2 x = pc x 493 6 := rfl
def I_t3 (x : Nat → Bool) : Nat := I_t1 x + I_t2 x
theorem t3 (x : Nat → Bool) : I_t3 x = (w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat + (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat := by
  have hs : ((I_t1 x) + (I_t2 x)) = (((w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat) + ((w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat)) := (add_eq (t1 x) (t2 x))
  have e1 : ((I_t1 x) + (I_t2 x)) = I_t3 x := by unfold I_t3; ac_rfl
  have e2 : (((w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat) + ((w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat)) = (w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat + (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s3 (x : Nat → Bool) : I_t3 x = pc x 487 12 := by
  have hl := s1 x
  have hr := s2 x
  have : pc x 487 12 = pc x 487 6 + pc x 493 6 := pc_add x 487 6 6
  unfold I_t3
  omega
def I_b4 (x : Nat → Bool) : Nat := 0 + (x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat
theorem b4 (x : Nat → Bool) : I_b4 x = (x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat := by
  unfold I_b4
  omega
def I_t4 (x : Nat → Bool) : Nat := I_b4 x
theorem t4 (x : Nat → Bool) : I_t4 x = (w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat := by
  have hs : ((I_b4 x) + ((x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat)) = (((x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat) + ((w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat)) := (add_eq (b4 x) (e2 x))
  have e1 : ((I_b4 x) + ((x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat)) = (I_t4 x) + ((x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat) := by unfold I_t4; ac_rfl
  have e2 : (((x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat) + ((w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat)) = ((w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat) + ((x 499).toNat + (x 500).toNat + (x 501).toNat + (x 502).toNat + (x 503).toNat + (x 504).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s4 (x : Nat → Bool) : I_t4 x = pc x 499 6 := rfl
def I_b5 (x : Nat → Bool) : Nat := 0 + (x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat
theorem b5 (x : Nat → Bool) : I_b5 x = (x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat := by
  unfold I_b5
  omega
def I_t5 (x : Nat → Bool) : Nat := I_b5 x
theorem t5 (x : Nat → Bool) : I_t5 x = (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat := by
  have hs : ((I_b5 x) + ((x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat)) = (((x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat) + ((w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat)) := (add_eq (b5 x) (e3 x))
  have e1 : ((I_b5 x) + ((x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat)) = (I_t5 x) + ((x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat) := by unfold I_t5; ac_rfl
  have e2 : (((x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat) + ((w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat)) = ((w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat) + ((x 505).toNat + (x 506).toNat + (x 507).toNat + (x 508).toNat + (x 509).toNat + (x 510).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s5 (x : Nat → Bool) : I_t5 x = pc x 505 6 := rfl
def I_t6 (x : Nat → Bool) : Nat := I_t4 x + I_t5 x
theorem t6 (x : Nat → Bool) : I_t6 x = (w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat + (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat := by
  have hs : ((I_t4 x) + (I_t5 x)) = (((w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat) + ((w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat)) := (add_eq (t4 x) (t5 x))
  have e1 : ((I_t4 x) + (I_t5 x)) = I_t6 x := by unfold I_t6; ac_rfl
  have e2 : (((w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat) + ((w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat)) = (w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat + (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s6 (x : Nat → Bool) : I_t6 x = pc x 499 12 := by
  have hl := s4 x
  have hr := s5 x
  have : pc x 499 12 = pc x 499 6 + pc x 505 6 := pc_add x 499 6 6
  unfold I_t6
  omega
def I_t7 (x : Nat → Bool) : Nat := I_t3 x + I_t6 x
theorem t7 (x : Nat → Bool) : I_t7 x = (w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat + (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat + (w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat + (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat := by
  have hs : ((I_t3 x) + (I_t6 x)) = (((w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat + (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat) + ((w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat + (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat)) := (add_eq (t3 x) (t6 x))
  have e1 : ((I_t3 x) + (I_t6 x)) = I_t7 x := by unfold I_t7; ac_rfl
  have e2 : (((w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat + (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat) + ((w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat + (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat)) = (w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat + (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat + (w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat + (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s7 (x : Nat → Bool) : I_t7 x = pc x 487 24 := by
  have hl := s3 x
  have hr := s6 x
  have : pc x 487 24 = pc x 487 12 + pc x 499 12 := pc_add x 487 12 12
  unfold I_t7
  omega
def I_b8 (x : Nat → Bool) : Nat := 0 + (x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat
theorem b8 (x : Nat → Bool) : I_b8 x = (x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat := by
  unfold I_b8
  omega
def I_t8 (x : Nat → Bool) : Nat := I_b8 x
theorem t8 (x : Nat → Bool) : I_t8 x = (w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat := by
  have hs : ((I_b8 x) + ((x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat)) = (((x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat) + ((w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat)) := (add_eq (b8 x) (e4 x))
  have e1 : ((I_b8 x) + ((x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat)) = (I_t8 x) + ((x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat) := by unfold I_t8; ac_rfl
  have e2 : (((x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat) + ((w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat)) = ((w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat) + ((x 469).toNat + (x 470).toNat + (x 471).toNat + (x 472).toNat + (x 473).toNat + (x 474).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s8 (x : Nat → Bool) : I_t8 x = pc x 469 6 := rfl
def I_b9 (x : Nat → Bool) : Nat := 0 + (x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat
theorem b9 (x : Nat → Bool) : I_b9 x = (x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat := by
  unfold I_b9
  omega
def I_t9 (x : Nat → Bool) : Nat := I_b9 x
theorem t9 (x : Nat → Bool) : I_t9 x = (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat := by
  have hs : ((I_b9 x) + ((x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat)) = (((x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat) + ((w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat)) := (add_eq (b9 x) (e5 x))
  have e1 : ((I_b9 x) + ((x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat)) = (I_t9 x) + ((x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat) := by unfold I_t9; ac_rfl
  have e2 : (((x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat) + ((w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat)) = ((w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat) + ((x 463).toNat + (x 464).toNat + (x 465).toNat + (x 466).toNat + (x 467).toNat + (x 468).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s9 (x : Nat → Bool) : I_t9 x = pc x 463 6 := rfl
def I_t10 (x : Nat → Bool) : Nat := I_t8 x + I_t9 x
theorem t10 (x : Nat → Bool) : I_t10 x = (w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat + (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat := by
  have hs : ((I_t8 x) + (I_t9 x)) = (((w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat) + ((w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat)) := (add_eq (t8 x) (t9 x))
  have e1 : ((I_t8 x) + (I_t9 x)) = I_t10 x := by unfold I_t10; ac_rfl
  have e2 : (((w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat) + ((w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat)) = (w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat + (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s10 (x : Nat → Bool) : I_t10 x = pc x 463 12 := by
  have hl := s8 x
  have hr := s9 x
  have : pc x 463 12 = pc x 463 6 + pc x 469 6 := pc_add x 463 6 6
  unfold I_t10
  omega
def I_b11 (x : Nat → Bool) : Nat := 0 + (x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat
theorem b11 (x : Nat → Bool) : I_b11 x = (x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat := by
  unfold I_b11
  omega
def I_t11 (x : Nat → Bool) : Nat := I_b11 x
theorem t11 (x : Nat → Bool) : I_t11 x = (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat := by
  have hs : ((I_b11 x) + ((x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat)) = (((x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat) + ((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat)) := (add_eq (b11 x) (e6 x))
  have e1 : ((I_b11 x) + ((x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat)) = (I_t11 x) + ((x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat) := by unfold I_t11; ac_rfl
  have e2 : (((x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat) + ((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat)) = ((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat) + ((x 481).toNat + (x 482).toNat + (x 483).toNat + (x 484).toNat + (x 485).toNat + (x 486).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s11 (x : Nat → Bool) : I_t11 x = pc x 481 6 := rfl
def I_b12 (x : Nat → Bool) : Nat := 0 + (x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat
theorem b12 (x : Nat → Bool) : I_b12 x = (x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat := by
  unfold I_b12
  omega
def I_t12 (x : Nat → Bool) : Nat := I_b12 x
theorem t12 (x : Nat → Bool) : I_t12 x = (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat := by
  have hs : ((I_b12 x) + ((x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat)) = (((x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat) + ((w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat)) := (add_eq (b12 x) (e7 x))
  have e1 : ((I_b12 x) + ((x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat)) = (I_t12 x) + ((x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat) := by unfold I_t12; ac_rfl
  have e2 : (((x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat) + ((w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat)) = ((w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat) + ((x 475).toNat + (x 476).toNat + (x 477).toNat + (x 478).toNat + (x 479).toNat + (x 480).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s12 (x : Nat → Bool) : I_t12 x = pc x 475 6 := rfl
def I_t13 (x : Nat → Bool) : Nat := I_t11 x + I_t12 x
theorem t13 (x : Nat → Bool) : I_t13 x = (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat := by
  have hs : ((I_t11 x) + (I_t12 x)) = (((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat) + ((w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat)) := (add_eq (t11 x) (t12 x))
  have e1 : ((I_t11 x) + (I_t12 x)) = I_t13 x := by unfold I_t13; ac_rfl
  have e2 : (((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat) + ((w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat)) = (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s13 (x : Nat → Bool) : I_t13 x = pc x 475 12 := by
  have hl := s11 x
  have hr := s12 x
  have : pc x 475 12 = pc x 475 6 + pc x 481 6 := pc_add x 475 6 6
  unfold I_t13
  omega
def I_t14 (x : Nat → Bool) : Nat := I_t10 x + I_t13 x
theorem t14 (x : Nat → Bool) : I_t14 x = (w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat + (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat + (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat := by
  have hs : ((I_t10 x) + (I_t13 x)) = (((w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat + (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat) + ((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat)) := (add_eq (t10 x) (t13 x))
  have e1 : ((I_t10 x) + (I_t13 x)) = I_t14 x := by unfold I_t14; ac_rfl
  have e2 : (((w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat + (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat) + ((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat)) = (w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat + (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat + (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s14 (x : Nat → Bool) : I_t14 x = pc x 463 24 := by
  have hl := s10 x
  have hr := s13 x
  have : pc x 463 24 = pc x 463 12 + pc x 475 12 := pc_add x 463 12 12
  unfold I_t14
  omega
def I_t15 (x : Nat → Bool) : Nat := I_t7 x + I_t14 x
theorem t15 (x : Nat → Bool) : I_t15 x = (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat + (w_n25 x).toNat + 2 * (w_n26 x).toNat + 4 * (w_n27 x).toNat + 2 * (w_n28 x).toNat + 4 * (w_n29 x).toNat + 8 * (w_n30 x).toNat + 4 * (w_n31 x).toNat + 8 * (w_n32 x).toNat + 16 * (w_n33 x).toNat := by
  have hs : (((((I_t7 x) + (I_t14 x)) + ((w_n1 x).toNat + (w_n4 x).toNat + (w_n7 x).toNat + (w_n10 x).toNat + (w_n13 x).toNat + (w_n16 x).toNat)) + (2 * (w_n2 x).toNat + 2 * (w_n5 x).toNat + 2 * (w_n8 x).toNat + 2 * (w_n11 x).toNat + 2 * (w_n14 x).toNat + 2 * (w_n17 x).toNat)) + (4 * (w_n3 x).toNat + 4 * (w_n6 x).toNat + 4 * (w_n9 x).toNat + 4 * (w_n12 x).toNat + 4 * (w_n15 x).toNat + 4 * (w_n18 x).toNat)) = ((((((w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat + (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat + (w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat + (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat) + ((w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat + (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat + (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat)) + ((w_n25 x).toNat + 2 * (w_n26 x).toNat + 4 * (w_n27 x).toNat)) + (2 * (w_n28 x).toNat + 4 * (w_n29 x).toNat + 8 * (w_n30 x).toNat)) + (4 * (w_n31 x).toNat + 8 * (w_n32 x).toNat + 16 * (w_n33 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t7 x) (t14 x)) (e8 x)) (e9 x)) (e10 x))
  have e1 : (((((I_t7 x) + (I_t14 x)) + ((w_n1 x).toNat + (w_n4 x).toNat + (w_n7 x).toNat + (w_n10 x).toNat + (w_n13 x).toNat + (w_n16 x).toNat)) + (2 * (w_n2 x).toNat + 2 * (w_n5 x).toNat + 2 * (w_n8 x).toNat + 2 * (w_n11 x).toNat + 2 * (w_n14 x).toNat + 2 * (w_n17 x).toNat)) + (4 * (w_n3 x).toNat + 4 * (w_n6 x).toNat + 4 * (w_n9 x).toNat + 4 * (w_n12 x).toNat + 4 * (w_n15 x).toNat + 4 * (w_n18 x).toNat)) = (I_t15 x) + ((w_n1 x).toNat + (w_n4 x).toNat + (w_n7 x).toNat + (w_n10 x).toNat + (w_n13 x).toNat + (w_n16 x).toNat + 2 * (w_n2 x).toNat + 2 * (w_n5 x).toNat + 2 * (w_n8 x).toNat + 2 * (w_n11 x).toNat + 2 * (w_n14 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n3 x).toNat + 4 * (w_n6 x).toNat + 4 * (w_n9 x).toNat + 4 * (w_n12 x).toNat + 4 * (w_n15 x).toNat + 4 * (w_n18 x).toNat) := by unfold I_t15; ac_rfl
  have e2 : ((((((w_n1 x).toNat + 2 * (w_n2 x).toNat + 4 * (w_n3 x).toNat + (w_n4 x).toNat + 2 * (w_n5 x).toNat + 4 * (w_n6 x).toNat + (w_n7 x).toNat + 2 * (w_n8 x).toNat + 4 * (w_n9 x).toNat + (w_n10 x).toNat + 2 * (w_n11 x).toNat + 4 * (w_n12 x).toNat) + ((w_n13 x).toNat + 2 * (w_n14 x).toNat + 4 * (w_n15 x).toNat + (w_n16 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n18 x).toNat + (w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat)) + ((w_n25 x).toNat + 2 * (w_n26 x).toNat + 4 * (w_n27 x).toNat)) + (2 * (w_n28 x).toNat + 4 * (w_n29 x).toNat + 8 * (w_n30 x).toNat)) + (4 * (w_n31 x).toNat + 8 * (w_n32 x).toNat + 16 * (w_n33 x).toNat)) = ((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat + (w_n25 x).toNat + 2 * (w_n26 x).toNat + 4 * (w_n27 x).toNat + 2 * (w_n28 x).toNat + 4 * (w_n29 x).toNat + 8 * (w_n30 x).toNat + 4 * (w_n31 x).toNat + 8 * (w_n32 x).toNat + 16 * (w_n33 x).toNat) + ((w_n1 x).toNat + (w_n4 x).toNat + (w_n7 x).toNat + (w_n10 x).toNat + (w_n13 x).toNat + (w_n16 x).toNat + 2 * (w_n2 x).toNat + 2 * (w_n5 x).toNat + 2 * (w_n8 x).toNat + 2 * (w_n11 x).toNat + 2 * (w_n14 x).toNat + 2 * (w_n17 x).toNat + 4 * (w_n3 x).toNat + 4 * (w_n6 x).toNat + 4 * (w_n9 x).toNat + 4 * (w_n12 x).toNat + 4 * (w_n15 x).toNat + 4 * (w_n18 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s15 (x : Nat → Bool) : I_t15 x = pc x 463 48 := by
  have hl := s7 x
  have hr := s14 x
  have : pc x 463 48 = pc x 463 24 + pc x 487 24 := pc_add x 463 24 24
  unfold I_t15
  omega
def I_b16 (x : Nat → Bool) : Nat := 0 + (x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat
theorem b16 (x : Nat → Bool) : I_b16 x = (x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat := by
  unfold I_b16
  omega
def I_t16 (x : Nat → Bool) : Nat := I_b16 x
theorem t16 (x : Nat → Bool) : I_t16 x = (w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat := by
  have hs : ((I_b16 x) + ((x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat)) = (((x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat) + ((w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat)) := (add_eq (b16 x) (e11 x))
  have e1 : ((I_b16 x) + ((x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat)) = (I_t16 x) + ((x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat) := by unfold I_t16; ac_rfl
  have e2 : (((x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat) + ((w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat)) = ((w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat) + ((x 547).toNat + (x 548).toNat + (x 549).toNat + (x 550).toNat + (x 551).toNat + (x 552).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s16 (x : Nat → Bool) : I_t16 x = pc x 547 6 := rfl
def I_b17 (x : Nat → Bool) : Nat := 0 + (x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat
theorem b17 (x : Nat → Bool) : I_b17 x = (x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat := by
  unfold I_b17
  omega
def I_t17 (x : Nat → Bool) : Nat := I_b17 x
theorem t17 (x : Nat → Bool) : I_t17 x = (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat := by
  have hs : ((I_b17 x) + ((x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat)) = (((x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat) + ((w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat)) := (add_eq (b17 x) (e12 x))
  have e1 : ((I_b17 x) + ((x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat)) = (I_t17 x) + ((x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat) := by unfold I_t17; ac_rfl
  have e2 : (((x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat) + ((w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat)) = ((w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat) + ((x 553).toNat + (x 554).toNat + (x 555).toNat + (x 556).toNat + (x 557).toNat + (x 558).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s17 (x : Nat → Bool) : I_t17 x = pc x 553 6 := rfl
def I_t18 (x : Nat → Bool) : Nat := I_t16 x + I_t17 x
theorem t18 (x : Nat → Bool) : I_t18 x = (w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat + (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat := by
  have hs : ((I_t16 x) + (I_t17 x)) = (((w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat) + ((w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat)) := (add_eq (t16 x) (t17 x))
  have e1 : ((I_t16 x) + (I_t17 x)) = I_t18 x := by unfold I_t18; ac_rfl
  have e2 : (((w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat) + ((w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat)) = (w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat + (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s18 (x : Nat → Bool) : I_t18 x = pc x 547 12 := by
  have hl := s16 x
  have hr := s17 x
  have : pc x 547 12 = pc x 547 6 + pc x 553 6 := pc_add x 547 6 6
  unfold I_t18
  omega
def I_b19 (x : Nat → Bool) : Nat := 0 + (x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat
theorem b19 (x : Nat → Bool) : I_b19 x = (x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat := by
  unfold I_b19
  omega
def I_t19 (x : Nat → Bool) : Nat := I_b19 x
theorem t19 (x : Nat → Bool) : I_t19 x = (w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat := by
  have hs : ((I_b19 x) + ((x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat)) = (((x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat) + ((w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat)) := (add_eq (b19 x) (e13 x))
  have e1 : ((I_b19 x) + ((x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat)) = (I_t19 x) + ((x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat) := by unfold I_t19; ac_rfl
  have e2 : (((x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat) + ((w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat)) = ((w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat) + ((x 535).toNat + (x 536).toNat + (x 537).toNat + (x 538).toNat + (x 539).toNat + (x 540).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s19 (x : Nat → Bool) : I_t19 x = pc x 535 6 := rfl
def I_b20 (x : Nat → Bool) : Nat := 0 + (x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat
theorem b20 (x : Nat → Bool) : I_b20 x = (x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat := by
  unfold I_b20
  omega
def I_t20 (x : Nat → Bool) : Nat := I_b20 x
theorem t20 (x : Nat → Bool) : I_t20 x = (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat := by
  have hs : ((I_b20 x) + ((x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat)) = (((x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat) + ((w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat)) := (add_eq (b20 x) (e14 x))
  have e1 : ((I_b20 x) + ((x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat)) = (I_t20 x) + ((x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat) := by unfold I_t20; ac_rfl
  have e2 : (((x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat) + ((w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat)) = ((w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat) + ((x 541).toNat + (x 542).toNat + (x 543).toNat + (x 544).toNat + (x 545).toNat + (x 546).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s20 (x : Nat → Bool) : I_t20 x = pc x 541 6 := rfl
def I_t21 (x : Nat → Bool) : Nat := I_t19 x + I_t20 x
theorem t21 (x : Nat → Bool) : I_t21 x = (w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat + (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat := by
  have hs : ((I_t19 x) + (I_t20 x)) = (((w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat) + ((w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat)) := (add_eq (t19 x) (t20 x))
  have e1 : ((I_t19 x) + (I_t20 x)) = I_t21 x := by unfold I_t21; ac_rfl
  have e2 : (((w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat) + ((w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat)) = (w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat + (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s21 (x : Nat → Bool) : I_t21 x = pc x 535 12 := by
  have hl := s19 x
  have hr := s20 x
  have : pc x 535 12 = pc x 535 6 + pc x 541 6 := pc_add x 535 6 6
  unfold I_t21
  omega
def I_t22 (x : Nat → Bool) : Nat := I_t18 x + I_t21 x
theorem t22 (x : Nat → Bool) : I_t22 x = (w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat + (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat + (w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat + (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat := by
  have hs : ((I_t18 x) + (I_t21 x)) = (((w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat + (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat) + ((w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat + (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat)) := (add_eq (t18 x) (t21 x))
  have e1 : ((I_t18 x) + (I_t21 x)) = I_t22 x := by unfold I_t22; ac_rfl
  have e2 : (((w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat + (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat) + ((w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat + (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat)) = (w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat + (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat + (w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat + (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s22 (x : Nat → Bool) : I_t22 x = pc x 535 24 := by
  have hl := s18 x
  have hr := s21 x
  have : pc x 535 24 = pc x 535 12 + pc x 547 12 := pc_add x 535 12 12
  unfold I_t22
  omega
def I_b23 (x : Nat → Bool) : Nat := 0 + (x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat
theorem b23 (x : Nat → Bool) : I_b23 x = (x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat := by
  unfold I_b23
  omega
def I_t23 (x : Nat → Bool) : Nat := I_b23 x
theorem t23 (x : Nat → Bool) : I_t23 x = (w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat := by
  have hs : ((I_b23 x) + ((x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat)) = (((x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat) + ((w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat)) := (add_eq (b23 x) (e15 x))
  have e1 : ((I_b23 x) + ((x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat)) = (I_t23 x) + ((x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat) := by unfold I_t23; ac_rfl
  have e2 : (((x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat) + ((w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat)) = ((w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat) + ((x 517).toNat + (x 518).toNat + (x 519).toNat + (x 520).toNat + (x 521).toNat + (x 522).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s23 (x : Nat → Bool) : I_t23 x = pc x 517 6 := rfl
def I_b24 (x : Nat → Bool) : Nat := 0 + (x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat
theorem b24 (x : Nat → Bool) : I_b24 x = (x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat := by
  unfold I_b24
  omega
def I_t24 (x : Nat → Bool) : Nat := I_b24 x
theorem t24 (x : Nat → Bool) : I_t24 x = (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat := by
  have hs : ((I_b24 x) + ((x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat)) = (((x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat) + ((w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat)) := (add_eq (b24 x) (e16 x))
  have e1 : ((I_b24 x) + ((x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat)) = (I_t24 x) + ((x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat) := by unfold I_t24; ac_rfl
  have e2 : (((x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat) + ((w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat)) = ((w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat) + ((x 511).toNat + (x 512).toNat + (x 513).toNat + (x 514).toNat + (x 515).toNat + (x 516).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s24 (x : Nat → Bool) : I_t24 x = pc x 511 6 := rfl
def I_t25 (x : Nat → Bool) : Nat := I_t23 x + I_t24 x
theorem t25 (x : Nat → Bool) : I_t25 x = (w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat + (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat := by
  have hs : ((I_t23 x) + (I_t24 x)) = (((w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat) + ((w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat)) := (add_eq (t23 x) (t24 x))
  have e1 : ((I_t23 x) + (I_t24 x)) = I_t25 x := by unfold I_t25; ac_rfl
  have e2 : (((w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat) + ((w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat)) = (w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat + (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s25 (x : Nat → Bool) : I_t25 x = pc x 511 12 := by
  have hl := s23 x
  have hr := s24 x
  have : pc x 511 12 = pc x 511 6 + pc x 517 6 := pc_add x 511 6 6
  unfold I_t25
  omega
def I_b26 (x : Nat → Bool) : Nat := 0 + (x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat
theorem b26 (x : Nat → Bool) : I_b26 x = (x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat := by
  unfold I_b26
  omega
def I_t26 (x : Nat → Bool) : Nat := I_b26 x
theorem t26 (x : Nat → Bool) : I_t26 x = (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat := by
  have hs : ((I_b26 x) + ((x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat)) = (((x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat) + ((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat)) := (add_eq (b26 x) (e17 x))
  have e1 : ((I_b26 x) + ((x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat)) = (I_t26 x) + ((x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat) := by unfold I_t26; ac_rfl
  have e2 : (((x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat) + ((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat)) = ((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat) + ((x 529).toNat + (x 530).toNat + (x 531).toNat + (x 532).toNat + (x 533).toNat + (x 534).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s26 (x : Nat → Bool) : I_t26 x = pc x 529 6 := rfl
def I_b27 (x : Nat → Bool) : Nat := 0 + (x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat
theorem b27 (x : Nat → Bool) : I_b27 x = (x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat := by
  unfold I_b27
  omega
def I_t27 (x : Nat → Bool) : Nat := I_b27 x
theorem t27 (x : Nat → Bool) : I_t27 x = (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat := by
  have hs : ((I_b27 x) + ((x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat)) = (((x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat) + ((w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat)) := (add_eq (b27 x) (e18 x))
  have e1 : ((I_b27 x) + ((x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat)) = (I_t27 x) + ((x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat) := by unfold I_t27; ac_rfl
  have e2 : (((x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat) + ((w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat)) = ((w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat) + ((x 523).toNat + (x 524).toNat + (x 525).toNat + (x 526).toNat + (x 527).toNat + (x 528).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s27 (x : Nat → Bool) : I_t27 x = pc x 523 6 := rfl
def I_t28 (x : Nat → Bool) : Nat := I_t26 x + I_t27 x
theorem t28 (x : Nat → Bool) : I_t28 x = (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat := by
  have hs : ((I_t26 x) + (I_t27 x)) = (((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat) + ((w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat)) := (add_eq (t26 x) (t27 x))
  have e1 : ((I_t26 x) + (I_t27 x)) = I_t28 x := by unfold I_t28; ac_rfl
  have e2 : (((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat) + ((w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat)) = (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s28 (x : Nat → Bool) : I_t28 x = pc x 523 12 := by
  have hl := s26 x
  have hr := s27 x
  have : pc x 523 12 = pc x 523 6 + pc x 529 6 := pc_add x 523 6 6
  unfold I_t28
  omega
def I_t29 (x : Nat → Bool) : Nat := I_t25 x + I_t28 x
theorem t29 (x : Nat → Bool) : I_t29 x = (w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat + (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat + (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat := by
  have hs : ((I_t25 x) + (I_t28 x)) = (((w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat + (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat) + ((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat)) := (add_eq (t25 x) (t28 x))
  have e1 : ((I_t25 x) + (I_t28 x)) = I_t29 x := by unfold I_t29; ac_rfl
  have e2 : (((w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat + (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat) + ((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat)) = (w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat + (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat + (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s29 (x : Nat → Bool) : I_t29 x = pc x 511 24 := by
  have hl := s25 x
  have hr := s28 x
  have : pc x 511 24 = pc x 511 12 + pc x 523 12 := pc_add x 511 12 12
  unfold I_t29
  omega
def I_t30 (x : Nat → Bool) : Nat := I_t22 x + I_t29 x
theorem t30 (x : Nat → Bool) : I_t30 x = (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat + (w_n58 x).toNat + 2 * (w_n59 x).toNat + 4 * (w_n60 x).toNat + 2 * (w_n61 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n63 x).toNat + 4 * (w_n64 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n66 x).toNat := by
  have hs : (((((I_t22 x) + (I_t29 x)) + ((w_n34 x).toNat + (w_n37 x).toNat + (w_n40 x).toNat + (w_n43 x).toNat + (w_n46 x).toNat + (w_n49 x).toNat)) + (2 * (w_n35 x).toNat + 2 * (w_n38 x).toNat + 2 * (w_n41 x).toNat + 2 * (w_n44 x).toNat + 2 * (w_n47 x).toNat + 2 * (w_n50 x).toNat)) + (4 * (w_n36 x).toNat + 4 * (w_n39 x).toNat + 4 * (w_n42 x).toNat + 4 * (w_n45 x).toNat + 4 * (w_n48 x).toNat + 4 * (w_n51 x).toNat)) = ((((((w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat + (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat + (w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat + (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat) + ((w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat + (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat + (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat)) + ((w_n58 x).toNat + 2 * (w_n59 x).toNat + 4 * (w_n60 x).toNat)) + (2 * (w_n61 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n63 x).toNat)) + (4 * (w_n64 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n66 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t22 x) (t29 x)) (e19 x)) (e20 x)) (e21 x))
  have e1 : (((((I_t22 x) + (I_t29 x)) + ((w_n34 x).toNat + (w_n37 x).toNat + (w_n40 x).toNat + (w_n43 x).toNat + (w_n46 x).toNat + (w_n49 x).toNat)) + (2 * (w_n35 x).toNat + 2 * (w_n38 x).toNat + 2 * (w_n41 x).toNat + 2 * (w_n44 x).toNat + 2 * (w_n47 x).toNat + 2 * (w_n50 x).toNat)) + (4 * (w_n36 x).toNat + 4 * (w_n39 x).toNat + 4 * (w_n42 x).toNat + 4 * (w_n45 x).toNat + 4 * (w_n48 x).toNat + 4 * (w_n51 x).toNat)) = (I_t30 x) + ((w_n34 x).toNat + (w_n37 x).toNat + (w_n40 x).toNat + (w_n43 x).toNat + (w_n46 x).toNat + (w_n49 x).toNat + 2 * (w_n35 x).toNat + 2 * (w_n38 x).toNat + 2 * (w_n41 x).toNat + 2 * (w_n44 x).toNat + 2 * (w_n47 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n36 x).toNat + 4 * (w_n39 x).toNat + 4 * (w_n42 x).toNat + 4 * (w_n45 x).toNat + 4 * (w_n48 x).toNat + 4 * (w_n51 x).toNat) := by unfold I_t30; ac_rfl
  have e2 : ((((((w_n34 x).toNat + 2 * (w_n35 x).toNat + 4 * (w_n36 x).toNat + (w_n37 x).toNat + 2 * (w_n38 x).toNat + 4 * (w_n39 x).toNat + (w_n40 x).toNat + 2 * (w_n41 x).toNat + 4 * (w_n42 x).toNat + (w_n43 x).toNat + 2 * (w_n44 x).toNat + 4 * (w_n45 x).toNat) + ((w_n46 x).toNat + 2 * (w_n47 x).toNat + 4 * (w_n48 x).toNat + (w_n49 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n51 x).toNat + (w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat)) + ((w_n58 x).toNat + 2 * (w_n59 x).toNat + 4 * (w_n60 x).toNat)) + (2 * (w_n61 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n63 x).toNat)) + (4 * (w_n64 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n66 x).toNat)) = ((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat + (w_n58 x).toNat + 2 * (w_n59 x).toNat + 4 * (w_n60 x).toNat + 2 * (w_n61 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n63 x).toNat + 4 * (w_n64 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n66 x).toNat) + ((w_n34 x).toNat + (w_n37 x).toNat + (w_n40 x).toNat + (w_n43 x).toNat + (w_n46 x).toNat + (w_n49 x).toNat + 2 * (w_n35 x).toNat + 2 * (w_n38 x).toNat + 2 * (w_n41 x).toNat + 2 * (w_n44 x).toNat + 2 * (w_n47 x).toNat + 2 * (w_n50 x).toNat + 4 * (w_n36 x).toNat + 4 * (w_n39 x).toNat + 4 * (w_n42 x).toNat + 4 * (w_n45 x).toNat + 4 * (w_n48 x).toNat + 4 * (w_n51 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s30 (x : Nat → Bool) : I_t30 x = pc x 511 48 := by
  have hl := s22 x
  have hr := s29 x
  have : pc x 511 48 = pc x 511 24 + pc x 535 24 := pc_add x 511 24 24
  unfold I_t30
  omega
def I_t31 (x : Nat → Bool) : Nat := I_t15 x + I_t30 x
theorem t31 (x : Nat → Bool) : I_t31 x = 16 * (w_n33 x).toNat + 2 * (w_n59 x).toNat + 2 * (w_n61 x).toNat + 16 * (w_n66 x).toNat + (w_n67 x).toNat + 2 * (w_n68 x).toNat + 2 * (w_n70 x).toNat + 4 * (w_n73 x).toNat + 16 * (w_n75 x).toNat + 4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 16 * (w_n78 x).toNat + 8 * (w_n79 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n81 x).toNat := by
  have hs : (((((((I_t15 x) + (I_t30 x)) + ((w_n19 x).toNat + (w_n22 x).toNat + (w_n25 x).toNat + (w_n52 x).toNat + (w_n55 x).toNat + (w_n58 x).toNat)) + (2 * (w_n20 x).toNat + 2 * (w_n23 x).toNat + 2 * (w_n26 x).toNat + 2 * (w_n28 x).toNat + 2 * (w_n53 x).toNat + 2 * (w_n56 x).toNat)) + (4 * (w_n21 x).toNat + 4 * (w_n24 x).toNat + 4 * (w_n27 x).toNat + 4 * (w_n29 x).toNat + 4 * (w_n31 x).toNat + 4 * (w_n54 x).toNat)) + (4 * (w_n57 x).toNat + 4 * (w_n60 x).toNat + 4 * (w_n62 x).toNat + 4 * (w_n64 x).toNat + 4 * (w_n69 x).toNat + 4 * (w_n71 x).toNat)) + (8 * (w_n30 x).toNat + 8 * (w_n32 x).toNat + 8 * (w_n63 x).toNat + 8 * (w_n65 x).toNat + 8 * (w_n72 x).toNat + 8 * (w_n74 x).toNat)) = ((((((((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat + (w_n25 x).toNat + 2 * (w_n26 x).toNat + 4 * (w_n27 x).toNat + 2 * (w_n28 x).toNat + 4 * (w_n29 x).toNat + 8 * (w_n30 x).toNat + 4 * (w_n31 x).toNat + 8 * (w_n32 x).toNat + 16 * (w_n33 x).toNat) + ((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat + (w_n58 x).toNat + 2 * (w_n59 x).toNat + 4 * (w_n60 x).toNat + 2 * (w_n61 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n63 x).toNat + 4 * (w_n64 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n66 x).toNat)) + ((w_n67 x).toNat + 2 * (w_n68 x).toNat + 4 * (w_n69 x).toNat)) + (2 * (w_n70 x).toNat + 4 * (w_n71 x).toNat + 8 * (w_n72 x).toNat)) + (4 * (w_n73 x).toNat + 8 * (w_n74 x).toNat + 16 * (w_n75 x).toNat)) + (4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 16 * (w_n78 x).toNat)) + (8 * (w_n79 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n81 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t15 x) (t30 x)) (e22 x)) (e23 x)) (e24 x)) (e25 x)) (e26 x))
  have e1 : (((((((I_t15 x) + (I_t30 x)) + ((w_n19 x).toNat + (w_n22 x).toNat + (w_n25 x).toNat + (w_n52 x).toNat + (w_n55 x).toNat + (w_n58 x).toNat)) + (2 * (w_n20 x).toNat + 2 * (w_n23 x).toNat + 2 * (w_n26 x).toNat + 2 * (w_n28 x).toNat + 2 * (w_n53 x).toNat + 2 * (w_n56 x).toNat)) + (4 * (w_n21 x).toNat + 4 * (w_n24 x).toNat + 4 * (w_n27 x).toNat + 4 * (w_n29 x).toNat + 4 * (w_n31 x).toNat + 4 * (w_n54 x).toNat)) + (4 * (w_n57 x).toNat + 4 * (w_n60 x).toNat + 4 * (w_n62 x).toNat + 4 * (w_n64 x).toNat + 4 * (w_n69 x).toNat + 4 * (w_n71 x).toNat)) + (8 * (w_n30 x).toNat + 8 * (w_n32 x).toNat + 8 * (w_n63 x).toNat + 8 * (w_n65 x).toNat + 8 * (w_n72 x).toNat + 8 * (w_n74 x).toNat)) = (I_t31 x) + ((w_n19 x).toNat + (w_n22 x).toNat + (w_n25 x).toNat + (w_n52 x).toNat + (w_n55 x).toNat + (w_n58 x).toNat + 2 * (w_n20 x).toNat + 2 * (w_n23 x).toNat + 2 * (w_n26 x).toNat + 2 * (w_n28 x).toNat + 2 * (w_n53 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n21 x).toNat + 4 * (w_n24 x).toNat + 4 * (w_n27 x).toNat + 4 * (w_n29 x).toNat + 4 * (w_n31 x).toNat + 4 * (w_n54 x).toNat + 4 * (w_n57 x).toNat + 4 * (w_n60 x).toNat + 4 * (w_n62 x).toNat + 4 * (w_n64 x).toNat + 4 * (w_n69 x).toNat + 4 * (w_n71 x).toNat + 8 * (w_n30 x).toNat + 8 * (w_n32 x).toNat + 8 * (w_n63 x).toNat + 8 * (w_n65 x).toNat + 8 * (w_n72 x).toNat + 8 * (w_n74 x).toNat) := by unfold I_t31; ac_rfl
  have e2 : ((((((((w_n19 x).toNat + 2 * (w_n20 x).toNat + 4 * (w_n21 x).toNat + (w_n22 x).toNat + 2 * (w_n23 x).toNat + 4 * (w_n24 x).toNat + (w_n25 x).toNat + 2 * (w_n26 x).toNat + 4 * (w_n27 x).toNat + 2 * (w_n28 x).toNat + 4 * (w_n29 x).toNat + 8 * (w_n30 x).toNat + 4 * (w_n31 x).toNat + 8 * (w_n32 x).toNat + 16 * (w_n33 x).toNat) + ((w_n52 x).toNat + 2 * (w_n53 x).toNat + 4 * (w_n54 x).toNat + (w_n55 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n57 x).toNat + (w_n58 x).toNat + 2 * (w_n59 x).toNat + 4 * (w_n60 x).toNat + 2 * (w_n61 x).toNat + 4 * (w_n62 x).toNat + 8 * (w_n63 x).toNat + 4 * (w_n64 x).toNat + 8 * (w_n65 x).toNat + 16 * (w_n66 x).toNat)) + ((w_n67 x).toNat + 2 * (w_n68 x).toNat + 4 * (w_n69 x).toNat)) + (2 * (w_n70 x).toNat + 4 * (w_n71 x).toNat + 8 * (w_n72 x).toNat)) + (4 * (w_n73 x).toNat + 8 * (w_n74 x).toNat + 16 * (w_n75 x).toNat)) + (4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 16 * (w_n78 x).toNat)) + (8 * (w_n79 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n81 x).toNat)) = (16 * (w_n33 x).toNat + 2 * (w_n59 x).toNat + 2 * (w_n61 x).toNat + 16 * (w_n66 x).toNat + (w_n67 x).toNat + 2 * (w_n68 x).toNat + 2 * (w_n70 x).toNat + 4 * (w_n73 x).toNat + 16 * (w_n75 x).toNat + 4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 16 * (w_n78 x).toNat + 8 * (w_n79 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n81 x).toNat) + ((w_n19 x).toNat + (w_n22 x).toNat + (w_n25 x).toNat + (w_n52 x).toNat + (w_n55 x).toNat + (w_n58 x).toNat + 2 * (w_n20 x).toNat + 2 * (w_n23 x).toNat + 2 * (w_n26 x).toNat + 2 * (w_n28 x).toNat + 2 * (w_n53 x).toNat + 2 * (w_n56 x).toNat + 4 * (w_n21 x).toNat + 4 * (w_n24 x).toNat + 4 * (w_n27 x).toNat + 4 * (w_n29 x).toNat + 4 * (w_n31 x).toNat + 4 * (w_n54 x).toNat + 4 * (w_n57 x).toNat + 4 * (w_n60 x).toNat + 4 * (w_n62 x).toNat + 4 * (w_n64 x).toNat + 4 * (w_n69 x).toNat + 4 * (w_n71 x).toNat + 8 * (w_n30 x).toNat + 8 * (w_n32 x).toNat + 8 * (w_n63 x).toNat + 8 * (w_n65 x).toNat + 8 * (w_n72 x).toNat + 8 * (w_n74 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s31 (x : Nat → Bool) : I_t31 x = pc x 463 96 := by
  have hl := s15 x
  have hr := s30 x
  have : pc x 463 96 = pc x 463 48 + pc x 511 48 := pc_add x 463 48 48
  unfold I_t31
  omega
def I_b32 (x : Nat → Bool) : Nat := 0 + (x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat
theorem b32 (x : Nat → Bool) : I_b32 x = (x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat := by
  unfold I_b32
  omega
def I_t32 (x : Nat → Bool) : Nat := I_b32 x
theorem t32 (x : Nat → Bool) : I_t32 x = (w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat := by
  have hs : ((I_b32 x) + ((x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat)) = (((x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat) + ((w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat)) := (add_eq (b32 x) (e27 x))
  have e1 : ((I_b32 x) + ((x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat)) = (I_t32 x) + ((x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat) := by unfold I_t32; ac_rfl
  have e2 : (((x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat) + ((w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat)) = ((w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat) + ((x 595).toNat + (x 596).toNat + (x 597).toNat + (x 598).toNat + (x 599).toNat + (x 600).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s32 (x : Nat → Bool) : I_t32 x = pc x 595 6 := rfl
def I_b33 (x : Nat → Bool) : Nat := 0 + (x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat
theorem b33 (x : Nat → Bool) : I_b33 x = (x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat := by
  unfold I_b33
  omega
def I_t33 (x : Nat → Bool) : Nat := I_b33 x
theorem t33 (x : Nat → Bool) : I_t33 x = (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat := by
  have hs : ((I_b33 x) + ((x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat)) = (((x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat) + ((w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat)) := (add_eq (b33 x) (e28 x))
  have e1 : ((I_b33 x) + ((x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat)) = (I_t33 x) + ((x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat) := by unfold I_t33; ac_rfl
  have e2 : (((x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat) + ((w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat)) = ((w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat) + ((x 601).toNat + (x 602).toNat + (x 603).toNat + (x 604).toNat + (x 605).toNat + (x 606).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s33 (x : Nat → Bool) : I_t33 x = pc x 601 6 := rfl
def I_t34 (x : Nat → Bool) : Nat := I_t32 x + I_t33 x
theorem t34 (x : Nat → Bool) : I_t34 x = (w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat + (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat := by
  have hs : ((I_t32 x) + (I_t33 x)) = (((w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat) + ((w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat)) := (add_eq (t32 x) (t33 x))
  have e1 : ((I_t32 x) + (I_t33 x)) = I_t34 x := by unfold I_t34; ac_rfl
  have e2 : (((w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat) + ((w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat)) = (w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat + (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s34 (x : Nat → Bool) : I_t34 x = pc x 595 12 := by
  have hl := s32 x
  have hr := s33 x
  have : pc x 595 12 = pc x 595 6 + pc x 601 6 := pc_add x 595 6 6
  unfold I_t34
  omega
def I_b35 (x : Nat → Bool) : Nat := 0 + (x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat
theorem b35 (x : Nat → Bool) : I_b35 x = (x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat := by
  unfold I_b35
  omega
def I_t35 (x : Nat → Bool) : Nat := I_b35 x
theorem t35 (x : Nat → Bool) : I_t35 x = (w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat := by
  have hs : ((I_b35 x) + ((x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat)) = (((x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat) + ((w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat)) := (add_eq (b35 x) (e29 x))
  have e1 : ((I_b35 x) + ((x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat)) = (I_t35 x) + ((x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat) := by unfold I_t35; ac_rfl
  have e2 : (((x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat) + ((w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat)) = ((w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat) + ((x 589).toNat + (x 590).toNat + (x 591).toNat + (x 592).toNat + (x 593).toNat + (x 594).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s35 (x : Nat → Bool) : I_t35 x = pc x 589 6 := rfl
def I_b36 (x : Nat → Bool) : Nat := 0 + (x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat
theorem b36 (x : Nat → Bool) : I_b36 x = (x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat := by
  unfold I_b36
  omega
def I_t36 (x : Nat → Bool) : Nat := I_b36 x
theorem t36 (x : Nat → Bool) : I_t36 x = (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat := by
  have hs : ((I_b36 x) + ((x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat)) = (((x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat) + ((w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat)) := (add_eq (b36 x) (e30 x))
  have e1 : ((I_b36 x) + ((x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat)) = (I_t36 x) + ((x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat) := by unfold I_t36; ac_rfl
  have e2 : (((x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat) + ((w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat)) = ((w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat) + ((x 583).toNat + (x 584).toNat + (x 585).toNat + (x 586).toNat + (x 587).toNat + (x 588).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s36 (x : Nat → Bool) : I_t36 x = pc x 583 6 := rfl
def I_t37 (x : Nat → Bool) : Nat := I_t35 x + I_t36 x
theorem t37 (x : Nat → Bool) : I_t37 x = (w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat + (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat := by
  have hs : ((I_t35 x) + (I_t36 x)) = (((w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat) + ((w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat)) := (add_eq (t35 x) (t36 x))
  have e1 : ((I_t35 x) + (I_t36 x)) = I_t37 x := by unfold I_t37; ac_rfl
  have e2 : (((w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat) + ((w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat)) = (w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat + (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s37 (x : Nat → Bool) : I_t37 x = pc x 583 12 := by
  have hl := s35 x
  have hr := s36 x
  have : pc x 583 12 = pc x 583 6 + pc x 589 6 := pc_add x 583 6 6
  unfold I_t37
  omega
def I_t38 (x : Nat → Bool) : Nat := I_t34 x + I_t37 x
theorem t38 (x : Nat → Bool) : I_t38 x = (w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat + (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat + (w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat + (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat := by
  have hs : ((I_t34 x) + (I_t37 x)) = (((w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat + (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat) + ((w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat + (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat)) := (add_eq (t34 x) (t37 x))
  have e1 : ((I_t34 x) + (I_t37 x)) = I_t38 x := by unfold I_t38; ac_rfl
  have e2 : (((w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat + (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat) + ((w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat + (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat)) = (w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat + (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat + (w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat + (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s38 (x : Nat → Bool) : I_t38 x = pc x 583 24 := by
  have hl := s34 x
  have hr := s37 x
  have : pc x 583 24 = pc x 583 12 + pc x 595 12 := pc_add x 583 12 12
  unfold I_t38
  omega
def I_b39 (x : Nat → Bool) : Nat := 0 + (x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat
theorem b39 (x : Nat → Bool) : I_b39 x = (x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat := by
  unfold I_b39
  omega
def I_t39 (x : Nat → Bool) : Nat := I_b39 x
theorem t39 (x : Nat → Bool) : I_t39 x = (w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat := by
  have hs : ((I_b39 x) + ((x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat)) = (((x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat) + ((w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat)) := (add_eq (b39 x) (e31 x))
  have e1 : ((I_b39 x) + ((x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat)) = (I_t39 x) + ((x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat) := by unfold I_t39; ac_rfl
  have e2 : (((x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat) + ((w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat)) = ((w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat) + ((x 565).toNat + (x 566).toNat + (x 567).toNat + (x 568).toNat + (x 569).toNat + (x 570).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s39 (x : Nat → Bool) : I_t39 x = pc x 565 6 := rfl
def I_b40 (x : Nat → Bool) : Nat := 0 + (x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat
theorem b40 (x : Nat → Bool) : I_b40 x = (x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat := by
  unfold I_b40
  omega
def I_t40 (x : Nat → Bool) : Nat := I_b40 x
theorem t40 (x : Nat → Bool) : I_t40 x = (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat := by
  have hs : ((I_b40 x) + ((x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat)) = (((x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat) + ((w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat)) := (add_eq (b40 x) (e32 x))
  have e1 : ((I_b40 x) + ((x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat)) = (I_t40 x) + ((x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat) := by unfold I_t40; ac_rfl
  have e2 : (((x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat) + ((w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat)) = ((w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat) + ((x 559).toNat + (x 560).toNat + (x 561).toNat + (x 562).toNat + (x 563).toNat + (x 564).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s40 (x : Nat → Bool) : I_t40 x = pc x 559 6 := rfl
def I_t41 (x : Nat → Bool) : Nat := I_t39 x + I_t40 x
theorem t41 (x : Nat → Bool) : I_t41 x = (w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat + (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat := by
  have hs : ((I_t39 x) + (I_t40 x)) = (((w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat) + ((w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat)) := (add_eq (t39 x) (t40 x))
  have e1 : ((I_t39 x) + (I_t40 x)) = I_t41 x := by unfold I_t41; ac_rfl
  have e2 : (((w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat) + ((w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat)) = (w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat + (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s41 (x : Nat → Bool) : I_t41 x = pc x 559 12 := by
  have hl := s39 x
  have hr := s40 x
  have : pc x 559 12 = pc x 559 6 + pc x 565 6 := pc_add x 559 6 6
  unfold I_t41
  omega
def I_b42 (x : Nat → Bool) : Nat := 0 + (x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat
theorem b42 (x : Nat → Bool) : I_b42 x = (x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat := by
  unfold I_b42
  omega
def I_t42 (x : Nat → Bool) : Nat := I_b42 x
theorem t42 (x : Nat → Bool) : I_t42 x = (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat := by
  have hs : ((I_b42 x) + ((x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat)) = (((x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat) + ((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat)) := (add_eq (b42 x) (e33 x))
  have e1 : ((I_b42 x) + ((x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat)) = (I_t42 x) + ((x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat) := by unfold I_t42; ac_rfl
  have e2 : (((x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat) + ((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat)) = ((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat) + ((x 577).toNat + (x 578).toNat + (x 579).toNat + (x 580).toNat + (x 581).toNat + (x 582).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s42 (x : Nat → Bool) : I_t42 x = pc x 577 6 := rfl
def I_b43 (x : Nat → Bool) : Nat := 0 + (x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat
theorem b43 (x : Nat → Bool) : I_b43 x = (x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat := by
  unfold I_b43
  omega
def I_t43 (x : Nat → Bool) : Nat := I_b43 x
theorem t43 (x : Nat → Bool) : I_t43 x = (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat := by
  have hs : ((I_b43 x) + ((x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat)) = (((x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat) + ((w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat)) := (add_eq (b43 x) (e34 x))
  have e1 : ((I_b43 x) + ((x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat)) = (I_t43 x) + ((x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat) := by unfold I_t43; ac_rfl
  have e2 : (((x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat) + ((w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat)) = ((w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat) + ((x 571).toNat + (x 572).toNat + (x 573).toNat + (x 574).toNat + (x 575).toNat + (x 576).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s43 (x : Nat → Bool) : I_t43 x = pc x 571 6 := rfl
def I_t44 (x : Nat → Bool) : Nat := I_t42 x + I_t43 x
theorem t44 (x : Nat → Bool) : I_t44 x = (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat := by
  have hs : ((I_t42 x) + (I_t43 x)) = (((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat) + ((w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat)) := (add_eq (t42 x) (t43 x))
  have e1 : ((I_t42 x) + (I_t43 x)) = I_t44 x := by unfold I_t44; ac_rfl
  have e2 : (((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat) + ((w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat)) = (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s44 (x : Nat → Bool) : I_t44 x = pc x 571 12 := by
  have hl := s42 x
  have hr := s43 x
  have : pc x 571 12 = pc x 571 6 + pc x 577 6 := pc_add x 571 6 6
  unfold I_t44
  omega
def I_t45 (x : Nat → Bool) : Nat := I_t41 x + I_t44 x
theorem t45 (x : Nat → Bool) : I_t45 x = (w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat + (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat + (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat := by
  have hs : ((I_t41 x) + (I_t44 x)) = (((w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat + (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat) + ((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat)) := (add_eq (t41 x) (t44 x))
  have e1 : ((I_t41 x) + (I_t44 x)) = I_t45 x := by unfold I_t45; ac_rfl
  have e2 : (((w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat + (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat) + ((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat)) = (w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat + (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat + (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s45 (x : Nat → Bool) : I_t45 x = pc x 559 24 := by
  have hl := s41 x
  have hr := s44 x
  have : pc x 559 24 = pc x 559 12 + pc x 571 12 := pc_add x 559 12 12
  unfold I_t45
  omega
def I_t46 (x : Nat → Bool) : Nat := I_t38 x + I_t45 x
theorem t46 (x : Nat → Bool) : I_t46 x = (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat + (w_n106 x).toNat + 2 * (w_n107 x).toNat + 4 * (w_n108 x).toNat + 2 * (w_n109 x).toNat + 4 * (w_n110 x).toNat + 8 * (w_n111 x).toNat + 4 * (w_n112 x).toNat + 8 * (w_n113 x).toNat + 16 * (w_n114 x).toNat := by
  have hs : (((((I_t38 x) + (I_t45 x)) + ((w_n82 x).toNat + (w_n85 x).toNat + (w_n88 x).toNat + (w_n91 x).toNat + (w_n94 x).toNat + (w_n97 x).toNat)) + (2 * (w_n83 x).toNat + 2 * (w_n86 x).toNat + 2 * (w_n89 x).toNat + 2 * (w_n92 x).toNat + 2 * (w_n95 x).toNat + 2 * (w_n98 x).toNat)) + (4 * (w_n84 x).toNat + 4 * (w_n87 x).toNat + 4 * (w_n90 x).toNat + 4 * (w_n93 x).toNat + 4 * (w_n96 x).toNat + 4 * (w_n99 x).toNat)) = ((((((w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat + (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat + (w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat + (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat) + ((w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat + (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat + (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat)) + ((w_n106 x).toNat + 2 * (w_n107 x).toNat + 4 * (w_n108 x).toNat)) + (2 * (w_n109 x).toNat + 4 * (w_n110 x).toNat + 8 * (w_n111 x).toNat)) + (4 * (w_n112 x).toNat + 8 * (w_n113 x).toNat + 16 * (w_n114 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t38 x) (t45 x)) (e35 x)) (e36 x)) (e37 x))
  have e1 : (((((I_t38 x) + (I_t45 x)) + ((w_n82 x).toNat + (w_n85 x).toNat + (w_n88 x).toNat + (w_n91 x).toNat + (w_n94 x).toNat + (w_n97 x).toNat)) + (2 * (w_n83 x).toNat + 2 * (w_n86 x).toNat + 2 * (w_n89 x).toNat + 2 * (w_n92 x).toNat + 2 * (w_n95 x).toNat + 2 * (w_n98 x).toNat)) + (4 * (w_n84 x).toNat + 4 * (w_n87 x).toNat + 4 * (w_n90 x).toNat + 4 * (w_n93 x).toNat + 4 * (w_n96 x).toNat + 4 * (w_n99 x).toNat)) = (I_t46 x) + ((w_n82 x).toNat + (w_n85 x).toNat + (w_n88 x).toNat + (w_n91 x).toNat + (w_n94 x).toNat + (w_n97 x).toNat + 2 * (w_n83 x).toNat + 2 * (w_n86 x).toNat + 2 * (w_n89 x).toNat + 2 * (w_n92 x).toNat + 2 * (w_n95 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n84 x).toNat + 4 * (w_n87 x).toNat + 4 * (w_n90 x).toNat + 4 * (w_n93 x).toNat + 4 * (w_n96 x).toNat + 4 * (w_n99 x).toNat) := by unfold I_t46; ac_rfl
  have e2 : ((((((w_n82 x).toNat + 2 * (w_n83 x).toNat + 4 * (w_n84 x).toNat + (w_n85 x).toNat + 2 * (w_n86 x).toNat + 4 * (w_n87 x).toNat + (w_n88 x).toNat + 2 * (w_n89 x).toNat + 4 * (w_n90 x).toNat + (w_n91 x).toNat + 2 * (w_n92 x).toNat + 4 * (w_n93 x).toNat) + ((w_n94 x).toNat + 2 * (w_n95 x).toNat + 4 * (w_n96 x).toNat + (w_n97 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n99 x).toNat + (w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat)) + ((w_n106 x).toNat + 2 * (w_n107 x).toNat + 4 * (w_n108 x).toNat)) + (2 * (w_n109 x).toNat + 4 * (w_n110 x).toNat + 8 * (w_n111 x).toNat)) + (4 * (w_n112 x).toNat + 8 * (w_n113 x).toNat + 16 * (w_n114 x).toNat)) = ((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat + (w_n106 x).toNat + 2 * (w_n107 x).toNat + 4 * (w_n108 x).toNat + 2 * (w_n109 x).toNat + 4 * (w_n110 x).toNat + 8 * (w_n111 x).toNat + 4 * (w_n112 x).toNat + 8 * (w_n113 x).toNat + 16 * (w_n114 x).toNat) + ((w_n82 x).toNat + (w_n85 x).toNat + (w_n88 x).toNat + (w_n91 x).toNat + (w_n94 x).toNat + (w_n97 x).toNat + 2 * (w_n83 x).toNat + 2 * (w_n86 x).toNat + 2 * (w_n89 x).toNat + 2 * (w_n92 x).toNat + 2 * (w_n95 x).toNat + 2 * (w_n98 x).toNat + 4 * (w_n84 x).toNat + 4 * (w_n87 x).toNat + 4 * (w_n90 x).toNat + 4 * (w_n93 x).toNat + 4 * (w_n96 x).toNat + 4 * (w_n99 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s46 (x : Nat → Bool) : I_t46 x = pc x 559 48 := by
  have hl := s38 x
  have hr := s45 x
  have : pc x 559 48 = pc x 559 24 + pc x 583 24 := pc_add x 559 24 24
  unfold I_t46
  omega
def I_b47 (x : Nat → Bool) : Nat := 0 + (x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat
theorem b47 (x : Nat → Bool) : I_b47 x = (x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat := by
  unfold I_b47
  omega
def I_t47 (x : Nat → Bool) : Nat := I_b47 x
theorem t47 (x : Nat → Bool) : I_t47 x = (w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat := by
  have hs : ((I_b47 x) + ((x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat)) = (((x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat) + ((w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat)) := (add_eq (b47 x) (e38 x))
  have e1 : ((I_b47 x) + ((x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat)) = (I_t47 x) + ((x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat) := by unfold I_t47; ac_rfl
  have e2 : (((x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat) + ((w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat)) = ((w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat) + ((x 607).toNat + (x 608).toNat + (x 609).toNat + (x 610).toNat + (x 611).toNat + (x 612).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s47 (x : Nat → Bool) : I_t47 x = pc x 607 6 := rfl
def I_b48 (x : Nat → Bool) : Nat := 0 + (x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat
theorem b48 (x : Nat → Bool) : I_b48 x = (x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat := by
  unfold I_b48
  omega
def I_t48 (x : Nat → Bool) : Nat := I_b48 x
theorem t48 (x : Nat → Bool) : I_t48 x = (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat := by
  have hs : ((I_b48 x) + ((x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat)) = (((x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat) + ((w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat)) := (add_eq (b48 x) (e39 x))
  have e1 : ((I_b48 x) + ((x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat)) = (I_t48 x) + ((x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat) := by unfold I_t48; ac_rfl
  have e2 : (((x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat) + ((w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat)) = ((w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat) + ((x 613).toNat + (x 614).toNat + (x 615).toNat + (x 616).toNat + (x 617).toNat + (x 618).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s48 (x : Nat → Bool) : I_t48 x = pc x 613 6 := rfl
def I_t49 (x : Nat → Bool) : Nat := I_t47 x + I_t48 x
theorem t49 (x : Nat → Bool) : I_t49 x = (w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat + (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat := by
  have hs : ((I_t47 x) + (I_t48 x)) = (((w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat) + ((w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat)) := (add_eq (t47 x) (t48 x))
  have e1 : ((I_t47 x) + (I_t48 x)) = I_t49 x := by unfold I_t49; ac_rfl
  have e2 : (((w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat) + ((w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat)) = (w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat + (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s49 (x : Nat → Bool) : I_t49 x = pc x 607 12 := by
  have hl := s47 x
  have hr := s48 x
  have : pc x 607 12 = pc x 607 6 + pc x 613 6 := pc_add x 607 6 6
  unfold I_t49
  omega
def I_b50 (x : Nat → Bool) : Nat := 0 + (x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat
theorem b50 (x : Nat → Bool) : I_b50 x = (x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat := by
  unfold I_b50
  omega
def I_t50 (x : Nat → Bool) : Nat := I_b50 x
theorem t50 (x : Nat → Bool) : I_t50 x = (w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat := by
  have hs : ((I_b50 x) + ((x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat)) = (((x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat) + ((w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat)) := (add_eq (b50 x) (e40 x))
  have e1 : ((I_b50 x) + ((x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat)) = (I_t50 x) + ((x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat) := by unfold I_t50; ac_rfl
  have e2 : (((x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat) + ((w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat)) = ((w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat) + ((x 619).toNat + (x 620).toNat + (x 621).toNat + (x 622).toNat + (x 623).toNat + (x 624).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s50 (x : Nat → Bool) : I_t50 x = pc x 619 6 := rfl
def I_b51 (x : Nat → Bool) : Nat := 0 + (x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat
theorem b51 (x : Nat → Bool) : I_b51 x = (x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat := by
  unfold I_b51
  omega
def I_t51 (x : Nat → Bool) : Nat := I_b51 x
theorem t51 (x : Nat → Bool) : I_t51 x = (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat := by
  have hs : ((I_b51 x) + ((x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat)) = (((x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat) + ((w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat)) := (add_eq (b51 x) (e41 x))
  have e1 : ((I_b51 x) + ((x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat)) = (I_t51 x) + ((x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat) := by unfold I_t51; ac_rfl
  have e2 : (((x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat) + ((w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat)) = ((w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat) + ((x 625).toNat + (x 626).toNat + (x 627).toNat + (x 628).toNat + (x 629).toNat + (x 630).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s51 (x : Nat → Bool) : I_t51 x = pc x 625 6 := rfl
def I_t52 (x : Nat → Bool) : Nat := I_t50 x + I_t51 x
theorem t52 (x : Nat → Bool) : I_t52 x = (w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat + (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat := by
  have hs : ((I_t50 x) + (I_t51 x)) = (((w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat) + ((w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat)) := (add_eq (t50 x) (t51 x))
  have e1 : ((I_t50 x) + (I_t51 x)) = I_t52 x := by unfold I_t52; ac_rfl
  have e2 : (((w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat) + ((w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat)) = (w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat + (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s52 (x : Nat → Bool) : I_t52 x = pc x 619 12 := by
  have hl := s50 x
  have hr := s51 x
  have : pc x 619 12 = pc x 619 6 + pc x 625 6 := pc_add x 619 6 6
  unfold I_t52
  omega
def I_t53 (x : Nat → Bool) : Nat := I_t49 x + I_t52 x
theorem t53 (x : Nat → Bool) : I_t53 x = (w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat + (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat + (w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat + (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat := by
  have hs : ((I_t49 x) + (I_t52 x)) = (((w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat + (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat) + ((w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat + (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat)) := (add_eq (t49 x) (t52 x))
  have e1 : ((I_t49 x) + (I_t52 x)) = I_t53 x := by unfold I_t53; ac_rfl
  have e2 : (((w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat + (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat) + ((w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat + (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat)) = (w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat + (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat + (w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat + (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s53 (x : Nat → Bool) : I_t53 x = pc x 607 24 := by
  have hl := s49 x
  have hr := s52 x
  have : pc x 607 24 = pc x 607 12 + pc x 619 12 := pc_add x 607 12 12
  unfold I_t53
  omega
def I_b54 (x : Nat → Bool) : Nat := 0 + (x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat
theorem b54 (x : Nat → Bool) : I_b54 x = (x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat := by
  unfold I_b54
  omega
def I_t54 (x : Nat → Bool) : Nat := I_b54 x
theorem t54 (x : Nat → Bool) : I_t54 x = (w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat := by
  have hs : ((I_b54 x) + ((x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat)) = (((x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat) + ((w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat)) := (add_eq (b54 x) (e42 x))
  have e1 : ((I_b54 x) + ((x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat)) = (I_t54 x) + ((x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat) := by unfold I_t54; ac_rfl
  have e2 : (((x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat) + ((w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat)) = ((w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat) + ((x 643).toNat + (x 644).toNat + (x 645).toNat + (x 646).toNat + (x 647).toNat + (x 648).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s54 (x : Nat → Bool) : I_t54 x = pc x 643 6 := rfl
def I_b55 (x : Nat → Bool) : Nat := 0 + (x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat
theorem b55 (x : Nat → Bool) : I_b55 x = (x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat := by
  unfold I_b55
  omega
def I_t55 (x : Nat → Bool) : Nat := I_b55 x
theorem t55 (x : Nat → Bool) : I_t55 x = (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat := by
  have hs : ((I_b55 x) + ((x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat)) = (((x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat) + ((w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat)) := (add_eq (b55 x) (e43 x))
  have e1 : ((I_b55 x) + ((x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat)) = (I_t55 x) + ((x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat) := by unfold I_t55; ac_rfl
  have e2 : (((x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat) + ((w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat)) = ((w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat) + ((x 649).toNat + (x 650).toNat + (x 651).toNat + (x 652).toNat + (x 653).toNat + (x 654).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s55 (x : Nat → Bool) : I_t55 x = pc x 649 6 := rfl
def I_t56 (x : Nat → Bool) : Nat := I_t54 x + I_t55 x
theorem t56 (x : Nat → Bool) : I_t56 x = (w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat + (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat := by
  have hs : ((I_t54 x) + (I_t55 x)) = (((w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat) + ((w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat)) := (add_eq (t54 x) (t55 x))
  have e1 : ((I_t54 x) + (I_t55 x)) = I_t56 x := by unfold I_t56; ac_rfl
  have e2 : (((w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat) + ((w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat)) = (w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat + (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s56 (x : Nat → Bool) : I_t56 x = pc x 643 12 := by
  have hl := s54 x
  have hr := s55 x
  have : pc x 643 12 = pc x 643 6 + pc x 649 6 := pc_add x 643 6 6
  unfold I_t56
  omega
def I_b57 (x : Nat → Bool) : Nat := 0 + (x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat
theorem b57 (x : Nat → Bool) : I_b57 x = (x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat := by
  unfold I_b57
  omega
def I_t57 (x : Nat → Bool) : Nat := I_b57 x
theorem t57 (x : Nat → Bool) : I_t57 x = (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat := by
  have hs : ((I_b57 x) + ((x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat)) = (((x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat) + ((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat)) := (add_eq (b57 x) (e44 x))
  have e1 : ((I_b57 x) + ((x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat)) = (I_t57 x) + ((x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat) := by unfold I_t57; ac_rfl
  have e2 : (((x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat) + ((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat)) = ((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat) + ((x 637).toNat + (x 638).toNat + (x 639).toNat + (x 640).toNat + (x 641).toNat + (x 642).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s57 (x : Nat → Bool) : I_t57 x = pc x 637 6 := rfl
def I_b58 (x : Nat → Bool) : Nat := 0 + (x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat
theorem b58 (x : Nat → Bool) : I_b58 x = (x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat := by
  unfold I_b58
  omega
def I_t58 (x : Nat → Bool) : Nat := I_b58 x
theorem t58 (x : Nat → Bool) : I_t58 x = (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat := by
  have hs : ((I_b58 x) + ((x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat)) = (((x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat) + ((w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat)) := (add_eq (b58 x) (e45 x))
  have e1 : ((I_b58 x) + ((x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat)) = (I_t58 x) + ((x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat) := by unfold I_t58; ac_rfl
  have e2 : (((x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat) + ((w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat)) = ((w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat) + ((x 631).toNat + (x 632).toNat + (x 633).toNat + (x 634).toNat + (x 635).toNat + (x 636).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s58 (x : Nat → Bool) : I_t58 x = pc x 631 6 := rfl
def I_t59 (x : Nat → Bool) : Nat := I_t57 x + I_t58 x
theorem t59 (x : Nat → Bool) : I_t59 x = (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat := by
  have hs : ((I_t57 x) + (I_t58 x)) = (((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat) + ((w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat)) := (add_eq (t57 x) (t58 x))
  have e1 : ((I_t57 x) + (I_t58 x)) = I_t59 x := by unfold I_t59; ac_rfl
  have e2 : (((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat) + ((w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat)) = (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s59 (x : Nat → Bool) : I_t59 x = pc x 631 12 := by
  have hl := s57 x
  have hr := s58 x
  have : pc x 631 12 = pc x 631 6 + pc x 637 6 := pc_add x 631 6 6
  unfold I_t59
  omega
def I_t60 (x : Nat → Bool) : Nat := I_t56 x + I_t59 x
theorem t60 (x : Nat → Bool) : I_t60 x = (w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat + (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat + (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat := by
  have hs : ((I_t56 x) + (I_t59 x)) = (((w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat + (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat) + ((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat)) := (add_eq (t56 x) (t59 x))
  have e1 : ((I_t56 x) + (I_t59 x)) = I_t60 x := by unfold I_t60; ac_rfl
  have e2 : (((w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat + (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat) + ((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat)) = (w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat + (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat + (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s60 (x : Nat → Bool) : I_t60 x = pc x 631 24 := by
  have hl := s56 x
  have hr := s59 x
  have : pc x 631 24 = pc x 631 12 + pc x 643 12 := pc_add x 631 12 12
  unfold I_t60
  omega
def I_t61 (x : Nat → Bool) : Nat := I_t53 x + I_t60 x
theorem t61 (x : Nat → Bool) : I_t61 x = (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat + (w_n139 x).toNat + 2 * (w_n140 x).toNat + 4 * (w_n141 x).toNat + 2 * (w_n142 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n144 x).toNat + 4 * (w_n145 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n147 x).toNat := by
  have hs : (((((I_t53 x) + (I_t60 x)) + ((w_n115 x).toNat + (w_n118 x).toNat + (w_n121 x).toNat + (w_n124 x).toNat + (w_n127 x).toNat + (w_n130 x).toNat)) + (2 * (w_n116 x).toNat + 2 * (w_n119 x).toNat + 2 * (w_n122 x).toNat + 2 * (w_n125 x).toNat + 2 * (w_n128 x).toNat + 2 * (w_n131 x).toNat)) + (4 * (w_n117 x).toNat + 4 * (w_n120 x).toNat + 4 * (w_n123 x).toNat + 4 * (w_n126 x).toNat + 4 * (w_n129 x).toNat + 4 * (w_n132 x).toNat)) = ((((((w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat + (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat + (w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat + (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat) + ((w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat + (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat + (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat)) + ((w_n139 x).toNat + 2 * (w_n140 x).toNat + 4 * (w_n141 x).toNat)) + (2 * (w_n142 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n144 x).toNat)) + (4 * (w_n145 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n147 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t53 x) (t60 x)) (e46 x)) (e47 x)) (e48 x))
  have e1 : (((((I_t53 x) + (I_t60 x)) + ((w_n115 x).toNat + (w_n118 x).toNat + (w_n121 x).toNat + (w_n124 x).toNat + (w_n127 x).toNat + (w_n130 x).toNat)) + (2 * (w_n116 x).toNat + 2 * (w_n119 x).toNat + 2 * (w_n122 x).toNat + 2 * (w_n125 x).toNat + 2 * (w_n128 x).toNat + 2 * (w_n131 x).toNat)) + (4 * (w_n117 x).toNat + 4 * (w_n120 x).toNat + 4 * (w_n123 x).toNat + 4 * (w_n126 x).toNat + 4 * (w_n129 x).toNat + 4 * (w_n132 x).toNat)) = (I_t61 x) + ((w_n115 x).toNat + (w_n118 x).toNat + (w_n121 x).toNat + (w_n124 x).toNat + (w_n127 x).toNat + (w_n130 x).toNat + 2 * (w_n116 x).toNat + 2 * (w_n119 x).toNat + 2 * (w_n122 x).toNat + 2 * (w_n125 x).toNat + 2 * (w_n128 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n117 x).toNat + 4 * (w_n120 x).toNat + 4 * (w_n123 x).toNat + 4 * (w_n126 x).toNat + 4 * (w_n129 x).toNat + 4 * (w_n132 x).toNat) := by unfold I_t61; ac_rfl
  have e2 : ((((((w_n115 x).toNat + 2 * (w_n116 x).toNat + 4 * (w_n117 x).toNat + (w_n118 x).toNat + 2 * (w_n119 x).toNat + 4 * (w_n120 x).toNat + (w_n121 x).toNat + 2 * (w_n122 x).toNat + 4 * (w_n123 x).toNat + (w_n124 x).toNat + 2 * (w_n125 x).toNat + 4 * (w_n126 x).toNat) + ((w_n127 x).toNat + 2 * (w_n128 x).toNat + 4 * (w_n129 x).toNat + (w_n130 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n132 x).toNat + (w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat)) + ((w_n139 x).toNat + 2 * (w_n140 x).toNat + 4 * (w_n141 x).toNat)) + (2 * (w_n142 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n144 x).toNat)) + (4 * (w_n145 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n147 x).toNat)) = ((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat + (w_n139 x).toNat + 2 * (w_n140 x).toNat + 4 * (w_n141 x).toNat + 2 * (w_n142 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n144 x).toNat + 4 * (w_n145 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n147 x).toNat) + ((w_n115 x).toNat + (w_n118 x).toNat + (w_n121 x).toNat + (w_n124 x).toNat + (w_n127 x).toNat + (w_n130 x).toNat + 2 * (w_n116 x).toNat + 2 * (w_n119 x).toNat + 2 * (w_n122 x).toNat + 2 * (w_n125 x).toNat + 2 * (w_n128 x).toNat + 2 * (w_n131 x).toNat + 4 * (w_n117 x).toNat + 4 * (w_n120 x).toNat + 4 * (w_n123 x).toNat + 4 * (w_n126 x).toNat + 4 * (w_n129 x).toNat + 4 * (w_n132 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s61 (x : Nat → Bool) : I_t61 x = pc x 607 48 := by
  have hl := s53 x
  have hr := s60 x
  have : pc x 607 48 = pc x 607 24 + pc x 631 24 := pc_add x 607 24 24
  unfold I_t61
  omega
def I_t62 (x : Nat → Bool) : Nat := I_t46 x + I_t61 x
theorem t62 (x : Nat → Bool) : I_t62 x = 16 * (w_n114 x).toNat + 2 * (w_n140 x).toNat + 2 * (w_n142 x).toNat + 16 * (w_n147 x).toNat + (w_n148 x).toNat + 2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n154 x).toNat + 16 * (w_n156 x).toNat + 4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat := by
  have hs : (((((((I_t46 x) + (I_t61 x)) + ((w_n100 x).toNat + (w_n103 x).toNat + (w_n106 x).toNat + (w_n133 x).toNat + (w_n136 x).toNat + (w_n139 x).toNat)) + (2 * (w_n101 x).toNat + 2 * (w_n104 x).toNat + 2 * (w_n107 x).toNat + 2 * (w_n109 x).toNat + 2 * (w_n134 x).toNat + 2 * (w_n137 x).toNat)) + (4 * (w_n102 x).toNat + 4 * (w_n105 x).toNat + 4 * (w_n108 x).toNat + 4 * (w_n110 x).toNat + 4 * (w_n112 x).toNat + 4 * (w_n135 x).toNat)) + (4 * (w_n138 x).toNat + 4 * (w_n141 x).toNat + 4 * (w_n143 x).toNat + 4 * (w_n145 x).toNat + 4 * (w_n150 x).toNat + 4 * (w_n152 x).toNat)) + (8 * (w_n111 x).toNat + 8 * (w_n113 x).toNat + 8 * (w_n144 x).toNat + 8 * (w_n146 x).toNat + 8 * (w_n153 x).toNat + 8 * (w_n155 x).toNat)) = ((((((((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat + (w_n106 x).toNat + 2 * (w_n107 x).toNat + 4 * (w_n108 x).toNat + 2 * (w_n109 x).toNat + 4 * (w_n110 x).toNat + 8 * (w_n111 x).toNat + 4 * (w_n112 x).toNat + 8 * (w_n113 x).toNat + 16 * (w_n114 x).toNat) + ((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat + (w_n139 x).toNat + 2 * (w_n140 x).toNat + 4 * (w_n141 x).toNat + 2 * (w_n142 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n144 x).toNat + 4 * (w_n145 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n147 x).toNat)) + ((w_n148 x).toNat + 2 * (w_n149 x).toNat + 4 * (w_n150 x).toNat)) + (2 * (w_n151 x).toNat + 4 * (w_n152 x).toNat + 8 * (w_n153 x).toNat)) + (4 * (w_n154 x).toNat + 8 * (w_n155 x).toNat + 16 * (w_n156 x).toNat)) + (4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat)) + (8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t46 x) (t61 x)) (e49 x)) (e50 x)) (e51 x)) (e52 x)) (e53 x))
  have e1 : (((((((I_t46 x) + (I_t61 x)) + ((w_n100 x).toNat + (w_n103 x).toNat + (w_n106 x).toNat + (w_n133 x).toNat + (w_n136 x).toNat + (w_n139 x).toNat)) + (2 * (w_n101 x).toNat + 2 * (w_n104 x).toNat + 2 * (w_n107 x).toNat + 2 * (w_n109 x).toNat + 2 * (w_n134 x).toNat + 2 * (w_n137 x).toNat)) + (4 * (w_n102 x).toNat + 4 * (w_n105 x).toNat + 4 * (w_n108 x).toNat + 4 * (w_n110 x).toNat + 4 * (w_n112 x).toNat + 4 * (w_n135 x).toNat)) + (4 * (w_n138 x).toNat + 4 * (w_n141 x).toNat + 4 * (w_n143 x).toNat + 4 * (w_n145 x).toNat + 4 * (w_n150 x).toNat + 4 * (w_n152 x).toNat)) + (8 * (w_n111 x).toNat + 8 * (w_n113 x).toNat + 8 * (w_n144 x).toNat + 8 * (w_n146 x).toNat + 8 * (w_n153 x).toNat + 8 * (w_n155 x).toNat)) = (I_t62 x) + ((w_n100 x).toNat + (w_n103 x).toNat + (w_n106 x).toNat + (w_n133 x).toNat + (w_n136 x).toNat + (w_n139 x).toNat + 2 * (w_n101 x).toNat + 2 * (w_n104 x).toNat + 2 * (w_n107 x).toNat + 2 * (w_n109 x).toNat + 2 * (w_n134 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n102 x).toNat + 4 * (w_n105 x).toNat + 4 * (w_n108 x).toNat + 4 * (w_n110 x).toNat + 4 * (w_n112 x).toNat + 4 * (w_n135 x).toNat + 4 * (w_n138 x).toNat + 4 * (w_n141 x).toNat + 4 * (w_n143 x).toNat + 4 * (w_n145 x).toNat + 4 * (w_n150 x).toNat + 4 * (w_n152 x).toNat + 8 * (w_n111 x).toNat + 8 * (w_n113 x).toNat + 8 * (w_n144 x).toNat + 8 * (w_n146 x).toNat + 8 * (w_n153 x).toNat + 8 * (w_n155 x).toNat) := by unfold I_t62; ac_rfl
  have e2 : ((((((((w_n100 x).toNat + 2 * (w_n101 x).toNat + 4 * (w_n102 x).toNat + (w_n103 x).toNat + 2 * (w_n104 x).toNat + 4 * (w_n105 x).toNat + (w_n106 x).toNat + 2 * (w_n107 x).toNat + 4 * (w_n108 x).toNat + 2 * (w_n109 x).toNat + 4 * (w_n110 x).toNat + 8 * (w_n111 x).toNat + 4 * (w_n112 x).toNat + 8 * (w_n113 x).toNat + 16 * (w_n114 x).toNat) + ((w_n133 x).toNat + 2 * (w_n134 x).toNat + 4 * (w_n135 x).toNat + (w_n136 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n138 x).toNat + (w_n139 x).toNat + 2 * (w_n140 x).toNat + 4 * (w_n141 x).toNat + 2 * (w_n142 x).toNat + 4 * (w_n143 x).toNat + 8 * (w_n144 x).toNat + 4 * (w_n145 x).toNat + 8 * (w_n146 x).toNat + 16 * (w_n147 x).toNat)) + ((w_n148 x).toNat + 2 * (w_n149 x).toNat + 4 * (w_n150 x).toNat)) + (2 * (w_n151 x).toNat + 4 * (w_n152 x).toNat + 8 * (w_n153 x).toNat)) + (4 * (w_n154 x).toNat + 8 * (w_n155 x).toNat + 16 * (w_n156 x).toNat)) + (4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat)) + (8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat)) = (16 * (w_n114 x).toNat + 2 * (w_n140 x).toNat + 2 * (w_n142 x).toNat + 16 * (w_n147 x).toNat + (w_n148 x).toNat + 2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n154 x).toNat + 16 * (w_n156 x).toNat + 4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat) + ((w_n100 x).toNat + (w_n103 x).toNat + (w_n106 x).toNat + (w_n133 x).toNat + (w_n136 x).toNat + (w_n139 x).toNat + 2 * (w_n101 x).toNat + 2 * (w_n104 x).toNat + 2 * (w_n107 x).toNat + 2 * (w_n109 x).toNat + 2 * (w_n134 x).toNat + 2 * (w_n137 x).toNat + 4 * (w_n102 x).toNat + 4 * (w_n105 x).toNat + 4 * (w_n108 x).toNat + 4 * (w_n110 x).toNat + 4 * (w_n112 x).toNat + 4 * (w_n135 x).toNat + 4 * (w_n138 x).toNat + 4 * (w_n141 x).toNat + 4 * (w_n143 x).toNat + 4 * (w_n145 x).toNat + 4 * (w_n150 x).toNat + 4 * (w_n152 x).toNat + 8 * (w_n111 x).toNat + 8 * (w_n113 x).toNat + 8 * (w_n144 x).toNat + 8 * (w_n146 x).toNat + 8 * (w_n153 x).toNat + 8 * (w_n155 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s62 (x : Nat → Bool) : I_t62 x = pc x 559 96 := by
  have hl := s46 x
  have hr := s61 x
  have : pc x 559 96 = pc x 559 48 + pc x 607 48 := pc_add x 559 48 48
  unfold I_t62
  omega
def I_t63 (x : Nat → Bool) : Nat := I_t31 x + I_t62 x
theorem t63 (x : Nat → Bool) : I_t63 x = (w_n67 x).toNat + 4 * (w_n73 x).toNat + 4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 8 * (w_n79 x).toNat + 32 * (w_n81 x).toNat + 16 * (w_n147 x).toNat + (w_n148 x).toNat + 2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n154 x).toNat + 16 * (w_n156 x).toNat + 4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat + 2 * (w_n163 x).toNat + 4 * (w_n164 x).toNat + 8 * (w_n165 x).toNat + 16 * (w_n166 x).toNat + 32 * (w_n167 x).toNat + 64 * (w_n168 x).toNat := by
  have hs : ((((I_t31 x) + (I_t62 x)) + (2 * (w_n59 x).toNat + 2 * (w_n61 x).toNat + 2 * (w_n68 x).toNat + 2 * (w_n70 x).toNat + 2 * (w_n140 x).toNat + 2 * (w_n142 x).toNat)) + (16 * (w_n33 x).toNat + 16 * (w_n66 x).toNat + 16 * (w_n75 x).toNat + 16 * (w_n78 x).toNat + 16 * (w_n80 x).toNat + 16 * (w_n114 x).toNat)) = ((((16 * (w_n33 x).toNat + 2 * (w_n59 x).toNat + 2 * (w_n61 x).toNat + 16 * (w_n66 x).toNat + (w_n67 x).toNat + 2 * (w_n68 x).toNat + 2 * (w_n70 x).toNat + 4 * (w_n73 x).toNat + 16 * (w_n75 x).toNat + 4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 16 * (w_n78 x).toNat + 8 * (w_n79 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n81 x).toNat) + (16 * (w_n114 x).toNat + 2 * (w_n140 x).toNat + 2 * (w_n142 x).toNat + 16 * (w_n147 x).toNat + (w_n148 x).toNat + 2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n154 x).toNat + 16 * (w_n156 x).toNat + 4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat)) + (2 * (w_n163 x).toNat + 4 * (w_n164 x).toNat + 8 * (w_n165 x).toNat)) + (16 * (w_n166 x).toNat + 32 * (w_n167 x).toNat + 64 * (w_n168 x).toNat)) := (add_eq (add_eq (add_eq (t31 x) (t62 x)) (e54 x)) (e55 x))
  have e1 : ((((I_t31 x) + (I_t62 x)) + (2 * (w_n59 x).toNat + 2 * (w_n61 x).toNat + 2 * (w_n68 x).toNat + 2 * (w_n70 x).toNat + 2 * (w_n140 x).toNat + 2 * (w_n142 x).toNat)) + (16 * (w_n33 x).toNat + 16 * (w_n66 x).toNat + 16 * (w_n75 x).toNat + 16 * (w_n78 x).toNat + 16 * (w_n80 x).toNat + 16 * (w_n114 x).toNat)) = (I_t63 x) + (2 * (w_n59 x).toNat + 2 * (w_n61 x).toNat + 2 * (w_n68 x).toNat + 2 * (w_n70 x).toNat + 2 * (w_n140 x).toNat + 2 * (w_n142 x).toNat + 16 * (w_n33 x).toNat + 16 * (w_n66 x).toNat + 16 * (w_n75 x).toNat + 16 * (w_n78 x).toNat + 16 * (w_n80 x).toNat + 16 * (w_n114 x).toNat) := by unfold I_t63; ac_rfl
  have e2 : ((((16 * (w_n33 x).toNat + 2 * (w_n59 x).toNat + 2 * (w_n61 x).toNat + 16 * (w_n66 x).toNat + (w_n67 x).toNat + 2 * (w_n68 x).toNat + 2 * (w_n70 x).toNat + 4 * (w_n73 x).toNat + 16 * (w_n75 x).toNat + 4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 16 * (w_n78 x).toNat + 8 * (w_n79 x).toNat + 16 * (w_n80 x).toNat + 32 * (w_n81 x).toNat) + (16 * (w_n114 x).toNat + 2 * (w_n140 x).toNat + 2 * (w_n142 x).toNat + 16 * (w_n147 x).toNat + (w_n148 x).toNat + 2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n154 x).toNat + 16 * (w_n156 x).toNat + 4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat)) + (2 * (w_n163 x).toNat + 4 * (w_n164 x).toNat + 8 * (w_n165 x).toNat)) + (16 * (w_n166 x).toNat + 32 * (w_n167 x).toNat + 64 * (w_n168 x).toNat)) = ((w_n67 x).toNat + 4 * (w_n73 x).toNat + 4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 8 * (w_n79 x).toNat + 32 * (w_n81 x).toNat + 16 * (w_n147 x).toNat + (w_n148 x).toNat + 2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n154 x).toNat + 16 * (w_n156 x).toNat + 4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat + 2 * (w_n163 x).toNat + 4 * (w_n164 x).toNat + 8 * (w_n165 x).toNat + 16 * (w_n166 x).toNat + 32 * (w_n167 x).toNat + 64 * (w_n168 x).toNat) + (2 * (w_n59 x).toNat + 2 * (w_n61 x).toNat + 2 * (w_n68 x).toNat + 2 * (w_n70 x).toNat + 2 * (w_n140 x).toNat + 2 * (w_n142 x).toNat + 16 * (w_n33 x).toNat + 16 * (w_n66 x).toNat + 16 * (w_n75 x).toNat + 16 * (w_n78 x).toNat + 16 * (w_n80 x).toNat + 16 * (w_n114 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s63 (x : Nat → Bool) : I_t63 x = pc x 463 192 := by
  have hl := s31 x
  have hr := s62 x
  have : pc x 463 192 = pc x 463 96 + pc x 559 96 := pc_add x 463 96 96
  unfold I_t63
  omega
def I_b64 (x : Nat → Bool) : Nat := 0 + (x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat
theorem b64 (x : Nat → Bool) : I_b64 x = (x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat := by
  unfold I_b64
  omega
def I_t64 (x : Nat → Bool) : Nat := I_b64 x
theorem t64 (x : Nat → Bool) : I_t64 x = (w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat := by
  have hs : ((I_b64 x) + ((x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat)) = (((x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat) + ((w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat)) := (add_eq (b64 x) (e56 x))
  have e1 : ((I_b64 x) + ((x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat)) = (I_t64 x) + ((x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat) := by unfold I_t64; ac_rfl
  have e2 : (((x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat) + ((w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat)) = ((w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat) + ((x 739).toNat + (x 740).toNat + (x 741).toNat + (x 742).toNat + (x 743).toNat + (x 744).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s64 (x : Nat → Bool) : I_t64 x = pc x 739 6 := rfl
def I_b65 (x : Nat → Bool) : Nat := 0 + (x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat
theorem b65 (x : Nat → Bool) : I_b65 x = (x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat := by
  unfold I_b65
  omega
def I_t65 (x : Nat → Bool) : Nat := I_b65 x
theorem t65 (x : Nat → Bool) : I_t65 x = (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat := by
  have hs : ((I_b65 x) + ((x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat)) = (((x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat) + ((w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat)) := (add_eq (b65 x) (e57 x))
  have e1 : ((I_b65 x) + ((x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat)) = (I_t65 x) + ((x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat) := by unfold I_t65; ac_rfl
  have e2 : (((x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat) + ((w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat)) = ((w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat) + ((x 745).toNat + (x 746).toNat + (x 747).toNat + (x 748).toNat + (x 749).toNat + (x 750).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s65 (x : Nat → Bool) : I_t65 x = pc x 745 6 := rfl
def I_t66 (x : Nat → Bool) : Nat := I_t64 x + I_t65 x
theorem t66 (x : Nat → Bool) : I_t66 x = (w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat + (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat := by
  have hs : ((I_t64 x) + (I_t65 x)) = (((w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat) + ((w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat)) := (add_eq (t64 x) (t65 x))
  have e1 : ((I_t64 x) + (I_t65 x)) = I_t66 x := by unfold I_t66; ac_rfl
  have e2 : (((w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat) + ((w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat)) = (w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat + (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s66 (x : Nat → Bool) : I_t66 x = pc x 739 12 := by
  have hl := s64 x
  have hr := s65 x
  have : pc x 739 12 = pc x 739 6 + pc x 745 6 := pc_add x 739 6 6
  unfold I_t66
  omega
def I_b67 (x : Nat → Bool) : Nat := 0 + (x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat
theorem b67 (x : Nat → Bool) : I_b67 x = (x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat := by
  unfold I_b67
  omega
def I_t67 (x : Nat → Bool) : Nat := I_b67 x
theorem t67 (x : Nat → Bool) : I_t67 x = (w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat := by
  have hs : ((I_b67 x) + ((x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat)) = (((x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat) + ((w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat)) := (add_eq (b67 x) (e58 x))
  have e1 : ((I_b67 x) + ((x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat)) = (I_t67 x) + ((x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat) := by unfold I_t67; ac_rfl
  have e2 : (((x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat) + ((w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat)) = ((w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat) + ((x 733).toNat + (x 734).toNat + (x 735).toNat + (x 736).toNat + (x 737).toNat + (x 738).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s67 (x : Nat → Bool) : I_t67 x = pc x 733 6 := rfl
def I_b68 (x : Nat → Bool) : Nat := 0 + (x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat
theorem b68 (x : Nat → Bool) : I_b68 x = (x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat := by
  unfold I_b68
  omega
def I_t68 (x : Nat → Bool) : Nat := I_b68 x
theorem t68 (x : Nat → Bool) : I_t68 x = (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat := by
  have hs : ((I_b68 x) + ((x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat)) = (((x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat) + ((w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat)) := (add_eq (b68 x) (e59 x))
  have e1 : ((I_b68 x) + ((x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat)) = (I_t68 x) + ((x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat) := by unfold I_t68; ac_rfl
  have e2 : (((x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat) + ((w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat)) = ((w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat) + ((x 727).toNat + (x 728).toNat + (x 729).toNat + (x 730).toNat + (x 731).toNat + (x 732).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s68 (x : Nat → Bool) : I_t68 x = pc x 727 6 := rfl
def I_t69 (x : Nat → Bool) : Nat := I_t67 x + I_t68 x
theorem t69 (x : Nat → Bool) : I_t69 x = (w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat + (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat := by
  have hs : ((I_t67 x) + (I_t68 x)) = (((w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat) + ((w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat)) := (add_eq (t67 x) (t68 x))
  have e1 : ((I_t67 x) + (I_t68 x)) = I_t69 x := by unfold I_t69; ac_rfl
  have e2 : (((w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat) + ((w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat)) = (w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat + (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s69 (x : Nat → Bool) : I_t69 x = pc x 727 12 := by
  have hl := s67 x
  have hr := s68 x
  have : pc x 727 12 = pc x 727 6 + pc x 733 6 := pc_add x 727 6 6
  unfold I_t69
  omega
def I_t70 (x : Nat → Bool) : Nat := I_t66 x + I_t69 x
theorem t70 (x : Nat → Bool) : I_t70 x = (w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat + (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat + (w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat + (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat := by
  have hs : ((I_t66 x) + (I_t69 x)) = (((w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat + (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat) + ((w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat + (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat)) := (add_eq (t66 x) (t69 x))
  have e1 : ((I_t66 x) + (I_t69 x)) = I_t70 x := by unfold I_t70; ac_rfl
  have e2 : (((w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat + (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat) + ((w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat + (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat)) = (w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat + (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat + (w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat + (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s70 (x : Nat → Bool) : I_t70 x = pc x 727 24 := by
  have hl := s66 x
  have hr := s69 x
  have : pc x 727 24 = pc x 727 12 + pc x 739 12 := pc_add x 727 12 12
  unfold I_t70
  omega
def I_b71 (x : Nat → Bool) : Nat := 0 + (x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat
theorem b71 (x : Nat → Bool) : I_b71 x = (x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat := by
  unfold I_b71
  omega
def I_t71 (x : Nat → Bool) : Nat := I_b71 x
theorem t71 (x : Nat → Bool) : I_t71 x = (w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat := by
  have hs : ((I_b71 x) + ((x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat)) = (((x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat) + ((w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat)) := (add_eq (b71 x) (e60 x))
  have e1 : ((I_b71 x) + ((x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat)) = (I_t71 x) + ((x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat) := by unfold I_t71; ac_rfl
  have e2 : (((x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat) + ((w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat)) = ((w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat) + ((x 709).toNat + (x 710).toNat + (x 711).toNat + (x 712).toNat + (x 713).toNat + (x 714).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s71 (x : Nat → Bool) : I_t71 x = pc x 709 6 := rfl
def I_b72 (x : Nat → Bool) : Nat := 0 + (x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat
theorem b72 (x : Nat → Bool) : I_b72 x = (x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat := by
  unfold I_b72
  omega
def I_t72 (x : Nat → Bool) : Nat := I_b72 x
theorem t72 (x : Nat → Bool) : I_t72 x = (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat := by
  have hs : ((I_b72 x) + ((x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat)) = (((x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat) + ((w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat)) := (add_eq (b72 x) (e61 x))
  have e1 : ((I_b72 x) + ((x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat)) = (I_t72 x) + ((x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat) := by unfold I_t72; ac_rfl
  have e2 : (((x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat) + ((w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat)) = ((w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat) + ((x 703).toNat + (x 704).toNat + (x 705).toNat + (x 706).toNat + (x 707).toNat + (x 708).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s72 (x : Nat → Bool) : I_t72 x = pc x 703 6 := rfl
def I_t73 (x : Nat → Bool) : Nat := I_t71 x + I_t72 x
theorem t73 (x : Nat → Bool) : I_t73 x = (w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat + (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat := by
  have hs : ((I_t71 x) + (I_t72 x)) = (((w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat) + ((w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat)) := (add_eq (t71 x) (t72 x))
  have e1 : ((I_t71 x) + (I_t72 x)) = I_t73 x := by unfold I_t73; ac_rfl
  have e2 : (((w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat) + ((w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat)) = (w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat + (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s73 (x : Nat → Bool) : I_t73 x = pc x 703 12 := by
  have hl := s71 x
  have hr := s72 x
  have : pc x 703 12 = pc x 703 6 + pc x 709 6 := pc_add x 703 6 6
  unfold I_t73
  omega
def I_b74 (x : Nat → Bool) : Nat := 0 + (x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat
theorem b74 (x : Nat → Bool) : I_b74 x = (x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat := by
  unfold I_b74
  omega
def I_t74 (x : Nat → Bool) : Nat := I_b74 x
theorem t74 (x : Nat → Bool) : I_t74 x = (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat := by
  have hs : ((I_b74 x) + ((x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat)) = (((x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat) + ((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat)) := (add_eq (b74 x) (e62 x))
  have e1 : ((I_b74 x) + ((x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat)) = (I_t74 x) + ((x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat) := by unfold I_t74; ac_rfl
  have e2 : (((x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat) + ((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat)) = ((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat) + ((x 721).toNat + (x 722).toNat + (x 723).toNat + (x 724).toNat + (x 725).toNat + (x 726).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s74 (x : Nat → Bool) : I_t74 x = pc x 721 6 := rfl
def I_b75 (x : Nat → Bool) : Nat := 0 + (x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat
theorem b75 (x : Nat → Bool) : I_b75 x = (x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat := by
  unfold I_b75
  omega
def I_t75 (x : Nat → Bool) : Nat := I_b75 x
theorem t75 (x : Nat → Bool) : I_t75 x = (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat := by
  have hs : ((I_b75 x) + ((x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat)) = (((x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat) + ((w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat)) := (add_eq (b75 x) (e63 x))
  have e1 : ((I_b75 x) + ((x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat)) = (I_t75 x) + ((x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat) := by unfold I_t75; ac_rfl
  have e2 : (((x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat) + ((w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat)) = ((w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat) + ((x 715).toNat + (x 716).toNat + (x 717).toNat + (x 718).toNat + (x 719).toNat + (x 720).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s75 (x : Nat → Bool) : I_t75 x = pc x 715 6 := rfl
def I_t76 (x : Nat → Bool) : Nat := I_t74 x + I_t75 x
theorem t76 (x : Nat → Bool) : I_t76 x = (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat := by
  have hs : ((I_t74 x) + (I_t75 x)) = (((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat) + ((w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat)) := (add_eq (t74 x) (t75 x))
  have e1 : ((I_t74 x) + (I_t75 x)) = I_t76 x := by unfold I_t76; ac_rfl
  have e2 : (((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat) + ((w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat)) = (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s76 (x : Nat → Bool) : I_t76 x = pc x 715 12 := by
  have hl := s74 x
  have hr := s75 x
  have : pc x 715 12 = pc x 715 6 + pc x 721 6 := pc_add x 715 6 6
  unfold I_t76
  omega
def I_t77 (x : Nat → Bool) : Nat := I_t73 x + I_t76 x
theorem t77 (x : Nat → Bool) : I_t77 x = (w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat + (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat + (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat := by
  have hs : ((I_t73 x) + (I_t76 x)) = (((w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat + (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat) + ((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat)) := (add_eq (t73 x) (t76 x))
  have e1 : ((I_t73 x) + (I_t76 x)) = I_t77 x := by unfold I_t77; ac_rfl
  have e2 : (((w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat + (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat) + ((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat)) = (w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat + (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat + (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s77 (x : Nat → Bool) : I_t77 x = pc x 703 24 := by
  have hl := s73 x
  have hr := s76 x
  have : pc x 703 24 = pc x 703 12 + pc x 715 12 := pc_add x 703 12 12
  unfold I_t77
  omega
def I_t78 (x : Nat → Bool) : Nat := I_t70 x + I_t77 x
theorem t78 (x : Nat → Bool) : I_t78 x = (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat + (w_n193 x).toNat + 2 * (w_n194 x).toNat + 4 * (w_n195 x).toNat + 2 * (w_n196 x).toNat + 4 * (w_n197 x).toNat + 8 * (w_n198 x).toNat + 4 * (w_n199 x).toNat + 8 * (w_n200 x).toNat + 16 * (w_n201 x).toNat := by
  have hs : (((((I_t70 x) + (I_t77 x)) + ((w_n169 x).toNat + (w_n172 x).toNat + (w_n175 x).toNat + (w_n178 x).toNat + (w_n181 x).toNat + (w_n184 x).toNat)) + (2 * (w_n170 x).toNat + 2 * (w_n173 x).toNat + 2 * (w_n176 x).toNat + 2 * (w_n179 x).toNat + 2 * (w_n182 x).toNat + 2 * (w_n185 x).toNat)) + (4 * (w_n171 x).toNat + 4 * (w_n174 x).toNat + 4 * (w_n177 x).toNat + 4 * (w_n180 x).toNat + 4 * (w_n183 x).toNat + 4 * (w_n186 x).toNat)) = ((((((w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat + (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat + (w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat + (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat) + ((w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat + (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat + (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat)) + ((w_n193 x).toNat + 2 * (w_n194 x).toNat + 4 * (w_n195 x).toNat)) + (2 * (w_n196 x).toNat + 4 * (w_n197 x).toNat + 8 * (w_n198 x).toNat)) + (4 * (w_n199 x).toNat + 8 * (w_n200 x).toNat + 16 * (w_n201 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t70 x) (t77 x)) (e64 x)) (e65 x)) (e66 x))
  have e1 : (((((I_t70 x) + (I_t77 x)) + ((w_n169 x).toNat + (w_n172 x).toNat + (w_n175 x).toNat + (w_n178 x).toNat + (w_n181 x).toNat + (w_n184 x).toNat)) + (2 * (w_n170 x).toNat + 2 * (w_n173 x).toNat + 2 * (w_n176 x).toNat + 2 * (w_n179 x).toNat + 2 * (w_n182 x).toNat + 2 * (w_n185 x).toNat)) + (4 * (w_n171 x).toNat + 4 * (w_n174 x).toNat + 4 * (w_n177 x).toNat + 4 * (w_n180 x).toNat + 4 * (w_n183 x).toNat + 4 * (w_n186 x).toNat)) = (I_t78 x) + ((w_n169 x).toNat + (w_n172 x).toNat + (w_n175 x).toNat + (w_n178 x).toNat + (w_n181 x).toNat + (w_n184 x).toNat + 2 * (w_n170 x).toNat + 2 * (w_n173 x).toNat + 2 * (w_n176 x).toNat + 2 * (w_n179 x).toNat + 2 * (w_n182 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n171 x).toNat + 4 * (w_n174 x).toNat + 4 * (w_n177 x).toNat + 4 * (w_n180 x).toNat + 4 * (w_n183 x).toNat + 4 * (w_n186 x).toNat) := by unfold I_t78; ac_rfl
  have e2 : ((((((w_n169 x).toNat + 2 * (w_n170 x).toNat + 4 * (w_n171 x).toNat + (w_n172 x).toNat + 2 * (w_n173 x).toNat + 4 * (w_n174 x).toNat + (w_n175 x).toNat + 2 * (w_n176 x).toNat + 4 * (w_n177 x).toNat + (w_n178 x).toNat + 2 * (w_n179 x).toNat + 4 * (w_n180 x).toNat) + ((w_n181 x).toNat + 2 * (w_n182 x).toNat + 4 * (w_n183 x).toNat + (w_n184 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n186 x).toNat + (w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat)) + ((w_n193 x).toNat + 2 * (w_n194 x).toNat + 4 * (w_n195 x).toNat)) + (2 * (w_n196 x).toNat + 4 * (w_n197 x).toNat + 8 * (w_n198 x).toNat)) + (4 * (w_n199 x).toNat + 8 * (w_n200 x).toNat + 16 * (w_n201 x).toNat)) = ((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat + (w_n193 x).toNat + 2 * (w_n194 x).toNat + 4 * (w_n195 x).toNat + 2 * (w_n196 x).toNat + 4 * (w_n197 x).toNat + 8 * (w_n198 x).toNat + 4 * (w_n199 x).toNat + 8 * (w_n200 x).toNat + 16 * (w_n201 x).toNat) + ((w_n169 x).toNat + (w_n172 x).toNat + (w_n175 x).toNat + (w_n178 x).toNat + (w_n181 x).toNat + (w_n184 x).toNat + 2 * (w_n170 x).toNat + 2 * (w_n173 x).toNat + 2 * (w_n176 x).toNat + 2 * (w_n179 x).toNat + 2 * (w_n182 x).toNat + 2 * (w_n185 x).toNat + 4 * (w_n171 x).toNat + 4 * (w_n174 x).toNat + 4 * (w_n177 x).toNat + 4 * (w_n180 x).toNat + 4 * (w_n183 x).toNat + 4 * (w_n186 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s78 (x : Nat → Bool) : I_t78 x = pc x 703 48 := by
  have hl := s70 x
  have hr := s77 x
  have : pc x 703 48 = pc x 703 24 + pc x 727 24 := pc_add x 703 24 24
  unfold I_t78
  omega
def I_b79 (x : Nat → Bool) : Nat := 0 + (x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat
theorem b79 (x : Nat → Bool) : I_b79 x = (x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat := by
  unfold I_b79
  omega
def I_t79 (x : Nat → Bool) : Nat := I_b79 x
theorem t79 (x : Nat → Bool) : I_t79 x = (w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat := by
  have hs : ((I_b79 x) + ((x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat)) = (((x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat) + ((w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat)) := (add_eq (b79 x) (e67 x))
  have e1 : ((I_b79 x) + ((x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat)) = (I_t79 x) + ((x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat) := by unfold I_t79; ac_rfl
  have e2 : (((x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat) + ((w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat)) = ((w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat) + ((x 667).toNat + (x 668).toNat + (x 669).toNat + (x 670).toNat + (x 671).toNat + (x 672).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s79 (x : Nat → Bool) : I_t79 x = pc x 667 6 := rfl
def I_b80 (x : Nat → Bool) : Nat := 0 + (x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat
theorem b80 (x : Nat → Bool) : I_b80 x = (x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat := by
  unfold I_b80
  omega
def I_t80 (x : Nat → Bool) : Nat := I_b80 x
theorem t80 (x : Nat → Bool) : I_t80 x = (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat := by
  have hs : ((I_b80 x) + ((x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat)) = (((x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat) + ((w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat)) := (add_eq (b80 x) (e68 x))
  have e1 : ((I_b80 x) + ((x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat)) = (I_t80 x) + ((x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat) := by unfold I_t80; ac_rfl
  have e2 : (((x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat) + ((w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat)) = ((w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat) + ((x 673).toNat + (x 674).toNat + (x 675).toNat + (x 676).toNat + (x 677).toNat + (x 678).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s80 (x : Nat → Bool) : I_t80 x = pc x 673 6 := rfl
def I_t81 (x : Nat → Bool) : Nat := I_t79 x + I_t80 x
theorem t81 (x : Nat → Bool) : I_t81 x = (w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat + (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat := by
  have hs : ((I_t79 x) + (I_t80 x)) = (((w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat) + ((w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat)) := (add_eq (t79 x) (t80 x))
  have e1 : ((I_t79 x) + (I_t80 x)) = I_t81 x := by unfold I_t81; ac_rfl
  have e2 : (((w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat) + ((w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat)) = (w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat + (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s81 (x : Nat → Bool) : I_t81 x = pc x 667 12 := by
  have hl := s79 x
  have hr := s80 x
  have : pc x 667 12 = pc x 667 6 + pc x 673 6 := pc_add x 667 6 6
  unfold I_t81
  omega
def I_b82 (x : Nat → Bool) : Nat := 0 + (x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat
theorem b82 (x : Nat → Bool) : I_b82 x = (x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat := by
  unfold I_b82
  omega
def I_t82 (x : Nat → Bool) : Nat := I_b82 x
theorem t82 (x : Nat → Bool) : I_t82 x = (w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat := by
  have hs : ((I_b82 x) + ((x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat)) = (((x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat) + ((w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat)) := (add_eq (b82 x) (e69 x))
  have e1 : ((I_b82 x) + ((x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat)) = (I_t82 x) + ((x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat) := by unfold I_t82; ac_rfl
  have e2 : (((x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat) + ((w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat)) = ((w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat) + ((x 661).toNat + (x 662).toNat + (x 663).toNat + (x 664).toNat + (x 665).toNat + (x 666).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s82 (x : Nat → Bool) : I_t82 x = pc x 661 6 := rfl
def I_b83 (x : Nat → Bool) : Nat := 0 + (x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat
theorem b83 (x : Nat → Bool) : I_b83 x = (x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat := by
  unfold I_b83
  omega
def I_t83 (x : Nat → Bool) : Nat := I_b83 x
theorem t83 (x : Nat → Bool) : I_t83 x = (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat := by
  have hs : ((I_b83 x) + ((x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat)) = (((x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat) + ((w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat)) := (add_eq (b83 x) (e70 x))
  have e1 : ((I_b83 x) + ((x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat)) = (I_t83 x) + ((x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat) := by unfold I_t83; ac_rfl
  have e2 : (((x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat) + ((w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat)) = ((w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat) + ((x 655).toNat + (x 656).toNat + (x 657).toNat + (x 658).toNat + (x 659).toNat + (x 660).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s83 (x : Nat → Bool) : I_t83 x = pc x 655 6 := rfl
def I_t84 (x : Nat → Bool) : Nat := I_t82 x + I_t83 x
theorem t84 (x : Nat → Bool) : I_t84 x = (w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat + (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat := by
  have hs : ((I_t82 x) + (I_t83 x)) = (((w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat) + ((w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat)) := (add_eq (t82 x) (t83 x))
  have e1 : ((I_t82 x) + (I_t83 x)) = I_t84 x := by unfold I_t84; ac_rfl
  have e2 : (((w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat) + ((w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat)) = (w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat + (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s84 (x : Nat → Bool) : I_t84 x = pc x 655 12 := by
  have hl := s82 x
  have hr := s83 x
  have : pc x 655 12 = pc x 655 6 + pc x 661 6 := pc_add x 655 6 6
  unfold I_t84
  omega
def I_t85 (x : Nat → Bool) : Nat := I_t81 x + I_t84 x
theorem t85 (x : Nat → Bool) : I_t85 x = (w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat + (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat + (w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat + (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat := by
  have hs : ((I_t81 x) + (I_t84 x)) = (((w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat + (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat) + ((w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat + (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat)) := (add_eq (t81 x) (t84 x))
  have e1 : ((I_t81 x) + (I_t84 x)) = I_t85 x := by unfold I_t85; ac_rfl
  have e2 : (((w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat + (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat) + ((w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat + (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat)) = (w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat + (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat + (w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat + (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s85 (x : Nat → Bool) : I_t85 x = pc x 655 24 := by
  have hl := s81 x
  have hr := s84 x
  have : pc x 655 24 = pc x 655 12 + pc x 667 12 := pc_add x 655 12 12
  unfold I_t85
  omega
def I_b86 (x : Nat → Bool) : Nat := 0 + (x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat
theorem b86 (x : Nat → Bool) : I_b86 x = (x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat := by
  unfold I_b86
  omega
def I_t86 (x : Nat → Bool) : Nat := I_b86 x
theorem t86 (x : Nat → Bool) : I_t86 x = (w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat := by
  have hs : ((I_b86 x) + ((x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat)) = (((x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat) + ((w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat)) := (add_eq (b86 x) (e71 x))
  have e1 : ((I_b86 x) + ((x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat)) = (I_t86 x) + ((x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat) := by unfold I_t86; ac_rfl
  have e2 : (((x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat) + ((w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat)) = ((w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat) + ((x 679).toNat + (x 680).toNat + (x 681).toNat + (x 682).toNat + (x 683).toNat + (x 684).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s86 (x : Nat → Bool) : I_t86 x = pc x 679 6 := rfl
def I_b87 (x : Nat → Bool) : Nat := 0 + (x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat
theorem b87 (x : Nat → Bool) : I_b87 x = (x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat := by
  unfold I_b87
  omega
def I_t87 (x : Nat → Bool) : Nat := I_b87 x
theorem t87 (x : Nat → Bool) : I_t87 x = (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat := by
  have hs : ((I_b87 x) + ((x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat)) = (((x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat) + ((w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat)) := (add_eq (b87 x) (e72 x))
  have e1 : ((I_b87 x) + ((x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat)) = (I_t87 x) + ((x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat) := by unfold I_t87; ac_rfl
  have e2 : (((x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat) + ((w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat)) = ((w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat) + ((x 685).toNat + (x 686).toNat + (x 687).toNat + (x 688).toNat + (x 689).toNat + (x 690).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s87 (x : Nat → Bool) : I_t87 x = pc x 685 6 := rfl
def I_t88 (x : Nat → Bool) : Nat := I_t86 x + I_t87 x
theorem t88 (x : Nat → Bool) : I_t88 x = (w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat + (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat := by
  have hs : ((I_t86 x) + (I_t87 x)) = (((w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat) + ((w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat)) := (add_eq (t86 x) (t87 x))
  have e1 : ((I_t86 x) + (I_t87 x)) = I_t88 x := by unfold I_t88; ac_rfl
  have e2 : (((w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat) + ((w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat)) = (w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat + (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s88 (x : Nat → Bool) : I_t88 x = pc x 679 12 := by
  have hl := s86 x
  have hr := s87 x
  have : pc x 679 12 = pc x 679 6 + pc x 685 6 := pc_add x 679 6 6
  unfold I_t88
  omega
def I_b89 (x : Nat → Bool) : Nat := 0 + (x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat
theorem b89 (x : Nat → Bool) : I_b89 x = (x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat := by
  unfold I_b89
  omega
def I_t89 (x : Nat → Bool) : Nat := I_b89 x
theorem t89 (x : Nat → Bool) : I_t89 x = (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat := by
  have hs : ((I_b89 x) + ((x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat)) = (((x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat) + ((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat)) := (add_eq (b89 x) (e73 x))
  have e1 : ((I_b89 x) + ((x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat)) = (I_t89 x) + ((x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat) := by unfold I_t89; ac_rfl
  have e2 : (((x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat) + ((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat)) = ((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat) + ((x 691).toNat + (x 692).toNat + (x 693).toNat + (x 694).toNat + (x 695).toNat + (x 696).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s89 (x : Nat → Bool) : I_t89 x = pc x 691 6 := rfl
def I_b90 (x : Nat → Bool) : Nat := 0 + (x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat
theorem b90 (x : Nat → Bool) : I_b90 x = (x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat := by
  unfold I_b90
  omega
def I_t90 (x : Nat → Bool) : Nat := I_b90 x
theorem t90 (x : Nat → Bool) : I_t90 x = (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat := by
  have hs : ((I_b90 x) + ((x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat)) = (((x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat) + ((w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat)) := (add_eq (b90 x) (e74 x))
  have e1 : ((I_b90 x) + ((x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat)) = (I_t90 x) + ((x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat) := by unfold I_t90; ac_rfl
  have e2 : (((x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat) + ((w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat)) = ((w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat) + ((x 697).toNat + (x 698).toNat + (x 699).toNat + (x 700).toNat + (x 701).toNat + (x 702).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s90 (x : Nat → Bool) : I_t90 x = pc x 697 6 := rfl
def I_t91 (x : Nat → Bool) : Nat := I_t89 x + I_t90 x
theorem t91 (x : Nat → Bool) : I_t91 x = (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat := by
  have hs : ((I_t89 x) + (I_t90 x)) = (((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat) + ((w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat)) := (add_eq (t89 x) (t90 x))
  have e1 : ((I_t89 x) + (I_t90 x)) = I_t91 x := by unfold I_t91; ac_rfl
  have e2 : (((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat) + ((w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat)) = (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s91 (x : Nat → Bool) : I_t91 x = pc x 691 12 := by
  have hl := s89 x
  have hr := s90 x
  have : pc x 691 12 = pc x 691 6 + pc x 697 6 := pc_add x 691 6 6
  unfold I_t91
  omega
def I_t92 (x : Nat → Bool) : Nat := I_t88 x + I_t91 x
theorem t92 (x : Nat → Bool) : I_t92 x = (w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat + (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat + (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat := by
  have hs : ((I_t88 x) + (I_t91 x)) = (((w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat + (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat) + ((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat)) := (add_eq (t88 x) (t91 x))
  have e1 : ((I_t88 x) + (I_t91 x)) = I_t92 x := by unfold I_t92; ac_rfl
  have e2 : (((w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat + (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat) + ((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat)) = (w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat + (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat + (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s92 (x : Nat → Bool) : I_t92 x = pc x 679 24 := by
  have hl := s88 x
  have hr := s91 x
  have : pc x 679 24 = pc x 679 12 + pc x 691 12 := pc_add x 679 12 12
  unfold I_t92
  omega
def I_t93 (x : Nat → Bool) : Nat := I_t85 x + I_t92 x
theorem t93 (x : Nat → Bool) : I_t93 x = (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat + (w_n226 x).toNat + 2 * (w_n227 x).toNat + 4 * (w_n228 x).toNat + 2 * (w_n229 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n231 x).toNat + 4 * (w_n232 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n234 x).toNat := by
  have hs : (((((I_t85 x) + (I_t92 x)) + ((w_n202 x).toNat + (w_n205 x).toNat + (w_n208 x).toNat + (w_n211 x).toNat + (w_n214 x).toNat + (w_n217 x).toNat)) + (2 * (w_n203 x).toNat + 2 * (w_n206 x).toNat + 2 * (w_n209 x).toNat + 2 * (w_n212 x).toNat + 2 * (w_n215 x).toNat + 2 * (w_n218 x).toNat)) + (4 * (w_n204 x).toNat + 4 * (w_n207 x).toNat + 4 * (w_n210 x).toNat + 4 * (w_n213 x).toNat + 4 * (w_n216 x).toNat + 4 * (w_n219 x).toNat)) = ((((((w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat + (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat + (w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat + (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat) + ((w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat + (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat + (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat)) + ((w_n226 x).toNat + 2 * (w_n227 x).toNat + 4 * (w_n228 x).toNat)) + (2 * (w_n229 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n231 x).toNat)) + (4 * (w_n232 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n234 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t85 x) (t92 x)) (e75 x)) (e76 x)) (e77 x))
  have e1 : (((((I_t85 x) + (I_t92 x)) + ((w_n202 x).toNat + (w_n205 x).toNat + (w_n208 x).toNat + (w_n211 x).toNat + (w_n214 x).toNat + (w_n217 x).toNat)) + (2 * (w_n203 x).toNat + 2 * (w_n206 x).toNat + 2 * (w_n209 x).toNat + 2 * (w_n212 x).toNat + 2 * (w_n215 x).toNat + 2 * (w_n218 x).toNat)) + (4 * (w_n204 x).toNat + 4 * (w_n207 x).toNat + 4 * (w_n210 x).toNat + 4 * (w_n213 x).toNat + 4 * (w_n216 x).toNat + 4 * (w_n219 x).toNat)) = (I_t93 x) + ((w_n202 x).toNat + (w_n205 x).toNat + (w_n208 x).toNat + (w_n211 x).toNat + (w_n214 x).toNat + (w_n217 x).toNat + 2 * (w_n203 x).toNat + 2 * (w_n206 x).toNat + 2 * (w_n209 x).toNat + 2 * (w_n212 x).toNat + 2 * (w_n215 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n204 x).toNat + 4 * (w_n207 x).toNat + 4 * (w_n210 x).toNat + 4 * (w_n213 x).toNat + 4 * (w_n216 x).toNat + 4 * (w_n219 x).toNat) := by unfold I_t93; ac_rfl
  have e2 : ((((((w_n202 x).toNat + 2 * (w_n203 x).toNat + 4 * (w_n204 x).toNat + (w_n205 x).toNat + 2 * (w_n206 x).toNat + 4 * (w_n207 x).toNat + (w_n208 x).toNat + 2 * (w_n209 x).toNat + 4 * (w_n210 x).toNat + (w_n211 x).toNat + 2 * (w_n212 x).toNat + 4 * (w_n213 x).toNat) + ((w_n214 x).toNat + 2 * (w_n215 x).toNat + 4 * (w_n216 x).toNat + (w_n217 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n219 x).toNat + (w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat)) + ((w_n226 x).toNat + 2 * (w_n227 x).toNat + 4 * (w_n228 x).toNat)) + (2 * (w_n229 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n231 x).toNat)) + (4 * (w_n232 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n234 x).toNat)) = ((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat + (w_n226 x).toNat + 2 * (w_n227 x).toNat + 4 * (w_n228 x).toNat + 2 * (w_n229 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n231 x).toNat + 4 * (w_n232 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n234 x).toNat) + ((w_n202 x).toNat + (w_n205 x).toNat + (w_n208 x).toNat + (w_n211 x).toNat + (w_n214 x).toNat + (w_n217 x).toNat + 2 * (w_n203 x).toNat + 2 * (w_n206 x).toNat + 2 * (w_n209 x).toNat + 2 * (w_n212 x).toNat + 2 * (w_n215 x).toNat + 2 * (w_n218 x).toNat + 4 * (w_n204 x).toNat + 4 * (w_n207 x).toNat + 4 * (w_n210 x).toNat + 4 * (w_n213 x).toNat + 4 * (w_n216 x).toNat + 4 * (w_n219 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s93 (x : Nat → Bool) : I_t93 x = pc x 655 48 := by
  have hl := s85 x
  have hr := s92 x
  have : pc x 655 48 = pc x 655 24 + pc x 679 24 := pc_add x 655 24 24
  unfold I_t93
  omega
def I_t94 (x : Nat → Bool) : Nat := I_t78 x + I_t93 x
theorem t94 (x : Nat → Bool) : I_t94 x = 16 * (w_n201 x).toNat + 2 * (w_n227 x).toNat + 2 * (w_n229 x).toNat + 16 * (w_n234 x).toNat + (w_n235 x).toNat + 2 * (w_n236 x).toNat + 2 * (w_n238 x).toNat + 4 * (w_n241 x).toNat + 16 * (w_n243 x).toNat + 4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 16 * (w_n246 x).toNat + 8 * (w_n247 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n249 x).toNat := by
  have hs : (((((((I_t78 x) + (I_t93 x)) + ((w_n187 x).toNat + (w_n190 x).toNat + (w_n193 x).toNat + (w_n220 x).toNat + (w_n223 x).toNat + (w_n226 x).toNat)) + (2 * (w_n188 x).toNat + 2 * (w_n191 x).toNat + 2 * (w_n194 x).toNat + 2 * (w_n196 x).toNat + 2 * (w_n221 x).toNat + 2 * (w_n224 x).toNat)) + (4 * (w_n189 x).toNat + 4 * (w_n192 x).toNat + 4 * (w_n195 x).toNat + 4 * (w_n197 x).toNat + 4 * (w_n199 x).toNat + 4 * (w_n222 x).toNat)) + (4 * (w_n225 x).toNat + 4 * (w_n228 x).toNat + 4 * (w_n230 x).toNat + 4 * (w_n232 x).toNat + 4 * (w_n237 x).toNat + 4 * (w_n239 x).toNat)) + (8 * (w_n198 x).toNat + 8 * (w_n200 x).toNat + 8 * (w_n231 x).toNat + 8 * (w_n233 x).toNat + 8 * (w_n240 x).toNat + 8 * (w_n242 x).toNat)) = ((((((((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat + (w_n193 x).toNat + 2 * (w_n194 x).toNat + 4 * (w_n195 x).toNat + 2 * (w_n196 x).toNat + 4 * (w_n197 x).toNat + 8 * (w_n198 x).toNat + 4 * (w_n199 x).toNat + 8 * (w_n200 x).toNat + 16 * (w_n201 x).toNat) + ((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat + (w_n226 x).toNat + 2 * (w_n227 x).toNat + 4 * (w_n228 x).toNat + 2 * (w_n229 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n231 x).toNat + 4 * (w_n232 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n234 x).toNat)) + ((w_n235 x).toNat + 2 * (w_n236 x).toNat + 4 * (w_n237 x).toNat)) + (2 * (w_n238 x).toNat + 4 * (w_n239 x).toNat + 8 * (w_n240 x).toNat)) + (4 * (w_n241 x).toNat + 8 * (w_n242 x).toNat + 16 * (w_n243 x).toNat)) + (4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 16 * (w_n246 x).toNat)) + (8 * (w_n247 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n249 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t78 x) (t93 x)) (e78 x)) (e79 x)) (e80 x)) (e81 x)) (e82 x))
  have e1 : (((((((I_t78 x) + (I_t93 x)) + ((w_n187 x).toNat + (w_n190 x).toNat + (w_n193 x).toNat + (w_n220 x).toNat + (w_n223 x).toNat + (w_n226 x).toNat)) + (2 * (w_n188 x).toNat + 2 * (w_n191 x).toNat + 2 * (w_n194 x).toNat + 2 * (w_n196 x).toNat + 2 * (w_n221 x).toNat + 2 * (w_n224 x).toNat)) + (4 * (w_n189 x).toNat + 4 * (w_n192 x).toNat + 4 * (w_n195 x).toNat + 4 * (w_n197 x).toNat + 4 * (w_n199 x).toNat + 4 * (w_n222 x).toNat)) + (4 * (w_n225 x).toNat + 4 * (w_n228 x).toNat + 4 * (w_n230 x).toNat + 4 * (w_n232 x).toNat + 4 * (w_n237 x).toNat + 4 * (w_n239 x).toNat)) + (8 * (w_n198 x).toNat + 8 * (w_n200 x).toNat + 8 * (w_n231 x).toNat + 8 * (w_n233 x).toNat + 8 * (w_n240 x).toNat + 8 * (w_n242 x).toNat)) = (I_t94 x) + ((w_n187 x).toNat + (w_n190 x).toNat + (w_n193 x).toNat + (w_n220 x).toNat + (w_n223 x).toNat + (w_n226 x).toNat + 2 * (w_n188 x).toNat + 2 * (w_n191 x).toNat + 2 * (w_n194 x).toNat + 2 * (w_n196 x).toNat + 2 * (w_n221 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n189 x).toNat + 4 * (w_n192 x).toNat + 4 * (w_n195 x).toNat + 4 * (w_n197 x).toNat + 4 * (w_n199 x).toNat + 4 * (w_n222 x).toNat + 4 * (w_n225 x).toNat + 4 * (w_n228 x).toNat + 4 * (w_n230 x).toNat + 4 * (w_n232 x).toNat + 4 * (w_n237 x).toNat + 4 * (w_n239 x).toNat + 8 * (w_n198 x).toNat + 8 * (w_n200 x).toNat + 8 * (w_n231 x).toNat + 8 * (w_n233 x).toNat + 8 * (w_n240 x).toNat + 8 * (w_n242 x).toNat) := by unfold I_t94; ac_rfl
  have e2 : ((((((((w_n187 x).toNat + 2 * (w_n188 x).toNat + 4 * (w_n189 x).toNat + (w_n190 x).toNat + 2 * (w_n191 x).toNat + 4 * (w_n192 x).toNat + (w_n193 x).toNat + 2 * (w_n194 x).toNat + 4 * (w_n195 x).toNat + 2 * (w_n196 x).toNat + 4 * (w_n197 x).toNat + 8 * (w_n198 x).toNat + 4 * (w_n199 x).toNat + 8 * (w_n200 x).toNat + 16 * (w_n201 x).toNat) + ((w_n220 x).toNat + 2 * (w_n221 x).toNat + 4 * (w_n222 x).toNat + (w_n223 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n225 x).toNat + (w_n226 x).toNat + 2 * (w_n227 x).toNat + 4 * (w_n228 x).toNat + 2 * (w_n229 x).toNat + 4 * (w_n230 x).toNat + 8 * (w_n231 x).toNat + 4 * (w_n232 x).toNat + 8 * (w_n233 x).toNat + 16 * (w_n234 x).toNat)) + ((w_n235 x).toNat + 2 * (w_n236 x).toNat + 4 * (w_n237 x).toNat)) + (2 * (w_n238 x).toNat + 4 * (w_n239 x).toNat + 8 * (w_n240 x).toNat)) + (4 * (w_n241 x).toNat + 8 * (w_n242 x).toNat + 16 * (w_n243 x).toNat)) + (4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 16 * (w_n246 x).toNat)) + (8 * (w_n247 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n249 x).toNat)) = (16 * (w_n201 x).toNat + 2 * (w_n227 x).toNat + 2 * (w_n229 x).toNat + 16 * (w_n234 x).toNat + (w_n235 x).toNat + 2 * (w_n236 x).toNat + 2 * (w_n238 x).toNat + 4 * (w_n241 x).toNat + 16 * (w_n243 x).toNat + 4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 16 * (w_n246 x).toNat + 8 * (w_n247 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n249 x).toNat) + ((w_n187 x).toNat + (w_n190 x).toNat + (w_n193 x).toNat + (w_n220 x).toNat + (w_n223 x).toNat + (w_n226 x).toNat + 2 * (w_n188 x).toNat + 2 * (w_n191 x).toNat + 2 * (w_n194 x).toNat + 2 * (w_n196 x).toNat + 2 * (w_n221 x).toNat + 2 * (w_n224 x).toNat + 4 * (w_n189 x).toNat + 4 * (w_n192 x).toNat + 4 * (w_n195 x).toNat + 4 * (w_n197 x).toNat + 4 * (w_n199 x).toNat + 4 * (w_n222 x).toNat + 4 * (w_n225 x).toNat + 4 * (w_n228 x).toNat + 4 * (w_n230 x).toNat + 4 * (w_n232 x).toNat + 4 * (w_n237 x).toNat + 4 * (w_n239 x).toNat + 8 * (w_n198 x).toNat + 8 * (w_n200 x).toNat + 8 * (w_n231 x).toNat + 8 * (w_n233 x).toNat + 8 * (w_n240 x).toNat + 8 * (w_n242 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s94 (x : Nat → Bool) : I_t94 x = pc x 655 96 := by
  have hl := s78 x
  have hr := s93 x
  have : pc x 655 96 = pc x 655 48 + pc x 703 48 := pc_add x 655 48 48
  unfold I_t94
  omega
def I_b95 (x : Nat → Bool) : Nat := 0 + (x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat
theorem b95 (x : Nat → Bool) : I_b95 x = (x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat := by
  unfold I_b95
  omega
def I_t95 (x : Nat → Bool) : Nat := I_b95 x
theorem t95 (x : Nat → Bool) : I_t95 x = (w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat := by
  have hs : ((I_b95 x) + ((x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat)) = (((x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat) + ((w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat)) := (add_eq (b95 x) (e83 x))
  have e1 : ((I_b95 x) + ((x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat)) = (I_t95 x) + ((x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat) := by unfold I_t95; ac_rfl
  have e2 : (((x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat) + ((w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat)) = ((w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat) + ((x 811).toNat + (x 812).toNat + (x 813).toNat + (x 814).toNat + (x 815).toNat + (x 816).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s95 (x : Nat → Bool) : I_t95 x = pc x 811 6 := rfl
def I_b96 (x : Nat → Bool) : Nat := 0 + (x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat
theorem b96 (x : Nat → Bool) : I_b96 x = (x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat := by
  unfold I_b96
  omega
def I_t96 (x : Nat → Bool) : Nat := I_b96 x
theorem t96 (x : Nat → Bool) : I_t96 x = (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat := by
  have hs : ((I_b96 x) + ((x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat)) = (((x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat) + ((w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat)) := (add_eq (b96 x) (e84 x))
  have e1 : ((I_b96 x) + ((x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat)) = (I_t96 x) + ((x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat) := by unfold I_t96; ac_rfl
  have e2 : (((x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat) + ((w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat)) = ((w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat) + ((x 817).toNat + (x 818).toNat + (x 819).toNat + (x 820).toNat + (x 821).toNat + (x 822).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s96 (x : Nat → Bool) : I_t96 x = pc x 817 6 := rfl
def I_t97 (x : Nat → Bool) : Nat := I_t95 x + I_t96 x
theorem t97 (x : Nat → Bool) : I_t97 x = (w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat + (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat := by
  have hs : ((I_t95 x) + (I_t96 x)) = (((w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat) + ((w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat)) := (add_eq (t95 x) (t96 x))
  have e1 : ((I_t95 x) + (I_t96 x)) = I_t97 x := by unfold I_t97; ac_rfl
  have e2 : (((w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat) + ((w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat)) = (w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat + (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s97 (x : Nat → Bool) : I_t97 x = pc x 811 12 := by
  have hl := s95 x
  have hr := s96 x
  have : pc x 811 12 = pc x 811 6 + pc x 817 6 := pc_add x 811 6 6
  unfold I_t97
  omega
def I_b98 (x : Nat → Bool) : Nat := 0 + (x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat
theorem b98 (x : Nat → Bool) : I_b98 x = (x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat := by
  unfold I_b98
  omega
def I_t98 (x : Nat → Bool) : Nat := I_b98 x
theorem t98 (x : Nat → Bool) : I_t98 x = (w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat := by
  have hs : ((I_b98 x) + ((x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat)) = (((x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat) + ((w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat)) := (add_eq (b98 x) (e85 x))
  have e1 : ((I_b98 x) + ((x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat)) = (I_t98 x) + ((x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat) := by unfold I_t98; ac_rfl
  have e2 : (((x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat) + ((w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat)) = ((w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat) + ((x 805).toNat + (x 806).toNat + (x 807).toNat + (x 808).toNat + (x 809).toNat + (x 810).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s98 (x : Nat → Bool) : I_t98 x = pc x 805 6 := rfl
def I_b99 (x : Nat → Bool) : Nat := 0 + (x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat
theorem b99 (x : Nat → Bool) : I_b99 x = (x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat := by
  unfold I_b99
  omega
def I_t99 (x : Nat → Bool) : Nat := I_b99 x
theorem t99 (x : Nat → Bool) : I_t99 x = (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat := by
  have hs : ((I_b99 x) + ((x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat)) = (((x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat) + ((w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat)) := (add_eq (b99 x) (e86 x))
  have e1 : ((I_b99 x) + ((x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat)) = (I_t99 x) + ((x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat) := by unfold I_t99; ac_rfl
  have e2 : (((x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat) + ((w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat)) = ((w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat) + ((x 799).toNat + (x 800).toNat + (x 801).toNat + (x 802).toNat + (x 803).toNat + (x 804).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s99 (x : Nat → Bool) : I_t99 x = pc x 799 6 := rfl
def I_t100 (x : Nat → Bool) : Nat := I_t98 x + I_t99 x
theorem t100 (x : Nat → Bool) : I_t100 x = (w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat + (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat := by
  have hs : ((I_t98 x) + (I_t99 x)) = (((w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat) + ((w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat)) := (add_eq (t98 x) (t99 x))
  have e1 : ((I_t98 x) + (I_t99 x)) = I_t100 x := by unfold I_t100; ac_rfl
  have e2 : (((w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat) + ((w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat)) = (w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat + (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s100 (x : Nat → Bool) : I_t100 x = pc x 799 12 := by
  have hl := s98 x
  have hr := s99 x
  have : pc x 799 12 = pc x 799 6 + pc x 805 6 := pc_add x 799 6 6
  unfold I_t100
  omega
def I_t101 (x : Nat → Bool) : Nat := I_t97 x + I_t100 x
theorem t101 (x : Nat → Bool) : I_t101 x = (w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat + (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat + (w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat + (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat := by
  have hs : ((I_t97 x) + (I_t100 x)) = (((w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat + (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat) + ((w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat + (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat)) := (add_eq (t97 x) (t100 x))
  have e1 : ((I_t97 x) + (I_t100 x)) = I_t101 x := by unfold I_t101; ac_rfl
  have e2 : (((w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat + (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat) + ((w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat + (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat)) = (w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat + (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat + (w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat + (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s101 (x : Nat → Bool) : I_t101 x = pc x 799 24 := by
  have hl := s97 x
  have hr := s100 x
  have : pc x 799 24 = pc x 799 12 + pc x 811 12 := pc_add x 799 12 12
  unfold I_t101
  omega
def I_b102 (x : Nat → Bool) : Nat := 0 + (x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat
theorem b102 (x : Nat → Bool) : I_b102 x = (x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat := by
  unfold I_b102
  omega
def I_t102 (x : Nat → Bool) : Nat := I_b102 x
theorem t102 (x : Nat → Bool) : I_t102 x = (w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat := by
  have hs : ((I_b102 x) + ((x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat)) = (((x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat) + ((w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat)) := (add_eq (b102 x) (e87 x))
  have e1 : ((I_b102 x) + ((x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat)) = (I_t102 x) + ((x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat) := by unfold I_t102; ac_rfl
  have e2 : (((x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat) + ((w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat)) = ((w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat) + ((x 829).toNat + (x 830).toNat + (x 831).toNat + (x 832).toNat + (x 833).toNat + (x 834).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s102 (x : Nat → Bool) : I_t102 x = pc x 829 6 := rfl
def I_b103 (x : Nat → Bool) : Nat := 0 + (x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat
theorem b103 (x : Nat → Bool) : I_b103 x = (x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat := by
  unfold I_b103
  omega
def I_t103 (x : Nat → Bool) : Nat := I_b103 x
theorem t103 (x : Nat → Bool) : I_t103 x = (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat := by
  have hs : ((I_b103 x) + ((x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat)) = (((x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat) + ((w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat)) := (add_eq (b103 x) (e88 x))
  have e1 : ((I_b103 x) + ((x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat)) = (I_t103 x) + ((x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat) := by unfold I_t103; ac_rfl
  have e2 : (((x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat) + ((w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat)) = ((w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat) + ((x 823).toNat + (x 824).toNat + (x 825).toNat + (x 826).toNat + (x 827).toNat + (x 828).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s103 (x : Nat → Bool) : I_t103 x = pc x 823 6 := rfl
def I_t104 (x : Nat → Bool) : Nat := I_t102 x + I_t103 x
theorem t104 (x : Nat → Bool) : I_t104 x = (w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat + (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat := by
  have hs : ((I_t102 x) + (I_t103 x)) = (((w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat) + ((w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat)) := (add_eq (t102 x) (t103 x))
  have e1 : ((I_t102 x) + (I_t103 x)) = I_t104 x := by unfold I_t104; ac_rfl
  have e2 : (((w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat) + ((w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat)) = (w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat + (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s104 (x : Nat → Bool) : I_t104 x = pc x 823 12 := by
  have hl := s102 x
  have hr := s103 x
  have : pc x 823 12 = pc x 823 6 + pc x 829 6 := pc_add x 823 6 6
  unfold I_t104
  omega
def I_b105 (x : Nat → Bool) : Nat := 0 + (x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat
theorem b105 (x : Nat → Bool) : I_b105 x = (x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat := by
  unfold I_b105
  omega
def I_t105 (x : Nat → Bool) : Nat := I_b105 x
theorem t105 (x : Nat → Bool) : I_t105 x = (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat := by
  have hs : ((I_b105 x) + ((x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat)) = (((x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat) + ((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat)) := (add_eq (b105 x) (e89 x))
  have e1 : ((I_b105 x) + ((x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat)) = (I_t105 x) + ((x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat) := by unfold I_t105; ac_rfl
  have e2 : (((x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat) + ((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat)) = ((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat) + ((x 835).toNat + (x 836).toNat + (x 837).toNat + (x 838).toNat + (x 839).toNat + (x 840).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s105 (x : Nat → Bool) : I_t105 x = pc x 835 6 := rfl
def I_b106 (x : Nat → Bool) : Nat := 0 + (x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat
theorem b106 (x : Nat → Bool) : I_b106 x = (x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat := by
  unfold I_b106
  omega
def I_t106 (x : Nat → Bool) : Nat := I_b106 x
theorem t106 (x : Nat → Bool) : I_t106 x = (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat := by
  have hs : ((I_b106 x) + ((x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat)) = (((x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat) + ((w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat)) := (add_eq (b106 x) (e90 x))
  have e1 : ((I_b106 x) + ((x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat)) = (I_t106 x) + ((x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat) := by unfold I_t106; ac_rfl
  have e2 : (((x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat) + ((w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat)) = ((w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat) + ((x 841).toNat + (x 842).toNat + (x 843).toNat + (x 844).toNat + (x 845).toNat + (x 846).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s106 (x : Nat → Bool) : I_t106 x = pc x 841 6 := rfl
def I_t107 (x : Nat → Bool) : Nat := I_t105 x + I_t106 x
theorem t107 (x : Nat → Bool) : I_t107 x = (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat := by
  have hs : ((I_t105 x) + (I_t106 x)) = (((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat) + ((w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat)) := (add_eq (t105 x) (t106 x))
  have e1 : ((I_t105 x) + (I_t106 x)) = I_t107 x := by unfold I_t107; ac_rfl
  have e2 : (((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat) + ((w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat)) = (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s107 (x : Nat → Bool) : I_t107 x = pc x 835 12 := by
  have hl := s105 x
  have hr := s106 x
  have : pc x 835 12 = pc x 835 6 + pc x 841 6 := pc_add x 835 6 6
  unfold I_t107
  omega
def I_t108 (x : Nat → Bool) : Nat := I_t104 x + I_t107 x
theorem t108 (x : Nat → Bool) : I_t108 x = (w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat + (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat + (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat := by
  have hs : ((I_t104 x) + (I_t107 x)) = (((w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat + (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat) + ((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat)) := (add_eq (t104 x) (t107 x))
  have e1 : ((I_t104 x) + (I_t107 x)) = I_t108 x := by unfold I_t108; ac_rfl
  have e2 : (((w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat + (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat) + ((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat)) = (w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat + (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat + (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s108 (x : Nat → Bool) : I_t108 x = pc x 823 24 := by
  have hl := s104 x
  have hr := s107 x
  have : pc x 823 24 = pc x 823 12 + pc x 835 12 := pc_add x 823 12 12
  unfold I_t108
  omega
def I_t109 (x : Nat → Bool) : Nat := I_t101 x + I_t108 x
theorem t109 (x : Nat → Bool) : I_t109 x = (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat + (w_n274 x).toNat + 2 * (w_n275 x).toNat + 4 * (w_n276 x).toNat + 2 * (w_n277 x).toNat + 4 * (w_n278 x).toNat + 8 * (w_n279 x).toNat + 4 * (w_n280 x).toNat + 8 * (w_n281 x).toNat + 16 * (w_n282 x).toNat := by
  have hs : (((((I_t101 x) + (I_t108 x)) + ((w_n250 x).toNat + (w_n253 x).toNat + (w_n256 x).toNat + (w_n259 x).toNat + (w_n262 x).toNat + (w_n265 x).toNat)) + (2 * (w_n251 x).toNat + 2 * (w_n254 x).toNat + 2 * (w_n257 x).toNat + 2 * (w_n260 x).toNat + 2 * (w_n263 x).toNat + 2 * (w_n266 x).toNat)) + (4 * (w_n252 x).toNat + 4 * (w_n255 x).toNat + 4 * (w_n258 x).toNat + 4 * (w_n261 x).toNat + 4 * (w_n264 x).toNat + 4 * (w_n267 x).toNat)) = ((((((w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat + (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat + (w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat + (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat) + ((w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat + (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat + (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat)) + ((w_n274 x).toNat + 2 * (w_n275 x).toNat + 4 * (w_n276 x).toNat)) + (2 * (w_n277 x).toNat + 4 * (w_n278 x).toNat + 8 * (w_n279 x).toNat)) + (4 * (w_n280 x).toNat + 8 * (w_n281 x).toNat + 16 * (w_n282 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t101 x) (t108 x)) (e91 x)) (e92 x)) (e93 x))
  have e1 : (((((I_t101 x) + (I_t108 x)) + ((w_n250 x).toNat + (w_n253 x).toNat + (w_n256 x).toNat + (w_n259 x).toNat + (w_n262 x).toNat + (w_n265 x).toNat)) + (2 * (w_n251 x).toNat + 2 * (w_n254 x).toNat + 2 * (w_n257 x).toNat + 2 * (w_n260 x).toNat + 2 * (w_n263 x).toNat + 2 * (w_n266 x).toNat)) + (4 * (w_n252 x).toNat + 4 * (w_n255 x).toNat + 4 * (w_n258 x).toNat + 4 * (w_n261 x).toNat + 4 * (w_n264 x).toNat + 4 * (w_n267 x).toNat)) = (I_t109 x) + ((w_n250 x).toNat + (w_n253 x).toNat + (w_n256 x).toNat + (w_n259 x).toNat + (w_n262 x).toNat + (w_n265 x).toNat + 2 * (w_n251 x).toNat + 2 * (w_n254 x).toNat + 2 * (w_n257 x).toNat + 2 * (w_n260 x).toNat + 2 * (w_n263 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n252 x).toNat + 4 * (w_n255 x).toNat + 4 * (w_n258 x).toNat + 4 * (w_n261 x).toNat + 4 * (w_n264 x).toNat + 4 * (w_n267 x).toNat) := by unfold I_t109; ac_rfl
  have e2 : ((((((w_n250 x).toNat + 2 * (w_n251 x).toNat + 4 * (w_n252 x).toNat + (w_n253 x).toNat + 2 * (w_n254 x).toNat + 4 * (w_n255 x).toNat + (w_n256 x).toNat + 2 * (w_n257 x).toNat + 4 * (w_n258 x).toNat + (w_n259 x).toNat + 2 * (w_n260 x).toNat + 4 * (w_n261 x).toNat) + ((w_n262 x).toNat + 2 * (w_n263 x).toNat + 4 * (w_n264 x).toNat + (w_n265 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n267 x).toNat + (w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat)) + ((w_n274 x).toNat + 2 * (w_n275 x).toNat + 4 * (w_n276 x).toNat)) + (2 * (w_n277 x).toNat + 4 * (w_n278 x).toNat + 8 * (w_n279 x).toNat)) + (4 * (w_n280 x).toNat + 8 * (w_n281 x).toNat + 16 * (w_n282 x).toNat)) = ((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat + (w_n274 x).toNat + 2 * (w_n275 x).toNat + 4 * (w_n276 x).toNat + 2 * (w_n277 x).toNat + 4 * (w_n278 x).toNat + 8 * (w_n279 x).toNat + 4 * (w_n280 x).toNat + 8 * (w_n281 x).toNat + 16 * (w_n282 x).toNat) + ((w_n250 x).toNat + (w_n253 x).toNat + (w_n256 x).toNat + (w_n259 x).toNat + (w_n262 x).toNat + (w_n265 x).toNat + 2 * (w_n251 x).toNat + 2 * (w_n254 x).toNat + 2 * (w_n257 x).toNat + 2 * (w_n260 x).toNat + 2 * (w_n263 x).toNat + 2 * (w_n266 x).toNat + 4 * (w_n252 x).toNat + 4 * (w_n255 x).toNat + 4 * (w_n258 x).toNat + 4 * (w_n261 x).toNat + 4 * (w_n264 x).toNat + 4 * (w_n267 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s109 (x : Nat → Bool) : I_t109 x = pc x 799 48 := by
  have hl := s101 x
  have hr := s108 x
  have : pc x 799 48 = pc x 799 24 + pc x 823 24 := pc_add x 799 24 24
  unfold I_t109
  omega
def I_b110 (x : Nat → Bool) : Nat := 0 + (x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat
theorem b110 (x : Nat → Bool) : I_b110 x = (x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat := by
  unfold I_b110
  omega
def I_t110 (x : Nat → Bool) : Nat := I_b110 x
theorem t110 (x : Nat → Bool) : I_t110 x = (w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat := by
  have hs : ((I_b110 x) + ((x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat)) = (((x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat) + ((w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat)) := (add_eq (b110 x) (e94 x))
  have e1 : ((I_b110 x) + ((x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat)) = (I_t110 x) + ((x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat) := by unfold I_t110; ac_rfl
  have e2 : (((x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat) + ((w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat)) = ((w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat) + ((x 757).toNat + (x 758).toNat + (x 759).toNat + (x 760).toNat + (x 761).toNat + (x 762).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s110 (x : Nat → Bool) : I_t110 x = pc x 757 6 := rfl
def I_b111 (x : Nat → Bool) : Nat := 0 + (x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat
theorem b111 (x : Nat → Bool) : I_b111 x = (x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat := by
  unfold I_b111
  omega
def I_t111 (x : Nat → Bool) : Nat := I_b111 x
theorem t111 (x : Nat → Bool) : I_t111 x = (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat := by
  have hs : ((I_b111 x) + ((x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat)) = (((x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat) + ((w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat)) := (add_eq (b111 x) (e95 x))
  have e1 : ((I_b111 x) + ((x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat)) = (I_t111 x) + ((x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat) := by unfold I_t111; ac_rfl
  have e2 : (((x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat) + ((w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat)) = ((w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat) + ((x 751).toNat + (x 752).toNat + (x 753).toNat + (x 754).toNat + (x 755).toNat + (x 756).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s111 (x : Nat → Bool) : I_t111 x = pc x 751 6 := rfl
def I_t112 (x : Nat → Bool) : Nat := I_t110 x + I_t111 x
theorem t112 (x : Nat → Bool) : I_t112 x = (w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat + (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat := by
  have hs : ((I_t110 x) + (I_t111 x)) = (((w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat) + ((w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat)) := (add_eq (t110 x) (t111 x))
  have e1 : ((I_t110 x) + (I_t111 x)) = I_t112 x := by unfold I_t112; ac_rfl
  have e2 : (((w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat) + ((w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat)) = (w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat + (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s112 (x : Nat → Bool) : I_t112 x = pc x 751 12 := by
  have hl := s110 x
  have hr := s111 x
  have : pc x 751 12 = pc x 751 6 + pc x 757 6 := pc_add x 751 6 6
  unfold I_t112
  omega
def I_b113 (x : Nat → Bool) : Nat := 0 + (x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat
theorem b113 (x : Nat → Bool) : I_b113 x = (x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat := by
  unfold I_b113
  omega
def I_t113 (x : Nat → Bool) : Nat := I_b113 x
theorem t113 (x : Nat → Bool) : I_t113 x = (w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat := by
  have hs : ((I_b113 x) + ((x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat)) = (((x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat) + ((w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat)) := (add_eq (b113 x) (e96 x))
  have e1 : ((I_b113 x) + ((x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat)) = (I_t113 x) + ((x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat) := by unfold I_t113; ac_rfl
  have e2 : (((x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat) + ((w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat)) = ((w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat) + ((x 769).toNat + (x 770).toNat + (x 771).toNat + (x 772).toNat + (x 773).toNat + (x 774).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s113 (x : Nat → Bool) : I_t113 x = pc x 769 6 := rfl
def I_b114 (x : Nat → Bool) : Nat := 0 + (x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat
theorem b114 (x : Nat → Bool) : I_b114 x = (x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat := by
  unfold I_b114
  omega
def I_t114 (x : Nat → Bool) : Nat := I_b114 x
theorem t114 (x : Nat → Bool) : I_t114 x = (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat := by
  have hs : ((I_b114 x) + ((x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat)) = (((x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat) + ((w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat)) := (add_eq (b114 x) (e97 x))
  have e1 : ((I_b114 x) + ((x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat)) = (I_t114 x) + ((x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat) := by unfold I_t114; ac_rfl
  have e2 : (((x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat) + ((w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat)) = ((w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat) + ((x 763).toNat + (x 764).toNat + (x 765).toNat + (x 766).toNat + (x 767).toNat + (x 768).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s114 (x : Nat → Bool) : I_t114 x = pc x 763 6 := rfl
def I_t115 (x : Nat → Bool) : Nat := I_t113 x + I_t114 x
theorem t115 (x : Nat → Bool) : I_t115 x = (w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat + (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat := by
  have hs : ((I_t113 x) + (I_t114 x)) = (((w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat) + ((w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat)) := (add_eq (t113 x) (t114 x))
  have e1 : ((I_t113 x) + (I_t114 x)) = I_t115 x := by unfold I_t115; ac_rfl
  have e2 : (((w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat) + ((w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat)) = (w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat + (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s115 (x : Nat → Bool) : I_t115 x = pc x 763 12 := by
  have hl := s113 x
  have hr := s114 x
  have : pc x 763 12 = pc x 763 6 + pc x 769 6 := pc_add x 763 6 6
  unfold I_t115
  omega
def I_t116 (x : Nat → Bool) : Nat := I_t112 x + I_t115 x
theorem t116 (x : Nat → Bool) : I_t116 x = (w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat + (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat + (w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat + (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat := by
  have hs : ((I_t112 x) + (I_t115 x)) = (((w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat + (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat) + ((w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat + (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat)) := (add_eq (t112 x) (t115 x))
  have e1 : ((I_t112 x) + (I_t115 x)) = I_t116 x := by unfold I_t116; ac_rfl
  have e2 : (((w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat + (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat) + ((w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat + (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat)) = (w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat + (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat + (w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat + (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s116 (x : Nat → Bool) : I_t116 x = pc x 751 24 := by
  have hl := s112 x
  have hr := s115 x
  have : pc x 751 24 = pc x 751 12 + pc x 763 12 := pc_add x 751 12 12
  unfold I_t116
  omega
def I_b117 (x : Nat → Bool) : Nat := 0 + (x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat
theorem b117 (x : Nat → Bool) : I_b117 x = (x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat := by
  unfold I_b117
  omega
def I_t117 (x : Nat → Bool) : Nat := I_b117 x
theorem t117 (x : Nat → Bool) : I_t117 x = (w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat := by
  have hs : ((I_b117 x) + ((x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat)) = (((x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat) + ((w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat)) := (add_eq (b117 x) (e98 x))
  have e1 : ((I_b117 x) + ((x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat)) = (I_t117 x) + ((x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat) := by unfold I_t117; ac_rfl
  have e2 : (((x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat) + ((w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat)) = ((w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat) + ((x 775).toNat + (x 776).toNat + (x 777).toNat + (x 778).toNat + (x 779).toNat + (x 780).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s117 (x : Nat → Bool) : I_t117 x = pc x 775 6 := rfl
def I_b118 (x : Nat → Bool) : Nat := 0 + (x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat
theorem b118 (x : Nat → Bool) : I_b118 x = (x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat := by
  unfold I_b118
  omega
def I_t118 (x : Nat → Bool) : Nat := I_b118 x
theorem t118 (x : Nat → Bool) : I_t118 x = (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat := by
  have hs : ((I_b118 x) + ((x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat)) = (((x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat) + ((w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat)) := (add_eq (b118 x) (e99 x))
  have e1 : ((I_b118 x) + ((x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat)) = (I_t118 x) + ((x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat) := by unfold I_t118; ac_rfl
  have e2 : (((x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat) + ((w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat)) = ((w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat) + ((x 781).toNat + (x 782).toNat + (x 783).toNat + (x 784).toNat + (x 785).toNat + (x 786).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s118 (x : Nat → Bool) : I_t118 x = pc x 781 6 := rfl
def I_t119 (x : Nat → Bool) : Nat := I_t117 x + I_t118 x
theorem t119 (x : Nat → Bool) : I_t119 x = (w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat + (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat := by
  have hs : ((I_t117 x) + (I_t118 x)) = (((w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat) + ((w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat)) := (add_eq (t117 x) (t118 x))
  have e1 : ((I_t117 x) + (I_t118 x)) = I_t119 x := by unfold I_t119; ac_rfl
  have e2 : (((w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat) + ((w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat)) = (w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat + (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s119 (x : Nat → Bool) : I_t119 x = pc x 775 12 := by
  have hl := s117 x
  have hr := s118 x
  have : pc x 775 12 = pc x 775 6 + pc x 781 6 := pc_add x 775 6 6
  unfold I_t119
  omega
def I_b120 (x : Nat → Bool) : Nat := 0 + (x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat
theorem b120 (x : Nat → Bool) : I_b120 x = (x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat := by
  unfold I_b120
  omega
def I_t120 (x : Nat → Bool) : Nat := I_b120 x
theorem t120 (x : Nat → Bool) : I_t120 x = (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat := by
  have hs : ((I_b120 x) + ((x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat)) = (((x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat) + ((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat)) := (add_eq (b120 x) (e100 x))
  have e1 : ((I_b120 x) + ((x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat)) = (I_t120 x) + ((x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat) := by unfold I_t120; ac_rfl
  have e2 : (((x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat) + ((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat)) = ((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat) + ((x 787).toNat + (x 788).toNat + (x 789).toNat + (x 790).toNat + (x 791).toNat + (x 792).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s120 (x : Nat → Bool) : I_t120 x = pc x 787 6 := rfl
def I_b121 (x : Nat → Bool) : Nat := 0 + (x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat
theorem b121 (x : Nat → Bool) : I_b121 x = (x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat := by
  unfold I_b121
  omega
def I_t121 (x : Nat → Bool) : Nat := I_b121 x
theorem t121 (x : Nat → Bool) : I_t121 x = (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat := by
  have hs : ((I_b121 x) + ((x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat)) = (((x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat) + ((w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat)) := (add_eq (b121 x) (e101 x))
  have e1 : ((I_b121 x) + ((x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat)) = (I_t121 x) + ((x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat) := by unfold I_t121; ac_rfl
  have e2 : (((x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat) + ((w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat)) = ((w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat) + ((x 793).toNat + (x 794).toNat + (x 795).toNat + (x 796).toNat + (x 797).toNat + (x 798).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s121 (x : Nat → Bool) : I_t121 x = pc x 793 6 := rfl
def I_t122 (x : Nat → Bool) : Nat := I_t120 x + I_t121 x
theorem t122 (x : Nat → Bool) : I_t122 x = (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat := by
  have hs : ((I_t120 x) + (I_t121 x)) = (((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat) + ((w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat)) := (add_eq (t120 x) (t121 x))
  have e1 : ((I_t120 x) + (I_t121 x)) = I_t122 x := by unfold I_t122; ac_rfl
  have e2 : (((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat) + ((w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat)) = (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s122 (x : Nat → Bool) : I_t122 x = pc x 787 12 := by
  have hl := s120 x
  have hr := s121 x
  have : pc x 787 12 = pc x 787 6 + pc x 793 6 := pc_add x 787 6 6
  unfold I_t122
  omega
def I_t123 (x : Nat → Bool) : Nat := I_t119 x + I_t122 x
theorem t123 (x : Nat → Bool) : I_t123 x = (w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat + (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat + (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat := by
  have hs : ((I_t119 x) + (I_t122 x)) = (((w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat + (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat) + ((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat)) := (add_eq (t119 x) (t122 x))
  have e1 : ((I_t119 x) + (I_t122 x)) = I_t123 x := by unfold I_t123; ac_rfl
  have e2 : (((w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat + (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat) + ((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat)) = (w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat + (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat + (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s123 (x : Nat → Bool) : I_t123 x = pc x 775 24 := by
  have hl := s119 x
  have hr := s122 x
  have : pc x 775 24 = pc x 775 12 + pc x 787 12 := pc_add x 775 12 12
  unfold I_t123
  omega
def I_t124 (x : Nat → Bool) : Nat := I_t116 x + I_t123 x
theorem t124 (x : Nat → Bool) : I_t124 x = (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat + (w_n307 x).toNat + 2 * (w_n308 x).toNat + 4 * (w_n309 x).toNat + 2 * (w_n310 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n312 x).toNat + 4 * (w_n313 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n315 x).toNat := by
  have hs : (((((I_t116 x) + (I_t123 x)) + ((w_n283 x).toNat + (w_n286 x).toNat + (w_n289 x).toNat + (w_n292 x).toNat + (w_n295 x).toNat + (w_n298 x).toNat)) + (2 * (w_n284 x).toNat + 2 * (w_n287 x).toNat + 2 * (w_n290 x).toNat + 2 * (w_n293 x).toNat + 2 * (w_n296 x).toNat + 2 * (w_n299 x).toNat)) + (4 * (w_n285 x).toNat + 4 * (w_n288 x).toNat + 4 * (w_n291 x).toNat + 4 * (w_n294 x).toNat + 4 * (w_n297 x).toNat + 4 * (w_n300 x).toNat)) = ((((((w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat + (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat + (w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat + (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat) + ((w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat + (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat + (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat)) + ((w_n307 x).toNat + 2 * (w_n308 x).toNat + 4 * (w_n309 x).toNat)) + (2 * (w_n310 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n312 x).toNat)) + (4 * (w_n313 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n315 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t116 x) (t123 x)) (e102 x)) (e103 x)) (e104 x))
  have e1 : (((((I_t116 x) + (I_t123 x)) + ((w_n283 x).toNat + (w_n286 x).toNat + (w_n289 x).toNat + (w_n292 x).toNat + (w_n295 x).toNat + (w_n298 x).toNat)) + (2 * (w_n284 x).toNat + 2 * (w_n287 x).toNat + 2 * (w_n290 x).toNat + 2 * (w_n293 x).toNat + 2 * (w_n296 x).toNat + 2 * (w_n299 x).toNat)) + (4 * (w_n285 x).toNat + 4 * (w_n288 x).toNat + 4 * (w_n291 x).toNat + 4 * (w_n294 x).toNat + 4 * (w_n297 x).toNat + 4 * (w_n300 x).toNat)) = (I_t124 x) + ((w_n283 x).toNat + (w_n286 x).toNat + (w_n289 x).toNat + (w_n292 x).toNat + (w_n295 x).toNat + (w_n298 x).toNat + 2 * (w_n284 x).toNat + 2 * (w_n287 x).toNat + 2 * (w_n290 x).toNat + 2 * (w_n293 x).toNat + 2 * (w_n296 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n285 x).toNat + 4 * (w_n288 x).toNat + 4 * (w_n291 x).toNat + 4 * (w_n294 x).toNat + 4 * (w_n297 x).toNat + 4 * (w_n300 x).toNat) := by unfold I_t124; ac_rfl
  have e2 : ((((((w_n283 x).toNat + 2 * (w_n284 x).toNat + 4 * (w_n285 x).toNat + (w_n286 x).toNat + 2 * (w_n287 x).toNat + 4 * (w_n288 x).toNat + (w_n289 x).toNat + 2 * (w_n290 x).toNat + 4 * (w_n291 x).toNat + (w_n292 x).toNat + 2 * (w_n293 x).toNat + 4 * (w_n294 x).toNat) + ((w_n295 x).toNat + 2 * (w_n296 x).toNat + 4 * (w_n297 x).toNat + (w_n298 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n300 x).toNat + (w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat)) + ((w_n307 x).toNat + 2 * (w_n308 x).toNat + 4 * (w_n309 x).toNat)) + (2 * (w_n310 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n312 x).toNat)) + (4 * (w_n313 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n315 x).toNat)) = ((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat + (w_n307 x).toNat + 2 * (w_n308 x).toNat + 4 * (w_n309 x).toNat + 2 * (w_n310 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n312 x).toNat + 4 * (w_n313 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n315 x).toNat) + ((w_n283 x).toNat + (w_n286 x).toNat + (w_n289 x).toNat + (w_n292 x).toNat + (w_n295 x).toNat + (w_n298 x).toNat + 2 * (w_n284 x).toNat + 2 * (w_n287 x).toNat + 2 * (w_n290 x).toNat + 2 * (w_n293 x).toNat + 2 * (w_n296 x).toNat + 2 * (w_n299 x).toNat + 4 * (w_n285 x).toNat + 4 * (w_n288 x).toNat + 4 * (w_n291 x).toNat + 4 * (w_n294 x).toNat + 4 * (w_n297 x).toNat + 4 * (w_n300 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s124 (x : Nat → Bool) : I_t124 x = pc x 751 48 := by
  have hl := s116 x
  have hr := s123 x
  have : pc x 751 48 = pc x 751 24 + pc x 775 24 := pc_add x 751 24 24
  unfold I_t124
  omega
def I_t125 (x : Nat → Bool) : Nat := I_t109 x + I_t124 x
theorem t125 (x : Nat → Bool) : I_t125 x = 16 * (w_n282 x).toNat + 2 * (w_n308 x).toNat + 2 * (w_n310 x).toNat + 16 * (w_n315 x).toNat + (w_n316 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 4 * (w_n322 x).toNat + 16 * (w_n324 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat + 8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat := by
  have hs : (((((((I_t109 x) + (I_t124 x)) + ((w_n268 x).toNat + (w_n271 x).toNat + (w_n274 x).toNat + (w_n301 x).toNat + (w_n304 x).toNat + (w_n307 x).toNat)) + (2 * (w_n269 x).toNat + 2 * (w_n272 x).toNat + 2 * (w_n275 x).toNat + 2 * (w_n277 x).toNat + 2 * (w_n302 x).toNat + 2 * (w_n305 x).toNat)) + (4 * (w_n270 x).toNat + 4 * (w_n273 x).toNat + 4 * (w_n276 x).toNat + 4 * (w_n278 x).toNat + 4 * (w_n280 x).toNat + 4 * (w_n303 x).toNat)) + (4 * (w_n306 x).toNat + 4 * (w_n309 x).toNat + 4 * (w_n311 x).toNat + 4 * (w_n313 x).toNat + 4 * (w_n318 x).toNat + 4 * (w_n320 x).toNat)) + (8 * (w_n279 x).toNat + 8 * (w_n281 x).toNat + 8 * (w_n312 x).toNat + 8 * (w_n314 x).toNat + 8 * (w_n321 x).toNat + 8 * (w_n323 x).toNat)) = ((((((((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat + (w_n274 x).toNat + 2 * (w_n275 x).toNat + 4 * (w_n276 x).toNat + 2 * (w_n277 x).toNat + 4 * (w_n278 x).toNat + 8 * (w_n279 x).toNat + 4 * (w_n280 x).toNat + 8 * (w_n281 x).toNat + 16 * (w_n282 x).toNat) + ((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat + (w_n307 x).toNat + 2 * (w_n308 x).toNat + 4 * (w_n309 x).toNat + 2 * (w_n310 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n312 x).toNat + 4 * (w_n313 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n315 x).toNat)) + ((w_n316 x).toNat + 2 * (w_n317 x).toNat + 4 * (w_n318 x).toNat)) + (2 * (w_n319 x).toNat + 4 * (w_n320 x).toNat + 8 * (w_n321 x).toNat)) + (4 * (w_n322 x).toNat + 8 * (w_n323 x).toNat + 16 * (w_n324 x).toNat)) + (4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat)) + (8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t109 x) (t124 x)) (e105 x)) (e106 x)) (e107 x)) (e108 x)) (e109 x))
  have e1 : (((((((I_t109 x) + (I_t124 x)) + ((w_n268 x).toNat + (w_n271 x).toNat + (w_n274 x).toNat + (w_n301 x).toNat + (w_n304 x).toNat + (w_n307 x).toNat)) + (2 * (w_n269 x).toNat + 2 * (w_n272 x).toNat + 2 * (w_n275 x).toNat + 2 * (w_n277 x).toNat + 2 * (w_n302 x).toNat + 2 * (w_n305 x).toNat)) + (4 * (w_n270 x).toNat + 4 * (w_n273 x).toNat + 4 * (w_n276 x).toNat + 4 * (w_n278 x).toNat + 4 * (w_n280 x).toNat + 4 * (w_n303 x).toNat)) + (4 * (w_n306 x).toNat + 4 * (w_n309 x).toNat + 4 * (w_n311 x).toNat + 4 * (w_n313 x).toNat + 4 * (w_n318 x).toNat + 4 * (w_n320 x).toNat)) + (8 * (w_n279 x).toNat + 8 * (w_n281 x).toNat + 8 * (w_n312 x).toNat + 8 * (w_n314 x).toNat + 8 * (w_n321 x).toNat + 8 * (w_n323 x).toNat)) = (I_t125 x) + ((w_n268 x).toNat + (w_n271 x).toNat + (w_n274 x).toNat + (w_n301 x).toNat + (w_n304 x).toNat + (w_n307 x).toNat + 2 * (w_n269 x).toNat + 2 * (w_n272 x).toNat + 2 * (w_n275 x).toNat + 2 * (w_n277 x).toNat + 2 * (w_n302 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n270 x).toNat + 4 * (w_n273 x).toNat + 4 * (w_n276 x).toNat + 4 * (w_n278 x).toNat + 4 * (w_n280 x).toNat + 4 * (w_n303 x).toNat + 4 * (w_n306 x).toNat + 4 * (w_n309 x).toNat + 4 * (w_n311 x).toNat + 4 * (w_n313 x).toNat + 4 * (w_n318 x).toNat + 4 * (w_n320 x).toNat + 8 * (w_n279 x).toNat + 8 * (w_n281 x).toNat + 8 * (w_n312 x).toNat + 8 * (w_n314 x).toNat + 8 * (w_n321 x).toNat + 8 * (w_n323 x).toNat) := by unfold I_t125; ac_rfl
  have e2 : ((((((((w_n268 x).toNat + 2 * (w_n269 x).toNat + 4 * (w_n270 x).toNat + (w_n271 x).toNat + 2 * (w_n272 x).toNat + 4 * (w_n273 x).toNat + (w_n274 x).toNat + 2 * (w_n275 x).toNat + 4 * (w_n276 x).toNat + 2 * (w_n277 x).toNat + 4 * (w_n278 x).toNat + 8 * (w_n279 x).toNat + 4 * (w_n280 x).toNat + 8 * (w_n281 x).toNat + 16 * (w_n282 x).toNat) + ((w_n301 x).toNat + 2 * (w_n302 x).toNat + 4 * (w_n303 x).toNat + (w_n304 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n306 x).toNat + (w_n307 x).toNat + 2 * (w_n308 x).toNat + 4 * (w_n309 x).toNat + 2 * (w_n310 x).toNat + 4 * (w_n311 x).toNat + 8 * (w_n312 x).toNat + 4 * (w_n313 x).toNat + 8 * (w_n314 x).toNat + 16 * (w_n315 x).toNat)) + ((w_n316 x).toNat + 2 * (w_n317 x).toNat + 4 * (w_n318 x).toNat)) + (2 * (w_n319 x).toNat + 4 * (w_n320 x).toNat + 8 * (w_n321 x).toNat)) + (4 * (w_n322 x).toNat + 8 * (w_n323 x).toNat + 16 * (w_n324 x).toNat)) + (4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat)) + (8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat)) = (16 * (w_n282 x).toNat + 2 * (w_n308 x).toNat + 2 * (w_n310 x).toNat + 16 * (w_n315 x).toNat + (w_n316 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 4 * (w_n322 x).toNat + 16 * (w_n324 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat + 8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat) + ((w_n268 x).toNat + (w_n271 x).toNat + (w_n274 x).toNat + (w_n301 x).toNat + (w_n304 x).toNat + (w_n307 x).toNat + 2 * (w_n269 x).toNat + 2 * (w_n272 x).toNat + 2 * (w_n275 x).toNat + 2 * (w_n277 x).toNat + 2 * (w_n302 x).toNat + 2 * (w_n305 x).toNat + 4 * (w_n270 x).toNat + 4 * (w_n273 x).toNat + 4 * (w_n276 x).toNat + 4 * (w_n278 x).toNat + 4 * (w_n280 x).toNat + 4 * (w_n303 x).toNat + 4 * (w_n306 x).toNat + 4 * (w_n309 x).toNat + 4 * (w_n311 x).toNat + 4 * (w_n313 x).toNat + 4 * (w_n318 x).toNat + 4 * (w_n320 x).toNat + 8 * (w_n279 x).toNat + 8 * (w_n281 x).toNat + 8 * (w_n312 x).toNat + 8 * (w_n314 x).toNat + 8 * (w_n321 x).toNat + 8 * (w_n323 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s125 (x : Nat → Bool) : I_t125 x = pc x 751 96 := by
  have hl := s109 x
  have hr := s124 x
  have : pc x 751 96 = pc x 751 48 + pc x 799 48 := pc_add x 751 48 48
  unfold I_t125
  omega
def I_t126 (x : Nat → Bool) : Nat := I_t94 x + I_t125 x
theorem t126 (x : Nat → Bool) : I_t126 x = (w_n235 x).toNat + 4 * (w_n241 x).toNat + 4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 8 * (w_n247 x).toNat + 32 * (w_n249 x).toNat + 16 * (w_n315 x).toNat + (w_n316 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 4 * (w_n322 x).toNat + 16 * (w_n324 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat + 8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat + 2 * (w_n331 x).toNat + 4 * (w_n332 x).toNat + 8 * (w_n333 x).toNat + 16 * (w_n334 x).toNat + 32 * (w_n335 x).toNat + 64 * (w_n336 x).toNat := by
  have hs : ((((I_t94 x) + (I_t125 x)) + (2 * (w_n227 x).toNat + 2 * (w_n229 x).toNat + 2 * (w_n236 x).toNat + 2 * (w_n238 x).toNat + 2 * (w_n308 x).toNat + 2 * (w_n310 x).toNat)) + (16 * (w_n201 x).toNat + 16 * (w_n234 x).toNat + 16 * (w_n243 x).toNat + 16 * (w_n246 x).toNat + 16 * (w_n248 x).toNat + 16 * (w_n282 x).toNat)) = ((((16 * (w_n201 x).toNat + 2 * (w_n227 x).toNat + 2 * (w_n229 x).toNat + 16 * (w_n234 x).toNat + (w_n235 x).toNat + 2 * (w_n236 x).toNat + 2 * (w_n238 x).toNat + 4 * (w_n241 x).toNat + 16 * (w_n243 x).toNat + 4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 16 * (w_n246 x).toNat + 8 * (w_n247 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n249 x).toNat) + (16 * (w_n282 x).toNat + 2 * (w_n308 x).toNat + 2 * (w_n310 x).toNat + 16 * (w_n315 x).toNat + (w_n316 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 4 * (w_n322 x).toNat + 16 * (w_n324 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat + 8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat)) + (2 * (w_n331 x).toNat + 4 * (w_n332 x).toNat + 8 * (w_n333 x).toNat)) + (16 * (w_n334 x).toNat + 32 * (w_n335 x).toNat + 64 * (w_n336 x).toNat)) := (add_eq (add_eq (add_eq (t94 x) (t125 x)) (e110 x)) (e111 x))
  have e1 : ((((I_t94 x) + (I_t125 x)) + (2 * (w_n227 x).toNat + 2 * (w_n229 x).toNat + 2 * (w_n236 x).toNat + 2 * (w_n238 x).toNat + 2 * (w_n308 x).toNat + 2 * (w_n310 x).toNat)) + (16 * (w_n201 x).toNat + 16 * (w_n234 x).toNat + 16 * (w_n243 x).toNat + 16 * (w_n246 x).toNat + 16 * (w_n248 x).toNat + 16 * (w_n282 x).toNat)) = (I_t126 x) + (2 * (w_n227 x).toNat + 2 * (w_n229 x).toNat + 2 * (w_n236 x).toNat + 2 * (w_n238 x).toNat + 2 * (w_n308 x).toNat + 2 * (w_n310 x).toNat + 16 * (w_n201 x).toNat + 16 * (w_n234 x).toNat + 16 * (w_n243 x).toNat + 16 * (w_n246 x).toNat + 16 * (w_n248 x).toNat + 16 * (w_n282 x).toNat) := by unfold I_t126; ac_rfl
  have e2 : ((((16 * (w_n201 x).toNat + 2 * (w_n227 x).toNat + 2 * (w_n229 x).toNat + 16 * (w_n234 x).toNat + (w_n235 x).toNat + 2 * (w_n236 x).toNat + 2 * (w_n238 x).toNat + 4 * (w_n241 x).toNat + 16 * (w_n243 x).toNat + 4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 16 * (w_n246 x).toNat + 8 * (w_n247 x).toNat + 16 * (w_n248 x).toNat + 32 * (w_n249 x).toNat) + (16 * (w_n282 x).toNat + 2 * (w_n308 x).toNat + 2 * (w_n310 x).toNat + 16 * (w_n315 x).toNat + (w_n316 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 4 * (w_n322 x).toNat + 16 * (w_n324 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat + 8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat)) + (2 * (w_n331 x).toNat + 4 * (w_n332 x).toNat + 8 * (w_n333 x).toNat)) + (16 * (w_n334 x).toNat + 32 * (w_n335 x).toNat + 64 * (w_n336 x).toNat)) = ((w_n235 x).toNat + 4 * (w_n241 x).toNat + 4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 8 * (w_n247 x).toNat + 32 * (w_n249 x).toNat + 16 * (w_n315 x).toNat + (w_n316 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 4 * (w_n322 x).toNat + 16 * (w_n324 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat + 8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat + 2 * (w_n331 x).toNat + 4 * (w_n332 x).toNat + 8 * (w_n333 x).toNat + 16 * (w_n334 x).toNat + 32 * (w_n335 x).toNat + 64 * (w_n336 x).toNat) + (2 * (w_n227 x).toNat + 2 * (w_n229 x).toNat + 2 * (w_n236 x).toNat + 2 * (w_n238 x).toNat + 2 * (w_n308 x).toNat + 2 * (w_n310 x).toNat + 16 * (w_n201 x).toNat + 16 * (w_n234 x).toNat + 16 * (w_n243 x).toNat + 16 * (w_n246 x).toNat + 16 * (w_n248 x).toNat + 16 * (w_n282 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s126 (x : Nat → Bool) : I_t126 x = pc x 655 192 := by
  have hl := s94 x
  have hr := s125 x
  have : pc x 655 192 = pc x 655 96 + pc x 751 96 := pc_add x 655 96 96
  unfold I_t126
  omega
def I_t127 (x : Nat → Bool) : Nat := I_t63 x + I_t126 x
theorem t127 (x : Nat → Bool) : I_t127 x = (w_n67 x).toNat + (w_n148 x).toNat + 64 * (w_n168 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + 64 * (w_n336 x).toNat + 2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 8 * (w_n344 x).toNat + 8 * (w_n346 x).toNat + 16 * (w_n347 x).toNat + 32 * (w_n348 x).toNat + 8 * (w_n349 x).toNat + 16 * (w_n350 x).toNat + 32 * (w_n351 x).toNat + 16 * (w_n352 x).toNat + 32 * (w_n353 x).toNat + 64 * (w_n354 x).toNat + 16 * (w_n355 x).toNat + 32 * (w_n356 x).toNat + 64 * (w_n357 x).toNat + 32 * (w_n358 x).toNat + 64 * (w_n359 x).toNat + 128 * (w_n360 x).toNat := by
  have hs : ((((((((((I_t63 x) + (I_t126 x)) + (2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 2 * (w_n163 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 2 * (w_n331 x).toNat)) + (4 * (w_n73 x).toNat + 4 * (w_n76 x).toNat + 4 * (w_n154 x).toNat + 4 * (w_n157 x).toNat + 4 * (w_n164 x).toNat + 4 * (w_n241 x).toNat)) + (4 * (w_n244 x).toNat + 4 * (w_n322 x).toNat + 4 * (w_n325 x).toNat + 4 * (w_n332 x).toNat + 4 * (w_n338 x).toNat + 4 * (w_n340 x).toNat)) + (8 * (w_n77 x).toNat + 8 * (w_n79 x).toNat + 8 * (w_n158 x).toNat + 8 * (w_n160 x).toNat + 8 * (w_n165 x).toNat + 8 * (w_n245 x).toNat)) + (8 * (w_n247 x).toNat + 8 * (w_n326 x).toNat + 8 * (w_n328 x).toNat + 8 * (w_n333 x).toNat + 8 * (w_n339 x).toNat + 8 * (w_n341 x).toNat)) + (16 * (w_n147 x).toNat + 16 * (w_n156 x).toNat + 16 * (w_n159 x).toNat + 16 * (w_n161 x).toNat + 16 * (w_n166 x).toNat + 16 * (w_n315 x).toNat)) + (16 * (w_n324 x).toNat + 16 * (w_n327 x).toNat + 16 * (w_n329 x).toNat + 16 * (w_n334 x).toNat + 16 * (w_n342 x).toNat + 16 * (w_n345 x).toNat)) + (32 * (w_n81 x).toNat + 32 * (w_n162 x).toNat + 32 * (w_n167 x).toNat + 32 * (w_n249 x).toNat + 32 * (w_n330 x).toNat + 32 * (w_n335 x).toNat)) = (((((((((((w_n67 x).toNat + 4 * (w_n73 x).toNat + 4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 8 * (w_n79 x).toNat + 32 * (w_n81 x).toNat + 16 * (w_n147 x).toNat + (w_n148 x).toNat + 2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n154 x).toNat + 16 * (w_n156 x).toNat + 4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat + 2 * (w_n163 x).toNat + 4 * (w_n164 x).toNat + 8 * (w_n165 x).toNat + 16 * (w_n166 x).toNat + 32 * (w_n167 x).toNat + 64 * (w_n168 x).toNat) + ((w_n235 x).toNat + 4 * (w_n241 x).toNat + 4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 8 * (w_n247 x).toNat + 32 * (w_n249 x).toNat + 16 * (w_n315 x).toNat + (w_n316 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 4 * (w_n322 x).toNat + 16 * (w_n324 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat + 8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat + 2 * (w_n331 x).toNat + 4 * (w_n332 x).toNat + 8 * (w_n333 x).toNat + 16 * (w_n334 x).toNat + 32 * (w_n335 x).toNat + 64 * (w_n336 x).toNat)) + (2 * (w_n337 x).toNat + 4 * (w_n338 x).toNat + 8 * (w_n339 x).toNat)) + (4 * (w_n340 x).toNat + 8 * (w_n341 x).toNat + 16 * (w_n342 x).toNat)) + (4 * (w_n343 x).toNat + 8 * (w_n344 x).toNat + 16 * (w_n345 x).toNat)) + (8 * (w_n346 x).toNat + 16 * (w_n347 x).toNat + 32 * (w_n348 x).toNat)) + (8 * (w_n349 x).toNat + 16 * (w_n350 x).toNat + 32 * (w_n351 x).toNat)) + (16 * (w_n352 x).toNat + 32 * (w_n353 x).toNat + 64 * (w_n354 x).toNat)) + (16 * (w_n355 x).toNat + 32 * (w_n356 x).toNat + 64 * (w_n357 x).toNat)) + (32 * (w_n358 x).toNat + 64 * (w_n359 x).toNat + 128 * (w_n360 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t63 x) (t126 x)) (e112 x)) (e113 x)) (e114 x)) (e115 x)) (e116 x)) (e117 x)) (e118 x)) (e119 x))
  have e1 : ((((((((((I_t63 x) + (I_t126 x)) + (2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 2 * (w_n163 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 2 * (w_n331 x).toNat)) + (4 * (w_n73 x).toNat + 4 * (w_n76 x).toNat + 4 * (w_n154 x).toNat + 4 * (w_n157 x).toNat + 4 * (w_n164 x).toNat + 4 * (w_n241 x).toNat)) + (4 * (w_n244 x).toNat + 4 * (w_n322 x).toNat + 4 * (w_n325 x).toNat + 4 * (w_n332 x).toNat + 4 * (w_n338 x).toNat + 4 * (w_n340 x).toNat)) + (8 * (w_n77 x).toNat + 8 * (w_n79 x).toNat + 8 * (w_n158 x).toNat + 8 * (w_n160 x).toNat + 8 * (w_n165 x).toNat + 8 * (w_n245 x).toNat)) + (8 * (w_n247 x).toNat + 8 * (w_n326 x).toNat + 8 * (w_n328 x).toNat + 8 * (w_n333 x).toNat + 8 * (w_n339 x).toNat + 8 * (w_n341 x).toNat)) + (16 * (w_n147 x).toNat + 16 * (w_n156 x).toNat + 16 * (w_n159 x).toNat + 16 * (w_n161 x).toNat + 16 * (w_n166 x).toNat + 16 * (w_n315 x).toNat)) + (16 * (w_n324 x).toNat + 16 * (w_n327 x).toNat + 16 * (w_n329 x).toNat + 16 * (w_n334 x).toNat + 16 * (w_n342 x).toNat + 16 * (w_n345 x).toNat)) + (32 * (w_n81 x).toNat + 32 * (w_n162 x).toNat + 32 * (w_n167 x).toNat + 32 * (w_n249 x).toNat + 32 * (w_n330 x).toNat + 32 * (w_n335 x).toNat)) = (I_t127 x) + (2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 2 * (w_n163 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 2 * (w_n331 x).toNat + 4 * (w_n73 x).toNat + 4 * (w_n76 x).toNat + 4 * (w_n154 x).toNat + 4 * (w_n157 x).toNat + 4 * (w_n164 x).toNat + 4 * (w_n241 x).toNat + 4 * (w_n244 x).toNat + 4 * (w_n322 x).toNat + 4 * (w_n325 x).toNat + 4 * (w_n332 x).toNat + 4 * (w_n338 x).toNat + 4 * (w_n340 x).toNat + 8 * (w_n77 x).toNat + 8 * (w_n79 x).toNat + 8 * (w_n158 x).toNat + 8 * (w_n160 x).toNat + 8 * (w_n165 x).toNat + 8 * (w_n245 x).toNat + 8 * (w_n247 x).toNat + 8 * (w_n326 x).toNat + 8 * (w_n328 x).toNat + 8 * (w_n333 x).toNat + 8 * (w_n339 x).toNat + 8 * (w_n341 x).toNat + 16 * (w_n147 x).toNat + 16 * (w_n156 x).toNat + 16 * (w_n159 x).toNat + 16 * (w_n161 x).toNat + 16 * (w_n166 x).toNat + 16 * (w_n315 x).toNat + 16 * (w_n324 x).toNat + 16 * (w_n327 x).toNat + 16 * (w_n329 x).toNat + 16 * (w_n334 x).toNat + 16 * (w_n342 x).toNat + 16 * (w_n345 x).toNat + 32 * (w_n81 x).toNat + 32 * (w_n162 x).toNat + 32 * (w_n167 x).toNat + 32 * (w_n249 x).toNat + 32 * (w_n330 x).toNat + 32 * (w_n335 x).toNat) := by unfold I_t127; ac_rfl
  have e2 : (((((((((((w_n67 x).toNat + 4 * (w_n73 x).toNat + 4 * (w_n76 x).toNat + 8 * (w_n77 x).toNat + 8 * (w_n79 x).toNat + 32 * (w_n81 x).toNat + 16 * (w_n147 x).toNat + (w_n148 x).toNat + 2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 4 * (w_n154 x).toNat + 16 * (w_n156 x).toNat + 4 * (w_n157 x).toNat + 8 * (w_n158 x).toNat + 16 * (w_n159 x).toNat + 8 * (w_n160 x).toNat + 16 * (w_n161 x).toNat + 32 * (w_n162 x).toNat + 2 * (w_n163 x).toNat + 4 * (w_n164 x).toNat + 8 * (w_n165 x).toNat + 16 * (w_n166 x).toNat + 32 * (w_n167 x).toNat + 64 * (w_n168 x).toNat) + ((w_n235 x).toNat + 4 * (w_n241 x).toNat + 4 * (w_n244 x).toNat + 8 * (w_n245 x).toNat + 8 * (w_n247 x).toNat + 32 * (w_n249 x).toNat + 16 * (w_n315 x).toNat + (w_n316 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 4 * (w_n322 x).toNat + 16 * (w_n324 x).toNat + 4 * (w_n325 x).toNat + 8 * (w_n326 x).toNat + 16 * (w_n327 x).toNat + 8 * (w_n328 x).toNat + 16 * (w_n329 x).toNat + 32 * (w_n330 x).toNat + 2 * (w_n331 x).toNat + 4 * (w_n332 x).toNat + 8 * (w_n333 x).toNat + 16 * (w_n334 x).toNat + 32 * (w_n335 x).toNat + 64 * (w_n336 x).toNat)) + (2 * (w_n337 x).toNat + 4 * (w_n338 x).toNat + 8 * (w_n339 x).toNat)) + (4 * (w_n340 x).toNat + 8 * (w_n341 x).toNat + 16 * (w_n342 x).toNat)) + (4 * (w_n343 x).toNat + 8 * (w_n344 x).toNat + 16 * (w_n345 x).toNat)) + (8 * (w_n346 x).toNat + 16 * (w_n347 x).toNat + 32 * (w_n348 x).toNat)) + (8 * (w_n349 x).toNat + 16 * (w_n350 x).toNat + 32 * (w_n351 x).toNat)) + (16 * (w_n352 x).toNat + 32 * (w_n353 x).toNat + 64 * (w_n354 x).toNat)) + (16 * (w_n355 x).toNat + 32 * (w_n356 x).toNat + 64 * (w_n357 x).toNat)) + (32 * (w_n358 x).toNat + 64 * (w_n359 x).toNat + 128 * (w_n360 x).toNat)) = ((w_n67 x).toNat + (w_n148 x).toNat + 64 * (w_n168 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + 64 * (w_n336 x).toNat + 2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 8 * (w_n344 x).toNat + 8 * (w_n346 x).toNat + 16 * (w_n347 x).toNat + 32 * (w_n348 x).toNat + 8 * (w_n349 x).toNat + 16 * (w_n350 x).toNat + 32 * (w_n351 x).toNat + 16 * (w_n352 x).toNat + 32 * (w_n353 x).toNat + 64 * (w_n354 x).toNat + 16 * (w_n355 x).toNat + 32 * (w_n356 x).toNat + 64 * (w_n357 x).toNat + 32 * (w_n358 x).toNat + 64 * (w_n359 x).toNat + 128 * (w_n360 x).toNat) + (2 * (w_n149 x).toNat + 2 * (w_n151 x).toNat + 2 * (w_n163 x).toNat + 2 * (w_n317 x).toNat + 2 * (w_n319 x).toNat + 2 * (w_n331 x).toNat + 4 * (w_n73 x).toNat + 4 * (w_n76 x).toNat + 4 * (w_n154 x).toNat + 4 * (w_n157 x).toNat + 4 * (w_n164 x).toNat + 4 * (w_n241 x).toNat + 4 * (w_n244 x).toNat + 4 * (w_n322 x).toNat + 4 * (w_n325 x).toNat + 4 * (w_n332 x).toNat + 4 * (w_n338 x).toNat + 4 * (w_n340 x).toNat + 8 * (w_n77 x).toNat + 8 * (w_n79 x).toNat + 8 * (w_n158 x).toNat + 8 * (w_n160 x).toNat + 8 * (w_n165 x).toNat + 8 * (w_n245 x).toNat + 8 * (w_n247 x).toNat + 8 * (w_n326 x).toNat + 8 * (w_n328 x).toNat + 8 * (w_n333 x).toNat + 8 * (w_n339 x).toNat + 8 * (w_n341 x).toNat + 16 * (w_n147 x).toNat + 16 * (w_n156 x).toNat + 16 * (w_n159 x).toNat + 16 * (w_n161 x).toNat + 16 * (w_n166 x).toNat + 16 * (w_n315 x).toNat + 16 * (w_n324 x).toNat + 16 * (w_n327 x).toNat + 16 * (w_n329 x).toNat + 16 * (w_n334 x).toNat + 16 * (w_n342 x).toNat + 16 * (w_n345 x).toNat + 32 * (w_n81 x).toNat + 32 * (w_n162 x).toNat + 32 * (w_n167 x).toNat + 32 * (w_n249 x).toNat + 32 * (w_n330 x).toNat + 32 * (w_n335 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s127 (x : Nat → Bool) : I_t127 x = pc x 463 384 := by
  have hl := s63 x
  have hr := s126 x
  have : pc x 463 384 = pc x 463 192 + pc x 655 192 := pc_add x 463 192 192
  unfold I_t127
  omega
def I_b128 (x : Nat → Bool) : Nat := 0 + (x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat
theorem b128 (x : Nat → Bool) : I_b128 x = (x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat := by
  unfold I_b128
  omega
def I_t128 (x : Nat → Bool) : Nat := I_b128 x
theorem t128 (x : Nat → Bool) : I_t128 x = (w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat := by
  have hs : ((I_b128 x) + ((x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat)) = (((x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat) + ((w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat)) := (add_eq (b128 x) (e120 x))
  have e1 : ((I_b128 x) + ((x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat)) = (I_t128 x) + ((x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat) := by unfold I_t128; ac_rfl
  have e2 : (((x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat) + ((w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat)) = ((w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat) + ((x 871).toNat + (x 872).toNat + (x 873).toNat + (x 874).toNat + (x 875).toNat + (x 876).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s128 (x : Nat → Bool) : I_t128 x = pc x 871 6 := rfl
def I_b129 (x : Nat → Bool) : Nat := 0 + (x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat
theorem b129 (x : Nat → Bool) : I_b129 x = (x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat := by
  unfold I_b129
  omega
def I_t129 (x : Nat → Bool) : Nat := I_b129 x
theorem t129 (x : Nat → Bool) : I_t129 x = (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat := by
  have hs : ((I_b129 x) + ((x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat)) = (((x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat) + ((w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat)) := (add_eq (b129 x) (e121 x))
  have e1 : ((I_b129 x) + ((x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat)) = (I_t129 x) + ((x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat) := by unfold I_t129; ac_rfl
  have e2 : (((x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat) + ((w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat)) = ((w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat) + ((x 877).toNat + (x 878).toNat + (x 879).toNat + (x 880).toNat + (x 881).toNat + (x 882).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s129 (x : Nat → Bool) : I_t129 x = pc x 877 6 := rfl
def I_t130 (x : Nat → Bool) : Nat := I_t128 x + I_t129 x
theorem t130 (x : Nat → Bool) : I_t130 x = (w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat + (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat := by
  have hs : ((I_t128 x) + (I_t129 x)) = (((w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat) + ((w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat)) := (add_eq (t128 x) (t129 x))
  have e1 : ((I_t128 x) + (I_t129 x)) = I_t130 x := by unfold I_t130; ac_rfl
  have e2 : (((w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat) + ((w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat)) = (w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat + (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s130 (x : Nat → Bool) : I_t130 x = pc x 871 12 := by
  have hl := s128 x
  have hr := s129 x
  have : pc x 871 12 = pc x 871 6 + pc x 877 6 := pc_add x 871 6 6
  unfold I_t130
  omega
def I_b131 (x : Nat → Bool) : Nat := 0 + (x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat
theorem b131 (x : Nat → Bool) : I_b131 x = (x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat := by
  unfold I_b131
  omega
def I_t131 (x : Nat → Bool) : Nat := I_b131 x
theorem t131 (x : Nat → Bool) : I_t131 x = (w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat := by
  have hs : ((I_b131 x) + ((x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat)) = (((x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat) + ((w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat)) := (add_eq (b131 x) (e122 x))
  have e1 : ((I_b131 x) + ((x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat)) = (I_t131 x) + ((x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat) := by unfold I_t131; ac_rfl
  have e2 : (((x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat) + ((w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat)) = ((w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat) + ((x 883).toNat + (x 884).toNat + (x 885).toNat + (x 886).toNat + (x 887).toNat + (x 888).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s131 (x : Nat → Bool) : I_t131 x = pc x 883 6 := rfl
def I_b132 (x : Nat → Bool) : Nat := 0 + (x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat
theorem b132 (x : Nat → Bool) : I_b132 x = (x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat := by
  unfold I_b132
  omega
def I_t132 (x : Nat → Bool) : Nat := I_b132 x
theorem t132 (x : Nat → Bool) : I_t132 x = (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat := by
  have hs : ((I_b132 x) + ((x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat)) = (((x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat) + ((w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat)) := (add_eq (b132 x) (e123 x))
  have e1 : ((I_b132 x) + ((x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat)) = (I_t132 x) + ((x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat) := by unfold I_t132; ac_rfl
  have e2 : (((x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat) + ((w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat)) = ((w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat) + ((x 889).toNat + (x 890).toNat + (x 891).toNat + (x 892).toNat + (x 893).toNat + (x 894).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s132 (x : Nat → Bool) : I_t132 x = pc x 889 6 := rfl
def I_t133 (x : Nat → Bool) : Nat := I_t131 x + I_t132 x
theorem t133 (x : Nat → Bool) : I_t133 x = (w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat + (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat := by
  have hs : ((I_t131 x) + (I_t132 x)) = (((w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat) + ((w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat)) := (add_eq (t131 x) (t132 x))
  have e1 : ((I_t131 x) + (I_t132 x)) = I_t133 x := by unfold I_t133; ac_rfl
  have e2 : (((w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat) + ((w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat)) = (w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat + (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s133 (x : Nat → Bool) : I_t133 x = pc x 883 12 := by
  have hl := s131 x
  have hr := s132 x
  have : pc x 883 12 = pc x 883 6 + pc x 889 6 := pc_add x 883 6 6
  unfold I_t133
  omega
def I_t134 (x : Nat → Bool) : Nat := I_t130 x + I_t133 x
theorem t134 (x : Nat → Bool) : I_t134 x = (w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat + (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat + (w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat + (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat := by
  have hs : ((I_t130 x) + (I_t133 x)) = (((w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat + (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat) + ((w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat + (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat)) := (add_eq (t130 x) (t133 x))
  have e1 : ((I_t130 x) + (I_t133 x)) = I_t134 x := by unfold I_t134; ac_rfl
  have e2 : (((w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat + (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat) + ((w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat + (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat)) = (w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat + (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat + (w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat + (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s134 (x : Nat → Bool) : I_t134 x = pc x 871 24 := by
  have hl := s130 x
  have hr := s133 x
  have : pc x 871 24 = pc x 871 12 + pc x 883 12 := pc_add x 871 12 12
  unfold I_t134
  omega
def I_b135 (x : Nat → Bool) : Nat := 0 + (x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat
theorem b135 (x : Nat → Bool) : I_b135 x = (x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat := by
  unfold I_b135
  omega
def I_t135 (x : Nat → Bool) : Nat := I_b135 x
theorem t135 (x : Nat → Bool) : I_t135 x = (w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat := by
  have hs : ((I_b135 x) + ((x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat)) = (((x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat) + ((w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat)) := (add_eq (b135 x) (e124 x))
  have e1 : ((I_b135 x) + ((x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat)) = (I_t135 x) + ((x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat) := by unfold I_t135; ac_rfl
  have e2 : (((x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat) + ((w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat)) = ((w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat) + ((x 859).toNat + (x 860).toNat + (x 861).toNat + (x 862).toNat + (x 863).toNat + (x 864).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s135 (x : Nat → Bool) : I_t135 x = pc x 859 6 := rfl
def I_b136 (x : Nat → Bool) : Nat := 0 + (x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat
theorem b136 (x : Nat → Bool) : I_b136 x = (x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat := by
  unfold I_b136
  omega
def I_t136 (x : Nat → Bool) : Nat := I_b136 x
theorem t136 (x : Nat → Bool) : I_t136 x = (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat := by
  have hs : ((I_b136 x) + ((x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat)) = (((x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat) + ((w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat)) := (add_eq (b136 x) (e125 x))
  have e1 : ((I_b136 x) + ((x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat)) = (I_t136 x) + ((x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat) := by unfold I_t136; ac_rfl
  have e2 : (((x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat) + ((w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat)) = ((w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat) + ((x 865).toNat + (x 866).toNat + (x 867).toNat + (x 868).toNat + (x 869).toNat + (x 870).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s136 (x : Nat → Bool) : I_t136 x = pc x 865 6 := rfl
def I_t137 (x : Nat → Bool) : Nat := I_t135 x + I_t136 x
theorem t137 (x : Nat → Bool) : I_t137 x = (w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat + (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat := by
  have hs : ((I_t135 x) + (I_t136 x)) = (((w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat) + ((w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat)) := (add_eq (t135 x) (t136 x))
  have e1 : ((I_t135 x) + (I_t136 x)) = I_t137 x := by unfold I_t137; ac_rfl
  have e2 : (((w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat) + ((w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat)) = (w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat + (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s137 (x : Nat → Bool) : I_t137 x = pc x 859 12 := by
  have hl := s135 x
  have hr := s136 x
  have : pc x 859 12 = pc x 859 6 + pc x 865 6 := pc_add x 859 6 6
  unfold I_t137
  omega
def I_b138 (x : Nat → Bool) : Nat := 0 + (x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat
theorem b138 (x : Nat → Bool) : I_b138 x = (x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat := by
  unfold I_b138
  omega
def I_t138 (x : Nat → Bool) : Nat := I_b138 x
theorem t138 (x : Nat → Bool) : I_t138 x = (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat := by
  have hs : ((I_b138 x) + ((x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat)) = (((x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat) + ((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat)) := (add_eq (b138 x) (e126 x))
  have e1 : ((I_b138 x) + ((x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat)) = (I_t138 x) + ((x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat) := by unfold I_t138; ac_rfl
  have e2 : (((x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat) + ((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat)) = ((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat) + ((x 847).toNat + (x 848).toNat + (x 849).toNat + (x 850).toNat + (x 851).toNat + (x 852).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s138 (x : Nat → Bool) : I_t138 x = pc x 847 6 := rfl
def I_b139 (x : Nat → Bool) : Nat := 0 + (x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat
theorem b139 (x : Nat → Bool) : I_b139 x = (x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat := by
  unfold I_b139
  omega
def I_t139 (x : Nat → Bool) : Nat := I_b139 x
theorem t139 (x : Nat → Bool) : I_t139 x = (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat := by
  have hs : ((I_b139 x) + ((x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat)) = (((x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat) + ((w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat)) := (add_eq (b139 x) (e127 x))
  have e1 : ((I_b139 x) + ((x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat)) = (I_t139 x) + ((x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat) := by unfold I_t139; ac_rfl
  have e2 : (((x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat) + ((w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat)) = ((w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat) + ((x 853).toNat + (x 854).toNat + (x 855).toNat + (x 856).toNat + (x 857).toNat + (x 858).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s139 (x : Nat → Bool) : I_t139 x = pc x 853 6 := rfl
def I_t140 (x : Nat → Bool) : Nat := I_t138 x + I_t139 x
theorem t140 (x : Nat → Bool) : I_t140 x = (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat := by
  have hs : ((I_t138 x) + (I_t139 x)) = (((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat) + ((w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat)) := (add_eq (t138 x) (t139 x))
  have e1 : ((I_t138 x) + (I_t139 x)) = I_t140 x := by unfold I_t140; ac_rfl
  have e2 : (((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat) + ((w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat)) = (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s140 (x : Nat → Bool) : I_t140 x = pc x 847 12 := by
  have hl := s138 x
  have hr := s139 x
  have : pc x 847 12 = pc x 847 6 + pc x 853 6 := pc_add x 847 6 6
  unfold I_t140
  omega
def I_t141 (x : Nat → Bool) : Nat := I_t137 x + I_t140 x
theorem t141 (x : Nat → Bool) : I_t141 x = (w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat + (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat + (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat := by
  have hs : ((I_t137 x) + (I_t140 x)) = (((w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat + (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat) + ((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat)) := (add_eq (t137 x) (t140 x))
  have e1 : ((I_t137 x) + (I_t140 x)) = I_t141 x := by unfold I_t141; ac_rfl
  have e2 : (((w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat + (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat) + ((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat)) = (w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat + (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat + (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s141 (x : Nat → Bool) : I_t141 x = pc x 847 24 := by
  have hl := s137 x
  have hr := s140 x
  have : pc x 847 24 = pc x 847 12 + pc x 859 12 := pc_add x 847 12 12
  unfold I_t141
  omega
def I_t142 (x : Nat → Bool) : Nat := I_t134 x + I_t141 x
theorem t142 (x : Nat → Bool) : I_t142 x = (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat + (w_n385 x).toNat + 2 * (w_n386 x).toNat + 4 * (w_n387 x).toNat + 2 * (w_n388 x).toNat + 4 * (w_n389 x).toNat + 8 * (w_n390 x).toNat + 4 * (w_n391 x).toNat + 8 * (w_n392 x).toNat + 16 * (w_n393 x).toNat := by
  have hs : (((((I_t134 x) + (I_t141 x)) + ((w_n361 x).toNat + (w_n364 x).toNat + (w_n367 x).toNat + (w_n370 x).toNat + (w_n373 x).toNat + (w_n376 x).toNat)) + (2 * (w_n362 x).toNat + 2 * (w_n365 x).toNat + 2 * (w_n368 x).toNat + 2 * (w_n371 x).toNat + 2 * (w_n374 x).toNat + 2 * (w_n377 x).toNat)) + (4 * (w_n363 x).toNat + 4 * (w_n366 x).toNat + 4 * (w_n369 x).toNat + 4 * (w_n372 x).toNat + 4 * (w_n375 x).toNat + 4 * (w_n378 x).toNat)) = ((((((w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat + (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat + (w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat + (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat) + ((w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat + (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat + (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat)) + ((w_n385 x).toNat + 2 * (w_n386 x).toNat + 4 * (w_n387 x).toNat)) + (2 * (w_n388 x).toNat + 4 * (w_n389 x).toNat + 8 * (w_n390 x).toNat)) + (4 * (w_n391 x).toNat + 8 * (w_n392 x).toNat + 16 * (w_n393 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t134 x) (t141 x)) (e128 x)) (e129 x)) (e130 x))
  have e1 : (((((I_t134 x) + (I_t141 x)) + ((w_n361 x).toNat + (w_n364 x).toNat + (w_n367 x).toNat + (w_n370 x).toNat + (w_n373 x).toNat + (w_n376 x).toNat)) + (2 * (w_n362 x).toNat + 2 * (w_n365 x).toNat + 2 * (w_n368 x).toNat + 2 * (w_n371 x).toNat + 2 * (w_n374 x).toNat + 2 * (w_n377 x).toNat)) + (4 * (w_n363 x).toNat + 4 * (w_n366 x).toNat + 4 * (w_n369 x).toNat + 4 * (w_n372 x).toNat + 4 * (w_n375 x).toNat + 4 * (w_n378 x).toNat)) = (I_t142 x) + ((w_n361 x).toNat + (w_n364 x).toNat + (w_n367 x).toNat + (w_n370 x).toNat + (w_n373 x).toNat + (w_n376 x).toNat + 2 * (w_n362 x).toNat + 2 * (w_n365 x).toNat + 2 * (w_n368 x).toNat + 2 * (w_n371 x).toNat + 2 * (w_n374 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n363 x).toNat + 4 * (w_n366 x).toNat + 4 * (w_n369 x).toNat + 4 * (w_n372 x).toNat + 4 * (w_n375 x).toNat + 4 * (w_n378 x).toNat) := by unfold I_t142; ac_rfl
  have e2 : ((((((w_n361 x).toNat + 2 * (w_n362 x).toNat + 4 * (w_n363 x).toNat + (w_n364 x).toNat + 2 * (w_n365 x).toNat + 4 * (w_n366 x).toNat + (w_n367 x).toNat + 2 * (w_n368 x).toNat + 4 * (w_n369 x).toNat + (w_n370 x).toNat + 2 * (w_n371 x).toNat + 4 * (w_n372 x).toNat) + ((w_n373 x).toNat + 2 * (w_n374 x).toNat + 4 * (w_n375 x).toNat + (w_n376 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n378 x).toNat + (w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat)) + ((w_n385 x).toNat + 2 * (w_n386 x).toNat + 4 * (w_n387 x).toNat)) + (2 * (w_n388 x).toNat + 4 * (w_n389 x).toNat + 8 * (w_n390 x).toNat)) + (4 * (w_n391 x).toNat + 8 * (w_n392 x).toNat + 16 * (w_n393 x).toNat)) = ((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat + (w_n385 x).toNat + 2 * (w_n386 x).toNat + 4 * (w_n387 x).toNat + 2 * (w_n388 x).toNat + 4 * (w_n389 x).toNat + 8 * (w_n390 x).toNat + 4 * (w_n391 x).toNat + 8 * (w_n392 x).toNat + 16 * (w_n393 x).toNat) + ((w_n361 x).toNat + (w_n364 x).toNat + (w_n367 x).toNat + (w_n370 x).toNat + (w_n373 x).toNat + (w_n376 x).toNat + 2 * (w_n362 x).toNat + 2 * (w_n365 x).toNat + 2 * (w_n368 x).toNat + 2 * (w_n371 x).toNat + 2 * (w_n374 x).toNat + 2 * (w_n377 x).toNat + 4 * (w_n363 x).toNat + 4 * (w_n366 x).toNat + 4 * (w_n369 x).toNat + 4 * (w_n372 x).toNat + 4 * (w_n375 x).toNat + 4 * (w_n378 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s142 (x : Nat → Bool) : I_t142 x = pc x 847 48 := by
  have hl := s134 x
  have hr := s141 x
  have : pc x 847 48 = pc x 847 24 + pc x 871 24 := pc_add x 847 24 24
  unfold I_t142
  omega
def I_b143 (x : Nat → Bool) : Nat := 0 + (x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat
theorem b143 (x : Nat → Bool) : I_b143 x = (x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat := by
  unfold I_b143
  omega
def I_t143 (x : Nat → Bool) : Nat := I_b143 x
theorem t143 (x : Nat → Bool) : I_t143 x = (w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat := by
  have hs : ((I_b143 x) + ((x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat)) = (((x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat) + ((w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat)) := (add_eq (b143 x) (e131 x))
  have e1 : ((I_b143 x) + ((x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat)) = (I_t143 x) + ((x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat) := by unfold I_t143; ac_rfl
  have e2 : (((x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat) + ((w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat)) = ((w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat) + ((x 937).toNat + (x 938).toNat + (x 939).toNat + (x 940).toNat + (x 941).toNat + (x 942).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s143 (x : Nat → Bool) : I_t143 x = pc x 937 6 := rfl
def I_b144 (x : Nat → Bool) : Nat := 0 + (x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat
theorem b144 (x : Nat → Bool) : I_b144 x = (x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat := by
  unfold I_b144
  omega
def I_t144 (x : Nat → Bool) : Nat := I_b144 x
theorem t144 (x : Nat → Bool) : I_t144 x = (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat := by
  have hs : ((I_b144 x) + ((x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat)) = (((x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat) + ((w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat)) := (add_eq (b144 x) (e132 x))
  have e1 : ((I_b144 x) + ((x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat)) = (I_t144 x) + ((x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat) := by unfold I_t144; ac_rfl
  have e2 : (((x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat) + ((w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat)) = ((w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat) + ((x 931).toNat + (x 932).toNat + (x 933).toNat + (x 934).toNat + (x 935).toNat + (x 936).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s144 (x : Nat → Bool) : I_t144 x = pc x 931 6 := rfl
def I_t145 (x : Nat → Bool) : Nat := I_t143 x + I_t144 x
theorem t145 (x : Nat → Bool) : I_t145 x = (w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat + (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat := by
  have hs : ((I_t143 x) + (I_t144 x)) = (((w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat) + ((w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat)) := (add_eq (t143 x) (t144 x))
  have e1 : ((I_t143 x) + (I_t144 x)) = I_t145 x := by unfold I_t145; ac_rfl
  have e2 : (((w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat) + ((w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat)) = (w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat + (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s145 (x : Nat → Bool) : I_t145 x = pc x 931 12 := by
  have hl := s143 x
  have hr := s144 x
  have : pc x 931 12 = pc x 931 6 + pc x 937 6 := pc_add x 931 6 6
  unfold I_t145
  omega
def I_b146 (x : Nat → Bool) : Nat := 0 + (x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat
theorem b146 (x : Nat → Bool) : I_b146 x = (x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat := by
  unfold I_b146
  omega
def I_t146 (x : Nat → Bool) : Nat := I_b146 x
theorem t146 (x : Nat → Bool) : I_t146 x = (w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat := by
  have hs : ((I_b146 x) + ((x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat)) = (((x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat) + ((w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat)) := (add_eq (b146 x) (e133 x))
  have e1 : ((I_b146 x) + ((x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat)) = (I_t146 x) + ((x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat) := by unfold I_t146; ac_rfl
  have e2 : (((x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat) + ((w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat)) = ((w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat) + ((x 925).toNat + (x 926).toNat + (x 927).toNat + (x 928).toNat + (x 929).toNat + (x 930).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s146 (x : Nat → Bool) : I_t146 x = pc x 925 6 := rfl
def I_b147 (x : Nat → Bool) : Nat := 0 + (x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat
theorem b147 (x : Nat → Bool) : I_b147 x = (x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat := by
  unfold I_b147
  omega
def I_t147 (x : Nat → Bool) : Nat := I_b147 x
theorem t147 (x : Nat → Bool) : I_t147 x = (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat := by
  have hs : ((I_b147 x) + ((x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat)) = (((x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat) + ((w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat)) := (add_eq (b147 x) (e134 x))
  have e1 : ((I_b147 x) + ((x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat)) = (I_t147 x) + ((x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat) := by unfold I_t147; ac_rfl
  have e2 : (((x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat) + ((w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat)) = ((w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat) + ((x 919).toNat + (x 920).toNat + (x 921).toNat + (x 922).toNat + (x 923).toNat + (x 924).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s147 (x : Nat → Bool) : I_t147 x = pc x 919 6 := rfl
def I_t148 (x : Nat → Bool) : Nat := I_t146 x + I_t147 x
theorem t148 (x : Nat → Bool) : I_t148 x = (w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat + (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat := by
  have hs : ((I_t146 x) + (I_t147 x)) = (((w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat) + ((w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat)) := (add_eq (t146 x) (t147 x))
  have e1 : ((I_t146 x) + (I_t147 x)) = I_t148 x := by unfold I_t148; ac_rfl
  have e2 : (((w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat) + ((w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat)) = (w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat + (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s148 (x : Nat → Bool) : I_t148 x = pc x 919 12 := by
  have hl := s146 x
  have hr := s147 x
  have : pc x 919 12 = pc x 919 6 + pc x 925 6 := pc_add x 919 6 6
  unfold I_t148
  omega
def I_t149 (x : Nat → Bool) : Nat := I_t145 x + I_t148 x
theorem t149 (x : Nat → Bool) : I_t149 x = (w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat + (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat + (w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat + (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat := by
  have hs : ((I_t145 x) + (I_t148 x)) = (((w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat + (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat) + ((w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat + (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat)) := (add_eq (t145 x) (t148 x))
  have e1 : ((I_t145 x) + (I_t148 x)) = I_t149 x := by unfold I_t149; ac_rfl
  have e2 : (((w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat + (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat) + ((w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat + (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat)) = (w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat + (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat + (w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat + (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s149 (x : Nat → Bool) : I_t149 x = pc x 919 24 := by
  have hl := s145 x
  have hr := s148 x
  have : pc x 919 24 = pc x 919 12 + pc x 931 12 := pc_add x 919 12 12
  unfold I_t149
  omega
def I_b150 (x : Nat → Bool) : Nat := 0 + (x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat
theorem b150 (x : Nat → Bool) : I_b150 x = (x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat := by
  unfold I_b150
  omega
def I_t150 (x : Nat → Bool) : Nat := I_b150 x
theorem t150 (x : Nat → Bool) : I_t150 x = (w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat := by
  have hs : ((I_b150 x) + ((x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat)) = (((x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat) + ((w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat)) := (add_eq (b150 x) (e135 x))
  have e1 : ((I_b150 x) + ((x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat)) = (I_t150 x) + ((x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat) := by unfold I_t150; ac_rfl
  have e2 : (((x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat) + ((w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat)) = ((w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat) + ((x 901).toNat + (x 902).toNat + (x 903).toNat + (x 904).toNat + (x 905).toNat + (x 906).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s150 (x : Nat → Bool) : I_t150 x = pc x 901 6 := rfl
def I_b151 (x : Nat → Bool) : Nat := 0 + (x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat
theorem b151 (x : Nat → Bool) : I_b151 x = (x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat := by
  unfold I_b151
  omega
def I_t151 (x : Nat → Bool) : Nat := I_b151 x
theorem t151 (x : Nat → Bool) : I_t151 x = (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat := by
  have hs : ((I_b151 x) + ((x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat)) = (((x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat) + ((w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat)) := (add_eq (b151 x) (e136 x))
  have e1 : ((I_b151 x) + ((x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat)) = (I_t151 x) + ((x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat) := by unfold I_t151; ac_rfl
  have e2 : (((x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat) + ((w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat)) = ((w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat) + ((x 895).toNat + (x 896).toNat + (x 897).toNat + (x 898).toNat + (x 899).toNat + (x 900).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s151 (x : Nat → Bool) : I_t151 x = pc x 895 6 := rfl
def I_t152 (x : Nat → Bool) : Nat := I_t150 x + I_t151 x
theorem t152 (x : Nat → Bool) : I_t152 x = (w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat + (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat := by
  have hs : ((I_t150 x) + (I_t151 x)) = (((w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat) + ((w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat)) := (add_eq (t150 x) (t151 x))
  have e1 : ((I_t150 x) + (I_t151 x)) = I_t152 x := by unfold I_t152; ac_rfl
  have e2 : (((w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat) + ((w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat)) = (w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat + (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s152 (x : Nat → Bool) : I_t152 x = pc x 895 12 := by
  have hl := s150 x
  have hr := s151 x
  have : pc x 895 12 = pc x 895 6 + pc x 901 6 := pc_add x 895 6 6
  unfold I_t152
  omega
def I_b153 (x : Nat → Bool) : Nat := 0 + (x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat
theorem b153 (x : Nat → Bool) : I_b153 x = (x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat := by
  unfold I_b153
  omega
def I_t153 (x : Nat → Bool) : Nat := I_b153 x
theorem t153 (x : Nat → Bool) : I_t153 x = (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat := by
  have hs : ((I_b153 x) + ((x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat)) = (((x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat) + ((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat)) := (add_eq (b153 x) (e137 x))
  have e1 : ((I_b153 x) + ((x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat)) = (I_t153 x) + ((x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat) := by unfold I_t153; ac_rfl
  have e2 : (((x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat) + ((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat)) = ((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat) + ((x 913).toNat + (x 914).toNat + (x 915).toNat + (x 916).toNat + (x 917).toNat + (x 918).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s153 (x : Nat → Bool) : I_t153 x = pc x 913 6 := rfl
def I_b154 (x : Nat → Bool) : Nat := 0 + (x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat
theorem b154 (x : Nat → Bool) : I_b154 x = (x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat := by
  unfold I_b154
  omega
def I_t154 (x : Nat → Bool) : Nat := I_b154 x
theorem t154 (x : Nat → Bool) : I_t154 x = (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat := by
  have hs : ((I_b154 x) + ((x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat)) = (((x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat) + ((w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat)) := (add_eq (b154 x) (e138 x))
  have e1 : ((I_b154 x) + ((x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat)) = (I_t154 x) + ((x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat) := by unfold I_t154; ac_rfl
  have e2 : (((x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat) + ((w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat)) = ((w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat) + ((x 907).toNat + (x 908).toNat + (x 909).toNat + (x 910).toNat + (x 911).toNat + (x 912).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s154 (x : Nat → Bool) : I_t154 x = pc x 907 6 := rfl
def I_t155 (x : Nat → Bool) : Nat := I_t153 x + I_t154 x
theorem t155 (x : Nat → Bool) : I_t155 x = (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat := by
  have hs : ((I_t153 x) + (I_t154 x)) = (((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat) + ((w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat)) := (add_eq (t153 x) (t154 x))
  have e1 : ((I_t153 x) + (I_t154 x)) = I_t155 x := by unfold I_t155; ac_rfl
  have e2 : (((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat) + ((w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat)) = (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s155 (x : Nat → Bool) : I_t155 x = pc x 907 12 := by
  have hl := s153 x
  have hr := s154 x
  have : pc x 907 12 = pc x 907 6 + pc x 913 6 := pc_add x 907 6 6
  unfold I_t155
  omega
def I_t156 (x : Nat → Bool) : Nat := I_t152 x + I_t155 x
theorem t156 (x : Nat → Bool) : I_t156 x = (w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat + (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat + (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat := by
  have hs : ((I_t152 x) + (I_t155 x)) = (((w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat + (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat) + ((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat)) := (add_eq (t152 x) (t155 x))
  have e1 : ((I_t152 x) + (I_t155 x)) = I_t156 x := by unfold I_t156; ac_rfl
  have e2 : (((w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat + (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat) + ((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat)) = (w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat + (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat + (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s156 (x : Nat → Bool) : I_t156 x = pc x 895 24 := by
  have hl := s152 x
  have hr := s155 x
  have : pc x 895 24 = pc x 895 12 + pc x 907 12 := pc_add x 895 12 12
  unfold I_t156
  omega
def I_t157 (x : Nat → Bool) : Nat := I_t149 x + I_t156 x
theorem t157 (x : Nat → Bool) : I_t157 x = (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat + (w_n418 x).toNat + 2 * (w_n419 x).toNat + 4 * (w_n420 x).toNat + 2 * (w_n421 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n423 x).toNat + 4 * (w_n424 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n426 x).toNat := by
  have hs : (((((I_t149 x) + (I_t156 x)) + ((w_n394 x).toNat + (w_n397 x).toNat + (w_n400 x).toNat + (w_n403 x).toNat + (w_n406 x).toNat + (w_n409 x).toNat)) + (2 * (w_n395 x).toNat + 2 * (w_n398 x).toNat + 2 * (w_n401 x).toNat + 2 * (w_n404 x).toNat + 2 * (w_n407 x).toNat + 2 * (w_n410 x).toNat)) + (4 * (w_n396 x).toNat + 4 * (w_n399 x).toNat + 4 * (w_n402 x).toNat + 4 * (w_n405 x).toNat + 4 * (w_n408 x).toNat + 4 * (w_n411 x).toNat)) = ((((((w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat + (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat + (w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat + (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat) + ((w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat + (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat + (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat)) + ((w_n418 x).toNat + 2 * (w_n419 x).toNat + 4 * (w_n420 x).toNat)) + (2 * (w_n421 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n423 x).toNat)) + (4 * (w_n424 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n426 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t149 x) (t156 x)) (e139 x)) (e140 x)) (e141 x))
  have e1 : (((((I_t149 x) + (I_t156 x)) + ((w_n394 x).toNat + (w_n397 x).toNat + (w_n400 x).toNat + (w_n403 x).toNat + (w_n406 x).toNat + (w_n409 x).toNat)) + (2 * (w_n395 x).toNat + 2 * (w_n398 x).toNat + 2 * (w_n401 x).toNat + 2 * (w_n404 x).toNat + 2 * (w_n407 x).toNat + 2 * (w_n410 x).toNat)) + (4 * (w_n396 x).toNat + 4 * (w_n399 x).toNat + 4 * (w_n402 x).toNat + 4 * (w_n405 x).toNat + 4 * (w_n408 x).toNat + 4 * (w_n411 x).toNat)) = (I_t157 x) + ((w_n394 x).toNat + (w_n397 x).toNat + (w_n400 x).toNat + (w_n403 x).toNat + (w_n406 x).toNat + (w_n409 x).toNat + 2 * (w_n395 x).toNat + 2 * (w_n398 x).toNat + 2 * (w_n401 x).toNat + 2 * (w_n404 x).toNat + 2 * (w_n407 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n396 x).toNat + 4 * (w_n399 x).toNat + 4 * (w_n402 x).toNat + 4 * (w_n405 x).toNat + 4 * (w_n408 x).toNat + 4 * (w_n411 x).toNat) := by unfold I_t157; ac_rfl
  have e2 : ((((((w_n394 x).toNat + 2 * (w_n395 x).toNat + 4 * (w_n396 x).toNat + (w_n397 x).toNat + 2 * (w_n398 x).toNat + 4 * (w_n399 x).toNat + (w_n400 x).toNat + 2 * (w_n401 x).toNat + 4 * (w_n402 x).toNat + (w_n403 x).toNat + 2 * (w_n404 x).toNat + 4 * (w_n405 x).toNat) + ((w_n406 x).toNat + 2 * (w_n407 x).toNat + 4 * (w_n408 x).toNat + (w_n409 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n411 x).toNat + (w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat)) + ((w_n418 x).toNat + 2 * (w_n419 x).toNat + 4 * (w_n420 x).toNat)) + (2 * (w_n421 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n423 x).toNat)) + (4 * (w_n424 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n426 x).toNat)) = ((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat + (w_n418 x).toNat + 2 * (w_n419 x).toNat + 4 * (w_n420 x).toNat + 2 * (w_n421 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n423 x).toNat + 4 * (w_n424 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n426 x).toNat) + ((w_n394 x).toNat + (w_n397 x).toNat + (w_n400 x).toNat + (w_n403 x).toNat + (w_n406 x).toNat + (w_n409 x).toNat + 2 * (w_n395 x).toNat + 2 * (w_n398 x).toNat + 2 * (w_n401 x).toNat + 2 * (w_n404 x).toNat + 2 * (w_n407 x).toNat + 2 * (w_n410 x).toNat + 4 * (w_n396 x).toNat + 4 * (w_n399 x).toNat + 4 * (w_n402 x).toNat + 4 * (w_n405 x).toNat + 4 * (w_n408 x).toNat + 4 * (w_n411 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s157 (x : Nat → Bool) : I_t157 x = pc x 895 48 := by
  have hl := s149 x
  have hr := s156 x
  have : pc x 895 48 = pc x 895 24 + pc x 919 24 := pc_add x 895 24 24
  unfold I_t157
  omega
def I_t158 (x : Nat → Bool) : Nat := I_t142 x + I_t157 x
theorem t158 (x : Nat → Bool) : I_t158 x = 16 * (w_n393 x).toNat + 2 * (w_n419 x).toNat + 2 * (w_n421 x).toNat + 16 * (w_n426 x).toNat + (w_n427 x).toNat + 2 * (w_n428 x).toNat + 2 * (w_n430 x).toNat + 4 * (w_n433 x).toNat + 16 * (w_n435 x).toNat + 4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 16 * (w_n438 x).toNat + 8 * (w_n439 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n441 x).toNat := by
  have hs : (((((((I_t142 x) + (I_t157 x)) + ((w_n379 x).toNat + (w_n382 x).toNat + (w_n385 x).toNat + (w_n412 x).toNat + (w_n415 x).toNat + (w_n418 x).toNat)) + (2 * (w_n380 x).toNat + 2 * (w_n383 x).toNat + 2 * (w_n386 x).toNat + 2 * (w_n388 x).toNat + 2 * (w_n413 x).toNat + 2 * (w_n416 x).toNat)) + (4 * (w_n381 x).toNat + 4 * (w_n384 x).toNat + 4 * (w_n387 x).toNat + 4 * (w_n389 x).toNat + 4 * (w_n391 x).toNat + 4 * (w_n414 x).toNat)) + (4 * (w_n417 x).toNat + 4 * (w_n420 x).toNat + 4 * (w_n422 x).toNat + 4 * (w_n424 x).toNat + 4 * (w_n429 x).toNat + 4 * (w_n431 x).toNat)) + (8 * (w_n390 x).toNat + 8 * (w_n392 x).toNat + 8 * (w_n423 x).toNat + 8 * (w_n425 x).toNat + 8 * (w_n432 x).toNat + 8 * (w_n434 x).toNat)) = ((((((((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat + (w_n385 x).toNat + 2 * (w_n386 x).toNat + 4 * (w_n387 x).toNat + 2 * (w_n388 x).toNat + 4 * (w_n389 x).toNat + 8 * (w_n390 x).toNat + 4 * (w_n391 x).toNat + 8 * (w_n392 x).toNat + 16 * (w_n393 x).toNat) + ((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat + (w_n418 x).toNat + 2 * (w_n419 x).toNat + 4 * (w_n420 x).toNat + 2 * (w_n421 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n423 x).toNat + 4 * (w_n424 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n426 x).toNat)) + ((w_n427 x).toNat + 2 * (w_n428 x).toNat + 4 * (w_n429 x).toNat)) + (2 * (w_n430 x).toNat + 4 * (w_n431 x).toNat + 8 * (w_n432 x).toNat)) + (4 * (w_n433 x).toNat + 8 * (w_n434 x).toNat + 16 * (w_n435 x).toNat)) + (4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 16 * (w_n438 x).toNat)) + (8 * (w_n439 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n441 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t142 x) (t157 x)) (e142 x)) (e143 x)) (e144 x)) (e145 x)) (e146 x))
  have e1 : (((((((I_t142 x) + (I_t157 x)) + ((w_n379 x).toNat + (w_n382 x).toNat + (w_n385 x).toNat + (w_n412 x).toNat + (w_n415 x).toNat + (w_n418 x).toNat)) + (2 * (w_n380 x).toNat + 2 * (w_n383 x).toNat + 2 * (w_n386 x).toNat + 2 * (w_n388 x).toNat + 2 * (w_n413 x).toNat + 2 * (w_n416 x).toNat)) + (4 * (w_n381 x).toNat + 4 * (w_n384 x).toNat + 4 * (w_n387 x).toNat + 4 * (w_n389 x).toNat + 4 * (w_n391 x).toNat + 4 * (w_n414 x).toNat)) + (4 * (w_n417 x).toNat + 4 * (w_n420 x).toNat + 4 * (w_n422 x).toNat + 4 * (w_n424 x).toNat + 4 * (w_n429 x).toNat + 4 * (w_n431 x).toNat)) + (8 * (w_n390 x).toNat + 8 * (w_n392 x).toNat + 8 * (w_n423 x).toNat + 8 * (w_n425 x).toNat + 8 * (w_n432 x).toNat + 8 * (w_n434 x).toNat)) = (I_t158 x) + ((w_n379 x).toNat + (w_n382 x).toNat + (w_n385 x).toNat + (w_n412 x).toNat + (w_n415 x).toNat + (w_n418 x).toNat + 2 * (w_n380 x).toNat + 2 * (w_n383 x).toNat + 2 * (w_n386 x).toNat + 2 * (w_n388 x).toNat + 2 * (w_n413 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n381 x).toNat + 4 * (w_n384 x).toNat + 4 * (w_n387 x).toNat + 4 * (w_n389 x).toNat + 4 * (w_n391 x).toNat + 4 * (w_n414 x).toNat + 4 * (w_n417 x).toNat + 4 * (w_n420 x).toNat + 4 * (w_n422 x).toNat + 4 * (w_n424 x).toNat + 4 * (w_n429 x).toNat + 4 * (w_n431 x).toNat + 8 * (w_n390 x).toNat + 8 * (w_n392 x).toNat + 8 * (w_n423 x).toNat + 8 * (w_n425 x).toNat + 8 * (w_n432 x).toNat + 8 * (w_n434 x).toNat) := by unfold I_t158; ac_rfl
  have e2 : ((((((((w_n379 x).toNat + 2 * (w_n380 x).toNat + 4 * (w_n381 x).toNat + (w_n382 x).toNat + 2 * (w_n383 x).toNat + 4 * (w_n384 x).toNat + (w_n385 x).toNat + 2 * (w_n386 x).toNat + 4 * (w_n387 x).toNat + 2 * (w_n388 x).toNat + 4 * (w_n389 x).toNat + 8 * (w_n390 x).toNat + 4 * (w_n391 x).toNat + 8 * (w_n392 x).toNat + 16 * (w_n393 x).toNat) + ((w_n412 x).toNat + 2 * (w_n413 x).toNat + 4 * (w_n414 x).toNat + (w_n415 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n417 x).toNat + (w_n418 x).toNat + 2 * (w_n419 x).toNat + 4 * (w_n420 x).toNat + 2 * (w_n421 x).toNat + 4 * (w_n422 x).toNat + 8 * (w_n423 x).toNat + 4 * (w_n424 x).toNat + 8 * (w_n425 x).toNat + 16 * (w_n426 x).toNat)) + ((w_n427 x).toNat + 2 * (w_n428 x).toNat + 4 * (w_n429 x).toNat)) + (2 * (w_n430 x).toNat + 4 * (w_n431 x).toNat + 8 * (w_n432 x).toNat)) + (4 * (w_n433 x).toNat + 8 * (w_n434 x).toNat + 16 * (w_n435 x).toNat)) + (4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 16 * (w_n438 x).toNat)) + (8 * (w_n439 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n441 x).toNat)) = (16 * (w_n393 x).toNat + 2 * (w_n419 x).toNat + 2 * (w_n421 x).toNat + 16 * (w_n426 x).toNat + (w_n427 x).toNat + 2 * (w_n428 x).toNat + 2 * (w_n430 x).toNat + 4 * (w_n433 x).toNat + 16 * (w_n435 x).toNat + 4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 16 * (w_n438 x).toNat + 8 * (w_n439 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n441 x).toNat) + ((w_n379 x).toNat + (w_n382 x).toNat + (w_n385 x).toNat + (w_n412 x).toNat + (w_n415 x).toNat + (w_n418 x).toNat + 2 * (w_n380 x).toNat + 2 * (w_n383 x).toNat + 2 * (w_n386 x).toNat + 2 * (w_n388 x).toNat + 2 * (w_n413 x).toNat + 2 * (w_n416 x).toNat + 4 * (w_n381 x).toNat + 4 * (w_n384 x).toNat + 4 * (w_n387 x).toNat + 4 * (w_n389 x).toNat + 4 * (w_n391 x).toNat + 4 * (w_n414 x).toNat + 4 * (w_n417 x).toNat + 4 * (w_n420 x).toNat + 4 * (w_n422 x).toNat + 4 * (w_n424 x).toNat + 4 * (w_n429 x).toNat + 4 * (w_n431 x).toNat + 8 * (w_n390 x).toNat + 8 * (w_n392 x).toNat + 8 * (w_n423 x).toNat + 8 * (w_n425 x).toNat + 8 * (w_n432 x).toNat + 8 * (w_n434 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s158 (x : Nat → Bool) : I_t158 x = pc x 847 96 := by
  have hl := s142 x
  have hr := s157 x
  have : pc x 847 96 = pc x 847 48 + pc x 895 48 := pc_add x 847 48 48
  unfold I_t158
  omega
def I_b159 (x : Nat → Bool) : Nat := 0 + (x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat
theorem b159 (x : Nat → Bool) : I_b159 x = (x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat := by
  unfold I_b159
  omega
def I_t159 (x : Nat → Bool) : Nat := I_b159 x
theorem t159 (x : Nat → Bool) : I_t159 x = (w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat := by
  have hs : ((I_b159 x) + ((x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat)) = (((x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat) + ((w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat)) := (add_eq (b159 x) (e147 x))
  have e1 : ((I_b159 x) + ((x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat)) = (I_t159 x) + ((x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat) := by unfold I_t159; ac_rfl
  have e2 : (((x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat) + ((w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat)) = ((w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat) + ((x 961).toNat + (x 962).toNat + (x 963).toNat + (x 964).toNat + (x 965).toNat + (x 966).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s159 (x : Nat → Bool) : I_t159 x = pc x 961 6 := rfl
def I_b160 (x : Nat → Bool) : Nat := 0 + (x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat
theorem b160 (x : Nat → Bool) : I_b160 x = (x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat := by
  unfold I_b160
  omega
def I_t160 (x : Nat → Bool) : Nat := I_b160 x
theorem t160 (x : Nat → Bool) : I_t160 x = (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat := by
  have hs : ((I_b160 x) + ((x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat)) = (((x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat) + ((w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat)) := (add_eq (b160 x) (e148 x))
  have e1 : ((I_b160 x) + ((x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat)) = (I_t160 x) + ((x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat) := by unfold I_t160; ac_rfl
  have e2 : (((x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat) + ((w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat)) = ((w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat) + ((x 955).toNat + (x 956).toNat + (x 957).toNat + (x 958).toNat + (x 959).toNat + (x 960).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s160 (x : Nat → Bool) : I_t160 x = pc x 955 6 := rfl
def I_t161 (x : Nat → Bool) : Nat := I_t159 x + I_t160 x
theorem t161 (x : Nat → Bool) : I_t161 x = (w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat + (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat := by
  have hs : ((I_t159 x) + (I_t160 x)) = (((w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat) + ((w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat)) := (add_eq (t159 x) (t160 x))
  have e1 : ((I_t159 x) + (I_t160 x)) = I_t161 x := by unfold I_t161; ac_rfl
  have e2 : (((w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat) + ((w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat)) = (w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat + (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s161 (x : Nat → Bool) : I_t161 x = pc x 955 12 := by
  have hl := s159 x
  have hr := s160 x
  have : pc x 955 12 = pc x 955 6 + pc x 961 6 := pc_add x 955 6 6
  unfold I_t161
  omega
def I_b162 (x : Nat → Bool) : Nat := 0 + (x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat
theorem b162 (x : Nat → Bool) : I_b162 x = (x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat := by
  unfold I_b162
  omega
def I_t162 (x : Nat → Bool) : Nat := I_b162 x
theorem t162 (x : Nat → Bool) : I_t162 x = (w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat := by
  have hs : ((I_b162 x) + ((x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat)) = (((x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat) + ((w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat)) := (add_eq (b162 x) (e149 x))
  have e1 : ((I_b162 x) + ((x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat)) = (I_t162 x) + ((x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat) := by unfold I_t162; ac_rfl
  have e2 : (((x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat) + ((w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat)) = ((w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat) + ((x 943).toNat + (x 944).toNat + (x 945).toNat + (x 946).toNat + (x 947).toNat + (x 948).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s162 (x : Nat → Bool) : I_t162 x = pc x 943 6 := rfl
def I_b163 (x : Nat → Bool) : Nat := 0 + (x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat
theorem b163 (x : Nat → Bool) : I_b163 x = (x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat := by
  unfold I_b163
  omega
def I_t163 (x : Nat → Bool) : Nat := I_b163 x
theorem t163 (x : Nat → Bool) : I_t163 x = (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat := by
  have hs : ((I_b163 x) + ((x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat)) = (((x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat) + ((w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat)) := (add_eq (b163 x) (e150 x))
  have e1 : ((I_b163 x) + ((x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat)) = (I_t163 x) + ((x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat) := by unfold I_t163; ac_rfl
  have e2 : (((x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat) + ((w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat)) = ((w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat) + ((x 949).toNat + (x 950).toNat + (x 951).toNat + (x 952).toNat + (x 953).toNat + (x 954).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s163 (x : Nat → Bool) : I_t163 x = pc x 949 6 := rfl
def I_t164 (x : Nat → Bool) : Nat := I_t162 x + I_t163 x
theorem t164 (x : Nat → Bool) : I_t164 x = (w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat + (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat := by
  have hs : ((I_t162 x) + (I_t163 x)) = (((w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat) + ((w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat)) := (add_eq (t162 x) (t163 x))
  have e1 : ((I_t162 x) + (I_t163 x)) = I_t164 x := by unfold I_t164; ac_rfl
  have e2 : (((w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat) + ((w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat)) = (w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat + (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s164 (x : Nat → Bool) : I_t164 x = pc x 943 12 := by
  have hl := s162 x
  have hr := s163 x
  have : pc x 943 12 = pc x 943 6 + pc x 949 6 := pc_add x 943 6 6
  unfold I_t164
  omega
def I_t165 (x : Nat → Bool) : Nat := I_t161 x + I_t164 x
theorem t165 (x : Nat → Bool) : I_t165 x = (w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat + (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat + (w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat + (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat := by
  have hs : ((I_t161 x) + (I_t164 x)) = (((w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat + (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat) + ((w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat + (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat)) := (add_eq (t161 x) (t164 x))
  have e1 : ((I_t161 x) + (I_t164 x)) = I_t165 x := by unfold I_t165; ac_rfl
  have e2 : (((w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat + (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat) + ((w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat + (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat)) = (w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat + (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat + (w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat + (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s165 (x : Nat → Bool) : I_t165 x = pc x 943 24 := by
  have hl := s161 x
  have hr := s164 x
  have : pc x 943 24 = pc x 943 12 + pc x 955 12 := pc_add x 943 12 12
  unfold I_t165
  omega
def I_b166 (x : Nat → Bool) : Nat := 0 + (x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat
theorem b166 (x : Nat → Bool) : I_b166 x = (x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat := by
  unfold I_b166
  omega
def I_t166 (x : Nat → Bool) : Nat := I_b166 x
theorem t166 (x : Nat → Bool) : I_t166 x = (w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat := by
  have hs : ((I_b166 x) + ((x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat)) = (((x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat) + ((w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat)) := (add_eq (b166 x) (e151 x))
  have e1 : ((I_b166 x) + ((x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat)) = (I_t166 x) + ((x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat) := by unfold I_t166; ac_rfl
  have e2 : (((x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat) + ((w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat)) = ((w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat) + ((x 973).toNat + (x 974).toNat + (x 975).toNat + (x 976).toNat + (x 977).toNat + (x 978).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s166 (x : Nat → Bool) : I_t166 x = pc x 973 6 := rfl
def I_b167 (x : Nat → Bool) : Nat := 0 + (x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat
theorem b167 (x : Nat → Bool) : I_b167 x = (x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat := by
  unfold I_b167
  omega
def I_t167 (x : Nat → Bool) : Nat := I_b167 x
theorem t167 (x : Nat → Bool) : I_t167 x = (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat := by
  have hs : ((I_b167 x) + ((x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat)) = (((x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat) + ((w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat)) := (add_eq (b167 x) (e152 x))
  have e1 : ((I_b167 x) + ((x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat)) = (I_t167 x) + ((x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat) := by unfold I_t167; ac_rfl
  have e2 : (((x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat) + ((w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat)) = ((w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat) + ((x 967).toNat + (x 968).toNat + (x 969).toNat + (x 970).toNat + (x 971).toNat + (x 972).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s167 (x : Nat → Bool) : I_t167 x = pc x 967 6 := rfl
def I_t168 (x : Nat → Bool) : Nat := I_t166 x + I_t167 x
theorem t168 (x : Nat → Bool) : I_t168 x = (w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat + (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat := by
  have hs : ((I_t166 x) + (I_t167 x)) = (((w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat) + ((w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat)) := (add_eq (t166 x) (t167 x))
  have e1 : ((I_t166 x) + (I_t167 x)) = I_t168 x := by unfold I_t168; ac_rfl
  have e2 : (((w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat) + ((w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat)) = (w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat + (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s168 (x : Nat → Bool) : I_t168 x = pc x 967 12 := by
  have hl := s166 x
  have hr := s167 x
  have : pc x 967 12 = pc x 967 6 + pc x 973 6 := pc_add x 967 6 6
  unfold I_t168
  omega
def I_b169 (x : Nat → Bool) : Nat := 0 + (x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat
theorem b169 (x : Nat → Bool) : I_b169 x = (x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat := by
  unfold I_b169
  omega
def I_t169 (x : Nat → Bool) : Nat := I_b169 x
theorem t169 (x : Nat → Bool) : I_t169 x = (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat := by
  have hs : ((I_b169 x) + ((x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat)) = (((x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat) + ((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat)) := (add_eq (b169 x) (e153 x))
  have e1 : ((I_b169 x) + ((x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat)) = (I_t169 x) + ((x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat) := by unfold I_t169; ac_rfl
  have e2 : (((x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat) + ((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat)) = ((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat) + ((x 985).toNat + (x 986).toNat + (x 987).toNat + (x 988).toNat + (x 989).toNat + (x 990).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s169 (x : Nat → Bool) : I_t169 x = pc x 985 6 := rfl
def I_b170 (x : Nat → Bool) : Nat := 0 + (x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat
theorem b170 (x : Nat → Bool) : I_b170 x = (x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat := by
  unfold I_b170
  omega
def I_t170 (x : Nat → Bool) : Nat := I_b170 x
theorem t170 (x : Nat → Bool) : I_t170 x = (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat := by
  have hs : ((I_b170 x) + ((x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat)) = (((x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat) + ((w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat)) := (add_eq (b170 x) (e154 x))
  have e1 : ((I_b170 x) + ((x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat)) = (I_t170 x) + ((x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat) := by unfold I_t170; ac_rfl
  have e2 : (((x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat) + ((w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat)) = ((w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat) + ((x 979).toNat + (x 980).toNat + (x 981).toNat + (x 982).toNat + (x 983).toNat + (x 984).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s170 (x : Nat → Bool) : I_t170 x = pc x 979 6 := rfl
def I_t171 (x : Nat → Bool) : Nat := I_t169 x + I_t170 x
theorem t171 (x : Nat → Bool) : I_t171 x = (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat := by
  have hs : ((I_t169 x) + (I_t170 x)) = (((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat) + ((w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat)) := (add_eq (t169 x) (t170 x))
  have e1 : ((I_t169 x) + (I_t170 x)) = I_t171 x := by unfold I_t171; ac_rfl
  have e2 : (((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat) + ((w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat)) = (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s171 (x : Nat → Bool) : I_t171 x = pc x 979 12 := by
  have hl := s169 x
  have hr := s170 x
  have : pc x 979 12 = pc x 979 6 + pc x 985 6 := pc_add x 979 6 6
  unfold I_t171
  omega
def I_t172 (x : Nat → Bool) : Nat := I_t168 x + I_t171 x
theorem t172 (x : Nat → Bool) : I_t172 x = (w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat + (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat + (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat := by
  have hs : ((I_t168 x) + (I_t171 x)) = (((w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat + (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat) + ((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat)) := (add_eq (t168 x) (t171 x))
  have e1 : ((I_t168 x) + (I_t171 x)) = I_t172 x := by unfold I_t172; ac_rfl
  have e2 : (((w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat + (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat) + ((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat)) = (w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat + (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat + (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s172 (x : Nat → Bool) : I_t172 x = pc x 967 24 := by
  have hl := s168 x
  have hr := s171 x
  have : pc x 967 24 = pc x 967 12 + pc x 979 12 := pc_add x 967 12 12
  unfold I_t172
  omega
def I_t173 (x : Nat → Bool) : Nat := I_t165 x + I_t172 x
theorem t173 (x : Nat → Bool) : I_t173 x = (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat + (w_n466 x).toNat + 2 * (w_n467 x).toNat + 4 * (w_n468 x).toNat + 2 * (w_n469 x).toNat + 4 * (w_n470 x).toNat + 8 * (w_n471 x).toNat + 4 * (w_n472 x).toNat + 8 * (w_n473 x).toNat + 16 * (w_n474 x).toNat := by
  have hs : (((((I_t165 x) + (I_t172 x)) + ((w_n442 x).toNat + (w_n445 x).toNat + (w_n448 x).toNat + (w_n451 x).toNat + (w_n454 x).toNat + (w_n457 x).toNat)) + (2 * (w_n443 x).toNat + 2 * (w_n446 x).toNat + 2 * (w_n449 x).toNat + 2 * (w_n452 x).toNat + 2 * (w_n455 x).toNat + 2 * (w_n458 x).toNat)) + (4 * (w_n444 x).toNat + 4 * (w_n447 x).toNat + 4 * (w_n450 x).toNat + 4 * (w_n453 x).toNat + 4 * (w_n456 x).toNat + 4 * (w_n459 x).toNat)) = ((((((w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat + (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat + (w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat + (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat) + ((w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat + (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat + (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat)) + ((w_n466 x).toNat + 2 * (w_n467 x).toNat + 4 * (w_n468 x).toNat)) + (2 * (w_n469 x).toNat + 4 * (w_n470 x).toNat + 8 * (w_n471 x).toNat)) + (4 * (w_n472 x).toNat + 8 * (w_n473 x).toNat + 16 * (w_n474 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t165 x) (t172 x)) (e155 x)) (e156 x)) (e157 x))
  have e1 : (((((I_t165 x) + (I_t172 x)) + ((w_n442 x).toNat + (w_n445 x).toNat + (w_n448 x).toNat + (w_n451 x).toNat + (w_n454 x).toNat + (w_n457 x).toNat)) + (2 * (w_n443 x).toNat + 2 * (w_n446 x).toNat + 2 * (w_n449 x).toNat + 2 * (w_n452 x).toNat + 2 * (w_n455 x).toNat + 2 * (w_n458 x).toNat)) + (4 * (w_n444 x).toNat + 4 * (w_n447 x).toNat + 4 * (w_n450 x).toNat + 4 * (w_n453 x).toNat + 4 * (w_n456 x).toNat + 4 * (w_n459 x).toNat)) = (I_t173 x) + ((w_n442 x).toNat + (w_n445 x).toNat + (w_n448 x).toNat + (w_n451 x).toNat + (w_n454 x).toNat + (w_n457 x).toNat + 2 * (w_n443 x).toNat + 2 * (w_n446 x).toNat + 2 * (w_n449 x).toNat + 2 * (w_n452 x).toNat + 2 * (w_n455 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n444 x).toNat + 4 * (w_n447 x).toNat + 4 * (w_n450 x).toNat + 4 * (w_n453 x).toNat + 4 * (w_n456 x).toNat + 4 * (w_n459 x).toNat) := by unfold I_t173; ac_rfl
  have e2 : ((((((w_n442 x).toNat + 2 * (w_n443 x).toNat + 4 * (w_n444 x).toNat + (w_n445 x).toNat + 2 * (w_n446 x).toNat + 4 * (w_n447 x).toNat + (w_n448 x).toNat + 2 * (w_n449 x).toNat + 4 * (w_n450 x).toNat + (w_n451 x).toNat + 2 * (w_n452 x).toNat + 4 * (w_n453 x).toNat) + ((w_n454 x).toNat + 2 * (w_n455 x).toNat + 4 * (w_n456 x).toNat + (w_n457 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n459 x).toNat + (w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat)) + ((w_n466 x).toNat + 2 * (w_n467 x).toNat + 4 * (w_n468 x).toNat)) + (2 * (w_n469 x).toNat + 4 * (w_n470 x).toNat + 8 * (w_n471 x).toNat)) + (4 * (w_n472 x).toNat + 8 * (w_n473 x).toNat + 16 * (w_n474 x).toNat)) = ((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat + (w_n466 x).toNat + 2 * (w_n467 x).toNat + 4 * (w_n468 x).toNat + 2 * (w_n469 x).toNat + 4 * (w_n470 x).toNat + 8 * (w_n471 x).toNat + 4 * (w_n472 x).toNat + 8 * (w_n473 x).toNat + 16 * (w_n474 x).toNat) + ((w_n442 x).toNat + (w_n445 x).toNat + (w_n448 x).toNat + (w_n451 x).toNat + (w_n454 x).toNat + (w_n457 x).toNat + 2 * (w_n443 x).toNat + 2 * (w_n446 x).toNat + 2 * (w_n449 x).toNat + 2 * (w_n452 x).toNat + 2 * (w_n455 x).toNat + 2 * (w_n458 x).toNat + 4 * (w_n444 x).toNat + 4 * (w_n447 x).toNat + 4 * (w_n450 x).toNat + 4 * (w_n453 x).toNat + 4 * (w_n456 x).toNat + 4 * (w_n459 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s173 (x : Nat → Bool) : I_t173 x = pc x 943 48 := by
  have hl := s165 x
  have hr := s172 x
  have : pc x 943 48 = pc x 943 24 + pc x 967 24 := pc_add x 943 24 24
  unfold I_t173
  omega
def I_b174 (x : Nat → Bool) : Nat := 0 + (x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat
theorem b174 (x : Nat → Bool) : I_b174 x = (x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat := by
  unfold I_b174
  omega
def I_t174 (x : Nat → Bool) : Nat := I_b174 x
theorem t174 (x : Nat → Bool) : I_t174 x = (w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat := by
  have hs : ((I_b174 x) + ((x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat)) = (((x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat) + ((w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat)) := (add_eq (b174 x) (e158 x))
  have e1 : ((I_b174 x) + ((x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat)) = (I_t174 x) + ((x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat) := by unfold I_t174; ac_rfl
  have e2 : (((x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat) + ((w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat)) = ((w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat) + ((x 991).toNat + (x 992).toNat + (x 993).toNat + (x 994).toNat + (x 995).toNat + (x 996).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s174 (x : Nat → Bool) : I_t174 x = pc x 991 6 := rfl
def I_b175 (x : Nat → Bool) : Nat := 0 + (x 997).toNat + (x 998).toNat + (x 999).toNat
theorem b175 (x : Nat → Bool) : I_b175 x = (x 997).toNat + (x 998).toNat + (x 999).toNat := by
  unfold I_b175
  omega
def I_t175 (x : Nat → Bool) : Nat := I_b175 x
theorem t175 (x : Nat → Bool) : I_t175 x = (w_n478 x).toNat + 2 * (w_n479 x).toNat := by
  have hs : ((I_b175 x) + ((x 997).toNat + (x 998).toNat + (x 999).toNat)) = (((x 997).toNat + (x 998).toNat + (x 999).toNat) + ((w_n478 x).toNat + 2 * (w_n479 x).toNat)) := (add_eq (b175 x) (e159 x))
  have e1 : ((I_b175 x) + ((x 997).toNat + (x 998).toNat + (x 999).toNat)) = (I_t175 x) + ((x 997).toNat + (x 998).toNat + (x 999).toNat) := by unfold I_t175; ac_rfl
  have e2 : (((x 997).toNat + (x 998).toNat + (x 999).toNat) + ((w_n478 x).toNat + 2 * (w_n479 x).toNat)) = ((w_n478 x).toNat + 2 * (w_n479 x).toNat) + ((x 997).toNat + (x 998).toNat + (x 999).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s175 (x : Nat → Bool) : I_t175 x = pc x 997 3 := rfl
def I_b176 (x : Nat → Bool) : Nat := 0 + (x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat + (x 6).toNat
theorem b176 (x : Nat → Bool) : I_b176 x = (x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat + (x 6).toNat := by
  unfold I_b176
  omega
def I_t176 (x : Nat → Bool) : Nat := I_b176 x
theorem t176 (x : Nat → Bool) : I_t176 x = (w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat := by
  have hs : (((((I_b176 x) + ((x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat)) + ((w_n480 x).toNat + (x 6).toNat)) + (2 * (w_n481 x).toNat + 2 * (w_n484 x).toNat)) + (4 * (w_n482 x).toNat + 4 * (w_n486 x).toNat)) = ((((((x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat + (x 6).toNat) + ((w_n480 x).toNat + 2 * (w_n481 x).toNat + 4 * (w_n482 x).toNat)) + ((w_n483 x).toNat + 2 * (w_n484 x).toNat)) + (2 * (w_n485 x).toNat + 4 * (w_n486 x).toNat)) + (4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (b176 x) (e160 x)) (e161 x)) (e162 x)) (e163 x))
  have e1 : (((((I_b176 x) + ((x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat)) + ((w_n480 x).toNat + (x 6).toNat)) + (2 * (w_n481 x).toNat + 2 * (w_n484 x).toNat)) + (4 * (w_n482 x).toNat + 4 * (w_n486 x).toNat)) = (I_t176 x) + ((x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat + (w_n480 x).toNat + (x 6).toNat + 2 * (w_n481 x).toNat + 2 * (w_n484 x).toNat + 4 * (w_n482 x).toNat + 4 * (w_n486 x).toNat) := by unfold I_t176; ac_rfl
  have e2 : ((((((x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat + (x 6).toNat) + ((w_n480 x).toNat + 2 * (w_n481 x).toNat + 4 * (w_n482 x).toNat)) + ((w_n483 x).toNat + 2 * (w_n484 x).toNat)) + (2 * (w_n485 x).toNat + 4 * (w_n486 x).toNat)) + (4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat)) = ((w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat) + ((x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat + (x 4).toNat + (x 5).toNat + (w_n480 x).toNat + (x 6).toNat + 2 * (w_n481 x).toNat + 2 * (w_n484 x).toNat + 4 * (w_n482 x).toNat + 4 * (w_n486 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s176 (x : Nat → Bool) : I_t176 x = pc x 0 7 := rfl
def I_t177 (x : Nat → Bool) : Nat := I_t175 x + I_t176 x
theorem t177 (x : Nat → Bool) : I_t177 x = (w_n478 x).toNat + 2 * (w_n479 x).toNat + (w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat := by
  have hs : ((I_t175 x) + (I_t176 x)) = (((w_n478 x).toNat + 2 * (w_n479 x).toNat) + ((w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat)) := (add_eq (t175 x) (t176 x))
  have e1 : ((I_t175 x) + (I_t176 x)) = I_t177 x := by unfold I_t177; ac_rfl
  have e2 : (((w_n478 x).toNat + 2 * (w_n479 x).toNat) + ((w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat)) = (w_n478 x).toNat + 2 * (w_n479 x).toNat + (w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s177 (x : Nat → Bool) : I_t177 x = pc x 0 7 + pc x 997 3 := by
  have hl := s175 x
  have hr := s176 x
  unfold I_t177
  omega
def I_t178 (x : Nat → Bool) : Nat := I_t174 x + I_t177 x
theorem t178 (x : Nat → Bool) : I_t178 x = (w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat + (w_n478 x).toNat + 2 * (w_n479 x).toNat + (w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat := by
  have hs : ((I_t174 x) + (I_t177 x)) = (((w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat) + ((w_n478 x).toNat + 2 * (w_n479 x).toNat + (w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat)) := (add_eq (t174 x) (t177 x))
  have e1 : ((I_t174 x) + (I_t177 x)) = I_t178 x := by unfold I_t178; ac_rfl
  have e2 : (((w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat) + ((w_n478 x).toNat + 2 * (w_n479 x).toNat + (w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat)) = (w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat + (w_n478 x).toNat + 2 * (w_n479 x).toNat + (w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s178 (x : Nat → Bool) : I_t178 x = pc x 0 7 + pc x 991 9 := by
  have hl := s174 x
  have hr := s177 x
  have : pc x 991 9 = pc x 991 6 + pc x 997 3 := pc_add x 991 6 3
  unfold I_t178
  omega
def I_b179 (x : Nat → Bool) : Nat := 0 + (x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat
theorem b179 (x : Nat → Bool) : I_b179 x = (x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat := by
  unfold I_b179
  omega
def I_t179 (x : Nat → Bool) : Nat := I_b179 x
theorem t179 (x : Nat → Bool) : I_t179 x = (w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat := by
  have hs : ((I_b179 x) + ((x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat)) = (((x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat) + ((w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat)) := (add_eq (b179 x) (e164 x))
  have e1 : ((I_b179 x) + ((x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat)) = (I_t179 x) + ((x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat) := by unfold I_t179; ac_rfl
  have e2 : (((x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat) + ((w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat)) = ((w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat) + ((x 25).toNat + (x 26).toNat + (x 27).toNat + (x 28).toNat + (x 29).toNat + (x 30).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s179 (x : Nat → Bool) : I_t179 x = pc x 25 6 := rfl
def I_b180 (x : Nat → Bool) : Nat := 0 + (x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat
theorem b180 (x : Nat → Bool) : I_b180 x = (x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat := by
  unfold I_b180
  omega
def I_t180 (x : Nat → Bool) : Nat := I_b180 x
theorem t180 (x : Nat → Bool) : I_t180 x = (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat := by
  have hs : ((I_b180 x) + ((x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat)) = (((x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat) + ((w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat)) := (add_eq (b180 x) (e165 x))
  have e1 : ((I_b180 x) + ((x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat)) = (I_t180 x) + ((x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat) := by unfold I_t180; ac_rfl
  have e2 : (((x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat) + ((w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat)) = ((w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat) + ((x 19).toNat + (x 20).toNat + (x 21).toNat + (x 22).toNat + (x 23).toNat + (x 24).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s180 (x : Nat → Bool) : I_t180 x = pc x 19 6 := rfl
def I_t181 (x : Nat → Bool) : Nat := I_t179 x + I_t180 x
theorem t181 (x : Nat → Bool) : I_t181 x = (w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat + (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat := by
  have hs : ((I_t179 x) + (I_t180 x)) = (((w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat) + ((w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat)) := (add_eq (t179 x) (t180 x))
  have e1 : ((I_t179 x) + (I_t180 x)) = I_t181 x := by unfold I_t181; ac_rfl
  have e2 : (((w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat) + ((w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat)) = (w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat + (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s181 (x : Nat → Bool) : I_t181 x = pc x 19 12 := by
  have hl := s179 x
  have hr := s180 x
  have : pc x 19 12 = pc x 19 6 + pc x 25 6 := pc_add x 19 6 6
  unfold I_t181
  omega
def I_b182 (x : Nat → Bool) : Nat := 0 + (x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat
theorem b182 (x : Nat → Bool) : I_b182 x = (x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat := by
  unfold I_b182
  omega
def I_t182 (x : Nat → Bool) : Nat := I_b182 x
theorem t182 (x : Nat → Bool) : I_t182 x = (w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat := by
  have hs : ((I_b182 x) + ((x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat)) = (((x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat) + ((w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat)) := (add_eq (b182 x) (e166 x))
  have e1 : ((I_b182 x) + ((x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat)) = (I_t182 x) + ((x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat) := by unfold I_t182; ac_rfl
  have e2 : (((x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat) + ((w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat)) = ((w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat) + ((x 13).toNat + (x 14).toNat + (x 15).toNat + (x 16).toNat + (x 17).toNat + (x 18).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s182 (x : Nat → Bool) : I_t182 x = pc x 13 6 := rfl
def I_b183 (x : Nat → Bool) : Nat := 0 + (x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat
theorem b183 (x : Nat → Bool) : I_b183 x = (x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat := by
  unfold I_b183
  omega
def I_t183 (x : Nat → Bool) : Nat := I_b183 x
theorem t183 (x : Nat → Bool) : I_t183 x = (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat := by
  have hs : ((I_b183 x) + ((x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat)) = (((x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat) + ((w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat)) := (add_eq (b183 x) (e167 x))
  have e1 : ((I_b183 x) + ((x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat)) = (I_t183 x) + ((x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat) := by unfold I_t183; ac_rfl
  have e2 : (((x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat) + ((w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat)) = ((w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat) + ((x 7).toNat + (x 8).toNat + (x 9).toNat + (x 10).toNat + (x 11).toNat + (x 12).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s183 (x : Nat → Bool) : I_t183 x = pc x 7 6 := rfl
def I_t184 (x : Nat → Bool) : Nat := I_t182 x + I_t183 x
theorem t184 (x : Nat → Bool) : I_t184 x = (w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat := by
  have hs : ((I_t182 x) + (I_t183 x)) = (((w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat) + ((w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat)) := (add_eq (t182 x) (t183 x))
  have e1 : ((I_t182 x) + (I_t183 x)) = I_t184 x := by unfold I_t184; ac_rfl
  have e2 : (((w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat) + ((w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat)) = (w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s184 (x : Nat → Bool) : I_t184 x = pc x 7 12 := by
  have hl := s182 x
  have hr := s183 x
  have : pc x 7 12 = pc x 7 6 + pc x 13 6 := pc_add x 7 6 6
  unfold I_t184
  omega
def I_t185 (x : Nat → Bool) : Nat := I_t181 x + I_t184 x
theorem t185 (x : Nat → Bool) : I_t185 x = (w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat + (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat + (w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat := by
  have hs : ((I_t181 x) + (I_t184 x)) = (((w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat + (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat) + ((w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat)) := (add_eq (t181 x) (t184 x))
  have e1 : ((I_t181 x) + (I_t184 x)) = I_t185 x := by unfold I_t185; ac_rfl
  have e2 : (((w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat + (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat) + ((w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat)) = (w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat + (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat + (w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s185 (x : Nat → Bool) : I_t185 x = pc x 7 24 := by
  have hl := s181 x
  have hr := s184 x
  have : pc x 7 24 = pc x 7 12 + pc x 19 12 := pc_add x 7 12 12
  unfold I_t185
  omega
def I_t186 (x : Nat → Bool) : Nat := I_t178 x + I_t185 x
theorem t186 (x : Nat → Bool) : I_t186 x = 8 * (w_n488 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + (w_n501 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n503 x).toNat + 2 * (w_n504 x).toNat + 4 * (w_n505 x).toNat + 8 * (w_n506 x).toNat + 4 * (w_n507 x).toNat + 8 * (w_n508 x).toNat + 16 * (w_n509 x).toNat := by
  have hs : (((((I_t178 x) + (I_t185 x)) + ((w_n475 x).toNat + (w_n478 x).toNat + (w_n483 x).toNat + (w_n489 x).toNat + (w_n492 x).toNat + (w_n495 x).toNat)) + (2 * (w_n476 x).toNat + 2 * (w_n479 x).toNat + 2 * (w_n485 x).toNat + 2 * (w_n490 x).toNat + 2 * (w_n493 x).toNat + 2 * (w_n496 x).toNat)) + (4 * (w_n477 x).toNat + 4 * (w_n487 x).toNat + 4 * (w_n491 x).toNat + 4 * (w_n494 x).toNat + 4 * (w_n497 x).toNat + 4 * (w_n500 x).toNat)) = ((((((w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat + (w_n478 x).toNat + 2 * (w_n479 x).toNat + (w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat) + ((w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat + (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat + (w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat)) + ((w_n501 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n503 x).toNat)) + (2 * (w_n504 x).toNat + 4 * (w_n505 x).toNat + 8 * (w_n506 x).toNat)) + (4 * (w_n507 x).toNat + 8 * (w_n508 x).toNat + 16 * (w_n509 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t178 x) (t185 x)) (e168 x)) (e169 x)) (e170 x))
  have e1 : (((((I_t178 x) + (I_t185 x)) + ((w_n475 x).toNat + (w_n478 x).toNat + (w_n483 x).toNat + (w_n489 x).toNat + (w_n492 x).toNat + (w_n495 x).toNat)) + (2 * (w_n476 x).toNat + 2 * (w_n479 x).toNat + 2 * (w_n485 x).toNat + 2 * (w_n490 x).toNat + 2 * (w_n493 x).toNat + 2 * (w_n496 x).toNat)) + (4 * (w_n477 x).toNat + 4 * (w_n487 x).toNat + 4 * (w_n491 x).toNat + 4 * (w_n494 x).toNat + 4 * (w_n497 x).toNat + 4 * (w_n500 x).toNat)) = (I_t186 x) + ((w_n475 x).toNat + (w_n478 x).toNat + (w_n483 x).toNat + (w_n489 x).toNat + (w_n492 x).toNat + (w_n495 x).toNat + 2 * (w_n476 x).toNat + 2 * (w_n479 x).toNat + 2 * (w_n485 x).toNat + 2 * (w_n490 x).toNat + 2 * (w_n493 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n477 x).toNat + 4 * (w_n487 x).toNat + 4 * (w_n491 x).toNat + 4 * (w_n494 x).toNat + 4 * (w_n497 x).toNat + 4 * (w_n500 x).toNat) := by unfold I_t186; ac_rfl
  have e2 : ((((((w_n475 x).toNat + 2 * (w_n476 x).toNat + 4 * (w_n477 x).toNat + (w_n478 x).toNat + 2 * (w_n479 x).toNat + (w_n483 x).toNat + 2 * (w_n485 x).toNat + 4 * (w_n487 x).toNat + 8 * (w_n488 x).toNat) + ((w_n489 x).toNat + 2 * (w_n490 x).toNat + 4 * (w_n491 x).toNat + (w_n492 x).toNat + 2 * (w_n493 x).toNat + 4 * (w_n494 x).toNat + (w_n495 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n497 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + 4 * (w_n500 x).toNat)) + ((w_n501 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n503 x).toNat)) + (2 * (w_n504 x).toNat + 4 * (w_n505 x).toNat + 8 * (w_n506 x).toNat)) + (4 * (w_n507 x).toNat + 8 * (w_n508 x).toNat + 16 * (w_n509 x).toNat)) = (8 * (w_n488 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + (w_n501 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n503 x).toNat + 2 * (w_n504 x).toNat + 4 * (w_n505 x).toNat + 8 * (w_n506 x).toNat + 4 * (w_n507 x).toNat + 8 * (w_n508 x).toNat + 16 * (w_n509 x).toNat) + ((w_n475 x).toNat + (w_n478 x).toNat + (w_n483 x).toNat + (w_n489 x).toNat + (w_n492 x).toNat + (w_n495 x).toNat + 2 * (w_n476 x).toNat + 2 * (w_n479 x).toNat + 2 * (w_n485 x).toNat + 2 * (w_n490 x).toNat + 2 * (w_n493 x).toNat + 2 * (w_n496 x).toNat + 4 * (w_n477 x).toNat + 4 * (w_n487 x).toNat + 4 * (w_n491 x).toNat + 4 * (w_n494 x).toNat + 4 * (w_n497 x).toNat + 4 * (w_n500 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s186 (x : Nat → Bool) : I_t186 x = pc x 0 31 + pc x 991 9 := by
  have hl := s178 x
  have hr := s185 x
  have : pc x 0 31 = pc x 0 7 + pc x 7 24 := pc_add x 0 7 24
  unfold I_t186
  omega
def I_b187 (x : Nat → Bool) : Nat := 0 + (x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat
theorem b187 (x : Nat → Bool) : I_b187 x = (x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat := by
  unfold I_b187
  omega
def I_t187 (x : Nat → Bool) : Nat := I_b187 x
theorem t187 (x : Nat → Bool) : I_t187 x = (w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat := by
  have hs : ((I_b187 x) + ((x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat)) = (((x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat) + ((w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat)) := (add_eq (b187 x) (e171 x))
  have e1 : ((I_b187 x) + ((x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat)) = (I_t187 x) + ((x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat) := by unfold I_t187; ac_rfl
  have e2 : (((x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat) + ((w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat)) = ((w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat) + ((x 43).toNat + (x 44).toNat + (x 45).toNat + (x 46).toNat + (x 47).toNat + (x 48).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s187 (x : Nat → Bool) : I_t187 x = pc x 43 6 := rfl
def I_b188 (x : Nat → Bool) : Nat := 0 + (x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat
theorem b188 (x : Nat → Bool) : I_b188 x = (x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat := by
  unfold I_b188
  omega
def I_t188 (x : Nat → Bool) : Nat := I_b188 x
theorem t188 (x : Nat → Bool) : I_t188 x = (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat := by
  have hs : ((I_b188 x) + ((x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat)) = (((x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat) + ((w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat)) := (add_eq (b188 x) (e172 x))
  have e1 : ((I_b188 x) + ((x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat)) = (I_t188 x) + ((x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat) := by unfold I_t188; ac_rfl
  have e2 : (((x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat) + ((w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat)) = ((w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat) + ((x 49).toNat + (x 50).toNat + (x 51).toNat + (x 52).toNat + (x 53).toNat + (x 54).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s188 (x : Nat → Bool) : I_t188 x = pc x 49 6 := rfl
def I_t189 (x : Nat → Bool) : Nat := I_t187 x + I_t188 x
theorem t189 (x : Nat → Bool) : I_t189 x = (w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat + (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat := by
  have hs : ((I_t187 x) + (I_t188 x)) = (((w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat) + ((w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat)) := (add_eq (t187 x) (t188 x))
  have e1 : ((I_t187 x) + (I_t188 x)) = I_t189 x := by unfold I_t189; ac_rfl
  have e2 : (((w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat) + ((w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat)) = (w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat + (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s189 (x : Nat → Bool) : I_t189 x = pc x 43 12 := by
  have hl := s187 x
  have hr := s188 x
  have : pc x 43 12 = pc x 43 6 + pc x 49 6 := pc_add x 43 6 6
  unfold I_t189
  omega
def I_b190 (x : Nat → Bool) : Nat := 0 + (x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat
theorem b190 (x : Nat → Bool) : I_b190 x = (x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat := by
  unfold I_b190
  omega
def I_t190 (x : Nat → Bool) : Nat := I_b190 x
theorem t190 (x : Nat → Bool) : I_t190 x = (w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat := by
  have hs : ((I_b190 x) + ((x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat)) = (((x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat) + ((w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat)) := (add_eq (b190 x) (e173 x))
  have e1 : ((I_b190 x) + ((x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat)) = (I_t190 x) + ((x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat) := by unfold I_t190; ac_rfl
  have e2 : (((x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat) + ((w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat)) = ((w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat) + ((x 31).toNat + (x 32).toNat + (x 33).toNat + (x 34).toNat + (x 35).toNat + (x 36).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s190 (x : Nat → Bool) : I_t190 x = pc x 31 6 := rfl
def I_b191 (x : Nat → Bool) : Nat := 0 + (x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat
theorem b191 (x : Nat → Bool) : I_b191 x = (x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat := by
  unfold I_b191
  omega
def I_t191 (x : Nat → Bool) : Nat := I_b191 x
theorem t191 (x : Nat → Bool) : I_t191 x = (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat := by
  have hs : ((I_b191 x) + ((x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat)) = (((x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat) + ((w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat)) := (add_eq (b191 x) (e174 x))
  have e1 : ((I_b191 x) + ((x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat)) = (I_t191 x) + ((x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat) := by unfold I_t191; ac_rfl
  have e2 : (((x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat) + ((w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat)) = ((w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat) + ((x 37).toNat + (x 38).toNat + (x 39).toNat + (x 40).toNat + (x 41).toNat + (x 42).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s191 (x : Nat → Bool) : I_t191 x = pc x 37 6 := rfl
def I_t192 (x : Nat → Bool) : Nat := I_t190 x + I_t191 x
theorem t192 (x : Nat → Bool) : I_t192 x = (w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat + (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat := by
  have hs : ((I_t190 x) + (I_t191 x)) = (((w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat) + ((w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat)) := (add_eq (t190 x) (t191 x))
  have e1 : ((I_t190 x) + (I_t191 x)) = I_t192 x := by unfold I_t192; ac_rfl
  have e2 : (((w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat) + ((w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat)) = (w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat + (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s192 (x : Nat → Bool) : I_t192 x = pc x 31 12 := by
  have hl := s190 x
  have hr := s191 x
  have : pc x 31 12 = pc x 31 6 + pc x 37 6 := pc_add x 31 6 6
  unfold I_t192
  omega
def I_t193 (x : Nat → Bool) : Nat := I_t189 x + I_t192 x
theorem t193 (x : Nat → Bool) : I_t193 x = (w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat + (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat + (w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat + (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat := by
  have hs : ((I_t189 x) + (I_t192 x)) = (((w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat + (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat) + ((w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat + (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat)) := (add_eq (t189 x) (t192 x))
  have e1 : ((I_t189 x) + (I_t192 x)) = I_t193 x := by unfold I_t193; ac_rfl
  have e2 : (((w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat + (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat) + ((w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat + (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat)) = (w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat + (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat + (w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat + (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s193 (x : Nat → Bool) : I_t193 x = pc x 31 24 := by
  have hl := s189 x
  have hr := s192 x
  have : pc x 31 24 = pc x 31 12 + pc x 43 12 := pc_add x 31 12 12
  unfold I_t193
  omega
def I_b194 (x : Nat → Bool) : Nat := 0 + (x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat
theorem b194 (x : Nat → Bool) : I_b194 x = (x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat := by
  unfold I_b194
  omega
def I_t194 (x : Nat → Bool) : Nat := I_b194 x
theorem t194 (x : Nat → Bool) : I_t194 x = (w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat := by
  have hs : ((I_b194 x) + ((x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat)) = (((x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat) + ((w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat)) := (add_eq (b194 x) (e175 x))
  have e1 : ((I_b194 x) + ((x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat)) = (I_t194 x) + ((x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat) := by unfold I_t194; ac_rfl
  have e2 : (((x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat) + ((w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat)) = ((w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat) + ((x 55).toNat + (x 56).toNat + (x 57).toNat + (x 58).toNat + (x 59).toNat + (x 60).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s194 (x : Nat → Bool) : I_t194 x = pc x 55 6 := rfl
def I_b195 (x : Nat → Bool) : Nat := 0 + (x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat
theorem b195 (x : Nat → Bool) : I_b195 x = (x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat := by
  unfold I_b195
  omega
def I_t195 (x : Nat → Bool) : Nat := I_b195 x
theorem t195 (x : Nat → Bool) : I_t195 x = (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat := by
  have hs : ((I_b195 x) + ((x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat)) = (((x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat) + ((w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat)) := (add_eq (b195 x) (e176 x))
  have e1 : ((I_b195 x) + ((x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat)) = (I_t195 x) + ((x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat) := by unfold I_t195; ac_rfl
  have e2 : (((x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat) + ((w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat)) = ((w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat) + ((x 61).toNat + (x 62).toNat + (x 63).toNat + (x 64).toNat + (x 65).toNat + (x 66).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s195 (x : Nat → Bool) : I_t195 x = pc x 61 6 := rfl
def I_t196 (x : Nat → Bool) : Nat := I_t194 x + I_t195 x
theorem t196 (x : Nat → Bool) : I_t196 x = (w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat + (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat := by
  have hs : ((I_t194 x) + (I_t195 x)) = (((w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat) + ((w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat)) := (add_eq (t194 x) (t195 x))
  have e1 : ((I_t194 x) + (I_t195 x)) = I_t196 x := by unfold I_t196; ac_rfl
  have e2 : (((w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat) + ((w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat)) = (w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat + (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s196 (x : Nat → Bool) : I_t196 x = pc x 55 12 := by
  have hl := s194 x
  have hr := s195 x
  have : pc x 55 12 = pc x 55 6 + pc x 61 6 := pc_add x 55 6 6
  unfold I_t196
  omega
def I_b197 (x : Nat → Bool) : Nat := 0 + (x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat
theorem b197 (x : Nat → Bool) : I_b197 x = (x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat := by
  unfold I_b197
  omega
def I_t197 (x : Nat → Bool) : Nat := I_b197 x
theorem t197 (x : Nat → Bool) : I_t197 x = (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat := by
  have hs : ((I_b197 x) + ((x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat)) = (((x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat) + ((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat)) := (add_eq (b197 x) (e177 x))
  have e1 : ((I_b197 x) + ((x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat)) = (I_t197 x) + ((x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat) := by unfold I_t197; ac_rfl
  have e2 : (((x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat) + ((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat)) = ((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat) + ((x 73).toNat + (x 74).toNat + (x 75).toNat + (x 76).toNat + (x 77).toNat + (x 78).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s197 (x : Nat → Bool) : I_t197 x = pc x 73 6 := rfl
def I_b198 (x : Nat → Bool) : Nat := 0 + (x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat
theorem b198 (x : Nat → Bool) : I_b198 x = (x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat := by
  unfold I_b198
  omega
def I_t198 (x : Nat → Bool) : Nat := I_b198 x
theorem t198 (x : Nat → Bool) : I_t198 x = (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat := by
  have hs : ((I_b198 x) + ((x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat)) = (((x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat) + ((w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat)) := (add_eq (b198 x) (e178 x))
  have e1 : ((I_b198 x) + ((x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat)) = (I_t198 x) + ((x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat) := by unfold I_t198; ac_rfl
  have e2 : (((x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat) + ((w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat)) = ((w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat) + ((x 67).toNat + (x 68).toNat + (x 69).toNat + (x 70).toNat + (x 71).toNat + (x 72).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s198 (x : Nat → Bool) : I_t198 x = pc x 67 6 := rfl
def I_t199 (x : Nat → Bool) : Nat := I_t197 x + I_t198 x
theorem t199 (x : Nat → Bool) : I_t199 x = (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat := by
  have hs : ((I_t197 x) + (I_t198 x)) = (((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat) + ((w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat)) := (add_eq (t197 x) (t198 x))
  have e1 : ((I_t197 x) + (I_t198 x)) = I_t199 x := by unfold I_t199; ac_rfl
  have e2 : (((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat) + ((w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat)) = (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s199 (x : Nat → Bool) : I_t199 x = pc x 67 12 := by
  have hl := s197 x
  have hr := s198 x
  have : pc x 67 12 = pc x 67 6 + pc x 73 6 := pc_add x 67 6 6
  unfold I_t199
  omega
def I_t200 (x : Nat → Bool) : Nat := I_t196 x + I_t199 x
theorem t200 (x : Nat → Bool) : I_t200 x = (w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat + (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat + (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat := by
  have hs : ((I_t196 x) + (I_t199 x)) = (((w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat + (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat) + ((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat)) := (add_eq (t196 x) (t199 x))
  have e1 : ((I_t196 x) + (I_t199 x)) = I_t200 x := by unfold I_t200; ac_rfl
  have e2 : (((w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat + (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat) + ((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat)) = (w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat + (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat + (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s200 (x : Nat → Bool) : I_t200 x = pc x 55 24 := by
  have hl := s196 x
  have hr := s199 x
  have : pc x 55 24 = pc x 55 12 + pc x 67 12 := pc_add x 55 12 12
  unfold I_t200
  omega
def I_t201 (x : Nat → Bool) : Nat := I_t193 x + I_t200 x
theorem t201 (x : Nat → Bool) : I_t201 x = (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat + (w_n534 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n536 x).toNat + 2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 8 * (w_n539 x).toNat + 4 * (w_n540 x).toNat + 8 * (w_n541 x).toNat + 16 * (w_n542 x).toNat := by
  have hs : (((((I_t193 x) + (I_t200 x)) + ((w_n510 x).toNat + (w_n513 x).toNat + (w_n516 x).toNat + (w_n519 x).toNat + (w_n522 x).toNat + (w_n525 x).toNat)) + (2 * (w_n511 x).toNat + 2 * (w_n514 x).toNat + 2 * (w_n517 x).toNat + 2 * (w_n520 x).toNat + 2 * (w_n523 x).toNat + 2 * (w_n526 x).toNat)) + (4 * (w_n512 x).toNat + 4 * (w_n515 x).toNat + 4 * (w_n518 x).toNat + 4 * (w_n521 x).toNat + 4 * (w_n524 x).toNat + 4 * (w_n527 x).toNat)) = ((((((w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat + (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat + (w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat + (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat) + ((w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat + (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat + (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat)) + ((w_n534 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n536 x).toNat)) + (2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 8 * (w_n539 x).toNat)) + (4 * (w_n540 x).toNat + 8 * (w_n541 x).toNat + 16 * (w_n542 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t193 x) (t200 x)) (e179 x)) (e180 x)) (e181 x))
  have e1 : (((((I_t193 x) + (I_t200 x)) + ((w_n510 x).toNat + (w_n513 x).toNat + (w_n516 x).toNat + (w_n519 x).toNat + (w_n522 x).toNat + (w_n525 x).toNat)) + (2 * (w_n511 x).toNat + 2 * (w_n514 x).toNat + 2 * (w_n517 x).toNat + 2 * (w_n520 x).toNat + 2 * (w_n523 x).toNat + 2 * (w_n526 x).toNat)) + (4 * (w_n512 x).toNat + 4 * (w_n515 x).toNat + 4 * (w_n518 x).toNat + 4 * (w_n521 x).toNat + 4 * (w_n524 x).toNat + 4 * (w_n527 x).toNat)) = (I_t201 x) + ((w_n510 x).toNat + (w_n513 x).toNat + (w_n516 x).toNat + (w_n519 x).toNat + (w_n522 x).toNat + (w_n525 x).toNat + 2 * (w_n511 x).toNat + 2 * (w_n514 x).toNat + 2 * (w_n517 x).toNat + 2 * (w_n520 x).toNat + 2 * (w_n523 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n512 x).toNat + 4 * (w_n515 x).toNat + 4 * (w_n518 x).toNat + 4 * (w_n521 x).toNat + 4 * (w_n524 x).toNat + 4 * (w_n527 x).toNat) := by unfold I_t201; ac_rfl
  have e2 : ((((((w_n510 x).toNat + 2 * (w_n511 x).toNat + 4 * (w_n512 x).toNat + (w_n513 x).toNat + 2 * (w_n514 x).toNat + 4 * (w_n515 x).toNat + (w_n516 x).toNat + 2 * (w_n517 x).toNat + 4 * (w_n518 x).toNat + (w_n519 x).toNat + 2 * (w_n520 x).toNat + 4 * (w_n521 x).toNat) + ((w_n522 x).toNat + 2 * (w_n523 x).toNat + 4 * (w_n524 x).toNat + (w_n525 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n527 x).toNat + (w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat)) + ((w_n534 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n536 x).toNat)) + (2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 8 * (w_n539 x).toNat)) + (4 * (w_n540 x).toNat + 8 * (w_n541 x).toNat + 16 * (w_n542 x).toNat)) = ((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat + (w_n534 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n536 x).toNat + 2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 8 * (w_n539 x).toNat + 4 * (w_n540 x).toNat + 8 * (w_n541 x).toNat + 16 * (w_n542 x).toNat) + ((w_n510 x).toNat + (w_n513 x).toNat + (w_n516 x).toNat + (w_n519 x).toNat + (w_n522 x).toNat + (w_n525 x).toNat + 2 * (w_n511 x).toNat + 2 * (w_n514 x).toNat + 2 * (w_n517 x).toNat + 2 * (w_n520 x).toNat + 2 * (w_n523 x).toNat + 2 * (w_n526 x).toNat + 4 * (w_n512 x).toNat + 4 * (w_n515 x).toNat + 4 * (w_n518 x).toNat + 4 * (w_n521 x).toNat + 4 * (w_n524 x).toNat + 4 * (w_n527 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s201 (x : Nat → Bool) : I_t201 x = pc x 31 48 := by
  have hl := s193 x
  have hr := s200 x
  have : pc x 31 48 = pc x 31 24 + pc x 55 24 := pc_add x 31 24 24
  unfold I_t201
  omega
def I_t202 (x : Nat → Bool) : Nat := I_t186 x + I_t201 x
theorem t202 (x : Nat → Bool) : I_t202 x = (w_n498 x).toNat + (w_n501 x).toNat + 16 * (w_n509 x).toNat + (w_n528 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + 2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 4 * (w_n540 x).toNat + 16 * (w_n542 x).toNat + 2 * (w_n543 x).toNat + 4 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 8 * (w_n547 x).toNat + 16 * (w_n548 x).toNat + 8 * (w_n549 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n551 x).toNat := by
  have hs : (((((I_t186 x) + (I_t201 x)) + (2 * (w_n499 x).toNat + 2 * (w_n502 x).toNat + 2 * (w_n504 x).toNat + 2 * (w_n529 x).toNat + 2 * (w_n532 x).toNat + 2 * (w_n535 x).toNat)) + (4 * (w_n503 x).toNat + 4 * (w_n505 x).toNat + 4 * (w_n507 x).toNat + 4 * (w_n530 x).toNat + 4 * (w_n533 x).toNat + 4 * (w_n536 x).toNat)) + (8 * (w_n488 x).toNat + 8 * (w_n506 x).toNat + 8 * (w_n508 x).toNat + 8 * (w_n539 x).toNat + 8 * (w_n541 x).toNat + 8 * (w_n545 x).toNat)) = (((((8 * (w_n488 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + (w_n501 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n503 x).toNat + 2 * (w_n504 x).toNat + 4 * (w_n505 x).toNat + 8 * (w_n506 x).toNat + 4 * (w_n507 x).toNat + 8 * (w_n508 x).toNat + 16 * (w_n509 x).toNat) + ((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat + (w_n534 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n536 x).toNat + 2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 8 * (w_n539 x).toNat + 4 * (w_n540 x).toNat + 8 * (w_n541 x).toNat + 16 * (w_n542 x).toNat)) + (2 * (w_n543 x).toNat + 4 * (w_n544 x).toNat + 8 * (w_n545 x).toNat)) + (4 * (w_n546 x).toNat + 8 * (w_n547 x).toNat + 16 * (w_n548 x).toNat)) + (8 * (w_n549 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n551 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t186 x) (t201 x)) (e182 x)) (e183 x)) (e184 x))
  have e1 : (((((I_t186 x) + (I_t201 x)) + (2 * (w_n499 x).toNat + 2 * (w_n502 x).toNat + 2 * (w_n504 x).toNat + 2 * (w_n529 x).toNat + 2 * (w_n532 x).toNat + 2 * (w_n535 x).toNat)) + (4 * (w_n503 x).toNat + 4 * (w_n505 x).toNat + 4 * (w_n507 x).toNat + 4 * (w_n530 x).toNat + 4 * (w_n533 x).toNat + 4 * (w_n536 x).toNat)) + (8 * (w_n488 x).toNat + 8 * (w_n506 x).toNat + 8 * (w_n508 x).toNat + 8 * (w_n539 x).toNat + 8 * (w_n541 x).toNat + 8 * (w_n545 x).toNat)) = (I_t202 x) + (2 * (w_n499 x).toNat + 2 * (w_n502 x).toNat + 2 * (w_n504 x).toNat + 2 * (w_n529 x).toNat + 2 * (w_n532 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n503 x).toNat + 4 * (w_n505 x).toNat + 4 * (w_n507 x).toNat + 4 * (w_n530 x).toNat + 4 * (w_n533 x).toNat + 4 * (w_n536 x).toNat + 8 * (w_n488 x).toNat + 8 * (w_n506 x).toNat + 8 * (w_n508 x).toNat + 8 * (w_n539 x).toNat + 8 * (w_n541 x).toNat + 8 * (w_n545 x).toNat) := by unfold I_t202; ac_rfl
  have e2 : (((((8 * (w_n488 x).toNat + (w_n498 x).toNat + 2 * (w_n499 x).toNat + (w_n501 x).toNat + 2 * (w_n502 x).toNat + 4 * (w_n503 x).toNat + 2 * (w_n504 x).toNat + 4 * (w_n505 x).toNat + 8 * (w_n506 x).toNat + 4 * (w_n507 x).toNat + 8 * (w_n508 x).toNat + 16 * (w_n509 x).toNat) + ((w_n528 x).toNat + 2 * (w_n529 x).toNat + 4 * (w_n530 x).toNat + (w_n531 x).toNat + 2 * (w_n532 x).toNat + 4 * (w_n533 x).toNat + (w_n534 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n536 x).toNat + 2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 8 * (w_n539 x).toNat + 4 * (w_n540 x).toNat + 8 * (w_n541 x).toNat + 16 * (w_n542 x).toNat)) + (2 * (w_n543 x).toNat + 4 * (w_n544 x).toNat + 8 * (w_n545 x).toNat)) + (4 * (w_n546 x).toNat + 8 * (w_n547 x).toNat + 16 * (w_n548 x).toNat)) + (8 * (w_n549 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n551 x).toNat)) = ((w_n498 x).toNat + (w_n501 x).toNat + 16 * (w_n509 x).toNat + (w_n528 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + 2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 4 * (w_n540 x).toNat + 16 * (w_n542 x).toNat + 2 * (w_n543 x).toNat + 4 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 8 * (w_n547 x).toNat + 16 * (w_n548 x).toNat + 8 * (w_n549 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n551 x).toNat) + (2 * (w_n499 x).toNat + 2 * (w_n502 x).toNat + 2 * (w_n504 x).toNat + 2 * (w_n529 x).toNat + 2 * (w_n532 x).toNat + 2 * (w_n535 x).toNat + 4 * (w_n503 x).toNat + 4 * (w_n505 x).toNat + 4 * (w_n507 x).toNat + 4 * (w_n530 x).toNat + 4 * (w_n533 x).toNat + 4 * (w_n536 x).toNat + 8 * (w_n488 x).toNat + 8 * (w_n506 x).toNat + 8 * (w_n508 x).toNat + 8 * (w_n539 x).toNat + 8 * (w_n541 x).toNat + 8 * (w_n545 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s202 (x : Nat → Bool) : I_t202 x = pc x 0 79 + pc x 991 9 := by
  have hl := s186 x
  have hr := s201 x
  have : pc x 0 79 = pc x 0 31 + pc x 31 48 := pc_add x 0 31 48
  unfold I_t202
  omega
def I_t203 (x : Nat → Bool) : Nat := I_t173 x + I_t202 x
theorem t203 (x : Nat → Bool) : I_t203 x = (w_n531 x).toNat + (w_n534 x).toNat + 32 * (w_n551 x).toNat + (w_n552 x).toNat + 2 * (w_n553 x).toNat + 2 * (w_n555 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 16 * (w_n563 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat + 16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat := by
  have hs : ((((((((I_t173 x) + (I_t202 x)) + ((w_n460 x).toNat + (w_n463 x).toNat + (w_n466 x).toNat + (w_n498 x).toNat + (w_n501 x).toNat + (w_n528 x).toNat)) + (2 * (w_n461 x).toNat + 2 * (w_n464 x).toNat + 2 * (w_n467 x).toNat + 2 * (w_n469 x).toNat + 2 * (w_n537 x).toNat + 2 * (w_n543 x).toNat)) + (4 * (w_n462 x).toNat + 4 * (w_n465 x).toNat + 4 * (w_n468 x).toNat + 4 * (w_n470 x).toNat + 4 * (w_n472 x).toNat + 4 * (w_n538 x).toNat)) + (4 * (w_n540 x).toNat + 4 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 4 * (w_n554 x).toNat + 4 * (w_n556 x).toNat + 4 * (w_n558 x).toNat)) + (8 * (w_n471 x).toNat + 8 * (w_n473 x).toNat + 8 * (w_n547 x).toNat + 8 * (w_n549 x).toNat + 8 * (w_n557 x).toNat + 8 * (w_n559 x).toNat)) + (16 * (w_n474 x).toNat + 16 * (w_n509 x).toNat + 16 * (w_n542 x).toNat + 16 * (w_n548 x).toNat + 16 * (w_n550 x).toNat + 16 * (w_n560 x).toNat)) = (((((((((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat + (w_n466 x).toNat + 2 * (w_n467 x).toNat + 4 * (w_n468 x).toNat + 2 * (w_n469 x).toNat + 4 * (w_n470 x).toNat + 8 * (w_n471 x).toNat + 4 * (w_n472 x).toNat + 8 * (w_n473 x).toNat + 16 * (w_n474 x).toNat) + ((w_n498 x).toNat + (w_n501 x).toNat + 16 * (w_n509 x).toNat + (w_n528 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + 2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 4 * (w_n540 x).toNat + 16 * (w_n542 x).toNat + 2 * (w_n543 x).toNat + 4 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 8 * (w_n547 x).toNat + 16 * (w_n548 x).toNat + 8 * (w_n549 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n551 x).toNat)) + ((w_n552 x).toNat + 2 * (w_n553 x).toNat + 4 * (w_n554 x).toNat)) + (2 * (w_n555 x).toNat + 4 * (w_n556 x).toNat + 8 * (w_n557 x).toNat)) + (4 * (w_n558 x).toNat + 8 * (w_n559 x).toNat + 16 * (w_n560 x).toNat)) + (4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 16 * (w_n563 x).toNat)) + (8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat)) + (16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t173 x) (t202 x)) (e185 x)) (e186 x)) (e187 x)) (e188 x)) (e189 x)) (e190 x))
  have e1 : ((((((((I_t173 x) + (I_t202 x)) + ((w_n460 x).toNat + (w_n463 x).toNat + (w_n466 x).toNat + (w_n498 x).toNat + (w_n501 x).toNat + (w_n528 x).toNat)) + (2 * (w_n461 x).toNat + 2 * (w_n464 x).toNat + 2 * (w_n467 x).toNat + 2 * (w_n469 x).toNat + 2 * (w_n537 x).toNat + 2 * (w_n543 x).toNat)) + (4 * (w_n462 x).toNat + 4 * (w_n465 x).toNat + 4 * (w_n468 x).toNat + 4 * (w_n470 x).toNat + 4 * (w_n472 x).toNat + 4 * (w_n538 x).toNat)) + (4 * (w_n540 x).toNat + 4 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 4 * (w_n554 x).toNat + 4 * (w_n556 x).toNat + 4 * (w_n558 x).toNat)) + (8 * (w_n471 x).toNat + 8 * (w_n473 x).toNat + 8 * (w_n547 x).toNat + 8 * (w_n549 x).toNat + 8 * (w_n557 x).toNat + 8 * (w_n559 x).toNat)) + (16 * (w_n474 x).toNat + 16 * (w_n509 x).toNat + 16 * (w_n542 x).toNat + 16 * (w_n548 x).toNat + 16 * (w_n550 x).toNat + 16 * (w_n560 x).toNat)) = (I_t203 x) + ((w_n460 x).toNat + (w_n463 x).toNat + (w_n466 x).toNat + (w_n498 x).toNat + (w_n501 x).toNat + (w_n528 x).toNat + 2 * (w_n461 x).toNat + 2 * (w_n464 x).toNat + 2 * (w_n467 x).toNat + 2 * (w_n469 x).toNat + 2 * (w_n537 x).toNat + 2 * (w_n543 x).toNat + 4 * (w_n462 x).toNat + 4 * (w_n465 x).toNat + 4 * (w_n468 x).toNat + 4 * (w_n470 x).toNat + 4 * (w_n472 x).toNat + 4 * (w_n538 x).toNat + 4 * (w_n540 x).toNat + 4 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 4 * (w_n554 x).toNat + 4 * (w_n556 x).toNat + 4 * (w_n558 x).toNat + 8 * (w_n471 x).toNat + 8 * (w_n473 x).toNat + 8 * (w_n547 x).toNat + 8 * (w_n549 x).toNat + 8 * (w_n557 x).toNat + 8 * (w_n559 x).toNat + 16 * (w_n474 x).toNat + 16 * (w_n509 x).toNat + 16 * (w_n542 x).toNat + 16 * (w_n548 x).toNat + 16 * (w_n550 x).toNat + 16 * (w_n560 x).toNat) := by unfold I_t203; ac_rfl
  have e2 : (((((((((w_n460 x).toNat + 2 * (w_n461 x).toNat + 4 * (w_n462 x).toNat + (w_n463 x).toNat + 2 * (w_n464 x).toNat + 4 * (w_n465 x).toNat + (w_n466 x).toNat + 2 * (w_n467 x).toNat + 4 * (w_n468 x).toNat + 2 * (w_n469 x).toNat + 4 * (w_n470 x).toNat + 8 * (w_n471 x).toNat + 4 * (w_n472 x).toNat + 8 * (w_n473 x).toNat + 16 * (w_n474 x).toNat) + ((w_n498 x).toNat + (w_n501 x).toNat + 16 * (w_n509 x).toNat + (w_n528 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + 2 * (w_n537 x).toNat + 4 * (w_n538 x).toNat + 4 * (w_n540 x).toNat + 16 * (w_n542 x).toNat + 2 * (w_n543 x).toNat + 4 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 8 * (w_n547 x).toNat + 16 * (w_n548 x).toNat + 8 * (w_n549 x).toNat + 16 * (w_n550 x).toNat + 32 * (w_n551 x).toNat)) + ((w_n552 x).toNat + 2 * (w_n553 x).toNat + 4 * (w_n554 x).toNat)) + (2 * (w_n555 x).toNat + 4 * (w_n556 x).toNat + 8 * (w_n557 x).toNat)) + (4 * (w_n558 x).toNat + 8 * (w_n559 x).toNat + 16 * (w_n560 x).toNat)) + (4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 16 * (w_n563 x).toNat)) + (8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat)) + (16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat)) = ((w_n531 x).toNat + (w_n534 x).toNat + 32 * (w_n551 x).toNat + (w_n552 x).toNat + 2 * (w_n553 x).toNat + 2 * (w_n555 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 16 * (w_n563 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat + 16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat) + ((w_n460 x).toNat + (w_n463 x).toNat + (w_n466 x).toNat + (w_n498 x).toNat + (w_n501 x).toNat + (w_n528 x).toNat + 2 * (w_n461 x).toNat + 2 * (w_n464 x).toNat + 2 * (w_n467 x).toNat + 2 * (w_n469 x).toNat + 2 * (w_n537 x).toNat + 2 * (w_n543 x).toNat + 4 * (w_n462 x).toNat + 4 * (w_n465 x).toNat + 4 * (w_n468 x).toNat + 4 * (w_n470 x).toNat + 4 * (w_n472 x).toNat + 4 * (w_n538 x).toNat + 4 * (w_n540 x).toNat + 4 * (w_n544 x).toNat + 4 * (w_n546 x).toNat + 4 * (w_n554 x).toNat + 4 * (w_n556 x).toNat + 4 * (w_n558 x).toNat + 8 * (w_n471 x).toNat + 8 * (w_n473 x).toNat + 8 * (w_n547 x).toNat + 8 * (w_n549 x).toNat + 8 * (w_n557 x).toNat + 8 * (w_n559 x).toNat + 16 * (w_n474 x).toNat + 16 * (w_n509 x).toNat + 16 * (w_n542 x).toNat + 16 * (w_n548 x).toNat + 16 * (w_n550 x).toNat + 16 * (w_n560 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s203 (x : Nat → Bool) : I_t203 x = pc x 0 79 + pc x 943 57 := by
  have hl := s173 x
  have hr := s202 x
  have : pc x 943 57 = pc x 943 48 + pc x 991 9 := pc_add x 943 48 9
  unfold I_t203
  omega
def I_t204 (x : Nat → Bool) : Nat := I_t158 x + I_t203 x
theorem t204 (x : Nat → Bool) : I_t204 x = (w_n427 x).toNat + 4 * (w_n433 x).toNat + 4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 8 * (w_n439 x).toNat + 32 * (w_n441 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + 32 * (w_n551 x).toNat + (w_n552 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat + 16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat + 2 * (w_n570 x).toNat + 4 * (w_n571 x).toNat + 8 * (w_n572 x).toNat + 16 * (w_n573 x).toNat + 32 * (w_n574 x).toNat + 64 * (w_n575 x).toNat := by
  have hs : ((((I_t158 x) + (I_t203 x)) + (2 * (w_n419 x).toNat + 2 * (w_n421 x).toNat + 2 * (w_n428 x).toNat + 2 * (w_n430 x).toNat + 2 * (w_n553 x).toNat + 2 * (w_n555 x).toNat)) + (16 * (w_n393 x).toNat + 16 * (w_n426 x).toNat + 16 * (w_n435 x).toNat + 16 * (w_n438 x).toNat + 16 * (w_n440 x).toNat + 16 * (w_n563 x).toNat)) = ((((16 * (w_n393 x).toNat + 2 * (w_n419 x).toNat + 2 * (w_n421 x).toNat + 16 * (w_n426 x).toNat + (w_n427 x).toNat + 2 * (w_n428 x).toNat + 2 * (w_n430 x).toNat + 4 * (w_n433 x).toNat + 16 * (w_n435 x).toNat + 4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 16 * (w_n438 x).toNat + 8 * (w_n439 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n441 x).toNat) + ((w_n531 x).toNat + (w_n534 x).toNat + 32 * (w_n551 x).toNat + (w_n552 x).toNat + 2 * (w_n553 x).toNat + 2 * (w_n555 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 16 * (w_n563 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat + 16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat)) + (2 * (w_n570 x).toNat + 4 * (w_n571 x).toNat + 8 * (w_n572 x).toNat)) + (16 * (w_n573 x).toNat + 32 * (w_n574 x).toNat + 64 * (w_n575 x).toNat)) := (add_eq (add_eq (add_eq (t158 x) (t203 x)) (e191 x)) (e192 x))
  have e1 : ((((I_t158 x) + (I_t203 x)) + (2 * (w_n419 x).toNat + 2 * (w_n421 x).toNat + 2 * (w_n428 x).toNat + 2 * (w_n430 x).toNat + 2 * (w_n553 x).toNat + 2 * (w_n555 x).toNat)) + (16 * (w_n393 x).toNat + 16 * (w_n426 x).toNat + 16 * (w_n435 x).toNat + 16 * (w_n438 x).toNat + 16 * (w_n440 x).toNat + 16 * (w_n563 x).toNat)) = (I_t204 x) + (2 * (w_n419 x).toNat + 2 * (w_n421 x).toNat + 2 * (w_n428 x).toNat + 2 * (w_n430 x).toNat + 2 * (w_n553 x).toNat + 2 * (w_n555 x).toNat + 16 * (w_n393 x).toNat + 16 * (w_n426 x).toNat + 16 * (w_n435 x).toNat + 16 * (w_n438 x).toNat + 16 * (w_n440 x).toNat + 16 * (w_n563 x).toNat) := by unfold I_t204; ac_rfl
  have e2 : ((((16 * (w_n393 x).toNat + 2 * (w_n419 x).toNat + 2 * (w_n421 x).toNat + 16 * (w_n426 x).toNat + (w_n427 x).toNat + 2 * (w_n428 x).toNat + 2 * (w_n430 x).toNat + 4 * (w_n433 x).toNat + 16 * (w_n435 x).toNat + 4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 16 * (w_n438 x).toNat + 8 * (w_n439 x).toNat + 16 * (w_n440 x).toNat + 32 * (w_n441 x).toNat) + ((w_n531 x).toNat + (w_n534 x).toNat + 32 * (w_n551 x).toNat + (w_n552 x).toNat + 2 * (w_n553 x).toNat + 2 * (w_n555 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 16 * (w_n563 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat + 16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat)) + (2 * (w_n570 x).toNat + 4 * (w_n571 x).toNat + 8 * (w_n572 x).toNat)) + (16 * (w_n573 x).toNat + 32 * (w_n574 x).toNat + 64 * (w_n575 x).toNat)) = ((w_n427 x).toNat + 4 * (w_n433 x).toNat + 4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 8 * (w_n439 x).toNat + 32 * (w_n441 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + 32 * (w_n551 x).toNat + (w_n552 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat + 16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat + 2 * (w_n570 x).toNat + 4 * (w_n571 x).toNat + 8 * (w_n572 x).toNat + 16 * (w_n573 x).toNat + 32 * (w_n574 x).toNat + 64 * (w_n575 x).toNat) + (2 * (w_n419 x).toNat + 2 * (w_n421 x).toNat + 2 * (w_n428 x).toNat + 2 * (w_n430 x).toNat + 2 * (w_n553 x).toNat + 2 * (w_n555 x).toNat + 16 * (w_n393 x).toNat + 16 * (w_n426 x).toNat + 16 * (w_n435 x).toNat + 16 * (w_n438 x).toNat + 16 * (w_n440 x).toNat + 16 * (w_n563 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s204 (x : Nat → Bool) : I_t204 x = pc x 0 79 + pc x 847 153 := by
  have hl := s158 x
  have hr := s203 x
  have : pc x 847 153 = pc x 847 96 + pc x 943 57 := pc_add x 847 96 57
  unfold I_t204
  omega
def I_b205 (x : Nat → Bool) : Nat := 0 + (x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat
theorem b205 (x : Nat → Bool) : I_b205 x = (x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat := by
  unfold I_b205
  omega
def I_t205 (x : Nat → Bool) : Nat := I_b205 x
theorem t205 (x : Nat → Bool) : I_t205 x = (w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat := by
  have hs : ((I_b205 x) + ((x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat)) = (((x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat) + ((w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat)) := (add_eq (b205 x) (e193 x))
  have e1 : ((I_b205 x) + ((x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat)) = (I_t205 x) + ((x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat) := by unfold I_t205; ac_rfl
  have e2 : (((x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat) + ((w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat)) = ((w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat) + ((x 145).toNat + (x 146).toNat + (x 147).toNat + (x 148).toNat + (x 149).toNat + (x 150).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s205 (x : Nat → Bool) : I_t205 x = pc x 145 6 := rfl
def I_b206 (x : Nat → Bool) : Nat := 0 + (x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat
theorem b206 (x : Nat → Bool) : I_b206 x = (x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat := by
  unfold I_b206
  omega
def I_t206 (x : Nat → Bool) : Nat := I_b206 x
theorem t206 (x : Nat → Bool) : I_t206 x = (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat := by
  have hs : ((I_b206 x) + ((x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat)) = (((x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat) + ((w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat)) := (add_eq (b206 x) (e194 x))
  have e1 : ((I_b206 x) + ((x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat)) = (I_t206 x) + ((x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat) := by unfold I_t206; ac_rfl
  have e2 : (((x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat) + ((w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat)) = ((w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat) + ((x 139).toNat + (x 140).toNat + (x 141).toNat + (x 142).toNat + (x 143).toNat + (x 144).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s206 (x : Nat → Bool) : I_t206 x = pc x 139 6 := rfl
def I_t207 (x : Nat → Bool) : Nat := I_t205 x + I_t206 x
theorem t207 (x : Nat → Bool) : I_t207 x = (w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat + (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat := by
  have hs : ((I_t205 x) + (I_t206 x)) = (((w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat) + ((w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat)) := (add_eq (t205 x) (t206 x))
  have e1 : ((I_t205 x) + (I_t206 x)) = I_t207 x := by unfold I_t207; ac_rfl
  have e2 : (((w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat) + ((w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat)) = (w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat + (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s207 (x : Nat → Bool) : I_t207 x = pc x 139 12 := by
  have hl := s205 x
  have hr := s206 x
  have : pc x 139 12 = pc x 139 6 + pc x 145 6 := pc_add x 139 6 6
  unfold I_t207
  omega
def I_b208 (x : Nat → Bool) : Nat := 0 + (x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat
theorem b208 (x : Nat → Bool) : I_b208 x = (x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat := by
  unfold I_b208
  omega
def I_t208 (x : Nat → Bool) : Nat := I_b208 x
theorem t208 (x : Nat → Bool) : I_t208 x = (w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat := by
  have hs : ((I_b208 x) + ((x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat)) = (((x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat) + ((w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat)) := (add_eq (b208 x) (e195 x))
  have e1 : ((I_b208 x) + ((x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat)) = (I_t208 x) + ((x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat) := by unfold I_t208; ac_rfl
  have e2 : (((x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat) + ((w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat)) = ((w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat) + ((x 127).toNat + (x 128).toNat + (x 129).toNat + (x 130).toNat + (x 131).toNat + (x 132).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s208 (x : Nat → Bool) : I_t208 x = pc x 127 6 := rfl
def I_b209 (x : Nat → Bool) : Nat := 0 + (x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat
theorem b209 (x : Nat → Bool) : I_b209 x = (x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat := by
  unfold I_b209
  omega
def I_t209 (x : Nat → Bool) : Nat := I_b209 x
theorem t209 (x : Nat → Bool) : I_t209 x = (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat := by
  have hs : ((I_b209 x) + ((x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat)) = (((x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat) + ((w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat)) := (add_eq (b209 x) (e196 x))
  have e1 : ((I_b209 x) + ((x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat)) = (I_t209 x) + ((x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat) := by unfold I_t209; ac_rfl
  have e2 : (((x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat) + ((w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat)) = ((w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat) + ((x 133).toNat + (x 134).toNat + (x 135).toNat + (x 136).toNat + (x 137).toNat + (x 138).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s209 (x : Nat → Bool) : I_t209 x = pc x 133 6 := rfl
def I_t210 (x : Nat → Bool) : Nat := I_t208 x + I_t209 x
theorem t210 (x : Nat → Bool) : I_t210 x = (w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat + (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat := by
  have hs : ((I_t208 x) + (I_t209 x)) = (((w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat) + ((w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat)) := (add_eq (t208 x) (t209 x))
  have e1 : ((I_t208 x) + (I_t209 x)) = I_t210 x := by unfold I_t210; ac_rfl
  have e2 : (((w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat) + ((w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat)) = (w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat + (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s210 (x : Nat → Bool) : I_t210 x = pc x 127 12 := by
  have hl := s208 x
  have hr := s209 x
  have : pc x 127 12 = pc x 127 6 + pc x 133 6 := pc_add x 127 6 6
  unfold I_t210
  omega
def I_t211 (x : Nat → Bool) : Nat := I_t207 x + I_t210 x
theorem t211 (x : Nat → Bool) : I_t211 x = (w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat + (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat + (w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat + (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat := by
  have hs : ((I_t207 x) + (I_t210 x)) = (((w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat + (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat) + ((w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat + (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat)) := (add_eq (t207 x) (t210 x))
  have e1 : ((I_t207 x) + (I_t210 x)) = I_t211 x := by unfold I_t211; ac_rfl
  have e2 : (((w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat + (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat) + ((w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat + (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat)) = (w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat + (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat + (w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat + (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s211 (x : Nat → Bool) : I_t211 x = pc x 127 24 := by
  have hl := s207 x
  have hr := s210 x
  have : pc x 127 24 = pc x 127 12 + pc x 139 12 := pc_add x 127 12 12
  unfold I_t211
  omega
def I_b212 (x : Nat → Bool) : Nat := 0 + (x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat
theorem b212 (x : Nat → Bool) : I_b212 x = (x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat := by
  unfold I_b212
  omega
def I_t212 (x : Nat → Bool) : Nat := I_b212 x
theorem t212 (x : Nat → Bool) : I_t212 x = (w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat := by
  have hs : ((I_b212 x) + ((x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat)) = (((x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat) + ((w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat)) := (add_eq (b212 x) (e197 x))
  have e1 : ((I_b212 x) + ((x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat)) = (I_t212 x) + ((x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat) := by unfold I_t212; ac_rfl
  have e2 : (((x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat) + ((w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat)) = ((w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat) + ((x 169).toNat + (x 170).toNat + (x 171).toNat + (x 172).toNat + (x 173).toNat + (x 174).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s212 (x : Nat → Bool) : I_t212 x = pc x 169 6 := rfl
def I_b213 (x : Nat → Bool) : Nat := 0 + (x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat
theorem b213 (x : Nat → Bool) : I_b213 x = (x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat := by
  unfold I_b213
  omega
def I_t213 (x : Nat → Bool) : Nat := I_b213 x
theorem t213 (x : Nat → Bool) : I_t213 x = (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat := by
  have hs : ((I_b213 x) + ((x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat)) = (((x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat) + ((w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat)) := (add_eq (b213 x) (e198 x))
  have e1 : ((I_b213 x) + ((x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat)) = (I_t213 x) + ((x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat) := by unfold I_t213; ac_rfl
  have e2 : (((x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat) + ((w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat)) = ((w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat) + ((x 163).toNat + (x 164).toNat + (x 165).toNat + (x 166).toNat + (x 167).toNat + (x 168).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s213 (x : Nat → Bool) : I_t213 x = pc x 163 6 := rfl
def I_t214 (x : Nat → Bool) : Nat := I_t212 x + I_t213 x
theorem t214 (x : Nat → Bool) : I_t214 x = (w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat + (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat := by
  have hs : ((I_t212 x) + (I_t213 x)) = (((w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat) + ((w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat)) := (add_eq (t212 x) (t213 x))
  have e1 : ((I_t212 x) + (I_t213 x)) = I_t214 x := by unfold I_t214; ac_rfl
  have e2 : (((w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat) + ((w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat)) = (w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat + (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s214 (x : Nat → Bool) : I_t214 x = pc x 163 12 := by
  have hl := s212 x
  have hr := s213 x
  have : pc x 163 12 = pc x 163 6 + pc x 169 6 := pc_add x 163 6 6
  unfold I_t214
  omega
def I_b215 (x : Nat → Bool) : Nat := 0 + (x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat
theorem b215 (x : Nat → Bool) : I_b215 x = (x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat := by
  unfold I_b215
  omega
def I_t215 (x : Nat → Bool) : Nat := I_b215 x
theorem t215 (x : Nat → Bool) : I_t215 x = (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat := by
  have hs : ((I_b215 x) + ((x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat)) = (((x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat) + ((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat)) := (add_eq (b215 x) (e199 x))
  have e1 : ((I_b215 x) + ((x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat)) = (I_t215 x) + ((x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat) := by unfold I_t215; ac_rfl
  have e2 : (((x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat) + ((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat)) = ((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat) + ((x 151).toNat + (x 152).toNat + (x 153).toNat + (x 154).toNat + (x 155).toNat + (x 156).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s215 (x : Nat → Bool) : I_t215 x = pc x 151 6 := rfl
def I_b216 (x : Nat → Bool) : Nat := 0 + (x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat
theorem b216 (x : Nat → Bool) : I_b216 x = (x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat := by
  unfold I_b216
  omega
def I_t216 (x : Nat → Bool) : Nat := I_b216 x
theorem t216 (x : Nat → Bool) : I_t216 x = (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat := by
  have hs : ((I_b216 x) + ((x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat)) = (((x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat) + ((w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat)) := (add_eq (b216 x) (e200 x))
  have e1 : ((I_b216 x) + ((x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat)) = (I_t216 x) + ((x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat) := by unfold I_t216; ac_rfl
  have e2 : (((x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat) + ((w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat)) = ((w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat) + ((x 157).toNat + (x 158).toNat + (x 159).toNat + (x 160).toNat + (x 161).toNat + (x 162).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s216 (x : Nat → Bool) : I_t216 x = pc x 157 6 := rfl
def I_t217 (x : Nat → Bool) : Nat := I_t215 x + I_t216 x
theorem t217 (x : Nat → Bool) : I_t217 x = (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat := by
  have hs : ((I_t215 x) + (I_t216 x)) = (((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat) + ((w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat)) := (add_eq (t215 x) (t216 x))
  have e1 : ((I_t215 x) + (I_t216 x)) = I_t217 x := by unfold I_t217; ac_rfl
  have e2 : (((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat) + ((w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat)) = (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s217 (x : Nat → Bool) : I_t217 x = pc x 151 12 := by
  have hl := s215 x
  have hr := s216 x
  have : pc x 151 12 = pc x 151 6 + pc x 157 6 := pc_add x 151 6 6
  unfold I_t217
  omega
def I_t218 (x : Nat → Bool) : Nat := I_t214 x + I_t217 x
theorem t218 (x : Nat → Bool) : I_t218 x = (w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat + (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat + (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat := by
  have hs : ((I_t214 x) + (I_t217 x)) = (((w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat + (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat) + ((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat)) := (add_eq (t214 x) (t217 x))
  have e1 : ((I_t214 x) + (I_t217 x)) = I_t218 x := by unfold I_t218; ac_rfl
  have e2 : (((w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat + (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat) + ((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat)) = (w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat + (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat + (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s218 (x : Nat → Bool) : I_t218 x = pc x 151 24 := by
  have hl := s214 x
  have hr := s217 x
  have : pc x 151 24 = pc x 151 12 + pc x 163 12 := pc_add x 151 12 12
  unfold I_t218
  omega
def I_t219 (x : Nat → Bool) : Nat := I_t211 x + I_t218 x
theorem t219 (x : Nat → Bool) : I_t219 x = (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat + (w_n600 x).toNat + 2 * (w_n601 x).toNat + 4 * (w_n602 x).toNat + 2 * (w_n603 x).toNat + 4 * (w_n604 x).toNat + 8 * (w_n605 x).toNat + 4 * (w_n606 x).toNat + 8 * (w_n607 x).toNat + 16 * (w_n608 x).toNat := by
  have hs : (((((I_t211 x) + (I_t218 x)) + ((w_n576 x).toNat + (w_n579 x).toNat + (w_n582 x).toNat + (w_n585 x).toNat + (w_n588 x).toNat + (w_n591 x).toNat)) + (2 * (w_n577 x).toNat + 2 * (w_n580 x).toNat + 2 * (w_n583 x).toNat + 2 * (w_n586 x).toNat + 2 * (w_n589 x).toNat + 2 * (w_n592 x).toNat)) + (4 * (w_n578 x).toNat + 4 * (w_n581 x).toNat + 4 * (w_n584 x).toNat + 4 * (w_n587 x).toNat + 4 * (w_n590 x).toNat + 4 * (w_n593 x).toNat)) = ((((((w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat + (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat + (w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat + (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat) + ((w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat + (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat + (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat)) + ((w_n600 x).toNat + 2 * (w_n601 x).toNat + 4 * (w_n602 x).toNat)) + (2 * (w_n603 x).toNat + 4 * (w_n604 x).toNat + 8 * (w_n605 x).toNat)) + (4 * (w_n606 x).toNat + 8 * (w_n607 x).toNat + 16 * (w_n608 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t211 x) (t218 x)) (e201 x)) (e202 x)) (e203 x))
  have e1 : (((((I_t211 x) + (I_t218 x)) + ((w_n576 x).toNat + (w_n579 x).toNat + (w_n582 x).toNat + (w_n585 x).toNat + (w_n588 x).toNat + (w_n591 x).toNat)) + (2 * (w_n577 x).toNat + 2 * (w_n580 x).toNat + 2 * (w_n583 x).toNat + 2 * (w_n586 x).toNat + 2 * (w_n589 x).toNat + 2 * (w_n592 x).toNat)) + (4 * (w_n578 x).toNat + 4 * (w_n581 x).toNat + 4 * (w_n584 x).toNat + 4 * (w_n587 x).toNat + 4 * (w_n590 x).toNat + 4 * (w_n593 x).toNat)) = (I_t219 x) + ((w_n576 x).toNat + (w_n579 x).toNat + (w_n582 x).toNat + (w_n585 x).toNat + (w_n588 x).toNat + (w_n591 x).toNat + 2 * (w_n577 x).toNat + 2 * (w_n580 x).toNat + 2 * (w_n583 x).toNat + 2 * (w_n586 x).toNat + 2 * (w_n589 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n578 x).toNat + 4 * (w_n581 x).toNat + 4 * (w_n584 x).toNat + 4 * (w_n587 x).toNat + 4 * (w_n590 x).toNat + 4 * (w_n593 x).toNat) := by unfold I_t219; ac_rfl
  have e2 : ((((((w_n576 x).toNat + 2 * (w_n577 x).toNat + 4 * (w_n578 x).toNat + (w_n579 x).toNat + 2 * (w_n580 x).toNat + 4 * (w_n581 x).toNat + (w_n582 x).toNat + 2 * (w_n583 x).toNat + 4 * (w_n584 x).toNat + (w_n585 x).toNat + 2 * (w_n586 x).toNat + 4 * (w_n587 x).toNat) + ((w_n588 x).toNat + 2 * (w_n589 x).toNat + 4 * (w_n590 x).toNat + (w_n591 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n593 x).toNat + (w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat)) + ((w_n600 x).toNat + 2 * (w_n601 x).toNat + 4 * (w_n602 x).toNat)) + (2 * (w_n603 x).toNat + 4 * (w_n604 x).toNat + 8 * (w_n605 x).toNat)) + (4 * (w_n606 x).toNat + 8 * (w_n607 x).toNat + 16 * (w_n608 x).toNat)) = ((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat + (w_n600 x).toNat + 2 * (w_n601 x).toNat + 4 * (w_n602 x).toNat + 2 * (w_n603 x).toNat + 4 * (w_n604 x).toNat + 8 * (w_n605 x).toNat + 4 * (w_n606 x).toNat + 8 * (w_n607 x).toNat + 16 * (w_n608 x).toNat) + ((w_n576 x).toNat + (w_n579 x).toNat + (w_n582 x).toNat + (w_n585 x).toNat + (w_n588 x).toNat + (w_n591 x).toNat + 2 * (w_n577 x).toNat + 2 * (w_n580 x).toNat + 2 * (w_n583 x).toNat + 2 * (w_n586 x).toNat + 2 * (w_n589 x).toNat + 2 * (w_n592 x).toNat + 4 * (w_n578 x).toNat + 4 * (w_n581 x).toNat + 4 * (w_n584 x).toNat + 4 * (w_n587 x).toNat + 4 * (w_n590 x).toNat + 4 * (w_n593 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s219 (x : Nat → Bool) : I_t219 x = pc x 127 48 := by
  have hl := s211 x
  have hr := s218 x
  have : pc x 127 48 = pc x 127 24 + pc x 151 24 := pc_add x 127 24 24
  unfold I_t219
  omega
def I_b220 (x : Nat → Bool) : Nat := 0 + (x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat
theorem b220 (x : Nat → Bool) : I_b220 x = (x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat := by
  unfold I_b220
  omega
def I_t220 (x : Nat → Bool) : Nat := I_b220 x
theorem t220 (x : Nat → Bool) : I_t220 x = (w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat := by
  have hs : ((I_b220 x) + ((x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat)) = (((x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat) + ((w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat)) := (add_eq (b220 x) (e204 x))
  have e1 : ((I_b220 x) + ((x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat)) = (I_t220 x) + ((x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat) := by unfold I_t220; ac_rfl
  have e2 : (((x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat) + ((w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat)) = ((w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat) + ((x 121).toNat + (x 122).toNat + (x 123).toNat + (x 124).toNat + (x 125).toNat + (x 126).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s220 (x : Nat → Bool) : I_t220 x = pc x 121 6 := rfl
def I_b221 (x : Nat → Bool) : Nat := 0 + (x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat
theorem b221 (x : Nat → Bool) : I_b221 x = (x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat := by
  unfold I_b221
  omega
def I_t221 (x : Nat → Bool) : Nat := I_b221 x
theorem t221 (x : Nat → Bool) : I_t221 x = (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat := by
  have hs : ((I_b221 x) + ((x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat)) = (((x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat) + ((w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat)) := (add_eq (b221 x) (e205 x))
  have e1 : ((I_b221 x) + ((x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat)) = (I_t221 x) + ((x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat) := by unfold I_t221; ac_rfl
  have e2 : (((x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat) + ((w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat)) = ((w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat) + ((x 115).toNat + (x 116).toNat + (x 117).toNat + (x 118).toNat + (x 119).toNat + (x 120).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s221 (x : Nat → Bool) : I_t221 x = pc x 115 6 := rfl
def I_t222 (x : Nat → Bool) : Nat := I_t220 x + I_t221 x
theorem t222 (x : Nat → Bool) : I_t222 x = (w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat + (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat := by
  have hs : ((I_t220 x) + (I_t221 x)) = (((w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat) + ((w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat)) := (add_eq (t220 x) (t221 x))
  have e1 : ((I_t220 x) + (I_t221 x)) = I_t222 x := by unfold I_t222; ac_rfl
  have e2 : (((w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat) + ((w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat)) = (w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat + (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s222 (x : Nat → Bool) : I_t222 x = pc x 115 12 := by
  have hl := s220 x
  have hr := s221 x
  have : pc x 115 12 = pc x 115 6 + pc x 121 6 := pc_add x 115 6 6
  unfold I_t222
  omega
def I_b223 (x : Nat → Bool) : Nat := 0 + (x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat
theorem b223 (x : Nat → Bool) : I_b223 x = (x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat := by
  unfold I_b223
  omega
def I_t223 (x : Nat → Bool) : Nat := I_b223 x
theorem t223 (x : Nat → Bool) : I_t223 x = (w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat := by
  have hs : ((I_b223 x) + ((x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat)) = (((x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat) + ((w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat)) := (add_eq (b223 x) (e206 x))
  have e1 : ((I_b223 x) + ((x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat)) = (I_t223 x) + ((x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat) := by unfold I_t223; ac_rfl
  have e2 : (((x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat) + ((w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat)) = ((w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat) + ((x 103).toNat + (x 104).toNat + (x 105).toNat + (x 106).toNat + (x 107).toNat + (x 108).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s223 (x : Nat → Bool) : I_t223 x = pc x 103 6 := rfl
def I_b224 (x : Nat → Bool) : Nat := 0 + (x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat
theorem b224 (x : Nat → Bool) : I_b224 x = (x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat := by
  unfold I_b224
  omega
def I_t224 (x : Nat → Bool) : Nat := I_b224 x
theorem t224 (x : Nat → Bool) : I_t224 x = (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat := by
  have hs : ((I_b224 x) + ((x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat)) = (((x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat) + ((w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat)) := (add_eq (b224 x) (e207 x))
  have e1 : ((I_b224 x) + ((x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat)) = (I_t224 x) + ((x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat) := by unfold I_t224; ac_rfl
  have e2 : (((x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat) + ((w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat)) = ((w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat) + ((x 109).toNat + (x 110).toNat + (x 111).toNat + (x 112).toNat + (x 113).toNat + (x 114).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s224 (x : Nat → Bool) : I_t224 x = pc x 109 6 := rfl
def I_t225 (x : Nat → Bool) : Nat := I_t223 x + I_t224 x
theorem t225 (x : Nat → Bool) : I_t225 x = (w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat + (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat := by
  have hs : ((I_t223 x) + (I_t224 x)) = (((w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat) + ((w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat)) := (add_eq (t223 x) (t224 x))
  have e1 : ((I_t223 x) + (I_t224 x)) = I_t225 x := by unfold I_t225; ac_rfl
  have e2 : (((w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat) + ((w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat)) = (w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat + (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s225 (x : Nat → Bool) : I_t225 x = pc x 103 12 := by
  have hl := s223 x
  have hr := s224 x
  have : pc x 103 12 = pc x 103 6 + pc x 109 6 := pc_add x 103 6 6
  unfold I_t225
  omega
def I_t226 (x : Nat → Bool) : Nat := I_t222 x + I_t225 x
theorem t226 (x : Nat → Bool) : I_t226 x = (w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat + (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat + (w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat + (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat := by
  have hs : ((I_t222 x) + (I_t225 x)) = (((w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat + (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat) + ((w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat + (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat)) := (add_eq (t222 x) (t225 x))
  have e1 : ((I_t222 x) + (I_t225 x)) = I_t226 x := by unfold I_t226; ac_rfl
  have e2 : (((w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat + (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat) + ((w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat + (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat)) = (w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat + (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat + (w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat + (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s226 (x : Nat → Bool) : I_t226 x = pc x 103 24 := by
  have hl := s222 x
  have hr := s225 x
  have : pc x 103 24 = pc x 103 12 + pc x 115 12 := pc_add x 103 12 12
  unfold I_t226
  omega
def I_b227 (x : Nat → Bool) : Nat := 0 + (x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat
theorem b227 (x : Nat → Bool) : I_b227 x = (x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat := by
  unfold I_b227
  omega
def I_t227 (x : Nat → Bool) : Nat := I_b227 x
theorem t227 (x : Nat → Bool) : I_t227 x = (w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat := by
  have hs : ((I_b227 x) + ((x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat)) = (((x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat) + ((w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat)) := (add_eq (b227 x) (e208 x))
  have e1 : ((I_b227 x) + ((x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat)) = (I_t227 x) + ((x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat) := by unfold I_t227; ac_rfl
  have e2 : (((x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat) + ((w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat)) = ((w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat) + ((x 79).toNat + (x 80).toNat + (x 81).toNat + (x 82).toNat + (x 83).toNat + (x 84).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s227 (x : Nat → Bool) : I_t227 x = pc x 79 6 := rfl
def I_b228 (x : Nat → Bool) : Nat := 0 + (x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat
theorem b228 (x : Nat → Bool) : I_b228 x = (x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat := by
  unfold I_b228
  omega
def I_t228 (x : Nat → Bool) : Nat := I_b228 x
theorem t228 (x : Nat → Bool) : I_t228 x = (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat := by
  have hs : ((I_b228 x) + ((x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat)) = (((x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat) + ((w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat)) := (add_eq (b228 x) (e209 x))
  have e1 : ((I_b228 x) + ((x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat)) = (I_t228 x) + ((x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat) := by unfold I_t228; ac_rfl
  have e2 : (((x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat) + ((w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat)) = ((w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat) + ((x 85).toNat + (x 86).toNat + (x 87).toNat + (x 88).toNat + (x 89).toNat + (x 90).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s228 (x : Nat → Bool) : I_t228 x = pc x 85 6 := rfl
def I_t229 (x : Nat → Bool) : Nat := I_t227 x + I_t228 x
theorem t229 (x : Nat → Bool) : I_t229 x = (w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat + (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat := by
  have hs : ((I_t227 x) + (I_t228 x)) = (((w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat) + ((w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat)) := (add_eq (t227 x) (t228 x))
  have e1 : ((I_t227 x) + (I_t228 x)) = I_t229 x := by unfold I_t229; ac_rfl
  have e2 : (((w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat) + ((w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat)) = (w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat + (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s229 (x : Nat → Bool) : I_t229 x = pc x 79 12 := by
  have hl := s227 x
  have hr := s228 x
  have : pc x 79 12 = pc x 79 6 + pc x 85 6 := pc_add x 79 6 6
  unfold I_t229
  omega
def I_b230 (x : Nat → Bool) : Nat := 0 + (x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat
theorem b230 (x : Nat → Bool) : I_b230 x = (x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat := by
  unfold I_b230
  omega
def I_t230 (x : Nat → Bool) : Nat := I_b230 x
theorem t230 (x : Nat → Bool) : I_t230 x = (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat := by
  have hs : ((I_b230 x) + ((x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat)) = (((x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat) + ((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat)) := (add_eq (b230 x) (e210 x))
  have e1 : ((I_b230 x) + ((x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat)) = (I_t230 x) + ((x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat) := by unfold I_t230; ac_rfl
  have e2 : (((x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat) + ((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat)) = ((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat) + ((x 91).toNat + (x 92).toNat + (x 93).toNat + (x 94).toNat + (x 95).toNat + (x 96).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s230 (x : Nat → Bool) : I_t230 x = pc x 91 6 := rfl
def I_b231 (x : Nat → Bool) : Nat := 0 + (x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat
theorem b231 (x : Nat → Bool) : I_b231 x = (x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat := by
  unfold I_b231
  omega
def I_t231 (x : Nat → Bool) : Nat := I_b231 x
theorem t231 (x : Nat → Bool) : I_t231 x = (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat := by
  have hs : ((I_b231 x) + ((x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat)) = (((x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat) + ((w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat)) := (add_eq (b231 x) (e211 x))
  have e1 : ((I_b231 x) + ((x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat)) = (I_t231 x) + ((x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat) := by unfold I_t231; ac_rfl
  have e2 : (((x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat) + ((w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat)) = ((w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat) + ((x 97).toNat + (x 98).toNat + (x 99).toNat + (x 100).toNat + (x 101).toNat + (x 102).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s231 (x : Nat → Bool) : I_t231 x = pc x 97 6 := rfl
def I_t232 (x : Nat → Bool) : Nat := I_t230 x + I_t231 x
theorem t232 (x : Nat → Bool) : I_t232 x = (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat := by
  have hs : ((I_t230 x) + (I_t231 x)) = (((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat) + ((w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat)) := (add_eq (t230 x) (t231 x))
  have e1 : ((I_t230 x) + (I_t231 x)) = I_t232 x := by unfold I_t232; ac_rfl
  have e2 : (((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat) + ((w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat)) = (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s232 (x : Nat → Bool) : I_t232 x = pc x 91 12 := by
  have hl := s230 x
  have hr := s231 x
  have : pc x 91 12 = pc x 91 6 + pc x 97 6 := pc_add x 91 6 6
  unfold I_t232
  omega
def I_t233 (x : Nat → Bool) : Nat := I_t229 x + I_t232 x
theorem t233 (x : Nat → Bool) : I_t233 x = (w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat + (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat + (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat := by
  have hs : ((I_t229 x) + (I_t232 x)) = (((w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat + (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat) + ((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat)) := (add_eq (t229 x) (t232 x))
  have e1 : ((I_t229 x) + (I_t232 x)) = I_t233 x := by unfold I_t233; ac_rfl
  have e2 : (((w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat + (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat) + ((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat)) = (w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat + (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat + (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s233 (x : Nat → Bool) : I_t233 x = pc x 79 24 := by
  have hl := s229 x
  have hr := s232 x
  have : pc x 79 24 = pc x 79 12 + pc x 91 12 := pc_add x 79 12 12
  unfold I_t233
  omega
def I_t234 (x : Nat → Bool) : Nat := I_t226 x + I_t233 x
theorem t234 (x : Nat → Bool) : I_t234 x = (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat + (w_n633 x).toNat + 2 * (w_n634 x).toNat + 4 * (w_n635 x).toNat + 2 * (w_n636 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n638 x).toNat + 4 * (w_n639 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n641 x).toNat := by
  have hs : (((((I_t226 x) + (I_t233 x)) + ((w_n609 x).toNat + (w_n612 x).toNat + (w_n615 x).toNat + (w_n618 x).toNat + (w_n621 x).toNat + (w_n624 x).toNat)) + (2 * (w_n610 x).toNat + 2 * (w_n613 x).toNat + 2 * (w_n616 x).toNat + 2 * (w_n619 x).toNat + 2 * (w_n622 x).toNat + 2 * (w_n625 x).toNat)) + (4 * (w_n611 x).toNat + 4 * (w_n614 x).toNat + 4 * (w_n617 x).toNat + 4 * (w_n620 x).toNat + 4 * (w_n623 x).toNat + 4 * (w_n626 x).toNat)) = ((((((w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat + (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat + (w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat + (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat) + ((w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat + (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat + (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat)) + ((w_n633 x).toNat + 2 * (w_n634 x).toNat + 4 * (w_n635 x).toNat)) + (2 * (w_n636 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n638 x).toNat)) + (4 * (w_n639 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n641 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t226 x) (t233 x)) (e212 x)) (e213 x)) (e214 x))
  have e1 : (((((I_t226 x) + (I_t233 x)) + ((w_n609 x).toNat + (w_n612 x).toNat + (w_n615 x).toNat + (w_n618 x).toNat + (w_n621 x).toNat + (w_n624 x).toNat)) + (2 * (w_n610 x).toNat + 2 * (w_n613 x).toNat + 2 * (w_n616 x).toNat + 2 * (w_n619 x).toNat + 2 * (w_n622 x).toNat + 2 * (w_n625 x).toNat)) + (4 * (w_n611 x).toNat + 4 * (w_n614 x).toNat + 4 * (w_n617 x).toNat + 4 * (w_n620 x).toNat + 4 * (w_n623 x).toNat + 4 * (w_n626 x).toNat)) = (I_t234 x) + ((w_n609 x).toNat + (w_n612 x).toNat + (w_n615 x).toNat + (w_n618 x).toNat + (w_n621 x).toNat + (w_n624 x).toNat + 2 * (w_n610 x).toNat + 2 * (w_n613 x).toNat + 2 * (w_n616 x).toNat + 2 * (w_n619 x).toNat + 2 * (w_n622 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n611 x).toNat + 4 * (w_n614 x).toNat + 4 * (w_n617 x).toNat + 4 * (w_n620 x).toNat + 4 * (w_n623 x).toNat + 4 * (w_n626 x).toNat) := by unfold I_t234; ac_rfl
  have e2 : ((((((w_n609 x).toNat + 2 * (w_n610 x).toNat + 4 * (w_n611 x).toNat + (w_n612 x).toNat + 2 * (w_n613 x).toNat + 4 * (w_n614 x).toNat + (w_n615 x).toNat + 2 * (w_n616 x).toNat + 4 * (w_n617 x).toNat + (w_n618 x).toNat + 2 * (w_n619 x).toNat + 4 * (w_n620 x).toNat) + ((w_n621 x).toNat + 2 * (w_n622 x).toNat + 4 * (w_n623 x).toNat + (w_n624 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n626 x).toNat + (w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat)) + ((w_n633 x).toNat + 2 * (w_n634 x).toNat + 4 * (w_n635 x).toNat)) + (2 * (w_n636 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n638 x).toNat)) + (4 * (w_n639 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n641 x).toNat)) = ((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat + (w_n633 x).toNat + 2 * (w_n634 x).toNat + 4 * (w_n635 x).toNat + 2 * (w_n636 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n638 x).toNat + 4 * (w_n639 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n641 x).toNat) + ((w_n609 x).toNat + (w_n612 x).toNat + (w_n615 x).toNat + (w_n618 x).toNat + (w_n621 x).toNat + (w_n624 x).toNat + 2 * (w_n610 x).toNat + 2 * (w_n613 x).toNat + 2 * (w_n616 x).toNat + 2 * (w_n619 x).toNat + 2 * (w_n622 x).toNat + 2 * (w_n625 x).toNat + 4 * (w_n611 x).toNat + 4 * (w_n614 x).toNat + 4 * (w_n617 x).toNat + 4 * (w_n620 x).toNat + 4 * (w_n623 x).toNat + 4 * (w_n626 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s234 (x : Nat → Bool) : I_t234 x = pc x 79 48 := by
  have hl := s226 x
  have hr := s233 x
  have : pc x 79 48 = pc x 79 24 + pc x 103 24 := pc_add x 79 24 24
  unfold I_t234
  omega
def I_t235 (x : Nat → Bool) : Nat := I_t219 x + I_t234 x
theorem t235 (x : Nat → Bool) : I_t235 x = 16 * (w_n608 x).toNat + 2 * (w_n634 x).toNat + 2 * (w_n636 x).toNat + 16 * (w_n641 x).toNat + (w_n642 x).toNat + 2 * (w_n643 x).toNat + 2 * (w_n645 x).toNat + 4 * (w_n648 x).toNat + 16 * (w_n650 x).toNat + 4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 16 * (w_n653 x).toNat + 8 * (w_n654 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n656 x).toNat := by
  have hs : (((((((I_t219 x) + (I_t234 x)) + ((w_n594 x).toNat + (w_n597 x).toNat + (w_n600 x).toNat + (w_n627 x).toNat + (w_n630 x).toNat + (w_n633 x).toNat)) + (2 * (w_n595 x).toNat + 2 * (w_n598 x).toNat + 2 * (w_n601 x).toNat + 2 * (w_n603 x).toNat + 2 * (w_n628 x).toNat + 2 * (w_n631 x).toNat)) + (4 * (w_n596 x).toNat + 4 * (w_n599 x).toNat + 4 * (w_n602 x).toNat + 4 * (w_n604 x).toNat + 4 * (w_n606 x).toNat + 4 * (w_n629 x).toNat)) + (4 * (w_n632 x).toNat + 4 * (w_n635 x).toNat + 4 * (w_n637 x).toNat + 4 * (w_n639 x).toNat + 4 * (w_n644 x).toNat + 4 * (w_n646 x).toNat)) + (8 * (w_n605 x).toNat + 8 * (w_n607 x).toNat + 8 * (w_n638 x).toNat + 8 * (w_n640 x).toNat + 8 * (w_n647 x).toNat + 8 * (w_n649 x).toNat)) = ((((((((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat + (w_n600 x).toNat + 2 * (w_n601 x).toNat + 4 * (w_n602 x).toNat + 2 * (w_n603 x).toNat + 4 * (w_n604 x).toNat + 8 * (w_n605 x).toNat + 4 * (w_n606 x).toNat + 8 * (w_n607 x).toNat + 16 * (w_n608 x).toNat) + ((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat + (w_n633 x).toNat + 2 * (w_n634 x).toNat + 4 * (w_n635 x).toNat + 2 * (w_n636 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n638 x).toNat + 4 * (w_n639 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n641 x).toNat)) + ((w_n642 x).toNat + 2 * (w_n643 x).toNat + 4 * (w_n644 x).toNat)) + (2 * (w_n645 x).toNat + 4 * (w_n646 x).toNat + 8 * (w_n647 x).toNat)) + (4 * (w_n648 x).toNat + 8 * (w_n649 x).toNat + 16 * (w_n650 x).toNat)) + (4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 16 * (w_n653 x).toNat)) + (8 * (w_n654 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n656 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t219 x) (t234 x)) (e215 x)) (e216 x)) (e217 x)) (e218 x)) (e219 x))
  have e1 : (((((((I_t219 x) + (I_t234 x)) + ((w_n594 x).toNat + (w_n597 x).toNat + (w_n600 x).toNat + (w_n627 x).toNat + (w_n630 x).toNat + (w_n633 x).toNat)) + (2 * (w_n595 x).toNat + 2 * (w_n598 x).toNat + 2 * (w_n601 x).toNat + 2 * (w_n603 x).toNat + 2 * (w_n628 x).toNat + 2 * (w_n631 x).toNat)) + (4 * (w_n596 x).toNat + 4 * (w_n599 x).toNat + 4 * (w_n602 x).toNat + 4 * (w_n604 x).toNat + 4 * (w_n606 x).toNat + 4 * (w_n629 x).toNat)) + (4 * (w_n632 x).toNat + 4 * (w_n635 x).toNat + 4 * (w_n637 x).toNat + 4 * (w_n639 x).toNat + 4 * (w_n644 x).toNat + 4 * (w_n646 x).toNat)) + (8 * (w_n605 x).toNat + 8 * (w_n607 x).toNat + 8 * (w_n638 x).toNat + 8 * (w_n640 x).toNat + 8 * (w_n647 x).toNat + 8 * (w_n649 x).toNat)) = (I_t235 x) + ((w_n594 x).toNat + (w_n597 x).toNat + (w_n600 x).toNat + (w_n627 x).toNat + (w_n630 x).toNat + (w_n633 x).toNat + 2 * (w_n595 x).toNat + 2 * (w_n598 x).toNat + 2 * (w_n601 x).toNat + 2 * (w_n603 x).toNat + 2 * (w_n628 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n596 x).toNat + 4 * (w_n599 x).toNat + 4 * (w_n602 x).toNat + 4 * (w_n604 x).toNat + 4 * (w_n606 x).toNat + 4 * (w_n629 x).toNat + 4 * (w_n632 x).toNat + 4 * (w_n635 x).toNat + 4 * (w_n637 x).toNat + 4 * (w_n639 x).toNat + 4 * (w_n644 x).toNat + 4 * (w_n646 x).toNat + 8 * (w_n605 x).toNat + 8 * (w_n607 x).toNat + 8 * (w_n638 x).toNat + 8 * (w_n640 x).toNat + 8 * (w_n647 x).toNat + 8 * (w_n649 x).toNat) := by unfold I_t235; ac_rfl
  have e2 : ((((((((w_n594 x).toNat + 2 * (w_n595 x).toNat + 4 * (w_n596 x).toNat + (w_n597 x).toNat + 2 * (w_n598 x).toNat + 4 * (w_n599 x).toNat + (w_n600 x).toNat + 2 * (w_n601 x).toNat + 4 * (w_n602 x).toNat + 2 * (w_n603 x).toNat + 4 * (w_n604 x).toNat + 8 * (w_n605 x).toNat + 4 * (w_n606 x).toNat + 8 * (w_n607 x).toNat + 16 * (w_n608 x).toNat) + ((w_n627 x).toNat + 2 * (w_n628 x).toNat + 4 * (w_n629 x).toNat + (w_n630 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n632 x).toNat + (w_n633 x).toNat + 2 * (w_n634 x).toNat + 4 * (w_n635 x).toNat + 2 * (w_n636 x).toNat + 4 * (w_n637 x).toNat + 8 * (w_n638 x).toNat + 4 * (w_n639 x).toNat + 8 * (w_n640 x).toNat + 16 * (w_n641 x).toNat)) + ((w_n642 x).toNat + 2 * (w_n643 x).toNat + 4 * (w_n644 x).toNat)) + (2 * (w_n645 x).toNat + 4 * (w_n646 x).toNat + 8 * (w_n647 x).toNat)) + (4 * (w_n648 x).toNat + 8 * (w_n649 x).toNat + 16 * (w_n650 x).toNat)) + (4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 16 * (w_n653 x).toNat)) + (8 * (w_n654 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n656 x).toNat)) = (16 * (w_n608 x).toNat + 2 * (w_n634 x).toNat + 2 * (w_n636 x).toNat + 16 * (w_n641 x).toNat + (w_n642 x).toNat + 2 * (w_n643 x).toNat + 2 * (w_n645 x).toNat + 4 * (w_n648 x).toNat + 16 * (w_n650 x).toNat + 4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 16 * (w_n653 x).toNat + 8 * (w_n654 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n656 x).toNat) + ((w_n594 x).toNat + (w_n597 x).toNat + (w_n600 x).toNat + (w_n627 x).toNat + (w_n630 x).toNat + (w_n633 x).toNat + 2 * (w_n595 x).toNat + 2 * (w_n598 x).toNat + 2 * (w_n601 x).toNat + 2 * (w_n603 x).toNat + 2 * (w_n628 x).toNat + 2 * (w_n631 x).toNat + 4 * (w_n596 x).toNat + 4 * (w_n599 x).toNat + 4 * (w_n602 x).toNat + 4 * (w_n604 x).toNat + 4 * (w_n606 x).toNat + 4 * (w_n629 x).toNat + 4 * (w_n632 x).toNat + 4 * (w_n635 x).toNat + 4 * (w_n637 x).toNat + 4 * (w_n639 x).toNat + 4 * (w_n644 x).toNat + 4 * (w_n646 x).toNat + 8 * (w_n605 x).toNat + 8 * (w_n607 x).toNat + 8 * (w_n638 x).toNat + 8 * (w_n640 x).toNat + 8 * (w_n647 x).toNat + 8 * (w_n649 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s235 (x : Nat → Bool) : I_t235 x = pc x 79 96 := by
  have hl := s219 x
  have hr := s234 x
  have : pc x 79 96 = pc x 79 48 + pc x 127 48 := pc_add x 79 48 48
  unfold I_t235
  omega
def I_b236 (x : Nat → Bool) : Nat := 0 + (x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat
theorem b236 (x : Nat → Bool) : I_b236 x = (x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat := by
  unfold I_b236
  omega
def I_t236 (x : Nat → Bool) : Nat := I_b236 x
theorem t236 (x : Nat → Bool) : I_t236 x = (w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat := by
  have hs : ((I_b236 x) + ((x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat)) = (((x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat) + ((w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat)) := (add_eq (b236 x) (e220 x))
  have e1 : ((I_b236 x) + ((x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat)) = (I_t236 x) + ((x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat) := by unfold I_t236; ac_rfl
  have e2 : (((x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat) + ((w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat)) = ((w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat) + ((x 205).toNat + (x 206).toNat + (x 207).toNat + (x 208).toNat + (x 209).toNat + (x 210).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s236 (x : Nat → Bool) : I_t236 x = pc x 205 6 := rfl
def I_b237 (x : Nat → Bool) : Nat := 0 + (x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat
theorem b237 (x : Nat → Bool) : I_b237 x = (x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat := by
  unfold I_b237
  omega
def I_t237 (x : Nat → Bool) : Nat := I_b237 x
theorem t237 (x : Nat → Bool) : I_t237 x = (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat := by
  have hs : ((I_b237 x) + ((x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat)) = (((x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat) + ((w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat)) := (add_eq (b237 x) (e221 x))
  have e1 : ((I_b237 x) + ((x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat)) = (I_t237 x) + ((x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat) := by unfold I_t237; ac_rfl
  have e2 : (((x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat) + ((w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat)) = ((w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat) + ((x 199).toNat + (x 200).toNat + (x 201).toNat + (x 202).toNat + (x 203).toNat + (x 204).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s237 (x : Nat → Bool) : I_t237 x = pc x 199 6 := rfl
def I_t238 (x : Nat → Bool) : Nat := I_t236 x + I_t237 x
theorem t238 (x : Nat → Bool) : I_t238 x = (w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat + (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat := by
  have hs : ((I_t236 x) + (I_t237 x)) = (((w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat) + ((w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat)) := (add_eq (t236 x) (t237 x))
  have e1 : ((I_t236 x) + (I_t237 x)) = I_t238 x := by unfold I_t238; ac_rfl
  have e2 : (((w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat) + ((w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat)) = (w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat + (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s238 (x : Nat → Bool) : I_t238 x = pc x 199 12 := by
  have hl := s236 x
  have hr := s237 x
  have : pc x 199 12 = pc x 199 6 + pc x 205 6 := pc_add x 199 6 6
  unfold I_t238
  omega
def I_b239 (x : Nat → Bool) : Nat := 0 + (x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat
theorem b239 (x : Nat → Bool) : I_b239 x = (x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat := by
  unfold I_b239
  omega
def I_t239 (x : Nat → Bool) : Nat := I_b239 x
theorem t239 (x : Nat → Bool) : I_t239 x = (w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat := by
  have hs : ((I_b239 x) + ((x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat)) = (((x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat) + ((w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat)) := (add_eq (b239 x) (e222 x))
  have e1 : ((I_b239 x) + ((x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat)) = (I_t239 x) + ((x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat) := by unfold I_t239; ac_rfl
  have e2 : (((x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat) + ((w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat)) = ((w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat) + ((x 217).toNat + (x 218).toNat + (x 219).toNat + (x 220).toNat + (x 221).toNat + (x 222).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s239 (x : Nat → Bool) : I_t239 x = pc x 217 6 := rfl
def I_b240 (x : Nat → Bool) : Nat := 0 + (x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat
theorem b240 (x : Nat → Bool) : I_b240 x = (x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat := by
  unfold I_b240
  omega
def I_t240 (x : Nat → Bool) : Nat := I_b240 x
theorem t240 (x : Nat → Bool) : I_t240 x = (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat := by
  have hs : ((I_b240 x) + ((x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat)) = (((x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat) + ((w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat)) := (add_eq (b240 x) (e223 x))
  have e1 : ((I_b240 x) + ((x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat)) = (I_t240 x) + ((x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat) := by unfold I_t240; ac_rfl
  have e2 : (((x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat) + ((w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat)) = ((w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat) + ((x 211).toNat + (x 212).toNat + (x 213).toNat + (x 214).toNat + (x 215).toNat + (x 216).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s240 (x : Nat → Bool) : I_t240 x = pc x 211 6 := rfl
def I_t241 (x : Nat → Bool) : Nat := I_t239 x + I_t240 x
theorem t241 (x : Nat → Bool) : I_t241 x = (w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat + (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat := by
  have hs : ((I_t239 x) + (I_t240 x)) = (((w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat) + ((w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat)) := (add_eq (t239 x) (t240 x))
  have e1 : ((I_t239 x) + (I_t240 x)) = I_t241 x := by unfold I_t241; ac_rfl
  have e2 : (((w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat) + ((w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat)) = (w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat + (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s241 (x : Nat → Bool) : I_t241 x = pc x 211 12 := by
  have hl := s239 x
  have hr := s240 x
  have : pc x 211 12 = pc x 211 6 + pc x 217 6 := pc_add x 211 6 6
  unfold I_t241
  omega
def I_t242 (x : Nat → Bool) : Nat := I_t238 x + I_t241 x
theorem t242 (x : Nat → Bool) : I_t242 x = (w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat + (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat + (w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat + (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat := by
  have hs : ((I_t238 x) + (I_t241 x)) = (((w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat + (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat) + ((w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat + (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat)) := (add_eq (t238 x) (t241 x))
  have e1 : ((I_t238 x) + (I_t241 x)) = I_t242 x := by unfold I_t242; ac_rfl
  have e2 : (((w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat + (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat) + ((w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat + (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat)) = (w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat + (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat + (w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat + (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s242 (x : Nat → Bool) : I_t242 x = pc x 199 24 := by
  have hl := s238 x
  have hr := s241 x
  have : pc x 199 24 = pc x 199 12 + pc x 211 12 := pc_add x 199 12 12
  unfold I_t242
  omega
def I_b243 (x : Nat → Bool) : Nat := 0 + (x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat
theorem b243 (x : Nat → Bool) : I_b243 x = (x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat := by
  unfold I_b243
  omega
def I_t243 (x : Nat → Bool) : Nat := I_b243 x
theorem t243 (x : Nat → Bool) : I_t243 x = (w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat := by
  have hs : ((I_b243 x) + ((x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat)) = (((x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat) + ((w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat)) := (add_eq (b243 x) (e224 x))
  have e1 : ((I_b243 x) + ((x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat)) = (I_t243 x) + ((x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat) := by unfold I_t243; ac_rfl
  have e2 : (((x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat) + ((w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat)) = ((w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat) + ((x 175).toNat + (x 176).toNat + (x 177).toNat + (x 178).toNat + (x 179).toNat + (x 180).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s243 (x : Nat → Bool) : I_t243 x = pc x 175 6 := rfl
def I_b244 (x : Nat → Bool) : Nat := 0 + (x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat
theorem b244 (x : Nat → Bool) : I_b244 x = (x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat := by
  unfold I_b244
  omega
def I_t244 (x : Nat → Bool) : Nat := I_b244 x
theorem t244 (x : Nat → Bool) : I_t244 x = (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat := by
  have hs : ((I_b244 x) + ((x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat)) = (((x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat) + ((w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat)) := (add_eq (b244 x) (e225 x))
  have e1 : ((I_b244 x) + ((x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat)) = (I_t244 x) + ((x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat) := by unfold I_t244; ac_rfl
  have e2 : (((x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat) + ((w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat)) = ((w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat) + ((x 181).toNat + (x 182).toNat + (x 183).toNat + (x 184).toNat + (x 185).toNat + (x 186).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s244 (x : Nat → Bool) : I_t244 x = pc x 181 6 := rfl
def I_t245 (x : Nat → Bool) : Nat := I_t243 x + I_t244 x
theorem t245 (x : Nat → Bool) : I_t245 x = (w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat + (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat := by
  have hs : ((I_t243 x) + (I_t244 x)) = (((w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat) + ((w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat)) := (add_eq (t243 x) (t244 x))
  have e1 : ((I_t243 x) + (I_t244 x)) = I_t245 x := by unfold I_t245; ac_rfl
  have e2 : (((w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat) + ((w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat)) = (w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat + (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s245 (x : Nat → Bool) : I_t245 x = pc x 175 12 := by
  have hl := s243 x
  have hr := s244 x
  have : pc x 175 12 = pc x 175 6 + pc x 181 6 := pc_add x 175 6 6
  unfold I_t245
  omega
def I_b246 (x : Nat → Bool) : Nat := 0 + (x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat
theorem b246 (x : Nat → Bool) : I_b246 x = (x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat := by
  unfold I_b246
  omega
def I_t246 (x : Nat → Bool) : Nat := I_b246 x
theorem t246 (x : Nat → Bool) : I_t246 x = (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat := by
  have hs : ((I_b246 x) + ((x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat)) = (((x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat) + ((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat)) := (add_eq (b246 x) (e226 x))
  have e1 : ((I_b246 x) + ((x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat)) = (I_t246 x) + ((x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat) := by unfold I_t246; ac_rfl
  have e2 : (((x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat) + ((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat)) = ((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat) + ((x 187).toNat + (x 188).toNat + (x 189).toNat + (x 190).toNat + (x 191).toNat + (x 192).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s246 (x : Nat → Bool) : I_t246 x = pc x 187 6 := rfl
def I_b247 (x : Nat → Bool) : Nat := 0 + (x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat
theorem b247 (x : Nat → Bool) : I_b247 x = (x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat := by
  unfold I_b247
  omega
def I_t247 (x : Nat → Bool) : Nat := I_b247 x
theorem t247 (x : Nat → Bool) : I_t247 x = (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat := by
  have hs : ((I_b247 x) + ((x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat)) = (((x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat) + ((w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat)) := (add_eq (b247 x) (e227 x))
  have e1 : ((I_b247 x) + ((x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat)) = (I_t247 x) + ((x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat) := by unfold I_t247; ac_rfl
  have e2 : (((x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat) + ((w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat)) = ((w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat) + ((x 193).toNat + (x 194).toNat + (x 195).toNat + (x 196).toNat + (x 197).toNat + (x 198).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s247 (x : Nat → Bool) : I_t247 x = pc x 193 6 := rfl
def I_t248 (x : Nat → Bool) : Nat := I_t246 x + I_t247 x
theorem t248 (x : Nat → Bool) : I_t248 x = (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat := by
  have hs : ((I_t246 x) + (I_t247 x)) = (((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat) + ((w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat)) := (add_eq (t246 x) (t247 x))
  have e1 : ((I_t246 x) + (I_t247 x)) = I_t248 x := by unfold I_t248; ac_rfl
  have e2 : (((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat) + ((w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat)) = (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s248 (x : Nat → Bool) : I_t248 x = pc x 187 12 := by
  have hl := s246 x
  have hr := s247 x
  have : pc x 187 12 = pc x 187 6 + pc x 193 6 := pc_add x 187 6 6
  unfold I_t248
  omega
def I_t249 (x : Nat → Bool) : Nat := I_t245 x + I_t248 x
theorem t249 (x : Nat → Bool) : I_t249 x = (w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat + (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat + (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat := by
  have hs : ((I_t245 x) + (I_t248 x)) = (((w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat + (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat) + ((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat)) := (add_eq (t245 x) (t248 x))
  have e1 : ((I_t245 x) + (I_t248 x)) = I_t249 x := by unfold I_t249; ac_rfl
  have e2 : (((w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat + (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat) + ((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat)) = (w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat + (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat + (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s249 (x : Nat → Bool) : I_t249 x = pc x 175 24 := by
  have hl := s245 x
  have hr := s248 x
  have : pc x 175 24 = pc x 175 12 + pc x 187 12 := pc_add x 175 12 12
  unfold I_t249
  omega
def I_t250 (x : Nat → Bool) : Nat := I_t242 x + I_t249 x
theorem t250 (x : Nat → Bool) : I_t250 x = (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat + (w_n681 x).toNat + 2 * (w_n682 x).toNat + 4 * (w_n683 x).toNat + 2 * (w_n684 x).toNat + 4 * (w_n685 x).toNat + 8 * (w_n686 x).toNat + 4 * (w_n687 x).toNat + 8 * (w_n688 x).toNat + 16 * (w_n689 x).toNat := by
  have hs : (((((I_t242 x) + (I_t249 x)) + ((w_n657 x).toNat + (w_n660 x).toNat + (w_n663 x).toNat + (w_n666 x).toNat + (w_n669 x).toNat + (w_n672 x).toNat)) + (2 * (w_n658 x).toNat + 2 * (w_n661 x).toNat + 2 * (w_n664 x).toNat + 2 * (w_n667 x).toNat + 2 * (w_n670 x).toNat + 2 * (w_n673 x).toNat)) + (4 * (w_n659 x).toNat + 4 * (w_n662 x).toNat + 4 * (w_n665 x).toNat + 4 * (w_n668 x).toNat + 4 * (w_n671 x).toNat + 4 * (w_n674 x).toNat)) = ((((((w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat + (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat + (w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat + (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat) + ((w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat + (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat + (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat)) + ((w_n681 x).toNat + 2 * (w_n682 x).toNat + 4 * (w_n683 x).toNat)) + (2 * (w_n684 x).toNat + 4 * (w_n685 x).toNat + 8 * (w_n686 x).toNat)) + (4 * (w_n687 x).toNat + 8 * (w_n688 x).toNat + 16 * (w_n689 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t242 x) (t249 x)) (e228 x)) (e229 x)) (e230 x))
  have e1 : (((((I_t242 x) + (I_t249 x)) + ((w_n657 x).toNat + (w_n660 x).toNat + (w_n663 x).toNat + (w_n666 x).toNat + (w_n669 x).toNat + (w_n672 x).toNat)) + (2 * (w_n658 x).toNat + 2 * (w_n661 x).toNat + 2 * (w_n664 x).toNat + 2 * (w_n667 x).toNat + 2 * (w_n670 x).toNat + 2 * (w_n673 x).toNat)) + (4 * (w_n659 x).toNat + 4 * (w_n662 x).toNat + 4 * (w_n665 x).toNat + 4 * (w_n668 x).toNat + 4 * (w_n671 x).toNat + 4 * (w_n674 x).toNat)) = (I_t250 x) + ((w_n657 x).toNat + (w_n660 x).toNat + (w_n663 x).toNat + (w_n666 x).toNat + (w_n669 x).toNat + (w_n672 x).toNat + 2 * (w_n658 x).toNat + 2 * (w_n661 x).toNat + 2 * (w_n664 x).toNat + 2 * (w_n667 x).toNat + 2 * (w_n670 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n659 x).toNat + 4 * (w_n662 x).toNat + 4 * (w_n665 x).toNat + 4 * (w_n668 x).toNat + 4 * (w_n671 x).toNat + 4 * (w_n674 x).toNat) := by unfold I_t250; ac_rfl
  have e2 : ((((((w_n657 x).toNat + 2 * (w_n658 x).toNat + 4 * (w_n659 x).toNat + (w_n660 x).toNat + 2 * (w_n661 x).toNat + 4 * (w_n662 x).toNat + (w_n663 x).toNat + 2 * (w_n664 x).toNat + 4 * (w_n665 x).toNat + (w_n666 x).toNat + 2 * (w_n667 x).toNat + 4 * (w_n668 x).toNat) + ((w_n669 x).toNat + 2 * (w_n670 x).toNat + 4 * (w_n671 x).toNat + (w_n672 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n674 x).toNat + (w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat)) + ((w_n681 x).toNat + 2 * (w_n682 x).toNat + 4 * (w_n683 x).toNat)) + (2 * (w_n684 x).toNat + 4 * (w_n685 x).toNat + 8 * (w_n686 x).toNat)) + (4 * (w_n687 x).toNat + 8 * (w_n688 x).toNat + 16 * (w_n689 x).toNat)) = ((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat + (w_n681 x).toNat + 2 * (w_n682 x).toNat + 4 * (w_n683 x).toNat + 2 * (w_n684 x).toNat + 4 * (w_n685 x).toNat + 8 * (w_n686 x).toNat + 4 * (w_n687 x).toNat + 8 * (w_n688 x).toNat + 16 * (w_n689 x).toNat) + ((w_n657 x).toNat + (w_n660 x).toNat + (w_n663 x).toNat + (w_n666 x).toNat + (w_n669 x).toNat + (w_n672 x).toNat + 2 * (w_n658 x).toNat + 2 * (w_n661 x).toNat + 2 * (w_n664 x).toNat + 2 * (w_n667 x).toNat + 2 * (w_n670 x).toNat + 2 * (w_n673 x).toNat + 4 * (w_n659 x).toNat + 4 * (w_n662 x).toNat + 4 * (w_n665 x).toNat + 4 * (w_n668 x).toNat + 4 * (w_n671 x).toNat + 4 * (w_n674 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s250 (x : Nat → Bool) : I_t250 x = pc x 175 48 := by
  have hl := s242 x
  have hr := s249 x
  have : pc x 175 48 = pc x 175 24 + pc x 199 24 := pc_add x 175 24 24
  unfold I_t250
  omega
def I_b251 (x : Nat → Bool) : Nat := 0 + (x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat
theorem b251 (x : Nat → Bool) : I_b251 x = (x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat := by
  unfold I_b251
  omega
def I_t251 (x : Nat → Bool) : Nat := I_b251 x
theorem t251 (x : Nat → Bool) : I_t251 x = (w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat := by
  have hs : ((I_b251 x) + ((x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat)) = (((x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat) + ((w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat)) := (add_eq (b251 x) (e231 x))
  have e1 : ((I_b251 x) + ((x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat)) = (I_t251 x) + ((x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat) := by unfold I_t251; ac_rfl
  have e2 : (((x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat) + ((w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat)) = ((w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat) + ((x 247).toNat + (x 248).toNat + (x 249).toNat + (x 250).toNat + (x 251).toNat + (x 252).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s251 (x : Nat → Bool) : I_t251 x = pc x 247 6 := rfl
def I_b252 (x : Nat → Bool) : Nat := 0 + (x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat
theorem b252 (x : Nat → Bool) : I_b252 x = (x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat := by
  unfold I_b252
  omega
def I_t252 (x : Nat → Bool) : Nat := I_b252 x
theorem t252 (x : Nat → Bool) : I_t252 x = (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat := by
  have hs : ((I_b252 x) + ((x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat)) = (((x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat) + ((w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat)) := (add_eq (b252 x) (e232 x))
  have e1 : ((I_b252 x) + ((x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat)) = (I_t252 x) + ((x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat) := by unfold I_t252; ac_rfl
  have e2 : (((x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat) + ((w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat)) = ((w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat) + ((x 253).toNat + (x 254).toNat + (x 255).toNat + (x 256).toNat + (x 257).toNat + (x 258).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s252 (x : Nat → Bool) : I_t252 x = pc x 253 6 := rfl
def I_t253 (x : Nat → Bool) : Nat := I_t251 x + I_t252 x
theorem t253 (x : Nat → Bool) : I_t253 x = (w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat + (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat := by
  have hs : ((I_t251 x) + (I_t252 x)) = (((w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat) + ((w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat)) := (add_eq (t251 x) (t252 x))
  have e1 : ((I_t251 x) + (I_t252 x)) = I_t253 x := by unfold I_t253; ac_rfl
  have e2 : (((w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat) + ((w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat)) = (w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat + (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s253 (x : Nat → Bool) : I_t253 x = pc x 247 12 := by
  have hl := s251 x
  have hr := s252 x
  have : pc x 247 12 = pc x 247 6 + pc x 253 6 := pc_add x 247 6 6
  unfold I_t253
  omega
def I_b254 (x : Nat → Bool) : Nat := 0 + (x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat
theorem b254 (x : Nat → Bool) : I_b254 x = (x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat := by
  unfold I_b254
  omega
def I_t254 (x : Nat → Bool) : Nat := I_b254 x
theorem t254 (x : Nat → Bool) : I_t254 x = (w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat := by
  have hs : ((I_b254 x) + ((x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat)) = (((x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat) + ((w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat)) := (add_eq (b254 x) (e233 x))
  have e1 : ((I_b254 x) + ((x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat)) = (I_t254 x) + ((x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat) := by unfold I_t254; ac_rfl
  have e2 : (((x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat) + ((w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat)) = ((w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat) + ((x 259).toNat + (x 260).toNat + (x 261).toNat + (x 262).toNat + (x 263).toNat + (x 264).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s254 (x : Nat → Bool) : I_t254 x = pc x 259 6 := rfl
def I_b255 (x : Nat → Bool) : Nat := 0 + (x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat
theorem b255 (x : Nat → Bool) : I_b255 x = (x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat := by
  unfold I_b255
  omega
def I_t255 (x : Nat → Bool) : Nat := I_b255 x
theorem t255 (x : Nat → Bool) : I_t255 x = (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat := by
  have hs : ((I_b255 x) + ((x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat)) = (((x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat) + ((w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat)) := (add_eq (b255 x) (e234 x))
  have e1 : ((I_b255 x) + ((x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat)) = (I_t255 x) + ((x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat) := by unfold I_t255; ac_rfl
  have e2 : (((x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat) + ((w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat)) = ((w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat) + ((x 265).toNat + (x 266).toNat + (x 267).toNat + (x 268).toNat + (x 269).toNat + (x 270).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s255 (x : Nat → Bool) : I_t255 x = pc x 265 6 := rfl
def I_t256 (x : Nat → Bool) : Nat := I_t254 x + I_t255 x
theorem t256 (x : Nat → Bool) : I_t256 x = (w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat + (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat := by
  have hs : ((I_t254 x) + (I_t255 x)) = (((w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat) + ((w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat)) := (add_eq (t254 x) (t255 x))
  have e1 : ((I_t254 x) + (I_t255 x)) = I_t256 x := by unfold I_t256; ac_rfl
  have e2 : (((w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat) + ((w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat)) = (w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat + (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s256 (x : Nat → Bool) : I_t256 x = pc x 259 12 := by
  have hl := s254 x
  have hr := s255 x
  have : pc x 259 12 = pc x 259 6 + pc x 265 6 := pc_add x 259 6 6
  unfold I_t256
  omega
def I_t257 (x : Nat → Bool) : Nat := I_t253 x + I_t256 x
theorem t257 (x : Nat → Bool) : I_t257 x = (w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat + (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat + (w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat + (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat := by
  have hs : ((I_t253 x) + (I_t256 x)) = (((w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat + (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat) + ((w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat + (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat)) := (add_eq (t253 x) (t256 x))
  have e1 : ((I_t253 x) + (I_t256 x)) = I_t257 x := by unfold I_t257; ac_rfl
  have e2 : (((w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat + (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat) + ((w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat + (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat)) = (w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat + (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat + (w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat + (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s257 (x : Nat → Bool) : I_t257 x = pc x 247 24 := by
  have hl := s253 x
  have hr := s256 x
  have : pc x 247 24 = pc x 247 12 + pc x 259 12 := pc_add x 247 12 12
  unfold I_t257
  omega
def I_b258 (x : Nat → Bool) : Nat := 0 + (x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat
theorem b258 (x : Nat → Bool) : I_b258 x = (x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat := by
  unfold I_b258
  omega
def I_t258 (x : Nat → Bool) : Nat := I_b258 x
theorem t258 (x : Nat → Bool) : I_t258 x = (w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat := by
  have hs : ((I_b258 x) + ((x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat)) = (((x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat) + ((w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat)) := (add_eq (b258 x) (e235 x))
  have e1 : ((I_b258 x) + ((x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat)) = (I_t258 x) + ((x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat) := by unfold I_t258; ac_rfl
  have e2 : (((x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat) + ((w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat)) = ((w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat) + ((x 235).toNat + (x 236).toNat + (x 237).toNat + (x 238).toNat + (x 239).toNat + (x 240).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s258 (x : Nat → Bool) : I_t258 x = pc x 235 6 := rfl
def I_b259 (x : Nat → Bool) : Nat := 0 + (x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat
theorem b259 (x : Nat → Bool) : I_b259 x = (x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat := by
  unfold I_b259
  omega
def I_t259 (x : Nat → Bool) : Nat := I_b259 x
theorem t259 (x : Nat → Bool) : I_t259 x = (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat := by
  have hs : ((I_b259 x) + ((x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat)) = (((x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat) + ((w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat)) := (add_eq (b259 x) (e236 x))
  have e1 : ((I_b259 x) + ((x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat)) = (I_t259 x) + ((x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat) := by unfold I_t259; ac_rfl
  have e2 : (((x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat) + ((w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat)) = ((w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat) + ((x 241).toNat + (x 242).toNat + (x 243).toNat + (x 244).toNat + (x 245).toNat + (x 246).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s259 (x : Nat → Bool) : I_t259 x = pc x 241 6 := rfl
def I_t260 (x : Nat → Bool) : Nat := I_t258 x + I_t259 x
theorem t260 (x : Nat → Bool) : I_t260 x = (w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat + (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat := by
  have hs : ((I_t258 x) + (I_t259 x)) = (((w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat) + ((w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat)) := (add_eq (t258 x) (t259 x))
  have e1 : ((I_t258 x) + (I_t259 x)) = I_t260 x := by unfold I_t260; ac_rfl
  have e2 : (((w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat) + ((w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat)) = (w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat + (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s260 (x : Nat → Bool) : I_t260 x = pc x 235 12 := by
  have hl := s258 x
  have hr := s259 x
  have : pc x 235 12 = pc x 235 6 + pc x 241 6 := pc_add x 235 6 6
  unfold I_t260
  omega
def I_b261 (x : Nat → Bool) : Nat := 0 + (x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat
theorem b261 (x : Nat → Bool) : I_b261 x = (x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat := by
  unfold I_b261
  omega
def I_t261 (x : Nat → Bool) : Nat := I_b261 x
theorem t261 (x : Nat → Bool) : I_t261 x = (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat := by
  have hs : ((I_b261 x) + ((x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat)) = (((x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat) + ((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat)) := (add_eq (b261 x) (e237 x))
  have e1 : ((I_b261 x) + ((x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat)) = (I_t261 x) + ((x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat) := by unfold I_t261; ac_rfl
  have e2 : (((x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat) + ((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat)) = ((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat) + ((x 229).toNat + (x 230).toNat + (x 231).toNat + (x 232).toNat + (x 233).toNat + (x 234).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s261 (x : Nat → Bool) : I_t261 x = pc x 229 6 := rfl
def I_b262 (x : Nat → Bool) : Nat := 0 + (x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat
theorem b262 (x : Nat → Bool) : I_b262 x = (x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat := by
  unfold I_b262
  omega
def I_t262 (x : Nat → Bool) : Nat := I_b262 x
theorem t262 (x : Nat → Bool) : I_t262 x = (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat := by
  have hs : ((I_b262 x) + ((x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat)) = (((x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat) + ((w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat)) := (add_eq (b262 x) (e238 x))
  have e1 : ((I_b262 x) + ((x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat)) = (I_t262 x) + ((x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat) := by unfold I_t262; ac_rfl
  have e2 : (((x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat) + ((w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat)) = ((w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat) + ((x 223).toNat + (x 224).toNat + (x 225).toNat + (x 226).toNat + (x 227).toNat + (x 228).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s262 (x : Nat → Bool) : I_t262 x = pc x 223 6 := rfl
def I_t263 (x : Nat → Bool) : Nat := I_t261 x + I_t262 x
theorem t263 (x : Nat → Bool) : I_t263 x = (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat := by
  have hs : ((I_t261 x) + (I_t262 x)) = (((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat) + ((w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat)) := (add_eq (t261 x) (t262 x))
  have e1 : ((I_t261 x) + (I_t262 x)) = I_t263 x := by unfold I_t263; ac_rfl
  have e2 : (((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat) + ((w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat)) = (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s263 (x : Nat → Bool) : I_t263 x = pc x 223 12 := by
  have hl := s261 x
  have hr := s262 x
  have : pc x 223 12 = pc x 223 6 + pc x 229 6 := pc_add x 223 6 6
  unfold I_t263
  omega
def I_t264 (x : Nat → Bool) : Nat := I_t260 x + I_t263 x
theorem t264 (x : Nat → Bool) : I_t264 x = (w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat + (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat + (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat := by
  have hs : ((I_t260 x) + (I_t263 x)) = (((w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat + (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat) + ((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat)) := (add_eq (t260 x) (t263 x))
  have e1 : ((I_t260 x) + (I_t263 x)) = I_t264 x := by unfold I_t264; ac_rfl
  have e2 : (((w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat + (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat) + ((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat)) = (w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat + (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat + (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s264 (x : Nat → Bool) : I_t264 x = pc x 223 24 := by
  have hl := s260 x
  have hr := s263 x
  have : pc x 223 24 = pc x 223 12 + pc x 235 12 := pc_add x 223 12 12
  unfold I_t264
  omega
def I_t265 (x : Nat → Bool) : Nat := I_t257 x + I_t264 x
theorem t265 (x : Nat → Bool) : I_t265 x = (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat + (w_n714 x).toNat + 2 * (w_n715 x).toNat + 4 * (w_n716 x).toNat + 2 * (w_n717 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n719 x).toNat + 4 * (w_n720 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n722 x).toNat := by
  have hs : (((((I_t257 x) + (I_t264 x)) + ((w_n690 x).toNat + (w_n693 x).toNat + (w_n696 x).toNat + (w_n699 x).toNat + (w_n702 x).toNat + (w_n705 x).toNat)) + (2 * (w_n691 x).toNat + 2 * (w_n694 x).toNat + 2 * (w_n697 x).toNat + 2 * (w_n700 x).toNat + 2 * (w_n703 x).toNat + 2 * (w_n706 x).toNat)) + (4 * (w_n692 x).toNat + 4 * (w_n695 x).toNat + 4 * (w_n698 x).toNat + 4 * (w_n701 x).toNat + 4 * (w_n704 x).toNat + 4 * (w_n707 x).toNat)) = ((((((w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat + (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat + (w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat + (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat) + ((w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat + (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat + (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat)) + ((w_n714 x).toNat + 2 * (w_n715 x).toNat + 4 * (w_n716 x).toNat)) + (2 * (w_n717 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n719 x).toNat)) + (4 * (w_n720 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n722 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t257 x) (t264 x)) (e239 x)) (e240 x)) (e241 x))
  have e1 : (((((I_t257 x) + (I_t264 x)) + ((w_n690 x).toNat + (w_n693 x).toNat + (w_n696 x).toNat + (w_n699 x).toNat + (w_n702 x).toNat + (w_n705 x).toNat)) + (2 * (w_n691 x).toNat + 2 * (w_n694 x).toNat + 2 * (w_n697 x).toNat + 2 * (w_n700 x).toNat + 2 * (w_n703 x).toNat + 2 * (w_n706 x).toNat)) + (4 * (w_n692 x).toNat + 4 * (w_n695 x).toNat + 4 * (w_n698 x).toNat + 4 * (w_n701 x).toNat + 4 * (w_n704 x).toNat + 4 * (w_n707 x).toNat)) = (I_t265 x) + ((w_n690 x).toNat + (w_n693 x).toNat + (w_n696 x).toNat + (w_n699 x).toNat + (w_n702 x).toNat + (w_n705 x).toNat + 2 * (w_n691 x).toNat + 2 * (w_n694 x).toNat + 2 * (w_n697 x).toNat + 2 * (w_n700 x).toNat + 2 * (w_n703 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n692 x).toNat + 4 * (w_n695 x).toNat + 4 * (w_n698 x).toNat + 4 * (w_n701 x).toNat + 4 * (w_n704 x).toNat + 4 * (w_n707 x).toNat) := by unfold I_t265; ac_rfl
  have e2 : ((((((w_n690 x).toNat + 2 * (w_n691 x).toNat + 4 * (w_n692 x).toNat + (w_n693 x).toNat + 2 * (w_n694 x).toNat + 4 * (w_n695 x).toNat + (w_n696 x).toNat + 2 * (w_n697 x).toNat + 4 * (w_n698 x).toNat + (w_n699 x).toNat + 2 * (w_n700 x).toNat + 4 * (w_n701 x).toNat) + ((w_n702 x).toNat + 2 * (w_n703 x).toNat + 4 * (w_n704 x).toNat + (w_n705 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n707 x).toNat + (w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat)) + ((w_n714 x).toNat + 2 * (w_n715 x).toNat + 4 * (w_n716 x).toNat)) + (2 * (w_n717 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n719 x).toNat)) + (4 * (w_n720 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n722 x).toNat)) = ((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat + (w_n714 x).toNat + 2 * (w_n715 x).toNat + 4 * (w_n716 x).toNat + 2 * (w_n717 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n719 x).toNat + 4 * (w_n720 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n722 x).toNat) + ((w_n690 x).toNat + (w_n693 x).toNat + (w_n696 x).toNat + (w_n699 x).toNat + (w_n702 x).toNat + (w_n705 x).toNat + 2 * (w_n691 x).toNat + 2 * (w_n694 x).toNat + 2 * (w_n697 x).toNat + 2 * (w_n700 x).toNat + 2 * (w_n703 x).toNat + 2 * (w_n706 x).toNat + 4 * (w_n692 x).toNat + 4 * (w_n695 x).toNat + 4 * (w_n698 x).toNat + 4 * (w_n701 x).toNat + 4 * (w_n704 x).toNat + 4 * (w_n707 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s265 (x : Nat → Bool) : I_t265 x = pc x 223 48 := by
  have hl := s257 x
  have hr := s264 x
  have : pc x 223 48 = pc x 223 24 + pc x 247 24 := pc_add x 223 24 24
  unfold I_t265
  omega
def I_t266 (x : Nat → Bool) : Nat := I_t250 x + I_t265 x
theorem t266 (x : Nat → Bool) : I_t266 x = 16 * (w_n689 x).toNat + 2 * (w_n715 x).toNat + 2 * (w_n717 x).toNat + 16 * (w_n722 x).toNat + (w_n723 x).toNat + 2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n729 x).toNat + 16 * (w_n731 x).toNat + 4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat := by
  have hs : (((((((I_t250 x) + (I_t265 x)) + ((w_n675 x).toNat + (w_n678 x).toNat + (w_n681 x).toNat + (w_n708 x).toNat + (w_n711 x).toNat + (w_n714 x).toNat)) + (2 * (w_n676 x).toNat + 2 * (w_n679 x).toNat + 2 * (w_n682 x).toNat + 2 * (w_n684 x).toNat + 2 * (w_n709 x).toNat + 2 * (w_n712 x).toNat)) + (4 * (w_n677 x).toNat + 4 * (w_n680 x).toNat + 4 * (w_n683 x).toNat + 4 * (w_n685 x).toNat + 4 * (w_n687 x).toNat + 4 * (w_n710 x).toNat)) + (4 * (w_n713 x).toNat + 4 * (w_n716 x).toNat + 4 * (w_n718 x).toNat + 4 * (w_n720 x).toNat + 4 * (w_n725 x).toNat + 4 * (w_n727 x).toNat)) + (8 * (w_n686 x).toNat + 8 * (w_n688 x).toNat + 8 * (w_n719 x).toNat + 8 * (w_n721 x).toNat + 8 * (w_n728 x).toNat + 8 * (w_n730 x).toNat)) = ((((((((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat + (w_n681 x).toNat + 2 * (w_n682 x).toNat + 4 * (w_n683 x).toNat + 2 * (w_n684 x).toNat + 4 * (w_n685 x).toNat + 8 * (w_n686 x).toNat + 4 * (w_n687 x).toNat + 8 * (w_n688 x).toNat + 16 * (w_n689 x).toNat) + ((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat + (w_n714 x).toNat + 2 * (w_n715 x).toNat + 4 * (w_n716 x).toNat + 2 * (w_n717 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n719 x).toNat + 4 * (w_n720 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n722 x).toNat)) + ((w_n723 x).toNat + 2 * (w_n724 x).toNat + 4 * (w_n725 x).toNat)) + (2 * (w_n726 x).toNat + 4 * (w_n727 x).toNat + 8 * (w_n728 x).toNat)) + (4 * (w_n729 x).toNat + 8 * (w_n730 x).toNat + 16 * (w_n731 x).toNat)) + (4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat)) + (8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t250 x) (t265 x)) (e242 x)) (e243 x)) (e244 x)) (e245 x)) (e246 x))
  have e1 : (((((((I_t250 x) + (I_t265 x)) + ((w_n675 x).toNat + (w_n678 x).toNat + (w_n681 x).toNat + (w_n708 x).toNat + (w_n711 x).toNat + (w_n714 x).toNat)) + (2 * (w_n676 x).toNat + 2 * (w_n679 x).toNat + 2 * (w_n682 x).toNat + 2 * (w_n684 x).toNat + 2 * (w_n709 x).toNat + 2 * (w_n712 x).toNat)) + (4 * (w_n677 x).toNat + 4 * (w_n680 x).toNat + 4 * (w_n683 x).toNat + 4 * (w_n685 x).toNat + 4 * (w_n687 x).toNat + 4 * (w_n710 x).toNat)) + (4 * (w_n713 x).toNat + 4 * (w_n716 x).toNat + 4 * (w_n718 x).toNat + 4 * (w_n720 x).toNat + 4 * (w_n725 x).toNat + 4 * (w_n727 x).toNat)) + (8 * (w_n686 x).toNat + 8 * (w_n688 x).toNat + 8 * (w_n719 x).toNat + 8 * (w_n721 x).toNat + 8 * (w_n728 x).toNat + 8 * (w_n730 x).toNat)) = (I_t266 x) + ((w_n675 x).toNat + (w_n678 x).toNat + (w_n681 x).toNat + (w_n708 x).toNat + (w_n711 x).toNat + (w_n714 x).toNat + 2 * (w_n676 x).toNat + 2 * (w_n679 x).toNat + 2 * (w_n682 x).toNat + 2 * (w_n684 x).toNat + 2 * (w_n709 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n677 x).toNat + 4 * (w_n680 x).toNat + 4 * (w_n683 x).toNat + 4 * (w_n685 x).toNat + 4 * (w_n687 x).toNat + 4 * (w_n710 x).toNat + 4 * (w_n713 x).toNat + 4 * (w_n716 x).toNat + 4 * (w_n718 x).toNat + 4 * (w_n720 x).toNat + 4 * (w_n725 x).toNat + 4 * (w_n727 x).toNat + 8 * (w_n686 x).toNat + 8 * (w_n688 x).toNat + 8 * (w_n719 x).toNat + 8 * (w_n721 x).toNat + 8 * (w_n728 x).toNat + 8 * (w_n730 x).toNat) := by unfold I_t266; ac_rfl
  have e2 : ((((((((w_n675 x).toNat + 2 * (w_n676 x).toNat + 4 * (w_n677 x).toNat + (w_n678 x).toNat + 2 * (w_n679 x).toNat + 4 * (w_n680 x).toNat + (w_n681 x).toNat + 2 * (w_n682 x).toNat + 4 * (w_n683 x).toNat + 2 * (w_n684 x).toNat + 4 * (w_n685 x).toNat + 8 * (w_n686 x).toNat + 4 * (w_n687 x).toNat + 8 * (w_n688 x).toNat + 16 * (w_n689 x).toNat) + ((w_n708 x).toNat + 2 * (w_n709 x).toNat + 4 * (w_n710 x).toNat + (w_n711 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n713 x).toNat + (w_n714 x).toNat + 2 * (w_n715 x).toNat + 4 * (w_n716 x).toNat + 2 * (w_n717 x).toNat + 4 * (w_n718 x).toNat + 8 * (w_n719 x).toNat + 4 * (w_n720 x).toNat + 8 * (w_n721 x).toNat + 16 * (w_n722 x).toNat)) + ((w_n723 x).toNat + 2 * (w_n724 x).toNat + 4 * (w_n725 x).toNat)) + (2 * (w_n726 x).toNat + 4 * (w_n727 x).toNat + 8 * (w_n728 x).toNat)) + (4 * (w_n729 x).toNat + 8 * (w_n730 x).toNat + 16 * (w_n731 x).toNat)) + (4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat)) + (8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat)) = (16 * (w_n689 x).toNat + 2 * (w_n715 x).toNat + 2 * (w_n717 x).toNat + 16 * (w_n722 x).toNat + (w_n723 x).toNat + 2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n729 x).toNat + 16 * (w_n731 x).toNat + 4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat) + ((w_n675 x).toNat + (w_n678 x).toNat + (w_n681 x).toNat + (w_n708 x).toNat + (w_n711 x).toNat + (w_n714 x).toNat + 2 * (w_n676 x).toNat + 2 * (w_n679 x).toNat + 2 * (w_n682 x).toNat + 2 * (w_n684 x).toNat + 2 * (w_n709 x).toNat + 2 * (w_n712 x).toNat + 4 * (w_n677 x).toNat + 4 * (w_n680 x).toNat + 4 * (w_n683 x).toNat + 4 * (w_n685 x).toNat + 4 * (w_n687 x).toNat + 4 * (w_n710 x).toNat + 4 * (w_n713 x).toNat + 4 * (w_n716 x).toNat + 4 * (w_n718 x).toNat + 4 * (w_n720 x).toNat + 4 * (w_n725 x).toNat + 4 * (w_n727 x).toNat + 8 * (w_n686 x).toNat + 8 * (w_n688 x).toNat + 8 * (w_n719 x).toNat + 8 * (w_n721 x).toNat + 8 * (w_n728 x).toNat + 8 * (w_n730 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s266 (x : Nat → Bool) : I_t266 x = pc x 175 96 := by
  have hl := s250 x
  have hr := s265 x
  have : pc x 175 96 = pc x 175 48 + pc x 223 48 := pc_add x 175 48 48
  unfold I_t266
  omega
def I_t267 (x : Nat → Bool) : Nat := I_t235 x + I_t266 x
theorem t267 (x : Nat → Bool) : I_t267 x = (w_n642 x).toNat + 4 * (w_n648 x).toNat + 4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 8 * (w_n654 x).toNat + 32 * (w_n656 x).toNat + 16 * (w_n722 x).toNat + (w_n723 x).toNat + 2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n729 x).toNat + 16 * (w_n731 x).toNat + 4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat + 2 * (w_n738 x).toNat + 4 * (w_n739 x).toNat + 8 * (w_n740 x).toNat + 16 * (w_n741 x).toNat + 32 * (w_n742 x).toNat + 64 * (w_n743 x).toNat := by
  have hs : ((((I_t235 x) + (I_t266 x)) + (2 * (w_n634 x).toNat + 2 * (w_n636 x).toNat + 2 * (w_n643 x).toNat + 2 * (w_n645 x).toNat + 2 * (w_n715 x).toNat + 2 * (w_n717 x).toNat)) + (16 * (w_n608 x).toNat + 16 * (w_n641 x).toNat + 16 * (w_n650 x).toNat + 16 * (w_n653 x).toNat + 16 * (w_n655 x).toNat + 16 * (w_n689 x).toNat)) = ((((16 * (w_n608 x).toNat + 2 * (w_n634 x).toNat + 2 * (w_n636 x).toNat + 16 * (w_n641 x).toNat + (w_n642 x).toNat + 2 * (w_n643 x).toNat + 2 * (w_n645 x).toNat + 4 * (w_n648 x).toNat + 16 * (w_n650 x).toNat + 4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 16 * (w_n653 x).toNat + 8 * (w_n654 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n656 x).toNat) + (16 * (w_n689 x).toNat + 2 * (w_n715 x).toNat + 2 * (w_n717 x).toNat + 16 * (w_n722 x).toNat + (w_n723 x).toNat + 2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n729 x).toNat + 16 * (w_n731 x).toNat + 4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat)) + (2 * (w_n738 x).toNat + 4 * (w_n739 x).toNat + 8 * (w_n740 x).toNat)) + (16 * (w_n741 x).toNat + 32 * (w_n742 x).toNat + 64 * (w_n743 x).toNat)) := (add_eq (add_eq (add_eq (t235 x) (t266 x)) (e247 x)) (e248 x))
  have e1 : ((((I_t235 x) + (I_t266 x)) + (2 * (w_n634 x).toNat + 2 * (w_n636 x).toNat + 2 * (w_n643 x).toNat + 2 * (w_n645 x).toNat + 2 * (w_n715 x).toNat + 2 * (w_n717 x).toNat)) + (16 * (w_n608 x).toNat + 16 * (w_n641 x).toNat + 16 * (w_n650 x).toNat + 16 * (w_n653 x).toNat + 16 * (w_n655 x).toNat + 16 * (w_n689 x).toNat)) = (I_t267 x) + (2 * (w_n634 x).toNat + 2 * (w_n636 x).toNat + 2 * (w_n643 x).toNat + 2 * (w_n645 x).toNat + 2 * (w_n715 x).toNat + 2 * (w_n717 x).toNat + 16 * (w_n608 x).toNat + 16 * (w_n641 x).toNat + 16 * (w_n650 x).toNat + 16 * (w_n653 x).toNat + 16 * (w_n655 x).toNat + 16 * (w_n689 x).toNat) := by unfold I_t267; ac_rfl
  have e2 : ((((16 * (w_n608 x).toNat + 2 * (w_n634 x).toNat + 2 * (w_n636 x).toNat + 16 * (w_n641 x).toNat + (w_n642 x).toNat + 2 * (w_n643 x).toNat + 2 * (w_n645 x).toNat + 4 * (w_n648 x).toNat + 16 * (w_n650 x).toNat + 4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 16 * (w_n653 x).toNat + 8 * (w_n654 x).toNat + 16 * (w_n655 x).toNat + 32 * (w_n656 x).toNat) + (16 * (w_n689 x).toNat + 2 * (w_n715 x).toNat + 2 * (w_n717 x).toNat + 16 * (w_n722 x).toNat + (w_n723 x).toNat + 2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n729 x).toNat + 16 * (w_n731 x).toNat + 4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat)) + (2 * (w_n738 x).toNat + 4 * (w_n739 x).toNat + 8 * (w_n740 x).toNat)) + (16 * (w_n741 x).toNat + 32 * (w_n742 x).toNat + 64 * (w_n743 x).toNat)) = ((w_n642 x).toNat + 4 * (w_n648 x).toNat + 4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 8 * (w_n654 x).toNat + 32 * (w_n656 x).toNat + 16 * (w_n722 x).toNat + (w_n723 x).toNat + 2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n729 x).toNat + 16 * (w_n731 x).toNat + 4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat + 2 * (w_n738 x).toNat + 4 * (w_n739 x).toNat + 8 * (w_n740 x).toNat + 16 * (w_n741 x).toNat + 32 * (w_n742 x).toNat + 64 * (w_n743 x).toNat) + (2 * (w_n634 x).toNat + 2 * (w_n636 x).toNat + 2 * (w_n643 x).toNat + 2 * (w_n645 x).toNat + 2 * (w_n715 x).toNat + 2 * (w_n717 x).toNat + 16 * (w_n608 x).toNat + 16 * (w_n641 x).toNat + 16 * (w_n650 x).toNat + 16 * (w_n653 x).toNat + 16 * (w_n655 x).toNat + 16 * (w_n689 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s267 (x : Nat → Bool) : I_t267 x = pc x 79 192 := by
  have hl := s235 x
  have hr := s266 x
  have : pc x 79 192 = pc x 79 96 + pc x 175 96 := pc_add x 79 96 96
  unfold I_t267
  omega
def I_b268 (x : Nat → Bool) : Nat := 0 + (x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat
theorem b268 (x : Nat → Bool) : I_b268 x = (x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat := by
  unfold I_b268
  omega
def I_t268 (x : Nat → Bool) : Nat := I_b268 x
theorem t268 (x : Nat → Bool) : I_t268 x = (w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat := by
  have hs : ((I_b268 x) + ((x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat)) = (((x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat) + ((w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat)) := (add_eq (b268 x) (e249 x))
  have e1 : ((I_b268 x) + ((x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat)) = (I_t268 x) + ((x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat) := by unfold I_t268; ac_rfl
  have e2 : (((x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat) + ((w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat)) = ((w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat) + ((x 361).toNat + (x 362).toNat + (x 363).toNat + (x 364).toNat + (x 365).toNat + (x 366).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s268 (x : Nat → Bool) : I_t268 x = pc x 361 6 := rfl
def I_b269 (x : Nat → Bool) : Nat := 0 + (x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat
theorem b269 (x : Nat → Bool) : I_b269 x = (x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat := by
  unfold I_b269
  omega
def I_t269 (x : Nat → Bool) : Nat := I_b269 x
theorem t269 (x : Nat → Bool) : I_t269 x = (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat := by
  have hs : ((I_b269 x) + ((x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat)) = (((x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat) + ((w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat)) := (add_eq (b269 x) (e250 x))
  have e1 : ((I_b269 x) + ((x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat)) = (I_t269 x) + ((x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat) := by unfold I_t269; ac_rfl
  have e2 : (((x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat) + ((w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat)) = ((w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat) + ((x 355).toNat + (x 356).toNat + (x 357).toNat + (x 358).toNat + (x 359).toNat + (x 360).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s269 (x : Nat → Bool) : I_t269 x = pc x 355 6 := rfl
def I_t270 (x : Nat → Bool) : Nat := I_t268 x + I_t269 x
theorem t270 (x : Nat → Bool) : I_t270 x = (w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat + (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat := by
  have hs : ((I_t268 x) + (I_t269 x)) = (((w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat) + ((w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat)) := (add_eq (t268 x) (t269 x))
  have e1 : ((I_t268 x) + (I_t269 x)) = I_t270 x := by unfold I_t270; ac_rfl
  have e2 : (((w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat) + ((w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat)) = (w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat + (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s270 (x : Nat → Bool) : I_t270 x = pc x 355 12 := by
  have hl := s268 x
  have hr := s269 x
  have : pc x 355 12 = pc x 355 6 + pc x 361 6 := pc_add x 355 6 6
  unfold I_t270
  omega
def I_b271 (x : Nat → Bool) : Nat := 0 + (x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat
theorem b271 (x : Nat → Bool) : I_b271 x = (x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat := by
  unfold I_b271
  omega
def I_t271 (x : Nat → Bool) : Nat := I_b271 x
theorem t271 (x : Nat → Bool) : I_t271 x = (w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat := by
  have hs : ((I_b271 x) + ((x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat)) = (((x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat) + ((w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat)) := (add_eq (b271 x) (e251 x))
  have e1 : ((I_b271 x) + ((x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat)) = (I_t271 x) + ((x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat) := by unfold I_t271; ac_rfl
  have e2 : (((x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat) + ((w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat)) = ((w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat) + ((x 349).toNat + (x 350).toNat + (x 351).toNat + (x 352).toNat + (x 353).toNat + (x 354).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s271 (x : Nat → Bool) : I_t271 x = pc x 349 6 := rfl
def I_b272 (x : Nat → Bool) : Nat := 0 + (x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat
theorem b272 (x : Nat → Bool) : I_b272 x = (x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat := by
  unfold I_b272
  omega
def I_t272 (x : Nat → Bool) : Nat := I_b272 x
theorem t272 (x : Nat → Bool) : I_t272 x = (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat := by
  have hs : ((I_b272 x) + ((x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat)) = (((x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat) + ((w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat)) := (add_eq (b272 x) (e252 x))
  have e1 : ((I_b272 x) + ((x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat)) = (I_t272 x) + ((x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat) := by unfold I_t272; ac_rfl
  have e2 : (((x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat) + ((w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat)) = ((w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat) + ((x 343).toNat + (x 344).toNat + (x 345).toNat + (x 346).toNat + (x 347).toNat + (x 348).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s272 (x : Nat → Bool) : I_t272 x = pc x 343 6 := rfl
def I_t273 (x : Nat → Bool) : Nat := I_t271 x + I_t272 x
theorem t273 (x : Nat → Bool) : I_t273 x = (w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat + (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat := by
  have hs : ((I_t271 x) + (I_t272 x)) = (((w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat) + ((w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat)) := (add_eq (t271 x) (t272 x))
  have e1 : ((I_t271 x) + (I_t272 x)) = I_t273 x := by unfold I_t273; ac_rfl
  have e2 : (((w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat) + ((w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat)) = (w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat + (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s273 (x : Nat → Bool) : I_t273 x = pc x 343 12 := by
  have hl := s271 x
  have hr := s272 x
  have : pc x 343 12 = pc x 343 6 + pc x 349 6 := pc_add x 343 6 6
  unfold I_t273
  omega
def I_t274 (x : Nat → Bool) : Nat := I_t270 x + I_t273 x
theorem t274 (x : Nat → Bool) : I_t274 x = (w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat + (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat + (w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat + (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat := by
  have hs : ((I_t270 x) + (I_t273 x)) = (((w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat + (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat) + ((w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat + (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat)) := (add_eq (t270 x) (t273 x))
  have e1 : ((I_t270 x) + (I_t273 x)) = I_t274 x := by unfold I_t274; ac_rfl
  have e2 : (((w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat + (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat) + ((w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat + (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat)) = (w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat + (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat + (w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat + (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s274 (x : Nat → Bool) : I_t274 x = pc x 343 24 := by
  have hl := s270 x
  have hr := s273 x
  have : pc x 343 24 = pc x 343 12 + pc x 355 12 := pc_add x 343 12 12
  unfold I_t274
  omega
def I_b275 (x : Nat → Bool) : Nat := 0 + (x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat
theorem b275 (x : Nat → Bool) : I_b275 x = (x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat := by
  unfold I_b275
  omega
def I_t275 (x : Nat → Bool) : Nat := I_b275 x
theorem t275 (x : Nat → Bool) : I_t275 x = (w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat := by
  have hs : ((I_b275 x) + ((x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat)) = (((x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat) + ((w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat)) := (add_eq (b275 x) (e253 x))
  have e1 : ((I_b275 x) + ((x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat)) = (I_t275 x) + ((x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat) := by unfold I_t275; ac_rfl
  have e2 : (((x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat) + ((w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat)) = ((w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat) + ((x 337).toNat + (x 338).toNat + (x 339).toNat + (x 340).toNat + (x 341).toNat + (x 342).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s275 (x : Nat → Bool) : I_t275 x = pc x 337 6 := rfl
def I_b276 (x : Nat → Bool) : Nat := 0 + (x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat
theorem b276 (x : Nat → Bool) : I_b276 x = (x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat := by
  unfold I_b276
  omega
def I_t276 (x : Nat → Bool) : Nat := I_b276 x
theorem t276 (x : Nat → Bool) : I_t276 x = (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat := by
  have hs : ((I_b276 x) + ((x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat)) = (((x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat) + ((w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat)) := (add_eq (b276 x) (e254 x))
  have e1 : ((I_b276 x) + ((x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat)) = (I_t276 x) + ((x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat) := by unfold I_t276; ac_rfl
  have e2 : (((x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat) + ((w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat)) = ((w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat) + ((x 331).toNat + (x 332).toNat + (x 333).toNat + (x 334).toNat + (x 335).toNat + (x 336).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s276 (x : Nat → Bool) : I_t276 x = pc x 331 6 := rfl
def I_t277 (x : Nat → Bool) : Nat := I_t275 x + I_t276 x
theorem t277 (x : Nat → Bool) : I_t277 x = (w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat + (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat := by
  have hs : ((I_t275 x) + (I_t276 x)) = (((w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat) + ((w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat)) := (add_eq (t275 x) (t276 x))
  have e1 : ((I_t275 x) + (I_t276 x)) = I_t277 x := by unfold I_t277; ac_rfl
  have e2 : (((w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat) + ((w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat)) = (w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat + (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s277 (x : Nat → Bool) : I_t277 x = pc x 331 12 := by
  have hl := s275 x
  have hr := s276 x
  have : pc x 331 12 = pc x 331 6 + pc x 337 6 := pc_add x 331 6 6
  unfold I_t277
  omega
def I_b278 (x : Nat → Bool) : Nat := 0 + (x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat
theorem b278 (x : Nat → Bool) : I_b278 x = (x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat := by
  unfold I_b278
  omega
def I_t278 (x : Nat → Bool) : Nat := I_b278 x
theorem t278 (x : Nat → Bool) : I_t278 x = (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat := by
  have hs : ((I_b278 x) + ((x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat)) = (((x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat) + ((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat)) := (add_eq (b278 x) (e255 x))
  have e1 : ((I_b278 x) + ((x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat)) = (I_t278 x) + ((x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat) := by unfold I_t278; ac_rfl
  have e2 : (((x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat) + ((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat)) = ((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat) + ((x 325).toNat + (x 326).toNat + (x 327).toNat + (x 328).toNat + (x 329).toNat + (x 330).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s278 (x : Nat → Bool) : I_t278 x = pc x 325 6 := rfl
def I_b279 (x : Nat → Bool) : Nat := 0 + (x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat
theorem b279 (x : Nat → Bool) : I_b279 x = (x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat := by
  unfold I_b279
  omega
def I_t279 (x : Nat → Bool) : Nat := I_b279 x
theorem t279 (x : Nat → Bool) : I_t279 x = (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat := by
  have hs : ((I_b279 x) + ((x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat)) = (((x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat) + ((w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat)) := (add_eq (b279 x) (e256 x))
  have e1 : ((I_b279 x) + ((x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat)) = (I_t279 x) + ((x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat) := by unfold I_t279; ac_rfl
  have e2 : (((x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat) + ((w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat)) = ((w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat) + ((x 319).toNat + (x 320).toNat + (x 321).toNat + (x 322).toNat + (x 323).toNat + (x 324).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s279 (x : Nat → Bool) : I_t279 x = pc x 319 6 := rfl
def I_t280 (x : Nat → Bool) : Nat := I_t278 x + I_t279 x
theorem t280 (x : Nat → Bool) : I_t280 x = (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat := by
  have hs : ((I_t278 x) + (I_t279 x)) = (((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat) + ((w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat)) := (add_eq (t278 x) (t279 x))
  have e1 : ((I_t278 x) + (I_t279 x)) = I_t280 x := by unfold I_t280; ac_rfl
  have e2 : (((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat) + ((w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat)) = (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s280 (x : Nat → Bool) : I_t280 x = pc x 319 12 := by
  have hl := s278 x
  have hr := s279 x
  have : pc x 319 12 = pc x 319 6 + pc x 325 6 := pc_add x 319 6 6
  unfold I_t280
  omega
def I_t281 (x : Nat → Bool) : Nat := I_t277 x + I_t280 x
theorem t281 (x : Nat → Bool) : I_t281 x = (w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat + (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat + (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat := by
  have hs : ((I_t277 x) + (I_t280 x)) = (((w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat + (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat) + ((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat)) := (add_eq (t277 x) (t280 x))
  have e1 : ((I_t277 x) + (I_t280 x)) = I_t281 x := by unfold I_t281; ac_rfl
  have e2 : (((w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat + (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat) + ((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat)) = (w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat + (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat + (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s281 (x : Nat → Bool) : I_t281 x = pc x 319 24 := by
  have hl := s277 x
  have hr := s280 x
  have : pc x 319 24 = pc x 319 12 + pc x 331 12 := pc_add x 319 12 12
  unfold I_t281
  omega
def I_t282 (x : Nat → Bool) : Nat := I_t274 x + I_t281 x
theorem t282 (x : Nat → Bool) : I_t282 x = (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat + (w_n768 x).toNat + 2 * (w_n769 x).toNat + 4 * (w_n770 x).toNat + 2 * (w_n771 x).toNat + 4 * (w_n772 x).toNat + 8 * (w_n773 x).toNat + 4 * (w_n774 x).toNat + 8 * (w_n775 x).toNat + 16 * (w_n776 x).toNat := by
  have hs : (((((I_t274 x) + (I_t281 x)) + ((w_n744 x).toNat + (w_n747 x).toNat + (w_n750 x).toNat + (w_n753 x).toNat + (w_n756 x).toNat + (w_n759 x).toNat)) + (2 * (w_n745 x).toNat + 2 * (w_n748 x).toNat + 2 * (w_n751 x).toNat + 2 * (w_n754 x).toNat + 2 * (w_n757 x).toNat + 2 * (w_n760 x).toNat)) + (4 * (w_n746 x).toNat + 4 * (w_n749 x).toNat + 4 * (w_n752 x).toNat + 4 * (w_n755 x).toNat + 4 * (w_n758 x).toNat + 4 * (w_n761 x).toNat)) = ((((((w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat + (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat + (w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat + (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat) + ((w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat + (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat + (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat)) + ((w_n768 x).toNat + 2 * (w_n769 x).toNat + 4 * (w_n770 x).toNat)) + (2 * (w_n771 x).toNat + 4 * (w_n772 x).toNat + 8 * (w_n773 x).toNat)) + (4 * (w_n774 x).toNat + 8 * (w_n775 x).toNat + 16 * (w_n776 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t274 x) (t281 x)) (e257 x)) (e258 x)) (e259 x))
  have e1 : (((((I_t274 x) + (I_t281 x)) + ((w_n744 x).toNat + (w_n747 x).toNat + (w_n750 x).toNat + (w_n753 x).toNat + (w_n756 x).toNat + (w_n759 x).toNat)) + (2 * (w_n745 x).toNat + 2 * (w_n748 x).toNat + 2 * (w_n751 x).toNat + 2 * (w_n754 x).toNat + 2 * (w_n757 x).toNat + 2 * (w_n760 x).toNat)) + (4 * (w_n746 x).toNat + 4 * (w_n749 x).toNat + 4 * (w_n752 x).toNat + 4 * (w_n755 x).toNat + 4 * (w_n758 x).toNat + 4 * (w_n761 x).toNat)) = (I_t282 x) + ((w_n744 x).toNat + (w_n747 x).toNat + (w_n750 x).toNat + (w_n753 x).toNat + (w_n756 x).toNat + (w_n759 x).toNat + 2 * (w_n745 x).toNat + 2 * (w_n748 x).toNat + 2 * (w_n751 x).toNat + 2 * (w_n754 x).toNat + 2 * (w_n757 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n746 x).toNat + 4 * (w_n749 x).toNat + 4 * (w_n752 x).toNat + 4 * (w_n755 x).toNat + 4 * (w_n758 x).toNat + 4 * (w_n761 x).toNat) := by unfold I_t282; ac_rfl
  have e2 : ((((((w_n744 x).toNat + 2 * (w_n745 x).toNat + 4 * (w_n746 x).toNat + (w_n747 x).toNat + 2 * (w_n748 x).toNat + 4 * (w_n749 x).toNat + (w_n750 x).toNat + 2 * (w_n751 x).toNat + 4 * (w_n752 x).toNat + (w_n753 x).toNat + 2 * (w_n754 x).toNat + 4 * (w_n755 x).toNat) + ((w_n756 x).toNat + 2 * (w_n757 x).toNat + 4 * (w_n758 x).toNat + (w_n759 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n761 x).toNat + (w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat)) + ((w_n768 x).toNat + 2 * (w_n769 x).toNat + 4 * (w_n770 x).toNat)) + (2 * (w_n771 x).toNat + 4 * (w_n772 x).toNat + 8 * (w_n773 x).toNat)) + (4 * (w_n774 x).toNat + 8 * (w_n775 x).toNat + 16 * (w_n776 x).toNat)) = ((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat + (w_n768 x).toNat + 2 * (w_n769 x).toNat + 4 * (w_n770 x).toNat + 2 * (w_n771 x).toNat + 4 * (w_n772 x).toNat + 8 * (w_n773 x).toNat + 4 * (w_n774 x).toNat + 8 * (w_n775 x).toNat + 16 * (w_n776 x).toNat) + ((w_n744 x).toNat + (w_n747 x).toNat + (w_n750 x).toNat + (w_n753 x).toNat + (w_n756 x).toNat + (w_n759 x).toNat + 2 * (w_n745 x).toNat + 2 * (w_n748 x).toNat + 2 * (w_n751 x).toNat + 2 * (w_n754 x).toNat + 2 * (w_n757 x).toNat + 2 * (w_n760 x).toNat + 4 * (w_n746 x).toNat + 4 * (w_n749 x).toNat + 4 * (w_n752 x).toNat + 4 * (w_n755 x).toNat + 4 * (w_n758 x).toNat + 4 * (w_n761 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s282 (x : Nat → Bool) : I_t282 x = pc x 319 48 := by
  have hl := s274 x
  have hr := s281 x
  have : pc x 319 48 = pc x 319 24 + pc x 343 24 := pc_add x 319 24 24
  unfold I_t282
  omega
def I_b283 (x : Nat → Bool) : Nat := 0 + (x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat
theorem b283 (x : Nat → Bool) : I_b283 x = (x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat := by
  unfold I_b283
  omega
def I_t283 (x : Nat → Bool) : Nat := I_b283 x
theorem t283 (x : Nat → Bool) : I_t283 x = (w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat := by
  have hs : ((I_b283 x) + ((x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat)) = (((x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat) + ((w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat)) := (add_eq (b283 x) (e260 x))
  have e1 : ((I_b283 x) + ((x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat)) = (I_t283 x) + ((x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat) := by unfold I_t283; ac_rfl
  have e2 : (((x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat) + ((w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat)) = ((w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat) + ((x 313).toNat + (x 314).toNat + (x 315).toNat + (x 316).toNat + (x 317).toNat + (x 318).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s283 (x : Nat → Bool) : I_t283 x = pc x 313 6 := rfl
def I_b284 (x : Nat → Bool) : Nat := 0 + (x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat
theorem b284 (x : Nat → Bool) : I_b284 x = (x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat := by
  unfold I_b284
  omega
def I_t284 (x : Nat → Bool) : Nat := I_b284 x
theorem t284 (x : Nat → Bool) : I_t284 x = (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat := by
  have hs : ((I_b284 x) + ((x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat)) = (((x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat) + ((w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat)) := (add_eq (b284 x) (e261 x))
  have e1 : ((I_b284 x) + ((x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat)) = (I_t284 x) + ((x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat) := by unfold I_t284; ac_rfl
  have e2 : (((x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat) + ((w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat)) = ((w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat) + ((x 307).toNat + (x 308).toNat + (x 309).toNat + (x 310).toNat + (x 311).toNat + (x 312).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s284 (x : Nat → Bool) : I_t284 x = pc x 307 6 := rfl
def I_t285 (x : Nat → Bool) : Nat := I_t283 x + I_t284 x
theorem t285 (x : Nat → Bool) : I_t285 x = (w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat + (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat := by
  have hs : ((I_t283 x) + (I_t284 x)) = (((w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat) + ((w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat)) := (add_eq (t283 x) (t284 x))
  have e1 : ((I_t283 x) + (I_t284 x)) = I_t285 x := by unfold I_t285; ac_rfl
  have e2 : (((w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat) + ((w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat)) = (w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat + (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s285 (x : Nat → Bool) : I_t285 x = pc x 307 12 := by
  have hl := s283 x
  have hr := s284 x
  have : pc x 307 12 = pc x 307 6 + pc x 313 6 := pc_add x 307 6 6
  unfold I_t285
  omega
def I_b286 (x : Nat → Bool) : Nat := 0 + (x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat
theorem b286 (x : Nat → Bool) : I_b286 x = (x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat := by
  unfold I_b286
  omega
def I_t286 (x : Nat → Bool) : Nat := I_b286 x
theorem t286 (x : Nat → Bool) : I_t286 x = (w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat := by
  have hs : ((I_b286 x) + ((x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat)) = (((x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat) + ((w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat)) := (add_eq (b286 x) (e262 x))
  have e1 : ((I_b286 x) + ((x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat)) = (I_t286 x) + ((x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat) := by unfold I_t286; ac_rfl
  have e2 : (((x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat) + ((w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat)) = ((w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat) + ((x 295).toNat + (x 296).toNat + (x 297).toNat + (x 298).toNat + (x 299).toNat + (x 300).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s286 (x : Nat → Bool) : I_t286 x = pc x 295 6 := rfl
def I_b287 (x : Nat → Bool) : Nat := 0 + (x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat
theorem b287 (x : Nat → Bool) : I_b287 x = (x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat := by
  unfold I_b287
  omega
def I_t287 (x : Nat → Bool) : Nat := I_b287 x
theorem t287 (x : Nat → Bool) : I_t287 x = (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat := by
  have hs : ((I_b287 x) + ((x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat)) = (((x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat) + ((w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat)) := (add_eq (b287 x) (e263 x))
  have e1 : ((I_b287 x) + ((x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat)) = (I_t287 x) + ((x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat) := by unfold I_t287; ac_rfl
  have e2 : (((x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat) + ((w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat)) = ((w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat) + ((x 301).toNat + (x 302).toNat + (x 303).toNat + (x 304).toNat + (x 305).toNat + (x 306).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s287 (x : Nat → Bool) : I_t287 x = pc x 301 6 := rfl
def I_t288 (x : Nat → Bool) : Nat := I_t286 x + I_t287 x
theorem t288 (x : Nat → Bool) : I_t288 x = (w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat + (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat := by
  have hs : ((I_t286 x) + (I_t287 x)) = (((w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat) + ((w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat)) := (add_eq (t286 x) (t287 x))
  have e1 : ((I_t286 x) + (I_t287 x)) = I_t288 x := by unfold I_t288; ac_rfl
  have e2 : (((w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat) + ((w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat)) = (w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat + (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s288 (x : Nat → Bool) : I_t288 x = pc x 295 12 := by
  have hl := s286 x
  have hr := s287 x
  have : pc x 295 12 = pc x 295 6 + pc x 301 6 := pc_add x 295 6 6
  unfold I_t288
  omega
def I_t289 (x : Nat → Bool) : Nat := I_t285 x + I_t288 x
theorem t289 (x : Nat → Bool) : I_t289 x = (w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat + (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat + (w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat + (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat := by
  have hs : ((I_t285 x) + (I_t288 x)) = (((w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat + (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat) + ((w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat + (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat)) := (add_eq (t285 x) (t288 x))
  have e1 : ((I_t285 x) + (I_t288 x)) = I_t289 x := by unfold I_t289; ac_rfl
  have e2 : (((w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat + (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat) + ((w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat + (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat)) = (w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat + (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat + (w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat + (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s289 (x : Nat → Bool) : I_t289 x = pc x 295 24 := by
  have hl := s285 x
  have hr := s288 x
  have : pc x 295 24 = pc x 295 12 + pc x 307 12 := pc_add x 295 12 12
  unfold I_t289
  omega
def I_b290 (x : Nat → Bool) : Nat := 0 + (x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat
theorem b290 (x : Nat → Bool) : I_b290 x = (x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat := by
  unfold I_b290
  omega
def I_t290 (x : Nat → Bool) : Nat := I_b290 x
theorem t290 (x : Nat → Bool) : I_t290 x = (w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat := by
  have hs : ((I_b290 x) + ((x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat)) = (((x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat) + ((w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat)) := (add_eq (b290 x) (e264 x))
  have e1 : ((I_b290 x) + ((x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat)) = (I_t290 x) + ((x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat) := by unfold I_t290; ac_rfl
  have e2 : (((x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat) + ((w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat)) = ((w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat) + ((x 271).toNat + (x 272).toNat + (x 273).toNat + (x 274).toNat + (x 275).toNat + (x 276).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s290 (x : Nat → Bool) : I_t290 x = pc x 271 6 := rfl
def I_b291 (x : Nat → Bool) : Nat := 0 + (x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat
theorem b291 (x : Nat → Bool) : I_b291 x = (x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat := by
  unfold I_b291
  omega
def I_t291 (x : Nat → Bool) : Nat := I_b291 x
theorem t291 (x : Nat → Bool) : I_t291 x = (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat := by
  have hs : ((I_b291 x) + ((x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat)) = (((x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat) + ((w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat)) := (add_eq (b291 x) (e265 x))
  have e1 : ((I_b291 x) + ((x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat)) = (I_t291 x) + ((x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat) := by unfold I_t291; ac_rfl
  have e2 : (((x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat) + ((w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat)) = ((w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat) + ((x 277).toNat + (x 278).toNat + (x 279).toNat + (x 280).toNat + (x 281).toNat + (x 282).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s291 (x : Nat → Bool) : I_t291 x = pc x 277 6 := rfl
def I_t292 (x : Nat → Bool) : Nat := I_t290 x + I_t291 x
theorem t292 (x : Nat → Bool) : I_t292 x = (w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat + (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat := by
  have hs : ((I_t290 x) + (I_t291 x)) = (((w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat) + ((w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat)) := (add_eq (t290 x) (t291 x))
  have e1 : ((I_t290 x) + (I_t291 x)) = I_t292 x := by unfold I_t292; ac_rfl
  have e2 : (((w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat) + ((w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat)) = (w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat + (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s292 (x : Nat → Bool) : I_t292 x = pc x 271 12 := by
  have hl := s290 x
  have hr := s291 x
  have : pc x 271 12 = pc x 271 6 + pc x 277 6 := pc_add x 271 6 6
  unfold I_t292
  omega
def I_b293 (x : Nat → Bool) : Nat := 0 + (x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat
theorem b293 (x : Nat → Bool) : I_b293 x = (x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat := by
  unfold I_b293
  omega
def I_t293 (x : Nat → Bool) : Nat := I_b293 x
theorem t293 (x : Nat → Bool) : I_t293 x = (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat := by
  have hs : ((I_b293 x) + ((x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat)) = (((x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat) + ((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat)) := (add_eq (b293 x) (e266 x))
  have e1 : ((I_b293 x) + ((x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat)) = (I_t293 x) + ((x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat) := by unfold I_t293; ac_rfl
  have e2 : (((x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat) + ((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat)) = ((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat) + ((x 289).toNat + (x 290).toNat + (x 291).toNat + (x 292).toNat + (x 293).toNat + (x 294).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s293 (x : Nat → Bool) : I_t293 x = pc x 289 6 := rfl
def I_b294 (x : Nat → Bool) : Nat := 0 + (x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat
theorem b294 (x : Nat → Bool) : I_b294 x = (x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat := by
  unfold I_b294
  omega
def I_t294 (x : Nat → Bool) : Nat := I_b294 x
theorem t294 (x : Nat → Bool) : I_t294 x = (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat := by
  have hs : ((I_b294 x) + ((x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat)) = (((x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat) + ((w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat)) := (add_eq (b294 x) (e267 x))
  have e1 : ((I_b294 x) + ((x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat)) = (I_t294 x) + ((x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat) := by unfold I_t294; ac_rfl
  have e2 : (((x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat) + ((w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat)) = ((w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat) + ((x 283).toNat + (x 284).toNat + (x 285).toNat + (x 286).toNat + (x 287).toNat + (x 288).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s294 (x : Nat → Bool) : I_t294 x = pc x 283 6 := rfl
def I_t295 (x : Nat → Bool) : Nat := I_t293 x + I_t294 x
theorem t295 (x : Nat → Bool) : I_t295 x = (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat := by
  have hs : ((I_t293 x) + (I_t294 x)) = (((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat) + ((w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat)) := (add_eq (t293 x) (t294 x))
  have e1 : ((I_t293 x) + (I_t294 x)) = I_t295 x := by unfold I_t295; ac_rfl
  have e2 : (((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat) + ((w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat)) = (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s295 (x : Nat → Bool) : I_t295 x = pc x 283 12 := by
  have hl := s293 x
  have hr := s294 x
  have : pc x 283 12 = pc x 283 6 + pc x 289 6 := pc_add x 283 6 6
  unfold I_t295
  omega
def I_t296 (x : Nat → Bool) : Nat := I_t292 x + I_t295 x
theorem t296 (x : Nat → Bool) : I_t296 x = (w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat + (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat + (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat := by
  have hs : ((I_t292 x) + (I_t295 x)) = (((w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat + (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat) + ((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat)) := (add_eq (t292 x) (t295 x))
  have e1 : ((I_t292 x) + (I_t295 x)) = I_t296 x := by unfold I_t296; ac_rfl
  have e2 : (((w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat + (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat) + ((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat)) = (w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat + (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat + (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s296 (x : Nat → Bool) : I_t296 x = pc x 271 24 := by
  have hl := s292 x
  have hr := s295 x
  have : pc x 271 24 = pc x 271 12 + pc x 283 12 := pc_add x 271 12 12
  unfold I_t296
  omega
def I_t297 (x : Nat → Bool) : Nat := I_t289 x + I_t296 x
theorem t297 (x : Nat → Bool) : I_t297 x = (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat + (w_n801 x).toNat + 2 * (w_n802 x).toNat + 4 * (w_n803 x).toNat + 2 * (w_n804 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n806 x).toNat + 4 * (w_n807 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n809 x).toNat := by
  have hs : (((((I_t289 x) + (I_t296 x)) + ((w_n777 x).toNat + (w_n780 x).toNat + (w_n783 x).toNat + (w_n786 x).toNat + (w_n789 x).toNat + (w_n792 x).toNat)) + (2 * (w_n778 x).toNat + 2 * (w_n781 x).toNat + 2 * (w_n784 x).toNat + 2 * (w_n787 x).toNat + 2 * (w_n790 x).toNat + 2 * (w_n793 x).toNat)) + (4 * (w_n779 x).toNat + 4 * (w_n782 x).toNat + 4 * (w_n785 x).toNat + 4 * (w_n788 x).toNat + 4 * (w_n791 x).toNat + 4 * (w_n794 x).toNat)) = ((((((w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat + (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat + (w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat + (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat) + ((w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat + (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat + (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat)) + ((w_n801 x).toNat + 2 * (w_n802 x).toNat + 4 * (w_n803 x).toNat)) + (2 * (w_n804 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n806 x).toNat)) + (4 * (w_n807 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n809 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t289 x) (t296 x)) (e268 x)) (e269 x)) (e270 x))
  have e1 : (((((I_t289 x) + (I_t296 x)) + ((w_n777 x).toNat + (w_n780 x).toNat + (w_n783 x).toNat + (w_n786 x).toNat + (w_n789 x).toNat + (w_n792 x).toNat)) + (2 * (w_n778 x).toNat + 2 * (w_n781 x).toNat + 2 * (w_n784 x).toNat + 2 * (w_n787 x).toNat + 2 * (w_n790 x).toNat + 2 * (w_n793 x).toNat)) + (4 * (w_n779 x).toNat + 4 * (w_n782 x).toNat + 4 * (w_n785 x).toNat + 4 * (w_n788 x).toNat + 4 * (w_n791 x).toNat + 4 * (w_n794 x).toNat)) = (I_t297 x) + ((w_n777 x).toNat + (w_n780 x).toNat + (w_n783 x).toNat + (w_n786 x).toNat + (w_n789 x).toNat + (w_n792 x).toNat + 2 * (w_n778 x).toNat + 2 * (w_n781 x).toNat + 2 * (w_n784 x).toNat + 2 * (w_n787 x).toNat + 2 * (w_n790 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n779 x).toNat + 4 * (w_n782 x).toNat + 4 * (w_n785 x).toNat + 4 * (w_n788 x).toNat + 4 * (w_n791 x).toNat + 4 * (w_n794 x).toNat) := by unfold I_t297; ac_rfl
  have e2 : ((((((w_n777 x).toNat + 2 * (w_n778 x).toNat + 4 * (w_n779 x).toNat + (w_n780 x).toNat + 2 * (w_n781 x).toNat + 4 * (w_n782 x).toNat + (w_n783 x).toNat + 2 * (w_n784 x).toNat + 4 * (w_n785 x).toNat + (w_n786 x).toNat + 2 * (w_n787 x).toNat + 4 * (w_n788 x).toNat) + ((w_n789 x).toNat + 2 * (w_n790 x).toNat + 4 * (w_n791 x).toNat + (w_n792 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n794 x).toNat + (w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat)) + ((w_n801 x).toNat + 2 * (w_n802 x).toNat + 4 * (w_n803 x).toNat)) + (2 * (w_n804 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n806 x).toNat)) + (4 * (w_n807 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n809 x).toNat)) = ((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat + (w_n801 x).toNat + 2 * (w_n802 x).toNat + 4 * (w_n803 x).toNat + 2 * (w_n804 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n806 x).toNat + 4 * (w_n807 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n809 x).toNat) + ((w_n777 x).toNat + (w_n780 x).toNat + (w_n783 x).toNat + (w_n786 x).toNat + (w_n789 x).toNat + (w_n792 x).toNat + 2 * (w_n778 x).toNat + 2 * (w_n781 x).toNat + 2 * (w_n784 x).toNat + 2 * (w_n787 x).toNat + 2 * (w_n790 x).toNat + 2 * (w_n793 x).toNat + 4 * (w_n779 x).toNat + 4 * (w_n782 x).toNat + 4 * (w_n785 x).toNat + 4 * (w_n788 x).toNat + 4 * (w_n791 x).toNat + 4 * (w_n794 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s297 (x : Nat → Bool) : I_t297 x = pc x 271 48 := by
  have hl := s289 x
  have hr := s296 x
  have : pc x 271 48 = pc x 271 24 + pc x 295 24 := pc_add x 271 24 24
  unfold I_t297
  omega
def I_t298 (x : Nat → Bool) : Nat := I_t282 x + I_t297 x
theorem t298 (x : Nat → Bool) : I_t298 x = 16 * (w_n776 x).toNat + 2 * (w_n802 x).toNat + 2 * (w_n804 x).toNat + 16 * (w_n809 x).toNat + (w_n810 x).toNat + 2 * (w_n811 x).toNat + 2 * (w_n813 x).toNat + 4 * (w_n816 x).toNat + 16 * (w_n818 x).toNat + 4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 16 * (w_n821 x).toNat + 8 * (w_n822 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n824 x).toNat := by
  have hs : (((((((I_t282 x) + (I_t297 x)) + ((w_n762 x).toNat + (w_n765 x).toNat + (w_n768 x).toNat + (w_n795 x).toNat + (w_n798 x).toNat + (w_n801 x).toNat)) + (2 * (w_n763 x).toNat + 2 * (w_n766 x).toNat + 2 * (w_n769 x).toNat + 2 * (w_n771 x).toNat + 2 * (w_n796 x).toNat + 2 * (w_n799 x).toNat)) + (4 * (w_n764 x).toNat + 4 * (w_n767 x).toNat + 4 * (w_n770 x).toNat + 4 * (w_n772 x).toNat + 4 * (w_n774 x).toNat + 4 * (w_n797 x).toNat)) + (4 * (w_n800 x).toNat + 4 * (w_n803 x).toNat + 4 * (w_n805 x).toNat + 4 * (w_n807 x).toNat + 4 * (w_n812 x).toNat + 4 * (w_n814 x).toNat)) + (8 * (w_n773 x).toNat + 8 * (w_n775 x).toNat + 8 * (w_n806 x).toNat + 8 * (w_n808 x).toNat + 8 * (w_n815 x).toNat + 8 * (w_n817 x).toNat)) = ((((((((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat + (w_n768 x).toNat + 2 * (w_n769 x).toNat + 4 * (w_n770 x).toNat + 2 * (w_n771 x).toNat + 4 * (w_n772 x).toNat + 8 * (w_n773 x).toNat + 4 * (w_n774 x).toNat + 8 * (w_n775 x).toNat + 16 * (w_n776 x).toNat) + ((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat + (w_n801 x).toNat + 2 * (w_n802 x).toNat + 4 * (w_n803 x).toNat + 2 * (w_n804 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n806 x).toNat + 4 * (w_n807 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n809 x).toNat)) + ((w_n810 x).toNat + 2 * (w_n811 x).toNat + 4 * (w_n812 x).toNat)) + (2 * (w_n813 x).toNat + 4 * (w_n814 x).toNat + 8 * (w_n815 x).toNat)) + (4 * (w_n816 x).toNat + 8 * (w_n817 x).toNat + 16 * (w_n818 x).toNat)) + (4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 16 * (w_n821 x).toNat)) + (8 * (w_n822 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n824 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t282 x) (t297 x)) (e271 x)) (e272 x)) (e273 x)) (e274 x)) (e275 x))
  have e1 : (((((((I_t282 x) + (I_t297 x)) + ((w_n762 x).toNat + (w_n765 x).toNat + (w_n768 x).toNat + (w_n795 x).toNat + (w_n798 x).toNat + (w_n801 x).toNat)) + (2 * (w_n763 x).toNat + 2 * (w_n766 x).toNat + 2 * (w_n769 x).toNat + 2 * (w_n771 x).toNat + 2 * (w_n796 x).toNat + 2 * (w_n799 x).toNat)) + (4 * (w_n764 x).toNat + 4 * (w_n767 x).toNat + 4 * (w_n770 x).toNat + 4 * (w_n772 x).toNat + 4 * (w_n774 x).toNat + 4 * (w_n797 x).toNat)) + (4 * (w_n800 x).toNat + 4 * (w_n803 x).toNat + 4 * (w_n805 x).toNat + 4 * (w_n807 x).toNat + 4 * (w_n812 x).toNat + 4 * (w_n814 x).toNat)) + (8 * (w_n773 x).toNat + 8 * (w_n775 x).toNat + 8 * (w_n806 x).toNat + 8 * (w_n808 x).toNat + 8 * (w_n815 x).toNat + 8 * (w_n817 x).toNat)) = (I_t298 x) + ((w_n762 x).toNat + (w_n765 x).toNat + (w_n768 x).toNat + (w_n795 x).toNat + (w_n798 x).toNat + (w_n801 x).toNat + 2 * (w_n763 x).toNat + 2 * (w_n766 x).toNat + 2 * (w_n769 x).toNat + 2 * (w_n771 x).toNat + 2 * (w_n796 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n764 x).toNat + 4 * (w_n767 x).toNat + 4 * (w_n770 x).toNat + 4 * (w_n772 x).toNat + 4 * (w_n774 x).toNat + 4 * (w_n797 x).toNat + 4 * (w_n800 x).toNat + 4 * (w_n803 x).toNat + 4 * (w_n805 x).toNat + 4 * (w_n807 x).toNat + 4 * (w_n812 x).toNat + 4 * (w_n814 x).toNat + 8 * (w_n773 x).toNat + 8 * (w_n775 x).toNat + 8 * (w_n806 x).toNat + 8 * (w_n808 x).toNat + 8 * (w_n815 x).toNat + 8 * (w_n817 x).toNat) := by unfold I_t298; ac_rfl
  have e2 : ((((((((w_n762 x).toNat + 2 * (w_n763 x).toNat + 4 * (w_n764 x).toNat + (w_n765 x).toNat + 2 * (w_n766 x).toNat + 4 * (w_n767 x).toNat + (w_n768 x).toNat + 2 * (w_n769 x).toNat + 4 * (w_n770 x).toNat + 2 * (w_n771 x).toNat + 4 * (w_n772 x).toNat + 8 * (w_n773 x).toNat + 4 * (w_n774 x).toNat + 8 * (w_n775 x).toNat + 16 * (w_n776 x).toNat) + ((w_n795 x).toNat + 2 * (w_n796 x).toNat + 4 * (w_n797 x).toNat + (w_n798 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n800 x).toNat + (w_n801 x).toNat + 2 * (w_n802 x).toNat + 4 * (w_n803 x).toNat + 2 * (w_n804 x).toNat + 4 * (w_n805 x).toNat + 8 * (w_n806 x).toNat + 4 * (w_n807 x).toNat + 8 * (w_n808 x).toNat + 16 * (w_n809 x).toNat)) + ((w_n810 x).toNat + 2 * (w_n811 x).toNat + 4 * (w_n812 x).toNat)) + (2 * (w_n813 x).toNat + 4 * (w_n814 x).toNat + 8 * (w_n815 x).toNat)) + (4 * (w_n816 x).toNat + 8 * (w_n817 x).toNat + 16 * (w_n818 x).toNat)) + (4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 16 * (w_n821 x).toNat)) + (8 * (w_n822 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n824 x).toNat)) = (16 * (w_n776 x).toNat + 2 * (w_n802 x).toNat + 2 * (w_n804 x).toNat + 16 * (w_n809 x).toNat + (w_n810 x).toNat + 2 * (w_n811 x).toNat + 2 * (w_n813 x).toNat + 4 * (w_n816 x).toNat + 16 * (w_n818 x).toNat + 4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 16 * (w_n821 x).toNat + 8 * (w_n822 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n824 x).toNat) + ((w_n762 x).toNat + (w_n765 x).toNat + (w_n768 x).toNat + (w_n795 x).toNat + (w_n798 x).toNat + (w_n801 x).toNat + 2 * (w_n763 x).toNat + 2 * (w_n766 x).toNat + 2 * (w_n769 x).toNat + 2 * (w_n771 x).toNat + 2 * (w_n796 x).toNat + 2 * (w_n799 x).toNat + 4 * (w_n764 x).toNat + 4 * (w_n767 x).toNat + 4 * (w_n770 x).toNat + 4 * (w_n772 x).toNat + 4 * (w_n774 x).toNat + 4 * (w_n797 x).toNat + 4 * (w_n800 x).toNat + 4 * (w_n803 x).toNat + 4 * (w_n805 x).toNat + 4 * (w_n807 x).toNat + 4 * (w_n812 x).toNat + 4 * (w_n814 x).toNat + 8 * (w_n773 x).toNat + 8 * (w_n775 x).toNat + 8 * (w_n806 x).toNat + 8 * (w_n808 x).toNat + 8 * (w_n815 x).toNat + 8 * (w_n817 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s298 (x : Nat → Bool) : I_t298 x = pc x 271 96 := by
  have hl := s282 x
  have hr := s297 x
  have : pc x 271 96 = pc x 271 48 + pc x 319 48 := pc_add x 271 48 48
  unfold I_t298
  omega
def I_b299 (x : Nat → Bool) : Nat := 0 + (x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat
theorem b299 (x : Nat → Bool) : I_b299 x = (x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat := by
  unfold I_b299
  omega
def I_t299 (x : Nat → Bool) : Nat := I_b299 x
theorem t299 (x : Nat → Bool) : I_t299 x = (w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat := by
  have hs : ((I_b299 x) + ((x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat)) = (((x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat) + ((w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat)) := (add_eq (b299 x) (e276 x))
  have e1 : ((I_b299 x) + ((x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat)) = (I_t299 x) + ((x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat) := by unfold I_t299; ac_rfl
  have e2 : (((x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat) + ((w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat)) = ((w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat) + ((x 433).toNat + (x 434).toNat + (x 435).toNat + (x 436).toNat + (x 437).toNat + (x 438).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s299 (x : Nat → Bool) : I_t299 x = pc x 433 6 := rfl
def I_b300 (x : Nat → Bool) : Nat := 0 + (x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat
theorem b300 (x : Nat → Bool) : I_b300 x = (x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat := by
  unfold I_b300
  omega
def I_t300 (x : Nat → Bool) : Nat := I_b300 x
theorem t300 (x : Nat → Bool) : I_t300 x = (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat := by
  have hs : ((I_b300 x) + ((x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat)) = (((x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat) + ((w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat)) := (add_eq (b300 x) (e277 x))
  have e1 : ((I_b300 x) + ((x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat)) = (I_t300 x) + ((x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat) := by unfold I_t300; ac_rfl
  have e2 : (((x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat) + ((w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat)) = ((w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat) + ((x 427).toNat + (x 428).toNat + (x 429).toNat + (x 430).toNat + (x 431).toNat + (x 432).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s300 (x : Nat → Bool) : I_t300 x = pc x 427 6 := rfl
def I_t301 (x : Nat → Bool) : Nat := I_t299 x + I_t300 x
theorem t301 (x : Nat → Bool) : I_t301 x = (w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat + (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat := by
  have hs : ((I_t299 x) + (I_t300 x)) = (((w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat) + ((w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat)) := (add_eq (t299 x) (t300 x))
  have e1 : ((I_t299 x) + (I_t300 x)) = I_t301 x := by unfold I_t301; ac_rfl
  have e2 : (((w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat) + ((w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat)) = (w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat + (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s301 (x : Nat → Bool) : I_t301 x = pc x 427 12 := by
  have hl := s299 x
  have hr := s300 x
  have : pc x 427 12 = pc x 427 6 + pc x 433 6 := pc_add x 427 6 6
  unfold I_t301
  omega
def I_b302 (x : Nat → Bool) : Nat := 0 + (x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat
theorem b302 (x : Nat → Bool) : I_b302 x = (x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat := by
  unfold I_b302
  omega
def I_t302 (x : Nat → Bool) : Nat := I_b302 x
theorem t302 (x : Nat → Bool) : I_t302 x = (w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat := by
  have hs : ((I_b302 x) + ((x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat)) = (((x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat) + ((w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat)) := (add_eq (b302 x) (e278 x))
  have e1 : ((I_b302 x) + ((x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat)) = (I_t302 x) + ((x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat) := by unfold I_t302; ac_rfl
  have e2 : (((x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat) + ((w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat)) = ((w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat) + ((x 421).toNat + (x 422).toNat + (x 423).toNat + (x 424).toNat + (x 425).toNat + (x 426).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s302 (x : Nat → Bool) : I_t302 x = pc x 421 6 := rfl
def I_b303 (x : Nat → Bool) : Nat := 0 + (x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat
theorem b303 (x : Nat → Bool) : I_b303 x = (x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat := by
  unfold I_b303
  omega
def I_t303 (x : Nat → Bool) : Nat := I_b303 x
theorem t303 (x : Nat → Bool) : I_t303 x = (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat := by
  have hs : ((I_b303 x) + ((x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat)) = (((x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat) + ((w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat)) := (add_eq (b303 x) (e279 x))
  have e1 : ((I_b303 x) + ((x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat)) = (I_t303 x) + ((x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat) := by unfold I_t303; ac_rfl
  have e2 : (((x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat) + ((w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat)) = ((w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat) + ((x 415).toNat + (x 416).toNat + (x 417).toNat + (x 418).toNat + (x 419).toNat + (x 420).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s303 (x : Nat → Bool) : I_t303 x = pc x 415 6 := rfl
def I_t304 (x : Nat → Bool) : Nat := I_t302 x + I_t303 x
theorem t304 (x : Nat → Bool) : I_t304 x = (w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat + (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat := by
  have hs : ((I_t302 x) + (I_t303 x)) = (((w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat) + ((w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat)) := (add_eq (t302 x) (t303 x))
  have e1 : ((I_t302 x) + (I_t303 x)) = I_t304 x := by unfold I_t304; ac_rfl
  have e2 : (((w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat) + ((w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat)) = (w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat + (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s304 (x : Nat → Bool) : I_t304 x = pc x 415 12 := by
  have hl := s302 x
  have hr := s303 x
  have : pc x 415 12 = pc x 415 6 + pc x 421 6 := pc_add x 415 6 6
  unfold I_t304
  omega
def I_t305 (x : Nat → Bool) : Nat := I_t301 x + I_t304 x
theorem t305 (x : Nat → Bool) : I_t305 x = (w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat + (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat + (w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat + (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat := by
  have hs : ((I_t301 x) + (I_t304 x)) = (((w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat + (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat) + ((w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat + (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat)) := (add_eq (t301 x) (t304 x))
  have e1 : ((I_t301 x) + (I_t304 x)) = I_t305 x := by unfold I_t305; ac_rfl
  have e2 : (((w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat + (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat) + ((w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat + (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat)) = (w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat + (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat + (w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat + (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s305 (x : Nat → Bool) : I_t305 x = pc x 415 24 := by
  have hl := s301 x
  have hr := s304 x
  have : pc x 415 24 = pc x 415 12 + pc x 427 12 := pc_add x 415 12 12
  unfold I_t305
  omega
def I_b306 (x : Nat → Bool) : Nat := 0 + (x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat
theorem b306 (x : Nat → Bool) : I_b306 x = (x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat := by
  unfold I_b306
  omega
def I_t306 (x : Nat → Bool) : Nat := I_b306 x
theorem t306 (x : Nat → Bool) : I_t306 x = (w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat := by
  have hs : ((I_b306 x) + ((x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat)) = (((x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat) + ((w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat)) := (add_eq (b306 x) (e280 x))
  have e1 : ((I_b306 x) + ((x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat)) = (I_t306 x) + ((x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat) := by unfold I_t306; ac_rfl
  have e2 : (((x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat) + ((w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat)) = ((w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat) + ((x 457).toNat + (x 458).toNat + (x 459).toNat + (x 460).toNat + (x 461).toNat + (x 462).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s306 (x : Nat → Bool) : I_t306 x = pc x 457 6 := rfl
def I_b307 (x : Nat → Bool) : Nat := 0 + (x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat
theorem b307 (x : Nat → Bool) : I_b307 x = (x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat := by
  unfold I_b307
  omega
def I_t307 (x : Nat → Bool) : Nat := I_b307 x
theorem t307 (x : Nat → Bool) : I_t307 x = (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat := by
  have hs : ((I_b307 x) + ((x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat)) = (((x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat) + ((w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat)) := (add_eq (b307 x) (e281 x))
  have e1 : ((I_b307 x) + ((x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat)) = (I_t307 x) + ((x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat) := by unfold I_t307; ac_rfl
  have e2 : (((x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat) + ((w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat)) = ((w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat) + ((x 451).toNat + (x 452).toNat + (x 453).toNat + (x 454).toNat + (x 455).toNat + (x 456).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s307 (x : Nat → Bool) : I_t307 x = pc x 451 6 := rfl
def I_t308 (x : Nat → Bool) : Nat := I_t306 x + I_t307 x
theorem t308 (x : Nat → Bool) : I_t308 x = (w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat + (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat := by
  have hs : ((I_t306 x) + (I_t307 x)) = (((w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat) + ((w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat)) := (add_eq (t306 x) (t307 x))
  have e1 : ((I_t306 x) + (I_t307 x)) = I_t308 x := by unfold I_t308; ac_rfl
  have e2 : (((w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat) + ((w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat)) = (w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat + (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s308 (x : Nat → Bool) : I_t308 x = pc x 451 12 := by
  have hl := s306 x
  have hr := s307 x
  have : pc x 451 12 = pc x 451 6 + pc x 457 6 := pc_add x 451 6 6
  unfold I_t308
  omega
def I_b309 (x : Nat → Bool) : Nat := 0 + (x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat
theorem b309 (x : Nat → Bool) : I_b309 x = (x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat := by
  unfold I_b309
  omega
def I_t309 (x : Nat → Bool) : Nat := I_b309 x
theorem t309 (x : Nat → Bool) : I_t309 x = (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat := by
  have hs : ((I_b309 x) + ((x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat)) = (((x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat) + ((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat)) := (add_eq (b309 x) (e282 x))
  have e1 : ((I_b309 x) + ((x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat)) = (I_t309 x) + ((x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat) := by unfold I_t309; ac_rfl
  have e2 : (((x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat) + ((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat)) = ((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat) + ((x 439).toNat + (x 440).toNat + (x 441).toNat + (x 442).toNat + (x 443).toNat + (x 444).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s309 (x : Nat → Bool) : I_t309 x = pc x 439 6 := rfl
def I_b310 (x : Nat → Bool) : Nat := 0 + (x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat
theorem b310 (x : Nat → Bool) : I_b310 x = (x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat := by
  unfold I_b310
  omega
def I_t310 (x : Nat → Bool) : Nat := I_b310 x
theorem t310 (x : Nat → Bool) : I_t310 x = (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat := by
  have hs : ((I_b310 x) + ((x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat)) = (((x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat) + ((w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat)) := (add_eq (b310 x) (e283 x))
  have e1 : ((I_b310 x) + ((x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat)) = (I_t310 x) + ((x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat) := by unfold I_t310; ac_rfl
  have e2 : (((x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat) + ((w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat)) = ((w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat) + ((x 445).toNat + (x 446).toNat + (x 447).toNat + (x 448).toNat + (x 449).toNat + (x 450).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s310 (x : Nat → Bool) : I_t310 x = pc x 445 6 := rfl
def I_t311 (x : Nat → Bool) : Nat := I_t309 x + I_t310 x
theorem t311 (x : Nat → Bool) : I_t311 x = (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat := by
  have hs : ((I_t309 x) + (I_t310 x)) = (((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat) + ((w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat)) := (add_eq (t309 x) (t310 x))
  have e1 : ((I_t309 x) + (I_t310 x)) = I_t311 x := by unfold I_t311; ac_rfl
  have e2 : (((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat) + ((w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat)) = (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s311 (x : Nat → Bool) : I_t311 x = pc x 439 12 := by
  have hl := s309 x
  have hr := s310 x
  have : pc x 439 12 = pc x 439 6 + pc x 445 6 := pc_add x 439 6 6
  unfold I_t311
  omega
def I_t312 (x : Nat → Bool) : Nat := I_t308 x + I_t311 x
theorem t312 (x : Nat → Bool) : I_t312 x = (w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat + (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat + (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat := by
  have hs : ((I_t308 x) + (I_t311 x)) = (((w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat + (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat) + ((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat)) := (add_eq (t308 x) (t311 x))
  have e1 : ((I_t308 x) + (I_t311 x)) = I_t312 x := by unfold I_t312; ac_rfl
  have e2 : (((w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat + (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat) + ((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat)) = (w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat + (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat + (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s312 (x : Nat → Bool) : I_t312 x = pc x 439 24 := by
  have hl := s308 x
  have hr := s311 x
  have : pc x 439 24 = pc x 439 12 + pc x 451 12 := pc_add x 439 12 12
  unfold I_t312
  omega
def I_t313 (x : Nat → Bool) : Nat := I_t305 x + I_t312 x
theorem t313 (x : Nat → Bool) : I_t313 x = (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat + (w_n849 x).toNat + 2 * (w_n850 x).toNat + 4 * (w_n851 x).toNat + 2 * (w_n852 x).toNat + 4 * (w_n853 x).toNat + 8 * (w_n854 x).toNat + 4 * (w_n855 x).toNat + 8 * (w_n856 x).toNat + 16 * (w_n857 x).toNat := by
  have hs : (((((I_t305 x) + (I_t312 x)) + ((w_n825 x).toNat + (w_n828 x).toNat + (w_n831 x).toNat + (w_n834 x).toNat + (w_n837 x).toNat + (w_n840 x).toNat)) + (2 * (w_n826 x).toNat + 2 * (w_n829 x).toNat + 2 * (w_n832 x).toNat + 2 * (w_n835 x).toNat + 2 * (w_n838 x).toNat + 2 * (w_n841 x).toNat)) + (4 * (w_n827 x).toNat + 4 * (w_n830 x).toNat + 4 * (w_n833 x).toNat + 4 * (w_n836 x).toNat + 4 * (w_n839 x).toNat + 4 * (w_n842 x).toNat)) = ((((((w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat + (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat + (w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat + (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat) + ((w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat + (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat + (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat)) + ((w_n849 x).toNat + 2 * (w_n850 x).toNat + 4 * (w_n851 x).toNat)) + (2 * (w_n852 x).toNat + 4 * (w_n853 x).toNat + 8 * (w_n854 x).toNat)) + (4 * (w_n855 x).toNat + 8 * (w_n856 x).toNat + 16 * (w_n857 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t305 x) (t312 x)) (e284 x)) (e285 x)) (e286 x))
  have e1 : (((((I_t305 x) + (I_t312 x)) + ((w_n825 x).toNat + (w_n828 x).toNat + (w_n831 x).toNat + (w_n834 x).toNat + (w_n837 x).toNat + (w_n840 x).toNat)) + (2 * (w_n826 x).toNat + 2 * (w_n829 x).toNat + 2 * (w_n832 x).toNat + 2 * (w_n835 x).toNat + 2 * (w_n838 x).toNat + 2 * (w_n841 x).toNat)) + (4 * (w_n827 x).toNat + 4 * (w_n830 x).toNat + 4 * (w_n833 x).toNat + 4 * (w_n836 x).toNat + 4 * (w_n839 x).toNat + 4 * (w_n842 x).toNat)) = (I_t313 x) + ((w_n825 x).toNat + (w_n828 x).toNat + (w_n831 x).toNat + (w_n834 x).toNat + (w_n837 x).toNat + (w_n840 x).toNat + 2 * (w_n826 x).toNat + 2 * (w_n829 x).toNat + 2 * (w_n832 x).toNat + 2 * (w_n835 x).toNat + 2 * (w_n838 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n827 x).toNat + 4 * (w_n830 x).toNat + 4 * (w_n833 x).toNat + 4 * (w_n836 x).toNat + 4 * (w_n839 x).toNat + 4 * (w_n842 x).toNat) := by unfold I_t313; ac_rfl
  have e2 : ((((((w_n825 x).toNat + 2 * (w_n826 x).toNat + 4 * (w_n827 x).toNat + (w_n828 x).toNat + 2 * (w_n829 x).toNat + 4 * (w_n830 x).toNat + (w_n831 x).toNat + 2 * (w_n832 x).toNat + 4 * (w_n833 x).toNat + (w_n834 x).toNat + 2 * (w_n835 x).toNat + 4 * (w_n836 x).toNat) + ((w_n837 x).toNat + 2 * (w_n838 x).toNat + 4 * (w_n839 x).toNat + (w_n840 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n842 x).toNat + (w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat)) + ((w_n849 x).toNat + 2 * (w_n850 x).toNat + 4 * (w_n851 x).toNat)) + (2 * (w_n852 x).toNat + 4 * (w_n853 x).toNat + 8 * (w_n854 x).toNat)) + (4 * (w_n855 x).toNat + 8 * (w_n856 x).toNat + 16 * (w_n857 x).toNat)) = ((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat + (w_n849 x).toNat + 2 * (w_n850 x).toNat + 4 * (w_n851 x).toNat + 2 * (w_n852 x).toNat + 4 * (w_n853 x).toNat + 8 * (w_n854 x).toNat + 4 * (w_n855 x).toNat + 8 * (w_n856 x).toNat + 16 * (w_n857 x).toNat) + ((w_n825 x).toNat + (w_n828 x).toNat + (w_n831 x).toNat + (w_n834 x).toNat + (w_n837 x).toNat + (w_n840 x).toNat + 2 * (w_n826 x).toNat + 2 * (w_n829 x).toNat + 2 * (w_n832 x).toNat + 2 * (w_n835 x).toNat + 2 * (w_n838 x).toNat + 2 * (w_n841 x).toNat + 4 * (w_n827 x).toNat + 4 * (w_n830 x).toNat + 4 * (w_n833 x).toNat + 4 * (w_n836 x).toNat + 4 * (w_n839 x).toNat + 4 * (w_n842 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s313 (x : Nat → Bool) : I_t313 x = pc x 415 48 := by
  have hl := s305 x
  have hr := s312 x
  have : pc x 415 48 = pc x 415 24 + pc x 439 24 := pc_add x 415 24 24
  unfold I_t313
  omega
def I_b314 (x : Nat → Bool) : Nat := 0 + (x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat
theorem b314 (x : Nat → Bool) : I_b314 x = (x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat := by
  unfold I_b314
  omega
def I_t314 (x : Nat → Bool) : Nat := I_b314 x
theorem t314 (x : Nat → Bool) : I_t314 x = (w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat := by
  have hs : ((I_b314 x) + ((x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat)) = (((x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat) + ((w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat)) := (add_eq (b314 x) (e287 x))
  have e1 : ((I_b314 x) + ((x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat)) = (I_t314 x) + ((x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat) := by unfold I_t314; ac_rfl
  have e2 : (((x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat) + ((w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat)) = ((w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat) + ((x 379).toNat + (x 380).toNat + (x 381).toNat + (x 382).toNat + (x 383).toNat + (x 384).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s314 (x : Nat → Bool) : I_t314 x = pc x 379 6 := rfl
def I_b315 (x : Nat → Bool) : Nat := 0 + (x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat
theorem b315 (x : Nat → Bool) : I_b315 x = (x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat := by
  unfold I_b315
  omega
def I_t315 (x : Nat → Bool) : Nat := I_b315 x
theorem t315 (x : Nat → Bool) : I_t315 x = (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat := by
  have hs : ((I_b315 x) + ((x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat)) = (((x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat) + ((w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat)) := (add_eq (b315 x) (e288 x))
  have e1 : ((I_b315 x) + ((x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat)) = (I_t315 x) + ((x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat) := by unfold I_t315; ac_rfl
  have e2 : (((x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat) + ((w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat)) = ((w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat) + ((x 385).toNat + (x 386).toNat + (x 387).toNat + (x 388).toNat + (x 389).toNat + (x 390).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s315 (x : Nat → Bool) : I_t315 x = pc x 385 6 := rfl
def I_t316 (x : Nat → Bool) : Nat := I_t314 x + I_t315 x
theorem t316 (x : Nat → Bool) : I_t316 x = (w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat + (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat := by
  have hs : ((I_t314 x) + (I_t315 x)) = (((w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat) + ((w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat)) := (add_eq (t314 x) (t315 x))
  have e1 : ((I_t314 x) + (I_t315 x)) = I_t316 x := by unfold I_t316; ac_rfl
  have e2 : (((w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat) + ((w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat)) = (w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat + (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s316 (x : Nat → Bool) : I_t316 x = pc x 379 12 := by
  have hl := s314 x
  have hr := s315 x
  have : pc x 379 12 = pc x 379 6 + pc x 385 6 := pc_add x 379 6 6
  unfold I_t316
  omega
def I_b317 (x : Nat → Bool) : Nat := 0 + (x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat
theorem b317 (x : Nat → Bool) : I_b317 x = (x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat := by
  unfold I_b317
  omega
def I_t317 (x : Nat → Bool) : Nat := I_b317 x
theorem t317 (x : Nat → Bool) : I_t317 x = (w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat := by
  have hs : ((I_b317 x) + ((x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat)) = (((x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat) + ((w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat)) := (add_eq (b317 x) (e289 x))
  have e1 : ((I_b317 x) + ((x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat)) = (I_t317 x) + ((x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat) := by unfold I_t317; ac_rfl
  have e2 : (((x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat) + ((w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat)) = ((w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat) + ((x 373).toNat + (x 374).toNat + (x 375).toNat + (x 376).toNat + (x 377).toNat + (x 378).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s317 (x : Nat → Bool) : I_t317 x = pc x 373 6 := rfl
def I_b318 (x : Nat → Bool) : Nat := 0 + (x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat
theorem b318 (x : Nat → Bool) : I_b318 x = (x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat := by
  unfold I_b318
  omega
def I_t318 (x : Nat → Bool) : Nat := I_b318 x
theorem t318 (x : Nat → Bool) : I_t318 x = (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat := by
  have hs : ((I_b318 x) + ((x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat)) = (((x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat) + ((w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat)) := (add_eq (b318 x) (e290 x))
  have e1 : ((I_b318 x) + ((x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat)) = (I_t318 x) + ((x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat) := by unfold I_t318; ac_rfl
  have e2 : (((x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat) + ((w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat)) = ((w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat) + ((x 367).toNat + (x 368).toNat + (x 369).toNat + (x 370).toNat + (x 371).toNat + (x 372).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s318 (x : Nat → Bool) : I_t318 x = pc x 367 6 := rfl
def I_t319 (x : Nat → Bool) : Nat := I_t317 x + I_t318 x
theorem t319 (x : Nat → Bool) : I_t319 x = (w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat + (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat := by
  have hs : ((I_t317 x) + (I_t318 x)) = (((w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat) + ((w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat)) := (add_eq (t317 x) (t318 x))
  have e1 : ((I_t317 x) + (I_t318 x)) = I_t319 x := by unfold I_t319; ac_rfl
  have e2 : (((w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat) + ((w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat)) = (w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat + (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s319 (x : Nat → Bool) : I_t319 x = pc x 367 12 := by
  have hl := s317 x
  have hr := s318 x
  have : pc x 367 12 = pc x 367 6 + pc x 373 6 := pc_add x 367 6 6
  unfold I_t319
  omega
def I_t320 (x : Nat → Bool) : Nat := I_t316 x + I_t319 x
theorem t320 (x : Nat → Bool) : I_t320 x = (w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat + (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat + (w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat + (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat := by
  have hs : ((I_t316 x) + (I_t319 x)) = (((w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat + (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat) + ((w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat + (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat)) := (add_eq (t316 x) (t319 x))
  have e1 : ((I_t316 x) + (I_t319 x)) = I_t320 x := by unfold I_t320; ac_rfl
  have e2 : (((w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat + (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat) + ((w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat + (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat)) = (w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat + (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat + (w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat + (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s320 (x : Nat → Bool) : I_t320 x = pc x 367 24 := by
  have hl := s316 x
  have hr := s319 x
  have : pc x 367 24 = pc x 367 12 + pc x 379 12 := pc_add x 367 12 12
  unfold I_t320
  omega
def I_b321 (x : Nat → Bool) : Nat := 0 + (x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat
theorem b321 (x : Nat → Bool) : I_b321 x = (x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat := by
  unfold I_b321
  omega
def I_t321 (x : Nat → Bool) : Nat := I_b321 x
theorem t321 (x : Nat → Bool) : I_t321 x = (w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat := by
  have hs : ((I_b321 x) + ((x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat)) = (((x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat) + ((w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat)) := (add_eq (b321 x) (e291 x))
  have e1 : ((I_b321 x) + ((x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat)) = (I_t321 x) + ((x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat) := by unfold I_t321; ac_rfl
  have e2 : (((x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat) + ((w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat)) = ((w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat) + ((x 403).toNat + (x 404).toNat + (x 405).toNat + (x 406).toNat + (x 407).toNat + (x 408).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s321 (x : Nat → Bool) : I_t321 x = pc x 403 6 := rfl
def I_b322 (x : Nat → Bool) : Nat := 0 + (x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat
theorem b322 (x : Nat → Bool) : I_b322 x = (x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat := by
  unfold I_b322
  omega
def I_t322 (x : Nat → Bool) : Nat := I_b322 x
theorem t322 (x : Nat → Bool) : I_t322 x = (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat := by
  have hs : ((I_b322 x) + ((x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat)) = (((x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat) + ((w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat)) := (add_eq (b322 x) (e292 x))
  have e1 : ((I_b322 x) + ((x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat)) = (I_t322 x) + ((x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat) := by unfold I_t322; ac_rfl
  have e2 : (((x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat) + ((w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat)) = ((w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat) + ((x 409).toNat + (x 410).toNat + (x 411).toNat + (x 412).toNat + (x 413).toNat + (x 414).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s322 (x : Nat → Bool) : I_t322 x = pc x 409 6 := rfl
def I_t323 (x : Nat → Bool) : Nat := I_t321 x + I_t322 x
theorem t323 (x : Nat → Bool) : I_t323 x = (w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat + (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat := by
  have hs : ((I_t321 x) + (I_t322 x)) = (((w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat) + ((w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat)) := (add_eq (t321 x) (t322 x))
  have e1 : ((I_t321 x) + (I_t322 x)) = I_t323 x := by unfold I_t323; ac_rfl
  have e2 : (((w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat) + ((w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat)) = (w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat + (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s323 (x : Nat → Bool) : I_t323 x = pc x 403 12 := by
  have hl := s321 x
  have hr := s322 x
  have : pc x 403 12 = pc x 403 6 + pc x 409 6 := pc_add x 403 6 6
  unfold I_t323
  omega
def I_b324 (x : Nat → Bool) : Nat := 0 + (x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat
theorem b324 (x : Nat → Bool) : I_b324 x = (x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat := by
  unfold I_b324
  omega
def I_t324 (x : Nat → Bool) : Nat := I_b324 x
theorem t324 (x : Nat → Bool) : I_t324 x = (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat := by
  have hs : ((I_b324 x) + ((x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat)) = (((x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat) + ((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat)) := (add_eq (b324 x) (e293 x))
  have e1 : ((I_b324 x) + ((x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat)) = (I_t324 x) + ((x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat) := by unfold I_t324; ac_rfl
  have e2 : (((x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat) + ((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat)) = ((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat) + ((x 391).toNat + (x 392).toNat + (x 393).toNat + (x 394).toNat + (x 395).toNat + (x 396).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s324 (x : Nat → Bool) : I_t324 x = pc x 391 6 := rfl
def I_b325 (x : Nat → Bool) : Nat := 0 + (x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat
theorem b325 (x : Nat → Bool) : I_b325 x = (x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat := by
  unfold I_b325
  omega
def I_t325 (x : Nat → Bool) : Nat := I_b325 x
theorem t325 (x : Nat → Bool) : I_t325 x = (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat := by
  have hs : ((I_b325 x) + ((x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat)) = (((x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat) + ((w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat)) := (add_eq (b325 x) (e294 x))
  have e1 : ((I_b325 x) + ((x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat)) = (I_t325 x) + ((x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat) := by unfold I_t325; ac_rfl
  have e2 : (((x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat) + ((w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat)) = ((w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat) + ((x 397).toNat + (x 398).toNat + (x 399).toNat + (x 400).toNat + (x 401).toNat + (x 402).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s325 (x : Nat → Bool) : I_t325 x = pc x 397 6 := rfl
def I_t326 (x : Nat → Bool) : Nat := I_t324 x + I_t325 x
theorem t326 (x : Nat → Bool) : I_t326 x = (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat := by
  have hs : ((I_t324 x) + (I_t325 x)) = (((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat) + ((w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat)) := (add_eq (t324 x) (t325 x))
  have e1 : ((I_t324 x) + (I_t325 x)) = I_t326 x := by unfold I_t326; ac_rfl
  have e2 : (((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat) + ((w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat)) = (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s326 (x : Nat → Bool) : I_t326 x = pc x 391 12 := by
  have hl := s324 x
  have hr := s325 x
  have : pc x 391 12 = pc x 391 6 + pc x 397 6 := pc_add x 391 6 6
  unfold I_t326
  omega
def I_t327 (x : Nat → Bool) : Nat := I_t323 x + I_t326 x
theorem t327 (x : Nat → Bool) : I_t327 x = (w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat + (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat + (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat := by
  have hs : ((I_t323 x) + (I_t326 x)) = (((w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat + (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat) + ((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat)) := (add_eq (t323 x) (t326 x))
  have e1 : ((I_t323 x) + (I_t326 x)) = I_t327 x := by unfold I_t327; ac_rfl
  have e2 : (((w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat + (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat) + ((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat)) = (w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat + (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat + (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s327 (x : Nat → Bool) : I_t327 x = pc x 391 24 := by
  have hl := s323 x
  have hr := s326 x
  have : pc x 391 24 = pc x 391 12 + pc x 403 12 := pc_add x 391 12 12
  unfold I_t327
  omega
def I_t328 (x : Nat → Bool) : Nat := I_t320 x + I_t327 x
theorem t328 (x : Nat → Bool) : I_t328 x = (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat + (w_n882 x).toNat + 2 * (w_n883 x).toNat + 4 * (w_n884 x).toNat + 2 * (w_n885 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n887 x).toNat + 4 * (w_n888 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n890 x).toNat := by
  have hs : (((((I_t320 x) + (I_t327 x)) + ((w_n858 x).toNat + (w_n861 x).toNat + (w_n864 x).toNat + (w_n867 x).toNat + (w_n870 x).toNat + (w_n873 x).toNat)) + (2 * (w_n859 x).toNat + 2 * (w_n862 x).toNat + 2 * (w_n865 x).toNat + 2 * (w_n868 x).toNat + 2 * (w_n871 x).toNat + 2 * (w_n874 x).toNat)) + (4 * (w_n860 x).toNat + 4 * (w_n863 x).toNat + 4 * (w_n866 x).toNat + 4 * (w_n869 x).toNat + 4 * (w_n872 x).toNat + 4 * (w_n875 x).toNat)) = ((((((w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat + (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat + (w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat + (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat) + ((w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat + (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat + (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat)) + ((w_n882 x).toNat + 2 * (w_n883 x).toNat + 4 * (w_n884 x).toNat)) + (2 * (w_n885 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n887 x).toNat)) + (4 * (w_n888 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n890 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (t320 x) (t327 x)) (e295 x)) (e296 x)) (e297 x))
  have e1 : (((((I_t320 x) + (I_t327 x)) + ((w_n858 x).toNat + (w_n861 x).toNat + (w_n864 x).toNat + (w_n867 x).toNat + (w_n870 x).toNat + (w_n873 x).toNat)) + (2 * (w_n859 x).toNat + 2 * (w_n862 x).toNat + 2 * (w_n865 x).toNat + 2 * (w_n868 x).toNat + 2 * (w_n871 x).toNat + 2 * (w_n874 x).toNat)) + (4 * (w_n860 x).toNat + 4 * (w_n863 x).toNat + 4 * (w_n866 x).toNat + 4 * (w_n869 x).toNat + 4 * (w_n872 x).toNat + 4 * (w_n875 x).toNat)) = (I_t328 x) + ((w_n858 x).toNat + (w_n861 x).toNat + (w_n864 x).toNat + (w_n867 x).toNat + (w_n870 x).toNat + (w_n873 x).toNat + 2 * (w_n859 x).toNat + 2 * (w_n862 x).toNat + 2 * (w_n865 x).toNat + 2 * (w_n868 x).toNat + 2 * (w_n871 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n860 x).toNat + 4 * (w_n863 x).toNat + 4 * (w_n866 x).toNat + 4 * (w_n869 x).toNat + 4 * (w_n872 x).toNat + 4 * (w_n875 x).toNat) := by unfold I_t328; ac_rfl
  have e2 : ((((((w_n858 x).toNat + 2 * (w_n859 x).toNat + 4 * (w_n860 x).toNat + (w_n861 x).toNat + 2 * (w_n862 x).toNat + 4 * (w_n863 x).toNat + (w_n864 x).toNat + 2 * (w_n865 x).toNat + 4 * (w_n866 x).toNat + (w_n867 x).toNat + 2 * (w_n868 x).toNat + 4 * (w_n869 x).toNat) + ((w_n870 x).toNat + 2 * (w_n871 x).toNat + 4 * (w_n872 x).toNat + (w_n873 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n875 x).toNat + (w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat)) + ((w_n882 x).toNat + 2 * (w_n883 x).toNat + 4 * (w_n884 x).toNat)) + (2 * (w_n885 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n887 x).toNat)) + (4 * (w_n888 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n890 x).toNat)) = ((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat + (w_n882 x).toNat + 2 * (w_n883 x).toNat + 4 * (w_n884 x).toNat + 2 * (w_n885 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n887 x).toNat + 4 * (w_n888 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n890 x).toNat) + ((w_n858 x).toNat + (w_n861 x).toNat + (w_n864 x).toNat + (w_n867 x).toNat + (w_n870 x).toNat + (w_n873 x).toNat + 2 * (w_n859 x).toNat + 2 * (w_n862 x).toNat + 2 * (w_n865 x).toNat + 2 * (w_n868 x).toNat + 2 * (w_n871 x).toNat + 2 * (w_n874 x).toNat + 4 * (w_n860 x).toNat + 4 * (w_n863 x).toNat + 4 * (w_n866 x).toNat + 4 * (w_n869 x).toNat + 4 * (w_n872 x).toNat + 4 * (w_n875 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s328 (x : Nat → Bool) : I_t328 x = pc x 367 48 := by
  have hl := s320 x
  have hr := s327 x
  have : pc x 367 48 = pc x 367 24 + pc x 391 24 := pc_add x 367 24 24
  unfold I_t328
  omega
def I_t329 (x : Nat → Bool) : Nat := I_t313 x + I_t328 x
theorem t329 (x : Nat → Bool) : I_t329 x = 16 * (w_n857 x).toNat + 2 * (w_n883 x).toNat + 2 * (w_n885 x).toNat + 16 * (w_n890 x).toNat + (w_n891 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 4 * (w_n897 x).toNat + 16 * (w_n899 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat + 8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat := by
  have hs : (((((((I_t313 x) + (I_t328 x)) + ((w_n843 x).toNat + (w_n846 x).toNat + (w_n849 x).toNat + (w_n876 x).toNat + (w_n879 x).toNat + (w_n882 x).toNat)) + (2 * (w_n844 x).toNat + 2 * (w_n847 x).toNat + 2 * (w_n850 x).toNat + 2 * (w_n852 x).toNat + 2 * (w_n877 x).toNat + 2 * (w_n880 x).toNat)) + (4 * (w_n845 x).toNat + 4 * (w_n848 x).toNat + 4 * (w_n851 x).toNat + 4 * (w_n853 x).toNat + 4 * (w_n855 x).toNat + 4 * (w_n878 x).toNat)) + (4 * (w_n881 x).toNat + 4 * (w_n884 x).toNat + 4 * (w_n886 x).toNat + 4 * (w_n888 x).toNat + 4 * (w_n893 x).toNat + 4 * (w_n895 x).toNat)) + (8 * (w_n854 x).toNat + 8 * (w_n856 x).toNat + 8 * (w_n887 x).toNat + 8 * (w_n889 x).toNat + 8 * (w_n896 x).toNat + 8 * (w_n898 x).toNat)) = ((((((((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat + (w_n849 x).toNat + 2 * (w_n850 x).toNat + 4 * (w_n851 x).toNat + 2 * (w_n852 x).toNat + 4 * (w_n853 x).toNat + 8 * (w_n854 x).toNat + 4 * (w_n855 x).toNat + 8 * (w_n856 x).toNat + 16 * (w_n857 x).toNat) + ((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat + (w_n882 x).toNat + 2 * (w_n883 x).toNat + 4 * (w_n884 x).toNat + 2 * (w_n885 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n887 x).toNat + 4 * (w_n888 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n890 x).toNat)) + ((w_n891 x).toNat + 2 * (w_n892 x).toNat + 4 * (w_n893 x).toNat)) + (2 * (w_n894 x).toNat + 4 * (w_n895 x).toNat + 8 * (w_n896 x).toNat)) + (4 * (w_n897 x).toNat + 8 * (w_n898 x).toNat + 16 * (w_n899 x).toNat)) + (4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat)) + (8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t313 x) (t328 x)) (e298 x)) (e299 x)) (e300 x)) (e301 x)) (e302 x))
  have e1 : (((((((I_t313 x) + (I_t328 x)) + ((w_n843 x).toNat + (w_n846 x).toNat + (w_n849 x).toNat + (w_n876 x).toNat + (w_n879 x).toNat + (w_n882 x).toNat)) + (2 * (w_n844 x).toNat + 2 * (w_n847 x).toNat + 2 * (w_n850 x).toNat + 2 * (w_n852 x).toNat + 2 * (w_n877 x).toNat + 2 * (w_n880 x).toNat)) + (4 * (w_n845 x).toNat + 4 * (w_n848 x).toNat + 4 * (w_n851 x).toNat + 4 * (w_n853 x).toNat + 4 * (w_n855 x).toNat + 4 * (w_n878 x).toNat)) + (4 * (w_n881 x).toNat + 4 * (w_n884 x).toNat + 4 * (w_n886 x).toNat + 4 * (w_n888 x).toNat + 4 * (w_n893 x).toNat + 4 * (w_n895 x).toNat)) + (8 * (w_n854 x).toNat + 8 * (w_n856 x).toNat + 8 * (w_n887 x).toNat + 8 * (w_n889 x).toNat + 8 * (w_n896 x).toNat + 8 * (w_n898 x).toNat)) = (I_t329 x) + ((w_n843 x).toNat + (w_n846 x).toNat + (w_n849 x).toNat + (w_n876 x).toNat + (w_n879 x).toNat + (w_n882 x).toNat + 2 * (w_n844 x).toNat + 2 * (w_n847 x).toNat + 2 * (w_n850 x).toNat + 2 * (w_n852 x).toNat + 2 * (w_n877 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n845 x).toNat + 4 * (w_n848 x).toNat + 4 * (w_n851 x).toNat + 4 * (w_n853 x).toNat + 4 * (w_n855 x).toNat + 4 * (w_n878 x).toNat + 4 * (w_n881 x).toNat + 4 * (w_n884 x).toNat + 4 * (w_n886 x).toNat + 4 * (w_n888 x).toNat + 4 * (w_n893 x).toNat + 4 * (w_n895 x).toNat + 8 * (w_n854 x).toNat + 8 * (w_n856 x).toNat + 8 * (w_n887 x).toNat + 8 * (w_n889 x).toNat + 8 * (w_n896 x).toNat + 8 * (w_n898 x).toNat) := by unfold I_t329; ac_rfl
  have e2 : ((((((((w_n843 x).toNat + 2 * (w_n844 x).toNat + 4 * (w_n845 x).toNat + (w_n846 x).toNat + 2 * (w_n847 x).toNat + 4 * (w_n848 x).toNat + (w_n849 x).toNat + 2 * (w_n850 x).toNat + 4 * (w_n851 x).toNat + 2 * (w_n852 x).toNat + 4 * (w_n853 x).toNat + 8 * (w_n854 x).toNat + 4 * (w_n855 x).toNat + 8 * (w_n856 x).toNat + 16 * (w_n857 x).toNat) + ((w_n876 x).toNat + 2 * (w_n877 x).toNat + 4 * (w_n878 x).toNat + (w_n879 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n881 x).toNat + (w_n882 x).toNat + 2 * (w_n883 x).toNat + 4 * (w_n884 x).toNat + 2 * (w_n885 x).toNat + 4 * (w_n886 x).toNat + 8 * (w_n887 x).toNat + 4 * (w_n888 x).toNat + 8 * (w_n889 x).toNat + 16 * (w_n890 x).toNat)) + ((w_n891 x).toNat + 2 * (w_n892 x).toNat + 4 * (w_n893 x).toNat)) + (2 * (w_n894 x).toNat + 4 * (w_n895 x).toNat + 8 * (w_n896 x).toNat)) + (4 * (w_n897 x).toNat + 8 * (w_n898 x).toNat + 16 * (w_n899 x).toNat)) + (4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat)) + (8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat)) = (16 * (w_n857 x).toNat + 2 * (w_n883 x).toNat + 2 * (w_n885 x).toNat + 16 * (w_n890 x).toNat + (w_n891 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 4 * (w_n897 x).toNat + 16 * (w_n899 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat + 8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat) + ((w_n843 x).toNat + (w_n846 x).toNat + (w_n849 x).toNat + (w_n876 x).toNat + (w_n879 x).toNat + (w_n882 x).toNat + 2 * (w_n844 x).toNat + 2 * (w_n847 x).toNat + 2 * (w_n850 x).toNat + 2 * (w_n852 x).toNat + 2 * (w_n877 x).toNat + 2 * (w_n880 x).toNat + 4 * (w_n845 x).toNat + 4 * (w_n848 x).toNat + 4 * (w_n851 x).toNat + 4 * (w_n853 x).toNat + 4 * (w_n855 x).toNat + 4 * (w_n878 x).toNat + 4 * (w_n881 x).toNat + 4 * (w_n884 x).toNat + 4 * (w_n886 x).toNat + 4 * (w_n888 x).toNat + 4 * (w_n893 x).toNat + 4 * (w_n895 x).toNat + 8 * (w_n854 x).toNat + 8 * (w_n856 x).toNat + 8 * (w_n887 x).toNat + 8 * (w_n889 x).toNat + 8 * (w_n896 x).toNat + 8 * (w_n898 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s329 (x : Nat → Bool) : I_t329 x = pc x 367 96 := by
  have hl := s313 x
  have hr := s328 x
  have : pc x 367 96 = pc x 367 48 + pc x 415 48 := pc_add x 367 48 48
  unfold I_t329
  omega
def I_t330 (x : Nat → Bool) : Nat := I_t298 x + I_t329 x
theorem t330 (x : Nat → Bool) : I_t330 x = (w_n810 x).toNat + 4 * (w_n816 x).toNat + 4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 8 * (w_n822 x).toNat + 32 * (w_n824 x).toNat + 16 * (w_n890 x).toNat + (w_n891 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 4 * (w_n897 x).toNat + 16 * (w_n899 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat + 8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat + 2 * (w_n906 x).toNat + 4 * (w_n907 x).toNat + 8 * (w_n908 x).toNat + 16 * (w_n909 x).toNat + 32 * (w_n910 x).toNat + 64 * (w_n911 x).toNat := by
  have hs : ((((I_t298 x) + (I_t329 x)) + (2 * (w_n802 x).toNat + 2 * (w_n804 x).toNat + 2 * (w_n811 x).toNat + 2 * (w_n813 x).toNat + 2 * (w_n883 x).toNat + 2 * (w_n885 x).toNat)) + (16 * (w_n776 x).toNat + 16 * (w_n809 x).toNat + 16 * (w_n818 x).toNat + 16 * (w_n821 x).toNat + 16 * (w_n823 x).toNat + 16 * (w_n857 x).toNat)) = ((((16 * (w_n776 x).toNat + 2 * (w_n802 x).toNat + 2 * (w_n804 x).toNat + 16 * (w_n809 x).toNat + (w_n810 x).toNat + 2 * (w_n811 x).toNat + 2 * (w_n813 x).toNat + 4 * (w_n816 x).toNat + 16 * (w_n818 x).toNat + 4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 16 * (w_n821 x).toNat + 8 * (w_n822 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n824 x).toNat) + (16 * (w_n857 x).toNat + 2 * (w_n883 x).toNat + 2 * (w_n885 x).toNat + 16 * (w_n890 x).toNat + (w_n891 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 4 * (w_n897 x).toNat + 16 * (w_n899 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat + 8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat)) + (2 * (w_n906 x).toNat + 4 * (w_n907 x).toNat + 8 * (w_n908 x).toNat)) + (16 * (w_n909 x).toNat + 32 * (w_n910 x).toNat + 64 * (w_n911 x).toNat)) := (add_eq (add_eq (add_eq (t298 x) (t329 x)) (e303 x)) (e304 x))
  have e1 : ((((I_t298 x) + (I_t329 x)) + (2 * (w_n802 x).toNat + 2 * (w_n804 x).toNat + 2 * (w_n811 x).toNat + 2 * (w_n813 x).toNat + 2 * (w_n883 x).toNat + 2 * (w_n885 x).toNat)) + (16 * (w_n776 x).toNat + 16 * (w_n809 x).toNat + 16 * (w_n818 x).toNat + 16 * (w_n821 x).toNat + 16 * (w_n823 x).toNat + 16 * (w_n857 x).toNat)) = (I_t330 x) + (2 * (w_n802 x).toNat + 2 * (w_n804 x).toNat + 2 * (w_n811 x).toNat + 2 * (w_n813 x).toNat + 2 * (w_n883 x).toNat + 2 * (w_n885 x).toNat + 16 * (w_n776 x).toNat + 16 * (w_n809 x).toNat + 16 * (w_n818 x).toNat + 16 * (w_n821 x).toNat + 16 * (w_n823 x).toNat + 16 * (w_n857 x).toNat) := by unfold I_t330; ac_rfl
  have e2 : ((((16 * (w_n776 x).toNat + 2 * (w_n802 x).toNat + 2 * (w_n804 x).toNat + 16 * (w_n809 x).toNat + (w_n810 x).toNat + 2 * (w_n811 x).toNat + 2 * (w_n813 x).toNat + 4 * (w_n816 x).toNat + 16 * (w_n818 x).toNat + 4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 16 * (w_n821 x).toNat + 8 * (w_n822 x).toNat + 16 * (w_n823 x).toNat + 32 * (w_n824 x).toNat) + (16 * (w_n857 x).toNat + 2 * (w_n883 x).toNat + 2 * (w_n885 x).toNat + 16 * (w_n890 x).toNat + (w_n891 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 4 * (w_n897 x).toNat + 16 * (w_n899 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat + 8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat)) + (2 * (w_n906 x).toNat + 4 * (w_n907 x).toNat + 8 * (w_n908 x).toNat)) + (16 * (w_n909 x).toNat + 32 * (w_n910 x).toNat + 64 * (w_n911 x).toNat)) = ((w_n810 x).toNat + 4 * (w_n816 x).toNat + 4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 8 * (w_n822 x).toNat + 32 * (w_n824 x).toNat + 16 * (w_n890 x).toNat + (w_n891 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 4 * (w_n897 x).toNat + 16 * (w_n899 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat + 8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat + 2 * (w_n906 x).toNat + 4 * (w_n907 x).toNat + 8 * (w_n908 x).toNat + 16 * (w_n909 x).toNat + 32 * (w_n910 x).toNat + 64 * (w_n911 x).toNat) + (2 * (w_n802 x).toNat + 2 * (w_n804 x).toNat + 2 * (w_n811 x).toNat + 2 * (w_n813 x).toNat + 2 * (w_n883 x).toNat + 2 * (w_n885 x).toNat + 16 * (w_n776 x).toNat + 16 * (w_n809 x).toNat + 16 * (w_n818 x).toNat + 16 * (w_n821 x).toNat + 16 * (w_n823 x).toNat + 16 * (w_n857 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s330 (x : Nat → Bool) : I_t330 x = pc x 271 192 := by
  have hl := s298 x
  have hr := s329 x
  have : pc x 271 192 = pc x 271 96 + pc x 367 96 := pc_add x 271 96 96
  unfold I_t330
  omega
def I_t331 (x : Nat → Bool) : Nat := I_t267 x + I_t330 x
theorem t331 (x : Nat → Bool) : I_t331 x = (w_n642 x).toNat + (w_n723 x).toNat + 64 * (w_n743 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 64 * (w_n911 x).toNat + 2 * (w_n912 x).toNat + 4 * (w_n918 x).toNat + 8 * (w_n919 x).toNat + 8 * (w_n921 x).toNat + 16 * (w_n922 x).toNat + 32 * (w_n923 x).toNat + 8 * (w_n924 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n926 x).toNat + 16 * (w_n927 x).toNat + 32 * (w_n928 x).toNat + 64 * (w_n929 x).toNat + 16 * (w_n930 x).toNat + 32 * (w_n931 x).toNat + 64 * (w_n932 x).toNat + 32 * (w_n933 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat := by
  have hs : ((((((((((I_t267 x) + (I_t330 x)) + (2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 2 * (w_n738 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 2 * (w_n906 x).toNat)) + (4 * (w_n648 x).toNat + 4 * (w_n651 x).toNat + 4 * (w_n729 x).toNat + 4 * (w_n732 x).toNat + 4 * (w_n739 x).toNat + 4 * (w_n816 x).toNat)) + (4 * (w_n819 x).toNat + 4 * (w_n897 x).toNat + 4 * (w_n900 x).toNat + 4 * (w_n907 x).toNat + 4 * (w_n913 x).toNat + 4 * (w_n915 x).toNat)) + (8 * (w_n652 x).toNat + 8 * (w_n654 x).toNat + 8 * (w_n733 x).toNat + 8 * (w_n735 x).toNat + 8 * (w_n740 x).toNat + 8 * (w_n820 x).toNat)) + (8 * (w_n822 x).toNat + 8 * (w_n901 x).toNat + 8 * (w_n903 x).toNat + 8 * (w_n908 x).toNat + 8 * (w_n914 x).toNat + 8 * (w_n916 x).toNat)) + (16 * (w_n722 x).toNat + 16 * (w_n731 x).toNat + 16 * (w_n734 x).toNat + 16 * (w_n736 x).toNat + 16 * (w_n741 x).toNat + 16 * (w_n890 x).toNat)) + (16 * (w_n899 x).toNat + 16 * (w_n902 x).toNat + 16 * (w_n904 x).toNat + 16 * (w_n909 x).toNat + 16 * (w_n917 x).toNat + 16 * (w_n920 x).toNat)) + (32 * (w_n656 x).toNat + 32 * (w_n737 x).toNat + 32 * (w_n742 x).toNat + 32 * (w_n824 x).toNat + 32 * (w_n905 x).toNat + 32 * (w_n910 x).toNat)) = (((((((((((w_n642 x).toNat + 4 * (w_n648 x).toNat + 4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 8 * (w_n654 x).toNat + 32 * (w_n656 x).toNat + 16 * (w_n722 x).toNat + (w_n723 x).toNat + 2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n729 x).toNat + 16 * (w_n731 x).toNat + 4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat + 2 * (w_n738 x).toNat + 4 * (w_n739 x).toNat + 8 * (w_n740 x).toNat + 16 * (w_n741 x).toNat + 32 * (w_n742 x).toNat + 64 * (w_n743 x).toNat) + ((w_n810 x).toNat + 4 * (w_n816 x).toNat + 4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 8 * (w_n822 x).toNat + 32 * (w_n824 x).toNat + 16 * (w_n890 x).toNat + (w_n891 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 4 * (w_n897 x).toNat + 16 * (w_n899 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat + 8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat + 2 * (w_n906 x).toNat + 4 * (w_n907 x).toNat + 8 * (w_n908 x).toNat + 16 * (w_n909 x).toNat + 32 * (w_n910 x).toNat + 64 * (w_n911 x).toNat)) + (2 * (w_n912 x).toNat + 4 * (w_n913 x).toNat + 8 * (w_n914 x).toNat)) + (4 * (w_n915 x).toNat + 8 * (w_n916 x).toNat + 16 * (w_n917 x).toNat)) + (4 * (w_n918 x).toNat + 8 * (w_n919 x).toNat + 16 * (w_n920 x).toNat)) + (8 * (w_n921 x).toNat + 16 * (w_n922 x).toNat + 32 * (w_n923 x).toNat)) + (8 * (w_n924 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n926 x).toNat)) + (16 * (w_n927 x).toNat + 32 * (w_n928 x).toNat + 64 * (w_n929 x).toNat)) + (16 * (w_n930 x).toNat + 32 * (w_n931 x).toNat + 64 * (w_n932 x).toNat)) + (32 * (w_n933 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t267 x) (t330 x)) (e305 x)) (e306 x)) (e307 x)) (e308 x)) (e309 x)) (e310 x)) (e311 x)) (e312 x))
  have e1 : ((((((((((I_t267 x) + (I_t330 x)) + (2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 2 * (w_n738 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 2 * (w_n906 x).toNat)) + (4 * (w_n648 x).toNat + 4 * (w_n651 x).toNat + 4 * (w_n729 x).toNat + 4 * (w_n732 x).toNat + 4 * (w_n739 x).toNat + 4 * (w_n816 x).toNat)) + (4 * (w_n819 x).toNat + 4 * (w_n897 x).toNat + 4 * (w_n900 x).toNat + 4 * (w_n907 x).toNat + 4 * (w_n913 x).toNat + 4 * (w_n915 x).toNat)) + (8 * (w_n652 x).toNat + 8 * (w_n654 x).toNat + 8 * (w_n733 x).toNat + 8 * (w_n735 x).toNat + 8 * (w_n740 x).toNat + 8 * (w_n820 x).toNat)) + (8 * (w_n822 x).toNat + 8 * (w_n901 x).toNat + 8 * (w_n903 x).toNat + 8 * (w_n908 x).toNat + 8 * (w_n914 x).toNat + 8 * (w_n916 x).toNat)) + (16 * (w_n722 x).toNat + 16 * (w_n731 x).toNat + 16 * (w_n734 x).toNat + 16 * (w_n736 x).toNat + 16 * (w_n741 x).toNat + 16 * (w_n890 x).toNat)) + (16 * (w_n899 x).toNat + 16 * (w_n902 x).toNat + 16 * (w_n904 x).toNat + 16 * (w_n909 x).toNat + 16 * (w_n917 x).toNat + 16 * (w_n920 x).toNat)) + (32 * (w_n656 x).toNat + 32 * (w_n737 x).toNat + 32 * (w_n742 x).toNat + 32 * (w_n824 x).toNat + 32 * (w_n905 x).toNat + 32 * (w_n910 x).toNat)) = (I_t331 x) + (2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 2 * (w_n738 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 2 * (w_n906 x).toNat + 4 * (w_n648 x).toNat + 4 * (w_n651 x).toNat + 4 * (w_n729 x).toNat + 4 * (w_n732 x).toNat + 4 * (w_n739 x).toNat + 4 * (w_n816 x).toNat + 4 * (w_n819 x).toNat + 4 * (w_n897 x).toNat + 4 * (w_n900 x).toNat + 4 * (w_n907 x).toNat + 4 * (w_n913 x).toNat + 4 * (w_n915 x).toNat + 8 * (w_n652 x).toNat + 8 * (w_n654 x).toNat + 8 * (w_n733 x).toNat + 8 * (w_n735 x).toNat + 8 * (w_n740 x).toNat + 8 * (w_n820 x).toNat + 8 * (w_n822 x).toNat + 8 * (w_n901 x).toNat + 8 * (w_n903 x).toNat + 8 * (w_n908 x).toNat + 8 * (w_n914 x).toNat + 8 * (w_n916 x).toNat + 16 * (w_n722 x).toNat + 16 * (w_n731 x).toNat + 16 * (w_n734 x).toNat + 16 * (w_n736 x).toNat + 16 * (w_n741 x).toNat + 16 * (w_n890 x).toNat + 16 * (w_n899 x).toNat + 16 * (w_n902 x).toNat + 16 * (w_n904 x).toNat + 16 * (w_n909 x).toNat + 16 * (w_n917 x).toNat + 16 * (w_n920 x).toNat + 32 * (w_n656 x).toNat + 32 * (w_n737 x).toNat + 32 * (w_n742 x).toNat + 32 * (w_n824 x).toNat + 32 * (w_n905 x).toNat + 32 * (w_n910 x).toNat) := by unfold I_t331; ac_rfl
  have e2 : (((((((((((w_n642 x).toNat + 4 * (w_n648 x).toNat + 4 * (w_n651 x).toNat + 8 * (w_n652 x).toNat + 8 * (w_n654 x).toNat + 32 * (w_n656 x).toNat + 16 * (w_n722 x).toNat + (w_n723 x).toNat + 2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 4 * (w_n729 x).toNat + 16 * (w_n731 x).toNat + 4 * (w_n732 x).toNat + 8 * (w_n733 x).toNat + 16 * (w_n734 x).toNat + 8 * (w_n735 x).toNat + 16 * (w_n736 x).toNat + 32 * (w_n737 x).toNat + 2 * (w_n738 x).toNat + 4 * (w_n739 x).toNat + 8 * (w_n740 x).toNat + 16 * (w_n741 x).toNat + 32 * (w_n742 x).toNat + 64 * (w_n743 x).toNat) + ((w_n810 x).toNat + 4 * (w_n816 x).toNat + 4 * (w_n819 x).toNat + 8 * (w_n820 x).toNat + 8 * (w_n822 x).toNat + 32 * (w_n824 x).toNat + 16 * (w_n890 x).toNat + (w_n891 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 4 * (w_n897 x).toNat + 16 * (w_n899 x).toNat + 4 * (w_n900 x).toNat + 8 * (w_n901 x).toNat + 16 * (w_n902 x).toNat + 8 * (w_n903 x).toNat + 16 * (w_n904 x).toNat + 32 * (w_n905 x).toNat + 2 * (w_n906 x).toNat + 4 * (w_n907 x).toNat + 8 * (w_n908 x).toNat + 16 * (w_n909 x).toNat + 32 * (w_n910 x).toNat + 64 * (w_n911 x).toNat)) + (2 * (w_n912 x).toNat + 4 * (w_n913 x).toNat + 8 * (w_n914 x).toNat)) + (4 * (w_n915 x).toNat + 8 * (w_n916 x).toNat + 16 * (w_n917 x).toNat)) + (4 * (w_n918 x).toNat + 8 * (w_n919 x).toNat + 16 * (w_n920 x).toNat)) + (8 * (w_n921 x).toNat + 16 * (w_n922 x).toNat + 32 * (w_n923 x).toNat)) + (8 * (w_n924 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n926 x).toNat)) + (16 * (w_n927 x).toNat + 32 * (w_n928 x).toNat + 64 * (w_n929 x).toNat)) + (16 * (w_n930 x).toNat + 32 * (w_n931 x).toNat + 64 * (w_n932 x).toNat)) + (32 * (w_n933 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat)) = ((w_n642 x).toNat + (w_n723 x).toNat + 64 * (w_n743 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 64 * (w_n911 x).toNat + 2 * (w_n912 x).toNat + 4 * (w_n918 x).toNat + 8 * (w_n919 x).toNat + 8 * (w_n921 x).toNat + 16 * (w_n922 x).toNat + 32 * (w_n923 x).toNat + 8 * (w_n924 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n926 x).toNat + 16 * (w_n927 x).toNat + 32 * (w_n928 x).toNat + 64 * (w_n929 x).toNat + 16 * (w_n930 x).toNat + 32 * (w_n931 x).toNat + 64 * (w_n932 x).toNat + 32 * (w_n933 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat) + (2 * (w_n724 x).toNat + 2 * (w_n726 x).toNat + 2 * (w_n738 x).toNat + 2 * (w_n892 x).toNat + 2 * (w_n894 x).toNat + 2 * (w_n906 x).toNat + 4 * (w_n648 x).toNat + 4 * (w_n651 x).toNat + 4 * (w_n729 x).toNat + 4 * (w_n732 x).toNat + 4 * (w_n739 x).toNat + 4 * (w_n816 x).toNat + 4 * (w_n819 x).toNat + 4 * (w_n897 x).toNat + 4 * (w_n900 x).toNat + 4 * (w_n907 x).toNat + 4 * (w_n913 x).toNat + 4 * (w_n915 x).toNat + 8 * (w_n652 x).toNat + 8 * (w_n654 x).toNat + 8 * (w_n733 x).toNat + 8 * (w_n735 x).toNat + 8 * (w_n740 x).toNat + 8 * (w_n820 x).toNat + 8 * (w_n822 x).toNat + 8 * (w_n901 x).toNat + 8 * (w_n903 x).toNat + 8 * (w_n908 x).toNat + 8 * (w_n914 x).toNat + 8 * (w_n916 x).toNat + 16 * (w_n722 x).toNat + 16 * (w_n731 x).toNat + 16 * (w_n734 x).toNat + 16 * (w_n736 x).toNat + 16 * (w_n741 x).toNat + 16 * (w_n890 x).toNat + 16 * (w_n899 x).toNat + 16 * (w_n902 x).toNat + 16 * (w_n904 x).toNat + 16 * (w_n909 x).toNat + 16 * (w_n917 x).toNat + 16 * (w_n920 x).toNat + 32 * (w_n656 x).toNat + 32 * (w_n737 x).toNat + 32 * (w_n742 x).toNat + 32 * (w_n824 x).toNat + 32 * (w_n905 x).toNat + 32 * (w_n910 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s331 (x : Nat → Bool) : I_t331 x = pc x 79 384 := by
  have hl := s267 x
  have hr := s330 x
  have : pc x 79 384 = pc x 79 192 + pc x 271 192 := pc_add x 79 192 192
  unfold I_t331
  omega
def I_t332 (x : Nat → Bool) : Nat := I_t204 x + I_t331 x
theorem t332 (x : Nat → Bool) : I_t332 x = 2 * (w_n570 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 2 * (w_n912 x).toNat + 8 * (w_n921 x).toNat + 8 * (w_n924 x).toNat + 16 * (w_n930 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n940 x).toNat + 16 * (w_n941 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 64 * (w_n947 x).toNat + 32 * (w_n948 x).toNat + 64 * (w_n949 x).toNat + 128 * (w_n950 x).toNat + 32 * (w_n951 x).toNat + 64 * (w_n952 x).toNat + 128 * (w_n953 x).toNat + 64 * (w_n954 x).toNat + 128 * (w_n955 x).toNat + 256 * (w_n956 x).toNat := by
  have hs : (((((((((I_t204 x) + (I_t331 x)) + ((w_n427 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + (w_n552 x).toNat + (w_n642 x).toNat + (w_n723 x).toNat)) + (4 * (w_n433 x).toNat + 4 * (w_n436 x).toNat + 4 * (w_n561 x).toNat + 4 * (w_n571 x).toNat + 4 * (w_n918 x).toNat + 4 * (w_n938 x).toNat)) + (8 * (w_n437 x).toNat + 8 * (w_n439 x).toNat + 8 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 8 * (w_n572 x).toNat + 8 * (w_n919 x).toNat)) + (16 * (w_n565 x).toNat + 16 * (w_n567 x).toNat + 16 * (w_n573 x).toNat + 16 * (w_n922 x).toNat + 16 * (w_n925 x).toNat + 16 * (w_n927 x).toNat)) + (32 * (w_n441 x).toNat + 32 * (w_n551 x).toNat + 32 * (w_n566 x).toNat + 32 * (w_n568 x).toNat + 32 * (w_n574 x).toNat + 32 * (w_n923 x).toNat)) + (32 * (w_n926 x).toNat + 32 * (w_n928 x).toNat + 32 * (w_n931 x).toNat + 32 * (w_n933 x).toNat + 32 * (w_n944 x).toNat + 32 * (w_n946 x).toNat)) + (64 * (w_n569 x).toNat + 64 * (w_n575 x).toNat + 64 * (w_n743 x).toNat + 64 * (w_n911 x).toNat + 64 * (w_n929 x).toNat + 64 * (w_n932 x).toNat)) = ((((((((((w_n427 x).toNat + 4 * (w_n433 x).toNat + 4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 8 * (w_n439 x).toNat + 32 * (w_n441 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + 32 * (w_n551 x).toNat + (w_n552 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat + 16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat + 2 * (w_n570 x).toNat + 4 * (w_n571 x).toNat + 8 * (w_n572 x).toNat + 16 * (w_n573 x).toNat + 32 * (w_n574 x).toNat + 64 * (w_n575 x).toNat) + ((w_n642 x).toNat + (w_n723 x).toNat + 64 * (w_n743 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 64 * (w_n911 x).toNat + 2 * (w_n912 x).toNat + 4 * (w_n918 x).toNat + 8 * (w_n919 x).toNat + 8 * (w_n921 x).toNat + 16 * (w_n922 x).toNat + 32 * (w_n923 x).toNat + 8 * (w_n924 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n926 x).toNat + 16 * (w_n927 x).toNat + 32 * (w_n928 x).toNat + 64 * (w_n929 x).toNat + 16 * (w_n930 x).toNat + 32 * (w_n931 x).toNat + 64 * (w_n932 x).toNat + 32 * (w_n933 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat)) + ((w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n938 x).toNat)) + (4 * (w_n939 x).toNat + 8 * (w_n940 x).toNat + 16 * (w_n941 x).toNat)) + (8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 32 * (w_n944 x).toNat)) + (16 * (w_n945 x).toNat + 32 * (w_n946 x).toNat + 64 * (w_n947 x).toNat)) + (32 * (w_n948 x).toNat + 64 * (w_n949 x).toNat + 128 * (w_n950 x).toNat)) + (32 * (w_n951 x).toNat + 64 * (w_n952 x).toNat + 128 * (w_n953 x).toNat)) + (64 * (w_n954 x).toNat + 128 * (w_n955 x).toNat + 256 * (w_n956 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t204 x) (t331 x)) (e313 x)) (e314 x)) (e315 x)) (e316 x)) (e317 x)) (e318 x)) (e319 x))
  have e1 : (((((((((I_t204 x) + (I_t331 x)) + ((w_n427 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + (w_n552 x).toNat + (w_n642 x).toNat + (w_n723 x).toNat)) + (4 * (w_n433 x).toNat + 4 * (w_n436 x).toNat + 4 * (w_n561 x).toNat + 4 * (w_n571 x).toNat + 4 * (w_n918 x).toNat + 4 * (w_n938 x).toNat)) + (8 * (w_n437 x).toNat + 8 * (w_n439 x).toNat + 8 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 8 * (w_n572 x).toNat + 8 * (w_n919 x).toNat)) + (16 * (w_n565 x).toNat + 16 * (w_n567 x).toNat + 16 * (w_n573 x).toNat + 16 * (w_n922 x).toNat + 16 * (w_n925 x).toNat + 16 * (w_n927 x).toNat)) + (32 * (w_n441 x).toNat + 32 * (w_n551 x).toNat + 32 * (w_n566 x).toNat + 32 * (w_n568 x).toNat + 32 * (w_n574 x).toNat + 32 * (w_n923 x).toNat)) + (32 * (w_n926 x).toNat + 32 * (w_n928 x).toNat + 32 * (w_n931 x).toNat + 32 * (w_n933 x).toNat + 32 * (w_n944 x).toNat + 32 * (w_n946 x).toNat)) + (64 * (w_n569 x).toNat + 64 * (w_n575 x).toNat + 64 * (w_n743 x).toNat + 64 * (w_n911 x).toNat + 64 * (w_n929 x).toNat + 64 * (w_n932 x).toNat)) = (I_t332 x) + ((w_n427 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + (w_n552 x).toNat + (w_n642 x).toNat + (w_n723 x).toNat + 4 * (w_n433 x).toNat + 4 * (w_n436 x).toNat + 4 * (w_n561 x).toNat + 4 * (w_n571 x).toNat + 4 * (w_n918 x).toNat + 4 * (w_n938 x).toNat + 8 * (w_n437 x).toNat + 8 * (w_n439 x).toNat + 8 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 8 * (w_n572 x).toNat + 8 * (w_n919 x).toNat + 16 * (w_n565 x).toNat + 16 * (w_n567 x).toNat + 16 * (w_n573 x).toNat + 16 * (w_n922 x).toNat + 16 * (w_n925 x).toNat + 16 * (w_n927 x).toNat + 32 * (w_n441 x).toNat + 32 * (w_n551 x).toNat + 32 * (w_n566 x).toNat + 32 * (w_n568 x).toNat + 32 * (w_n574 x).toNat + 32 * (w_n923 x).toNat + 32 * (w_n926 x).toNat + 32 * (w_n928 x).toNat + 32 * (w_n931 x).toNat + 32 * (w_n933 x).toNat + 32 * (w_n944 x).toNat + 32 * (w_n946 x).toNat + 64 * (w_n569 x).toNat + 64 * (w_n575 x).toNat + 64 * (w_n743 x).toNat + 64 * (w_n911 x).toNat + 64 * (w_n929 x).toNat + 64 * (w_n932 x).toNat) := by unfold I_t332; ac_rfl
  have e2 : ((((((((((w_n427 x).toNat + 4 * (w_n433 x).toNat + 4 * (w_n436 x).toNat + 8 * (w_n437 x).toNat + 8 * (w_n439 x).toNat + 32 * (w_n441 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + 32 * (w_n551 x).toNat + (w_n552 x).toNat + 4 * (w_n561 x).toNat + 8 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 16 * (w_n565 x).toNat + 32 * (w_n566 x).toNat + 16 * (w_n567 x).toNat + 32 * (w_n568 x).toNat + 64 * (w_n569 x).toNat + 2 * (w_n570 x).toNat + 4 * (w_n571 x).toNat + 8 * (w_n572 x).toNat + 16 * (w_n573 x).toNat + 32 * (w_n574 x).toNat + 64 * (w_n575 x).toNat) + ((w_n642 x).toNat + (w_n723 x).toNat + 64 * (w_n743 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 64 * (w_n911 x).toNat + 2 * (w_n912 x).toNat + 4 * (w_n918 x).toNat + 8 * (w_n919 x).toNat + 8 * (w_n921 x).toNat + 16 * (w_n922 x).toNat + 32 * (w_n923 x).toNat + 8 * (w_n924 x).toNat + 16 * (w_n925 x).toNat + 32 * (w_n926 x).toNat + 16 * (w_n927 x).toNat + 32 * (w_n928 x).toNat + 64 * (w_n929 x).toNat + 16 * (w_n930 x).toNat + 32 * (w_n931 x).toNat + 64 * (w_n932 x).toNat + 32 * (w_n933 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat)) + ((w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n938 x).toNat)) + (4 * (w_n939 x).toNat + 8 * (w_n940 x).toNat + 16 * (w_n941 x).toNat)) + (8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 32 * (w_n944 x).toNat)) + (16 * (w_n945 x).toNat + 32 * (w_n946 x).toNat + 64 * (w_n947 x).toNat)) + (32 * (w_n948 x).toNat + 64 * (w_n949 x).toNat + 128 * (w_n950 x).toNat)) + (32 * (w_n951 x).toNat + 64 * (w_n952 x).toNat + 128 * (w_n953 x).toNat)) + (64 * (w_n954 x).toNat + 128 * (w_n955 x).toNat + 256 * (w_n956 x).toNat)) = (2 * (w_n570 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 2 * (w_n912 x).toNat + 8 * (w_n921 x).toNat + 8 * (w_n924 x).toNat + 16 * (w_n930 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n940 x).toNat + 16 * (w_n941 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 64 * (w_n947 x).toNat + 32 * (w_n948 x).toNat + 64 * (w_n949 x).toNat + 128 * (w_n950 x).toNat + 32 * (w_n951 x).toNat + 64 * (w_n952 x).toNat + 128 * (w_n953 x).toNat + 64 * (w_n954 x).toNat + 128 * (w_n955 x).toNat + 256 * (w_n956 x).toNat) + ((w_n427 x).toNat + (w_n531 x).toNat + (w_n534 x).toNat + (w_n552 x).toNat + (w_n642 x).toNat + (w_n723 x).toNat + 4 * (w_n433 x).toNat + 4 * (w_n436 x).toNat + 4 * (w_n561 x).toNat + 4 * (w_n571 x).toNat + 4 * (w_n918 x).toNat + 4 * (w_n938 x).toNat + 8 * (w_n437 x).toNat + 8 * (w_n439 x).toNat + 8 * (w_n562 x).toNat + 8 * (w_n564 x).toNat + 8 * (w_n572 x).toNat + 8 * (w_n919 x).toNat + 16 * (w_n565 x).toNat + 16 * (w_n567 x).toNat + 16 * (w_n573 x).toNat + 16 * (w_n922 x).toNat + 16 * (w_n925 x).toNat + 16 * (w_n927 x).toNat + 32 * (w_n441 x).toNat + 32 * (w_n551 x).toNat + 32 * (w_n566 x).toNat + 32 * (w_n568 x).toNat + 32 * (w_n574 x).toNat + 32 * (w_n923 x).toNat + 32 * (w_n926 x).toNat + 32 * (w_n928 x).toNat + 32 * (w_n931 x).toNat + 32 * (w_n933 x).toNat + 32 * (w_n944 x).toNat + 32 * (w_n946 x).toNat + 64 * (w_n569 x).toNat + 64 * (w_n575 x).toNat + 64 * (w_n743 x).toNat + 64 * (w_n911 x).toNat + 64 * (w_n929 x).toNat + 64 * (w_n932 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s332 (x : Nat → Bool) : I_t332 x = pc x 0 463 + pc x 847 153 := by
  have hl := s204 x
  have hr := s331 x
  have : pc x 0 463 = pc x 0 79 + pc x 79 384 := pc_add x 0 79 384
  unfold I_t332
  omega
def I_t333 (x : Nat → Bool) : Nat := I_t127 x + I_t332 x
theorem t333 (x : Nat → Bool) : I_t333 x = 2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 32 * (w_n951 x).toNat + 256 * (w_n956 x).toNat + (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat + 16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat := by
  have hs : (((((((((I_t127 x) + (I_t332 x)) + ((w_n67 x).toNat + (w_n148 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat)) + (8 * (w_n344 x).toNat + 8 * (w_n346 x).toNat + 8 * (w_n349 x).toNat + 8 * (w_n921 x).toNat + 8 * (w_n924 x).toNat + 8 * (w_n940 x).toNat)) + (16 * (w_n347 x).toNat + 16 * (w_n350 x).toNat + 16 * (w_n352 x).toNat + 16 * (w_n355 x).toNat + 16 * (w_n930 x).toNat + 16 * (w_n941 x).toNat)) + (32 * (w_n348 x).toNat + 32 * (w_n351 x).toNat + 32 * (w_n353 x).toNat + 32 * (w_n356 x).toNat + 32 * (w_n358 x).toNat + 32 * (w_n948 x).toNat)) + (64 * (w_n168 x).toNat + 64 * (w_n336 x).toNat + 64 * (w_n354 x).toNat + 64 * (w_n357 x).toNat + 64 * (w_n359 x).toNat + 64 * (w_n934 x).toNat)) + (64 * (w_n947 x).toNat + 64 * (w_n949 x).toNat + 64 * (w_n952 x).toNat + 64 * (w_n954 x).toNat + 64 * (w_n965 x).toNat + 64 * (w_n967 x).toNat)) + (128 * (w_n360 x).toNat + 128 * (w_n935 x).toNat + 128 * (w_n950 x).toNat + 128 * (w_n953 x).toNat + 128 * (w_n955 x).toNat + 128 * (w_n968 x).toNat)) = ((((((((((w_n67 x).toNat + (w_n148 x).toNat + 64 * (w_n168 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + 64 * (w_n336 x).toNat + 2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 8 * (w_n344 x).toNat + 8 * (w_n346 x).toNat + 16 * (w_n347 x).toNat + 32 * (w_n348 x).toNat + 8 * (w_n349 x).toNat + 16 * (w_n350 x).toNat + 32 * (w_n351 x).toNat + 16 * (w_n352 x).toNat + 32 * (w_n353 x).toNat + 64 * (w_n354 x).toNat + 16 * (w_n355 x).toNat + 32 * (w_n356 x).toNat + 64 * (w_n357 x).toNat + 32 * (w_n358 x).toNat + 64 * (w_n359 x).toNat + 128 * (w_n360 x).toNat) + (2 * (w_n570 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 2 * (w_n912 x).toNat + 8 * (w_n921 x).toNat + 8 * (w_n924 x).toNat + 16 * (w_n930 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n940 x).toNat + 16 * (w_n941 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 64 * (w_n947 x).toNat + 32 * (w_n948 x).toNat + 64 * (w_n949 x).toNat + 128 * (w_n950 x).toNat + 32 * (w_n951 x).toNat + 64 * (w_n952 x).toNat + 128 * (w_n953 x).toNat + 64 * (w_n954 x).toNat + 128 * (w_n955 x).toNat + 256 * (w_n956 x).toNat)) + ((w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat)) + (8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat)) + (16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 64 * (w_n965 x).toNat)) + (32 * (w_n966 x).toNat + 64 * (w_n967 x).toNat + 128 * (w_n968 x).toNat)) + (64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat)) + (64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat)) + (128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t127 x) (t332 x)) (e320 x)) (e321 x)) (e322 x)) (e323 x)) (e324 x)) (e325 x)) (e326 x))
  have e1 : (((((((((I_t127 x) + (I_t332 x)) + ((w_n67 x).toNat + (w_n148 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat)) + (8 * (w_n344 x).toNat + 8 * (w_n346 x).toNat + 8 * (w_n349 x).toNat + 8 * (w_n921 x).toNat + 8 * (w_n924 x).toNat + 8 * (w_n940 x).toNat)) + (16 * (w_n347 x).toNat + 16 * (w_n350 x).toNat + 16 * (w_n352 x).toNat + 16 * (w_n355 x).toNat + 16 * (w_n930 x).toNat + 16 * (w_n941 x).toNat)) + (32 * (w_n348 x).toNat + 32 * (w_n351 x).toNat + 32 * (w_n353 x).toNat + 32 * (w_n356 x).toNat + 32 * (w_n358 x).toNat + 32 * (w_n948 x).toNat)) + (64 * (w_n168 x).toNat + 64 * (w_n336 x).toNat + 64 * (w_n354 x).toNat + 64 * (w_n357 x).toNat + 64 * (w_n359 x).toNat + 64 * (w_n934 x).toNat)) + (64 * (w_n947 x).toNat + 64 * (w_n949 x).toNat + 64 * (w_n952 x).toNat + 64 * (w_n954 x).toNat + 64 * (w_n965 x).toNat + 64 * (w_n967 x).toNat)) + (128 * (w_n360 x).toNat + 128 * (w_n935 x).toNat + 128 * (w_n950 x).toNat + 128 * (w_n953 x).toNat + 128 * (w_n955 x).toNat + 128 * (w_n968 x).toNat)) = (I_t333 x) + ((w_n67 x).toNat + (w_n148 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 8 * (w_n344 x).toNat + 8 * (w_n346 x).toNat + 8 * (w_n349 x).toNat + 8 * (w_n921 x).toNat + 8 * (w_n924 x).toNat + 8 * (w_n940 x).toNat + 16 * (w_n347 x).toNat + 16 * (w_n350 x).toNat + 16 * (w_n352 x).toNat + 16 * (w_n355 x).toNat + 16 * (w_n930 x).toNat + 16 * (w_n941 x).toNat + 32 * (w_n348 x).toNat + 32 * (w_n351 x).toNat + 32 * (w_n353 x).toNat + 32 * (w_n356 x).toNat + 32 * (w_n358 x).toNat + 32 * (w_n948 x).toNat + 64 * (w_n168 x).toNat + 64 * (w_n336 x).toNat + 64 * (w_n354 x).toNat + 64 * (w_n357 x).toNat + 64 * (w_n359 x).toNat + 64 * (w_n934 x).toNat + 64 * (w_n947 x).toNat + 64 * (w_n949 x).toNat + 64 * (w_n952 x).toNat + 64 * (w_n954 x).toNat + 64 * (w_n965 x).toNat + 64 * (w_n967 x).toNat + 128 * (w_n360 x).toNat + 128 * (w_n935 x).toNat + 128 * (w_n950 x).toNat + 128 * (w_n953 x).toNat + 128 * (w_n955 x).toNat + 128 * (w_n968 x).toNat) := by unfold I_t333; ac_rfl
  have e2 : ((((((((((w_n67 x).toNat + (w_n148 x).toNat + 64 * (w_n168 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + 64 * (w_n336 x).toNat + 2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 8 * (w_n344 x).toNat + 8 * (w_n346 x).toNat + 16 * (w_n347 x).toNat + 32 * (w_n348 x).toNat + 8 * (w_n349 x).toNat + 16 * (w_n350 x).toNat + 32 * (w_n351 x).toNat + 16 * (w_n352 x).toNat + 32 * (w_n353 x).toNat + 64 * (w_n354 x).toNat + 16 * (w_n355 x).toNat + 32 * (w_n356 x).toNat + 64 * (w_n357 x).toNat + 32 * (w_n358 x).toNat + 64 * (w_n359 x).toNat + 128 * (w_n360 x).toNat) + (2 * (w_n570 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 2 * (w_n912 x).toNat + 8 * (w_n921 x).toNat + 8 * (w_n924 x).toNat + 16 * (w_n930 x).toNat + 64 * (w_n934 x).toNat + 128 * (w_n935 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n940 x).toNat + 16 * (w_n941 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 64 * (w_n947 x).toNat + 32 * (w_n948 x).toNat + 64 * (w_n949 x).toNat + 128 * (w_n950 x).toNat + 32 * (w_n951 x).toNat + 64 * (w_n952 x).toNat + 128 * (w_n953 x).toNat + 64 * (w_n954 x).toNat + 128 * (w_n955 x).toNat + 256 * (w_n956 x).toNat)) + ((w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat)) + (8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat)) + (16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 64 * (w_n965 x).toNat)) + (32 * (w_n966 x).toNat + 64 * (w_n967 x).toNat + 128 * (w_n968 x).toNat)) + (64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat)) + (64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat)) + (128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat)) = (2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 32 * (w_n951 x).toNat + 256 * (w_n956 x).toNat + (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat + 16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat) + ((w_n67 x).toNat + (w_n148 x).toNat + (w_n235 x).toNat + (w_n316 x).toNat + (w_n810 x).toNat + (w_n891 x).toNat + 8 * (w_n344 x).toNat + 8 * (w_n346 x).toNat + 8 * (w_n349 x).toNat + 8 * (w_n921 x).toNat + 8 * (w_n924 x).toNat + 8 * (w_n940 x).toNat + 16 * (w_n347 x).toNat + 16 * (w_n350 x).toNat + 16 * (w_n352 x).toNat + 16 * (w_n355 x).toNat + 16 * (w_n930 x).toNat + 16 * (w_n941 x).toNat + 32 * (w_n348 x).toNat + 32 * (w_n351 x).toNat + 32 * (w_n353 x).toNat + 32 * (w_n356 x).toNat + 32 * (w_n358 x).toNat + 32 * (w_n948 x).toNat + 64 * (w_n168 x).toNat + 64 * (w_n336 x).toNat + 64 * (w_n354 x).toNat + 64 * (w_n357 x).toNat + 64 * (w_n359 x).toNat + 64 * (w_n934 x).toNat + 64 * (w_n947 x).toNat + 64 * (w_n949 x).toNat + 64 * (w_n952 x).toNat + 64 * (w_n954 x).toNat + 64 * (w_n965 x).toNat + 64 * (w_n967 x).toNat + 128 * (w_n360 x).toNat + 128 * (w_n935 x).toNat + 128 * (w_n950 x).toNat + 128 * (w_n953 x).toNat + 128 * (w_n955 x).toNat + 128 * (w_n968 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem s333 (x : Nat → Bool) : I_t333 x = pc x 0 1000 := by
  have hl := s127 x
  have hr := s332 x
  have : pc x 0 847 = pc x 0 463 + pc x 463 384 := pc_add x 0 463 384
  have : pc x 0 1000 = pc x 0 847 + pc x 847 153 := pc_add x 0 847 153
  unfold I_t333
  omega
def I_t334 (x : Nat → Bool) : Nat := I_t0 x + I_t333 x
theorem t334 (x : Nat → Bool) : I_t334 x = (x 1000).toNat + 2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 32 * (w_n951 x).toNat + 256 * (w_n956 x).toNat + (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat + 16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat := by
  have hs : ((I_t0 x) + (I_t333 x)) = (((x 1000).toNat) + (2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 32 * (w_n951 x).toNat + 256 * (w_n956 x).toNat + (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat + 16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat)) := (add_eq (t0 x) (t333 x))
  have e1 : ((I_t0 x) + (I_t333 x)) = I_t334 x := by unfold I_t334; ac_rfl
  have e2 : (((x 1000).toNat) + (2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 32 * (w_n951 x).toNat + 256 * (w_n956 x).toNat + (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat + 16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat)) = (x 1000).toNat + 2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 32 * (w_n951 x).toNat + 256 * (w_n956 x).toNat + (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat + 16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat := by ac_rfl
  exact e1.symm.trans (hs.trans e2)
theorem s334 (x : Nat → Bool) : I_t334 x = pc x 0 1001 := by
  have hl := s0 x
  have hr := s333 x
  have : pc x 0 1001 = pc x 0 1000 + pc x 1000 1 := pc_add x 0 1000 1
  unfold I_t334
  omega
def I_c0 (x : Nat → Bool) : Nat := I_t334 x
theorem c0 (x : Nat → Bool) : I_c0 x + 1 + 2 + 8 = 256 * (w_n956 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat + 128 * (w_n989 x).toNat + 128 * (w_n990 x).toNat + r327 x + 2 * r328 x + 4 * r329 x + 8 * r330 x + 16 * r331 x + 32 * r332 x + 64 * r333 x := by
  have hs : ((((((((I_t334 x) + ((x 1000).toNat + (w_n936 x).toNat + (w_n957 x).toNat + 1)) + (2 * (w_n337 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + 2 * (w_n937 x).toNat + 2 * (w_n958 x).toNat + 2 * (w_n978 x).toNat + 2)) + (4 * (w_n343 x).toNat + 4 * (w_n939 x).toNat + 4 * (w_n959 x).toNat + 4 * (w_n979 x).toNat + 4 * (w_n980 x).toNat)) + (8 * (w_n942 x).toNat + 8 * (w_n960 x).toNat + 8 * (w_n981 x).toNat + 8 * (w_n982 x).toNat + 16 * (w_n943 x).toNat + 8)) + (16 * (w_n945 x).toNat + 16 * (w_n961 x).toNat + 16 * (w_n963 x).toNat + 16 * (w_n983 x).toNat + 16 * (w_n984 x).toNat + 32 * (w_n951 x).toNat)) + (32 * (w_n962 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 32 * (w_n985 x).toNat + 32 * (w_n986 x).toNat + 64 * (w_n969 x).toNat)) + (64 * (w_n972 x).toNat + 64 * (w_n987 x).toNat + 64 * (w_n988 x).toNat)) = (((((((((x 1000).toNat + 2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 32 * (w_n951 x).toNat + 256 * (w_n956 x).toNat + (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat + 16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat) + (2 * (w_n978 x).toNat + 4 * (w_n979 x).toNat + r327 x)) + (4 * (w_n980 x).toNat + 8 * (w_n981 x).toNat + 2 * r328 x)) + (8 * (w_n982 x).toNat + 16 * (w_n983 x).toNat + 4 * r329 x)) + (16 * (w_n984 x).toNat + 32 * (w_n985 x).toNat + 8 * r330 x)) + (32 * (w_n986 x).toNat + 64 * (w_n987 x).toNat + 16 * r331 x)) + (64 * (w_n988 x).toNat + 128 * (w_n989 x).toNat + 32 * r332 x)) + (128 * (w_n990 x).toNat + 64 * r333 x)) := (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (add_eq (t334 x) (e327 x)) (e328 x)) (e329 x)) (e330 x)) (e331 x)) (e332 x)) (e333 x))
  have e1 : ((((((((I_t334 x) + ((x 1000).toNat + (w_n936 x).toNat + (w_n957 x).toNat + 1)) + (2 * (w_n337 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + 2 * (w_n937 x).toNat + 2 * (w_n958 x).toNat + 2 * (w_n978 x).toNat + 2)) + (4 * (w_n343 x).toNat + 4 * (w_n939 x).toNat + 4 * (w_n959 x).toNat + 4 * (w_n979 x).toNat + 4 * (w_n980 x).toNat)) + (8 * (w_n942 x).toNat + 8 * (w_n960 x).toNat + 8 * (w_n981 x).toNat + 8 * (w_n982 x).toNat + 16 * (w_n943 x).toNat + 8)) + (16 * (w_n945 x).toNat + 16 * (w_n961 x).toNat + 16 * (w_n963 x).toNat + 16 * (w_n983 x).toNat + 16 * (w_n984 x).toNat + 32 * (w_n951 x).toNat)) + (32 * (w_n962 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 32 * (w_n985 x).toNat + 32 * (w_n986 x).toNat + 64 * (w_n969 x).toNat)) + (64 * (w_n972 x).toNat + 64 * (w_n987 x).toNat + 64 * (w_n988 x).toNat)) = (I_c0 x + 1 + 2 + 8) + ((x 1000).toNat + (w_n936 x).toNat + (w_n957 x).toNat + 2 * (w_n337 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + 2 * (w_n937 x).toNat + 2 * (w_n958 x).toNat + 2 * (w_n978 x).toNat + 4 * (w_n343 x).toNat + 4 * (w_n939 x).toNat + 4 * (w_n959 x).toNat + 4 * (w_n979 x).toNat + 4 * (w_n980 x).toNat + 8 * (w_n942 x).toNat + 8 * (w_n960 x).toNat + 8 * (w_n981 x).toNat + 8 * (w_n982 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 16 * (w_n961 x).toNat + 16 * (w_n963 x).toNat + 16 * (w_n983 x).toNat + 16 * (w_n984 x).toNat + 32 * (w_n951 x).toNat + 32 * (w_n962 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 32 * (w_n985 x).toNat + 32 * (w_n986 x).toNat + 64 * (w_n969 x).toNat + 64 * (w_n972 x).toNat + 64 * (w_n987 x).toNat + 64 * (w_n988 x).toNat) := by unfold I_c0; ac_rfl
  have e2 : (((((((((x 1000).toNat + 2 * (w_n337 x).toNat + 4 * (w_n343 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + (w_n936 x).toNat + 2 * (w_n937 x).toNat + 4 * (w_n939 x).toNat + 8 * (w_n942 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 32 * (w_n951 x).toNat + 256 * (w_n956 x).toNat + (w_n957 x).toNat + 2 * (w_n958 x).toNat + 4 * (w_n959 x).toNat + 8 * (w_n960 x).toNat + 16 * (w_n961 x).toNat + 32 * (w_n962 x).toNat + 16 * (w_n963 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 64 * (w_n969 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 64 * (w_n972 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat) + (2 * (w_n978 x).toNat + 4 * (w_n979 x).toNat + r327 x)) + (4 * (w_n980 x).toNat + 8 * (w_n981 x).toNat + 2 * r328 x)) + (8 * (w_n982 x).toNat + 16 * (w_n983 x).toNat + 4 * r329 x)) + (16 * (w_n984 x).toNat + 32 * (w_n985 x).toNat + 8 * r330 x)) + (32 * (w_n986 x).toNat + 64 * (w_n987 x).toNat + 16 * r331 x)) + (64 * (w_n988 x).toNat + 128 * (w_n989 x).toNat + 32 * r332 x)) + (128 * (w_n990 x).toNat + 64 * r333 x)) = (256 * (w_n956 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat + 128 * (w_n989 x).toNat + 128 * (w_n990 x).toNat + r327 x + 2 * r328 x + 4 * r329 x + 8 * r330 x + 16 * r331 x + 32 * r332 x + 64 * r333 x) + ((x 1000).toNat + (w_n936 x).toNat + (w_n957 x).toNat + 2 * (w_n337 x).toNat + 2 * (w_n570 x).toNat + 2 * (w_n912 x).toNat + 2 * (w_n937 x).toNat + 2 * (w_n958 x).toNat + 2 * (w_n978 x).toNat + 4 * (w_n343 x).toNat + 4 * (w_n939 x).toNat + 4 * (w_n959 x).toNat + 4 * (w_n979 x).toNat + 4 * (w_n980 x).toNat + 8 * (w_n942 x).toNat + 8 * (w_n960 x).toNat + 8 * (w_n981 x).toNat + 8 * (w_n982 x).toNat + 16 * (w_n943 x).toNat + 16 * (w_n945 x).toNat + 16 * (w_n961 x).toNat + 16 * (w_n963 x).toNat + 16 * (w_n983 x).toNat + 16 * (w_n984 x).toNat + 32 * (w_n951 x).toNat + 32 * (w_n962 x).toNat + 32 * (w_n964 x).toNat + 32 * (w_n966 x).toNat + 32 * (w_n985 x).toNat + 32 * (w_n986 x).toNat + 64 * (w_n969 x).toNat + 64 * (w_n972 x).toNat + 64 * (w_n987 x).toNat + 64 * (w_n988 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
def I_c2 (x : Nat → Bool) : Nat := I_c0 x
theorem c2 (x : Nat → Bool) : I_c2 x + 1 + 2 + 8 = 256 * (w_n971 x).toNat + 256 * (w_n974 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat + 256 * (w_n991 x).toNat + 512 * (w_n992 x).toNat + r327 x + 2 * r328 x + 4 * r329 x + 8 * r330 x + 16 * r331 x + 32 * r332 x + 64 * r333 x + 128 * r334 x := by
  have hs : ((I_c0 x + 1 + 2 + 8) + (128 * (w_n970 x).toNat + 128 * (w_n973 x).toNat + 128 * (w_n975 x).toNat + 128 * (w_n989 x).toNat + 128 * (w_n990 x).toNat + 256 * (w_n956 x).toNat)) = ((256 * (w_n956 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat + 128 * (w_n989 x).toNat + 128 * (w_n990 x).toNat + r327 x + 2 * r328 x + 4 * r329 x + 8 * r330 x + 16 * r331 x + 32 * r332 x + 64 * r333 x) + (256 * (w_n991 x).toNat + 512 * (w_n992 x).toNat + 128 * r334 x)) := (add_eq (c0 x) (e334 x))
  have e1 : ((I_c0 x + 1 + 2 + 8) + (128 * (w_n970 x).toNat + 128 * (w_n973 x).toNat + 128 * (w_n975 x).toNat + 128 * (w_n989 x).toNat + 128 * (w_n990 x).toNat + 256 * (w_n956 x).toNat)) = (I_c2 x + 1 + 2 + 8) + (128 * (w_n970 x).toNat + 128 * (w_n973 x).toNat + 128 * (w_n975 x).toNat + 128 * (w_n989 x).toNat + 128 * (w_n990 x).toNat + 256 * (w_n956 x).toNat) := by unfold I_c2; ac_rfl
  have e2 : ((256 * (w_n956 x).toNat + 128 * (w_n970 x).toNat + 256 * (w_n971 x).toNat + 128 * (w_n973 x).toNat + 256 * (w_n974 x).toNat + 128 * (w_n975 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat + 128 * (w_n989 x).toNat + 128 * (w_n990 x).toNat + r327 x + 2 * r328 x + 4 * r329 x + 8 * r330 x + 16 * r331 x + 32 * r332 x + 64 * r333 x) + (256 * (w_n991 x).toNat + 512 * (w_n992 x).toNat + 128 * r334 x)) = (256 * (w_n971 x).toNat + 256 * (w_n974 x).toNat + 256 * (w_n976 x).toNat + 512 * (w_n977 x).toNat + 256 * (w_n991 x).toNat + 512 * (w_n992 x).toNat + r327 x + 2 * r328 x + 4 * r329 x + 8 * r330 x + 16 * r331 x + 32 * r332 x + 64 * r333 x + 128 * r334 x) + (128 * (w_n970 x).toNat + 128 * (w_n973 x).toNat + 128 * (w_n975 x).toNat + 128 * (w_n989 x).toNat + 128 * (w_n990 x).toNat + 256 * (w_n956 x).toNat) := by ac_rfl
  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))
theorem correct (x : Nat → Bool) : w_maj x = decide (popcount x 1001 ≥ 501) := by
  apply of_iff
  have hle := popcount_le x 1001
  have ht := c2 x
  have hI : I_c2 x = popcount x 1001 := by
    simp only [I_c0, I_c2]
    rw [s334 x]
    exact (popcount_eq_pc x 1001).symm
  rw [hI] at ht
  have := r327_lt x
  have := r328_lt x
  have := r329_lt x
  have := r330_lt x
  have := r331_lt x
  have := r332_lt x
  have := r333_lt x
  have := r334_lt x
  have := Bool.toNat_le (w_n971 x)
  have := Bool.toNat_le (w_n974 x)
  have := Bool.toNat_le (w_n976 x)
  have := Bool.toNat_le (w_n977 x)
  have := Bool.toNat_le (w_n991 x)
  have := Bool.toNat_le (w_n992 x)
  have := to_iff _ _ (e335 x)
  have := Bool.toNat_le (w_maj x)
  omega
#print axioms correct
