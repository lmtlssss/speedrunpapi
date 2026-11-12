/-
Fold division.  D + eps = 2^P with eps small.  A running value W = T * 2^(P+o) + L is replaced by
W' = L + T * eps * 2^o.  The difference is T * D * 2^o, so T is a quotient digit at offset o.
Core Lean only.
-/
namespace Colony.Fold

/-- One fold removes exactly T * D * 2^o. -/
theorem step (P o T L eps D W W' : Nat) (hD : D + eps = 2 ^ P)
    (hW : W = T * 2 ^ (P + o) + L) (hW' : W' = L + T * eps * 2 ^ o) :
    W = W' + T * D * 2 ^ o := by
  subst hW hW'
  rw [Nat.pow_add, ← hD]
  grind

/-- The quotient accumulates: X = Qa * D * 2^(o+b) + W  becomes  X = (Qa * 2^b + T) * D * 2^o + W'. -/
theorem invariant (X Qa D P o b T L eps W W' : Nat) (hD : D + eps = 2 ^ P)
    (hX : X = Qa * D * 2 ^ (o + b) + W)
    (hW : W = T * 2 ^ (P + o) + L) (hW' : W' = L + T * eps * 2 ^ o) :
    X = (Qa * 2 ^ b + T) * D * 2 ^ o + W' := by
  have h := step P o T L eps D W W' hD hW hW'
  rw [hX, h, Nat.pow_add]
  grind

/-- Two rows S + C = W < 3 * 2^(p+b): both top fields are below 3 * 2^b and the low parts sum below 2 * 2^p. -/
theorem fields (p b S C W : Nat) (h : S + C = W) (hW : W < 3 * 2 ^ (p + b)) :
    S / 2 ^ p < 3 * 2 ^ b ∧ C / 2 ^ p < 3 * 2 ^ b ∧ S / 2 ^ p + C / 2 ^ p < 3 * 2 ^ b ∧
    S % 2 ^ p + C % 2 ^ p < 2 * 2 ^ p ∧
    W = (S / 2 ^ p + C / 2 ^ p) * 2 ^ p + (S % 2 ^ p + C % 2 ^ p) := by
  have hp : 0 < 2 ^ p := Nat.two_pow_pos _
  have hs := Nat.div_add_mod S (2 ^ p)
  have hc := Nat.div_add_mod C (2 ^ p)
  have ms := Nat.mod_lt S hp
  have mc := Nat.mod_lt C hp
  have e : W = (S / 2 ^ p + C / 2 ^ p) * 2 ^ p + (S % 2 ^ p + C % 2 ^ p) := by
    rw [Nat.add_mul, Nat.mul_comm (S / 2 ^ p), Nat.mul_comm (C / 2 ^ p)]; omega
  have hsum : (S / 2 ^ p + C / 2 ^ p) * 2 ^ p < (3 * 2 ^ b) * 2 ^ p := by
    have : 3 * 2 ^ (p + b) = (3 * 2 ^ b) * 2 ^ p := by rw [Nat.pow_add]; grind
    omega
  have hlt : S / 2 ^ p + C / 2 ^ p < 3 * 2 ^ b := Nat.lt_of_mul_lt_mul_right hsum
  exact ⟨Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt, Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt, hlt, by omega, e⟩

/-- T < 3 * 2^b, eps < 2^(P-g), g = b + 2:  4 * T * eps < 3 * 2^P. -/
theorem small (P b g T eps : Nat) (hg : g = b + 2) (hgP : g ≤ P)
    (he : eps < 2 ^ (P - g)) (hT : T < 3 * 2 ^ b) : 4 * (T * eps) < 3 * 2 ^ P := by
  have e : 2 ^ P = 4 * (2 ^ b * 2 ^ (P - g)) := by
    have : P = 2 + (b + (P - g)) := by omega
    conv => lhs; rw [this]
    rw [Nat.pow_add, Nat.pow_add]
  have hpos : 0 < 2 ^ (P - g) := Nat.two_pow_pos _
  have h1 : T * eps < 3 * 2 ^ b * 2 ^ (P - g) := by
    cases Nat.eq_zero_or_pos T with
    | inl h0 => subst h0; simp; exact Nat.mul_pos (Nat.mul_pos (by omega) (Nat.two_pow_pos _)) hpos
    | inr hTp =>
      calc T * eps < T * 2 ^ (P - g) := Nat.mul_lt_mul_of_pos_left he hTp
        _ ≤ 3 * 2 ^ b * 2 ^ (P - g) := Nat.mul_le_mul_right _ (by omega)
  have : 3 * 2 ^ b * 2 ^ (P - g) = 3 * (2 ^ b * 2 ^ (P - g)) := by grind
  omega

/-- The folded value stays below 3 * 2^p. -/
theorem bound (P o p b g T L eps W' : Nat) (hp : p = P + o) (hg : g = b + 2) (hgP : g ≤ P)
    (he : eps < 2 ^ (P - g)) (hT : T < 3 * 2 ^ b) (hL : L < 2 * 2 ^ p)
    (hW' : W' = L + T * eps * 2 ^ o) : W' < 3 * 2 ^ p := by
  have hs := small P b g T eps hg hgP he hT
  have ho : 0 < 2 ^ o := Nat.two_pow_pos _
  have h4 : 4 * (T * eps * 2 ^ o) < 3 * 2 ^ p := by
    have : 4 * (T * eps) * 2 ^ o < 3 * 2 ^ P * 2 ^ o := Nat.mul_lt_mul_of_pos_right hs ho
    have e1 : 4 * (T * eps * 2 ^ o) = 4 * (T * eps) * 2 ^ o := by grind
    have e2 : 3 * 2 ^ p = 3 * 2 ^ P * 2 ^ o := by rw [hp, Nat.pow_add]; grind
    omega
  omega

/-- After the last field (offset 0):  c = M * 2^s,  c * a = Q' * (c * d) + T * 2^P + L,  D = c * d.
    Then Q = Q' + T satisfies  Q * d ≤ a < Q * d + 3 * d. -/
theorem last (a d c Q' T L eps P b g : Nat) (hc : 0 < c)
    (hD : c * d + eps = 2 ^ P) (hg : g = b + 2) (hb : 2 ≤ b) (hgP : g ≤ P)
    (he : eps < 2 ^ (P - g)) (hT : T < 3 * 2 ^ b) (hL : L < 2 * 2 ^ P)
    (hX : c * a = Q' * (c * d) + (T * 2 ^ P + L)) :
    (Q' + T) * d ≤ a ∧ a < (Q' + T) * d + 3 * d := by
  have hs := small P b g T eps hg hgP he hT
  have key : c * a = c * ((Q' + T) * d) + (T * eps + L) := by
    rw [hX, ← hD]; grind
  -- 12 * eps ≤ 2^P because g ≥ 4
  have e16 : 2 ^ P = 2 ^ g * 2 ^ (P - g) := by
    rw [← Nat.pow_add]; congr 1; omega
  have g16 : 16 ≤ 2 ^ g := by
    have : g = 4 + (g - 4) := by omega
    rw [this, Nat.pow_add]
    have : 0 < 2 ^ (g - 4) := Nat.two_pow_pos _
    omega
  have hpos : 0 < 2 ^ (P - g) := Nat.two_pow_pos _
  have h16 : 16 * 2 ^ (P - g) ≤ 2 ^ P := by rw [e16]; exact Nat.mul_le_mul_right _ g16
  have hE : T * eps + L < 3 * (c * d) := by omega
  constructor
  · have : c * ((Q' + T) * d) ≤ c * a := by omega
    exact Nat.le_of_mul_le_mul_left this hc
  · have : c * a < c * ((Q' + T) * d + 3 * d) := by
      have : c * ((Q' + T) * d + 3 * d) = c * ((Q' + T) * d) + 3 * (c * d) := by grind
      omega
    exact Nat.lt_of_mul_lt_mul_left this

/-- Selection among R, R - d, R - 2d. -/
theorem select (a d Q : Nat) (hd : 0 < d) (h1 : Q * d ≤ a) (h2 : a < Q * d + 3 * d) :
    let R := a - Q * d
    (R < d → a / d = Q ∧ a % d = R) ∧
    (d ≤ R → R < 2 * d → a / d = Q + 1 ∧ a % d = R - d) ∧
    (2 * d ≤ R → a / d = Q + 2 ∧ a % d = R - 2 * d) := by
  intro R
  have hR : a = Q * d + R := by omega
  refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_⟩
  · exact (Nat.div_mod_unique hd).mpr ⟨by rw [Nat.mul_comm]; omega, h⟩
  · refine (Nat.div_mod_unique hd).mpr ⟨?_, by omega⟩
    rw [Nat.mul_add, Nat.mul_comm d Q]; omega
  · refine (Nat.div_mod_unique hd).mpr ⟨?_, by omega⟩
    rw [Nat.mul_add, Nat.mul_comm d Q]; omega

end Colony.Fold

#print axioms Colony.Fold.invariant
#print axioms Colony.Fold.fields
#print axioms Colony.Fold.bound
#print axioms Colony.Fold.last
#print axioms Colony.Fold.select
