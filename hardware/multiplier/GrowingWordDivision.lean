/-!
# Growing-word non-restoring division

`stepZ` is the exact non-restoring step on integers.  `rowW` is the row a circuit builds: it keeps the
remainder modulo `2 * H` only, and takes the sign as `H ≤ b ∨ H ≤ word`.  `run_spec` shows that after
any sequence of dividend bits the kept word, the sign and the quotient bits are those of exact division.
Core Lean 4 only.
-/

namespace Colony

/-- Exact non-restoring step: subtract while the remainder is non-negative, add back otherwise. -/
def stepZ (b r x : Int) : Int := if 0 ≤ r then 2 * r + x - b else 2 * r + x + b

/-- Invariant of the exact recurrence: `A` is the dividend prefix read so far, `Q` the quotient bits. -/
def Inv (b A Q r : Int) : Prop :=
  (0 ≤ r → r = A - Q * b ∧ r < b) ∧ (r < 0 → r = A - (Q + 1) * b ∧ -b ≤ r)

theorem inv_step (b A Q r x : Int) (_hb : 0 < b) (hx : x = 0 ∨ x = 1) (h : Inv b A Q r) :
    Inv b (2 * A + x) (2 * Q + (if 0 ≤ stepZ b r x then 1 else 0)) (stepZ b r x) := by
  have e1 : (2 * Q + 1) * b = 2 * (Q * b) + b := by
    rw [Int.add_mul, Int.mul_assoc, Int.one_mul]
  have e2 : (2 * Q + 0 + 1) * b = 2 * (Q * b) + b := by
    rw [Int.add_zero]; exact e1
  have e3 : (Q + 1) * b = Q * b + b := by rw [Int.add_mul, Int.one_mul]
  have e4 : (2 * Q + 1 + 1) * b = 2 * (Q * b) + b + b := by
    rw [Int.add_mul, e1, Int.one_mul]
  have e5 : (2 * Q + 0) * b = 2 * (Q * b) := by rw [Int.add_zero, Int.mul_assoc]
  obtain ⟨hp, hn⟩ := h
  unfold stepZ
  by_cases hr : 0 ≤ r
  · obtain ⟨h1, h2⟩ := hp hr
    simp only [hr, if_true]
    by_cases hq : 0 ≤ 2 * r + x - b
    · simp only [hq, if_true]
      refine ⟨fun _ => ⟨?_, ?_⟩, fun hneg => absurd hq (by omega)⟩
      · rw [e1]; omega
      · rcases hx with hx | hx <;> omega
    · simp only [hq, if_false]
      refine ⟨fun hpos => absurd hpos hq, fun _ => ⟨?_, ?_⟩⟩
      · rw [e2]; omega
      · rcases hx with hx | hx <;> omega
  · have hr' : r < 0 := by omega
    obtain ⟨h1, h2⟩ := hn hr'
    simp only [hr, if_false]
    by_cases hq : 0 ≤ 2 * r + x + b
    · simp only [hq, if_true]
      refine ⟨fun _ => ⟨?_, ?_⟩, fun hneg => absurd hq (by omega)⟩
      · rw [e1]; rw [e3] at h1; omega
      · rcases hx with hx | hx <;> omega
    · simp only [hq, if_false]
      refine ⟨fun hpos => absurd hpos hq, fun _ => ⟨?_, ?_⟩⟩
      · rw [e2]; rw [e3] at h1; omega
      · rcases hx with hx | hx <;> omega

/-- Two's complement: on `[-H, H)` the top bit of the word modulo `2 * H` is the sign. -/
theorem sign_top (r H : Int) (h1 : -H ≤ r) (h2 : r < H) : (H ≤ r % (2 * H)) ↔ r < 0 := by
  by_cases hr : r < 0
  · have : r / (2 * H) = -1 ∧ r % (2 * H) = r + 2 * H :=
      (Int.ediv_emod_unique (by omega)).mpr ⟨by omega, by omega, by omega⟩
    rw [this.2]; constructor <;> intro <;> omega
  · have : r % (2 * H) = r := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]; constructor <;> intro <;> omega

/-- The row as built: previous word `w` modulo `H`, new word modulo `2 * H`.
`b xnor s` over the row's columns is `b % (2H)` for `s = 1` and `2H - 1 - b % (2H)` for `s = 0`. -/
def rowW (b w x H : Int) (s : Bool) : Int :=
  (2 * w + x + (if s then b % (2 * H) else 2 * H - 1 - b % (2 * H)) + (if s then 0 else 1)) % (2 * H)

theorem row_congr (b r w x H : Int) (_hH : 0 < H) (hw : w = r % H) (s : Bool) (hs : s = true ↔ r < 0) :
    rowW b w x H s = stepZ b r x % (2 * H) := by
  have h2 : 2 * w = (2 * r) % (2 * H) := by
    rw [hw]; exact (Int.mul_emod_mul_of_pos r H (by omega)).symm
  unfold rowW stepZ
  cases s with
  | true =>
    have hr : ¬ (0 ≤ r) := by have := hs.mp rfl; omega
    simp only [if_true, hr, if_false]
    rw [h2, Int.add_zero]
    have : (2 * r % (2 * H) + x + b % (2 * H)) = (2 * r % (2 * H) + (x + b % (2 * H))) := by omega
    rw [this, Int.emod_add_emod]
    have : (2 * r + (x + b % (2 * H))) = (2 * r + x + b % (2 * H)) := by omega
    rw [this, Int.add_emod_emod]
  | false =>
    have hr : 0 ≤ r := by
      by_cases h : r < 0
      · exact absurd (hs.mpr h) (by simp)
      · omega
    simp only [hr, if_true, Bool.false_eq_true, if_false]
    rw [h2]
    have e : (2 * r % (2 * H) + x + (2 * H - 1 - b % (2 * H)) + 1)
        = (2 * r % (2 * H) + (x + 2 * H - b % (2 * H))) := by omega
    rw [e, Int.emod_add_emod]
    have e2 : (2 * r + (x + 2 * H - b % (2 * H))) = (2 * r + x + 2 * H - b % (2 * H)) := by omega
    rw [e2, Int.sub_emod_emod]
    have e3 : (2 * r + x + 2 * H - b) = (2 * r + x - b) + (2 * H) * 1 := by omega
    rw [e3, Int.add_mul_emod_self_left]

/-- The circuit: rows over the dividend bits, most significant first.  State: modulus `H` of the kept
word, the word `w`, the sign `s`, the quotient `Q`. -/
def run (b : Int) : List Bool → Int → Int → Bool → Int → Int × Int × Bool × Int
  | [], H, w, s, Q => (H, w, s, Q)
  | x :: xs, H, w, s, Q =>
    run b xs (2 * H) (rowW b w (if x then 1 else 0) H s)
      (decide (H ≤ b) || decide (H ≤ rowW b w (if x then 1 else 0) H s))
      (2 * Q + (if (decide (H ≤ b) || decide (H ≤ rowW b w (if x then 1 else 0) H s)) = true then 0 else 1))

/-- Value of a bit string read after a prefix `A`. -/
def val : List Bool → Int → Int
  | [], A => A
  | x :: xs, A => val xs (2 * A + (if x then 1 else 0))

/-- Main lemma: the kept word, sign and quotient follow the exact recurrence. -/
theorem run_spec (b : Int) (hb : 0 < b) :
    ∀ (xs : List Bool) (H w : Int) (s : Bool) (Q A r : Int),
      0 < H → 0 ≤ Q → 0 ≤ A → 2 * A + 2 ≤ H → Inv b A Q r →
      w = r % H → (s = true ↔ r < 0) →
      ∃ r', Inv b (val xs A) (run b xs H w s Q).2.2.2 r' ∧
        (run b xs H w s Q).2.1 = r' % (run b xs H w s Q).1 ∧
        ((run b xs H w s Q).2.2.1 = true ↔ r' < 0) ∧ 0 ≤ (run b xs H w s Q).2.2.2 := by
  intro xs
  induction xs with
  | nil =>
    intro H w s Q A r _ hQ _ _ hinv hw hs
    exact ⟨r, hinv, hw, hs, hQ⟩
  | cons x xs ih =>
    intro H w s Q A r hH hQ hA hAH hinv hw hs
    have hx : (if x then (1 : Int) else 0) = 0 ∨ (if x then (1 : Int) else 0) = 1 := by
      cases x <;> simp
    have hinv' := inv_step b A Q r _ hb hx hinv
    have hcong := row_congr b r w (if x then 1 else 0) H hH hw s hs
    have hsign : ((decide (H ≤ b) || decide (H ≤ rowW b w (if x then 1 else 0) H s)) = true ↔
        stepZ b r (if x then 1 else 0) < 0) := by
      rw [hcong]
      obtain ⟨hp', hn'⟩ := hinv'
      by_cases hflag : H ≤ b
      · have hneg : stepZ b r (if x then 1 else 0) < 0 := by
          by_cases h : stepZ b r (if x then 1 else 0) < 0
          · exact h
          · have h0 : 0 ≤ stepZ b r (if x then 1 else 0) := by omega
            have := (hp' h0).1
            rw [if_pos h0] at this
            have e1 : (2 * Q + 1) * b = 2 * (Q * b) + b := by
              rw [Int.add_mul, Int.mul_assoc, Int.one_mul]
            rw [e1] at this
            have hQb : 0 ≤ Q * b := Int.mul_nonneg hQ (by omega)
            rcases hx with hx | hx <;> omega
        simp [hflag, hneg]
      · have hlt : b < H := by omega
        have hrange1 : -H ≤ stepZ b r (if x then 1 else 0) := by
          by_cases h : stepZ b r (if x then 1 else 0) < 0
          · have := (hn' h).2; omega
          · omega
        have hrange2 : stepZ b r (if x then 1 else 0) < H := by
          by_cases h : stepZ b r (if x then 1 else 0) < 0
          · omega
          · have := (hp' (by omega)).2; omega
        have := sign_top _ H hrange1 hrange2
        simp [hflag, this]
    have hQ' : 0 ≤ 2 * Q + (if (decide (H ≤ b) || decide (H ≤ rowW b w (if x then 1 else 0) H s)) = true then (0 : Int) else 1) := by
      split <;> omega
    have hq_eq : (2 * Q + (if (decide (H ≤ b) || decide (H ≤ rowW b w (if x then 1 else 0) H s)) = true then (0 : Int) else 1))
        = 2 * Q + (if 0 ≤ stepZ b r (if x then 1 else 0) then 1 else 0) := by
      by_cases h : stepZ b r (if x then 1 else 0) < 0
      · have h1 := hsign.mpr h
        have h2 : ¬ (0 ≤ stepZ b r (if x then 1 else 0)) := by omega
        simp [h1, h2]
      · have h1 : ¬ ((decide (H ≤ b) || decide (H ≤ rowW b w (if x then 1 else 0) H s)) = true) := fun hh => h (hsign.mp hh)
        have h2 : 0 ≤ stepZ b r (if x then 1 else 0) := by omega
        simp [h1, h2]
    exact ih (2 * H) (rowW b w (if x then 1 else 0) H s)
      (decide (H ≤ b) || decide (H ≤ rowW b w (if x then 1 else 0) H s))
      (2 * Q + (if (decide (H ≤ b) || decide (H ≤ rowW b w (if x then 1 else 0) H s)) = true then (0 : Int) else 1))
      (2 * A + (if x then 1 else 0)) (stepZ b r (if x then 1 else 0))
      (by omega) hQ' (by rcases hx with hx | hx <;> omega) (by rcases hx with hx | hx <;> omega)
      (by rw [hq_eq]; exact hinv') hcong hsign

theorem run_fst (b : Int) : ∀ (xs : List Bool) (H w : Int) (s : Bool) (Q : Int),
    (run b xs H w s Q).1 = H * 2 ^ xs.length := by
  intro xs
  induction xs with
  | nil => intro H w s Q; simp [run]
  | cons x xs ih =>
    intro H w s Q
    show (run b xs (2 * H) _ _ _).1 = _
    rw [ih, List.length_cons, Int.pow_succ]
    rw [Int.mul_comm 2 H, Int.mul_assoc, Int.mul_comm 2 (2 ^ xs.length)]

/-- **Division.**  For a divisor `0 < b ≤ 2^n` and an `n`-bit dividend given by its bits, the rows
return the quotient, and `word + (sign ? b : 0)` modulo `2^n` is the remainder. -/
theorem div_correct (b : Int) (hb : 0 < b) (xs : List Bool) (hbn : b ≤ 2 ^ xs.length) :
    val xs 0 / b = (run b xs 2 0 false 0).2.2.2 ∧
    val xs 0 % b = ((run b xs 2 0 false 0).2.1 + (if (run b xs 2 0 false 0).2.2.1 then b else 0)) % 2 ^ xs.length := by
  have hinv : Inv b 0 0 0 := ⟨fun _ => ⟨by simp, hb⟩, fun h => absurd h (by omega)⟩
  obtain ⟨r, ⟨hp, hn⟩, hw, hs, _⟩ := run_spec b hb xs 2 0 false 0 0 0 (by omega) (by omega) (by omega) (by omega) hinv (by simp) (by simp)
  rw [run_fst] at hw
  have hK : (0 : Int) < 2 ^ xs.length := Int.pow_pos (by omega)
  have hdvd : (2 : Int) ^ xs.length ∣ 2 * 2 ^ xs.length := ⟨2, by rw [Int.mul_comm]⟩
  have hmod : (run b xs 2 0 false 0).2.1 % 2 ^ xs.length = r % 2 ^ xs.length := by
    rw [hw, Int.emod_emod_of_dvd _ hdvd]
  have e3 : ((run b xs 2 0 false 0).2.2.2 + 1) * b = (run b xs 2 0 false 0).2.2.2 * b + b := by
    rw [Int.add_mul, Int.one_mul]
  by_cases hr : r < 0
  · have hst := hs.mpr hr
    obtain ⟨h1, h2⟩ := hn hr
    rw [e3] at h1
    have huniq := (Int.ediv_emod_unique (a := val xs 0) (r := r + b) (q := (run b xs 2 0 false 0).2.2.2) hb).mpr
      ⟨by rw [Int.mul_comm]; omega, by omega, by omega⟩
    refine ⟨huniq.1, ?_⟩
    rw [huniq.2, hst]
    simp only [if_true]
    rw [← Int.emod_add_emod, hmod, Int.emod_add_emod]
    exact (Int.emod_eq_of_lt (by omega) (by omega)).symm
  · have hst : (run b xs 2 0 false 0).2.2.1 = false := by
      cases h : (run b xs 2 0 false 0).2.2.1
      · rfl
      · exact absurd (hs.mp h) hr
    obtain ⟨h1, h2⟩ := hp (by omega)
    have huniq := (Int.ediv_emod_unique (a := val xs 0) (r := r) (q := (run b xs 2 0 false 0).2.2.2) hb).mpr
      ⟨by rw [Int.mul_comm]; omega, by omega, h2⟩
    refine ⟨huniq.1, ?_⟩
    rw [huniq.2, hst]
    simp only [Bool.false_eq_true, if_false, Int.add_zero]
    rw [hmod]
    exact (Int.emod_eq_of_lt (by omega) (by omega)).symm

/-- **Divisor zero.**  No row goes negative: the quotient bits are all ones and the word is the dividend. -/
theorem div_zero : ∀ (xs : List Bool) (H Q A : Int), 0 < H → 0 ≤ A → 2 * A + 2 ≤ H →
    (run 0 xs H A false Q).2.1 = val xs A ∧ (run 0 xs H A false Q).2.2.1 = false ∧
    (run 0 xs H A false Q).2.2.2 + 1 = (Q + 1) * 2 ^ xs.length := by
  intro xs
  induction xs with
  | nil => intro H Q A _ _ _; simp [run, val]
  | cons x xs ih =>
    intro H Q A hH hA hAH
    have hx : (if x then (1 : Int) else 0) = 0 ∨ (if x then (1 : Int) else 0) = 1 := by
      cases x <;> simp
    have hrow : rowW 0 A (if x then 1 else 0) H false = 2 * A + (if x then 1 else 0) := by
      unfold rowW
      simp only [Bool.false_eq_true, if_false, Int.zero_emod, Int.sub_zero]
      have e : (2 * A + (if x then 1 else 0) + (2 * H - 1) + 1) = (2 * A + (if x then 1 else 0)) + (2 * H) * 1 := by omega
      rw [e, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by rcases hx with hx | hx <;> omega) (by rcases hx with hx | hx <;> omega)
    have hsg : (decide (H ≤ 0) || decide (H ≤ rowW 0 A (if x then 1 else 0) H false)) = false := by
      rw [hrow]
      have h1 : ¬ (H ≤ 0) := by omega
      have h2 : ¬ (H ≤ 2 * A + (if x then 1 else 0)) := by rcases hx with hx | hx <;> omega
      simp [h1, h2]
    have hrun : run 0 (x :: xs) H A false Q
        = run 0 xs (2 * H) (2 * A + (if x then 1 else 0)) false (2 * Q + 1) := by
      show run 0 xs (2 * H) (rowW 0 A (if x then 1 else 0) H false)
        (decide (H ≤ 0) || decide (H ≤ rowW 0 A (if x then 1 else 0) H false))
        (2 * Q + (if (decide (H ≤ 0) || decide (H ≤ rowW 0 A (if x then 1 else 0) H false)) = true then 0 else 1)) = _
      rw [hsg, hrow]
      simp
    have := ih (2 * H) (2 * Q + 1) (2 * A + (if x then 1 else 0)) (by omega)
      (by rcases hx with hx | hx <;> omega) (by rcases hx with hx | hx <;> omega)
    rw [hrun]
    refine ⟨this.1, this.2.1, ?_⟩
    rw [this.2.2, List.length_cons, Int.pow_succ]
    have e : (2 * Q + 1 + 1) = (Q + 1) * 2 := by omega
    rw [e, Int.mul_assoc, Int.mul_comm 2 (2 ^ xs.length)]

end Colony

#print axioms Colony.div_correct
#print axioms Colony.div_zero
