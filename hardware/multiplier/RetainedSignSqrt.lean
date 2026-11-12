/-!
# Retained-sign square root

`stepS` is the exact non-restoring square-root step on integers.  `rowS` is the row a circuit builds:
it keeps the remainder modulo `4 * G` only (`G = 2^k` at row `k`), adds one expression for both
signs, and takes the sign as the top bit.  `sqrt_correct` shows the root bits satisfy
`Q * Q ≤ X < (Q + 1) * (Q + 1)` for every radicand given by its bit pairs.  Core Lean 4 only.
-/

namespace Colony

/-- Exact step: `p` is the next pair of radicand bits, `Q` the root bits so far. -/
def stepS (r Q p : Int) : Int := if 0 ≤ r then 4 * r + p - (4 * Q + 1) else 4 * r + p + (4 * Q + 3)

/-- Invariant: `X` is the radicand prefix read so far. -/
def InvS (X Q r : Int) : Prop :=
  (0 ≤ r → r = X - Q * Q ∧ r ≤ 2 * Q) ∧ (r < 0 → r = X - (Q + 1) * (Q + 1) ∧ -(2 * Q + 1) ≤ r)

theorem invS_step (X Q r p : Int) (_hQ : 0 ≤ Q) (hp0 : 0 ≤ p) (hp3 : p ≤ 3) (h : InvS X Q r) :
    InvS (4 * X + p) (2 * Q + (if 0 ≤ stepS r Q p then 1 else 0)) (stepS r Q p) := by
  have e1 : (2 * Q + 1) * (2 * Q + 1) = 4 * (Q * Q) + 4 * Q + 1 := by grind
  have e2 : (2 * Q + 0 + 1) * (2 * Q + 0 + 1) = 4 * (Q * Q) + 4 * Q + 1 := by grind
  have e3 : (Q + 1) * (Q + 1) = Q * Q + 2 * Q + 1 := by grind
  have e5 : (2 * Q + 0) * (2 * Q + 0) = 4 * (Q * Q) := by grind
  obtain ⟨hp, hn⟩ := h
  unfold stepS
  by_cases hr : 0 ≤ r
  · obtain ⟨h1, h2⟩ := hp hr
    simp only [hr, if_true]
    by_cases hq : 0 ≤ 4 * r + p - (4 * Q + 1)
    · simp only [hq, if_true]
      refine ⟨fun _ => ⟨?_, ?_⟩, fun hneg => absurd hq (by omega)⟩
      · rw [e1]; omega
      · omega
    · simp only [hq, if_false]
      refine ⟨fun hpos => absurd hpos hq, fun _ => ⟨?_, ?_⟩⟩
      · rw [e2]; omega
      · omega
  · have hr' : r < 0 := by omega
    obtain ⟨h1, h2⟩ := hn hr'
    rw [e3] at h1
    simp only [hr, if_false]
    by_cases hq : 0 ≤ 4 * r + p + (4 * Q + 3)
    · simp only [hq, if_true]
      refine ⟨fun _ => ⟨?_, ?_⟩, fun hneg => absurd hq (by omega)⟩
      · rw [e1]; omega
      · omega
    · simp only [hq, if_false]
      refine ⟨fun hpos => absurd hpos hq, fun _ => ⟨?_, ?_⟩⟩
      · rw [e2]; omega
      · omega

/-- Two's complement: on `[-H, H)` the top bit of the word modulo `2 * H` is the sign. -/
theorem sign_topS (r H : Int) (h1 : -H ≤ r) (h2 : r < H) : (H ≤ r % (2 * H)) ↔ r < 0 := by
  by_cases hr : r < 0
  · have : r / (2 * H) = -1 ∧ r % (2 * H) = r + 2 * H :=
      (Int.ediv_emod_unique (by omega)).mpr ⟨by omega, by omega, by omega⟩
    rw [this.2]; constructor <;> intro <;> omega
  · have : r % (2 * H) = r := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]; constructor <;> intro <;> omega

/-- The row as built.  Previous word `w` modulo `2 * G`, new word modulo `4 * G`.
`Q xnor s` over the row's columns is `Q` for `s = 1` and `G - 1 - Q` for `s = 0`. -/
def rowS (w p Q G : Int) (s : Bool) : Int :=
  (4 * w + p + 3 + 4 * (if s then Q else G - 1 - Q)) % (4 * G)

theorem rowS_congr (r w p Q G : Int) (hw : w = r % (2 * G)) (s : Bool) (hs : s = true ↔ r < 0) :
    rowS w p Q G s = stepS r Q p % (4 * G) := by
  have h4 : (4 * w) % (4 * G) = (4 * r) % (4 * G) := by
    rw [hw]
    have a1 : 4 * (r % (2 * G)) = 2 * (2 * (r % (2 * G))) := by omega
    have a2 : 2 * (r % (2 * G)) = (2 * r) % (2 * (2 * G)) := (Int.mul_emod_mul_of_pos r (2 * G) (by omega)).symm
    have a3 : (4 : Int) * G = 2 * (2 * G) := by omega
    rw [a1, a2, a3]
    have a4 : 2 * (2 * r % (2 * (2 * G))) = (2 * (2 * r)) % (2 * (2 * (2 * G))) :=
      (Int.mul_emod_mul_of_pos (2 * r) (2 * (2 * G)) (by omega)).symm
    rw [a4]
    have a5 : (2 * (2 * r)) = 4 * r := by omega
    rw [a5]
    exact Int.emod_emod_of_dvd _ ⟨2, by omega⟩
  unfold rowS stepS
  cases s with
  | true =>
    have hr : ¬ (0 ≤ r) := by have := hs.mp rfl; omega
    simp only [if_true, hr, if_false]
    have e : (4 * w + p + 3 + 4 * Q) = (4 * w + (p + 3 + 4 * Q)) := by omega
    rw [e, ← Int.emod_add_emod, h4, Int.emod_add_emod]
    have e2 : (4 * r + (p + 3 + 4 * Q)) = (4 * r + p + (4 * Q + 3)) := by omega
    rw [e2]
  | false =>
    have hr : 0 ≤ r := by
      by_cases h : r < 0
      · exact absurd (hs.mpr h) (by simp)
      · omega
    simp only [hr, if_true, Bool.false_eq_true, if_false]
    have e : (4 * w + p + 3 + 4 * (G - 1 - Q)) = (4 * w + (p - (4 * Q + 1) + (4 * G) * 1)) := by omega
    rw [e, ← Int.emod_add_emod, h4, Int.emod_add_emod]
    have e2 : (4 * r + (p - (4 * Q + 1) + 4 * G * 1)) = (4 * r + p - (4 * Q + 1)) + (4 * G) * 1 := by omega
    rw [e2, Int.add_mul_emod_self_left]

/-- The circuit: rows over the radicand's bit pairs, most significant first.
State: `G = 2^k`, the word `w`, the sign `s`, the root `Q`. -/
def runS : List Int → Int → Int → Bool → Int → Int × Int × Bool × Int
  | [], G, w, s, Q => (G, w, s, Q)
  | p :: ps, G, w, s, Q =>
    runS ps (2 * G) (rowS w p Q G s) (decide (2 * G ≤ rowS w p Q G s))
      (2 * Q + (if decide (2 * G ≤ rowS w p Q G s) = true then 0 else 1))

/-- Value of a string of bit pairs read after a prefix `X`. -/
def valS : List Int → Int → Int
  | [], X => X
  | p :: ps, X => valS ps (4 * X + p)

theorem runS_spec : ∀ (ps : List Int) (G w : Int) (s : Bool) (Q X r : Int),
    (∀ p ∈ ps, 0 ≤ p ∧ p ≤ 3) → 0 < G → 0 ≤ Q → 2 * Q + 2 ≤ G → InvS X Q r →
    w = r % (2 * G) → (s = true ↔ r < 0) →
    ∃ r', InvS (valS ps X) (runS ps G w s Q).2.2.2 r' ∧ 0 ≤ (runS ps G w s Q).2.2.2 := by
  intro ps
  induction ps with
  | nil =>
    intro G w s Q X r _ _ hQ _ hinv _ _
    exact ⟨r, hinv, hQ⟩
  | cons p ps ih =>
    intro G w s Q X r hps hG hQ hQG hinv hw hs
    obtain ⟨hp0, hp3⟩ := hps p (List.mem_cons_self ..)
    have hinv' := invS_step X Q r p hQ hp0 hp3 hinv
    have hcong := rowS_congr r w p Q G hw s hs
    have hsign : (decide (2 * G ≤ rowS w p Q G s) = true ↔ stepS r Q p < 0) := by
      rw [hcong]
      obtain ⟨hp', hn'⟩ := hinv'
      have hrange1 : -(2 * G) ≤ stepS r Q p := by
        by_cases h : stepS r Q p < 0
        · have := (hn' h).2
          split at this <;> omega
        · omega
      have hrange2 : stepS r Q p < 2 * G := by
        by_cases h : stepS r Q p < 0
        · omega
        · have := (hp' (by omega)).2
          split at this <;> omega
      have e : (4 : Int) * G = 2 * (2 * G) := by omega
      rw [e]
      have := sign_topS _ (2 * G) hrange1 hrange2
      simp [this]
    have hq_eq : (2 * Q + (if decide (2 * G ≤ rowS w p Q G s) = true then (0 : Int) else 1))
        = 2 * Q + (if 0 ≤ stepS r Q p then 1 else 0) := by
      by_cases h : stepS r Q p < 0
      · have h1 := hsign.mpr h
        have h2 : ¬ (0 ≤ stepS r Q p) := by omega
        simp [h1, h2]
      · have h1 : ¬ (decide (2 * G ≤ rowS w p Q G s) = true) := fun hh => h (hsign.mp hh)
        have h2 : 0 ≤ stepS r Q p := by omega
        simp [h1, h2]
    have hQ' : 0 ≤ 2 * Q + (if decide (2 * G ≤ rowS w p Q G s) = true then (0 : Int) else 1) := by
      split <;> omega
    have hQG' : 2 * (2 * Q + (if decide (2 * G ≤ rowS w p Q G s) = true then (0 : Int) else 1)) + 2 ≤ 2 * G := by
      split <;> omega
    have hcong' : rowS w p Q G s = stepS r Q p % (2 * (2 * G)) := by
      rw [hcong]; congr 1; omega
    exact ih (2 * G) (rowS w p Q G s) (decide (2 * G ≤ rowS w p Q G s))
      (2 * Q + (if decide (2 * G ≤ rowS w p Q G s) = true then (0 : Int) else 1)) (4 * X + p) (stepS r Q p)
      (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (by omega) hQ' hQG'
      (by rw [hq_eq]; exact hinv') hcong' hsign

/-- **Square root.**  For a radicand given by its bit pairs, the rows return `Q` with
`Q * Q ≤ X < (Q + 1) * (Q + 1)`. -/
theorem sqrt_correct (ps : List Int) (hps : ∀ p ∈ ps, 0 ≤ p ∧ p ≤ 3) :
    (runS ps 2 0 false 0).2.2.2 * (runS ps 2 0 false 0).2.2.2 ≤ valS ps 0 ∧
    valS ps 0 < ((runS ps 2 0 false 0).2.2.2 + 1) * ((runS ps 2 0 false 0).2.2.2 + 1) := by
  have hinv : InvS 0 0 0 := ⟨fun _ => ⟨by simp, by omega⟩, fun h => absurd h (by omega)⟩
  obtain ⟨r, ⟨hp, hn⟩, hQ⟩ := runS_spec ps 2 0 false 0 0 0 hps (by omega) (by omega) (by omega) hinv (by simp) (by simp)
  have e3 : ((runS ps 2 0 false 0).2.2.2 + 1) * ((runS ps 2 0 false 0).2.2.2 + 1)
      = (runS ps 2 0 false 0).2.2.2 * (runS ps 2 0 false 0).2.2.2 + 2 * (runS ps 2 0 false 0).2.2.2 + 1 := by grind
  rw [e3]
  by_cases hr : r < 0
  · obtain ⟨h1, h2⟩ := hn hr
    rw [e3] at h1
    constructor <;> omega
  · obtain ⟨h1, h2⟩ := hp (by omega)
    constructor <;> omega

end Colony

#print axioms Colony.sqrt_correct
