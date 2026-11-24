module

public import BalancedRepetitionThreshold.RotationEngine

import Mathlib.Tactic

/-!
# Exact Unconditional Proof for the 7-Letter Balanced Witness `v7` (`E(v7) = 6 / 5`)

Defines `v7 = colour (sturmian α7) y7 y'7` with:
- `α7 = (11 - √10) / 37` (continued fraction `[0; 4, 1, (2, 1, 1)]`),
- `y7 = (6 7)^ω` (`[5, 6]` in 0-indexed `Fin 7`),
- `y'7 = (1 2 3 4 1 5 3 2 1 4 3 5)^ω` (`[0, 1, 2, 3, 0, 4, 2, 1, 0, 3, 2, 4]` in 0-indexed `Fin 7`),
(crediting Rampersad–Shallit–Vandomme (2018) Table 1 for the colouring of `x7`; `v7` modifies only
the continued-fraction preperiod of the Sturmian slope).

Proves 100% unconditionally in the pure Lean 4 kernel:
- `v7_isBalanced : IsBalanced v7`
- `v7_usesAllLetters : UsesAllLetters v7`
- `v7_attains : HasPeriod v7 0 6 5` (prefix `1 2 3 6 4 1`, exponent `6 / 5`)
- `v7_run_bound : ∀ i p r, 0 < p → (∀ k < r, v7 (i + k) = v7 (i + k + p)) → r * 5 ≤ p`
- `v7_critExp_eq : critExp v7 = ((6 : ℝ) / 5 : ℝ) ∧ ((6 : ℝ) / 5 : ℝ) ∈ minPeriodExponentSet v7`
-/

@[expose] public section

namespace BalancedRepetitionThreshold

/-- Rare-letter frequency `α7 = (11 - √10) / 37` for `v7`. -/
noncomputable def α7 : ℝ := (11 - Real.sqrt 10) / 37

/-- Period-2 colour table on `true` (`a`) positions of `v7` (0-indexed for printed `{6, 7}`). -/
def y7Tab : List ℕ := [5, 6]

/-- Period-12 colour table on `false` (`b`) positions of `v7` (0-indexed for printed `{1..5}`). -/
def y'7Tab : List ℕ := [0, 1, 2, 3, 0, 4, 2, 1, 0, 3, 2, 4]

/-- Periodic colour sequence `y7` on `Fin 7`. -/
def y7 (k : ℕ) : Fin 7 :=
  ⟨y7Tab.getD (k % 2) 0, by
    have hk : k % 2 < 2 := Nat.mod_lt k (by omega)
    interval_cases (k % 2) <;> decide⟩

/-- Periodic colour sequence `y'7` on `Fin 7`. -/
def y'7 (k : ℕ) : Fin 7 :=
  ⟨y'7Tab.getD (k % 12) 0, by
    have hk : k % 12 < 12 := Nat.mod_lt k (by omega)
    interval_cases (k % 12) <;> decide⟩

/-- The 7-letter balanced witness `v7 = colour (sturmian α7) y7 y'7`. -/
noncomputable def v7 : ℕ → Fin 7 :=
  colour (sturmian α7) y7 y'7

/-- Tight rational enclosure of `√10`: `31622 / 10000 < √10 < 31623 / 10000`. -/
theorem sqrt10_bounds : (31622 : ℝ) / 10000 < Real.sqrt 10 ∧ Real.sqrt 10 < (31623 : ℝ) / 10000 := by
  have hsq : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  constructor <;> nlinarith

/-- Rational enclosure of `α7`: `211 / 1000 < α7 < 212 / 1000`. -/
theorem α7_bounds : (211 : ℝ) / 1000 < α7 ∧ α7 < (212 : ℝ) / 1000 := by
  unfold α7
  have := sqrt10_bounds
  constructor <;> linarith

theorem α7_pos : 0 < α7 := by linarith [α7_bounds.1]
theorem α7_lt_half : α7 < 1 / 2 := by linarith [α7_bounds.2]
theorem α7_lt_one : α7 < 1 := by linarith [α7_bounds.2]

/-- `α7` is irrational (no non-zero integer multiple of `α7` is an integer). -/
theorem α7_irrational {u v : ℤ} (hu : u ≠ 0) : (u : ℝ) * α7 ≠ (v : ℝ) := by
  have hirr : Irrational (Real.sqrt ((10 : ℕ) : ℝ)) := by
    rw [irrational_sqrt_natCast_iff]
    rintro ⟨k, hk⟩
    have hkle : k ≤ 3 := by nlinarith
    interval_cases k <;> omega
  have hα : α7 = (((11 : ℤ) : ℝ) + ((-1 : ℤ) : ℝ) * Real.sqrt ((10 : ℕ) : ℝ)) / ((37 : ℕ) : ℝ) := by
    unfold α7; push_cast; ring
  rw [hα]
  exact quad_ne_int_div (A := 11) (B := -1) (C := 37) (D := 10) (by omega) (by omega) hirr hu

theorem y7_val_ge (m : ℕ) : 5 ≤ (y7 m).val := by
  simp only [y7]
  have hm : m % 2 < 2 := Nat.mod_lt m (by omega)
  interval_cases (m % 2) <;> decide

theorem yPrime7_val_lt (m : ℕ) : (y'7 m).val < 5 := by
  simp only [y'7]
  have hm : m % 12 < 12 := Nat.mod_lt m (by omega)
  interval_cases (m % 12) <;> decide

/-- `y7` and `y'7` have disjoint alphabets (`{5, 6}` vs `{0, 1, 2, 3, 4}`). -/
theorem y7_disjoint_yPrime7 (a b : ℕ) : y7 a ≠ y'7 b := by
  intro heq
  have h1 := y7_val_ge a
  have h2 := yPrime7_val_lt b
  have hv := congrArg Fin.val heq
  omega

/-- Direct 1-balance of `v7` (unconditional, zero recurrence hypothesis). -/
theorem v7_isBalanced : IsBalanced v7 := by
  apply colour_isBalanced_of_constantGap α7_pos α7_lt_one y7 y'7
  have hcg_y' : ∀ (c : Fin 7) (g r : ℕ), g ∣ 12 → 0 < g → r < g →
      c.val < 5 →
      (∀ t < 12, y'7Tab.getD t 0 = c.val ↔ t % g = r) →
      (∀ m, y7 m ≠ c) ∧ ∃ g' r', HasConstantGap y'7 c g' r' := by
    intro c g r hgdvd hg hr hc htab
    refine ⟨fun m h => by have := y7_val_ge m; have := congrArg Fin.val h; omega,
      g, r, hg, hr, fun m => ?_⟩
    rw [Fin.ext_iff]
    simp only [y'7]
    have hmod : m % g = (m % 12) % g := (Nat.mod_mod_of_dvd m hgdvd).symm
    rw [hmod]
    exact htab (m % 12) (Nat.mod_lt m (by omega))
  have hcg_y : ∀ (c : Fin 7) (r : ℕ), r < 2 →
      5 ≤ c.val →
      (∀ t < 2, y7Tab.getD t 0 = c.val ↔ t = r) →
      (∀ m, y'7 m ≠ c) ∧ ∃ g' r', HasConstantGap y7 c g' r' := by
    intro c r hr hc htab
    refine ⟨fun m h => by have := yPrime7_val_lt m; have := congrArg Fin.val h; omega,
      2, r, by omega, hr, fun m => ?_⟩
    rw [Fin.ext_iff]
    simp only [y7]
    exact htab (m % 2) (Nat.mod_lt m (by omega))
  intro c
  fin_cases c
  · exact Or.inr (hcg_y' 0 4 0 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 1 6 1 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 2 4 2 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 3 6 3 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 4 6 5 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inl (hcg_y 5 0 (by omega) (by decide) (by decide))
  · exact Or.inl (hcg_y 6 1 (by omega) (by decide) (by decide))

/-- `v7` uses all 7 letters of `Fin 7`. -/
theorem v7_usesAllLetters : UsesAllLetters v7 := by
  apply colour_usesAllLetters α7_pos α7_lt_one y7 y'7
  intro c
  fin_cases c
  · exact Or.inr ⟨0, by decide⟩
  · exact Or.inr ⟨1, by decide⟩
  · exact Or.inr ⟨2, by decide⟩
  · exact Or.inr ⟨3, by decide⟩
  · exact Or.inr ⟨5, by decide⟩
  · exact Or.inl ⟨0, by decide⟩
  · exact Or.inl ⟨1, by decide⟩

/-- Exact attainment witness: prefix `1 2 3 6 4 1` (`v7 0 = v7 5 = 0`) has period `5`, length `6`,
exponent `6 / 5`. -/
theorem v7_attains : HasPeriod v7 0 6 5 := by
  have hb := α7_bounds
  have hfl : ∀ n m : ℕ, (m : ℝ) ≤ (n : ℝ) * α7 → (n : ℝ) * α7 < (m : ℝ) + 1 →
      ⌊(n : ℝ) * α7⌋ = (m : ℤ) := by
    intro n m h1 h2
    rw [Int.floor_eq_iff]; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hf1 : ⌊((1 : ℕ) : ℝ) * α7⌋ = 0 := hfl 1 0 (by push_cast; linarith) (by push_cast; linarith)
  have hf2 : ⌊((2 : ℕ) : ℝ) * α7⌋ = 0 := hfl 2 0 (by push_cast; linarith) (by push_cast; linarith)
  have hf6 : ⌊((6 : ℕ) : ℝ) * α7⌋ = 1 := hfl 6 1 (by push_cast; linarith) (by push_cast; linarith)
  have hf7 : ⌊((7 : ℕ) : ℝ) * α7⌋ = 1 := hfl 7 1 (by push_cast; linarith) (by push_cast; linarith)
  have hu0 : sturmian α7 0 = false := by
    unfold sturmian; change decide (⌊((2 : ℕ) : ℝ) * α7⌋ - ⌊((1 : ℕ) : ℝ) * α7⌋ = 1) = false
    rw [hf2, hf1]; decide
  have hu5 : sturmian α7 5 = false := by
    unfold sturmian; change decide (⌊((7 : ℕ) : ℝ) * α7⌋ - ⌊((6 : ℕ) : ℝ) * α7⌋ = 1) = false
    rw [hf7, hf6]; decide
  have hcf0 : countFalse (sturmian α7) 0 = 0 := by simp [countFalse]
  have hcf5 : countFalse (sturmian α7) 5 = 4 := by
    have hct5 := sturmian_countTrue_eq_floor α7_pos α7_lt_one 5
    have hsum5 := countTrue_add_countFalse (sturmian α7) 5
    change (countTrue (sturmian α7) 5 : ℤ) = ⌊((6 : ℕ) : ℝ) * α7⌋ at hct5
    rw [hf6] at hct5
    omega
  refine ⟨by omega, by omega, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [add_zero, zero_add, v7, colour, hu0, hu5, hcf0, hcf5, Bool.false_eq_true, ↓reduceIte]
  decide

/-! ### Small Periods (`1 ≤ p < 20`) via Pure-Kernel Cut Partition -/

/-- Exact sorted cut partition of `[0, 1)` for `L = 23` steps of `sturmian α7`. -/
def cuts7 : List (ℕ × ℤ) :=
  [(0, 0), (14, 3), (9, 2), (23, 5), (4, 1), (18, 4), (13, 3), (8, 2), (22, 5), (3, 1),
   (17, 4), (12, 3), (7, 2), (21, 5), (2, 1), (16, 4), (11, 3), (6, 2), (20, 5), (1, 1),
   (15, 4), (10, 3), (5, 2), (19, 5), (0, 1)]

private theorem cuts7_ok : checkCutPartition 23 211 212 1000 cuts7 = true := by decide

private theorem small7_ok : checkSmallPeriods 20 5 2 12 y7Tab y'7Tab 23 cuts7 = true := by decide

/-- Small-period upper bound for `v7`: every period `1 ≤ p < 20` has `r * 5 ≤ p`. -/
theorem v7_small_periods {i p r : ℕ} (hp0 : 0 < p) (hp_lt : p < 20)
    (hrun : ∀ k < r, v7 (i + k) = v7 (i + k + p)) :
    r * 5 ≤ p :=
  checkSmallPeriods_sound (den := 5) (P_small := 20) (L := 23) (ma := 2) (mb := 12) (prec := 1000)
    α7_pos α7_lt_one (by omega) (by omega) (by omega) (by omega)
    (fun q _ hq => by omega) y7_disjoint_yPrime7 (fun _ => rfl) (fun _ => rfl)
    α7_bounds.1 α7_bounds.2 cuts7_ok small7_ok hp0 hp_lt hrun

/-! ### All Large Periods (`p ≥ 20`) via Periodic Continued-Fraction Level Analysis -/

/-- Partial quotients `[0; 4, 1, (2, 1, 1)]` of `α7`. -/
def a7 (k : ℕ) : ℕ :=
  if k = 0 then 0
  else if k = 1 then 4
  else if k = 2 then 1
  else match (k - 3) % 3 with
    | 0 => 2
    | 1 => 1
    | _ => 1

/-- Periodic error ratios `θ7 r = η_{3+r} / η_{2+r}` (`r ∈ {0, 1, 2}`). -/
noncomputable def θ7 (r : ℕ) : ℝ :=
  match r % 3 with
  | 0 => (-2 + Real.sqrt 10) / 2
  | 1 => (-1 + Real.sqrt 10) / 3
  | _ => (-2 + Real.sqrt 10) / 3

theorem a7_ge_one (j : ℕ) (hj : 1 ≤ j) : 1 ≤ a7 j := by
  unfold a7
  split_ifs <;> try omega
  split <;> omega

theorem a7_per3 (n : ℕ) : a7 (n + 4) = a7 (4 + n % 3) := by
  have h1 : n + 4 ≠ 0 ∧ n + 4 ≠ 1 ∧ n + 4 ≠ 2 := by omega
  have h2 : 4 + n % 3 ≠ 0 ∧ 4 + n % 3 ≠ 1 ∧ 4 + n % 3 ≠ 2 := by omega
  unfold a7
  simp only [h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2, ↓reduceIte]
  have hmod : (n + 4 - 3) % 3 = (4 + n % 3 - 3) % 3 := by omega
  rw [hmod]

theorem a7_per12 (k : ℕ) (hk : 3 ≤ k) : a7 (k + 1 + 12) = a7 (k + 1) := by
  have h1 : k + 1 + 12 ≠ 0 ∧ k + 1 + 12 ≠ 1 ∧ k + 1 + 12 ≠ 2 := by omega
  have h2 : k + 1 ≠ 0 ∧ k + 1 ≠ 1 ∧ k + 1 ≠ 2 := by omega
  unfold a7
  simp only [h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2, ↓reduceIte]
  have hmod : (k + 1 + 12 - 3) % 3 = (k + 1 - 3) % 3 := by omega
  rw [hmod]

theorem eta7_periodic_ratio : ∀ n : ℕ, eta a7 α7 (n + 3) = θ7 (n % 3) * eta a7 α7 (n + 2) := by
  apply eta_periodic_ratio (T := 3) (by omega) θ7
  · have hp2 : convP a7 2 = 1 := by decide
    have hq2 : convQ a7 2 = 5 := by decide
    have hp3 : convP a7 3 = 3 := by decide
    have hq3 : convQ a7 3 = 14 := by decide
    unfold eta θ7 α7
    rw [hp2, hq2, hp3, hq3]
    have hsq : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
    simp only [Nat.cast_ofNat, Nat.cast_one]
    nlinarith
  · exact a7_per3
  · intro r hr
    have hsq : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
    interval_cases r
    · change 1 - ((1 : ℕ) : ℝ) * ((-2 + Real.sqrt 10) / 2) =
          ((-2 + Real.sqrt 10) / 2) * ((-1 + Real.sqrt 10) / 3)
      push_cast; nlinarith
    · change 1 - ((1 : ℕ) : ℝ) * ((-1 + Real.sqrt 10) / 3) =
          ((-1 + Real.sqrt 10) / 3) * ((-2 + Real.sqrt 10) / 3)
      push_cast; nlinarith
    · change 1 - ((2 : ℕ) : ℝ) * ((-2 + Real.sqrt 10) / 3) =
          ((-2 + Real.sqrt 10) / 3) * ((-2 + Real.sqrt 10) / 2)
      push_cast; nlinarith

/-- Scaled rational brackets `(lo, hi)` (denominator `1000`) for `θ7 (r % 3)`. -/
def θ7Bracket (r : ℕ) : ℕ × ℕ :=
  match r % 3 with
  | 0 => (581, 582)
  | 1 => (720, 721)
  | _ => (387, 388)

theorem θ7_bracket_sound (r : ℕ) :
    ((θ7Bracket r).1 : ℝ) / 1000 < θ7 r ∧ θ7 r < ((θ7Bracket r).2 : ℝ) / 1000 := by
  have hs := sqrt10_bounds
  have hmod : r % 3 < 3 := Nat.mod_lt r (by omega)
  unfold θ7Bracket θ7
  interval_cases (r % 3) <;> constructor <;> push_cast <;> linarith

/-- Exact ratio identities at `k = 1` and `k = 2`. -/
theorem eta7_k1_ratio : eta a7 α7 1 / eta a7 α7 0 = θ7 1 := by
  have hp0 : convP a7 0 = 0 := by decide
  have hq0 : convQ a7 0 = 1 := by decide
  have hp1 : convP a7 1 = 1 := by decide
  have hq1 : convQ a7 1 = 4 := by decide
  have h0pos : 0 < eta a7 α7 0 := by
    unfold eta; rw [hp0, hq0]; simp; exact α7_pos
  rw [div_eq_iff (ne_of_gt h0pos)]
  unfold eta θ7 α7
  rw [hp0, hq0, hp1, hq1]
  have hsq : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  nlinarith

theorem eta7_k2_ratio : eta a7 α7 2 / eta a7 α7 1 = θ7 2 := by
  have hp1 : convP a7 1 = 1 := by decide
  have hq1 : convQ a7 1 = 4 := by decide
  have hp2 : convP a7 2 = 1 := by decide
  have hq2 : convQ a7 2 = 5 := by decide
  have h1pos : 0 < eta a7 α7 1 := by
    unfold eta; rw [hp1, hq1]; have := α7_bounds; push_cast; norm_num; linarith
  rw [div_eq_iff (ne_of_gt h1pos)]
  unfold eta θ7 α7
  rw [hp1, hq1, hp2, hq2]
  have hsq : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  simp only [Nat.cast_ofNat, Nat.cast_one]
  nlinarith

private theorem level7_k1_ok :
    let st := convModState a7 2 12 1
    checkLevelClass 2 12 5 (a7 2) st.1 st.2.1 st.2.2.1 st.2.2.2 720 721 1000
      (.exact (convQ a7 1) (convQPrev a7 1)) = true := by decide

private theorem level7_k2_ok :
    let st := convModState a7 2 12 2
    checkLevelClass 2 12 5 (a7 3) st.1 st.2.1 st.2.2.1 st.2.2.2 387 388 1000
      (.exact (convQ a7 2) (convQPrev a7 2)) = true := by decide

private theorem level7_mod_per12 :
    convModState a7 2 12 (3 + 12) = convModState a7 2 12 3 := by decide

private theorem level7_tail_ok :
    (List.range 12).all (fun s =>
      let st := convModState a7 2 12 (3 + s)
      let br := θ7Bracket s
      checkLevelClass 2 12 5 (a7 (3 + s + 1)) st.1 st.2.1 st.2.2.1 st.2.2.2 br.1 br.2 1000 .unit) = true := by
  decide

private theorem y7_match_even : ∀ s < 2, ∀ t < 2,
    y7Tab.getD s 0 = y7Tab.getD ((s + t) % 2) 0 → t = 0 := by decide

private theorem y'7_consec_match_dvd12 : ∀ s < 12, ∀ t < 12,
    y'7Tab.getD s 0 = y'7Tab.getD ((s + t) % 12) 0 →
    y'7Tab.getD ((s + 1) % 12) 0 = y'7Tab.getD ((s + 1 + t) % 12) 0 → t = 0 := by decide

/-- Large-period upper bound for `v7`: every period `p ≥ 20` has `r * 5 ≤ p`. -/
theorem v7_large_periods {i p r : ℕ} (hp20 : 20 ≤ p)
    (hrun : ∀ k < r, v7 (i + k) = v7 (i + k + p)) :
    r * 5 ≤ p := by
  have hp0 : 0 < p := by omega
  have hust : ∀ k < r, sturmian α7 (i + k) = sturmian α7 (i + k + p) :=
    fun k hk => (colour_match_implies y7_disjoint_yPrime7 (hrun k hk)).1
  obtain ⟨m, hm_half⟩ := exists_nearest_int ((p : ℝ) * α7)
  by_cases hδ_ge : α7 ≤ |(p : ℝ) * α7 - (m : ℝ)|
  · have hr_lt : r < 5 := sturmian_run_lt_of_large_dist α7_pos α7_lt_half
      (K := 5) (by push_cast; linarith [α7_bounds.1]) hδ_ge hm_half hust
    omega
  · push Not at hδ_ge
    by_contra hgt
    push Not at hgt
    have hr5 : 5 ≤ r := by omega
    -- Force full colour: 2 ∣ m and 12 ∣ (p - m).
    have hK_true : (1 : ℝ) ≤ (5 : ℝ) * α7 := by linarith [α7_bounds.1]
    have hK_fl : ⌊(5 : ℝ) * α7⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [α7_bounds.1, α7_bounds.2]
    have hK_false : (2 : ℤ) ≤ (5 : ℤ) - ⌊(5 : ℝ) * α7⌋ - 1 := by rw [hK_fl]; omega
    obtain ⟨ka, hka, hua⟩ := exists_true_in_block α7_pos α7_lt_one hK_true hr5
    obtain ⟨kb1, hkb1, kb2, hkb2, hub1, hub2, hcf_consec⟩ :=
      exists_two_consec_false_in_block α7_pos α7_lt_one hK_false hr5
    have hca := sturmian_match_counts_of_small_dist α7_pos α7_lt_half hδ_ge (hust ka hka)
    have hcb1 := sturmian_match_counts_of_small_dist α7_pos α7_lt_half hδ_ge (hust kb1 hkb1)
    have hcb2 := sturmian_match_counts_of_small_dist α7_pos α7_lt_half hδ_ge (hust kb2 hkb2)
    have hm0 : 0 ≤ m := hca.1
    have hm_le_p : m.toNat ≤ p := by
      have : (countFalse (sturmian α7) (i + ka) : ℤ) ≤ countFalse (sturmian α7) (i + ka + p) :=
        Int.ofNat_le.mpr (countFalse_mono _ (Nat.le_add_right _ _))
      omega
    have hma : m.toNat % 2 = 0 := by
      have hya := (colour_match_implies y7_disjoint_yPrime7 (hrun ka hka)).2.1 hua
      have hct : countTrue (sturmian α7) (i + ka + p) = countTrue (sturmian α7) (i + ka) + m.toNat := by
        omega
      rw [hct] at hya
      have hval := congrArg Fin.val hya
      simp only [y7] at hval
      have hmod : (countTrue (sturmian α7) (i + ka) + m.toNat) % 2 =
          (countTrue (sturmian α7) (i + ka) % 2 + m.toNat % 2) % 2 := Nat.add_mod _ _ _
      rw [hmod] at hval
      exact y7_match_even _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) hval
    have hmb : (p - m.toNat) % 12 = 0 := by
      have hyb1 := (colour_match_implies y7_disjoint_yPrime7 (hrun kb1 hkb1)).2.2 hub1
      have hyb2 := (colour_match_implies y7_disjoint_yPrime7 (hrun kb2 hkb2)).2.2 hub2
      have hcf1 : countFalse (sturmian α7) (i + kb1 + p) =
          countFalse (sturmian α7) (i + kb1) + (p - m.toNat) := by omega
      have hcf2 : countFalse (sturmian α7) (i + kb2 + p) =
          countFalse (sturmian α7) (i + kb1) + 1 + (p - m.toNat) := by omega
      rw [hcf1] at hyb1
      rw [hcf2, hcf_consec] at hyb2
      have hv1 := congrArg Fin.val hyb1
      have hv2 := congrArg Fin.val hyb2
      simp only [y'7] at hv1 hv2
      set s := countFalse (sturmian α7) (i + kb1)
      set t := p - m.toNat
      have hm1 : (s + t) % 12 = (s % 12 + t % 12) % 12 := Nat.add_mod s t 12
      have hm2 : (s + 1) % 12 = (s % 12 + 1) % 12 := (Nat.mod_add_mod s 12 1).symm
      have hm3 : (s + 1 + t) % 12 = (s % 12 + 1 + t % 12) % 12 := by
        rw [Nat.add_mod (s + 1) t, hm2, Nat.mod_add_mod]
      rw [hm1] at hv1
      rw [hm2, hm3] at hv2
      exact y'7_consec_match_dvd12 (s % 12) (Nat.mod_lt _ (by omega)) (t % 12)
        (Nat.mod_lt _ (by omega)) hv1 hv2
    -- Locate level k ≥ 1 for δ = |p * α7 - m|.
    have hη0_eq : eta a7 α7 0 = α7 := by unfold eta; simp [convP, convQ, convPQ]
    have hη0_pos : 0 < eta a7 α7 0 := by rw [hη0_eq]; exact α7_pos
    have hη1_pos : 0 < eta a7 α7 1 := by
      have hp1 : convP a7 1 = 1 := by decide
      have hq1 : convQ a7 1 = 4 := by decide
      unfold eta; rw [hp1, hq1]; push_cast; norm_num; linarith [α7_bounds.2]
    have hη1_lt : eta a7 α7 1 < eta a7 α7 0 := by
      have hp1 : convP a7 1 = 1 := by decide
      have hq1 : convQ a7 1 = 4 := by decide
      rw [hη0_eq]; unfold eta; rw [hp1, hq1]; push_cast; norm_num; linarith [α7_bounds.1]
    have hη2_pos : 0 < eta a7 α7 2 := by
      have hp2 : convP a7 2 = 1 := by decide
      have hq2 : convQ a7 2 = 5 := by decide
      unfold eta; rw [hp2, hq2]; push_cast; norm_num; linarith [α7_bounds.1]
    have hη2_lt : eta a7 α7 2 < eta a7 α7 1 := by
      have hrat := eta7_k2_ratio
      have hbr := θ7_bracket_sound 2
      have hlt1 : θ7 2 < 1 := by norm_num [θ7Bracket] at hbr; linarith
      have : eta a7 α7 2 = θ7 2 * eta a7 α7 1 := by
        rw [← hrat, div_mul_cancel₀ _ (ne_of_gt hη1_pos)]
      nlinarith
    have hθ_pos : ∀ r' < 3, 0 < θ7 r' := fun r' _ => by
      have hbr := θ7_bracket_sound r'
      have hnn : (0 : ℝ) ≤ ((θ7Bracket r').1 : ℝ) / 1000 := by positivity
      linarith
    have hθ_le : ∀ r' < 3, θ7 r' ≤ 4 / 5 := fun r' hr' => by
      have hbr := θ7_bracket_sound r'
      interval_cases r' <;> norm_num [θ7Bracket] at hbr <;> linarith
    obtain ⟨hη_pos, hη_dec, hlevel⟩ := eta_level_exists (T := 3) (M := 4 / 5)
      (by omega) hη0_pos hη1_pos hη1_lt hη2_pos hη2_lt eta7_periodic_ratio hθ_pos hθ_le (by norm_num)
    have hδ0 : 0 < |(p : ℝ) * α7 - (m : ℝ)| := by
      rw [abs_pos]
      exact sub_ne_zero.mpr (α7_irrational (u := (p : ℤ)) (v := m) (by omega))
    obtain ⟨k, hk1, hδ_lo, hδ_hi⟩ := hlevel |(p : ℝ) * α7 - (m : ℝ)| hδ0 (by rw [hη0_eq]; exact hδ_ge)
    -- Dispatch k = 1, k = 2, or k ≥ 3 to checkLevelClass_sound!
    have hle_p : r * 5 ≤ p := by
      by_cases hk_1 : k = 1
      · subst hk_1
        have hbr := θ7_bracket_sound 1
        dsimp [θ7Bracket] at hbr
        exact checkLevelClass_sound (den := 5) (loN := 720) (hiN := 721) (prec := 1000)
          (mode := .exact (convQ a7 1) (convQPrev a7 1))
          α7_pos α7_lt_half (fun _ _ hu => α7_irrational hu) a7_ge_one
          (le_refl 1) (by omega) (by omega) rfl rfl (hη_pos 1) (hη_pos 0) (hη_pos 2)
          (hη_dec 0) (hη_dec 1)
          (by rw [eta7_k1_ratio]; exact hbr.1) (by rw [eta7_k1_ratio]; exact hbr.2)
          ⟨rfl, rfl⟩ level7_k1_ok hp0 hm0 hδ_lo hδ_hi hδ_ge hma hmb hust
      · by_cases hk_2 : k = 2
        · subst hk_2
          have hbr := θ7_bracket_sound 2
          dsimp [θ7Bracket] at hbr
          exact checkLevelClass_sound (den := 5) (loN := 387) (hiN := 388) (prec := 1000)
            (mode := .exact (convQ a7 2) (convQPrev a7 2))
            α7_pos α7_lt_half (fun _ _ hu => α7_irrational hu) a7_ge_one
            (by omega) (by omega) (by omega) rfl rfl (hη_pos 2) (hη_pos 1) (hη_pos 3)
            (hη_dec 1) (hη_dec 2)
            (by rw [eta7_k2_ratio]; exact hbr.1) (by rw [eta7_k2_ratio]; exact hbr.2)
            ⟨rfl, rfl⟩ level7_k2_ok hp0 hm0 hδ_lo hδ_hi hδ_ge hma hmb hust
        · have hk3 : 3 ≤ k := by omega
          let s := (k - 3) % 12
          have hs_lt : s < 12 := Nat.mod_lt _ (by omega)
          have hmod_eq : convModState a7 2 12 k = convModState a7 2 12 (3 + s) :=
            convModState_periodic (by decide) 2 12 12 (by omega) a7_per12 level7_mod_per12 k hk3
          have hak1_eq : a7 (k + 1) = a7 (3 + s + 1) := by
            have hk4 : k + 1 = (k - 3) + 4 := by omega
            have hs4 : 3 + s + 1 = s + 4 := by omega
            rw [hk4, hs4, a7_per3, a7_per3]
            have : s % 3 = (k - 3) % 3 := Nat.mod_mod_of_dvd (k - 3) (by omega)
            rw [this]
          have hrat_eq : eta a7 α7 k / eta a7 α7 (k - 1) = θ7 s := by
            set t := k - 3
            have h1 : k = t + 3 := by omega
            have h2 : k - 1 = t + 2 := by omega
            rw [h2, h1, eta7_periodic_ratio t, mul_div_cancel_right₀ _ (ne_of_gt (hη_pos _))]
            have hmod3 : s % 3 = t % 3 := Nat.mod_mod_of_dvd t (by omega)
            unfold θ7; rw [hmod3, Nat.mod_mod]
          have hbr := θ7_bracket_sound s
          have hchk_s := (List.all_eq_true.mp level7_tail_ok) s (List.mem_range.mpr hs_lt)
          have hdec_k : eta a7 α7 k < eta a7 α7 (k - 1) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega]
            exact hη_dec (k - 1)
          exact checkLevelClass_sound (den := 5) (mode := .unit)
            α7_pos α7_lt_half (fun _ _ hu => α7_irrational hu) a7_ge_one
            hk1 (by omega) (by omega) hak1_eq hmod_eq (hη_pos k) (hη_pos (k - 1)) (hη_pos (k + 1))
            hdec_k (hη_dec k) (by rw [hrat_eq]; exact hbr.1) (by rw [hrat_eq]; exact hbr.2)
            (convQPrev_bounds a7_ge_one hk1).2 hchk_s hp0 hm0 hδ_lo hδ_hi hδ_ge hma hmb hust
    omega

/-- All-periods run bound for `v7`: every match run satisfies `r * 5 ≤ p`. -/
theorem v7_run_bound (i p r : ℕ) (hp : 0 < p)
    (hrun : ∀ k < r, v7 (i + k) = v7 (i + k + p)) :
    r * 5 ≤ p := by
  by_cases hlt : p < 20
  · exact v7_small_periods hp hlt hrun
  · exact v7_large_periods (by omega) hrun

/-- Critical exponent upper bound `critExp v7 ≤ 6 / 5`. -/
theorem v7_critExp_le : critExp v7 ≤ (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) :=
  critExp_le_of_run_bound (num := 6) (den := 5) (by omega) (by omega)
    (fun i p r hp hrun => by simpa using v7_run_bound i p r hp hrun)

/-- Exact attained critical exponent of `v7`: `critExp v7 = 6 / 5` (achieved as a maximum). -/
theorem v7_critExp_eq :
    critExp v7 = (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ∧
    (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v7 :=
  attains_critExp_of_period (num := 6) (den := 5) (by omega) v7_critExp_le v7_attains (by omega)

end BalancedRepetitionThreshold
