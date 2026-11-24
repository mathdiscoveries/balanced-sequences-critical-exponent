module

public import BalancedRepetitionThreshold.RotationEngine

import Mathlib.Tactic

/-!
# Exact Unconditional Proof for the 9-Letter Balanced Witness `v9` (`E(v9) = 8 / 7`)

Defines `v9 = colour (sturmian α9) y9 y'9` with:
- `α9 = (41 - 2 √2) / 239` (continued fraction `[0; 6, 3, (1, 4)]`),
- `y9 = (1 2)^ω` (`[0, 1]` in 0-indexed `Fin 9`),
- `y'9 = (3 6 4 7 5 8 3 9 4 6 5 7 3 8 4 9 5 6 3 7 4 8 5 9)^ω` (period 24, interleaving cycles
  `(3 4 5)` and `(6 7 8 9)`; same colouring as `x9` of RSV 2018 / DDP 2021).

Proves 100% unconditionally in the pure Lean 4 kernel:
- `v9_isBalanced : IsBalanced v9`
- `v9_usesAllLetters : UsesAllLetters v9`
- `v9_attains : HasPeriod v9 0 8 7` (prefix `3 6 4 7 5 1 8 3`, exponent `8 / 7`)
- `v9_run_bound : ∀ i p r, 0 < p → (∀ k < r, v9 (i + k) = v9 (i + k + p)) → r * 7 ≤ p`
- `v9_critExp_eq : critExp v9 = ((8 : ℝ) / 7 : ℝ) ∧ ((8 : ℝ) / 7 : ℝ) ∈ minPeriodExponentSet v9`
-/

@[expose] public section

namespace BalancedRepetitionThreshold

/-- Rare-letter frequency `α9 = (41 - 2 √2) / 239` for `v9`. -/
noncomputable def α9 : ℝ := (41 - 2 * Real.sqrt 2) / 239

/-- Period-2 colour table on `true` (`a`) positions of `v9` (0-indexed for printed `{1, 2}`). -/
def y9Tab : List ℕ := [0, 1]

/-- Period-24 colour table on `false` (`b`) positions of `v9` (0-indexed for printed `{3..9}`). -/
def y'9Tab : List ℕ :=
  [2, 5, 3, 6, 4, 7, 2, 8, 3, 5, 4, 6, 2, 7, 3, 8, 4, 5, 2, 6, 3, 7, 4, 8]

/-- Periodic colour sequence `y9` on `Fin 9`. -/
def y9 (k : ℕ) : Fin 9 :=
  ⟨y9Tab.getD (k % 2) 0, by
    have hk : k % 2 < 2 := Nat.mod_lt k (by omega)
    interval_cases (k % 2) <;> decide⟩

/-- Periodic colour sequence `y'9` on `Fin 9`. -/
def y'9 (k : ℕ) : Fin 9 :=
  ⟨y'9Tab.getD (k % 24) 0, by
    have hk : k % 24 < 24 := Nat.mod_lt k (by omega)
    interval_cases (k % 24) <;> decide⟩

/-- The 9-letter balanced witness `v9 = colour (sturmian α9) y9 y'9`. -/
noncomputable def v9 : ℕ → Fin 9 :=
  colour (sturmian α9) y9 y'9

/-- Tight rational enclosure of `√2`: `14142 / 10000 < √2 < 14143 / 10000`. -/
theorem sqrt2_bounds : (14142 : ℝ) / 10000 < Real.sqrt 2 ∧ Real.sqrt 2 < (14143 : ℝ) / 10000 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

/-- Rational enclosure of `α9`: `1597 / 10000 < α9 < 1598 / 10000`. -/
theorem α9_bounds : (1597 : ℝ) / 10000 < α9 ∧ α9 < (1598 : ℝ) / 10000 := by
  unfold α9
  have := sqrt2_bounds
  constructor <;> linarith

theorem α9_pos : 0 < α9 := by linarith [α9_bounds.1]
theorem α9_lt_half : α9 < 1 / 2 := by linarith [α9_bounds.2]
theorem α9_lt_one : α9 < 1 := by linarith [α9_bounds.2]

/-- `α9` is irrational. -/
theorem α9_irrational {u v : ℤ} (hu : u ≠ 0) : (u : ℝ) * α9 ≠ (v : ℝ) := by
  have hirr : Irrational (Real.sqrt ((2 : ℕ) : ℝ)) := by
    rw [irrational_sqrt_natCast_iff]
    rintro ⟨k, hk⟩
    have hkle : k ≤ 2 := by nlinarith
    interval_cases k <;> omega
  have hα : α9 = (((41 : ℤ) : ℝ) + ((-2 : ℤ) : ℝ) * Real.sqrt ((2 : ℕ) : ℝ)) / ((239 : ℕ) : ℝ) := by
    unfold α9; push_cast; ring
  rw [hα]
  exact quad_ne_int_div (A := 41) (B := -2) (C := 239) (D := 2) (by omega) (by omega) hirr hu

theorem y9_val_lt (m : ℕ) : (y9 m).val < 2 := by
  simp only [y9]
  have hm : m % 2 < 2 := Nat.mod_lt m (by omega)
  interval_cases (m % 2) <;> decide

theorem yPrime9_val_ge (m : ℕ) : 2 ≤ (y'9 m).val := by
  simp only [y'9]
  have hm : m % 24 < 24 := Nat.mod_lt m (by omega)
  interval_cases (m % 24) <;> decide

/-- `y9` and `y'9` have disjoint alphabets (`{0, 1}` vs `{2..8}`). -/
theorem y9_disjoint_yPrime9 (a b : ℕ) : y9 a ≠ y'9 b := by
  intro heq
  have h1 := y9_val_lt a
  have h2 := yPrime9_val_ge b
  have hv := congrArg Fin.val heq
  omega

/-- Direct 1-balance of `v9` (unconditional, zero recurrence hypothesis). -/
theorem v9_isBalanced : IsBalanced v9 := by
  apply colour_isBalanced_of_constantGap α9_pos α9_lt_one y9 y'9
  have hcg_y' : ∀ (c : Fin 9) (g r : ℕ), g ∣ 24 → 0 < g → r < g →
      2 ≤ c.val →
      (∀ t < 24, y'9Tab.getD t 0 = c.val ↔ t % g = r) →
      (∀ m, y9 m ≠ c) ∧ ∃ g' r', HasConstantGap y'9 c g' r' := by
    intro c g r hgdvd hg hr hc htab
    refine ⟨fun m h => by have := y9_val_lt m; have := congrArg Fin.val h; omega,
      g, r, hg, hr, fun m => ?_⟩
    rw [Fin.ext_iff]
    simp only [y'9]
    have hmod : m % g = (m % 24) % g := (Nat.mod_mod_of_dvd m hgdvd).symm
    rw [hmod]
    exact htab (m % 24) (Nat.mod_lt m (by omega))
  have hcg_y : ∀ (c : Fin 9) (r : ℕ), r < 2 →
      c.val < 2 →
      (∀ t < 2, y9Tab.getD t 0 = c.val ↔ t = r) →
      (∀ m, y'9 m ≠ c) ∧ ∃ g' r', HasConstantGap y9 c g' r' := by
    intro c r hr hc htab
    refine ⟨fun m h => by have := yPrime9_val_ge m; have := congrArg Fin.val h; omega,
      2, r, by omega, hr, fun m => ?_⟩
    rw [Fin.ext_iff]
    simp only [y9]
    exact htab (m % 2) (Nat.mod_lt m (by omega))
  intro c
  fin_cases c
  · exact Or.inl (hcg_y 0 0 (by omega) (by decide) (by decide))
  · exact Or.inl (hcg_y 1 1 (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 2 6 0 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 3 6 2 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 4 6 4 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 5 8 1 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 6 8 3 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 7 8 5 (by omega) (by omega) (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 8 8 7 (by omega) (by omega) (by omega) (by decide) (by decide))

/-- `v9` uses all 9 letters of `Fin 9`. -/
theorem v9_usesAllLetters : UsesAllLetters v9 := by
  apply colour_usesAllLetters α9_pos α9_lt_one y9 y'9
  intro c
  fin_cases c
  · exact Or.inl ⟨0, by decide⟩
  · exact Or.inl ⟨1, by decide⟩
  · exact Or.inr ⟨0, by decide⟩
  · exact Or.inr ⟨2, by decide⟩
  · exact Or.inr ⟨4, by decide⟩
  · exact Or.inr ⟨1, by decide⟩
  · exact Or.inr ⟨3, by decide⟩
  · exact Or.inr ⟨5, by decide⟩
  · exact Or.inr ⟨7, by decide⟩

/-- Exact attainment witness: prefix `3 6 4 7 5 1 8 3` (`v9 0 = v9 7 = 2`) has period `7`,
length `8`, exponent `8 / 7`. -/
theorem v9_attains : HasPeriod v9 0 8 7 := by
  have hb := α9_bounds
  have hfl : ∀ n m : ℕ, (m : ℝ) ≤ (n : ℝ) * α9 → (n : ℝ) * α9 < (m : ℝ) + 1 →
      ⌊(n : ℝ) * α9⌋ = (m : ℤ) := by
    intro n m h1 h2
    rw [Int.floor_eq_iff]; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hf1 : ⌊((1 : ℕ) : ℝ) * α9⌋ = 0 := hfl 1 0 (by push_cast; linarith) (by push_cast; linarith)
  have hf2 : ⌊((2 : ℕ) : ℝ) * α9⌋ = 0 := hfl 2 0 (by push_cast; linarith) (by push_cast; linarith)
  have hf8 : ⌊((8 : ℕ) : ℝ) * α9⌋ = 1 := hfl 8 1 (by push_cast; linarith) (by push_cast; linarith)
  have hf9 : ⌊((9 : ℕ) : ℝ) * α9⌋ = 1 := hfl 9 1 (by push_cast; linarith) (by push_cast; linarith)
  have hu0 : sturmian α9 0 = false := by
    unfold sturmian; change decide (⌊((2 : ℕ) : ℝ) * α9⌋ - ⌊((1 : ℕ) : ℝ) * α9⌋ = 1) = false
    rw [hf2, hf1]; decide
  have hu7 : sturmian α9 7 = false := by
    unfold sturmian; change decide (⌊((9 : ℕ) : ℝ) * α9⌋ - ⌊((8 : ℕ) : ℝ) * α9⌋ = 1) = false
    rw [hf9, hf8]; decide
  have hcf0 : countFalse (sturmian α9) 0 = 0 := by simp [countFalse]
  have hcf7 : countFalse (sturmian α9) 7 = 6 := by
    have hct7 := sturmian_countTrue_eq_floor α9_pos α9_lt_one 7
    have hsum7 := countTrue_add_countFalse (sturmian α9) 7
    change (countTrue (sturmian α9) 7 : ℤ) = ⌊((8 : ℕ) : ℝ) * α9⌋ at hct7
    rw [hf8] at hct7
    omega
  refine ⟨by omega, by omega, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [add_zero, zero_add, v9, colour, hu0, hu7, hcf0, hcf7, Bool.false_eq_true, ↓reduceIte]
  decide

/-! ### Small Periods (`1 ≤ p < 42`) via Pure-Kernel Cut Partition -/

/-- Exact sorted cut partition of `[0, 1)` for `L = 47` steps of `sturmian α9`. -/
def cuts9 : List (ℕ × ℤ) :=
  [(0, 0), (25, 4), (6, 1), (31, 5), (12, 2), (37, 6), (18, 3), (43, 7), (24, 4), (5, 1),
   (30, 5), (11, 2), (36, 6), (17, 3), (42, 7), (23, 4), (4, 1), (29, 5), (10, 2), (35, 6),
   (16, 3), (41, 7), (22, 4), (47, 8), (3, 1), (28, 5), (9, 2), (34, 6), (15, 3), (40, 7),
   (21, 4), (46, 8), (2, 1), (27, 5), (8, 2), (33, 6), (14, 3), (39, 7), (20, 4), (45, 8),
   (1, 1), (26, 5), (7, 2), (32, 6), (13, 3), (38, 7), (19, 4), (44, 8), (0, 1)]

private theorem cuts9_ok : checkCutPartition 47 1597 1598 10000 cuts9 = true := by decide

/-- Chunked pure-kernel small-period check over a slice of cut indices `t ∈ [t0, t0 + cnt)`. -/
private def checkSmall9Slice (t0 cnt : ℕ) : Bool :=
  (List.range cnt).all fun dt =>
    let t := t0 + dt
    let uWord := sturmianFactorFromCut cuts9 47 t
    (List.range 42).all fun p =>
      if p == 0 then true
      else
        let r0 := p / 7 + 1
        if avoidsMatchAt uWord p r0 then true
        else
          (List.range 2).all fun pa =>
            (List.range 24).all fun pb =>
              avoidsMatchAt (colourWord y9Tab y'9Tab 2 24 pa pb uWord) p r0

private theorem small9_s0 : checkSmall9Slice 0 8 = true := by decide
private theorem small9_s1 : checkSmall9Slice 8 8 = true := by decide
private theorem small9_s2 : checkSmall9Slice 16 8 = true := by decide
private theorem small9_s3 : checkSmall9Slice 24 8 = true := by decide
private theorem small9_s4 : checkSmall9Slice 32 8 = true := by decide
private theorem small9_s5 : checkSmall9Slice 40 8 = true := by decide

private theorem small9_ok : checkSmallPeriods 42 7 2 24 y9Tab y'9Tab 47 cuts9 = true := by
  unfold checkSmallPeriods
  rw [List.all_eq_true]
  intro t ht
  simp only [List.mem_range] at ht
  have hslice : ∀ t0 cnt, checkSmall9Slice t0 cnt = true → ∀ dt < cnt,
      (List.range 42).all (fun p =>
        if p == 0 then true
        else
          let r0 := p / 7 + 1
          if avoidsMatchAt (sturmianFactorFromCut cuts9 47 (t0 + dt)) p r0 then true
          else
            (List.range 2).all fun pa =>
              (List.range 24).all fun pb =>
                avoidsMatchAt (colourWord y9Tab y'9Tab 2 24 pa pb (sturmianFactorFromCut cuts9 47 (t0 + dt))) p r0) = true := by
    intro t0 cnt hs dt hdt
    unfold checkSmall9Slice at hs
    exact (List.all_eq_true.mp hs) dt (List.mem_range.mpr hdt)
  by_cases h0 : t < 8
  · simpa using hslice 0 8 small9_s0 t h0
  · by_cases h1 : t < 16
    · have := hslice 8 8 small9_s1 (t - 8) (by omega)
      have heq : 8 + (t - 8) = t := by omega
      rwa [heq] at this
    · by_cases h2 : t < 24
      · have := hslice 16 8 small9_s2 (t - 16) (by omega)
        have heq : 16 + (t - 16) = t := by omega
        rwa [heq] at this
      · by_cases h3 : t < 32
        · have := hslice 24 8 small9_s3 (t - 24) (by omega)
          have heq : 24 + (t - 24) = t := by omega
          rwa [heq] at this
        · by_cases h4 : t < 40
          · have := hslice 32 8 small9_s4 (t - 32) (by omega)
            have heq : 32 + (t - 32) = t := by omega
            rwa [heq] at this
          · have := hslice 40 8 small9_s5 (t - 40) (by omega)
            have heq : 40 + (t - 40) = t := by omega
            rwa [heq] at this

/-- Small-period upper bound for `v9`: every period `1 ≤ p < 42` has `r * 7 ≤ p`. -/
theorem v9_small_periods {i p r : ℕ} (hp0 : 0 < p) (hp_lt : p < 42)
    (hrun : ∀ k < r, v9 (i + k) = v9 (i + k + p)) :
    r * 7 ≤ p :=
  checkSmallPeriods_sound (den := 7) (P_small := 42) (L := 47) (ma := 2) (mb := 24) (prec := 10000)
    α9_pos α9_lt_one (by omega) (by omega) (by omega) (by omega)
    (fun q _ hq => by omega) y9_disjoint_yPrime9 (fun _ => rfl) (fun _ => rfl)
    α9_bounds.1 α9_bounds.2 cuts9_ok small9_ok hp0 hp_lt hrun

/-! ### All Large Periods (`p ≥ 42`) via Periodic Continued-Fraction Level Analysis -/

/-- Partial quotients `[0; 6, 3, (1, 4)]` of `α9`. -/
def a9 (k : ℕ) : ℕ :=
  if k = 0 then 0
  else if k = 1 then 6
  else if k = 2 then 3
  else match (k - 3) % 2 with
    | 0 => 1
    | _ => 4

/-- Periodic error ratios `θ9 r = η_{3+r} / η_{2+r}` (`r ∈ {0, 1}`). -/
noncomputable def θ9 (r : ℕ) : ℝ :=
  match r % 2 with
  | 0 => (-1 + Real.sqrt 2) / 2
  | _ => -2 + 2 * Real.sqrt 2

theorem a9_ge_one (j : ℕ) (hj : 1 ≤ j) : 1 ≤ a9 j := by
  unfold a9
  split_ifs <;> try omega
  split <;> omega

theorem a9_per2 (n : ℕ) : a9 (n + 4) = a9 (4 + n % 2) := by
  have h1 : n + 4 ≠ 0 ∧ n + 4 ≠ 1 ∧ n + 4 ≠ 2 := by omega
  have h2 : 4 + n % 2 ≠ 0 ∧ 4 + n % 2 ≠ 1 ∧ 4 + n % 2 ≠ 2 := by omega
  unfold a9
  simp only [h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2, ↓reduceIte]
  have hmod : (n + 4 - 3) % 2 = (4 + n % 2 - 3) % 2 := by omega
  rw [hmod]

theorem a9_per8 (k : ℕ) (hk : 3 ≤ k) : a9 (k + 1 + 8) = a9 (k + 1) := by
  have h1 : k + 1 + 8 ≠ 0 ∧ k + 1 + 8 ≠ 1 ∧ k + 1 + 8 ≠ 2 := by omega
  have h2 : k + 1 ≠ 0 ∧ k + 1 ≠ 1 ∧ k + 1 ≠ 2 := by omega
  unfold a9
  simp only [h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2, ↓reduceIte]
  have hmod : (k + 1 + 8 - 3) % 2 = (k + 1 - 3) % 2 := by omega
  rw [hmod]

theorem eta9_periodic_ratio : ∀ n : ℕ, eta a9 α9 (n + 3) = θ9 (n % 2) * eta a9 α9 (n + 2) := by
  apply eta_periodic_ratio (T := 2) (by omega) θ9
  · have hp2 : convP a9 2 = 3 := by decide
    have hq2 : convQ a9 2 = 19 := by decide
    have hp3 : convP a9 3 = 4 := by decide
    have hq3 : convQ a9 3 = 25 := by decide
    unfold eta θ9 α9
    rw [hp2, hq2, hp3, hq3]
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [Nat.cast_ofNat]
    nlinarith
  · exact a9_per2
  · intro r hr
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    interval_cases r
    · change 1 - ((4 : ℕ) : ℝ) * ((-1 + Real.sqrt 2) / 2) =
          ((-1 + Real.sqrt 2) / 2) * (-2 + 2 * Real.sqrt 2)
      push_cast; nlinarith
    · change 1 - ((1 : ℕ) : ℝ) * (-2 + 2 * Real.sqrt 2) =
          (-2 + 2 * Real.sqrt 2) * ((-1 + Real.sqrt 2) / 2)
      push_cast; nlinarith

/-- Scaled rational brackets `(lo, hi)` (denominator `1000`) for `θ9 (r % 2)`. -/
def θ9Bracket (r : ℕ) : ℕ × ℕ :=
  match r % 2 with
  | 0 => (207, 208)
  | _ => (828, 829)

theorem θ9_bracket_sound (r : ℕ) :
    ((θ9Bracket r).1 : ℝ) / 1000 < θ9 r ∧ θ9 r < ((θ9Bracket r).2 : ℝ) / 1000 := by
  have hs := sqrt2_bounds
  have hmod : r % 2 < 2 := Nat.mod_lt r (by omega)
  unfold θ9Bracket θ9
  interval_cases (r % 2) <;> constructor <;> push_cast <;> linarith

/-- Exact ratio identities at `k = 1` and `k = 2`. -/
theorem eta9_k1_ratio : eta a9 α9 1 / eta a9 α9 0 = (-1 + 2 * Real.sqrt 2) / 7 := by
  have hp0 : convP a9 0 = 0 := by decide
  have hq0 : convQ a9 0 = 1 := by decide
  have hp1 : convP a9 1 = 1 := by decide
  have hq1 : convQ a9 1 = 6 := by decide
  have h0pos : 0 < eta a9 α9 0 := by unfold eta; rw [hp0, hq0]; simp; exact α9_pos
  rw [div_eq_iff (ne_of_gt h0pos)]
  unfold eta α9
  rw [hp0, hq0, hp1, hq1]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  nlinarith

theorem eta9_k2_ratio : eta a9 α9 2 / eta a9 α9 1 = θ9 1 := by
  have hp1 : convP a9 1 = 1 := by decide
  have hq1 : convQ a9 1 = 6 := by decide
  have hp2 : convP a9 2 = 3 := by decide
  have hq2 : convQ a9 2 = 19 := by decide
  have h1pos : 0 < eta a9 α9 1 := by
    unfold eta; rw [hp1, hq1]; have := α9_bounds; push_cast; norm_num; linarith
  rw [div_eq_iff (ne_of_gt h1pos)]
  unfold eta θ9 α9
  rw [hp1, hq1, hp2, hq2]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [Nat.cast_ofNat, Nat.cast_one]
  nlinarith

private theorem level9_k1_ok :
    let st := convModState a9 2 24 1
    checkLevelClass 2 24 7 (a9 2) st.1 st.2.1 st.2.2.1 st.2.2.2 261 262 1000
      (.exact (convQ a9 1) (convQPrev a9 1)) = true := by decide

private theorem level9_k2_ok :
    let st := convModState a9 2 24 2
    checkLevelClass 2 24 7 (a9 3) st.1 st.2.1 st.2.2.1 st.2.2.2 828 829 1000
      (.exact (convQ a9 2) (convQPrev a9 2)) = true := by decide

private theorem level9_mod_per8 :
    convModState a9 2 24 (3 + 8) = convModState a9 2 24 3 := by decide

private theorem level9_tail_ok :
    (List.range 8).all (fun s =>
      let st := convModState a9 2 24 (3 + s)
      let br := θ9Bracket s
      checkLevelClass 2 24 7 (a9 (3 + s + 1)) st.1 st.2.1 st.2.2.1 st.2.2.2 br.1 br.2 1000 .unit) = true := by
  decide

private theorem y9_match_even : ∀ s < 2, ∀ t < 2,
    y9Tab.getD s 0 = y9Tab.getD ((s + t) % 2) 0 → t = 0 := by decide

private theorem y'9_consec_match_dvd24 : ∀ s < 24, ∀ t < 24,
    y'9Tab.getD s 0 = y'9Tab.getD ((s + t) % 24) 0 →
    y'9Tab.getD ((s + 1) % 24) 0 = y'9Tab.getD ((s + 1 + t) % 24) 0 → t = 0 := by decide

/-- Large-period upper bound for `v9`: every period `p ≥ 42` has `r * 7 ≤ p`. -/
theorem v9_large_periods {i p r : ℕ} (hp42 : 42 ≤ p)
    (hrun : ∀ k < r, v9 (i + k) = v9 (i + k + p)) :
    r * 7 ≤ p := by
  have hp0 : 0 < p := by omega
  have hust : ∀ k < r, sturmian α9 (i + k) = sturmian α9 (i + k + p) :=
    fun k hk => (colour_match_implies y9_disjoint_yPrime9 (hrun k hk)).1
  obtain ⟨m, hm_half⟩ := exists_nearest_int ((p : ℝ) * α9)
  by_cases hδ_ge : α9 ≤ |(p : ℝ) * α9 - (m : ℝ)|
  · have hr_lt : r < 7 := sturmian_run_lt_of_large_dist α9_pos α9_lt_half
      (K := 7) (by push_cast; linarith [α9_bounds.1]) hδ_ge hm_half hust
    omega
  · push Not at hδ_ge
    by_contra hgt
    push Not at hgt
    have hr7 : 7 ≤ r := by omega
    have hK_true : (1 : ℝ) ≤ (7 : ℝ) * α9 := by linarith [α9_bounds.1]
    have hK_fl : ⌊(7 : ℝ) * α9⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [α9_bounds.1, α9_bounds.2]
    have hK_false : (2 : ℤ) ≤ (7 : ℤ) - ⌊(7 : ℝ) * α9⌋ - 1 := by rw [hK_fl]; omega
    obtain ⟨ka, hka, hua⟩ := exists_true_in_block α9_pos α9_lt_one hK_true hr7
    obtain ⟨kb1, hkb1, kb2, hkb2, hub1, hub2, hcf_consec⟩ :=
      exists_two_consec_false_in_block α9_pos α9_lt_one hK_false hr7
    have hca := sturmian_match_counts_of_small_dist α9_pos α9_lt_half hδ_ge (hust ka hka)
    have hcb1 := sturmian_match_counts_of_small_dist α9_pos α9_lt_half hδ_ge (hust kb1 hkb1)
    have hcb2 := sturmian_match_counts_of_small_dist α9_pos α9_lt_half hδ_ge (hust kb2 hkb2)
    have hm0 : 0 ≤ m := hca.1
    have hm_le_p : m.toNat ≤ p := by
      have : (countFalse (sturmian α9) (i + ka) : ℤ) ≤ countFalse (sturmian α9) (i + ka + p) :=
        Int.ofNat_le.mpr (countFalse_mono _ (Nat.le_add_right _ _))
      omega
    have hma : m.toNat % 2 = 0 := by
      have hya := (colour_match_implies y9_disjoint_yPrime9 (hrun ka hka)).2.1 hua
      have hct : countTrue (sturmian α9) (i + ka + p) = countTrue (sturmian α9) (i + ka) + m.toNat := by
        omega
      rw [hct] at hya
      have hval := congrArg Fin.val hya
      simp only [y9] at hval
      have hmod : (countTrue (sturmian α9) (i + ka) + m.toNat) % 2 =
          (countTrue (sturmian α9) (i + ka) % 2 + m.toNat % 2) % 2 := Nat.add_mod _ _ _
      rw [hmod] at hval
      exact y9_match_even _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) hval
    have hmb : (p - m.toNat) % 24 = 0 := by
      have hyb1 := (colour_match_implies y9_disjoint_yPrime9 (hrun kb1 hkb1)).2.2 hub1
      have hyb2 := (colour_match_implies y9_disjoint_yPrime9 (hrun kb2 hkb2)).2.2 hub2
      have hcf1 : countFalse (sturmian α9) (i + kb1 + p) =
          countFalse (sturmian α9) (i + kb1) + (p - m.toNat) := by omega
      have hcf2 : countFalse (sturmian α9) (i + kb2 + p) =
          countFalse (sturmian α9) (i + kb1) + 1 + (p - m.toNat) := by omega
      rw [hcf1] at hyb1
      rw [hcf2, hcf_consec] at hyb2
      have hv1 := congrArg Fin.val hyb1
      have hv2 := congrArg Fin.val hyb2
      simp only [y'9] at hv1 hv2
      set s := countFalse (sturmian α9) (i + kb1)
      set t := p - m.toNat
      have hm1 : (s + t) % 24 = (s % 24 + t % 24) % 24 := Nat.add_mod s t 24
      have hm2 : (s + 1) % 24 = (s % 24 + 1) % 24 := (Nat.mod_add_mod s 24 1).symm
      have hm3 : (s + 1 + t) % 24 = (s % 24 + 1 + t % 24) % 24 := by
        rw [Nat.add_mod (s + 1) t, hm2, Nat.mod_add_mod]
      rw [hm1] at hv1
      rw [hm2, hm3] at hv2
      exact y'9_consec_match_dvd24 (s % 24) (Nat.mod_lt _ (by omega)) (t % 24)
        (Nat.mod_lt _ (by omega)) hv1 hv2
    have hη0_eq : eta a9 α9 0 = α9 := by unfold eta; simp [convP, convQ, convPQ]
    have hη0_pos : 0 < eta a9 α9 0 := by rw [hη0_eq]; exact α9_pos
    have hη1_pos : 0 < eta a9 α9 1 := by
      have hp1 : convP a9 1 = 1 := by decide
      have hq1 : convQ a9 1 = 6 := by decide
      unfold eta; rw [hp1, hq1]; push_cast; norm_num; linarith [α9_bounds.2]
    have hη1_lt : eta a9 α9 1 < eta a9 α9 0 := by
      have hp1 : convP a9 1 = 1 := by decide
      have hq1 : convQ a9 1 = 6 := by decide
      rw [hη0_eq]; unfold eta; rw [hp1, hq1]; push_cast; norm_num; linarith [α9_bounds.1]
    have hη2_pos : 0 < eta a9 α9 2 := by
      have hp2 : convP a9 2 = 3 := by decide
      have hq2 : convQ a9 2 = 19 := by decide
      unfold eta; rw [hp2, hq2]; push_cast; norm_num; linarith [α9_bounds.1]
    have hη2_lt : eta a9 α9 2 < eta a9 α9 1 := by
      have hrat := eta9_k2_ratio
      have hbr := θ9_bracket_sound 1
      have hlt1 : θ9 1 < 1 := by norm_num [θ9Bracket] at hbr; linarith
      have : eta a9 α9 2 = θ9 1 * eta a9 α9 1 := by
        rw [← hrat, div_mul_cancel₀ _ (ne_of_gt hη1_pos)]
      nlinarith
    have hθ_pos : ∀ r' < 2, 0 < θ9 r' := fun r' _ => by
      have hbr := θ9_bracket_sound r'
      have hnn : (0 : ℝ) ≤ ((θ9Bracket r').1 : ℝ) / 1000 := by positivity
      linarith
    have hθ_le : ∀ r' < 2, θ9 r' ≤ 9 / 10 := fun r' hr' => by
      have hbr := θ9_bracket_sound r'
      interval_cases r' <;> norm_num [θ9Bracket] at hbr <;> linarith
    obtain ⟨hη_pos, hη_dec, hlevel⟩ := eta_level_exists (T := 2) (M := 9 / 10)
      (by omega) hη0_pos hη1_pos hη1_lt hη2_pos hη2_lt eta9_periodic_ratio hθ_pos hθ_le (by norm_num)
    have hδ0 : 0 < |(p : ℝ) * α9 - (m : ℝ)| := by
      rw [abs_pos]
      exact sub_ne_zero.mpr (α9_irrational (u := (p : ℤ)) (v := m) (by omega))
    obtain ⟨k, hk1, hδ_lo, hδ_hi⟩ := hlevel |(p : ℝ) * α9 - (m : ℝ)| hδ0 (by rw [hη0_eq]; exact hδ_ge)
    have hle_p : r * 7 ≤ p := by
      by_cases hk_1 : k = 1
      · subst hk_1
        have hs := sqrt2_bounds
        have hlo1 : ((261 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) < eta a9 α9 1 / eta a9 α9 0 := by
          rw [eta9_k1_ratio]; push_cast; linarith
        have hhi1 : eta a9 α9 1 / eta a9 α9 0 < ((262 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by
          rw [eta9_k1_ratio]; push_cast; linarith
        exact checkLevelClass_sound (den := 7) (loN := 261) (hiN := 262) (prec := 1000)
          (mode := .exact (convQ a9 1) (convQPrev a9 1))
          α9_pos α9_lt_half (fun _ _ hu => α9_irrational hu) a9_ge_one
          (le_refl 1) (by omega) (by omega) rfl rfl (hη_pos 1) (hη_pos 0) (hη_pos 2)
          (hη_dec 0) (hη_dec 1) hlo1 hhi1 ⟨rfl, rfl⟩ level9_k1_ok hp0 hm0 hδ_lo hδ_hi hδ_ge hma hmb hust
      · by_cases hk_2 : k = 2
        · subst hk_2
          have hbr := θ9_bracket_sound 1
          dsimp [θ9Bracket] at hbr
          exact checkLevelClass_sound (den := 7) (loN := 828) (hiN := 829) (prec := 1000)
            (mode := .exact (convQ a9 2) (convQPrev a9 2))
            α9_pos α9_lt_half (fun _ _ hu => α9_irrational hu) a9_ge_one
            (by omega) (by omega) (by omega) rfl rfl (hη_pos 2) (hη_pos 1) (hη_pos 3)
            (hη_dec 1) (hη_dec 2)
            (by rw [eta9_k2_ratio]; exact hbr.1) (by rw [eta9_k2_ratio]; exact hbr.2)
            ⟨rfl, rfl⟩ level9_k2_ok hp0 hm0 hδ_lo hδ_hi hδ_ge hma hmb hust
        · have hk3 : 3 ≤ k := by omega
          let s := (k - 3) % 8
          have hs_lt : s < 8 := Nat.mod_lt _ (by omega)
          have hmod_eq : convModState a9 2 24 k = convModState a9 2 24 (3 + s) :=
            convModState_periodic (by decide) 2 24 8 (by omega) a9_per8 level9_mod_per8 k hk3
          have hak1_eq : a9 (k + 1) = a9 (3 + s + 1) := by
            have hk4 : k + 1 = (k - 3) + 4 := by omega
            have hs4 : 3 + s + 1 = s + 4 := by omega
            rw [hk4, hs4, a9_per2, a9_per2]
            have : s % 2 = (k - 3) % 2 := Nat.mod_mod_of_dvd (k - 3) (by omega)
            rw [this]
          have hrat_eq : eta a9 α9 k / eta a9 α9 (k - 1) = θ9 s := by
            set t := k - 3
            have h1 : k = t + 3 := by omega
            have h2 : k - 1 = t + 2 := by omega
            rw [h2, h1, eta9_periodic_ratio t, mul_div_cancel_right₀ _ (ne_of_gt (hη_pos _))]
            have hmod2 : s % 2 = t % 2 := Nat.mod_mod_of_dvd t (by omega)
            unfold θ9; rw [hmod2, Nat.mod_mod]
          have hbr := θ9_bracket_sound s
          have hchk_s := (List.all_eq_true.mp level9_tail_ok) s (List.mem_range.mpr hs_lt)
          have hdec_k : eta a9 α9 k < eta a9 α9 (k - 1) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega]
            exact hη_dec (k - 1)
          exact checkLevelClass_sound (den := 7) (mode := .unit)
            α9_pos α9_lt_half (fun _ _ hu => α9_irrational hu) a9_ge_one
            hk1 (by omega) (by omega) hak1_eq hmod_eq (hη_pos k) (hη_pos (k - 1)) (hη_pos (k + 1))
            hdec_k (hη_dec k) (by rw [hrat_eq]; exact hbr.1) (by rw [hrat_eq]; exact hbr.2)
            (convQPrev_bounds a9_ge_one hk1).2 hchk_s hp0 hm0 hδ_lo hδ_hi hδ_ge hma hmb hust
    omega

/-- All-periods run bound for `v9`: every match run satisfies `r * 7 ≤ p`. -/
theorem v9_run_bound (i p r : ℕ) (hp : 0 < p)
    (hrun : ∀ k < r, v9 (i + k) = v9 (i + k + p)) :
    r * 7 ≤ p := by
  by_cases hlt : p < 42
  · exact v9_small_periods hp hlt hrun
  · exact v9_large_periods (by omega) hrun

/-- Critical exponent upper bound `critExp v9 ≤ 8 / 7`. -/
theorem v9_critExp_le : critExp v9 ≤ (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) :=
  critExp_le_of_run_bound (num := 8) (den := 7) (by omega) (by omega)
    (fun i p r hp hrun => by simpa using v9_run_bound i p r hp hrun)

/-- Exact attained critical exponent of `v9`: `critExp v9 = 8 / 7` (achieved as a maximum). -/
theorem v9_critExp_eq :
    critExp v9 = (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ∧
    (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v9 :=
  attains_critExp_of_period (num := 8) (den := 7) (by omega) v9_critExp_le v9_attains (by omega)

end BalancedRepetitionThreshold
