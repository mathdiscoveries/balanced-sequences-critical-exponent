module

public import BalancedRepetitionThreshold.RotationEngine

import Mathlib.Tactic

/-!
# Exact Unconditional Proof for the 10-Letter Balanced Witness `v10` (`E(v10) = 9 / 8`)

Defines `v10 = colour (sturmian α10) y10 y'10` with:
- `α10 = (7 + √5) / 22` (continued fraction `[0; 2, 2, (1)]`; slope `θ = [0; 1, 2, (1)]`),
- `y10 = (1 2 3 4 5)^ω` (`[0, 1, 2, 3, 4]` in 0-indexed `Fin 10`),
- `y'10 = (6 7 8 9 10)^ω` (`[5, 6, 7, 8, 9]` in 0-indexed `Fin 10`),
(the `δ = 5` instance of the `x_{2δ}` colouring family of Dvořáková–Pelantová–Opočenská–Shur 2021,
Theorem 19, where Theorem 19 was stated only for `δ ≥ 7`).

Proves 100% unconditionally in the pure Lean 4 kernel:
- `v10_isBalanced : IsBalanced v10`
- `v10_usesAllLetters : UsesAllLetters v10`
- `v10_attains : HasPeriod v10 4 9 8` (factor `8 9 3 10 4 6 5 7 8`, exponent `9 / 8`)
- `v10_run_bound : ∀ i p r, 0 < p → (∀ k < r, v10 (i + k) = v10 (i + k + p)) → r * 8 ≤ p`
- `v10_critExp_eq : critExp v10 = ((9 : ℝ) / 8 : ℝ) ∧ ((9 : ℝ) / 8 : ℝ) ∈ minPeriodExponentSet v10`
-/

@[expose] public section

namespace BalancedRepetitionThreshold

/-- Rare-letter frequency `α10 = (7 + √5) / 22` for `v10`. -/
noncomputable def α10 : ℝ := (7 + Real.sqrt 5) / 22

/-- Period-5 colour table on `true` (`a`) positions of `v10` (0-indexed for printed `{1..5}`). -/
def y10Tab : List ℕ := [0, 1, 2, 3, 4]

/-- Period-5 colour table on `false` (`b`) positions of `v10` (0-indexed for printed `{6..10}`). -/
def y'10Tab : List ℕ := [5, 6, 7, 8, 9]

/-- Periodic colour sequence `y10` on `Fin 10`. -/
def y10 (k : ℕ) : Fin 10 :=
  ⟨y10Tab.getD (k % 5) 0, by
    have hk : k % 5 < 5 := Nat.mod_lt k (by omega)
    interval_cases (k % 5) <;> decide⟩

/-- Periodic colour sequence `y'10` on `Fin 10`. -/
def y'10 (k : ℕ) : Fin 10 :=
  ⟨y'10Tab.getD (k % 5) 0, by
    have hk : k % 5 < 5 := Nat.mod_lt k (by omega)
    interval_cases (k % 5) <;> decide⟩

/-- The 10-letter balanced witness `v10 = colour (sturmian α10) y10 y'10`. -/
noncomputable def v10 : ℕ → Fin 10 :=
  colour (sturmian α10) y10 y'10

/-- Tight rational enclosure of `√5`: `223606 / 100000 < √5 < 223607 / 100000`. -/
theorem sqrt5_bounds : (223606 : ℝ) / 100000 < Real.sqrt 5 ∧ Real.sqrt 5 < (223607 : ℝ) / 100000 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  constructor <;> nlinarith

/-- Rational enclosure of `α10`: `419 / 1000 < α10 < 420 / 1000`. -/
theorem α10_bounds : (419 : ℝ) / 1000 < α10 ∧ α10 < (420 : ℝ) / 1000 := by
  unfold α10
  have := sqrt5_bounds
  constructor <;> linarith

theorem α10_pos : 0 < α10 := by linarith [α10_bounds.1]
theorem α10_lt_half : α10 < 1 / 2 := by linarith [α10_bounds.2]
theorem α10_lt_one : α10 < 1 := by linarith [α10_bounds.2]

/-- `α10` is irrational. -/
theorem α10_irrational {u v : ℤ} (hu : u ≠ 0) : (u : ℝ) * α10 ≠ (v : ℝ) := by
  have hirr : Irrational (Real.sqrt ((5 : ℕ) : ℝ)) := by
    rw [irrational_sqrt_natCast_iff]
    rintro ⟨k, hk⟩
    have hkle : k ≤ 2 := by nlinarith
    interval_cases k <;> omega
  have hα : α10 = (((7 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * Real.sqrt ((5 : ℕ) : ℝ)) / ((22 : ℕ) : ℝ) := by
    unfold α10; push_cast; ring
  rw [hα]
  exact quad_ne_int_div (A := 7) (B := 1) (C := 22) (D := 5) (by omega) (by omega) hirr hu

theorem y10_val_lt (m : ℕ) : (y10 m).val < 5 := by
  simp only [y10]
  have hm : m % 5 < 5 := Nat.mod_lt m (by omega)
  interval_cases (m % 5) <;> decide

theorem yPrime10_val_ge (m : ℕ) : 5 ≤ (y'10 m).val := by
  simp only [y'10]
  have hm : m % 5 < 5 := Nat.mod_lt m (by omega)
  interval_cases (m % 5) <;> decide

/-- `y10` and `y'10` have disjoint alphabets (`{0..4}` vs `{5..9}`). -/
theorem y10_disjoint_yPrime10 (a b : ℕ) : y10 a ≠ y'10 b := by
  intro heq
  have h1 := y10_val_lt a
  have h2 := yPrime10_val_ge b
  have hv := congrArg Fin.val heq
  omega

/-- Direct 1-balance of `v10` (unconditional, zero recurrence hypothesis). -/
theorem v10_isBalanced : IsBalanced v10 := by
  apply colour_isBalanced_of_constantGap α10_pos α10_lt_one y10 y'10
  have hcg_y : ∀ (c : Fin 10) (r : ℕ), r < 5 → c.val < 5 →
      (∀ t < 5, y10Tab.getD t 0 = c.val ↔ t = r) →
      (∀ m, y'10 m ≠ c) ∧ ∃ g' r', HasConstantGap y10 c g' r' := by
    intro c r hr hc htab
    refine ⟨fun m h => by have := yPrime10_val_ge m; have := congrArg Fin.val h; omega,
      5, r, by omega, hr, fun m => ?_⟩
    rw [Fin.ext_iff]
    simp only [y10]
    exact htab (m % 5) (Nat.mod_lt m (by omega))
  have hcg_y' : ∀ (c : Fin 10) (r : ℕ), r < 5 → 5 ≤ c.val →
      (∀ t < 5, y'10Tab.getD t 0 = c.val ↔ t = r) →
      (∀ m, y10 m ≠ c) ∧ ∃ g' r', HasConstantGap y'10 c g' r' := by
    intro c r hr hc htab
    refine ⟨fun m h => by have := y10_val_lt m; have := congrArg Fin.val h; omega,
      5, r, by omega, hr, fun m => ?_⟩
    rw [Fin.ext_iff]
    simp only [y'10]
    exact htab (m % 5) (Nat.mod_lt m (by omega))
  intro c
  fin_cases c
  · exact Or.inl (hcg_y 0 0 (by omega) (by decide) (by decide))
  · exact Or.inl (hcg_y 1 1 (by omega) (by decide) (by decide))
  · exact Or.inl (hcg_y 2 2 (by omega) (by decide) (by decide))
  · exact Or.inl (hcg_y 3 3 (by omega) (by decide) (by decide))
  · exact Or.inl (hcg_y 4 4 (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 5 0 (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 6 1 (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 7 2 (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 8 3 (by omega) (by decide) (by decide))
  · exact Or.inr (hcg_y' 9 4 (by omega) (by decide) (by decide))

/-- `v10` uses all 10 letters of `Fin 10`. -/
theorem v10_usesAllLetters : UsesAllLetters v10 := by
  apply colour_usesAllLetters α10_pos α10_lt_one y10 y'10
  intro c
  fin_cases c
  · exact Or.inl ⟨0, by decide⟩
  · exact Or.inl ⟨1, by decide⟩
  · exact Or.inl ⟨2, by decide⟩
  · exact Or.inl ⟨3, by decide⟩
  · exact Or.inl ⟨4, by decide⟩
  · exact Or.inr ⟨0, by decide⟩
  · exact Or.inr ⟨1, by decide⟩
  · exact Or.inr ⟨2, by decide⟩
  · exact Or.inr ⟨3, by decide⟩
  · exact Or.inr ⟨4, by decide⟩

/-- Exact attainment witness: factor `8 9 3 10 4 6 5 7 8` at positions `4..12`
(`v10 4 = v10 12 = 7`) has period `8`, length `9`, exponent `9 / 8`. -/
theorem v10_attains : HasPeriod v10 4 9 8 := by
  have hb := α10_bounds
  have hfl : ∀ n m : ℕ, (m : ℝ) ≤ (n : ℝ) * α10 → (n : ℝ) * α10 < (m : ℝ) + 1 →
      ⌊(n : ℝ) * α10⌋ = (m : ℤ) := by
    intro n m h1 h2
    rw [Int.floor_eq_iff]; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hf5 : ⌊((5 : ℕ) : ℝ) * α10⌋ = 2 := hfl 5 2 (by push_cast; linarith) (by push_cast; linarith)
  have hf6 : ⌊((6 : ℕ) : ℝ) * α10⌋ = 2 := hfl 6 2 (by push_cast; linarith) (by push_cast; linarith)
  have hf13 : ⌊((13 : ℕ) : ℝ) * α10⌋ = 5 := hfl 13 5 (by push_cast; linarith) (by push_cast; linarith)
  have hf14 : ⌊((14 : ℕ) : ℝ) * α10⌋ = 5 := hfl 14 5 (by push_cast; linarith) (by push_cast; linarith)
  have hu4 : sturmian α10 4 = false := by
    unfold sturmian; change decide (⌊((6 : ℕ) : ℝ) * α10⌋ - ⌊((5 : ℕ) : ℝ) * α10⌋ = 1) = false
    rw [hf6, hf5]; decide
  have hu12 : sturmian α10 12 = false := by
    unfold sturmian; change decide (⌊((14 : ℕ) : ℝ) * α10⌋ - ⌊((13 : ℕ) : ℝ) * α10⌋ = 1) = false
    rw [hf14, hf13]; decide
  have hcf4 : countFalse (sturmian α10) 4 = 2 := by
    have hct4 := sturmian_countTrue_eq_floor α10_pos α10_lt_one 4
    have hsum4 := countTrue_add_countFalse (sturmian α10) 4
    change (countTrue (sturmian α10) 4 : ℤ) = ⌊((5 : ℕ) : ℝ) * α10⌋ at hct4
    rw [hf5] at hct4
    omega
  have hcf12 : countFalse (sturmian α10) 12 = 7 := by
    have hct12 := sturmian_countTrue_eq_floor α10_pos α10_lt_one 12
    have hsum12 := countTrue_add_countFalse (sturmian α10) 12
    change (countTrue (sturmian α10) 12 : ℤ) = ⌊((13 : ℕ) : ℝ) * α10⌋ at hct12
    rw [hf13] at hct12
    omega
  refine ⟨by omega, by omega, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [add_zero, v10, colour, hu4, hu12, hcf4, hcf12, Bool.false_eq_true, ↓reduceIte]
  decide

/-! ### Small Periods (`1 ≤ p < 16`) via Pure-Kernel Cut Partition -/

/-- Exact sorted cut partition of `[0, 1)` for `L = 17` steps of `sturmian α10`. -/
def cuts10 : List (ℕ × ℤ) :=
  [(0, 0), (7, 3), (14, 6), (2, 1), (9, 4), (16, 7), (4, 2), (11, 5), (6, 3), (13, 6),
   (1, 1), (8, 4), (15, 7), (3, 2), (10, 5), (17, 8), (5, 3), (12, 6), (0, 1)]

private theorem cuts10_ok : checkCutPartition 17 419 420 1000 cuts10 = true := by decide

private theorem small10_ok : checkSmallPeriods 16 8 5 5 y10Tab y'10Tab 17 cuts10 = true := by decide

/-- Small-period upper bound for `v10`: every period `1 ≤ p < 16` has `r * 8 ≤ p`. -/
theorem v10_small_periods {i p r : ℕ} (hp0 : 0 < p) (hp_lt : p < 16)
    (hrun : ∀ k < r, v10 (i + k) = v10 (i + k + p)) :
    r * 8 ≤ p :=
  checkSmallPeriods_sound (den := 8) (P_small := 16) (L := 17) (ma := 5) (mb := 5) (prec := 1000)
    α10_pos α10_lt_one (by omega) (by omega) (by omega) (by omega)
    (fun q _ hq => by omega) y10_disjoint_yPrime10 (fun _ => rfl) (fun _ => rfl)
    α10_bounds.1 α10_bounds.2 cuts10_ok small10_ok hp0 hp_lt hrun

/-! ### All Large Periods (`p ≥ 16`) via Periodic Continued-Fraction Level Analysis -/

/-- Partial quotients `[0; 2, 2, (1)]` of `α10`. -/
def a10 (k : ℕ) : ℕ :=
  if k = 0 then 0
  else if k = 1 then 2
  else if k = 2 then 2
  else 1

/-- Constant tail error ratio `θ10 = (-1 + √5) / 2` (`1 / φ`). -/
noncomputable def θ10 : ℝ := (-1 + Real.sqrt 5) / 2

theorem a10_ge_one (j : ℕ) (hj : 1 ≤ j) : 1 ≤ a10 j := by
  unfold a10; split_ifs <;> omega

theorem a10_tail_one (k : ℕ) (hk : 3 ≤ k) : a10 k = 1 := by
  unfold a10; split_ifs <;> omega

theorem a10_per1 (n : ℕ) : a10 (n + 4) = a10 (4 + n % 1) := by
  rw [a10_tail_one _ (by omega), a10_tail_one _ (by omega)]

theorem a10_per20 (k : ℕ) (hk : 3 ≤ k) : a10 (k + 1 + 20) = a10 (k + 1) := by
  rw [a10_tail_one _ (by omega), a10_tail_one _ (by omega)]

theorem eta10_periodic_ratio : ∀ n : ℕ, eta a10 α10 (n + 3) = θ10 * eta a10 α10 (n + 2) := by
  have h := eta_periodic_ratio (a := a10) (α := α10) (T := 1) (by omega) (fun _ => θ10)
    (by
      have hp2 : convP a10 2 = 2 := by decide
      have hq2 : convQ a10 2 = 5 := by decide
      have hp3 : convP a10 3 = 3 := by decide
      have hq3 : convQ a10 3 = 7 := by decide
      unfold eta θ10 α10
      rw [hp2, hq2, hp3, hq3]
      have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      ring_nf; rw [hsq]; ring)
    a10_per1
    (by
      intro r hr
      have hr0 : r = 0 := by omega
      subst hr0
      have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      change 1 - ((1 : ℕ) : ℝ) * ((-1 + Real.sqrt 5) / 2) =
          ((-1 + Real.sqrt 5) / 2) * ((-1 + Real.sqrt 5) / 2)
      push_cast; ring_nf; rw [hsq]; ring)
  exact h

theorem θ10_bounds : (618 : ℝ) / 1000 < θ10 ∧ θ10 < (619 : ℝ) / 1000 := by
  unfold θ10; have := sqrt5_bounds; constructor <;> linarith

/-- Exact ratio identities at `k = 1` and `k = 2`. -/
theorem eta10_k1_ratio : eta a10 α10 1 / eta a10 α10 0 = (3 - Real.sqrt 5) / 2 := by
  have hp0 : convP a10 0 = 0 := by decide
  have hq0 : convQ a10 0 = 1 := by decide
  have hp1 : convP a10 1 = 1 := by decide
  have hq1 : convQ a10 1 = 2 := by decide
  have h0pos : 0 < eta a10 α10 0 := by unfold eta; rw [hp0, hq0]; simp; exact α10_pos
  rw [div_eq_iff (ne_of_gt h0pos)]
  unfold eta α10
  rw [hp0, hq0, hp1, hq1]
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf; rw [hsq]; ring

theorem eta10_k2_ratio : eta a10 α10 2 / eta a10 α10 1 = θ10 := by
  have hp1 : convP a10 1 = 1 := by decide
  have hq1 : convQ a10 1 = 2 := by decide
  have hp2 : convP a10 2 = 2 := by decide
  have hq2 : convQ a10 2 = 5 := by decide
  have h1pos : 0 < eta a10 α10 1 := by
    unfold eta; rw [hp1, hq1]; have := α10_bounds; push_cast; norm_num; linarith
  rw [div_eq_iff (ne_of_gt h1pos)]
  unfold eta θ10 α10
  rw [hp1, hq1, hp2, hq2]
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf; rw [hsq]; ring

private theorem level10_k1_ok :
    let st := convModState a10 5 5 1
    checkLevelClass 5 5 8 (a10 2) st.1 st.2.1 st.2.2.1 st.2.2.2 381 382 1000
      (.exact (convQ a10 1) (convQPrev a10 1)) = true := by decide

private theorem level10_k2_ok :
    let st := convModState a10 5 5 2
    checkLevelClass 5 5 8 (a10 3) st.1 st.2.1 st.2.2.1 st.2.2.2 618 619 1000
      (.exact (convQ a10 2) (convQPrev a10 2)) = true := by decide

private theorem level10_mod_per20 :
    convModState a10 5 5 (3 + 20) = convModState a10 5 5 3 := by decide

private theorem level10_tail_ok :
    (List.range 20).all (fun s =>
      let st := convModState a10 5 5 (3 + s)
      checkLevelClass 5 5 8 1 st.1 st.2.1 st.2.2.1 st.2.2.2 618 619 1000 .half) = true := by
  decide

private theorem y10_match_dvd5 : ∀ s < 5, ∀ t < 5,
    y10Tab.getD s 0 = y10Tab.getD ((s + t) % 5) 0 → t = 0 := by decide

private theorem y'10_match_dvd5 : ∀ s < 5, ∀ t < 5,
    y'10Tab.getD s 0 = y'10Tab.getD ((s + t) % 5) 0 → t = 0 := by decide

/-- Large-period upper bound for `v10`: every period `p ≥ 16` has `r * 8 ≤ p`. -/
theorem v10_large_periods {i p r : ℕ} (hp16 : 16 ≤ p)
    (hrun : ∀ k < r, v10 (i + k) = v10 (i + k + p)) :
    r * 8 ≤ p := by
  have hp0 : 0 < p := by omega
  have hust : ∀ k < r, sturmian α10 (i + k) = sturmian α10 (i + k + p) :=
    fun k hk => (colour_match_implies y10_disjoint_yPrime10 (hrun k hk)).1
  obtain ⟨m, hm_half⟩ := exists_nearest_int ((p : ℝ) * α10)
  by_cases hδ_ge : α10 ≤ |(p : ℝ) * α10 - (m : ℝ)|
  · have hr_lt : r < 3 := sturmian_run_lt_of_large_dist α10_pos α10_lt_half
      (K := 3) (by push_cast; linarith [α10_bounds.1]) hδ_ge hm_half hust
    omega
  · push Not at hδ_ge
    by_contra hgt
    push Not at hgt
    have hr3 : 3 ≤ r := by omega
    have hK_true : (1 : ℝ) ≤ (3 : ℝ) * α10 := by linarith [α10_bounds.1]
    have hK_fl : ⌊(3 : ℝ) * α10⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [α10_bounds.1, α10_bounds.2]
    have hK_false : (1 : ℤ) ≤ (3 : ℤ) - ⌊(3 : ℝ) * α10⌋ - 1 := by rw [hK_fl]; omega
    obtain ⟨ka, hka, hua⟩ := exists_true_in_block α10_pos α10_lt_one hK_true hr3
    obtain ⟨kb, hkb, hub⟩ := exists_false_in_block α10_pos α10_lt_one hK_false hr3
    have hca := sturmian_match_counts_of_small_dist α10_pos α10_lt_half hδ_ge (hust ka hka)
    have hcb := sturmian_match_counts_of_small_dist α10_pos α10_lt_half hδ_ge (hust kb hkb)
    have hm0 : 0 ≤ m := hca.1
    have hm_le_p : m.toNat ≤ p := by
      have : (countFalse (sturmian α10) (i + ka) : ℤ) ≤ countFalse (sturmian α10) (i + ka + p) :=
        Int.ofNat_le.mpr (countFalse_mono _ (Nat.le_add_right _ _))
      omega
    have hma : m.toNat % 5 = 0 := by
      have hya := (colour_match_implies y10_disjoint_yPrime10 (hrun ka hka)).2.1 hua
      have hct : countTrue (sturmian α10) (i + ka + p) = countTrue (sturmian α10) (i + ka) + m.toNat := by
        omega
      rw [hct] at hya
      have hval := congrArg Fin.val hya
      simp only [y10] at hval
      have hmod : (countTrue (sturmian α10) (i + ka) + m.toNat) % 5 =
          (countTrue (sturmian α10) (i + ka) % 5 + m.toNat % 5) % 5 := Nat.add_mod _ _ _
      rw [hmod] at hval
      exact y10_match_dvd5 _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) hval
    have hmb : (p - m.toNat) % 5 = 0 := by
      have hyb := (colour_match_implies y10_disjoint_yPrime10 (hrun kb hkb)).2.2 hub
      have hcf : countFalse (sturmian α10) (i + kb + p) =
          countFalse (sturmian α10) (i + kb) + (p - m.toNat) := by omega
      rw [hcf] at hyb
      have hval := congrArg Fin.val hyb
      simp only [y'10] at hval
      have hmod : (countFalse (sturmian α10) (i + kb) + (p - m.toNat)) % 5 =
          (countFalse (sturmian α10) (i + kb) % 5 + (p - m.toNat) % 5) % 5 := Nat.add_mod _ _ _
      rw [hmod] at hval
      exact y'10_match_dvd5 _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) hval
    have hη0_eq : eta a10 α10 0 = α10 := by unfold eta; simp [convP, convQ, convPQ]
    have hη0_pos : 0 < eta a10 α10 0 := by rw [hη0_eq]; exact α10_pos
    have hη1_pos : 0 < eta a10 α10 1 := by
      have hp1 : convP a10 1 = 1 := by decide
      have hq1 : convQ a10 1 = 2 := by decide
      unfold eta; rw [hp1, hq1]; push_cast; norm_num; linarith [α10_bounds.2]
    have hη1_lt : eta a10 α10 1 < eta a10 α10 0 := by
      have hp1 : convP a10 1 = 1 := by decide
      have hq1 : convQ a10 1 = 2 := by decide
      rw [hη0_eq]; unfold eta; rw [hp1, hq1]; push_cast; norm_num; linarith [α10_bounds.1]
    have hη2_pos : 0 < eta a10 α10 2 := by
      have hp2 : convP a10 2 = 2 := by decide
      have hq2 : convQ a10 2 = 5 := by decide
      unfold eta; rw [hp2, hq2]; push_cast; norm_num; linarith [α10_bounds.1]
    have hη2_lt : eta a10 α10 2 < eta a10 α10 1 := by
      have hrat := eta10_k2_ratio
      have hlt1 : θ10 < 1 := by linarith [θ10_bounds.2]
      have : eta a10 α10 2 = θ10 * eta a10 α10 1 := by
        rw [← hrat, div_mul_cancel₀ _ (ne_of_gt hη1_pos)]
      nlinarith
    obtain ⟨hη_pos, hη_dec, hlevel⟩ := eta_level_exists (T := 1) (θ := fun _ => θ10) (M := 7 / 10)
      (by omega) hη0_pos hη1_pos hη1_lt hη2_pos hη2_lt eta10_periodic_ratio
      (fun _ _ => by linarith [θ10_bounds.1]) (fun _ _ => by linarith [θ10_bounds.2]) (by norm_num)
    have hδ0 : 0 < |(p : ℝ) * α10 - (m : ℝ)| := by
      rw [abs_pos]
      exact sub_ne_zero.mpr (α10_irrational (u := (p : ℤ)) (v := m) (by omega))
    obtain ⟨k, hk1, hδ_lo, hδ_hi⟩ := hlevel |(p : ℝ) * α10 - (m : ℝ)| hδ0 (by rw [hη0_eq]; exact hδ_ge)
    have hle_p : r * 8 ≤ p := by
      by_cases hk_1 : k = 1
      · subst hk_1
        have hs := sqrt5_bounds
        have hlo1 : ((381 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) < eta a10 α10 1 / eta a10 α10 0 := by
          rw [eta10_k1_ratio]; push_cast; linarith
        have hhi1 : eta a10 α10 1 / eta a10 α10 0 < ((382 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by
          rw [eta10_k1_ratio]; push_cast; linarith
        exact checkLevelClass_sound (den := 8) (loN := 381) (hiN := 382) (prec := 1000)
          (mode := .exact (convQ a10 1) (convQPrev a10 1))
          α10_pos α10_lt_half (fun _ _ hu => α10_irrational hu) a10_ge_one
          (le_refl 1) (by omega) (by omega) rfl rfl (hη_pos 1) (hη_pos 0) (hη_pos 2)
          (hη_dec 0) (hη_dec 1) hlo1 hhi1 ⟨rfl, rfl⟩ level10_k1_ok hp0 hm0 hδ_lo hδ_hi hδ_ge hma hmb hust
      · by_cases hk_2 : k = 2
        · subst hk_2
          exact checkLevelClass_sound (den := 8) (loN := 618) (hiN := 619) (prec := 1000)
            (mode := .exact (convQ a10 2) (convQPrev a10 2))
            α10_pos α10_lt_half (fun _ _ hu => α10_irrational hu) a10_ge_one
            (by omega) (by omega) (by omega) rfl rfl (hη_pos 2) (hη_pos 1) (hη_pos 3)
            (hη_dec 1) (hη_dec 2) (by rw [eta10_k2_ratio]; exact_mod_cast θ10_bounds.1)
            (by rw [eta10_k2_ratio]; exact_mod_cast θ10_bounds.2)
            ⟨rfl, rfl⟩ level10_k2_ok hp0 hm0 hδ_lo hδ_hi hδ_ge hma hmb hust
        · have hk3 : 3 ≤ k := by omega
          let s := (k - 3) % 20
          have hs_lt : s < 20 := Nat.mod_lt _ (by omega)
          have hmod_eq : convModState a10 5 5 k = convModState a10 5 5 (3 + s) :=
            convModState_periodic (by decide) 5 5 20 (by omega) a10_per20 level10_mod_per20 k hk3
          have hak1_eq : a10 (k + 1) = 1 := a10_tail_one (k + 1) (by omega)
          have hrat_eq : eta a10 α10 k / eta a10 α10 (k - 1) = θ10 := by
            set t := k - 3
            have h1 : k = t + 3 := by omega
            have h2 : k - 1 = t + 2 := by omega
            rw [h2, h1, eta10_periodic_ratio t, mul_div_cancel_right₀ _ (ne_of_gt (hη_pos _))]
          have hchk_s := (List.all_eq_true.mp level10_tail_ok) s (List.mem_range.mpr hs_lt)
          have hmode_half : LevelBoundMode.Holds .half (convQ a10 k) (convQPrev a10 k) :=
            ⟨(convQPrev_bounds a10_ge_one hk1).2, convQ_le_two_prev_of_tail_one a10_ge_one a10_tail_one hk3⟩
          have hdec_k : eta a10 α10 k < eta a10 α10 (k - 1) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega]
            exact hη_dec (k - 1)
          exact checkLevelClass_sound (den := 8) (loN := 618) (hiN := 619) (prec := 1000) (mode := .half)
            α10_pos α10_lt_half (fun _ _ hu => α10_irrational hu) a10_ge_one
            hk1 (by omega) (by omega) hak1_eq hmod_eq (hη_pos k) (hη_pos (k - 1)) (hη_pos (k + 1))
            hdec_k (hη_dec k) (by rw [hrat_eq]; exact_mod_cast θ10_bounds.1)
            (by rw [hrat_eq]; exact_mod_cast θ10_bounds.2)
            hmode_half hchk_s hp0 hm0 hδ_lo hδ_hi hδ_ge hma hmb hust
    omega

/-- All-periods run bound for `v10`: every match run satisfies `r * 8 ≤ p`. -/
theorem v10_run_bound (i p r : ℕ) (hp : 0 < p)
    (hrun : ∀ k < r, v10 (i + k) = v10 (i + k + p)) :
    r * 8 ≤ p := by
  by_cases hlt : p < 16
  · exact v10_small_periods hp hlt hrun
  · exact v10_large_periods (by omega) hrun

/-- Critical exponent upper bound `critExp v10 ≤ 9 / 8`. -/
theorem v10_critExp_le : critExp v10 ≤ (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) :=
  critExp_le_of_run_bound (num := 9) (den := 8) (by omega) (by omega)
    (fun i p r hp hrun => by simpa using v10_run_bound i p r hp hrun)

/-- Exact attained critical exponent of `v10`: `critExp v10 = 9 / 8` (achieved as a maximum). -/
theorem v10_critExp_eq :
    critExp v10 = (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ∧
    (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v10 :=
  attains_critExp_of_period (num := 9) (den := 8) (by omega) v10_critExp_le v10_attains (by omega)

end BalancedRepetitionThreshold
