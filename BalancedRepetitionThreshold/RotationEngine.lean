module

public import BalancedRepetitionThreshold.Sturmian
public import Mathlib.NumberTheory.Real.Irrational

import Mathlib.Tactic

/-!
# Unified Circle-Rotation, Three-Gap, Continued-Fraction, and Small-Period Engine

This module provides the completely general, 100% pure-kernel machinery used to prove exact
all-periods critical exponent upper bounds `critExp (colour (sturmian α) y y') ≤ (den + 1) / den`
for all three witnesses `v7`, `v9`, and `v10`:

1. **Circle rotation & large-distance bound (`sturmian_run_lt_of_large_dist`)**:
   when `α ≤ |p α - m| ≤ 1 / 2` (with `0 < α < 1 / 2`), no `true` letter matches at distance `p`,
   so every match run has length `< K` whenever `1 ≤ K α`.
2. **Exact match-window counts (`sturmian_match_counts_of_small_dist`)**:
   when `|p α - m| < α`, every matching position `n` has exactly `m` `true` letters and `p - m`
   `false` letters in `[n, n + p)`.
3. **Unconditional three-gap return-time bound (`sturmian_three_gap_run_bound`)**:
   using the two-sided orbit `t ↦ Int.fract (t α)` on `ℤ` (requiring zero uniform recurrence or
   Kronecker density), any positive/negative semiconvergent pair `(a, b)` with errors `0 < e₁, e₂ < δ`
   bounds every match run by `r + 2 ≤ a + b`.
4. **Periodic continued-fraction convergent & level engine**:
   exact determinant identity, exact periodic error ratios `η (n + 3) = θ (n % T) * η (n + 2)`,
   level existence `η k ≤ δ < η (k - 1)`, basis decomposition `(p, m) = c (q_k, p_k) + d (q_{k-1}, p_{k-1})`,
   modular state periodicity, and a pure-kernel rational-enclosure level checker `checkLevelClass`.
5. **Pure-kernel cut-partition & small-period checker (`checkCutPartition`, `checkSmallPeriods`)**:
   certifies all `L + 1` factors of `sturmian α` of length `L` from a rational bracket of `α`
   and checks all periods `1 ≤ p < P_small` across all colour phases in the Lean 4 kernel.
-/

@[expose] public section

namespace BalancedRepetitionThreshold

/-! ## Section 1: Circle Rotation, Match Counts, and Three-Gap Return-Time Bound -/

/-- Helper characterizing `Int.fract x = y` from `x = k + y` with `y ∈ [0, 1)`. -/
theorem fract_eq_of_int_add {x y : ℝ} (k : ℤ) (h : x = (k : ℝ) + y) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Int.fract x = y := by
  rw [Int.fract_eq_iff]
  exact ⟨hy0, hy1, k, by linarith⟩

/-- Every real number `x` has a nearest integer `m` with `|x - m| ≤ 1 / 2`. -/
theorem exists_nearest_int (x : ℝ) : ∃ m : ℤ, |x - (m : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : (⌊x + 1 / 2⌋ : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < (⌊x + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- For `0 < α < 1/2`, if `α ≤ |p α - m| ≤ 1/2`, no `true` letter in `sturmian α` matches at
distance `p`. -/
theorem sturmian_no_true_match_of_large_dist {α : ℝ} (hα0 : 0 < α) (hα2 : α < 1 / 2)
    {p : ℕ} {m : ℤ} (hlo : α ≤ |(p : ℝ) * α - (m : ℝ)|)
    (hhi : |(p : ℝ) * α - (m : ℝ)| ≤ 1 / 2) (n : ℕ) :
    ¬ (sturmian α n = true ∧ sturmian α (n + p) = true) := by
  have hα1 : α < 1 := by linarith
  rintro ⟨h1, h2⟩
  rw [sturmian_iff_fract hα1] at h1 h2
  set x := Int.fract (((n + 1 : ℕ) : ℝ) * α)
  set K : ℤ := ⌊((n + 1 : ℕ) : ℝ) * α⌋
  set ε : ℝ := (p : ℝ) * α - (m : ℝ)
  have hx0 : 0 ≤ x := Int.fract_nonneg _
  have hx1 : x < 1 := Int.fract_lt_one _
  have hdecom : ((n + p + 1 : ℕ) : ℝ) * α = ((K + m : ℤ) : ℝ) + (x + ε) := by
    have hfl : ((n + 1 : ℕ) : ℝ) * α = (K : ℝ) + x := (Int.floor_add_fract _).symm
    have hcast : ((n + p + 1 : ℕ) : ℝ) * α = ((n + 1 : ℕ) : ℝ) * α + (p : ℝ) * α := by
      push_cast; ring
    rw [hcast, hfl]
    push_cast
    dsimp only [ε]
    ring
  by_cases hε : 0 ≤ ε
  · have hε_lo : α ≤ ε := by rwa [abs_of_nonneg hε] at hlo
    have hε_hi : ε ≤ 1 / 2 := by rwa [abs_of_nonneg hε] at hhi
    have hfx : Int.fract (((n + p + 1 : ℕ) : ℝ) * α) = x + ε - 1 := by
      apply fract_eq_of_int_add (K + m + 1)
      · rw [hdecom]; push_cast; ring
      · linarith
      · linarith
    rw [hfx] at h2
    linarith
  · push Not at hε
    have hε_lo : α ≤ -ε := by rwa [abs_of_neg hε] at hlo
    have hε_hi : -ε ≤ 1 / 2 := by rwa [abs_of_neg hε] at hhi
    have hfx : Int.fract (((n + p + 1 : ℕ) : ℝ) * α) = x + ε := by
      apply fract_eq_of_int_add (K + m) hdecom
      · linarith
      · linarith
    rw [hfx] at h2
    linarith

/-- Any block of length `K` with `1 ≤ K α` contains a `true` letter of `sturmian α`. -/
theorem exists_true_in_block {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {K i r : ℕ}
    (hK : 1 ≤ (K : ℝ) * α) (hKr : K ≤ r) :
    ∃ k < r, sturmian α (i + k) = true := by
  have hfl : (1 : ℤ) ≤ ⌊(K : ℝ) * α⌋ := Int.le_floor.mpr (by exact_mod_cast hK)
  have hb := (sturmian_interval_countTrue_bounds hα0 hα1 i K).1
  have hpos : 0 < ((Finset.range K).filter (fun j => sturmian α (i + j) = true)).card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_range] at hk
  exact ⟨k, lt_of_lt_of_le hk.1 hKr, hk.2⟩

/-- Any block of length `K` with `1 ≤ K - ⌊K α⌋ - 1` contains a `false` letter of `sturmian α`. -/
theorem exists_false_in_block {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {K i r : ℕ}
    (hK : 1 ≤ (K : ℤ) - ⌊(K : ℝ) * α⌋ - 1) (hKr : K ≤ r) :
    ∃ k < r, sturmian α (i + k) = false := by
  have hb := (sturmian_interval_countFalse_bounds hα0 hα1 i K).1
  have hpos : 0 < ((Finset.range K).filter (fun j => sturmian α (i + j) = false)).card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_range] at hk
  exact ⟨k, lt_of_lt_of_le hk.1 hKr, hk.2⟩

/-- Any block of length `K` with `2 ≤ K - ⌊K α⌋ - 1` contains two `false` letters whose
`countFalse` indices are consecutive (`s` and `s + 1`). -/
theorem exists_two_consec_false_in_block {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {K i r : ℕ}
    (hK : 2 ≤ (K : ℤ) - ⌊(K : ℝ) * α⌋ - 1) (hKr : K ≤ r) :
    ∃ k₁ < r, ∃ k₂ < r,
      sturmian α (i + k₁) = false ∧
      sturmian α (i + k₂) = false ∧
      countFalse (sturmian α) (i + k₂) = countFalse (sturmian α) (i + k₁) + 1 := by
  have hb := (sturmian_interval_countFalse_bounds hα0 hα1 i K).1
  have hint := countFalse_interval (sturmian α) i K
  set s := countFalse (sturmian α) i
  have hge2 : s + 2 ≤ countFalse (sturmian α) (i + K) := by omega
  -- Helper: for any target t with s ≤ t < countFalse u (i + K), find k < K with u (i + k) = false
  -- and countFalse u (i + k) = t.
  have hfind : ∀ t : ℕ, s ≤ t → t < countFalse (sturmian α) (i + K) →
      ∃ k < K, sturmian α (i + k) = false ∧ countFalse (sturmian α) (i + k) = t := by
    intro t ht1 ht2
    classical
    have hex : ∃ m : ℕ, t < countFalse (sturmian α) (i + m) := ⟨K, ht2⟩
    let m := Nat.find hex
    have hm_spec : t < countFalse (sturmian α) (i + m) := Nat.find_spec hex
    have hm_le : m ≤ K := Nat.find_min' hex ht2
    have hm_pos : 0 < m := by
      by_contra h0
      have hm0 : m = 0 := by omega
      rw [hm0, add_zero] at hm_spec
      omega
    let k := m - 1
    have hk_lt : k < m := by omega
    have hk_le : countFalse (sturmian α) (i + k) ≤ t := by
      have := Nat.find_min hex hk_lt
      omega
    have hstep : countFalse (sturmian α) (i + m) = countFalse (sturmian α) (i + k) +
        (if sturmian α (i + k) = false then 1 else 0) := by
      have heq : i + m = i + k + 1 := by omega
      rw [heq, countFalse_succ]
    refine ⟨k, by omega, ?_, ?_⟩
    · by_contra hne
      simp [hne] at hstep
      omega
    · by_cases hf : sturmian α (i + k) = false
      · simp [hf] at hstep; omega
      · simp [hf] at hstep; omega
  obtain ⟨k₁, hk1, hf1, hc1⟩ := hfind s (le_refl s) (by omega)
  obtain ⟨k₂, hk2, hf2, hc2⟩ := hfind (s + 1) (by omega) (by omega)
  exact ⟨k₁, lt_of_lt_of_le hk1 hKr, k₂, lt_of_lt_of_le hk2 hKr, hf1, hf2, by omega⟩

/-- When `α ≤ |p α - m| ≤ 1/2` and `1 ≤ K α`, every match run of `sturmian α` at period `p` has
length strictly less than `K`. -/
theorem sturmian_run_lt_of_large_dist {α : ℝ} (hα0 : 0 < α) (hα2 : α < 1 / 2)
    {p K i r : ℕ} {m : ℤ} (hK : 1 ≤ (K : ℝ) * α)
    (hlo : α ≤ |(p : ℝ) * α - (m : ℝ)|) (hhi : |(p : ℝ) * α - (m : ℝ)| ≤ 1 / 2)
    (hrun : ∀ k < r, sturmian α (i + k) = sturmian α (i + k + p)) :
    r < K := by
  by_contra hge
  push Not at hge
  obtain ⟨k, hkr, ht⟩ := exists_true_in_block hα0 (by linarith) hK hge
  have ht' : sturmian α (i + k + p) = true := by rw [← hrun k hkr, ht]
  exact sturmian_no_true_match_of_large_dist hα0 hα2 hlo hhi (i + k) ⟨ht, ht'⟩

/-- When `|p α - m| < α` (with `0 < α < 1/2`), every matching position `n` of `sturmian α` at
period `p` has exactly `m` `true` letters and `p - m` `false` letters in `[n, n + p)`. -/
theorem sturmian_match_counts_of_small_dist {α : ℝ} (hα0 : 0 < α) (hα2 : α < 1 / 2)
    {p : ℕ} {m : ℤ} (hδα : |(p : ℝ) * α - (m : ℝ)| < α)
    {n : ℕ} (hmatch : sturmian α n = sturmian α (n + p)) :
    0 ≤ m ∧
    (countTrue (sturmian α) (n + p) : ℤ) - (countTrue (sturmian α) n : ℤ) = m ∧
    (countFalse (sturmian α) (n + p) : ℤ) - (countFalse (sturmian α) n : ℤ) = (p : ℤ) - m := by
  have hα1 : α < 1 := by linarith
  set x := Int.fract (((n + 1 : ℕ) : ℝ) * α)
  set K : ℤ := ⌊((n + 1 : ℕ) : ℝ) * α⌋
  set ε : ℝ := (p : ℝ) * α - (m : ℝ)
  have hx0 : 0 ≤ x := Int.fract_nonneg _
  have hx1 : x < 1 := Int.fract_lt_one _
  have hfl_n := sturmian_countTrue_eq_floor hα0 hα1 n
  have hfl_np := sturmian_countTrue_eq_floor hα0 hα1 (n + p)
  have hdecom : ((n + p + 1 : ℕ) : ℝ) * α = ((K + m : ℤ) : ℝ) + (x + ε) := by
    have hfl : ((n + 1 : ℕ) : ℝ) * α = (K : ℝ) + x := (Int.floor_add_fract _).symm
    have hcast : ((n + p + 1 : ℕ) : ℝ) * α = ((n + 1 : ℕ) : ℝ) * α + (p : ℝ) * α := by
      push_cast; ring
    rw [hcast, hfl]
    push_cast
    dsimp only [ε]
    ring
  have hfl_diff : ⌊((n + p + 1 : ℕ) : ℝ) * α⌋ - K = m + ⌊x + ε⌋ := by
    have h1 : ⌊((n + p + 1 : ℕ) : ℝ) * α⌋ = (K + m) + ⌊x + ε⌋ := by
      rw [hdecom]
      exact Int.floor_intCast_add (K + m) (x + ε)
    omega
  have hxe0 : ⌊x + ε⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    by_cases hε : 0 ≤ ε
    · have hε_lt : ε < α := by rwa [abs_of_nonneg hε] at hδα
      refine ⟨by linarith, ?_⟩
      by_contra hge
      push Not at hge
      have ht1 : sturmian α n = true := (sturmian_iff_fract hα1 n).mpr (by linarith)
      have hfx : Int.fract (((n + p + 1 : ℕ) : ℝ) * α) = x + ε - 1 := by
        apply fract_eq_of_int_add (K + m + 1)
        · rw [hdecom]; push_cast; ring
        · linarith
        · linarith
      have ht2 : sturmian α (n + p) = true := by rw [← hmatch, ht1]
      have h2 := (sturmian_iff_fract hα1 (n + p)).mp ht2
      rw [hfx] at h2
      linarith
    · push Not at hε
      have hε_lt : -ε < α := by rwa [abs_of_neg hε] at hδα
      refine ⟨?_, by linarith⟩
      by_contra hlt
      push Not at hlt
      have hf1 : sturmian α n ≠ true := by
        intro ht1
        have h1 := (sturmian_iff_fract hα1 n).mp ht1
        linarith
      have hfx : Int.fract (((n + p + 1 : ℕ) : ℝ) * α) = x + ε + 1 := by
        apply fract_eq_of_int_add (K + m - 1)
        · rw [hdecom]; push_cast; ring
        · linarith
        · linarith
      have ht2 : sturmian α (n + p) = true := (sturmian_iff_fract hα1 (n + p)).mpr (by rw [hfx]; linarith)
      rw [← hmatch] at ht2
      exact hf1 ht2
  have hct : (countTrue (sturmian α) (n + p) : ℤ) - (countTrue (sturmian α) n : ℤ) = m := by
    rw [hfl_np, hfl_n]
    change ⌊((n + p + 1 : ℕ) : ℝ) * α⌋ - K = m
    omega
  have hmono : countTrue (sturmian α) n ≤ countTrue (sturmian α) (n + p) :=
    countTrue_mono _ (Nat.le_add_right n p)
  have hsum1 := countTrue_add_countFalse (sturmian α) n
  have hsum2 := countTrue_add_countFalse (sturmian α) (n + p)
  exact ⟨by omega, hct, by omega⟩

/-- **Unconditional Three-Gap Return-Time Bound** (zero uniform recurrence or Kronecker needed):
if `0 < α < 1/2`, `0 < δ < α` where `δ = |p α - m|`, and `a, b ≥ 1` satisfy
`0 < a α - pa < δ` and `0 < pb - b α < δ`, then every non-empty match run of `sturmian α` of
length `r ≥ 1` at period `p` satisfies `r + 2 ≤ a + b`. -/
theorem sturmian_three_gap_run_bound {α : ℝ} (_hα0 : 0 < α) (hα2 : α < 1 / 2)
    {p i r a b : ℕ} {m pa pb : ℤ}
    (hr : 1 ≤ r)
    (hδ0 : 0 < |(p : ℝ) * α - (m : ℝ)|)
    (hδα : |(p : ℝ) * α - (m : ℝ)| < α)
    (ha : 0 < a) (hb : 0 < b)
    (he1 : 0 < (a : ℝ) * α - (pa : ℝ) ∧ (a : ℝ) * α - (pa : ℝ) < |(p : ℝ) * α - (m : ℝ)|)
    (he2 : 0 < (pb : ℝ) - (b : ℝ) * α ∧ (pb : ℝ) - (b : ℝ) * α < |(p : ℝ) * α - (m : ℝ)|)
    (hrun : ∀ k < r, sturmian α (i + k) = sturmian α (i + k + p)) :
    r + 2 ≤ a + b := by
  have hα1 : α < 1 := by linarith
  set ε : ℝ := (p : ℝ) * α - (m : ℝ)
  set δ : ℝ := |ε|
  set e₁ : ℝ := (a : ℝ) * α - (pa : ℝ)
  set e₂ : ℝ := (pb : ℝ) - (b : ℝ) * α
  let z : ℤ → ℝ := fun t => Int.fract ((t : ℝ) * α)
  let c : ℝ := if 0 < ε then 1 - α - δ else 1 - α
  have hc0 : 0 ≤ c := by
    dsimp only [c]; split_ifs <;> linarith
  have hc1 : c + δ ≤ 1 := by
    dsimp only [c]; split_ifs <;> linarith
  -- Step 1: No t ∈ [i, i + r] lands in J = [c, c + δ).
  have hmiss : ∀ t : ℤ, (i : ℤ) ≤ t → t ≤ (i + r : ℤ) → ¬ (c ≤ z t ∧ z t < c + δ) := by
    intro t ht1 ht2 ⟨hlo, hhi⟩
    by_cases hti : t = (i : ℤ)
    · -- t = i: then x_i = z (i + 1) lands in the shifted mismatch interval, contradicting match at k = 0.
      subst hti
      have hmatch0 : sturmian α i = sturmian α (i + p) := by
        simpa using hrun 0 (by omega)
      set Ki : ℤ := ⌊((i : ℤ) : ℝ) * α⌋
      have hzi_decom : ((i : ℤ) : ℝ) * α = (Ki : ℝ) + z (i : ℤ) := (Int.floor_add_fract _).symm
      by_cases hε : 0 < ε
      · have hδeq : δ = ε := abs_of_pos hε
        have hceq : c = 1 - α - δ := by simp only [c, hε, ↓reduceIte]
        rw [hceq] at hlo hhi
        -- x_i = z i + α ∈ [1 - δ, 1)
        have hxi : Int.fract (((i + 1 : ℕ) : ℝ) * α) = z (i : ℤ) + α := by
          apply fract_eq_of_int_add Ki
          · have h1 : ((i + 1 : ℕ) : ℝ) * α = ((i : ℤ) : ℝ) * α + α := by push_cast; ring
            rw [h1, hzi_decom]; ring
          · linarith
          · linarith
        have ht1 : sturmian α i = true := (sturmian_iff_fract hα1 i).mpr (by rw [hxi]; linarith)
        have hxip : Int.fract (((i + p + 1 : ℕ) : ℝ) * α) = z (i : ℤ) + α + ε - 1 := by
          apply fract_eq_of_int_add (Ki + m + 1)
          · have h1 : ((i + p + 1 : ℕ) : ℝ) * α = ((i : ℤ) : ℝ) * α + α + (p : ℝ) * α := by
              push_cast; ring
            rw [h1, hzi_decom]; push_cast; dsimp only [ε]; ring
          · linarith
          · linarith
        have ht2 : sturmian α (i + p) = true := by rw [← hmatch0, ht1]
        have h2 := (sturmian_iff_fract hα1 (i + p)).mp ht2
        rw [hxip] at h2
        linarith
      · have hε_neg : ε < 0 := by
          have hne : ε ≠ 0 := fun h0 => by simp [δ, h0] at hδ0
          exact lt_of_le_of_ne (not_lt.mp hε) hne
        have hδeq : δ = -ε := abs_of_neg hε_neg
        have hceq : c = 1 - α := by simp only [c, hε, ↓reduceIte]
        rw [hceq] at hlo hhi
        -- x_i = z i + α - 1 ∈ [0, δ)
        have hxi : Int.fract (((i + 1 : ℕ) : ℝ) * α) = z (i : ℤ) + α - 1 := by
          apply fract_eq_of_int_add (Ki + 1)
          · have h1 : ((i + 1 : ℕ) : ℝ) * α = ((i : ℤ) : ℝ) * α + α := by push_cast; ring
            rw [h1, hzi_decom]; push_cast; ring
          · linarith
          · linarith
        have hf1 : sturmian α i ≠ true := by
          intro ht1
          have h1 := (sturmian_iff_fract hα1 i).mp ht1
          rw [hxi] at h1; linarith
        have hxip : Int.fract (((i + p + 1 : ℕ) : ℝ) * α) = z (i : ℤ) + α + ε := by
          apply fract_eq_of_int_add (Ki + m)
          · have h1 : ((i + p + 1 : ℕ) : ℝ) * α = ((i : ℤ) : ℝ) * α + α + (p : ℝ) * α := by
              push_cast; ring
            rw [h1, hzi_decom]; push_cast; dsimp only [ε]; ring
          · linarith
          · linarith
        have ht2 : sturmian α (i + p) = true :=
          (sturmian_iff_fract hα1 (i + p)).mpr (by rw [hxip]; linarith)
        rw [← hmatch0] at ht2
        exact hf1 ht2
    · -- t = i + k + 1 with k < r: z t = x_{i+k} lands directly in J, contradicting match at k.
      let k : ℕ := (t - (i : ℤ) - 1).toNat
      have hk_lt : k < r := by omega
      have ht_eq : t = ((i + k + 1 : ℕ) : ℤ) := by omega
      have hmatchk := hrun k hk_lt
      have hzt_eq : z t = Int.fract (((i + k + 1 : ℕ) : ℝ) * α) := by
        dsimp only [z]; rw [ht_eq]; push_cast; rfl
      rw [hzt_eq] at hlo hhi
      set Kk : ℤ := ⌊((i + k + 1 : ℕ) : ℝ) * α⌋
      set xk := Int.fract (((i + k + 1 : ℕ) : ℝ) * α)
      have hxk_decom : ((i + k + 1 : ℕ) : ℝ) * α = (Kk : ℝ) + xk := (Int.floor_add_fract _).symm
      by_cases hε : 0 < ε
      · have hδeq : δ = ε := abs_of_pos hε
        have hceq : c = 1 - α - δ := by simp only [c, hε, ↓reduceIte]
        rw [hceq] at hlo hhi
        have hf1 : sturmian α (i + k) ≠ true := by
          intro ht1
          have h1 := (sturmian_iff_fract hα1 (i + k)).mp ht1
          linarith
        have hxkp : Int.fract (((i + k + p + 1 : ℕ) : ℝ) * α) = xk + ε := by
          apply fract_eq_of_int_add (Kk + m)
          · have h1 : ((i + k + p + 1 : ℕ) : ℝ) * α = ((i + k + 1 : ℕ) : ℝ) * α + (p : ℝ) * α := by
              push_cast; ring
            rw [h1, hxk_decom]; push_cast; dsimp only [ε]; ring
          · linarith
          · linarith
        have ht2 : sturmian α (i + k + p) = true :=
          (sturmian_iff_fract hα1 (i + k + p)).mpr (by rw [hxkp]; linarith)
        rw [← hmatchk] at ht2
        exact hf1 ht2
      · have hε_neg : ε < 0 := by
          have hne : ε ≠ 0 := fun h0 => by simp [δ, h0] at hδ0
          exact lt_of_le_of_ne (not_lt.mp hε) hne
        have hδeq : δ = -ε := abs_of_neg hε_neg
        have hceq : c = 1 - α := by simp only [c, hε, ↓reduceIte]
        rw [hceq] at hlo hhi
        have ht1 : sturmian α (i + k) = true :=
          (sturmian_iff_fract hα1 (i + k)).mpr (by linarith)
        have hxkp : Int.fract (((i + k + p + 1 : ℕ) : ℝ) * α) = xk + ε := by
          apply fract_eq_of_int_add (Kk + m)
          · have h1 : ((i + k + p + 1 : ℕ) : ℝ) * α = ((i + k + 1 : ℕ) : ℝ) * α + (p : ℝ) * α := by
              push_cast; ring
            rw [h1, hxk_decom]; push_cast; dsimp only [ε]; ring
          · linarith
          · linarith
        have ht2 : sturmian α (i + k + p) = true := by rw [← hmatchk, ht1]
        have h2 := (sturmian_iff_fract hα1 (i + k + p)).mp ht2
        rw [hxkp] at h2
        linarith
  -- Step 2: Explicit backward hit t₀ ≤ i with z t₀ ∈ [c, c + δ) using step -a (shift -e₁).
  have hhit_back : ∃ t₀ : ℤ, t₀ ≤ (i : ℤ) ∧ c ≤ z t₀ ∧ z t₀ < c + δ := by
    set zi := z (i : ℤ)
    have hzi0 : 0 ≤ zi := Int.fract_nonneg _
    have hzi1 : zi < 1 := Int.fract_lt_one _
    set d₀ : ℝ := if c ≤ zi then zi - c else zi + 1 - c
    have hd0_nonneg : 0 ≤ d₀ := by dsimp only [d₀]; split_ifs <;> linarith
    have hfl_nonneg : 0 ≤ ⌊d₀ / e₁⌋ := Int.floor_nonneg.mpr (div_nonneg hd0_nonneg (le_of_lt he1.1))
    let K : ℕ := ⌊d₀ / e₁⌋.toNat
    have hK_cast : (K : ℝ) = (⌊d₀ / e₁⌋ : ℝ) := by
      have : (K : ℤ) = ⌊d₀ / e₁⌋ := Int.toNat_of_nonneg hfl_nonneg
      exact_mod_cast this
    have hK_lo : (K : ℝ) * e₁ ≤ d₀ := by
      rw [hK_cast]
      exact (le_div_iff₀ he1.1).mp (Int.floor_le (d₀ / e₁))
    have hK_hi : d₀ < ((K : ℝ) + 1) * e₁ := by
      rw [hK_cast]
      exact (div_lt_iff₀ he1.1).mp (Int.lt_floor_add_one (d₀ / e₁))
    let t₀ : ℤ := (i : ℤ) - (K : ℤ) * (a : ℤ)
    have ht0_le : t₀ ≤ (i : ℤ) := by
      have : (0 : ℤ) ≤ (K : ℤ) * (a : ℤ) := by positivity
      omega
    have hzt0 : z t₀ = c + (d₀ - (K : ℝ) * e₁) := by
      set Ki : ℤ := ⌊((i : ℤ) : ℝ) * α⌋
      have hzi_decom : ((i : ℤ) : ℝ) * α = (Ki : ℝ) + zi := (Int.floor_add_fract _).symm
      by_cases hcz : c ≤ zi
      · have hd0_eq : d₀ = zi - c := by simp only [d₀, hcz, ↓reduceIte]
        apply fract_eq_of_int_add (Ki - (K : ℤ) * pa)
        · have h1 : (t₀ : ℝ) * α = ((i : ℤ) : ℝ) * α - (K : ℝ) * ((a : ℝ) * α) := by
            dsimp only [t₀]; push_cast; ring
          rw [h1, hzi_decom, hd0_eq]; push_cast; dsimp only [e₁]; ring
        · linarith
        · linarith [he1.2]
      · have hd0_eq : d₀ = zi + 1 - c := by simp only [d₀, hcz, ↓reduceIte]
        apply fract_eq_of_int_add (Ki - (K : ℤ) * pa - 1)
        · have h1 : (t₀ : ℝ) * α = ((i : ℤ) : ℝ) * α - (K : ℝ) * ((a : ℝ) * α) := by
            dsimp only [t₀]; push_cast; ring
          rw [h1, hzi_decom, hd0_eq]; push_cast; dsimp only [e₁]; ring
        · linarith
        · linarith [he1.2]
    exact ⟨t₀, ht0_le, by rw [hzt0]; linarith, by rw [hzt0]; linarith [he1.2]⟩
  -- Step 3: Maximize t_prev ∈ [t₀, i] with z t_prev ∈ [c, c + δ).
  obtain ⟨t₀, ht0_le, ht0_lo, ht0_hi⟩ := hhit_back
  classical
  let S : Finset ℤ := (Finset.Icc t₀ (i : ℤ)).filter (fun t => c ≤ z t ∧ z t < c + δ)
  have hS_ne : S.Nonempty := ⟨t₀, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl t₀, ht0_le⟩, ht0_lo, ht0_hi⟩⟩
  let tp : ℤ := S.max' hS_ne
  have htp_mem : tp ∈ S := Finset.max'_mem S hS_ne
  have htp_le_i : tp ≤ (i : ℤ) := (Finset.mem_Icc.mp (Finset.mem_filter.mp htp_mem).1).2
  have htp_lo : c ≤ z tp := (Finset.mem_filter.mp htp_mem).2.1
  have htp_hi : z tp < c + δ := (Finset.mem_filter.mp htp_mem).2.2
  have htp_lt_i : tp < (i : ℤ) := by
    by_contra hge
    have heq : tp = (i : ℤ) := by omega
    rw [heq] at htp_lo htp_hi
    exact hmiss (i : ℤ) (le_refl _) (by omega) ⟨htp_lo, htp_hi⟩
  -- Step 4: Three-gap forward return step from tp: ∃ s ≤ a + b, 0 < s ∧ z (tp + s) ∈ [c, c + δ).
  have hstep : ∃ s : ℕ, 0 < s ∧ s ≤ a + b ∧ c ≤ z (tp + (s : ℤ)) ∧ z (tp + (s : ℤ)) < c + δ := by
    set y := z tp
    set Kp : ℤ := ⌊(tp : ℝ) * α⌋
    have hyp_decom : (tp : ℝ) * α = (Kp : ℝ) + y := (Int.floor_add_fract _).symm
    by_cases h1 : y < c + δ - e₁
    · refine ⟨a, ha, by omega, ?_, ?_⟩
      · have hza : z (tp + (a : ℤ)) = y + e₁ := by
          apply fract_eq_of_int_add (Kp + pa)
          · have hcast : ((tp + (a : ℤ) : ℤ) : ℝ) * α = (tp : ℝ) * α + (a : ℝ) * α := by
              push_cast; ring
            rw [hcast, hyp_decom]; push_cast; dsimp only [e₁]; ring
          · linarith [he1.1]
          · linarith
        rw [hza]; linarith [he1.1]
      · have hza : z (tp + (a : ℤ)) = y + e₁ := by
          apply fract_eq_of_int_add (Kp + pa)
          · have hcast : ((tp + (a : ℤ) : ℤ) : ℝ) * α = (tp : ℝ) * α + (a : ℝ) * α := by
              push_cast; ring
            rw [hcast, hyp_decom]; push_cast; dsimp only [e₁]; ring
          · linarith [he1.1]
          · linarith
        rw [hza]; linarith
    · by_cases h2 : c + e₂ ≤ y
      · refine ⟨b, hb, by omega, ?_, ?_⟩
        · have hzb : z (tp + (b : ℤ)) = y - e₂ := by
            apply fract_eq_of_int_add (Kp + pb)
            · have hcast : ((tp + (b : ℤ) : ℤ) : ℝ) * α = (tp : ℝ) * α + (b : ℝ) * α := by
                push_cast; ring
              rw [hcast, hyp_decom]; push_cast; dsimp only [e₂]; ring
            · linarith
            · linarith [he2.1]
          rw [hzb]; linarith
        · have hzb : z (tp + (b : ℤ)) = y - e₂ := by
            apply fract_eq_of_int_add (Kp + pb)
            · have hcast : ((tp + (b : ℤ) : ℤ) : ℝ) * α = (tp : ℝ) * α + (b : ℝ) * α := by
                push_cast; ring
              rw [hcast, hyp_decom]; push_cast; dsimp only [e₂]; ring
            · linarith
            · linarith [he2.1]
          rw [hzb]; linarith [he2.1]
      · push Not at h1 h2
        refine ⟨a + b, by omega, le_refl _, ?_, ?_⟩
        · have hzab : z (tp + ((a + b : ℕ) : ℤ)) = y + e₁ - e₂ := by
            apply fract_eq_of_int_add (Kp + pa + pb)
            · have hcast : ((tp + ((a + b : ℕ) : ℤ) : ℤ) : ℝ) * α =
                  (tp : ℝ) * α + (a : ℝ) * α + (b : ℝ) * α := by push_cast; ring
              rw [hcast, hyp_decom]; push_cast; dsimp only [e₁, e₂]; ring
            · linarith [he2.2]
            · linarith [he1.2]
          rw [hzab]; linarith [he2.2]
        · have hzab : z (tp + ((a + b : ℕ) : ℤ)) = y + e₁ - e₂ := by
            apply fract_eq_of_int_add (Kp + pa + pb)
            · have hcast : ((tp + ((a + b : ℕ) : ℤ) : ℤ) : ℝ) * α =
                  (tp : ℝ) * α + (a : ℝ) * α + (b : ℝ) * α := by push_cast; ring
              rw [hcast, hyp_decom]; push_cast; dsimp only [e₁, e₂]; ring
            · linarith [he2.2]
            · linarith [he1.2]
          rw [hzab]; linarith [he1.2]
  obtain ⟨s, hs_pos, hs_le, hs_lo, hs_hi⟩ := hstep
  -- Step 5: By maximality of tp in S, tp + s > i; by hmiss, tp + s > i + r.
  have hgt_i : (i : ℤ) < tp + (s : ℤ) := by
    by_contra hle
    push Not at hle
    have hmem : tp + (s : ℤ) ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, hle⟩, hs_lo, hs_hi⟩
      have htp_ge : t₀ ≤ tp := (Finset.mem_Icc.mp (Finset.mem_filter.mp htp_mem).1).1
      omega
    have hmax := Finset.le_max' S (tp + (s : ℤ)) hmem
    omega
  have hgt_ir : (i + r : ℤ) < tp + (s : ℤ) := by
    by_contra hle
    push Not at hle
    exact hmiss (tp + (s : ℤ)) (by omega) hle ⟨hs_lo, hs_hi⟩
  omega

/-- Symmetric wrapper for `sturmian_three_gap_run_bound`: `a` and `b` may carry opposite signs
`sgn ∈ {1, -1}`. -/
theorem sturmian_three_gap_run_bound_sym {α : ℝ} (hα0 : 0 < α) (hα2 : α < 1 / 2)
    {p i r a b : ℕ} {m pa pb : ℤ} {sgn : ℝ}
    (hsgn : sgn = 1 ∨ sgn = -1) (hr : 1 ≤ r)
    (hδ0 : 0 < |(p : ℝ) * α - (m : ℝ)|) (hδα : |(p : ℝ) * α - (m : ℝ)| < α)
    (ha : 0 < a) (hb : 0 < b)
    (he1 : 0 < sgn * ((a : ℝ) * α - (pa : ℝ)) ∧ sgn * ((a : ℝ) * α - (pa : ℝ)) < |(p : ℝ) * α - (m : ℝ)|)
    (he2 : 0 < (-sgn) * ((b : ℝ) * α - (pb : ℝ)) ∧ (-sgn) * ((b : ℝ) * α - (pb : ℝ)) < |(p : ℝ) * α - (m : ℝ)|)
    (hrun : ∀ k < r, sturmian α (i + k) = sturmian α (i + k + p)) :
    r + 2 ≤ a + b := by
  rcases hsgn with rfl | rfl
  · simp only [one_mul, neg_mul, neg_sub] at he1 he2
    exact sturmian_three_gap_run_bound hα0 hα2 hr hδ0 hδα ha hb he1 he2 hrun
  · simp only [neg_mul, one_mul, neg_sub, neg_neg] at he1 he2
    have h := sturmian_three_gap_run_bound hα0 hα2 hr hδ0 hδα hb ha he2 he1 hrun
    omega

/-! ## Section 2: Colour Match Projection -/

/-- When `y` and `y'` have disjoint alphabets, a match in `colour u y y'` projects to a match in
`u` and a colour match in `y` or `y'`. -/
theorem colour_match_implies {d : ℕ} {u : ℕ → Bool} {y y' : ℕ → Fin d}
    (hdisj : ∀ a b, y a ≠ y' b) {n p : ℕ}
    (h : colour u y y' n = colour u y y' (n + p)) :
    u n = u (n + p) ∧
    (u n = true → y (countTrue u n) = y (countTrue u (n + p))) ∧
    (u n = false → y' (countFalse u n) = y' (countFalse u (n + p))) := by
  unfold colour at h
  cases h1 : u n <;> cases h2 : u (n + p)
  · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨rfl, fun hc => Bool.noConfusion hc, fun _ => h⟩
  · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
    exact False.elim (hdisj _ _ h.symm)
  · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
    exact False.elim (hdisj _ _ h)
  · simp only [h1, h2, ↓reduceIte] at h
    exact ⟨rfl, fun _ => h, fun hc => Bool.noConfusion hc⟩

/-! ## Section 3: Continued-Fraction Convergents, Periodic Ratios, and Level Engine -/

/-- Simultaneous convergent tuple `(p_k, q_k, p_{k-1}, q_{k-1})` for partial quotients `a : ℕ → ℕ`
with `a 0 = 0`. -/
def convPQ (a : ℕ → ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (0, 1, 1, 0)
  | k + 1 =>
    let t := convPQ a k
    (a (k + 1) * t.1 + t.2.2.1, a (k + 1) * t.2.1 + t.2.2.2, t.1, t.2.1)

/-- Numerator `p_k` of the `k`-th convergent. -/
def convP (a : ℕ → ℕ) (k : ℕ) : ℕ := (convPQ a k).1

/-- Denominator `q_k` of the `k`-th convergent. -/
def convQ (a : ℕ → ℕ) (k : ℕ) : ℕ := (convPQ a k).2.1

/-- Previous numerator `p_{k-1}` (with `p_{-1} = 1`). -/
def convPPrev (a : ℕ → ℕ) (k : ℕ) : ℕ := (convPQ a k).2.2.1

/-- Previous denominator `q_{k-1}` (with `q_{-1} = 0`). -/
def convQPrev (a : ℕ → ℕ) (k : ℕ) : ℕ := (convPQ a k).2.2.2

/-- Unsigned convergent approximation error `η_k = (-1)^k (q_k α - p_k)`. -/
noncomputable def eta (a : ℕ → ℕ) (α : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * ((convQ a k : ℝ) * α - (convP a k : ℝ))

theorem convP_succ (a : ℕ → ℕ) (k : ℕ) :
    convP a (k + 1) = a (k + 1) * convP a k + convPPrev a k := rfl

theorem convQ_succ (a : ℕ → ℕ) (k : ℕ) :
    convQ a (k + 1) = a (k + 1) * convQ a k + convQPrev a k := rfl

theorem convPPrev_succ (a : ℕ → ℕ) (k : ℕ) : convPPrev a (k + 1) = convP a k := rfl

theorem convQPrev_succ (a : ℕ → ℕ) (k : ℕ) : convQPrev a (k + 1) = convQ a k := rfl

/-- Unimodular determinant identity: `q_k p_{k-1} - p_k q_{k-1} = (-1)^k`. -/
theorem conv_det (a : ℕ → ℕ) (k : ℕ) :
    (convQ a k : ℤ) * (convPPrev a k : ℤ) - (convP a k : ℤ) * (convQPrev a k : ℤ) = (-1 : ℤ) ^ k := by
  induction k with
  | zero => simp [convP, convQ, convPPrev, convQPrev, convPQ]
  | succ k ih =>
    rw [convP_succ, convQ_succ, convPPrev_succ, convQPrev_succ]
    push_cast
    rw [pow_succ]
    linarith

/-- `0 < q_k` for all `k` when `∀ j ≥ 1, 1 ≤ a j`. -/
theorem convQ_pos {a : ℕ → ℕ} (ha : ∀ j, 1 ≤ j → 1 ≤ a j) (k : ℕ) : 0 < convQ a k := by
  induction k with
  | zero => simp [convQ, convPQ]
  | succ k ih =>
    rw [convQ_succ]
    have h1 : 1 ≤ a (k + 1) := ha (k + 1) (by omega)
    nlinarith

/-- `0 < q_{k-1}` and `q_{k-1} ≤ q_k` for all `k ≥ 1`. -/
theorem convQPrev_bounds {a : ℕ → ℕ} (ha : ∀ j, 1 ≤ j → 1 ≤ a j) {k : ℕ} (hk : 1 ≤ k) :
    0 < convQPrev a k ∧ convQPrev a k ≤ convQ a k := by
  cases k with
  | zero => omega
  | succ k =>
    rw [convQPrev_succ, convQ_succ]
    have hpos := convQ_pos ha k
    have h1 : 1 ≤ a (k + 1) := ha (k + 1) (by omega)
    exact ⟨hpos, by nlinarith⟩

/-- When `a (k + 1) = 1` for all `k ≥ 2`, `q_k ≤ 2 * q_{k-1}` for all `k ≥ 3`. -/
theorem convQ_le_two_prev_of_tail_one {a : ℕ → ℕ} (ha : ∀ j, 1 ≤ j → 1 ≤ a j)
    (htail : ∀ k, 3 ≤ k → a k = 1) {k : ℕ} (hk : 3 ≤ k) :
    convQ a k ≤ 2 * convQPrev a k := by
  cases k with
  | zero => omega
  | succ k =>
    rw [convQ_succ, convQPrev_succ, htail (k + 1) hk, one_mul]
    have hle := (convQPrev_bounds ha (by omega : 1 ≤ k)).2
    omega

/-- `p_k ≤ q_k` for all `k` when `a 1 ≥ 1`. -/
theorem convP_le_convQ {a : ℕ → ℕ} (ha1 : 1 ≤ a 1) (k : ℕ) :
    convP a k ≤ convQ a k ∧ (1 ≤ k → convPPrev a k ≤ convQPrev a k) := by
  induction k with
  | zero => simp [convP, convQ, convPQ]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [convP, convQ, convPPrev, convQPrev, convPQ, mul_zero, zero_add, mul_one, add_zero]
      exact ⟨ha1, fun _ => by omega⟩
    | succ k =>
      have h1 : convP a (k + 1) ≤ convQ a (k + 1) := ih.1
      have h2 : convPPrev a (k + 1) ≤ convQPrev a (k + 1) := ih.2 (by omega)
      rw [convP_succ, convQ_succ, convPPrev_succ, convQPrev_succ]
      exact ⟨Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2, fun _ => h1⟩

/-- Exact recurrence for unsigned approximation errors: `η_{k+1} = η_{k-1} - a_{k+1} η_k` for `k ≥ 1`. -/
theorem eta_recurrence (a : ℕ → ℕ) (α : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    eta a α (k + 1) = eta a α (k - 1) - (a (k + 1) : ℝ) * eta a α k := by
  cases k with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel]
    unfold eta
    rw [convQ_succ, convP_succ, convQPrev_succ, convPPrev_succ]
    push_cast
    have hp1 : (-1 : ℝ) ^ (k + 1 + 1) = (-1 : ℝ) ^ k := by rw [pow_succ, pow_succ]; ring
    have hp2 : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by rw [pow_succ]; ring
    rw [hp1, hp2]
    ring

/-- **Exact periodic error ratio induction**:
if `η 3 = θ 0 * η 2`, `a (n + 4) = a (4 + n % T)`, and `1 - a (4 + r) * θ r = θ r * θ ((r + 1) % T)`
for all `r < T`, then `η (n + 3) = θ (n % T) * η (n + 2)` for all `n : ℕ`. -/
theorem eta_periodic_ratio {a : ℕ → ℕ} {α : ℝ} {T : ℕ} (hT : 0 < T) (θ : ℕ → ℝ)
    (hbase : eta a α 3 = θ 0 * eta a α 2)
    (ha_per : ∀ n : ℕ, a (n + 4) = a (4 + n % T))
    (halg : ∀ r < T, 1 - (a (4 + r) : ℝ) * θ r = θ r * θ ((r + 1) % T)) :
    ∀ n : ℕ, eta a α (n + 3) = θ (n % T) * eta a α (n + 2) := by
  intro n
  induction n with
  | zero =>
    simpa [Nat.zero_mod] using hbase
  | succ n ih =>
    have hrec := eta_recurrence a α (k := n + 3) (by omega)
    have hsub : n + 3 - 1 = n + 2 := by omega
    rw [hsub, ih] at hrec
    have ha_eq : a (n + 3 + 1) = a (4 + n % T) := ha_per n
    have hmod_lt : n % T < T := Nat.mod_lt n hT
    have hid := halg (n % T) hmod_lt
    have hmod_succ : (n + 1) % T = (n % T + 1) % T := (Nat.mod_add_mod n T 1).symm
    have hcalc : eta a α (n + 3 + 1) =
        (1 - (a (4 + n % T) : ℝ) * θ (n % T)) * eta a α (n + 2) := by
      rw [hrec, ha_eq]; ring
    have hidx : n + 1 + 2 = n + 3 := by omega
    rw [hidx, ih]
    calc eta a α (n + 1 + 3)
        = (1 - (a (4 + n % T) : ℝ) * θ (n % T)) * eta a α (n + 2) := hcalc
      _ = θ (n % T) * θ ((n % T + 1) % T) * eta a α (n + 2) := by rw [hid]
      _ = θ ((n + 1) % T) * (θ (n % T) * eta a α (n + 2)) := by rw [← hmod_succ]; ring

/-- Positivity, strict decrease, and level existence for `eta a α`. -/
theorem eta_level_exists {a : ℕ → ℕ} {α : ℝ} {T : ℕ} (hT : 0 < T) {θ : ℕ → ℝ} {M : ℝ}
    (h0 : 0 < eta a α 0) (h1 : 0 < eta a α 1) (h10 : eta a α 1 < eta a α 0)
    (h2 : 0 < eta a α 2) (h21 : eta a α 2 < eta a α 1)
    (hrat : ∀ n : ℕ, eta a α (n + 3) = θ (n % T) * eta a α (n + 2))
    (hθ_pos : ∀ r < T, 0 < θ r) (hθ_le : ∀ r < T, θ r ≤ M) (hM1 : M < 1) :
    (∀ k : ℕ, 0 < eta a α k) ∧
    (∀ k : ℕ, eta a α (k + 1) < eta a α k) ∧
    (∀ δ : ℝ, 0 < δ → δ < eta a α 0 → ∃ k : ℕ, 1 ≤ k ∧ eta a α k ≤ δ ∧ δ < eta a α (k - 1)) := by
  have hpos : ∀ k : ℕ, 0 < eta a α k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 => exact h0
      | 1 => exact h1
      | 2 => exact h2
      | n + 3 =>
        rw [hrat n]
        exact mul_pos (hθ_pos (n % T) (Nat.mod_lt n hT)) (ih (n + 2) (by omega))
  have hdec : ∀ k : ℕ, eta a α (k + 1) < eta a α k := by
    intro k
    match k with
    | 0 => exact h10
    | 1 => exact h21
    | n + 2 =>
      rw [hrat n]
      have hθ1 : θ (n % T) < 1 := lt_of_le_of_lt (hθ_le (n % T) (Nat.mod_lt n hT)) hM1
      have hp := hpos (n + 2)
      nlinarith
  have hpow : ∀ n : ℕ, eta a α (n + 2) ≤ M ^ n * eta a α 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hrat n, pow_succ']
      have hle := hθ_le (n % T) (Nat.mod_lt n hT)
      have hM0 : 0 ≤ M := le_trans (le_of_lt (hθ_pos 0 hT)) (hθ_le 0 hT)
      have hp := le_of_lt (hpos (n + 2))
      have h1 : θ (n % T) * eta a α (n + 2) ≤ M * eta a α (n + 2) := mul_le_mul_of_nonneg_right hle hp
      have h2 : M * eta a α (n + 2) ≤ M * (M ^ n * eta a α 2) := mul_le_mul_of_nonneg_left ih hM0
      linarith
  refine ⟨hpos, hdec, ?_⟩
  intro δ hδ0 hδ_lt
  have hM0 : 0 ≤ M := le_trans (le_of_lt (hθ_pos 0 hT)) (hθ_le 0 hT)
  have hex : ∃ n : ℕ, eta a α n ≤ δ := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hδ0 h2) hM1
    refine ⟨N + 2, ?_⟩
    have hlt : M ^ N * eta a α 2 < δ := (lt_div_iff₀ h2).mp hN
    linarith [hpow N]
  classical
  let k := Nat.find hex
  have hk_le : eta a α k ≤ δ := Nat.find_spec hex
  have hk_pos : 1 ≤ k := by
    by_contra hlt
    have hk0 : k = 0 := by omega
    rw [hk0] at hk_le
    linarith
  have hk_prev : δ < eta a α (k - 1) := by
    have hnot := Nat.find_min hex (show k - 1 < k by omega)
    linarith
  exact ⟨k, hk_pos, hk_le, hk_prev⟩

/-- Unimodular basis decomposition at level `k ≥ 1`: every `(p, m)` with `0 < p` and
`|p α - m| < η_{k-1}` decomposes uniquely as `c (q_k, p_k) + d (q_{k-1}, p_{k-1})` with
`c ≥ 1`, `0 ≤ d ≤ c`, and `|p α - m| = |c η_k - d η_{k-1}|`. -/
theorem level_basis_decomp {a : ℕ → ℕ} {α : ℝ} (ha : ∀ j, 1 ≤ j → 1 ≤ a j) {k : ℕ} (hk : 1 ≤ k)
    (hηk : 0 < eta a α k) (hηk1 : 0 < eta a α (k - 1)) (hηlt : eta a α k < eta a α (k - 1))
    {p : ℕ} (hp : 0 < p) {m : ℤ} (hδ : |(p : ℝ) * α - (m : ℝ)| < eta a α (k - 1)) :
    ∃ c d : ℕ, 1 ≤ c ∧ d ≤ c ∧
      p = c * convQ a k + d * convQPrev a k ∧
      m = (c : ℤ) * (convP a k : ℤ) + (d : ℤ) * (convPPrev a k : ℤ) ∧
      |(p : ℝ) * α - (m : ℝ)| = |(c : ℝ) * eta a α k - (d : ℝ) * eta a α (k - 1)| := by
  have hdet := conv_det a k
  let s : ℤ := (-1 : ℤ) ^ k
  have hs2 : s * s = 1 := by
    dsimp only [s]; rw [← mul_pow]; norm_num
  let cZ : ℤ := s * ((p : ℤ) * (convPPrev a k : ℤ) - m * (convQPrev a k : ℤ))
  let dZ : ℤ := s * (m * (convQ a k : ℤ) - (p : ℤ) * (convP a k : ℤ))
  have hp_eq : (p : ℤ) = cZ * (convQ a k : ℤ) + dZ * (convQPrev a k : ℤ) := by
    have hlin : cZ * (convQ a k : ℤ) + dZ * (convQPrev a k : ℤ) =
        s * ((convQ a k : ℤ) * (convPPrev a k : ℤ) - (convP a k : ℤ) * (convQPrev a k : ℤ)) * (p : ℤ) := by
      dsimp only [cZ, dZ]; ring
    rw [hlin, hdet]
    change (p : ℤ) = s * s * (p : ℤ)
    rw [hs2, one_mul]
  have hm_eq : m = cZ * (convP a k : ℤ) + dZ * (convPPrev a k : ℤ) := by
    have hlin : cZ * (convP a k : ℤ) + dZ * (convPPrev a k : ℤ) =
        s * ((convQ a k : ℤ) * (convPPrev a k : ℤ) - (convP a k : ℤ) * (convQPrev a k : ℤ)) * m := by
      dsimp only [cZ, dZ]; ring
    rw [hlin, hdet]
    change m = s * s * m
    rw [hs2, one_mul]
  have hprev_p : convPPrev a k = convP a (k - 1) := by
    cases k with | zero => omega | succ k => rfl
  have hprev_q : convQPrev a k = convQ a (k - 1) := by
    cases k with | zero => omega | succ k => rfl
  have hdiff_eq : (p : ℝ) * α - (m : ℝ) =
      (-1 : ℝ) ^ k * ((cZ : ℝ) * eta a α k - (dZ : ℝ) * eta a α (k - 1)) := by
    have hpR : (p : ℝ) = (cZ : ℝ) * (convQ a k : ℝ) + (dZ : ℝ) * (convQ a (k - 1) : ℝ) := by
      rw [← hprev_q]; exact_mod_cast hp_eq
    have hmR : (m : ℝ) = (cZ : ℝ) * (convP a k : ℝ) + (dZ : ℝ) * (convP a (k - 1) : ℝ) := by
      rw [← hprev_p]; exact_mod_cast hm_eq
    rw [hpR, hmR]
    unfold eta
    have hpow2 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
    have hpow_prev : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k - 1) = -1 := by
      cases k with
      | zero => omega
      | succ k =>
        simp only [Nat.add_sub_cancel, pow_succ]
        have : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
        linarith
    calc ((cZ : ℝ) * (convQ a k : ℝ) + (dZ : ℝ) * (convQ a (k - 1) : ℝ)) * α -
          ((cZ : ℝ) * (convP a k : ℝ) + (dZ : ℝ) * (convP a (k - 1) : ℝ))
        = (cZ : ℝ) * ((convQ a k : ℝ) * α - (convP a k : ℝ)) +
          (dZ : ℝ) * ((convQ a (k - 1) : ℝ) * α - (convP a (k - 1) : ℝ)) := by ring
      _ = (cZ : ℝ) * (((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * ((convQ a k : ℝ) * α - (convP a k : ℝ))) -
          (dZ : ℝ) * (((-1 : ℝ) ^ k * (-1 : ℝ) ^ (k - 1)) * ((convQ a (k - 1) : ℝ) * α - (convP a (k - 1) : ℝ))) := by
          rw [hpow2, hpow_prev]; ring
      _ = (-1 : ℝ) ^ k * ((cZ : ℝ) * ((-1 : ℝ) ^ k * ((convQ a k : ℝ) * α - (convP a k : ℝ))) -
          (dZ : ℝ) * ((-1 : ℝ) ^ (k - 1) * ((convQ a (k - 1) : ℝ) * α - (convP a (k - 1) : ℝ)))) := by ring
  have habs : |(p : ℝ) * α - (m : ℝ)| = |(cZ : ℝ) * eta a α k - (dZ : ℝ) * eta a α (k - 1)| := by
    rw [hdiff_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs] at hδ
  have hqk_pos : 0 < convQ a k := convQ_pos ha k
  have hqk1_pos : 0 < convQPrev a k := (convQPrev_bounds ha hk).1
  have hc_pos : 1 ≤ cZ := by
    by_contra hle
    push Not at hle
    have hc0 : cZ ≤ 0 := by omega
    have hd_pos : 1 ≤ dZ := by
      by_contra hdle
      have hd0 : dZ ≤ 0 := by omega
      have : cZ * (convQ a k : ℤ) + dZ * (convQPrev a k : ℤ) ≤ 0 := by nlinarith
      omega
    have hcR : (cZ : ℝ) ≤ 0 := by exact_mod_cast hc0
    have hdR : (1 : ℝ) ≤ (dZ : ℝ) := by exact_mod_cast hd_pos
    have hge : eta a α (k - 1) ≤ (dZ : ℝ) * eta a α (k - 1) - (cZ : ℝ) * eta a α k := by nlinarith
    have hab := neg_le_abs ((cZ : ℝ) * eta a α k - (dZ : ℝ) * eta a α (k - 1))
    linarith
  have hd_nonneg : 0 ≤ dZ := by
    by_contra hlt
    push Not at hlt
    have hd1 : dZ ≤ -1 := by omega
    have hcR : (1 : ℝ) ≤ (cZ : ℝ) := by exact_mod_cast hc_pos
    have hdR : (dZ : ℝ) ≤ -1 := by exact_mod_cast hd1
    have hge : eta a α (k - 1) < (cZ : ℝ) * eta a α k - (dZ : ℝ) * eta a α (k - 1) := by nlinarith
    have hab := le_abs_self ((cZ : ℝ) * eta a α k - (dZ : ℝ) * eta a α (k - 1))
    linarith
  have hd_le_c : dZ ≤ cZ := by
    by_contra hgt
    push Not at hgt
    have hge1 : cZ + 1 ≤ dZ := by omega
    have hR : (cZ : ℝ) + 1 ≤ (dZ : ℝ) := by exact_mod_cast hge1
    have hcR : (1 : ℝ) ≤ (cZ : ℝ) := by exact_mod_cast hc_pos
    have hge : eta a α (k - 1) < (dZ : ℝ) * eta a α (k - 1) - (cZ : ℝ) * eta a α k := by nlinarith
    have hab := neg_le_abs ((cZ : ℝ) * eta a α k - (dZ : ℝ) * eta a α (k - 1))
    linarith
  let c : ℕ := cZ.toNat
  let d : ℕ := dZ.toNat
  have hc_cast : (c : ℤ) = cZ := Int.toNat_of_nonneg (by omega)
  have hd_cast : (d : ℤ) = dZ := Int.toNat_of_nonneg hd_nonneg
  have hcR : (c : ℝ) = (cZ : ℝ) := by exact_mod_cast hc_cast
  have hdR : (d : ℝ) = (dZ : ℝ) := by exact_mod_cast hd_cast
  refine ⟨c, d, by omega, by omega, ?_, ?_, ?_⟩
  · have : (p : ℤ) = ((c * convQ a k + d * convQPrev a k : ℕ) : ℤ) := by
      push_cast; rw [hc_cast, hd_cast]; exact hp_eq
    exact_mod_cast this
  · rw [hc_cast, hd_cast]; exact hm_eq
  · rw [habs, hcR, hdR]

/-- Modular convergent state `(p_k % ma, (q_k - p_k) % mb, p_{k-1} % ma, (q_{k-1} - p_{k-1}) % mb)`. -/
def convModState (a : ℕ → ℕ) (ma mb k : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (convP a k % ma, (convQ a k - convP a k) % mb,
   convPPrev a k % ma, (convQPrev a k - convPPrev a k) % mb)

/-- Modular convergent state transition depends only on `a (k + 1)` and the previous modular state. -/
theorem convModState_succ {a : ℕ → ℕ} (ha1 : 1 ≤ a 1) (ma mb : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    convModState a ma mb (k + 1) =
    let s := convModState a ma mb k
    ((a (k + 1) * s.1 + s.2.2.1) % ma,
     (a (k + 1) * s.2.1 + s.2.2.2) % mb,
     s.1, s.2.1) := by
  have hle := convP_le_convQ ha1 k
  have h1 : convP a k ≤ convQ a k := hle.1
  have h2 : convPPrev a k ≤ convQPrev a k := hle.2 hk
  have hdiff : convQ a (k + 1) - convP a (k + 1) =
      a (k + 1) * (convQ a k - convP a k) + (convQPrev a k - convPPrev a k) := by
    rw [convQ_succ, convP_succ]
    have hmul : a (k + 1) * (convQ a k - convP a k) = a (k + 1) * convQ a k - a (k + 1) * convP a k :=
      Nat.mul_sub_left_distrib _ _ _
    have hmle : a (k + 1) * convP a k ≤ a (k + 1) * convQ a k := Nat.mul_le_mul_left _ h1
    omega
  have h1mod : (a (k + 1) * convP a k + convPPrev a k) % ma =
      (a (k + 1) * (convP a k % ma) + convPPrev a k % ma) % ma := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.add_mod (a (k + 1) * (convP a k % ma)),
      Nat.mul_mod (a (k + 1)) (convP a k % ma),
      Nat.mod_mod_of_dvd _ (dvd_refl ma), Nat.mod_mod_of_dvd _ (dvd_refl ma)]
  have h2mod : (a (k + 1) * (convQ a k - convP a k) + (convQPrev a k - convPPrev a k)) % mb =
      (a (k + 1) * ((convQ a k - convP a k) % mb) + (convQPrev a k - convPPrev a k) % mb) % mb := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.add_mod (a (k + 1) * ((convQ a k - convP a k) % mb)),
      Nat.mul_mod (a (k + 1)) ((convQ a k - convP a k) % mb),
      Nat.mod_mod_of_dvd _ (dvd_refl mb), Nat.mod_mod_of_dvd _ (dvd_refl mb)]
  unfold convModState
  rw [hdiff, convP_succ, convPPrev_succ, convQPrev_succ, h1mod, h2mod]

/-- Periodicity of `convModState` from `k = 3` onward: if `a (k + 1)` has period `L_per` for
`k ≥ 3` and `convModState` agrees at `3 + L_per` and `3`, then it has period `L_per` for all `k ≥ 3`. -/
theorem convModState_periodic {a : ℕ → ℕ} (ha1 : 1 ≤ a 1) (ma mb L_per : ℕ) (hL : 0 < L_per)
    (ha_per : ∀ k : ℕ, 3 ≤ k → a (k + 1 + L_per) = a (k + 1))
    (hbase : convModState a ma mb (3 + L_per) = convModState a ma mb 3) :
    ∀ k : ℕ, 3 ≤ k → convModState a ma mb k = convModState a ma mb (3 + (k - 3) % L_per) := by
  have hshift : ∀ n : ℕ, convModState a ma mb (n + 3 + L_per) = convModState a ma mb (n + 3) := by
    intro n
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      have h1 : n + 1 + 3 + L_per = (n + 3 + L_per) + 1 := by omega
      have h2 : n + 1 + 3 = (n + 3) + 1 := by omega
      have h3 : n + 3 + L_per + 1 = (n + 3) + 1 + L_per := by omega
      rw [h1, h2, convModState_succ ha1 ma mb (by omega), convModState_succ ha1 ma mb (by omega),
        ih, h3, ha_per (n + 3) (by omega)]
  intro k hk
  generalize hm : k - 3 = m
  have hk_eq : k = m + 3 := by omega
  rw [hk_eq]
  clear hk_eq hk hm k
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hlt : m < L_per
    · rw [Nat.mod_eq_of_lt hlt, add_comm]
    · have hsub : m = (m - L_per) + L_per := by omega
      have hmod : m % L_per = (m - L_per) % L_per := by
        conv_lhs => rw [hsub, Nat.add_mod_right]
      rw [hmod]
      have heq : m + 3 = (m - L_per) + 3 + L_per := by omega
      rw [heq, hshift (m - L_per)]
      exact ih (m - L_per) (by omega)

/-- Irrationality helper: if `Irrational (Real.sqrt D)` and `b ≠ 0`, then `(a + b √D) / c` is
irrational (no non-zero integer `u` makes `u * α` an integer). -/
theorem quad_ne_int_div {A B : ℤ} {C D : ℕ} (hB : B ≠ 0) (hC : 0 < C)
    (hirr : Irrational (Real.sqrt (D : ℝ))) {u v : ℤ} (hu : u ≠ 0) :
    (u : ℝ) * (((A : ℝ) + (B : ℝ) * Real.sqrt (D : ℝ)) / (C : ℝ)) ≠ (v : ℝ) := by
  intro heq
  have hC0 : (C : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hC)
  have h1 : (u : ℝ) * ((A : ℝ) + (B : ℝ) * Real.sqrt (D : ℝ)) = (v : ℝ) * (C : ℝ) := by
    field_simp [hC0] at heq
    linarith
  have h2 : ((u * B : ℤ) : ℝ) * Real.sqrt (D : ℝ) = ((v * (C : ℤ) - u * A : ℤ) : ℝ) := by
    push_cast; linarith
  have huB : (u * B : ℤ) ≠ 0 := mul_ne_zero hu hB
  have huBR : ((u * B : ℤ) : ℝ) ≠ 0 := by exact_mod_cast huB
  have hrat : Real.sqrt (D : ℝ) = (((v * (C : ℤ) - u * A : ℤ) / (u * B : ℤ) : ℚ) : ℝ) := by
    have hq : (((v * (C : ℤ) - u * A : ℤ) / (u * B : ℤ) : ℚ) : ℝ) =
        ((v * (C : ℤ) - u * A : ℤ) : ℝ) / ((u * B : ℤ) : ℝ) := by
      push_cast; rfl
    rw [hq, eq_div_iff huBR, mul_comm]
    exact h2
  exact hirr ⟨((v * (C : ℤ) - u * A : ℤ) / (u * B : ℤ) : ℚ), hrat.symm⟩

/-- Bound mode for linear inequality `den * (J * q_k + q_{k-1} - 2) ≤ c * q_k + d * q_{k-1}`. -/
inductive LevelBoundMode : Type
  | exact (qk qk1 : ℕ)
  | unit
  | half

/-- Semantic precondition on `(q_k, q_{k-1})` corresponding to each `LevelBoundMode`. -/
def LevelBoundMode.Holds (mode : LevelBoundMode) (qk qk1 : ℕ) : Prop :=
  match mode with
  | .exact qk' qk1' => qk = qk' ∧ qk1 = qk1'
  | .unit => qk1 ≤ qk
  | .half => qk1 ≤ qk ∧ qk ≤ 2 * qk1

/-- Check the linear bound in `(q_k, q_{k-1})` for a given `(c, d, J, den)` and mode. -/
def checkLinearBound (mode : LevelBoundMode) (den c d J : ℕ) : Bool :=
  match mode with
  | .exact qk qk1 => decide (den * (J * qk + qk1 - 2) ≤ c * qk + d * qk1)
  | .unit => decide (den * J ≤ c) && decide (den * (J + 1) ≤ c + d)
  | .half => decide (den * (2 * J + 1) ≤ 2 * c + d) && decide (den * (J + 1) ≤ c + d)

/-- Find the least `j ∈ [1, ak1]` such that `prec - j * loN < dLo` (or `ak1` if none). -/
def findSemiconvJ (ak1 loN prec : ℕ) (dLo : ℤ) : ℕ :=
  go 1 ak1
where
  go (j : ℕ) : ℕ → ℕ
    | 0 => ak1
    | fuel + 1 =>
      if (prec : ℤ) - (j : ℤ) * (loN : ℤ) < dLo then j
      else go (j + 1) fuel

/-- Check a single `(c, d)` pair inside a level class using scaled integer interval arithmetic. -/
def checkLevelPair (ma mb den ak1 pa pb pa1 pb1 loN hiN prec : ℕ)
    (mode : LevelBoundMode) (c d : ℕ) : Bool :=
  if (c * pa + d * pa1) % ma != 0 || (c * pb + d * pb1) % mb != 0 then
    true
  else
    let xLo : ℤ := (c : ℤ) * (loN : ℤ) - (d : ℤ) * (prec : ℤ)
    let xHi : ℤ := (c : ℤ) * (hiN : ℤ) - (d : ℤ) * (prec : ℤ)
    let dLo : ℤ := if 0 ≤ xLo then xLo else if xHi ≤ 0 then -xHi else 0
    let dHi : ℤ := if 0 ≤ xLo then xHi else if xHi ≤ 0 then -xLo else max (-xLo) xHi
    if dHi < (loN : ℤ) || (prec : ℤ) ≤ dLo then
      true
    else if (hiN : ℤ) < dLo then
      let j := findSemiconvJ ak1 loN prec dLo
      checkLinearBound mode den c d (j + 1)
    else
      false

/-- Pure-kernel level-class checker: verifies all `(c, d)` with `1 ≤ c < den * (ak1 + 2)` and
`0 ≤ d ≤ c`. -/
def checkLevelClass (ma mb den ak1 pa pb pa1 pb1 loN hiN prec : ℕ)
    (mode : LevelBoundMode) : Bool :=
  let cLim := den * (ak1 + 2)
  (List.range cLim).all fun c =>
    if c == 0 then true
    else (List.range (c + 1)).all fun d =>
      checkLevelPair ma mb den ak1 pa pb pa1 pb1 loN hiN prec mode c d

/-- Soundness of `findSemiconvJ.go`: returns `j` with `1 ≤ j ≤ ak1`, and if `j < ak1` then
`prec - j * loN < dLo`. -/
theorem findSemiconvJ_spec (ak1 loN prec : ℕ) (dLo : ℤ) (hak1 : 1 ≤ ak1) :
    let j := findSemiconvJ ak1 loN prec dLo
    1 ≤ j ∧ j ≤ ak1 ∧ (j < ak1 → (prec : ℤ) - (j : ℤ) * (loN : ℤ) < dLo) := by
  have hgo : ∀ (j fuel : ℕ), 1 ≤ j → j + fuel = ak1 + 1 →
      let r := findSemiconvJ.go ak1 loN prec dLo j fuel
      1 ≤ r ∧ r ≤ ak1 ∧ (r < ak1 → (prec : ℤ) - (r : ℤ) * (loN : ℤ) < dLo) := by
    intro j fuel
    induction fuel generalizing j with
    | zero =>
      intro _ _
      simp only [findSemiconvJ.go]
      exact ⟨hak1, le_refl ak1, fun h => by omega⟩
    | succ fuel ih =>
      intro hj hsum
      simp only [findSemiconvJ.go]
      split_ifs with hlt
      · exact ⟨hj, by omega, fun _ => hlt⟩
      · exact ih (j + 1) (by omega) (by omega)
  exact hgo 1 ak1 (le_refl 1) (by omega)

/-- Soundness of `checkLinearBound`: implies `den * (J * qk + qk1 - 2) ≤ c * qk + d * qk1`
under the corresponding hypothesis on `(qk, qk1)`. -/
theorem checkLinearBound_sound {mode : LevelBoundMode} {den c d J qk qk1 : ℕ}
    (hchk : checkLinearBound mode den c d J = true)
    (hmode : mode.Holds qk qk1) :
    den * (J * qk + qk1 - 2) ≤ c * qk + d * qk1 := by
  cases mode with
  | exact qk' qk1' =>
    rcases hmode with ⟨rfl, rfl⟩
    simp only [checkLinearBound, decide_eq_true_eq] at hchk
    exact hchk
  | unit =>
    simp only [checkLinearBound, Bool.and_eq_true, decide_eq_true_eq] at hchk
    have h1 : den * (J * qk + qk1) ≤ c * qk + d * qk1 := by
      have hq : qk1 ≤ qk := hmode
      have hc : den * J ≤ c := hchk.1
      have hcd : den * (J + 1) ≤ c + d := hchk.2
      -- Write (c - den * J) * qk + d * qk1 - den * qk1 ≥ (c - den * J + d - den) * qk1 ≥ 0.
      have hA : den * J * qk ≤ c * qk := Nat.mul_le_mul_right qk hc
      have hB : (c - den * J) * qk1 ≤ (c - den * J) * qk := Nat.mul_le_mul_left _ hq
      have hC : den * J * qk + (c - den * J) * qk = c * qk := by
        rw [← Nat.add_mul, Nat.add_sub_of_le hc]
      have hD : den * qk1 ≤ (c - den * J) * qk1 + d * qk1 := by
        rw [← Nat.add_mul]
        apply Nat.mul_le_mul_right
        have hstep : den * (J + 1) = den * J + den := by ring
        omega
      calc den * (J * qk + qk1) = den * J * qk + den * qk1 := by ring
        _ ≤ den * J * qk + ((c - den * J) * qk1 + d * qk1) := Nat.add_le_add_left hD _
        _ ≤ den * J * qk + ((c - den * J) * qk + d * qk1) := Nat.add_le_add_left (Nat.add_le_add_right hB _) _
        _ = (den * J * qk + (c - den * J) * qk) + d * qk1 := by ring
        _ = c * qk + d * qk1 := by rw [hC]
    exact le_trans (Nat.mul_le_mul_left den (Nat.sub_le _ _)) h1
  | half =>
    simp only [checkLinearBound, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hmode with ⟨hle, h2le⟩
    have h1 : den * (J * qk + qk1) ≤ c * qk + d * qk1 := by
      -- Convex combination of endpoints qk = qk1 and qk = 2 * qk1:
      -- let u = qk - qk1 ≥ 0, v = 2 * qk1 - qk ≥ 0; then u + v = qk1, qk = 2*u + v, qk1 = u + v.
      let u := qk - qk1
      let v := 2 * qk1 - qk
      have hqk_eq : qk = 2 * u + v := by omega
      have hqk1_eq : qk1 = u + v := by omega
      have h1u : den * (2 * J + 1) ≤ 2 * c + d := hchk.1
      have h1v : den * (J + 1) ≤ c + d := hchk.2
      calc den * (J * qk + qk1)
          = den * (2 * J + 1) * u + den * (J + 1) * v := by rw [hqk_eq, hqk1_eq]; ring
        _ ≤ (2 * c + d) * u + (c + d) * v :=
            Nat.add_le_add (Nat.mul_le_mul_right u h1u) (Nat.mul_le_mul_right v h1v)
        _ = c * (2 * u + v) + d * (u + v) := by ring
        _ = c * qk + d * qk1 := by rw [← hqk_eq, ← hqk1_eq]
    exact le_trans (Nat.mul_le_mul_left den (Nat.sub_le _ _)) h1

/-- Three-gap semiconvergent run bound at level `k ≥ 1`: if `η_k < δ` and `η_{k-1} - j η_k < δ`
for `1 ≤ j ≤ a_{k+1}`, then every match run of length `r ≥ 1` satisfies
`r + 2 ≤ (j + 1) * q_k + q_{k-1}`. -/
theorem level_three_gap_step {a : ℕ → ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 1 / 2)
    (ha : ∀ j, 1 ≤ j → 1 ≤ a j)
    {k ak1 j p i r : ℕ} {m : ℤ}
    (hk : 1 ≤ k) (hak1 : a (k + 1) = ak1)
    (_hj1 : 1 ≤ j) (hjak : j ≤ ak1) (hr1 : 1 ≤ r)
    (hηk : 0 < eta a α k) (hηk_next : 0 < eta a α (k + 1))
    (hδα : |(p : ℝ) * α - (m : ℝ)| < α)
    (hgt1 : eta a α k < |(p : ℝ) * α - (m : ℝ)|)
    (hgt2 : eta a α (k - 1) - (j : ℝ) * eta a α k < |(p : ℝ) * α - (m : ℝ)|)
    (hrun : ∀ t < r, sturmian α (i + t) = sturmian α (i + t + p)) :
    r + 2 ≤ (j + 1) * convQ a k + convQPrev a k := by
  have hδ0 : 0 < |(p : ℝ) * α - (m : ℝ)| := lt_trans hηk hgt1
  have hqk_pos : 0 < convQ a k := convQ_pos ha k
  have hqk1_pos : 0 < convQPrev a k := (convQPrev_bounds ha hk).1
  have hrec_k : eta a α (k + 1) = eta a α (k - 1) - (ak1 : ℝ) * eta a α k := by
    rw [← hak1]; exact eta_recurrence a α hk
  have he2_pos : 0 < eta a α (k - 1) - (j : ℝ) * eta a α k := by
    have hjR : (j : ℝ) ≤ (ak1 : ℝ) := by exact_mod_cast hjak
    nlinarith
  have hprev_p : convPPrev a k = convP a (k - 1) := by
    cases k with | zero => omega | succ k => rfl
  have hprev_q : convQPrev a k = convQ a (k - 1) := by
    cases k with | zero => omega | succ k => rfl
  let sgn : ℝ := (-1 : ℝ) ^ k
  have hsgn : sgn = 1 ∨ sgn = -1 := by
    dsimp only [sgn]
    rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · left; rw [← two_mul, pow_mul]; norm_num
    · right; rw [pow_succ, pow_mul]; norm_num
  have hsgn_prev : (-sgn) = (-1 : ℝ) ^ (k - 1) := by
    dsimp only [sgn]
    cases k with
    | zero => omega
    | succ k => simp [pow_succ]
  have hval1 : sgn * ((convQ a k : ℝ) * α - ((convP a k : ℤ) : ℝ)) = eta a α k := by
    simp [eta, sgn]
  have hval2 : (-sgn) * (((convQPrev a k + j * convQ a k : ℕ) : ℝ) * α -
      (((convPPrev a k + j * convP a k : ℕ) : ℤ) : ℝ)) =
      eta a α (k - 1) - (j : ℝ) * eta a α k := by
    push_cast
    rw [hprev_p, hprev_q]
    have hlin : (-sgn) * (((convQ a (k - 1) : ℝ) + (j : ℝ) * (convQ a k : ℝ)) * α -
        ((convP a (k - 1) : ℝ) + (j : ℝ) * (convP a k : ℝ))) =
        ((-sgn) * ((convQ a (k - 1) : ℝ) * α - (convP a (k - 1) : ℝ))) -
        (j : ℝ) * (sgn * ((convQ a k : ℝ) * α - (convP a k : ℝ))) := by ring
    rw [hlin, hsgn_prev]
    rfl
  have hbound := sturmian_three_gap_run_bound_sym
    (a := convQ a k) (b := convQPrev a k + j * convQ a k)
    (pa := (convP a k : ℤ)) (pb := ((convPPrev a k + j * convP a k : ℕ) : ℤ))
    (sgn := sgn) hα0 hα2 hsgn hr1 hδ0 hδα
    hqk_pos (by omega)
    (by rw [hval1]; exact ⟨hηk, hgt1⟩)
    (by rw [hval2]; exact ⟨he2_pos, hgt2⟩)
    hrun
  have hsum : convQ a k + (convQPrev a k + j * convQ a k) = (j + 1) * convQ a k + convQPrev a k := by ring
  omega

/-- Large-`c` branch at level `k ≥ 1`: whenever `c ≥ den * (ak1 + 2)` (with `1 ≤ den`),
irrationality of `α` forces `η_k < δ`, giving `r * den ≤ p` immediately. -/
theorem level_big_c_bound {a : ℕ → ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 1 / 2)
    (hirr : ∀ (u v : ℤ), u ≠ 0 → (u : ℝ) * α ≠ (v : ℝ))
    (ha : ∀ j, 1 ≤ j → 1 ≤ a j)
    {k ak1 den c d p i r : ℕ} {m : ℤ}
    (hk : 1 ≤ k) (hden : 1 ≤ den) (hak1 : a (k + 1) = ak1)
    (hc1 : 1 ≤ c) (hc_big : den * (ak1 + 2) ≤ c) (hr1 : 1 ≤ r)
    (hηk : 0 < eta a α k) (hηk_next : 0 < eta a α (k + 1)) (hηlt_next : eta a α (k + 1) < eta a α k)
    (hp_cd : p = c * convQ a k + d * convQPrev a k)
    (hδ_lo : eta a α k ≤ |(p : ℝ) * α - (m : ℝ)|)
    (hδ_cd : |(p : ℝ) * α - (m : ℝ)| = |(c : ℝ) * eta a α k - (d : ℝ) * eta a α (k - 1)|)
    (hδα : |(p : ℝ) * α - (m : ℝ)| < α)
    (hrun : ∀ t < r, sturmian α (i + t) = sturmian α (i + t + p)) :
    r * den ≤ p := by
  have hak1_pos : 1 ≤ ak1 := by rw [← hak1]; exact ha (k + 1) (by omega)
  have hqk_pos : 0 < convQ a k := convQ_pos ha k
  have hqk1_b := convQPrev_bounds ha hk
  have hc2 : 2 ≤ c := by
    have : 3 ≤ den * (ak1 + 2) := by nlinarith
    omega
  have hgt1 : eta a α k < |(p : ℝ) * α - (m : ℝ)| := by
    by_contra hle
    have heq : |(p : ℝ) * α - (m : ℝ)| = eta a α k := le_antisymm (not_lt.mp hle) hδ_lo
    rw [hδ_cd] at heq
    have hlin : ∃ s : ℕ, 1 ≤ s ∧ (s : ℝ) * eta a α k = (d : ℝ) * eta a α (k - 1) := by
      rcases eq_or_eq_neg_of_abs_eq heq with hpos | hneg
      · refine ⟨c - 1, by omega, ?_⟩
        have hc1R : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by rw [Nat.cast_sub hc1, Nat.cast_one]
        rw [hc1R]; linarith
      · refine ⟨c + 1, by omega, ?_⟩
        push_cast; linarith
    obtain ⟨s, hs1, hs_eq⟩ := hlin
    have hprev_p : convPPrev a k = convP a (k - 1) := by
      cases k with | zero => omega | succ k => rfl
    have hprev_q : convQPrev a k = convQ a (k - 1) := by
      cases k with | zero => omega | succ k => rfl
    have hpow_prev : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k - 1) = -1 := by
      cases k with
      | zero => omega
      | succ k =>
        simp only [Nat.add_sub_cancel, pow_succ]
        have : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
        linarith
    have hpow2 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
    have hrat : (((s * convQ a k + d * convQPrev a k : ℕ) : ℤ) : ℝ) * α =
        (((s * convP a k + d * convPPrev a k : ℕ) : ℤ) : ℝ) := by
      have hmul := congrArg (fun x => (-1 : ℝ) ^ k * x) hs_eq
      dsimp only [eta] at hmul
      rw [hprev_p, hprev_q]
      have hL : (-1 : ℝ) ^ k * ((s : ℝ) * ((-1 : ℝ) ^ k * ((convQ a k : ℝ) * α - (convP a k : ℝ)))) =
          (s : ℝ) * ((convQ a k : ℝ) * α - (convP a k : ℝ)) := by
        have : (-1 : ℝ) ^ k * ((s : ℝ) * ((-1 : ℝ) ^ k * ((convQ a k : ℝ) * α - (convP a k : ℝ)))) =
            ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * ((s : ℝ) * ((convQ a k : ℝ) * α - (convP a k : ℝ))) := by ring
        rw [this, hpow2, one_mul]
      have hR : (-1 : ℝ) ^ k * ((d : ℝ) * ((-1 : ℝ) ^ (k - 1) * ((convQ a (k - 1) : ℝ) * α - (convP a (k - 1) : ℝ)))) =
          -(d : ℝ) * ((convQ a (k - 1) : ℝ) * α - (convP a (k - 1) : ℝ)) := by
        have : (-1 : ℝ) ^ k * ((d : ℝ) * ((-1 : ℝ) ^ (k - 1) * ((convQ a (k - 1) : ℝ) * α - (convP a (k - 1) : ℝ)))) =
            ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (k - 1)) * ((d : ℝ) * ((convQ a (k - 1) : ℝ) * α - (convP a (k - 1) : ℝ))) := by ring
        rw [this, hpow_prev]; ring
      rw [hL, hR] at hmul
      push_cast
      linarith
    have hu_ne : ((s * convQ a k + d * convQPrev a k : ℕ) : ℤ) ≠ 0 := by
      have : 0 < s * convQ a k := Nat.mul_pos (by omega) hqk_pos
      omega
    exact hirr _ _ hu_ne hrat
  have hrec_k : eta a α (k + 1) = eta a α (k - 1) - (ak1 : ℝ) * eta a α k := by
    rw [← hak1]; exact eta_recurrence a α hk
  have hgt2 : eta a α (k - 1) - (ak1 : ℝ) * eta a α k < |(p : ℝ) * α - (m : ℝ)| := by
    rw [← hrec_k]; exact lt_trans hηlt_next hgt1
  have htg := level_three_gap_step hα0 hα2 ha hk hak1 hak1_pos (le_refl ak1) hr1
    hηk hηk_next hδα hgt1 hgt2 hrun
  have hle : r ≤ (ak1 + 2) * convQ a k := by
    have hstep : (ak1 + 2) * convQ a k = (ak1 + 1) * convQ a k + convQ a k := by ring
    have := hqk1_b.2
    omega
  calc r * den ≤ (ak1 + 2) * convQ a k * den := Nat.mul_le_mul_right den hle
    _ = den * (ak1 + 2) * convQ a k := by ring
    _ ≤ c * convQ a k := Nat.mul_le_mul_right (convQ a k) hc_big
    _ ≤ c * convQ a k + d * convQPrev a k := Nat.le_add_right _ _
    _ = p := hp_cd.symm

/-- Soundness of a single checked `(c, d)` pair inside `checkLevelClass`. -/
theorem checkLevelPair_sound {a : ℕ → ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 1 / 2)
    (ha : ∀ j, 1 ≤ j → 1 ≤ a j)
    {k ma mb den ak1 pa pb pa1 pb1 loN hiN prec c d p i r : ℕ} {m : ℤ}
    {mode : LevelBoundMode}
    (hk : 1 ≤ k) (hprec : 0 < prec) (hak1 : a (k + 1) = ak1)
    (hc1 : 1 ≤ c) (hr1 : 1 ≤ r)
    (hηk : 0 < eta a α k) (hηk1 : 0 < eta a α (k - 1)) (hηk_next : 0 < eta a α (k + 1))
    (hηlt_next : eta a α (k + 1) < eta a α k)
    (hθ_lo : (loN : ℝ) / (prec : ℝ) < eta a α k / eta a α (k - 1))
    (hθ_hi : eta a α k / eta a α (k - 1) < (hiN : ℝ) / (prec : ℝ))
    (hmode : mode.Holds (convQ a k) (convQPrev a k))
    (hc_ma : (c * pa + d * pa1) % ma = 0) (hc_mb : (c * pb + d * pb1) % mb = 0)
    (hpair : checkLevelPair ma mb den ak1 pa pb pa1 pb1 loN hiN prec mode c d = true)
    (hp_cd : p = c * convQ a k + d * convQPrev a k)
    (hδ_lo : eta a α k ≤ |(p : ℝ) * α - (m : ℝ)|)
    (hδ_hi : |(p : ℝ) * α - (m : ℝ)| < eta a α (k - 1))
    (hδ_cd : |(p : ℝ) * α - (m : ℝ)| = |(c : ℝ) * eta a α k - (d : ℝ) * eta a α (k - 1)|)
    (hδα : |(p : ℝ) * α - (m : ℝ)| < α)
    (hrun : ∀ t < r, sturmian α (i + t) = sturmian α (i + t + p)) :
    r * den ≤ p := by
  have hak1_pos : 1 ≤ ak1 := by rw [← hak1]; exact ha (k + 1) (by omega)
  unfold checkLevelPair at hpair
  have hmod_false : ((c * pa + d * pa1) % ma != 0 || (c * pb + d * pb1) % mb != 0) = false := by
    simp [hc_ma, hc_mb]
  simp only [hmod_false, Bool.false_eq_true, ↓reduceIte] at hpair
  set θ : ℝ := eta a α k / eta a α (k - 1)
  have hprecR : (0 : ℝ) < (prec : ℝ) := Nat.cast_pos.mpr hprec
  have hθ_lo' : (loN : ℝ) < (prec : ℝ) * θ := by
    have := (div_lt_iff₀ hprecR).mp hθ_lo; linarith
  have hθ_hi' : (prec : ℝ) * θ < (hiN : ℝ) := by
    have := (lt_div_iff₀ hprecR).mp hθ_hi; linarith
  set x : ℝ := (c : ℝ) * θ - (d : ℝ)
  set px : ℝ := (prec : ℝ) * x
  have hδ_scaled : |(p : ℝ) * α - (m : ℝ)| = |x| * eta a α (k - 1) := by
    rw [hδ_cd]
    have h1 : (c : ℝ) * eta a α k - (d : ℝ) * eta a α (k - 1) = x * eta a α (k - 1) := by
      dsimp only [x, θ]; field_simp [ne_of_gt hηk1]
    rw [h1, abs_mul, abs_of_pos hηk1]
  have hx_lo_bound : θ ≤ |x| := by
    have : eta a α k ≤ |x| * eta a α (k - 1) := by rwa [← hδ_scaled]
    exact (div_le_iff₀ hηk1).mpr this
  have hx_hi_bound : |x| < 1 := by
    have : |x| * eta a α (k - 1) < 1 * eta a α (k - 1) := by rw [one_mul, ← hδ_scaled]; exact hδ_hi
    exact lt_of_mul_lt_mul_right this (le_of_lt hηk1)
  set xLo : ℤ := (c : ℤ) * (loN : ℤ) - (d : ℤ) * (prec : ℤ)
  set xHi : ℤ := (c : ℤ) * (hiN : ℤ) - (d : ℤ) * (prec : ℤ)
  have hpx_lo : (xLo : ℝ) < px := by
    have hcR : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr (by omega)
    dsimp only [xLo, px, x]; push_cast; nlinarith
  have hpx_hi : px < (xHi : ℝ) := by
    have hcR : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr (by omega)
    dsimp only [xHi, px, x]; push_cast; nlinarith
  set dLo : ℤ := if 0 ≤ xLo then xLo else if xHi ≤ 0 then -xHi else 0
  set dHi : ℤ := if 0 ≤ xLo then xHi else if xHi ≤ 0 then -xLo else max (-xLo) xHi
  have hpx_abs : (prec : ℝ) * |x| = |px| := by
    dsimp only [px]; rw [abs_mul, abs_of_pos hprecR]
  have habs_lo : (dLo : ℝ) ≤ (prec : ℝ) * |x| := by
    rw [hpx_abs]; dsimp only [dLo]
    split_ifs with h1 h2
    · have h1R : (0 : ℝ) ≤ (xLo : ℝ) := by exact_mod_cast h1
      rw [abs_of_nonneg (by linarith)]; linarith
    · have h2R : (xHi : ℝ) ≤ 0 := by exact_mod_cast h2
      push_cast; rw [abs_of_neg (by linarith)]; linarith
    · push_cast; exact abs_nonneg _
  have habs_hi : (prec : ℝ) * |x| ≤ (dHi : ℝ) := by
    rw [hpx_abs]; dsimp only [dHi]
    split_ifs with h1 h2
    · have h1R : (0 : ℝ) ≤ (xLo : ℝ) := by exact_mod_cast h1
      rw [abs_of_nonneg (by linarith)]; linarith
    · have h2R : (xHi : ℝ) ≤ 0 := by exact_mod_cast h2
      push_cast; rw [abs_of_neg (by linarith)]; linarith
    · push_cast; rw [abs_le]
      exact ⟨by linarith [le_max_left (-(xLo : ℝ)) (xHi : ℝ)],
             by linarith [le_max_right (-(xLo : ℝ)) (xHi : ℝ)]⟩
  have hnot_out : ¬ (dHi < (loN : ℤ) ∨ (prec : ℤ) ≤ dLo) := by
    rintro (h1 | h2)
    · have h1R : (dHi : ℝ) < (loN : ℝ) := by exact_mod_cast h1
      have hlo_px : (prec : ℝ) * θ ≤ (prec : ℝ) * |x| :=
        mul_le_mul_of_nonneg_left hx_lo_bound (le_of_lt hprecR)
      linarith
    · have h2R : (prec : ℝ) ≤ (dLo : ℝ) := by exact_mod_cast h2
      have hlt_px : (prec : ℝ) * |x| < (prec : ℝ) := by nlinarith
      linarith
  have hcond1 : (decide (dHi < (loN : ℤ)) || decide ((prec : ℤ) ≤ dLo)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨fun h => hnot_out (Or.inl h), fun h => hnot_out (Or.inr h)⟩
  have hpair' : (if (hiN : ℤ) < dLo then
      checkLinearBound mode den c d (findSemiconvJ ak1 loN prec dLo + 1) else false) = true := by
    change (if (decide (dHi < (loN : ℤ)) || decide ((prec : ℤ) ≤ dLo)) then true
      else if (hiN : ℤ) < dLo then checkLinearBound mode den c d (findSemiconvJ ak1 loN prec dLo + 1)
      else false) = true at hpair
    rw [hcond1] at hpair
    simpa using hpair
  by_cases hhi_lt : (hiN : ℤ) < dLo
  · simp only [hhi_lt, ↓reduceIte] at hpair'
    have hhiR : (hiN : ℝ) < (dLo : ℝ) := by exact_mod_cast hhi_lt
    have hθ_lt_x : θ < |x| := by nlinarith
    have hgt1 : eta a α k < |(p : ℝ) * α - (m : ℝ)| := by
      rw [hδ_scaled]
      have := mul_lt_mul_of_pos_right hθ_lt_x hηk1
      dsimp only [θ] at this
      rwa [div_mul_cancel₀ _ (ne_of_gt hηk1)] at this
    set j := findSemiconvJ ak1 loN prec dLo
    obtain ⟨hj1, hjak, hj_spec⟩ := findSemiconvJ_spec ak1 loN prec dLo hak1_pos
    have hgt2 : eta a α (k - 1) - (j : ℝ) * eta a α k < |(p : ℝ) * α - (m : ℝ)| := by
      by_cases hj_lt : j < ak1
      · have hjR : (prec : ℝ) - (j : ℝ) * (loN : ℝ) < (dLo : ℝ) := by exact_mod_cast (hj_spec hj_lt)
        have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by omega)
        have h1 : (prec : ℝ) * (1 - (j : ℝ) * θ) < (prec : ℝ) * |x| := by nlinarith
        have h2 : 1 - (j : ℝ) * θ < |x| := lt_of_mul_lt_mul_left h1 (le_of_lt hprecR)
        have h3 := mul_lt_mul_of_pos_right h2 hηk1
        rw [hδ_scaled]
        have h4 : (1 - (j : ℝ) * θ) * eta a α (k - 1) = eta a α (k - 1) - (j : ℝ) * eta a α k := by
          dsimp only [θ]; field_simp [ne_of_gt hηk1]
        linarith
      · have hj_eq : j = ak1 := by omega
        rw [hj_eq]
        have hrec_k : eta a α (k + 1) = eta a α (k - 1) - (ak1 : ℝ) * eta a α k := by
          rw [← hak1]; exact eta_recurrence a α hk
        rw [← hrec_k]
        exact lt_trans hηlt_next hgt1
    have htg := level_three_gap_step hα0 hα2 ha hk hak1 hj1 hjak hr1
      hηk hηk_next hδα hgt1 hgt2 hrun
    have hlin := checkLinearBound_sound (qk := convQ a k) (qk1 := convQPrev a k) hpair' hmode
    have hr_le : r ≤ (j + 1) * convQ a k + convQPrev a k - 2 := Nat.le_sub_of_add_le htg
    calc r * den = den * r := mul_comm r den
      _ ≤ den * ((j + 1) * convQ a k + convQPrev a k - 2) := Nat.mul_le_mul_left den hr_le
      _ ≤ c * convQ a k + d * convQPrev a k := hlin
      _ = p := hp_cd.symm
  · simp only [hhi_lt, ↓reduceIte] at hpair'
    exact Bool.noConfusion hpair'

/-- **Main soundness theorem for `checkLevelClass`**:
if a level `k ≥ 1` has `a (k + 1) = ak1`, modular state `(pa, pb, pa1, pb1)`, ratio
`θ = η_k / η_{k-1} ∈ (loN / prec, hiN / prec)`, and `checkLevelClass = true`, then EVERY
full-colour period `p` at level `k` (`η_k ≤ |p α - m| < η_{k-1}`) has every match run of
`sturmian α` bounded by `r * den ≤ p`. -/
theorem checkLevelClass_sound {a : ℕ → ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 1 / 2)
    (hirr : ∀ (u v : ℤ), u ≠ 0 → (u : ℝ) * α ≠ (v : ℝ))
    (ha : ∀ j, 1 ≤ j → 1 ≤ a j)
    {k ma mb den ak1 pa pb pa1 pb1 loN hiN prec : ℕ}
    {mode : LevelBoundMode}
    (hk : 1 ≤ k) (hden : 1 ≤ den) (hprec : 0 < prec)
    (hak1 : a (k + 1) = ak1)
    (hmod : convModState a ma mb k = (pa, pb, pa1, pb1))
    (hηk : 0 < eta a α k) (hηk1 : 0 < eta a α (k - 1)) (hηk_next : 0 < eta a α (k + 1))
    (hηlt : eta a α k < eta a α (k - 1)) (hηlt_next : eta a α (k + 1) < eta a α k)
    (hθ_lo : (loN : ℝ) / (prec : ℝ) < eta a α k / eta a α (k - 1))
    (hθ_hi : eta a α k / eta a α (k - 1) < (hiN : ℝ) / (prec : ℝ))
    (hmode : mode.Holds (convQ a k) (convQPrev a k))
    (hchk : checkLevelClass ma mb den ak1 pa pb pa1 pb1 loN hiN prec mode = true)
    {p i r : ℕ} {m : ℤ}
    (hp : 0 < p) (hm0 : 0 ≤ m)
    (hδ_lo : eta a α k ≤ |(p : ℝ) * α - (m : ℝ)|)
    (hδ_hi : |(p : ℝ) * α - (m : ℝ)| < eta a α (k - 1))
    (hδα : |(p : ℝ) * α - (m : ℝ)| < α)
    (hma : m.toNat % ma = 0) (hmb : (p - m.toNat) % mb = 0)
    (hrun : ∀ t < r, sturmian α (i + t) = sturmian α (i + t + p)) :
    r * den ≤ p := by
  by_cases hr0 : r = 0
  · subst hr0; simp
  have hr1 : 1 ≤ r := by omega
  obtain ⟨c, d, hc1, hdc, hp_cd, hm_cd, hδ_cd⟩ :=
    level_basis_decomp ha hk hηk hηk1 hηlt hp hδ_hi
  by_cases hc_big : den * (ak1 + 2) ≤ c
  · exact level_big_c_bound hα0 hα2 hirr ha hk hden hak1 hc1 hc_big hr1
      hηk hηk_next hηlt_next hp_cd hδ_lo hδ_cd hδα hrun
  · push Not at hc_big
    have hpa_eq : convP a k % ma = pa := congrArg Prod.fst hmod
    have hpb_eq : (convQ a k - convP a k) % mb = pb := congrArg (fun x => x.2.1) hmod
    have hpa1_eq : convPPrev a k % ma = pa1 := congrArg (fun x => x.2.2.1) hmod
    have hpb1_eq : (convQPrev a k - convPPrev a k) % mb = pb1 := congrArg (fun x => x.2.2.2) hmod
    have hm_nat : m.toNat = c * convP a k + d * convPPrev a k := by
      have : (m.toNat : ℤ) = ((c * convP a k + d * convPPrev a k : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hm0]; push_cast; exact hm_cd
      exact_mod_cast this
    have hp_le_q := convP_le_convQ (ha 1 (le_refl 1)) k
    have hpm_nat : p - m.toNat = c * (convQ a k - convP a k) + d * (convQPrev a k - convPPrev a k) := by
      rw [hp_cd, hm_nat]
      have h1 : c * (convQ a k - convP a k) = c * convQ a k - c * convP a k :=
        Nat.mul_sub_left_distrib _ _ _
      have h2 : d * (convQPrev a k - convPPrev a k) = d * convQPrev a k - d * convPPrev a k :=
        Nat.mul_sub_left_distrib _ _ _
      have h3 : c * convP a k ≤ c * convQ a k := Nat.mul_le_mul_left c hp_le_q.1
      have h4 : d * convPPrev a k ≤ d * convQPrev a k := Nat.mul_le_mul_left d (hp_le_q.2 hk)
      omega
    have hc_ma : (c * pa + d * pa1) % ma = 0 := by
      rw [← hpa_eq, ← hpa1_eq]
      have hrew : (c * (convP a k % ma) + d * (convPPrev a k % ma)) % ma =
          (c * convP a k + d * convPPrev a k) % ma := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd _ (dvd_refl ma), ← Nat.mul_mod,
          Nat.mul_mod d, Nat.mod_mod_of_dvd _ (dvd_refl ma), ← Nat.mul_mod, ← Nat.add_mod]
      rw [hrew, ← hm_nat]
      exact hma
    have hc_mb : (c * pb + d * pb1) % mb = 0 := by
      rw [← hpb_eq, ← hpb1_eq]
      have hrew : (c * ((convQ a k - convP a k) % mb) + d * ((convQPrev a k - convPPrev a k) % mb)) % mb =
          (c * (convQ a k - convP a k) + d * (convQPrev a k - convPPrev a k)) % mb := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd _ (dvd_refl mb), ← Nat.mul_mod,
          Nat.mul_mod d, Nat.mod_mod_of_dvd _ (dvd_refl mb), ← Nat.mul_mod, ← Nat.add_mod]
      rw [hrew, ← hpm_nat]
      exact hmb
    unfold checkLevelClass at hchk
    simp only [List.all_eq_true, List.mem_range] at hchk
    have hc_ok := hchk c hc_big
    have hc_ne0 : (c == 0) = false := by rw [beq_eq_false_iff_ne]; omega
    simp only [hc_ne0, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, List.mem_range] at hc_ok
    exact checkLevelPair_sound hα0 hα2 ha hk hprec hak1 hc1 hr1
      hηk hηk1 hηk_next hηlt_next hθ_lo hθ_hi hmode hc_ma hc_mb
      (hc_ok d (by omega)) hp_cd hδ_lo hδ_hi hδ_cd hδα hrun

/-! ## Section 4: Pure-Kernel Cut-Partition & Small-Period Checker -/

/-- Check that `m₁ - k₁ * α < m₂ - k₂ * α` holds unconditionally for all `α ∈ (loA / prec, hiA / prec)`. -/
def checkCutStep (loA hiA prec : ℕ) (p1 p2 : ℕ × ℤ) : Bool :=
  let (k1, m1) := p1
  let (k2, m2) := p2
  let dk : ℤ := (k2 : ℤ) - (k1 : ℤ)
  let dm : ℤ := m2 - m1
  if 0 ≤ dk then
    decide (dk * (hiA : ℤ) ≤ dm * (prec : ℤ) - 1)
  else
    decide (dk * (loA : ℤ) ≤ dm * (prec : ℤ) - 1)

/-- Check pairwise strict increase along a list of cuts. -/
def checkCutsIncreasing (loA hiA prec : ℕ) : List (ℕ × ℤ) → Bool
  | [] => true
  | [_] => true
  | p1 :: p2 :: rest => checkCutStep loA hiA prec p1 p2 && checkCutsIncreasing loA hiA prec (p2 :: rest)

/-- Find the index of `(k, _)` in `cuts` (returns `0` if absent; validity checked by `checkCutPartition`). -/
def findCutPos (cuts : List (ℕ × ℤ)) (k : ℕ) : ℕ :=
  go 0 cuts
where
  go (idx : ℕ) : List (ℕ × ℤ) → ℕ
    | [] => idx
    | (k', _) :: rest => if k' == k then idx else go (idx + 1) rest

/-- Pure-kernel checker certifying that `cuts` is the exact sorted cut partition of `[0, 1)` for
`L` steps of `sturmian α`: `cuts[0] = (0, 0)`, `cuts[L+1] = (0, 1)`, every `k ∈ {0, ..., L}` appears
in `cuts[0..L]`, and `val t = m_t - k_t * α` is strictly increasing. -/
def checkCutPartition (L loA hiA prec : ℕ) (cuts : List (ℕ × ℤ)) : Bool :=
  decide (cuts.length = L + 2) &&
  (cuts.head? == some (0, 0)) &&
  (cuts.getLast? == some (0, 1)) &&
  checkCutsIncreasing loA hiA prec cuts &&
  (List.range (L + 1)).all fun k =>
    let idx := findCutPos cuts k
    decide (idx < L + 1) &&
    match cuts[idx]? with
    | some (k', _) => k' == k
    | none => false

/-- The `t`-th Sturmian factor of length `L` induced by a cut partition (`t ∈ {0, ..., L}`). -/
def sturmianFactorFromCut (cuts : List (ℕ × ℤ)) (L t : ℕ) : List Bool :=
  let pos := fun k => findCutPos cuts k
  (List.range L).map fun j =>
    let p1 := pos (j + 1)
    let p0 := pos j
    if p1 < p0 then decide (p1 ≤ t ∧ t < p0)
    else decide (p1 ≤ t ∨ t < p0)

/-- Soundness of `checkCutStep`. -/
theorem checkCutStep_sound {α : ℝ} {loA hiA prec : ℕ} (hprec : 0 < prec)
    (hlo : (loA : ℝ) / (prec : ℝ) < α) (hhi : α < (hiA : ℝ) / (prec : ℝ))
    {p1 p2 : ℕ × ℤ} (hchk : checkCutStep loA hiA prec p1 p2 = true) :
    (p1.2 : ℝ) - (p1.1 : ℝ) * α < (p2.2 : ℝ) - (p2.1 : ℝ) * α := by
  rcases p1 with ⟨k1, m1⟩
  rcases p2 with ⟨k2, m2⟩
  unfold checkCutStep at hchk
  have hprecR : (0 : ℝ) < (prec : ℝ) := Nat.cast_pos.mpr hprec
  have hlo' : (loA : ℝ) < (prec : ℝ) * α := by
    have := (div_lt_iff₀ hprecR).mp hlo; linarith
  have hhi' : (prec : ℝ) * α < (hiA : ℝ) := by
    have := (lt_div_iff₀ hprecR).mp hhi; linarith
  by_cases hdk : (0 : ℤ) ≤ (k2 : ℤ) - (k1 : ℤ)
  · simp only [hdk, ↓reduceIte, decide_eq_true_eq] at hchk
    have hR : (((k2 : ℤ) - (k1 : ℤ)) : ℝ) * (hiA : ℝ) ≤ ((m2 - m1 : ℤ) : ℝ) * (prec : ℝ) - 1 := by
      exact_mod_cast hchk
    have hdkR : (0 : ℝ) ≤ (k2 : ℝ) - (k1 : ℝ) := by exact_mod_cast hdk
    push_cast at hR
    have h1 : ((k2 : ℝ) - (k1 : ℝ)) * ((prec : ℝ) * α) ≤ ((k2 : ℝ) - (k1 : ℝ)) * (hiA : ℝ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hhi') hdkR
    have h2 : (prec : ℝ) * (((k2 : ℝ) - (k1 : ℝ)) * α) < (prec : ℝ) * ((m2 : ℝ) - (m1 : ℝ)) := by
      linarith
    have h3 := lt_of_mul_lt_mul_left h2 (le_of_lt hprecR)
    linarith
  · simp only [hdk, ↓reduceIte, decide_eq_true_eq] at hchk
    have hR : (((k2 : ℤ) - (k1 : ℤ)) : ℝ) * (loA : ℝ) ≤ ((m2 - m1 : ℤ) : ℝ) * (prec : ℝ) - 1 := by
      exact_mod_cast hchk
    have hdkR : (k2 : ℝ) - (k1 : ℝ) ≤ 0 := by
      have : (k2 : ℤ) - (k1 : ℤ) ≤ 0 := by omega
      exact_mod_cast this
    push_cast at hR
    have h1 : ((k2 : ℝ) - (k1 : ℝ)) * ((prec : ℝ) * α) ≤ ((k2 : ℝ) - (k1 : ℝ)) * (loA : ℝ) :=
      mul_le_mul_of_nonpos_left (le_of_lt hlo') hdkR
    have h2 : (prec : ℝ) * (((k2 : ℝ) - (k1 : ℝ)) * α) < (prec : ℝ) * ((m2 : ℝ) - (m1 : ℝ)) := by
      linarith
    have h3 := lt_of_mul_lt_mul_left h2 (le_of_lt hprecR)
    linarith

/-- Soundness of `checkCutsIncreasing`: consecutive entries are strictly increasing in `m - k α`. -/
theorem checkCutsIncreasing_step {α : ℝ} {loA hiA prec : ℕ} (hprec : 0 < prec)
    (hlo : (loA : ℝ) / (prec : ℝ) < α) (hhi : α < (hiA : ℝ) / (prec : ℝ))
    {cuts : List (ℕ × ℤ)} (hchk : checkCutsIncreasing loA hiA prec cuts = true) :
    ∀ t (ht : t + 1 < cuts.length),
      (cuts[t].2 : ℝ) - (cuts[t].1 : ℝ) * α < (cuts[t + 1].2 : ℝ) - (cuts[t + 1].1 : ℝ) * α := by
  induction cuts with
  | nil => intro t ht; simp at ht
  | cons p1 rest ih =>
    cases rest with
    | nil => intro t ht; simp at ht
    | cons p2 tail =>
      simp only [checkCutsIncreasing, Bool.and_eq_true] at hchk
      intro t ht
      cases t with
      | zero => exact checkCutStep_sound hprec hlo hhi hchk.1
      | succ t =>
        simp only [List.getElem_cons_succ]
        exact ih hchk.2 t (by simp at ht ⊢; omega)

/-- Strict monotonicity of `val t = cuts[t].2 - cuts[t].1 * α` from consecutive strict increase. -/
theorem cutVal_strictMono {α : ℝ} {loA hiA prec : ℕ} (hprec : 0 < prec)
    (hlo : (loA : ℝ) / (prec : ℝ) < α) (hhi : α < (hiA : ℝ) / (prec : ℝ))
    {cuts : List (ℕ × ℤ)} (hchk : checkCutsIncreasing loA hiA prec cuts = true)
    {s t : ℕ} (hst : s < t) (ht : t < cuts.length) :
    (cuts[s].2 : ℝ) - (cuts[s].1 : ℝ) * α < (cuts[t].2 : ℝ) - (cuts[t].1 : ℝ) * α := by
  have hstep := checkCutsIncreasing_step hprec hlo hhi hchk
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases heq : s = t
    · subst heq; exact hstep s ht
    · exact lt_trans (ih (by omega) (by omega)) (hstep t ht)

/-- **Soundness of `checkCutPartition`**: every length-`L` factor of `sturmian α` occurs in
`sturmianFactorFromCut cuts L t` for some `t < L + 1`. -/
theorem sturmian_factor_mem_cutWords {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {L loA hiA prec : ℕ} (hprec : 0 < prec)
    (hlo : (loA : ℝ) / (prec : ℝ) < α) (hhi : α < (hiA : ℝ) / (prec : ℝ))
    {cuts : List (ℕ × ℤ)} (hchk : checkCutPartition L loA hiA prec cuts = true) (i : ℕ) :
    ∃ t < L + 1, ∀ j (hj : j < L),
      sturmian α (i + j) = (sturmianFactorFromCut cuts L t)[j]'(by simp [sturmianFactorFromCut, hj]) := by
  unfold checkCutPartition at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hlen, hhead⟩, hlast⟩, hinc⟩, hall⟩
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hall
  let val : ℕ → ℝ := fun idx =>
    match cuts[idx]? with
    | some (k, m) => (m : ℝ) - (k : ℝ) * α
    | none => 0
  have hval_eq : ∀ idx (hidx : idx < cuts.length),
      val idx = (cuts[idx].2 : ℝ) - (cuts[idx].1 : ℝ) * α := by
    intro idx hidx
    simp only [val, List.getElem?_eq_getElem hidx]
  have hval_mono : ∀ s t, s < t → t < L + 2 → val s < val t := by
    intro s t hst ht
    rw [hval_eq s (by omega), hval_eq t (by omega)]
    exact cutVal_strictMono hprec hlo hhi hinc hst (by omega)
  have hval_le : ∀ s t, s ≤ t → t < L + 2 → val s ≤ val t := by
    intro s t hst ht
    rcases eq_or_lt_of_le hst with rfl | hlt
    · exact le_refl _
    · exact le_of_lt (hval_mono s t hlt ht)
  have hval0 : val 0 = 0 := by
    cases h : cuts with
    | nil => simp [h] at hlen
    | cons p rest =>
      rw [h] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      simp [val, h]
  have hvalLast : val (L + 1) = 1 := by
    have hidx : L + 1 < cuts.length := by omega
    have hgl : cuts[L + 1]? = cuts.getLast? := by
      rw [List.getLast?_eq_getElem?, hlen]; simp
    dsimp only [val]
    rw [hgl, hlast]
    norm_num
  -- Locate x = Int.fract ((i + 1) * α) in [val t, val (t + 1)).
  set x := Int.fract (((i + 1 : ℕ) : ℝ) * α)
  have hx0 : 0 ≤ x := Int.fract_nonneg _
  have hx1 : x < 1 := Int.fract_lt_one _
  have hex_t : ∃ t < L + 1, val t ≤ x ∧ x < val (t + 1) := by
    have hgt : ∃ s : ℕ, s ≤ L + 1 ∧ x < val s := ⟨L + 1, le_refl _, by rw [hvalLast]; exact hx1⟩
    classical
    set s := Nat.find hgt
    have hs : s ≤ L + 1 ∧ x < val s := Nat.find_spec hgt
    have hs_pos : 1 ≤ s := by
      by_contra h0
      have hs0 : s = 0 := by omega
      rw [hs0, hval0] at hs
      linarith
    have hprev : val (s - 1) ≤ x := by
      have hnot := Nat.find_min hgt (show s - 1 < s by omega)
      push Not at hnot
      exact hnot (by omega)
    refine ⟨s - 1, by omega, hprev, ?_⟩
    have : s - 1 + 1 = s := by omega
    rw [this]; exact hs.2
  obtain ⟨t, htL, htx_lo, htx_hi⟩ := hex_t
  refine ⟨t, htL, ?_⟩
  intro j hj
  simp only [sturmianFactorFromCut, List.getElem_map, List.getElem_range]
  -- Extract cut specs for k = j and k = j + 1.
  have hpos_spec : ∀ k < L + 1,
      ∃ hidx : findCutPos cuts k < L + 1, (cuts[findCutPos cuts k]'(by omega)).1 = k := by
    intro k hk
    have h := hall k hk
    have hidx : findCutPos cuts k < L + 1 := h.1
    have hmatch := h.2
    rw [List.getElem?_eq_getElem (by omega : findCutPos cuts k < cuts.length)] at hmatch
    simp only [beq_iff_eq] at hmatch
    exact ⟨hidx, hmatch⟩
  let p0 := findCutPos cuts j
  let p1 := findCutPos cuts (j + 1)
  obtain ⟨hp0_lt, hp0_k⟩ := hpos_spec j (by omega)
  obtain ⟨hp1_lt, hp1_k⟩ := hpos_spec (j + 1) (by omega)
  have hp0_val : val p0 = ((cuts[p0]'(by omega)).2 : ℝ) - (j : ℝ) * α := by
    rw [hval_eq p0 (by omega), hp0_k]
  have hp1_val : val p1 = ((cuts[p1]'(by omega)).2 : ℝ) - ((j + 1 : ℕ) : ℝ) * α := by
    rw [hval_eq p1 (by omega), hp1_k]
  set m0 : ℤ := (cuts[p0]'(by omega)).2
  set m1 : ℤ := (cuts[p1]'(by omega)).2
  have hv0_ge0 : 0 ≤ val p0 := by rw [← hval0]; exact hval_le 0 p0 (Nat.zero_le _) (by omega)
  have hv0_lt1 : val p0 < 1 := by rw [← hvalLast]; exact hval_mono p0 (L + 1) hp0_lt (by omega)
  have hv1_ge0 : 0 ≤ val p1 := by rw [← hval0]; exact hval_le 0 p1 (Nat.zero_le _) (by omega)
  have hv1_lt1 : val p1 < 1 := by rw [← hvalLast]; exact hval_mono p1 (L + 1) hp1_lt (by omega)
  -- p1 ≠ 0 because cuts[0].1 = 0 while cuts[p1].1 = j + 1 ≠ 0.
  have hp1_pos : 0 < p1 := by
    by_contra h0
    have hp10 : p1 = 0 := by omega
    have hc0 : cuts[0]? = some (0, 0) := by rw [← List.head?_eq_getElem?]; exact hhead
    rw [List.getElem?_eq_getElem (by omega : 0 < cuts.length), Option.some.injEq] at hc0
    have hzero : (cuts[p1]'(by omega)).1 = 0 := by simp [hp10, hc0]
    rw [hp1_k] at hzero
    omega
  have hv1_pos : 0 < val p1 := by rw [← hval0]; exact hval_mono 0 p1 hp1_pos (by omega)
  -- Relate m1 and m0: val p1 - val p0 = (m1 - m0) - α ∈ (-1, 1) and val p1 ∈ (0, 1).
  have hdiff_m : (m1 : ℝ) - (m0 : ℝ) = val p1 - val p0 + α := by
    have : val p1 = (m1 : ℝ) - ((j : ℝ) + 1) * α := by rw [hp1_val]; push_cast; ring
    have : val p0 = (m0 : ℝ) - (j : ℝ) * α := hp0_val
    linarith
  have hm_cases : (m1 = m0 ∧ val p1 = val p0 - α ∧ p1 < p0) ∨
                  (m1 = m0 + 1 ∧ val p1 = val p0 + 1 - α ∧ p0 < p1) := by
    have hgt : (-1 : ℝ) < (m1 : ℝ) - (m0 : ℝ) := by linarith
    have hlt : (m1 : ℝ) - (m0 : ℝ) < 2 := by linarith
    have hZ1 : -1 < m1 - m0 := by exact_mod_cast hgt
    have hZ2 : m1 - m0 < 2 := by exact_mod_cast hlt
    have h01 : m1 = m0 ∨ m1 = m0 + 1 := by omega
    rcases h01 with heq | heq
    · left
      have hv : val p1 = val p0 - α := by rw [heq] at hdiff_m; linarith
      have hltp : p1 < p0 := by
        by_contra hge
        have : val p0 ≤ val p1 := hval_le p0 p1 (by omega) (by omega)
        linarith
      exact ⟨heq, hv, hltp⟩
    · right
      have hv : val p1 = val p0 + 1 - α := by rw [heq] at hdiff_m; push_cast at hdiff_m; linarith
      have hltp : p0 < p1 := by
        by_contra hge
        have : val p1 ≤ val p0 := hval_le p1 p0 (by omega) (by omega)
        linarith
      exact ⟨heq, hv, hltp⟩
  -- Compute Int.fract ((i + j + 1) * α) from x = Int.fract ((i + 1) * α) and val p0 = m0 - j α.
  set Ki : ℤ := ⌊((i + 1 : ℕ) : ℝ) * α⌋
  have hdecom : ((i + j + 1 : ℕ) : ℝ) * α = ((Ki + m0 : ℤ) : ℝ) + (x - val p0) := by
    have h1 : ((i + 1 : ℕ) : ℝ) * α = (Ki : ℝ) + x := (Int.floor_add_fract _).symm
    have h2 : ((i + j + 1 : ℕ) : ℝ) * α = ((i + 1 : ℕ) : ℝ) * α + (j : ℝ) * α := by
      push_cast; ring
    rw [h2, h1, hp0_val]; push_cast; ring
  have hfract_cases :
      (p0 ≤ t → Int.fract (((i + j + 1 : ℕ) : ℝ) * α) = x - val p0) ∧
      (t < p0 → Int.fract (((i + j + 1 : ℕ) : ℝ) * α) = x - val p0 + 1) := by
    constructor
    · intro hp0t
      have hle : val p0 ≤ x := le_trans (hval_le p0 t hp0t (by omega)) htx_lo
      exact fract_eq_of_int_add (Ki + m0) hdecom (by linarith) (by linarith)
    · intro htp0
      have hlt : x < val p0 := lt_of_lt_of_le htx_hi (hval_le (t + 1) p0 (by omega) (by omega))
      apply fract_eq_of_int_add (Ki + m0 - 1)
      · rw [hdecom]; push_cast; ring
      · linarith
      · linarith
  -- Match both sides as Booleans via Bool.eq_iff_iff.
  apply eq_of_beq
  rw [beq_iff_eq]
  -- Wait: use `apply Bool.eq_iff_iff.mp`? Even simpler: `by_cases` on `sturmian α (i + j) = true`!
  have hiff : sturmian α (i + j) = true ↔
      (if p1 < p0 then decide (p1 ≤ t ∧ t < p0) else decide (p1 ≤ t ∨ t < p0)) = true := by
    rw [sturmian_iff_fract hα1 (i + j)]
    rcases hm_cases with ⟨_, hv, hltp⟩ | ⟨_, hv, hltp⟩
    · simp only [hltp, ↓reduceIte, decide_eq_true_eq]
      constructor
      · intro hge
        by_cases htp0 : t < p0
        · rw [hfract_cases.2 htp0] at hge
          have hv1_le_x : val p1 ≤ x := by linarith
          have hp1_le_t : p1 ≤ t := by
            by_contra hgt
            have : x < val p1 := lt_of_lt_of_le htx_hi (hval_le (t + 1) p1 (by omega) (by omega))
            linarith
          exact ⟨hp1_le_t, htp0⟩
        · rw [hfract_cases.1 (by omega)] at hge
          linarith
      · rintro ⟨hp1t, htp0⟩
        rw [hfract_cases.2 htp0]
        have hv1_le_x : val p1 ≤ x := le_trans (hval_le p1 t hp1t (by omega)) htx_lo
        linarith
    · have hnot : ¬ (p1 < p0) := by omega
      simp only [hnot, ↓reduceIte, decide_eq_true_eq]
      constructor
      · intro hge
        by_cases htp0 : t < p0
        · exact Or.inr htp0
        · left
          rw [hfract_cases.1 (by omega)] at hge
          have hv1_le_x : val p1 ≤ x := by linarith
          by_contra hgt
          have : x < val p1 := lt_of_lt_of_le htx_hi (hval_le (t + 1) p1 (by omega) (by omega))
          linarith
      · rintro (hp1t | htp0)
        · have hp0t : p0 ≤ t := by omega
          rw [hfract_cases.1 hp0t]
          have hv1_le_x : val p1 ≤ x := le_trans (hval_le p1 t hp1t (by omega)) htx_lo
          linarith
        · rw [hfract_cases.2 htp0]
          linarith
  cases hl : sturmian α (i + j) <;> cases hr : (if p1 < p0 then decide (p1 ≤ t ∧ t < p0) else decide (p1 ≤ t ∨ t < p0))
  · rfl
  · exact False.elim (Bool.noConfusion (hl.symm.trans (hiff.mpr hr)))
  · exact False.elim (Bool.noConfusion (hr.symm.trans (hiff.mp hl)))
  · rfl

/-- Colour a finite boolean word `uWord` starting from phases `(pa, pb)` using periodic tables
`yTab` (length `ma`) and `y'Tab` (length `mb`). -/
def colourWord (yTab y'Tab : List ℕ) (ma mb pa pb : ℕ) : List Bool → List ℕ
  | [] => []
  | true :: rest => yTab.getD (pa % ma) 0 :: colourWord yTab y'Tab ma mb ((pa + 1) % ma) pb rest
  | false :: rest => y'Tab.getD (pb % mb) 0 :: colourWord yTab y'Tab ma mb pa ((pb + 1) % mb) rest

/-- Length preservation of `colourWord`. -/
theorem length_colourWord (yTab y'Tab : List ℕ) (ma mb pa pb : ℕ) (u : List Bool) :
    (colourWord yTab y'Tab ma mb pa pb u).length = u.length := by
  induction u generalizing pa pb with
  | nil => rfl
  | cons b rest ih =>
    cases b <;> simp [colourWord, ih]

/-- Elementwise correspondence between `colourWord` and `colour u y y'` on any contiguous factor. -/
theorem getElem_colourWord_eq {d : ℕ} {u : ℕ → Bool} {y y' : ℕ → Fin d}
    {yTab y'Tab : List ℕ} {ma mb : ℕ} (_hma : 0 < ma) (_hmb : 0 < mb)
    (hy : ∀ k : ℕ, (y k).val = yTab.getD (k % ma) 0)
    (hy' : ∀ k : ℕ, (y' k).val = y'Tab.getD (k % mb) 0)
    (i L : ℕ) (uWord : List Bool) (hlen : uWord.length = L)
    (hmatch : ∀ j (hj : j < L), u (i + j) = uWord[j]'(by omega))
    (j : ℕ) (hj : j < L) :
    (colour u y y' (i + j)).val =
      (colourWord yTab y'Tab ma mb (countTrue u i % ma) (countFalse u i % mb) uWord)[j]'(by
        rw [length_colourWord, hlen]; exact hj) := by
  -- Prove a generalized version for arbitrary starting phases congruent mod ma, mb.
  have hgen : ∀ (L i pa pb : ℕ) (uWord : List Bool) (hlen : uWord.length = L),
      pa % ma = countTrue u i % ma →
      pb % mb = countFalse u i % mb →
      (∀ j (hj : j < L), u (i + j) = uWord[j]'(by omega)) →
      ∀ j (hj : j < L),
        (colour u y y' (i + j)).val =
          (colourWord yTab y'Tab ma mb pa pb uWord)[j]'(by rw [length_colourWord]; omega) := by
    intro L
    induction L with
    | zero => intro _ _ _ _ _ _ _ _ j hj; omega
    | succ L ih =>
      intro i pa pb uWord hlen hpa hpb hm j hj
      cases uWord with
      | nil => simp at hlen
      | cons b rest =>
        have hrest_len : rest.length = L := by simp at hlen; omega
        have hb0 : u i = b := by simpa using hm 0 (Nat.zero_lt_succ L)
        cases j with
        | zero =>
          simp only [add_zero, colour, hb0]
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, colourWord, List.getElem_cons_zero]
            rw [hy', hpb]
          · simp only [↓reduceIte, colourWord, List.getElem_cons_zero]
            rw [hy, hpa]
        | succ j =>
          have hshift : i + (j + 1) = (i + 1) + j := by omega
          rw [hshift]
          have hm_rest : ∀ k (hk : k < L), u ((i + 1) + k) = rest[k]'(by omega) := by
            intro k hk
            have := hm (k + 1) (Nat.succ_lt_succ hk)
            have heq : i + (k + 1) = (i + 1) + k := by omega
            rwa [heq] at this
          cases b
          · simp only [colourWord, List.getElem_cons_succ]
            exact ih (i + 1) pa ((pb + 1) % mb) rest hrest_len
              (by rw [countTrue_succ, hb0]; simpa using hpa)
              (by rw [countFalse_succ, hb0]; simp only [↓reduceIte]
                  rw [Nat.mod_mod_of_dvd _ (dvd_refl mb), Nat.add_mod, hpb, ← Nat.add_mod])
              hm_rest j (by omega)
          · simp only [colourWord, List.getElem_cons_succ]
            exact ih (i + 1) ((pa + 1) % ma) pb rest hrest_len
              (by rw [countTrue_succ, hb0]; simp only [↓reduceIte]
                  rw [Nat.mod_mod_of_dvd _ (dvd_refl ma), Nat.add_mod, hpa, ← Nat.add_mod])
              (by rw [countFalse_succ, hb0]; simpa using hpb)
              hm_rest j (by omega)
  exact hgen L i (countTrue u i % ma) (countFalse u i % mb) uWord hlen
    (Nat.mod_mod_of_dvd _ (dvd_refl ma)) (Nat.mod_mod_of_dvd _ (dvd_refl mb)) hmatch j hj

/-- Test whether `w` avoids a match of length `r0` at period `p` starting at position `0`. -/
def avoidsMatchAt {α : Type*} [BEq α] (w : List α) (p r0 : ℕ) : Bool :=
  (List.range r0).any fun k => !(w[k]? == w[p + k]?)

/-- Pure-kernel small-period checker: verifies that no factor of `sturmian α` of length `L`
at any phase `(pa, pb) ∈ Fin ma × Fin mb` has a match run of length `r0 = p / den + 1` at any
period `1 ≤ p < P_small`. -/
def checkSmallPeriods (P_small den ma mb : ℕ) (yTab y'Tab : List ℕ)
    (L : ℕ) (cuts : List (ℕ × ℤ)) : Bool :=
  (List.range (L + 1)).all fun t =>
    let uWord := sturmianFactorFromCut cuts L t
    (List.range P_small).all fun p =>
      if p == 0 then true
      else
        let r0 := p / den + 1
        if avoidsMatchAt uWord p r0 then true
        else
          (List.range ma).all fun pa =>
            (List.range mb).all fun pb =>
              avoidsMatchAt (colourWord yTab y'Tab ma mb pa pb uWord) p r0

/-- **Soundness of `checkSmallPeriods`**: if `checkCutPartition` and `checkSmallPeriods` both
return `true`, then every period `1 ≤ p < P_small` satisfies `r * den ≤ p` for every match run
of `colour (sturmian α) y y'`. -/
theorem checkSmallPeriods_sound {d : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y y' : ℕ → Fin d} {yTab y'Tab : List ℕ} {P_small den ma mb L loA hiA prec : ℕ}
    (hden : 0 < den) (hma : 0 < ma) (hmb : 0 < mb) (hprec : 0 < prec)
    (hL_ge : ∀ p, 1 ≤ p → p < P_small → p + (p / den + 1) ≤ L)
    (hdisj : ∀ a b, y a ≠ y' b)
    (hy : ∀ k : ℕ, (y k).val = yTab.getD (k % ma) 0)
    (hy' : ∀ k : ℕ, (y' k).val = y'Tab.getD (k % mb) 0)
    (hlo : (loA : ℝ) / (prec : ℝ) < α) (hhi : α < (hiA : ℝ) / (prec : ℝ))
    {cuts : List (ℕ × ℤ)}
    (hcut : checkCutPartition L loA hiA prec cuts = true)
    (hsmall : checkSmallPeriods P_small den ma mb yTab y'Tab L cuts = true)
    {i p r : ℕ} (hp0 : 0 < p) (hp_lt : p < P_small)
    (hrun : ∀ k < r, colour (sturmian α) y y' (i + k) = colour (sturmian α) y y' (i + k + p)) :
    r * den ≤ p := by
  by_contra hgt
  push Not at hgt
  let r0 := p / den + 1
  have hr0_le : r0 ≤ r := by
    have hdiv : den * (p / den) + p % den = p := Nat.div_add_mod p den
    have hrem : p % den < den := Nat.mod_lt p hden
    have hlt : p / den < r := by
      by_contra hge
      push Not at hge
      have hm : r * den ≤ den * (p / den) := by
        calc r * den ≤ (p / den) * den := Nat.mul_le_mul_right den hge
          _ = den * (p / den) := mul_comm _ _
      omega
    omega
  have hpr0_le : p + r0 ≤ L := hL_ge p hp0 hp_lt
  obtain ⟨t, htL, hu_eq⟩ := sturmian_factor_mem_cutWords hα0 hα1 hprec hlo hhi hcut i
  let uWord := sturmianFactorFromCut cuts L t
  have huWord_len : uWord.length = L := by simp [uWord, sturmianFactorFromCut]
  unfold checkSmallPeriods at hsmall
  simp only [List.all_eq_true, List.mem_range] at hsmall
  have hp_ok := hsmall t htL p hp_lt
  have hp_ne0 : (p == 0) = false := by rw [beq_eq_false_iff_ne]; omega
  simp only [hp_ne0, Bool.false_eq_true, ↓reduceIte] at hp_ok
  -- First show uWord matches at distance p for r0 steps, so avoidsMatchAt uWord p r0 = false.
  have hu_match : avoidsMatchAt uWord p r0 = false := by
    unfold avoidsMatchAt
    rw [List.any_eq_false]
    intro k hk
    simp only [List.mem_range] at hk
    have hkL : k < L := by omega
    have hpkL : p + k < L := by omega
    have h1 := hu_eq k hkL
    have h2 := hu_eq (p + k) hpkL
    have hcol := hrun k (lt_of_lt_of_le hk hr0_le)
    have hst := (colour_match_implies hdisj hcol).1
    have hidx : i + k + p = i + (p + k) := by omega
    rw [hidx] at hst
    have heq : uWord[k]'(by omega) = uWord[p + k]'(by omega) := by
      rw [← h1, ← h2]; exact hst
    simp [List.getElem?_eq_getElem (by omega : k < uWord.length),
      List.getElem?_eq_getElem (by omega : p + k < uWord.length), heq]
  have hp_ok' : ∀ pa < ma, ∀ pb < mb,
      avoidsMatchAt (colourWord yTab y'Tab ma mb pa pb uWord) p r0 = true := by
    change (if avoidsMatchAt uWord p r0 then true
      else (List.range ma).all fun pa => (List.range mb).all fun pb =>
        avoidsMatchAt (colourWord yTab y'Tab ma mb pa pb uWord) p r0) = true at hp_ok
    rw [hu_match] at hp_ok
    simp only [Bool.false_eq_true, ↓reduceIte, List.all_eq_true, List.mem_range] at hp_ok
    exact hp_ok
  let pa := countTrue (sturmian α) i % ma
  let pb := countFalse (sturmian α) i % mb
  have hcol_avoid := hp_ok' pa (Nat.mod_lt _ hma) pb (Nat.mod_lt _ hmb)
  unfold avoidsMatchAt at hcol_avoid
  rw [List.any_eq_true] at hcol_avoid
  obtain ⟨k, hk, hneq⟩ := hcol_avoid
  simp only [List.mem_range, Bool.not_eq_true', beq_eq_false_iff_ne] at hk hneq
  let cWord := colourWord yTab y'Tab ma mb pa pb uWord
  have hcWord_len : cWord.length = L := by rw [length_colourWord, huWord_len]
  have hkL : k < L := by omega
  have hpkL : p + k < L := by omega
  have h1 := getElem_colourWord_eq hma hmb hy hy' i L uWord huWord_len hu_eq k hkL
  have h2 := getElem_colourWord_eq hma hmb hy hy' i L uWord huWord_len hu_eq (p + k) hpkL
  have hcol := hrun k (lt_of_lt_of_le hk hr0_le)
  have hidx : i + k + p = i + (p + k) := by omega
  rw [hidx] at hcol
  have hval_eq : cWord[k]'(by omega) = cWord[p + k]'(by omega) := by
    rw [← h1, ← h2, hcol]
  change cWord[k]? ≠ cWord[p + k]? at hneq
  rw [List.getElem?_eq_getElem (by omega : k < cWord.length),
    List.getElem?_eq_getElem (by omega : p + k < cWord.length)] at hneq
  exact hneq (congrArg some hval_eq)

end BalancedRepetitionThreshold
