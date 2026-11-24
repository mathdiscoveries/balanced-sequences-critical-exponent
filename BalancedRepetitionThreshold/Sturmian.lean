module

public import BalancedRepetitionThreshold.Defs

import Mathlib.Tactic

/-!
# Mechanical Sturmian Sequences, Colouring, and Direct Universal Balance Proof

This module defines:
- `sturmian α n : Bool` (`⌊(n + 2) α⌋ - ⌊(n + 1) α⌋ = 1`),
- `countTrue`, `countFalse`, and `colour u y y'`,
- `HasConstantGap` for periodic constant-gap letter occurrences.

And proves unconditionally (with zero recurrence or Hubert-theorem assumption):
- Telescoping count identity for `sturmian α`,
- 1-balance of `sturmian α`,
- Fractional-part characterization `sturmian α n = true ↔ 1 - α ≤ Int.fract ((n + 1) * α)`,
- Direct 1-balance of `colour (sturmian α) y y'` whenever `y` and `y'` have disjoint alphabets
  and every letter occurs with constant gap in its colour sequence,
- Surjectivity of `countTrue` and `countFalse` onto `ℕ` (yielding `UsesAllLetters` for any
  periodic colouring covering `Fin d`).
-/

@[expose] public section

namespace BalancedRepetitionThreshold

/-- Mechanical Sturmian sequence of rare-letter frequency `α ∈ (0, 1)`:
`true` represents the rare letter `a`, `false` represents the frequent letter `b`. -/
noncomputable def sturmian (α : ℝ) (n : ℕ) : Bool :=
  decide (⌊((n + 2 : ℕ) : ℝ) * α⌋ - ⌊((n + 1 : ℕ) : ℝ) * α⌋ = 1)

/-- Number of `true` (`a`) entries in `u` strictly before position `n`. -/
def countTrue (u : ℕ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun j => u j = true)).card

/-- Number of `false` (`b`) entries in `u` strictly before position `n`. -/
def countFalse (u : ℕ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun j => u j = false)).card

/-- Colouring `colour(u, y, y')`: replaces the `k`-th `true` in `u` by `y k` and the `k`-th
`false` in `u` by `y' k`. -/
def colour {d : ℕ} (u : ℕ → Bool) (y y' : ℕ → Fin d) (n : ℕ) : Fin d :=
  if u n then y (countTrue u n) else y' (countFalse u n)

/-- Helper: for any boolean predicate on `Finset.range n`, `true`-count plus `false`-count is `n`. -/
theorem card_filter_bool_add (f : ℕ → Bool) (n : ℕ) :
    ((Finset.range n).filter (fun j => f j = true)).card +
    ((Finset.range n).filter (fun j => f j = false)).card = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    have h1 : n ∉ (Finset.range n).filter (fun j => f j = true) := by simp
    have h2 : n ∉ (Finset.range n).filter (fun j => f j = false) := by simp
    cases hf : f n
    · simp only [Bool.false_eq_true, ↓reduceIte, Finset.card_insert_of_notMem h2]
      omega
    · simp only [↓reduceIte, Bool.true_eq_false, Finset.card_insert_of_notMem h1]
      omega

/-- `countTrue u n + countFalse u n = n`. -/
theorem countTrue_add_countFalse (u : ℕ → Bool) (n : ℕ) :
    countTrue u n + countFalse u n = n :=
  card_filter_bool_add u n

/-- Step recurrence for `countTrue`. -/
theorem countTrue_succ (u : ℕ → Bool) (n : ℕ) :
    countTrue u (n + 1) = countTrue u n + (if u n = true then 1 else 0) := by
  unfold countTrue
  rw [Finset.range_add_one, Finset.filter_insert]
  have hnotmem : n ∉ (Finset.range n).filter (fun j => u j = true) := by simp
  by_cases h : u n = true
  · simp [h, Finset.card_insert_of_notMem hnotmem]
  · simp [h]

/-- Step recurrence for `countFalse`. -/
theorem countFalse_succ (u : ℕ → Bool) (n : ℕ) :
    countFalse u (n + 1) = countFalse u n + (if u n = false then 1 else 0) := by
  unfold countFalse
  rw [Finset.range_add_one, Finset.filter_insert]
  have hnotmem : n ∉ (Finset.range n).filter (fun j => u j = false) := by simp
  by_cases h : u n = false
  · simp [h, Finset.card_insert_of_notMem hnotmem]
  · simp [h]

/-- Monotonicity of `countTrue`. -/
theorem countTrue_mono (u : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    countTrue u m ≤ countTrue u n := by
  unfold countTrue
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

/-- Monotonicity of `countFalse`. -/
theorem countFalse_mono (u : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    countFalse u m ≤ countFalse u n := by
  unfold countFalse
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

/-- Interval count of `true` equals `countTrue u (i + L) - countTrue u i`. -/
theorem countTrue_interval (u : ℕ → Bool) (i L : ℕ) :
    ((Finset.range L).filter (fun j => u (i + j) = true)).card + countTrue u i =
      countTrue u (i + L) := by
  induction L with
  | zero =>
    simp
  | succ L ih =>
    rw [Finset.range_add_one, Finset.filter_insert, ← Nat.add_assoc, countTrue_succ]
    have hnotmem : L ∉ (Finset.range L).filter (fun j => u (i + j) = true) := by simp
    by_cases h : u (i + L) = true
    · simp only [h, ↓reduceIte, Finset.card_insert_of_notMem hnotmem]
      omega
    · simp [h, ih]

/-- Interval count of `false` equals `countFalse u (i + L) - countFalse u i`. -/
theorem countFalse_interval (u : ℕ → Bool) (i L : ℕ) :
    ((Finset.range L).filter (fun j => u (i + j) = false)).card + countFalse u i =
      countFalse u (i + L) := by
  induction L with
  | zero =>
    simp
  | succ L ih =>
    rw [Finset.range_add_one, Finset.filter_insert, ← Nat.add_assoc, countFalse_succ]
    have hnotmem : L ∉ (Finset.range L).filter (fun j => u (i + j) = false) := by simp
    by_cases h : u (i + L) = false
    · simp only [h, ↓reduceIte, Finset.card_insert_of_notMem hnotmem]
      omega
    · simp [h, ih]

/-- For `0 < α < 1`, `⌊(n + 2) α⌋ - ⌊(n + 1) α⌋` is either `0` or `1`, and equals the integer
indicator of `sturmian α n`. -/
theorem sturmian_int_indicator {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    (if sturmian α n = true then (1 : ℤ) else 0) =
      ⌊((n + 2 : ℕ) : ℝ) * α⌋ - ⌊((n + 1 : ℕ) : ℝ) * α⌋ := by
  have h1 : ((n + 1 : ℕ) : ℝ) * α ≤ ((n + 2 : ℕ) : ℝ) * α := by
    push_cast; nlinarith
  have h2 : ((n + 2 : ℕ) : ℝ) * α < ((n + 1 : ℕ) : ℝ) * α + 1 := by
    push_cast; nlinarith
  have hlo : ⌊((n + 1 : ℕ) : ℝ) * α⌋ ≤ ⌊((n + 2 : ℕ) : ℝ) * α⌋ :=
    Int.floor_mono h1
  have hhi : ⌊((n + 2 : ℕ) : ℝ) * α⌋ ≤ ⌊((n + 1 : ℕ) : ℝ) * α⌋ + 1 := by
    have : ⌊((n + 2 : ℕ) : ℝ) * α⌋ < ⌊((n + 1 : ℕ) : ℝ) * α⌋ + 2 := by
      rw [Int.floor_lt]
      have hfl : (((⌊((n + 1 : ℕ) : ℝ) * α⌋ : ℤ) : ℝ)) + 1 > ((n + 1 : ℕ) : ℝ) * α :=
        Int.lt_floor_add_one _
      simp only [Int.cast_add, Int.cast_ofNat]
      linarith
    omega
  unfold sturmian
  by_cases heq : ⌊((n + 2 : ℕ) : ℝ) * α⌋ - ⌊((n + 1 : ℕ) : ℝ) * α⌋ = 1
  · simp only [decide_eq_true_eq, heq, ↓reduceIte]
  · simp only [decide_eq_true_eq, heq, ↓reduceIte]
    omega

/-- Exact telescoping formula for `countTrue (sturmian α) n`: equals `⌊(n + 1) α⌋`. -/
theorem sturmian_countTrue_eq_floor {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    (countTrue (sturmian α) n : ℤ) = ⌊((n + 1 : ℕ) : ℝ) * α⌋ := by
  induction n with
  | zero =>
    simp only [countTrue, Finset.range_zero, Finset.filter_empty, Finset.card_empty,
      Nat.cast_zero, zero_add, Nat.cast_one, one_mul]
    exact (Int.floor_eq_zero_iff.mpr ⟨le_of_lt hα0, hα1⟩).symm
  | succ n ih =>
    rw [countTrue_succ, Nat.cast_add]
    have hind := sturmian_int_indicator hα0 hα1 n
    have hcast : ((if sturmian α n = true then 1 else 0 : ℕ) : ℤ) =
        (if sturmian α n = true then (1 : ℤ) else 0) := by
      split_ifs <;> rfl
    rw [hcast, hind, ih]
    ring

/-- Exact telescoping formula for the number of `true` letters in `factor (sturmian α) i L`. -/
theorem sturmian_interval_countTrue_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (i L : ℕ) :
    (((Finset.range L).filter (fun j => sturmian α (i + j) = true)).card : ℤ) =
      ⌊((i + L + 1 : ℕ) : ℝ) * α⌋ - ⌊((i + 1 : ℕ) : ℝ) * α⌋ := by
  have h := countTrue_interval (sturmian α) i L
  have h1 := sturmian_countTrue_eq_floor hα0 hα1 i
  have h2 := sturmian_countTrue_eq_floor hα0 hα1 (i + L)
  omega

/-- Floor super/subadditivity: `⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1`. -/
theorem floor_add_bounds (x y : ℝ) :
    ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ ∧ ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith [Int.floor_le x, Int.floor_le y]
  · have hlt : ⌊x + y⌋ < ⌊x⌋ + ⌊y⌋ + 2 := by
      rw [Int.floor_lt]
      push_cast
      linarith [Int.lt_floor_add_one x, Int.lt_floor_add_one y]
    omega

/-- Every length-`L` factor of `sturmian α` has `true`-count in `{⌊L α⌋, ⌊L α⌋ + 1}`. -/
theorem sturmian_interval_countTrue_bounds {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (i L : ℕ) :
    ⌊(L : ℝ) * α⌋ ≤ (((Finset.range L).filter (fun j => sturmian α (i + j) = true)).card : ℤ) ∧
    (((Finset.range L).filter (fun j => sturmian α (i + j) = true)).card : ℤ) ≤
      ⌊(L : ℝ) * α⌋ + 1 := by
  rw [sturmian_interval_countTrue_eq hα0 hα1 i L]
  have hsum : ((i + L + 1 : ℕ) : ℝ) * α = ((i + 1 : ℕ) : ℝ) * α + (L : ℝ) * α := by
    push_cast; ring
  rw [hsum]
  have hb := floor_add_bounds (((i + 1 : ℕ) : ℝ) * α) ((L : ℝ) * α)
  omega

/-- Every length-`L` factor of `sturmian α` has `false`-count in
`{L - ⌊L α⌋ - 1, L - ⌊L α⌋}`. -/
theorem sturmian_interval_countFalse_bounds {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (i L : ℕ) :
    (L : ℤ) - ⌊(L : ℝ) * α⌋ - 1 ≤
      (((Finset.range L).filter (fun j => sturmian α (i + j) = false)).card : ℤ) ∧
    (((Finset.range L).filter (fun j => sturmian α (i + j) = false)).card : ℤ) ≤
      (L : ℤ) - ⌊(L : ℝ) * α⌋ := by
  have htot := card_filter_bool_add (fun j => sturmian α (i + j)) L
  have hb := sturmian_interval_countTrue_bounds hα0 hα1 i L
  omega

/-- Fractional-part characterization of `sturmian α n`:
`sturmian α n = true ↔ 1 - α ≤ Int.fract ((n + 1) * α)`. -/
theorem sturmian_iff_fract {α : ℝ} (hα1 : α < 1) (n : ℕ) :
    sturmian α n = true ↔ 1 - α ≤ Int.fract (((n + 1 : ℕ) : ℝ) * α) := by
  have hstep : ((n + 2 : ℕ) : ℝ) * α = ((n + 1 : ℕ) : ℝ) * α + α := by
    push_cast; ring
  have hdecom : ((n + 1 : ℕ) : ℝ) * α = ⌊((n + 1 : ℕ) : ℝ) * α⌋ + Int.fract (((n + 1 : ℕ) : ℝ) * α) :=
    (Int.floor_add_fract _).symm
  have hfl : ⌊((n + 2 : ℕ) : ℝ) * α⌋ - ⌊((n + 1 : ℕ) : ℝ) * α⌋ =
      ⌊Int.fract (((n + 1 : ℕ) : ℝ) * α) + α⌋ := by
    have hfl2 : ⌊((n + 2 : ℕ) : ℝ) * α⌋ =
        ⌊((n + 1 : ℕ) : ℝ) * α⌋ + ⌊Int.fract (((n + 1 : ℕ) : ℝ) * α) + α⌋ := by
      conv_lhs => rw [hstep, hdecom, add_assoc]
      exact Int.floor_intCast_add _ _
    omega
  have hf0 : 0 ≤ Int.fract (((n + 1 : ℕ) : ℝ) * α) := Int.fract_nonneg _
  have hf1 : Int.fract (((n + 1 : ℕ) : ℝ) * α) < 1 := Int.fract_lt_one _
  unfold sturmian
  rw [decide_eq_true_eq, hfl]
  constructor
  · intro h
    have hge : (1 : ℝ) ≤ Int.fract (((n + 1 : ℕ) : ℝ) * α) + α := by
      have := Int.floor_le (Int.fract (((n + 1 : ℕ) : ℝ) * α) + α)
      rw [h] at this
      simpa using this
    linarith
  · intro h
    rw [Int.floor_eq_iff]
    constructor
    · simp only [Int.cast_one]; linarith
    · simp only [Int.cast_one]; linarith

/-- Constant-gap property: letter `c` occurs in `seq` precisely at indices congruent to `r (mod g)`. -/
def HasConstantGap {d : ℕ} (seq : ℕ → Fin d) (c : Fin d) (g r : ℕ) : Prop :=
  0 < g ∧ r < g ∧ ∀ m : ℕ, seq m = c ↔ m % g = r

/-- Counting indices congruent to `r (mod g)` in a contiguous block `[s, s + M)` of length `M`:
the count lies in `[M / g, (M + g - 1) / g]`. -/
theorem card_mod_interval_bounds (s M g r : ℕ) (hg : 0 < g) (hr : r < g) :
    M / g ≤ ((Finset.range M).filter (fun t => (s + t) % g = r)).card ∧
    ((Finset.range M).filter (fun t => (s + t) % g = r)).card ≤ (M + g - 1) / g := by
  -- First prove exact count = 1 on any full block of length g.
  have hfull : ∀ base : ℕ,
      ((Finset.range g).filter (fun t => (base + t) % g = r)).card = 1 := by
    intro base
    let t0 : ℕ := (r + g - base % g) % g
    have ht0_lt : t0 < g := Nat.mod_lt _ hg
    have ht0_mod : (base + t0) % g = r := by
      have hbm : base % g < g := Nat.mod_lt _ hg
      have h1 : (base + t0) % g = (base % g + (r + g - base % g)) % g := by
        dsimp only [t0]
        rw [Nat.add_mod_mod, ← Nat.mod_add_mod]
      rw [h1]
      have h2 : base % g + (r + g - base % g) = r + g := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
    have hset : (Finset.range g).filter (fun t => (base + t) % g = r) = {t0} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨ht, hmod⟩
        have hdiff : (base + t) ≡ (base + t0) [MOD g] := by
          change (base + t) % g = (base + t0) % g
          rw [hmod, ht0_mod]
        have hmod_eq : t % g = t0 % g := Nat.ModEq.add_left_cancel' base hdiff
        rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht0_lt] at hmod_eq
        exact hmod_eq
      · rintro rfl
        exact ⟨ht0_lt, ht0_mod⟩
    rw [hset, Finset.card_singleton]
  -- Next prove for any rem < g, count on range rem is ≤ 1.
  have hrem : ∀ base rem : ℕ, rem < g →
      ((Finset.range rem).filter (fun t => (base + t) % g = r)).card ≤ 1 := by
    intro base rem hrg
    calc ((Finset.range rem).filter (fun t => (base + t) % g = r)).card
        ≤ ((Finset.range g).filter (fun t => (base + t) % g = r)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (le_of_lt hrg)))
      _ = 1 := hfull base
  -- Split an interval of length a + b into [base, base + a) and [base + a, base + a + b).
  have hsplit : ∀ base a b : ℕ,
      ((Finset.range (a + b)).filter (fun t => (base + t) % g = r)).card =
      ((Finset.range a).filter (fun t => (base + t) % g = r)).card +
      ((Finset.range b).filter (fun t => (base + a + t) % g = r)).card := by
    intro base a b
    induction b with
    | zero => simp
    | succ b ih =>
      rw [← Nat.add_assoc, Finset.range_add_one, Finset.filter_insert,
        Finset.range_add_one, Finset.filter_insert]
      have hn1 : a + b ∉ (Finset.range (a + b)).filter (fun t => (base + t) % g = r) := by simp
      have hn2 : b ∉ (Finset.range b).filter (fun t => (base + a + t) % g = r) := by simp
      have heq : base + (a + b) = base + a + b := by omega
      rw [heq]
      by_cases h : (base + a + b) % g = r
      · simp only [h, ↓reduceIte, Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2]
        omega
      · simp only [h, ↓reduceIte]
        exact ih
  -- Exact count on g * q consecutive indices is q.
  have hmul : ∀ base q : ℕ,
      ((Finset.range (g * q)).filter (fun t => (base + t) % g = r)).card = q := by
    intro base q
    induction q generalizing base with
    | zero => simp
    | succ q ih =>
      have h1 : g * (q + 1) = g + g * q := by ring
      rw [h1, hsplit base g (g * q), hfull base, ih (base + g)]
      omega
  -- Write M = g * (M / g) + M % g.
  have hdiv : M = g * (M / g) + M % g := (Nat.div_add_mod M g).symm
  have hrem_lt : M % g < g := Nat.mod_lt M hg
  have hcard :
      ((Finset.range M).filter (fun t => (s + t) % g = r)).card =
      M / g + ((Finset.range (M % g)).filter (fun t => (s + g * (M / g) + t) % g = r)).card := by
    conv_lhs => rw [hdiv]
    rw [hsplit s (g * (M / g)) (M % g), hmul s (M / g)]
  rw [hcard]
  constructor
  · omega
  · by_cases hmod0 : M % g = 0
    · simp only [hmod0, Finset.range_zero, Finset.filter_empty, Finset.card_empty, add_zero]
      have h1 : (M + g - 1) / g = M / g := by
        have hzero : (g - 1) / g = 0 := Nat.div_eq_of_lt (by omega)
        have hsum : M + g - 1 = g * (M / g) + (g - 1) := by omega
        rw [hsum, Nat.mul_add_div hg, hzero, add_zero]
      omega
    · have hle1 := hrem (s + g * (M / g)) (M % g) hrem_lt
      have h1 : (M + g - 1) / g = M / g + 1 := by
        have hzero : (M % g - 1) / g = 0 := Nat.div_eq_of_lt (by omega)
        have hstep : g * (M / g + 1) = g * (M / g) + g := by ring
        have hsum : M + g - 1 = g * (M / g + 1) + (M % g - 1) := by omega
        rw [hsum, Nat.mul_add_div hg, hzero, add_zero]
      omega

/-- Diameter-1 lemma for constant-gap counts over consecutive block sizes `M₁, M₂ ∈ {k, k + 1}`. -/
theorem mod_count_diff_le_one {k M₁ M₂ g c₁ c₂ : ℕ} (hg : 0 < g)
    (hM₁ : k ≤ M₁ ∧ M₁ ≤ k + 1) (hM₂ : k ≤ M₂ ∧ M₂ ≤ k + 1)
    (hc₁ : M₁ / g ≤ c₁ ∧ c₁ ≤ (M₁ + g - 1) / g)
    (hc₂ : M₂ / g ≤ c₂ ∧ c₂ ≤ (M₂ + g - 1) / g) :
    |(c₁ : ℤ) - (c₂ : ℤ)| ≤ 1 := by
  -- Show (k + g) / g = k / g + 1, so both c₁ and c₂ lie in [k / g, k / g + 1].
  have hdiv : g * (k / g) + k % g = k := Nat.div_add_mod k g
  have hrem_lt : k % g < g := Nat.mod_lt k hg
  have hstep : g * (k / g + 1) = g * (k / g) + g := by ring
  have hhi_eq : (k + g) / g = k / g + 1 := by
    have hzero : (k % g) / g = 0 := Nat.div_eq_of_lt hrem_lt
    have hsum : k + g = g * (k / g + 1) + k % g := by omega
    rw [hsum, Nat.mul_add_div hg, hzero, add_zero]
  have hb1 : k / g ≤ c₁ ∧ c₁ ≤ k / g + 1 := by
    have hlo : k / g ≤ M₁ / g := Nat.div_le_div_right hM₁.1
    have hhi : (M₁ + g - 1) / g ≤ (k + g) / g := Nat.div_le_div_right (by omega)
    omega
  have hb2 : k / g ≤ c₂ ∧ c₂ ≤ k / g + 1 := by
    have hlo : k / g ≤ M₂ / g := Nat.div_le_div_right hM₂.1
    have hhi : (M₂ + g - 1) / g ≤ (k + g) / g := Nat.div_le_div_right (by omega)
    omega
  rw [abs_le]; constructor <;> omega

/-- Counting occurrences of a letter `c` belonging strictly to the `true`-colour sequence `y`
in a factor `factor (colour u y y') i L` equals counting `c` in `y` over the contiguous block
`[countTrue u i, countTrue u (i + L))`. -/
theorem count_colour_true_eq {d : ℕ} (u : ℕ → Bool) (y y' : ℕ → Fin d) (c : Fin d)
    (hnot : ∀ m : ℕ, y' m ≠ c) (i L : ℕ) :
    (factor (colour u y y') i L).count c =
      ((Finset.range (countTrue u (i + L) - countTrue u i)).filter
        (fun t => y (countTrue u i + t) = c)).card := by
  rw [count_factor_eq_card_filter]
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnotmem : L ∉ (Finset.range L).filter (fun j => colour u y y' (i + j) = c) := by simp
    have hstep : countTrue u (i + (L + 1)) =
        countTrue u (i + L) + (if u (i + L) = true then 1 else 0) := by
      rw [← Nat.add_assoc, countTrue_succ]
    have hmono : countTrue u i ≤ countTrue u (i + L) := countTrue_mono u (Nat.le_add_right i L)
    by_cases hu : u (i + L) = true
    · have hcol : colour u y y' (i + L) = y (countTrue u (i + L)) := by
        simp [colour, hu]
      have hdiff : countTrue u (i + (L + 1)) - countTrue u i =
          (countTrue u (i + L) - countTrue u i) + 1 := by
        rw [hstep, hu]; simp; omega
      rw [hdiff, Finset.range_add_one, Finset.filter_insert]
      have hnotmem2 : countTrue u (i + L) - countTrue u i ∉
          (Finset.range (countTrue u (i + L) - countTrue u i)).filter
            (fun t => y (countTrue u i + t) = c) := by simp
      have hidx : countTrue u i + (countTrue u (i + L) - countTrue u i) = countTrue u (i + L) := by
        omega
      rw [hcol, hidx]
      by_cases hy : y (countTrue u (i + L)) = c
      · simp [hy, Finset.card_insert_of_notMem hnotmem, Finset.card_insert_of_notMem hnotmem2, ih]
      · simp [hy, ih]
    · have hcol : colour u y y' (i + L) = y' (countFalse u (i + L)) := by
        simp [colour, hu]
      have hne : colour u y y' (i + L) ≠ c := by
        rw [hcol]; exact hnot _
      have hdiff : countTrue u (i + (L + 1)) - countTrue u i =
          countTrue u (i + L) - countTrue u i := by
        rw [hstep]; simp [hu]
      rw [hdiff]
      simp [hne, ih]

/-- Counting occurrences of a letter `c` belonging strictly to the `false`-colour sequence `y'`
in `factor (colour u y y') i L` equals counting `c` in `y'` over
`[countFalse u i, countFalse u (i + L))`. -/
theorem count_colour_false_eq {d : ℕ} (u : ℕ → Bool) (y y' : ℕ → Fin d) (c : Fin d)
    (hnot : ∀ m : ℕ, y m ≠ c) (i L : ℕ) :
    (factor (colour u y y') i L).count c =
      ((Finset.range (countFalse u (i + L) - countFalse u i)).filter
        (fun t => y' (countFalse u i + t) = c)).card := by
  rw [count_factor_eq_card_filter]
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnotmem : L ∉ (Finset.range L).filter (fun j => colour u y y' (i + j) = c) := by simp
    have hstep : countFalse u (i + (L + 1)) =
        countFalse u (i + L) + (if u (i + L) = false then 1 else 0) := by
      rw [← Nat.add_assoc, countFalse_succ]
    have hmono : countFalse u i ≤ countFalse u (i + L) := countFalse_mono u (Nat.le_add_right i L)
    by_cases hu : u (i + L) = false
    · have hcol : colour u y y' (i + L) = y' (countFalse u (i + L)) := by
        simp [colour, hu]
      have hdiff : countFalse u (i + (L + 1)) - countFalse u i =
          (countFalse u (i + L) - countFalse u i) + 1 := by
        rw [hstep, hu]; simp; omega
      rw [hdiff, Finset.range_add_one, Finset.filter_insert]
      have hnotmem2 : countFalse u (i + L) - countFalse u i ∉
          (Finset.range (countFalse u (i + L) - countFalse u i)).filter
            (fun t => y' (countFalse u i + t) = c) := by simp
      have hidx : countFalse u i + (countFalse u (i + L) - countFalse u i) = countFalse u (i + L) := by
        omega
      rw [hcol, hidx]
      by_cases hy : y' (countFalse u (i + L)) = c
      · simp [hy, Finset.card_insert_of_notMem hnotmem, Finset.card_insert_of_notMem hnotmem2, ih]
      · simp [hy, ih]
    · have hut : u (i + L) = true := by
        cases h : u (i + L) <;> simp_all
      have hcol : colour u y y' (i + L) = y (countTrue u (i + L)) := by
        simp [colour, hut]
      have hne : colour u y y' (i + L) ≠ c := by
        rw [hcol]; exact hnot _
      have hdiff : countFalse u (i + (L + 1)) - countFalse u i =
          countFalse u (i + L) - countFalse u i := by
        rw [hstep]; simp [hu]
      rw [hdiff]
      simp [hne, ih]

/-- **Universal Direct Balance Theorem** (no recurrence or Hubert's theorem needed):
if `0 < α < 1` and every letter `c : Fin d` is either constant-gap in `y` (and absent from `y'`)
or constant-gap in `y'` (and absent from `y`), then `colour (sturmian α) y y'` is 1-balanced. -/
theorem colour_isBalanced_of_constantGap {d : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (y y' : ℕ → Fin d)
    (hcg : ∀ c : Fin d,
      ((∀ m, y' m ≠ c) ∧ ∃ g r, HasConstantGap y c g r) ∨
      ((∀ m, y m ≠ c) ∧ ∃ g r, HasConstantGap y' c g r)) :
    IsBalanced (colour (sturmian α) y y') := by
  intro c L i j
  rcases hcg c with ⟨hnot, g, r, hg, hr, hiff⟩ | ⟨hnot, g, r, hg, hr, hiff⟩
  · -- Letter c occurs in y with constant gap g.
    rw [count_colour_true_eq _ _ _ _ hnot i L, count_colour_true_eq _ _ _ _ hnot j L]
    have hfl_nonneg : 0 ≤ ⌊(L : ℝ) * α⌋ := Int.floor_nonneg.mpr (by positivity)
    let k : ℕ := ⌊(L : ℝ) * α⌋.toNat
    have hk_cast : (k : ℤ) = ⌊(L : ℝ) * α⌋ := Int.toNat_of_nonneg hfl_nonneg
    have hMi : k ≤ countTrue (sturmian α) (i + L) - countTrue (sturmian α) i ∧
        countTrue (sturmian α) (i + L) - countTrue (sturmian α) i ≤ k + 1 := by
      have h1 := countTrue_interval (sturmian α) i L
      have h2 := sturmian_interval_countTrue_bounds hα0 hα1 i L
      omega
    have hMj : k ≤ countTrue (sturmian α) (j + L) - countTrue (sturmian α) j ∧
        countTrue (sturmian α) (j + L) - countTrue (sturmian α) j ≤ k + 1 := by
      have h1 := countTrue_interval (sturmian α) j L
      have h2 := sturmian_interval_countTrue_bounds hα0 hα1 j L
      omega
    have hci := card_mod_interval_bounds (countTrue (sturmian α) i)
      (countTrue (sturmian α) (i + L) - countTrue (sturmian α) i) g r hg hr
    have hcj := card_mod_interval_bounds (countTrue (sturmian α) j)
      (countTrue (sturmian α) (j + L) - countTrue (sturmian α) j) g r hg hr
    have hfi : ((Finset.range (countTrue (sturmian α) (i + L) - countTrue (sturmian α) i)).filter
        (fun t => y (countTrue (sturmian α) i + t) = c)).card =
        ((Finset.range (countTrue (sturmian α) (i + L) - countTrue (sturmian α) i)).filter
        (fun t => (countTrue (sturmian α) i + t) % g = r)).card := by
      congr 1; ext t; simp [hiff]
    have hfj : ((Finset.range (countTrue (sturmian α) (j + L) - countTrue (sturmian α) j)).filter
        (fun t => y (countTrue (sturmian α) j + t) = c)).card =
        ((Finset.range (countTrue (sturmian α) (j + L) - countTrue (sturmian α) j)).filter
        (fun t => (countTrue (sturmian α) j + t) % g = r)).card := by
      congr 1; ext t; simp [hiff]
    rw [hfi, hfj]
    exact mod_count_diff_le_one hg hMi hMj hci hcj
  · -- Letter c occurs in y' with constant gap g.
    rw [count_colour_false_eq _ _ _ _ hnot i L, count_colour_false_eq _ _ _ _ hnot j L]
    by_cases hL0 : L = 0
    · subst hL0; simp
    · have hfl_lt : ⌊(L : ℝ) * α⌋ < (L : ℤ) := by
        rw [Int.floor_lt]
        have hLpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hL0)
        simp only [Int.cast_natCast]
        nlinarith
      have hnonneg : 0 ≤ (L : ℤ) - ⌊(L : ℝ) * α⌋ - 1 := by omega
      let k : ℕ := ((L : ℤ) - ⌊(L : ℝ) * α⌋ - 1).toNat
      have hk_cast : (k : ℤ) = (L : ℤ) - ⌊(L : ℝ) * α⌋ - 1 := Int.toNat_of_nonneg hnonneg
      have hMi : k ≤ countFalse (sturmian α) (i + L) - countFalse (sturmian α) i ∧
          countFalse (sturmian α) (i + L) - countFalse (sturmian α) i ≤ k + 1 := by
        have h1 := countFalse_interval (sturmian α) i L
        have h2 := sturmian_interval_countFalse_bounds hα0 hα1 i L
        omega
      have hMj : k ≤ countFalse (sturmian α) (j + L) - countFalse (sturmian α) j ∧
          countFalse (sturmian α) (j + L) - countFalse (sturmian α) j ≤ k + 1 := by
        have h1 := countFalse_interval (sturmian α) j L
        have h2 := sturmian_interval_countFalse_bounds hα0 hα1 j L
        omega
      have hci := card_mod_interval_bounds (countFalse (sturmian α) i)
        (countFalse (sturmian α) (i + L) - countFalse (sturmian α) i) g r hg hr
      have hcj := card_mod_interval_bounds (countFalse (sturmian α) j)
        (countFalse (sturmian α) (j + L) - countFalse (sturmian α) j) g r hg hr
      have hfi : ((Finset.range (countFalse (sturmian α) (i + L) - countFalse (sturmian α) i)).filter
          (fun t => y' (countFalse (sturmian α) i + t) = c)).card =
          ((Finset.range (countFalse (sturmian α) (i + L) - countFalse (sturmian α) i)).filter
          (fun t => (countFalse (sturmian α) i + t) % g = r)).card := by
        congr 1; ext t; simp [hiff]
      have hfj : ((Finset.range (countFalse (sturmian α) (j + L) - countFalse (sturmian α) j)).filter
          (fun t => y' (countFalse (sturmian α) j + t) = c)).card =
          ((Finset.range (countFalse (sturmian α) (j + L) - countFalse (sturmian α) j)).filter
          (fun t => (countFalse (sturmian α) j + t) % g = r)).card := by
        congr 1; ext t; simp [hiff]
      rw [hfi, hfj]
      exact mod_count_diff_le_one hg hMi hMj hci hcj

/-- Every index `k : ℕ` is attained as `countTrue (sturmian α) n` at some `true` position `n`. -/
theorem sturmian_exists_true_index {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∃ n : ℕ, sturmian α n = true ∧ countTrue (sturmian α) n = k := by
  have hex : ∃ m : ℕ, k < countTrue (sturmian α) m := by
    obtain ⟨M, hM⟩ := exists_nat_gt (((k + 1 : ℕ) : ℝ) / α)
    refine ⟨M, ?_⟩
    have hfl := sturmian_countTrue_eq_floor hα0 hα1 M
    have hge : ((k + 1 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) * α := by
      have h1 : ((k + 1 : ℕ) : ℝ) < (M : ℝ) * α := (div_lt_iff₀ hα0).mp hM
      push_cast at h1 ⊢
      nlinarith
    have hfl_ge : (k + 1 : ℤ) ≤ ⌊((M + 1 : ℕ) : ℝ) * α⌋ := Int.le_floor.mpr (by exact_mod_cast hge)
    omega
  classical
  let m := Nat.find hex
  have hm_spec : k < countTrue (sturmian α) m := Nat.find_spec hex
  have hm_pos : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0] at hm_spec
    simp [countTrue] at hm_spec
  let n := m - 1
  have hn_lt : n < m := by omega
  have hn_le : countTrue (sturmian α) n ≤ k := by
    have := Nat.find_min hex hn_lt
    omega
  have hstep : countTrue (sturmian α) m = countTrue (sturmian α) n +
      (if sturmian α n = true then 1 else 0) := by
    have hm_eq : m = n + 1 := by omega
    rw [hm_eq, countTrue_succ]
  refine ⟨n, ?_, ?_⟩
  · by_contra hne
    simp [hne] at hstep
    omega
  · by_cases ht : sturmian α n = true
    · simp [ht] at hstep; omega
    · simp [ht] at hstep; omega

/-- Every index `k : ℕ` is attained as `countFalse (sturmian α) n` at some `false` position `n`. -/
theorem sturmian_exists_false_index {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∃ n : ℕ, sturmian α n = false ∧ countFalse (sturmian α) n = k := by
  have hex : ∃ m : ℕ, k < countFalse (sturmian α) m := by
    have h1a : 0 < 1 - α := by linarith
    obtain ⟨M, hM⟩ := exists_nat_gt (((k + 2 : ℕ) : ℝ) / (1 - α))
    refine ⟨M, ?_⟩
    have hfl := sturmian_countTrue_eq_floor hα0 hα1 M
    have hsum := countTrue_add_countFalse (sturmian α) M
    have hlt : ⌊((M + 1 : ℕ) : ℝ) * α⌋ ≤ (((M + 1 : ℕ) : ℝ) * α) := Int.floor_le _
    have h1 : ((k + 2 : ℕ) : ℝ) < (M : ℝ) * (1 - α) := (div_lt_iff₀ h1a).mp hM
    have h2 : ((k : ℝ) + 1) < (M : ℝ) - ((M + 1 : ℕ) : ℝ) * α := by
      push_cast at h1 ⊢; linarith
    have h3 : (k : ℝ) < (M : ℝ) - (⌊((M + 1 : ℕ) : ℝ) * α⌋ : ℝ) := by linarith
    have h4 : (k : ℝ) < (countFalse (sturmian α) M : ℝ) := by
      have : (countFalse (sturmian α) M : ℝ) = (M : ℝ) - (⌊((M + 1 : ℕ) : ℝ) * α⌋ : ℝ) := by
        have hzi : (countFalse (sturmian α) M : ℤ) = (M : ℤ) - ⌊((M + 1 : ℕ) : ℝ) * α⌋ := by
          omega
        exact_mod_cast hzi
      linarith
    exact_mod_cast h4
  classical
  let m := Nat.find hex
  have hm_spec : k < countFalse (sturmian α) m := Nat.find_spec hex
  have hm_pos : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0] at hm_spec
    simp [countFalse] at hm_spec
  let n := m - 1
  have hn_lt : n < m := by omega
  have hn_le : countFalse (sturmian α) n ≤ k := by
    have := Nat.find_min hex hn_lt
    omega
  have hstep : countFalse (sturmian α) m = countFalse (sturmian α) n +
      (if sturmian α n = false then 1 else 0) := by
    have hm_eq : m = n + 1 := by omega
    rw [hm_eq, countFalse_succ]
  refine ⟨n, ?_, ?_⟩
  · by_contra hne
    simp [hne] at hstep
    omega
  · by_cases hf : sturmian α n = false
    · simp [hf] at hstep; omega
    · simp [hf] at hstep; omega

/-- If every letter `c : Fin d` appears in `y` or in `y'`, then `colour (sturmian α) y y'` uses
all `d` letters. -/
theorem colour_usesAllLetters {d : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (y y' : ℕ → Fin d)
    (hcover : ∀ c : Fin d, (∃ k, y k = c) ∨ (∃ k, y' k = c)) :
    UsesAllLetters (colour (sturmian α) y y') := by
  intro c
  rcases hcover c with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨n, hnt, hnc⟩ := sturmian_exists_true_index hα0 hα1 k
    exact ⟨n, by simp [colour, hnt, hnc, hk]⟩
  · obtain ⟨n, hnf, hnc⟩ := sturmian_exists_false_index hα0 hα1 k
    exact ⟨n, by simp [colour, hnf, hnc, hk]⟩

end BalancedRepetitionThreshold
