module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Count

import Mathlib.Tactic

/-!
# Exact Definitions for Balanced Sequences and Repetition Thresholds `RTB(d)`

This module formalizes the exact definitions from all five printed papers:
- Rampersad, Shallit, Vandomme (arXiv:1801.05334, TCS 777 (2019)), Definitions 1 & 2;
- Dolce, Dvořáková, Pelantová (arXiv:2108.07503);
- Dvořáková, Pelantová, Opočenská, Shur (arXiv:2112.02854, TCS 922 (2022));
- Dvořáková, Opočenská, Pelantová (arXiv:2208.00366);
- Dvořáková, Pelantová (arXiv:2309.00988).

No recurrence, aperiodicity, or alphabet-usage side hypothesis is added to `IsBalanced` or `RTB`.
We also define `RTB_strict` (restricting to sequences that use all `d` letters) and prove the
equivalence between the any-period critical exponent (RSV) and the minimal-period critical
exponent (DPOS).
-/

@[expose] public section

namespace BalancedRepetitionThreshold

/-- The contiguous factor of length `L` starting at position `i` in an infinite sequence `w`. -/
def factor {α : Type*} (w : ℕ → α) (i L : ℕ) : List α :=
  (List.range L).map (fun j => w (i + j))

/-- The length of `factor w i L` is `L`. -/
theorem length_factor {α : Type*} (w : ℕ → α) (i L : ℕ) :
    (factor w i L).length = L := by
  simp [factor]

/-- Letter count in `factor w i L` expressed via `Finset.filter` on `Finset.range L`. -/
theorem count_factor_eq_card_filter {α : Type*} [DecidableEq α]
    (w : ℕ → α) (a : α) (i L : ℕ) :
    (factor w i L).count a = ((Finset.range L).filter (fun j => w (i + j) = a)).card := by
  induction L with
  | zero =>
    simp [factor]
  | succ L ih =>
    rw [factor, List.range_succ, List.map_append, List.map_singleton, List.count_append,
      List.count_singleton]
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnotmem : L ∉ (Finset.range L).filter (fun j => w (i + j) = a) := by
      simp
    by_cases h : w (i + L) = a
    · simp only [beq_iff_eq, h, ↓reduceIte, Finset.card_insert_of_notMem hnotmem]
      rw [← ih, factor]
    · have hne : (w (i + L) == a) = false := by
        simp [beq_eq_false_iff_ne, h]
      simp only [hne, Bool.false_eq_true, ↓reduceIte, h]
      rw [← ih, factor, add_zero]

/-- A finite word `u` over `Fin d` is 1-balanced if any two factors of equal length differ in the
count of any letter by at most `1`. -/
def IsBalancedList {d : ℕ} (u : List (Fin d)) : Prop :=
  ∀ (a : Fin d) (L i j : ℕ), i + L ≤ u.length → j + L ≤ u.length →
    |(((u.drop i).take L).count a : ℤ) - (((u.drop j).take L).count a : ℤ)| ≤ 1

/-- An infinite sequence `w : ℕ → Fin d` is 1-balanced (Definition 1 across all five printed
papers) if for every letter `a : Fin d`, every length `L : ℕ`, and all start positions `i, j : ℕ`,
the counts of `a` in `factor w i L` and `factor w j L` differ by at most `1`. -/
def IsBalanced {d : ℕ} (w : ℕ → Fin d) : Prop :=
  ∀ (a : Fin d) (L i j : ℕ),
    |((factor w i L).count a : ℤ) - ((factor w j L).count a : ℤ)| ≤ 1

/-- Every prefix of a balanced infinite sequence is a balanced finite word. -/
theorem isBalancedList_prefix_of_isBalanced {d : ℕ} {w : ℕ → Fin d} (hw : IsBalanced w) (n : ℕ) :
    IsBalancedList (factor w 0 n) := by
  intro a L i j hi hj
  rw [length_factor] at hi hj
  have hslice : ∀ s, s + L ≤ n → ((factor w 0 n).drop s).take L = factor w s L := by
    intro s hs
    apply List.ext_getElem
    · simp [factor]; omega
    · intro k hk1 hk2
      simp only [List.getElem_take, List.getElem_drop, factor, List.getElem_map,
        List.getElem_range, zero_add]
  rw [hslice i hi, hslice j hj]
  exact hw a L i j

/-- A sequence `w : ℕ → Fin d` uses all `d` letters of its alphabet. -/
def UsesAllLetters {d : ℕ} (w : ℕ → Fin d) : Prop :=
  ∀ a : Fin d, ∃ i : ℕ, w i = a

/-- The factor `factor w i L` has period `p` (with `0 < p ≤ L`). -/
def HasPeriod {α : Type*} (w : ℕ → α) (i L p : ℕ) : Prop :=
  0 < p ∧ p ≤ L ∧ ∀ k : ℕ, k + p < L → w (i + k) = w (i + k + p)

/-- `p` is the minimal period of the factor `factor w i L`. -/
def IsMinPeriod {α : Type*} (w : ℕ → α) (i L p : ℕ) : Prop :=
  HasPeriod w i L p ∧ ∀ q : ℕ, HasPeriod w i L q → p ≤ q

/-- The set of factor exponents `L / p` (in `EReal`, so periodic sequences have supremum `⊤`)
over all non-empty factors with period `p ≤ L`. -/
def exponentSet {d : ℕ} (w : ℕ → Fin d) : Set EReal :=
  { e : EReal | ∃ i L p : ℕ, HasPeriod w i L p ∧ e = (((L : ℝ) / (p : ℝ) : ℝ) : EReal) }

/-- The set of minimal-period factor exponents `|z| / per(z)` (DPOS Definition). -/
def minPeriodExponentSet {d : ℕ} (w : ℕ → Fin d) : Set EReal :=
  { e : EReal | ∃ i L p : ℕ, IsMinPeriod w i L p ∧ e = (((L : ℝ) / (p : ℝ) : ℝ) : EReal) }

/-- The unrestricted exponent set allowing `p > L` (for any non-empty factor `0 < L` and `0 < p`). -/
def unrestrictedExponentSet {d : ℕ} (w : ℕ → Fin d) : Set EReal :=
  { e : EReal | ∃ i L p : ℕ, 0 < L ∧ 0 < p ∧
    (∀ k : ℕ, k + p < L → w (i + k) = w (i + k + p)) ∧
    e = (((L : ℝ) / (p : ℝ) : ℝ) : EReal) }

/-- The critical exponent `E(w) ∈ EReal` of an infinite sequence `w : ℕ → Fin d`. -/
noncomputable def critExp {d : ℕ} (w : ℕ → Fin d) : EReal :=
  sSup (exponentSet w)

/-- The balanced-sequence repetition threshold `RTB(d) = inf { E(w) | w balanced over Fin d }`. -/
noncomputable def RTB (d : ℕ) : EReal :=
  sInf { e : EReal | ∃ w : ℕ → Fin d, IsBalanced w ∧ critExp w = e }

/-- The strict balanced-sequence repetition threshold restricting to sequences using all `d`
letters. -/
noncomputable def RTB_strict (d : ℕ) : EReal :=
  sInf { e : EReal | ∃ w : ℕ → Fin d, IsBalanced w ∧ UsesAllLetters w ∧ critExp w = e }

/-- Every sequence has `1 ∈ exponentSet w` (via any length-1 factor with period 1). -/
theorem one_mem_exponentSet {d : ℕ} (w : ℕ → Fin d) :
    ((1 : ℝ) : EReal) ∈ exponentSet w := by
  refine ⟨0, 1, 1, ⟨by omega, by omega, fun k hk => by omega⟩, ?_⟩
  norm_num

/-- Every sequence has `1 ∈ minPeriodExponentSet w`. -/
theorem one_mem_minPeriodExponentSet {d : ℕ} (w : ℕ → Fin d) :
    ((1 : ℝ) : EReal) ∈ minPeriodExponentSet w := by
  refine ⟨0, 1, 1, ⟨⟨by omega, by omega, fun k hk => by omega⟩, fun q hq => hq.1⟩, ?_⟩
  norm_num

/-- Every sequence satisfies `1 ≤ critExp w`. -/
theorem one_le_critExp {d : ℕ} (w : ℕ → Fin d) :
    ((1 : ℝ) : EReal) ≤ critExp w :=
  le_sSup (one_mem_exponentSet w)

/-- The minimal-period critical exponent equals `critExp w` (equivalence of RSV and DPOS). -/
theorem sSup_minPeriodExponentSet_eq_critExp {d : ℕ} (w : ℕ → Fin d) :
    sSup (minPeriodExponentSet w) = critExp w := by
  apply le_antisymm
  · apply sSup_le
    rintro e ⟨i, L, p, hp, rfl⟩
    exact le_sSup ⟨i, L, p, hp.1, rfl⟩
  · apply sSup_le
    rintro e ⟨i, L, p, hp, rfl⟩
    classical
    have hex : ∃ q : ℕ, HasPeriod w i L q := ⟨p, hp⟩
    let q := Nat.find hex
    have hq : HasPeriod w i L q := Nat.find_spec hex
    have hmin : IsMinPeriod w i L q := ⟨hq, fun r hr => Nat.find_min' hex hr⟩
    have hqp : q ≤ p := Nat.find_min' hex hp
    have hle : (((L : ℝ) / (p : ℝ) : ℝ) : EReal) ≤ (((L : ℝ) / (q : ℝ) : ℝ) : EReal) := by
      rw [EReal.coe_le_coe_iff]
      have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq.1
      have hqp' : (q : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hqp
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg L) hqpos hqp'
    exact le_trans hle (le_sSup ⟨i, L, q, hmin, rfl⟩)

/-- Removing the `p ≤ L` side condition does not change the critical exponent. -/
theorem sSup_unrestrictedExponentSet_eq_critExp {d : ℕ} (w : ℕ → Fin d) :
    sSup (unrestrictedExponentSet w) = critExp w := by
  apply le_antisymm
  · apply sSup_le
    rintro e ⟨i, L, p, hL, hp, hper, rfl⟩
    by_cases hle : p ≤ L
    · exact le_sSup ⟨i, L, p, ⟨hp, hle, hper⟩, rfl⟩
    · have hlt : (L : ℝ) / (p : ℝ) ≤ 1 := by
        rw [div_le_one (Nat.cast_pos.mpr hp)]
        exact Nat.cast_le.mpr (by omega)
      exact le_trans (EReal.coe_le_coe_iff.mpr hlt) (one_le_critExp w)
  · apply sSup_le
    rintro e ⟨i, L, p, hp, rfl⟩
    exact le_sSup ⟨i, L, p, lt_of_lt_of_le hp.1 hp.2.1, hp.1, hp.2.2, rfl⟩

/-- If every match run `w (i + k) = w (i + k + p)` for `k < r` satisfies `r * den ≤ p * (num - den)`
(with `0 < den ≤ num`), then `critExp w ≤ num / den`. -/
theorem critExp_le_of_run_bound {d : ℕ} {w : ℕ → Fin d} {num den : ℕ}
    (hden : 0 < den) (hnd : den ≤ num)
    (hbound : ∀ i p r : ℕ, 0 < p → (∀ k < r, w (i + k) = w (i + k + p)) →
      r * den ≤ p * (num - den)) :
    critExp w ≤ (((num : ℝ) / (den : ℝ) : ℝ) : EReal) := by
  apply sSup_le
  rintro e ⟨i, L, p, ⟨hp, hpL, hper⟩, rfl⟩
  rw [EReal.coe_le_coe_iff]
  have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hdenR : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  rw [div_le_div_iff₀ hpR hdenR]
  have hrun : (L - p) * den ≤ p * (num - den) := by
    apply hbound i p (L - p) hp
    intro k hk
    exact hper k (by omega)
  have hnat : L * den ≤ num * p := by
    have h1 : L = (L - p) + p := (Nat.sub_add_cancel hpL).symm
    have h2 : num = (num - den) + den := (Nat.sub_add_cancel hnd).symm
    calc L * den = ((L - p) + p) * den := by rw [← h1]
      _ = (L - p) * den + p * den := by ring
      _ ≤ p * (num - den) + p * den := Nat.add_le_add_right hrun _
      _ = p * ((num - den) + den) := by ring
      _ = p * num := by rw [← h2]
      _ = num * p := mul_comm p num
  exact_mod_cast hnat

/-- Witnessing a single factor `(i, L, p)` with `p * num ≤ L * den` gives `num / den ≤ critExp w`. -/
theorem le_critExp_of_period {d : ℕ} {w : ℕ → Fin d} {i L p num den : ℕ}
    (hden : 0 < den) (hper : HasPeriod w i L p) (hineq : p * num ≤ L * den) :
    (((num : ℝ) / (den : ℝ) : ℝ) : EReal) ≤ critExp w := by
  have hle : (((num : ℝ) / (den : ℝ) : ℝ) : EReal) ≤ (((L : ℝ) / (p : ℝ) : ℝ) : EReal) := by
    rw [EReal.coe_le_coe_iff]
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr hden) (Nat.cast_pos.mpr hper.1)]
    have h : num * p ≤ L * den := by linarith
    exact_mod_cast h
  exact le_trans hle (le_sSup ⟨i, L, p, hper, rfl⟩)

/-- If `critExp w ≤ num / den` and a factor `(i, L, p)` achieves `L * den = p * num`, then
`critExp w = num / den` and the supremum is attained as a maximum in `minPeriodExponentSet w`. -/
theorem attains_critExp_of_period {d : ℕ} {w : ℕ → Fin d} {i L p num den : ℕ}
    (hden : 0 < den)
    (hub : critExp w ≤ (((num : ℝ) / (den : ℝ) : ℝ) : EReal))
    (hper : HasPeriod w i L p)
    (heq : L * den = p * num) :
    critExp w = (((num : ℝ) / (den : ℝ) : ℝ) : EReal) ∧
    (((num : ℝ) / (den : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet w := by
  have hlb : (((num : ℝ) / (den : ℝ) : ℝ) : EReal) ≤ critExp w :=
    le_critExp_of_period hden hper (le_of_eq heq.symm)
  have hcrit : critExp w = (((num : ℝ) / (den : ℝ) : ℝ) : EReal) := le_antisymm hub hlb
  have hval : (L : ℝ) / (p : ℝ) = (num : ℝ) / (den : ℝ) := by
    rw [div_eq_div_iff (ne_of_gt (Nat.cast_pos.mpr hper.1)) (ne_of_gt (Nat.cast_pos.mpr hden))]
    have h : (L : ℝ) * (den : ℝ) = (num : ℝ) * (p : ℝ) := by
      have : L * den = num * p := by linarith
      exact_mod_cast this
    exact h
  have hmin : IsMinPeriod w i L p := by
    refine ⟨hper, ?_⟩
    intro q hq
    by_contra hlt
    push Not at hlt
    have hmem : (((L : ℝ) / (q : ℝ) : ℝ) : EReal) ∈ exponentSet w := ⟨i, L, q, hq, rfl⟩
    have hqle : (((L : ℝ) / (q : ℝ) : ℝ) : EReal) ≤ (((num : ℝ) / (den : ℝ) : ℝ) : EReal) :=
      le_trans (le_sSup hmem) hub
    rw [EReal.coe_le_coe_iff, ← hval] at hqle
    have hLpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hper.1 hper.2.1)
    have hqp : (q : ℝ) < (p : ℝ) := Nat.cast_lt.mpr hlt
    have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq.1
    have hstrict : (L : ℝ) / (p : ℝ) < (L : ℝ) / (q : ℝ) :=
      div_lt_div_of_pos_left hLpos hqpos hqp
    linarith
  exact ⟨hcrit, ⟨i, L, p, hmin, by rw [hval]⟩⟩

/-- `RTB d ≤ RTB_strict d` since every sequence using all letters is a sequence over `Fin d`. -/
theorem RTB_le_RTB_strict (d : ℕ) : RTB d ≤ RTB_strict d := by
  apply le_sInf
  rintro e ⟨w, hbal, _, rfl⟩
  exact sInf_le ⟨w, hbal, rfl⟩

/-- Lower-bound introduction rule for `RTB d`. -/
theorem le_RTB_of_forall {d : ℕ} {B : EReal}
    (h : ∀ w : ℕ → Fin d, IsBalanced w → B ≤ critExp w) :
    B ≤ RTB d := by
  apply le_sInf
  rintro e ⟨w, hbal, rfl⟩
  exact h w hbal

/-- Upper-bound introduction rule for `RTB d` via a balanced witness. -/
theorem RTB_le_of_witness {d : ℕ} {w : ℕ → Fin d} {B : EReal}
    (hbal : IsBalanced w) (hcrit : critExp w ≤ B) :
    RTB d ≤ B :=
  le_trans (sInf_le ⟨w, hbal, rfl⟩) hcrit

/-- Upper-bound introduction rule for `RTB_strict d` via a balanced witness using all letters. -/
theorem RTB_strict_le_of_witness {d : ℕ} {w : ℕ → Fin d} {B : EReal}
    (hbal : IsBalanced w) (hall : UsesAllLetters w) (hcrit : critExp w ≤ B) :
    RTB_strict d ≤ B :=
  le_trans (sInf_le ⟨w, hbal, hall, rfl⟩) hcrit

end BalancedRepetitionThreshold
