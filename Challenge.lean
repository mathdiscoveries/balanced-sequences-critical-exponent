module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Count

/-!
# Palomar Challenge: Balanced-Sequence Repetition Threshold Refutation: Exact RTB(7) = 6/5, RTB(9) = 8/7, and RTB(10) = 9/8

Self-contained definitions of 1-balanced infinite sequences `IsBalanced`, alphabet coverage
`UsesAllLetters`, factor periods `HasPeriod` and minimal periods `IsMinPeriod`, the critical
exponent `critExp` in `EReal`, the balanced-sequence repetition thresholds `RTB` and `RTB_strict`,
mechanical Sturmian sequences `sturmian`, colourings `colour`, and the explicit witnesses `v7`,
`v9`, and `v10`, together with 26 compared theorems establishing exact values `RTB(7) = 6/5 < 5/4`,
`RTB(9) = 8/7 < 7/6`, and `RTB(10) = 9/8 < 8/7` (both unrestricted and strict all-letters variants).
-/

@[expose] public section

namespace BalancedRepetitionThresholdChallenge

/-- The contiguous factor of length `L` starting at position `i` in an infinite sequence `w`. -/
def factor {α : Type*} (w : ℕ → α) (i L : ℕ) : List α :=
  (List.range L).map (fun j => w (i + j))

/-- An infinite sequence `w : ℕ → Fin d` is 1-balanced if for every letter `a : Fin d`, every
length `L : ℕ`, and all start positions `i, j : ℕ`, the counts of `a` in `factor w i L` and
`factor w j L` differ by at most `1`. -/
def IsBalanced {d : ℕ} (w : ℕ → Fin d) : Prop :=
  ∀ (a : Fin d) (L i j : ℕ),
    |((factor w i L).count a : ℤ) - ((factor w j L).count a : ℤ)| ≤ 1

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

/-- The set of minimal-period factor exponents `L / p`. -/
def minPeriodExponentSet {d : ℕ} (w : ℕ → Fin d) : Set EReal :=
  { e : EReal | ∃ i L p : ℕ, IsMinPeriod w i L p ∧ e = (((L : ℝ) / (p : ℝ) : ℝ) : EReal) }

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

/-- Rare-letter frequency `α7 = (11 - √10) / 37` for `v7`. -/
noncomputable def α7 : ℝ := (11 - Real.sqrt 10) / 37

/-- Period-2 colour sequence `y7` on `Fin 7` (0-indexed for printed `(6 7)^ω`). -/
def y7 (k : ℕ) : Fin 7 :=
  match k % 2 with
  | 0 => 5
  | _ => 6

/-- Period-12 colour sequence `y'7` on `Fin 7` (0-indexed for printed `(1 2 3 4 1 5 3 2 1 4 3 5)^ω`). -/
def y'7 (k : ℕ) : Fin 7 :=
  match k % 12 with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 4
  | 6 => 2 | 7 => 1 | 8 => 0 | 9 => 3 | 10 => 2 | _ => 4

/-- The 7-letter balanced witness `v7 = colour (sturmian α7) y7 y'7`. -/
noncomputable def v7 : ℕ → Fin 7 :=
  colour (sturmian α7) y7 y'7

/-- Rare-letter frequency `α9 = (41 - 2 √2) / 239` for `v9`. -/
noncomputable def α9 : ℝ := (41 - 2 * Real.sqrt 2) / 239

/-- Period-2 colour sequence `y9` on `Fin 9` (0-indexed for printed `(1 2)^ω`). -/
def y9 (k : ℕ) : Fin 9 :=
  match k % 2 with
  | 0 => 0
  | _ => 1

/-- Period-24 colour sequence `y'9` on `Fin 9`. -/
def y'9 (k : ℕ) : Fin 9 :=
  match k % 24 with
  | 0 => 2 | 1 => 5 | 2 => 3 | 3 => 6 | 4 => 4 | 5 => 7
  | 6 => 2 | 7 => 8 | 8 => 3 | 9 => 5 | 10 => 4 | 11 => 6
  | 12 => 2 | 13 => 7 | 14 => 3 | 15 => 8 | 16 => 4 | 17 => 5
  | 18 => 2 | 19 => 6 | 20 => 3 | 21 => 7 | 22 => 4 | _ => 8

/-- The 9-letter balanced witness `v9 = colour (sturmian α9) y9 y'9`. -/
noncomputable def v9 : ℕ → Fin 9 :=
  colour (sturmian α9) y9 y'9

/-- Rare-letter frequency `α10 = (7 + √5) / 22` for `v10`. -/
noncomputable def α10 : ℝ := (7 + Real.sqrt 5) / 22

/-- Period-5 colour sequence `y10` on `Fin 10` (0-indexed for printed `(1 2 3 4 5)^ω`). -/
def y10 (k : ℕ) : Fin 10 :=
  match k % 5 with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 4

/-- Period-5 colour sequence `y'10` on `Fin 10` (0-indexed for printed `(6 7 8 9 10)^ω`). -/
def y'10 (k : ℕ) : Fin 10 :=
  match k % 5 with
  | 0 => 5 | 1 => 6 | 2 => 7 | 3 => 8 | _ => 9

/-- The 10-letter balanced witness `v10 = colour (sturmian α10) y10 y'10`. -/
noncomputable def v10 : ℕ → Fin 10 :=
  colour (sturmian α10) y10 y'10

/-- Exact value `RTB(7) = 6/5`. -/
theorem rtb_7_eq : RTB 7 = (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) := by sorry

/-- Exact value `RTB(9) = 8/7`. -/
theorem rtb_9_eq : RTB 9 = (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) := by sorry

/-- Exact value `RTB(10) = 9/8`. -/
theorem rtb_10_eq : RTB 10 = (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) := by sorry

/-- Refutation of the listed value `5/4`: `RTB(7) < 5/4`. -/
theorem rtb_7_lt_printed : RTB 7 < (((5 : ℝ) / (4 : ℝ) : ℝ) : EReal) := by sorry

/-- Refutation of the listed value `7/6`: `RTB(9) < 7/6`. -/
theorem rtb_9_lt_printed : RTB 9 < (((7 : ℝ) / (6 : ℝ) : ℝ) : EReal) := by sorry

/-- Refutation of the listed value `8/7`: `RTB(10) < 8/7`. -/
theorem rtb_10_lt_printed : RTB 10 < (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) := by sorry

/-- Exact value `RTB_strict(7) = 6/5` (all 7 letters required). -/
theorem rtb_strict_7_eq : RTB_strict 7 = (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) := by sorry

/-- Exact value `RTB_strict(9) = 8/7` (all 9 letters required). -/
theorem rtb_strict_9_eq : RTB_strict 9 = (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) := by sorry

/-- Exact value `RTB_strict(10) = 9/8` (all 10 letters required). -/
theorem rtb_strict_10_eq : RTB_strict 10 = (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) := by sorry

/-- Every 1-balanced sequence over `Fin 7` has critical exponent at least `6/5`. -/
theorem critExp_ge_7 (w : ℕ → Fin 7) (hw : IsBalanced w) :
    (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ≤ critExp w := by sorry

/-- Every 1-balanced sequence over `Fin 9` has critical exponent at least `8/7`. -/
theorem critExp_ge_9 (w : ℕ → Fin 9) (hw : IsBalanced w) :
    (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ≤ critExp w := by sorry

/-- Every 1-balanced sequence over `Fin 10` has critical exponent at least `9/8`. -/
theorem critExp_ge_10 (w : ℕ → Fin 10) (hw : IsBalanced w) :
    (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ≤ critExp w := by sorry

/-- The explicit 7-letter witness `v7` is 1-balanced. -/
theorem v7_isBalanced : IsBalanced v7 := by sorry

/-- The explicit 9-letter witness `v9` is 1-balanced. -/
theorem v9_isBalanced : IsBalanced v9 := by sorry

/-- The explicit 10-letter witness `v10` is 1-balanced. -/
theorem v10_isBalanced : IsBalanced v10 := by sorry

/-- The explicit 7-letter witness `v7` uses all 7 letters. -/
theorem v7_usesAllLetters : UsesAllLetters v7 := by sorry

/-- The explicit 9-letter witness `v9` uses all 9 letters. -/
theorem v9_usesAllLetters : UsesAllLetters v9 := by sorry

/-- The explicit 10-letter witness `v10` uses all 10 letters. -/
theorem v10_usesAllLetters : UsesAllLetters v10 := by sorry

/-- Explicit attaining factor of exponent `6/5` in `v7` (prefix of length 6, period 5). -/
theorem v7_attains : HasPeriod v7 0 6 5 := by sorry

/-- Explicit attaining factor of exponent `8/7` in `v9` (prefix of length 8, period 7). -/
theorem v9_attains : HasPeriod v9 0 8 7 := by sorry

/-- Explicit attaining factor of exponent `9/8` in `v10` (factor at index 4 of length 9, period 8). -/
theorem v10_attains : HasPeriod v10 4 9 8 := by sorry

/-- Exact critical exponent `E(v7) = 6/5`, attained as a maximum in `minPeriodExponentSet v7`. -/
theorem v7_critExp_eq :
    critExp v7 = (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ∧
    (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v7 := by sorry

/-- Exact critical exponent `E(v9) = 8/7`, attained as a maximum in `minPeriodExponentSet v9`. -/
theorem v9_critExp_eq :
    critExp v9 = (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ∧
    (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v9 := by sorry

/-- Exact critical exponent `E(v10) = 9/8`, attained as a maximum in `minPeriodExponentSet v10`. -/
theorem v10_critExp_eq :
    critExp v10 = (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ∧
    (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v10 := by sorry

/-- Equivalence of minimal-period and any-period critical exponent definitions. -/
theorem sSup_minPeriodExponentSet_eq_critExp {d : ℕ} (w : ℕ → Fin d) :
    sSup (minPeriodExponentSet w) = critExp w := by sorry

/-- Combined headline theorem bundling exact values `RTB(7) = 6/5`, `RTB(9) = 8/7`, `RTB(10) = 9/8`,
strict all-letters variants, strict refutations of `5/4`, `7/6`, `8/7`, and explicit attained
balanced witnesses `v7`, `v9`, and `v10`. -/
theorem r22_1_1_main :
    (RTB 7 = (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ∧
     RTB_strict 7 = (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ∧
     RTB 7 < (((5 : ℝ) / (4 : ℝ) : ℝ) : EReal) ∧
     IsBalanced v7 ∧ UsesAllLetters v7 ∧
     critExp v7 = (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ∧
     (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v7) ∧
    (RTB 9 = (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ∧
     RTB_strict 9 = (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ∧
     RTB 9 < (((7 : ℝ) / (6 : ℝ) : ℝ) : EReal) ∧
     IsBalanced v9 ∧ UsesAllLetters v9 ∧
     critExp v9 = (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ∧
     (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v9) ∧
    (RTB 10 = (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ∧
     RTB_strict 10 = (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ∧
     RTB 10 < (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ∧
     IsBalanced v10 ∧ UsesAllLetters v10 ∧
     critExp v10 = (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ∧
     (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v10) := by sorry

end BalancedRepetitionThresholdChallenge
