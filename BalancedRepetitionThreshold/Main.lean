module

public import BalancedRepetitionThreshold.LowerBound7
public import BalancedRepetitionThreshold.LowerBound9
public import BalancedRepetitionThreshold.LowerBound10
public import BalancedRepetitionThreshold.WitnessV7
public import BalancedRepetitionThreshold.WitnessV9
public import BalancedRepetitionThreshold.WitnessV10

import Mathlib.Tactic

/-!
# Main Theorems for `R22-1-1` with `v7`: Exact Values of `RTB(7)`, `RTB(9)`, and `RTB(10)`

Combines the three unconditional pure-kernel lower-bound witness trees (`LowerBound7`, `LowerBound9`,
`LowerBound10`) and the three unconditional Sturmian-colouring upper-bound witnesses (`WitnessV7`,
`WitnessV9`, `WitnessV10`) to prove:

- `RTB 7 = RTB_strict 7 = 6 / 5 < 5 / 4` (attained by `v7`),
- `RTB 9 = RTB_strict 9 = 8 / 7 < 7 / 6` (attained by `v9`),
- `RTB 10 = RTB_strict 10 = 9 / 8 < 8 / 7` (attained by `v10`),

refuting three of the six printed values `(d - 2) / (d - 3)` (`5 / 4`, `7 / 6`, `8 / 7`) stated as
known in Rampersad–Shallit–Vandomme (2018), Dolce–Dvořáková–Pelantová (2021),
Dvořáková–Pelantová–Opočenská–Shur (2021), Dvořáková–Opočenská–Pelantová (2022), and
Dvořáková–Pelantová (2023).
-/

@[expose] public section

namespace BalancedRepetitionThreshold

/-! ## Exact Values for `d = 7` -/

/-- Upper bound `RTB 7 ≤ 6 / 5`. -/
theorem rtb_le_7 : RTB 7 ≤ (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) :=
  RTB_le_of_witness v7_isBalanced v7_critExp_le

/-- Strict upper bound `RTB_strict 7 ≤ 6 / 5`. -/
theorem rtb_strict_le_7 : RTB_strict 7 ≤ (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) :=
  RTB_strict_le_of_witness v7_isBalanced v7_usesAllLetters v7_critExp_le

/-- **Exact value `RTB 7 = 6 / 5`.** -/
theorem rtb_7_eq : RTB 7 = (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) :=
  le_antisymm rtb_le_7 rtb_ge_7

/-- **Exact value `RTB_strict 7 = 6 / 5`.** -/
theorem rtb_strict_7_eq : RTB_strict 7 = (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) :=
  le_antisymm rtb_strict_le_7 (le_trans rtb_ge_7 (RTB_le_RTB_strict 7))

/-- **Refutation of the printed value `RTB(7) = 5 / 4`**: `RTB 7 < 5 / 4`. -/
theorem rtb_7_lt_printed : RTB 7 < (((5 : ℝ) / (4 : ℝ) : ℝ) : EReal) := by
  rw [rtb_7_eq, EReal.coe_lt_coe_iff]
  norm_num

/-! ## Exact Values for `d = 9` -/

/-- Upper bound `RTB 9 ≤ 8 / 7`. -/
theorem rtb_le_9 : RTB 9 ≤ (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) :=
  RTB_le_of_witness v9_isBalanced v9_critExp_le

/-- Strict upper bound `RTB_strict 9 ≤ 8 / 7`. -/
theorem rtb_strict_le_9 : RTB_strict 9 ≤ (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) :=
  RTB_strict_le_of_witness v9_isBalanced v9_usesAllLetters v9_critExp_le

/-- **Exact value `RTB 9 = 8 / 7`.** -/
theorem rtb_9_eq : RTB 9 = (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) :=
  le_antisymm rtb_le_9 rtb_ge_9

/-- **Exact value `RTB_strict 9 = 8 / 7`.** -/
theorem rtb_strict_9_eq : RTB_strict 9 = (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) :=
  le_antisymm rtb_strict_le_9 (le_trans rtb_ge_9 (RTB_le_RTB_strict 9))

/-- **Refutation of the printed value `RTB(9) = 7 / 6`**: `RTB 9 < 7 / 6`. -/
theorem rtb_9_lt_printed : RTB 9 < (((7 : ℝ) / (6 : ℝ) : ℝ) : EReal) := by
  rw [rtb_9_eq, EReal.coe_lt_coe_iff]
  norm_num

/-! ## Exact Values for `d = 10` -/

/-- Upper bound `RTB 10 ≤ 9 / 8`. -/
theorem rtb_le_10 : RTB 10 ≤ (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) :=
  RTB_le_of_witness v10_isBalanced v10_critExp_le

/-- Strict upper bound `RTB_strict 10 ≤ 9 / 8`. -/
theorem rtb_strict_le_10 : RTB_strict 10 ≤ (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) :=
  RTB_strict_le_of_witness v10_isBalanced v10_usesAllLetters v10_critExp_le

/-- **Exact value `RTB 10 = 9 / 8`.** -/
theorem rtb_10_eq : RTB 10 = (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) :=
  le_antisymm rtb_le_10 rtb_ge_10

/-- **Exact value `RTB_strict 10 = 9 / 8`.** -/
theorem rtb_strict_10_eq : RTB_strict 10 = (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) :=
  le_antisymm rtb_strict_le_10 (le_trans rtb_ge_10 (RTB_le_RTB_strict 10))

/-- **Refutation of the printed value `RTB(10) = 8 / 7`**: `RTB 10 < 8 / 7`. -/
theorem rtb_10_lt_printed : RTB 10 < (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) := by
  rw [rtb_10_eq, EReal.coe_lt_coe_iff]
  norm_num

/-! ## Combined Headline Theorem (`R22-1-1` with `v7`) -/

/-- **Combined Headline Theorem (`R22-1-1` with `v7`)**:
Exact values `RTB(7) = 6/5`, `RTB(9) = 8/7`, `RTB(10) = 9/8` (both unrestricted and strict
all-letters variants), strict refutation of the printed values `5/4`, `7/6`, `8/7`, and attained
balanced witnesses `v7`, `v9`, `v10` using all `d` letters with critical exponents achieved as
maxima in `minPeriodExponentSet`. -/
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
     (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ∈ minPeriodExponentSet v10) :=
  ⟨⟨rtb_7_eq, rtb_strict_7_eq, rtb_7_lt_printed, v7_isBalanced, v7_usesAllLetters,
      v7_critExp_eq.1, v7_critExp_eq.2⟩,
   ⟨rtb_9_eq, rtb_strict_9_eq, rtb_9_lt_printed, v9_isBalanced, v9_usesAllLetters,
      v9_critExp_eq.1, v9_critExp_eq.2⟩,
   ⟨rtb_10_eq, rtb_strict_10_eq, rtb_10_lt_printed, v10_isBalanced, v10_usesAllLetters,
      v10_critExp_eq.1, v10_critExp_eq.2⟩⟩

end BalancedRepetitionThreshold
