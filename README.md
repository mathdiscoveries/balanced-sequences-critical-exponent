# Balanced-Sequence Repetition Threshold Refutation: Exact RTB(7) = 6/5, RTB(9) = 8/7, and RTB(10) = 9/8

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization establishing exact values of the
balanced-sequence repetition threshold $\mathrm{RTB}(d)$ for alphabets of size $d \in \{7, 9, 10\}$:

- $\mathrm{RTB}(7) = \mathrm{RTB}^*(7) = 6/5 < 5/4$, attained by the explicit word $v_7$,
- $\mathrm{RTB}(9) = \mathrm{RTB}^*(9) = 8/7 < 7/6$, attained by the explicit word $v_9$,
- $\mathrm{RTB}(10) = \mathrm{RTB}^*(10) = 9/8 < 8/7$, attained by the explicit word $v_{10}$,

refuting three of the six values $(d - 2)/(d - 3)$ listed as established for $5 \le d \le 10$
across papers from 2018 to 2023. The cases $d = 5, 6, 8$ and $d \ge 11$ are not addressed.

**Verification Scope (Full Lean 4 Kernel Coverage):** Main results in the companion paper:
6 of 6 in Lean 4 (100%) · 12 of 12 abstract claims in Lean 4 (100%) · 18 of 18 paper claims
in Lean 4 (100%) · 0 by external certificate · 0 by written proof. Within
`BalancedRepetitionThreshold`, 11 of 13 `.lean` files import Mathlib. All 26 compared theorems
in `Solution.lean` and all 193 public theorems in `BalancedRepetitionThreshold` build with zero
`sorry`, zero `native_decide`, and Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) only.

## Formalized Headline Results (`Challenge.lean` / `Solution.lean`)

1. **Exact balanced-sequence repetition thresholds** (`rtb_7_eq`, `rtb_9_eq`, `rtb_10_eq`):
   $\mathrm{RTB}(7) = 6/5$, $\mathrm{RTB}(9) = 8/7$, and $\mathrm{RTB}(10) = 9/8$ over all
   1-balanced sequences `w : ℕ → Fin d` (with no recurrence, aperiodicity, or alphabet-usage
   side hypothesis).
2. **Strict refutations of the listed values** (`rtb_7_lt_printed`, `rtb_9_lt_printed`,
   `rtb_10_lt_printed`): $\mathrm{RTB}(7) < 5/4$, $\mathrm{RTB}(9) < 7/6$, and
   $\mathrm{RTB}(10) < 8/7$.
3. **Strict all-letters thresholds** (`rtb_strict_7_eq`, `rtb_strict_9_eq`,
   `rtb_strict_10_eq`): restricting to 1-balanced words that use all $d$ letters yields the
   same exact values $6/5$, $8/7$, and $9/8$.
4. **Universal lower bounds via kernel-checked finite witness trees** (`critExp_ge_7`,
   `critExp_ge_9`, `critExp_ge_10`): every 1-balanced sequence over `Fin 7`, `Fin 9`, or
   `Fin 10` has critical exponent at least $6/5$, $8/7$, or $9/8$, proved by exhaustive
   prefix-refutation trees of $905$, $2{,}941$, and $4{,}868$ nodes checked inside the Lean
   kernel without `native_decide`.
5. **Explicit 1-balanced Sturmian-colouring witnesses** (`v7_isBalanced`, `v9_isBalanced`,
   `v10_isBalanced`, `v7_usesAllLetters`, `v9_usesAllLetters`, `v10_usesAllLetters`,
   `v7_attains`, `v9_attains`, `v10_attains`, `v7_critExp_eq`, `v9_critExp_eq`,
   `v10_critExp_eq`):
   - $v_7$ colours `sturmian ((11 - √10) / 37)` by the periodic colourings of $x_7$ from
     Rampersad, Shallit, and Vandomme (`arXiv:1801.05334`, Table 1), attaining $E(v_7) = 6/5$
     on its prefix of length $6$ with period $5$.
   - $v_9$ colours `sturmian ((41 - 2√2) / 239)` by the periodic colourings of $x_9$ from
     Rampersad, Shallit, and Vandomme (`arXiv:1801.05334`, Table 1), attaining $E(v_9) = 8/7$
     on its prefix of length $8$ with period $7$.
   - $v_{10}$ colours `sturmian ((7 + √5) / 22)` by $(0,1,2,3,4)^\omega$ and
     $(5,6,7,8,9)^\omega$ (the $\delta = 5$ instance of the $x_{2\delta}$ colouring family of
     Dvořáková, Pelantová, Opočenská, and Shur, `arXiv:2112.02854`, Theorem 19), attaining
     $E(v_{10}) = 9/8$ at index $4$ with length $9$ and period $8$.
6. **Definition equivalence & combined bundle** (`sSup_minPeriodExponentSet_eq_critExp`,
   `r22_1_1_main`): proves that minimal-period and any-period critical exponent definitions
   coincide for every infinite sequence, and bundles all exact values, refutations, and
   witnesses into one headline theorem.

Companion working paper and verification archives live at
https://mathdiscoveries.org/results/balanced-sequences-critical-exponent.

## Build & Verify

```bash
lake build BalancedRepetitionThreshold Challenge Solution
lake env lean BalancedRepetitionThreshold/Verify.lean
```

## Disclosure & License

Generated and checked by AI research agents built and directed by **Tyler B. Hughes**. No
human mathematician has yet refereed the proof. Licensed under Apache-2.0.
