module

public import BalancedRepetitionThreshold.LowerBoundEngine

import Mathlib.Tactic

/-!
# Pure-Kernel Lower-Bound Witness Tree for `d = 7` (`RTB(7) ≥ 6/5`)

Replays the complete finite refutation tree of `905` nodes (`19` pure-kernel `decide`
chunks, max `133` nodes/chunk, zero `native_decide`, zero `set_option`) to prove
unconditionally that every 1-balanced sequence over `Fin 7` has critical exponent `≥ 6/5`.
-/

@[expose] public section

namespace BalancedRepetitionThreshold

private def cert_d7_8 : LowerCert :=
  .rep 2 6

private theorem ok_d7_8 : checkLowerCert 7 6 [1, 0, 5, 4, 3, 2, 1, 0] cert_d7_8 = true := by
  decide

private theorem ref_d7_8 : IsRefuted 7 6 [1, 0, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 6 [1, 0, 5, 4, 3, 2, 1, 0] cert_d7_8 ok_d7_8

private def cert_d7_11 : LowerCert :=
  .rep 2 7

private theorem ok_d7_11 : checkLowerCert 7 7 [2, 1, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_11 = true := by
  decide

private theorem ref_d7_11 : IsRefuted 7 7 [2, 1, 6, 0, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [2, 1, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_11 ok_d7_11

private def cert_d7_14 : LowerCert :=
  .branch [.branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 2, .branch [.rep 2 7, .branch [.rep 2 6, .branch [.branch [.branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 2, .branch [.branch [.rep 2 6, .branch [.branch [.branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 32, .unbal 26 13 0], .rep 2 6], .rep 2 7], .unbal 7 7 3], .rep 2 6], .rep 2 7], .unbal 7 7 0]], .branch [.unbal 14 7 4, .rep 2 7]], .rep 2 6], .rep 2 7], .unbal 7 7 1]], .rep 2 7]]], .branch [.rep 2 7, .unbal 14 7 3]], .rep 2 6], .rep 2 7], .unbal 7 7 0]]]]], .branch [.rep 2 7, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 14 7 1, .branch [.branch [.branch [.branch [.branch [.branch [.rep 6 30, .unbal 14 7 6], .rep 2 6], .rep 2 7], .unbal 14 7 4], .rep 2 6], .rep 2 7]], .rep 2 6], .rep 2 7], .unbal 14 7 5], .rep 2 6], .rep 2 7], .unbal 14 7 2]], .rep 2 7], .unbal 14 7 6], .rep 2 6], .rep 2 7], .branch [.rep 2 6, .branch [.branch [.rep 2 7, .unbal 14 7 6], .unbal 7 7 0]]], .rep 2 6]]], .rep 2 6], .rep 2 7]

private theorem ok_d7_14 : checkLowerCert 7 7 [4, 2, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_14 = true := by
  decide

private theorem ref_d7_14 : IsRefuted 7 7 [4, 2, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [4, 2, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_14 ok_d7_14

private def cert_d7_15 : LowerCert :=
  .branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 2, .branch [.rep 2 7, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 2, .branch [.branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 32, .rep 2 7], .unbal 7 7 5], .rep 2 6], .branch [.rep 2 7, .unbal 14 7 3]], .rep 2 6], .rep 2 7], .unbal 7 7 0]], .rep 2 7], .unbal 7 7 3]], .branch [.rep 2 7, .unbal 14 7 1]], .rep 2 6], .rep 2 7]]], .rep 2 7], .unbal 7 7 1]], .branch [.rep 2 7, .unbal 14 7 0]], .rep 2 6]]]], .rep 2 7], .unbal 7 7 0]]

private theorem ok_d7_15 : checkLowerCert 7 7 [5, 2, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_15 = true := by
  decide

private theorem ref_d7_15 : IsRefuted 7 7 [5, 2, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [5, 2, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_15 ok_d7_15

private theorem ref_d7_13 : IsRefuted 7 7 [2, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d7_14 ref_d7_15

private def cert_d7_16 : LowerCert :=
  .rep 2 6

private theorem ok_d7_16 : checkLowerCert 7 7 [4, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_16 = true := by
  decide

private theorem ref_d7_16 : IsRefuted 7 7 [4, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [4, 3, 1, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_16 ok_d7_16

private theorem ref_d7_12 : IsRefuted 7 7 [3, 1, 6, 0, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d7_13 ref_d7_16

private theorem ref_d7_10 : IsRefuted 7 7 [1, 6, 0, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d7_11 ref_d7_12

private def cert_d7_17 : LowerCert :=
  .branch [.branch [.branch [.rep 2 7, .branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.rep 2 7, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.unbal 14 7 1, .rep 2 7], .unbal 7 7 2]], .branch [.rep 2 7, .unbal 14 7 0]], .rep 2 6]], .branch [.branch [.unbal 7 7 4, .branch [.branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.unbal 14 7 5, .rep 2 7], .branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 32, .rep 2 7], .unbal 7 7 5], .rep 2 6], .rep 2 7], .unbal 7 7 2], .rep 2 6], .branch [.rep 2 7, .unbal 14 7 0]]], .rep 2 7], .unbal 7 7 3]], .rep 2 7], .unbal 7 7 0]]]], .rep 2 7], .unbal 7 7 2]], .rep 2 7]], .rep 2 6]]], .rep 2 7], .unbal 7 7 0]]], .branch [.branch [.branch [.branch [.branch [.rep 2 6, .branch [.branch [.unbal 7 7 3, .rep 2 7], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.branch [.branch [.rep 5 24, .branch [.rep 2 7, .unbal 7 7 4]], .rep 2 6], .branch [.rep 2 7, .unbal 7 7 2]], .rep 2 6], .branch [.rep 2 7, .unbal 7 7 0]]], .branch [.unbal 7 7 1, .rep 2 7]], .rep 2 6], .branch [.rep 2 7, .unbal 7 7 2]], .rep 2 6], .branch [.rep 2 7, .unbal 7 7 0]], .rep 2 6]]], .branch [.unbal 7 7 1, .rep 2 7]], .rep 2 6], .branch [.rep 2 7, .unbal 7 7 0]], .rep 2 6]], .rep 2 6]

private theorem ok_d7_17 : checkLowerCert 7 7 [2, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_17 = true := by
  decide

private theorem ref_d7_17 : IsRefuted 7 7 [2, 6, 0, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [2, 6, 0, 5, 4, 3, 2, 1, 0] cert_d7_17 ok_d7_17

private theorem ref_d7_9 : IsRefuted 7 7 [6, 0, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d7_10 ref_d7_17

private theorem ref_d7_7 : IsRefuted 7 6 [0, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d7_8 ref_d7_9

private def cert_d7_20 : LowerCert :=
  .rep 2 7

private theorem ok_d7_20 : checkLowerCert 7 7 [1, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_20 = true := by
  decide

private theorem ref_d7_20 : IsRefuted 7 7 [1, 0, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [1, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_20 ok_d7_20

private def cert_d7_24 : LowerCert :=
  .rep 2 7

private theorem ok_d7_24 : checkLowerCert 7 7 [4, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_24 = true := by
  decide

private theorem ref_d7_24 : IsRefuted 7 7 [4, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [4, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_24 ok_d7_24

private def cert_d7_27 : LowerCert :=
  .branch [.rep 2 6, .branch [.unbal 7 7 1, .branch [.rep 2 7, .branch [.branch [.unbal 7 7 4, .branch [.branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 1, .branch [.rep 2 7, .branch [.rep 2 6, .branch [.branch [.branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 6, .rep 7 32], .branch [.unbal 14 7 5, .rep 2 7]], .rep 2 6], .rep 2 7], .unbal 7 7 2], .rep 2 6], .rep 2 7]]], .branch [.rep 2 7, .unbal 14 7 3]], .rep 2 6], .rep 2 7], .unbal 7 7 0]]]]], .branch [.rep 2 7, .unbal 14 7 2]], .rep 2 6], .rep 2 7]], .rep 2 6]]]]

private theorem ok_d7_27 : checkLowerCert 7 7 [0, 4, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_27 = true := by
  decide

private theorem ref_d7_27 : IsRefuted 7 7 [0, 4, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [0, 4, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_27 ok_d7_27

private def cert_d7_28 : LowerCert :=
  .branch [.rep 2 7, .branch [.branch [.branch [.rep 2 7, .branch [.branch [.branch [.branch [.rep 2 6, .branch [.branch [.rep 2 7, .branch [.branch [.branch [.branch [.branch [.unbal 14 7 0, .branch [.rep 2 7, .branch [.branch [.branch [.branch [.branch [.branch [.rep 6 30, .rep 2 7], .unbal 14 7 6], .rep 2 6], .rep 2 7], .unbal 14 7 3], .rep 2 6]]], .rep 2 6], .rep 2 7], .unbal 14 7 4], .rep 2 6]], .unbal 14 7 1]], .rep 2 7], .branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .unbal 14 7 1]]]], .rep 2 6]], .branch [.branch [.unbal 7 7 4, .branch [.rep 2 7, .branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .branch [.branch [.branch [.rep 2 7, .unbal 14 7 5], .branch [.branch [.unbal 7 7 4, .branch [.branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .branch [.branch [.branch [.unbal 14 7 6, .rep 2 7], .branch [.branch [.branch [.branch [.branch [.unbal 7 7 0, .branch [.rep 2 7, .unbal 26 13 6]], .rep 2 6], .rep 2 7], .unbal 7 7 2], .rep 2 6]], .rep 2 6]]]], .rep 2 7]], .rep 2 6]], .rep 2 6]]]]]], .rep 2 6]], .rep 2 6]]

private theorem ok_d7_28 : checkLowerCert 7 7 [6, 4, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_28 = true := by
  decide

private theorem ref_d7_28 : IsRefuted 7 7 [6, 4, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [6, 4, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_28 ok_d7_28

private theorem ref_d7_26 : IsRefuted 7 7 [4, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d7_27 ref_d7_28

private def cert_d7_29 : LowerCert :=
  .rep 2 6

private theorem ok_d7_29 : checkLowerCert 7 7 [6, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_29 = true := by
  decide

private theorem ref_d7_29 : IsRefuted 7 7 [6, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [6, 5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_29 ok_d7_29

private theorem ref_d7_25 : IsRefuted 7 7 [5, 3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d7_26 ref_d7_29

private theorem ref_d7_23 : IsRefuted 7 7 [3, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d7_24 ref_d7_25

private def cert_d7_30 : LowerCert :=
  .branch [.branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 1, .branch [.rep 2 7, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 1, .branch [.rep 2 7, .unbal 14 7 3]]], .branch [.rep 2 7, .unbal 14 7 2]], .rep 2 6], .rep 2 7], .branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 1, .branch [.rep 2 7, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 6, .rep 7 32], .rep 2 7], .unbal 7 7 4], .rep 2 6], .branch [.rep 2 7, .unbal 14 7 2]], .rep 2 6], .rep 2 7]]], .rep 2 7], .unbal 7 7 2]], .branch [.rep 2 7, .unbal 14 7 0]], .rep 2 6]]]], .rep 2 7], .unbal 7 7 0]]], .rep 2 6]]]], .rep 2 7], .branch [.rep 2 6, .branch [.branch [.unbal 7 7 1, .rep 2 7], .branch [.branch [.branch [.unbal 7 7 3, .rep 2 7], .branch [.branch [.branch [.unbal 7 7 5, .rep 2 7], .branch [.branch [.branch [.rep 2 6, .branch [.branch [.unbal 7 7 1, .rep 2 7], .branch [.branch [.branch [.unbal 7 7 3, .rep 2 7], .branch [.branch [.branch [.branch [.branch [.rep 2 6, .rep 5 24], .branch [.unbal 7 7 0, .rep 2 7]], .rep 2 6], .branch [.rep 2 7, .unbal 7 7 2]], .rep 2 6]], .rep 2 6]]], .branch [.unbal 7 7 0, .rep 2 7]], .rep 2 6]], .rep 2 6]], .rep 2 6]]]], .rep 2 6]

private theorem ok_d7_30 : checkLowerCert 7 7 [4, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_30 = true := by
  decide

private theorem ref_d7_30 : IsRefuted 7 7 [4, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [4, 1, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_30 ok_d7_30

private theorem ref_d7_22 : IsRefuted 7 7 [1, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d7_23 ref_d7_30

private def cert_d7_31 : LowerCert :=
  .rep 2 6

private theorem ok_d7_31 : checkLowerCert 7 7 [3, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_31 = true := by
  decide

private theorem ref_d7_31 : IsRefuted 7 7 [3, 2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [3, 2, 0, 6, 5, 4, 3, 2, 1, 0] cert_d7_31 ok_d7_31

private theorem ref_d7_21 : IsRefuted 7 7 [2, 0, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d7_22 ref_d7_31

private theorem ref_d7_19 : IsRefuted 7 7 [0, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d7_20 ref_d7_21

private def cert_d7_35 : LowerCert :=
  .rep 2 7

private theorem ok_d7_35 : checkLowerCert 7 7 [3, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_35 = true := by
  decide

private theorem ref_d7_35 : IsRefuted 7 7 [3, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [3, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_35 ok_d7_35

private def cert_d7_38 : LowerCert :=
  .branch [.branch [.rep 2 6, .branch [.branch [.rep 2 7, .branch [.branch [.branch [.branch [.branch [.unbal 14 7 0, .branch [.rep 2 7, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 6, .branch [.branch [.branch [.branch [.branch [.branch [.rep 6 30, .rep 2 6], .rep 2 7], .unbal 14 7 5], .rep 2 6], .rep 2 7], .unbal 14 7 2]], .rep 2 7], .unbal 14 7 6], .rep 2 6], .rep 2 7], .unbal 14 7 3], .rep 2 6]]], .rep 2 6], .rep 2 7], .branch [.rep 2 6, .branch [.branch [.unbal 14 7 0, .rep 2 7], .unbal 7 7 1]]], .rep 2 6]], .branch [.branch [.unbal 7 7 3, .branch [.rep 2 7, .branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.rep 2 7, .unbal 14 7 4], .branch [.branch [.unbal 7 7 3, .branch [.branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.branch [.unbal 14 7 5, .rep 2 7], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 6, .rep 7 32], .rep 2 7], .unbal 7 7 4], .rep 2 6], .rep 2 7], .unbal 7 7 1], .rep 2 6]]], .rep 2 7], .unbal 7 7 2]], .rep 2 7]], .rep 2 6]]], .rep 2 7], .unbal 7 7 1]]]], .rep 2 6]]], .rep 2 7]

private theorem ok_d7_38 : checkLowerCert 7 7 [5, 3, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_38 = true := by
  decide

private theorem ref_d7_38 : IsRefuted 7 7 [5, 3, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [5, 3, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_38 ok_d7_38

private def cert_d7_39 : LowerCert :=
  .branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .branch [.branch [.unbal 7 7 3, .branch [.rep 2 7, .branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .branch [.branch [.unbal 7 7 3, .branch [.branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 7 7 0, .rep 7 32], .rep 2 6], .branch [.rep 2 7, .unbal 14 7 4]], .rep 2 6], .rep 2 7], .unbal 7 7 1], .rep 2 6]]]], .branch [.rep 2 7, .unbal 14 7 2]], .rep 2 6], .rep 2 7]], .rep 2 6]]]], .branch [.rep 2 7, .unbal 14 7 1]], .rep 2 6]]], .rep 2 6]]]]

private theorem ok_d7_39 : checkLowerCert 7 7 [6, 3, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_39 = true := by
  decide

private theorem ref_d7_39 : IsRefuted 7 7 [6, 3, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [6, 3, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_39 ok_d7_39

private theorem ref_d7_37 : IsRefuted 7 7 [3, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d7_38 ref_d7_39

private def cert_d7_40 : LowerCert :=
  .rep 2 6

private theorem ok_d7_40 : checkLowerCert 7 7 [5, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_40 = true := by
  decide

private theorem ref_d7_40 : IsRefuted 7 7 [5, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [5, 4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_40 ok_d7_40

private theorem ref_d7_36 : IsRefuted 7 7 [4, 2, 0, 1, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d7_37 ref_d7_40

private theorem ref_d7_34 : IsRefuted 7 7 [2, 0, 1, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d7_35 ref_d7_36

private def cert_d7_41 : LowerCert :=
  .branch [.branch [.branch [.rep 2 7, .branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .branch [.branch [.branch [.rep 2 7, .branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .unbal 14 7 2]]], .branch [.rep 2 7, .unbal 14 7 1]], .rep 2 6]], .branch [.branch [.unbal 7 7 5, .branch [.branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .branch [.branch [.branch [.unbal 14 7 6, .rep 2 7], .branch [.rep 2 6, .branch [.branch [.branch [.rep 2 6, .branch [.unbal 7 7 0, .branch [.rep 2 7, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 7 7 0, .rep 7 32], .rep 2 6], .rep 2 7], .unbal 7 7 3], .rep 2 6], .branch [.rep 2 7, .unbal 14 7 1]], .rep 2 6]]]], .rep 2 7], .unbal 7 7 1]]], .rep 2 6]]]], .rep 2 7]], .rep 2 6]], .rep 2 6]]]]], .branch [.branch [.branch [.rep 2 6, .branch [.branch [.unbal 7 7 2, .rep 2 7], .branch [.branch [.branch [.unbal 7 7 4, .rep 2 7], .branch [.branch [.branch [.branch [.branch [.rep 2 6, .branch [.branch [.unbal 7 7 2, .rep 2 7], .branch [.branch [.branch [.branch [.branch [.rep 5 24, .rep 2 6], .branch [.rep 2 7, .unbal 7 7 3]], .rep 2 6], .branch [.rep 2 7, .unbal 7 7 1]], .rep 2 6]]], .branch [.unbal 7 7 0, .rep 2 7]], .rep 2 6], .branch [.rep 2 7, .unbal 7 7 1]], .rep 2 6]], .rep 2 6]]], .branch [.unbal 7 7 0, .rep 2 7]], .rep 2 6]], .rep 2 6]

private theorem ok_d7_41 : checkLowerCert 7 7 [3, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_41 = true := by
  decide

private theorem ref_d7_41 : IsRefuted 7 7 [3, 0, 1, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [3, 0, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_41 ok_d7_41

private theorem ref_d7_33 : IsRefuted 7 7 [0, 1, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d7_34 ref_d7_41

private def cert_d7_42 : LowerCert :=
  .rep 2 6

private theorem ok_d7_42 : checkLowerCert 7 7 [2, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_42 = true := by
  decide

private theorem ref_d7_42 : IsRefuted 7 7 [2, 1, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 7 [2, 1, 6, 5, 4, 3, 2, 1, 0] cert_d7_42 ok_d7_42

private theorem ref_d7_32 : IsRefuted 7 7 [1, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d7_33 ref_d7_42

private theorem ref_d7_18 : IsRefuted 7 7 [6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d7_19 ref_d7_32

private theorem ref_d7_6 : IsRefuted 7 6 [5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d7_7 ref_d7_18

private theorem ref_d7_5 : IsRefuted 7 5 [4, 3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 5) (by omega) (by decide) (by decide) ref_d7_6

private theorem ref_d7_4 : IsRefuted 7 4 [3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 4) (by omega) (by decide) (by decide) ref_d7_5

private theorem ref_d7_3 : IsRefuted 7 3 [2, 1, 0] :=
  isRefuted_split1 (c1 := 3) (by omega) (by decide) (by decide) ref_d7_4

private theorem ref_d7_2 : IsRefuted 7 2 [1, 0] :=
  isRefuted_split1 (c1 := 2) (by omega) (by decide) (by decide) ref_d7_3

private theorem ref_d7_1 : IsRefuted 7 1 [0] :=
  isRefuted_split1 (c1 := 1) (by omega) (by decide) (by decide) ref_d7_2

private theorem ref_d7_0 : IsRefuted 7 0 [] :=
  isRefuted_split1 (c1 := 0) (by omega) (by decide) (by decide) ref_d7_1

/-- The empty prefix over `Fin 7` is refuted at threshold `6/5`. -/
theorem isRefuted_7 : IsRefuted 7 0 [] :=
  ref_d7_0

/-- Every 1-balanced sequence over `Fin 7` has critical exponent at least `6/5`. -/
theorem critExp_ge_7 (w : ℕ → Fin 7) (hw : IsBalanced w) :
    (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ≤ critExp w := by
  have h := (rtb_ge_of_refuted (d := 7) (by omega) isRefuted_7).1 w hw
  simpa using h

/-- Lower bound `RTB 7 ≥ 6/5` (unconditional, zero recurrence/aperiodicity assumption). -/
theorem rtb_ge_7 : (((6 : ℝ) / (5 : ℝ) : ℝ) : EReal) ≤ RTB 7 := by
  have h := (rtb_ge_of_refuted (d := 7) (by omega) isRefuted_7).2
  simpa using h

end BalancedRepetitionThreshold
