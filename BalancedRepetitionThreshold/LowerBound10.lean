module

public import BalancedRepetitionThreshold.LowerBoundEngine

import Mathlib.Tactic

/-!
# Pure-Kernel Lower-Bound Witness Tree for `d = 10` (`RTB(10) ≥ 9/8`)

Replays the complete finite refutation tree of `4868` nodes (`169` pure-kernel `decide`
chunks, max `139` nodes/chunk, zero `native_decide`, zero `set_option`) to prove
unconditionally that every 1-balanced sequence over `Fin 10` has critical exponent `≥ 9/8`.
-/

@[expose] public section

namespace BalancedRepetitionThreshold

private def cert_d10_11 : LowerCert :=
  .rep 2 9

private theorem ok_d10_11 : checkLowerCert 10 9 [1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_11 = true := by
  decide

private theorem ref_d10_11 : IsRefuted 10 9 [1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_11 ok_d10_11

private def cert_d10_14 : LowerCert :=
  .rep 2 10

private theorem ok_d10_14 : checkLowerCert 10 10 [2, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_14 = true := by
  decide

private theorem ref_d10_14 : IsRefuted 10 10 [2, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_14 ok_d10_14

private def cert_d10_18 : LowerCert :=
  .rep 2 10

private theorem ok_d10_18 : checkLowerCert 10 10 [5, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_18 = true := by
  decide

private theorem ref_d10_18 : IsRefuted 10 10 [5, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_18 ok_d10_18

private def cert_d10_24 : LowerCert :=
  .branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 5, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 5, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .rep 2 9], .rep 2 10], .unbal 10 10 6], .rep 2 9], .rep 2 10], .unbal 10 10 3], .rep 2 9], .rep 2 10], .unbal 10 10 0]], .branch [.unbal 20 10 7, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 10 10 4]], .rep 2 10], .unbal 10 10 1]], .rep 2 10]]], .branch [.rep 2 10, .unbal 20 10 6]], .rep 2 9], .rep 2 10], .unbal 10 10 3]], .rep 2 10], .unbal 10 10 0]]]]], .branch [.rep 2 10, .unbal 20 10 4]], .rep 2 9], .rep 2 10], .unbal 10 10 1]], .rep 2 10]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 3]], .rep 2 9], .rep 2 10], .unbal 10 10 0]]]], .rep 2 9]]]]

private theorem ok_d10_24 : checkLowerCert 10 10 [1, 8, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_24 = true := by
  decide

private theorem ref_d10_24 : IsRefuted 10 10 [1, 8, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 8, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_24 ok_d10_24

private def cert_d10_25 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 1, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 8 63, .rep 2 9], .rep 2 10], .unbal 20 10 7], .rep 2 9], .rep 2 10], .unbal 20 10 4], .rep 2 9], .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 20 10 8], .rep 2 9], .rep 2 10], .unbal 20 10 5], .rep 2 9], .rep 2 10], .unbal 20 10 2]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .rep 2 10], .unbal 20 10 7], .rep 2 9], .rep 2 10], .unbal 20 10 4], .rep 2 9]]], .rep 2 9], .rep 2 10], .unbal 20 10 8], .rep 2 9], .rep 2 10], .unbal 20 10 5], .rep 2 9]], .unbal 20 10 2]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .rep 2 10], .branch [.rep 2 9, .branch [.branch [.rep 2 10, .unbal 20 10 9], .unbal 10 10 0]]], .rep 2 9]], .branch [.branch [.unbal 10 10 5, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.rep 2 10, .unbal 20 10 9], .unbal 10 10 0]]]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_25 : checkLowerCert 10 10 [9, 8, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_25 = true := by
  decide

private theorem ref_d10_25 : IsRefuted 10 10 [9, 8, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_25 ok_d10_25

private theorem ref_d10_23 : IsRefuted 10 10 [8, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_24 ref_d10_25

private def cert_d10_26 : LowerCert :=
  .rep 2 9

private theorem ok_d10_26 : checkLowerCert 10 10 [9, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_26 = true := by
  decide

private theorem ref_d10_26 : IsRefuted 10 10 [9, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_26 ok_d10_26

private theorem ref_d10_22 : IsRefuted 10 10 [0, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_23 ref_d10_26

private def cert_d10_27 : LowerCert :=
  .rep 2 10

private theorem ok_d10_27 : checkLowerCert 10 10 [8, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_27 = true := by
  decide

private theorem ref_d10_27 : IsRefuted 10 10 [8, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_27 ok_d10_27

private theorem ref_d10_21 : IsRefuted 10 10 [7, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_22 ref_d10_27

private def cert_d10_28 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 5, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 5, .branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .unbal 10 10 8], .rep 2 9], .branch [.rep 2 10, .unbal 20 10 6]], .rep 2 9], .rep 2 10], .unbal 10 10 3], .rep 2 9], .rep 2 10], .unbal 10 10 0]], .rep 2 10], .unbal 10 10 6]], .branch [.rep 2 10, .unbal 20 10 4]], .rep 2 9], .rep 2 10], .unbal 10 10 1]], .rep 2 10]]], .rep 2 10], .unbal 10 10 4]], .branch [.rep 2 10, .unbal 20 10 3]], .rep 2 9], .rep 2 10], .unbal 10 10 0]]]]], .rep 2 10], .unbal 10 10 3]], .branch [.rep 2 10, .unbal 20 10 1]], .rep 2 9], .rep 2 10]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 1]], .branch [.rep 2 10, .unbal 20 10 0]], .rep 2 9]]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 0]]

private theorem ok_d10_28 : checkLowerCert 10 10 [8, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_28 = true := by
  decide

private theorem ref_d10_28 : IsRefuted 10 10 [8, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_28 ok_d10_28

private theorem ref_d10_20 : IsRefuted 10 10 [5, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_21 ref_d10_28

private def cert_d10_29 : LowerCert :=
  .rep 2 9

private theorem ok_d10_29 : checkLowerCert 10 10 [7, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_29 = true := by
  decide

private theorem ref_d10_29 : IsRefuted 10 10 [7, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_29 ok_d10_29

private theorem ref_d10_19 : IsRefuted 10 10 [6, 4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_20 ref_d10_29

private theorem ref_d10_17 : IsRefuted 10 10 [4, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_18 ref_d10_19

private def cert_d10_33 : LowerCert :=
  .rep 2 10

private theorem ok_d10_33 : checkLowerCert 10 10 [7, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_33 = true := by
  decide

private theorem ref_d10_33 : IsRefuted 10 10 [7, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_33 ok_d10_33

private def cert_d10_35 : LowerCert :=
  .rep 2 9

private theorem ok_d10_35 : checkLowerCert 10 10 [0, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_35 = true := by
  decide

private theorem ref_d10_35 : IsRefuted 10 10 [0, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_35 ok_d10_35

private def cert_d10_37 : LowerCert :=
  .branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .unbal 20 10 4]]], .rep 2 10], .unbal 10 10 1]], .branch [.rep 2 10, .unbal 20 10 0]], .rep 2 9]], .branch [.branch [.unbal 10 10 7, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 20 10 8, .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .unbal 10 10 8], .rep 2 9], .rep 2 10], .unbal 10 10 5], .rep 2 9], .branch [.rep 2 10, .unbal 20 10 3]], .rep 2 9], .rep 2 10], .unbal 10 10 0]], .rep 2 10], .unbal 10 10 6]], .rep 2 10], .unbal 10 10 3]], .branch [.rep 2 10, .unbal 20 10 1]], .rep 2 9], .rep 2 10]]], .rep 2 10], .unbal 10 10 5]], .rep 2 10], .unbal 10 10 1]], .branch [.rep 2 10, .unbal 20 10 0]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 3]], .rep 2 10], .unbal 10 10 0]]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 1]], .rep 2 10]], .rep 2 9]], .rep 2 9]]]], .rep 2 10]

private theorem ok_d10_37 : checkLowerCert 10 10 [0, 7, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_37 = true := by
  decide

private theorem ref_d10_37 : IsRefuted 10 10 [0, 7, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 7, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_37 ok_d10_37

private def cert_d10_38 : LowerCert :=
  .unbal 10 10 0

private theorem ok_d10_38 : checkLowerCert 10 10 [9, 7, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_38 = true := by
  decide

private theorem ref_d10_38 : IsRefuted 10 10 [9, 7, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 7, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_38 ok_d10_38

private theorem ref_d10_36 : IsRefuted 10 10 [7, 8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_37 ref_d10_38

private theorem ref_d10_34 : IsRefuted 10 10 [8, 6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_35 ref_d10_36

private theorem ref_d10_32 : IsRefuted 10 10 [6, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_33 ref_d10_34

private def cert_d10_43 : LowerCert :=
  .branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 6, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 2, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .rep 2 10], .unbal 10 10 0]], .unbal 19 19 7], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9], .rep 2 10]]], .unbal 19 19 5], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]], .rep 2 9]]]]

private theorem ok_d10_43 : checkLowerCert 10 10 [1, 8, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_43 = true := by
  decide

private theorem ref_d10_43 : IsRefuted 10 10 [1, 8, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 8, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_43 ok_d10_43

private def cert_d10_44 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 6, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .rep 2 10], .unbal 20 10 4], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .rep 2 10], .unbal 20 10 6], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 20 10 8], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]], .rep 2 9]]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_44 : checkLowerCert 10 10 [9, 8, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_44 = true := by
  decide

private theorem ref_d10_44 : IsRefuted 10 10 [9, 8, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_44 ok_d10_44

private theorem ref_d10_42 : IsRefuted 10 10 [8, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_43 ref_d10_44

private def cert_d10_45 : LowerCert :=
  .rep 2 9

private theorem ok_d10_45 : checkLowerCert 10 10 [9, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_45 = true := by
  decide

private theorem ref_d10_45 : IsRefuted 10 10 [9, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_45 ok_d10_45

private theorem ref_d10_41 : IsRefuted 10 10 [0, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_42 ref_d10_45

private def cert_d10_46 : LowerCert :=
  .branch [.rep 2 10, .unbal 10 10 0]

private theorem ok_d10_46 : checkLowerCert 10 10 [8, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_46 = true := by
  decide

private theorem ref_d10_46 : IsRefuted 10 10 [8, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_46 ok_d10_46

private theorem ref_d10_40 : IsRefuted 10 10 [6, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_41 ref_d10_46

private def cert_d10_47 : LowerCert :=
  .rep 2 9

private theorem ok_d10_47 : checkLowerCert 10 10 [8, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_47 = true := by
  decide

private theorem ref_d10_47 : IsRefuted 10 10 [8, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_47 ok_d10_47

private theorem ref_d10_39 : IsRefuted 10 10 [7, 4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_40 ref_d10_47

private theorem ref_d10_31 : IsRefuted 10 10 [4, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_32 ref_d10_39

private def cert_d10_48 : LowerCert :=
  .rep 2 9

private theorem ok_d10_48 : checkLowerCert 10 10 [6, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_48 = true := by
  decide

private theorem ref_d10_48 : IsRefuted 10 10 [6, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_48 ok_d10_48

private theorem ref_d10_30 : IsRefuted 10 10 [5, 2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_31 ref_d10_48

private theorem ref_d10_16 : IsRefuted 10 10 [2, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_17 ref_d10_30

private def cert_d10_49 : LowerCert :=
  .rep 2 9

private theorem ok_d10_49 : checkLowerCert 10 10 [4, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_49 = true := by
  decide

private theorem ref_d10_49 : IsRefuted 10 10 [4, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_49 ok_d10_49

private theorem ref_d10_15 : IsRefuted 10 10 [3, 1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_16 ref_d10_49

private theorem ref_d10_13 : IsRefuted 10 10 [1, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_14 ref_d10_15

private def cert_d10_53 : LowerCert :=
  .rep 2 10

private theorem ok_d10_53 : checkLowerCert 10 10 [4, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_53 = true := by
  decide

private theorem ref_d10_53 : IsRefuted 10 10 [4, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_53 ok_d10_53

private def cert_d10_57 : LowerCert :=
  .rep 2 10

private theorem ok_d10_57 : checkLowerCert 10 10 [7, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_57 = true := by
  decide

private theorem ref_d10_57 : IsRefuted 10 10 [7, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_57 ok_d10_57

private def cert_d10_59 : LowerCert :=
  .rep 2 9

private theorem ok_d10_59 : checkLowerCert 10 10 [0, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_59 = true := by
  decide

private theorem ref_d10_59 : IsRefuted 10 10 [0, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_59 ok_d10_59

private def cert_d10_63 : LowerCert :=
  .rep 2 9

private theorem ok_d10_63 : checkLowerCert 10 10 [1, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_63 = true := by
  decide

private theorem ref_d10_63 : IsRefuted 10 10 [1, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_63 ok_d10_63

private def cert_d10_65 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 20 10 1, .rep 2 10], .unbal 10 10 2]], .branch [.rep 2 10, .unbal 20 10 0]], .rep 2 9]], .branch [.branch [.unbal 10 10 7, .branch [.branch [.rep 2 9, .branch [.branch [.unbal 20 10 1, .rep 2 10], .unbal 10 10 2]], .rep 2 10]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_65 : checkLowerCert 10 10 [1, 9, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_65 = true := by
  decide

private theorem ref_d10_65 : IsRefuted 10 10 [1, 9, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 9, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_65 ok_d10_65

private def cert_d10_66 : LowerCert :=
  .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 7, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .unbal 20 10 5], .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .unbal 20 10 6], .branch [.branch [.unbal 10 10 4, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 20 10 8, .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .unbal 10 10 8], .rep 2 9], .rep 2 10], .unbal 10 10 5], .rep 2 9], .rep 2 10], .unbal 10 10 2], .rep 2 9], .branch [.rep 2 10, .unbal 20 10 0]]], .rep 2 10], .unbal 10 10 6]], .rep 2 10], .unbal 10 10 3]], .rep 2 10], .unbal 10 10 0]]]], .rep 2 10], .unbal 10 10 5]], .rep 2 10], .unbal 10 10 2]], .rep 2 10]], .rep 2 9]]], .rep 2 10], .unbal 10 10 3]], .rep 2 10], .unbal 10 10 0]]]], .rep 2 9]]], .rep 2 10], .unbal 10 10 2]], .rep 2 10]], .rep 2 9]]], .rep 2 9]

private theorem ok_d10_66 : checkLowerCert 10 10 [3, 9, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_66 = true := by
  decide

private theorem ref_d10_66 : IsRefuted 10 10 [3, 9, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 9, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_66 ok_d10_66

private theorem ref_d10_64 : IsRefuted 10 10 [9, 2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_65 ref_d10_66

private theorem ref_d10_62 : IsRefuted 10 10 [2, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_63 ref_d10_64

private def cert_d10_67 : LowerCert :=
  .rep 2 10

private theorem ok_d10_67 : checkLowerCert 10 10 [9, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_67 = true := by
  decide

private theorem ref_d10_67 : IsRefuted 10 10 [9, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_67 ok_d10_67

private theorem ref_d10_61 : IsRefuted 10 10 [0, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_62 ref_d10_67

private def cert_d10_68 : LowerCert :=
  .unbal 10 10 0

private theorem ok_d10_68 : checkLowerCert 10 10 [9, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_68 = true := by
  decide

private theorem ref_d10_68 : IsRefuted 10 10 [9, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_68 ok_d10_68

private theorem ref_d10_60 : IsRefuted 10 10 [7, 8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_61 ref_d10_68

private theorem ref_d10_58 : IsRefuted 10 10 [8, 6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_59 ref_d10_60

private theorem ref_d10_56 : IsRefuted 10 10 [6, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_57 ref_d10_58

private def cert_d10_74 : LowerCert :=
  .rep 2 9

private theorem ok_d10_74 : checkLowerCert 10 10 [1, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_74 = true := by
  decide

private theorem ref_d10_74 : IsRefuted 10 10 [1, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_74 ok_d10_74

private def cert_d10_76 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 6, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 1, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .rep 2 9], .rep 2 10], .unbal 20 10 6], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 20 10 8], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]], .rep 2 9]]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_76 : checkLowerCert 10 10 [1, 9, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_76 = true := by
  decide

private theorem ref_d10_76 : IsRefuted 10 10 [1, 9, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 9, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_76 ok_d10_76

private def cert_d10_77 : LowerCert :=
  .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .unbal 20 10 5], .branch [.branch [.unbal 10 10 4, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 19 19 7, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .rep 2 10], .unbal 10 10 2], .rep 2 9], .unbal 19 19 0]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .rep 2 10], .unbal 10 10 0]]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .rep 2 10]], .rep 2 9]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]]], .rep 2 9]

private theorem ok_d10_77 : checkLowerCert 10 10 [3, 9, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_77 = true := by
  decide

private theorem ref_d10_77 : IsRefuted 10 10 [3, 9, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 9, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_77 ok_d10_77

private theorem ref_d10_75 : IsRefuted 10 10 [9, 2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_76 ref_d10_77

private theorem ref_d10_73 : IsRefuted 10 10 [2, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_74 ref_d10_75

private def cert_d10_78 : LowerCert :=
  .branch [.unbal 10 10 1, .rep 2 10]

private theorem ok_d10_78 : checkLowerCert 10 10 [9, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_78 = true := by
  decide

private theorem ref_d10_78 : IsRefuted 10 10 [9, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_78 ok_d10_78

private theorem ref_d10_72 : IsRefuted 10 10 [8, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_73 ref_d10_78

private def cert_d10_79 : LowerCert :=
  .rep 2 9

private theorem ok_d10_79 : checkLowerCert 10 10 [9, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_79 = true := by
  decide

private theorem ref_d10_79 : IsRefuted 10 10 [9, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_79 ok_d10_79

private theorem ref_d10_71 : IsRefuted 10 10 [0, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_72 ref_d10_79

private def cert_d10_80 : LowerCert :=
  .branch [.rep 2 10, .unbal 10 10 0]

private theorem ok_d10_80 : checkLowerCert 10 10 [8, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_80 = true := by
  decide

private theorem ref_d10_80 : IsRefuted 10 10 [8, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_80 ok_d10_80

private theorem ref_d10_70 : IsRefuted 10 10 [6, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_71 ref_d10_80

private def cert_d10_81 : LowerCert :=
  .rep 2 9

private theorem ok_d10_81 : checkLowerCert 10 10 [8, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_81 = true := by
  decide

private theorem ref_d10_81 : IsRefuted 10 10 [8, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_81 ok_d10_81

private theorem ref_d10_69 : IsRefuted 10 10 [7, 4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_70 ref_d10_81

private theorem ref_d10_55 : IsRefuted 10 10 [4, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_56 ref_d10_69

private def cert_d10_82 : LowerCert :=
  .rep 2 9

private theorem ok_d10_82 : checkLowerCert 10 10 [6, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_82 = true := by
  decide

private theorem ref_d10_82 : IsRefuted 10 10 [6, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_82 ok_d10_82

private theorem ref_d10_54 : IsRefuted 10 10 [5, 3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_55 ref_d10_82

private theorem ref_d10_52 : IsRefuted 10 10 [3, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_53 ref_d10_54

private def cert_d10_86 : LowerCert :=
  .rep 2 10

private theorem ok_d10_86 : checkLowerCert 10 10 [6, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_86 = true := by
  decide

private theorem ref_d10_86 : IsRefuted 10 10 [6, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_86 ok_d10_86

private def cert_d10_92 : LowerCert :=
  .rep 2 9

private theorem ok_d10_92 : checkLowerCert 10 10 [1, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_92 = true := by
  decide

private theorem ref_d10_92 : IsRefuted 10 10 [1, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_92 ok_d10_92

private def cert_d10_94 : LowerCert :=
  .branch [.unbal 10 10 3, .rep 2 10]

private theorem ok_d10_94 : checkLowerCert 10 10 [1, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_94 = true := by
  decide

private theorem ref_d10_94 : IsRefuted 10 10 [1, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_94 ok_d10_94

private def cert_d10_97 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 1, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .unbal 20 10 8], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]], .unbal 20 10 3]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]]

private theorem ok_d10_97 : checkLowerCert 10 10 [3, 1, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_97 = true := by
  decide

private theorem ref_d10_97 : IsRefuted 10 10 [3, 1, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 1, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_97 ok_d10_97

private def cert_d10_98 : LowerCert :=
  .branch [.branch [.unbal 10 10 6, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 20 10 7, .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .rep 2 9], .rep 2 10], .unbal 10 10 4], .rep 2 9], .unbal 19 19 2], .rep 2 9], .unbal 28 28 0]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .rep 2 10], .unbal 10 10 2]], .unbal 19 19 0], .rep 2 9]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .rep 2 10], .unbal 10 10 0]]], .rep 2 9]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .rep 2 10]], .rep 2 9]

private theorem ok_d10_98 : checkLowerCert 10 10 [5, 1, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_98 = true := by
  decide

private theorem ref_d10_98 : IsRefuted 10 10 [5, 1, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 1, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_98 ok_d10_98

private theorem ref_d10_96 : IsRefuted 10 10 [1, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_97 ref_d10_98

private def cert_d10_99 : LowerCert :=
  .rep 2 9

private theorem ok_d10_99 : checkLowerCert 10 10 [3, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_99 = true := by
  decide

private theorem ref_d10_99 : IsRefuted 10 10 [3, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_99 ok_d10_99

private theorem ref_d10_95 : IsRefuted 10 10 [4, 9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_96 ref_d10_99

private theorem ref_d10_93 : IsRefuted 10 10 [9, 2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_94 ref_d10_95

private theorem ref_d10_91 : IsRefuted 10 10 [2, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_92 ref_d10_93

private def cert_d10_100 : LowerCert :=
  .branch [.unbal 10 10 1, .rep 2 10]

private theorem ok_d10_100 : checkLowerCert 10 10 [9, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_100 = true := by
  decide

private theorem ref_d10_100 : IsRefuted 10 10 [9, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_100 ok_d10_100

private theorem ref_d10_90 : IsRefuted 10 10 [8, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_91 ref_d10_100

private def cert_d10_101 : LowerCert :=
  .rep 2 9

private theorem ok_d10_101 : checkLowerCert 10 10 [9, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_101 = true := by
  decide

private theorem ref_d10_101 : IsRefuted 10 10 [9, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_101 ok_d10_101

private theorem ref_d10_89 : IsRefuted 10 10 [0, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_90 ref_d10_101

private def cert_d10_102 : LowerCert :=
  .branch [.rep 2 10, .unbal 10 10 0]

private theorem ok_d10_102 : checkLowerCert 10 10 [8, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_102 = true := by
  decide

private theorem ref_d10_102 : IsRefuted 10 10 [8, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_102 ok_d10_102

private theorem ref_d10_88 : IsRefuted 10 10 [6, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_89 ref_d10_102

private def cert_d10_103 : LowerCert :=
  .rep 2 9

private theorem ok_d10_103 : checkLowerCert 10 10 [8, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_103 = true := by
  decide

private theorem ref_d10_103 : IsRefuted 10 10 [8, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_103 ok_d10_103

private theorem ref_d10_87 : IsRefuted 10 10 [7, 5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_88 ref_d10_103

private theorem ref_d10_85 : IsRefuted 10 10 [5, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_86 ref_d10_87

private def cert_d10_110 : LowerCert :=
  .rep 2 9

private theorem ok_d10_110 : checkLowerCert 10 10 [1, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_110 = true := by
  decide

private theorem ref_d10_110 : IsRefuted 10 10 [1, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_110 ok_d10_110

private def cert_d10_112 : LowerCert :=
  .branch [.unbal 10 10 3, .rep 2 10]

private theorem ok_d10_112 : checkLowerCert 10 10 [1, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_112 = true := by
  decide

private theorem ref_d10_112 : IsRefuted 10 10 [1, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_112 ok_d10_112

private def cert_d10_115 : LowerCert :=
  .branch [.unbal 10 10 5, .rep 2 10]

private theorem ok_d10_115 : checkLowerCert 10 10 [3, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_115 = true := by
  decide

private theorem ref_d10_115 : IsRefuted 10 10 [3, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_115 ok_d10_115

private def cert_d10_118 : LowerCert :=
  .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .branch [.rep 2 10, .unbal 10 10 6]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 6]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .rep 2 10], .unbal 20 10 3]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .rep 2 10], .unbal 20 10 5], .rep 2 9]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .rep 2 10]

private theorem ok_d10_118 : checkLowerCert 10 10 [5, 3, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_118 = true := by
  decide

private theorem ref_d10_118 : IsRefuted 10 10 [5, 3, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 3, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_118 ok_d10_118

private def cert_d10_119 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .unbal 10 10 6], .rep 2 9], .unbal 19 19 4], .rep 2 9], .unbal 28 28 2], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 10 10 4]], .unbal 19 19 2], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 10 10 2]], .unbal 19 19 0], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 1, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 10 10 0]]

private theorem ok_d10_119 : checkLowerCert 10 10 [7, 3, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_119 = true := by
  decide

private theorem ref_d10_119 : IsRefuted 10 10 [7, 3, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 3, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_119 ok_d10_119

private theorem ref_d10_117 : IsRefuted 10 10 [3, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_118 ref_d10_119

private def cert_d10_120 : LowerCert :=
  .rep 2 9

private theorem ok_d10_120 : checkLowerCert 10 10 [5, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_120 = true := by
  decide

private theorem ref_d10_120 : IsRefuted 10 10 [5, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_120 ok_d10_120

private theorem ref_d10_116 : IsRefuted 10 10 [6, 1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_117 ref_d10_120

private theorem ref_d10_114 : IsRefuted 10 10 [1, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_115 ref_d10_116

private def cert_d10_121 : LowerCert :=
  .rep 2 9

private theorem ok_d10_121 : checkLowerCert 10 10 [3, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_121 = true := by
  decide

private theorem ref_d10_121 : IsRefuted 10 10 [3, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_121 ok_d10_121

private theorem ref_d10_113 : IsRefuted 10 10 [4, 9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_114 ref_d10_121

private theorem ref_d10_111 : IsRefuted 10 10 [9, 2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_112 ref_d10_113

private theorem ref_d10_109 : IsRefuted 10 10 [2, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_110 ref_d10_111

private def cert_d10_122 : LowerCert :=
  .branch [.unbal 10 10 1, .rep 2 10]

private theorem ok_d10_122 : checkLowerCert 10 10 [9, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_122 = true := by
  decide

private theorem ref_d10_122 : IsRefuted 10 10 [9, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_122 ok_d10_122

private theorem ref_d10_108 : IsRefuted 10 10 [8, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_109 ref_d10_122

private def cert_d10_123 : LowerCert :=
  .rep 2 9

private theorem ok_d10_123 : checkLowerCert 10 10 [9, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_123 = true := by
  decide

private theorem ref_d10_123 : IsRefuted 10 10 [9, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_123 ok_d10_123

private theorem ref_d10_107 : IsRefuted 10 10 [0, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_108 ref_d10_123

private def cert_d10_124 : LowerCert :=
  .rep 2 10

private theorem ok_d10_124 : checkLowerCert 10 10 [8, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_124 = true := by
  decide

private theorem ref_d10_124 : IsRefuted 10 10 [8, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_124 ok_d10_124

private theorem ref_d10_106 : IsRefuted 10 10 [7, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_107 ref_d10_124

private def cert_d10_125 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 7, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .unbal 19 19 6], .rep 2 9], .unbal 28 28 4], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]]], .rep 2 10], .unbal 10 10 6]], .unbal 19 19 4], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]]], .rep 2 10], .unbal 10 10 4]], .unbal 19 19 2], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]], .rep 2 9]]], .rep 2 10], .unbal 10 10 2]], .branch [.rep 2 10, .unbal 20 10 0]], .rep 2 9]], .rep 2 9]], .rep 2 9]]], .rep 2 10], .unbal 10 10 0]]

private theorem ok_d10_125 : checkLowerCert 10 10 [8, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_125 = true := by
  decide

private theorem ref_d10_125 : IsRefuted 10 10 [8, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_125 ok_d10_125

private theorem ref_d10_105 : IsRefuted 10 10 [5, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_106 ref_d10_125

private def cert_d10_126 : LowerCert :=
  .rep 2 9

private theorem ok_d10_126 : checkLowerCert 10 10 [7, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_126 = true := by
  decide

private theorem ref_d10_126 : IsRefuted 10 10 [7, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_126 ok_d10_126

private theorem ref_d10_104 : IsRefuted 10 10 [6, 3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_105 ref_d10_126

private theorem ref_d10_84 : IsRefuted 10 10 [3, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_85 ref_d10_104

private def cert_d10_127 : LowerCert :=
  .rep 2 9

private theorem ok_d10_127 : checkLowerCert 10 10 [5, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_127 = true := by
  decide

private theorem ref_d10_127 : IsRefuted 10 10 [5, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_127 ok_d10_127

private theorem ref_d10_83 : IsRefuted 10 10 [4, 1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_84 ref_d10_127

private theorem ref_d10_51 : IsRefuted 10 10 [1, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_52 ref_d10_83

private def cert_d10_128 : LowerCert :=
  .rep 2 9

private theorem ok_d10_128 : checkLowerCert 10 10 [3, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_128 = true := by
  decide

private theorem ref_d10_128 : IsRefuted 10 10 [3, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_128 ok_d10_128

private theorem ref_d10_50 : IsRefuted 10 10 [2, 9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_51 ref_d10_128

private theorem ref_d10_12 : IsRefuted 10 10 [9, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_13 ref_d10_50

private theorem ref_d10_10 : IsRefuted 10 9 [0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_11 ref_d10_12

private def cert_d10_131 : LowerCert :=
  .rep 2 10

private theorem ok_d10_131 : checkLowerCert 10 10 [1, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_131 = true := by
  decide

private theorem ref_d10_131 : IsRefuted 10 10 [1, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_131 ok_d10_131

private def cert_d10_135 : LowerCert :=
  .rep 2 10

private theorem ok_d10_135 : checkLowerCert 10 10 [4, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_135 = true := by
  decide

private theorem ref_d10_135 : IsRefuted 10 10 [4, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_135 ok_d10_135

private def cert_d10_139 : LowerCert :=
  .rep 2 10

private theorem ok_d10_139 : checkLowerCert 10 10 [7, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_139 = true := by
  decide

private theorem ref_d10_139 : IsRefuted 10 10 [7, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_139 ok_d10_139

private def cert_d10_142 : LowerCert :=
  .branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 7, .branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 4, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .branch [.unbal 20 10 8, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 10 10 5], .rep 2 9], .rep 2 10], .unbal 10 10 2], .rep 2 9], .rep 2 10]]], .branch [.rep 2 10, .unbal 20 10 6]], .rep 2 9], .rep 2 10], .unbal 10 10 3]], .rep 2 10], .unbal 10 10 0]]]]], .branch [.rep 2 10, .unbal 20 10 5]], .rep 2 9], .rep 2 10], .unbal 10 10 2]], .rep 2 10]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 3]], .rep 2 9], .rep 2 10], .unbal 10 10 0]]]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 2]], .rep 2 9], .rep 2 10]], .rep 2 9]]], .rep 2 9]]]]

private theorem ok_d10_142 : checkLowerCert 10 10 [0, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_142 = true := by
  decide

private theorem ref_d10_142 : IsRefuted 10 10 [0, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_142 ok_d10_142

private def cert_d10_144 : LowerCert :=
  .rep 2 10

private theorem ok_d10_144 : checkLowerCert 10 10 [0, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_144 = true := by
  decide

private theorem ref_d10_144 : IsRefuted 10 10 [0, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_144 ok_d10_144

private def cert_d10_147 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.unbal 20 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 8 63, .unbal 20 10 9], .rep 2 9], .rep 2 10], .unbal 20 10 6], .rep 2 9], .rep 2 10], .unbal 20 10 3], .rep 2 9]]], .rep 2 9], .rep 2 10], .unbal 20 10 7], .rep 2 9], .rep 2 10], .unbal 20 10 4], .rep 2 9]], .unbal 20 10 1]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .rep 2 10], .unbal 20 10 6], .rep 2 9]], .unbal 20 10 3], .rep 2 9]]], .rep 2 9], .rep 2 10], .unbal 20 10 7], .rep 2 9]], .unbal 20 10 4], .rep 2 9]], .unbal 20 10 1]], .rep 2 10], .branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .unbal 20 10 1]]]], .rep 2 9]], .branch [.branch [.unbal 10 10 7, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .unbal 20 10 1]]]]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_147 : checkLowerCert 10 10 [1, 0, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_147 = true := by
  decide

private theorem ref_d10_147 : IsRefuted 10 10 [1, 0, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 0, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_147 ok_d10_147

private def cert_d10_148 : LowerCert :=
  .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 7, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .unbal 20 10 5], .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 7, .branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .unbal 20 10 6], .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .unbal 20 10 8], .branch [.branch [.unbal 10 10 4, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 20 10 9, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 10 10 0, .branch [.rep 2 10, .rep 9 66]], .rep 2 9], .rep 2 10], .unbal 10 10 5], .rep 2 9], .rep 2 10], .unbal 10 10 2], .rep 2 9]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 3]], .rep 2 10]], .rep 2 9]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 2]]]], .rep 2 9]], .rep 2 9]]]], .rep 2 10]], .rep 2 9]]], .rep 2 9]], .rep 2 9]]]]]], .rep 2 9]]], .rep 2 9]

private theorem ok_d10_148 : checkLowerCert 10 10 [3, 0, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_148 = true := by
  decide

private theorem ref_d10_148 : IsRefuted 10 10 [3, 0, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 0, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_148 ok_d10_148

private theorem ref_d10_146 : IsRefuted 10 10 [0, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_147 ref_d10_148

private def cert_d10_149 : LowerCert :=
  .rep 2 9

private theorem ok_d10_149 : checkLowerCert 10 10 [1, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_149 = true := by
  decide

private theorem ref_d10_149 : IsRefuted 10 10 [1, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_149 ok_d10_149

private theorem ref_d10_145 : IsRefuted 10 10 [2, 9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d10_146 ref_d10_149

private theorem ref_d10_143 : IsRefuted 10 10 [9, 7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_144 ref_d10_145

private theorem ref_d10_141 : IsRefuted 10 10 [7, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_142 ref_d10_143

private def cert_d10_150 : LowerCert :=
  .rep 2 9

private theorem ok_d10_150 : checkLowerCert 10 10 [9, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_150 = true := by
  decide

private theorem ref_d10_150 : IsRefuted 10 10 [9, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_150 ok_d10_150

private theorem ref_d10_140 : IsRefuted 10 10 [8, 6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_141 ref_d10_150

private theorem ref_d10_138 : IsRefuted 10 10 [6, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_139 ref_d10_140

private def cert_d10_154 : LowerCert :=
  .branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .unbal 20 10 6]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 2]], .rep 2 9], .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 4, .branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .rep 2 10], .unbal 10 10 7], .rep 2 9], .branch [.rep 2 10, .unbal 20 10 5]], .rep 2 9], .rep 2 10], .unbal 10 10 2], .rep 2 9], .rep 2 10]]], .rep 2 10], .unbal 10 10 5]], .branch [.rep 2 10, .unbal 20 10 3]], .rep 2 9], .rep 2 10], .unbal 10 10 0]]]]], .rep 2 10], .unbal 10 10 3]], .branch [.rep 2 10, .unbal 20 10 2]], .rep 2 9], .rep 2 10]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 2]], .branch [.rep 2 10, .unbal 20 10 0]], .rep 2 9]]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 0]]], .rep 2 9]]], .rep 2 9]]]]

private theorem ok_d10_154 : checkLowerCert 10 10 [0, 8, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_154 = true := by
  decide

private theorem ref_d10_154 : IsRefuted 10 10 [0, 8, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 8, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_154 ok_d10_154

private def cert_d10_155 : LowerCert :=
  .rep 2 10

private theorem ok_d10_155 : checkLowerCert 10 10 [9, 8, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_155 = true := by
  decide

private theorem ref_d10_155 : IsRefuted 10 10 [9, 8, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_155 ok_d10_155

private theorem ref_d10_153 : IsRefuted 10 10 [8, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_154 ref_d10_155

private def cert_d10_157 : LowerCert :=
  .rep 2 9

private theorem ok_d10_157 : checkLowerCert 10 10 [0, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_157 = true := by
  decide

private theorem ref_d10_157 : IsRefuted 10 10 [0, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_157 ok_d10_157

private def cert_d10_159 : LowerCert :=
  .branch [.unbal 10 10 1, .rep 2 10]

private theorem ok_d10_159 : checkLowerCert 10 10 [0, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_159 = true := by
  decide

private theorem ref_d10_159 : IsRefuted 10 10 [0, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_159 ok_d10_159

private def cert_d10_162 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 6, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 8, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 6, .rep 2 10], .branch [.branch [.branch [.branch [.unbal 20 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 20 10 6], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]], .rep 2 9]]], .rep 2 10], .unbal 20 10 8], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]], .rep 2 9]], .rep 2 9]]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]], .rep 2 9]], .rep 2 9]], .unbal 20 10 1]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_162 : checkLowerCert 10 10 [1, 0, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_162 = true := by
  decide

private theorem ref_d10_162 : IsRefuted 10 10 [1, 0, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 0, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_162 ok_d10_162

private def cert_d10_163 : LowerCert :=
  .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 8, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.rep 2 10, .unbal 20 10 5], .branch [.branch [.unbal 10 10 4, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.unbal 19 19 7, .branch [.branch [.unbal 10 10 4, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.unbal 19 19 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .rep 2 10], .unbal 10 10 2], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .rep 2 10]], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]]], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9]], .rep 2 9]]], .rep 2 9]

private theorem ok_d10_163 : checkLowerCert 10 10 [3, 0, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_163 = true := by
  decide

private theorem ref_d10_163 : IsRefuted 10 10 [3, 0, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 0, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_163 ok_d10_163

private theorem ref_d10_161 : IsRefuted 10 10 [0, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_162 ref_d10_163

private def cert_d10_164 : LowerCert :=
  .rep 2 9

private theorem ok_d10_164 : checkLowerCert 10 10 [1, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_164 = true := by
  decide

private theorem ref_d10_164 : IsRefuted 10 10 [1, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_164 ok_d10_164

private theorem ref_d10_160 : IsRefuted 10 10 [2, 8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d10_161 ref_d10_164

private theorem ref_d10_158 : IsRefuted 10 10 [8, 9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_159 ref_d10_160

private theorem ref_d10_156 : IsRefuted 10 10 [9, 6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_157 ref_d10_158

private theorem ref_d10_152 : IsRefuted 10 10 [6, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_153 ref_d10_156

private def cert_d10_165 : LowerCert :=
  .rep 2 9

private theorem ok_d10_165 : checkLowerCert 10 10 [8, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_165 = true := by
  decide

private theorem ref_d10_165 : IsRefuted 10 10 [8, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_165 ok_d10_165

private theorem ref_d10_151 : IsRefuted 10 10 [7, 4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_152 ref_d10_165

private theorem ref_d10_137 : IsRefuted 10 10 [4, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_138 ref_d10_151

private def cert_d10_166 : LowerCert :=
  .rep 2 9

private theorem ok_d10_166 : checkLowerCert 10 10 [6, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_166 = true := by
  decide

private theorem ref_d10_166 : IsRefuted 10 10 [6, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_166 ok_d10_166

private theorem ref_d10_136 : IsRefuted 10 10 [5, 3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_137 ref_d10_166

private theorem ref_d10_134 : IsRefuted 10 10 [3, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_135 ref_d10_136

private def cert_d10_170 : LowerCert :=
  .rep 2 10

private theorem ok_d10_170 : checkLowerCert 10 10 [6, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_170 = true := by
  decide

private theorem ref_d10_170 : IsRefuted 10 10 [6, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_170 ok_d10_170

private def cert_d10_175 : LowerCert :=
  .rep 2 9

private theorem ok_d10_175 : checkLowerCert 10 10 [2, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_175 = true := by
  decide

private theorem ref_d10_175 : IsRefuted 10 10 [2, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_175 ok_d10_175

private def cert_d10_177 : LowerCert :=
  .unbal 10 10 1

private theorem ok_d10_177 : checkLowerCert 10 10 [1, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_177 = true := by
  decide

private theorem ref_d10_177 : IsRefuted 10 10 [1, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_177 ok_d10_177

private def cert_d10_179 : LowerCert :=
  .rep 2 10

private theorem ok_d10_179 : checkLowerCert 10 10 [1, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_179 = true := by
  decide

private theorem ref_d10_179 : IsRefuted 10 10 [1, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_179 ok_d10_179

private def cert_d10_182 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .unbal 20 10 3]]], .branch [.rep 2 10, .unbal 20 10 2]], .rep 2 9], .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .unbal 20 10 3]]], .rep 2 10], .unbal 10 10 0]]], .rep 2 9]]

private theorem ok_d10_182 : checkLowerCert 10 10 [3, 1, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_182 = true := by
  decide

private theorem ref_d10_182 : IsRefuted 10 10 [3, 1, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 1, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_182 ok_d10_182

private def cert_d10_183 : LowerCert :=
  .branch [.branch [.unbal 10 10 6, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .unbal 20 10 7], .branch [.branch [.unbal 10 10 6, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 20 10 8, .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .rep 2 10], .unbal 10 10 7], .rep 2 9], .rep 2 10], .unbal 10 10 4], .rep 2 9], .branch [.rep 2 10, .unbal 20 10 2]], .rep 2 9], .rep 2 10]]], .rep 2 10], .unbal 10 10 5]], .rep 2 10], .unbal 10 10 2]], .branch [.rep 2 10, .unbal 20 10 0]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 4]], .rep 2 10], .unbal 10 10 0]]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 2]], .rep 2 10]], .rep 2 9]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 0]]]], .rep 2 9]

private theorem ok_d10_183 : checkLowerCert 10 10 [5, 1, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_183 = true := by
  decide

private theorem ref_d10_183 : IsRefuted 10 10 [5, 1, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 1, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_183 ok_d10_183

private theorem ref_d10_181 : IsRefuted 10 10 [1, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_182 ref_d10_183

private def cert_d10_184 : LowerCert :=
  .rep 2 9

private theorem ok_d10_184 : checkLowerCert 10 10 [3, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_184 = true := by
  decide

private theorem ref_d10_184 : IsRefuted 10 10 [3, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_184 ok_d10_184

private theorem ref_d10_180 : IsRefuted 10 10 [4, 2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_181 ref_d10_184

private theorem ref_d10_178 : IsRefuted 10 10 [2, 9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_179 ref_d10_180

private theorem ref_d10_176 : IsRefuted 10 10 [9, 0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_177 ref_d10_178

private theorem ref_d10_174 : IsRefuted 10 10 [0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_175 ref_d10_176

private def cert_d10_185 : LowerCert :=
  .rep 2 10

private theorem ok_d10_185 : checkLowerCert 10 10 [9, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_185 = true := by
  decide

private theorem ref_d10_185 : IsRefuted 10 10 [9, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_185 ok_d10_185

private theorem ref_d10_173 : IsRefuted 10 10 [8, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_174 ref_d10_185

private def cert_d10_187 : LowerCert :=
  .rep 2 9

private theorem ok_d10_187 : checkLowerCert 10 10 [0, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_187 = true := by
  decide

private theorem ref_d10_187 : IsRefuted 10 10 [0, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_187 ok_d10_187

private def cert_d10_189 : LowerCert :=
  .branch [.unbal 10 10 1, .rep 2 10]

private theorem ok_d10_189 : checkLowerCert 10 10 [0, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_189 = true := by
  decide

private theorem ref_d10_189 : IsRefuted 10 10 [0, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_189 ok_d10_189

private def cert_d10_192 : LowerCert :=
  .branch [.unbal 10 10 3, .rep 2 10]

private theorem ok_d10_192 : checkLowerCert 10 10 [1, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_192 = true := by
  decide

private theorem ref_d10_192 : IsRefuted 10 10 [1, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_192 ok_d10_192

private def cert_d10_195 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 8, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 6, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .rep 2 10], .unbal 20 10 8], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]], .rep 2 9]]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]], .rep 2 9]], .unbal 20 10 1]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]], .rep 2 9]], .unbal 20 10 3], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_195 : checkLowerCert 10 10 [3, 1, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_195 = true := by
  decide

private theorem ref_d10_195 : IsRefuted 10 10 [3, 1, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 1, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_195 ok_d10_195

private def cert_d10_196 : LowerCert :=
  .branch [.branch [.unbal 10 10 6, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.rep 2 10, .unbal 20 10 7], .branch [.branch [.unbal 10 10 6, .branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.unbal 19 19 9, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 10 10 4], .rep 2 9], .unbal 19 19 2], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 10 10 2]]], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10]], .rep 2 9]], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9]]], .rep 2 9]

private theorem ok_d10_196 : checkLowerCert 10 10 [5, 1, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_196 = true := by
  decide

private theorem ref_d10_196 : IsRefuted 10 10 [5, 1, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 1, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_196 ok_d10_196

private theorem ref_d10_194 : IsRefuted 10 10 [1, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_195 ref_d10_196

private def cert_d10_197 : LowerCert :=
  .rep 2 9

private theorem ok_d10_197 : checkLowerCert 10 10 [3, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_197 = true := by
  decide

private theorem ref_d10_197 : IsRefuted 10 10 [3, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_197 ok_d10_197

private theorem ref_d10_193 : IsRefuted 10 10 [4, 0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_194 ref_d10_197

private theorem ref_d10_191 : IsRefuted 10 10 [0, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_192 ref_d10_193

private def cert_d10_198 : LowerCert :=
  .rep 2 9

private theorem ok_d10_198 : checkLowerCert 10 10 [1, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_198 = true := by
  decide

private theorem ref_d10_198 : IsRefuted 10 10 [1, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_198 ok_d10_198

private theorem ref_d10_190 : IsRefuted 10 10 [2, 8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d10_191 ref_d10_198

private theorem ref_d10_188 : IsRefuted 10 10 [8, 9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_189 ref_d10_190

private theorem ref_d10_186 : IsRefuted 10 10 [9, 6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_187 ref_d10_188

private theorem ref_d10_172 : IsRefuted 10 10 [6, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_173 ref_d10_186

private def cert_d10_199 : LowerCert :=
  .rep 2 9

private theorem ok_d10_199 : checkLowerCert 10 10 [8, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_199 = true := by
  decide

private theorem ref_d10_199 : IsRefuted 10 10 [8, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_199 ok_d10_199

private theorem ref_d10_171 : IsRefuted 10 10 [7, 5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_172 ref_d10_199

private theorem ref_d10_169 : IsRefuted 10 10 [5, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_170 ref_d10_171

private def cert_d10_203 : LowerCert :=
  .rep 2 10

private theorem ok_d10_203 : checkLowerCert 10 10 [8, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_203 = true := by
  decide

private theorem ref_d10_203 : IsRefuted 10 10 [8, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_203 ok_d10_203

private def cert_d10_205 : LowerCert :=
  .rep 2 9

private theorem ok_d10_205 : checkLowerCert 10 10 [0, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_205 = true := by
  decide

private theorem ref_d10_205 : IsRefuted 10 10 [0, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_205 ok_d10_205

private def cert_d10_207 : LowerCert :=
  .branch [.unbal 10 10 1, .rep 2 10]

private theorem ok_d10_207 : checkLowerCert 10 10 [0, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_207 = true := by
  decide

private theorem ref_d10_207 : IsRefuted 10 10 [0, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_207 ok_d10_207

private def cert_d10_210 : LowerCert :=
  .branch [.unbal 10 10 3, .rep 2 10]

private theorem ok_d10_210 : checkLowerCert 10 10 [1, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_210 = true := by
  decide

private theorem ref_d10_210 : IsRefuted 10 10 [1, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_210 ok_d10_210

private def cert_d10_213 : LowerCert :=
  .branch [.unbal 10 10 5, .rep 2 10]

private theorem ok_d10_213 : checkLowerCert 10 10 [3, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_213 = true := by
  decide

private theorem ref_d10_213 : IsRefuted 10 10 [3, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_213 ok_d10_213

private def cert_d10_216 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .rep 2 9], .branch [.rep 2 10, .unbal 10 10 6]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]], .unbal 20 10 1]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]], .unbal 20 10 3], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9]], .unbal 20 10 5], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9]]

private theorem ok_d10_216 : checkLowerCert 10 10 [5, 3, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_216 = true := by
  decide

private theorem ref_d10_216 : IsRefuted 10 10 [5, 3, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 3, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_216 ok_d10_216

private def cert_d10_217 : LowerCert :=
  .branch [.branch [.unbal 10 10 8, .branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.unbal 20 10 9, .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .unbal 28 28 9], .rep 2 9]]], .rep 2 10], .unbal 10 10 4]], .unbal 19 19 2], .rep 2 9]], .rep 2 9]], .rep 2 9]]], .rep 2 10], .unbal 10 10 2]]], .rep 2 9]], .rep 2 9]], .rep 2 9]]], .rep 2 10]], .rep 2 9]

private theorem ok_d10_217 : checkLowerCert 10 10 [7, 3, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_217 = true := by
  decide

private theorem ref_d10_217 : IsRefuted 10 10 [7, 3, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 3, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_217 ok_d10_217

private theorem ref_d10_215 : IsRefuted 10 10 [3, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_216 ref_d10_217

private def cert_d10_218 : LowerCert :=
  .rep 2 9

private theorem ok_d10_218 : checkLowerCert 10 10 [5, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_218 = true := by
  decide

private theorem ref_d10_218 : IsRefuted 10 10 [5, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_218 ok_d10_218

private theorem ref_d10_214 : IsRefuted 10 10 [6, 1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_215 ref_d10_218

private theorem ref_d10_212 : IsRefuted 10 10 [1, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_213 ref_d10_214

private def cert_d10_219 : LowerCert :=
  .rep 2 9

private theorem ok_d10_219 : checkLowerCert 10 10 [3, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_219 = true := by
  decide

private theorem ref_d10_219 : IsRefuted 10 10 [3, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_219 ok_d10_219

private theorem ref_d10_211 : IsRefuted 10 10 [4, 0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_212 ref_d10_219

private theorem ref_d10_209 : IsRefuted 10 10 [0, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_210 ref_d10_211

private def cert_d10_220 : LowerCert :=
  .rep 2 9

private theorem ok_d10_220 : checkLowerCert 10 10 [1, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_220 = true := by
  decide

private theorem ref_d10_220 : IsRefuted 10 10 [1, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_220 ok_d10_220

private theorem ref_d10_208 : IsRefuted 10 10 [2, 8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d10_209 ref_d10_220

private theorem ref_d10_206 : IsRefuted 10 10 [8, 9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_207 ref_d10_208

private theorem ref_d10_204 : IsRefuted 10 10 [9, 7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_205 ref_d10_206

private theorem ref_d10_202 : IsRefuted 10 10 [7, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_203 ref_d10_204

private def cert_d10_223 : LowerCert :=
  .branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 7, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .unbal 28 28 6], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .rep 2 10]]], .unbal 19 19 6], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]]]], .unbal 19 19 4], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 0]], .rep 2 9]], .rep 2 9]], .rep 2 9]]]]

private theorem ok_d10_223 : checkLowerCert 10 10 [0, 7, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_223 = true := by
  decide

private theorem ref_d10_223 : IsRefuted 10 10 [0, 7, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 7, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_223 ok_d10_223

private def cert_d10_224 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 7, .rep 2 10], .branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 1, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .branch [.rep 2 10, .unbal 10 10 6]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .rep 2 10], .unbal 20 10 3], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .rep 2 10], .unbal 20 10 5], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 20 10 7], .rep 2 9]], .rep 2 9]], .rep 2 9]]], .rep 2 10], .branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 7, .rep 2 10], .unbal 19 19 9], .rep 2 9]], .rep 2 9]], .rep 2 9]]]]], .rep 2 9]], .rep 2 9]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_224 : checkLowerCert 10 10 [9, 7, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_224 = true := by
  decide

private theorem ref_d10_224 : IsRefuted 10 10 [9, 7, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 7, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_224 ok_d10_224

private theorem ref_d10_222 : IsRefuted 10 10 [7, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_223 ref_d10_224

private def cert_d10_225 : LowerCert :=
  .rep 2 9

private theorem ok_d10_225 : checkLowerCert 10 10 [9, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_225 = true := by
  decide

private theorem ref_d10_225 : IsRefuted 10 10 [9, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_225 ok_d10_225

private theorem ref_d10_221 : IsRefuted 10 10 [8, 5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_222 ref_d10_225

private theorem ref_d10_201 : IsRefuted 10 10 [5, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_202 ref_d10_221

private def cert_d10_226 : LowerCert :=
  .rep 2 9

private theorem ok_d10_226 : checkLowerCert 10 10 [7, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_226 = true := by
  decide

private theorem ref_d10_226 : IsRefuted 10 10 [7, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_226 ok_d10_226

private theorem ref_d10_200 : IsRefuted 10 10 [6, 3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_201 ref_d10_226

private theorem ref_d10_168 : IsRefuted 10 10 [3, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_169 ref_d10_200

private def cert_d10_227 : LowerCert :=
  .rep 2 9

private theorem ok_d10_227 : checkLowerCert 10 10 [5, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_227 = true := by
  decide

private theorem ref_d10_227 : IsRefuted 10 10 [5, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_227 ok_d10_227

private theorem ref_d10_167 : IsRefuted 10 10 [4, 1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_168 ref_d10_227

private theorem ref_d10_133 : IsRefuted 10 10 [1, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_134 ref_d10_167

private def cert_d10_228 : LowerCert :=
  .rep 2 9

private theorem ok_d10_228 : checkLowerCert 10 10 [3, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_228 = true := by
  decide

private theorem ref_d10_228 : IsRefuted 10 10 [3, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_228 ok_d10_228

private theorem ref_d10_132 : IsRefuted 10 10 [2, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_133 ref_d10_228

private theorem ref_d10_130 : IsRefuted 10 10 [0, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_131 ref_d10_132

private def cert_d10_232 : LowerCert :=
  .rep 2 10

private theorem ok_d10_232 : checkLowerCert 10 10 [3, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_232 = true := by
  decide

private theorem ref_d10_232 : IsRefuted 10 10 [3, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [3, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_232 ok_d10_232

private def cert_d10_236 : LowerCert :=
  .rep 2 10

private theorem ok_d10_236 : checkLowerCert 10 10 [6, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_236 = true := by
  decide

private theorem ref_d10_236 : IsRefuted 10 10 [6, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_236 ok_d10_236

private def cert_d10_241 : LowerCert :=
  .rep 2 9

private theorem ok_d10_241 : checkLowerCert 10 10 [0, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_241 = true := by
  decide

private theorem ref_d10_241 : IsRefuted 10 10 [0, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_241 ok_d10_241

private def cert_d10_243 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.unbal 20 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 8 63, .rep 2 10], .unbal 20 10 8], .rep 2 9], .rep 2 10], .unbal 20 10 5], .rep 2 9], .rep 2 10], .unbal 20 10 2]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .rep 2 10], .unbal 20 10 6], .rep 2 9], .rep 2 10], .unbal 20 10 3], .rep 2 9]]], .rep 2 9], .rep 2 10], .unbal 20 10 8], .rep 2 9], .rep 2 10], .unbal 20 10 5], .rep 2 9]], .unbal 20 10 2]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .rep 2 10], .unbal 20 10 6], .rep 2 9]], .unbal 20 10 3], .rep 2 9]]], .rep 2 9], .rep 2 10], .branch [.rep 2 9, .branch [.branch [.unbal 20 10 0, .rep 2 10], .unbal 10 10 1]]], .rep 2 9]], .branch [.branch [.unbal 10 10 6, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.unbal 20 10 0, .rep 2 10], .unbal 10 10 1]]]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_243 : checkLowerCert 10 10 [0, 9, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_243 = true := by
  decide

private theorem ref_d10_243 : IsRefuted 10 10 [0, 9, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 9, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_243 ok_d10_243

private def cert_d10_244 : LowerCert :=
  .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 6, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .unbal 20 10 4], .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 6, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .unbal 20 10 5], .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .unbal 20 10 7], .branch [.branch [.unbal 10 10 3, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 20 10 8, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .rep 2 10], .unbal 10 10 7], .rep 2 9], .rep 2 10], .unbal 10 10 4], .rep 2 9], .rep 2 10], .unbal 10 10 1], .rep 2 9]]], .rep 2 10], .unbal 10 10 5]], .rep 2 10], .unbal 10 10 2]], .rep 2 10]], .rep 2 9]]], .rep 2 10], .unbal 10 10 4]], .rep 2 10], .unbal 10 10 1]]]], .rep 2 9]]], .rep 2 10], .unbal 10 10 2]], .rep 2 10]], .rep 2 9]]], .rep 2 9]]], .rep 2 10], .unbal 10 10 1]]]], .rep 2 9]]], .rep 2 9]

private theorem ok_d10_244 : checkLowerCert 10 10 [2, 9, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_244 = true := by
  decide

private theorem ref_d10_244 : IsRefuted 10 10 [2, 9, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 9, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_244 ok_d10_244

private theorem ref_d10_242 : IsRefuted 10 10 [9, 1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_243 ref_d10_244

private theorem ref_d10_240 : IsRefuted 10 10 [1, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_241 ref_d10_242

private def cert_d10_245 : LowerCert :=
  .rep 2 10

private theorem ok_d10_245 : checkLowerCert 10 10 [9, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_245 = true := by
  decide

private theorem ref_d10_245 : IsRefuted 10 10 [9, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_245 ok_d10_245

private theorem ref_d10_239 : IsRefuted 10 10 [8, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_240 ref_d10_245

private def cert_d10_246 : LowerCert :=
  .branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 6, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 6, .branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 3, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .rep 2 9], .branch [.rep 2 10, .unbal 20 10 7]], .rep 2 9], .rep 2 10], .unbal 10 10 4], .rep 2 9], .rep 2 10], .unbal 10 10 1], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 5]], .rep 2 9], .rep 2 10], .unbal 10 10 2]], .rep 2 10]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 4]], .rep 2 9], .rep 2 10], .unbal 10 10 1]]]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 2]], .rep 2 9], .rep 2 10]], .rep 2 9]]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 1]], .rep 2 9]]], .rep 2 9]]], .rep 2 9]]]]

private theorem ok_d10_246 : checkLowerCert 10 10 [9, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_246 = true := by
  decide

private theorem ref_d10_246 : IsRefuted 10 10 [9, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_246 ok_d10_246

private theorem ref_d10_238 : IsRefuted 10 10 [6, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_239 ref_d10_246

private def cert_d10_247 : LowerCert :=
  .rep 2 9

private theorem ok_d10_247 : checkLowerCert 10 10 [8, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_247 = true := by
  decide

private theorem ref_d10_247 : IsRefuted 10 10 [8, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_247 ok_d10_247

private theorem ref_d10_237 : IsRefuted 10 10 [7, 5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_238 ref_d10_247

private theorem ref_d10_235 : IsRefuted 10 10 [5, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_236 ref_d10_237

private def cert_d10_251 : LowerCert :=
  .rep 2 10

private theorem ok_d10_251 : checkLowerCert 10 10 [8, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_251 = true := by
  decide

private theorem ref_d10_251 : IsRefuted 10 10 [8, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_251 ok_d10_251

private def cert_d10_253 : LowerCert :=
  .rep 2 9

private theorem ok_d10_253 : checkLowerCert 10 10 [1, 9, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_253 = true := by
  decide

private theorem ref_d10_253 : IsRefuted 10 10 [1, 9, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 9, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_253 ok_d10_253

private def cert_d10_254 : LowerCert :=
  .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .unbal 20 10 5]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 1]], .rep 2 9]], .branch [.branch [.unbal 10 10 8, .branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 20 10 9, .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 3, .branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .rep 2 9], .rep 2 10], .unbal 10 10 6], .rep 2 9], .branch [.rep 2 10, .unbal 20 10 4]], .rep 2 9], .rep 2 10], .unbal 10 10 1], .rep 2 9]]]], .rep 2 10], .unbal 10 10 4]], .branch [.rep 2 10, .unbal 20 10 2]], .rep 2 9], .rep 2 10]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 2]], .branch [.rep 2 10, .unbal 20 10 1]], .rep 2 9]]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 1]]], .rep 2 9]]], .rep 2 9]]]], .rep 2 10]], .rep 2 9]], .rep 2 9]]], .rep 2 9]]]

private theorem ok_d10_254 : checkLowerCert 10 10 [8, 9, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_254 = true := by
  decide

private theorem ref_d10_254 : IsRefuted 10 10 [8, 9, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 9, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_254 ok_d10_254

private theorem ref_d10_252 : IsRefuted 10 10 [9, 7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_253 ref_d10_254

private theorem ref_d10_250 : IsRefuted 10 10 [7, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_251 ref_d10_252

private def cert_d10_258 : LowerCert :=
  .rep 2 9

private theorem ok_d10_258 : checkLowerCert 10 10 [0, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_258 = true := by
  decide

private theorem ref_d10_258 : IsRefuted 10 10 [0, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_258 ok_d10_258

private def cert_d10_260 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 7, .rep 2 10], .branch [.branch [.branch [.branch [.unbal 20 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 3, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .branch [.rep 2 10, .unbal 10 10 6]], .rep 2 9], .rep 2 10], .unbal 20 10 5], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 20 10 7], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]], .rep 2 9]]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_260 : checkLowerCert 10 10 [0, 9, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_260 = true := by
  decide

private theorem ref_d10_260 : IsRefuted 10 10 [0, 9, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 9, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_260 ok_d10_260

private def cert_d10_261 : LowerCert :=
  .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 7, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .unbal 20 10 4], .branch [.branch [.unbal 10 10 3, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 19 19 6, .branch [.branch [.unbal 10 10 3, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 19 19 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .branch [.rep 2 10, .unbal 10 10 6]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .rep 2 10], .unbal 10 10 1], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .rep 2 10]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 2]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]]], .rep 2 9]

private theorem ok_d10_261 : checkLowerCert 10 10 [2, 9, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_261 = true := by
  decide

private theorem ref_d10_261 : IsRefuted 10 10 [2, 9, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 9, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_261 ok_d10_261

private theorem ref_d10_259 : IsRefuted 10 10 [9, 1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_260 ref_d10_261

private theorem ref_d10_257 : IsRefuted 10 10 [1, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_258 ref_d10_259

private def cert_d10_262 : LowerCert :=
  .branch [.unbal 10 10 0, .rep 2 10]

private theorem ok_d10_262 : checkLowerCert 10 10 [9, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_262 = true := by
  decide

private theorem ref_d10_262 : IsRefuted 10 10 [9, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_262 ok_d10_262

private theorem ref_d10_256 : IsRefuted 10 10 [7, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_257 ref_d10_262

private def cert_d10_263 : LowerCert :=
  .rep 2 9

private theorem ok_d10_263 : checkLowerCert 10 10 [9, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_263 = true := by
  decide

private theorem ref_d10_263 : IsRefuted 10 10 [9, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_263 ok_d10_263

private theorem ref_d10_255 : IsRefuted 10 10 [8, 5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_256 ref_d10_263

private theorem ref_d10_249 : IsRefuted 10 10 [5, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_250 ref_d10_255

private def cert_d10_264 : LowerCert :=
  .rep 2 9

private theorem ok_d10_264 : checkLowerCert 10 10 [7, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_264 = true := by
  decide

private theorem ref_d10_264 : IsRefuted 10 10 [7, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_264 ok_d10_264

private theorem ref_d10_248 : IsRefuted 10 10 [6, 3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_249 ref_d10_264

private theorem ref_d10_234 : IsRefuted 10 10 [3, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_235 ref_d10_248

private def cert_d10_265 : LowerCert :=
  .rep 2 9

private theorem ok_d10_265 : checkLowerCert 10 10 [5, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_265 = true := by
  decide

private theorem ref_d10_265 : IsRefuted 10 10 [5, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_265 ok_d10_265

private theorem ref_d10_233 : IsRefuted 10 10 [4, 2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_234 ref_d10_265

private theorem ref_d10_231 : IsRefuted 10 10 [2, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_232 ref_d10_233

private def cert_d10_269 : LowerCert :=
  .rep 2 10

private theorem ok_d10_269 : checkLowerCert 10 10 [5, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_269 = true := by
  decide

private theorem ref_d10_269 : IsRefuted 10 10 [5, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [5, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_269 ok_d10_269

private def cert_d10_273 : LowerCert :=
  .rep 2 10

private theorem ok_d10_273 : checkLowerCert 10 10 [8, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_273 = true := by
  decide

private theorem ref_d10_273 : IsRefuted 10 10 [8, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_273 ok_d10_273

private def cert_d10_275 : LowerCert :=
  .rep 2 9

private theorem ok_d10_275 : checkLowerCert 10 10 [1, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_275 = true := by
  decide

private theorem ref_d10_275 : IsRefuted 10 10 [1, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [1, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_275 ok_d10_275

private def cert_d10_277 : LowerCert :=
  .unbal 10 10 0

private theorem ok_d10_277 : checkLowerCert 10 10 [0, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_277 = true := by
  decide

private theorem ref_d10_277 : IsRefuted 10 10 [0, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_277 ok_d10_277

private def cert_d10_279 : LowerCert :=
  .rep 2 10

private theorem ok_d10_279 : checkLowerCert 10 10 [0, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_279 = true := by
  decide

private theorem ref_d10_279 : IsRefuted 10 10 [0, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_279 ok_d10_279

private def cert_d10_282 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .unbal 20 10 2]]], .branch [.rep 2 10, .unbal 20 10 1]], .rep 2 9]], .branch [.branch [.unbal 10 10 8, .branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .unbal 20 10 2]]], .rep 2 10]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_282 : checkLowerCert 10 10 [2, 0, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_282 = true := by
  decide

private theorem ref_d10_282 : IsRefuted 10 10 [2, 0, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 0, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_282 ok_d10_282

private def cert_d10_283 : LowerCert :=
  .branch [.branch [.unbal 10 10 5, .branch [.rep 2 10, .branch [.branch [.unbal 10 10 8, .branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .unbal 20 10 6], .branch [.branch [.unbal 10 10 5, .branch [.rep 2 10, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.rep 2 10, .unbal 20 10 7], .branch [.branch [.unbal 10 10 5, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 20 10 9, .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 9 66, .rep 2 9], .rep 2 10], .unbal 10 10 6], .rep 2 9], .rep 2 10], .unbal 10 10 3], .rep 2 9], .branch [.rep 2 10, .unbal 20 10 1]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 4]], .rep 2 10], .unbal 10 10 1]]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 3]], .rep 2 10]], .rep 2 9]], .rep 2 9]]]], .rep 2 10], .unbal 10 10 1]]]], .rep 2 9]], .rep 2 9]]]], .rep 2 10]], .rep 2 9]]], .rep 2 9]

private theorem ok_d10_283 : checkLowerCert 10 10 [4, 0, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_283 = true := by
  decide

private theorem ref_d10_283 : IsRefuted 10 10 [4, 0, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 0, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_283 ok_d10_283

private theorem ref_d10_281 : IsRefuted 10 10 [0, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_282 ref_d10_283

private def cert_d10_284 : LowerCert :=
  .rep 2 9

private theorem ok_d10_284 : checkLowerCert 10 10 [2, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_284 = true := by
  decide

private theorem ref_d10_284 : IsRefuted 10 10 [2, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_284 ok_d10_284

private theorem ref_d10_280 : IsRefuted 10 10 [3, 1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_281 ref_d10_284

private theorem ref_d10_278 : IsRefuted 10 10 [1, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_279 ref_d10_280

private theorem ref_d10_276 : IsRefuted 10 10 [8, 9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d10_277 ref_d10_278

private theorem ref_d10_274 : IsRefuted 10 10 [9, 7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_275 ref_d10_276

private theorem ref_d10_272 : IsRefuted 10 10 [7, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_273 ref_d10_274

private def cert_d10_288 : LowerCert :=
  .rep 2 9

private theorem ok_d10_288 : checkLowerCert 10 10 [0, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_288 = true := by
  decide

private theorem ref_d10_288 : IsRefuted 10 10 [0, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_288 ok_d10_288

private def cert_d10_290 : LowerCert :=
  .branch [.unbal 10 10 2, .rep 2 10]

private theorem ok_d10_290 : checkLowerCert 10 10 [0, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_290 = true := by
  decide

private theorem ref_d10_290 : IsRefuted 10 10 [0, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_290 ok_d10_290

private def cert_d10_293 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 7, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 5, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .rep 2 10], .unbal 20 10 7], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]]], .rep 2 10], .unbal 20 10 9], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]], .unbal 20 10 2]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]]

private theorem ok_d10_293 : checkLowerCert 10 10 [2, 0, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_293 = true := by
  decide

private theorem ref_d10_293 : IsRefuted 10 10 [2, 0, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 0, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_293 ok_d10_293

private def cert_d10_294 : LowerCert :=
  .branch [.branch [.unbal 10 10 5, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.rep 2 10, .unbal 20 10 6], .branch [.branch [.unbal 10 10 5, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.unbal 19 19 8, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .branch [.rep 2 10, .unbal 10 10 6]], .rep 2 9], .rep 2 10], .unbal 10 10 3], .rep 2 9], .unbal 19 19 1], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 4]], .rep 2 9], .rep 2 10], .unbal 10 10 1]]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .rep 2 10]], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]]], .rep 2 9]

private theorem ok_d10_294 : checkLowerCert 10 10 [4, 0, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_294 = true := by
  decide

private theorem ref_d10_294 : IsRefuted 10 10 [4, 0, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 0, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_294 ok_d10_294

private theorem ref_d10_292 : IsRefuted 10 10 [0, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_293 ref_d10_294

private def cert_d10_295 : LowerCert :=
  .rep 2 9

private theorem ok_d10_295 : checkLowerCert 10 10 [2, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_295 = true := by
  decide

private theorem ref_d10_295 : IsRefuted 10 10 [2, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_295 ok_d10_295

private theorem ref_d10_291 : IsRefuted 10 10 [3, 9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_292 ref_d10_295

private theorem ref_d10_289 : IsRefuted 10 10 [9, 1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_290 ref_d10_291

private theorem ref_d10_287 : IsRefuted 10 10 [1, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_288 ref_d10_289

private def cert_d10_296 : LowerCert :=
  .branch [.unbal 10 10 0, .rep 2 10]

private theorem ok_d10_296 : checkLowerCert 10 10 [9, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_296 = true := by
  decide

private theorem ref_d10_296 : IsRefuted 10 10 [9, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_296 ok_d10_296

private theorem ref_d10_286 : IsRefuted 10 10 [7, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_287 ref_d10_296

private def cert_d10_297 : LowerCert :=
  .rep 2 9

private theorem ok_d10_297 : checkLowerCert 10 10 [9, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_297 = true := by
  decide

private theorem ref_d10_297 : IsRefuted 10 10 [9, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_297 ok_d10_297

private theorem ref_d10_285 : IsRefuted 10 10 [8, 5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_286 ref_d10_297

private theorem ref_d10_271 : IsRefuted 10 10 [5, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_272 ref_d10_285

private def cert_d10_298 : LowerCert :=
  .rep 2 9

private theorem ok_d10_298 : checkLowerCert 10 10 [7, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_298 = true := by
  decide

private theorem ref_d10_298 : IsRefuted 10 10 [7, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_298 ok_d10_298

private theorem ref_d10_270 : IsRefuted 10 10 [6, 4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_271 ref_d10_298

private theorem ref_d10_268 : IsRefuted 10 10 [4, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_269 ref_d10_270

private def cert_d10_302 : LowerCert :=
  .rep 2 10

private theorem ok_d10_302 : checkLowerCert 10 10 [7, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_302 = true := by
  decide

private theorem ref_d10_302 : IsRefuted 10 10 [7, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [7, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_302 ok_d10_302

private def cert_d10_306 : LowerCert :=
  .rep 2 9

private theorem ok_d10_306 : checkLowerCert 10 10 [0, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_306 = true := by
  decide

private theorem ref_d10_306 : IsRefuted 10 10 [0, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_306 ok_d10_306

private def cert_d10_308 : LowerCert :=
  .branch [.unbal 10 10 2, .rep 2 10]

private theorem ok_d10_308 : checkLowerCert 10 10 [0, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_308 = true := by
  decide

private theorem ref_d10_308 : IsRefuted 10 10 [0, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_308 ok_d10_308

private def cert_d10_311 : LowerCert :=
  .branch [.unbal 10 10 4, .rep 2 10]

private theorem ok_d10_311 : checkLowerCert 10 10 [2, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_311 = true := by
  decide

private theorem ref_d10_311 : IsRefuted 10 10 [2, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_311 ok_d10_311

private def cert_d10_314 : LowerCert :=
  .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 20 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .unbal 20 10 2]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .unbal 20 10 4], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]]

private theorem ok_d10_314 : checkLowerCert 10 10 [4, 2, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_314 = true := by
  decide

private theorem ref_d10_314 : IsRefuted 10 10 [4, 2, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 2, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_314 ok_d10_314

private def cert_d10_315 : LowerCert :=
  .branch [.branch [.unbal 10 10 7, .branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.unbal 20 10 8, .rep 2 10], .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .rep 2 10], .unbal 10 10 5], .rep 2 9], .unbal 19 19 3], .rep 2 9], .unbal 28 28 1], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 10 10 3]], .unbal 19 19 1], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10], .unbal 10 10 1]]], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10]], .rep 2 9]

private theorem ok_d10_315 : checkLowerCert 10 10 [6, 2, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_315 = true := by
  decide

private theorem ref_d10_315 : IsRefuted 10 10 [6, 2, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 2, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_315 ok_d10_315

private theorem ref_d10_313 : IsRefuted 10 10 [2, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_314 ref_d10_315

private def cert_d10_316 : LowerCert :=
  .rep 2 9

private theorem ok_d10_316 : checkLowerCert 10 10 [4, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_316 = true := by
  decide

private theorem ref_d10_316 : IsRefuted 10 10 [4, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_316 ok_d10_316

private theorem ref_d10_312 : IsRefuted 10 10 [5, 0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_313 ref_d10_316

private theorem ref_d10_310 : IsRefuted 10 10 [0, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_311 ref_d10_312

private def cert_d10_317 : LowerCert :=
  .rep 2 9

private theorem ok_d10_317 : checkLowerCert 10 10 [2, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_317 = true := by
  decide

private theorem ref_d10_317 : IsRefuted 10 10 [2, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_317 ok_d10_317

private theorem ref_d10_309 : IsRefuted 10 10 [3, 9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_310 ref_d10_317

private theorem ref_d10_307 : IsRefuted 10 10 [9, 1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_308 ref_d10_309

private theorem ref_d10_305 : IsRefuted 10 10 [1, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_306 ref_d10_307

private def cert_d10_318 : LowerCert :=
  .branch [.unbal 10 10 0, .rep 2 10]

private theorem ok_d10_318 : checkLowerCert 10 10 [9, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_318 = true := by
  decide

private theorem ref_d10_318 : IsRefuted 10 10 [9, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_318 ok_d10_318

private theorem ref_d10_304 : IsRefuted 10 10 [7, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_305 ref_d10_318

private def cert_d10_319 : LowerCert :=
  .rep 2 9

private theorem ok_d10_319 : checkLowerCert 10 10 [9, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_319 = true := by
  decide

private theorem ref_d10_319 : IsRefuted 10 10 [9, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_319 ok_d10_319

private theorem ref_d10_303 : IsRefuted 10 10 [8, 6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_304 ref_d10_319

private theorem ref_d10_301 : IsRefuted 10 10 [6, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_302 ref_d10_303

private def cert_d10_324 : LowerCert :=
  .rep 2 9

private theorem ok_d10_324 : checkLowerCert 10 10 [0, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_324 = true := by
  decide

private theorem ref_d10_324 : IsRefuted 10 10 [0, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_324 ok_d10_324

private def cert_d10_326 : LowerCert :=
  .branch [.unbal 10 10 2, .rep 2 10]

private theorem ok_d10_326 : checkLowerCert 10 10 [0, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_326 = true := by
  decide

private theorem ref_d10_326 : IsRefuted 10 10 [0, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [0, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_326 ok_d10_326

private def cert_d10_329 : LowerCert :=
  .branch [.unbal 10 10 4, .rep 2 10]

private theorem ok_d10_329 : checkLowerCert 10 10 [2, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_329 = true := by
  decide

private theorem ref_d10_329 : IsRefuted 10 10 [2, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_329 ok_d10_329

private def cert_d10_332 : LowerCert :=
  .branch [.unbal 10 10 6, .rep 2 10]

private theorem ok_d10_332 : checkLowerCert 10 10 [4, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_332 = true := by
  decide

private theorem ref_d10_332 : IsRefuted 10 10 [4, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_332 ok_d10_332

private def cert_d10_335 : LowerCert :=
  .branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 54, .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .rep 2 10], .unbal 20 10 2]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 5]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .rep 2 10], .unbal 20 10 4], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .rep 2 10], .unbal 20 10 6], .rep 2 9]], .rep 2 9]]], .branch [.unbal 10 10 0, .rep 2 10]], .rep 2 9], .rep 2 10]

private theorem ok_d10_335 : checkLowerCert 10 10 [6, 4, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_335 = true := by
  decide

private theorem ref_d10_335 : IsRefuted 10 10 [6, 4, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 4, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_335 ok_d10_335

private def cert_d10_336 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 6, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.unbal 10 10 2, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .rep 2 9], .unbal 19 19 5], .rep 2 9], .unbal 28 28 3], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]]], .rep 2 10], .unbal 10 10 5]], .unbal 19 19 3], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]]], .rep 2 10], .unbal 10 10 3]], .unbal 19 19 1], .rep 2 9]], .rep 2 9]], .rep 2 9]]], .rep 2 10], .unbal 10 10 1]]

private theorem ok_d10_336 : checkLowerCert 10 10 [8, 4, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_336 = true := by
  decide

private theorem ref_d10_336 : IsRefuted 10 10 [8, 4, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 4, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_336 ok_d10_336

private theorem ref_d10_334 : IsRefuted 10 10 [4, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_335 ref_d10_336

private def cert_d10_337 : LowerCert :=
  .rep 2 9

private theorem ok_d10_337 : checkLowerCert 10 10 [6, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_337 = true := by
  decide

private theorem ref_d10_337 : IsRefuted 10 10 [6, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_337 ok_d10_337

private theorem ref_d10_333 : IsRefuted 10 10 [7, 2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_334 ref_d10_337

private theorem ref_d10_331 : IsRefuted 10 10 [2, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_332 ref_d10_333

private def cert_d10_338 : LowerCert :=
  .rep 2 9

private theorem ok_d10_338 : checkLowerCert 10 10 [4, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_338 = true := by
  decide

private theorem ref_d10_338 : IsRefuted 10 10 [4, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_338 ok_d10_338

private theorem ref_d10_330 : IsRefuted 10 10 [5, 0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_331 ref_d10_338

private theorem ref_d10_328 : IsRefuted 10 10 [0, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_329 ref_d10_330

private def cert_d10_339 : LowerCert :=
  .rep 2 9

private theorem ok_d10_339 : checkLowerCert 10 10 [2, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_339 = true := by
  decide

private theorem ref_d10_339 : IsRefuted 10 10 [2, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_339 ok_d10_339

private theorem ref_d10_327 : IsRefuted 10 10 [3, 9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_328 ref_d10_339

private theorem ref_d10_325 : IsRefuted 10 10 [9, 1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_326 ref_d10_327

private theorem ref_d10_323 : IsRefuted 10 10 [1, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_324 ref_d10_325

private def cert_d10_340 : LowerCert :=
  .rep 2 10

private theorem ok_d10_340 : checkLowerCert 10 10 [9, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_340 = true := by
  decide

private theorem ref_d10_340 : IsRefuted 10 10 [9, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_340 ok_d10_340

private theorem ref_d10_322 : IsRefuted 10 10 [8, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_323 ref_d10_340

private def cert_d10_341 : LowerCert :=
  .branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 6, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 8, .rep 2 10], .branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.unbal 10 10 6, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.unbal 10 10 4, .rep 2 10], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 9, .branch [.unbal 10 10 0, .branch [.rep 2 10, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 55, .rep 2 9], .unbal 28 28 5], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]]]], .unbal 19 19 5], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 3]], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]]]], .unbal 19 19 3], .rep 2 9], .branch [.rep 2 10, .unbal 10 10 1]], .rep 2 9]], .rep 2 9]], .rep 2 9]]]], .branch [.rep 2 10, .unbal 20 10 1]], .rep 2 9]], .rep 2 9]], .rep 2 9]], .rep 2 9]]]]

private theorem ok_d10_341 : checkLowerCert 10 10 [9, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_341 = true := by
  decide

private theorem ref_d10_341 : IsRefuted 10 10 [9, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [9, 6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_341 ok_d10_341

private theorem ref_d10_321 : IsRefuted 10 10 [6, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 8) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_322 ref_d10_341

private def cert_d10_342 : LowerCert :=
  .rep 2 9

private theorem ok_d10_342 : checkLowerCert 10 10 [8, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_342 = true := by
  decide

private theorem ref_d10_342 : IsRefuted 10 10 [8, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [8, 7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_342 ok_d10_342

private theorem ref_d10_320 : IsRefuted 10 10 [7, 4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d10_321 ref_d10_342

private theorem ref_d10_300 : IsRefuted 10 10 [4, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d10_301 ref_d10_320

private def cert_d10_343 : LowerCert :=
  .rep 2 9

private theorem ok_d10_343 : checkLowerCert 10 10 [6, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_343 = true := by
  decide

private theorem ref_d10_343 : IsRefuted 10 10 [6, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [6, 5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_343 ok_d10_343

private theorem ref_d10_299 : IsRefuted 10 10 [5, 2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d10_300 ref_d10_343

private theorem ref_d10_267 : IsRefuted 10 10 [2, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d10_268 ref_d10_299

private def cert_d10_344 : LowerCert :=
  .rep 2 9

private theorem ok_d10_344 : checkLowerCert 10 10 [4, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_344 = true := by
  decide

private theorem ref_d10_344 : IsRefuted 10 10 [4, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [4, 3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_344 ok_d10_344

private theorem ref_d10_266 : IsRefuted 10 10 [3, 0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d10_267 ref_d10_344

private theorem ref_d10_230 : IsRefuted 10 10 [0, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d10_231 ref_d10_266

private def cert_d10_345 : LowerCert :=
  .rep 2 9

private theorem ok_d10_345 : checkLowerCert 10 10 [2, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_345 = true := by
  decide

private theorem ref_d10_345 : IsRefuted 10 10 [2, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 10 [2, 1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d10_345 ok_d10_345

private theorem ref_d10_229 : IsRefuted 10 10 [1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d10_230 ref_d10_345

private theorem ref_d10_129 : IsRefuted 10 10 [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d10_130 ref_d10_229

private theorem ref_d10_9 : IsRefuted 10 9 [8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 9) (by omega) (by decide) (by decide) (by decide) ref_d10_10 ref_d10_129

private theorem ref_d10_8 : IsRefuted 10 8 [7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 8) (by omega) (by decide) (by decide) ref_d10_9

private theorem ref_d10_7 : IsRefuted 10 7 [6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 7) (by omega) (by decide) (by decide) ref_d10_8

private theorem ref_d10_6 : IsRefuted 10 6 [5, 4, 3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 6) (by omega) (by decide) (by decide) ref_d10_7

private theorem ref_d10_5 : IsRefuted 10 5 [4, 3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 5) (by omega) (by decide) (by decide) ref_d10_6

private theorem ref_d10_4 : IsRefuted 10 4 [3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 4) (by omega) (by decide) (by decide) ref_d10_5

private theorem ref_d10_3 : IsRefuted 10 3 [2, 1, 0] :=
  isRefuted_split1 (c1 := 3) (by omega) (by decide) (by decide) ref_d10_4

private theorem ref_d10_2 : IsRefuted 10 2 [1, 0] :=
  isRefuted_split1 (c1 := 2) (by omega) (by decide) (by decide) ref_d10_3

private theorem ref_d10_1 : IsRefuted 10 1 [0] :=
  isRefuted_split1 (c1 := 1) (by omega) (by decide) (by decide) ref_d10_2

private theorem ref_d10_0 : IsRefuted 10 0 [] :=
  isRefuted_split1 (c1 := 0) (by omega) (by decide) (by decide) ref_d10_1

/-- The empty prefix over `Fin 10` is refuted at threshold `9/8`. -/
theorem isRefuted_10 : IsRefuted 10 0 [] :=
  ref_d10_0

/-- Every 1-balanced sequence over `Fin 10` has critical exponent at least `9/8`. -/
theorem critExp_ge_10 (w : ℕ → Fin 10) (hw : IsBalanced w) :
    (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ≤ critExp w := by
  have h := (rtb_ge_of_refuted (d := 10) (by omega) isRefuted_10).1 w hw
  simpa using h

/-- Lower bound `RTB 10 ≥ 9/8` (unconditional, zero recurrence/aperiodicity assumption). -/
theorem rtb_ge_10 : (((9 : ℝ) / (8 : ℝ) : ℝ) : EReal) ≤ RTB 10 := by
  have h := (rtb_ge_of_refuted (d := 10) (by omega) isRefuted_10).2
  simpa using h

end BalancedRepetitionThreshold
