module

public import BalancedRepetitionThreshold.LowerBoundEngine

import Mathlib.Tactic

/-!
# Pure-Kernel Lower-Bound Witness Tree for `d = 9` (`RTB(9) ≥ 8/7`)

Replays the complete finite refutation tree of `2941` nodes (`82` pure-kernel `decide`
chunks, max `137` nodes/chunk, zero `native_decide`, zero `set_option`) to prove
unconditionally that every 1-balanced sequence over `Fin 9` has critical exponent `≥ 8/7`.
-/

@[expose] public section

namespace BalancedRepetitionThreshold

private def cert_d9_10 : LowerCert :=
  .rep 2 8

private theorem ok_d9_10 : checkLowerCert 9 8 [1, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_10 = true := by
  decide

private theorem ref_d9_10 : IsRefuted 9 8 [1, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 8 [1, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_10 ok_d9_10

private def cert_d9_13 : LowerCert :=
  .rep 2 9

private theorem ok_d9_13 : checkLowerCert 9 9 [2, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_13 = true := by
  decide

private theorem ref_d9_13 : IsRefuted 9 9 [2, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [2, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_13 ok_d9_13

private def cert_d9_17 : LowerCert :=
  .rep 2 9

private theorem ok_d9_17 : checkLowerCert 9 9 [5, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_17 = true := by
  decide

private theorem ref_d9_17 : IsRefuted 9 9 [5, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [5, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_17 ok_d9_17

private def cert_d9_22 : LowerCert :=
  .branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.rep 2 9, .branch [.branch [.unbal 9 9 5, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.rep 2 9, .branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .unbal 25 25 0], .branch [.unbal 18 9 6, .rep 2 9]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 4]], .rep 2 8], .rep 2 9], .unbal 9 9 1]], .rep 2 9]]], .branch [.rep 2 9, .unbal 18 9 4]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 3]], .rep 2 8], .rep 2 9], .unbal 9 9 0]]]]], .branch [.rep 2 9, .unbal 18 9 3]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8], .rep 2 9]], .rep 2 8]]]]

private theorem ok_d9_22 : checkLowerCert 9 9 [1, 7, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_22 = true := by
  decide

private theorem ref_d9_22 : IsRefuted 9 9 [1, 7, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 7, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_22 ok_d9_22

private def cert_d9_23 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 18 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 48, .rep 2 9], .unbal 18 9 7], .rep 2 8], .rep 2 9], .unbal 18 9 4], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]]], .rep 2 9], .unbal 18 9 8], .rep 2 8], .rep 2 9], .unbal 18 9 5], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]]], .rep 2 8], .rep 2 9], .unbal 18 9 7], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]], .unbal 18 9 2]], .rep 2 9], .unbal 18 9 8], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]], .branch [.branch [.unbal 9 9 5, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 2, .rep 2 9], .branch [.branch [.branch [.unbal 18 9 6, .rep 2 9], .branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 7], .unbal 9 9 0]]], .rep 2 8]]], .rep 2 9], .unbal 18 9 8], .rep 2 8], .rep 2 9]], .rep 2 8]], .rep 2 8]]

private theorem ok_d9_23 : checkLowerCert 9 9 [8, 7, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_23 = true := by
  decide

private theorem ref_d9_23 : IsRefuted 9 9 [8, 7, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 7, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_23 ok_d9_23

private theorem ref_d9_21 : IsRefuted 9 9 [7, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_22 ref_d9_23

private def cert_d9_24 : LowerCert :=
  .rep 2 8

private theorem ok_d9_24 : checkLowerCert 9 9 [8, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_24 = true := by
  decide

private theorem ref_d9_24 : IsRefuted 9 9 [8, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_24 ok_d9_24

private theorem ref_d9_20 : IsRefuted 9 9 [0, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_21 ref_d9_24

private def cert_d9_25 : LowerCert :=
  .branch [.rep 2 9, .unbal 9 9 0]

private theorem ok_d9_25 : checkLowerCert 9 9 [7, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_25 = true := by
  decide

private theorem ref_d9_25 : IsRefuted 9 9 [7, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_25 ok_d9_25

private theorem ref_d9_19 : IsRefuted 9 9 [5, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_20 ref_d9_25

private def cert_d9_26 : LowerCert :=
  .rep 2 8

private theorem ok_d9_26 : checkLowerCert 9 9 [7, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_26 = true := by
  decide

private theorem ref_d9_26 : IsRefuted 9 9 [7, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_26 ok_d9_26

private theorem ref_d9_18 : IsRefuted 9 9 [6, 4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_19 ref_d9_26

private theorem ref_d9_16 : IsRefuted 9 9 [4, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d9_17 ref_d9_18

private def cert_d9_32 : LowerCert :=
  .branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.rep 2 9, .unbal 18 9 4]]], .branch [.rep 2 9, .unbal 18 9 3]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8], .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 8 50, .rep 2 8], .rep 2 9], .unbal 9 9 5], .rep 2 8], .unbal 17 17 3], .rep 2 8], .rep 2 9], .unbal 9 9 0]], .unbal 17 17 6], .rep 2 8], .rep 2 9], .unbal 9 9 3]], .unbal 17 17 1], .rep 2 8], .rep 2 9]]], .unbal 17 17 5], .rep 2 8], .rep 2 9], .unbal 9 9 1]], .unbal 17 17 0], .rep 2 8]]]], .branch [.rep 2 9, .unbal 18 9 3]], .rep 2 8], .rep 2 9], .unbal 9 9 0]]], .rep 2 8]]]]

private theorem ok_d9_32 : checkLowerCert 9 9 [1, 7, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_32 = true := by
  decide

private theorem ref_d9_32 : IsRefuted 9 9 [1, 7, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 7, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_32 ok_d9_32

private def cert_d9_33 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 4, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 2, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 18 9 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 48, .rep 2 8], .branch [.rep 2 9, .unbal 9 9 5]], .rep 2 8], .rep 2 9], .unbal 18 9 4], .rep 2 8], .rep 2 9]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 5]], .rep 2 8], .rep 2 9], .unbal 18 9 6], .rep 2 8], .rep 2 9], .unbal 18 9 2]], .branch [.unbal 9 9 1, .rep 2 9]], .rep 2 8], .rep 2 9], .unbal 18 9 7], .rep 2 8], .rep 2 9], .unbal 18 9 4], .rep 2 8]]], .rep 2 9], .unbal 18 9 8], .rep 2 8], .rep 2 9], .branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 8], .unbal 9 9 0]]], .rep 2 8]], .rep 2 8]]

private theorem ok_d9_33 : checkLowerCert 9 9 [8, 7, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_33 = true := by
  decide

private theorem ref_d9_33 : IsRefuted 9 9 [8, 7, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 7, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_33 ok_d9_33

private theorem ref_d9_31 : IsRefuted 9 9 [7, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_32 ref_d9_33

private def cert_d9_34 : LowerCert :=
  .rep 2 8

private theorem ok_d9_34 : checkLowerCert 9 9 [8, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_34 = true := by
  decide

private theorem ref_d9_34 : IsRefuted 9 9 [8, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_34 ok_d9_34

private theorem ref_d9_30 : IsRefuted 9 9 [0, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_31 ref_d9_34

private def cert_d9_35 : LowerCert :=
  .rep 2 9

private theorem ok_d9_35 : checkLowerCert 9 9 [7, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_35 = true := by
  decide

private theorem ref_d9_35 : IsRefuted 9 9 [7, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_35 ok_d9_35

private theorem ref_d9_29 : IsRefuted 9 9 [6, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_30 ref_d9_35

private def cert_d9_36 : LowerCert :=
  .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 6, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 2, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 25 25 1, .rep 2 9], .unbal 9 9 0]], .rep 2 9], .unbal 9 9 5]], .branch [.rep 2 9, .unbal 18 9 3]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8], .rep 2 9]]], .rep 2 9], .unbal 9 9 3]], .branch [.rep 2 9, .unbal 18 9 1]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]]]], .rep 2 9], .unbal 9 9 1]], .branch [.rep 2 9, .unbal 18 9 0]], .rep 2 8]], .rep 2 8]]]], .rep 2 9], .unbal 9 9 0]]

private theorem ok_d9_36 : checkLowerCert 9 9 [7, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_36 = true := by
  decide

private theorem ref_d9_36 : IsRefuted 9 9 [7, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_36 ok_d9_36

private theorem ref_d9_28 : IsRefuted 9 9 [4, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_29 ref_d9_36

private def cert_d9_37 : LowerCert :=
  .rep 2 8

private theorem ok_d9_37 : checkLowerCert 9 9 [6, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_37 = true := by
  decide

private theorem ref_d9_37 : IsRefuted 9 9 [6, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [6, 5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_37 ok_d9_37

private theorem ref_d9_27 : IsRefuted 9 9 [5, 2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d9_28 ref_d9_37

private theorem ref_d9_15 : IsRefuted 9 9 [2, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d9_16 ref_d9_27

private def cert_d9_38 : LowerCert :=
  .rep 2 8

private theorem ok_d9_38 : checkLowerCert 9 9 [4, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_38 = true := by
  decide

private theorem ref_d9_38 : IsRefuted 9 9 [4, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [4, 3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_38 ok_d9_38

private theorem ref_d9_14 : IsRefuted 9 9 [3, 1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d9_15 ref_d9_38

private theorem ref_d9_12 : IsRefuted 9 9 [1, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d9_13 ref_d9_14

private def cert_d9_42 : LowerCert :=
  .rep 2 9

private theorem ok_d9_42 : checkLowerCert 9 9 [4, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_42 = true := by
  decide

private theorem ref_d9_42 : IsRefuted 9 9 [4, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [4, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_42 ok_d9_42

private def cert_d9_49 : LowerCert :=
  .rep 2 8

private theorem ok_d9_49 : checkLowerCert 9 9 [1, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_49 = true := by
  decide

private theorem ref_d9_49 : IsRefuted 9 9 [1, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_49 ok_d9_49

private def cert_d9_51 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 18 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 18 9 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 48, .rep 2 8], .rep 2 9], .unbal 18 9 6], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .rep 2 9]], .rep 2 8], .rep 2 9], .unbal 18 9 7], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .rep 2 9], .unbal 18 9 3]], .rep 2 9], .unbal 18 9 8], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .rep 2 9], .unbal 18 9 4], .rep 2 8]]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.branch [.unbal 18 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 4, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 8], .unbal 9 9 2]], .unbal 17 17 0], .rep 2 8]], .rep 2 8]]], .rep 2 8], .rep 2 9], .unbal 9 9 0]]], .rep 2 8]]

private theorem ok_d9_51 : checkLowerCert 9 9 [1, 8, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_51 = true := by
  decide

private theorem ref_d9_51 : IsRefuted 9 9 [1, 8, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 8, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_51 ok_d9_51

private def cert_d9_52 : LowerCert :=
  .branch [.branch [.unbal 9 9 4, .branch [.rep 2 9, .branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 5], .branch [.branch [.unbal 9 9 4, .branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 18 9 6, .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 25 25 2, .rep 2 8], .unbal 34 17 0]], .branch [.unbal 9 9 1, .rep 2 9]], .rep 2 8], .rep 2 9], .unbal 9 9 3]], .rep 2 9], .unbal 9 9 0]]]], .branch [.unbal 9 9 1, .rep 2 9]], .rep 2 8], .rep 2 9], .unbal 9 9 2]], .rep 2 9]], .rep 2 8]]], .branch [.unbal 9 9 1, .rep 2 9]], .rep 2 8], .rep 2 9], .unbal 9 9 0]]]], .rep 2 8]

private theorem ok_d9_52 : checkLowerCert 9 9 [3, 8, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_52 = true := by
  decide

private theorem ref_d9_52 : IsRefuted 9 9 [3, 8, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [3, 8, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_52 ok_d9_52

private theorem ref_d9_50 : IsRefuted 9 9 [8, 2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d9_51 ref_d9_52

private theorem ref_d9_48 : IsRefuted 9 9 [2, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_49 ref_d9_50

private def cert_d9_53 : LowerCert :=
  .branch [.unbal 9 9 1, .rep 2 9]

private theorem ok_d9_53 : checkLowerCert 9 9 [8, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_53 = true := by
  decide

private theorem ref_d9_53 : IsRefuted 9 9 [8, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_53 ok_d9_53

private theorem ref_d9_47 : IsRefuted 9 9 [7, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_48 ref_d9_53

private def cert_d9_54 : LowerCert :=
  .rep 2 8

private theorem ok_d9_54 : checkLowerCert 9 9 [8, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_54 = true := by
  decide

private theorem ref_d9_54 : IsRefuted 9 9 [8, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_54 ok_d9_54

private theorem ref_d9_46 : IsRefuted 9 9 [0, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_47 ref_d9_54

private def cert_d9_55 : LowerCert :=
  .rep 2 9

private theorem ok_d9_55 : checkLowerCert 9 9 [7, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_55 = true := by
  decide

private theorem ref_d9_55 : IsRefuted 9 9 [7, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_55 ok_d9_55

private theorem ref_d9_45 : IsRefuted 9 9 [6, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_46 ref_d9_55

private def cert_d9_56 : LowerCert :=
  .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 6, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 18 9 1, .rep 2 9], .unbal 9 9 2]], .branch [.rep 2 9, .unbal 18 9 0]], .rep 2 8]], .rep 2 8]], .branch [.branch [.unbal 9 9 4, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 5], .branch [.branch [.unbal 9 9 4, .branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 17 17 7, .branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 8 50, .unbal 9 9 7], .rep 2 8], .unbal 17 17 5], .rep 2 8], .rep 2 9], .unbal 9 9 2], .rep 2 8], .unbal 17 17 0]], .rep 2 9], .unbal 9 9 5]], .unbal 17 17 3], .rep 2 8], .rep 2 9], .unbal 9 9 0]]]], .rep 2 9], .unbal 9 9 3]], .unbal 17 17 2], .rep 2 8], .rep 2 9]], .rep 2 8]]], .rep 2 9], .unbal 9 9 2]], .branch [.rep 2 9, .unbal 18 9 0]], .rep 2 8]]], .rep 2 8]]], .rep 2 9], .unbal 9 9 0]]

private theorem ok_d9_56 : checkLowerCert 9 9 [7, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_56 = true := by
  decide

private theorem ref_d9_56 : IsRefuted 9 9 [7, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_56 ok_d9_56

private theorem ref_d9_44 : IsRefuted 9 9 [4, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_45 ref_d9_56

private def cert_d9_57 : LowerCert :=
  .rep 2 8

private theorem ok_d9_57 : checkLowerCert 9 9 [6, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_57 = true := by
  decide

private theorem ref_d9_57 : IsRefuted 9 9 [6, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [6, 5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_57 ok_d9_57

private theorem ref_d9_43 : IsRefuted 9 9 [5, 3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d9_44 ref_d9_57

private theorem ref_d9_41 : IsRefuted 9 9 [3, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d9_42 ref_d9_43

private def cert_d9_60 : LowerCert :=
  .branch [.rep 2 9, .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 18 9 1, .rep 2 9], .unbal 9 9 4]], .unbal 17 17 2], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]], .unbal 18 9 3]], .rep 2 9], .unbal 9 9 2]], .branch [.rep 2 9, .unbal 18 9 0]], .rep 2 8]], .branch [.branch [.unbal 9 9 6, .branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.unbal 18 9 7, .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.unbal 25 25 4, .rep 2 8], .unbal 34 17 2], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]]], .rep 2 9], .unbal 9 9 5]], .rep 2 9], .unbal 9 9 2]], .branch [.rep 2 9, .unbal 18 9 0]], .rep 2 8]]], .rep 2 9], .unbal 9 9 4]], .rep 2 9], .unbal 9 9 0]]], .rep 2 8]]], .rep 2 9], .unbal 9 9 2]], .rep 2 9]], .rep 2 8]], .rep 2 8]]], .rep 2 9], .unbal 9 9 0]]]

private theorem ok_d9_60 : checkLowerCert 9 9 [5, 3, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_60 = true := by
  decide

private theorem ref_d9_60 : IsRefuted 9 9 [5, 3, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [5, 3, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_60 ok_d9_60

private def cert_d9_61 : LowerCert :=
  .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 5, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.rep 6 40, .rep 2 8], .branch [.rep 2 9, .unbal 9 9 4]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]]], .branch [.unbal 9 9 1, .rep 2 9]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 4]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]]], .branch [.unbal 9 9 1, .rep 2 9]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]], .rep 2 8]]], .branch [.unbal 9 9 1, .rep 2 9]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]

private theorem ok_d9_61 : checkLowerCert 9 9 [6, 3, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_61 = true := by
  decide

private theorem ref_d9_61 : IsRefuted 9 9 [6, 3, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [6, 3, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_61 ok_d9_61

private theorem ref_d9_59 : IsRefuted 9 9 [3, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d9_60 ref_d9_61

private def cert_d9_62 : LowerCert :=
  .rep 2 8

private theorem ok_d9_62 : checkLowerCert 9 9 [5, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_62 = true := by
  decide

private theorem ref_d9_62 : IsRefuted 9 9 [5, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [5, 4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_62 ok_d9_62

private theorem ref_d9_58 : IsRefuted 9 9 [4, 1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d9_59 ref_d9_62

private theorem ref_d9_40 : IsRefuted 9 9 [1, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d9_41 ref_d9_58

private def cert_d9_63 : LowerCert :=
  .rep 2 8

private theorem ok_d9_63 : checkLowerCert 9 9 [3, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_63 = true := by
  decide

private theorem ref_d9_63 : IsRefuted 9 9 [3, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [3, 2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_63 ok_d9_63

private theorem ref_d9_39 : IsRefuted 9 9 [2, 8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d9_40 ref_d9_63

private theorem ref_d9_11 : IsRefuted 9 9 [8, 0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d9_12 ref_d9_39

private theorem ref_d9_9 : IsRefuted 9 8 [0, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_10 ref_d9_11

private def cert_d9_66 : LowerCert :=
  .rep 2 9

private theorem ok_d9_66 : checkLowerCert 9 9 [1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_66 = true := by
  decide

private theorem ref_d9_66 : IsRefuted 9 9 [1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_66 ok_d9_66

private def cert_d9_70 : LowerCert :=
  .rep 2 9

private theorem ok_d9_70 : checkLowerCert 9 9 [4, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_70 = true := by
  decide

private theorem ref_d9_70 : IsRefuted 9 9 [4, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [4, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_70 ok_d9_70

private def cert_d9_74 : LowerCert :=
  .rep 2 9

private theorem ok_d9_74 : checkLowerCert 9 9 [7, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_74 = true := by
  decide

private theorem ref_d9_74 : IsRefuted 9 9 [7, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_74 ok_d9_74

private def cert_d9_76 : LowerCert :=
  .rep 2 8

private theorem ok_d9_76 : checkLowerCert 9 9 [0, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_76 = true := by
  decide

private theorem ref_d9_76 : IsRefuted 9 9 [0, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_76 ok_d9_76

private def cert_d9_78 : LowerCert :=
  .branch [.unbal 9 9 1, .rep 2 9]

private theorem ok_d9_78 : checkLowerCert 9 9 [0, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_78 = true := by
  decide

private theorem ref_d9_78 : IsRefuted 9 9 [0, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_78 ok_d9_78

private def cert_d9_81 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.unbal 18 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 18 9 0, .rep 7 48], .rep 2 8], .rep 2 9], .unbal 18 9 6], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8]], .unbal 18 9 1]], .rep 2 9], .unbal 18 9 7], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8]], .unbal 18 9 3], .rep 2 8]]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8]], .unbal 18 9 4], .rep 2 8]], .unbal 18 9 1]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8]], .branch [.branch [.unbal 9 9 7, .branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 4, .rep 2 9], .branch [.branch [.branch [.unbal 18 9 8, .rep 2 9], .branch [.rep 2 8, .branch [.branch [.unbal 18 9 0, .rep 2 9], .unbal 9 9 2]]], .rep 2 8]], .rep 2 8]], .unbal 18 9 1]], .rep 2 9]], .rep 2 8]], .rep 2 8]]

private theorem ok_d9_81 : checkLowerCert 9 9 [1, 0, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_81 = true := by
  decide

private theorem ref_d9_81 : IsRefuted 9 9 [1, 0, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 0, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_81 ok_d9_81

private def cert_d9_82 : LowerCert :=
  .branch [.branch [.unbal 9 9 4, .branch [.rep 2 9, .branch [.branch [.unbal 9 9 7, .branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 1, .rep 2 9], .branch [.branch [.branch [.rep 2 9, .unbal 18 9 5], .branch [.branch [.unbal 9 9 4, .branch [.rep 2 9, .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 1, .rep 2 9], .branch [.branch [.branch [.rep 2 9, .unbal 18 9 6], .branch [.branch [.unbal 9 9 4, .branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 1, .rep 2 9], .branch [.branch [.branch [.unbal 18 9 8, .rep 2 9], .branch [.unbal 25 25 2, .rep 2 8]], .rep 2 8]]], .rep 2 9], .unbal 9 9 3]], .rep 2 9]], .rep 2 8]], .rep 2 8]]], .rep 2 9], .unbal 9 9 2]]]], .rep 2 8]], .rep 2 8]]], .rep 2 9]], .rep 2 8]]], .rep 2 8]

private theorem ok_d9_82 : checkLowerCert 9 9 [3, 0, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_82 = true := by
  decide

private theorem ref_d9_82 : IsRefuted 9 9 [3, 0, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [3, 0, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_82 ok_d9_82

private theorem ref_d9_80 : IsRefuted 9 9 [0, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d9_81 ref_d9_82

private def cert_d9_83 : LowerCert :=
  .rep 2 8

private theorem ok_d9_83 : checkLowerCert 9 9 [1, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_83 = true := by
  decide

private theorem ref_d9_83 : IsRefuted 9 9 [1, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_83 ok_d9_83

private theorem ref_d9_79 : IsRefuted 9 9 [2, 7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d9_80 ref_d9_83

private theorem ref_d9_77 : IsRefuted 9 9 [7, 8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d9_78 ref_d9_79

private theorem ref_d9_75 : IsRefuted 9 9 [8, 6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_76 ref_d9_77

private theorem ref_d9_73 : IsRefuted 9 9 [6, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_74 ref_d9_75

private def cert_d9_86 : LowerCert :=
  .branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.branch [.unbal 9 9 4, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.branch [.unbal 9 9 4, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.branch [.branch [.branch [.unbal 25 25 3, .rep 2 9], .unbal 9 9 2], .rep 2 8], .rep 2 9]]], .branch [.rep 2 9, .unbal 18 9 5]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 3]], .rep 2 8], .rep 2 9], .unbal 9 9 0]]]]], .branch [.rep 2 9, .unbal 18 9 3]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .rep 2 9]], .rep 2 8]]]], .branch [.rep 2 9, .unbal 18 9 2]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]]], .rep 2 8]]]]

private theorem ok_d9_86 : checkLowerCert 9 9 [0, 6, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_86 = true := by
  decide

private theorem ref_d9_86 : IsRefuted 9 9 [0, 6, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 6, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_86 ok_d9_86

private def cert_d9_87 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 6, .rep 2 9], .branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 4, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.unbal 18 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 1, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 48, .rep 2 8], .rep 2 9], .unbal 18 9 6], .rep 2 8], .rep 2 9], .unbal 18 9 3], .rep 2 8]]], .rep 2 9], .unbal 18 9 8], .rep 2 8], .rep 2 9], .unbal 18 9 4], .rep 2 8]], .rep 2 8]]], .rep 2 8], .rep 2 9], .unbal 18 9 6], .rep 2 8]], .rep 2 8]], .unbal 18 9 1]], .rep 2 9], .branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .unbal 18 9 1]]]], .rep 2 8]], .rep 2 8]], .branch [.branch [.unbal 9 9 4, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 1, .rep 2 9], .branch [.branch [.branch [.rep 2 9, .unbal 18 9 5], .branch [.branch [.unbal 9 9 4, .branch [.rep 2 9, .unbal 18 9 6]], .rep 2 8]], .rep 2 8]]], .rep 2 9], .branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .unbal 18 9 5], .branch [.branch [.unbal 9 9 4, .branch [.rep 2 9, .unbal 17 17 8]], .rep 2 8]], .rep 2 8]]]]], .rep 2 8]]], .rep 2 8]], .rep 2 8]]

private theorem ok_d9_87 : checkLowerCert 9 9 [8, 6, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_87 = true := by
  decide

private theorem ref_d9_87 : IsRefuted 9 9 [8, 6, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 6, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_87 ok_d9_87

private theorem ref_d9_85 : IsRefuted 9 9 [6, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_86 ref_d9_87

private def cert_d9_88 : LowerCert :=
  .rep 2 8

private theorem ok_d9_88 : checkLowerCert 9 9 [8, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_88 = true := by
  decide

private theorem ref_d9_88 : IsRefuted 9 9 [8, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_88 ok_d9_88

private theorem ref_d9_84 : IsRefuted 9 9 [7, 4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_85 ref_d9_88

private theorem ref_d9_72 : IsRefuted 9 9 [4, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_73 ref_d9_84

private def cert_d9_89 : LowerCert :=
  .rep 2 8

private theorem ok_d9_89 : checkLowerCert 9 9 [6, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_89 = true := by
  decide

private theorem ref_d9_89 : IsRefuted 9 9 [6, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [6, 5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_89 ok_d9_89

private theorem ref_d9_71 : IsRefuted 9 9 [5, 3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d9_72 ref_d9_89

private theorem ref_d9_69 : IsRefuted 9 9 [3, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d9_70 ref_d9_71

private def cert_d9_93 : LowerCert :=
  .rep 2 9

private theorem ok_d9_93 : checkLowerCert 9 9 [6, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_93 = true := by
  decide

private theorem ref_d9_93 : IsRefuted 9 9 [6, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [6, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_93 ok_d9_93

private def cert_d9_96 : LowerCert :=
  .branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .unbal 18 9 3]]], .branch [.rep 2 9, .unbal 18 9 2]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]], .branch [.branch [.unbal 9 9 6, .branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 18 9 7, .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 8 50, .unbal 17 17 7], .rep 2 8], .rep 2 9], .unbal 9 9 4], .rep 2 8], .unbal 17 17 2], .rep 2 8], .rep 2 9]]], .unbal 17 17 5], .rep 2 8], .rep 2 9], .unbal 9 9 2]], .unbal 17 17 0], .rep 2 8]]]], .unbal 17 17 4], .rep 2 8], .rep 2 9], .unbal 9 9 0]]], .rep 2 8]]]], .branch [.rep 2 9, .unbal 18 9 2]], .rep 2 8], .rep 2 9]], .rep 2 8]], .rep 2 8]]]]

private theorem ok_d9_96 : checkLowerCert 9 9 [0, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_96 = true := by
  decide

private theorem ref_d9_96 : IsRefuted 9 9 [0, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_96 ok_d9_96

private def cert_d9_98 : LowerCert :=
  .rep 2 9

private theorem ok_d9_98 : checkLowerCert 9 9 [0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_98 = true := by
  decide

private theorem ref_d9_98 : IsRefuted 9 9 [0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_98 ok_d9_98

private def cert_d9_101 : LowerCert :=
  .branch [.unbal 9 9 3, .rep 2 9]

private theorem ok_d9_101 : checkLowerCert 9 9 [1, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_101 = true := by
  decide

private theorem ref_d9_101 : IsRefuted 9 9 [1, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_101 ok_d9_101

private def cert_d9_104 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 1, .rep 2 9], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 18 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 48, .unbal 18 9 8], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 4]], .rep 2 8], .rep 2 9], .unbal 18 9 3], .rep 2 8]]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 4]], .rep 2 8], .rep 2 9], .unbal 18 9 5], .rep 2 8]], .unbal 18 9 1]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .rep 2 9], .unbal 18 9 6], .rep 2 8]], .unbal 18 9 3], .rep 2 8]]], .rep 2 9], .branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 6, .rep 2 9], .unbal 17 17 8], .rep 2 8]], .unbal 18 9 3], .rep 2 8]]]]], .rep 2 8]]

private theorem ok_d9_104 : checkLowerCert 9 9 [3, 1, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_104 = true := by
  decide

private theorem ref_d9_104 : IsRefuted 9 9 [3, 1, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [3, 1, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_104 ok_d9_104

private def cert_d9_105 : LowerCert :=
  .branch [.branch [.unbal 9 9 6, .branch [.rep 2 9, .branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.rep 2 9, .unbal 18 9 7], .branch [.branch [.unbal 9 9 6, .branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.unbal 18 9 8, .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 3, .rep 2 9], .unbal 34 17 8], .rep 2 8]]]], .rep 2 9], .unbal 9 9 2]]], .rep 2 8]], .rep 2 8]]]], .rep 2 9]], .rep 2 8]], .rep 2 8]], .rep 2 8]]]]]], .rep 2 8]

private theorem ok_d9_105 : checkLowerCert 9 9 [5, 1, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_105 = true := by
  decide

private theorem ref_d9_105 : IsRefuted 9 9 [5, 1, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [5, 1, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_105 ok_d9_105

private theorem ref_d9_103 : IsRefuted 9 9 [1, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d9_104 ref_d9_105

private def cert_d9_106 : LowerCert :=
  .rep 2 8

private theorem ok_d9_106 : checkLowerCert 9 9 [3, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_106 = true := by
  decide

private theorem ref_d9_106 : IsRefuted 9 9 [3, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [3, 4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_106 ok_d9_106

private theorem ref_d9_102 : IsRefuted 9 9 [4, 0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d9_103 ref_d9_106

private theorem ref_d9_100 : IsRefuted 9 9 [0, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d9_101 ref_d9_102

private def cert_d9_107 : LowerCert :=
  .rep 2 8

private theorem ok_d9_107 : checkLowerCert 9 9 [1, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_107 = true := by
  decide

private theorem ref_d9_107 : IsRefuted 9 9 [1, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [1, 2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_107 ok_d9_107

private theorem ref_d9_99 : IsRefuted 9 9 [2, 8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d9_100 ref_d9_107

private theorem ref_d9_97 : IsRefuted 9 9 [8, 6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d9_98 ref_d9_99

private theorem ref_d9_95 : IsRefuted 9 9 [6, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_96 ref_d9_97

private def cert_d9_108 : LowerCert :=
  .rep 2 8

private theorem ok_d9_108 : checkLowerCert 9 9 [8, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_108 = true := by
  decide

private theorem ref_d9_108 : IsRefuted 9 9 [8, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_108 ok_d9_108

private theorem ref_d9_94 : IsRefuted 9 9 [7, 5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_95 ref_d9_108

private theorem ref_d9_92 : IsRefuted 9 9 [5, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_93 ref_d9_94

private def cert_d9_111 : LowerCert :=
  .branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 5, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .unbal 18 9 3]]], .unbal 17 17 4], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .rep 2 9], .unbal 18 9 5], .rep 2 8]]]], .branch [.rep 2 9, .unbal 18 9 2]], .rep 2 8], .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 5, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 1, .branch [.unbal 25 25 0, .rep 2 9]]], .rep 2 9], .unbal 9 9 4]], .branch [.rep 2 9, .unbal 18 9 2]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 0]], .rep 2 8]]]], .rep 2 9], .unbal 9 9 2]], .branch [.rep 2 9, .unbal 18 9 0]], .rep 2 8]], .rep 2 8]]]], .rep 2 9], .unbal 9 9 0]]], .rep 2 8]], .rep 2 8]]]], .rep 2 9]

private theorem ok_d9_111 : checkLowerCert 9 9 [7, 5, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_111 = true := by
  decide

private theorem ref_d9_111 : IsRefuted 9 9 [7, 5, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 5, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_111 ok_d9_111

private def cert_d9_112 : LowerCert :=
  .branch [.rep 2 8, .branch [.branch [.unbal 9 9 1, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 5, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 7, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 1, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 5, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 1, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.rep 6 40, .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 4]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8]], .rep 2 8]]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8]], .rep 2 8]], .rep 2 8]]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8]], .rep 2 8]], .rep 2 8]], .rep 2 8]]]

private theorem ok_d9_112 : checkLowerCert 9 9 [8, 5, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_112 = true := by
  decide

private theorem ref_d9_112 : IsRefuted 9 9 [8, 5, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 5, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_112 ok_d9_112

private theorem ref_d9_110 : IsRefuted 9 9 [5, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_111 ref_d9_112

private def cert_d9_113 : LowerCert :=
  .rep 2 8

private theorem ok_d9_113 : checkLowerCert 9 9 [7, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_113 = true := by
  decide

private theorem ref_d9_113 : IsRefuted 9 9 [7, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_113 ok_d9_113

private theorem ref_d9_109 : IsRefuted 9 9 [6, 3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_110 ref_d9_113

private theorem ref_d9_91 : IsRefuted 9 9 [3, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d9_92 ref_d9_109

private def cert_d9_114 : LowerCert :=
  .rep 2 8

private theorem ok_d9_114 : checkLowerCert 9 9 [5, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_114 = true := by
  decide

private theorem ref_d9_114 : IsRefuted 9 9 [5, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [5, 4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_114 ok_d9_114

private theorem ref_d9_90 : IsRefuted 9 9 [4, 1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d9_91 ref_d9_114

private theorem ref_d9_68 : IsRefuted 9 9 [1, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d9_69 ref_d9_90

private def cert_d9_115 : LowerCert :=
  .rep 2 8

private theorem ok_d9_115 : checkLowerCert 9 9 [3, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_115 = true := by
  decide

private theorem ref_d9_115 : IsRefuted 9 9 [3, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [3, 2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_115 ok_d9_115

private theorem ref_d9_67 : IsRefuted 9 9 [2, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d9_68 ref_d9_115

private theorem ref_d9_65 : IsRefuted 9 9 [0, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d9_66 ref_d9_67

private def cert_d9_119 : LowerCert :=
  .rep 2 9

private theorem ok_d9_119 : checkLowerCert 9 9 [3, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_119 = true := by
  decide

private theorem ref_d9_119 : IsRefuted 9 9 [3, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [3, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_119 ok_d9_119

private def cert_d9_123 : LowerCert :=
  .rep 2 9

private theorem ok_d9_123 : checkLowerCert 9 9 [6, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_123 = true := by
  decide

private theorem ref_d9_123 : IsRefuted 9 9 [6, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [6, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_123 ok_d9_123

private def cert_d9_127 : LowerCert :=
  .rep 2 8

private theorem ok_d9_127 : checkLowerCert 9 9 [0, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_127 = true := by
  decide

private theorem ref_d9_127 : IsRefuted 9 9 [0, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_127 ok_d9_127

private def cert_d9_129 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.unbal 18 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 18 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 48, .unbal 18 9 8], .rep 2 8], .rep 2 9], .unbal 18 9 5], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8]]], .rep 2 8], .rep 2 9], .unbal 18 9 6], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8]], .unbal 18 9 2]], .rep 2 9], .unbal 18 9 8], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8]], .unbal 18 9 3], .rep 2 8]]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8]], .branch [.branch [.unbal 9 9 6, .branch [.branch [.branch [.unbal 18 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.unbal 18 9 7, .rep 2 9], .branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 8], .unbal 9 9 1]]], .rep 2 8]], .rep 2 8]]], .rep 2 8], .rep 2 9]], .rep 2 8]], .rep 2 8]]

private theorem ok_d9_129 : checkLowerCert 9 9 [0, 8, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_129 = true := by
  decide

private theorem ref_d9_129 : IsRefuted 9 9 [0, 8, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 8, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_129 ok_d9_129

private def cert_d9_130 : LowerCert :=
  .branch [.branch [.unbal 9 9 3, .branch [.rep 2 9, .branch [.branch [.unbal 9 9 6, .branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 4], .branch [.branch [.unbal 9 9 3, .branch [.rep 2 9, .branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 5], .branch [.branch [.unbal 9 9 3, .branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 18 9 7, .rep 2 9], .branch [.unbal 25 25 1, .rep 2 8]]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .rep 2 9], .unbal 9 9 2]], .rep 2 9]], .rep 2 8]]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .rep 2 9], .unbal 9 9 1]]]], .rep 2 8]]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .rep 2 9]], .rep 2 8]]], .rep 2 8]

private theorem ok_d9_130 : checkLowerCert 9 9 [2, 8, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_130 = true := by
  decide

private theorem ref_d9_130 : IsRefuted 9 9 [2, 8, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [2, 8, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_130 ok_d9_130

private theorem ref_d9_128 : IsRefuted 9 9 [8, 1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d9_129 ref_d9_130

private theorem ref_d9_126 : IsRefuted 9 9 [1, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_127 ref_d9_128

private def cert_d9_131 : LowerCert :=
  .branch [.unbal 9 9 0, .rep 2 9]

private theorem ok_d9_131 : checkLowerCert 9 9 [8, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_131 = true := by
  decide

private theorem ref_d9_131 : IsRefuted 9 9 [8, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_131 ok_d9_131

private theorem ref_d9_125 : IsRefuted 9 9 [6, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_126 ref_d9_131

private def cert_d9_132 : LowerCert :=
  .rep 2 8

private theorem ok_d9_132 : checkLowerCert 9 9 [8, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_132 = true := by
  decide

private theorem ref_d9_132 : IsRefuted 9 9 [8, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_132 ok_d9_132

private theorem ref_d9_124 : IsRefuted 9 9 [7, 5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_125 ref_d9_132

private theorem ref_d9_122 : IsRefuted 9 9 [5, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_123 ref_d9_124

private def cert_d9_137 : LowerCert :=
  .rep 2 8

private theorem ok_d9_137 : checkLowerCert 9 9 [0, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_137 = true := by
  decide

private theorem ref_d9_137 : IsRefuted 9 9 [0, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_137 ok_d9_137

private def cert_d9_139 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 5, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.unbal 18 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 3, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 2, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 48, .branch [.rep 2 9, .unbal 9 9 6]], .rep 2 8], .rep 2 9], .unbal 18 9 5], .rep 2 8], .rep 2 9], .unbal 18 9 2]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .rep 2 9], .unbal 18 9 7], .rep 2 8], .rep 2 9], .unbal 18 9 3], .rep 2 8]]], .rep 2 9], .unbal 18 9 8], .rep 2 8], .rep 2 9], .unbal 18 9 5], .rep 2 8]], .rep 2 8]]], .rep 2 8], .rep 2 9], .branch [.rep 2 8, .branch [.branch [.unbal 18 9 0, .rep 2 9], .unbal 9 9 1]]], .rep 2 8]], .rep 2 8]]

private theorem ok_d9_139 : checkLowerCert 9 9 [0, 8, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_139 = true := by
  decide

private theorem ref_d9_139 : IsRefuted 9 9 [0, 8, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 8, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_139 ok_d9_139

private def cert_d9_140 : LowerCert :=
  .branch [.branch [.unbal 9 9 3, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 4], .branch [.branch [.unbal 9 9 3, .branch [.rep 2 9, .unbal 18 9 5]], .rep 2 8]]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .unbal 18 9 4], .branch [.branch [.unbal 9 9 3, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 17 17 6, .branch [.branch [.unbal 9 9 3, .branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 17 17 7, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 8 50, .rep 2 9], .unbal 9 9 6], .rep 2 8], .unbal 17 17 4], .rep 2 8], .rep 2 9], .unbal 9 9 1], .rep 2 8]]], .rep 2 9], .unbal 9 9 4]], .unbal 17 17 2], .rep 2 8], .rep 2 9]], .rep 2 8]]], .rep 2 9], .unbal 9 9 2]], .unbal 17 17 1], .rep 2 8]]], .rep 2 8]]], .rep 2 9], .unbal 9 9 1]]], .rep 2 8]]], .rep 2 8]

private theorem ok_d9_140 : checkLowerCert 9 9 [2, 8, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_140 = true := by
  decide

private theorem ref_d9_140 : IsRefuted 9 9 [2, 8, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [2, 8, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_140 ok_d9_140

private theorem ref_d9_138 : IsRefuted 9 9 [8, 1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d9_139 ref_d9_140

private theorem ref_d9_136 : IsRefuted 9 9 [1, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_137 ref_d9_138

private def cert_d9_141 : LowerCert :=
  .rep 2 9

private theorem ok_d9_141 : checkLowerCert 9 9 [8, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_141 = true := by
  decide

private theorem ref_d9_141 : IsRefuted 9 9 [8, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_141 ok_d9_141

private theorem ref_d9_135 : IsRefuted 9 9 [7, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_136 ref_d9_141

private def cert_d9_142 : LowerCert :=
  .branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.unbal 9 9 3, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 7, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.unbal 9 9 3, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.unbal 9 9 3, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 25 25 2, .rep 2 9], .unbal 9 9 1], .rep 2 8]]]], .branch [.rep 2 9, .unbal 18 9 4]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 2]], .rep 2 8], .rep 2 9]], .rep 2 8]]]], .branch [.rep 2 9, .unbal 18 9 2]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8]]], .rep 2 8]]]], .branch [.rep 2 9, .unbal 18 9 1]], .rep 2 8]], .rep 2 8]]], .rep 2 8]]]]

private theorem ok_d9_142 : checkLowerCert 9 9 [8, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_142 = true := by
  decide

private theorem ref_d9_142 : IsRefuted 9 9 [8, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_142 ok_d9_142

private theorem ref_d9_134 : IsRefuted 9 9 [5, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_135 ref_d9_142

private def cert_d9_143 : LowerCert :=
  .rep 2 8

private theorem ok_d9_143 : checkLowerCert 9 9 [7, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_143 = true := by
  decide

private theorem ref_d9_143 : IsRefuted 9 9 [7, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_143 ok_d9_143

private theorem ref_d9_133 : IsRefuted 9 9 [6, 3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_134 ref_d9_143

private theorem ref_d9_121 : IsRefuted 9 9 [3, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d9_122 ref_d9_133

private def cert_d9_144 : LowerCert :=
  .rep 2 8

private theorem ok_d9_144 : checkLowerCert 9 9 [5, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_144 = true := by
  decide

private theorem ref_d9_144 : IsRefuted 9 9 [5, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [5, 4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_144 ok_d9_144

private theorem ref_d9_120 : IsRefuted 9 9 [4, 2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d9_121 ref_d9_144

private theorem ref_d9_118 : IsRefuted 9 9 [2, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 3) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d9_119 ref_d9_120

private def cert_d9_148 : LowerCert :=
  .rep 2 9

private theorem ok_d9_148 : checkLowerCert 9 9 [5, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_148 = true := by
  decide

private theorem ref_d9_148 : IsRefuted 9 9 [5, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [5, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_148 ok_d9_148

private def cert_d9_153 : LowerCert :=
  .rep 2 8

private theorem ok_d9_153 : checkLowerCert 9 9 [0, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_153 = true := by
  decide

private theorem ref_d9_153 : IsRefuted 9 9 [0, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_153 ok_d9_153

private def cert_d9_155 : LowerCert :=
  .branch [.unbal 9 9 2, .rep 2 9]

private theorem ok_d9_155 : checkLowerCert 9 9 [0, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_155 = true := by
  decide

private theorem ref_d9_155 : IsRefuted 9 9 [0, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [0, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_155 ok_d9_155

private def cert_d9_158 : LowerCert :=
  .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.unbal 18 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 7 48, .rep 2 9], .unbal 18 9 7], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 3]], .rep 2 8], .rep 2 9], .unbal 18 9 2]], .rep 2 9], .unbal 18 9 8], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 3]], .rep 2 8], .rep 2 9], .unbal 18 9 4], .rep 2 8]]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 3]], .rep 2 8], .rep 2 9], .unbal 18 9 5], .rep 2 8]], .unbal 18 9 2]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 5, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 18 9 0, .rep 2 9], .unbal 9 9 3]], .unbal 17 17 1], .rep 2 8]], .rep 2 8]], .unbal 18 9 2]], .rep 2 9], .unbal 9 9 1]]], .rep 2 8]]

private theorem ok_d9_158 : checkLowerCert 9 9 [2, 0, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_158 = true := by
  decide

private theorem ref_d9_158 : IsRefuted 9 9 [2, 0, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [2, 0, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_158 ok_d9_158

private def cert_d9_159 : LowerCert :=
  .branch [.branch [.unbal 9 9 5, .branch [.rep 2 9, .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 2, .rep 2 9], .branch [.branch [.branch [.rep 2 9, .unbal 18 9 6], .branch [.branch [.unbal 9 9 5, .branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 2, .rep 2 9], .branch [.branch [.branch [.unbal 18 9 7, .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 2, .rep 2 9], .branch [.branch [.branch [.unbal 25 25 3, .rep 2 8], .unbal 34 17 1], .rep 2 8]]], .rep 2 9], .unbal 9 9 4]], .rep 2 9], .unbal 9 9 1]]], .rep 2 8]]], .rep 2 9], .unbal 9 9 3]], .rep 2 9]], .rep 2 8]], .rep 2 8]]], .rep 2 9], .unbal 9 9 1]]]], .rep 2 8]

private theorem ok_d9_159 : checkLowerCert 9 9 [4, 0, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_159 = true := by
  decide

private theorem ref_d9_159 : IsRefuted 9 9 [4, 0, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [4, 0, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_159 ok_d9_159

private theorem ref_d9_157 : IsRefuted 9 9 [0, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d9_158 ref_d9_159

private def cert_d9_160 : LowerCert :=
  .rep 2 8

private theorem ok_d9_160 : checkLowerCert 9 9 [2, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_160 = true := by
  decide

private theorem ref_d9_160 : IsRefuted 9 9 [2, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [2, 3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_160 ok_d9_160

private theorem ref_d9_156 : IsRefuted 9 9 [3, 8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d9_157 ref_d9_160

private theorem ref_d9_154 : IsRefuted 9 9 [8, 1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d9_155 ref_d9_156

private theorem ref_d9_152 : IsRefuted 9 9 [1, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_153 ref_d9_154

private def cert_d9_161 : LowerCert :=
  .rep 2 9

private theorem ok_d9_161 : checkLowerCert 9 9 [8, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_161 = true := by
  decide

private theorem ref_d9_161 : IsRefuted 9 9 [8, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_161 ok_d9_161

private theorem ref_d9_151 : IsRefuted 9 9 [7, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 1) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_152 ref_d9_161

private def cert_d9_162 : LowerCert :=
  .branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 7, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .unbal 18 9 2]]], .branch [.rep 2 9, .unbal 18 9 1]], .rep 2 8]], .rep 2 8]], .branch [.branch [.unbal 9 9 5, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .unbal 18 9 6], .branch [.branch [.unbal 9 9 5, .branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.unbal 17 17 8, .branch [.rep 2 8, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 8 50, .rep 2 8], .unbal 17 17 6], .rep 2 8], .rep 2 9], .unbal 9 9 3], .rep 2 8], .unbal 17 17 1], .rep 2 8]]]], .unbal 17 17 4], .rep 2 8], .rep 2 9], .unbal 9 9 1]]], .rep 2 8]]]], .unbal 17 17 3], .rep 2 8], .rep 2 9]], .rep 2 8]], .rep 2 8]]]], .branch [.rep 2 9, .unbal 18 9 1]], .rep 2 8]]], .rep 2 8]], .rep 2 8]]]]

private theorem ok_d9_162 : checkLowerCert 9 9 [8, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_162 = true := by
  decide

private theorem ref_d9_162 : IsRefuted 9 9 [8, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [8, 5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_162 ok_d9_162

private theorem ref_d9_150 : IsRefuted 9 9 [5, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 7) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_151 ref_d9_162

private def cert_d9_163 : LowerCert :=
  .rep 2 8

private theorem ok_d9_163 : checkLowerCert 9 9 [7, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_163 = true := by
  decide

private theorem ref_d9_163 : IsRefuted 9 9 [7, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_163 ok_d9_163

private theorem ref_d9_149 : IsRefuted 9 9 [6, 4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_150 ref_d9_163

private theorem ref_d9_147 : IsRefuted 9 9 [4, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 5) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d9_148 ref_d9_149

private def cert_d9_166 : LowerCert :=
  .branch [.rep 2 9, .branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 4, .rep 2 9], .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.rep 2 9, .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .unbal 18 9 2]]], .unbal 17 17 3], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8]], .unbal 18 9 4], .rep 2 8]]]], .branch [.rep 2 9, .unbal 18 9 1]], .rep 2 8]], .branch [.branch [.unbal 9 9 7, .branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 4, .rep 2 9], .branch [.branch [.branch [.unbal 18 9 8, .rep 2 9], .branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .branch [.branch [.branch [.unbal 9 9 4, .rep 2 9], .branch [.branch [.branch [.rep 2 8, .branch [.branch [.branch [.rep 2 8, .branch [.unbal 9 9 0, .branch [.rep 2 9, .unbal 25 25 8]]], .rep 2 9], .unbal 9 9 3]], .branch [.rep 2 9, .unbal 18 9 1]], .rep 2 8]], .rep 2 8]]]], .rep 2 9], .unbal 9 9 1]]], .rep 2 8]], .rep 2 8]]]], .rep 2 9]], .rep 2 8]], .rep 2 8]], .rep 2 8]]]]]

private theorem ok_d9_166 : checkLowerCert 9 9 [6, 4, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_166 = true := by
  decide

private theorem ref_d9_166 : IsRefuted 9 9 [6, 4, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [6, 4, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_166 ok_d9_166

private def cert_d9_167 : LowerCert :=
  .branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 2, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 4, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 6, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 2, .rep 2 9], .branch [.branch [.branch [.unbal 9 9 4, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.branch [.rep 2 8, .branch [.branch [.unbal 9 9 2, .rep 2 9], .branch [.branch [.branch [.branch [.branch [.branch [.rep 6 40, .branch [.rep 2 9, .unbal 9 9 5]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 3]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8]]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 3]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8]], .rep 2 8]]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8], .branch [.rep 2 9, .unbal 9 9 1]], .rep 2 8]], .rep 2 8]], .rep 2 8]]], .branch [.unbal 9 9 0, .rep 2 9]], .rep 2 8]

private theorem ok_d9_167 : checkLowerCert 9 9 [7, 4, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_167 = true := by
  decide

private theorem ref_d9_167 : IsRefuted 9 9 [7, 4, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [7, 4, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_167 ok_d9_167

private theorem ref_d9_165 : IsRefuted 9 9 [4, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 6) (c2 := 7) (by omega) (by decide) (by decide) (by decide) ref_d9_166 ref_d9_167

private def cert_d9_168 : LowerCert :=
  .rep 2 8

private theorem ok_d9_168 : checkLowerCert 9 9 [6, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_168 = true := by
  decide

private theorem ref_d9_168 : IsRefuted 9 9 [6, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [6, 5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_168 ok_d9_168

private theorem ref_d9_164 : IsRefuted 9 9 [5, 2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 6) (by omega) (by decide) (by decide) (by decide) ref_d9_165 ref_d9_168

private theorem ref_d9_146 : IsRefuted 9 9 [2, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 4) (c2 := 5) (by omega) (by decide) (by decide) (by decide) ref_d9_147 ref_d9_164

private def cert_d9_169 : LowerCert :=
  .rep 2 8

private theorem ok_d9_169 : checkLowerCert 9 9 [4, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_169 = true := by
  decide

private theorem ref_d9_169 : IsRefuted 9 9 [4, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [4, 3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_169 ok_d9_169

private theorem ref_d9_145 : IsRefuted 9 9 [3, 0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 4) (by omega) (by decide) (by decide) (by decide) ref_d9_146 ref_d9_169

private theorem ref_d9_117 : IsRefuted 9 9 [0, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 2) (c2 := 3) (by omega) (by decide) (by decide) (by decide) ref_d9_118 ref_d9_145

private def cert_d9_170 : LowerCert :=
  .rep 2 8

private theorem ok_d9_170 : checkLowerCert 9 9 [2, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_170 = true := by
  decide

private theorem ref_d9_170 : IsRefuted 9 9 [2, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  checkLowerCert_sound (by omega) 9 [2, 1, 8, 7, 6, 5, 4, 3, 2, 1, 0] cert_d9_170 ok_d9_170

private theorem ref_d9_116 : IsRefuted 9 9 [1, 8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 2) (by omega) (by decide) (by decide) (by decide) ref_d9_117 ref_d9_170

private theorem ref_d9_64 : IsRefuted 9 9 [8, 7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 1) (by omega) (by decide) (by decide) (by decide) ref_d9_65 ref_d9_116

private theorem ref_d9_8 : IsRefuted 9 8 [7, 6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split2 (c1 := 0) (c2 := 8) (by omega) (by decide) (by decide) (by decide) ref_d9_9 ref_d9_64

private theorem ref_d9_7 : IsRefuted 9 7 [6, 5, 4, 3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 7) (by omega) (by decide) (by decide) ref_d9_8

private theorem ref_d9_6 : IsRefuted 9 6 [5, 4, 3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 6) (by omega) (by decide) (by decide) ref_d9_7

private theorem ref_d9_5 : IsRefuted 9 5 [4, 3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 5) (by omega) (by decide) (by decide) ref_d9_6

private theorem ref_d9_4 : IsRefuted 9 4 [3, 2, 1, 0] :=
  isRefuted_split1 (c1 := 4) (by omega) (by decide) (by decide) ref_d9_5

private theorem ref_d9_3 : IsRefuted 9 3 [2, 1, 0] :=
  isRefuted_split1 (c1 := 3) (by omega) (by decide) (by decide) ref_d9_4

private theorem ref_d9_2 : IsRefuted 9 2 [1, 0] :=
  isRefuted_split1 (c1 := 2) (by omega) (by decide) (by decide) ref_d9_3

private theorem ref_d9_1 : IsRefuted 9 1 [0] :=
  isRefuted_split1 (c1 := 1) (by omega) (by decide) (by decide) ref_d9_2

private theorem ref_d9_0 : IsRefuted 9 0 [] :=
  isRefuted_split1 (c1 := 0) (by omega) (by decide) (by decide) ref_d9_1

/-- The empty prefix over `Fin 9` is refuted at threshold `8/7`. -/
theorem isRefuted_9 : IsRefuted 9 0 [] :=
  ref_d9_0

/-- Every 1-balanced sequence over `Fin 9` has critical exponent at least `8/7`. -/
theorem critExp_ge_9 (w : ℕ → Fin 9) (hw : IsBalanced w) :
    (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ≤ critExp w := by
  have h := (rtb_ge_of_refuted (d := 9) (by omega) isRefuted_9).1 w hw
  simpa using h

/-- Lower bound `RTB 9 ≥ 8/7` (unconditional, zero recurrence/aperiodicity assumption). -/
theorem rtb_ge_9 : (((8 : ℝ) / (7 : ℝ) : ℝ) : EReal) ≤ RTB 9 := by
  have h := (rtb_ge_of_refuted (d := 9) (by omega) isRefuted_9).2
  simpa using h

end BalancedRepetitionThreshold
