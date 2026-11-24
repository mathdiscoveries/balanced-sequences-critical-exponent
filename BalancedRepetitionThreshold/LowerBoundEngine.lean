module

public import BalancedRepetitionThreshold.Defs

import Mathlib.Tactic

/-!
# Pure-Kernel Lower-Bound Witness-Tree Engine

This module formalizes a sound finite-tree refutation checker for `RTB(d) ≥ (d - 1) / (d - 2)`.

Given an alphabet size `d ≥ 3` and any infinite 1-balanced sequence `w : ℕ → Fin d`, suppose
for contradiction that every factor of `w` has exponent strictly less than `(d - 1) / (d - 2)`.
Then:
1. Every prefix of `w`, canonicalized dynamically in order of first letter appearance, satisfies
   `MatchesPrefixRev w used uRev`.
2. Any candidate next letter `c` already appearing in the last `d - 2` letters of `uRev` creates
   an immediate single-letter repetition at distance `p ≤ d - 2` (exponent `(p + 1) / p ≥ (d - 1) / (d - 2)`),
   leaving at most `2` candidate extensions per node once `used ≥ d - 1`.
3. Every remaining branch is terminated by an explicit witness:
   - `LowerCert.rep r p`: matching run of length `r` at period `p` ending at the last letter with
     `p * (d - 1) ≤ (p + r) * (d - 2)`;
   - `LowerCert.unbal shift L a`: two equal-length windows of length `L` whose counts of letter `a`
     differ by at least `2`.

Every tree check executes strictly inside the Lean 4 kernel via `decide` (zero `native_decide`,
zero `set_option`), and `isRefuted_step` allows large trees (`d = 9, 10`) to be split cleanly
across independent subtrees within default kernel heartbeats.
-/

@[expose] public section

namespace BalancedRepetitionThreshold

/-- Reversed-prefix canonical matching predicate: `uRev` (head = last letter) matches `w[0..n)`
under a map `f : ℕ → Fin d` injective on `{0, ..., used - 1}`. -/
def MatchesPrefixRev {d : ℕ} (w : ℕ → Fin d) (used : ℕ) (uRev : List ℕ) : Prop :=
  used ≤ d ∧
  ∃ f : ℕ → Fin d,
    (∀ a b, a < used → b < used → f a = f b → a = b) ∧
    (∀ x ∈ uRev, x < used) ∧
    (∀ k (hk : k < uRev.length), w (uRev.length - 1 - k) = f uRev[k])

/-- A node `(used, uRev)` is refuted at threshold `(d - 1) / (d - 2)` if no balanced `d`-ary
sequence avoiding exponents `≥ (d - 1) / (d - 2)` can match `(used, uRev)`. -/
def IsRefuted (d used : ℕ) (uRev : List ℕ) : Prop :=
  ∀ w : ℕ → Fin d, IsBalanced w →
    (∀ i L p, HasPeriod w i L p → L * (d - 2) < p * (d - 1)) →
    ¬ MatchesPrefixRev w used uRev

/-- Test whether `c` appears among the first `k` elements of `xs`. -/
def memTake : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => false
  | k + 1, c, x :: xs => (x == c) || memTake k c xs

/-- Test whether the first `r` elements of `xs` and `ys` exist and agree elementwise. -/
def eqPrefix : ℕ → List ℕ → List ℕ → Bool
  | 0, _, _ => true
  | _ + 1, [], _ => false
  | _ + 1, _, [] => false
  | r + 1, x :: xs, y :: ys => (x == y) && eqPrefix r xs ys

/-- Count occurrences of `a` among the first `L` elements of `xs`. -/
def countTake (a : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | L + 1, x :: xs => (if x == a then 1 else 0) + countTake a L xs

/-- Compressed finite witness tree for `RTB(d) ≥ (d - 1) / (d - 2)`. -/
inductive LowerCert : Type
  | rep (r p : ℕ) : LowerCert
  | unbal (shift L a : ℕ) : LowerCert
  | branch (children : List LowerCert) : LowerCert

/-- Structurally recursive helper for `nextCandidate` (kernel-reducible under `decide`). -/
def nextCandidateGo (d : ℕ) (uRev : List ℕ) (c : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
      if memTake (d - 2) c uRev then nextCandidateGo d uRev (c + 1) fuel
      else some c

/-- Find the least candidate `c' ∈ [c, lim)` not occurring in the first `d - 2` letters of `uRev`. -/
def nextCandidate (d : ℕ) (uRev : List ℕ) (c lim : ℕ) : Option ℕ :=
  nextCandidateGo d uRev c (lim - c)

mutual
/-- Check that `uRev` has an explicit repetition or balance witness, or that every non-recent
canonical extension `c < min (used + 1) d` is refuted by the next certificate in `children`. -/
def checkLowerCert (d used : ℕ) (uRev : List ℕ) : LowerCert → Bool
  | .rep r p =>
      decide (0 < p) && decide (0 < r) &&
      decide (p + r ≤ uRev.length) &&
      decide (p * (d - 1) ≤ (p + r) * (d - 2)) &&
      eqPrefix r uRev (uRev.drop p)
  | .unbal shift L a =>
      decide (a < used) && decide (0 < L) &&
      decide (shift + L ≤ uRev.length) &&
      let c1 := countTake a L uRev
      let c2 := countTake a L (uRev.drop shift)
      decide (c1 + 2 ≤ c2) || decide (c2 + 2 ≤ c1)
  | .branch children =>
      checkLowerCertList d used uRev 0 (min (used + 1) d) children

/-- Check a list of child certificates against all non-recent extensions in `[c, lim)`. -/
def checkLowerCertList (d used : ℕ) (uRev : List ℕ) (c lim : ℕ) : List LowerCert → Bool
  | [] => (nextCandidate d uRev c lim).isNone
  | child :: rest =>
      match nextCandidate d uRev c lim with
      | none => false
      | some c' =>
          checkLowerCert d (max used (c' + 1)) (c' :: uRev) child &&
          checkLowerCertList d used uRev (c' + 1) lim rest
end

/-- Soundness of `memTake`: if `memTake k c xs = true`, there is an index `j < k` with `xs[j] = c`. -/
theorem memTake_eq_true {k c : ℕ} {xs : List ℕ} (h : memTake k c xs = true) :
    ∃ j : ℕ, j < k ∧ ∃ hj : j < xs.length, xs[j] = c := by
  induction k generalizing xs with
  | zero => simp [memTake] at h
  | succ k ih =>
    cases xs with
    | nil => simp [memTake] at h
    | cons x xs =>
      simp only [memTake, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | hrest
      · exact ⟨0, Nat.zero_lt_succ k, Nat.zero_lt_succ _, rfl⟩
      · obtain ⟨j, hjk, hjlen, hval⟩ := ih hrest
        exact ⟨j + 1, Nat.succ_lt_succ hjk, Nat.succ_lt_succ hjlen, hval⟩

/-- Soundness of `eqPrefix`: if `eqPrefix r xs ys = true`, then `xs` and `ys` agree on `[0, r)`. -/
theorem eqPrefix_eq_true {r : ℕ} {xs ys : List ℕ} (h : eqPrefix r xs ys = true) :
    ∀ t : ℕ, t < r → ∃ hx : t < xs.length, ∃ hy : t < ys.length, xs[t] = ys[t] := by
  induction r generalizing xs ys with
  | zero => intro t ht; omega
  | succ r ih =>
    cases xs with
    | nil => simp [eqPrefix] at h
    | cons x xs =>
      cases ys with
      | nil => simp [eqPrefix] at h
      | cons y ys =>
        simp only [eqPrefix, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨rfl, hrest⟩
        intro t ht
        cases t with
        | zero => exact ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _, rfl⟩
        | succ t =>
          obtain ⟨hx, hy, hval⟩ := ih hrest t (Nat.lt_of_succ_lt_succ ht)
          exact ⟨Nat.succ_lt_succ hx, Nat.succ_lt_succ hy, hval⟩

/-- `countTake a L xs` equals `((xs.take L).count a)`. -/
theorem countTake_eq_count_take (a L : ℕ) (xs : List ℕ) :
    countTake a L xs = (xs.take L).count a := by
  induction L generalizing xs with
  | zero => simp [countTake]
  | succ L ih =>
    cases xs with
    | nil => simp [countTake]
    | cons x xs =>
      simp only [countTake, List.take_succ_cons, List.count_cons]
      rw [ih xs]
      by_cases h : x = a
      · subst h; simp; omega
      · have h1 : (x == a) = false := beq_false_of_ne h
        simp [h1]

/-- Counting `a` in `(uRev.drop s).take L` equals counting `f a` in `factor w (n - (s + L)) L`
under an injective reversed-prefix match. -/
theorem countTake_drop_eq_factor_count {d used s L a : ℕ} {w : ℕ → Fin d} {uRev : List ℕ}
    {f : ℕ → Fin d}
    (hinj : ∀ x y, x < used → y < used → f x = f y → x = y)
    (hlt : ∀ x ∈ uRev, x < used)
    (hmatch : ∀ k (hk : k < uRev.length), w (uRev.length - 1 - k) = f uRev[k])
    (ha : a < used) (hsL : s + L ≤ uRev.length) :
    countTake a L (uRev.drop s) = (factor w (uRev.length - (s + L)) L).count (f a) := by
  rw [countTake_eq_count_take, count_factor_eq_card_filter]
  -- Express ((uRev.drop s).take L).count a as a Finset.filter card over Finset.range L.
  have hlist : ((uRev.drop s).take L).count a =
      ((Finset.range L).filter (fun t => (uRev[s + t]?).getD (a + 1) = a)).card := by
    have h1 : (uRev.drop s).take L =
        (List.range L).map (fun t => (uRev[s + t]?).getD (a + 1)) := by
      apply List.ext_getElem
      · simp; omega
      · intro t ht1 ht2
        simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
        have hst : s + t < uRev.length := by simp at ht1; omega
        simp [List.getElem?_eq_getElem hst]
    rw [h1]
    exact count_factor_eq_card_filter (fun k => (uRev[k]?).getD (a + 1)) a s L
  rw [hlist]
  -- Biject t ↦ L - 1 - t between the two Finset.range L filters.
  apply Finset.card_bij (fun t _ => L - 1 - t)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    rcases ht with ⟨htL, hval⟩
    refine ⟨by omega, ?_⟩
    have hst : s + t < uRev.length := by omega
    simp only [List.getElem?_eq_getElem hst, Option.getD_some] at hval
    have hpos : uRev.length - (s + L) + (L - 1 - t) = uRev.length - 1 - (s + t) := by omega
    rw [hpos, hmatch (s + t) hst, hval]
  · intro t1 ht1 t2 ht2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at ht1 ht2
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rcases hj with ⟨hjL, hval⟩
    refine ⟨L - 1 - j, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have hst : s + (L - 1 - j) < uRev.length := by omega
    simp only [List.getElem?_eq_getElem hst, Option.getD_some]
    have hpos : uRev.length - 1 - (s + (L - 1 - j)) = uRev.length - (s + L) + j := by omega
    have hmw := hmatch (s + (L - 1 - j)) hst
    rw [hpos, hval] at hmw
    have hmem : uRev[s + (L - 1 - j)] < used := hlt _ (List.getElem_mem hst)
    exact (hinj _ _ ha hmem hmw).symm

/-- Every sequence `w : ℕ → Fin d` matches the empty prefix `(used = 0, uRev = [])`. -/
theorem matchesPrefixRev_nil {d : ℕ} (hd : 0 < d) (w : ℕ → Fin d) :
    MatchesPrefixRev w 0 [] := by
  refine ⟨Nat.zero_le d, fun _ => ⟨0, hd⟩, ?_, ?_, ?_⟩
  · intro a _ ha; omega
  · intro x hx; simp at hx
  · intro k hk; simp at hk

/-- Extension step: from any match `(used, uRev)`, the next letter `w uRev.length` extends the
match to some `c < min (used + 1) d`. -/
theorem matchesPrefixRev_extend {d used : ℕ} {w : ℕ → Fin d} {uRev : List ℕ}
    (hm : MatchesPrefixRev w used uRev) :
    ∃ c : ℕ, c < min (used + 1) d ∧ MatchesPrefixRev w (max used (c + 1)) (c :: uRev) := by
  rcases hm with ⟨hud, f, hinj, hlt, hmatch⟩
  let x : Fin d := w uRev.length
  by_cases hex : ∃ c : ℕ, c < used ∧ f c = x
  · rcases hex with ⟨c, hc, hfc⟩
    refine ⟨c, by omega, ?_⟩
    have hmax : max used (c + 1) = used := by omega
    rw [hmax]
    refine ⟨hud, f, hinj, ?_, ?_⟩
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hc
      · exact hlt y hy
    · intro k hk
      cases k with
      | zero =>
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
        exact hfc.symm
      | succ k =>
        simp only [List.length_cons, List.getElem_cons_succ]
        have hk' : k < uRev.length := by simp at hk; omega
        have hpos : uRev.length + 1 - 1 - (k + 1) = uRev.length - 1 - k := by omega
        rw [hpos]
        exact hmatch k hk'
  · push Not at hex
    -- Since x is outside f '' {0, ..., used - 1}, we must have used < d by pigeonhole.
    have hult : used < d := by
      by_contra hge
      have heq : used = d := by omega
      subst heq
      let g : Fin used → Fin used := fun i => f i.val
      have hginj : Function.Injective g := by
        intro i j hij
        exact Fin.ext (hinj i.val j.val i.isLt j.isLt hij)
      have hgsurj : Function.Surjective g := Finite.injective_iff_surjective.mp hginj
      obtain ⟨i, hi⟩ := hgsurj x
      exact hex i.val i.isLt hi
    refine ⟨used, by omega, ?_⟩
    have hmax : max used (used + 1) = used + 1 := by omega
    rw [hmax]
    let f' : ℕ → Fin d := fun k => if k = used then x else f k
    refine ⟨by omega, f', ?_, ?_, ?_⟩
    · intro a b ha hb hab
      by_cases hau : a = used <;> by_cases hbu : b = used
      · omega
      · simp only [f', hau, ↓reduceIte, hbu] at hab
        exact False.elim (hex b (by omega) hab.symm)
      · simp only [f', hau, ↓reduceIte, hbu] at hab
        exact False.elim (hex a (by omega) hab)
      · simp only [f', hau, ↓reduceIte, hbu] at hab
        exact hinj a b (by omega) (by omega) hab
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · have := hlt y hy; omega
    · intro k hk
      cases k with
      | zero =>
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero,
          f', ↓reduceIte]
        rfl
      | succ k =>
        simp only [List.length_cons, List.getElem_cons_succ]
        have hk' : k < uRev.length := by simp at hk; omega
        have hpos : uRev.length + 1 - 1 - (k + 1) = uRev.length - 1 - k := by omega
        have hne : uRev[k] ≠ used := by
          have := hlt _ (List.getElem_mem hk'); omega
        rw [hpos]
        simp only [f', hne, ↓reduceIte]
        exact hmatch k hk'

/-- Soundness of the recent-letter filter: if `c` appeared within the last `d - 2` letters of
`uRev`, then extending by `c` is immediately refuted. -/
theorem isRefuted_of_memTake {d used c : ℕ} {uRev : List ℕ}
    (hd : 3 ≤ d) (hmem : memTake (d - 2) c uRev = true) :
    IsRefuted d (max used (c + 1)) (c :: uRev) := by
  intro w _ hno hm
  obtain ⟨j, hjlt, hjlen, hval⟩ := memTake_eq_true hmem
  rcases hm with ⟨_, f, _, _, hmatch⟩
  let n := uRev.length
  let p := j + 1
  have hp_pos : 0 < p := Nat.succ_pos j
  have hp_le : p ≤ d - 2 := by omega
  have hper : HasPeriod w (n - p) (p + 1) p := by
    refine ⟨hp_pos, by omega, ?_⟩
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    have h1 := hmatch 0 (Nat.zero_lt_succ n)
    have h2 := hmatch (j + 1) (Nat.succ_lt_succ hjlen)
    simp only [List.length_cons, List.getElem_cons_zero, List.getElem_cons_succ, hval] at h1 h2
    have heq1 : n - p + 0 = n + 1 - 1 - (j + 1) := by omega
    have heq2 : n - p + 0 + p = n + 1 - 1 - 0 := by omega
    rw [heq2, heq1, h1, h2]
  have hstrict := hno (n - p) (p + 1) p hper
  have hineq : p * (d - 1) ≤ (p + 1) * (d - 2) := by
    have : p * (d - 1) = p * (d - 2) + p := by
      have : d - 1 = (d - 2) + 1 := by omega
      rw [this]; ring
    have : (p + 1) * (d - 2) = p * (d - 2) + (d - 2) := by ring
    omega
  omega

/-- Modular branching step: if every non-recent canonical extension `c < min (used + 1) d` is
refuted, then `(used, uRev)` is refuted. -/
theorem isRefuted_step {d used : ℕ} {uRev : List ℕ} (hd : 3 ≤ d)
    (hchild : ∀ c : ℕ, c < min (used + 1) d → memTake (d - 2) c uRev = false →
      IsRefuted d (max used (c + 1)) (c :: uRev)) :
    IsRefuted d used uRev := by
  intro w hbal hno hm
  obtain ⟨c, hclim, hm'⟩ := matchesPrefixRev_extend hm
  cases hmt : memTake (d - 2) c uRev
  · exact hchild c hclim hmt w hbal hno hm'
  · exact isRefuted_of_memTake hd hmt w hbal hno hm'

/-- Soundness of `LowerCert.rep`. -/
theorem isRefuted_rep {d used r p : ℕ} {uRev : List ℕ}
    (hp : 0 < p) (hr : 0 < r) (hlen : p + r ≤ uRev.length)
    (hexp : p * (d - 1) ≤ (p + r) * (d - 2))
    (heq : eqPrefix r uRev (uRev.drop p) = true) :
    IsRefuted d used uRev := by
  intro w _ hno hm
  rcases hm with ⟨_, f, _, _, hmatch⟩
  have hpre := eqPrefix_eq_true heq
  let n := uRev.length
  let i := n - (p + r)
  have hper : HasPeriod w i (p + r) p := by
    refine ⟨hp, by omega, ?_⟩
    intro k hk
    have hkr : k < r := by omega
    let t := r - 1 - k
    have htr : t < r := by omega
    obtain ⟨hx, hy, hxy⟩ := hpre t htr
    have htp : t + p < n := by omega
    have hdrop : (uRev.drop p)[t]'hy = uRev[p + t]'(by omega) := List.getElem_drop
    rw [hdrop] at hxy
    have hm1 := hmatch (p + t) (by omega)
    have hm2 := hmatch t hx
    have hpos1 : i + k = n - 1 - (p + t) := by omega
    have hpos2 : i + k + p = n - 1 - t := by omega
    rw [hpos2, hpos1, hm1, hm2, hxy]
  have hstrict := hno i (p + r) p hper
  omega

/-- Soundness of `LowerCert.unbal`. -/
theorem isRefuted_unbal {d used shift L a : ℕ} {uRev : List ℕ}
    (ha : a < used) (_hL : 0 < L) (hsL : shift + L ≤ uRev.length)
    (hdiff : countTake a L uRev + 2 ≤ countTake a L (uRev.drop shift) ∨
             countTake a L (uRev.drop shift) + 2 ≤ countTake a L uRev) :
    IsRefuted d used uRev := by
  intro w hbal _ hm
  rcases hm with ⟨_, f, hinj, hlt, hmatch⟩
  have h1 := countTake_drop_eq_factor_count (s := 0) (L := L) hinj hlt hmatch ha (by omega)
  have h2 := countTake_drop_eq_factor_count (s := shift) (L := L) hinj hlt hmatch ha hsL
  simp only [List.drop_zero, zero_add] at h1
  have hb := hbal (f a) L (uRev.length - L) (uRev.length - (shift + L))
  rw [← h1, ← h2] at hb
  rw [abs_le] at hb
  omega

/-- Soundness of `nextCandidate`: if `none`, every `c' ∈ [c, lim)` is in the last `d - 2` letters. -/
theorem nextCandidate_none {d : ℕ} {uRev : List ℕ} {c lim : ℕ}
    (h : nextCandidate d uRev c lim = none) :
    ∀ x : ℕ, c ≤ x → x < lim → memTake (d - 2) x uRev = true := by
  unfold nextCandidate at h
  generalize hk : lim - c = fuel at h
  induction fuel generalizing c with
  | zero =>
    intro x hx1 hx2; omega
  | succ fuel ih =>
    simp only [nextCandidateGo] at h
    cases hmt : memTake (d - 2) c uRev
    · simp [hmt] at h
    · simp only [hmt, ↓reduceIte] at h
      intro x hx1 hx2
      by_cases heq : x = c
      · subst heq; exact hmt
      · exact ih (c := c + 1) (by omega) h x (by omega) hx2

/-- Soundness of `nextCandidate`: if `some c'`, then `c ≤ c' < lim` and every `x ∈ [c, c')` is
in the last `d - 2` letters. -/
theorem nextCandidate_some {d : ℕ} {uRev : List ℕ} {c lim c' : ℕ}
    (h : nextCandidate d uRev c lim = some c') :
    c ≤ c' ∧ c' < lim ∧ ∀ x : ℕ, c ≤ x → x < c' → memTake (d - 2) x uRev = true := by
  unfold nextCandidate at h
  generalize hk : lim - c = fuel at h
  induction fuel generalizing c with
  | zero =>
    simp [nextCandidateGo] at h
  | succ fuel ih =>
    simp only [nextCandidateGo] at h
    cases hmt : memTake (d - 2) c uRev
    · simp only [hmt, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨le_refl c, by omega, fun x hx1 hx2 => by omega⟩
    · simp only [hmt, ↓reduceIte] at h
      obtain ⟨h1, h2, hall⟩ := ih (c := c + 1) (by omega) h
      refine ⟨by omega, h2, fun x hx1 hx2 => ?_⟩
      by_cases heq : x = c
      · subst heq; exact hmt
      · exact hall x (by omega) hx2

mutual
/-- Main soundness theorem for `checkLowerCert`: any passing certificate refutes `(used, uRev)`. -/
theorem checkLowerCert_sound {d : ℕ} (hd : 3 ≤ d) (used : ℕ) (uRev : List ℕ) :
    ∀ cert : LowerCert,
      checkLowerCert d used uRev cert = true → IsRefuted d used uRev
  | .rep r p, hchk => by
    simp only [checkLowerCert, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨⟨hp, hr⟩, hlen⟩, hexp⟩, heq⟩
    exact isRefuted_rep hp hr hlen hexp heq
  | .unbal shift L a, hchk => by
    simp only [checkLowerCert, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨ha, hL⟩, hsL⟩, hdiff⟩
    exact isRefuted_unbal ha hL hsL hdiff
  | .branch children, hchk => by
    simp only [checkLowerCert] at hchk
    exact isRefuted_step hd fun c hclim hmt =>
      checkLowerCertList_sound hd used uRev 0 (min (used + 1) d) children hchk c (Nat.zero_le c)
        hclim hmt

/-- Mutual soundness helper for `checkLowerCertList`. -/
theorem checkLowerCertList_sound {d : ℕ} (hd : 3 ≤ d) (used : ℕ) (uRev : List ℕ) :
    ∀ (c0 lim : ℕ) (cs : List LowerCert),
      checkLowerCertList d used uRev c0 lim cs = true →
      ∀ c : ℕ, c0 ≤ c → c < lim → memTake (d - 2) c uRev = false →
        IsRefuted d (max used (c + 1)) (c :: uRev)
  | c0, lim, [], hchk => by
    simp only [checkLowerCertList, Option.isNone_iff_eq_none] at hchk
    intro c hc1 hc2 hmt
    have ht := nextCandidate_none hchk c hc1 hc2
    rw [ht] at hmt
    exact Bool.noConfusion hmt
  | c0, lim, child :: rest, hchk => by
    simp only [checkLowerCertList] at hchk
    cases hnc : nextCandidate d uRev c0 lim with
    | none => simp [hnc] at hchk
    | some c' =>
      simp only [hnc, Bool.and_eq_true] at hchk
      rcases hchk with ⟨hchild, hrest⟩
      obtain ⟨hc'1, hc'2, hskip⟩ := nextCandidate_some hnc
      intro c hc1 hc2 hmt
      by_cases hlt : c < c'
      · have ht := hskip c hc1 hlt
        rw [ht] at hmt
        exact Bool.noConfusion hmt
      · by_cases heq : c = c'
        · subst heq
          exact checkLowerCert_sound hd (max used (c + 1)) (c :: uRev) child hchild
        · exact checkLowerCertList_sound hd used uRev (c' + 1) lim rest hrest c (by omega) hc2 hmt
end

/-- Modular 1-child split: if `c1` is the sole non-recent canonical extension of `(used, uRev)`
and is refuted, then `(used, uRev)` is refuted. -/
theorem isRefuted_split1 {d used c1 : ℕ} {uRev : List ℕ} (hd : 3 ≤ d)
    (h1 : nextCandidate d uRev 0 (min (used + 1) d) = some c1)
    (h2 : nextCandidate d uRev (c1 + 1) (min (used + 1) d) = none)
    (hr1 : IsRefuted d (max used (c1 + 1)) (c1 :: uRev)) :
    IsRefuted d used uRev := by
  apply isRefuted_step hd
  intro c hclim hmt
  obtain ⟨hc1_lo, _, hskip1⟩ := nextCandidate_some h1
  by_cases hlt : c < c1
  · have ht := hskip1 c (Nat.zero_le c) hlt
    rw [ht] at hmt
    exact Bool.noConfusion hmt
  · by_cases heq : c = c1
    · subst heq; exact hr1
    · have ht := nextCandidate_none h2 c (by omega) hclim
      rw [ht] at hmt
      exact Bool.noConfusion hmt

/-- Modular 2-child split: if `c1, c2` are the only two non-recent canonical extensions of
`(used, uRev)` and both are refuted, then `(used, uRev)` is refuted. -/
theorem isRefuted_split2 {d used c1 c2 : ℕ} {uRev : List ℕ} (hd : 3 ≤ d)
    (h1 : nextCandidate d uRev 0 (min (used + 1) d) = some c1)
    (h2 : nextCandidate d uRev (c1 + 1) (min (used + 1) d) = some c2)
    (h3 : nextCandidate d uRev (c2 + 1) (min (used + 1) d) = none)
    (hr1 : IsRefuted d (max used (c1 + 1)) (c1 :: uRev))
    (hr2 : IsRefuted d (max used (c2 + 1)) (c2 :: uRev)) :
    IsRefuted d used uRev := by
  apply isRefuted_step hd
  intro c hclim hmt
  obtain ⟨_, _, hskip1⟩ := nextCandidate_some h1
  obtain ⟨hc2_lo, _, hskip2⟩ := nextCandidate_some h2
  by_cases hlt1 : c < c1
  · have ht := hskip1 c (Nat.zero_le c) hlt1
    rw [ht] at hmt
    exact Bool.noConfusion hmt
  · by_cases heq1 : c = c1
    · subst heq1; exact hr1
    · by_cases hlt2 : c < c2
      · have ht := hskip2 c (by omega) hlt2
        rw [ht] at hmt
        exact Bool.noConfusion hmt
      · by_cases heq2 : c = c2
        · subst heq2; exact hr2
        · have ht := nextCandidate_none h3 c (by omega) hclim
          rw [ht] at hmt
          exact Bool.noConfusion hmt

/-- From a refutation of the empty prefix `(0, [])`, deduce the lower bound
`((d - 1) / (d - 2)) ≤ critExp w` for every balanced `d`-ary sequence `w`, and hence
`((d - 1) / (d - 2)) ≤ RTB d`. -/
theorem rtb_ge_of_refuted {d : ℕ} (hd : 3 ≤ d) (href : IsRefuted d 0 []) :
    (∀ w : ℕ → Fin d, IsBalanced w →
      ((((d - 1 : ℕ) : ℝ) / ((d - 2 : ℕ) : ℝ) : ℝ) : EReal) ≤ critExp w) ∧
    ((((d - 1 : ℕ) : ℝ) / ((d - 2 : ℕ) : ℝ) : ℝ) : EReal) ≤ RTB d := by
  have hall : ∀ w : ℕ → Fin d, IsBalanced w →
      ((((d - 1 : ℕ) : ℝ) / ((d - 2 : ℕ) : ℝ) : ℝ) : EReal) ≤ critExp w := by
    intro w hbal
    by_contra hnot
    have hno : ∀ i L p, HasPeriod w i L p → L * (d - 2) < p * (d - 1) := by
      intro i L p hper
      by_contra hge
      push Not at hge
      exact hnot (le_critExp_of_period (by omega) hper hge)
    exact href w hbal hno (matchesPrefixRev_nil (by omega) w)
  exact ⟨hall, le_RTB_of_forall hall⟩

end BalancedRepetitionThreshold
