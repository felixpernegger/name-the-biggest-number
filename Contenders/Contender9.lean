/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
import Contenders.Contender8
import Mathlib.Logic.Function.Iterate

def reverseConwayChain : List ℕ → ℕ
  | [] => 1
  | [a] => a
  | [b, a] => a ^ b
  | [c, b, a] => knuthArrow a b c
  | 0 :: l => reverseConwayChain l
  | 1 :: l => reverseConwayChain l
  | _ :: 0 :: l => reverseConwayChain l
  | _ :: 1 :: l => reverseConwayChain l
  | (b + 1) :: (a + 1) :: l => reverseConwayChain (b :: (reverseConwayChain ((b + 1) :: a :: l)) :: l)
  termination_by l => (l.length, List.getI l 0, List.getI l 1)
  decreasing_by
  all_goals simp [Prod.lex_def]

theorem reverseConwayChain_zero (l : List ℕ) (hl : 3 ≤ l.length):
    reverseConwayChain (0 :: l) = reverseConwayChain l := by
  rw [reverseConwayChain] <;> grind

/--
Conway chains as described in
https://en.wikipedia.org/wiki/Conway_chained_arrow_notation
We filter out element of value zero to stay consistent with the original notation.
-/
def conwayChain (l : List ℕ) : ℕ := reverseConwayChain (l.reverse.filter (· ≠ 0))

theorem knuthArrow_conwayChain (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    knuthArrow a b c = conwayChain [a, b, c] := by
  have : (List.filter (fun x => decide (x ≠ 0)) [a, b, c].reverse) = [c, b, a] := by grind
  rw [conwayChain, this, reverseConwayChain]

/-- Submitted by Felix Pernegger. -/
def contender_9 : Nat := conwayChain [3, 3, 65, 2]

theorem contender_8_lt_contender_9 : contender_8 < contender_9 := by
  let f (n : ℕ) : ℕ := knuthArrow 3 3 n
  have f_eq {n : ℕ} (hn : n ≠ 0) : f n = conwayChain [3, 3, n] := by
    unfold f
    rw [knuthArrow_conwayChain] <;> grind
  have f_mono : StrictMono f^[64] := by
    refine StrictMono.iterate ?_ 64
    intro n m nm
    unfold f
    exact knuthArrow_strict_mono_third le_rfl (by norm_num) nm
  have ite_one {n : ℕ} (hn : n ≠ 0) : f^[n] 4 = grahamSeq n := by
    induction n with
    | zero => simp_all
    | succ n ih =>
      rcases eq_or_ne n 0 with rfl | hn
      · unfold f
        rw [grahamSeq, grahamSeq]
        simp
      rw [add_comm, Function.iterate_add_apply, ih hn, Function.iterate_one]
      unfold f
      rw [add_comm, grahamSeq]
  have ts_eq (n : ℕ) : conwayChain [3, 3, n + 1, 2] = f^[n] 27 := by
    simp only [conwayChain, ne_eq, decide_not, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, OfNat.ofNat_ne_zero, decide_false, Bool.not_false, List.filter_cons_of_pos,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, List.filter_nil]
    induction n with
    | zero =>
      unfold f
      simp only [zero_add, Function.iterate_zero, id_eq]
      rw [reverseConwayChain, reverseConwayChain] <;> grind
    | succ n ih =>
      rw [reverseConwayChain, reverseConwayChain, ih] <;> try grind
      rw [add_comm, Function.iterate_add_apply, Function.iterate_one]
      trans knuthArrow 3 3 (f^[n] 27)
      swap
      · rfl
      have : f^[n] 27 ≠ 0 := by
        rcases eq_or_ne n 0 with rfl | hn
        · unfold f
          simp
        have f_mono' : StrictMono fun n ↦ f^[n] 27 := by
          refine StrictMono.strictMono_iterate_of_lt_map ?_ ?_
          · intro n m nm
            unfold f
            exact knuthArrow_strict_mono_third le_rfl (by norm_num) nm
          · unfold f
            apply lt_of_le_of_lt (b := knuthArrow 3 3 1)
            · simp
            apply knuthArrow_strict_mono <;> grind
        symm
        apply ne_of_lt
        apply lt_of_le_of_lt (b := f^[0] 27)
        · simp
        apply f_mono' (by grind)
      rw [knuthArrow_conwayChain] <;> try grind
      simp [conwayChain, this]
  rw [contender_8, ← ite_one (by norm_num), contender_9, ts_eq]
  exact f_mono (by norm_num)
