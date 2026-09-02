/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
import Contenders.Contender6
import Mathlib.Computability.Ackermann
import Mathlib.Data.Nat.Hyperoperation

def grahamSeq : ℕ → ℕ
  | 0 => 4
  | n + 1 => knuthArrow 3 3 (grahamSeq n)

/-- Submitted by Felix Pernegger. -/
def contender_7 : Nat := grahamSeq 1

theorem contender_6_lt_contender_7 : contender_6 < contender_7 := by
  unfold contender_6 contender_7
  rw [ack_eq_knuthArrow, grahamSeq, grahamSeq]
  dsimp only [Nat.reduceAdd]
  apply lt_of_lt_of_le (b := knuthArrow 2 5 2)
  · simp only [tsub_lt_self_iff, Nat.ofNat_pos, and_true]
    apply lt_of_lt_of_le (b := knuthArrow 2 1 1)
    · simp
    · apply knuthArrow_mono <;> norm_num
  nth_rw 2 [knuthArrow]
  apply knuthArrow_mono
  · norm_num
  · norm_num
  · dsimp only [Nat.reduceAdd]
    trans knuthArrow 3 2 2
    · rw [knuthArrow, knuthArrow_third_one]
      simp only [Nat.reduceAdd]
      trans 3 ^ 2
      · norm_num
      gcongr
      · norm_num
      rw [knuthArrow, knuthArrow_third_one]
      · simp
    apply knuthArrow_mono <;> norm_num
  · norm_num
