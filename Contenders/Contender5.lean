/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
import Contenders.Contender4
import Mathlib.Data.Nat.Log

/-- The number `1234...n` (in decimal)-/
def concatenateNum : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    (10 ^ Nat.clog 10 (n + 2)) * concatenateNum n + n + 1

@[simp]
theorem concatenateNum_zero : concatenateNum 0 = 0 :=
  rfl

@[simp]
theorem concatenateNum_succ (n : ℕ) :
    concatenateNum (n + 1) = (10 ^ Nat.clog 10 (n + 2)) * concatenateNum n + n + 1 :=
  rfl

example : concatenateNum 11 = 1234567891011 :=
  rfl

theorem monotone_concatenateNum : StrictMono concatenateNum := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  rw [concatenateNum_succ]
  apply lt_of_le_of_lt (b := (10 ^ Nat.clog 10 (n + 2) * concatenateNum n))
  · nth_rw 1 [← Nat.one_mul (concatenateNum n)]
    gcongr
    grind
  · lia

/-- Submitted by Felix Pernegger. -/
def contender_5 : Nat := concatenateNum 10

theorem contender_4_lt_contender_5 : contender_4 < contender_5 := by
  trans (concatenateNum 3)
  · decide
  · unfold contender_5
    exact monotone_concatenateNum (by norm_num)
