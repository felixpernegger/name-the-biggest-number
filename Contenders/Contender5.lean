/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
import Contenders.Contender4
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Iterate


/-- Graham's arrow function a ↑ⁿ b -/
def arrowFunction (a : ℕ) : ℕ → ℕ → ℕ
  | b, 0 => a * b
  | 0, _ => a
  | b + 1, n + 1 => arrowFunction a (arrowFunction a b (n + 1)) n

theorem arrowFunction_succ_succ (a b n : ℕ) :
    arrowFunction a (b + 1) (n + 1) = arrowFunction a (arrowFunction a b (n + 1)) n := by
  rw [arrowFunction]

@[simp]
theorem arrowFunction_third_zero (a b : ℕ) : arrowFunction a b 0 = a * b := by
  rw [arrowFunction]

@[simp]
theorem arrowFunction_zero_succ (a n : ℕ) : arrowFunction a 0 (n + 1) = a := by
  rw [arrowFunction]
  simp

@[simp]
theorem arrowFunction_third_one (a b : ℕ) : arrowFunction a b 1 = a ^ (b + 1) := by
  induction b with
  | zero =>
    simp
  | succ b ih =>
    rw [arrowFunction_succ_succ, ih]
    simp only [arrowFunction_third_zero]
    grind

theorem arrowFunction_succ_eq_iterate (a b n : ℕ) :
    arrowFunction a b (n + 1) = (arrowFunction a · n)^[b] a := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [arrowFunction_succ_succ, ih, Function.iterate_succ_apply']

private theorem le_arrowFunction_one (a b : ℕ) (ha : 2 ≤ a) : b + 1 ≤ arrowFunction a b 1 := by
  induction b with
  | zero => simpa using (show 1 ≤ a by omega)
  | succ b ih =>
    rw [arrowFunction_succ_succ, arrowFunction_third_zero]
    exact (show b + 2 ≤ 2 * (b + 1) by omega).trans (Nat.mul_le_mul ha ih)

private theorem arrowFunction_mono_second_and_le_succ_third (a : ℕ) (ha : 2 ≤ a) (n : ℕ) :
    Monotone (arrowFunction a · n) ∧
      (∀ b, arrowFunction a b n ≤ arrowFunction a b (n + 1)) ∧
      a ≤ arrowFunction a a n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro b c hbc
      simpa using Nat.mul_le_mul_left a hbc
    · intro b
      cases b with
      | zero => simp
      | succ b =>
        rw [arrowFunction_third_zero, arrowFunction_succ_succ, arrowFunction_third_zero]
        exact Nat.mul_le_mul_left a (le_arrowFunction_one a b ha)
    · rw [arrowFunction_third_zero]
      simpa only [Nat.mul_one] using
        (Nat.mul_le_mul_left a (show 1 ≤ a by omega) : a * 1 ≤ a * a)
  | succ n ih =>
    rcases ih with ⟨hmono, hle, ha_self⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [arrowFunction_succ_eq_iterate] using
        hmono.monotone_iterate_of_le_map ha_self
    · intro b
      rw [arrowFunction_succ_eq_iterate, arrowFunction_succ_eq_iterate]
      exact hmono.iterate_le_of_le hle b a
    · exact ha_self.trans (hle a)

theorem arrow_function_mono_third (a b : ℕ) (ha : 2 ≤ a) : Monotone (arrowFunction a b ·) :=
  monotone_nat_of_le_succ fun n ↦ (arrowFunction_mono_second_and_le_succ_third a ha n).2.1 b

/-- F(n) := 3 ↑ⁿ 3 -/
def F (n : ℕ) : ℕ := arrowFunction 3 3 n

/-- Gₙ := Fⁿ(4). Graham's muber would be G₆₄.
We submit G₁ which is still very big but and too large to write down,
but doesn't kill the competition -/
def G (n : ℕ) : ℕ := Nat.iterate F n 4

/-- Submitted by Felix Pernegger. -/
def contender_5 : Nat := G 1

theorem contender_4_lt_contender_5 : contender_4 < contender_5 := by
  unfold contender_4 contender_5 G F
  simp only [Function.iterate_one]
  apply lt_of_lt_of_le (b := arrowFunction 3 3 2)
  · rw [arrowFunction]
    simp only [Nat.reduceAdd, arrowFunction_third_one]
    apply lt_of_le_of_lt (b := 3 ^ (3 + 1))
    · simp
    · gcongr
      simp only [Nat.one_lt_ofNat]
      rw [arrowFunction_succ_succ, arrowFunction_succ_succ]
      simp

  exact arrow_function_mono_third 3 3 (by norm_num) (show 2 ≤ 4 by norm_num)
