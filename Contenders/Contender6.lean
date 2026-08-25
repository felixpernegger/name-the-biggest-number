/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
import Contenders.Contender5
import Mathlib.Computability.Ackermann
import Mathlib.Data.Nat.Hyperoperation

def knuthArrow : ℕ → ℕ → ℕ → ℕ
  | a, b, 0 => a * b
  | _, 0, _ => 1
  | a, b + 1, n + 1 => knuthArrow a (knuthArrow a b (n + 1)) n

variable (a b n : ℕ)

@[simp]
theorem knuthArrow_third_zero : knuthArrow a b 0 = a * b := by
  rw [knuthArrow]

@[simp]
theorem knuthArrow_zero_succ : knuthArrow a 0 (n + 1) = 1 := by
  simp [knuthArrow]

theorem knuthArrow_succ_succ :
    knuthArrow a (b + 1) (n + 1) = knuthArrow a (knuthArrow a b (n + 1)) n := by
  nth_rw 1 [knuthArrow]

@[simp]
theorem knuthArrow_third_one : knuthArrow a b 1 = a ^ b := by
  induction b with
  | zero =>
    simp [knuthArrow_zero_succ]
  | succ b ih =>
    rw [knuthArrow_succ_succ, knuthArrow_third_zero, ih]
    grind

theorem one_le_knuthArrow_succ {a : ℕ} (ha : 1 ≤ a) (b n : ℕ) :
    1 ≤ knuthArrow a b (n + 1) := by
  induction n generalizing b with
  | zero => simpa using (one_le_pow₀ ha : 1 ≤ a ^ b)
  | succ n ih =>
    cases b with
    | zero => simp
    | succ b =>
      rw [knuthArrow_succ_succ]
      exact ih _

theorem knuthArrow_mono_first_second (n : ℕ) {a₁ a₂ b₁ b₂ : ℕ} (ha : 1 ≤ a₁)
    (haa : a₁ ≤ a₂) (hbb : b₁ ≤ b₂) :
    knuthArrow a₁ b₁ n ≤ knuthArrow a₂ b₂ n := by
  induction n generalizing a₁ a₂ b₁ b₂ with
  | zero =>
    simp only [knuthArrow_third_zero]
    exact Nat.mul_le_mul haa hbb
  | succ n ih =>
    induction b₂ generalizing b₁ with
    | zero =>
      have : b₁ = 0 := Nat.eq_zero_of_le_zero hbb
      subst b₁
      simp
    | succ b₂ hb =>
      cases b₁ with
      | zero =>
        rw [knuthArrow_zero_succ]
        exact one_le_knuthArrow_succ (ha.trans haa) _ _
      | succ b₁ =>
        rw [knuthArrow_succ_succ, knuthArrow_succ_succ]
        apply ih ha haa
        exact hb (Nat.le_of_succ_le_succ hbb)

theorem knuthArrow_mono_first (b n : ℕ) {a₁ a₂ : ℕ} (ha : 1 ≤ a₁)
    (haa : a₁ ≤ a₂) :
    knuthArrow a₁ b n ≤ knuthArrow a₂ b n :=
  knuthArrow_mono_first_second n ha haa le_rfl

theorem knuthArrow_mono_second (a n : ℕ) {b₁ b₂ : ℕ} (ha : 1 ≤ a) (hbb : b₁ ≤ b₂) :
    knuthArrow a b₁ n ≤ knuthArrow a b₂ n :=
  knuthArrow_mono_first_second n ha le_rfl hbb

theorem knuthArrow_le_succ_third (a b n : ℕ) (ha : 2 ≤ a) :
    knuthArrow a b n ≤ knuthArrow a b (n + 1) := by
  induction n generalizing b with
  | zero =>
    rw [knuthArrow_third_zero, knuthArrow_third_one]
    exact Nat.mul_le_pow (by omega) b
  | succ n ih =>
    induction b with
    | zero => simp
    | succ b hb =>
      rw [knuthArrow_succ_succ, knuthArrow_succ_succ]
      exact (knuthArrow_mono_first_second n (by omega) le_rfl hb).trans (ih _)

theorem knuthArrow_mono_third {a b n₁ n₂ : ℕ} (ha : 2 ≤ a) (hnn : n₁ ≤ n₂) :
    knuthArrow a b n₁ ≤ knuthArrow a b n₂ :=
  (monotone_nat_of_le_succ fun n ↦ knuthArrow_le_succ_third a b n ha) hnn

theorem knuthArrow_mono {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (ha : 2 ≤ a₁)
    (haa : a₁ ≤ a₂) (hbb : b₁ ≤ b₂) (hnn : n₁ ≤ n₂) :
    knuthArrow a₁ b₁ n₁ ≤ knuthArrow a₂ b₂ n₂ :=
  (knuthArrow_mono_first_second n₁ (by omega) haa hbb).trans
    (knuthArrow_mono_third (ha.trans haa) hnn)

@[simp]
theorem knuthArrow_two_one (n : ℕ) : knuthArrow 2 1 n = 2 := by
  induction n with
  | zero => simp
  | succ n ih => simp [knuthArrow, ih]

@[simp]
theorem knuthArrow_two_two (n : ℕ) : knuthArrow 2 2 n = 4 := by
  induction n with
  | zero => simp
  | succ n ih => simp [knuthArrow, ih]

theorem hyperoperation_eq_knuthArrow (a b n : ℕ) : hyperoperation (n + 2) a b = knuthArrow a b n := by
  induction n generalizing a b with
  | zero => rw [knuthArrow_third_zero, hyperoperation_two]
  | succ n ih =>
    induction b with
    | zero => rw [knuthArrow_zero_succ, hyperoperation_ge_three_eq_one]
    | succ b hb => rw [hyperoperation_recursion, knuthArrow_succ_succ, ih, hb]

theorem ack_eq_knuthArrow (m n : ℕ) : ack (m + 2) n = knuthArrow 2 (n + 3) m - 3 := by
  induction m generalizing n with
  | zero =>
    simp only [zero_add, ack_two, knuthArrow_third_zero]
    grind
  | succ m ih =>
    induction n generalizing m with
    | zero => simp [knuthArrow, ← ih]
    | succ n hn =>
      rw [ack_succ_succ, ih, knuthArrow_succ_succ]
      congr
      rw [hn]
      · apply Nat.sub_add_cancel
        clear ih hn
        trans knuthArrow 2 2 0
        · simp
        · apply knuthArrow_mono <;> grind
      · exact ih

/-- Submitted by Felix Pernegger. -/
def contender_6 : Nat := ack 4 2

theorem contender_5_lt_contender_6 : contender_5 < contender_6 := by
  rw [contender_6]
  unfold contender_5
  have : concatenateNum 10 = 12345678910 := rfl
  rw [this, ack_eq_knuthArrow, knuthArrow_succ_succ]
  simp only [Nat.reduceAdd, gt_iff_lt]
  simp only [knuthArrow_third_one]
  suffices : 35 < knuthArrow 2 4 2
  · trans 2 ^ 35 - 3
    · norm_num
    · gcongr <;> norm_num
  rw [knuthArrow_succ_succ]
  simp only [Nat.reduceAdd, knuthArrow_third_one]
  suffices : 6 < knuthArrow 2 3 2
  · trans 2 ^ 6
    · norm_num
    · gcongr
      norm_num
  · rw [knuthArrow_succ_succ]
    simp
