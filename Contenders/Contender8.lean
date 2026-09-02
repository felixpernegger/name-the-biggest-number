/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
import Contenders.Contender7

@[simp]
theorem knuthArrow_one (a n : ℕ) : knuthArrow a 1 n = a := by
  induction n with
  | zero => simp
  | succ n ih => simp [knuthArrow, ih]

theorem knuthArrow_lt_first (b n : ℕ) {a₁ a₂ : ℕ} (ha : 1 ≤ a₁) (hb : 0 < b)
    (haa : a₁ < a₂) : knuthArrow a₁ b n < knuthArrow a₂ b n := by
  induction n generalizing a₁ a₂ b with
  | zero =>
    simp only [knuthArrow_third_zero]
    exact Nat.mul_lt_mul_of_pos_right haa hb
  | succ n ih =>
    cases b with
    | zero => grind
    | succ b =>
      rw [knuthArrow_succ_succ, knuthArrow_succ_succ]
      apply lt_of_lt_of_le (b := knuthArrow a₂ (knuthArrow a₁ b (n + 1)) n)
      · exact ih _ ha (one_le_knuthArrow_succ ha _ _) haa
      · exact knuthArrow_mono_second a₂ n (by grind)
          (knuthArrow_mono_first b (n + 1) ha haa.le)

theorem knuthArrow_lt_second (a n : ℕ) {b₁ b₂ : ℕ} (ha : 2 ≤ a) (hbb : b₁ < b₂) :
    knuthArrow a b₁ n < knuthArrow a b₂ n := by
  induction n generalizing b₁ b₂ with
  | zero =>
    simp only [knuthArrow_third_zero]
    exact Nat.mul_lt_mul_of_pos_left hbb (by grind)
  | succ n ih =>
    induction b₂ generalizing b₁ with
    | zero => grind
    | succ b₂ hb =>
      cases b₁ with
      | zero =>
        rw [knuthArrow_zero_succ]
        exact lt_of_lt_of_le (by grind : 1 < a) (by
          simpa only [knuthArrow_one] using
            (knuthArrow_mono_second a (n + 1) (by grind) (by grind : 1 ≤ b₂ + 1)))
      | succ b₁ =>
        rw [knuthArrow_succ_succ, knuthArrow_succ_succ]
        exact ih (hb (Nat.lt_of_succ_lt_succ hbb))

theorem mul_lt_pow_of_three_le {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b) : a * b < a ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    cases b with
    | zero => grind
    | succ b =>
      cases b with
      | zero =>
        simp only [pow_succ]
        nlinarith
      | succ b =>
        rw [pow_succ]
        have hpow : a ≤ a ^ (b + 2) := Nat.le_self_pow (by grind) a
        nlinarith [ih (by grind)]

theorem knuthArrow_lt_succ_third (a b n : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) :
    knuthArrow a b n < knuthArrow a b (n + 1) := by
  induction n generalizing b with
  | zero =>
    rw [knuthArrow_third_zero, knuthArrow_third_one]
    exact mul_lt_pow_of_three_le ha hb
  | succ n ih =>
    induction b with
    | zero => grind
    | succ b hb' =>
      cases b with
      | zero => grind
      | succ b =>
        rw [knuthArrow_succ_succ]
        nth_rw 2 [knuthArrow_succ_succ]
        cases b with
        | zero =>
          simp only [zero_add, knuthArrow_one]
          exact ih a (by grind)
        | succ b =>
          exact (knuthArrow_lt_second a n (by grind) (hb' (by grind))).trans_le
            (knuthArrow_le_succ_third a _ n (by grind))

theorem knuthArrow_strict_mono_third {a b n₁ n₂ : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b)
    (hnn : n₁ < n₂) : knuthArrow a b n₁ < knuthArrow a b n₂ :=
  (strictMono_nat_of_lt_succ fun n ↦ knuthArrow_lt_succ_third a b n ha hb) hnn

theorem knuthArrow_strict_mono {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (ha : 3 ≤ a₁)
    (hb : 2 ≤ b₁) (haa : a₁ ≤ a₂) (hbb : b₁ ≤ b₂) (hnn : n₁ ≤ n₂)
    (hstrict : a₁ < a₂ ∨ b₁ < b₂ ∨ n₁ < n₂) :
    knuthArrow a₁ b₁ n₁ < knuthArrow a₂ b₂ n₂ := by
  rcases hstrict with haa' | hbb' | hnn'
  · exact (knuthArrow_lt_first b₁ n₁ (by grind) (by grind) haa').trans_le
      ((knuthArrow_mono_second a₂ n₁ (by grind) hbb).trans
        (knuthArrow_mono_third (by grind) hnn))
  · exact (knuthArrow_mono_first b₁ n₁ (by grind) haa).trans_lt
      ((knuthArrow_lt_second a₂ n₁ (by grind) hbb').trans_le
        (knuthArrow_mono_third (by grind) hnn))
  · exact (knuthArrow_mono_first_second n₁ (by grind) haa hbb).trans_lt
      (knuthArrow_strict_mono_third (by grind) (by grind) hnn')

theorem strictMono_grahamSeq : StrictMono grahamSeq := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  induction n
  · rw [grahamSeq, grahamSeq, grahamSeq]
    apply lt_of_lt_of_le (b := knuthArrow 3 3 1)
    · simp
    apply knuthArrow_mono <;> norm_num
  rename_i n hn
  rw [grahamSeq, grahamSeq]
  exact knuthArrow_strict_mono (by grind) (by grind) le_rfl le_rfl hn.le (Or.inr (Or.inr hn))

/-- Submitted by Felix Pernegger.
This is Graham's number. -/
def contender_8 : Nat := grahamSeq 64

theorem contender_7_lt_contender_8 : contender_7 < contender_8 := by
  unfold contender_7 contender_8
  exact strictMono_grahamSeq (by norm_num)
