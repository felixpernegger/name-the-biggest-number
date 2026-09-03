/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
import Contenders.Contender9

theorem reverseConwayChain_one (l : List ℕ) :
    reverseConwayChain (1 :: l) = reverseConwayChain l := by
  cases l using reverseConwayChain.induct <;> simp_all [reverseConwayChain]

def StrongGrowth (f : ℕ → ℕ) : Prop :=
  StrictMonoOn f (Set.Ici 1) ∧ ∀ n, 1 ≤ n → n + 1 < f n

def conwayHierarchy (f : ℕ → ℕ) (base : ℕ) : ℕ → ℕ → ℕ
  | 0, n => f n
  | _ + 1, 0 => base
  | k + 1, n + 1 => (conwayHierarchy f base k)^[n] base

theorem strongGrowth_of_strictMonoOn {f : ℕ → ℕ}
    (hmono : StrictMonoOn f (Set.Ici 1)) (hbase : 3 ≤ f 1) :
    StrongGrowth f := by
  refine ⟨hmono, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => omega
  | succ n hn ih =>
    have hstep : f n < f (n + 1) :=
      hmono (by simpa only [Set.mem_Ici] using hn)
        (by simpa only [Set.mem_Ici] using (show 1 ≤ n + 1 by omega)) (by omega)
    omega

theorem conwayHierarchy_strongGrowth {f : ℕ → ℕ} {base : ℕ}
    (hf : StrongGrowth f) (hbase : 3 ≤ base) :
    ∀ k, StrongGrowth (conwayHierarchy f base k) := by
  intro k
  induction k with
  | zero => exact hf
  | succ k ih =>
    let g := conwayHierarchy f base k
    have hg : StrongGrowth g := ih
    have hiter_pos (n : ℕ) : 1 ≤ g^[n] base := by
      induction n with
      | zero =>
        simp only [Function.iterate_zero_apply]
        omega
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        have := hg.2 _ ih
        omega
    have hiter_lt (n : ℕ) : g^[n] base < g^[n + 1] base := by
      rw [Function.iterate_succ_apply']
      exact (hg.2 _ (hiter_pos n)).trans' (Nat.lt_succ_self _)
    have hiter_strict : StrictMono fun n ↦ g^[n] base :=
      strictMono_nat_of_lt_succ hiter_lt
    have hbound (n : ℕ) : n + 2 < g^[n] base := by
      induction n with
      | zero =>
        simp only [Function.iterate_zero_apply]
        omega
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        have := hg.2 _ (hiter_pos n)
        omega
    constructor
    · intro x hx y hy hxy
      have hx' : 1 ≤ x := by simpa only [Set.mem_Ici] using hx
      have hy' : 1 ≤ y := by simpa only [Set.mem_Ici] using hy
      obtain ⟨x, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hx'))
      obtain ⟨y, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hy'))
      simp only [conwayHierarchy]
      apply hiter_strict
      omega
    · intro n hn
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hn))
      simp only [conwayHierarchy]
      exact hbound n

theorem conwayHierarchy_lt_succ {f : ℕ → ℕ} {base : ℕ}
    (hf : StrongGrowth f) (hbase : 3 ≤ base) (k : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    conwayHierarchy f base k p < conwayHierarchy f base (k + 1) p := by
  let g := conwayHierarchy f base k
  have hg : StrongGrowth g := conwayHierarchy_strongGrowth hf hbase k
  induction p, hp using Nat.le_induction with
  | base =>
    change g 2 < g base
    exact hg.1 (by simp)
      (by simpa only [Set.mem_Ici] using (show 1 ≤ base by omega)) (by omega)
  | succ p hp ih =>
    have hp1 : 1 ≤ p := by omega
    have hnextp : g p < conwayHierarchy f base (k + 1) p := ih
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hp1))
    have harg : q + 1 + 1 ≤ g (q + 1) := by
      have := hg.2 (q + 1) (by omega)
      omega
    have hgp : 1 ≤ g (q + 1) := by omega
    simp only [Nat.succ_eq_add_one] at hnextp
    change g (q + 1 + 1) < g^[q + 1] base
    rw [Function.iterate_succ_apply']
    change g (q + 1 + 1) < g (conwayHierarchy f base (k + 1) (q + 1))
    apply lt_of_le_of_lt (b := g (g (q + 1)))
    · exact hg.1.monotoneOn (by simp)
        (by simpa only [Set.mem_Ici] using hgp) harg
    · exact hg.1 (by simpa only [Set.mem_Ici] using hgp)
        (by simpa only [Set.mem_Ici] using hgp.trans hnextp.le) hnextp

theorem conwayHierarchy_strictMono_level {f : ℕ → ℕ} {base p : ℕ}
    (hf : StrongGrowth f) (hbase : 3 ≤ base) (hp : 2 ≤ p) :
    StrictMono fun k ↦ conwayHierarchy f base k p :=
  strictMono_nat_of_lt_succ fun k ↦ conwayHierarchy_lt_succ hf hbase k hp

theorem reverseConwayChain_second_one (a : ℕ) (l : List ℕ) (hl : 2 ≤ l.length) :
    reverseConwayChain (a :: 1 :: l) = reverseConwayChain l := by
  cases a with
  | zero =>
    rw [reverseConwayChain_zero (1 :: l) (by simp; omega), reverseConwayChain_one]
  | succ a =>
    cases a with
    | zero => rw [reverseConwayChain_one, reverseConwayChain_one]
    | succ a => rw [reverseConwayChain] <;> grind

theorem reverseConwayChain_rec (q p : ℕ) (l : List ℕ) (hq : 1 ≤ q) (hp : 1 ≤ p)
    (hl : 2 ≤ l.length) :
    reverseConwayChain ((q + 1) :: (p + 1) :: l) =
      reverseConwayChain (q :: reverseConwayChain ((q + 1) :: p :: l) :: l) := by
  rw [reverseConwayChain] <;> grind

theorem reverseConwayChain_eq_hierarchy (t : List ℕ) (ht : 2 ≤ t.length)
    (hf : StrongGrowth fun n ↦ reverseConwayChain (n :: t))
    (hbase : 3 ≤ reverseConwayChain t) {q p : ℕ} (hq : 1 ≤ q) (hp : 1 ≤ p) :
    reverseConwayChain (q :: p :: t) =
      conwayHierarchy (fun n ↦ reverseConwayChain (n :: t)) (reverseConwayChain t)
        (q - 1) p := by
  induction q, hq using Nat.le_induction generalizing p with
  | base =>
    simp only [Nat.one_sub]
    exact reverseConwayChain_one (p :: t)
  | succ q hq ihq =>
    induction p, hp using Nat.le_induction with
    | base =>
      rw [reverseConwayChain_second_one (q + 1) t ht]
      have hq' : q = (q - 1) + 1 := by omega
      rw [show q + 1 - 1 = q by omega, hq', conwayHierarchy]
      simp
    | succ p hp ihp =>
      rw [show q + 1 - 1 = q by omega] at ihp ⊢
      rw [reverseConwayChain_rec q p t hq hp ht, ihp]
      have hg := conwayHierarchy_strongGrowth hf hbase q
      have hinner : 1 ≤
          conwayHierarchy (fun n ↦ reverseConwayChain (n :: t)) (reverseConwayChain t)
            q p := by
        have := hg.2 p hp
        omega
      rw [ihq hinner]
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hq))
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hp))
      simp only [conwayHierarchy, Function.iterate_succ_apply', Nat.succ_sub_one]

theorem reverseConwayChain_strongGrowth (l : List ℕ) (hl : ∀ i ∈ l, 2 ≤ i)
    (hbase : 3 ≤ l.getLastD 0) :
    StrongGrowth fun n ↦ reverseConwayChain (n :: l) := by
  induction l with
  | nil => simp_all
  | cons a t ih =>
    have ha : 2 ≤ a := hl a (by simp)
    cases t with
    | nil =>
      apply strongGrowth_of_strictMonoOn
      · intro x hx y hy hxy
        simp only [reverseConwayChain]
        exact pow_lt_pow_right₀ (a := a) (by omega) hxy
      · have : 3 ≤ a := by
          simpa [List.getLastD] using hbase
        simpa [reverseConwayChain] using this
    | cons b t =>
      have hb : 2 ≤ b := hl b (by simp)
      cases t with
      | nil =>
        apply strongGrowth_of_strictMonoOn
        · intro x hx y hy hxy
          simp only [reverseConwayChain]
          exact knuthArrow_strict_mono_third (by
            change 3 ≤ b at hbase
            exact hbase) ha hxy
        · simp only [reverseConwayChain, knuthArrow_third_one]
          have hb3 : 3 ≤ b := by
            change 3 ≤ b at hbase
            exact hbase
          exact hb3.trans (Nat.le_self_pow (by omega) b)
      | cons c t =>
        let tail := b :: c :: t
        have htail : ∀ i ∈ tail, 2 ≤ i := by
          intro i hi
          apply hl i
          simp_all [tail]
        have htailBase : 3 ≤ tail.getLastD 0 := by
          simpa [tail] using hbase
        have htailStrong : StrongGrowth fun n ↦ reverseConwayChain (n :: tail) :=
          ih htail htailBase
        have htailValue : 3 ≤ reverseConwayChain tail := by
          have h := htailStrong.2 1 (by omega)
          change 2 < reverseConwayChain (1 :: tail) at h
          rw [reverseConwayChain_one] at h
          omega
        have heq (q : ℕ) (hq : 1 ≤ q) :
            reverseConwayChain (q :: a :: tail) =
              conwayHierarchy (fun n ↦ reverseConwayChain (n :: tail))
                (reverseConwayChain tail) (q - 1) a :=
          reverseConwayChain_eq_hierarchy tail (by simp [tail]) htailStrong htailValue hq
            (by omega)
        apply strongGrowth_of_strictMonoOn
        · intro x hx y hy hxy
          have hx' : 1 ≤ x := by simpa only [Set.mem_Ici] using hx
          have hy' : 1 ≤ y := by simpa only [Set.mem_Ici] using hy
          change reverseConwayChain (x :: a :: tail) <
            reverseConwayChain (y :: a :: tail)
          rw [heq x hx', heq y hy']
          apply conwayHierarchy_strictMono_level htailStrong htailValue ha
          omega
        · change 3 ≤ reverseConwayChain (1 :: a :: tail)
          rw [reverseConwayChain_one]
          have h := htailStrong.2 a (by omega)
          change a + 1 < reverseConwayChain (a :: tail) at h
          omega

theorem reverseConwayChain_lt_cons (l : List ℕ) {a : ℕ}
    (hl : ∀ i ∈ l, 3 ≤ i) (ha : 1 < a) :
    reverseConwayChain l < reverseConwayChain (a :: l) := by
  cases l with
  | nil => simpa [reverseConwayChain] using ha
  | cons b l =>
    have hgrowth := reverseConwayChain_strongGrowth (b :: l) (by
      intro i hi
      exact (hl i hi).trans' (by omega)) (by
      apply hl
      rw [List.getLastD_cons]
      exact List.getLastD_mem_cons)
    rw [← reverseConwayChain_one (b :: l)]
    exact hgrowth.1 (by simp) (by simpa only [Set.mem_Ici] using ha.le) ha

theorem conwayChain_append_lt (l r : List ℕ) (hl : ∀ i ∈ l, 3 ≤ i)
    (hrne : r ≠ []) (hr : ∀ i ∈ r, 3 ≤ i) :
    conwayChain l < conwayChain (l.append r) := by
  have hlfilter : l.reverse.filter (· ≠ 0) = l.reverse := by
    apply List.filter_eq_self.mpr
    intro i hi
    simp only [decide_eq_true_eq]
    exact ne_of_gt (Nat.zero_lt_one.trans_le ((hl i (by simpa using hi)).trans' (by omega)))
  have hrfilter : r.reverse.filter (· ≠ 0) = r.reverse := by
    apply List.filter_eq_self.mpr
    intro i hi
    simp only [decide_eq_true_eq]
    exact ne_of_gt (Nat.zero_lt_one.trans_le ((hr i (by simpa using hi)).trans' (by omega)))
  simp only [conwayChain, List.append_eq, List.reverse_append, List.filter_append, hlfilter,
    hrfilter]
  let s := l.reverse
  have grow (t : List ℕ) (ht : t ≠ []) (hall : ∀ i ∈ t, 3 ≤ i) :
      reverseConwayChain s < reverseConwayChain (t ++ s) := by
    induction t with
    | nil => contradiction
    | cons a t ih =>
      cases t with
      | nil =>
        simpa using (reverseConwayChain_lt_cons s (by
          intro i hi
          apply hl i
          simpa [s] using hi) (by
          have := hall a (by simp)
          omega))
      | cons b t =>
        have htail : reverseConwayChain s < reverseConwayChain ((b :: t) ++ s) := by
          apply ih
          · simp
          · intro i hi
            apply hall i
            simp_all
        exact htail.trans (by
          simpa using (reverseConwayChain_lt_cons ((b :: t) ++ s) (by
            intro i hi
            rcases List.mem_append.mp hi with hi | hi
            · apply hall i
              simp_all
            · apply hl i
              simpa [s] using hi) (by
            have := hall a (by simp)
            omega)))
  apply grow r.reverse
  · simpa using hrne
  · intro i hi
    apply hr i
    simpa using hi


/-- Submitted by Felix Pernegger. -/
def contender_10 : Nat := conwayChain (List.replicate 100 100)

theorem contender_9_lt_contender_10 : contender_9 < contender_10 := by
  let f (n : ℕ) := knuthArrow 3 3 n
  let g (n : ℕ) := knuthArrow 100 100 n
  let base := 100 ^ 100
  have hfChain : StrongGrowth fun n ↦ reverseConwayChain [n, 3, 3] :=
    reverseConwayChain_strongGrowth [3, 3] (by simp) (by simp)
  have hgChain : StrongGrowth fun n ↦ reverseConwayChain [n, 100, 100] :=
    reverseConwayChain_strongGrowth [100, 100] (by simp) (by simp)
  have hf_eq : (fun n ↦ reverseConwayChain [n, 3, 3]) = f := by
    funext n
    rw [reverseConwayChain]
  have hg_eq : (fun n ↦ reverseConwayChain [n, 100, 100]) = g := by
    funext n
    rw [reverseConwayChain]
  have hfStrong : StrongGrowth f := by
    rw [← hf_eq]
    exact hfChain
  have hgStrong : StrongGrowth g := by
    rw [← hg_eq]
    exact hgChain
  have hthree : reverseConwayChain [3, 3] = 27 := by
    rw [reverseConwayChain]
    norm_num
  have hundred : reverseConwayChain [100, 100] = base := by
    rw [reverseConwayChain]
  have hbase : 3 ≤ base := by
    dsimp [base]
    exact le_trans (by norm_num : 3 ≤ 100) (Nat.le_self_pow (n := 100) (by norm_num) 100)
  have hfg (n : ℕ) : f n ≤ g n := by
    exact (knuthArrow_strict_mono (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) le_rfl (Or.inl (by norm_num))).le
  have hgmono : StrictMono g := by
    intro m n hmn
    exact knuthArrow_strict_mono_third (by norm_num) (by norm_num) hmn
  have hiter (n : ℕ) {x y : ℕ} (hxy : x ≤ y) : f^[n] x ≤ g^[n] y := by
    induction n with
    | zero => simpa
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (hfg _).trans (hgmono.monotone ih)
  have hc9 : contender_9 = f^[64] 27 := by
    change reverseConwayChain [2, 65, 3, 3] = _
    rw [reverseConwayChain_eq_hierarchy [3, 3] (by simp)
      hfChain (by rw [hthree]; norm_num) (q := 2) (p := 65) (by norm_num) (by norm_num)]
    rw [show 65 = 64 + 1 by omega, conwayHierarchy, hf_eq, hthree]
    change f^[64] 27 = f^[64] 27
    rfl
  have hbase_lt : 27 < base := by
    dsimp [base]
    exact lt_of_lt_of_le (by norm_num : 27 < 100)
      (Nat.le_self_pow (n := 100) (by norm_num) 100)
  have hg_iter_strict : StrictMono fun n ↦ g^[n] base := by
    apply StrictMono.strictMono_iterate_of_lt_map hgmono
    have := hgStrong.2 base (by omega)
    omega
  have hsmall : f^[64] 27 < g^[99] base :=
    (hiter 64 hbase_lt.le).trans_lt (hg_iter_strict (by norm_num))
  have hlevel : g^[99] base < conwayHierarchy g base 99 100 := by
    calc
      g^[99] base = conwayHierarchy g base 1 100 := by
        rw [show 100 = 99 + 1 by omega, conwayHierarchy]
        rfl
      _ < conwayHierarchy g base 99 100 :=
        conwayHierarchy_strictMono_level (p := 100) hgStrong hbase (by norm_num)
          (by norm_num)
  have hfour : conwayHierarchy g base 99 100 = conwayChain (List.replicate 4 100) := by
    change _ = reverseConwayChain [100, 100, 100, 100]
    rw [reverseConwayChain_eq_hierarchy [100, 100] (by simp)
      hgChain (by rw [hundred]; exact hbase) (q := 100) (p := 100) (by norm_num)
      (by norm_num)]
    rw [hg_eq, hundred]
  have happ := conwayChain_append_lt (List.replicate 4 100) (List.replicate 96 100)
    (by simp) (by simp) (by simp)
  have hrepl : List.replicate 4 100 ++ List.replicate 96 100 = List.replicate 100 100 := by
    rw [← List.replicate_add]
  change conwayChain (List.replicate 4 100) <
    conwayChain (List.replicate 4 100 ++ List.replicate 96 100) at happ
  rw [hrepl] at happ
  rw [hc9, contender_10]
  exact hsmall.trans (hlevel.trans (hfour.trans_lt happ))
