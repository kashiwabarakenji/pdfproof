import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
--import Mathlib.Analysis.SpecialFunctions.Ineq
import LeanCopilot

------------
----練習1---
------------

-- 距離関数 d : α → α → ℝ が定義された集合 α を仮定します
variable {α : Type} (d : α → α → ℝ)

-- 公理を定義します
axiom axiom1 : ∀ x y : α, d x y = (0 : ℝ) ↔ x = y
axiom axiom2 : ∀ x y z : α, d x y + d z y ≥ d x z

-- 証明すべき補題2: 対称性 d(x, y) = d(y, x)
lemma symmetric (d : α → α → ℝ) (x y : α) : d x y = d y x := by
  apply le_antisymm
  have h1 := axiom2 d x x y
  rw [(axiom1 d x x).mpr rfl] at h1
  simp_all

  have h2 := axiom2 d y y x
  rw [(axiom1 d y y).mpr rfl] at h2
  simp at h2
  simp_all

-- 証明すべき補題1: 非負性 d(x, y) ≥ 0
lemma nonneg (d : α → α → ℝ) (x y : α) : d x y ≥ 0 := by
  have h := axiom2 d x y x
  have hxx : d x x = 0 := (axiom1 d x x).mpr rfl
  simp_all only [ge_iff_le, nonneg_add_self_iff]

  --文法上clear axiom1 axiom2 できない。

  --------------------
  ------練習2--------
  --------------------

variable {X : Type} [DecidableEq X]

-- 距離関数 d の定義
def d_2 (x y : X) : ℝ := if x = y then 0 else 1

-- 距離空間の条件を示します
example : ∀ x y z : X, d_2 x y ≥ 0 ∧ d_2 x y = d_2 y x ∧ (d_2 x y = 0 ↔ x = y) ∧ (d_2 x y + d_2 y z ≥ d_2 x z) := by
  intro x y z
  constructor
  -- 非負性
  · by_cases h : x = y
    · rw [d_2, if_pos h]
      --exact le_refl 0
    · rw [d_2, if_neg h]
      exact zero_le_one
  constructor
  -- 対称性
  · by_cases h : x = y
    · rw [d_2, if_pos h]
      subst h
      simp [d_2]
    · rw [d_2, d_2, if_neg h]
      split
      next h_1 =>
        subst h_1
        simp_all only [not_true_eq_false]
      next h_1 => simp_all only
  constructor
  -- 同一性
  · apply Iff.intro
    · intro a
      rw [d_2] at a
      simp_all only [ite_eq_left_iff, one_ne_zero, imp_false, Decidable.not_not]
    · intro a
      subst a
      simp [d_2]
  -- 三角不等式
  · by_cases hxz : x = z
    · rw [d_2]
      subst hxz
      simp_all only [ge_iff_le]
      split
      next h =>
        subst h
        simp_all only [zero_add, le_refl]
      next h =>
        simp [d_2, h]
        split
        next h_1 =>
          subst h_1
          simp_all only [not_true_eq_false]
        next h_1 => simp_all only [nonneg_add_self_iff, zero_le_one]
    · by_cases hxy : x = y
      · subst hxy
        simp_all only [ge_iff_le, le_add_iff_nonneg_left]
        rw [d_2]
        simp_all only [↓reduceIte, le_refl]
      · simp_all only [ge_iff_le]
        have dxz: d_2 x z = 1 := by
          rw [d_2, if_neg hxz]
        have dxy: d_2 x y = 1 := by
          rw [d_2, if_neg hxy]
        rw [dxz,dxy]
        simp
        rw [d_2]
        split
        next h =>
          subst h
          simp_all only [not_false_eq_true, le_refl]
        next h => simp_all only [zero_le_one]

--------------------
------練習3--------
--------------------

open Real
open Metric

theorem sum_sq_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) :
  (∑ i in Finset.univ, (x i) ^ 2) = 0 ↔ ∀ i, x i = 0 := by
  apply Iff.intro
  · intro h
    have h_nonneg : ∀ i ∈ Finset.univ, (x i) ^ 2 ≥ 0 := fun i _ => sq_nonneg (x i)
    have h_zero : ∀ i ∈ Finset.univ, (x i) ^ 2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h
    intro i
    exact pow_eq_zero (h_zero i (Finset.mem_univ i))
  · intro h
    rw [Finset.sum_eq_zero]
    intro i _
    rw [h i]
    exact zero_pow (by norm_num)

-- 各 i に対して (x i - z i)^2 の項の展開が成立することを示す補題
lemma sum_sq_expand {n : ℕ} (x y z : Fin n → ℝ) :
  ∑ i : Fin n, ((x i - y i) ^ 2 + 2 * (x i - y i) * (y i - z i) + (y i - z i) ^ 2) ≤
    ∑ i : Fin n, (x i - y i) ^ 2 + ∑ i : Fin n, (y i - z i) ^ 2 + ∑ i : Fin n, 2 * |(x i - y i) * (y i - z i)| := by
  -- 各 i に対して項ごとの不等式を構成する

  -- 定義した関数fとgを用意
  let f := λ i => (x i - y i)^2 + 2 * (x i - y i) * (y i - z i) + (y i - z i)^2
  let g := λ i => (x i - y i)^2 + (y i - z i)^2 + 2 * |(x i - y i) * (y i - z i)|
  have h_each : ∀ i ∈ Finset.univ, f i ≤ g i := by
    intro i _
      -- 2ab ≤ 2|ab|
    have : 2 * (x i - y i) * (y i - z i) ≤ 2 * |(x i - y i) * (y i - z i)| := by
      --have h_pos : 0 < 2 := by norm_num
      rw [mul_assoc]
      apply @mul_le_mul_of_nonneg_left _ 2 ((x i - y i) * (y i - z i)) (|(x i - y i) * (y i - z i)|) _ _ _ _
      simp_all only [Finset.mem_univ, Nat.ofNat_pos]
      exact le_abs_self _
      simp_all only [Finset.mem_univ, Nat.ofNat_nonneg]
      -- (x i - y i)^2 + 2ab + (y i - z i)^2 ≤ (x i - y i)^2 + (y i - z i)^2 + 2|ab|
    simp_all only [Finset.mem_univ, ge_iff_le, f, g]
    linarith

  -- Finset.sum_le_sum に h_each を適用
  have tmp: ∑ i : Fin n, ((x i - y i) ^ 2 + 2 * (x i - y i) * (y i - z i) + (y i - z i) ^ 2) ≤ ∑ i : Fin n, ((x i - y i) ^ 2 + (y i - z i) ^ 2 + 2 * |(x i - y i) * (y i - z i)|)
:= by
    exact Finset.sum_le_sum h_each
  have tmp2: ∑ i : Fin n, (x i - y i) ^ 2 + ∑ i : Fin n, (y i - z i) ^ 2 + ∑ i : Fin n, 2 * |(x i - y i) * (y i - z i)| = ∑ i : Fin n, ((x i - y i) ^ 2 + (y i - z i) ^ 2 + 2 * |(x i - y i) * (y i - z i)|):= by
   rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_all only [Finset.mem_univ, true_implies, f, g]

lemma cauchy_schwarz' {n : ℕ} (a b : Fin n → ℝ) :
  (∑ i : Fin n, |a i * b i|) ≤ sqrt (∑ i : Fin n, a i^2) * sqrt (∑ i : Fin n, b i^2) :=
  by
    --apply CauchySchwarz.le _ _
    apply Finset.sum_mul_sq_le_sq_mul_sq --2乗の形で書かれている。

/- エラーたくさん 消す
-- Cauchy-Schwarz の不等式を Finset に対して定義する補題
lemma CauchySchwarz_finset {n : ℕ} (a b : Fin n → ℝ) :
  ∑ i, |a i * b i| ≤ Real.sqrt (∑ i, a i^2) * Real.sqrt (∑ i, b i^2) := by
  -- 各項の絶対値を取ったシーケンスを定義
  let a' := λ i=> |a i|
  let b' := λ i=> |b i|

  -- a' と b' の各項が非負であることを確認
  have h_nonneg_a : ∀ i, a' i ≥ 0 := λ i=> abs_nonneg (a i)
  have h_nonneg_b : ∀ i, b' i ≥ 0 := λ i=> abs_nonneg (b i)

  -- Cauchy-Schwarz の標準的不等式を適用
  have inner_product_le : ∑ i, a' i * b' i ≤ Real.sqrt (∑ i, a' i^2) * Real.sqrt (∑ i, b' i^2) := by
    simp_all only [ge_iff_le, abs_nonneg, implies_true, sq_abs, a', b']
    sorry

  -- 右辺を展開して ∑ |a_i * b_i| に一致させる
  have : ∑ i, a' i * b' i = ∑ i, |a i * b i| :=
    Finset.sum_congr rfl (λ i _=> by
    exact abs_mul (a i) (b i))

  rw [this] at inner_product_le
  exact inner_product_le
-/

lemma le_of_le_sum_of_nonneg {a b c : ℝ}
  (ha : a ≥ 0)
  (hb : b ≥ 0)
  (hc : c ≥ 0)
  (h : c^2 ≤ a^2 + b^2 + 2 * a * b) :
  c ≤ a + b := by
  -- 右辺の和の平方を計算します
  have h_sum_sq : (a + b)^2 = a^2 + b^2 + 2 * a * b:= by ring

  -- 仮定 h を h_sum_sq に基づいて書き換えます
  rw [←h_sum_sq] at h

  -- 両辺が非負であることを確認します
  have hab_nonneg : a + b ≥ 0 := add_nonneg ha hb

  -- 両辺の平方根を取る準備として、c^2 ≤ (a + b)^2 を確認します
  -- 両辺が非負なので、sqrt を適用できます
  -- これは sqrt が単調増加関数であることを利用します
  have h_sqrt : sqrt (c^2) ≤ sqrt ((a + b)^2) := by
    apply sqrt_le_sqrt
    exact h

  -- c は非負であるため、sqrt (c^2) = c となります
  simp_all only [ge_iff_le, sqrt_sq]
  contrapose! hab_nonneg
  nlinarith

-- n次元のユークリッド空間上のユークリッド距離を定義します。
noncomputable def euclidean_dist {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

-- 距離空間であることを示します。
instance : MetricSpace (Fin n → ℝ) where
  dist := euclidean_dist
  dist_self := by
    intro x
    unfold euclidean_dist
    have : ∑ i, (x i - x i) ^ 2 = 0 := by
      simp [pow_two, sub_self]
    simp_all only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, sqrt_zero]
  eq_of_dist_eq_zero := by
    intro x y h
    unfold euclidean_dist at h
    have this_lem: (∑ i, (x i - y i) ^ 2) = 0 := by
      exact (sqrt_eq_zero h).mp
    have eq_zero : ∀ i, (x i - y i) ^ 2 = 0 := by -- fun i =>
      intro i
      have eq_zero := sum_sq_eq_zero_iff (λ i => x i - y i)
      simp_all only [sqrt_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
        implies_true]

    exact funext fun i => sub_eq_zero.mp (pow_eq_zero (eq_zero i))
  dist_comm := by
    intro x y
    unfold euclidean_dist
    simp_all only
    congr
    ext1 x_1
    ring

  dist_triangle := by
    intro x y z
    unfold euclidean_dist
        -- まず、2乗した形で三角不等式を証明します
    have squared_triangle_ineq : (∑ i, (x i - z i) ^ 2) ≤ (∑ i, (x i - y i) ^ 2) + (∑ i, (y i - z i) ^ 2) + ∑ i, 2 * |(x i - y i) * (y i - z i)| := by
      calc
        ∑ i, (x i - z i) ^ 2 = ∑ i, ((x i - y i) + (y i - z i)) ^ 2 := by
          congr
          ext i
          simp_all only [sub_add_sub_cancel]
        _ = ∑ i, ((x i - y i) ^ 2 + 2 * (x i - y i) * (y i - z i) + (y i - z i) ^ 2) := by
          simp only [sq, add_mul, mul_add, add_assoc]
          congr
          ext1 x_1
          simp_all only [add_right_inj]
          ring
        _ ≤ ∑ i, (x i - y i) ^ 2 + ∑ i, (y i - z i) ^ 2 + ∑ i, 2 * |(x i - y i) * (y i - z i)| := by

          exact sum_sq_expand x y z

    have squared_triangle_eq : (∑ i, (x i - z i) ^ 2) = (∑ i, (x i - y i) ^ 2) + (∑ i, (y i - z i) ^ 2) + ∑ i, 2 * (x i - y i) * (y i - z i) := by
      calc
        ∑ i, (x i - z i) ^ 2 = ∑ i, ((x i - y i) + (y i - z i)) ^ 2 := by
          congr
          ext i
          simp_all only [sub_add_sub_cancel]
        _ = ∑ i, ((x i - y i) ^ 2 + 2 * (x i - y i) * (y i - z i) + (y i - z i) ^ 2) := by
          simp only [sq, add_mul, mul_add, add_assoc]
          congr
          ext1 x_1
          simp_all only [add_right_inj]
          ring
        _ = (∑ i, (x i - y i) ^ 2) + (∑ i, (y i - z i) ^ 2) + ∑ i, 2 * (x i - y i) * (y i - z i) := by
          rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
          ring

    dsimp [dist]
    apply @le_of_le_sum_of_nonneg √(∑ i : Fin n, (x i - y i) ^ 2)  √(∑ i : Fin n, (y i - z i) ^ 2) √(∑ i : Fin n, (x i - z i) ^ 2)
    simp_all only [ge_iff_le, sqrt_nonneg]
    simp_all only [ge_iff_le, sqrt_nonneg]
    simp_all only [ge_iff_le, sqrt_nonneg]
    convert squared_triangle_ineq --この条件ではないよう。
    · rw [sq]
      field_simp
    · symm
      field_simp
    · symm
      field_simp
    · -- goal 2 * √(∑ i : Fin n, (x i - y i) ^ 2) * √(∑ i : Fin n, (y i - z i) ^ 2) = ∑ i : Fin n, 2 * |(x i - y i) * (y i - z i)|
      --これは等号では一般には成り立たない。<=不等号であれば、成り立つ。
      --have squared_triangle_ineq : (∑ i, (x i - z i) ^ 2) ≤ (∑ i, (x i - y i) ^ 2) + (∑ i, (y i - z i) ^ 2) + ∑ i, 2 * (x i - y i) * (y i - z i)
      --という絶対値なしを証明すべきだったのか。ここでコーシーシュワルツを使う必要あり。
      sorry
