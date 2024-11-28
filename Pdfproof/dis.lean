import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
--import Mathlib.Analysis.Supremum
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Order.Monotone
import Mathlib.Data.Set.Defs
import Mathlib.Order.SetNotation


--import Mathlib.Integral.IntervalIntegral

import Mathlib.Data.Fintype.Basic
--import Mathlib.Analysis.NormedSpace.Basic
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
--証明するのに丸一日かかった。

open Real --sqrtを使うため

--下で使っている。
lemma sum_sq_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) :
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
    simp

-- 各 i に対して (x i - z i)^2 の項の展開が成立することを示す補題。下で使っている。
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



--下で使っている
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


lemma le_of_le_mul_of_nonneg {a b c : ℝ}
  (ha : a ≥ 0)
  (hb : b ≥ 0)
  (hc : c ≥ 0)
  (h : c^2 ≤ a^2 * b^2) :
  c ≤ a * b := by
    have hh: c^2 <= (a*b)^2 := by
      rw [pow_two]
      simp_all only [ge_iff_le]
      linarith
    have hab: a*b ≥ 0 := by
      exact mul_nonneg ha hb

    by_contra hlt
    simp_all only [ge_iff_le, not_le]
    have := hh
    simp_all only
    rw [mul_comm] at this
    nlinarith

lemma finset_sum_abs_mul_le_sqrt_mul_sqrt {α : Type*} (s : Finset α) (f g : α → ℝ) :
    ∑ i in s, |f i * g i| ≤ sqrt (∑ i in s, f i ^ 2) * sqrt (∑ i in s, g i ^ 2) := by
  -- 各項の絶対値付きのコーシー・シュワルツ不等式を用意
  have cauchy_schwarz := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => |f i|) (fun i => |g i|)
  apply le_of_le_mul_of_nonneg
  simp only [sq_abs, ge_iff_le, sqrt_nonneg]
  simp only [sq_abs, ge_iff_le, sqrt_nonneg]
  simp only [sq_abs, ge_iff_le]
  positivity
  simp_all
  have congr_sum: ∑ i in s, |f i * g i| = ∑ i in s, |f i| * |g i| := by
    apply Finset.sum_congr rfl
    intros i _
    exact abs_mul (f i) (g i)
  rw [←congr_sum] at cauchy_schwarz
  simp_all
  rw [Real.sq_sqrt]
  rw [Real.sq_sqrt]
  exact cauchy_schwarz
  positivity
  positivity

--下で使っているので、正しく証明する必要あり。上の補題と同じ。
lemma cauchy_schwarz' {n : ℕ} (a b : Fin n → ℝ) :
  (∑ i : Fin n, |a i * b i|) ≤ sqrt (∑ i : Fin n, a i^2) * sqrt (∑ i : Fin n, b i^2) :=
  by
    have fi := finset_sum_abs_mul_le_sqrt_mul_sqrt Finset.univ a b
    exact fi

-- n次元のユークリッド空間上のユークリッド距離を定義します。
noncomputable def euclidean_dist {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

-- 距離空間であることを示します。
noncomputable instance : MetricSpace (Fin n → ℝ) where
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
      dsimp [dist] at h
      rw [Real.sqrt_eq_zero] at h
      exact h
      positivity
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
    -- コメントアウトするとエラーが出る
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

    --コメントアウトするとエラーが出る。コーシーシュワルツの不等式。
    have lem_cauchy: ∑ i, 2 * |(x i - y i) * (y i - z i)| ≤ 2 * sqrt (∑ i, (x i - y i) ^ 2) * sqrt (∑ i, (y i - z i) ^ 2) := by
      have h_cauchy := cauchy_schwarz' (λ i => x i - y i) (λ i => y i - z i)
      norm_num
      rw [mul_assoc]
      rw [←Finset.mul_sum]
      apply @mul_le_mul_of_nonneg_left _ 2  (∑ i :Fin n,|(x i - y i) * (y i - z i)|) (sqrt (∑ i :Fin n, (x i - y i) ^ 2) * sqrt (∑ i :Fin n, (y i - z i) ^ 2))
      simp_all only [add_le_add_iff_left]
      simp_all only [add_le_add_iff_left, Nat.ofNat_nonneg]

    dsimp [dist]

    apply @le_of_le_sum_of_nonneg √(∑ i : Fin n, (x i - y i) ^ 2)  √(∑ i : Fin n, (y i - z i) ^ 2) √(∑ i : Fin n, (x i - z i) ^ 2)
    simp_all only [sqrt_nonneg]
    simp_all only [sqrt_nonneg]
    simp_all only [sqrt_nonneg]
    rw [Real.sq_sqrt]
    rw [Real.sq_sqrt]
    rw [Real.sq_sqrt]
    linarith
    positivity
    positivity
    positivity

--------------------
------練習4--------
--------------------

-- n 次元実数空間を Fin n → ℝ として定義
def EuclideanSpace (n : ℕ) := Fin n → ℝ
axiom n_pos {n : ℕ} : n > 0

lemma univ_nonempty {n : ℕ} : (Finset.univ : Finset (Fin n)).Nonempty :=
  Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp n_pos)
-- 距離関数 d' の定義
def d' {n : ℕ} (x y : EuclideanSpace n) : ℝ :=
    if h : n > 0 then (Finset.univ : Finset (Fin n)).sup' (by
    simp_all only [gt_iff_lt]
    rw [Finset.univ_nonempty_iff]
    cases n
    · simp_all only [lt_self_iff_false]
    · simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
      infer_instance) (λ i => |x i - y i|) else 0

-- 非負性の証明
lemma d'_nonneg {n : ℕ} (x y : EuclideanSpace n) : 0 ≤ d' x y :=
  by
    unfold d'
    by_cases h : n > 0
    · simp_all only [gt_iff_lt, ↓reduceDIte, Finset.le_sup'_iff, Finset.mem_univ, abs_nonneg, and_self]
      apply Exists.intro
      · simp_all only
      · use 0
    · simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, lt_self_iff_false, ↓reduceDIte, le_refl]

-- 同一性の証明 nが1以上である仮定が必要か。
lemma d'_eq_zero {n : ℕ} (x y : EuclideanSpace n) : d' x y = 0 ↔ x = y := by
  apply Iff.intro
  · intro h
    unfold d' at h
    let s:= (Finset.univ : Finset (Fin n))
    have s_nonempty:s.Nonempty := univ_nonempty
    have h_abs : ∀ i, |x i - y i| = 0 := by
      intro i
      have h_sup := (@Finset.sup'_le_iff  Real (Fin n) _ _ s_nonempty (λ i => abs (x i - y i)) (0:ℝ)).mp
      simp [↓reduceDIte, s] at h
      let hh := h n_pos
      simp_all only [s]
      simp only [Finset.mem_univ, abs_nonpos_iff, true_implies, abs_zero, Finset.sup'_const, le_refl,
        implies_true, abs_eq_zero] at hh
      simp_all only [s]
      simp at h_sup
      exact abs_eq_zero.mpr (h_sup i)

    have h_eq : ∀ i, x i = y i := by
      intro i
      simp_all only [gt_iff_lt, ↓reduceDIte, Finset.sup'_const, dite_eq_ite, ite_self, abs_eq_zero]
      convert sub_eq_zero.1 (h_abs i)
    simp_all only [gt_iff_lt, ↓reduceDIte, sub_self, abs_zero, Finset.sup'_const, dite_eq_ite, ite_self, implies_true]
    funext i
    simp_all only

  · intro h
    subst h
    unfold d'
    by_cases h : n > 0
    · simp_all only [gt_iff_lt, ↓reduceDIte, Finset.le_sup'_iff, Finset.mem_univ, and_self]
      simp_all only [sub_self, abs_zero, Finset.sup'_const]
    · simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, lt_self_iff_false, ↓reduceDIte, le_refl]

-- 対称性の証明
lemma d'_symm {n : ℕ} (x y : EuclideanSpace n) : d' x y = d' y x :=
  by
    unfold d'
    by_cases h : n > 0
    · by_cases h : n > 0
      · simp only [d', h, if_true]
        congr
        ext i
        simp_all only [gt_iff_lt]
        simp_rw [abs_sub_comm]
      · simp_all only [gt_iff_lt]
    · simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, lt_self_iff_false, ↓reduceDIte]

-- 三角不等式の証明
lemma d'_triangle {n : ℕ} (x y z : EuclideanSpace n) : d' x z ≤ d' x y + d' y z :=
  by
    unfold d'
    by_cases h : n > 0
    · simp only [d', h, if_true]
      apply Finset.sup'_le
      simp_all only [gt_iff_lt]
      rw [Finset.univ_nonempty_iff]
      use 0
      intro i
      intro _
      simp_all only [gt_iff_lt, ↓reduceDIte, Finset.le_sup', Finset.mem_univ, abs_sub]
      -- goal |x i - z i| ≤ (Finset.univ.sup' ⋯ fun i ↦ |x i - y i|) + Finset.univ.sup' ⋯ fun i ↦ |y i - z i|
      calc
        |x i - z i| = |(x i - y i) + (y i - z i)| := by rw [sub_add_sub_cancel]
        _ ≤ |x i - y i| + |y i - z i| := abs_add _ _
      apply add_le_add
      · simp_all only [Finset.le_sup'_iff, Finset.mem_univ, true_and]
        simp_all only [gt_iff_lt]
        use i
      · simp_all only [Finset.le_sup'_iff, Finset.mem_univ, true_and]
        simp_all only [gt_iff_lt]
        use i
    · simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, lt_self_iff_false, ↓reduceDIte, add_zero, le_refl]

-- 距離空間のインスタンスの定義
instance EuclideanSpace_metric {n : ℕ} : MetricSpace (EuclideanSpace n) :=
{
  dist := d',
  dist_self := λ x => (d'_eq_zero x x).mpr rfl,
  dist_comm := d'_symm,
  dist_triangle := d'_triangle,
  eq_of_dist_eq_zero := by
    intro x y h
    exact (d'_eq_zero x y).mp h
}

--------------------
------練習5--------
--------------------

def Ic := Set.Icc (0:Real) 1

--rangeが有界であることを示す。
lemma bdd_above_range {fs :  Ic → ℝ} (hf2 : Continuous fs):
  BddAbove (Set.range fs) := by
    let Ic := Set.Icc (0:Real) 1
    --let fs : Ic → ℝ := λ x => f x.val
    have isCompact_Icc_s: IsCompact (Set.univ : Set Ic) := by
      simp_all only [Ic]
      exact isCompact_univ
    --have isCompact_Icc_s2: IsCompact Ic := by
    --  simp_all only [Ic]
    --  apply isCompact_Icc
    --have hf2: Continuous fs := by
    --  simp_all only [Ic, fs]
    --  rw [continuousOn_iff_continuous_restrict] at hf
    --  exact hf
    obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ fs '' Set.univ, y ≤ M :=
      IsCompact.bddAbove (IsCompact.image isCompact_Icc_s hf2)
    -- 上界を明示

    use M
    -- y が f の像に属する場合に上界を確認
    intros y hy
    apply hM y
    simp_all

--直接は、使ってない。rangeが閉集合であること。地域のcompact性はcompact_image2などで示している。
lemma image_closed
  {fs : Ic → ℝ}
  (hf : Continuous fs ) :
  IsOpen ((fs '' (Set.univ : Set Ic))ᶜ) := by
  -- 閉区間 [a, b] がコンパクトであることを確認
  --have compact_Icc : IsCompact (Set.Icc a b) := isCompact_Icc

  -- 関数 f が [a, b] 上で連続であることを確認
  --have f_continuous : ContinuousOn f (Set.Icc a b) := hf

  --let s := Set.Icc a b
  --let fs : Ic → ℝ := λ x => f x

  have compact_Icc_s: IsCompact Ic := isCompact_Icc
  have compact_Icc_s2: IsCompact (Set.univ : Set Ic) := by
    simp_all only [Ic]
    exact isCompact_univ

  have compact_image : IsCompact (fs '' (Set.univ:Set Ic)) := by
    simp_all only [Set.image_univ]
    have compact_Icc_s := compact_Icc_s2
    simp_all only
    simpa using compact_Icc_s.image hf

  -- f の像 f '' [a, b] がコンパクトであることを確認

  -- 実数空間ではコンパクト集合は閉集合であるため、f '' [a, b] は閉集合
  have closed_image : IsClosed (fs '' Set.univ) := by
    simp_all only [Set.image_univ]
    exact compact_image.isClosed

  simp_all only [Set.image_univ, isOpen_compl_iff]

--使ってない。消してよさそう。
lemma closure_extensive: ∀ {α : Type} [TopologicalSpace α] (s : Set α), s ⊆ closure s := by
  intro α
  intro s
  intro x
  intro h
  intro a
  exact subset_closure a

--いつの間にかエラーが解消したが、使ってない。消してよさそう。
lemma closed_ssup {α : Type} [TopologicalSpace α] (ss : Set α) (s : Set ℝ) (non:Nonempty ss)(hBddAbove : Bornology.IsBounded s) (h : IsClosed s) (f : α → ℝ) : f '' (Set.univ : Set ss) = s → ∃ x : ss, f x = sSup s := by
  intro a
  rw [←a]
  simp_all only [Set.image_univ, Subtype.exists]
  --let s := f ''  ss
  have lem0: IsClosed s := by
    subst a
    simp_all only [nonempty_subtype, Subtype.range_coe_subtype, Set.setOf_mem_eq]

  have nonemp: s.Nonempty := by
    dsimp [Nonempty]
    obtain ⟨val, property⟩ := non
    subst a
    simp_all only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq, Set.image_nonempty]
    use val

  have nonemp2: Nonempty s:= by
    simp
    exact nonemp

    -- 実数空間では、閉かつ有界な集合はコンパクトである
  have h_compact : IsCompact s :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨lem0, hBddAbove⟩

  have h_max : ∃ y ∈ s, y = sSup s := by
    use sSup s
    constructor
    exact IsCompact.sSup_mem h_compact nonemp
    exact rfl

  subst a
  simp_all only [nonempty_subtype, Subtype.range_coe_subtype, Set.setOf_mem_eq, Set.image_nonempty, Set.mem_image,
    exists_eq_right, exists_prop]


  /- 未完成だし、使ってない。
  lemma closed_supr {α : Type} [TopologicalSpace α] (ss : Set α) (s : Set ℝ) (non:Nonempty ss)(hBddAbove : Bornology.IsBounded s) (h : IsClosed s) (f : α → ℝ) : f '' (Set.univ : Set ss) = s → ∃ x : ss, f x = ⨆ y ∈ s,y := by
  intro a
  rw [←a]
  simp_all only [Set.image_univ, Subtype.exists]
  --let s := f ''  ss
  have lem0: IsClosed s := by
    subst a
    simp_all only [nonempty_subtype, Subtype.range_coe_subtype, Set.setOf_mem_eq]

  have nonemp: s.Nonempty := by
    dsimp [Nonempty]
    obtain ⟨val, property⟩ := non
    subst a
    simp_all only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq, Set.image_nonempty]
    use val

  have nonemp2: Nonempty s:= by
    simp
    exact nonemp

    -- 実数空間では、閉かつ有界な集合はコンパクトである
  have h_compact : IsCompact s :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨lem0, hBddAbove⟩

   --isLUB_ciSup∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyCompleteLattice α] [inst_1 : Nonempty ι] {f : ι → α},   BddAbove (range f) → IsLUB (range f) (⨆ i, f i)
  have h_LUB : IsLUB s (⨆ y ∈ s,y) := by
    exact Real.isLUB_sSup s nonemp hBddAbove
  have h_max : ∃ y ∈ s, y = ⨆ z ∈ s,z := by
    use ⨆ (z ∈ s),z
    constructor
    exact IsCompact.sSup_mem h_compact nonemp
    --sが閉集合の仮定hを使うかも。実数の集合で有界な閉集合な集合はコンパクトで最大値が存在。
    --#check cSup_mem
    --exact Real.isLUB_sSup s nonemp h_bdd_above



  subst a
  simp_all only [nonempty_subtype, Subtype.range_coe_subtype, Set.setOf_mem_eq, Set.image_nonempty, Set.mem_image,
    exists_eq_right, exists_prop]
  -/

--Bornology.IsBoundedのほう。
lemma cont_bounded {a b : ℝ} (hab : a ≤ b)
  {f : ℝ → ℝ}
  (hf : ContinuousOn f (Set.Icc a b)):
  let s := Set.Icc a b
  let fs : s → ℝ := λ x => f x.val
  @Bornology.IsBounded Real _ ((Set.image fs (Set.univ : Set s)):Set Real) :=
  by
    --have compact_Icc : IsCompact (Set.Icc a b) := isCompact_Icc
    have f_continuous : ContinuousOn f (Set.Icc a b) := hf
    let s := Set.Icc a b
    let fs : s → ℝ := λ x => f x.val
    let bdd_s : @Bornology.IsBounded Real _ ((fs '' (Set.univ:Set s)):Set Real) := by
      have fs_continuous : Continuous fs := continuousOn_iff_continuous_restrict.mp f_continuous
      have compact_Icc_s: IsCompact (Set.univ : Set s) := isCompact_univ
      /-
      have compact_image : IsCompact ((fs '' Set.univ):Set Real) := by
        exact IsCompact.image compact_Icc_s fs_continuous
      have closed_image : IsClosed ((fs '' Set.univ):Set Real) := IsCompact.isClosed (IsCompact.image compact_Icc_s fs_continuous)
      -/
      have compact_image2 : IsCompact ((fs '' Set.univ):Set Real) := by
        exact IsCompact.image compact_Icc_s fs_continuous
      /-
      have closed_image2 : IsClosed ((fs '' Set.univ):Set Real) := IsCompact.isClosed compact_image2
      have h_image :((fs '' (Set.univ : Set s)):Set Real) = ((f '' Set.Icc a b):Set Real) := by
        simp only [Set.image_univ, Subtype.range_coe_subtype]
        simp_all only [Set.image_univ, s, fs]
        rw [Set.image_eq_range]
      have exist_lem: ∃ t, IsCompact t ∧((fs '' (Set.univ:Set s)):Set Real) ⊆ t:= by
        use fs '' Set.univ
      -/
      have bdd: @Bornology.IsBounded Real _ (fs '' (Set.univ:Set s):Set Real) := by
        --let tmp:= (@Bornology.inCompact.isBounded_iff Real _ ((fs '' (Set.univ:Set s)):Set Real)).mpr exist_lem
        --こっちの関数はうまくいかなかった。
        let tmp:= IsCompact.isBounded compact_image2
        exact tmp
      exact bdd
    exact bdd_s

lemma sup_exists {f : Ic → ℝ}
  (hf : Continuous f) :
  ∃ x : Ic, f x = sSup (f '' (Set.univ:Set Ic)) := by
  -- 区間 [a, b] がコンパクトであることを確認
    have lem0: IsClosed (f '' (Set.univ:Set Ic)) := by
      have closed_image : IsClosed (Set.univ:Set Ic) := by
        simp_all only [isClosed_univ]
      exact isOpen_compl_iff.mp (image_closed hf)

    have bdd: Bornology.IsBounded (f '' Set.Icc a b) := by
      --have h_compact : IsCompact (Set.Icc a b) := isCompact_Icc
      have h_bdd := cont_bounded hf
      simp_all only [Set.image_univ]
      convert h_bdd
      rw [Set.image_eq_range]


--
lemma supr_exists {f : Ic → ℝ}
  (hf : Continuous f) :
  ∃ x : (Set.univ:Set Ic), f x = ⨆ ( y ∈ f '' (Set.univ:Set Ic)), y:= by
  -- 区間 [a, b] がコンパクトであることを確認
    have lem0: IsClosed (f '' (Set.univ:Set Ic)) := by
      have closed_image : IsClosed (f '' (Set.univ:Set Ic)) := isOpen_compl_iff.mp (image_closed hf)
      simp_all only [Set.image_univ]
--Bornologyでのrangeのbounded性。未完成だが使うことがあるのか。
    have bdd: Bornology.IsBounded (f '' (Set.univ:Set Ic)) := by
      --have h_compact : IsCompact (Set.Icc a b) := isCompact_Icc
      simp_all only [Set.image_univ]
      sorry
    sorry

--下のbfで同じことをしているので、不要だったかも。でもこちらは上限値を与えている？
theorem bounded_closed_set_has_maximum (S : Set ℝ) (h_bdd : BddAbove S) (h_closed : IsClosed S) (h_nonempty : S.Nonempty) :
  ∃ x ∈ S, ∀ y ∈ S, y ≤ x := by
  -- S が空でないことを仮定
    -- sup S が存在する（BddAbove と Nonempty の仮定により）
    let M := sSup S
    -- sup S が上界であることと、S が閉集合であることを利用
    have hM_sup : ∀ y ∈ S, y ≤ M := λ y hy => le_csSup h_bdd hy
    have hM_closed : M ∈ S := by
      exact IsClosed.csSup_mem h_closed h_nonempty h_bdd

    use M

--一般論での包含関係とsupの関係。使ってない。消してよさそう。
lemma bdd_subset {A B : Set ℝ} (hB_subset_A : B ⊆ A) (hA_bdd : BddAbove A) : BddAbove B := by
    -- `A` が上に有界であることから、上界 `M` を得る
    obtain ⟨M, hM⟩ := hA_bdd
    -- `M` を `B` の上界として使用
    use M
    intros x hx
    -- `B ⊆ A` なので `x ∈ A` も成り立つ
    exact hM (hB_subset_A hx)

--有界で閉のAの上限がAに属すること。
lemma bf_subset3 {A:Set Real} (h3_closed: IsClosed A)(b3_bdd:BddAbove A)(b3_nonempty:A.Nonempty ) : sSup A ∈ A := by
  exact IsClosed.csSup_mem h3_closed b3_nonempty b3_bdd

--chatGPTに成り立つかどうか聞いてみる。成り立ちそうな感じはする。bf_subset3を利用して証明できないか。
--lemma bf_subset4 {A:Set Real} (h3_closed: IsClosed A)(b3_bdd:BddAbove A)(b3_nonempty:A.Nonempty ) : ⨆ z ∈ A,z ∈ A := by

lemma sup_lem {x : Ic} (f : Ic → Real) (hf: Continuous f): f x ≤ ⨆ y ∈ (f '' (Set.univ : Set (Set.Icc (0 : ℝ) 1))), y := by

  have nonempty : Set.Nonempty Ic := by
    unfold Ic
    simp_all only [Set.nonempty_Icc, zero_le_one]

  have compact_Icc : IsCompact Ic := isCompact_Icc

  have compact_Icc_s: IsCompact (Set.univ : Set Ic) := by
    simp_all only [Ic]
    exact isCompact_univ

  have compact_range_f : IsCompact (f '' (Set.univ:Set Ic)) := by
    simp_all only [Set.image_univ]
    have compact_Icc := compact_Icc_s
    simp_all only
    simpa using compact_Icc.image hf

  have bf: BddAbove (f '' (Set.univ:Set Ic)) := by
    exact IsCompact.bddAbove compact_range_f

  have f_nonempty : (f '' (Set.univ:Set Ic)).Nonempty := by
    simp_all only [Set.image_univ, Set.mem_univ]
    use f x

  have eq_range: (Set.range f) = f '' Set.univ := by
    simp_all only [Set.image_univ, Set.mem_univ, Set.mem_range, exists_apply_eq_apply]

  have bf_subset2: sSup (f '' (Set.univ:Set Ic)) ∈ (f '' (Set.univ:Set Ic)) := by
    exact IsClosed.csSup_mem (IsCompact.isClosed compact_range_f) f_nonempty bf

  have bf_exists: ∃ x ∈ (Set.univ:Set Ic), f x = ⨆ z ∈ (f '' (Set.univ:Set Ic)),z := by
    obtain ⟨x, hx⟩ := supr_exists hf
    use x

    simp_all only [Set.mem_univ, true_and]

  have contain_f : f x ∈ f '' Set.univ := by
    simp_all only [Set.mem_image, Set.mem_univ]
    use x
  /-
  --言明がおかしいような気がする。
  have contain_f2: f x ∈ Set.range fun y ↦ ⨆ (_ : y ∈ f '' Set.univ), y := by
    simp_all only [Set.mem_image, Set.mem_univ]
    obtain ⟨a, ha₀, ha'⟩ := bf_exists
    use a
    simp
    exact le_csSup bf (Set.mem_image_of_mem f (Set.mem_univ x))
  -/




  --成り立つとは思いますが、sSup_rangeでは証明ができないのかも。
  have eq_sup: sSup (f '' (Set.univ:Set Ic)) = ⨆ z ∈ (f '' (Set.univ:Set Ic)),z := by
    --rw [ciSup, Subtype.range_coe]
    rw [sSup_eq_iSup' (f '' (Set.univ:Set Ic))]
    simp
    congr
    --左辺の範囲が問題。ここが問題。
    sorry


  have bf_bdd : BddAbove (f '' Set.univ) := by
    exact IsCompact.bddAbove compact_range_f
  --have compact_range : IsCompact (Set.range (λ y => ⨆ (_ : y ∈ f '' Set.univ), y)) := by
  --  apply IsCompact.range
  --  exact continuous_iSup (λ y=> continuous_const)
  have bf_bdd2: BddAbove (Set.range fun y ↦ ⨆ (_ : y ∈ f '' Set.univ), y) := by
    dsimp [BddAbove]
    use sSup (f '' Set.univ)
    simp
    rintro _ ⟨x, hx, rfl⟩
    have contain_f : f ⟨x, _⟩ ∈ f '' Set.univ := by
      simp_all only [Set.mem_image, Set.mem_univ]
      use x
    exact le_csSup bf contain_f

  exact @le_csSup _ _ (f '' (Set.univ:Set Ic)) _ bf_bdd contain_f

lemma triangle_lem  {f g : Ic → ℝ} (hf : Continuous f) (hg : Continuous g ) :
    (⨆ x  ∈ (Set.univ:Set Ic), f x + g x) ≤ (⨆ x  ∈ (Set.univ:Set Ic), f x) + (⨆ x  ∈ (Set.univ:Set Ic), g x) := by
  -- まず、Set.Icc a b が空でないことを示す補助的な定理を使います
  have nonempty : Set.Nonempty Ic := by
    unfold Ic
    simp_all only [Set.nonempty_Icc, zero_le_one]

  have compact_Icc : IsCompact Ic := isCompact_Icc

 -- have compact_Icc_s : IsCompact (Set.univ:Set Ic) := by

  have compact_Icc_s: IsCompact (Set.univ : Set Ic) := by
    simp_all only [Ic]
    exact isCompact_univ

  have compact_range_f : IsCompact (f '' (Set.univ:Set Ic)) := by
    simp_all only [Set.image_univ]
    have compact_Icc := compact_Icc_s
    simp_all only
    simpa using compact_Icc.image hf

  have bf: BddAbove (f '' (Set.univ:Set Ic)) := by
    exact IsCompact.bddAbove compact_range_f

  dsimp [BddAbove] at bf

  obtain ⟨sup_f, hf'⟩ := bf

  have compact_range_g : IsCompact (g '' (Set.univ:Set Ic)) := by
    simp_all only [Set.image_univ]
    have compact_Icc := compact_Icc_s
    simp_all only
    simpa using compact_Icc.image hg

  have bg: BddAbove (g '' (Set.univ:Set Ic)) := by
    exact IsCompact.bddAbove compact_range_g

  have bg2: BddAbove (Set.range g) := by
    exact bdd_above_range hg

   -- f の上限 sup_f と g の上限 sup_g を定義
  -- fとgは、s上で連続であるため、sの像の上限が存在する
  let sup_f : ℝ := ⨆ y∈ (f '' (Set.univ:Set Ic)),y
  let sup_g : ℝ := ⨆ y∈ (g '' (Set.univ:Set Ic)),y

  have H : ∀ x ∈ (Set.univ:Set Ic), f x + g x ≤ (sup_f : ℝ) + (sup_g : ℝ) := by
    intros x hx
    -- f x ≤ sup_f
    have contain_f: f x ∈ f '' Set.univ := by
      simp_all only [Set.mem_image, Set.mem_univ]
      use x

    --have h_upper : ∀ a ∈ Ic, a  ≤ sSup Ic := λ a ha => le_csSup (IsCompact.bddAbove compact_Icc) ha

/-
    have contain_f2:sup_f ∈ upperBounds (f '' Set.univ) := by
      simp_all only [Set.mem_image, Set.mem_univ]
      dsimp [sup_f]
      dsimp [upperBounds]
      intros y hy
      simp_all only [Set.mem_image, Set.mem_univ]
      simp_all
      rcases hy with ⟨a, ha₀, ha'⟩
      have tmp := le_csSup (IsCompact.bddAbove compact_range_f) (Set.mem_range_self x)

      have y_in_range : y ∈ f '' Set.univ := ⟨⟨a, ha₀⟩, ⟨Set.mem_univ _, ha'⟩⟩

      have y_in_range2 : y ∈ Set.range f := by
        subst ha'
        simp_all only [Set.image_univ, Set.mem_range, exists_apply_eq_apply]

      have y_le_sup : y ≤ ⨆ z ∈ (f '' Set.univ),z := by
        convert le_csSup (IsCompact.bddAbove compact_range_f) y_in_range2
        symm
        rw [sSup_range]
        simp
        have range_tmp2: sSup (Set.range f) = ⨆ z ∈ Set.range f, z := by --成り立ちそうではあるが。
          --exact rfl
          simp_all only [Set.image_univ, Set.mem_univ]
          convert sSup_eq_iSup' (Set.range f)
          simp_all
          sorry


        have range_tmp: iSup f = ⨆ z ∈ Set.range f,z := by
          simp_all only [Set.image_univ, Set.mem_univ]
          rw [(sSup_eq_iSup' (Set.range f) (IsCompact.bddAbove compact_range_f))]

          -/

      /-
      have tmp_eq: sSup (Set.range f) = sup_f := by
        dsimp [sup_f]

        --goal : sSup (Set.range f) = ⨆ (y : ℝ) (H : y ∈ f '' Set.univ), y
        --rw [sSup_eq_iSup (IsCompact.bddAbove compact_range_f)] completeでしか使えない。
        let tmp2 := sSup_eq_iSup' (Set.range f)-- (IsCompact.bddAbove compact_range_f)
        simp_all
        rw [← Set.image_univ] at tmp2
      -/

    --独立した補題にしたほうがいいかも。
    --連続関数に関する最大値が存在する定理にする必要があるので、sSupではなく、iSupにする必要がある。
    --ただし、有界閉を定義域として持つ連続関数の値域は、有界閉であることが示されているので、それから最大値を取るindexがあることを示すことができそう。





    -- f x + g x ≤ sup_f + sup_g を導出
    linarith
/-
  -- したがって、sup (f + g) ≤ sup_f + sup_g
  have :  fs x + gs x ≤ sup_f + sup_g := by
    apply csSup_le
    -- Show that the set is nonempty
    { use a
      simp [hab] }
    -- Show that every element in the set is less than or equal to the upper bound
    { intros x hx
      simp only [hx]
      exact H ⟨x, hx⟩ }

  apply csSup_le
  -- Show that the set is nonempty
  { use a
    simp [hab] }
  -- Show that every element in the set is less than or equal to the upper bound
  { intros x hx
    obtain ⟨y, hy⟩ := hx
    rw [←hy]
    exact H ⟨x, hx⟩ }

-/


def C₀ := ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ

-- 距離関数を定義
noncomputable def supDist (f g : C₀) : ℝ := ⨆ x : Set.Icc 0 1, |(f.1 x) - (g.1 x)|

-- メトリック空間のインスタンスを定義
noncomputable instance : Dist C₀ where
  dist f g := ⨆ x : Set.Icc (0 : ℝ) 1, |(f.1 x) - (g.1 x)|




--indexが有限の場合
lemma sSup_mono {α : Type*} [CompleteLattice α] (f g : ℕ → α) (h : ∀ i, f i ≤ g i) :
  sSup (Set.range f) ≤ sSup (Set.range g) := by
  rw [← iSup, ← iSup] -- `sSup` を `iSup` に変換
  apply iSup_mono
  exact h

--alphaを実数全体にすると、有界性がなくなり、completelatticeにならない。
lemma sSup_mono_cont {α β: Type*} [CompleteLattice α] (f g : β → α) (h : ∀ i:β, f i ≤ g i) :
  sSup (Set.range f) ≤ sSup (Set.range g) := by
  rw [← iSup, ← iSup] -- `sSup` を `iSup` に変換
  apply iSup_mono
  exact h

--まずは、定義域も値域もコンパクトな空間を作る。
--それから3角不等式を証明する。

/-
-- 定義域と連続関数 f, g を仮定
def Ic := Set.Icc (0:Real) 1
variable {f g : Ic → ℝ}
variable (hf : Continuous f)
variable (hg : Continuous g)

example (f g h : C₀) :
  (⨆ x : Set.Icc (0 : ℝ) 1, |f.toFun x - h.toFun x|) ≤
  (⨆ x : Set.Icc (0 : ℝ) 1, |f.toFun x - g.toFun x| + |g.toFun x - h.toFun x|) := by
  let Ic := Set.Icc (0:Real) 1
  calc
    ⨆ x : Set.Icc (0 : ℝ) 1, |f.toFun x - h.toFun x| ≤ ⨆ x : Set.Icc (0 : ℝ) 1, (|f.toFun x - g.toFun x| + |g.toFun x - h.toFun x|) := by
      apply @sSup_mono_cont ((f '' Ic) ∪ (g '' Ic)) (λ (x : Set.Icc (0:Real) 1) => |f.toFun x - g.toFun x|) ( λ x => |g.toFun x - h.toFun x|)
      intro x
      exact abs_sub_le _ _ _
    _ ≤ (⨆ x : Set.Icc (0 : ℝ) 1, |f.toFun x - g.toFun x|) + (⨆ x : Set.Icc (0 : ℝ) 1, |g.toFun x - h.toFun x|) := by
      sorry
-/


instance : MetricSpace C₀ where
  dist := supDist

  -- dist(f, f) = 0 を証明
  dist_self f :=
    calc
      dist f f = ⨆ x ∈ Set.Icc 0 1, |f.1 x - f.1 x| := by
        simp only [sub_self, abs_zero]
        simp_all only [Set.mem_Icc, ciSup_const_zero, ciSup_const]
        simp [dist]
          _ = ⨆ x ∈ Set.Icc 0 1, 0 := by simp
          _ = 0 := by simp_all only [Set.mem_Icc, zero_le, true_and, ciSup_const_zero, ciSup_const]

  -- dist(f, g) = dist(g, f) を証明
  dist_comm f g :=
    calc
      dist f g = ⨆ x : Set.Icc 0 1, |f.1 x - g.1 x| := by rfl
      _ = ⨆ x : Set.Icc 0 1, |g.1 x - f.1 x| := by
        simp_all only [ContinuousMap.toFun_eq_coe]
        simp only [abs_sub_comm]
      _ = dist g f := rfl

  -- 三角不等式を証明: dist(f, h) ≤ dist(f, g) + dist(g, h)
  dist_triangle f g h := by
    have onetwo: 0 < 1:= by
      norm_num
    have f_cont: Continuous f.toFun := f.continuous_toFun
    have g_cont: Continuous g.toFun := g.continuous_toFun
    have h_cont: Continuous h.toFun := h.continuous_toFun
    have fg_cont: Continuous (λ x => f.toFun x - g.toFun x) := by
      exact f_cont.sub g_cont
    have gh_cont: Continuous (λ x => g.toFun x - h.toFun x) := by
      exact g_cont.sub h_cont

    calc
      dist f h = ⨆ x : Set.Icc 0 1, |f.1 x - h.1 x| := by rfl
         _  ≤ ⨆ x : Set.Icc 0 1, |f.1 x - g.1 x| + |g.1 x - h.1 x| := by
          apply triangle_lem fg_cont gh_cont (fun x:Ic => (f.1 x) - (g.1 x)) (fun x => (g.1 x) - (h.1 x))
         /-
            have h_bdd : BddAbove (Set.range (λ x => |f.1 x - g.1 x| + |g.1 x - h.1 x|)) := by
              apply BddAbove.intro
              intro y
              simp only [Set.mem_range, exists_prop]
              rintro ⟨x, rfl⟩
              exact abs_sub_le (f.1 x) (g.1 x) (h.1 x)
              intro y
              simp only [Set.mem_range, exists_prop]
              rintro ⟨x, rfl⟩
              exact abs_sub_le (f.1 x) (g.1 x) (h.1 x)
            exact le_ciSup h_bdd (Set.mem_univ x)
          -/
/-
         _ ≤ ⨆ x ∈ Ic, |f x - g x| + ⨆ x ∈ Ic, |g x - h x| :=
              le_add_of_nonneg_left (supr_nonneg _)
         _ = dist f g + dist g h := rfl
-/


/-
-- 任意の a_i <= ⨆ j ∈ J, a_j を示す定理
theorem le_supr_of_mem {J : Set ℕ} {a : ℕ → ℝ} (i : ℕ) (hi : i ∈ J) : a i ≤ Sup J a :=
  le_Sup hi

-- Jが閉区間 [0,1] である場合の有界性の証明
theorem bounded_image_of_continuous {f : ℕ → ℝ} (hf : Continuous f) : BddAbove (f '' Icc (0 : ℝ) 1) :=
  let J := Icc (0 : ℝ) 1
  have is_compact_J : IsCompact J := isCompact_Icc 0 1
  have is_continuous_f : Continuous (fun x => f x) := hf
  have is_compact_image : IsCompact (f '' J) := is_continuous_f.isCompact_image is_compact_J
  is_compact_image.bddAbove

-- 距離空間としての定義
noncomputable def supNorm (f : Set.Icc 0 1 → ℝ) : ℝ :=
  ⨆ y ∈ (Set.range (λ x => |f x|)),y

noncomputable def C_interval_metric_space : MetricSpace (Set.Icc 0 1 → ℝ) :=
{ dist := λ f g => supNorm (λ x => |f x - g x|),
  dist_self := by
    intro f
    unfold supNorm
    simp_all only [sub_self, abs_zero, Set.range_const, csSup_singleton],
  dist_comm := λ f g => by
    unfold supNorm
    congr
    funext x
    obtain ⟨val, property⟩ := x
    sorry
  dist_triangle := λ f g h =>
    calc
     supNorm (λ x => |f x - h x|) ≤ supNorm (λ x => |f x - g x| + |g x - h x|) :=
      by
        unfold supNorm
        congr
        simp_all only [abs_abs]
        apply Real.sSup_le
        intro x
        exact abs_sub_le (f x) (g x) (h x)
        apply Real.Sup_le_Sup
        intro x
        exact abs_sub_le _ _
    _ ≤ supNorm (λ x => |f x - g x|) + supNorm (λ x => |g x - h x|) :=
      by
        unfold supNorm
        congr
        simp_all only [abs_abs]
        apply Real.sSup_le
        intro x
        exact Real.sSup_add_sSup_le (Set.range (λ x => |f x - g x|)) (Set.range (λ x => |g x - h x|))

}
-/


-----------------------
------練習14-----------
-----------------------

-- 距離空間 X において、開集合の交わりが開集合であることを証明
example {X : Type} [MetricSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
  IsOpen (A ∩ B) :=
by
  --rw [isOpen_iff_ball_subset] 必要ない。

  apply Metric.isOpen_iff.mpr --これがポイント

  intro x hx
  -- x ∈ A ∩ B より x ∈ A かつ x ∈ B
  have ⟨hAx, hBx⟩ := hx

  have hA' := isOpen_iff_mem_nhds.mp hA
  have hB' := isOpen_iff_mem_nhds.mp hB
  rcases Metric.mem_nhds_iff.1 (hA' x hAx) with ⟨εA, hεA, hSubA⟩
  rcases Metric.mem_nhds_iff.1 (hB' x hBx) with ⟨εB, hεB, hSubB⟩
  -- 開球 U ∩ V が x を含むことを示す
  -- ε = min(εA, εB) を定義
  let ε := min εA εB
  have hε : ε > 0  := lt_min hεA hεB
  -- 開球 B(x, ε) が A ∩ B に含まれることを示す
  have ball_lem: Metric.ball x ε ⊆ A ∩ B := by
    intro y hy
    -- 開球 B(x, ε) に含まれる任意の点 y について、y ∈ A かつ y ∈ B を示す
    constructor
    · exact hSubA (lt_of_lt_of_le hy (min_le_left εA εB))
    · exact hSubB (lt_of_lt_of_le hy (min_le_right εA εB))

  have : ∃ ε > 0, Metric.ball x ε ⊆ A ∩ B := by
    exact ⟨ε, hε, ball_lem⟩

  exact this

-----------------------
------練習15-----------
-----------------------

-- 距離空間 X において、開集合の合併が開集合であることを証明
example {X : Type} [PseudoMetricSpace X] (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) :
  IsOpen (⋃ i, U i) :=
by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  -- x ∈ ⋃ i, U i より、ある i が存在して x ∈ U i
  obtain ⟨i, hxU⟩ := Set.mem_iUnion.mp hx
  -- U i が開集合なので、x の開近傍を見つける
  obtain ⟨ε, hε, hV_sub⟩ := Metric.isOpen_iff.mp (hU i) x hxU
  --let V := Metric.ball x ε
  simp_all only [Set.mem_iUnion, gt_iff_lt]
  obtain ⟨w, h⟩ := hx
  apply Exists.intro
  · apply And.intro
    · rfl
    · simp_all only [Set.mem_iUnion]
      apply And.intro
      · exact isOpen_iUnion hU
      · exact ⟨w, h⟩

-----------------------
------練習18-----------
-----------------------

-- 有理数集合が実数空間で稠密であることを証明。もともとdenseになっている。
example : Dense (Set.univ : Set ℚ) :=
by
  simp

-- 有理数集合が実数空間で稠密であることを定義から証明
example : ∀ x : ℝ, ∀ ε > 0, ∃ q : ℚ, |x - q| < ε :=
by
  intros x ε hε
  -- 適切な n を選ぶ
  let n := Nat.ceil (1 / ε)
  --have hn : n > 0 := Nat.ceil_pos.mpr (one_div_pos.mpr hε)
  -- n に基づいて有理数を構成
  let q : ℚ := by
    exact Int.floor (n * x) / n
  use q
  -- q の評価
  calc
    |x - q| = |x - (Int.floor (n * x) / n)| := by simp_all only [gt_iff_lt, one_div, Nat.ceil_pos, inv_pos,
      Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, n, q]
    _  = |x - ↑⌊↑n * x⌋ / ↑n| := by simp_all only [gt_iff_lt, one_div, Nat.ceil_pos, inv_pos, n]
    _  = |(↑n * x) / ↑n - ↑(Int.floor (↑n * x)) / ↑n| := by simp_all only [gt_iff_lt, one_div, Nat.ceil_pos,
      inv_pos, ne_eq, Nat.cast_eq_zero, Nat.ceil_eq_zero, inv_nonpos, not_le, mul_div_cancel_left₀, n]
    _   = |(↑n * x - ↑(Int.floor (↑n * x))) / ↑n| := by rw [sub_div]
    _   = |↑n * x - ↑(Int.floor (↑n * x))| / |↑n| := abs_div _ _
    _  = |n * x - Int.floor (n * x)| / n := by simp_all only [gt_iff_lt, one_div, Nat.ceil_pos, inv_pos,
      Int.self_sub_floor, Nat.abs_cast, n]
    _ < 1 / n := by
      simp_all only [gt_iff_lt, one_div, Nat.ceil_pos, inv_pos, Int.self_sub_floor, n]
      rw [abs]
      simp_all only [neg_le_self_iff, Int.fract_nonneg, sup_of_le_left]
      apply lt_of_le_of_lt _
      rw [div_lt_iff]
      on_goal 5 => {rw [mul_comm]
      }
      · simp_all only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, Nat.ceil_eq_zero, inv_nonpos, not_le,
          IsUnit.inv_mul_cancel]
        apply Int.fract_lt_one
      · simp_all only [Nat.cast_pos, Nat.ceil_pos, inv_pos]
    _ ≤ ε := by
      rw [one_div]
      simp_all only [gt_iff_lt, one_div, Nat.ceil_pos, inv_pos, n]
      rw [inv_le]
      · exact Nat.le_ceil _
      · simp_all only [Nat.cast_pos, Nat.ceil_pos, inv_pos]
      · simp_all only

-----------------------
------練習19-----------
-----------------------

-- 距離空間 X における閉包 cl(A) が閉集合であることを証明
example {X : Type} [MetricSpace X] (A : Set X) :
  IsClosed (closure A) :=
by
  -- 閉包は常に閉集合であることは、閉包の定義から直ちに従う。
  exact isClosed_closure

-- 距離空間 X において、閉包が集積点全体と一致することを証明
example {X : Type} [MetricSpace X] (A : Set X) :
  closure A = {x | ∀ ε > 0, ∃ y ∈ A, dist x y < ε} :=
by
  ext x
  constructor
  -- x ∈ closure A → x は A の集積点
  · intro hx
    rw [Metric.mem_closure_iff] at hx
    exact hx
  -- x が A の集積点 → x ∈ closure A
  · intro hx
    rw [Metric.mem_closure_iff]
    exact hx

-----------------------
------練習24-----------
-----------------------

-- 距離空間の連続写像の同値性。既存の定理を使って示した。
example {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
  (Continuous f ↔ ∀ A : Set Y, IsOpen A → IsOpen (f ⁻¹' A)) :=
by
  constructor
  -- 連続性から逆像が開集合となることを示す
  · intro h_cont A hA
    exact continuous_def.mp h_cont A hA
  -- 逆像が開集合であることから連続性を示す
  · intro h_preimage
    apply continuous_def.mpr
    exact h_preimage
