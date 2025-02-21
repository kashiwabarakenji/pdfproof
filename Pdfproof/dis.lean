import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
--import Mathlib.MeasureTheory.MeasureSpace
--import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Monotone
--import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
--import Mathlib.Analysis.NormedSpace.LpSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
--import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.SetIntegral
--import Mathlib.Analysis.Minkowski
import LeanCopilot
--import MeasureTheory.Integral.SetIntegral

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
  (_ : c ≥ 0)
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
  (_ : c ≥ 0)
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
def MyEuclideanSpace (n : ℕ) := Fin n → ℝ
axiom n_pos {n : ℕ} : n > 0

lemma univ_nonempty {n : ℕ} : (Finset.univ : Finset (Fin n)).Nonempty :=
  Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp n_pos)
-- 距離関数 d' の定義
def d' {n : ℕ} (x y : MyEuclideanSpace n) : ℝ :=
    if h : n > 0 then (Finset.univ : Finset (Fin n)).sup' (by
    simp_all only [gt_iff_lt]
    rw [Finset.univ_nonempty_iff]
    cases n
    · simp_all only [lt_self_iff_false]
    · simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
      infer_instance) (λ i => |x i - y i|) else 0

-- 非負性の証明
lemma d'_nonneg {n : ℕ} (x y : MyEuclideanSpace n) : 0 ≤ d' x y :=
  by
    unfold d'
    by_cases h : n > 0
    · simp_all only [gt_iff_lt, ↓reduceDIte, Finset.le_sup'_iff, Finset.mem_univ, abs_nonneg, and_self]
      apply Exists.intro
      · simp_all only
      · use 0
    · simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, lt_self_iff_false, ↓reduceDIte, le_refl]

-- 同一性の証明 nが1以上である仮定が必要か。
lemma d'_eq_zero {n : ℕ} (x y : MyEuclideanSpace n) : d' x y = 0 ↔ x = y := by
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
lemma d'_symm {n : ℕ} (x y : MyEuclideanSpace n) : d' x y = d' y x :=
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
lemma d'_triangle {n : ℕ} (x y z : MyEuclideanSpace n) : d' x z ≤ d' x y + d' y z :=
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
instance EuclideanSpace_metric {n : ℕ} : MetricSpace (MyEuclideanSpace n) :=
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

----非空性

--定義域の非空性
lemma nonemptyIc: Nonempty Ic:= by
  simp_all only [nonempty_subtype]
  use 1
  simp [Ic]

--値域の非空性
lemma nonemptyRange (f:Ic→Real): (f '' (Set.univ:Set Ic)).Nonempty:= by
    simp_all only [Set.image_univ, Set.mem_univ]
    use (f ⟨0, by simp [Ic]⟩)
    simp_all only [Set.Icc.mk_zero, Set.mem_range, exists_apply_eq_apply]

----有界性

--rangeが有界であることを示す。使っている。
lemma bdd_above_range {fs :  Ic → ℝ} (hf2 : Continuous fs):
  BddAbove (Set.range fs) := by
    let Ic := Set.Icc (0:Real) 1
    have isCompact_Icc_s: IsCompact (Set.univ : Set Ic) := by
      simp_all only [Ic]
      exact isCompact_univ

    obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ fs '' Set.univ, y ≤ M :=
      IsCompact.bddAbove (IsCompact.image isCompact_Icc_s hf2)

    use M
    -- y が f の像に属する場合に上界を確認
    intros y hy
    apply hM y
    simp_all

--上の補題と、形が Set.rangeかf '' (Set.univ : Set Ic)の違いだけ。
lemma bdd_above_range2 {fs :  Ic → ℝ} (hf2 : Continuous fs):
  BddAbove (fs '' (Set.univ : Set Ic)) := by
    rw [Set.image_univ]
    exact bdd_above_range hf2

--値域のBddAboveを使いやすい形に変換。
lemma bdd_modify {f: Ic → ℝ} (bdd_g:BddAbove (f '' Set.univ)):BddAbove (Set.range (λ x => ⨆ (_ : x ∈ Set.univ), f x)):= by
   simp_all only [Set.image_univ, Set.mem_univ, ciSup_unique]

----閉集合であること

--rangeが閉集合であること。supr_existsでつかっている。
lemma range_closed
  {fs : Ic → ℝ}
  (hf : Continuous fs ) :
  --IsOpen ((fs '' (Set.univ : Set Ic))ᶜ) := by
  IsClosed ((fs '' (Set.univ : Set Ic))) := by
  rw [←isOpen_compl_iff]

  have compact_Icc_s: IsCompact (Set.univ : Set Ic) := by
    simp_all only [Ic]
    exact isCompact_univ

  have compact_image : IsCompact (fs '' (Set.univ:Set Ic)) := by
    simp_all only [Set.image_univ]
    have compact_Icc_s := compact_Icc_s
    simp_all only
    simpa using compact_Icc_s.image hf

  -- f の像 f '' [a, b] がコンパクトであることを確認

  -- 実数空間ではコンパクト集合は閉集合であるため、f '' [a, b] は閉集合
  have closed_image : IsClosed (fs '' Set.univ) := by
    simp_all only [Set.image_univ]
    exact compact_image.isClosed

  simp_all only [Set.image_univ, isOpen_compl_iff]

----重要な補題たち

--Icを考えない値域だけの議論。
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

--最大値をとる点が存在すること。重要な補題。
lemma supr_exists {f : Ic → ℝ}
  (hf : Continuous f) :
  ∃ x : (Set.univ:Set Ic), f x = sSup (f '' (Set.univ:Set Ic)):= by
  obtain ⟨y0, h0, h1⟩ := bounded_closed_set_has_maximum (f '' (Set.univ:Set Ic)) (bdd_above_range2 hf) (range_closed hf) (nonemptyRange f)
  obtain ⟨x0, hx⟩ := h0
  obtain ⟨hy, hh⟩ := hx
  have lem: y0 = sSup (f '' Set.univ) := by
    rw [←hh]
    apply le_antisymm
    · have assum_lem: f x0 ∈ f '' Set.univ := by
        subst hh
        simp_all only [Set.mem_univ, Set.image_univ, Set.mem_range, Subtype.exists, forall_exists_index,
          exists_apply_eq_apply]
      apply le_csSup (bdd_above_range2 hf) assum_lem
    · --
      have upperb:f x0 ∈ upperBounds (f '' (Set.univ:Set Ic)):= by
        subst hh
        simp_all only [Set.mem_univ, Set.image_univ, Set.mem_range, Subtype.exists, forall_exists_index,
          exists_apply_eq_apply]
        obtain ⟨val, property⟩ := x0
        rintro _ ⟨y, rfl⟩
        obtain ⟨val_1, property_1⟩ := y
        exact h1 _ _ property_1 rfl
      exact csSup_le (nonemptyRange f) upperb
  use ⟨x0, hy⟩
  subst lem
  simp_all only [Set.image_univ, Set.mem_range, Subtype.exists, forall_exists_index]

--set_option pp.all true
--⨆ y ∈ (f '' (Set.univ : Set (Set.Icc (0 : ℝ) 1))), y := byだったが、証明できなかったので、sSupにした。
--supが他の部分よりも値が大きいこと。重要な補題。
lemma sup_lem (x : Ic) (f : Ic → Real) (hf: Continuous f): f x ≤ sSup (f '' (Set.univ:Set Ic)):= by

  have compact_Icc_s: IsCompact (Set.univ : Set Ic) := by
    simp_all only [Ic]
    exact isCompact_univ

  have compact_range_f : IsCompact (f '' (Set.univ:Set Ic)) := by
    simp_all only [Set.image_univ]
    have compact_Icc := compact_Icc_s
    simp_all only
    simpa using compact_Icc.image hf

  have contain_f : f x ∈ f '' Set.univ := by
    simp_all only [Set.mem_image, Set.mem_univ]
    use x

  have bf_bdd : BddAbove (f '' Set.univ) := by
    exact IsCompact.bddAbove compact_range_f

  exact @le_csSup _ _ (f '' (Set.univ:Set Ic)) _ bf_bdd contain_f

--iSupの中に大小が成り立てば、iSupをとっても不等号。
lemma triangle_mono (ff gg : Ic → ℝ)(bdd_g: BddAbove (Set.range (λ x => ⨆ (_ : x ∈ Set.univ), gg x)))  (mono:∀ (x : ↑Ic), ⨆ (_ : x ∈ Set.univ), ff x ≤ ⨆ (_ : x ∈ Set.univ), gg x ):
   ⨆ x ∈ (Set.univ:Set Ic), ff x <= ⨆ x ∈ (Set.univ:Set Ic), gg x := by
  exact ciSup_mono bdd_g mono

lemma triangle_mono2 (ff gg : Ic → ℝ) (bdd:BddAbove (gg '' Set.univ)) (mono:∀ (x : ↑Ic), ff x ≤ gg x ): --(hff : Continuous ff) (hgg : Continuous gg)
   ⨆ x ∈ (Set.univ:Set Ic), ff x ≤ ⨆ x ∈ (Set.univ:Set Ic), gg x := by
   let bdd_g := bdd_modify bdd
   have mono: ∀ (x : ↑Ic), ⨆ (_ : x ∈ Set.univ), ff x ≤ ⨆ (_ : x ∈ Set.univ), gg x := by
     intro x
     simp_all only [Subtype.forall, Set.mem_univ, ciSup_unique]
   exact triangle_mono ff gg bdd_g mono

----ここからメトリックを定義。

def C₀ := ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ

-- 距離関数を定義
noncomputable def supDist (f g : C₀) : ℝ := ⨆ x : Ic, |(f.1 x) - (g.1 x)|

-- メトリック空間のインスタンスを定義。これをなくすとエラーになる。
noncomputable instance : Dist C₀ where
  dist f g := ⨆ x : Set.Icc (0 : ℝ) 1, |(f.1 x) - (g.1 x)|

noncomputable instance : MetricSpace C₀ where
  dist := supDist

  -- dist(f, f) = 0 を証明
  dist_self f :=
    calc
      dist f f = ⨆ x : Set.Icc 0 1, |f.1 x - f.1 x| := by
        simp only [sub_self, abs_zero]
        simp_all only [Set.mem_Icc,  ciSup_const]
        simp [dist]
          _ = ⨆ x ∈ Ic, 0 := by simp
          _ = 0 := by simp

  -- dist(f, g) = dist(g, f) を証明
  dist_comm f g :=
    calc
      dist f g = ⨆ x : Ic, |f.1 x - g.1 x| := by rfl
      _ = ⨆ x : Ic, |g.1 x - f.1 x| := by
        simp_all only [ContinuousMap.toFun_eq_coe]
        simp only [abs_sub_comm]
      _ = dist g f := rfl

  -- 三角不等式を証明: dist(f, h) ≤ dist(f, g) + dist(g, h)
  dist_triangle f g h := by
    have f_cont: Continuous f.toFun := f.continuous_toFun
    have g_cont: Continuous g.toFun := g.continuous_toFun
    have h_cont: Continuous h.toFun := h.continuous_toFun
    have fg_cont: Continuous (λ x => f.toFun x - g.toFun x) := by
      exact f_cont.sub g_cont
    have gh_cont: Continuous (λ x => g.toFun x - h.toFun x) := by
      exact g_cont.sub h_cont
    have fh_cont: Continuous (λ x => f.toFun x - h.toFun x) := by
      exact f_cont.sub h_cont

    let fgh := fun (x:Ic) => |f.1 x - g.1 x| + |g.1 x - h.1 x|
    have fgh_cont: Continuous (λ x => |f.toFun x - g.toFun x|+|g.toFun x - h.toFun x|) := by
      exact (continuous_abs.comp fg_cont).add (continuous_abs.comp gh_cont)

    have bdd_fg : BddAbove (Set.range (λ x => ⨆ (_ : x ∈ Set.univ), |f.toFun x - g.toFun x|)) := by
      apply bdd_modify
      exact bdd_above_range2 (continuous_abs.comp fg_cont)

    have bdd_gh : BddAbove (Set.range (λ x => ⨆ (_ : x ∈ Set.univ), |g.toFun x - h.toFun x|)) := by
      apply bdd_modify
      exact bdd_above_range2 (continuous_abs.comp gh_cont)

    have bdd_fgh:BddAbove ((fun x => |f.toFun x - g.toFun x| + |g.toFun x - h.toFun x|) '' Set.univ) := by
      exact bdd_above_range2 fgh_cont

    have abs_ineq (a b c:Real) : |a - c| <= |a - b| + |b - c| := by
      calc
          |a - c| = |(a - b) + (b - c)| := by rw [sub_add_sub_cancel]
         _ <= |a - b| + |b - c|  := abs_add (a - b) (b - c)

    have abs_all: ∀ x : Ic, |f.1 x - h.1 x| ≤ |f.1 x - g.1 x| + |g.1 x - h.1 x| := by
      intro x
      exact abs_ineq (f.1 x) (g.1 x) (h.1 x)

    have dist_fh : dist f h = ⨆ x : Ic, |f.1 x - h.1 x| := by rfl
    have dist_fg : dist f g = ⨆ x : Ic, |f.1 x - g.1 x| := by rfl
    have dist_gh : dist g h = ⨆ x : Ic, |g.1 x - h.1 x| := by rfl

    let fg := λ x => |f.1 x - g.1 x|
    have fg_cont: Continuous fg := by
      simp_all only [zero_lt_one, ContinuousMap.toFun_eq_coe, Set.mem_univ, ciSup_unique, Set.image_univ,
        implies_true, fg]
      fun_prop
    have gh_cont: Continuous (λ x => |g.1 x - h.1 x|) := by
      simp_all only [zero_lt_one, ContinuousMap.toFun_eq_coe, Set.mem_univ, ciSup_unique, Set.image_univ,
        implies_true]
      fun_prop
    let gh := λ x => |g.1 x - h.1 x|

    obtain ⟨x_0, h_x0⟩ := supr_exists fgh_cont
    calc
      dist f h = ⨆ x : Ic, |f.1 x - h.1 x| := dist_fh
      _ ≤ ⨆ x : Ic, (|f.1 x - g.1 x| + |g.1 x - h.1 x|) := by
        --let ineq (x :Ic):= abs_ineq (f.1 x) (g.1 x) (h.1 x)
        --goal ⨆ x, |f.toFun x - h.toFun x| ≤ ⨆ x, |f.toFun x - g.toFun x| + |g.toFun x - h.toFun x|
        --#check triangle_mono2 (fun x => |f.1 x - h.1 x|) (fun x => |f.1 x - g.1 x| + |g.1 x - h.1 x|) bdd_fgh abs_all
        --⨆ x ∈ Set.univ, |f.toFun x - h.toFun x| ≤ ⨆ x ∈ Set.univ, |f.toFun x - g.toFun x| + |g.toFun x - h.toFun x|
        convert triangle_mono2 (fun x => |f.1 x - h.1 x|) (fun x => |f.1 x - g.1 x| + |g.1 x - h.1 x|) bdd_fgh abs_all
        simp_all only [zero_lt_one, ContinuousMap.toFun_eq_coe, Set.mem_univ, ciSup_unique, Set.image_univ,
          implies_true]
        simp_all only [zero_lt_one, ContinuousMap.toFun_eq_coe, Set.mem_univ, ciSup_unique, Set.image_univ,
          implies_true]
      _ =  |f.1 x_0.1 - g.1 x_0.1| + |g.1 x_0.1 - h.1 x_0.1| := by
        simp_all only [zero_lt_one, ContinuousMap.toFun_eq_coe, Set.mem_univ, ciSup_unique, Set.image_univ,
          implies_true]
        simp_all only [ContinuousMap.toFun_eq_coe, fg, fgh]
        obtain ⟨val, property⟩ := x_0
        obtain ⟨val, property⟩ := val
        simp_all only
        simp_all only [Set.mem_univ]
        rfl
      _ ≤ (⨆ x : Ic, |f.1 x - g.1 x|) + |g.1 x_0.1 - h.1 x_0.1| := by
        have sup_fg: |f.1 x_0.1 - g.1 x_0.1| ≤ ⨆ x : Ic, |f.1 x - g.1 x| := by
          rw [←@sSup_range Real Ic _ (λ x => |f.1 x - g.1 x|) ]
          let tmp:= sup_lem x_0.1 fg fg_cont
          dsimp [fg] at tmp
          convert tmp
          simp_all only [ContinuousMap.toFun_eq_coe, Set.mem_univ, ciSup_unique, Set.image_univ, implies_true]
          --simp_all only [zero_lt_one, ContinuousMap.toFun_eq_coe, fgh]
          obtain ⟨val, property⟩ := x_0
          obtain ⟨val, property⟩ := val
          simp_all only
          rfl
        exact add_le_add_right sup_fg _

      _ ≤ (⨆ x : Ic, |f.1 x - g.1 x|) + (⨆ x : Ic, |g.1 x - h.1 x|) := by
        have sup_gh: |g.1 x_0.1 - h.1 x_0.1| ≤ ⨆ x : Ic, |g.1 x - h.1 x| := by
          rw [←@sSup_range Real Ic _ (λ x => |g.1 x - h.1 x|) ]
          let tmp:= sup_lem x_0.1 gh gh_cont
          dsimp [gh] at tmp
          convert tmp
          simp_all only [ContinuousMap.toFun_eq_coe, Set.mem_univ, ciSup_unique, Set.image_univ, implies_true]
          obtain ⟨val, property⟩ := x_0
          obtain ⟨val, property⟩ := val
          simp_all only
          rfl
        exact add_le_add_left sup_gh _
      _ = dist f g + dist g h := by rw [dist_fg, dist_gh]

  -- ∀ {x y : α}, dist x y = 0 → x = y
  eq_of_dist_eq_zero := by
    have dist0 : ∀ {f g : C₀}, dist f g = 0 → f = g := by
      intros f g h
      dsimp [dist] at h
      have sup_zero_implies_all_zero (fz  : C₀) (h_nonneg : ∀ x:Ic, 0 ≤ fz.1 x) :
       (⨆ x, fz.1 x) = 0 → ∀ x, fz.1 x = 0 := by
          intro h_sup x
          -- f(x) ≥ 0 より、上限は f(x) を超えない
          have h_le : fz.1 x ≤ ⨆ x, fz.1 x := by exact le_ciSup (bdd_above_range fz.2) x
          have nonempty_Ic : Nonempty Ic := ⟨⟨0, by simp [Ic]⟩⟩
          -- 上限が 0 なので、 f(x) ≤ 0
          rw [h_sup] at h_le
          have h_eq : fz.1 x = 0 := by
            apply le_antisymm
            · exact h_le
            · exact h_nonneg x
          exact h_eq
      have cont: Continuous (λ x => |f.1 x - g.1 x|) := by
        exact continuous_abs.comp (f.continuous_toFun.sub g.continuous_toFun)
      have h_eq : ∀ x, |f.1 x - g.1 x| = 0 := sup_zero_implies_all_zero ⟨λ x => |f.1 x - g.1 x|,cont⟩ (λ x => abs_nonneg (f.1 x - g.1 x)) h
      have h_eq2 : ∀ x, f.1 x = g.1 x := by
        intro x
        let h_eq_x := h_eq x
        rw [@abs_eq_zero _ _ _ _ (f.1 x - g.1 x) _] at h_eq_x
        exact sub_eq_zero.mp h_eq_x

      convert h_eq2
      apply Iff.intro
      · intro a x
        subst a
        simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Set.mem_Icc, sub_self, abs_zero, ciSup_const,
          implies_true]
      · intro a
        apply ContinuousMap.ext
        exact a
    intro x y a
    simp_all only
    simpa [supDist, a] using dist0 a

---練習5の証明に使ってないもの。証明に使わなかったもの。

--fが出てこない一般論。
--lemma eq_sup2 {A : Set ℝ} (hBdd : BddAbove A) (hClosed : IsClosed A) (non: A.Nonempty): sSup A = ⨆ z ∈ A, z := by

--有界で閉のAの上限がAに属すること。
lemma bf_subset3 {A:Set Real} (h3_closed: IsClosed A)(b3_bdd:BddAbove A)(b3_nonempty:A.Nonempty ) : sSup A ∈ A := by
  exact IsClosed.csSup_mem h3_closed b3_nonempty b3_bdd

--一般論での包含関係とsupの上限の関係。
lemma bdd_subset {A B : Set ℝ} (hB_subset_A : B ⊆ A) (hA_bdd : BddAbove A) : BddAbove B := by
    -- `A` が上に有界であることから、上界 `M` を得る
    obtain ⟨M, hM⟩ := hA_bdd
    -- `M` を `B` の上界として使用
    use M
    intros x hx
    -- `B ⊆ A` なので `x ∈ A` も成り立つ
    exact hM (hB_subset_A hx)

--indexが有限の場合
lemma sSup_mono {α : Type*} [CompleteLattice α] (f g : ℕ → α) (h : ∀ i, f i ≤ g i) :
  sSup (Set.range f) ≤ sSup (Set.range g) := by
  rw [← iSup, ← iSup] -- `sSup` を `iSup` に変換
  apply iSup_mono
  exact h

--alphaを実数全体にすると、有界性がなくなり、completelatticeにならない。よって使ってない。
lemma sSup_mono_cont {α β: Type*} [CompleteLattice α] (f g : β → α) (h : ∀ i:β, f i ≤ g i) :
  sSup (Set.range f) ≤ sSup (Set.range g) := by
  rw [← iSup, ← iSup] -- `sSup` を `iSup` に変換
  apply iSup_mono
  exact h

--今は証明に使ってないが使える可能性がある。トポロジカルな一般論。
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

--Bornology.IsBoundedのほうの有界性。使ってない。定義域をIcに合わせていない。
lemma cont_bounded {a b : ℝ}
  {f : ℝ → ℝ}
  (hf : ContinuousOn f (Set.Icc a b)):
  let s := Set.Icc a b
  let fs : s → ℝ := λ x => f x.val
  @Bornology.IsBounded Real _ ((Set.image fs (Set.univ : Set s)):Set Real) :=
  by

    have f_continuous : ContinuousOn f (Set.Icc a b) := hf
    let s := Set.Icc a b
    let fs : s → ℝ := λ x => f x.val
    let bdd_s : @Bornology.IsBounded Real _ ((fs '' (Set.univ:Set s)):Set Real) := by
      have fs_continuous : Continuous fs := continuousOn_iff_continuous_restrict.mp f_continuous
      have compact_Icc_s: IsCompact (Set.univ : Set s) := isCompact_univ

      have compact_image2 : IsCompact ((fs '' Set.univ):Set Real) := by
        exact IsCompact.image compact_Icc_s fs_continuous

      have bdd: @Bornology.IsBounded Real _ (fs '' (Set.univ:Set s):Set Real) := by

        let tmp:= IsCompact.isBounded compact_image2
        exact tmp
      exact bdd
    exact bdd_s
---

--練習 6。とりあえず、保留。時間ができたら後日、取り組んでみる。2025 2 21。
--とりあえず、sorryでうめた。
--距離空間になるための。

open MeasureTheory

--前の問題で定義したのが残っている。
--def C₀ := ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ
--def Ic := Set.Icc (0:Real) 1

/--
任意の連続関数 `f` が非負かつ積分が 0 のとき，`f` が恒等的に 0 となることを示す補題．
この補題は Lean 4 で標準的に存在しないため，自前で証明する．
-/

noncomputable instance : MeasureSpace ℝ := Real.measureSpace
--noncomputable instance : MeasureSpace Ic := sorry  --これは定義する必要があるのか。

noncomputable def extend_f (f : C₀) : ℝ → ℝ :=
  Function.extend Subtype.val f.1 0

--積分の変数は、Icでなくて、Rである必要がある。しかし、fの引数は、Icである必要がある。
--xがRの要素であるが、Icの範囲に入っていることをLean 4に伝えられないので、extend_fで回避。
lemma continuous_nonneg_eq_zero_of_integral_zero {f : C₀} (hf_nonneg : ∀ x, 0 ≤ f.1 x)
    (hf_int_zero : ∫ x in (Set.Icc 0 1), (extend_f f) x = 0):
    ∀ x ∈ Set.Icc 0 1, f.1 x = 0 :=
by
  sorry -- なにかMathlib 4の定理を使えないか。ChatGPTに提案してもらった証明はうまりそうになかった。

/-
\( (f-g)^2 \) が `[0,1]` 上可積分であることを示す．Lean 4 では
`ContinuousOn.integrableOn_isCompact isCompact_Icc measurableSet_Icc`
を用いる．
-/
--lemma integrable_sq_diff (hf_cont : ContinuousOn f (Set.Icc 0 1)) (hg_cont : ContinuousOn g (Set.Icc 0 1)) :
--  Integrable (fun x => (f x - g x) ^ 2) (MeasureTheory.Measure.restrict volume (Set.Icc (0 : ℝ) 1)) := by
--sorry

/-- \((a - b)^2\) と \((b - a)^2\) は等しい．使わないかも。-/
lemma sq_diff_comm (a b : ℝ) : (a - b) ^ 2 = (b - a) ^ 2 := by
  -- 好みで rw していっても良いが simp [sub_eq_neg_add] などでも同様の結果が出る．
  rw [pow_two, pow_two, mul_sub, sub_mul, mul_comm]
  ring

/--
\(\int_0^1 (f x)^2 dx = 0\) のとき，\(f\) は `[0,1]` 上恒等的に 0 であることを示す．
Mathlib 3 の `Continuous.ae_eq_zero_of_integral_eq_zero` 相当の議論を
`continuous_nonneg_eq_zero_of_integral_zero` を使って置き換える．
-/

lemma continuous_sq_eq_zero_of_integral_zero {f : C₀}
    --(hf_cont : ContinuousOn f (Set.Icc 0 1))
    (h : ∫ x in Set.Icc (0 : ℝ) 1, (extend_f f x) ^ 2 = 0) :
    ∀ x ∈ Set.Icc 0 1, f.1 x = 0 := by
  -- (f x) ^ 2 は常に非負
  have hf_nonneg : ∀ x, 0 ≤ (f.1 x) ^ 2 := by
    intro x
    exact pow_two_nonneg (f.1 x)
  -- 積分が 0 なので、(f x) ^ 2 = 0
  have hf_eq_zero : ∀ x ∈ Set.Icc 0 1, (f.1 x) ^ 2 = 0 := by
    have hf_sq_cont : ContinuousOn (fun x => (f.1 x) ^ 2) (Set.Icc 0 1) := by
      simp_all
      fun_prop
    show ∀ x ∈ Set.Icc 0 1, f.toFun x ^ 2 = 0
    let f2 := fun x => f.toFun x ^ 2
    have f2inC : Continuous f2:=
    by
      simp_all [f2]
      fun_prop

    have : ∀ x, f2 x ≥ 0 :=
    by
      intro x
      simp_all [f2]
      obtain ⟨val, property⟩ := x
      positivity
    have :∀ (x : ↑(Set.Icc 0 1)), 0 ≤ (⟨f2,f2inC⟩ : C₀).toFun x :=
    by
      intro x
      dsimp [f2]
      obtain ⟨val, property⟩ := x
      positivity

    let cne := continuous_nonneg_eq_zero_of_integral_zero this
    simp at cne
    have : ∫ (x : ℝ) in Set.Icc 0 1, extend_f f x ^ 2 = 0 ↔ ∫ (x : ℝ) in Set.Icc 0 1, extend_f { toFun := f2, continuous_toFun := f2inC } x = 0 :=
    by
      apply Iff.intro
      · dsimp [extend_f]
        dsimp [f2]
        have :∀ x:ℝ,Function.extend Subtype.val (f.1) 0 x ^ 2 = Function.extend Subtype.val (fun x ↦ f.1 x ^ 2) 0 x :=
        by
          intro x
          simp
          sorry --なりたたないという話もある。ひだりは、適用してから2乗しているのか。
          --Function.extendについて調べる必要あり。
        sorry
      · sorry
    rw [this] at h
    specialize cne h
    simp
    dsimp [f2] at cne
    sorry --なんか間違っている。ゴールが一致しないので、もう一度、考え方を見直す。
    --exact cne

  -- (f x) ^ 2 = 0 ならば f x = 0
  intro x hx
  specialize hf_eq_zero x hx
  exact pow_eq_zero hf_eq_zero

/-- \(\displaystyle L^2\) 距離を連続関数上で定義する． -/
noncomputable def L2_distance (f g : C₀) : ℝ :=
  Real.sqrt (∫ x in Set.Icc (0 : ℝ) 1, (extend_f f x - extend_f g x) ^ 2)

/--
上で定義した `L2_distance` が，実際に `MetricSpace` の公理を満たすことの証明．
Minkowski の不等式を使う部分は省略しており，`sorry` を入れている．
-/
-- ContinuousMap subtraction
instance : Sub C₀ where
  sub f g := ⟨λ x => f.1 x - g.1 x, f.continuous_toFun.sub g.continuous_toFun⟩

--距離空間の公理を満たすためには、定義域を[0,1]に制限する必要がある。
noncomputable instance : MetricSpace C₀ where
  dist := by
   exact L2_distance

  dist_self f := by
    simp_all only
    simp [L2_distance]
    -- (f x - f x)^2 = 0 の積分
    --have : ∫ x in Set.Icc 0 1, (f x - f x) ^ 2 = ∫ x in Set.Icc 0 1, (0 : ℝ) := by simp
    --rw [this, integral_zero, Real.sqrt_zero]

  dist_comm f g := by
    simp [L2_distance]
    congr 1
    --funext x
    --exact sq_diff_comm (f x) (g x)
    congr
    ext x : 1
    ring

  dist_triangle f g h := by
    -- 本来は (f - h)^2 <= (f - g + g - h)^2 を用いて Minkowski の不等式を示す必要がある
    -- ここでは省略し、sorry で示す.
    --intro
    simp [L2_distance]
    show √(∫ (x : ℝ) in Set.Icc 0 1, (extend_f f x - extend_f h x) ^ 2) ≤
  √(∫ (x : ℝ) in Set.Icc 0 1, (extend_f f x - extend_f g x) ^ 2) +
    √(∫ (x : ℝ) in Set.Icc 0 1, (extend_f g x - extend_f h x) ^ 2)
    sorry --なんか証明が大変そう。

  eq_of_dist_eq_zero := by
    intro f g hfg
    simp [L2_distance, Real.sqrt_eq_zero] at hfg
    dsimp [C₀]
    ext x
    show f.1 x = g.1 x
    have h_integral_zero : ∫ x in Set.Icc 0 1, (extend_f (f - g)) x ^ 2 = 0 := by
      simp [extend_f, Function.extend_def]
      rw [←Real.sqrt_eq_zero] --ゴールがふたつに分かれる。
      · --show √(∫ (x : ℝ) in Set.Icc 0 1, Function.extend Subtype.val (⇑(f - g)) 0 x ^ 2) = 0
        sorry --うまくいかない。
      · obtain ⟨val, property⟩ := x
        simp_all only [Set.mem_Icc]
        obtain ⟨left, right⟩ := property
        positivity

    have h_eq : ∀ x ∈ Set.Icc 0 1, (f - g).toFun x = 0 := continuous_sq_eq_zero_of_integral_zero h_integral_zero
    specialize h_eq x
    have : x ∈ Set.Icc 0 1:=
    by
      simp_all only [Set.mem_Icc, zero_le', true_and, ContinuousMap.toFun_eq_coe]
      obtain ⟨val, property⟩ := x
      simpa using property.2
    specialize h_eq this
    simp_all only [Set.mem_Icc, zero_le', true_and, ContinuousMap.toFun_eq_coe]
    obtain ⟨val, property⟩ := x
    exact sub_eq_zero.mp h_eq

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
      rw [div_lt_iff₀]
      on_goal 5 => {rw [mul_comm]
      }
      · simp_all only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, Nat.ceil_eq_zero, inv_nonpos, not_le,
          IsUnit.inv_mul_cancel]
        apply Int.fract_lt_one
      · simp_all only [Nat.cast_pos, Nat.ceil_pos, inv_pos]
    _ ≤ ε := by
      rw [one_div]
      simp_all only [gt_iff_lt, one_div, Nat.ceil_pos, inv_pos, n]
      rw [inv_le_comm₀]
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
