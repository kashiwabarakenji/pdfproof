import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real
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
