import LeanCopilot
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs
import Mathlib.Order.Lattice

-- 一般的なLattice αを仮定
variable {α : Type*} [Lattice α]

--練習問題 3
-- 1. x ∧ y ≤ x の証明
theorem my_inf_le_left (x y : α) : x ⊓ y ≤ x :=
by
  simp_all only [inf_le_left] --定理を適用しただけ

-- 2. x ≤ x ∨ y の証明
theorem my_le_sup_left (x y : α) : x ≤ x ⊔ y :=
by
  simp_all only [le_sup_left] --定理を適用しただけ

-- (x ≥ z ∧ y ≥ z) ↔ z ≤ x ⊓ y の証明
theorem le_inf_iff_ge {α : Type*} [Lattice α] (x y z : α) : (x ≥ z ∧ y ≥ z) ↔ z ≤ x ⊓ y :=
by
  -- 両方向に分ける
  constructor
  -- (x ≥ z ∧ y ≥ z) → z ≤ x ⊓ y の証明
  · intro h
    exact le_inf h.1 h.2
  -- z ≤ x ⊓ y → (x ≥ z ∧ y ≥ z) の証明
  · intro h
    constructor
    simp_all only [le_inf_iff, ge_iff_le]
    simp_all only [le_inf_iff, ge_iff_le]

-- z ≥ x ⊔ y ↔ (z ≥ x ∧ z ≥ y) の証明
theorem sup_le_iff_ge {α : Type*} [Lattice α] (x y z : α) : (z ≥ x ⊔ y) ↔ (z ≥ x ∧ z ≥ y) :=
by
  -- 両方向に分ける
  constructor
  -- z ≥ x ⊔ y → (z ≥ x ∧ z ≥ y) の証明
  · intro h
    constructor
    · exact le_sup_left.trans h
    · exact le_sup_right.trans h
  -- (z ≥ x ∧ z ≥ y) → z ≥ x ⊔ y の証明
  · intro h
    exact sup_le h.1 h.2

-- 練習問題 4

-- A ∪ B が A と B の最小上界であることを示す
theorem union_is_lub {α : Type*} (A B : Set α) :
  ∀ C : Set α, (A ⊆ C ∧ B ⊆ C) ↔ A ∪ B ⊆ C :=
by
  intro C
  constructor
  -- (A ⊆ C ∧ B ⊆ C) → A ∪ B ⊆ C
  · intro h
    apply Set.union_subset h.1 h.2
  -- A ∪ B ⊆ C → (A ⊆ C ∧ B ⊆ C)
  · intro h
    constructor
    · exact Set.subset_union_left.trans h
    · exact Set.subset_union_right.trans h

-- A ∩ B が A と B の最大下界であることを示す
theorem inter_is_glb {α : Type*} (A B : Set α) :
  ∀ D : Set α, (D ⊆ A ∧ D ⊆ B) ↔ D ⊆ A ∩ B :=
by
  intro D
  constructor
  -- (D ⊆ A ∧ D ⊆ B) → D ⊆ A ∩ B
  · intro h
    apply Set.subset_inter h.1 h.2
  -- D ⊆ A ∩ B → (D ⊆ A ∧ D ⊆ B)
  · intro h
    constructor
    simp_all only [Set.subset_inter_iff]
    simp_all only [Set.subset_inter_iff]

-- 練習問題 5
-- x以上かつ、y以上の自然集全体の最小なものが、xとyの最小公倍数であることを示す。
-- 自然数 x と y の最小公倍数が、x以上かつy以上の自然数全体の最小のものであることを証明
theorem lcm_is_least_upper_bound (x y : ℕ) :
  (x ∣ Nat.lcm x y ∧ y ∣ Nat.lcm x y) ∧ ∀ n, (x ∣ n ∧ y ∣ n) → Nat.lcm x y ∣ n := by
  -- 定理の左部分 (x ∣ lcm x y ∧ y ∣ lcm x y) を証明
  constructor
  · -- x ∣ lcm x y ∧ y ∣ lcm x y を証明
    exact ⟨Nat.dvd_lcm_left x y, Nat.dvd_lcm_right x y⟩
  -- 定理の右部分 ∀ n, (x ∣ n ∧ y ∣ n) → lcm x y ∣ n を証明
  · intro n hn
  -- hn は (x ∣ n ∧ y ∣ n) である
  -- これにより lcm x y ∣ n を証明
    exact Nat.lcm_dvd hn.1 hn.2

-- 交わり (最大公約数) が最大下界であることの証明
theorem gcd_is_greatest_lower_bound (x y : ℕ) :
  (Nat.gcd x y ∣ x ∧ Nat.gcd x y ∣ y) ∧ ∀ d, (d ∣ x ∧ d ∣ y) → d ∣ Nat.gcd x y :=
by
  constructor
  -- 最大公約数が下界であることを示す
  · exact ⟨Nat.gcd_dvd_left x y, Nat.gcd_dvd_right x y⟩
  -- 任意の下界 d に対して、最大公約数が d を割り切ることを示す
  · intro d hd
    exact Nat.dvd_gcd hd.1 hd.2

-- 新しい型 `Divides` の定義
structure Divides where
  val : ℕ
  deriving Repr, BEq

-- Define extensionality for Divides
theorem Divides.ext {a b : Divides} (h : a.val = b.val) : a = b :=
  by cases a; cases b; congr;

-- `Divides` 型と自然数との間の暗黙の変換を定義
instance : Coe Divides ℕ where
  coe := Divides.val

-- 自然数から `Divides` 型への暗黙の変換を定義
instance : Coe ℕ Divides where
  coe := Divides.mk

-- `Divides` 型に対する `PartialOrder` インスタンスの定義
instance : PartialOrder Divides where
  le a b := a.val ∣ b.val
  le_refl a := Nat.dvd_refl a.val
  le_trans a b c hab hbc := Nat.dvd_trans hab hbc
  le_antisymm a b hab hba := by
    apply Divides.ext
    exact Nat.dvd_antisymm hab hba
