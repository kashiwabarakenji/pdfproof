import LeanCopilot
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
--import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
--import Mathlib.Order.Defs
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
----------
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

------------------
------練習6--------
------------------


-- ℝ^2 の上の順序の定義: (x1, y1) >= (x2, y2) ⇔ x1 >= x2 かつ y1 >= y2
structure R2 : Type where
  (x : ℝ)
  (y : ℝ)

namespace R2

instance : PartialOrder R2 where
  le a b := a.x ≤ b.x ∧ a.y ≤ b.y
  le_refl a := ⟨le_refl a.x, le_refl a.y⟩
  le_trans a b c hab hbc := ⟨le_trans hab.1 hbc.1, le_trans hab.2 hbc.2⟩
  le_antisymm a b hab hba := by
    have hx : a.x = b.x := le_antisymm hab.1 hba.1
    have hy : a.y = b.y := le_antisymm hab.2 hba.2
    simp_all only [le_refl, and_self]
    cases a
    simp_all only

-- 上限 (sup) と下限 (inf) の定義
noncomputable instance : Lattice R2 where
  sup a b := ⟨max a.x b.x, max a.y b.y⟩
  le_sup_left a b := ⟨le_max_left a.x b.x, le_max_left a.y b.y⟩
  le_sup_right a b := ⟨le_max_right a.x b.x, le_max_right a.y b.y⟩
  sup_le _ _ _ hac hbc := ⟨max_le hac.1 hbc.1, max_le hac.2 hbc.2⟩
  inf a b := ⟨min a.x b.x, min a.y b.y⟩
  inf_le_left a b := ⟨min_le_left a.x b.x, min_le_left a.y b.y⟩
  inf_le_right a b := ⟨min_le_right a.x b.x, min_le_right a.y b.y⟩
  le_inf _ _ _ hab hac := ⟨le_min hab.1 hac.1, le_min hab.2 hac.2⟩

end R2

------------------
-----練習7 --------
------------------

variable {α : Type} [Lattice α]

-- 冪等性: x ⊓ x = x, x ⊔ x = x
theorem meet_idempotent (x : α) : x ⊓ x = x := by
  rw [inf_idem]

theorem join_idempotent (x : α) : x ⊔ x = x := by
  rw [sup_idem]

-- 交換律: x ⊓ y = y ⊓ x, x ⊔ y = y ⊔ x
theorem meet_comm (x y : α) : x ⊓ y = y ⊓ x := by
  rw [inf_comm]

theorem join_comm (x y : α) : x ⊔ y = y ⊔ x := by
  rw [sup_comm]

-- 結合律: x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z
theorem meet_assoc (x y z : α) : x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z := by
  rw [inf_assoc]

theorem join_assoc (x y z : α) : x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by
  rw [sup_assoc]

-- 吸収律: x ⊓ (y ⊔ x) = x, x ⊔ (x ⊓ y) = x
theorem meet_absorption (x y : α) : x ⊓ (y ⊔ x) = x := by
  simp_all only [le_sup_right, inf_of_le_left]

theorem join_absorption (x y : α) : x ⊔ (x ⊓ y) = x := by
  rw [sup_inf_self]

------------------
-----練習10--------
------------------

--束に対して、
-- meet distributive law
-- a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)
-- join distributive law
-- a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)
--が同値であることを証明する問題。
--式変形で証明するのは難しい。双対性より成り立つというよくある証明も間違っていると思われる。
--禁止部分束を利用するのが簡単に証明できると思われる。
--meet distributive lawが成り立たないとすると、
--a ⊓ (b ⊔ c) > (a ⊓ b) ⊔ (a ⊓ c) となる。この2元とbかcは比べられないので、
--これらをすべてjoinしたa ⊔ b ⊔ c と、a ⊓ b ⊓ cを加えて、5元を考える。
--これらの5元が全て異なる場合は、N5と呼ばれる部分束になり、
-- X = a ⊓ (b ⊔ c), Y = (a ⊓ b) ⊔ (a ⊓ c), Z = bとすると、計算により、
--X ⊔ (Y ⊓ Z)=Xと
--(X ⊔ Y) ⊓ (X ⊔ Z)=Yが成り立ち、XとYが異なるので、join distributive lawが成り立たない。
--5元のどれかが一致する場合は、M3という部分束になり、やはりjoin distributive lawが成り立たない。
--以下のlean 4で証明は、作成するのに2日かかった。

lemma meet_distributive_law_iff_join_distributive_law
  (α : Type) [Lattice α] :
  (∀ a b c : α, a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) ) →
  (∀ a b c : α, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c))
    :=
by
  contrapose
  intro h_forall
  push_neg at h_forall
  --apply not_forall.mp at h
  obtain ⟨a, b, c, h_exist⟩ := h_forall
  intro h
  let X := a ⊓ (b ⊔ c)
  let Y := (a ⊓ b) ⊔ (a ⊓ c)
  have h_existXY: X ≠ Y := by
    intro h_eq
    apply h_exist
    exact h_eq
  let Zb := b
  --XとYが一致することを示せば、矛盾が生じる。

  have h0: a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c) := by
    apply ge_iff_le.mp
    exact le_inf_sup

  --h1の証明にh0を利用している。Xのほうが自明に大きい。この命題も証明には使ってない。
  have h1 : X >= Y := by
    simp_all only [X,Y]

  --使ってないように見えて、コメントアウトするとエラーになる。
  have h3: Y ⊔ Zb >= X := by
    dsimp [X, Y, Zb]
    simp_all
    --goal a ⊓ (b ⊔ c) ≤ a ⊓ (a ⊓ b ⊔ c) ⊔ b
    conv =>
      rhs
      rw [sup_comm]
    rw [h b a ((a ⊓ b ⊔ c))]
    --goal  a ⊓ (b ⊔ c) ≤ (b ⊔ a) ⊓ (b ⊔ (a ⊓ b ⊔ c))
    have h3_lem: a <= b ⊔ a := by
      exact le_sup_right
    have h3_lem2: (b ⊔ c) <= (b ⊔ (a ⊓ b ⊔ c)) := by
      simp_all only [inf_le_left, sup_of_le_right, le_inf_iff, and_self, le_sup_right, sup_le_iff, le_sup_left,
        true_and, Y, X]
      apply le_sup_of_le_right
      simp_all only [le_sup_right]
    exact inf_le_inf h3_lem h3_lem2


  --M3のケースとN5のケースで場合分け。
  by_cases m3n5: a ⊓ b <= c
  case pos => --N5のケース


    --明示的に引用されてないが、コメントアウトするとエラーになるので、引用されていると思われる。
    have h3_dual: X ⊓ Zb <= Y := by
      dsimp [X, Y, Zb]
      simp_all
      --goal a ⊓ (b ⊔ c) ⊓ b ≤ a   ∧   a ⊓ (b ⊔ c) ⊓ b ≤ a ⊓ b ⊔ c
      symm
      constructor
      rw [inf_assoc]
      rw [inf_comm]
      rw [inf_comm (b ⊔ c) b]
      rw [inf_sup_self]
      rw [inf_comm]
      exact m3n5

      simp_all only [inf_le_left, sup_of_le_right, le_inf_iff, and_self, le_sup_left, inf_of_le_right, Y, X, Zb]
      rw [inf_assoc]
      rw [inf_comm]
      rw [inf_comm (b ⊔ c) b]
      rw [inf_sup_self]
      simp_all only [inf_le_right]


    let left_hand:= Y ⊔ (X ⊓ Zb)
    let right_hand:= (Y ⊔ Zb) ⊓ (Y ⊔ X)
    have left_eq: Y ⊔ (X ⊓ Zb) = Y := by
      simp_all only [inf_le_left, sup_of_le_left, le_refl, le_sup_left, inf_of_le_left, not_true_eq_false, X, Y, Zb]
    have right_eq: (Y ⊔ Zb) ⊓ (Y ⊔ X) = X := by
      simp_all only [inf_le_left, sup_of_le_left, le_refl, le_sup_left, inf_of_le_left, not_true_eq_false, X, Y, Zb]
      simp_all only [inf_le_left, sup_of_le_right, ne_eq, le_inf_iff, true_and, ge_iff_le, inf_of_le_right]
    have h4 : left_hand = right_hand := by
      dsimp [left_hand, right_hand]
      conv =>
        rhs
        rw [inf_comm]
      exact h Y X Zb
    have h5 : X = Y := by
      rw [←left_eq]
      conv =>
        lhs
        rw [←right_eq]
      symm
      dsimp [left_hand,right_hand] at h4
      exact h4
    contradiction

  case neg => --M3のケース　N5と同じように証明できるので場合分けが必要だったか不明。negの条件をどこで使っているのか。

    --h3_dualも使ってないように見えてコメントアウトするとエラーになるので使っていると思われる。
    have h3_dual: X ⊓ Zb <= Y := by
      dsimp [X, Y, Zb]
      simp_all
      --goal a ⊓ (b ⊔ c) ⊓ b ≤ a   ∧   a ⊓ (b ⊔ c) ⊓ b ≤ a ⊓ b ⊔ c
      symm
      constructor
      rw [inf_assoc]
      rw [inf_comm]
      rw [inf_comm (b ⊔ c) b]
      rw [inf_sup_self]
      rw [inf_comm]
      simp_all only [inf_le_left, sup_of_le_right, not_false_eq_true, le_inf_iff, and_self, le_sup_left, X, Y, Zb]

      simp_all only [inf_le_left, sup_of_le_right, le_inf_iff, and_self, le_sup_left, inf_of_le_right, Y, X, Zb]
      rw [inf_assoc]
      rw [inf_comm]
      rw [inf_comm (b ⊔ c) b]
      rw [inf_sup_self]
      simp_all only [inf_le_right]

    let left_hand:= Y ⊔ (X ⊓ Zb)
    let right_hand:= (Y ⊔ Zb) ⊓ (Y ⊔ X)
    have left_eq: Y ⊔ (X ⊓ Zb) = Y := by
      simp_all only [inf_le_left, sup_of_le_left, le_refl, le_sup_left, inf_of_le_left, not_true_eq_false, X, Y, Zb]
    have right_eq: (Y ⊔ Zb) ⊓ (Y ⊔ X) = X := by
      simp_all only [inf_le_left, sup_of_le_left, le_refl, le_sup_left, inf_of_le_left, not_true_eq_false, X, Y, Zb]
      simp_all only [inf_le_left, sup_of_le_right, ne_eq, le_inf_iff, true_and, ge_iff_le, inf_of_le_right]
    have h4 : left_hand = right_hand := by
      dsimp [left_hand, right_hand]
      conv =>
        rhs
        rw [inf_comm]
      exact h Y X Zb
    have h5 : X = Y := by
      rw [←left_eq]
      conv =>
        lhs
        rw [←right_eq]
      symm
      dsimp [left_hand,right_hand] at h4
      exact h4
    contradiction
