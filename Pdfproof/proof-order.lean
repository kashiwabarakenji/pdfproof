import LeanCopilot
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Init.Data.List.OfFn
import Mathlib.Data.List.OfFn
--import Mathlib.Init.Data.Nat.Lemmas
--import Mathlib.Data.Real.Basic
--import Mathlib.Order.Basic
--import Mathlib.Order.Defs
--import Mathlib.Data.List.Basic
--import Init.Data.List.Find
--import Mathlib.Data.List.Defs
--import Mathlib.Data.Fin.Basic
import Init.Data.Fin.Fold
import Init.Data.List.Lemmas

----------------------
-----2項関係と順序------
----------------------

--2項関係と順序　練習1
--variable {X Y : Type}
-- 同値関係を定義します: x ~ y は f(x) = f(y) とする
def rel (f :X → Y) (x y : X) : Prop := f x = f y

--2項関係と順序 練習1
-- 同値関係であることの証明
example : Equivalence (rel f) :=
  ⟨
    -- 反射律: 任意の x に対して、rel f x x が成り立つ
    fun _ => rfl,

    -- 対称律: rel f x y が成り立つなら、rel f y x も成り立つ
    fun {_ _} h => h.symm,

    -- 推移律: rel f x y と rel f y z が成り立つなら、rel f x z も成り立つ
    fun {_ _ _} hxy hyz => hxy.trans hyz
  ⟩

-- intro を使った同値関係の証明 --EquivalenceはInit.Coreに定義。
example : Equivalence (rel f) :=
by
  constructor
  -- 反射律の証明
  -- 任意の x に対して、rel f x x を証明
  · intro a
    exact rfl

  -- 対称律の証明
  · intro x y h
    exact h.symm

  -- 推移律の証明
  · intro x y z hxy hyz
    exact hxy.trans hyz

--------------------
--2項関係と順序　練習２

-- M を α の部分集合の集合として定義
variable (M : Set (Set α))

-- パーティションの条件を定義
def is_partition : Prop :=
  -- 全域性: 任意の x ∈ α に対して、x を含む A ∈ M が存在する
  (∀ x : α, ∃ A ∈ M, x ∈ A) ∧
  -- 互いに素: 異なる A, B ∈ M に対して、A ∩ B = ∅
  (∀ A ∈ M, ∀ B ∈ M, A ≠ B → A ∩ B = ∅)

-- 関係 R を定義: xRy ↔ ∃ A ∈ M, x ∈ A ∧ y ∈ A
def RR (x y : α) : Prop :=
  ∃ A ∈ M, x ∈ A ∧ y ∈ A

-- R が同値関係であることを証明
example (hM : is_partition M) : Equivalence (RR M):=

--structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
--  refl  : ∀ x, r x x
--  symm  : ∀ {x y}, r x y → r y x
--  trans : ∀ {x y z}, r x y → r y z → r x z
-- 同値関係の反射律
{
    refl := fun x =>
      -- 全域性より、x を含む A ∈ M が存在する
      let ⟨A, hA_mem, hx⟩ := hM.1 x
      -- xRx を示す: A ∈ M で x ∈ A かつ x ∈ A
      ⟨A, hA_mem, hx, hx⟩

    -- 同値関係の対称律
    symm := by
      intro x y hxy
      obtain ⟨A, hA_mem, hxA, hyA⟩ := hxy
      -- yRx を示す: 同じ A を用いればよい
      exact ⟨A, hA_mem, hyA, hxA⟩

    -- 同値関係の推移律
    trans := by
      intro x y z hxy hyz
      let ⟨A, hA_mem, hxA, hyA⟩ := hxy
      let ⟨B, hB_mem, hyB, hzB⟩ := hyz
      dsimp [is_partition] at hM
      let hM2 := (hM.2 A hA_mem B hB_mem)

      have hAB : A = B := by
        by_contra hne
        have hABempty : A ∩ B = ∅ := hM2 hne
        have hABnonempty : y ∈ A ∩ B := by
          simp only [Set.mem_inter_iff]
          exact ⟨hyA, hyB⟩
        rw [hABempty] at hABnonempty
        exact Set.not_mem_empty y hABnonempty
      rw [←hAB] at hzB
      dsimp [RR]
      subst hAB --以下はLean Copilotによる証明
      simp_all only
      obtain ⟨left, right⟩ := hM
      apply Exists.intro
      · apply And.intro
        on_goal 2 => apply And.intro
        on_goal 3 => {exact hzB
        }
        · simp_all only
        · simp_all only
}

------------------
--2項関係と順序　練習3
------------------

example {α : Type}
  (X : Set α) (_ : X.Nonempty)
  (R : α → α → Prop) (hR : Equivalence R) :
  (∀ S ∈ { s : Set α | ∃ y ∈ X, s = {x | R x y} }, S.Nonempty) ∧
  (∀ S₁ S₂, S₁ ∈ { s : Set α | ∃ y ∈ X, s = {x | R x y} } → S₂ ∈ { s : Set α | ∃ y ∈ X, s = {x | R x y} } → S₁ ≠ S₂ → S₁ ∩ S₂ = ∅) ∧
  (∀ x ∈ X, ∃ S ∈ { s : Set α | ∃ y ∈ X, s = {x | R x y} }, x ∈ S) :=
by
  constructor
  -- 1. 各部分集合 S ∈ M は非空である
  · intro S hS
    -- SがMの要素であることから、あるy ∈ Xが存在してS = {x | R x y}である
    obtain ⟨y, _, hS_eq⟩ := hS
    -- y自身がSに属するため、Sは非空
    have y_in_S : y ∈ {x | R x y} := hR.refl y
    subst hS_eq
    exact ⟨y, y_in_S⟩

  -- 2. 異なる部分集合 S₁, S₂ ∈ M は互いに素である
  · constructor
    · intro S₁ S₂ hS₁ hS₂ hNeq
      -- S₁とS₂がMの要素であることから、それぞれに対応するy₁, y₂が存在する
      obtain ⟨y₁, _, hS₁_eq⟩ := hS₁
      obtain ⟨y₂, _, hS₂_eq⟩ := hS₂
      -- S₁とS₂をそれぞれの同値類に書き換える
      rw [hS₁_eq, hS₂_eq]
      -- S₁ ∩ S₂ ≠ ∅ ならば同値類が等しいことを示す
      by_contra hne
      have hNonempty : ({x | R x y₁} ∩ {x | R x y₂}).Nonempty := by
        subst hS₂_eq hS₁_eq
        simp_all only [ne_eq]
        rw [Set.nonempty_iff_ne_empty]
        simp_all only [ne_eq, not_false_eq_true]

      obtain ⟨x0, hx⟩ := Set.nonempty_def.mp hNonempty
      obtain ⟨hx1, hx2⟩ := hx
      -- R x y₁ と R x y₂ が成り立つ
      rw [Set.mem_setOf_eq] at hx1 hx2

      have Ry1y2 : R y₁ y₂ := hR.trans ((hR.symm) hx1) hx2

      have hSame : S₁ =  S₂ := by
        apply Set.ext
        intro x
        apply Iff.intro
        · intro h
          rw [hS₁_eq, Set.mem_setOf_eq] at h
          rw [hS₂_eq, Set.mem_setOf_eq]
          exact hR.trans h Ry1y2
        · intro h
          rw [hS₂_eq, Set.mem_setOf_eq] at h
          rw [hS₁_eq, Set.mem_setOf_eq]
          exact hR.trans h (hR.symm Ry1y2)
      exfalso
      subst hSame hS₂_eq
      simp_all only [Set.inter_self, ne_eq, not_true_eq_false]

    -- 3. 全体集合 X が M の部分集合の和集合であることを証明
    · intro x0 a
      simp_all only [Set.mem_setOf_eq]
      --goal  ∃ S, (∃ y ∈ X, S = {x | R x y}) ∧ x0 ∈ S
      apply Exists.intro
      · apply And.intro
        · use x0
        · simp_all only [Set.mem_setOf_eq]
          exact hR.refl x0

/-- 練習3をAIにリファクタリングしてもらったもの。わかりやすくなったかは微妙。
# 同値関係からの分割の証明
非空な集合 `X` 上の同値関係 `R` が与えられたとき、集合 `M` を以下のように定義します。
\[ M = \{ [y] \mid y \in X \} \]
ここで、\([y] = \{ x \in X \mid R(x, y) \}\) は元 `y` に対応する同値類（同値クラス）です。
本定理では、集合 `M` が集合 `X` の分割（パーティション）を形成することを示します。分割の条件は以下の三つです：
1. **非空性:** 各部分集合は非空である。
2. **互いに素:** 異なる部分集合は互いに交わらない。
3. **全体覆い:** 全ての元が少なくとも一つの部分集合に含まれる。
## 定理の宣言
以下の定理 `equivalenceRelationPartition` は、上述の条件を満たすことを証明します。
- `α` : 任意の型。
- `X` : 非空な `α` 型の集合。
- `R` : `α` 型の元同士の同値関係。
- `hR` : `R` が同値関係であることの証明。
-/

theorem equivalenceRelationPartition {α : Type}
  (X : Set α)
  (R : α → α → Prop) (hR : Equivalence R) :
  -- 定義された集合 M が以下の三つの条件を満たすことを示す
  (∀ equivalenceClass ∈ { s : Set α | ∃ y ∈ X, s = {x | R x y} }, equivalenceClass.Nonempty) ∧
  (∀ equivalenceClass₁ equivalenceClass₂,
      equivalenceClass₁ ∈ { s : Set α | ∃ y ∈ X, s = {x | R x y} } →
      equivalenceClass₂ ∈ { s : Set α | ∃ y ∈ X, s = {x | R x y} } →
      equivalenceClass₁ ≠ equivalenceClass₂ → equivalenceClass₁ ∩ equivalenceClass₂ = ∅) ∧
  (∀ x ∈ X, ∃ equivalenceClass ∈ { s : Set α | ∃ y ∈ X, s = {x | R x y} }, x ∈ equivalenceClass) :=
by
  -- 同値類の集合を `equivalenceClasses` として定義
  --have equivalenceClasses : Set (Set α) := { s : Set α | ∃ y ∈ X, s = {x | R x y} }

  constructor
  -- 1. 各同値類は非空であることを証明
  · intro equivalenceClass hEquivalenceClass
    -- `equivalenceClass` が `equivalenceClasses` の要素であることから、ある `y ∈ X` が存在して `equivalenceClass = {x | R x y}` である
    obtain ⟨y, _, hEquivalenceClass_eq⟩ := hEquivalenceClass
    -- 同値関係の反射律より、`y ∈ {x | R x y}` が成り立つ
    have y_in_class : y ∈ {x | R x y} := hR.refl y
    -- `equivalenceClass` を `{x | R x y}` に置き換える
    subst hEquivalenceClass_eq
    -- よって、`{x | R x y}` は `y` を含むため非空である
    exact ⟨y, y_in_class⟩

  -- 2. 異なる同値類は互いに素であることを証明
  · constructor
    · intro equivalenceClass₁ equivalenceClass₂ hEquivalenceClass₁ hEquivalenceClass₂ hClassesDistinct
      -- `equivalenceClass₁` と `equivalenceClass₂` が `equivalenceClasses` の要素であることから、それぞれに対応する `y₁, y₂ ∈ X` が存在する
      obtain ⟨y₁, _, hEquivalenceClass₁_eq⟩ := hEquivalenceClass₁
      obtain ⟨y₂, _, hEquivalenceClass₂_eq⟩ := hEquivalenceClass₂
      -- `equivalenceClass₁` と `equivalenceClass₂` をそれぞれの同値類に書き換える
      rw [hEquivalenceClass₁_eq, hEquivalenceClass₂_eq]
      -- 異なる同値類の交わりが空であることを示すため、仮に交わりが非空とすると矛盾を導く
      by_contra hIntersectionEmpty
      have hNonEmpty : ∃ x, x ∈ {x | R x y₁} ∧ x ∈ {x | R x y₂} := by
        subst hEquivalenceClass₁_eq hEquivalenceClass₂_eq
        simp_all only [ne_eq, Set.mem_setOf_eq]
        contrapose! hIntersectionEmpty
        ext1 x
        simp_all only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_false_eq_true,
          implies_true]
      -- 交わりから `x` が存在し、`R x y₁` と `R x y₂` が成り立つ
      obtain ⟨x₀, hx₁, hx₂⟩ := hNonEmpty
      -- `R x₀ y₁` と `R x₀ y₂` から同値関係の推移律を用いて `R y₁ y₂` を導く
      have hRy1y2 : R y₁ y₂ := hR.trans (hR.symm hx₁) hx₂
      -- `R y₁ y₂` より、同値類は等しいことを示す
      have hSameClasses : {x | R x y₁} = {x | R x y₂} :=
        Set.ext (λ z => ⟨λ h => hR.trans h hRy1y2, λ h => hR.trans h (hR.symm hRy1y2)⟩)
      -- よって、`equivalenceClass₁ = equivalenceClass₂` が成り立つ
      subst hEquivalenceClass₁_eq hEquivalenceClass₂_eq
      simp_all only [Set.inter_self, Set.mem_setOf_eq]

    -- 3. 全体集合 `X` が `equivalenceClasses` の部分集合の和集合であることを証明
    · intro x hxX
      -- 任意の `x ∈ X` に対して、その同値類 `{z | R z x}` を選ぶ
      use { z | R z x }
      -- `{z | R z x}` が `equivalenceClasses` の要素であることを示すために、`x ∈ X` であることを利用
      use ⟨x, hxX, rfl⟩
      -- `x` が `{z | R z x}` に属することを示す
      exact hR.refl x

------------------------
--2項関係と順序 練習4
------------------------

-- 整数全体の集合での同値関係を定義
def equiv_rel (n : ℤ) (x y : ℤ) : Prop :=
  ∃ k : ℤ, x - y = n * k

-- 反射性の証明
theorem my_refl (n : ℤ) : ∀ x : ℤ, equiv_rel n x x :=
by
  intro x
  use 0
  simp_all only [Int.sub_self, Int.mul_zero]

-- 対称性の証明
theorem my_symm (n : ℤ) : ∀ x y : ℤ, equiv_rel n x y → equiv_rel n y x :=
by
  intro x y h
  rcases h with ⟨k, hk⟩
  use -k
  rw [Int.mul_neg, ←hk, Int.sub_eq_add_neg, Int.add_comm]
  omega

-- 推移性の証明
theorem my_trans (n : ℤ) : ∀ x y z : ℤ, equiv_rel n x y → equiv_rel n y z → equiv_rel n x z :=
by
  intro x y z h1 h2
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  use k1 + k2
  calc
    x - z = (x - y) + (y - z) := by simp_all only; omega--rw [←sub_add_sub_cancel x y z]
    _   = n * k1 + n * k2   := by rw [hk1, hk2]
    _   = n * (k1 + k2)     := by rw [Int.mul_add]

-- 同値関係の証明
theorem equiv_is_equiv (n : ℤ) : Equivalence (equiv_rel n) :=
⟨my_refl n, @my_symm n, @my_trans n⟩

--------------------------------

--自然数にはすでにPartialOrderの構造が入っているので
-- PartialOrder Nat としてPartialOrderを定義するとエラーになる。
--#check PartialOrder Nat
-- 自然数をラップする新しい型 MyNat を定義する。
structure MyNat where
  val : Nat
  deriving DecidableEq, Repr
/-
--プリントにはないが自然数における通常の大小関係「小なりイコール」(≤) 関係を定義してみると
instance natPartialOrder : PartialOrder MyNat where
  -- 順序関係として ≤ を設定します。
  le := fun a b => a.val ≤ b.val

  -- 反射律: 任意の自然数 a に対して a ≤ a が成り立つことを示します。
  le_refl := fun a => Nat.le_refl a.val

  -- 推移律: a ≤ b かつ b ≤ c ならば a ≤ c であることを示します。
  le_trans := fun a b c hab hbc => Nat.le_trans hab hbc

  -- 反対称律: a ≤ b かつ b ≤ a ならば a = b であることを示します。
  le_antisymm := fun a b hab hba => congrArg MyNat.mk (Nat.le_antisymm hab hba)

-/

--練習4のinstanceバージョン
--利用する補題
lemma mul_eq_one_of_ge_one {a b : Nat} (h : a * b = 1) : a = 1 ∧ b = 1 := by
  have a_eq_one : a = 1 := by
    cases a
    case zero =>
      simp_all only [Nat.zero_mul, zero_ne_one]
    case succ =>
      cases b
      case zero =>
        simp_all only [Nat.mul_zero, Nat.zero_ne_one]
      case succ =>
        simp_all only [Nat.succ_mul]
        simp_all only [Nat.add_left_eq_self]
        injection h
        rename_i n_eq
        --aesop_unfold at n_eq
        simp_all only [Nat.add_eq, Nat.add_eq_zero_iff]
        obtain ⟨left, right⟩ := n_eq
        subst right
        simp_all only [Nat.zero_add, Nat.mul_one]


  have b_eq_one : b = 1 := by
    subst a_eq_one
    simp_all only [Nat.one_mul]
  -- 結論として、a = 1 かつ b = 1 である
  exact ⟨a_eq_one, b_eq_one⟩

-- Nat から MyNat への変換関数
def ofNat (n : Nat) : MyNat := ⟨n⟩

-- MyNat から Nat への変換関数
def toNat (a : MyNat) : Nat := a.val

-- Nat から MyNat への自動変換を定義します。
instance : Coe Nat MyNat where
  coe := ofNat

-- MyNat に対する割り切る関係を定義します。
def Mydvd (a b : MyNat) : Prop := ∃ k : Nat, b.val = a.val * k

-- MyNat に対する PartialOrder のインスタンスを定義します。
instance myNatPartialOrder : PartialOrder MyNat where
  -- 順序関係として dvd を設定します。
  le := Mydvd

  -- 反射律: 任意の MyNat a に対して a ≤ a が成り立つことを示します。
  le_refl := fun a =>
    ⟨1, (Nat.mul_one a.val).symm⟩

  -- 推移律: a ≤ b かつ b ≤ c ならば a ≤ c であることを示します。
  le_trans := fun a b c hab hbc =>
    match hab, hbc with
    | ⟨k, hk⟩, ⟨l, hl⟩ =>
      ⟨k * l, by
        rw [hl, hk]
        rw [Nat.mul_assoc]
      ⟩

  -- 反対称律: a ≤ b かつ b ≤ a ならば a = b であることを示します。
  le_antisymm := fun a b hab hba =>
    by
      -- hab: ∃ k, b.val = a.val * k
      -- hba: ∃ l, a.val = b.val * l
      obtain ⟨k, hk⟩ := hab
      obtain ⟨l, hl⟩ := hba

      -- b.val = a.val * k かつ a.val = b.val * l から a.val = a.val * k * l
      --rw [hk] at hl

      -- a.val * (k * l) = a.val
      -- ここで、a.val ≠ 0 または a.val = 0 の場合を分ける
      by_cases aval: a.val = 0
      case pos =>
        -- a.val = 0 ならば b.val = 0 も同様
        rw [aval] at hk
        have : b.val = 0 := by
          simp_all only [Nat.zero_mul]
        simp_all only [Nat.zero_mul]
        cases a
        simp_all only
        subst aval
        simp [this.symm]
      case neg =>
        have canc: a.val * (l * k) = a.val := by
            rw [Nat.mul_comm l k]
            rw [←Nat.mul_assoc]
            rw [←hk]
            exact hl.symm
        have canc2: a.val * (l * k) = a.val*1 := by
          simp
          exact canc
        -- a.val > 0 ならば k * l = 1 でなければならない
        have kl_eq_one : k * l = 1 := by
          let natv := (Nat.pos_of_ne_zero aval)
          let natv2 := Nat.eq_of_mul_eq_mul_left natv canc2
          rw [Nat.mul_comm]
          apply natv2

        -- 自然数において k * l = 1 ならば k = 1 かつ l = 1
        have k_eq_one : k = 1 := by
          exact (mul_eq_one_of_ge_one kl_eq_one).1

        have l_eq_one : l = 1 := by
          --rw [k_eq_one] at kl_eq_one
          exact (mul_eq_one_of_ge_one kl_eq_one).2

        -- したがって, b.val = a.val * 1 = a.val
        rw [k_eq_one] at hk
        simp at hk
        exact congrArg MyNat.mk hk.symm

/-
--以下は証明はあっていると思われるが、NにはすでにPartialOrderの構造が入っているので
--PartialOrder Nat のインスタンスとしてPartialOrderを定義するとreflに関するエラーになる。

instance dvdPartialOrder : PartialOrder Nat := by

{
  -- 部分順序の順序関係を dvd に設定します。
  le := dvd

  -- 反射律: 任意の自然数 a に対して a divides a であることを示します。
  le_refl := by
    intro a
    use 1
    rw [Nat.mul_one]

  -- 推移律: a divides b かつ b divides c ならば a divides c であることを示します。
  le_trans := by
    intros a b c hab hbc
    simp_all only
    exact dvd_trans hab hbc

  -- 反対称律: a divides b かつ b divides a ならば a = b であることを示します。
  le_antisymm := by
    intros a b hab hba
    obtain ⟨k, hk⟩ := hab
    obtain ⟨l, hl⟩ := hba
    -- b = a * k かつ a = b * l から a = a * k * l となる
    --rw [hk, hl] at *
    -- よって、a * (k * l) = a
    have h_eq : a * (k * l) = a := by
      rw [←Nat.mul_assoc]
      rw [←hk]
      exact hl.symm
    have h_eq2: a * (k * l) = a*1 := by
      simp
      exact h_eq

    -- a が 0 の場合
    by_cases ha: a = 0
    case pos =>
      -- a = 0 ならば b = 0 である
      subst hl
      simp_all only [zero_mul, mul_one]
    case neg =>
      -- a が正の場合、k * l = 1 でなければならない
      have kl_eq_one : k * l = 1 := by
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) h_eq2

      have k_eq_one: k = 1 := by
        exact (mul_eq_one_of_ge_one kl_eq_one).1

      rw [k_eq_one] at hk
      simp at hk
      exact hk.symm
}

-/
--------------------
--2項関係と順序 練習5--
--------------------

-- X の上の関係を定義
variable {X : Type} (R : X → X → Prop)

-- Q の定義
def Q (x y : X) : Prop := R x y ∨ x = y

-- 関係 R が推移的であること
variable (trans_R : ∀ ⦃x y z : X⦄, R x y → R y z → R x z)

-- 関係 R が反射的でないこと
variable (not_refl_R : ∀ x : X, ¬R x x)

-- 反射性の証明 (Qは反射的)
theorem Q_refl : ∀ x : X, Q R x x :=
by
  intro x
  -- Q の定義によって、x = x が成立するため反射性が成立
  right
  rfl

-- 反対称性の証明 (Qは反対称的)
theorem Q_antisymm (trans_R : ∀ ⦃x y z : X⦄, R x y → R y z → R x z) (not_refl_R : ∀ x : X, ¬R x x) : ∀ {x y : X}, Q R x y → Q R y x → x = y :=
by
  intros x y hxy hyx
  cases hxy with
  | inl rxy =>
    -- xRy が成立する場合
    cases hyx with
    | inl ryx =>
      -- yRx が成立する場合は矛盾
      exfalso

      have := not_refl_R x
      exact this (trans_R rxy ryx)
    | inr rfl =>
      -- y = x が成立する場合は x = y
      subst rfl
      simp_all only
  | inr rfl =>
    -- x = y が成立する場合は x = y
    subst rfl
    simp_all only

-- 推移性の証明 (Qは推移的)
theorem Q_trans (trans_R : ∀ ⦃x y z : X⦄, R x y → R y z → R x z) : ∀ {x y z : X}, Q R x y → Q R y z → Q R x z :=
by
  intros x y z hxy hyz
  cases hxy with
  | inl rxy =>
    -- xRy が成立する場合
    cases hyz with
    | inl ryz =>
      -- yRz が成立する場合、R の推移性により xRz が成立
      left
      exact trans_R rxy ryz
    | inr rfl =>
      -- y = z の場合、xRz が成立
      left
      subst rfl
      simp_all only
  | inr rfl =>
    -- x = y の場合、Q(y, z) の結果は Q(x, z) に対応する
    subst rfl
    simp_all only

-- Qが半順序関係であることの証明
instance Q_is_partial_order : PartialOrder X :=
{
  le := Q R,
  le_refl := Q_refl R,
  le_antisymm := @Q_antisymm X R trans_R not_refl_R,
  le_trans := @Q_trans X R trans_R
}

--------------------
--2項関係と順序 練習6--
--------------------

-- 任意の型 α を仮定
variable {α : Type}

-- 部分集合間の包含関係を定義。Fは証明に使ってないが、F上の部分集合として定義。冪集合として証明されている。
instance (_ : Set (Set α)): PartialOrder (Set α) where
  le := Set.Subset
  le_refl := fun A => Set.Subset.refl A
  le_trans := fun A B C hab Hbc => Set.Subset.trans hab Hbc
  le_antisymm := fun A B hab Hba => Set.Subset.antisymm hab Hba

/-
反射律:任意の集合 A に対して、A は自分自身の部分集合であるため、A ⊆ A が成り立ちます。
反対称律:任意の集合 A, B に対して、A ⊆ B かつ B ⊆ A ならば A = B となります。
推移律:任意の集合 A, B, C に対して、A ⊆ B かつ B ⊆ C ならば A ⊆ C となります。
-/

example (X : Type)  : PartialOrder (Set X) :=
  { le := Set.Subset
    le_refl := Set.Subset.refl
    le_trans := fun A B C hab hbc => Set.Subset.trans hab hbc
    le_antisymm := fun A B hab Hba => Set.Subset.antisymm hab Hba
  }

--------------------
--2項関係と順序 練習7--
--------------------

-- 新しい型 `Divides` の定義
structure Divides where
(val : ℕ)

-- `Divides` 型に対する `PartialOrder` インスタンスの定義
instance : PartialOrder Divides where
  le := λ a b => a.val ∣ b.val
  le_refl := λ a => Nat.dvd_refl a.val
  le_trans := λ a b c hab hbc => Nat.dvd_trans hab hbc
  le_antisymm := λ a b hab hba =>
    by
      cases a
      cases b
      congr
      exact Nat.dvd_antisymm hab hba

-- `Divides` 型に対する `Decidable` インスタンスの定義
instance : DecidableRel (λ a b : Divides => a ≤ b) :=
  λ a b => inferInstanceAs (Decidable (a.val ∣ b.val))

-- 補助関数: `Divides` 型から自然数への変換
instance : Coe Divides ℕ where
  coe := Divides.val

-- `Divides` 型の要素を簡単に作成するためのヘルパー関数
def mkDivides (n : ℕ) : Divides :=
  ⟨n⟩

-- `Divides` 型の要素同士の等価性を自然数の等価性に基づいて定義
instance : BEq Divides where
  beq a b := a.val == b.val

-- `Divides` 型の要素の順序を表示用に定義
instance : ToString Divides where
  toString a := toString a.val

-- 使用例
def example1 : Divides := mkDivides 6
def example2 : Divides := mkDivides 12

--------------------
--2項関係と順序 練習9--
--------------------
--辞書式順序が全順序になることを示す問題。完全性が示せていない。
--4.15でFin.length_ofFnができるので、Lean Copilotが対応したら、そのときに完成させる。現在は難しい。
variable {P : Type} [LinearOrder P]

instance : LinearOrder (Fin n) :=
{
  le := fun i j => i.val ≤ j.val,
  lt := fun i j => i.val < j.val,
  le_refl := fun i => Nat.le_refl i.val,
  le_trans := fun i j k hij hjk => Nat.le_trans hij hjk,
  le_antisymm := fun i j hij hji => Fin.eq_of_val_eq (Nat.le_antisymm hij hji),
  le_total := fun i j => Nat.le_total i.val j.val,
  decidableLE := by infer_instance,
  decidableLT := inferInstance,
  compare := fun i j =>
    if i.val < j.val then Ordering.lt
    else if i.val = j.val then Ordering.eq
    else Ordering.gt,
  compare_eq_compareOfLessAndEq := fun i j =>
    match Nat.lt_trichotomy i.val j.val with
    | Or.inl hlt =>
      by
        simp [compare, hlt]
        rw [compareOfLessAndEq]
        simp_all only [↓reduceIte]
    | Or.inr (Or.inl heq) =>
      by
        simp [compare, heq]
        cases i
        simp_all only [Fin.eta]
        subst heq
        simp_all only [Fin.is_lt]
        simp [compareOfLessAndEq]
    | Or.inr (Or.inr hgt) =>
      by
        simp [compare, hgt]
        split
        next h => simp [compareOfLessAndEq, h]
        next h =>
          --simp_all only [not_lt]
          split
          next h_1 => simp_all only [lt_self_iff_false]
          next h_1 =>
            rw [compareOfLessAndEq]
            simp_all only
            split
            next h_2 =>
              simp_all only [Fin.val_fin_lt, Fin.not_lt, reduceCtorEq]
              omega
            next h_2 =>
              simp_all only [not_lt]
              split
              next h_2 =>
                subst h_2
                simp_all only [lt_self_iff_false]
              next h_2 => simp_all only

  lt_iff_le_not_le := by
    intro a b
    constructor
    · intro h
      simp_all only [not_le, and_true]
      simpa using h.le
    · intro h
      simp_all only [not_le, and_true]
}

lemma List.head?_mem {α : Type _} {l : List α} {a : α}
    (h : l.head? = some a) : a ∈ l := by
  match l with
  | [] => contradiction
  | x :: xs =>
    injection h with hx
    rw [hx]
    apply List.Mem.head

lemma List.eq_nil_of_head?_eq_none {α : Type _} {l : List α}
    (h : l.head? = none) : l = [] := by
  match l with
  | [] => rfl
  | _ :: _ => contradiction

theorem List.findIdx?_le_length' {α : Type} {xs : List α} {p : α → Bool}
  (h : List.findIdx? p xs = some i) :
  i < xs.length := by
    induction xs generalizing i with
    | nil => simp at h
    | cons a as h_ih =>
      simp [List.findIdx?] at h
      split at h
      · simp_all only [Option.some.injEq, length_cons]
        subst h
        simp_all only [Nat.zero_lt_succ]
      ·
        simp_all only [Bool.not_eq_true, Option.map_eq_some', length_cons]
        obtain ⟨w, h⟩ := h
        obtain ⟨left, right⟩ := h
        subst right
        simp_all only [Option.some.injEq, forall_eq', Nat.add_lt_add_iff_right]

def findFirstNonZeroIndex (l : List Int) : Option (Fin l.length) := by
  let pred : Int → Bool := λ x => x ≠ 0
  match nn:List.findIdx? pred l with
  | none =>
    exact none
  | some i =>
      have h_i_lt_length : i < l.length := by
        apply List.findIdx?_le_length'
        exact nn
      exact some ⟨i, h_i_lt_length⟩



--4.15になったらFin.length_ofFnができるので、そのときまで待つ。今は時期尚早。
--今はエラーがとれないので、コメントアウト

def smallestDiffWithProof
  {n : ℕ} {P : Type}
  [DecidableEq P]        -- P の等号可判定性
  (a b : Fin n → P)
  (nonempty : ∃ i : Fin n, a i ≠ b i)
  : { i : Fin n // (a i ≠ b i) ∧ ∀ j < i, a j = b j } :=
by
  clear M X R trans_R not_refl_R
  --noneはリストに入らずに候補のindexのみはいる。使わないかも。


  --
  let listfin := List.ofFn (λ i : Fin n => i)
  have listlen: listfin.length = n := by --これのせいで1日かかった。4.15にすることで解決。
    dsimp [listfin]
    exact (List.length_ofFn (λ i : Fin n => i))

  --candidatesを使わずにこっちを返り値としてつかったほうがいいかも。
  let idxo := List.findIdx? (λ i => a i ≠ b i) listfin
  have idxfsome: idxo.isSome := by
    have idxsome2: listfin.any (λ i => a i ≠ b i) := by
      obtain ⟨w, h⟩ := nonempty
      simp
      use w
      constructor
      dsimp [listfin]
      have : w = (List.ofFn fun i ↦ i)[w] := by
        simp
      --rw [this]
      --dsimp [List.ofFn]
      rw [List.mem_ofFn (fun i => i) w]
      dsimp [Set.range]
      use w

      rw [←ne_eq]
      exact h

    rw [List.findIdx?_isSome]
    exact idxsome2
  have idxf_eqn:∃ (idxs:Nat),some idxs = List.findIdx? (λ i => a i ≠ b i) listfin :=
  by
    match m:List.findIdx? (λ i => a i ≠ b i) listfin with
    | some idfxx =>
      -- idx が l の範囲内であることを証明
      use idfxx
    | none =>
      -- この場合は isSome が矛盾する
      --have : List.findIdx? (λ i => a i ≠ b i) listfin = none := m
      --仮定のmとidxo.isSomeが矛盾する。
      dsimp [idxo] at idxfsome
      exfalso
      rw [List.findIdx?_isSome] at idxfsome
      rw [List.any_eq_true] at idxfsome
      simp at idxfsome
      obtain ⟨x, hx_mem, hx⟩ := idxfsome
      let lf := List.findIdx?_of_eq_none m x
      dsimp [listfin] at lf
      simp at lf
      contradiction

  match m:List.findIdx? (λ i => a i ≠ b i) listfin with
  | none =>
    -- この場合は candidates が空であるため、矛盾
    have : ¬ List.findIdx? (λ i => a i ≠ b i) listfin = none := by
      by_contra hcontra
      obtain ⟨w, h⟩ := idxf_eqn
      rw [hcontra] at h
      contradiction
    contradiction

  | some idx =>
    have : idx < n := by
      rw [←listlen]
      apply List.findIdx?_le_length'
      exact m

    let idxff := Fin.mk idx this

    have hidx: a idxff ≠ b idxff := by
      let getE:= List.findIdx?_eq_some_iff_getElem.mp m
      obtain ⟨hj2, hj3⟩ := getE
      let hj31 := hj3.left
      dsimp [listfin] at hj31
      simp at hj31
      dsimp [idxff]
      exact hj31

    have hminimal: ∀ j < idxff, a j = b j := by
      obtain ⟨idxf, idxfsome⟩ := idxf_eqn
      have :idxf < n := by
        rw [←listlen]
        apply List.findIdx?_le_length'
        rw [idxfsome]

      let idxff := Fin.mk idxf this

      have before_eq: ∀ j < idxff, a j = b j := by
        intro j hj
        let getE:= List.findIdx?_eq_some_iff_getElem.mp idxfsome.symm
        obtain ⟨hj2, hj3⟩ := getE
        let hfj31 := hj3.left
        let hfj32 := hj3.right j hj
        dsimp [listfin] at hfj32
        simp at hfj32
        exact hfj32

      rename_i idxff_1
      intro j a_1
      simp_all only [ne_eq, List.length_ofFn, Option.isSome_some, decide_not, Option.some.injEq, listfin, idxo,
        idxff_1, idxff]

    exact ⟨idxff, hidx, hminimal⟩
/-
-- 定義: P^n 上の辞書式順序 PreOrderから定義に変えようと思って取り組んだけど、却って失敗したから戻した。
-- 練習9はまだできていない。Orderのinstanceの定義が複雑で難しすぎ。もっといろいろなleanに関する知識をつけてから再度、取り組む。
-- Mathlib.Data.List.Lexを使って証明した方がよかった。

def lexOrder {n : ℕ} [DecidableEq (Fin n → P)][DecidableRel fun (x x_1:Fin n) ↦ x ≤ x_1 ]: LinearOrder (Fin n → P) :=
{
  le := λ x y => (∃ i : Fin n, (x i < y i) ∧ ∀ j : Fin n, j < i → x j = y j) ∨ x = y,
  lt := λ x y => (∃ i : Fin n, (x i < y i) ∧ ∀ j : Fin n, j < i → x j = y j),
  le_refl := by --∀ (a : Fin n → P), a ≤ a
  {
    intro a
    right
    simp_all only
  },
  le_trans := by --goal ∀ (a b c : Fin n → P), a ≤ b → b ≤ c → a ≤ c
  {
    intro a b c hab hbc
    obtain ⟨i, hibi, hia⟩ := hab
    obtain ⟨j, hjcj, hbj⟩ := hbc
    cases lt_or_ge i j with
    | inl h =>
      left
      use i
      constructor
      · simp_all only
      · intros k hkj
        simp_all only
        apply hbj
        exact hkj.trans h
        --exact hbj k hk
    | inr h =>
      cases eq_or_lt_of_le h with
      | inl hh =>
        subst hh
        simp_all only [ge_iff_le, le_refl]
        apply Or.inl
        apply Exists.intro
        · apply And.intro
          · exact hibi.trans hjcj
          · intro j_1 a_1
            apply hia
            exact a_1

      | inr hh =>
        left
        use j
        constructor
        · simp_all only [ge_iff_le]
        · intros k hki
          let hbjk := hbj k
          have hkij: k < i :=
          by
            simp_all only [ge_iff_le]
            omega
          let hiak := hia k hkij
          rw [hbjk] at hiak
          exact hiak
          exact hki
    rename_i h
    subst h
    simp_all only
    exact Or.inl ⟨i, hibi, hia⟩

    rename_i h
    subst h
    simp_all only

  },
  le_antisymm := by --goal ∀ (a b : Fin n → P), a ≤ b → b ≤ a → a = b
  {
    intro a b hab hba
    cases hab
    case inr hab_eq => exact hab_eq
    case inl hab_lt =>
      cases hba
      case inr hba_eq => exact hba_eq.symm
      case inl hba_lt =>
        obtain ⟨i, hia, hib⟩ := hab_lt
        obtain ⟨j, hjb, hja⟩ := hba_lt
        cases lt_or_ge i j with
        | inl h =>
          simp_all only [lt_self_iff_false]
        | inr h =>
          cases eq_or_lt_of_le h with
          | inl hh =>
            subst hh
            simp_all only [ge_iff_le, le_refl]
            simp_all only [implies_true]
            contrapose! hjb
            simp_all only [ne_eq]
            exact le_of_lt hia
          | inr hh =>
            have hji: j < i := hh
            have hibj := hib j hji
            rw [hja] at hibj
            simp_all only [lt_self_iff_false]
            simp_all only [lt_self_iff_false]
  },
  le_total := by --goal ∀ (a b : Fin n → P), a ≤ b ∨ b ≤ a
  {
    intro a b
    by_cases h : a = b
    case pos =>
      right
      subst h
      simp_all only [lt_self_iff_false, implies_true, and_true, exists_false, or_true]
    case neg =>
      have : ∃ i : Fin n, ¬ (a i = b i) :=
      by
        have nf: ¬ (∀ i : Fin n, a i = b i) ↔  ∃ i : Fin n, ¬ (a i = b i) := by
          apply Iff.intro
          · intro h
            by_contra hcontra
            apply h
            intro i
            by_contra hcontra2
            simp_all only [not_forall]
          · intro a_1
            simp_all only [not_forall]
        apply nf.mp
        by_contra hcontra
        have :a=b := by
          apply funext
          intro i
          exact hcontra i
        subst this
        simp_all only [not_true_eq_false]
      let ⟨i_min,hi⟩ := smallestDiffWithProof a b this
      simp_all only [or_false]
      have : (b i_min < a i_min) ∨ (a i_min < b i_min) := by
        simp_all only [gt_iff_lt, lt_or_lt_iff_ne, ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        simp [a_1] at hi
      cases this with
      | inl hlt =>
        right
        left
        use i_min
        constructor
        · exact hlt
        · intros j hjw
          exact (hi.2 j hjw).symm
      | inr hlt =>
        left
        use i_min
        constructor
        · exact hlt
        · intros j hjw
          exact hi.2 j hjw
      --a_i > b_i または a_i < b_i である
  },
  decidableLE := by infer_instance,
  decidableLT := by infer_instance,
  decidableEq := inferInstance,

  min_def := by
    have :∀ (a b : Fin n → P) [Decidable (a ≤ b)], a ⊓ b = if a ≤ b then a else b:=
    by
      intro a b
      intro i
      by_cases h: a ≤ b
      case pos =>
        simp_all only [inf_of_le_left, ↓reduceIte]
      case neg =>
        simp_all only [↓reduceIte, inf_eq_right]
        simp only [not_le] at h
        let lt := @le_total (Fin n → P) (lexOrder) a b
        cases lt with
        | inl hlt =>
          exfalso
          exact h hlt
        | inr hlt =>
          exact hlt

    exact this


  max_def := by
    sorry,

  lt_iff_le_not_le := by
    intro a b
    constructor
    · intro h
      simp_all only [not_le, and_true]
      simp_all
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      constructor
      · intro x ba
        by_cases hh: x >= left
        case pos =>
          by_cases hhh: x = left
          case pos =>
            subst hhh
            exfalso
            let lt := lt_trans left_1 ba
            simp_all only [ge_iff_le, le_refl]
            exact lt.not_lt lt

          case neg =>
            use left
            constructor
            · simp_all only [ge_iff_le]
              omega
            · intro hcont
              rw [hcont] at left_1
              simp_all only [lt_self_iff_false]

        case neg =>
          simp_all only [not_le, and_true]
          simp_all
      · intro hab
        have :∀ j, a j = b j := by
          intro j
          rw [←hab]
        let thisl := (this left)
        rw [thisl] at left_1
        subst hab
        simp_all only [lt_self_iff_false]

    · intro h
      simp_all only [not_le, and_true]
      simp_all
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      cases left with
      | inl h => simp_all only
      | inr h_1 =>
        subst h_1
        simp_all only [lt_self_iff_false, not_true_eq_false, and_true, IsEmpty.forall_iff, implies_true]
 }

-- 全順序性の証明
instance lex_is_linear_order {n : ℕ} [d:DecidableEq (Fin n → P)] : LinearOrder (Fin n → P) :=
by
  convert lexOrder
  rename_i inst
  exact inst

  exact d
-/

-------------------------
-- 練習10 x が最小元ならば極小元であることを証明
-------------------------
lemma min_imp_minimal  {Q : Type*} [PartialOrder Q]{x : Q} (h_min : ∀ y : Q, x ≤ y) :
  ∀ y : Q, y ≤ x → y = x :=
by
  -- 任意の y が x 以下であると仮定する
  intro y h_le
  -- すでに x は最小元なので x ≤ y
  have h_ge : x ≤ y := h_min y
  -- 反対称性により、y = x
  exact le_antisymm h_le h_ge

--------------
--練習12:最小元が存在すれば一意であることを証明
--------------

lemma unique_minimum {Q : Type*} [PartialOrder Q]{x y : Q} (h_min_x : ∀ z : Q, x ≤ z)
  (h_min_y : ∀ z : Q, y ≤ z) : x = y :=
by
  -- h_min_x により x ≤ y
  have hxy : x ≤ y := h_min_x y
  -- h_min_y により y ≤ x
  have hyx : y ≤ x := h_min_y x
  -- 反対称性により x = y
  exact le_antisymm hxy hyx
