---ZF集合論-----
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Real.Basic
import LeanCopilot

-------------
---練習1------
-------------

--練習1は矛盾する公理系なので難しいが、属するという関係を改めて定義して示す。

universe u

-- 集合の型を `MySet` として定義し、要素関係 `elem` を導入
variable (MySet : Type u)
variable (elem : MySet → MySet → Prop)   -- `a ∈ b` の関係を表現

-- 公理：外延性の公理 (Extensionality)
axiom extensionality (A B : MySet) : (∀ x : MySet, elem x A ↔ elem x B) → A = B

-- 空集合の存在公理 (Empty Set)
variable (emptySet : MySet)
axiom emptySetAxiom : ∀ x : MySet, ¬ elem x emptySet

-- ラッセル集合 Λ の定義： Λ は自分自身を要素に含まない集合を表す
variable (RussellSet : MySet)

-- ラッセルのパラドックに相当する命題
axiom RussellParadox : ∀ (MySet : Type u) (elem : MySet → MySet → Prop) (RussellSet : MySet), elem RussellSet RussellSet ↔ ¬ elem RussellSet RussellSet

-- ラッセルのパラドックから矛盾を導く定理
theorem RussellParadoxContradiction (elem : MySet → MySet → Prop)(RussellSet : MySet): False :=
  have h : elem RussellSet RussellSet ↔ ¬ elem RussellSet RussellSet := RussellParadox MySet elem RussellSet
  by
    -- elem RussellSet RussellSet が真である場合
    by_cases h_elem : elem RussellSet RussellSet
    · -- h_elem が真なので、h.mp h_elem により ¬ elem RussellSet RussellSet が成り立つ
      have h_not_elem : ¬ elem RussellSet RussellSet := h.mp h_elem
      -- しかし h_elem と h_not_elem が共に成り立つため矛盾
      exact h_not_elem h_elem

    · -- elem RussellSet RussellSet が偽である場合
      have h_pos:elem RussellSet RussellSet := h.mpr h_elem
      contradiction

-------------
---練習2------
-------------

-- 集合の型を `MySetType` として定義し、要素関係 `myElem` を導入
axiom MySetType : Type u
axiom myElem : MySetType → MySetType → Prop   -- `a ∈ b` の関係を表現

-- 外延性の公理
axiom Myextensionality (A B : MySetType) : (∀ x : MySetType, myElem x A ↔ myElem x B) → A = B

-- 空集合の定義
axiom MyemptySet : MySetType
axiom MyemptySetAxiom : ∀ (x : MySetType), ¬ (myElem x MyemptySet)


-- 部分集合の定義
def subset {MySetType : Type} (myElem : MySetType → MySetType → Prop) (A B : MySetType) : Prop := ∀ x : MySetType, myElem x A → myElem x B

--#check MyemptySetAxiom

-- 練習2の定理: 集合 a が空集合である ⇔ a が任意の集合の部分集合である
theorem emptySet_subset_iff (a: MySetType) : (∀ b : MySetType, subset myElem a b) ↔ a = MyemptySet := by
  apply Iff.intro
  -- a が任意の集合 b の部分集合であるならば a = emptySet であることを示す
  · intro h
    apply extensionality
    intro x
    apply Iff.intro
    · intro _
      have _ := h MyemptySet
      simp_all only
      exact h _
    · intro _
      simp_all only
  -- a = emptySet ならば a が任意の集合の部分集合であることを示す
  · intro h
    rw [h]
    intro b
    subst h
    dsimp [subset]
    intro x a
    let cont := (MyemptySetAxiom x)
    contradiction
