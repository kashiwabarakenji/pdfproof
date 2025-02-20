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
variable (MySetT : Type u)
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
axiom myElem : MySetType.{u} → MySetType.{u} → Prop   -- `a ∈ b` の関係を表現

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

-------------
---練習3------
-------------

-- 空集合であることを定義的に表すための述語
def IsEmptySet (A : MySetType.{u}) : Prop := ∀ x : MySetType.{u}, ¬ myElem x A

-- 空集合は存在すると一意的であることを示す定理
-- すなわち、任意の空集合 A は MyemptySet と等しい。
theorem uniqueness_of_emptySet (A : MySetType) (hA : IsEmptySet A) : A = MyemptySet := by
  apply Myextensionality
  intro x
  apply Iff.intro
  · intro h
    -- x ∈ A は空集合性より矛盾
    exact False.elim (hA x h)
  · intro h
    -- x ∈ MyemptySet は仮定より成り立たない
    exfalso
    let me:=MyemptySetAxiom
    exact me x h

  -------------
  ----練習5-----
  -------------

-- 対集合の存在公理 (S3)
axiom myPair : MySetType.{u} → MySetType.{u} → MySetType.{u}
axiom myPair_spec : ∀ (A B x : MySetType), myElem x (myPair A B) ↔ (x = A ∨ x = B)

-- 合併集合の存在公理 (S4)
-- 任意の集合 S に対して、∪S が存在することを主張する公理。
axiom myUnionExist : MySetType.{u} → MySetType.{u}
axiom myUnionExist_spec : ∀ (S x : MySetType), myElem x (myUnionExist S) ↔ ∃y, myElem y S ∧ myElem x y

-- ここで、myUnion A B を ∪{A,B} として定義する。
variable (A B:MySetType)

--#check myUnionExist (myPair A B)
noncomputable def myUnion (A B : MySetType) : MySetType := myUnionExist (myPair A B)

-- union_spec の証明: x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
theorem union_spec (A B x : MySetType) : myElem x (myUnion A B) ↔ (myElem x A ∨ myElem x B) := by
  rw [myUnion, myUnionExist_spec (myPair A B) x]
  apply Iff.intro
  · intro ⟨y, hy_in_pair, hx_in_y⟩
    rw [myPair_spec A B y] at hy_in_pair
    cases hy_in_pair with
    | inl ha =>
      rw [ha] at hx_in_y
      left
      exact hx_in_y
    | inr hb =>
      rw [hb] at hx_in_y
      right
      exact hx_in_y
  · intro h
    cases h with
    | inl hA =>
      exists A
      constructor
      · rw [myPair_spec A B A]
        left
        rfl
      · exact hA
    | inr hB =>
      exists B
      constructor
      · rw [myPair_spec A B B]
        right
        rfl
      · exact hB

theorem subset_union_eq (A B : MySetType) : subset myElem A B ↔ myUnion A B = B := by
  apply Iff.intro
  · intro h
    apply Myextensionality
    intro x
    apply Iff.intro
    · intro hx
      rw [union_spec A B x] at hx
      cases hx with
      | inl ha =>
        exact h x ha
      | inr hb =>
        exact hb
    · intro hx
      rw [union_spec A B x]
      right
      exact hx
  · intro h
    intro x ha
    -- hより a ∪ b = b
    -- x ∈ a → x ∈ a ∪ b より、x ∈ b
    have eqSymm : myUnion A B = B := h
    rw [← eqSymm]
    rw [union_spec A B x]
    left
    exact ha

  -------------
  ----練習6-----
  -------------

theorem union_empty (A : MySetType.{u}) : myUnion A MyemptySet = A := by
  apply Myextensionality
  intro x
  apply Iff.intro
  · intro hx
    -- x ∈ A ∪ ∅ より x ∈ A ∨ x ∈ ∅
    rw [union_spec A MyemptySet x] at hx
    cases hx with
    | inl hA => exact hA
    | inr hEmpty =>
      by_contra h
      exact MyemptySetAxiom x hEmpty
  · intro hA
    -- x ∈ A ならば x ∈ A ∪ ∅ は
    rw [union_spec A MyemptySet x]
    left
    exact hA

--------------
---練習9-----
--------------

axiom separation (a : MySetType.{u}) (P : MySetType.{u} → Prop) :
  ∃ b : MySetType.{u}, ∀ x : MySetType.{u}, myElem x b ↔ (myElem x a ∧ P x)

theorem separation_spec (a : MySetType.{u}) (P : MySetType.{u} → Prop) :
  ∃ b, ∀ x, myElem x b ↔ (myElem x a ∧ P x) := by
  exact separation a P

noncomputable def Dash (a : MySetType.{u}) : MySetType.{u} := Classical.choose (separation a (λ x => ¬ myElem x x))
def Dash_spec (a : MySetType.{u}) : ∀ x : MySetType.{u}, myElem x (Dash a) ↔ (myElem x a ∧ ¬ myElem x x) :=
  Classical.choose_spec (separation a (λ x => ¬ myElem x x))

theorem russell_like_paradox (a : MySetType.{u}) : ¬ myElem (Dash a) a := by

    intro hContra   -- 仮定: (Dash a) ∈ a
    have h_spec := Dash_spec a (Dash a)

    rw [h_spec] at h_spec
    rw [←h_spec] at h_spec  -- ちょっとややこしいが、単に h_spec の内容をよく見直すだけで良い

    -- 実際には以下のように簡潔に書ける：
    have : (myElem (Dash a) (Dash a) ↔ (myElem (Dash a) a ∧ ¬ myElem (Dash a) (Dash a))) := Dash_spec a (Dash a)

    have h_self := Dash_spec a (Dash a)
    rw [←h_self] at h_self  -- myElem (Dash a) (Dash a) が左辺にも右辺にも出ることを確認

    have eq: ∀ x, myElem x (Dash a) ↔ (myElem x a ∧ ¬ myElem x x) := Dash_spec a
    have h := eq (Dash a)
    --by_contra h_contra
    have : myElem (Dash a) (Dash a) ↔ ¬ myElem (Dash a) (Dash a) := by
      rw [h]
      apply Iff.intro
      · intro hh
        simp
        intro _
        exact h.mpr hh
      · intro hh
        constructor
        simp at hh
        exact hContra

        simp at hh
        exact (h.mp (hh hContra)).2

    exfalso
    exact iff_not_self this

----------
--練習10---
----------

--集合aを持ってくると、それに属さない集合が必ずある。
lemma exacise10zf (a : MySetType.{u}):∃ b: MySetType.{u}, ¬ myElem b a :=
by
  let b := Dash a
  have : ¬ myElem b a :=
  by
    exact russell_like_paradox a

  use b

axiom foundation: ∀ a:MySetType.{u}, ¬ IsEmptySet a → ∃ b:MySetType.{u},myElem b a ∧ ∀ c:MySetType.{u},¬ ((myElem c a) ∧ (myElem c b))

----------
--練習11---
----------

--どんな集合も自分自身を要素として含まないこと。
lemma exacise11zf (x : MySetType.{u}): ¬ myElem x x :=
by
  by_contra h_contra
  let a := (myPair x x:MySetType.{u}) --シングルトンは、同じもののペアで表す。
  have : ¬IsEmptySet a :=
  by
    dsimp [IsEmptySet]
    push_neg
    use x
    dsimp [a]
    apply (myPair_spec x x x).mpr
    simp

  let fd := foundation a this --正則性の公理を用いる。
  obtain ⟨b,hb⟩ := fd
  let hbx := hb.2 x
  have : myElem x a :=
  by
    dsimp [a]
    apply (myPair_spec x x x).mpr
    simp
  simp at hbx
  specialize hbx this
  have : x = b :=
  by
    apply Myextensionality x b --外延性の公理を用いる。
    intro xx
    apply Iff.intro
    · intro a_1
      simp_all only [not_and, not_false_eq_true, a]
      obtain ⟨left, right⟩ := hb
      rw [myPair_spec x x b] at left
      simp at left
      rw [left]
      exact a_1
    · intro a_1
      simp_all only [not_and, not_false_eq_true, a]
      obtain ⟨left, right⟩ := hb
      rw [myPair_spec x x b] at left
      simp at left
      rw [←left]
      exact a_1
  subst this
  simp_all only [a]
