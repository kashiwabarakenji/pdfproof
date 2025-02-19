import LeanCopilot
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Order.SymmDiff
--------------
-----集合------
--------------

--集合 練習1
-- 集合 A ⊆ B かつ B ⊆ C のとき、A ⊆ C であることを証明
example {α : Type} {A B C : Set α} : A ⊆ B → B ⊆ C → A ⊆ C :=
by
  intros hAB hBC --hAB : A ⊆ B , hBC : B ⊆ C
  intro x --α : Type
  intro hA --hA : x ∈ A
  apply hBC
  apply hAB
  exact hA

--集合 練習2(前半)
example {α : Type} (A B C : Set α) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
by
  apply Set.ext -- goal: ∀ (x : α), x ∈ A ∪ B ∩ C ↔ x ∈ (A ∪ B) ∩ (A ∪ C)
  intro x -- goal: x ∈ A ∪ B ∩ C ↔ x ∈ (A ∪ B) ∩ (A ∪ C)
  apply Iff.intro -- 両方向に証明を分解
  · show x ∈ A ∪ B ∩ C → x ∈ (A ∪ B) ∩ (A ∪ C) --showはその時点のゴールを表示する。
    intro h -- h : x ∈ A ∪ (B ∩ C)
    cases h with
    | inl hA => -- hA : x ∈ Aのとき
      constructor
      . left --x ∈ A ∪ Bのうち左側のゴールを証明する。
        exact hA
      . left
        exact hA
    | inr hBC => -- hBC : x ∈ B ∩ Cのとき
      constructor
      . right
        exact hBC.1
      . right
        exact hBC.2

  · show x ∈ (A ∪ B) ∩ (A ∪ C) → x ∈ A ∪ B ∩ C
    intro h -- h : x ∈ (A ∪ B) ∩ (A ∪ C)
    obtain ⟨left, right⟩ := h -- left : x ∈ A ∪ B, right : x ∈ A ∪ C
    cases left with
    | inl h =>
      cases right with
      | inl h_1 =>
        exact Or.inl h --x ∈ A ∪ B ∩ Cのうち左側のゴールを選択。
      | inr h_2 =>
        exact Or.inl h
    | inr h_1 =>
      cases right with
      | inl h =>
        exact Or.inl h
      | inr h_2 =>
        exact Or.inr ⟨h_1, h_2⟩

--集合 練習2(後半)
--simoを利用した証明の例
example {α : Type} (A B C : Set α) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
by
  ext x --要素が含まれるかの議論に変換。
  show x ∈ A ∩ (B ∪ C) ↔ x ∈ A ∩ B ∪ A ∩ C
  simp only [Set.mem_inter_iff, Set.mem_union]
  -- Set.mem_inter_iff.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b
  -- Set.mem_union.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b
  --ここにtautoを入れると、その時点で証明が終わってしまう。
  apply Iff.intro --左から右の証明との証明に分解
  · show x ∈ A ∧ (x ∈ B ∨ x ∈ C) → x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C
    intro h --x ∈ A ∧ (x ∈ B ∨ x ∈ C)
    cases h with
    | intro hA hBC => --hA : x ∈ A, hBC : x ∈ B ∨ x ∈ C
      cases hBC with
      | inl hB => --hB : x ∈ B
        exact Or.inl ⟨hA, hB⟩
      | inr hC => --hC : x ∈ C
        exact Or.inr ⟨hA, hC⟩
  · show x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C → x ∈ A ∧ (x ∈ B ∨ x ∈ C)
    intro h
    cases h with
    | inl h => simp_all only [true_or, and_self]
    | inr h_1 => simp_all only [or_true, and_self]

--集合 練習3（前半）
example {α : Type} {A B C : Set α} : (A ⊆ B ∧ A ⊆ C) ↔ A ⊆ (B ∩ C) :=
by
  apply Iff.intro
  · show A ⊆ B ∧ A ⊆ C → A ⊆ B ∩ C
    intro h
    intro x hA
    have hB := h.1 hA -- A ⊆ B から x ∈ B
    have hC := h.2 hA -- A ⊆ C から x ∈ C
    exact ⟨hB, hC⟩ -- よって x ∈ B ∩ C

  · show A ⊆ B ∩ C → A ⊆ B ∧ A ⊆ C
    intro h
    constructor
    -- A ⊆ B を証明
    intro x hA
    exact (h hA).1
    -- A ⊆ C を証明
    intro x hA
    exact (h hA).2

--集合 練習3（後半）
example {α : Type} {A B C : Set α} : (A ⊆ C ∧ B ⊆ C) ↔ A ∪ B ⊆ C :=
by
  apply Iff.intro
  · show A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C
    intro h
    intro x
    intro hx
    cases hx with
    | inl hA => exact h.1 hA
    | inr hB => exact h.2 hB

  · show A ∪ B ⊆ C → A ⊆ C ∧ B ⊆ C
    intro h
    constructor
    · show A ⊆ C
      intro x hA
      apply h
      exact Or.inl hA
    · show B ⊆ C
      intro x hB
      apply h
      exact Or.inr hB

--集合 練習4
--既存の定理のrwの例。
example {α : Type} {A B : Set α} : A ⊆ B ↔ Bᶜ ⊆ Aᶜ :=
by
  apply Iff.intro
  · show  A ⊆ B → Bᶜ ⊆ Aᶜ
    intro h
    intro x
    intro hxB
    show x ∈ Aᶜ
    simp
    show x ∉ A
    intro a --a: x ∈ Aになり、ゴールがFalseになる。
    exact hxB (h a) --h aは、x ∈ Bとなり、hxB:x ∈ Bᶜに矛盾。

  · show Bᶜ ⊆ Aᶜ → A ⊆ B
    intro h
    intro x
    intro hxA
    by_contra hxB
    exact h hxB hxA

--集合 練習6 -- rwの例として使える。
example {α : Type} {A B : Set α} : A ⊆ B ↔ A ∩ B = A :=
by
  apply Iff.intro
  · show A ⊆ B → A ∩ B = A
    intro h
    apply Set.ext
    show ∀ (x : α), x ∈ A ∩ B ↔ x ∈ A
    intro x
    show x ∈ A ∩ B ↔ x ∈ A
    apply Iff.intro
    · show  x ∈ A ∩ B → x ∈ A
      intro hAB
      exact hAB.1
    -- goal: x ∈ A → x ∈ A ∩ B
    · intro hA
      exact ⟨hA, h hA⟩

  -- A ∩ B = A → A ⊆ B
  · intro h
    intro x
    intro hA --goal : x ∈ B --hA: x ∈ A
    rw [← h] at hA -- hA : x ∈ A ∩ B
    exact hA.2

--練習6:上の言明の証明を既存の定理に帰着させた例。
example {α : Type} {A B : Set α} : A ⊆ B ↔ A ∩ B = A :=
by
  rw [Set.inter_eq_left]

--集合 練習7
-- 差集合は、　A \ Bという表記になる。A - Bではない。
example  {α : Type} {A B C: Set α}: A \ (B \ C) = (A \ B) ∪ (A ∩ C) :=
by
  ext x
  simp only [Set.mem_diff, not_and, not_not, Set.mem_union, Set.mem_inter_iff] --全部必要。
  --Set.mem_diff Set.mem_diff.{u} {α : Type u} {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t
  --not_and {a b : Prop} : ¬(a ∧ b) ↔ a → ¬b
  -- goal x ∈ A ∧ (x ∈ B → x ∈ C) ↔ x ∈ A ∧ x ∉ B ∨ x ∈ A ∧ x ∈ C
  apply Iff.intro
  · intro a
    simp_all only [true_and]
    obtain ⟨_, right⟩ := a -- _はプレイスホルダー。その値は取り出してもつかわないので。
    by_cases h : x ∈ B
    -- ケース 1: x ∈ B の場合
    case pos =>
      right
      exact ‹x ∈ B → x ∈ C› h
    -- ケース 2: x ∉ B の場合
    case neg =>
      left
      exact h

  · intro a
    cases a with
    | inl h => simp_all only [false_implies, and_self]
    | inr h_1 => simp_all only [implies_true, and_self]

--練習7:上の言明の証明をtautoの計算に帰着させた例。
example {α : Type} {A B C : Set α} : A \ (B \ C) = (A \ B) ∪ (A ∩ C) :=
by
  ext x
  simp only [Set.mem_diff, not_and, not_not, Set.mem_union, Set.mem_inter_iff]
  tauto

--集合 練習8
example  {α : Type} {A B C: Set α}: (A ∪ B) \ C =(A \ C) ∪ (B \ C) :=
by
  ext x
  simp only [Set.mem_diff, Set.mem_union]
  apply Iff.intro
  · intro h
    simp_all only [not_false_eq_true, and_true]
  · intro h
    cases h with
    | inl ha => simp_all only [true_or, not_false_eq_true, and_self]
    | inr hb => simp_all only [or_true, not_false_eq_true, and_self]

--上の言明の証明をtautoの計算に帰着させた例。
example  {α : Type} {A B C: Set α}: (A ∪ B) \ C =(A \ C) ∪ (B \ C) :=
by
  ext x
  simp only [Set.mem_diff, Set.mem_union]
  tauto

--the symmetric difference (△) operator
--import Mathlib.Order.SymmDiff
-- 対称差（symmDiff）を表す △ 演算子を定義
infixl:70 " ∆ " => symmDiff

--集合 練習9
-- A ∪ B = (A △ B) △ (A ∩ B) を示す
example {α : Type} (A B : Set α) : A ∪ B = (A ∆ B) ∆ (A ∩ B) :=
by
  apply Set.ext
  intro x
  -- 両方向の証明
  apply Iff.intro

  · show x ∈ A ∪ B → x ∈ A ∆ B ∆ (A ∩ B)
    intro h
    cases h with
    | inl hA =>
      unfold symmDiff -- 定義を展開
      simp_all only [Set.sup_eq_union, Set.mem_union, Set.mem_diff, or_false, Set.mem_inter_iff]
      tauto

    | inr hB =>
      unfold symmDiff
      simp_all only [Set.sup_eq_union, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
      tauto

  · show x ∈ A ∆ B ∆ (A ∩ B) → x ∈ A ∪ B
    intro h
    unfold symmDiff at h
    simp_all only [Set.sup_eq_union, Set.mem_union, Set.mem_diff, Set.mem_inter_iff, not_and, not_or, not_not]
    cases h with
    | inl h_1 =>
      obtain ⟨left, _⟩ := h_1 --使わない変数は_で表す。place holderと呼ぶ。
      cases left with
      | inl h => simp_all only [not_false_eq_true, imp_self, or_false]
      | inr h_1 => simp_all only [not_true_eq_false, false_implies, or_true]
    | inr h_2 => simp_all only [or_self]

--集合 練習10
example {α : Type} (A B C: Set α) : (A ∆ B) ∆ C= A ∆ (B ∆ C) :=
by
  apply Set.ext
  intro x
  simp [symmDiff, Set.mem_diff, Set.mem_union, Set.mem_inter]
-- 2進論理を整理
-- (x ∈ A ∆ B ∆ C) は、x が奇数回 A, B, C のどれかに含まれること
-- これは排他的論理和 (XOR) と同じ
-- ここでは、ブール論理を用いて証明
-- 具体的には、以下の等式を示す:
-- (x ∈ A ↔ x ∉ B ↔ x ∉ C) ↔ (x ∈ A ↔ (x ∉ B ↔ x ∉ C))
-- これはブール代数の結合律に従う
-- よって、両辺は同値
  tauto --tautoを使えば、分解する必要なし。
  /-
  apply Iff.intro
  · intro a
    cases a with
    | inl h =>
      tauto
    | inr h_1 =>
      tauto
  · intro a
    cases a with
    |
      inl h =>
      tauto
    | inr h_1 =>
      tauto
  -/

-- 集合 練習11
example {α : Type} (A B C: Set α) : A ∩ (B ∆ C) = (A ∩ B) ∆ (A ∩ C) := by
  ext x
  -- 左側の定義を展開
  simp [symmDiff, Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
  -- 場合分けをする
  tauto

-- 集合 練習12 排中律が使われている例
example {A B:Prop} (h: A → B): ¬ A ∨ B :=
  Or.elim (Classical.em A)
   (fun hA => Or.inr (h hA))
   (fun hA => Or.inl hA)

--集合 練習14 デカルト積 productを使ってみた。
example {α: Type} (A B C: Set α): (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) :=
  by
    apply Set.ext
    intro x
    apply Iff.intro
    -- x ∈ (A ∪ B) ×ˢ C -> x ∈ (A ×ˢ C) ∪ (B ×ˢ C)
    intro hABC
    obtain ⟨hAB, hC⟩ := hABC
    cases hAB with
    | inl hA =>
      apply Or.inl
      constructor
      exact hA
      exact hC
    | inr hB =>
      apply Or.inr
      constructor
      exact hB
      exact hC
    -- x ∈ (A ×ˢ C) ∪ (B ×ˢ C) -> x ∈ (A ∪ B) ×ˢ C
    intro hACBC
    cases hACBC with
    | inl hAC =>
      obtain ⟨hA, hC⟩ := hAC
      constructor
      exact Or.inl hA
      exact hC
    | inr hBC =>
      obtain ⟨hB, hC⟩ := hBC
      constructor
      exact Or.inr hB
      exact hC
