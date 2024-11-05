import LeanCopilot
--import Mathlib.Init.Logic
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
    intros hAB hBC
    intro x
    intro hA
    apply hBC
    apply hAB
    exact hA

--集合 練習2(前半)
example {α : Type} (A B C : Set α) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
  by
    apply Set.ext -- goal: ∀ (x : α), x ∈ A ∪ B ∩ C ↔ x ∈ (A ∪ B) ∩ (A ∪ C)
    intro x -- goal: x ∈ A ∪ B ∩ C ↔ x ∈ (A ∪ B) ∩ (A ∪ C)
    apply Iff.intro -- 両方向に証明を分解
    -- A ∪ (B ∩ C) ⊆ (A ∪ B) ∩ (A ∪ C)の証明
    intro h -- h : x ∈ A ∪ (B ∩ C)
    cases h with
    | inl hA => -- hA : x ∈ Aのとき
      constructor
      . left; exact hA
      . left; exact hA
    | inr hBC => -- hBC : x ∈ B ∩ Cのとき
      constructor
      . right; exact hBC.1
      . right; exact hBC.2
    -- (A ∪ B) ∩ (A ∪ C) ⊆ A ∪ (B ∩ C)の証明
    intro h -- h : x ∈ (A ∪ B) ∩ (A ∪ C) -- goal: x ∈ A ∪ B ∩ C
    --simp only [Set.mem_inter_iff, Set.mem_union] 必要なかったのでコメントアウト。後で消す。
    obtain ⟨left, right⟩ := h -- left : x ∈ A ∪ B, right : x ∈ A ∪ C
    cases left with
    | inl h =>
      cases right with
      | inl h_1 =>
        exact Or.inl h
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
    --goal x ∈ A ∩ (B ∪ C) ↔ x ∈ A ∩ B ∪ A ∩ C
    simp only [Set.mem_inter_iff, Set.mem_union]
    -- Set.mem_inter_iff.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b
    -- Set.mem_union.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b
    --goal: x ∈ A ∧ (x ∈ B ∨ x ∈ C) ↔ x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C
    --ここにtautoを入れると、その時点で証明が終わってしまう。
    apply Iff.intro --左から右の証明との証明に分解
    · intro a --左から右。goal: x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C
      cases a with
      | intro hA hBC => --hA : x ∈ A, hBC : x ∈ B ∨ x ∈ C
        cases hBC with
        | inl hB => --hB : x ∈ B
          exact Or.inl ⟨hA, hB⟩
        | inr hC => --hC : x ∈ C
          exact Or.inr ⟨hA, hC⟩
    · intro a --右から左。goal: x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C
      cases a with
      | inl h => simp_all only [true_or, and_self]
      | inr h_1 => simp_all only [or_true, and_self]

--集合 練習3（前半）
example {α : Type} {A B C : Set α} : (A ⊆ B ∧ A ⊆ C) ↔ A ⊆ (B ∩ C) :=
  by
    apply Iff.intro
    -- (A ⊆ B ∧ A ⊆ C) → A ⊆ (B ∩ C)
    · intro h
      intro x hA
      have hB := h.1 hA -- A ⊆ B から x ∈ B
      have hC := h.2 hA -- A ⊆ C から x ∈ C
      exact ⟨hB, hC⟩ -- よって x ∈ B ∩ C

    -- A ⊆ (B ∩ C) → (A ⊆ B ∧ A ⊆ C)
    · intro h
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
    -- A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C
    · intro h
      intro x
      intro hx
      cases hx with
      | inl hA => exact h.1 hA
      | inr hB => exact h.2 hB

    -- A ∪ B ⊆ C → A ⊆ C ∧ B ⊆ C
    · intro h
      constructor
      -- A ⊆ C を証明
      · intro x hA
        apply h
        exact Or.inl hA
      -- B ⊆ C を証明
      · intro x hB
        apply h
        exact Or.inr hB

--集合 練習4
--既存の定理のrwの例。
example {α : Type} {A B : Set α} : A ⊆ B ↔ Bᶜ ⊆ Aᶜ :=
  by
    apply Iff.intro
    -- goal: A ⊆ B → Bᶜ ⊆ Aᶜ
    · intro h
      intro x
      intro hxB
      rw [Set.mem_compl_iff] --pᶜ ↔ ¬p
      tauto

    -- goal: Bᶜ ⊆ Aᶜ → A ⊆ B
    · intro h
      intro x
      intro hxA
      by_contra hxB
      exact h hxB hxA

--集合 練習6 -- rwの例として使える。
example {α : Type} {A B : Set α} : A ⊆ B ↔ A ∩ B = A :=
  by
    apply Iff.intro
    -- A ⊆ B → A ∩ B = A
    · intro h
      apply Set.ext -- goal: ∀ (x : α), x ∈ A ∩ B ↔ x ∈ A
      intro x -- goal: x ∈ A ∩ B ↔ x ∈ A
      apply Iff.intro
      -- goal: x ∈ A ∩ B → x ∈ A
      intro hAB
      exact hAB.1
      -- goal: x ∈ A → x ∈ A ∩ B
      intro hA
      exact ⟨hA, h hA⟩

    -- A ∩ B = A → A ⊆ B
    · intro h
      intro x
      intro hA --goal : x ∈ B --hA: x ∈ A
      rw [← h] at hA -- hA : x ∈ A ∩ B
      exact hA.2

--上の言明の証明を既存の定理に帰着させた例。
example {α : Type} {A B : Set α} : A ⊆ B ↔ A ∩ B = A :=
by
  rw [Set.inter_eq_left]

--集合 練習7
-- 差集合は、　A \ Bという表記になる。A - Bではない。
example  {α : Type} {A B C: Set α}: A \ (B \ C)=(A \ B) ∪ (A ∩ C) :=
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

--上の言明の証明をtautoの計算に帰着させた例。
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
    · intro a
      simp_all only [not_false_eq_true, and_true] --もっと細かく証明したい。
    · intro a
      cases a with
      | inl h => simp_all only [true_or, not_false_eq_true, and_self]
      | inr h_1 => simp_all only [or_true, not_false_eq_true, and_self]

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

    -- A ∪ B ⊆ (A △ B) △ (A ∩ B)
    · intro h
      cases h with
      | inl hA =>
        unfold symmDiff -- 定義を展開
        simp_all only [Set.sup_eq_union, Set.mem_union, Set.mem_diff, or_false, Set.mem_inter_iff]
        tauto

      | inr hB =>
        unfold symmDiff
        simp_all only [Set.sup_eq_union, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
        tauto

    -- (A △ B) △ (A ∩ B) ⊆ A ∪ B
    · intro h
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
    apply Iff.intro
    · intro a
      cases a with
      | inl h => simp_all only [imp_false, false_implies, and_true, not_false_eq_true, false_and, or_false]
      |
        inr h_1 =>
        simp_all only [implies_true, true_implies, true_and, not_true_eq_false, and_false, false_or]
        obtain ⟨_, right⟩ := h_1
        obtain ⟨left_1, right⟩ := right
        tauto
    · intro a
      cases a with
      |
        inl h =>
        simp_all only [true_and, not_true_eq_false, and_false, or_false, true_implies, implies_true, and_true]
        obtain ⟨_, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        tauto
      | inr h_1 =>
        simp_all only [false_and, not_false_eq_true, and_true, false_or, false_implies, imp_false, true_and]


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

-------------
---- 写像 ----
-------------

--写像 練習3
-- f : X → Y に対して、任意の A ⊆ B ⊆ X に対して f(A) ⊆ f(B) を示す。像はf''で表す。
-- haveが登場する例になっている。
example {X Y : Type} (f : X → Y) {A B : Set X} (h : A ⊆ B) : f '' A ⊆ f '' B :=
  by
    intro y
    -- ゴールは y ∈ f '' A → y ∈ f '' B
    intro hy --y ∈ f '' A
    cases hy with
    | intro x hx => -- hx : x ∈ A ∧ f x = y
      let fx_eq_y := hx.2
      -- fx_eq_y : f x = y
      have hB: x ∈ B := h hx.1
      let rst := Set.mem_image_of_mem f hB
      rw [fx_eq_y] at rst
      exact rst

--写像 練習4
-- f(A ∩ B) ⊆ f(A) ∩ f(B) を証明する
example {X Y : Type} (f : X → Y) (A B : Set X) : f '' (A ∩ B) ⊆ (f '' A) ∩ (f '' B) :=
  by
    intro y
    intro h
    -- y ∈ f(A ∩ B) を解釈
    cases h with
    | intro x hx =>
      let  fx_eq_y := hx.2
      -- hx : x ∈ A ∩ B, fx_eq_y : f x = y
      constructor
      -- f(x) ∈ f(A)
      · cases hx.1 with
        | intro hA hB => --hA x ∈ A  hB : x ∈ B --goal y ∈ f '' A
          let rst := Set.mem_image_of_mem f hA
          rw [fx_eq_y] at rst
          exact rst
        -- f(x) ∈ f(B)
      · cases hx.1 with
        | intro hA hB => --hA x ∈ A  hB : x ∈ B --goal y ∈ f '' A
          let rst := Set.mem_image_of_mem f hB
          rw [fx_eq_y] at rst
          exact rst

--写像 練習5
-- f(A ∪ B) = f(A) ∪ f(B) を証明
example {X Y : Type} (f : X → Y) (A B : Set X) : f '' (A ∪ B) = f '' A ∪ f '' B :=
  by
    apply Set.ext -- 集合の等式を示すために extensionality を使用
    intro y
    apply Iff.intro
    -- f(A ∪ B) ⊆ f(A) ∪ f(B)
    · intro h
      cases h with
      | intro x hx  =>
        let fx_eq_y := hx.2
        cases hx.1 with
        | inl hA =>
          left
          exact ⟨x, hA, fx_eq_y⟩
        | inr hB =>
          right
          exact ⟨x, hB, fx_eq_y⟩

    -- f(A) ∪ f(B) ⊆ f(A ∪ B)
    · intro h
      cases h with
      | inl hA =>
        cases hA with
        | intro x hxA =>
          let fx_eq_y := hxA.2
          exact ⟨x, Or.inl hxA.1, fx_eq_y⟩
      | inr hB =>
        cases hB with
        | intro x hxB =>
          let fx_eq_y := hxB.2
          exact ⟨x, Or.inr hxB.1, fx_eq_y⟩

--写像 練習6(前半)
-- 任意の A, B ⊆ Y に対して f^{-1}(A ∩ B) = f^{-1}(A) ∩ f^{-1}(B) を証明。ChatGPT-4そのまま通った。
example {X Y : Type} (f : X → Y) (A B : Set Y) : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B :=
  by
    apply Set.ext -- 集合の等式を示すために外延性を使用
    intro x
    apply Iff.intro
    -- f⁻¹(A ∩ B) ⊆ f⁻¹(A) ∩ f⁻¹(B)
    · intro h
      constructor
      -- f(x) ∈ A
      exact h.1
      -- f(x) ∈ B
      exact h.2

      -- f⁻¹(A) ∩ f⁻¹(B) ⊆ f⁻¹(A ∩ B)
    · intro h
      exact ⟨h.1, h.2⟩

--写像 練習6(後半)
-- 任意の A, B ⊆ Y に対して f^{-1}(A ∪ B) = f^{-1}(A) ∪ f^{-1}(B) を証明
example {X Y : Type} (f : X → Y) (A B : Set Y) : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
  by
    apply Set.ext -- 集合の等式を示すために外延性を使用
    intro x
    apply Iff.intro
    -- f⁻¹(A ∪ B) ⊆ f⁻¹(A) ∪ f⁻¹(B)
    · intro h
      cases h with
      | inl hA =>
        left
        exact hA
      | inr hB =>
        right
        exact hB

      -- f⁻¹(A) ∪ f⁻¹(B) ⊆ f⁻¹(A ∪ B)
    · intro h
      cases h with
      | inl hA =>
        exact Or.inl hA
      | inr hB =>
        exact Or.inr hB

--写像 練習7の補題
--下の証明で使う補助補題。補題を用いる例になっている。
lemma diff_empty {α : Type} {x₁ x₂ : α} (h : ¬(x₁ = x₂)) : {x₁} ∩ {x₂} = (∅ : Set α) :=
  by
    apply Set.eq_empty_iff_forall_not_mem.mpr --mprは左から右の部分を取り出したもの。
    intro y
    intro hy
    cases hy with
    | intro hy₁ hy₂ =>
      apply h
      exact Eq.trans hy₁.symm hy₂

--写像 練習7
-- 任意の A, B ⊆ X について f(A ∩ B) = f(A) ∩ f(B) であることが、f が単射であることと同値であることを示す
example  {X Y : Type} (f : X → Y) :
  (∀ A B : Set X, f '' (A ∩ B) = f '' A ∩ f '' B) ↔ Function.Injective f :=
  by
    apply Iff.intro

    -- (→) 方向: f(A ∩ B) = f(A) ∩ f(B) → f が単射
    · intro h_inj
      -- x₁, x₂ ∈ X に対して、f(x₁) = f(x₂) のとき、x₁ = x₂ を示す
      intro x₁ x₂ hfx
      -- A を {x₁}、B を {x₂} として交差に関する条件を考える
      have h := h_inj {x₁} {x₂}
      simp at h
      -- f({x₁}) = {f(x₁)} かつ f({x₂}) = {f(x₂)} より、仮定 f(x₁) = f(x₂) から同じ像が得られる
      have h₁ : f '' ({x₁} ∩ {x₂}) = {f x₁} := by
        simp_all only [Set.image_singleton, Set.inter_self]
      simp only [Set.image_singleton, Set.inter_self] at h₁
      by_contra conh
      have h3: f '' ({x₁} ∩ {x₂}) = (∅ : Set Y) := by
        rw[diff_empty conh]
        -- Set.image_singleton.{u_1, u_2} {α : Type u_1} {β : Type u_2} {f : α → β} {a : α} : f '' {a} = {f a}
        -- Set.image_empty.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α → β) : f '' ∅ = ∅
        simp_all only [Set.image_singleton, Set.inter_self, ne_eq, Set.image_empty]

      -- Set.singleton_ne_empty.{u} {α : Type u} (a : α) : {a} ≠ ∅
      -- ne_eq.{u_1} {α : Sort u_1} (a b : α) : (a ≠ b) = ¬a = b
      -- goal False
      simp_all only [Set.image_singleton, Set.inter_self, ne_eq, Set.singleton_ne_empty]

      -- (←) 方向: f が単射 → f(A ∩ B) = f(A) ∩ f(B)
    · intro hf
      -- 任意の A, B ⊆ X について、f(A ∩ B) ⊆ f(A) ∩ f(B) と f(A) ∩ f(B) ⊆ f(A ∩ B) を示す
      intros A B
      apply Set.ext --等価性を示すために外延性を使用
      intro y -- y ∈ f '' (A ∩ B) ↔ y ∈ f '' A ∩ f '' B
      apply Iff.intro -- 両方向に証明を分解

      -- f(A ∩ B) ⊆ f(A) ∩ f(B)
      · intro h
        -- f '' (A ∩ B) に属する y が与えられたとき、それが f(A) ∩ f(B) にも属することを示す
        obtain ⟨x, hx1, hx2⟩ := h --hx1 : x ∈ A ∩ B, hx2 : f x = y
        constructor
        -- f(x) ∈ f(A)
        · exact ⟨x, hx1.1, hx2⟩
        -- f(x) ∈ f(B)
        · exact ⟨x, hx1.2, hx2⟩

        -- f(A) ∩ f(B) ⊆ f(A ∩ B)
      · intro h
        -- f(A) と f(B) の共通部分にある y が f(A ∩ B) に属することを示す
        obtain ⟨a, haA, hfa⟩ := h.1 -- f a = y
        obtain ⟨b, hbB, hfb⟩ := h.2 -- f b = y
        have : f a = f b := by --rw [← hfa, ← hfb]
          subst hfa
          simp_all only [Set.mem_inter_iff, Set.mem_image]
        have : a = b := hf this
        subst this -- goal : y ∈ f '' (A ∩ B)
        exact ⟨a, ⟨haA, hbB⟩, hfa⟩

--写像 練習7
--別証明というほど違わないが、上と同じ言明をあらためて証明したもの。証明の流れは同じ。
example {X Y : Type} (f : X → Y) :
  (∀ A B : Set X, f '' (A ∩ B) = f '' A ∩ f '' B) ↔ Function.Injective f :=
by
  apply Iff.intro

  -- (→) direction: f(A ∩ B) = f(A) ∩ f(B) → f is injective
  · intro h_inj
    intro x₁ x₂ hfx
    -- Consider A = {x₁}, B = {x₂} and use the given condition on intersections
    have h := h_inj {x₁} {x₂}
    simp only [Set.image_singleton, Set.inter_empty, Set.image_empty] at h
    -- From f(x₁) = f(x₂), we get the same image for both sets
    by_contra hne -- Goal False
    have : f '' ({x₁} ∩ {x₂}) = ∅ := by
      simp [hne]
      simp_all only [Set.image_singleton]
      tauto
    -- But f '' ({x₁} ∩ {x₂}) = {f x₁}, which leads to a contradiction
    simp_all only [Set.inter_self, Set.singleton_ne_empty]

  -- (←) direction: f is injective → f(A ∩ B) = f(A) ∩ f(B)
  · intro hf
    intros A B
    apply Set.ext
    intro y
    apply Iff.intro

    -- f(A ∩ B) ⊆ f(A) ∩ f(B)
    · intro h
      obtain ⟨x, hx, rfl⟩ := h --hx: x ∈ A ∩ B
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩

      -- f(A) ∩ f(B) ⊆ f(A ∩ B)
    · intro h -- goal: y ∈ f '' (A ∩ B) -- h: y ∈ f '' A ∩ f '' B
      obtain ⟨a, haA, rfl⟩ := h.1
      obtain ⟨b, hbB, hfb⟩ := h.2 --  f b = f a
      have : a = b := by
        apply hf
        simp_all only
      subst this -- goal: f a ∈ f '' (A ∩ B)
      exact ⟨a, ⟨haA, hbB⟩, rfl⟩

--写像 練習8
--lean copilotを使った証明。このあとに短くした証明ものせる。
example {α β : Type}  (f : α → β) :
  (∀ A : Set α, (f '' A)ᶜ ⊆ f '' (Aᶜ)  ) ↔ Function.Surjective f :=
  by
    apply Iff.intro

    -- (→) 方向: f が全射なら f(A)^c ⊆ f(A^c) が成り立つことを示す
    -- 仮定: 任意の A に対して f(A^c) ⊆ (f(A))^c が成り立つ
    · intro h
      rw [Function.Surjective]
      by_contra hns
      push_neg at hns
      obtain ⟨y, hy⟩ := hns

      have h1 : y ∈ (f '' Set.univ)ᶜ := by
        simp_all only [Set.image_subset_iff, Set.preimage_compl, Set.compl_subset_compl, ne_eq, Set.image_univ,
          Set.mem_compl_iff, Set.mem_range, exists_false, not_false_eq_true]
      have h2 : y ∉ f '' (Set.univᶜ) := by
        simp_all only [Set.image_subset_iff, Set.preimage_compl, Set.compl_subset_compl, ne_eq, Set.image_univ,
      Set.mem_compl_iff, Set.mem_range, exists_false, not_false_eq_true, Set.compl_univ, Set.image_empty,
      Set.mem_empty_iff_false]
      exact h2 (h Set.univ h1)

    -- (←) 方向: 任意の A ⊆ X について f(A)^c ⊆ f(A^c) ならば f が全射であることを示す
    · intro h
      intro A
      -- y が Y の任意の要素とする
      -- A = ∅ とすると f(∅) = ∅ なので補集合を考える
      rw [Function.Surjective] at h

      --have sub0: X ⊆ Y ↔ Yᶜ ⊆ Xᶜ := by
      --  intro h
      --  rw [Set.subset_iff, Set.compl_subset_compl]
      --  exact h
      have sub1: (f '' A)ᶜ ⊆ f '' Aᶜ ↔ (f '' Aᶜ)ᶜ ⊆ (f '' A) := by
        apply Iff.intro
        intro h
        intro x hxA
        simp_all only [Set.mem_compl_iff, Set.mem_compl_iff]
        by_contra hnx
        let hnx2 :=(h hnx)
        contradiction

        intro h'
        intro x hxA
        simp_all only [Set.mem_compl_iff, Set.mem_compl_iff]
        by_contra hnx
        let hnx2 :=(h' hnx)
        contradiction

      rw [sub1]
      intro y
      -- 任意の y ∈ (f '' Aᶜ)ᶜ を取る
      intro hy
      -- y ∉ f '' Aᶜ であることを仮定
      simp at hy
      -- 全射性 hf により、ある x ∈ α が存在して f x = y となる
      obtain ⟨x, hx⟩ := h y
      -- ここで、y ∉ f '' Aᶜ なので、x ∉ Aᶜ すなわち x ∈ A
      by_contra hh
      -- x ∈ Aᶜ であると仮定すると矛盾
      subst hx
      simp_all only [Set.mem_image, not_exists, not_and]
      apply hy
      on_goal 2 => {apply Eq.refl}
      · apply Aesop.BuiltinRules.not_intro
        intro a
        apply hh
        · exact a
        · simp_all only

-- 別証明というわけでもないが、同じ定理の証明をふたたび書いてみる。
example {α β : Type}  (f : α → β) :
  (∀ A : Set α, (f '' A)ᶜ ⊆ f '' (Aᶜ)) ↔ Function.Surjective f :=
  by
    apply Iff.intro

    -- (→) 方向: f が全射なら f(A)^c ⊆ f(A^c) が成り立つことを示す
    -- 仮定: 任意の A に対して f(A^c) ⊆ (f(A))^c が成り立つ
    intro h
    rw [Function.Surjective]
    by_contra hns --背理法
    push_neg at hns
    obtain ⟨y, hy⟩ := hns

    -- f が全射ではないので、ある y ∈ β に対して f(x) = y となる x が存在しない
    -- このとき、y は f '' α に含まれないので y ∈ (f '' Set.univ)ᶜ となる
    -- Set.univは全体集合
    have hynot : y ∈ (f '' Set.univ)ᶜ := by
      simp_all only [Set.mem_compl_iff, Set.mem_range]
      --Set.mem_compl_iff:  a ∈ UpperSet.compl s ↔ a ∉ s
      --Set.mem_range  : x ∈ Set.range f ↔ ∃ y, f y = x
      simp [hy]

    -- 仮定より (f '' Set.univ)ᶜ ⊆ f '' (Set.univᶜ)
    specialize h Set.univ -- Set.univは全体集合
    -- Set.univᶜ は空集合なので、f '' (Set.univᶜ) = f '' ∅ = ∅
    rw [Set.compl_univ, Set.image_empty] at h
    --Set.compl_univ : Set.univᶜ = ∅

    -- よって (f '' Set.univ)ᶜ ⊆ ∅
    -- すると y ∈ ∅ となり矛盾が生じる
    exact Set.not_mem_empty y (h hynot)
    --a ∉ ∅

    -- (←) 方向: f(A)^c ⊆ f(A^c) なら f が全射であることを示す
    intro hsurj
    rw [Function.Surjective] at hsurj
    intros A x hx
    -- x が f(A)^c に属するという仮定のもとで、f が全射なら矛盾を導く
    rw [Set.mem_compl_iff, Set.mem_image] at hx
    --Set.mem_compl_iff:  a ∈ UpperSet.compl s ↔ a ∉ s
    --Set.mem_image:  y ∈ f '' s ↔ ∃ x ∈ s, f x = y
    --
    by_contra hns
    -- 存在しない元yを取得
    push_neg at hns
    obtain ⟨a, ha⟩ := hsurj x
    subst ha  --代入
    simp_all only [not_exists, not_and, Set.mem_image, Set.mem_compl_iff]
    --#check not_exists -- not_exists.{u_1} {α : Sort u_1} {p : α → Prop} : (¬∃ x, p x) ↔ ∀ (x : α), ¬p x
    --#check not_and -- not_and : ¬a ∧ ¬b ↔ ¬(a ∧ b)
    apply hns
    on_goal 2 => {apply Eq.refl}
    · intro h
      apply hx a
      simp_all only
      exact rfl

--写像 練習9
--単射と単射の合成は単射
example {A B C : Type} (f : A → B) (g : B → C)
  (hf : Function.Injective f) (hg : Function.Injective g) :
  Function.Injective (g ∘ f) := by
  -- 任意の x₁, x₂ ∈ A に対して g(f(x₁)) = g(f(x₂)) を仮定
  intros x₁ x₂ h
  -- g が単射なので、f(x₁) = f(x₂) を導く
  apply hf
  apply hg
  exact h

--写像 練習10
--全射と全射の合成は全射
example {A B C : Type} (f : A → B) (g : B → C)
  (hf : Function.Surjective f) (hg : Function.Surjective g) :
  Function.Surjective (g ∘ f) := by
  -- 任意の c ∈ C に対して、ある a ∈ A を見つける
  intro c
  -- g が全射なので、ある b ∈ B が存在して g(b) = c
  obtain ⟨b, hb⟩ := hg c
  -- f が全射なので、ある a ∈ A が存在して f(a) = b
  obtain ⟨a, ha⟩ := hf b
  -- 合成関数の値 g(f(a)) = c となる
  use a
  rw [Function.comp_apply, ha, hb]

--写像 練習11
lemma subset_preimage_image {X Y : Type}(f : X → Y)(A : Set X): A ⊆ f ⁻¹' (f '' A) :=
by
  intro x hx
  simp only [Set.mem_preimage, Set.mem_image]
  use x, hx

--写像 練習12
example {X Y : Type} (f : X → Y) (B : Set Y) : B ∩ f '' Set.univ = f '' (f ⁻¹' B) :=
by
  apply Set.ext
  intro y
  apply Iff.intro
  -- B ∩ f(X) ⊆ f(f⁻¹(B))
  · intro h
    cases h with
    | intro hB hfX =>
      obtain ⟨x, _, rfl⟩ := hfX
      exact ⟨x, ⟨hB, rfl⟩⟩
  -- f(f⁻¹(B)) ⊆ B ∩ f(X)
  · intro h
    cases h with
    | intro x hx =>
      obtain ⟨hB, rfl⟩ := hx
      exact ⟨hB, ⟨x, ⟨Set.mem_univ x, rfl⟩⟩⟩

--写像 練習13
--写像 f : X → Y が与えられたとき、Xの部分集合AとYの部分集合Bに対して、
-- f '' (A ∩ f ⁻¹' B) = f '' A ∩ B が成り⽴つことを⽰す。
theorem image_inter_preimage_eq {X Y : Type} (f : X → Y) (A : Set X) (B : Set Y): f '' (A ∩ f ⁻¹' B) = (f '' A) ∩ B :=
by
  ext y
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_preimage]
  apply Iff.intro
  · -- y ∈ f '' (A ∩ f ⁻¹' B) → y ∈ f '' A ∩ B
    intro h
    cases h with
    | intro x hx =>
      obtain ⟨left, right⟩ := hx
      obtain ⟨left, right_1⟩ := left
      subst right
      simp_all only [and_true]
      exact ⟨x, left, rfl⟩
  · -- y ∈ f '' A ∩ B → y ∈ f '' (A ∩ f ⁻¹' B)
    rintro ⟨⟨x, hx, rfl⟩, hy⟩
    constructor
    apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [and_self]

--写像 練習13の別証明
theorem image_inter_preimage_eq2 {X Y : Type} (f : X → Y) (A : Set X) (B : Set Y) :
  f '' (A ∩ f ⁻¹' B) = (f '' A) ∩ B := by
  ext y
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_preimage]
  --goal ∃ x, (x ∈ A ∧ f x ∈ B) ∧ f x = y) ↔ (∃ x ∈ A, f x = y) ∧ y ∈ B
  constructor
  · rintro ⟨x, ⟨hxA, hxB⟩, rfl⟩ --hxA : x ∈ A   hxB : f x ∈ B
    exact ⟨⟨x, hxA, rfl⟩, hxB⟩
  · rintro ⟨⟨x, hxA, rfl⟩, hyB⟩ --hxA : x ∈ A   hyB : f x ∈ B
    exact ⟨x, ⟨hxA, hyB⟩, rfl⟩
