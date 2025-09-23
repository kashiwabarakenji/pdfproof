--pdf proof by Lean
import LeanCopilot
import Mathlib.Data.Real.Basic

--命題論理 例1
example {A:Prop} {B:Prop} {C:Prop} : (A → (B → C)) → (B → (A → C)) :=
  by
    intro hAB --goal : B → (A → C)
    intro hB --goal : A → C
    intro hA --goal : C
    exact (hAB hA) hB --カッコはなくても同じ

--例1 ラムダ式を使った場合の証明
example {A B C : Prop} : (A → (B → C)) → (B → (A → C)) :=
  fun h =>        -- まず、(A → (B → C))という関数 h を受け取る
    fun b =>            -- 次に、B を受け取る
      fun a =>          -- その後に、A を受け取る
         h a b          -- h に a を適用して B → C を得て、次に b を適用して C を得る

--命題論理 練習1
example {A:Prop} {B:Prop} : A → ((A → B) → B) :=
  by
    intro hA --goal : (A → B) → B
    intro hAB --goal : B
    exact hAB hA

--ラムダ式を使った場合の証明
example {A B : Prop} : A → ((A → B) → B) :=
  fun a =>       -- A が真であることを仮定して a : A を受け取る
    fun f =>     -- 次に、A → B という関数 f を受け取る
      f a        -- f に a を適用して B を得る

--命題論理 練習2
example {A:Prop} {B:Prop} : (A → (A → B)) → (A → B) :=
  by
    intro hAAB --goal : A → B
    intro hA --goal : B
    exact (hAAB hA) hA --カッコはなくても同じ


--命題論理 例2
example {A:Prop} {B:Prop} {C:Prop} : ((A ∧ B) → C) → (A → (B → C)) :=
  by
    intro hABC --goal : A → (B → C)
    intro hA --goal : B → C
    intro hB --goal : C
    exact hABC ⟨hA, hB⟩


--命題論理 練習3
example {A:Prop} {B:Prop} : A → (B → (A ∧ B)) :=
  by
    intro hA --goal : B → (A ∧ B)
    intro hB --goal : A ∧ B
    exact ⟨hA, hB⟩

--命題論理 例3
example {A B C D:Prop} : ((A → C) ∧ (B → D)) → ((A ∨ B) → (C ∨ D)):=
  by
    intro hACBD --goal : (A ∨ B) → (C ∨ D).    仮定hACBDの内容は ((A → C) ∧ (B → D))
    intro hAB --goal : C ∨ D.  仮定hABの内容は、 (A ∨ B)
    cases hAB with --ここで (A ∨ B) の左右で場合分け。withを使ったバージョン
    | inl hA => --左の場合。 hAにAが入る。｜は縦棒。
      exact Or.inl (hACBD.left hA) -- goal (C ∨ D)の左側Cを示す。
    | inr hB => --右の場合。 hBにBが入る。
      exact Or.inr (hACBD.right hB) -- goal (C ∨ D)の右側Dを示す。

--例3 ラムダ式を使った場合の証明
example {A B C D : Prop}: ((A → C) ∧ (B → D)) → ((A ∨ B) → (C ∨ D)) :=
  fun h =>
    fun hab =>
      hab.elim
        (fun ha => Or.inl (h.left ha))
        (fun hb => Or.inr (h.right hb))

--命題論理 練習4
example {A:Prop} {B:Prop} {C:Prop} : (A ∨ B → C) → (( A → C) ∧ (B → C)) :=
  by
    intro hABC --goal : (A → C) ∧ (B → C)
    constructor  --かつをそれぞれの場合に分ける。
    · intro hA --goal : C
      exact hABC (Or.inl hA)
    · intro hB --goal : C
      exact hABC (Or.inr hB)

--命題論理 練習5
example {A:Prop} {B:Prop} {C:Prop} : ((A → B) ∨ (A → C)) → (A → B ∨ C) :=
  by
    intro hABAC --goal : A → (B ∨ C)
    intro hA --goal : B ∨ C
    cases hABAC with
    | inl hAB => -- hAB : A → B
      exact Or.inl (hAB hA) --goalのB ∨ Cのうち、左側のBを示す。
    | inr hAC => -- hAC : A → C
      exact Or.inr (hAC hA)

--命題論理 例4
example {A:Prop} {B:Prop} : (A → B) → (¬B → ¬A) :=
  by
    intro hAB --goal : ¬B → ¬A
    intro hNB --goal : ¬A
    intro hA --goal : False  hA:Aが仮定に加わる。
    exact hNB (hAB hA) -- 左が ¬B  右が B  これは矛盾

--命題論理 練習6
example {A:Prop} {B:Prop} : (A → ¬B) → (B → ¬A) :=
  by
    intro hANB --goal : B → ¬A
    intro hB --goal : ¬A
    intro hA --goal : False
    exact (hANB hA) hB


--命題論理 練習7
--Falseは常に偽である、証明できない命題
example {A:Prop}: (A → False) → ¬A := -- Falseとfalseは違う
  by
    intro hAF --goal : ¬A
    intro hA --goal : False
    exact hAF hA

--命題論理 練習8
example {A:Prop}: False ↔ (A ∧ ¬A) :=
  by
    apply Iff.intro --goalを両方向に2つに分解。
    · intro hF --goal : A ∧ ¬A
      cases hF
    · intro ⟨a, na⟩; exact na a  -- 右から左への証明は簡単

--命題論理 例4
example {A:Prop}: ¬¬A → A :=
  by
    intro hNNA --goal : A
    by_contra hA -- goal : False　排中律を利用している。
    exact hNNA hA -- hNNA : ¬¬A  hA : ¬A

--命題論理 練習8
example {A:Prop}: A→¬¬A := --この証明には排中律は必要ない。
  by
    intro hA --goal : ¬¬A
    intro hNA --goal : False --hNA : ¬A
    exact hNA hA -- hA : A

--命題論理 練習9
example (A : Prop) : A → ¬¬A := by
  intro a h
  exact h a

--命題論理 練習10
example {A B : Prop} : ¬(A ∨ B) → (¬ A ∧ ¬ B) := by
  intro h
  constructor
  · intro a
    apply h
    left
    exact a
  · intro b
    apply h
    right
    exact b

--命題論理 練習11
example (A B : Prop) : (¬A ∧ ¬B) → ¬(A ∨ B) := by
  intro h hab
  cases hab with
  | inl ha => exact h.left ha
  | inr hb => exact h.right hb

--命題論理 練習12
example (A B : Prop) : (A → B) → (¬A ∨ B) := by
  intro h
  by_cases ha : A
  case pos =>
    right
    exact h ha
  case neg =>
    left
    exact ha

--命題論理 練習13
example (A B : Prop) : (¬A ∨ B) → (A → B) := by
  intro h ha
  cases h with
  | inl hna => exact False.elim (hna ha)
  | inr hb => exact hb

--スライドの中の例
example (a: A) (b: B) : (A ∧ B : Prop) :=
by
  /- constructor -- goalはA ∧ B。「かつ」の証明を分岐。
  exact a -- 左側の証明が完了
  exact b -- 右側の証明が完了 -/
  exact ⟨a,b⟩ --両方同時に完了。(a,b)ではないので注意。
