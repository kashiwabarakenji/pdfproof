--pdf proof by Lean
import LeanCopilot
import Mathlib.Data.Real.Basic
--import Mathlib.Data.Set.Basic
--import Mathlib.Tactic.ByContra
--import Mathlib.Init.Data.Nat.Lemmas
--import Mathlib.Logic.Relation
--import Mathlib.Data.Set.Function
--import Mathlib.Logic.Function.Basic


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
    · simp  -- 右から左への証明は簡単

--命題論理 例4
example {A:Prop}: ¬¬A → A :=
  by
    intro hNNA --goal : A
    by_contra hA -- goal : False　排中律を利用している。import Mathlib.Tactic.ByContraが必要。
    exact hNNA hA -- hNNA : ¬¬A  hA : ¬A

--命題論理 練習8
example {A:Prop}: A→¬¬A := --この証明には排中律は必要ない。
  by
    intro hA --goal : ¬¬A
    intro hNA --goal : False --hNA : ¬A
    exact hNA hA -- hA : A

--命題論理 練習9
example (A : Prop) : A → ¬¬A := by
  intro a
  intro h
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
  intro h
  intro hab
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
  intro h
  intro ha
  cases h with
  | inl hna => exact False.elim (hna ha)
  | inr hb => exact hb

--スライドの中の例
example (a: (A : Prop))  (b: (B :Prop)):(A ∧ B:Prop):=
by
  /- constructor -- goalはA ∧ B。「かつ」の証明を分岐。
  exact a -- 左側の証明が完了
  exact b -- 右側の証明が完了 -/
  exact ⟨a,b⟩ --両方同時に完了。(a,b)ではないので注意。

--- 述語論理

--述語論理 練習1
example : ∀ (x: Real),∃ (y :Real), x = y :=  -- Realとℝは同じ。実数全体の集合。
  by
    intro x --goal : ∃ (y : Real), x = y
    exact ⟨x, rfl⟩ -- rflは、両辺が等しいことを示す。

--述語論理 練習2
def my_prime (n : ℕ) : Prop :=
  n > 1 ∧ ∀ m : ℕ, m ∣ n → m = 1 ∨ m = n


example :∀ (x : ℝ), x*x ≥ 0 :=
  by
    intro x --goal : x * x ≥ 0
    exact (mul_self_nonneg x)

--述語論理 練習3
example {y : ℝ} : (∀(x : ℝ), x*x ≥ y*y) ↔ y = 0 :=
  by
    apply Iff.intro
    · intro h --goal : y ≥ 0
      simp_all only [ge_iff_le, le_refl]
      contrapose! h
      use 0
      simp_all only [mul_zero, mul_self_pos, ne_eq]
      simp_all only [not_false_eq_true]
    · intro h --goal : ∀ (x : ℝ), x * x ≥ y * y
      intro x --goal : x * x ≥ y * y
      subst h
      simp_all only [mul_zero, ge_iff_le]
      apply mul_self_nonneg

--述語論理 練習3 ラムダ式を使った証明
example (y : ℝ) : (∀ x, x ^ 2 ≥ y ^ 2) ↔ y = 0 :=
  Iff.intro
    (fun h => by
      -- h: ∀x, x² ≥ y²
      -- 特にx = 0の場合、0 ≥ y² なので y² ≤ 0 となり y = 0
     contrapose! h
     use 0
     simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
     positivity
      )
    (fun h x =>
      by
        subst h       -- h: y = 0 を代入
        simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    )

--述語論理 例1
-- P(x)とは書かずに P xと書く。
example {P: α → Prop} {Q: α → Prop}: (∀ x : α, P x → Q x) → ((∀ x : α, P x) → (∀ x : α, Q x)) :=
  by --ここで　α　は型変数
    intro h1 h2 --h1 : ∀ (x : α), P x → Q x, h2 : ∀ (x : α), P x
    intro x --allの除去・goalはQ x
    apply h1 --goalがP xに。
    apply h2 --h2を適用してゴールが得られるので証明完了。

--上と同じ命題の証明を、ラムダ式で証明を書いたもの。
example {α : Type} {P: α → Prop} {Q: α → Prop}:
  (∀ x : α, P x → Q x) → ((∀ x : α, P x) → (∀ x : α, Q x)) := λ hPQ hP x => hPQ x (hP x)

--述語論理 例2
example {α : Type} {P: α → Prop}: (∀x, (A → P x)) → (A → ∀x, P x) :=
  by
    intro a a_1 --a : ∀ (x : α), A → P x, a_1 : A
    intro x
    apply a
    exact a_1

--少し別の書き方
example {α : Type} {P: α → Prop}{A: Prop}:  (∀x, (A → P x)) → (A → ∀x, P x) :=
  by
    intro a a_1 x
    exact a x a_1

--上と同じ命題の証明を、ラムダ式で証明を書いたもの。
example {α : Type} {P: α → Prop} {A: Prop}:
  (∀x, (A → P x)) → (A → ∀x, P x) := λ hAP hA x => hAP x hA

--述語論理 練習5
example {α : Type} {P: α → Prop}:  (A → ∀x, P x) → (∀x, (A → P x)) :=
  by
    intro a x a_1
    exact a a_1 x

--上と同じ命題の証明を、ラムダ式で証明を書いたもの。
example {α : Type} {P: α → Prop} {A: Prop}:
  (A → ∀x, P x) → (∀x, (A → P x)) := λ hA x hAx => hA hAx x

--述語論理 例3 --スライドにもobtainを使う例として登場。existsの中身を取り出す。
example {α : Type} {P: α → Prop} {Q: α → Prop}: (∀x,(P x → Q x)) → ((∃x, P x) → ∃x, Q x) :=
  by
    intro a a_1 --a : ∀ (x : α), P x → Q x, a_1 : ∃ (x : α), P x
    obtain ⟨w, h⟩ := a_1 --a1の中身をwとhに分解 a1 : ∃ (x : α), P x , w : α, h : P w
    exact ⟨w, a w h⟩ --a wは、P w → Q w  カッコの記号に注意。

--上と同じ命題の証明を、useを使って書いたもの。
example {α : Type} {P: α → Prop} {Q: α → Prop}: (∀x,(P x → Q x)) → ((∃x, P x) → ∃x, Q x) :=
  by
    intro a a_1 --a : ∀ (x : α), P x → Q x, a_1 : ∃ (x : α), P x
    obtain ⟨w, h⟩ := a_1 --a1の中身をwとhに分解 a1 : ∃ (x : α), P x , w : α, h : P w
    use w -- exists　xとしてwを使う。
    exact (a w) h --a wは、P w → Q w

--述語論理 例4
--スライドのuseを使う例。existsの中身を与える。
example {α : Type} {P: α → Prop} {A: Prop}:(∃x,(A ∧ P x)) → (A ∧ ∃x,P x) :=
  by
    intro a
    obtain ⟨xx, h⟩ := a --h : A ∧ P x
    --cases' a with xx h  obtainの代わりにこっちでも良い。
    constructor
    · exact h.1 -- A
    · use xx -- exists　xとしてxxを使う。
      exact h.2 -- P xx

--述語論理 練習7
example {α : Type} {P: α → Prop} {A: Prop}: (A ∧ ∃x, P x) → ∃x, (A ∧ P x) :=
  by
    intro a
    obtain ⟨aa, h⟩ := a
    obtain ⟨x1, hh⟩ := h
    use x1

--述語論理 例5
example {α : Type} {P: α → Prop}: ¬(∃x, P x) → ∀x,¬(P x) :=
  by
    intro a x
    rw [not_exists] at a  --そのまま利用しているのでずるいかも。
    exact a x

--例5を定理を使わずに証明。
example {α : Type} {P : α → Prop} : ¬(∃ x, P x) → ∀ x, ¬(P x) :=
by
  intro h
  intro x --ここでゴールは、¬P x
  intro px --px：P xとなり、goalがFalseになる。
  have ex : ∃ x, P x := ⟨x, px⟩ --補題を証明してexと命名
  exact h ex -- ¬A A  の順で並べることで矛盾Falseが得られる。

--述語論理 練習8
example {α : Type} {P: α → Prop}: (∀x, ¬P x) → (¬∃x, P x) :=
  by
    intro a
    rw [not_exists]
    exact a

example {α : Type} {P : α → Prop} : (∀x, ¬P x) → (¬∃x, P x) :=
by
  intro h -- Introduce the hypothesis that ∀x, ¬P x.
  intro hp -- Introduce a new hypothesis for the negation of the existential quantifier.
  obtain ⟨x, px⟩ := hp -- Extract the witness `x` and `P x` from the existential statement.
  exact h x px -- Apply the universally quantified `h` to `x` and `P x` to reach a contradiction.

--述語論理 練習9
example {α : Type} {P: α → Prop}: (¬∀x,P x) → ∃x,¬P x :=
  by
    intro a
    rw [not_forall] at a
    exact a

--述語論理 練習10
example {α : Type} {P: α → Prop}: (∃x,¬P x) → ¬∀x, P x :=
  by
    intro a
    rw [not_forall]
    exact a

example {α : Type} {P : α → Prop} : (∃x, ¬P x) → ¬(∀x, P x) :=
by
  intro h -- Introduce the hypothesis that ∃x, ¬P x.
  by_contra h1 -- Assume the opposite (that ∀x, P x).
  obtain ⟨x, px⟩ := h -- Extract the witness `x` and `¬P x`.
  exact px (h1 x) -- Apply `h1` (∀x, P x) to this specific `x`, reaching a contradiction.

--述語論理 練習11
example (P Q : α → Prop) : (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x) := by
  intro h
  constructor
  · intro x
    exact (h x).1
  · intro x
    exact (h x).2

--述語論理 練習12
example (P Q : α → Prop) : (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  intro a x
  exact ⟨a.1 x, a.2 x⟩

--述語論理 練習13
example (P Q : α→Prop) :(∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x) :=
by
 intro h
 intro x
 cases h with
 | inl h1 =>
   exact Or.inl (h1 x)
 | inr h2 =>
   exact Or.inr (h2 x)

example{α:Type}{P Q:α→Prop}:(∀x:α,P x)∨(∀x:α,Q x)→(∀x:α,P x ∨ Q x):=
by
  intro h --ゴールが∀x:α,P x ∨ Q xの構成になり、項 h:(∀x:α,P x)∨(∀x:α,Qx)が作られる
  cases h with --h:(∀x:α,P x)∨(∀x:α,Q x)で場合分け
  | inl hP => --hP:∀x:α,P x
    intro x --ゴールが P x ∨ Q xの構成になり、項 x:αが作られる
    exact Or.inl (hP x) --hP xで P xが作られ、Orの導入でゴールを作れるので証明終了
  | inr hQ => --hQ:∀x:α,Q x
    intro x --ゴールが P x ∨ Q xの構成になり、項 x:αが作られる
    exact Or.inr (hQ x)
