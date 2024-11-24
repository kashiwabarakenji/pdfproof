----------
----濃度---
----------
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Logic.Function.Basic
import LeanCopilot
import Mathlib.Data.Real.Basic  --これがあるとuseが使える。Mathlib.Tactic.Useがよみこまれているのかも。
import Mathlib.Analysis.SpecialFunctions.Log.Basic
--import Mathlib.Data.Rat.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Cardinality
--import Mathlib.Data.Equiv.Basic

--import Mathlib.SetTheory.Countable.Basic
--import Mathlib.Data.PProd.Basic
--import Mathlib.Topology.Instances.Real
--import Mathlib.Topology.Separation
--import Mathlib.Topology.DenseEmbedding
--import Mathlib.Topology.MetricSpace.Basic -- Add this import for `exists_countable_dense_subset`

--checkをうまく働かせるにもこのインポートが必要。checkがこれを使っているのかも。

--import Mathlib.Tactic.Basic
--import Mathlib.Data.Set.Function
--import Mathlib.Init.Data.Nat.Lemmas
--import Mathlib.Order.Basic
--import Mathlib.Order.Defs
--import Mathlib.Data.Equiv.Basic

------------
---練習1
------------

-- 集合の濃度が等しいという関係を全単射が存在することとして定義します。
def same_cardinality (X Y : Set α) : Prop :=
  ∃ (f : X → Y), Function.Bijective f

-- 反射律: 任意の集合 X について、X は自分自身と濃度が等しい。
theorem same_cardinality_refl (X : Set α) : same_cardinality X X :=
by
  exists id
  constructor
  · exact Function.injective_id
  · exact Function.surjective_id

-- 対称律: 濃度が等しい関係は対称的。
theorem same_cardinality_symm {X Y : Set α} (h : same_cardinality X Y) : same_cardinality Y X :=
by
  rcases h with ⟨f, hf⟩
  obtain ⟨g, hg⟩ := Function.bijective_iff_has_inverse.mp hf
  exists g
  constructor
  · exact Function.RightInverse.injective hg.2
  · obtain ⟨left, _⟩ := hg
    exact left.surjective

-- 推移律: 濃度が等しい関係は推移的。
theorem same_cardinality_trans {X Y Z : Set α} (hXY : same_cardinality X Y) (hYZ : same_cardinality Y Z) :
  same_cardinality X Z :=
by
  rcases hXY with ⟨f, hf⟩
  rcases hYZ with ⟨g, hg⟩
  exists g ∘ f
  constructor
  · exact Function.Injective.comp hg.1 hf.1
  · exact Function.Surjective.comp hg.2 hf.2

------------
---練習2----
------------

-- 集合 A と B が濃度が等しいとき、その冪集合も濃度が等しいことを示す
theorem power_set_same_cardinality {A B : Set α} (ff: A →  B) (h : Function.Bijective ff) :
  ∃ (g : Set A → Set B), Function.Bijective g :=
by
  -- 濃度が等しい関係から全単射 f を取り出す
  --rcases h with ⟨f, hf⟩

  -- 冪集合の各要素に対応する写像を定義する
  let gg : Set A → Set B := λ (S:Set A) => { y | ∃ x ∈ S, ff x = y }

  -- この g が全単射であることを証明する
  exists gg
  constructor
  -- Injective の証明
  · intros S₁ S₂ h_eq
    ext x
    constructor
    · intro hx
      have : ff x ∈ gg S₁ := ⟨x, hx, rfl⟩
      rw [h_eq] at this
      rcases this with ⟨x₂, hx₂, hfx⟩
      exact h.1 hfx ▸ hx₂
    · intro hx
      have : ff x ∈ gg S₂ := ⟨x, hx, rfl⟩
      rw [←h_eq] at this
      rcases this with ⟨x₁, hx₁, hfx⟩
      exact h.1 hfx ▸ hx₁

  -- Surjective の証明 任意のTに対して、g S = T となる S が存在することを示す。
  · intro T
    let S := { x | ff x ∈ T } --Tに移るようなAの元を集めて、Sとする。
    exists S
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, hfx⟩
      have hx' : ff x ∈ T := hx
      rw [hfx] at hx'
      exact hx'
    · ----
      intro hy
      simp_all only [Subtype.exists, Set.mem_setOf_eq, gg, S]
      --have h_inv := Function.bijective_iff_has_inverse.mp h
      --#check h.2 --h.right : Function.Surjective ff
      have hy' := h.2 y
      obtain ⟨x, hx2⟩ := hy' --hx2 : ff x = y
      subst hx2
      obtain ⟨val, property⟩ := x --val ∈ A
      --goal ∃ a, ∃ (h : a ∈ A), ff ⟨a, ⋯⟩ ∈ T ∧ ff ⟨a, ⋯⟩ = ff ⟨val, property⟩
      use val
      simp_all only [and_self, exists_const]

------------
---練習3----
------------
--自然数全体から偶数全体への全単射を作る。
-- 偶数であることの定義
def is_even (n : ℕ) : Prop := ∃ k : ℕ, n = 2 * k

-- 偶数全体の集合
def even_numbers : Set ℕ := { n | is_even n }

-- 写像 f : ℕ → even_numbers を定義
def f (n : ℕ) : even_numbers := ⟨2 * n, ⟨n, rfl⟩⟩

lemma f_range: ∀n: ℕ, (f n : ℕ) ∈ even_numbers := by
  intro n
  use n
  rfl

-- f が単射であることの証明
lemma f_injective : Function.Injective f := by
  intros a b h
  -- 仮定 h : f a = f b がある場合、2 * a = 2 * b を意味する
  dsimp [f] at h
  simp_all only [Subtype.mk.injEq, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]

-- f が全射であることの証明。帰納法なんて使わなくても、直接構成できるのでは。
lemma f_surjective : Function.Surjective f := by
  dsimp [Function.Surjective]
  simp_all
  intro b hb
  dsimp [even_numbers] at hb
  dsimp [is_even] at hb
  obtain ⟨k, hk⟩ := hb
  subst hk
  exact ⟨k, rfl⟩

theorem f_bijective : Function.Bijective f :=
  ⟨f_injective, f_surjective⟩

------------
---練習4----
------------

-- 正の実数全体の集合をサブタイプとして定義
def pos_real := {x : ℝ // 0 < x}

-- 関数 f: ℝ → pos_real を定義。f(x) = e^x
noncomputable def exp_to_pos_real : ℝ → pos_real := λ x=> ⟨Real.exp x, Real.exp_pos x⟩

-- 関数 g: pos_real → ℝ を定義。g(s) = ln(s.val)
noncomputable def g : pos_real → ℝ := λ s => Real.log s.val

-- ℝ と pos_real 間の同型 (equiv) を構成
noncomputable def real_pos_real_equiv : ℝ ≃ pos_real :=
{ toFun := exp_to_pos_real,
  invFun := g,
  left_inv := λ x => by
    -- g(f(x)) = ln(e^x) = x を証明
    simp [g, exp_to_pos_real, Real.log_exp],

  right_inv := λ s => Subtype.eq (by
    -- f(g(s)) = e^{ln(s)} = s を証明
    simp [exp_to_pos_real, g]
    exact Real.exp_log s.2
  )
}

------------
---練習5----
------------

-- A ⊆ B ならば、card A ≤ card B であることの証明
example (α β : Type) (h : α → β) (h_inj : Function.Injective h) : Cardinal.mk α ≤ Cardinal.mk β := by
  exact Cardinal.mk_le_of_injective h_inj

------------
---練習6----
------------

--写像 全射fの逆向きの単射gを構成。Lean by Exampleの問題。片側のみ。

theorem surj_to_inj {A B : Type} (f : A →B) (hf : ∀b : B, ∃a : A, f a = b) :∃g : B →A, ∀x y : B, g x = g y →x = y :=
by
  -- ‘f‘ が全射であることから、逆向きの写像‘g‘ を構成するために、‘hf‘ から具体的な‘a‘ を取得
  let g : B →A := fun b =>
    (hf b).choose -- のLean ‘choose‘ を使って要素を選びます
  -- ‘g(b)‘ の性質を確認
  have hg : ∀b : B, f (g b) = b := fun b =>
     (hf b).choose_spec -- ‘choose_spec‘ により、選択した要素が‘f (g b) = b‘ を満たすことを確認。選択公理を使用
  -- 存在する写像‘g‘ とその単射性の証明を提供
  apply Exists.intro g
  intro x y h
  -- ‘g(x) = g(y)‘ ならば‘f(g(x)) = f(g(y))‘ よりx = y が成り立つ
  calc
  x = f (g x) := (hg x).symm
  _ = f (g y) := by rw [h]
  _ = y := hg y

------------
---定理1----
------------

-- 集合 M の巾集合の濃度が M の濃度より真に大きいことを示す
example (M : Type) : Cardinal.mk M < Cardinal.mk (Set M) :=
by
  -- 巾集合の濃度は M の濃度より大きい (カントールの定理)
  have tmp: 2^(Cardinal.mk M) = Cardinal.mk (Set M) := by
    simp_all only [Cardinal.mk_set]
  let result := Cardinal.cantor (Cardinal.mk  M)
  rw [tmp] at result
  exact result

------------
---練習7----
------------

def f7 {α : Type*} (s : α) : Set α := {s}

-- f が単射であることを証明。定理を利用。
theorem f7_injective {α : Type*} : Function.Injective (@f7 α) := by
  apply Set.singleton_injective

--直接的な定理を使わずに証明。
theorem f7_injective2 {α : Type*} : Function.Injective (@f7 α) := by
  dsimp [Function.Injective]
  intros a b h
  rw [f7] at h
  rw [f7] at h
  simp_all only [Set.singleton_eq_singleton_iff]--{a} = {b} となるとき、a = b となる定理。

------------
---練習8----
------------

--すでに定義されている濃度の順序に関しては、すでに半順序の構造が入っている。

example : PartialOrder Cardinal := by
  infer_instance

-- 反射律: 任意のカーディナリティ a に対して、a ≤ a が成り立つ
example (a : Cardinal) : a ≤ a := by
  apply le_refl

-- 反対称律: 任意のカーディナリティ a, b に対して、a ≤ b かつ b ≤ a ならば a = b が成り立つ
example (a b : Cardinal) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  apply le_antisymm h₁ h₂

-- 推移律: 任意のカーディナリティ a, b, c に対して、a ≤ b かつ b ≤ c ならば a ≤ c が成り立つ
example (a b c : Cardinal) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  apply le_trans h₁ h₂

-----------
---練習9---
-----------

open Cardinal

theorem countable_integers : #ℤ = aleph0 := by
  -- ℕ と ℤ の間に全単射（equiv）を構成
  let f : ULift ℕ ≃ ℤ := {
    toFun := λ n => if n.down % 2 = 0 then n.down / 2 else -((n.down + 1) / 2),
    invFun := λ z => ⟨if 0 ≤ z then 2 * Int.natAbs z else 2 * Int.natAbs z - 1⟩,
    left_inv := by
      have left_inv_lem: Function.LeftInverse (fun z ↦ if 0 ≤ z then 2 * z.natAbs else 2 * z.natAbs - 1) fun n ↦
       if n % 2 = 0 then Int.ofNat (n / 2) else -Int.ofNat ((n + 1) / 2) := by
        intro n
        by_cases h : 0 ≤ n
        · simp
          split_ifs with h₁ h₂ h₃
          · simp_all only [zero_le]
            norm_cast
            omega
          · simp_all only [not_le]
            exfalso
            omega
          · simp_all only [zero_le, Nat.mod_two_ne_zero, Left.nonneg_neg_iff, Int.natAbs_neg]
            exfalso
            omega
          · simp_all only [zero_le, Nat.mod_two_ne_zero, Left.nonneg_neg_iff, not_le, Int.natAbs_neg]
            symm
            omega

        · simp
          split_ifs with h₁ h₂ h₃
          · simp_all only [zero_le, not_true_eq_false]
          · simp_all only [zero_le, not_true_eq_false]
          · simp_all only [zero_le, not_true_eq_false]
          · simp_all only [zero_le, not_true_eq_false]
      simp_all only [Int.ofNat_eq_coe, Int.ofNat_ediv, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      tauto

    right_inv := by
      intro z
      by_cases h : 0 ≤ z
      · simp_all only [↓reduceIte, Nat.mul_mod_right, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_natAbs, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, abs_eq_self]
      · simp_all only [not_le, Nat.cast_ite, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_natAbs]
        split
        next h_1 =>
          simp_all only [Nat.mul_mod_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            mul_div_cancel_left₀, abs_eq_self]
        next h_1 =>
          simp_all only [not_le]
          split
          next h_1 =>
            norm_cast
            simp_all only [Int.ofNat_ediv, Nat.cast_ofNat]
            omega
          next h_1 =>
            simp_all only [Nat.mod_two_ne_zero]
            omega
    }
  -- ℕ ≃ ℤ なのでカーディナリティが等しいことが言える
  exact Cardinal.mk_congr f.symm

-----------
---練習10---
-----------

def NatPos : Type := {n : ℕ // n > 0}
instance : Nonempty NatPos := ⟨⟨1, by decide⟩⟩
def NatPosSet : Set ℕ := {n | n > 0}  --NatPosだけだと、Setにならない。

theorem natPos_countable : Countable NatPos := by
  -- 自然数から ℕ⁺ への全単射を定義
  let f : ℕ → NatPos := λ n => ⟨n + 1, Nat.succ_pos n⟩

  have NatPosNonempty : Set.Nonempty NatPosSet := ⟨1, Nat.succ_pos 0⟩

  -- f が全単射であることを証明
  have f_bij : Function.Bijective f := by
    constructor
    -- 単射性の証明
    { intros a b h
      dsimp [f] at h
      rw [Subtype.mk.injEq] at h
      exact Nat.succ.inj h
    }
    -- 全射性の証明
    { intro p
      obtain ⟨m, hm⟩ := p
      use m - 1
      dsimp [f]
      rw [Subtype.mk.injEq]
      exact Nat.succ_pred_eq_of_pos hm
    }

  -- f が全単射であるため、NatPos は可算である
  simp_all only [f]

  exact (Set.countable_iff_exists_surjective NatPosNonempty).2 ⟨f, fun p => f_bij.2 p⟩

theorem int_countable : Set.Countable (Set.univ : Set ℤ) := by
   exact Set.countable_univ

-- インスタンス: ℤ × ℕ⁺ が可算であることを示す
theorem int_natPos_countable : Countable (Set.prod (Set.univ : Set ℤ) NatPosSet) := by
  -- ℤ × ℕ⁺ は可算な集合の積
  apply Set.Countable.prod int_countable natPos_countable
  -- ℤ が可算であること

--#check Set.prod (Set.univ : Set ℤ) NatPosSet

-- 関数定義: ℤ × ℕ⁺ → ℚ を定義

def int_natPos := (Set.prod (Set.univ : Set ℤ) NatPosSet)

def int_natPos_to_Q (p : int_natPos): ℚ :=
  p.1.1 / (p.1.2 : ℤ)



-- 定理: 有理数 ℚ が可算であることを示す
theorem q_countable : Set.Countable (Set.univ: Set ℚ) := by
  /-
  --使ってない
  have int_natPos_Nonempty : int_natPos.Nonempty := by
    use 1
    dsimp [int_natPos]
    simp [NatPosSet]
    simp [Set.prod]

  -- ℤ × ℕ⁺ から ℚ への全射を構築 使ってない
  have suj: ∃ f : int_natPos →  ℚ, Function.Surjective f := ⟨int_natPos_to_Q, by
    intro q
    simp_all only [Subtype.exists, Prod.exists]
    let z := q.num
    let d := q.den
    --obtain ⟨val, property⟩ := q
    --obtain ⟨fst, snd⟩ := val
    have d_pos : d > 0 := q.den_pos
    use z
    use d
    simp [int_natPos_to_Q]
    simp_all only [gt_iff_lt, d, z]
    apply And.intro
    · exact ⟨Set.mem_univ q.num, q.den_pos⟩
    · exact q.num_div_den
  ⟩
  -/

  have suj_func: Function.Surjective int_natPos_to_Q := by
    intro q
    simp_all only [Subtype.exists, Prod.exists]
    let z := q.num
    let d := q.den
    have d_pos : d > 0 := q.den_pos
    use z
    use d
    simp [int_natPos_to_Q]
    simp_all only [d, z]
    apply And.intro
    · exact ⟨Set.mem_univ q.num, q.den_pos⟩
    · exact q.num_div_den

  haveI : Countable ℚ := Set.countable_univ_iff.mp q_countable
  let result := Function.Surjective.countable suj_func
  simp_all only [result]
  apply Set.countable_univ


-----------
---練習12---
-----------

theorem infinite_card_eq_aleph0 {A : Type} (hA : Infinite A) (h : #A ≤ aleph0) : #A = aleph0 := by
  apply le_antisymm
  · exact h
  · -- A が無限集合であるため、自然数から A への単射が存在
    exact Cardinal.aleph0_le_mk A

-----------
---定理4---片側のみ
-----------

--直接には使ってないが、基本の原理
theorem exists_rat_in_open_interval (a b : ℝ) (h : a < b) : ∃ q : ℚ, a < q ∧ (q : ℝ) < b := by
  -- 実数の密度性を利用して、有理数近似を求める
  --#check @exists_rat_btwn _ _ (Real.instArchimedean) a b h
  obtain ⟨q, hq⟩ := exists_rat_btwn h
  -- q が a と b の間にあることを確認する
  use q

--とりあえず、片側だけ示した。もう片方は、10進展開を使ったりして、大変そうなので、とりあえずは保留。
theorem real_card_le_set_of_rational  : #ℝ ≤ 2^#ℚ := by
  let real_to_rational_subset_type : ℝ → Set ℚ := λ r => {q : ℚ | r ≤ (q : ℝ)}
  have func_inj: Function.Injective real_to_rational_subset_type := by
    intros x y h
    simp_all only [real_to_rational_subset_type]
    by_contra hxy_ne
    -- 実数の順序性に基づき、仮定に矛盾を導く
    cases lt_or_gt_of_ne hxy_ne with
    | inl hlt =>
      -- x < y の場合
      have ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have hq : ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y := ⟨q, hq1, hq2⟩
      cases hq with
      | intro q hq_props =>
        --消すと動かない。
        have _ : q ∉  real_to_rational_subset_type y := by
          simp [real_to_rational_subset_type]
          by_cases hq : ↑q = y
          case pos =>
            rw [hq] at hq_props
            subst hq
            simp_all only [Rat.cast_le, Rat.cast_lt, le_refl, and_true, lt_self_iff_false, or_true]
          case neg =>
            obtain ⟨_, right⟩ := hq_props
            contrapose! hq
            linarith

        have q_in_x_set : q ∈ real_to_rational_subset_type x := by
          simp [real_to_rational_subset_type]
          simp_all only [Set.mem_setOf_eq, not_le, real_to_rational_subset_type]
          obtain ⟨left, _⟩ := hq_props
          exact le_of_lt left
        simp_all only [Set.mem_setOf_eq, not_le, real_to_rational_subset_type]
        obtain ⟨_, right⟩ := hq_props
        linarith

    | inr hgt =>
      -- y < x の場合（対称性により同様の処理を適用）
      have ⟨q, hq1, hq2⟩ := exists_rat_btwn hgt
      have hq : ∃ q : ℚ, y < (q : ℝ) ∧ (q : ℝ) < x := ⟨q, hq1, hq2⟩
      cases hq with
      | intro q hq_props =>
        have q_not_in_x_set : q ∉ real_to_rational_subset_type x := by
          simp [real_to_rational_subset_type]
          exact hq_props.right
        have q_in_y_set : q ∈ real_to_rational_subset_type y := by
          simp_all only [gt_iff_lt, Set.mem_setOf_eq, not_le, real_to_rational_subset_type]
          obtain ⟨left,_⟩ := hq_props
          linarith
        simp_all only [gt_iff_lt, not_true_eq_false, real_to_rational_subset_type]

  let result := @Cardinal.mk_le_of_injective ℝ (Set ℚ) real_to_rational_subset_type func_inj
  simpa using result --#R <= #(Set ℚ)から #R <= 2^#Q に変換

--定理をちょっと使って、逆方向も一応証明しておく。本当に証明するのは大変そう。
theorem cardinality_nat_subset_le_real :
  (2 ^ (#ℕ)) = (#ℝ) :=
by
  -- `Cardinal.nat_power_aleph0` を用いて、2以上の自然数の指数が実数の濃度であることを示す。
  have h : (2 : Cardinal) ^ ℵ₀ = #ℝ := by
    --rw [←mk_nat]
    rw [←Cardinal.continuum]
    exact Cardinal.mk_real.symm
  simp_all only [two_power_aleph0, mk_eq_aleph0]
