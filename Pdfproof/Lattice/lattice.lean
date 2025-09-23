import LeanCopilot
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Init.Data.Nat.Lcm
import Init.Data.Nat.Gcd
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GCDMonoid.Nat
--import Mathlib.Algebra.MonoidWithZero.Defs

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

instance : Lattice Divides where
  sup a b := Nat.lcm a.val b.val
  le_sup_left a b := Nat.dvd_lcm_left a.val b.val
  le_sup_right a b := Nat.dvd_lcm_right a.val b.val
  sup_le _ _ _ hac hbc := Nat.lcm_dvd hac hbc
  inf a b := Nat.gcd a.val b.val
  inf_le_left a b := Nat.gcd_dvd_left a.val b.val
  inf_le_right a b := Nat.gcd_dvd_right a.val b.val
  le_inf _ _ _ hab hac := Nat.dvd_gcd hab hac

--以下がdistributive latticeを示す部分。

--2025年9月 QwenとChatGPT5の合わせ技。

theorem gcd_lcm_eq_lcm_gcd (a b c : ℕ) :
    Nat.gcd (Nat.lcm a b) (Nat.lcm a c) = Nat.lcm a (Nat.gcd b c) := by
classical
  -- 0 が絡む簡単ケースは先に掃除
  by_cases ha : a = 0
  · -- a = 0 → 両辺とも lcm 0 _ = 0 なので 0
    simp [ha]
  by_cases hb : b = 0
  · -- b = 0 → gcd (lcm a 0) (lcm a c) = gcd 0 (lcm a c) = lcm a c
    --          lcm a (gcd 0 c) = lcm a c
    simp [hb]
  by_cases hc : c = 0
  · -- c = 0 も同様
    simp [hc]

  -- ここから主ケース：a,b,c すべて ≠ 0
  have hL0 : Nat.gcd (Nat.lcm a b) (Nat.lcm a c) ≠ 0 := by
    -- gcd x y = 0 ↔ x=0 ∧ y=0 を使って背理
    intro h
    rcases (Nat.gcd_eq_zero_iff).mp h with ⟨h1, h2⟩
    have : a = 0 ∨ b = 0 := (Nat.lcm_eq_zero_iff).mp h1
    have : a = 0 ∨ c = 0 := (Nat.lcm_eq_zero_iff).mp h2
    simp_all only [Nat.gcd_self, Nat.lcm_eq_zero_iff, or_self]
  have hR0 : Nat.lcm a (Nat.gcd b c) ≠ 0 := by
    -- lcm a d = 0 ↔ a=0 ∨ d=0、gcd b c = 0 ↔ b=0 ∧ c=0
    intro h
    rcases (Nat.lcm_eq_zero_iff).mp h with h' | h'
    · exact ha h'
    · have : b = 0 ∧ c = 0 := (Nat.gcd_eq_zero_iff).mp h'
      exact hb this.1

  -- 以降、factorization の一致を示す
  have hfac :
      (Nat.gcd (Nat.lcm a b) (Nat.lcm a c)).factorization
        = (Nat.lcm a (Nat.gcd b c)).factorization := by
    -- lcm/gcd の factorization を展開して、座標ごとに sup_inf_left を適用
    have h₁ : (a.lcm b).factorization = a.factorization ⊔ b.factorization :=
      Nat.factorization_lcm ha hb
    have h₂ : (a.lcm c).factorization = a.factorization ⊔ c.factorization :=
      Nat.factorization_lcm ha hc
    have h₃ : (b.gcd c).factorization = b.factorization ⊓ c.factorization := by
      exact Nat.factorization_gcd hb hc
    have h₄ : (a.lcm b) ≠ 0 := by
      exact fun h0 => (Nat.lcm_eq_zero_iff.mp h0).elim ha (fun hb0 => hb hb0)
    have h₅ : (a.lcm c) ≠ 0 := by
      exact fun h0 => (Nat.lcm_eq_zero_iff.mp h0).elim ha (fun hc0 => hc hc0)
    -- gcd の factorization も（上で非零を確保したので）展開できる
    have hg : ((a.lcm b).gcd (a.lcm c)).factorization
                = (a.lcm b).factorization ⊓ (a.lcm c).factorization :=
      Nat.factorization_gcd h₄ h₅
    -- ここから計算列。型詰まり回避のため ext p で座標化して sup_inf_left を使う
    ext p
    -- 左辺
    have := congrArg (fun f => f p) hg
    -- 右辺（lcm 側）
    have hr : (Nat.lcm a (Nat.gcd b c)).factorization
                = a.factorization ⊔ (b.gcd c).factorization := by
      -- a ≠ 0 ∧ gcd b c ≠ 0 を示してから lcm の factorization を展開
      have hg0 : Nat.gcd b c ≠ 0 := by
        intro h0; exact hb ((Nat.gcd_eq_zero_iff.mp h0).1)
      simpa using (Nat.factorization_lcm ha hg0)
    -- 置換して座標ごとに分配律 silは必要。
    let sil := sup_inf_left (a := a.factorization p)
                            (b := b.factorization p)
                            (c := c.factorization p)
    simp [h₃, hr]
    simp_all only [ne_eq, Nat.gcd_eq_zero_iff, and_self, not_false_eq_true, Nat.lcm_eq_zero_iff,
      or_self, Finsupp.inf_apply, Finsupp.sup_apply]

  -- 素因数指数の一致から＝を結論（両辺が非零であることは hL0, hR0）
  exact Nat.eq_of_factorization_eq hL0 hR0 (fun p => congrArg (fun f => f p) hfac)

--instance: GCDMonoid ℕ := instGCDMonoidNat --これを探すのも時間がかかった。

--上の定理の2024年版の証明。大きくは違わないのかも。
theorem gcd_lcm_eq_lcm_gcd.old (a b c : ℕ) :
    Nat.gcd (Nat.lcm a b) (Nat.lcm a c) = Nat.lcm a (Nat.gcd b c) := by
  -- We use `Nat.eq_of_factorization_eq`:
  --   Two numbers are equal if, for every prime p, their exponent in
  --   the prime-factorization is the same.
  by_cases ha : a = 0  --0のときを別扱いしないといけないことに気がつくのに時間がかかった。
  case pos =>
    subst ha
    simp_all only [Nat.lcm_zero_left, Nat.gcd_self]
  case neg =>
    by_cases hb : b = 0
    case pos =>
      subst hb
      simp_all only [Nat.lcm_zero_right]
      simp_all only [Nat.gcd_zero_left]
    case neg =>
      by_cases hc : c = 0
      case pos =>
        subst hc
        simp_all only [Nat.lcm_zero_right, Nat.gcd_zero_right]
      case neg =>
        apply Nat.eq_of_factorization_eq
        · intro p
          have h_lcm1 : lcm a b ≠ 0 := by simp_all only [ne_eq, lcm_eq_zero_iff, or_self, not_false_eq_true]
          have h_lcm2 : lcm a c ≠ 0 := by simp_all only [ne_eq, lcm_eq_zero_iff, or_self, not_false_eq_true]
          have h_gcd : gcd (lcm a b) (lcm a c) ≠ 0 :=
          by simp_all only [ne_eq, lcm_eq_zero_iff, or_self, not_false_eq_true, gcd_eq_zero_iff, and_self]
          contradiction
        · intro p
          have h_gcd : gcd b c ≠ 0 := by simp_all only [ne_eq, gcd_eq_zero_iff, and_self, not_false_eq_true]
          have h_lcm : lcm a (gcd b c) ≠ 0 :=
          by simp_all only [ne_eq, gcd_eq_zero_iff, and_self, not_false_eq_true,
            lcm_eq_zero_iff, or_self]
          contradiction
        · intro p
          let nnn := Nat.max_min_distrib_left (Nat.factorization a p) (Nat.factorization b p) (Nat.factorization c p)
          simp at nnn
          rw [Nat.factorization_gcd, Nat.factorization_lcm, Nat.factorization_lcm]
          rw [Nat.factorization_lcm]
          rw [Nat.factorization_gcd]
          simp_all only [Finsupp.inf_apply, Finsupp.sup_apply]
          --補題を適用する時にゼロでないという条件が必要なので後ろでまとめて証明。
          · exact hb
          · exact hc
          · exact ha
          · intro h
            rw [Nat.gcd_eq_zero_iff] at h
            obtain ⟨h1, h2⟩ := h
            contradiction
          · exact ha
          · exact hc
          · exact ha
          · exact hb
          · intro h
            let lez := lcm_eq_zero_iff a b
            have : a.lcm b = lcm a b :=
            by
              rfl
            rw [this] at h
            simp_all only [or_self]
          · intro h
            have : a.lcm c = lcm a c :=
            by
              rfl
            rw [this] at h
            rw [lcm_eq_zero_iff] at h
            simp_all only [or_self]

------------------
------練習6--------
------------------


-- ℝ^2 の上の順序の定義: (x1, y1) >= (x2, y2) ⇔ x1 >= x2 かつ y1 >= y2
@[ext]
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

theorem sup_inf_distrib (a b c : R2) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  -- 各成分ごとに等式を示す
  ext
  · -- x成分について
    apply max_min_distrib_left
  · -- y成分について
    apply max_min_distrib_left

theorem inf_sup_distrib (a b c : R2) :
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  -- 各成分ごとに等式を示す
  ext
  · -- x成分について
    apply min_max_distrib_left
  · -- y成分について
    apply min_max_distrib_left

-- 分配束であることの証明。練習11の内容。
noncomputable instance : DistribLattice R2 where
  le_sup_inf a b c := by
    let sid := sup_inf_distrib a b c
    simp_all only [le_refl]

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

----練習8--------
variable {L : Type*} [Lattice L]
--この問題は、inf_eq_leftそのまま。
theorem lattice_le_iff_inf_eq:
  ∀ x y:L, x ≤ y ↔ x ⊓ y = x :=
by
  intro x y
  apply Iff.intro
  · intro h
    exact inf_eq_left.mpr h
  ·
    intro a
    simp_all only [inf_eq_left]
    --theorem inf_eq_left : a ⊓ b = a ↔ a ≤ b :=
    --le_antisymm_iff.trans <| by simp [le_rfl]

--同じ問題をやや基本的なところから証明。
theorem lattice_le_iff_inf_eq_sup_eq' :
    ∀ x y:L, x ≤ y ↔ x ⊓ y = x := by
  intro x y
  constructor
  · intro h
    -- `x ⊓ y` は `x, y` の greatest lower bound（GLB）
    -- よって `x ⊓ y ≤ x`
    have h₁ : x ⊓ y ≤ x := inf_le_left
    -- また `x ≤ y` より `x` は `x ⊓ y` の lower bound
    have h₂ : x ≤ x ⊓ y := le_inf le_rfl h
    -- `x ⊓ y ≤ x` かつ `x ≤ x ⊓ y` なので等号成立
    exact le_antisymm h₁ h₂
  · intro h
    -- `x ⊓ y = x` より `x ≤ x ⊓ y`
    rw [←h]
    -- `x ⊓ y` の定義より `x ⊓ y ≤ y`
    exact inf_le_right

--練習9
theorem meet_join_distrib_right :
    ∀ x y z : L, x ⊓ (y ⊔ z) ≥ (x ⊓ y) ⊔ (x ⊓ z) := by
  intro x y z
  -- `x ⊓ y ≤ x ⊓ (y ⊔ z)` と `x ⊓ z ≤ x ⊓ (y ⊔ z)` を示せば
  -- `sup_le` を使って結論が得られる
  apply sup_le
  · apply inf_le_inf_left x
    apply le_sup_left
  · apply inf_le_inf_left x
    apply le_sup_right

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

      simp_all only [inf_le_left, sup_of_le_right, le_inf_iff, and_self, Y, X, Zb]
      rw [inf_assoc]
      rw [inf_comm]
      rw [inf_comm (b ⊔ c) b]
      rw [inf_sup_self]
      simp_all only [inf_le_right]


    let left_hand:= Y ⊔ (X ⊓ Zb)
    let right_hand:= (Y ⊔ Zb) ⊓ (Y ⊔ X)
    have left_eq: Y ⊔ (X ⊓ Zb) = Y := by
      simp_all only [sup_of_le_left, X, Y, Zb]
    have right_eq: (Y ⊔ Zb) ⊓ (Y ⊔ X) = X := by
      simp_all only [sup_of_le_left, X, Y, Zb]
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

      simp_all only [inf_le_left, sup_of_le_right, le_inf_iff, and_self, Y, X, Zb]
      rw [inf_assoc]
      rw [inf_comm]
      rw [inf_comm (b ⊔ c) b]
      rw [inf_sup_self]
      simp_all only [inf_le_right]

    let left_hand:= Y ⊔ (X ⊓ Zb)
    let right_hand:= (Y ⊔ Zb) ⊓ (Y ⊔ X)
    have left_eq: Y ⊔ (X ⊓ Zb) = Y := by
      simp_all only [sup_of_le_left, X, Y, Zb]
    have right_eq: (Y ⊔ Zb) ⊓ (Y ⊔ X) = X := by
      simp_all only [sup_of_le_left, X, Y, Zb]
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

--練習 11は練習6の照明の中で行っている。
--練習 12は、すでにインスタンスが設定されているので省略。
--練習13,14,15,20はTODO。当てはめるだけともいえる。

--練習21と練習22は別ファイル。
