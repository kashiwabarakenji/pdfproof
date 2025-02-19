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

instance: GCDMonoid ℕ := instGCDMonoidNat --これを探すのも時間がかかった。

theorem gcd_lcm_eq_lcm_gcd (a b c : ℕ) :
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
      simp_all only [Nat.lcm_zero_right, Nat.gcd_zero_right]
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
          simp_all only [Finsupp.inf_apply, Finsupp.sup_apply, nnn]
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
            simp_all only [or_self, lez]
          · intro h
            have : a.lcm c = lcm a c :=
            by
              rfl
            rw [this] at h
            rw [lcm_eq_zero_iff] at h
            simp_all only [or_self]

/- 既存の定理を使わずに証明しようとして、方針は悪くなかったが、定義に戻って証明するのが大変で断念。しばらくしたら消す。
noncomputable def padicVal (p n : Nat) : Nat :=
  if h : p.Prime then
    -- 素数 p に対する定義
    Nat.strongRecOn n fun m IH =>
      if hm:m = 0 then 0
      else if p ∣ m then 1 + IH (m / p) (Nat.div_lt_self (Nat.pos_of_ne_zero (by exact hm)) (Nat.Prime.one_lt h))
      else 0
  else
    0

/-- 記法: v_p(n) を `padicVal p n` の糖衣構文で書けるようにする -/
notation "v_p(" n ", " p ")" => padicVal p n
notation "v_p" => padicVal

/--
「`p^k` が `n` を割り切る」ことと「`v_p(n) ≥ k`」が同値になることを示す。

この定理は，`padicVal p n` の定義を展開しつつ，
- p が素数かどうか
- n = 0 かどうか
- p ∣ n かどうか

などで場合分けをして証明します。
-/
lemma prime_pow_div_iff (p n k : Nat) (hp : p.Prime) :
    p^k ∣ n ↔ v_p(n, p) ≥ k := by
  -- 完全に再帰定義にもとづく場合分けを行なう
  induction n generalizing k with
  | zero =>
    -- n=0 の場合，p^k ∣ 0 は常に真だが，v_p(0,p) = if p.Prime then 0 else 0 なので 0。
    -- 従って「p^k ∣ 0 ↔ 0 ≥ k」は「k=0 のときのみ真」となる。
    -- p^k with k>0 は 0 を割り切るが v_p(0,p)=0 なので≥kは false になる…
    -- ただし Lean の自然数割り算の取り扱いで微妙になるので補足が必要
    -- ここでは p^k | 0 は k≥0 なら常に真ともいえるが v_p(0,p)=0 => k≤0 でないとダメ
    -- ということで最終的には k=0 なら両辺真，k>0 なら両辺偽
    cases k with
    | zero =>
      -- k=0 => p^0=1 ∣ 0 は真，v_p(0,p)=0 ≥ 0 も真
      simp
    | succ k' =>
      -- k>0 => p^(k'+1) ∣ 0 も真だが v_p(0,p)=0 ≥ (k'+1) は偽
      -- Lean 標準の「0 を割り切る」は 0 mod p^(k'+1) = 0 なので「常に真」
      -- よってここの場合分けは矛盾が出ますが，「↔」の両辺偽…？など細かいです。
      -- ひとまず contradiction or 反例… ここは少し丁寧に扱う必要があるが
      -- 細かいことは省略して gcd-lcm 証明には支障ないので sorry でもOKな箇所です。
      apply Iff.intro
      · intro h
        -- ここには到達しないはず
        --simp at h
        simp
        dsimp [padicVal]
        --show k' + 1 ≤ if h:Nat.Prime p then Nat.strongRecOn 0 fun m IH ↦ if hm : m = 0 then 0 else if p ∣ m then 1 + IH (m / p) ⋯ else 0 else 0
        have : v_p(0,p) = 0 := by dsimp [padicVal]; rw [dif_pos hp]; rfl
        simp [this] at h
        sorry
      ·
        intro a
        simp_all only [ge_iff_le, dvd_zero]

  | succ n' IH =>
    -- n>0 の場合
    if hprime : p.Prime then
      -- p は素数
      if hdiv : p ∣ (Nat.succ n') then
        -- p∣(n'+1) => v_p(n'+1,p)=1 + v_p((n'+1)/p,p)
        -- ここでさらに k との大小関係で場合分け
        dsimp [padicVal]
        have : Nat.succ n' = p * (Nat.succ n' / p) := by
          simp_all only [ge_iff_le, Nat.succ_eq_add_one]
          rw [mul_comm]
          rw [Nat.div_mul_cancel hdiv]
        --show (p ^ k ∣ n' + 1) ↔
        --  (if h : Nat.Prime p then
        --  Nat.strongRecOn (n' + 1) fun m IH ↦ if hm : m = 0 then 0 else if p ∣ m then 1 + IH (m / p) ⋯ else 0
        -- else 0) ≥  k
        sorry
      else
        -- p ∣ (n'+1) が成り立たない => v_p(n'+1,p)=0
        show p ^ k ∣ n' + 1 ↔ v_p(n' + 1, p) ≥ k
        apply Iff.intro
        · intro h
          -- ここには到達しないはず
          simp at h
          simp
          dsimp [padicVal]
          --show k ≤ if h : Nat.Prime p then Nat.strongRecOn (n' + 1) fun m IH ↦ if hm : m = 0 then 0 else if p ∣ m then 1 + IH (m / p) ⋯ else 0 else 0
          sorry
        · dsimp [padicVal]
          -- (if h : Nat.Prime p then
          -- Nat.strongRecOn (n' + 1) fun m IH ↦ if hm : m = 0 then 0 else if p ∣ m then 1 + IH (m / p) ⋯ else 0
          -- else 0) ≥   k → p ^ k ∣ n' + 1
          sorry
    else
      -- p が素数でない => 定義上 v_p(n'+1,p)=0
      -- p^k ∣ n'+1 => k=0 でしかあり得ない… など
      simp_all only

theorem gcd_lcm_eq_lcm_gcd (a b c : ℕ) :
    Nat.gcd (Nat.lcm a b) (Nat.lcm a c) = Nat.lcm a (Nat.gcd b c) := by
  -- 場合分け：0 が絡むときは簡単に終わる
  cases a with
  | zero =>
    -- a = 0 の場合，左辺も右辺も最小公倍数や最大公約数が 0 になったりする。
    -- lcm 0 b = 0, gcd 0 b = b などの補題を使えば，ごく簡単に両辺 0=0 が示せる。
    simp_all only [Nat.lcm_zero_left, Nat.gcd_self]
  | succ a' =>
    -- a ≠ 0 の場合はもっと一般的な手法で証明する
    cases b with
    | zero =>
      show ((a' + 1).lcm 0).gcd ((a' + 1).lcm c) = (a' + 1).lcm (Nat.gcd 0 c)
      -- b = 0 の場合は，lcm a 0 = 0, gcd a 0 = a などを使って証明する
      simp_all only [Nat.lcm_zero_right, Nat.gcd_zero_right]
      simp_all only [Nat.gcd_zero_left]
    | succ b' =>
      cases c with
      | zero =>
        simp_all only [Nat.lcm_zero_right, Nat.gcd_zero_right]
      | succ c' =>
        -- ここで、gcd_mul_lcm や dvd_gcd_iff, lcm_dvd_iff を駆使して
        --   gcd(lcm a b, lcm a c) と lcm a (gcd b c) を
        --   いずれも「a*(何か)/gcd(...)」の形に書き表す。
        --  そのうえで「同じ値だ」と示す。
        show ((a' + 1).lcm (b' + 1)).gcd ((a' + 1).lcm (c' + 1)) = (a' + 1).lcm ((b' + 1).gcd (c' + 1))
        sorry

/--
  上記の等式から割り切りがただちに従う。
  すなわち ∀ a b c, gcd(lcm a b, lcm a c) ∣ lcm a (gcd b c).
-/
theorem lcm_gcd_divides_lcm_gcd (a b c : ℕ) :
    Nat.gcd (Nat.lcm a b) (Nat.lcm a c) ∣ Nat.lcm a (Nat.gcd b c) := by
  rw [← gcd_lcm_eq_lcm_gcd]  -- 左辺を右辺と同じ形に書き直す
-/

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
    simp_all only [le_refl, sid]

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

--練習 11は練習6の照明の中で行っている。
--練習 12は、すでにインスタンスが設定されているので省略。
--練習13,14,15,20はTODO。当てはめるだけともいえる。

--練習21と練習22は別ファイル。
