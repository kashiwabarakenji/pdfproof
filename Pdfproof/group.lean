import Mathlib.Algebra.Group.Defs
--import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Finiteness
--import Mathlib.Data.Finset.Lattice -- lcm を使うために必要なインポート
import LeanCopilot
--import Mathlib.Algebra.BigOperators.Group.Finset
--import Mathlib.Data.Equiv.Basic

-----------
---練習1----
-----------

-- Gを型として定義し、*という二項演算があるとします
variable {G : Type} [Mul G]

-- 単位元の一意性を示すための定理を定義します
theorem unique_identity (e e' : G) (h_e : ∀ a : G, e * a = a ∧ a * e = a)
    (h_e' : ∀ a : G, e' * a = a ∧ a * e' = a) : e = e' :=
by
  -- e'を右から掛けることにより等式を導きます
  calc
    e = e' * e := by rw [(h_e' e).1]
    _ = e' := by rw [(h_e e').2]

-----------
---練習2----
-----------

-- M をモノイドとする
variable {M : Type} [Monoid M]

-- 逆元の一意性を示す定理
theorem unique_inverse (x y z : M) (hy : x * y = 1 ∧ y * x = 1) (hz : x * z = 1 ∧ z * x = 1) : y = z :=
by
  calc
    y = y * 1 := by rw [mul_one]
    _ = y * (x * z) := by rw [hz.1]
    _ = y * x * z := by rw [mul_assoc]
    _ = 1 * z := by rw [hy.2]
    _ = z := by rw [one_mul]

-----------
---練習3----
-----------

-- 元 x の逆元の逆元が x 自身であることを示す定理
theorem inverse_of_inverse_eq_self (x x_inv y : M) (hx : x * x_inv = 1 ∧ x_inv * x = 1) (hy : x_inv * y = 1 ∧ y * x_inv = 1) : x = y :=
by
  -- hy と hx を利用して証明を進めます
  calc
    x = x * (x_inv * y) := by rw [hy.1, mul_one]
    _ = x * x_inv * y := by rw [mul_assoc]
    _ = 1 * y := by rw [hx.1]
    _ = y := by rw [one_mul]

-----------
---練習5----
-----------

variable {X : Type}

-- 型 `X` 上の全単射を `Perm X` として定義します
def bijectionGroup : Group (Equiv.Perm X) := by infer_instance
/-
{
  mul := Equiv.trans,          -- 写像の合成
  one := Equiv.refl X,              -- 恒等写像
  inv := Equiv.symm,                -- 逆写像
  mul_assoc := Equiv.trans_assoc,   -- 結合律
  one_mul := Equiv.refl_trans,      -- 恒等写像との合成
  mul_one := Equiv.trans_refl,      -- 恒等写像との合成
  inv_mul_cancel := Equiv.symm_trans_self, -- 左逆元の存在
}
-/


-----------
---練習6----
-----------

variable {G : Type} [Group G]

-- 部分群の条件と新しい条件が同値であることを証明
theorem subgroup_condition (H : Set G) :
  (H.Nonempty ∧ ∀ x y : G, x ∈ H → y∈ H → x * y⁻¹ ∈ H) ↔ (∃ S : Subgroup G, S.carrier = H) :=
by
  constructor
  case mp =>
    intro h
    have ⟨h_nonempty, h_condition⟩ := h
    obtain ⟨h, hHnon⟩ := h_nonempty
    -- 任意の x ∈ H を取得
    -- H をキャリアとする部分群を構築
    --この辺りも重複していて無駄だけど使っている。
    have h1 : (1 : G) ∈ H := by
        let tmp :=  h_condition h h hHnon hHnon
        simp at tmp
        exact tmp

    have hinv : ∀ h : G, h ∈ H → h⁻¹ ∈ H := by
      intro h hh
      let tmp := h_condition 1 h h1 hh
      simp at tmp
      exact tmp

    have hxy: ∀ x y : G, x ∈ H → y ∈ H → x * y ∈ H := by
      intro x y hx hy
      let tmp_inv: y⁻¹ ∈ H := hinv y hy
      let tmp_mul: x * (y⁻¹)⁻¹ ∈ H := h_condition x y⁻¹ hx tmp_inv
      simp at tmp_mul
      exact tmp_mul

    let S : Subgroup G :=
    { carrier := H,
      one_mem' := by
        specialize h_condition h h hHnon hHnon
        rw [mul_inv_cancel] at h_condition
        exact h_condition,
      inv_mem' := by
        intro a ha
        specialize h_condition a h ha hHnon
        group at h_condition
        simp_all only [implies_true, and_true, Int.reduceNeg, zpow_neg, zpow_one]
      mul_mem' := by
        intro a b ha hb
        specialize h_condition a (b⁻¹)
        simp_all only [true_and, inv_inv, forall_const]
    }
    use S

  case mpr =>
    intro h
    obtain ⟨S, hS⟩ := h
    rw [←hS]
    subst hS
    simp_all only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid]
    apply And.intro
    · constructor
      · simp_all only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid]
        exact S.one_mem
    · intro x y a a_1
      apply MulMemClass.mul_mem
      · simp_all only
      · simp_all only [inv_mem_iff]

-----------
---練習10----
-----------


-- 任意の有限群 G に対して、全ての元 x に対して x^n = 1 となる正の整数 n が存在することを示す。
--ラグランジュの定理を使って証明している。
theorem exists_universal_order (G : Type) [Fintype G] [Group G] :
  ∃ n : ℕ, 0 < n ∧ ∀ x : G, x ^ n = 1 :=
by
  -- n を群 G の位数とする
  use Fintype.card G
  constructor
  -- n が正であることを示す
  · -- 群の位数は少なくとも 1 である
    exact Fintype.card_pos
  -- 任意の x に対して x^n = 1 であることを示す
  · intro x
    -- Lagrange の定理より、orderOf x は |G| を割り切る
    have h : orderOf x ∣ Fintype.card G := by apply orderOf_dvd_card
    -- n = |G| = orderOf x * k となる k が存在する
    obtain ⟨k, hk⟩ := h
    -- x^n = x^(orderOf x * k) = (x^(orderOf x))^k = 1^k = 1
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
