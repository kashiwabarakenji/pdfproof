import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import LeanCopilot
import Mathlib.Algebra.BigOperators.Group.Finset
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

    -- (→)方向：新しい条件から部分群の条件を満たすことを証明
  · intro h
    obtain ⟨hH_nonempty, hH⟩ := h
    -- 部分群の生成を定義
    let S := Subgroup.closure H
    use S
    ext x
    constructor
    -- (←) x ∈ S → x ∈ H
    · intro hx
      have h1 : (1 : G) ∈ H := by
        obtain ⟨h, hHnon⟩ := hH_nonempty
        let tmp := hH h h hHnon hHnon
        simp at tmp
        exact tmp

      have hinv : ∀ h : G, h ∈ H → h⁻¹ ∈ H := by
        intro h hh
        let tmp := hH 1 h h1 hh
        simp at tmp
        exact tmp

      have hxy: ∀ x y : G, x ∈ H → y ∈ H → x * y ∈ H := by
        intro x y hx hy
        let tmp_inv: y⁻¹ ∈ H := hinv y hy
        let tmp_mul: x * (y⁻¹)⁻¹ ∈ H := hH x y⁻¹ hx tmp_inv
        simp at tmp_mul
        exact tmp_mul

      exact Subgroup.closure_induction hx (fun h hH => hH) h1 hxy hinv
      --exact @Subgroup.closure_induction G _ _ _ _ hx (fun h hH => hH) h1 hxy hinv

    · intro a
      simp_all only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, S]
      exact Subgroup.subset_closure a

  -- (→) x ∈ H → x ∈ S
  · intro h
    obtain ⟨S, hS⟩ := h
    subst hS
    simp_all only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid]
    apply And.intro
    · use 1
      simp_all only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid]
      apply OneMemClass.one_mem
    · intro x y a a_1
      apply MulMemClass.mul_mem
      · simp_all only
      · simp_all only [inv_mem_iff]
