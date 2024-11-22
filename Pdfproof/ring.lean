import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Group.Defs

------------
---練習3-----
------------

-- 環 R の性質
example (R : Type) [Ring R] (h : (1 : R) = (0 : R)) :
  ∀ x : R, x = 0 :=
by
  intro x
  -- 1 * x = x と 0 * x = 0 を考える
  have h1 : 1 * x = x := by rw [one_mul]
  have h2 : 0 * x = 0 := by rw [zero_mul]
  -- 仮定 1 = 0 を用いる
  rw [h] at h1
  -- 1 * x = 0 * x = 0 より x = 0
  rw [h2] at h1
  exact h1.symm

------------
---練習7-----
------------

-- 環 R とイデアル I, J を考える。もともとLeanに組み込まれている定理を使って、証明している。
example {R : Type} [Ring R] [GroupWithZero R] (I J : Ideal R) :
  Ideal R := by
  -- 共通部分 I ∩ J がイデアルであることを示す
  let K := I ⊓ J
  exact K

------------
---練習8-----
------------

-- 環 R とその元 a が可逆元である場合
def ring_mul_inv {R : Type} [DivisionRing R] (a : R) (ha : IsUnit a) :
  RingHom R R :=
{ toFun := fun x : R => a * x * a⁻¹,
  map_one' := by
    --#check @IsUnit.mul_inv_cancel R _ a ha
    have h_inv: a * a⁻¹ = 1 := IsUnit.mul_inv_cancel ha
    --have h_inv2: a⁻¹ * a = 1 := by
    --exact IsUnit.inv_mul_cancel ha
    calc
      a * 1 * a⁻¹ = 1 := by
        rw [mul_one]
        rw [h_inv],

  map_mul' := by
    intro x y
    calc
      a * (x * y) * a⁻¹ = a * x * (y * a⁻¹) := by
        rw [←mul_assoc]
        rw [mul_assoc]
  _= (a * x) * 1 * (y * a⁻¹) := by
        rw [mul_one]
  _= (a * x) * (1) * (y * a⁻¹) := by
        rfl
  _= (a * x) * (a⁻¹ * a) * (y * a⁻¹) := by
        rw [IsUnit.inv_mul_cancel ha]
  _= (a * x * a⁻¹) * (a * y * a⁻¹) := by
        rw [←mul_assoc]
        rw [←mul_assoc]
        rw [mul_assoc]
        rw [mul_assoc]
        simp_all
        constructor
        rw [mul_assoc],
  map_add' := by
    intro x y
    calc
      a * (x + y) * a⁻¹ = a * x * a⁻¹ + a * y * a⁻¹ := by rw [mul_add, add_mul],
  map_zero' := by
    calc
      a * 0 * a⁻¹ = 0 := by rw [mul_zero, zero_mul]
}
