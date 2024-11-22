import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.GroupTheory.Order.Min

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
---練習14-----
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

------------
---練習16-----
------------

-- 環準同型の核がイデアルであることを証明
example {R R' : Type} [Ring R] [Ring R'] (f : R →+* R') :
  Ideal R :=
by
  -- 核を定義
  let ker_f : AddSubgroup R := {
    carrier := { x : R | f x = 0 },
    zero_mem' := by exact RingHom.map_zero f,
    add_mem' := by
      intros x y hx hy
      have hxy: f (x + y) = 0 := by
       calc
        f (x + y) = f x + f y := RingHom.map_add f x y
        _ = 0 + 0 := by rw [hx, hy]
        _ = 0 := add_zero 0
      exact hxy,

    neg_mem' := by
      intros x hx
      have hx: f x = 0 := by exact hx
      have hnx: f (-x) = 0 := by
        calc
          f (-x) = -f x := RingHom.map_neg f x
          _ = -0 := by rw [hx]
          _ = 0 := neg_zero
      exact hnx
  }
  -- 外部乗法閉包性
/-
  have h_add : ∀ x y, x ∈ ker_f → y ∈ ker_f → x + y ∈ ker_f := by
    intros x y hx hy
    have hxy: f (x + y) = 0 := by
      calc
        f (x + y) = f x + f y := RingHom.map_add f x y
        _ = 0 + 0 := by rw [hx, hy]
        _ = 0 := add_zero 0
    exact hxy

  have h_mul : ∀ x ∈ ker_f, ∀ r : R, r * x ∈ ker_f := by
    intros x hx r
    have hrx: f (r * x) = 0 := by
     calc
      f (r * x) = f r * f x := RingHom.map_mul f r x
      _ = f r * 0 := by rw [hx]
      _ = 0 := mul_zero (f r)
    exact hrx
  -- 以上より核はイデアル
  -/
  exact ⟨ker_f.toAddSubmonoid, by
    intros c x hx
    have hcx: f (c • x) = 0 := by
      calc
        f (c • x) = f c * f x := RingHom.map_mul f c x
        _ = f c * 0 := by rw [hx]
        _ = 0 := mul_zero (f c)
    exact hcx⟩

------------
---練習18-----
------------

example (p : ℕ) [hp : Fact (Nat.Prime p)] : Field (ZMod p) :=
by
  -- ZMod p が整域である
  --haveI : CommRing (ZMod p) := ZMod.commRing p
  haveI : IsDomain (ZMod p) := inferInstance
  -- ZMod p が有限体であることから、Field である
  exact ZMod.instField p

------------
---練習23-----
------------

-- 体が整域であることを証明
example {R : Type} [Field R] : IsDomain R :=
by
  exact inferInstance
  -- 体は可換で単位元を持つ環であるため、IsDomain の要件を満たす
  -- 零因子が存在しないことを示す
  /-intro a b h
  by_cases ha : a = 0
  · -- a = 0 の場合
    left
    exact ha
  · -- a ≠ 0 の場合
    right
    have h_inv : a * a⁻¹ = 1 := mul_inv_cancel ha
    calc
      b = 1 * b := (one_mul b).symm
      _ = (a * a⁻¹) * b := by rw [h_inv]
      _ = a⁻¹ * (a * b) := by rw [mul_assoc]
      _ = a⁻¹ * 0 := by rw [h]
      _ = 0 := by rw [mul_zero]
  -/
