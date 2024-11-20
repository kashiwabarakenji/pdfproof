import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Deprecated.Subgroup

import LeanCopilot

-- 群の準同型写像が単位元を単位元に写すことを示す定理
theorem group_hom_maps_one {G G' : Type _} [Group G] [Group G']
  (f : G →* G') : f 1 = 1 :=
by
  -- 群準同型の性質より、f(1 * 1) = f(1) * f(1) が成り立つ
  -- これより、f(1) = f(1) * f(1) が得られる
  --rw [MonoidHom.map_one] これだけでもOK。モノイドの単位元は単位元に移る。
  have h2 : 1*f 1 = f 1 * f 1 := by
    simp_all only [map_one, mul_one]

  symm
  exact (@mul_right_cancel _ _ _ 1 (f 1) (f 1)) h2


--------------
-----練習2----
--------------

-- 群準同型写像が逆元を逆元に写すことを示す定理
theorem group_hom_map_inv {G G' : Type*} [Group G] [Group G']
  (f : G →* G') (x : G) : f (x⁻¹) = (f x)⁻¹ :=
by
  -- 群準同型の性質より、f(x * x⁻¹) = f(x) * f(x⁻¹) が成り立つ
  have h1 : f (x * x⁻¹) = f x * f x⁻¹ := f.map_mul x x⁻¹

  -- 左辺は f(e_G) であり、e_G は単位元なので f(e_G) = e_G' となる
  have h2 : f (x * x⁻¹) = f 1 := by rw [mul_inv_cancel]
  have h3 : f 1 = 1 := f.map_one

  -- 以上より、1 = f x * f x⁻¹ が成り立つ
  rw [h2, h3] at h1

  -- 群 G' の逆元の性質より、f x⁻¹ は (f x) の逆元である
  simp_all only [map_inv, mul_inv_cancel, map_one]

--------------
-----練習3----
--------------

-- 群準同型写像の像が部分群であることを示す定理 既存の定理を利用した場合。
example {G G' : Type*} [Group G] [Group G']
  (f : G →* G') : IsSubgroup (Set.range f) := by
  exact f.range.isSubgroup

--こちらは定義をしてからinstanceを確認。
def group_hom_image_is_subgroup {G G' : Type*} [Group G] [Group G'] (f : G →* G') : Subgroup (G') :=
{ carrier := Set.range f,
  one_mem' := ⟨1, f.map_one⟩,
  mul_mem' := by
    rintro _ _ ⟨x, hx⟩ ⟨y, hy⟩
    use x * y
    rw [←hx, ←hy]
    exact f.map_mul x y,
  inv_mem' := by
    rintro _ ⟨x, hx⟩
    use x⁻¹
    rw [←hx]
    exact f.map_inv x
}

instance {G G' : Type*} [Group G] [Group G'] (f : G →* G') : Group (group_hom_image_is_subgroup f) :=
{
  mul := λ a b => ⟨a.1 * b.1, (group_hom_image_is_subgroup f).mul_mem' a.2 b.2⟩,
  one := ⟨1, (group_hom_image_is_subgroup f).one_mem'⟩,
  inv := λ a => ⟨a.1⁻¹, (group_hom_image_is_subgroup f).inv_mem' a.2⟩,
  div := λ a b => ⟨a.1 * b.1⁻¹, (group_hom_image_is_subgroup f).mul_mem' a.2 ((group_hom_image_is_subgroup f).inv_mem' b.2)⟩,
  div_eq_mul_inv := λ a b => Subtype.ext (by
  simp_all only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid]
  obtain ⟨val, property⟩ := a
  obtain ⟨val_1, property_1⟩ := b
  simp_all only
  rfl),
  mul_assoc := λ a b c=> Subtype.ext (mul_assoc a.1 b.1 c.1),
  one_mul := λ a => Subtype.ext (one_mul a.1),
  mul_one := λ a => Subtype.ext (mul_one a.1),
  inv_mul_cancel := λ a => Subtype.ext (inv_mul_cancel a.1)
}

--------------
-----練習6----
--------------

-- 群準同型写像の合成が群準同型写像であることを示す定理
def group_hom_comp_is_group_hom {G : Type*} [Group G] (f g : G →* G) : G →* G :=
{
  toFun := g.toFun ∘ f.toFun,  -- 合成写像 g ∘ f を定義
  map_one' := by
    -- (g ∘ f)(1) = g(f(1)) を示す
    rw [Function.comp_apply]  -- 定義により (g ∘ f)(1) = g (f 1)
    simp_all only [OneHom.toFun_eq_coe, map_one]
  map_mul' := by
    -- (g ∘ f)(x * y) = (g ∘ f)(x) * (g ∘ f)(y) を示す
    intros x y                  -- 任意の x, y ∈ G を取る
    simp only [Function.comp_apply, f.map_mul, g.map_mul]    -- 定義により (g ∘ f)(x * y) = g(f(x * y))
    simp_all only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, map_mul]
}

-- 使用例: 自分で定義した合成写像が群準同型であることを確認
example {G : Type*} [Group G] (f g : G →* G) : G →* G :=
  group_hom_comp_is_group_hom f g
