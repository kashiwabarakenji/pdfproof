import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Deprecated.Subgroup
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.Group.Subsemigroup.Basic

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
--isSubgroupは、Deprecatedな関数。
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
    intro x hx
    simp_all only [Set.mem_range]
    obtain ⟨w, h⟩ := hx
    subst h
    apply Exists.intro
    · exact f.map_inv w
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

--------------
-----練習7----
--------------

def group_hom_ker_is_subgroup {G G' : Type*} [Group G] [Group G']
  (f : G →* G') : Subgroup G :=
{
  carrier := { x : G | f x = 1 },  -- 核をキャリアとする
  one_mem' := by
    -- 単位元が核に含まれることを示す
    simp only [Set.mem_setOf_eq, f.map_one],
  mul_mem' := by
    -- 核の2つの元の積が核に含まれることを示す
    intro x y hx hy
    simp_all only [Set.mem_setOf_eq, map_mul, mul_one],
  inv_mem' := by
    -- 核の元の逆元が核に含まれることを示す
    intro x hx
    simp_all only [Set.mem_setOf_eq, map_inv, inv_one],
}

instance {G G' : Type*} [Group G] [Group G'] (f : G →* G') : Group (group_hom_ker_is_subgroup f) :=
{
  mul := λ a b => ⟨a.1 * b.1, (group_hom_ker_is_subgroup f).mul_mem' a.2 b.2⟩,
  one := ⟨1, (group_hom_ker_is_subgroup f).one_mem'⟩,
  inv := λ a => ⟨a.1⁻¹, (group_hom_ker_is_subgroup f).inv_mem' a.2⟩,
  div := λ a b => ⟨a.1 * b.1⁻¹, (group_hom_ker_is_subgroup f).mul_mem' a.2 ((group_hom_ker_is_subgroup f).inv_mem' b.2)⟩,
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
-----練習8----
--------------

-- 群準同型写像の単射性と核の関係に関する定理
theorem groupHom_injective_iff_ker_trivial {G G' : Type*} [Group G] [Group G']
  (f : G →* G') : Function.Injective f ↔ f.ker = ⊥ := by

  constructor
  -- 必要条件: f が単射ならば ker f = {1_G}
  · intro h_inj
    ext x
    constructor
    ·  -- {x | f x = 1} ⊆ {1_G}
      intro hx
      -- f x = 1_G ならば x = 1_G を示す
      have h : x = 1 := h_inj (by rw [hx, f.map_one])
      exact h
    ·  -- {1_G} ⊆ {x | f x = 1}
      intro h1
      simp_all only [Subgroup.mem_bot]
      subst h1
      apply OneMemClass.one_mem

  ·  -- 十分条件: ker f = {1_G} ならば f が単射
    intro hker
    intros x y hxy
    -- f x = f y ならば x = y を示す
    have h : f (x * y⁻¹) = 1 := by
      rw [f.map_mul]
      rw [hxy]
      rw [f.map_inv]
      simp
    -- x * y⁻¹ ∈ ker f
    have : x * y⁻¹ ∈ f.ker := by
      --dsimp [MonoidHom.ker]
      exact h

    have : x * y⁻¹ = 1 := by
      simp_all only [map_mul, map_inv, mul_inv_cancel, Subgroup.mem_bot]
    -- x * y⁻¹ = 1_G となるため、x = y である
    rw [mul_eq_one_iff_eq_inv] at this
    simp at this
    exact this

-- 使用例: 準同型写像 f が単射であることを確認
example {G G' : Type*} [Group G] [Group G']
  (f : G →* G') (h : f.ker = ⊥) : Function.Injective f :=
  (groupHom_injective_iff_ker_trivial f).mpr h

--------------
-----練習9----
--------------

-- f が G から G' への同型写像である場合、f⁻¹ が G' から G への同型写像であることを証明
theorem inv_is_group_isomorphism {G G' : Type} [Group G] [Group G']
  (f : G →* G') (h : Function.Bijective f) :
  ∃ g : G' →* G, Function.Bijective g ∧ (∀ x : G, g (f x) = x) ∧ (∀ y : G', f (g y) = y) :=
by
  -- f⁻¹ を定義するため、h から逆写像を取得
  let g := MulEquiv.symm (MulEquiv.ofBijective f h)
  use g.toMonoidHom
  constructor
  -- g が全単射であることを示す
  · exact g.bijective
  -- f と g が逆写像の性質を満たすことを示す
  · constructor
    -- g (f x) = x
    · intro x
      simp_all only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, g]
      symm
      simp [MulEquiv.ofBijective]
    -- f (g x) = x
    · intro y
      simp_all only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.ofBijective_apply_symm_apply, g]

-------------------
------練習10--------
--------------------

-- 群 G の自己同型写像の集合が群であることを示したいが、Mathlib 4では、MulAut G はすでに群のinstance。
variable {G : Type} [Group G]
#check Group (MulAut G)

lemma div_inv (G : Type) [Group G] [Semigroup (MulAut G)] (a b : MulAut G) : a / b = a * b⁻¹ :=
by
  rfl

instance semigroup_mul_aut (G : Type) [Group G] : Semigroup (MulAut G) :=
{
  mul := λ f g => f.trans g, -- 写像の合成
  mul_assoc := λ _ _ _ => MulEquiv.ext (λ _ => rfl), -- 結合律の証明
}

instance mul_one_class_mul_aut (G : Type) [Group G] : MulOneClass (MulAut G) :=
{
  mul := (· * ·), -- 前述の `Semigroup` インスタンスの `mul` を再利用
  one := MulEquiv.refl G, -- 恒等写像
  mul_one := λ _ => MulEquiv.ext (λ _ => rfl), -- 右単位元の証明
  one_mul := λ _ => MulEquiv.ext (λ _ => rfl), -- 左単位元の証明
}

instance group_mul_aut (G : Type) [Group G] : Group (MulAut G) :=
{
  mul := (· * ·), -- 前述の `Semigroup` インスタンスの `mul` を再利用
  one := MulEquiv.refl G, -- 恒等写像
  inv := λ f => f.symm, -- 逆写像
  mul_assoc := λ f g h => MulEquiv.ext (λ x => rfl), -- 結合律の証明
  one_mul := MulOneClass.mul_one, -- 既に定義済みの左単位元を再利用
  mul_one := MulOneClass.mul_one, -- 既に定義済みの右単位元を再利用
  inv_mul_cancel := λ f => MulEquiv.ext (λ x => f.symm_apply_apply x), -- 逆元との積が単位元であることの証明
}

-------------------
------練習13--------
-------------------

--最初からアーベル群の部分群は、正規部分群であると、instanceで設定されている。
theorem abelian_group_subgroup_normal {G : Type*} [CommGroup G]
  {H : Subgroup G} : H.Normal := by
  -- 正規部分群の定義に基づいて証明
  infer_instance

-------------------
------練習14--------
-------------------

variable {G : Type*} [Group G]
variable (H : Subgroup G)
--variable (f : H → H)

-- 正しい書き方：
--#check Set.image f (Set.univ : Set H)
--#check f '' (Set.univ : Set H)

--結構使っているが、xをx^(-1)にしたものも作っても良かったかも。もしくは、直接conj_memを使っても良かったかも。
lemma conj_mem_normal {G : Type*} [Group G] {H : Subgroup G}
  (H_normal : H.Normal) (x : G) (h : G) (h_mem : h ∈ H) : x * h * x⁻¹ ∈ H :=
by
    -- H が正規部分群であるため、x * H * x⁻¹ = H
    exact H_normal.conj_mem h h_mem x

-- 定理: 群 G の部分群 H が正規部分群であることの必要十分条件は、
-- 任意の x ∈ G に対して xH = Hx であることである。
theorem normal_iff_left_cosets_eq_right_cosets {G : Type*} [Group G] {H : Subgroup G} :
  H.Normal ↔ ∀ x : G, (Set.image (λ h=> x * h) H) = (Set.image (λ h => h * x) H) :=
  by
  constructor
  · -- 正規部分群 H から ∀x, Set.image (λ h => x * h) H = Set.image (λ h => h * x) H を示す
    intro h_normal
    intro x
    -- 定義: f : H → H を h ↦ x * h * x⁻¹ とする
    --have elem: ∀ h ∈ H, x * h * x⁻¹ ∈ H := by

    let f : H → H := λ h => ⟨x * h * x⁻¹, h_normal.conj_mem h h.2 x⟩
    let g : H → H := λ h => ⟨x⁻¹ * h * x, by
      let h_norm:=h_normal.conj_mem h h.2 x⁻¹
      simp at h_norm
      exact h_norm⟩

    -- f が全単射であることを示す。使ってなかった。
    /-
    have f_bij : Function.Bijective f :=
        -- f は単射であることの証明
        by
          constructor
          · intro h1 h2
            intro a
            simp_all only [Subtype.mk.injEq, mul_left_inj, mul_right_inj, SetLike.coe_eq_coe, f]

          · intro h
            -- h = x * (x⁻¹ * h * x) * x⁻¹ となるので、x⁻¹ * h * x ∈ H である
            use ⟨x⁻¹ * ↑h * x, by
            let conj := conj_mem_normal h_normal x⁻¹ h h.2
            simp at conj
            exact conj⟩
            simp_all only [f]
            obtain ⟨val, property⟩ := h
            simp_all only [Subtype.mk.injEq]
            simp [mul_assoc]
    -/

    -- 任意の h ∈ H に対して、x * h = f h * x であることを示す。コメントアウトするとエラー。
    have _ : ∀ (h : G) (hh : h ∈ H), x * h = (f ⟨h, hh⟩) * x :=
      by
        intro h hh
        simp only [Function.comp_apply]
        simp only [mul_assoc]
        simp_all only [inv_mul_cancel, mul_one, f]

    -- Set.image (λ h => x * h) H = Set.image (λ h => f h * x) H であることを示す
    have h1 : Set.image (λ h => x * h) H.carrier = Set.image (λ h => f h * x) (Set.univ:Set H.carrier) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨h, hH, rfl⟩
        --goal (fun h ↦ x * h) h ∈ (fun h ↦ ↑(f h) * x) '' Set.univ
        rw [Set.mem_image]
        use f ⟨x⁻¹ * h * x, by
          let h_norm := h_normal.conj_mem h hH x⁻¹
          simp at h_norm
          exact h_norm
          ⟩
        constructor
        · exact Set.mem_univ (f ⟨h, hH⟩)
        · --↑(f (f ⟨h, hH⟩)) * x = (fun h ↦ x * h) h
          dsimp [f]
          simp_all
          rw [←mul_assoc]
          rw [←mul_assoc]
          rw [mul_inv_cancel]
          rw [one_mul]
          rw [mul_assoc]
          rw [mul_inv_cancel]
          simp_all only [mul_one, f]

      · intro hy
        rcases hy with ⟨h, _, rfl⟩
        use (↑h : G)
        constructor
        · exact h.2
        · -- (fun h ↦ x * h) ↑h = (fun h ↦ ↑(f h) * x) h
          dsimp [f]
          simp_all

-- Set.image (λ h => f h * x) H = Set.image (λ h => h * x) H であることを示す
    have h2 : Set.image (λ h => f h * x) (Set.univ:Set H.carrier) = Set.image (λ h => x * h) H := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨h, _, rfl⟩
        rw [Set.mem_image]
        use h
        constructor
        · simp_all
        · -- (fun h ↦ f h * x) h = (fun h ↦ x * h) h
          dsimp [f]
          simp_all
      · intro hy
        rcases hy with ⟨h, hH, rfl⟩
        use ⟨x⁻¹ *f ⟨h, hH⟩*x, by
          dsimp [f]
          rw [mul_assoc]
          rw [mul_assoc]
          simp
          exact hH
          ⟩
        constructor
        · exact Set.mem_univ (f ⟨h, hH⟩)
        · -- (fun h ↦ f h * x) (f ⟨h, hH⟩) = (fun h ↦ x * h) ⟨h, hH⟩
          dsimp [f]
          simp_all
          rw [mul_assoc]
          rw [mul_assoc]
          simp
    ext z
    apply Iff.intro
    · intro h
      rw [Set.mem_image] at h
      rw [Set.mem_image]
      obtain ⟨hr, hrH, rfl⟩ := h
      have :  x * hr ∈ (fun h ↦ x * h) '' H.carrier  := by
        rw [Set.mem_image]
        use hr
        constructor
        · dsimp [f]
          exact hrH
        · rfl
      rw [h1] at this
      rw [Set.mem_image] at this
      use f ⟨hr, hrH⟩
      constructor
      · dsimp [f]
        simp_all
        exact conj_mem_normal h_normal x hr hrH
      · dsimp [f]
        simp_all
    · intro h
      rw [Set.mem_image] at h
      rw [Set.mem_image]
      obtain ⟨hr, hrH, rfl⟩ := h
      have :  f ⟨hr, hrH⟩ * x ∈ (fun h ↦ f h * x) '' Set.univ  := by
        rw [Set.mem_image]
        use ⟨hr,hrH⟩--f ⟨hr, hrH⟩
        constructor
        · simp
        · rfl
      rw [h2] at this
      rw [Set.mem_image] at this
      use g ⟨hr, hrH⟩
      constructor
      dsimp [f]
      simp_all
      let h_conj := conj_mem_normal h_normal x⁻¹ hr hrH
      simp at h_conj
      exact h_conj

      dsimp [f]
      rw [←mul_assoc]
      rw [←mul_assoc]
      simp_all

   -- ∀x, Set.image (λ h => x * h) H = Set.image (λ h => h * x) H から H.Normal を示す
  · intro h_cosets_eq
    -- H.Normal の定義を構築する
    constructor
    intro hh hx
    -- Set.image (λ h => x * h) H = Set.image (λ h => h * x) H を利用する
    -- 定義: f : H → H を h ↦ x * h * x⁻¹ とする

    intro g

    --一般的な補題なので、定理の外に出しても良かった。
    have lem0 {A B:Set G}:A=B → (Set.image (λ x=> g * x) A) = (Set.image (λ x => g * x) B):= by
      intro eq
      rw [eq]
    --#check h_cosets_eq g
    --#check lem0 (h_cosets_eq g⁻¹)
    have lem1: (fun xx ↦ g * xx) '' ((fun xx ↦ g⁻¹ * xx) '' ↑H) = (fun xx ↦ g * xx) '' ((fun xx ↦ xx * g⁻¹) '' ↑H):= by
      exact lem0 (h_cosets_eq g⁻¹)
    simp only [Set.image_image] at lem1
    simp only [←mul_assoc] at lem1
    simp at lem1

    have lem3 : ((fun xx ↦ g⁻¹ * xx) '' ↑H) =  ((fun xx ↦ xx*g⁻¹) '' ↑H) := by
      exact h_cosets_eq g⁻¹
    have lem4: (fun xx ↦ g * xx) '' ((fun xx ↦ xx * g⁻¹) '' H) = (fun xx ↦ g * xx) '' ((fun xx ↦ g⁻¹ * xx) '' H) := by
      exact lem0 lem3.symm

    simp at lem4
    have lem5: (fun xx ↦  g * (xx * g⁻¹)) '' H  =  (fun xx ↦ g * xx) '' ((fun xx ↦ xx * g⁻¹) '' H) := by
      rw [Set.image_image]
    have lem6: (fun xx ↦  (xx)) '' H  =  (fun xx ↦ g * xx) '' ((fun xx ↦ g⁻¹ * xx) '' H) := by
      rw [Set.image_image]
      have : (fun x ↦ g * (g⁻¹ * x)) = (fun x ↦ (g * g⁻¹) * x) := by
        funext x
        rw [mul_assoc] -- 結合律: hh * (hh⁻¹ * x) = (hh * hh⁻¹) * x
      rw [this]
      funext x
      simp

    simp at lem5
    simp at lem6
    rw [←lem5] at lem4
    rw [←lem6] at lem4
    have lem7:  H = (fun a ↦ g * a * g⁻¹) '' H := by
      exact lem1
    have lem8 : g * hh * g⁻¹ ∈ (fun a ↦ g * a * g⁻¹) '' H := by
      simp only [Set.mem_image]
      use hh
      constructor
      · exact hx
      · simp
    rw [←lem7] at lem8
    exact lem8
