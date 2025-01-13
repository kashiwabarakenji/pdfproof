import LeanCopilot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic

variable {α : Type}  [DecidableEq α] [Fintype α]

structure SetFamily (α : Type) [DecidableEq α] [Fintype α] where
  (ground: Finset α)
  (sets : Finset α → Prop)
  (inc_ground : sets s → s ⊆ ground)

structure SetFamily.preclosure_operator (F : SetFamily α) where
  (Family : SetFamily α)
  (cl : Finset F.ground → Finset F.ground)
  (extensive : ∀ s : Finset F.ground, s ⊆ cl s)
  (monotone : ∀ s t : Finset F.ground, s ⊆ t → cl s ⊆ cl t)

structure SetFamily.closure_operator (F : SetFamily α) extends SetFamily.preclosure_operator F where
  (idempotent : ∀ s : Finset F.ground, cl s = cl (cl s))

structure ClosureSystem (α : Type) [DecidableEq α]  [Fintype α] extends SetFamily α where
  (intersection_closed : ∀ s t , sets s → sets t → sets (s ∩ t))
  (has_ground : sets ground)

def finsetIntersection {α : Type} [DecidableEq α]
  (family : Finset (Finset α)) : Finset α :=
  (family.sup id).filter (fun x => ∀ f ∈ family, x ∈ f)

--closure systemでないと全体集合が含まれないので、証明できないかも。
lemma extensive_from_SF_finset {α : Type} [DecidableEq α] [Fintype α] [DecidableEq (Set α)][Fintype (Set α)]
  (F : ClosureSystem α)[DecidablePred F.sets]:
  ∀ s : Finset F.ground, s ⊆
      let cl := fun s =>
      let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
      let ios := finsetIntersection (F.ground.powerset.filter (fun (t:Finset α) => F.sets t ∧ sval ⊆ t))
     ios.subtype (λ x => x ∈ F.ground)
   cl s :=
by
  simp
  intro s
  dsimp [finsetIntersection]
  simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp]
  rw [Finset.map_eq_image]
  simp
  intro x hx
  rw [@Finset.mem_subtype]
  rw [Finset.mem_filter]
  simp
  constructor

  obtain ⟨val, property⟩ := x
  simp_all only
  use F.ground
  simp_all only [subset_refl, and_true, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    exists_const]
  apply And.intro
  · simp_all only
  · apply And.intro
    · exact F.has_ground
    · simp [Finset.image_subset_iff]

  intro f a a_1 a_2
  obtain ⟨val, property⟩ := x
  simp_all only
  apply a_2
  simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]

/- Setに帰着させるアプローチ。Fintypeが証明できなくて、挫折。
lemma extensive_from_SF_set {α : Type} [DecidableEq α] [Fintype α] [DecidableEq (Set α)][Fintype (Set α)]
  (F : SetFamily α)[DecidablePred F.sets]:
  ∀ s : Finset F.ground, s ⊆
      let cl := fun s =>
      let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
      let ios := ((F.ground.powerset.filter (fun (t:Finset α) => F.sets t ∧ sval ⊆ t)).image (fun ss => (ss.toSet))).toSet.sInter
      haveI : Fintype ↑ios := by
          sorry
     ios.toFinset.subtype (λ x => x ∈ F.ground)
   cl s :=
  by
    intro s
    simp_all only [Finset.coe_image, Finset.coe_filter, Finset.mem_powerset, Set.sInter_image, Set.mem_setOf_eq,
      eq_mpr_eq_cast]
    intro x hx
    simp_all only [Finset.coe_image, Finset.coe_filter, Finset.mem_powerset, Set.sInter_image, Set.mem_setOf_eq,
      Finset.mem_subtype, Set.mem_toFinset, Set.mem_iInter, Finset.mem_coe, and_imp]
    intro i a a_1 a_2
    obtain ⟨val, property⟩ := x
    simp_all only
    apply a_2
    simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,
      exists_const]
-/
