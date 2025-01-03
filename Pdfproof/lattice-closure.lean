import LeanCopilot
--import Mathlib.Order.BoundedOrder
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Lattice.Basic

variable {α : Type}  [DecidableEq α] [Fintype α]

/-
structure LatticeClosure (α : Type) [PartialOrder α] where
  (lattice : Lattice α)
  (closure : Set α)
  (closure_lattice : Lattice closure)
  (closure_le : ∀ x y : α, x ≤ y → x ∈ closure → y ∈ closure)
  (closure_sup : ∀ x y : closure, x.1 ⊔ y.1 ∈ closure)
-/

structure SetFamily (α : Type) [DecidableEq α] [Fintype α] where
  (ground: Finset α)
  (sets : Finset α → Prop)
  (inc_ground : sets s → s ⊆ ground)

structure SetFamily.closure_operator (F : SetFamily α) where
  (Family : SetFamily α)
  (cl : Finset F.ground → Finset F.ground)
  (extensive : ∀ s : Finset F.ground, s ⊆ cl s)
  (monotone : ∀ s t : Finset F.ground, s ⊆ t → cl s ⊆ cl t)
  (idempotent : ∀ s : Finset F.ground, cl s = cl (cl s))

structure ClosureSystem (α : Type) [DecidableEq α]  [Fintype α] extends SetFamily α where
  (intersection_closed : ∀ s t , sets s → sets t → sets (s ∩ t))
  (has_ground : sets ground)

/--
任意の有限集合族 `S` に対して、
`S.fold (· ∩ ·) Finset.univ id` は「`S` のすべての要素(集合)の共通部分」を表す。

- `S.fold` は Finset 上で定義されている畳み込み操作。
- 第一引数 `(· ∩ ·)` は積集合(共通部分)演算子。
- 第二引数 `Finset.univ` は畳み込みの初期値 (ここでは全体集合)。
- 第三引数 `id` は要素をそのまま扱う関数。fold の定義上必須の引数です。
-/
--使ってない。集合のほうにもってきて考えるのは、筋が良くないかも。Listのほうに変換して共通部分をとったほうがいい。それがこの次の補題。
theorem finset_subfamily_intersection_closed {α : Type*} [DecidableEq α]
    (A : Finset α) (A0 : Finset (Finset α))
    (nonemptyA0 : A0.Nonempty)
    (h : ∀ X ∈ A0, X ⊆ A) : (⋂ x ∈ A0.toSet, x) ⊆ A.toSet := by
  -- 共通部分の要素xを取る
  intro y
  intro hy
  -- 共通部分の定義により、任意のX ∈ A0に対してy ∈ X
  rw [@Set.mem_def] at hy

  -- A0.toSetの任意の要素に対してyが含まれることを示す
  have h1 : ∀ X ∈ A0, y ∈ X := by
    intro X hX
    simp_all only [Finset.mem_coe]
    apply hy
    simp_all only [Set.mem_range]
    apply Exists.intro
    · ext x : 1
      simp_all only [Set.mem_iInter, Finset.mem_coe]
      apply Iff.intro
      intro a
      on_goal 2 => {
        intro a i
        exact a
      }
      simp_all only [forall_const]
      exact a
  -- A0の要素Xを1つ取る（A0が空でない場合）
  by_cases h_empty : A0.Nonempty
  -- 空でない場合
  case pos =>
    obtain ⟨X, hX⟩ := h_empty
    -- XはAの部分集合
    have hXA := h X hX
    -- yはXの要素
    have hyX := h1 X hX
    -- AはFinsetなのでtoSetを使って変換
    simp_all only [Finset.mem_coe]
    apply h
    · exact hX
    · simp_all only
  -- A0が空の場合
  case neg =>
    simp_all only

--clの定義のところで使うつもりだったが現状で使ってない。本当は使う必要があって、定義がよくないのかもしれない。
--帰納法で示しているが、帰納的な仮定を使わずに証明できる命題だった。
theorem finset_subfamily_intersection_closed_list {α : Type} [DecidableEq α][Fintype α]
    (A : Finset α) (A0 : Finset (Finset α))
    (nonemptyA0 : A0.Nonempty)
    (h : ∀ X ∈ A0, X ⊆ A) : A0.toList.foldr (λ x acc => x ∩ acc) Finset.univ ⊆ A :=
by
  match v:A0.toList with
  | List.nil => simp_all
  | List.cons hd tl =>

    have hdin : hd ∈ A0.toList := by
      simp_all

    have asub : ∀ X ∈ A0.toList, X ⊆ A := by
      intro X
      intro hX
      apply h
      simp_all
      rw [←Finset.mem_toList]
      simp_all only [List.mem_cons]

    have hdsub : hd ⊆ A := by
      apply asub
      exact hdin

    simp [Finset.subset_iff]
    intro x a a_1
    apply hdsub
    simp_all only

@[simp] lemma filter_mem {α : Type} [DecidableEq α] [Fintype α] (s : Finset α) (C : ClosureSystem α) :
  ∀ x ∈ s.filter (λ x => x ∈ C.ground), x ∈ C.ground :=
  by
    intro x
    intro h
    simp_all

noncomputable def intersectionOfSubsets {α : Type} [DecidableEq α][Fintype α] (A0 : Finset (Finset α)) : Finset α :=
  A0.toList.foldr (fun x acc => x ∩ acc) Finset.univ

lemma intersectionOfSubsets_def {α : Type} [DecidableEq α][Fintype α] (A0 : Finset (Finset α)) :
  intersectionOfSubsets A0 = A0.toList.foldr (fun x acc => x ∩ acc) Finset.univ := by rfl


--帰納法を使わずに、finset_subfamily_intersection_closed_listで示す。
lemma intersectioninground {α : Type} [DecidableEq α][Fintype α] (C: ClosureSystem α) [DecidablePred C.sets]:
  ∀ s ∈ C.ground.powerset,  intersectionOfSubsets (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)) ⊆ C.ground :=
  by
    intro s
    intro hs
    simp_all only [Finset.mem_powerset]
    intro X
    intro hX
    have nonemp : (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)).Nonempty := by
      simp_all only [Finset.Nonempty]
      use C.ground
      rw [Finset.mem_filter]
      rw [Finset.mem_powerset]
      constructor
      · simp_all only [subset_refl]
      · constructor
        exact C.has_ground
        simp_all only

    have allt: ∀ X ∈ (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)), X ⊆ C.ground := by
      intro X
      intro hX
      simp_all only [Finset.mem_filter, Finset.mem_powerset]

    --集合Setの方でやるのは間違い。リストを使うべき。
    --let fs := finset_subfamily_intersection_closed C.ground (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)) nonemp allt
    let fslst := finset_subfamily_intersection_closed_list C.ground (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)) nonemp allt
    exact fslst hX

--次の証明の目標はこれ。sを含むもので共通部分をとってもやはりsを含むことを証明する。どのような補題を示せばいいのか。集合族の大きさに関する帰納法が使える補題を設定する。
lemma intersectionExtension {α : Type} [DecidableEq α][Fintype α] (C: ClosureSystem α) [DecidablePred C.sets]:
  ∀ s ∈ C.ground.powerset, s ⊆ intersectionOfSubsets (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t))  :=
  by
    intro s
    intro hs
    simp_all only [Finset.mem_powerset]
    intro x
    intro hx
    --induction hs with
    --| subset => exact hx
    sorry

--def toSubtypeFinset {α : Type} [DecidableEq α][Fintype α] (C: ClosureSystem α) (s : Finset α) : Finset {x // x ∈ C.ground} :=
--  (s.filter (λ x => (x ∈ C.ground))).map ⟨λ x => ⟨x, filter_mem s C x (by simp_all)⟩, λ a b h => by simp_all⟩


noncomputable def closure_operator_from_CS  (C: ClosureSystem α) [DecidablePred C.sets]: SetFamily.closure_operator (C.toSetFamily) :=
  {   Family := C.toSetFamily,
      cl := by
        intro s
        let sval :=s.map ⟨Subtype.val, Subtype.val_injective⟩
        --#check intersectionOfSubsets (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ sval ⊆ t))
        --#check (s.map ⟨Subtype.val, Subtype.val_injective⟩).subtype (λ x => x ∈ C.ground)
        let ios := (intersectionOfSubsets (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ sval ⊆ t)))
        exact ios.subtype (λ x => x ∈ C.ground)

      extensive :=
      by
        intro s
        intro x
        intro h
        --simp_all
        have h1 : s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ C.ground := by
          obtain ⟨val, property⟩ := x
          intro x hx
          simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right,
            exists_eq_right]
          obtain ⟨w, h_1⟩ := hx
          simp_all only
        --obtain ⟨val, property⟩ := x
        --simp_all only
        --dsimp [intersectionOfSubsets]
        simp
        sorry

      monotone := by sorry
      idempotent := by sorry
  }
