--閉包システムの定義から閉包作用素を示す。つまりextensiveやmonotoneやindempotentを示した。
--ここではclosureシステムを有限の台集合で帰納的に考えた。Setに持ち込んで証明するともっと簡単だと思われる。
import LeanCopilot
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
import Init.Data.List.MinMax
import Mathlib.Data.List.MinMax
--import Mathlib.Algebra.BigOperators.Group.Finset
import Init.Data.List.Lemmas
import Pdfproof.closure_lemma
import Pdfproof.lattice_common

--set_option maxHeartbeats 2000000

variable {α : Type}  [DecidableEq α] [Fintype α]

structure SetFamily (α : Type) [DecidableEq α] [Fintype α] where
  (ground: Finset α)
  (sets : Finset α → Prop)
  (inc_ground : sets s → s ⊆ ground)

--定義には、台集合だけが必要で集合族は必要ない。Familyもいらないのでは。groundだけがいる。
structure SetFamily.preclosure_operator (ground:Finset α) where
  --(Family : SetFamily α)
  (cl : Finset ground → Finset ground)
  (extensive : ∀ s : Finset ground, s ⊆ cl s)
  (monotone : ∀ s t : Finset ground, s ⊆ t → cl s ⊆ cl t)

structure SetFamily.closure_operator (ground:Finset α) extends SetFamily.preclosure_operator ground where
  (idempotent : ∀ s : Finset ground, cl s = cl (cl s))

structure ClosureSystem (α : Type) [DecidableEq α]  [Fintype α] extends SetFamily α where
  (intersection_closed : ∀ s t , sets s → sets t → sets (s ∩ t))
  (has_ground : sets ground)

--intersectioningroundの証明で使っている。どの集合よりも大きい集合は、finsetInterよりも大きい。
--帰納法で示している。無限でも成り立つので、帰納的な仮定を使わずに、集合Setに持ってきても証明できる命題だと思われる。
lemma finset_subfamily_intersection_closed_list {α : Type} [DecidableEq α][Fintype α]
    (A : Finset α) (A0 : Finset (Finset α))
    (nonemptyA0 : A0.Nonempty)
    (h : ∀ X ∈ A0, X ⊆ A) : A0.toList.foldr (λ x acc => x ∩ acc) Finset.univ ⊆ A :=
by
  match v:A0.toList with --vのラベルをとるとなぜかエラーになる。
  | List.nil => simp_all
  | List.cons hd tl =>

    have hdin : hd ∈ A0.toList := by
      simp_all

    have asub : ∀ X ∈ A0.toList, X ⊆ A := by --仮定hのリスト版。
      intro X
      intro hX
      apply h
      simp_all
      rw [←Finset.mem_toList]
      simp_all only [List.mem_cons]

    have hdsub : hd ⊆ A := by
      apply asub
      exact hdin

    --have :List.foldr (fun x acc ↦ x ∩ acc) Finset.univ tl ⊆ A := うまく証明できない。

    simp [Finset.subset_iff] --部分集合を要素のimplyの関係に変換。
    intro x a a_1
    apply hdsub
    simp_all only --ここで帰納法の仮定をつかっている。

--finsetInterがground setに含まれるという補題。
--finset_subfamily_intersection_closed_listで示す。2箇所で使われている。
lemma intersectioninground {α : Type} [DecidableEq α][Fintype α] (C: ClosureSystem α) [DecidablePred C.sets]:
  ∀ s ∈ C.ground.powerset,  finsetInter (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)) ⊆ C.ground :=
  by
    intro s
    intro hs
    simp_all only [Finset.mem_powerset]
    intro X
    intro hX
    --引数のひとつ
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
    --引数のひとつ
    have allt: ∀ X ∈ (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)), X ⊆ C.ground := by
      intro X
      intro hX
      simp_all only [Finset.mem_filter, Finset.mem_powerset]

    let fslst := finset_subfamily_intersection_closed_list C.ground (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)) nonemp allt
    exact fslst hX

--extensiveの証明。finset_inter_subset_iffを使っている。
lemma intersectionExtension {α : Type} [DecidableEq α][Fintype α] (F: SetFamily α) [DecidablePred F.sets]:
  ∀ s ∈ F.ground.powerset, s ⊆ finsetInter (F.ground.powerset.filter (fun (t:Finset α) => F.sets t ∧ s ⊆ t))  :=
  by
    intro s
    intro hs
    simp_all only [Finset.mem_powerset]
    intro x
    intro hx
    let A0 := F.ground.powerset.filter (fun (t:Finset α) => F.sets t ∧ s ⊆ t)
    have xall: ∀ X ∈ A0, s ⊆ X := by
      intro X
      intro hX
      simp_all only [Finset.mem_filter,   A0]
    let fi := (finset_inter_subset_iff A0 s).mp xall
    exact fi hx

----------------------------------------------------------------------------
--ここから下は、monotoneの証明に関わる部分。

--意外とたくさん使われている定義。listInter_mono'でも使われている。最終的にはcommonに移動するかも。
noncomputable def listInter {α : Type u} [DecidableEq α] [Fintype α]
  (L : List (Finset α)) : Finset α :=
  L.foldr (fun x acc => x ∩ acc) Finset.univ

--listInter_mono'の証明で使われている。List.foldrしたものともともとの要素の包含関係。inductionが使われている。
lemma finsetInter_element {α : Type} [DecidableEq α][Fintype α] (L1 : List (Finset α)) (a : α)
  (h : a ∈ List.foldr (fun x acc ↦ x ∩ acc) Finset.univ L1) :
  ∀ x ∈ L1, a ∈ x :=
by
  intro x hx
  induction L1 with
  | nil =>
    simp_all only [List.foldr_nil, Finset.mem_univ, List.not_mem_nil]
  | cons y ys ih =>
    simp_all only [List.foldr_cons, Finset.mem_inter, List.mem_cons, forall_const]
    obtain ⟨left, right⟩ := h
    cases hx with
    | inl h =>
      subst h
      simp_all only [implies_true]
    | inr h_1 => simp_all only [forall_const] --帰納法の仮定ihを暗黙に使っている。

--finsetInter_elementの集合版。finset_subfamily_intersection_closed_ともちょっと似ているが違う。monotoneでないところで使われている。
lemma finsetInter_subset {α : Type} [DecidableEq α][Fintype α] (A0: Finset (Finset α)):
  ∀ X ∈ A0, finsetInter A0 ⊆ X :=
by
  intro X hX
  dsimp [finsetInter]
  exact fun y hy => finsetInter_element A0.toList y hy X (Finset.mem_toList.mpr hX)

--finsetInter_mono'の証明で使われている。
lemma listInter_mono'
    {α : Type} [DecidableEq α] [Fintype α]
    {L1 L2 : List (Finset α)}
    (h : ∀ (y : Finset α), y ∈ L2 → ∃ (x : Finset α), x ∈ L1 ∧ x ⊆ y)
    : listInter L1 ⊆ listInter L2 := by

  -- 補助関数 aux: L2 を cases で分解しながら「すべての y ∈ L2 について ∃ x ∈ L1, x ⊆ y」という仮定のもとで listInter L1 ⊆ listInter L2 を示す。
  let rec aux (L1 L2 : List (Finset α))
    (h' : ∀ y ∈ L2, ∃ x ∈ L1, x ⊆ y)
    : listInter L1 ⊆ listInter L2 :=
  by
    -- L2 を「cases ... with」スタイルで分解
    cases hl2 : L2 with
    | nil =>
      -- L2 = [] の場合
      --   listInter L2 = Finset.univ, よって常に listInter L1 ⊆ Finset.univ
      simp [listInter]
    | cons yy ys =>
      -- L2 = yy :: ys の場合
      simp [listInter]
      -- 目標は  listInter L1 ⊆ yy ∩ listInter ys
      apply Finset.subset_inter
      · -- まず listInter L1 ⊆ yy を示す
        -- h' から「yy ∈ L2 ⇒ ∃ x ∈ L1, x ⊆ yy」が取れる
        match h' yy (by simp [hl2]) with
        | ⟨xx, hx_in, hx_sub⟩ =>
          -- listInter L1 は L1 のすべての要素との共通部分
          -- 特に「L1 に属するどの要素にも含まれる」ので， L1 の要素 x に対して "listInter L1 ⊆ x" が言える
          have : listInter L1 ⊆ xx := by
            simp [listInter]
            intro a a_in
            exact finsetInter_element L1 a a_in xx hx_in
          -- 以上より  listInter L1 ⊆ x かつ x ⊆ y だから listInter L1 ⊆ y
          subst hl2
          simp_all only [List.mem_cons, forall_eq_or_imp]
          obtain ⟨left, right⟩ := h'
          obtain ⟨w, h_1⟩ := left
          obtain ⟨left, right_1⟩ := h_1
          apply Set.Subset.trans
          · exact this
          · exact hx_sub
      ·
        -- 再帰呼び出し aux L1 ys ... で結論が得られる
        have : ∀ z ∈ ys, ∃ x ∈ L1, x ⊆ z := by
          intro z hz
          -- z が ys に属する ⇒ z は (y :: ys) に属するので h' から要素が得られる
          subst hl2
          simp_all only [List.mem_cons, forall_eq_or_imp]
        exact aux L1 ys this

  -- 以上で定義した aux を呼び出してゴールを示す
  exact aux L1 L2 h

--monotone性の証明に使われる。finsetInterの単調性の証明。
theorem finsetInter_mono'
    {α : Type} [DecidableEq α] [Fintype α]
    {A B : Finset (Finset α)}
    (h : ∀ y ∈ B, ∃ x ∈ A, x ⊆ y)
    : finsetInter A ⊆ finsetInter B := by
  simp [finsetInter]
  -- あとは listInter_mono' を使うだけ
  apply listInter_mono'
  -- B.toList 上の任意の要素 y に対して，「∃ x ∈ A, x ⊆ y」を示す
  intro y hy
  match h y (by rw [Finset.mem_toList] at hy; exact hy) with
  | ⟨x, hxA, hx_sub⟩ =>
    -- x ∈ A なら x ∈ A.toList なので、listInter_mono' の仮定を満たす
    simp_all only [Finset.mem_toList]
---------------------------------------------------------------------------------------------------
--extensive性の証明を外に出したもの。
lemma extensive_from_SF {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α)[DecidablePred F.sets]:
  ∀ s : Finset F.ground, s ⊆
    let cl := fun s =>
    let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
    let ios := (finsetInter (F.ground.powerset.filter (fun (t:Finset α) => F.sets t ∧ sval ⊆ t)))
    ios.subtype (λ x => x ∈ F.ground)
  cl s :=
by

  let cl := fun (s:Finset F.ground) =>
    let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
    let ios := (finsetInter (F.ground.powerset.filter (fun (t : Finset α) => F.sets t ∧ sval ⊆ t)))
    ios.subtype (λ x => x ∈ F.ground)
  intro s
  let sval :=s.map ⟨Subtype.val, Subtype.val_injective⟩
  intro x
  intro h
  --simp_all
  have h1 : s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ F.ground := by
    obtain ⟨val, property⟩ := x
    intro x hx
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right] at hx--
    obtain ⟨w, h_1⟩ := hx
    simp_all only

  have : sval ∈ F.ground.powerset := by
    simp_all only [Finset.mem_powerset]
    simp_all only [sval]

  have h2 := intersectionExtension F sval this
  simp_all only [Finset.mem_subtype, sval]
  obtain ⟨val, property⟩ := x
  simp_all only [Finset.mem_subtype]

  apply h2
  simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right, exists_const]--

noncomputable def preclosure_operator_from_SF {α :Type} [DecidableEq α][Fintype α] (F: SetFamily α) [DecidablePred F.sets]: SetFamily.preclosure_operator F.ground :=
  let cl := fun s =>
    let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
    let ios := (finsetInter (F.ground.powerset.filter (fun (t:Finset α) => F.sets t ∧ sval ⊆ t)))
    ios.subtype (λ x => x ∈ F.ground)
{
  cl := cl
  --extensive := extensive_from_SF F, -- これではだめ。
  --monotone := monotone_closure_operator F cl,   -- 明示的に補題を渡す

  extensive := --そのまま、適用すると、エラーになったので、一回letで置いた。
  by
    let ef := extensive_from_SF F
    intro s
    simp_all only [cl, ef]

  monotone := by
    have h1 : ∀ s t : Finset F.ground, s ⊆ t → cl s ⊆ cl t := by
      intro s
      intro t
      intro h
      simp_all only [Finset.subset_iff]
      intro x
      intro hx
      unfold cl

      let S := Finset.filter (fun (u:Finset α) => F.sets u ∧ s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ u) F.ground.powerset
      let T := Finset.filter (fun (u:Finset α) => F.sets u ∧ t.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ u) F.ground.powerset

      let fs := fun (u:Finset α) => F.sets u ∧ s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ u
      let ft := fun (u:Finset α) => F.sets u ∧ t.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ u
      have : ∀ u, ft u → fs u := by
        intro u
        intro hu
        simp_all only [ Finset.mem_subtype,  true_and, cl, ft, fs]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := hu
        simp_all only
        intro x hx
        simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right]--
        obtain ⟨w, h_1⟩ := hx
        apply right
        simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,
          exists_const]


      have h3 : T ⊆ S := by
        simp_all only [Finset.subset_iff]
        intro y
        intro hy
        simp_all only [ true_and, Finset.mem_filter,   fs, ft, S, T]

      have arg : ∀ y ∈ T, ∃ x ∈ S, x ⊆ y := by
        intro y
        intro hy
        use y
        simp_all only [Subtype.forall, Finset.mem_subtype, Finset.map_subset_map, true_and, and_imp, Finset.mem_filter,
          Finset.mem_powerset, and_self, subset_refl, cl, ft, fs, T, S]

      simp --ないとエラー
      apply finsetInter_mono' arg
      simp_all only [Subtype.forall, Finset.mem_subtype, Finset.map_subset_map, true_and, and_imp, Finset.mem_filter,
        Finset.mem_powerset, cl, ft, fs, T, S]

    exact h1
  }

----------------------------------------------------------------------------
--あとは、idempotent性の証明だけなので、その部分。
--ここから下は、setsの共通部分は、またsetsになることの証明。idempotentの証明に使うcl_in_F_setsの証明に関係する部分。
-- F.setsはintersection_closedだが、S'はintersection closedとは限らない。
-- Fは帰納法で大きくなったり、小さくなったりせずに、Sが変わる。極大な集合を取る必要がない。
--この補題は結構使っている。
lemma finite_intersection_in_C {α : Type} [DecidableEq α][Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets]:
  ∀ S : Finset (Finset α), S.Nonempty → (∀ s ∈ S, F.sets s) → F.sets (finsetInter S) :=
by
  -- 基底ケース: S が単一要素集合の場合
  have base_case :
    ∀ x : Finset α,
      (∀ s ∈ ({x} : Finset (Finset α)),  F.sets s) →
      F.sets (finsetInter ({x} : Finset (Finset α))) :=
    by
      intro x h_all
      rw [finsetInter]
      simp
      exact h_all x (Finset.mem_singleton_self x)
  -- 帰納ステップ: S = insert x s の場合。後ろの| inr h_nonempty_Sで暗黙に使っている。
  have inductive_step :
    ∀ x : Finset α,
      ∀ S' : Finset (Finset α),
        x ∉ S' →
        S'.Nonempty →
        (∀ s ∈ insert x S', F.sets s) →
        F.sets (finsetInter S' ) →
        F.sets (finsetInter (insert x S') ) :=
    by
      intros x S' h_not_mem h_nonempty h_all h_inter_S'
      --rw [Finset.insert_eq, finsetInter]
      --simp [Finset.insert_eq, finsetInter]
      simp_all only [Finset.mem_singleton, forall_eq, Finset.mem_insert, forall_eq_or_imp]
      obtain ⟨left, right⟩ := h_all
      --#check (right x (Finset.mem_insert_self x S') h_inter_S')
      let fi := F.intersection_closed x (finsetInter S') left h_inter_S'
      have : x ∩ finsetInter S' = finsetInter (insert x S') := by
        dsimp [finsetInter]
        rw [Finset.insert_eq]
        exact insert_foldr_inter x S' h_not_mem
      rwa [← this]


  -- Finset.induction_on を利用して証明を完成
  intro S--h_nonempty h_all
  induction S using Finset.induction_on with --Finset.induction_on Sを使う。
  | empty =>
      -- 矛盾: S が空集合で Nonempty を満たすことはない
      intro h_nonempty
      exfalso
      exact False.elim (Finset.not_nonempty_empty h_nonempty)
  | @insert a s a_notin_s ih  => --ihに帰納法の仮定がはいっている。
      -- 帰納ステップ: S = insert x s
      --protected theorem induction_on {α : Type*} {p : Finset α → Prop} [DecidableEq α] (s : Finset α)
      --(empty : p ∅) (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : p s :=

      intro h_nonempty h_all

      cases s.eq_empty_or_nonempty with
      | inl h_empty =>
          -- s = ∅ の場合
          subst h_empty
          simp_all only [Finset.mem_singleton, forall_eq, Finset.mem_insert, forall_eq_or_imp, and_imp,
            Finset.not_mem_empty, not_false_eq_true, Finset.not_nonempty_empty, forall_const, not_isEmpty_of_nonempty,
            IsEmpty.forall_iff, insert_emptyc_eq, Finset.singleton_nonempty]
      | inr h_nonempty_S =>
          -- s≠ ∅ の場合。このケースでihを暗黙に使っている。
          simp_all only [Finset.mem_singleton, forall_eq, Finset.mem_insert, forall_eq_or_imp, and_imp, or_true,
            implies_true, forall_const, Finset.insert_nonempty, not_false_eq_true]

--subtypeの計算と、finsetInterの順番に関する補題。mapでなくて、image版。
--cl_in_F_sets_lemmaの証明で使っている。
lemma intersection_lemma_image  {α : Type} [DecidableEq α] [Fintype α] (p : α → Prop) [DecidablePred p] (S : Finset (Finset (Subtype p))) (Snonemp: S.Nonempty) :
  (finsetInter S).image Subtype.val = finsetInter (S.image (fun t => t.image Subtype.val)) :=

by
  -- 補題 `intersection_lemma` を利用して証明
  dsimp [finsetInter]
  --unfold List.foldr
  rw [Finset.image]
  rw [Finset.image]
  let il := intersection_lemma p S Snonemp
  convert il
  rw [@Finset.map_eq_image]
  simp_all only [Function.Embedding.coeFn_mk]
  rfl

  congr
  ext x a : 2
  simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Finset.mem_map,
    Function.Embedding.coeFn_mk]

 --cl_in_F_setsの証明で使っている。finite_intersection_in_Cのsubtype版。
 --finite_intersection_in_Cを使って証明している。
lemma finite_intersection_in_C_subtype
  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets]:
  let p := fun x => x ∈ F.ground
  ∀ S : Finset (Finset (Subtype p)), S.Nonempty → (∀ s ∈ S, F.sets (s.image Subtype.val)) → F.sets ((finsetInter S).map ⟨Subtype.val,Subtype.val_injective⟩) :=
by
  -- 定理の主張：帰納法により証明する
  intro p S h_nonempty h_all
  -- サブタイプの集合族 S を通常の集合族に変換
  --let p : α → Prop := fun x => x ∈ F.ground
  let S_val := (S : Finset (Finset (Subtype p))).image (fun s => s.image Subtype.val)
  -- S_val は Finset (Finset α)
  have h_S_val_nonempty : S_val.Nonempty :=
    by
      rcases h_nonempty with ⟨t, ht⟩
      use t.image Subtype.val
      simp_all only [Finset.mem_image, S_val]
      exact ⟨t, ht, rfl⟩
  -- 各要素が F.sets に属することを確認
  have h_S_val_all : ∀ s ∈ S_val, F.sets s :=
    by
      intro s hs
      simp_all only [Finset.image_nonempty, Finset.mem_image, S_val]
      obtain ⟨w, h⟩ := hs
      obtain ⟨left, right⟩ := h
      subst right
      simp_all only
  -- 元の定理を適用して F.sets (finsetInter S_val) を得る
  have h_finset_inter : F.sets (finsetInter S_val) :=
    finite_intersection_in_C F S_val h_S_val_nonempty h_S_val_all --これの引数を一生懸命計算。
  -- finsetInter S の値が finsetInter S_val に対応することを示す

  have : (finsetInter S).map ⟨Subtype.val, Subtype.val_injective⟩ =  finsetInter (S.image (fun t => t.map ⟨Subtype.val, Subtype.val_injective⟩ )):=
  by
    let il := intersection_lemma p S h_nonempty --これも中心的に使う補題か。
    convert il --exactだとうまくいかないが、convertだと即座に証明できる。

  simp_all only [Finset.image_nonempty, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    implies_true, p, S_val]
  convert h_finset_inter
  ext x a : 2
  simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,
    Finset.mem_image]

--intersection_lemmaと内容が近いがこちらのほうが複雑。intersection_lemmaを使って証明する。証明が大変だった。cl_in_F_setsで使っている。
--言明に空集合を排除する条件はつけずに証明の中の場合分けで乗り切る。
lemma cl_in_F_sets_lemma  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets] (s : Finset { x // x ∈ F.ground }):
   Finset.subtype (fun x ↦ x ∈ F.ground) (finsetInter (Finset.filter (fun t ↦ F.sets t ∧ s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ t) F.ground.powerset)) = finsetInter (Finset.image (fun t ↦ Finset.subtype (fun x ↦ x ∈ F.ground) t) (Finset.filter (fun t ↦ F.sets t ∧ s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ t) F.ground.powerset)) :=
by

  set filtered := Finset.filter (fun t ↦ F.sets t ∧ s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ t) F.ground.powerset
  by_cases filtered.image (λ t => t.subtype (λ x => x ∈ F.ground)) = ∅
  case pos =>
    simp_all only [Finset.image_eq_empty, Finset.image_empty, filtered]
    simp [finsetInter]
  case neg nonemp =>
     --iliはlem2の証明で暗黙につかっている。
    have nonemp2: (Finset.image (fun t ↦ t.subtype (λ x => x ∈ F.ground)) filtered).Nonempty :=
    by
      simp_all only [nonemp, Finset.image_eq_empty, Finset.image_empty, filtered]
      simp_all only [Finset.image_nonempty]
      rwa [Finset.nonempty_iff_ne_empty]
    let ili := (intersection_lemma_image (fun x => x ∈ F.ground) (filtered.image (λ t => t.subtype (λ x => x ∈ F.ground))) nonemp2).symm
    let tmp :=  (Finset.image (fun t ↦ Finset.subtype (fun x ↦ x ∈ F.ground) t) filtered)
    let tmp_right := (Finset.image (fun t ↦ Finset.subtype (fun x ↦ x ∈ F.ground) t) filtered)
    let tmpimage2 := tmp.image (fun t ↦ t.image Subtype.val)

    --lem2はlem5の証明に使っている。lem 5の直前に移動すると何故かエラー。
    have lem2:finsetInter tmpimage2 = Finset.image Subtype.val (finsetInter tmp_right) :=
    by
      simp_all only [Finset.map_inj, tmpimage2, tmp, filtered, tmp_right]
      rw [Finset.map_eq_image]  --これはimageを増やす方向。simpによって、mapができてしまた。
      simp_all only [Function.Embedding.coeFn_mk]
      ext a : 1
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]--
      apply Iff.intro
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        simp_all only [exists_true_left]
        convert h
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        simp_all only [exists_true_left]
        convert h

    --lem3はlem 5の証明に使っている。
    have lem3 :∀ (ss :Finset α), Finset.image (fun t ↦ Subtype.val t) (Finset.subtype (fun x ↦ x ∈ F.ground) ss) = Finset.filter (fun t ↦ t ∈ F.ground) ss :=
    by
      intro ss
      simp_all only [filtered, tmpimage2, tmp, tmp_right]
      ext a : 1
      simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, Finset.mem_filter]--

    --lem 4の証明で使っている。
    have lem4_lem :∀ (s: Finset α), Finset.image Subtype.val (Finset.subtype (fun t => t∈ F.ground) s) = s.filter (fun t => t∈ F.ground) :=
    by
      intro s_1
      ext a : 1
      simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, Finset.mem_filter]

    -- lem4はlem 5の証明中で使っている。ただし、lem　4もlem 5もlem_mainの証明で使っている。
    have lem4: Finset.image (fun t ↦ Finset.image Subtype.val t) (Finset.image (fun t ↦ Finset.subtype (fun x ↦ x ∈ F.ground) t) filtered) = filtered := by
      simp_all only [Finset.mem_image, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right]
      ext x
      simp
      dsimp [filtered]
      apply Iff.intro
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        subst right
        simp_all only [Finset.mem_filter, Finset.mem_powerset, filtered, tmpimage2, tmp]
        obtain ⟨left, right⟩ := left
        obtain ⟨left_1, right⟩ := right
        apply And.intro
        ·
          simp_all only [implies_true]
          intro x hx
          simp_all only [Finset.mem_filter]
        · apply And.intro
          simp_all only [implies_true]
          rwa [Finset.filter_true_of_mem left]

          simp_all only [implies_true]
          intro x hx
          simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,
            Finset.mem_filter]
          obtain ⟨w_1, h⟩ := hx
          simp_all only [and_true]
          apply right
          simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,
            exists_const]
      · intro a
        apply Exists.intro
        · apply And.intro
          ·
            simp_all only [implies_true, Finset.mem_filter, Finset.mem_powerset, filtered]
            apply And.intro
            on_goal 2 => apply And.intro
            on_goal 2 => {exact a.2.1
            }
            · simp_all only [implies_true, Finset.mem_filter, Finset.mem_powerset, and_self, filtered]
            · simp_all only [implies_true, Finset.mem_filter, Finset.mem_powerset, and_self, filtered]
          ·
            simp_all only [implies_true, Finset.mem_filter, Finset.mem_powerset, filtered]
            obtain ⟨left, right⟩ := a
            obtain ⟨left_1, right⟩ := right
            ext a : 1
            simp_all only [Finset.mem_filter, and_iff_left_iff_imp]
            intro a_1
            exact left a_1

    have lem5:finsetInter (Finset.image (fun t ↦ Finset.subtype (fun x ↦ x ∈ F.ground) t) filtered) =
        Finset.subtype (fun x ↦ x ∈ F.ground) (finsetInter filtered) :=
      by
        simp_all only [filtered, tmpimage2, tmp, tmp_right]
        rw [Finset.map_eq_image]
        ext x
        simp_all only [Finset.mem_image, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right]
        apply Iff.intro
        · intro a
          simp_all only [implies_true, Finset.mem_subtype, Finset.mem_image, Subtype.exists, exists_and_right,
            exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]
        · intro a
          simp_all only [implies_true, Finset.mem_subtype, Finset.mem_image, Subtype.exists, exists_and_right,
            exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]

    simp_all only [filtered]

--cl_in_F_setsの証明で使っている。subtypeをとってvalを取るのは、filterを取るのと同じ。
lemma subtype_image_val_eq_filter {α : Type} [DecidableEq α]
  (p : α → Prop) [DecidablePred p] (s : Finset α) :
  Finset.image Subtype.val (Finset.subtype p s) = s.filter p :=
by
  ext x
  simp [Finset.mem_image, Finset.mem_filter, Finset.mem_subtype]

--cl_in_F_setsの証明で使っている。subtypeの台集合に含まれるsは、フィルターをとっても変わらない。
lemma filter_eq_self_of_subset {α : Type} [DecidableEq α] [Fintype α]
  (p : α → Prop) [DecidablePred p] (s : Finset α) (h_subset : s ⊆ (Finset.univ.filter p)) :
  s.filter p = s :=
by
  ext x
  simp [Finset.mem_filter]
  intro a
  simpa using h_subset a

-- `clcs` の定義。つぎの言明で使う。
noncomputable def clcs {α : Type} [DecidableEq α] [Fintype α] (F : ClosureSystem α) [DecidablePred F.sets]
  (s : Finset { x // x ∈ F.ground }) : Finset { x // x ∈ F.ground } :=
  let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
  let ios := finsetInter (F.ground.powerset.filter (fun (t : Finset α) => F.sets t ∧ sval ⊆ t))
  ios.subtype (λ x => x ∈ F.ground)

-- `F.sets (clcs s)` の証明。 subtypeがらみで意外と難しかった。idepotentの証明で用いるつもりだったが使ってないかも。
--finsetInter_eq_sを使って証明した方がよかったかも。
theorem cl_in_F_sets {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets] :
  ∀ (s : Finset { x // x ∈ F.ground }), F.sets ((clcs F s).map ⟨Subtype.val, Subtype.val_injective⟩) :=
by
  intro s
  let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
  let candidates := F.ground.powerset.filter (fun t => F.sets t ∧ sval ⊆ t) --sを含むhyperedgeたち。
  have h_nonempty : candidates.Nonempty :=
    by
      use F.ground
      dsimp [candidates]
      simp [Finset.mem_filter, Finset.mem_powerset]
      constructor
      exact F.has_ground
      simp_all only [sval]
      intro t ht
      simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right]
      obtain ⟨w, h⟩ := ht
      simp_all only

  have fiarg:  (∀ s ∈ candidates, F.sets s) := --candidatesの元が本当にhyperedgeである保証
  by
    intro s_1 a
    simp_all only [Finset.mem_filter, Finset.mem_powerset, candidates, sval]

  have : F.sets ((clcs F s).map ⟨Subtype.val, Subtype.val_injective⟩) := by
    dsimp [clcs] --clcsを展開する必要があるが、本当は補題で済ませたい。
    let fi := finite_intersection_in_C F candidates h_nonempty fiarg
    dsimp [candidates] at fi
    -- finite_intersection_in_C_subtypeを使うべき。

    --以下は頑張って示した。
    let candidates_subtype := candidates.image (λ t => t.subtype (λ x => x ∈ F.ground))
    have h_candidates_subtype_nonempty : candidates_subtype.Nonempty := by
      simp only [Finset.Nonempty, Finset.mem_image]
      use F.ground.subtype (λ x => x ∈ F.ground)
      dsimp [candidates]
      dsimp [candidates_subtype]
      dsimp [candidates]
      rw [Finset.mem_image]
      use F.ground
      rw [Finset.mem_filter]
      constructor
      constructor
      simp_all only [Finset.mem_powerset, subset_refl]
      constructor
      exact F.has_ground

      simp_all only [sval]

      intro x hx
      simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right]
      obtain ⟨w, h⟩ := hx
      simp_all only

      simp_all only

    --以下は頑張って示した。
    let fiarg_subtype : ∀ s ∈ candidates_subtype, F.sets (Finset.image Subtype.val s) := by
      intro s hs
      dsimp [candidates_subtype] at hs
      simp only [Finset.mem_image] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      rw [subtype_image_val_eq_filter]
      have : t ⊆ F.ground := by
        simp_all only [Finset.image_nonempty, Finset.mem_filter, Finset.mem_powerset, candidates_subtype, candidates,
          sval]
      rw [filter_eq_self_of_subset]
      simp_all only [Finset.image_nonempty, Finset.mem_filter, Finset.mem_powerset, true_and, and_self,
        candidates_subtype, candidates, sval]
      simp_all only [Finset.image_nonempty, Finset.mem_filter, Finset.mem_powerset, true_and, Finset.filter_univ_mem,
        candidates_subtype, candidates, sval]

    let fis := finite_intersection_in_C_subtype F candidates_subtype h_candidates_subtype_nonempty fiarg_subtype
    dsimp [candidates_subtype] at fis
    dsimp [candidates] at fis
    have : (finsetInter (Finset.filter (fun t ↦ F.sets t ∧ sval ⊆ t) F.ground.powerset)).subtype (λ x => x ∈ F.ground) = finsetInter (Finset.image (fun t ↦ t.subtype (λ x => x ∈ F.ground)) (Finset.filter (fun t ↦ F.sets t ∧ sval ⊆ t) F.ground.powerset)) := by
      dsimp [sval]
      exact cl_in_F_sets_lemma F s
    rw [← this] at fis
    exact fis

  simp_all only [Finset.mem_filter, Finset.mem_powerset, implies_true, candidates, sval]

noncomputable def closure_operator_from_CS {α :Type} [DecidableEq α][Fintype α] (C: ClosureSystem α) [DecidablePred C.sets]: SetFamily.closure_operator (C.ground) :=
  let cl := fun s =>
    let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
    let ios := (finsetInter (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ sval ⊆ t)))
    ios.subtype (λ x => x ∈ C.ground)
{
  cl := cl
  extensive := --そのまま、適用すると、エラーになったので、一回letで置いた。
  by
    let ef := extensive_from_SF C.toSetFamily
    intro s
    simp_all only [cl, ef]

  monotone := by
    let po := (preclosure_operator_from_SF C.toSetFamily).monotone
    intro s t hst
    simp_all only [cl, po]
    tauto

  idempotent :=
  by
    intro s --subtype
    let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
    let cl_s := finsetInter (C.ground.powerset.filter (fun t => C.sets t ∧ sval ⊆ t)) --clの値。普通の集合
    let cl_cl_s := finsetInter (C.ground.powerset.filter (fun t => C.sets t ∧ cl_s ⊆ t)) -- cl(cl(s))の値。普通の集合
    have h_cl_s : cl s = cl_s.subtype (λ x => x ∈ C.ground) := rfl  --両辺subtype
    have h_cl_cl_s : cl (cl s) = cl_cl_s.subtype (λ x => x ∈ C.ground) :=  --両辺subtype
    by
      simp_all only [cl]
      congr
      funext x
      simp_all
      dsimp [cl_s]
      rw [Finset.map_eq_image]
      intro xsx
      apply Iff.intro
      · intro a
        have hx : x ∈ Finset.filter (fun t ↦ C.sets t ∧ sval ⊆ t) C.ground.powerset := by
          simp [xsx, sval]
          --rw [Finset.mem_filter]
          constructor
          · exact C.inc_ground xsx
          · rw [Finset.map_eq_image]
            simp at a
            --このファイル最後の未解決だった部分。goal Finset.image (⇑{ toFun := Subtype.val, inj' := ⋯ }) s ⊆ x
            --xは、通常の集合
            --a : Finset.image Subtype.val  (Finset.subtype (fun x ↦ x ∈ C.ground)  (finsetInter (Finset.filter (fun t ↦ C.sets t ∧ Finset.map { toFun := Subtype.val, inj' := ⋯ } s ⊆ t) C.ground.powerset))) ⊆ x
            --clの像をsubtypeにして、valを取っているので、x in C.groundでfinlterを撮っているのと同じか。clの値をgroundでfilterしたもの。つまりxは、clの値を含む集合。
            --sは任意のsubtypeで、hyperedgeとは限らない。
            --示すべきことは、subtypeのsのvalは、clの値を含む集合になることで、単なるextensiveのような気がする。
            let ef := extensive_from_SF C.toSetFamily
            simp_all only [Function.Embedding.coeFn_mk]
            intro y hy
            simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
            obtain ⟨w, h⟩ := hy
            apply a
            simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
              exists_eq_right_right, and_true]
            simpa using ef _ h

        have h_all : ∀ s ∈ Finset.filter (fun t ↦ C.sets t ∧ sval ⊆ t) C.ground.powerset, C.sets s := by
          intros s hs
          simp_all only [Function.Embedding.coeFn_mk, Finset.mem_filter, Finset.mem_powerset, true_and, sval]
        --この部分もfinsetInterが他の部分の部分集合になればよい。
        exact finsetInter_subset _ _ hx
        --lemma finsetInter_subset {α : Type} [DecidableEq α][Fintype α] (A0: Finset (Finset α)): ∀ X ∈ A0, finsetInter A0 ⊆ X
      · intro a
        simp_all only [Function.Embedding.coeFn_mk, sval]
        rw [Finset.image_subset_iff]
        intro x_1 a_1
        simp_all only [Finset.mem_subtype]
        obtain ⟨val, property⟩ := x_1
        simp_all only
        apply a
        simp_all only [cl_s, sval, cl]

    have h_cl_s_in_sets : C.sets cl_s := by
      apply finite_intersection_in_C
      simp only [Finset.filter_nonempty_iff, Finset.mem_filter, Finset.mem_powerset]
      use C.ground
      simp only [subset_refl, true_and]
      constructor
      exact C.has_ground
      intro t ht
      simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,
        cl, cl_s, sval, cl_cl_s]
      obtain ⟨w, h⟩ := ht
      simp_all only

      simp_all only [cl, cl_s, sval]
      intro s_1 a
      simp_all only [Finset.mem_filter, Finset.mem_powerset, cl_cl_s, cl_s, sval]

    have h_cl_s_subset : sval ⊆ cl_s := by
      dsimp [cl_s,sval]
      let ef := extensive_from_SF C.toSetFamily s
      simp at ef
      convert ef
      simp_all
      apply (finset_inter_subset_iff _ _).mpr
      intro t ht
      simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists,
        exists_and_right, exists_eq_right, cl, cl_s, sval]
      obtain ⟨w, h⟩ := ht
      simp_all only [cl, cl_cl_s, cl_s, sval]
      simpa using ef h

      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
      --finsetInterの要素はもとのどの要素よりも小さいことを示ればよさそう。
        apply intersectioninground C sval
        simp_all only [Finset.mem_powerset, cl, cl_cl_s, cl_s, sval]
        intro x hx
        simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right]
        obtain ⟨w, h⟩ := hx
        simp_all only

      · simp_all only [true_and, cl, cl_cl_s, cl_s, sval]
        rw [Finset.subset_iff] at ef
        simp_all only [Finset.mem_subtype, Subtype.forall]
        intro a ha
        simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right]
        obtain ⟨w, h⟩ := ha
        simp_all only

    --以下の部分はcl_in_F_setsを用いて証明するはずだったが、ChatGPTはその道を取らなかった。ということは、cl_in_F_setsももっと簡単に証明できるかも。
    have h_cl_cl_s_eq_cl_s : cl_cl_s = cl_s := by
      apply finsetInter_eq_s
      simp only [Finset.filter_nonempty_iff, Finset.mem_filter, Finset.mem_powerset]
      constructor
      -- Groundの部分集合のfinsetInterがGroundsetであることを利用する。
      · dsimp [cl_s]
        have : sval ∈ C.ground.powerset :=
        by
          simp_all only [Finset.mem_powerset, cl, cl_s, sval, cl_cl_s]
          intro x hx
          simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right,
            exists_eq_right]
          obtain ⟨w, h⟩ := hx
          simp_all only
        exact intersectioninground C sval this
      · simp_all only [subset_refl, and_self, cl, cl_s, sval, cl_cl_s]
      · intro t a
        simp_all only [Finset.mem_filter, Finset.mem_powerset, cl, cl_s, sval, cl_cl_s]
    dsimp [cl_cl_s] at h_cl_cl_s_eq_cl_s
    dsimp [cl_s] at h_cl_s_in_sets
    dsimp [h_cl_cl_s_eq_cl_s]
    simp_all only [cl, cl_s, sval, cl_cl_s]
}

------
--以下は結果的に使われなくなった部分。
--finsetInset_monoで使われているが、finset_monoが使われてないので、一緒に移動した。
lemma listInter_mono {α : Type u} [DecidableEq α] [Fintype α]
    {L1 L2 : List (Finset α)}
    (h_len : L1.length = L2.length)
    (h_sub : ∀ i : Nat, i < L1.length → L1.get! i ⊆ L2.get! i) :
    listInter L1 ⊆ listInter L2 := by
  -- 証明は L1 に対する単純な再帰 (induction) で行うのが分かりやすいです
  cases hl1:L1 with
  | nil =>
    -- L1 = [] の場合
    -- listInter [] = Finset.univ なので，Finset.univ ⊆ listInter L2 は自明
    simp [listInter]
    have :L2 = [] := by
      rw [←hl1]
      subst hl1
      simp_all only [List.length_nil, List.get!_eq_getElem!, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem,
        Option.getD_some]
      simpa using h_len.symm
    subst this hl1
    simp_all only [List.length_nil, not_lt_zero', List.get!_eq_getElem!, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem, Option.getD_some, subset_refl, implies_true, List.foldr_nil]
  | cons x xs =>
    -- L1 = x :: xs の場合
    cases hl2:L2 with
    | nil =>
      -- L2 = [] は長さ一致に反するので矛盾
      exfalso
      subst hl2
      simp_all only [List.length_cons, List.length_nil, AddLeftCancelMonoid.add_eq_zero, List.length_eq_zero,
        one_ne_zero, and_false]
    | cons y ys =>
      -- L2 = y :: ys
      -- ここで h_len : L1.length = L2.length
      -- すなわち x :: xs の長さ = y :: ys の長さ から xs.length + 1 = ys.length + 1 を得たい
      -- しかしそのままだと Nat.succ.inj を直接は使えないことがある
      rw [hl1] at h_len
      rw [hl2] at h_len
      rw [List.length_cons] at h_len
      rw [List.length_cons] at h_len
      -- h_len は xs.length.succ = ys.length.succ の形になった
      let h_len' := Nat.succ.inj h_len
      -- これで xs.length = ys.length が得られた
      -- あとは単調性を示す
      dsimp [listInter]  -- listInter (x :: xs) = x ∩ listInter xs
      apply Finset.subset_inter
      · -- x ⊆ y 先頭のものが包含関係があること。
        have hx:x = L1.get! 0 := by
          rw [hl1]
          simp
        have hy:y = L2.get! 0 := by
          rw [hl2]
          simp
        have h0 : 0 < L1.length := by
          rw [hl1]
          simp
        let h0' := h_sub 0 h0
        subst hl1 hl2
        simp_all only [List.get!_eq_getElem!, List.getElem!_eq_getElem?_getD, List.length_cons,
          add_pos_iff, zero_lt_one, or_true, List.getElem?_eq_getElem, List.getElem_cons_zero, Option.getD_some]--
        intro i hi
        simp_all only [Finset.mem_inter]
        --obtain ⟨left, right⟩ := hi
        apply h0'
        simp_all only [List.get!_eq_getElem!, List.getElem!_eq_getElem?_getD,
         List.getElem?_eq_getElem, List.getElem_cons_zero, Option.getD_some]--
      · -- listInter xs ⊆ listInter ys 残りの部分も包含関係があること。これは帰納法の仮定を使う。
        have arg: ∀ (i : ℕ), i  < xs.length → xs.get! i ⊆ ys.get! i:=
        by
          let fun_ih := (fun i hi => h_sub (i+1) hi) --帰納法の仮定の仮定が満たされていることを確認。
          rw [hl1] at fun_ih
          rw [hl2] at fun_ih
          intro i a
          subst hl1 hl2
          simp_all only [List.length_cons, add_lt_add_iff_right, List.get!_eq_getElem!,
            List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, List.getElem_cons_succ, Option.getD_some,
            h_len']

        let ih := listInter_mono h_len' arg
        subst hl1 hl2
        simp_all only [List.length_cons, List.get!_eq_getElem!, List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem, Option.getD_some, h_len']
        intro i hi
        simp_all only [Finset.mem_inter]
        obtain ⟨left, right⟩ := hi
        apply ih
        exact right

--extensiveの証明に使えるかと思って証明したが、リストの数が同じでないので使えなかった。
theorem finsetInter_mono {α : Type} [DecidableEq α] [Fintype α]
    {A B : Finset (Finset α)}
    (h_len : A.toList.length = B.toList.length)
    (h_sub : ∀ i : Nat, i < A.toList.length →
              A.toList.get! i ⊆ B.toList.get! i) :
    finsetInter (A : Finset (Finset α)) ⊆ finsetInter (B : Finset (Finset α)) := by
  -- finsetInter A = listInter A.toList, finsetInter B = listInter B.toList
  simp [finsetInter]
  -- あとは listInter_mono を使えばよい
  apply listInter_mono h_len h_sub
/-
--現状では使ってない。集合のほうにもってきて考えるファイルに入れるのがよい。
--Finsetでない一般のSetの閉包集合族の場合は別のファイルで考える。
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
-/
/-
@[simp] lemma filter_mem {α : Type} [DecidableEq α] [Fintype α] (s : Finset α) (C : ClosureSystem α) :
  ∀ x ∈ s.filter (λ x => x ∈ C.ground), x ∈ C.ground :=
  by
    intro x
    intro h
    simp_all
-/
/-
--使われてない。
lemma intersectionOfSubsets_def {α : Type} [DecidableEq α][Fintype α] (A0 : Finset (Finset α)) :
  finsetInter A0 = A0.toList.foldr (fun x acc => x ∩ acc) Finset.univ := by rfl
-/

--ここから下は、閉集合族から極大なものをひとつとっても閉集合族になることを示す部分。
--ここで証明したことは、List.max?に関して非空な場合の最大値の存在と、最大値であることを保証する定理を証明した。List.max?_spec
--当然、mathlibにあると思われるが、List.maximumのほうはあっても、max?のほうにはなく、等価性の証明もない。
--と思ったら、以下のものがあった。
 --List.max?_eq_some_iff.{u_1} {α : Type u_1} {a : α} [Max α] [LE α] [anti : Std.Antisymm fun x1 x2 ↦ x1 ≤ x2]
    --(le_refl : ∀ (a : α), a ≤ a) (max_eq_or : ∀ (a b : α), a ⊔ b = a ∨ a ⊔ b = b)
    --(max_le_iff : ∀ (a b c : α), b ⊔ c ≤ a ↔ b ≤ a ∧ c ≤ a) {xs : List α} : xs.max? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, b ≤ a
--そのLinearOrder版を証明しようとしたが、途中で挫折した。
--theorem List.max?_eq_some_iff_linear_order {α : Type _} [LinearOrder α] {a : α} {xs : List α} :
--  xs.max? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, b ≤ a :=
--List.max?_mem やList.max?_le_iffを使って証明しようとしたが挫折。

--使ってない？
omit [DecidableEq α] [Fintype α]
lemma mini_lem [LinearOrder α] (a b:α) (bs:List α ): List.foldl max (a ⊔ b) bs = a ⊔ List.foldl max b bs :=
  by
    cases hb:bs with
    | nil =>
      -- ベースケース: bs = []
      simp
    | cons x xs =>
      -- 帰納法ステップ: bs = x :: xs
      simp [List.foldl]
      have ih := mini_lem b x xs
      simp [max_assoc]
      rw [ih]
      simp [←max_assoc]
      exact mini_lem (a ⊔ b) x xs

--exsts2に拡張されたので使ってない。
theorem max?_exists [DecidableEq α] [LinearOrder α] {l : List α} (l_ne : l ≠ []) :
  ∃ m : α, l.max? = some m :=
by
  cases l with
  | nil =>
    -- 空リストの場合は矛盾
    contradiction
  | cons a as =>
    -- 非空リストの場合
    use List.foldl max a as
    simp [List.max?]

theorem max?_exists2 [DecidableEq α] [LinearOrder α] {l : List α} (l_ne : l ≠ []) :
 ∃ m : α, l.max? = some m ∧ m ∈ l :=
 by
  cases l with
  | nil =>
    -- 空リストの場合は矛盾
    contradiction
  | cons a as =>
    -- 非空リストの場合
    use List.foldl max a as
    constructor
    · simp [List.max?]
    · dsimp [List.foldl]
      induction as generalizing a with
      | nil =>
        -- ベースケース: 空リストの場合
        simp [List.foldl]
      | cons b bs ih =>
        -- 帰納法ステップ: as = b :: bs の場合
        simp [List.foldl]
        -- max a b が a か b かで分岐
        cases max_choice a b with
        | inl h1 =>
          -- max a b = a の場合
          rw [h1]
          -- 帰納法の仮定 ih : foldl max a bs ∈ a :: b :: bs
          -- これを Or で場合分けしてそのまま詰める
          simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.mem_cons, forall_const, sup_eq_left]
          specialize ih a
          cases ih with
          | inl h => simp_all only [true_or]
          | inr h_1 => simp_all only [or_true]
        | inr h2 =>
          -- max a b = b の場合
          rw [h2]
          -- 帰納法の仮定 ih : foldl max a bs ∈ a :: b :: bs
          -- ただし今度はアキュムレータが b に変わるので ih b を使う
          right
          simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.mem_cons, forall_const, sup_eq_right]

--List maxに対して、最大値の存在を保証する定理
theorem List.max?_spec {β : Type} [DecidableEq β] [LinearOrder β] {l : List β} (l_ne : l ≠ []) :
  ∃ m:β  , l.max? = some m ∧ (∀ x ∈ l, x ≤ m) ∧ m ∈ l :=
by

  cases l with
    | nil =>
      -- 空リストの場合、仮定に矛盾
      contradiction
    | cons a as =>
      -- 非空リストの場合
      obtain ⟨m, hm⟩ := max?_exists l_ne
      by_cases as = []
      case pos =>
        rename_i h
        subst h
        simp_all only [ne_eq, cons_ne_self, not_false_eq_true, max?_cons, max?_nil, Option.elim_none,
          Option.some.injEq, mem_singleton, forall_eq, exists_eq_left', le_refl, and_self]

      case neg =>
        have : as ≠ [] := by
          intro c
          subst c
          simp_all only [ne_eq, cons_ne_self, not_false_eq_true]
        obtain ⟨mm, hmm⟩ := max?_exists2 this
        let hmm1 := hmm.1
        let hmm2 := hmm.2
        obtain ⟨mmx, hmmx,hmmxx⟩ := List.max?_spec this
        use m
        constructor
        exact hm
        constructor
        · rename_i h
          intro x a_1
          simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, max?_cons, Option.elim_some, Option.some.injEq,
            mem_cons]
          subst hm hmmx
          simp_all only [and_true, le_sup_iff]
          obtain ⟨left, right⟩ := hmm
          cases a_1 with
          | inl h =>
            subst h
            simp_all only [le_refl, true_or]
          | inr h_1 => simp_all only [or_true]
        · simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, max?_cons, Option.elim_some, Option.some.injEq,
          mem_cons]
          subst hm hmmx
          simp_all only [and_true, sup_eq_left]
          obtain ⟨left, right⟩ := hmm
          by_cases mm <= a
          case pos =>
            left
            simp_all only [true_or]
          case neg =>
            right
            have : mm = a ⊔ mm := by
              rename_i h
              simp_all only [not_le, right_eq_sup]
              exact le_of_lt h
            rw [←this]
            exact right
--end max?exist
-----
--`F : Finset (Finset α)` が「交わりで閉じている」ことを表す述語。どの2つ A, B ∈ F についても A ∩ B ∈ F
def IntersectClosed [Fintype α] (F : Finset (Finset α)) : Prop :=
  (Finset.univ ∈ F) ∧ ∀ A B, A ∈ F → B ∈ F → A ∩ B ∈ F

--包含関係でこれ以上大きくならない（真の上位集合が無い）要素。
def isMaximal (F : Finset (Finset α)) (M : Finset α) : Prop :=
  M ∈ F ∧ ∀ (N : Finset α), N ∈ F → M ⊆ N → N = M

--極大要素を除いても交わり閉が保たれる

/-
- F : Finset (Finset α) が交わり閉
- M : Finset α が極大要素 (isMaximal F M)
- ただし M ≠ univ  (全体集合でない極大要素)
⇒ F.erase M も交わり閉
   （すなわち (1) univ ∈ F.erase M, (2) A,B ∈ F.erase M ⇒ A ∩ B ∈ F.erase M）
-/
theorem removeMaximalPreservesIntersectClosed [Fintype α] [DecidableEq α]
  (F : Finset (Finset α))
  (hF : IntersectClosed F)
  {M : Finset α} (hM : isMaximal F M)
  (hMne : M ≠ Finset.univ)
  : IntersectClosed (F.erase M) :=
by
  -- hF : univ ∈ F, ∀ A,B ∈ F, A ∩ B ∈ F
  let ⟨univ_in_F, inter_closed⟩ := hF
  let ⟨M_in_F, M_max⟩ := hM

  /- (1) univ_mem: univ ∈ F.erase M
       には M ≠ univ だから univ ∉ {M} ⇒ univ はまだ F.erase M に残る -/
  --have univ_mem' : Finset.univ ∈ F.erase M := by
  --  apply Finset.mem_erase_of_ne_of_mem
  --  · exact hMne
  --  · exact univ_in_F

  /- (2) closed_inter: A, B ∈ (F.erase M) ⇒ A ∩ B ∈ (F.erase M)
       ここで A,B ≠ M は明らかだが、「A ∩ B = M」になってしまったら困るので矛盾を導く
   -/
  have inter_closed' : ∀ A B, A ∈ F.erase M → B ∈ F.erase M → A ∩ B ∈ F.erase M :=
    by
      intros A B hA hB
      -- A,B が元々 F に属すること & A≠M, B≠M
      have A_in_F : A ∈ F := Finset.mem_of_mem_erase hA
      have A_ne_M : A ≠ M := Finset.ne_of_mem_erase hA
      have B_in_F : B ∈ F := Finset.mem_of_mem_erase hB
      have B_ne_M : B ≠ M := Finset.ne_of_mem_erase hB

      -- まず元々の交わり閉性: A∩B ∈ F
      have AB_in_F : A ∩ B ∈ F := inter_closed A B A_in_F B_in_F

      -- A ∩ B を "F.erase M" に入れるには、これが M でないことを示せばよい
      apply Finset.mem_erase_of_ne_of_mem
      · by_contra eqABM
        -- eqABM: A ∩ B = M
        -- ⇒ M ⊆ A, M ⊆ B
        have MsubA : M ⊆ A := by rw [←eqABM]; apply Finset.inter_subset_left
        have MsubB : M ⊆ B := by rw [←eqABM]; apply Finset.inter_subset_right
        -- M_max: M ⊆ A ∧ A∈F ⇒ A=M, あるいは矛盾
        let eqA := M_max A A_in_F MsubA
        contradiction
      · exact AB_in_F

  -- 以上で (F.erase M) も「univ を含み、交わりが閉じている」と示せた
  simp_all only [subset_refl, Finset.subset_univ, ne_eq, not_true_eq_false]

  namespace ExampleUsingMaxEqSome
--ここからは集合として、最大の元が存在するということ。largestCard_spec がメイン定理。

/--/
`maxCard l` : リスト `l : List (Finset α)` の各 `s.card` のうち最大値。
-/
def maxCard (l : List (Finset α)) : Nat :=
  (l.map (·.card)).max?.getD 0

--`maxCardElements l` :リスト `l` 内で要素数が `maxCard l` と一致する全ての集合をフィルタリングして返す。必要ない気もする。
def maxCardElements (l : List (Finset α)) : List (Finset α) :=
  l.filter (λ s => s.card = maxCard l)

lemma card_eq_max  {l : List (Finset α)} {s : Finset α}
  (hs_in_l : s ∈ l)
  (hm_forall : ∀ a ∈ l, a.card ≤ s.card)
  (hm_in : ∃ a ∈ l, a.card = s.card) :
  s.card = (l.map (fun x ↦ x.card)).max?.getD 0 :=
by
  -- `hm_in` から `s.card` がリスト内のカード数に等しいことを取り出す
  obtain ⟨a, ha_in_l, ha_eq⟩ := hm_in
  -- `hm_forall` によって `s.card` はリスト内のすべてのカード数以上
  have h_max : ∀ b ∈ l.map (fun x ↦ x.card), b ≤ s.card := by
    intro b hb
    obtain ⟨x, hx_in_l, rfl⟩ := List.mem_map.mp hb
    exact hm_forall x hx_in_l
  -- リストの最大値は `s.card` に等しい
  let ls := l.map (fun x ↦ x.card)
  have ls_ne : ls ≠ [] := by
    simp_all only [ne_eq, List.map_eq_nil_iff, not_false_eq_true]
    simp_all only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true, List.map_eq_nil_iff, ls]
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [List.not_mem_nil]
  let lm := List.max?_spec ls_ne
  obtain ⟨m, hm⟩ := lm
  have :∃ ms:Finset α , ms ∈ l ∧ ms.card = m :=
  by
    use a
    use ha_in_l
    simp_all only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true, ne_eq,
      List.map_eq_nil_iff, ls]
    obtain ⟨left, right⟩ := hm
    obtain ⟨left_1, right⟩ := right
    obtain ⟨w, h⟩ := right
    obtain ⟨left_2, right⟩ := h
    subst right
    refine le_antisymm ?_ ?_
    · simp_all only
    · simp_all only
  obtain ⟨ms, hms⟩ := this
  simp_all only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true, ne_eq, List.map_eq_nil_iff,
    Option.getD_some, ls]
  obtain ⟨left, right⟩ := hm
  obtain ⟨left_1, right_1⟩ := hms
  obtain ⟨left_2, right⟩ := right
  obtain ⟨w, h⟩ := right
  obtain ⟨left_3, right⟩ := h
  subst right
  refine le_antisymm ?_ ?_
  · simp_all only
  · simp_all only

--最大値を持つ集合をとって、それが最大の大きさである保証をする定理。この形でなくて、maxCardElementsが空でないことを示せば十分かも。
theorem largestCard_spec  (l : List (Finset α)) (hne : l ≠ []) :
    maxCardElements l ≠ [] := by

  -- 定義を開く
  unfold maxCardElements maxCard

  -- l.map (·.card) を一旦 l' としておく
  set l' := l.map (·.card) with hl'

  -- リスト l が空でないなら、l' も空でない
  have l'_ne : l' ≠ [] := by
    intro contra
    -- map後のリストが空なら、元のリストも空になるはずなので矛盾
    have : l.length = 0 := by
      simp_all only [ne_eq, List.map_eq_nil_iff, l']
    simp_all only [ne_eq, List.map_eq_nil_iff, l']
  /-
    ここで仮定されている補題 `List.max?_spec` を使う：
      List.max?_spec l'_ne : ∃ m, l'.max? = some m ∧ (∀ x ∈ l', x ≤ m) ∧ m ∈ l'
  -/
  rcases List.max?_spec l'_ne with ⟨m, hm_eq, hm_forall, hm_in⟩
  rw [← hm_eq] at *
  simp only [Option.getD_some] at hm_eq

  -- m ∈ l' とは ∃ s ∈ l, s.card = m の意味
  rcases List.mem_map.mp hm_in with ⟨s, hs_in_l, rfl⟩

  -- s.card = m かつ s ∈ l なので、filter で残る => maxCardElements l に含まれる。  -- つまり filter 結果は空でない
  simp_all [l']

  let ce := card_eq_max hs_in_l hm_forall hm_in
  use s

end ExampleUsingMaxEqSome
