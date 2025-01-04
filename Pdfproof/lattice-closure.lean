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

noncomputable def finsetInter {α : Type} [DecidableEq α][Fintype α] (A0 : Finset (Finset α)) : Finset α :=
  A0.toList.foldr (fun x acc => x ∩ acc) Finset.univ

lemma intersectionOfSubsets_def {α : Type} [DecidableEq α][Fintype α] (A0 : Finset (Finset α)) :
  finsetInter A0 = A0.toList.foldr (fun x acc => x ∩ acc) Finset.univ := by rfl


--帰納法を使わずに、finset_subfamily_intersection_closed_listで示す。
lemma intersectioninground {α : Type} [DecidableEq α][Fintype α] (C: ClosureSystem α) [DecidablePred C.sets]:
  ∀ s ∈ C.ground.powerset,  finsetInter (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)) ⊆ C.ground :=
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


lemma finset_inter_subset_iff_lem {α : Type} [DecidableEq α][Fintype α] (fl : List (Finset α)) (A : Finset α) :(∀ X ∈ fl, A ⊆ X ) → A ⊆ List.foldr (fun x acc ↦ x ∩ acc) Finset.univ fl := by
      cases hc:fl with
      | nil =>
        intro h
        subst hc
        simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.foldr_nil, Finset.subset_univ]
      | cons hd tl =>
        intro h
        have hdin : hd ∈ fl := by
          simp_all
        have hda : A ⊆ hd  := by
          apply h
          subst hc
          simp_all only [List.mem_cons, forall_eq_or_imp, true_or]
        have ih0: ∀ X ∈ tl, A ⊆ X := by
            intro XX
            intro hXX
            apply h
            subst hc
            simp_all only [List.mem_cons, forall_eq_or_imp, true_and, true_or, or_true]
        simp
        have ih: ∀ X ∈ tl, A ⊆ X → A ⊆ tl.foldr (fun x acc => x ∩ acc) Finset.univ := by
          intro X HX hh
          exact finset_inter_subset_iff_lem tl A ih0

        subst hc
        rw [@Finset.subset_inter_iff]
        constructor
        · simp_all only [List.mem_cons]

        · exact finset_inter_subset_iff_lem tl A ih0

lemma all_inters_subset_of_mem {α : Type} [DecidableEq α][Fintype α]
  (fl : List (Finset α)) :
  ∀ X ∈ fl,
    (fl.foldr (fun x acc => x ∩ acc) Finset.univ) ⊆ X := by

  -- リストに名前をつける

  -- リスト l に対して帰納法
  cases hl:fl with
  | nil =>
    -- このとき A0 が空なので，
    -- 「X ∈ A0」が起きたら矛盾
    intros X hX
    subst hl
    simp_all only [List.not_mem_nil]

  | cons hd tl =>
    -- 任意の X が hd :: tl に入るとき，
    -- 交わり (hd ∩ foldr(...tl)) が X の部分集合であることを示したい
    intros X hX
    -- foldr の定義展開
    simp_all only [List.foldr_cons]
    -- hd :: tl に属している X は，「X = hd」か「X ∈ tl」
    have hd_or_tl: X = hd ∨ X ∈ tl := by
      subst hl
      simp_all only [List.mem_cons]

    cases hd_or_tl with
    | inl hdc => -- X = hd の場合
      subst hdc
      subst hl
      simp_all only [List.mem_cons, true_or, Finset.inter_subset_left]
      -- hd ∩ (...) ⊆ hd は Finset.inter_subset_left で証明
    | inr tlc => -- X ∈ tl の場合
      -- まず，hd ∩ (...) は (...) の部分集合
      -- 帰納法の仮定で tl の交わりが X の部分集合
      let alli := all_inters_subset_of_mem tl X tlc
      simp at alli
      subst hl
      simp_all only [List.mem_cons, or_true]
      intro x hx
      simp_all only [Finset.mem_inter]
      obtain ⟨left, right⟩ := hx
      exact alli right

lemma finset_inter_subset_iff {α : Type} [DecidableEq α][Fintype α] (A0 : Finset (Finset α)) (A : Finset α) :
  (∀ X ∈ A0, A ⊆ X )  ↔ A ⊆ finsetInter A0  :=
  by
    constructor
    let fl := A0.toList
    dsimp [finsetInter]
    intro h
    apply finset_inter_subset_iff_lem fl A
    intro X a
    simp_all only [Finset.mem_toList, fl]

    intro h
    intro X hX
    have : finsetInter A0 ⊆ X:= by
      dsimp [finsetInter]
      apply all_inters_subset_of_mem A0.toList
      rw [Finset.mem_toList]
      exact hX
    exact h.trans this

lemma intersectionExtension {α : Type} [DecidableEq α][Fintype α] (C: ClosureSystem α) [DecidablePred C.sets]:
  ∀ s ∈ C.ground.powerset, s ⊆ finsetInter (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t))  :=
  by
    intro s
    intro hs
    simp_all only [Finset.mem_powerset]
    intro x
    intro hx
    let A0 := C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ s ⊆ t)
    have xall: ∀ X ∈ A0, s ⊆ X := by
      intro X
      intro hX
      simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_true, true_and, A0]
    let fi := (finset_inter_subset_iff A0 s).mp xall
    exact fi hx

noncomputable def listInter {α : Type u} [DecidableEq α] [Fintype α]
  (L : List (Finset α)) : Finset α :=
  L.foldr (fun x acc => x ∩ acc) Finset.univ

theorem listInter_mono {α : Type u} [DecidableEq α] [Fintype α]
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
      -- すなわち x :: xs の長さ = y :: ys の長さ から
      --  xs.length + 1 = ys.length + 1 を得たい
      -- しかしそのままだと Nat.succ.inj を直接は使えないことがある
      --すでにh_subが書き換わってしまっている。
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
    | inr h_1 => simp_all only [forall_const]

theorem listInter_mono'
    {α : Type} [DecidableEq α] [Fintype α]
    {L1 L2 : List (Finset α)}
    (h : ∀ (y : Finset α), y ∈ L2 → ∃ (x : Finset α), x ∈ L1 ∧ x ⊆ y)
    : listInter L1 ⊆ listInter L2 := by

  ------------------------------------------------------------------------
  -- 補助関数 aux:
  --   L2 を cases で分解しながら「すべての y ∈ L2 について ∃ x ∈ L1, x ⊆ y」
  --   という仮定のもとで listInter L1 ⊆ listInter L2 を示す。
  ------------------------------------------------------------------------
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
      ·
        ----------------------------------------------------------------
        -- まず listInter L1 ⊆ yy を示す
        ----------------------------------------------------------------
        -- h' から「yy ∈ L2 ⇒ ∃ x ∈ L1, x ⊆ yy」が取れる
        match h' yy (by simp [hl2]) with
        | ⟨xx, hx_in, hx_sub⟩ =>
          -- listInter L1 は L1 のすべての要素との共通部分
          -- 特に「L1 に属するどの要素にも含まれる」ので，
          -- L1 の要素 x に対して "listInter L1 ⊆ x" が言える
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
        ----------------------------------------------------------------
        -- 次に listInter L1 ⊆ listInter ys を示す
        ----------------------------------------------------------------
        -- ここで「ys の任意の要素 z」にも「∃ x ∈ L1, x ⊆ z」が成り立つことを示せば，
        -- 再帰呼び出し aux L1 ys ... で結論が得られる
        have : ∀ z ∈ ys, ∃ x ∈ L1, x ⊆ z := by
          intro z hz
          -- z が ys に属する ⇒ z は (y :: ys) に属するので h' から要素が得られる
          subst hl2
          simp_all only [List.mem_cons, forall_eq_or_imp]
        exact aux L1 ys this

  -- 以上で定義した aux を呼び出してゴールを示す
  exact aux L1 L2 h

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

noncomputable def closure_operator_from_CS {α :Type} [DecidableEq α][Fintype α] (C: ClosureSystem α) [DecidablePred C.sets]: SetFamily.closure_operator (C.toSetFamily) :=
  let cl := fun s =>
    let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
    let ios := (finsetInter (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ sval ⊆ t)))
    ios.subtype (λ x => x ∈ C.ground)
{
  Family := C.toSetFamily,
  cl := cl
  /-by --定義をletに移動。
    intro s
    let sval :=s.map ⟨Subtype.val, Subtype.val_injective⟩
    let ios := (finsetInter (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ sval ⊆ t)))
    exact ios.subtype (λ x => x ∈ C.ground)
  -/

  extensive :=
  by
    intro s
    let sval :=s.map ⟨Subtype.val, Subtype.val_injective⟩
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

    have : sval ∈ C.ground.powerset := by
      simp_all only [Finset.mem_powerset]

    have h2 := intersectionExtension C sval this
    simp_all only [Finset.mem_powerset, Finset.mem_subtype, sval]
    obtain ⟨val, property⟩ := x
    simp_all only [Finset.mem_subtype, cl]

    apply h2
    simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,
      exists_const]

  monotone := by
    have h1 : ∀ s t : Finset C.ground, s ⊆ t → cl s ⊆ cl t := by
      intro s
      intro t
      intro h
      simp_all only [Finset.subset_iff]
      intro x
      intro hx
      unfold cl

      /-have h2 : s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ t.map ⟨Subtype.val, Subtype.val_injective⟩ := by
        intro x
        intro hx
        simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right,
          exists_eq_right]
        obtain ⟨w, h_1⟩ := hx
        simp_all only
        simp_all
      -/
      let S := Finset.filter (fun (u:Finset α) => C.sets u ∧ s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ u) C.ground.powerset
      let T := Finset.filter (fun (u:Finset α) => C.sets u ∧ t.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ u) C.ground.powerset

      let fs := fun (u:Finset α) => C.sets u ∧ s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ u
      let ft := fun (u:Finset α) => C.sets u ∧ t.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ u
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

  idempotent := by sorry
  }
