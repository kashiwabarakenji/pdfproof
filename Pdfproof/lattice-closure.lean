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
import Init.Data.List.MinMax
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset

set_option maxHeartbeats 2000000

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

--使ってない。集合のほうにもってきて考えるのは、筋が良くないかも。Listのほうに変換して共通部分をとったほうがいい。それがこの次の補題。
--Finsetでない一般のSetの平行集合族の場合は別のファイルで考える。
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

--sを含むもので共通部分をとってもやはりsを含むことを証明する。どのような補題を示せばいいのか。集合族の大きさに関する帰納法が使える補題を設定する。

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

  have h2 := intersectionExtension F sval this
  simp_all only [Finset.mem_subtype, sval]
  obtain ⟨val, property⟩ := x
  simp_all only [Finset.mem_subtype]

  apply h2
  simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right, exists_const]--

noncomputable def closure_operator_from_SF {α :Type} [DecidableEq α][Fintype α] (F: SetFamily α) [DecidablePred F.sets]: SetFamily.preclosure_operator F :=
  let cl := fun s =>
    let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
    let ios := (finsetInter (F.ground.powerset.filter (fun (t:Finset α) => F.sets t ∧ sval ⊆ t)))
    ios.subtype (λ x => x ∈ F.ground)
{
  Family := F,
  cl := cl
  --extensive := extensive_from_SF F, -- 明示的に補題を渡す
  --monotone := monotone_closure_operator F cl,   -- 明示的に補題を渡す
  --/そとに出そうとしたがheartbeat問題が出たので、戻した。clの共用問題などなかなか難しい。
  extensive :=
  by
    intro s
    let sval :=s.map ⟨Subtype.val, Subtype.val_injective⟩
    intro x
    intro h
    --simp_all
    have h1 : s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ F.ground := by
      obtain ⟨val, property⟩ := x
      intro x hx
      simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right,
        exists_eq_right]
      obtain ⟨w, h_1⟩ := hx
      simp_all only

    have : sval ∈ F.ground.powerset := by
      simp_all only [Finset.mem_powerset]

    have h2 := intersectionExtension F sval this
    simp_all only [Finset.mem_powerset, Finset.mem_subtype, sval]
    obtain ⟨val, property⟩ := x
    simp_all only [Finset.mem_subtype, cl]

    apply h2
    simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,
      exists_const]


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


--namespace max?exist

open List

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
lemma mini_lem [LinearOrder α] (a b:α) (bs:List α ): foldl max (a ⊔ b) bs = a ⊔ foldl max b bs :=
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
          simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, mem_cons, forall_const, sup_eq_left]
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
          simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, mem_cons, forall_const, sup_eq_right]

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
    simp_all only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true, map_eq_nil_iff, ls]
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [not_mem_nil]
  let lm := List.max?_spec ls_ne
  obtain ⟨m, hm⟩ := lm
  have :∃ ms:Finset α , ms ∈ l ∧ ms.card = m :=
  by
    use a
    use ha_in_l
    simp_all only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true, ne_eq,
      map_eq_nil_iff, ls]
    obtain ⟨left, right⟩ := hm
    obtain ⟨left_1, right⟩ := right
    obtain ⟨w, h⟩ := right
    obtain ⟨left_2, right⟩ := h
    subst right
    refine le_antisymm ?_ ?_
    · simp_all only
    · simp_all only
  obtain ⟨ms, hms⟩ := this
  simp_all only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, implies_true, ne_eq, map_eq_nil_iff,
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
  rcases max?_spec l'_ne with ⟨m, hm_eq, hm_forall, hm_in⟩
  rw [← hm_eq] at *
  simp only [Option.getD_some] at hm_eq

  -- m ∈ l' とは ∃ s ∈ l, s.card = m の意味
  rcases List.mem_map.mp hm_in with ⟨s, hs_in_l, rfl⟩

  -- s.card = m かつ s ∈ l なので、filter で残る => maxCardElements l に含まれる。  -- つまり filter 結果は空でない
  simp_all [l']

  let ce := card_eq_max hs_in_l hm_forall hm_in
  use s

end ExampleUsingMaxEqSome

--ここから下は、閉集合族から極大なものをひとつとっても閉集合族になることを示す部分。

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
----------------------------------------------------------------
--setsの共通部分は、またsetsになることの証明。idempotentの証明に使う。

lemma insert_foldr_inter {α : Type} [DecidableEq α] [Fintype α]
  (x : Finset α) (S' : Finset (Finset α)) (x_not_mem : x ∉ S') :
  x ∩ foldr (fun x acc ↦ x ∩ acc) Finset.univ S'.toList =
  foldr (fun x acc ↦ x ∩ acc) Finset.univ (insert x S').toList :=
by
  -- `Finset.toList_insert` を利用して順序が置換であることを取得
  have h_perm : List.Perm (insert x S').toList (x :: S'.toList) :=
  by
    apply Finset.toList_insert
    simp_all only [not_false_eq_true]

  -- `foldr` の順序不変性を利用して置換に基づき両辺を比較
  --暗黙に使っている？
  have h_comm : LeftCommutative (fun (x acc : Finset α) ↦ x ∩ acc) :=
  by
    --fun a b c => by simp [Finset.inter_assoc, Finset.inter_comm]
    constructor
    intro a₁ a₂ b
    ext a : 1
    simp_all only [Finset.mem_inter]
    apply Iff.intro
    · intro a_1
      simp_all only [and_self]
    · intro a_1
      simp_all only [and_self]

  -- `List.Perm.foldr_eq` を適用して両辺を比較
  rw [List.Perm.foldr_eq h_perm]
  simp_all only [foldr_cons]



  -- F.setsはintersection_closedだが、S'はintersection closedとは限らない。
  -- Fは帰納法で大きくなったり、小さくなったりせずに、Sが変わる。
  --極大な元を取ったりしなくても、帰納法が使える。よって、極大な集合の存在定理は無駄になったかも。
theorem finite_intersection_in_C {α : Type} [DecidableEq α][Fintype α]
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
  -- 帰納ステップ: S = insert x S' の場合

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

      --(h_all x (Finset.mem_insert_self x S')) h_inter_S'
  -- Finset.induction_on を利用して証明を完成
  intro S--h_nonempty h_all
  induction S using Finset.induction_on with
  | empty =>
      -- 矛盾: S が空集合で Nonempty を満たすことはない
      intro h_nonempty
      exfalso
      exact False.elim (Finset.not_nonempty_empty h_nonempty)
  | @insert a s a_notin_s S'  =>
      -- 帰納ステップ: S = insert x S'
      --protected theorem induction_on {α : Type*} {p : Finset α → Prop} [DecidableEq α] (s : Finset α)
      --(empty : p ∅) (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : p s :=
      intro h_nonempty h_all

      cases s.eq_empty_or_nonempty with
      | inl h_empty =>
          -- S' = ∅ の場合
          subst h_empty
          simp_all only [Finset.mem_singleton, forall_eq, Finset.mem_insert, forall_eq_or_imp, and_imp,
            Finset.not_mem_empty, not_false_eq_true, Finset.not_nonempty_empty, forall_const, not_isEmpty_of_nonempty,
            IsEmpty.forall_iff, insert_emptyc_eq, Finset.singleton_nonempty]
      | inr h_nonempty_S =>
          -- S' ≠ ∅ の場合
          simp_all only [Finset.mem_singleton, forall_eq, Finset.mem_insert, forall_eq_or_imp, and_imp, or_true,
            implies_true, forall_const, Finset.insert_nonempty, not_false_eq_true]

lemma inter_lemma {α : Type} [DecidableEq α]
  (p : α → Prop) [DecidablePred p]
  (A B : Finset (Subtype p)) :
  (A ∩ B).map ⟨Subtype.val, Subtype.val_injective⟩ =
  A.map ⟨Subtype.val, Subtype.val_injective⟩ ∩ B.map ⟨Subtype.val, Subtype.val_injective⟩ :=
by
  -- 要素ベースの証明を行うため、ext を使う
  ext x
  -- 両辺の要素を展開して比較
  simp only [Finset.mem_map, Finset.mem_inter]
  constructor
  · -- (→) 方向: 左辺に属するなら右辺にも属する
    rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
    constructor
    · exact ⟨y, hyA, rfl⟩
    · exact ⟨y, hyB, rfl⟩
  · -- (←) 方向: 右辺に属するなら左辺にも属する
    rintro ⟨⟨yA, hyA, rfl⟩, ⟨yB, hyB, h_eq⟩⟩
    have h_eq_val := Subtype.ext h_eq
    subst h_eq_val
    cases h_eq
    simp_all only [Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right, exists_prop, and_true]
    obtain ⟨val, property⟩ := yB
    simp_all only

--このままだとSが空集合のときに成り立ってないよう。Subtypeを先にとるとunicになって、subtypeをあとにとると、F.groundになる。
--空でないという仮定を入れるのが良さそう。
lemma intersection_lemma  {α : Type} [DecidableEq α] [Fintype α] (p : α → Prop) [DecidablePred p] (S : Finset (Finset (Subtype p)))
 :  S.Nonempty → (finsetInter S).map ⟨Subtype.val, Subtype.val_injective⟩ = finsetInter (S.image (fun t => t.map ⟨Subtype.val, Subtype.val_injective⟩ )) :=
by
  -- 帰納法を用いるため、`S` のリスト表現に基づいて進めます。
  let L := S.toList
  /-have nonnil : L ≠ [] := by
    simp_all only [ne_eq, Finset.toList_eq_nil, L]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
  -/
  have main: L ≠ [] → (finsetInter S).map ⟨Subtype.val, Subtype.val_injective⟩ = finsetInter (S.image (fun t => t.map ⟨Subtype.val, Subtype.val_injective⟩ )) :=
  by
  -- `L` に基づいて帰納法を開始します。
    induction L generalizing S with
    | nil =>
      intro h_nonempty
      contradiction

    | cons head tail ih =>
      -- 再帰ステップ (`S = {head} ∪ tail`)
      intro h_nonempty
      simp [finsetInter, List.foldr]
      -- 帰納仮定を適用

      simp_all only [forall_const]
      simp_all only [ne_eq, reduceCtorEq, not_false_eq_true]
      by_cases h_empty : tail = []
      case pos =>
        --subst h_empty
        --simp_all only [not_true_eq_false, IsEmpty.forall_iff, implies_true]
        --L = head:: tail
        have :S = {head} := by
        --L= head:tailであることはどうやったらわかるか？

      case neg =>

        let iht := ih tail.toFinset h_empty
        apply ih
        simp_all only [not_false_eq_true]

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

 --下で使っている。上の補題を使っていて、それが未解決なので、これも未解決になっている。
 theorem finite_intersection_in_C_subtype
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
    finite_intersection_in_C F S_val h_S_val_nonempty h_S_val_all
  -- finsetInter S の値が finsetInter S_val に対応することを示す
  have : (finsetInter S).map ⟨Subtype.val, Subtype.val_injective⟩ =  finsetInter (S.image (fun t => t.map ⟨Subtype.val, Subtype.val_injective⟩ )):=
  by
    let il := intersection_lemma p S h_nonempty
    convert il

  simp_all only [Finset.image_nonempty, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    implies_true, p, S_val]
  convert h_finset_inter
  ext x a : 2
  simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,
    Finset.mem_image]

--intersection_lemmaと内容がかぶっているので、intersection_lemmaを使って証明する。
--空集合を排除する条件は必要か。
lemma cl_in_F_sets_lemma  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets] (s : Finset { x // x ∈ F.ground }):
   Finset.subtype (fun x ↦ x ∈ F.ground) (finsetInter (Finset.filter (fun t ↦ F.sets t ∧ s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ t) F.ground.powerset)) = finsetInter (Finset.image (fun t ↦ Finset.subtype (fun x ↦ x ∈ F.ground) t) (Finset.filter (fun t ↦ F.sets t ∧ s.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ t) F.ground.powerset)) :=
by
  --mapでなくて、imageで定義したので、map関係をコメントアウト。消して良い。
  /- 証明は完了しているが使ってない。
  have lemf: Finset.image (fun tt => Finset.filter (fun t => t ∈ F.ground) tt) filtered = filtered :=
  by
    simp_all only [filtered]
    rw [Finset.map_eq_image]
    ext x
    simp_all only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right_1⟩ := right_1
      subst right
      apply And.intro
      · simp_all only [Function.Embedding.coeFn_mk]
        intro x hx
        simp_all only [Finset.mem_filter]
      · apply And.intro
        · simp_all only [Function.Embedding.coeFn_mk]
          rwa [Finset.filter_true_of_mem left]
        ·
          simp_all only [Function.Embedding.coeFn_mk]
          intro x hx
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Finset.mem_filter]
          obtain ⟨w_1, h⟩ := hx
          simp_all only [and_true]
          apply right_1
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]
    · intro a
      simp_all only [Function.Embedding.coeFn_mk]
      obtain ⟨left, right⟩ := a
      obtain ⟨left_1, right⟩ := right
      apply Exists.intro
      · apply And.intro
        · apply And.intro
          on_goal 2 => apply And.intro
          on_goal 2 => {exact left_1
          }
          · simp_all only
          · simp_all only
        · rw [Finset.filter_true_of_mem left]
  -/
  --ilはlem1の証明に使っているがlem1がそもそもいらないのかも。
  --let il := (intersection_lemma (fun x => x ∈ F.ground) (filtered.image (λ t => t.subtype (λ x => x ∈ F.ground)))).symm
  --let tmpimage := tmp.image (fun t ↦ t.map ⟨Subtype.val, Subtype.val_injective⟩)
  --lem 1をコメントアウトするとエラーになる。simpで利用しているよう。なしでも証明は通るように書き換えた。
  /-
  have lem1:finsetInter tmpimage = Finset.map ⟨Subtype.val, Subtype.val_injective⟩ (finsetInter tmp_right) :=
  by
    simp_all only [Finset.map_inj, tmpimage, tmp, filtered,tmp_right]
    ext a : 1
    obtain ⟨val, property⟩ := a
    apply Iff.intro
    · intro a
      convert a
    · intro a
      convert a

  dsimp [tmpimage, tmp, tmp_right] at lem1
  rw [Finset.map_eq_image] at lem1 --コメントアウトするとエラ〜
  --rw [Finset.map_eq_image] at il --コメントアウトするとエラ〜
  -/

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

lemma finsetInter_empty {α : Type} [DecidableEq α] (s : Finset α) :
  s ∈ (∅ : Finset (Finset α)) → False :=
by
  intro h_mem
  exact Finset.not_mem_empty s h_mem

lemma subtype_image_val_eq_filter {α : Type} [DecidableEq α]
  (p : α → Prop) [DecidablePred p] (s : Finset α) :
  Finset.image Subtype.val (Finset.subtype p s) = s.filter p :=
by
  ext x
  simp [Finset.mem_image, Finset.mem_filter, Finset.mem_subtype]

lemma filter_eq_self_of_subset {α : Type} [DecidableEq α] [Fintype α]
  (p : α → Prop) [DecidablePred p] (s : Finset α) (h_subset : s ⊆ (Finset.univ.filter p)) :
  s.filter p = s :=
by
  ext x
  simp [Finset.mem_filter]
  intro a
  simpa using h_subset a

-- `cl` の定義
noncomputable def clcs {α : Type} [DecidableEq α] [Fintype α] (F : ClosureSystem α) [DecidablePred F.sets]
  (s : Finset { x // x ∈ F.ground }) : Finset { x // x ∈ F.ground } :=
  let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
  let ios := finsetInter (F.ground.powerset.filter (fun (t : Finset α) => F.sets t ∧ sval ⊆ t))
  ios.subtype (λ x => x ∈ F.ground)

-- `F.sets (clcs s)` の証明。 subtypeがらみで難しい。
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

-----------------------------------------------------------------------------------------
--ここから下は、sets sがclでs自身に映ること。ただし、この言明は、subtypeを考慮してないので最終的につかえるかわからない。

theorem finsetInter_eq_s {α : Type} [DecidableEq α] [Fintype α]
  (A : Finset (Finset α)) (s : Finset α)
  (h_mem : s ∈ A) (h_subset : ∀ t ∈ A, s ⊆ t) :
  finsetInter A = s :=
by
  induction A using Finset.induction_on with
  | empty =>
      -- 矛盾: A が空集合の場合、s ∈ A が成り立たない
      exfalso
      exact Finset.not_mem_empty s h_mem
  | insert a_not_s  ih =>
      rename_i ft  s' A' -- ftはFintype。使わないかも。

      -- A = insert x A' の場合
      rw [finsetInter]
      let ifi := insert_foldr_inter s' A' a_not_s
      rw [←ifi]
      by_cases h_eq : s ∈ A'
      case pos =>
        have :foldr (fun x acc ↦ x ∩ acc) Finset.univ A'.toList = s := by
          apply ih h_eq
          intro t ht
          exact h_subset t (Finset.mem_insert_of_mem ht)
        rw [this]
        have : s ⊆ s' := by
          apply h_subset s' (Finset.mem_insert_self s' A')
        ext
        simp [subset_def]
        rename_i this_1 a_1
        intro a_2
        subst this_1
        simp_all only [Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp, true_and]
        exact this a_2

      case neg =>
        -- サブケース: a ≠ s の場合
        -- この場合、s ⊆ a が成り立たない
        have : s = s' := by
          simp_all only [Finset.insert_eq_of_mem, implies_true, forall_const, IsEmpty.forall_iff, Finset.mem_insert,
            or_false, forall_eq_or_imp, subset_refl, true_and, not_false_eq_true]
        rw [←this]
        have : s ⊆ foldr (fun x acc ↦ x ∩ acc) Finset.univ A'.toList := by
          apply (finset_inter_subset_iff A' s).mp
          intro X a
          subst this
          simp_all only [Finset.insert_eq_of_mem, implies_true, forall_const, IsEmpty.forall_iff, not_false_eq_true,
            Finset.mem_insert, or_false, forall_eq_or_imp, subset_refl, true_and]
        rw [@Finset.inter_eq_left]
        exact this

  /-
noncomputable def closure_operator_from_CS {α :Type} [DecidableEq α][Fintype α] (C: ClosureSystem α) [DecidablePred C.sets]: SetFamily.closure_operator (C.toSetFamily)
  let cl := fun s =>
    let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
    let ios := (finsetInter (C.ground.powerset.filter (fun (t:Finset α) => C.sets t ∧ sval ⊆ t)))
    ios.subtype (λ x => x ∈ C.ground)
{
  Family := C.toSetFamily,
  cl := cl
  idempotent := by sorry
    --下に、閉集合族からひとつ要素を除いても閉集合族であることを示しているので、それを使えば、帰納法でidempotentを示せる。
    --clの像がsetsの元であることと、setsの元sがclにより、sに映ることを示せば良い。
-/

-- 帰納法の練習。消して良い。
theorem length_ge_one_implies_nonempty (xs : List α) :
  xs.length ≥ 1 → xs ≠ [] :=
by
  induction xs with
  | nil =>
      -- 基底ケース: xs = []
      intro h
      -- 矛盾を導く
      exfalso
      simp at h
  | cons x xs' ih =>
      -- 帰納ステップ: xs = x :: xs'
      intro _
      intro h_eq
      contradiction -- リストが空でないため、矛盾


theorem sum_commutative {α : Type} [AddCommMonoid α] (s : Finset ℕ) :
  s.sum id = s.sum id :=
by
  induction s using Finset.induction with
  | empty =>
      -- 空集合の場合
      simp [Finset.sum_empty]
  | insert x s' =>
      -- s = insert x s' の場合
      simp [Finset.sum_insert]


theorem length_append (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length :=
by
  induction xs with
  | nil =>
      -- xs = []
      rw [List.nil_append]
      simp -- 長さの性質
  | cons x xs ih =>
      -- xs = x :: xs
      rw [List.cons_append]
      simp
      simp_all only [List.length_append]
      omega

theorem example0 (n : Nat) : n + 0 = n :=
by
  let original := n
  induction n with
  | zero =>
    have: original = 0 := by
      simp
    dsimp [original]


  | succ n ih =>
      -- このブランチでは n = succ k
      rw [Nat.succ_add]

theorem nonempty_list_induction {α : Type} (P : List α → Prop) :
  (∀ x xs, P (x :: xs)) → ∀ l, l ≠ [] → P l :=
by
  intro h_base
  intro l h_nonempty
  induction l with
  | nil =>
      -- 空リストのケースでは矛盾を示す
      exfalso
      exact h_nonempty rfl
  | cons head tail =>
      -- 非空リストのケース
      exact h_base head tail

theorem example2 {α : Type} (L : List α) : L = [] ∨ ∃ x xs, L = x :: xs :=
by
  induction L with
  | nil =>
      -- `L = []` が成立するが、コンテキストには明示されない
      exact Or.inl rfl
  | cons head tail ih =>
      -- `L = head :: tail` が成立するが、コンテキストには明示されない
      exact Or.inr ⟨head, tail, rfl⟩
