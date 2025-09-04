--lattice-closure.leanの中のintersection_lemmaを証明するのが目標。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Init.Data.List.BasicAux
import Mathlib.Data.Finset.Dedup
import Pdfproof.lattice_common
import LeanCopilot

variable {α : Type}  [DecidableEq α] [Fintype α]

open Finset

--共通に使われる補題。
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


--sを含むもので共通部分をとってもやはりsを含むことを証明する。リストを使った命題にして、帰納的に分解している。
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
          exact finset_inter_subset_iff_lem tl A ih0 --ここで帰納法の仮定を使っている。

        subst hc
        rw [@Finset.subset_inter_iff]
        constructor
        · simp_all only [List.mem_cons]

        · exact finset_inter_subset_iff_lem tl A ih0



--extensiveの証明で使われている。finset_inter_subset_iff_lemを使っている。
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

--foldrを帰納的に分解している。idempotentの証明で使われている。
lemma insert_foldr_inter {α : Type} [DecidableEq α] [Fintype α]
  (x : Finset α) (S' : Finset (Finset α)) (x_not_mem : x ∉ S') :
  x ∩ List.foldr (fun x acc ↦ x ∩ acc) Finset.univ S'.toList =
  List.foldr (fun x acc ↦ x ∩ acc) Finset.univ (insert x S').toList :=
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
  simp_all only [List.foldr_cons]


--noncomputable def finsetInter {α : Type} [DecidableEq α][Fintype α] (A0 : Finset (Finset α)) : Finset α :=
--  A0.toList.foldr (fun x acc => x ∩ acc) Finset.univ

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

--intersection_lemmaで表示されている。
theorem h_image_toList {α β : Type} [DecidableEq β]
    (S : Finset α) (f : α → β) :--(h_inj : Function.Injective f) :
    List.toFinset ((S.image f).toList) = List.toFinset (S.toList.map f) := by
  -- まず、左辺を展開
  have h_left : List.toFinset ((S.image f).toList) = S.image f := by
    -- toListとtoFinsetは互いに逆の関係
    simp_all only [toList_toFinset]

  -- 次に、右辺を展開
  have h_right : List.toFinset (S.toList.map f) = S.image f := by
    -- toListとmapの性質を使用
    simp_all only [toList_toFinset]
    ext a : 1
    simp_all only [List.mem_toFinset, List.mem_map, mem_toList, mem_image]

  -- 両辺が等しいことを示す
  rw [h_left, h_right]
  -- リストの要素が同じで長さも同じなら、リストは等しい
  --exact List.eq_of_perm (List.Perm.of_eq_length_and_mem h_length h_elem)
/-
instance inter_left_commutative {α : Type} [DecidableEq α] : LeftCommutative (fun (x1 x2 : Finset α) => x1 ∩ x2) :=
by
  constructor
  intro a₁ a₂ b
  ext a : 1
  simp_all only [mem_inter]
  apply Iff.intro
  · intro a_1
    simp_all only [and_self]
  · intro a_1
    simp_all only [and_self]
-/

--cl_in_F_sets_lemmaの証明に使われている。o1作成がもとになっている。
lemma intersection_lemma
  {α : Type} [DecidableEq α] [Fintype α]
  (p : α → Prop) [DecidablePred p]
  (S : Finset (Finset (Subtype p)))
  (h : S.Nonempty)
  : (finsetInter S).map ⟨Subtype.val, Subtype.val_injective⟩
    = finsetInter (S.image (fun t => t.map ⟨Subtype.val, Subtype.val_injective⟩)) :=
by
  -- finsetInter S = foldr (· ∩ ·) univ (S.toList)
  -- であることを展開して扱います。

  -- Step 1. S が空の場合は仮定 h: S.Nonempty と矛盾。
  --         よって空でないリスト (S.toList) を得ます。
  set l := S.toList with l_def
  have : l ≠ [] := by
    intro hl
    simp_all only [Finset.toList_eq_nil, Finset.not_nonempty_empty, l]

  -- Step 2. S.image (λ t => t.map val) の toList は
  --         l.map (λ t => t.map val) と同じ要素からなる (順序は不問)。
  --         intersection (∩) は可換・結合的なので
  --         リストの順序に依存せず foldr の結果が同じになることを使います。
  set l' := (S.image (fun t => t.map ⟨Subtype.val, Subtype.val_injective⟩)).toList with l'_def

  -- ここで、l' は l.map (...) の要素と同値 (順序のみ違う) であることを使い、
  -- foldr (· ∩ ·) が可換・結合的な演算であるので
  -- foldr の結果が対応することを示せば十分です。

  -- Step 3. l による帰納法で証明します。
  --         (実際には l が空でないのでパターンは cons だけ考えればよい)

  -- 補助定義：foldInter の略記 (Subtype p 版) とそれを map val したもの
  let foldInterSubtype : List (Finset (Subtype p)) → Finset (Subtype p)
    := fun xs => xs.foldr (· ∩ ·) Finset.univ
  let foldInterSubtypeMapVal : List (Finset (Subtype p)) → Finset α
    := fun xs => (foldInterSubtype xs).map ⟨Subtype.val, Subtype.val_injective⟩

  -- 同様に α 版
  let foldInterAlpha : List (Finset α) → Finset α
    := fun xs => xs.foldr (· ∩ ·) Finset.univ

  -- 目標は foldInterSubtypeMapVal l = foldInterAlpha (l.map (·.map val))
  -- ただし順序が S.image (...) と一致しなくてもよい(順序の違いは可換性で吸収)。

  -- 帰納法に必要な補題を作り、同時に証明します。
  -- list が要素 t :: ts の形に分解できる場合のみ示せば十分です。
  suffices fold_map_eq : ∀ (xs : List (Finset (Subtype p))),
    xs ≠ [] → ((foldInterSubtype xs).map ⟨Subtype.val, Subtype.val_injective⟩) = (foldInterAlpha (xs.map (fun A => A.map ⟨Subtype.val, Subtype.val_injective⟩)))
  from
  by
    -- 最終的にこの補題 fold_map_eq を使ってゴールを示します。
    -- S.toList = l なのでちょうど適用できます。
    -- S.image (...) の toList = l' は l.map (...) の要素と同値なので
    -- foldMap の可換性から両者の foldr 結果は一致します。
    rw [finsetInter, finsetInter] --この結果も両辺はFinsetである。
    --search_proof
    let fm := fold_map_eq S.toList this
    dsimp [foldInterSubtypeMapVal, foldInterSubtype, foldInterAlpha] at fm
    rw [←l_def, ←l'_def]
    rw [fm]
    dsimp [l', l]
    --以下の補題でリストが等しいということを示さずに、集合として等しければよい。
    have finset_eq:(List.map (fun A ↦ map ⟨Subtype.val, Subtype.val_injective⟩ A) S.toList).toFinset = (image (fun t ↦ map ⟨Subtype.val, Subtype.val_injective⟩ t) S) :=
    by
      simp_all only [l, l']
      have h_image_toList2 := h_image_toList S (fun tt => tt.map ⟨Subtype.val, Subtype.val_injective⟩)
      --言明はリストとして等しいことを示さないといけないが、補題は、Finsetとして等しいことを示している。
      simp_all only [toList_toFinset]
    --simp_all only [toList_toFinset, List.map_const', length_toList, l, l']

    rw [←finset_eq]
    simp_all
    rw [←finset_eq]
    --foldrが可換であることを使って、foldrの結果が一致することを示す。
      --rw [Finset.inter_assoc, Finset.inter_comm b, ←Finset.inter_assoc]
    have nodup1: List.Nodup (List.map (fun A ↦ map ⟨Subtype.val, Subtype.val_injective⟩ A) S.toList) := by
      apply List.Nodup.map
      · apply Finset.map_injective
      · exact Finset.nodup_toList _
    have nodup2: List.Nodup ((image (fun t ↦ map ⟨Subtype.val, Subtype.val_injective⟩ t) S).toList) := by
      apply Finset.nodup_toList
    have lp :List.Perm (List.map (fun A ↦ map ⟨Subtype.val, Subtype.val_injective⟩ A) S.toList) (image (fun t ↦ map ⟨Subtype.val, Subtype.val_injective⟩ t) S).toList :=
    by
      --have perm_eq : (List.map (fun A ↦ map ⟨Subtype.val, Subtype.val_injective⟩ A) S.toList).perm (image (fun t ↦ map ⟨Subtype.val, Subtype.val_injective⟩ t) S).toList :=
      --  by
      simp at finset_eq
      apply List.perm_of_nodup_nodup_toFinset_eq nodup1 nodup2
      simp_all only [toList_toFinset]

    have left_comm : LeftCommutative (fun (x1 x2 : Finset α) => x1 ∩ x2) := by
      constructor
      intro a₁ a₂ b
      ext a : 1
      simp_all only [mem_inter]
      apply Iff.intro
      · intro a_1
        simp_all only [and_self]
      · intro a_1
        simp_all only [and_self]
    let perm_eq := List.Perm.foldr_eq lp (f := fun (x1 x2 : Finset α) => x1 ∩ x2)
    simp_all only

  -- fold_map_eq の本体を証明
  intro xs hxs
  --goal
  --map { toFun := Subtype.val, inj' := ⋯ } (foldInterSubtype xs) =
  --foldInterAlpha (List.map (fun A ↦ map { toFun := Subtype.val, inj' := ⋯ } A) xs)
  induction xs with
  | nil => contradiction  -- hxs との矛盾
  | cons x ys ih =>
    by_cases h_empty : ys = []
    case pos =>
      subst h_empty
      simp_all only [ne_eq, toList_eq_nil, not_true_eq_false, List.foldr_nil, List.map_nil, IsEmpty.forall_iff,
        List.cons_ne_self, not_false_eq_true, List.foldr_cons, inter_univ, List.map_cons, l, l', foldInterSubtype,
        foldInterAlpha]
    case neg =>
      -- foldInterSubtype (x :: ys) = x ∩ foldInterSubtype ys
      -- map val すると inter_lemma から
      -- map val x ∩ map val (foldInterSubtype ys)
      -- 帰納法的に map val (foldInterSubtype ys) = foldInterAlpha (ys.map (·.map val)) が成り立てばよい。
      simp_all only [ne_eq, toList_eq_nil, reduceCtorEq, not_false_eq_true, List.foldr_cons, List.map_cons, l, l',
        foldInterSubtype, foldInterAlpha]

      calc
        (foldInterSubtype (x :: ys)).map ⟨Subtype.val, Subtype.val_injective⟩
          = (x ∩ foldInterSubtype ys).map ⟨Subtype.val, Subtype.val_injective⟩
            := by rfl
        _ = x.map ⟨Subtype.val, Subtype.val_injective⟩
              ∩ (foldInterSubtype ys).map ⟨Subtype.val, Subtype.val_injective⟩
            := by rw [inter_lemma]
        _ = x.map ⟨Subtype.val, Subtype.val_injective⟩
              ∩ foldInterAlpha (ys.map (fun A => A.map ⟨Subtype.val, Subtype.val_injective⟩))
            := by
                simp_all only [foldInterSubtype, foldInterAlpha]
                --exact @Finset.univ_inter α _
                -- 帰納法呼び出し
        -- いま x.map val と foldInterAlpha (ys.map (·.map val)) がある。
        -- これを foldInterAlpha ((x.map val) :: (ys.map (·.map val))) と等しくするには
        -- foldInterAlpha (x.map val :: list) = x.map val ∩ foldInterAlpha list
        -- の定義通り。
        _ = foldInterAlpha ((x.map ⟨Subtype.val, Subtype.val_injective⟩)
                          :: ys.map (fun A => A.map ⟨Subtype.val, Subtype.val_injective⟩))
            := by rfl

------
-----------------------------------------------------------------------------------------
--sets sがclでs自身に映ること。ただし、この言明は、また、subtypeを考慮してない。
--idempoteentの証明で使っている。
lemma finsetInter_eq_s {α : Type} [DecidableEq α] [Fintype α]
  (A : Finset (Finset α)) (s : Finset α)
  (h_mem : s ∈ A) (h_subset : ∀ t ∈ A, s ⊆ t) :
  finsetInter A = s :=
by
  induction A using Finset.induction_on with
  | empty =>
      -- 矛盾: A が空集合の場合、s ∈ A が成り立たない
      exfalso
      exact Finset.notMem_empty s h_mem
  | insert s' A' a_not_s  ih =>

      -- A = insert x A' の場合
      rw [finsetInter]
      let ifi := insert_foldr_inter s' A' a_not_s
      rw [←ifi]
      by_cases h_eq : s ∈ A'
      case pos =>
        have :List.foldr (fun x acc ↦ x ∩ acc) Finset.univ A'.toList = s := by
          apply ih h_eq
          intro t ht
          exact h_subset t (Finset.mem_insert_of_mem ht)
        rw [this]
        have : s ⊆ s' := by
          apply h_subset s' (Finset.mem_insert_self s' A')
        ext
        rename_i this_1 a_1
        constructor
        · exact fun a ↦ mem_of_mem_inter_right a
        · exact fun a ↦
          mem_inter_of_mem (this (h_subset s h_mem a)) (h_subset s h_mem (h_subset s h_mem a))

      case neg =>
        -- サブケース: a ≠ s の場合
        -- この場合、s ⊆ a が成り立たない
        have : s = s' := by
          simp_all only [Finset.insert_eq_of_mem, implies_true, forall_const, IsEmpty.forall_iff, Finset.mem_insert,
            or_false, forall_eq_or_imp, subset_refl, true_and, not_false_eq_true]
        rw [←this]
        have : s ⊆ List.foldr (fun x acc ↦ x ∩ acc) Finset.univ A'.toList := by
          apply (finset_inter_subset_iff A' s).mp
          intro X a
          subst this
          simp_all only [Finset.insert_eq_of_mem, implies_true, forall_const, IsEmpty.forall_iff, not_false_eq_true,
            Finset.mem_insert, or_false, forall_eq_or_imp, subset_refl, true_and]
        rw [@Finset.inter_eq_left]
        exact this

/-上で証明できたので、こちらはいらなくなった。そもそも証明できてないので、消す。
--intersection_lemmaの別の証明の試み。どっちかが証明できればいいが、どちらも証明の目処が立っていない。
lemma intersection_lemma2  {α : Type} [DecidableEq α] [Fintype α] (p : α → Prop) [DecidablePred p] (S : Finset (Finset (Subtype p)))
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
  have main: ∀ L:List (Finset (Subtype p)) ,L ≠ [] → (finsetInter L.toFinset).map ⟨Subtype.val, Subtype.val_injective⟩ = finsetInter (L.toFinset.image (fun t => t.map ⟨Subtype.val, Subtype.val_injective⟩ )) :=
  by
  -- `L` に基づいて帰納法を開始します。
    intro L
    induction L with
    | nil =>
      intro h_nonempty
      simp_all only [ne_eq, not_true_eq_false]

    | cons head tail ih =>
      -- 再帰ステップ (`S = {head} ∪ tail`)
      intro h_nonempty
      simp [finsetInter, List.foldr]
      -- 帰納仮定を適用
      --simp_all only [forall_const]
      --simp_all only [ne_eq, reduceCtorEq, not_false_eq_true]
      by_cases h_empty : tail = []
      case pos =>
        --simp_all only [not_true_eq_false, IsEmpty.forall_iff, implies_true]
        --L = head:: tail
        --subst h_empty
        subst h_empty
        simp_all only [ne_eq, not_true_eq_false, List.toFinset_nil, Finset.image_empty, IsEmpty.forall_iff, List.cons_ne_self,
          not_false_eq_true, insert_emptyc_eq, Finset.toList_singleton, List.foldr_cons, List.foldr_nil, Finset.inter_univ]
      case neg => --tail ≠ []のケース
        let iht := ih h_empty
        rw [finsetInter] at iht
        dsimp [finsetInter] at iht
        rw [Finset.map_eq_image]
        rw [Finset.map_eq_image] at iht
        dsimp [List.foldr]
        unfold List.foldr
        rw [insert]
        simp at iht
        --simp_all only [ne_eq, not_false_eq_true, forall_const, reduceCtorEq]
        split--ゴールを上のmatchで分解
        next x heq => --heqを見ると、空の場合。空の場合は考えなくても良い？
          simp_all only [Finset.toList_eq_nil]
          simp_all only [ne_eq, not_false_eq_true, forall_const, reduceCtorEq]
          split
          next x_1 heq_1 => simp_all only [Finset.toList_eq_nil, Finset.insert_ne_empty]
          next x_1 a as heq_1 => sorry
            --contradiction heqとheq_1がなんらかの矛盾が起こるのでは。
            --simp at heq_1

            --sorry --heq_1によると、こちらが帰納ケース
            --(insert (Finset.map { toFun := Subtype.val, inj' := ⋯ } head)   (Finset.image (fun t ↦ Finset.map { toFun := Subtype.val, inj' := ⋯ } t) tail.toFinset)).toList = a :: as
          --heq1 Finset.image Subtype.val Finset.univ = a ∩ foldr (fun x acc ↦ x ∩ acc) Finset.univ as
          --heq: Finset.instInsert.1 head tail.toFinset = ∅
          --左辺は全体集合。heq1だけで、矛盾が起きそう。a=Finset.univとなる。
        next x a as heq =>
          split
          next x_1 heq_1 => simp_all only [Finset.toList_eq_nil, Finset.insert_ne_empty]
          next x_1 a_1 as_1 heq_1 =>
            let il := inter_lemma p (a_1.subtype p) ((List.foldr (fun x acc ↦ x ∩ acc) Finset.univ as_1).subtype p)
            rw [List.foldr.eq_def]
            --rw [← @Function.Embedding.coe_subtype]
            split
            sorry

            rw [Finset.map_eq_image] at il
            --convert il.symm
            --search_proof
            sorry

  intro Snonempty
  have Lnonempty: L ≠ [] :=
  by
    simp_all only [ne_eq, Finset.toList_eq_nil, L]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [Finset.not_nonempty_empty]
  have :L.toFinset = S := by
    simp_all only [ne_eq, Finset.toList_eq_nil, Finset.toList_toFinset, L]
  rw [←this]
  exact main L Lnonempty
-/
/-使ってないので消す。List.perm_of_nodup_nodup_toFinset_eqを使えばいい。
--------------------------------------------------------------------------------
-- 1) 「重複なし & 長さが同じ & 要素が同じ」ならリストは等しい
--------------------------------------------------------------------------------

lemma eq_of_nodup_of_length_eq_of_forall_mem_iff
  {α : Type} [DecidableEq α]
  {l1 l2 : List α}
  (h1 : l1.Nodup) (h2 : l2.Nodup)
  (hlen : l1.length = l2.length)
  (helem : ∀ x, x ∈ l1 ↔ x ∈ l2)
: l1 = l2 := by
  /-
   -- `List.Nodup` の場合、長さと要素の一致からリスト全体の一致を示せる
  apply List.eq_of_perm_of_nodup この定理がない。
  -- リストの順列性を証明
  apply List.perm_of_mem_iff この定理もない。
  -- 要素の存在が互いに対応していることを利用
  exact helem
  -- `Nodup` の条件
  exact h1
  -/
  --List.perm_of_nodup_nodup_toFinset_eq
  --theorem
  --∀ {α : Type u_1} [inst : DecidableEq α] {l l' : List α},   List.Nodup l → List.Nodup l' → List.toFinset l = List.toFinset l' → List.Perm l l'


  -- l1 をパターンマッチしながらリスト帰納法
  induction l1 generalizing l2
  case nil =>
    -- l1 = [] のケース
    -- 長さが同じ ⇒ l2 も空リスト
    simp_all only [List.nodup_nil, List.length_nil, List.not_mem_nil, false_iff, List.nil_eq]
    simpa using hlen.symm
  case cons x xs ih =>
    -- l1 = x :: xs のケース
    match l2 with
    | [] =>
      -- l2 = [] とすると長さが同じという仮定に反する
      cases hlen
    | y :: ys =>
      ------------------------------------------------------------------------
      -- x が l2 に属することを「要素集合が同じ」から得る
      ------------------------------------------------------------------------
      have x_in_l2 : x ∈ y :: ys := (helem x).1 (List.mem_cons_self x xs)
      cases x_in_l2 with
      | head hxy =>
        ----------------------------------------------------------------------
        -- x_in_l2 = inl hxy ⇒ x = y
        ----------------------------------------------------------------------
        -- すると l2 = x :: ys, 先頭が一致。
        -- あとは xs と ys について同じリストになることを示せばよい。
        --rw [←hxy] at *
        -- 「x :: xs = x :: ys」と示したい。要するに xs = ys。
        -- 帰納法 ih を使う。
        apply (congrArg (List.cons x)) (ih
          -- xs.nodup
          (by rw [List.nodup_cons] at h1; exact h1.2)
          -- ys.nodup
          (by rw [List.nodup_cons] at h2; exact h2.2)
          -- length(xs) = length(ys)
          (by apply Nat.succ_injective; exact hlen)
          -- 要素集合 xs ↔ ys
          (by
            intro a
            specialize helem a
            -- helem : a ∈ x::xs ↔ a ∈ x::ys
            -- 先頭 x は除外して考える形へ書き換え
            rw [List.mem_cons, List.mem_cons] at helem
            simp_all only [List.nodup_cons, List.length_cons, add_left_inj, forall_const]
            obtain ⟨left, right⟩ := h1
            obtain ⟨left_1, right_1⟩ := h2
            apply Iff.intro
            · intro a_1
              simp_all only [or_true, true_iff]
              cases helem with
              | inl h =>
                subst h
                simp_all only
              | inr h_1 => simp_all only
            · intro a_1
              simp_all only [or_true, iff_true]
              cases helem with
              | inl h =>
                subst h
                simp_all only
              | inr h_1 => simp_all only
          )
        )

      | tail x_in_ys =>
        ----------------------------------------------------------------------
        -- x_in_l2 = inr x_in_ys ⇒ x ≠ y かつ x ∈ ys
        ----------------------------------------------------------------------
        -- 同様に y ∈ l1 ⇒ y ∈ x::xs ⇒ y = x ∨ y ∈ xs
        have y_in_l1 : y ∈ x :: xs := (helem y).2 (List.mem_cons_self y ys)
        match y_in_l1 with
        | .head hyx =>
          -- y = x とすると x ≠ y と矛盾
          sorry
        | .tail x y_in_xs =>
          -- x ≠ y, x ∈ ys, y ∈ xs
          -- これは "クロス状" の入り方をしており、どこかで nodup と衝突する
          --
          -- l1 = x::xs は nodup なので「x は xs に含まれない」はず
          rw [List.nodup_cons] at h1

          have : x ∉ xs := by simp_all only [List.nodup_cons, List.mem_cons, forall_const, List.length_cons,
            add_left_inj, not_false_eq_true]
          -- しかし x_in_ys, y_in_xs, x≠y という状況から
          -- xs, ys の要素が入り乱れて最終的に矛盾を導ける
          --
          -- ここでは簡潔に「x ∈ ys ⇒ l2 = y::ys には先頭y≠x ⇒ x は tail ys にいる」
          --  さらに y ∈ xs ⇒ l1 = x::xs には先頭x≠y ⇒ y は tail xs にいる
          --  すると xs, ys 双方に x,y が混在し、いずれ nodup に矛盾
          sorry

--------------------------------------------------------------------------------
-- 2) メイン補題: (S.image f).toList = S.toList.map f
--    injective の場合のみ成り立つ
--------------------------------------------------------------------------------
-/

/-
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

-/
