--lattice-closure.leanの中のintersection_lemmaを証明するのが目標。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Init.Data.List.BasicAux
import Mathlib.Data.Finset.Dedup
import LeanCopilot

variable {α : Type}  [DecidableEq α] [Fintype α]

open Finset

noncomputable def finsetInter {α : Type} [DecidableEq α][Fintype α] (A0 : Finset (Finset α)) : Finset α :=
  A0.toList.foldr (fun x acc => x ∩ acc) Finset.univ

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

--o1作成 closure-lemmaに移すか。
lemma intersection_lemma
  {α : Type} [DecidableEq α] [Fintype α]
  (p : α → Prop) [DecidablePred p]
  (S : Finset (Finset (Subtype p)))
  (h : S.Nonempty)
  : (finsetInter S).map ⟨Subtype.val, Subtype.val_injective⟩
    = finsetInter (S.image (fun t => t.map ⟨Subtype.val, Subtype.val_injective⟩)) := by
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
    simp_all only [perm_eq]

  -- fold_map_eq の本体を証明
  intro xs hxs
  match xs with
  | [] => contradiction  -- hxs との矛盾
  | x :: ys =>
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

               have ih : (foldInterSubtype ys).map ⟨Subtype.val, Subtype.val_injective⟩ =
                    foldInterAlpha (ys.map (fun A => A.map ⟨Subtype.val, Subtype.val_injective⟩))
                := by sorry
                --apply fold_map_eq ys (List.cons_ne_nil x ys hxs)

               rw [ih]
      -- いま x.map val と foldInterAlpha (ys.map (·.map val)) がある。
      -- これを foldInterAlpha ((x.map val) :: (ys.map (·.map val))) と等しくするには
      -- foldInterAlpha (x.map val :: list) = x.map val ∩ foldInterAlpha list
      -- の定義通り。
      _ = foldInterAlpha ((x.map ⟨Subtype.val, Subtype.val_injective⟩)
                        :: ys.map (fun A => A.map ⟨Subtype.val, Subtype.val_injective⟩))
          := by rfl

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

lemma image_toList_eq_map
  {α β : Type} [DecidableEq α] [DecidableEq β]
  {f : α → β} (hf : Function.Injective f)
  (S : Finset α)
  : (S.image f).toList = S.toList.map f := by

  -- 証明方針:
  --   1) 両辺とも nodup
  --   2) 長さが等しい
  --   3) 要素が一致する
  -- 上の eq_of_nodup_of_length_eq_of_forall_mem_iff により結論付ける

  let LHS := (S.image f).toList
  let RHS := S.toList.map f

  ----------------------------------------------------------------
  -- (1) nodup : S.image f の toList は常に重複なし
  --             S.toList は重複なし、f が injective なら map しても重複なし
  ----------------------------------------------------------------
  have hLHS_nodup : LHS.Nodup := (S.image f).nodup_toList
  have hRHS_nodup : RHS.Nodup := by sorry

  ----------------------------------------------------------------
  -- (2) length が等しい
  --     |S.image f| = |S| (injective f のとき) ⇒ length 一致
  ----------------------------------------------------------------
  have hlen : LHS.length = RHS.length := by
    calc
      LHS.length
        = (S.image f).card      := by rw [Finset.length_toList]
      _ = S.card                := by rw [card_image_of_injective _ hf]
      _ = S.toList.length       := (Finset.length_toList S).symm
      _ = RHS.length            := by rw [List.length_map]

  ----------------------------------------------------------------
  -- (3) ∀ x, x ∈ LHS ↔ x ∈ RHS
  ----------------------------------------------------------------
  have hmem : ∀ x, x ∈ LHS ↔ x ∈ RHS := by
    intro x
    constructor
    · -- (→) x ∈ LHS ⇒ x ∈ RHS
      intro hx
      rw [Finset.mem_toList] at hx
      -- x ∈ S.image f ⇒ ∃ a ∈ S, f a = x
      simp_all only [length_toList, List.length_map, mem_image, List.mem_map, mem_toList, LHS, RHS]
    · -- (←) x ∈ RHS ⇒ x ∈ LHS
      intro hx
      -- x ∈ S.toList.map f ⇒ ∃ a, a ∈ S.toList ∧ f a = x
      rcases List.mem_map.mp hx with ⟨a, ha_list, fa_eq_x⟩
      rw [Finset.mem_toList] at ha_list
      -- f a が S.image f に属する
      rw [Finset.mem_toList]
      rw [←fa_eq_x]
      exact Finset.mem_image_of_mem f ha_list

  ----------------------------------------------------------------
  -- (4) 上の補題を使って両リストが等しい
  ----------------------------------------------------------------
  exact eq_of_nodup_of_length_eq_of_forall_mem_iff
    hLHS_nodup
    hRHS_nodup
    hlen
    hmem
/-
/--
  Injective な関数 `f : α → β` について、
  `(S.image f).toList` は `S.toList.map f` と同じリストになる。
  （順序も含めて最終的に同一とみなせるように証明している。）
-/
lemma image_toList_eq_map
  {α β : Type} [DecidableEq α] [DecidableEq β]
  {f : α → β} (hf : Function.Injective f)
  (S : Finset α)
  : (S.image f).toList = S.toList.map f := by

  -- 証明の方針：
  --  1) 「同じ要素を同じ回数だけ含む」こと（実際には injective なので回数は1回ずつ）。
  --  2) 両者がともに nodup であること。
  --  3) 長さが同じこと。
  -- 以上からリストが等しいと結論付ける。

  let LHS := (S.image f).toList
  let RHS := S.toList.map f

  --------------------------------------------------------------------------------
  -- Step 1. LHS と RHS の要素がちょうど一致すること (同じ "set of elements") を示す
  --------------------------------------------------------------------------------
  have same_mem : ∀ (y : β), y ∈ LHS ↔ y ∈ RHS := by
    intro y
    constructor
    · -- (→) LHS → RHS
      intro h
      -- LHS = (S.image f).toList なので
      -- 「y が LHS に属する」とは「y が S.image f に属する」のと同値
      -- （List.mem_toList と Finset.mem_image を行き来）
      have : y ∈ S.image f := by
        rw [Finset.mem_toList] at h
        exact h
      -- y ∈ S.image f とは ∃ x ∈ S, f x = y
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp this
      -- すると RHS = S.toList.map f 上で y = f x が出現するかをチェック
      -- x が S.toList に属するから、その map にも f x が含まれる
      apply List.mem_map_of_mem f
      rw [Finset.mem_toList]
      exact hxS

    · -- (←) RHS → LHS
      intro h
      -- y ∈ RHS とは y ∈ S.toList.map f
      -- すなわち ∃ x ∈ S.toList, f x = y
      rcases List.mem_map.mp h with ⟨x, hx_list, rfl⟩
      -- x ∈ S.toList とは x ∈ S
      rw [Finset.mem_toList] at hx_list
      -- 従って f x ∈ S.image f → (S.image f).toList にも属する
      rw [Finset.mem_toList]
      exact mem_image_of_mem f hx_list

  --------------------------------------------------------------------------------
  -- Step 2. 両リストがともに `nodup` であること
  --------------------------------------------------------------------------------
  have nodup_LHS : LHS.Nodup := (S.image f).nodup_toList
  have nodup_RHS : RHS.Nodup := by
    -- RHS = S.toList.map f
    -- S.toList は nodup、f は injective なので map f しても重複は生じない
    apply List.Nodup.map
    · exact hf
    · exact S.nodup_toList

  --------------------------------------------------------------------------------
  -- Step 3. 両リストの長さが同じこと
  --------------------------------------------------------------------------------
  have length_eq : LHS.length = RHS.length := by
    -- injective なら Finset.image f は |S| と同じ要素数になる
    -- よって LHS.length = card (S.image f) = card S = S.toList.length = RHS.length
    calc
      LHS.length
        = (S.image f).card       := by rw [Finset.length_toList]
      _ = S.card                 := by rw [card_image_of_injective _ hf]
      _ = S.toList.length        := (Finset.length_toList S).symm
      _ = RHS.length             := by rw [List.length_map]

  --------------------------------------------------------------------------------
  -- Step 4. 上記 1)〜3) から LHS = RHS と結論付け
  --   「要素集合が同じ & nodup & 長さ同じ」⇒ リストとして等しい
  --------------------------------------------------------------------------------

  exact List.Perm.eq_of_perm nodup_LHS nodup_RHS same_mem




--------------------------------------------------------------------------------
-- 実際に使いたい形 (S : Finset (Subtype p)) / f = Subtype.val の例
--------------------------------------------------------------------------------

lemma image_subtype_val_toList_eq_map
  {α : Type} [DecidableEq α]
  {p : α → Prop} [DecidablePred p]
  (S : Finset (Subtype p))
  : (S.image (fun t => t.val)).toList = S.toList.map (fun t => t.val) := by
  -- Subtype.val は injective
  apply image_toList_eq_map (hf := Subtype.val_injective) S

-/
