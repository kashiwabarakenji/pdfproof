--closure systemからclosure operatorを導入するために、extensiveとmonotoneとidempotentを証明したもの。
--別のファイルでは、intersectionをListに変換した後にfoldrを使って定義して、言明を帰納法で証明したが、
--ここでは、intersectionをFinsetのままで定義して(finsetIntersection M)、主に帰納法を使わずに証明した。こちらのほうが証明として良いと思われる。
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

structure ClosureSystem (α : Type) [DecidableEq α]  [Fintype α] extends SetFamily α where
  (intersection_closed : ∀ s t , sets s → sets t → sets (s ∩ t))
  (has_ground : sets ground)
  (has_empty: sets ∅)

--よく考えたら定義に集合族は必要なく、　台集合さえわかればいい。
structure SetFamily.preclosure_operator (ground:Finset α) where
  (cl : Finset ground → Finset ground)
  (extensive : ∀ s : Finset ground, s ⊆ cl s)
  (monotone : ∀ s t : Finset ground, s ⊆ t → cl s ⊆ cl t)

structure SetFamily.closure_operator (ground:Finset α) extends SetFamily.preclosure_operator ground where
  (idempotent : ∀ s : Finset ground, cl s = cl (cl s))

def finsetIntersection {α : Type} [DecidableEq α]
  (family : Finset (Finset α)) : Finset α :=
  (family.sup id).filter (fun x => ∀ f ∈ family, x ∈ f)

def closureOperator {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets] (s : Finset F.ground) : Finset F.ground :=
  let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
  let ios := finsetIntersection (F.ground.powerset.filter (fun (t : Finset α) => F.sets t ∧ sval ⊆ t))
  ios.subtype (λ x => x ∈ F.ground)

--closure systemでないと全体集合が含まれないので、ただの集合族では証明できない。
lemma extensive_from_SF_finset {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α)[DecidablePred F.sets]:
  ∀ s : Finset F.ground, s ⊆ closureOperator F s :=
by
  dsimp [closureOperator]
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

  · obtain ⟨val, property⟩ := x
    simp_all only
    use F.ground
    simp_all only [subset_refl, and_true]--
    apply And.intro
    · simp_all only
    · apply And.intro
      · exact F.has_ground
      · simp [Finset.image_subset_iff]

  · intro f a a_1 a_2
    obtain ⟨val, property⟩ := x
    simp_all only
    apply a_2
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]--

lemma monotone_from_SF_finset {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α)[DecidablePred F.sets]:
  ∀ s t : Finset F.ground, s ⊆ t → closureOperator F s ⊆ closureOperator F t :=
by
  dsimp [closureOperator]
  intro s t h
  dsimp [finsetIntersection]
  simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp]
  rw [Finset.map_eq_image]
  simp
  intro x hx
  rw [@Finset.mem_subtype]
  rw [Finset.mem_filter]
  simp
  constructor
  · use F.ground
    simp_all only [subset_refl]
    apply And.intro
    · constructor
      · simp_all only
      · constructor
        · exact F.has_ground
        · simp_all only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_sup]--
          obtain ⟨val, property⟩ := x
          --obtain ⟨left, right⟩ := hx
          --obtain ⟨w, h_1⟩ := left
          --simp_all only
          intro x hx
          simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right,exists_eq_right]--
          obtain ⟨w_1, h_1⟩ := hx
          simp_all only [subset_refl]

    · simp_all only [Finset.coe_mem]

  · intro f a a_1 a_2
    obtain ⟨val, property⟩ := x
    simp_all only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_sup, Finset.mem_powerset, id_eq]--
    obtain ⟨left, right⟩ := hx
    obtain ⟨w, h_1⟩ := left
    obtain ⟨left, right_1⟩ := h_1
    simp_all only [subset_refl]
    apply right
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · intro x hx
      simp_all only [subset_refl, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      obtain ⟨w_1, h_1⟩ := hx
      apply a_2
      simp_all only [subset_refl, Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right,
        exists_eq_right, exists_true_left]
      exact h h_1

lemma finite_intersection_in_closureSystem
  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α)
  (M : Finset (Finset α))
  (M_nonempty : M.Nonempty)
  (all_inF : ∀ T ∈ M, F.sets T)
  : F.sets (finsetIntersection M) := by
  classical

  -- **ここで `Finset.induction_on` を使う**
  induction M using Finset.induction_on --(p := λ (s : Finset (Finset α))=> F.sets (finsetIntersection s))
    -- 1) base case: s = ∅
  case empty =>
    -- finsetIntersection ∅ = F.ground なので F.sets (finsetIntersection ∅)
    dsimp [finsetIntersection]
    simp
    exact F.has_empty

    -- 2) induction step: s = insert T₀ M' と仮定
  case insert T₀ M' T₀_not_in_M' ih =>
    cases M'.eq_empty_or_nonempty with
    | inl hM'_empty =>
      -- M' = ∅ の場合 => M = {T₀}
      -- finsetIntersection {T₀} = T₀
      have : finsetIntersection {T₀} = T₀ := by
        apply Finset.ext
        intro x
        simp only [finsetIntersection, Finset.mem_filter, Finset.sup_singleton,
          Finset.mem_singleton, id_eq]
        -- 「x ∈ T₀ ∧ ∀ f ∈ {T₀}, x ∈ f」は x ∈ T₀ と同値
        subst hM'_empty
        simp_all only [Finset.notMem_empty, not_false_eq_true, forall_eq, and_self]
      subst hM'_empty
      simp_all only [LawfulSingleton.insert_empty_eq,Finset.mem_singleton]--

    | inr hM'_nonempty =>
      -- M' が非空 => 帰納仮定 ih : F.sets (finsetIntersection M')
      -- T₀ も F.sets (all_inF が保証) => 交わりに閉じている => T₀ ∩ finsetIntersection M' ∈ F.sets
      have T₀_inF    := all_inF T₀ (Finset.mem_insert_self T₀ M')
      have M'_inFset := ih  -- これが帰納仮定 (insert の引数 ih)
      -- finsetIntersection (insert T₀ M') = T₀ ∩ finsetIntersection M'
      have key : finsetIntersection (insert T₀ M')
              = T₀ ∩ (finsetIntersection M') := by
        apply Finset.ext
        intro x --xは全体の共通部分から取ってくる。
        simp only [finsetIntersection, Finset.mem_filter,
                    Finset.mem_insert, Finset.mem_inter,
                    Finset.mem_sup, id_eq]
        constructor
        · -- → 方向
          intro h
          -- h : x ∈ (insert T₀ M').sup id ∧ (∀ A ∈ insert T₀ M', x ∈ A)
          --     すなわち (x ∈ T₀ ∪ M'.sup id) ∧ ...
          constructor -- x ∈ T₀ ∩ finsetIntersection M'
          · --x ∈ T₀を示す。
            simp_all only [Finset.mem_insert, or_true, implies_true, Finset.insert_nonempty,
              forall_eq_or_imp, true_and, forall_const, exists_eq_or_imp]
          · --(∃ i ∈ M', x ∈ i) ∧ ∀ f ∈ M', x ∈ f
            obtain ⟨left, right⟩ := h
            obtain ⟨w, h⟩ := left
            by_cases h1 : w ∈ M'
            case pos =>
              simp_all only [Finset.mem_insert, or_true, implies_true, Finset.insert_nonempty,
                forall_eq_or_imp, true_and, forall_const, and_self, and_true]
              obtain ⟨left, right⟩ := right
              apply Exists.intro
              · apply And.intro
                · exact h1
                · simp_all only
            case neg =>
              have : w = T₀ := by
                simp_all only [Finset.mem_insert, or_true, implies_true, Finset.insert_nonempty,
                  forall_eq_or_imp, true_and, forall_const, or_false, not_false_eq_true]
              subst this
              simp_all only [Finset.mem_insert, or_true, implies_true, forall_const,
                not_false_eq_true, Finset.insert_nonempty, forall_eq_or_imp, true_and, or_false,
                and_true]
              have : Nonempty M' := by
                simp_all only [nonempty_subtype]
                exact hM'_nonempty
              let ww := Classical.choice this
              obtain ⟨val, property⟩ := ww
              simp_all only [nonempty_subtype]
              obtain ⟨w_1, h_1⟩ := this
              apply Exists.intro
              · apply And.intro
                · apply property
                · simp_all only

        · intro a
          simp_all only [implies_true,forall_eq_or_imp,  exists_eq_or_imp, or_self, and_self]--
      convert F.intersection_closed T₀ (finsetIntersection M') T₀_inF (M'_inFset hM'_nonempty (fun T hT => all_inF T (Finset.mem_insert_of_mem hT)))

lemma closureOperator_image_in_sets
  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets]
  (s : Finset F.ground) :
  F.sets ((closureOperator F s).image Subtype.val) := by

  -- 1. 記号整理
  let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
  let M := F.ground.powerset.filter (fun t => F.sets t ∧ sval ⊆ t)
  let I := finsetIntersection M  -- "intersection of all t in M"

  -- 2. M が空でないことを示す
  --    理由: ground ∈ M （F.has_ground と sval ⊆ F.ground より）
  have M_nonempty : M.Nonempty := by
    have : F.sets F.ground := F.has_ground
    have : sval ⊆ F.ground := by
      intro x hx
      simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,sval]
      obtain ⟨w, h⟩ := hx
      simp_all only
    simp_all only [sval, M]
    rw [Finset.nonempty_iff_ne_empty]
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    rw [Finset.eq_empty_iff_forall_notMem] at a
    simp_all only [Finset.mem_filter, Finset.mem_powerset, not_and, subset_refl]

  -- 3. 補題 finite_intersection_in_closureSystem を使って
  --    I = finsetIntersection M が F.sets であることを示す
  have I_inF : F.sets I := by
    apply finite_intersection_in_closureSystem F M
    · exact M_nonempty
    · -- M の要素は (F.sets t ∧ sval ⊆ t) を満たすから、F.sets t
      intro T hT
      exact (Finset.mem_filter.mp hT).2.left

  -- 4. closureOperator F s の map (Subtype.val) がちょうど I に一致する
  have : I = (closureOperator F s).map ⟨Subtype.val, Subtype.val_injective⟩ := by
    -- unfold して確認
    unfold closureOperator
    simp_all only [M, sval, I]
    ext a : 1
    simp_all only [Finset.mem_map, Finset.mem_subtype, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_left,exists_prop, exists_eq_right_right, iff_self_and]--
    intro a_1
    rw [finsetIntersection] at a_1
    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_sup, id_eq, subset_refl]
    obtain ⟨left, right⟩ := a_1
    obtain ⟨w, h⟩ := left
    obtain ⟨left, right_1⟩ := h
    obtain ⟨left, right_2⟩ := left
    --obtain ⟨left_1, right_2⟩ := right_2
    simp_all only [subset_refl]
    apply left
    simp_all only

  -- 5. よって、結論として F.sets ((closureOperator F s).map ... )
  --    は F.sets I と同じなので成立
  simp_all only [M, sval, I]
  convert I_inF
  ext x a : 2
  simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Finset.mem_map,
    Function.Embedding.coeFn_mk]

lemma mem_finsetIntersection_iff_of_nonempty
  {α : Type} [DecidableEq α]
  {family : Finset (Finset α)} {x : α}
  (hne : family.Nonempty)
  :
  x ∈ finsetIntersection family
  ↔ ∀ f ∈ family, x ∈ f
:= by
  -- unfold して「x ∈ (family.sup id).filter (...)」を展開
  simp only [finsetIntersection, Finset.mem_filter]
  -- x ∈ filter A p ↔ (x ∈ A ∧ p x)
  -- ∴ ここでは「(x ∈ family.sup id) ∧ (∀ f ∈ family, x ∈ f)」
  --
  -- これを「(∀ f ∈ family, x ∈ f)」だけに簡単化するには、
  --   「x が family のすべての要素に入る → x はそのうちの1つ f0 にも入る → よって x ∈ union」
  -- という一方向の補足が必要
  refine Iff.intro
    (fun h => h.2)   -- (←) すでに h.2 が「∀ f ∈ family, x ∈ f」
    (fun hx =>
      -- (→) x が「すべての f ∈ family」に入るならば
      -- union (sup id family) にも入る，かつもちろん (∀f, x∈f)
      have x_in_union : x ∈ family.sup id := by
        -- union に入るためには「ある1つの集合 f ∈ family に x ∈ f」があれば十分
        simp_all only [Finset.mem_sup, id_eq]
        contrapose! hne
        simp_all only [imp_false, IsEmpty.forall_iff, implies_true, Finset.not_nonempty_iff_eq_empty]
        ext a : 1
        simp_all only [Finset.notMem_empty]
      -- 以上で (x ∈ sup id ∧ ∀ f∈family, x∈f) が示せる
      ⟨x_in_union, hx⟩
    )

lemma idempotent_from_SF_finset_lem
  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets]
  : ∀ s : Finset F.ground, F.sets (s.image Subtype.val) → closureOperator F s = s :=
by
  intro s hFsets
  -- 記号整理：
  -- s : Finset F.ground であり、s.map val は α の Finset
  let sval := s.image (Subtype.val : F.ground → α)

  ------------------------------------------------------------------------------
  -- 1. s.map val ∈ M であること (closureOperator の定義で用いた M)
  ------------------------------------------------------------------------------
  --    M := { t | t ⊆ F.ground, F.sets t ∧ s.val ⊆ t }
  -- ここで s 自体が F.sets をみたす (仮定) かつ s.val ⊆ s.val は自明
  -- よって s.map val は M の一員
  --dsimp only [closureOperator]
  let M := F.ground.powerset.filter (fun t => F.sets t ∧ sval ⊆ t)
  have s_in_M : sval ∈ M := by
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, and_true, M, sval]
    intro t ht
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    obtain ⟨w, h⟩ := ht
    simp_all only
    --simp only [Finset.mem_filter, Finset.mem_powerset]

  ------------------------------------------------------------------------------
  -- 2. finsetIntersection M は M のすべての要素に共通する要素の集まり
  --    特に s.map val も M の要素のひとつなので、
  --    交わりは s.map val の部分集合である。
  ------------------------------------------------------------------------------
  -- また他方で、M の各要素 t は s.map val を含むので、交わりは「s.map val に含まれる全要素」でもある
  -- つまり交わりは s.map val と等しくなる。
  let I := finsetIntersection M
  have I_subset_s : I ⊆ sval := by
    -- I は M の要素 t すべてに含まれる要素の集合
    -- かつ s_in_M : sval ∈ M
    -- よって I は sval にも含まれる
    intro x hx
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, and_true, Finset.mem_image,
      Subtype.exists, exists_and_right, exists_eq_right, M, sval, I]
    have : x ∈ F.ground:= by
      simp only [finsetIntersection] at hx
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_sup, id_eq, subset_refl]
      obtain ⟨left, right⟩ := hx
      obtain ⟨w, h⟩ := left
      obtain ⟨left, right_1⟩ := h
      obtain ⟨left, right_2⟩ := left
      obtain ⟨left_1, right_2⟩ := right_2
      simp_all only [subset_refl]
      apply s_in_M
      simp_all only [subset_refl]
    --use this
    simp_all only [exists_true_left]
    have : F.ground ∈ Finset.filter (fun t => F.sets t ∧ Finset.image Subtype.val s ⊆ t) F.ground.powerset := by
      simp [Finset.mem_filter, Finset.mem_powerset, F.has_ground]
      simp_all only
    have M_nonempty : M.Nonempty := by
      use F.ground
    let mf := (mem_finsetIntersection_iff_of_nonempty M_nonempty).mp hx
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_true, true_and]
    have : sval ∈ M :=
    by
      simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, M, sval]
    let ms := mf sval this
    simp [sval] at ms
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, exists_true_left, M, sval]

  have s_subset_I : sval ⊆ I := by
    -- s.map val は M の各 t に含まれる (by 定義: sval ⊆ t)
    -- よって sval の要素 x は M に属するすべての t でも x ∈ t
    -- ゆえに x ∈ 交わり
    intro x hx
    --simp only [finsetIntersection, Finset.mem_filter]
    -- 「x は M のすべての t に含まれ、かつ x ∈ sup id M」 を示す
    dsimp [I]
    dsimp [finsetIntersection]
    rw [Finset.mem_filter]
    constructor
    · -- x ∈ (M.sup id)
      -- これは「何らかの t ∈ M に x ∈ t」がいえればOK
      -- 実際には t = sval がそう
      apply Finset.mem_sup.mpr
      refine ⟨sval, s_in_M, ?_⟩
      simp only [id_eq]
      exact hx
    · -- x はすべての t ∈ M で t に属する
      intro t ht
      simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, and_true, Finset.mem_image,
        Subtype.exists, exists_and_right, exists_eq_right, M, sval, I]
      obtain ⟨w, h⟩ := hx
      obtain ⟨left, right⟩ := ht
      obtain ⟨left_1, right⟩ := right
      apply right
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]

  -- 以上 2つの包含より I = s.map val
  have : I = sval := by
    apply Finset.Subset.antisymm
    · exact I_subset_s
    · exact s_subset_I

  ------------------------------------------------------------------------------
  -- 3. closureOperator F s は I を Finset F.ground に戻したもの
  ------------------------------------------------------------------------------
  -- ところが s も「I を F.ground に戻した」ものと同一視できる。
  -- 実際、s は (s.map val).subtype(...) と等しくなる（要素レベルで同じ）。
  --dsimp only [closureOperator]
  -- closureOperator F s は  I.subtype (λ x => x ∈ F.ground)
  -- 今、I = s.map val
  -- かつ s はちょうど (s.map val).subtype(...) に等しい
  apply Finset.ext
  intro x
  constructor
  · -- (→) x ∈ closureOperator F s ⇒ x ∈ s
    intro hx
    simp only at hx
    -- x.val ∈ I かつ I = s.map val
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, and_true, M, sval, I]
    obtain ⟨val, property⟩ := x
    dsimp only [closureOperator] at hx
    rw [Finset.map_eq_image] at hx
    simp at hx
    have :val ∈ finsetIntersection (Finset.filter (fun t ↦ F.sets t ∧ sval ⊆ t) F.ground.powerset):=
    by
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left,
        exists_const, sval]
    have :val ∈ finsetIntersection M:=
    by
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left,
        exists_const, sval, M]
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, exists_const,
      sval, M]

  · -- (←) x ∈ s ⇒ x ∈ closureOperator F s
    intro hx
    let ef := extensive_from_SF_finset F s
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, and_true, M, sval, I]
    obtain ⟨val, property⟩ := x
    exact ef hx

lemma idempotent_from_SF_finset {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α)[DecidablePred F.sets]:
  ∀ s : Finset F.ground, closureOperator F s = closureOperator F (closureOperator F s) :=
by

  intro s
  -- 記号整理: T := closureOperator F s
  let T := closureOperator F s

  -- (1) T.map val は F.sets に属する (closureOperator_image_in_sets の適用)
  have T_inF : F.sets (T.image Subtype.val) :=
    closureOperator_image_in_sets F s

  -- (2) T はすでに「F.sets (T.map val) をみたす Finset F.ground」なので、
  --     idempotent_from_SF_finset_lem を使えば closureOperator F T = T
  have : closureOperator F T = T := by
    apply idempotent_from_SF_finset_lem F
    exact T_inF  -- T は F.sets に入っている

  -- (3) 結論:
  --     closureOperator F s = T
  --     ⇒ closureOperator F (closureOperator F s) = closureOperator F T = T
  --     ∴ closureOperator F s = closureOperator F (closureOperator F s)
  calc
    closureOperator F s
      = T                  := rfl
   _  = closureOperator F T := by rw [this]

noncomputable def preclosure_operator_from_SF {α :Type} [DecidableEq α][Fintype α] (F: ClosureSystem α) [DecidablePred F.sets]: SetFamily.preclosure_operator F.ground :=
{
  cl := closureOperator F,
  extensive := extensive_from_SF_finset F,
  monotone := monotone_from_SF_finset F
}

noncomputable def closure_operator_from_SF {α :Type} [DecidableEq α][Fintype α] (F: ClosureSystem α) [DecidablePred F.sets]: SetFamily.closure_operator F.ground :=
{
  cl := closureOperator F,
  extensive := extensive_from_SF_finset F,
  monotone := monotone_from_SF_finset F,
  idempotent := idempotent_from_SF_finset F
}

-------------------------------
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
