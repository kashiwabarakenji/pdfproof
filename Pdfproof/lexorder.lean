import LeanCopilot
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.OfFn
import Init.Data.List.Find
import Init.Data.List.Basic
--import Lean.Meta.Tactic.Simp

--orderの練習9の辞書式順序の問題が大変なのでファイルを分けた。

variable {P : Type} [LinearOrder P]

--Listをつけないとなぜかlength_consが見つからない。
theorem List.findIdx?_le_length' {α : Type} {xs : List α} {p : α → Bool}
    (h : List.findIdx? p xs = some i) : i < xs.length :=
by
  induction xs generalizing i with
  | nil => simp at h
  | cons a as h_ih =>
    simp [List.findIdx?] at h
    split at h
    · simp_all only [Option.some.injEq, length_cons]
      subst h
      simp_all only [Nat.zero_lt_succ]
    ·
      simp_all only [Bool.not_eq_true, Option.map_eq_some', length_cons]
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      subst right
      simp_all only [Option.some.injEq, forall_eq', Nat.add_lt_add_iff_right]

def smallestDiffWithProof
  {n : ℕ} {P : Type}
  [DecidableEq P]        -- P の等号可判定性
  (a b : Fin n → P)
  (nonempty : ∃ i : Fin n, a i ≠ b i)
  : { i : Fin n // (a i ≠ b i) ∧ ∀ j < i, a j = b j } :=
by
  let listfin := List.ofFn (λ i : Fin n => i)
  have listlen: listfin.length = n := by --これのせいで1日かかった。4.15にすることで解決。
    dsimp [listfin]
    exact (List.length_ofFn (λ i : Fin n => i))

  --candidatesを使わずにこっちを返り値としてつかったほうがいいかも。
  let idxo := List.findIdx? (λ i => a i ≠ b i) listfin
  have idxfsome: idxo.isSome := by
    have idxsome2: listfin.any (λ i => a i ≠ b i) := by
      obtain ⟨w, h⟩ := nonempty
      simp
      use w
      constructor
      dsimp [listfin]
      have : w = (List.ofFn fun i ↦ i)[w] := by
        simp
      --rw [this]
      --dsimp [List.ofFn]
      rw [List.mem_ofFn (fun i => i) w]
      dsimp [Set.range]
      use w

      rw [←ne_eq]
      exact h

    rw [List.findIdx?_isSome]
    exact idxsome2
  have idxf_eqn:∃ (idxs:Nat),some idxs = List.findIdx? (λ i => a i ≠ b i) listfin :=
  by
    match m:List.findIdx? (λ i => a i ≠ b i) listfin with
    | some idfxx =>
      -- idx が l の範囲内であることを証明
      use idfxx
    | none =>
      -- この場合は isSome が矛盾する
      --have : List.findIdx? (λ i => a i ≠ b i) listfin = none := m
      --仮定のmとidxo.isSomeが矛盾する。
      dsimp [idxo] at idxfsome
      exfalso
      rw [List.findIdx?_isSome] at idxfsome
      rw [List.any_eq_true] at idxfsome
      simp at idxfsome
      obtain ⟨x, hx_mem, hx⟩ := idxfsome
      let lf := List.findIdx?_of_eq_none m x
      dsimp [listfin] at lf
      simp at lf
      contradiction

  match m:List.findIdx? (λ i => a i ≠ b i) listfin with
  | none =>
    -- この場合は candidates が空であるため、矛盾
    have : ¬ List.findIdx? (λ i => a i ≠ b i) listfin = none := by
      by_contra hcontra
      obtain ⟨w, h⟩ := idxf_eqn
      rw [hcontra] at h
      contradiction
    contradiction

  | some idx =>
    have : idx < n := by
      rw [←listlen]
      apply List.findIdx?_le_length'
      exact m

    let idxff := Fin.mk idx this

    have hidx: a idxff ≠ b idxff := by
      let getE:= List.findIdx?_eq_some_iff_getElem.mp m
      obtain ⟨hj2, hj3⟩ := getE
      let hj31 := hj3.left
      dsimp [listfin] at hj31
      simp at hj31
      dsimp [idxff]
      exact hj31

    have hminimal: ∀ j < idxff, a j = b j := by
      obtain ⟨idxf, idxfsome⟩ := idxf_eqn
      have :idxf < n := by
        rw [←listlen]
        apply List.findIdx?_le_length'
        rw [idxfsome]

      let idxff := Fin.mk idxf this

      have before_eq: ∀ j < idxff, a j = b j := by
        intro j hj
        let getE:= List.findIdx?_eq_some_iff_getElem.mp idxfsome.symm
        obtain ⟨hj2, hj3⟩ := getE
        let hfj31 := hj3.left
        let hfj32 := hj3.right j hj
        dsimp [listfin] at hfj32
        simp at hfj32
        exact hfj32

      rename_i idxff_1
      intro j a_1
      simp_all only [ne_eq, List.length_ofFn, Option.isSome_some, decide_not, Option.some.injEq, listfin, idxo,
        idxff_1, idxff]

    exact ⟨idxff, hidx, hminimal⟩

-- 辞書式順序の `LE` 型クラスインスタンス
instance : LE (Fin n → P) where
  le x y :=
    (∃ i : Fin n, (x i < y i) ∧ ∀ j : Fin n, j < i → x j = y j) ∨ x = y

-- `LT` 型クラスも定義
instance : LT (Fin n → P) where
  lt x y :=
    (x ≤ y) ∧ ¬(y ≤ x)

-- `Preorder` のインスタンス定義
--PreorderとPartialOrderとLinearOrderの順番に定義する。
instance lexPreorder : Preorder (Fin n → P) where
  le := (· ≤ ·) -- `LE` 型クラスで定義した `le` を利用
  lt := (· < ·) -- `LT` 型クラスで定義した `lt` を利用

  -- 反射律の証明
  le_refl := by
    intro x
    right
    rfl

  -- 推移律の証明
  le_trans := by
    intro x y z hxy hyz
    cases hxy with
    | inl hxy1 =>
      cases hyz with
      | inl hyz1 =>
        let ⟨i, hi1, hi2⟩ := hxy1
        let ⟨j, hj1, hj2⟩ := hyz1
        -- i と j の大小関係を場合分け
        by_cases h : i ≤ j
        case pos =>
          left
          use i
          constructor
          by_cases h' : i = j
          case pos =>
            rw [h']
            subst h'
            simp_all only [Fin.le_refl]
            apply lt_of_le_of_lt
            · exact hi1.le
            · exact hj1
          case neg =>
            have i_lt_j : i < j := by
              omega
            simp_all only

          intro j_1 a
          simp_all only
          apply hj2
          omega
        case neg =>
          simp_all only [Fin.not_le, ge_iff_le]
          have j_lt_i : j < i := by
            simp_all only
          simp_all only [ge_iff_le]
          left
          use j
          constructor
          simp_all only

          intro j_1 a
          have j_lt_i : j_1 < i := by
            omega
          let rxy := hi2 j_1 j_lt_i
          let ryz := hj2 j_1 a
          rw [rxy]
          exact ryz

      | inr hyz2 =>
        rw [←hyz2]
        subst hyz2
        simp_all only
        obtain ⟨w, h⟩ := hxy1
        constructor
        use w

    | inr hxy2 =>
      rw [hxy2]
      exact hyz

  lt_iff_le_not_le := by
    intro x y
    apply Iff.intro
    intro h
    constructor
    · exact h.left
    · exact h.right
    intro h
    constructor
    · exact h.left
    · exact h.right

instance  lexPartialOrder : PartialOrder (Fin n → P) where
  le := (· ≤ ·) -- `LE` 型クラスで定義した `le` を利用
  lt := (· < ·)
  -- Preorder の反射律と推移律を再利用
  le_refl := lexPreorder.le_refl
  le_trans := lexPreorder.le_trans

  le_antisymm := by
    intro x y hxy hyx
    cases hxy with
    | inl hxy1 =>
      cases hyx with
      | inl hyx1 =>
        let ⟨i, hi1, hi2⟩ := hxy1
        let ⟨j, hj1, hj2⟩ := hyx1
        by_cases h : i ≤ j
        case pos =>
          by_cases h' : i = j
          case pos =>
            rw [h'] at hi1
            exfalso
            exact lt_asymm hi1 hj1
          case neg =>
            have i_lt_j : i < j := by
              omega
            have h'' : x i = y i := by
              exact (hj2 i i_lt_j).symm
            rw [h''] at hi1
            exfalso
            exact lt_irrefl (y i) hi1
        case neg =>
          have h' : j < i := by
            omega
          have h'' : x j = y j := by
            simp_all only [lt_self_iff_false]
          have h''' : x i = y i := by
            simp_all only [lt_self_iff_false]
          simp_all only [lt_self_iff_false]
      | inr hyx2 =>
        rw [←hyx2]

    | inr hxy2 =>
      rw [hxy2]

/-minとmaxの計算可能性に関するいろいろなまちがいたち。
もともとはlatticeのminとmaxが設定されているので、要素ごとにminとmaxがとられてしまう。
lattice構造から定義すると大変なので、minとmaxだけを定義すればよい。
instance lexLattice : Lattice (Fin n → P) where

Decidableにしようとすると、x >= yの判定の具体的なアルゴリズムを記述する必要があって、実現困難。
instance decidableLeFinFun [DecidableEq P] :
    DecidableRel ((· ≤ ·) : (Fin n → P) → (Fin n → P) → Prop) :=
  fun x y =>
    if h : (∃ i : Fin n, (x i < y i) ∧ ∀ j : Fin n, j < i → x j = y j) ∨ x = y
    then isTrue h
    else isFalse h

Classical.emでなくて、Classical.decを使う必要があった。
noncomputable def minFinFun (x y : Fin n → P) :  (Fin n → P) :=
  match Classical.em (x ≤ y) with
  | Or.inl _ => x
  | Or.inr _ => y

ifでなくてmatchを使う必要があった。
noncomputable def minFinFun (x y : Fin n → P) :  (Fin n → P) :=
  if Classical.dec (x ≤ y) then x else y
  -/
noncomputable def minFinFun (x y : Fin n → P) : Fin n → P :=
  match Classical.dec (x ≤ y) with
  | isTrue _  => x
  | isFalse _ => y

noncomputable def maxFinFun (x y : Fin n → P) : Fin n → P :=
  match Classical.dec (x ≤ y) with
  | isTrue _  => y
  | isFalse _ => x

noncomputable instance lexLinearOrder: LinearOrder (Fin n → P) where
  le := (· ≤ ·) -- `LE` 型クラスで定義した `le` を利用
  lt := (· < ·)
  -- Preorder の反射律と推移律を再利用
  le_refl := lexPreorder.le_refl
  le_trans := lexPreorder.le_trans
  le_antisymm := lexPartialOrder.le_antisymm

  le_total := by
    intro a b
    by_cases h : a = b
    case pos =>
      right
      subst h
      simp_all only [lt_self_iff_false, implies_true, and_true, exists_false, or_true]
      simp_all only [le_refl]
    case neg =>
      have : ∃ i : Fin n, ¬ (a i = b i) :=
      by
        have nf: ¬ (∀ i : Fin n, a i = b i) ↔  ∃ i : Fin n, ¬ (a i = b i) := by
          apply Iff.intro
          · intro h
            by_contra hcontra
            apply h
            intro i
            by_contra hcontra2
            simp_all only [not_forall]
          · intro a_1
            simp_all only [not_forall]
        apply nf.mp
        by_contra hcontra
        have :a=b := by
          apply funext
          intro i
          exact hcontra i
        subst this
        simp_all only [not_true_eq_false]
      let ⟨i_min,hi⟩ := smallestDiffWithProof a b this
      simp_all only [or_false]
      have : (b i_min < a i_min) ∨ (a i_min < b i_min) := by
        simp_all only [gt_iff_lt, lt_or_lt_iff_ne, ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        simp [a_1] at hi
      cases this with
      | inl hlt =>
        right
        left
        use i_min
        constructor
        · exact hlt
        · intros j hjw
          exact (hi.2 j hjw).symm
      | inr hlt =>
        left
        simp_all only [ne_eq]
        obtain ⟨w, h_1⟩ := this
        obtain ⟨left, right⟩ := hi
        dsimp [LE.le]
        left
        use i_min

  lt_iff_le_not_le := by
    intro x y
    apply Iff.intro
    intro h
    constructor
    · exact h.left
    · exact h.right
    intro h
    constructor
    · exact h.left
    · exact h.right

  min x y := minFinFun x y

  min_def := by
    intro x y
    by_cases h : x ≤ y
    case pos =>
      simp_all only [↓reduceIte]
      simp [minFinFun, h]
      split
      next x_1 h_1 heq => simp_all only
      next x_1 h_1 heq => simp_all only
    case neg =>
      simp_all only [↓reduceIte]
      simp [minFinFun, h]
      split
      next x_1 h_1 heq => simp_all only [not_true_eq_false]
      next x_1 h_1 heq => simp_all only [not_false_eq_true]

  max x y := maxFinFun x y

  max_def := by
    intro x y
    by_cases h : x ≤ y
    case pos =>
      simp_all only [↓reduceIte]
      simp [maxFinFun, h]
      split
      next x_1 h_1 heq => simp_all only
      next x_1 h_1 heq => simp_all only
    case neg =>
      simp_all only [↓reduceIte]
      simp [maxFinFun, h]
      split
      next x_1 h_1 heq => simp_all only [not_true_eq_false]
      next x_1 h_1 heq => simp_all only [not_false_eq_true]

  decidableLE := by
    intro x y
    simp_all only
    by_cases h : x ≤ y
    · simp_all only
      infer_instance
    · simp_all only
      infer_instance

  decidableLT := by
    intro x y
    simp_all only
    by_cases h : x < y
    · simp_all only
      infer_instance
    · simp_all only
      infer_instance
