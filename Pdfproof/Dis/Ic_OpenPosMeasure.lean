import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Basic
--import Mathlib.Order.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.SetNotation
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Sqrt
--import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Order.Group.Lattice
import LeanCopilot

open Classical
open MeasureTheory Real Set Metric Function Filter TopologicalSpace ENNReal

--このファイルは、dis_func_metricの証明を補助するもの。01連続関数がL2ノルムで距離空間になることの証明で、
--01閉区間がOpenPosMeasureを持つことを証明する。そのために、Ic上の測度を定義し、その測度がOpenPosMeasureを持つことを証明する。
--基本的な定義とinstanceの設定

def Ic := Set.Icc (0:Real) 1
def Ic_c := Icᶜ

--Ic上のMeasureSpaceの定義。これがないと01上の積分がうまく定義できない。
noncomputable instance : MeasureTheory.MeasureSpace Ic := --(Set.Icc (0 : ℝ) 1) :=
  MeasureTheory.Measure.Subtype.measureSpace
noncomputable instance : MeasurableSpace Ic := by infer_instance

noncomputable instance : MeasureTheory.MeasureSpace Ic_c :=
  MeasureTheory.Measure.Subtype.measureSpace
noncomputable instance : MeasurableSpace Ic_c := by infer_instance
/-
アイデア:
1. U が Ic の部分空間位相で開であり非空とする。
2. U = V ∩ Ic を満たす開集合 V (ℝ の位相で開) が存在する。
3. U が非空なので x ∈ U を取れる。
4. V が ℝ 上で開なので、x を中心とする小区間 (x - ε, x + ε) ⊆ V を取れる。
5. その区間をさらに Ic と交わすと (x - ε, x + ε) ∩ Ic ⊆ U となり、
   これが非縮退区間なら Lebesgue 測度は正となる。
6. 測度の単調性から U の測度も正となる。
-/
lemma openSubspace_nonempty_measure_pos
    (U : Set Ic) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (volume:Measure Ic) U :=
by
  let ⟨x, hxU⟩ := hne
  -- U = V ∩ Ic となる V を得る
  let ⟨V, hVU⟩ := isOpen_induced_iff.mp hU      -- isOpen_subtype': U が部分空間位相で開なら U= V ∩ univSet (ここでは Ic).
  have xInV : x.1 ∈ V := by
    -- x : Ic なので x.1 は ℝ 上で 0 ≤ x.1 ≤ 1
    -- x ∈ U = V ∩ Ic なので x.1 ∈ V
    obtain ⟨val, property⟩ := x
    obtain ⟨left, right⟩ := hVU
    subst right
    simp_all only [mem_preimage]
  -- V は ℝ 上で開なので、x.1 の付近に小区間がとれる
  obtain ⟨ε, εpos, hball⟩ := Metric.isOpen_iff.1 (hVU.left) x.1 xInV

  -- その区間を Ic と交わして得た集合が U に含まれることを示す
  -- x は Ic の点だが、x.1 は [0,1] に入る実数
  let I := (ball x.1 ε) ∩ (Icc 0 1)
  have I_subset_U : I ⊆ U := by
    intro y hy
    have : y ∈ V ∩ Ic :=
    by
      simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, mem_Icc, I]
      obtain ⟨val, property⟩ := x
      obtain ⟨left, right⟩ := hVU
      obtain ⟨left_1, right_1⟩ := hy
      obtain ⟨left_2, right_1⟩ := right_1
      subst right
      simp_all only [mem_preimage]
      apply And.intro
      · apply hball
        simp_all only [mem_ball]
      · constructor
        · simp_all only
        · simp_all only
    simp_all [I]
    obtain ⟨left, right⟩ := hVU
    subst right
    simp_all only [mem_preimage]
  -- I が非空かどうかをチェック
  -- x.1 ∈ ball x.1 ε かつ x.1 ∈ Icc 0 1 は明らか (ただし ε > 0 なので問題なし)
  have xInI : x.1 ∈ I := ⟨mem_ball_self εpos, x.2⟩
  -- ball x.1 ε は (x.1 - ε, x.1 + ε) のような開区間なので、I も区間の切り出しになり正 measure を持つ
  -- measure を restricted measure (Ic 上の測度) で評価したいので、単調性を使う
  have : 0 < (Measure.restrict volume Ic) I:= by
    suffices volume.restrict Ic I = volume I by
      rw [this]
      let a := max (x.1 - ε) 0
      let b := min (x.1 + ε) 1
      have a_lt_b : a < b := by
        have : x - ε < x + ε := by linarith
        simp
        dsimp [a]
        dsimp [b]
        rw [@lt_min_iff]
        rw [@max_lt_iff]
        rw [@max_lt_iff]
        dsimp [I] at xInI
        simp at xInI
        have hx0: x.1 ≥ 0 :=
        by
          exact unitInterval.nonneg x
        have hx1: x.1 ≤ 1 :=
        by
          exact unitInterval.le_one x
        constructor
        constructor
        exact this
        exact add_pos_of_nonneg_of_pos hx0 εpos
        constructor
        simp_all only [gt_iff_lt, ge_iff_le, I]
        linarith
        simp_all only [gt_iff_lt, ge_iff_le, zero_lt_one, I]
      have Ioo_ab_subset : Ioo a b ⊆ I := by
        intro y hy
        obtain ⟨y_ge_a, y_le_b⟩ := hy
        dsimp [I]
        simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
          sup_lt_iff, zero_lt_one, and_true, mem_Icc, a, b, I]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := hVU
        obtain ⟨left_1, right_1⟩ := a_lt_b  --この辺りをコメントアウトすると、linarithが失敗する。
        obtain ⟨left_2, right_2⟩ := y_ge_a
        obtain ⟨left_3, right_3⟩ := y_le_b
        obtain ⟨left_1, right_4⟩ := left_1
        subst right
        simp_all only [mem_preimage, Subtype.image_preimage_coe, subset_inter_iff]
        obtain ⟨left_4, right⟩ := I_subset_U
        apply And.intro
        · rw [dist_eq_norm]
          simp_all only [norm_eq_abs]
          rw [abs]
          simp_all only [neg_sub, sup_lt_iff]
          apply And.intro
          · linarith
          · linarith
        · apply And.intro
          · positivity
          · exact right_3.le

      show 0 < volume I
      let a' := (3*a+b)/4
      let b' := (a+3*b)/4
      let I':= Icc a' b'
      have a'_lt_b': a' < b':=
      by
        dsimp [a',b']
        ring_nf
        linarith
      have sub' :I' ⊂ Ioo a b:=
      by
        dsimp [I',Ioo,Icc,a',b']
        rw [@ssubset_def]
        constructor
        · intro x hx
          simp at hx
          simp
          constructor
          · have a_le_x: a≤x:=by
              linarith
            have a_ne_x: a≠ x:= by
              by_contra h_contra
              rw [h_contra] at hx
              linarith
            exact lt_of_le_of_ne a_le_x a_ne_x
          · have x_le_b :x ≤ b :=by
              linarith
            have x_ne_b :x ≠ b := by
              by_contra h_contra
              rw [h_contra] at hx
              linarith
            exact lt_of_le_of_ne x_le_b x_ne_b
        · by_contra h_contra
          let y := a/8+(b*7/8)
          have y_in_Ioo : y ∈ {x | a < x ∧ x < b} := by
            constructor
            · -- a < y を示す
              calc
                a = a * 8 / 8 := by ring
                _ < (a + b*7) / 8 := by linarith
                _ = y := by exact add_div a (b * 7) 8
            · -- y < b を示す
              calc
                y = (a / 8 + b * 7 / 8) := by rfl
                _ < (b * 8 / 8) := by linarith
                _ = b := by ring
          have y_not_in_Icc : y ∉ {x | (3 * a + b) / 4 ≤ x ∧ x ≤ (a + 3 * b) / 4} := by
            by_contra h_contra'
            simp at h_contra'
            have : y > (a + 3 * b) / 4:= by
              dsimp [y]
              linarith
            let h_c := h_contra'.2
            rw [←ge_iff_le] at h_c
            exact lt_irrefl y (lt_of_le_of_lt h_c this)
          simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self,
            lt_inf_iff, sup_lt_iff, zero_lt_one, and_true, subset_inter_iff, setOf_subset_setOf,
            and_imp, mem_setOf_eq, not_true_eq_false, a, b, y, I, b', a']

      have Icc_ab_subset : I' ⊆ I := by
        intro y hy
        have : y ∈ Ioo a b := by
          exact sub'.1 hy
        exact Ioo_ab_subset this

      show 0 < volume I
      have I_le_I:volume I' ≤ volume I  := by
        exact OuterMeasureClass.measure_mono volume Icc_ab_subset

      have measure_Icc_ab : 0 < volume I' := by
    -- volume(Icc a b) = Real.volume (Icc a b) = ennreal.ofReal (b - a) (b>a)
    --  b > a ⇒ b - a > 0 ⇒ ennreal.ofReal (b-a) > 0
        rw [Real.volume_Icc]
        simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
          sup_lt_iff, zero_lt_one, and_true, subset_inter_iff, ofReal_pos, sub_pos, a', b', a, b, I, I']
      -- 以上より Icc a b ⊆ I up to measure 0 ⇒ measure(I) ≥ measure(Icc a b)
      -- 従って measure(I) > 0
      exact lt_of_le_of_lt' I_le_I measure_Icc_ab

    apply MeasureTheory.Measure.restrict_eq_self volume
    simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, I]
    obtain ⟨val, property⟩ := x
    obtain ⟨left, right⟩ := hVU
    subst right
    simp_all only [mem_preimage, Subtype.image_preimage_coe, subset_inter_iff]

  calc
     (0 : ℝ≥0∞) < (Measure.restrict volume Ic) I:= by exact this
     _ ≤ (Measure.restrict volume Ic) U:= measure_mono I_subset_U
     _ ≤  volume U := by
      show (volume.restrict Ic) (Subtype.val '' U) ≤ volume U
      have h_sub : Subtype.val '' U ⊆ Ic :=
      by rintro x ⟨y, hy, rfl⟩; exact y.2
      rw [Measure.restrict_eq_self volume h_sub]
      show  volume (Subtype.val '' U) ≤ volume U
      have measU:MeasurableSet U :=
      by
        simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, image_subset_iff,
          Subtype.coe_preimage_self, subset_univ, I]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := hVU
        subst right
        simp_all only [mem_preimage, Subtype.image_preimage_coe, subset_inter_iff]
        obtain ⟨left_1, right⟩ := I_subset_U
        exact hU.measurableSet
      have measSU:MeasurableSet (Subtype.val '' U) :=
      by
        apply MeasurableSet.subtype_image
        · dsimp [Ic]
          exact measurableSet_Icc
        · exact measU
      have :volume (Subtype.val '' U) = volume U :=
      by
        let cs := comap_subtype_coe_apply measurableSet_Icc volume U
        simp at cs
        suffices  (Measure.comap Subtype.val volume) U = volume U from
        by
          exact id (Eq.symm cs)
        simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, I]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := hVU
        subst right
        simp_all only [mem_preimage, Subtype.image_preimage_coe, subset_inter_iff]
        obtain ⟨left_1, right⟩ := I_subset_U
        rfl
      simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, le_refl, I]

-- 以上の補題を使って IsOpenPosMeasure を与える
noncomputable instance : MeasureTheory.Measure.IsOpenPosMeasure (volume:Measure Ic) where
  open_pos := fun U hU hne =>
  by
    let os := openSubspace_nonempty_measure_pos U hU hne
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp [a] at os

noncomputable instance : MeasureSpace ℝ := Real.measureSpace  --これはもともと設定されているかも。
--Ic上のMeasureSpaceの定義。これがないと01上の積分がうまく定義できない。
noncomputable instance : MeasureTheory.MeasureSpace Ic := --(Set.Icc (0 : ℝ) 1) :=
  MeasureTheory.Measure.Subtype.measureSpace
noncomputable instance : MeasurableSpace Ic := by infer_instance
--noncomputable instance : MeasureSpace Ic where
--  volume := @MeasureTheory.Measure.restrict ℝ _ (MeasureTheory.MeasureSpace.volume : Measure ℝ) (Set.univ : Set Ic)
--noncomputable instance : MeasureSpace Ic where
--  volume := MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.univ:Set Ic)

noncomputable instance : CompactSpace Ic :=
by
  dsimp [Ic]
  infer_instance

noncomputable instance: CompactIccSpace Ic :=
by
  apply CompactIccSpace.mk
  refine fun {a b} ↦ ?_
  refine Subtype.isCompact_iff.mpr ?_
  dsimp [Ic]
  simp_all only [image_subtype_val_Icc]
  obtain ⟨val, property⟩ := a
  obtain ⟨val_1, property_1⟩ := b
  simp_all only
  exact isCompact_Icc

def hIc:IsCompact Ic:=
by
  exact isCompact_Icc

def mIc:MeasurableSet Ic:=
by
  exact measurableSet_Icc

def measurableSet_Ic_c: MeasurableSet Ic_c := by
    simp_all only [Ic_c]
    simp_all only [MeasurableSet.compl_iff]
    apply MeasurableSet.congr
    on_goal 2 => ext x : 1
    on_goal 2 => apply Iff.intro
    on_goal 2 => {
      intro a
      exact a
    }
    · apply measurableSet_Icc
    · intro a
      simp_all only

instance : TopologicalSpace Ic := inferInstance

--インスタンスの証明でつかっている。
lemma compact_set_has_finite_measure {K : Set Ic} (hK : IsCompact K) :
  volume K < ⊤ :=
by
  -- `K` の像 `Subtype.val '' K` が `ℝ` 上でコンパクト
  have hK_comp : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val

  -- `ℝ` 上のコンパクト集合の測度が有限であることを利用
  have hK_finite : MeasureTheory.MeasureSpace.volume (Subtype.val '' K) < ⊤ :=
    IsCompact.measure_lt_top hK_comp

  -- `Measure.restrict_apply` を使い `volume K = MeasureTheory.MeasureSpace.volume (K ∩ Set.univ)` に展開
  have volume_eq : volume K = MeasureTheory.MeasureSpace.volume (K ∩ Set.univ) :=
    by simp_all only [inter_univ]

  have h_meas : MeasurableSet K := IsCompact.measurableSet hK
  have h_meas2:  MeasurableSet (Subtype.val '' K) := IsCompact.measurableSet hK_comp
  have RIc:(MeasureTheory.MeasureSpace.volume : Measure Ic) (Subtype.val ⁻¹' (Subtype.val '' K))
    = (MeasureTheory.MeasureSpace.volume : Measure ℝ) (Subtype.val '' K) :=
  by
    let mtm := @MeasureTheory.Measure.restrict_apply ℝ _ (volume : Measure ℝ) Ic (Subtype.val '' K) h_meas2

    have preimage:Subtype.val ⁻¹' (Subtype.val '' K) = K:=
    by
      simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq]
    rw [preimage]

    have :Subtype.val '' K ∩ Ic = Subtype.val '' K:=
    by
      simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq,
        image_val_inter_self_left_eq_coe]

    rw [this] at mtm
    rw [←mtm]

    suffices (volume.restrict Ic) K = volume K from
    by
      simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq,
        image_val_inter_self_left_eq_coe, Measure.restrict_apply]

    have : Measure.comap Subtype.val volume = volume.restrict (univ : Set Ic):=
    by
      simp_all only [inter_univ, Measure.restrict_apply, Subtype.val_injective, preimage_image_eq,
        image_val_inter_self_left_eq_coe, Measure.restrict_univ]
      rfl
    simp_all only [inter_univ, Measure.restrict_apply, Subtype.val_injective, preimage_image_eq,
      image_val_inter_self_left_eq_coe, Measure.restrict_univ]
    rw [←this]
    dsimp [volume]
    rw [MeasureTheory.Measure.comap_apply]
    · simp_all only [Subtype.val_injective]
    · show ∀ (s : Set { x // x ∈ Ic }), MeasurableSet s → MeasurableSet (Subtype.val '' s)
      intro s hs
      apply MeasurableSet.subtype_image
      · apply MeasurableSet.inter
        · apply measurableSet_le
          · simp_all only [measurable_const]
          · exact measurable_id
        · apply measurableSet_le
          · exact measurable_id
          · simp_all only [measurable_const]
      exact hs

    · show MeasurableSet K
      simp_all only

  -- `K ∩ Set.univ ⊆ Subtype.val '' K` の単調性を利用
  have measure_mono2 : MeasureTheory.MeasureSpace.volume (Subtype.val '' K) ≤ MeasureTheory.MeasureSpace.volume (K ∩ Set.univ) :=
  by
    have eq_univ : K ∩ Set.univ = K := by rw [inter_univ]

    -- Step 2: `K ⊆ Subtype.val ⁻¹' (Subtype.val '' K)` を示す
    --have h_subset : K ⊆ Subtype.val ⁻¹' (Subtype.val '' K) :=
    --  fun x hx => mem_preimage.mpr (mem_image_of_mem Subtype.val hx)

    have measure_mono_r : (MeasureTheory.MeasureSpace.volume : Measure ℝ) K ≤
    (MeasureTheory.MeasureSpace.volume : Measure Ic) (Subtype.val ⁻¹' (Subtype.val '' K)) :=
    by
    -- Step 3: 測度の単調性を適用
      have measure_mono_ineq : (MeasureTheory.MeasureSpace.volume :Measure Ic) K≤
        (MeasureTheory.MeasureSpace.volume : Measure ℝ) (Subtype.val '' K) :=
      by
        --let mtm := @MeasureTheory.Measure.restrict_apply _ _  volume Ic (Subtype.val '' K) h_meas2
        simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq, le_refl]

      simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq, le_refl]
    -- `K ∩ Set.univ = K` なので書き換える
    rw [eq_univ]
    have :Subtype.val ⁻¹' (Subtype.val '' K) = K:=
    by
      simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq]
    rw [this] at measure_mono_r
    exact measure_mono_r

  -- 測度の有限性より `volume K < ⊤`
  rw [volume_eq]

  have measure_mono3 :  MeasureTheory.MeasureSpace.volume (K ∩ Set.univ) ≤ MeasureTheory.MeasureSpace.volume (Subtype.val '' K):=
  by
    simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq]

  simp_all only [inter_univ, gt_iff_lt]
  exact measure_mono3.trans_lt hK_finite

--IcへのFiniteMeasureOnCompactsの設定はうまくいった。後ろの定理で利用している。
--MeasureTheory.IsFiniteMeasureOnCompacts.mkを使ってもできるかも。
--theorem ∀ {α : Type u_1} {m0 : MeasurableSpace α} [inst : TopologicalSpace α] {μ : Measure α},   (∀ ⦃K : Set α⦄, IsCompact K → ↑↑μ K < ⊤) → IsFiniteMeasureOnCompacts μ
noncomputable instance : IsFiniteMeasureOnCompacts (volume : Measure Ic) where
  lt_top_of_isCompact :=
  by
    intro K hK
    have hK_ms : MeasurableSet (K : Set Ic) := hK.measurableSet
    -- K ⊆ univ is trivial.
    have hK_sub : K ⊆ Set.univ := by intro x hx; trivial
    have rfl1 : volume K = MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.univ : Set Ic) K := by simp_all only [subset_univ,
      Measure.restrict_univ]
    rw [rfl1]
    have rfl2 : MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.univ : Set Ic) K = MeasureTheory.MeasureSpace.volume K :=
      by simp_all only [subset_univ, Measure.restrict_univ]
    rw [rfl2]
    have hK_comp : IsCompact (K : Set ℝ) :=
    by
      simp_all only [subset_univ, Measure.restrict_univ]
      convert hK
      simp_all only [iff_true]
      exact hK.image continuous_subtype_val

    have : MeasurableSet (K : Set Ic) := hK.measurableSet
    have : K ⊆ Set.univ := by
      intro x hx
      trivial
    rw [rfl1]
    have : MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.univ:Set Ic) K = MeasureTheory.MeasureSpace.volume K :=
    by
      simp_all only [Measure.restrict_univ, subset_univ]
    rw [this]
    have hK_comp : IsCompact (K : Set ℝ) :=
      by
        simp_all only [Measure.restrict_univ, subset_univ]
    have hK_bounded : Bornology.IsBounded (K : Set ℝ) := IsCompact.isBounded hK_comp
    simp_all only [Measure.restrict_univ, subset_univ, gt_iff_lt]
    have hK_comp : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val

    -- `ℝ` のコンパクト集合の測度が有限であることを利用
    have hK_finite : MeasureTheory.MeasureSpace.volume (Subtype.val '' K) < ⊤ :=
      IsCompact.measure_lt_top hK_comp

    -- `Measure.restrict` の単調性より、`volume K ≤ volume (Subtype.val '' K)`
    --#check @measure_Icc_lt_top  Ic _ _ _ _ volume _ 0 1
    exact compact_set_has_finite_measure hK
    --let mi := @measure_Icc_lt_top  Ic _ _ _ _ volume _ 0 1



------------------------------------------------------
----古いものや、証明に使ってないもの。保存しているものなど。
------------------------------------------------------

--これは頑張って証明した。現在は使ってないかも。OpenPosiの証明に使えるかもしれないと思ったが使ってない。
lemma open_ball_lemma {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hxU : x ∈ U) :
    ∃ ε > 0, Ioo (x - ε) (x + ε) ⊆ U :=
by
  -- `isOpen_iff_forall_mem_open` を適用して、x を含む開集合 V ⊆ U を得る
  obtain ⟨V, hV_subU, hV_open, hxV⟩ := isOpen_iff_forall_mem_open.mp hU x hxU
  -- `Metric.isOpen_iff` を適用して、V 内の x で開球 ball x ε ⊆ V を得る
  obtain ⟨ε, hε_pos, h_ball_subV⟩ := Metric.isOpen_iff.mp hV_open x hxV
  -- 開区間 Ioo (x - ε, x + ε) が開球 ball x ε に含まれることを示す
  have hIoo_sub_ball : Ioo (x - ε) (x + ε) ⊆ ball x ε := by
    intro y hy
    rw [mem_ball]
    rw [dist_comm]
    simp_all only [gt_iff_lt, mem_Ioo]
    obtain ⟨left, right⟩ := hy
    rw [dist_eq_norm]
    simp_all only [norm_eq_abs]
    rw [abs]
    simp_all only [neg_sub, sup_lt_iff]
    apply And.intro
    · linarith
    · linarith
  -- 包含関係を伝播させて `Ioo (x - ε, x + ε) ⊆ U` を示す
  refine ⟨ε, hε_pos, ?_⟩
  simp_all only [gt_iff_lt]
  intro y hy
  simp_all only [mem_Ioo]
  obtain ⟨left, right⟩ := hy
  apply hV_subU
  apply h_ball_subV
  simp_all only [mem_ball]
  apply hIoo_sub_ball
  simp_all only [mem_Ioo, and_self]

--これも頑張って証明した。使ってないかも。
lemma open_ball_lemma_strong {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hxU : x ∈ U) (hxI : x ∈ Ioo 0 1):
  ∃ ε > 0,
    ε < min (dist x 0) (dist x 1) ∧
    Ioo (x - ε) (x + ε) ⊆ U ∧
    Ioo (x - ε) (x + ε) ⊆ Icc 0 1 := by
  -- open_ball_lemma を使用して ε を取得
  obtain ⟨ε, hε_pos, hIoo_subU⟩ := open_ball_lemma hU hxU

  obtain ⟨hx0, hx1⟩ := hxI
  -- `ε` を小さくして `Ioo (x - ε) (x + ε) ⊆ Ioo 0 1` となるように調整する
  let δ := (min ε (min (x - 0) (1 - x)))/2
  have hδ_pos : δ > 0 := by
    simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, δ]
  have hIoo_sub_Ioo01 : Ioo (x - δ) (x + δ) ⊆ Ioo 0 1 := by
    intro y hy
    rw [mem_Ioo] at hy ⊢
    constructor
    ·
      simp_all only [gt_iff_lt, sub_zero, δ]
      obtain ⟨left, right⟩ := hy
      apply lt_of_le_of_lt
      on_goal 2 => {exact left
      }
      ·
        simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos,
          sub_nonneg]
        rw [div_le_iff₀ ]
        simp_all only [inf_le_iff, le_mul_iff_one_le_right, Nat.one_le_ofNat, tsub_le_iff_right,
          true_or, or_true]
        simp_all only [Nat.ofNat_pos]

    ·
      simp_all only [gt_iff_lt, sub_zero, δ]
      obtain ⟨left, right⟩ := hy
      apply lt_of_lt_of_le
      exact right
      have :(ε ⊓ (x ⊓ (1 - x))) / 2 < 1-x:=
      by
        have :(1 - x)/2 < 1 -x :=
        by
          simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos,
            half_lt_self_iff]
        have :(ε /2 ⊓ (x /2 ⊓ (1 - x)/2 ))  < 1-x:=
        by
          simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos,
            half_lt_self_iff, inf_lt_iff, or_true]
        have :(ε /2 ⊓ (x /2 ⊓ (1 - x)/2 )) = (ε ⊓ (x ⊓ (1 - x))) / 2 :=
        by
          --simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, half_lt_self_iff, δ]
          --ring_nf
          rw [min_div_div_right]  -- `min (a / 2) (b / 2) = (min a b) / 2`
          rw [← min_assoc]
          rw [min_div_div_right]  -- `min (a / 2) (b / 2) = (min a b) / 2`
          simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos,
            half_lt_self_iff, inf_lt_iff, or_true]
          ac_rfl
          exact zero_le_two
          exact zero_le_two
        simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos,
          half_lt_self_iff]
      simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos,
        ge_iff_le]
      linarith

  -- したがって `Ioo (x - δ) (x + δ) ⊆ U ∩ Ioo 0 1` となる
  use δ, hδ_pos  --あっているか不明。
  constructor
  · dsimp [dist]
    rw [@lt_min_iff]
    constructor
    · simp
      dsimp [Ioo] at hIoo_sub_Ioo01
      rw [@setOf_and] at hIoo_sub_Ioo01
      suffices   δ < x from by
        simp_all [δ]
        rw [abs]
        simp_all only [lt_sup_iff, true_or]
      dsimp [δ]
      simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, δ]
      rw [div_lt_iff₀ (zero_lt_two' ℝ)]
      simp_all only [inf_lt_iff, lt_mul_iff_one_lt_right, Nat.one_lt_ofNat, true_or, or_true]
    · suffices δ < 1 - x from by
        simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, δ]
        rw [abs]
        simp_all only [neg_sub, lt_sup_iff, or_true]
      dsimp [Ioo] at hIoo_sub_Ioo01
      rw [@setOf_and] at hIoo_sub_Ioo01
      dsimp [δ]
      simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, δ]
      rw [div_lt_iff₀']
      simp_all only [inf_lt_iff]
      simp_all only [sub_pos, lt_mul_iff_one_lt_left, Nat.one_lt_ofNat, or_true]
      simp_all only [Nat.ofNat_pos]

  · dsimp [Ioo] at hIoo_subU
    dsimp [Ioo] at hIoo_sub_Ioo01
    simp at hIoo_sub_Ioo01
    simp_all only [gt_iff_lt, sub_zero, δ]
    constructor
    · dsimp [Ioo]
      intro y hy
      simp at hy
      obtain ⟨left, right⟩ := hy
      rw [← sub_lt_iff_lt_add'] at right
      have : y∈ {x_1 | x - ε < x_1 ∧ x_1 < x + ε} := by
        simp
        have : ε > (ε ⊓ (x ⊓ (1 - x))) / 2 :=
          by
            simp_all only [gt_iff_lt, lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left,
              Nat.ofNat_pos]
            rw [div_lt_iff₀ (zero_lt_two' ℝ)]
            simp_all only [inf_lt_iff, lt_mul_iff_one_lt_right, Nat.one_lt_ofNat, true_or]
        constructor
        ·
          simp_all only [sub_lt_self_iff, lt_add_iff_pos_right, Nat.ofNat_pos,
            div_pos_iff_of_pos_right, lt_inf_iff, sub_pos, true_and, gt_iff_lt]
          obtain ⟨left_1, right_1⟩ := hδ_pos
          linarith
        · linarith
      simp_all only [mem_setOf_eq]
      simp_all only [sub_lt_self_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right,
        lt_inf_iff, sub_pos, true_and]
      obtain ⟨left_1, right_1⟩ := hδ_pos
      obtain ⟨left_2, right_2⟩ := this
      exact hIoo_subU ⟨left_2, right_2⟩
    · dsimp [Ioo]
      dsimp [Icc]
      intro y hy
      simp
      constructor
      · simp at hy
        simp_all only [sub_lt_self_iff, lt_add_iff_pos_right, Nat.ofNat_pos,
          div_pos_iff_of_pos_right, lt_inf_iff, sub_pos, true_and]
        obtain ⟨left, right⟩ := hδ_pos
        obtain ⟨left_1, right_1⟩ := hy
        apply le_of_lt
        simp_all only
      ·
        simp_all only [sub_lt_self_iff, lt_add_iff_pos_right, Nat.ofNat_pos,
          div_pos_iff_of_pos_right, lt_inf_iff, sub_pos, true_and, mem_setOf_eq]
        obtain ⟨left, right⟩ := hδ_pos
        obtain ⟨left_1, right_1⟩ := hy
        apply le_of_lt
        simp_all only
