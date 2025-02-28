import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice
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
import Mathlib.Analysis.SpecialFunctions.Integrals
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
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Order.Group.Lattice
import LeanCopilot

--距離空間の練習 6。01区間の連続関数がL2ノルムで距離の公理を満たす問題。
--証明が難しく未完なのは、2つの関数の距離が0であれば、関数が一致する部分と、三角不等式の部分。
--2月27日現在。どちらの部分も未完。ここ1週間、これだけに取り組んでいるが。
--最初、うまく積分が定義できなかったので、0,1閉区間上の関数を実数全体にextendする方法で
--積分を定義していたが、それだと、他の部分で証明が難しくなることが判明して、01上にMesurable Spaceを定義する方法に変更した。
--しかし、三角不等式を示すところで、実数全体に拡張した方がよいというアドバイスがあったので、部分的に拡張している。
--至るところzeroであれば、zeroを証明するために01閉区間IcにOpenPosの空間のインスタンスを設定しようとしたが、
--instanceの定義がおかしいのか、相対位相がちゃんと定義されてないからなのか、証明できない命題が出てきてしまった。
--よって、IcにOpenPosを設定するのは断念。でも、OpenPosをやめて、直接、証明しようとしても、
--区間の端の扱いなど難しいところが出てきて、結局、IcにOpenPosを設定するという一般的なアプローチのほうが
--よいのではないかと思い直して、OpenPosのアプローチをはじめからやり直すかもしれない。
--OpenPosのインスタンスの設定には、後ろにあるopen_ball_lemmaとopen_ball_lemma_strongの定理が使えるかも。
--FiniteMeasureOnCompactsのinstanceの設定で3角不等式の部分の距離の有界性が示せた。

--あと2日ぐらい頑張れば完全に証明できそうだが、ルベーグ積分について勉強してから再開するといいかも。
set_option maxHeartbeats 2000000
open Classical
open MeasureTheory Real Set Metric Function Filter TopologicalSpace ENNReal

--基本的な定義とinstanceの設定

instance : SeminormedAddCommGroup ℝ := by
  constructor
  simp_all only [norm_eq_abs]
  simp [dist_eq]

def C₀ := ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ
def Ic := Set.Icc (0:Real) 1

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

instance : TopologicalSpace Ic := inferInstance

--使ってないかも。
lemma measure_restrict_eq_measure {K : Set ℝ} (hK : MeasurableSet K) (hK_sub : K ⊆ Ic) :
  (volume.restrict Ic) K = (volume : Measure ℝ) K :=
by
  -- `Measure.restrict_apply` を適用
  rw [MeasureTheory.Measure.restrict_apply hK]

  -- `K ⊆ Ic` なので `K ∩ Ic = K`
  rw [inter_eq_self_of_subset_left hK_sub]

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
      simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq, subset_refl]
    rw [preimage]

    have :Subtype.val '' K ∩ Ic = Subtype.val '' K:=
    by
      simp_all only [inter_univ, subset_refl, Subtype.val_injective, preimage_image_eq,
        image_val_inter_self_left_eq_coe]

    rw [this] at mtm
    rw [←mtm]

    suffices (volume.restrict Ic) K = volume K from
    by
      simp_all only [inter_univ, subset_refl, Subtype.val_injective, preimage_image_eq,
        image_val_inter_self_left_eq_coe, Measure.restrict_apply]

    have : Measure.comap Subtype.val volume = volume.restrict (univ : Set Ic):=
    by
      simp_all only [inter_univ, subset_refl, Measure.restrict_apply, Subtype.val_injective, preimage_image_eq,
        image_val_inter_self_left_eq_coe, Measure.restrict_univ]
      rfl
    simp_all only [inter_univ, subset_refl, Measure.restrict_apply, Subtype.val_injective, preimage_image_eq,
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
        simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq, subset_refl, le_refl]

      simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq, subset_refl, le_refl]
    -- `K ∩ Set.univ = K` なので書き換える
    rw [eq_univ]
    have :Subtype.val ⁻¹' (Subtype.val '' K) = K:=
    by
      simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq, subset_refl]
    rw [this] at measure_mono_r
    exact measure_mono_r

  -- 測度の有限性より `volume K < ⊤`
  rw [volume_eq]

  have measure_mono3 :  MeasureTheory.MeasureSpace.volume (K ∩ Set.univ) ≤ MeasureTheory.MeasureSpace.volume (Subtype.val '' K):=
  by
    simp_all only [inter_univ, Subtype.val_injective, preimage_image_eq, subset_refl]

  simp_all only [inter_univ, gt_iff_lt]
  exact measure_mono3.trans_lt hK_finite

--IcへのFiniteMeasureOnCompactsの設定はうまくいった。
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

-----------------------------------------------

--連続関数がいたるところ0であれば、0という補題。未完。
lemma continuous_eq_zero_of_ae_eq_zero_Ic
  (f : C₀)
  (h : ∀ᵐ x ∂(volume : MeasureTheory.Measure Ic), f.1 x = 0) :
  ∀ x : Ic, f.1 x = 0 :=
by

  /-
    1) 「f = 0 がほぼ至る所成り立つ」という仮定 h から，
       {x | f x ≠ 0} の測度が 0 であることを取り出す
  -/
  have h_eq : (fun x => f.1 x) =ᶠ[ae (volume : MeasureTheory.Measure Ic)] 0 := h
  have zero_measure : (volume : MeasureTheory.Measure Ic) {x | f.1 x ≠ 0} = 0 :=
  by
    simp_all only [ContinuousMap.toFun_eq_coe, Function.const_apply]
    simp_all only [ne_eq]
    exact h

  --連続関数がいたるところで0ならば、常に0という定理。
  --Continuous.ae_eq_iff_eqは使えなかった理由は、IcにOpenPosMeasureのインスタンスがないから。
-- 実数上の閉区間は、実際にはOpenPosMeasureのinstanceを設定可能だが、難しいので保留中。

  /-
    2) もし {x | f x ≠ 0} が非空かつ開集合ならば，
       その部分集合は正の測度をもつはずで，0 とは矛盾する。
       連続関数 f の「≠ 0 の部分」は開集合になるので，測度 0 なら空集合でないといけない。
  -/
  -- Ic 上で「≠ 0」の部分集合を E とおく
  set E := {x : Ic | f.1 x ≠ 0} with hE

  -- もし E が空でないなら矛盾を導く
  by_contra H
  push_neg at H
  obtain ⟨x₀, hx₀⟩ := H   -- E 内にある点 x₀ 。0や1になることもあるのか。その場合は場合分けしたほうがいいのか。
  --xが0ならば、その近くに0でない点があるので問題ないが。
  /-
    連続性により，x₀ のまわりでは f x は 0 でない値を取り続ける。
    すると E は (区間の中で) 開集合になるので，そこの測度は正になるはず。
    ところが先ほど volume E = 0 を得ており矛盾。
  -/
  have : f.1 x₀ ≠ 0 := hx₀
  let ε := |f.1 x₀| / 2
  have hε : 0 < ε := by
    apply half_pos
    exact abs_pos.mpr this

  -- f の連続性から，x₀ 近傍で f x が f x₀ に近くなる領域を取る
  --have : ∃ U : Set Ic, IsOpen U ∧ x₀ ∈ U ∧ ∀ y ∈ U, |f.1 y - f.1 x₀| < ε :=
--  by
--    sorry
  have : UniformContinuous f.1 :=
  by
    have isCompact:IsCompact Ic:=
    by
      dsimp [Ic]
      simp_all only [ContinuousMap.toFun_eq_coe, ne_eq, not_false_eq_true, abs_pos, div_pos_iff_of_pos_left,
        Nat.ofNat_pos, E, ε]
      obtain ⟨val, property⟩ := x₀
      apply isCompact_Icc
    have Compact_Ic: CompactSpace Ic:=
    by
      simp_all only [ContinuousMap.toFun_eq_coe, ne_eq, not_false_eq_true, abs_pos, div_pos_iff_of_pos_left,
        Nat.ofNat_pos, E, ε]
      obtain ⟨val, property⟩ := x₀
      rw [← isCompact_iff_compactSpace]
      simp_all only [E]
    apply Compact_Ic.uniformContinuous_of_continuous f.2

  obtain ⟨δ, δpos, hδ⟩ := Metric.uniformContinuous_iff.mp this ε hε

  --rcases this with ⟨U, hUopen, hx₀U, hU⟩
  let U := { y : Ic | |(y : ℝ) - (x₀ : ℝ)| < δ }
  -- U の任意の点 y で f y と f x₀ は近いので，f y は 0 にならない
  have U_subset_E : U ⊆ E :=
  by
    simp_all [E, ε]
    obtain ⟨val, property⟩ := x₀
    intro z hz
    simp
    dsimp [U] at hz
    let hd := hδ z z.2 val property
    simp at hd
    dsimp [dist] at hd
    specialize hd hz
    by_contra h_contra
    rw [h_contra] at hd
    simp at hd
    ring_nf at hd
    rw [@mul_one_div] at hd
    dsimp [Ic] at hd
    rw [ContinuousMap.congr_arg f rfl] at hd
    set F := |f.1 ⟨val, property⟩| with FF
    dsimp [property] at FF
    rw [←FF] at hd
    have : F ≥ 0:=
    by
      simp_all only [ContinuousMap.toFun_eq_coe, ge_iff_le, abs_nonneg, U, E, F]
    linarith

  --U上ではゼロでなく、測度もゼロでないことが示せる。
  -- ところが measure E = 0 より measure U = 0 となり，
  have zero_U : volume U = 0 := measure_mono_null U_subset_E zero_measure

  -- 0でない値の周りにepsilonを十分に小さくとると、その周りには0でない場所ができる。
  -- その範囲の測度は0でない。上ですでにepsilonを取っている。
  --開区間の測度は、幅で表せる。
  have measure_pos : 0 < (volume : Measure Ic) U :=
  by
    sorry
    /-
    -- U = { y in [0,1] | |y.val - x₀.val| < δ } なので，
    --  その投影はインターバル (x₀.1 - δ, x₀.1 + δ) ∩ [0,1]
    --  これは長さ > 0 の区間．
    --xが0や1のときは場合分けした方がよいかも。0のときは、0からdeltaのところは開集合。
    --もしくはxをdelta/2にとってもよさそう。
    by_cases hx0: x₀.val = 0
    case pos =>
      sorry
    case neg =>
    by_cases hx1: x₀.val = 1
    case pos =>
      sorry
    case neg =>  --x0が0でも1でもないケース。

    let low : Ic := ⟨x₀.val - δ, by {
      -- Prove that x₀.val - δ ∈ Icc 0 1.
      have h₁ : 0 < δ := δpos
      have h₀ : 0 < x₀.val := by --xがぴったり0のときはどうするのか。
        simp_all [ε, E, U]
        obtain ⟨val, property⟩ := x₀
        simp_all only [E]
        dsimp [Ic] at property
        dsimp [Icc] at property
        have :val ≠ 0:=
        by
          simp_all only [ne_eq, E]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [sub_zero, Icc.mk_zero, not_true_eq_false, E]
        exact unitInterval.pos_iff_ne_zero.mpr hx0
      have h_low : 0 ≤ x₀.val - δ := by sorry --本当になりたつのか？そもそも必要か。IccじゃなくてもIocでもvolume正にできそう。
      have h_up : x₀.val - δ ≤ 1 := by linarith [x₀.property.2]
      exact ⟨h_low, h_up⟩
    }⟩
    let high : Ic := ⟨x₀.val + δ, by {
      -- Prove that x₀.val + δ ∈ Icc 0 1
      have h₁ : 0 < δ := δpos
      have h_up : x₀.val + δ ≤ 1 := by sorry
      have h_low : 0 ≤ x₀.val + δ := by sorry
      exact ⟨h_low, h_up⟩
    }⟩
    have : low < high:=
    by
      simp_all only [ContinuousMap.toFun_eq_coe, ne_eq, not_false_eq_true, abs_pos, div_pos_iff_of_pos_left,
        Nat.ofNat_pos, Subtype.mk_lt_mk, ε, E, U, low, high]
      linarith
    let mtv : ENNReal := (volume:Measure Ic) (Ioo low high) --ENNReal.ofReal ((x₀.val + δ) - (x₀.val - δ))
    have mtv_pos : 0 < mtv :=
    by
      simp_all only [E, sub_pos, gt_iff_lt, zero_lt_one, zero_lt_two, zero_lt_one', zero_lt_two']
      simp_all only [ContinuousMap.toFun_eq_coe, ne_eq, not_false_eq_true, abs_pos, div_pos_iff_of_pos_left,
        Nat.ofNat_pos, ε, U, E, mtv, low, high]
      obtain ⟨val, property⟩ := x₀
      obtain ⟨val_1, property_1⟩ := low
      obtain ⟨val_2, property_2⟩ := high
      simp_all only [E]
      --lowが0だったり、highが1だったりしても、測度は正になりそう。
      --非空なIooは測度が正であるという定理をつかうはず。ただ、Icのvolumeで考えないといけないので、面倒。
      --exact (@MeasureTheory.Measure.measure_Ioo_pos Ic _ _ _ (volume : Measure Ic) _ _ low.val high.val).mpr (Subtype.val_lt.2 this)
      --この直接的な方法でやるかIcがOpenPosMeasureのインスタンスを持つことを示すかのどっちか。
      --OpenPosのインスタンスが難しいので断念してこちらに戻ってきたが、同じくらい難しかった。
      --両者のやっていることは本質的に同じな気がする。OpenPosiのほうが簡単な可能性もある。
      sorry
    have mtv_eq : mtv ≤ (volume : Measure Ic) U :=
    by
      dsimp [mtv]
      apply measure_mono
      simp_all only [ContinuousMap.toFun_eq_coe, ne_eq, not_false_eq_true, abs_pos, div_pos_iff_of_pos_left,
        Nat.ofNat_pos, ε, U, mtv, E, low, high]
      obtain ⟨val, property⟩ := x₀
      obtain ⟨val_1, property_1⟩ := low
      obtain ⟨val_2, property_2⟩ := high
      simp_all only [E]
    exact lt_of_lt_of_le mtv_pos mtv_eq

  -/

    --apply measure_pos_of_exists_mem_open
    --· exact zero_U
  --· -- show: ∃ z ∈ U, IsOpen (U)  (もう持ってる)
   --   exact ⟨x₀, hx₀U, U_open⟩

  -- 結局 measure(U) = 0 と measure(U) > 0 の矛盾
  --linarith
  have : U = ∅ := by
    -- 「サブスペースの非空開集合は測度 > 0」の議論
    -- ここで measure U = 0 と矛盾 => U = ∅
    dsimp [U]
    simp_all only [ContinuousMap.toFun_eq_coe, ne_eq, not_false_eq_true, abs_pos, div_pos_iff_of_pos_left,
      Nat.ofNat_pos, gt_iff_lt, Subtype.forall, mem_Icc, setOf_subset_setOf, lt_self_iff_false, U, E, ε]

  -- すると x₀ ∈ U の仮定に矛盾
  --Eのvolumeが0でないということを示す必要あり。

  simp_all only [ContinuousMap.toFun_eq_coe, ne_eq, not_false_eq_true, abs_pos, div_pos_iff_of_pos_left,
    Nat.ofNat_pos, isOpen_empty, mem_empty_iff_false, E, ε]
  simp_all only [gt_iff_lt, Subtype.forall, mem_Icc, empty_subset, measure_empty, lt_self_iff_false, U, E, ε]


--これは、01上で関数を定義した場合の補題。以下を使って証明したい。
--theorem continuous_eq_zero_of_ae_eq_zero_Ic
--  (f : C₀) (h : ∀ᵐ x ∂(volume : MeasureTheory.Measure Ic), f.1 x = 0) :
--  ∀ x : Ic, f.1 x = 0
lemma continuous_nonneg_eq_zero_of_integral_zero_Ic (f : C(Ic, ℝ))(hf_nonneg : ∀ x, 0 ≤ f.1 x)
    (h : ∫ x : Ic, (f.1 x) = 0) :
    ∀ x :Ic, f.1 x = 0 :=
by
  have h_nonneg : 0 ≤ fun x => f x := by
    intro x
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Measure.restrict_univ, Pi.zero_apply]

  -- `f` が積分可能であることを示す
  have h_cont : ContinuousOn f (Set.univ : Set Ic) := f.continuous.continuousOn
  --have h_cont2: ContinuousOn f.1 Ic:= f.continuous.continuousOn

  -- The interval [0, 1] is compact
  have h_compact : IsCompact Ic := isCompact_Icc

  have h_integrable : Integrable f volume :=
  by

    let ci := @Continuous.integrableOn_Icc Ic ℝ _ _ _ f.1 volume _ ⟨0, by simp [Ic]⟩ ⟨1, by simp [Ic]⟩ _ _ _ _ f.2
    --FiniteMeasure.integrable_on_compactのinstanceが必要。

    --apply @MeasureTheory.IntegrableOn.integrable R全体に定義されている関数を制限するものなので、ここでは適切でない可能性。
    convert ci
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Icc.mk_zero, Icc.mk_one]
    ext s : 1
    --show Integrable (⇑f) x = IntegrableOn (⇑f) (Icc 0 1) x
    let mti := MeasureTheory.IntegrableOn f (Set.univ:Set Ic) volume
    have: Icc ⟨0, by simp [Ic]⟩ ⟨1, by simp [Ic]⟩ = (univ : Set Ic) :=
    by
      simp_all only [Icc.mk_zero, Icc.mk_one]
      ext x : 1
      simp_all only [mem_Icc, mem_univ, iff_true]
      obtain ⟨val, property⟩ := x
      exact property

    have IcRW: IntegrableOn (⇑f) (Icc ⟨0, by simp [Ic]⟩ ⟨1, by simp [Ic]⟩) s = IntegrableOn f (univ:Set Ic) s :=
    by
      simp_all only [Icc.mk_zero, Icc.mk_one, integrableOn_univ]

    have :IntegrableOn f (univ:Set Ic) s = Integrable f (s.restrict (univ:Set Ic)):=
    by
      simp_all only [integrableOn_univ, Measure.restrict_univ]
    rw [←IcRW] at this
    simp at this
    rw [this]

  -- `f` が測度論的に 0 であることを示す
  have h_ae_zero : f =ᵐ[volume] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => hf_nonneg x) h_integrable).mp h
  -- `continuous_eq_zero_of_ae_eq_zero_Ic` を適用
  exact continuous_eq_zero_of_ae_eq_zero_Ic f h_ae_zero

--使っている。
lemma q2c {f : C₀} : Continuous (fun x => (f.1 x)^2) :=
by
  simp_all only [ContinuousMap.toFun_eq_coe]
  fun_prop

lemma continuous_sq_eq_zero_of_integral_zero_Ic {f : C₀}
   (h : ∫ x in (Set.univ : Set Ic), (f.1 x)^2 = 0) :
   ∀ x :Ic, f.1 x = 0 :=
by
  have hf_nonneg : ∀ x, 0 ≤ (f.1 x) ^ 2 := by
    intro x
    exact pow_two_nonneg (f.1 x)
  -- 積分が 0 なので、(f x) ^ 2 = 0
  have hf_eq_zero : ∀ x ∈ Set.Icc 0 1, (f.1 x) ^ 2 = 0 := by
    have hf_sq_cont : ContinuousOn (fun x => (f.1 x) ^ 2) (Set.Icc 0 1) := by
      simp_all
      fun_prop
    show ∀ x ∈ Set.Icc 0 1, f.toFun x ^ 2 = 0
    let f2 := fun x => f.toFun x ^ 2
    let f2c := ContinuousMap.mk (fun (x:Ic) => (f.1 x) ^ 2) (@q2c f)
    have f2inC : Continuous f2:=
    by
      simp_all [f2]
      fun_prop

    have : ∀ x, f2 x ≥ 0 :=
    by
      intro x
      simp_all [f2]
      obtain ⟨val, property⟩ := x
      positivity
    have :∀ (x : ↑(Set.Icc 0 1)), 0 ≤ (⟨f2,f2inC⟩ : C₀).toFun x :=
    by
      intro x
      dsimp [f2]
      obtain ⟨val, property⟩ := x
      positivity

    let cne := continuous_nonneg_eq_zero_of_integral_zero_Ic f2c
    intro x hx
    dsimp [f2c] at cne
    specialize cne this
    have :∫ (x : Ic), (f.1 x) ^ 2 = 0 :=
    by
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, integral_zero, le_refl, implies_true, ge_iff_le,
        mem_Icc, zero_le', true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Subtype.forall,
        forall_const, zero_pow, f2c, f2]
    specialize cne this
    show f.toFun x ^ 2 = 0
    simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, integral_zero, le_refl, implies_true, ge_iff_le,
      mem_Icc, zero_le', true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Subtype.forall,
      f2c, f2]
    simp_all only [ContinuousMap.toFun_eq_coe, f2, f2c]
    obtain ⟨val, property⟩ := x
    simp_all only [f2c, f2]

  -- (f x) ^ 2 = 0 ならば f x = 0
  show ∀ (x : ↑Ic), f.toFun x = 0
  intro x
  exact pow_eq_zero (hf_eq_zero x (Set.mem_Icc.2 ⟨x.2.1, x.2.2⟩))

-------------------------------------------------------------------------
--------この辺りから下が三角不等式や可測性に関係がある部分-----------------------
------------------------------------------------------------------------

noncomputable def L2_distance_Ic (f g : C₀) : ℝ :=
  Real.sqrt (∫ x in (Set.univ:Set Ic), (f.1 x - g.1 x) ^ 2)

-- ContinuousMap subtraction --これがないとHSub C₀ C₀ ?m.1384936が1500目ぐらいででる。
instance : Sub C₀ where
  sub f g := ⟨λ x => f.1 x - g.1 x, f.continuous_toFun.sub g.continuous_toFun⟩

instance : AddGroup C₀ where
  add := λ f g => ⟨λ x => f.1 x + g.1 x, f.continuous_toFun.add g.continuous_toFun⟩
  zero := ⟨λ x => 0, continuous_const⟩
  neg := λ f => ⟨λ x => -f.1 x, f.continuous_toFun.neg⟩
  add_assoc := by
    intros
    rename_i a b c
    dsimp [Add.add]
    dsimp [C₀ ]
    ext
    ring_nf
  zero_add := by
    intros
    dsimp [C₀]
    ring_nf
  add_zero := by
    intros
    dsimp [C₀]
    ext x
    ring_nf

  nsmul := λ n f => ⟨λ x => n • f.1 x, f.continuous_toFun.nsmul n⟩
  zsmul := λ n f => ⟨λ x => n • f.1 x, f.continuous_toFun.zsmul n⟩
  neg_add_cancel := by
    intros
    dsimp [Add.add]
    dsimp [C₀]
    ext
    ring_nf
    simp_all only [ContinuousMap.add_apply, ContinuousMap.coe_mk, neg_add_cancel, ContinuousMap.zero_apply]

noncomputable def toFun (f : C₀) : ℝ → ℝ :=
  fun x => if hx:x ∈ Ic then f.1 ⟨x,hx⟩ else 0

--Icから実数全体に拡張した関数の可測性。うまいMathlibの定理がなかなか見つからず、
--Measurable.iteやMeasurable.piecewiseを使って証明しようとしたが、全体で可測である仮定を求められてうまくいかず。
--キー定理として、MeasurableEmbedding.measurable_extendを使うが、テクニカルに難しい同値性のゴールに陥って
--最後はかなり強引で、なにをやっているのか不明な状態だが、AIの力を借りてエラーがないことをまで持って行った。
lemma toFun_measurable (f : C₀) : Measurable (toFun f) :=
by
  have hIc : MeasurableSet Ic := (isCompact_Icc).measurableSet

  -- ② f は [0,1] 上で連続なので可測
  have :∀ x:Ic, f.1 x = toFun f x :=
  by
    intro x
    simp_all only [toFun]
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta]
  have : (fun x : { x // x ∈ Ic } => f.1 x) = (fun x : { x // x ∈ Ic } => toFun f x) :=
  by
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall]
  have hf_sub : Measurable (fun x : { x // x ∈ Ic } => f.1 x) :=
  by
    exact f.measurable
  have hf_sub2 : Measurable (fun x : { x // x ∈ Ic } => toFun f x) :=
  by
    rw [←this]
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall]

  have hf_on_Ic : Measurable (fun x : Ic => f.1 ⟨x, by simp [Ic]⟩) := by
    exact f.continuous.measurable

   -- `Subtype.val` は可測な埋め込み
  have h_meas_val : MeasurableEmbedding (Subtype.val : Ic → ℝ) :=
  by
    exact MeasurableEmbedding.subtype_coe hIc

  have h_meas_f_val : Measurable ((toFun f) ∘ (Subtype.val : Ic → ℝ)) :=
  by
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Subtype.coe_eta]
    exact hf_sub2


  have h_meas_Ic : MeasurableSet (univ : Set Ic) :=
  by
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Subtype.coe_eta, MeasurableSet.univ]

  have h_meas_zero : Measurable (fun (x:ℝ) => (0:ℝ)) := measurable_const

  have h_meas_f : Measurable f.1 :=
  by
    exact f.measurable

  -- `MeasurableEmbedding.measurable_extend` を適用
  let me := MeasurableEmbedding.measurable_extend h_meas_val h_meas_f h_meas_zero
  unfold toFun
  dsimp [Function.extend] at me
  have: Function.extend Subtype.val f.1 (fun x ↦ 0) = fun x ↦ if hx : x ∈ Ic then f.toFun ⟨x, hx⟩ else 0 :=
  by
    show (Function.extend Subtype.val f.toFun fun x ↦ 0) = fun x ↦ if hx : x ∈ Ic then f.toFun ⟨x, hx⟩ else 0
    --ここからはかなり強引な場合分け。
    ext x
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Subtype.coe_eta]
    split
    · dsimp [Function.extend]
      split
      · rename_i h0 h1
        --obtain ⟨val, property⟩ := x
        obtain ⟨val1, property1⟩ := h1
        dsimp [toFun]
        split
        · rename_i h0
          rename_i h1
          have ch1: choose (Exists.intro val1 property1 : ∃ a, ↑a = x) = x :=
          by
            simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Subtype.coe_eta]
            subst property1
            simp_all only [MeasurableSet.univ, Subtype.coe_prop, choose_eq]
          have ch2: choose (Exists.intro (↑val1) property1 : ∃ a, a = x) = x :=
          by
            subst property1
            simp_all only [MeasurableSet.univ, Subtype.coe_prop, choose_eq]
          have ch3: choose (Exists.intro (val1) property1 : ∃ a, a.val = x) = ⟨x,h0⟩ :=
          by
            --subst property1
            --simp_all only [MeasurableSet.univ, Subtype.coe_prop, choose_eq]
            have ch4: (choose (Exists.intro (val1) property1 : ∃ a, a.val = x)).val = x :=
            by
              simp_all only [MeasurableSet.univ, Subtype.coe_prop, choose_eq]
              --subst property1
              --simp_all only [MeasurableSet.univ, Subtype.coe_prop, choose_eq]
              set chosen_val := choose (Exists.intro val1 property1: ∃ a, a.val = x) with h_choose
              have h_chosen_property : chosen_val.val = x := choose_spec (Exists.intro val1 property1: ∃ a, a.val = x)
              exact h_chosen_property
            subst property1
            simp_all only [MeasurableSet.univ, choose_eq, Subtype.coe_eta]
            simp_all only [Subtype.coe_prop]
            obtain ⟨val, property⟩ := val1
            simp_all only
            ext : 1
            simp_all only
          subst property1
          simp_all only [MeasurableSet.univ, choose_eq, Subtype.coe_eta]
        · simp_all only [MeasurableSet.univ, not_true_eq_false]
      · dsimp [toFun]
        split
        · rename_i h0 h1
          have :x ∉ Ic := by
            simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Subtype.coe_eta]
            by_contra h_contra
            push_neg at h0
            let cont := h0 ⟨x,h1⟩
            contradiction
          contradiction
        · simp_all only [MeasurableSet.univ, not_true_eq_false]
    · dsimp [Function.extend]
      split
      ·
        rename_i h h_1
        simp_all only [MeasurableSet.univ]
        obtain ⟨w, h_1⟩ := h_1
        obtain ⟨val, property⟩ := w
        subst h_1
        simp_all only
        contrapose! h
        simp_all only [ne_eq]
        exact property
      · simp_all only [MeasurableSet.univ, Subtype.exists, mem_Icc, exists_prop, exists_eq_right, not_and, not_le]
  simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Subtype.coe_eta, MeasurableSet.univ, dite_eq_ite]
  convert h_meas_f_val
  simp_all only [iff_true]
  rwa [← this]

lemma embedding_coe_NNReal :  Topology.IsEmbedding (fun x:NNReal => (x:ℝ)) :=
by
  rw [Topology.isEmbedding_iff]
  apply And.intro
  · apply Topology.IsInducing.induced
  · exact Subtype.coe_injective

--本当は逆向きが証明に必要だった。こっちは使ってない。下に同様に証明した逆向きの補題がある。
lemma continuous_on_coe_NNReal {f : ℝ → NNReal} {s : Set ℝ}
    (hf : ContinuousOn (fun x ↦ (f x : ℝ)) s) :
    ContinuousOn f s := by
  rw [ContinuousOn]  -- ContinuousOn f s ↔ ∀ x ∈ s, ContinuousAt f x (𝓝[s] x)
  intro x hx
  rw [ContinuousWithinAt]  -- ContinuousAt f x (𝓝[s] x) ↔ Tendsto f (𝓝[s] x) (𝓝 (f x))
  intro V V_in
  simp
  obtain ⟨O, O_open⟩ := _root_.mem_nhds_iff.mp V_in
  rw [ContinuousOn] at hf
  specialize hf x hx  -- x ∈ s での連続性
  rw [ContinuousWithinAt] at hf
  dsimp [nhdsWithin]
  simp_all only [NNReal.tendsto_coe]
  obtain ⟨left, right⟩ := O_open
  obtain ⟨left_1, right⟩ := right
  apply hf
  simp_all only

--上の逆向きの補題。
lemma continuous_on_coe_NNReal2 {f : ℝ → NNReal} {s : Set ℝ}
    (hf : ContinuousOn f s ): ContinuousOn (fun x ↦ (f x : ℝ)) s:=
by
  dsimp [ContinuousOn]
  dsimp [ContinuousOn] at hf
  dsimp [ContinuousWithinAt]
  dsimp [ContinuousWithinAt] at hf
  intro x hx
  simp
  intro V V_in
  simp
  obtain ⟨O, O_open⟩ := _root_.mem_nhds_iff.mp V_in
  specialize hf x hx
  dsimp [nhdsWithin]
  dsimp [nhdsWithin] at hf
  obtain ⟨left, right⟩ := O_open
  obtain ⟨left_1, right⟩ := right
  apply hf
  simp_all only

------------------------------------------------------------------------
--def toFun (f : C₀) : (ℝ → ℝ) := fun x =>
--   if hx : x ∈ Ic then f.1 ⟨x, hx⟩ else 0
--関数の有界性を示す部分。未完だったが、MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompactを
--使えばいいことが判明して短くなった。
noncomputable def functionIntegrable (f : C₀) : MeasureTheory.Lp ℝ 2 (volume: Measure ℝ) :=
by
  have meas_f : Measurable (toFun f) := toFun_measurable f
  have ASf:AEStronglyMeasurable (toFun f) volume :=
  by
    --simp_all only [ContinuousMap.toFun_eq_coe, toFun]
    exact meas_f |>.aestronglyMeasurable
  let fₘ : ℝ →ₘ[volume] ℝ := AEEqFun.mk (toFun f) ASf

  --下のsimp_allで暗黙に使っている。
  have ASfm:AEStronglyMeasurable (fₘ) volume :=
  by
    simp_all only [ContinuousMap.toFun_eq_coe, toFun, fₘ]
    apply AEStronglyMeasurable.congr
    on_goal 2 => {rfl
    }
    · apply AEEqFun.aestronglyMeasurable
  /-こっちもなりたつが使ってないようなので、コメントアウト。
  have fcOn: ContinuousOn (toFun f) Ic:=
  by
    dsimp [toFun]
    rw [continuousOn_iff_continuous_restrict]
    unfold toFun
    simp_all only [ContinuousMap.toFun_eq_coe, restrict_dite, Subtype.coe_eta, fₘ]
    fun_prop
  -/

  let mti :=@MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact ℝ _ _ volume _ Ic hIc
  simp_all only [fₘ]
  apply Subtype.mk
  · apply ZeroMemClass.zero_mem

  --MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompactの定理を利用することで後ろの証明がいらなくなったかも。

  /- 定理の活用により、いらなくなった部分。一部未完だが、頑張れば埋まるかも。
    --∀ {α : Type u_1} {m0 : MeasurableSpace α} [inst : TopologicalSpace α] {μ : Measure α}   [self : IsFiniteMeasureOnCompacts μ] ⦃K : Set α⦄, IsCompact K → ↑↑μ K < ⊤

  have fₘ_in_L2 : Memℒp fₘ 2 volume :=
  by
    have :∃ M, ∀ x ∈ Icc 0 1, ‖toFun f x‖ ≤ M :=
      @IsCompact.exists_bound_of_continuousOn ℝ _ _ _ Ic hIc _ fcOn
    obtain ⟨M,hM⟩ := this

    -- `|toFun f x|^2` の上界を与える
    have bound : ∀ x ∈ Icc 0 1, ‖toFun f x‖^2 ≤ M^2 := by
      intro x hx
      simp [toFun]
      specialize hM x
      specialize hM hx
      split
      · dsimp [toFun] at hM
        dsimp [Ic] at hM
        simp_all
        apply sq_le_sq'
        · exact neg_le_of_abs_le hM
        ·
          obtain ⟨left, right⟩ := hx
          exact le_of_abs_le hM
      · simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, ↓reduceDIte, norm_zero, pow_nonneg, toFun]

    -- L²ノルムが有限であることを示す
    refine ⟨?_, ?_⟩
    · exact ASfm
    · --MeasureTheory.set_lintegral_lt_top_of_isCompactは、実数全体で連続でないと使えないので、この場合は適さない。
      have integral_bound :(∫ x in Icc (0:ℝ) 1, ‖toFun f x‖^2 ∂volume) ≤ (∫ x in Icc (0:ℝ) 1, M^2 ∂volume) := by
        apply MeasureTheory.integral_mono
        · show Integrable (fun a ↦ ‖toFun f a‖ ^ 2) (volume.restrict (Icc 0 1))
          dsimp [Integrable]
          constructor
          · show AEStronglyMeasurable (fun a ↦ |toFun f a| ^ 2) (volume.restrict (Icc 0 1))
            have :Measurable (fun a ↦toFun f a) :=
            by
              exact toFun_measurable f
            have :Measurable (fun a ↦|toFun f a|^2) :=
            by
              apply Measurable.pow
              · show Measurable fun x ↦ |toFun f x|
                exact Measurable.comp measurable_abs this
              · simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, sq_abs, dite_pow, ne_eq,
                OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, measurable_const, toFun, fₘ]
            simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, sq_abs, dite_pow, ne_eq,
              OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, toFun, fₘ]
            exact this.aestronglyMeasurable

          · show HasFiniteIntegral (fun a ↦ |toFun f a| ^ 2) (volume.restrict (Icc 0 1))
            let gg : ℝ → NNReal := fun x => Real.toNNReal (|toFun f x|^2)
            let g : ℝ → ℝ := fun x => (toFun f x) ^ 2
            have h1 : ContinuousOn (fun x => (toFun f x)) (Icc 0 1) := by
              simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, sq_abs, dite_pow, ne_eq,
                OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, toFun, fₘ]
              exact fcOn

            have h2 : ContinuousOn g (Icc 0 1) := by
              dsimp [g]
              apply ContinuousOn.pow
              exact h1

            have h3 : ∀ x ∈ Icc 0 1, 0 ≤ g x := by
              intro x hx
              dsimp [g]
              simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, sq_abs, dite_pow, ne_eq,
                OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, toFun, g, fₘ]
              obtain ⟨left, right⟩ := hx
              split
              next h_1 => positivity
              next h_1 => simp_all only [le_refl, g, toFun, fₘ]

            have h4 : ContinuousOn (fun x => (g x).toNNReal) (Icc 0 1) := by
              exact continuous_real_toNNReal.comp_continuousOn h2

            have :ContinuousOn (fun x ↦ (if hx : x ∈ Ic then (toFun f x) ^ 2 else 0).toNNReal) Ic := by

              refine ContinuousOn.congr h4 (fun x hx => ?_)
              simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, sq_abs, dite_pow, ne_eq,
                OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ↓reduceDIte, toFun, g, fₘ]

              -- `Icc 0 1` はコンパクト、測度は有限
            have measure_finite : volume Ic ≠ ⊤ := by exact IsCompact.measure_ne_top hIc

            have gg_cont': ContinuousOn (fun x => (gg x)) Ic :=
            by
              simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, sq_abs, dite_pow, ne_eq,
                OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ↓reduceDIte, toFun, fₘ, gg]
            have : ∀ x:Ic, (g x).toNNReal = gg x :=
            by
              intro x
              simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, sq_abs, dite_pow, ne_eq,
                OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ↓reduceDIte, Subtype.coe_prop, Subtype.coe_eta,
                toFun, g, fₘ, gg]
            have ggg_cont': ContinuousOn (fun x ↦ (gg x : ℝ)) Ic :=
            by
              exact (@continuous_on_coe_NNReal2 gg Ic gg_cont')

            --一生懸命にcontinuous_on_coe_NNRealを証明したのに役に立たなかった。
            ---ggg_cont'からgg_contでなくて、gg_contからggg_cont'という方向を証明する必要があった。
            --逆も証明することで証明がうまくいった。

            have integrable_on_Ic : IntegrableOn (fun x => (gg x : ℝ)) Ic volume := by
              apply @ContinuousOn.integrableOn_compact' ℝ ℝ _ _ _ (fun x => gg x) volume _ Ic _
              · exact isCompact_Icc  -- `Icc 0 1` はコンパクト
              · exact measurableSet_Icc  -- `Icc 0 1` は可測
              · exact ggg_cont'

            -- 定理を適用
            have lintegral_finite : ∫⁻ x in Ic, (gg x) ∂volume < ⊤ := by
              sorry --Integralbleであれば、有界だったはず。
              --MeasureTheory.IntegrableOn.set_lintegral_lt_topみたいなもの。

            dsimp [gg,Icc] at integrable_on_Ic
            show HasFiniteIntegral (fun a ↦ |toFun f a| ^ 2) (volume.restrict (Icc 0 1))
            dsimp [HasFiniteIntegral]
            dsimp [gg,Ic] at lintegral_finite
            show ∫⁻ (a : ℝ) in Icc 0 1, ‖|toFun f a| ^ 2‖ₑ < ⊤
            convert lintegral_finite
            rename_i h0 x
            show ‖|toFun f x| ^ 2‖ₑ = ↑(|toFun f x| ^ 2).toNNReal
            sorry --積分やnormに対して勉強してから再び取り組んだ方がいいかも。保留。

            --refine @MeasureTheory.setLIntegral_lt_top_of_isCompact _ _ _ _ Ic measure_finite isCompact_Icc gg

        · simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, sq_abs, dite_pow, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integrable_const, toFun, fₘ]
        · intro x
          show (fun a ↦ ‖toFun f a‖ ^ 2) x ≤ (fun a ↦ M ^ 2) x
          simp
          show toFun f x ^ 2 ≤ M ^ 2
          unfold toFun
          split
          · rename_i h0
            let bh :=bound x h0
            simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, ge_iff_le, toFun, fₘ]
            apply le_trans
            on_goal 2 => {exact bh
            }
            · simp_all only [ContinuousMap.toFun_eq_coe, ↓reduceDIte, norm_eq_abs, sq_abs, le_refl, toFun, fₘ]
          ·
            simp_all only [ContinuousMap.toFun_eq_coe, mem_Icc, norm_eq_abs, and_imp, sq_abs, dite_pow, ne_eq,
              OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, toFun, fₘ]
            positivity
      show eLpNorm (↑fₘ) 2 volume < ⊤
      -- ∫ (x : ℝ) in Icc 0 1, ‖toFun f x‖ ^ 2 ≤ ∫ (x : ℝ) in Icc 0 1, M ^ 2は、ここまでで示された。
      --haveで積分の値とゴールが等しいことを示すとよさそう。必要か不明。
      --have : eLpNorm (fₘ) 2 volume = (ENNReal.ofReal (∫ x in Icc (0:ℝ) 1, ‖toFun f x‖^2 ∂volume)) :=
      --by
      --  dsimp [fₘ]
      sorry --内側で、integralであることを示しているので、それを利用して証明できそう。
  --dsimp [eLpNorm]
  --#check Lp ℝ 2 volume

  have fLp:fₘ ∈ Lp ℝ 2 volume :=
  by
    exact Lp.mem_Lp_iff_memℒp.mpr fₘ_in_L2
  let F : MeasureTheory.Lp ℝ 2 volume := ⟨fₘ, fLp⟩
  exact F
  -/

lemma LP2norm {F G:Lp ℝ 2 (volume:Measure ℝ)}{f g : C₀} (h_f:F = functionIntegrable f) (h_g:G = functionIntegrable g):
 L2_distance_Ic f g = ‖F - G‖ :=
by
  dsimp [functionIntegrable] at h_f h_g
  dsimp [L2_distance_Ic]
  rw [h_f,h_g]

  simp [intervalIntegral, h_f, h_g]
  subst h_f h_g
  --show √(∫ (x : ↑Ic), (f x - g x) ^ 2) = ‖⟨AEEqFun.mk (toFun f) ⋯, ⋯⟩ - ⟨AEEqFun.mk (toFun g) ⋯, ⋯⟩‖
  --chatGPTによれば定義を展開していけば証明できるとのこと。
  sorry

--距離空間の公理を満たすためには、定義域を[0,1]に制限する必要がある。
noncomputable instance : MetricSpace C₀ where
  dist := by
   exact L2_distance_Ic

  dist_self f := by
    simp_all only
    simp [L2_distance_Ic]

  dist_comm f g := by
    simp [L2_distance_Ic]
    congr 1
    congr
    ext x : 1
    ring

  dist_triangle f g h := by
    set F := functionIntegrable f with h_F
    set G := functionIntegrable g with h_G
    set H := functionIntegrable h with h_H
    -- Lp.norm_sub_le （すなわち Minkowski の不等式）を適用できる
    -- 「L^2 ノルムの三角不等式」： ∥F - H∥ ≤ ∥F - G∥ + ∥G - H∥
    calc
      L2_distance_Ic f h
        = ‖F - H‖  -- L^2ノルムをそのまま書くと同じ
         := by
              exact LP2norm h_F h_H
      _ ≤ ‖F - G‖ + ‖G - H‖
      := by exact norm_sub_le_norm_sub_add_norm_sub F G H
      _ = L2_distance_Ic f g + L2_distance_Ic g h
      := by rw [LP2norm h_F h_G]
            rw [LP2norm h_G h_H]

  eq_of_dist_eq_zero := by
    intro f g hfg
    simp [L2_distance_Ic] at hfg

    dsimp [C₀]
    ext x
    show f.1 x = g.1 x
    --hfgのルートをとるのに必要な部分。
    have ps:∫ x in (Set.univ:Set Ic), (f.1 x - g.1 x) ^ 2 ≥ 0:=
    by
      have : (0 : ℝ) ≤ 1 :=
      by
        simp_all only [implies_true, Pi.sub_apply, Set.mem_Icc, ge_iff_le, and_imp, zero_le_one]
      have nonneg : ∀ (x : Ic),(f.1 x -g.1 x) ^ 2 ≥ 0 := by
        intro x
        positivity
      simp_all only [zero_le_one, ContinuousMap.toFun_eq_coe, ge_iff_le, Subtype.forall, Measure.restrict_univ]
      obtain ⟨val, property⟩ := x
      simp_all only [mem_Icc]
      obtain ⟨left, right⟩ := property
      positivity

    have ps2:(∫ x in (Set.univ:Set Ic), (f.1 x - g.1 x) ^ 2) = 0 :=
    by
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, ge_iff_le, sqrt_eq_zero, le_refl]

    have ps3:(∫ x in (Set.univ:Set Ic), ((f.1 - g.1) x) ^ 2) = 0 :=
    by
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, ge_iff_le, Pi.sub_apply]

    have h_integral_zero : ∫ x in (Set.univ:Set Ic), ((f.1 x - g.1 x) ^ 2) = 0 :=
    by
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, ge_iff_le, Pi.sub_apply]

    let diff := ContinuousMap.mk (λ x => f.1 x - g.1 x) (f.continuous_toFun.sub g.continuous_toFun)
    let cs := @continuous_sq_eq_zero_of_integral_zero_Ic (f-g) h_integral_zero
    have h_eq : ∀ x ∈ Set.Icc 0 1, diff.toFun x = 0 :=
    by
      intro x_1 a
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, ge_iff_le, Pi.sub_apply, mem_Icc, zero_le',
        true_and, ContinuousMap.coe_mk, sqrt_zero, le_refl, diff]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := x_1
      simp_all only [mem_Icc]
      obtain ⟨left, right⟩ := property
      apply cs
    specialize h_eq x
    have : x ∈ Set.Icc 0 1:=
    by
      simp_all only [Set.mem_Icc, zero_le', true_and, ContinuousMap.toFun_eq_coe]
      obtain ⟨val, property⟩ := x
      simpa using property.2
    specialize h_eq this
    simp_all only [Set.mem_Icc, zero_le', true_and, ContinuousMap.toFun_eq_coe]
    obtain ⟨val, property⟩ := x
    simp_all only [ge_iff_le, le_refl, Measure.restrict_univ, Pi.sub_apply, ContinuousMap.toFun_eq_coe,
      ContinuousMap.coe_mk, sqrt_zero, diff]
    exact sub_eq_zero.mp h_eq

------------------------------------------------------
----古いものや、証明に使ってないもの。保存しているものなど。
------------------------------------------------------

--これは頑張って証明した。現在は使ってないかも。OpenPosiの照明に使えるかもしれない。
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
      simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, δ]
      obtain ⟨left, right⟩ := hy
      apply lt_of_le_of_lt
      on_goal 2 => {exact left
      }
      ·
        simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, sub_nonneg, δ]
        rw [div_le_iff₀ ]
        simp_all only [inf_le_iff, le_mul_iff_one_le_right, Nat.one_le_ofNat, tsub_le_iff_right, true_or, or_true, δ]
        simp_all only [Nat.ofNat_pos, δ]

    ·
      simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, δ]
      obtain ⟨left, right⟩ := hy
      apply lt_of_lt_of_le
      exact right
      have :(ε ⊓ (x ⊓ (1 - x))) / 2 < 1-x:=
      by
        have :(1 - x)/2 < 1 -x :=
        by
          simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, half_lt_self_iff, δ]
        have :(ε /2 ⊓ (x /2 ⊓ (1 - x)/2 ))  < 1-x:=
        by
          simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, half_lt_self_iff,
            inf_lt_iff, or_true, δ]
        have :(ε /2 ⊓ (x /2 ⊓ (1 - x)/2 )) = (ε ⊓ (x ⊓ (1 - x))) / 2 :=
        by
          --simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, half_lt_self_iff, δ]
          --ring_nf
          rw [min_div_div_right]  -- `min (a / 2) (b / 2) = (min a b) / 2`
          rw [← min_assoc]
          rw [min_div_div_right]  -- `min (a / 2) (b / 2) = (min a b) / 2`
          simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, half_lt_self_iff,
            inf_lt_iff, or_true, δ]
          ac_rfl
          exact zero_le_two
          exact zero_le_two
        simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, half_lt_self_iff, δ]
      simp_all only [lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, ge_iff_le, δ]
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
        simp_all only [lt_sup_iff, true_or, δ]
      dsimp [δ]
      simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, δ]
      rw [div_lt_iff₀ (zero_lt_two' ℝ)]
      simp_all only [inf_lt_iff, lt_mul_iff_one_lt_right, Nat.one_lt_ofNat, true_or, or_true, δ]
    · suffices δ < 1 - x from by
        simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, δ]
        rw [abs]
        simp_all only [neg_sub, lt_sup_iff, or_true, δ]
      dsimp [Ioo] at hIoo_sub_Ioo01
      rw [@setOf_and] at hIoo_sub_Ioo01
      dsimp [δ]
      simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, δ]
      rw [div_lt_iff₀']
      simp_all only [inf_lt_iff, sub_pos, lt_mul_iff_one_lt_right, Nat.one_lt_ofNat, or_true, δ]
      simp_all only [sub_pos, lt_mul_iff_one_lt_left, Nat.one_lt_ofNat, or_true, δ]
      simp_all only [Nat.ofNat_pos, δ]

  · dsimp [Ioo] at hIoo_subU
    dsimp [Ioo] at hIoo_sub_Ioo01
    simp at hIoo_sub_Ioo01
    simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, δ]
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
            simp_all only [gt_iff_lt, sub_zero, lt_inf_iff, sub_pos, and_self, div_pos_iff_of_pos_left, Nat.ofNat_pos, δ]
            rw [div_lt_iff₀ (zero_lt_two' ℝ)]
            simp_all only [inf_lt_iff, lt_mul_iff_one_lt_right, Nat.one_lt_ofNat, true_or, or_true, δ]
        constructor
        ·
          simp_all only [sub_lt_self_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right, lt_inf_iff,
            sub_pos, true_and, gt_iff_lt, δ]
          obtain ⟨left_1, right_1⟩ := hδ_pos
          linarith
        · linarith
      simp_all only [mem_setOf_eq, δ]
      simp_all only [sub_lt_self_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right, lt_inf_iff,
        sub_pos, true_and, δ]
      obtain ⟨left_1, right_1⟩ := hδ_pos
      obtain ⟨left_2, right_2⟩ := this
      exact hIoo_subU ⟨left_2, right_2⟩
    · dsimp [Ioo]
      dsimp [Icc]
      intro y hy
      simp
      constructor
      · simp at hy
        simp_all only [sub_lt_self_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right, lt_inf_iff,
          sub_pos, true_and, δ]
        obtain ⟨left, right⟩ := hδ_pos
        obtain ⟨left_1, right_1⟩ := hy
        apply le_of_lt
        simp_all only [δ]
      ·
        simp_all only [sub_lt_self_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right, lt_inf_iff,
          sub_pos, true_and, mem_setOf_eq, δ]
        obtain ⟨left, right⟩ := hδ_pos
        obtain ⟨left_1, right_1⟩ := hy
        apply le_of_lt
        simp_all only [δ]

--IcにOpenPosのインスタンスを設定する部分。
--このままだとopen_posに証明不可能な言明が出てくる。Uが01の範囲外だとゴールが成り立たない。
--atをつかって回避。でも証明は未完。
--Icのtopologyは、相対位相が導入済み。測度も誘導された測度。
--import Mathlib.Topology.Instances.Real
--import Mathlib.MeasureTheory.Measure.Space
--import Mathlib.MeasureTheory.Measure.OpenPos
--import Mathlib.Topology.SubsetProperties

--open Set Filter Topology MeasureTheory

--noncomputable def Ic : Set ℝ := Set.Icc (0 : ℝ) 1

/--
「Ic 上の開集合が非空ならば測度が正」という補題。

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
  -- ただし mathlib には isOpen_subtype などの補題があるので使い方に合わせて調整
  -- あるいは exists_open_subtype なども利用可能
  -- ここでは単に「∃ V (ℝ の上で開), U = V ∩ Ic」という事実を指す
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
    -- measureSpace の実装上 (Measure.subtype.measureSpace Ic) は
    -- 実数上の Lebesgue measure を Ic に restrict したものと同じ
    -- 従って I の測度は (x.1 - ε, x.1 + ε) ∩ [0,1] の実際の長さに等しく正
    -- 正確には measure.restrict_eq_self や Ioc/Icc/Ioo の measure 計算などで示す
    -- 以下はスケッチ
    suffices volume.restrict Ic I = volume I by
      -- 上記 = volume I > 0 を示せば良い
      rw [this]
      -- I を具体的区間 Ioo(...) に書き換えてその measure が正であることを示す
      let a := max (x.1 - ε) 0
      let b := min (x.1 + ε) 1
      have a_lt_b : a < b := by
        -- a = max(0, x-ε), b = min(1, x+ε)
        -- x は [0,1], ε>0
        -- 大雑把に 0 ≤ x ≤ 1 ⇒ x-ε ≤ x+ε ⇒ かつ端点考慮しても max(...) < min(...) が成立
        -- 詳細には場合分けなしでも linarith などで示せることが多いです
        -- ここでは手作業で不等式を確認するか linarith する
        have : x - ε < x + ε := by linarith
        -- max(0, x-ε) ≤ x+ε,  min(1, x+ε) ≥ x-ε など
        -- さらに x ∈ [0,1] で ε>0 なのでしっかりと正の幅が出る
        -- 以下は簡易に:
        --   0 ≤ x ≤ 1 ⇒ x+ε > 0 ⇒ min(1, x+ε) > max(0, x-ε)
        --   なぜなら x-ε < x+ε, 0 ≤ x+ε, などを合わせると
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
        simp_all only [gt_iff_lt, ge_iff_le, a, b, I]
        linarith
        simp_all only [gt_iff_lt, ge_iff_le, zero_lt_one, a, b, I]
      have Ioo_ab_subset : Ioo a b ⊆ I := by
    -- 厳密には、これは成り立たない。|y-x| = εのケースが問題。
    --「閉球 vs 開球」で端点をどう扱うかは measure 0 の問題なので
    -- 下記では「|y - x| ≤ ε ⇒ y ∈ ball x ε」とは厳密には違うが
    -- 一般に (closed_ball x ε) \ (ball x ε) は端点のみ (measure 0)
    -- という事実で吸収可能です。
    -- もしくは「実際に a < y < b を示し |y-x| < ε をチェック」としてもOK。
        intro y hy
        obtain ⟨y_ge_a, y_le_b⟩ := hy
        -- y ≥ a = max(0,x-ε) ⇒ y ≥ 0, y ≥ x-ε
        -- y ≤ b = min(1,x+ε) ⇒ y ≤ 1, y ≤ x+ε
        dsimp [I]
        simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
          sup_lt_iff, zero_lt_one, and_true, mem_Icc, a, b, I]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := hVU
        obtain ⟨left_1, right_1⟩ := a_lt_b
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
        /-
        have h0 : 0 ≤ y := by

        have h1 : y ≤ 1 := by
          simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
            sup_lt_iff, zero_lt_one, and_true, sup_le_iff, tsub_le_iff_right, le_inf_iff, a, b, I]
        have h_ball' : |y - x| ≤ ε := by  --等号を外すと成り立たない。
          have : x - ε ≤ y ∧ y ≤ x + ε := by
            constructor
            · simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
              sup_lt_iff, zero_lt_one, and_true, sup_le_iff, tsub_le_iff_right, le_inf_iff, a, b, I]
            · simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
              sup_lt_iff, zero_lt_one, and_true, sup_le_iff, tsub_le_iff_right, le_inf_iff, a, b, I]
          -- これで x - ε ≤ y ≤ x+ε ⇒ |y-x| ≤ ε
          rw [abs_le]
          simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
            sup_lt_iff, zero_lt_one, and_true, sup_le_iff, le_inf_iff, tsub_le_iff_right, neg_le_sub_iff_le_add,
            true_and, a, b, I]
          obtain ⟨val, property⟩ := x
          obtain ⟨left, right⟩ := hVU
          subst right
          linarith
        -- y がちょうど端点 x±ε の場合には `|y-x| = ε` となり "ball x ε" ではなく "closed_ball x ε"。
        -- しかし measure の観点では端点差は 0 なので包含（up to measure 0）。
        -- いちおう「subset でなく ⊆ᵐ (almost everywhere)」とするか、
        --   measure(I \ (Icc a b)) = 0
        -- のように述べてもOK。
        -- ここでは簡潔に「ball と closed_ball の違いは measure 0 なので吸収」とするか、
        --   'if h_ball < ε then done else boundary is measure zero'
        --   としてまとめる。
        refine mem_inter ?_ ?_
        · -- y ∈ ball x ε up to measure zero
          -- if h_ball < ε then trivially. if h_ball = ε then boundary...
          -- measure 的には問題なし
          -- Lean 上で厳密に "y ∈ ball x ε" を示すなら "h_ball < ε" が必要
          -- しかし h_ball = ε のとき strict < にはならない
          -- measure 0 という事実に頼るか,
          --   or we can define a slightly smaller radius (ε/2) to do the containment
          --   but that changes the length
          -- → typical measure-theoretic approach: "almost everything"
          -- ここでは 'subset' を使いたいなら,
          --   alternative: y - x < ε or x - y < ε => strictly
          --   we can do (ball x (ε - δ)) for small δ>0
          -- "strictly" でなくても measure(Icc a b) ≤ measure( ball x ε )
          show y ∈ ball (↑x) ε
          dsimp [ball]
          dsimp [dist]
          sorry
        · -- y ∈ [0,1]
          exact ⟨h0, h1⟩
      -/
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
          simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
            sup_lt_iff, zero_lt_one, and_true, subset_inter_iff, setOf_subset_setOf, and_imp, mem_setOf_eq,
            not_true_eq_false, a, I', b, y, I, b', a']

      have Icc_ab_subset : I' ⊆ I := by
        intro y hy
        have : y ∈ Ioo a b := by
          exact sub'.1 hy
        exact Ioo_ab_subset this

      /-


    -- 厳密には、これは成り立たない。|y-x| = εのケースが問題。
    --「閉球 vs 開球」で端点をどう扱うかは measure 0 の問題なので
    -- 下記では「|y - x| ≤ ε ⇒ y ∈ ball x ε」とは厳密には違うが
    -- 一般に (closed_ball x ε) \ (ball x ε) は端点のみ (measure 0)
    -- という事実で吸収可能です。
    -- もしくは「実際に a < y < b を示し |y-x| < ε をチェック」としてもOK。
        intro y hy
        obtain ⟨y_ge_a, y_le_b⟩ := hy
        -- y ≥ a = max(0,x-ε) ⇒ y ≥ 0, y ≥ x-ε
        -- y ≤ b = min(1,x+ε) ⇒ y ≤ 1, y ≤ x+ε
        dsimp [I]
        have h0 : 0 ≤ y := by
          simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
            sup_lt_iff, zero_lt_one, and_true, sup_le_iff, tsub_le_iff_right, le_inf_iff, a, b, I]
        have h1 : y ≤ 1 := by
          simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
            sup_lt_iff, zero_lt_one, and_true, sup_le_iff, tsub_le_iff_right, le_inf_iff, a, b, I]
        have h_ball' : |y - x| ≤ ε := by  --等号を外すと成り立たない。
          have : x - ε ≤ y ∧ y ≤ x + ε := by
            constructor
            · simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
              sup_lt_iff, zero_lt_one, and_true, sup_le_iff, tsub_le_iff_right, le_inf_iff, a, b, I]
            · simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
              sup_lt_iff, zero_lt_one, and_true, sup_le_iff, tsub_le_iff_right, le_inf_iff, a, b, I]
          -- これで x - ε ≤ y ≤ x+ε ⇒ |y-x| ≤ ε
          rw [abs_le]
          simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, lt_inf_iff,
            sup_lt_iff, zero_lt_one, and_true, sup_le_iff, le_inf_iff, tsub_le_iff_right, neg_le_sub_iff_le_add,
            true_and, a, b, I]
          obtain ⟨val, property⟩ := x
          obtain ⟨left, right⟩ := hVU
          subst right
          linarith
        -- y がちょうど端点 x±ε の場合には `|y-x| = ε` となり "ball x ε" ではなく "closed_ball x ε"。
        -- しかし measure の観点では端点差は 0 なので包含（up to measure 0）。
        -- いちおう「subset でなく ⊆ᵐ (almost everywhere)」とするか、
        --   measure(I \ (Icc a b)) = 0
        -- のように述べてもOK。
        -- ここでは簡潔に「ball と closed_ball の違いは measure 0 なので吸収」とするか、
        --   'if h_ball < ε then done else boundary is measure zero'
        --   としてまとめる。
        refine mem_inter ?_ ?_
        · -- y ∈ ball x ε up to measure zero
          -- if h_ball < ε then trivially. if h_ball = ε then boundary...
          -- measure 的には問題なし
          -- Lean 上で厳密に "y ∈ ball x ε" を示すなら "h_ball < ε" が必要
          -- しかし h_ball = ε のとき strict < にはならない
          -- measure 0 という事実に頼るか,
          --   or we can define a slightly smaller radius (ε/2) to do the containment
          --   but that changes the length
          -- → typical measure-theoretic approach: "almost everything"
          -- ここでは 'subset' を使いたいなら,
          --   alternative: y - x < ε or x - y < ε => strictly
          --   we can do (ball x (ε - δ)) for small δ>0
          -- "strictly" でなくても measure(Icc a b) ≤ measure( ball x ε )
          show y ∈ ball (↑x) ε
          dsimp [ball]
          dsimp [dist]
          sorry
        · -- y ∈ [0,1]
          exact ⟨h0, h1⟩
      -/
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
      exact gt_of_ge_of_gt I_le_I measure_Icc_ab

      /- grokに提案されたもの。本質的に同じだと思われるので、上のo1のものと未解決の部分を比べてみる。
      suffices (Measure.restrict volume (Icc 0 1)) I = volume I from by
      -- I は (Icc 0 1) の部分集合
      simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, measurableSet_Icc,
        Measure.restrict_apply']
      obtain ⟨val, property⟩ := x
      obtain ⟨left, right⟩ := hVU
      subst right
      simp_all only [mem_preimage, Subtype.image_preimage_coe, subset_inter_iff]
      obtain ⟨left_1, right⟩ := I_subset_U
      have hI_eq : I = Ioo (max (val - ε) 0) (min (val + ε) 1) := by
        ext y
        simp only [mem_inter_iff, mem_ball, mem_Icc, mem_Ioo, Real.dist_eq]
        constructor
        · intro ⟨h_dist, h_Ic⟩
          constructor
          · apply max_lt
            · exact sub_lt_of_abs_sub_lt_left h_dist
            · sorry
          · apply lt_min
            · sorry
            · sorry
        · intro ⟨h_left, h_right⟩
          constructor
          · simp only [Real.dist_eq]
            have h1 : val - ε < y := (max_lt_iff.mp h_left).1
            have h2 : y < val + ε := by simp_all only [sup_lt_iff, true_and, lt_inf_iff]
            sorry
          ·
            simp_all only [sup_lt_iff, lt_inf_iff, mem_Icc]
            obtain ⟨left_2, right_1⟩ := h_left
            obtain ⟨left_3, right_2⟩ := h_right
            apply And.intro
            · positivity
            · linarith

      rw [hI_eq]
      have hI_pos : 0 < volume (Ioo (max (val - ε) 0) (min (val + ε) 1)) :=
        -- Define the positivity condition of the interval length:
        have h_length_pos : max (val - ε) 0 < min (val + ε) 1 :=
          by
            have h_left : max (val - ε) 0 ≤ val :=
              by
                apply max_le
                simp_all only [mem_inter_iff, mem_ball, dist_self, mem_Icc, true_and, tsub_le_iff_right,
                  le_add_iff_nonneg_right, volume_Ioo, I]
                obtain ⟨left_2, right_1⟩ := xInI
                positivity
                exact property.1
            have h_right : val ≤ min (val + ε) 1 :=
              by
                apply le_min
                simp_all only [mem_inter_iff, mem_ball, dist_self, mem_Icc, true_and, sup_le_iff, tsub_le_iff_right,
                  le_add_iff_nonneg_right, and_true, I]
                simp_all only [mem_inter_iff, mem_ball, dist_self, mem_Icc, true_and, sup_le_iff, tsub_le_iff_right,
                  le_add_iff_nonneg_right, and_true, I]
            apply lt_of_le_of_lt h_left
            sorry
        (MeasureTheory.Measure.measure_Ioo_pos volume).mpr h_length_pos
      sorry
      -/
    apply MeasureTheory.Measure.restrict_eq_self volume
    simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, inter_subset_right, I]
      --apply MeasureTheory.Measure.measure_pos_of_nonempty_interior
      --εpos : ε > 0
      --ball val ε ∩ Icc 0 1 ⊆ V
      --volume (ball val ε ∩ Icc 0 1 ∩ Icc 0 1) = volume (ball val ε ∩ Icc 0 1)
      --exact ⟨x.1, xInI⟩
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
      --have : U ⊆ Ic := fun u hu => u.2  -- U は Ic 上の集合なので, その carrier は常に Ic
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
      let mr := measure_restrict_eq_measure measSU h_sub
      rw [←mr]
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
      simp_all only [gt_iff_lt, mem_inter_iff, mem_ball, dist_self, Subtype.coe_prop, and_self, le_refl, I, mr]

-- 以上の補題を使って IsOpenPosMeasure を与える
noncomputable instance : MeasureTheory.Measure.IsOpenPosMeasure (volume:Measure Ic) where
  open_pos := fun U hU hne =>
  by
    let os := openSubspace_nonempty_measure_pos U hU hne
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp [a] at os



/-
instance : @MeasureTheory.Measure.IsOpenPosMeasure Ic _ _ (MeasureTheory.MeasureSpace.volume.restrict (Set.univ:Set Ic)) where
  open_pos := fun U hU hU_nonempty =>
  by

    obtain ⟨x, hxU⟩ := hU_nonempty
    simp_all only [Measure.restrict_univ, ne_eq]
    --obtain ⟨val, property⟩ := x
    apply Aesop.BuiltinRules.not_intro
    obtain ⟨V, hV_subU, hV_open, hxV⟩ := isOpen_iff_forall_mem_open.mp hU x hxU
    obtain ⟨ε, hε_pos, h_ball_subV⟩ := Metric.isOpen_iff.mp hV_open x hxV
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
    have IIc: Ioo (x - ε) (x + ε) ⊆ Ic :=
    by
      dsimp [Ioo]
      dsimp [Ic]
      dsimp [Icc]
      intro y hy
      simp
      simp at hy
      simp [Ioo] at hIoo_sub_ball
      have : {x_1 | ↑x - ε < x_1 ∧ x_1 < ↑x + ε} ⊆ V:=
      by
        intro xx hxx
        simp at hxx
        obtain ⟨left, right⟩ := hxx
        dsimp [Set.image]
        have:xx∈ Ic:=
        by
          simp_all only [gt_iff_lt]
          obtain ⟨val, property⟩ := x
          obtain ⟨left_1, right_1⟩ := hy
          simp_all only
          dsimp [Ic]
          dsimp [Icc]
          constructor
          · sorry
          · sorry --subtypeとそうでないのと混じっていて難しい。
        use ⟨xx,this⟩
        simp_all only [gt_iff_lt, and_true]
        obtain ⟨val, property⟩ := x
        obtain ⟨left_1, right_1⟩ := hy
        simp_all only
        apply h_ball_subV
        simp_all only [mem_ball]
        apply hIoo_sub_ball
        simp_all only [mem_setOf_eq, and_self]
      sorry

    have hIoo_sub_ball_sub : (Ioo (x - ε) (x + ε)).image (fun x=> x∈ Ic) ⊆ (ball x ε).image (fun x=> x∈ Ic) :=
    by
      simp_all only [gt_iff_lt, const_apply, image_subset_iff]
      obtain ⟨val, property⟩ := x
      simp_all only
      intro x hx
      simp_all only [mem_Ioo, mem_preimage, mem_image, mem_ball, Subtype.exists, exists_and_right, exists_eq_right,
        eq_iff_iff]
      obtain ⟨left, right⟩ := hx
      apply Exists.intro
      · apply And.intro
        on_goal 2 => apply Iff.intro
        on_goal 3 => {
          intro a
          apply property
        }
        · simp_all only [dist_self, exists_const]
        · intro a
          simp_all only
          apply IIc
          simp_all only [mem_Ioo, and_self]

    have : MeasureTheory.MeasureSpace.volume.restrict univ (Ioo (x - ε) (x + ε)) > 0:=
    by
      simp_all only [gt_iff_lt, volume_Ioo, add_sub_sub_cancel, ofReal_pos, pos_add_self_iff]
      simp_all only [Measure.restrict_univ, volume_Ioo, add_sub_sub_cancel, ofReal_pos, pos_add_self_iff]

    have : MeasureTheory.MeasureSpace.volume.restrict univ (ball x ε) > 0:=
    by
      apply lt_of_lt_of_le this
      --let mm:= @MeasureTheory.Measure.restrict_mono Ic _  (coe⁻¹' (Ioo (x - ε) (x + ε))) hIoo_sub_ball_sub _
      sorry
    sorry

--全実数での定理。参考までに残す。
theorem continuous_eq_zero_of_ae_eq_zero {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ᵐ x ∂volume, f x = 0) :
  ∀ x, f x = 0 := by
  -- `g(x) = 0` と定義し、`f` と `g` がほとんど至る所等しいことを利用する
  have h_eq : f =ᶠ[ae MeasureTheory.MeasureSpace.volume] 0 := h
  -- `MeasureTheory.Measure.eq_of_ae_eq` 定理を適用する
  let  mt := MeasureTheory.Measure.eq_of_ae_eq h_eq hf continuous_const
  exact fun x ↦ congrFun mt x

lemma real_isOpenPosMeasure : MeasureTheory.Measure.IsOpenPosMeasure (volume : Measure ℝ) :=
  by
    refine ⟨λ U hU hne => ?_⟩

    obtain ⟨x, hxU⟩ := hne
    sorry
-/

--MeasureTheory.Measure.IsOpenPosMeasureを適用すればよいと思って作ったが、
--OpenPosMeasureのインスタンスを設定しないといけなくて、大変。

------OpenPosはここまで。
-----------------
/- locallyFiniteMeasureのInstanceを設定するこころみ。いろいろうまくいかなくて、完成しそうにないので断念。
--IsFiniteMeasureOnCompactsのinstanceの設定に必要だったが、そっちも断念。
--つまり、設定できれば三角不等式のところの測度の有界性の証明に用いることができる。
example {lnum rnum : ℝ} (Hlin : lnum ∈ Ic) (Hrin : rnum ∈ Ic) {x : ℝ}
  (hx : x ∈ Ioo lnum rnum) :
  Ioo lnum rnum ∈ nhds x :=
isOpen_Ioo.mem_nhds hx

noncomputable instance : IsLocallyFiniteMeasure (volume : Measure Ic) where
  finiteAtNhds := fun x =>
    let ε : ℝ := 1
    have hε : 0 < ε := zero_lt_one
    have hU : Ioo (x.val - ε) (x.val + ε) ⊆ Set.univ := subset_univ _
    ⟨Ioo (x.val - ε) (x.val + ε), isOpen_Ioo, measure_Icc_lt_top (x.val - ε) (x.val + ε)⟩

noncomputable instance : IsLocallyFiniteMeasure (volume : Measure Ic) where
  finiteAtNhds := fun x =>
    let ε := 1
    have hε : 0 < ε := zero_lt_one
    let lnum := max (x.val - ε) 0
    let rnum := min (x.val + ε) 1
    have lr0: (x.val - ε) < (x.val + ε) := by
      simp_all only [Nat.lt_one_iff, pos_of_gt, Nat.cast_one, ε]
      obtain ⟨val, property⟩ := x
      simp_all only
      linarith
    have lr1: 0 < 1 := by
      trivial
    have lr: lnum ≤ rnum := by
      simp_all only [Nat.cast_one, Nat.lt_one_iff, pos_of_gt, le_inf_iff, sup_le_iff, tsub_le_iff_right, zero_le_one,
        and_true, ε, lnum, rnum]
      obtain ⟨val, property⟩ := x
      simp_all only
      dsimp [Ic] at property
      dsimp [Icc] at property
      obtain ⟨left, right⟩ := property
      apply And.intro
      · apply And.intro
        · linarith
        · positivity
      · linarith

    have hU : Icc lnum rnum ⊆ (Set.univ:Set Ic) :=
    by
      simp_all only [Nat.lt_one_iff, pos_of_gt, Nat.cast_one, image_univ, Subtype.range_coe_subtype, setOf_mem_eq, ε,
        lnum, rnum]
      obtain ⟨val, property⟩ := x
      simp_all only
      apply Icc_subset_Icc
      · simp_all only [le_sup_right]
      · simp_all only [inf_le_right]
    have lin : lnum ∈ Ic :=
    by
      simp_all only [Nat.lt_one_iff, pos_of_gt, Nat.cast_one, image_univ, Subtype.range_coe_subtype, setOf_mem_eq, ε,
        lnum]
      obtain ⟨val, property⟩ := x
      simp_all only
      apply hU
      simp_all only [mem_Icc, le_refl, tsub_le_iff_right, true_and]
    have rin : rnum ∈ Ic :=
    by
      simp_all only [Nat.cast_one, Nat.lt_one_iff, pos_of_gt, le_inf_iff, sup_le_iff, tsub_le_iff_right, zero_le_one,
        and_true, image_univ, Subtype.range_coe_subtype, setOf_mem_eq, ε, lnum, rnum]
      obtain ⟨val, property⟩ := x
      obtain ⟨left, right⟩ := lr
      obtain ⟨left, right_1⟩ := left
      simp_all only [ε]
      apply hU
      simp_all only [mem_Icc, le_inf_iff, sup_le_iff, tsub_le_iff_right, and_self, zero_le_one, le_refl, ε]
  have arg2:Ioo ⟨lnum, lin⟩ ⟨rnum, rin⟩ ∈ nhds x  :=
  by
    simp_all only [Nat.cast_one, Nat.lt_one_iff, pos_of_gt, le_inf_iff, sup_le_iff, tsub_le_iff_right, zero_le_one,
      and_true, image_univ, Subtype.range_coe_subtype, setOf_mem_eq, ε, lnum, rnum]
    obtain ⟨val, property⟩ := x
    obtain ⟨left, right⟩ := lr
    obtain ⟨left, right_1⟩ := left
    simp_all only [ε]
    by_cases val = 0
    case pos h =>
      simp_all
      dsimp [Ioo]
      subst h
      simp_all only [Nat.cast_one, zero_sub, Left.neg_nonpos_iff, zero_le_one, sup_of_le_right, zero_add, le_refl,
        inf_of_le_left, ε, lnum, rnum]
      show {x : Ic | 0 < (x : ℝ) ∧ (x : ℝ) < 1} ∈ nhds (⟨0, by simp_all only [lnum, ε, rnum]⟩ : Ic)
      simp_all only [Icc.mk_zero, unitInterval.coe_pos, unitInterval.coe_lt_one, lnum, ε, rnum]
      --apply isOpen_Ioo.mem_nhds
      sorry
      --たぶんなりたたない。

    case neg =>
      apply isOpen_Ioo.mem_nhds
      dsimp [Ioo]
      constructor
      · simp
        dsimp [Ic] at property
        dsimp [Icc] at property
        sorry


    --hxFilter.mem_nhds_iff.mpr ⟨Ioo ⟨lnum, lin⟩ ⟨rnum, rin⟩, isOpen_Ioo, hx, Subset.rfl⟩

  ⟨(Ioo ⟨lnum,lin⟩ ⟨rnum,rin⟩),
      arg2,
      measure_Icc_lt_top (x.val - ε) (x.val + ε)⟩
-/

--IcのvolumeにIsFiniteMeasureOnCompactsを設定する試み。
--Integrableのインスタンスを設定するために必要だったが、うまくいってない。
--全体の証明を完成させる上では、これを証明してもいいし、直接証明する方法もあるが、同じようなことを証明する必要。

------------ここからIcでない古いバージョン---------
--これは実数全体に拡張する方向。廃止の方針。
noncomputable def extend_f (f : C₀) : ℝ → ℝ := Function.extend Subtype.val f.1 0
noncomputable def extend_f2 (f : C₀) : ℝ → ℝ := Function.extend (Subtype.val : Ic → ℝ) (λ x => (f.1 x)^2) 0


/-- \(\displaystyle L^2\) 距離を連続関数上で定義する． -/
noncomputable def L2_distance (f g : C₀) : ℝ :=
  Real.sqrt (∫ x in Set.Icc (0 : ℝ) 1, (extend_f f x - extend_f g x) ^ 2)

/-
任意の連続関数 `f` が非負かつ積分が 0 のとき，`f` が恒等的に 0 となることを示す補題．
この補題は Lean 4 で標準的に存在しないため，自前で証明する．
-/

--積分の変数は、Icでなくて、Rである必要がある。しかし、fの引数は、Icである必要がある。
--xがRの要素であるが、Icの範囲に入っていることをLean 4に伝えられないので、extend_fで回避。
/-lemma continuous_nonneg_eq_zero_of_integral_zero {f : C₀} (hf_nonneg : ∀ x, 0 ≤ f.1 x)
    (hf_int_zero : ∫ x in (Set.Icc 0 1), (extend_f f) x = 0):
    ∀ x ∈ Set.Icc 0 1, f.1 x = 0 :=
by
  sorry -- なにかMathlib 4の定理を使えないか。ChatGPTに提案してもらった証明はうまりそうになかった。

\(\int_0^1 (f x)^2 dx = 0\) のとき，\(f\) は `[0,1]` 上恒等的に 0 であることを示す．
Mathlib 3 の `Continuous.ae_eq_zero_of_integral_eq_zero` 相当の議論を
`continuous_nonneg_eq_zero_of_integral_zero` を使って置き換える．
-/
/-
  --こっちは2乗の値が0だったから関数が0になるというもの。extend版。
lemma continuous_sq_eq_zero_of_integral_zero {f : C₀}
    --(hf_cont : ContinuousOn f (Set.Icc 0 1))
    (h : (∫ x in Set.Icc (0 : ℝ) 1, extend_f2 f x) = 0) :
    ∀ x ∈ Set.Icc 0 1, f.1 x = 0 := by
  -- (f x) ^ 2 は常に非負
  have hf_nonneg : ∀ x, 0 ≤ (f.1 x) ^ 2 := by
    intro x
    exact pow_two_nonneg (f.1 x)
  -- 積分が 0 なので、(f x) ^ 2 = 0
  have hf_eq_zero : ∀ x ∈ Set.Icc 0 1, (f.1 x) ^ 2 = 0 := by
    have hf_sq_cont : ContinuousOn (fun x => (f.1 x) ^ 2) (Set.Icc 0 1) := by
      simp_all
      fun_prop
    show ∀ x ∈ Set.Icc 0 1, f.toFun x ^ 2 = 0
    let f2 := fun x => f.toFun x ^ 2
    let f2c := ContinuousMap.mk (fun (x:Ic) => (f.1 x) ^ 2) (@q2c f)
    have f2inC : Continuous f2:=
    by
      simp_all [f2]
      fun_prop

    have : ∀ x, f2 x ≥ 0 :=
    by
      intro x
      simp_all [f2]
      obtain ⟨val, property⟩ := x
      positivity
    have :∀ (x : ↑(Set.Icc 0 1)), 0 ≤ (⟨f2,f2inC⟩ : C₀).toFun x :=
    by
      intro x
      dsimp [f2]
      obtain ⟨val, property⟩ := x
      positivity

    let cne := continuous_nonneg_eq_zero_of_integral_zero this
    simp at cne
    intro x hx
    --rw [←mul_self_eq_zero]
    have : ∫ (x : ℝ) in Set.Icc 0 1, extend_f2 f x = 0 ↔ ∫ (x : ℝ) in Set.Icc 0 1, extend_f { toFun := f2, continuous_toFun := f2inC } x = 0 :=
    by
      apply Iff.intro
      · dsimp [extend_f]
        dsimp [extend_f2]
        dsimp [f2]
        /- have : ∀ (x : ℝ), Function.extend (Subtype.val : Ic → ℝ) ((f.1) ^ 2) (fun _ => 0) x = Function.extend (Subtype.val : Ic → ℝ) (fun x => (f.1 x) ^ 2) (fun _ => 0) x := by intro x simp exact rfl -/
        intro hh
        simp at this
        exact h

      · intro h
        dsimp [extend_f2]
        dsimp [f2] at h
        simp at h
        dsimp [extend_f] at h
        exact h

    rw [this] at h
    specialize cne h
    simp
    dsimp [f2] at cne
    specialize cne x hx
    have : (x : ℝ) ≤ 1 := by
      obtain ⟨val, property⟩ := x
      simpa using property.2
    specialize cne this
    simp at cne
    exact cne

  -- (f x) ^ 2 = 0 ならば f x = 0
  intro x hx
  specialize hf_eq_zero x hx
  exact pow_eq_zero hf_eq_zero

  /-Icでない版の記録
  noncomputable instance : MetricSpace C₀ where
  dist := by
   exact L2_distance

  dist_self f := by
    simp_all only
    simp [L2_distance]
    -- (f x - f x)^2 = 0 の積分
    --have : ∫ x in Set.Icc 0 1, (f x - f x) ^ 2 = ∫ x in Set.Icc 0 1, (0 : ℝ) := by simp
    --rw [this, integral_zero, Real.sqrt_zero]

  dist_comm f g := by
    simp [L2_distance]
    congr 1
    --funext x
    --exact sq_diff_comm (f x) (g x)
    congr
    ext x : 1
    ring

  dist_triangle f g h := by
    -- 本来は (f - h)^2 <= (f - g + g - h)^2 を用いて Minkowski の不等式を示す必要がある
    -- ここでは省略し、sorry で示す.
    --intro
    simp [L2_distance]
    show √(∫ (x : ℝ) in Set.Icc 0 1, (extend_f f x - extend_f h x) ^ 2) ≤
  √(∫ (x : ℝ) in Set.Icc 0 1, (extend_f f x - extend_f g x) ^ 2) +
    √(∫ (x : ℝ) in Set.Icc 0 1, (extend_f g x - extend_f h x) ^ 2)
    dsimp [extend_f]
    dsimp [Function.extend]
    simp
    --ただでさえ難しいのにextendのせいでより難しくなっている。
    sorry


  eq_of_dist_eq_zero := by
    intro f g hfg
    simp [L2_distance] at hfg

    --使っている。
    have exf: (extend_f (f-g))^2 = extend_f2 (f-g) :=
    by
      dsimp [extend_f]
      dsimp [extend_f2]
      ext x : 1
      --showをいれたことで証明がうまくいった。なぜ？
      show (Function.extend Subtype.val ((f - g).1) 0 ^ 2) x = Function.extend Subtype.val (fun x ↦ ((f - g).1 x ^ 2)) 0 x
      simp [Function.extend]

    have exf':  ∀ x,  (extend_f (f-g) x)^2  = extend_f2 (f-g) x:=
    by
      intro x
      exact Eq.symm (ext_cauchy (congrArg cauchy (congrFun (id (Eq.symm exf)) x)))

    --使っている。
    have exf2: (extend_f (f-g)) = (extend_f f - extend_f g) :=
    by
      dsimp [extend_f]
      --simp
      funext
      dsimp [Function.extend]
      simp
      split
      next h =>
        obtain ⟨left, right⟩ := h
        rfl
      next h => simp_all only [not_and, not_le, sub_self]

    have exf2': ∀ x, (extend_f (f-g)) x = (extend_f f x - extend_f g x):=
    by
      intro x
      simp_all only [Pi.sub_apply]


    have exf3: ∀ x, (extend_f f x - extend_f g x) ^ 2 = (extend_f2 (f - g)) x :=
    by
      intro x
      --dsimp [extend_f,extend_f2]
      rw [← exf2']
      rw [←exf' x]

    dsimp [C₀]
    ext x
    show f.1 x = g.1 x
    --hfgのルートをとるのに必要な部分。
    have ps:∫ (x : ℝ) in Set.Icc 0 1, (extend_f f x - extend_f g x) ^ 2 ≥ 0:=
    by
      have nonneg: ∀ (x : ℝ), x ∈ Set.Icc 0 1 → (extend_f f x - extend_f g x) ^ 2 ≥ 0 :=
      by
        intro x hx
        rw [exf3]
        dsimp [extend_f2]
        dsimp [Function.extend]
        split
        positivity
        trivial

      --simp [integral_nonneg,ge_iff_le]
      have : (0 : ℝ) ≤ 1 :=
      by
        simp_all only [implies_true, Pi.sub_apply, Set.mem_Icc, ge_iff_le, and_imp, zero_le_one]
      let iii := @intervalIntegral.integral_nonneg _ (0 : ℝ) 1 volume this (λ x => nonneg x)
      rw [ge_iff_le]
      --dsimp [Set.Icc]
      --convert iii
      unfold Set.Icc at iii
      --@intervalIntegral ℝ normedAddCommGroup InnerProductSpace.toNormedSpace (fun u ↦ (extend_f f u - extend_f g u) ^ 2) 0 1 volume : ℝ
      dsimp [intervalIntegral] at iii
      convert iii
      simp
      exact integral_Icc_eq_integral_Ioc

    have ps2:(∫ (x : ℝ) in Set.Icc 0 1, (extend_f f x - extend_f g x) ^ 2) = 0 :=
    by
      simp_all only [sqrt_eq_zero, ge_iff_le, le_refl]

    have ps3:(∫ (x : ℝ) in Set.Icc 0 1, (extend_f (f - g) x) ^ 2) = 0 :=
    by
      rw [exf2]
      simp_all only [sqrt_zero, ge_iff_le, le_refl, Pi.sub_apply]

    have h_integral_zero : ∫ x in Set.Icc 0 1, (extend_f2 (f - g)) x = 0 :=
    by
      simp_all only [implies_true, Pi.sub_apply, ge_iff_le]

    have h_eq : ∀ x ∈ Set.Icc 0 1, (f - g).toFun x = 0 := continuous_sq_eq_zero_of_integral_zero h_integral_zero
    specialize h_eq x
    have : x ∈ Set.Icc 0 1:=
    by
      simp_all only [Set.mem_Icc, zero_le', true_and, ContinuousMap.toFun_eq_coe]
      obtain ⟨val, property⟩ := x
      simpa using property.2
    specialize h_eq this
    simp_all only [Set.mem_Icc, zero_le', true_and, ContinuousMap.toFun_eq_coe]
    obtain ⟨val, property⟩ := x
    exact sub_eq_zero.mp h_eq
    -/
  -/
