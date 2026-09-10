import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.Basic
--import Mathlib.Order.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.SetNotation
import Mathlib.Order.Filter.Basic
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Order.Group.Lattice
import Pdfproof.Dis.Ic_OpenPosMeasure

--01閉区間上の連続関数がL2ノルムで距離関数になる問題。無駄に01閉区間を実数全体の関数に拡張してしまったので、
--証明が長くなった。どういう選択をすればよいのか掴みきれずに証明に50時間以上かかっている。
--多くの証明が拡張に関わる部分。拡張しなくて、うまくインスタンスを設定できれば、もっとすっきりと証明できたと思われる。
--証明の構成は、
--01閉区間Icのインスタンスの設定は別ファイルIc_OpenPosMeasureにある。
--距離が一致すれば、関数が一致する部分。いたるところで0であれば、連続関数が0であることの証明。これにOpenPosMeasureが必要だった。
--セミノルムの有限性の証明。
--L2距離とセミノルムの関係の証明。eLPnormを利用。

set_option maxHeartbeats 2000000  --もとのままではうまくいかないかも。
open Classical
open MeasureTheory Real Set Metric Function Filter TopologicalSpace ENNReal
-----------------------------------------------------------------------------------
--基本的な定義とinstanceの設定。Icに関する基本的な設定は、Pdfproof.Ic_OpenPosMeasure.leanで設定済み。

/-! The space of real-valued continuous functions on the closed unit interval. -/
abbrev C₀ := ContinuousMap Ic ℝ

-- `ContinuousMap` already carries the required additive structure, so no local
-- instances are needed here.

--使ってない。
lemma measure_restrict_eq_measure {K : Set ℝ} (hK : MeasurableSet K) (hK_sub : K ⊆ Ic) :
  (volume.restrict Ic ) K = (volume : Measure ℝ) K :=
by
  -- `Measure.restrict_apply` を適用
  rw [MeasureTheory.Measure.restrict_apply hK]
  -- `K ⊆ Ic` なので `K ∩ Ic = K`
  rw [inter_eq_self_of_subset_left hK_sub]

/-- Extend a continuous function on `Ic` by zero to a function on `ℝ`. -/
noncomputable def toFun (f : C₀) : ℝ → ℝ :=
  fun x => if hx:x ∈ Ic then f.1 ⟨x,hx⟩ else 0

/-- The zero extension agrees with `f` on the closed unit interval. -/
@[simp] lemma toFun_apply_of_mem (f : C₀) {x : ℝ} (hx : x ∈ Ic) :
    toFun f x = f ⟨x, hx⟩ := by
  simp [toFun, hx]

/-- The zero extension vanishes outside the closed unit interval. -/
@[simp] lemma toFun_apply_of_not_mem (f : C₀) {x : ℝ} (hx : x ∉ Ic) :
    toFun f x = 0 := by
  simp [toFun, hx]

/-- The zero extension is supported on the closed unit interval. -/
lemma support_toFun_subset_Ic (f : C₀) : Function.support (toFun f) ⊆ Ic := by
  intro x hx
  by_contra hxIc
  exact hx (toFun_apply_of_not_mem f hxIc)

/-- The `Lᵖ` norm of the zero extension is unchanged by restricting to `Ic`. -/
lemma eLpNorm_toFun_restrict (f : C₀) (p : ℝ≥0∞) :
    eLpNorm (toFun f) p (volume.restrict Ic) = eLpNorm (toFun f) p volume :=
  eLpNorm_restrict_eq_of_support_subset (support_toFun_subset_Ic f)

/-- The zero extension of a continuous function on `Ic` is measurable on `ℝ`. -/
lemma toFun_measurable (f : C₀) : Measurable (toFun f) :=
by
  --have mIc : MeasurableSet Ic := (isCompact_Icc).measurableSet

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
    exact MeasurableEmbedding.subtype_coe mIc

  have h_meas_f_val : Measurable ((toFun f) ∘ (Subtype.val : Ic → ℝ)) :=
  by
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Subtype.coe_eta]
    exact hf_sub2


  have h_meas_Ic : MeasurableSet (univ : Set Ic) := --mIcとしてグローバルにも定義。
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
            simp_all
          have ch2: choose (Exists.intro (↑val1) property1 : ∃ a, a = x) = x :=
          by
            subst property1
            simp_all only [MeasurableSet.univ, Subtype.coe_prop, choose_eq]
          have ch3: choose (Exists.intro (val1) property1 : ∃ a, a.val = x) = ⟨x,h0⟩ :=
          by
            have ch4: (choose (Exists.intro (val1) property1 : ∃ a, a.val = x)).val = x :=
            by
              simp_all only [MeasurableSet.univ,choose_eq]
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
            simp_all
            by_contra h_contra
            simp_all only [not_false_eq_true]
            obtain ⟨y, hy⟩ := h1
            simp_all only [forall_const]
            linarith
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

-----------------------------------------------

--連続関数がいたるところ0であれば、0という補題。距離が0ならば関数が一致する証明で利用。

lemma continuous_eq_zero_of_ae_eq_zero_Ic
  (f : C₀)
  (h : ∀ᵐ x ∂(volume : MeasureTheory.Measure Ic), f.1 x = 0) :
  ∀ x : Ic, f.1 x = 0 :=
by

  --「f = 0 がほぼ至る所成り立つ」という仮定 h から， {x | f x ≠ 0} の測度が 0 であることを取り出す
  have h_eq : (fun x => f.1 x) =ᶠ[ae (volume : MeasureTheory.Measure Ic)] 0 := h

  let g:Ic→ ℝ := fun x => 0
  have :Continuous g:= by
    simp_all only [ContinuousMap.toFun_eq_coe, g]
    fun_prop

  let cae := Continuous.ae_eq_iff_eq (volume:Measure Ic) f.2 this
  intro x
  dsimp [g] at cae
  let ch := cae.mp h_eq
  exact congrFun ch x

--これは、01上で関数を定義した場合の補題。continuous_eq_zero_of_ae_eq_zero_Icを使って証明する。
--距離の定義をリーマン積分を利用したものからeLPnormというルベーグ積分を利用したものに変更したので、不要な部分がある可能性がある。
lemma continuous_nonneg_eq_zero_of_integral_zero_Ic (f : C(Ic, ℝ))(hf_nonneg : ∀ x, 0 ≤ f.1 x)
    (h : ∫⁻ x : Ic, ENNReal.ofReal (f.1 x) = 0) :
    ∀ x :Ic, f.1 x = 0 :=
by
  have h_nonneg : 0 ≤ fun x => f x := by
    intro x
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall,Pi.zero_apply]

  -- `f` が積分可能であることを示す
  have h_cont : ContinuousOn f (Set.univ : Set Ic) := f.continuous.continuousOn

  have : Measurable f.1 := f.measurable
  have h_ae_zero: ∀ᵐ (x : Ic), f.1 x = 0 :=
  by
    let mle :=(MeasureTheory.lintegral_eq_zero_iff (Measurable.ennreal_ofReal this)).mp h
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall]
    filter_upwards [mle] with x hx
    simp_all only [ContinuousMap.toFun_eq_coe, Pi.zero_apply, ofReal_eq_zero]
    obtain ⟨val, property⟩ := x
    exact le_antisymm hx (hf_nonneg _ _)

  exact continuous_eq_zero_of_ae_eq_zero_Ic f h_ae_zero

--2乗の関数が連続であること。後ろで使っている。
lemma q2c {f : C₀} : Continuous (fun x => (f.1 x)^2) :=
by
  simp_all only [ContinuousMap.toFun_eq_coe]
  fun_prop

--2乗の関数が0であれば、恒等的にゼロであること。
lemma continuous_sq_eq_zero_of_integral_zero_Ic {f : C₀}
   (h : ∫⁻ x in (Set.univ : Set Ic), ENNReal.ofReal ((f.1 x)^2) = 0) :
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
    have :∫⁻ (x : Ic), ENNReal.ofReal ((f.1 x) ^ 2) = 0 :=
    by
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, le_refl, implies_true, ge_iff_le,
        mem_Icc, zero_le', true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Subtype.forall,
        forall_const, zero_pow,  f2]

    specialize cne this
    show f.toFun x ^ 2 = 0
    simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, le_refl, implies_true,
      mem_Icc, zero_le', true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Subtype.forall,
       f2]
    simp_all only [ContinuousMap.toFun_eq_coe, f2]
    obtain ⟨val, property⟩ := x

    simp_all

  show ∀ (x : ↑Ic), f.toFun x = 0
  intro x
  exact pow_eq_zero (hf_eq_zero x (Set.mem_Icc.2 ⟨x.2.1, x.2.2⟩))

-------------------------------------------------------------------------
--------この辺りから下が三角不等式の証明に使うセミノルムの定義のための有界性の証明---
------------------------------------------------------------------------
--MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompactを利用して証明。

--使ってないので消しても良さそう。
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

--上の逆向きの補題。こっちを使っている。
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

--2乗の関数がMeasurableであること。こちらのほうはつかってないよう。
/-
theorem measurable_pow_two {α : Type*} {m : MeasurableSpace α}
  {f : α → ℝ} (hf : Measurable f) : Measurable (fun x => ‖f x‖ ^ (2 : ℕ)) := by
  -- First, show that the absolute value |f| is measurable
  have h_abs : Measurable (fun x => |f x|) := by
    exact hf.abs

  have h_pow : Measurable (fun x => |f x| ^ (2 : ℕ)) := by
    exact Measurable.pow_const h_abs 2

  have h_eq : (fun x => ‖f x‖ ^ (2 : ℕ)) = (fun x => |f x| ^ (2 : ℕ)) := by
    ext x
    simp [Real.norm_eq_abs]

  rw [h_eq]
  exact h_pow
-/

--2乗の関数がMeasurableであること。こちらを使っている。
theorem measurable_pow_two_enn {α : Type*} {m : MeasurableSpace α}
  {f : α → ℝ} (hf : Measurable f) : Measurable (fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) := by
  simp_all only [norm_eq_abs, sq_abs]
  refine Measurable.ennreal_ofReal ?_
  exact Measurable.pow_const hf 2

--積分をIcとIc_cに分ける補題。これを使って、三角不等式の証明をする。
lemma piecewise_lem (f:C₀):(∫⁻ (x : ℝ), ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) = (∫⁻ (x : ℝ) in Ic, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) + (∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) :=
by
  let lac:= @lintegral_add_compl ℝ Real.measurableSpace volume (fun x => ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) Ic mIc
  exact lac.symm

--Ic_cの積分が0であることを示す補題。これを使って、三角不等式の証明をする。
lemma zero_Ic_c_lem (f:C₀): (∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) = 0 :=
by
  apply (lintegral_eq_zero_iff (measurable_pow_two_enn (toFun_measurable f))).mpr
  --apply Filter.Eventually
  have : ∀ x, x ∉ Ic → ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ)) = 0 := by
    intro x hx
    simp [toFun_apply_of_not_mem f hx]
  have h_ae : (fun x:(Ic_c) => ENNReal.ofReal (‖toFun f x.val‖ ^ 2)) =ᶠ[ae (volume:Measure Ic_c)] 0 := by
    simp_all only [norm_eq_abs,  sq_abs, ofReal_eq_zero]
    filter_upwards with x
    simp_all only [Pi.zero_apply, ofReal_eq_zero]
    obtain ⟨val, property⟩ := x
    simp_all only
    exact this _ property

  apply (ae_restrict_iff_subtype measurableSet_Ic_c).mpr
  simp_all only [ norm_eq_abs, sq_abs, ofReal_eq_zero, Pi.zero_apply]
  filter_upwards with x
  obtain ⟨val, property⟩ := x
  simp_all only
  exact this _ property


lemma mem_L2_f_ext {f: C₀}: MemLp (toFun f) 2 volume :=
by
  constructor
  · convert toFun_measurable f
    apply Iff.intro
    exact fun a ↦ toFun_measurable f
    apply Measurable.aestronglyMeasurable
  · show eLpNorm (toFun f) 2 volume < ⊤
    have h_f_sq : (fun x => |toFun f x|^2) = fun x => (toFun f x)^2 :=
      by simp_all only [sq_abs]

    -- `MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact` を使う
    let h_measure_finite :=@MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact ℝ _ _ volume _ Ic hIc
    simp_all only [sq_abs, gt_iff_lt]
    have :ContinuousOn (toFun f) Ic:=
    by
      dsimp [toFun]
      rw [continuousOn_iff_continuous_restrict]
      unfold toFun
      simp_all only [ContinuousMap.toFun_eq_coe, restrict_dite, Subtype.coe_eta]
      fun_prop
    --fの値の有限性
    have h_f_bounded := IsCompact.exists_bound_of_continuousOn isCompact_Icc this
    obtain ⟨M, hM⟩ := h_f_bounded
    --f^2の値の有界性 R全体に広げたことで証明が大変になった。
    have h_f_sq : ∀ x :ℝ, x ∈ Set.Icc 0 1 → ‖toFun f x‖^2 ≤ M^2 :=
    by
      intro x hx
      specialize hM x hx
      have :‖toFun f x‖ ≥ 0:=
      by
        simp_all only [mem_Icc, norm_eq_abs, ge_iff_le, abs_nonneg]
      exact pow_le_pow_left₀ this hM 2
    have posM : 0 ≤ M:=
    by
      have : 0 ≤ ‖toFun f 0‖:=
      by
        simp_all only [mem_Icc, norm_eq_abs,  abs_nonneg]
      let h0 := hM 0 (by simp)
      linarith

    --実数全体で不等号がなりたつこと。これもR全体である必要はなかった。
    have h_f_sq2: ∀ x :ℝ,  (‖toFun f x‖^2) ≤ M^2 :=
    by
      intro x
      by_cases h : x ∈ Ic
      · exact h_f_sq x h
      · have : ‖toFun f x‖ ^ 2 = 0 :=
        by
          dsimp [toFun]
          split
          case isTrue h' =>
            contradiction
          case isFalse h' =>
            simp
        simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          pow_eq_zero_iff, norm_zero, zero_pow, pow_nonneg]

    have h_f_sq3: ∀ x :ℝ, ENNReal.ofReal (‖toFun f x‖^2) ≤ ENNReal.ofReal (M^2) :=
    by
      intro x
      exact ENNReal.ofReal_le_ofReal (h_f_sq2 x)

    have h_f_sq4: ∀ x :Ic, ENNReal.ofReal (‖toFun f x‖^2) ≤ ENNReal.ofReal (M^2) :=
    by
      intro x
      exact ENNReal.ofReal_le_ofReal (h_f_sq2 x)

    let mtl := @MeasureTheory.lintegral_mono Ic _ volume (fun x => ENNReal.ofReal (‖toFun f x‖^2)) (fun x => ENNReal.ofReal (M^2)) h_f_sq4
    -- ルベーグ積分を評価する
    let eel := @eLpNorm_eq_lintegral_rpow_enorm ℝ ℝ _ 2 _ volume (by norm_num) (by simp)

    have :(∫⁻ (x : ℝ), (‖toFun f x‖ₑ ^ (2:ℕ))) = (∫⁻ (x : ℝ), ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) :=
    by
      simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs,
         implies_true]
      rw [lintegral_congr]
      · intro x
        ring_nf
        dsimp [toFun]
        split
        case isTrue h' =>
          have :‖f.1 ⟨x, h'⟩‖ₑ ^ 2 = ENNReal.ofReal ((f.1 ⟨x,h'⟩) ^ 2) :=
          by

            rw [Real.enorm_eq_ofReal_abs]
            simp
            --f.1 ⟨x, h'⟩ < 0のときは成り立たない可能性がある。
            show ENNReal.ofReal |f.1 ⟨x, h'⟩| ^ 2 = ENNReal.ofReal (f.1 ⟨x, h'⟩ ^ 2)
            have : |f.1 ⟨x, h'⟩| ^ 2 = (f.1 ⟨x, h'⟩) ^ 2:=
            by
              simp_all only [ContinuousMap.toFun_eq_coe, sq_abs]
            rw [←this]
            have : |f.1 ⟨x, h'⟩| ≥ 0:=
            by
              simp_all only [ContinuousMap.toFun_eq_coe, sq_abs, ge_iff_le, abs_nonneg]
            exact Eq.symm (ofReal_pow this 2)

          simp_all only [ContinuousMap.toFun_eq_coe]
        case isFalse h' =>
          simp

    --補題zero_Ic_c_lemとして独立させているが残っている。ノルムの違いなどで補題のほうがうまくマッチしないため。もっと柔軟な補題にすればよかったかも。
    have zero_Ic_c: (∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) = 0 :=
    by
      apply (lintegral_eq_zero_iff (measurable_pow_two_enn (toFun_measurable f))).mpr
      --apply Filter.Eventually
      have : ∀ x, x ∉ Ic → ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ)) = 0 :=
        by
          intro x hx
          dsimp [toFun]
          simp [hx]
      have h_ae : (fun x:(Ic_c) => ENNReal.ofReal (‖toFun f x.val‖ ^ 2)) =ᶠ[ae (volume:Measure Ic_c)] 0 := by
        simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, ofReal_eq_zero, implies_true]
        filter_upwards with x
        simp_all only [Pi.zero_apply, ofReal_eq_zero]
        obtain ⟨val, property⟩ := x
        simp_all only
        exact this _ property

      apply (ae_restrict_iff_subtype measurableSet_Ic_c).mpr
      simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, ofReal_eq_zero, Pi.zero_apply, implies_true]
      filter_upwards with x
      obtain ⟨val, property⟩ := x
      simp_all only
      exact this _ property

    --これも補題として独立させたが残っている。
    have i_piecewise:(∫⁻ (x : ℝ), ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) = (∫⁻ (x : ℝ) in Ic, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) + (∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) :=
    by
      let lac:= @lintegral_add_compl ℝ Real.measurableSpace volume (fun x => ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) Ic mIc
      exact lac.symm

    have :∀ x, ‖toFun f x‖ₑ ^ (2:ℝ) = ‖toFun f x‖ₑ ^ (2:ℕ):= by
       exact fun x ↦ ENNReal.rpow_two ‖toFun f x‖ₑ

    --証明が長いのでcalcにしなくてもよかったかも。
    calc
      eLpNorm (toFun f) 2 volume
        =  (∫⁻ (x : ℝ), (‖toFun f x‖ₑ ^ ENNReal.toReal 2)) ^ (1 / ENNReal.toReal 2) :=
          by simp [eel]
      _ = ((∫⁻ (x : ℝ), ‖toFun f x‖ₑ ^ (2:ℝ))) ^ (1 / (2:ℝ)):= by
            have :ENNReal.toReal 2 = 2:=
            by
              simp
            rw [this]
      _ = ((∫⁻ (x : ℝ), ‖toFun f x‖ₑ ^ (2:ℕ))) ^ (1 / (2:ℝ)):= by
        simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, one_div]
      --_ = ((∫⁻ (x : ℝ), ‖toFun f x‖ₑ ^ (2:ℕ))) ^ (1 / (2:ℕ)):= by
      _ = ((∫⁻ (x : ℝ), ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ)))) ^ (1 / (2:ℝ)) :=
        by simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs]
      --積分範囲に注意。ここから変わっている。IcとIc以外で積分を分けた方がいいのかも。Ic以外の積分の値は0となる。
      _ = ((∫⁻ (x : ℝ) in Ic, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) + (∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ)))) ^ (1 / (2:ℝ)) :=
        by
          rw [i_piecewise]

      _ = ((∫⁻ (x : ℝ) in Ic, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ)))) ^ (1 / (2:ℝ)) :=
        by
          simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, add_zero, one_div]
      _ ≤  (∫⁻ (x : Ic), ENNReal.ofReal (M^2) ) ^ (1 / (2:ℝ)) :=
          by
            --using mtlと^ (1 / (2:ℝ))が正に対して、単調なことも。
            let rrl := @ENNReal.rpow_le_rpow ((∫⁻ (x : Ic), ENNReal.ofReal (‖toFun f x‖ ^ 2))) ((∫⁻ (x : Ic), ENNReal.ofReal (M^2) )) (1 / 2)

            specialize rrl mtl
            specialize rrl (by norm_num)
            convert rrl
            exact (@MeasureTheory.lintegral_subtype_comap ℝ _ volume Ic mIc (fun x => ENNReal.ofReal (‖toFun f x‖ ^ 2))).symm
      _ = (∫⁻ (x : Ic), ENNReal.ofReal (M^2)*(ENNReal.ofReal 1)) ^ (1 / (2:ℝ)) := by simp_all only [mem_Icc,
        norm_eq_abs, and_imp, sq_abs, pow_nonneg, ofReal_le_ofReal_iff, implies_true, add_zero, lintegral_const,
        one_div, ofReal_one, mul_one]
      _ = ((ENNReal.ofReal (M^2)) * ( (∫⁻ x in Ic,ENNReal.ofReal 1))) ^ (1 / (2:ℝ)) := by

            rw [@MeasureTheory.lintegral_const_mul _ _ _ (ENNReal.ofReal (M^2)) (fun x => ENNReal.ofReal 1) (by simp)]
            rw [←@MeasureTheory.lintegral_subtype_comap ℝ _ volume Ic mIc (fun x => ENNReal.ofReal 1)]
            rw [MeasureTheory.lintegral_const]
            simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, pow_nonneg, ofReal_le_ofReal_iff, implies_true,
              add_zero, ofReal_one, one_mul, one_div, lintegral_const]
            rfl

      _ = (ENNReal.ofReal (M^2) * volume Ic)^ (1 / (2:ℝ))  :=
        by
          simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, ofReal_one, lintegral_const, MeasurableSet.univ,
            Measure.restrict_apply, univ_inter, one_mul]
      _ < ⊤ :=
      by
        simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, implies_true, one_div,ENNReal.ofReal_pow,lt_top_iff_ne_top]
        have : ENNReal.ofReal M^2 * volume Ic ≠ ∞ := by
          simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          rw [ENNReal.mul_eq_top] at a
          simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero, not_le,
            pow_eq_top_iff, ofReal_ne_top, and_true, false_and, or_false]
          obtain ⟨left, right⟩ := a
          simp [right] at h_measure_finite
        simp_all only [ne_eq]
        simp_all only [rpow_eq_top_iff, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
          ofReal_eq_zero, inv_neg'', inv_pos, Nat.ofNat_pos, and_true, or_false, not_and, not_lt, Nat.ofNat_nonneg,
          implies_true]
----------------距離関数の設定-----------------------
--定義をリーマン積分から変更。
noncomputable def L2_distance_Ic (f g : C₀) : ℝ :=
   ‖(@mem_L2_f_ext (f-g)).toLp‖
  --Real.sqrt (∫ x in (Set.univ:Set Ic), (f.1 x - g.1 x) ^ 2)

--セミノルムと距離関数の関係。
lemma LP2norm {f h : C₀} :
-- L2_distance_Ic f g = ‖(@mem_L2_f_ext f).toLp - (@mem_L2_f_ext g).toLp‖ :=
  L2_distance_Ic f h = ‖(@mem_L2_f_ext f).toLp-(@mem_L2_f_ext h).toLp‖ :=
by
  simp [L2_distance_Ic]
  dsimp [MemLp.toLp]

  dsimp [Lp.norm_def]
  dsimp [eLpNorm ]
  simp
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  simp
  rw [lintegral_congr_ae]
  simp only [sub_eq_add_neg]
  simp
  --fh_rw3で暗黙につかっている。
  have fh_rw2:∀ x, (toFun f + -toFun h) x = toFun (f + -h) x := by
    intro x
    simp_all only [Pi.add_apply, Pi.neg_apply]
    unfold toFun
    split
    case isTrue h' =>
      simp_all only [ContinuousMap.toFun_eq_coe]
      rfl
    case isFalse h' =>
      simp_all only [neg_zero, add_zero]

  --後ろで使っている。
  have fh_rw2': (toFun f + -toFun h) = toFun (f + -h) := by
    funext x
    simp_all only [Pi.add_apply, Pi.neg_apply]

  --後ろで使っている。
  have fh_rw3: toFun (f + -h) = toFun (f - h):= by
    simp_all only [Pi.add_apply, Pi.neg_apply]
    rfl

  --have ff_eq: ∀ ff:ℝ → ℝ, ff =ᵐ[volume] ff := by
  --  intro ff
  --  simp_all only [Pi.add_apply, Pi.neg_apply, EventuallyEq.refl]
  --let tt := ff_eq (toFun (f + -h))
  /- 簡単な場合の証明で練習した部分。f-hでなく、fだけで証明している。消してもよい。
  have meas_f : Measurable (toFun f) := toFun_measurable f
  have ASf:AEStronglyMeasurable (toFun f) volume :=
  by
    exact meas_f |>.aestronglyMeasurable
  have : ↑(AEEqFun.mk (toFun f) ASf) =ᵐ[volume] (toFun f):= by
    simp_all only [Pi.add_apply, Pi.neg_apply]
    filter_upwards [AEEqFun.coeFn_mk _ ASf]
    intro a_1 a_2
    simp_all only

  let tta := ae_lem (toFun f) ASf
  have : ∀ᵐ aa ∂volume,‖toFun f aa‖ₑ = ‖(AEEqFun.mk (toFun f) ASf) aa‖ₑ := by
    filter_upwards [tta] with a ha
    simp_all only [Pi.add_apply, Pi.neg_apply]
  -/

  have :  ∀ ff:ℝ → ℝ, (aesm:AEStronglyMeasurable ff) →  ↑(AEEqFun.mk ff aesm) =ᵐ[volume] ff := by
    intro ff aesm
    simp_all only [AEEqFun.coeFn_mk]

  have ae_lem:  ∀ ff:ℝ → ℝ, (aesm:AEStronglyMeasurable ff) → ∀ᵐ aa ∂volume, ‖↑((AEEqFun.mk ff aesm) aa)‖ₑ = ‖ff aa‖ₑ := by
    intro ff aesm
    filter_upwards [this ff aesm] with aa haa
    simp_all only [AEEqFun.coeFn_mk]

  have meas_fh : Measurable (toFun (f-h)) := toFun_measurable (f-h)
  have ASfh:AEStronglyMeasurable (toFun (f - h)) volume:=
  by
    exact meas_fh |>.aestronglyMeasurable

  let ttfh:= ae_lem (toFun (f-h)) ASfh
  have : ∀ᵐ aa ∂volume,‖toFun (f + -h) aa‖ₑ = ‖(AEEqFun.mk (toFun (f - h)) ASfh) aa‖ₑ := by
    filter_upwards [ttfh] with aa haa
    simp_all only [AEEqFun.coeFn_mk]

  rw [←fh_rw3] at ASfh
  let ttfh' := ae_lem (toFun (f + -h)) ASfh
  rw [←fh_rw2'] at ASfh
  have : ∀ᵐ aa ∂volume,‖toFun (f + -h) aa‖ₑ = ‖(AEEqFun.mk (toFun f + - toFun h) ASfh) aa‖ₑ := by
    filter_upwards [ttfh'] with aa haa
    simp_all only [AEEqFun.coeFn_mk]

  rename_i this_5
  simp_all only [ Pi.add_apply, Pi.neg_apply]
  filter_upwards [this_5] with a ha
  simp_all only

-------------------------------------------------------------------------
-----ここから距離の公理の証明
-------------------------------------------------------------------------

--マイナスにしてもノルムが変わらないこと。距離の公理の証明に利用。
lemma eLpNorm_neg_eq {f : ℝ → ℝ} :
  eLpNorm (λ x => - f x) 2 volume = eLpNorm f 2 volume :=
by
  dsimp [eLpNorm]
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]

  rw [lintegral_congr_ae]
  simp_all only [enorm_neg, toReal_ofNat,EventuallyEq.refl]

--距離空間の公理を満たすためには、定義域を[0,1]に制限する必要がある。
noncomputable instance : MetricSpace C₀ where
  dist := by
   exact L2_distance_Ic

  dist_self f := by
    simp [L2_distance_Ic]
    unfold toFun
    simp

  dist_comm f g := by
    simp [L2_distance_Ic]
    congr 1
    ring_nf
    --unfold toFun
    --rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
    let ele := @eLpNorm_neg_eq (toFun (f-g))
    have :-toFun (f - g) = toFun (g-f) := by
      unfold toFun
      simp_all only [ContinuousMap.toFun_eq_coe]
      ext x
      split
      · rename_i h0
        simp [h0]
        simp only [sub_eq_add_neg]
        rw [ContinuousMap.add_apply]
        rw [ContinuousMap.add_apply]
        simp
        congr
        exact neg_neg _
      · simp_all only [Pi.neg_apply, ↓reduceDIte, neg_zero]

    symm
    simp [← this]

  dist_triangle f g h := by
    let fₘ := @mem_L2_f_ext f
    let gₘ := @mem_L2_f_ext g
    let hₘ := @mem_L2_f_ext h
    let f_L2 := fₘ.toLp
    let g_L2 := gₘ.toLp
    let h_L2 := hₘ.toLp
    calc
      L2_distance_Ic f h
        = ‖f_L2 - h_L2‖ := by
          dsimp [f_L2, h_L2,fₘ,hₘ]
          exact (@LP2norm f h)

      _ ≤ ‖f_L2 - g_L2‖ + ‖g_L2 - h_L2‖ := norm_sub_le_norm_sub_add_norm_sub f_L2 g_L2 h_L2
      _ = L2_distance_Ic f g + L2_distance_Ic g h
        :=
        by
          dsimp [f_L2, g_L2, h_L2,fₘ,gₘ,hₘ]
          let lfg := (@LP2norm f g)
          let lgh := (@LP2norm g h)
          rw [←lfg,←lgh]

  eq_of_dist_eq_zero := by
    intro f g hfg
    simp [L2_distance_Ic] at hfg

    dsimp [C₀]
    ext x
    show f.1 x = g.1 x

    dsimp [eLpNorm] at hfg
    simp at hfg
    dsimp [eLpNorm'] at hfg
    simp at hfg

    --他の部分とかぶっている。
    have h_integral_zero:((∫⁻ (a : ℝ),  (‖toFun (f - g) a‖ₑ ^ 2)) ) = 0 := by
      rw [ENNReal.toReal_eq_zero_iff] at hfg
      cases hfg
      case inl h' =>
        --rw [ENNReal.rpow_eq_zero_iff]
        have hr : (0:ℝ) < ((2⁻¹):ℝ) := by norm_num
        let ere := (@ENNReal.rpow_eq_zero_iff ((∫⁻ (a : ℝ), (‖toFun (f - g) a‖ₑ ^ 2)) ) (2⁻¹:ℝ) ).mp h'
        simp_all only [inv_pos, Nat.ofNat_pos]
        obtain ⟨val, property⟩ := x
        simp_all only [mem_Icc]
        obtain ⟨left, right⟩ := property
        cases ere with
        | inl h => simp_all only [inv_pos, Nat.ofNat_pos, and_true]
        | inr h_1 =>
          exfalso
          simp at h_1
          linarith
        --h'を書き換える必要。
      case inr h_inf => -- `∞` の場合は矛盾（ルベーグ積分は有限）
        exfalso
        -- ノルムの有界性から証明。
        have h_integral_finite : (∫⁻ (a : ℝ), (‖toFun (f - g) a‖ₑ ^ 2)) < ⊤ := by

          let fₘ := (@mem_L2_f_ext f).toLp
          let gₘ := (@mem_L2_f_ext g).toLp
          let fgₘ := (@mem_L2_f_ext (f - g)).toLp
          let fglp := fgₘ.2
          have h_memLp : MemLp (toFun (f - g)) 2 volume := @mem_L2_f_ext (f - g)
          -- `Memℒp` の定義から `eLpNorm` が有限
          have h_norm : eLpNorm (toFun (f - g)) 2 volume < ∞ := by exact MemLp.eLpNorm_lt_top h_memLp--h_memℒp.2
          -- `eLpNorm` の定義を適用
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm] at h_norm

          simp_all only [rpow_eq_top_iff, inv_neg'', inv_pos, Nat.ofNat_pos, and_true, toReal_ofNat,
            one_div, gt_iff_lt]
          obtain ⟨val, property⟩ := x
          --obtain ⟨val_1, property_1⟩ := fₘ
          --obtain ⟨val_2, property_2⟩ := gₘ
          --obtain ⟨val_3, property_3⟩ := fgₘ
          simp_all only [mem_Icc]
          obtain ⟨left, right⟩ := property
          cases h_inf with
          | inl h => simp_all only [ zero_lt_top]
          | inr h_1 => simp_all only [ENNReal.rpow_ofNat, inv_pos, Nat.ofNat_pos, top_rpow_of_pos, lt_self_iff_false]

          · simp_all only [rpow_eq_top_iff, inv_neg'', inv_pos, Nat.ofNat_pos, and_true, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true]

          · simp_all only [rpow_eq_top_iff, inv_neg'', inv_pos, Nat.ofNat_pos, and_true, ne_eq, ofNat_ne_top,
              not_false_eq_true]

        simp_all only [rpow_eq_top_iff, inv_neg'', inv_pos, Nat.ofNat_pos, and_true]
        obtain ⟨val, property⟩ := x
        simp_all only [mem_Icc]
        obtain ⟨left, right⟩ := property
        cases h_inf with
        | inl h =>
          simp_all only [zero_lt_top]
          --obtain ⟨left_1, right_1⟩ := h
          linarith
        | inr h_1 => simp_all only [lt_self_iff_false]

    --補題を適用したかったが、そのまま直接証明した部分もあって、うまくいってない。
    have h_integral_zero:((∫⁻ (a : ℝ),  ENNReal.ofReal (‖toFun (f - g) a‖ ^ 2)) ) = 0 := by
      --convert h_integral_zero
      let lc := @lintegral_congr _ _ volume (fun a => ENNReal.ofReal (‖toFun (f - g) a‖ ^ 2)) (fun a => ‖toFun (f - g) a‖ₑ ^ 2)
      have :∀ a:ℝ, ENNReal.ofReal (‖toFun (f - g) a‖ ^ 2) = ‖toFun (f - g) a‖ₑ ^ 2 := by
        let eq_pointwise : ∀ x : ℝ, ENNReal.ofReal (‖toFun (f - g) x‖ ^ 2) = ‖toFun (f - g) x‖ₑ ^ 2 :=
          fun x => by
            simp_all only [norm_eq_abs, sq_abs]
            rw [Real.enorm_eq_ofReal_abs]
            rw [←abs_sq]
            rename_i x_1
            simp_all only [inv_pos, Nat.ofNat_pos, zero_rpow_of_pos, toReal_zero, abs_pow, sq_abs]
            obtain ⟨val, property⟩ := x_1
            simp_all only [mem_Icc]
            --obtain ⟨left, right⟩ := property
            rw [← ENNReal.ofReal_pow]
            · simp_all only [sq_abs]
            · simp_all only [abs_nonneg]
        intro a
        simp_all only [norm_eq_abs, sq_abs]
        --obtain ⟨val, property⟩ := x
        --obtain ⟨left, right⟩ := property
        simpa using eq_pointwise a
      simp_all only [inv_pos, Nat.ofNat_pos, zero_rpow_of_pos, toReal_zero, norm_eq_abs, sq_abs]

    have h_integral_Ic_c : ∫⁻ x in (Set.univ:Set Ic_c), ENNReal.ofReal ((toFun f x - toFun g x) ^ 2) = 0 :=
    by
      let zic := zero_Ic_c_lem (⟨fun x:Ic => ((f.1 x) + - (g.1 x))^(2:ℝ),by
        simp_all only [ContinuousMap.toFun_eq_coe, Real.rpow_two]
        --obtain ⟨val, property⟩ := x
        --simp_all only [mem_Icc]
        --obtain ⟨left, right⟩ := property
        fun_prop
      ⟩)
      simp at zic
      simp
      dsimp [Ic] at zic
      dsimp [Ic_c]
      dsimp [Ic]

      convert zic
      rw [MeasureTheory.lintegral_congr_ae]
      · simp_all only
        symm
        rw [lintegral_zero]

      · --show (fun x ↦ ENNReal.ofReal ((toFun f ↑x - toFun g ↑x) ^ 2)) =ᶠ[ae volume] fun a ↦ 0
        have h : ∀ (x : Ic_c), ENNReal.ofReal ((toFun f ↑x - toFun g ↑x) ^ 2) = 0 := by
          intro x
          unfold toFun
          split
          case isTrue h' =>
            simp_all only [ContinuousMap.toFun_eq_coe]
            obtain ⟨val, property⟩ := x  --とるとエラー
            simp_all only
            simp_all only [ofReal_eq_zero]
            --obtain ⟨val_1, property_1⟩ := x
            rw [← zic] at zic
            simp_all only
            --simp_all only [mem_Icc]
            --obtain ⟨left, right⟩ := property_1
            norm_cast
          case isFalse h' =>
            simp
        simp_all only [ofReal_eq_zero, Subtype.forall]
        obtain ⟨val, property⟩ := x
        filter_upwards with x
        simp_all only [ofReal_eq_zero, Subtype.coe_prop]
    --have :∫⁻ (x : ↑Ic) in univ, ENNReal.ofReal ((f - g).toFun x ^ 2) ∂@volume = 0 :=
    --by
    have :∀ x∈ Icᶜ, ‖toFun (f - g) x‖ ^ 2= (toFun f x - toFun g x) ^ 2 := by
      intro x hx
      simp_all only [norm_eq_abs, sq_abs]
      unfold toFun
      split
      case isTrue h' =>
        simp_all only [ContinuousMap.toFun_eq_coe]
        rfl
      case isFalse h' =>
        simp


    have integral_zoro: ∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun (f - g) x‖ ^ 2) = 0 :=
    by
      have : ∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun (f - g) x‖ ^ 2) = ∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal ((toFun f x - toFun g x) ^ 2) :=
      by
        apply lintegral_congr
        intro x
        unfold toFun
        split
        case isTrue h' =>
          simp_all only [ContinuousMap.toFun_eq_coe]
          rename_i x_1
          simp_all only [Measure.restrict_univ, mem_compl_iff, norm_eq_abs, sq_abs]

          rfl
        case isFalse h' =>
          simp
      rw [this]
      convert h_integral_Ic_c
      simp
      have mIc_c : MeasurableSet (Icᶜ) := measurableSet_Icc.compl
      dsimp [Ic_c]
      let mls :=(@MeasureTheory.lintegral_subtype_comap ℝ _ volume Ic_c mIc_c (fun x => ENNReal.ofReal ((toFun f x - toFun g x) ^ 2))).symm
      dsimp [Ic_c] at mls
      exact mls

    have :((∫⁻ (a : ℝ), ENNReal.ofReal (‖toFun (f - g) a‖ ^ 2)) ) = ((∫⁻ (a : ℝ) in Ic, ENNReal.ofReal (‖toFun (f - g) a‖ ^ 2)) ) :=
    by
      rw [piecewise_lem (f - g)]
      simp_all only [Measure.restrict_univ, mem_compl_iff, norm_eq_abs, sq_abs, add_zero]

    have :((∫⁻ (a : ℝ) in Ic, ENNReal.ofReal (‖toFun (f - g) a‖ ^ 2)) ) = 0 :=
    by
      simp_all only [inv_pos, Nat.ofNat_pos, zero_rpow_of_pos,  norm_eq_abs, sq_abs, Measure.restrict_univ,
        mem_compl_iff]
    have :∫⁻ (x : ↑Ic) in univ, ENNReal.ofReal (toFun (f - g) x ^ 2) = 0:=
    by
      let mls := (@MeasureTheory.lintegral_subtype_comap ℝ _ volume Ic mIc (fun x => ENNReal.ofReal (((toFun (f - g)) x )^ 2)))
      simp
      simp at mls
      simp at this
      rw [←mls] at this
      exact this

    have :∫⁻ (x : ↑Ic) in univ, ENNReal.ofReal ((f - g).1 x ^ 2) = 0 := by
      convert this
      rename_i x_1
      unfold toFun
      split
      case isTrue h' =>
        simp_all only [ContinuousMap.toFun_eq_coe]
        rfl
      case isFalse h' =>
        simp
        simp_all only [inv_pos, Nat.ofNat_pos, zero_rpow_of_pos, ENNReal.toReal_zero, norm_eq_abs, sq_abs,
          Measure.restrict_univ, mem_compl_iff, Subtype.coe_prop, not_true_eq_false]

    let diff := ContinuousMap.mk (λ x => f.1 x - g.1 x) (f.continuous_toFun.sub g.continuous_toFun)
    let cs := @continuous_sq_eq_zero_of_integral_zero_Ic (f-g) this
    have h_eq : ∀ x ∈ Set.Icc 0 1, diff.toFun x = 0 :=
    by
      intro x_1 a
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, mem_Icc, zero_le', true_and,
        diff]
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
    simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, ContinuousMap.coe_mk, diff]
    exact sub_eq_zero.mp h_eq
