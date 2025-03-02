import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice
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
import Pdfproof.Ic_OpenPosMeasure
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

instance : MeasurableSpace ℝ := borel ℝ
instance : OpensMeasurableSpace ℝ := inferInstance

def C₀ := ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ
--def Ic := Set.Icc (0:Real) 1 --Pdfproof.Ic_OpenPosMeasure.leanで設定済み。

--使ってないかも。
lemma measure_restrict_eq_measure {K : Set ℝ} (hK : MeasurableSet K) (hK_sub : K ⊆ Ic) :
  (volume.restrict Ic ) K = (volume : Measure ℝ) K :=
by
  -- `Measure.restrict_apply` を適用
  rw [MeasureTheory.Measure.restrict_apply hK]
  -- `K ⊆ Ic` なので `K ∩ Ic = K`
  --congr
  --simp_all only [inter_eq_left]
  rw [inter_eq_self_of_subset_left hK_sub]

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
  /-have zero_measure : (volume : MeasureTheory.Measure Ic) {x | f.1 x ≠ 0} = 0 :=
  by
    simp_all only [ContinuousMap.toFun_eq_coe, Function.const_apply]
    simp_all only [ne_eq]
    exact h
  -/

  let g:Ic→ ℝ := fun x => 0
  have :Continuous g:= by
    simp_all only [ContinuousMap.toFun_eq_coe, ne_eq, g]
    fun_prop

  let cae := Continuous.ae_eq_iff_eq (volume:Measure Ic) f.2 this
  intro x
  dsimp [g] at cae
  let ch := cae.mp h_eq
  exact congrFun ch x

--これは、01上で関数を定義した場合の補題。以下を使って証明したい。
--theorem continuous_eq_zero_of_ae_eq_zero_Ic
--  (f : C₀) (h : ∀ᵐ x ∂(volume : MeasureTheory.Measure Ic), f.1 x = 0) :
--  ∀ x : Ic, f.1 x = 0
--この定理自体が、リーマン積分とルベーグ積分を繋ぐものだったので、最初からルベーグ積分で定義した場合は不要というわけでもないか。
lemma continuous_nonneg_eq_zero_of_integral_zero_Ic (f : C(Ic, ℝ))(hf_nonneg : ∀ x, 0 ≤ f.1 x)
    (h : ∫⁻ x : Ic, ENNReal.ofReal (f.1 x) = 0) :
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
  /-
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
  -/
  have : Measurable f.1 := f.measurable
  have h_ae_zero: ∀ᵐ (x : Ic), f.1 x = 0 :=
  by
    let mle :=(MeasureTheory.lintegral_eq_zero_iff (Measurable.ennreal_ofReal this)).mp h
    simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall]
    filter_upwards [mle] with x hx
    simp_all only [ContinuousMap.toFun_eq_coe, Pi.zero_apply, ofReal_eq_zero]
    obtain ⟨val, property⟩ := x
    exact le_antisymm hx (hf_nonneg _ _)

  -- `f` が測度論的に 0 であることを示す
  --have h_ae_zero : f =ᵐ[volume] 0 :=
  --  (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => hf_nonneg x) h_integrable).mp h
  -- `continuous_eq_zero_of_ae_eq_zero_Ic` を適用
  exact continuous_eq_zero_of_ae_eq_zero_Ic f h_ae_zero

--使っている。
lemma q2c {f : C₀} : Continuous (fun x => (f.1 x)^2) :=
by
  simp_all only [ContinuousMap.toFun_eq_coe]
  fun_prop

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
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, integral_zero, le_refl, implies_true, ge_iff_le,
        mem_Icc, zero_le', true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Subtype.forall,
        forall_const, zero_pow, f2c, f2]
    --have ∫⁻ (x : ↑Ic), ENNReal.ofReal (f.1 x ^ 2) = 0 :=
    --by
    specialize cne this
    show f.toFun x ^ 2 = 0
    simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, integral_zero, le_refl, implies_true, ge_iff_le,
      mem_Icc, zero_le', true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Subtype.forall,
      f2c, f2]
    simp_all only [ContinuousMap.toFun_eq_coe, f2, f2c]
    obtain ⟨val, property⟩ := x
    --search_proof
    simp_all only [f2c, f2]

  -- (f x) ^ 2 = 0 ならば f x = 0
  show ∀ (x : ↑Ic), f.toFun x = 0
  intro x
  exact pow_eq_zero (hf_eq_zero x (Set.mem_Icc.2 ⟨x.2.1, x.2.2⟩))

-------------------------------------------------------------------------
--------この辺りから下が三角不等式や可測性に関係がある部分-----------------------
------------------------------------------------------------------------



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
  have mIc : MeasurableSet Ic := (isCompact_Icc).measurableSet

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
            simp_all only [ContinuousMap.toFun_eq_coe, Subtype.forall, Subtype.coe_eta]
            subst property1
            simp_all only [MeasurableSet.univ, Subtype.coe_prop, choose_eq]
          have ch2: choose (Exists.intro (↑val1) property1 : ∃ a, a = x) = x :=
          by
            subst property1
            simp_all only [MeasurableSet.univ, Subtype.coe_prop, choose_eq]
          have ch3: choose (Exists.intro (val1) property1 : ∃ a, a.val = x) = ⟨x,h0⟩ :=
          by
            have ch4: (choose (Exists.intro (val1) property1 : ∃ a, a.val = x)).val = x :=
            by
              simp_all only [MeasurableSet.univ, Subtype.coe_prop, choose_eq]
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
theorem measurable_pow_two {α : Type*} {m : MeasurableSpace α}
  {f : α → ℝ} (hf : Measurable f) : Measurable (fun x => ‖f x‖ ^ (2 : ℕ)) := by
  -- First, show that the absolute value |f| is measurable
  have h_abs : Measurable (fun x => |f x|) := by
    exact hf.abs

  -- Show that |f|^2 is measurable using the fact that
  -- the composition of measurable functions is measurable
  have h_pow : Measurable (fun x => |f x| ^ (2 : ℕ)) := by
    exact Measurable.pow_const h_abs 2

  -- Since ‖f x‖ = |f x| for real-valued functions
  -- we can show they're equal and substitute
  have h_eq : (fun x => ‖f x‖ ^ (2 : ℕ)) = (fun x => |f x| ^ (2 : ℕ)) := by
    ext x
    simp [Real.norm_eq_abs]

  -- Complete the proof using our equality
  rw [h_eq]
  exact h_pow

theorem measurable_pow_two_enn {α : Type*} {m : MeasurableSpace α}
  {f : α → ℝ} (hf : Measurable f) : Measurable (fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) := by
  simp_all only [norm_eq_abs, sq_abs]
  refine Measurable.ennreal_ofReal ?_
  exact Measurable.pow_const hf 2

lemma piecewise_lem (f:C₀):(∫⁻ (x : ℝ), ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) = (∫⁻ (x : ℝ) in Ic, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) + (∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) :=
by
  let lac:= @lintegral_add_compl ℝ Real.measurableSpace volume (fun x => ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) Ic mIc
  exact lac.symm

lemma zero_Ic_c_lem (f:C₀): (∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) = 0 :=
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

  --apply Filter.Eventually.of_forall

  have measurableSet_Ic_c: MeasurableSet Ic_c := by
    simp_all only [Ic_c, MeasurableSet.compl]
    simp_all only [mem_Icc, norm_eq_abs, and_imp, implies_true, sq_abs, ofReal_eq_zero, MeasurableSet.compl_iff]
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

  apply (ae_restrict_iff_subtype measurableSet_Ic_c).mpr
  simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, ofReal_eq_zero, Pi.zero_apply, implies_true]
  filter_upwards with x
  obtain ⟨val, property⟩ := x
  simp_all only
  exact this _ property

lemma mem_L2_f_ext : Memℒp (toFun f) 2 volume :=
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
    --apply integrable_of_integral_lt_top
    --have h_compact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
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
    -- 2. |f(x)|^2 も M^2 で抑えられる
    --f^2の値の有界性 R全体に広げる必要はなかった。Icだけでよい。
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
        simp_all only [mem_Icc, norm_eq_abs, ge_iff_le, abs_nonneg]
      let h0 := hM 0 (by simp [Ic])
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

    --これは積分範囲がRなのでおかしい。Icにすべき。
    --let mtl := @MeasureTheory.lintegral_mono ℝ _ volume (fun x => ENNReal.ofReal (‖toFun f x‖^2)) (fun x => ENNReal.ofReal (M^2)) h_f_sq3
    let mtl := @MeasureTheory.lintegral_mono Ic _ volume (fun x => ENNReal.ofReal (‖toFun f x‖^2)) (fun x => ENNReal.ofReal (M^2)) h_f_sq4
    -- 3. ルベーグ積分を評価する
    let eel := @eLpNorm_eq_lintegral_rpow_enorm ℝ ℝ _ 2 volume _ (by norm_num) (by simp) (toFun f)

    have :(∫⁻ (x : ℝ), (‖toFun f x‖ₑ ^ (2:ℕ))) = (∫⁻ (x : ℝ), ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) :=
    by
      simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, const_apply, lintegral_const,
        measure_univ_of_isAddLeftInvariant, implies_true]
      rw [lintegral_congr]
      · intro x
        ring_nf
        dsimp [toFun]
        split
        case isTrue h' =>
          have :‖f.1 ⟨x, h'⟩‖ₑ ^ 2 = ENNReal.ofReal ((f.1 ⟨x,h'⟩) ^ 2) :=
          by
            --have : (0 : ℝ) ≤ 2 := by norm_num
            --let eor := ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (toFun f x)) this
            rw [Real.enorm_eq_ofReal_abs]
            simp
            --f.1 ⟨x, h'⟩ < 0のときは成り立たない可能性がある。
            show ENNReal.ofReal |f.1 ⟨x, h'⟩| ^ 2 = ENNReal.ofReal (f.1 ⟨x, h'⟩ ^ 2)
            have : |f.1 ⟨x, h'⟩| ^ 2 = (f.1 ⟨x, h'⟩) ^ 2:=
            by
              simp_all only [Nat.ofNat_nonneg, ContinuousMap.toFun_eq_coe, sq_abs]
            rw [←this]
            have : |f.1 ⟨x, h'⟩| ≥ 0:=
            by
              simp_all only [ContinuousMap.toFun_eq_coe, sq_abs, ge_iff_le, abs_nonneg]
            exact Eq.symm (ofReal_pow this 2)

          simp_all only [ContinuousMap.toFun_eq_coe]
        case isFalse h' =>
          simp

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

      --apply Filter.Eventually.of_forall

      have measurableSet_Ic_c: MeasurableSet Ic_c := by
        simp_all only [Ic_c, MeasurableSet.compl]
        simp_all only [mem_Icc, norm_eq_abs, and_imp, implies_true, sq_abs, ofReal_eq_zero, MeasurableSet.compl_iff]
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

      apply (ae_restrict_iff_subtype measurableSet_Ic_c).mpr
      simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, ofReal_eq_zero, Pi.zero_apply, implies_true]
      filter_upwards with x
      obtain ⟨val, property⟩ := x
      simp_all only
      exact this _ property

    have i_piecewise:(∫⁻ (x : ℝ), ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) = (∫⁻ (x : ℝ) in Ic, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) + (∫⁻ (x : ℝ) in Icᶜ, ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) :=
    by
      let lac:= @lintegral_add_compl ℝ Real.measurableSpace volume (fun x => ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ))) Ic mIc
      exact lac.symm

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
        simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, rpow_ofNat, one_div]
      --_ = ((∫⁻ (x : ℝ), ‖toFun f x‖ₑ ^ (2:ℕ))) ^ (1 / (2:ℕ)):= by
      _ = ((∫⁻ (x : ℝ), ENNReal.ofReal (‖toFun f x‖ ^ (2:ℕ)))) ^ (1 / (2:ℝ)) :=
        by simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, Nat.reduceDiv, pow_zero]
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
            --have :∫⁻ (x : ↑Ic), ENNReal.ofReal (‖toFun f ↑x‖ ^ 2) ≤  (∫⁻ (x : ↑Ic), ENNReal.ofReal (M ^ 2)) :=
            --by
            specialize rrl mtl
            specialize rrl (by norm_num)
            convert rrl
            exact (@MeasureTheory.lintegral_subtype_comap ℝ _ volume Ic mIc (fun x => ENNReal.ofReal (‖toFun f x‖ ^ 2))).symm
      _ = (∫⁻ (x : Ic), ENNReal.ofReal (M^2)*(ENNReal.ofReal 1)) ^ (1 / (2:ℝ)) := by simp_all only [mem_Icc,
        norm_eq_abs, and_imp, sq_abs, pow_nonneg, ofReal_le_ofReal_iff, implies_true, add_zero, lintegral_const,
        one_div, ofReal_one, mul_one]
      _ = ((ENNReal.ofReal (M^2)) * ( (∫⁻ x in Ic,ENNReal.ofReal 1))) ^ (1 / (2:ℝ)) := by
            --simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, lintegral_const, measure_univ_of_isAddLeftInvariant,
            --  Nat.reduceDiv, pow_zero, ofReal_one, MeasurableSet.univ, Measure.restrict_apply, univ_inter, one_mul]
            --simp_all only [implies_true, pow_nonneg, ofReal_le_ofReal_iff, add_zero, one_div]
            --#check @MeasureTheory.lintegral_subtype_comap _ _ _ _ mIc (fun x => ENNReal.ofReal (M^2))
            rw [@MeasureTheory.lintegral_const_mul _ _ _ (ENNReal.ofReal (M^2)) (fun x => ENNReal.ofReal 1) (by simp)]
            rw [←@MeasureTheory.lintegral_subtype_comap ℝ _ volume Ic mIc (fun x => ENNReal.ofReal 1)]
            rw [MeasureTheory.lintegral_const]
            simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, pow_nonneg, ofReal_le_ofReal_iff, implies_true,
              add_zero, ofReal_one, one_mul, one_div, lintegral_const]
            rfl
            --rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (M^2)) Ic]
      _ = (ENNReal.ofReal (M^2) * volume Ic)^ (1 / (2:ℝ))  :=
        by
          simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, ofReal_one, lintegral_const, MeasurableSet.univ,
            Measure.restrict_apply, univ_inter, one_mul, Nat.reduceDiv, pow_zero]
      _ < ⊤ :=
      by
        simp_all only [mem_Icc, norm_eq_abs, and_imp, sq_abs, Nat.reduceDiv, pow_zero, one_lt_top,h_measure_finite,Nat.cast_two,implies_true, Nat.cast_ofNat, one_div,ENNReal.ofReal_pow,lt_top_iff_ne_top]
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

--noncomputable def L2_norm (f : C₀) : ℝ := ENNReal.toReal (eLpNorm (fun x : Ic => f.1 x) 2 (volume:Measure Ic))

/-

instance : AddCommGroup C₀ where
  add := (· + ·)
  add_assoc := by
    intro a b c
    simp [add_assoc]
  zero_add := by intros; apply ContinuousMap.ext; simp
  add_zero := by intros; apply ContinuousMap.ext; simp
  neg := (- ·)
  --add_left_neg := by intros; apply ContinuousMap.ext; simp
  add_comm := by
    intro a b
    simp_all only
    --simp [add_comm]
    --連続関数の和が連続で、順番を取り替えても値が等しい。
    search_proof

instance : MetricSpace C₀ where
  dist f g := L2_norm_ext (f - g)
  dist_self f := by simp [L2_norm_ext, snorm_zero]
  dist_comm f g := by simp [L2_norm_ext, norm_sub_rev]
  dist_triangle f g h := by
    rw [← sub_add_sub_cancel]
    apply snorm_add_le (mem_L2_f_ext (f - g)) (mem_L2_f_ext (g - h))
  eq_of_dist_eq_zero := by
    intros f g hfg
    have : toFun f =ᵐ[volume] toFun g := snorm_eq_zero_iff.mp hfg
    apply ContinuousMap.ext
    intro x
    apply this.eq_of_mem

instance : NormedAddCommGroup C₀ where
  norm := L2_norm_ext
  dist_eq := rfl

instance : NormedAddCommGroup C₀ where
  norm f := L2_norm f
  dist f g := L2_norm (f - g)
  add_comm f :=
  dist_self f :=
  dist_comm :=
  dist_triangle :=
  eq_of_dist_eq_zero :=

-/

/-
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
  · apply ZeroMemClass.zero_mem --これがおかしい。
-/
/-
lemma LP2norm {F G : Lp ℝ 2 (volume : Measure ℝ)} {f g : C₀}
  (h_f : F = functionIntegrable f) (h_g : G = functionIntegrable g) :
  L2_distance_Ic f g = ‖F - G‖ :=
by
  have : ‖F - G‖ = 0 :=by
    subst h_f h_g
    simp_all only [norm_eq_zero]
    simp [functionIntegrable]

  -- `L2_distance_Ic` の定義を展開
  rw [L2_distance_Ic]
  -- `Lp` ノルムの定義を展開
  rw [MeasureTheory.Lp.norm_def]
  rw [← @Lp.norm_def]
  rw [h_f, h_g]
  dsimp [functionIntegrable]
  simp

  --rw [← Real.sqrt_sq (norm_nonneg (F - G))]
  -- `Lp` 空間の `p=2` の場合のノルム定義を適用
  --rw [MeasureTheory.Lp.norm_def]
  -- `functionIntegrable` の定義を代入
  sorry
-/
  /-消す
  rw [h_f, h_g]
  -- 積分の形が `L2_distance_Ic` の定義と一致することを確認
  simp only [Pi.sub_apply, Real.norm_eq_abs]

  #check eLpNorm
  #check MeasureTheory.Lp.norm_def

  dsimp [eLpNorm]
  --simp only [MeasureTheory.snorm_eq_snorm', MeasureTheory.snorm', ennreal.rpow_one_div]
  -- `functionIntegrable` の定義を代入
  rw [h_f, h_g]
  -- `Lp` 空間における距離の定義と `L2_distance_Ic` の定義が一致することを確認
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  -/

--定義を変更。
noncomputable def L2_distance_Ic (f g : C₀) : ℝ :=
   ‖(@mem_L2_f_ext (f-g)).toLp‖
  --Real.sqrt (∫ x in (Set.univ:Set Ic), (f.1 x - g.1 x) ^ 2)

--このままの形だと積分の中に積分が入っていることになるが、いいのか。
lemma LP2norm {f h : C₀} :
-- L2_distance_Ic f g = ‖(@mem_L2_f_ext f).toLp - (@mem_L2_f_ext g).toLp‖ :=
  L2_distance_Ic f h = ‖(@mem_L2_f_ext f).toLp-(@mem_L2_f_ext h).toLp‖ :=
by
  simp [L2_distance_Ic]
  dsimp [Memℒp.toLp]

  dsimp [Lp.norm_def]
  dsimp [eLpNorm ]
  simp
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  simp
  rw [lintegral_congr_ae]
  simp only [AEEqFun.coeFn_sub, sub_eq_add_neg]
  simp
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

  have fh_rw2': (toFun f + -toFun h) = toFun (f + -h) := by
    funext x
    simp_all only [Pi.add_apply, Pi.neg_apply]

  have fh_rw3: toFun (f + -h) = toFun (f - h):= by
    simp_all only [Pi.add_apply, Pi.neg_apply]
    rfl

  have ff_eq: ∀ ff:ℝ → ℝ, ff =ᵐ[volume] ff := by
    intro ff
    simp_all only [Pi.add_apply, Pi.neg_apply, EventuallyEq.refl]
  let tt := ff_eq (toFun (f + -h))

  have meas_f : Measurable (toFun f) := toFun_measurable f
  have ASf:AEStronglyMeasurable (toFun f) volume :=
  by
    exact meas_f |>.aestronglyMeasurable
  have : ↑(AEEqFun.mk (toFun f) ASf) =ᵐ[volume] (toFun f):= by
    simp_all only [Pi.add_apply, Pi.neg_apply]
    filter_upwards [AEEqFun.coeFn_mk _ ASf]
    intro a_1 a_2
    simp_all only

  have :  ∀ ff:ℝ → ℝ, (aesm:AEStronglyMeasurable ff) →  ↑(AEEqFun.mk ff aesm) =ᵐ[volume] ff := by
    intro ff aesm
    simp_all only [AEEqFun.coeFn_mk]

  have ae_lem:  ∀ ff:ℝ → ℝ, (aesm:AEStronglyMeasurable ff) → ∀ᵐ aa ∂volume, ‖↑((AEEqFun.mk ff aesm) aa)‖ₑ = ‖ff aa‖ₑ := by
    intro ff aesm
    filter_upwards [this ff aesm] with aa haa
    simp_all only [AEEqFun.coeFn_mk]

  let tta := ae_lem (toFun f) ASf
  have : ∀ᵐ aa ∂volume,‖toFun f aa‖ₑ = ‖(AEEqFun.mk (toFun f) ASf) aa‖ₑ := by
    filter_upwards [tta] with a ha
    simp_all only [Pi.add_apply, Pi.neg_apply]

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

  --have assum: ∀ᵐ aa ∂volume, ‖toFun (f + -h) aa‖ₑ = ‖ (AEEqFun.mk (toFun f + -toFun h) ASfh) aa‖ₑ := this

  rename_i this_5
  simp_all only [const_apply, Pi.add_apply, Pi.neg_apply]
  filter_upwards [this_5] with a ha
  simp_all only

lemma eLpNorm_neg_eq {f : ℝ → ℝ} :
  eLpNorm (λ x => - f x) 2 volume = eLpNorm f 2 volume :=
by
  dsimp [eLpNorm]
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]

  rw [lintegral_congr_ae]
  simp_all only [enorm_neg, toReal_ofNat, rpow_ofNat, EventuallyEq.refl]

--距離空間の公理を満たすためには、定義域を[0,1]に制限する必要がある。
noncomputable instance : MetricSpace C₀ where
  dist := by
   exact L2_distance_Ic

  dist_self f := by
    simp_all only
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
        simp only [neg_sub, sub_eq_add_neg]
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
    --hfgのルートをとるのに必要な部分。
    /-
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
    -/
    /-
    have ps2:(∫ x in (Set.univ:Set Ic), (f.1 x - g.1 x) ^ 2) = 0 :=
    by
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, ge_iff_le, sqrt_eq_zero, le_refl]

    have ps3:(∫ x in (Set.univ:Set Ic), ((f.1 - g.1) x) ^ 2) = 0 :=
    by
      simp_all only [Measure.restrict_univ, ContinuousMap.toFun_eq_coe, ge_iff_le, Pi.sub_apply]
    -/
    dsimp [eLpNorm] at hfg
    simp at hfg
    dsimp [eLpNorm'] at hfg
    unfold toFun at hfg
    simp at hfg
    --ここで関数の値をIc上とIc以外のところにわける。補題を作る。

    have h_integral_zero : ∫⁻ x in (Set.univ:Set Ic), ENNReal.ofReal ((f.1 x - g.1 x) ^ 2) = 0 :=
    by
      rw [piecewise_lem (f-g)]
      rw [zero_Ic_c_lem]

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
