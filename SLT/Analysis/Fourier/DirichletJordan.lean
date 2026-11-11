/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.Analysis.Fourier.DirichletKernel
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# The Dirichlet kernel against a monotone function: the Dirichlet–Jordan near part

For a monotone `φ : ℝ → ℝ` the near part `∫₀^δ (φ(t) − φ(0+)) D_M(t) dt` of the Dirichlet-kernel
integral vanishes as `M → ∞`. With the Stieltjes measure `μ` of the right-continuous
modification `F = rightLim φ` (`Monotone.stieltjesFunction`), `φ(t) − φ(0+) = μ((0, t])` off a
countable set, so by Fubini the near part is `∫_{(0,δ]} (∫_v^δ D_M) dμ(v)`; the inner integral is
`∫_{Mv}^{Mδ} sinc`, bounded uniformly (`Real.abs_integral_sinc_le`) and tending to `0` for every
`v > 0` (`Real.tendsto_integral_sinc`), so dominated convergence for the finite measure `μ((0,δ])`
finishes. This is the classical route to the Dirichlet–Jordan theorem: the Lipschitz
hypothesis of `tendsto_integral_mul_dirichletKer` is replaced by bounded variation.
-/

public section

open MeasureTheory Set Filter Topology Real Function
open scoped ENNReal

namespace Real

section Monotone

/-- `∫_{v}^{δ} D_M(t) dt = ∫_{Mv}^{Mδ} sinc`. -/
private theorem integral_dirichletKer_Ioc_eq (M v δ : ℝ) (hv : v ≤ δ) :
    ∫ t in Ioc v δ, dirichletKer M t = ∫ x in M * v..M * δ, sinc x := by
  rw [← intervalIntegral.integral_of_le hv]
  unfold dirichletKer
  rw [intervalIntegral.integral_const_mul, ← smul_eq_mul,
    intervalIntegral.smul_integral_comp_mul_left]

/-- The uniform bound on `∫_{a}^{b} sinc`. -/
private theorem abs_integral_sinc_interval_le (a b : ℝ) :
    |∫ x in a..b, sinc x| ≤ 2 * (π / 2 + 2) := by
  have hab : IntervalIntegrable sinc volume 0 b := continuous_sinc.intervalIntegrable _ _
  have hac : IntervalIntegrable sinc volume 0 a := continuous_sinc.intervalIntegrable _ _
  rw [← intervalIntegral.integral_interval_sub_left hab hac]
  calc |(∫ x in (0 : ℝ)..b, sinc x) - ∫ x in (0 : ℝ)..a, sinc x|
      ≤ |∫ x in (0 : ℝ)..b, sinc x| + |∫ x in (0 : ℝ)..a, sinc x| := abs_sub _ _
    _ ≤ (π / 2 + 2) + (π / 2 + 2) := add_le_add (abs_integral_sinc_le b) (abs_integral_sinc_le a)
    _ = 2 * (π / 2 + 2) := by ring

/-- `∫_{Mv}^{Mδ} sinc → 0` as `M → ∞` for fixed `0 < v ≤ δ`. -/
private theorem tendsto_integral_sinc_interval {v δ : ℝ} (hv : 0 < v) (hδ : 0 < δ) :
    Tendsto (fun M : ℝ ↦ ∫ x in M * v..M * δ, sinc x) atTop (𝓝 0) := by
  have h1 := tendsto_integral_sinc.comp (tendsto_id.atTop_mul_const hδ)
  have h2 := tendsto_integral_sinc.comp (tendsto_id.atTop_mul_const hv)
  have := h1.sub h2
  rw [sub_self] at this
  refine this.congr fun M ↦ ?_
  simp only [Function.comp]
  exact intervalIntegral.integral_interval_sub_left (continuous_sinc.intervalIntegrable _ _)
    (continuous_sinc.intervalIntegrable _ _)

variable {φ : ℝ → ℝ}

/-- A monotone function agrees with its right limit off a countable set, hence a.e. -/
private theorem monotone_ae_eq_rightLim (hφ : Monotone φ) : φ =ᵐ[volume] rightLim φ := by
  have hc : {x | ¬ContinuousAt φ x}.Countable := hφ.countable_not_continuousAt
  refine (hc.measure_zero volume) |> fun h0 ↦ ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx ↦ ?_) h0
  intro hcont
  exact hx ((hcont.continuousWithinAt).rightLim_eq).symm

/-- **The Dirichlet–Jordan near part for a monotone function**:
`∫₀^δ (φ(t) − φ(0+)) D_M(t) dt → 0`. -/
private theorem tendsto_integral_monotone_sub_rightLim_mul_dirichletKer (hφ : Monotone φ) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (φ t - rightLim φ 0) * dirichletKer M t) atTop
      (𝓝 0) := by
  classical
  set F : StieltjesFunction ℝ := hφ.stieltjesFunction with hF
  set μ : Measure ℝ := F.measure with hμ
  have hFeq : ∀ x, F x = rightLim φ x := fun x ↦ rfl
  -- the finite measure `μ` on `(0, δ]`
  have hμδ : μ (Ioc 0 δ) < ∞ := by
    rw [hμ, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (μ.restrict (Ioc 0 δ)) := isFiniteMeasure_restrict.mpr hμδ.ne
  -- `F t − F 0 = μ((0, t])` for `t ≥ 0`
  have hincr : ∀ t, 0 ≤ t → F t - F 0 = (μ (Ioc 0 t)).toReal := by
    intro t ht
    rw [hμ, StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono ht))]
  -- `μ((0, t]) = ∫ 1_{(0,t]} dμ|_{(0,δ]}` for `t ≤ δ`
  have hind : ∀ t ∈ Ioc (0 : ℝ) δ,
      (μ (Ioc 0 t)).toReal = ∫ v, (Ioc (0 : ℝ) t).indicator 1 v ∂(μ.restrict (Ioc 0 δ)) := by
    intro t ht
    rw [integral_indicator_one measurableSet_Ioc, measureReal_def,
      Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioc_right ht.2)]
  -- the a.e. rewriting of the near part
  have hae : ∀ M, ∫ t in Ioc (0 : ℝ) δ, (φ t - rightLim φ 0) * dirichletKer M t
      = ∫ t in Ioc (0 : ℝ) δ, (∫ v, (Ioc (0 : ℝ) t).indicator 1 v ∂(μ.restrict (Ioc 0 δ)))
          * dirichletKer M t := by
    intro M
    have h1 : (fun t ↦ (φ t - rightLim φ 0) * dirichletKer M t)
        =ᵐ[volume.restrict (Ioc 0 δ)] fun t ↦ (F t - F 0) * dirichletKer M t := by
      have := monotone_ae_eq_rightLim hφ
      filter_upwards [ae_restrict_of_ae this] with t ht
      rw [ht]
      simp only [hFeq]
    rw [integral_congr_ae h1]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    rw [hincr t ht.1.le, hind t ht]
  simp_rw [hae]
  -- Fubini
  have hK : ∀ M, Integrable
      (fun p : ℝ × ℝ ↦ (Ioc (0 : ℝ) p.1).indicator 1 p.2 * dirichletKer M p.1)
      ((volume.restrict (Ioc (0 : ℝ) δ)).prod (μ.restrict (Ioc 0 δ))) := by
    intro M
    have hmeas : Measurable fun p : ℝ × ℝ ↦ (Ioc (0 : ℝ) p.1).indicator (1 : ℝ → ℝ) p.2
        * dirichletKer M p.1 := by
      have hset : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioc (0 : ℝ) p.1} := by
        have : {p : ℝ × ℝ | p.2 ∈ Ioc (0 : ℝ) p.1} = {p : ℝ × ℝ | 0 < p.2} ∩ {p | p.2 ≤ p.1} := by
          ext p; simp [mem_Ioc]
        rw [this]
        exact (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst)
      have : (fun p : ℝ × ℝ ↦ (Ioc (0 : ℝ) p.1).indicator (1 : ℝ → ℝ) p.2 * dirichletKer M p.1)
          = fun p ↦ {p : ℝ × ℝ | p.2 ∈ Ioc (0 : ℝ) p.1}.indicator
            (fun p ↦ dirichletKer M p.1) p := by
        funext p
        by_cases hp : p.2 ∈ Ioc (0 : ℝ) p.1
        · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 ∈ Ioc (0 : ℝ) p.1}
            from hp), Pi.one_apply, one_mul]
        · rw [indicator_of_notMem hp, indicator_of_notMem
            (show p ∉ {p : ℝ × ℝ | p.2 ∈ Ioc (0 : ℝ) p.1} from hp), zero_mul]
      rw [this]
      exact ((continuous_dirichletKer M).measurable.comp measurable_fst).indicator hset
    refine (integrable_const |M|).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun p ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |(Ioc (0 : ℝ) p.1).indicator (1 : ℝ → ℝ) p.2| * |dirichletKer M p.1|
        ≤ 1 * |M| := by
          refine mul_le_mul ?_ (abs_dirichletKer_le M _) (abs_nonneg _) zero_le_one
          by_cases hp : p.2 ∈ Ioc (0 : ℝ) p.1 <;> simp [hp]
      _ = |M| := one_mul _
  have hswap : ∀ M,
      ∫ t in Ioc (0 : ℝ) δ, (∫ v, (Ioc (0 : ℝ) t).indicator 1 v ∂(μ.restrict (Ioc 0 δ)))
        * dirichletKer M t
      = ∫ v in Ioc (0 : ℝ) δ,
          ∫ t in Ioc (0 : ℝ) δ, (Ioc (0 : ℝ) t).indicator 1 v * dirichletKer M t ∂volume ∂μ := by
    intro M
    have := integral_integral_swap
      (f := fun t v ↦ (Ioc (0 : ℝ) t).indicator (1 : ℝ → ℝ) v * dirichletKer M t) (hK M)
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    rw [integral_mul_const]
  simp_rw [hswap]
  -- the inner integral is `∫_{Mv}^{Mδ} sinc` for `v ∈ (0, δ]`
  have hinner : ∀ M, ∀ v ∈ Ioc (0 : ℝ) δ,
      ∫ t in Ioc (0 : ℝ) δ, (Ioc (0 : ℝ) t).indicator 1 v * dirichletKer M t
        = ∫ x in M * v..M * δ, sinc x := by
    intro M v hv
    have hsub : Icc v δ ⊆ Ioc (0 : ℝ) δ := fun t ht ↦ ⟨hv.1.trans_le ht.1, ht.2⟩
    rw [← integral_dirichletKer_Ioc_eq M v δ hv.2]
    conv_rhs => rw [← integral_Icc_eq_integral_Ioc, ← inter_eq_right.mpr hsub,
      ← setIntegral_indicator measurableSet_Icc]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    by_cases htv : v ≤ t
    · have h1 : v ∈ Ioc (0 : ℝ) t := ⟨hv.1, htv⟩
      have h2 : t ∈ Icc v δ := ⟨htv, ht.2⟩
      simp [indicator_of_mem h1, indicator_of_mem h2]
    · have h1 : v ∉ Ioc (0 : ℝ) t := fun h ↦ htv h.2
      have h2 : t ∉ Icc v δ := fun h ↦ htv h.1
      simp [indicator_of_notMem h1, indicator_of_notMem h2]
  -- dominated convergence in `M`
  have hbound : ∀ M, ∀ v ∈ Ioc (0 : ℝ) δ, ‖∫ x in M * v..M * δ, sinc x‖ ≤ 2 * (π / 2 + 2) :=
    fun M v _ ↦ by rw [Real.norm_eq_abs]; exact abs_integral_sinc_interval_le _ _
  have hlim : ∀ v ∈ Ioc (0 : ℝ) δ,
      Tendsto (fun M : ℝ ↦ ∫ x in M * v..M * δ, sinc x) atTop (𝓝 0) :=
    fun v hv ↦ tendsto_integral_sinc_interval hv.1 hδ
  have hcont : ∀ M, Continuous fun v : ℝ ↦ ∫ x in M * v..M * δ, sinc x := by
    intro M
    have h1 : Continuous fun b : ℝ ↦ ∫ x in (0 : ℝ)..b, sinc x :=
      intervalIntegral.continuous_primitive (fun a b ↦ continuous_sinc.intervalIntegrable a b) 0
    have : (fun v : ℝ ↦ ∫ x in M * v..M * δ, sinc x)
        = fun v ↦ (∫ x in (0 : ℝ)..M * δ, sinc x) - ∫ x in (0 : ℝ)..M * v, sinc x := by
      funext v
      rw [intervalIntegral.integral_interval_sub_left (continuous_sinc.intervalIntegrable _ _)
        (continuous_sinc.intervalIntegrable _ _)]
    rw [this]
    exact continuous_const.sub (h1.comp (continuous_const.mul continuous_id))
  have hdom := tendsto_integral_filter_of_dominated_convergence (μ := μ.restrict (Ioc 0 δ))
    (F := fun (M : ℝ) v ↦ ∫ x in M * v..M * δ, sinc x) (f := fun _ ↦ (0 : ℝ))
    (fun _ ↦ 2 * (π / 2 + 2))
    (Eventually.of_forall fun M ↦ (hcont M).aestronglyMeasurable)
    (Eventually.of_forall fun M ↦ ae_restrict_of_forall_mem measurableSet_Ioc (hbound M))
    (integrable_const _) (ae_restrict_of_forall_mem measurableSet_Ioc hlim)
  simp only [integral_zero] at hdom
  refine hdom.congr fun M ↦ ?_
  exact setIntegral_congr_fun measurableSet_Ioc fun v hv ↦ (hinner M v hv).symm

end Monotone

section BoundedVariation

/-- The clamped extension of a function on `[a, b]` to `ℝ`. -/
private noncomputable def clampExt (a b : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ := p (max a (min b x))

private theorem clampExt_of_mem {a b : ℝ} (p : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc a b) :
    clampExt a b p x = p x := by
  unfold clampExt
  rw [min_eq_right hx.2, max_eq_right hx.1]

private theorem monotone_clampExt {a b : ℝ} (hab : a ≤ b) {p : ℝ → ℝ}
    (hp : MonotoneOn p (Icc a b)) :
    Monotone (clampExt a b p) := by
  intro x y hxy
  unfold clampExt
  have hmem : ∀ z, max a (min b z) ∈ Icc a b := fun z ↦
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  exact hp (hmem x) (hmem y) (max_le_max le_rfl (min_le_min le_rfl hxy))

/-- **Jordan decomposition with monotone pieces on `ℝ`**: a function of bounded variation on
`[a, b]` agrees there with the difference of two monotone functions on `ℝ`. -/
theorem _root_.BoundedVariationOn.exists_monotone_sub_monotone {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hbv : BoundedVariationOn g (Icc a b)) :
    ∃ p q : ℝ → ℝ, Monotone p ∧ Monotone q ∧ ∀ x ∈ Icc a b, g x = p x - q x := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn hbv.locallyBoundedVariationOn
  refine ⟨clampExt a b p, clampExt a b q, monotone_clampExt hab hp, monotone_clampExt hab hq,
    fun x hx ↦ ?_⟩
  rw [clampExt_of_mem p hx, clampExt_of_mem q hx, hpq]
  rfl

/-- A monotone function is bounded on `[a, b]` by `|p b| + |p a|`. -/
theorem _root_.Monotone.abs_le_of_mem {p : ℝ → ℝ} (hp : Monotone p) {a b t : ℝ} (ht : t ∈ Icc a b) :
    |p t| ≤ |p b| + |p a| := by
  have h1 := hp ht.1
  have h2 := hp ht.2
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (p b), le_abs_self (p b), neg_abs_le (p a),
    le_abs_self (p a), abs_nonneg (p a), abs_nonneg (p b)]

/-- The shift `t ↦ r + t` maps `𝓝[>] 0` to `𝓝[>] r`. -/
private theorem tendsto_add_nhdsGT (r : ℝ) : Tendsto (fun t : ℝ ↦ r + t) (𝓝[>] 0) (𝓝[>] r) := by
  refine Tendsto.inf ?_ (tendsto_principal_principal.mpr fun t ht ↦ ?_)
  · have : Tendsto (fun t : ℝ ↦ r + t) (𝓝 0) (𝓝 (r + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    simpa using this
  · exact lt_add_of_pos_right r ht

/-- The reflection `x ↦ 2r − x` maps `𝓝[>] r` to `𝓝[<] r`. -/
private theorem tendsto_reflect_nhdsGT (r : ℝ) :
    Tendsto (fun x : ℝ ↦ 2 * r - x) (𝓝[>] r) (𝓝[<] r) := by
  refine Tendsto.inf ?_ (tendsto_principal_principal.mpr fun x hx ↦ ?_)
  · have : Tendsto (fun x : ℝ ↦ 2 * r - x) (𝓝 r) (𝓝 (2 * r - r)) :=
      (continuous_const.sub continuous_id).tendsto r
    simpa [two_mul] using this
  · change 2 * r - x < r
    linarith [show r < x from hx]

/-- **The Dirichlet–Jordan near part on the right**: for `g` of bounded variation on
`[r − δ, r + δ]` with right limit `g(r+) = gp`, `∫₀^δ (g(r + t) − gp) D_M(t) dt → 0`. -/
theorem tendsto_near_right_of_boundedVariationOn {g : ℝ → ℝ} {r δ gp : ℝ} (hδ : 0 < δ)
    (hbv : BoundedVariationOn g (Icc (r - δ) (r + δ))) (hgp : Tendsto g (𝓝[>] r) (𝓝 gp)) :
    Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g (r + t) - gp) * dirichletKer M t) atTop
      (𝓝 0) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn hbv.locallyBoundedVariationOn
  have hab : r - δ ≤ r + δ := by linarith
  set φ₁ : ℝ → ℝ := fun t ↦ clampExt (r - δ) (r + δ) p (r + t) with hφ₁
  set φ₂ : ℝ → ℝ := fun t ↦ clampExt (r - δ) (r + δ) q (r + t) with hφ₂
  have hm₁ : Monotone φ₁ := (monotone_clampExt hab hp).comp fun x y hxy ↦ by
    simpa using hxy
  have hm₂ : Monotone φ₂ := (monotone_clampExt hab hq).comp fun x y hxy ↦ by
    simpa using hxy
  -- `g(r + t) = φ₁ t − φ₂ t` on `(0, δ]`
  have hg_eq : ∀ t ∈ Ioc (0 : ℝ) δ, g (r + t) = φ₁ t - φ₂ t := by
    intro t ht
    have hmem : r + t ∈ Icc (r - δ) (r + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp only [hφ₁, hφ₂, clampExt_of_mem p hmem, clampExt_of_mem q hmem]
    rw [hpq]
    rfl
  -- the right limit of `g` at `r` is `rightLim φ₁ 0 − rightLim φ₂ 0`
  have hlim : gp = rightLim φ₁ 0 - rightLim φ₂ 0 := by
    have h1 : Tendsto (fun t ↦ g (r + t)) (𝓝[>] 0) (𝓝 gp) := hgp.comp (tendsto_add_nhdsGT r)
    have h2 : Tendsto (fun t ↦ φ₁ t - φ₂ t) (𝓝[>] 0) (𝓝 (rightLim φ₁ 0 - rightLim φ₂ 0)) :=
      (hm₁.tendsto_rightLim 0).sub (hm₂.tendsto_rightLim 0)
    have h3 : Tendsto (fun t ↦ g (r + t)) (𝓝[>] 0) (𝓝 (rightLim φ₁ 0 - rightLim φ₂ 0)) := by
      refine h2.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      exact (hg_eq t ⟨ht.1, ht.2.le⟩).symm
    exact tendsto_nhds_unique h1 h3
  have e : ∀ M, ∫ t in Ioc (0 : ℝ) δ, (g (r + t) - gp) * dirichletKer M t
      = (∫ t in Ioc (0 : ℝ) δ, (φ₁ t - rightLim φ₁ 0) * dirichletKer M t)
        - ∫ t in Ioc (0 : ℝ) δ, (φ₂ t - rightLim φ₂ 0) * dirichletKer M t := by
    intro M
    have hD : IntegrableOn (dirichletKer M) (Ioc 0 δ) :=
      ((continuous_dirichletKer M).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hint : ∀ (φ : ℝ → ℝ) (c : ℝ), Monotone φ →
        IntegrableOn (fun t ↦ (φ t - c) * dirichletKer M t) (Ioc 0 δ) := by
      intro φ c hφ
      have hb : ∀ t ∈ Ioc (0 : ℝ) δ, |φ t - c| ≤ |φ δ| + |φ 0| + |c| := by
        intro t ht
        have h1 := hφ ht.1.le
        have h2 := hφ ht.2
        calc |φ t - c| ≤ |φ t| + |c| := abs_sub _ _
          _ ≤ (|φ δ| + |φ 0|) + |c| := by
              have : |φ t| ≤ |φ δ| + |φ 0| := by
                rw [abs_le]
                constructor <;> linarith [neg_abs_le (φ δ), le_abs_self (φ δ), neg_abs_le (φ 0),
                  le_abs_self (φ 0), abs_nonneg (φ δ), abs_nonneg (φ 0)]
              linarith
      refine (hD.norm.const_mul (|φ δ| + |φ 0| + |c|)).mono' ?_ ?_
      · exact ((hφ.measurable.sub measurable_const).mul
          (continuous_dirichletKer M).measurable).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hb t ht) (norm_nonneg _)
    rw [← integral_sub (hint φ₁ _ hm₁) (hint φ₂ _ hm₂)]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    rw [hg_eq t ht, hlim]
    ring
  simp_rw [e]
  have := (tendsto_integral_monotone_sub_rightLim_mul_dirichletKer hm₁ hδ).sub
    (tendsto_integral_monotone_sub_rightLim_mul_dirichletKer hm₂ hδ)
  simpa using this

/-- **The Dirichlet–Jordan near part on the left**, by reflection. -/
theorem tendsto_near_left_of_boundedVariationOn {g : ℝ → ℝ} {r δ gm : ℝ} (hδ : 0 < δ)
    (hbv : BoundedVariationOn g (Icc (r - δ) (r + δ))) (hgm : Tendsto g (𝓝[<] r) (𝓝 gm)) :
    Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g (r - t) - gm) * dirichletKer M t) atTop
      (𝓝 0) := by
  -- the reflected function `g̃(x) = g(2r − x)` has bounded variation and right limit `gm`
  set g' : ℝ → ℝ := fun x ↦ g (2 * r - x) with hg'
  have hbv' : BoundedVariationOn g' (Icc (r - δ) (r + δ)) := by
    unfold BoundedVariationOn at hbv ⊢
    refine ne_top_of_le_ne_top hbv ?_
    have hanti : AntitoneOn (fun x : ℝ ↦ 2 * r - x) (Icc (r - δ) (r + δ)) :=
      fun x _ y _ hxy ↦ by simp only; linarith
    have hmaps : MapsTo (fun x : ℝ ↦ 2 * r - x) (Icc (r - δ) (r + δ)) (Icc (r - δ) (r + δ)) :=
      fun x hx ↦ ⟨by linarith [hx.2], by linarith [hx.1]⟩
    exact eVariationOn.comp_le_of_antitoneOn g _ hanti hmaps
  have hgp' : Tendsto g' (𝓝[>] r) (𝓝 gm) := hgm.comp (tendsto_reflect_nhdsGT r)
  have h := tendsto_near_right_of_boundedVariationOn hδ hbv' hgp'
  refine h.congr fun M ↦ setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
  simp only [hg']
  congr 3
  ring

/-- **The Dirichlet–Jordan theorem for the kernel**: for integrable `g` of bounded variation on
`[r − δ, r + δ]` with one-sided limits `g(r±)`,
`∫ g(v) sin(M(v−r))/(v−r) dv → (π/2)(g(r+) + g(r−))`. -/
theorem tendsto_integral_mul_dirichletKer_of_boundedVariationOn {g : ℝ → ℝ} (hg : Integrable g)
    {r δ gp gm : ℝ} (hδ : 0 < δ) (hbv : BoundedVariationOn g (Icc (r - δ) (r + δ)))
    (hgp : Tendsto g (𝓝[>] r) (𝓝 gp)) (hgm : Tendsto g (𝓝[<] r) (𝓝 gm)) :
    Tendsto (fun M : ℝ ↦ ∫ v, g v * dirichletKer M (v - r)) atTop (𝓝 (π / 2 * (gp + gm))) :=
  tendsto_integral_mul_dirichletKer_of_near hg r hδ
    (tendsto_near_right_of_boundedVariationOn hδ hbv hgp)
    (tendsto_near_left_of_boundedVariationOn hδ hbv hgm)

end BoundedVariation

end Real
