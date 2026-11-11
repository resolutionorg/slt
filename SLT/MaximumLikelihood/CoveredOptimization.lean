/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.OptimizerFaces
public import SLT.MaximumLikelihood.Assembly
import SLT.MaximumLikelihood.Envelope
public import SLT.MaximumLikelihood.Geometry
import SLT.FreeEnergy.Discharge
import SLT.Probability.Moments.EmpiricalSumEven
public import SLT.FreeEnergy.SamplewiseResolution
import SLT.EmpiricalProcess.Modification
public import SLT.FreeEnergy.FundamentalConditions
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Ring.IsFormallyReal
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Optimizers on the covered parameter set

Reduce positive-sublevel coverage to the full-coverage MLE API by removing only
zero-energy parameters outside the compact union of chart images. Replacing the
estimator at zero energy preserves its errors almost surely.
-/

public section

namespace SingularLearningTheory

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {d : ℕ}

namespace ResolutionAtlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- The compact feasible set seen by the optimizer atlas: all its chart images,
plus the original high-energy tail. -/
@[expose] def coveredSet (δ : ℝ) : Set (Fin d → ℝ) :=
  (⋃ α, R.g α '' cube d (R.b α)) ∪ {w | w ∈ W ∧ δ ≤ K w}

theorem coveredSet_subset (δ : ℝ) : R.coveredSet δ ⊆ W := by
  rintro w (hw | hw)
  · obtain ⟨α, u, hu, rfl⟩ := Set.mem_iUnion.mp hw
    exact R.g_mapsTo α hu
  · exact hw.1

theorem chart_mem_coveredSet (δ : ℝ) (α : R.ι) {u : Fin d → ℝ} (hu : u ∈ cube d (R.b α)) :
    R.g α u ∈ R.coveredSet δ :=
  Or.inl (Set.mem_iUnion.mpr ⟨α, u, hu, rfl⟩)

theorem isCompact_coveredSet (δ : ℝ) (hW : IsCompact W) (hK : ContinuousOn K W) :
    IsCompact (R.coveredSet δ) := by
  have hcharts : IsCompact (⋃ α, R.g α '' cube d (R.b α)) :=
    isCompact_iUnion fun α ↦
      isCompact_Icc.image_of_continuousOn
        (R.g_analytic α).continuousOn
  have htail : IsCompact {w | w ∈ W ∧ δ ≤ K w} := by
    change IsCompact (W ∩ K ⁻¹' Ici δ)
    exact hW.of_isClosed_subset
      (hK.preimage_isClosed_of_isClosed hW.isClosed isClosed_Ici) inter_subset_left
  exact hcharts.union htail

theorem positive_mem_coveredSet {δ : ℝ}
    (hcover : ∀ w ∈ W, 0 < K w → K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    {w : Fin d → ℝ} (hw : w ∈ W) (hKpos : 0 < K w) : w ∈ R.coveredSet δ := by
  by_cases hlow : K w < δ
  · obtain ⟨α, u, rfl⟩ := hcover w hw hKpos hlow
    exact R.chart_mem_coveredSet δ α u.2
  · exact Or.inr ⟨hw, le_of_not_gt hlow⟩

/-- Full low-sublevel coverage is automatic on coveredSet, including its zeros. -/
theorem coveredSet_cover {δ : ℝ} {w : Fin d → ℝ}
    (hw : w ∈ R.coveredSet δ) (hlow : K w < δ) :
    ∃ α, ∃ u : cube d (R.b α), R.g α u = w := by
  rcases hw with hw | hw
  · obtain ⟨α, u, hu, hgu⟩ := Set.mem_iUnion.mp hw
    exact ⟨α, ⟨u, hu⟩, hgu⟩
  · exact False.elim ((not_lt_of_ge hw.2) hlow)

/-- The same chart geometry, now viewed over the covered compact feasible set.
The zero prior lets the unchanged statistical API consume this auxiliary atlas. -/
@[expose] noncomputable def coveredAtlas (δ : ℝ) : ResolutionAtlas K (fun _ ↦ 0) (R.coveredSet δ) :=
  optimizerZeroPriorAtlas R.b R.b_pos R.k R.active R.g R.g_analytic R.g_measurable
    (fun α _ hu ↦ R.chart_mem_coveredSet δ α hu) R.monomial

theorem coveredAtlas_cover {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ w ∈ R.coveredSet δ, K w < η →
      ∃ α, ∃ u : cube d ((R.coveredAtlas δ).b α), (R.coveredAtlas δ).g α u = w :=
  ⟨δ, hδ, fun _ hw hk ↦ R.coveredSet_cover hw hk⟩

theorem zero_mem_cube (α : R.ι) : (0 : Fin d → ℝ) ∈ cube d (R.b α) :=
  ⟨fun _ ↦ le_rfl, fun _ ↦ (R.b_pos α).le⟩

theorem K_chart_origin (α : R.ι) : K (R.g α 0) = 0 := by
  rw [R.monomial α 0 (R.zero_mem_cube α)]
  obtain ⟨j, hj⟩ := R.active α
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by
    simp [show 2 * R.k α j ≠ 0 by omega])

variable {X : Type*} [MeasurableSpace X] {q : Measure X}
  {f : X → (Fin d → ℝ) → ℝ} {s : ℝ≥0∞}

variable {R} in
/-- Coefficient fields and their expansions do not change under this restriction. -/
@[expose] noncomputable def AnalyticResolvedLikelihood.coveredLikelihood (δ : ℝ)
    (L : R.AnalyticResolvedLikelihood s q f) :
    (R.coveredAtlas δ).AnalyticResolvedLikelihood s q f where
  a := L.a
  a_measurable := L.a_measurable
  factor := L.factor
  mean := L.mean
  memLp := L.memLp
  loc := L.loc

end ResolutionAtlas

/-- Restrict the feasible set while retaining the same ambient analytic extension. -/
theorem FundamentalConditionI.monoSet
    {X : Type*} [MeasurableSpace X] {q : Measure X}
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {K : (Fin d → ℝ) → ℝ}
    {f : X → (Fin d → ℝ) → ℝ} {W V : Set (Fin d → ℝ)}
    (I : FundamentalConditionI s q f K W) (hVW : V ⊆ W) :
    FundamentalConditionI s q f K V := by
  obtain ⟨U, hU, hWU, F, hF, hFf⟩ := I.ls_analytic
  exact ⟨I.two_le, I.K_eq, U, hU, hVW.trans hWU, F, hF, hFf⟩

/-- Continuous sections turn pointwise almost-sure zero identities into one
common event. This includes isolated and lower-dimensional feasible zeros. -/
private theorem ae_forall_zero_of_continuousOn
    {X : Type*} [MeasurableSpace X] {q : Measure X}
    {T : Set (Fin d → ℝ)} {f : X → (Fin d → ℝ) → ℝ}
    (hc : ∀ᵐ x ∂q, ContinuousOn (f x) T)
    (hzero : ∀ w ∈ T, ∀ᵐ x ∂q, f x w = 0) :
    ∀ᵐ x ∂q, ∀ w ∈ T, f x w = 0 := by
  obtain ⟨D, hDT, hDc, hTD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace T).exists_countable_dense_subset
  have hD : ∀ᵐ x ∂q, ∀ w ∈ D, f x w = 0 :=
    (ae_ball_iff hDc).mpr fun w hw ↦ hzero w (hDT hw)
  filter_upwards [hc, hD] with x hcx hx
  exact EqOn.of_subset_closure hx hcx continuousOn_const hDT hTD

/-- RFV plus square integrability supplies the common zero section. -/
private theorem ae_forall_zero_of_relative_second_moment
    {X : Type*} [MeasurableSpace X] {q : Measure X}
    {K : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {f : X → (Fin d → ℝ) → ℝ} {C : ℝ}
    (hc : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    (hi : ∀ w ∈ W, Integrable (fun x ↦ f x w ^ 2) q)
    (hb : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C * K w) :
    ∀ᵐ x ∂q, ∀ w ∈ W, K w = 0 → f x w = 0 := by
  have hz := ae_forall_zero_of_continuousOn
    (T := {w | w ∈ W ∧ K w = 0})
    (hc.mono fun x hx ↦ hx.mono fun _ hw ↦ hw.1) (fun w hw ↦ by
      have hI : ∫ x, f x w ^ 2 ∂q = 0 := by
        refine le_antisymm ?_ (integral_nonneg fun x ↦ sq_nonneg _)
        simpa [hw.2] using hb w hw.1
      have hs := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (f x w))
        (hi w hw.1)).mp hI
      filter_upwards [hs] with x hx
      have hx' : f x w ^ 2 = 0 := hx
      exact sq_eq_zero_iff.mp hx')
  filter_upwards [hz] with x hx w hw hKw
  exact hx w ⟨hw, hKw⟩

private theorem empiricalLoss_zero_of_ae_zero
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {q : Measure X} {P : Measure Ω} {Xs : ℕ → Ω → X}
    {K : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} {f : X → (Fin d → ℝ) → ℝ}
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hz : ∀ᵐ x ∂q, ∀ w ∈ W, K w = 0 → f x w = 0) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ w ∈ W, K w = 0 → empiricalLoss f Xs n ω w = 0 := by
  filter_upwards [ae_forall_range_comp hX hlaw hz n] with ω hω w hw hKw
  have hsum : (∑ i ∈ Finset.range n, f (Xs i ω) w) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ hω i hi w hw hKw
  simp [empiricalLoss, hsum]

namespace MaximumLikelihood

/-- A deterministic replacement on the zero-energy event. -/
private noncomputable def repairZero (K : (Fin d → ℝ) → ℝ) (z w : Fin d → ℝ) : Fin d → ℝ :=
  if K w = 0 then z else w

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- The repaired estimator lies in the covered set and has exactly the same
energy and objective. This is a deterministic statement about one sample. -/
private theorem repairZero_properties {δ : ℝ}
    (hcover : ∀ w ∈ W, 0 < K w → K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    (hK : ∀ w ∈ W, 0 ≤ K w) {S : (Fin d → ℝ) → ℝ}
    (hzero : ∀ w ∈ W, K w = 0 → S w = 0)
    {z : Fin d → ℝ} (hz : z ∈ R.coveredSet δ) (hzK : K z = 0)
    {w : Fin d → ℝ} (hw : w ∈ W) (hmin : ∀ v ∈ W, S w ≤ S v) :
    repairZero K z w ∈ R.coveredSet δ ∧
      K (repairZero K z w) = K w ∧ S (repairZero K z w) = S w ∧
      ∀ v ∈ R.coveredSet δ, S (repairZero K z w) ≤ S v := by
  have hzW : z ∈ W := R.coveredSet_subset δ hz
  by_cases hKw : K w = 0
  · have hSz : S z = S w := (hzero z hzW hzK).trans (hzero w hw hKw).symm
    simp only [repairZero, if_pos hKw]
    refine ⟨hz, hzK.trans hKw.symm, hSz, fun v hv ↦ ?_⟩
    rw [hSz]
    exact hmin v (R.coveredSet_subset δ hv)
  · have hKpos : 0 < K w := lt_of_le_of_ne (hK w hw) (Ne.symm hKw)
    simp only [repairZero, if_neg hKw, true_and]
    exact ⟨R.positive_mem_coveredSet hcover hw hKpos,
      fun v hv ↦ hmin v (R.coveredSet_subset δ hv)⟩

private theorem measurable_repairZero
    {Ω : Type*} [MeasurableSpace Ω] (hK : Measurable K)
    (z : Fin d → ℝ) {w : Ω → Fin d → ℝ} (hw : Measurable w) :
    Measurable fun ω ↦ repairZero K z (w ω) := by
  classical
  exact Measurable.ite (measurableSet_eq_fun (hK.comp hw) measurable_const)
    measurable_const hw

/-- Directly usable inputs for the unchanged full-cover MLE theorem. Choosing
any chart origin supplies z, hz and hzK. -/
private theorem repaired_estimator_inputs
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure Ω} {Xs : ℕ → Ω → X} {f : X → (Fin d → ℝ) → ℝ}
    {δ : ℝ} (hcover : ∀ w ∈ W, 0 < K w → K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    (hK : ∀ w ∈ W, 0 ≤ K w) (hKm : Measurable K)
    (hzero : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W, K w = 0 → empiricalLoss f Xs n ω w = 0)
    {z : Fin d → ℝ} (hz : z ∈ R.coveredSet δ) (hzK : K z = 0)
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n : ℕ, Measurable (ŵ n))
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      empiricalLoss f Xs n ω (ŵ n ω) ≤ empiricalLoss f Xs n ω w) :
    let ŵc := fun (n : ℕ) ω ↦ repairZero K z (ŵ n ω)
    (∀ n : ℕ, Measurable (ŵc n)) ∧
      (∀ n : ℕ, ∀ᵐ ω ∂P, ŵc n ω ∈ R.coveredSet δ) ∧
      (∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ R.coveredSet δ,
        empiricalLoss f Xs n ω (ŵc n ω) ≤ empiricalLoss f Xs n ω w) ∧
      (∀ n : ℕ, (fun ω ↦ K (ŵc n ω)) =ᵐ[P] fun ω ↦ K (ŵ n ω)) ∧
      (∀ n : ℕ, (fun ω ↦ empiricalLoss f Xs n ω (ŵc n ω)) =ᵐ[P]
        fun ω ↦ empiricalLoss f Xs n ω (ŵ n ω)) := by
  dsimp only
  have hall : ∀ n : ℕ, ∀ᵐ ω ∂P,
      repairZero K z (ŵ n ω) ∈ R.coveredSet δ ∧
      K (repairZero K z (ŵ n ω)) = K (ŵ n ω) ∧
      empiricalLoss f Xs n ω (repairZero K z (ŵ n ω)) = empiricalLoss f Xs n ω (ŵ n ω) ∧
      ∀ w ∈ R.coveredSet δ,
        empiricalLoss f Xs n ω (repairZero K z (ŵ n ω)) ≤ empiricalLoss f Xs n ω w := by
    intro n
    filter_upwards [hzero n, hŵW n, hmin n] with ω hω0 hωW hωmin
    exact repairZero_properties R hcover hK hω0 hz hzK hωW hωmin
  exact ⟨fun n ↦ measurable_repairZero hKm z (hŵ n),
    fun n ↦ (hall n).mono fun _ h ↦ h.1,
    fun n ↦ (hall n).mono fun _ h ↦ h.2.2.2,
    fun n ↦ (hall n).mono fun _ h ↦ h.2.1,
    fun n ↦ (hall n).mono fun _ h ↦ h.2.2.1⟩


section PositiveCoverageTheorem

variable {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [MeasurableSpace Ω'] {q : Measure X} [IsProbabilityMeasure q]
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {f : X → (Fin d → ℝ) → ℝ}

/-- The existing full-coverage theorem extended to positive-sublevel coverage.
Zero-only feasible pieces are retained in W, and any measurable minimizer is
allowed; repair is internal and preserves both reported errors almost surely. -/
theorem maximumLikelihood_asymptotics_of_positive_cover
    (I : FundamentalConditionI 4 q f K W) (L : R.AnalyticResolvedLikelihood 4 q f)
    (hf : Measurable (Function.uncurry f)) (hW : IsCompact W)
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    {C : ℝ} (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C * K w)
    (hcover : ∃ δ > 0, ∀ w ∈ W, 0 < K w → K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    {Xs : ℕ → Ω → X} (hX : ∀ i, MeasurePreserving (Xs i) P q) (hIndep : iIndepFun Xs P)
    (E : EmpiricalProcessLimit q (fun x (u : ResolutionAtlas.Domain R) ↦ L.a u.1 x u.2) Xs P P')
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n : ℕ, Measurable (ŵ n))
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      empiricalLoss f Xs n ω (ŵ n ω) ≤ empiricalLoss f Xs n ω w) :
    let G := fun (n : ℕ) ω ↦ (n : ℝ) * K (ŵ n ω)
    let T := fun (n : ℕ) ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)
    let M := fun ω' ↦ ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedZeroSet R)
        (E.Ψlim ω')
    Integrable M P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (G n) P ∧ Integrable (T n) P) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (G n ω, T n ω)) atTop
        (fun ω' ↦ (M ω', -M ω')) (fun _ ↦ P) P' ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, G n ω ∂P) atTop (𝓝 (∫ ω', M ω' ∂P')) ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) ∧
      TendstoInMeasure P (fun (n : ℕ) ω ↦
        (G n ω - ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedZeroSet R)
            (E.Ψ n ω),
          T n ω + ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedZeroSet R)
              (E.Ψ n ω))) atTop 0 := by
  classical
  dsimp only
  obtain ⟨δ, hδ, hcoverδ⟩ := hcover
  have hi : ∀ w ∈ W, Integrable (fun x ↦ f x w ^ 2) q := fun w hw ↦
    integrable_pow_of_memLp (s := 4) (by norm_num)
      (I.memLp hw) (by norm_num)
  have hzero := empiricalLoss_zero_of_ae_zero
    (fun i ↦ (hX i).measurable) (fun i ↦ (hX i).map_eq)
    (ae_forall_zero_of_relative_second_moment hcont hi hRFV)
  let α₀ : R.ι := Classical.choice inferInstance
  let z : Fin d → ℝ := R.g α₀ 0
  have hz : z ∈ R.coveredSet δ := R.chart_mem_coveredSet δ α₀ (R.zero_mem_cube α₀)
  have hzK : K z = 0 := R.K_chart_origin α₀
  let ŵc : ℕ → Ω → Fin d → ℝ := fun n ω ↦ repairZero K z (ŵ n ω)
  obtain ⟨hŵcm, hŵcW, hminc, hKae, hTae⟩ := repaired_estimator_inputs R hcoverδ hK0
    (measurable_K_of_integral hf I.K_eq) hzero hz hzK ŵ hŵ hŵW hmin
  have hWc : IsCompact (R.coveredSet δ) := R.isCompact_coveredSet δ hW
    I.continuousOn_K
  have hres := maximumLikelihood_asymptotics_with_approx (R.coveredAtlas δ)
    (I.monoSet (R.coveredSet_subset δ))
        (ResolutionAtlas.AnalyticResolvedLikelihood.coveredLikelihood δ L) hf hWc
    (fun w hw ↦ hK0 w (R.coveredSet_subset δ hw))
    (hcont.mono fun x hx ↦ hx.mono (R.coveredSet_subset δ)) hz hzK
    (R.coveredAtlas_cover hδ) hX hIndep E ŵc hŵcm hŵcW hminc
  dsimp only at hres
  obtain ⟨hM, hInt, hLaw, hGlim, hTlim, hApprox⟩ := hres
  have hG : ∀ n : ℕ, (fun ω ↦ (n : ℝ) * K (ŵc n ω)) =ᵐ[P]
      fun ω ↦ (n : ℝ) * K (ŵ n ω) := fun n ↦
    (hKae n).mono fun _ h ↦ congrArg (fun x : ℝ ↦ (n : ℝ) * x) h
  have hT : ∀ n : ℕ, (fun ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵc n ω)) =ᵐ[P]
      fun ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) := fun n ↦
    (hTae n).mono fun _ h ↦ congrArg (fun x : ℝ ↦ (n : ℝ) * x) h
  refine ⟨hM, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hInt] with n hn
    exact ⟨hn.1.congr (hG n), hn.2.congr (hT n)⟩
  · exact TendstoInDistribution.congr
      (fun n ↦ (hG n).prodMk (hT n)) (Filter.Eventually.of_forall fun _ ↦ rfl) hLaw
  · have heq : (fun n : ℕ ↦ ∫ ω, (n : ℝ) * K (ŵ n ω) ∂P) =
        fun n : ℕ ↦ ∫ ω, (n : ℝ) * K (ŵc n ω) ∂P :=
      funext fun n ↦ (integral_congr_ae (hG n)).symm
    rw [heq]
    exact hGlim
  · have heq : (fun n : ℕ ↦ ∫ ω, (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) ∂P) =
        fun n : ℕ ↦ ∫ ω, (n : ℝ) * empiricalLoss f Xs n ω (ŵc n ω) ∂P :=
      funext fun n ↦ (integral_congr_ae (hT n)).symm
    rw [heq]
    exact hTlim
  · apply TendstoInMeasure.congr (h_tendsto := hApprox)
      (h_right := Filter.Eventually.of_forall fun _ ↦ rfl)
    intro n
    filter_upwards [hKae n, hTae n] with ω hKω hTω
    exact Prod.ext (congrArg (fun x : ℝ ↦ (n : ℝ) * x -
      ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedZeroSet R) (E.Ψ n ω)) hKω)
      (congrArg (fun x : ℝ ↦ (n : ℝ) * x +
        ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedZeroSet R) (E.Ψ n ω)) hTω)

end PositiveCoverageTheorem
end MaximumLikelihood
end SingularLearningTheory
