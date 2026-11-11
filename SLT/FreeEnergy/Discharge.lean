/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.EmpiricalProcess.LimitOfAnalytic
public import SLT.EmpiricalProcess.Transport
public import SLT.EmpiricalProcess.Chaining
public import SLT.EmpiricalProcess.TightnessFromPatches
public import SLT.EmpiricalProcess.MajorantsOfExpansion
public import SLT.EmpiricalProcess.FourthMoment
public import SLT.FreeEnergy.FundamentalConditions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The empirical-process inputs of the free energy formula, derived

| Thesis | Lean |
| --- | --- |
| [Hit26, Equation (5.2.2)], [Wat09, Theorem 5.9] for `ξ_n` | |
| | `AnalyticResolvedLikelihood.exists_empiricalProcessLimit_chart` |
| [Hit26, Equation (5.0.5)], [Wat09, Theorem 5.9] for `ψ_n` on | |
| `{K ≥ δ}` | `FundamentalConditionI.exists_tail_empiricalProcessLimit` |
| [Hit26, Theorem 5.2.6], "`∇ξ_n` converges in distribution" | |
| | `AnalyticResolvedLikelihood.primaryLipschitzTight` |
| [Hit26, Lemma 4.2.4] (`s = 4`) for `ξ_n` and for `ψ_n` on `{K ≥ δ}` | |
| | `AnalyticResolvedLikelihood.momentBound_chart`, `FundamentalConditionI.momentBound_tail` |

The free energy theorems of `SLTChallenge/FreeEnergy.lean` take the conclusions of
[Wat09, Theorem 5.9] for the chart process `ξ_n` on `⊔_α U_α` and for `ψ_n` on `{K ≥ δ}`, and the
Lipschitz tightness of `ξ_n` in the primary coordinates, as hypotheses. Here they are derived: the
chart process is the empirical process of the `L²(q)`-analytic quotient `a_α` of
[Wat09, Theorem 6.1] (`AnalyticResolvedLikelihood`), whose local expansions transport to the
disjoint union of the cubes (with the metric `Metric.Sigma.metricSpace`, whose topology is the
disjoint-union topology), so `exists_empiricalProcessLimit_of_l2Expansion` applies; the Lipschitz
majorants of the same expansions chain along segments of the convex cubes
(`SingularLearningTheory.EmpiricalProcess.enorm_sub_le_sum_of_patchMajorants`) and Markov's
inequality gives `PrimaryLipschitzTight`; and `f/√K` is `L^s(q)`-valued analytic near the compact
`{K ≥ δ}` (`√K = exp(log K / 2)` there), so
`SingularLearningTheory.LsValuedAnalytic.exists_empiricalProcessLimit` applies.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

variable {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {q : Measure X}
  [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P] {Xs : ℕ → Ω → X}

namespace ResolutionAtlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- The distance from `u` to `(0_P, u_{Pᶜ})` is at most `Σ_{j ∈ P} u_j`. -/
theorem dist_primaryZero_le (α : R.ι) (u : cube d (R.b α)) :
    dist u (R.primaryZero α u) ≤ ∑ j ∈ R.primary α, (u : Fin d → ℝ) j := by
  have hu : ∀ j, 0 ≤ (u : Fin d → ℝ) j ∧ (u : Fin d → ℝ) j ≤ R.b α := fun j ↦ ⟨u.2.1 j, u.2.2 j⟩
  have hsum : 0 ≤ ∑ j ∈ R.primary α, (u : Fin d → ℝ) j := Finset.sum_nonneg fun j _ ↦ (hu j).1
  rw [Subtype.dist_eq, dist_pi_le_iff hsum]
  intro j
  simp only [primaryZero, Real.dist_eq]
  by_cases hj : j ∈ R.primary α
  · simp only [hj, ite_true, sub_zero, abs_of_nonneg (hu j).1]
    exact Finset.single_le_sum (fun i _ ↦ (hu i).1) hj
  · simp only [hj, ite_false, min_eq_right (hu j).2, max_eq_right (hu j).1, sub_self, abs_zero]
    exact hsum

/-- The metric `Metric.Sigma.metricSpace` on the disjoint union of the chart cubes restricts to
the metric of each cube. -/
theorem sigma_dist_same (α : R.ι) (u v : cube d (R.b α)) :
    letI : MetricSpace ((α : R.ι) × cube d (R.b α)) := Metric.Sigma.metricSpace
    dist (⟨α, u⟩ : (α : R.ι) × cube d (R.b α)) ⟨α, v⟩ = dist u v := by
  change Metric.Sigma.dist _ _ = _
  simp [Metric.Sigma.dist]

variable {R} {f : X → (Fin d → ℝ) → ℝ} {s : ℝ≥0∞}

/-- [Hit26, Equation (5.2.2)]: [Wat09, Theorem 5.9]
for the chart process on the disjoint union of the chart cubes, from the `L²(q)`-regularity of the
quotient `a_α` ([Wat09, Theorem 6.1]). -/
theorem AnalyticResolvedLikelihood.exists_empiricalProcessLimit_chart
    (L : R.AnalyticResolvedLikelihood s q f)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) :
    ∃ (P' : Measure C((α : R.ι) × cube d (R.b α), ℝ)) (_ : IsProbabilityMeasure P'),
      Nonempty (EmpiricalProcessLimit q
        (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2) Xs P P') := by
  letI : MetricSpace ((α : R.ι) × cube d (R.b α)) := Metric.Sigma.metricSpace
  refine exists_empiricalProcessLimit_of_l2Expansion
    (f := fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2)
    (fun u ↦ (continuous_eval_const u.2).measurable.comp (L.a_measurable u.1))
    (Eventually.of_forall fun x ↦ continuous_sigma fun α ↦ (L.a α x).continuous)
    (fun u ↦ L.memLp u.1 u.2) ?_ ?_ hX hlaw hind
  · have : (fun u : (α : R.ι) × cube d (R.b α) ↦ ∫ x, L.a u.1 x u.2 ∂q)
        = fun u ↦ ∏ j, (u.2 : Fin d → ℝ) j ^ R.k u.1 j := funext fun u ↦ L.mean u.1 u.2
    rw [this]
    refine continuous_sigma fun α ↦ ?_
    change Continuous fun a : cube d (R.b α) ↦ ∏ j, (a : Fin d → ℝ) j ^ R.k α j
    exact continuous_finsetProd _ fun j _ ↦
      ((continuous_apply j).comp continuous_subtype_val).pow _
  · rintro ⟨α, u⟩
    obtain ⟨B, hBo, huB, E, -⟩ := L.loc α u
    have hι : ∀ u ∈ B, ∀ v ∈ B,
        dist (⟨α, u⟩ : (α : R.ι) × cube d (R.b α)) ⟨α, v⟩ = dist u v :=
      fun u _ v _ ↦ R.sigma_dist_same α u v
    have hg : ∀ x, ∀ u ∈ B, (fun x (p : (α : R.ι) × cube d (R.b α)) ↦ L.a p.1 x p.2) x
        (⟨α, u⟩ : (α : R.ι) × cube d (R.b α)) = L.a α x u := fun _ _ _ ↦ rfl
    refine ⟨Sigma.mk α '' B, isOpenMap_sigmaMk _ hBo, ⟨u, huB, rfl⟩, ⟨?_⟩⟩
    exact E.image (fun v : cube d (R.b α) ↦ (⟨α, v⟩ : (α : R.ι) × cube d (R.b α))) hι _ hg

/-- The chart process has Lipschitz constants bounded in probability on every
whole chart cube. This strengthens the primary-face estimate used by free energy
and also controls projection and recovery in maximum-likelihood asymptotics. -/
theorem AnalyticResolvedLikelihood.chartLipschitzTight (L : R.AnalyticResolvedLikelihood s q f)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P)
    {Ψ : ℕ → Ω → C((α : R.ι) × cube d (R.b α), ℝ)}
    (hΨ : ∀ n, ∀ᵐ ω ∂P, ∀ u, Ψ n ω u
      = empiricalProcess q (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2) Xs n ω u) :
    ∀ η > 0, ∃ C > 0, ∀ n,
      P {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
        |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v} ≤ ENNReal.ofReal η := by
  classical
  -- the chart process on each cube
  set Ψc : (α : R.ι) → ℕ → Ω → C(cube d (R.b α), ℝ) := fun α n ω ↦
    (Ψ n ω).comp (ContinuousMap.sigmaMk (X := fun α ↦ cube d (R.b α)) α) with hΨc_def
  have hΨc : ∀ α n, ∀ᵐ ω ∂P, ∀ u,
      Ψc α n ω u = empiricalProcess q (fun x v ↦ L.a α x v) Xs n ω u := fun α n ↦ by
    filter_upwards [hΨ n] with ω hω u
    exact hω ⟨α, u⟩
  -- finite covers of the cubes by patches with expansions
  choose B hBo hBu hBE using L.loc
  have hcover : ∀ α, ∃ t : Finset (cube d (R.b α)), ⋃ i : t, B α i = univ := fun α ↦ by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (B α) (hBo α)
      fun u _ ↦ mem_iUnion.mpr ⟨u, hBu α u⟩
    refine ⟨t, eq_univ_of_univ_subset (ht.trans fun u hu ↦ ?_)⟩
    simp only [mem_iUnion, exists_prop] at hu
    obtain ⟨i, hi, hui⟩ := hu
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hui⟩
  choose t ht using hcover
  obtain ⟨M, -⟩ : ∃ _ : (α : R.ι) → (i : t α) → EmpiricalProcess.PatchMajorants (Ψc α) P (B α i),
      True :=
    ⟨fun α i ↦ (hBE α i).choose.patchMajorants Xs hX hlaw hind
      (TopologicalSpace.IsSeparable.of_separableSpace _)
      (Eventually.of_forall fun x ↦ (L.a α x).continuous.continuousOn) (hΨc α), trivial⟩
  have hchain : ∀ α n, ∀ᵐ ω ∂P, ∀ u v : cube d (R.b α),
      ‖Ψc α n ω u - Ψc α n ω v‖ₑ ≤ (∑ i : t α, (M α i).R n ω) * edist u v := fun α n ↦
    EmpiricalProcess.enorm_sub_le_sum_of_patchMajorants (fun i : t α ↦ hBo α i) (ht α) (M α) n
  -- the global majorant `Q_n = Σ_α Σ_i R_{α,i,n}` and its second moment
  have hQm : ∀ n, Measurable fun ω ↦ ∑ p : (α : R.ι) × t α, (M p.1 p.2).R n ω := fun n ↦
    Finset.measurable_sum _ fun p _ ↦ (M p.1 p.2).R_measurable n
  have hQC : ∀ n, ∫⁻ ω, (∑ p : (α : R.ι) × t α, (M p.1 p.2).R n ω) ^ 2 ∂P
      ≤ (∑ p : (α : R.ι) × t α, (M p.1 p.2).CR ^ (1 / 2 : ℝ)) ^ 2 := fun n ↦
    lintegral_sum_sq_le_of_le (g := fun p : (α : R.ι) × t α ↦ (M p.1 p.2).R n)
      (C := fun p : (α : R.ι) × t α ↦ (M p.1 p.2).CR)
      (fun p ↦ (M p.1 p.2).R_measurable n) fun p ↦ (M p.1 p.2).lintegral_R_sq_le n
  have hCtop : (∑ p : (α : R.ι) × t α, (M p.1 p.2).CR ^ (1 / 2 : ℝ)) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.sum_ne_top.mpr fun p _ ↦
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) (M p.1 p.2).CR_ne_top)
  have hQge : ∀ α n ω, ∑ i : t α, (M α i).R n ω ≤ ∑ p : (α : R.ι) × t α, (M p.1 p.2).R n ω :=
    fun α n ω ↦ by
      rw [Fintype.sum_sigma]
      exact Finset.single_le_sum (f := fun α ↦ ∑ i : t α, (M α i).R n ω) (fun _ _ ↦ zero_le)
        (Finset.mem_univ α)
  intro η hη
  -- the level `Lr` from Markov's inequality
  obtain ⟨Cr, hCr⟩ :
      ∃ Cr : ℝ, Cr = ((∑ p : (α : R.ι) × t α, (M p.1 p.2).CR ^ (1 / 2 : ℝ)) ^ 2).toReal :=
    ⟨_, rfl⟩
  have hCr0 : 0 ≤ Cr := hCr ▸ ENNReal.toReal_nonneg
  obtain ⟨Lr, hLr_def⟩ : ∃ Lr : ℝ, Lr = Real.sqrt (Cr / η) + 1 := ⟨_, rfl⟩
  have hLr : 0 < Lr := by rw [hLr_def]; positivity
  have hmarkov : ∀ n, P {ω | ENNReal.ofReal Lr ≤ ∑ p : (α : R.ι) × t α, (M p.1 p.2).R n ω}
      ≤ ENNReal.ofReal η := fun n ↦ by
    refine measure_le_of_lintegral_sq_le (hQm n) (ENNReal.ofReal_pos.mpr hLr).ne'
      ENNReal.ofReal_ne_top ((hQC n).trans ?_)
    rw [← ENNReal.ofReal_pow hLr.le, ← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_toReal hCtop,
      ← hCr]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Real.sqrt (Cr / η) ^ 2 = Cr / η := Real.sq_sqrt (div_nonneg hCr0 hη.le)
    have h2 : Real.sqrt (Cr / η) ^ 2 ≤ Lr ^ 2 := by
      rw [hLr_def]
      nlinarith [Real.sqrt_nonneg (Cr / η)]
    calc Cr = η * (Cr / η) := by field_simp
      _ ≤ η * Lr ^ 2 := by rw [← h1]; exact mul_le_mul_of_nonneg_left h2 hη.le
  refine ⟨Lr, hLr, fun n ↦ le_trans (measure_mono_ae ?_) (hmarkov n)⟩
  have hall : ∀ᵐ ω ∂P, ∀ α, ∀ u v : cube d (R.b α),
      ‖Ψc α n ω u - Ψc α n ω v‖ₑ ≤ (∑ i : t α, (M α i).R n ω) * edist u v :=
    ae_all_iff.mpr fun α ↦ hchain α n
  filter_upwards [hall] with ω hω hbad
  by_contra hQ
  refine hbad fun α u v ↦ ?_
  have hQlt : ∑ p : (α : R.ι) × t α, (M p.1 p.2).R n ω < ENNReal.ofReal Lr := not_le.mp hQ
  have h1 := hω α u v
  have h2 : (∑ i : t α, (M α i).R n ω) * edist u v
      ≤ ENNReal.ofReal Lr * ENNReal.ofReal (dist u v) := by
    rw [edist_dist]
    gcongr
    exact (hQge α n ω).trans hQlt.le
  have h3 := h1.trans h2
  rw [← ENNReal.ofReal_mul hLr.le, Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hLr.le dist_nonneg)] at h3
  exact h3

/-- [Hit26, Theorem 5.2.6], the step "`∇ξ_n` converges in distribution", in the form the formal
proof uses: the Lipschitz constants
of the chart process in the primary coordinates are bounded in probability, from the Lipschitz
majorants of the local expansions of `a_α` chained along segments of the cube. -/
theorem AnalyticResolvedLikelihood.primaryLipschitzTight (L : R.AnalyticResolvedLikelihood s q f)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P)
    {Ψ : ℕ → Ω → C((α : R.ι) × cube d (R.b α), ℝ)}
    (hΨ : ∀ n, ∀ᵐ ω ∂P, ∀ u, Ψ n ω u
      = empiricalProcess q (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2) Xs n ω u) :
    R.PrimaryLipschitzTight Ψ P := by
  intro η hη
  obtain ⟨C, hC, hbound⟩ := L.chartLipschitzTight hX hlaw hind hΨ η hη
  refine ⟨C, 0, fun n _ ↦ le_trans (measure_mono ?_) (hbound n)⟩
  intro ω hbad hgood
  apply hbad
  intro α u
  exact (hgood α u (R.primaryZero α u)).trans
    (mul_le_mul_of_nonneg_left (R.dist_primaryZero_le α u) hC.le)

/-- [Hit26, Lemma 4.2.4] with `s = 4` for the chart process, from the
`L⁴(q)`-regularity of the quotient `a_α` (fundamental condition I with `s = 4`). -/
theorem AnalyticResolvedLikelihood.momentBound_chart (L : R.AnalyticResolvedLikelihood 4 q f)
    (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    (E : EmpiricalProcessLimit q (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2)
      Xs P P') :
    E.MomentBound 4 := by
  letI : MetricSpace ((α : R.ι) × cube d (R.b α)) := Metric.Sigma.metricSpace
  refine E.momentBound_four hX hlaw hind
    (Eventually.of_forall fun x ↦ continuous_sigma fun α ↦ (L.a α x).continuous) ?_
  rintro ⟨α, u⟩
  obtain ⟨B, hBo, huB, E', hE'⟩ := L.loc α u
  have hι : ∀ u ∈ B, ∀ v ∈ B,
      dist (⟨α, u⟩ : (α : R.ι) × cube d (R.b α)) ⟨α, v⟩ = dist u v :=
    fun u _ v _ ↦ R.sigma_dist_same α u v
  have hg : ∀ x, ∀ u ∈ B, (fun x (p : (α : R.ι) × cube d (R.b α)) ↦ L.a p.1 x p.2) x
      (⟨α, u⟩ : (α : R.ι) × cube d (R.b α)) = L.a α x u := fun _ _ _ ↦ rfl
  exact ⟨Sigma.mk α '' B, isOpenMap_sigmaMk _ hBo, ⟨u, huB, rfl⟩,
    E'.image (fun v : cube d (R.b α) ↦ (⟨α, v⟩ : (α : R.ι) × cube d (R.b α))) hι _ hg,
    hE'.image _ hι _ hg⟩

end ResolutionAtlas

/-! ### `ψ_n` on `{K ≥ δ}` -/

namespace FundamentalConditionI

variable {s : ℝ≥0∞} [Fact (1 ≤ s)] {f : X → (Fin d → ℝ) → ℝ} {K : (Fin d → ℝ) → ℝ}
  {W : Set (Fin d → ℝ)}

/-- `K` is real analytic on an open set where `f` has an analytic `L^s(q)`-valued
representative `F` (`K = ∫ F(·) dq`). -/
theorem analyticOnNhd_K_of (I : FundamentalConditionI s q f K W) {U : Set (Fin d → ℝ)}
    {F : (Fin d → ℝ) → Lp ℝ s q} (hU : IsOpen U) (hF : AnalyticOnNhd ℝ F U)
    (hFf : ∀ w ∈ U, (F w : X → ℝ) =ᵐ[q] fun x ↦ f x w) : AnalyticOnNhd ℝ K U := by
  refine ((lpIntegral q).comp_analyticOnNhd hF).congr hU fun w hw ↦ ?_
  change lpIntegral q (F w) = K w
  rw [lpIntegral_apply, I.K_eq w]
  exact integral_congr_ae (hFf w hw)

/-- `K` is real analytic on an open neighbourhood of `W`. -/
theorem exists_analyticOnNhd_K (I : FundamentalConditionI s q f K W) :
    ∃ U, IsOpen U ∧ W ⊆ U ∧ AnalyticOnNhd ℝ K U := by
  obtain ⟨U, hU, hWU, F, hF, hFf⟩ := I.ls_analytic
  exact ⟨U, hU, hWU, I.analyticOnNhd_K_of hU hF hFf⟩

/-- The tail set `{w ∈ W | δ ≤ K(w)}` is compact. -/
theorem isCompact_tail (I : FundamentalConditionI s q f K W) (hW : IsCompact W) (δ : ℝ) :
    IsCompact {w | w ∈ W ∧ δ ≤ K w} := by
  have : {w | w ∈ W ∧ δ ≤ K w} = W ∩ K ⁻¹' Ici δ := by
    ext w
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici]
  rw [this]
  exact hW.of_isClosed_subset (I.continuousOn_K.preimage_isClosed_of_isClosed
    hW.isClosed isClosed_Ici) inter_subset_left

/-- `f/√K` is `L^s(q)`-valued analytic on a neighbourhood of `{w ∈ W | δ ≤ K(w)}`
(`√K = exp(log K / 2)` where `K > 0`). -/
theorem lsValuedAnalytic_tail (I : FundamentalConditionI s q f K W) {δ : ℝ} (hδ : 0 < δ) :
    LsValuedAnalytic s q (fun x w ↦ f x w / Real.sqrt (K w)) {w | w ∈ W ∧ δ ≤ K w} := by
  obtain ⟨U, hU, hWU, F, hF, hFf⟩ := I.ls_analytic
  have hKa := I.analyticOnNhd_K_of hU hF hFf
  set U' : Set (Fin d → ℝ) := U ∩ K ⁻¹' Ioi (δ / 2) with hU'_def
  have hU'o : IsOpen U' := hKa.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hKpos : ∀ w ∈ U', 0 < K w := fun w hw ↦ (half_pos hδ).trans hw.2
  have hca : AnalyticOnNhd ℝ (fun w ↦ Real.exp (-(Real.log (K w) / 2))) U' := fun w hw ↦ by
    have hlog : AnalyticAt ℝ (fun w ↦ Real.log (K w)) w :=
      (analyticAt_log (hKpos w hw)).comp (hKa w hw.1)
    exact analyticAt_rexp.comp (hlog.div_const.neg)
  have hc : ∀ w ∈ U', Real.exp (-(Real.log (K w) / 2)) = (Real.sqrt (K w))⁻¹ := fun w hw ↦ by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (hKpos w hw), ← Real.exp_neg]
    ring_nf
  have hF'a : AnalyticOnNhd ℝ (fun w ↦ Real.exp (-(Real.log (K w) / 2)) • F w) U' :=
    fun w hw ↦ (hca w hw).smul (hF w hw.1)
  have hF'f : ∀ w ∈ U', ((Real.exp (-(Real.log (K w) / 2)) • F w : Lp ℝ s q) : X → ℝ)
      =ᵐ[q] fun x ↦ f x w / Real.sqrt (K w) := fun w hw ↦ by
    filter_upwards [Lp.coeFn_smul (Real.exp (-(Real.log (K w) / 2))) (F w), hFf w hw.1]
      with x hx hx'
    rw [hx, Pi.smul_apply, smul_eq_mul, hx', hc w hw, div_eq_inv_mul]
  exact ⟨U', hU'o, fun w hw ↦ ⟨hWU hw.1, show δ / 2 < K w by linarith [hw.2]⟩, _, hF'a, hF'f⟩

/-- `f/√K` is continuous on `{w ∈ W | δ ≤ K(w)}` for almost every `x`, given the standing
continuity of `f(x, ·)` on `W`. -/
theorem ae_continuousOn_tail (I : FundamentalConditionI s q f K W)
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x ∂q, ContinuousOn (fun w ↦ f x w / Real.sqrt (K w)) {w | w ∈ W ∧ δ ≤ K w} := by
  filter_upwards [hcont] with x hx
  refine (hx.mono fun w hw ↦ hw.1).div
    (Real.continuous_sqrt.comp_continuousOn (I.continuousOn_K.mono fun w hw ↦ hw.1)) fun w hw ↦ (Real.sqrt_pos.mpr (hδ.trans_le hw.2)).ne'

/-- [Hit26, Equation (5.0.5)]: [Wat09, Theorem 5.9] for
`ψ_n`, the empirical process of `f/√K`, on the compact `{K ≥ δ}`, under fundamental condition I and
the standing continuity of `f(x, ·)`. -/
theorem exists_tail_empiricalProcessLimit (I : FundamentalConditionI s q f K W)
    (hW : IsCompact W) (hf_meas : ∀ w, Measurable fun x ↦ f x w)
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W) {δ : ℝ} (hδ : 0 < δ) (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) :
    ∃ (P' : Measure C({w // w ∈ W ∧ δ ≤ K w}, ℝ)) (_ : IsProbabilityMeasure P'),
      Nonempty (EmpiricalProcessLimit q
        (fun x (w : {w // w ∈ W ∧ δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P P') :=
  LsValuedAnalytic.exists_empiricalProcessLimit I.two_le (I.isCompact_tail hW δ)
    (fun w ↦ (hf_meas w).div_const _) (I.ae_continuousOn_tail hcont hδ)
    (I.lsValuedAnalytic_tail hδ) hX hlaw hind

/-- [Hit26, Lemma 4.2.4] with `s = 4` for `ψ_n` on `{K ≥ δ}`, from
fundamental condition I with `s = 4`. -/
theorem momentBound_tail (I : FundamentalConditionI 4 q f K W) (hW : IsCompact W)
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W) {δ : ℝ} (hδ : 0 < δ) (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P P') :
    T.MomentBound 4 :=
  EmpiricalProcessLimit.momentBound_of_lsValuedAnalytic (W := {w | w ∈ W ∧ δ ≤ K w})
    (f := fun x w ↦ f x w / Real.sqrt (K w)) (I.isCompact_tail hW δ) T hX hlaw hind
    (I.ae_continuousOn_tail hcont hδ) (I.lsValuedAnalytic_tail hδ)

end FundamentalConditionI

end SingularLearningTheory
