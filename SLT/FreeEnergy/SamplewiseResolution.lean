/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.ChartQuotient
public import SLT.FreeEnergy.FundamentalConditions
public import SLT.EmpiricalProcess.LocalExpansion
public import SLT.EmpiricalProcess.Modification
import SLT.EmpiricalProcess.Borel
import SLT.FreeEnergy.PositiveCoordinates
public import SLT.EmpiricalProcess.Defs
public import SLT.StandardForm.ResolvedLikelihood

/-!
# [Wat09, Theorem 6.1], samplewise: the resolved likelihood

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]), samplewise form | |
| | `ResolutionAtlas.exists_resolvedLikelihood` |

From the chart-wide `L^s(q)`-valued analytic quotient
(`exists_analytic_quotient`) and the samplewise representatives of its local
power series (`HasFPowerSeriesOnBall.exists_l2Expansion_repr`), the measurable `C(U_α, ℝ)`-valued
representative
`a_α(x, ·)` of [Hit26, Lemma 5.2.3] is assembled: on each ball
of a finite cover of the cube, `f(x, g_α u) = u^{k_α} r_i(x, u)` for almost every `x` and all `u`
(identified on a countable dense set, extended by the almost-sure continuity of `u ↦ f(x, g_α u)`);
the local representatives agree on overlaps off the divisor `{u^{k_α} = 0}`, which is dense, hence
everywhere; they are glued on a measurable full-measure set and set to `0` elsewhere.
The analytic quotient and its pointwise a.e. agreement with the samplewise representative
are retained, including on the divisor. Its mean identity transfers to the representative.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)
  {X : Type*} [MeasurableSpace X] {q : Measure X} [IsProbabilityMeasure q]

end ResolutionAtlas

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {X : Type*} [MeasurableSpace X] {q : Measure X} [IsProbabilityMeasure q]

/-- [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]) on one
chart, from its data, in the samplewise form: a measurable `a : X → C(U_α, ℝ)` with `f(x, g_α u) =
u^{k_α} a(x)(u)` for almost every `x` and all `u`, and `∫ a(x)(u) q(dx) = u^{k_α}`. -/
theorem exists_chart_representative_with_analytic_of_chart {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {f : X → (Fin d → ℝ) → ℝ} (hK : ∀ w, K w = ∫ x, f x w ∂q) {V : Set (Fin d → ℝ)}
    (hWV : W ⊆ V) {F : (Fin d → ℝ) → Lp ℝ s q} (hFa : AnalyticOnNhd ℝ F V)
    (hFf : ∀ w ∈ V, (F w : X → ℝ) =ᵐ[q] fun x ↦ f x w) {C : ℝ} (hC : 0 < C)
    (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w)
    {b : ℝ} (hb : 0 < b) {g : (Fin d → ℝ) → (Fin d → ℝ)} {k : Fin d → ℕ}
    (hg : AnalyticOnNhd ℝ g (cube d b)) (hgW : MapsTo g (cube d b) W)
    (hmono : ∀ u ∈ cube d b, K (g u) = ∏ j, u j ^ (2 * k j))
    (hcont : ∀ᵐ x ∂q, Continuous fun u : cube d (b) ↦ f x (g u)) :
    ∃ (A : (Fin d → ℝ) → Lp ℝ s q) (a : X → C(cube d (b), ℝ)),
      AnalyticOnNhd ℝ A (cube d (b)) ∧
      (∀ u : cube d (b), (A u : X → ℝ) =ᵐ[q] fun x ↦ a x u) ∧
      Measurable a ∧
      (∀ᵐ x ∂q, ∀ u : cube d (b),
        f x (g u) = (∏ j, (u : Fin d → ℝ) j ^ k j) * a x u) ∧
      (∀ u : cube d (b), ∫ x, a x u ∂q = ∏ j, (u : Fin d → ℝ) j ^ k j) ∧
      (∀ u : cube d (b), MemLp (fun x ↦ a x u) 2 q) ∧
      ∀ u : cube d (b), ∃ B : Set (cube d (b)), IsOpen B ∧ u ∈ B ∧
        ∃ E : L2Expansion q (fun x v ↦ a x v) B, E.HigherMoment s := by
  classical
  have hs2 : (2 : ℝ≥0∞) ≤ s := hs
  set P : (Fin d → ℝ) → ℝ := fun u ↦ ∏ j, u j ^ k j with hP
  have hPc : Continuous P := continuous_finsetProd _ fun j _ ↦ (continuous_apply j).pow _
  have hPpos : ∀ v : Fin d → ℝ, (∀ j, 0 < v j) → P v ≠ 0 := fun v hv ↦
    (Finset.prod_pos fun j _ ↦ pow_pos (hv j) _).ne'
  obtain ⟨A, hA, hfactorA, hmeanA⟩ :=
    exists_analytic_quotient_of_chart hs hK hWV hFa hFf hC hRFV hb hg hgW hmono
  have hAf : ∀ u ∈ cube d (b), (P u • A u : Lp ℝ s q) = F (g u) :=
    fun u hu ↦ (hfactorA u hu).symm
  -- local power-series representatives of the same analytic quotient
  have hloc : ∀ a : cube d (b), ∃ (B : Set (cube d (b))) (rep : X → cube d (b) → ℝ),
      IsOpen B ∧ a ∈ B ∧ (∀ u ∈ B, (A u : X → ℝ) =ᵐ[q] fun x ↦ rep x u) ∧
      (∀ u, Measurable fun x ↦ rep x u) ∧
      (∀ᵐ x ∂q, ContinuousOn (rep x) B) ∧
      (∀ u ∈ B, ∀ᵐ x ∂q, f x (g u) = P u * rep x u) ∧
      (∀ u ∈ B, ∫ x, rep x u ∂q = P u) ∧
      (∀ u ∈ B, MemLp (fun x ↦ rep x u) 2 q) ∧
      ∃ E : L2Expansion q rep B, E.HigherMoment s := by
    intro a
    obtain ⟨p, r, hpr⟩ := hA a a.2
    obtain ⟨ρ, hρ, hrep⟩ := HasFPowerSeriesOnBall.exists_l2Expansion_repr hs2 hpr
      fun u : cube d (b) ↦ (u : Fin d → ℝ)
    set B : Set (cube d (b)) := {u | dist (u : Fin d → ℝ) a < ρ}
    have hBo : IsOpen B := isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
    have haB : a ∈ B := by simpa [B] using hρ
    obtain ⟨rep, hrep_meas, hrep_cont, hrepF, hE⟩ := hrep B
      (fun u hu ↦ le_of_lt hu)
      (fun u _ v _ ↦ le_of_eq (Subtype.dist_eq u v).symm)
    refine ⟨B, rep, hBo, haB, fun u hu ↦ (hrepF u hu).2.symm,
      hrep_meas, hrep_cont, fun u hu ↦ ?_, fun u hu ↦ ?_,
      fun u hu ↦ ((Lp.memLp (A u)).mono_exponent hs2).ae_eq (hrepF u hu).2.symm, hE⟩
    · have h2 : (F (g u) : X → ℝ) =ᵐ[q] fun x ↦ P u * A u x := by
        rw [← hAf u u.2]
        filter_upwards [Lp.coeFn_smul (P u) (A u)] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul]
      filter_upwards [hFf _ (hWV (hgW u.2)), h2, (hrepF u hu).2] with x hx hx' hx''
      rw [← hx, hx', hx'']
    · rw [integral_congr_ae (hrepF u hu).2]
      exact hmeanA u u.2
  choose B rep hBo haB hrepA hrep_meas hrep_cont hid hmean hmemLp hE using hloc
  -- a finite subcover and a choice of patch for every point
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover B hBo fun u _ ↦ mem_iUnion.mpr ⟨u, haB u⟩
  have hcover : ∀ u : cube d (b), ∃ i ∈ t, u ∈ B i := fun u ↦ by
    have := ht (mem_univ u)
    simpa only [mem_iUnion, exists_prop] using this
  choose ι hιt hιB using hcover
  choose D hDB hDc hBD using fun i ↦
    (TopologicalSpace.IsSeparable.of_separableSpace (B i)).exists_countable_dense_subset
  -- the measurable good set
  obtain ⟨G₀, hG₀m, hG₀q, hG₀⟩ :=
    exists_measurable_continuity_set q (fun x (u : cube d (b)) ↦ f x (g u)) hcont
  have hgood_i : ∀ i, ∃ S : Set X, MeasurableSet S ∧ q Sᶜ = 0 ∧ ∀ x ∈ S,
      ContinuousOn (rep i x) (B i) ∧ ∀ u ∈ D i, f x (g u) = P u * rep i x u := by
    intro i
    have h1 : ∀ᵐ x ∂q, ContinuousOn (rep i x) (B i) ∧
        ∀ u ∈ D i, f x (g u) = P u * rep i x u :=
      (hrep_cont i).and ((ae_ball_iff (hDc i)).mpr fun u hu ↦ hid i u (hDB i hu))
    obtain ⟨T, hT, hTm, hTq⟩ := exists_measurable_superset_of_null (ae_iff.mp h1)
    exact ⟨Tᶜ, hTm.compl, by rwa [compl_compl], fun x hx ↦ by_contra fun h ↦ hx (hT h)⟩
  choose S hSm hSq hS using hgood_i
  set good : Set X := G₀ ∩ ⋂ i ∈ t, S i with hgood_def
  have hgoodm : MeasurableSet good := hG₀m.inter (Finset.measurableSet_biInter _ fun i _ ↦ hSm i)
  have hgood_ae : ∀ᵐ x ∂q, x ∈ good := by
    have h1 : ∀ᵐ x ∂q, x ∈ G₀ := mem_ae_iff.mpr hG₀q
    have h2 : ∀ᵐ x ∂q, ∀ i ∈ t, x ∈ S i :=
      (Finset.eventually_all t).mpr fun i _ ↦ mem_ae_iff.mpr (hSq i)
    filter_upwards [h1, h2] with x hx hx'
    exact ⟨hx, mem_iInter₂.mpr hx'⟩
  -- on the good set: the identities on every patch, compatibility, continuity of the glued map
  have hid' : ∀ x ∈ good, ∀ i ∈ t, ∀ u ∈ B i, f x (g u) = P u * rep i x u := by
    intro x hx i hi u hu
    have hxS := (mem_iInter₂.mp hx.2) i hi
    have hc1 : ContinuousOn (fun u : cube d (b) ↦ f x (g u)) (B i) :=
      (hG₀ x hx.1).continuousOn
    have hc2 : ContinuousOn (fun u : cube d (b) ↦ P u * rep i x u) (B i) :=
      (hPc.comp continuous_subtype_val).continuousOn.mul (hS i x hxS).1
    exact EqOn.of_subset_closure (fun u hu ↦ (hS i x hxS).2 u hu) hc1 hc2 (hDB i) (hBD i) hu
  have hcompat : ∀ x ∈ good, ∀ i ∈ t, ∀ j ∈ t, ∀ u ∈ B i ∩ B j, rep i x u = rep j x u := by
    intro x hx i hi j hj u hu
    refine eq_of_eqOn_posCoords hb ((hBo i).inter (hBo j)) hu
      ((hS i x ((mem_iInter₂.mp hx.2) i hi)).1.continuousAt ((hBo i).mem_nhds hu.1))
      ((hS j x ((mem_iInter₂.mp hx.2) j hj)).1.continuousAt ((hBo j).mem_nhds hu.2)) ?_
    intro v hv hvpos
    exact mul_left_cancel₀ (hPpos v hvpos)
      ((hid' x hx i hi v hv.1).symm.trans (hid' x hx j hj v hv.2))
  have hglue_cont : ∀ x ∈ good, Continuous fun u : cube d (b) ↦ rep (ι u) x u := by
    intro x hx
    rw [continuous_iff_continuousAt]
    intro u₀
    have h1 : ContinuousAt (fun u ↦ rep (ι u₀) x u) u₀ :=
      (hS (ι u₀) x ((mem_iInter₂.mp hx.2) (ι u₀) (hιt u₀))).1.continuousAt
        ((hBo _).mem_nhds (hιB u₀))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(hBo (ι u₀)).mem_nhds (hιB u₀)] with u hu
    exact hcompat x hx (ι u) (hιt u) (ι u₀) (hιt u₀) u ⟨hιB u, hu⟩
  -- the representative
  have hae : ∀ u, (fun x ↦ (if hx : x ∈ good then (⟨fun u ↦ rep (ι u) x u, hglue_cont x hx⟩ :
      C(cube d (b), ℝ)) else 0) u) =ᵐ[q] fun x ↦ rep (ι u) x u := fun u ↦ by
    filter_upwards [hgood_ae] with x hx
    simp [dite_eq_left hx]
  refine ⟨A, fun x ↦ if hx : x ∈ good then ⟨fun u ↦ rep (ι u) x u, hglue_cont x hx⟩ else 0, hA,
    fun u ↦ (hrepA (ι u) u (hιB u)).trans (hae u).symm, ?_, ?_,
    ?_, fun u ↦ (hmemLp (ι u) u (hιB u)).ae_eq (hae u).symm, fun u₀ ↦ ?_⟩
  · refine ContinuousMap.measurable_of_eval fun u ↦ ?_
    have : (fun x ↦ (if hx : x ∈ good then (⟨fun u ↦ rep (ι u) x u, hglue_cont x hx⟩ :
        C(cube d (b), ℝ)) else 0) u) = good.indicator fun x ↦ rep (ι u) x u := by
      funext x
      by_cases hx : x ∈ good
      · simp [hx]
      · simp [hx]
    rw [this]
    exact (hrep_meas (ι u) u).indicator hgoodm
  · filter_upwards [hgood_ae] with x hx u
    simp only [dite_eq_left hx, ContinuousMap.coe_mk]
    exact hid' x hx (ι u) (hιt u) u (hιB u)
  · intro u
    rw [integral_congr_ae (hae u)]
    exact hmean (ι u) u (hιB u)
  · -- the local expansion around `u₀`: the patch `B (ι u₀)`, with `a = rep (ι u₀)` a.e. on it
    obtain ⟨E, hE4⟩ := hE (ι u₀)
    refine ⟨B (ι u₀), hBo _, hιB u₀, E.congr fun v hv ↦ ?_, hE4.congr _⟩
    filter_upwards [hgood_ae] with x hx
    simp only [dite_eq_left hx, ContinuousMap.coe_mk]
    exact hcompat x hx (ι u₀) (hιt u₀) (ι v) (hιt v) v ⟨hv, hιB v⟩

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)
  {X : Type*} [MeasurableSpace X] {q : Measure X} [IsProbabilityMeasure q]

/-- [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]) on one
chart, in the samplewise form: a measurable `a : X → C(U_α, ℝ)` with `f(x, g_α u) = u^{k_α} a(x)(u)`
for almost every `x` and all `u`, and `∫ a(x)(u) q(dx) = u^{k_α}`. -/
theorem exists_chart_representative_with_analytic {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {f : X → (Fin d → ℝ) → ℝ} (hK : ∀ w, K w = ∫ x, f x w ∂q) {V : Set (Fin d → ℝ)}
    (hWV : W ⊆ V) {F : (Fin d → ℝ) → Lp ℝ s q} (hFa : AnalyticOnNhd ℝ F V)
    (hFf : ∀ w ∈ V, (F w : X → ℝ) =ᵐ[q] fun x ↦ f x w) {C : ℝ} (hC : 0 < C)
    (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w) (α : R.ι)
    (hcont : ∀ᵐ x ∂q, Continuous fun u : cube d (R.b α) ↦ f x (R.g α u)) :
    ∃ (A : (Fin d → ℝ) → Lp ℝ s q) (a : X → C(cube d (R.b α), ℝ)),
      AnalyticOnNhd ℝ A (cube d (R.b α)) ∧
      (∀ u : cube d (R.b α), (A u : X → ℝ) =ᵐ[q] fun x ↦ a x u) ∧
      Measurable a ∧
      (∀ᵐ x ∂q, ∀ u : cube d (R.b α),
        f x (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * a x u) ∧
      (∀ u : cube d (R.b α), ∫ x, a x u ∂q = ∏ j, (u : Fin d → ℝ) j ^ R.k α j) ∧
      (∀ u : cube d (R.b α), MemLp (fun x ↦ a x u) 2 q) ∧
      ∀ u : cube d (R.b α), ∃ B : Set (cube d (R.b α)), IsOpen B ∧ u ∈ B ∧
        ∃ E : L2Expansion q (fun x v ↦ a x v) B, E.HigherMoment s :=
  exists_chart_representative_with_analytic_of_chart hs hK hWV hFa hFf hC hRFV (R.b_pos α)
    (R.g_analytic α) (R.g_mapsTo α) (R.monomial α) hcont

/-- [Wat09, Theorem 6.1] on one chart, with the coefficient `L^s(q)`-valued analytic on a
neighbourhood of the cube: `a : X → (Fin d → ℝ) → ℝ`, measurable in `x` and continuous on the cube
in `u`, with `f(x, g_α u) = u^{k_α} a(x, u)` for almost every `x` and `∫ a(x, u) q(dx) = u^{k_α}`.
Off the cube `a` is the analytic `L^s(q)`-valued extension. -/
theorem exists_lsValuedAnalytic_chart_representative {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {f : X → (Fin d → ℝ) → ℝ} (hK : ∀ w, K w = ∫ x, f x w ∂q) {V : Set (Fin d → ℝ)}
    (hWV : W ⊆ V) {F : (Fin d → ℝ) → Lp ℝ s q} (hFa : AnalyticOnNhd ℝ F V)
    (hFf : ∀ w ∈ V, (F w : X → ℝ) =ᵐ[q] fun x ↦ f x w) {C : ℝ} (hC : 0 < C)
    (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w) (α : R.ι)
    (hcont : ∀ᵐ x ∂q, Continuous fun u : cube d (R.b α) ↦ f x (R.g α u)) :
    ∃ a : X → (Fin d → ℝ) → ℝ,
      (∀ u : cube d (R.b α), Measurable fun x ↦ a x u) ∧
      (∀ x, ContinuousOn (a x) (cube d (R.b α))) ∧
      LsValuedAnalytic s q a (cube d (R.b α)) ∧
      (∀ᵐ x ∂q, ∀ u : cube d (R.b α),
        f x (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * a x u) ∧
      ∀ u : cube d (R.b α), ∫ x, a x u ∂q = ∏ j, (u : Fin d → ℝ) j ^ R.k α j := by
  classical
  obtain ⟨A, a, hA, ha_eq, ha_meas, ha_factor, ha_mean, -, -⟩ :=
    R.exists_chart_representative_with_analytic hs hK hWV hFa hFf hC hRFV α hcont
  let a' : X → (Fin d → ℝ) → ℝ := fun x u ↦
    if hu : u ∈ cube d (R.b α) then a x ⟨u, hu⟩ else A u x
  have ha' : ∀ x (u : cube d (R.b α)), a' x u = a x u := fun x u ↦ by
    simp only [a', dite_eq_left u.2]
  refine ⟨a', fun u ↦ ?_, fun x ↦ ?_, ?_, ?_, fun u ↦ ?_⟩
  · simpa only [ha', Function.comp_def] using (continuous_eval_const u).measurable.comp ha_meas
  · rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun u : cube d (R.b α) ↦ a' x u)
    simpa only [ha'] using (a x).continuous
  · refine ⟨{u | AnalyticAt ℝ A u}, isOpen_analyticAt ℝ A, hA, A, fun u hu ↦ hu, ?_⟩
    intro u _
    by_cases hu : u ∈ cube d (R.b α)
    · simpa only [a', dite_eq_left hu] using ha_eq ⟨u, hu⟩
    · exact Filter.Eventually.of_forall fun x ↦ by simp only [a', dite_eq_right hu]
  · simpa only [ha'] using ha_factor
  · simpa only [ha'] using ha_mean u

/-- The samplewise projection of `exists_chart_representative_with_analytic`. -/
theorem exists_chart_representative {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {f : X → (Fin d → ℝ) → ℝ} (hK : ∀ w, K w = ∫ x, f x w ∂q) {V : Set (Fin d → ℝ)}
    (hWV : W ⊆ V) {F : (Fin d → ℝ) → Lp ℝ s q} (hFa : AnalyticOnNhd ℝ F V)
    (hFf : ∀ w ∈ V, (F w : X → ℝ) =ᵐ[q] fun x ↦ f x w) {C : ℝ} (hC : 0 < C)
    (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w) (α : R.ι)
    (hcont : ∀ᵐ x ∂q, Continuous fun u : cube d (R.b α) ↦ f x (R.g α u)) :
    ∃ a : X → C(cube d (R.b α), ℝ), Measurable a ∧
      (∀ᵐ x ∂q, ∀ u : cube d (R.b α),
        f x (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * a x u) ∧
      (∀ u : cube d (R.b α), ∫ x, a x u ∂q = ∏ j, (u : Fin d → ℝ) j ^ R.k α j) ∧
      (∀ u : cube d (R.b α), MemLp (fun x ↦ a x u) 2 q) ∧
      ∀ u : cube d (R.b α), ∃ B : Set (cube d (R.b α)), IsOpen B ∧ u ∈ B ∧
        ∃ E : L2Expansion q (fun x v ↦ a x v) B, E.HigherMoment s := by
  obtain ⟨A, a, -, -, ha⟩ :=
    R.exists_chart_representative_with_analytic hs hK hWV hFa hFf hC hRFV α hcont
  exact ⟨a, ha⟩

/-- `ResolvedLikelihood` together with the `L^s(q)`-regularity of `a_α` that the empirical-process
chapter needs (thesis: "`a` is `L^s(q)`-valued real analytic"): `a_α(·, u) ∈ L²(q)` for every `u`,
and local `L²(q)`-expansions of `a_α` around every point of the cube with coefficients in `L^s(q)`
(`HigherMoment s`). -/
structure AnalyticResolvedLikelihood (s : ℝ≥0∞) (q : Measure X) (f : X → (Fin d → ℝ) → ℝ)
    extends R.ResolvedLikelihood q f where
  memLp : ∀ α (u : cube d (R.b α)), MemLp (fun x ↦ a α x u) 2 q
  loc : ∀ α (u : cube d (R.b α)), ∃ B : Set (cube d (R.b α)), IsOpen B ∧ u ∈ B ∧
    ∃ E : L2Expansion q (fun x v ↦ a α x v) B, E.HigherMoment s

/-- [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]),
samplewise, with the `L²(q)`-regularity of the quotient: for `f` `L^s(q)`-valued analytic on a
neighbourhood of `W` with `s ≥ 2`, relatively finite variance, chart maps analytic on a
neighbourhood of their cubes, and `u ↦ f(x, g_α u)` continuous for almost every `x`. -/
theorem exists_analyticResolvedLikelihood {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {f : X → (Fin d → ℝ) → ℝ} (hK : ∀ w, K w = ∫ x, f x w ∂q) (hf : LsValuedAnalytic s q f W)
    {C : ℝ} (hC : 0 < C) (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w)
    (hcont : ∀ᵐ x ∂q, ∀ α, Continuous fun u : cube d (R.b α) ↦ f x (R.g α u)) :
    Nonempty (R.AnalyticResolvedLikelihood s q f) := by
  obtain ⟨V, -, hWV, F, hFa, hFf⟩ := hf
  have h := fun α ↦ R.exists_chart_representative hs hK hWV hFa hFf hC hRFV α
    (hcont.mono fun x hx ↦ hx α)
  choose a ha_meas ha_factor ha_mean ha_memLp ha_loc using h
  exact ⟨⟨⟨a, ha_meas, ha_factor, ha_mean⟩, ha_memLp, ha_loc⟩⟩

/-- [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]),
samplewise: for `f` `L^s(q)`-valued analytic on a neighbourhood of `W` with `s ≥ 2`, relatively
finite variance, chart maps analytic on a neighbourhood of their cubes, and `u ↦ f(x, g_α u)`
continuous for almost every `x`, the resolved likelihood exists (`ResolvedLikelihood`). -/
theorem exists_resolvedLikelihood {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {f : X → (Fin d → ℝ) → ℝ} (hK : ∀ w, K w = ∫ x, f x w ∂q) (hf : LsValuedAnalytic s q f W)
    {C : ℝ} (hC : 0 < C) (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w)
    (hcont : ∀ᵐ x ∂q, ∀ α, Continuous fun u : cube d (R.b α) ↦ f x (R.g α u)) :
    Nonempty (R.ResolvedLikelihood q f) := by
  obtain ⟨L⟩ := R.exists_analyticResolvedLikelihood hs hK hf hC hRFV hcont
  exact ⟨L.toResolvedLikelihood⟩

end ResolutionAtlas

end SingularLearningTheory
