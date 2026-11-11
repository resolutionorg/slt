/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.LocalQuotient
public import SLT.FreeEnergy.FundamentalConditions
public import SLT.FreeEnergy.PositiveCoordinates
public import SLT.Resolution.Atlas
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# [Wat09, Theorem 6.1] on a whole chart: the `L^s(q)`-valued analytic quotient

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]), chart-wide form | |
| | `ResolutionAtlas.exists_analytic_quotient` |

The local quotients of `AnalyticOnNhd.analyticAt_factor_monomial_of_bound_on_cube` — around every
point of the
closed chart cube, `F ∘ g_α = u^{k_α} • G` with `G` analytic near the point — are glued into one
map `a : ℝ^d → L^s(q)`, analytic at every point of the cube, with `F(g_α u) = u^{k_α} • a u` and
`∫ a(u) dq = u^{k_α}` on the cube. Two local quotients agree where `u^{k_α} ≠ 0`, a dense open
set, hence on their whole (open) overlap by continuity; `a` is defined as the quotient of any
patch containing the point. The mean identity holds where `u^{k_α} ≠ 0` by cancelling in
`∫ F(g_α u) dq = K(g_α u) = u^{2k_α}`, and on the divisor by continuity along the points of the cube
with positive coordinates.
-/

public section

namespace SingularLearningTheory.ResolutionAtlas

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)
  {X : Type*} [MeasurableSpace X] {q : Measure X} [IsProbabilityMeasure q]

/-- The points with a nonzero monomial `u^k` are dense. -/
theorem _root_.dense_monomial_ne_zero (k : Fin d → ℕ) : Dense
    {u : Fin d → ℝ | ∏ j, u j ^ k j ≠ 0} := by
  have : Dense (Set.pi univ fun _ : Fin d ↦ ({0}ᶜ : Set ℝ)) :=
    dense_pi univ fun _ _ ↦ dense_compl_singleton 0
  exact this.mono fun u (hu : u ∈ Set.pi univ fun _ : Fin d ↦ ({0}ᶜ : Set ℝ)) ↦
    Finset.prod_ne_zero_iff.mpr fun j _ ↦
      pow_ne_zero _ (Set.mem_compl_singleton_iff.mp (hu j (mem_univ j)))

end SingularLearningTheory.ResolutionAtlas

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {X : Type*} [MeasurableSpace X] {q : Measure X} [IsProbabilityMeasure q]

/-- [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]) on one
chart, from its data: for `F : U → L^s(q)` analytic (`s ≥ 2`) representing `f`, under relatively
finite variance and a chart map analytic on a neighbourhood of its cube, there is `a : ℝ^d → L^s(q)`
analytic at every point of the cube with `F(g_α u) = u^{k_α} • a u` and `∫ a(u) dq = u^{k_α}` for
all `u` in the cube. -/
theorem exists_analytic_quotient_of_chart {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {f : X → (Fin d → ℝ) → ℝ} (hK : ∀ w, K w = ∫ x, f x w ∂q) {V : Set (Fin d → ℝ)}
    (hWV : W ⊆ V) {F : (Fin d → ℝ) → Lp ℝ s q} (hFa : AnalyticOnNhd ℝ F V)
    (hFf : ∀ w ∈ V, (F w : X → ℝ) =ᵐ[q] fun x ↦ f x w) {C : ℝ} (hC : 0 < C)
    (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w)
    {b : ℝ} (hb : 0 < b) {g : (Fin d → ℝ) → (Fin d → ℝ)} {k : Fin d → ℕ}
    (hg : AnalyticOnNhd ℝ g (cube d b)) (hgW : MapsTo g (cube d b) W)
    (hmono : ∀ u ∈ cube d b, K (g u) = ∏ j, u j ^ (2 * k j)) :
    ∃ a : (Fin d → ℝ) → Lp ℝ s q, AnalyticOnNhd ℝ a (cube d b) ∧
      (∀ u ∈ cube d b, F (g u) = (∏ j, u j ^ k j) • a u) ∧
      ∀ u ∈ cube d b, ∫ x, a u x ∂q = ∏ j, u j ^ k j := by
  classical
  have hs2 : (2 : ℝ≥0∞) ≤ s := hs
  set P : (Fin d → ℝ) → ℝ := fun u ↦ ∏ j, u j ^ k j with hP
  have hPc : Continuous P := continuous_finsetProd _ fun j _ ↦ (continuous_apply j).pow _
  have hPpos : ∀ v : Fin d → ℝ, (∀ j, 0 < v j) → P v ≠ 0 := fun v hv ↦
    (Finset.prod_pos fun j _ ↦ pow_pos (hv j) _).ne'
  -- the `L^s(q)`-valued map `A u = F(g_α u)` on a neighbourhood of the cube, detected in `L²(q)`
  set A : (Fin d → ℝ) → Lp ℝ s q := fun u ↦ F (g u) with hA_def
  have hgV : ∀ u ∈ cube d b, g u ∈ V := fun u hu ↦ hWV (hgW hu)
  have hA : AnalyticOnNhd ℝ A (cube d b) := fun u hu ↦ (hFa _ (hgV u hu)).comp (hg u hu)
  have hbound : ∀ u ∈ cube d b, ‖lpInclusion q hs2 (A u)‖ ≤ C⁻¹ ^ (1 / 2 : ℝ) * P u := by
    intro u hu
    have hu0 : ∀ i, 0 ≤ u i := fun i ↦ hu.1 i
    rw [norm_lpInclusion_two q hs2 _ (hFf _ (hgV u hu))]
    have h1 : ∫ x, f x (g u) ^ 2 ∂q ≤ C⁻¹ * (P u) ^ 2 := by
      rw [hP, ← Finset.prod_pow_two_mul, ← hmono u hu]
      exact hRFV _ (hgW hu)
    have h2 : 0 ≤ P u := Finset.prod_nonneg fun i _ ↦ pow_nonneg (hu0 i) _
    calc (∫ x, f x (g u) ^ 2 ∂q) ^ (1 / 2 : ℝ)
        ≤ (C⁻¹ * (P u) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (integral_nonneg fun x ↦ sq_nonneg _) h1 (by norm_num)
      _ = C⁻¹ ^ (1 / 2 : ℝ) * P u := by
          rw [Real.mul_rpow (by positivity) (sq_nonneg _), ← Real.sqrt_eq_rpow ((P u) ^ 2),
            Real.sqrt_sq h2]
  have hAmean : ∀ u ∈ cube d b, lpIntegral q (A u) = P u ^ 2 := by
    intro u hu
    rw [lpIntegral_apply, integral_congr_ae (hFf _ (hgV u hu)), ← hK, hmono u hu, hP,
      Finset.prod_pow_two_mul]
  -- the local quotients, on open balls where they are analytic and divide `A`
  have hloc : ∀ a₀ ∈ cube d b, ∃ G : (Fin d → ℝ) → Lp ℝ s q, ∃ ε > 0,
      ∀ u ∈ Metric.ball a₀ ε, AnalyticAt ℝ G u ∧ A u = P u • G u := by
    intro a₀ ha₀
    obtain ⟨G, hGa, hAG⟩ := AnalyticOnNhd.analyticAt_factor_monomial_of_bound_on_cube
      (lpInclusion q hs2) (lpInclusion_injective q hs2) (k) hb hA (by positivity) hbound ha₀
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hGa.eventually_analyticAt.and hAG)
    exact ⟨G, ε, hε, fun u hu ↦ hball hu⟩
  choose! G ε hε hG using hloc
  -- two local quotients agree on their overlap: where `P ≠ 0` by cancellation, a dense set
  have hcompat : ∀ a₀ ∈ cube d b, ∀ a₁ ∈ cube d b,
      ∀ u ∈ Metric.ball a₀ (ε a₀) ∩ Metric.ball a₁ (ε a₁), G a₀ u = G a₁ u := by
    intro a₀ h₀ a₁ h₁ u hu
    have hO : IsOpen (Metric.ball a₀ (ε a₀) ∩ Metric.ball a₁ (ε a₁)) :=
      Metric.isOpen_ball.inter Metric.isOpen_ball
    refine Set.EqOn.of_subset_closure
      (s := (Metric.ball a₀ (ε a₀) ∩ Metric.ball a₁ (ε a₁)) ∩ {u | P u ≠ 0}) ?_
      (fun v hv ↦ (hG a₀ h₀ v hv.1).1.continuousAt.continuousWithinAt)
      (fun v hv ↦ (hG a₁ h₁ v hv.2).1.continuousAt.continuousWithinAt) inter_subset_left
      ((dense_monomial_ne_zero (k)).open_subset_closure_inter hO) hu
    rintro v ⟨⟨hv₀, hv₁⟩, hPv⟩
    exact smul_right_injective _ hPv ((hG a₀ h₀ v hv₀).2.symm.trans (hG a₁ h₁ v hv₁).2)
  -- the glued quotient
  let a : (Fin d → ℝ) → Lp ℝ s q := fun u ↦
    if h : ∃ a₀ ∈ cube d b, u ∈ Metric.ball a₀ (ε a₀) then G h.choose u else 0
  have hlocal : ∀ a₀ ∈ cube d b, ∀ u ∈ Metric.ball a₀ (ε a₀), a u = G a₀ u := by
    intro a₀ h₀ u hu
    have h : ∃ a₁ ∈ cube d b, u ∈ Metric.ball a₁ (ε a₁) := ⟨a₀, h₀, hu⟩
    simp only [a, dite_eq_left h]
    exact hcompat _ h.choose_spec.1 a₀ h₀ u ⟨h.choose_spec.2, hu⟩
  have ha : AnalyticOnNhd ℝ a (cube d b) := fun u hu ↦
    (hG u hu u (Metric.mem_ball_self (hε u hu))).1.congr
      (Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds u (hε u hu))
        fun v hv ↦ (hlocal u hu v hv).symm)
  have hfactor : ∀ u ∈ cube d b, A u = P u • a u := fun u hu ↦ by
    rw [hlocal u hu u (Metric.mem_ball_self (hε u hu))]
    exact (hG u hu u (Metric.mem_ball_self (hε u hu))).2
  refine ⟨a, ha, hfactor, fun u hu ↦ ?_⟩
  -- the mean identity: cancel `P` off the divisor, extend by continuity
  rw [← lpIntegral_apply]
  refine eq_of_eqOn_posCoords hb isOpen_univ (mem_univ (⟨u, hu⟩ : cube d b))
    (φ := fun v : cube d b ↦ lpIntegral q (a v)) (ψ := fun v ↦ P v)
    (ContinuousAt.comp (f := (Subtype.val : cube d b → Fin d → ℝ))
      (g := fun z ↦ lpIntegral q (a z)) (x := ⟨u, hu⟩)
      ((lpIntegral q).continuous.continuousAt.comp (ha u hu).continuousAt)
      continuous_subtype_val.continuousAt) (hPc.comp continuous_subtype_val).continuousAt ?_
  intro v _ hvpos
  have := hAmean v v.2
  rw [hfactor v v.2, map_smul, smul_eq_mul] at this
  exact mul_left_cancel₀ (hPpos v hvpos) (by rw [this]; ring)

end SingularLearningTheory

namespace SingularLearningTheory.ResolutionAtlas

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)
  {X : Type*} [MeasurableSpace X] {q : Measure X} [IsProbabilityMeasure q]

/-- [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]) on one
chart: for `F : U → L^s(q)` analytic (`s ≥ 2`) representing `f`, under relatively finite variance
and a chart map analytic on a neighbourhood of its cube, there is `a : ℝ^d → L^s(q)` analytic at
every point of the cube with `F(g_α u) = u^{k_α} • a u` and `∫ a(u) dq = u^{k_α}` for all `u` in the
cube. -/
theorem exists_analytic_quotient {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {f : X → (Fin d → ℝ) → ℝ} (hK : ∀ w, K w = ∫ x, f x w ∂q) {V : Set (Fin d → ℝ)}
    (hWV : W ⊆ V) {F : (Fin d → ℝ) → Lp ℝ s q} (hFa : AnalyticOnNhd ℝ F V)
    (hFf : ∀ w ∈ V, (F w : X → ℝ) =ᵐ[q] fun x ↦ f x w) {C : ℝ} (hC : 0 < C)
    (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w) (α : R.ι) :
    ∃ a : (Fin d → ℝ) → Lp ℝ s q, AnalyticOnNhd ℝ a (cube d (R.b α)) ∧
      (∀ u ∈ cube d (R.b α), F (R.g α u) = (∏ j, u j ^ R.k α j) • a u) ∧
      ∀ u ∈ cube d (R.b α), ∫ x, a u x ∂q = ∏ j, u j ^ R.k α j :=
  exists_analytic_quotient_of_chart hs hK hWV hFa hFf hC hRFV (R.b_pos α) (R.g_analytic α)
    (R.g_mapsTo α) (R.monomial α)

end SingularLearningTheory.ResolutionAtlas
