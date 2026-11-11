/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FeatureCovarianceLLN
public import SLT.BayesGibbs.Prior.FeatureEnvelope
public import SLT.BayesGibbs.Prior.AEPairTransport
public import SLT.MeasureTheory.Constructions.BorelSpace.Sigma
import SLT.EmpiricalProcess.Borel
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Continuous features on a combined domain

Two random continuous features $F$ on $U$ and $G$ on $V$, both compact metric spaces, combine
into one feature on the disjoint union of $U$ and $V$. Its norm is at most $\|F\| + \|G\|$, so it
is in $L^p$ when both are. This lets the chart feature and the tail feature of the log density
ratio share one strong law for products. When the log density ratio factors as
$f(x, w) = r(w)F(x, u)$ at two parameters, the error of its empirical covariance at those
parameters is at most $r(w)r(v)$ times the uniform error of the product feature.

## Main definitions

* `SingularLearningTheory.BayesGibbs.CombinedFeatureDomain`: the disjoint union of $U$ and $V$, as a
  sigma type over `Bool` with fibers `SingularLearningTheory.BayesGibbs.FeatureFiber`.
* `SingularLearningTheory.BayesGibbs.combinedFeature`: the feature that is $F$ on $U$ and $G$ on $V$.

## Main results

* `SingularLearningTheory.BayesGibbs.memLp_combinedFeature`: the combined feature is in $L^p$ when
  both features are.
* `SingularLearningTheory.BayesGibbs.factored_product_kernel_error_le`: the empirical covariance error
  of a factored function at two points is bounded by the uniform product-feature error.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

universe u

/-- A finite sigma index uses exactly the same canonical metric construction
as the chart sigma index, including when the tail is empty. -/
@[expose] def FeatureFiber (U V : Type u) : Bool → Type u
  | false => U
  | true => V

instance featureFiberMetric {U V : Type u} [MetricSpace U] [MetricSpace V] (b : Bool) :
    MetricSpace (FeatureFiber U V b) := by
  cases b
  · exact inferInstanceAs (MetricSpace U)
  · exact inferInstanceAs (MetricSpace V)
@[expose] instance featureFiberCompact {U V : Type u} [MetricSpace U] [MetricSpace V]
    [CompactSpace U] [CompactSpace V] (b : Bool) : CompactSpace (FeatureFiber U V b) := by
  cases b
  · exact inferInstanceAs (CompactSpace U)
  · exact inferInstanceAs (CompactSpace V)

/-- The disjoint union of `U` and `V`, as a sigma type over `Bool` whose fiber over `false` is `U`
and over `true` is `V` (`SingularLearningTheory.BayesGibbs.FeatureFiber`). -/
abbrev CombinedFeatureDomain (U V : Type u) := (b : Bool) × FeatureFiber U V b

section Combined
variable {X : Type*} {U V : Type u} [MeasurableSpace X]
  [MetricSpace U] [MetricSpace V] [CompactSpace U] [CompactSpace V]
  {q : Measure X}
/-- The metric `Metric.Sigma.metricSpace` on the disjoint union
`SingularLearningTheory.BayesGibbs.CombinedFeatureDomain`, local to this module. It is the
construction used for the disjoint union `SingularLearningTheory.ResolutionAtlas.FaceDomain` of
the chart cubes. -/
noncomputable local instance combinedFeatureMetric : MetricSpace (CombinedFeatureDomain U V) := Metric.Sigma.metricSpace

/-- The random continuous feature on `SingularLearningTheory.BayesGibbs.CombinedFeatureDomain U V`
that is $F(x)$ on $U$ and $G(x)$ on $V$ at the sample point $x$. Its norm is at most
$\|F(x)\| + \|G(x)\|$ (`SingularLearningTheory.BayesGibbs.norm_combinedFeature_le`). -/
@[expose] noncomputable def combinedFeature (F : X → C(U, ℝ)) (G : X → C(V, ℝ))
    (x : X) : C(CombinedFeatureDomain U V, ℝ) :=
  ⟨fun u ↦ match u with
    | ⟨false, u⟩ => F x u
    | ⟨true, v⟩ => G x v,
    continuous_sigma fun b ↦ by cases b; exact (F x).continuous; exact (G x).continuous⟩

@[simp] theorem combinedFeature_false (F : X → C(U, ℝ)) (G : X → C(V, ℝ)) (x : X) (u : U) :
    combinedFeature F G x ⟨false, u⟩ = F x u := rfl
@[simp] theorem combinedFeature_true (F : X → C(U, ℝ)) (G : X → C(V, ℝ)) (x : X) (v : V) :
    combinedFeature F G x ⟨true, v⟩ = G x v := rfl

theorem measurable_combinedFeature {F : X → C(U, ℝ)} {G : X → C(V, ℝ)}
    (hF : Measurable F) (hG : Measurable G) : Measurable (combinedFeature F G) := by
  apply ContinuousMap.measurable_of_eval
  rintro ⟨b, u⟩
  cases b
  · exact (continuous_eval_const u).measurable.comp hF
  · exact (continuous_eval_const u).measurable.comp hG

private theorem norm_combinedFeature_le (F : X → C(U, ℝ)) (G : X → C(V, ℝ)) (x : X) :
    ‖combinedFeature F G x‖ ≤ ‖F x‖ + ‖G x‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  rintro ⟨b, u⟩
  cases b
  · exact ((F x).norm_coe_le_norm u).trans (le_add_of_nonneg_right (norm_nonneg _))
  · exact ((G x).norm_coe_le_norm u).trans (le_add_of_nonneg_left (norm_nonneg _))

theorem memLp_combinedFeature {F : X → C(U, ℝ)} {G : X → C(V, ℝ)} {p : ℝ≥0∞}
    (hFm : Measurable F) (hGm : Measurable G) (hF : MemLp F p q) (hG : MemLp G p q) :
    MemLp (combinedFeature F G) p q := by
  apply (hF.norm.add hG.norm).of_le (measurable_combinedFeature hFm hGm).aestronglyMeasurable
  filter_upwards with x
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    using norm_combinedFeature_le F G x
end Combined

/-- Scalar form of the LLN error transported by a factorization at two points.
The factorization may hold only on a q-full event; all finite sample indices are
supplied on the common sample event. -/
theorem factored_product_kernel_error_le
    {X Ω U V : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [MetricSpace U] [CompactSpace U] {q : Measure X} [IsProbabilityMeasure q]
    {Xs : ℕ → Ω → X} {F : X → C(U, ℝ)} {f : X → V → ℝ} {r : V → ℝ}
    (hFm : Measurable F) (hF : MemLp F 2 q)
    (n : ℕ) (ω : Ω) (w v : V) (u t : U)
    (hrw : 0 ≤ r w) (hrv : 0 ≤ r v)
    (hwq : ∀ᵐ x ∂q, f x w = r w * F x u)
    (hvq : ∀ᵐ x ∂q, f x v = r v * F x t)
    (hws : ∀ i < n, f (Xs i ω) w = r w * F (Xs i ω) u)
    (hvs : ∀ i < n, f (Xs i ω) v = r v * F (Xs i ω) t) :
    |(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, f (Xs i ω) w * f (Xs i ω) v) -
      ∫ x, f x w * f x v ∂q| ≤
      ‖(n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, productFeature (F (Xs i ω))) -
        ∫ x, productFeature (F x) ∂q‖ * (r w * r v) := by
  have hsum : (∑ i ∈ Finset.range n, f (Xs i ω) w * f (Xs i ω) v) =
      (r w * r v) * ∑ i ∈ Finset.range n, F (Xs i ω) u * F (Xs i ω) t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hws i (Finset.mem_range.mp hi), hvs i (Finset.mem_range.mp hi)]
    ring
  have hpop : (∫ x, f x w * f x v ∂q) =
      (r w * r v) * ∫ x, F x u * F x t ∂q := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hwq, hvq] with x hxw hxv
    rw [hxw, hxv]
    ring
  rw [hsum, hpop]
  calc
    _ = (r w * r v) * |(n : ℝ)⁻¹ *
        (∑ i ∈ Finset.range n, F (Xs i ω) u * F (Xs i ω) t) -
        ∫ x, F x u * F x t ∂q| := by
      calc
        _ = |(r w * r v) * ((n : ℝ)⁻¹ *
            (∑ i ∈ Finset.range n, F (Xs i ω) u * F (Xs i ω) t) -
            ∫ x, F x u * F x t ∂q)| := by congr 1; ring
        _ = _ := by rw [abs_mul, abs_of_nonneg (mul_nonneg hrw hrv)]
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (productFeature_error_le hFm hF n ω u t) (mul_nonneg hrw hrv)

end SingularLearningTheory.BayesGibbs
