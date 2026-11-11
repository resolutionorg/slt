/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FeatureEnvelopeSix
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import SLT.EmpiricalProcess.Defs
import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Strong law for products of a continuous feature

Let $F(x) \in C(U)$ be a random continuous feature on a compact metric space $U$, with $\|F\|$ in
$L^2(q)$. Applying the strong law of large numbers in the Banach space $C(U \times U)$ to the
product feature $F(x, u)F(x, v)$ shows that the empirical second moments
$\frac{1}{n}\sum_{i<n} F(X_i, u)F(X_i, v)$ converge to $E_q[F(x, u)F(x, v)]$ almost surely,
uniformly in $(u, v)$. With the feature of the log density ratio, this controls the empirical
covariance of $f$ uniformly over pairs of parameters, which the replacement of the empirical
functional variance by its population form needs.

## Main results

* `SingularLearningTheory.BayesGibbs.productFeature_strongLaw`: the uniform error of the empirical
  mean of `SingularLearningTheory.BayesGibbs.productFeature` tends to zero almost surely.
* `SingularLearningTheory.BayesGibbs.productFeature_error_le`: the uniform error bounds the error of
  the empirical second moment at each pair $(u, v)$.
* `SingularLearningTheory.BayesGibbs.measurable_productFeature_error`: the uniform error is measurable.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {U : Type*} [MetricSpace U] [CompactSpace U]

/-- Raw product feature, retaining the full covariance diagonal. -/
@[expose] noncomputable def productFeature (h : C(U, ℝ)) : C(U × U, ℝ) :=
  h.comp ⟨Prod.fst, continuous_fst⟩ * h.comp ⟨Prod.snd, continuous_snd⟩

@[simp] theorem productFeature_apply (h : C(U, ℝ)) (u v : U) :
    productFeature h (u, v) = h u * h v := rfl

private theorem continuous_productFeature : Continuous (productFeature (U := U)) :=
  (ContinuousMap.compCLM ℝ ℝ (⟨Prod.fst, continuous_fst⟩ : C(U × U, U))).continuous.mul
    (ContinuousMap.compCLM ℝ ℝ (⟨Prod.snd, continuous_snd⟩ : C(U × U, U))).continuous

private theorem norm_productFeature_le (h : C(U, ℝ)) : ‖productFeature h‖ ≤ ‖h‖ ^ 2 := by
  apply (ContinuousMap.norm_le _ (sq_nonneg _)).mpr
  intro uv
  rw [productFeature_apply, norm_mul, pow_two]
  exact mul_le_mul (h.norm_coe_le_norm uv.1) (h.norm_coe_le_norm uv.2)
    (norm_nonneg _) (norm_nonneg _)

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {Xs : ℕ → Ω → X} {F : X → C(U, ℝ)}

private theorem integrable_productFeature (hFm : Measurable F) (hF : MemLp F 2 q) :
    Integrable (fun x ↦ productFeature (F x)) q :=
  hF.integrable_norm_pow'.mono' (continuous_productFeature.measurable.comp hFm).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ norm_productFeature_le (F x))

/-- Banach-valued strong law for the full product kernel. Uniform convergence
on U×U replaces a separate feature-derivative uniform-LLN closure. -/
theorem productFeature_strongLaw (hFm : Measurable F) (hF : MemLp F 2 q)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ ‖(n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, productFeature (F (Xs i ω))) -
        ∫ x, productFeature (F x) ∂q‖) atTop (𝓝 0) := by
  let G : X → C(U × U, ℝ) := fun x ↦ productFeature (F x)
  have hGm : Measurable G := continuous_productFeature.measurable.comp hFm
  have hGi : Integrable G q := integrable_productFeature hFm hF
  have hG0 : Integrable (G ∘ Xs 0) P := by
    apply (integrable_map_measure hGm.aestronglyMeasurable (hX 0).aemeasurable).mp
    rwa [hlaw 0]
  have hident : ∀ i, IdentDistrib (G ∘ Xs i) (G ∘ Xs 0) P P := fun i ↦
    (show IdentDistrib (Xs i) (Xs 0) P P from
      ⟨(hX i).aemeasurable, (hX 0).aemeasurable, (hlaw i).trans (hlaw 0).symm⟩).comp hGm
  have hstrong := strong_law_ae (fun i ↦ G ∘ Xs i) hG0
    (fun i j hij ↦ (hind.indepFun hij).comp hGm hGm) hident
  have hmean : (∫ ω, G (Xs 0 ω) ∂P) = ∫ x, G x ∂q := by
    rw [← hlaw 0, integral_map (hX 0).aemeasurable hGm.aestronglyMeasurable]
  filter_upwards [hstrong] with ω hω
  dsimp only [Function.comp_def] at hω
  rw [hmean] at hω
  simpa only [sub_self, norm_zero] using (hω.sub (tendsto_const_nhds (x := ∫ x, G x ∂q))).norm

/-- The same scalar controls all diagonal and off-diagonal products. -/
theorem productFeature_error_le (hFm : Measurable F) (hF : MemLp F 2 q)
    (n : ℕ) (ω : Ω) (u v : U) :
    |(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, F (Xs i ω) u * F (Xs i ω) v) -
        ∫ x, F x u * F x v ∂q| ≤
      ‖(n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, productFeature (F (Xs i ω))) -
        ∫ x, productFeature (F x) ∂q‖ := by
  have h := ContinuousMap.norm_coe_le_norm
    ((n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, productFeature (F (Xs i ω))) -
      ∫ x, productFeature (F x) ∂q) (u, v)
  simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    smul_eq_mul, productFeature_apply, ContinuousMap.integral_apply (integrable_productFeature hFm hF),
    Real.norm_eq_abs] using h

/-- Measurability of the uniform raw product-feature LLN error. Keeping the
compact domain abstract avoids repeated reductions of sigma metrics. -/
theorem measurable_productFeature_error
    {U X Ω : Type*} [MetricSpace U] [CompactSpace U]
    [MeasurableSpace X] [MeasurableSpace Ω]
    {q : Measure X} {Xs : ℕ → Ω → X} {F : X → C(U, ℝ)}
    (hFm : Measurable F) (hX : ∀ i, Measurable (Xs i)) (n : ℕ) :
    Measurable (fun ω ↦
      ‖(n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, productFeature (F (Xs i ω))) -
        ∫ x, productFeature (F x) ∂q‖) := by
  have hG : ∀ i, Measurable (fun ω ↦ productFeature (F (Xs i ω))) := fun i ↦
    (continuous_productFeature (U := U)).measurable.comp (hFm.comp (hX i))
  have hsum : Measurable (fun ω ↦
      ∑ i ∈ Finset.range n, productFeature (F (Xs i ω))) :=
    Finset.measurable_sum _ fun i _ ↦ hG i
  exact ((hsum.const_smul ((n : ℝ)⁻¹)).sub measurable_const).norm

end SingularLearningTheory.BayesGibbs
