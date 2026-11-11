/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import SLT.BayesGibbs.CompactBase.Finite
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Stein's identity on a compact base

Stein's identity for a Gaussian field of general covariance on a compact base, by finite
quantisation and dominated convergence.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory.GaussianPosterior

section Limits

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K]
  [BorelSpace K] {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (𝒞 : PSDKernel K) {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → C(K, ℝ))
  {q : ℕ → K → K} {ε : ℕ → ℝ}

omit [MetricSpace K] [CompactSpace K] [Nonempty K] [BorelSpace K] [IsFiniteMeasure ρ] in
private theorem map_quantize_ne_zero {q : K → K} (hq : Measurable q)
    (hρ : ρ ≠ 0) : ρ.map q ≠ 0 := by
  intro h
  apply hρ
  have := map_quantize_univ ρ hq
  rw [h, Measure.coe_zero, Pi.zero_apply] at this
  exact Measure.measure_univ_eq_zero.1 this.symm


omit [MeasurableSpace K] [BorelSpace K] [Nonempty K] in
/-- The diagonal of a continuous kernel on a compact base is bounded. -/
theorem _root_.PSDKernel.exists_diag_bound : ∃ c : ℝ, 0 ≤ c ∧ ∀ x, 𝒞.C x x ≤ c := by
  set f : C(K, ℝ) := ⟨fun x ↦ 𝒞.C x x, 𝒞.continuous_diag⟩
  exact ⟨‖f‖, norm_nonneg f, fun x ↦ (le_abs_self _).trans
    ((Real.norm_eq_abs _).symm ▸ f.norm_coe_le_norm x)⟩

omit [Nonempty K] [MeasurableSpace K] [BorelSpace K] in
/-- Dominating functions of the form `C (1 + ‖g‖²)` are integrable. -/
theorem integrable_const_mul_one_add_sq (hsq : Integrable (fun ω ↦ ‖g ω‖ ^ 2) P) (C : ℝ) :
    Integrable (fun ω ↦ C * (1 + ‖g ω‖ ^ 2)) P :=
  ((integrable_const (1 : ℝ)).add hsq).const_mul C

omit [Nonempty K] in
private theorem measurable_compactH_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (hg : ∀ x, Measurable fun ω ↦ g ω x) (hq : ∀ n, Measurable (q n))
    (hfin : ∀ n, (Set.range (q n)).Finite) (n : ℕ) :
    Measurable fun ω ↦ compactH β lam (ρ.map (q n)) (g ω) := by
  have := nonempty_atoms ρ (hq n) (hfin n) hρ
  have : (fun ω ↦ compactH β lam (ρ.map (q n)) (g ω)) = fun ω ↦
      quartetH β lam (atomWt ρ (hfin n)) (fun i ↦ g ω (atomPt ρ (hfin n) i)) :=
    funext fun ω ↦ compactH_map_eq ρ hβ hlam (g ω) (hq n) (hfin n)
  rw [this]
  exact (continuous_quartetH hβ hlam (atomWt_pos ρ (hfin n))).measurable.comp
    (Measurable.of_eval fun i ↦ hg _)

omit [Nonempty K] in
private theorem measurable_compactV_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (hg : ∀ x, Measurable fun ω ↦ g ω x) (hq : ∀ n, Measurable (q n))
    (hfin : ∀ n, (Set.range (q n)).Finite) (n : ℕ) :
    Measurable fun ω ↦ compactV (ρ.map (q n)) β lam 𝒞 (g ω) := by
  have := nonempty_atoms ρ (hq n) (hfin n) hρ
  have : (fun ω ↦ compactV (ρ.map (q n)) β lam 𝒞 (g ω)) = fun ω ↦
      quartetVgen β lam (atomWt ρ (hfin n)) (𝒞.kernelMatrix (atomPt ρ (hfin n)))
        (fun i ↦ g ω (atomPt ρ (hfin n) i)) :=
    funext fun ω ↦ compactV_map_eq ρ hβ hlam 𝒞 (g ω) (hq n) (hfin n) hρ
  rw [this]
  exact (continuous_quartetVgen hβ hlam (atomWt_pos ρ (hfin n)) _).measurable.comp
    (Measurable.of_eval fun i ↦ hg _)

/-! ### Dominated convergence along the quantisation sequence -/

variable (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (hg : ∀ x, Measurable fun ω ↦ g ω x)
  (hsq : Integrable (fun ω ↦ ‖g ω‖ ^ 2) P) (hq : ∀ n, Measurable (q n))
  (hfin : ∀ n, (Set.range (q n)).Finite) (hε : Tendsto ε atTop (𝓝 0))
  (hqε : ∀ n x, dist x (q n x) < ε n)
include hβ hlam hρ hg hsq hq hfin hε hqε

omit [Nonempty K] in
/-- **`E H_{ρₙ}(g) → E H_ρ(g)`.** -/
private theorem tendsto_integral_compactH_map :
    Tendsto (fun n ↦ ∫ ω, compactH β lam (ρ.map (q n)) (g ω) ∂P) atTop
      (𝓝 (∫ ω, compactH β lam ρ (g ω) ∂P)) := by
  have hB : 0 ≤ Real.sqrt (2 * lam / β) := Real.sqrt_nonneg _
  refine tendsto_integral_of_dominated_convergence
    (fun ω ↦ (Real.sqrt (2 * lam / β) + 1 / 2) * (1 + ‖g ω‖ ^ 2))
    (fun n ↦ (measurable_compactH_map ρ g hβ hlam hρ hg hq hfin n).aestronglyMeasurable)
    (integrable_const_mul_one_add_sq P g hsq _)
    (fun n ↦ Filter.Eventually.of_forall fun ω ↦ ?_)
    (Filter.Eventually.of_forall fun ω ↦ tendsto_compactH_map ρ hβ hlam hρ (g ω) hq hε hqε)
  rw [Real.norm_eq_abs]
  refine (abs_compactH_le (ρ.map (q n)) hβ hlam (g ω) (map_quantize_ne_zero ρ (hq n) hρ)
    le_rfl).trans ?_
  nlinarith [norm_nonneg (g ω), sq_nonneg (‖g ω‖ - 1)]

omit [MeasurableSpace Ω] hg hsq hfin hε hqε in
private theorem abs_compactV_map_le {c : ℝ} (hc : ∀ x, 𝒞.C x x ≤ c) (n : ℕ) (ω : Ω) :
    |compactV (ρ.map (q n)) β lam 𝒞 (g ω)| ≤ c * (2 * lam / β + ‖g ω‖ ^ 2 / 4) := by
  have h0 := compactV_nonneg (ρ.map (q n)) hβ hlam 𝒞 (g ω) (map_quantize_ne_zero ρ (hq n) hρ)
  rw [abs_of_nonneg h0]
  exact compactV_le (ρ.map (q n)) hβ hlam 𝒞 (g ω) (map_quantize_ne_zero ρ (hq n) hρ) hc le_rfl

/-- **`E V_{ρₙ}(g) → E V_ρ(g)`.** -/
private theorem tendsto_integral_compactV_map :
    Tendsto (fun n ↦ ∫ ω, compactV (ρ.map (q n)) β lam 𝒞 (g ω) ∂P) atTop
      (𝓝 (∫ ω, compactV ρ β lam 𝒞 (g ω) ∂P)) := by
  obtain ⟨c, hc0, hc⟩ := 𝒞.exists_diag_bound
  have hB : 0 ≤ 2 * lam / β := div_nonneg (by linarith) hβ.le
  refine tendsto_integral_of_dominated_convergence
    (fun ω ↦ (c * (2 * lam / β + 1 / 4)) * (1 + ‖g ω‖ ^ 2))
    (fun n ↦ (measurable_compactV_map ρ 𝒞 g hβ hlam hρ hg hq hfin n).aestronglyMeasurable)
    (integrable_const_mul_one_add_sq P g hsq _)
    (fun n ↦ Filter.Eventually.of_forall fun ω ↦ ?_)
    (Filter.Eventually.of_forall fun ω ↦ tendsto_compactV_map ρ hβ hlam 𝒞 (g ω) hρ hq hε hqε)
  rw [Real.norm_eq_abs]
  refine (abs_compactV_map_le ρ 𝒞 g hβ hlam hρ hq hc n ω).trans ?_
  nlinarith [norm_nonneg (g ω), sq_nonneg ‖g ω‖, mul_nonneg hc0 hB,
    mul_nonneg hc0 (sq_nonneg ‖g ω‖)]

end Limits

end SingularLearningTheory.GaussianPosterior

namespace ProbabilityTheory.GaussianField

open SingularLearningTheory SingularLearningTheory.GaussianPosterior

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K]
  [BorelSpace K] {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (hρ : ρ ≠ 0) {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (Γ : GaussianField 𝒞 P)


include hβ hlam hρ

/-- **Gaussian integration by parts on the compact base**: `E H_ρ(G) = β E V_ρ(G)`. -/
theorem integral_compactH_eq :
    ∫ ω, compactH β lam ρ (Γ.G ω) ∂P = β * ∫ ω, compactV ρ β lam 𝒞 (Γ.G ω) ∂P := by
  obtain ⟨q, hq, hfin, hqε⟩ := CompactSpace.exists_quantization_seq (K := K)
  have h1 := tendsto_integral_compactH_map ρ P Γ.G hβ hlam hρ Γ.measurable_eval
    Γ.integrable_sq_norm hq hfin tendsto_one_div_add_atTop_nhds_zero_nat hqε
  have h2 := (tendsto_integral_compactV_map ρ 𝒞 P Γ.G hβ hlam hρ Γ.measurable_eval
    Γ.integrable_sq_norm hq hfin tendsto_one_div_add_atTop_nhds_zero_nat hqε).const_mul β
  exact tendsto_nhds_unique h1 (h2.congr fun n ↦
    (Γ.integral_compactH_map_eq ρ hβ hlam hρ (hq n) (hfin n)).symm)


end ProbabilityTheory.GaussianField

namespace SingularLearningTheory.GaussianPosterior
end SingularLearningTheory.GaussianPosterior
