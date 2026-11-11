/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.Envelope
public import SLT.BayesGibbs.Prior.AETransport
public import SLT.MaximumLikelihood.Geometry
public import SLT.FreeEnergy.FundamentalConditions
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The empirical process envelope under the prior

For each $n \ge 1$, almost surely, the scaled deviation of the empirical loss from $K$ is bounded
by the norms of the empirical processes on the charts and on the tail, for almost every
parameter under the prior:
$$\sqrt{n}\,|K_n(w) - K(w)| \le \sqrt{K(w)}\,\max(\|\Psi_n\|, \|\Psi^T_n\|)$$
(`SingularLearningTheory.BayesGibbs.ae_relative_envelope_of_chart_and_tail`). Below the level
$K < \delta$ of the resolution atlas the transport of the prior to the charts covers almost every
parameter. There $\sqrt{K} = u^k$ and the deviation is $u^k\Psi_n(u)$. On the tail
$K \ge \delta$ the deviation is $\sqrt{K}$ times the tail process. No assumption that the charts
cover every parameter is needed. This envelope bounds the posterior observables of
[Wat09, Theorem 6.8] through the sixth moments of the empirical processes.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

variable {d : ℕ} {X Ω Ω' ΩT : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [MeasurableSpace Ω'] [MeasurableSpace ΩT]
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {PT : Measure ΩT} [IsProbabilityMeasure PT]
  {Xs : ℕ → Ω → X} {f : X → (Fin d → ℝ) → ℝ}
  {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W) (L : R.ResolvedLikelihood q f)

/-- The quantitative relative fluctuation envelope under the prior. Unlike the
pointwise MLE version this needs no chart-coverage assumption: transport supplies
prior-a.e. coverage below R.δ, and the tail process covers K≥R.δ. -/
theorem ae_relative_envelope_of_chart_and_tail
    (hW : MeasurableSet W) (hφ : IntegrableOn φ W)
    (hf : Measurable (Function.uncurry f)) (hK : ∀ w, K w = ∫ x, f x w ∂q)
    [CompactSpace {w // w ∈ W ∧ R.δ ≤ K w}]
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (E : EmpiricalProcessLimit q
      (fun x (u : ResolutionAtlas.Domain R) ↦ L.a u.1 x u.2) Xs P P')
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P PT)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P, ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
      Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤
        Real.sqrt (K w) * max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖ := by
  have hn0 : 0 < n := by omega
  have hKm := MaximumLikelihood.measurable_K_of_integral hf hK
  filter_upwards [MaximumLikelihood.sampleLoss_chart_ae R L hX hlaw E hn, T.Ψ_ae_eq n]
    with ω hc ht
  have hKnm : Measurable (empiricalLoss f Xs n ω) :=
    (measurable_uncurry_empiricalLoss hf hX n).of_uncurry_left
  apply R.ae_prior_of_chart_and_tail hW hφ
    (measurableSet_le (measurable_const.mul (hKnm.sub hKm).abs)
      (hKm.sqrt.mul measurable_const))
  · intro α u hu
    let v : cube d (R.b α) := ⟨u, hu⟩
    let h : ℝ := ∏ j, u j ^ R.k α j
    have hh0 : 0 ≤ h := MaximumLikelihood.monomial_nonneg
      (fun j ↦ hu.1 j)
    have hKg : K (R.g α u) = h ^ 2 := ResolutionAtlas.K_g_eq_square R α v
    have hdev : Real.sqrt n * (empiricalLoss f Xs n ω (R.g α u) - K (R.g α u)) =
        h * E.Ψ n ω ⟨α, v⟩ := by
      apply MaximumLikelihood.centered_deviation_of_sample_identity hn0
      rw [hc α v, hKg]
      change (n : ℝ) * h ^ 2 + Real.sqrt n * h * E.Ψ n ω ⟨α, v⟩ =
        (n : ℝ) * h ^ 2 + Real.sqrt n * (h * E.Ψ n ω ⟨α, v⟩)
      ring
    have hnorm : |E.Ψ n ω ⟨α, v⟩| ≤ ‖E.Ψ n ω‖ := by
      simpa only [Real.norm_eq_abs] using (E.Ψ n ω).norm_coe_le_norm ⟨α, v⟩
    calc Real.sqrt n * |empiricalLoss f Xs n ω (R.g α u) - K (R.g α u)|
        = |Real.sqrt n * (empiricalLoss f Xs n ω (R.g α u) - K (R.g α u))| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = h * |E.Ψ n ω ⟨α, v⟩| := by rw [hdev, abs_mul, abs_of_nonneg hh0]
      _ ≤ h * ‖E.Ψ n ω‖ := mul_le_mul_of_nonneg_left hnorm hh0
      _ ≤ Real.sqrt (K (R.g α u)) * max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖ := by
          rw [hKg, Real.sqrt_sq hh0]
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) hh0
  · intro w hw hwδ
    have hKw : 0 < K w := R.δ_pos.trans_le hwδ
    let v : {w // w ∈ W ∧ R.δ ≤ K w} := ⟨w, hw, hwδ⟩
    have htval : T.Ψ n ω v = tailProcess K f Xs n ω w := by
      rw [ht v, tailProcess_eq_empiricalProcess hK]
      rfl
    have hnorm : |tailProcess K f Xs n ω w| ≤ ‖T.Ψ n ω‖ := by
      rw [← htval, ← Real.norm_eq_abs]
      exact (T.Ψ n ω).norm_coe_le_norm v
    calc Real.sqrt n * |empiricalLoss f Xs n ω w - K w|
        = |Real.sqrt n * (empiricalLoss f Xs n ω w - K w)| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = Real.sqrt (K w) * |tailProcess K f Xs n ω w| := by
          rw [empiricalLoss_centered_tail K f Xs hn0 ω hKw,
            abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (K w) * ‖T.Ψ n ω‖ :=
          mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (K w) * max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)

end SingularLearningTheory.BayesGibbs
