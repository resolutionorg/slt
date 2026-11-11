/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.RadialMoment
public import SLT.BayesGibbs.ExpMeasure
public import SLT.BayesGibbs.LaplaceDoubling.Basic

/-!
# Posterior moments of powers of $K$, with $K \ge 0$ almost everywhere

Under the two-sided bound $n\beta K/2 - c \le G \le 3n\beta K/2 + c$ on the potential and the
Laplace doubling bound on the prior, every nonnegative power $K^r$ is integrable under the tilted
measure $e^{-G}\nu / Z$, with $E[K^r] \le (4/(n\beta))^r\bigl((2(\log D + 2c))^r + C\bigr)$
(`SingularLearningTheory.BayesGibbs.posterior_rpow_moment_le_ae`). It needs $K \ge 0$ only almost
everywhere under $\nu$, as for the prior restricted to the parameter set: it applies the bound
for nonnegative $K$ to $\max(0, K)$, which agrees with $K$ almost everywhere.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {W : Type*} [MeasurableSpace W] {ν : Measure W} [IsFiniteMeasure ν]

/-- Every nonnegative radial power under the ambient posterior.
Prior-a.e. positivity suffices; K is replaced by max(0,K) off its full event. -/
theorem posterior_rpow_moment_le_ae {K G : W → ℝ}
    (hν : ν ≠ 0) (hKm : Measurable K) (hGm : Measurable G)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {n β c D r C : ℝ} (hn : 0 < n) (hβ : 0 < β) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hscalar : ∀ y : ℝ, 0 ≤ y → y ^ r ≤ C * Real.exp (y / 2))
    (hlow : ∀ᵐ w ∂ν, n * β * (K w / 2) - c ≤ G w)
    (hup : ∀ᵐ w ∂ν, G w ≤ n * β * (3 / 2 * K w) + c)
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :
    IsProbabilityMeasure (Measure.expMeasure ν G) ∧
      Integrable (fun w ↦ (K w) ^ r) (Measure.expMeasure ν G) ∧
      (∫ w, (K w) ^ r ∂Measure.expMeasure ν G) ≤
        (4 / (n * β)) ^ r * ((2 * (Real.log D + 2 * c)) ^ r + C) := by
  let K' := fun w ↦ max 0 (K w)
  have heq : K' =ᵐ[ν] K := hK0.mono fun w hw ↦ max_eq_right hw
  have hJ : ∀ a : ℝ, (∫ w, Real.exp (-(a * K' w)) ∂ν) =
      ∫ w, Real.exp (-(a * K w)) ∂ν := by
    intro a
    apply integral_congr_ae
    filter_upwards [heq] with w hw
    rw [hw]
  obtain ⟨hp, hi, hb⟩ := posterior_rpow_moment_le (K := K') hν (measurable_const.max hKm) hGm
    (fun _ ↦ le_max_left _ _)
    (by filter_upwards [heq, hKB] with w hw h; simpa only [hw] using h)
    hn hβ hc hD hr hC hscalar
    (by filter_upwards [heq, hlow] with w hw hl; simpa only [hw] using hl)
    (by filter_upwards [heq, hup] with w hw hu; simpa only [hw] using hu)
    (by simpa only [hJ] using hLD)
  have hep : (fun w ↦ (K' w) ^ r) =ᵐ[Measure.expMeasure ν G] (fun w ↦ (K w) ^ r) := by
    filter_upwards [ae_expMeasure_of_ae heq] with w hw
    rw [hw]
  exact ⟨hp, hi.congr hep, (integral_congr_ae hep) ▸ hb⟩

end SingularLearningTheory.BayesGibbs
