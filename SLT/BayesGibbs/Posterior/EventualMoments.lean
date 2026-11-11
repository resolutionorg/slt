/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FiniteSample.PosteriorFive
import SLT.BayesGibbs.Posterior.GibbsVarianceBounds
import SLT.BayesGibbs.Posterior.FirstMoment
import SLT.BayesGibbs.ExpMeasure
import SLT.BayesGibbs.Posterior.RadialMoment
public import SLT.BayesGibbs.LaplaceDoubling.Basic
public import SLT.FreeEnergy.FundamentalConditions

/-!
# The posterior is eventually a probability measure

`SingularLearningTheory.BayesGibbs.eventually_ae_posterior_probability_integrable` shows that for all
large $n$, almost surely, the posterior $e^{-n\beta K_n}\nu/Z_n$ is a probability measure under
which both $K$ and the empirical loss $K_n$ are integrable. It assumes that $K$ is bounded and
nonnegative, that $\sqrt n\,|K_n - K| \le L_n \sqrt K$, and the Laplace doubling bound
$\int e^{-n\beta K/4}\,d\nu \le D \int e^{-3n\beta K/2}\,d\nu$. These facts make the Gibbs errors
well defined on one common event.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- Posterior probability and both Gibbs integrability facts on a
common eventual event, derived from the envelope and Laplace bounds. -/
theorem eventually_ae_posterior_probability_integrable {d : ℕ} {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν] {P : Measure Ω}
    {K : (Fin d → ℝ) → ℝ} {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (hν : ν ≠ 0) (hKm : Measurable K) (hf : Measurable (Function.uncurry f))
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {L : ℕ → Ω → ℝ}
    (he : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ᵐ w ∂ν,
      Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤ L n ω * Real.sqrt (K w))
    {β D : ℝ} (hβ : 0 < β) (hD : 1 ≤ D)
    (hLD : ∀ᶠ n : ℕ in atTop, ∫ w, Real.exp (-((n : ℝ) * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * (n : ℝ) * β / 2 * K w)) ∂ν) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w)
      IsProbabilityMeasure Q ∧ Integrable K Q ∧ Integrable (empiricalLoss f Xs n ω) Q := by
  filter_upwards [hLD, eventually_ge_atTop 1] with n hLDn hn
  filter_upwards [he n hn] with ω heω
  let Kn := empiricalLoss f Xs n ω
  let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * Kn w)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hKnm : Measurable Kn := by
    unfold Kn empiricalLoss
    exact (Finset.measurable_sum _ fun i _ ↦ hf.of_uncurry_left).div_const _
  have hsand : ∀ᵐ w ∂ν,
      (n : ℝ) * β * (K w / 2) - β / 2 * L n ω ^ 2 ≤ (n : ℝ) * β * Kn w ∧
      (n : ℝ) * β * Kn w ≤ (n : ℝ) * β * (3 / 2 * K w) + β / 2 * L n ω ^ 2 := by
    filter_upwards [hK0, heω] with w hw0 hwe
    simpa only [zero_div, add_zero, zero_mul] using
      tilted_exponent_bounds (f := 0) (A := 0) (σ := 0) hw0 hn' hβ
        ⟨le_rfl, zero_le_one⟩ hwe (by simp)
  obtain ⟨hQ, hKi, _⟩ := posterior_first_moment_le_ae
    (G := fun w ↦ (n : ℝ) * β * Kn w) hν hKm (hKnm.const_mul _)
    hK0 hKB hn' hβ (by positivity : 0 ≤ β / 2 * L n ω ^ 2) hD
    (hsand.mono fun _ h ↦ h.1) (hsand.mono fun _ h ↦ h.2) hLDn
  letI : IsProbabilityMeasure Q := hQ
  exact ⟨hQ, hKi, (integrable_empirical_and_abs_gibbs_training_le hKi hKnm.aestronglyMeasurable
    (ae_expMeasure_of_ae hK0) hn' (ae_expMeasure_of_ae heω)).1⟩

end SingularLearningTheory.BayesGibbs
