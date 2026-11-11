/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.LaplaceDoubling.FromLimits
public import SLT.BayesGibbs.ExpMeasure
public import SLT.SingularIntegrals.Volume.Atlas
public import SLT.SingularIntegrals.Volume.Consequences
import SLT.SingularIntegrals.Resolution
public import SLT.Resolution.Atlas
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Laplace doubling bound from a nondegenerate resolution atlas

For a nondegenerate resolution atlas of $K$ on a compact set $W$ with prior $\varphi$,
`SingularLearningTheory.NondegenerateResolutionAtlas.eventually_laplace_doubling` gives a constant
$D \ge 1$ such that, for all large $n$,
$$\int_W e^{-n\beta K/4}\varphi \le D \int_W e^{-3n\beta K/2}\varphi.$$
Both integrals, scaled by $n^\lambda/(\log n)^{m-1}$, converge to positive limits by the
asymptotics of the sublevel volume of the atlas, and the bound follows. The bounds on posterior
moments take this inequality as a hypothesis.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace SingularLearningTheory.NondegenerateResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- The volume coefficient supplies the deterministic Laplace doubling
bound for posterior estimates. Only an eventual bound is needed. -/
theorem eventually_laplace_doubling (R : NondegenerateResolutionAtlas K φ W)
    (hW : IsCompact W) (hKm : Measurable K) (hKc : ContinuousOn K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) {β : ℝ} (hβ : 0 < β) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      (∫ w, Real.exp (-((n : ℝ) * β / 4 * K w))
        ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))) ≤
      D * ∫ w, Real.exp (-(3 * (n : ℝ) * β / 2 * K w))
        ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)) := by
  obtain ⟨c, hc, hV⟩ := R.exists_sublevelVolume_limit hW.measurableSet hKm hφ hφi
  have hLap := (sublevelVolume_limit_consequences hW hKc hK hφ hφi
    R.toResolutionAtlas.mult_pos hc hV).1
  let s : ℕ → ℝ := fun n ↦ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1)
  let Z : ℝ → ℕ → ℝ := fun a n ↦ ∫ w, Real.exp (-((n : ℝ) * a * K w))
    ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))
  have hZ (a : ℝ) (ha : 0 < a) :
      Tendsto (fun n ↦ s n * Z a n) atTop (𝓝 (c * Real.Gamma (R.rlct + 1) / a ^ R.rlct)) := by
    have ht := (hLap a ha).comp tendsto_natCast_atTop_atTop
    simpa only [s, Z, Function.comp_def, BayesGibbs.integral_exp_restricted_prior
      hW.measurableSet hφ hφi, normalizedPartitionFunction] using ht
  have hs : ∀ᶠ n : ℕ in atTop, 0 < s n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _)
      (pow_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < n))) _)
  have hβ₂ : 0 < 3 * β / 2 := by positivity
  have hc₂ : 0 < c * Real.Gamma (R.rlct + 1) / (3 * β / 2) ^ R.rlct :=
    div_pos (mul_pos hc (Real.Gamma_pos_of_pos (by linarith [R.toResolutionAtlas.rlct_pos])))
      (Real.rpow_pos_of_pos hβ₂ _)
  obtain ⟨D, hD, hDn⟩ := BayesGibbs.eventually_doubling_of_normalized_limits hs
    (hZ (β / 4) (by positivity)) (hZ (3 * β / 2) hβ₂) hc₂
  refine ⟨D, hD, hDn.mono fun n hn ↦ ?_⟩
  simpa only [Z, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hn

end SingularLearningTheory.NondegenerateResolutionAtlas
