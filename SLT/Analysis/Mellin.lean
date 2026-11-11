/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.Mellin.InverseMellinBV
public import SLT.Analysis.Mellin.PowerLog
public import SLT.Analysis.Mellin.Defs

/-! # Mellin transforms

The proved counterpart of `SLTChallenge/Mellin.lean`. -/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology

/-- **Mellin inversion for functions of bounded variation.** If `f` has bounded variation near `t`,
the truncated inverse Mellin integrals converge to the average of the two one-sided limits of `f` at
`t`. The inverse integral is the symmetric limit `T → ∞`, as in Remark 4.3(1).

Relation to the source.
* **Strengthening.** Integrability of $f(t)\,t^c$ on the line $\operatorname{Re} z = c$ replaces the
  book's absolute convergence on a strip $a < \operatorname{Re} z < b$.

Source statement: [Wat09, Theorem 4.5] -/
theorem inverseMellin_tendsto_of_boundedVariation
    (f : ℝ → ℝ) (c : ℝ)
    (hconv : IntegrableOn (fun t ↦ f t * t ^ c) (Ioi 0))
    (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) (hεt : ε < t)
    (hbv : BoundedVariationOn f (Icc (t - ε) (t + ε)))
    (fp fm : ℝ) (hfp : Tendsto f (𝓝[>] t) (𝓝 fp))
    (hfm : Tendsto f (𝓝[<] t) (𝓝 fm)) :
    Tendsto (fun T ↦ inverseMellinTrunc c (SingularLearningTheory.mellinTransform f) t T)
      atTop (𝓝 (((fp + fm) / 2 : ℝ) : ℂ)) :=
  MellinAnalysis.inverseMellin_tendsto_of_boundedVariation f hconv ht hε hεt hbv hfp hfm

/-- **Holomorphy on a strip of absolute convergence.** Weighted integrability
at both boundary exponents gives a holomorphic Mellin transform in the intervening strip. -/
-- `hab` is unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
theorem mellinTransform_differentiableOn_strip
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (ha : IntegrableOn (fun t ↦ f t * t ^ a) (Ioi 0))
    (hb : IntegrableOn (fun t ↦ f t * t ^ b) (Ioi 0)) :
    DifferentiableOn ℂ (SingularLearningTheory.mellinTransform f)
      {z : ℂ | a < z.re ∧ z.re < b} :=
  MellinAnalysis.mellinTransform_differentiableOn_strip f a b ha hb

/-- **Mellin transform of a power times a power of the logarithm.** For `Re z > −λ`, the Mellin
transform of `f(t) = 𝟙_(0,a)(t) a^(−λ)/(m−1)! t^(λ−1) log(a/t)^(m−1)` is `a^z/(z+λ)^m`.

Relation to the source.
* **Strengthening.** The book's assumption $\lambda > 0$ is not needed.

Source statement: [Wat09, Example 4.7] -/
theorem mellinTransform_power_log
    (lam a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 1 ≤ m)
    (z : ℂ) (hz : -lam < z.re) :
    let f := (Ioo 0 a).indicator
      (fun t ↦ a ^ (-lam) / (m - 1).factorial * t ^ (lam - 1) * Real.log (a / t) ^ (m - 1))
    SingularLearningTheory.mellinTransform f z = (a : ℂ) ^ z / (z + (lam : ℂ)) ^ m :=
  by
  intro f
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hfac : ((m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hint : ∀ t : ℝ, (t : ℂ) ^ z * ((f t : ℝ) : ℂ) =
      ((a ^ (-lam) / (m - 1).factorial : ℝ) : ℂ) * ((t : ℂ) ^ z *
        (((Ioo 0 a).indicator
          (fun t ↦ t ^ (lam - 1) * Real.log (a / t) ^ (m - 1)) t : ℝ) : ℂ)) := by
    intro t
    simp only [f, Set.indicator]
    split_ifs <;> push_cast <;> ring
  have key := MellinAnalysis.mellinTransform_power_log lam a ha m hm z hz
  unfold SingularLearningTheory.mellinTransform at key ⊢
  simp_rw [hint]
  rw [MeasureTheory.integral_const_mul, key, Complex.ofReal_div, Complex.ofReal_cpow ha.le,
    Complex.ofReal_natCast]
  have hpow : (a : ℂ) ^ (((-lam : ℝ)) : ℂ) * (a : ℂ) ^ (z + lam) = (a : ℂ) ^ z := by
    rw [← Complex.cpow_add _ _ ha0]; congr 1; push_cast; ring
  rw [← hpow]
  field_simp

end SingularLearningTheory
