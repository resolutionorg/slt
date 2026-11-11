/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic

/-!
# Uniqueness of meromorphic continuation from a right half-plane

Two meromorphic functions on the complex plane which agree on a right half-plane
agree in a punctured neighbourhood of every point. This leaves their assigned values
at poles unrestricted. The proof propagates infinite order of their difference on
the connected plane, using Mathlib's meromorphic identity principle.
-/

public section

open Filter Set Topology

/-- Agreement on a right half-plane determines a meromorphic function on the complex
plane up to its assigned values at isolated points. This is the uniqueness principle
needed for the zeta continuation of [Wat09, Theorem 6.6]. -/
theorem MeromorphicOn.eventuallyEq_nhdsNE_of_eqOn_re_gt
    {f g : ℂ → ℂ} (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (c : ℝ) (hfg : ∀ z : ℂ, c < z.re → f z = g z) (z : ℂ) :
    f =ᶠ[𝓝[≠] z] g := by
  have he : f - g =ᶠ[𝓝[≠] ((c + 1 : ℝ) : ℂ)] 0 := by
    have hn : ∀ᶠ w : ℂ in 𝓝 ((c + 1 : ℝ) : ℂ), c < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with w hw
    exact sub_eq_zero.mpr (hfg w hw)
  have ho := (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ z)
    (meromorphicOrderAt_eq_top_iff.mpr he)
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp ho] with w hw
  exact sub_eq_zero.mp hw
