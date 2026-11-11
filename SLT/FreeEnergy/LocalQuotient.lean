/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.AnalyticDivision
public import SLT.Resolution.Atlas

/-!
# Analytic division by a monomial at every point of the chart cube

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 5.2.3], the division at a point of `U_α` | |
| | `AnalyticOnNhd.analyticAt_factor_monomial_of_bound_on_cube` |

`AnalyticAt.analyticAt_factor_monomial_of_bound` divides an analytic `A : ℝ^d → E` by the
monomial `u^k` at the origin, given `‖T (A u)‖ ≤ C u^k` on a positive cube. Here the same is done
at an arbitrary point `a` of the closed cube `[0, b]^d`, given the bound on the whole cube: the
coordinates with `a_j = 0` carry the vanishing order `k_j`, the others are divided out as
nonvanishing analytic factors. Near an upper face `a_j = b` the cube lies on the side `u_j < b`,
so the origin lemma is applied after the inward reflection `t_j ↦ a_j − t_j` ([Hit26]'s
argument only ever looks at the origin of a chart).
-/

public section

namespace SingularLearningTheory.AnalyticDivision

open Filter Topology Set

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- [Hit26, Lemma 5.2.3], the division step at a point
`a` of the cube: if `A` is analytic on a neighbourhood of `[0, b]^d` and `‖T (A u)‖ ≤ C u^k` on the
cube for an injective `T`, then `A u = u^k • G u` near `a` with `G` analytic at `a`. -/
theorem _root_.AnalyticOnNhd.analyticAt_factor_monomial_of_bound_on_cube {L : Type*}
    [NormedAddCommGroup L]
    [NormedSpace ℝ L] (T : E →L[ℝ] L) (hT : Function.Injective T) (k : Fin d → ℕ)
    {A : (Fin d → ℝ) → E} {b : ℝ} (hb : 0 < b) (hA : AnalyticOnNhd ℝ A (cube d b)) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u ∈ cube d b, ‖T (A u)‖ ≤ C * ∏ i, u i ^ k i) {a : Fin d → ℝ}
    (ha : a ∈ cube d b) :
    ∃ G : (Fin d → ℝ) → E, AnalyticAt ℝ G a ∧ ∀ᶠ u in 𝓝 a, A u = (∏ i, u i ^ k i) • G u := by
  classical
  -- the inward sign, the reduced exponents, and the affine change of variables
  set σ : Fin d → ℝ := fun j ↦ if a j = b then -1 else 1 with hσ
  have hσsq : ∀ j, σ j * σ j = 1 := fun j ↦ by simp only [hσ]; split_ifs <;> norm_num
  set k' : Fin d → ℕ := fun j ↦ if a j = 0 then k j else 0 with hk'
  set ψ : (Fin d → ℝ) → (Fin d → ℝ) := fun u j ↦ σ j * (u j - a j) with hψ
  set φ : (Fin d → ℝ) → (Fin d → ℝ) := fun t j ↦ a j + σ j * t j with hφ
  have hφψ : ∀ u, φ (ψ u) = u := fun u ↦ by
    funext j
    simp only [hφ, hψ]
    rw [← mul_assoc, hσsq]
    ring
  have hφ0 : φ 0 = a := by funext j; simp [hφ]
  have hψa : ψ a = 0 := by funext j; simp [hψ]
  have hproj : ∀ (j : Fin d) (x : Fin d → ℝ), AnalyticAt ℝ (fun u : Fin d → ℝ ↦ u j) x := fun j x ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).analyticAt x
  have hφan : AnalyticAt ℝ φ 0 :=
    AnalyticAt.pi fun j ↦ analyticAt_const.add (analyticAt_const.mul (hproj j 0))
  have hψan : AnalyticAt ℝ ψ a :=
    AnalyticAt.pi fun j ↦ analyticAt_const.mul ((hproj j a).sub analyticAt_const)
  have hAφ : AnalyticAt ℝ (A ∘ φ) 0 := by
    have := hA a ha
    rw [← hφ0] at this
    exact this.comp hφan
  -- a positive cube of inward increments staying inside `[0, b]^d`
  obtain ⟨ε, hε, hεb, hεa⟩ : ∃ ε > 0, ε ≤ b ∧ ∀ j, a j < b → ε ≤ b - a j := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε ≤ b ∧ ∀ j, a j < b → ε ≤ b - a j := by
      refine (eventually_le_nhds hb).and (eventually_all.mpr fun j ↦ ?_)
      by_cases h : a j < b
      · exact (eventually_le_nhds (sub_pos.mpr h)).mono fun ε hε _ ↦ hε
      · exact Eventually.of_forall fun ε h' ↦ absurd h' h
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (ε ≤ b ∧ ∀ j, a j < b → ε ≤ b - a j) ∧ ε ∈ Ioi (0 : ℝ) :=
      (eventually_nhdsWithin_of_eventually_nhds h1).and self_mem_nhdsWithin
    obtain ⟨ε, ⟨hεb, hεa⟩, hε⟩ := h2.exists
    exact ⟨ε, hε, hεb, hεa⟩
  have hmem : ∀ t ∈ ocube _ ε, φ t ∈ cube d b := by
    intro t ht
    refine mem_cube.2 fun j ↦ ?_
    obtain ⟨ht0, htε⟩ := ht j (mem_univ j)
    obtain ⟨ha0, hab⟩ := mem_cube.1 ha j
    simp only [hφ, hσ]
    split_ifs with h
    · exact ⟨by linarith, by linarith⟩
    · have hlt : a j < b := lt_of_le_of_ne hab h
      exact ⟨by linarith, by linarith [hεa j hlt]⟩
  have hbound' : ∀ t ∈ ocube _ ε,
      ‖T ((A ∘ φ) t)‖ ≤ (C * ∏ j, if a j = 0 then 1 else b ^ k j) * ∏ j, t j ^ k' j := by
    intro t ht
    refine (hbound _ (hmem t ht)).trans ?_
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
      (fun j _ ↦ pow_nonneg ((hmem t ht).1 j) _) fun j _ ↦ ?_) hC
    by_cases h0 : a j = 0
    · simp only [h0, ite_true, hk', one_mul, hφ, hσ, hb.ne, ite_false, zero_add]
      exact le_rfl
    · simp only [h0, ite_false, hk', pow_zero, mul_one]
      exact pow_le_pow_left₀ ((hmem t ht).1 j) ((hmem t ht).2 j) _
  obtain ⟨G', hG', hAG'⟩ :=
    AnalyticAt.analyticAt_factor_monomial_of_bound T hT (∑ i, k' i) k' rfl hAφ hε hbound'
  -- the nonvanishing factor `∏_{a_j ≠ 0} u_j^{k_j}`
  set Pc : (Fin d → ℝ) → ℝ := fun u ↦ ∏ j, if a j = 0 then 1 else u j ^ k j with hPc
  have hPcan : AnalyticAt ℝ Pc a := Finset.analyticAt_fun_prod _ fun j _ ↦ by
    split_ifs
    · exact analyticAt_const
    · exact (hproj j a).fun_pow _
  have hPca : Pc a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ by
    split_ifs with h
    · exact one_ne_zero
    · exact pow_ne_zero _ h
  have hG'ψ : AnalyticAt ℝ (G' ∘ ψ) a := by
    rw [← hψa] at hG'
    exact hG'.comp hψan
  refine ⟨fun u ↦ (Pc u)⁻¹ • G' (ψ u), (hPcan.inv hPca).smul hG'ψ, ?_⟩
  have h1 : ∀ᶠ u in 𝓝 a, A (φ (ψ u)) = (∏ j, ψ u j ^ k' j) • G' (ψ u) := by
    have : Tendsto ψ (𝓝 a) (𝓝 0) := by
      rw [← hψa]
      exact hψan.continuousAt
    exact this.eventually hAG'
  have h2 : ∀ᶠ u in 𝓝 a, Pc u ≠ 0 := hPcan.continuousAt.eventually_ne hPca
  filter_upwards [h1, h2] with u hu hPu
  rw [hφψ] at hu
  rw [hu, smul_smul]
  congr 1
  rw [eq_comm, mul_inv_eq_iff_eq_mul₀ hPu, hPc, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [hψ, hk', hσ]
  by_cases h0 : a j = 0
  · simp [h0, hb.ne]
  · simp [h0]

end SingularLearningTheory.AnalyticDivision
