/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import SLT.Resolution.Components

/-!
# Finitely many resolutions covering `W₀`

Step 1 of the plan in [Hit26, Section 3.3.1]:
a resolution of `F = K φ₂ ∏ H_i` centred at each point of the compact `W₀ = {K = 0} ∩ W`, a
finite subfamily whose open sets `U_σ` cover `W₀`, and ([Hit26]'s "shrinking `V_σ` as
necessary") open `E_σ` with `closure E_σ ⋐ U_σ` still covering `W₀`.

| Thesis | Lean |
| --- | --- |
| remark after [Hit26, Theorem 3.3.1] (translation) | |
| | `Resolution.translate` |
| [Hit26, Section 3.3.1], plan, step 1 | |
| | `ResolutionCover`, `exists_resolutionCover` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped Manifold ContDiff

variable {d : ℕ}

/-- A resolution map followed by a translation is a local analytic diffeomorphism over
`{F ≠ 0}`. Supports `Resolution.translate`. -/
theorem Resolution.isLocalDiffeomorphOn_add {F : (Fin d → ℝ) → ℝ} (R : Resolution F)
    (w₀ : Fin d → ℝ) :
    IsLocalDiffeomorphOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω (fun P ↦ R.π P + w₀)
      (R.π ⁻¹' {w | F w ≠ 0}) := by
  let T : Diffeomorph 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) (Fin d → ℝ) (Fin d → ℝ) ω :=
    { Equiv.addRight w₀ with
      contMDiff_toFun := contMDiff_iff_contDiff.mpr (contDiff_id.add contDiff_const)
      contMDiff_invFun := contMDiff_iff_contDiff.mpr (contDiff_id.add contDiff_const) }
  exact fun P ↦ (R.isLocalDiffeomorphOn P).comp _ _ (T.isLocalDiffeomorph _)

/-- Translating a resolution: if `π : M → U` resolves `F`, then `π + w₀ : M → U + w₀` resolves
`w ↦ F (w - w₀)`. -/
@[expose] protected def Resolution.translate {F : (Fin d → ℝ) → ℝ} (R : Resolution F)
    (w₀ : Fin d → ℝ) : Resolution (fun w ↦ F (w - w₀)) where
  U := (fun w ↦ w + w₀) '' R.U
  isOpen_U := (Homeomorph.addRight w₀).isOpen_image.mpr R.isOpen_U
  M := R.M
  π P := R.π P + w₀
  analytic_π := R.analytic_π.add contMDiff_const
  range_π := by rw [← R.range_π, ← range_comp]; rfl
  proper C hC hCc := by
    have : (fun P ↦ R.π P + w₀) ⁻¹' C = R.π ⁻¹' ((fun w ↦ w - w₀) '' C) := by
      ext P
      simp only [mem_preimage, mem_image]
      exact ⟨fun h ↦ ⟨R.π P + w₀, h, add_sub_cancel_right _ _⟩,
        fun ⟨v, hv, hvP⟩ ↦ by rw [← hvP, sub_add_cancel]; exact hv⟩
    rw [this]
    refine R.proper _ ?_ (hCc.image (continuous_id.sub continuous_const))
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hC hv
    simpa [add_sub_cancel_right] using hu
  isLocalDiffeomorphOn := by
    have h : (fun P ↦ R.π P + w₀) ⁻¹' {w | F (w - w₀) ≠ 0} = R.π ⁻¹' {w | F w ≠ 0} := by
      ext P; simp [add_sub_cancel_right]
    rw [h]
    exact R.isLocalDiffeomorphOn_add w₀
  bijOn := by
    have h : (fun P ↦ R.π P + w₀) ⁻¹' {w | F (w - w₀) ≠ 0} = R.π ⁻¹' {w | F w ≠ 0} := by
      ext P; simp [add_sub_cancel_right]
    have hZ' : (fun w ↦ w + w₀) '' R.U \ {w | F (w - w₀) = 0} =
        (fun w ↦ w + w₀) '' (R.U \ {w | F w = 0}) := by
      rw [image_sdiff (add_left_injective w₀)]
      congr 1
      ext w
      simp only [mem_ofPred_eq, mem_image]
      exact ⟨fun h ↦ ⟨w - w₀, h, sub_add_cancel w w₀⟩,
        fun ⟨v, hv, hvw⟩ ↦ by rw [← hvw, add_sub_cancel_right]; exact hv⟩
    rw [h, hZ']
    exact ((add_left_injective w₀).injOn.bijOn_image).comp R.bijOn
  chart P hP := by
    obtain ⟨e, he, hPe, heP, S, k, h, b, hS, hFg, hb, hb0, hdet⟩ := R.chart P (by simpa using hP)
    refine ⟨e, he, hPe, heP, S, k, h, b, hS, ?_, hb, hb0, ?_⟩
    · intro u hu
      simpa [add_sub_cancel_right] using hFg u hu
    · intro u hu
      have : (fun P ↦ R.π P + w₀) ∘ e.symm = fun u ↦ (R.π ∘ e.symm) u + w₀ := rfl
      rw [this, fderiv_add_const]
      exact hdet u hu

/-- Finitely many resolutions of `F` over open subsets `U σ` of `U`, with relatively compact
open `E σ ⋐ U σ` covering `W₀`. -/
structure ResolutionCover (F : (Fin d → ℝ) → ℝ) (U W₀ : Set (Fin d → ℝ)) where
  /-- The finite, nonempty index type of the resolutions. -/
  ι : Type
  [fintype : Fintype ι]
  [nonempty : Nonempty ι]
  /-- The resolutions. -/
  resolution : ι → Resolution F
  U_subset : ∀ σ, (resolution σ).U ⊆ U
  /-- The open set $E_\sigma$, with compact closure inside $U_\sigma$. The sets $E_\sigma$ cover
  $W_0$. -/
  E : ι → Set (Fin d → ℝ)
  E_open : ∀ σ, IsOpen (E σ)
  closure_E_subset : ∀ σ, closure (E σ) ⊆ (resolution σ).U
  closure_E_compact : ∀ σ, IsCompact (closure (E σ))
  cover : W₀ ⊆ ⋃ σ, E σ

attribute [instance] ResolutionCover.fintype ResolutionCover.nonempty

/-- [Hit26, Section 3.3.1], step 1 of the
plan: for `F` analytic on an open `U` containing the compact nonempty `W₀ ⊆ {F = 0}`, with
nonzero germ at every point of `W₀`, Hironaka's theorem (`exists_resolution_of_isConnected`,
applied on a ball about each point) gives a finite cover of `W₀` by resolutions. -/
theorem exists_resolutionCover {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U) {W₀ : Set (Fin d → ℝ)}
    (hW₀ : IsCompact W₀) (hW₀U : W₀ ⊆ U)
    (hgerm : ∀ w ∈ W₀, ¬ (F =ᶠ[𝓝 w] 0)) (hne : W₀.Nonempty) :
    Nonempty (ResolutionCover F U W₀) := by
  have key : ∀ w : W₀, ∃ (R : Resolution F) (E : Set (Fin d → ℝ)),
      R.U ⊆ U ∧ IsOpen E ∧ closure E ⊆ R.U ∧ IsCompact (closure E) ∧ (w : Fin d → ℝ) ∈ E := by
    rintro ⟨w, hw⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU w (hW₀U hw)
    have hFne : ∃ x ∈ Metric.ball w r, F x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hgerm w hw (Filter.eventually_of_mem (Metric.ball_mem_nhds w hr) hcon)
    obtain ⟨R, hRU⟩ := exists_resolution_of_isConnected Metric.isOpen_ball
      ⟨Metric.nonempty_ball.mpr hr, (convex_ball w r).isPreconnected⟩ (hF.mono hrU) hFne
    refine ⟨R, Metric.ball w (r / 2), hRU ▸ hrU, Metric.isOpen_ball, ?_, ?_,
      Metric.mem_ball_self (half_pos hr)⟩
    · rw [hRU]
      exact Metric.closure_ball_subset_closedBall.trans
        (Metric.closedBall_subset_ball (half_lt_self hr))
    · exact (isCompact_closedBall w _).of_isClosed_subset isClosed_closure
        Metric.closure_ball_subset_closedBall
  choose R E hRU hEo hEV hEc hwE using key
  have hcov : W₀ ⊆ ⋃ w : W₀, E w := fun w hw ↦ mem_iUnion.mpr ⟨⟨w, hw⟩, hwE ⟨w, hw⟩⟩
  obtain ⟨t, ht⟩ := hW₀.elim_finite_subcover E hEo hcov
  obtain ⟨w₁, hw₁⟩ := hne
  obtain ⟨σ₁, hσ₁t, -⟩ := mem_iUnion₂.mp (ht hw₁)
  refine ⟨{ ι := {w : W₀ // w ∈ t}
            fintype := inferInstance
            nonempty := ⟨⟨σ₁, hσ₁t⟩⟩
            resolution := fun σ ↦ R σ.1
            U_subset := fun σ ↦ hRU σ.1
            E := fun σ ↦ E σ.1
            E_open := fun σ ↦ hEo σ.1
            closure_E_subset := fun σ ↦ hEV σ.1
            closure_E_compact := fun σ ↦ hEc σ.1
            cover := ?_ }⟩
  intro w hw
  obtain ⟨σ, hσt, hσ⟩ := mem_iUnion₂.mp (ht hw)
  exact mem_iUnion.mpr ⟨⟨σ, hσt⟩, hσ⟩

end SingularLearningTheory
