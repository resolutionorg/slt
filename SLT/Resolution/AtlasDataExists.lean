/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Assembly
import SLT.Resolution.Outer
import SLT.Geometry.Manifold.Cutoff
import SLT.Resolution.Factorisation
public import SLT.StandardForm.FundamentalConditionI
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The choices of the construction

[Hit26, Section 3.3.1], steps 1–3 of the plan
and the two partitions of unity, packaged as `AtlasData`: from Hironaka's theorem
(`exists_resolution_of_isConnected`), fundamental condition II, `K` analytic and nonnegative near
the compact `W` with a zero on `W`, and nonzero germs of `K` and `φ` at every point of `W₀`.

| Thesis | Lean |
| --- | --- |
| [Hit26, Section 3.3.1], steps 1–3 | |
| | `exists_atlasData_of_factor`, `exists_atlasData` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {d : ℕ}

/-- [Hit26, Section 3.3.1]: the choices of the
construction, from Hironaka's theorem, for `W` semianalytic and a prior `φ = φ₁ φ₂` on an open
`U₂ ⊇ W` with `φ₁ > 0` smooth and `φ₂` analytic, nonnegative on `W` (the data of fundamental
condition II, with nonnegativity of `φ₂` asked on `W` only). -/
theorem exists_atlasData_of_factor {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (hW : IsCompact W) (hWs : Semianalytic W)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hWU : W ⊆ U) (hKa : AnalyticOnNhd ℝ K U)
    (hK : ∀ w ∈ W, 0 ≤ K w) {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hK₀ : K w₀ = 0)
    (hKg : ∀ w ∈ W, K w = 0 → ¬ (K =ᶠ[𝓝 w] 0)) (hφg : ∀ w ∈ W, K w = 0 → ¬ (φ =ᶠ[𝓝 w] 0))
    {U₂ : Set (Fin d → ℝ)} (hU₂ : IsOpen U₂) (hWU₂ : W ⊆ U₂) {φ₁ φ₂ : (Fin d → ℝ) → ℝ}
    (hφ₁ : ∀ w ∈ U₂, 0 < φ₁ w) (hφ₁s : ContDiffOn ℝ (⊤ : ℕ∞) φ₁ U₂) (hφ₂ : ∀ w ∈ W, 0 ≤ φ₂ w)
    (hφ₂a : AnalyticOnNhd ℝ φ₂ U₂) (hφ : ∀ w ∈ U₂, φ w = φ₁ w * φ₂ w) :
    Nonempty (AtlasData K φ W) := by
  classical
  obtain ⟨U₀, N, H₀, hU₀, hWU₀, hH₀, hW_eq⟩ := hWs
  obtain ⟨H, hHa₀, hHg₀, hHW⟩ := exists_normalized_semianalytic hU₀ hH₀
  have hWH₀ : ∀ w ∈ U₀, (w ∈ W ↔ ∀ i, 0 ≤ H i w) := fun w hw ↦ (hW_eq w hw).trans (hHW w hw)
  -- The common open neighbourhood and the function to resolve.
  set U' := U ∩ U₂ ∩ U₀ with hU'def
  have hU' : IsOpen U' := (hU.inter hU₂).inter hU₀
  have hWU' : W ⊆ U' := fun w hw ↦ ⟨⟨hWU hw, hWU₂ hw⟩, hWU₀ hw⟩
  have hU'U : U' ⊆ U := inter_subset_left.trans inter_subset_left
  have hU'U₂ : U' ⊆ U₂ := inter_subset_left.trans inter_subset_right
  have hKa' : AnalyticOnNhd ℝ K U' := hKa.mono hU'U
  have hφ₂a' : AnalyticOnNhd ℝ φ₂ U' := hφ₂a.mono hU'U₂
  have hHa : ∀ i, AnalyticOnNhd ℝ (H i) U' := fun i ↦ (hHa₀ i).mono inter_subset_right
  have hHg : ∀ i, ∀ w ∈ U', ¬ (H i =ᶠ[𝓝 w] 0) := fun i w hw ↦ hHg₀ i w hw.2
  have hWH : ∀ w ∈ U', (w ∈ W ↔ ∀ i, 0 ≤ H i w) := fun w hw ↦ hWH₀ w hw.2
  have hHprod : ∀ w ∈ U', AnalyticAt ℝ (fun w ↦ ∏ i, H i w) w := fun w hw ↦
    Finset.analyticAt_fun_prod _ fun i _ ↦ hHa i w hw
  have hFa : AnalyticOnNhd ℝ (fun w ↦ K w * φ₂ w * ∏ i, H i w) U' := fun w hw ↦
    ((hKa' w hw).mul (hφ₂a' w hw)).mul (hHprod w hw)
  -- The zero set `W₀`.
  set W₀ : Set (Fin d → ℝ) := {w | w ∈ W ∧ K w = 0} with hW₀def
  have hKc : ContinuousOn K W := hKa.continuousOn.mono hWU
  have hW₀c : IsCompact W₀ := by
    have : W₀ = W ∩ K ⁻¹' {0} := by
      ext w
      simp [W₀]
    rw [this]
    exact hW.of_isClosed_subset
      (hKc.preimage_isClosed_of_isClosed hW.isClosed isClosed_singleton) inter_subset_left
  have hW₀U' : W₀ ⊆ U' := fun w hw ↦ hWU' hw.1
  have hgerm : ∀ w ∈ W₀, ¬ ((fun w ↦ K w * φ₂ w * ∏ i, H i w) =ᶠ[𝓝 w] 0) := by
    intro w hw hF
    have hKw : AnalyticAt ℝ K w := hKa w (hWU hw.1)
    have hφw : AnalyticAt ℝ φ₂ w := hφ₂a w (hWU₂ hw.1)
    rcases (hKw.mul hφw).eventuallyEq_zero_or_of_mul (hHprod w (hW₀U' hw)) hF with h | h
    · rcases hKw.eventuallyEq_zero_or_of_mul hφw h with h | h
      · exact hKg w hw.1 hw.2 h
      · exact not_eventuallyEq_zero_of_mul hU₂ (hWU₂ hw.1) hφ (hφg w hw.1 hw.2) h
    · obtain ⟨i, -, hi⟩ :=
        Finset.eventuallyEq_zero_of_prod Finset.univ (fun i _ ↦ hHa i w (hW₀U' hw)) h
      exact hHg i w (hW₀U' hw) hi
  -- The cover by resolutions.
  obtain ⟨RC⟩ :=
    exists_resolutionCover hU' hFa hW₀c hW₀U' hgerm ⟨w₀, hw₀, hK₀⟩
  -- The chart covers of the fibres over `T σ = W₀ ∩ closure (E σ)`.
  have hT : ∀ σ, IsCompact (W₀ ∩ closure (RC.E σ)) := fun σ ↦
    hW₀c.inter_right isClosed_closure
  have hTV : ∀ σ, W₀ ∩ closure (RC.E σ) ⊆ (RC.resolution σ).U := fun σ w hw ↦
    RC.closure_E_subset σ hw.2
  have hVU : ∀ σ, (RC.resolution σ).U ⊆ U' := RC.U_subset
  have hC : ∀ σ, Nonempty (ChartCover K φ₂ H (RC.resolution σ).π (W₀ ∩ closure (RC.E σ))) := fun σ ↦
    (RC.resolution σ).exists_chartCover (fun _ _ ↦ rfl) (hKa'.mono (hVU σ))
      (hφ₂a'.mono (hVU σ)) (fun i ↦ (hHa i).mono (hVU σ)) (hT σ) (hTV σ)
      fun w hw ↦ hw.1.2
  obtain ⟨C⟩ :
      Nonempty ((σ : RC.ι) → ChartCover K φ₂ H (RC.resolution σ).π (W₀ ∩ closure (RC.E σ))) :=
    ⟨fun σ ↦ Classical.choice (hC σ)⟩
  -- The compact base sets `Bcl σ = closure (B σ)` inside the saturated open sets.
  have hAo : ∀ σ, IsOpen ((C σ).saturated ((RC.resolution σ).U)) := fun σ ↦
    (C σ).isOpen_saturated
  have hTA : ∀ σ, W₀ ∩ closure (RC.E σ) ⊆ (C σ).saturated ((RC.resolution σ).U) := fun σ ↦
    (C σ).subset_saturated (hTV σ) (C σ).cover
  have hB : ∀ σ, ∃ B : Set (Fin d → ℝ), IsOpen B ∧ W₀ ∩ closure (RC.E σ) ⊆ B ∧
      closure B ⊆ (C σ).saturated ((RC.resolution σ).U) ∧ IsCompact (closure B) := fun σ ↦
    exists_open_between_and_isCompact_closure (hT σ) (hAo σ) (hTA σ)
  choose B hBo hTB hBA hBc using hB
  have hBV : ∀ σ, closure (B σ) ⊆ (RC.resolution σ).U := fun σ ↦
    (hBA σ).trans ((C σ).saturated_subset _)
  have hBO : ∀ σ, (RC.resolution σ).π ⁻¹' closure (B σ) ⊆ (C σ).smallUnion := fun σ ↦
    (preimage_mono (hBA σ)).trans ((C σ).preimage_saturated_subset _)
  have hPT : ∀ σ i, (RC.resolution σ).π ((C σ).P i) ∈ W₀ ∩ closure (RC.E σ) := fun σ i ↦
    (C σ).P_mem i
  have hPB : ∀ σ i, (RC.resolution σ).π ((C σ).P i) ∈ closure (B σ) := fun σ i ↦
    subset_closure (hTB σ (hPT σ i))
  -- The inner partitions of unity.
  have hρ : ∀ σ, Nonempty (ChartCover.InnerPartition (C σ) (closure (B σ))) := fun σ ↦
    (C σ).exists_innerPartition (hBc σ) (hBV σ) (hBO σ) (hPB σ)
  obtain ⟨ρ⟩ : Nonempty ((σ : RC.ι) → ChartCover.InnerPartition (C σ) (closure (B σ))) :=
    ⟨fun σ ↦ Classical.choice (hρ σ)⟩
  -- The threshold and the outer partition of unity.
  have hW₀Bu : ∀ w ∈ W, K w = 0 → w ∈ ⋃ σ, B σ := by
    intro w hw hK0
    obtain ⟨σ, hσ⟩ := mem_iUnion.mp (RC.cover ⟨hw, hK0⟩)
    exact mem_iUnion.mpr ⟨σ, hTB σ ⟨⟨hw, hK0⟩, subset_closure hσ⟩⟩
  obtain ⟨δ, hδ, hδB⟩ := IsCompact.exists_delta hW hKc hK (isOpen_iUnion hBo) hW₀Bu
  have hTδ : IsCompact {w | w ∈ W ∧ K w ≤ δ} := by
    have : {w | w ∈ W ∧ K w ≤ δ} = W ∩ K ⁻¹' Iic δ := by
      ext w
      simp
    rw [this]
    exact hW.of_isClosed_subset
      (hKc.preimage_isClosed_of_isClosed hW.isClosed isClosed_Iic) inter_subset_left
  obtain ⟨ρO, hρOs, hρOnn, hρOsupp, hsum1, hsumle, hρOpos⟩ :=
    exists_smooth_partition hBo hTδ fun w hw ↦ hδB w hw.1 hw.2
  refine ⟨⟨hW, U', hU', hWU', N, H, hHa, hWH, hKa', hK, φ₁, φ₂, fun w hw ↦ hφ₁ w (hU'U₂ hw),
    hφ₁s.mono hU'U₂, hφ₂, hφ₂a', fun w hw ↦ hφ w (hU'U₂ hw), RC, C,
    fun σ ↦ closure (B σ), hBc, hBV, hBO, ρ, ρO, hρOs, hρOnn,
    fun σ w h ↦ subset_closure (hρOsupp σ w h), fun σ i ↦ ?_, δ, hδ,
    fun w hw hK ↦ hsum1 w ⟨hw, hK.le⟩, hsumle⟩⟩
  refine hρOpos σ _ ⟨⟨(hPT σ i).1.1, ?_⟩, hTB σ (hPT σ i)⟩
  rw [(hPT σ i).1.2]
  exact hδ.le

/-- [Hit26, Section 3.3.1]: the choices of the
construction, from Hironaka's theorem and fundamental condition II. -/
theorem exists_atlasData {K φ : (Fin d → ℝ) → ℝ}
    {W : Set (Fin d → ℝ)} (hW : IsCompact W) (II : FundamentalConditionII φ W)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hWU : W ⊆ U) (hKa : AnalyticOnNhd ℝ K U)
    (hK : ∀ w ∈ W, 0 ≤ K w) {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hK₀ : K w₀ = 0)
    (hKg : ∀ w ∈ W, K w = 0 → ¬ (K =ᶠ[𝓝 w] 0)) (hφg : ∀ w ∈ W, K w = 0 → ¬ (φ =ᶠ[𝓝 w] 0)) :
    Nonempty (AtlasData K φ W) := by
  obtain ⟨U₂, hU₂, hWU₂, φ₁, φ₂, hφ₁, hφ₁s, hφ₂, hφ₂a, hφ⟩ := II.factor
  exact exists_atlasData_of_factor hW II.semianalytic hU hWU hKa hK hw₀ hK₀ hKg hφg hU₂
    hWU₂ hφ₁ hφ₁s hφ₂ hφ₂a hφ

end SingularLearningTheory
