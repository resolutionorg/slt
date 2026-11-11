/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.AtlasDataExists
public import SLT.StandardForm.FundamentalConditionI
public import SLT.Resolution.Atlas

/-!
# A nondegenerate resolution atlas from Hironaka's theorem

The end of the construction: from Hironaka's theorem (`exists_resolution_of_isConnected`,
derived from the hironaka package), fundamental condition II, and the standing hypotheses on `K`
and `W`, the resolution atlas the free energy theorems consume exists, with analytic chart maps
and Lipschitz weights, and is nondegenerate.

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 3.3.1], in the atlas form | |
| | `exists_nondegenerateResolutionAtlas`, `exists_nondegenerateResolutionAtlas_of_analytic` |

## The hypotheses

- `hW`, `II`, `hU`, `hWU`, `hKa`, `hK` — `W` compact, fundamental condition II, `K` analytic on
  an open neighbourhood `U` of `W` and nonnegative on `W`; these are [Hit26]'s standing
  hypotheses on `W` and on `K` (`K` is the Kullback–Leibler divergence, nonnegative, and analytic
  by fundamental condition I).
- `hw₀`, `hK₀` — `K` has a zero on `W` (this does not require statistical realisability).
- `hKg`, `hφg` — the germs of `K` and `φ` at every point of `W₀ = W ∩ {K = 0}` are nonzero. The
  thesis assumes this silently: its resolution theorem is applied to `K φ₂ ∏ H_i`, which must be a
  nonzero germ, and its atlas has `K ∘ g_α = u^{2k}` with some `k_j > 0`, which fails where `K`
  vanishes identically. Both are automatic when `W₀` has empty interior in `W` and `φ > 0` near
  `W₀`, the situation of every example in [Hit26].
- `hvol` — the prior gives positive mass to every neighbourhood `{K < ε}` of `W₀` in `W`. Without
  it the atlas can be empty (all of `W₀` could sit where `φ = 0`); [Hit26] needs it too, since
  otherwise the state density vanishes near `0` and the free energy has no `λ log n` term.

**Deviation from the source:** `hKg`, `hφg` and `hvol` are explicit; [Hit26] does not state
them.
-/

public section

namespace SingularLearningTheory

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {d : ℕ}

/-- [Hit26, Theorem 3.3.1] in the atlas form the free
energy theorems consume (`ResolutionAtlas`, `NondegenerateResolutionAtlas`), derived from
Hironaka's theorem for one function: a finite nonempty family of monomialising charts with
analytic chart maps and C¹ weights, one of whose essential charts carries positive trace
mass. Hypotheses: module docstring. -/
theorem exists_nondegenerateResolutionAtlas {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hW : IsCompact W) (II : FundamentalConditionII φ W) {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hWU : W ⊆ U)
    (hKa : AnalyticOnNhd ℝ K U) (hK : ∀ w ∈ W, 0 ≤ K w) {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W)
    (hK₀ : K w₀ = 0) (hKg : ∀ w ∈ W, K w = 0 → ¬ (K =ᶠ[𝓝 w] 0))
    (hφg : ∀ w ∈ W, K w = 0 → ¬ (φ =ᶠ[𝓝 w] 0))
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)) :
    Nonempty (NondegenerateResolutionAtlas K φ W) := by
  obtain ⟨A⟩ := exists_atlasData hW II hU hWU hKa hK hw₀ hK₀ hKg hφg
  haveI := A.nonempty_ι hvol
  exact ⟨A.toNondegenerateResolutionAtlas⟩

/-- `exists_nondegenerateResolutionAtlas` for the deterministic setting of [Hit26,
Section 3.3.1]: `W` compact and semianalytic,
`K` and `φ` real analytic on an open neighbourhood of `W`, `K ≥ 0` and `φ ≥ 0` on `W` (fundamental
condition II with `φ₁ = 1`, `φ₂ = φ`). -/
theorem exists_nondegenerateResolutionAtlas_of_analytic {K φ : (Fin d → ℝ) → ℝ}
    {W : Set (Fin d → ℝ)} (hW : IsCompact W) (hWs : Semianalytic W)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hWU : W ⊆ U) (hKa : AnalyticOnNhd ℝ K U)
    (hK : ∀ w ∈ W, 0 ≤ K w) (hφa : AnalyticOnNhd ℝ φ U) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hK₀ : K w₀ = 0)
    (hKg : ∀ w ∈ W, K w = 0 → ¬ (K =ᶠ[𝓝 w] 0)) (hφg : ∀ w ∈ W, K w = 0 → ¬ (φ =ᶠ[𝓝 w] 0))
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)) :
    Nonempty (NondegenerateResolutionAtlas K φ W) := by
  obtain ⟨A⟩ := exists_atlasData_of_factor hW hWs hU hWU hKa hK hw₀ hK₀ hKg hφg hU hWU
    (φ₁ := fun _ ↦ 1) (fun _ _ ↦ one_pos) contDiffOn_const hφ hφa (fun w _ ↦ (one_mul (φ w)).symm)
  haveI := A.nonempty_ι hvol
  exact ⟨A.toNondegenerateResolutionAtlas⟩

end SingularLearningTheory
