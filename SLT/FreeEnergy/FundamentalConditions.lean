/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.StochasticAsymptotics
public import SLT.FreeEnergy.AnalyticDivision
public import SLT.StandardForm.FundamentalConditionI
public import SLT.StandardForm.ResolvedLikelihood
public import SLT.EmpiricalProcess.Defs
public import Mathlib.Order.CompletePartialOrder

/-!
# [Wat09, Theorem 6.1] and the empirical process on the resolution

Formalises [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]) in
`L^s(q)`-valued germ form and the construction of the random inputs of
[Hit26, Theorem 5.2.6] from a sample. The standing assumptions (fundamental
conditions I and II) are the structures of `StandardForm/Defs.lean` and `Setting.lean`, and the
samplewise conclusion of [Wat09, Theorem 6.1] is the structure `ResolvedLikelihood` of
`StandardForm/ResolvedLikelihood.lean`.

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]), `L^s(q)`-valued germ | |
| | `ResolutionAtlas.resolution_of_f_germ` |
| [Hit26, Equation (5.0.3)], `K_n` | `empiricalLoss` |
| [Hit26, Equation (5.0.5)], `ψ_n` | `tailProcess` |
| [Hit26, Equation (5.2.2)], `ξ_n` | |
| | `ResolutionAtlas.ResolvedLikelihood.chartProcess` |
| `K_n(g_α(u)) = u^{2k} − n^{-1/2} u^k ξ_n(u)` | |
| | `ResolutionAtlas.ResolvedLikelihood.empiricalLoss_comp_g` |
| [Hit26, Lemma 5.2.4] applied to `nK_n = nK + √n√K ψ_n` | |
| | `ResolutionAtlas.tail_bound_of_tailProcess_le` |
| the random inputs of [Wat09, Theorem 6.7] from a sample | |
| | `ResolutionAtlas.ResolvedLikelihood.toEmpiricalProcessInput` |
| the same from [Hit26]'s statements ([Wat09, Theorem 5.9] for `ξ_n` and `ψ_n`) | |
| | `ResolutionAtlas.ResolvedLikelihood.empiricalProcessInput` |
| `ψ_n` is the empirical process of `f / √K` |
`SingularLearningTheory.tailProcess_eq_empiricalProcess` |
| `ξ_n = −ψ_n` a.s. for the empirical process of `a` on `⊔_α U_α` | |
| | `ResolutionAtlas.ResolvedLikelihood.ae_chartProcess_eq` |
| [Hit26, Lemma 4.2.4] ([Wat09, Theorem 5.8]), conclusion, uniformly in `n` | |
| | `EmpiricalProcessLimit.MomentBound` |
| [Hit26, Theorem 5.2.6], "`∇ξ_n` converges in distribution" (see below) | |
| | `ResolutionAtlas.PrimaryLipschitzTight` |

## [Wat09, Theorem 6.1]

[Hit26, Lemma 5.2.3] asserts, for each chart, a factorisation
`f(x, g_α(u)) = u^{k_α} a_α(x, u)` with `a_α` `L^s(q)`-valued analytic and
`E_q[a_α(·, u)] = u^{k_α}`. Its thesis proof is defective and its statement is only true in
`L^s(q)` with a common null set.

The `L^s(q)`-valued statement is proved here as a germ at the origin of a chart
(`resolution_of_f_germ`): from `L^s(q)`-valued real analyticity of `f` on a neighbourhood of `W`
(item 2 of fundamental condition I), `s ≥ 2`, relatively finite variance and the chart map
analytic at `0`, there is `G` analytic at `0` with `F(g_α u) = u^{k_α} • G u` and
`∫ G u dq = u^{k_α}` near `0`. The analytic core is `AnalyticAt.analyticAt_factor_monomial_of_bound`
(`AnalyticDivision.lean`), applied with the inclusion `L^s(q) → L²(q)` as the detecting map, since
relatively finite variance only bounds the `L²` norm.

The conclusion in the form the empirical process needs — measurable `C(U_α, ℝ)`-valued
representatives `x ↦ a_α(x, ·)`, the factorisation for `q`-almost every `x` simultaneously for all
`u`, and the mean identity — is the structure `ResolvedLikelihood`; the passage from the
`L^s(q)`-valued germ to such representatives (and from the germ at `0` to the whole cube) is
`FreeEnergy/LocalQuotient.lean` and `FreeEnergy/SamplewiseResolution.lean`.

## From a sample to `EmpiricalProcessInput`

Given a resolved likelihood and an identically distributed sample `X_i ∼ q`, `K_n` and `ξ_n` are
defined as in [Hit26] and the two algebraic fields of `EmpiricalProcessInput`
(`chart_identity`, `tail_bound`) are proved (`toEmpiricalProcessInput`). The
empirical-process facts are then derived from [Hit26]'s own statements
(`empiricalProcessInput`): [Hit26, Theorem 4.2.9] for the chart process on
the resolution `M = ⊔_α U_α` gives `tendsto` (with `ξ_n = −ψ_n`), the same theorem for `ψ_n`
on the compact `{K ≥ δ}` gives the tail control `B_n = sup_{K ≥ δ} |ψ_n|` and its boundedness
in probability, and the Lipschitz tightness in the primary coordinates is the predicate
`PrimaryLipschitzTight` below (derived in `FreeEnergy/Discharge.lean`). Independence of the
sample is not used.

## Deviation from the source: Lipschitz tightness in the primary coordinates

The proof of [Hit26, Theorem 5.2.6] applies [Wat09, Theorem 4.9] to the chart process
`ξ_n`, which needs a bound on `‖∇ξ_n‖`, and justifies it with "`ξ_n` and `∇ξ_n` converge in
distribution". The empirical-process chapter proves convergence in distribution of `ξ_n` in
`C(U_α, ℝ)` and the modulus bound `E[sup_{‖u−u'‖≤δ} |ξ_n(u) − ξ_n(u')|^s] ≤ B δ^s`
([Hit26, Lemma 4.2.8]); neither gives a Lipschitz bound,
and nothing is proved about `∇ξ_n`. What the formal proof of [Wat09, Theorem 6.7] uses is that the
Lipschitz constants of `ξ_n` in the
*primary* coordinates, relative to the face `u_P = 0`, are bounded in probability
(`ResolutionAtlas.PrimaryLipschitzTight`); `FreeEnergy/Discharge.lean` derives it from the
local `L²(q)`-expansions of `a_α`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory

variable {d : ℕ}

variable {X : Type*} [MeasurableSpace X]

/-! ### Continuous linear maps on `L^s(q)` -/

section Lp

variable {p₁ p₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] (q : Measure X) [IsProbabilityMeasure q]

/-- The inclusion `L^{p₂}(q) → L^{p₁}(q)`, `p₁ ≤ p₂`, on a probability space; a contraction. -/
@[expose] noncomputable def _root_.MeasureTheory.lpInclusion
    (hp : p₁ ≤ p₂) : Lp ℝ p₂ q →L[ℝ] Lp ℝ p₁ q :=
  LinearMap.mkContinuous
    { toFun := fun g ↦ ((Lp.memLp g).mono_exponent hp).toLp g
      map_add' := fun g₁ g₂ ↦ by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_add g₁ g₂)
      map_smul' := fun c g ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_smul c g) }
    1 fun g ↦ by
      rw [one_mul]
      change ‖((Lp.memLp g).mono_exponent hp).toLp g‖ ≤ ‖g‖
      rw [Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g)
        (eLpNorm_le_eLpNorm_of_exponent_le hp)

theorem _root_.MeasureTheory.coeFn_lpInclusion (hp : p₁ ≤ p₂) (g : Lp ℝ p₂ q) :
    (lpInclusion q hp g : X → ℝ) =ᵐ[q] g :=
  MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent hp)

theorem _root_.MeasureTheory.lpInclusion_injective (hp : p₁ ≤ p₂) : Function.Injective
    (lpInclusion q hp) := by
  intro g₁ g₂ h
  refine Lp.ext ((coeFn_lpInclusion q hp g₁).symm.trans (.trans ?_ (coeFn_lpInclusion q hp g₂)))
  rw [h]

/-- Integration `L^{p}(q) → ℝ` as a continuous linear map. -/
@[expose] noncomputable def _root_.MeasureTheory.lpIntegral : Lp ℝ p₂ q →L[ℝ] ℝ :=
  L1.integralCLM.comp (lpInclusion q (Fact.out : 1 ≤ p₂))

theorem _root_.MeasureTheory.lpIntegral_apply (g : Lp ℝ p₂ q) : lpIntegral q g = ∫ x, g x ∂q := by
  calc lpIntegral q g = L1.integralCLM (lpInclusion q (Fact.out : 1 ≤ p₂) g) := rfl
    _ = L1.integral (lpInclusion q (Fact.out : 1 ≤ p₂) g) := (L1.integral_eq _).symm
    _ = ∫ x, (lpInclusion q (Fact.out : 1 ≤ p₂) g) x ∂q := L1.integral_eq_integral _
    _ = ∫ x, g x ∂q := integral_congr_ae (coeFn_lpInclusion q _ g)

/-- `‖g‖_{L²} = (∫ g²)^{1/2}` for an `L²` element, from a representative. -/
theorem _root_.MeasureTheory.norm_lpInclusion_two (hp : (2 : ℝ≥0∞) ≤ p₂) (g : Lp ℝ p₂ q) {h : X → ℝ}
    (hg : (g : X → ℝ) =ᵐ[q] h) :
    ‖lpInclusion q hp g‖ = (∫ x, h x ^ 2 ∂q) ^ (1 / 2 : ℝ) := by
  have hmem : MemLp (lpInclusion q hp g : X → ℝ) 2 q := Lp.memLp _
  rw [Lp.norm_def, hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (by positivity)]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [(coeFn_lpInclusion q hp g).trans hg] with x hx
    rw [hx, ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  · simp

end Lp

/-- `K_n(w) = (1/n) Σ_{i<n} f(X_i, w)`, [Hit26, Equation (5.0.3)]. -/
@[expose] noncomputable def empiricalLoss {Ω : Type*} (f : X → (Fin d → ℝ) → ℝ) (Xs : ℕ → Ω → X)
    (n : ℕ)
    (ω : Ω) (w : Fin d → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, f (Xs i ω) w) / n

/-- `ψ_n(w) = n^{-1/2} Σ_{i<n} (f(X_i, w) − K(w)) / √K(w)`, [Hit26,
Equation (5.0.5)]. -/
@[expose] noncomputable def tailProcess {Ω : Type*} (K : (Fin d → ℝ) → ℝ) (f : X → (Fin d → ℝ) → ℝ)
    (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) (w : Fin d → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, (f (Xs i ω) w - K w)) / (Real.sqrt n * Real.sqrt (K w))

theorem measurable_uncurry_empiricalLoss {Ω : Type*} [MeasurableSpace Ω]
    {f : X → (Fin d → ℝ) → ℝ} (hf : Measurable (Function.uncurry f)) {Xs : ℕ → Ω → X}
    (hX : ∀ i, Measurable (Xs i)) (n : ℕ) :
    Measurable (Function.uncurry (empiricalLoss f Xs n)) := by
  refine (Finset.measurable_sum _ fun i _ ↦ ?_).div_const _
  exact hf.comp ((hX i).prodMap measurable_id)

namespace ResolutionAtlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]),
`L^s(q)`-valued, as a germ at the origin of a chart: for `f` `L^s(q)`-valued real analytic on a
neighbourhood `U ⊇ W` (represented by `F`), `s ≥ 2`, relatively finite variance
(`∫ f(x, w)² dq ≤ C⁻¹ K(w)`, [Hit26, Definition 2.3.3]) and analyticity of the chart map at
`0`, there is `G` analytic at `0` with `F(g_α u) = u^{k_α} • G u` and `∫ G u dq = u^{k_α}` near
`0`. The detecting map is the inclusion `L^s(q) → L²(q)` (the bound is an `L²` bound); the mean
identity follows from `K ∘ g_α = u^{2k_α}` by the identity theorem twice. -/
theorem resolution_of_f_germ {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} [IsProbabilityMeasure q]
    {f : X → (Fin d → ℝ) → ℝ} (hs : 2 ≤ s) (hK : ∀ w, K w = ∫ x, f x w ∂q)
    {U : Set (Fin d → ℝ)} (hWU : W ⊆ U) {F : (Fin d → ℝ) → Lp ℝ s q} (hF : AnalyticOnNhd ℝ F U)
    (hFf : ∀ w ∈ U, (F w : X → ℝ) =ᵐ[q] fun x ↦ f x w) {C : ℝ} (hC : 0 < C)
    (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w) (α : R.ι) :
    ∃ G : (Fin d → ℝ) → Lp ℝ s q, AnalyticAt ℝ G 0 ∧
      (∀ᶠ u in 𝓝 0, F (R.g α u) = (∏ j, u j ^ R.k α j) • G u) ∧
      ∀ᶠ u in 𝓝 0, ∫ x, G u x ∂q = ∏ j, u j ^ R.k α j := by
  have hb := R.b_pos α
  have hs2 : (2 : ℝ≥0∞) ≤ s := hs
  have hcube : ∀ u ∈ ocube d (R.b α), u ∈ cube d (R.b α) := fun u hu ↦
    mem_cube.2 fun i ↦ ⟨(hu i (Set.mem_univ i)).1.le, (hu i (Set.mem_univ i)).2.le⟩
  have hgU : ∀ u ∈ cube d (R.b α), R.g α u ∈ U := fun u hu ↦ hWU (R.g_mapsTo α hu)
  have h0 : (0 : Fin d → ℝ) ∈ cube d (R.b α) := ⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩
  -- `u ↦ F (g u)` is analytic at `0`
  have hA : AnalyticAt ℝ (fun u ↦ F (R.g α u)) 0 := (hF _ (hgU 0 h0)).comp (R.g_analytic α 0 h0)
  have hproj : ∀ i, AnalyticAt ℝ (fun u : Fin d → ℝ ↦ u i) 0 := fun i ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i).analyticAt 0
  -- the `L²` bound on the positive cube
  set T := lpInclusion q hs2 with hT_def
  have hbound : ∀ u ∈ ocube d (R.b α),
      ‖T (F (R.g α u))‖ ≤ C⁻¹ ^ (1 / 2 : ℝ) * ∏ i, u i ^ R.k α i := by
    intro u hu
    have hu' := hcube u hu
    have hu0 : ∀ i, 0 ≤ u i := fun i ↦ (hu i (Set.mem_univ i)).1.le
    rw [norm_lpInclusion_two q hs2 _ (hFf _ (hgU u hu'))]
    have h1 : ∫ x, f x (R.g α u) ^ 2 ∂q ≤ C⁻¹ * (∏ i, u i ^ R.k α i) ^ 2 := by
      rw [← Finset.prod_pow_two_mul, ← R.monomial α u hu']
      exact hRFV _ (R.g_mapsTo α hu')
    have h2 : 0 ≤ ∏ i, u i ^ R.k α i := Finset.prod_nonneg fun i _ ↦ pow_nonneg (hu0 i) _
    calc (∫ x, f x (R.g α u) ^ 2 ∂q) ^ (1 / 2 : ℝ)
        ≤ (C⁻¹ * (∏ i, u i ^ R.k α i) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (integral_nonneg fun x ↦ sq_nonneg _) h1 (by norm_num)
      _ = C⁻¹ ^ (1 / 2 : ℝ) * ∏ i, u i ^ R.k α i := by
          rw [Real.mul_rpow (by positivity) (sq_nonneg _),
            ← Real.sqrt_eq_rpow ((∏ i, u i ^ R.k α i) ^ 2), Real.sqrt_sq h2]
  obtain ⟨G, hG, hFG⟩ := AnalyticAt.analyticAt_factor_monomial_of_bound T
    (lpInclusion_injective q hs2) _ (R.k α) rfl hA hb hbound
  refine ⟨G, hG, hFG, ?_⟩
  -- the mean identity: `∫ F (g u) = K (g u) = u^{2k}` near `0` by the identity theorem
  have hΦ : ∀ w ∈ U, lpIntegral q (F w) = K w := fun w hw ↦ by
    rw [lpIntegral_apply, hK]
    exact integral_congr_ae (hFf w hw)
  have hK : ∀ᶠ u in 𝓝 0, lpIntegral q (F (R.g α u)) = ∏ i, u i ^ (2 * R.k α i) := by
    have hB : AnalyticAt ℝ (fun u ↦ lpIntegral q (F (R.g α u)) - ∏ i, u i ^ (2 * R.k α i)) 0 :=
      (((lpIntegral q).analyticAt _).comp hA).sub (Finset.analyticAt_fun_prod _ fun i _ ↦
        (hproj i).fun_pow _)
    filter_upwards [AnalyticAt.eventually_eq_zero_of_ocube hB hb fun u hu ↦ by
      rw [hΦ _ (hgU u (hcube u hu)), R.monomial α u (hcube u hu), sub_self]] with u hu
    exact sub_eq_zero.mp hu
  have hGmean : ∀ᶠ u in 𝓝 0, lpIntegral q (G u) = ∏ i, u i ^ R.k α i := by
    have hB : AnalyticAt ℝ (fun u ↦ lpIntegral q (G u) - ∏ i, u i ^ R.k α i) 0 :=
      (((lpIntegral q).analyticAt _).comp hG).sub (Finset.analyticAt_fun_prod _ fun i _ ↦
        (hproj i).fun_pow _)
    obtain ⟨δ, hδ, hFG'⟩ := Metric.eventually_nhds_iff.mp hFG
    obtain ⟨δ', hδ', hK'⟩ := Metric.eventually_nhds_iff.mp hK
    set ε := min (min δ δ') (R.b α) with hε_def
    have hε : 0 < ε := lt_min (lt_min hδ hδ') hb
    have hvanG : ∀ u ∈ ocube _ ε,
        lpIntegral q (G u) - ∏ i, u i ^ R.k α i = 0 := by
      intro u hu
      have hun : ‖u‖ < ε := AnalyticDivision.norm_lt_of_mem_ocube hε hu
      have hu0 : 0 < ∏ i, u i ^ R.k α i :=
        Finset.prod_pos fun i _ ↦ pow_pos (hu i (Set.mem_univ i)).1 _
      have h1 := hFG' (show dist u 0 < δ by
        rw [dist_zero_right]; exact hun.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      have h2 := hK' (show dist u 0 < δ' by
        rw [dist_zero_right]; exact hun.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      rw [h1, map_smul, smul_eq_mul, Finset.prod_pow_two_mul] at h2
      rw [sub_eq_zero]
      exact mul_left_cancel₀ hu0.ne' (by rw [h2]; ring)
    filter_upwards [AnalyticAt.eventually_eq_zero_of_ocube hB hε hvanG]
      with u hu
    exact sub_eq_zero.mp hu
  filter_upwards [hGmean] with u hu
  rw [← lpIntegral_apply, hu]

/-- `u ↦ u^{k_α}` as a continuous function on the chart cube. -/
@[expose] noncomputable def chartMonomial (α : R.ι) : C(cube d (R.b α), ℝ) :=
  ⟨fun u ↦ ∏ j, (u : Fin d → ℝ) j ^ R.k α j,
    continuous_finsetProd _ fun j _ ↦ ((continuous_apply j).comp continuous_subtype_val).pow _⟩

/-- Off the localization, `K ≥ δ`. -/
theorem δ_le_of_χ_lt_one {w : Fin d → ℝ} (hw : w ∈ W) (hχ : R.χ w < 1) : R.δ ≤ K w :=
  not_lt.mp fun h ↦ absurd hχ (by rw [R.χ_eq_one w hw h]; exact lt_irrefl 1)

omit [MeasurableSpace X] in
/-- The tail control of `EmpiricalProcessInput` from a bound on the empirical process `ψ_n`
off the localization: `nK_n = nK + √n √K ψ_n ≥ nK/2 − ψ_n²/2 ≥ nδ/2 − B_n²/2`
([Hit26, Lemma 5.2.4]). -/
theorem tail_bound_of_tailProcess_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X} {B : ℕ → Ω → ℝ}
    (hψ : ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ W, R.χ w < 1 → |tailProcess K f Xs n ω w| ≤ B n ω) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ w ∈ W, R.χ w < 1 →
      n * R.δ / 2 - B n ω ^ 2 / 2 ≤ n * empiricalLoss f Xs n ω w := by
  filter_upwards [hψ n] with ω hω w hw hχ
  have hKδ : R.δ ≤ K w := R.δ_le_of_χ_lt_one hw hχ
  have hKpos : 0 < K w := R.δ_pos.trans_le hKδ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul, zero_div, zero_sub]
    have := sq_nonneg (B 0 ω)
    linarith
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : Real.sqrt n * Real.sqrt (K w) * tailProcess K f Xs n ω w
        = ∑ i ∈ Finset.range n, (f (Xs i ω) w - K w) := by
      rw [tailProcess, mul_comm, div_mul_cancel₀ _ (by positivity)]
    have hid : n * empiricalLoss f Xs n ω w
        = n * K w + Real.sqrt n * Real.sqrt (K w) * tailProcess K f Xs n ω w := by
      rw [hsq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        empiricalLoss, mul_div_cancel₀ _ hn0.ne']
      ring
    have h1 : (Real.sqrt n * Real.sqrt (K w)) ^ 2 = n * K w := by
      rw [mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hKpos.le]
    have hyoung := sq_nonneg (Real.sqrt n * Real.sqrt (K w) + tailProcess K f Xs n ω w)
    have hB := hω w hw hχ
    have hψ2 : tailProcess K f Xs n ω w ^ 2 ≤ B n ω ^ 2 :=
      sq_le_sq' (abs_le.mp hB).1 (abs_le.mp hB).2
    have hnδ : n * R.δ ≤ n * K w := mul_le_mul_of_nonneg_left hKδ hn0.le
    rw [hid]
    nlinarith

namespace ResolvedLikelihood

variable {R} {q : Measure X} {f : X → (Fin d → ℝ) → ℝ} (L : R.ResolvedLikelihood q f)
  {Ω : Type*} [MeasurableSpace Ω] (Xs : ℕ → Ω → X)

/-- The chart processes `ξ_{n,α}(u) = −n^{-1/2} Σ_{i<n} (a_α(X_i, u) − u^{k_α})`, [Hit26,
Equation (5.2.2)], as an element of `∏_α C(U_α, ℝ)`.
-/
@[expose] noncomputable def chartProcess (n : ℕ) (ω : Ω) : R.ChartFunctions := fun α ↦
  (-(Real.sqrt n)⁻¹) • ∑ i ∈ Finset.range n, (L.a α (Xs i ω) - R.chartMonomial α)

theorem measurable_chartProcess (hX : ∀ i, Measurable (Xs i)) (n : ℕ) :
    Measurable (L.chartProcess Xs n) := by
  refine measurable_pi_iff.mpr fun α ↦ ?_
  have h : Measurable fun ω ↦ ∑ i ∈ Finset.range n, (L.a α (Xs i ω) - R.chartMonomial α) :=
    Finset.measurable_sum _ fun i _ ↦ ((L.a_measurable α).comp (hX i)).sub measurable_const
  exact h.const_smul (-(Real.sqrt n)⁻¹ : ℝ)

/-- Thesis: `K_n(g_α(u)) = u^{2k} − n^{-1/2} u^k ξ_n(u)` (with the corrected sign), almost surely
for `n ≥ 1`, from the factorisation of
[Wat09, Theorem 6.1] transported to the sample. -/
theorem empiricalLoss_comp_g {P : Measure Ω} (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) {n : ℕ} (hn : 1 ≤ n) (α : R.ι) :
    ∀ᵐ ω ∂P, ∀ u : cube d (R.b α),
      empiricalLoss f Xs n ω (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
        (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * L.chartProcess Xs n ω α u := by
  have hae : ∀ i ∈ Finset.range n, ∀ᵐ ω ∂P, ∀ u : cube d (R.b α),
      f (Xs i ω) (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * L.a α (Xs i ω) u := by
    intro i _
    refine ae_of_ae_map (hX i).aemeasurable (p := fun x ↦ ∀ u : cube d (R.b α),
      f x (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * L.a α x u) ?_
    rw [hlaw i]
    exact L.factor α
  filter_upwards [(Filter.eventually_all_finset _).mpr hae] with ω hω u
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hs : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  simp only [empiricalLoss, chartProcess, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    ContinuousMap.sub_apply, chartMonomial, ContinuousMap.coe_mk, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i hi ↦ hω i hi u), ← Finset.mul_sum, Finset.prod_pow_two_mul,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linear_combination (-((∏ j, (u : Fin d → ℝ) j ^ R.k α j) *
    ((∑ i ∈ Finset.range n, L.a α (Xs i ω) u) - n * ∏ j, (u : Fin d → ℝ) j ^ R.k α j))) * hs +
    (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 * mul_inv_cancel₀ hn0

/-- The random inputs of [Hit26, Theorem 5.2.6] from an identically
distributed sample `X_i ∼ q` and a resolved likelihood ([Wat09, Theorem 6.1]): `K_n` and `ξ_n` are
the thesis's, `chart_identity` and `tail_bound` are proved, and the empirical-process facts
([Hit26, Theorem 4.2.9] for `ξ_n`, tightness of its primary Lipschitz
constants, and the bound `B_n` on `sup_{K ≥ δ} |ψ_n|`) are hypotheses. -/
@[expose] noncomputable def toEmpiricalProcessInput (β : ℝ) {Ω' : Type*} [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hf : Measurable (Function.uncurry f)) (Ξlim : Ω' → R.ChartFunctions)
    (htendsto : TendstoInDistribution (L.chartProcess Xs) atTop Ξlim (fun _ ↦ P) P')
    (hlip : ∀ η > 0, ∃ L' : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | ¬ ∀ α, ∀ u : cube d (R.b α),
        |L.chartProcess Xs n ω α u - L.chartProcess Xs n ω α (R.primaryZero α u)|
          ≤ L' * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j} ≤ ENNReal.ofReal η)
    (B : ℕ → Ω → ℝ) (hBm : ∀ n, Measurable (B n))
    (hBt : ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, P {ω | M < |B n ω|} ≤ ENNReal.ofReal η)
    (hψ : ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ W, R.χ w < 1 → |tailProcess K f Xs n ω w| ≤ B n ω) :
    R.EmpiricalProcessInput β P P' where
  Kn := empiricalLoss f Xs
  Kn_measurable := measurable_uncurry_empiricalLoss hf hX
  Ξ := L.chartProcess Xs
  Ξ_measurable := L.measurable_chartProcess Xs hX
  chart_identity := fun _ hn α ↦ L.empiricalLoss_comp_g Xs hX hlaw hn α
  Ξlim := Ξlim
  tendsto := htendsto
  lipschitz_tight := hlip
  B := B
  B_measurable := hBm
  B_tight := hBt
  tail_bound := R.tail_bound_of_tailProcess_le hψ

end ResolvedLikelihood

end ResolutionAtlas

/-! ### From [Hit26]'s empirical-process statements to `EmpiricalProcessInput` -/

/-- The sup norm of a continuous function on a compact space is bounded by the supremum of
its values, in `ℝ≥0∞`. No thesis counterpart. -/
theorem _root_.ContinuousMap.enorm_le_iSup_enorm {U : Type*} [TopologicalSpace U]
    [CompactSpace U] (Φ : C(U, ℝ)) : ‖Φ‖ₑ ≤ ⨆ u, ‖Φ u‖ₑ := by
  rcases eq_or_ne (⨆ u, ‖Φ u‖ₑ) ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hM : 0 ≤ (⨆ u, ‖Φ u‖ₑ).toReal := ENNReal.toReal_nonneg
  have hle : ‖Φ‖ ≤ (⨆ u, ‖Φ u‖ₑ).toReal := by
    rw [ContinuousMap.norm_le _ hM]
    intro u
    have := ENNReal.toReal_mono htop (le_iSup (fun u ↦ ‖Φ u‖ₑ) u)
    rwa [toReal_enorm] at this
  calc ‖Φ‖ₑ = ENNReal.ofReal ‖Φ‖ := (ofReal_norm Φ).symm
    _ ≤ ENNReal.ofReal (⨆ u, ‖Φ u‖ₑ).toReal := ENNReal.ofReal_le_ofReal hle
    _ = ⨆ u, ‖Φ u‖ₑ := ENNReal.ofReal_toReal htop

/-- `K` is continuous on the open set `U` of fundamental condition I: `K(w) = ∫ F(w) dq` is a
continuous linear functional of the analytic map `F`. No thesis counterpart. -/
theorem FundamentalConditionI.continuousOn_K {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X}
    [IsProbabilityMeasure q] {f : X → (Fin d → ℝ) → ℝ}
    {K : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (I : FundamentalConditionI s q f K W) :
    ContinuousOn K W := by
  obtain ⟨U, -, hWU, F, hF, hFf⟩ := I.ls_analytic
  have h : ∀ w ∈ U, K w = lpIntegral q (F w) := fun w hw ↦ by
    rw [lpIntegral_apply, I.K_eq]
    exact (integral_congr_ae (hFf w hw)).symm
  exact (((lpIntegral q).continuous.comp_continuousOn hF.continuousOn).congr h).mono hWU

/-! ### The moment bound of [Wat09, Theorem 5.8] and the Lipschitz tightness of the chart process -/

section EmpiricalProcessPredicates

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {U : Type*} [TopologicalSpace U]
  {q : Measure X} {f : X → U → ℝ} {Xs : ℕ → Ω → X} {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- The conclusion of [Hit26, Lemma 4.2.4] ([Wat09, Theorem 5.8]) with index
`s`, uniformly in `n`: `E[sup_u |ψ_n(u)|^s] ≤ C` for all `n`.
The free energy formula's expectation part uses it with `s = 4`
(`EmpiricalProcess/FourthMoment.lean`). -/
@[expose] def EmpiricalProcessLimit.MomentBound (E : EmpiricalProcessLimit q f Xs P P')
    (s : ℕ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, ∫⁻ ω, (⨆ u, ‖E.Ψ n ω u‖ₑ) ^ s ∂P ≤ C

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- **Deviation from the source** (module docstring). The Lipschitz constants of the chart
process `ξ_n` in the primary coordinates are bounded in probability: for every `η > 0` there is
`L` such that, for all large `n`, with probability at least `1 − η`, on every chart `α` and at
every `u ∈ U_α`,
`|ξ_n(u) − ξ_n(0_P, u_{Pᶜ})| ≤ L Σ_{j ∈ P_α} u_j`
(`(0_P, u_{Pᶜ})` is `u` with its primary coordinates set to `0`). [Hit26]'s proof of
[Hit26, Theorem 5.2.6] uses "`∇ξ_n` converges in distribution", which the
empirical-process chapter does not prove. -/
@[expose] def ResolutionAtlas.PrimaryLipschitzTight (Ξ : ℕ → Ω → C((α : R.ι) × cube d (R.b α), ℝ))
    (P : Measure Ω) : Prop :=
  ∀ η > 0, ∃ L : ℝ, ∃ N : ℕ, ∀ n ≥ N,
    P {ω | ¬ ∀ α, ∀ u : cube d (R.b α),
      |Ξ n ω ⟨α, u⟩ - Ξ n ω ⟨α, R.primaryZero α u⟩| ≤ L * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j}
      ≤ ENNReal.ofReal η

end EmpiricalProcessPredicates

namespace ResolutionAtlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- The restriction of a continuous function on the resolution `M = ⊔_α U_α` to the charts. -/
@[expose] noncomputable def toChartFunctions (Φ : C((α : R.ι) × cube d (R.b α),
    ℝ)) : R.ChartFunctions :=
  fun α ↦ Φ.comp (ContinuousMap.sigmaMk (X := fun α : R.ι ↦ ↥(cube d (R.b α))) α)

theorem toChartFunctions_apply (Φ : C((α : R.ι) × cube d (R.b α), ℝ)) (α : R.ι)
    (u : cube d (R.b α)) : R.toChartFunctions Φ α u = Φ ⟨α, u⟩ := rfl

theorem toChartFunctions_neg (Φ : C((α : R.ι) × cube d (R.b α), ℝ)) :
    R.toChartFunctions (-Φ) = -(R.toChartFunctions Φ) :=
  funext fun _ ↦ ContinuousMap.ext fun _ ↦ rfl

theorem continuous_toChartFunctions : Continuous R.toChartFunctions := by
  unfold toChartFunctions
  exact continuous_pi fun α ↦ ContinuousMap.continuous_precomp _

/-- `‖Φ|_charts‖ ≤ sup_{(α, u)} |Φ(α, u)|`. -/
theorem enorm_toChartFunctions_le (Φ : C((α : R.ι) × cube d (R.b α), ℝ)) :
    ‖R.toChartFunctions Φ‖ₑ ≤ ⨆ p, ‖Φ p‖ₑ := by
  rcases eq_or_ne (⨆ p, ‖Φ p‖ₑ) ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hM : 0 ≤ (⨆ p, ‖Φ p‖ₑ).toReal := ENNReal.toReal_nonneg
  have hle : ‖R.toChartFunctions Φ‖ ≤ (⨆ p, ‖Φ p‖ₑ).toReal := by
    rw [pi_norm_le_iff_of_nonneg hM]
    intro α
    rw [ContinuousMap.norm_le _ hM]
    intro u
    have := ENNReal.toReal_mono htop (le_iSup (fun p ↦ ‖Φ p‖ₑ) ⟨α, u⟩)
    rw [toChartFunctions_apply]
    rwa [toReal_enorm] at this
  calc ‖R.toChartFunctions Φ‖ₑ = ENNReal.ofReal ‖R.toChartFunctions Φ‖ :=
        (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (⨆ p, ‖Φ p‖ₑ).toReal := ENNReal.ofReal_le_ofReal hle
    _ = ⨆ p, ‖Φ p‖ₑ := ENNReal.ofReal_toReal htop

/-- [Hit26]'s `ψ_n` ([Hit26, Equation (5.0.5)]) is the
empirical process of `f / √K`, since `∫ f(x, w) / √K(w) dq = K(w) / √K(w)`. -/
theorem _root_.SingularLearningTheory.tailProcess_eq_empiricalProcess {Ω : Type*} {q : Measure X}
    {f : X → (Fin d → ℝ) → ℝ}
    (hK : ∀ w, K w = ∫ x, f x w ∂q) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) (w : Fin d → ℝ) :
    tailProcess K f Xs n ω w
      = empiricalProcess q (fun x w ↦ f x w / Real.sqrt (K w)) Xs n ω w := by
  simp only [tailProcess, empiricalProcess, integral_div, ← hK, ← sub_div, ← Finset.sum_div]
  rw [inv_mul_eq_div, div_div, mul_comm]

namespace ResolvedLikelihood

variable {R} {q : Measure X} {f : X → (Fin d → ℝ) → ℝ} (L : R.ResolvedLikelihood q f)
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {Xs : ℕ → Ω → X}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- The chart process `ξ_n` is `−ψ_n`, almost surely, for the empirical process `ψ_n` of `a` on
the resolution ([Hit26]'s sign,
[Hit26, Equation (5.2.2)]). -/
theorem ae_chartProcess_eq
    (E : EmpiricalProcessLimit q (fun x (p : (α : R.ι) × cube d (R.b α)) ↦ L.a p.1 x p.2)
      Xs P P') (n : ℕ) :
    ∀ᵐ ω ∂P, L.chartProcess Xs n ω = -(R.toChartFunctions (E.Ψ n ω)) := by
  filter_upwards [E.Ψ_ae_eq n] with ω hω
  funext α
  ext u
  simp only [chartProcess, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    ContinuousMap.sub_apply, chartMonomial, ContinuousMap.coe_mk, smul_eq_mul, Pi.neg_apply,
    ContinuousMap.neg_apply, toChartFunctions_apply, hω, empiricalProcess, L.mean, neg_mul]

/-- The random inputs of [Hit26, Theorem 5.2.6] from [Hit26]'s own
empirical-process statements: an i.i.d. sample `X_i ∼ q` (only the law is used), the
resolved likelihood ([Wat09, Theorem 6.1]), [Hit26, Theorem 4.2.9] for the chart
process `ξ_n` on the resolution and for `ψ_n` on `{K ≥ δ}`, and the Lipschitz tightness of
`ξ_n` in the primary coordinates. The chart process is the continuous representative
`−ψ_n` of the theorem, which agrees with `ξ_n` almost surely. -/
@[expose] noncomputable def empiricalProcessInput (β : ℝ) (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hf : Measurable (Function.uncurry f)) (hK : ∀ w, K w = ∫ x, f x w ∂q)
    (hc : IsCompact {w | w ∈ W ∧ R.δ ≤ K w})
    (E : EmpiricalProcessLimit q (fun x (p : (α : R.ι) × cube d (R.b α)) ↦ L.a p.1 x p.2)
      Xs P P')
    (hlip : R.PrimaryLipschitzTight E.Ψ P)
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P P') :
    R.EmpiricalProcessInput β P P' :=
  haveI : CompactSpace {w // w ∈ W ∧ R.δ ≤ K w} := isCompact_iff_compactSpace.mp hc
  { Kn := empiricalLoss f Xs
    Kn_measurable := measurable_uncurry_empiricalLoss hf hX
    Ξ := fun n ω ↦ -(R.toChartFunctions (E.Ψ n ω))
    Ξ_measurable := fun n ↦
      (continuous_neg.comp R.continuous_toChartFunctions).measurable.comp (E.Ψ_measurable n)
    chart_identity := fun n hn α ↦ by
      filter_upwards [L.empiricalLoss_comp_g Xs hX hlaw hn α, L.ae_chartProcess_eq E n]
        with ω hω hΞ u
      rw [hω u, hΞ]
    Ξlim := fun ω' ↦ -(R.toChartFunctions (E.Ψlim ω'))
    tendsto := E.tendsto.continuous_comp (g := fun Φ ↦ -(R.toChartFunctions Φ))
      (continuous_neg.comp R.continuous_toChartFunctions)
    lipschitz_tight := by
      intro η hη
      obtain ⟨L', N, hN⟩ := hlip η hη
      refine ⟨L', N, fun n hn ↦ le_of_eq_of_le (congrArg P ?_) (hN n hn)⟩
      ext ω
      simp only [mem_ofPred_eq, Pi.neg_apply, ContinuousMap.neg_apply, toChartFunctions_apply,
        neg_sub_neg, abs_sub_comm]
    B := fun n ω ↦ ‖T.Ψ n ω‖
    B_measurable := fun n ↦ (T.Ψ_measurable n).norm
    B_tight := by
      intro η hη
      obtain ⟨M, N, hMN⟩ := T.tendsto.eventually_measure_norm_gt_le hη
      exact ⟨M, N, fun n hn ↦ by simpa only [abs_norm] using hMN n hn⟩
    tail_bound := R.tail_bound_of_tailProcess_le fun n ↦ by
      filter_upwards [T.Ψ_ae_eq n] with ω hω w hw hχ
      have hKδ : R.δ ≤ K w := R.δ_le_of_χ_lt_one hw hχ
      have hψ : T.Ψ n ω ⟨w, hw, hKδ⟩ = tailProcess K f Xs n ω w := by
        rw [hω, tailProcess_eq_empiricalProcess hK]; rfl
      rw [← hψ, ← Real.norm_eq_abs]
      exact ContinuousMap.norm_coe_le_norm _ _ }

end ResolvedLikelihood

end ResolutionAtlas

end SingularLearningTheory
