/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.Analysis.Mellin.InverseMellinPV
public import SLT.Analysis.Fourier.DirichletJordan
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# [Wat09, Theorem 4.5] with the book's hypothesis: bounded variation near `s`

`inverseMellin_tendsto_of_boundedVariation`: if (4.10) converges absolutely at `Re z = c`
and `f` has bounded variation on
a neighbourhood `[s − ε, s + ε]` of `s > 0`, then the symmetric truncations of the inverse line
integral converge to `½{f(s+0) + f(s−0)}` — exactly the statement of Theorem 4.5 (the one-sided
limits exist by `remark_4_3_one_sided_limits`; here they are named `fp`, `fm`).

In the logarithmic variable the representative `h(x) = f(eˣ) e^{(c+1)x}` near `u = log s` is
`h(u ± t) − f(s±0) s^{c+1} = s^{c+1} [(g(±t) − f(s±0)) + g(±t)(e^{±(c+1)t} − 1)]` with
`g(t) = f(s eᵗ)`, of bounded variation near `0` (`eVariationOn.comp_le_of_monotoneOn`): the first
term is the Dirichlet–Jordan near part (`Real.tendsto_near_right_of_boundedVariationOn`);
the second is
Riemann–Lebesgue for a Lipschitz-dominated integrand
(`Real.tendsto_integral_mul_dirichletKer_Ioc_of_le_mul`).
-/

public section

open MeasureTheory Set Filter Topology Complex

namespace SingularLearningTheory.MellinAnalysis

/-- `t ↦ s eᵗ` maps `𝓝[>] 0` to `𝓝[>] s`. -/
private theorem tendsto_mul_exp_nhdsGT {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t : ℝ ↦ s * Real.exp t) (𝓝[>] 0) (𝓝[>] s) := by
  refine Tendsto.inf ?_ (tendsto_principal_principal.mpr fun t ht ↦ ?_)
  · have : Tendsto (fun t : ℝ ↦ s * Real.exp t) (𝓝 0) (𝓝 (s * Real.exp 0)) :=
      (continuous_const.mul Real.continuous_exp).tendsto 0
    simpa using this
  · have h1 : (1 : ℝ) < Real.exp t := by simpa using Real.exp_lt_exp.mpr (show (0 : ℝ) < t from ht)
    exact lt_mul_of_one_lt_right hs h1

/-- `t ↦ s eᵗ` maps `𝓝[<] 0` to `𝓝[<] s`. -/
private theorem tendsto_mul_exp_nhdsLT {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t : ℝ ↦ s * Real.exp t) (𝓝[<] 0) (𝓝[<] s) := by
  refine Tendsto.inf ?_ (tendsto_principal_principal.mpr fun t ht ↦ ?_)
  · have : Tendsto (fun t : ℝ ↦ s * Real.exp t) (𝓝 0) (𝓝 (s * Real.exp 0)) :=
      (continuous_const.mul Real.continuous_exp).tendsto 0
    simpa using this
  · have h1 : Real.exp t < 1 := by simpa using Real.exp_lt_exp.mpr (show t < (0 : ℝ) from ht)
    exact mul_lt_of_lt_one_right hs h1

/-- **[Wat09, Theorem 4.5] (inverse Mellin transform), the book's statement.** If (4.10)
converges absolutely at `Re z = c` and `f` has bounded variation on `[s − ε, s + ε]` (`s > 0`,
`0 < ε < s`), with one-sided limits `f(s+0) = fp`, `f(s−0) = fm`, then
`(1/2πi) ∫_{c−iM}^{c+iM} F(z) s^{−z−1} dz → ½{f(s+0) + f(s−0)}` as `M → ∞`. -/
theorem inverseMellin_tendsto_of_boundedVariation (f : ℝ → ℝ) {c : ℝ}
    (hconv : IntegrableOn (fun t ↦ f t * t ^ c) (Ioi 0)) {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε)
    (hεs : ε < s) (hbv : BoundedVariationOn f (Icc (s - ε) (s + ε)))
    {fp fm : ℝ} (hfp : Tendsto f (𝓝[>] s) (𝓝 fp)) (hfm : Tendsto f (𝓝[<] s) (𝓝 fm)) :
    Tendsto (fun M : ℝ ↦ inverseMellinTrunc c (mellinTransform f) s M) atTop
      (𝓝 (((fp + fm) / 2 : ℝ) : ℂ)) := by
  -- the logarithmic radius `δ = log((s + ε)/s)`: `s e^δ = s + ε`, `s e^{−δ} ≥ s − ε`
  set δ := Real.log ((s + ε) / s) with hδdef
  have hratio : 1 < (s + ε) / s := by rw [one_lt_div hs]; linarith
  have hδ : 0 < δ := Real.log_pos hratio
  have hexpδ : Real.exp δ = (s + ε) / s := Real.exp_log (by positivity)
  have hexpnδ : Real.exp (-δ) = s / (s + ε) := by rw [Real.exp_neg, hexpδ, inv_div]
  set u := Real.log s with hu
  set a := c + 1 with ha
  have hsu : Real.exp u = s := Real.exp_log hs
  have hsa : Real.exp (a * u) = s ^ a := by rw [Real.rpow_def_of_pos hs, mul_comm]
  have hsa0 : 0 < s ^ a := Real.rpow_pos_of_pos hs a
  -- `g(t) = f(s eᵗ)`
  set g : ℝ → ℝ := fun t ↦ f (s * Real.exp t) with hg
  have hmono : MonotoneOn (fun t : ℝ ↦ s * Real.exp t) (Icc (-δ) δ) :=
    fun x _ y _ hxy ↦ mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxy) hs.le
  have hmaps : MapsTo (fun t : ℝ ↦ s * Real.exp t) (Icc (-δ) δ) (Icc (s - ε) (s + ε)) := by
    intro t ht
    have hspos : 0 < s + ε := by linarith
    constructor
    · have h1 : Real.exp (-δ) ≤ Real.exp t := Real.exp_le_exp.mpr ht.1
      have h3 : s - ε ≤ s * (s / (s + ε)) := by
        rw [mul_div_assoc', le_div_iff₀ hspos]
        nlinarith
      calc s - ε ≤ s * (s / (s + ε)) := h3
        _ = s * Real.exp (-δ) := by rw [hexpnδ]
        _ ≤ s * Real.exp t := mul_le_mul_of_nonneg_left h1 hs.le
    · calc s * Real.exp t ≤ s * Real.exp δ :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht.2) hs.le
        _ = s + ε := by rw [hexpδ]; field_simp
  have hbvg : BoundedVariationOn g (Icc (-δ) δ) := by
    unfold BoundedVariationOn at hbv ⊢
    exact ne_top_of_le_ne_top hbv (eVariationOn.comp_le_of_monotoneOn f _ hmono hmaps)
  have hbvg' : BoundedVariationOn g (Icc (0 - δ) (0 + δ)) := by rwa [zero_sub, zero_add]
  have hgp : Tendsto g (𝓝[>] 0) (𝓝 fp) := hfp.comp (tendsto_mul_exp_nhdsGT hs)
  have hgm : Tendsto g (𝓝[<] 0) (𝓝 fm) := hfm.comp (tendsto_mul_exp_nhdsLT hs)
  -- monotone pieces and the bound `B` on `[−δ, δ]`
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    BoundedVariationOn.exists_monotone_sub_monotone (by linarith : -δ ≤ δ) hbvg
  set B : ℝ := |p δ| + |p (-δ)| + (|q δ| + |q (-δ)|) with hB
  have hgB : ∀ t ∈ Icc (-δ) δ, |g t| ≤ B := fun t ht ↦ by
    rw [hpq t ht]
    calc |p t - q t| ≤ |p t| + |q t| := abs_sub _ _
      _ ≤ B := add_le_add (Monotone.abs_le_of_mem hp ht) (Monotone.abs_le_of_mem hq ht)
  have hIoc : Ioc (0 : ℝ) δ ⊆ Icc (-δ) δ := fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩
  have hnegIoc : ∀ t ∈ Ioc (0 : ℝ) δ, -t ∈ Icc (-δ) δ := fun t ht ↦
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- measurability of `g` and of `t ↦ g(−t)` on `(0, δ]`
  have hgm₁ : AEStronglyMeasurable g (volume.restrict (Ioc 0 δ)) := by
    refine (hp.measurable.sub hq.measurable).aestronglyMeasurable.congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ (hpq t (hIoc ht)).symm
  have hgm₂ : AEStronglyMeasurable (fun t ↦ g (-t)) (volume.restrict (Ioc 0 δ)) := by
    have h1 : Antitone fun t : ℝ ↦ p (-t) := hp.comp_antitone fun x y hxy ↦ neg_le_neg hxy
    have h2 : Antitone fun t : ℝ ↦ q (-t) := hq.comp_antitone fun x y hxy ↦ neg_le_neg hxy
    refine (h1.measurable.sub h2.measurable).aestronglyMeasurable.congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ (hpq (-t) (hnegIoc t ht)).symm
  -- the Lipschitz bound on `e^{±at} − 1`
  have hexp_lip : ∀ t ∈ Ioc (0 : ℝ) δ, |Real.exp (a * t) - 1| ≤ |a| * Real.exp (|a| * δ) * t ∧
      |Real.exp (-(a * t)) - 1| ≤ |a| * Real.exp (|a| * δ) * t := by
    intro t ht
    have h1 := Real.abs_exp_sub_one_le_abs_mul_exp (a * t)
    have h2 := Real.abs_exp_sub_one_le_abs_mul_exp (-(a * t))
    rw [abs_mul, abs_of_pos ht.1] at h1
    rw [abs_neg, abs_mul, abs_of_pos ht.1] at h2
    have hle : Real.exp (|a| * t) ≤ Real.exp (|a| * δ) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _))
    constructor
    · refine h1.trans ?_
      calc |a| * t * Real.exp (|a| * t) ≤ |a| * t * Real.exp (|a| * δ) :=
            mul_le_mul_of_nonneg_left hle (mul_nonneg (abs_nonneg _) ht.1.le)
        _ = |a| * Real.exp (|a| * δ) * t := by ring
    · refine h2.trans ?_
      calc |a| * t * Real.exp (|a| * t) ≤ |a| * t * Real.exp (|a| * δ) :=
            mul_le_mul_of_nonneg_left hle (mul_nonneg (abs_nonneg _) ht.1.le)
        _ = |a| * Real.exp (|a| * δ) * t := by ring
  have hB0 : 0 ≤ B := by positivity
  -- the right near part
  have hdecR : ∀ t, logVar f c (u + t) - fp * s ^ a
      = s ^ a * ((g t - fp) + g t * (Real.exp (a * t) - 1)) := by
    intro t
    simp only [logVar, hg, Real.exp_add, hsu, ← ha]
    rw [mul_add, Real.exp_add, hsa]
    ring
  have hNR : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ,
      (logVar f c (u + t) - fp * s ^ a) * Real.dirichletKer M t) atTop (𝓝 0) := by
    have h1 := Real.tendsto_near_right_of_boundedVariationOn hδ hbvg' hgp
    simp only [zero_add] at h1
    have hlip : ∀ t ∈ Ioc (0 : ℝ) δ, |g t * (Real.exp (a * t) - 1)|
        ≤ (B * (|a| * Real.exp (|a| * δ))) * t := fun t ht ↦ by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (hgB t (hIoc ht)) (hexp_lip t ht).1 (abs_nonneg _) hB0
    have h2 := Real.tendsto_integral_mul_dirichletKer_Ioc_of_le_mul
      (hgm₁.mul (Continuous.aestronglyMeasurable (by fun_prop))) hlip
    have e : ∀ M, ∫ t in Ioc (0 : ℝ) δ, (logVar f c (u + t) - fp * s ^ a) * Real.dirichletKer M t
        = s ^ a * ((∫ t in Ioc (0 : ℝ) δ, (g t - fp) * Real.dirichletKer M t)
          + ∫ t in Ioc (0 : ℝ) δ, g t * (Real.exp (a * t) - 1) * Real.dirichletKer M t) := by
      intro M
      rw [← integral_add
        (Real.integrableOn_mul_dirichletKer_of_bounded (q := fun t ↦ g t - fp)
          (hgm₁.sub aestronglyMeasurable_const)
          (fun t ht ↦ (abs_sub _ _).trans (add_le_add (hgB t (hIoc ht)) le_rfl)) M)
        (Real.integrableOn_mul_dirichletKer_of_bounded (q := fun t ↦ g t * (Real.exp (a * t) - 1))
          (hgm₁.mul (Continuous.aestronglyMeasurable (by fun_prop)))
          (fun t ht ↦ (hlip t ht).trans (mul_le_mul_of_nonneg_left ht.2 (by positivity))) M),
        ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
      rw [hdecR]
      ring
    simp_rw [e]
    simpa using (h1.add h2).const_mul (s ^ a)
  -- the left near part
  have hdecL : ∀ t, logVar f c (u - t) - fm * s ^ a
      = s ^ a * ((g (-t) - fm) + g (-t) * (Real.exp (-(a * t)) - 1)) := by
    intro t
    simp only [logVar, hg, sub_eq_add_neg, Real.exp_add, hsu, ← ha]
    rw [mul_add, Real.exp_add, hsa, mul_neg]
    ring
  have hNL : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ,
      (logVar f c (u - t) - fm * s ^ a) * Real.dirichletKer M t) atTop (𝓝 0) := by
    have h1 := Real.tendsto_near_left_of_boundedVariationOn hδ hbvg' hgm
    simp only [zero_sub] at h1
    have hlip : ∀ t ∈ Ioc (0 : ℝ) δ, |g (-t) * (Real.exp (-(a * t)) - 1)|
        ≤ (B * (|a| * Real.exp (|a| * δ))) * t := fun t ht ↦ by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (hgB (-t) (hnegIoc t ht)) (hexp_lip t ht).2 (abs_nonneg _) hB0
    have h2 := Real.tendsto_integral_mul_dirichletKer_Ioc_of_le_mul
      (hgm₂.mul (Continuous.aestronglyMeasurable (by fun_prop))) hlip
    have e : ∀ M, ∫ t in Ioc (0 : ℝ) δ, (logVar f c (u - t) - fm * s ^ a) * Real.dirichletKer M t
        = s ^ a * ((∫ t in Ioc (0 : ℝ) δ, (g (-t) - fm) * Real.dirichletKer M t)
          + ∫ t in Ioc (0 : ℝ) δ, g (-t) * (Real.exp (-(a * t)) - 1) * Real.dirichletKer M t) := by
      intro M
      rw [← integral_add
        (Real.integrableOn_mul_dirichletKer_of_bounded (q := fun t ↦ g (-t) - fm)
          (hgm₂.sub aestronglyMeasurable_const)
          (fun t ht ↦ (abs_sub _ _).trans (add_le_add (hgB (-t) (hnegIoc t ht)) le_rfl)) M)
        (Real.integrableOn_mul_dirichletKer_of_bounded
          (q := fun t ↦ g (-t) * (Real.exp (-(a * t)) - 1))
          (hgm₂.mul (Continuous.aestronglyMeasurable (by fun_prop)))
          (fun t ht ↦ (hlip t ht).trans (mul_le_mul_of_nonneg_left ht.2 (by positivity))) M),
        ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
      rw [hdecL]
      ring
    simp_rw [e]
    simpa using (h1.add h2).const_mul (s ^ a)
  exact inverseMellin_tendsto_of_near f hconv hs hδ hNR hNL

end SingularLearningTheory.MellinAnalysis
