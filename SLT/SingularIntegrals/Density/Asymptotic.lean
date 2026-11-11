/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Density.Chart
public import SLT.SingularIntegrals.Density.Continuity
public import SLT.SingularIntegrals.Density.Tauberian
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The density asymptotic of a monomial chart

Freeze an essential coordinate. The frozen reduced density is antitone, so its
volume limit determines its density limit. The Lipschitz error is bounded by the
coordinate-weight density, whose volume coefficient is zero because its trace
vanishes on the primary face.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.SliceDensity
open SingularLearningTheory.MellinAnalysis

variable {n : ℕ} {k h : Fin (n + 1) → ℕ} {b : ℝ}
  {f : (Fin (n + 1) → ℝ) → ℝ} {p : Fin (n + 1)}

/-- Freezing a primary coordinate leaves the leading volume coefficient unchanged. -/
private theorem tendsto_frozen_slice_volume (hb : 0 < b) (hp : 0 < k p)
    (hfm : Measurable f) (hf : ContDiffOn ℝ 1 f (cube (n + 1) b)) (hf0 : ∀ u, 0 ≤ f u)
    (hprimary : p ∈ (ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)).primary
        ()) :
    let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
    Tendsto (fun t ↦ (∫⁻ s in Iio t, sliceDens k h b (frozenWt f p) p s).toReal /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0) (𝓝 R.sublevelCoefficient) := by
  let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
  let hg := contDiffOn_frozenWt (p := p) hb.le hf
  let R₀ := ResolutionAtlas.monomialAtlas k h b (frozenWt f p) hb ⟨p, hp⟩ hg (fun u _ ↦ hf0 _)
  have hcoef : R.sublevelCoefficient = R₀.sublevelCoefficient :=
    ResolutionAtlas.monomialAtlas.coefficient_eq_of_trace k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
      hg (fun u _ ↦ hf0 _) (fun v _ ↦ by
        unfold frozenWt
        have hz : ((R.primary ())ᶜ.piecewise v (0 : Fin (n + 1) → ℝ)) p = 0 := by
          simp [hprimary, R]
        rw [← hz, Function.update_eq_self])
  have hv := tendsto_slice_volume (h := h) hb hp (measurable_frozenWt hfm) hg (fun u _ ↦ hf0 _)
  change Tendsto (fun t ↦ (∫⁻ s in Iio t, sliceDens k h b (frozenWt f p) p s).toReal /
    (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0) (𝓝 R₀.sublevelCoefficient) at hv
  rwa [← hcoef] at hv

/-- The coordinate weight vanishes on the primary face and hence has zero volume coefficient. -/
private theorem tendsto_coordinate_slice_volume_zero (hb : 0 < b) (hp : 0 < k p)
    (hf : ContDiffOn ℝ 1 f (cube (n + 1) b)) (hf0 : ∀ u, 0 ≤ f u)
    (hprimary : p ∈ (ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)).primary
        ()) :
    let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
    Tendsto (fun t ↦ (∫⁻ s in Iio t, sliceDens k h b (fun u ↦ u p) p s).toReal /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0) (𝓝 0) := by
  let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
  have hg : ContDiffOn ℝ 1 (fun u : Fin (n + 1) → ℝ ↦ u p) (cube (n + 1) b) :=
    (contDiff_apply ℝ (fun _ : Fin (n + 1) ↦ ℝ) p).contDiffOn
  have hg0 : ∀ u ∈ cube (n + 1) b, 0 ≤ u p := fun u hu ↦ hu.1 p
  let Rg := ResolutionAtlas.monomialAtlas k h b (fun u ↦ u p) hb ⟨p, hp⟩ hg hg0
  have htrace : Rg.essentialTraceMass () = 0 := by
    unfold ResolutionAtlas.essentialTraceMass
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro v hv
    have hz : ((Rg.primary ())ᶜ.piecewise v (0 : Fin (n + 1) → ℝ)) p = 0 := by
      simp [show p ∈ Rg.primary () from hprimary]
    change (∏ j ∈ (Rg.primary ())ᶜ, v j ^ Rg.secondaryExponent () j) *
      (((Rg.primary ())ᶜ.piecewise v 0) p) = 0
    rw [hz, mul_zero]
  have hcoef : Rg.sublevelCoefficient = 0 := by
    rw [ResolutionAtlas.monomialAtlas.coefficient_eq]
    change Rg.sublevelChartCoefficient () = 0
    unfold ResolutionAtlas.sublevelChartCoefficient
    rw [htrace, mul_zero]
  have hv := tendsto_slice_volume (h := h) hb hp (measurable_pi_apply p) hg hg0
  change Tendsto (fun t ↦ (∫⁻ s in Iio t, sliceDens k h b (fun u ↦ u p) p s).toReal /
    (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0) (𝓝 Rg.sublevelCoefficient) at hv
  rwa [hcoef] at hv

/-- The coordinate-error density is negligible at the original chart scale. -/
private theorem tendsto_coordinate_density_zero (hb : 0 < b) (hp : 0 < k p)
    (hf : ContDiffOn ℝ 1 f (cube (n + 1) b)) (hf0 : ∀ u, 0 ≤ f u)
    (hprimary : p ∈ (ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)).primary
        ()) :
    let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
    Tendsto (fun t ↦ t * (sliceDens k h b (fun u ↦ u p) p t).toReal /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0) (𝓝 0) := by
  let h' := Function.update h p (h p + 1)
  let ν := lamP k h' p
  let G := redDens k h' b (fun _ ↦ 1) p ν
  have hν : 0 < ν := by
    dsimp [ν, lamP]
    exact div_pos (by positivity) (aExp_pos hp)
  have hfac : ∀ s, 0 < s → sliceDens k h b (fun u ↦ u p) p s =
      ENNReal.ofReal (s ^ (ν - 1)) * G s := by
    intro s hs
    rw [sliceDens_coord_eq]
    exact sliceDens_eq_redDens hs (aExp_pos hp)
  have hanti : ∀ s t, 0 < s → s ≤ t → G t ≤ G s := fun s t hs hst ↦
    redDens_frozen_antitone (k := k) (h := h') (b := b) (f := fun _ ↦ 1) (p := p) hs hst
  have hfin : ∀ t, 0 < t → ∫⁻ s in Iio t, sliceDens k h b (fun u ↦ u p) p s ≠ ⊤ :=
    fun t _ ↦ ne_top_of_le_ne_top
      (lintegral_slice_ne_top hb hp (measurable_pi_apply p) (continuous_apply p).continuousOn)
      (setLIntegral_le_lintegral _ _)
  exact tendsto_t_mul_density_zero hν hfac hanti hfin
    (tendsto_coordinate_slice_volume_zero hb hp hf hf0 hprimary)

/-- The frozen density has the coefficient `λ` times the volume coefficient. -/
private theorem tendsto_frozen_density (hb : 0 < b) (hp : 0 < k p)
    (hfm : Measurable f) (hf : ContDiffOn ℝ 1 f (cube (n + 1) b)) (hf0 : ∀ u, 0 ≤ f u)
    (hprimary : p ∈ (ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)).primary
        ()) :
    let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
    Tendsto (fun t ↦ t * (sliceDens k h b (frozenWt f p) p t).toReal /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0)
      (𝓝 (R.rlct * R.sublevelCoefficient)) := by
  let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
  have hlam : lamP k h p = R.rlct := by
    exact (R.ratio_eq_of_mem_primary hprimary).trans (ResolutionAtlas.monomialAtlas.rlct_eq ..).symm
  let G := redDens k h b (frozenWt f p) p (lamP k h p)
  have hfac : ∀ s, 0 < s → sliceDens k h b (frozenWt f p) p s =
      ENNReal.ofReal (s ^ (R.rlct - 1)) * G s := by
    intro s hs
    rw [← hlam]
    exact sliceDens_eq_redDens hs (aExp_pos hp)
  have hanti : ∀ s t, 0 < s → s ≤ t → G t ≤ G s := fun s t hs hst ↦
    redDens_frozen_antitone hs hst
  have hfin : ∀ t, 0 < t → ∫⁻ s in Iio t, sliceDens k h b (frozenWt f p) p s ≠ ⊤ :=
    fun t _ ↦ ne_top_of_le_ne_top
      (lintegral_slice_ne_top hb hp (measurable_frozenWt hfm)
        (contDiffOn_frozenWt hb.le hf).continuousOn) (setLIntegral_le_lintegral _ _)
  have hlim := tendsto_toReal_div_of_antitone R.rlct_pos hfac hanti hfin
    (tendsto_frozen_slice_volume hb hp hfm hf hf0 hprimary)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [hfac t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _),
    Real.rpow_sub_one ht.ne']
  have hn : t ^ R.rlct ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  change (G t).toReal / (-Real.log t) ^ (R.mult - 1) =
    t * (t ^ R.rlct / t * (G t).toReal) / (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))
  field_simp [(show 0 < t from ht).ne', hn]

/-- A continuously differentiable nonnegative chart weight has the exact state-density limit. -/
theorem tendsto_chart_density (hb : 0 < b) (hp : 0 < k p)
    (hfc : Continuous f) (hf : ContDiffOn ℝ 1 f (cube (n + 1) b)) (hf0 : ∀ u, 0 ≤ f u)
    (hprimary : p ∈ (ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)).primary
        ())
    {L : ℝ} (hL : 0 ≤ L)
    (hfL : ∀ u ∈ cube (n + 1) b, ∀ u' ∈ cube (n + 1) b,
      |f u - f u'| ≤ L * ∑ q, |u q - u' q|) :
    let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
    Tendsto (fun t ↦ t * (sliceDens k h b f p t).toReal /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0)
      (𝓝 (R.rlct * R.sublevelCoefficient)) := by
  let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hp⟩ hf (fun u _ ↦ hf0 u)
  have h0 := tendsto_frozen_density hb hp hfc.measurable hf hf0 hprimary
  have hg := (tendsto_coordinate_density_zero hb hp hf hf0 hprimary).const_mul L
  simp only [mul_zero] at hg
  have hupper := h0.add hg
  have hlower := h0.sub hg
  simp only [add_zero] at hupper
  simp only [sub_zero] at hlower
  have hfc0 : Continuous (frozenWt f p) := by
    unfold frozenWt
    fun_prop
  have hbounds : ∀ᶠ t in 𝓝[>] 0,
      t * (sliceDens k h b (frozenWt f p) p t).toReal /
          (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1)) -
        L * (t * (sliceDens k h b (fun u ↦ u p) p t).toReal /
          (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) ≤
        t * (sliceDens k h b f p t).toReal / (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1)) ∧
      t * (sliceDens k h b f p t).toReal / (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1)) ≤
        t * (sliceDens k h b (frozenWt f p) p t).toReal /
          (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1)) +
        L * (t * (sliceDens k h b (fun u ↦ u p) p t).toReal /
          (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (Real.rpow_pos_of_pos hb (aExp k p)))]
      with t ht
    have ht1 := ht.2.trans_le (min_le_left _ _)
    have htb := ht.2.trans_le (min_le_right _ _)
    have hff := (continuousAt_sliceDens (h := h) hb hp hfc ht.1 htb).2
    have hf0f := (continuousAt_sliceDens (h := h) hb hp hfc0 ht.1 htb).2
    have hgf := (continuousAt_sliceDens (h := h) hb hp (continuous_apply p) ht.1 htb).2
    have he := sliceDens_perturb (h := h) hb hp hfc.measurable hf0 hL hfL ht.1
    have hu := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨hf0f, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgf⟩) he.1
    have hl := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨hff, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgf⟩) he.2
    rw [ENNReal.toReal_add hf0f (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgf),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hL] at hu
    rw [ENNReal.toReal_add hff (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgf),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hL] at hl
    have hS : 0 ≤ t / (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1)) :=
      div_nonneg ht.1.le (mul_nonneg (Real.rpow_nonneg ht.1.le _)
        (pow_nonneg (neg_nonneg.mpr (Real.log_nonpos ht.1.le ht1.le)) _))
    have hu' := mul_le_mul_of_nonneg_left hu hS
    have hl' := mul_le_mul_of_nonneg_left hl hS
    simp only [div_eq_mul_inv] at hu' hl' ⊢
    constructor <;> nlinarith only [hu', hl']
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hbounds.mono fun _ h ↦ h.1) (hbounds.mono fun _ h ↦ h.2)

end SingularLearningTheory.SliceDensity
