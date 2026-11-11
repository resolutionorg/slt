/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Volume.Atlas
public import SLT.SingularIntegrals.Density.Reduced

/-!
# A single monomial chart as a resolution atlas

This identifies the slice density with the sublevel-volume function, so the
volume limits apply to frozen weights and to the coordinate error weights as well.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.SliceDensity

variable {d : ℕ}

/-- A monomial chart with a continuously differentiable weight is itself an atlas. -/
@[expose] noncomputable def _root_.SingularLearningTheory.ResolutionAtlas.monomialAtlas
    (k h : Fin d → ℕ) (b : ℝ) (f : (Fin d → ℝ) → ℝ)
    (hb : 0 < b) (hk : ∃ j, 0 < k j)
    (hf : ContDiffOn ℝ 1 f (cube d b)) (hf0 : ∀ u ∈ cube d b, 0 ≤ f u) :
    ResolutionAtlas (fun u ↦ ∏ j, u j ^ (2 * k j))
      (fun u ↦ (∏ j, u j ^ (h j : ℝ)) * f u) (cube d b) where
  ι := Unit
  b := fun _ ↦ b
  b_pos := fun _ ↦ hb
  k := fun _ ↦ k
  h := fun _ ↦ h
  active := fun _ ↦ hk
  g := fun _ ↦ id
  g_analytic := fun _ ↦ analyticOnNhd_id
  g_measurable := fun _ ↦ measurable_id
  g_mapsTo := fun _ ↦ mapsTo_id _
  monomial := fun _ _ _ ↦ rfl
  weight := fun _ ↦ f
  weight_nonneg := fun _ ↦ hf0
  weight_contDiffOn := fun _ ↦ hf
  χ := fun _ ↦ 1
  χ_measurable := measurable_const
  χ_nonneg := fun _ ↦ zero_le_one
  χ_le_one := fun _ ↦ le_rfl
  δ := 1
  δ_pos := one_pos
  χ_eq_one := fun _ _ _ ↦ rfl
  transport := by simp

end SingularLearningTheory.SliceDensity

namespace SingularLearningTheory.ResolutionAtlas.monomialAtlas

open SingularLearningTheory SingularLearningTheory.SliceDensity

variable {d : ℕ} (k h : Fin d → ℕ) (b : ℝ) (f : (Fin d → ℝ) → ℝ)
  (hb : 0 < b) (hk : ∃ j, 0 < k j)
  (hf : ContDiffOn ℝ 1 f (cube d b)) (hf0 : ∀ u ∈ cube d b, 0 ≤ f u)

@[simp] theorem rlct_eq :
    (monomialAtlas k h b f hb hk hf hf0).rlct =
      (monomialAtlas k h b f hb hk hf hf0).chartRlct () := by
  change Finset.univ.inf' _ (fun _ : Unit ↦
    (monomialAtlas k h b f hb hk hf hf0).chartRlct ()) = _
  exact Finset.inf'_const _ _

@[simp] theorem mult_eq :
    (monomialAtlas k h b f hb hk hf hf0).mult =
      (monomialAtlas k h b f hb hk hf hf0).chartMult () := by
  change (monomialAtlas k h b f hb hk hf hf0).minimalCharts.sup' _
    (fun _ ↦ (monomialAtlas k h b f hb hk hf hf0).chartMult ()) = _
  exact Finset.sup'_const _ _

private theorem isEssential : (monomialAtlas k h b f hb hk hf hf0).IsEssential () :=
  ⟨(rlct_eq ..).symm, (mult_eq ..).symm⟩

/-- The coefficient of a single chart is its essential trace coefficient. -/
theorem coefficient_eq :
    (monomialAtlas k h b f hb hk hf hf0).sublevelCoefficient =
      (monomialAtlas k h b f hb hk hf hf0).sublevelChartCoefficient () := by
  classical
  change (∑ α : Unit, if (monomialAtlas k h b f hb hk hf hf0).IsEssential α then
    (monomialAtlas k h b f hb hk hf hf0).sublevelChartCoefficient α else 0) = _
  rw [show (Finset.univ : Finset Unit) = {()} from rfl, Finset.sum_singleton]
  exact ite_eq_left (isEssential ..)

/-- Only the weight on the primary face contributes to the leading volume coefficient. -/
theorem coefficient_eq_of_trace {g : (Fin d → ℝ) → ℝ}
    (hg : ContDiffOn ℝ 1 g (cube d b)) (hg0 : ∀ u ∈ cube d b, 0 ≤ g u)
    (heq : ∀ v ∈ cube d b,
      f (((monomialAtlas k h b f hb hk hf hf0).primary ())ᶜ.piecewise v 0) =
      g (((monomialAtlas k h b f hb hk hf hf0).primary ())ᶜ.piecewise v 0)) :
    (monomialAtlas k h b f hb hk hf hf0).sublevelCoefficient =
      (monomialAtlas k h b g hb hk hg hg0).sublevelCoefficient := by
  rw [coefficient_eq, coefficient_eq]
  unfold ResolutionAtlas.sublevelChartCoefficient
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  exact congrArg (fun x ↦ (∏ j ∈ ((monomialAtlas k h b f hb hk hf hf0).primary ())ᶜ,
    v j ^ (monomialAtlas k h b f hb hk hf hf0).secondaryExponent () j) * x) (heq v hv)

end SingularLearningTheory.ResolutionAtlas.monomialAtlas

namespace SingularLearningTheory.SliceDensity

open SingularLearningTheory.MellinAnalysis

section Density

variable {n : ℕ} {k h : Fin (n + 1) → ℕ} {b : ℝ}
  {f : (Fin (n + 1) → ℝ) → ℝ} {p : Fin (n + 1)}

/-- The state measure of a monomial chart has the slice density. -/
private theorem stateDensityMeasure_eq_slice (hb : 0 < b) (hkp : 0 < k p)
    (hfm : Measurable f) :
    stateDensityMeasure (fun u ↦ ∏ j, u j ^ (2 * k j))
      (fun u ↦ (∏ j, u j ^ (h j : ℝ)) * f u) (cube (n + 1) b) =
        volume.withDensity (sliceDens k h b f p) := by
  rw [stateDensityMeasure]
  convert map_monomial_eq_withDensity_sliceDens hb hkp hfm using 2
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  simp only [Real.rpow_natCast]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu.1 j) _),
    ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ pow_nonneg (hu.1 j) _), mul_comm]

/-- A continuous chart weight gives finite total slice mass. -/
theorem lintegral_slice_ne_top (hb : 0 < b) (hkp : 0 < k p) (hfm : Measurable f)
    (hfc : ContinuousOn f (cube (n + 1) b)) :
    ∫⁻ t, sliceDens k h b f p t ≠ ⊤ := by
  have hρc : ContinuousOn (fun u ↦ (∏ j, u j ^ (h j : ℝ)) * f u) (cube (n + 1) b) :=
    (continuous_finsetProd _ fun j _ ↦
      (Real.continuous_rpow_const (Nat.cast_nonneg (h j))).comp
        (continuous_apply j)).continuousOn.mul hfc
  have hρ := hρc.integrableOn_compact (μ := volume) isCompact_Icc
  have := isFiniteMeasure_withDensity_ofReal hρ.2
  have : IsFiniteMeasure (stateDensityMeasure (fun u ↦ ∏ j, u j ^ (2 * k j))
      (fun u ↦ (∏ j, u j ^ (h j : ℝ)) * f u) (cube (n + 1) b)) := by
    unfold stateDensityMeasure
    infer_instance
  have : IsFiniteMeasure (volume.withDensity (sliceDens k h b f p)) :=
    (stateDensityMeasure_eq_slice hb hkp hfm) ▸ inferInstance
  simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using
    (measure_ne_top (volume.withDensity (sliceDens k h b f p)) univ)

/-- The real slice density is integrable on the whole line. -/
theorem integrable_slice (hb : 0 < b) (hkp : 0 < k p) (hfm : Measurable f)
    (hfc : ContinuousOn f (cube (n + 1) b)) :
    Integrable (fun t ↦ (sliceDens k h b f p t).toReal) :=
  integrable_toReal_of_lintegral_ne_top (measurable_sliceDens hfm).aemeasurable
    (lintegral_slice_ne_top hb hkp hfm hfc)

/-- The real slice density represents the monomial state measure. -/
theorem isStateDensity_slice (hb : 0 < b) (hkp : 0 < k p) (hfm : Measurable f)
    (hfc : ContinuousOn f (cube (n + 1) b)) :
    IsStateDensity (fun u ↦ ∏ j, u j ^ (2 * k j))
      (fun u ↦ (∏ j, u j ^ (h j : ℝ)) * f u) (cube (n + 1) b)
      (fun t ↦ (sliceDens k h b f p t).toReal) := by
  refine ⟨(measurable_sliceDens hfm).ennreal_toReal, fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  rw [stateDensityMeasure_eq_slice hb hkp hfm]
  apply withDensity_congr_ae
  filter_upwards [ae_lt_top (measurable_sliceDens hfm)
    (lintegral_slice_ne_top hb hkp hfm hfc)] with t ht
  exact (ENNReal.ofReal_toReal ht.ne).symm

/-- The slice cumulative mass is exactly the sublevel volume. -/
private theorem sublevelVolume_eq_lintegral_slice (hb : 0 < b) (hkp : 0 < k p)
    (hfm : Measurable f) (hf0 : ∀ u ∈ cube (n + 1) b, 0 ≤ f u) (t : ℝ) :
    sublevelVolume (fun u ↦ ∏ j, u j ^ (2 * k j))
      (fun u ↦ (∏ j, u j ^ (h j : ℝ)) * f u) (cube (n + 1) b) t =
        (∫⁻ s in Iio t, sliceDens k h b f p s).toReal := by
  rw [sublevelVolume_eq_stateDensityMeasure_Iic
    (K := fun u ↦ ∏ j, u j ^ (2 * k j))
    (φ := fun u ↦ (∏ j, u j ^ (h j : ℝ)) * f u) (W := cube (n + 1) b)
    measurable_monomial
    (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Icc fun u hu ↦
      mul_nonneg (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
        (hf0 u hu)), stateDensityMeasure_eq_slice hb hkp hfm,
    withDensity_apply _ measurableSet_Iic, setLIntegral_congr Iio_ae_eq_Iic.symm]

/-- Exact volume asymptotics for the cumulative slice density. -/
theorem tendsto_slice_volume (hb : 0 < b) (hkp : 0 < k p)
    (hfm : Measurable f) (hf : ContDiffOn ℝ 1 f (cube (n + 1) b))
    (hf0 : ∀ u ∈ cube (n + 1) b, 0 ≤ f u) :
    let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hkp⟩ hf hf0
    Tendsto (fun t ↦ (∫⁻ s in Iio t, sliceDens k h b f p s).toReal /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0) (𝓝 R.sublevelCoefficient) := by
  let R := ResolutionAtlas.monomialAtlas k h b f hb ⟨p, hkp⟩ hf hf0
  have hρc : ContinuousOn (fun u ↦ (∏ j, u j ^ (h j : ℝ)) * f u) (cube (n + 1) b) :=
    (continuous_finsetProd _ fun j _ ↦
      (Real.continuous_rpow_const (Nat.cast_nonneg (h j))).comp
        (continuous_apply j)).continuousOn.mul hf.continuousOn
  have hv := R.tendsto_sublevelVolume measurableSet_Icc measurable_monomial
    (fun u hu ↦ mul_nonneg
      (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _) (hf0 u hu))
    (hρc.integrableOn_compact isCompact_Icc)
  exact hv.congr fun t ↦ by rw [sublevelVolume_eq_lintegral_slice hb hkp hfm hf0]

/-- Freezing a coordinate at zero preserves the chart's differentiability. -/
theorem contDiffOn_frozenWt (hb : 0 ≤ b) (hf : ContDiffOn ℝ 1 f (cube (n + 1) b)) :
    ContDiffOn ℝ 1 (frozenWt f p) (cube (n + 1) b) := by
  classical
  have hu : ContDiff ℝ 1 (fun u : Fin (n + 1) → ℝ ↦ Function.update u p 0) := by
    apply contDiff_pi.mpr
    intro j
    by_cases hj : j = p
    · subst j; simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : Fin (n + 1) → ℝ ↦ (0 : ℝ)))
    · simpa only [Function.update_of_ne hj] using contDiff_apply ℝ (fun _ : Fin (n + 1) ↦ ℝ) j
  exact hf.comp hu.contDiffOn (fun _ hu ↦ update_mem_box hu hb)

end Density

end SingularLearningTheory.SliceDensity
