/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Atlas
public import SLT.VolumeScaling.SpectatorFactor
public import SLT.VolumeScaling.BlowUpSubstitution
public import SLT.VolumeScaling.Transport
public import SLT.MeasureTheory.Measure.WithDensityPi

/-!
# Monomial sublevel volumes on the positive cube

The volume-scaling library reads off the sublevel-volume exponents of a monomial
`∏ |x_j|^{2k_j}` against the power densities `|x_j|^{h_j}` on a *centred* cube `[−b, b]^d`
(`VolumeScaling.hasLLCExponentsOn_weighted_monomial_support`). The chart cubes of a resolution
atlas are the positive cubes `[0, b]^d` with the densities `u_j^{h_j}`. This module folds the
centred cube onto the positive one along the coordinatewise absolute value: the weighted
sublevel measure of the centred cube is `2^d` times that of the positive cube
(`measure_centredCube_inter_eq`), so the exponents agree
(`SingularLearningTheory.hasLLCExponentsOn_monomial_cube`). No thesis counterpart; used by
`TypeOfAtlas.lean`.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology Asymptotics SingularLearningTheory
open scoped ENNReal

/-- The weighted line measure `|x|^h dx`. -/
noncomputable abbrev _root_.MeasureTheory.Measure.weightedLine (h : ℝ) : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal (|x| ^ h)

/-- The weighted line measure is invariant under `x ↦ −x`. -/
private theorem map_neg_weightedLine (h : ℝ) :
    Measure.map (fun x : ℝ ↦ (-1 : ℝ) * x) (Measure.weightedLine h) = Measure.weightedLine h := by
  have hg : Measurable fun x : ℝ ↦ ENNReal.ofReal (|x| ^ h) := by fun_prop
  have hcomp : (fun x : ℝ ↦ ENNReal.ofReal (|x| ^ h))
      = (fun x : ℝ ↦ ENNReal.ofReal (|x| ^ h)) ∘ fun x : ℝ ↦ (-1 : ℝ) * x := by
    funext x
    simp
  conv_lhs => rw [Measure.weightedLine, hcomp]
  rw [SLT.MeasureTheory.Measure.map_withDensity_comp
      volume (measurable_const_mul _) hg, Real.map_volume_mul_left
    (by norm_num)]
  simp [Measure.weightedLine]

private theorem weightedLine_singleton_zero (h : ℝ) : Measure.weightedLine h {0} = 0 :=
  withDensity_absolutelyContinuous _ _ Real.volume_singleton

/-- Folding the weighted interval `[−b, b]` onto `[0, b]` along `|·|` doubles the measure. -/
theorem _root_.MeasureTheory.Measure.map_abs_weightedLine_Icc (h : ℝ) (b : ℝ) :
    Measure.map (fun x : ℝ ↦ |x|) ((Measure.weightedLine h).restrict (Icc (-b) b))
      = (2 : ℝ≥0∞) • (Measure.weightedLine h).restrict (Icc 0 b) := by
  ext s hs
  have habs : Measurable fun x : ℝ ↦ |x| := continuous_abs.measurable
  rw [Measure.map_apply habs hs, Measure.restrict_apply (habs hs), Measure.smul_apply,
    Measure.restrict_apply hs, smul_eq_mul]
  have hset : (fun x : ℝ ↦ |x|) ⁻¹' s ∩ Icc (-b) b
      = (s ∩ Icc 0 b) ∪ (fun x : ℝ ↦ (-1 : ℝ) * x) ⁻¹' (s ∩ Ioc 0 b) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Icc, mem_union, mem_Ioc, neg_one_mul]
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      constructor
      · rintro ⟨hs, -, hb⟩
        exact Or.inl ⟨hs, hx, hb⟩
      · rintro (⟨hs, -, hb⟩ | ⟨-, h0, -⟩)
        · exact ⟨hs, by linarith, hb⟩
        · linarith
    · rw [abs_of_neg hx]
      constructor
      · rintro ⟨hs, hb, -⟩
        exact Or.inr ⟨hs, by linarith, by linarith⟩
      · rintro (⟨-, h0, -⟩ | ⟨hs, -, hb⟩)
        · linarith
        · exact ⟨hs, by linarith, by linarith⟩
  have hdisj : Disjoint (s ∩ Icc 0 b) ((fun x : ℝ ↦ (-1 : ℝ) * x) ⁻¹' (s ∩ Ioc 0 b)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx0, -⟩ ⟨-, hx, -⟩
    simp only [neg_one_mul] at hx
    linarith
  have hmeas : MeasurableSet ((fun x : ℝ ↦ (-1 : ℝ) * x) ⁻¹' (s ∩ Ioc 0 b)) :=
    (measurable_const_mul _) (hs.inter measurableSet_Ioc)
  rw [hset, measure_union hdisj hmeas, ← Measure.map_apply (measurable_const_mul _)
    (hs.inter measurableSet_Ioc), map_neg_weightedLine]
  have hIoc : Measure.weightedLine h (s ∩ Ioc 0 b) = Measure.weightedLine h (s ∩ Icc 0 b) := by
    rw [← Icc_sdiff_left, ← inter_sdiff_assoc, measure_sdiff_null (weightedLine_singleton_zero h)]
  rw [hIoc, two_mul]

/-- The centred cube `[−b, b]^d`. -/
private abbrev centeredCube (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ ↦ Icc (-b) b

/-- The coordinatewise absolute value. -/
private def absMap {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ := fun j ↦ |x j|

private theorem measurable_absMap {d : ℕ} : Measurable (absMap (d := d)) :=
  Measurable.of_eval fun j ↦ continuous_abs.measurable.comp (measurable_pi_apply j)

/-- The product of the weighted line measures `∏ |x_j|^{h_j} dx`. -/
noncomputable abbrev _root_.MeasureTheory.Measure.weightedPi {d : ℕ}
    (h : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun j ↦ Measure.weightedLine (h j)

private theorem isFiniteMeasure_weightedLine_restrict {h b : ℝ} (hh : 0 ≤ h) (hb : 0 < b) :
    IsFiniteMeasure ((Measure.weightedLine h).restrict (Icc (-b) b)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (weighted_Icc_ne_top hh hb)⟩

private theorem isFiniteMeasure_weightedLine_restrict_pos {h b : ℝ} (hh : 0 ≤ h) (hb : 0 < b) :
    IsFiniteMeasure ((Measure.weightedLine h).restrict (Icc 0 b)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono (Icc_subset_Icc (by linarith) le_rfl))
      (lt_top_iff_ne_top.mpr (weighted_Icc_ne_top hh hb))⟩

/-- Folding the weighted centred cube onto the positive cube multiplies the measure by `2^d`:
`(weightedPi h) (centeredCube ∩ absMap ⁻¹' S) = 2^d (weightedPi h) (cube ∩ S)`. -/
private theorem weightedPi_centeredCube_inter {d : ℕ} (h : Fin d → ℝ) (hh : ∀ j, 0 ≤ h j) {b : ℝ}
    (hb : 0 < b) {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    Measure.weightedPi h (centeredCube d b ∩ absMap ⁻¹' S) = 2 ^ d * Measure.weightedPi h
        (cube d b ∩ S) := by
  haveI : ∀ j, IsFiniteMeasure ((Measure.weightedLine (h j)).restrict (Icc (-b) b)) := fun j ↦
    isFiniteMeasure_weightedLine_restrict (hh j) hb
  haveI : ∀ j, IsFiniteMeasure ((Measure.weightedLine (h j)).restrict (Icc 0 b)) := fun j ↦
    isFiniteMeasure_weightedLine_restrict_pos (hh j) hb
  have hmap : Measure.map absMap ((Measure.weightedPi h).restrict (centeredCube d b))
      = (2 : ℝ≥0∞) ^ d • (Measure.weightedPi h).restrict (cube d b) := by
    rw [centeredCube, Measure.restrict_pi_pi, cube_eq_pi, Measure.restrict_pi_pi]
    have h1 := Measure.pi_map_pi (μ := fun j ↦ (Measure.weightedLine (h j)).restrict (Icc (-b) b))
      (f := fun _ : Fin d ↦ fun x : ℝ ↦ |x|) (fun _ ↦ continuous_abs.measurable.aemeasurable)
    simp only [Measure.map_abs_weightedLine_Icc] at h1
    rw [show (fun x : Fin d → ℝ ↦ fun j ↦ |x j|) = absMap from rfl] at h1
    rw [h1]
    haveI : ∀ j, IsFiniteMeasure ((2 : ℝ≥0∞) • (Measure.weightedLine (h j)).restrict (Icc 0 b)) :=
      fun j ↦ Measure.smul_finite _ (by simp)
    refine Measure.pi_eq fun s hs ↦ ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
    simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have h2 : Measure.weightedPi h (centeredCube d b ∩ absMap ⁻¹' S)
      = ((Measure.weightedPi h).restrict (centeredCube d b)) (absMap ⁻¹' S) := by
    rw [Measure.restrict_apply (measurable_absMap hS), inter_comm]
  rw [h2, ← Measure.map_apply measurable_absMap hS, hmap, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hS, inter_comm]

/-- `MeasureTheory.Measure.weightedPi h` is the Lebesgue measure with the density `∏ |x_j|^{h_j}`.
-/
theorem _root_.MeasureTheory.Measure.weightedPi_eq_withDensity {d : ℕ} (h : Fin d → ℝ) :
    Measure.weightedPi h = volume.withDensity fun x ↦ ∏ j, ENNReal.ofReal (|x j| ^ h j) := by
  change Measure.pi (fun j ↦ volume.withDensity fun x ↦ ENNReal.ofReal (|x| ^ h j)) = _
  rw [Measure.pi_withDensity (fun _ ↦ volume) (fun j x ↦ ENNReal.ofReal (|x| ^ h j))
    (fun _ ↦ by fun_prop), volume_pi]

/-- The sublevel volume of a function only depends on the measure restricted to the
localization set. -/
private theorem sublevelVol_congr_restrict {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    {K : Set α}
    (hK : MeasurableSet K) (h : μ.restrict K = ν.restrict K) (f : α → ℝ) (ε : ℝ) :
    sublevelVol μ K f ε = sublevelVol ν K f ε := by
  rw [sublevelVol, sublevelVol, inter_comm, ← Measure.restrict_apply' hK, h,
    Measure.restrict_apply' hK, inter_comm]

/-- **The monomial read-off on the positive cube.** The monomial `∏ u_j^{2k_j}` on `[0, b]^d`
against the density `∏ u_j^{h_j}` has sublevel-volume exponents `λ = min_{k_j > 0} (h_j + 1)/(2k_j)`
and multiplicity the number of coordinates attaining the minimum (coordinates with `k_j = 0`
are spectators). The centred-cube read-off of the volume-scaling library, folded. -/
theorem _root_.SingularLearningTheory.hasLLCExponentsOn_monomial_cube {d : ℕ} (k h : Fin d → ℕ)
    {lam : ℝ}
    (hlam : 0 < lam)
    (hmin : ∀ j, 0 < k j → lam ≤ ((h j : ℝ) + 1) / (2 * k j))
    (hatt : ∃ j, 0 < k j ∧ ((h j : ℝ) + 1) / (2 * k j) = lam) {b : ℝ} (hb : 0 < b) :
    HasLLCExponentsOn (volume.withDensity fun u ↦ ENNReal.ofReal (∏ j, u j ^ (h j : ℝ)))
      (cube d b) (fun u ↦ ∏ j, u j ^ (2 * k j)) lam
      ((Finset.univ.filter fun j ↦ 0 < k j ∧ ((h j : ℝ) + 1) / (2 * k j) = lam).card) := by
  have hh : ∀ j, (0 : ℝ) ≤ (h j : ℝ) := fun j ↦ Nat.cast_nonneg _
  have hcentred := hasLLCExponentsOn_weighted_monomial_support k (fun j ↦ (h j : ℝ)) hh
    hmin hatt hb
  have hfun : (fun x : Fin d → ℝ ↦ ∏ j, |x j| ^ (2 * k j : ℝ)) = fun u ↦ ∏ j, u j ^ (2 * k j) := by
    funext x
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [show (2 * k j : ℝ) = ((2 * k j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      (even_two_mul (k j)).pow_abs]
  have hcube : MeasurableSet (cube d b) := measurableSet_Icc
  have hfm : Measurable fun u : Fin d → ℝ ↦ ∏ j, u j ^ (2 * k j) :=
    Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
  -- the fold: sublevel volumes on the centred cube are `2^d` times those on the positive cube
  have hV : sublevelVol (Measure.weightedPi fun j ↦ (h j : ℝ)) (centeredCube d b)
      (fun u ↦ ∏ j, u j ^ (2 * k j)) =ᶠ[𝓝[>] (0 : ℝ)] fun ε ↦ (2 : ℝ) ^ d *
        sublevelVol (Measure.weightedPi fun j ↦ (h j : ℝ)) (cube d b) (fun u ↦ ∏ j, u j ^ (2 * k j))
            ε := by
    refine Eventually.of_forall fun ε ↦ ?_
    simp only [sublevelVol]
    have hS : MeasurableSet {u : Fin d → ℝ | ∏ j, u j ^ (2 * k j) ≤ ε} :=
      measurableSet_le hfm measurable_const
    have hinv : {u : Fin d → ℝ | ∏ j, u j ^ (2 * k j) ≤ ε}
        = absMap ⁻¹' {u : Fin d → ℝ | ∏ j, u j ^ (2 * k j) ≤ ε} := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, absMap, (even_two_mul _).pow_abs]
    conv_lhs => rw [hinv]
    rw [weightedPi_centeredCube_inter _ hh hb hS, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat]
  rw [hfun] at hcentred
  have hpos : HasLLCExponentsOn (Measure.weightedPi fun j ↦ (h j : ℝ)) (cube d b)
      (fun u ↦ ∏ j, u j ^ (2 * k j)) lam
      ((Finset.univ.filter fun j ↦ 0 < k j ∧ ((h j : ℝ) + 1) / (2 * k j) = lam).card) :=
    (hasLLCExponentsOn_congr_const_mul (by positivity) hV).mp hcentred
  -- change the density to `∏ u_j^{h_j}` on the cube
  have hrestr : (Measure.weightedPi fun j ↦ (h j : ℝ)).restrict (cube d b)
      = (volume.withDensity fun u ↦ ENNReal.ofReal (∏ j, u j ^ (h j : ℝ))).restrict (cube d b) := by
    rw [Measure.weightedPi_eq_withDensity, restrict_withDensity hcube, restrict_withDensity hcube]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hcube] with u hu
    rw [ENNReal.ofReal_prod_of_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _]
    exact Finset.prod_congr rfl fun j _ ↦ by rw [abs_of_nonneg (hu.1 j)]
  rw [HasLLCExponentsOn, funext (sublevelVol_congr_restrict hcube hrestr _)] at hpos
  exact hpos

end SingularLearningTheory
