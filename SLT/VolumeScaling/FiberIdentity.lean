/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
import SLT.VolumeScaling.WeightedMonomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Positivity.Finset

/-!
# The exact fiber identity

For `F(x,y) = |x|^p · g(y)` on `[-1,1] ×ˢ K` against the `|x|^h`-weighted product, Fubini over
the abstract factor and the exact one-dimensional weighted volume (`WeightedMonomial`) give the
exact sublevel measure

  `μ_F(ε) = (2/(h+1)) · ( ν(K ∩ {g ≤ ε})
            + ∫⁻_{K ∩ {ε < g}} ((ε/g)^β) dν )`,  `β = (h+1)/p`:

below the threshold the fiber is full, above it the one-dimensional computation reads off the
fiber mass exactly. Stated at the `lintegral`/ENNReal level (no integrability side
conditions); the strict peel (`StrictPeel`) uses it with a dyadic-shell estimate.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory

/-- The full mass of the weighted interval. -/
theorem weighted_Icc_mass {h : ℝ} (hh : 0 ≤ h) :
    (volume.withDensity fun x => ENNReal.ofReal (|x| ^ h))
      (Icc (-1 : ℝ) 1) = ENNReal.ofReal (2 / (h + 1)) := by
  have hcont : Continuous fun x : ℝ => |x| ^ h :=
    continuous_abs.rpow_const fun x => Or.inr hh
  rw [withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
      (Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (abs_nonneg x) h),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_abs_rpow_symm hh zero_le_one, Real.one_rpow]
  norm_num

/-- The measure-level one-dimensional computation: the weighted sublevel
mass of `|x|^p` at a threshold in `(0,1)`. -/
theorem weighted_measure_sublevel {p h t : ℝ} (hp : 0 < p) (hh : 0 ≤ h)
    (ht0 : 0 < t) (ht1 : t < 1) :
    (volume.withDensity fun x => ENNReal.ofReal (|x| ^ h))
      (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p ≤ t})
      = ENNReal.ofReal (2 / (h + 1) * t ^ ((h + 1) / p)) := by
  have hfin : (volume.withDensity fun x => ENNReal.ofReal (|x| ^ h))
      (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p ≤ t}) ≠ ⊤ := by
    refine lt_top_iff_ne_top.mp (lt_of_le_of_lt
      (measure_mono inter_subset_left) ?_)
    rw [weighted_Icc_mass hh]
    exact ENNReal.ofReal_lt_top
  have hV := sublevelVol_abs_rpow_withDensity_Icc hp hh ht0 ht1
  unfold sublevelVol at hV
  rw [← ENNReal.ofReal_toReal hfin, hV]

/-- **The exact fiber identity**: the sublevel mass of `|x|^p · g(y)` on
the weighted product splits exactly into the full fibers below threshold
and the exactly computed fibers above it. -/
theorem prod_weighted_fiber_measure {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [SFinite ν] {K : Set β} (hK : MeasurableSet K)
    {g : β → ℝ} (hgm : Measurable g) {p h ε : ℝ} (hp : 0 < p)
    (hh : 0 ≤ h) (hε0 : 0 < ε)
    (hg0 : ∀ y ∈ K, 0 ≤ g y) :
    ((volume.withDensity fun x => ENNReal.ofReal (|x| ^ h)).prod ν)
      ((Icc (-1 : ℝ) 1 ×ˢ K) ∩ {z : ℝ × β | |z.1| ^ p * g z.2 ≤ ε})
    = ENNReal.ofReal (2 / (h + 1)) *
        (ν (K ∩ {y | g y ≤ ε})
         + ∫⁻ y in K ∩ {y | ε < g y},
             ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ∂ν) := by
  classical
  set μw := volume.withDensity fun x => ENNReal.ofReal (|x| ^ h)
    with hμw
  have hFm : MeasurableSet
      {z : ℝ × β | |z.1| ^ p * g z.2 ≤ ε} := by
    have h1 : Measurable fun z : ℝ × β => |z.1| ^ p * g z.2 := by
      have hpow : Measurable fun q : ℝ × ℝ => q.1 ^ q.2 :=
        measurable_pow
      exact (hpow.comp
        ((measurable_fst.abs).prodMk measurable_const)).mul
        (hgm.comp measurable_snd)
    exact h1 measurableSet_Iic
  have hSm : MeasurableSet
      ((Icc (-1 : ℝ) 1 ×ˢ K) ∩ {z : ℝ × β | |z.1| ^ p * g z.2 ≤ ε}) :=
    (measurableSet_Icc.prod hK).inter hFm
  rw [Measure.prod_apply_symm hSm]
  -- identify the fibers
  have hfiber : ∀ y : β, (fun x => (x, y)) ⁻¹'
      ((Icc (-1 : ℝ) 1 ×ˢ K) ∩ {z : ℝ × β | |z.1| ^ p * g z.2 ≤ ε})
      = if y ∈ K then Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε}
        else ∅ := by
    intro y
    by_cases hy : y ∈ K
    · simp only [ite_eq_left hy]
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_prod, mem_ofPred_eq,
        mem_Icc]
      tauto
    · simp only [ite_eq_right hy]
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_prod, mem_ofPred_eq,
        mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact absurd h1.2 hy
  have hlin : ∫⁻ y, μw ((fun x => (x, y)) ⁻¹'
      ((Icc (-1 : ℝ) 1 ×ˢ K) ∩
        {z : ℝ × β | |z.1| ^ p * g z.2 ≤ ε})) ∂ν
      = ∫⁻ y in K, μw (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε}) ∂ν := by
    rw [← lintegral_indicator hK]
    refine lintegral_congr fun y => ?_
    rw [hfiber y]
    by_cases hy : y ∈ K
    · rw [ite_eq_left hy, Set.indicator_of_mem hy]
    · rw [ite_eq_right hy, Set.indicator_of_notMem hy, measure_empty]
  rw [hlin]
  -- split below/above the threshold
  have hdisj : Disjoint (K ∩ {y | g y ≤ ε}) (K ∩ {y | ε < g y}) := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨_, (hle : g y ≤ ε)⟩ ⟨_, (hgt : ε < g y)⟩
    exact absurd hle (not_le.mpr hgt)
  have hunion : K = (K ∩ {y | g y ≤ ε}) ∪ (K ∩ {y | ε < g y}) := by
    rw [← Set.inter_union_distrib_left]
    refine (Set.inter_eq_left.mpr fun y _ => ?_).symm
    rcases le_or_gt (g y) ε with hle | hgt
    · exact Or.inl hle
    · exact Or.inr hgt
  have hm1 : MeasurableSet (K ∩ {y | g y ≤ ε}) :=
    hK.inter (hgm measurableSet_Iic)
  have hm2 : MeasurableSet (K ∩ {y | ε < g y}) :=
    hK.inter (hgm measurableSet_Ioi)
  rw [show ∫⁻ y in K,
        μw (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε}) ∂ν
      = (∫⁻ y in K ∩ {y | g y ≤ ε},
          μw (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε}) ∂ν)
        + ∫⁻ y in K ∩ {y | ε < g y},
            μw (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε}) ∂ν by
    conv_lhs => rw [hunion]
    exact lintegral_union hm2 hdisj]
  -- below threshold: the fiber is everything
  have hbelow : ∫⁻ y in K ∩ {y | g y ≤ ε},
      μw (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε}) ∂ν
      = ENNReal.ofReal (2 / (h + 1)) * ν (K ∩ {y | g y ≤ ε}) := by
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun hm1 ?_
    intro y hy
    change μw (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε})
      = ENNReal.ofReal (2 / (h + 1))
    have hfull : Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε}
        = Icc (-1 : ℝ) 1 := by
      refine Set.inter_eq_left.mpr fun x hx => ?_
      have h1 : |x| ^ p ≤ 1 :=
        Real.rpow_le_one (abs_nonneg x)
          (abs_le.mpr ⟨hx.1, hx.2⟩) hp.le
      have h2 : |x| ^ p * g y ≤ 1 * g y :=
        mul_le_mul_of_nonneg_right h1 (hg0 y hy.1)
      calc |x| ^ p * g y ≤ 1 * g y := h2
        _ = g y := one_mul _
        _ ≤ ε := hy.2
    rw [hfull, hμw, weighted_Icc_mass hh]
  -- above threshold: the one-dimensional computation reads the fiber
  have hmeas2 : Measurable fun y =>
      ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) := by
    have hpow : Measurable fun q : ℝ × ℝ => q.1 ^ q.2 := measurable_pow
    exact (hpow.comp
      ((measurable_const.div hgm).prodMk measurable_const)).ennreal_ofReal
  have habove : ∫⁻ y in K ∩ {y | ε < g y},
      μw (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε}) ∂ν
      = ENNReal.ofReal (2 / (h + 1)) *
        ∫⁻ y in K ∩ {y | ε < g y},
          ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ∂ν := by
    rw [← lintegral_const_mul _ hmeas2]
    refine setLIntegral_congr_fun hm2 ?_
    intro y hy
    change μw (Icc (-1 : ℝ) 1 ∩ {x | |x| ^ p * g y ≤ ε})
      = ENNReal.ofReal (2 / (h + 1))
        * ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p))
    have hgy : ε < g y := hy.2
    have hgpos : 0 < g y := hε0.trans hgy
    have hset : {x : ℝ | |x| ^ p * g y ≤ ε}
        = {x : ℝ | |x| ^ p ≤ ε / g y} := by
      ext x
      rw [mem_ofPred_eq, mem_ofPred_eq, le_div_iff₀ hgpos]
    rw [hset, hμw, weighted_measure_sublevel hp hh
      (div_pos hε0 hgpos) ((div_lt_one hgpos).mpr hgy),
      ENNReal.ofReal_mul (by positivity)]
  rw [hbelow, habove, mul_add]

end SingularLearningTheory
