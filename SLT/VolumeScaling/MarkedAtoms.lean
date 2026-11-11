/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott
-/
module

public import SLT.PartialResolution.MarkedTransport
import SLT.PartialResolution.ExactTransport
public import SLT.PartialResolution.Defs
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The marked-scaling and marked-shear transports

The two volume transports of the chart-box blow-up primitives of hironaka's
`Hironaka.Analytic.PartialResolution.MarkedTransport`:

* `Analytic.transportsToOn_markedScale`: the marked scaling `markedScale u b` (the pivot coordinate
  scales the marked block) transports the volume on the whole space with the monomial density
  `markedDensity u n = |x_u|^n`;
* `Analytic.transportsToOn_markedShear`: the marked shear `markedShear b c` (the marked block
absorbs a
  measurable function of the other coordinates) transports it with unit density.

Both are conjugations, through the measure-preserving splits `markScaleSplit` and `shearSplit`
supplied upstream, of the canonical atoms proved here: the block scaling
`(u, y) ↦ (u, u • y)` (`transportsToOn_scaleBlockProd`, per fiber `Measure.addHaar_smul`, the
`u = 0` fiber null) and the shear `(w, y) ↦ (w, y + c w)` (`measurePreserving_shearEquivGen`, a
skew product of translations).
-/

public section

open MeasureTheory Set Analytic
open scoped ENNReal Pointwise

namespace Analytic

/-! ## The block-scaling atom -/

/-- The blow-up substitution: the scalar coordinate scales the block. -/
private def scaleBlock (m : ℕ) : ℝ × (Fin m → ℝ) → ℝ × (Fin m → ℝ) :=
  fun p => (p.1, p.1 • p.2)

private theorem measurable_scaleBlock (m : ℕ) : Measurable (scaleBlock m) :=
  measurable_fst.prodMk (measurable_fst.smul measurable_snd)

/-- The scaling density. -/
private noncomputable def scaleDensity (m : ℕ) : ℝ × (Fin m → ℝ) → ℝ≥0∞ :=
  fun p => ENNReal.ofReal (|p.1| ^ m)

private theorem measurable_scaleDensity (m : ℕ) : Measurable (scaleDensity m) :=
  (measurable_fst.abs.pow_const m).ennreal_ofReal

/-- The global identity: the weighted product volume pushes forward to
the product volume. -/
private theorem map_scaleBlock_withDensity (m : ℕ) :
    Measure.map (scaleBlock m) (volume.withDensity (scaleDensity m)) =
      volume := by
  ext t ht
  rw [Measure.map_apply (measurable_scaleBlock m) ht,
    withDensity_apply _ ((measurable_scaleBlock m) ht)]
  have hS : MeasurableSet (scaleBlock m ⁻¹' t) := (measurable_scaleBlock m) ht
  calc ∫⁻ p in scaleBlock m ⁻¹' t, scaleDensity m p ∂volume
      = ∫⁻ p, (scaleBlock m ⁻¹' t).indicator (scaleDensity m) p ∂volume := by
        rw [lintegral_indicator hS]
    _ = ∫⁻ u, ∫⁻ y, (scaleBlock m ⁻¹' t).indicator (scaleDensity m) (u, y)
          ∂volume ∂volume := by
        exact lintegral_prod _ ((measurable_scaleDensity m).indicator hS).aemeasurable
    _ = ∫⁻ u, volume (Prod.mk u ⁻¹' t) ∂volume := by
        refine lintegral_congr_ae ?_
        filter_upwards [compl_mem_ae_iff.mpr
          (Real.volume_singleton (a := 0))] with u hu
        have hu0 : u ≠ 0 := by simpa using hu
        have hmemb : MeasurableSet {y : Fin m → ℝ | u • y ∈ Prod.mk u ⁻¹' t} :=
          (measurable_id.const_smul u) (measurable_prodMk_left ht)
        calc ∫⁻ y, (scaleBlock m ⁻¹' t).indicator (scaleDensity m) (u, y) ∂volume
            = ∫⁻ y, ENNReal.ofReal (|u| ^ m) *
                ({y : Fin m → ℝ | u • y ∈ Prod.mk u ⁻¹' t}).indicator
                  1 y ∂volume := by
              refine lintegral_congr fun y => ?_
              by_cases hy : (u, u • y) ∈ t
              · rw [indicator_of_mem (by exact hy) (scaleDensity m),
                  indicator_of_mem (by exact hy)]
                simp [scaleDensity]
              · rw [indicator_of_notMem (by exact hy) (scaleDensity m),
                  indicator_of_notMem (by exact hy)]
                simp
          _ = ENNReal.ofReal (|u| ^ m) *
                ∫⁻ y, ({y : Fin m → ℝ | u • y ∈ Prod.mk u ⁻¹' t}).indicator
                  1 y ∂volume :=
              lintegral_const_mul _ (measurable_const.indicator hmemb)
          _ = ENNReal.ofReal (|u| ^ m) *
                volume {y : Fin m → ℝ | u • y ∈ Prod.mk u ⁻¹' t} := by
              rw [lintegral_indicator_one hmemb]
          _ = volume (Prod.mk u ⁻¹' t) := by
              have hset : {y : Fin m → ℝ | u • y ∈ Prod.mk u ⁻¹' t} =
                  u⁻¹ • (Prod.mk u ⁻¹' t) := by
                ext y
                rw [mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀
                  (inv_ne_zero hu0), inv_inv]
              rw [hset, Measure.addHaar_smul, Module.finrank_pi,
                Fintype.card_fin, ← mul_assoc,
                ← ENNReal.ofReal_mul (by positivity),
                abs_pow, ← mul_pow, ← abs_mul, mul_inv_cancel₀ hu0]
              simp
    _ = volume t := (Measure.prod_apply ht).symm

/-- The injectivized substitution: identity on the `u = 0` slice.
Globally injective and surjective; agrees with `scaleBlock` off the
null slice. -/
private noncomputable def scaleBlockInj (m : ℕ) :
    ℝ × (Fin m → ℝ) → ℝ × (Fin m → ℝ) :=
  fun p => if p.1 = 0 then p else scaleBlock m p

private theorem measurable_scaleBlockInj (m : ℕ) :
    Measurable (scaleBlockInj m) :=
  Measurable.ite (measurable_fst (measurableSet_singleton 0))
    measurable_id (measurable_scaleBlock m)

private theorem scaleBlockInj_injective (m : ℕ) :
    Function.Injective (scaleBlockInj m) := by
  rintro ⟨u, y⟩ ⟨v, z⟩ h
  have hfst : u = v := by
    have h1 := congrArg Prod.fst h
    simpa [scaleBlockInj, scaleBlock, apply_ite Prod.fst] using h1
  subst hfst
  by_cases hu : u = 0
  · simpa [scaleBlockInj, hu] using h
  · have hsnd := congrArg Prod.snd h
    simp only [scaleBlockInj, ite_eq_right hu, scaleBlock] at hsnd
    exact Prod.ext rfl (smul_right_injective _ hu hsnd)

private theorem scaleBlockInj_surjective (m : ℕ) :
    Function.Surjective (scaleBlockInj m) := by
  rintro ⟨u, z⟩
  by_cases hu : u = 0
  · exact ⟨(u, z), by simp [scaleBlockInj, hu]⟩
  · refine ⟨(u, u⁻¹ • z), ?_⟩
    simp [scaleBlockInj, scaleBlock, hu, smul_smul]

/-- The `u = 0` slice is null. -/
private theorem volume_slice_zero (m : ℕ) :
    volume {p : ℝ × (Fin m → ℝ) | p.1 = 0} = 0 := by
  have : {p : ℝ × (Fin m → ℝ) | p.1 = 0} = {(0 : ℝ)} ×ˢ univ := by
    ext p
    simp [Set.mem_prod]
  rw [this, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_singleton, zero_mul]

private theorem map_scaleBlockInj_withDensity (m : ℕ) :
    Measure.map (scaleBlockInj m) (volume.withDensity (scaleDensity m)) =
      volume := by
  have hcongr : Measure.map (scaleBlockInj m)
      (volume.withDensity (scaleDensity m)) =
      Measure.map (scaleBlock m) (volume.withDensity (scaleDensity m)) := by
    refine Measure.map_congr ?_
    refine Filter.EventuallyEq.filter_mono ?_
      ((withDensity_absolutelyContinuous _ _).ae_le)
    filter_upwards [compl_mem_ae_iff.mpr (volume_slice_zero m)] with p hp
    simp only [scaleBlockInj, ite_eq_right (by simpa using hp)]
  rw [hcongr, map_scaleBlock_withDensity m]

/-- The spectator-extended substitution: the canonical atom times the
identity on a spectator factor. -/
private noncomputable def scaleBlockProd (m : ℕ) (W : Type*) :
    (ℝ × (Fin m → ℝ)) × W → (ℝ × (Fin m → ℝ)) × W :=
  Prod.map (scaleBlock m) id

/-- The spectator-extended injectivization. -/
private noncomputable def scaleBlockInjProd (m : ℕ) (W : Type*) :
    (ℝ × (Fin m → ℝ)) × W → (ℝ × (Fin m → ℝ)) × W :=
  Prod.map (scaleBlockInj m) id

/-- The spectator-extended density. -/
private noncomputable def scaleDensityProd (m : ℕ) (W : Type*) :
    (ℝ × (Fin m → ℝ)) × W → ℝ≥0∞ :=
  fun p => scaleDensity m p.1

variable {W : Type*} [MeasureSpace W] [SigmaFinite (volume : Measure W)]

omit [MeasureSpace W] [SigmaFinite (volume : Measure W)] in
private theorem measurable_scaleDensityProd (m : ℕ) [MeasurableSpace W] :
    Measurable (scaleDensityProd m W) :=
  (measurable_scaleDensity m).comp measurable_fst

private theorem map_scaleBlockInjProd_withDensity (m : ℕ) :
    Measure.map (scaleBlockInjProd m W)
      (volume.withDensity (scaleDensityProd m W)) = volume := by
  have h1 : (volume : Measure ((ℝ × (Fin m → ℝ)) × W)).withDensity
      (scaleDensityProd m W) =
      ((volume : Measure (ℝ × (Fin m → ℝ))).withDensity
        (scaleDensity m)).prod volume := by
    rw [show (volume : Measure ((ℝ × (Fin m → ℝ)) × W)) =
      (volume : Measure (ℝ × (Fin m → ℝ))).prod volume from rfl]
    exact MeasureTheory.withDensity_fst_prod (measurable_scaleDensity m)
  rw [scaleBlockInjProd, h1,
    ← Measure.map_prod_map _ _ (measurable_scaleBlockInj m) measurable_id,
    map_scaleBlockInj_withDensity m, Measure.map_id]
  rfl

omit [SigmaFinite (volume : Measure W)] in
private theorem measurable_scaleBlockProd (m : ℕ) :
    Measurable (scaleBlockProd m W) :=
  ((measurable_scaleBlock m).comp measurable_fst).prodMk measurable_snd

/-- The product slice is null. -/
private theorem volume_sliceProd_zero (m : ℕ) :
    volume {p : (ℝ × (Fin m → ℝ)) × W | p.1.1 = 0} = 0 := by
  have : {p : (ℝ × (Fin m → ℝ)) × W | p.1.1 = 0} =
      {q : ℝ × (Fin m → ℝ) | q.1 = 0} ×ˢ Set.univ := by
    ext p
    simp [Set.mem_prod]
  rw [this, show (volume : Measure ((ℝ × (Fin m → ℝ)) × W)) =
    (volume : Measure (ℝ × (Fin m → ℝ))).prod volume from rfl,
    Measure.prod_prod, volume_slice_zero m, zero_mul]

/-- **The spectator-extended block-scaling atom**. -/
private theorem transportsToOn_scaleBlockProd (m : ℕ) :
    TransportsToOn volume volume Set.univ (scaleBlockProd m W)
      (scaleDensityProd m W) := by
  have hemb : MeasurableEmbedding (scaleBlockInjProd m W) :=
    MeasurableEmbedding.prodMap
      ((measurable_scaleBlockInj m).measurableEmbedding
        (scaleBlockInj_injective m))
      MeasurableEmbedding.id
  have hbase : TransportsToOn volume volume Set.univ
      (scaleBlockInjProd m W) (scaleDensityProd m W) := by
    refine TransportsToOn.of_measurableEmbedding hemb
      (measurable_scaleDensityProd m) ?_
    rw [Set.range_eq_univ.mpr
      (show Function.Surjective (scaleBlockInjProd m W) from
        (scaleBlockInj_surjective m).prodMap Function.surjective_id),
      Measure.restrict_univ]
    exact map_scaleBlockInjProd_withDensity m
  refine TransportsToOn.congr_fun_ae hbase (measurable_scaleBlockProd m)
    (volume_sliceProd_zero m) (fun p hp => ?_) ?_ ?_
  · have hp0 : p.1.1 ≠ 0 := hp
    simp only [scaleBlockInjProd, scaleBlockProd, Prod.map, scaleBlockInj,
      ite_eq_right hp0]
  · refine measure_mono_null (fun q hq => ?_) (volume_sliceProd_zero m)
    obtain ⟨p, hp, rfl⟩ := hq
    have hp0 : p.1.1 = 0 := hp
    simp only [scaleBlockInjProd, Prod.map, Set.mem_ofPred_eq, scaleBlockInj,
      ite_eq_left hp0]
    exact hp0
  · refine measure_mono_null (fun q hq => ?_) (volume_sliceProd_zero m)
    obtain ⟨p, hp, rfl⟩ := hq
    exact hp

/-! ## The shear atom -/

/-- The shear `(w, y) ↦ (w, y + c w)` with an arbitrary source space, as a measurable
equivalence (the inverse subtracts). -/
private def shearEquivGen (W : Type*) [MeasurableSpace W] {m : ℕ}
    (c : W → Fin m → ℝ) (hc : Measurable c) :
    (W × (Fin m → ℝ)) ≃ᵐ (W × (Fin m → ℝ)) where
  toFun p := (p.1, p.2 + c p.1)
  invFun p := (p.1, p.2 - c p.1)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun :=
    measurable_fst.prodMk (measurable_snd.add (hc.comp measurable_fst))
  measurable_invFun :=
    measurable_fst.prodMk (measurable_snd.sub (hc.comp measurable_fst))

/-- Shears preserve volume: skew product over the identity with per-fiber translations. -/
private theorem measurePreserving_shearEquivGen (W : Type*) [MeasureSpace W]
    [SFinite (volume : Measure W)] {m : ℕ} (c : W → Fin m → ℝ)
    (hc : Measurable c) :
    MeasurePreserving (shearEquivGen W c hc) volume volume :=
  MeasurePreserving.skew_product (MeasurePreserving.id _)
    (measurable_snd.add (hc.comp measurable_fst))
    (Filter.Eventually.of_forall fun u =>
      (measurePreserving_add_right volume (c u)).map_eq)

/-! ## The marked transports -/

variable {d n : ℕ}

/-- **The marked-scaling transport**: the pivot coordinate scales the
marked block, with density `|x u|^n`, on the whole space. -/
theorem transportsToOn_markedScale (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) :
    TransportsToOn volume volume Set.univ (markedScale u b)
      (markedDensity u n) := by
  classical
  have h := TransportsToOn.conj (markScaleSplit u b hbu)
    (measurePreserving_markScaleSplit u b hbu)
    (transportsToOn_scaleBlockProd (W := MarkCompl u b → ℝ) n)
  rw [Set.preimage_univ] at h
  have hfun : (fun x => (markScaleSplit u b hbu).symm
      (scaleBlockProd n (MarkCompl u b → ℝ) (markScaleSplit u b hbu x))) =
      markedScale u b := by
    funext x j
    by_cases hj : j = u
    · rw [hj]
      rw [show (scaleBlockProd n (MarkCompl u b → ℝ)
          (markScaleSplit u b hbu x)) =
          ((x u, fun i => x u * x (b i)), fun s => x s.1) from rfl,
        markScaleSplit_symm_pivot, markedScale,
        ite_eq_right (fun h' : ∃ i, b i = u => hbu h'.choose h'.choose_spec)]
    · by_cases hj' : ∃ i, b i = j
      · obtain ⟨i, rfl⟩ := hj'
        rw [show (scaleBlockProd n (MarkCompl u b → ℝ)
            (markScaleSplit u b hbu x)) =
            ((x u, fun i' => x u * x (b i')), fun s => x s.1) from rfl,
          markScaleSplit_symm_block, markedScale, ite_eq_left ⟨i, rfl⟩]
      · have hs := markScaleSplit_symm_spec u b hbu
          ((x u, fun i' => x u * x (b i')), fun s => x s.1)
          ⟨j, hj, fun i hi => hj' ⟨i, hi⟩⟩
        rw [show (scaleBlockProd n (MarkCompl u b → ℝ)
            (markScaleSplit u b hbu x)) =
            ((x u, fun i' => x u * x (b i')), fun s => x s.1) from rfl,
          hs, markedScale, ite_eq_right hj']
  have hden : (fun x => scaleDensityProd n (MarkCompl u b → ℝ)
      (markScaleSplit u b hbu x)) = markedDensity u n := rfl
  rw [hfun, hden] at h
  exact h

/-- **The marked-shear transport**: unit density. -/
theorem transportsToOn_markedShear (b : Fin n ↪ Fin d)
    (c : (TargetCompl b → ℝ) → Fin n → ℝ) (hc : Measurable c) :
    TransportsToOn volume volume Set.univ (markedShear b c)
      fun _ => 1 := by
  classical
  have h := TransportsToOn.conj (shearSplit b)
    (measurePreserving_shearSplit b)
    ((shearEquivGen (TargetCompl b → ℝ) c hc).transportsToOn_one
      (measurePreserving_shearEquivGen _ c hc))
  rw [Set.preimage_univ] at h
  have hfun : (fun x => (shearSplit b).symm
      (shearEquivGen (TargetCompl b → ℝ) c hc (shearSplit b x))) =
      markedShear b c := by
    funext x j
    by_cases hj : ∃ i, b i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [show (shearEquivGen (TargetCompl b → ℝ) c hc (shearSplit b x)) =
          ((fun s => x s.1), (fun i' => x (b i')) + c fun s => x s.1)
          from rfl,
        shearSplit_symm_target, markedShear]
      have hbi : ∃ i', b i' = b i := ⟨i, rfl⟩
      rw [dite_eq_left hbi]
      change x (b i) + c (fun s => x s.1) i = _
      rw [b.injective hbi.choose_spec]
    · have hs := shearSplit_symm_compl b
        ((fun s => x s.1), (fun i' => x (b i')) + c fun s => x s.1)
        ⟨j, fun i hi => hj ⟨i, hi⟩⟩
      rw [show (shearEquivGen (TargetCompl b → ℝ) c hc (shearSplit b x)) =
          ((fun s => x s.1), (fun i' => x (b i')) + c fun s => x s.1)
          from rfl, hs, markedShear, dite_eq_right hj]
  rw [hfun] at h
  exact h

end Analytic
