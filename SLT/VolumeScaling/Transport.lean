/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic

/-!
# Transporting volume-scaling exponents across spaces

`HasLLCExponentsOn` is a Θ-statement about the real-valued function `sublevelVol μ K f`;
anything that identifies two such functions up to a positive constant identifies the exponent
predicates. This file records that observation three ways:

* `hasLLCExponentsOn_congr_const_mul` — eventually-equal sublevel volumes up to a positive
  constant give the same exponents (iff);
* `MeasurePreserving.hasLLCExponentsOn_comp` — pulling back along a measure-preserving
  `MeasurableEquiv` preserves exponents exactly (the chart-side coordinate reindexings are of
  this kind);
* `hasLLCExponentsOn_comp_smul_measurableEquiv` — same with the pushforward only a positive
  finite multiple of the target measure (a linear equivalence with non-unit determinant), and
  its basis-free form for a continuous linear equivalence between Haar-measured spaces.

The monomial read-offs (`MonomialReadOff`, `CubeRescale`) and the power
composition (`PowerComp`) transfer their statements along coordinate reindexings with these.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal NNReal

namespace SingularLearningTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {K : Set α} {K' : Set β}
  {f : α → ℝ} {g : β → ℝ} {lam theta : ℝ}

/-- Θ-statements are invariant under eventual equality on the left. -/
theorem _root_.Filter.EventuallyEq.isTheta_congr_left {ι F G : Type*} [Norm F] [Norm G]
    {l : Filter ι}
    {f g : ι → F} {h : ι → G} (hfg : f =ᶠ[l] g) :
    f =Θ[l] h ↔ g =Θ[l] h :=
  ⟨fun H => ⟨hfg.symm.trans_isBigO H.1, H.2.trans_eventuallyEq hfg⟩,
   fun H => ⟨hfg.trans_isBigO H.1, H.2.trans_eventuallyEq hfg.symm⟩⟩

/-- If two localized sublevel-volume functions eventually agree up to a
positive constant, the exponent predicates agree. -/
theorem hasLLCExponentsOn_congr_const_mul {c : ℝ} (hc : 0 < c)
    (hV : sublevelVol μ K f =ᶠ[𝓝[>] (0 : ℝ)]
      fun t => c * sublevelVol ν K' g t) :
    HasLLCExponentsOn μ K f lam theta ↔
      HasLLCExponentsOn ν K' g lam theta := by
  rw [HasLLCExponentsOn, HasLLCExponentsOn, Filter.EventuallyEq.isTheta_congr_left hV,
    isTheta_const_mul_left hc.ne']

/-- Pulling back along a measure-preserving `MeasurableEquiv` preserves the
sublevel volumes exactly. -/
theorem sublevelVol_comp_measurePreserving (T : α ≃ᵐ β)
    (hT : MeasurePreserving T μ ν) (K' : Set β) (g : β → ℝ) (t : ℝ) :
    sublevelVol μ (T ⁻¹' K') (fun x => g (T x)) t = sublevelVol ν K' g t := by
  rw [sublevelVol, sublevelVol,
    show (T ⁻¹' K') ∩ {x | g (T x) ≤ t} = T ⁻¹' (K' ∩ {y | g y ≤ t}) from rfl,
    ← MeasurableEquiv.map_apply T, hT.map_eq]

/-- Weighted sublevel volumes pull back exactly along a
measure-preserving `MeasurableEquiv`, the weight composing with the
map (preimage form: the source-side localization is `T ⁻¹' A`). -/
theorem sublevelVol_withDensity_comp_measurePreserving (T : α ≃ᵐ β)
    (hT : MeasurePreserving T μ ν) {w : β → ℝ≥0∞} {A : Set β}
    (hA : MeasurableSet A) {g : β → ℝ} (hg : Measurable g) (ε : ℝ) :
    sublevelVol (μ.withDensity fun x => w (T x)) (T ⁻¹' A)
      (fun x => g (T x)) ε
      = sublevelVol (ν.withDensity w) A g ε := by
  rw [sublevelVol, sublevelVol]
  congr 1
  have hAg : MeasurableSet (A ∩ {y | g y ≤ ε}) :=
    hA.inter (measurableSet_le hg measurable_const)
  rw [show (T ⁻¹' A) ∩ {x | g (T x) ≤ ε}
      = T ⁻¹' (A ∩ {y | g y ≤ ε}) from rfl,
    withDensity_apply _ (T.measurable hAg), withDensity_apply _ hAg]
  have h := hT.setLIntegral_comp_emb T.measurableEmbedding w
    (T ⁻¹' (A ∩ {y | g y ≤ ε}))
  rwa [Set.image_preimage_eq _ T.surjective] at h

/-- **The source-map squeeze**: when the preimage of the localization
set is sandwiched between two sets, the weighted sublevel volume is
sandwiched between the substituted volumes on those sets.  In the
applications `T` is a shear (measure-preserving, fixing the pivot so
the scale weight composes to itself), `A` a box, and the sandwiching
sets two centered boxes. -/
theorem sublevelVol_squeeze_of_preimage (T : α ≃ᵐ β)
    (hT : MeasurePreserving T μ ν) {w : β → ℝ≥0∞} {A : Set β}
    (hA : MeasurableSet A) {g : β → ℝ} (hg : Measurable g)
    {Bs Bb : Set α} (hsmall : Bs ⊆ T ⁻¹' A) (hbig : T ⁻¹' A ⊆ Bb)
    (hfin : (μ.withDensity fun x => w (T x)) Bb ≠ ⊤) (ε : ℝ) :
    sublevelVol (μ.withDensity fun x => w (T x)) Bs
        (fun x => g (T x)) ε
      ≤ sublevelVol (ν.withDensity w) A g ε ∧
    sublevelVol (ν.withDensity w) A g ε
      ≤ sublevelVol (μ.withDensity fun x => w (T x)) Bb
        (fun x => g (T x)) ε := by
  rw [← sublevelVol_withDensity_comp_measurePreserving T hT hA hg ε]
  have hfinA : (μ.withDensity fun x => w (T x)) (T ⁻¹' A) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono hbig)
  exact ⟨sublevelVol_mono_set hsmall hfinA _ ε,
    sublevelVol_mono_set hbig hfin _ ε⟩

/-- **Cross-space transport, measure-preserving case.** Pulling back along a
measure-preserving `MeasurableEquiv` preserves the volume-scaling
exponents (an iff, no constants moved). -/
theorem _root_.MeasureTheory.MeasurePreserving.hasLLCExponentsOn_comp (T : α ≃ᵐ β)
    (hT : MeasurePreserving T μ ν) :
    HasLLCExponentsOn μ (T ⁻¹' K') (fun x => g (T x)) lam theta ↔
      HasLLCExponentsOn ν K' g lam theta := by
  rw [HasLLCExponentsOn, HasLLCExponentsOn,
    funext (sublevelVol_comp_measurePreserving T hT K' g)]

/-- **Cross-space transport, constant-Jacobian case.** If the pushforward of
`μ` along a `MeasurableEquiv` is a positive finite multiple of `ν` (a linear
equivalence between finite-dimensional spaces, say), pulling back preserves
the volume-scaling exponents. -/
theorem hasLLCExponentsOn_comp_smul_measurableEquiv (T : α ≃ᵐ β)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hmap : Measure.map T μ = c • ν) :
    HasLLCExponentsOn μ (T ⁻¹' K') (fun x => g (T x)) lam theta ↔
      HasLLCExponentsOn ν K' g lam theta := by
  refine hasLLCExponentsOn_congr_const_mul
    (c := c.toReal) (ENNReal.toReal_pos hc0 hctop)
    (Eventually.of_forall fun t => ?_)
  simp only [sublevelVol]
  rw [show (T ⁻¹' K') ∩ {x | g (T x) ≤ t} = T ⁻¹' (K' ∩ {y | g y ≤ t}) from rfl,
    ← MeasurableEquiv.map_apply T, hmap, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul]

section LinearEquiv

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
  [(volume : Measure F).IsAddHaarMeasure] [FiniteDimensional ℝ F]

/-- **Cross-space transport along a continuous linear equivalence**
(basis-free). The pushforward of one Haar volume along `L`
is a Haar measure, hence a positive finite multiple of the other Haar
volume — the multiple is never computed. -/
theorem hasLLCExponentsOn_comp_continuousLinearEquiv (L : E ≃L[ℝ] F)
    (K' : Set F) (g : F → ℝ) {lam theta : ℝ} :
    HasLLCExponentsOn volume (L ⁻¹' K') (fun x => g (L x)) lam theta ↔
      HasLLCExponentsOn volume K' g lam theta := by
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (volume.map L) (volume : Measure F)
  have hmap : volume.map (L.toHomeomorph.toMeasurableEquiv : E ≃ᵐ F)
      = (((volume.map L).addHaarScalarFactor volume : ℝ≥0) : ℝ≥0∞) • volume :=
    Measure.isAddLeftInvariant_eq_smul (volume.map L) volume
  exact hasLLCExponentsOn_comp_smul_measurableEquiv
    (L.toHomeomorph.toMeasurableEquiv : E ≃ᵐ F)
    (by exact_mod_cast hpos.ne') ENNReal.coe_ne_top hmap

end LinearEquiv

end SingularLearningTheory
