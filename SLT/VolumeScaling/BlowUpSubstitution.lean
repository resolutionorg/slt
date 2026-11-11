/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The one-variable blow-up substitution

The measure identity behind the blow-up chart lemma: the scaling chart
`Φ ((u, a), x) = ((u, a), u·x)` carries the `|u|`-weighted measure on a set `K` to the
unweighted measure on `Φ '' K`. Stated with an s-finite base measure `μ` on the `(u, a)`-factor,
so that a codimension-`q` chart is a routine `(q−1)`-fold composition of one-variable
substitutions: each application absorbs one `|u|` factor into `μ`. The statements need only
measurable sets (no compactness anywhere).

Corollaries transfer `sublevelVol` and `HasLLCOn`/`HasLLCExponentsOn` across the scaling map.
Nothing else in the library uses `chartScale` or `chartScaleVec`: the read-offs pass from a
chart to its image through the transport identity
(`TransportsToOn.hasLLCExponentsOn_image_inter` in `ChartSandwich`), and `CubeRescale` uses
only the density-composition lemma `SLT.MeasureTheory.Measure.map_withDensity_comp`.
-/

@[expose] public section

open Filter MeasureTheory Set Asymptotics
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α]

/-- Pushforward commutes with a pulled-back density: the generic transport
lemma for densities accumulated by earlier blow-up stages (when a later
chart rescales the old exceptional coordinate, its `|u|`-power density
transports through the new chart by this lemma). A copy of resolution-common's
`MeasureTheory.Measure.map_withDensity_comp`, kept until slt requires resolution-common. -/
theorem _root_.SLT.MeasureTheory.Measure.map_withDensity_comp {β γ : Type*}
    [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure β) {f : β → γ} (hf : Measurable f) {g : γ → ℝ≥0∞}
    (hg : Measurable g) :
    Measure.map f (ν.withDensity (g ∘ f)) = (Measure.map f ν).withDensity g := by
  ext S hS
  rw [Measure.map_apply hf hS, withDensity_apply _ (hf hS), withDensity_apply _ hS,
    setLIntegral_map hS hg hf]
  rfl

/-- The one-variable scaling chart: the last coordinate is scaled by the
exceptional coordinate `u` (the first coordinate of the parametric
factor); everything else is a spectator. -/
def chartScale (p : (ℝ × α) × ℝ) : (ℝ × α) × ℝ :=
  (p.1, p.1.1 * p.2)

theorem measurable_chartScale : Measurable (chartScale (α := α)) :=
  measurable_fst.prodMk ((measurable_fst.fst).mul measurable_snd)

omit [MeasurableSpace α] in
@[simp] theorem chartScale_apply (ua : ℝ × α) (x : ℝ) :
    chartScale (ua, x) = (ua, ua.1 * x) := rfl

/-- 1D slice form of the substitution: scaling by `u` trades a `|u|`
weight for the image set. Stated in tested form to keep all
`map`/`restrict` plumbing out of the Fubini assembly; the `u = 0` slice
vanishes on both sides. -/
theorem _root_.ofReal_abs_mul_volume_preimage_inter (u : ℝ) {A T : Set ℝ}
    (hA : MeasurableSet A) (hT : MeasurableSet T) :
    ENNReal.ofReal |u| * volume ((u * ·) ⁻¹' T ∩ A)
      = volume ((u * ·) '' A ∩ T) := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [abs_zero, ENNReal.ofReal_zero, zero_mul]
    refine (measure_mono_null (t := {(0 : ℝ)}) (fun y hy => ?_)
      Real.volume_singleton).symm
    obtain ⟨⟨x, -, rfl⟩, -⟩ := hy
    simp
  · have himg : (u * ·) '' A = (u⁻¹ * ·) ⁻¹' A := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [inv_mul_cancel_left₀ hu] using hx
      · intro hy
        exact ⟨u⁻¹ * y, hy, mul_inv_cancel_left₀ hu y⟩
    have hW : MeasurableSet ((u * ·) '' A ∩ T) := by
      rw [himg]
      exact (hA.preimage (measurable_const_mul _)).inter hT
    have happ : volume ((u * ·) ⁻¹' ((u * ·) '' A ∩ T))
        = (ENNReal.ofReal |u⁻¹| • volume) ((u * ·) '' A ∩ T) := by
      rw [← Measure.map_apply (measurable_const_mul u) hW,
        Real.map_volume_mul_left hu]
    have hpre : (u * ·) ⁻¹' ((u * ·) '' A ∩ T) = (u * ·) ⁻¹' T ∩ A := by
      rw [preimage_inter, himg, ← preimage_comp]
      have : (u⁻¹ * ·) ∘ (u * ·) = id := by
        funext x
        simp [inv_mul_cancel_left₀ hu]
      rw [this, preimage_id, inter_comm]
    rw [hpre] at happ
    rw [happ, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul (abs_nonneg u), abs_inv,
      mul_inv_cancel₀ (abs_ne_zero.mpr hu), ENNReal.ofReal_one, one_mul]

/-- Indicator of a product-space set along a fixed first coordinate. -/
private theorem indicator_prodMk {β γ : Type*} (E : Set (β × γ))
    (w : β × γ → ℝ≥0∞) (b : β) (c : γ) :
    E.indicator w (b, c) = (Prod.mk b ⁻¹' E).indicator (fun y => w (b, y)) c := by
  by_cases h : (b, c) ∈ E
  · rw [indicator_of_mem h,
      indicator_of_mem (show c ∈ Prod.mk b ⁻¹' E from h)]
  · rw [indicator_of_notMem h,
      indicator_of_notMem (show c ∉ Prod.mk b ⁻¹' E from h)]

omit [MeasurableSpace α] in
/-- Fiber of the chart image over a fixed `(u, a)`: it is the scaled fiber
of the source set. -/
theorem preimage_prodMk_chartScale_image (K : Set ((ℝ × α) × ℝ)) (ua : ℝ × α) :
    Prod.mk ua ⁻¹' (chartScale '' K) = (ua.1 * ·) '' (Prod.mk ua ⁻¹' K) := by
  ext y
  constructor
  · rintro ⟨⟨ua', x⟩, hmem, heq⟩
    injection heq with h1 h2
    subst h1
    exact ⟨x, hmem, h2⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(ua, x), hx, rfl⟩

/-- **The one-variable blow-up substitution** (base-measure-parametric form): the scaling
chart pushes the `|u|`-weighted measure restricted to `K` to the
unweighted measure restricted to the chart image. A codimension-`q`
blow-up chart is a `(q−1)`-fold composition: each substitution absorbs one `|u|`
factor (residual powers live in `μ`). -/
theorem map_chartScale_withDensity_restrict (μ : Measure (ℝ × α))
    {K : Set ((ℝ × α) × ℝ)} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScale '' K)) :
    Measure.map chartScale
        (((μ.prod volume).withDensity (fun p => ENNReal.ofReal |p.1.1|)).restrict K)
      = (μ.prod volume).restrict (chartScale '' K) := by
  ext S hS
  have hpreS : MeasurableSet (chartScale ⁻¹' S) := measurable_chartScale hS
  rw [Measure.map_apply measurable_chartScale hS,
    Measure.restrict_apply hpreS,
    withDensity_apply _ (hpreS.inter hK),
    Measure.restrict_apply hS,
    Measure.prod_apply (hS.inter hImg),
    ← lintegral_indicator (hpreS.inter hK),
    lintegral_prod _ (((((measurable_fst.fst).abs).ennreal_ofReal).indicator
      (hpreS.inter hK)).aemeasurable)]
  refine lintegral_congr fun ua => ?_
  have hSf : MeasurableSet (Prod.mk ua ⁻¹' S) := hS.preimage measurable_prodMk_left
  have hKf : MeasurableSet (Prod.mk ua ⁻¹' K) := hK.preimage measurable_prodMk_left
  have hfib : ∀ x : ℝ,
      (chartScale ⁻¹' S ∩ K).indicator (fun p => ENNReal.ofReal |p.1.1|) (ua, x)
        = ((ua.1 * ·) ⁻¹' (Prod.mk ua ⁻¹' S) ∩ Prod.mk ua ⁻¹' K).indicator
            (fun _ => ENNReal.ofReal |ua.1|) x := by
    intro x
    rw [indicator_prodMk]
    rfl
  rw [funext hfib,
    lintegral_indicator_const ((hSf.preimage (measurable_const_mul _)).inter hKf),
    preimage_inter, preimage_prodMk_chartScale_image,
    ofReal_abs_mul_volume_preimage_inter ua.1 hKf hSf, inter_comm]

/-- Sublevel volumes transfer across the one-variable substitution: the unweighted
sublevel volume of `f` on the image equals the `|u|`-weighted sublevel
volume of the pullback `f ∘ chartScale` on the source. -/
theorem sublevelVol_chartScale (μ : Measure (ℝ × α))
    {K : Set ((ℝ × α) × ℝ)} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScale '' K))
    {f : (ℝ × α) × ℝ → ℝ} (hf : Measurable f) (ε : ℝ) :
    sublevelVol (μ.prod volume) (chartScale '' K) f ε
      = sublevelVol
          ((μ.prod volume).withDensity (fun p => ENNReal.ofReal |p.1.1|)) K
          (f ∘ chartScale) ε := by
  have hSε : MeasurableSet {p : (ℝ × α) × ℝ | f p ≤ ε} :=
    hf measurableSet_Iic
  have h := congrArg (fun ν : Measure ((ℝ × α) × ℝ) => ν {p | f p ≤ ε})
    (map_chartScale_withDensity_restrict μ hK hImg)
  -- evaluate the measure identity on the sublevel set
  rw [Measure.map_apply measurable_chartScale hSε,
    Measure.restrict_apply (measurable_chartScale hSε),
    Measure.restrict_apply hSε] at h
  unfold sublevelVol
  rw [inter_comm (chartScale '' K), ← h, inter_comm]
  rfl

/-- `HasLLCOn` transfers across the one-variable substitution. -/
theorem hasLLCOn_chartScale_iff (μ : Measure (ℝ × α))
    {K : Set ((ℝ × α) × ℝ)} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScale '' K))
    {f : (ℝ × α) × ℝ → ℝ} (hf : Measurable f) {lam theta c : ℝ} :
    HasLLCOn (μ.prod volume) (chartScale '' K) f lam theta c
      ↔ HasLLCOn
          ((μ.prod volume).withDensity (fun p => ENNReal.ofReal |p.1.1|)) K
          (f ∘ chartScale) lam theta c := by
  unfold HasLLCOn
  rw [funext fun ε => congrArg (· / llcScale lam theta ε)
    (sublevelVol_chartScale μ hK hImg hf ε)]

/-- `HasLLCExponentsOn` transfers across the one-variable substitution. -/
theorem hasLLCExponentsOn_chartScale_iff (μ : Measure (ℝ × α))
    {K : Set ((ℝ × α) × ℝ)} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScale '' K))
    {f : (ℝ × α) × ℝ → ℝ} (hf : Measurable f) {lam theta : ℝ} :
    HasLLCExponentsOn (μ.prod volume) (chartScale '' K) f lam theta
      ↔ HasLLCExponentsOn
          ((μ.prod volume).withDensity (fun p => ENNReal.ofReal |p.1.1|)) K
          (f ∘ chartScale) lam theta := by
  unfold HasLLCExponentsOn
  rw [funext fun ε => sublevelVol_chartScale μ hK hImg hf ε]

/-! ## The codimension-`q` chart: all scaled coordinates at once

`chartScaleVec` scales an `n`-dimensional block by the exceptional
coordinate; the Jacobian factor is `|u| ^ n`. Same Fubini skeleton as the
one-variable substitution; the slice lemma needs no case split (`addHaar_smul` is
unconditional, and `image_inter_preimage` needs no injectivity). -/

section Vec

variable {n : ℕ}

/-- The codimension-`(n+1)` scaling chart: an `n`-dimensional coordinate
block is scaled by the exceptional coordinate `u`. -/
def chartScaleVec (p : (ℝ × α) × (Fin n → ℝ)) : (ℝ × α) × (Fin n → ℝ) :=
  (p.1, p.1.1 • p.2)

theorem measurable_chartScaleVec : Measurable (chartScaleVec (α := α) (n := n)) :=
  measurable_fst.prodMk ((measurable_fst.fst).smul measurable_snd)

omit [MeasurableSpace α] in
@[simp] theorem chartScaleVec_apply (ua : ℝ × α) (x : Fin n → ℝ) :
    chartScaleVec (ua, x) = (ua, ua.1 • x) := rfl

/-- `n`-dimensional slice form of the substitution: scaling a block by `u`
trades a `|u| ^ n` weight for the image set. No case split: both
`Set.image_inter_preimage` and `Measure.addHaar_smul` are unconditional. -/
theorem _root_.ofReal_abs_pow_mul_volume_preimage_inter (u : ℝ) {A T : Set (Fin n → ℝ)} :
    ENNReal.ofReal (|u| ^ n) * volume ((u • ·) ⁻¹' T ∩ A)
      = volume ((u • ·) '' A ∩ T) := by
  rw [← Set.image_inter_preimage, Set.image_smul, Measure.addHaar_smul,
    Module.finrank_fin_fun, abs_pow, inter_comm]

omit [MeasurableSpace α] in
/-- Fiber of the vector chart image over a fixed `(u, a)`. -/
theorem preimage_prodMk_chartScaleVec_image (K : Set ((ℝ × α) × (Fin n → ℝ)))
    (ua : ℝ × α) :
    Prod.mk ua ⁻¹' (chartScaleVec '' K) = (ua.1 • ·) '' (Prod.mk ua ⁻¹' K) := by
  ext y
  constructor
  · rintro ⟨⟨ua', x⟩, hmem, heq⟩
    injection heq with h1 h2
    subst h1
    exact ⟨x, hmem, h2⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(ua, x), hx, rfl⟩

/-- **The codimension-`(n+1)` chart lemma**: the block-scaling
chart pushes the `|u| ^ n`-weighted measure restricted to `K` to the
unweighted measure restricted to the chart image. Base-measure-parametric
as in the one-variable substitution: residual densities from earlier blow-up stages live in
`μ`. -/
theorem map_chartScaleVec_withDensity_restrict (μ : Measure (ℝ × α))
    {K : Set ((ℝ × α) × (Fin n → ℝ))} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScaleVec '' K)) :
    Measure.map chartScaleVec
        (((μ.prod volume).withDensity
          (fun p => ENNReal.ofReal (|p.1.1| ^ n))).restrict K)
      = (μ.prod volume).restrict (chartScaleVec '' K) := by
  ext S hS
  have hpreS : MeasurableSet (chartScaleVec ⁻¹' S) := measurable_chartScaleVec hS
  rw [Measure.map_apply measurable_chartScaleVec hS,
    Measure.restrict_apply hpreS,
    withDensity_apply _ (hpreS.inter hK),
    Measure.restrict_apply hS,
    Measure.prod_apply (hS.inter hImg),
    ← lintegral_indicator (hpreS.inter hK),
    lintegral_prod _ ((((((measurable_fst.fst).abs).pow_const n).ennreal_ofReal).indicator
      (hpreS.inter hK)).aemeasurable)]
  refine lintegral_congr fun ua => ?_
  have hSf : MeasurableSet (Prod.mk ua ⁻¹' S) := hS.preimage measurable_prodMk_left
  have hKf : MeasurableSet (Prod.mk ua ⁻¹' K) := hK.preimage measurable_prodMk_left
  have hfib : ∀ x : Fin n → ℝ,
      (chartScaleVec ⁻¹' S ∩ K).indicator
          (fun p => ENNReal.ofReal (|p.1.1| ^ n)) (ua, x)
        = ((ua.1 • ·) ⁻¹' (Prod.mk ua ⁻¹' S) ∩ Prod.mk ua ⁻¹' K).indicator
            (fun _ => ENNReal.ofReal (|ua.1| ^ n)) x := by
    intro x
    rw [indicator_prodMk]
    rfl
  rw [funext hfib,
    lintegral_indicator_const ((hSf.preimage (measurable_const_smul _)).inter hKf),
    preimage_inter, preimage_prodMk_chartScaleVec_image,
    ofReal_abs_pow_mul_volume_preimage_inter ua.1, inter_comm]

/-- Sublevel volumes transfer across the codimension-`(n+1)` chart. -/
theorem sublevelVol_chartScaleVec (μ : Measure (ℝ × α))
    {K : Set ((ℝ × α) × (Fin n → ℝ))} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScaleVec '' K))
    {f : (ℝ × α) × (Fin n → ℝ) → ℝ} (hf : Measurable f) (ε : ℝ) :
    sublevelVol (μ.prod volume) (chartScaleVec '' K) f ε
      = sublevelVol
          ((μ.prod volume).withDensity (fun p => ENNReal.ofReal (|p.1.1| ^ n))) K
          (f ∘ chartScaleVec) ε := by
  have hSε : MeasurableSet {p : (ℝ × α) × (Fin n → ℝ) | f p ≤ ε} :=
    hf measurableSet_Iic
  have h := congrArg (fun ν : Measure ((ℝ × α) × (Fin n → ℝ)) => ν {p | f p ≤ ε})
    (map_chartScaleVec_withDensity_restrict μ hK hImg)
  -- evaluate the measure identity on the sublevel set
  rw [Measure.map_apply measurable_chartScaleVec hSε,
    Measure.restrict_apply (measurable_chartScaleVec hSε),
    Measure.restrict_apply hSε] at h
  unfold sublevelVol
  rw [inter_comm (chartScaleVec '' K), ← h, inter_comm]
  rfl

/-- `HasLLCOn` transfers across the codimension-`(n+1)` chart. -/
theorem hasLLCOn_chartScaleVec_iff (μ : Measure (ℝ × α))
    {K : Set ((ℝ × α) × (Fin n → ℝ))} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScaleVec '' K))
    {f : (ℝ × α) × (Fin n → ℝ) → ℝ} (hf : Measurable f) {lam theta c : ℝ} :
    HasLLCOn (μ.prod volume) (chartScaleVec '' K) f lam theta c
      ↔ HasLLCOn
          ((μ.prod volume).withDensity (fun p => ENNReal.ofReal (|p.1.1| ^ n))) K
          (f ∘ chartScaleVec) lam theta c := by
  unfold HasLLCOn
  rw [funext fun ε => congrArg (· / llcScale lam theta ε)
    (sublevelVol_chartScaleVec μ hK hImg hf ε)]

/-- `HasLLCExponentsOn` transfers across the codimension-`(n+1)` chart. -/
theorem hasLLCExponentsOn_chartScaleVec_iff (μ : Measure (ℝ × α))
    {K : Set ((ℝ × α) × (Fin n → ℝ))} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScaleVec '' K))
    {f : (ℝ × α) × (Fin n → ℝ) → ℝ} (hf : Measurable f) {lam theta : ℝ} :
    HasLLCExponentsOn (μ.prod volume) (chartScaleVec '' K) f lam theta
      ↔ HasLLCExponentsOn
          ((μ.prod volume).withDensity (fun p => ENNReal.ofReal (|p.1.1| ^ n))) K
          (f ∘ chartScaleVec) lam theta := by
  unfold HasLLCExponentsOn
  rw [funext fun ε => sublevelVol_chartScaleVec μ hK hImg hf ε]

/-- Weighted form of the chart lemma: an arbitrary residual density `g`
(e.g. the accumulated Jacobian factors of earlier blow-up stages) rides
along, pulled back through the chart on the source side. This is the
form suited to carrying densities along a sequence of charts; nothing else
in the library uses it. -/
theorem map_chartScaleVec_withDensity_restrict' (μ : Measure (ℝ × α))
    {K : Set ((ℝ × α) × (Fin n → ℝ))} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScaleVec '' K))
    {g : (ℝ × α) × (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    Measure.map chartScaleVec
        (((μ.prod volume).withDensity
          (fun p => ENNReal.ofReal (|p.1.1| ^ n) * g (chartScaleVec p))).restrict K)
      = ((μ.prod volume).withDensity g).restrict (chartScaleVec '' K) := by
  rw [show (fun p => ENNReal.ofReal (|p.1.1| ^ n) * g (chartScaleVec p))
      = (fun p => ENNReal.ofReal (|p.1.1| ^ n)) * (g ∘ chartScaleVec) from rfl,
    withDensity_mul _ ((((measurable_fst.fst).abs).pow_const n).ennreal_ofReal)
      (hg.comp measurable_chartScaleVec),
    restrict_withDensity hK,
    SLT.MeasureTheory.Measure.map_withDensity_comp _ measurable_chartScaleVec hg,
    map_chartScaleVec_withDensity_restrict μ hK hImg,
    ← restrict_withDensity hImg]

end Vec

end SingularLearningTheory
