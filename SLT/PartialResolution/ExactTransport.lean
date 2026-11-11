/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.PartialResolution.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Local exact measure transport: the calculus

The calculus of the exact transports `TransportsToOn μX μY K φ J` of a chart map. The
`Measure.map`, image-measure, and sublevel forms are derived, not primary
(`map_withDensity_eq`, `image_inter_eq`, `sublevel_eq`). Transports restrict to smaller domains
(`mono_dom`), reweight on the target (`withDensity_target`), are insensitive to changing the map
on a null set with null images (`congr_fun_ae`) and extend across such a set (`mono_ae`), and
compose (`comp`) and conjugate by measure-preserving equivalences (`TransportsToOn.conj`).
Transports arise from measurable embeddings (`of_measurableEmbedding`), from measure-preserving
equivalences (`MeasurePreserving.restrict_image`, `MeasurableEquiv.transportsToOn_one`), and
from a density in the first factor of a product (`withDensity_fst_prod`). Every chart of a
`MonomialChartCover` carries such a transport, and the change-of-variables identity of a partial
resolution produces one (`PartialResolution.transportsToOn`).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Analytic

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z]

namespace TransportsToOn

variable {μX : Measure X} {μY : Measure Y} {μZ : Measure Z}
  {K : Set X} {φ : X → Y} {J : X → ℝ≥0∞}

/-- The image-measure form: the target measure of (test set ∩ image)
is the weighted source measure of the preimage trace. -/
theorem image_inter_eq (h : TransportsToOn μX μY K φ J) {s : Set X}
    (hs : s ⊆ K) {t : Set Y} (ht : MeasurableSet t) :
    μY (t ∩ φ '' s) = ∫⁻ x in φ ⁻¹' t ∩ s, J x ∂μX := by
  have key := h.2.2 s hs (t.indicator fun _ => 1)
    (measurable_const.indicator ht)
  calc μY (t ∩ φ '' s)
      = (μY.restrict (t ∩ φ '' s)) univ := by
        rw [Measure.restrict_apply_univ]
    _ = ∫⁻ y in t ∩ φ '' s, 1 ∂μY := by rw [lintegral_one]
    _ = ∫⁻ y in φ '' s, t.indicator (fun _ => 1) y ∂μY := by
        rw [lintegral_indicator ht, Measure.restrict_restrict ht]
    _ = ∫⁻ x in s, t.indicator (fun _ => 1) (φ x) * J x ∂μX :=
        key.symm
    _ = ∫⁻ x in s, (φ ⁻¹' t).indicator J x ∂μX := by
        refine lintegral_congr fun x => ?_
        by_cases hx : φ x ∈ t
        · simp [hx, indicator_of_mem]
        · simp [hx, indicator_of_notMem]
    _ = ∫⁻ x in φ ⁻¹' t ∩ s, J x ∂μX := by
        rw [lintegral_indicator (h.1 ht), Measure.restrict_restrict (h.1 ht)]

/-- The localized `Measure.map` form. -/
theorem map_withDensity_eq (h : TransportsToOn μX μY K φ J) {s : Set X}
    (hs : s ⊆ K) :
    Measure.map φ ((μX.restrict s).withDensity J) =
      μY.restrict (φ '' s) := by
  ext t ht
  rw [Measure.map_apply h.1 ht, withDensity_apply _ (h.1 ht),
    Measure.restrict_restrict (h.1 ht), Measure.restrict_apply ht,
    ← h.image_inter_eq hs ht, inter_comm]

/-- The sublevel-set bridge: target sublevel mass over the image equals
the weighted source mass of the pulled-back sublevel set. -/
theorem sublevel_eq (h : TransportsToOn μX μY K φ J) {s : Set X}
    (hs : s ⊆ K) {f : Y → ℝ} (hf : Measurable f) (ε : ℝ) :
    μY ({y | f y ≤ ε} ∩ φ '' s) =
      ∫⁻ x in {x | f (φ x) ≤ ε} ∩ s, J x ∂μX :=
  h.image_inter_eq hs (measurableSet_le hf measurable_const)

/-- Transport on a larger domain restricts to any smaller one. -/
theorem mono_dom (h : TransportsToOn μX μY K φ J) {K' : Set X}
    (hK : K' ⊆ K) : TransportsToOn μX μY K' φ J :=
  ⟨h.1, h.2.1, fun s hs => h.2.2 s (hs.trans hK)⟩

/-- Reweighting the target: a transport into `μY` with density `J` is a
transport into `μY.withDensity ρ` with the pulled-back density
`(ρ ∘ φ) · J`.  This is how a chart's Lebesgue-to-Lebesgue transport
feeds a density-weighted ambient measure: the chart carries the
pulled-back ambient density times its own Jacobian density. -/
theorem withDensity_target [SFinite μY] (h : TransportsToOn μX μY K φ J)
    {ρ : Y → ℝ≥0∞} (hρ : Measurable ρ) :
    TransportsToOn μX (μY.withDensity ρ) K φ (fun x => ρ (φ x) * J x) := by
  refine ⟨h.1, (hρ.comp h.1).mul h.2.1, fun s hs g hg => ?_⟩
  calc ∫⁻ x in s, g (φ x) * (ρ (φ x) * J x) ∂μX
      = ∫⁻ x in s, (fun y => ρ y * g y) (φ x) * J x ∂μX := by
        refine lintegral_congr fun x => ?_
        dsimp only
        ring
    _ = ∫⁻ y in φ '' s, ρ y * g y ∂μY := h.2.2 s hs _ (hρ.mul hg)
    _ = ∫⁻ y in φ '' s, g y ∂(μY.withDensity ρ) := by
        rw [restrict_withDensity' (φ '' s) ρ,
          lintegral_withDensity_eq_lintegral_mul _ hρ hg]
        rfl

/-- A measurable embedding whose pushforward of the weighted measure is
the target on its range transports exactly.  `withDensity_apply'`
(arbitrary sets, `SFinite`) and the embedding's arbitrary-set
`map_apply` carry the localization. -/
theorem of_measurableEmbedding [SFinite μX] {φ : X → Y}
    {J : X → ℝ≥0∞} (hf : MeasurableEmbedding φ) (hJ : Measurable J)
    (hmap : Measure.map φ (μX.withDensity J) = μY.restrict (range φ)) :
    TransportsToOn μX μY univ φ J := by
  refine ⟨hf.measurable, hJ, fun s _ g hg => ?_⟩
  have hlhs : (∫⁻ x, g (φ x) ∂((μX.restrict s).withDensity J)) =
      ∫⁻ x in s, g (φ x) * J x ∂μX := by
    rw [lintegral_withDensity_eq_lintegral_mul (μX.restrict s) hJ
      (g := fun x => g (φ x)) (hg.comp hf.measurable)]
    exact lintegral_congr fun x => mul_comm _ _
  have key : Measure.map φ ((μX.restrict s).withDensity J) =
      μY.restrict (φ '' s) := by
    ext t ht
    rw [Measure.map_apply hf.measurable ht,
      withDensity_apply _ (hf.measurable ht),
      Measure.restrict_restrict (hf.measurable ht),
      Measure.restrict_apply ht, ← Set.image_preimage_inter φ s t]
    calc ∫⁻ x in φ ⁻¹' t ∩ s, J x ∂μX
        = (μX.withDensity J) (φ ⁻¹' t ∩ s) := (withDensity_apply' _ _).symm
      _ = Measure.map φ (μX.withDensity J) (φ '' (φ ⁻¹' t ∩ s)) := by
          rw [hf.map_apply, Set.preimage_image_eq _ hf.injective]
      _ = (μY.restrict (range φ)) (φ '' (φ ⁻¹' t ∩ s)) := by rw [hmap]
      _ = μY (φ '' (φ ⁻¹' t ∩ s)) := by
          rw [Measure.restrict_apply' hf.measurableSet_range,
            Set.inter_eq_left.mpr (Set.image_subset_range _ _)]
  rw [← hlhs, ← lintegral_map hg hf.measurable, key]

/-- Transport is invariant under changing the map on a source-null set
whose images under both maps are target-null. -/
theorem congr_fun_ae (h : TransportsToOn μX μY K φ J) {φ' : X → Y}
    (hφ' : Measurable φ') {N : Set X} (hN : μX N = 0)
    (heq : ∀ x ∉ N, φ x = φ' x)
    (himg : μY (φ '' N) = 0) (himg' : μY (φ' '' N) = 0) :
    TransportsToOn μX μY K φ' J := by
  refine ⟨hφ', h.2.1, fun s hs g hg => ?_⟩
  have h1 : (∫⁻ x in s, g (φ' x) * J x ∂μX) =
      ∫⁻ x in s, g (φ x) * J x ∂μX := by
    refine lintegral_congr_ae (Filter.EventuallyEq.filter_mono ?_
      (ae_mono Measure.restrict_le_self))
    filter_upwards [compl_mem_ae_iff.mpr hN] with x hx
    rw [heq x hx]
  have h2 : μY.restrict (φ' '' s) = μY.restrict (φ '' s) := by
    refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
    · refine measure_mono_null (fun y hy => ?_) himg'
      obtain ⟨⟨x, hxs, rfl⟩, hyn⟩ := hy
      by_cases hxN : x ∈ N
      · exact ⟨x, hxN, rfl⟩
      · exact absurd ⟨x, hxs, heq x hxN⟩ hyn
    · refine measure_mono_null (fun y hy => ?_) himg
      obtain ⟨⟨x, hxs, rfl⟩, hyn⟩ := hy
      by_cases hxN : x ∈ N
      · exact ⟨x, hxN, rfl⟩
      · exact absurd ⟨x, hxs, (heq x hxN).symm⟩ hyn
  rw [h1, show (∫⁻ y in φ' '' s, g y ∂μY) = ∫⁻ y in φ '' s, g y ∂μY
      from by rw [h2]]
  exact h.2.2 s hs g hg

/-- Null correction: transport extends across a source-null set with
target-null image — the route around non-injective slices of blow-up
substitutions. -/
theorem mono_ae (h : TransportsToOn μX μY K φ J) {N : Set X}
    (hN : μX N = 0) (hNimg : μY (φ '' N) = 0) :
    TransportsToOn μX μY (K ∪ N) φ J := by
  refine ⟨h.1, h.2.1, fun s hs g hg => ?_⟩
  have hsub : s \ (s ∩ K) ⊆ N := fun x hx =>
    (hs hx.1).resolve_left fun hK => hx.2 ⟨hx.1, hK⟩
  have h1 : μX.restrict s = μX.restrict (s ∩ K) :=
    Measure.restrict_congr_set (ae_eq_set.mpr
      ⟨measure_mono_null hsub hN,
        measure_mono_null (by
          rintro x ⟨⟨hxs, -⟩, hns⟩
          exact hns hxs) (measure_empty (μ := μX))⟩)
  have h2 : μY.restrict (φ '' s) = μY.restrict (φ '' (s ∩ K)) :=
    Measure.restrict_congr_set (ae_eq_set.mpr
      ⟨measure_mono_null (fun y hy => by
          obtain ⟨x, hxs, rfl⟩ := hy.1
          exact ⟨x, hsub ⟨hxs, fun hxK => hy.2 ⟨x, hxK, rfl⟩⟩, rfl⟩) hNimg,
        measure_mono_null (by
          rintro y ⟨⟨x, hx, rfl⟩, hy⟩
          exact hy ⟨x, hx.1, rfl⟩) (measure_empty (μ := μY))⟩)
  rw [show (∫⁻ x in s, g (φ x) * J x ∂μX) =
      ∫⁻ x in s ∩ K, g (φ x) * J x ∂μX from by rw [h1],
    show (∫⁻ y in φ '' s, g y ∂μY) =
      ∫⁻ y in φ '' (s ∩ K), g y ∂μY from by rw [h2]]
  exact h.2.2 (s ∩ K) inter_subset_right g hg

/-- Composition: feed the outer Jacobian into the inner test
function. -/
theorem comp {KX : Set X} {KY : Set Y} {ψ : X → Y} {φ : Y → Z}
    {Jψ : X → ℝ≥0∞} {Jφ : Y → ℝ≥0∞}
    (hψ : TransportsToOn μX μY KX ψ Jψ)
    (hφ : TransportsToOn μY μZ KY φ Jφ) (hmaps : MapsTo ψ KX KY) :
    TransportsToOn μX μZ KX (fun x => φ (ψ x))
      (fun x => Jψ x * Jφ (ψ x)) := by
  refine ⟨hφ.1.comp hψ.1, hψ.2.1.mul (hφ.2.1.comp hψ.1), ?_⟩
  intro s hs g hg
  have h1 : ∫⁻ x in s, g (φ (ψ x)) * (Jψ x * Jφ (ψ x)) ∂μX =
      ∫⁻ x in s, (fun y => g (φ y) * Jφ y) (ψ x) * Jψ x ∂μX := by
    refine lintegral_congr fun x => ?_
    ring
  rw [h1, hψ.2.2 s hs (fun y => g (φ y) * Jφ y)
      ((hg.comp hφ.1).mul hφ.2.1),
    hφ.2.2 (ψ '' s) ((Set.image_mono hs).trans hmaps.image_subset) g hg,
    image_image]

end TransportsToOn

/-- A measure-preserving equivalence restricts to any source set,
transporting onto the image: `MeasurableEmbedding.map_apply` evaluates
the pushforward on arbitrary sets, so no measurability of `s` or its
image is needed. -/
theorem _root_.MeasureTheory.MeasurePreserving.restrict_image
    {μX : Measure X} {μY : Measure Y} {e : X ≃ᵐ Y}
    (h : MeasurePreserving e μX μY) (s : Set X) :
    MeasurePreserving e (μX.restrict s) (μY.restrict (e '' s)) := by
  refine ⟨e.measurable, ?_⟩
  ext t ht
  rw [Measure.map_apply e.measurable ht,
    Measure.restrict_apply (e.measurable ht), Measure.restrict_apply ht]
  calc μX (e ⁻¹' t ∩ s)
      = μX (e ⁻¹' (t ∩ e '' s)) := by
        rw [preimage_inter, Set.preimage_image_eq _ e.injective]
    _ = Measure.map e μX (t ∩ e '' s) :=
        (e.measurableEmbedding.map_apply _ _).symm
    _ = μY (t ∩ e '' s) := by rw [h.map_eq]

/-- A measure-preserving equivalence transports with unit density. -/
theorem _root_.MeasurableEquiv.transportsToOn_one (e : X ≃ᵐ Y)
    {μX : Measure X} {μY : Measure Y} (h : MeasurePreserving e μX μY) :
    TransportsToOn μX μY univ e fun _ => 1 := by
  refine ⟨e.measurable, measurable_const, fun s _ g hg => ?_⟩
  simp only [mul_one]
  exact (h.restrict_image s).lintegral_comp hg

/-- A `fst`-density on a product is the product of the weighted first
factor: the spectator-extension lemma for marked charts. -/
theorem _root_.MeasureTheory.withDensity_fst_prod {X W : Type*}
    [MeasurableSpace X] [MeasurableSpace W] {μ : Measure X}
    {ρ : Measure W} [SFinite ρ] {J : X → ℝ≥0∞} (hJ : Measurable J) :
    (μ.prod ρ).withDensity (fun p => J p.1) =
      (μ.withDensity J).prod ρ := by
  ext t ht
  rw [withDensity_apply _ ht, Measure.prod_apply ht]
  calc ∫⁻ p in t, J p.1 ∂(μ.prod ρ)
      = ∫⁻ p, t.indicator (fun p => J p.1) p ∂(μ.prod ρ) := by
        rw [lintegral_indicator ht]
    _ = ∫⁻ x, ∫⁻ w, t.indicator (fun p => J p.1) (x, w) ∂ρ ∂μ :=
        lintegral_prod _ ((hJ.comp measurable_fst).indicator ht).aemeasurable
    _ = ∫⁻ x, J x * ρ (Prod.mk x ⁻¹' t) ∂μ := by
        refine lintegral_congr fun x => ?_
        calc ∫⁻ w, t.indicator (fun p => J p.1) (x, w) ∂ρ
            = ∫⁻ w, (Prod.mk x ⁻¹' t).indicator (fun _ => J x) w ∂ρ := by
              refine lintegral_congr fun w => ?_
              by_cases hw : (x, w) ∈ t
              · rw [Set.indicator_of_mem hw, Set.indicator_of_mem
                  (show w ∈ Prod.mk x ⁻¹' t from hw)]
              · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem
                  (show w ∉ Prod.mk x ⁻¹' t from hw)]
          _ = J x * ρ (Prod.mk x ⁻¹' t) := by
              rw [lintegral_indicator (measurable_prodMk_left ht),
                setLIntegral_const, mul_comm]
    _ = ∫⁻ x, ρ (Prod.mk x ⁻¹' t) ∂(μ.withDensity J) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hJ
          (measurable_measure_prodMk_left ht)]
        rfl

/-- Conjugation by a measure-preserving equivalence: a self-map
transport on the target conjugates to one on the source, with the
pulled-back density. -/
theorem TransportsToOn.conj {X Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Z] {μX : Measure X} {μZ : Measure Z}
    (e : X ≃ᵐ Z) (he : MeasurePreserving e μX μZ) {K : Set Z}
    {φ : Z → Z} {J : Z → ℝ≥0∞} (h : TransportsToOn μZ μZ K φ J) :
    TransportsToOn μX μX (e ⁻¹' K)
      (fun x => e.symm (φ (e x))) fun x => J (e x) := by
  have h1 : TransportsToOn μX μZ (e ⁻¹' K) e (fun _ => 1) :=
    (e.transportsToOn_one he).mono_dom (subset_univ _)
  have h2 := h1.comp h (mapsTo_preimage _ _)
  have h3 : TransportsToOn μZ μX univ e.symm (fun _ => 1) :=
    e.symm.transportsToOn_one (he.symm e)
  have h4 := h2.comp h3 (mapsTo_univ _ _)
  refine ⟨h4.1, h.2.1.comp (he.measurable), fun s hs g hg => ?_⟩
  have := h4.2.2 s hs g hg
  simpa [one_mul, mul_one] using this

end Analytic
