/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import SLT.MeasureTheory.Measure.Lebesgue.CoordHyperplanes
public import SLT.Resolution.Hironaka
public import SLT.Geometry.Manifold.MaximalAtlas
import Hironaka.Resolution.Standard.Analytic
import SLT.Geometry.Manifold.ChartedSpace.ContinuousLinearEquiv
import SLT.Geometry.Manifold.ContMDiff.Basic
import SLT.Resolution.CentredChart
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Resolutions over an open set with nonzero germs, and what they give

A real analytic `F` on an open `U` that is not identically zero near any point of `U` has a
resolution over `U` (`exists_resolution_of_nonzero_germs`). It is read off the local
monomialization of the hironaka package, `exists_proper_analytic_monomialization`
([Ati70, Resolution Theorem] with the Jacobian clause of [BM97, Theorem 1.10]), which gives over
`U` a proper analytic `π : M → U`, an analytic isomorphism over `{F ≠ 0}`, in whose chart at every
point both `F ∘ π` and the Jacobian determinant of `π` are units times monomials:

* that theorem is stated on Euclidean space; `M` is modelled on `Fin d → ℝ` by composing its
  charts with the linear equivalence `EuclideanSpace.equiv`
  (`ChartedSpace.transContinuousLinearEquiv`), which keeps it an analytic manifold and changes
  nothing analytic, since the identity of `M` is analytic between the two structures;
* `π` is onto, its image being closed (properness) and containing the dense set `{F ≠ 0}`;
* over `U \ {F = 0}`, `π` and the analytic inverse glued from its local inverses by injectivity
  (`IsLocalDiffeomorphOn.exists_contMDiffOn_leftInvOn`) form a partial diffeomorphism, so `π` is
  a local analytic diffeomorphism there for the model `Fin d → ℝ`;
* at a point over a zero of `F`, the two monomial forms in the chart at the point give Watanabe's
  centred chart with `F ∘ π = ± u^k` exactly (`exists_centred_chart_of_eventually_monomial`).

Over a connected open set (`exists_resolution_of_isConnected`) this is Hironaka's theorem in the
form of [Hit26, Theorem 3.3.1], and over a finite union of balls it is
`exists_resolution_of_finite_balls`.

For any resolution: the resolving manifold is σ-compact and second countable
(`Resolution.secondCountableTopology`, from properness); `π` has an analytic left inverse over
`U \ {F = 0}` (`Resolution.exists_contMDiffOn_leftInvOn`); and the zero set of `F` in `U` is
Lebesgue null (`Resolution.volume_zeroSet_eq_zero`: in each chart over the zero set it is the
image of the coordinate walls).

Supports [Hit26, Theorem 3.3.1] in the global form
`exists_sltResolution` (`SLT/Resolution.lean`).
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

variable {d : ℕ}

namespace Resolution

variable {F : (Fin d → ℝ) → ℝ} (R : Resolution F)

/-- A resolving manifold is σ-compact: `M = ⋃ₙ π ⁻¹' Kₙ` for a compact exhaustion `Kₙ` of the
open `U`, each preimage compact by properness. -/
instance sigmaCompactSpace : SigmaCompactSpace R.M := by
  have : LocallyCompactSpace R.U := R.isOpen_U.locallyCompactSpace
  have hσ : IsSigmaCompact R.U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hKU⟩ := hσ
  refine ⟨⟨fun n ↦ R.π ⁻¹' K n, fun n ↦ R.proper _ ?_ (hK n), ?_⟩⟩
  · rw [← hKU]; exact subset_iUnion K n
  · rw [← preimage_iUnion, hKU]
    exact eq_univ_of_forall R.mem_U

/-- A resolving manifold is second countable (from σ-compactness and the countable cover by
chart domains). -/
instance secondCountableTopology : SecondCountableTopology R.M :=
  ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℝ) R.M

/-- The zero set of `F` in `U` is Lebesgue null: it is covered by countably many chart images
`π (e⁻¹ (e.target ∩ walls))`, where the walls are the coordinate hyperplanes, and the image of a
null set under the differentiable `π ∘ e⁻¹` is null. Supports the exceptional set of
`exists_sltResolution`. -/
theorem volume_zeroSet_eq_zero : volume {w | w ∈ R.U ∧ F w = 0} = 0 := by
  classical
  set Z : Set R.M := R.π ⁻¹' {w | F w = 0} with hZ
  set walls : Set (Fin d → ℝ) := ⋃ j ∈ (Finset.univ : Finset (Fin d)), {u | u j = 0}
  have hwalls : volume walls = 0 := measure_mono_null (fun u hu ↦ by
    obtain ⟨j, -, hj⟩ := mem_iUnion₂.mp hu; exact ⟨j, hj⟩) (volume_coordHyperplanes d)
  -- a chart at every point of `Z` in which `F ∘ π` is `±` a monomial
  have hch : ∀ P ∈ Z, ∃ e : OpenPartialHomeomorph R.M (Fin d → ℝ),
      e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.M ∧ P ∈ e.source ∧
      ∀ u ∈ e.target, F (R.π (e.symm u)) = 0 → u ∈ walls := by
    intro P hP
    obtain ⟨e, he, hPe, -, S, k, -, -, hS, hFe, -⟩ := R.chart P hP
    refine ⟨e, he, hPe, fun u hu h0 ↦ ?_⟩
    have hS0 : S ≠ 0 := by rcases hS with rfl | rfl <;> norm_num
    rw [hFe u hu] at h0
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp ((mul_eq_zero.mp h0).resolve_left hS0)
    exact mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ j)) (pow_eq_zero_iff'.mp hj).1
  choose e he hPe hwall using hch
  let src : R.M → Set R.M := fun P ↦ if h : P ∈ Z then (e P h).source else ∅
  obtain ⟨T, hTZ, hTc, hTU⟩ := isOpen_biUnion_countable Z src fun P hP ↦ by
    simp only [src, dite_eq_left hP]; exact (e P hP).open_source
  -- the zero set is covered by the chart images of the walls
  let img : R.M → Set (Fin d → ℝ) := fun P ↦
    if h : P ∈ Z then (R.π ∘ (e P h).symm) '' ((e P h).target ∩ walls) else ∅
  have hcover : {w | w ∈ R.U ∧ F w = 0} ⊆ ⋃ P ∈ T, img P := by
    rintro w ⟨hwV, hw0⟩
    obtain ⟨P, rfl⟩ := R.range_π.symm ▸ hwV
    have hPZ : P ∈ Z := hw0
    have : P ∈ ⋃ Q ∈ Z, src Q :=
      mem_biUnion hPZ (by simp only [src, dite_eq_left hPZ]; exact hPe P hPZ)
    rw [← hTU] at this
    obtain ⟨Q, hQT, hPQ⟩ := mem_iUnion₂.mp this
    have hQZ := hTZ hQT
    simp only [src, dite_eq_left hQZ] at hPQ
    refine mem_biUnion hQT ?_
    simp only [img, dite_eq_left hQZ]
    refine ⟨e Q hQZ P, ⟨(e Q hQZ).map_source hPQ, hwall Q hQZ _ ((e Q hQZ).map_source hPQ) ?_⟩, ?_⟩
    · rw [(e Q hQZ).left_inv hPQ]; exact hw0
    · simp [(e Q hQZ).left_inv hPQ]
  refine measure_mono_null hcover ((measure_biUnion_null_iff hTc).mpr fun P hP ↦ ?_)
  have hPZ := hTZ hP
  simp only [img, dite_eq_left hPZ]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    ((analyticOnNhd_comp_symm_of_mem_maximalAtlas R.analytic_π (he P hPZ)).differentiableOn.mono
      inter_subset_left)
    (measure_mono_null inter_subset_right hwalls)

end Resolution

/-- The determinant of a continuous linear endomorphism conjugated by a continuous linear
equivalence is unchanged. -/
private theorem det_comp_comp_symm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (A : E →L[ℝ] E) (L : E ≃L[ℝ] E') :
    ((L : E →L[ℝ] E').comp (A.comp (L.symm : E' →L[ℝ] E))).det = A.det :=
  LinearMap.det_conj (A : E →ₗ[ℝ] E) L.toLinearEquiv

/-- **Resolution of singularities over an open set** ([Hit26, Theorem 3.3.1] for one function,
over the whole of `U`). A real analytic `F` on an open `U ⊆ ℝ^d` that is not identically zero
near any point of `U` has a resolution over `U`: read off the local monomialization
`exists_proper_analytic_monomialization` of the hironaka package (module docstring). -/
theorem exists_resolution_of_nonzero_germs {U : Set (Fin d → ℝ)} {F : (Fin d → ℝ) → ℝ}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℝ F U) (hFg : ∀ w ∈ U, ¬ (F =ᶠ[𝓝 w] 0)) :
    ∃ R : Resolution F, R.U = U := by
  classical
  -- `ℝ^d` as Euclidean space, where the monomialization is stated
  set L : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ with hL
  set U' : Opens (EuclideanSpace ℝ (Fin d)) := ⟨L ⁻¹' U, hU.preimage L.continuous⟩ with hU'
  set f : EuclideanSpace ℝ (Fin d) → ℝ := F ∘ L with hfdef
  have hf : AnalyticOnNhd ℝ f U' := fun x hx ↦
    (hF (L x) hx).comp ((L : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ)).analyticAt x)
  have hf₀ : ∀ x ∈ U', ∃ᶠ y in 𝓝 x, f y ≠ 0 := by
    intro x hx
    have h := hFg (L x) hx
    have hmap : Filter.map L (𝓝 x) = 𝓝 (L x) := L.toHomeomorph.map_nhds_eq x
    rw [Filter.EventuallyEq, Filter.not_eventually, ← hmap, Filter.frequently_map] at h
    exact h
  obtain ⟨M, _, _, π, hman, ht2, -, hπ, hprop, hloc, hbij, hmono⟩ :=
    exists_proper_analytic_monomialization.{0} U' hf hf₀
  -- `M` modelled on `Fin d → ℝ`
  let _ : ChartedSpace (Fin d → ℝ) M := ChartedSpace.transContinuousLinearEquiv L M
  have hman' : IsManifold 𝓘(ℝ, Fin d → ℝ) ω M :=
    ChartedSpace.isManifold_transContinuousLinearEquiv L
  have hid : ContMDiff (𝓡 d) 𝓘(ℝ, Fin d → ℝ) ω (id : M → M) :=
    ChartedSpace.contMDiff_id_transContinuousLinearEquiv L
  have hid' : ContMDiff 𝓘(ℝ, Fin d → ℝ) (𝓡 d) ω (id : M → M) :=
    ChartedSpace.contMDiff_id_transContinuousLinearEquiv_symm L
  set g : M → (Fin d → ℝ) := fun p ↦ L (π p : EuclideanSpace ℝ (Fin d)) with hg
  have hg₀ : ContMDiff (𝓡 d) 𝓘(ℝ, Fin d → ℝ) ω g :=
    L.contDiff.contMDiff.comp (contMDiff_subtype_val.comp hπ)
  have hga : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g := hg₀.comp hid'
  set S : Set U' := {x | f x ≠ 0} with hS
  have hZc : g ⁻¹' {w | F w ≠ 0} = π ⁻¹' S := by
    ext p
    exact Iff.rfl
  have hLU : ∀ w ∈ U, L.symm w ∈ U' := fun w hw ↦ by
    change L (L.symm w) ∈ U
    rwa [L.apply_symm_apply]
  -- `π` is onto: its image is closed and contains the dense set `{f ≠ 0}`
  have hsurj : Function.Surjective π := by
    have hcl : IsClosed (range π) := by
      rw [← image_univ]
      exact hprop.isClosedMap _ isClosed_univ
    have hsub : S ⊆ range π := fun x hx ↦ by
      obtain ⟨q, -, hq⟩ := hbij.surjOn hx
      exact ⟨q, hq⟩
    have hdense : ∀ x : U', x ∈ closure S := fun x ↦ by
      rw [mem_closure_iff_frequently, nhds_subtype, Filter.frequently_comap]
      exact ((hf₀ x x.2).and_eventually (U'.isOpen.mem_nhds x.2)).mono
        fun y hy ↦ ⟨⟨y, hy.2⟩, rfl, hy.1⟩
    exact fun x ↦ hcl.closure_subset_iff.2 hsub (hdense x)
  have hrange : range g = U := by
    refine Subset.antisymm ?_ fun w hw ↦ ?_
    · rintro _ ⟨p, rfl⟩
      exact (π p).2
    · obtain ⟨q, hq⟩ := hsurj ⟨L.symm w, hLU w hw⟩
      exact ⟨q, by simp [hg, hq]⟩
  have hinj : InjOn g (g ⁻¹' {w | F w ≠ 0}) := by
    rw [hZc]
    exact (L.injective.comp Subtype.val_injective).injOn.comp hbij.injOn (mapsTo_univ _ _)
  have hsurj' : SurjOn g (g ⁻¹' {w | F w ≠ 0}) (U \ {w | F w = 0}) := by
    rintro w ⟨hw, hw0⟩
    obtain ⟨p, hp, hpw⟩ := hbij.surjOn (show (⟨L.symm w, hLU w hw⟩ : U') ∈ S by
      change F (L (L.symm w)) ≠ 0
      rwa [L.apply_symm_apply])
    exact ⟨p, hp, by simp [hg, hpw]⟩
  have hgU : ∀ p, g p ∈ U := fun p ↦ hrange ▸ mem_range_self p
  have hpre : g ⁻¹' (U \ {w | F w = 0}) = g ⁻¹' {w | F w ≠ 0} := by
    ext p
    simp [hgU p]
  -- over `U \ {F = 0}`, a local diffeomorphism for the model `Fin d → ℝ`, through the analytic
  -- left inverse glued from the local inverses of `π`
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g
      (g ⁻¹' {w | F w ≠ 0}) := by
    rcases isEmpty_or_nonempty M with hM | hM
    · exact fun x ↦ isEmptyElim x.1
    set w₀ := g (Classical.arbitrary M)
    have hw₀ : w₀ ∈ U := hgU _
    obtain ⟨h, hh, hleft⟩ := hloc.exists_contMDiffOn_leftInvOn hbij
    let ι : (Fin d → ℝ) → U' := fun w ↦ if hw : w ∈ U then ⟨L.symm w, hLU w hw⟩ else
      ⟨L.symm w₀, hLU w₀ hw₀⟩
    have hιU : ∀ w (hw : w ∈ U), ι w = ⟨L.symm w, hLU w hw⟩ := fun w hw ↦ dite_eq_left hw
    have hT : IsOpen (U \ {w | F w = 0}) := by
      have : U \ {w | F w = 0} = U ∩ F ⁻¹' {0}ᶜ := by ext w; simp
      rw [this]
      exact hF.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
    have hleft' : ∀ p ∈ g ⁻¹' (U \ {w | F w = 0}), (h ∘ ι) (g p) = p := by
      intro p hp
      have hpS : p ∈ π ⁻¹' S := by rw [hpre] at hp; exact hp
      have : ι (g p) = π p := by
        rw [hιU _ (π p).2]
        exact Subtype.ext (L.symm_apply_apply _)
      change h (ι (g p)) = p
      rw [this, hleft p hpS]
    rw [← hpre]
    refine IsLocalDiffeomorphOn.of_contMDiffOn_leftInvOn hT hga (fun w hw ↦ ?_) hleft'
      fun w hw ↦ ?_
    · have hι : ContMDiffWithinAt 𝓘(ℝ, Fin d → ℝ) (𝓡 d) ω ι (U \ {w | F w = 0}) w := by
        rw [← contMDiffWithinAt_subtypeVal_comp_iff']
        refine (L.symm.contDiff.contMDiff.contMDiffAt.contMDiffWithinAt).congr
          (fun w' hw' ↦ ?_) ?_
        · simp [hιU w' hw'.1]
        · simp [hιU w hw.1]
      have hιS : MapsTo ι (U \ {w | F w = 0}) S := fun w' hw' ↦ by
        rw [hιU w' hw'.1]
        change F (L (L.symm w')) ≠ 0
        rw [L.apply_symm_apply]
        exact hw'.2
      exact (hid _).comp_contMDiffWithinAt w ((hh _ (hιS hw)).comp w hι hιS)
    · obtain ⟨p, hp, rfl⟩ := hsurj' hw
      rw [hleft' p (hpre ▸ hp)]
  refine ⟨{ U := U
            isOpen_U := hU
            M := M
            isManifold := hman'
            π := g
            analytic_π := hga
            range_π := hrange
            proper := fun C hCU hC ↦ ?_
            isLocalDiffeomorphOn := hlocal
            bijOn := ⟨fun p hp ↦ ⟨hgU p, hp⟩, hinj, hsurj'⟩
            chart := ?_ }, rfl⟩
  · -- properness
    have hC' : IsCompact (Subtype.val ⁻¹' (L ⁻¹' C) : Set U') :=
      (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
        (by rw [Subtype.range_coe]; exact preimage_mono hCU)).2
        (L.toHomeomorph.isCompact_preimage.2 hC)
    exact hprop.isCompact_preimage hC'
  · -- Watanabe's chart from the two monomial forms in the chart at `P`
    intro P hP
    obtain ⟨⟨α, u, hu, hu0, hev⟩, ⟨β, v, hv, hv0, hev'⟩⟩ := hmono P
    set c := chartAt (EuclideanSpace ℝ (Fin d)) P with hc
    set φ := chartAt (Fin d → ℝ) P with hφ
    have hφc : φ = c.transHomeomorph L.toHomeomorph := rfl
    have hPs : P ∈ φ.source := mem_chart_source _ P
    have hφt : ∀ y ∈ φ.target, extChartAt (𝓡 d) P (φ.symm y) = L.symm y := fun y hy ↦ by
      rw [hφc, OpenPartialHomeomorph.transHomeomorph_target] at hy
      simp only [hφc, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, ← hc]
      exact c.right_inv hy
    have hwt : ∀ y ∈ φ.target, ∀ (m : Fin d → ℕ),
        ∏ i, extChartAt (𝓡 d) P (φ.symm y) i ^ m i = ∏ i, y i ^ m i := fun y hy m ↦ by
      rw [hφt y hy]
      rfl
    have htend := φ.tendsto_symm hPs
    have hunit : ∀ {w : M → ℝ}, ContMDiffAt (𝓡 d) 𝓘(ℝ) ω w P → w P ≠ 0 →
        AnalyticAt ℝ (w ∘ φ.symm) (φ P) ∧ (w ∘ φ.symm) (φ P) ≠ 0 := fun hw hw0 ↦
      ⟨(hw.comp P (hid' P)).analyticAt_comp_chartAt_symm, by simpa [φ.left_inv hPs] using hw0⟩
    obtain ⟨ha, ha0⟩ := hunit hu hu0
    obtain ⟨hb, hb0⟩ := hunit hv hv0
    refine exists_centred_chart_of_eventually_monomial (α := α) (β := β) hga
      (IsManifold.chart_mem_maximalAtlas P) hPs hP ha ha0 hb hb0 ?_ ?_
    · filter_upwards [htend.eventually hev, φ.open_target.mem_nhds (φ.map_source hPs)]
        with y hy hyt
      rw [← hwt y hyt α]
      exact hy
    · filter_upwards [htend.eventually hev', φ.open_target.mem_nhds (φ.map_source hPs)]
        with y hy hyt
      have hcomp : g ∘ φ.symm = L ∘ (Subtype.val ∘ π ∘ (extChartAt (𝓡 d) P).symm) ∘ L.symm := by
        funext z
        simp [hg, hφc, ← hc]
      rw [hcomp, L.comp_fderiv, L.symm.comp_right_fderiv, det_comp_comp_symm, ← hφt y hyt,
        ← hwt y hyt β]
      exact hy

/-- **Hironaka's theorem**, [Hit26, Theorem 3.3.1] for a single function: a real analytic `F` on
a connected open `D`, not identically zero there, has a resolution over the whole of `D`
(`exists_resolution_of_nonzero_germs`, `F` having a nonzero germ at every point of `D` by the
identity theorem).

Relation to the source.
* **Strengthening.** [Hit26] resolves `F` over some open neighbourhood `V ⊆ D` of the origin,
  assuming `0 ∈ D` and `F 0 = 0`; here the resolution is over all of `D` and those hypotheses are
  not needed.
* **Deviation.** `D` is connected, and `π` is onto `D`. [Hit26] does not assert that `g` is onto
  `V`, and without connectedness its statement is satisfiable degenerately: if `F ≡ 0` on the
  component of `0` and `F ≠ 0` on another component, then `V = D`, `M` the other component and `g`
  the inclusion satisfy every clause while missing the origin. -/
theorem exists_resolution_of_isConnected {D : Set (Fin d → ℝ)} {F : (Fin d → ℝ) → ℝ}
    (hDo : IsOpen D) (hDc : IsConnected D) (hF : AnalyticOnNhd ℝ F D) (hne : ∃ w ∈ D, F w ≠ 0) :
    ∃ R : Resolution F, R.U = D :=
  exists_resolution_of_nonzero_germs hDo hF fun x hx hev ↦ by
    obtain ⟨w, hwD, hw⟩ := hne
    exact hw (hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc.isPreconnected hx hev hwD)

/-- A resolution of `F` over a finite union of balls `⋃ x ∈ t, ball x (r x)` inside an open `U₀`
on which `F` is analytic with nonzero germs: `exists_resolution_of_nonzero_germs` over the
union. -/
theorem exists_resolution_of_finite_balls {U₀ : Set (Fin d → ℝ)} {F : (Fin d → ℝ) → ℝ}
    (hF : AnalyticOnNhd ℝ F U₀) (hgerm : ∀ x ∈ U₀, ¬ (F =ᶠ[𝓝 x] 0))
    {t : Finset (Fin d → ℝ)} {r : (Fin d → ℝ) → ℝ}
    (hU : (⋃ x ∈ t, Metric.ball x (r x)) ⊆ U₀) :
    ∃ R : Resolution F, R.U = ⋃ x ∈ t, Metric.ball x (r x) :=
  exists_resolution_of_nonzero_germs (isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball) (hF.mono hU)
    fun w hw ↦ hgerm w (hU hw)

end SingularLearningTheory
