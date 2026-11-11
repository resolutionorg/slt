/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import SLT.PartialResolution.Structural.Terminal
public import SLT.Resolution.Components
import SLT.Analysis.Calculus.InverseFunctionTheorem.InjOn
import SLT.PartialResolution.Structural.OfMonomialCharts
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected

/-!
# A monomial resolution near a point of an analytic function

For `K` real-analytic on an open `U ⊆ ℝ^n` and a point `w ∈ U` near which `K` is not identically
zero, there is a compact neighbourhood `N` of `w` with a partial resolution of `K` on `N` all of
whose charts are monomial (`SingularLearningTheory.exists_monomialPartialResolution_at`), the input of the
chart-form read-off `SingularLearningTheory.exists_monomialChartCover_of_isMonomial`.

The resolution is `SingularLearningTheory.exists_resolution_of_isConnected` for `K (w + ·)` over a
ball `W` about the origin: a proper analytic map `g : M → ℝ^d` onto `W`, an analytic isomorphism
over `W ∖ K⁻¹(0)`, with Watanabe's chart `K ∘ g ∘ φ⁻¹ = S · u^k`, `det D(g ∘ φ⁻¹) = b · u^h` at
every point over the zero set [Wat09, Theorem 2.3].

* Every point `P` of `M` has a chart of the maximal atlas in which `g ∘ φ⁻¹` is a monomial chart
  (`IsMonomialChart`) on a closed ball about `φ P`
  (`SingularLearningTheory.Resolution.exists_isMonomialChart`): over the zero set, the
  resolution's chart; off it, any chart of the atlas, shrunk to where `K ∘ g` does not vanish, with
  exponents `0` (the Jacobian does not vanish there,
  `SingularLearningTheory.Resolution.det_fderiv_comp_symm_ne_zero`).
* The injectivity clause of a monomial chart asks for injectivity where the Jacobian monomial does
  not vanish, a set larger than the one over `W ∖ K⁻¹(0)` where `g` is injective. Since `K` is
  analytic on the connected `W` and not identically zero, its zero set has empty interior in `W`,
  and a map injective over the complement of a set with empty interior is injective where its
  Jacobian does not vanish (`Set.InjOn.injOn_det_fderiv_ne_zero`, by the inverse function theorem)
  (`SingularLearningTheory.Resolution.isMonomialChart_comp_symm`).
* The preimage under `g` of the closed ball `N₀` of half the radius is compact (properness), so
  finitely many of these charts cover it; since `g` is onto `W` their images cover `N₀`, and the
  charts translated by `w` cover `N = w + N₀`. Monomial charts covering a compact set give a
  monomial resolution of it (`Analytic.PartialResolution.exists_isMonomial_of_subset_iUnion_image`).
-/

public section

open Set Filter Topology TopologicalSpace Analytic
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Analytic.IsMonomialChart

variable {n : ℕ} {F : (Fin n → ℝ) → ℝ} {φ : (Fin n → ℝ) → (Fin n → ℝ)} {dom W : Set (Fin n → ℝ)}
  {e h : Fin n →₀ ℕ}

/-- A monomial chart of `F (w + ·)`, translated by `w`, is a monomial chart of `F`. -/
theorem const_add {w : Fin n → ℝ} (hc : IsMonomialChart (fun x ↦ F (w + x)) φ dom e h W) :
    IsMonomialChart F (fun y ↦ w + φ y) dom e h W where
  isOpen := hc.isOpen
  subset := hc.subset
  analyticOnNhd y hy := analyticAt_const.add (hc.analyticOnNhd y hy)
  injOn _ ha _ hb hab := hc.injOn ha hb (add_left_cancel hab)
  exists_unit := hc.exists_unit
  exists_jacUnit := by
    obtain ⟨v, hv, hv0, hve⟩ := hc.exists_jacUnit
    exact ⟨v, hv, hv0, fun y hy ↦ by rw [fderiv_const_add]; exact hve y hy⟩

end Analytic.IsMonomialChart

namespace SingularLearningTheory.Resolution

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} (R : Resolution K)

/-- In every chart of the resolving manifold, the resolution read in the chart is injective where
`K` does not vanish (the isomorphism clause off the zero set). -/
theorem injOn_comp_symm (φ : OpenPartialHomeomorph R.M (Fin d → ℝ)) :
    InjOn (R.π ∘ φ.symm) (φ.target ∩ (R.π ∘ φ.symm) ⁻¹' {x | K x ≠ 0}) := fun _ hy₁ _ hy₂ heq ↦
  φ.symm.injOn hy₁.1 hy₂.1 (R.injOn hy₁.2 hy₂.2 heq)

/-- Where `K` does not vanish, the Jacobian determinant of the resolution read in a chart of the
maximal atlas is nonzero: there the resolution is a local diffeomorphism
(`Resolution.isLocalDiffeomorphOn`). -/
theorem det_fderiv_comp_symm_ne_zero {φ : OpenPartialHomeomorph R.M (Fin d → ℝ)}
    (hφ : φ ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.M) {u : Fin d → ℝ} (hu : u ∈ φ.target)
    (hK : K (R.π (φ.symm u)) ≠ 0) : (fderiv ℝ (R.π ∘ φ.symm) u).det ≠ 0 := by
  have h : IsLocalDiffeomorphAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω (R.π ∘ φ.symm) u :=
    ((φ.toPartialDiffeomorph hφ).symm.isLocalDiffeomorphAt (I := 𝓘(ℝ, Fin d → ℝ))
      (J := 𝓘(ℝ, Fin d → ℝ)) (n := ω) hu).comp (K := 𝓘(ℝ, Fin d → ℝ)) (P := Fin d → ℝ)
      (R.isLocalDiffeomorphOn ⟨φ.symm u, hK⟩)
  have hne : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have heq : fderiv ℝ (R.π ∘ φ.symm) u =
      (h.mfderivToContinuousLinearEquiv hne).toContinuousLinearMap :=
    ContinuousLinearMap.ext fun v ↦
      congrArg (· v) (mfderiv_eq_fderiv (𝕜 := ℝ) (f := R.π ∘ φ.symm) (x := u)).symm
  rw [heq]
  exact (LinearEquiv.isUnit_det' (h.mfderivToContinuousLinearEquiv hne).toLinearEquiv).ne_zero

/-- **The resolution read in a chart is a monomial chart** wherever `K` and the Jacobian are units
times monomials: for a chart `φ` of the maximal atlas, an open `O ⊆ φ.target` on which
`K ∘ π ∘ φ⁻¹ = u · y^e` and `det D(π ∘ φ⁻¹) = v · y^h` with `u, v` continuous and nonvanishing,
`π ∘ φ⁻¹` is a monomial chart of `K` on every `B ⊆ O`, provided every point of `U` is a limit of
points where `K` does not vanish. The injectivity clause holds because `π ∘ φ⁻¹` is injective
where `K ∘ π ∘ φ⁻¹` does not vanish (`Resolution.injOn_comp_symm`), hence, by the inverse
function theorem, where its Jacobian does not (`Set.InjOn.injOn_det_fderiv_ne_zero`). -/
theorem isMonomialChart_comp_symm (hK : ∀ x ∈ R.U, x ∈ closure {x | K x ≠ 0})
    {φ : OpenPartialHomeomorph R.M (Fin d → ℝ)}
    (hφ : φ ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.M) {O : Set (Fin d → ℝ)} (hO : IsOpen O)
    (hOφ : O ⊆ φ.target) {e h : Fin d →₀ ℕ} {u v : (Fin d → ℝ) → ℝ} (hu : ContinuousOn u O)
    (hu0 : ∀ y ∈ O, u y ≠ 0) (hue : ∀ y ∈ O, K (R.π (φ.symm y)) = u y * monomialEval y e)
    (hv : ContinuousOn v O) (hv0 : ∀ y ∈ O, v y ≠ 0)
    (hve : ∀ y ∈ O, (fderiv ℝ (R.π ∘ φ.symm) y).det = v y * monomialEval y h)
    {B : Set (Fin d → ℝ)} (hB : B ⊆ O) :
    IsMonomialChart K (R.π ∘ φ.symm) B e h O where
  isOpen := hO
  subset := hB
  analyticOnNhd := (analyticOnNhd_comp_symm_of_mem_maximalAtlas R.analytic_π hφ).mono hOφ
  injOn := by
    have hinj : InjOn (R.π ∘ φ.symm) {y | y ∈ O ∧ (fderiv ℝ (R.π ∘ φ.symm) y).det ≠ 0} :=
      ((R.injOn_comp_symm φ).mono (inter_subset_inter_left _ hOφ)).injOn_det_fderiv_ne_zero hO
        (((analyticOnNhd_comp_symm_of_mem_maximalAtlas R.analytic_π hφ).mono hOφ).contDiffOn
          hO.uniqueDiffOn)
        fun y _ ↦ hK _ (R.mem_U _)
    exact hinj.mono fun y hy ↦ (⟨hy.1, by rw [hve y hy.1]; exact mul_ne_zero (hv0 y hy.1) hy.2⟩ :
      y ∈ O ∧ (fderiv ℝ (R.π ∘ φ.symm) y).det ≠ 0)
  exists_unit := ⟨u, hu, hu0, hue⟩
  exists_jacUnit := ⟨v, hv, hv0, hve⟩

/-- **Every point of the resolving manifold carries a monomial chart**: a chart `φ` of the maximal
atlas about `P` and a closed ball about `φ P` on which `π ∘ φ⁻¹` is a monomial chart of `K`. Over
the zero set the chart is the resolution's chart (`Resolution.chart`), with the exponents of
`K` and of the Jacobian; off it, it is the chart of the atlas at `P` with both exponents `0`, on
the part of its target where `K ∘ π` does not vanish. -/
theorem exists_isMonomialChart
    (hKc : ContinuousOn K R.U) (hK : ∀ x ∈ R.U, x ∈ closure {x | K x ≠ 0}) (P : R.M) :
    ∃ (φ : OpenPartialHomeomorph R.M (Fin d → ℝ)) (r : ℝ), P ∈ φ.source ∧ 0 < r ∧
      ∃ (e h : Fin d →₀ ℕ) (O : Set (Fin d → ℝ)),
        IsMonomialChart K (R.π ∘ φ.symm) (Metric.closedBall (φ P) r) e h O := by
  by_cases hP : K (R.π P) = 0
  · -- over the zero set: the resolution's chart
    obtain ⟨φ, hφ, hPs, -, S, k, hh, b, hS, hfS, hb, hb0, hJ⟩ := R.chart P hP
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp φ.open_target (φ P) (φ.map_source hPs)
    refine ⟨φ, ε / 2, hPs, half_pos hε, Finsupp.equivFunOnFinite.symm k,
      Finsupp.equivFunOnFinite.symm hh, φ.target,
      R.isMonomialChart_comp_symm hK hφ φ.open_target subset_rfl (u := fun _ ↦ S)
        continuousOn_const
        (fun _ _ ↦ ?_) (fun y hy ↦ ?_) hb.continuousOn hb0 (fun y hy ↦ ?_)
        ((Metric.closedBall_subset_ball (half_lt_self hε)).trans hball)⟩
    · rcases hS with rfl | rfl <;> norm_num
    · rw [hfS y hy, monomialEval_eq_prod]
      simp
    · rw [hJ y hy, monomialEval_eq_prod]
      simp
  · -- off the zero set: any chart, on the part of its target where `K ∘ R.π` does not vanish
    let φ := _root_.chartAt (Fin d → ℝ) P
    have hφ : φ ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.M := IsManifold.chart_mem_maximalAtlas P
    have hPs : P ∈ φ.source := mem_chart_source _ P
    have hrep := analyticOnNhd_comp_symm_of_mem_maximalAtlas R.analytic_π hφ
    have hKrep : ContinuousOn (fun y ↦ K (R.π (φ.symm y))) φ.target :=
      hKc.comp hrep.continuousOn fun y _ ↦ R.mem_U _
    set O := φ.target ∩ (fun y ↦ K (R.π (φ.symm y))) ⁻¹' {x | x ≠ 0} with hOdef
    have hO : IsOpen O := hKrep.isOpen_inter_preimage φ.open_target isOpen_ne
    have hOφ : O ⊆ φ.target := inter_subset_left
    have hPO : φ P ∈ O := by
      refine ⟨φ.map_source hPs, ?_⟩
      change K (R.π (φ.symm (φ P))) ≠ 0
      rwa [φ.left_inv hPs]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (φ P) hPO
    have hdet : ContinuousOn (fun y ↦ (fderiv ℝ (R.π ∘ φ.symm) y).det) O :=
      ContinuousLinearMap.continuous_det.comp_continuousOn
        (((hrep.contDiffOn (n := 1) φ.open_target.uniqueDiffOn).continuousOn_fderiv_of_isOpen
          φ.open_target le_rfl).mono hOφ)
    refine ⟨φ, ε / 2, hPs, half_pos hε, 0, 0, O,
      R.isMonomialChart_comp_symm hK hφ hO hOφ (hKrep.mono hOφ) (fun y hy ↦ hy.2)
        (fun y _ ↦ by rw [monomialEval_zero, mul_one]) hdet
        (fun y hy ↦ R.det_fderiv_comp_symm_ne_zero hφ (hOφ hy) hy.2)
        (fun y _ ↦ by rw [monomialEval_zero, mul_one])
        ((Metric.closedBall_subset_ball (half_lt_self hε)).trans hball)⟩

end SingularLearningTheory.Resolution

namespace SingularLearningTheory

/-- **A monomial resolution near a point of a real-analytic function**: for `K` real-analytic on
an open `U ⊆ ℝ^n` and a point `w ∈ U` near which `K` is not identically zero, there are a compact
neighbourhood `N` of `w` and a partial resolution of `K` on `N` all of whose charts are monomial
(`Analytic.PartialResolution.IsMonomial`). The charts are those of a resolution of `K (w + ·)` onto
a ball about the origin (`SingularLearningTheory.exists_resolution_of_isConnected`), translated
by `w`; finitely many of them cover `N` because the resolution is proper and onto the ball. -/
theorem exists_monomialPartialResolution_at {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {K : (Fin n → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin n → ℝ} (hw : w ∈ U)
    (hne : ¬ K =ᶠ[𝓝 w] 0) :
    ∃ N : Set (Fin n → ℝ), IsCompact N ∧ N ∈ 𝓝 w ∧
      ∃ R : PartialResolution n K N, R.IsMonomial := by
  classical
  -- `K` recentred at the origin, on the ball `W` of radius `ε` about it
  let K₀ : (Fin n → ℝ) → ℝ := fun x ↦ K (w + x)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU w hw
  let W : Opens (Fin n → ℝ) := ⟨Metric.ball 0 ε, Metric.isOpen_ball⟩
  have hWc : IsConnected (W : Set (Fin n → ℝ)) := Metric.isConnected_ball hε
  have hK₀ : AnalyticOnNhd ℝ K₀ (W : Set (Fin n → ℝ)) := fun x hx ↦ by
    refine (hK (w + x) (hεU ?_)).comp (analyticAt_const.add analyticAt_id)
    rwa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_zero_right]
  have hne₀ : ¬ ∀ᶠ x in 𝓝 (0 : Fin n → ℝ), K₀ x = 0 := by
    intro h
    apply hne
    have ht : Tendsto (fun x : Fin n → ℝ ↦ x - w) (𝓝 w) (𝓝 0) := by
      rw [← sub_self w]
      exact tendsto_id.sub tendsto_const_nhds
    filter_upwards [ht.eventually h] with x hx
    simpa [K₀] using hx
  -- the zero set of `K₀` has empty interior in `W`
  have hcl : ∀ x ∈ (W : Set (Fin n → ℝ)), x ∈ closure {x | K₀ x ≠ 0} := by
    intro x hx
    refine mem_closure_iff_nhds.mpr fun O hO ↦ ?_
    by_contra hemp
    have hev : K₀ =ᶠ[𝓝 x] 0 := Filter.mem_of_superset hO fun y hy ↦ by
      by_contra hy0
      exact hemp ⟨y, hy, hy0⟩
    have h0 := hK₀.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWc.isPreconnected hx hev
    exact hne₀ (Filter.mem_of_superset (Metric.ball_mem_nhds 0 hε) fun y hy ↦ h0 hy)
  -- a resolution of `K₀` onto `W`
  have hK₀ne : ∃ x ∈ (W : Set (Fin n → ℝ)), K₀ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne₀ (Filter.mem_of_superset (Metric.ball_mem_nhds 0 hε) hcon)
  obtain ⟨R, hRW⟩ :=
    SingularLearningTheory.exists_resolution_of_isConnected W.isOpen hWc hK₀ hK₀ne
  -- a monomial chart about every point of the resolving manifold
  choose φ r hPs hr e h V hc using
    R.exists_isMonomialChart (hRW ▸ hK₀.continuousOn) (hRW ▸ hcl)
  -- finitely many of them cover the compact preimage of the closed ball `N₀` of radius `ε / 2`
  have hN₀W : Metric.closedBall (0 : Fin n → ℝ) (ε / 2) ⊆ (W : Set (Fin n → ℝ)) :=
    Metric.closedBall_subset_ball (half_lt_self hε)
  have hC := R.proper _ (hRW ▸ hN₀W) (isCompact_closedBall 0 (ε / 2))
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun P ↦ (φ P).source ∩ φ P ⁻¹' Metric.ball (φ P P) (r P))
    (fun P ↦ (φ P).isOpen_inter_preimage Metric.isOpen_ball)
    fun P _ ↦ mem_iUnion.mpr ⟨P, hPs P, Metric.mem_ball_self (hr P)⟩
  -- their images, translated by `w`, cover the closed ball `N` of radius `ε / 2` about `w`
  refine ⟨Metric.closedBall w (ε / 2), isCompact_closedBall w (ε / 2),
    Metric.closedBall_mem_nhds w (half_pos hε), ?_⟩
  refine PartialResolution.exists_isMonomial_of_subset_iUnion_image (ι := {P // P ∈ t})
    (isCompact_closedBall w (ε / 2)) (φ := fun P y ↦ w + R.π ((φ P).symm y))
    (dom := fun P ↦ Metric.closedBall (φ P P) (r P))
    (fun P ↦ ⟨e P, h P, V P, (hc P).const_add⟩) (fun P ↦ isCompact_closedBall _ _) ?_
  intro x hx
  have hx₀ : x - w ∈ Metric.closedBall (0 : Fin n → ℝ) (ε / 2) := by
    rwa [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
  obtain ⟨P, hgP⟩ := (R.range_π.trans hRW).symm ▸ hN₀W hx₀
  have hPC : P ∈ R.π ⁻¹' Metric.closedBall 0 (ε / 2) := by rw [mem_preimage, hgP]; exact hx₀
  obtain ⟨Q, hQt, hPQ⟩ := mem_iUnion₂.mp (ht hPC)
  refine mem_iUnion.mpr ⟨⟨Q, hQt⟩, φ Q P, Metric.ball_subset_closedBall hPQ.2, ?_⟩
  change w + R.π ((φ Q).symm (φ Q P)) = x
  rw [(φ Q).left_inv hPQ.1, hgP, add_sub_cancel]

end SingularLearningTheory
