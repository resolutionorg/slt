/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Transport
public import SLT.Resolution.Cover
public import SLT.Resolution.Outer
public import SLT.Geometry.Manifold.Cutoff
public import SLT.Resolution.Nondegenerate
public import SLT.StandardForm.FundamentalConditionI
import SLT.Resolution.Surjective
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Assembling the resolution atlas

[Hit26, Section 3.3.1], the bookkeeping that
turns the resolutions of `K φ₂ ∏ H_i` at the points of `W₀` into the finite chart family with
weights of [Hit26, Equation (3.3.5)]. The data the construction
chooses are bundled in `AtlasData`: the semianalytic description of `W` and the factorisation of
the prior (fundamental condition II), the finite cover by resolutions, and for each resolution the
chart cover, the compact base set `Bcl_σ`, the inner partition of unity and the outer weight
`ρ̃_σ`, together with the threshold `δ` below which the outer weights sum to `1`. From these,
`AtlasData.toResolutionAtlas` is the atlas: charts indexed by (resolution, chart, good orthant),
chart maps `g ∘ e.symm ∘ (ε ⊙ ·²)`, exponents `k_α = q`, `h_α = 2(p + r) + 1`, the weights of
`Transport.lean`, localization `χ = Σ_σ ρ̃_σ`, and the transport identity by summing
`ChartCover.lintegral_transport` over the resolutions. Its weights are positive at the chart
origins, so the atlas is nondegenerate (`Nondegenerate.lean`); accessibility of the prior mass
near `W₀` makes the chart family nonempty.

| Thesis | Lean |
| --- | --- |
| [Hit26, Section 3.3.1], the chart family `A` | |
| | `AtlasData.ι`, `AtlasData.toResolutionAtlas` |
| [Hit26, Equation (3.3.5)] | `AtlasData.transport_identity` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {d : ℕ}

/-- The data of the construction of the atlas, see the module docstring. -/
structure AtlasData (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) where
  W_compact : IsCompact W
  /-- The open neighbourhood `U` of `W` on which `K` is analytic, `φ = φ₁ φ₂` and `W` is cut
  out by the `H_i`. -/
  U : Set (Fin d → ℝ)
  U_open : IsOpen U
  W_subset : W ⊆ U
  /-- The semianalytic description `W = {H_i ≥ 0}` in `U`, each `H_i` with nonzero germ on
  `U`. -/
  N : ℕ
  /-- The functions $H_i$, analytic on `U`, with
  $W = \{w \in U : H_i(w) \ge 0 \text{ for all } i\}$. -/
  H : Fin N → (Fin d → ℝ) → ℝ
  H_analytic : ∀ i, AnalyticOnNhd ℝ (H i) U
  domain_eq : ∀ w ∈ U, (w ∈ W ↔ ∀ i, 0 ≤ H i w)
  K_analytic : AnalyticOnNhd ℝ K U
  K_nonneg : ∀ w ∈ W, 0 ≤ K w
  /-- The factor $\varphi_1$ of the prior $\varphi = \varphi_1\varphi_2$, positive and smooth
  on `U`. -/
  φ₁ : (Fin d → ℝ) → ℝ
  /-- The factor $\varphi_2$ of the prior $\varphi = \varphi_1\varphi_2$, analytic on `U` and
  nonnegative on `W`. -/
  φ₂ : (Fin d → ℝ) → ℝ
  φ₁_pos : ∀ w ∈ U, 0 < φ₁ w
  φ₁_smooth : ContDiffOn ℝ ∞ φ₁ U
  φ₂_nonneg : ∀ w ∈ W, 0 ≤ φ₂ w
  φ₂_analytic : AnalyticOnNhd ℝ φ₂ U
  φ_eq : ∀ w ∈ U, φ w = φ₁ w * φ₂ w
  /-- The resolutions of `F = K φ₂ ∏ H_i` covering `W₀`. -/
  RC : ResolutionCover (fun w ↦ K w * φ₂ w * ∏ i, H i w) U {w | w ∈ W ∧ K w = 0}
  /-- For each resolution: the chart cover of the fibre over `W₀ ∩ closure E_σ`. -/
  C : (σ : RC.ι) →
    ChartCover K φ₂ H (RC.resolution σ).π ({w | w ∈ W ∧ K w = 0} ∩ closure (RC.E σ))
  /-- The compact base set of the outer weight, with fibre in the union of the small boxes. -/
  Bcl : RC.ι → Set (Fin d → ℝ)
  Bcl_compact : ∀ σ, IsCompact (Bcl σ)
  Bcl_subset : ∀ σ, Bcl σ ⊆ (RC.resolution σ).U
  Bcl_fibre : ∀ σ, (RC.resolution σ).π ⁻¹' Bcl σ ⊆ (C σ).smallUnion
  /-- The inner partitions of unity. -/
  ρ : (σ : RC.ι) → ChartCover.InnerPartition (C σ) (Bcl σ)
  /-- The outer weights `ρ̃_σ`, positive at the images of the chart centres. -/
  ρO : RC.ι → (Fin d → ℝ) → ℝ
  ρO_smooth : ∀ σ, ContDiff ℝ ∞ (ρO σ)
  ρO_nonneg : ∀ σ w, 0 ≤ ρO σ w
  ρO_supp : ∀ σ w, ρO σ w ≠ 0 → w ∈ Bcl σ
  ρO_pos : ∀ σ (i : (C σ).I), 0 < ρO σ ((RC.resolution σ).π ((C σ).P i))
  /-- The threshold `δ`: below it the outer weights sum to `1` on `W`. -/
  δ : ℝ
  δ_pos : 0 < δ
  sum_ρO_eq_one : ∀ w ∈ W, K w < δ → ∑ σ, ρO σ w = 1
  sum_ρO_le_one : ∀ w, ∑ σ, ρO σ w ≤ 1

namespace AtlasData

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (A : AtlasData K φ W)

/-- The chart family `A`: a resolution, a chart of its cover, and a good orthant. -/
@[expose] noncomputable def ι : Type :=
  Σ σ : A.RC.ι, Σ i : (A.C σ).I, ((A.C σ).goodOrthants W i : Finset (Fin d → Bool))

noncomputable instance : Fintype A.ι := by unfold ι; infer_instance

/-- The chart map `g_α`. -/
@[expose] noncomputable def chartMap (α : A.ι) : (Fin d → ℝ) → (Fin d → ℝ) :=
  (A.C α.1).gα α.2.1 α.2.2.1

/-- The side length `√a_i` of the chart cube. -/
@[expose] noncomputable def rad (α : A.ι) : ℝ := (A.C α.1).rad α.2.1

/-- `k_α`. -/
@[expose] def expK (α : A.ι) (j : Fin d) : ℕ := (A.C α.1).expK α.2.1 j

/-- `h_α`. -/
@[expose] def expH (α : A.ι) (j : Fin d) : ℕ := (A.C α.1).expH α.2.1 j

/-- The chart weight `φ̃_α`. -/
@[expose] noncomputable def weight (α : A.ι) : (Fin d → ℝ) → ℝ :=
  (A.C α.1).weight (A.ρ α.1) (A.ρO α.1) A.φ₁ α.2.1 α.2.2.1

/-- The localization `χ = Σ_σ ρ̃_σ`. -/
@[expose] noncomputable def χ (w : Fin d → ℝ) : ℝ := ∑ σ, A.ρO σ w

theorem isGood (α : A.ι) : ((A.C α.1).ch α.2.1).IsGood W α.2.2.1 := by
  classical
  exact (Finset.mem_filter.mp α.2.2.2).2

theorem W_closed (A : AtlasData K φ W) : IsClosed W := A.W_compact.isClosed

theorem measurable_chartMap (α : A.ι) : Measurable (A.chartMap α) :=
  ((A.C α.1).ch α.2.1).measurable_chartMap (A.RC.resolution α.1).analytic_π _

theorem analyticOnNhd_chartMap (α : A.ι) :
    AnalyticOnNhd ℝ (A.chartMap α) (cube d (A.rad α)) :=
  (((A.C α.1).ch α.2.1).chartMap_analyticOnNhd (A.RC.resolution α.1).analytic_π _).mono
    ((A.C α.1).cube_subset _)

theorem chartMap_mapsTo (α : A.ι) : MapsTo (A.chartMap α) (cube d (A.rad α)) W :=
  (((A.C α.1).ch α.2.1).mapsTo_of_isGood (A.RC.resolution α.1).analytic_π A.W_closed
    (A.isGood α)).mono_left
    ((A.C α.1).cube_subset _)

theorem K_chartMap (α : A.ι) {u : Fin d → ℝ} (hu : u ∈ cube d (A.rad α)) :
    K (A.chartMap α u) = ∏ j, u j ^ (2 * A.expK α j) :=
  ((A.C α.1).ch α.2.1).Kf_chartMap_of_isGood A.K_nonneg (A.isGood α) ((A.C α.1).cube_subset _ hu)

private theorem cube_subset_obox' (α : A.ι) :
    cube d (A.rad α) ⊆ obox d ((A.C α.1).ch α.2.1).rad' :=
  ((A.C α.1).cube_subset _).trans ((A.C α.1).ch α.2.1).cube_subset_obox

/-- The chart map is analytic on the open box where it is given by `Γ ∘ orthantSq`. -/
private theorem analyticOnNhd_chartMap_obox (α : A.ι) :
    AnalyticOnNhd ℝ (A.chartMap α) (obox d ((A.C α.1).ch α.2.1).rad') := fun u hu ↦ by
  have hΓ : AnalyticAt ℝ (fun w ↦ ((A.C α.1).ch α.2.1).Γ (orthantSq α.2.2.1 w)) u :=
    AnalyticAt.comp (f := orthantSq α.2.2.1)
      (((A.C α.1).ch α.2.1).Γ_analyticOnNhd (A.RC.resolution α.1).analytic_π _
        (((A.C α.1).ch α.2.1).orthantSq_mem_O _ hu))
      (analyticOnNhd_orthantSq _ u (mem_univ _))
  exact hΓ.congr (Filter.eventuallyEq_of_mem ((isOpen_obox d _).mem_nhds hu)
    fun _ hw ↦ (((A.C α.1).ch α.2.1).chartMap_eq _ hw).symm)

theorem weight_nonneg (α : A.ι) {u : Fin d → ℝ} (hu : u ∈ cube d (A.rad α)) :
    0 ≤ A.weight α u := by
  have haφ := ((A.C α.1).ch α.2.1).aφ_mul_sign_pos A.φ₂_nonneg (A.isGood α)
    ((A.C α.1).cube_subset _ hu)
  have hφ₁ := (A.φ₁_pos _ (A.W_subset (A.chartMap_mapsTo α hu))).le
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
    haφ.le) hφ₁) (A.ρO_nonneg _ _)) ((A.ρ α.1).nonneg _ _)

/-- The weight is smooth on an open neighbourhood of the closed chart cube. Keeping this
neighbourhood permits smooth extension for the chart zeta continuation. -/
theorem exists_weight_smooth_neighbourhood (α : A.ι) :
    ∃ S : Set (Fin d → ℝ), IsOpen S ∧ cube d (A.rad α) ⊆ S ∧
      ContDiffOn ℝ ∞ (A.weight α) S := by
  set c := (A.C α.1).ch α.2.1
  set S := obox d c.rad' ∩ A.chartMap α ⁻¹' A.U
  have hchart : ContDiffOn ℝ ∞ (A.chartMap α) S :=
    ((A.analyticOnNhd_chartMap_obox α).mono inter_subset_left).contDiffOn_of_completeSpace
  have hsq : ∀ f : (Fin d → ℝ) → ℝ, AnalyticOnNhd ℝ f c.O →
      ContDiffOn ℝ ∞ (fun u ↦ f (orthantSq α.2.2.1 u)) S := fun f hf ↦
    (hf.comp ((analyticOnNhd_orthantSq _).mono (subset_univ S)) fun u hu ↦
      c.orthantSq_mem_O _ hu.1).contDiffOn_of_completeSpace
  have hbJ : ContDiffOn ℝ ∞ (fun u ↦ |c.bJ (orthantSq α.2.2.1 u)|) S :=
    (hsq _ c.bJ_analytic).abs fun u hu ↦ c.bJ_ne _ (c.orthantSq_mem_O _ hu.1)
  have haφ : ContDiffOn ℝ ∞
      (fun u ↦ c.aφ (orthantSq α.2.2.1 u) * ∏ j, orthantSign α.2.2.1 j ^ c.r j) S :=
    (hsq _ c.aφ_analytic).mul contDiffOn_const
  have hφ₁ : ContDiffOn ℝ ∞ (fun u ↦ A.φ₁ (A.chartMap α u)) S :=
    A.φ₁_smooth.comp hchart fun u hu ↦ hu.2
  have hρO : ContDiffOn ℝ ∞ (fun u ↦ A.ρO α.1 (A.chartMap α u)) S :=
    (A.ρO_smooth α.1).comp_contDiffOn hchart
  have hρ : ContDiffOn ℝ ∞ (fun u ↦ (A.ρ α.1).ρ α.2.1 (c.e.symm (orthantSq α.2.2.1 u))) S :=
    ((A.ρ α.1).smooth α.2.1 c.e c.he).comp
      ((analyticOnNhd_orthantSq _).contDiffOn_of_completeSpace.mono (subset_univ _))
      fun u hu ↦ c.O_subset (c.orthantSq_mem_O _ hu.1)
  have hsub : cube d (A.rad α) ⊆ S := fun u hu ↦
    ⟨A.cube_subset_obox' α hu, A.W_subset (A.chartMap_mapsTo α hu)⟩
  have hS : IsOpen S := (A.analyticOnNhd_chartMap_obox α).continuousOn.isOpen_inter_preimage
    (isOpen_obox d _) A.U_open
  exact ⟨S, hS, hsub, ((((contDiffOn_const.mul hbJ).mul haφ).mul hφ₁).mul hρO).mul hρ⟩

/-- The chart weights are smooth on their closed cubes. -/
theorem weight_contDiffOn (α : A.ι) : ContDiffOn ℝ ∞ (A.weight α) (cube d (A.rad α)) := by
  obtain ⟨S, _, hsub, hs⟩ := A.exists_weight_smooth_neighbourhood α
  exact hs.mono hsub

/-- A globally smooth representative of the chart weight, agreeing on the cube.
A smooth cutoff inside its domain supplies the amplitude for repeated integration by parts
in the zeta continuation argument. -/
theorem exists_smooth_weight_extension (α : A.ι) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧ EqOn g (A.weight α) (cube d (A.rad α)) := by
  obtain ⟨S, hS, hsub, hs⟩ := A.exists_weight_smooth_neighbourhood α
  have hcpt : IsCompact (cube d (A.rad α)) := isCompact_Icc
  obtain ⟨χ, hχ, _, _, hχone, hχsupp, _⟩ := exists_smooth_cutoff hcpt hS hsub
  refine ⟨fun u ↦ χ u * A.weight α u, ?_, fun u hu ↦ by simp only [hχone u hu, one_mul]⟩
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ S
  · exact hχ.contDiffAt.mul (hs.contDiffAt (hS.mem_nhds hu))
  · have hu' : u ∉ tsupport χ := fun h ↦ hu (hχsupp h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hu'] with v hv
    simp [image_eq_zero_of_notMem_tsupport hv]

theorem weight_continuousOn (α : A.ι) : ContinuousOn (A.weight α) (cube d (A.rad α)) :=
  (A.weight_contDiffOn α).continuousOn

/-- The weights are positive at the chart origins ([Wat09, Theorem 6.5] (3)). -/
theorem weight_pos (α : A.ι) : 0 < A.weight α 0 := by
  have h0 : (0 : Fin d → ℝ) ∈ cube d (A.rad α) := ⟨fun _ ↦ le_rfl, fun _ ↦ ((A.C α.1).rad_pos _).le⟩
  have hsq : orthantSq α.2.2.1 (0 : Fin d → ℝ) = 0 := by funext j; simp [orthantSq]
  have hP : ((A.C α.1).ch α.2.1).e.symm 0 = (A.C α.1).P α.2.1 := by
    have := ((A.C α.1).ch α.2.1).e.left_inv ((A.C α.1).ch α.2.1).mem_source
    rwa [((A.C α.1).ch α.2.1).e_P] at this
  have hg : A.chartMap α 0 = (A.RC.resolution α.1).π ((A.C α.1).P α.2.1) :=
    ((A.C α.1).ch α.2.1).chartMap_zero _
  have hbJ : 0 < |((A.C α.1).ch α.2.1).bJ (orthantSq α.2.2.1 0)| :=
    abs_pos.mpr (((A.C α.1).ch α.2.1).bJ_ne _
      (((A.C α.1).ch α.2.1).orthantSq_mem_O _ (A.cube_subset_obox' α h0)))
  have haφ := ((A.C α.1).ch α.2.1).aφ_mul_sign_pos A.φ₂_nonneg (A.isGood α)
    ((A.C α.1).cube_subset _ h0)
  have hφ₁ : 0 < A.φ₁ (A.chartMap α 0) := A.φ₁_pos _ (A.W_subset (A.chartMap_mapsTo α h0))
  have hρO : 0 < A.ρO α.1 (A.chartMap α 0) := hg ▸ A.ρO_pos α.1 α.2.1
  have hρ : 0 < (A.ρ α.1).ρ α.2.1 (((A.C α.1).ch α.2.1).e.symm (orthantSq α.2.2.1 0)) := by
    rw [hsq, hP]; exact (A.ρ α.1).pos_centre _
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by positivity) hbJ) haφ) hφ₁) hρO) hρ

theorem exists_lipschitz_weight (α : A.ι) :
    ∃ L : NNReal, LipschitzOnWith L (A.weight α) (cube d (A.rad α)) :=
  (A.weight_contDiffOn α).exists_lipschitzOnWith (by simp)
    (convex_Icc _ _) isCompact_Icc

theorem χ_continuous : Continuous A.χ :=
  continuous_finsetSum _ fun σ _ ↦ (A.ρO_smooth σ).continuous

theorem χ_nonneg (w : Fin d → ℝ) : 0 ≤ A.χ w := Finset.sum_nonneg fun σ _ ↦ A.ρO_nonneg σ w

theorem χ_le_one (w : Fin d → ℝ) : A.χ w ≤ 1 := A.sum_ρO_le_one w

theorem χ_eq_one {w : Fin d → ℝ} (hw : w ∈ W) (hK : K w < A.δ) : A.χ w = 1 :=
  A.sum_ρO_eq_one w hw hK

open Classical in
/-- A measurable version of the prior, `φ₁ φ₂` on `U` and `0` outside; it agrees with `φ` on `W`. -/
@[expose] noncomputable def prior : (Fin d → ℝ) → ℝ := A.U.piecewise
    (fun w ↦ A.φ₁ w * A.φ₂ w) fun _ ↦ 0

theorem prior_eq_mul {w : Fin d → ℝ} (hw : w ∈ W) : A.prior w = A.φ₁ w * A.φ₂ w := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ (A.W_subset hw)

theorem prior_eq {w : Fin d → ℝ} (hw : w ∈ W) : A.prior w = φ w := by
  rw [A.prior_eq_mul hw, A.φ_eq w (A.W_subset hw)]

theorem measurable_prior : Measurable A.prior := by
  classical
  have h1 : ContinuousOn (fun w ↦ A.φ₁ w * A.φ₂ w) A.U :=
    A.φ₁_smooth.continuousOn.mul A.φ₂_analytic.continuousOn
  exact h1.measurable_piecewise continuousOn_const A.U_open.measurableSet

/-- The transport identity of one resolution, in the variables of the assembly. -/
theorem lintegral_transport_σ (σ : A.RC.ι) (Fm : (Fin d → ℝ) → ℝ≥0∞) (hFm : Measurable Fm) :
    ∫⁻ w in W, Fm w * ENNReal.ofReal (A.ρO σ w * A.prior w)
      = ∑ i, ∑ ε ∈ (A.C σ).goodOrthants W i, ∫⁻ u in cube d ((A.C σ).rad i),
          Fm ((A.C σ).gα i ε u) * ENNReal.ofReal
            ((∏ j, u j ^ ((A.C σ).expH i j : ℝ)) * (A.C σ).weight (A.ρ σ) (A.ρO σ) A.φ₁ i ε u) :=
  (A.C σ).lintegral_transport (fun _ _ ↦ rfl)
    (((A.K_analytic.mul A.φ₂_analytic).mul fun w hw ↦
      Finset.analyticAt_fun_prod _ fun i _ ↦ A.H_analytic i w hw).continuousOn.mono
        (A.RC.U_subset σ))
    (fun w hw ↦ A.domain_eq w (A.RC.U_subset σ hw)) A.W_closed
    A.W_closed.measurableSet A.φ₂_nonneg (fun _ hw ↦ A.prior_eq_mul hw)
    (fun _ hw ↦ (A.φ₁_pos _ (A.W_subset hw)).le) A.measurable_prior (A.ρO_smooth σ).continuous
    (A.ρO_nonneg σ) (A.ρO_supp σ) (A.Bcl_compact σ).isClosed.measurableSet (A.Bcl_subset σ)
    (A.Bcl_fibre σ) (A.ρ σ) Fm hFm

/-- A sum over the chart indices `A.ι = Σ σ, Σ i, goodOrthants` as an iterated sum. -/
theorem sum_ι (f : (σ : A.RC.ι) → (A.C σ).I → (Fin d → Bool) → ℝ≥0∞) :
    ∑ α : A.ι, f α.1 α.2.1 α.2.2.1 = ∑ σ, ∑ i, ∑ ε ∈ (A.C σ).goodOrthants W i, f σ i ε := by
  change ∑ α : (Σ σ : A.RC.ι, Σ i : (A.C σ).I, ((A.C σ).goodOrthants W i : Finset (Fin d → Bool))),
    f α.1 α.2.1 α.2.2.1 = _
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact Finset.sum_coe_sort ((A.C σ).goodOrthants W i) (f σ i)

/-- [Hit26, Equation (3.3.5)]: the localised prior measure
on `W` is the sum of the pushforwards of the weighted chart cubes. -/
theorem transport_identity :
    (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (A.χ w * φ w))
      = ∑ α, Measure.map (A.chartMap α) ((volume.restrict (cube d (A.rad α))).withDensity
          fun u ↦ ENNReal.ofReal ((∏ j, u j ^ (A.expH α j : ℝ)) * A.weight α u)) := by
  classical
  have hWm : MeasurableSet W := A.W_closed.measurableSet
  -- the prior may be replaced by its measurable version on `W`
  have hLHS : (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (A.χ w * φ w))
      = (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (A.χ w * A.prior w)) :=
    withDensity_congr_ae (ae_restrict_of_forall_mem hWm fun w hw ↦ by
      simp only
      rw [A.prior_eq hw])
  rw [hLHS]
  have hdens : Measurable fun w ↦ ENNReal.ofReal (A.χ w * A.prior w) :=
    ENNReal.measurable_ofReal.comp (A.χ_continuous.measurable.mul A.measurable_prior)
  refine Measure.ext_of_lintegral _ fun Fm hFm ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens hFm, lintegral_finsetSum_measure]
  -- the right-hand side, chart by chart
  have hRHS : ∀ α : A.ι, ∫⁻ w, Fm w ∂(Measure.map (A.chartMap α)
      ((volume.restrict (cube d (A.rad α))).withDensity
        fun u ↦ ENNReal.ofReal ((∏ j, u j ^ (A.expH α j : ℝ)) * A.weight α u)))
      = ∫⁻ u in cube d (A.rad α), Fm (A.chartMap α u) *
          ENNReal.ofReal ((∏ j, u j ^ (A.expH α j : ℝ)) * A.weight α u) := by
    intro α
    have hcube : MeasurableSet (cube d (A.rad α)) := measurableSet_Icc
    have hw : AEMeasurable (fun u ↦ ENNReal.ofReal ((∏ j, u j ^ (A.expH α j : ℝ)) * A.weight α u))
        (volume.restrict (cube d (A.rad α))) := by
      refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
      refine ContinuousOn.aemeasurable ?_ hcube
      refine ContinuousOn.mul ?_ (A.weight_continuousOn α)
      exact continuousOn_finsetProd _ fun j _ ↦
        (continuous_apply j).continuousOn.rpow_const fun u _ ↦ Or.inr (Nat.cast_nonneg _)
    rw [lintegral_map hFm (A.measurable_chartMap α), lintegral_withDensity_eq_lintegral_mul₀ hw
      (g := fun a ↦ Fm (A.chartMap α a)) (hFm.comp (A.measurable_chartMap α)).aemeasurable]
    refine lintegral_congr fun u ↦ ?_
    simp only [Pi.mul_apply]
    ring
  simp_rw [hRHS]
  -- the left-hand side, resolution by resolution
  have hLHS' : ∫⁻ w in W, ENNReal.ofReal (A.χ w * A.prior w) * Fm w
      = ∑ σ, ∫⁻ w in W, Fm w * ENNReal.ofReal (A.ρO σ w * A.prior w) := by
    rw [← lintegral_finsetSum (f := fun σ w ↦ Fm w * ENNReal.ofReal (A.ρO σ w * A.prior w)) _
      fun σ _ ↦ by
        exact hFm.mul (ENNReal.measurable_ofReal.comp ((A.ρO_smooth σ).continuous.measurable.mul
          A.measurable_prior))]
    refine setLIntegral_congr_fun hWm fun w hw ↦ ?_
    have hφnn : 0 ≤ A.prior w := by
      rw [A.prior_eq_mul hw]
      exact mul_nonneg (A.φ₁_pos w (A.W_subset hw)).le (A.φ₂_nonneg w hw)
    rw [χ, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun σ _ ↦ mul_nonneg (A.ρO_nonneg σ w) hφnn,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ ↦ mul_comm _ _
  simp only [Pi.mul_apply]
  rw [hLHS']
  simp_rw [A.lintegral_transport_σ _ Fm hFm]
  exact (A.sum_ι fun σ i ε ↦ ∫⁻ u in cube d ((A.C σ).rad i), Fm ((A.C σ).gα i ε u) *
    ENNReal.ofReal ((∏ j, u j ^ ((A.C σ).expH i j : ℝ)) *
      (A.C σ).weight (A.ρ σ) (A.ρO σ) A.φ₁ i ε u)).symm

/-- Accessibility of the prior mass near `W₀` forces the chart family to be nonempty. -/
theorem nonempty_ι (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)) :
    Nonempty A.ι := by
  classical
  by_contra hempty
  rw [not_nonempty_iff] at hempty
  have hT := A.transport_identity
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hT
  have hWm : MeasurableSet W := A.W_closed.measurableSet
  have hS : MeasurableSet (W ∩ {w | K w < A.δ}) := by
    have : W ∩ {w | K w < A.δ} = W ∩ (A.U ∩ K ⁻¹' Iio A.δ) := by
      ext w
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iio]
      constructor
      · rintro ⟨hw, hK⟩; exact ⟨hw, A.W_subset hw, hK⟩
      · rintro ⟨hw, -, hK⟩; exact ⟨hw, hK⟩
    rw [this]
    exact hWm.inter
      (A.K_analytic.continuousOn.isOpen_inter_preimage A.U_open isOpen_Iio).measurableSet
  have h0 : ∫⁻ w in W, ENNReal.ofReal (A.χ w * φ w) = 0 := by
    have := congrArg (fun μ : Measure (Fin d → ℝ) ↦ μ univ) hT
    simpa [withDensity_apply _ MeasurableSet.univ] using this
  have h1 : ∫⁻ w in W ∩ {w | K w < A.δ}, ENNReal.ofReal (φ w) = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ w in W ∩ {w | K w < A.δ}, ENNReal.ofReal (φ w)
        = ∫⁻ w in W ∩ {w | K w < A.δ}, ENNReal.ofReal (A.χ w * φ w) := by
          refine setLIntegral_congr_fun hS fun w hw ↦ ?_
          rw [A.χ_eq_one hw.1 hw.2, one_mul]
      _ ≤ ∫⁻ w in W, ENNReal.ofReal (A.χ w * φ w) := lintegral_mono_set inter_subset_left
      _ = 0 := h0
  exact (hvol A.δ A.δ_pos).ne' h1

/-- The resolution atlas of the construction. -/
@[expose] noncomputable def toResolutionAtlas [Nonempty A.ι] : ResolutionAtlas K φ W where
  ι := A.ι
  b := A.rad
  b_pos α := (A.C α.1).rad_pos α.2.1
  k := A.expK
  h := A.expH
  active α := ((A.C α.1).ch α.2.1).q_ne
  g := A.chartMap
  g_analytic := A.analyticOnNhd_chartMap
  g_measurable := A.measurable_chartMap
  g_mapsTo := A.chartMap_mapsTo
  monomial α _ hu := A.K_chartMap α hu
  weight := A.weight
  weight_nonneg α _ hu := A.weight_nonneg α hu
  weight_contDiffOn := fun α ↦ (A.weight_contDiffOn α).of_le (by simp)
  χ := A.χ
  χ_measurable := A.χ_continuous.measurable
  χ_nonneg := A.χ_nonneg
  χ_le_one := A.χ_le_one
  δ := A.δ
  δ_pos := A.δ_pos
  χ_eq_one _ hw hK := A.χ_eq_one hw hK
  transport := A.transport_identity

/-- The nondegenerate atlas of the construction. -/
@[expose] noncomputable def toNondegenerateResolutionAtlas [Nonempty A.ι] :
    NondegenerateResolutionAtlas K φ W :=
  NondegenerateResolutionAtlas.ofWeightPos A.toResolutionAtlas A.weight_pos

end AtlasData

end SingularLearningTheory
