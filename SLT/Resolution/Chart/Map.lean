/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Chart.Cover
public import SLT.Resolution.Surjective
public import SLT.Resolution.Orthant
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The chart maps of the atlas

For a monomialising chart `c` at a point of the resolution over `{K = 0}`
(`MonomialChart`) and an orthant `ε ∈ {±1}^d`, the chart map of the atlas is
`u ↦ g (e.symm (ε ⊙ u²))` on the cube `[0, √b]^d` ([Hit26,
Section 3.3.1]: "each orthant is analytically
isomorphic to `[0, b)^d`", with the substitution `v_j = u_j²` of the remark after
[Hit26, Theorem 3.3.1] making every exponent even). Outside a
slightly larger open cube the map is constant, so that it is a measurable total function that is
analytic on a neighbourhood of the cube. A *good* orthant is one whose open cube maps into `W`; by
the constant sign of the units `c_i` on the connected orthant piece, an orthant is good or its open
cube misses `W` entirely, and on a good orthant `K ∘ g_α = u^{2q}` exactly (`K ≥ 0` on `W` fixes the
sign).

| Thesis | Lean |
| --- | --- |
| [Hit26, Section 3.3.1], `U ∩ g⁻¹(W)` as orthants | |
| | `MonomialChart.chartMap`, `MonomialChart.IsGood`, `MonomialChart.isGood_or_disjoint` |
| `K ∘ g_α = u^{2k}` on a chart | `MonomialChart.Kf_chartMap_of_isGood` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

variable {d N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  {Kf φ₂ : (Fin d → ℝ) → ℝ} {H : Fin N → (Fin d → ℝ) → ℝ} {g : M → (Fin d → ℝ)} {P : M}

/-- A continuous nonvanishing function on a preconnected set has constant sign. No thesis
counterpart. -/
theorem _root_.IsPreconnected.pos_or_neg_of_ne_zero {E : Type*} [TopologicalSpace E] {S : Set E}
    (hS : IsPreconnected S) {f : E → ℝ} (hf : ContinuousOn f S) (hne : ∀ x ∈ S, f x ≠ 0) :
    (∀ x ∈ S, 0 < f x) ∨ ∀ x ∈ S, f x < 0 := by
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩⟩ := h
  have hx' : f x < 0 := lt_of_le_of_ne hfx (hne x hx)
  have hy' : 0 < f y := lt_of_le_of_ne hfy (hne y hy).symm
  obtain ⟨z, hz, hz0⟩ : (0 : ℝ) ∈ f '' S :=
    (hS.image f hf).Icc_subset (mem_image_of_mem f hx) (mem_image_of_mem f hy) ⟨hx'.le, hy'.le⟩
  exact hne z hz hz0

namespace MonomialChart

variable (c : MonomialChart Kf φ₂ H g P)

/-- A box strictly larger than `[-b, b]^d` still inside the open set `O`. -/
theorem exists_box_lt : ∃ b', c.b < b' ∧ box d b' ⊆ c.O := by
  obtain ⟨δ, hδ, hsub⟩ :=
    isCompact_Icc.exists_thickening_subset_open c.O_open c.box_subset
  have hb := c.b_pos
  refine ⟨c.b + δ / 2, by linarith, fun u hu ↦ hsub ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨fun j ↦ max (-c.b) (min c.b (u j)), ⟨fun j ↦ le_max_left _ _, fun j ↦ ?_⟩, ?_⟩
  · exact max_le (by linarith) (min_le_left _ _)
  · refine ((dist_pi_le_iff (by positivity)).mpr fun j ↦ ?_).trans_lt (half_lt_self hδ)
    obtain ⟨h1, h2⟩ := mem_box.1 hu j
    rw [Real.dist_eq, abs_le]
    rcases le_or_gt (u j) (-c.b) with h | h
    · rw [min_eq_right (h.trans (by linarith)), max_eq_left h]
      constructor <;> linarith
    rcases le_or_gt c.b (u j) with h' | h'
    · rw [min_eq_left h', max_eq_right (by linarith)]
      constructor <;> linarith
    · rw [min_eq_right h'.le, max_eq_right h.le]
      constructor <;> linarith

/-- The radius of a larger box inside `O`. -/
@[expose] noncomputable def b' : ℝ := Classical.choose c.exists_box_lt

theorem b_lt_b' : c.b < c.b' := (Classical.choose_spec c.exists_box_lt).1

theorem box_b'_subset : box d c.b' ⊆ c.O := (Classical.choose_spec c.exists_box_lt).2

theorem b'_pos : 0 < c.b' := c.b_pos.trans c.b_lt_b'

/-- The coordinate expression `g ∘ e.symm` of the resolution map. -/
@[expose] def Γ : (Fin d → ℝ) → (Fin d → ℝ) := g ∘ c.e.symm

private theorem Γ_apply (v : Fin d → ℝ) : c.Γ v = g (c.e.symm v) := rfl

theorem Γ_zero : c.Γ 0 = g P := by
  rw [Γ_apply, ← c.e_P, c.e.left_inv c.mem_source]

theorem Γ_analyticOnNhd
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) : AnalyticOnNhd ℝ c.Γ c.O := by
  have h1 : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω (g ∘ c.e.symm) c.e.target :=
    hg.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas c.he)
  exact (c.e.open_target.analyticOn_iff_analyticOnNhd.mp
    ((contDiffOn_omega_iff_analyticOn c.e.open_target.uniqueDiffOn).mp h1.contDiffOn)).mono
    c.O_subset

/-- Off the coordinate hyperplanes the resolved product does not vanish, so `e.symm v ∉ M₀`. -/
theorem F_Γ_ne_zero {F : (Fin d → ℝ) → ℝ} {V : Set (Fin d → ℝ)} (hgV : ∀ x, g x ∈ V)
    (hF : ∀ w ∈ V, F w = Kf w * φ₂ w * ∏ i, H i w) {v : Fin d → ℝ} (hv : v ∈ c.O)
    (hne : ∀ j, v j ≠ 0) : F (c.Γ v) ≠ 0 := by
  have hV : c.Γ v ∈ V := hgV _
  have hmono : ∀ m : Fin d → ℕ, ∏ j, v j ^ m j ≠ 0 := fun m ↦
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (hne j)
  have hS : c.S₀ ≠ 0 := by rcases c.S₀_sign with h | h <;> rw [h] <;> norm_num
  rw [hF _ hV, Γ_apply, c.K_eq v hv, c.φ₂_eq v hv]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero hS (hmono _))
    (mul_ne_zero (c.aφ_ne v hv) (hmono _))) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_)
  rw [c.H_eq i v hv]
  exact mul_ne_zero (c.cH_ne i v hv) (hmono _)

theorem Γ_injOn {F : (Fin d → ℝ) → ℝ} {V : Set (Fin d → ℝ)} (hgV : ∀ x, g x ∈ V)
    (hinj : InjOn g (g ⁻¹' {w | F w ≠ 0})) (hF : ∀ w ∈ V, F w = Kf w * φ₂ w * ∏ i, H i w) :
    InjOn c.Γ {v | v ∈ c.O ∧ ∀ j, v j ≠ 0} := by
  intro v hv v' hv' h
  have h1 : c.e.symm v ∈ g ⁻¹' {w | F w ≠ 0} := c.F_Γ_ne_zero hgV hF hv.1 hv.2
  have h2 : c.e.symm v' ∈ g ⁻¹' {w | F w ≠ 0} := c.F_Γ_ne_zero hgV hF hv'.1 hv'.2
  have h3 : c.e.symm v = c.e.symm v' := hinj h1 h2 h
  exact c.e.symm.injOn (c.O_subset hv.1) (c.O_subset hv'.1) h3

/-- The radius `√b` of the chart cube `[0, √b]^d`. -/
@[expose] noncomputable def rad : ℝ := Real.sqrt c.b

/-- The radius `√b'` of the open cube on which the chart map is given by the analytic formula. -/
@[expose] noncomputable def rad' : ℝ := Real.sqrt c.b'

theorem rad_pos : 0 < c.rad := Real.sqrt_pos.mpr c.b_pos

theorem rad_lt_rad' : c.rad < c.rad' := Real.sqrt_lt_sqrt c.b_pos.le c.b_lt_b'

theorem orthantSq_mem_O (ε : Fin d → Bool) {u : Fin d → ℝ} (hu : u ∈ obox d c.rad') :
    orthantSq ε u ∈ c.O := by
  refine c.box_b'_subset (mem_box.2 fun j ↦ ?_)
  obtain ⟨h1, h2⟩ := hu j (mem_univ j)
  have hrad : c.rad' ^ 2 = c.b' := Real.sq_sqrt c.b'_pos.le
  have hlt : u j ^ 2 < c.b' := hrad ▸ sq_lt_sq' h1 h2
  have h0 : 0 ≤ u j ^ 2 := sq_nonneg _
  simp only [orthantSq, orthantSign]
  split_ifs <;> constructor <;> linarith

theorem cube_subset_obox : cube d c.rad ⊆ obox d c.rad' := by
  intro u hu j _
  obtain ⟨h0, h1⟩ := mem_cube.1 hu j
  have := c.rad_lt_rad'
  have := c.rad_pos
  constructor <;> linarith

private theorem ocube_subset_obox : ocube d c.rad ⊆ obox d c.rad' := fun _ hu ↦
  c.cube_subset_obox (mem_cube.2 fun j ↦ ⟨(hu j (mem_univ j)).1.le, (hu j (mem_univ j)).2.le⟩)

open Classical in
/-- The chart map of the atlas for the orthant `ε`: `g (e.symm (ε ⊙ u²))` on the open cube
`(-√b', √b')^d`, the constant `g P` outside. -/
@[expose] noncomputable def chartMap (ε : Fin d → Bool) : (Fin d → ℝ) → (Fin d → ℝ) := fun u ↦
  if u ∈ obox d c.rad' then c.Γ (orthantSq ε u) else g P

theorem chartMap_eq (ε : Fin d → Bool) {u : Fin d → ℝ} (hu : u ∈ obox d c.rad') :
    c.chartMap ε u = c.Γ (orthantSq ε u) := ite_eq_left hu

theorem chartMap_zero (ε : Fin d → Bool) : c.chartMap ε 0 = g P := by
  have h0 : (0 : Fin d → ℝ) ∈ obox d c.rad' := zero_mem_obox (c.rad_pos.trans c.rad_lt_rad')
  have hsq : orthantSq ε 0 = 0 := by funext j; simp [orthantSq]
  rw [c.chartMap_eq ε h0, hsq, c.Γ_zero]

/-- The chart map agrees with the analytic formula on the open box. -/
private theorem chartMap_eventuallyEq (ε : Fin d → Bool) {u : Fin d → ℝ}
    (hu : u ∈ obox d c.rad') : c.chartMap ε =ᶠ[𝓝 u] fun w ↦ c.Γ (orthantSq ε w) :=
  Filter.eventuallyEq_of_mem ((isOpen_obox d c.rad').mem_nhds hu) fun _ hw ↦ c.chartMap_eq ε hw

private theorem analyticAt_formula
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) (ε : Fin d → Bool) {u : Fin d → ℝ}
    (hu : u ∈ obox d c.rad') :
    AnalyticAt ℝ (fun w ↦ c.Γ (orthantSq ε w)) u :=
  AnalyticAt.comp (f := orthantSq ε) (c.Γ_analyticOnNhd hg _ (c.orthantSq_mem_O ε hu))
    (analyticOnNhd_orthantSq ε u (mem_univ _))

private theorem analyticAt_chartMap
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) (ε : Fin d → Bool) {u : Fin d → ℝ}
    (hu : u ∈ obox d c.rad') :
    AnalyticAt ℝ (c.chartMap ε) u :=
  (c.analyticAt_formula hg ε hu).congr (c.chartMap_eventuallyEq ε hu).symm

theorem measurable_chartMap
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) (ε : Fin d → Bool) :
    Measurable (c.chartMap ε) := by
  classical
  have hcont : ContinuousOn (fun u ↦ c.Γ (orthantSq ε u)) (obox d c.rad') := fun u hu ↦
    (c.analyticAt_formula hg ε hu).continuousAt.continuousWithinAt
  have hmeas : MeasurableSet (obox d c.rad') := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo
  exact hcont.measurable_piecewise (g := fun _ ↦ g P) continuousOn_const hmeas

theorem chartMap_analyticOnNhd
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) (ε : Fin d → Bool) :
    AnalyticOnNhd ℝ (c.chartMap ε) (cube d c.rad) := fun _ hu ↦
  c.analyticAt_chartMap hg ε (c.cube_subset_obox hu)

theorem hasFDerivAt_chartMap
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) (ε : Fin d → Bool) {u : Fin d → ℝ}
    (hu : u ∈ obox d c.rad') :
    HasFDerivAt (c.chartMap ε) ((fderiv ℝ c.Γ (orthantSq ε u)).comp (orthantSqDeriv ε u)) u := by
  have hΓ : HasFDerivAt c.Γ (fderiv ℝ c.Γ (orthantSq ε u)) (orthantSq ε u) :=
    (c.Γ_analyticOnNhd hg _ (c.orthantSq_mem_O ε hu)).differentiableAt.hasFDerivAt
  exact (hΓ.comp u (hasFDerivAt_orthantSq ε u)).congr_of_eventuallyEq
    (c.chartMap_eventuallyEq ε hu)

/-- The Jacobian of the chart map on the open positive cube: `|b_J(v)| u^{2p} ∏ 2 u_j`. -/
theorem abs_det_fderiv_chartMap
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) (ε : Fin d → Bool) {u : Fin d → ℝ}
    (hu : u ∈ ocube d c.rad) :
    |(fderiv ℝ (c.chartMap ε) u).det|
      = |c.bJ (orthantSq ε u)| * (∏ j, u j ^ (2 * c.p j)) * ∏ j, 2 * u j := by
  have hu' : u ∈ obox d c.rad' := c.ocube_subset_obox hu
  have hu0 : ∀ j, 0 ≤ u j := fun j ↦ (hu j (mem_univ j)).1.le
  have hdet : (fderiv ℝ c.Γ (orthantSq ε u)).det
      = c.bJ (orthantSq ε u) * ∏ j, orthantSq ε u j ^ c.p j :=
    c.det_eq _ (c.orthantSq_mem_O ε hu')
  rw [(c.hasFDerivAt_chartMap hg ε hu').fderiv, ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, abs_mul, ← ContinuousLinearMap.det,
    ← ContinuousLinearMap.det, abs_det_orthantSqDeriv ε hu0, hdet, abs_mul, Finset.abs_prod]
  congr 2
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [orthantSq]
  rw [abs_pow, abs_mul, abs_orthantSign, one_mul, abs_pow, sq_abs, pow_mul]

theorem chartMap_injOn {F : (Fin d → ℝ) → ℝ} {V : Set (Fin d → ℝ)} (hgV : ∀ x, g x ∈ V)
    (hinj : InjOn g (g ⁻¹' {w | F w ≠ 0}))
    (hF : ∀ w ∈ V, F w = Kf w * φ₂ w * ∏ i, H i w) (ε : Fin d → Bool) :
    InjOn (c.chartMap ε) (ocube d c.rad) := by
  have hmaps : MapsTo (orthantSq ε) (ocube d c.rad) {v | v ∈ c.O ∧ ∀ j, v j ≠ 0} := fun u hu ↦
    ⟨c.orthantSq_mem_O ε (c.ocube_subset_obox hu), fun j ↦
      mul_ne_zero (orthantSign_ne_zero ε j) (pow_ne_zero _ (hu j (mem_univ j)).1.ne')⟩
  exact ((c.Γ_injOn hgV hinj hF).comp (orthantSq_injOn ε c.rad) hmaps).congr fun u hu ↦
    (c.chartMap_eq ε (c.ocube_subset_obox hu)).symm

/-- The monomial of `ε ⊙ u²` splits into the orthant sign and the even monomial of `u`. -/
private theorem prod_orthantSq_pow (ε : Fin d → Bool) (u : Fin d → ℝ) (m : Fin d → ℕ) :
    ∏ j, orthantSq ε u j ^ m j = (∏ j, orthantSign ε j ^ m j) * ∏ j, u j ^ (2 * m j) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [orthantSq]
  rw [mul_pow, pow_mul]

theorem Kf_chartMap (ε : Fin d → Bool) {u : Fin d → ℝ} (hu : u ∈ obox d c.rad') :
    Kf (c.chartMap ε u) = c.S₀ * (∏ j, orthantSign ε j ^ c.q j) * ∏ j, u j ^ (2 * c.q j) := by
  rw [c.chartMap_eq ε hu, Γ_apply, c.K_eq _ (c.orthantSq_mem_O ε hu), prod_orthantSq_pow,
    mul_assoc]

theorem φ₂_chartMap (ε : Fin d → Bool) {u : Fin d → ℝ} (hu : u ∈ obox d c.rad') :
    φ₂ (c.chartMap ε u)
      = c.aφ (orthantSq ε u) * (∏ j, orthantSign ε j ^ c.r j) * ∏ j, u j ^ (2 * c.r j) := by
  rw [c.chartMap_eq ε hu, Γ_apply, c.φ₂_eq _ (c.orthantSq_mem_O ε hu), prod_orthantSq_pow,
    mul_assoc]

theorem H_chartMap (i : Fin N) (ε : Fin d → Bool) {u : Fin d → ℝ} (hu : u ∈ obox d c.rad') :
    H i (c.chartMap ε u)
      = c.cH i (orthantSq ε u) * (∏ j, orthantSign ε j ^ c.kH i j) * ∏ j, u j ^ (2 * c.kH i j) := by
  rw [c.chartMap_eq ε hu, Γ_apply, c.H_eq i _ (c.orthantSq_mem_O ε hu), prod_orthantSq_pow,
    mul_assoc]

/-- A *good* orthant: the open cube maps into `W`. -/
@[expose] def IsGood (W : Set (Fin d → ℝ)) (ε : Fin d → Bool) : Prop :=
  ∀ u ∈ ocube d c.rad, c.chartMap ε u ∈ W

/-- The even monomial `u^{2m}` is positive on the open cube. -/
private theorem prod_pow_two_mul_pos {u : Fin d → ℝ} (hu : u ∈ ocube d c.rad) (m : Fin d → ℕ) :
    0 < ∏ j, u j ^ (2 * m j) :=
  Finset.prod_pos fun j _ ↦ pow_pos (hu j (mem_univ j)).1 _

private theorem prod_orthantSign_pow_ne_zero (ε : Fin d → Bool) (m : Fin d → ℕ) :
    ∏ j, orthantSign ε j ^ m j ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (orthantSign_ne_zero ε j)

/-- The image of an open box under the signed square map is preconnected. -/
private theorem isPreconnected_image_orthantSq (ε : Fin d → Bool) (a : ℝ) :
    IsPreconnected (orthantSq ε '' obox d a) :=
  (convex_pi fun _ _ ↦ convex_Ioo _ _).isPreconnected.image _
    ((analyticOnNhd_orthantSq ε).continuousOn.mono (subset_univ _))

private theorem isPreconnected_image_orthantSq_ocube (ε : Fin d → Bool) (a : ℝ) :
    IsPreconnected (orthantSq ε '' ocube d a) :=
  (convex_pi fun _ _ ↦ convex_Ioo _ _).isPreconnected.image _
    ((analyticOnNhd_orthantSq ε).continuousOn.mono (subset_univ _))

private theorem half_mem_ocube : (fun _ ↦ c.rad / 2 : Fin d → ℝ) ∈ ocube d c.rad := fun _ _ ↦
  ⟨half_pos c.rad_pos, half_lt_self c.rad_pos⟩

/-- [Hit26, Section 3.3.1]: because each
`H_i ∘ g` is a unit times a monomial, an orthant either maps into `W = {H_i ≥ 0}` (the
description holding on a set `U` containing the orthant's image) or misses it. -/
theorem isGood_or_disjoint {W U : Set (Fin d → ℝ)} (hWH : ∀ w ∈ U, (w ∈ W ↔ ∀ i, 0 ≤ H i w))
    (ε : Fin d → Bool) (hU : ∀ u ∈ ocube d c.rad, c.chartMap ε u ∈ U) :
    c.IsGood W ε ∨ ∀ u ∈ ocube d c.rad, c.chartMap ε u ∉ W := by
  by_cases hex : ∃ u₀ ∈ ocube d c.rad, c.chartMap ε u₀ ∈ W
  · left
    obtain ⟨u₀, hu₀, hW₀⟩ := hex
    have himg : orthantSq ε '' ocube d c.rad ⊆ c.O := by
      rintro _ ⟨u, hu, rfl⟩
      exact c.orthantSq_mem_O ε (c.ocube_subset_obox hu)
    intro u hu
    refine (hWH _ (hU u hu)).mpr fun i ↦ ?_
    have hne : ∀ v ∈ orthantSq ε '' ocube d c.rad,
        c.cH i v * ∏ j, orthantSign ε j ^ c.kH i j ≠ 0 :=
      fun v hv ↦ mul_ne_zero (c.cH_ne i v (himg hv)) (prod_orthantSign_pow_ne_zero ε _)
    have hcont : ContinuousOn (fun v ↦ c.cH i v * ∏ j, orthantSign ε j ^ c.kH i j)
        (orthantSq ε '' ocube d c.rad) :=
      ((c.cH_analytic i).continuousOn.mono himg).mul continuousOn_const
    have h₀ : 0 < c.cH i (orthantSq ε u₀) * ∏ j, orthantSign ε j ^ c.kH i j := by
      have hH := (hWH _ (hU u₀ hu₀)).mp hW₀ i
      rw [c.H_chartMap i ε (c.ocube_subset_obox hu₀)] at hH
      exact lt_of_le_of_ne (nonneg_of_mul_nonneg_left hH (c.prod_pow_two_mul_pos hu₀ _))
        (hne _ (mem_image_of_mem _ hu₀)).symm
    rcases IsPreconnected.pos_or_neg_of_ne_zero (isPreconnected_image_orthantSq_ocube ε c.rad)
      hcont hne with hpos | hneg
    · rw [c.H_chartMap i ε (c.ocube_subset_obox hu)]
      exact (mul_pos (hpos _ (mem_image_of_mem _ hu)) (c.prod_pow_two_mul_pos hu _)).le
    · exact absurd h₀ (not_lt.mpr (hneg _ (mem_image_of_mem _ hu₀)).le)
  · right
    push Not at hex
    exact hex

theorem mapsTo_of_isGood
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) {W : Set (Fin d → ℝ)} (hW : IsClosed W)
    {ε : Fin d → Bool} (hε : c.IsGood W ε) :
    MapsTo (c.chartMap ε) (cube d c.rad) W := by
  intro u hu
  have hcl : u ∈ closure (ocube d c.rad) := by
    have h : closure (ocube d c.rad) = cube d c.rad := by
      rw [ocube, cube_eq_pi]
      rw [closure_pi_set]
      exact Set.pi_congr rfl fun _ _ ↦ closure_Ioo c.rad_pos.ne
    rw [h]
    exact hu
  have hcont : ContinuousWithinAt (c.chartMap ε) (ocube d c.rad) u :=
    (c.analyticAt_chartMap hg ε (c.cube_subset_obox hu)).continuousAt.continuousWithinAt
  rw [← hW.closure_eq]
  exact closure_mono (image_subset_iff.mpr fun w hw ↦ hε w hw) (hcont.mem_closure_image hcl)

/-- On a good orthant `K ∘ g_α = u^{2q}`: the sign `S₀ ε^q` is `1` because `K ≥ 0` on `W`. -/
theorem Kf_chartMap_of_isGood {W : Set (Fin d → ℝ)} (hK : ∀ w ∈ W, 0 ≤ Kf w) {ε : Fin d → Bool}
    (hε : c.IsGood W ε) {u : Fin d → ℝ} (hu : u ∈ cube d c.rad) :
    Kf (c.chartMap ε u) = ∏ j, u j ^ (2 * c.q j) := by
  have habs : |c.S₀ * ∏ j, orthantSign ε j ^ c.q j| = 1 := by
    have h1 : |c.S₀| = 1 := by rcases c.S₀_sign with h | h <;> rw [h] <;> norm_num
    rw [abs_mul, Finset.abs_prod, h1, one_mul]
    exact Finset.prod_eq_one fun j _ ↦ by rw [abs_pow, abs_orthantSign, one_pow]
  have hK₀ := hK _ (hε _ c.half_mem_ocube)
  rw [c.Kf_chartMap ε (c.ocube_subset_obox c.half_mem_ocube)] at hK₀
  have hsign : 0 ≤ c.S₀ * ∏ j, orthantSign ε j ^ c.q j :=
    nonneg_of_mul_nonneg_left hK₀ (c.prod_pow_two_mul_pos c.half_mem_ocube _)
  have hone : c.S₀ * ∏ j, orthantSign ε j ^ c.q j = 1 := by
    rcases (abs_eq zero_le_one).mp habs with h | h
    · exact h
    · linarith
  rw [c.Kf_chartMap ε (c.cube_subset_obox hu), hone, one_mul]

/-- On a good orthant the unit of `φ₂` times the orthant sign is positive (`φ₂ ≥ 0` there). -/
theorem aφ_mul_sign_pos {W : Set (Fin d → ℝ)} (hφ : ∀ w ∈ W, 0 ≤ φ₂ w)
    {ε : Fin d → Bool} (hε : c.IsGood W ε) {u : Fin d → ℝ} (hu : u ∈ cube d c.rad) :
    0 < c.aφ (orthantSq ε u) * ∏ j, orthantSign ε j ^ c.r j := by
  have himg : orthantSq ε '' obox d c.rad' ⊆ c.O := by
    rintro _ ⟨w, hw, rfl⟩
    exact c.orthantSq_mem_O ε hw
  have hne : ∀ v ∈ orthantSq ε '' obox d c.rad', c.aφ v * ∏ j, orthantSign ε j ^ c.r j ≠ 0 :=
    fun v hv ↦ mul_ne_zero (c.aφ_ne v (himg hv)) (prod_orthantSign_pow_ne_zero ε _)
  have hcont : ContinuousOn (fun v ↦ c.aφ v * ∏ j, orthantSign ε j ^ c.r j)
      (orthantSq ε '' obox d c.rad') :=
    (c.aφ_analytic.continuousOn.mono himg).mul continuousOn_const
  have hu₀ : (fun _ ↦ c.rad / 2 : Fin d → ℝ) ∈ obox d c.rad' :=
    c.ocube_subset_obox c.half_mem_ocube
  have h₀ : 0 < c.aφ (orthantSq ε fun _ ↦ c.rad / 2) * ∏ j, orthantSign ε j ^ c.r j := by
    have hφ₀ := hφ _ (hε _ c.half_mem_ocube)
    rw [c.φ₂_chartMap ε hu₀] at hφ₀
    exact lt_of_le_of_ne
      (nonneg_of_mul_nonneg_left hφ₀ (c.prod_pow_two_mul_pos c.half_mem_ocube _))
      (hne _ (mem_image_of_mem _ hu₀)).symm
  rcases IsPreconnected.pos_or_neg_of_ne_zero (isPreconnected_image_orthantSq ε c.rad') hcont hne
    with hpos | hneg
  · exact hpos _ (mem_image_of_mem _ (c.cube_subset_obox hu))
  · exact absurd h₀ (not_lt.mpr (hneg _ (mem_image_of_mem _ hu₀)).le)

end MonomialChart

end SingularLearningTheory
