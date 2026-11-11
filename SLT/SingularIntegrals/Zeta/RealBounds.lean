/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.TypeOfAtlas
public import SLT.Analysis.Mellin.ChartSum
import SLT.SingularIntegrals.DeterministicFreeEnergy
import SLT.SingularIntegrals.Resolution
public import SLT.Resolution.Atlas
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Real chart bounds at the leading zeta pole

All invariants and weight estimates use the
resolution atlas. One essential chart with positive origin weight gives the lower bound;
the finite sum of chart bounds gives the upper bound.
-/

public section

open MeasureTheory Set Finset Filter Topology

namespace SingularLearningTheory
namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
variable (R : ResolutionAtlas K φ W)

/-- The exponent $2k_{\alpha,j}x + h_{\alpha,j}$ of $u_j$ in the integrand
$u^{2k_\alpha x + h_\alpha}\tilde\varphi_\alpha(u)$ of the chart integral
`SingularLearningTheory.ResolutionAtlas.realChartMellin` of chart $\alpha$ at a real $x$. It
exceeds $-1$ for $x > -\lambda$
(`SingularLearningTheory.ResolutionAtlas.mellinExponent_gt_of_gt_rlct`). -/
@[expose] noncomputable def mellinExponent (α : R.ι) (x : ℝ) (j : Fin d) : ℝ :=
  2 * R.k α j * x + R.h α j

/-- The product $\prod_j b^{e_j + 1}/(e_j + 1)$, with the exponents $e_j$ of
`SingularLearningTheory.ResolutionAtlas.mellinExponent` at $x$. For $b > 0$ and every $e_j > -1$
it is the integral of the monomial $u^e$ over the cube $[0, b]^d$: the chart integral
`SingularLearningTheory.ResolutionAtlas.realChartMellin` with the chart weight replaced by $1$.
A bound $M$ on the chart weight bounds the chart integral by $M$ times this product
(`SingularLearningTheory.ResolutionAtlas.realChartMellin_le`). -/
@[expose] noncomputable def monomialMellinProduct (α : R.ι) (b x : ℝ) : ℝ :=
  ∏ j, b ^ (R.mellinExponent α x j + 1) / (R.mellinExponent α x j + 1)

/-- `SingularLearningTheory.ResolutionAtlas.monomialMellinProduct` with its pole of order
$m_\alpha$ at $-\lambda_\alpha$ removed: each primary denominator
$e_j + 1 = 2k_{\alpha,j}(x + \lambda_\alpha)$ is replaced by $2k_{\alpha,j}$, so that it is the
product times $(x + \lambda_\alpha)^{m_\alpha}$
(`SingularLearningTheory.ResolutionAtlas.monomialMellinProduct_mul_pow`). For $b > 0$ it is
continuous and positive at $-\lambda_\alpha$. -/
@[expose] noncomputable def monomialMellinRegular (α : R.ι) (b x : ℝ) : ℝ :=
  (∏ j ∈ R.primary α, b ^ (R.mellinExponent α x j + 1) / (2 * R.k α j)) *
  ∏ j ∈ (R.primary α)ᶜ,
    b ^ (R.mellinExponent α x j + 1) / (R.mellinExponent α x j + 1)

theorem mellinExponent_gt_of_gt_chartRlct (α : R.ι) {x : ℝ}
    (hx : -R.chartRlct α < x) (j : Fin d) : -1 < R.mellinExponent α x j := by
  rcases Nat.eq_zero_or_pos (R.k α j) with hk | hk
  · simp only [mellinExponent, hk, Nat.cast_zero, mul_zero, zero_mul, zero_add]
    exact neg_one_lt_zero.trans_le (Nat.cast_nonneg _)
  · have hact : j ∈ R.activeSet α := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hk⟩
    have hle : R.chartRlct α ≤ R.ratio α j := Finset.inf'_le _ hact
    have hk' : (0 : ℝ) < 2 * R.k α j := by positivity
    change R.chartRlct α ≤ ((R.h α j : ℝ) + 1) / (2 * R.k α j) at hle
    rw [le_div_iff₀ hk'] at hle
    dsimp only [mellinExponent]
    nlinarith

theorem mellinExponent_gt_of_gt_rlct {x : ℝ} (hx : -R.rlct < x)
    (α : R.ι) (j : Fin d) : -1 < R.mellinExponent α x j :=
  R.mellinExponent_gt_of_gt_chartRlct α
    ((neg_le_neg (R.rlct_le_chartRlct α)).trans_lt hx) j

theorem mellinExponent_add_one_primary (α : R.ι) {j : Fin d}
    (hj : j ∈ R.primary α) (x : ℝ) :
    R.mellinExponent α x j + 1 = 2 * R.k α j * (x + R.chartRlct α) := by
  have hk : (2 * (R.k α j : ℝ)) ≠ 0 := by
    have := R.k_pos_of_mem_primary hj
    positivity
  have hr := R.ratio_eq_of_mem_primary hj
  have he : (R.h α j : ℝ) + 1 = 2 * R.k α j * R.chartRlct α := by
    rw [div_eq_iff hk] at hr
    nlinarith [hr]
  dsimp only [mellinExponent]
  nlinarith [he]

theorem mellinExponent_add_one_secondary_pos (α : R.ι) {j : Fin d}
    (hj : j ∉ R.primary α) :
    0 < R.mellinExponent α (-R.chartRlct α) j + 1 := by
  have := R.two_mul_k_mul_chartRlct_lt_of_notMem_primary hj
  dsimp only [mellinExponent]
  linarith

/-- Exact cancellation of the primary denominators. -/
theorem monomialMellinProduct_mul_pow (α : R.ι) (b : ℝ) {x : ℝ}
    (hx : x ≠ -R.chartRlct α) :
    (x + R.chartRlct α) ^ R.chartMult α * R.monomialMellinProduct α b x =
      R.monomialMellinRegular α b x := by
  classical
  have hx' : x + R.chartRlct α ≠ 0 := fun h ↦ hx (by linarith)
  unfold monomialMellinProduct monomialMellinRegular
  rw [← Finset.prod_mul_prod_compl (R.primary α)
    (fun j ↦ b ^ (R.mellinExponent α x j + 1) / (R.mellinExponent α x j + 1))]
  have hS : (∏ j ∈ R.primary α,
      b ^ (R.mellinExponent α x j + 1) / (R.mellinExponent α x j + 1)) =
      (∏ j ∈ R.primary α, b ^ (R.mellinExponent α x j + 1) / (2 * R.k α j)) /
        (x + R.chartRlct α) ^ (R.primary α).card := by
    rw [← Finset.prod_const, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [R.mellinExponent_add_one_primary α hj, div_div,
      mul_comm (2 * (R.k α j : ℝ))]
  rw [hS]
  change (x + R.chartRlct α) ^ (R.primary α).card * _ = _
  field_simp

theorem monomialMellinRegular_pos (α : R.ι) {b : ℝ} (hb : 0 < b) :
    0 < R.monomialMellinRegular α b (-R.chartRlct α) := by
  unfold monomialMellinRegular
  refine mul_pos (Finset.prod_pos fun j hj ↦ div_pos (Real.rpow_pos_of_pos hb _) ?_)
    (Finset.prod_pos fun j hj ↦ div_pos (Real.rpow_pos_of_pos hb _) ?_)
  · have := R.k_pos_of_mem_primary hj
    positivity
  · exact R.mellinExponent_add_one_secondary_pos α (Finset.mem_compl.mp hj)

theorem continuousAt_monomialMellinRegular (α : R.ι) {b : ℝ} (hb : 0 < b) :
    ContinuousAt (R.monomialMellinRegular α b) (-R.chartRlct α) := by
  have hexp : ∀ j, Continuous (fun x ↦ R.mellinExponent α x j + 1) := fun j ↦ by
    unfold mellinExponent
    fun_prop
  have hpow : ∀ j, Continuous (fun x ↦ b ^ (R.mellinExponent α x j + 1)) := fun j ↦
    continuous_const.rpow (hexp j) fun _ ↦ Or.inl hb.ne'
  unfold monomialMellinRegular ContinuousAt
  refine Tendsto.mul (tendsto_finsetProd _ fun j _ ↦ ?_)
    (tendsto_finsetProd _ fun j hj ↦ ?_)
  · exact ((hpow j).tendsto _).div_const _
  · exact ((hpow j).tendsto _).div ((hexp j).tendsto _)
      (R.mellinExponent_add_one_secondary_pos α (Finset.mem_compl.mp hj)).ne'

/-- The normalized constant-amplitude integral has a positive limit at its own pole. -/
theorem tendsto_normalized_monomialMellinProduct (α : R.ι) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ ↦ (x + R.chartRlct α) ^ R.chartMult α *
      R.monomialMellinProduct α b x) (𝓝[>] (-R.chartRlct α))
      (𝓝 (R.monomialMellinRegular α b (-R.chartRlct α))) := by
  refine ((R.continuousAt_monomialMellinRegular α hb).tendsto.mono_left
    nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (R.monomialMellinProduct_mul_pow α b (ne_of_gt hx)).symm

/-- At the global pole, every monomial chart has a bounded normalized product.
This includes all nonessential charts; no positivity of their limits is asserted. -/
theorem exists_limit_global_normalized_monomialMellinProduct
    (α : R.ι) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, Tendsto (fun x : ℝ ↦ (x + R.rlct) ^ R.mult *
      R.monomialMellinProduct α b x) (𝓝[>] (-R.rlct)) (𝓝 C) := by
  rcases (R.rlct_le_chartRlct α).lt_or_eq with hlt | heq
  · have hexp : ∀ j, Continuous (fun x ↦ R.mellinExponent α x j + 1) := fun j ↦ by
      unfold mellinExponent
      fun_prop
    have hprod : ContinuousAt (R.monomialMellinProduct α b) (-R.rlct) := by
      unfold monomialMellinProduct ContinuousAt
      refine tendsto_finsetProd _ fun j _ ↦ ?_
      have hp := (continuous_const.rpow (hexp j) fun _ ↦ Or.inl hb.ne').tendsto (-R.rlct)
      refine hp.div ((hexp j).tendsto _) ?_
      have hg := R.mellinExponent_gt_of_gt_chartRlct α (neg_lt_neg hlt) j
      linarith
    have hc : ContinuousAt (fun x : ℝ ↦ (x + R.rlct) ^ R.mult *
        R.monomialMellinProduct α b x) (-R.rlct) :=
      (((continuous_id.add continuous_const).pow R.mult).continuousAt).mul hprod
    exact ⟨_, hc.tendsto.mono_left nhdsWithin_le_nhds⟩
  · have hα : R.chartRlct α = R.rlct := heq.symm
    have hn := R.chartMult_le_mult hα
    have hloc := R.tendsto_normalized_monomialMellinProduct α hb
    rw [hα] at hloc
    have hp : Tendsto (fun x : ℝ ↦ (x + R.rlct) ^ (R.mult - R.chartMult α))
        (𝓝[>] (-R.rlct)) (𝓝 ((-R.rlct + R.rlct) ^ (R.mult - R.chartMult α))) :=
      (((continuous_id.add continuous_const).pow _).tendsto _).mono_left nhdsWithin_le_nhds
    refine ⟨_, (hp.mul hloc).congr fun x ↦ ?_⟩
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]

/-- The integral $\int_{[0, b_\alpha]^d} u^{2k_\alpha x + h_\alpha}\tilde\varphi_\alpha(u)\,du$
of chart $\alpha$ at a real $x$, with $\tilde\varphi_\alpha$ the chart weight
`SingularLearningTheory.ResolutionAtlas.weight`. Since $K \circ g_\alpha = u^{2k_\alpha}$, it is
the term of chart $\alpha$ in the localized zeta function $\int K(w)^x\chi(w)\varphi(w)\,dw$, and
the value on the real axis of the complex chart integral
(`SingularLearningTheory.ResolutionAtlas.remainderZeta_eq_ofReal_realChartMellin`). Its
integrand is integrable for $x > -\lambda$. -/
@[expose] noncomputable def realChartMellin (α : R.ι) (x : ℝ) : ℝ :=
  ∫ u in cube d (R.b α), (∏ j, u j ^ R.mellinExponent α x j) * R.weight α u

theorem integrable_realChartMellin (α : R.ι) {x : ℝ} (hx : -R.rlct < x) :
    IntegrableOn (fun u ↦ (∏ j, u j ^ R.mellinExponent α x j) * R.weight α u)
      (cube d (R.b α)) :=
  (integrableOn_cube_rpow (R.mellinExponent_gt_of_gt_rlct hx α) (R.b_pos α)).mul_continuousOn
    (R.weight_continuousOn α) isCompact_Icc

theorem realChartMellin_nonneg (α : R.ι) (x : ℝ) : 0 ≤ R.realChartMellin α x := by
  refine setIntegral_nonneg measurableSet_Icc fun u hu ↦ ?_
  exact mul_nonneg
    (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
    (R.weight_nonneg α u hu)

theorem realChartMellin_le (α : R.ι) {M : ℝ}
    (hM : ∀ u ∈ cube d (R.b α), R.weight α u ≤ M)
    {x : ℝ} (hx : -R.rlct < x) :
    R.realChartMellin α x ≤ M * R.monomialMellinProduct α (R.b α) x := by
  have hi := integrableOn_cube_rpow (R.mellinExponent_gt_of_gt_rlct hx α) (R.b_pos α)
  calc R.realChartMellin α x
      ≤ ∫ u in cube d (R.b α), (∏ j, u j ^ R.mellinExponent α x j) * M := by
        refine setIntegral_mono_on (R.integrable_realChartMellin α hx) (hi.mul_const M)
          measurableSet_Icc fun u hu ↦ ?_
        exact mul_le_mul_of_nonneg_left (hM u hu)
          (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
    _ = M * R.monomialMellinProduct α (R.b α) x := by
      rw [integral_mul_const, integral_cube_rpow (R.mellinExponent_gt_of_gt_rlct hx α) (R.b_pos α)]
      exact mul_comm _ _

/-- Origin positivity yields a smaller cube with a positive constant weight floor. -/
theorem exists_weight_lower_cube (α : R.ι) (h0 : 0 < R.weight α 0) :
    ∃ b c : ℝ, 0 < b ∧ b ≤ R.b α ∧ 0 < c ∧
      ∀ u ∈ cube d b, c ≤ R.weight α u := by
  have hzero : (0 : Fin d → ℝ) ∈ cube d (R.b α) := ⟨fun _ ↦ le_rfl, fun _ ↦ (R.b_pos α).le⟩
  let c := R.weight α 0 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨δ, hδ, hnear⟩ :=
    Metric.continuousWithinAt_iff.mp (R.weight_continuousOn α 0 hzero) c hc
  let b := min (δ / 2) (R.b α)
  have hb : 0 < b := lt_min (half_pos hδ) (R.b_pos α)
  have hbb : b ≤ R.b α := min_le_right _ _
  refine ⟨b, c, hb, hbb, hc, fun u hu ↦ ?_⟩
  have huc : u ∈ cube d (R.b α) := mem_cube.2 fun j ↦
    ⟨(hu.1 j), (hu.2 j).trans hbb⟩
  have hud : dist u 0 < δ := by
    rw [dist_pi_lt_iff hδ]
    intro j
    rw [Real.dist_eq, Pi.zero_apply, sub_zero, abs_of_nonneg (hu.1 j)]
    exact ((hu.2 j).trans (min_le_left _ _)).trans_lt (half_lt_self hδ)
  have h := hnear huc hud
  rw [Real.dist_eq, abs_sub_lt_iff] at h
  dsimp [c] at *
  linarith

/-- Lower bound from one chart and a smaller cube. -/
theorem monomialMellinProduct_le_sum (α : R.ι) {b c : ℝ}
    (hb : 0 < b) (hbb : b ≤ R.b α)
    (hw : ∀ u ∈ cube d b, c ≤ R.weight α u)
    {x : ℝ} (hx : -R.rlct < x) :
    c * R.monomialMellinProduct α b x ≤ ∑ γ, R.realChartMellin γ x := by
  have hsub : cube d b ⊆ cube d (R.b α) :=
    Icc_subset_Icc le_rfl fun _ ↦ hbb
  have hi := R.integrable_realChartMellin α hx
  have hip := integrableOn_cube_rpow (R.mellinExponent_gt_of_gt_rlct hx α) hb
  calc c * R.monomialMellinProduct α b x
      = ∫ u in cube d b, (∏ j, u j ^ R.mellinExponent α x j) * c := by
        rw [integral_mul_const, integral_cube_rpow (R.mellinExponent_gt_of_gt_rlct hx α) hb]
        exact mul_comm _ _
    _ ≤ ∫ u in cube d b, (∏ j, u j ^ R.mellinExponent α x j) * R.weight α u := by
        refine setIntegral_mono_on (hip.mul_const c) (hi.mono_set hsub)
          measurableSet_Icc fun u hu ↦ ?_
        exact mul_le_mul_of_nonneg_left (hw u hu)
          (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
    _ ≤ R.realChartMellin α x :=
      setIntegral_mono_set hi
        ((ae_restrict_mem measurableSet_Icc).mono fun u hu ↦
          mul_nonneg
            (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
            (R.weight_nonneg α u hu)) hsub.eventuallyLE
    _ ≤ ∑ γ, R.realChartMellin γ x :=
      Finset.single_le_sum (fun γ _ ↦ R.realChartMellin_nonneg γ x) (Finset.mem_univ α)

/-- The actual assembled atlas supplies the hypothesis with any essential chart.
A general NondegenerateResolutionAtlas need not have positive weight at the origin. -/
theorem exists_scaled_realChartMellin_sum_bounds
    (hpos : ∃ α, R.IsEssential α ∧ 0 < R.weight α 0) :
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in 𝓝[>] (-R.rlct),
      c ≤ (x + R.rlct) ^ R.mult * (∑ α, R.realChartMellin α x) ∧
      (x + R.rlct) ^ R.mult * (∑ α, R.realChartMellin α x) ≤ C := by
  classical
  obtain ⟨α, hα, hα0⟩ := hpos
  obtain ⟨b, c, hb, hbb, hc, hw⟩ := R.exists_weight_lower_cube α hα0
  have hlo := (R.tendsto_normalized_monomialMellinProduct α hb).const_mul c
  rw [hα.1, hα.2] at hlo
  let L := c * R.monomialMellinRegular α b (-R.rlct)
  have hL : 0 < L := by
    dsimp [L]
    rw [← hα.1]
    exact mul_pos hc (R.monomialMellinRegular_pos α hb)
  have hlo' : Tendsto (fun x : ℝ ↦ (x + R.rlct) ^ R.mult *
      (c * R.monomialMellinProduct α b x)) (𝓝[>] (-R.rlct)) (𝓝 L) := by
    convert hlo using 1
    funext x
    ring
  choose M hMpos hM using R.exists_weight_le
  choose U hU using fun γ ↦ R.exists_limit_global_normalized_monomialMellinProduct γ (R.b_pos γ)
  have hhi : Tendsto (fun x : ℝ ↦ ∑ γ, M γ *
      ((x + R.rlct) ^ R.mult * R.monomialMellinProduct γ (R.b γ) x))
      (𝓝[>] (-R.rlct)) (𝓝 (∑ γ, M γ * U γ)) :=
    tendsto_finsetSum _ fun γ _ ↦ (hU γ).const_mul (M γ)
  refine ⟨L / 2, (∑ γ, M γ * U γ) + 1, half_pos hL, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    hlo'.eventually (eventually_gt_nhds (half_lt_self hL)),
    hhi.eventually (eventually_lt_nhds (lt_add_one _))] with x hx hl hu
  change -R.rlct < x at hx
  have hp : 0 ≤ (x + R.rlct) ^ R.mult := pow_nonneg (by linarith : 0 ≤ x + R.rlct) _
  constructor
  · exact hl.le.trans (mul_le_mul_of_nonneg_left
      (R.monomialMellinProduct_le_sum α hb hbb hw hx) hp)
  · refine le_trans ?_ hu.le
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun γ _ ↦ by
      have hh := mul_le_mul_of_nonneg_left (R.realChartMellin_le γ (hM γ) hx) hp
      nlinarith [hh]

end ResolutionAtlas
end SingularLearningTheory
