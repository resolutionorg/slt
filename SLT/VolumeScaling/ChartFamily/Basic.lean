/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.ChartFamily.Defs

/-!
# Chart families: the exponents of a chart and of a family

Elementary facts about the chart families with two-sided monomial bounds
(`ResolutionChartData`, `MonomialChartCover`), and their combinatorial exponents, from which the
general theorem (`MonomialChartCover.hasLLCExponentsOn_cover`) reads off the sublevel-volume
exponents of the loss on the covered neighborhood.

* The monomial `mon e` is nonnegative and continuous.
* A chart has positive upper constants, its box lies in a centered cube (`exists_cube_superset`),
  and a small centered cube in its box maps into any given neighborhood of `w` (`exists_subbox`).
* Each chart carries its least exponent `lam = min_{eᵢ ≠ 0} (hᵢ + 1)/eᵢ` over the active
  coordinates `{i : eᵢ ≠ 0}` and its multiplicity `theta`, the number of active coordinates
  attaining it.
* The combinatorial exponents of a family are the least `lam` (`combLam`) and, among the charts
  attaining it, the greatest `theta` (`combTheta`); one chart attains both (`exists_leading`).
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology ENNReal

namespace SingularLearningTheory

theorem mon_nonneg {d : ℕ} (e : Fin d → ℕ) (u : Fin d → ℝ) : 0 ≤ mon e u :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _

/-- **The monomial is continuous.** As a function of the
coordinate vector, `mon e u = ∏ᵢ |uᵢ|^{eᵢ}` is continuous: each factor is the (continuous)
coordinate projection composed with the absolute value, raised to a fixed natural power, and a
finite product of continuous functions is continuous. -/
theorem continuous_mon {d : ℕ} (e : Fin d → ℕ) : Continuous (mon e) := by
  unfold mon
  exact continuous_finsetProd _ fun i _ => ((continuous_apply i).abs).pow (e i)

namespace ResolutionChartData

variable {Ambient : Type*} [TopologicalSpace Ambient] {f : Ambient → ℝ} {w : Ambient}

/-- The upper loss constant is positive. -/
theorem Cf_pos (χ : ResolutionChartData Ambient f w) : 0 < χ.Cf :=
  lt_of_lt_of_le χ.cf_pos χ.cf_le_Cf

/-- The upper Jacobian constant is positive. -/
theorem CJ_pos (χ : ResolutionChartData Ambient f w) : 0 < χ.CJ :=
  lt_of_lt_of_le χ.cJ_pos χ.cJ_le_CJ

/-- The chart box sits inside a centered cube `[-R, R]^d` of some positive
radius `R`. This packages the boundedness field in the cube form the chart-local
read-off uses (the sup norm on `Fin d → ℝ` makes a closed ball a cube). -/
theorem exists_cube_superset (χ : ResolutionChartData Ambient f w) :
    ∃ R : ℝ, 0 < R ∧ χ.K ⊆ Set.univ.pi (fun _ : Fin χ.d => Set.Icc (-R) R) := by
  obtain ⟨R, hR, hsub⟩ := χ.K_bounded.subset_closedBall_lt 0 0
  refine ⟨R, hR, fun u hu => ?_⟩
  have hu' : ‖u‖ ≤ R := mem_closedBall_zero_iff.mp (hsub hu)
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro i
  have hi : |u i| ≤ R := by
    rw [← Real.norm_eq_abs]; exact (pi_norm_le_iff_of_nonneg hR.le).mp hu' i
  exact abs_le.mp hi

/-- The active coordinate set `{i : eᵢ ≠ 0}` is nonempty, since the loss
exponent vector is nonzero. -/
theorem exists_active (χ : ResolutionChartData Ambient f w) : ∃ i, χ.e i ≠ 0 := by
  simpa using Function.ne_iff.mp χ.e_ne_zero

/-- The active coordinate set `{i : eᵢ ≠ 0}` as a `Finset`. -/
def activeSet (χ : ResolutionChartData Ambient f w) : Finset (Fin χ.d) :=
  Finset.univ.filter (fun i => χ.e i ≠ 0)

theorem mem_activeSet (χ : ResolutionChartData Ambient f w) {i : Fin χ.d} :
    i ∈ χ.activeSet ↔ χ.e i ≠ 0 := by
  simp [activeSet]

theorem activeSet_nonempty (χ : ResolutionChartData Ambient f w) :
    χ.activeSet.Nonempty := by
  obtain ⟨i, hi⟩ := χ.exists_active
  exact ⟨i, χ.mem_activeSet.mpr hi⟩

/-- The per-coordinate ratio `(hᵢ + 1)/eᵢ`. -/
noncomputable def ratio (χ : ResolutionChartData Ambient f w) (i : Fin χ.d) : ℝ :=
  ((χ.h i : ℝ) + 1) / (χ.e i : ℝ)

/-- **The least exponent.** `λ = ⨅_{i : eᵢ ≠ 0} (hᵢ+1)/eᵢ`, the
least ratio over the (nonempty) active coordinate set. -/
noncomputable def lam (χ : ResolutionChartData Ambient f w) : ℝ :=
  χ.activeSet.inf' χ.activeSet_nonempty χ.ratio

/-- **The multiplicity.** `θ = #{i : eᵢ ≠ 0 and (hᵢ+1)/eᵢ = λ}`,
the number of active coordinates attaining the least ratio. -/
noncomputable def theta (χ : ResolutionChartData Ambient f w) : ℕ :=
  (χ.activeSet.filter (fun i => χ.ratio i = χ.lam)).card

/-- The least ratio is a lower bound on every active coordinate's ratio. -/
theorem lam_le_ratio (χ : ResolutionChartData Ambient f w) {i : Fin χ.d}
    (hi : i ∈ χ.activeSet) : χ.lam ≤ χ.ratio i :=
  Finset.inf'_le _ hi

/-- The least ratio is attained by some active coordinate. -/
theorem exists_ratio_eq_lam (χ : ResolutionChartData Ambient f w) :
    ∃ i ∈ χ.activeSet, χ.ratio i = χ.lam := by
  obtain ⟨i, hi, hval⟩ := χ.activeSet.exists_mem_eq_inf' χ.activeSet_nonempty χ.ratio
  exact ⟨i, hi, hval.symm⟩

/-- The multiplicity is at least one: the least ratio is attained. -/
theorem theta_pos (χ : ResolutionChartData Ambient f w) : 0 < χ.theta := by
  obtain ⟨i, hi, hval⟩ := χ.exists_ratio_eq_lam
  refine Finset.card_pos.mpr ⟨i, ?_⟩
  exact Finset.mem_filter.mpr ⟨hi, hval⟩

/-- **The continuity subbox.** If the chart's continuous
parametrization sends the origin into an open set `U`, there is a positive radius
`r` whose symmetric cube `[-r, r]^d` about the origin lies inside the chart box
`K` and whose image under the parametrization lies in `U`. The cube is the
`[-R, R]^n` shape the box-rescaling read-off (restriction to a smaller box)
uses. -/
theorem exists_subbox (χ : ResolutionChartData Ambient f w) {U : Set Ambient}
    (hU : IsOpen U) (hwU : w ∈ U) :
    ∃ r > 0, Set.univ.pi (fun _ : Fin χ.d => Set.Icc (-r) r) ⊆ χ.K ∧
      χ.φ '' (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-r) r) ⊆ U := by
  have hopen : IsOpen (χ.φ ⁻¹' U ∩ interior χ.K) :=
    (hU.preimage χ.φ_continuous).inter isOpen_interior
  have h0 : (0 : Fin χ.d → ℝ) ∈ χ.φ ⁻¹' U ∩ interior χ.K := by
    refine ⟨?_, χ.zero_mem_interior⟩
    simp only [Set.mem_preimage, χ.φ_zero]; exact hwU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  have hcube : Set.univ.pi (fun _ : Fin χ.d => Set.Icc (-(r / 2)) (r / 2))
      ⊆ Metric.ball (0 : Fin χ.d → ℝ) r := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hle : ‖u‖ ≤ r / 2 := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      have hi := hu i (Set.mem_univ i)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hi.1, hi.2⟩
    linarith
  refine ⟨r / 2, by positivity, ?_, ?_⟩
  · intro u hu
    exact interior_subset (hball (hcube hu)).2
  · rintro y ⟨u, hu, rfl⟩
    exact (hball (hcube hu)).1

end ResolutionChartData

namespace MonomialChartCover

variable {Ambient : Type*} [MeasurableSpace Ambient] [TopologicalSpace Ambient]
  {μ : Measure Ambient} {f : Ambient → ℝ} {w : Ambient}
  {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The combinatorial least exponent.** `combλ = ⨅_α λ_α`, the
least per-chart least-exponent over the (nonempty, finite) family. -/
noncomputable def combLam (D : MonomialChartCover Ambient μ f w ι) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun α => (D.chart α).lam)

/-- The charts attaining the combinatorial least exponent. -/
noncomputable def minimizers (D : MonomialChartCover Ambient μ f w ι) : Finset ι :=
  Finset.univ.filter (fun α => (D.chart α).lam = D.combLam)

theorem minimizers_nonempty (D : MonomialChartCover Ambient μ f w ι) :
    D.minimizers.Nonempty := by
  obtain ⟨β, _, hβ⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) (fun α => (D.chart α).lam)
  exact ⟨β, Finset.mem_filter.mpr ⟨Finset.mem_univ β, hβ.symm⟩⟩

/-- **The combinatorial multiplicity.** `combθ = max{θ_α : λ_α = combλ}`, the
greatest multiplicity among the charts attaining the least exponent. -/
noncomputable def combTheta (D : MonomialChartCover Ambient μ f w ι) : ℕ :=
  D.minimizers.sup' D.minimizers_nonempty (fun α => (D.chart α).theta)

/-- **Leading-chart attainment.** Some chart `β` realizes both
the combinatorial least exponent and the combinatorial multiplicity. -/
theorem exists_leading (D : MonomialChartCover Ambient μ f w ι) :
    ∃ β, (D.chart β).lam = D.combLam ∧ (D.chart β).theta = D.combTheta := by
  obtain ⟨β, hβmem, hβval⟩ :=
    Finset.exists_mem_eq_sup' D.minimizers_nonempty (fun α => (D.chart α).theta)
  exact ⟨β, (Finset.mem_filter.mp hβmem).2, hβval.symm⟩

end MonomialChartCover

end SingularLearningTheory
