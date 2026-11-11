/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Hironaka.Manifold.Submanifold.Charts
public import SLT.Resolution.Hironaka
public import SLT.Resolution.Factorisation
public import SLT.Analysis.Analytic.UnitAbsorption
public import SLT.Geometry.Manifold.ChartTrans
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Monomialising charts of a simultaneous resolution ([Wat09, Theorem 2.8])

[Hit26, Theorem 3.3.1] for the functions
`F₀ = K, F₁ = φ₂, F₂, … = H_i` (the potential, the analytic factor of the prior, the functions
cutting out `W`), derived from a `Resolution` of the single function
`F = K φ₂ ∏ H_i`: at a point `P` of the resolution over `{K = 0}` there is a chart `e`
of the maximal analytic atlas centred at `P`, with a box `[-b, b]^d` in its target, on which
`K ∘ g ∘ e.symm = S₀ v^q` (pure, `S₀ = ±1`, [Wat09, Remark 2.7]), `φ₂ ∘ g ∘ e.symm = a_φ v^r`,
`H_i ∘ g ∘ e.symm = c_i v^{k^i}` and `det (g ∘ e.symm)' = b_J v^p`, all units analytic and
nonvanishing on an open neighbourhood `O` of the box. This is the chart-level content the
thesis's bookkeeping section starts from (the pure form for `K` is available
exactly at points over `{K = 0}`, which is where the charts are centred).

The chart restricted to `e⁻¹ O` (`MonomialChart.eO`) has target `O`, and when `K ∘ g ≥ 0` on `O`
the loss is `v^q` with every `q_j` even (`MonomialChart.S₀_eq_one_and_even_of_nonneg`).

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 3.3.1], conditions (3), at a point | |
| over `{F₀ = 0}`, from the single-function form | `MonomialChart`,
`SingularLearningTheory.Resolution.exists_monomialChart` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped Manifold ContDiff

variable {d N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]

/-- The closed box `[-b, b]^d`. -/
abbrev box (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) := Icc (fun _ ↦ -b) (fun _ ↦ b)

theorem mem_box {b : ℝ} {v : Fin d → ℝ} : v ∈ box d b ↔ ∀ j, v j ∈ Icc (-b) b :=
  ⟨fun h j ↦ ⟨h.1 j, h.2 j⟩, fun h ↦ ⟨fun j ↦ (h j).1, fun j ↦ (h j).2⟩⟩

/-- The box as the product of its sides, for the product measure. -/
theorem box_eq_pi (d : ℕ) (b : ℝ) : box d b = univ.pi fun _ ↦ Icc (-b) b :=
  (pi_univ_Icc _ _).symm

/-- A monomialising chart at `P`: conditions (3) of [Hit26,
Theorem 3.3.1] for `K, φ₂, H_i` in a chart `e` of the
maximal analytic atlas centred at `P`, on an open neighbourhood `O ⊆ e.target` of the box `[-b,
b]^d`, with the pure form for `K`. -/
structure MonomialChart (Kf φ₂ : (Fin d → ℝ) → ℝ) (H : Fin N → (Fin d → ℝ) → ℝ)
    (g : M → (Fin d → ℝ)) (P : M) where
  /-- The chart $e$ of the maximal analytic atlas of `M`, centered at `P`: $P$ lies in its source
  and $e(P) = 0$. -/
  e : OpenPartialHomeomorph M (Fin d → ℝ)
  he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M
  mem_source : P ∈ e.source
  e_P : e P = 0
  /-- The half-width $b > 0$ of the box $[-b, b]^d$ (`SingularLearningTheory.box`) in the target
  of $e$. -/
  b : ℝ
  b_pos : 0 < b
  /-- An open neighborhood of the box inside the target of $e$, on which the monomial forms below
  hold and their analytic units do not vanish. -/
  O : Set (Fin d → ℝ)
  O_open : IsOpen O
  box_subset : box d b ⊆ O
  O_subset : O ⊆ e.target
  /-- `K ∘ g ∘ e.symm = S₀ v^q` on `O`, `S₀ = ±1`, `q ≠ 0`. -/
  q : Fin d → ℕ
  /-- The sign $S_0 = \pm 1$ in $K \circ g \circ e^{-1} = S_0 v^q$ on `O`. -/
  S₀ : ℝ
  S₀_sign : S₀ = 1 ∨ S₀ = -1
  q_ne : ∃ j, 0 < q j
  K_eq : ∀ v ∈ O, Kf (g (e.symm v)) = S₀ * ∏ j, v j ^ q j
  /-- `φ₂ ∘ g ∘ e.symm = a_φ v^r` on `O`. -/
  r : Fin d → ℕ
  /-- The analytic unit $a_\varphi$ in $\varphi_2 \circ g \circ e^{-1} = a_\varphi v^r$ on `O`,
  nonvanishing there. -/
  aφ : (Fin d → ℝ) → ℝ
  aφ_analytic : AnalyticOnNhd ℝ aφ O
  aφ_ne : ∀ v ∈ O, aφ v ≠ 0
  φ₂_eq : ∀ v ∈ O, φ₂ (g (e.symm v)) = aφ v * ∏ j, v j ^ r j
  /-- `H_i ∘ g ∘ e.symm = c_i v^{k^i}` on `O`. -/
  kH : Fin N → Fin d → ℕ
  /-- The analytic units $c_i$ in $H_i \circ g \circ e^{-1} = c_i v^{k^i}$ on `O`, nonvanishing
  there. -/
  cH : Fin N → (Fin d → ℝ) → ℝ
  cH_analytic : ∀ i, AnalyticOnNhd ℝ (cH i) O
  cH_ne : ∀ i, ∀ v ∈ O, cH i v ≠ 0
  H_eq : ∀ i, ∀ v ∈ O, H i (g (e.symm v)) = cH i v * ∏ j, v j ^ kH i j
  /-- The Jacobian determinant of `g ∘ e.symm` is `b_J v^p` on `O`. -/
  p : Fin d → ℕ
  /-- The analytic unit $b_J$ in the Jacobian determinant $\det (g \circ e^{-1})' = b_J v^p$ on
  `O`, nonvanishing there. -/
  bJ : (Fin d → ℝ) → ℝ
  bJ_analytic : AnalyticOnNhd ℝ bJ O
  bJ_ne : ∀ v ∈ O, bJ v ≠ 0
  det_eq : ∀ v ∈ O, (fderiv ℝ (g ∘ e.symm) v).det = bJ v * ∏ j, v j ^ p j

/-- The monomial of `updateMap j (fun v ↦ v j * c v) v` picks up the factor `c v ^ m j`.
No thesis counterpart; used by `Resolution.exists_monomialChart`. -/
private theorem prod_pow_of_eq_updateMap {j : Fin d} {c : (Fin d → ℝ) → ℝ} {v w : Fin d → ℝ}
    (hw : w = updateMap j (fun v ↦ v j * c v) v) (m : Fin d → ℕ) :
    ∏ i, w i ^ m i = c v ^ m j * ∏ i, v i ^ m i := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i ↦ w i ^ m i) (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i ↦ v i ^ m i) (Finset.mem_univ j)]
  have hrest : ∏ i ∈ Finset.univ.erase j, w i ^ m i = ∏ i ∈ Finset.univ.erase j, v i ^ m i :=
    Finset.prod_congr rfl fun i hi ↦ by
      rw [hw, updateMap_apply, ite_eq_right (Finset.ne_of_mem_erase hi)]
  have hj : w j = v j * c v := by rw [hw, updateMap_apply, ite_eq_left rfl]
  rw [hrest, hj, mul_pow]
  ring

/-- The partial derivative `∂_j (v_j c(v)) = c(v) + v_j ∂_j c(v)`. No thesis counterpart; used by
`Resolution.exists_monomialChart`. -/
private theorem fderiv_coordMul_single {c : (Fin d → ℝ) → ℝ} {v : Fin d → ℝ} (j : Fin d)
    (hc : DifferentiableAt ℝ c v) :
    fderiv ℝ (fun v ↦ v j * c v) v (Pi.single j 1) = c v + v j * fderiv ℝ c v (Pi.single j 1) := by
  have h : HasFDerivAt (fun v ↦ v j * c v)
      (v j • fderiv ℝ c v + c v • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j) v :=
    (hasFDerivAt_apply (𝕜 := ℝ) j v).mul hc.hasFDerivAt
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  ring

/-- `v ↦ ∂_j (v_j c(v))` is analytic where `c` is. No thesis counterpart; used by
`Resolution.exists_monomialChart`. -/
private theorem analyticAt_fderiv_coordMul_single {c : (Fin d → ℝ) → ℝ} {v : Fin d → ℝ}
    (j : Fin d) (hc : AnalyticAt ℝ c v) :
    AnalyticAt ℝ (fun v ↦ fderiv ℝ (fun v ↦ v j * c v) v (Pi.single j 1)) v := by
  have hf : AnalyticAt ℝ (fun v : Fin d → ℝ ↦ v j * c v) v :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).analyticAt v).mul hc
  exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin d → ℝ)).analyticAt _).comp hf.fderiv

/-- [Hit26, Theorem 3.3.1], conditions (3) for the
functions `K, φ₂, H_i`, derived from a resolution `(V, M, g)` of the product `F = K φ₂ ∏ H_i`
([Wat09, Theorem 2.8] via [Wat09, Theorem 2.7] and [Wat09, Remark 2.7]): every point `P` of the
resolution over `{K = 0}` has a monomialising chart. -/
theorem Resolution.exists_monomialChart {F Kf φ₂ : (Fin d → ℝ) → ℝ}
    {H : Fin N → (Fin d → ℝ) → ℝ} (R : Resolution F)
    (hF : ∀ w ∈ R.U, F w = Kf w * φ₂ w * ∏ i, H i w) (hK : AnalyticOnNhd ℝ Kf R.U)
    (hφ : AnalyticOnNhd ℝ φ₂ R.U) (hH : ∀ i, AnalyticOnNhd ℝ (H i) R.U) {P : R.M}
    (hP : Kf (R.π P) = 0) : Nonempty (MonomialChart Kf φ₂ H R.π P) := by
  -- the chart of the resolution at `P`
  have hgPV : R.π P ∈ R.U := R.mem_U P
  have hFP : P ∈ R.π ⁻¹' {w | F w = 0} := by
    change F (R.π P) = 0
    rw [hF _ hgPV, hP, zero_mul, zero_mul]
  obtain ⟨e₀, he₀, hPsrc, hP0, S, k, h, b₀, hS, hFk, hb₀a, hb₀ne, hdet⟩ := R.chart P hFP
  have hS0 : S ≠ 0 := by rcases hS with rfl | rfl <;> norm_num
  have h0tgt : (0 : Fin d → ℝ) ∈ e₀.target := hP0 ▸ e₀.map_source hPsrc
  have he₀0 : e₀.symm 0 = P := by rw [← hP0, e₀.left_inv hPsrc]
  have hG : AnalyticOnNhd ℝ (R.π ∘ e₀.symm) e₀.target := by
    have h1 : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω (R.π ∘ e₀.symm) e₀.target :=
      R.analytic_π.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he₀)
    exact e₀.open_target.analyticOn_iff_analyticOnNhd.mp
      ((contDiffOn_omega_iff_analyticOn e₀.open_target.uniqueDiffOn).mp h1.contDiffOn)
  have hGV : ∀ u, R.π (e₀.symm u) ∈ R.U := fun u ↦ R.mem_U _
  -- the factors of `F ∘ π ∘ e₀.symm` as one family
  obtain ⟨Ff, hFf0, hFf1, hFf2⟩ : ∃ Ff : Fin (N + 2) → (Fin d → ℝ) → ℝ,
      Ff 0 = (fun u ↦ Kf (R.π (e₀.symm u))) ∧ Ff (Fin.succ 0) = (fun u ↦ φ₂ (R.π (e₀.symm u))) ∧
      ∀ i : Fin N, Ff i.succ.succ = fun u ↦ H i (R.π (e₀.symm u)) :=
    ⟨Fin.cons (fun u ↦ Kf (R.π (e₀.symm u)))
      (Fin.cons (fun u ↦ φ₂ (R.π (e₀.symm u))) fun i u ↦ H i (R.π (e₀.symm u))),
      Fin.cons_zero _ _, by simp, fun i ↦ by simp⟩
  have hFfa : ∀ i, AnalyticAt ℝ (Ff i) 0 := by
    have hG0 : AnalyticAt ℝ (R.π ∘ e₀.symm) 0 := hG 0 h0tgt
    intro i
    refine Fin.cases ?_ ?_ i
    · rw [hFf0]
      have : AnalyticAt ℝ Kf (R.π (e₀.symm 0)) := by rw [he₀0]; exact hK _ hgPV
      exact AnalyticAt.comp (f := R.π ∘ e₀.symm) this hG0
    intro i
    refine Fin.cases ?_ ?_ i
    · rw [hFf1]
      have : AnalyticAt ℝ φ₂ (R.π (e₀.symm 0)) := by rw [he₀0]; exact hφ _ hgPV
      exact AnalyticAt.comp (f := R.π ∘ e₀.symm) this hG0
    intro i
    rw [hFf2]
    have : AnalyticAt ℝ (H i) (R.π (e₀.symm 0)) := by rw [he₀0]; exact hH i _ hgPV
    exact AnalyticAt.comp (f := R.π ∘ e₀.symm) this hG0
  have hprodF : ∀ᶠ u in 𝓝 (0 : Fin d → ℝ), ∏ i, Ff i u = S * ∏ l, u l ^ k l := by
    filter_upwards [e₀.open_target.mem_nhds h0tgt] with u hu
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [hFf0, hFf1, hFf2]
    rw [← mul_assoc, ← hF _ (hGV u), hFk u hu]
  obtain ⟨Kexp, a, -, ha, hprodS, hFf⟩ :=
    exists_unit_factorization_pi (a := fun _ ↦ S) hFfa analyticAt_const hprodF
  have hprodS' : ∀ᶠ u in 𝓝 (0 : Fin d → ℝ), ∏ i, a i u = S := hprodS
  have ha0 : a 0 0 ≠ 0 := by
    have h0 : ∏ i, a i 0 = S := hprodS'.self_of_nhds
    have : ∏ i, a i 0 ≠ 0 := h0 ▸ hS0
    exact Finset.prod_ne_zero_iff.mp this 0 (Finset.mem_univ _)
  have hj : ∃ j, 0 < Kexp 0 j := by
    by_contra hc
    push Not at hc
    have h00 : Ff 0 0 = a 0 0 * ∏ l, (0 : Fin d → ℝ) l ^ Kexp 0 l := (hFf 0).self_of_nhds
    have hzero : ∀ l, Kexp 0 l = 0 := fun l ↦ Nat.le_zero.mp (hc l)
    simp only [hzero, pow_zero, Finset.prod_const_one, mul_one, hFf0, he₀0, hP] at h00
    exact ha0 h00.symm
  obtain ⟨j, hj'⟩ := hj
  -- absorb the unit of `K` into the `j`-th coordinate
  obtain ⟨Φ, c, S₀, h0Φ, hΦ0, hΦa, hΦsa, hc, hc0, hS₀, hshape, hmono⟩ :=
    AnalyticAt.exists_unit_absorbing_coordinates (ha 0) ha0 hj'
  have h0Φt : (0 : Fin d → ℝ) ∈ Φ.target := hΦ0 ▸ Φ.map_source h0Φ
  have hτ0 : Φ.symm 0 = 0 := by
    calc Φ.symm 0 = Φ.symm (Φ 0) := by rw [hΦ0]
      _ = 0 := Φ.left_inv h0Φ
  have hτa : AnalyticAt ℝ Φ.symm 0 := hΦsa 0 h0Φt
  have hτev : ∀ {p : (Fin d → ℝ) → Prop}, (∀ᶠ u in 𝓝 0, p u) → ∀ᶠ v in 𝓝 0, p (Φ.symm v) := by
    intro p hp
    apply hτa.continuousAt.eventually
    rwa [hτ0]
  -- the new chart
  have he : e₀.trans Φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.M :=
    mem_maximalAtlas_trans he₀ (mem_contDiffGroupoid_of_analytic Φ hΦa hΦsa)
  have hPe : P ∈ (e₀.trans Φ).source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hPsrc, by rw [mem_preimage, hP0]; exact h0Φ⟩
  have heP : e₀.trans Φ P = 0 := by
    rw [OpenPartialHomeomorph.trans_apply, hP0, hΦ0]
  have hesymm : ∀ v, (e₀.trans Φ).symm v = e₀.symm (Φ.symm v) := fun v ↦ by
    rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
  -- the Jacobian factor of the coordinate change at `0`
  have hD0 : fderiv ℝ (fun v ↦ v j * c v) 0 (Pi.single j 1) ≠ 0 := by
    rw [fderiv_coordMul_single j hc.differentiableAt]
    simpa using hc0.ne'
  -- one neighbourhood of `0` on which everything holds
  have hQ : ∀ᶠ v in 𝓝 (0 : Fin d → ℝ), v ∈ Φ.target ∧ Φ.symm v ∈ e₀.target ∧
      (∀ i, AnalyticAt ℝ (a i) (Φ.symm v)) ∧ ∏ i, a i (Φ.symm v) = S ∧
      (∀ i, Ff i (Φ.symm v) = a i (Φ.symm v) * ∏ l, Φ.symm v l ^ Kexp i l) ∧
      Φ.symm v = updateMap j (fun v ↦ v j * c v) v ∧
      a 0 (Φ.symm v) * ∏ i, Φ.symm v i ^ Kexp 0 i = S₀ * ∏ i, v i ^ Kexp 0 i ∧
      AnalyticAt ℝ c v ∧ 0 < c v ∧ AnalyticAt ℝ Φ.symm v ∧
      fderiv ℝ (fun v ↦ v j * c v) v (Pi.single j 1) ≠ 0 := by
    filter_upwards [Φ.open_target.mem_nhds h0Φt, hτev (e₀.open_target.mem_nhds h0tgt),
      hτev (Filter.eventually_all.mpr fun i ↦ (ha i).eventually_analyticAt), hτev hprodS',
      hτev (Filter.eventually_all.mpr hFf), hshape, hmono, hc.eventually_analyticAt,
      hc.continuousAt.eventually (lt_mem_nhds hc0), hτa.eventually_analyticAt,
      (analyticAt_fderiv_coordMul_single j hc).continuousAt.eventually_ne hD0] with
      v h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hQ
  have hbox : box d (ρ / 2) ⊆ Metric.ball (0 : Fin d → ℝ) ρ := by
    intro v hv
    rw [mem_ball_zero_iff]
    have hnorm : ‖v‖ ≤ ρ / 2 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨hv.1 i, hv.2 i⟩
    linarith
  have hOe : Metric.ball (0 : Fin d → ℝ) ρ ⊆ (e₀.trans Φ).target := by
    intro v hv
    rw [OpenPartialHomeomorph.trans_target]
    obtain ⟨h1, h2, -⟩ := hball (Metric.mem_ball.mp hv)
    exact ⟨h1, h2⟩
  have hane : ∀ v ∈ Metric.ball (0 : Fin d → ℝ) ρ, ∀ i, a i (Φ.symm v) ≠ 0 := by
    intro v hv i
    obtain ⟨-, -, -, h4, -⟩ := hball (Metric.mem_ball.mp hv)
    rw [← h4] at hS0
    exact Finset.prod_ne_zero_iff.mp hS0 i (Finset.mem_univ _)
  -- the units `a_i(τ v) c(v)^{K_i j}` are analytic and nonvanishing on the ball
  have hunit_a : ∀ i, AnalyticOnNhd ℝ (fun v ↦ a i (Φ.symm v) * c v ^ Kexp i j)
      (Metric.ball (0 : Fin d → ℝ) ρ) := by
    intro i v hv
    obtain ⟨-, -, h3, -, -, -, -, h8, -, h10, -⟩ := hball (Metric.mem_ball.mp hv)
    exact ((h3 i).comp h10).mul (h8.pow _)
  have hunit_ne : ∀ i, ∀ v ∈ Metric.ball (0 : Fin d → ℝ) ρ,
      a i (Φ.symm v) * c v ^ Kexp i j ≠ 0 := by
    intro i v hv
    obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := hball (Metric.mem_ball.mp hv)
    exact mul_ne_zero (hane v hv i) (pow_ne_zero _ h9.ne')
  -- the three monomial forms
  have hKeq : ∀ v ∈ Metric.ball (0 : Fin d → ℝ) ρ,
      Kf (R.π ((e₀.trans Φ).symm v)) = S₀ * ∏ l, v l ^ Kexp 0 l := by
    intro v hv
    obtain ⟨-, -, -, -, h5, -, h7, -⟩ := hball (Metric.mem_ball.mp hv)
    have h50 := h5 0
    simp only [hFf0] at h50
    rw [hesymm, h50, h7]
  have hφeq : ∀ v ∈ Metric.ball (0 : Fin d → ℝ) ρ, φ₂ (R.π ((e₀.trans Φ).symm v)) =
      (a (Fin.succ 0) (Φ.symm v) * c v ^ Kexp (Fin.succ 0) j) *
        ∏ l, v l ^ Kexp (Fin.succ 0) l := by
    intro v hv
    obtain ⟨-, -, -, -, h5, h6, -⟩ := hball (Metric.mem_ball.mp hv)
    have h51 := h5 (Fin.succ 0)
    simp only [hFf1] at h51
    rw [hesymm, h51, prod_pow_of_eq_updateMap h6]
    ring
  have hHeq : ∀ i, ∀ v ∈ Metric.ball (0 : Fin d → ℝ) ρ, H i (R.π ((e₀.trans Φ).symm v)) =
      (a i.succ.succ (Φ.symm v) * c v ^ Kexp i.succ.succ j) * ∏ l, v l ^ Kexp i.succ.succ l := by
    intro i v hv
    obtain ⟨-, -, -, -, h5, h6, -⟩ := hball (Metric.mem_ball.mp hv)
    have h5i := h5 i.succ.succ
    simp only [hFf2] at h5i
    rw [hesymm, h5i, prod_pow_of_eq_updateMap h6]
    ring
  -- the Jacobian determinant
  have hbJa : AnalyticOnNhd ℝ (fun v ↦ b₀ (Φ.symm v) * c v ^ h j *
      fderiv ℝ (fun v ↦ v j * c v) v (Pi.single j 1)) (Metric.ball (0 : Fin d → ℝ) ρ) := by
    intro v hv
    obtain ⟨-, h2, -, -, -, -, -, h8, -, h10, -⟩ := hball (Metric.mem_ball.mp hv)
    exact (((hb₀a _ h2).comp h10).mul (h8.pow _)).mul (analyticAt_fderiv_coordMul_single j h8)
  have hbJne : ∀ v ∈ Metric.ball (0 : Fin d → ℝ) ρ, b₀ (Φ.symm v) * c v ^ h j *
      fderiv ℝ (fun v ↦ v j * c v) v (Pi.single j 1) ≠ 0 := by
    intro v hv
    obtain ⟨-, h2, -, -, -, -, -, -, h9, -, h11⟩ := hball (Metric.mem_ball.mp hv)
    exact mul_ne_zero (mul_ne_zero (hb₀ne _ h2) (pow_ne_zero _ h9.ne')) h11
  have hdet' : ∀ v ∈ Metric.ball (0 : Fin d → ℝ) ρ,
      (fderiv ℝ (R.π ∘ (e₀.trans Φ).symm) v).det =
        (b₀ (Φ.symm v) * c v ^ h j * fderiv ℝ (fun v ↦ v j * c v) v (Pi.single j 1)) *
          ∏ l, v l ^ h l := by
    intro v hv
    obtain ⟨-, h2, -, -, -, h6, -, h8, -, h10, -⟩ := hball (Metric.mem_ball.mp hv)
    have hcomp : R.π ∘ (e₀.trans Φ).symm = (R.π ∘ e₀.symm) ∘ Φ.symm := by
      rw [OpenPartialHomeomorph.coe_trans_symm]
      rfl
    have hτeq : (Φ.symm : (Fin d → ℝ) → (Fin d → ℝ)) =ᶠ[𝓝 v]
        updateMap j (fun v ↦ v j * c v) :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hv) fun w hw ↦
        (hball (Metric.mem_ball.mp hw)).2.2.2.2.2.1
    have hcv : HasFDerivAt (fun v ↦ v j * c v) (fderiv ℝ (fun v ↦ v j * c v) v) v :=
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).analyticAt v).mul
        h8).differentiableAt.hasFDerivAt
    have hτd : fderiv ℝ Φ.symm v = updateMapDeriv j (fderiv ℝ (fun v ↦ v j * c v) v) := by
      rw [hτeq.fderiv_eq]
      exact (hasFDerivAt_updateMap hcv).fderiv
    rw [hcomp, fderiv_comp v (hG _ h2).differentiableAt h10.differentiableAt,
      ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      ← ContinuousLinearMap.det, ← ContinuousLinearMap.det, hdet _ h2, hτd, det_updateMapDeriv,
      prod_pow_of_eq_updateMap h6]
    ring
  exact ⟨⟨e₀.trans Φ, he, hPe, heP, ρ / 2, by positivity, Metric.ball 0 ρ, Metric.isOpen_ball,
    hbox, hOe, Kexp 0, S₀, hS₀, ⟨j, hj'⟩, hKeq, Kexp (Fin.succ 0), _, hunit_a _, hunit_ne _, hφeq,
    fun i ↦ Kexp i.succ.succ, _, fun i ↦ hunit_a _, fun i ↦ hunit_ne _, hHeq, h, _, hbJa, hbJne,
    hdet'⟩⟩

namespace MonomialChart

variable {Kf φ₂ : (Fin d → ℝ) → ℝ} {H : Fin N → (Fin d → ℝ) → ℝ} {g : M → (Fin d → ℝ)} {P : M}
  (c : MonomialChart Kf φ₂ H g P)

/-! ## The chart restricted to `e⁻¹ O` -/

/-- The domain `e⁻¹ O` of the chart. -/
@[expose] def domO : Set M := c.e.source ∩ c.e ⁻¹' c.O

theorem isOpen_domO : IsOpen c.domO := c.e.isOpen_inter_preimage c.O_open

theorem mem_domO {x : M} : x ∈ c.domO ↔ x ∈ c.e.source ∧ c.e x ∈ c.O := Iff.rfl

/-- The chart restricted to `e⁻¹ O`, whose target is `O` (`eO_target`). -/
@[expose] def eO : OpenPartialHomeomorph M (Fin d → ℝ) := c.e.restrOpen c.domO c.isOpen_domO

theorem eO_apply (x : M) : c.eO x = c.e x := rfl

theorem eO_symm_apply (v : Fin d → ℝ) : c.eO.symm v = c.e.symm v := rfl

theorem mem_eO_source {x : M} : x ∈ c.eO.source ↔ x ∈ c.e.source ∧ c.e x ∈ c.O := by
  rw [eO, OpenPartialHomeomorph.restrOpen_source]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1, h⟩⟩

theorem eO_mem_maximalAtlas : c.eO ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M := by
  rw [eO, OpenPartialHomeomorph.restrOpen_eq_restr]
  exact restr_mem_maximalAtlas _ c.he c.isOpen_domO

theorem eO_target : c.eO.target = c.O := by
  ext v
  change v ∈ c.e.target ∩ c.e.symm ⁻¹' c.domO ↔ v ∈ c.O
  constructor
  · rintro ⟨hv, hv'⟩
    have := (c.mem_domO.mp hv').2
    rwa [c.e.right_inv hv] at this
  · intro hv
    have hvt : v ∈ c.e.target := c.O_subset hv
    exact ⟨hvt, c.mem_domO.mpr ⟨c.e.map_target hvt, by rwa [c.e.right_inv hvt]⟩⟩

theorem zero_mem_O : (0 : Fin d → ℝ) ∈ c.O :=
  c.box_subset ⟨fun _ ↦ neg_nonpos.mpr c.b_pos.le, fun _ ↦ c.b_pos.le⟩

/-- [Wat09, Remark 2.6] (8), in the library's vocabulary (hironaka's `even_exponents_of_nonneg`): if
`K ∘ g ∘ e⁻¹ ≥ 0` on `O`, then `S₀ = 1` and every exponent `q_j` is even. Evaluate the monomial
form at `b • 1` and at `b • (1 with −1 in slot j)`, both in the box. -/
theorem S₀_eq_one_and_even_of_nonneg (hK : ∀ v ∈ c.O, 0 ≤ Kf (g (c.e.symm v))) :
    c.S₀ = 1 ∧ ∀ j, Even (c.q j) := by
  have hval : ∀ v : Fin d → ℝ, (∀ j, |v j| ≤ 1) → 0 ≤ c.S₀ * ∏ j, v j ^ c.q j := by
    intro v hv
    have hmem : c.b • v ∈ c.O := c.box_subset <| mem_box.2 fun j ↦ by
      rw [Pi.smul_apply, smul_eq_mul]
      refine abs_le.mp ?_
      rw [abs_mul, abs_of_pos c.b_pos]
      calc c.b * |v j| ≤ c.b * 1 := mul_le_mul_of_nonneg_left (hv j) c.b_pos.le
        _ = c.b := mul_one _
    have h1 := hK _ hmem
    rw [c.K_eq _ hmem] at h1
    have h2 : ∏ j, (c.b • v) j ^ c.q j = c.b ^ (∑ j, c.q j) * ∏ j, v j ^ c.q j := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
    rw [h2, mul_left_comm] at h1
    exact nonneg_of_mul_nonneg_right h1 (pow_pos c.b_pos _)
  have hS1 : c.S₀ = 1 := by
    have h1 := hval 1 fun j ↦ by simp
    simp only [Pi.one_apply, one_pow, Finset.prod_const_one, mul_one] at h1
    rcases c.S₀_sign with h | h
    · exact h
    · rw [h] at h1
      norm_num at h1
  refine ⟨hS1, fun i ↦ ?_⟩
  have h1 := hval (Function.update (1 : Fin d → ℝ) i (-1)) fun j ↦ by
    by_cases hji : j = i
    · subst hji; simp
    · simp [Function.update_of_ne hji]
  rw [hS1, one_mul, Finset.prod_eq_single i (fun j _ hji ↦ by simp [Function.update_of_ne hji])
    (fun h ↦ absurd (Finset.mem_univ i) h)] at h1
  simp only [Function.update_self] at h1
  rcases Nat.even_or_odd (c.q i) with he | ho
  · exact he
  · rw [ho.neg_one_pow] at h1
    norm_num at h1

end MonomialChart

end SingularLearningTheory
