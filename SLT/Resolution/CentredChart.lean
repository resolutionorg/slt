/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Algebra.Module.Determinant
import SLT.Geometry.Manifold.MaximalAtlas
import SLT.Analytic.AnalyticIso.Inverse
import Hironaka.Analytic.Calculus.Det
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Normed.Module.Connected

/-!
# A centred chart in which a function and a Jacobian are monomials

Let `G : M → ℝ^d` be an analytic map from an analytic manifold, `P ∈ M` with `F (G P) = 0`, and
`φ` a chart of the maximal analytic atlas at `P` in which, near `φ P`, both `F ∘ G ∘ φ⁻¹` and the
Jacobian determinant of `G ∘ φ⁻¹` are monomials `y^α`, `y^β` times analytic functions not
vanishing at `φ P`. Then there is a chart `e` of the maximal analytic atlas centred at `P`
(`e P = 0`) in which, on the whole of its target, `F ∘ G ∘ e⁻¹ = S u^k` with `S = ±1` and the
Jacobian determinant of `G ∘ e⁻¹` is `b(u) u^h` with `b` analytic and nonvanishing
(`exists_centred_chart_of_eventually_monomial`): the chart clause (3) of Watanabe's
Theorem 2.3 [Wat09, Theorem 2.3], which is `SingularLearningTheory.Resolution.chart`.

The chart is built in two steps:

* translating `φ` by `-φ P` centres it; a monomial `y^α` becomes `(u + φ P)^α`, which is a unit
  times the monomial `u^k` in the coordinates that vanish at `φ P` (`prod_add_pow_eq_mul_prod_pow`);
* the unit `a` of `F ∘ G ∘ e⁻¹ = a · u^k` is absorbed into a coordinate `u_j` with `k_j ≥ 1` by
  `v_j = (S a)^{1/k_j} u_j` (`S` the sign of `a(0)`), after [Wat09, Remark 2.7], which absorbs
  `|a|` into `u₁`. The coordinate change is analytic with an analytic inverse near `0`
  (`Analytic.IsLocalAnalyticIsoAt.exists_openPartialHomeomorph`), and the chart is cut down to the
  image of a ball, on which the sign `S` is constant.
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped Manifold ContDiff

variable {d : ℕ}

/-- A monomial in `u + v₀` is a polynomial unit times the monomial in `u` whose exponents are
those of the coordinates vanishing at `v₀`. -/
private theorem prod_add_pow_eq_mul_prod_pow (v₀ u : Fin d → ℝ) (α : Fin d → ℕ) :
    ∏ i, (u + v₀) i ^ α i =
      (∏ i, if v₀ i = 0 then 1 else (u i + v₀ i) ^ α i) *
        ∏ i, u i ^ (if v₀ i = 0 then α i else 0) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  split_ifs with h <;> simp [h]

/-- The unit of `prod_add_pow_eq_mul_prod_pow` is analytic and does not vanish at `0`. -/
private theorem analyticAt_prod_ite_and_ne_zero (v₀ : Fin d → ℝ) (α : Fin d → ℕ) :
    AnalyticAt ℝ (fun u : Fin d → ℝ ↦ ∏ i, if v₀ i = 0 then 1 else (u i + v₀ i) ^ α i) 0 ∧
      (∏ i, if v₀ i = 0 then (1 : ℝ) else ((0 : Fin d → ℝ) i + v₀ i) ^ α i) ≠ 0 := by
  refine ⟨Finset.analyticAt_fun_prod _ fun i _ ↦ ?_, Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_⟩
  · split_ifs
    · exact analyticAt_const
    · exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i).analyticAt
        _).add analyticAt_const).pow _
  · split_ifs with h
    · exact one_ne_zero
    · simpa using pow_ne_zero _ h

/-- The determinant of the linear map `v ↦ v + e_j ((t - 1) v_j)` of `ℝ^d` is `t`: its matrix is
diagonal with `t` in place `j` and `1` elsewhere. -/
private theorem det_id_add_single_smul_proj (j : Fin d) (t : ℝ) :
    (ContinuousLinearMap.id ℝ (Fin d → ℝ) +
      (ContinuousLinearMap.pi (Pi.single j (ContinuousLinearMap.id ℝ ℝ)) :
        ℝ →L[ℝ] (Fin d → ℝ)).comp ((t - 1) • ContinuousLinearMap.proj j)).det = t := by
  classical
  set L := ContinuousLinearMap.id ℝ (Fin d → ℝ) +
    (ContinuousLinearMap.pi (Pi.single j (ContinuousLinearMap.id ℝ ℝ)) :
      ℝ →L[ℝ] (Fin d → ℝ)).comp ((t - 1) • ContinuousLinearMap.proj j) with hL
  have hmat : LinearMap.toMatrix' (L : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) =
      Matrix.diagonal (fun i ↦ if i = j then t else 1) := by
    ext i l
    rw [LinearMap.toMatrix'_apply, Matrix.diagonal_apply]
    simp only [hL, ContinuousLinearMap.coe_coe, add_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      smul_apply, ContinuousLinearMap.proj_apply, Pi.add_apply,
      ContinuousLinearMap.pi_apply, Pi.single_apply, smul_eq_mul]
    by_cases hil : i = l
    · subst hil
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    · by_cases hij : i = j
      · subst hij
        simp [hil]
      · simp [hil, hij]
  change LinearMap.det (L : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = t
  rw [← LinearMap.det_toMatrix', hmat, Matrix.det_diagonal, Finset.prod_ite_eq',
    ite_eq_left (Finset.mem_univ _)]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ω M] {G : M → (Fin d → ℝ)} {F : (Fin d → ℝ) → ℝ}

/-- The unit `a` of `F ∘ G ∘ φ⁻¹ = a · u^k`, on a connected open `V ∋ 0` inside the target of a
chart `φ` centred at `P`, is absorbed into a coordinate `u_j` with `k_j ≥ 1` by
`v_j = (S a)^{1/k_j} u_j`, `S` the sign of `a(0)` [Wat09, Remark 2.7]; the Jacobian's unit changes
by the coordinate change. -/
private theorem exists_chart_absorbing_unit (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω G)
    {φ : OpenPartialHomeomorph M (Fin d → ℝ)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M) {P : M} (hP : P ∈ φ.source)
    (hP0 : φ P = 0) (k h : Fin d → ℕ) (a b : (Fin d → ℝ) → ℝ) {V : Set (Fin d → ℝ)}
    (hV : IsOpen V) (h0V : (0 : Fin d → ℝ) ∈ V) (hVt : V ⊆ φ.target) (hVc : IsPreconnected V)
    (ha : AnalyticOnNhd ℝ a V) (ha0 : ∀ u ∈ V, a u ≠ 0) (hb : AnalyticOnNhd ℝ b V)
    (hb0 : ∀ u ∈ V, b u ≠ 0) (hk : ∃ i, 0 < k i)
    (hfa : ∀ u ∈ V, F (G (φ.symm u)) = a u * ∏ i, u i ^ k i)
    (hJ : ∀ u ∈ V, (fderiv ℝ (G ∘ φ.symm) u).det = b u * ∏ i, u i ^ h i) :
    ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M, P ∈ e.source ∧ e P = 0 ∧
      ∃ (S : ℝ) (k h : Fin d → ℕ) (b : (Fin d → ℝ) → ℝ),
        (S = 1 ∨ S = -1) ∧
        (∀ u ∈ e.target, F (G (e.symm u)) = S * ∏ j, u j ^ k j) ∧
        AnalyticOnNhd ℝ b e.target ∧ (∀ u ∈ e.target, b u ≠ 0) ∧
        ∀ u ∈ e.target, (fderiv ℝ (G ∘ e.symm) u).det = b u * ∏ j, u j ^ h j := by
  classical
  obtain ⟨j, hkj⟩ := hk
  -- the sign of `a` on the connected `V`
  set S : ℝ := if 0 < a 0 then 1 else -1 with hSdef
  have hS : S = 1 ∨ S = -1 := by
    rw [hSdef]
    split_ifs <;> simp
  have hSa : ∀ u ∈ V, 0 < S * a u := by
    have hconn : (a '' V).OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hVc.image a ha.continuousOn)
    have h0 : (0 : ℝ) ∉ a '' V := by
      rintro ⟨x, hx, hx0⟩
      exact ha0 x hx hx0
    intro u hu
    rw [hSdef]
    split_ifs with hpos
    · rw [one_mul]
      rcases lt_or_ge 0 (a u) with hgt | hle
      · exact hgt
      · exact absurd (hconn.out ⟨u, hu, rfl⟩ ⟨0, h0V, rfl⟩ ⟨hle, hpos.le⟩) h0
    · rw [neg_one_mul, neg_pos]
      have hpos' : a 0 ≤ 0 := not_lt.mp hpos
      rcases lt_or_ge (a u) 0 with hlt | hge
      · exact hlt
      · exact absurd (hconn.out ⟨0, h0V, rfl⟩ ⟨u, hu, rfl⟩ ⟨hpos', hge⟩) h0
  have hSS : S * S = 1 := by
    rcases hS with h | h <;> rw [h] <;> norm_num
  -- the `k_j`-th root `c = (S a)^{1/k_j}`
  set c : (Fin d → ℝ) → ℝ := fun u ↦ Real.exp (Real.log (S * a u) * (k j : ℝ)⁻¹) with hcdef
  have hc0 : ∀ u, 0 < c u := fun u ↦ Real.exp_pos _
  have hkj' : (k j : ℝ) ≠ 0 := by exact_mod_cast hkj.ne'
  have hcpow : ∀ u ∈ V, c u ^ k j = S * a u := by
    intro u hu
    rw [hcdef]
    dsimp only
    rw [← Real.rpow_natCast, ← Real.exp_mul, inv_mul_cancel_right₀ hkj', Real.exp_log (hSa u hu)]
  have hcan : AnalyticOnNhd ℝ c V := fun u hu ↦ by
    have h1 : AnalyticAt ℝ (fun x ↦ S * a x) u := analyticAt_const.mul (ha u hu)
    have h2 : AnalyticAt ℝ (fun x ↦ Real.log (S * a x)) u :=
      AnalyticAt.comp (g := Real.log) (f := fun x ↦ S * a x) (x := u)
        (analyticAt_log (hSa u hu)) h1
    have h3 : AnalyticAt ℝ (fun x ↦ Real.log (S * a x) * (k j : ℝ)⁻¹) u :=
      h2.mul analyticAt_const
    exact analyticAt_rexp.comp h3
  -- the coordinate change `Ψ u = u + e_j ((c u - 1) u_j)`, i.e. `v_j = c u · u_j`, `v_i = u_i`
  set sj : ℝ →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.pi (Pi.single j (ContinuousLinearMap.id ℝ ℝ)) with hsj
  have hsj_apply : ∀ (t : ℝ) (i : Fin d), sj t i = if i = j then t else 0 := by
    intro t i
    rw [hsj, ContinuousLinearMap.pi_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  set Ψ : (Fin d → ℝ) → (Fin d → ℝ) := fun u ↦ u + sj ((c u - 1) * u j) with hΨ
  have hΨj : ∀ u, Ψ u j = c u * u j := fun u ↦ by
    rw [hΨ]
    dsimp only
    rw [Pi.add_apply, hsj_apply, ite_eq_left rfl]
    ring
  have hΨi : ∀ u i, i ≠ j → Ψ u i = u i := fun u i hij ↦ by
    rw [hΨ]
    dsimp only
    rw [Pi.add_apply, hsj_apply, ite_eq_right hij, add_zero]
  have hΨ0 : Ψ 0 = 0 := by
    rw [hΨ]
    dsimp only
    simp
  have hmono : ∀ (u : Fin d → ℝ) (m : Fin d → ℕ),
      ∏ i, Ψ u i ^ m i = c u ^ m j * ∏ i, u i ^ m i := by
    intro u m
    have h1 : ∏ i ∈ Finset.univ.erase j, Ψ u i ^ m i = ∏ i ∈ Finset.univ.erase j, u i ^ m i :=
      Finset.prod_congr rfl fun i hi ↦ by rw [hΨi u i (Finset.ne_of_mem_erase hi)]
    have h2 : ∏ i, Ψ u i ^ m i = Ψ u j ^ m j * ∏ i ∈ Finset.univ.erase j, Ψ u i ^ m i :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
    have h3 : ∏ i, u i ^ m i = u j ^ m j * ∏ i ∈ Finset.univ.erase j, u i ^ m i :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
    rw [h2, h3, h1, hΨj, mul_pow, mul_assoc]
  -- `Ψ` is a local analytic isomorphism at `0`
  have hcV : AnalyticAt ℝ c 0 := hcan 0 h0V
  have hproj : AnalyticAt ℝ (fun u : Fin d → ℝ ↦ u j) 0 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).analyticAt 0
  have hΨan : AnalyticAt ℝ Ψ 0 := by
    rw [hΨ]
    exact analyticAt_id.add ((sj.analyticAt _).comp ((hcV.sub analyticAt_const).mul hproj))
  have hdet : (fderiv ℝ Ψ 0).det = c 0 := by
    have hc' : HasFDerivAt (fun u ↦ c u - 1) (fderiv ℝ c 0) 0 :=
      hcV.differentiableAt.hasFDerivAt.sub_const 1
    have hp := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin d ↦ ℝ) j (0 : Fin d → ℝ)
    have h4 := hc'.mul hp
    have h5 := (hasFDerivAt_id (0 : Fin d → ℝ)).add (sj.hasFDerivAt.comp (0 : Fin d → ℝ) h4)
    have hdΨ : HasFDerivAt Ψ (fderiv ℝ Ψ 0) 0 := hΨan.differentiableAt.hasFDerivAt
    have heq := h5.unique hdΨ
    rw [← heq]
    simp only [Pi.zero_apply, zero_smul, add_zero]
    exact det_id_add_single_smul_proj j (c 0)
  have hiso : Analytic.IsLocalAnalyticIsoAt ℝ Ψ 0 :=
    .of_det_ne_zero hΨan (by rw [hdet]; exact (hc0 0).ne')
  obtain ⟨e, h0e, hecoe, hean, -, hesym, hedet⟩ := hiso.exists_openPartialHomeomorph
  have hean' : AnalyticOnNhd ℝ e e.source := by
    rw [hecoe]
    exact hean
  -- a ball `B` around `0` inside `V ∩ e.source`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hV.inter e.open_source) 0 ⟨h0V, h0e⟩
  set B := Metric.ball (0 : Fin d → ℝ) ε with hB
  have hBV : B ⊆ V := fun u hu ↦ (hball hu).1
  have hBe : B ⊆ e.source := fun u hu ↦ (hball hu).2
  have hBt : B ⊆ φ.target := fun u hu ↦ hVt (hBV hu)
  set φ' := (φ.restrOpen (φ.source ∩ φ ⁻¹' B) (φ.isOpen_inter_preimage Metric.isOpen_ball)).trans
    e with hφ'
  have hsrc : φ'.source = φ.source ∩ φ ⁻¹' B :=
    φ.restrOpen_trans_source_eq Metric.isOpen_ball e hBe
  have htgt : φ'.target = e '' B := φ.restrOpen_trans_target_eq Metric.isOpen_ball hBt e hBe
  have hφ'c : (⇑φ' : M → Fin d → ℝ) = e ∘ φ := by
    rw [hφ', OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_restrOpen]
  have hφ's : (⇑φ'.symm : (Fin d → ℝ) → M) = φ.symm ∘ e.symm := by
    rw [hφ', OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.coe_restrOpen_symm]
  have hrep : G ∘ φ'.symm = (G ∘ φ.symm) ∘ e.symm := by
    rw [hφ's]
    rfl
  have hPs : P ∈ φ.source ∩ φ ⁻¹' B :=
    ⟨hP, by rw [mem_preimage, hP0]; exact Metric.mem_ball_self hε⟩
  have hmaps : ∀ v ∈ e '' B, e.symm v ∈ B := by
    rintro v ⟨u, hu, rfl⟩
    rw [e.left_inv (hBe hu)]
    exact hu
  have hsub : e '' B ⊆ e.target := by
    rintro v ⟨u, hu, rfl⟩
    exact e.map_source (hBe hu)
  have hrep_an := analyticOnNhd_comp_symm_of_mem_maximalAtlas hG hφ
  refine ⟨φ', OpenPartialHomeomorph.restrOpen_trans_mem_maximalAtlas hφ _
      hean'.contDiffOn_of_completeSpace hesym.contDiffOn_of_completeSpace, hsrc ▸ hPs, ?_,
    S, k, h, fun v ↦ b (e.symm v) * (c (e.symm v) ^ h j)⁻¹ * (fderiv ℝ e.symm v).det, hS,
    ?_, ?_, ?_, ?_⟩
  · rw [hφ'c, Function.comp_apply, hP0, congr_fun hecoe 0, hΨ0]
  · rw [htgt]
    rintro v ⟨u, hu, rfl⟩
    rw [← Function.comp_apply (f := G), hrep, Function.comp_apply, Function.comp_apply,
      e.left_inv (hBe hu), hfa u (hBV hu), congr_fun hecoe u, hmono u k, hcpow u (hBV hu),
      ← mul_assoc, ← mul_assoc, hSS, one_mul]
  · rw [htgt]
    intro v hv
    have hu := hmaps v hv
    have hes : AnalyticAt ℝ e.symm v := hesym v (hsub hv)
    refine (((hb _ (hBV hu)).comp hes).mul ?_).mul
      (Analytic.analyticOnNhd_det_fderiv e.open_target hesym v (hsub hv))
    exact (((hcan _ (hBV hu)).comp hes).pow (h j)).inv (pow_ne_zero _ (hc0 _).ne')
  · rw [htgt]
    rintro v ⟨u, hu, rfl⟩
    beta_reduce
    rw [e.left_inv (hBe hu)]
    exact mul_ne_zero (mul_ne_zero (hb0 u (hBV hu)) (inv_ne_zero (pow_ne_zero _ (hc0 u).ne')))
      ((ContinuousLinearMap.isInvertible_iff_det_ne_zero _).1 (hedet _ (e.map_source (hBe hu))))
  · rw [htgt]
    rintro v ⟨u, hu, rfl⟩
    have hu' : e.symm (e u) = u := e.left_inv (hBe hu)
    have hdiff_rep : DifferentiableAt ℝ (G ∘ φ.symm) (e.symm (e u)) := by
      rw [hu']
      exact (hrep_an u (hBt hu)).differentiableAt
    have hdiff_e : DifferentiableAt ℝ e.symm (e u) :=
      (hesym _ (e.map_source (hBe hu))).differentiableAt
    have hcne : c u ^ h j ≠ 0 := pow_ne_zero _ (hc0 u).ne'
    have hdc : ∀ A B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ), (A.comp B).det = A.det * B.det :=
      fun A B ↦ LinearMap.det_comp _ _
    beta_reduce
    rw [hrep, fderiv_comp _ hdiff_rep hdiff_e, hdc, hu', hJ u (hBV hu), congr_fun hecoe u,
      hmono u h]
    field_simp

/-- **A centred chart with monomial forms.** If `G` is analytic, `F (G P) = 0`, and in a chart `φ`
of the maximal analytic atlas at `P`, near `φ P`, `F ∘ G ∘ φ⁻¹ = a · y^α` and
`det D(G ∘ φ⁻¹) = b · y^β` with `a`, `b` analytic and nonzero at `φ P`, then there is a chart `e`
of the maximal analytic atlas centred at `P` in which, on its whole target, `F ∘ G ∘ e⁻¹ = S u^k`
with `S = ±1` and `det D(G ∘ e⁻¹) = b' u^h` with `b'` analytic and nonvanishing: Watanabe's chart
clause [Wat09, Theorem 2.3 (3)]. -/
theorem exists_centred_chart_of_eventually_monomial
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω G) {φ : OpenPartialHomeomorph M (Fin d → ℝ)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M) {P : M} (hP : P ∈ φ.source)
    (hFP : F (G P) = 0) {α β : Fin d → ℕ} {a b : (Fin d → ℝ) → ℝ} (ha : AnalyticAt ℝ a (φ P))
    (ha0 : a (φ P) ≠ 0) (hb : AnalyticAt ℝ b (φ P)) (hb0 : b (φ P) ≠ 0)
    (hFa : ∀ᶠ y in 𝓝 (φ P), F (G (φ.symm y)) = a y * ∏ i, y i ^ α i)
    (hJb : ∀ᶠ y in 𝓝 (φ P), (fderiv ℝ (G ∘ φ.symm) y).det = b y * ∏ i, y i ^ β i) :
    ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M, P ∈ e.source ∧ e P = 0 ∧
      ∃ (S : ℝ) (k h : Fin d → ℕ) (b : (Fin d → ℝ) → ℝ),
        (S = 1 ∨ S = -1) ∧
        (∀ u ∈ e.target, F (G (e.symm u)) = S * ∏ j, u j ^ k j) ∧
        AnalyticOnNhd ℝ b e.target ∧ (∀ u ∈ e.target, b u ≠ 0) ∧
        ∀ u ∈ e.target, (fderiv ℝ (G ∘ e.symm) u).det = b u * ∏ j, u j ^ h j := by
  classical
  set v₀ := φ P with hv₀
  -- the chart `φ` translated by `-φ P`
  set τ : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) :=
    (Homeomorph.addRight (-v₀)).toOpenPartialHomeomorph with hτ
  have hτc : ContDiffOn ℝ ω τ τ.source :=
    (contDiff_id.add contDiff_const).contDiffOn
  have hτc' : ContDiffOn ℝ ω τ.symm τ.target :=
    (contDiff_id.add contDiff_const).contDiffOn
  set φ₁ := (φ.restrOpen φ.source φ.open_source).trans τ with hφ₁
  have hφ₁m : φ₁ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M :=
    OpenPartialHomeomorph.restrOpen_trans_mem_maximalAtlas hφ _ hτc hτc'
  have hφ₁s : ∀ u, φ₁.symm u = φ.symm (u + v₀) := fun u ↦ by
    simp [hφ₁, hτ, Homeomorph.addRight_symm]
  have hPφ₁ : P ∈ φ₁.source := by
    simp [hφ₁, hτ, hP]
  have hφ₁P : φ₁ P = 0 := by
    simp [hφ₁, hτ, hv₀]
  have h0t : (0 : Fin d → ℝ) ∈ φ₁.target := hφ₁P ▸ φ₁.map_source hPφ₁
  -- the monomial forms in the centred coordinates
  set k : Fin d → ℕ := fun i ↦ if v₀ i = 0 then α i else 0 with hk
  set h : Fin d → ℕ := fun i ↦ if v₀ i = 0 then β i else 0 with hh
  set wa : (Fin d → ℝ) → ℝ := fun u ↦ ∏ i, if v₀ i = 0 then 1 else (u i + v₀ i) ^ α i
  set wb : (Fin d → ℝ) → ℝ := fun u ↦ ∏ i, if v₀ i = 0 then 1 else (u i + v₀ i) ^ β i
  set a' : (Fin d → ℝ) → ℝ := fun u ↦ a (u + v₀) * wa u with ha'
  set b' : (Fin d → ℝ) → ℝ := fun u ↦ b (u + v₀) * wb u with hb'
  have htr : Tendsto (fun u : Fin d → ℝ ↦ u + v₀) (𝓝 0) (𝓝 v₀) := by
    simpa using (continuous_id.add continuous_const).tendsto (0 : Fin d → ℝ) (f := fun u ↦ u + v₀)
  have hshift : ∀ {f : (Fin d → ℝ) → ℝ}, AnalyticAt ℝ f v₀ →
      AnalyticAt ℝ (fun u ↦ f (u + v₀)) 0 := fun hf ↦ by
    refine AnalyticAt.comp (g := _) (f := fun u : Fin d → ℝ ↦ u + v₀) ?_
      (analyticAt_id.add analyticAt_const)
    simpa using hf
  obtain ⟨hwa, hwa0⟩ := analyticAt_prod_ite_and_ne_zero v₀ α
  obtain ⟨hwb, hwb0⟩ := analyticAt_prod_ite_and_ne_zero v₀ β
  have ha'a : AnalyticAt ℝ a' 0 := (hshift ha).mul hwa
  have hb'a : AnalyticAt ℝ b' 0 := (hshift hb).mul hwb
  have ha'0 : a' 0 ≠ 0 := mul_ne_zero (by simpa using ha0) hwa0
  have hb'0 : b' 0 ≠ 0 := mul_ne_zero (by simpa using hb0) hwb0
  have hFa' : ∀ᶠ u in 𝓝 0, F (G (φ₁.symm u)) = a' u * ∏ i, u i ^ k i := by
    filter_upwards [htr.eventually hFa] with u hu
    rw [hφ₁s, hu, ha', mul_assoc, ← prod_add_pow_eq_mul_prod_pow v₀ u α]
  have hJb' : ∀ᶠ u in 𝓝 0, (fderiv ℝ (G ∘ φ₁.symm) u).det = b' u * ∏ i, u i ^ h i := by
    filter_upwards [htr.eventually hJb] with u hu
    have hcomp : G ∘ φ₁.symm = fun u ↦ (G ∘ φ.symm) (u + v₀) := funext fun u ↦ by
      simp [hφ₁s]
    rw [hcomp, fderiv_comp_add_right, hu, hb', mul_assoc,
      ← prod_add_pow_eq_mul_prod_pow v₀ u β]
  -- a ball around `0` on which all of this holds
  have hev : ∀ᶠ u in 𝓝 (0 : Fin d → ℝ), u ∈ φ₁.target ∧ AnalyticAt ℝ a' u ∧ a' u ≠ 0 ∧
      AnalyticAt ℝ b' u ∧ b' u ≠ 0 ∧ F (G (φ₁.symm u)) = a' u * ∏ i, u i ^ k i ∧
      (fderiv ℝ (G ∘ φ₁.symm) u).det = b' u * ∏ i, u i ^ h i :=
    (show ∀ᶠ u in 𝓝 (0 : Fin d → ℝ), u ∈ φ₁.target from φ₁.open_target.mem_nhds h0t).and
      (ha'a.eventually_analyticAt.and
      ((ha'a.continuousAt.eventually_ne ha'0).and (hb'a.eventually_analyticAt.and
        ((hb'a.continuousAt.eventually_ne hb'0).and (hFa'.and hJb')))))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  -- some exponent of `F` is positive, since `F (G P) = 0`
  have hkpos : ∃ i, 0 < k i := by
    by_contra hcon
    push Not at hcon
    have h0 := (hball 0 (Metric.mem_ball_self hr)).2.2.2.2.2.1
    rw [hφ₁s, zero_add, hv₀, φ.left_inv hP, hFP] at h0
    have : ∏ i, (0 : Fin d → ℝ) i ^ k i = 1 :=
      Finset.prod_eq_one fun i _ ↦ by rw [Nat.le_zero.mp (hcon i), pow_zero]
    rw [this, mul_one] at h0
    exact ha'0 h0.symm
  exact exists_chart_absorbing_unit hG hφ₁m hPφ₁ hφ₁P k h a' b' Metric.isOpen_ball
    (Metric.mem_ball_self hr) (fun u hu ↦ (hball u hu).1) (convex_ball 0 r).isPreconnected
    (fun u hu ↦ (hball u hu).2.1) (fun u hu ↦ (hball u hu).2.2.1)
    (fun u hu ↦ (hball u hu).2.2.2.1) (fun u hu ↦ (hball u hu).2.2.2.2.1) hkpos
    (fun u hu ↦ (hball u hu).2.2.2.2.2.1) fun u hu ↦ (hball u hu).2.2.2.2.2.2

end SingularLearningTheory
