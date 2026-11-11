/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.Analytic.UpdateMap
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorbing a unit into a coordinate ([Wat09, Remark 2.7])

[Hit26, Theorem 3.3.1] puts `F₀ = K` into the pure
monomial form `S u^k`, while a factor of a resolved product only comes as `a₀(u) u^k` with `a₀`
a nonvanishing unit (`Resolution/Factorisation.lean`). The [Wat09]'s Remark 2.7 removes the
unit by the coordinate change `v_j = |a₀(u)|^{1/k_j} u_j` (some `k_j ≥ 1`), `v_i = u_i`
otherwise: an analytic local diffeomorphism at `0` whose inverse `τ` satisfies
`a₀(τ v) (τ v)^k = ± v^k`. The inverse is analytic by the inverse function theorem
(`ContDiffAt.toOpenPartialHomeomorph`) and Mathlib's power series of an inverse
(`OpenPartialHomeomorph.hasFPowerSeriesAt_symm`).

| Thesis | Lean |
| --- | --- |
| [Hit26, Equation (3.3.1)] from `a₀ u^k` ([Wat09, Remark 2.7]) | |
| | `AnalyticAt.exists_unit_absorbing_coordinates` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped ContDiff

variable {d : ℕ}

/-- `f ^ r` is analytic where `f` is analytic and positive. No thesis counterpart. -/
private theorem _root_.AnalyticAt.rpow_const_of_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (hpos : 0 < f x) (r : ℝ) :
    AnalyticAt ℝ (fun u ↦ f u ^ r) x := by
  have hev : ∀ᶠ u in 𝓝 x, 0 < f u := hf.continuousAt.eventually (lt_mem_nhds hpos)
  have h : AnalyticAt ℝ (fun u ↦ Real.exp (Real.log (f u) * r)) x :=
    analyticAt_rexp.comp (((analyticAt_log hpos).comp hf).mul analyticAt_const)
  refine h.congr ?_
  filter_upwards [hev] with u hu
  exact (Real.rpow_def_of_pos hu r).symm

/-- `|f| ^ r` is analytic where `f` is analytic and nonzero. No thesis counterpart. -/
private theorem _root_.AnalyticAt.abs_rpow_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (h0 : f x ≠ 0) (r : ℝ) :
    AnalyticAt ℝ (fun u ↦ |f u| ^ r) x := by
  rcases h0.lt_or_gt with hneg | hpos
  · have hev : ∀ᶠ u in 𝓝 x, f u < 0 := hf.continuousAt.eventually (gt_mem_nhds hneg)
    refine ((hf.neg).rpow_const_of_pos (by simpa using hneg) r).congr ?_
    filter_upwards [hev] with u hu
    simp [abs_of_neg hu]
  · have hev : ∀ᶠ u in 𝓝 x, 0 < f u := hf.continuousAt.eventually (lt_mem_nhds hpos)
    refine (hf.rpow_const_of_pos hpos r).congr ?_
    filter_upwards [hev] with u hu
    simp [abs_of_pos hu]

/-- [Wat09, Remark 2.7]. [Hit26, Theorem 3.3.1],
the passage from `a₀(u) u^k` (a nonvanishing analytic unit times a monomial, `k_j ≥ 1`) to the
pure form [Hit26, Equation (3.3.1)]: there is an analytic local diffeomorphism
`Φ` of `ℝ^d` at `0` (analytic with analytic inverse on its source and target, `Φ 0 = 0`) whose
inverse `τ = Φ.symm` changes only the `j`-th coordinate (`τ v = update v j (v_j c(v))` with
`c` analytic and positive at `0`) and satisfies `a₀(τ v) (τ v)^k = S v^k` near `0`, `S = ±1`. -/
theorem _root_.AnalyticAt.exists_unit_absorbing_coordinates {a₀ : (Fin d → ℝ) → ℝ}
    (ha : AnalyticAt ℝ a₀ 0)
    (ha0 : a₀ 0 ≠ 0) {k : Fin d → ℕ} {j : Fin d} (hj : 0 < k j) :
    ∃ (Φ : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)) (c : (Fin d → ℝ) → ℝ) (S : ℝ),
      (0 : Fin d → ℝ) ∈ Φ.source ∧ Φ 0 = 0 ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      AnalyticAt ℝ c 0 ∧ 0 < c 0 ∧ (S = 1 ∨ S = -1) ∧
      (∀ᶠ v in 𝓝 0, Φ.symm v = updateMap j (fun v ↦ v j * c v) v) ∧
      ∀ᶠ v in 𝓝 0, a₀ (Φ.symm v) * ∏ i, Φ.symm v i ^ k i = S * ∏ i, v i ^ k i := by
  -- the scaling factor `s = |a₀|^{1/k_j}` and the coordinate change `t`
  set s : (Fin d → ℝ) → ℝ := fun u ↦ |a₀ u| ^ ((k j : ℝ)⁻¹) with hs_def
  have hs : AnalyticAt ℝ s 0 := ha.abs_rpow_const ha0 _
  have hs0 : 0 < s 0 := Real.rpow_pos_of_pos (abs_pos.mpr ha0) _
  have hspos : ∀ u, a₀ u ≠ 0 → 0 < s u := fun u hu ↦ Real.rpow_pos_of_pos (abs_pos.mpr hu) _
  have hspow : ∀ u, s u ^ k j = |a₀ u| := fun u ↦
    Real.rpow_inv_natCast_pow (abs_nonneg _) hj.ne'
  set t : (Fin d → ℝ) → (Fin d → ℝ) := updateMap j (fun u ↦ u j * s u) with ht_def
  have hproj : ∀ i : Fin d, AnalyticAt ℝ (fun u : Fin d → ℝ ↦ u i) (0 : Fin d → ℝ) := fun i ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i).analyticAt _
  have ht : AnalyticAt ℝ t 0 := analyticAt_updateMap ((hproj j).mul hs)
  have ht0 : t 0 = 0 := by
    funext i
    rw [ht_def, updateMap_apply]
    split_ifs <;> simp
  -- the derivative of `t` at `0` is the invertible diagonal map `(1, …, s 0, …, 1)`
  set E₀ : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.piCongrRight fun i ↦
    if i = j then ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (s 0) hs0.ne')
    else ContinuousLinearEquiv.refl ℝ ℝ with hE₀_def
  have hderiv_j : HasFDerivAt (fun u : Fin d → ℝ ↦ u j * s u)
      ((s 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j) 0 := by
    have h := (hasFDerivAt_apply (𝕜 := ℝ) j (0 : Fin d → ℝ)).mul hs.differentiableAt.hasFDerivAt
    simpa [Pi.mul_def] using h
  have hE₀ : HasFDerivAt t (E₀ : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) 0 := by
    convert hasFDerivAt_updateMap (j := j) hderiv_j using 1
    ext v i
    simp only [hE₀_def, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.piCongrRight_apply,
      updateMapDeriv, ContinuousLinearMap.pi_apply]
    split_ifs with hi
    · subst hi
      simp [ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
    · simp
  -- the inverse function theorem
  have hω : (ω : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_zero
  set Φ := ht.contDiffAt.toOpenPartialHomeomorph t hE₀ hω with hΦ_def
  have hΦcoe : (Φ : (Fin d → ℝ) → (Fin d → ℝ)) = t := rfl
  have h0src : (0 : Fin d → ℝ) ∈ Φ.source := ht.contDiffAt.mem_toOpenPartialHomeomorph_source hE₀ hω
  have hΦ0 : Φ 0 = 0 := by rw [hΦcoe, ht0]
  have h0tgt : (0 : Fin d → ℝ) ∈ Φ.target := hΦ0 ▸ Φ.map_source h0src
  set τ : (Fin d → ℝ) → (Fin d → ℝ) := fun v ↦ Φ.symm v with hτ_def
  have hτ0 : τ 0 = 0 := by
    calc τ 0 = Φ.symm (Φ 0) := by rw [hΦ0]
      _ = 0 := Φ.left_inv h0src
  -- analyticity of the inverse
  have hτ : AnalyticAt ℝ τ 0 := by
    obtain ⟨p, hp⟩ := ht
    have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ (Fin d → ℝ) (Fin d → ℝ)).symm E₀ := by
      have := hp.hasFDerivAt.unique hE₀
      rw [← this, LinearIsometryEquiv.symm_apply_apply]
    have := Φ.hasFPowerSeriesAt_symm h0src (hΦcoe ▸ hp) hp1
    rw [hΦ0] at this
    exact ⟨_, this⟩
  -- the factor `c` and the shape of `τ`
  have hτcont : ContinuousAt τ 0 := hτ.continuousAt
  have hsτ : ∀ᶠ v in 𝓝 0, a₀ (τ v) ≠ 0 := by
    have : ∀ᶠ u in 𝓝 (0 : Fin d → ℝ), a₀ u ≠ 0 := ha.continuousAt.eventually_ne ha0
    rw [← hτ0] at this
    exact hτcont.eventually this
  set c : (Fin d → ℝ) → ℝ := fun v ↦ (s (τ v))⁻¹ with hc_def
  have hc : AnalyticAt ℝ c 0 := by
    have : AnalyticAt ℝ s (τ 0) := by rw [hτ0]; exact hs
    exact (this.comp hτ).inv (by change s (τ 0) ≠ 0; rw [hτ0]; exact hs0.ne')
  have hc0 : 0 < c 0 := by rw [hc_def]; simp only [hτ0]; exact inv_pos.mpr hs0
  have hright : ∀ᶠ v in 𝓝 0, t (τ v) = v := by
    filter_upwards [Φ.open_target.mem_nhds h0tgt] with v hv
    rw [← hΦcoe]; exact Φ.right_inv hv
  have hshape : ∀ᶠ v in 𝓝 0, τ v = updateMap j (fun v ↦ v j * c v) v := by
    filter_upwards [hright, hsτ] with v hv hv0
    funext i
    have hi := congrFun hv i
    rw [ht_def, updateMap_apply] at hi
    rw [updateMap_apply]
    split_ifs at hi ⊢ with hij
    · subst hij
      rw [hc_def]
      have hpos := hspos _ hv0
      field_simp
      linarith [hi]
    · exact hi
  -- the sign
  set S : ℝ := if 0 < a₀ 0 then 1 else -1 with hS_def
  have hS : S = 1 ∨ S = -1 := by rw [hS_def]; split_ifs <;> simp
  have hsign : ∀ᶠ v in 𝓝 0, a₀ (τ v) * |a₀ (τ v)|⁻¹ = S := by
    rcases ha0.lt_or_gt with hneg | hpos
    · have : ∀ᶠ u in 𝓝 (0 : Fin d → ℝ), a₀ u < 0 := ha.continuousAt.eventually (gt_mem_nhds hneg)
      rw [← hτ0] at this
      filter_upwards [hτcont.eventually this] with v hv
      rw [abs_of_neg hv, inv_neg, mul_neg, mul_inv_cancel₀ hv.ne, hS_def,
        ite_eq_right (not_lt.mpr hneg.le)]
    · have : ∀ᶠ u in 𝓝 (0 : Fin d → ℝ), 0 < a₀ u := ha.continuousAt.eventually (lt_mem_nhds hpos)
      rw [← hτ0] at this
      filter_upwards [hτcont.eventually this] with v hv
      rw [abs_of_pos hv, mul_inv_cancel₀ hv.ne', hS_def, ite_eq_left hpos]
  have hmono : ∀ᶠ v in 𝓝 0, a₀ (τ v) * ∏ i, τ v i ^ k i = S * ∏ i, v i ^ k i := by
    filter_upwards [hshape, hsτ, hsign] with v hv hv0 hvS
    have hprod : ∏ i, τ v i ^ k i = c v ^ k j * ∏ i, v i ^ k i := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i ↦ τ v i ^ k i) (Finset.mem_univ j),
        ← Finset.mul_prod_erase Finset.univ (fun i ↦ v i ^ k i) (Finset.mem_univ j)]
      have hj' : τ v j = v j * c v := by rw [hv, updateMap_apply, ite_eq_left rfl]
      have hrest : ∏ i ∈ Finset.univ.erase j, τ v i ^ k i = ∏ i ∈ Finset.univ.erase j, v i ^ k i :=
        Finset.prod_congr rfl fun i hi ↦ by
          rw [hv, updateMap_apply, ite_eq_right (Finset.ne_of_mem_erase hi)]
      rw [hrest, hj', mul_pow]
      ring
    have hck : c v ^ k j = |a₀ (τ v)|⁻¹ := by
      rw [hc_def, inv_pow, hspow]
    rw [hprod, hck, ← mul_assoc, hvS]
  -- restrict `Φ` to an open neighbourhood of `0` on which it is analytic with analytic inverse
  have hN₀ : IsOpen (Φ.source ∩ {u | AnalyticAt ℝ t u} ∩
      (Φ.source ∩ Φ ⁻¹' {v | AnalyticAt ℝ τ v})) :=
    (Φ.open_source.inter (isOpen_analyticAt ℝ t)).inter
      (Φ.isOpen_inter_preimage (isOpen_analyticAt ℝ τ))
  set Φ' := Φ.restrOpen _ hN₀ with hΦ'_def
  have hΦ'src : Φ'.source = Φ.source ∩ (Φ.source ∩ {u | AnalyticAt ℝ t u} ∩
      (Φ.source ∩ Φ ⁻¹' {v | AnalyticAt ℝ τ v})) := Φ.restrOpen_source _ hN₀
  have hΦ'tgt : Φ'.target = Φ.target ∩ Φ.symm ⁻¹' (Φ.source ∩ {u | AnalyticAt ℝ t u} ∩
      (Φ.source ∩ Φ ⁻¹' {v | AnalyticAt ℝ τ v})) := rfl
  refine ⟨Φ', c, S, ?_, hΦ0, ?_, ?_, hc, hc0, hS, hshape, hmono⟩
  · rw [hΦ'src]
    exact ⟨h0src, ⟨h0src, ht⟩, h0src, by rw [mem_preimage, hΦ0]; exact hτ⟩
  · intro u hu
    rw [hΦ'src] at hu
    exact hu.2.1.2
  · intro v hv
    rw [hΦ'tgt] at hv
    have := hv.2.2.2
    rw [mem_preimage, Φ.right_inv hv.1] at this
    exact this

end SingularLearningTheory
