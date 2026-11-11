/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import SLT.PartialResolution.Structural.Terminal
import SLT.MeasureTheory.Measure.Lebesgue.CoordHyperplanes
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Partial resolutions from finitely many monomial charts

A monomial chart `IsMonomialChart F φ dom e h W` on a compact domain is a partial resolution of `F`
on the image `φ '' dom` with one chart (`PartialResolution.ofMonomialChart`). Its exceptional set
is the part `{y ∈ dom | y^h = 0}` of the domain where the Jacobian monomial vanishes, a closed
subset of the coordinate hyperplanes, off which the chart is injective with nonvanishing Jacobian
(`IsMonomialChart.injOn`, `IsMonomialChart.det_ne_zero`); the multiplicity is one off the image of
the exceptional set, which is null because the chart is differentiable.

Finitely many monomial charts on compact domains whose images cover a compact set `N` give a
monomial resolution of `F` on `N` (`PartialResolution.exists_isMonomial_of_subset_iUnion_image`):
the disjoint union of the one-chart resolutions (`PartialResolution.sigma`), restricted to `N`
(`PartialResolution.restrict`).
-/

public section

open Set MeasureTheory

namespace Analytic

variable {n : ℕ}

/-- A monomial is a continuous function of the point. -/
theorem continuous_monomialEval (h : Fin n →₀ ℕ) :
    Continuous fun y : Fin n → ℝ ↦ monomialEval y h := by
  simp_rw [monomialEval_eq_prod]
  exact continuous_finsetProd _ fun k _ ↦ (continuous_apply k).pow _

/-- The zero set of a monomial lies in the union of the coordinate hyperplanes, so it is null. -/
theorem volume_setOf_monomialEval_eq_zero (h : Fin n →₀ ℕ) :
    volume {y : Fin n → ℝ | monomialEval y h = 0} = 0 := by
  refine measure_mono_null (fun y hy ↦ ?_) (volume_coordHyperplanes n)
  rw [mem_ofPred_eq, monomialEval_eq_prod, Finset.prod_eq_zero_iff] at hy
  obtain ⟨k, -, hk⟩ := hy
  refine ⟨k, ?_⟩
  by_contra hk0
  exact pow_ne_zero _ hk0 hk

namespace PartialResolution

variable {F : (Fin n → ℝ) → ℝ} {φ : (Fin n → ℝ) → (Fin n → ℝ)} {dom W : Set (Fin n → ℝ)}
  {e h : Fin n →₀ ℕ}

/-- **A monomial chart on a compact domain is a partial resolution of its image**, with one chart,
the exceptional set `{y ∈ dom | y^h = 0}` where the Jacobian monomial vanishes, multiplicity one,
and as multiplicity null set the image of the exceptional set. -/
def ofMonomialChart (hc : IsMonomialChart F φ dom e h W) (hdom : IsCompact dom) :
    PartialResolution n F (φ '' dom) where
  K_compact := hdom.image_of_continuousOn (hc.analyticOnNhd.continuousOn.mono hc.subset)
  ι := Unit
  dom _ := dom
  dom_compact _ := hdom
  φ _ := φ
  smooth _ := ⟨W, hc.isOpen, hc.subset, hc.analyticOnNhd.contDiffOn hc.isOpen.uniqueDiffOn⟩
  mapsTo _ := mapsTo_image φ dom
  cover := by
    rw [iUnion_const, Set.sdiff_self]
    exact measure_empty
  E _ := dom ∩ {y | monomialEval y h = 0}
  E_subset _ := inter_subset_left
  E_closed _ := hdom.isClosed.inter (isClosed_eq (continuous_monomialEval h) continuous_const)
  E_null _ := measure_mono_null inter_subset_right (volume_setOf_monomialEval_eq_zero h)
  inj _ := hc.injOn.mono fun y hy ↦
    (⟨hc.subset hy.1, fun h0 ↦ hy.2 ⟨hy.1, h0⟩⟩ : y ∈ W ∧ monomialEval y h ≠ 0)
  jac_ne_zero _ := fun y hy ↦ hc.det_ne_zero (hc.subset hy.1) fun h0 ↦ hy.2 ⟨hy.1, h0⟩
  mult := 1
  multN := φ '' (dom ∩ {y | monomialEval y h = 0})
  multN_null := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (fun y hy ↦ (hc.analyticOnNhd y (hc.subset hy.1)).differentiableAt.differentiableWithinAt)
    (measure_mono_null inter_subset_right (volume_setOf_monomialEval_eq_zero h))
  mult_bound := by
    rintro y ⟨-, hyN⟩
    have hE : ∀ z ∈ dom, φ z = y → z ∈ W ∧ monomialEval z h ≠ 0 := fun z hz hzy ↦
      ⟨hc.subset hz, fun h0 ↦ hyN ⟨z, ⟨hz, h0⟩, hzy⟩⟩
    refine (encard_le_one_iff.mpr ?_).trans (by norm_num)
    rintro ⟨u, x⟩ ⟨u', x'⟩ ⟨hx, hφx⟩ ⟨hx', hφx'⟩
    obtain rfl : u = u' := Subsingleton.elim _ _
    exact congrArg (Prod.mk u) (hc.injOn (hE x hx hφx) (hE x' hx' hφx') (hφx.trans hφx'.symm))

/-- The one-chart partial resolution of a monomial chart is monomial. -/
theorem isMonomial_ofMonomialChart (hc : IsMonomialChart F φ dom e h W) (hdom : IsCompact dom) :
    (ofMonomialChart hc hdom).IsMonomial :=
  fun _ ↦ ⟨e, h, W, hc⟩

/-- **Monomial charts covering a compact set give a monomial resolution of it**: finitely many
monomial charts of `F` on compact domains whose images cover a compact `N` give a partial
resolution of `F` on `N` all of whose charts are monomial (the disjoint union of the one-chart
resolutions `ofMonomialChart`, restricted to `N`). -/
theorem exists_isMonomial_of_subset_iUnion_image {ι : Type} [Finite ι] {N : Set (Fin n → ℝ)}
    (hN : IsCompact N) {φ : ι → (Fin n → ℝ) → (Fin n → ℝ)} {dom : ι → Set (Fin n → ℝ)}
    (hc : ∀ i, ∃ (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)), IsMonomialChart F (φ i) (dom i) e h W)
    (hdom : ∀ i, IsCompact (dom i)) (hcov : N ⊆ ⋃ i, φ i '' dom i) :
    ∃ R : PartialResolution n F N, R.IsMonomial := by
  have := Fintype.ofFinite ι
  choose e h W hc using hc
  let S := sigma fun i ↦ ofMonomialChart (hc i) (hdom i)
  exact ⟨S.restrict hcov hN, forallChart_restrict S hcov hN (chartPredStable_isMonomialChart F)
    (forallChart_sigma _ fun i ↦ isMonomial_ofMonomialChart (hc i) (hdom i))⟩

end PartialResolution

end Analytic
