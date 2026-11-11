/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.EmpiricalProcess.LimitOfAnalytic
public import SLT.EmpiricalProcess.MajorantsOfExpansion
public import SLT.Probability.Moments.EmpiricalSumEven
import SLT.MeasureTheory.Integral.Lebesgue.Minkowski
public import SLT.FreeEnergy.FundamentalConditions

/-!
# [Wat09, Theorem 5.8] for every even `s`: the `s`-th moment of `sup |ψ_n|`

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 4.2.4], `s = 2m`, uniformly in `n` | |
| | `EmpiricalProcessLimit.momentBound_even`, |
| | `EmpiricalProcessLimit.momentBound_of_lsValuedAnalytic_even` |
| [Hit26, Lemma 4.2.4], `s = 4` | |
| | `EmpiricalProcessLimit.momentBound_four`, |
| | `EmpiricalProcessLimit.momentBound_of_lsValuedAnalytic` |

On a patch with an `L²(q)`-expansion whose coefficients lie in `L^{2m}(q)` with
`Σ_i c_i ‖b_i‖_{2m} < ∞`, the majorant `S_n = Σ_i c_i |Y^n_i|` of `sup_B |ψ_n|` has `2m`-th moment
bounded uniformly in `n` ([Wat09, Theorem 5.7] (2) for `s = 2m`,
`Probability/Moments/EmpiricalSumEven.lean`, and Minkowski in `L^{2m}`); over a finite cover of the
compact
parameter space, `E[sup_U |ψ_n|^{2m}] ≤ (Σ_i C_i^{1/(2m)})^{2m}`. This is the field `MomentBound
(2m)` of an `EmpiricalProcessLimit`; the expectation part of the free energy formula uses `s = 4`.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {q : Measure X}
  [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P] {Xs : ℕ → Ω → X}

namespace L2Expansion

variable {U : Type*} [PseudoMetricSpace U] {f : X → U → ℝ} {B : Set U} (E : L2Expansion q f B)

/-- [Hit26, Lemma 4.2.3] (2) and Minkowski: the `2m`-th moment of a
weighted series of the coefficient processes, uniformly in `n`. -/
theorem lintegral_tsum_coefficientProcess_pow_le (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) {m : ℕ} (hm : 1 ≤ m)
    (hs : E.HigherMoment (2 * m : ℝ≥0∞)) (w : E.ι → ℝ) (n : ℕ) :
    ∫⁻ ω, (∑' i, ENNReal.ofReal (w i) * ‖E.coefficientProcess Xs i n ω‖ₑ) ^ (2 * m) ∂P
      ≤ (∑' i, ENNReal.ofReal (w i) * (2 ^ (m + 1) * eLpNorm (E.b i) (2 * m : ℝ≥0∞) q))
          ^ (2 * m) := by
  have hm0 : (2 * m : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  refine (lintegral_tsum_pow_le
    (g := fun i ω ↦ ENNReal.ofReal (w i) * ‖E.coefficientProcess Xs i n ω‖ₑ)
    (fun i ↦ measurable_const.mul (E.measurable_coefficientProcess Xs hX i n).enorm)
    (by omega)).trans ?_
  gcongr with i
  push_cast
  have h1 : ∫⁻ ω, (ENNReal.ofReal (w i) * ‖E.coefficientProcess Xs i n ω‖ₑ) ^ (2 * m) ∂P
      = ENNReal.ofReal (w i) ^ (2 * m) * ∫⁻ ω, ‖E.coefficientProcess Xs i n ω‖ₑ ^ (2 * m) ∂P := by
    simp_rw [mul_pow]
    exact lintegral_const_mul _ ((E.measurable_coefficientProcess Xs hX i n).enorm.pow_const _)
  have hexp : ((2 * m : ℕ) : ℝ) * (1 / (2 * m : ℝ)) = 1 := by
    push_cast
    exact mul_one_div_cancel hm0
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_natCast (ENNReal.ofReal (w i)) (2 * m), ← ENNReal.rpow_mul, hexp,
    ENNReal.rpow_one]
  gcongr
  exact rpow_lintegral_enorm_pow_empiricalSum_le hX hlaw hind (E.b_measurable i) hm (hs.1 i) n

omit [IsProbabilityMeasure q] in
/-- The constant of the `2m`-th moment bound is finite. -/
theorem tsum_ofReal_c_mul_eLpNorm_ne_top {m : ℕ} (hs : E.HigherMoment (2 * m : ℝ≥0∞)) :
    ∑' i, ENNReal.ofReal (E.c i) * (2 ^ (m + 1) * eLpNorm (E.b i) (2 * m : ℝ≥0∞) q) ≠ ⊤ := by
  have : ∀ i, ENNReal.ofReal (E.c i) * (2 ^ (m + 1) * eLpNorm (E.b i) (2 * m : ℝ≥0∞) q)
      = ENNReal.ofReal (2 ^ (m + 1) * (E.c i * (eLpNorm (E.b i) (2 * m : ℝ≥0∞) q).toReal)) :=
    fun i ↦ by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (E.c_nonneg i),
        ENNReal.ofReal_toReal (hs.1 i).eLpNorm_ne_top, ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]
      ring
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun i ↦ mul_nonneg (by positivity) (mul_nonneg (E.c_nonneg i) ENNReal.toReal_nonneg))
    (hs.2.mul_left _)]
  exact ENNReal.ofReal_ne_top

/-- [Wat09, Theorem 5.8] (`s = 2m`) on one patch: the majorant `S_n` of `sup_B |ψ_n|` has `2m`-th
moment bounded uniformly in `n`. -/
theorem exists_majorant_even (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hind : iIndepFun Xs P) {m : ℕ} (hm : 1 ≤ m) (hs : E.HigherMoment (2 * m : ℝ≥0∞))
    (hB : TopologicalSpace.IsSeparable B) (hf : ∀ᵐ x ∂q, ContinuousOn (f x) B)
    {Ψ : ℕ → Ω → C(U, ℝ)} (hΨ : ∀ n, ∀ᵐ ω ∂P, ∀ u, Ψ n ω u = empiricalProcess q f Xs n ω u) :
    ∃ (S : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞), C ≠ ⊤ ∧ (∀ n, Measurable (S n)) ∧
      (∀ n, ∫⁻ ω, S n ω ^ (2 * m) ∂P ≤ C) ∧ ∀ n, ∀ᵐ ω ∂P, ∀ u ∈ B, ‖Ψ n ω u‖ₑ ≤ S n ω := by
  let M := E.patchMajorants Xs hX hlaw hind hB hf hΨ
  refine ⟨M.S,
    (∑' i, ENNReal.ofReal (E.c i) * (2 ^ (m + 1) * eLpNorm (E.b i) (2 * m : ℝ≥0∞) q)) ^ (2 * m),
    ENNReal.pow_ne_top (E.tsum_ofReal_c_mul_eLpNorm_ne_top hs), M.S_measurable, fun n ↦ ?_,
    M.enorm_le⟩
  exact E.lintegral_tsum_coefficientProcess_pow_le hX hlaw hind hm hs E.c n

end L2Expansion

namespace EmpiricalProcessLimit

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- [Hit26, Lemma 4.2.4] with `s = 2m`, uniformly in `n`: on a compact metric
parameter space with local expansions whose coefficients lie in `L^{2m}(q)`, the random continuous
function of an empirical-process limit satisfies `E[sup_U |Ψ_n|^{2m}] ≤ C` for all `n`. -/
theorem momentBound_even {U : Type*} [MetricSpace U] [CompactSpace U] {f : X → U → ℝ}
    (E : EmpiricalProcessLimit q f Xs P P') (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) {m : ℕ} (hm : 1 ≤ m)
    (hf_cont : ∀ᵐ x ∂q, Continuous (f x))
    (hloc : ∀ u : U, ∃ B : Set U, IsOpen B ∧ u ∈ B ∧
      ∃ E' : L2Expansion q f B, E'.HigherMoment (2 * m : ℝ≥0∞)) :
    E.MomentBound (2 * m) := by
  classical
  choose B hBo hBu hBE using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover B hBo fun u _ ↦ mem_iUnion.mpr ⟨u, hBu u⟩
  have hcover : ∀ u : U, ∃ i ∈ t, u ∈ B i := fun u ↦ by
    have := ht (mem_univ u)
    simpa only [mem_iUnion, exists_prop] using this
  have hmaj : ∀ i : t, ∃ (S : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞), C ≠ ⊤ ∧ (∀ n, Measurable (S n)) ∧
      (∀ n, ∫⁻ ω, S n ω ^ (2 * m) ∂P ≤ C) ∧
        ∀ n, ∀ᵐ ω ∂P, ∀ u ∈ B i, ‖E.Ψ n ω u‖ₑ ≤ S n ω := fun i ↦ by
    obtain ⟨E', hs⟩ := hBE i
    exact E'.exists_majorant_even hX hlaw hind hm hs
      (TopologicalSpace.IsSeparable.of_separableSpace _) (hf_cont.mono fun x hx ↦ hx.continuousOn)
      E.Ψ_ae_eq
  choose S C hC hSm hSC hS using hmaj
  refine ⟨(∑ i : t, C i ^ (1 / ((2 * m : ℕ) : ℝ))) ^ (2 * m),
    ENNReal.pow_ne_top (ENNReal.sum_ne_top.mpr fun i _ ↦
      ENNReal.rpow_ne_top_of_nonneg (by positivity) (hC i)), fun n ↦ ?_⟩
  calc ∫⁻ ω, (⨆ u, ‖E.Ψ n ω u‖ₑ) ^ (2 * m) ∂P ≤ ∫⁻ ω, (∑ i : t, S i n ω) ^ (2 * m) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_all_iff.mpr fun i : t ↦ hS i n] with ω hω
        gcongr
        refine iSup_le fun u ↦ ?_
        obtain ⟨i, hi, hui⟩ := hcover u
        exact (hω ⟨i, hi⟩ u hui).trans
          (Finset.single_le_sum (f := fun i : t ↦ S i n ω) (fun _ _ ↦ zero_le)
            (Finset.mem_univ _))
    _ ≤ (∑ i : t, (∫⁻ ω, S i n ω ^ (2 * m) ∂P) ^ (1 / ((2 * m : ℕ) : ℝ))) ^ (2 * m) :=
        lintegral_sum_pow_le (fun i ↦ hSm i n) Finset.univ (by omega)
    _ ≤ (∑ i : t, C i ^ (1 / ((2 * m : ℕ) : ℝ))) ^ (2 * m) := by
        gcongr with i
        exact hSC i n

/-- [Hit26, Lemma 4.2.4] with `s = 4`, uniformly in `n` (the case `m = 2` of
`momentBound_even`). -/
theorem momentBound_four {U : Type*} [MetricSpace U] [CompactSpace U] {f : X → U → ℝ}
    (E : EmpiricalProcessLimit q f Xs P P') (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P)
    (hf_cont : ∀ᵐ x ∂q, Continuous (f x))
    (hloc : ∀ u : U, ∃ B : Set U, IsOpen B ∧ u ∈ B ∧
      ∃ E' : L2Expansion q f B, E'.HigherMoment 4) :
    E.MomentBound 4 := by
  have h : (2 * ((2 : ℕ) : ℝ≥0∞)) = 4 := by norm_num
  exact E.momentBound_even hX hlaw hind (m := 2) (by norm_num) hf_cont
    (by simpa only [h] using hloc)

/-- [Hit26, Lemma 4.2.4] with `s = 2m` for `f` `L^{2m}(q)`-valued analytic on
a neighbourhood of the compact `W ⊆ ℝ^d`. -/
theorem momentBound_of_lsValuedAnalytic_even {d : ℕ} {W : Set (Fin d → ℝ)} (hW : IsCompact W)
    {f : X → (Fin d → ℝ) → ℝ} (E : EmpiricalProcessLimit q (fun x (w : W) ↦ f x w) Xs P P')
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P)
    (hf_cont : ∀ᵐ x ∂q, ContinuousOn (f x) W) {s : ℝ≥0∞} [Fact (1 ≤ s)] {m : ℕ} (hm : 1 ≤ m)
    (hsm : s = 2 * m) (hf : LsValuedAnalytic s q f W) :
    E.MomentBound (2 * m) := by
  subst hsm
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW
  refine E.momentBound_even hX hlaw hind hm ?_ (LsValuedAnalytic.loc ?_ hf)
  · filter_upwards [hf_cont] with x hx
    exact continuousOn_iff_continuous_domRestrict.mp hx
  · exact le_mul_of_one_le_right zero_le (by exact_mod_cast hm)

/-- [Hit26, Lemma 4.2.4] with `s = 4` for `f` `L⁴(q)`-valued analytic on a
neighbourhood of the compact `W ⊆ ℝ^d`. -/
theorem momentBound_of_lsValuedAnalytic {d : ℕ} {W : Set (Fin d → ℝ)} (hW : IsCompact W)
    {f : X → (Fin d → ℝ) → ℝ} (E : EmpiricalProcessLimit q (fun x (w : W) ↦ f x w) Xs P P')
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P)
    (hf_cont : ∀ᵐ x ∂q, ContinuousOn (f x) W) (hf : LsValuedAnalytic 4 q f W) :
    E.MomentBound 4 := by
  exact E.momentBound_of_lsValuedAnalytic_even hW hX hlaw hind hf_cont (m := 2) (by norm_num)
    (by norm_num) hf

end EmpiricalProcessLimit

end SingularLearningTheory
