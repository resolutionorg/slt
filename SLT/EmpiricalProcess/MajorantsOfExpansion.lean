/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.EmpiricalProcess.LocalExpansion
public import SLT.Probability.Moments.EmpiricalSum
public import SLT.EmpiricalProcess.PatchMajorants
public import SLT.EmpiricalProcess.Modification
import SLT.MeasureTheory.Integral.Lebesgue.Minkowski
public import SLT.EmpiricalProcess.Defs

/-!
# [Wat09, Theorem 5.8] and the equicontinuity lemma on one patch, for `s = 2`

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 4.2.4], on one ball, `s = 2` | |
| | `L2Expansion.patchMajorants` (field `S`) |
| [Hit26, Lemma 4.2.8], on one ball, `s = 2` | |
| | `L2Expansion.patchMajorants` (field `R`) |

On a patch `B` with an `L²(q)`-expansion `f(x, u) = Σ_i b_i(x) m_i(u)`, the empirical process is
almost surely `ψ_n(u) = Σ_i Y^n_i m_i(u)` with the coefficient processes
`Y^n_i = n^{-1/2} Σ_{l<n} (b_i(X_l) − E b_i)` (`hasSum_coefficientProcess_mul`), so
`sup_B |ψ_n| ≤ Σ_i c_i |Y^n_i|` and `|ψ_n(u) − ψ_n(v)| ≤ (Σ_i lip_i |Y^n_i|) dist(u, v)`. [Wat09,
Theorem 5.7] (`‖Y^n_i‖_{L²(P)} ≤ ‖b_i‖_{L²(q)}`) and Minkowski's inequality bound the second moments
of the two majorants by `(Σ_i c_i ‖b_i‖₂)²` and `(Σ_i lip_i ‖b_i‖₂)²`, uniformly in `n`.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

variable {X Ω U : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [PseudoMetricSpace U]
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {f : X → U → ℝ} {B : Set U} (E : L2Expansion q f B) (Xs : ℕ → Ω → X)

namespace L2Expansion

/-- The coefficient processes `Y^n_i = n^{-1/2} Σ_{l<n} (b_i(X_l) − E b_i)` of the proof of
[Hit26, Lemma 4.2.4]. -/
@[expose] noncomputable def coefficientProcess (i : E.ι) (n : ℕ) (ω : Ω) : ℝ :=
  (√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (E.b i (Xs l ω) - ∫ x, E.b i x ∂q)

omit [IsProbabilityMeasure q] in
theorem measurable_coefficientProcess (hX : ∀ i, Measurable (Xs i)) (i : E.ι) (n : ℕ) :
    Measurable (E.coefficientProcess Xs i n) :=
  measurable_const.mul (Finset.measurable_sum _ fun l _ ↦
    ((E.b_measurable i).comp (hX l)).sub measurable_const)

omit [IsProbabilityMeasure q] in
theorem eLpNorm_b_ne_top (i : E.ι) : eLpNorm (E.b i) 2 q ≠ ⊤ := (E.b_memLp i).eLpNorm_ne_top

omit [IsProbabilityMeasure q] in
theorem ofReal_mul_eLpNorm (w : E.ι → ℝ) (hw : ∀ i, 0 ≤ w i) (i : E.ι) :
    ENNReal.ofReal (w i * (eLpNorm (E.b i) 2 q).toReal)
      = ENNReal.ofReal (w i) * eLpNorm (E.b i) 2 q := by
  rw [ENNReal.ofReal_mul (hw i), ENNReal.ofReal_toReal (E.eLpNorm_b_ne_top i)]

omit [IsProbabilityMeasure q] in
/-- `Σ_i w_i ‖b_i‖₂` as an extended real, finite. -/
theorem tsum_ofReal_mul_eLpNorm_ne_top {w : E.ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hs : Summable fun i ↦ w i * (eLpNorm (E.b i) 2 q).toReal) :
    ∑' i, ENNReal.ofReal (w i) * eLpNorm (E.b i) 2 q ≠ ⊤ := by
  simp_rw [← E.ofReal_mul_eLpNorm w hw]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ mul_nonneg (hw i) ENNReal.toReal_nonneg) hs]
  exact ENNReal.ofReal_ne_top

theorem abs_integral_b_le (i : E.ι) : |∫ x, E.b i x ∂q| ≤ (eLpNorm (E.b i) 2 q).toReal := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  simp_rw [ofReal_norm]
  rw [← eLpNorm_one_eq_lintegral_enorm (E.b_measurable i).aestronglyMeasurable]
  exact ENNReal.toReal_mono (E.eLpNorm_b_ne_top i)
    (eLpNorm_le_eLpNorm_of_exponent_le one_le_two)

theorem summable_integral_mul {u : U} (hu : u ∈ B) :
    Summable fun i ↦ (∫ x, E.b i x ∂q) * E.m i u := by
  refine E.summable_c.of_norm_bounded fun i ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul (E.abs_m_le i u hu) (E.abs_integral_b_le i) (abs_nonneg _) (E.c_nonneg i)

/-- The mean of `f(·, u)` is the sum of the means of the coefficients (integration is continuous
and linear on `L²(q)`). -/
theorem hasSum_integral_mul {u : U} (hu : u ∈ B) :
    HasSum (fun i ↦ (∫ x, E.b i x ∂q) * E.m i u) (∫ x, f x u ∂q) := by
  have h1 : ∫ x, f x u ∂q = ∫ x, ∑' i, E.b i x * E.m i u ∂q := by
    refine integral_congr_ae ?_
    filter_upwards [E.expansion u hu] with x hx
    exact hx.tsum_eq.symm
  have h2 : ∫ x, ∑' i, E.b i x * E.m i u ∂q = ∑' i, ∫ x, E.b i x * E.m i u ∂q := by
    refine integral_tsum (fun i ↦ ((E.b_measurable i).mul_const _).aestronglyMeasurable) ?_
    refine ne_top_of_le_ne_top (E.tsum_ofReal_mul_eLpNorm_ne_top E.c_nonneg E.summable_c)
      (ENNReal.tsum_le_tsum fun i ↦ ?_)
    calc ∫⁻ x, ‖E.b i x * E.m i u‖ₑ ∂q = ∫⁻ x, ‖E.b i x‖ₑ * ‖E.m i u‖ₑ ∂q := by
          simp_rw [enorm_mul]
      _ ≤ ∫⁻ x, ‖E.b i x‖ₑ * ENNReal.ofReal (E.c i) ∂q := by
          gcongr with x
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (E.abs_m_le i u hu)
      _ = (∫⁻ x, ‖E.b i x‖ₑ ∂q) * ENNReal.ofReal (E.c i) :=
          lintegral_mul_const _ (E.b_measurable i).enorm
      _ ≤ eLpNorm (E.b i) 2 q * ENNReal.ofReal (E.c i) := by
          gcongr
          rw [← eLpNorm_one_eq_lintegral_enorm (E.b_measurable i).aestronglyMeasurable]
          exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two
      _ = ENNReal.ofReal (E.c i) * eLpNorm (E.b i) 2 q := mul_comm _ _
  rw [h1, h2]
  simp_rw [integral_mul_const]
  exact (E.summable_integral_mul hu).hasSum

omit [MeasurableSpace Ω] in
/-- On a patch, `ψ_n(u) = Σ_i Y^n_i m_i(u)` for every `u ∈ B`, whenever every `X_l`, `l < n`,
lies in the set where the expansion holds for all `u ∈ B`. -/
theorem hasSum_coefficientProcess_mul {n : ℕ} {ω : Ω}
    (hω : ∀ l ∈ Finset.range n, ∀ u ∈ B, HasSum (fun i ↦ E.b i (Xs l ω) * E.m i u) (f (Xs l ω) u))
    {u : U} (hu : u ∈ B) :
    HasSum (fun i ↦ E.coefficientProcess Xs i n ω * E.m i u) (empiricalProcess q f Xs n ω u) := by
  have hl : ∀ l ∈ Finset.range n, HasSum (fun i ↦ (E.b i (Xs l ω) - ∫ x, E.b i x ∂q) * E.m i u)
      (f (Xs l ω) u - ∫ x, f x u ∂q) := fun l hl ↦ by
    have := (hω l hl u hu).sub (E.hasSum_integral_mul hu)
    refine this.congr_fun fun i ↦ ?_
    ring
  have := (hasSum_sum hl).mul_left (√(n : ℝ))⁻¹
  refine this.congr_fun fun i ↦ ?_
  simp only [coefficientProcess, Finset.sum_mul, mul_assoc]

omit [IsProbabilityMeasure q] in
theorem enorm_m_le {u : U} (hu : u ∈ B) (i : E.ι) : ‖E.m i u‖ₑ ≤ ENNReal.ofReal (E.c i) := by
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (E.abs_m_le i u hu)

omit [IsProbabilityMeasure q] in
theorem enorm_m_sub_le {u v : U} (hu : u ∈ B) (hv : v ∈ B) (i : E.ι) :
    ‖E.m i u - E.m i v‖ₑ ≤ ENNReal.ofReal (E.lip i) * edist u v := by
  rw [Real.enorm_eq_ofReal_abs, edist_dist, ← ENNReal.ofReal_mul (E.lip_nonneg i)]
  exact ENNReal.ofReal_le_ofReal (E.abs_m_sub_le i u hu v hv)

/-- The second moment of a weighted series of the coefficient processes is bounded by the square
of the weighted series of `L²(q)`-norms, uniformly in `n` ([Wat09, Theorem 5.7] and Minkowski). -/
theorem lintegral_tsum_coefficientProcess_sq_le (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) (w : E.ι → ℝ) (n : ℕ) :
    ∫⁻ ω, (∑' i, ENNReal.ofReal (w i) * ‖E.coefficientProcess Xs i n ω‖ₑ) ^ 2 ∂P
      ≤ (∑' i, ENNReal.ofReal (w i) * eLpNorm (E.b i) 2 q) ^ 2 := by
  refine (lintegral_tsum_sq_le
    (g := fun i ω ↦ ENNReal.ofReal (w i) * ‖E.coefficientProcess Xs i n ω‖ₑ)
    fun i ↦ measurable_const.mul (E.measurable_coefficientProcess Xs hX i n).enorm).trans ?_
  gcongr with i
  have h1 : ∫⁻ ω, (ENNReal.ofReal (w i) * ‖E.coefficientProcess Xs i n ω‖ₑ) ^ 2 ∂P
      = ENNReal.ofReal (w i) ^ 2 * ∫⁻ ω, ‖E.coefficientProcess Xs i n ω‖ₑ ^ 2 ∂P := by
    simp_rw [mul_pow]
    exact lintegral_const_mul _ ((E.measurable_coefficientProcess Xs hX i n).enorm.pow_const 2)
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul, show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  gcongr
  exact rpow_lintegral_enorm_sq_empiricalSum_le hX hlaw hind (E.b_measurable i) (E.b_memLp i) n

/-- [Hit26, Lemma 4.2.4] and
[Hit26, Lemma 4.2.8] on one patch, for `s = 2`: the majorants
`S_n = Σ_i c_i |Y^n_i|` of `sup_B |ψ_n|` and `R_n = Σ_i lip_i |Y^n_i|` of the Lipschitz constant of
`ψ_n` on `B`, with second moments `≤ (Σ_i c_i ‖b_i‖₂)²`, `≤ (Σ_i lip_i ‖b_i‖₂)²`. -/
@[expose] noncomputable def patchMajorants (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q)
    (hind : iIndepFun Xs P) (hB : TopologicalSpace.IsSeparable B)
    (hf : ∀ᵐ x ∂q, ContinuousOn (f x) B) {Ψ : ℕ → Ω → C(U, ℝ)}
    (hΨ : ∀ n, ∀ᵐ ω ∂P, ∀ u, Ψ n ω u = empiricalProcess q f Xs n ω u) :
    EmpiricalProcess.PatchMajorants Ψ P B where
  S n ω := ∑' i, ENNReal.ofReal (E.c i) * ‖E.coefficientProcess Xs i n ω‖ₑ
  R n ω := ∑' i, ENNReal.ofReal (E.lip i) * ‖E.coefficientProcess Xs i n ω‖ₑ
  S_measurable n := Measurable.tsum fun i ↦
    measurable_const.mul (E.measurable_coefficientProcess Xs hX i n).enorm
  R_measurable n := Measurable.tsum fun i ↦
    measurable_const.mul (E.measurable_coefficientProcess Xs hX i n).enorm
  CS := (∑' i, ENNReal.ofReal (E.c i) * eLpNorm (E.b i) 2 q) ^ 2
  CR := (∑' i, ENNReal.ofReal (E.lip i) * eLpNorm (E.b i) 2 q) ^ 2
  CS_ne_top := ENNReal.pow_ne_top (E.tsum_ofReal_mul_eLpNorm_ne_top E.c_nonneg E.summable_c)
  CR_ne_top := ENNReal.pow_ne_top (E.tsum_ofReal_mul_eLpNorm_ne_top E.lip_nonneg E.summable_lip)
  lintegral_S_sq_le n := E.lintegral_tsum_coefficientProcess_sq_le Xs hX hlaw hind E.c n
  lintegral_R_sq_le n := E.lintegral_tsum_coefficientProcess_sq_le Xs hX hlaw hind E.lip n
  enorm_le n := by
    filter_upwards [hΨ n, ae_forall_range_comp hX hlaw (E.ae_forall_hasSum hB hf) n] with ω hω hgood
      u hu
    rw [hω u, ← (E.hasSum_coefficientProcess_mul Xs hgood hu).tsum_eq]
    refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun i ↦ ?_)
    rw [enorm_mul, mul_comm]
    gcongr
    exact E.enorm_m_le hu i
  enorm_sub_le n := by
    filter_upwards [hΨ n, ae_forall_range_comp hX hlaw (E.ae_forall_hasSum hB hf) n] with ω hω hgood
      u hu v hv
    rw [hω u, hω v, ← ((E.hasSum_coefficientProcess_mul Xs hgood hu).sub
      (E.hasSum_coefficientProcess_mul Xs hgood hv)).tsum_eq, ← ENNReal.tsum_mul_right]
    refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun i ↦ ?_)
    calc ‖E.coefficientProcess Xs i n ω * E.m i u - E.coefficientProcess Xs i n ω * E.m i v‖ₑ
        = ‖E.coefficientProcess Xs i n ω‖ₑ * ‖E.m i u - E.m i v‖ₑ := by rw [← mul_sub, enorm_mul]
      _ ≤ ‖E.coefficientProcess Xs i n ω‖ₑ * (ENNReal.ofReal (E.lip i) * edist u v) := by
          gcongr
          exact E.enorm_m_sub_le hu hv i
      _ = ENNReal.ofReal (E.lip i) * ‖E.coefficientProcess Xs i n ω‖ₑ * edist u v := by ring

end L2Expansion

end SingularLearningTheory
