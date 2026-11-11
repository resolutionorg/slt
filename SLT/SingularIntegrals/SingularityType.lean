/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Transforms
public import SLT.Setting
public import SLT.VolumeScaling.Laplace.Asymptotic
public import SLT.VolumeScaling.Comparison
public import SLT.VolumeScaling.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
public import SLT.SingularIntegrals.Defs

/-!
# The singularity type `(λ, m)` by volume scaling

The learning coefficient `λ` and its multiplicity `m` defined intrinsically, by the scaling of
the sublevel volume `V(ε) = ∫_{W ∩ {K ≤ ε}} φ(w) dw` as `ε → 0⁺`: `(λ, m)` is *the singularity
type* of `(K, φ, W)` when `V(ε)` is two-sidedly bounded by `ε^λ (−log ε)^{m−1}`. This is the
characterisation of the local learning coefficient by volume scaling that [Hit26] offers in
[Hit26, Remark 6.2.3] ([Lau24, Definition 1]), and the
definition used by the volume-scaling library `SLT/VolumeScaling/`, whose `HasLLCExponentsOn`
it is (`isSingularityType_iff`). [Hit26] itself defines `λ, m` chart-wise from a resolution
([Hit26, Equation (5.2.1)]); that every nondegenerate atlas
computes the intrinsic pair is `NondegenerateResolutionAtlas.isSingularityType`
(`TypeOfAtlas.lean`).

| Thesis | Lean |
| --- | --- |
| [Hit26, Remark 6.2.3] | `IsSingularityType` |
| uniqueness of `(λ, m)` (implicit in [Hit26]) | `IsSingularityType.unique` |
| [Hit26, Theorem 3.3.9], from the type | |
| | `IsSingularityType.deterministic_asymptotics` |

## Conventions

`m : ℕ` is [Hit26]'s multiplicity, and the exponent of `−log ε` is the *real* `m − 1`, so
that the scales for different `m` are pairwise incomparable and `(λ, m)` is unique
(`(m − 1 : ℕ)` would identify `m = 0` with `m = 1`). Nothing here assumes `1 ≤ m`; it is a
theorem whenever a resolution atlas exists (`ResolutionAtlas.mult_pos`).

The Laplace bridge `IsSingularityType.deterministic_asymptotics` is the deterministic free
energy formula with the type as its hypothesis: no resolution of singularities is involved.
The direction from the asymptotics of `Z₀(n)` back to the volume (Tauberian) is not needed and
not proved.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology Asymptotics SingularLearningTheory
open scoped ENNReal

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-! ## Two-sided bounds and `Θ` -/

/-- No thesis counterpart. For an eventually nonnegative `V`, two-sided eventual bounds by
positive multiples of the scale are the same as `V =Θ scale` (dln's
`hasLLCExponentsOn_iff_eventually_bounds` for an arbitrary nonnegative function). -/
private theorem isTheta_llcScale_iff_bounds {V : ℝ → ℝ} (hV : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ V ε)
    (lam theta : ℝ) :
    V =Θ[𝓝[>] (0 : ℝ)] llcScale lam theta ↔
      ∃ c₁ > (0 : ℝ), ∃ c₂ > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        c₁ * llcScale lam theta ε ≤ V ε ∧ V ε ≤ c₂ * llcScale lam theta ε := by
  constructor
  · rintro ⟨hVO, hOV⟩
    obtain ⟨c₂, hc₂, hb₂⟩ := isBigO_iff'.mp hVO
    obtain ⟨C, hC, hb₁⟩ := isBigO_iff'.mp hOV
    refine ⟨C⁻¹, by positivity, c₂, hc₂, ?_⟩
    filter_upwards [hb₂, hb₁, hV, llcScale_eventually_pos (lam := lam) (theta := theta)]
      with ε h₂ h₁ h0 hs
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg hs.le] at h₂ h₁
    exact ⟨by rw [inv_mul_le_iff₀ hC]; exact h₁, h₂⟩
  · rintro ⟨c₁, hc₁, c₂, hc₂, hb⟩
    constructor
    · refine IsBigO.of_bound c₂ ?_
      filter_upwards [hb, hV, llcScale_eventually_pos (lam := lam) (theta := theta)]
        with ε h h0 hs
      rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg hs.le]
      exact h.2
    · refine IsBigO.of_bound c₁⁻¹ ?_
      filter_upwards [hb, hV, llcScale_eventually_pos (lam := lam) (theta := theta)]
        with ε h h0 hs
      rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg hs.le, ← div_eq_inv_mul,
        le_div_iff₀ hc₁]
      linarith [h.1]

/-- The type as a `Θ`-statement about the sublevel volume. -/
theorem IsSingularityType.isTheta {lam : ℝ} {m : ℕ} (h : IsSingularityType K φ W lam m) :
    (fun ε ↦ ∫ w in W ∩ {w | K w ≤ ε}, φ w) =Θ[𝓝[>] (0 : ℝ)] llcScale lam m := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hb⟩ := h
  have hV : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ ∫ w in W ∩ {w | K w ≤ ε}, φ w := by
    filter_upwards [hb, llcScale_eventually_pos (lam := lam) (theta := m)] with ε h hs
    exact le_trans (mul_pos hc₁ hs).le h.1
  exact (isTheta_llcScale_iff_bounds hV lam m).mpr ⟨c₁, hc₁, c₂, hc₂, hb⟩

/-- The singularity type is unique: no hypotheses on `K`, `φ`, `W`. -/
theorem IsSingularityType.unique {l₁ l₂ : ℝ} {m₁ m₂ : ℕ} (h₁ : IsSingularityType K φ W l₁ m₁)
    (h₂ : IsSingularityType K φ W l₂ m₂) : l₁ = l₂ ∧ m₁ = m₂ := by
  obtain ⟨hl, hm⟩ := llcScale_isTheta_iff_eq.mp (h₁.isTheta.symm.trans h₂.isTheta)
  exact ⟨hl, Nat.cast_injective hm⟩

/-! ## The bridge to the volume-scaling library -/

/-- No thesis counterpart. The library's sublevel volume of `K` on `W` against `φ dw` is the
thesis's `V(ε) = ∫_{W ∩ {K ≤ ε}} φ`. -/
theorem _root_.SingularLearningTheory.sublevelVol_priorMeasure (hW : MeasurableSet W)
    (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφm : AEMeasurable φ (volume.restrict W)) (ε : ℝ) :
    sublevelVol (priorMeasure φ Set.univ) W K ε = ∫ w in W ∩ {w | K w ≤ ε}, φ w := by
  have hsub : volume.restrict (W ∩ {w | K w ≤ ε}) ≤ volume.restrict W :=
    Measure.restrict_mono inter_subset_left le_rfl
  rw [sublevelVol, priorMeasure, Measure.restrict_univ,
    withDensity_apply' _ (W ∩ {w | K w ≤ ε}),
    integral_eq_lintegral_of_nonneg_ae
      (ae_mono hsub ((ae_restrict_iff' hW).mpr (.of_forall hφ)))
      (hφm.mono_measure hsub).aestronglyMeasurable]

/-- `IsSingularityType` is the volume-scaling library's `HasLLCExponentsOn` for the prior
measure `φ dw` on `W` (with the multiplicity cast to `ℝ`). -/
theorem isSingularityType_iff (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφm : AEMeasurable φ (volume.restrict W)) {lam : ℝ} {m : ℕ} :
    IsSingularityType K φ W lam m ↔ HasLLCExponentsOn (priorMeasure φ Set.univ) W K lam m := by
  rw [hasLLCExponentsOn_iff_eventually_bounds]
  simp only [sublevelVol_priorMeasure hW hφ hφm, llcScale]
  rfl

/-- The prior measure of `W` is finite when `φ` is integrable on `W`. -/
theorem priorMeasure_ne_top (hW : MeasurableSet W) (hφi : IntegrableOn φ W) :
    priorMeasure φ Set.univ W ≠ ⊤ := by
  rw [priorMeasure, Measure.restrict_univ, withDensity_apply _ hW]
  exact ne_top_of_le_ne_top hφi.hasFiniteIntegral.ne (lintegral_ofReal_le_lintegral_enorm φ)

/-! ## The Laplace bridge: the deterministic free energy formula from the type -/

section Laplace

variable (hW : MeasurableSet W) (hKm : AEMeasurable K (volume.restrict W))
  (hK : ∀ w ∈ W, 0 ≤ K w) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)

include hW hφ hφi in
/-- No thesis counterpart. `Z₀(n)` is the Laplace integral of `βK` against the prior measure
`φ dw` on `W`. -/
theorem normalizedPartitionFunction_eq_integral_priorMeasure (β n : ℝ) :
    normalizedPartitionFunction K φ W β n
      = ∫ w in W, Real.exp (-(n * (β * K w))) ∂(priorMeasure φ Set.univ) := by
  rw [normalizedPartitionFunction, priorMeasure, Measure.restrict_univ, restrict_withDensity hW,
    integral_withDensity_eq_integral_toReal_smul₀ hφi.aemeasurable.ennreal_ofReal
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hW fun w hw ↦ ?_
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hφ w hw)]
  rw [mul_comm, mul_assoc]

include hW hKm hK hφ hφi in
/-- No thesis counterpart. `Z₀(n)` is nonincreasing in `n` (for `K ≥ 0`, `φ ≥ 0`). -/
private theorem normalizedPartitionFunction_antitone {β : ℝ} (hβ : 0 < β) {n₁ n₂ : ℝ} (hn₁ : 0 ≤ n₁)
    (hn : n₁ ≤ n₂) :
    normalizedPartitionFunction K φ W β n₂ ≤ normalizedPartitionFunction K φ W β n₁ := by
  have hint : ∀ n : ℝ, 0 ≤ n →
      IntegrableOn (fun w ↦ Real.exp (-(n * β * K w)) * φ w) W := fun n hn ↦ by
    refine hφi.bdd_mul (c := 1) ?_ ?_
    · exact (Real.measurable_exp.comp_aemeasurable
        ((hKm.const_mul (n * β)).neg)).aestronglyMeasurable
    · filter_upwards [(ae_restrict_iff' hW).mpr (Filter.Eventually.of_forall hK)] with w hw
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have := mul_nonneg (mul_nonneg hn hβ.le) hw
      linarith
  refine setIntegral_mono_on (hint n₂ (hn₁.trans hn)) (hint n₁ hn₁) hW fun w hw ↦ ?_
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hφ w hw)
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hβ.le) (hK w hw)
  linarith

include hW hφ in
/-- `Z₀(n) ≥ 0`. -/
private theorem normalizedPartitionFunction_nonneg (β n : ℝ) :
    0 ≤ normalizedPartitionFunction K φ W β n :=
  setIntegral_nonneg hW fun w hw ↦ mul_nonneg (Real.exp_pos _).le (hφ w hw)

include hW hKm hK hφ hφi in
/-- [Hit26, Theorem 3.3.9], with the singularity type as the
hypothesis: if `(λ, m)` is the singularity type of `(K, φ, W)` then, for every `β > 0`,

`F₀(n) = −log Z₀(n) = λ log n − (m − 1) log log n + O(1)`,

the `O(1)` uniform over `n ≥ 3`. Hypotheses: `W` measurable, `K` measurable on `W` and `≥ 0` there,
`φ ≥ 0` integrable on `W`; no resolution of singularities. The route is the Laplace representation
of `laplaceIntegral` as `nβ ∫₀^∞ e^{−nβε} V(ε) dε` (`VolumeScaling.LaplaceAsymptotic`), which gives
the bound for large `n`; for `n` in a bounded range `laplaceIntegral` is bounded above by `Z₀(3)`
and below by its positive value at the threshold, since `laplaceIntegral` is nonincreasing in `n`.
-/
theorem IsSingularityType.deterministic_asymptotics {lam : ℝ} {m : ℕ}
    (h : IsSingularityType K φ W lam m) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, ∀ n : ℝ, 3 ≤ n →
      |(-Real.log (normalizedPartitionFunction K φ W β n)) -
        (lam * Real.log n - ((m : ℝ) - 1) * Real.log (Real.log n))| ≤ C := by
  have hμW : priorMeasure φ Set.univ W ≠ ⊤ := priorMeasure_ne_top hW hφi
  have hT : HasLLCExponentsOn (priorMeasure φ Set.univ) W (fun w ↦ β * K w) lam m := by
    refine ((isSingularityType_iff hW hφ hφi.aemeasurable).mp h).of_mutually_dominated
      (inv_pos.mpr hβ) hβ (fun w _ ↦ ?_) (fun w _ ↦ le_rfl)
    rw [← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]
  have hac : (priorMeasure φ Set.univ).restrict W ≪ volume.restrict W := by
    rw [priorMeasure, Measure.restrict_univ, restrict_withDensity hW]
    exact withDensity_absolutelyContinuous _ _
  have hf : AEMeasurable (fun w ↦ β * K w) ((priorMeasure φ Set.univ).restrict W) :=
    (hKm.const_mul β).mono_ac hac
  have hf0 : 0 ≤ᵐ[(priorMeasure φ Set.univ).restrict W] fun w ↦ β * K w :=
    hac.ae_le ((ae_restrict_iff' hW).mpr (.of_forall fun w hw ↦ mul_nonneg hβ.le (hK w hw)))
  have hZ : ∀ n : ℝ, normalizedPartitionFunction K φ W β n
      = ∫ w in W, Real.exp (-(n * (β * K w))) ∂(priorMeasure φ Set.univ) :=
    normalizedPartitionFunction_eq_integral_priorMeasure hW hφ hφi β
  -- the eventual bound
  obtain ⟨C₀, hC₀⟩ := isBigO_iff.mp (hT.log_laplace_sub_isBigO hf hf0 hμW)
  -- eventual positivity of `laplaceIntegral`
  have hpos : ∀ᶠ n : ℝ in atTop, 0 < normalizedPartitionFunction K φ W β n := by
    obtain ⟨c, -, hc⟩ := isBigO_iff'.mp (hT.laplace_isTheta hf hf0 hμW).2
    filter_upwards [hc, laplaceScale_eventually_pos (lam := lam) (theta := m)] with n hn hs
    rw [hZ]
    refine lt_of_le_of_ne (hZ n ▸ normalizedPartitionFunction_nonneg hW hφ β n) fun h0 ↦ ?_
    rw [← h0, norm_zero, mul_zero, norm_le_zero_iff] at hn
    exact hs.ne' hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hC₀.and (hpos.and (eventually_ge_atTop 3)))
  obtain ⟨hNb, hNpos, hN3⟩ := hN N le_rfl
  set Z : ℝ → ℝ := normalizedPartitionFunction K φ W β with hZdef
  have hZN : 0 < Z N := hNpos
  have hlogN : 1 < Real.log N := by
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) this
      _ ≤ Real.log N := Real.log_le_log (by norm_num) hN3
  refine ⟨max C₀ (|Real.log (Z N)| + |Real.log (Z 3)| +
    (|lam| * Real.log N + |(m : ℝ) - 1| * Real.log (Real.log N))), fun n hn ↦ ?_⟩
  rcases le_or_gt N n with hnN | hnN
  · -- large `n`: the eventual bound
    obtain ⟨hb, -, -⟩ := hN n hnN
    rw [norm_one, mul_one, Real.norm_eq_abs, ← hZ] at hb
    refine le_trans (le_of_eq ?_) (hb.trans (le_max_left _ _))
    rw [← abs_neg]
    congr 1
    ring
  · -- `3 ≤ n < N`: monotonicity of `laplaceIntegral`
    have hn0 : 0 < n := by linarith
    have hZmono₁ : Z N ≤ Z n :=
      normalizedPartitionFunction_antitone hW hKm hK hφ hφi hβ hn0.le hnN.le
    have hZmono₂ : Z n ≤ Z 3 :=
      normalizedPartitionFunction_antitone hW hKm hK hφ hφi hβ (by norm_num) hn
    have hZn : 0 < Z n := hZN.trans_le hZmono₁
    have hlog₁ : Real.log (Z N) ≤ Real.log (Z n) := Real.log_le_log hZN hZmono₁
    have hlog₂ : Real.log (Z n) ≤ Real.log (Z 3) := Real.log_le_log hZn hZmono₂
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hlogn_le : Real.log n ≤ Real.log N := Real.log_le_log hn0 hnN.le
    have hloglog : 0 ≤ Real.log (Real.log n) := by
      refine Real.log_nonneg ?_
      have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) this.le
        _ ≤ Real.log n := Real.log_le_log (by norm_num) hn
    have hloglog_le : Real.log (Real.log n) ≤ Real.log (Real.log N) :=
      Real.log_le_log hlogn hlogn_le
    refine le_trans ?_ (le_max_right _ _)
    have hlogZ : |Real.log (Z n)| ≤ |Real.log (Z N)| + |Real.log (Z 3)| :=
      abs_le.mpr ⟨by linarith [neg_abs_le (Real.log (Z N)), abs_nonneg (Real.log (Z 3))],
        by linarith [le_abs_self (Real.log (Z 3)), abs_nonneg (Real.log (Z N))]⟩
    have hmodel : |lam * Real.log n - ((m : ℝ) - 1) * Real.log (Real.log n)|
        ≤ |lam| * Real.log N + |(m : ℝ) - 1| * Real.log (Real.log N) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hlogn, abs_of_nonneg hloglog]
      gcongr
    calc |(-Real.log (Z n)) - (lam * Real.log n - ((m : ℝ) - 1) * Real.log (Real.log n))|
        ≤ |Real.log (Z n)| + |lam * Real.log n - ((m : ℝ) - 1) * Real.log (Real.log n)| := by
          rw [sub_eq_add_neg, ← abs_neg]
          refine le_trans (le_of_eq ?_) (abs_add_le _ _)
          rw [neg_add, neg_neg, neg_neg]
      _ ≤ (|Real.log (Z N)| + |Real.log (Z 3)|) +
            (|lam| * Real.log N + |(m : ℝ) - 1| * Real.log (Real.log N)) :=
          add_le_add hlogZ hmodel

end Laplace

/-! ## Sanity: `K = w²` on `[−1, 1]` -/

/-- No thesis counterpart; a sanity check of the definition. `K(w) = w²` with the uniform
prior on `W = [−1, 1]` has singularity type `(1/2, 1)`: `V(ε) = 2√ε` for `ε ≤ 1`. -/
theorem isSingularityType_sq :
    IsSingularityType (fun w : Fin 1 → ℝ ↦ w 0 ^ 2) (fun _ ↦ 1) (Icc (-1) 1) (1 / 2) 1 := by
  refine ⟨2, two_pos, 2, two_pos, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε.2.le
  have hset : Icc (-1 : Fin 1 → ℝ) 1 ∩ {w | w 0 ^ 2 ≤ ε}
      = Icc (fun _ ↦ -Real.sqrt ε) (fun _ ↦ Real.sqrt ε) := by
    ext w
    simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq, Pi.le_def, Fin.forall_fin_one,
      Pi.neg_apply, Pi.one_apply, Real.sq_le hε.1.le]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, by linarith⟩, h1, h2⟩
  have hvol : ∫ w in Icc (-1 : Fin 1 → ℝ) 1 ∩ {w | w 0 ^ 2 ≤ ε}, (1 : ℝ) = 2 * Real.sqrt ε := by
    have hle : (fun _ : Fin 1 ↦ -Real.sqrt ε) ≤ fun _ ↦ Real.sqrt ε :=
      fun _ ↦ by linarith [Real.sqrt_nonneg ε]
    rw [hset, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      Real.volume_Icc_pi_toReal hle, Fin.prod_univ_one]
    ring
  have hscale : ε ^ (1 / 2 : ℝ) * (-Real.log ε) ^ (((1 : ℕ) : ℝ) - 1) = Real.sqrt ε := by
    rw [Nat.cast_one, sub_self, Real.rpow_zero, mul_one, Real.sqrt_eq_rpow]
  rw [hvol, hscale]
  constructor <;> linarith

end SingularLearningTheory
