/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Asymptotic uniform integrability

[Hit26, Lemma 5.2.8] and the definition preceding it.

| Thesis | Lean |
| --- | --- |
| `E[|A_n| 1(|A_n| > M)]` | `MeasureTheory.tailExpectation` |
| AUI: `lim_M limsup_n E[|A_n| 1(|A_n| > M)] = 0` | `MeasureTheory.AsympUnifIntegrable` |
| [Hit26, Lemma 5.2.8] (1) |
`MeasureTheory.AsympUnifIntegrable.of_abs_le` |
| [Hit26, Lemma 5.2.8] (2), for `s = 2` | |
| | `MeasureTheory.asympUnifIntegrable_of_lintegral_sq_le` |
| the limit inherits the tail bound (implicit in (3)) | |
| | `MeasureTheory.AsympUnifIntegrable.tailExpectation_limit_le` |
| [Hit26, Lemma 5.2.8] (3), with `f = id` | |
| | `MeasureTheory.AsympUnifIntegrable.tendsto_integral` |

[Hit26]'s `lim_M limsup_n … = 0` is stated in the equivalent `ε`-form: for every `ε > 0`
there is `M` with `E[|A_n| 1(|A_n| > M)] ≤ ε` for all large `n` (the tail expectation is
antitone in `M`). Tail expectations are Lebesgue integrals in `ℝ≥0∞`, so no integrability
is assumed; integrability of `A_n` (for large `n`) and of the limit follows from AUI. Part (2)
is proved for every real moment order greater than one. The free energy formula uses
the square-moment specialization; Bayes/Gibbs quartic bounds use order `3/2`. Part (3) is proved for
`f = id`; [Hit26] applies it to `f = id` as well.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

/-- The tail expectation `E[|X| 1(|X| > M)]`, as a Lebesgue integral. -/
@[expose] noncomputable def tailExpectation (P : Measure Ω) (X : Ω → ℝ) (M : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, {ω | M < |X ω|}.indicator (fun ω ↦ ‖X ω‖ₑ) ω ∂P

/-- Thesis definition of *asymptotically uniformly integrable*, in `ε`-form. -/
@[expose] def AsympUnifIntegrable (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℝ, ∀ᶠ n in atTop, tailExpectation P (X n) M ≤ ENNReal.ofReal ε

private theorem tailExpectation_anti (X : Ω → ℝ) : Antitone (tailExpectation P X) := by
  intro M M' h
  refine lintegral_mono fun ω ↦ ?_
  exact indicator_le_indicator_of_subset (fun ω hω ↦ lt_of_le_of_lt h hω) (fun _ ↦ zero_le) ω

omit [MeasurableSpace Ω] in
private theorem enorm_eq_indicator_add {X : Ω → ℝ} (M : ℝ) (ω : Ω) :
    ‖X ω‖ₑ ≤ {ω | M < |X ω|}.indicator (fun ω ↦ ‖X ω‖ₑ) ω + ENNReal.ofReal M := by
  by_cases h : M < |X ω|
  · rw [indicator_of_mem (show ω ∈ {ω | M < |X ω|} from h)]
    exact le_self_add
  · rw [indicator_of_notMem (show ω ∉ {ω | M < |X ω|} from h), zero_add, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (not_lt.mp h)

/-- A finite tail expectation gives integrability (for a finite measure). -/
private theorem integrable_of_tailExpectation_ne_top [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) {M : ℝ} (h : tailExpectation P X M ≠ ⊤) : Integrable X P := by
  refine ⟨hX, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ ω, ‖X ω‖ₑ ∂P
      ≤ ∫⁻ ω, ({ω | M < |X ω|}.indicator (fun ω ↦ ‖X ω‖ₑ) ω + ENNReal.ofReal M) ∂P :=
        lintegral_mono fun ω ↦ enorm_eq_indicator_add M ω
    _ = tailExpectation P X M + ENNReal.ofReal M * P univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]; rfl
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨h.lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (measure_lt_top _ _)⟩

/-- [Hit26, Lemma 5.2.8] (1): domination. -/
theorem AsympUnifIntegrable.of_abs_le {X Y : ℕ → Ω → ℝ} (hY : AsympUnifIntegrable P Y)
    (hle : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, |X n ω| ≤ Y n ω) : AsympUnifIntegrable P X := by
  intro ε hε
  obtain ⟨M, hM⟩ := hY ε hε
  refine ⟨M, ?_⟩
  filter_upwards [hM, hle] with n hn hle
  refine le_trans (lintegral_mono_ae ?_) hn
  filter_upwards [hle] with ω hω
  by_cases h : M < |X n ω|
  · rw [indicator_of_mem (show ω ∈ {ω | M < |X n ω|} from h),
      indicator_of_mem
        (show ω ∈ {ω | M < |Y n ω|} from lt_of_lt_of_le h (hω.trans (le_abs_self _))),
      Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hω.trans (le_abs_self _))
  · rw [indicator_of_notMem (show ω ∉ {ω | M < |X n ω|} from h)]
    exact zero_le

/-- Any eventual uniformly bounded moment of real order p>1 implies AUI.
The ofReal formulation matches Bochner moment estimates without measurability
assumptions on the original signed variables. -/
private theorem asympUnifIntegrable_of_lintegral_abs_rpow_le {X : ℕ → Ω → ℝ}
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ᶠ n in atTop, ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂P ≤ C) :
    AsympUnifIntegrable P X := by
  intro ε hε
  let T : ℝ := C.toReal / ε + 1
  have hT : 0 < T := by dsimp [T]; positivity
  let M : ℝ := T ^ ((p - 1)⁻¹)
  have hM : 0 < M := Real.rpow_pos_of_pos hT _
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hMT : M ^ (p - 1) = T := by
    dsimp [M]
    rw [← Real.rpow_mul hT.le, inv_mul_cancel₀ hp1.ne', Real.rpow_one]
  have hTne : ENNReal.ofReal T ≠ 0 := (ENNReal.ofReal_pos.mpr hT).ne'
  have hTinv : (ENNReal.ofReal T)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hTne
  refine ⟨M, ?_⟩
  filter_upwards [h] with n hn
  have hpt : ∀ ω, {ω | M < |X n ω|}.indicator (fun ω ↦ ‖X n ω‖ₑ) ω ≤
      ENNReal.ofReal (|X n ω| ^ p) * (ENNReal.ofReal T)⁻¹ := by
    intro ω
    by_cases hω : M < |X n ω|
    · rw [indicator_of_mem (show ω ∈ {ω | M < |X n ω|} from hω), ← div_eq_mul_inv,
        ENNReal.le_div_iff_mul_le (Or.inl hTne) (Or.inl ENNReal.ofReal_ne_top),
        Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
      have hscale : T ≤ |X n ω| ^ (p - 1) := by
        rw [← hMT]
        exact Real.rpow_le_rpow hM.le hω.le hp1.le
      have hy : 0 < |X n ω| := hM.trans hω
      apply ENNReal.ofReal_le_ofReal
      calc |X n ω| * T ≤ |X n ω| * |X n ω| ^ (p - 1) :=
          mul_le_mul_of_nonneg_left hscale (abs_nonneg _)
        _ = |X n ω| ^ (1 + (p - 1)) := by rw [Real.rpow_add hy, Real.rpow_one]
        _ = |X n ω| ^ p := by congr 1; ring
    · rw [indicator_of_notMem (show ω ∉ {ω | M < |X n ω|} from hω)]
      exact zero_le
  calc tailExpectation P (X n) M
      ≤ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) * (ENNReal.ofReal T)⁻¹ ∂P := lintegral_mono hpt
    _ = (∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂P) * (ENNReal.ofReal T)⁻¹ :=
        lintegral_mul_const' _ _ hTinv
    _ ≤ C * (ENNReal.ofReal T)⁻¹ := mul_le_mul' hn le_rfl
    _ ≤ ENNReal.ofReal ε := by
        rw [← div_eq_mul_inv, ENNReal.div_le_iff hTne ENNReal.ofReal_ne_top,
          ← ENNReal.ofReal_mul hε.le, ← ENNReal.ofReal_toReal hC]
        apply ENNReal.ofReal_le_ofReal
        dsimp [T]
        rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
        linarith

/-- The ENNReal-rpow version, matching empirical-process MomentBound. -/
private theorem asympUnifIntegrable_of_lintegral_rpow_le {X : ℕ → Ω → ℝ}
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ᶠ n in atTop, ∫⁻ ω, ‖X n ω‖ₑ ^ p ∂P ≤ C) :
    AsympUnifIntegrable P X := by
  apply asympUnifIntegrable_of_lintegral_abs_rpow_le hp hC
  filter_upwards [h] with n hn
  simpa only [Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (le_trans zero_le_one hp.le)] using hn

/-- Asymptotic uniform integrability from eventual bounds on the `3/2` moments; nothing is
required at `n = 0`. -/
private theorem asympUnifIntegrable_of_integral_abs_rpow_le {X : ℕ → Ω → ℝ}
    {p C : ℝ} (hp : 1 < p)
    (hi : ∀ᶠ n in atTop, Integrable (fun ω ↦ |X n ω| ^ p) P)
    (hb : ∀ᶠ n in atTop, ∫ ω, |X n ω| ^ p ∂P ≤ C) :
    AsympUnifIntegrable P X := by
  apply asympUnifIntegrable_of_lintegral_abs_rpow_le hp (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top
  filter_upwards [hi, hb] with n hin hbn
  rw [← ofReal_integral_eq_lintegral_ofReal hin
    (Eventually.of_forall fun ω ↦ Real.rpow_nonneg (abs_nonneg _) p)]
  exact ENNReal.ofReal_le_ofReal hbn

/-- Convenient specialization used by Bayes/Gibbs finite-sample bounds. -/
theorem asympUnifIntegrable_of_integral_three_halves_le {X : ℕ → Ω → ℝ} {C : ℝ}
    (hi : ∀ᶠ n in atTop, Integrable (fun ω ↦ |X n ω| ^ (3 / 2 : ℝ)) P)
    (hb : ∀ᶠ n in atTop, ∫ ω, |X n ω| ^ (3 / 2 : ℝ) ∂P ≤ C) :
    AsympUnifIntegrable P X :=
  asympUnifIntegrable_of_integral_abs_rpow_le (by norm_num) hi hb


/-- [Hit26, Lemma 5.2.8] (2), for `s = 2`: a uniform
bound on `E[X_n²]` makes `X_n` AUI. -/
theorem asympUnifIntegrable_of_lintegral_sq_le {X : ℕ → Ω → ℝ} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ᶠ n in atTop, ∫⁻ ω, ‖X n ω‖ₑ ^ 2 ∂P ≤ C) : AsympUnifIntegrable P X := by
  apply asympUnifIntegrable_of_lintegral_rpow_le (p := 2) (by norm_num) hC
  simpa only [ENNReal.rpow_two] using h

/-- The clamp `x ↦ max (−M) (min M x)` as a bounded continuous function. -/
private noncomputable def clampBCF (M : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ max (-M) (min M x))
    (continuous_const.max (continuous_const.min continuous_id)) |M| fun x ↦ by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(neg_le_neg (le_abs_self M)).trans (le_max_left _ _),
        max_le (neg_le_abs M) ((min_le_left _ _).trans (le_abs_self M))⟩

private theorem clampBCF_apply (M x : ℝ) : clampBCF M x = max (-M) (min M x) := rfl

private theorem clampBCF_of_abs_le {M x : ℝ} (hx : |x| ≤ M) : clampBCF M x = x := by
  rw [clampBCF_apply, min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]

/-- `|x − clamp_M x| ≤ |x| 1(|x| > M)` for `M ≥ 0`. -/
private theorem enorm_sub_clampBCF_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    ‖x - clampBCF M x‖ₑ ≤ {x | M < |x|}.indicator (fun x ↦ ‖x‖ₑ) x := by
  by_cases hx : M < |x|
  · rw [indicator_of_mem (show x ∈ {x | M < |x|} from hx), Real.enorm_eq_ofReal_abs,
      Real.enorm_eq_ofReal_abs, clampBCF_apply]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at hx ⊢
      rw [min_eq_left hx.le, max_eq_right (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_neg h0] at hx ⊢
      rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · rw [indicator_of_notMem (show x ∉ {x | M < |x|} from hx), clampBCF_of_abs_le (not_lt.mp hx),
      sub_self, enorm_zero]

/-- The truncation error of the expectation is bounded by the tail expectation. -/
private theorem abs_integral_sub_clampBCF_le [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable X P)
    {M : ℝ} (hM : 0 ≤ M) :
    |(∫ ω, X ω ∂P) - ∫ ω, clampBCF M (X ω) ∂P| ≤ (tailExpectation P X M).toReal := by
  have hc : Integrable (fun ω ↦ clampBCF M (X ω)) P :=
    Integrable.of_bound ((clampBCF M).continuous.comp_aestronglyMeasurable hX.1) ‖clampBCF M‖
      (Eventually.of_forall fun ω ↦ (clampBCF M).norm_coe_le_norm _)
  rw [← integral_sub hX hc, ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  simp_rw [ofReal_norm]
  refine ENNReal.toReal_mono ?_ (lintegral_mono fun ω ↦ enorm_sub_clampBCF_le hM (X ω))
  exact ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω ↦ indicator_le_self _ _ ω)
    (hasFiniteIntegral_iff_enorm.mp hX.2))

section Limit

variable [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}

/-- The continuous cutoff `x ↦ |x| min(1, max(0, |x| − M))`, squeezed between
`|x| 1(|x| > M + 1)` and `|x| 1(|x| > M)`. -/
private theorem cutoff_bounds (M x : ℝ) :
    {x | M + 1 < |x|}.indicator (fun x ↦ ‖x‖ₑ) x
        ≤ ENNReal.ofReal (|x| * min 1 (max 0 (|x| - M))) ∧
      ENNReal.ofReal (|x| * min 1 (max 0 (|x| - M)))
        ≤ {x | M < |x|}.indicator (fun x ↦ ‖x‖ₑ) x := by
  constructor
  · by_cases hx : M + 1 < |x|
    · rw [indicator_of_mem (show x ∈ {x | M + 1 < |x|} from hx), Real.enorm_eq_ofReal_abs,
        max_eq_right (by linarith), min_eq_left (by linarith), mul_one]
    · rw [indicator_of_notMem (show x ∉ {x | M + 1 < |x|} from hx)]
      exact zero_le
  · by_cases hx : M < |x|
    · rw [indicator_of_mem (show x ∈ {x | M < |x|} from hx), Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      exact mul_le_of_le_one_right (abs_nonneg x) (min_le_left _ _)
    · rw [indicator_of_notMem (show x ∉ {x | M < |x|} from hx), max_eq_left (by linarith),
        min_eq_right zero_le_one, mul_zero, ENNReal.ofReal_zero]

/-- The limit of an AUI sequence converging in distribution inherits the tail bound (via
the lower-semicontinuity half of the portmanteau theorem). -/
private theorem AsympUnifIntegrable.tailExpectation_limit_le (hX : AsympUnifIntegrable P X)
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ tailExpectation P' Z M ≤ ENNReal.ofReal ε := by
  obtain ⟨M₀, hM₀⟩ := hX ε hε
  set M : ℝ := max M₀ 0 with hM_def
  refine ⟨M + 1, by positivity, ?_⟩
  have hXm : ∀ n, AEMeasurable (X n) P := h.forall_aemeasurable
  have hZm : AEMeasurable Z P' := h.aemeasurable_limit
  set g : ℝ → ℝ := fun x ↦ |x| * min 1 (max 0 (|x| - M)) with hg_def
  have hgc : Continuous g :=
    continuous_abs.mul (continuous_const.min (continuous_const.max (continuous_abs.sub
      continuous_const)))
  have hg0 : 0 ≤ g := fun x ↦ mul_nonneg (abs_nonneg _) (le_min zero_le_one (le_max_left _ _))
  have hopens : ∀ G, IsOpen G → (P'.map Z) G ≤ atTop.liminf fun n ↦ (P.map (X n)) G := fun G hG ↦
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto hG
  have hfatou := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hgc hg0 hopens
  rw [lintegral_map' hgc.measurable.ennreal_ofReal.aemeasurable hZm] at hfatou
  simp_rw [lintegral_map' hgc.measurable.ennreal_ofReal.aemeasurable (hXm _)] at hfatou
  calc tailExpectation P' Z (M + 1)
      ≤ ∫⁻ ω', ENNReal.ofReal (g (Z ω')) ∂P' := lintegral_mono fun ω' ↦ (cutoff_bounds M _).1
    _ ≤ atTop.liminf fun n ↦ ∫⁻ ω, ENNReal.ofReal (g (X n ω)) ∂P := hfatou
    _ ≤ atTop.liminf fun n ↦ tailExpectation P (X n) M₀ := by
        refine liminf_le_liminf (Eventually.of_forall fun n ↦ lintegral_mono fun ω ↦ ?_)
        refine (cutoff_bounds M _).2.trans ?_
        exact indicator_le_indicator_of_subset
          (fun x (hx : M < |x|) ↦ show M₀ < |x| from (le_max_left M₀ 0).trans_lt hx)
          (fun _ ↦ zero_le) _
    _ ≤ ENNReal.ofReal ε := by
        refine (liminf_le_liminf hM₀).trans_eq ?_
        exact liminf_const _

theorem AsympUnifIntegrable.integrable_limit (hX : AsympUnifIntegrable P X)
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') : Integrable Z P' := by
  obtain ⟨M, -, hM⟩ := hX.tailExpectation_limit_le h one_pos
  exact integrable_of_tailExpectation_ne_top h.aemeasurable_limit.aestronglyMeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM)

theorem AsympUnifIntegrable.eventually_integrable (hX : AsympUnifIntegrable P X)
    (hm : ∀ n, AEStronglyMeasurable (X n) P) : ∀ᶠ n in atTop, Integrable (X n) P := by
  obtain ⟨M, hM⟩ := hX 1 one_pos
  filter_upwards [hM] with n hn
  exact integrable_of_tailExpectation_ne_top (hm n) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hn)

/-- [Hit26, Lemma 5.2.8] (3), `f = id`: an AUI sequence
converging in distribution has convergent expectations. -/
theorem AsympUnifIntegrable.tendsto_integral (hX : AsympUnifIntegrable P X)
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') :
    Tendsto (fun n ↦ ∫ ω, X n ω ∂P) atTop (𝓝 (∫ ω', Z ω' ∂P')) := by
  have hXm : ∀ n, AEMeasurable (X n) P := h.forall_aemeasurable
  have hZm : AEMeasurable Z P' := h.aemeasurable_limit
  have hZi : Integrable Z P' := hX.integrable_limit h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M₁, hM₁⟩ := hX (ε / 4) (by positivity)
  obtain ⟨M₂, hM₂0, hM₂⟩ := hX.tailExpectation_limit_le h (by positivity : 0 < ε / 4)
  set M : ℝ := max M₁ M₂ with hM_def
  have hM0 : 0 ≤ M := hM₂0.trans (le_max_right _ _)
  have hM₁' : ∀ᶠ n in atTop, tailExpectation P (X n) M ≤ ENNReal.ofReal (ε / 4) :=
    hM₁.mono fun n hn ↦ (tailExpectation_anti _ (le_max_left _ _)).trans hn
  have hM₂' : tailExpectation P' Z M ≤ ENNReal.ofReal (ε / 4) :=
    (tailExpectation_anti _ (le_max_right _ _)).trans hM₂
  -- weak convergence for the clamp
  have hconv : Tendsto (fun n ↦ ∫ ω, clampBCF M (X n ω) ∂P) atTop
      (𝓝 (∫ ω', clampBCF M (Z ω') ∂P')) := by
    have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h.tendsto (clampBCF M)
    simp only [ProbabilityMeasure.coe_mk] at this
    have hZ : ∫ y, clampBCF M y ∂(P'.map Z) = ∫ ω', clampBCF M (Z ω') ∂P' :=
      integral_map hZm (clampBCF M).continuous.aestronglyMeasurable
    have hXn : ∀ n, ∫ y, clampBCF M y ∂(P.map (X n)) = ∫ ω, clampBCF M (X n ω) ∂P := fun n ↦
      integral_map (hXm n) (clampBCF M).continuous.aestronglyMeasurable
    simpa only [hZ, hXn] using this
  rw [Metric.tendsto_nhds] at hconv
  filter_upwards [hM₁', hconv (ε / 4) (by positivity),
    hX.eventually_integrable fun n ↦ (hXm n).aestronglyMeasurable] with n hn₁ hn₂ hn₃
  have hA := abs_integral_sub_clampBCF_le hn₃ hM0
  have hB := abs_integral_sub_clampBCF_le hZi hM0
  have hA' : (tailExpectation P (X n) M).toReal ≤ ε / 4 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hn₁
  have hB' : (tailExpectation P' Z M).toReal ≤ ε / 4 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hM₂'
  rw [Real.dist_eq] at hn₂ ⊢
  calc |(∫ ω, X n ω ∂P) - ∫ ω', Z ω' ∂P'|
      = |((∫ ω, X n ω ∂P) - ∫ ω, clampBCF M (X n ω) ∂P) +
          ((∫ ω, clampBCF M (X n ω) ∂P) - ∫ ω', clampBCF M (Z ω') ∂P') +
          ((∫ ω', clampBCF M (Z ω') ∂P') - ∫ ω', Z ω' ∂P')| := by ring_nf
    _ ≤ |(∫ ω, X n ω ∂P) - ∫ ω, clampBCF M (X n ω) ∂P| +
          |(∫ ω, clampBCF M (X n ω) ∂P) - ∫ ω', clampBCF M (Z ω') ∂P'| +
          |(∫ ω', clampBCF M (Z ω') ∂P') - ∫ ω', Z ω' ∂P'| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by
        refine add_le_add (add_le_add (hA.trans hA') hn₂.le) ?_
        rw [abs_sub_comm]
        exact hB.trans hB'
    _ < ε := by linarith

end Limit

end MeasureTheory
