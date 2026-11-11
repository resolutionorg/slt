/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.FrozenKernel
public import SLT.SingularIntegrals.DeterministicFreeEnergy
import SLT.SingularIntegrals.Resolution
public import SLT.EmpiricalProcess.Defs
import Mathlib.Order.CompletePartialOrder
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Analysis.Complex.ExponentialBounds
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# [Wat09, Theorem 6.7]: the stochastic free energy asymptotics

[Hit26, Theorem 5.2.6], with
[Hit26, Lemma 5.2.5] and the
probabilistic transfer step of its proof.

| Thesis | Lean |
| --- | --- |
| transfer of the uniform deterministic approximation to convergence in probability | |
| (no thesis counterpart; implicit in the proof of [Wat09, Theorem 6.7]) |
`MeasureTheory.tendstoInMeasure_of_uniform_on` |
| "`ξ_n` converges in distribution, hence …" (boundedness in probability) | |
| | `TendstoInDistribution.eventually_measure_norm_gt_le` |
| continuous mapping for `−log` on `(0, ∞)` (proof of [Hit26, Theorem 5.2.9]) | |
| | `MeasureTheory.tendstoInDistribution_comp_of_continuousOn_Ioi` |
| the chart function space `∏_α C(U_α, ℝ)` ([Hit26]'s `C(M, ℝ)`) | |
| | `ResolutionAtlas.ChartFunctions` |
| `Y^{α*}(χ)` and `Y(χ)`, [Hit26, Equation (5.2.5)] | |
| | `ResolutionAtlas.chartLimit`, `ResolutionAtlas.limitFunctional` |
| `Z_n^α(χ)` of the proof of [Wat09, Theorem 6.7] | `ResolutionAtlas.chartPartition` |
| `Y` is continuous in the uniform topology | `ResolutionAtlas.continuous_limitFunctional` |
| the random inputs of [Wat09, Theorem 6.7] (`ξ_n`, its limit, `ψ_n` tail control) | |
| | `ResolutionAtlas.EmpiricalProcessInput` |
| `Z_n^0`, [Hit26, Equation (5.0.4)] | |
| | `ResolutionAtlas.EmpiricalProcessInput.normalizedEvidence` |
| `Z_n^{≥ε}`, [Hit26, Equation (5.2.4)] | |
| | `ResolutionAtlas.EmpiricalProcessInput.tail` |
| `Z_n^0 = Σ_α Z_n^α(ξ_n) + Z_n^{≥ε}` (a.s.) | `…EmpiricalProcessInput.ae_normalizedEvidence_eq` |
| [Hit26, Equation (5.2.6)] and its consequence | |
| | `…EmpiricalProcessInput.tail_le`, `…EmpiricalProcessInput.tail_tendsto` |
| [Hit26, Equation (5.2.7)], deterministic uniform form | |
| | `ResolutionAtlas.essential_uniform_approx` |
| [Hit26, Equation (5.2.10)], deterministic uniform form | |
| | `ResolutionAtlas.nonessential_uniform_small` |
| [Hit26, Theorem 5.2.6] ([Wat09, Theorem 6.7]) | |
| | `ResolutionAtlas.EmpiricalProcessInput.tendstoInDistribution_normalizedEvidence` |

[Hit26, Lemma 5.2.4] is `abn_inequality`;
[Hit26, Lemma 5.2.5] is
`MeasureTheory.tendstoInMeasure_of_tendstoInDistribution_const` (1), and Mathlib's
`tendstoInDistribution_of_tendstoInMeasure_sub` (2) and
`TendstoInDistribution.add_of_tendstoInMeasure_const` (3), restated here as
`tendstoInDistribution_of_sub_tendstoInMeasure` and
`tendstoInDistribution_add_of_tendstoInMeasure_const`; convergence in probability is
`MeasureTheory.TendstoInMeasure`. The finite-sum and domination lemmas for convergence in
probability (`MeasureTheory.tendstoInMeasure_finset_sum_zero`,
`MeasureTheory.tendstoInMeasure_zero_of_abs_le`) are
consequences of the definition used alongside (2).

## Hypotheses of the formal theorem

The random inputs are the hypothesis structure `EmpiricalProcessInput`; in [Hit26] they
come from fundamental conditions I / II via [Wat09, Theorem 6.1] and [Wat09, Theorem 5.9]. Two
points where the formalisation is more explicit than [Hit26]:

* The chart weights of the essential charts are assumed Lipschitz on the cube
  (`tendstoInDistribution_normalizedEvidence`'s `hLip`). [Hit26]'s weights are `C¹`
  ([Wat09, Theorem 4.9] needs `‖∇φ‖`), so this is weaker than [Hit26]'s hypothesis.
* The tail control uses a bound `B_n` on `sup_{K ≥ ε} |ψ_n|` that is bounded in probability
  (`B_tight`), rather than convergence in distribution of `ψ_n`; this is all the proof uses.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory

open SingularLearningTheory.NormalCrossing

/-- Uniform-on-controlled-sets transfer. If `F_n → G` uniformly on each of the measurable
sets `B j`, and `X_n` eventually lies in some `B j` with probability arbitrarily close to
`1`, then `F_n (X_n) − G (X_n) → 0` in probability. This is the abstract form of the step
"`ξ_n` and `∇ξ_n` converge in distribution, hence the deterministic bound gives convergence
in probability" in the proof of [Hit26, Theorem 5.2.6]; it needs neither a
measurable supremum nor compactness or measurability of the `B j` (only the outer measure
of `{X_n ∉ B j}` enters). -/
theorem _root_.MeasureTheory.tendstoInMeasure_of_uniform_on {Ω S : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℕ → Set S} {X : ℕ → Ω → S} {F : ℕ → S → ℝ} {G : S → ℝ}
    (h1 : ∀ j, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ B j, |F n x - G x| ≤ ε)
    (h2 : ∀ η > 0, ∃ j N : ℕ, ∀ n ≥ N, P {ω | X n ω ∉ B j} ≤ ENNReal.ofReal η) :
    TendstoInMeasure P (fun n ω ↦ F n (X n ω) - G (X n ω)) atTop 0 := by
  refine tendstoInMeasure_of_ne_top fun ε hε hεtop ↦ ?_
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact ⟨0, fun n _ ↦ le_top⟩
  obtain ⟨j, N₁, hN₁⟩ := h2 η.toReal (ENNReal.toReal_pos hη.ne' hηtop)
  obtain ⟨N₂, hN₂⟩ := h1 j (ε.toReal / 2) (by
    have := ENNReal.toReal_pos hε.ne' hεtop
    positivity)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  calc P {ω | ε ≤ edist (F n (X n ω) - G (X n ω)) ((0 : Ω → ℝ) ω)}
      ≤ P {ω | X n ω ∉ B j} := by
        refine measure_mono fun ω hω ↦ ?_
        intro hmem
        have hle := hN₂ n hn₂ (X n ω) hmem
        have hε' : ε.toReal / 2 < ε.toReal := by
          have := ENNReal.toReal_pos hε.ne' hεtop
          linarith
        have : edist (F n (X n ω) - G (X n ω)) ((0 : Ω → ℝ) ω) < ε := by
          rw [edist_dist, Pi.zero_apply, dist_zero_right, Real.norm_eq_abs,
            ← ENNReal.ofReal_toReal hεtop]
          exact ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos hε.ne' hεtop) |>.mpr
            (hle.trans_lt hε')
        exact absurd hω (not_le.mpr this)
    _ ≤ ENNReal.ofReal η.toReal := hN₁ n hn₁
    _ = η := ENNReal.ofReal_toReal hηtop

/-- Domination: if `|Y n| ≤ Z n` almost surely and `Z n → 0` in probability, then
`Y n → 0` in probability. No thesis counterpart. -/
theorem _root_.MeasureTheory.tendstoInMeasure_zero_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    {Y Z : ℕ → Ω → ℝ} (hle : ∀ n, ∀ᵐ ω ∂P, |Y n ω| ≤ Z n ω)
    (hZ : TendstoInMeasure P Z atTop 0) : TendstoInMeasure P Y atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hZ ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hZ ε hε)
    (fun n ↦ zero_le) fun n ↦ measure_mono_ae ?_
  filter_upwards [hle n] with ω hω hε'
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hε' ⊢
  exact hε'.trans (hω.trans (le_abs_self _))

theorem _root_.MeasureTheory.tendstoInMeasure_zero_const {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} :
    TendstoInMeasure P (fun _ : ℕ ↦ (0 : Ω → ℝ)) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp [hε.not_ge]

/-- Sums of sequences converging to `0` in probability converge to `0` in probability.
No thesis counterpart. -/
theorem _root_.MeasureTheory.tendstoInMeasure_add_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    {Y Z : ℕ → Ω → ℝ} (hY : TendstoInMeasure P Y atTop 0) (hZ : TendstoInMeasure P Z atTop 0) :
    TendstoInMeasure P (fun n ω ↦ Y n ω + Z n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hY hZ ⊢
  intro ε hε
  have h := (hY (ε / 2) (half_pos hε)).add (hZ (ε / 2) (half_pos hε))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n ↦ zero_le)
    fun n ↦ (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs, mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  have := abs_add_le (Y n ω) (Z n ω)
  linarith [hcon.1, hcon.2]

theorem _root_.MeasureTheory.tendstoInMeasure_finset_sum_zero {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    (s : Finset ι) {Y : ι → ℕ → Ω → ℝ} (h : ∀ i ∈ s, TendstoInMeasure P (Y i) atTop 0) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ s, Y i n ω) atTop 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact tendstoInMeasure_zero_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact tendstoInMeasure_add_zero (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Convergence in distribution implies boundedness in probability: for every `η > 0` there
is `M` with `P(‖X n‖ > M) ≤ η` for all large `n`. No thesis counterpart ([Hit26]'s
"`ξ_n` converges in distribution, hence ..."). -/
theorem _root_.MeasureTheory.TendstoInDistribution.eventually_measure_norm_gt_le
    {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {X : ℕ → Ω → E} {Z : Ω' → E} (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P')
    {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, P {ω | M < ‖X n ω‖} ≤ ENNReal.ofReal η := by
  have hZ := h.aemeasurable_limit
  have hU : Tendsto (fun M : ℕ ↦ P' {ω | ‖Z ω‖ < M}) atTop
      (𝓝 (P' (⋃ M : ℕ, {ω | ‖Z ω‖ < (M : ℝ)}))) :=
    tendsto_measure_iUnion_atTop fun M M' hMM' ω (hω : ‖Z ω‖ < M) ↦
      show ‖Z ω‖ < M' from hω.trans_le (by exact_mod_cast hMM')
  have hUniv : (⋃ M : ℕ, {ω | ‖Z ω‖ < (M : ℝ)}) = univ := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    exact exists_nat_gt ‖Z ω‖
  rw [hUniv, measure_univ] at hU
  have hη2 : (1 : ENNReal) - ENNReal.ofReal (η / 2) < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ENNReal.ofReal_pos.mpr (half_pos hη)).ne'
  obtain ⟨M, hM⟩ := (hU.eventually (eventually_gt_nhds hη2)).exists
  have hopen : IsOpen {x : E | ‖x‖ < (M : ℝ)} := isOpen_lt continuous_norm continuous_const
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto hopen
  change (P'.map Z) {x : E | ‖x‖ < (M : ℝ)}
      ≤ atTop.liminf fun n ↦ (P.map (X n)) {x : E | ‖x‖ < (M : ℝ)} at hlim
  rw [Measure.map_apply_of_aemeasurable hZ hopen.measurableSet] at hlim
  have hlt : (1 : ENNReal) - ENNReal.ofReal (η / 2)
      < atTop.liminf fun n ↦ (P.map (X n)) {x : E | ‖x‖ < (M : ℝ)} := hM.trans_le hlim
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hlt)
  refine ⟨M, N, fun n hn ↦ ?_⟩
  calc P {ω | (M : ℝ) < ‖X n ω‖}
      = (P.map (X n)) {x : E | (M : ℝ) < ‖x‖} :=
        (Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n)
          (measurableSet_lt measurable_const continuous_norm.measurable)).symm
    _ ≤ (P.map (X n)) {x : E | ‖x‖ < (M : ℝ)}ᶜ :=
        measure_mono fun x (hx : (M : ℝ) < ‖x‖) ↦ show ¬ ‖x‖ < (M : ℝ) from not_lt.mpr hx.le
    _ = 1 - (P.map (X n)) {x : E | ‖x‖ < (M : ℝ)} := prob_compl_eq_one_sub hopen.measurableSet
    _ ≤ 1 - (1 - ENNReal.ofReal (η / 2)) := tsub_le_tsub_left (hN n hn).le _
    _ ≤ ENNReal.ofReal (η / 2) := tsub_tsub_le
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)

/-- For a bounded continuous `F` and any `g, g'` agreeing where `X ≥ c`,
`|∫ F (g X) − ∫ F (g' X)| ≤ 2 ‖F‖ P(X < c)`. No thesis counterpart. -/
private theorem abs_integral_sub_le_of_eqOn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : BoundedContinuousFunction ℝ ℝ) {g g' : ℝ → ℝ} {c : ℝ}
    (hgg' : ∀ x, c ≤ x → g x = g' x) (X : Ω → ℝ)
    (h₁ : AEStronglyMeasurable (fun ω ↦ F (g (X ω))) P)
    (h₂ : AEStronglyMeasurable (fun ω ↦ F (g' (X ω))) P) :
    |(∫ ω, F (g (X ω)) ∂P) - ∫ ω, F (g' (X ω)) ∂P|
      ≤ 2 * ‖F‖ * (P {ω | X ω < c}).toReal := by
  have hint₁ : Integrable (fun ω ↦ F (g (X ω))) P :=
    Integrable.of_bound h₁ ‖F‖ (Eventually.of_forall fun ω ↦ F.norm_coe_le_norm _)
  have hint₂ : Integrable (fun ω ↦ F (g' (X ω))) P :=
    Integrable.of_bound h₂ ‖F‖ (Eventually.of_forall fun ω ↦ F.norm_coe_le_norm _)
  rw [← integral_sub hint₁ hint₂, ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  have hpt : ∀ ω, ENNReal.ofReal ‖F (g (X ω)) - F (g' (X ω))‖
      ≤ {ω | X ω < c}.indicator (fun _ ↦ ENNReal.ofReal (2 * ‖F‖)) ω := by
    intro ω
    by_cases hω : X ω < c
    · rw [indicator_of_mem (show ω ∈ {ω | X ω < c} from hω)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖F (g (X ω)) - F (g' (X ω))‖ ≤ ‖F (g (X ω))‖ + ‖F (g' (X ω))‖ := norm_sub_le _ _
        _ ≤ ‖F‖ + ‖F‖ := add_le_add (F.norm_coe_le_norm _) (F.norm_coe_le_norm _)
        _ = 2 * ‖F‖ := by ring
    · rw [hgg' _ (not_lt.mp hω), sub_self, norm_zero, ENNReal.ofReal_zero]
      exact zero_le
  have hfin : ∫⁻ ω, {ω | X ω < c}.indicator (fun _ ↦ ENNReal.ofReal (2 * ‖F‖)) ω ∂P ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω ↦ indicator_le_self _ _ ω) ?_)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  calc (∫⁻ ω, ENNReal.ofReal ‖F (g (X ω)) - F (g' (X ω))‖ ∂P).toReal
      ≤ (∫⁻ ω, {ω | X ω < c}.indicator (fun _ ↦ ENNReal.ofReal (2 * ‖F‖)) ω ∂P).toReal :=
        ENNReal.toReal_mono hfin (lintegral_mono hpt)
    _ ≤ (ENNReal.ofReal (2 * ‖F‖) * P {ω | X ω < c}).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          (lintegral_indicator_const_le _ _)
    _ = 2 * ‖F‖ * (P {ω | X ω < c}).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- Continuous mapping theorem for a map continuous on `(0, ∞)` and a limit that is almost
surely positive. Used for `x ↦ −log x`. No thesis counterpart ([Hit26] passes from
[Wat09, Theorem 6.7] to `−log Y(ξ)` silently). -/
theorem _root_.MeasureTheory.tendstoInDistribution_comp_of_continuousOn_Ioi {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ioi 0)) (hgm : Measurable g) (hZ : ∀ᵐ ω' ∂P', 0 < Z ω') :
    TendstoInDistribution (fun n ω ↦ g (X n ω)) atTop (fun ω' ↦ g (Z ω')) (fun _ ↦ P) P' := by
  have hXm : ∀ n, AEMeasurable (X n) P := h.forall_aemeasurable
  have hZm : AEMeasurable Z P' := h.aemeasurable_limit
  refine ⟨fun n ↦ hgm.comp_aemeasurable (hXm n), hgm.comp_aemeasurable hZm, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun F ↦ ?_
  simp only [ProbabilityMeasure.coe_mk]
  have hmapZ : ∫ y, F y ∂(Measure.map (fun ω' ↦ g (Z ω')) P') = ∫ ω', F (g (Z ω')) ∂P' :=
    integral_map (φ := fun ω' ↦ g (Z ω')) (hgm.comp_aemeasurable hZm)
      F.continuous.aestronglyMeasurable
  have hmapX : ∀ n, ∫ y, F y ∂(Measure.map (fun ω ↦ g (X n ω)) P) = ∫ ω, F (g (X n ω)) ∂P :=
    fun n ↦ integral_map (φ := fun ω ↦ g (X n ω)) (hgm.comp_aemeasurable (hXm n))
      F.continuous.aestronglyMeasurable
  simp_rw [hmapZ, hmapX]
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- the truncated maps `g_c x = g (max x c)` are continuous
  have hgc : ∀ c : ℝ, 0 < c → Continuous fun x ↦ g (max x c) := fun c hc ↦
    hg.comp_continuous (continuous_id.max continuous_const) fun x ↦
      lt_of_lt_of_le hc (le_max_right x c)
  have hgceq : ∀ c x : ℝ, c ≤ x → g x = g (max x c) := fun c x hcx ↦ by rw [max_eq_left hcx]
  -- `P'(Z ≤ c) → P'(Z ≤ 0) = 0` as `c ↓ 0`
  set δ : ℝ := ε / (8 * (‖F‖ + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  have hZ0 : P' {ω' | Z ω' ≤ 0} = 0 := by
    have := ae_iff.mp hZ
    simpa only [not_lt] using this
  have hanti : Antitone fun k : ℕ ↦ {ω' | Z ω' ≤ 1 / ((k : ℝ) + 1)} := by
    intro k l hkl ω' hω'
    have hkl' : ((k : ℝ) + 1) ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hkl
    exact le_trans hω' (one_div_le_one_div_of_le (by positivity) hkl')
  have hinter : (⋂ k : ℕ, {ω' | Z ω' ≤ 1 / ((k : ℝ) + 1)}) = {ω' | Z ω' ≤ 0} := by
    ext ω'
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro hk
      refine le_of_forall_pos_lt_add fun η hη ↦ ?_
      obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hη
      exact (hk k).trans_lt (by linarith)
    · intro h0 k
      exact h0.trans (by positivity)
  have hlim : Tendsto (fun k : ℕ ↦ P' {ω' | Z ω' ≤ 1 / ((k : ℝ) + 1)}) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P')
      (s := fun k : ℕ ↦ {ω' | Z ω' ≤ 1 / ((k : ℝ) + 1)}) (fun k ↦ (nullMeasurableSet_le hZm
        aemeasurable_const)) hanti ⟨0, measure_ne_top _ _⟩
    rwa [hinter, hZ0] at this
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))).exists
  set c : ℝ := 1 / ((k : ℝ) + 1) with hc_def
  have hc : 0 < c := by positivity
  -- portmanteau: eventually `P(X_n ≤ c) < ofReal δ`
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto
    (isClosed_Iic (a := c))
  have hport' : atTop.limsup (fun n ↦ P {ω | X n ω ≤ c}) < ENNReal.ofReal δ := by
    refine lt_of_le_of_lt ?_ hk
    have h1 : ∀ n, P {ω | X n ω ≤ c} = (P.map (X n)) (Iic c) := fun n ↦
      (Measure.map_apply_of_aemeasurable (hXm n) measurableSet_Iic).symm
    have h2 : P' {ω' | Z ω' ≤ c} = (P'.map Z) (Iic c) :=
      (Measure.map_apply_of_aemeasurable hZm measurableSet_Iic).symm
    simp_rw [h1, h2]
    exact hport
  have hev₁ : ∀ᶠ n in atTop, P {ω | X n ω ≤ c} < ENNReal.ofReal δ :=
    eventually_lt_of_limsup_lt hport'
  -- continuous mapping for the truncated map
  have hcont' := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (h.continuous_comp (hgc c hc)).tendsto F
  simp only [ProbabilityMeasure.coe_mk] at hcont'
  have hmapZc : ∫ y, F y ∂(Measure.map ((fun x ↦ g (max x c)) ∘ Z) P')
      = ∫ ω', F (g (max (Z ω') c)) ∂P' :=
    integral_map ((hgc c hc).measurable.comp_aemeasurable hZm) F.continuous.aestronglyMeasurable
  have hmapXc : ∀ n, ∫ y, F y ∂(Measure.map ((fun x ↦ g (max x c)) ∘ X n) P)
      = ∫ ω, F (g (max (X n ω) c)) ∂P := fun n ↦
    integral_map ((hgc c hc).measurable.comp_aemeasurable (hXm n)) F.continuous.aestronglyMeasurable
  simp_rw [hmapZc, hmapXc] at hcont'
  rw [Metric.tendsto_nhds] at hcont'
  have hev₂ := hcont' (ε / 4) (by positivity)
  filter_upwards [hev₁, hev₂] with n hn₁ hn₂
  -- assemble
  have hZc : (P' {ω' | Z ω' < c}).toReal ≤ δ := by
    refine ENNReal.toReal_le_of_le_ofReal hδ.le ?_
    exact (measure_mono fun ω' (hω' : Z ω' < c) ↦ hω'.le).trans hk.le
  have hXc : (P {ω | X n ω < c}).toReal ≤ δ := by
    refine ENNReal.toReal_le_of_le_ofReal hδ.le ?_
    exact (measure_mono fun ω (hω : X n ω < c) ↦ hω.le).trans hn₁.le
  have hA := abs_integral_sub_le_of_eqOn (P := P) F (hgceq c) (X n)
    (F.continuous.comp_aestronglyMeasurable (hgm.comp_aemeasurable (hXm n)).aestronglyMeasurable)
    (F.continuous.comp_aestronglyMeasurable
      ((hgc c hc).measurable.comp_aemeasurable (hXm n)).aestronglyMeasurable)
  have hB := abs_integral_sub_le_of_eqOn (P := P') F (hgceq c) Z
    (F.continuous.comp_aestronglyMeasurable (hgm.comp_aemeasurable hZm).aestronglyMeasurable)
    (F.continuous.comp_aestronglyMeasurable
      ((hgc c hc).measurable.comp_aemeasurable hZm).aestronglyMeasurable)
  have hF : 2 * ‖F‖ * δ ≤ ε / 4 := by
    rw [hδ_def]
    have h1 : 0 ≤ ‖F‖ := norm_nonneg F
    rw [show 2 * ‖F‖ * (ε / (8 * (‖F‖ + 1))) = ε / 4 * (‖F‖ / (‖F‖ + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  rw [Real.dist_eq] at hn₂ ⊢
  calc |(∫ ω, F (g (X n ω)) ∂P) - ∫ ω', F (g (Z ω')) ∂P'|
      = |((∫ ω, F (g (X n ω)) ∂P) - ∫ ω, F (g (max (X n ω) c)) ∂P) +
          ((∫ ω, F (g (max (X n ω) c)) ∂P) - ∫ ω', F (g (max (Z ω') c)) ∂P') +
          ((∫ ω', F (g (max (Z ω') c)) ∂P') - ∫ ω', F (g (Z ω')) ∂P')| := by ring_nf
    _ ≤ |(∫ ω, F (g (X n ω)) ∂P) - ∫ ω, F (g (max (X n ω) c)) ∂P| +
          |(∫ ω, F (g (max (X n ω) c)) ∂P) - ∫ ω', F (g (max (Z ω') c)) ∂P'| +
          |(∫ ω', F (g (max (Z ω') c)) ∂P') - ∫ ω', F (g (Z ω')) ∂P'| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * ‖F‖ * δ + ε / 4 + 2 * ‖F‖ * δ := by
        refine add_le_add (add_le_add ?_ hn₂.le) ?_
        · exact hA.trans (mul_le_mul_of_nonneg_left hXc (by positivity))
        · rw [abs_sub_comm]
          exact hB.trans (mul_le_mul_of_nonneg_left hZc (by positivity))
    _ < ε := by linarith

/-- [Hit26, Lemma 5.2.4]: `n a² − a b ≥ (a² − b²)/2` for
`n ≥ 1`. -/
private theorem abn_inequality (a b : ℝ) {n : ℝ} (hn : 1 ≤ n) :
    (a ^ 2 - b ^ 2) / 2 ≤ n * a ^ 2 - a * b := by
  nlinarith [sq_nonneg (a - b), mul_nonneg (sub_nonneg.2 hn) (sq_nonneg a)]

/-- [Hit26, Lemma 5.2.5] (1): convergence in
distribution to a constant is convergence in probability (portmanteau, closed sets). -/
theorem _root_.MeasureTheory.tendstoInMeasure_of_tendstoInDistribution_const {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {c : ℝ}
    (h : TendstoInDistribution X atTop (fun _ ↦ c) (fun _ ↦ P) P') :
    TendstoInMeasure P X atTop (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hclosed : IsClosed {x : ℝ | ε ≤ ‖x - c‖} :=
    isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hclosed
  change atTop.limsup (fun n ↦ (P.map (X n)) {x : ℝ | ε ≤ ‖x - c‖})
    ≤ (P'.map fun _ ↦ c) {x : ℝ | ε ≤ ‖x - c‖} at hport
  rw [Measure.map_const, measure_univ, one_smul,
    Measure.dirac_apply' _ hclosed.measurableSet] at hport
  have hc : c ∉ {x : ℝ | ε ≤ ‖x - c‖} := by simp [hε.not_ge]
  rw [indicator_of_notMem hc] at hport
  have hmap : ∀ n, P {ω | ε ≤ ‖X n ω - c‖} = (P.map (X n)) {x : ℝ | ε ≤ ‖x - c‖} := fun n ↦
    (Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hclosed.measurableSet).symm
  simp_rw [hmap]
  exact tendsto_of_le_liminf_of_limsup_le
    (le_liminf_of_le (h := Eventually.of_forall fun _ ↦ zero_le)) hport

/-- [Hit26, Lemma 5.2.5] (2), Mathlib's
`tendstoInDistribution_of_tendstoInMeasure_sub`. -/
private theorem tendstoInDistribution_of_sub_tendstoInMeasure {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {Y Z : ℕ → Ω → ℝ} {Y' : Ω' → ℝ}
    (hY : TendstoInDistribution Y atTop Y' (fun _ ↦ P) P')
    (hYZ : TendstoInMeasure P (fun n ω ↦ Z n ω - Y n ω) atTop 0) (hZ : ∀ n, AEMeasurable (Z n) P) :
    TendstoInDistribution Z atTop Y' (fun _ ↦ P) P' :=
  tendstoInDistribution_of_tendstoInMeasure_sub Z Y' hY hYZ hZ

/-- [Hit26, Lemma 5.2.5] (3), Slutsky,
Mathlib's `TendstoInDistribution.add_of_tendstoInMeasure_const`. -/
private theorem tendstoInDistribution_add_of_tendstoInMeasure_const {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {Y Z : ℕ → Ω → ℝ} {Y' : Ω' → ℝ} {c : ℝ}
    (hY : TendstoInDistribution Y atTop Y' (fun _ ↦ P) P')
    (hZ : TendstoInMeasure P Z atTop (fun _ ↦ c)) (hZm : ∀ n, AEMeasurable (Z n) P) :
    TendstoInDistribution (fun n ω ↦ Y n ω + Z n ω) atTop (fun ω' ↦ Y' ω' + c) (fun _ ↦ P) P' :=
  hY.add_of_tendstoInMeasure_const hZ hZm

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- The chart function space `∏_α C(U_α, ℝ)` in which the chart processes live. -/
abbrev ChartFunctions : Type := (α : R.ι) → C(cube d (R.b α), ℝ)

/-- The constant `γ_α = 1 / (2^{m_α} (m_α − 1)! ∏_{j ∈ P_α} k_j)`. -/
@[expose] noncomputable def chartGamma (α : R.ι) : ℝ :=
  1 / (2 ^ R.chartMult α * (R.chartMult α - 1).factorial * ∏ j ∈ R.primary α, (R.k α j : ℝ))

/-- The limit functional of one chart, `Y^α(ζ)` of [Hit26,
Equation (5.2.5)], written on the whole cube
(the primary coordinates are integrated out trivially, hence the `b^{-m_α}`). -/
@[expose] noncomputable def chartLimit (β : ℝ) (α : R.ι) (ζ : C(cube d (R.b α), ℝ)) : ℝ :=
  R.chartGamma α / R.b α ^ R.chartMult α *
    ∫ v in cube d (R.b α), (∏ j ∈ (R.primary α)ᶜ, v j ^ R.secondaryExponent α j) *
      R.weight α (R.primaryZero α v) *
      ∫ t in Ioi 0, t ^ (R.rlct - 1) *
        Real.exp (-(β * t) + β * Real.sqrt t * ζ (R.primaryZero α v))

/-- `Y(ζ) = Σ_{α ∈ A*} Y^α(ζ_α)`, [Hit26,
Equation (5.2.5)]. -/
@[expose] noncomputable def limitFunctional (β : ℝ) (ζ : R.ChartFunctions) : ℝ :=
  open scoped Classical in ∑ α, if R.IsEssential α then R.chartLimit β α (ζ α) else 0

/-- Coordinatewise clamping of `ℝ^d` onto the cube `[0, b_α]^d`; the identity on the cube.
Extends functions on the cube to measurable functions on `ℝ^d`. -/
@[expose] noncomputable def clamp (α : R.ι) (v : Fin d → ℝ) : cube d (R.b α) :=
  ⟨fun j ↦ max 0 (min (R.b α) (v j)),
    ⟨fun _ ↦ le_max_left _ _, fun _ ↦ max_le (R.b_pos α).le (min_le_left _ _)⟩⟩

theorem clamp_of_mem {α : R.ι} {u : Fin d → ℝ} (hu : u ∈ cube d (R.b α)) :
    R.clamp α u = ⟨u, hu⟩ := by
  refine Subtype.ext (funext fun j ↦ ?_)
  obtain ⟨h0, hb⟩ := mem_cube.1 hu j
  simp only [clamp]
  rw [min_eq_right hb, max_eq_right h0]

theorem continuous_clamp (α : R.ι) : Continuous (R.clamp α) :=
  Continuous.subtype_mk
    (continuous_pi fun j ↦ continuous_const.max (continuous_const.min (continuous_apply j))) _

/-- The chart functional
`Z_n^α(ζ) = ∫_{U_α} e^{-nβu^{2k_α} + β√n u^{k_α} ζ(u)} u^{h_α} φ̃_α(u) du` of the proof of [Hit26,
Theorem 5.2.6], for `ζ ∈ C(U_α, ℝ)`. -/
@[expose] noncomputable def chartPartition (α : R.ι) (β n : ℝ) (ζ : C(cube d (R.b α), ℝ)) : ℝ :=
  ∫ u in cube d (R.b α),
    Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j)) +
        Real.sqrt n * β * (∏ j, u j ^ R.k α j) * ζ (R.clamp α u)) *
      ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)

theorem chartPartition_nonneg (α : R.ι) (β n : ℝ) (ζ : C(cube d (R.b α), ℝ)) :
    0 ≤ R.chartPartition α β n ζ := by
  refine setIntegral_nonneg measurableSet_Icc fun u hu ↦ ?_
  exact mul_nonneg (Real.exp_pos _).le (mul_nonneg
    (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
    (R.weight_nonneg α u hu))

/-- No thesis counterpart: `−nβU² + √n β U ξ ≤ β ξ² / 2` (the first display of the proof of
[Wat09, Theorem 4.8], in the form used for `e^{-nβK_n}` on a chart). -/
theorem _root_.Real.exponent_le_half_sq {n β U ξ : ℝ} (hn : 0 ≤ n) (hβ : 0 ≤ β) :
    -(n * β * U ^ 2) + Real.sqrt n * β * U * ξ ≤ β * ξ ^ 2 / 2 := by
  have h1 : β * Real.sqrt n ^ 2 * U ^ 2 = β * n * U ^ 2 := by rw [Real.sq_sqrt hn]
  have h2 := mul_nonneg hβ (sq_nonneg (Real.sqrt n * U - ξ))
  have h3 := mul_nonneg hβ (mul_nonneg hn (sq_nonneg U))
  nlinarith

theorem _root_.Finset.prod_pow_two_mul (u : Fin d → ℝ) (k : Fin d → ℕ) :
    ∏ j, u j ^ (2 * k j) = (∏ j, u j ^ k j) ^ 2 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ ↦ pow_mul' _ _ _

/-- `vol([0, b]^m) = b^m`. No thesis counterpart. -/
theorem _root_.SingularLearningTheory.volume_cube_toReal (m : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (volume (cube m b)).toReal = b ^ m := by
  rw [cube_eq_pi, volume_pi_pi]
  simp only [Real.volume_Icc, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hb]

/-- An integrand depending only on the second block integrates to `b^m` times its integral
over the second cube. No thesis counterpart. -/
theorem _root_.SingularLearningTheory.setIntegral_prod_cube_snd {m s : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (g : (Fin s → ℝ) → ℝ) :
    ∫ z in cube m b ×ˢ cube s b, g z.2 = b ^ m * ∫ v in cube s b, g v := by
  have := setIntegral_prod_mul (μ := volume) (ν := volume) (fun _ : Fin m → ℝ ↦ (1 : ℝ)) g
    (cube m b) (cube s b)
  simp only [one_mul] at this
  rw [Measure.volume_eq_prod, this, setIntegral_const, measureReal_def, volume_cube_toReal m hb,
    smul_eq_mul, mul_one]

/-! ### Block coordinates of a chart

The primary coordinates of a chart are moved to the first block, the secondary ones to the second,
by `MeasurableEquiv.blockEquiv`; the chart functional and `Y^α` become the two-block
`normalCrossingIntegral` and `frozenLimit` of [Wat09, Theorems 4.8] / 4.9. -/

section Block

/-- Block data of a chart: `m_α = r + 1` and bijections of the primary and secondary
coordinates with `Fin (r + 1)` and `Fin (d − (r + 1))`. -/
theorem exists_blockData (α : R.ι) : ∃ (r : ℕ) (_ : Fin (r + 1) ≃ {j // j ∈ R.primary α})
    (_ : Fin (d - (r + 1)) ≃ {j // j ∉ R.primary α}), r + 1 = R.chartMult α := by
  obtain ⟨r, hr⟩ : ∃ r, r + 1 = R.chartMult α :=
    ⟨_, Nat.succ_pred_eq_of_pos (R.chartMult_pos α)⟩
  have hcardP : Fintype.card {j // j ∈ R.primary α} = r + 1 := by
    rw [Fintype.card_coe, hr]; rfl
  have hcardS : Fintype.card {j // j ∉ R.primary α} = d - (r + 1) := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardP]
  exact ⟨r, (Fintype.equivFinOfCardEq hcardP).symm, (Fintype.equivFinOfCardEq hcardS).symm, hr⟩

variable {r s : ℕ} {α : R.ι} (eP : Fin (r + 1) ≃ {j // j ∈ R.primary α})
  (eS : Fin s ≃ {j // j ∉ R.primary α})

theorem primaryZero_blockEquiv (z : (Fin (r + 1) → ℝ) × (Fin s → ℝ)) :
    R.primaryZero α (MeasurableEquiv.blockEquiv eP eS z) = R.clamp α
        (MeasurableEquiv.blockEquiv eP eS (0, z.2)) := by
  refine Subtype.ext (funext fun j ↦ ?_)
  obtain ⟨t, rfl⟩ := (Equiv.blockIndex eP eS).surjective j
  rcases t with i | i
  · simp only [primaryZero, clamp, Equiv.blockIndex_inl, MeasurableEquiv.blockEquiv_apply_inl,
      (eP i).2, ite_true,
      Pi.zero_apply]
    rw [min_eq_right (R.b_pos α).le, max_self]
  · simp only [primaryZero, clamp, Equiv.blockIndex_inr, MeasurableEquiv.blockEquiv_apply_inr,
      (eS i).2, ite_false]

theorem sum_primary_blockEquiv (z : (Fin (r + 1) → ℝ) × (Fin s → ℝ)) :
    ∑ j ∈ R.primary α, MeasurableEquiv.blockEquiv eP eS z j = ∑ i, z.1 i := by
  rw [Finset.sum_subtype (R.primary α) (fun _ ↦ Iff.rfl), ← Equiv.sum_comp eP]
  simp

theorem prod_compl_primary_blockEquiv (z : (Fin (r + 1) → ℝ) × (Fin s → ℝ)) :
    ∏ j ∈ (R.primary α)ᶜ, MeasurableEquiv.blockEquiv eP eS z j ^ R.secondaryExponent α j
      = NormalCrossing.secondaryWeight (fun i ↦ R.k α (eS i)) (fun i ↦ (R.h α (eS i) : ℝ)) R.rlct
          z.2 := by
  rw [Finset.prod_subtype (R.primary α)ᶜ (fun _ ↦ Finset.mem_compl), ← Equiv.prod_comp eS,
    NormalCrossing.secondaryWeight]
  simp [secondaryExponent]

/-- The chart functional in block coordinates is `Z^0(n, ξ, φ)` of [Wat09, Theorem 4.8] for the
chart's exponent data, with `ξ, φ` the clamped `ζ` and chart weight. -/
theorem chartPartition_eq_blockIntegral (β n : ℝ) (ζ : C(cube d (R.b α), ℝ)) :
    R.chartPartition α β n ζ
      = NormalCrossing.blockIntegral (fun i ↦ R.k α (eP i)) (fun i ↦ (R.h α (eP i) : ℝ))
          (fun i ↦ R.k α (eS i))
          (fun i ↦ (R.h α (eS i) : ℝ)) (R.b α) β 0 n
          (fun z ↦ ζ (R.clamp α (MeasurableEquiv.blockEquiv eP eS z)))
          (fun z ↦ R.weight α (R.clamp α (MeasurableEquiv.blockEquiv eP eS z))) := by
  rw [chartPartition, ← (MeasurableEquiv.blockEquiv_measurePreserving eP
      eS).setIntegral_preimage_emb
    (MeasurableEquiv.blockEquiv eP eS).measurableEmbedding,
        MeasurableEquiv.blockEquiv_preimage_cube, NormalCrossing.blockIntegral]
  refine setIntegral_congr_fun (measurableSet_Icc.prod
    measurableSet_Icc) fun z hz ↦ ?_
  have hu : MeasurableEquiv.blockEquiv eP eS z ∈ cube d (R.b α) := by
    rw [← MeasurableEquiv.blockEquiv_preimage_cube eP eS] at hz; exact hz
  have hsq : Real.sqrt (∏ j, MeasurableEquiv.blockEquiv eP eS z j ^ (2 * R.k α j))
      = ∏ j, MeasurableEquiv.blockEquiv eP eS z j ^ R.k α j := by
    rw [Finset.prod_pow_two_mul, Real.sqrt_sq (Finset.prod_nonneg fun j _ ↦
      pow_nonneg (hu.1 j) _)]
  simp only [Real.rpow_zero, one_mul, potential, NormalCrossing.monomialWeight]
  rw [← MeasurableEquiv.prod_blockEquiv eP eS fun j x ↦ x ^ (2 * R.k α j), hsq,
    ← MeasurableEquiv.prod_blockEquiv eP eS fun j x ↦ x ^ (R.h α j : ℝ), R.clamp_of_mem hu]
  ring

/-- `Y^α` in block coordinates is the `frozenLimit` of [Wat09, Theorem 4.9] for the chart's exponent
data, for a chart with `λ_α = λ`. -/
theorem chartLimit_eq_frozenLimit (hα : R.chartRlct α = R.rlct) (hr : r + 1 = R.chartMult α)
    (β : ℝ) (ζ : C(cube d (R.b α), ℝ)) :
    R.chartLimit β α ζ
      = frozenLimit (fun i ↦ R.k α (eP i)) (fun i ↦ (R.h α (eP i) : ℝ)) (fun i ↦ R.k α (eS i))
          (fun i ↦ (R.h α (eS i) : ℝ)) R.rlct (R.b α) β
          (fun v ↦ ζ (R.clamp α (MeasurableEquiv.blockEquiv eP eS (0, v))))
          (fun v ↦ R.weight α (R.clamp α (MeasurableEquiv.blockEquiv eP eS (0, v)))) := by
  have hb := R.b_pos α
  have hγ : NormalCrossing.gammaConst (fun i ↦ R.k α (eP i)) (fun i ↦ (R.h α (eP i) : ℝ)) R.rlct
      (R.b α)
      = R.chartGamma α := by
    have hk : ∀ i, (R.h α (eP i) : ℝ) + 1 = 2 * R.k α (eP i) * R.rlct := fun i ↦ by
      have h1 := R.ratio_eq_of_mem_primary (eP i).2
      have hk : (0 : ℝ) < R.k α (eP i) := by exact_mod_cast R.k_pos_of_mem_primary (eP i).2
      rw [hα, div_eq_iff (by positivity)] at h1
      linarith
    have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦ hk i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.sum_mul, ← Finset.mul_sum] at hsum
    have hexp : (∑ i, (R.h α (eP i) : ℝ)) + ((r + 1 : ℕ) : ℝ)
        - 2 * ((∑ i, R.k α (eP i) : ℕ) : ℝ) * R.rlct = 0 := by
      push_cast at hsum ⊢; linarith
    rw [NormalCrossing.gammaConst, chartGamma, hexp, Real.rpow_zero, ← hr, Nat.add_sub_cancel,
      ← Finset.prod_coe_sort (R.primary α), ← Equiv.prod_comp eP]
  have h2 : ∀ z : (Fin (r + 1) → ℝ) × (Fin s → ℝ),
      R.primaryZero α (MeasurableEquiv.blockEquiv eP eS z) = R.clamp α
          (MeasurableEquiv.blockEquiv eP eS (0, z.2)) :=
    R.primaryZero_blockEquiv eP eS
  rw [chartLimit, frozenLimit, hγ, ← (MeasurableEquiv.blockEquiv_measurePreserving eP
      eS).setIntegral_preimage_emb
    (MeasurableEquiv.blockEquiv eP eS).measurableEmbedding,
        MeasurableEquiv.blockEquiv_preimage_cube]
  simp_rw [R.prod_compl_primary_blockEquiv eP eS, h2]
  rw [setIntegral_prod_cube_snd hb.le fun v ↦
    NormalCrossing.secondaryWeight (fun i ↦ R.k α (eS i)) (fun i ↦ (R.h α (eS i) : ℝ)) R.rlct v *
      R.weight α (R.clamp α (MeasurableEquiv.blockEquiv eP eS (0, v))) *
      ∫ t in Ioi 0, t ^ (R.rlct - 1) *
        Real.exp (-(β * t) + β * Real.sqrt t * ζ (R.clamp α (MeasurableEquiv.blockEquiv eP eS
            (0, v)))), ← hr]
  field_simp

end Block

/-! ### Continuity of `Y` -/

/-- The inner integral `J(x) = ∫₀^∞ t^{λ-1} e^{-βt + β√t x} dt` of `Y^α`. -/
@[expose] noncomputable def _root_.SingularLearningTheory.frozenInner (lam β x : ℝ) : ℝ :=
  ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * x)

/-- `J` is Lipschitz on `[-M, M]`: `|J(x) − J(y)| ≤ β e^{βM²/2} (∫₀^∞ t^{λ-1/2} e^{-βt/2}) |x − y|`.
No thesis counterpart ([Hit26]: "`Y` is continuous with respect to the uniform topology"). -/
theorem _root_.SingularLearningTheory.abs_frozenInner_sub_le {lam β : ℝ} (hlam0 : 0 < lam)
    (hβ : 0 < β) {x y M : ℝ}
    (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |frozenInner lam β x - frozenInner lam β y|
      ≤ β * Real.exp (β * M ^ 2 / 2) *
          (∫ t in Ioi 0, t ^ (lam - 1 / 2) * Real.exp (-(β * t / 2))) * |x - y| := by
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ (lam - 1 / 2) * Real.exp (-(β * t / 2))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_half (by linarith) hβ
  rw [frozenInner, frozenInner, ← integral_sub (NormalCrossing.integrableOn_rpow_mul_exp_frozen
      hlam0 hβ hx)
    (NormalCrossing.integrableOn_rpow_mul_exp_frozen hlam0 hβ hy), ← Real.norm_eq_abs]
  calc ‖∫ t in Ioi 0, (t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * x) -
          t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * y))‖
      ≤ ∫ t in Ioi 0, β * Real.exp (β * M ^ 2 / 2) * |x - y| *
          (t ^ (lam - 1 / 2) * Real.exp (-(β * t / 2))) := by
        refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht : 0 < t := ht
        have hbx : -(β * t) + β * Real.sqrt t * x ≤ β * M ^ 2 / 2 + -(β * t / 2) := by
          have := NormalCrossing.exp_frozen_le hβ.le ht.le hx
          rwa [← Real.exp_add, Real.exp_le_exp] at this
        have hby : -(β * t) + β * Real.sqrt t * y ≤ β * M ^ 2 / 2 + -(β * t / 2) := by
          have := NormalCrossing.exp_frozen_le hβ.le ht.le hy
          rwa [← Real.exp_add, Real.exp_le_exp] at this
        have hsq : t ^ (lam - 1) * Real.sqrt t = t ^ (lam - 1 / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]; ring_nf
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
        calc t ^ (lam - 1) * |Real.exp (-(β * t) + β * Real.sqrt t * x) -
                Real.exp (-(β * t) + β * Real.sqrt t * y)|
            ≤ t ^ (lam - 1) * (Real.exp (β * M ^ 2 / 2 + -(β * t / 2)) *
                |(-(β * t) + β * Real.sqrt t * x) - (-(β * t) + β * Real.sqrt t * y)|) :=
              mul_le_mul_of_nonneg_left (Real.abs_exp_sub_exp_le hbx hby) (Real.rpow_nonneg ht.le _)
          _ = t ^ (lam - 1) * (Real.exp (β * M ^ 2 / 2 + -(β * t / 2)) *
                (β * Real.sqrt t * |x - y|)) := by
              congr 2
              rw [show (-(β * t) + β * Real.sqrt t * x) - (-(β * t) + β * Real.sqrt t * y)
                  = β * Real.sqrt t * (x - y) by ring, abs_mul,
                abs_of_nonneg (mul_nonneg hβ.le (Real.sqrt_nonneg t))]
          _ = β * Real.exp (β * M ^ 2 / 2) * |x - y| *
                ((t ^ (lam - 1) * Real.sqrt t) * Real.exp (-(β * t / 2))) := by
              rw [Real.exp_add]; ring
          _ = _ := by rw [hsq]
    _ = _ := by rw [integral_const_mul]; ring

theorem _root_.SingularLearningTheory.continuous_frozenInner {lam β : ℝ} (hlam0 : 0 < lam)
    (hβ : 0 < β) :
    Continuous (frozenInner lam β) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hmem : x₀ ∈ Metric.ball (0 : ℝ) (|x₀| + 1) := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]; linarith
  set C := β * Real.exp (β * (|x₀| + 1) ^ 2 / 2) *
    ∫ t in Ioi 0, t ^ (lam - 1 / 2) * Real.exp (-(β * t / 2)) with hC_def
  have hC : 0 ≤ C :=
    mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht ↦
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)
  refine (LipschitzOnWith.continuousOn (K := Real.toNNReal C) ?_).continuousAt
    (Metric.closedBall_mem_nhds_of_mem hmem)
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at hx hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC]
  exact abs_frozenInner_sub_le hlam0 hβ hx hy

theorem continuous_primaryZero (α : R.ι) : Continuous (R.primaryZero α) := by
  refine Continuous.subtype_mk (continuous_pi fun j ↦ ?_) _
  split_ifs
  · exact continuous_const
  · exact continuous_const.max (continuous_const.min (continuous_apply j))

/-- The trace weight `v^μ φ̃_α(0, v)` of `Y^α`, on the whole cube. -/
@[expose] noncomputable def traceWeight (α : R.ι) (v : Fin d → ℝ) : ℝ :=
  (∏ j ∈ (R.primary α)ᶜ, v j ^ R.secondaryExponent α j) * R.weight α (R.primaryZero α v)

theorem chartLimit_eq (β : ℝ) (α : R.ι) (ζ : C(cube d (R.b α), ℝ)) :
    R.chartLimit β α ζ = R.chartGamma α / R.b α ^ R.chartMult α *
      ∫ v in cube d (R.b α), R.traceWeight α v * frozenInner R.rlct β (ζ (R.primaryZero α v)) :=
  rfl

theorem continuous_weight_primaryZero (α : R.ι) :
    Continuous fun v ↦ R.weight α (R.primaryZero α v) :=
  (R.weight_continuousOn α).comp_continuous
    (continuous_subtype_val.comp (R.continuous_primaryZero α)) fun v ↦ (R.primaryZero α v).2

/-- The trace weight is integrable on the cube: every secondary exponent exceeds `−1`. -/
theorem integrableOn_traceWeight (α : R.ι) :
    IntegrableOn (R.traceWeight α) (cube d (R.b α)) := by
  have hb := R.b_pos α
  have hμ : ∀ j, -1 < (if j ∈ R.primary α then (0 : ℝ) else R.secondaryExponent α j) := fun j ↦ by
    split_ifs with hj
    · norm_num
    · exact R.neg_one_lt_secondaryExponent hj
  have hprod : ∀ v : Fin d → ℝ, ∏ j ∈ (R.primary α)ᶜ, v j ^ R.secondaryExponent α j
      = ∏ j, v j ^ (if j ∈ R.primary α then (0 : ℝ) else R.secondaryExponent α j) := by
    intro v
    rw [show (R.primary α)ᶜ = Finset.univ.filter (fun j ↦ j ∉ R.primary α) by ext; simp,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    by_cases hj : j ∈ R.primary α <;> simp [hj]
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (R.weight_continuousOn α)
  refine ((integrableOn_cube_rpow hμ hb).bdd_mul (c := P)
    (R.continuous_weight_primaryZero α).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v ↦ hP _ (R.primaryZero α v).2)).congr
    (Filter.Eventually.of_forall fun v ↦ ?_)
  simp only [traceWeight, hprod]
  ring

theorem integrableOn_traceWeight_mul_frozenInner {β : ℝ} (hβ : 0 < β) (α : R.ι)
    (ζ : C(cube d (R.b α), ℝ)) :
    IntegrableOn (fun v ↦ R.traceWeight α v * frozenInner R.rlct β (ζ (R.primaryZero α v)))
      (cube d (R.b α)) := by
  refine ((R.integrableOn_traceWeight α).bdd_mul
    (c := Real.exp (β * ‖ζ‖ ^ 2 / 2) * ∫ t in Ioi 0, t ^ (R.rlct - 1) * Real.exp (-(β * t / 2)))
    ((continuous_frozenInner R.rlct_pos hβ).comp
      ((map_continuous ζ).comp (R.continuous_primaryZero α))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v ↦ ?_)).congr
    (Filter.Eventually.of_forall fun v ↦ mul_comm _ _)
  exact (Real.norm_eq_abs _).le.trans (NormalCrossing.abs_integral_rpow_mul_exp_frozen_le R.rlct_pos
      hβ
    ((Real.norm_eq_abs _).symm.le.trans (ContinuousMap.norm_coe_le_norm ζ _)))

/-- `Y^α` is Lipschitz on sup-norm balls. No thesis counterpart. -/
theorem abs_chartLimit_sub_le {β : ℝ} (hβ : 0 < β) (α : R.ι) {M : ℝ} {ζ₁ ζ₂ : C(cube d (R.b α), ℝ)}
    (h₁ : ‖ζ₁‖ ≤ M) (h₂ : ‖ζ₂‖ ≤ M) :
    |R.chartLimit β α ζ₁ - R.chartLimit β α ζ₂|
      ≤ |R.chartGamma α / R.b α ^ R.chartMult α| * (∫ v in cube d (R.b α), |R.traceWeight α v|) *
          (β * Real.exp (β * M ^ 2 / 2) *
            ∫ t in Ioi 0, t ^ (R.rlct - 1 / 2) * Real.exp (-(β * t / 2))) * ‖ζ₁ - ζ₂‖ := by
  rw [chartLimit_eq, chartLimit_eq, ← mul_sub,
    ← integral_sub (R.integrableOn_traceWeight_mul_frozenInner hβ α ζ₁)
      (R.integrableOn_traceWeight_mul_frozenInner hβ α ζ₂), abs_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.norm_eq_abs, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((R.integrableOn_traceWeight α).abs.mul_const _) ?_
  refine Filter.Eventually.of_forall fun v ↦ ?_
  have hζ : |ζ₁ (R.primaryZero α v) - ζ₂ (R.primaryZero α v)| ≤ ‖ζ₁ - ζ₂‖ := by
    rw [← ContinuousMap.sub_apply, ← Real.norm_eq_abs]
    exact ContinuousMap.norm_coe_le_norm _ _
  have hL : 0 ≤ β * Real.exp (β * M ^ 2 / 2) *
      ∫ t in Ioi 0, t ^ (R.rlct - 1 / 2) * Real.exp (-(β * t / 2)) :=
    mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht ↦
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)
  rw [← mul_sub, Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (abs_frozenInner_sub_le R.rlct_pos hβ
    ((Real.norm_eq_abs _).symm.le.trans ((ContinuousMap.norm_coe_le_norm ζ₁ _).trans h₁))
    ((Real.norm_eq_abs _).symm.le.trans ((ContinuousMap.norm_coe_le_norm ζ₂ _).trans h₂))).trans
    (mul_le_mul_of_nonneg_left hζ hL)

/-- `Y^α : C(U_α, ℝ) → ℝ` is continuous (locally Lipschitz). -/
theorem continuous_chartLimit {β : ℝ} (hβ : 0 < β) (α : R.ι) : Continuous (R.chartLimit β α) := by
  rw [continuous_iff_continuousAt]
  intro ζ₀
  have hmem : ζ₀ ∈ Metric.ball (0 : C(cube d (R.b α), ℝ)) (‖ζ₀‖ + 1) := by
    rw [mem_ball_zero_iff]; linarith
  set C := |R.chartGamma α / R.b α ^ R.chartMult α| *
    (∫ v in cube d (R.b α), |R.traceWeight α v|) *
    (β * Real.exp (β * (‖ζ₀‖ + 1) ^ 2 / 2) *
      ∫ t in Ioi 0, t ^ (R.rlct - 1 / 2) * Real.exp (-(β * t / 2))) with hC_def
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (integral_nonneg fun v ↦ abs_nonneg (R.traceWeight α v)))
      (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht ↦
        mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le))
  refine (LipschitzOnWith.continuousOn (K := Real.toNNReal C) ?_).continuousAt
    (Metric.closedBall_mem_nhds_of_mem hmem)
  refine LipschitzOnWith.of_dist_le_mul fun ζ₁ h₁ ζ₂ h₂ ↦ ?_
  rw [mem_closedBall_zero_iff] at h₁ h₂
  rw [dist_eq_norm, Real.norm_eq_abs, dist_eq_norm, Real.coe_toNNReal _ hC]
  exact R.abs_chartLimit_sub_le hβ α h₁ h₂

/-- `Y : ∏_α C(U_α, ℝ) → ℝ` is continuous in the product sup-norm topology ([Hit26]'s
"`Y` is continuous with respect to the uniform topology on `C(M, ℝ)`"). -/
theorem continuous_limitFunctional {β : ℝ} (hβ : 0 < β) : Continuous (R.limitFunctional β) := by
  unfold limitFunctional
  refine continuous_finsetSum _ fun α _ ↦ ?_
  split_ifs
  · exact (R.continuous_chartLimit hβ α).comp (continuous_apply α)
  · exact continuous_const

/-- No thesis counterpart. `n^λ e^{-cn} / (log n)^{m-1} → 0` for every `λ`, `m`, the decay of
the tail [Hit26, Equation (5.2.6)]. -/
theorem _root_.Real.tendsto_normalization_mul_exp (lam : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ lam / Real.log n ^ (m - 1) * Real.exp (-(n * c)))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam c hc).comp
    tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · exact Filter.Eventually.of_forall fun n ↦ mul_nonneg (div_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg (Real.log_natCast_nonneg n) _))
      (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans h3
    simp only [Function.comp]
    calc (n : ℝ) ^ lam / Real.log n ^ (m - 1) * Real.exp (-(n * c))
        ≤ (n : ℝ) ^ lam / 1 * Real.exp (-(n * c)) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left
            (Real.rpow_nonneg (Nat.cast_nonneg n) _) one_pos (one_le_pow₀ hlog))
            (Real.exp_pos _).le
      _ = (n : ℝ) ^ lam * Real.exp (-c * n) := by rw [div_one]; ring_nf

/-! ### The two chart estimates of the proof of [Wat09, Theorem 6.7] -/

/-- A weight that is Lipschitz on the cube is Lipschitz towards its primary trace:
`|φ̃(u) − φ̃(0, v)| ≤ L Σ_{j ∈ P} u_j` (the sup distance from `u` to `(0, v)` is at most the
sum of the primary coordinates). -/
theorem weight_sub_primaryZero_le {α : R.ι} {L : NNReal}
    (hL : LipschitzOnWith L (R.weight α) (cube d (R.b α))) {u : Fin d → ℝ}
    (hu : u ∈ cube d (R.b α)) :
    |R.weight α u - R.weight α (R.primaryZero α u)| ≤ L * ∑ j ∈ R.primary α, u j := by
  have hsum : 0 ≤ ∑ j ∈ R.primary α, u j :=
    Finset.sum_nonneg fun j _ ↦ hu.1 j
  have hdist : dist u (R.primaryZero α u) ≤ ∑ j ∈ R.primary α, u j := by
    refine (dist_pi_le_iff hsum).mpr fun j ↦ ?_
    by_cases hj : j ∈ R.primary α
    · simp only [primaryZero, hj, ite_true, Real.dist_eq, sub_zero,
        abs_of_nonneg (hu.1 j)]
      exact Finset.single_le_sum (fun i _ ↦ hu.1 i) hj
    · obtain ⟨h0, hb⟩ := mem_cube.1 hu j
      simp only [primaryZero, hj, ite_false, Real.dist_eq, min_eq_right hb, max_eq_right h0,
        sub_self, abs_zero]
      exact hsum
  rw [← Real.dist_eq]
  exact (hL.dist_le_mul u hu _ (R.primaryZero α u).2).trans
    (mul_le_mul_of_nonneg_left hdist L.2)

theorem measurable_clamp_comp {α : R.ι} (ζ : C(cube d (R.b α), ℝ)) :
    Measurable fun v ↦ ζ (R.clamp α v) :=
  (map_continuous ζ).measurable.comp (R.continuous_clamp α).measurable

theorem measurable_weight_clamp (α : R.ι) : Measurable fun v ↦ R.weight α (R.clamp α v) :=
  ((R.weight_continuousOn α).comp_continuous
    (continuous_subtype_val.comp (R.continuous_clamp α)) fun v ↦ (R.clamp α v).2).measurable

/-- The essential-chart estimate [Hit26, Equation (5.2.7)] in its
deterministic, uniform form: for an essential chart with Lipschitz weight, uniformly over
`ζ` with `‖ζ‖ ≤ M` and primary Lipschitz constant `L`,
`n^λ Z_n^α(ζ) / (log n)^{m-1} − Y^α(ζ) → 0` ([Wat09, Theorem 4.9] via `uniform_approx`). -/
theorem essential_uniform_approx {α : R.ι} (hα : R.IsEssential α) {Lw : NNReal}
    (hLw : LipschitzOnWith Lw (R.weight α) (cube d (R.b α))) {β : ℝ} (hβ : 0 < β) (M L : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ζ : C(cube d (R.b α), ℝ), ‖ζ‖ ≤ M →
      (∀ u : cube d (R.b α),
        |ζ u - ζ (R.primaryZero α u)| ≤ L * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j) →
      |(n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * R.chartPartition α β n ζ
        - R.chartLimit β α ζ| ≤ ε := by
  obtain ⟨r, eP, eS, hr⟩ := R.exists_blockData α
  have hb := R.b_pos α
  have hk : ∀ i, 0 < R.k α (eP i) := fun i ↦ R.k_pos_of_mem_primary (eP i).2
  have hlam : ∀ i, ((R.h α (eP i) : ℝ) + 1) / (2 * R.k α (eP i)) = R.rlct := fun i ↦
    (R.ratio_eq_of_mem_primary (eP i).2).trans hα.1
  have hsec : ∀ i, 2 * R.k α (eS i) * R.rlct < (R.h α (eS i) : ℝ) + 1 := fun i ↦ by
    have := R.two_mul_k_mul_chartRlct_lt_of_notMem_primary (eS i).2
    rwa [hα.1] at this
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (R.weight_continuousOn α)
  obtain ⟨N₀, hN₀⟩ := uniform_approx hk hlam R.rlct_pos hsec hb hβ M P L Lw hε
  refine ⟨⌈N₀⌉₊, fun n hn ζ hζ hζL ↦ ?_⟩
  have hn' : N₀ ≤ (n : ℝ) := (Nat.le_ceil N₀).trans (by exact_mod_cast hn)
  have hmult : R.mult - 1 = r := by rw [← hα.2, ← hr, Nat.add_sub_cancel]
  rw [R.chartPartition_eq_blockIntegral eP eS, R.chartLimit_eq_frozenLimit eP eS hα.1 hr,
      hmult]
  have hmemS : ∀ z ∈ cube (r + 1) (R.b α) ×ˢ cube (d - (r + 1)) (R.b α),
      MeasurableEquiv.blockEquiv eP eS z ∈ cube d (R.b α) := fun z hz ↦ by
    rw [← MeasurableEquiv.blockEquiv_preimage_cube eP eS] at hz; exact hz
  refine hN₀ n hn' _ _ ((R.measurable_clamp_comp ζ).comp (MeasurableEquiv.blockEquiv eP
      eS).measurable)
    ((R.measurable_weight_clamp α).comp (MeasurableEquiv.blockEquiv eP eS).measurable)
    (fun z _ ↦ ?_) (fun z _ ↦ ?_) (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · exact (Real.norm_eq_abs _).symm.le.trans ((ContinuousMap.norm_coe_le_norm ζ _).trans hζ)
  · exact (Real.norm_eq_abs _).symm.le.trans (hP _ (R.clamp α _).2)
  · rw [← R.primaryZero_blockEquiv eP eS z, R.clamp_of_mem (hmemS z hz),
      ← R.sum_primary_blockEquiv eP eS z]
    exact hζL ⟨_, hmemS z hz⟩
  · rw [← R.primaryZero_blockEquiv eP eS z, R.clamp_of_mem (hmemS z hz),
      ← R.sum_primary_blockEquiv eP eS z]
    exact R.weight_sub_primaryZero_le hLw (hmemS z hz)

/-- The non-essential-chart estimate [Hit26, Equation (5.2.10)] in its
deterministic, uniform form: for a non-essential chart, uniformly over `ζ` with `‖ζ‖ ≤ M`,
`n^λ Z_n^α(ζ) / (log n)^{m-1} → 0` ([Wat09, Theorem 4.8] and
[Hit26, Equation (5.2.9)]). -/
theorem nonessential_uniform_small {α : R.ι} (hα : ¬ R.IsEssential α) {β : ℝ} (hβ : 0 < β)
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ζ : C(cube d (R.b α), ℝ), ‖ζ‖ ≤ M →
      |(n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * R.chartPartition α β n ζ| ≤ ε := by
  obtain ⟨r, eP, eS, hr⟩ := R.exists_blockData α
  have hb := R.b_pos α
  have hk : ∀ i, 0 < R.k α (eP i) := fun i ↦ R.k_pos_of_mem_primary (eP i).2
  have hlam : ∀ i, ((R.h α (eP i) : ℝ) + 1) / (2 * R.k α (eP i)) = R.chartRlct α := fun i ↦
    R.ratio_eq_of_mem_primary (eP i).2
  have hsec : ∀ i, 2 * R.k α (eS i) * R.chartRlct α < (R.h α (eS i) : ℝ) + 1 := fun i ↦
    R.two_mul_k_mul_chartRlct_lt_of_notMem_primary (eS i).2
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (R.weight_continuousOn α)
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0 ⟨fun j ↦ le_rfl, fun j ↦ hb.le⟩)
  obtain ⟨a₁, -, a₂, ha₂, hZ⟩ := blockIntegral_bounds hk hlam (R.chartRlct_pos α) hsec hb hβ le_rfl
  have hC0 : 0 ≤ a₂ * Real.exp (β * M ^ 2 / 2) * P := by positivity
  have hmlt : R.chartRlct α = R.rlct → r + 1 ≤ R.mult - 1 := fun heq ↦ by
    rcases (R.not_isEssential_iff α).mp hα with hlt | ⟨_, hlt⟩
    · exact absurd heq hlt.ne'
    · omega
  have hdecay := NormalCrossing.tendsto_rpow_div_log_pow_mul_of_le
    (F := fun n : ℝ ↦ if 2 ≤ n then
      a₂ * Real.exp (β * M ^ 2 / 2) * P * Real.log n ^ r / n ^ R.chartRlct α else 0)
    (lam := R.rlct) (q := 0) (r := R.mult - 1) (mlt := r + 1) hC0
    (fun n ↦ by
      split_ifs with hn
      · have : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
        have : 0 < n := by linarith
        positivity
      · exact le_rfl)
    (fun n hn ↦ by rw [ite_eq_left hn, Nat.add_sub_cancel, add_zero])
    (R.rlct_le_chartRlct α) (by omega) hmlt
  have hdecay' := (hdecay.comp tendsto_natCast_atTop_atTop).eventually (eventually_le_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdecay'
  refine ⟨max N 2, fun n hn ζ hζ ↦ ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hnN : N ≤ n := le_of_max_le_left hn
  have ha0 : 0 ≤ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (pow_nonneg (Real.log_nonneg (by linarith)) _)
  rw [abs_of_nonneg (mul_nonneg ha0 (R.chartPartition_nonneg α β n ζ)),
    R.chartPartition_eq_blockIntegral eP eS]
  have hZn := (hZ _ _ M 0 P ((R.measurable_clamp_comp ζ).comp
      (MeasurableEquiv.blockEquiv eP eS).measurable)
    ((R.measurable_weight_clamp α).comp (MeasurableEquiv.blockEquiv eP eS).measurable) le_rfl
    (fun z _ ↦ (Real.norm_eq_abs _).symm.le.trans ((ContinuousMap.norm_coe_le_norm ζ _).trans hζ))
    (fun z _ ↦ R.weight_nonneg α _ (R.clamp α _).2)
    (fun z _ ↦ (Real.le_norm_self _).trans (hP _ (R.clamp α _).2)) n hn2).2
  have hNn := hN n hnN
  simp only [Function.comp, ite_eq_left hn2, add_zero] at hNn
  calc (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
        NormalCrossing.blockIntegral _ _ _ _ (R.b α) β 0 n _ _
      ≤ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
          (a₂ * Real.log n ^ r / n ^ (R.chartRlct α + 0) * Real.exp (β * M ^ 2 / 2) * P) :=
        mul_le_mul_of_nonneg_left hZn ha0
    _ = (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
          (a₂ * Real.exp (β * M ^ 2 / 2) * P * Real.log n ^ r / n ^ R.chartRlct α) := by
        rw [add_zero]; ring
    _ ≤ ε := hNn

/-- The random inputs to [Hit26, Theorem 5.2.6], as consumed by its proof:
an empirical loss `K_n`, chart
processes `ξ_{n,α}` with `K_n ∘ g_α = u^{2k_α} − n^{-1/2} u^{k_α} ξ_{n,α}`, their joint weak
limit, boundedness in probability of their primary Lipschitz constants, and the tail control
`n K_n ≥ nδ/2 − B_n²/2` off the localization. In [Hit26] these are produced from an i.i.d.
sample via [Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]) and
[Hit26, Theorem 4.2.9] ([Wat09, Theorem 5.9]); here they are hypotheses. -/
structure EmpiricalProcessInput (β : ℝ) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P'] where
  /-- The empirical loss `K_n(w) = (1/n) Σ f(X_i, w)`. -/
  Kn : ℕ → Ω → (Fin d → ℝ) → ℝ
  Kn_measurable : ∀ n, Measurable (Function.uncurry (Kn n))
  /-- The chart processes `ξ_{n,α}`, as random elements of `∏_α C(U_α, ℝ)`. -/
  Ξ : ℕ → Ω → R.ChartFunctions
  Ξ_measurable : ∀ n, Measurable (Ξ n)
  /-- [Hit26, Equation (5.2.2)], corrected sign:
  `K_n(g_α(u)) = u^{2k} − n^{-1/2} u^{k} ξ_n(u)` for `n ≥ 1`. -/
  chart_identity : ∀ n, 1 ≤ n → ∀ α, ∀ᵐ ω ∂P, ∀ u : cube d (R.b α),
    Kn n ω (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
      (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * Ξ n ω α u
  /-- The limit process `ξ` on a probability space `Ω'`. -/
  Ξlim : Ω' → R.ChartFunctions
  /-- Joint convergence in distribution of all chart processes
  ([Hit26, Theorem 4.2.9]). -/
  tendsto : TendstoInDistribution Ξ atTop Ξlim (fun _ ↦ P) P'
  /-- Boundedness in probability of the Lipschitz constants in the primary coordinates
  ([Hit26]'s "`∇ξ_n` converges in distribution"). -/
  lipschitz_tight : ∀ η > 0, ∃ L : ℝ, ∃ N : ℕ, ∀ n ≥ N,
    P {ω | ¬ ∀ α, ∀ u : cube d (R.b α),
      |Ξ n ω α u - Ξ n ω α (R.primaryZero α u)| ≤ L * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j}
      ≤ ENNReal.ofReal η
  /-- The tail control `n K_n(w) ≥ nδ/2 − B_n²/2` where `χ < 1`, with `B_n` bounded in
  probability ([Hit26]'s `sup_{K ≥ ε} |ψ_n|` and
  [Hit26, Lemma 5.2.4]). -/
  B : ℕ → Ω → ℝ
  B_measurable : ∀ n, Measurable (B n)
  B_tight : ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, P {ω | M < |B n ω|} ≤ ENNReal.ofReal η
  tail_bound : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W, R.χ w < 1 →
    n * R.δ / 2 - B n ω ^ 2 / 2 ≤ n * Kn n ω w

namespace EmpiricalProcessInput

variable {R}
variable {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (I : R.EmpiricalProcessInput β P P')

/-- The normalised partition function
`Z_n^0 = ∫_W e^{-nβK_n(w)} φ(w) dw` of [Hit26,
Equation (5.0.4)]. -/
@[expose] noncomputable def normalizedEvidence (n : ℕ) (ω : Ω) : ℝ :=
  ∫ w in W, Real.exp (-(n * β * I.Kn n ω w)) * φ w

/-- The tail `Z_n^{≥ε}`: the part of `Z_n^0` off the localization, [Hit26,
Equation (5.2.4)]. -/
@[expose] noncomputable def tail (n : ℕ) (ω : Ω) : ℝ :=
  ∫ w in W, Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w)

/-- On a chart, `e^{-nβK_n(g_α(u))} = e^{-nβu^{2k} + √n β u^k ξ_{n,α}(u)}`
([Hit26, Equation (5.2.2)] exponentiated). -/
theorem exp_Kn_comp_g (n : ℕ) (ω : Ω) (α : R.ι)
    (hω : ∀ u : cube d (R.b α), I.Kn n ω (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
      (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * I.Ξ n ω α u)
    {u : Fin d → ℝ} (hu : u ∈ cube d (R.b α)) :
    Real.exp (-(n * β * I.Kn n ω (R.g α u)))
      = Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j)) +
          Real.sqrt n * β * (∏ j, u j ^ R.k α j) * I.Ξ n ω α (R.clamp α u)) := by
  have h := hω ⟨u, hu⟩
  simp only at h
  rw [h, R.clamp_of_mem hu]
  congr 1
  have hs : (n : ℝ) * (Real.sqrt n)⁻¹ = Real.sqrt n := by
    rw [← div_eq_mul_inv, Real.div_sqrt]
  linear_combination (β * (∏ j, u j ^ R.k α j) * I.Ξ n ω α ⟨u, hu⟩) * hs

/-- The chart exponential is bounded by `e^{β‖ξ_{n,α}‖²/2}` on the cube. -/
theorem exp_chart_le (n : ℕ) (ω : Ω) (α : R.ι) (hβ : 0 ≤ β) (u : Fin d → ℝ) :
    Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j)) +
        Real.sqrt n * β * (∏ j, u j ^ R.k α j) * I.Ξ n ω α (R.clamp α u))
      ≤ Real.exp (β * ‖I.Ξ n ω α‖ ^ 2 / 2) := by
  refine Real.exp_le_exp.mpr ?_
  rw [Finset.prod_pow_two_mul]
  refine (Real.exponent_le_half_sq (Nat.cast_nonneg n) hβ).trans ?_
  have hζ : |I.Ξ n ω α (R.clamp α u)| ≤ ‖I.Ξ n ω α‖ :=
    (Real.norm_eq_abs _).symm.le.trans (ContinuousMap.norm_coe_le_norm _ _)
  have : (I.Ξ n ω α (R.clamp α u)) ^ 2 ≤ ‖I.Ξ n ω α‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hζ 2
  gcongr

/-- Off the localization, `e^{-nβK_n} (1 − χ) φ ≤ e^{-nβδ/2 + βB_n²/2} φ`: the pointwise form of
[Hit26, Equation (5.2.6)]. -/
theorem exp_mul_tail_weight_le {n : ℕ} {ω : Ω}
    (hτ : ∀ w ∈ W, R.χ w < 1 → n * R.δ / 2 - I.B n ω ^ 2 / 2 ≤ n * I.Kn n ω w) (hβ : 0 ≤ β)
    {w : Fin d → ℝ} (hw : w ∈ W) (hφw : 0 ≤ φ w) :
    Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w)
      ≤ Real.exp (-(n * β * R.δ / 2) + β * I.B n ω ^ 2 / 2) * φ w := by
  have hχφ : 0 ≤ (1 - R.χ w) * φ w := mul_nonneg (sub_nonneg.2 (R.χ_le_one w)) hφw
  by_cases hχ : R.χ w < 1
  · have h1 := hτ w hw hχ
    have h2 : Real.exp (-(n * β * I.Kn n ω w))
        ≤ Real.exp (-(n * β * R.δ / 2) + β * I.B n ω ^ 2 / 2) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_left h1 hβ
      linarith
    calc Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w)
        ≤ Real.exp (-(n * β * R.δ / 2) + β * I.B n ω ^ 2 / 2) * (1 * φ w) :=
          mul_le_mul h2 (mul_le_mul_of_nonneg_right (sub_le_self _ (R.χ_nonneg w)) hφw)
            hχφ (Real.exp_pos _).le
      _ = _ := by ring
  · have : R.χ w = 1 := le_antisymm (R.χ_le_one w) (not_lt.mp hχ)
    rw [this, sub_self, zero_mul, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le hφw

/-- The decomposition `Z_n^0 = Z_n^{<ε} + Z_n^{≥ε}` with `Z_n^{<ε} = Σ_α Z_n^α(ξ_{n,α})`
([Hit26, Equation (5.2.3)] and
[Hit26, Equation (5.2.4)]) of the proof of
[Hit26, Theorem 5.2.6], almost surely: `transport` moves the localised part to
the charts, where `chart_identity` rewrites the integrand. -/
theorem ae_normalizedEvidence_eq (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P, I.normalizedEvidence n ω = ∑ α, R.chartPartition α β n (I.Ξ n ω α) + I.tail n ω := by
  have hci : ∀ᵐ ω ∂P, ∀ α, ∀ u : cube d (R.b α),
      I.Kn n ω (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
        (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * I.Ξ n ω α u :=
    ae_all_iff.mpr fun α ↦ I.chart_identity n hn α
  filter_upwards [hci, I.tail_bound n] with ω hω hτ
  have hFm : Measurable fun w ↦ Real.exp (-(n * β * I.Kn n ω w)) :=
    Real.measurable_exp.comp (measurable_const.mul (I.Kn_measurable n).of_uncurry_left).neg
  have hFb : ∀ α, ∃ C, ∀ u ∈ cube d (R.b α), |Real.exp (-(n * β * I.Kn n ω (R.g α u)))| ≤ C := by
    intro α
    refine ⟨Real.exp (β * ‖I.Ξ n ω α‖ ^ 2 / 2), fun u hu ↦ ?_⟩
    rw [abs_of_pos (Real.exp_pos _), I.exp_Kn_comp_g n ω α (hω α) hu]
    exact I.exp_chart_le n ω α hβ.le u
  obtain ⟨hint, heq⟩ := R.integral_localized_eq_sum_of_bounded hW hφ hφi hFm hFb
  have htail : IntegrableOn
      (fun w ↦ Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w)) W := by
    refine Integrable.mono'
      (hφi.const_mul (Real.exp (-(n * β * R.δ / 2) + β * I.B n ω ^ 2 / 2))) ?_ ?_
    · exact hFm.aestronglyMeasurable.mul
        ((measurable_const.sub R.χ_measurable).aestronglyMeasurable.mul hφi.aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem hW] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (sub_nonneg.2 (R.χ_le_one w)) (hφ w hw)))]
      exact I.exp_mul_tail_weight_le hτ hβ.le hw (hφ w hw)
  have hsplit : ∀ w, Real.exp (-(n * β * I.Kn n ω w)) * φ w
      = Real.exp (-(n * β * I.Kn n ω w)) * (R.χ w * φ w) +
        Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w) := fun w ↦ by ring
  simp only [normalizedEvidence, tail]
  simp_rw [hsplit]
  rw [integral_add hint htail, heq]
  congr 1
  refine Finset.sum_congr rfl fun α _ ↦
    setIntegral_congr_fun measurableSet_Icc fun u hu ↦ ?_
  rw [I.exp_Kn_comp_g n ω α (hω α) hu]

/-- The integrand of `Z_n^0` is integrable on `W` almost surely: the localised part by
`transport` and the chart bounds, the rest by the tail bound. No thesis counterpart. -/
theorem ae_integrableOn (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P, IntegrableOn (fun w ↦ Real.exp (-(n * β * I.Kn n ω w)) * φ w) W := by
  have hci : ∀ᵐ ω ∂P, ∀ α, ∀ u : cube d (R.b α),
      I.Kn n ω (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
        (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * I.Ξ n ω α u :=
    ae_all_iff.mpr fun α ↦ I.chart_identity n hn α
  filter_upwards [hci, I.tail_bound n] with ω hω hτ
  have hFm : Measurable fun w ↦ Real.exp (-(n * β * I.Kn n ω w)) :=
    Real.measurable_exp.comp (measurable_const.mul (I.Kn_measurable n).of_uncurry_left).neg
  have hFb : ∀ α, ∃ C, ∀ u ∈ cube d (R.b α), |Real.exp (-(n * β * I.Kn n ω (R.g α u)))| ≤ C := by
    intro α
    refine ⟨Real.exp (β * ‖I.Ξ n ω α‖ ^ 2 / 2), fun u hu ↦ ?_⟩
    rw [abs_of_pos (Real.exp_pos _), I.exp_Kn_comp_g n ω α (hω α) hu]
    exact I.exp_chart_le n ω α hβ.le u
  obtain ⟨hint, -⟩ := R.integral_localized_eq_sum_of_bounded hW hφ hφi hFm hFb
  have htail : IntegrableOn
      (fun w ↦ Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w)) W := by
    refine Integrable.mono'
      (hφi.const_mul (Real.exp (-(n * β * R.δ / 2) + β * I.B n ω ^ 2 / 2))) ?_ ?_
    · exact hFm.aestronglyMeasurable.mul
        ((measurable_const.sub R.χ_measurable).aestronglyMeasurable.mul hφi.aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem hW] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (sub_nonneg.2 (R.χ_le_one w)) (hφ w hw)))]
      exact I.exp_mul_tail_weight_le hτ hβ.le hw (hφ w hw)
  exact (hint.add htail).congr
    (Filter.Eventually.of_forall fun w ↦ by simp only [Pi.add_apply]; ring)

theorem tail_nonneg (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (n : ℕ) (ω : Ω) :
    0 ≤ I.tail n ω :=
  setIntegral_nonneg hW fun w hw ↦ mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (sub_nonneg.2 (R.χ_le_one w)) (hφ w hw))

/-- [Hit26, Equation (5.2.6)]:
`Z_n^{≥ε} ≤ e^{-nβδ/2 + βB_n²/2} ∫_W φ` almost surely. -/
theorem tail_le (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) (n : ℕ) :
    ∀ᵐ ω ∂P, I.tail n ω
      ≤ Real.exp (-(n * β * R.δ / 2) + β * I.B n ω ^ 2 / 2) * ∫ w in W, φ w := by
  filter_upwards [I.tail_bound n] with ω hτ
  rw [tail, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (hφi.const_mul _) ?_
  · filter_upwards [ae_restrict_mem hW] with w hw
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (sub_nonneg.2 (R.χ_le_one w)) (hφ w hw))
  · filter_upwards [ae_restrict_mem hW] with w hw
    exact I.exp_mul_tail_weight_le hτ hβ.le hw (hφ w hw)

/-- The tail is negligible in probability: `n^λ Z_n^{≥ε} / (log n)^{m-1} → 0` (the first
part of the proof of [Hit26, Theorem 5.2.6]), for any normalisation `λ, m`. -/
theorem tail_tendsto (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) (lam : ℝ) (m : ℕ) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) ↦ (n : ℝ) ^ lam / Real.log n ^ (m - 1) * I.tail n ω)
      atTop 0 := by
  have hc : 0 ≤ ∫ w in W, φ w := setIntegral_nonneg hW hφ
  have ha0 : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ lam / Real.log n ^ (m - 1) := fun n ↦
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (pow_nonneg (Real.log_natCast_nonneg n) _)
  have hZ := tendstoInMeasure_of_uniform_on (P := P) (B := fun j : ℕ ↦ {x : ℝ | |x| ≤ j})
    (X := I.B) (G := fun _ ↦ (0 : ℝ))
    (F := fun (n : ℕ) (x : ℝ) ↦ (n : ℝ) ^ lam / Real.log n ^ (m - 1) *
      (Real.exp (-(n * β * R.δ / 2)) * Real.exp (β * x ^ 2 / 2) * ∫ w in W, φ w))
    (fun j ε hε ↦ ?_) (fun η hη ↦ ?_)
  · refine tendstoInMeasure_zero_of_abs_le (fun n ↦ ?_) hZ
    filter_upwards [I.tail_le hW hφ hφi hβ n] with ω hω
    simp only [sub_zero]
    rw [Real.exp_add] at hω
    rw [abs_mul, abs_of_nonneg (ha0 n), abs_of_nonneg (I.tail_nonneg hW hφ n ω)]
    exact mul_le_mul_of_nonneg_left hω (ha0 n)
  · have h := (Real.tendsto_normalization_mul_exp lam m (div_pos (mul_pos hβ R.δ_pos)
      two_pos)).mul_const
      (Real.exp (β * (j : ℝ) ^ 2 / 2) * ∫ w in W, φ w)
    rw [zero_mul] at h
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (eventually_le_nhds hε))
    refine ⟨N, fun n hn x hx ↦ ?_⟩
    have hx2 : x ^ 2 ≤ (j : ℝ) ^ 2 := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
    simp only [sub_zero]
    rw [abs_of_nonneg (mul_nonneg (ha0 n)
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hc))]
    calc (n : ℝ) ^ lam / Real.log n ^ (m - 1) *
          (Real.exp (-(n * β * R.δ / 2)) * Real.exp (β * x ^ 2 / 2) * ∫ w in W, φ w)
        ≤ (n : ℝ) ^ lam / Real.log n ^ (m - 1) *
          (Real.exp (-(n * β * R.δ / 2)) * Real.exp (β * (j : ℝ) ^ 2 / 2) * ∫ w in W, φ w) := by
          gcongr
      _ = (n : ℝ) ^ lam / Real.log n ^ (m - 1) * Real.exp (-(n * (β * R.δ / 2))) *
          (Real.exp (β * (j : ℝ) ^ 2 / 2) * ∫ w in W, φ w) := by
          rw [show (n : ℝ) * β * R.δ / 2 = n * (β * R.δ / 2) by ring]; ring
      _ ≤ ε := hN n hn
  · obtain ⟨M, N, hMN⟩ := I.B_tight η hη
    refine ⟨⌈M⌉₊, N, fun n hn ↦ (measure_mono fun ω hω ↦ ?_).trans (hMN n hn)⟩
    simp only [mem_ofPred_eq, not_le] at hω ⊢
    exact (Nat.le_ceil M).trans_lt hω

/-- The core of the proof of [Hit26, Theorem 5.2.6]:
`n^λ Z_n^0 / (log n)^{m−1} − Y(ξ_n) → 0` in probability, from the two chart estimates
(`essential_uniform_approx`, `nonessential_uniform_small`) transferred to the chart processes
and the tail estimate `tail_tendsto`. -/
theorem tendstoInMeasure_normalizedEvidence_sub_limitFunctional (hW : MeasurableSet W)
    (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) (hβ : 0 < β)
    (hLip : ∀ α, R.IsEssential α →
      ∃ L : NNReal, LipschitzOnWith L (R.weight α) (cube d (R.b α))) :
    TendstoInMeasure P (fun (n : ℕ) (ω : Ω) ↦
      (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω -
        R.limitFunctional β (I.Ξ n ω)) atTop 0 := by
  classical
  have hnorm : ∀ α, ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < ‖I.Ξ n ω α‖} ≤ ENNReal.ofReal η := fun α η hη ↦
    (I.tendsto.continuous_comp (continuous_apply α)).eventually_measure_norm_gt_le hη
  have hchart : ∀ α, TendstoInMeasure P (fun (n : ℕ) (ω : Ω) ↦
      (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * R.chartPartition α β n (I.Ξ n ω α) -
        (if R.IsEssential α then R.chartLimit β α (I.Ξ n ω α) else 0)) atTop 0 := by
    intro α
    by_cases hα : R.IsEssential α
    · obtain ⟨Lw, hLw⟩ := hLip α hα
      simp only [ite_eq_left hα]
      refine tendstoInMeasure_of_uniform_on (X := fun n ω ↦ I.Ξ n ω α) (G := R.chartLimit β α)
        (F := fun (n : ℕ) ζ ↦ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
          R.chartPartition α β n ζ)
        (B := fun j : ℕ ↦ {ζ : C(cube d (R.b α), ℝ) |
        ‖ζ‖ ≤ j ∧ ∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)|
          ≤ j * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i}) (fun j ε hε ↦ ?_) (fun η hη ↦ ?_)
      · obtain ⟨N, hN⟩ := R.essential_uniform_approx hα hLw hβ j j hε
        exact ⟨N, fun n hn ζ hζ ↦ hN n hn ζ hζ.1 hζ.2⟩
      · obtain ⟨M, N₁, hN₁⟩ := hnorm α (η / 2) (half_pos hη)
        obtain ⟨L, N₂, hN₂⟩ := I.lipschitz_tight (η / 2) (half_pos hη)
        refine ⟨⌈max M L⌉₊, max N₁ N₂, fun n hn ↦ ?_⟩
        have hM : M ≤ ⌈max M L⌉₊ := (le_max_left M L).trans (Nat.le_ceil _)
        have hL : L ≤ ⌈max M L⌉₊ := (le_max_right M L).trans (Nat.le_ceil _)
        calc P {ω | I.Ξ n ω α ∉ {ζ : C(cube d (R.b α), ℝ) | ‖ζ‖ ≤ ⌈max M L⌉₊ ∧
              ∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)|
                ≤ ⌈max M L⌉₊ * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i}}
            ≤ P ({ω | M < ‖I.Ξ n ω α‖} ∪ {ω | ¬ ∀ α, ∀ u : cube d (R.b α),
                |I.Ξ n ω α u - I.Ξ n ω α (R.primaryZero α u)|
                  ≤ L * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j}) := by
              refine measure_mono fun ω hω ↦ ?_
              by_contra hcon
              simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_not] at hcon
              obtain ⟨hMω, hLω⟩ := hcon
              refine hω ⟨hMω.trans hM, fun u ↦ (hLω α u).trans
                (mul_le_mul_of_nonneg_right hL ?_)⟩
              exact Finset.sum_nonneg fun i _ ↦ u.2.1 i
          _ ≤ P {ω | M < ‖I.Ξ n ω α‖} + P {ω | ¬ ∀ α, ∀ u : cube d (R.b α),
                |I.Ξ n ω α u - I.Ξ n ω α (R.primaryZero α u)|
                  ≤ L * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j} := measure_union_le _ _
          _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
              add_le_add (hN₁ n (le_of_max_le_left hn)) (hN₂ n (le_of_max_le_right hn))
          _ = ENNReal.ofReal η := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
    · simp only [ite_eq_right hα, sub_zero]
      have h1 : ∀ j : ℕ, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ ζ ∈ {ζ : C(cube d (R.b α), ℝ) | ‖ζ‖ ≤ j},
          |(fun (n : ℕ) (ζ : C(cube d (R.b α), ℝ)) ↦
              (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * R.chartPartition α β n ζ) n ζ -
            (fun _ ↦ (0 : ℝ)) ζ| ≤ ε := fun j ε hε ↦ by
        obtain ⟨N, hN⟩ := R.nonessential_uniform_small hα hβ j hε
        exact ⟨N, fun n hn ζ hζ ↦ by simpa using hN n hn ζ hζ⟩
      have h2 : ∀ η > 0, ∃ j N : ℕ, ∀ n ≥ N,
          P {ω | I.Ξ n ω α ∉ {ζ : C(cube d (R.b α), ℝ) | ‖ζ‖ ≤ j}} ≤ ENNReal.ofReal η := by
        intro η hη
        obtain ⟨M, N, hN⟩ := hnorm α η hη
        refine ⟨⌈M⌉₊, N, fun n hn ↦ (measure_mono fun ω hω ↦ ?_).trans (hN n hn)⟩
        simp only [mem_ofPred_eq, not_le] at hω ⊢
        exact (Nat.le_ceil M).trans_lt hω
      simpa only [sub_zero] using tendstoInMeasure_of_uniform_on h1 h2
  refine (tendstoInMeasure_add_zero
    (tendstoInMeasure_finset_sum_zero Finset.univ fun α _ ↦ hchart α)
    (I.tail_tendsto hW hφ hφi hβ R.rlct R.mult)).congr' ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop 1] with n hn
  filter_upwards [I.ae_normalizedEvidence_eq hW hφ hφi hβ hn] with ω hω
  simp only [hω, limitFunctional, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
  ring

/-- [Hit26, Theorem 5.2.6] ([Wat09, Theorem 6.7]): given a resolution atlas
whose essential chart weights are Lipschitz and the empirical-process inputs `I`,
`n^λ Z_n^0 / (log n)^{m-1} → Y(ξ)` in distribution, where `ξ` is the limit of the chart
processes. The ambient hypotheses (`W` measurable, `φ ≥ 0` integrable on `W`) hold in the
thesis's setting; the Lipschitz weights are [Hit26]'s `C¹` chart weights. -/
theorem tendstoInDistribution_normalizedEvidence (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) (hβ : 0 < β)
    (hLip : ∀ α, R.IsEssential α →
      ∃ L : NNReal, LipschitzOnWith L (R.weight α) (cube d (R.b α))) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) ↦ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n
          ω) atTop
      (fun ω' ↦ R.limitFunctional β (I.Ξlim ω')) (fun _ ↦ P) P' := by
  classical
  have hY : TendstoInDistribution (fun n ω ↦ R.limitFunctional β (I.Ξ n ω)) atTop
      (fun ω' ↦ R.limitFunctional β (I.Ξlim ω')) (fun _ ↦ P) P' :=
    I.tendsto.continuous_comp (g := R.limitFunctional β) (R.continuous_limitFunctional hβ)
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun ω ↦ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω) P := fun n
          ↦ by
    have : AEStronglyMeasurable
        (fun p : Ω × (Fin d → ℝ) ↦ Real.exp (-(n * β * I.Kn n p.1 p.2)) * φ p.2)
        (P.prod (volume.restrict W)) :=
      (Real.measurable_exp.comp
        (measurable_const.mul (I.Kn_measurable n)).neg).aestronglyMeasurable.mul
        hφi.aestronglyMeasurable.comp_snd
    exact this.integral_prod_right'.aemeasurable.const_mul _
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hY
    (I.tendstoInMeasure_normalizedEvidence_sub_limitFunctional hW hφ hφi hβ hLip) hmeas

end EmpiricalProcessInput

end ResolutionAtlas

end SingularLearningTheory
