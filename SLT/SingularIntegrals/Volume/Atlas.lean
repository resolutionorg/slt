/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Volume.Block
public import SLT.FreeEnergy.Main
public import SLT.SingularIntegrals.TypeOfAtlas
public import SLT.SingularIntegrals.Zeta.FromResolution
public import SLT.SingularIntegrals.SingularityType
public import SLT.StandardForm.FundamentalConditionI
public import SLT.FreeEnergy.StochasticAsymptotics
public import SLT.SingularIntegrals.DeterministicFreeEnergy
import SLT.SingularIntegrals.Resolution

/-!
# Exact sublevel-volume asymptotics

The block limit is transported through a resolution atlas. Its coefficient
reuses the frozen-limit normalization, and positivity follows from an essential
chart. The final theorem constructs an atlas under the analytic hypotheses.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory

open SingularLearningTheory.NormalCrossing

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The chart sublevel integral at level `1/n`, written using the radial cutoff. -/
@[expose] noncomputable def sublevelChartMass (α : R.ι) (n : ℝ) : ℝ :=
  ∫ u in cube d (R.b α), SublevelVolume.cutoff (n * ∏ j, u j ^ (2 * R.k α j)) *
    ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)

/-- The contribution of an essential chart to the exact volume coefficient. -/
@[expose] noncomputable def sublevelChartCoefficient (α : R.ι) : ℝ :=
  R.chartGamma α / (R.rlct * R.b α ^ R.chartMult α) * R.essentialTraceMass α

/-- The coefficient $c$ of the sublevel volume asymptotics $V(t) \sim c\, t^\lambda (-\log t)^{m-1}$
as $t \to 0^+$ (`SingularLearningTheory.ResolutionAtlas.tendsto_sublevelVolume`): the sum of
`SingularLearningTheory.ResolutionAtlas.sublevelChartCoefficient` over the essential charts. It is
positive for a nondegenerate atlas
(`SingularLearningTheory.NondegenerateResolutionAtlas.sublevelCoefficient_pos`). -/
@[expose] noncomputable def sublevelCoefficient : ℝ :=
  open scoped Classical in ∑ α, if R.IsEssential α then R.sublevelChartCoefficient α else 0

theorem sublevelChartMass_nonneg (α : R.ι) (n : ℝ) :
    0 ≤ R.sublevelChartMass α n := by
  refine setIntegral_nonneg (R.measurableSet_cube α) fun u hu ↦ ?_
  exact mul_nonneg (SublevelVolume.cutoff_nonneg _) (mul_nonneg
    (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
    (R.weight_nonneg α u hu))

theorem sublevelChartCoefficient_nonneg (α : R.ι) :
    0 ≤ R.sublevelChartCoefficient α := by
  have hT : 0 ≤ R.essentialTraceMass α := by
    rw [R.essentialTraceMass_eq]
    exact setIntegral_nonneg (R.measurableSet_cube α) fun v hv ↦ R.traceWeight_nonneg α hv
  exact mul_nonneg (div_nonneg (R.chartGamma_pos α).le
    (mul_nonneg R.rlct_pos.le (pow_nonneg (R.b_pos α).le _))) hT

section Block

variable {r s : ℕ} {α : R.ι}
  (eP : Fin (r + 1) ≃ {j // j ∈ R.primary α})
  (eS : Fin s ≃ {j // j ∉ R.primary α})

theorem sublevelChartMass_eq_blockMass (n : ℝ) :
    R.sublevelChartMass α n =
      SublevelVolume.blockMass (fun i ↦ R.k α (eP i)) (fun i ↦ (R.h α (eP i) : ℝ))
        (fun i ↦ R.k α (eS i)) (fun i ↦ (R.h α (eS i) : ℝ)) (R.b α) n
        (fun z ↦ R.weight α (R.clamp α (MeasurableEquiv.blockEquiv eP eS z))) := by
  rw [sublevelChartMass,
    ← (MeasurableEquiv.blockEquiv_measurePreserving eP eS).setIntegral_preimage_emb
      (MeasurableEquiv.blockEquiv eP eS).measurableEmbedding,
    MeasurableEquiv.blockEquiv_preimage_cube, SublevelVolume.blockMass_eq_setIntegral]
  refine setIntegral_congr_fun (measurableSet_Icc.prod
    measurableSet_Icc) fun z hz ↦ ?_
  have hu : MeasurableEquiv.blockEquiv eP eS z ∈ cube d (R.b α) := by
    rw [← MeasurableEquiv.blockEquiv_preimage_cube eP eS] at hz
    exact hz
  simp only [potential, NormalCrossing.monomialWeight]
  rw [← MeasurableEquiv.prod_blockEquiv eP eS (fun j x ↦ x ^ (2 * R.k α j)),
    ← MeasurableEquiv.prod_blockEquiv eP eS (fun j x ↦ x ^ (R.h α j : ℝ)), R.clamp_of_mem hu]
  ring

/-- Reuse the existing frozen-limit coordinate identity and cancel its positive
radial factor. This supplies all chart permutation and `b^m` normalization algebra. -/
theorem sublevelChartCoefficient_eq_block
    (hα : R.chartRlct α = R.rlct) (hr : r + 1 = R.chartMult α) :
    R.sublevelChartCoefficient α =
      NormalCrossing.gammaConst (fun i ↦ R.k α (eP i)) (fun i ↦ (R.h α (eP i) : ℝ)) R.rlct (R.b α) /
        R.rlct * ∫ v in cube s (R.b α),
          NormalCrossing.secondaryWeight (fun i ↦ R.k α (eS i)) (fun i ↦ (R.h α (eS i) : ℝ)) R.rlct
              v *
            R.weight α (R.clamp α (MeasurableEquiv.blockEquiv eP eS (0, v))) := by
  have heq := R.chartLimit_eq_frozenLimit eP eS hα hr 1
    (0 : C(cube d (R.b α), ℝ))
  rw [R.chartLimit_eq] at heq
  simp only [ContinuousMap.zero_apply, integral_mul_const] at heq
  rw [← R.essentialTraceMass_eq] at heq
  unfold frozenLimit at heq
  simp only [mul_zero, add_zero, one_mul] at heq
  rw [integral_mul_const] at heq
  have hJ : frozenInner R.rlct 1 0 =
      ∫ t in Ioi 0, t ^ (R.rlct - 1) * Real.exp (-t) := by
    simp only [frozenInner, mul_zero, add_zero, one_mul]
  rw [← hJ] at heq
  have hJ0 := frozenInner_pos R.rlct_pos (by norm_num : (0 : ℝ) < 1) 0
  have hc : R.chartGamma α / R.b α ^ R.chartMult α * R.essentialTraceMass α =
      NormalCrossing.gammaConst (fun i ↦ R.k α (eP i)) (fun i ↦ (R.h α (eP i) : ℝ)) R.rlct (R.b α) *
        ∫ v in cube s (R.b α),
          NormalCrossing.secondaryWeight (fun i ↦ R.k α (eS i)) (fun i ↦ (R.h α (eS i) : ℝ)) R.rlct
              v *
            R.weight α (R.clamp α (MeasurableEquiv.blockEquiv eP eS (0, v))) := by
    apply mul_right_cancel₀ hJ0.ne'
    simpa only [mul_assoc] using heq
  have hc' := congrArg (fun x : ℝ ↦ x / R.rlct) hc
  unfold sublevelChartCoefficient
  convert hc' using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

end Block

theorem tendsto_sublevelChartMass_of_essential {α : R.ι} (hα : R.IsEssential α) :
    Tendsto (fun n : ℝ ↦ n ^ R.rlct / Real.log n ^ (R.mult - 1) * R.sublevelChartMass α n)
      atTop (𝓝 (R.sublevelChartCoefficient α)) := by
  obtain ⟨r, eP, eS, hr⟩ := R.exists_blockData α
  obtain ⟨Lw, hLw⟩ := R.exists_lipschitzOnWith_weight α
  have hb := R.b_pos α
  have hk : ∀ i, 0 < R.k α (eP i) := fun i ↦ R.k_pos_of_mem_primary (eP i).2
  have hlam : ∀ i, ((R.h α (eP i) : ℝ) + 1) / (2 * R.k α (eP i)) = R.rlct :=
    fun i ↦ (R.ratio_eq_of_mem_primary (eP i).2).trans hα.1
  have hsec : ∀ i, 2 * R.k α (eS i) * R.rlct < (R.h α (eS i) : ℝ) + 1 := fun i ↦ by
    have hi := R.two_mul_k_mul_chartRlct_lt_of_notMem_primary (eS i).2
    rwa [hα.1] at hi
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (R.weight_continuousOn α)
  have hmemS : ∀ z ∈ cube (r + 1) (R.b α) ×ˢ cube (d - (r + 1)) (R.b α),
      MeasurableEquiv.blockEquiv eP eS z ∈ cube d (R.b α) := fun z hz ↦ by
    rw [← MeasurableEquiv.blockEquiv_preimage_cube eP eS] at hz
    exact hz
  have hphi : ∀ z ∈ cube (r + 1) (R.b α) ×ˢ cube (d - (r + 1)) (R.b α),
      |R.weight α (R.clamp α (MeasurableEquiv.blockEquiv eP eS z))| ≤ P := fun z _ ↦
    (Real.norm_eq_abs _).symm.le.trans (hP _ (R.clamp α _).2)
  have hphiL : ∀ z ∈ cube (r + 1) (R.b α) ×ˢ cube (d - (r + 1)) (R.b α),
      |R.weight α (R.clamp α (MeasurableEquiv.blockEquiv eP eS z)) -
        R.weight α (R.clamp α (MeasurableEquiv.blockEquiv eP eS (0, z.2)))| ≤ (Lw : ℝ) * ∑ j, z.1
            j := by
    intro z hz
    rw [← R.primaryZero_blockEquiv eP eS z, R.clamp_of_mem (hmemS z hz),
      ← R.sum_primary_blockEquiv eP eS z]
    exact R.weight_sub_primaryZero_le hLw (hmemS z hz)
  have h := SublevelVolume.tendsto_blockMass hk hlam R.rlct_pos hsec hb
    ((R.measurable_weight_clamp α).comp (MeasurableEquiv.blockEquiv eP eS).measurable) hphi Lw.2
        hphiL
  dsimp only [Function.comp_apply] at h
  rw [← R.sublevelChartCoefficient_eq_block eP eS hα.1 hr] at h
  have hmult : R.mult - 1 = r := by rw [← hα.2, ← hr, Nat.add_sub_cancel]
  exact h.congr fun n ↦ by
    rw [hmult, R.sublevelChartMass_eq_blockMass eP eS]
    rfl

theorem sublevelChartMass_le_exp_mul_chartIntegral (α : R.ι) (n : ℝ) :
    R.sublevelChartMass α n ≤ Real.exp 1 * R.chartIntegral α 1 n := by
  have hc : ContinuousOn (fun u : Fin d → ℝ ↦
      Real.exp (-(n * 1 * ∏ j, u j ^ (2 * R.k α j))) *
        ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)) (cube d (R.b α)) := by
    refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ (R.weight_continuousOn α))
    · exact (Real.continuous_exp.comp
        ((continuous_const.mul (continuous_finsetProd _ fun j _ ↦
          (continuous_apply j).pow _)).neg)).continuousOn
    · exact (continuous_finsetProd _ fun j _ ↦
        (Real.continuous_rpow_const (Nat.cast_nonneg _)).comp (continuous_apply j)).continuousOn
  have hint := (hc.integrableOn_compact (μ := volume)
    isCompact_Icc).const_mul (Real.exp 1)
  rw [sublevelChartMass, chartIntegral, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ hint ?_
  · filter_upwards [ae_restrict_mem (R.measurableSet_cube α)] with u hu
    exact mul_nonneg (SublevelVolume.cutoff_nonneg _) (mul_nonneg
      (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
      (R.weight_nonneg α u hu))
  · filter_upwards [ae_restrict_mem (R.measurableSet_cube α)] with u hu
    have hρ : 0 ≤ (∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u := mul_nonneg
      (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
      (R.weight_nonneg α u hu)
    simpa only [mul_one, mul_assoc] using
      mul_le_mul_of_nonneg_right (SublevelVolume.cutoff_le_exp
        (n * ∏ j, u j ^ (2 * R.k α j))) hρ

theorem tendsto_sublevelChartMass_of_nonessential {α : R.ι} (hα : ¬ R.IsEssential α) :
    Tendsto (fun n : ℝ ↦ n ^ R.rlct / Real.log n ^ (R.mult - 1) * R.sublevelChartMass α n)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := R.chartIntegral_le α (by norm_num : (0 : ℝ) < 1)
  have hbound : ∀ n : ℝ, 2 ≤ n → R.sublevelChartMass α n ≤
      (Real.exp 1 * max C 0) * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α := by
    intro n hn
    have hn0 : 0 < n := by linarith
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    calc R.sublevelChartMass α n ≤ Real.exp 1 * R.chartIntegral α 1 n :=
          R.sublevelChartMass_le_exp_mul_chartIntegral α n
      _ ≤ Real.exp 1 * (C * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α) :=
          mul_le_mul_of_nonneg_left (hC n hn) (Real.exp_pos _).le
      _ ≤ Real.exp 1 * (max C 0 * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hlog _))
              (Real.rpow_nonneg hn0.le _)) (Real.exp_pos _).le
      _ = _ := by ring
  have hmlt : R.chartRlct α = R.rlct → R.chartMult α ≤ R.mult - 1 := by
    intro heq
    rcases (R.not_isEssential_iff α).mp hα with hlt | ⟨_, hlt⟩
    · exact (hlt.ne' heq).elim
    · omega
  have h := NormalCrossing.tendsto_rpow_div_log_pow_mul_of_le
    (F := R.sublevelChartMass α) (C := Real.exp 1 * max C 0)
    (lam := R.rlct) (q := 0) (thr := R.chartRlct α)
    (r := R.mult - 1) (mlt := R.chartMult α)
    (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))
    (R.sublevelChartMass_nonneg α) (by simpa only [add_zero] using hbound)
    (R.rlct_le_chartRlct α) (R.chartMult_pos α) hmlt
  simpa only [add_zero] using h

theorem tendsto_sum_sublevelChartMass :
    Tendsto (fun n : ℝ ↦ n ^ R.rlct / Real.log n ^ (R.mult - 1) *
      ∑ α, R.sublevelChartMass α n) atTop (𝓝 R.sublevelCoefficient) := by
  classical
  have hchart : ∀ α : R.ι, Tendsto
      (fun n : ℝ ↦ n ^ R.rlct / Real.log n ^ (R.mult - 1) * R.sublevelChartMass α n)
      atTop (𝓝 (if R.IsEssential α then R.sublevelChartCoefficient α else 0)) := by
    intro α
    split_ifs with hα
    · exact R.tendsto_sublevelChartMass_of_essential hα
    · exact R.tendsto_sublevelChartMass_of_nonessential hα
  have hsum := tendsto_finsetSum (Finset.univ : Finset R.ι) fun α _ ↦ hchart α
  simpa only [sublevelCoefficient, Finset.mul_sum] using hsum

/-- Exact transport below the localization threshold, using the existing generic
bounded-integrand transport instead of another measure conversion argument. -/
theorem sublevelVolume_inv_eq_sum (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    {n : ℝ} (hn : 0 < n) (hδ : n⁻¹ < R.δ) :
    sublevelVolume K φ W n⁻¹ = ∑ α, R.sublevelChartMass α n := by
  have hF : Measurable fun w ↦ SublevelVolume.cutoff (n * K w) :=
    SublevelVolume.measurable_cutoff.comp (hKm.const_mul n)
  have hb : ∀ α, ∃ C, ∀ u ∈ cube d (R.b α),
      |SublevelVolume.cutoff (n * K (R.g α u))| ≤ C := by
    intro α
    refine ⟨1, fun u _ ↦ ?_⟩
    rw [abs_of_nonneg (SublevelVolume.cutoff_nonneg _)]
    exact SublevelVolume.cutoff_le_one _
  have htransport := (R.integral_localized_eq_sum_of_bounded hW hφ hφi hF hb).2
  have hcut : ∀ w, n * K w ≤ 1 ↔ K w ≤ n⁻¹ := fun w ↦ by
    rw [← one_div, le_div_iff₀ hn, mul_comm n]
  calc sublevelVolume K φ W n⁻¹
      = ∫ w in W, SublevelVolume.cutoff (n * K w) * (R.χ w * φ w) := by
        refine setIntegral_congr_fun hW fun w hw ↦ ?_
        by_cases hkw : K w ≤ n⁻¹
        · have hχ := R.χ_eq_one w hw (hkw.trans_lt hδ)
          simp [SublevelVolume.cutoff, Set.indicator, hkw, (hcut w).mpr hkw, hχ]
        · have hnkw : ¬ n * K w ≤ 1 := fun h ↦ hkw ((hcut w).mp h)
          simp [SublevelVolume.cutoff, Set.indicator, hkw, hnkw]
    _ = _ := htransport.trans (Finset.sum_congr rfl fun α _ ↦ by
      refine setIntegral_congr_fun (R.measurableSet_cube α) fun u hu ↦ ?_
      rw [R.monomial α u hu])

theorem tendsto_sublevelVolume_inv (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) :
    Tendsto (fun n : ℝ ↦ n ^ R.rlct / Real.log n ^ (R.mult - 1) *
      sublevelVolume K φ W n⁻¹) atTop (𝓝 R.sublevelCoefficient) := by
  refine R.tendsto_sum_sublevelChartMass.congr' ?_
  have hsmall : ∀ᶠ n : ℝ in atTop, n⁻¹ < R.δ :=
    tendsto_inv_atTop_zero.eventually (eventually_lt_nhds R.δ_pos)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with n hn hδ
  rw [R.sublevelVolume_inv_eq_sum hW hKm hφ hφi hn hδ]

theorem tendsto_sublevelVolume (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) :
    Tendsto (fun t : ℝ ↦ sublevelVolume K φ W t /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1)))
      (𝓝[>] 0) (𝓝 R.sublevelCoefficient) := by
  have h := (R.tendsto_sublevelVolume_inv hW hKm hφ hφi).comp tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  simp only [Function.comp_apply, inv_inv, Real.inv_rpow ht0.le, Real.log_inv,
    div_eq_mul_inv, mul_inv_rev]
  ring

end ResolutionAtlas

namespace NondegenerateResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : NondegenerateResolutionAtlas K φ W)

theorem sublevelCoefficient_pos : 0 < R.toResolutionAtlas.sublevelCoefficient := by
  classical
  obtain ⟨α, hα, hT⟩ := R.traceMass_pos
  have hC : 0 < R.toResolutionAtlas.sublevelChartCoefficient α :=
    mul_pos (div_pos (R.toResolutionAtlas.chartGamma_pos α)
      (mul_pos R.toResolutionAtlas.rlct_pos (pow_pos (R.b_pos α) _))) hT
  rw [ResolutionAtlas.sublevelCoefficient]
  refine hC.trans_le ?_
  calc R.toResolutionAtlas.sublevelChartCoefficient α
      = (if R.toResolutionAtlas.IsEssential α then
          R.toResolutionAtlas.sublevelChartCoefficient α else 0) := by rw [ite_eq_left hα]
    _ ≤ ∑ a, if R.toResolutionAtlas.IsEssential a then
          R.toResolutionAtlas.sublevelChartCoefficient a else 0 :=
      Finset.single_le_sum (f := fun a ↦ if R.toResolutionAtlas.IsEssential a then
        R.toResolutionAtlas.sublevelChartCoefficient a else 0) (fun a _ ↦ by
          split_ifs
          · exact R.toResolutionAtlas.sublevelChartCoefficient_nonneg a
          · exact le_rfl) (Finset.mem_univ α)

theorem exists_sublevelVolume_limit (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun t : ℝ ↦ sublevelVolume K φ W t /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0) (𝓝 C) :=
  ⟨R.toResolutionAtlas.sublevelCoefficient, R.sublevelCoefficient_pos,
    R.toResolutionAtlas.tendsto_sublevelVolume hW hKm hφ hφi⟩

end NondegenerateResolutionAtlas

/-- Equality on the parameter domain is enough to preserve every sublevel volume. -/
theorem sublevelVolume_congr_on {d : ℕ} {K K' φ : (Fin d → ℝ) → ℝ}
    {W : Set (Fin d → ℝ)} (hW : MeasurableSet W) (h : ∀ w ∈ W, K w = K' w) (t : ℝ) :
    sublevelVolume K φ W t = sublevelVolume K' φ W t := by
  refine setIntegral_congr_fun hW fun w hw ↦ ?_
  simp only [Set.indicator_apply, Set.mem_ofPred, h w hw]

/-- Exact volume asymptotics under precisely the deterministic analytic assumptions.
The given singularity type is identified with that of the constructed atlas. -/
theorem singularityType_exact_sublevelVolume
    {d : ℕ} (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hKg : ∀ w ∈ W, K w = 0 → ¬ (K =ᶠ[𝓝 w] 0))
    (hφg : ∀ w ∈ W, K w = 0 → ¬ (φ =ᶠ[𝓝 w] 0))
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w))
    (lam : ℝ) (m : ℕ) (htype : IsSingularityType K φ W lam m) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun t ↦ sublevelVolume K φ W t /
      (t ^ lam * (-Real.log t) ^ (m - 1))) (𝓝[>] 0) (𝓝 C) := by
  classical
  obtain ⟨A⟩ := exists_atlasData_of_sublevel_mass hW hKa hK II hKg hφg hvol
  have : Nonempty A.ι := A.nonempty_ι hvol
  let R := A.toNondegenerateResolutionAtlas
  have hWm : MeasurableSet W := hW.isClosed.measurableSet
  obtain ⟨U, hU, hWU, φ₁, φ₂, hφ₁, hφ₁s, hφ₂, hφ₂a, hφeq⟩ := II.factor
  have hφ : ∀ w ∈ W, 0 ≤ φ w := fun w hw ↦ by
    rw [hφeq w (hWU hw)]
    exact mul_nonneg (hφ₁ w (hWU hw)).le (hφ₂ w hw)
  have hφc : ContinuousOn φ W :=
    ((hφ₁s.continuousOn.mul hφ₂a.continuousOn).mono hWU).congr
      (fun w hw ↦ hφeq w (hWU hw))
  have hφi : IntegrableOn φ W := hφc.integrableOn_compact hW
  have hagree : ∀ w ∈ W, K w = W.piecewise K 0 w := fun w hw ↦
    (Set.piecewise_eq_of_mem W _ _ hw).symm
  have hKm : Measurable (W.piecewise K 0) :=
    ContinuousOn.measurable_piecewise hKa.continuousOn continuousOn_const hWm
  have htypeR : IsSingularityType K φ W R.rlct R.mult :=
    ((R.congr hagree).isSingularityType hWm hKm hφ hφi.aemeasurable).congr
      (fun w hw ↦ (hagree w hw).symm)
  obtain ⟨hlam, hm⟩ := htype.unique htypeR
  obtain ⟨C, hC, hlim⟩ := (R.congr hagree).exists_sublevelVolume_limit hWm hKm hφ hφi
  refine ⟨C, hC, ?_⟩
  rw [hlam, hm]
  exact hlim.congr fun t ↦ by
    rw [← sublevelVolume_congr_on hWm hagree t]
    rfl

end SingularLearningTheory
