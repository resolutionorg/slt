/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.StochasticAsymptotics
public import SLT.BayesGibbs.Weighted.BlockLimit
import SLT.SingularIntegrals.DeterministicFreeEnergy
import SLT.SingularIntegrals.Resolution

/-!
# Marked radial integrals on one chart

On a chart $\alpha$ of a resolution atlas, with $K \circ g_\alpha = u^{2k}$ and Jacobian factor
$u^h$, the marked radial integral of a chart field $\zeta$ and a continuous mark $A$ is
$$\int_{[0, b]^d} (u^{2k})^p\, e^{-n\beta u^{2k} + \sqrt n\,\beta u^k \zeta(u)}\, u^h A(u)\,du.$$
Its limit evaluates $\zeta$ and $A$ where the primary coordinates vanish and integrates them
against the secondary weight and the radial kernel
$t^{\lambda + p - 1} e^{-\beta t + \beta\sqrt t\,\zeta}$. Scaled by
$n^{\lambda + p}/(\log n)^{m-1}$, the integral converges to this limit on essential charts and to
zero on the others, uniformly over fields and marks with bounded norm and a bounded Lipschitz
constant in the primary coordinates. The cases $p = 1/2$ and $p = 1$ are the limits of the first
and second feature insertions in the posterior.

## Main definitions

* `SingularLearningTheory.ResolutionAtlas.chartRadialInsertion`: the marked radial integral on a
  chart.
* `SingularLearningTheory.ResolutionAtlas.chartRadialLimit`: its limit.

## Main results

* `SingularLearningTheory.ResolutionAtlas.chartRadialInsertion_eq_blockIntegral` and
  `SingularLearningTheory.ResolutionAtlas.chartRadialLimit_eq_block`: both written in block
  coordinates that separate the primary and the secondary coordinates, the integral as
  `SingularLearningTheory.NormalCrossing.blockIntegral`.
* `SingularLearningTheory.ResolutionAtlas.essential_radial_insertion_uniform`: on an essential chart,
  the scaled integral converges to its limit uniformly.
* `SingularLearningTheory.ResolutionAtlas.nonessential_radial_insertion_uniform`: on a chart that is
  not essential, the scaled integral tends to zero uniformly over bounded fields and marks.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.ResolutionAtlas

open SingularLearningTheory.NormalCrossing

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- A radial insertion with a signed continuous total amplitude. For posterior
insertions use amplitude `chart weight * mark`. -/
@[expose] noncomputable def chartRadialInsertion (α : R.ι) (β p n : ℝ)
    (ζ A : C(cube d (R.b α), ℝ)) : ℝ :=
  ∫ u in cube d (R.b α),
    (∏ j, u j ^ (2 * R.k α j)) ^ p *
      Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j)) +
        Real.sqrt n * β * (∏ j, u j ^ R.k α j) * ζ (R.clamp α u)) *
      (∏ j, u j ^ (R.h α j : ℝ)) * A (R.clamp α u)

/-- The marked radial limit. The secondary measure and chart constant stay
unchanged; the power in the radial kernel is shifted by p. -/
@[expose] noncomputable def chartRadialLimit (β p : ℝ) (α : R.ι)
    (ζ A : C(cube d (R.b α), ℝ)) : ℝ :=
  R.chartGamma α / R.b α ^ R.chartMult α *
    ∫ v in cube d (R.b α),
      (∏ j ∈ (R.primary α)ᶜ, v j ^ R.secondaryExponent α j) *
        A (R.primaryZero α v) *
        ∫ t in Ioi 0, t ^ (R.rlct + p - 1) *
          Real.exp (-(β * t) + β * Real.sqrt t * ζ (R.primaryZero α v))

section Block

variable {r s : ℕ} {α : R.ι} (eP : Fin (r + 1) ≃ {j // j ∈ R.primary α})
  (eS : Fin s ≃ {j // j ∉ R.primary α})

theorem chartRadialInsertion_eq_blockIntegral (β p n : ℝ)
    (ζ A : C(cube d (R.b α), ℝ)) :
    R.chartRadialInsertion α β p n ζ A =
      NormalCrossing.blockIntegral (fun i ↦ R.k α (eP i)) (fun i ↦ (R.h α (eP i) : ℝ))
        (fun i ↦ R.k α (eS i)) (fun i ↦ (R.h α (eS i) : ℝ)) (R.b α) β p n
        (fun z ↦ ζ (R.clamp α (MeasurableEquiv.blockEquiv eP eS z)))
        (fun z ↦ A (R.clamp α (MeasurableEquiv.blockEquiv eP eS z))) := by
  rw [chartRadialInsertion, ← (MeasurableEquiv.blockEquiv_measurePreserving eP
      eS).setIntegral_preimage_emb
    (MeasurableEquiv.blockEquiv eP eS).measurableEmbedding,
        MeasurableEquiv.blockEquiv_preimage_cube, NormalCrossing.blockIntegral]
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦ ?_
  have hu : MeasurableEquiv.blockEquiv eP eS z ∈ cube d (R.b α) := by
    rw [← MeasurableEquiv.blockEquiv_preimage_cube eP eS] at hz; exact hz
  have hsq : Real.sqrt (∏ j, MeasurableEquiv.blockEquiv eP eS z j ^ (2 * R.k α j)) =
      ∏ j, MeasurableEquiv.blockEquiv eP eS z j ^ R.k α j := by
    rw [Finset.prod_pow_two_mul, Real.sqrt_sq (Finset.prod_nonneg fun j _ ↦
      pow_nonneg (hu.1 j) _)]
  simp only [potential, NormalCrossing.monomialWeight]
  rw [← MeasurableEquiv.prod_blockEquiv eP eS fun j x ↦ x ^ (2 * R.k α j), hsq,
    ← MeasurableEquiv.prod_blockEquiv eP eS fun j x ↦ x ^ (R.h α j : ℝ)]

theorem chartRadialLimit_eq_block (hα : R.chartRlct α = R.rlct)
    (hr : r + 1 = R.chartMult α) (β p : ℝ) (ζ A : C(cube d (R.b α), ℝ)) :
    R.chartRadialLimit β p α ζ A =
      NormalCrossing.gammaConst (fun i ↦ R.k α (eP i)) (fun i ↦ (R.h α (eP i) : ℝ)) R.rlct (R.b α) *
        ∫ v in cube s (R.b α),
          NormalCrossing.secondaryWeight (fun i ↦ R.k α (eS i)) (fun i ↦ (R.h α (eS i) : ℝ)) R.rlct
              v *
            A (R.clamp α (MeasurableEquiv.blockEquiv eP eS (0, v))) *
            ∫ t in Ioi 0, t ^ (R.rlct + p - 1) *
              Real.exp (-(β * t) + β * Real.sqrt t *
                ζ (R.clamp α (MeasurableEquiv.blockEquiv eP eS (0, v)))) := by
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
    have hexp : (∑ i, (R.h α (eP i) : ℝ)) + ((r + 1 : ℕ) : ℝ) -
        2 * ((∑ i, R.k α (eP i) : ℕ) : ℝ) * R.rlct = 0 := by
      push_cast at hsum ⊢; linarith
    rw [NormalCrossing.gammaConst, chartGamma, hexp, Real.rpow_zero, ← hr, Nat.add_sub_cancel,
      ← Finset.prod_coe_sort (R.primary α), ← Equiv.prod_comp eP]
  have h2 : ∀ z : (Fin (r + 1) → ℝ) × (Fin s → ℝ),
      R.primaryZero α (MeasurableEquiv.blockEquiv eP eS z) = R.clamp α
          (MeasurableEquiv.blockEquiv eP eS (0, z.2)) :=
    R.primaryZero_blockEquiv eP eS
  rw [chartRadialLimit, hγ, ← (MeasurableEquiv.blockEquiv_measurePreserving eP
      eS).setIntegral_preimage_emb
    (MeasurableEquiv.blockEquiv eP eS).measurableEmbedding,
        MeasurableEquiv.blockEquiv_preimage_cube]
  simp_rw [R.prod_compl_primary_blockEquiv eP eS, h2]
  rw [setIntegral_prod_cube_snd hb.le fun v ↦
    NormalCrossing.secondaryWeight (fun i ↦ R.k α (eS i)) (fun i ↦ (R.h α (eS i) : ℝ)) R.rlct v *
      A (R.clamp α (MeasurableEquiv.blockEquiv eP eS (0, v))) *
      ∫ t in Ioi 0, t ^ (R.rlct + p - 1) *
        Real.exp (-(β * t) + β * Real.sqrt t * ζ (R.clamp α (MeasurableEquiv.blockEquiv eP eS
            (0, v)))), ← hr]
  field_simp

end Block

/-- Uniform essential-chart insertion limit, including the p=1/2 and p=1
limits needed for first and second feature insertions. The amplitude may have
any sign. Its primary modulus and norm bounds are uniform in the conclusion. -/
theorem essential_radial_insertion_uniform {α : R.ι} (hα : R.IsEssential α)
    {β p : ℝ} (hβ : 0 < β) (hp : 0 ≤ p) (M P Lξ LA : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ζ A : C(cube d (R.b α), ℝ),
      ‖ζ‖ ≤ M → ‖A‖ ≤ P →
      (∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)| ≤
        Lξ * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j) →
      (∀ u : cube d (R.b α), |A u - A (R.primaryZero α u)| ≤
        LA * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j) →
      |(n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        R.chartRadialInsertion α β p n ζ A - R.chartRadialLimit β p α ζ A| ≤ ε := by
  obtain ⟨r, eP, eS, hr⟩ := R.exists_blockData α
  have hb := R.b_pos α
  have hk : ∀ i, 0 < R.k α (eP i) := fun i ↦ R.k_pos_of_mem_primary (eP i).2
  have hlam : ∀ i, ((R.h α (eP i) : ℝ) + 1) / (2 * R.k α (eP i)) = R.rlct := fun i ↦
    (R.ratio_eq_of_mem_primary (eP i).2).trans hα.1
  have hsec : ∀ i, 2 * R.k α (eS i) * R.rlct < (R.h α (eS i) : ℝ) + 1 := fun i ↦ by
    have := R.two_mul_k_mul_chartRlct_lt_of_notMem_primary (eS i).2
    rwa [hα.1] at this
  obtain ⟨N₀, hN₀⟩ := uniform_approx_radial_insertion hk hlam R.rlct_pos hsec hb hβ hp
    M P Lξ LA hε
  refine ⟨⌈N₀⌉₊, fun n hn ζ A hζ hA hζL hAL ↦ ?_⟩
  have hn' : N₀ ≤ (n : ℝ) := (Nat.le_ceil N₀).trans (by exact_mod_cast hn)
  have hmult : R.mult - 1 = r := by rw [← hα.2, ← hr, Nat.add_sub_cancel]
  rw [R.chartRadialInsertion_eq_blockIntegral eP eS, R.chartRadialLimit_eq_block eP eS
      hα.1 hr, hmult]
  have hmemS : ∀ z ∈ cube (r + 1) (R.b α) ×ˢ cube (d - (r + 1)) (R.b α),
      MeasurableEquiv.blockEquiv eP eS z ∈ cube d (R.b α) := fun z hz ↦ by
    rw [← MeasurableEquiv.blockEquiv_preimage_cube eP eS] at hz; exact hz
  refine hN₀ n hn' _ _ ((R.measurable_clamp_comp ζ).comp (MeasurableEquiv.blockEquiv eP
      eS).measurable)
    ((R.measurable_clamp_comp A).comp (MeasurableEquiv.blockEquiv eP eS).measurable)
    (fun z _ ↦ ?_) (fun z _ ↦ ?_) (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · exact (Real.norm_eq_abs _).symm.le.trans ((ContinuousMap.norm_coe_le_norm ζ _).trans hζ)
  · exact (Real.norm_eq_abs _).symm.le.trans ((ContinuousMap.norm_coe_le_norm A _).trans hA)
  · rw [← R.primaryZero_blockEquiv eP eS z, R.clamp_of_mem (hmemS z hz),
      ← R.sum_primary_blockEquiv eP eS z]
    exact hζL ⟨_, hmemS z hz⟩
  · rw [← R.primaryZero_blockEquiv eP eS z, R.clamp_of_mem (hmemS z hz),
      ← R.sum_primary_blockEquiv eP eS z]
    exact hAL ⟨_, hmemS z hz⟩

/-- Nonessential signed radial insertions vanish at the global radial scale.
No primary regularity of the amplitude is needed. -/
theorem nonessential_radial_insertion_uniform {α : R.ι} (hα : ¬ R.IsEssential α)
    {β p P : ℝ} (hβ : 0 < β) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ζ A : C(cube d (R.b α), ℝ), ‖ζ‖ ≤ M → ‖A‖ ≤ P →
      |(n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        R.chartRadialInsertion α β p n ζ A| ≤ ε := by
  obtain ⟨r, eP, eS, hr⟩ := R.exists_blockData α
  have hb := R.b_pos α
  have hk : ∀ i, 0 < R.k α (eP i) := fun i ↦ R.k_pos_of_mem_primary (eP i).2
  have hlam : ∀ i, ((R.h α (eP i) : ℝ) + 1) / (2 * R.k α (eP i)) = R.chartRlct α := fun i ↦
    R.ratio_eq_of_mem_primary (eP i).2
  have hsec : ∀ i, 2 * R.k α (eS i) * R.chartRlct α < (R.h α (eS i) : ℝ) + 1 := fun i ↦
    R.two_mul_k_mul_chartRlct_lt_of_notMem_primary (eS i).2
  obtain ⟨a₁, -, a₂, ha₂, hZ⟩ := blockIntegral_bounds hk hlam (R.chartRlct_pos α) hsec hb hβ hp
  have hC0 : 0 ≤ a₂ * Real.exp (β * M ^ 2 / 2) * P := by positivity
  have hmlt : R.chartRlct α = R.rlct → r + 1 ≤ R.mult - 1 := fun heq ↦ by
    rcases (R.not_isEssential_iff α).mp hα with hlt | ⟨_, hlt⟩
    · exact absurd heq hlt.ne'
    · omega
  have hdecay := NormalCrossing.tendsto_rpow_div_log_pow_mul_of_le
    (F := fun n : ℝ ↦ if 2 ≤ n then
      a₂ * Real.exp (β * M ^ 2 / 2) * P * Real.log n ^ r / n ^ (R.chartRlct α + p) else 0)
    (lam := R.rlct) (q := p) (r := R.mult - 1) (mlt := r + 1) hC0
    (fun n ↦ by
      split_ifs with hn
      · have : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
        have : 0 < n := by linarith
        positivity
      · exact le_rfl)
    (fun n hn ↦ by rw [ite_eq_left hn, Nat.add_sub_cancel])
    (R.rlct_le_chartRlct α) (by omega) hmlt
  have hdecay' := (hdecay.comp tendsto_natCast_atTop_atTop).eventually (eventually_le_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdecay'
  refine ⟨max N 2, fun n hn ζ A hζ hA ↦ ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hnN : N ≤ n := le_of_max_le_left hn
  have ha0 : 0 ≤ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (pow_nonneg (Real.log_nonneg (by linarith)) _)
  have hξm := (R.measurable_clamp_comp ζ).comp (MeasurableEquiv.blockEquiv eP eS).measurable
  have hξ : ∀ z ∈ cube (r + 1) (R.b α) ×ˢ cube (d - (r + 1)) (R.b α),
      |ζ (R.clamp α (MeasurableEquiv.blockEquiv eP eS z))| ≤ M := fun z _ ↦
    (Real.norm_eq_abs _).symm.le.trans ((ContinuousMap.norm_coe_le_norm ζ _).trans hζ)
  have hAb : ∀ z ∈ cube (r + 1) (R.b α) ×ˢ cube (d - (r + 1)) (R.b α),
      |A (R.clamp α (MeasurableEquiv.blockEquiv eP eS z))| ≤ P := fun z _ ↦
    (Real.norm_eq_abs _).symm.le.trans ((ContinuousMap.norm_coe_le_norm A _).trans hA)
  have hprim : ∀ i : Fin (r + 1), (-1 : ℝ) < (R.h α (eP i) : ℝ) := fun i ↦
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)
  have hsecond : ∀ i : Fin (d - (r + 1)), (-1 : ℝ) < (R.h α (eS i) : ℝ) := fun i ↦
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)
  have habs := NormalCrossing.abs_blockIntegral_le_const_amplitude (fun i ↦ R.k α (eP i))
    (fun i ↦ R.k α (eS i))
    hprim hsecond
    hb hβ.le hp (Nat.cast_nonneg n) hP hξm hξ hAb
  have hZn := (hZ _ (fun _ ↦ P) M 0 P hξm measurable_const le_rfl hξ
    (fun _ _ ↦ hP) (fun _ _ ↦ le_rfl) n hn2).2
  have hNn := hN n hnN
  simp only [Function.comp, ite_eq_left hn2] at hNn
  rw [R.chartRadialInsertion_eq_blockIntegral eP eS, abs_mul, abs_of_nonneg ha0]
  calc
    _ ≤ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        (a₂ * Real.log n ^ r / n ^ (R.chartRlct α + p) *
          Real.exp (β * M ^ 2 / 2) * P) :=
      mul_le_mul_of_nonneg_left (habs.trans hZn) ha0
    _ = (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        (a₂ * Real.exp (β * M ^ 2 / 2) * P * Real.log n ^ r / n ^ (R.chartRlct α + p)) := by ring
    _ ≤ ε := hNn

end SingularLearningTheory.ResolutionAtlas
