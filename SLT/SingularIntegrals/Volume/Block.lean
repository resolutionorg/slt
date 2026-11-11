/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.FrozenKernel

/-!
# Exact weighted sublevel asymptotics on normal-crossing blocks

The monomial density formula transports measurable radial test functions.
For the sublevel indicator, the existing frozen-kernel and shifted-exponent error
estimates give an exact limit with coefficient `gammaConst / lam`.

The test-kernel substitution and Fubini algebra generalize `FrozenKernel.frozen_inner`
and `frozen_identity`. The original exponential specializations remain unchanged.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.SublevelVolume

open SingularLearningTheory.NormalCrossing

/-- The indicator of $(-\infty, 1]$, so that $\mathrm{cutoff}(nK)$ is the indicator of the
sublevel set $\{K \le 1/n\}$ for $n > 0$. In place of the factor $e^{-nK}$ of a partition
function, it gives the masses of sublevel sets, such as
`SingularLearningTheory.SublevelVolume.blockMass`. -/
@[expose] noncomputable def cutoff : ℝ → ℝ := (Iic (1 : ℝ)).indicator (fun _ ↦ 1)

theorem measurable_cutoff : Measurable cutoff :=
  measurable_const.indicator measurableSet_Iic

theorem cutoff_nonneg (t : ℝ) : 0 ≤ cutoff t := by
  unfold cutoff
  exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) t

theorem cutoff_le_one (t : ℝ) : cutoff t ≤ 1 := by
  unfold cutoff
  by_cases ht : t ≤ 1 <;> simp [Set.indicator, ht]

theorem cutoff_le_exp (t : ℝ) : cutoff t ≤ Real.exp 1 * Real.exp (-t) := by
  unfold cutoff
  by_cases ht : t ≤ 1
  · rw [Set.indicator_of_mem (show t ∈ Iic (1 : ℝ) from ht), ← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith)
  · rw [Set.indicator_of_notMem (show t ∉ Iic (1 : ℝ) from ht)]
    positivity

private theorem integral_cutoff_rpow {lam : ℝ} (hlam : 0 < lam) :
    ∫ t in Ioi (0 : ℝ), t ^ (lam - 1) * cutoff t = 1 / lam := by
  have heq : (fun t : ℝ ↦ t ^ (lam - 1) * cutoff t) =
      (Iic (1 : ℝ)).indicator (fun t ↦ t ^ (lam - 1)) := by
    funext t
    by_cases ht : t ≤ 1 <;> simp [cutoff, Set.indicator, ht]
  rw [heq, setIntegral_indicator measurableSet_Iic]
  have hset : Ioi (0 : ℝ) ∩ Iic 1 = Ioc 0 1 := by ext t; simp
  rw [hset, integral_Ioc_eq_integral_Ioo]
  simpa using integral_rpow_mul_log_pow
    (a := 1) (s := lam) one_pos hlam 0

private theorem integrableOn_cutoff_rpow {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ ↦ t ^ (lam - 1) * cutoff t) (Ioi 0) := by
  have hG : IntegrableOn (fun t : ℝ ↦ t ^ (lam - 1) * Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_half (a := lam - 1) (by linarith)
      (by norm_num : (0 : ℝ) < 2)
  refine (hG.const_mul (Real.exp 1)).mono'
    ((by fun_prop : Measurable fun t : ℝ ↦ t ^ (lam - 1)).mul
        measurable_cutoff).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (cutoff_nonneg t))]
  calc t ^ (lam - 1) * cutoff t
      ≤ t ^ (lam - 1) * (Real.exp 1 * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left (cutoff_le_exp t) (Real.rpow_nonneg ht0.le _)
    _ = _ := by ring

section Block

variable {r s : ℕ}
  {k : Fin (r + 1) → ℕ} {h : Fin (r + 1) → ℝ}
  {k' : Fin s → ℕ} {h' : Fin s → ℝ} {lam b : ℝ}

/-- The mass $\int \mathrm{cutoff}(n\,u^{2k}v^{2k'})\,u^h v^{h'}\varphi(u, v)\,du\,dv$ of the
sublevel set $\{u^{2k}v^{2k'} \le 1/n\}$ of the normal crossing potential
`SingularLearningTheory.NormalCrossing.potential` in the block $[0, b]^{r+1} \times [0, b]^s$,
against the
weight `SingularLearningTheory.NormalCrossing.monomialWeight` times a test function $\varphi$.
Under the
hypotheses of `SingularLearningTheory.SublevelVolume.tendsto_blockMass`, scaled by
$n^\lambda/(\log n)^r$ it tends to $\gamma_b/\lambda \int_{[0, b]^s} v^\mu\varphi(0, v)\,dv$. -/
@[expose] noncomputable def blockMass (k : Fin (r + 1) → ℕ) (h : Fin (r + 1) → ℝ)
    (k' : Fin s → ℕ) (h' : Fin s → ℝ) (b n : ℝ)
    (phi : (Fin (r + 1) → ℝ) × (Fin s → ℝ) → ℝ) : ℝ :=
  ∫ z, cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi z
    ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b)))

theorem blockMass_eq_setIntegral (n : ℝ)
    (phi : (Fin (r + 1) → ℝ) × (Fin s → ℝ) → ℝ) :
    blockMass k h k' h' b n phi =
      ∫ z in cube (r + 1) b ×ˢ cube s b,
        cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi z := by
  rw [blockMass, restrict_ocube_eq, restrict_ocube_eq, Measure.prod_restrict]
  rfl

theorem blockMass_eq_sublevel (n : ℝ) (hn : 0 < n)
    (phi : (Fin (r + 1) → ℝ) × (Fin s → ℝ) → ℝ) :
    blockMass k h k' h' b n phi =
      ∫ z in cube (r + 1) b ×ˢ cube s b,
        {z | potential k k' z ≤ n⁻¹}.indicator
          (fun z ↦ NormalCrossing.monomialWeight h h' z * phi z) z := by
  rw [blockMass_eq_setIntegral]
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  have heq : n * potential k k' z ≤ 1 ↔ potential k k' z ≤ n⁻¹ := by
    rw [← one_div, le_div_iff₀ hn]
    rw [mul_comm n]
  by_cases hz : potential k k' z ≤ n⁻¹
  · simp [cutoff, Set.indicator, hz, heq.mpr hz]
  · have hnK : ¬ n * potential k k' z ≤ 1 := fun h ↦ hz (heq.mp h)
    simp [cutoff, Set.indicator, hz, hnK]

private theorem integrable_blockMass_integrand
    (hh : ∀ j, -1 < h j) (hh' : ∀ j, -1 < h' j) (hb : 0 < b)
    {phi : (Fin (r + 1) → ℝ) × (Fin s → ℝ) → ℝ} {P : ℝ}
    (hphim : Measurable phi)
    (hphi : ∀ z ∈ cube (r + 1) b ×ˢ cube s b, |phi z| ≤ P) (n : ℝ) :
    Integrable
        (fun z ↦ cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi z)
      ((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b))) := by
  have hw : Integrable (NormalCrossing.monomialWeight h h')
      ((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b))) := by
    rw [restrict_ocube_eq, restrict_ocube_eq]
    exact (integrableOn_cube_rpow hh hb).mul_prod (integrableOn_cube_rpow hh' hb)
  have hm : Measurable fun z : (Fin (r + 1) → ℝ) × (Fin s → ℝ) ↦
      cutoff (n * potential k k' z) * phi z :=
    (measurable_cutoff.comp ((measurable_potential k k').const_mul n)).mul hphim
  refine (hw.bdd_mul (c := P) hm.aestronglyMeasurable ?_).congr
    (Eventually.of_forall fun z ↦ by ring)
  filter_upwards [ae_prod_ocube (m := r + 1) (m' := s) b] with z hz
  have hzS : z ∈ cube (r + 1) b ×ˢ cube s b :=
    ⟨mem_cube.2 fun j ↦ Ioo_subset_Icc_self (hz.1 j), mem_cube.2 fun j ↦ Ioo_subset_Icc_self
        (hz.2 j)⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutoff_nonneg _)]
  exact (mul_le_mul_of_nonneg_right (cutoff_le_one _) (abs_nonneg _)).trans
    (by simpa using hphi z hzS)

/-- The exact critical-block density from `integral_cube_monomial`.
Its name lets every bounded or integrable test kernel reuse the same transport. -/
private noncomputable def radialDensity (k : Fin (r + 1) → ℕ) (h : Fin (r + 1) → ℝ)
    (lam b a : ℝ) : ℝ → ℝ :=
  (Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator
    (fun t ↦ NormalCrossing.gammaConst k h lam b * t ^ (lam - 1) / a ^ lam *
      Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ r)

private theorem integrable_radialDensity (hlam0 : 0 < lam) (hb : 0 < b)
    {a : ℝ} (ha : 0 < a) : Integrable (radialDensity k h lam b a) := by
  rw [radialDensity, integrable_indicator_iff measurableSet_Ioo]
  have haux := (integrableOn_rpow_mul_log_pow_Ioo hlam0
    (by positivity : 0 < a * b ^ (2 * ∑ j, k j)) r).const_mul
      (NormalCrossing.gammaConst k h lam b / a ^ lam)
  exact IntegrableOn.congr_fun haux (fun t _ ↦ by ring) measurableSet_Ioo

private theorem integrable_cutoff_radialDensity (hlam0 : 0 < lam) (hb : 0 < b)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun t ↦ cutoff t * radialDensity k h lam b a t) := by
  refine ((integrable_radialDensity (k := k) (h := h) hlam0 hb ha).indicator
    (s := Iic (1 : ℝ)) measurableSet_Iic).congr
    (Eventually.of_forall fun t ↦ ?_)
  by_cases ht : t ≤ 1 <;> simp [cutoff, Set.indicator, ht]

/-- Generic inner transport. No regularity of the test kernel beyond measurability
and integrability against the explicit critical-block density is used. -/
private theorem frozen_test_inner
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hb : 0 < b) {phi0 : (Fin s → ℝ) → ℝ}
    {f : ℝ → ℝ} (hfm : Measurable f)
    {n : ℝ} (hn : 1 < n) {v : Fin s → ℝ} (hv : ∀ j, v j ∈ Ioo 0 b)
    (hint : Integrable (fun t ↦ f t * radialDensity k h lam b
      (n * ∏ j, v j ^ (2 * k' j)) t)) :
    n ^ lam / Real.log n ^ r *
      (∫ u in ocube (r + 1) b,
        f (n * potential k k' (u, v)) * NormalCrossing.monomialWeight h h' (u, v) * phi0 v)
      = NormalCrossing.gammaConst k h lam b * (NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
          ∫ t in Ioi 0, t ^ (lam - 1) * f t * NormalCrossing.logRatio k k' b n v t) := by
  have hv0 : ∀ j, 0 < v j := fun j ↦ (hv j).1
  have hn0 : 0 < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos hn
  have hV : 0 < ∏ j, v j ^ (2 * k' j) := Finset.prod_pos fun j _ ↦ pow_pos (hv0 j) _
  set a : ℝ := n * ∏ j, v j ^ (2 * k' j) with ha_def
  have ha : 0 < a := by positivity
  have hc : a * b ^ (2 * ∑ j, k j) = n * NormalCrossing.secondaryScale k k' b v := by
    rw [ha_def, NormalCrossing.secondaryScale]; ring
  have hre : (∫ u in ocube (r + 1) b,
        f (n * potential k k' (u, v)) * NormalCrossing.monomialWeight h h' (u, v) * phi0 v)
      = (∫ u in cube (r + 1) b,
          f (a * ∏ j, u j ^ (2 * k j)) * ∏ j, u j ^ h j) *
          ((∏ j, v j ^ h' j) * phi0 v) := by
    rw [← integral_mul_const, ← restrict_ocube_eq]
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo) fun u _ ↦ ?_
    have harg : n * potential k k' (u, v) = a * ∏ j, u j ^ (2 * k j) := by
      simp only [potential, ha_def]; ring
    rw [harg, NormalCrossing.monomialWeight]
    ring
  set nu : ℝ → ℝ := (Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator
    (fun t ↦ NormalCrossing.gammaConst k h lam b * t ^ (lam - 1) / a ^ lam *
      Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ r) with hnu_def
  have step := integral_cube_monomial (r := r) (a := a) hk hlam ha hb
    (f := f) hfm.aestronglyMeasurable hint
  have hpt : ∀ t, f t * nu t =
      NormalCrossing.gammaConst k h lam b / a ^ lam * Real.log n ^ r *
        (t ^ (lam - 1) * f t * NormalCrossing.logRatio k k' b n v t) := by
    intro t
    rw [hnu_def, NormalCrossing.logRatio, hc]
    by_cases ht : t ∈ Ioo 0 (n * NormalCrossing.secondaryScale k k' b v)
    · rw [indicator_of_mem ht, indicator_of_mem ht, div_pow]
      have ha' : 0 < a ^ lam := Real.rpow_pos_of_pos ha _
      field_simp
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp
  have hpull : (∫ t in Ioi 0, f t * nu t) =
      NormalCrossing.gammaConst k h lam b / a ^ lam * Real.log n ^ r *
        ∫ t in Ioi 0, t ^ (lam - 1) * f t * NormalCrossing.logRatio k k' b n v t := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have hVpow : (∏ j, v j ^ (2 * k' j)) ^ lam = ∏ j, v j ^ (2 * k' j * lam) := by
    rw [← Real.finsetProd_rpow _ _ fun j _ ↦ pow_nonneg (hv0 j).le _]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hv0 j).le]
    push_cast
    ring_nf
  have hvw : (∏ j, v j ^ h' j) / (∏ j, v j ^ (2 * k' j)) ^ lam =
      NormalCrossing.secondaryWeight k' h' lam v := by
    rw [hVpow, ← Finset.prod_div_distrib, NormalCrossing.secondaryWeight]
    exact Finset.prod_congr rfl fun j _ ↦ (Real.rpow_sub (hv0 j) _ _).symm
  have hapow : a ^ lam = n ^ lam * (∏ j, v j ^ (2 * k' j)) ^ lam := by
    rw [ha_def]
    exact Real.mul_rpow hn0.le hV.le
  have hnl : 0 < n ^ lam := Real.rpow_pos_of_pos hn0 _
  have hVl : 0 < (∏ j, v j ^ (2 * k' j)) ^ lam := Real.rpow_pos_of_pos hV _
  rw [hre, step, hpull, ← hvw, hapow]
  generalize (∫ t in Ioi 0, t ^ (lam - 1) * f t * NormalCrossing.logRatio k k' b n v t) = J
  field_simp

/-- Generic outer transport. The two integrability premises are exactly the
premises used by monomial substitution and Fubini, respectively. -/
private theorem frozen_test_identity
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam) (hb : 0 < b)
    {phi0 : (Fin s → ℝ) → ℝ} {F : (Fin s → ℝ) → ℝ → ℝ}
    (hFm : ∀ v, Measurable (F v)) {n : ℝ} (hn : 1 < n)
    (hFdensity : ∀ v, (∀ j, v j ∈ Ioo 0 b) →
      Integrable (fun t ↦ F v t * radialDensity k h lam b
        (n * ∏ j, v j ^ (2 * k' j)) t))
    (hint : Integrable (fun z ↦ F z.2 (n * potential k k' z) *
        NormalCrossing.monomialWeight h h' z * phi0 z.2)
      ((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b)))) :
    n ^ lam / Real.log n ^ r *
      (∫ z, F z.2 (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi0 z.2
        ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b))))
      = NormalCrossing.gammaConst k h lam b *
        ∫ v in cube s b, NormalCrossing.secondaryWeight k' h' lam v * phi0 v
          *
          ∫ t in Ioi 0, t ^ (lam - 1) * F v t * NormalCrossing.logRatio k k' b n v t := by
  rw [integral_prod_symm _ hint, ← integral_const_mul (n ^ lam / Real.log n ^ r),
    ← restrict_ocube_eq (m := s), ← integral_const_mul (NormalCrossing.gammaConst k h lam b)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)] with v hv
  have hv' : ∀ j, v j ∈ Ioo 0 b := fun j ↦ hv j (mem_univ j)
  exact frozen_test_inner hk hlam hb (hFm v) hn hv' (hFdensity v hv')

/-- Indicator specialization of the generic inner transport. -/
private theorem frozen_sublevel_inner
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hb : 0 < b) {phi0 : (Fin s → ℝ) → ℝ}
    {n : ℝ} (hn : 1 < n) {v : Fin s → ℝ} (hv : ∀ j, v j ∈ Ioo 0 b) :
    n ^ lam / Real.log n ^ r *
      (∫ u in ocube (r + 1) b,
        cutoff (n * potential k k' (u, v)) * NormalCrossing.monomialWeight h h' (u, v) * phi0 v)
      = NormalCrossing.gammaConst k h lam b * (NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
          ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t) := by
  refine frozen_test_inner hk hlam hb measurable_cutoff hn hv ?_
  exact integrable_cutoff_radialDensity hlam0 hb
    (mul_pos (by linarith) (Finset.prod_pos fun j _ ↦ pow_pos (hv j).1 _))

/-- Indicator specialization of the generic outer transport. -/
private theorem frozen_sublevel_identity
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b)
    {phi0 : (Fin s → ℝ) → ℝ} {P : ℝ} (hphim : Measurable phi0)
    (hphi : ∀ v ∈ cube s b, |phi0 v| ≤ P) {n : ℝ} (hn : 1 < n) :
    n ^ lam / Real.log n ^ r * blockMass k h k' h' b n (fun z ↦ phi0 z.2)
      = NormalCrossing.gammaConst k h lam b *
        ∫ v in cube s b, NormalCrossing.secondaryWeight k' h' lam v * phi0 v
          *
          ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t := by
  obtain ⟨hh, hh', -, -⟩ := NormalCrossing.exponents_aux hk hlam hlam0 hsec (p := 0) le_rfl
  apply frozen_test_identity hk hlam hb (fun _ ↦ measurable_cutoff) hn
  · intro v hv
    exact integrable_cutoff_radialDensity hlam0 hb
      (mul_pos (by linarith) (Finset.prod_pos fun j _ ↦ pow_pos (hv j).1 _))
  · exact integrable_blockMass_integrand (k := k) (k' := k') hh hh' hb
      (hphim.comp measurable_snd) (fun z hz ↦ hphi z.2 hz.2) n

private theorem integrableOn_cutoff_rpow_logRatio (hlam0 : 0 < lam) (hb : 0 < b)
    {n : ℝ} (hn : 0 < n) {v : Fin s → ℝ} (hv : ∀ j, 0 < v j) :
    IntegrableOn (fun t ↦ t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t)
        (Ioi 0) := by
  have hR := NormalCrossing.integrableOn_rpow_mul_logRatio (k := k) (k' := k') hlam0 hn
    (NormalCrossing.secondaryScale_pos hb hv)
  refine (hR.bdd_mul (c := 1) measurable_cutoff.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)).congr (Eventually.of_forall fun t ↦ by ring)
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg t)]
  exact cutoff_le_one t

/-- The limit of the scaled block mass `SingularLearningTheory.SublevelVolume.blockMass` of a test
function $\varphi_0(v)$ of the secondary coordinates alone
(`SingularLearningTheory.SublevelVolume.tendsto_frozen_blockMass`): the constant $\gamma_b$
(`SingularLearningTheory.NormalCrossing.gammaConst`) times the integral of $v^\mu\varphi_0(v)$ over
$[0, b]^s$,
with $v^\mu$ the weight `SingularLearningTheory.NormalCrossing.secondaryWeight`, times
$\int_0^\infty t^{\lambda - 1}\mathrm{cutoff}(t)\,dt$, which is $1/\lambda$ for $\lambda > 0$
(`SingularLearningTheory.SublevelVolume.cutoffLimit_eq`). -/
private noncomputable def cutoffLimit (k : Fin (r + 1) → ℕ) (h : Fin (r + 1) → ℝ)
    (k' : Fin s → ℕ) (h' : Fin s → ℝ) (lam b : ℝ) (phi0 : (Fin s → ℝ) → ℝ) : ℝ :=
  NormalCrossing.gammaConst k h lam b * ∫ v in cube s b, NormalCrossing.secondaryWeight k' h' lam v
      * phi0 v *
    ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t

private theorem cutoffLimit_eq (hlam0 : 0 < lam) (phi0 : (Fin s → ℝ) → ℝ) :
    cutoffLimit k h k' h' lam b phi0 = NormalCrossing.gammaConst k h lam b / lam *
      ∫ v in cube s b, NormalCrossing.secondaryWeight k' h' lam v * phi0 v := by
  rw [cutoffLimit, integral_cutoff_rpow hlam0, integral_mul_const]
  ring

private theorem frozen_sublevel_pointwise_bound (hlam0 : 0 < lam) (hb : 0 < b)
    {phi0 : (Fin s → ℝ) → ℝ} {P : ℝ}
    (hphi : ∀ v ∈ cube s b, |phi0 v| ≤ P) {n : ℝ} (hn : 1 < n)
    {v : Fin s → ℝ} (hv : ∀ j, v j ∈ Ioo 0 b) :
    |(NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
        ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t)
      - NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
        ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t|
      ≤ P * Real.exp 1 * (NormalCrossing.secondaryWeight k' h' lam v *
          ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(2 * t / 2)) *
            |NormalCrossing.logRatio k k' b n v t - 1|) := by
  have hv0 : ∀ j, 0 < v j := fun j ↦ (hv j).1
  have hvc : v ∈ cube s b := mem_cube.2 fun j ↦ Ioo_subset_Icc_self (hv j)
  have hw := NormalCrossing.secondaryWeight_nonneg (k' := k') (h' := h') (lam := lam) fun j
      ↦ (hv0 j).le
  have hP := hphi v hvc
  have hP0 : 0 ≤ P := (abs_nonneg _).trans hP
  have h1 := integrableOn_cutoff_rpow_logRatio (k := k) (k' := k') hlam0 hb
    (show 0 < n by linarith) hv0
  have h2 := integrableOn_cutoff_rpow hlam0
  have hE := NormalCrossing.integrableOn_frozenError_inner (k := k) (k' := k') hlam0 hb
    (by norm_num : (0 : ℝ) < 2) hn hv0
  have hJ : |∫ t in Ioi 0,
        (t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t - t ^ (lam - 1) * cutoff
            t)|
      ≤ Real.exp 1 * ∫ t in Ioi 0,
          t ^ (lam - 1) * Real.exp (-(2 * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1| := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun t ↦ norm_nonneg _) (hE.const_mul _) ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, show t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t
          - t ^ (lam - 1) * cutoff t
        = t ^ (lam - 1) * cutoff t * (NormalCrossing.logRatio k k' b n v t - 1) by ring,
      abs_mul, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (cutoff_nonneg t))]
    calc t ^ (lam - 1) * cutoff t * |NormalCrossing.logRatio k k' b n v t - 1|
        ≤ t ^ (lam - 1) * (Real.exp 1 * Real.exp (-t)) * |NormalCrossing.logRatio k k' b n v t -
            1| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (cutoff_le_exp t)
            (Real.rpow_nonneg ht0.le _)) (abs_nonneg _)
      _ = _ := by rw [show -(2 * t / 2) = -t by ring]; ring
  rw [← mul_sub, ← integral_sub h1 h2, abs_mul, abs_mul, abs_of_nonneg hw]
  calc NormalCrossing.secondaryWeight k' h' lam v * |phi0 v| * |∫ t in Ioi 0,
        (t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t - t ^ (lam - 1) * cutoff
            t)|
      ≤ NormalCrossing.secondaryWeight k' h' lam v * P * (Real.exp 1 * ∫ t in Ioi 0,
          t ^ (lam - 1) * Real.exp (-(2 * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hP hw) hJ (abs_nonneg _) (mul_nonneg hw hP0)
    _ = _ := by ring

private theorem abs_frozen_blockMass_sub_limit_le
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b)
    {phi0 : (Fin s → ℝ) → ℝ} {P : ℝ} (hphim : Measurable phi0)
    (hphi : ∀ v ∈ cube s b, |phi0 v| ≤ P) {n : ℝ} (hn : 2 ≤ n) :
    |n ^ lam / Real.log n ^ r * blockMass k h k' h' b n (fun z ↦ phi0 z.2)
      - cutoffLimit k h k' h' lam b phi0|
      ≤ NormalCrossing.gammaConst k h lam b * P * Real.exp 1 *
          NormalCrossing.frozenError k k' h' lam b 2 n := by
  have hn1 : 1 < n := by linarith
  have hgamma := gammaConst_pos h lam hk hb
  have hmu : ∀ j, -1 < h' j - 2 * k' j * lam := fun j ↦ by linarith [hsec j]
  rw [frozen_sublevel_identity hk hlam hlam0 hsec hb hphim hphi hn1,
    cutoffLimit, ← mul_sub, abs_mul, abs_of_pos hgamma, NormalCrossing.frozenError]
  have hR := NormalCrossing.measurable_logRatio_uncurry (k := k) (k' := k') (b := b) (r := r) n
  have hGinf : Measurable fun p : (Fin s → ℝ) × ℝ ↦ p.2 ^ (lam - 1) * cutoff p.2 :=
    (by fun_prop : Measurable fun p : (Fin s → ℝ) × ℝ ↦ p.2 ^ (lam - 1)).mul
      (measurable_cutoff.comp measurable_snd)
  have hGn : Measurable fun p : (Fin s → ℝ) × ℝ ↦
      p.2 ^ (lam - 1) * cutoff p.2 * NormalCrossing.logRatio k k' b n p.1 p.2 := hGinf.mul hR
  have hJn := stronglyMeasurable_integral_Ioi hGn
  have hJinf := stronglyMeasurable_integral_Ioi hGinf
  have hwm := NormalCrossing.measurable_secondaryWeight (k' := k') (h' := h') (lam := lam)
  have hae : ∀ᵐ v ∂(volume.restrict (cube s b)), ∀ j, v j ∈ Ioo 0 b := by
    rw [← restrict_ocube_eq]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)] with v hv
    exact fun j ↦ hv j (mem_univ j)
  have hintE := NormalCrossing.integrable_frozenError_integrand (k := k) (h' := h') hlam0 hsec hb
    (by norm_num : (0 : ℝ) < 2) hn1
  have hwint : IntegrableOn (NormalCrossing.secondaryWeight k' h' lam) (cube s b) :=
      integrableOn_cube_rpow hmu hb
  have hwphi : Integrable (fun v ↦ NormalCrossing.secondaryWeight k' h' lam v * phi0 v)
      (volume.restrict (cube s b)) := by
    refine (hwint.bdd_mul (c := P) hphim.aestronglyMeasurable ?_).congr
      (Eventually.of_forall fun v ↦ mul_comm _ _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    simpa only [Real.norm_eq_abs] using hphi v hv
  have hIinf : Integrable (fun v ↦ NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
      ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t) (volume.restrict (cube s b)) := hwphi.mul_const _
  have hIdiff : Integrable (fun v ↦ NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
      (∫ t in Ioi 0, t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t)
        - NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
          ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t) (volume.restrict (cube s b)) := by
    refine (hintE.const_mul (P * Real.exp 1)).mono'
      (((hwm.stronglyMeasurable.mul hphim.stronglyMeasurable).mul hJn).sub
        ((hwm.stronglyMeasurable.mul hphim.stronglyMeasurable).mul hJinf)).aestronglyMeasurable ?_
    filter_upwards [hae] with v hv
    rw [Real.norm_eq_abs]
    exact frozen_sublevel_pointwise_bound hlam0 hb hphi hn1 hv
  have hIn : Integrable (fun v ↦ NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
      ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t)
      (volume.restrict (cube s b)) := by
    refine (hIdiff.add hIinf).congr (Eventually.of_forall fun v ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have key : |(∫ v in cube s b, NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
        ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t * NormalCrossing.logRatio k k' b n v t)
      - ∫ v in cube s b, NormalCrossing.secondaryWeight k' h' lam v * phi0 v *
        ∫ t in Ioi 0, t ^ (lam - 1) * cutoff t|
      ≤ P * Real.exp 1 * ∫ v in cube s b, NormalCrossing.secondaryWeight k' h' lam v *
          ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(2 * t / 2)) *
            |NormalCrossing.logRatio k k' b n v t - 1| := by
    rw [← integral_sub hIn hIinf, ← Real.norm_eq_abs, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun v ↦ norm_nonneg _) (hintE.const_mul _) ?_)
    filter_upwards [hae] with v hv
    rw [Real.norm_eq_abs]
    exact frozen_sublevel_pointwise_bound hlam0 hb hphi hn1 hv
  exact (mul_le_mul_of_nonneg_left key hgamma.le).trans_eq (by ring)

private theorem tendsto_frozen_blockMass
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b)
    {phi0 : (Fin s → ℝ) → ℝ} {P : ℝ} (hphim : Measurable phi0)
    (hphi : ∀ v ∈ cube s b, |phi0 v| ≤ P) :
    Tendsto (fun n : ℝ ↦ n ^ lam / Real.log n ^ r *
      blockMass k h k' h' b n (fun z ↦ phi0 z.2)) atTop
      (𝓝 (cutoffLimit k h k' h' lam b phi0)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  have hE := NormalCrossing.frozenError_tendsto (k := k) (k' := k') (h' := h')
    hk hlam0 hsec hb (by norm_num : (0 : ℝ) < 2)
  have hupper := hE.const_mul (NormalCrossing.gammaConst k h lam b * P * Real.exp 1)
  simp only [mul_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun n ↦ abs_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with n hn
  exact abs_frozen_blockMass_sub_limit_le hk hlam hlam0 hsec hb hphim hphi hn

private theorem unfreeze_sublevel_pointwise (_hb : 0 < b)
    {phi : (Fin (r + 1) → ℝ) × (Fin s → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hphiL : ∀ z ∈ cube (r + 1) b ×ˢ cube s b,
      |phi z - phi (0, z.2)| ≤ L * ∑ j, z.1 j)
    (n : ℝ) {z : (Fin (r + 1) → ℝ) × (Fin s → ℝ)}
    (hz : (∀ j, z.1 j ∈ Ioo 0 b) ∧ ∀ j, z.2 j ∈ Ioo 0 b) :
    |cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi z
      - cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi (0, z.2)|
      ≤ Real.exp 1 * L * ∑ j,
        (potential k k' z ^ (0 : ℝ) * Real.exp (-(n * 1 * potential k k' z)) *
          NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z) := by
  have hzS : z ∈ cube (r + 1) b ×ˢ cube s b :=
    ⟨mem_cube.2 fun j ↦ Ioo_subset_Icc_self (hz.1 j), mem_cube.2 fun j ↦ Ioo_subset_Icc_self
        (hz.2 j)⟩
  have hw := monomialWeight_nonneg h h' (fun j ↦ (hz.1 j).1.le) (fun j ↦ (hz.2 j).1.le)
  have hsum : 0 ≤ ∑ j, z.1 j := Finset.sum_nonneg fun j _ ↦ (hz.1 j).1.le
  rw [← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg (cutoff_nonneg _) hw)]
  calc cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * |phi z - phi (0, z.2)|
      ≤ cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * (L * ∑ j, z.1 j) :=
        mul_le_mul_of_nonneg_left (hphiL z hzS) (mul_nonneg (cutoff_nonneg _) hw)
    _ ≤ (Real.exp 1 * Real.exp (-(n * potential k k' z))) *
          NormalCrossing.monomialWeight h h' z * (L * ∑ j, z.1 j) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (cutoff_le_exp _) hw) (mul_nonneg hL hsum)
    _ = _ := by
        have hupdate : ∀ j, NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z =
            z.1 j * NormalCrossing.monomialWeight h h' z :=
          fun j ↦ monomialWeight_update h h' j (hz.1 j).1.ne'
        simp_rw [hupdate]
        simp only [Real.rpow_zero, one_mul, mul_one]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ ↦ by ring)

private theorem abs_blockMass_sub_frozen_le
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b)
    {phi : (Fin (r + 1) → ℝ) × (Fin s → ℝ) → ℝ} {P L : ℝ}
    (hphim : Measurable phi)
    (hphi : ∀ z ∈ cube (r + 1) b ×ˢ cube s b, |phi z| ≤ P)
    (hL : 0 ≤ L)
    (hphiL : ∀ z ∈ cube (r + 1) b ×ˢ cube s b,
      |phi z - phi (0, z.2)| ≤ L * ∑ j, z.1 j) {n : ℝ} (hn : 0 ≤ n) :
    |blockMass k h k' h' b n phi - blockMass k h k' h' b n (fun z ↦ phi (0, z.2))|
      ≤ Real.exp 1 * L * ∑ j, NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h'
          b 1 0 n :=
          by
  obtain ⟨hh, hh', -, -⟩ := NormalCrossing.exponents_aux hk hlam hlam0 hsec (p := 0) le_rfl
  have h0S : ∀ z ∈ cube (r + 1) b ×ˢ cube s b,
      ((0 : Fin (r + 1) → ℝ), z.2) ∈ cube (r + 1) b ×ˢ cube s b :=
    fun z hz ↦ ⟨⟨fun j ↦ le_rfl, fun j ↦ hb.le⟩, hz.2⟩
  have hphi0m : Measurable fun z : (Fin (r + 1) → ℝ) × (Fin s → ℝ) ↦ phi (0, z.2) :=
    hphim.comp (measurable_const.prodMk measurable_snd)
  have hhj : ∀ j i, -1 < Function.update h j (h j + 1) i := by
    intro j i
    rcases eq_or_ne i j with rfl | hij
    · rw [Function.update_self]; linarith [hh i]
    · rw [Function.update_of_ne hij]; exact hh i
  have hF := integrable_blockMass_integrand (k := k) (k' := k') hh hh' hb hphim hphi n
  have hG := integrable_blockMass_integrand (k := k) (k' := k') hh hh' hb hphi0m
    (fun z hz ↦ hphi _ (h0S z hz)) n
  have hT : ∀ j, Integrable (fun z ↦ potential k k' z ^ (0 : ℝ) *
      Real.exp (-(n * 1 * potential k k' z)) *
        NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z)
      ((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b))) :=
    fun j ↦ integrable_blockIntegral₀_integrand k k' (hhj j) hh' hb zero_le_one le_rfl hn
  rw [blockMass, blockMass, ← integral_sub hF hG]
  calc |∫ z, _ ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b)))|
      ≤ ∫ z, |cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi z
          - cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi (0, z.2)|
        ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b))) := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := (volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b)))
          (fun z ↦ cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi z
            - cutoff (n * potential k k' z) * NormalCrossing.monomialWeight h h' z * phi (0, z.2))
    _ ≤ ∫ z, Real.exp 1 * L * ∑ j,
          (potential k k' z ^ (0 : ℝ) * Real.exp (-(n * 1 * potential k k' z)) *
            NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z)
        ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube s b))) := by
        refine integral_mono_ae (hF.sub hG).abs
          ((integrable_finsetSum _ (fun j _ ↦ hT j)).const_mul _) ?_
        filter_upwards [ae_prod_ocube (m := r + 1) (m' := s) b] with z hz
        exact unfreeze_sublevel_pointwise hb hL hphiL n hz
    _ = _ := by
        rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦ hT j)]
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [blockIntegral₀_eq_integral_prod]

theorem tendsto_blockMass
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b)
    {phi : (Fin (r + 1) → ℝ) × (Fin s → ℝ) → ℝ} {P L : ℝ}
    (hphim : Measurable phi)
    (hphi : ∀ z ∈ cube (r + 1) b ×ˢ cube s b, |phi z| ≤ P)
    (hL : 0 ≤ L)
    (hphiL : ∀ z ∈ cube (r + 1) b ×ˢ cube s b,
      |phi z - phi (0, z.2)| ≤ L * ∑ j, z.1 j) :
    Tendsto (fun n : ℝ ↦ n ^ lam / Real.log n ^ r * blockMass k h k' h' b n phi)
      atTop (𝓝 (NormalCrossing.gammaConst k h lam b / lam *
        ∫ v in cube s b, NormalCrossing.secondaryWeight k' h' lam v * phi (0, v))) := by
  have hphi0m : Measurable fun v : Fin s → ℝ ↦ phi (0, v) :=
    hphim.comp (measurable_const.prodMk measurable_id)
  have hphi0 : ∀ v ∈ cube s b, |phi (0, v)| ≤ P := fun v hv ↦
    hphi (0, v) ⟨⟨fun j ↦ le_rfl, fun j ↦ hb.le⟩, hv⟩
  have hfrozen := tendsto_frozen_blockMass hk hlam hlam0 hsec hb hphi0m hphi0
  have hshift : ∀ j, Tendsto (fun n : ℝ ↦ n ^ lam / Real.log n ^ r *
      NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b 1 0 n) atTop (𝓝 0) :=
          by
    intro j
    have hj := NormalCrossing.shifted_negligible hk hlam hlam0 hsec hb
      (by norm_num : (0 : ℝ) < 2) j (q := 0) le_rfl
    simpa only [add_zero, show (2 : ℝ) / 2 = 1 by norm_num] using hj
  have hsum : Tendsto (fun n : ℝ ↦ Real.exp 1 * L * ∑ j,
      (n ^ lam / Real.log n ^ r *
        NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b 1 0 n))
      atTop (𝓝 0) := by
    have hs := tendsto_finsetSum (Finset.univ : Finset (Fin (r + 1))) fun j _ ↦ hshift j
    simpa using hs.const_mul (Real.exp 1 * L)
  have hdiff : Tendsto (fun n : ℝ ↦ n ^ lam / Real.log n ^ r *
      (blockMass k h k' h' b n phi - blockMass k h k' h' b n (fun z ↦ phi (0, z.2))))
      atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simp only [Real.dist_eq, sub_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with n hn
    have hn0 : 0 ≤ n := by linarith
    have ha : 0 ≤ n ^ lam / Real.log n ^ r := by
      exact div_nonneg (Real.rpow_nonneg hn0 _) (pow_nonneg (Real.log_nonneg (by linarith)) _)
    rw [abs_mul, abs_of_nonneg ha]
    calc n ^ lam / Real.log n ^ r *
          |blockMass k h k' h' b n phi - blockMass k h k' h' b n (fun z ↦ phi (0, z.2))|
        ≤ n ^ lam / Real.log n ^ r * (Real.exp 1 * L *
            ∑ j, NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b 1 0 n) :=
          mul_le_mul_of_nonneg_left
            (abs_blockMass_sub_frozen_le hk hlam hlam0 hsec hb hphim hphi hL hphiL hn0) ha
      _ = _ := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ ↦ by ring)
  have htotal := hdiff.add hfrozen
  rw [zero_add, cutoffLimit_eq hlam0] at htotal
  refine htotal.congr (fun n ↦ ?_)
  ring

end Block

end SingularLearningTheory.SublevelVolume

