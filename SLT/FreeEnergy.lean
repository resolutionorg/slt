/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.StandardForm
public import SLT.SingularIntegrals
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import SLT.EmpiricalProcess.ProductSpace
import SLT.FreeEnergy.Discharge
import SLT.FreeEnergy.Main
import SLT.FreeEnergy.NullSublevel
import SLT.Resolution
import SLT.MaximumLikelihood.MomentDowngrade
import SLT.Resolution.FromHironaka
import SLT.Resolution.OptimizerProcess
import SLT.Resolution.PieceAtlas
import SLT.SingularIntegrals.Resolution
public import SLT.FreeEnergy.Defs

/-!
# The free energy formula

The theorems of `SLTChallenge/FreeEnergy.lean`, proved from the library. The definitions are
in `SLT/FreeEnergy/Defs.lean`, and the standard form is in `SLT/StandardForm.lean`. The
`*_of_inputs` bridges take the conclusions of [Wat09, Theorems 6.1, 5.9 and 5.8] as hypotheses
and wrap the library's `EmpiricalProcessInput.tendstoInDistribution_normalizedEvidence`,
`NondegenerateResolutionAtlas.free_energy_formula`, `tendsto_integral_Rn` and
`eventually_integral_normalizedFreeEnergy_eq`; the challenge's theorems derive those inputs
(`FreeEnergy/SamplewiseResolution.lean`, `FreeEnergy/Discharge.lean`,
`EmpiricalProcess/FourthMoment.lean`) and, for the free energy formula, build the atlas from
Hironaka's theorem (`Resolution/FromHironaka.lean`).
-/

@[expose] public section

-- These statements mirror SLTChallenge word for word, so they keep hypotheses of the book
-- that the delegated proofs here don't need.
set_option linter.unusedVariables false

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open Real (exp log)
open scoped ENNReal Manifold

variable {d : ℕ} {X : Type*} [MeasurableSpace X]


/-! ## The limit functional `Y` -/

section LimitFunctional

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

open scoped Classical in
/-- The limit functional of [Wat09, Theorem 6.7] on the charts of a resolution atlas, the
atlas-indexed form of `Y`. -/
private noncomputable def AtlasY (β : ℝ) (R : ResolutionAtlas K φ W)
    (χ : C((α : R.ι) × cube d (R.b α), ℝ)) : ℝ :=
  ∑ α ∈ Finset.univ.filter R.IsEssential,
    let k := R.k α
    let h := R.h α
    let hk := R.active α
    let I := criticalCoords k h hk
    let F := Icc (0 : {j // j ∉ I} → ℝ) (fun _ ↦ R.b α)
    gammaConst k h hk *
      ∫ t in Ioi (0 : ℝ), ∫ v : F,
        let u := toCriticalFace k h hk (R.b_pos α).le v
        t ^ (R.rlct - 1) * (∏ j, v.val j ^ ((h j : ℝ) - 2 * k j * R.rlct)) *
          exp (-(β * t) + β * √t * χ ⟨α, u⟩) * R.weight α u
        ∂(volume.comap Subtype.val)

end LimitFunctional


section ZnBridges

variable {Ω : Type*} [MeasurableSpace Ω] {W : Set (Fin d → ℝ)}

/-! ### `Z_n = e^{−nβ L_n(w₀)} Z_n^0` -/

/-- The densities are positive at the sample points, almost surely. -/
theorem ae_pos_at_samples {q : Measure X} {p : (Fin d → ℝ) → X → ℝ}
    (hp_pos : ∀ᵐ x ∂q, ∀ w ∈ W, 0 < p w x) {Xs : ℕ → Ω → X} {P : Measure Ω}
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ i ∈ Finset.range n, ∀ w ∈ W, 0 < p w (Xs i ω) := by
  refine (Filter.eventually_all_finset _).mpr fun i _ ↦ ?_
  refine ae_of_ae_map (hX i).aemeasurable (p := fun x ↦ ∀ w ∈ W, 0 < p w x) ?_
  rw [hlaw i]
  exact hp_pos

omit [MeasurableSpace X] [MeasurableSpace Ω] in
/-- `K_n(w) = L_n(w) − L_n(w₀)` on `W`, where the densities are positive. -/
theorem empiricalExcessLoss_eq_sub {p : (Fin d → ℝ) → X → ℝ} {Xs : ℕ → Ω → X} {n : ℕ} {ω : Ω}
    (hpos : ∀ i ∈ Finset.range n, ∀ w ∈ W, 0 < p w (Xs i ω)) {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W)
    {w : Fin d → ℝ} (hw : w ∈ W) : empiricalExcessLoss p w₀ Xs n ω w = empiricalNegativeLogLikelihood p Xs n ω w - empiricalNegativeLogLikelihood p Xs n ω w₀ := by
  simp only [empiricalExcessLoss, empiricalNegativeLogLikelihood, logDensityRatio]
  rw [Finset.sum_congr rfl fun i hi ↦ Real.log_div (hpos i hi w₀ hw₀).ne' (hpos i hi w hw).ne',
    Finset.sum_sub_distrib]
  ring

omit [MeasurableSpace X] [MeasurableSpace Ω] in
theorem evidence_eq_exp_mul_normalizedEvidence (hW : MeasurableSet W) {p : (Fin d → ℝ) → X → ℝ}
    {Xs : ℕ → Ω → X}
    {n : ℕ} {ω : Ω} (hpos : ∀ i ∈ Finset.range n, ∀ w ∈ W, 0 < p w (Xs i ω))
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (φ : (Fin d → ℝ) → ℝ) (β : ℝ) :
    evidence p W φ β Xs n ω = exp (-(n * β * empiricalNegativeLogLikelihood p Xs n ω w₀)) *
        normalizedEvidence p w₀ W φ β Xs n ω := by
  unfold evidence normalizedEvidence
  rw [← integral_const_mul]
  refine setIntegral_congr_fun hW fun w hw ↦ ?_
  rw [empiricalExcessLoss_eq_sub hpos hw₀ hw, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

omit [MeasurableSpace X] [MeasurableSpace Ω] in
/-- `F_n = nβ L_n(w₀) − log Z_n^0` where `Z_n^0 > 0`. -/
theorem freeEnergy_eq_add_neg_log_normalizedEvidence (hW : MeasurableSet W)
    {p : (Fin d → ℝ) → X → ℝ} {Xs : ℕ → Ω → X}
    {n : ℕ} {ω : Ω} (hpos : ∀ i ∈ Finset.range n, ∀ w ∈ W, 0 < p w (Xs i ω))
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (φ : (Fin d → ℝ) → ℝ) (β : ℝ)
    (hZ : 0 < normalizedEvidence p w₀ W φ β Xs n ω) :
    freeEnergy p W φ β Xs n ω = n * β * empiricalNegativeLogLikelihood p Xs n ω w₀ + -log
        (normalizedEvidence p w₀ W φ β Xs n ω) := by
  rw [freeEnergy, evidence_eq_exp_mul_normalizedEvidence hW hpos hw₀ φ β, Real.log_mul
      (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  ring

end ZnBridges

section YBridges

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- The point of the cube of chart $\alpha$ whose primary coordinates are $0$ and whose secondary
coordinates are those of $v$, clamped to $[0, b_\alpha]$. It is
`SingularLearningTheory.ResolutionAtlas.primaryZero` with the secondary coordinates indexed by the
complement of `SingularLearningTheory.ResolutionAtlas.primary`. -/
private noncomputable def zeroPrimary (R : ResolutionAtlas K φ W) (α : R.ι)
    (v : {j // j ∉ R.primary α} → ℝ) : cube d (R.b α) :=
  R.primaryZero α fun j ↦ if h : j ∈ R.primary α then 0 else v ⟨j, h⟩

/-- The cube $[0, b_\alpha]$ in each secondary coordinate of chart $\alpha$, those outside
`SingularLearningTheory.ResolutionAtlas.primary`. The limit functional
`SingularLearningTheory.AtlasY` integrates over it
(`SingularLearningTheory.Y_eq_secondary_integral`). -/
private def secondaryCube (R : ResolutionAtlas K φ W) (α : R.ι) :
    Set ({j // j ∉ R.primary α} → ℝ) :=
  Set.pi univ fun _ ↦ Icc 0 (R.b α)

/-- The critical coordinates of a chart are the atlas's primary coordinates. -/
private theorem criticalCoords_eq_primary (α : R.ι) :
    criticalCoords (R.k α) (R.h α) (R.active α) = R.primary α :=
  rfl

private theorem gammaConst_eq_chartGamma (α : R.ι) :
    gammaConst (R.k α) (R.h α) (R.active α) = R.chartGamma α := by
  unfold gammaConst monomialMultiplicity
  rw [criticalCoords_eq_primary]
  rfl

open scoped Classical in
/-- `Y` as a sum of set integrals over the secondary cubes, the form the proof library uses. -/
private theorem Y_eq_secondary_integral (β : ℝ)
    (χ : C((α : R.ι) × cube d (R.b α), ℝ)) :
    AtlasY β R χ = ∑ α ∈ Finset.univ.filter R.IsEssential, R.chartGamma α *
      ∫ t in Ioi (0 : ℝ), ∫ v in secondaryCube R α,
        t ^ (R.rlct - 1) * (∏ j, v j ^ R.secondaryExponent α j) *
          exp (-(β * t) + β * √t * χ ⟨α, zeroPrimary R α v⟩) *
          R.weight α (zeroPrimary R α v) := by
  classical
  unfold AtlasY
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  dsimp only
  rw [gammaConst_eq_chartGamma]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  unfold toCriticalFace
  rw! (castMode := .all) [criticalCoords_eq_primary]
  have hsc : secondaryCube R α = Icc (0 : {j // j ∉ R.primary α} → ℝ) (fun _ ↦ R.b α) :=
    Set.pi_univ_Icc _ _
  rw [hsc]
  rw [← integral_subtype_comap measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with v
  have hp : (⟨fun j ↦ if hj : j ∈ R.primary α then 0 else v.val ⟨j, hj⟩,
      by
        refine SingularLearningTheory.mem_cube.2 fun j ↦ ?_
        split_ifs with hj
        · exact ⟨le_rfl, (R.b_pos α).le⟩
        · exact ⟨v.2.1 ⟨j, hj⟩, v.2.2 ⟨j, hj⟩⟩⟩ : cube d (R.b α))
      = zeroPrimary R α v := by
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ R.primary α
    · simp [zeroPrimary, ResolutionAtlas.primaryZero, hj]
    · simpa [zeroPrimary, ResolutionAtlas.primaryZero, hj,
        min_eq_right (v.2.2 ⟨j, hj⟩)] using v.2.1 ⟨j, hj⟩
  exact congrArg (fun u : cube d (R.b α) ↦
    t ^ (R.rlct - 1) * (∏ j, v.val j ^ R.secondaryExponent α j) *
      exp (-(β * t) + β * √t * χ ⟨α, u⟩) * R.weight α u) hp

/-- Integrating a function of `(0, v)` over the chart cube integrates out the primary
coordinates: `∫_{[0,b]^d} G(0, v_{Pᶜ}) dv = b^{m_α} ∫_{[0,b]^{d−m_α}} G(0, v) dv`. -/
private theorem integral_cube_primaryZero (α : R.ι) (G : cube d (R.b α) → ℝ) :
    ∫ v in cube d (R.b α), G (R.primaryZero α v)
      = R.b α ^ R.chartMult α * ∫ v in secondaryCube R α, G (zeroPrimary R α v) := by
  classical
  have hb := R.b_pos α
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d ↦ ℝ) (fun j ↦ j ∈ R.primary α)
    with he
  have hmp : MeasurePreserving e := by
    convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d ↦ ℝ) (fun j ↦ j ∈ R.primary α)
  set cubeP : Set ({j // j ∈ R.primary α} → ℝ) := Set.pi univ fun _ ↦ Icc 0 (R.b α) with hcubeP
  have hpre : cube d (R.b α) = e ⁻¹' (cubeP ×ˢ secondaryCube R α) := by
    ext v
    simp only [SingularLearningTheory.cube_eq_pi, secondaryCube, hcubeP, mem_preimage, mem_prod,
        Set.mem_pi, mem_univ,
      true_imp_iff, he, MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.coe_mk,
      Equiv.piEquivPiSubtypeProd_apply]
    constructor
    · intro h
      exact ⟨fun j ↦ h j, fun j ↦ h j⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j ∈ R.primary α
      · exact h1 ⟨j, hj⟩
      · exact h2 ⟨j, hj⟩
  have hpz : ∀ z, R.primaryZero α (e.symm z) = zeroPrimary R α z.2 := by
    intro z
    refine Subtype.ext (funext fun j ↦ ?_)
    simp only [ResolutionAtlas.primaryZero, zeroPrimary, he, MeasurableEquiv.piEquivPiSubtypeProd,
      MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, Equiv.piEquivPiSubtypeProd_symm_apply]
    by_cases hj : j ∈ R.primary α
    · simp [hj]
    · simp [hj]
  have hint : ∫ v in cube d (R.b α), G (R.primaryZero α v)
      = ∫ z in cubeP ×ˢ secondaryCube R α, G (zeroPrimary R α z.2) := by
    rw [← hmp.setIntegral_preimage_emb e.measurableEmbedding
      (fun z ↦ G (zeroPrimary R α z.2)) (cubeP ×ˢ secondaryCube R α), ← hpre]
    refine setIntegral_congr_fun measurableSet_Icc fun v _ ↦ ?_
    rw [← hpz, e.symm_apply_apply]
  have hvol : ∫ _ in cubeP, (1 : ℝ) = R.b α ^ R.chartMult α := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, hcubeP, volume_pi_pi]
    simp only [Real.volume_Icc, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hb.le]
    rfl
  rw [hint, Measure.volume_eq_prod, ← hvol, ← setIntegral_prod_mul (fun _ ↦ (1 : ℝ))
    (fun v ↦ G (zeroPrimary R α v)) cubeP (secondaryCube R α)]
  simp only [one_mul]

/-- On the secondary cube, the clamp in `zeroPrimary` is the identity. -/
private theorem zeroPrimary_apply_of_mem (α : R.ι) {v : {j // j ∉ R.primary α} → ℝ}
    (hv : v ∈ secondaryCube R α) {j : Fin d} (hj : j ∉ R.primary α) :
    (zeroPrimary R α v : Fin d → ℝ) j = v ⟨j, hj⟩ := by
  obtain ⟨h0, hb⟩ := hv ⟨j, hj⟩ (mem_univ _)
  simp only [zeroPrimary, ResolutionAtlas.primaryZero, hj, ite_false, dite_eq_right,
    not_false_eq_true]
  rw [min_eq_right hb, max_eq_right h0]

/-- On the chart cube, the clamp in `primaryZero` is the identity on the secondary coordinates. -/
private theorem primaryZero_apply_of_mem (α : R.ι) {v : Fin d → ℝ} (hv : v ∈ cube d (R.b α))
    {j : Fin d} (hj : j ∉ R.primary α) : (R.primaryZero α v : Fin d → ℝ) j = v j := by
  obtain ⟨h0, hb⟩ := mem_cube.1 hv j
  simp only [ResolutionAtlas.primaryZero, hj, ite_false]
  rw [min_eq_right hb, max_eq_right h0]

/-- The integrand of `Y^α`, as a function of `t` and a point `u` of the chart cube. -/
private noncomputable def yIntegrand (β : ℝ) (α : R.ι) (ζ : C(cube d (R.b α), ℝ)) (t : ℝ)
    (u : cube d (R.b α)) : ℝ :=
  t ^ (R.rlct - 1) * exp (-(β * t) + β * √t * ζ u) *
    ((∏ j ∈ (R.primary α)ᶜ, (u : Fin d → ℝ) j ^ R.secondaryExponent α j) * R.weight α u)

private theorem measurable_yIntegrand (β : ℝ) (α : R.ι) (ζ : C(cube d (R.b α), ℝ)) :
    Measurable (Function.uncurry fun t v ↦ yIntegrand R β α ζ t (R.primaryZero α v)) := by
  have hpz : Measurable fun z : ℝ × (Fin d → ℝ) ↦ R.primaryZero α z.2 :=
    (R.continuous_primaryZero α).measurable.comp measurable_snd
  refine ((measurable_fst.pow_const _).mul (Real.measurable_exp.comp ?_)).mul (Measurable.mul ?_ ?_)
  · refine ((measurable_const.mul measurable_fst).neg).add (Measurable.mul ?_ ?_)
    · exact (measurable_const.mul (Real.continuous_sqrt.measurable.comp measurable_fst))
    · exact (map_continuous ζ).measurable.comp hpz
  · refine Finset.measurable_prod _ fun j _ ↦ ?_
    exact ((measurable_pi_apply j).comp (measurable_subtype_coe.comp hpz)).pow_const _
  · exact (R.continuous_weight_primaryZero α).measurable.comp measurable_snd

/-- The `Y^α` integrand is dominated by the product of an integrable function of `t` and the
trace weight, so Fubini applies. -/
private theorem integrable_yIntegrand {β : ℝ} (hβ : 0 < β) (α : R.ι)
    (ζ : C(cube d (R.b α), ℝ)) :
    Integrable (Function.uncurry fun t v ↦ yIntegrand R β α ζ t (R.primaryZero α v))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (cube d (R.b α)))) := by
  have hcube : MeasurableSet (cube d (R.b α)) := measurableSet_Icc
  have hg : IntegrableOn (fun t : ℝ ↦ t ^ (R.rlct - 1) *
      exp (-(β * t) + β * √t * ‖ζ‖)) (Ioi 0) :=
    NormalCrossing.integrableOn_rpow_mul_exp_frozen R.rlct_pos hβ (abs_norm ζ).le
  refine Integrable.mono' (hg.mul_prod (R.integrableOn_traceWeight α))
    (measurable_yIntegrand R β α ζ).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod hcube)] with z hz
  obtain ⟨ht, hv⟩ := hz
  have ht : (0 : ℝ) < z.1 := ht
  have hw0 : 0 ≤ R.weight α (R.primaryZero α z.2) := R.weight_nonneg α _ (R.primaryZero α z.2).2
  have hprod : ∀ j, 0 ≤ ((R.primaryZero α z.2 : Fin d → ℝ) j) ^ R.secondaryExponent α j :=
    fun j ↦ Real.rpow_nonneg ((R.primaryZero α z.2).2.1 j) _
  have hprod' : (∏ j ∈ (R.primary α)ᶜ,
        (R.primaryZero α z.2 : Fin d → ℝ) j ^ R.secondaryExponent α j)
      = ∏ j ∈ (R.primary α)ᶜ, z.2 j ^ R.secondaryExponent α j :=
    Finset.prod_congr rfl fun j hj ↦ by
      rw [primaryZero_apply_of_mem R α hv (Finset.mem_compl.mp hj)]
  simp only [Function.uncurry, yIntegrand, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
    (mul_nonneg (Finset.prod_nonneg fun j _ ↦ hprod j) hw0)), hprod',
    ResolutionAtlas.traceWeight]
  have hζ : ζ (R.primaryZero α z.2) ≤ ‖ζ‖ :=
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (ContinuousMap.norm_coe_le_norm ζ _))
  have hexp : exp (-(β * z.1) + β * √z.1 * ζ (R.primaryZero α z.2))
      ≤ exp (-(β * z.1) + β * √z.1 * ‖ζ‖) := by
    gcongr
  have htw : 0 ≤ (∏ j ∈ (R.primary α)ᶜ, z.2 j ^ R.secondaryExponent α j) *
      R.weight α (R.primaryZero α z.2) := by
    rw [← hprod']
    exact mul_nonneg (Finset.prod_nonneg fun j _ ↦ hprod j) hw0
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht.le _)) htw

/-- `Y` equals the library's `limitFunctional`: on each essential chart,
the secondary-coordinate integral is `b^{−m}` times the whole-cube integral,
and the order of integration is swapped by Fubini. -/
private theorem Y_eq_limitFunctional {β : ℝ} (hβ : 0 < β)
    (χ : C((α : R.ι) × cube d (R.b α), ℝ)) :
    AtlasY β R χ = R.limitFunctional β (R.toChartFunctions χ) := by
  classical
  rw [Y_eq_secondary_integral R]
  unfold ResolutionAtlas.limitFunctional
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  split_ifs with hα
  swap
  · rfl
  have hb := R.b_pos α
  have hsc : MeasurableSet (secondaryCube R α) := MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hcube : MeasurableSet (cube d (R.b α)) := measurableSet_Icc
  set ζ : C(cube d (R.b α), ℝ) := R.toChartFunctions χ α with hζ
  -- the inner integrand on the secondary cube is `yIntegrand` at `(0, v)`
  have hinner : ∀ t : ℝ, ∫ v in secondaryCube R α,
      t ^ (R.rlct - 1) * (∏ j, v j ^ R.secondaryExponent α j) *
        exp (-(β * t) + β * √t * χ ⟨α, zeroPrimary R α v⟩) *
        R.weight α (zeroPrimary R α v)
      = (R.b α ^ R.chartMult α)⁻¹ * ∫ v in cube d (R.b α),
          yIntegrand R β α ζ t (R.primaryZero α v) := by
    intro t
    rw [integral_cube_primaryZero R α (yIntegrand R β α ζ t), ← mul_assoc,
      inv_mul_cancel₀ (pow_pos hb _).ne', one_mul]
    refine setIntegral_congr_fun hsc fun v hv ↦ ?_
    have hprod : ∏ j ∈ (R.primary α)ᶜ, (zeroPrimary R α v : Fin d → ℝ) j ^ R.secondaryExponent α j
        = ∏ j : {j // j ∉ R.primary α}, v j ^ R.secondaryExponent α j := by
      rw [Finset.prod_subtype (R.primary α)ᶜ (fun j ↦ Finset.mem_compl)
        (fun j ↦ (zeroPrimary R α v : Fin d → ℝ) j ^ R.secondaryExponent α j)]
      exact Finset.prod_congr rfl fun j _ ↦ by rw [zeroPrimary_apply_of_mem R α hv j.2]
    simp only [yIntegrand, hprod, hζ, ResolutionAtlas.toChartFunctions_apply]
    ring
  simp only [hinner]
  rw [integral_const_mul, ← mul_assoc, R.chartLimit_eq, div_eq_mul_inv,
    hα.2, integral_integral_swap (integrable_yIntegrand R hβ α ζ)]
  congr 1
  refine setIntegral_congr_fun hcube fun v hv ↦ ?_
  simp only [yIntegrand, frozenInner, ResolutionAtlas.traceWeight]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  have hprod' : (∏ j ∈ (R.primary α)ᶜ,
        (R.primaryZero α v : Fin d → ℝ) j ^ R.secondaryExponent α j)
      = ∏ j ∈ (R.primary α)ᶜ, v j ^ R.secondaryExponent α j :=
    Finset.prod_congr rfl fun j hj ↦ by
      rw [primaryZero_apply_of_mem R α hv (Finset.mem_compl.mp hj)]
  rw [hprod']
  ring

end YBridges

section FreeEnergy

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- `tendstoInDistribution_normalizedEvidence` from the conclusions of [Wat09, Theorems 6.1 and 5.9]
taken as hypotheses: the resolved likelihood `L`, the empirical-process limits `E` (chart process)
and `T` (`ψ_n` on `{K ≥ δ}`) on one probability space, and the Lipschitz tightness `hlip`; the
library's `EmpiricalProcessInput.tendstoInDistribution_normalizedEvidence` after the `Y` bridge. -/
private theorem tendstoInDistribution_normalizedEvidence_of_inputs
    -- the model
    (q : Measure X) [IsProbabilityMeasure q] (p : (Fin d → ℝ) → X → ℝ)
    (hp : Measurable (Function.uncurry p)) (W : Set (Fin d → ℝ)) (hW : IsCompact W)
    (φ : (Fin d → ℝ) → ℝ) (β : ℝ) (hβ : 0 < β)
    -- an optimal parameter `w₀ ∈ W₀`
    (w₀ : Fin d → ℝ)
    -- fundamental conditions I (`s = 2`) and II
    (I : SingularLearningTheory.FundamentalConditionI 2 q (logDensityRatio p w₀) (excessLoss q p w₀) W)
    (II : SingularLearningTheory.FundamentalConditionII φ W)
    -- the sample
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : ∀ i, MeasurePreserving (Xs i) P q)
    -- resolution of singularities
    (R : ResolutionAtlas (excessLoss q p w₀) φ W)
    (hLip : ∀ α, R.IsEssential α →
      ∃ L : NNReal, LipschitzOnWith L (R.weight α) (cube d (R.b α)))
    -- conclusions of [Wat09, Theorems 6.1 and 5.9]
    (Lk : R.ResolvedLikelihood q (logDensityRatio p w₀)) (P' : Measure Ω') [IsProbabilityMeasure P']
    (E : SingularLearningTheory.EmpiricalProcessLimit q
      (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ Lk.a u.1 x u.2) Xs P P')
    (hlip : R.PrimaryLipschitzTight E.Ψ P)
    (T : SingularLearningTheory.EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ excessLoss q p w₀ w}) ↦ logDensityRatio p w₀ x w / √(excessLoss q p w₀ w))
      Xs P P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) ↦ (n : ℝ) ^ R.rlct / log n ^ (R.mult - 1) * normalizedEvidence p w₀ W φ
          β Xs n ω)
      atTop (fun ω' ↦ AtlasY β R (-(E.Ψlim ω'))) (fun _ ↦ P) P' := by
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hXl : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  have hWm : MeasurableSet W := hW.isClosed.measurableSet
  have hφ : ∀ w ∈ W, 0 ≤ φ w := fun _ hw ↦ II.nonneg hw
  have hφi : IntegrableOn φ W := (II.continuousOn).integrableOn_compact hW
  let J : R.EmpiricalProcessInput β P P' := Lk.empiricalProcessInput β P P' hXm hXl
    (measurable_uncurry_logDensityRatio hp w₀) (fun _ ↦ rfl) (I.isCompact_tail hW R.δ) E hlip T
  have hY : (fun ω' ↦ AtlasY β R (-(E.Ψlim ω'))) = fun ω' ↦ R.limitFunctional β (J.Ξlim ω') := by
    funext ω'
    rw [Y_eq_limitFunctional R hβ, ResolutionAtlas.toChartFunctions_neg]
    rfl
  rw [hY]
  exact J.tendstoInDistribution_normalizedEvidence hWm hφ hφi hβ hLip


/-- The stochastic part of the free energy formula from the same inputs as
`tendstoInDistribution_normalizedEvidence_of_inputs`; the library's
`NondegenerateResolutionAtlas.free_energy_formula`. -/
private theorem free_energy_formula_stochastic_of_inputs
    -- the model
    (q : Measure X) [IsProbabilityMeasure q] (p : (Fin d → ℝ) → X → ℝ)
    (hp : Measurable (Function.uncurry p)) (W : Set (Fin d → ℝ)) (hW : IsCompact W)
    (hp_pos : ∀ᵐ x ∂q, ∀ w ∈ W, 0 < p w x) (φ : (Fin d → ℝ) → ℝ) (β : ℝ) (hβ : 0 < β)
    -- an optimal parameter `w₀ ∈ W₀`
    (w₀ : Fin d → ℝ) (hw₀ : w₀ ∈ W)
    -- fundamental conditions I (`s = 2`) and II
    (I : SingularLearningTheory.FundamentalConditionI 2 q (logDensityRatio p w₀) (excessLoss q p w₀) W)
    (II : SingularLearningTheory.FundamentalConditionII φ W)
    -- the sample
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : ∀ i, MeasurePreserving (Xs i) P q)
    -- resolution of singularities, nondegenerate
    (R : NondegenerateResolutionAtlas (excessLoss q p w₀) φ W)
    (hLip : ∀ α, R.IsEssential α →
      ∃ L : NNReal, LipschitzOnWith L (R.weight α) (cube d (R.b α)))
    -- conclusions of [Wat09, Theorems 6.1 and 5.9]
    (Lk : R.toResolutionAtlas.ResolvedLikelihood q (logDensityRatio p w₀))
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (E : SingularLearningTheory.EmpiricalProcessLimit q
      (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ Lk.a u.1 x u.2) Xs P P')
    (hlip : R.toResolutionAtlas.PrimaryLipschitzTight E.Ψ P)
    (T : SingularLearningTheory.EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ excessLoss q p w₀ w}) ↦ logDensityRatio p w₀ x w / √(excessLoss q p w₀ w))
      Xs P P') :
    ∃ Rn : ℕ → Ω → ℝ,
      (∀ n : ℕ, 2 ≤ n → ∀ᵐ ω ∂P,
        freeEnergy p W φ β Xs n ω = n * β * empiricalNegativeLogLikelihood p Xs n ω w₀ + R.rlct *
            log n
          - ((R.mult - 1 : ℕ) : ℝ) * log (log n) + Rn n ω) ∧
      TendstoInDistribution Rn atTop
        (fun ω' ↦ -log (AtlasY β R.toResolutionAtlas (-(E.Ψlim ω')))) (fun _ ↦ P) P' := by
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hXl : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  have hWm : MeasurableSet W := hW.isClosed.measurableSet
  have hφ : ∀ w ∈ W, 0 ≤ φ w := fun _ hw ↦ II.nonneg hw
  have hφi : IntegrableOn φ W := (II.continuousOn).integrableOn_compact hW
  let J : R.toResolutionAtlas.EmpiricalProcessInput β P P' := Lk.empiricalProcessInput β P P'
    hXm hXl (measurable_uncurry_logDensityRatio hp w₀) (fun _ ↦ rfl) (I.isCompact_tail hW R.δ) E
    hlip T
  refine ⟨J.Rn, fun n hn ↦ ?_, ?_⟩
  · filter_upwards
      [R.normalizedEvidence_pos J hWm hφ hφi hβ hn, ae_pos_at_samples hp_pos hXm hXl n] with ω hZ
      hpos
    rw [freeEnergy_eq_add_neg_log_normalizedEvidence hWm hpos hw₀ φ β hZ]
    exact J.freeEnergy_eq (fun n ω ↦ empiricalNegativeLogLikelihood p Xs n ω w₀) hn hZ
  · have hY : (fun ω' ↦ -log (AtlasY β R.toResolutionAtlas (-(E.Ψlim ω'))))
        = fun ω' ↦ -log (R.limitFunctional β (J.Ξlim ω')) := by
      funext ω'
      rw [Y_eq_limitFunctional R.toResolutionAtlas hβ, ResolutionAtlas.toChartFunctions_neg]
      rfl
    rw [hY]
    exact R.free_energy_formula J hWm hφ hφi hβ hLip


/-- The expectation part of the free energy formula from the inputs of
`free_energy_formula_stochastic_of_inputs` and the fourth-moment bounds `hE`, `hT`
([Wat09, Theorem 5.8], `s = 4`); the library's `eventually_integral_normalizedFreeEnergy_eq` and
`tendsto_integral_Rn`. -/
private theorem free_energy_formula_expectation_of_inputs
    -- the model
    (q : Measure X) [IsProbabilityMeasure q] (p : (Fin d → ℝ) → X → ℝ)
    (hp : Measurable (Function.uncurry p)) (W : Set (Fin d → ℝ)) (hW : IsCompact W)
    (hp_pos : ∀ᵐ x ∂q, ∀ w ∈ W, 0 < p w x) (φ : (Fin d → ℝ) → ℝ) (β : ℝ) (hβ : 0 < β)
    -- an optimal parameter `w₀ ∈ W₀`
    (w₀ : Fin d → ℝ) (hw₀ : w₀ ∈ W) (hL : Integrable (fun x ↦ log (p w₀ x)) q)
    -- fundamental conditions I (`s = 2` and `s = 4`) and II
    (I : SingularLearningTheory.FundamentalConditionI 2 q (logDensityRatio p w₀) (excessLoss q p w₀) W)
    (II : SingularLearningTheory.FundamentalConditionII φ W)
    -- the sample
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : ∀ i, MeasurePreserving (Xs i) P q)
    -- resolution of singularities, nondegenerate
    (R : NondegenerateResolutionAtlas (excessLoss q p w₀) φ W)
    (hLip : ∀ α, R.IsEssential α →
      ∃ L : NNReal, LipschitzOnWith L (R.weight α) (cube d (R.b α)))
    -- conclusions of [Wat09, Theorems 6.1, 5.9 and 5.8]
    (Lk : R.toResolutionAtlas.ResolvedLikelihood q (logDensityRatio p w₀))
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (E : SingularLearningTheory.EmpiricalProcessLimit q
      (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ Lk.a u.1 x u.2) Xs P P')
    (hlip : R.toResolutionAtlas.PrimaryLipschitzTight E.Ψ P)
    (T : SingularLearningTheory.EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ excessLoss q p w₀ w}) ↦ logDensityRatio p w₀ x w / √(excessLoss q p w₀ w))
      Xs P P')
    (hE : E.MomentBound 4) (hT : T.MomentBound 4) :
    ∃ Rn : ℕ → Ω → ℝ,
      (∀ n : ℕ, 2 ≤ n → ∀ᵐ ω ∂P,
        freeEnergy p W φ β Xs n ω = n * β * empiricalNegativeLogLikelihood p Xs n ω w₀ + R.rlct *
            log n
          - ((R.mult - 1 : ℕ) : ℝ) * log (log n) + Rn n ω) ∧
      (∀ᶠ n : ℕ in atTop,
        ∫ ω, freeEnergy p W φ β Xs n ω ∂P = n * β * expectedNegativeLogLikelihood q p w₀ + R.rlct *
            log n
          - ((R.mult - 1 : ℕ) : ℝ) * log (log n) + ∫ ω, Rn n ω ∂P) ∧
      Tendsto (fun n ↦ ∫ ω, Rn n ω ∂P) atTop
        (𝓝 (∫ ω', -log (AtlasY β R.toResolutionAtlas (-(E.Ψlim ω'))) ∂P')) ∧
      TendstoInDistribution Rn atTop
        (fun ω' ↦ -log (AtlasY β R.toResolutionAtlas (-(E.Ψlim ω')))) (fun _ ↦ P) P' := by
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hXl : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  have hWm : MeasurableSet W := hW.isClosed.measurableSet
  have hφ : ∀ w ∈ W, 0 ≤ φ w := fun _ hw ↦ II.nonneg hw
  have hφi : IntegrableOn φ W := (II.continuousOn).integrableOn_compact hW
  let J' : R.toResolutionAtlas.IntegrableEmpiricalProcessInput β P P' :=
    Lk.integrableEmpiricalProcessInput β P P' hXm hXl (measurable_uncurry_logDensityRatio hp w₀)
      (fun _ ↦ rfl) (I.isCompact_tail hW R.δ) E hlip T hE hT
  let J : R.toResolutionAtlas.EmpiricalProcessInput β P P' := J'.toEmpiricalProcessInput
  -- the sample means of `log p(X_i|w₀)`
  have hlog : ∀ i, Integrable (fun ω ↦ log (p w₀ (Xs i ω))) P := fun i ↦ by
    have h := hL
    rw [← (hX i).map_eq] at h
    exact (integrable_map_measure h.1 (hX i).measurable.aemeasurable).mp h
  have hlog_int : ∀ i, ∫ ω, log (p w₀ (Xs i ω)) ∂P = ∫ x, log (p w₀ x) ∂q := fun i ↦ by
    have h := hL
    rw [← (hX i).map_eq] at h ⊢
    exact (integral_map (hX i).measurable.aemeasurable h.1).symm
  refine ⟨J.Rn, fun n hn ↦ ?_, ?_, ?_, ?_⟩
  · filter_upwards
      [R.normalizedEvidence_pos J hWm hφ hφi hβ hn, ae_pos_at_samples hp_pos hXm hXl n] with ω hZ
      hpos
    rw [freeEnergy_eq_add_neg_log_normalizedEvidence hWm hpos hw₀ φ β hZ]
    exact J.freeEnergy_eq (fun n ω ↦ empiricalNegativeLogLikelihood p Xs n ω w₀) hn hZ
  · filter_upwards [R.eventually_integral_normalizedFreeEnergy_eq J' hWm hφ hφi hβ,
      (R.asympUnifIntegrable_Rn J' hWm hφ hφi hβ).eventually_integrable
        (J.aestronglyMeasurable_Rn hφi), eventually_ge_atTop 2] with n hFn0 hRint hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hae : (fun ω ↦ freeEnergy p W φ β Xs n ω) =ᵐ[P] fun ω ↦ n * β *
        empiricalNegativeLogLikelihood p Xs n ω w₀ + J.normalizedFreeEnergy n ω := by
      filter_upwards
          [R.normalizedEvidence_pos J hWm hφ hφi hβ hn, ae_pos_at_samples hp_pos hXm hXl n]
        with ω hZ hpos
      exact freeEnergy_eq_add_neg_log_normalizedEvidence hWm hpos hw₀ φ β hZ
    have hLn_int : Integrable (fun ω ↦ empiricalNegativeLogLikelihood p Xs n ω w₀) P :=
      ((integrable_finsetSum _ fun i _ ↦ hlog i).neg).div_const _
    have hLn : ∫ ω, empiricalNegativeLogLikelihood p Xs n ω w₀ ∂P = expectedNegativeLogLikelihood q p w₀ := by
      unfold empiricalNegativeLogLikelihood expectedNegativeLogLikelihood
      rw [integral_div, integral_neg, integral_finsetSum _ fun i _ ↦ hlog i]
      simp only [hlog_int, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [neg_div, mul_div_cancel_left₀ _ hn0]
    have hFn0_int : Integrable (J.normalizedFreeEnergy n) P := by
      have heq : J.normalizedFreeEnergy n =ᵐ[P] fun ω ↦
          (R.rlct * log n - ((R.mult - 1 : ℕ) : ℝ) * log (log n)) + J.Rn n ω := by
        filter_upwards [R.normalizedEvidence_pos J hWm hφ hφi hβ hn] with ω hZ
        exact J.normalizedFreeEnergy_eq hn hZ
      exact ((integrable_const _).add hRint).congr heq.symm
    rw [integral_congr_ae hae, integral_add (hLn_int.const_mul _) hFn0_int, integral_const_mul,
      hLn, hFn0]
    ring
  · have hY : (fun ω' ↦ -log (AtlasY β R.toResolutionAtlas (-(E.Ψlim ω'))))
        = fun ω' ↦ -log (R.limitFunctional β (J'.Ξlim ω')) := by
      funext ω'
      rw [Y_eq_limitFunctional R.toResolutionAtlas hβ, ResolutionAtlas.toChartFunctions_neg]
      rfl
    rw [hY]
    exact R.tendsto_integral_Rn J' hWm hφ hφi hβ hLip
  · have hY : (fun ω' ↦ -log (AtlasY β R.toResolutionAtlas (-(E.Ψlim ω'))))
        = fun ω' ↦ -log (R.limitFunctional β (J.Ξlim ω')) := by
      funext ω'
      rw [Y_eq_limitFunctional R.toResolutionAtlas hβ, ResolutionAtlas.toChartFunctions_neg]
      rfl
    rw [hY]
    exact R.free_energy_formula J hWm hφ hφi hβ hLip


end FreeEnergy


/-- `tendstoInDistribution_normalizedEvidence` for fixed resolved coefficients `L` and a limit `Ψ`
of their centred empirical process: the normalised evidence converges in law to `Y(−Ψ)`. -/
private theorem tendstoInDistribution_normalizedEvidence_of_limit
    (q : Measure X) [IsProbabilityMeasure q] (p : (Fin d → ℝ) → X → ℝ)
    (hp : Measurable (Function.uncurry p)) (W : Set (Fin d → ℝ)) (hW : IsCompact W)
    (φ : (Fin d → ℝ) → ℝ)
    (w₀ : Fin d → ℝ)
    (I : FundamentalConditionI 2 q (logDensityRatio p w₀) (excessLoss q p w₀) W) (II : FundamentalConditionII φ W)
    (hcont : ∀ᵐ x ∂q, ContinuousOn (logDensityRatio p w₀ x) W)
    (R : ResolutionAtlas (excessLoss q p w₀) φ W)
    (hLip : ∀ α, R.IsEssential α →
      ∃ L : NNReal, LipschitzOnWith L (R.weight α) (cube d (R.b α)))
    (L : R.AnalyticResolvedLikelihood 2 q (logDensityRatio p w₀))
    (β : ℝ) (hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
    [IsProbabilityMeasure P] (hXs : IsIIDSample q Xs P)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (E : EmpiricalProcessLimit q
      (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2) Xs P P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) ↦
        (n : ℝ) ^ R.rlct / log n ^ (R.mult - 1) * normalizedEvidence p w₀ W φ β Xs n ω)
      atTop (fun ω' ↦ AtlasY β R (-(E.Ψlim ω'))) (fun _ ↦ P) P' :=
  by
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hXl : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  obtain ⟨P₂, hP₂, ⟨T₀⟩⟩ := I.exists_tail_empiricalProcessLimit hW
    (fun w ↦ (measurable_uncurry_logDensityRatio hp w₀).comp
      (measurable_id.prodMk measurable_const)) hcont R.δ_pos hXm hXl hIndep
  have h := tendstoInDistribution_normalizedEvidence_of_inputs q p hp W hW φ β hβ w₀
    I II Xs P hX R hLip L.toResolvedLikelihood
    (P'.prod P₂) E.prodFst
    (L.primaryLipschitzTight hXm hXl hIndep E.Ψ_ae_eq)
    T₀.prodSnd
  have hY : Continuous (fun χ : C((α : R.ι) × cube d (R.b α), ℝ) ↦ AtlasY β R (-χ)) := by
    simp_rw [Y_eq_limitFunctional R hβ]
    exact (R.continuous_limitFunctional hβ).comp (R.continuous_toChartFunctions.comp continuous_neg)
  have hm := hY.measurable.comp_aemeasurable E.tendsto.aemeasurable_limit
  refine ⟨h.forall_aemeasurable, hm, ?_⟩
  convert h.tendsto using 3
  congr 1
  apply ProbabilityMeasure.toMeasure_injective
  exact (Measure.map_comp_fst hm).symm

section AtlasStandardForm

end AtlasStandardForm

section PieceBridges

open SingularLearningTheory.SLTResolution SingularLearningTheory.SLTResolution.ChartFamily

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} {R : SLTResolution K φ W}
  {F : R.ChartFamily}

/-- The resolved log density ratio of the pieces, read on an atlas whose charts are the pieces, as
the library's `ResolutionAtlas.AnalyticResolvedLikelihood`: the coefficients are continuous on the
cubes, and their `L^s(q)`-analyticity gives the local `L²(q)` expansions. -/
noncomputable def ResolvedLogDensityRatio.toAnalyticResolvedLikelihood {s : ℝ≥0∞} [Fact (1 ≤ s)]
    {q : Measure X} [IsProbabilityMeasure q] {f : X → (Fin d → ℝ) → ℝ} {φ' : (Fin d → ℝ) → ℝ}
    (L : ResolvedLogDensityRatio s F q f) (A : ResolutionAtlas K φ' W) (e : A.ι → F.Piece)
    (hb : ∀ i, A.b i = (e i).radius) (hk : ∀ i, A.k i = (e i).k)
    (hg : ∀ i, ∀ u ∈ cube d (A.b i), A.g i u = (e i).map u) (hs : 2 ≤ s) :
    A.AnalyticResolvedLikelihood s q f :=
  have hmem : ∀ i (u : cube d (A.b i)), (u : Fin d → ℝ) ∈ cube d (e i).radius := fun i u ↦ by
    rw [← hb]; exact u.2
  have hcont : ∀ i x, ContinuousOn (L.a (e i) x) (cube d (A.b i)) := fun i x ↦ by
    have := L.a_continuous (e i) x
    rwa [← hb] at this
  have hls : ∀ i, LsValuedAnalytic s q (L.a (e i)) (cube d (A.b i)) := fun i ↦ by
    have := L.ls_analytic (e i)
    rwa [← hb] at this
  { a := fun i x ↦ ⟨fun u ↦ L.a (e i) x u, continuousOn_iff_continuous_domRestrict.mp (hcont i x)⟩
    a_measurable := fun i ↦ ContinuousMap.measurable_of_eval fun u ↦
      L.a_measurable (e i) ⟨u, hmem i u⟩
    factor := fun i ↦ (L.factor (e i)).mono fun x hx u ↦ by
      rw [hg i u u.2, hk]
      exact hx ⟨u, hmem i u⟩
    mean := fun i u ↦ by
      rw [hk]
      exact L.mean (e i) ⟨u, hmem i u⟩
    memLp := by
      intro i u
      obtain ⟨U, -, hU, G, -, hG⟩ := hls i
      exact ((Lp.memLp (G u)).mono_exponent hs).ae_eq (hG u (hU u.2))
    loc := by
      intro i u
      obtain ⟨U, -, hU, G, hGa, hGeq⟩ := hls i
      obtain ⟨p, r, hpr⟩ := hGa u (hU u.2)
      obtain ⟨ρ, hρ, hrep⟩ := HasFPowerSeriesOnBall.exists_l2Expansion hs hpr
        (fun v : cube d (A.b i) ↦ (v : Fin d → ℝ)) (fun x v ↦ L.a (e i) x v)
        (fun v _ ↦ hGeq v (hU v.2))
      refine ⟨{v | dist (v : Fin d → ℝ) u < ρ},
        isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const,
        by simpa using hρ, ?_⟩
      exact hrep _ (fun v hv ↦ le_of_lt hv)
        (fun v _ w _ ↦ le_of_eq (Subtype.dist_eq v w).symm) }

open scoped Classical in
/-- `Y` of a chart family is the atlas-indexed `Y` of the atlas of its pieces, once the
resolution's `(λ, m)` is the atlas's. -/
private theorem Y_eq_atlasY [Nonempty R.M] [Nonempty F.Piece]
    {ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel}
    {hρ : ρ.IsSubordinate fun i ↦ (F.chart i).openCube} {hW : IsCompact W}
    {hKc : ContinuousOn K W} {hK : ∀ w ∈ W, 0 ≤ K w} {hφc : ContinuousOn φ W}
    (hl : R.rlct = (toResolutionAtlas ρ hρ hW hKc hK hφc).rlct)
    (hm : R.mult = (toResolutionAtlas ρ hρ hW hKc hK hφc).mult) (β : ℝ)
    (χ : C((α : F.Piece) × cube d α.radius, ℝ)) :
    F.limitFunctional β ρ χ = AtlasY β (toResolutionAtlas ρ hρ hW hKc hK hφc)
      χ := by
  classical
  set A := toResolutionAtlas ρ hρ hW hKc hK hφc
  have hess : ∀ α : F.Piece, α.IsEssential ↔ A.IsEssential α := fun α ↦ by
    unfold Piece.IsEssential ResolutionAtlas.IsEssential
    rw [toResolutionAtlas_chartRlct, toResolutionAtlas_chartMult, hl, hm]
  unfold SLTResolution.ChartFamily.limitFunctional AtlasY
  have hfs : ∀ g : F.Piece → ℝ, (∑ᶠ (α : F.Piece) (_ : α.IsEssential), g α)
      = ∑ α ∈ Finset.univ.filter fun α : F.Piece ↦ α.IsEssential, g α := fun g ↦
    finsum_cond_eq_sum_of_cond_iff g fun {α} _ ↦ by simp
  rw [hfs, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  by_cases h : α.IsEssential
  · rw [ite_eq_left h, ite_eq_left ((hess α).mp h), hl]
    rfl
  · rw [ite_eq_right h, ite_eq_right fun h' ↦ h ((hess α).mpr h')]

end PieceBridges

/-- **Convergence in law of the normalized evidence.** For a resolution `R`, a chart family `F` of
it and a partition of unity `ρ` subordinate to `F`, there are resolved coefficients `a` on the
pieces (`exists_resolvedLogDensityRatio`) such that, for every `β > 0` and every i.i.d. sample, the
centred empirical process of `a` has a limit `Ψ` and `n^λ (log n)^{−(m−1)} Z_n^0` converges in law
to `Y(ξ)`, where `λ` and `m` are read off `R`. Here `ξ = −Ψ`, with the sign of the standard form
(6.10). Since the left-hand side does not involve `F` or `ρ`, neither does the law of `Y(ξ)`.

Relation to the source.
* **Strengthening.** Stated for every resolution, chart family and subordinate partition of unity;
  the law of the limit does not depend on them.
* **Correction.** The printed limit lacks the factor $y^\mu$ of [Wat09, Definition 6.8] and §6.3.3;
  the limit here carries it, as $\prod_j v_j^{h_j - 2k_j\lambda}$.
* **Gap.** $f(x, \cdot)$ is assumed continuous on $W$ for $q$-almost every $x$.

Source statement: [Wat09, Theorem 6.7] -/
-- `hw₀` is unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
theorem tendstoInDistribution_normalizedEvidence {d : ℕ} {X : Type*} [MeasurableSpace X]
    -- data distribution
    (q : Measure X) [IsProbabilityMeasure q]
    -- model
    (p : (Fin d → ℝ) → X → ℝ)
    (hp : Measurable (Function.uncurry p)) (W : Set (Fin d → ℝ)) (hW : IsCompact W)
    -- prior
    (φ : (Fin d → ℝ) → ℝ)
    -- `w₀` need not minimise `L`: RFV already gives `K ≥ 0` on `W`
    (w₀ : Fin d → ℝ) (hw₀ : w₀ ∈ W)
    (hRFV : RelativelyFiniteVariance q p w₀ W)
    -- fundamental condition I makes `K` real analytic on an open neighbourhood of `W`
    (I : FundamentalConditionI 2 q (logDensityRatio p w₀) (excessLoss q p w₀) W)
    (II : FundamentalConditionII φ W)
    -- needed in addition to fundamental condition I
    (hcont : ∀ᵐ x ∂q, ContinuousOn (logDensityRatio p w₀ x) W)
    -- a resolution, a chart family of it and a subordinate partition of unity
    (R : SLTResolution (excessLoss q p w₀) φ W) (F : R.ChartFamily)
    (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hρ : ρ.IsSubordinate fun i ↦ (F.chart i).openCube) :
    let lam := R.rlct
    let m := R.mult
    let U := (α : F.Piece) × cube d α.radius
    -- the existence of `L` is [Wat09, Theorem 6.1]
    ∃ L : ResolvedLogDensityRatio 2 F q (logDensityRatio p w₀),
      let a : X → U → ℝ := fun x ⟨α, u⟩ ↦ L.a α x u
      ∀ (β : ℝ) (hβ : 0 < β)
        -- iid dataset drawn from q
        (Ω : Type*) [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
        [IsProbabilityMeasure P]
        (hXs : IsIIDSample q Xs P),
        -- the limit of the empirical process
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P'),
        ∃ E : EmpiricalProcessLimit q a Xs P P',
          let Zn0 := normalizedEvidence p w₀ W φ β Xs
          -- the book's limit process `ξ = −Ψ`, the sign of the standard form (6.10)
          let ξ := fun ω' ↦ -E.Ψlim ω'
          TendstoInDistribution
            (fun (n : ℕ) (ω : Ω) ↦
              (n : ℝ) ^ lam / log n ^ (m - 1) * Zn0 n ω)
            atTop (fun ω' ↦ F.limitFunctional β ρ (ξ ω')) (fun _ ↦ P) P' :=
  by
  classical
  have hK := hRFV.excessLoss_nonneg
  have hKc : ContinuousOn (excessLoss q p w₀) W := I.continuousOn_K
  have hφ0 : ∀ w ∈ W, 0 ≤ φ w := fun w hw ↦
    II.nonneg hw
  have hφc : ContinuousOn φ W := II.continuousOn
  obtain ⟨L⟩ := exists_resolvedLogDensityRatio q p W hW.isClosed φ 2 w₀ I hRFV hcont R F
  refine ⟨L, ?_⟩
  dsimp only
  intro β hβ Ω _ Xs P _ hXs
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  obtain ⟨Ω', mΩ', P', hP', ⟨E⟩⟩ := exists_empiricalProcessLimit le_rfl L Xs P hXs
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  refine ⟨Ω', mΩ', P', hP', E, ?_⟩
  rcases isEmpty_or_nonempty F.Piece with hF | hF
  · -- no pieces: `W` carries no mass near the zeros of `K`, `λ = m = 0` and `Y = 0`
    have hset : ∀ z ∈ R.resolvedParameterSet, excessLoss q p w₀ (R.π z) = 0 → False :=
      fun z hz hz0 ↦ isEmptyElim (F.nonempty_piece_of_mem_sublevel ⟨hz, by
        show excessLoss q p w₀ (R.π z) ≤ F.δ
        rw [hz0]
        exact F.δ_pos.le⟩).some
    have hl : R.rlct = 0 := by
      have : {l | ∃ z ∈ R.resolvedParameterSet, excessLoss q p w₀ (R.π z) = 0 ∧
          ∃ C : R.Chart z, C.rlct = l} = ∅ :=
        Set.eq_empty_of_forall_notMem fun l ⟨z, hz, hz0, _⟩ ↦ hset z hz hz0
      rw [SLTResolution.rlct, this, Real.sInf_empty]
    have hm : R.mult = 0 := by
      have : {m | ∃ z ∈ R.resolvedParameterSet, excessLoss q p w₀ (R.π z) = 0 ∧
          ∃ C : R.Chart z, C.rlct = R.rlct ∧ C.mult = m} = ∅ :=
        Set.eq_empty_of_forall_notMem fun m ⟨z, hz, hz0, _⟩ ↦ hset z hz hz0
      rw [SLTResolution.mult, this, csSup_empty]
      rfl
    have hY : ∀ χ, F.limitFunctional β ρ χ = 0 := fun χ ↦ by
      unfold SLTResolution.ChartFamily.limitFunctional
      exact finsum_of_isEmpty _
    obtain ⟨δ, hδ, hnull⟩ := F.exists_volume_sublevel_eq_zero hW hKc hK
    have hφi : IntegrableOn φ W := hφc.integrableOn_compact hW
    have hT := FundamentalConditionI.tendstoInMeasure_evidence_of_null_sublevel I hW
        (measurable_uncurry_logDensityRatio hp w₀)
      hcont hδ hnull hφ0 hφi hβ (fun i ↦ (hX i).measurable) (fun i ↦ (hX i).map_eq) hIndep
    have hfun : (fun (n : ℕ) (ω : Ω) ↦
          (n : ℝ) ^ R.rlct / log n ^ (R.mult - 1) * normalizedEvidence p w₀ W φ β Xs n ω)
        = fun (n : ℕ) ω ↦ ∫ w in W,
          exp (-(n * β * empiricalLoss (logDensityRatio p w₀) Xs n ω w)) * φ w := by
      funext n ω
      rw [hl, hm, Real.rpow_zero, Nat.zero_sub, pow_zero, div_one, one_mul]
      rfl
    have hmeas : ∀ n : ℕ, AEMeasurable (fun ω ↦ ∫ w in W,
        exp (-(n * β * empiricalLoss (logDensityRatio p w₀) Xs n ω w)) * φ w) P := by
      intro n
      have : AEStronglyMeasurable (fun z : Ω × (Fin d → ℝ) ↦
          exp (-(n * β * empiricalLoss (logDensityRatio p w₀) Xs n z.1 z.2)) * φ z.2)
          (P.prod (volume.restrict W)) :=
        (Real.measurable_exp.comp (measurable_const.mul (measurable_uncurry_empiricalLoss
          (measurable_uncurry_logDensityRatio hp w₀) (fun i ↦ (hX i).measurable) n)).neg
          ).aestronglyMeasurable.mul hφi.aestronglyMeasurable.comp_snd
      exact this.integral_prod_right'.aemeasurable
    have hD := hT.tendstoInDistribution hmeas
    rw [hfun]
    simp only [hY]
    refine ⟨hD.forall_aemeasurable, aemeasurable_const, ?_⟩
    convert hD.tendsto using 3
    have h0 : Measure.map (0 : Ω → ℝ) P = Measure.dirac 0 := by
      rw [show (0 : Ω → ℝ) = fun _ ↦ 0 from rfl, Measure.map_const, measure_univ, one_smul]
    simp only [Measure.map_const, measure_univ, one_smul, h0]
  · have : Nonempty R.M := ⟨F.centre (Classical.arbitrary F.Piece).chart⟩
    obtain ⟨hl, hm⟩ := F.rlct_eq_and_mult_eq ρ hρ hW hKc hK hφ0 hφc
    set A := SingularLearningTheory.SLTResolution.ChartFamily.toResolutionAtlas ρ hρ hW hKc hK
      hφc
    let LA : A.AnalyticResolvedLikelihood 2 q (logDensityRatio p w₀) :=
      L.toAnalyticResolvedLikelihood A id (fun _ ↦ rfl) (fun _ ↦ rfl)
        (fun α u hu ↦ α.extMap_eq (α.cube_subset_domain hu)) le_rfl
    have : ∀ α : F.Piece, CompactSpace (cube d α.radius) := fun α ↦
      isCompact_iff_compactSpace.mp isCompact_Icc
    have hf : (fun x (v : (α : F.Piece) × cube d α.radius) ↦ L.a v.1 x v.2)
        = fun x (u : (α : A.ι) × cube d (A.b α)) ↦ LA.a u.1 x u.2 := rfl
    let EA : EmpiricalProcessLimit q
        (fun x (u : (α : A.ι) × cube d (A.b α)) ↦ LA.a u.1 x u.2) Xs P P' :=
      hf ▸ E
    have h := tendstoInDistribution_normalizedEvidence_of_limit q p hp W hW φ w₀ I II hcont A
      (fun α _ ↦ A.exists_lipschitzOnWith_weight α) LA β hβ Xs P hXs P' EA
    rw [hl, hm]
    convert h using 2 with ω'
    rw [Y_eq_atlasY hl hm]
    congr 1

/-- **Free energy formula.** There are `λ > 0` and `m ≥ 1` such that for every `β > 0` and every
i.i.d. sample, `F_n = nβ L_n(w₀) + λ log n − (m − 1) log log n + R_n` almost surely for `n ≥ 2`,
where `R_n` converges in law.

Relation to the source.
* **Translation.** $n\beta L_n(w_0)$ replaces the book's $n\beta S_n$; the two agree when
  $q = p(\cdot \mid w_0)$.
* **Restatement.** $(\lambda, m)$ is the singularity type, defined by volume scaling, where the book
  has the largest pole of the zeta function and its order; the two agree by
  `zetaFunction_meromorphic_continuation`.
* **Formalisation note.** The limit of $R_n$ is left existential here. The library identifies it as
  $-\log Y(\xi)$, the $F^R(\xi)$ of Main Formula II, in
  `NondegenerateResolutionAtlas.free_energy_formula` ([Wat09, Main Theorem 6.2]), stated for its
  internal resolution atlas.

Source statement: [Wat09, Corollary 6.1(1)] -/
theorem free_energy_formula {d : ℕ} {X : Type*} [MeasurableSpace X]
    -- data distribution
    (q : Measure X) [IsProbabilityMeasure q]
    -- model, parameter space and reference parameter
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 2 q p W w₀)
    -- prior
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W) :
    ∃ (lam : ℝ) (m : ℕ),
      0 < lam ∧ 1 ≤ m ∧ IsSingularityType (excessLoss q p w₀) φ W lam m ∧
      ∀ (β : ℝ) (hβ : 0 < β)
        -- iid dataset drawn from q
        (Ω : Type*) [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
        [IsProbabilityMeasure P]
        (hXs : IsIIDSample q Xs P),
        let Fn := freeEnergy p W φ β Xs
        let Ln := fun (n : ℕ) (ω : Ω) ↦ empiricalNegativeLogLikelihood p Xs n ω w₀
        ∃ Rn : ℕ → Ω → ℝ,
          (∀ (n : ℕ) (hn : 2 ≤ n), ∀ᵐ ω ∂P,
            Fn n ω = n * β * Ln n ω + lam * log n
              - ((m : ℝ) - 1) * log (log n) + Rn n ω) ∧
          ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
            (_ : IsProbabilityMeasure P') (Rlim : Ω' → ℝ),
            TendstoInDistribution Rn atTop Rlim (fun _ ↦ P) P' := by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I, hcont⟩ := hA
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  have hK := hRFV.excessLoss_nonneg
  obtain ⟨C, hC, hRFV'⟩ := hRFV.exists_integral_sq_le_inv_mul
  obtain ⟨UK, hUK, hWUK, hKa⟩ := I.exists_analyticOnNhd_K
  obtain ⟨R⟩ := exists_nondegenerateResolutionAtlas hW II hUK hWUK
    hKa hK hw₀ (excessLoss_self q p w₀) hKg hφg hvol
  have hcontg : ∀ᵐ x ∂q, ∀ α,
      Continuous fun u : cube d (R.b α) ↦ logDensityRatio p w₀ x (R.g α u) := by
    filter_upwards [hcont] with x hx α
    exact hx.comp_continuous ((R.g_analytic α).continuousOn.comp_continuous continuous_subtype_val
      fun u ↦ u.2) fun u ↦ R.g_mapsTo α u.2
  have hf : LsValuedAnalytic 2 q (logDensityRatio p w₀) W :=
    I.ls_analytic
  obtain ⟨Lk⟩ := R.toResolutionAtlas.exists_analyticResolvedLikelihood I.two_le (fun _ ↦ rfl) hf hC
    hRFV' hcontg
  refine ⟨R.rlct, R.mult, R.toResolutionAtlas.rlct_pos, R.toResolutionAtlas.mult_pos,
    R.isSingularityType_of_continuousOn hW I.continuousOn_K (fun w hw ↦ II.nonneg hw)
      II.continuousOn, ?_⟩
  have hcast : ((R.mult - 1 : ℕ) : ℝ) = (R.mult : ℝ) - 1 :=
    Nat.cast_pred R.toResolutionAtlas.mult_pos
  intro β hβ Ω _ Xs P _ hXs
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hXl : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  obtain ⟨P₁, hP₁, ⟨E₀⟩⟩ :=
    Lk.exists_empiricalProcessLimit_chart hXm hXl hIndep
  obtain ⟨P₂, hP₂, ⟨T₀⟩⟩ := I.exists_tail_empiricalProcessLimit hW
    (fun w ↦ (measurable_uncurry_logDensityRatio hp w₀).comp
      (measurable_id.prodMk measurable_const)) hcont R.δ_pos hXm hXl hIndep
  obtain ⟨Rn, h1, h2⟩ := free_energy_formula_stochastic_of_inputs q p hp W hW hp_pos φ β hβ w₀
    hw₀ I II Xs P hX R (fun α _ ↦ R.toResolutionAtlas.exists_lipschitzOnWith_weight α) Lk.toResolvedLikelihood (P₁.prod P₂)
    E₀.prodFst
    (Lk.primaryLipschitzTight hXm hXl hIndep E₀.Ψ_ae_eq) T₀.prodSnd
  rw [hcast] at h1
  exact ⟨Rn, h1, _, inferInstance, P₁.prod P₂, inferInstance, _, h2⟩

/-- **Free energy formula in expectation.** If fundamental condition I holds with index `s = 4`,
then, with `λ`, `m` and `R_n` as in `free_energy_formula`, for all large `n` `E[F_n] = nβ L + λ log
n − (m − 1) log log n + E[R_n]`, where `L = E[L_n(w₀)]` and `E[R_n]` converges. `hL` (`log p(·|w₀)`
is q-integrable) makes `L` finite.

Relation to the source.
* **Translation.** $n\beta L$ with $L = L(w_0)$ replaces the book's $n\beta S$; the two agree when
  $q = p(\cdot \mid w_0)$.

Source statement: [Wat09, Corollary 6.1(2)] -/
theorem free_energy_formula_expectation {d : ℕ} {X : Type*} [MeasurableSpace X]
    -- data distribution
    (q : Measure X) [IsProbabilityMeasure q]
    -- model, parameter space and reference parameter
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 4 q p W w₀)
    (hL : Integrable (fun x ↦ log (p w₀ x)) q)
    -- prior
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W) :
    let L := expectedNegativeLogLikelihood q p w₀
    ∃ (lam : ℝ) (m : ℕ),
      0 < lam ∧ 1 ≤ m ∧ IsSingularityType (excessLoss q p w₀) φ W lam m ∧
      ∀ (β : ℝ) (hβ : 0 < β)
        -- iid dataset drawn from q
        (Ω : Type*) [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
        [IsProbabilityMeasure P]
        (hXs : IsIIDSample q Xs P),
        let Fn := freeEnergy p W φ β Xs
        let Ln := fun (n : ℕ) (ω : Ω) ↦ empiricalNegativeLogLikelihood p Xs n ω w₀
        ∃ Rn : ℕ → Ω → ℝ,
          (∀ (n : ℕ) (hn : 2 ≤ n), ∀ᵐ ω ∂P,
            Fn n ω = n * β * Ln n ω + lam * log n
              - ((m : ℝ) - 1) * log (log n) + Rn n ω) ∧
          (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
            (_ : IsProbabilityMeasure P') (Rlim : Ω' → ℝ),
            TendstoInDistribution Rn atTop Rlim (fun _ ↦ P) P') ∧
          (∀ᶠ n : ℕ in atTop,
            ∫ ω, Fn n ω ∂P = n * β * L + lam * log n
              - ((m : ℝ) - 1) * log (log n) + ∫ ω, Rn n ω ∂P) ∧
          ∃ ℓ : ℝ, Tendsto (fun n ↦ ∫ ω, Rn n ω ∂P) atTop (𝓝 ℓ) := by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I₄, hcont⟩ := hA
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  have I := FundamentalConditionI.monoExponent I₄ (t := 2) le_rfl (by norm_num)
  have hK := hRFV.excessLoss_nonneg
  obtain ⟨C, hC, hRFV'⟩ := hRFV.exists_integral_sq_le_inv_mul
  obtain ⟨UK, hUK, hWUK, hKa⟩ := I.exists_analyticOnNhd_K
  obtain ⟨R⟩ := exists_nondegenerateResolutionAtlas hW II hUK hWUK
    hKa hK hw₀ (excessLoss_self q p w₀) hKg hφg hvol
  have hcontg : ∀ᵐ x ∂q, ∀ α,
      Continuous fun u : cube d (R.b α) ↦ logDensityRatio p w₀ x (R.g α u) := by
    filter_upwards [hcont] with x hx α
    exact hx.comp_continuous ((R.g_analytic α).continuousOn.comp_continuous continuous_subtype_val
      fun u ↦ u.2) fun u ↦ R.g_mapsTo α u.2
  have hf : LsValuedAnalytic 4 q (logDensityRatio p w₀) W :=
    I₄.ls_analytic
  obtain ⟨Lk⟩ := R.toResolutionAtlas.exists_analyticResolvedLikelihood I₄.two_le (fun _ ↦ rfl) hf
    hC hRFV' hcontg
  refine ⟨R.rlct, R.mult, R.toResolutionAtlas.rlct_pos, R.toResolutionAtlas.mult_pos,
    R.isSingularityType_of_continuousOn hW I.continuousOn_K (fun w hw ↦ II.nonneg hw)
      II.continuousOn, ?_⟩
  have hcast : ((R.mult - 1 : ℕ) : ℝ) = (R.mult : ℝ) - 1 :=
    Nat.cast_pred R.toResolutionAtlas.mult_pos
  intro β hβ Ω _ Xs P _ hXs
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hXl : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  obtain ⟨P₁, hP₁, ⟨E₀⟩⟩ :=
    Lk.exists_empiricalProcessLimit_chart hXm hXl hIndep
  obtain ⟨P₂, hP₂, ⟨T₀⟩⟩ := I₄.exists_tail_empiricalProcessLimit hW
    (fun w ↦ (measurable_uncurry_logDensityRatio hp w₀).comp
      (measurable_id.prodMk measurable_const)) hcont R.δ_pos hXm hXl hIndep
  obtain ⟨Rn, h1, h2, h3, h4⟩ := free_energy_formula_expectation_of_inputs q p hp W hW hp_pos φ β
    hβ w₀ hw₀ hL I II Xs P hX R (fun α _ ↦ R.toResolutionAtlas.exists_lipschitzOnWith_weight α) Lk.toResolvedLikelihood
    (P₁.prod P₂)
    E₀.prodFst
    (Lk.primaryLipschitzTight hXm hXl hIndep E₀.Ψ_ae_eq) T₀.prodSnd
    (Lk.momentBound_chart hXm hXl hIndep E₀)
    (I₄.momentBound_tail hW hcont R.δ_pos hXm hXl hIndep T₀)
  rw [hcast] at h1 h2
  exact ⟨Rn, h1, ⟨_, inferInstance, P₁.prod P₂, inferInstance, _, h4⟩, h2, _, h3⟩

end SingularLearningTheory
