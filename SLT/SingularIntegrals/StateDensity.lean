/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import SLT.SingularIntegrals.Defs


/-!
# The state density function

Formalises the first section of [Hit26]'s singular-integrals chapter
([Hit26, Section 3.1]).

| Thesis | Lean |
| --- | --- |
| sublevel volume function `V(t; φ)` | `sublevelVolume` |
| state density function `ν(t; φ)` | `IsStateDensity` |
| [Hit26, Theorem 3.1.5] ([Wat09, Theorem 4.4]) | `integral_stateDensityMeasure`, |
| | `SingularLearningTheory.IsStateDensity.integral_mul` |

## The formalisation choice

[Hit26] defines the state density as the pointwise derivative
`ν(t; φ) = (d/dt) V(t; φ)`, which exists only away from the critical values of
`K` ([Hit26, Lemma 3.1.2], [Wat09, Theorem 4.3]).
Carrying a partially-defined derivative through every downstream calculation is
painful, and [Wat09, Theorem 4.4] is not really about the derivative: it is the statement
that integrating against `ν` is a change of variables along `K`.

So we take the measure-theoretic route. `stateDensityMeasure` is the pushforward
of `φ(w) dw|_W` along `K` — a measure on `ℝ` which always exists. `V(t; φ)` is
its cumulative distribution (`sublevelVolume_eq_stateDensityMeasure_Iic`), and a
function `ν` is *a* state density exactly when it is a density for that measure
(`IsStateDensity`). `IsStateDensity.sublevelVolume_eq` recovers [Hit26]'s
characterisation `V(t; φ) = ∫_{-∞}^t ν`, and
`IsStateDensity.hasDerivAt_sublevelVolume` recovers `ν = dV/dt` at the points
where [Hit26]'s `d/dt` exists.

This also sidesteps a specification hazard: Lean's Bochner integral is total, so
an unqualified integral identity can hold vacuously when the integrand is not
integrable. An identity between finite measures cannot.

[Wat09, Theorem 4.3] itself — the surface-integral formula
`ν(t; φ) = ∫_{K⁻¹(t)} φ(w)/‖∇K(w)‖ dσ(w)` — is not formalised: Mathlib has no
surface measure on the level sets of a smooth function. Nothing downstream uses
it. It is a pedagogical aside in [Hit26], and the free energy formula reaches
`ν` only through explicit normal-crossing computations ([Wat09, Theorem 4.6]).
-/

public section

open MeasureTheory Set

namespace SingularLearningTheory

variable {E : Type*} [MeasureSpace E] {K φ : E → ℝ} {W : Set E} {ν : ℝ → ℝ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pushforward of the weighted volume `φ(w) dw|_W` along `K`. [Hit26]'s
state density function `ν(t; φ)` is a Lebesgue density for this measure; see
`IsStateDensity`. -/
@[expose] noncomputable def stateDensityMeasure (K φ : E → ℝ) (W : Set E) : Measure ℝ :=
  Measure.map K ((volume.restrict W).withDensity fun w ↦ ENNReal.ofReal (φ w))

/-- `ν` is *the state density function* `ν(t; φ)` of `K` on `W`: a nonnegative
Lebesgue density for `stateDensityMeasure K φ W`.

[Hit26] defines `ν(t; φ) = (d/dt) V(t; φ)`; `IsStateDensity.sublevelVolume_eq`
and `IsStateDensity.hasDerivAt_sublevelVolume` show this predicate says exactly
that, without requiring `V` to be differentiable everywhere. -/
structure IsStateDensity (K φ : E → ℝ) (W : Set E) (ν : ℝ → ℝ) : Prop where
  measurable : Measurable ν
  nonneg : ∀ t, 0 ≤ ν t
  withDensity_eq :
    stateDensityMeasure K φ W = volume.withDensity fun t ↦ ENNReal.ofReal (ν t)

section Pushforward

/-- `V(t; φ)` is the cumulative distribution of the state density measure: the
thesis's `∫_W 𝟙(K w ≤ t) φ(w) dw` is the mass the pushforward puts on `(-∞, t]`. -/
theorem sublevelVolume_eq_stateDensityMeasure_Iic (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    (t : ℝ) :
    sublevelVolume K φ W t = (stateDensityMeasure K φ W (Iic t)).toReal := by
  have hmeas : MeasurableSet {w : E | K w ≤ t} := hK measurableSet_Iic
  rw [stateDensityMeasure, Measure.map_apply hK measurableSet_Iic,
    withDensity_apply _ (hK measurableSet_Iic), sublevelVolume,
    integral_indicator hmeas]
  exact integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hφ0)
    (hφ.restrict).aestronglyMeasurable

/-- [Hit26, Theorem 3.1.5] ([Wat09, Theorem 4.4]), in
pushforward form: integrating a function of the energy against the state density
measure is the same as integrating it over `W` against the weight `φ`.

[Hit26] writes this as `∫₀^∞ f(t) ν(t; φ) dt = ∫_W f(K(w)) φ(w) dw`; see
`IsStateDensity.integral_mul` for that form. -/
private theorem integral_stateDensityMeasure (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    {f : ℝ → F} (hf : AEStronglyMeasurable f (stateDensityMeasure K φ W)) :
    ∫ t, f t ∂(stateDensityMeasure K φ W) = ∫ w in W, φ w • f (K w) := by
  rw [stateDensityMeasure] at hf ⊢
  rw [integral_map hK.aemeasurable hf,
    integral_withDensity_eq_integral_toReal_smul₀
      (hφ.ennreal_ofReal) (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hφ0] with w hw
  rw [ENNReal.toReal_ofReal hw]

end Pushforward

section StateDensity

variable (h : IsStateDensity K φ W ν)
include h

/-- The state density measure is the Lebesgue measure weighted by `ν`, so
integration against it is integration against `ν(t) dt`. -/
theorem IsStateDensity.integral_eq (f : ℝ → F) :
    ∫ t, f t ∂(stateDensityMeasure K φ W) = ∫ t, ν t • f t := by
  rw [h.withDensity_eq,
    integral_withDensity_eq_integral_toReal_smul₀
      (h.measurable.ennreal_ofReal.aemeasurable)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  change (ENNReal.ofReal (ν t)).toReal • f t = ν t • f t
  rw [ENNReal.toReal_ofReal (h.nonneg t)]

/-- [Hit26, Theorem 3.1.5] ([Wat09, Theorem 4.4]) in the form
[Hit26] states it: `∫ f(t) ν(t; φ) dt = ∫_W f(K(w)) φ(w) dw`.

[Hit26] integrates over `(0, ∞)`; here the integral is over all of `ℝ`, which
is the same thing whenever `K ≥ 0` on `W`, since then `ν` vanishes off `[0, ∞)`. -/
private theorem integral_smul_isStateDensity (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    {f : ℝ → F} (hf : AEStronglyMeasurable f volume) :
    ∫ t, ν t • f t = ∫ w in W, φ w • f (K w) := by
  rw [← integral_stateDensityMeasure hK hφ hφ0 (h.withDensity_eq ▸ hf.mono_ac
      (withDensity_absolutelyContinuous _ _)),
    h.integral_eq f]

/-- [Hit26, Theorem 3.1.5] ([Wat09, Theorem 4.4]) for
real-valued `f`, in [Hit26]'s own notation. -/
theorem IsStateDensity.integral_mul (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume) :
    ∫ t, f t * ν t = ∫ w in W, f (K w) * φ w := by
  simpa [mul_comm] using integral_smul_isStateDensity h hK hφ hφ0 hf

/-- When `K ≥ 0` on `W` the state density vanishes on the negative axis, so the
integrals above may be taken over `(0, ∞)` as [Hit26] writes them. -/
theorem IsStateDensity.ae_eq_zero_of_nonneg (hK : Measurable K)
    (hK0 : ∀ w ∈ W, 0 ≤ K w) : ν =ᵐ[volume.restrict (Iio 0)] 0 := by
  have hmass : (volume.withDensity fun t ↦ ENNReal.ofReal (ν t)) (Iio 0) = 0 := by
    rw [← h.withDensity_eq, stateDensityMeasure,
      Measure.map_apply hK measurableSet_Iio, withDensity_apply _ (hK measurableSet_Iio),
      Measure.restrict_restrict (hK measurableSet_Iio),
      show K ⁻¹' Iio 0 ∩ W = (∅ : Set E) from
        eq_empty_of_forall_notMem fun w hw ↦ absurd hw.1 (not_lt.mpr (hK0 w hw.2))]
    simp
  rw [withDensity_apply _ measurableSet_Iio,
    lintegral_eq_zero_iff h.measurable.ennreal_ofReal] at hmass
  filter_upwards [hmass] with t ht
  exact le_antisymm (by simpa [ENNReal.ofReal_eq_zero] using ht) (h.nonneg t)

/-- [Wat09, Theorem 4.4] with the region of integration `(0, ∞)` exactly as [Hit26]
writes it, for Banach-space-valued `f`. -/
theorem IsStateDensity.setIntegral_smul (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    (hK0 : ∀ w ∈ W, 0 ≤ K w) {f : ℝ → F} (hf : AEStronglyMeasurable f volume)
    (hfν : Integrable (fun t ↦ ν t • f t)) :
    ∫ t in Ioi 0, ν t • f t = ∫ w in W, φ w • f (K w) := by
  rw [← integral_smul_isStateDensity h hK hφ hφ0 hf,
    ← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hfν, compl_Ioi]
  have : ∫ t in Iic 0, ν t • f t = 0 := by
    rw [← MeasureTheory.restrict_Iio_eq_restrict_Iic]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h.ae_eq_zero_of_nonneg hK hK0] with t ht
    simp [ht]
  rw [this, add_zero]

/-- [Hit26]'s `∫₀^∞ f(t) ν(t; φ) dt = ∫_W f(K(w)) φ(w) dw`, with the region of
integration exactly as [Hit26] writes it. -/
theorem IsStateDensity.setIntegral_mul (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    (hK0 : ∀ w ∈ W, 0 ≤ K w) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hfν : Integrable (fun t ↦ f t * ν t)) :
    ∫ t in Ioi 0, f t * ν t = ∫ w in W, f (K w) * φ w := by
  simpa [mul_comm] using IsStateDensity.setIntegral_smul h hK hφ hφ0 hK0 hf
    (by simpa [mul_comm] using hfν)

/-- [Hit26]'s defining property of the state density, integrated: `V(t; φ)` is
the integral of `ν` over `(-∞, t]`. Together with
`IsStateDensity.hasDerivAt_sublevelVolume` this is the statement that
`ν = dV/dt`. -/
theorem IsStateDensity.sublevelVolume_eq (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    (t : ℝ) :
    sublevelVolume K φ W t = ∫ s in Iic t, ν s := by
  rw [sublevelVolume_eq_stateDensityMeasure_Iic hK hφ hφ0, h.withDensity_eq,
    withDensity_apply _ measurableSet_Iic]
  exact (integral_eq_lintegral_of_nonneg_ae (.of_forall h.nonneg)
    h.measurable.aestronglyMeasurable).symm

/-- [Hit26]'s definition `ν(t; φ) = (d/dt) V(t; φ)`, recovered: wherever `ν` is
continuous, it is the derivative of the sublevel volume function. Together with
`IsStateDensity.sublevelVolume_eq` this justifies reading `IsStateDensity` as
"`ν` is the state density function of `K`".

The integrability hypothesis `hint` says each sublevel set has finite `φ`-volume,
which holds in [Hit26]'s setting since `W` is compact and `φ` is continuous. -/
theorem IsStateDensity.hasDerivAt_sublevelVolume (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    (hint : ∀ u, IntegrableOn ν (Iic u)) {t : ℝ} (hνt : ContinuousAt ν t) :
    HasDerivAt (sublevelVolume K φ W) (ν t) t := by
  have key : sublevelVolume K φ W
      = fun u ↦ (∫ s in Iic (t - 1), ν s) + ∫ s in (t - 1)..u, ν s := by
    funext u
    rw [h.sublevelVolume_eq hK hφ hφ0 u, ← intervalIntegral.integral_Iic_sub_Iic
      (hint (t - 1)) (hint u)]
    ring
  have hsub : uIoc (t - 1) t ⊆ Iic t := by
    rw [uIoc_of_le (by linarith)]; exact fun _ hx ↦ hx.2
  rw [key]
  simpa using intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_iff.mpr ((hint t).mono_set hsub))
    h.measurable.stronglyMeasurable.stronglyMeasurableAtFilter hνt

end StateDensity

end SingularLearningTheory
