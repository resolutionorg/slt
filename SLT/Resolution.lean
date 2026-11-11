/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.PieceTransport
public import SLT.SingularIntegrals.SingularityType
import SLT.Resolution.PieceAtlas
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
import Mathlib.Topology.Sheaves.Init
public import SLT.StandardForm.FundamentalConditionI
public import SLT.Resolution.Components
public import SLT.Resolution.MonomialChart
public import SLT.Resolution.Orthant
public import SLT.Resolution.Outer
import SLT.Resolution.Factorisation
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Algebra.Ring.IsFormallyReal
import Std.Tactic.BVDecide.Normalize.Prop
public import SLT.Resolution.Defs

/-!
# Resolution of singularities

The theorems of `SLTChallenge/Resolution.lean`, proved from the library. Its definitions are in
`SLT/Resolution/Defs.lean`.

`exists_sltResolution` resolves `F = K φ₂ ∏ H_i` over `U' = U ∩ U₀`, where the `H_i ≥ 0` cut
out `W` on the open `U₀` and are normalised to have nonzero germs on `U₀`
(`exists_normalized_semianalytic`): one resolution per connected component, glued
(`exists_resolution_of_nonzero_germs`). The exceptional set is the zero set of `F` in `U'`,
null by `Resolution.volume_zeroSet_eq_zero`; off it the resolution is a local diffeomorphism
(`Resolution.isLocalDiffeomorphOn`). Each chart is a `MonomialChart` restricted
to its box neighbourhood `O` (`MonomialChart.nonempty_sltChart`): `K ≥ 0` makes the loss
`u^{2k}` (`MonomialChart.S₀_eq_one_and_even_of_nonneg`), the prior density over `W` is
`φ₁ |a_φ| |b_J| · |u^{r + p}|`, and on an open orthant each `H_i ∘ π = c_i u^{k^i}` has one sign
(`MonomialChart.H_pos_or_neg`), so the orthant lies over the open set `{H_i > 0 ∀ i} ⊆ W` or
over the complement of `W`.

The learning coefficient and multiplicity of a resolution are those of the atlas of the pieces of
any chart family (`SLTResolution.ChartFamily.rlct_eq_and_mult_eq`): the atlas of a family, with a
partition of unity positive at the centre of an essential chart, is nondegenerate and its `(λ, m)`
is the singularity type (`ChartFamily.exists_isSingularityType`); adding any chart of the resolution
at a point of `W̃` over a zero of `K` gives another family with the same type, so that chart's `λ`
is at least the family's, and its `m` at most the family's when the `λ` agree.

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 3.3.1], global form | `exists_sltResolution` |
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

namespace SingularLearningTheory

variable {d : ℕ}

open scoped Manifold ContDiff

/-! ## Signs on open orthants -/

section Orthants

variable {r : ℝ} {s : Fin d → Bool} {u : Fin d → ℝ}

private theorem mem_box_of_mem_openOrthant (hu : u ∈ openOrthant r s) : u ∈ box d r :=
  mem_box.2 fun j ↦ abs_le.mp (hu j).1

/-- On the open orthant `s`, a monomial is its sign `∏ ε_j^{k_j}` times `∏ |u_j|^{k_j}`.
Supports `MonomialChart.H_pos_or_neg`. -/
private theorem prod_pow_eq_of_mem_openOrthant (hu : u ∈ openOrthant r s) (k : Fin d → ℕ) :
    ∏ j, u j ^ k j = (∏ j, orthantSign s j ^ k j) * ∏ j, |u j| ^ k j := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [← mul_pow]
  congr 1
  have h := (hu j).2
  unfold orthantSign
  split_ifs at h ⊢
  · rw [abs_of_pos h, one_mul]
  · rw [abs_of_neg (neg_pos.mp h), neg_one_mul, neg_neg]

end Orthants

/-- A continuous function without zeros on a preconnected set has one sign there. Supports
`MonomialChart.H_pos_or_neg`. -/
private theorem pos_or_neg_of_isPreconnected {X : Type*} [TopologicalSpace X] {s : Set X}
    {f : X → ℝ}
    (hs : IsPreconnected s) (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    (∀ x ∈ s, 0 < f x) ∨ ∀ x ∈ s, f x < 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩ := hcon
  obtain ⟨x, hx, hfx⟩ := hs.intermediate_value ha hb hf ⟨hfa, hfb⟩
  exact h0 x hx hfx

namespace MonomialChart

variable {N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  {K φ₂ : (Fin d → ℝ) → ℝ} {H : Fin N → (Fin d → ℝ) → ℝ} {g : M → (Fin d → ℝ)} {z : M}
  (c : MonomialChart K φ₂ H g z)

/-- On each open orthant of the box, `H_i ∘ g = c_i u^{k^i}` has one sign: `c_i` is a unit on the
connected box and the monomial has the sign `∏ ε_j^{k^i_j}`. Supports
`SLTChart.orthant_dichotomy`. -/
theorem H_pos_or_neg (i : Fin N) (s : Fin d → Bool) :
    (∀ u ∈ openOrthant c.b s, 0 < H i (g (c.e.symm u))) ∨
      ∀ u ∈ openOrthant c.b s, H i (g (c.e.symm u)) < 0 := by
  set τ := ∏ j, orthantSign s j ^ c.kH i j
  have hτ : τ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (orthantSign_ne_zero s j)
  have hbox : IsPreconnected (box d c.b) := (convex_Icc _ _).isPreconnected
  have hc := pos_or_neg_of_isPreconnected hbox
    ((c.cH_analytic i).continuousOn.mono c.box_subset) fun v hv ↦ c.cH_ne i v (c.box_subset hv)
  have hform : ∀ u ∈ openOrthant c.b s,
      H i (g (c.e.symm u)) = c.cH i u * τ * ∏ j, |u j| ^ c.kH i j := by
    intro u hu
    rw [c.H_eq i u (c.box_subset (mem_box_of_mem_openOrthant hu)),
      prod_pow_eq_of_mem_openOrthant hu, mul_assoc]
  have hP : ∀ u ∈ openOrthant c.b s, 0 < ∏ j, |u j| ^ c.kH i j := fun u hu ↦
    Finset.prod_pos fun j _ ↦ pow_pos (abs_pos.mpr (ne_zero_of_mem_openOrthant hu j)) _
  have hb : ∀ u ∈ openOrthant c.b s, u ∈ box d c.b := fun u hu ↦ mem_box_of_mem_openOrthant hu
  rcases hc with hc | hc <;> rcases hτ.lt_or_gt with hτ' | hτ'
  · refine Or.inr fun u hu ↦ ?_
    rw [hform u hu]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (hc u (hb u hu)) hτ') (hP u hu)
  · refine Or.inl fun u hu ↦ ?_
    rw [hform u hu]
    exact mul_pos (mul_pos (hc u (hb u hu)) hτ') (hP u hu)
  · refine Or.inl fun u hu ↦ ?_
    rw [hform u hu]
    exact mul_pos (mul_pos_of_neg_of_neg (hc u (hb u hu)) hτ') (hP u hu)
  · refine Or.inr fun u hu ↦ ?_
    rw [hform u hu]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (hc u (hb u hu)) hτ') (hP u hu)

/-- A monomial chart of an analytic `π` with `K ∘ π ≥ 0`, restricted to its box neighbourhood
`O` (`eO`), is an `SLTChart`: radius `b`, `k = q / 2`, `h = r + p` and density unit
`φ₁ |a_φ| |b_J|`. The orthant condition needs only that `{H_i > 0 ∀ i}` lies in the interior of
`W` and `{H_i < 0}` outside `W` along `π`. Supports `exists_sltResolution`. -/
theorem nonempty_sltChart {φ φ₁ : (Fin d → ℝ) → ℝ}
    {W U : Set (Fin d → ℝ)} (c : MonomialChart K φ₂ H g z)
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) (hU : IsOpen U) (hgU : ∀ x, g x ∈ U)
    (hK₀ : ∀ x, 0 ≤ K (g x)) (hφ₁ : ContDiffOn ℝ ∞ φ₁ U) (hφ₁₀ : ∀ w ∈ U, 0 < φ₁ w)
    (hφ₂₀ : ∀ w ∈ W, 0 ≤ φ₂ w) (hφ : ∀ w ∈ U, φ w = φ₁ w * φ₂ w)
    (hint : ∀ x, (∀ i, 0 < H i (g x)) → g x ∈ interior W)
    (hout : ∀ x i, H i (g x) < 0 → g x ∉ W) :
    Nonempty (SLTChart g K φ W z) := by
  obtain ⟨hS, hq⟩ := c.S₀_eq_one_and_even_of_nonneg fun _ _ ↦ hK₀ _
  have hG := analyticOnNhd_comp_symm_of_mem_maximalAtlas hg c.he
  refine ⟨{ extension := c.eO
            extension_mem := c.eO_mem_maximalAtlas
            mem_source := c.mem_eO_source.mpr ⟨c.mem_source, c.e_P ▸ c.zero_mem_O⟩
            centered := c.e_P
            radius := c.b
            radius_pos := c.b_pos
            box_subset := by rw [c.eO_target]; exact c.box_subset
            k := fun j ↦ c.q j / 2
            active := ?_
            loss_eq := fun u hu ↦ ?_
            h := c.r + c.p
            densityUnit := fun u ↦ φ₁ (g (c.e.symm u)) * |c.aφ u| * |c.bJ u|
            densityUnit_contDiffOn := ?_
            densityUnit_pos := fun u hu ↦ ?_
            density_eq := fun u hu hW ↦ ?_
            orthant_dichotomy := fun s ↦ ?_ }⟩
  · obtain ⟨j, hj⟩ := c.q_ne
    exact ⟨j, by have := Nat.two_mul_div_two_of_even (hq j); omega⟩
  · rw [c.eO_symm_apply, c.K_eq u (c.eO_target ▸ hu), hS, one_mul]
    exact Finset.prod_congr rfl fun j _ ↦ by rw [Nat.two_mul_div_two_of_even (hq j)]
  · rw [c.eO_target]
    intro u hu
    refine ContDiffAt.contDiffWithinAt ?_
    have h1 : ContDiffAt ℝ ∞ (fun u ↦ φ₁ (g (c.e.symm u))) u :=
      (hφ₁.contDiffAt (hU.mem_nhds (hgU _))).comp u (hG u (c.O_subset hu)).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun u ↦ |c.aφ u|) u :=
      (contDiffAt_abs (c.aφ_ne u hu)).comp u (c.aφ_analytic u hu).contDiffAt
    have h3 : ContDiffAt ℝ ∞ (fun u ↦ |c.bJ u|) u :=
      (contDiffAt_abs (c.bJ_ne u hu)).comp u (c.bJ_analytic u hu).contDiffAt
    exact (h1.mul h2).mul h3
  · rw [c.eO_target] at hu
    exact mul_pos (mul_pos (hφ₁₀ _ (hgU _)) (abs_pos.mpr (c.aφ_ne u hu)))
      (abs_pos.mpr (c.bJ_ne u hu))
  · rw [c.eO_target] at hu
    change φ (g (c.e.symm u)) * |(fderiv ℝ (g ∘ c.e.symm) u).det|
      = φ₁ (g (c.e.symm u)) * |c.aφ u| * |c.bJ u| * |∏ j, u j ^ (c.r + c.p) j|
    have hφ₂nn : 0 ≤ φ₂ (g (c.e.symm u)) := hφ₂₀ _ hW
    rw [c.φ₂_eq u hu] at hφ₂nn
    rw [hφ _ (hgU _), c.φ₂_eq u hu, c.det_eq u hu, ← abs_of_nonneg hφ₂nn]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, abs_mul]
    ring
  · by_cases hall : ∀ i, ∀ u ∈ openOrthant c.b s, 0 < H i (g (c.e.symm u))
    · exact Or.inl fun u hu ↦ hint _ fun i ↦ hall i u hu
    · push Not at hall
      obtain ⟨i, u₀, hu₀, hle⟩ := hall
      have hneg := (c.H_pos_or_neg i s).resolve_left fun h ↦ (h u₀ hu₀).not_ge hle
      exact Or.inr fun u hu ↦ hout _ i (hneg u hu)

end MonomialChart

/-! ## Existence -/

/-- **Resolution of singularities**, in the global form of `SLTResolution`. Hypotheses: `W` is
semianalytic; `K` is analytic and nonnegative on an open `U ⊇ W` and not identically zero near any
point of `U`; and on `U` the prior factors as `φ = φ₁ φ₂` with `φ₁ > 0` smooth and `φ₂` analytic,
nonnegative on `W` and not identically zero near any point of `U`. The resolution is over an open
neighbourhood of `W` inside `U`, which is smaller than `U` when the semianalytic presentation of `W`
is given on a smaller open set.

Relation to the source.
* **Strengthening.** [Wat09, Theorem 2.8] is local, near a common zero of the functions; here the
  resolution is over an open neighbourhood of $W$, with a chart around every point over a zero of
  $K$ in $W$, as in Atiyah's form of the theorem.
* **Interpretation.** The book's hypothesis that each function vanishes at the point and is not
  constant is read, for a resolution over all of $U$, as `K` and `φ₂` not identically zero near any
  point of $U$.
* **Interpretation.** The prior and the Jacobian determinant are recorded only through their product
  on $W$, the functions cutting out $W$ only through the orthant condition, and the charts are
  centred cubes $[-r, r]^d$.

Source statement: [Wat09, Theorem 2.8] -/
theorem exists_sltResolution {d : ℕ} {K φ φ₁ φ₂ : (Fin d → ℝ) → ℝ} {W U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hWU : W ⊆ U) (hW : Semianalytic W)
    (hK : AnalyticOnNhd ℝ K U) (hK₀ : ∀ w ∈ U, 0 ≤ K w)
    (hKg : ∀ w ∈ U, ¬ K =ᶠ[𝓝 w] 0)
    (hφ₁ : ContDiffOn ℝ ∞ φ₁ U) (hφ₁₀ : ∀ w ∈ U, 0 < φ₁ w)
    (hφ₂ : AnalyticOnNhd ℝ φ₂ U) (hφ₂₀ : ∀ w ∈ W, 0 ≤ φ₂ w)
    (hφ₂g : ∀ w ∈ U, ¬ φ₂ =ᶠ[𝓝 w] 0)
    (hφ : ∀ w ∈ U, φ w = φ₁ w * φ₂ w) :
    ∃ R : SLTResolution K φ W, R.U ⊆ U := by
  classical
  obtain ⟨U₀, N, H₀, hU₀, hWU₀, hH₀, hW_eq⟩ := hW
  obtain ⟨H, hHa, hHg, hHW⟩ := exists_normalized_semianalytic hU₀ hH₀
  set U' := U ∩ U₀ with hU'def
  have hU'o : IsOpen U' := hU.inter hU₀
  have hWU' : W ⊆ U' := fun w hw ↦ ⟨hWU hw, hWU₀ hw⟩
  have hU'U : U' ⊆ U := inter_subset_left
  have hWH : ∀ w ∈ U', (w ∈ W ↔ ∀ i, 0 ≤ H i w) := fun w hw ↦
    (hW_eq w hw.2).trans (hHW w hw.2)
  -- the function to resolve, with nonzero germs on `U'`
  set F : (Fin d → ℝ) → ℝ := fun w ↦ K w * φ₂ w * ∏ i, H i w with hFdef
  have hHprod : ∀ w ∈ U', AnalyticAt ℝ (fun w ↦ ∏ i, H i w) w := fun w hw ↦
    Finset.analyticAt_fun_prod _ fun i _ ↦ hHa i w hw.2
  have hFa : AnalyticOnNhd ℝ F U' := fun w hw ↦
    ((hK w hw.1).mul (hφ₂ w hw.1)).mul (hHprod w hw)
  have hFg : ∀ w ∈ U', ¬ (F =ᶠ[𝓝 w] 0) := by
    intro w hw hF0
    rcases ((hK w hw.1).mul (hφ₂ w hw.1)).eventuallyEq_zero_or_of_mul (hHprod w hw) hF0 with
      h | h
    · rcases (hK w hw.1).eventuallyEq_zero_or_of_mul (hφ₂ w hw.1) h with h | h
      · exact hKg w hw.1 h
      · exact hφ₂g w hw.1 h
    · obtain ⟨i, -, hi⟩ := Finset.eventuallyEq_zero_of_prod Finset.univ (fun i _ ↦ hHa i w hw.2) h
      exact hHg i w hw.2 hi
  -- the open set `{H_i > 0 ∀ i}` lies in the interior of `W`
  have hpos : ∀ w ∈ U', (∀ i, 0 < H i w) → w ∈ interior W := by
    intro w hw hHw
    have hG : IsOpen (U' ∩ ⋂ i, (U' ∩ H i ⁻¹' Ioi 0)) :=
      hU'o.inter (isOpen_iInter_of_finite fun i ↦
        ((hHa i).continuousOn.mono inter_subset_right).isOpen_inter_preimage hU'o isOpen_Ioi)
    refine interior_maximal (fun v hv ↦ ?_) hG ⟨hw, mem_iInter.mpr fun i ↦ ⟨hw, hHw i⟩⟩
    exact (hWH v hv.1).mpr fun i ↦ (mem_iInter.mp hv.2 i).2.le
  obtain ⟨R, hRU⟩ := exists_resolution_of_nonzero_germs hU'o hFa hFg
  have hRU' : R.U ⊆ U := by rw [hRU]; exact hU'U
  have hRU₀ : R.U ⊆ U₀ := by rw [hRU]; exact inter_subset_right
  let _ : MeasurableSpace R.M := borel R.M
  have : BorelSpace R.M := ⟨rfl⟩
  have hπU : ∀ x, R.π x ∈ U' := fun x ↦ hRU ▸ R.mem_U x
  have hpre : R.π ⁻¹' {w | w ∈ U' ∧ F w = 0}ᶜ = R.π ⁻¹' {w | F w ≠ 0} := by
    ext x
    simp [hπU x]
  have hdiff : U' \ {w | w ∈ U' ∧ F w = 0} = R.U \ {w | F w = 0} := by
    ext w
    simp only [hRU, Set.mem_sdiff, mem_ofPred_eq, not_and]
    exact ⟨fun h ↦ ⟨h.1, h.2 h.1⟩, fun h ↦ ⟨h.1, fun _ ↦ h.2⟩⟩
  refine ⟨{ U := U'
            isOpen_U := hU'o
            W_subset_U := hWU'
            M := R.M
            π := R.π
            analytic_π := R.analytic_π
            range_π := R.range_π.trans hRU
            proper := hRU ▸ R.proper
            exceptional := {w | w ∈ U' ∧ F w = 0}
            volume_exceptional := hRU ▸ R.volume_zeroSet_eq_zero
            zeros_subset_exceptional := fun w hw ↦ ⟨hw.1, by simp [F, hw.2]⟩
            bijOn_off_exceptional := ?_
            isLocalDiffeomorphOn_off_exceptional := ?_
            charts := fun z hzW hz0 ↦ ?_ }, hU'U⟩
  · rw [hpre, hdiff]
    exact R.bijOn
  · rw [hpre]
    exact R.isLocalDiffeomorphOn
  · obtain ⟨c⟩ := R.exists_monomialChart (fun _ _ ↦ rfl) (hK.mono hRU') (hφ₂.mono hRU')
      (fun i ↦ (hHa i).mono hRU₀) hz0
    exact c.nonempty_sltChart R.analytic_π hU (fun x ↦ hU'U (hπU x))
      (fun x ↦ hK₀ _ (hU'U (hπU x))) hφ₁ hφ₁₀ hφ₂₀ hφ
      (fun x hx ↦ hpos _ (hπU x) hx)
      (fun x i hx hxW ↦ ((hWH _ (hπU x)).mp hxW i).not_gt hx)

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

section Identification

open SLTResolution SLTResolution.ChartFamily

variable {R : SLTResolution K φ W} {F : R.ChartFamily}
  {ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel}
  {hρ : ρ.IsSubordinate fun i ↦ (F.chart i).openCube} {hW : IsCompact W}
  {hKc : ContinuousOn K W} {hK : ∀ w ∈ W, 0 ≤ K w} {hφc : ContinuousOn φ W}

/-- The learning coefficient of a chart of the atlas of the pieces is that of its chart. -/
theorem SLTResolution.ChartFamily.toResolutionAtlas_chartRlct [Nonempty R.M] [Nonempty F.Piece]
    (α : F.Piece) :
    (toResolutionAtlas ρ hρ hW hKc hK hφc).chartRlct α = (F.chart α.chart).rlct :=
  rfl

/-- The multiplicity of a chart of the atlas of the pieces is that of its chart. -/
theorem SLTResolution.ChartFamily.toResolutionAtlas_chartMult [Nonempty R.M] [Nonempty F.Piece]
    (α : F.Piece) :
    (toResolutionAtlas ρ hρ hW hKc hK hφc).chartMult α = (F.chart α.chart).mult :=
  rfl

end Identification

open SLTResolution SLTResolution.ChartFamily in
/-- **The learning coefficient and multiplicity of a resolution** are those of the atlas of the
pieces of any chart family with a piece. -/
theorem SLTResolution.ChartFamily.rlct_eq_and_mult_eq {R : SLTResolution K φ W} (F : R.ChartFamily)
    [Nonempty R.M] [Nonempty F.Piece]
    (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hρ : ρ.IsSubordinate fun i ↦ (F.chart i).openCube) (hW : IsCompact W)
    (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφc : ContinuousOn φ W) :
    R.rlct = (toResolutionAtlas ρ hρ hW hKc hK hφc).rlct ∧
      R.mult = (toResolutionAtlas ρ hρ hW hKc hK hφc).mult := by
  classical
  set A := toResolutionAtlas ρ hρ hW hKc hK hφc
  obtain ⟨ρ₁, hρ₁, hT⟩ := F.exists_isSingularityType hW hKc hK hφ hφc
  -- every chart at a point of `W̃` over a zero is no better than the family
  have hcmp : ∀ z ∈ R.resolvedParameterSet, K (R.π z) = 0 → ∀ C : R.Chart z,
      A.rlct ≤ C.rlct ∧ (C.rlct = A.rlct → C.mult ≤ A.mult) := by
    intro z hz hz0 C
    set F' := F.insert C
    have : Nonempty F'.Piece := ⟨Piece.toInsert C (Classical.arbitrary F.Piece)⟩
    obtain ⟨ρ', hρ', hT'⟩ := F'.exists_isSingularityType hW hKc hK hφ hφc
    set A' := toResolutionAtlas ρ' hρ' hW hKc hK hφc
    obtain ⟨hl, hm⟩ := hT'.unique hT
    obtain ⟨s, hs, -⟩ := R.exists_admissible_of_mem C hz C.mem_openCube
    set β : F'.Piece := insertPiece C hs
    have hβr : A'.chartRlct β = C.rlct := rfl
    have hβm : A'.chartMult β = C.mult :=
      SLTResolution.ChartFamily.toResolutionAtlas_chartMult (ρ := ρ') (hρ := hρ') β
    have hle : A'.rlct ≤ C.rlct := hβr ▸ Finset.inf'_le _ (Finset.mem_univ β)
    refine ⟨hl ▸ hle, fun hCeq ↦ ?_⟩
    have hmin : β ∈ A'.minimalCharts := Finset.mem_filter.mpr
      ⟨Finset.mem_univ β, by rw [hβr, hCeq]; exact hl.symm⟩
    rw [← hβm]
    exact hm ▸ Finset.le_sup' A'.chartMult hmin
  -- an essential piece of the family
  obtain ⟨α, hα, hαeq⟩ := Finset.exists_mem_eq_sup'
    (ResolutionAtlas.minimalCharts_nonempty A) A.chartMult
  have hαr : (F.chart α.chart).rlct = A.rlct := (Finset.mem_filter.mp hα).2
  have hαm : (F.chart α.chart).mult = A.mult := by
    rw [← toResolutionAtlas_chartMult (ρ := ρ) (hρ := hρ) α, ResolutionAtlas.mult, hαeq]
  have hcz : F.centre α.chart ∈ R.resolvedParameterSet :=
    R.center_mem_resolvedParameterSet _ α.admissible
  have hcz0 : K (R.π (F.centre α.chart)) = 0 := (F.chart α.chart).loss_center
  have hrlct : R.rlct = A.rlct := by
    refine IsLeast.csInf_eq ⟨⟨_, hcz, hcz0, F.chart α.chart, hαr⟩, ?_⟩
    rintro l ⟨z, hz, hz0, C, rfl⟩
    exact (hcmp z hz hz0 C).1
  refine ⟨hrlct, IsGreatest.csSup_eq ⟨⟨_, hcz, hcz0, F.chart α.chart, hαr.trans hrlct.symm, hαm⟩,
    ?_⟩⟩
  rintro m ⟨z, hz, hz0, C, hCr, rfl⟩
  exact (hcmp z hz hz0 C).2 (hCr.trans hrlct)

/-- Every resolution of `K ≥ 0` over a compact `W` has a finite chart family: finitely many of
its charts cover a sublevel of `K` in the resolved parameter set, as in the local coordinates of
[Wat09, Theorem 6.5]. `hK` is needed: `K ∘ π = u^{2k} ≥ 0` on every chart cube, so no chart covers
a point of `W̃` where `K < 0`.

Relation to the source.
* **Strengthening.** Every resolution of $K$ has a chart family, not only the resolution of
  $K(\varepsilon - K)\varphi_2 \prod_j \pi_j$ that [Wat09, Theorem 6.5] constructs.
* **Correction.** [Wat09, Theorem 6.5] is printed for an arbitrary $\varepsilon > 0$, which can
  fail: at a critical point $x$ of $K$ with $0 < K(x) \le \varepsilon$ no chart has
  $K \circ g = u^{2k}$ with $k \ne 0$ near a preimage of $x$. The family covers the sublevel
  $\{K \le \delta\}$ for some $\delta > 0$, as in [Wat09, Remark 6.1 (1)], "for a sufficiently small
  constant".
* **Formalisation note.** The unit of a chart is smooth and positive on the chart's target, which
  contains the closed cube, so it is bounded below on every piece ([Wat09, Theorem 6.5 (3)]). -/
theorem SLTResolution.exists_chartFamily
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (R : SLTResolution K φ W) (hW : IsCompact W)
    (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w) : Nonempty R.ChartFamily :=
  R.exists_chartFamily' hW hKc hK

/-- Every chart family has a smooth partition of unity on the resolving manifold, subordinate to
its open cubes and summing to one on the sublevel it covers: the partition of unity of [Wat09,
Theorem 6.5(4)].

Relation to the source.
* **Gap.** The change of variables of the prior along the pieces and the bounds (6.14) of [Wat09,
  Theorem 6.5 (4)] are not stated. -/
theorem SLTResolution.ChartFamily.exists_partitionOfUnity
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {R : SLTResolution K φ W}
    (F : R.ChartFamily) (hW : IsCompact W) (hKc : ContinuousOn K W) :
    ∃ ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel,
      ρ.IsSubordinate fun i ↦ (F.chart i).openCube :=
  F.exists_partitionOfUnity' hW.isClosed hKc

/-- [Wat09, Definition 6.4], eqs. (6.16) and (6.17): the learning coefficient and multiplicity read
off any resolution are the singularity type of `K` and `φ` on `W`. `hvol` (every sublevel `{K < ε}`
has positive prior mass) rules out a resolution whose resolved parameter set misses the zeros of
`K`.

Relation to the source.
* **Strengthening.** [Wat09, Definition 6.4] reads $(\lambda, m)$ off the local coordinates of
  Theorem 6.5; here the pair read off any resolution is the singularity type, which
  `zetaFunction_meromorphic_continuation` identifies with the largest pole of the zeta function and
  its order. -/
theorem SLTResolution.isSingularityType
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (R : SLTResolution K φ W) (hW : IsCompact W)
    (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφc : ContinuousOn φ W)
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)) :
    IsSingularityType K φ W R.rlct R.mult := by
  obtain ⟨F⟩ := R.exists_chartFamily' hW hKc hK
  rcases isEmpty_or_nonempty F.Piece with hF | hF
  · obtain ⟨δ, hδ, hnull⟩ := F.exists_volume_sublevel_eq_zero hW hKc hK
    refine absurd (hvol δ hδ) (not_lt.mpr (le_of_eq ?_))
    exact setLIntegral_measure_zero _ _
      (measure_mono_null (inter_subset_inter_right W
        (fun w (hw : K w < δ) ↦ hw.le : {w | K w < δ} ⊆ {w | K w ≤ δ})) hnull)
  · have : Nonempty R.M := ⟨F.centre (Classical.arbitrary F.Piece).chart⟩
    obtain ⟨ρ, hρ, hT⟩ := F.exists_isSingularityType hW hKc hK hφ hφc
    obtain ⟨hl, hm⟩ := F.rlct_eq_and_mult_eq ρ hρ hW hKc hK hφ hφc
    rw [hl, hm]
    exact hT

end SingularLearningTheory
