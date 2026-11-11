/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.PartialResolution.Structural.Sigma
public import SLT.PartialResolution.Structural.Restrict
public import Hironaka.Analytic.ConvSeries.Radius

/-!
# Terminal (monomial) charts and monomial resolutions

"`f` is locally normal crossings if each point of `M` admits a coordinate neighbourhood `U`, with
coordinates `x = (x_1, …, x_m)`, such that `f(x) = x_1^{a_1} ⋯ x_m^{a_m} g(x)` where `g` vanishes
nowhere in `U`" [BM88, Definition 4.3]. In chart form (`IsMonomialChart F φ dom e h W`) the
condition is stated for a chart `φ` together with its Jacobian: an open `W ⊇ dom` on which `φ` is
analytic, injective off the set where the Jacobian monomial vanishes, and continuous nonvanishing
`u, v` on `W` with `F ∘ φ = u · y^e` and `det Dφ = v · y^h` on `W`. The Jacobian clause is what
the change-of-variables formula of the chart-form theorems needs; the open `W` is carried
explicitly so that a chart may be recentred at boundary points of its box (`Translate.lean`). The
exceptional set of a terminal chart is `{y | y^h = 0}`: the determinant vanishes exactly there
(`IsMonomialChart.det_ne_zero`), so "injective and of nonvanishing determinant off the
exceptional set" is the `injOn` field plus that lemma.

`PartialResolution.ForallChart R P`: every chart of `R` satisfies the chart predicate `P φ dom E`;
predicates stable under shrinking the domain (`ChartPredStable`) pass through `restrict`
(`forallChart_restrict`), and every predicate passes through `sigma` (`forallChart_sigma`).
`PartialResolution.IsMonomial R` is the case "terminal for some exponents and some `W`", a stable
predicate (`IsMonomialChart.mono`, `chartPredStable_isMonomialChart`); this is the conclusion
"`f ∘ π_j` is locally normal crossings on `W_j`" of [BM88, Theorem 4.4 (4)] in chart form.
-/

@[expose] public section

open Set Analytic

namespace Analytic

variable {n : ℕ}

/-- A terminal (monomial) chart for `F`: an open `W ⊇ dom` on which `φ` is analytic, injective where
the Jacobian monomial `y^h` does not vanish, with `F ∘ φ = u · y^e` and `det Dφ = v · y^h` for
continuous nonvanishing `u, v` on `W`. The normal-crossings condition of [BM88, Definition 4.3]
together with the same condition on the Jacobian of the chart. -/
structure IsMonomialChart (F : (Fin n → ℝ) → ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (dom : Set (Fin n → ℝ)) (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)) : Prop where
  isOpen : IsOpen W
  subset : dom ⊆ W
  analyticOnNhd : AnalyticOnNhd ℝ φ W
  injOn : InjOn φ {y | y ∈ W ∧ monomialEval y h ≠ 0}
  exists_unit : ∃ u : (Fin n → ℝ) → ℝ, ContinuousOn u W ∧ (∀ y ∈ W, u y ≠ 0) ∧
    ∀ y ∈ W, F (φ y) = u y * monomialEval y e
  exists_jacUnit : ∃ v : (Fin n → ℝ) → ℝ, ContinuousOn v W ∧ (∀ y ∈ W, v y ≠ 0) ∧
    ∀ y ∈ W, (fderiv ℝ φ y).det = v y * monomialEval y h

/-- A per-chart predicate: a property of the chart map, its domain and its exceptional set. -/
abbrev ChartPred (n : ℕ) : Type :=
  ((Fin n → ℝ) → (Fin n → ℝ)) → Set (Fin n → ℝ) → Set (Fin n → ℝ) → Prop

/-- A chart predicate stable under shrinking the chart domain (with the exceptional set cut down
to the new domain, as `restrict` does). -/
def ChartPredStable (P : ChartPred n) : Prop :=
  ∀ (φ : (Fin n → ℝ) → (Fin n → ℝ)) (dom E dom' : Set (Fin n → ℝ)),
    dom' ⊆ dom → P φ dom E → P φ dom' (E ∩ dom')

namespace PartialResolution

variable {F : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}

/-- Every chart of `R` satisfies the chart predicate `P`. -/
def ForallChart (R : PartialResolution n F K) (P : ChartPred n) : Prop :=
  ∀ i, P (R.φ i) (R.dom i) (R.E i)

/-- A monomial resolution: every chart is terminal (for some exponents and some open
neighbourhood of its box). This is "`f ∘ π_j` is locally normal crossings on `W_j`"
[BM88, Theorem 4.4 (4)] in chart form. -/
abbrev IsMonomial (R : PartialResolution n F K) : Prop :=
  R.ForallChart fun φ dom _ =>
    ∃ (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)), IsMonomialChart F φ dom e h W

end PartialResolution

namespace IsMonomialChart

variable {F : (Fin n → ℝ) → ℝ} {φ : (Fin n → ℝ) → (Fin n → ℝ)} {dom W : Set (Fin n → ℝ)}
  {e h : Fin n →₀ ℕ}

/-- The Jacobian of a terminal chart does not vanish where its monomial does not. -/
theorem det_ne_zero (hc : IsMonomialChart F φ dom e h W) {y : Fin n → ℝ} (hy : y ∈ W)
    (hm : monomialEval y h ≠ 0) : (fderiv ℝ φ y).det ≠ 0 := by
  obtain ⟨v, -, hv0, hv⟩ := hc.exists_jacUnit
  rw [hv y hy]
  exact mul_ne_zero (hv0 y hy) hm

/-- A terminal chart stays terminal on a smaller box (same `W`). -/
theorem mono (hc : IsMonomialChart F φ dom e h W) {dom' : Set (Fin n → ℝ)} (hd : dom' ⊆ dom) :
    IsMonomialChart F φ dom' e h W :=
  { hc with subset := hd.trans hc.subset }

end IsMonomialChart

/-- "Terminal for some exponents and some `W`" is stable under shrinking the box. -/
theorem chartPredStable_isMonomialChart (F : (Fin n → ℝ) → ℝ) :
    ChartPredStable fun φ dom (_ : Set (Fin n → ℝ)) =>
      ∃ (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)), IsMonomialChart F φ dom e h W :=
  fun _ _ _ _ hd ⟨e, h, W, hc⟩ => ⟨e, h, W, hc.mono hd⟩

namespace PartialResolution

variable {F : (Fin n → ℝ) → ℝ}

/-- A chart predicate holding on every summand holds on the disjoint union. -/
theorem forallChart_sigma {ι : Type} [Fintype ι] {K : ι → Set (Fin n → ℝ)}
    (R : ∀ i, PartialResolution n F (K i)) {P : ChartPred n} (h : ∀ i, (R i).ForallChart P) :
    (sigma R).ForallChart P :=
  fun p => h p.1 p.2

/-- A stable chart predicate passes to the restriction. -/
theorem forallChart_restrict {K' : Set (Fin n → ℝ)} (R : PartialResolution n F K')
    {K : Set (Fin n → ℝ)} (hK : K ⊆ K') (hKc : IsCompact K) {P : ChartPred n}
    (hP : ChartPredStable P) (h : R.ForallChart P) : (R.restrict hK hKc).ForallChart P :=
  fun i => hP _ _ _ _ inter_subset_left (h i)

end PartialResolution

end Analytic
