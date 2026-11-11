/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.ChartFamily.Basic
public import SLT.Data.Finset.Argmin

/-!
# `combLam`/`combTheta` agree across two chart families related by a surjection (route (a), D4)

The `MonomialChartCover`-level specialization of `VolumeScaling.aggLift`
(`Dln/VolumeScaling/AggregateLift.lean`): for two resolution chart families — a "full" family
`D₁` indexed by `ι` and a "compressed" family `D₂` indexed by `κ`, over the same ambient space,
loss, and base point — related by a map `g : ι → κ` with a section `s : κ → ι`, the per-chart
hypotheses

* `H1`       — `(D₂.chart (g a)).lam ≤ (D₁.chart a).lam`              (compressed `λ` ≤ full `λ`),
* `Hlam_sec` — `(D₁.chart (s b)).lam = (D₂.chart b).lam`             (representative `λ` identity),
* `H2`       — at equal `λ`, `(D₁.chart a).theta ≤ (D₂.chart (g a)).theta` (full `θ` ≤ comp `θ`),
* `Hth_sec`  — `(D₁.chart (s b)).theta = (D₂.chart b).theta`         (representative `θ` identity),

give `D₁.combLam = D₂.combLam` and `D₁.combTheta = D₂.combTheta`.

This is the exact statement route (a)'s global lift (D4 / D2b / D3b) invokes, abstracted over the
cover bundle's leaf-to-representative map: D4 supplies `g := leafComp`, `s :=` the representative
section, with `H1`/`H2` the committed per-pivot exponent comparison
(`lam2OfVec_le_of_ratioDom` / `thetaOfVec_le_of_ratioDom`, via the per-slot read-off) and the
section identities from the bundle's representative structure.  The proof is a direct
application of `Finset.inf'_univ_eq_of_le_of_section` / `Finset.sup'_argmin_eq_of_le_of_section`:
`combLam` unfolds to the family infimum,
`combTheta` to the supremum over the argmin set, matching the kernel's conclusion definitionally
(the differing nonemptiness witnesses are proof-irrelevant).
-/

public section

namespace SingularLearningTheory

open MonomialChartCover

variable {Ambient : Type*} [MeasurableSpace Ambient] [TopologicalSpace Ambient]
  {μ : MeasureTheory.Measure Ambient} {f : Ambient → ℝ} {w : Ambient}
  {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

/-- **Route-(a) D4 (Network-side).** Two resolution chart families related by a
surjection-with-section, with fibrewise `λ`-domination, `θ`-domination at equal `λ`, and the
representative section identities, have equal combinatorial least-exponent and equal
combinatorial multiplicity. -/
theorem MonomialChartCover.combLamTheta_eq_of_surjSection
    (D₁ : MonomialChartCover Ambient μ f w ι) (D₂ : MonomialChartCover Ambient μ f w κ)
    (g : ι → κ) (s : κ → ι)
    (H1 : ∀ a, (D₂.chart (g a)).lam ≤ (D₁.chart a).lam)
    (Hlam_sec : ∀ b, (D₁.chart (s b)).lam = (D₂.chart b).lam)
    (H2 : ∀ a, (D₁.chart a).lam = (D₂.chart (g a)).lam →
      (D₁.chart a).theta ≤ (D₂.chart (g a)).theta)
    (Hth_sec : ∀ b, (D₁.chart (s b)).theta = (D₂.chart b).theta) :
    D₁.combLam = D₂.combLam ∧ D₁.combTheta = D₂.combTheta :=
  ⟨Finset.inf'_univ_eq_of_le_of_section g s (fun a => (D₁.chart a).lam) (fun b => (D₂.chart b).lam)
      H1 Hlam_sec,
   Finset.sup'_argmin_eq_of_le_of_section g s (fun a => (D₁.chart a).lam)
       (fun b => (D₂.chart b).lam)
     (fun a => (D₁.chart a).theta) (fun b => (D₂.chart b).theta) H1 Hlam_sec H2 Hth_sec⟩

end SingularLearningTheory
