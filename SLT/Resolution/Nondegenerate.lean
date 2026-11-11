/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.Main
public import SLT.Resolution.Atlas

/-!
# Nondegeneracy from positive weights at the chart origins

[Wat09, Theorem 6.5] (3)–(4) chooses the partition of unity with every chart weight positive on the
open cube; the atlas construction of this directory makes every weight positive at the origin of its
chart. That suffices for `NondegenerateResolutionAtlas`: an essential chart's trace integrand is
nonnegative, integrable (`integrableOn_traceWeight`), and positive on a neighbourhood of the
origin in the open cube, so its trace mass is positive. Repairs [Hit26]'s lower bound.

| Thesis | Lean |
| --- | --- |
| positive essential trace mass (not in [Hit26]; [Wat09, Theorem 6.5] (3)) | |
| | `NondegenerateResolutionAtlas.ofWeightPos` |
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

namespace ResolutionAtlas

variable (R : ResolutionAtlas K φ W)

/-- If the weight of a chart is positive at the origin of the chart, its essential trace mass is
positive. -/
theorem essentialTraceMass_pos_of_weight_pos (α : R.ι) (h0 : 0 < R.weight α 0) :
    0 < R.essentialTraceMass α := by
  have hb := R.b_pos α
  have hcube : MeasurableSet (cube d (R.b α)) := measurableSet_Icc
  rw [R.essentialTraceMass_eq α]
  -- the trace weight is nonnegative on the cube and integrable
  have hnn : 0 ≤ᵐ[volume.restrict (cube d (R.b α))] R.traceWeight α := by
    filter_upwards [ae_restrict_mem hcube] with v hv
    exact R.traceWeight_nonneg α hv
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn (R.integrableOn_traceWeight α)]
  -- it is positive on `ocube ∩ ball 0 r` for a small `r`, where the weight is still positive
  have hcont : ContinuousAt (fun v ↦ R.weight α (R.primaryZero α v)) 0 :=
    (R.continuous_weight_primaryZero α).continuousAt
  have hpz : (R.primaryZero α 0 : Fin d → ℝ) = 0 := by
    funext j
    simp only [primaryZero]
    split_ifs <;> simp [hb.le]
  have hw0 : 0 < R.weight α (R.primaryZero α 0) := by rw [hpz]; exact h0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (lt_mem_nhds hw0))
  have hopen : IsOpen (ocube d (min r (R.b α))) := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
  have hne : (ocube d (min r (R.b α))).Nonempty :=
    ⟨fun _ ↦ min r (R.b α) / 2, fun j _ ↦ ⟨by positivity, by linarith [lt_min hr hb]⟩⟩
  refine lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono fun v hv ↦ ?_)
  have hvr : ∀ j, 0 < v j ∧ v j < min r (R.b α) := fun j ↦ hv j (mem_univ j)
  have hvc : v ∈ cube d (R.b α) := mem_cube.2 fun j ↦
    ⟨(hvr j).1.le, ((hvr j).2.trans_le (min_le_right _ _)).le⟩
  refine ⟨?_, hvc⟩
  rw [Function.mem_support, traceWeight]
  refine (mul_pos (Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hvr j).1 _) ?_).ne'
  refine hball ?_
  rw [dist_zero_right, pi_norm_lt_iff hr]
  intro j
  rw [Real.norm_eq_abs, abs_of_pos (hvr j).1]
  exact (hvr j).2.trans_le (min_le_left _ _)

end ResolutionAtlas

/-- An atlas all of whose weights are positive at the chart origins is nondegenerate: every
essential chart (there is one, the family is finite and nonempty) has positive trace mass. -/
@[expose] noncomputable def NondegenerateResolutionAtlas.ofWeightPos (R : ResolutionAtlas K φ W)
    (h : ∀ α, 0 < R.weight α 0) : NondegenerateResolutionAtlas K φ W :=
  { R with
    traceMass_pos := by
      obtain ⟨α, hα, hαeq⟩ := Finset.exists_mem_eq_sup'
        (ResolutionAtlas.minimalCharts_nonempty R) R.chartMult
      refine ⟨α, ⟨(Finset.mem_filter.mp hα).2, ?_⟩, R.essentialTraceMass_pos_of_weight_pos α (h α)⟩
      rw [ResolutionAtlas.mult, hαeq] }

end SingularLearningTheory
