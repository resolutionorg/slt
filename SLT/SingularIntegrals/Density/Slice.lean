/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.Analysis.Mellin.SmoothContinuation
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The state density of a monomial chart: the slice formula

For a chart `[0,b]^{n+1}` with `K = ∏ u_q^{2k_q}` and density `f(u) ∏ u_q^{h_q}` (`f ≥ 0`
measurable), the pushforward of the chart measure under `K` has the density obtained by solving
`K = t` for one active coordinate `p` (`k_p > 0`): with `a = 2k_p`, `A(y) = ∏_{q ≠ p} y_q^{2k_q}`
and `x(t, y) = (t/A(y))^{1/a}`,

  `v(t) = ∫ 1_{0 < t < A(y) b^a} · t^{1/a − 1} / (a A(y)^{1/a})
    · x^{h_p} f(x, y) ∏ y_j^{h_j} dy`.

(`sliceDens`), and `K_*(f ∏u^h du|_{box}) = v(t) dt` (`map_monomial_eq_withDensity_sliceDens`).

The proof is Tonelli: slice the box along the coordinate `p` (`lintegral_box_insertNth`),
substitute `t = A(y) u_p^a` in the inner integral (`lintegral_Ioo_comp_mul_rpow`, the
one-dimensional change of variables `lintegral_image_eq_lintegral_abs_deriv_mul`), and swap.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.SliceDensity

open SingularLearningTheory.MellinAnalysis

section Slicing

variable {n : ℕ}

/-- Slicing a box `lintegral` along coordinate `p`. -/
private theorem lintegral_box_insertNth (b : Fin (n + 1) → ℝ) (p : Fin (n + 1))
    {Φ : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ u in Icc 0 b, Φ u =
      ∫⁻ y in Icc 0 (b ∘ p.succAbove), ∫⁻ x in Icc (0 : ℝ) (b p), Φ (p.insertNth x y) := by
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) p).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) p).symm _
  have hbox := preimage_box_piFinSuccAbove b p
  rw [← lintegral_indicator measurableSet_Icc, hem.lintegral_map_equiv]
  have hind : ∀ z, (Icc 0 b).indicator Φ (e z) =
      (Icc 0 (b p) ×ˢ Icc 0 (b ∘ p.succAbove)).indicator (fun z ↦ Φ (e z)) z := by
    intro z
    rw [← hbox]
    exact (Set.indicator_comp_right (s := Icc 0 b) e).symm
  simp_rw [hind]
  rw [lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc),
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod_symm' (fun z ↦ Φ (e z)) (hΦ.comp e.measurable)

end Slicing

section OneDim

/-- **The one-dimensional substitution `t = A u^a`** on `(0, b)`: for `a, A, b > 0`,
`∫_0^b H(A u^a) w(u) du = ∫_0^{A b^a} H(t) · (t^{1/a − 1}/(a A^{1/a})) · w((t/A)^{1/a}) dt`. -/
private theorem lintegral_Ioo_comp_mul_rpow {a A b : ℝ} (ha : 0 < a) (hA : 0 < A) (hb : 0 < b)
    (H w : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioo (0 : ℝ) b, H (A * u ^ a) * w u =
      ∫⁻ t in Ioo (0 : ℝ) (A * b ^ a),
        H t * (ENNReal.ofReal (t ^ (1 / a - 1) / (a * A ^ (1 / a))) * w ((t / A) ^ (1 / a))) := by
  set f : ℝ → ℝ := fun u ↦ A * u ^ a with hf
  have hinj : InjOn f (Ioo 0 b) := by
    refine StrictMonoOn.injOn fun u hu v hv huv ↦ ?_
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hu.1.le huv ha) hA
  have himg : f '' Ioo 0 b = Ioo 0 (A * b ^ a) := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨mul_pos hA (Real.rpow_pos_of_pos hu.1 a),
        mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hu.1.le hu.2 ha) hA⟩
    · intro ht
      have ht0 : 0 < t / A := div_pos ht.1 hA
      refine ⟨(t / A) ^ (1 / a), ⟨Real.rpow_pos_of_pos ht0 _, ?_⟩, ?_⟩
      · have h1 : t / A < b ^ a := by rw [div_lt_iff₀ hA, mul_comm]; exact ht.2
        have h2 := Real.rpow_lt_rpow ht0.le h1 (by positivity : (0 : ℝ) < 1 / a)
        rwa [← Real.rpow_mul hb.le, mul_one_div_cancel ha.ne', Real.rpow_one] at h2
      · simp only [hf]
        rw [← Real.rpow_mul ht0.le, one_div_mul_cancel ha.ne', Real.rpow_one,
          mul_div_cancel₀ _ hA.ne']
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) b, HasDerivWithinAt f (A * (a * u ^ (a - 1))) (Ioo 0 b) u :=
    fun u hu ↦ ((Real.hasDerivAt_rpow_const (Or.inl hu.1.ne')).const_mul A).hasDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj
    (fun t ↦ H t * (ENNReal.ofReal (t ^ (1 / a - 1) / (a * A ^ (1 / a))) * w ((t / A) ^ (1 / a))))
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu ↦ ?_
  have hu0 : 0 < u := hu.1
  have hfu : f u = A * u ^ a := rfl
  -- the inverse substitution returns `u`, and the Jacobian factors cancel
  have hback : (A * u ^ a / A) ^ (1 / a) = u := by
    rw [mul_div_cancel_left₀ _ hA.ne', ← Real.rpow_mul hu0.le, mul_one_div_cancel ha.ne',
      Real.rpow_one]
  have hjac : |A * (a * u ^ (a - 1))| * ((A * u ^ a) ^ (1 / a - 1) / (a * A ^ (1 / a))) = 1 := by
    have hpos : 0 < A * (a * u ^ (a - 1)) := by positivity
    rw [abs_of_pos hpos, Real.mul_rpow hA.le (Real.rpow_pos_of_pos hu0 a).le,
      ← Real.rpow_mul hu0.le]
    have hA1 : A ^ (1 / a - 1) = A ^ (1 / a) / A := by
      rw [Real.rpow_sub hA, Real.rpow_one]
    rw [hA1]
    have hu1 : u ^ (a * (1 / a - 1)) = u ^ (1 - a) := by
      congr 1
      field_simp
    rw [hu1, show u ^ (1 - a) = (u ^ (a - 1))⁻¹ by
      rw [← Real.rpow_neg hu0.le]; congr 1; ring]
    have hua : u ^ (a - 1) ≠ 0 := (Real.rpow_pos_of_pos hu0 _).ne'
    have hAa : A ^ (1 / a) ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
    field_simp
  simp only [hfu, hback]
  have hE : ENNReal.ofReal |A * (a * u ^ (a - 1))| *
      ENNReal.ofReal ((A * u ^ a) ^ (1 / a - 1) / (a * A ^ (1 / a))) = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), hjac, ENNReal.ofReal_one]
  calc H (A * u ^ a) * w u
      = (ENNReal.ofReal |A * (a * u ^ (a - 1))| *
          ENNReal.ofReal ((A * u ^ a) ^ (1 / a - 1) / (a * A ^ (1 / a)))) *
          (H (A * u ^ a) * w u) := by rw [hE, one_mul]
    _ = _ := by ring

end OneDim

section Chart

variable {n : ℕ} (k h : Fin (n + 1) → ℕ) (b : ℝ) (f : (Fin (n + 1) → ℝ) → ℝ) (p : Fin (n + 1))

/-- The exponent `a = 2k_p` of the solved coordinate. -/
@[expose] noncomputable def aExp : ℝ := 2 * k p

/-- `A(y) = ∏_{q ≠ p} y_q^{2k_q}` over the remaining coordinates. -/
@[expose] noncomputable def chartA (y : Fin n → ℝ) : ℝ := ∏ j, y j ^ (2 * k (p.succAbove j))

/-- The solved coordinate `x(t, y) = (t / A(y))^{1/a}`. -/
@[expose] noncomputable def xOf (t : ℝ) (y : Fin n → ℝ) : ℝ := (t / chartA k p y) ^ (1 / aExp k p)

/-- The slice integrand, including the Jacobian of the inverse monomial substitution. -/
@[expose] noncomputable def sliceInt (y : Fin n → ℝ) (t : ℝ) : ℝ≥0∞ :=
  (Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p)).indicator (fun t ↦
    ENNReal.ofReal (t ^ (1 / aExp k p - 1) / (aExp k p * chartA k p y ^ (1 / aExp k p))) *
      (ENNReal.ofReal (xOf k p t y ^ (h p)) * ENNReal.ofReal (f (p.insertNth (xOf k p t y) y)) *
        ∏ j, ENNReal.ofReal (y j ^ (h (p.succAbove j))))) t

/-- **The slice density** of the chart pushforward. -/
@[expose] noncomputable def sliceDens (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Icc 0 (fun _ ↦ b), sliceInt k h b f p y t

variable {k h b f p}

theorem measurable_chartA : Measurable (chartA k p) :=
  Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _

theorem measurable_xOf_uncurry : Measurable (fun q : (Fin n → ℝ) × ℝ ↦ xOf k p q.2 q.1) :=
  (measurable_snd.div (measurable_chartA.comp measurable_fst)).pow_const _

private theorem measurable_sliceInt_uncurry (hfm : Measurable f) :
    Measurable (fun q : (Fin n → ℝ) × ℝ ↦ sliceInt k h b f p q.1 q.2) := by
  have hS : MeasurableSet {q : (Fin n → ℝ) × ℝ | 0 < q.2 ∧ q.2 < chartA k p q.1 * b ^ aExp k p} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd ((measurable_chartA.comp measurable_fst).mul_const _))
  have hins : Measurable (fun q : (Fin n → ℝ) × ℝ ↦
      p.insertNth (α := fun _ ↦ ℝ) (xOf k p q.2 q.1) q.1) := by
    have := (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) p).symm.measurable.comp
      ((measurable_xOf_uncurry (k := k) (p := p)).prodMk measurable_fst)
    exact this
  have hG : Measurable (fun q : (Fin n → ℝ) × ℝ ↦
      ENNReal.ofReal (q.2 ^ (1 / aExp k p - 1) / (aExp k p * chartA k p q.1 ^ (1 / aExp k p))) *
        (ENNReal.ofReal (xOf k p q.2 q.1 ^ (h p)) *
          ENNReal.ofReal (f (p.insertNth (xOf k p q.2 q.1) q.1)) *
          ∏ j, ENNReal.ofReal (q.1 j ^ (h (p.succAbove j))))) := by
    refine ((measurable_snd.pow_const _).div
      (((measurable_chartA.comp measurable_fst).pow_const _).const_mul _)).ennreal_ofReal.mul
      (((measurable_xOf_uncurry.pow_const _).ennreal_ofReal.mul
        (hfm.comp hins).ennreal_ofReal).mul ?_)
    exact Finset.measurable_prod _ fun j _ ↦
      ((measurable_pi_apply j).comp measurable_fst).pow_const _ |>.ennreal_ofReal
  convert hG.indicator hS using 1
  funext q
  simp only [sliceInt, Set.indicator_apply, Set.mem_Ioo, Set.mem_ofPred_eq]

theorem measurable_sliceDens (hfm : Measurable f) : Measurable (sliceDens k h b f p) :=
  Measurable.lintegral_prod_left' (μ := volume.restrict (Icc 0 fun _ ↦ b))
    (measurable_sliceInt_uncurry hfm)

/-- The monomial `K(u) = ∏ u_q^{2k_q}` on the chart. -/
theorem measurable_monomial : Measurable fun u : Fin (n + 1) → ℝ ↦ ∏ q, u q ^ (2 * k q) :=
  Finset.measurable_prod _ fun q _ ↦ (measurable_pi_apply q).pow_const _

private theorem measurable_chartDens (hfm : Measurable f) :
    Measurable fun u : Fin (n + 1) → ℝ ↦ ENNReal.ofReal (f u) * ∏ q, ENNReal.ofReal (u q ^ h q) :=
  hfm.ennreal_ofReal.mul
    (Finset.measurable_prod _ fun q _ ↦ ((measurable_pi_apply q).pow_const _).ennreal_ofReal)

/-- **Tonelli for the slice density**: for every measurable `H`,
`∫_{box} H(K(u)) f(u) ∏ u^h du = ∫ H(t) v(t) dt`. -/
private theorem lintegral_box_monomial_eq (hb : 0 < b) (hkp : 0 < k p) (hfm : Measurable f)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ u in Icc 0 (fun _ ↦ b),
        H (∏ q, u q ^ (2 * k q)) * (ENNReal.ofReal (f u) * ∏ q, ENNReal.ofReal (u q ^ h q)) =
      ∫⁻ t, H t * sliceDens k h b f p t := by
  have ha : 0 < aExp k p := by unfold aExp; positivity
  -- slice along `p`
  rw [lintegral_box_insertNth (fun _ ↦ b) p (Φ := fun u ↦
    H (∏ q, u q ^ (2 * k q)) * (ENNReal.ofReal (f u) * ∏ q, ENNReal.ofReal (u q ^ h q)))
    ((hH.comp measurable_monomial).mul (measurable_chartDens hfm))]
  -- the inner integral for a.e. `y` (all coordinates positive)
  have hinner : ∀ᵐ y ∂(volume.restrict (Icc 0 fun _ ↦ b)),
      ∫⁻ x in Icc (0 : ℝ) b,
          H (∏ q, (p.insertNth (α := fun _ ↦ ℝ) x y) q ^ (2 * k q)) *
            (ENNReal.ofReal (f (p.insertNth x y)) *
              ∏ q, ENNReal.ofReal ((p.insertNth (α := fun _ ↦ ℝ) x y) q ^ h q)) =
        ∫⁻ t, H t * sliceInt k h b f p y t := by
    filter_upwards [ae_box_pos (fun _ : Fin n ↦ b)] with y hy
    have hA : 0 < chartA k p y := Finset.prod_pos fun j _ ↦ pow_pos (hy j).1 _
    rw [setLIntegral_congr (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := b)).symm]
    have hpt : ∀ x ∈ Ioo (0 : ℝ) b,
        H (∏ q, (p.insertNth (α := fun _ ↦ ℝ) x y) q ^ (2 * k q)) *
            (ENNReal.ofReal (f (p.insertNth x y)) *
              ∏ q, ENNReal.ofReal ((p.insertNth (α := fun _ ↦ ℝ) x y) q ^ h q)) =
          H (chartA k p y * x ^ aExp k p) *
            (ENNReal.ofReal (x ^ (h p)) * ENNReal.ofReal (f (p.insertNth x y)) *
              ∏ j, ENNReal.ofReal (y j ^ (h (p.succAbove j)))) := by
      intro x hx
      have h1 : ∏ q, (p.insertNth (α := fun _ ↦ ℝ) x y) q ^ (2 * k q) =
          chartA k p y * x ^ aExp k p := by
        rw [Fin.prod_univ_succAbove _ p, Fin.insertNth_apply_same, mul_comm]
        simp only [Fin.insertNth_apply_succAbove, chartA, aExp]
        rw [← Real.rpow_natCast]
        push_cast
        ring_nf
      have h2 : ∏ q, ENNReal.ofReal ((p.insertNth (α := fun _ ↦ ℝ) x y) q ^ h q) =
          ENNReal.ofReal (x ^ (h p)) * ∏ j, ENNReal.ofReal (y j ^ (h (p.succAbove j))) := by
        rw [Fin.prod_univ_succAbove _ p, Fin.insertNth_apply_same]
        simp only [Fin.insertNth_apply_succAbove]
      rw [h1, h2]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioo hpt,
      lintegral_Ioo_comp_mul_rpow ha hA hb H
        (fun x ↦ ENNReal.ofReal (x ^ (h p)) * ENNReal.ofReal (f (p.insertNth x y)) *
          ∏ j, ENNReal.ofReal (y j ^ (h (p.succAbove j)))),
      ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t ↦ ?_
    simp only [sliceInt, xOf]
    rw [Set.indicator_mul_right]
  rw [show Icc 0 ((fun _ : Fin (n + 1) ↦ b) ∘ p.succAbove) = Icc 0 fun _ ↦ b from rfl,
    lintegral_congr_ae hinner]
  -- swap the two integrals
  have hmeas : Measurable (Function.uncurry fun (y : Fin n → ℝ) (t : ℝ) ↦
      H t * sliceInt k h b f p y t) :=
    (hH.comp measurable_snd).mul (measurable_sliceInt_uncurry hfm)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun t ↦ ?_
  unfold sliceDens
  rw [lintegral_const_mul _ (measurable_sliceInt_uncurry hfm).of_uncurry_right]

/-- **The chart pushforward has the slice density**: `K_*(f ∏ u^h · vol|_{box}) = v dt`. -/
theorem map_monomial_eq_withDensity_sliceDens (hb : 0 < b) (hkp : 0 < k p) (hfm : Measurable f) :
    Measure.map (fun u : Fin (n + 1) → ℝ ↦ ∏ q, u q ^ (2 * k q))
        ((volume.restrict (Icc 0 fun _ ↦ b)).withDensity
          fun u ↦ ENNReal.ofReal (f u) * ∏ q, ENNReal.ofReal (u q ^ h q)) =
      volume.withDensity (sliceDens k h b f p) := by
  refine Measure.ext_of_lintegral _ fun H hH ↦ ?_
  rw [lintegral_map hH measurable_monomial,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_chartDens hfm)
      (g := fun u ↦ H (∏ q, u q ^ (2 * k q))) (hH.comp measurable_monomial),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_sliceDens hfm) hH]
  calc _ = ∫⁻ u in Icc 0 (fun _ ↦ b),
        H (∏ q, u q ^ (2 * k q)) * (ENNReal.ofReal (f u) * ∏ q, ENNReal.ofReal (u q ^ h q)) :=
        lintegral_congr fun u ↦ by simp only [Pi.mul_apply]; ring
    _ = ∫⁻ t, H t * sliceDens k h b f p t := lintegral_box_monomial_eq hb hkp hfm hH
    _ = _ := lintegral_congr fun t ↦ by simp only [Pi.mul_apply]; ring

end Chart

end SingularLearningTheory.SliceDensity
