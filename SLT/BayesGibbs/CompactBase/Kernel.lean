/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import SLT.BayesGibbs.CompactBase.Quantise
import SLT.BayesGibbs.FiniteQuartet.Det
import SLT.BayesGibbs.RadialMoments
import SLT.FreeEnergy.Main
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Positive-semidefinite kernels on a compact base

Continuous positive-semidefinite kernels, the two-replica quantities on a compact base, their
positivity and quadratic bounds, and their quantisation limits.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory.GaussianPosterior

/-- A continuous symmetric positive-semidefinite kernel. -/
structure _root_.PSDKernel (K : Type*) [TopologicalSpace K] where
  /-- The kernel. -/
  C : K → K → ℝ
  protected symm : ∀ x y, C x y = C y x
  psd : ∀ (m : ℕ) (x : Fin m → K) (v : Fin m → ℝ),
    0 ≤ ∑ i, ∑ j, C (x i) (x j) * v i * v j
  continuous : Continuous (Function.uncurry C)

end SingularLearningTheory.GaussianPosterior

namespace PSDKernel

open SingularLearningTheory SingularLearningTheory.GaussianPosterior

variable {K : Type*} [TopologicalSpace K] (𝒞 : PSDKernel K)

theorem diag_nonneg (x : K) : 0 ≤ 𝒞.C x x := by
  have := 𝒞.psd 1 (fun _ ↦ x) (fun _ ↦ 1)
  simpa using this

/-- The `2 × 2` minor: `C(x,y)² ≤ C(x,x) C(y,y)`. -/
protected theorem sq_le (x y : K) : 𝒞.C x y ^ 2 ≤ 𝒞.C x x * 𝒞.C y y := by
  have h : ∀ s t : ℝ,
      0 ≤ 𝒞.C x x * s * s + 𝒞.C x y * s * t + (𝒞.C x y * t * s + 𝒞.C y y * t * t) := by
    intro s t
    have := 𝒞.psd 2 ![x, y] ![s, t]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      𝒞.symm y x] at this
    exact this
  rcases (𝒞.diag_nonneg x).lt_or_eq with ha | ha
  · have := h (𝒞.C x y) (-𝒞.C x x)
    nlinarith
  · rw [← ha, zero_mul]
    by_contra hb
    have hb' : 𝒞.C x y ≠ 0 := by
      intro h0
      exact hb (by rw [h0]; norm_num)
    have := h (-(𝒞.C y y + 1) / (2 * 𝒞.C x y)) 1
    rw [← ha] at this
    have key : 𝒞.C x y * (-(𝒞.C y y + 1) / (2 * 𝒞.C x y)) = -(𝒞.C y y + 1) / 2 := by
      field_simp
    nlinarith [key]

protected theorem continuous_diag : Continuous fun x ↦ 𝒞.C x x :=
  𝒞.continuous.comp (continuous_id.prodMk continuous_id)

/-- Positive semidefiniteness over an arbitrary finite set of points. -/
theorem sum_sum_nonneg (T : Finset K) (v : K → ℝ) :
    0 ≤ ∑ a ∈ T, ∑ b ∈ T, 𝒞.C a b * v a * v b := by
  have := 𝒞.psd T.card (fun i ↦ (T.equivFin.symm i : K)) (fun i ↦ v (T.equivFin.symm i))
  calc (0 : ℝ) ≤ _ := this
    _ = ∑ a : T, ∑ b : T, 𝒞.C a b * v a * v b := by
        refine Fintype.sum_equiv T.equivFin.symm _ _ fun i ↦ ?_
        exact Fintype.sum_equiv T.equivFin.symm _ _ fun j ↦ rfl
    _ = ∑ a ∈ T, ∑ b ∈ T, 𝒞.C a b * v a * v b := by
        rw [← Finset.sum_coe_sort T]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← Finset.sum_coe_sort T]

end PSDKernel

namespace SingularLearningTheory.GaussianPosterior

/-- `2z ≤ a + b` when `z² ≤ ab` with `a, b ≥ 0`. -/
private theorem two_mul_le_add_of_sq_le {z a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : z ^ 2 ≤ a * b) :
    2 * z ≤ a + b := by
  have h1 : (2 * z) ^ 2 ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  exact (abs_le_of_sq_le_sq' h1 (by linarith)).2

section Finite

variable {K : Type*} [MeasurableSpace K] [MeasurableSingletonClass K] (ρ : Measure K)
  [IsFiniteMeasure ρ]

/-- **Integrals against a finite-range map are finite sums**:
`∫ f(q x) dρ = ∑_{a ∈ range q} ρ(q⁻¹{a}) f(a)`. -/
theorem _root_.MeasureTheory.integral_comp_finiteRange {q : K → K} (hq : Measurable q)
    (hfin : (Set.range q).Finite)
    (f : K → ℝ) :
    ∫ x, f (q x) ∂ρ = ∑ a ∈ hfin.toFinset, ρ.real (q ⁻¹' {a}) * f a := by
  have hpt : ∀ x, f (q x) = ∑ a ∈ hfin.toFinset, (q ⁻¹' {a}).indicator (fun _ ↦ f a) x := by
    intro x
    rw [Finset.sum_eq_single (q x)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (hfin.mem_toFinset.2 (Set.mem_range_self x)) h
  simp_rw [hpt]
  rw [integral_finsetSum _ fun a _ ↦
    (integrable_const (f a)).indicator (hq (measurableSet_singleton a))]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [integral_indicator_const _ (hq (measurableSet_singleton a)), smul_eq_mul]

end Finite


section Kernel

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ}

/-- The bilocal integrand `C(x,y) S_{λ+1/2}(g x) S_{λ+1/2}(g y)` on `K × K`. -/
@[expose] noncomputable def bilocalC (β lam : ℝ) (𝒞 : PSDKernel K) (g : K → ℝ) (z : K × K) : ℝ :=
  𝒞.C z.1 z.2 * frozenInner (lam + 1 / 2) β (g z.1) * frozenInner (lam + 1 / 2) β (g z.2)

variable (ρ : Measure K) [IsFiniteMeasure ρ]

/-- `∫∫ C(x,y) S_{λ+1/2}(g x) S_{λ+1/2}(g y) dρ dρ`. -/
@[expose] noncomputable def compactQnum (β lam : ℝ) (𝒞 : PSDKernel K) (g : K → ℝ) : ℝ :=
  ∫ z, bilocalC β lam 𝒞 g z ∂(ρ.prod ρ)

/-- `Q_ρ(g) = compactQnum / D²`. -/
@[expose] noncomputable def compactQ (β lam : ℝ) (𝒞 : PSDKernel K) (g : K → ℝ) : ℝ :=
  compactQnum ρ β lam 𝒞 g / compactD β lam ρ g ^ 2

/-- The diagonal term `⟨r C(x,x)⟩ = ∫ C(x,x) S_{λ+1}(g x) dρ / D`. -/
@[expose] noncomputable def compactDiag (β lam : ℝ) (𝒞 : PSDKernel K) (g : K → ℝ) : ℝ :=
  (∫ x, 𝒞.C x x * frozenInner (lam + 1) β (g x) ∂ρ) / compactD β lam ρ g

/-- The connected two-point function `V_ρ(g) = ⟨r C(x,x)⟩ − ⟨√(rs) C(x,y)⟩`. -/
@[expose] noncomputable def compactV (β lam : ℝ) (𝒞 : PSDKernel K) (g : K → ℝ) : ℝ :=
  compactDiag ρ β lam 𝒞 g - compactQ ρ β lam 𝒞 g

variable (hβ : 0 < β) (hlam : 0 < lam) (𝒞 : PSDKernel K) (g : C(K, ℝ))
include hβ hlam

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem continuous_bilocalC : Continuous (bilocalC β lam 𝒞 g) :=
  (𝒞.continuous.mul ((continuous_frozenInner (by linarith) hβ).comp
    (g.continuous.comp continuous_fst))).mul
    ((continuous_frozenInner (by linarith) hβ).comp
      (g.continuous.comp continuous_snd))

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
private theorem continuous_diag_fluctuation :
    Continuous fun x ↦ 𝒞.C x x * frozenInner (lam + 1) β (g x) :=
  𝒞.continuous_diag.mul ((continuous_frozenInner (by linarith) hβ).comp g.continuous)

theorem compactQnum_map {q : K → K} (hq : Measurable q) :
    compactQnum (ρ.map q) β lam 𝒞 g = ∫ z, bilocalC β lam 𝒞 g (q z.1, q z.2) ∂(ρ.prod ρ) := by
  unfold compactQnum
  rw [Measure.map_prod_map _ _ hq hq, integral_map (hq.prodMap hq).aemeasurable
    (continuous_bilocalC hβ hlam 𝒞 g).measurable.aestronglyMeasurable]
  rfl

omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactDiag_map {q : K → K} (hq : Measurable q) :
    compactDiag (ρ.map q) β lam 𝒞 g =
      (∫ x, 𝒞.C (q x) (q x) * frozenInner (lam + 1) β (g (q x)) ∂ρ) /
        compactD β lam (ρ.map q) g := by
  unfold compactDiag
  rw [integral_map (f := fun x ↦ 𝒞.C x x * frozenInner (lam + 1) β (g x)) hq.aemeasurable
    (continuous_diag_fluctuation hβ hlam 𝒞 g).measurable.aestronglyMeasurable]

/-- **Positivity on finitely supported measures**: for a finite-range quantisation `q`,
`compactQnum (ρ.map q) ≥ 0` is the finite PSD inequality. -/
private theorem compactQnum_map_nonneg {q : K → K} (hq : Measurable q)
    (hfin : (Set.range q).Finite) :
    0 ≤ compactQnum (ρ.map q) β lam 𝒞 g := by
  set F : C(K × K, ℝ) := ⟨bilocalC β lam 𝒞 g, continuous_bilocalC hβ hlam 𝒞 g⟩ with hF
  have hint : Integrable (fun z : K × K ↦ bilocalC β lam 𝒞 g (q z.1, q z.2)) (ρ.prod ρ) :=
    Integrable.of_bound ((continuous_bilocalC hβ hlam 𝒞 g).measurable.comp
      (((hq.comp measurable_fst).prodMk (hq.comp measurable_snd)))).aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall fun z ↦ F.norm_coe_le_norm (q z.1, q z.2))
  rw [compactQnum_map ρ hβ hlam 𝒞 g hq, integral_prod _ hint]
  have hin : ∀ x, ∫ y, bilocalC β lam 𝒞 g (q x, q y) ∂ρ =
      ∑ b ∈ hfin.toFinset, ρ.real (q ⁻¹' {b}) * bilocalC β lam 𝒞 g (q x, b) := fun x ↦
    integral_comp_finiteRange ρ hq hfin (fun b ↦ bilocalC β lam 𝒞 g (q x, b))
  simp_rw [hin]
  have hout := integral_comp_finiteRange ρ hq hfin
    (fun a ↦ ∑ b ∈ hfin.toFinset, ρ.real (q ⁻¹' {b}) * bilocalC β lam 𝒞 g (a, b))
  beta_reduce at hout
  rw [hout]
  have hre : ∑ a ∈ hfin.toFinset, ρ.real (q ⁻¹' {a}) *
      ∑ b ∈ hfin.toFinset, ρ.real (q ⁻¹' {b}) * bilocalC β lam 𝒞 g (a, b) =
      ∑ a ∈ hfin.toFinset, ∑ b ∈ hfin.toFinset, 𝒞.C a b *
        (ρ.real (q ⁻¹' {a}) * frozenInner (lam + 1 / 2) β (g a)) *
        (ρ.real (q ⁻¹' {b}) * frozenInner (lam + 1 / 2) β (g b)) := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    simp only [bilocalC]
    ring
  rw [hre]
  exact 𝒞.sum_sum_nonneg _ _

omit hβ hlam in
/-- Product integrals of continuous functions converge under quantisation. -/
private theorem tendsto_integral_prod_comp_quantize (F : C(K × K, ℝ)) {q : ℕ → K → K}
    (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n ↦ ∫ z, F (q n z.1, q n z.2) ∂(ρ.prod ρ)) atTop
      (𝓝 (∫ z, F z ∂(ρ.prod ρ))) := by
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖F‖)
    (fun n ↦ (F.continuous.measurable.comp
      (((hq n).comp measurable_fst).prodMk ((hq n).comp measurable_snd))).aestronglyMeasurable)
    (integrable_const _) (fun n ↦ Filter.Eventually.of_forall fun z ↦ F.norm_coe_le_norm _)
    (Filter.Eventually.of_forall fun z ↦ ?_)
  exact (F.continuous.tendsto z).comp
    ((tendsto_quantize hε hqε z.1).prodMk_nhds (tendsto_quantize hε hqε z.2))

private theorem tendsto_compactQnum_map {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n ↦ compactQnum (ρ.map (q n)) β lam 𝒞 g) atTop
      (𝓝 (compactQnum ρ β lam 𝒞 g)) := by
  simp_rw [compactQnum_map ρ hβ hlam 𝒞 g (hq _)]
  exact tendsto_integral_prod_comp_quantize ρ
    ⟨bilocalC β lam 𝒞 g, continuous_bilocalC hβ hlam 𝒞 g⟩ hq hε hqε

/-- **`Q_ρ(g) ≥ 0`**: positive semidefiniteness passes from finite point sets to the compact base
through mass-preserving quantisation. -/
private theorem compactQnum_nonneg [Nonempty K] : 0 ≤ compactQnum ρ β lam 𝒞 g := by
  obtain ⟨q, hq, hfin, hqε⟩ := CompactSpace.exists_quantization_seq (K := K)
  exact ge_of_tendsto' (tendsto_compactQnum_map ρ hβ hlam 𝒞 g hq
    tendsto_one_div_add_atTop_nhds_zero_nat hqε) fun n ↦
    compactQnum_map_nonneg ρ hβ hlam 𝒞 g (hq n) (hfin n)

private theorem compactQ_nonneg [Nonempty K] : 0 ≤ compactQ ρ β lam 𝒞 g :=
  div_nonneg (compactQnum_nonneg ρ hβ hlam 𝒞 g) (sq_nonneg _)

/-- **AM–GM**: `compactQnum ≤ D · ∫ C(x,x) S_{λ+1}(g x) dρ`. -/
private theorem compactQnum_le :
    compactQnum ρ β lam 𝒞 g ≤
      compactD β lam ρ g * ∫ x, 𝒞.C x x * frozenInner (lam + 1) β (g x) ∂ρ := by
  set P : K → ℝ := fun x ↦ 𝒞.C x x * frozenInner (lam + 1) β (g x) with hP
  set L : K → ℝ := fun x ↦ frozenInner lam β (g x) with hL
  have hPc : Continuous P := continuous_diag_fluctuation hβ hlam 𝒞 g
  have hLc : Continuous L := (continuous_frozenInner hlam hβ).comp g.continuous
  have hP0 : ∀ x, 0 ≤ P x := fun x ↦
    mul_nonneg (𝒞.diag_nonneg x) (frozenInner_pos (by linarith) hβ _).le
  have hpt : ∀ z : K × K, 2 * bilocalC β lam 𝒞 g z ≤ P z.1 * L z.2 + L z.1 * P z.2 := by
    intro z
    have hL1 := frozenInner_pos hlam hβ (g z.1)
    have hL2 := frozenInner_pos hlam hβ (g z.2)
    have hS1 := frozenInner_pos (by linarith : 0 < lam + 1) hβ (g z.1)
    have h1 := fluctuation_half_sq_le hβ hlam (g z.1)
    have h2 := fluctuation_half_sq_le hβ hlam (g z.2)
    have hC := 𝒞.sq_le z.1 z.2
    have hc1 := 𝒞.diag_nonneg z.1
    have hc2 := 𝒞.diag_nonneg z.2
    refine two_mul_le_add_of_sq_le (mul_nonneg (hP0 _) hL2.le) (mul_nonneg hL1.le (hP0 _)) ?_
    simp only [bilocalC, hP, hL]
    calc (𝒞.C z.1 z.2 * frozenInner (lam + 1 / 2) β (g z.1) *
          frozenInner (lam + 1 / 2) β (g z.2)) ^ 2
        = 𝒞.C z.1 z.2 ^ 2 * (frozenInner (lam + 1 / 2) β (g z.1) ^ 2 *
            frozenInner (lam + 1 / 2) β (g z.2) ^ 2) := by ring
      _ ≤ (𝒞.C z.1 z.1 * 𝒞.C z.2 z.2) *
            ((frozenInner lam β (g z.1) * frozenInner (lam + 1) β (g z.1)) *
            (frozenInner lam β (g z.2) * frozenInner (lam + 1) β (g z.2))) :=
          mul_le_mul hC (mul_le_mul h1 h2 (sq_nonneg _) (mul_pos hL1 hS1).le) (by positivity)
            (mul_nonneg hc1 hc2)
      _ = _ := by ring
  have hbil : Integrable (bilocalC β lam 𝒞 g) (ρ.prod ρ) :=
    Continuous.integrable_of_compactSpace _ (continuous_bilocalC hβ hlam 𝒞 g)
  have hPint : Integrable P ρ := Continuous.integrable_of_compactSpace _ hPc
  have hLint : Integrable L ρ := Continuous.integrable_of_compactSpace _ hLc
  have hmono : ∫ z, 2 * bilocalC β lam 𝒞 g z ∂(ρ.prod ρ) ≤
      ∫ z, (P z.1 * L z.2 + L z.1 * P z.2) ∂(ρ.prod ρ) :=
    integral_mono (hbil.const_mul 2) ((hPint.mul_prod hLint).add (hLint.mul_prod hPint))
      fun z ↦ hpt z
  have hRHS : ∫ z, (P z.1 * L z.2 + L z.1 * P z.2) ∂(ρ.prod ρ) =
      2 * ((∫ x, P x ∂ρ) * ∫ x, L x ∂ρ) := by
    rw [integral_add (hPint.mul_prod hLint) (hLint.mul_prod hPint), integral_prod_mul,
      integral_prod_mul]
    ring
  rw [integral_const_mul, hRHS] at hmono
  have hD : compactD β lam ρ g = ∫ x, L x ∂ρ := rfl
  rw [hD]
  unfold compactQnum
  linarith

private theorem compactQ_le_compactDiag (hρ : ρ ≠ 0) :
    compactQ ρ β lam 𝒞 g ≤ compactDiag ρ β lam 𝒞 g := by
  have hD := compactD_pos ρ hβ hlam hρ g
  unfold compactQ compactDiag
  rw [div_le_div_iff₀ (by positivity) hD]
  calc compactQnum ρ β lam 𝒞 g * compactD β lam ρ g
      ≤ (compactD β lam ρ g * ∫ x, 𝒞.C x x * frozenInner (lam + 1) β (g x) ∂ρ) *
          compactD β lam ρ g := mul_le_mul_of_nonneg_right (compactQnum_le ρ hβ hlam 𝒞 g) hD.le
    _ = _ := by ring

theorem compactV_nonneg [Nonempty K] (hρ : ρ ≠ 0) : 0 ≤ compactV ρ β lam 𝒞 g := by
  unfold compactV
  linarith [compactQ_le_compactDiag ρ hβ hlam 𝒞 g hρ]

private theorem compactV_le_compactDiag [Nonempty K] :
    compactV ρ β lam 𝒞 g ≤ compactDiag ρ β lam 𝒞 g := by
  unfold compactV
  linarith [compactQ_nonneg ρ hβ hlam 𝒞 g]

omit 𝒞 in
/-- **`M₂ ≤ 2λ/β + R²/4`** for `‖g‖ ≤ R`. -/
private theorem compactM2_le (hρ : ρ ≠ 0) {R : ℝ} (hR : ‖g‖ ≤ R) :
    compactM2 β lam ρ g ≤ 2 * lam / β + R ^ 2 / 4 := by
  have hD := compactD_pos ρ hβ hlam hρ g
  unfold compactM2
  rw [div_le_iff₀ hD]
  unfold compactD
  rw [← integral_const_mul]
  refine integral_mono (integrable_fluctuation_comp ρ hβ (by linarith) g)
    ((integrable_fluctuation_comp ρ hβ hlam g).const_mul _) fun x ↦ ?_
  refine (fluctuation_succ_le hβ hlam (g x)).trans
    (mul_le_mul_of_nonneg_right ?_ (frozenInner_pos hlam hβ _).le)
  have hgx' : |g x| ≤ ‖g‖ := by
    have := g.norm_coe_le_norm x
    rwa [Real.norm_eq_abs] at this
  have hgx : max (g x) 0 ≤ R := max_le ((le_abs_self _).trans (hgx'.trans hR))
    ((norm_nonneg g).trans hR)
  have : max (g x) 0 ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (le_max_right _ _) hgx 2
  linarith

omit 𝒞 in
/-- **`|H| ≤ R(√(2λ/β) + R/2)`** for `‖g‖ ≤ R`. -/
theorem abs_compactH_le (hρ : ρ ≠ 0) {R : ℝ} (hR : ‖g‖ ≤ R) :
    |compactH β lam ρ g| ≤ R * (Real.sqrt (2 * lam / β) + R / 2) := by
  have hD := compactD_pos ρ hβ hlam hρ g
  have hR0 : 0 ≤ R := (norm_nonneg g).trans hR
  have hB : 0 ≤ 2 * lam / β := div_nonneg (by linarith) hβ.le
  unfold compactH
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  refine (norm_integral_le_integral_norm
    (fun x ↦ g x * frozenInner (lam + 1 / 2) β (g x))).trans ?_
  unfold compactD
  rw [← integral_const_mul]
  refine integral_mono (Continuous.integrable_of_compactSpace _ (g.continuous.mul
    ((continuous_frozenInner (by linarith) hβ).comp g.continuous))).norm
    ((integrable_fluctuation_comp ρ hβ hlam g).const_mul _) fun x ↦ ?_
  have hgx : |g x| ≤ R := by
    have := g.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at this
    exact this.trans hR
  have hmax : max (g x) 0 ≤ R := max_le ((le_abs_self _).trans hgx) hR0
  have hsq : Real.sqrt (2 * lam / β + max (g x) 0 ^ 2 / 4) ≤ Real.sqrt (2 * lam / β) + R / 2 := by
    refine (Real.sqrt_le_sqrt ?_).trans ((sqrt_le_sqrt_add (2 * lam / β) R hB).trans ?_)
    · have := pow_le_pow_left₀ (le_max_right _ _) hmax 2
      linarith
    · rw [abs_of_nonneg hR0]
  have hhalf := fluctuation_half_le hβ hlam (g x)
  have hS := frozenInner_pos hlam hβ (g x)
  have hS' := frozenInner_pos (by linarith : 0 < lam + 1 / 2) hβ (g x)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hS']
  calc |g x| * frozenInner (lam + 1 / 2) β (g x)
      ≤ R * (Real.sqrt (2 * lam / β + max (g x) 0 ^ 2 / 4) * frozenInner lam β (g x)) :=
        mul_le_mul hgx hhalf hS'.le hR0
    _ ≤ R * ((Real.sqrt (2 * lam / β) + R / 2) * frozenInner lam β (g x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hS.le) hR0
    _ = _ := by ring

private theorem compactDiag_le (hρ : ρ ≠ 0) {c : ℝ} (hc : ∀ x, 𝒞.C x x ≤ c) :
    compactDiag ρ β lam 𝒞 g ≤ c * compactM2 β lam ρ g := by
  have hD := compactD_pos ρ hβ hlam hρ g
  unfold compactDiag compactM2
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hD, ← integral_const_mul]
  exact integral_mono
    (Continuous.integrable_of_compactSpace _ (continuous_diag_fluctuation hβ hlam 𝒞 g))
    ((integrable_fluctuation_comp ρ hβ (by linarith) g).const_mul _) fun x ↦
    mul_le_mul_of_nonneg_right (hc x) (frozenInner_pos (by linarith) hβ _).le

/-- **`0 ≤ V ≤ c(2λ/β + R²/4)`** when `C(x,x) ≤ c` and `‖g‖ ≤ R`. -/
theorem compactV_le [Nonempty K] (hρ : ρ ≠ 0) {c R : ℝ} (hc : ∀ x, 𝒞.C x x ≤ c) (hR : ‖g‖ ≤ R) :
    compactV ρ β lam 𝒞 g ≤ c * (2 * lam / β + R ^ 2 / 4) := by
  have hc0 : 0 ≤ c := (𝒞.diag_nonneg (Classical.arbitrary K)).trans (hc _)
  calc compactV ρ β lam 𝒞 g ≤ compactDiag ρ β lam 𝒞 g := compactV_le_compactDiag ρ hβ hlam 𝒞 g
    _ ≤ c * compactM2 β lam ρ g := compactDiag_le ρ hβ hlam 𝒞 g hρ hc
    _ ≤ c * (2 * lam / β + R ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (compactM2_le ρ hβ hlam g hρ hR) hc0

/-! ### Convergence under quantisation -/

private theorem tendsto_compactDiag_map (hρ : ρ ≠ 0) {q : ℕ → K → K} (hq : ∀ n, Measurable (q n))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n ↦ compactDiag (ρ.map (q n)) β lam 𝒞 g) atTop
      (𝓝 (compactDiag ρ β lam 𝒞 g)) := by
  simp_rw [compactDiag_map ρ hβ hlam 𝒞 g (hq _)]
  exact (tendsto_integral_comp_quantize ρ ⟨_, continuous_diag_fluctuation hβ hlam 𝒞 g⟩ hq hε
    hqε).div (tendsto_compactD_map ρ hβ hlam g hq hε hqε) (compactD_pos ρ hβ hlam hρ g).ne'

private theorem tendsto_compactQ_map (hρ : ρ ≠ 0) {q : ℕ → K → K} (hq : ∀ n, Measurable (q n))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n ↦ compactQ (ρ.map (q n)) β lam 𝒞 g) atTop (𝓝 (compactQ ρ β lam 𝒞 g)) := by
  unfold compactQ
  exact (tendsto_compactQnum_map ρ hβ hlam 𝒞 g hq hε hqε).div
    ((tendsto_compactD_map ρ hβ hlam g hq hε hqε).pow 2)
    (pow_ne_zero 2 (compactD_pos ρ hβ hlam hρ g).ne')

/-- **`V` converges under quantisation.** -/
theorem tendsto_compactV_map (hρ : ρ ≠ 0) {q : ℕ → K → K} (hq : ∀ n, Measurable (q n))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n ↦ compactV (ρ.map (q n)) β lam 𝒞 g) atTop (𝓝 (compactV ρ β lam 𝒞 g)) := by
  unfold compactV
  exact (tendsto_compactDiag_map ρ hβ hlam 𝒞 g hρ hq hε hqε).sub
    (tendsto_compactQ_map ρ hβ hlam 𝒞 g hρ hq hε hqε)

end Kernel

end SingularLearningTheory.GaussianPosterior
