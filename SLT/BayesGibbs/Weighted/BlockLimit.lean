/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.QuantitativeApprox
public import SLT.FreeEnergy.FrozenKernel

/-!
# Marked radial integrals in block coordinates

In the block coordinates of a normal crossing, with $r + 1$ primary coordinates whose exponents
$k, h$ attain $\lambda = (h_j + 1)/(2k_j)$ and secondary exponents $k', h'$, the integral
`SingularLearningTheory.NormalCrossing.blockIntegral` with radial power $K^p$ and amplitude
$\varphi$, scaled by $n^{\lambda + p}/(\log n)^r$, converges to its frozen limit for every
$p \ge 0$. The convergence is uniform over fields $\xi$ and amplitudes $\varphi$ that are bounded
and have a Lipschitz bound in the primary coordinates. The case $p = 0$ is
`SingularLearningTheory.uniform_approx`, and the general case follows by shifting $h$ by $2kp$. The
cases $p = 1/2$ and $p = 1$ give the first and second feature insertions in the posterior.

## Main results

* `SingularLearningTheory.uniform_approx_radial_insertion`: the uniform limit.
* `SingularLearningTheory.NormalCrossing.marked_amplitude_primary_bound`: the product of two bounded
functions with a Lipschitz bound in the primary coordinates has one too, so a chart weight times a
mark is an amplitude to which the limit applies. *
`SingularLearningTheory.NormalCrossing.abs_blockIntegral_le_const_amplitude`: an amplitude bounded
by $P$ gives an integral at most the integral with the constant amplitude $P$, which controls the
charts that are not essential.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory

open SingularLearningTheory.NormalCrossing

/-- The block insertion limit for every nonnegative radial power. The
amplitude is arbitrary signed bounded measurable and primary-Lipschitz; thus
one may use the original chart weight times any bounded Lipschitz mark.

The p=1/2 and p=1 cases are the first and second feature insertions needed by
the Bayes/Gibbs quartet. No new frozen-kernel estimates are required. -/
theorem uniform_approx_radial_insertion
    {r m' : ℕ} {k : Fin (r + 1) → ℕ} {h : Fin (r + 1) → ℝ}
    {k' : Fin m' → ℕ} {h' : Fin m' → ℝ} {lam b β p : ℝ}
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1)
    (hb : 0 < b) (hβ : 0 < β) (hp : 0 ≤ p)
    (M P Lξ Lφ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℝ, ∀ n : ℝ, N ≤ n →
      ∀ ξ φ : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) → ℝ,
      Measurable ξ → Measurable φ →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z| ≤ M) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |φ z| ≤ P) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b,
        |ξ z - ξ (0, z.2)| ≤ Lξ * ∑ j, z.1 j) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b,
        |φ z - φ (0, z.2)| ≤ Lφ * ∑ j, z.1 j) →
      |n ^ (lam + p) / Real.log n ^ r * NormalCrossing.blockIntegral k h k' h' b β p n ξ φ -
        NormalCrossing.gammaConst k h lam b * ∫ v in cube m' b,
          NormalCrossing.secondaryWeight k' h' lam v * φ (0, v) *
            ∫ t in Ioi 0, t ^ (lam + p - 1) *
              Real.exp (-(β * t) + β * Real.sqrt t * ξ (0, v))| ≤ ε := by
  have hlam' : ∀ j, ((h j + 2 * k j * p) + 1) / (2 * k j) = lam + p := by
    intro j
    have hj : (0 : ℝ) < k j := by exact_mod_cast hk j
    have hden : (2 * (k j : ℝ)) ≠ 0 := by positivity
    have he := (div_eq_iff hden).mp (hlam j)
    apply (div_eq_iff hden).mpr
    nlinarith
  have hsec' : ∀ j, 2 * k' j * (lam + p) < (h' j + 2 * k' j * p) + 1 := by
    intro j
    nlinarith [hsec j]
  obtain ⟨N, hN⟩ := uniform_approx hk hlam' (by linarith) hsec' hb hβ M P Lξ Lφ hε
  refine ⟨N, fun n hn ξ φ hξm hφm hξ hφ hξL hφL ↦ ?_⟩
  rw [blockIntegral_shift k h k' h' b β p n ξ φ,
    ← frozenLimit_shift k h k' h' lam b β p
      (fun v ↦ ξ (0, v)) (fun v ↦ φ (0, v))]
  exact hN n hn ξ φ hξm hφm hξ hφ hξL hφL

/-- Product amplitudes inherit the primary Lipschitz bound. This is the
only added amplitude estimate needed to apply the radial insertion limit. -/
theorem NormalCrossing.marked_amplitude_primary_bound {U : Type*} {w a : U → ℝ} {π : U → U}
    {s : U → ℝ} {P A Lw La : ℝ}
    (hw : ∀ u, |w u| ≤ P) (ha : ∀ u, |a u| ≤ A)
    (hwL : ∀ u, |w u - w (π u)| ≤ Lw * s u)
    (haL : ∀ u, |a u - a (π u)| ≤ La * s u) (hP : 0 ≤ P) (hA : 0 ≤ A) :
    ∀ u, |w u * a u - w (π u) * a (π u)| ≤ (A * Lw + P * La) * s u := by
  intro u
  have e : w u * a u - w (π u) * a (π u) =
      (w u - w (π u)) * a u + w (π u) * (a u - a (π u)) := by ring
  rw [e]
  calc
    _ ≤ |(w u - w (π u)) * a u| + |w (π u) * (a u - a (π u))| := abs_add_le _ _
    _ = |a u| * |w u - w (π u)| + |w (π u)| * |a u - a (π u)| := by
      rw [abs_mul, abs_mul]
      ring
    _ ≤ A * (Lw * s u) + P * (La * s u) :=
      add_le_add (mul_le_mul (ha u) (hwL u) (abs_nonneg _) hA)
        (mul_le_mul (hw (π u)) (haL u) (abs_nonneg _) hP)
    _ = _ := by ring

/-- Signed amplitudes are dominated by the constant amplitude P. This is the
additional estimate needed for nonessential marked charts. -/
theorem NormalCrossing.abs_blockIntegral_le_const_amplitude
    {m m' : ℕ} (k : Fin m → ℕ) {h : Fin m → ℝ} (k' : Fin m' → ℕ)
    {h' : Fin m' → ℝ} {b β p n P M : ℝ}
    {ξ a : (Fin m → ℝ) × (Fin m' → ℝ) → ℝ}
    (hh : ∀ j, -1 < h j) (hh' : ∀ j, -1 < h' j) (hb : 0 < b)
    (hβ : 0 ≤ β) (hp : 0 ≤ p) (hn : 0 ≤ n) (hP : 0 ≤ P)
    (hξm : Measurable ξ)
    (hξ : ∀ z ∈ cube m b ×ˢ cube m' b, |ξ z| ≤ M)
    (ha : ∀ z ∈ cube m b ×ˢ cube m' b, |a z| ≤ P) :
    |NormalCrossing.blockIntegral k h k' h' b β p n ξ a| ≤ NormalCrossing.blockIntegral k h k' h' b
        β p n ξ
        (fun _ ↦ P) := by
  have hS : MeasurableSet (cube m b ×ˢ cube m' b) :=
    measurableSet_Icc.prod
      measurableSet_Icc
  have hint := integrable_blockIntegral_integrand k k' hh hh' hb hβ hp hn hξm
    (measurable_const (a := P)) hξ (fun _ _ ↦ (abs_of_nonneg hP).le)
  rw [restrict_ocube_eq, restrict_ocube_eq, Measure.prod_restrict] at hint
  rw [NormalCrossing.blockIntegral, NormalCrossing.blockIntegral, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hint
  filter_upwards [ae_restrict_mem hS] with z hz
  have hK : 0 ≤ potential k k' z :=
    potential_nonneg k k' (fun j ↦ hz.1.1 j)
      (fun j ↦ hz.2.1 j)
  have hw : 0 ≤ NormalCrossing.monomialWeight h h' z :=
    monomialWeight_nonneg h h' (fun j ↦ hz.1.1 j)
      (fun j ↦ hz.2.1 j)
  have hnonneg : 0 ≤ potential k k' z ^ p *
      Real.exp (-(n * β * potential k k' z) +
        Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
      NormalCrossing.monomialWeight h h' z :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hK _) (Real.exp_pos _).le) hw
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
  exact mul_le_mul_of_nonneg_left (ha z hz) hnonneg

end SingularLearningTheory
