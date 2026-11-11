import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import SLT.SingularIntegrals

open Verso.Genre
open Verso.Genre.Manual
open Informal
open SingularLearningTheory MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option verso.blueprint.autoDeps true
set_option maxHeartbeats 800000

#doc (Manual) "Singular learning machines (Chapter 7)" =>

Of Chapter 7 the library covers Theorem 7.1, the characterisations of the learning coefficient.
The worked examples of §7.2–§7.8 are not on the statement surface described here.

# Learning coefficient (§7.1)

::::definition "def:volume" (lean := "SingularLearningTheory.laplaceIntegral, SingularLearningTheory.sublevelVolume, SingularLearningTheory.stateDensity")
%%%
paperIdentity := some { label := "[Wat09, eqs. (4.1), (4.8), (4.9)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The singular integral $`Z_0(n) = \int_W e^{-nK(w)} \varphi(w)\,dw` (eq. (4.1)), the *volume*
$`V(t) = \int_W \mathbf{1}(K(w) < t)\, \varphi(w)\,dw` (eq. (4.9)) and the *state density*
$`v(t) = \int \delta(t - K(w))\, \varphi(w)\,dw` (eq. (4.8)).

`laplaceIntegral K φ W β n` is $`\int_W e^{-n\beta K(w)} \varphi(w)\,dw`, with an inverse
temperature $`\beta` (the book's integral is $`\beta = 1`); `sublevelVolume K φ W t` is
$`\int_W \mathbf{1}(K(w) \le t)\, \varphi(w)\,dw`; and `stateDensity K φ W` is the derivative of
`sublevelVolume K φ W`.

::::

::::theorem "thm:7_1" (lean := "SingularLearningTheory.tendsto_rpow_div_log_pow_mul_laplaceIntegral, SingularLearningTheory.tendsto_neg_log_laplaceIntegral_div_log, SingularLearningTheory.tendsto_stateDensity_div_rpow_mul_neg_log_pow, SingularLearningTheory.tendsto_log_sublevelVolume_ratio_div_log")
%%%
paperIdentity := some { label := "[Wat09, Theorem 7.1]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The learning coefficient $`\lambda` and its order $`m` are characterised by: (1) the asymptotics
of $`\int e^{-nK(w)} \varphi(w)\,dw \sim c_1\, n^{-\lambda} (\log n)^{m-1}`; (2)
$`-\log \int e^{-nK} \varphi \,/\, \log n \to \lambda`; (3) the state density
$`v(t) \sim c_2\, t^{\lambda - 1} (-\log t)^{m-1}`; (4)
$`\log\bigl(V(at)/V(t)\bigr) / \log a \to \lambda`.

The four theorems share the hypotheses of {bpref "thm:6_6"}[Theorem 6.6]: $`W` compact, $`K`
real analytic near $`W` and nonnegative on it, Fundamental Condition (II) and the zero-set
conditions ({bpref "def:zero_set"}[]); and they take the singularity type $`(\lambda, m)` of
$`K` and $`\varphi` ({bpref "def:2_7"}[]), with $`\lambda > 0` and $`m \ge 1`. In terms of the
objects of {bpref "def:volume"}[]:

1. for every $`\beta > 0` there is $`c_1 > 0` with
   $`n^\lambda (\log n)^{-(m-1)} Z_0(n) \to c_1` as $`n \to \infty`
   (`tendsto_rpow_div_log_pow_mul_laplaceIntegral`);
2. $`-\log Z_0(n) / \log n \to \lambda` at $`\beta = 1`
   (`tendsto_neg_log_laplaceIntegral_div_log`);
3. $`V` is differentiable on some interval $`(0, \varepsilon)` and there is $`c_2 > 0` with
   $`v(t) / (t^{\lambda - 1} (-\log t)^{m-1}) \to c_2` as $`t \to 0^+`
   (`tendsto_stateDensity_div_rpow_mul_neg_log_pow`);
4. $`\log(V(at)/V(t)) / \log a \to \lambda` as $`t \to 0^+`, for every $`a > 0`, $`a \ne 1`
   (`tendsto_log_sublevelVolume_ratio_div_log`).

::::
