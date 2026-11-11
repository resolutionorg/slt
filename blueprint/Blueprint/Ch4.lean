import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import SLT.Analysis.Mellin
import SLT.SingularIntegrals

open Verso.Genre
open Verso.Genre.Manual
open Informal
open SingularLearningTheory MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option verso.blueprint.autoDeps true

#doc (Manual) "Mellin transforms and singular integrals (Chapter 4)" =>

Chapter 4 relates the zeta function to the singular integrals of Chapter 6 through the Mellin
transform (§4.3), and computes the singular integrals of a normal crossing function (§4.4), which
are the integrals over the pieces of Theorem 6.5 that the proofs of Chapter 6 reduce to.

# Mellin transform (§4.3)

::::definition "def:4_8" (lean := "SingularLearningTheory.mellinTransform, SingularLearningTheory.inverseMellinTrunc")
%%%
paperIdentity := some { label := "[Wat09, Definition 4.8, Remark 4.3 (1)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The *Mellin transform* of $`f : (0, \infty) \to \mathbb{R}` is
$$`(\mathcal{M}f)(z) = \int_0^\infty f(t)\, t^z\,dt.`

`mellinTransform f z` is this integral. `inverseMellinTrunc c F t T` is the truncated inverse
integral $`\frac{1}{2\pi i} \int_{c - iT}^{c + iT} F(z)\, t^{-z-1}\,dz` of Remark 4.3 (1),
parametrised by the imaginary coordinate.

::::

::::theorem "thm:mellin_strip" (lean := "SingularLearningTheory.mellinTransform_differentiableOn_strip")
%%%
paperIdentity := some { label := "[Wat09, §4.3]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
If $`f(t)\,t^a` and $`f(t)\,t^b` are integrable on $`(0, \infty)` for $`a < b`, the Mellin
transform of $`f` is holomorphic on the strip $`a < \operatorname{Re} z < b`.
::::

::::theorem "thm:4_5" (lean := "SingularLearningTheory.inverseMellin_tendsto_of_boundedVariation")
%%%
paperIdentity := some { label := "[Wat09, Theorem 4.5]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
(Mellin inversion.) If $`f` has bounded variation near $`t > 0`, the truncated inverse Mellin
integrals of $`\mathcal{M}f` on the line $`\operatorname{Re} z = c` converge, as $`T \to \infty`,
to the average $`(f(t^+) + f(t^-))/2` of the one-sided limits of $`f` at $`t`.

::::

::::theorem "ex:4_7" (lean := "SingularLearningTheory.mellinTransform_power_log")
%%%
paperIdentity := some { label := "[Wat09, Example 4.7]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
For $`a > 0`, $`m \ge 1` and $`\operatorname{Re} z > -\lambda`, the Mellin transform of
$$`f(t) = \mathbf{1}_{(0, a)}(t)\, \frac{a^{-\lambda}}{(m-1)!}\, t^{\lambda - 1} \log(a/t)^{m-1}`
is $`a^z / (z + \lambda)^m`.

::::

# Singular integral of a normal crossing function (§4.4)

::::definition "def:4_10" (lean := "SingularLearningTheory.normalCrossing, SingularLearningTheory.monomialWeight, SingularLearningTheory.monomialRlct, SingularLearningTheory.criticalCoords, SingularLearningTheory.monomialMultiplicity, SingularLearningTheory.toCriticalFace, SingularLearningTheory.normalCrossingIntegral, SingularLearningTheory.normalCrossingIntegral₀, SingularLearningTheory.gammaConst, SingularLearningTheory.normalCrossingCentralPart")
%%%
paperIdentity := some { label := "[Wat09, Definition 4.10, eqs. (4.16), (4.18), (4.19)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
On the cube $`[0, b]^d` (`cube d b`), for exponents $`k, h \in \mathbb{N}^d` with some
$`k_j > 0`: the normal crossing potential $`x^{2k}` (`normalCrossing k`), the weight $`x^h`
(`monomialWeight h`), the threshold $`\lambda = \min_{k_j > 0} (h_j + 1)/(2k_j)`
(`monomialRlct`), the coordinates attaining it (`criticalCoords`) and their number $`m`
(`monomialMultiplicity`, the book's $`r`). The *partition function* of Definition 4.10 is
$$`Z^p(n, \xi, \varphi) = \int_{[0, b]^d} K(x)^p\,
  e^{-n\beta K(x) + \sqrt n \beta \sqrt{K(x)}\, \xi(x)}\, x^h\, \varphi(x)\,dx, \qquad K(x) = x^{2k},`
for continuous $`\xi, \varphi` on the cube (`normalCrossingIntegral`); its case $`\xi = 0`,
$`\varphi = 1` is the singular integral $`Z^p(n)` of eq. (4.18) (`normalCrossingIntegral₀`).
The *central part* $`Y^p(n, \xi, \varphi)` of eq. (4.19) (`normalCrossingCentralPart`) is
$`\gamma_b (\log n)^{m-1} / n^{\lambda + p}` times the integral over $`t > 0` and the face
$`\{x_j = 0,\ j \text{ critical}\}` (`toCriticalFace`) of
$`t^{\lambda + p - 1} e^{-\beta t + \beta \sqrt t\, \xi} \prod_j v_j^{h_j - 2k_j\lambda}\,
\varphi`, with the constant $`\gamma_b` of eq. (4.16) (`gammaConst`).

::::

::::theorem "thm:4_7" (lean := "SingularLearningTheory.normalCrossingIntegral₀_bounds")
%%%
paperIdentity := some { label := "[Wat09, Theorem 4.7]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
For $`b, \beta > 0` and $`p \ge 0` there are $`a_1, a_2 > 0` with
$$`a_1 \frac{(\log n)^{m-1}}{n^{\lambda + p}} \le Z^p(n) \le a_2 \frac{(\log n)^{m-1}}{n^{\lambda + p}}`
for every real $`n \ge 2`, with $`\lambda` and $`m` as in {bpref "def:4_10"}[Definition 4.10].

::::

::::theorem "thm:4_8" (lean := "SingularLearningTheory.normalCrossingIntegral_bounds_of_nonneg")
%%%
paperIdentity := some { label := "[Wat09, Theorem 4.8]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Bounds on the partition function with a field $`\xi` and a weight $`\varphi`: there is $`a_2 > 0`,
and for every continuous $`\varphi \ge 0` on the cube with $`\varphi(0) > 0` there is
$`a_1 > 0`, such that for every continuous $`\xi` and real $`n \ge 2`
$$`a_1 \frac{(\log n)^{m-1}}{n^{\lambda+p}} e^{-\beta \|\xi\|^2/2} \le Z^p(n, \xi, \varphi)
  \le a_2 \frac{(\log n)^{m-1}}{n^{\lambda+p}} e^{\beta \|\xi\|^2/2} \|\varphi\|.`

::::

::::theorem "thm:4_9" (lean := "SingularLearningTheory.abs_normalCrossingIntegral_sub_normalCrossingCentralPart_le")
%%%
paperIdentity := some { label := "[Wat09, Theorem 4.9]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The central part approximates the partition function: there is $`C > 0` such that for all
$`C^1` functions $`\xi, \varphi` on the cube and real $`n \ge 2`
$$`|Z^p(n, \xi, \varphi) - Y^p(n, \xi, \varphi)| \le C \frac{(\log n)^{m-2}}{n^{\lambda+p}}
  e^{\beta\|\xi\|^2/2} \bigl(\beta \|\nabla \xi\| \|\varphi\| + \|\nabla\varphi\| + \|\varphi\|\bigr).`

::::
