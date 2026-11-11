/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Local analytic isomorphisms of a normed space over `K = ℝ` or `ℂ`

A map `f : E → E` of a normed space over `𝕜` (`[RCLike 𝕜]`) is a local analytic isomorphism at
`a` when it is analytic at `a` with invertible derivative. Over a general `E` the invariant is
`ContinuousLinearMap.IsInvertible` (a determinant needs coordinates); on `Fin n → 𝕜` the two
agree (`isLocalAnalyticIsoAt_iff_det_ne_zero` in `Inverse.lean`), and for `𝕜 = ℝ` on
`Fin n → ℝ` the notion is that of `Analytic.IsLocalAnalyticIsoAt` in
`SLT/Analytic/AnalyticIso/Inverse.lean`, which is stated with `det ≠ 0`. This is the
hypothesis of the inverse function theorem in the form the sources use it ("by the implicit
function theorem", [BM97, §1]; [Hir64, Chapter 0, §1, p. 121]).
-/

@[expose] public section

namespace Analytic

variable (𝕜 : Type) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `f : E → E` is a local analytic isomorphism over `𝕜` at `a` if it is analytic at `a` and its
derivative there is an invertible continuous linear map. -/
def IsLocalAnalyticIsoAt (f : E → E) (a : E) : Prop :=
  AnalyticAt 𝕜 f a ∧ (fderiv 𝕜 f a).IsInvertible

end Analytic
