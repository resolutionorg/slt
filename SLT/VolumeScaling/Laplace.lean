/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Laplace.Scale
public import SLT.VolumeScaling.Laplace.Representation
public import SLT.VolumeScaling.Laplace.Model
public import SLT.VolumeScaling.Laplace.Asymptotic
public import SLT.VolumeScaling.Laplace.Moments
public import SLT.VolumeScaling.Laplace.Cumulants

/-!
# The deterministic Laplace asymptotic

The modules of the deterministic Laplace asymptotic from `HasLLCOn`: `LaplaceScale` (the target
scale `s^{−λ}(log s)^{θ−1}` and the exponential-domination lemma), `LaplaceRepresentation` (the
layer-cake representation and the tail estimate), `LaplaceModel` (the substitution identity, the
integrability of the head, and the head Θ-bound), `LaplaceAsymptotic`
(the assemblies and the constant-carrying limit / free-energy
forms), `LaplaceMoments` (the weighted-kernel foundation: the
moment kernels, their integrability, the weighted-kernel asymptotic, and
the raw-moment recursion `M_{n+1} = s·A_{n+1} − (n+1)·A_n`),
`LaplaceCumulants` (the leading cumulant limits: the first cumulant
`s·E_s[f] → λ`).
-/

public section
