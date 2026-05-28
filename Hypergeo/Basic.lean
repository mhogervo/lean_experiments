/-
Copyright (c) 2026 Matthijs Hogervorst. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthijs Hogervorst
-/
import Mathlib

/-!
# Hypergeo

Experiments and (eventually) contributions on the theory of special functions in Lean 4 /
Mathlib, with a focus on the Gauss hypergeometric function `₂F₁` (`ordinaryHypergeometric`).

## Contents

* `ordinaryHypergeometric_symm` — `₂F₁` is symmetric in its first two parameters `a`, `b`.
* `Hypergeo.Deriv` — the parameter-shift derivative identity
  `d/dx ₂F₁(a,b;c;x) = (ab/c) · ₂F₁(a+1,b+1;c+1;x)`, valid inside the unit disk of convergence.

## Relevant Mathlib API

The starting point is `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric`, which defines
`ordinaryHypergeometric` (notation `₂F₁`) and `ordinaryHypergeometricSeries`, establishes the
radius of convergence, and treats the terminating (polynomial) cases. Related material lives under
`Mathlib.Analysis.SpecialFunctions` (`Gamma`, `Beta`, `Pochhammer`).
-/

variable {𝕂 : Type*} {𝔸 : Type*} [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-- `₂F₁` is symmetric in its first two parameters: `₂F₁(a,b;c;x) = ₂F₁(b,a;c;x)`. This is
immediate from the symmetry of the underlying series, `ordinaryHypergeometricSeries_symm`. -/
theorem ordinaryHypergeometric_symm (a b c : 𝕂) (x : 𝔸) :
    ₂F₁ a b c x = ₂F₁ b a c x := by
  unfold ordinaryHypergeometric
  rw [ordinaryHypergeometricSeries_symm]
