/-
Copyright (c) 2026 Matthijs Hogervorst. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthijs Hogervorst
-/
import Mathlib

/-!
# Derivative of the Gauss hypergeometric function ₂F₁

We prove the parameter-shift derivative identity
$$\frac{d}{dx}\,{}_2F_1(a,b;c;x) = \frac{ab}{c}\,{}_2F_1(a+1,b+1;c+1;x)$$
inside the unit disk of convergence, over `𝕂 = ℝ` or `ℂ` (`RCLike`).

The proof has two parts, matching the natural split:
* `coeff_succ_eq` — a purely algebraic ("formal") identity on the series coefficients;
* `hasDerivAt_ordinaryHypergeometric` — the analytic statement, obtained by
  differentiating the power series term by term inside the disk of convergence.
-/

open FormalMultilinearSeries Polynomial

variable {𝕂 : Type*} [RCLike 𝕂]

/-- **Formal step.** The coefficient identity underlying the derivative formula:
`(n+1) · cₙ₊₁(a,b,c) = (ab/c) · cₙ(a+1,b+1,c+1)`, where `cₙ` is the `n`-th
`ordinaryHypergeometric` coefficient. This is a field identity (no analysis), powered by the
Pochhammer recurrence `(x)_{n+1} = x · (x+1)_n`. -/
lemma coeff_succ_eq (a b c : 𝕂) (n : ℕ) :
    ((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1)
      = a * b / c * ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n := by
  -- The Pochhammer parameter-shift recurrence, evaluated at any point.
  have key : ∀ z : 𝕂, (ascPochhammer 𝕂 (n + 1)).eval z
      = z * (ascPochhammer 𝕂 n).eval (z + 1) := fun z => by
    rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one]
  have hn1 : ((n : 𝕂) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hfac : (n.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfact : ((n + 1).factorial : 𝕂) = ((n : 𝕂) + 1) * (n.factorial : 𝕂) := by
    rw [Nat.factorial_succ]; push_cast; ring
  simp only [ordinaryHypergeometricCoefficient]
  rw [key a, key b, key c, hfact]
  set X := (ascPochhammer 𝕂 n).eval (a + 1)
  set Y := (ascPochhammer 𝕂 n).eval (b + 1)
  set Z := (ascPochhammer 𝕂 n).eval (c + 1)
  simp only [mul_inv]
  field_simp

/-- **Analytic step / main result.** The Gauss hypergeometric function is differentiable inside its
unit disk of convergence, with
`d/dx ₂F₁(a,b;c;x) = (ab/c) · ₂F₁(a+1,b+1;c+1;x)`,
assuming none of `a, b, c` is a non-positive integer (so the radius of convergence is `1`).

The analytic content — that an analytic function may be differentiated term by term inside its
disk of convergence — is supplied entirely by `HasFPowerSeriesOnBall.fderiv`; the coefficient
bookkeeping is `coeff_succ_eq`. -/
theorem hasDerivAt_ordinaryHypergeometric (a b c : 𝕂)
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c)
    {x : 𝕂} (hx : ‖x‖ < 1) :
    HasDerivAt (₂F₁ a b c) (a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x) x := by
  -- The shifted parameters also avoid the non-positive integers.
  have habc' : ∀ kn : ℕ, (kn : 𝕂) ≠ -(a + 1) ∧ (kn : 𝕂) ≠ -(b + 1) ∧ (kn : 𝕂) ≠ -(c + 1) := by
    refine fun kn => ⟨fun h => (habc (kn + 1)).1 ?_, fun h => (habc (kn + 1)).2.1 ?_,
      fun h => (habc (kn + 1)).2.2 ?_⟩ <;> · push_cast; linear_combination h
  -- Both series have radius of convergence `1`.
  have hpr : (ordinaryHypergeometricSeries 𝕂 a b c).radius = 1 :=
    ordinaryHypergeometricSeries_radius_eq_one 𝕂 a b c habc
  have hqr : (ordinaryHypergeometricSeries 𝕂 (a + 1) (b + 1) (c + 1)).radius = 1 :=
    ordinaryHypergeometricSeries_radius_eq_one 𝕂 (a + 1) (b + 1) (c + 1) habc'
  set p := ordinaryHypergeometricSeries 𝕂 a b c with hpdef
  set q := ordinaryHypergeometricSeries 𝕂 (a + 1) (b + 1) (c + 1) with hqdef
  have hxn : (‖x‖₊ : ENNReal) < 1 := by exact_mod_cast hx
  have hxb : x ∈ Metric.eball (0 : 𝕂) 1 := by
    rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]; exact hxn
  -- `₂F₁ a b c` and `(ab/c) • ₂F₁ (a+1) (b+1) (c+1)` have power series on the unit ball.
  have hP : HasFPowerSeriesOnBall (₂F₁ a b c) p 0 1 := by
    have h := p.hasFPowerSeriesOnBall (by rw [hpr]; norm_num); rwa [hpr] at h
  have hQ : HasFPowerSeriesOnBall (₂F₁ (a + 1) (b + 1) (c + 1)) q 0 1 := by
    have h := q.hasFPowerSeriesOnBall (by rw [hqr]; norm_num); rwa [hqr] at h
  -- LIBRARY term-by-term differentiation: the derivative's power series is `p.derivSeries`.
  have hsumF : HasSum (fun n => p.derivSeries n fun _ => x) (fderiv 𝕂 (₂F₁ a b c) x) := by
    simpa using (hP.fderiv).hasSum hxb
  -- Evaluating the (linear) Fréchet derivative at `1` turns this into the scalar derivative,
  -- with the reindexed coefficients `(n+1)•cₙ₊₁` (this is `derivSeries_coeff_one`).
  set L : (𝕂 →L[𝕂] 𝕂) →L[𝕂] 𝕂 := ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂) with hL
  have hfun : (fun n => L (p.derivSeries n fun _ => x))
      = fun n => (x ^ n) • ((n + 1) • p.coeff (n + 1)) := by
    funext n
    rw [hL, ContinuousLinearMap.apply_apply, apply_eq_pow_smul_coeff,
      ContinuousLinearMap.smul_apply, derivSeries_coeff_one]
  have hderiv : HasSum (fun n => (x ^ n) • ((n + 1) • p.coeff (n + 1)))
      (deriv (₂F₁ a b c) x) := by
    have h := L.hasSum hsumF
    rw [hfun] at h
    rwa [hL, ContinuousLinearMap.apply_apply, fderiv_apply_one_eq_deriv] at h
  -- The scaled shifted series sums to `(ab/c) • ₂F₁ (a+1) (b+1) (c+1) x`.
  have hsumG : HasSum (fun n => (a * b / c) • (x ^ n • q.coeff n))
      ((a * b / c) • ₂F₁ (a + 1) (b + 1) (c + 1) x) := by
    have h := (hQ.const_smul (c := a * b / c)).hasSum hxb
    simpa only [zero_add, FormalMultilinearSeries.smul_apply,
      ContinuousMultilinearMap.smul_apply, apply_eq_pow_smul_coeff, Pi.smul_apply] using h
  -- Term-by-term, the two series agree (this is where `coeff_succ_eq` enters).
  have hterm : ∀ n, (x ^ n) • ((n + 1) • p.coeff (n + 1))
      = (a * b / c) • (x ^ n • q.coeff n) := by
    intro n
    have hp : p.coeff (n + 1) = ordinaryHypergeometricCoefficient a b c (n + 1) := by
      simp only [hpdef, ordinaryHypergeometricSeries, coeff_ofScalars]
    have hq : q.coeff n = ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n := by
      simp only [hqdef, ordinaryHypergeometricSeries, coeff_ofScalars]
    have hinner : ((n + 1) • p.coeff (n + 1)) = (a * b / c) • q.coeff n := by
      rw [hp, hq, nsmul_eq_mul, smul_eq_mul]; push_cast; exact coeff_succ_eq a b c n
    rw [hinner, smul_comm]
  -- Equal sequences have equal sums, giving the value of the derivative.
  have hval : deriv (₂F₁ a b c) x = a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x := by
    have h := hderiv.unique (by simpa only [← hterm] using hsumG)
    rwa [smul_eq_mul] at h
  -- `₂F₁ a b c` is analytic, hence differentiable, at `x`; combine with the value above.
  have hdiff : DifferentiableAt 𝕂 (₂F₁ a b c) x := (hP.analyticOnNhd x hxb).differentiableAt
  simpa only [hval] using hdiff.hasDerivAt
