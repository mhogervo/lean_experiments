/-
Copyright (c) 2026 Matthijs Hogervorst. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthijs Hogervorst
-/
import Hypergeo.Basic
import Hypergeo.Deriv

/-!
# Toward the hypergeometric ODE

This file works toward the Gauss hypergeometric differential equation
`x(1-x) y'' + (c - (a+b+1)x) y' - ab y = 0` for `y = ₂F₁(a,b;c;x)` inside the unit disk.

As stepping stones we establish the Euler-operator ("ladder") contiguous relations, e.g.
`x · d/dx ₂F₁(a,b;c;x) = a (₂F₁(a+1,b;c;x) - ₂F₁(a,b;c;x))`.
-/

open FormalMultilinearSeries Polynomial

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Inside the unit disk, `₂F₁ a b c x` is the sum of its defining power series
`∑ₙ cₙ(a,b,c) xⁿ`, provided none of `a, b, c` is a non-positive integer. -/
theorem hasSum_ordinaryHypergeometric (a b c : 𝕂)
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    HasSum (fun n => ordinaryHypergeometricCoefficient a b c n • x ^ n) (₂F₁ a b c x) := by
  have hpr : (ordinaryHypergeometricSeries 𝕂 a b c).radius = 1 :=
    ordinaryHypergeometricSeries_radius_eq_one 𝕂 a b c habc
  have hxb : x ∈ Metric.eball (0 : 𝕂) 1 := by
    have hxn : (‖x‖₊ : ENNReal) < 1 := by exact_mod_cast hx
    rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]; exact hxn
  have hP : HasFPowerSeriesOnBall (₂F₁ a b c) (ordinaryHypergeometricSeries 𝕂 a b c) 0 1 := by
    have h := (ordinaryHypergeometricSeries 𝕂 a b c).hasFPowerSeriesOnBall (by rw [hpr]; norm_num)
    rwa [hpr] at h
  simpa only [ordinaryHypergeometricSeries_apply_eq, zero_add] using hP.hasSum hxb

/-- Coefficient identity behind the `a`-ladder relation:
`a · (cₙ₊₁(a+1,b,c) − cₙ₊₁(a,b,c)) = (ab/c) · cₙ(a+1,b+1,c+1)`. Pure field algebra. -/
lemma coeff_contiguous_a (a b c : 𝕂) (n : ℕ) :
    a * (ordinaryHypergeometricCoefficient (a + 1) b c (n + 1)
          - ordinaryHypergeometricCoefficient a b c (n + 1))
      = a * b / c * ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n := by
  have eL : ∀ z : 𝕂, (ascPochhammer 𝕂 (n + 1)).eval z = z * (ascPochhammer 𝕂 n).eval (z + 1) :=
    fun z => by
      rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one]
  have eRa : (ascPochhammer 𝕂 (n + 1)).eval (a + 1)
      = (ascPochhammer 𝕂 n).eval (a + 1) * ((a + 1) + n) := ascPochhammer_succ_eval n (a + 1)
  have hn1 : ((n : 𝕂) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hfac : (n.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfact : ((n + 1).factorial : 𝕂) = ((n : 𝕂) + 1) * (n.factorial : 𝕂) := by
    rw [Nat.factorial_succ]; push_cast; ring
  simp only [ordinaryHypergeometricCoefficient]
  rw [eL a, eL b, eL c, eRa, hfact]
  set Xa := (ascPochhammer 𝕂 n).eval (a + 1)
  set Xb := (ascPochhammer 𝕂 n).eval (b + 1)
  set Xc := (ascPochhammer 𝕂 n).eval (c + 1)
  simp only [mul_inv]
  field_simp
  ring

/-- **`a`-ladder (contiguous) relation.** Inside the unit disk,
`x · d/dx ₂F₁(a,b;c;x) = a (₂F₁(a+1,b;c;x) − ₂F₁(a,b;c;x))`. -/
lemma ordinaryHypergeometric_contiguous_a (a b c : 𝕂)
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    x * deriv (₂F₁ a b c) x = a * (₂F₁ (a + 1) b c x - ₂F₁ a b c x) := by
  have ha1 : ∀ kn : ℕ, (kn : 𝕂) ≠ -(a + 1) :=
    fun kn h => (habc (kn + 1)).1 (by push_cast; linear_combination h)
  have habc1 : ∀ kn : ℕ, (kn : 𝕂) ≠ -(a + 1) ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c :=
    fun kn => ⟨ha1 kn, (habc kn).2.1, (habc kn).2.2⟩
  have habc' : ∀ kn : ℕ, (kn : 𝕂) ≠ -(a + 1) ∧ (kn : 𝕂) ≠ -(b + 1) ∧ (kn : 𝕂) ≠ -(c + 1) := by
    refine fun kn => ⟨ha1 kn, fun h => (habc (kn + 1)).2.1 ?_, fun h => (habc (kn + 1)).2.2 ?_⟩ <;>
      · push_cast; linear_combination h
  have hF := hasSum_ordinaryHypergeometric a b c habc hx
  have hF1 := hasSum_ordinaryHypergeometric (a + 1) b c habc1 hx
  have hG := hasSum_ordinaryHypergeometric (a + 1) (b + 1) (c + 1) habc' hx
  rw [(hasDerivAt_ordinaryHypergeometric a b c habc hx).deriv]
  set g : ℕ → 𝕂 := fun n => a * ((ordinaryHypergeometricCoefficient (a + 1) b c n
      - ordinaryHypergeometricCoefficient a b c n) • x ^ n) with hg
  have hLHS : HasSum g (a * (₂F₁ (a + 1) b c x - ₂F₁ a b c x)) := by
    simpa only [hg, sub_smul] using (hF1.sub hF).mul_left a
  have hg0 : g 0 = 0 := by simp [hg, ordinaryHypergeometricCoefficient]
  have hsum_eq : (fun n => g (n + 1))
      = fun n => x * (a * b / c * (ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n
          • x ^ n)) := by
    funext n
    simp only [hg, smul_eq_mul, pow_succ]
    linear_combination (x ^ n * x) * coeff_contiguous_a a b c n
  have hRHS : HasSum (fun n => g (n + 1)) (x * (a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x)) := by
    rw [hsum_eq]; exact (hG.mul_left (a * b / c)).mul_left x
  have key := (hasSum_nat_add_iff (f := g) 1).mp hRHS
  rw [Finset.sum_range_one, hg0, add_zero] at key
  exact (hLHS.unique key).symm

/-- The three-term recurrence satisfied by the hypergeometric coefficients:
`(n+1)(c+n) cₙ₊₁ = (a+n)(b+n) cₙ`, valid when `c + n ≠ 0`. This is the ODE in coefficient form. -/
lemma coeff_recurrence (a b c : 𝕂) (n : ℕ) (hcn : c + (n : 𝕂) ≠ 0) :
    ((n : 𝕂) + 1) * (c + n) * ordinaryHypergeometricCoefficient a b c (n + 1)
      = (a + n) * (b + n) * ordinaryHypergeometricCoefficient a b c n := by
  have ea : (ascPochhammer 𝕂 (n + 1)).eval a = (ascPochhammer 𝕂 n).eval a * (a + n) :=
    ascPochhammer_succ_eval n a
  have eb : (ascPochhammer 𝕂 (n + 1)).eval b = (ascPochhammer 𝕂 n).eval b * (b + n) :=
    ascPochhammer_succ_eval n b
  have ec : (ascPochhammer 𝕂 (n + 1)).eval c = (ascPochhammer 𝕂 n).eval c * (c + n) :=
    ascPochhammer_succ_eval n c
  have hn1 : ((n : 𝕂) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hfac : (n.factorial : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfact : ((n + 1).factorial : 𝕂) = ((n : 𝕂) + 1) * (n.factorial : 𝕂) := by
    rw [Nat.factorial_succ]; push_cast; ring
  simp only [ordinaryHypergeometricCoefficient]
  rw [ea, eb, ec, hfact]
  set Pa := (ascPochhammer 𝕂 n).eval a
  set Pb := (ascPochhammer 𝕂 n).eval b
  set Pc := (ascPochhammer 𝕂 n).eval c
  simp only [mul_inv]
  field_simp

/-- The power series of the derivative: `d/dx ₂F₁(a,b;c;x) = ∑ₙ (n+1) cₙ₊₁ xⁿ` inside the unit
disk. Rides on the derivative lemma and `coeff_succ_eq`; no reindexing needed. -/
lemma hasSum_deriv_ordinaryHypergeometric (a b c : 𝕂)
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    HasSum (fun (n : ℕ) => ((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1) • x ^ n)
      (deriv (₂F₁ a b c) x) := by
  have habc' : ∀ kn : ℕ, (kn : 𝕂) ≠ -(a + 1) ∧ (kn : 𝕂) ≠ -(b + 1) ∧ (kn : 𝕂) ≠ -(c + 1) := by
    refine fun kn => ⟨fun h => (habc (kn + 1)).1 ?_, fun h => (habc (kn + 1)).2.1 ?_,
      fun h => (habc (kn + 1)).2.2 ?_⟩ <;> · push_cast; linear_combination h
  have hG := hasSum_ordinaryHypergeometric (a + 1) (b + 1) (c + 1) habc' hx
  rw [(hasDerivAt_ordinaryHypergeometric a b c habc hx).deriv]
  have heq : (fun (n : ℕ) =>
        ((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1) • x ^ n)
      = fun (n : ℕ) =>
        a * b / c * (ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n • x ^ n) := by
    funext n
    simp only [smul_eq_mul]
    linear_combination (x ^ n) * coeff_succ_eq a b c n
  rw [heq]
  exact hG.mul_left (a * b / c)

/-- The power series of the second derivative:
`d²/dx² ₂F₁(a,b;c;x) = ∑ₙ (n+1)(n+2) cₙ₊₂ xⁿ` inside the unit disk. -/
lemma hasSum_deriv2_ordinaryHypergeometric (a b c : 𝕂)
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    HasSum (fun (n : ℕ) =>
        ((n : 𝕂) + 1) * ((n : 𝕂) + 2) * ordinaryHypergeometricCoefficient a b c (n + 2) • x ^ n)
      (deriv (deriv (₂F₁ a b c)) x) := by
  have habc' : ∀ kn : ℕ, (kn : 𝕂) ≠ -(a + 1) ∧ (kn : 𝕂) ≠ -(b + 1) ∧ (kn : 𝕂) ≠ -(c + 1) := by
    refine fun kn => ⟨fun h => (habc (kn + 1)).1 ?_, fun h => (habc (kn + 1)).2.1 ?_,
      fun h => (habc (kn + 1)).2.2 ?_⟩ <;> · push_cast; linear_combination h
  have hball : Metric.ball (0 : 𝕂) 1 ∈ nhds x :=
    Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using hx)
  have hev : deriv (₂F₁ a b c) =ᶠ[nhds x] fun y => a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) y := by
    filter_upwards [hball] with y hy
    exact (hasDerivAt_ordinaryHypergeometric a b c habc
      (by simpa [Metric.mem_ball, dist_eq_norm] using hy)).deriv
  have hdiffG : DifferentiableAt 𝕂 (₂F₁ (a + 1) (b + 1) (c + 1)) x :=
    (hasDerivAt_ordinaryHypergeometric (a + 1) (b + 1) (c + 1) habc' hx).differentiableAt
  have h2 : deriv (deriv (₂F₁ a b c)) x = a * b / c * deriv (₂F₁ (a + 1) (b + 1) (c + 1)) x := by
    rw [hev.deriv_eq, deriv_const_mul _ hdiffG]
  rw [h2]
  have hdG := hasSum_deriv_ordinaryHypergeometric (a + 1) (b + 1) (c + 1) habc' hx
  have heq : (fun (n : ℕ) =>
        ((n : 𝕂) + 1) * ((n : 𝕂) + 2) * ordinaryHypergeometricCoefficient a b c (n + 2) • x ^ n)
      = fun (n : ℕ) => a * b / c
          * (((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) (n + 1)
              • x ^ n) := by
    funext n
    simp only [smul_eq_mul]
    have hcs := coeff_succ_eq a b c (n + 1)
    rw [show n + 1 + 1 = n + 2 from rfl] at hcs
    push_cast at hcs
    linear_combination ((n : 𝕂) + 1) * x ^ n * hcs
  rw [heq]
  exact hdG.mul_left (a * b / c)

/-- **`b`-ladder (contiguous) relation.** Inside the unit disk,
`x · d/dx ₂F₁(a,b;c;x) = b (₂F₁(a,b+1;c;x) − ₂F₁(a,b;c;x))`. Immediate from the `a`-ladder and
the `a ↔ b` symmetry `ordinaryHypergeometric_symm`. -/
lemma ordinaryHypergeometric_contiguous_b (a b c : 𝕂)
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    x * deriv (₂F₁ a b c) x = b * (₂F₁ a (b + 1) c x - ₂F₁ a b c x) := by
  have hsymm : (₂F₁ a b c) = (₂F₁ b a c : 𝕂 → 𝕂) :=
    funext fun (y : 𝕂) => ordinaryHypergeometric_symm a b c y
  have habcba : ∀ kn : ℕ, (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -c :=
    fun kn => ⟨(habc kn).2.1, (habc kn).1, (habc kn).2.2⟩
  have h := ordinaryHypergeometric_contiguous_a b a c habcba hx
  rw [hsymm, ordinaryHypergeometric_symm a (b + 1) c x]
  exact h
