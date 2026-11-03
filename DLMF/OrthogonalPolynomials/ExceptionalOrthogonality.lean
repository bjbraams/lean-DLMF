/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals.AngularRepresentations

/-!
# Orthogonality of the exceptional Laguerre and Hermite polynomials

The exceptional `X₁`-Laguerre polynomials and the exceptional Hermite polynomials of DLMF §18.36
are obtained from classical polynomials by a first-order operator that is independent of the
degree: `L̂_n = (x + k)² eˣ (L_n^{(k-1)} e^{-x} / (x + k))'` and, up to normalization,
`Ĥ_{n+3} = -2 η² e^{x²} (H_n e^{-x²} / η)'` with `η = 2x² + 1`. One integration by parts reduces
the exceptional orthogonality relations to the classical ones for `L_n^{(k-1)}` and `H_n`.

## Main results

* `exceptionalLaguerre_orthogonality`: DLMF 18.36.6.
* `exceptionalHermite_orthonormal`: DLMF 18.36.10.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open DLMF.Hypergeometric DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

namespace ExceptionalLaguerre

/-- `L_n^{(k-1)}` as a complex polynomial. -/
private def laguerrePoly (k : ℝ) (n : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (n + 1), C (poch (((k - 1 : ℝ) : ℂ) + 1) n / n.factorial *
    kummerMCoeff (-(n : ℂ)) (((k - 1 : ℝ) : ℂ) + 1) j) * X ^ j

/-- Evaluation of `laguerrePoly` is `L_n^{(k-1)}`. -/
private lemma eval_laguerrePoly (k : ℝ) (n : ℕ) (z : ℂ) :
    (laguerrePoly k n).eval z = laguerrePolyL ((k - 1 : ℝ) : ℂ) n z := by
  rw [laguerrePolyL_eq_sum_coeff, laguerrePoly, eval_finsetSum]
  simp

/-- `L_n^{(k-1)}` as a polynomial function. -/
private lemma laguerrePolyL_eq_eval (k : ℝ) (n : ℕ) :
    laguerrePolyL ((k - 1 : ℝ) : ℂ) n = fun z => (laguerrePoly k n).eval z :=
  funext fun z => (eval_laguerrePoly k n z).symm

/-- The derivative of `L_n^{(k-1)}` as a polynomial evaluation. -/
private lemma deriv_laguerrePolyL_eq (k : ℝ) (n : ℕ) (z : ℂ) :
    deriv (laguerrePolyL ((k - 1 : ℝ) : ℂ) n) z = (derivative (laguerrePoly k n)).eval z := by
  rw [laguerrePolyL_eq_eval]; exact Polynomial.deriv _

/-- The second derivative of `L_n^{(k-1)}` as a polynomial evaluation. -/
private lemma deriv_deriv_laguerrePolyL_eq (k : ℝ) (n : ℕ) (z : ℂ) :
    deriv (deriv (laguerrePolyL ((k - 1 : ℝ) : ℂ) n)) z =
      (derivative (derivative (laguerrePoly k n))).eval z := by
  have h : deriv (laguerrePolyL ((k - 1 : ℝ) : ℂ) n) =
      fun z => (derivative (laguerrePoly k n)).eval z :=
    funext (deriv_laguerrePolyL_eq k n)
  rw [h]; exact Polynomial.deriv _

/-- Laguerre's differential equation for `L_n^{(k-1)}` as a polynomial identity. -/
private lemma laguerrePoly_ode {k : ℝ} (hk : 0 < k) (n : ℕ) :
    X * derivative (derivative (laguerrePoly k n)) + (C (k : ℂ) - X) *
      derivative (laguerrePoly k n) + C (n : ℂ) * laguerrePoly k n = 0 := by
  apply Polynomial.funext; intro z
  have h := laguerrePolyL_differential_equation (α := ((k - 1 : ℝ) : ℂ))
    (by simp; linarith) n z
  rw [deriv_deriv_laguerrePolyL_eq, deriv_laguerrePolyL_eq, ← eval_laguerrePoly] at h
  simp only [eval_add, eval_mul, eval_X, eval_sub, eval_C, eval_zero]
  push_cast at h
  linear_combination h

/-- The exceptional polynomial in terms of `L_n^{(k-1)}`. -/
private def excPoly (k : ℝ) (n : ℕ) : ℂ[X] :=
  (X + C (k : ℂ)) * derivative (laguerrePoly k n) - (X + C ((k : ℂ) + 1)) * laguerrePoly k n

/-- `L̂_n = (x + k) f' - (x + k + 1) f` with `f = L_n^{(k-1)}`. -/
private lemma exceptionalLaguerre_eq_eval {k : ℝ} (hk : 0 < k) (n : ℕ) (z : ℂ) :
    exceptionalLaguerre k n z = (excPoly k n).eval z := by
  have hα : -1 < (((k - 1 : ℝ) : ℂ)).re := by simp; linarith
  have e : ((k - 1 : ℝ) : ℂ) + 1 = k := by push_cast; ring
  simp only [excPoly, eval_sub, eval_mul, eval_add, eval_X, eval_C,
    ← deriv_laguerrePolyL_eq, eval_laguerrePoly]
  rcases n with _ | j
  · have h0 : laguerrePolyL ((k - 1 : ℝ) : ℂ) 0 = fun _ => 1 :=
      funext fun x => laguerrePolyL_zero _ x
    rw [h0, deriv_const]
    simp [exceptionalLaguerre, laguerrePolyL_zero]
    ring
  · have raise := laguerrePolyL_raise_parameter hα j z
    have der := laguerrePolyL_derivative hα j z
    rw [e] at raise der
    simp only [exceptionalLaguerre, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    linear_combination (z + k + 1) * raise - (z + k) * der

/-- `k L̂_n + x L̂_n' = -(n + k + 1)(x + k) L_n^{(k-1)}`. -/
private lemma excPoly_key {k : ℝ} (hk : 0 < k) (n : ℕ) :
    C (k : ℂ) * excPoly k n + X * derivative (excPoly k n) +
      C ((n : ℂ) + k + 1) * (X + C (k : ℂ)) * laguerrePoly k n = 0 := by
  have h := laguerrePoly_ode hk n
  simp only [excPoly, derivative_sub, derivative_mul, derivative_X,
    derivative_C, map_add, map_one, derivative_one]
  linear_combination (X + C (k : ℂ)) * h

/-- A polynomial times the Laguerre weight times a bounded factor is integrable. -/
private lemma integrable_eval_mul_weight (p : ℂ[X]) {α : ℝ} (hα : -1 < α) {h : ℝ → ℂ} {c : ℝ}
    (hm : AEStronglyMeasurable h (volume.restrict (Set.Ioi 0)))
    (hb : ∀ x ∈ Set.Ioi (0 : ℝ), ‖h x‖ ≤ c) :
    Integrable (fun x : ℝ => p.eval (x : ℂ) * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ)) * h x)
      (volume.restrict (Set.Ioi 0)) := by
  have hp : Integrable (fun x : ℝ => p.eval (x : ℂ) * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ)))
      (volume.restrict (Set.Ioi 0)) := by
    have := integrable_finsetSum (Finset.range (p.natDegree + 1)) fun i _ =>
      (laguerrePolyL_weight_moment hα i).1.const_mul (p.coeff i)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  exact hp.mul_bdd hm ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => hb x hx)

/-- `x^k` times the exceptional polynomial. -/
private def leftFactor (k : ℝ) (m : ℕ) (x : ℝ) : ℂ := ((x ^ k : ℝ) : ℂ) * (excPoly k m).eval (x : ℂ)

/-- Derivative of `x^k L̂_m(x)` on the positive half-line. -/
private lemma hasDerivAt_leftFactor {k : ℝ} (hk : 0 < k) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (leftFactor k m) (-((m : ℂ) + k + 1) * ((x : ℂ) + k) *
      ((x ^ (k - 1) : ℝ) : ℂ) * (laguerrePoly k m).eval (x : ℂ)) x := by
  have h1 : HasDerivAt (fun y : ℝ => ((y ^ k : ℝ) : ℂ)) ((k * x ^ (k - 1) : ℝ) : ℂ) x :=
    (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).ofReal_comp
  have h2 : HasDerivAt (fun y : ℝ => (excPoly k m).eval (y : ℂ))
      ((derivative (excPoly k m)).eval (x : ℂ)) x :=
    ((excPoly k m).hasDerivAt (x : ℂ)).comp_ofReal
  refine (h1.mul h2).congr_deriv ?_
  have key := congrArg (Polynomial.eval (x : ℂ)) (excPoly_key hk m)
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_zero] at key
  have hxk : ((x ^ k : ℝ) : ℂ) = (x : ℂ) * ((x ^ (k - 1) : ℝ) : ℂ) := by
    rw [← ofReal_mul, Real.rpow_sub_one hx.ne', mul_div_cancel₀ _ hx.ne']
  rw [hxk, ofReal_mul]
  set w := ((x ^ (k - 1) : ℝ) : ℂ)
  linear_combination w * key

/-- `L_n^{(k-1)}(x) e^{-x} / (x + k)`. -/
private def rightFactor (k : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (laguerrePoly k n).eval (x : ℂ) * ((Real.exp (-x) / (x + k) : ℝ) : ℂ)

/-- Derivative of `L_n^{(k-1)}(x) e^{-x} / (x + k)`. -/
private lemma hasDerivAt_rightFactor {k : ℝ} (hk : 0 < k) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (rightFactor k n)
      ((excPoly k n).eval (x : ℂ) * ((Real.exp (-x) / (x + k) ^ 2 : ℝ) : ℂ)) x := by
  have hxk : x + k ≠ 0 := by positivity
  have h1 := ((laguerrePoly k n).hasDerivAt (x : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y) / (y + k))
      ((Real.exp (-x) * (-1) * (x + k) - Real.exp (-x) * 1) / (x + k) ^ 2) x :=
    ((hasDerivAt_neg x).exp).div ((hasDerivAt_id x).add_const k) hxk
  refine (h1.mul h2.ofReal_comp).congr_deriv ?_
  have hxk' : (x : ℂ) + k ≠ 0 := by exact_mod_cast hxk
  simp only [excPoly, eval_sub, eval_mul, eval_add, eval_X, eval_C]
  push_cast
  field_simp
  ring

/-- The boundary term vanishes at `0`. -/
private lemma tendsto_zero_leftFactor_mul_rightFactor {k : ℝ} (hk : 0 < k) (m n : ℕ) :
    Tendsto (leftFactor k m * rightFactor k n) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (leftFactor k m * rightFactor k n) 0 := by
    have hk0 : (0 : ℝ) + k ≠ 0 := by simp; exact hk.ne'
    refine ContinuousAt.mul ?_ ?_
    · exact (continuous_ofReal.continuousAt.comp
        (Real.continuousAt_rpow_const 0 k (Or.inr hk.le))).mul
        ((excPoly k m).continuous.continuousAt.comp continuous_ofReal.continuousAt)
    · exact ((laguerrePoly k n).continuous.continuousAt.comp continuous_ofReal.continuousAt).mul
        (continuous_ofReal.continuousAt.comp ((Real.continuous_exp.comp
          continuous_neg).continuousAt.div (continuous_id.add continuous_const).continuousAt hk0))
  have h0 : (leftFactor k m * rightFactor k n) 0 = 0 := by
    simp [leftFactor, Real.zero_rpow hk.ne']
  rw [← h0]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-- A polynomial times `x^k e^{-x}` tends to zero at infinity. -/
private lemma tendsto_eval_mul_rpow_exp (q : ℂ[X]) (k : ℝ) :
    Tendsto (fun x : ℝ => q.eval (x : ℂ) * ((x ^ k * Real.exp (-x) : ℝ) : ℂ)) atTop (𝓝 0) := by
  have h : ∀ i : ℕ, Tendsto (fun x : ℝ => q.coeff i * ((x ^ ((i : ℝ) + k) *
      Real.exp (-1 * x) : ℝ) : ℂ)) atTop (𝓝 0) := fun i => by
    simpa using ((continuous_ofReal.tendsto 0).comp
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((i : ℝ) + k) 1 one_pos)).const_mul (q.coeff i)
  have hs := tendsto_finsetSum (Finset.range (q.natDegree + 1)) fun i _ => h i
  simp only [Finset.sum_const_zero] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.rpow_add hx, Real.rpow_natCast]
  push_cast
  ring_nf

/-- The boundary term vanishes at infinity. -/
private lemma tendsto_atTop_leftFactor_mul_rightFactor (k : ℝ) (m n : ℕ) :
    Tendsto (leftFactor k m * rightFactor k n) atTop (𝓝 0) := by
  have h1 := tendsto_eval_mul_rpow_exp (excPoly k m * laguerrePoly k n) k
  have h2 : Tendsto (fun x : ℝ => (((x + k)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_ofReal.tendsto 0).comp
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ k tendsto_id))
  have := h1.mul h2
  rw [zero_mul] at this
  refine this.congr' (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply, leftFactor, rightFactor, eval_mul, div_eq_mul_inv]
  push_cast
  ring

end ExceptionalLaguerre
open ExceptionalLaguerre in
/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Set.Ioi 0,
exceptionalLaguerre k m x * exceptionalLaguerre k n x * exceptionalLaguerreWeight k x = if m =
n then (n + 1 + (k : ℂ)) * Gamma (n + (k : ℂ)) / n.factorial else 0`. -/
@[dlmf 18.36.E6]
theorem exceptionalLaguerre_orthogonality {k : ℝ} (hk : 0 < k) (m n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exceptionalLaguerre k m x * exceptionalLaguerre k n x *
        exceptionalLaguerreWeight k x =
      if m = n then (n + 1 + (k : ℂ)) * Gamma (n + (k : ℂ)) / n.factorial else 0 := by
  have hα : -1 < k - 1 := by linarith
  have hbd : ∀ j : ℕ, ∀ x ∈ Set.Ioi (0 : ℝ), ‖((((x + k) ^ j)⁻¹ : ℝ) : ℂ)‖ ≤ ((k ^ j)⁻¹) :=
    fun j x hx => by
      have hx : 0 < x := hx
      rw [norm_real, Real.norm_of_nonneg (by positivity)]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hk.le (by linarith) j)
  have hmeas : ∀ j : ℕ, AEStronglyMeasurable (fun x : ℝ => ((((x + k) ^ j)⁻¹ : ℝ) : ℂ))
      (volume.restrict (Set.Ioi 0)) := fun j =>
    (continuous_ofReal.measurable.comp ((measurable_id.add_const k).pow_const j).inv)
      |>.aestronglyMeasurable
  -- pointwise identities on the positive half-line
  have hcp : ∀ x : ℝ, 0 < x → (x : ℂ) ^ (((k - 1 : ℝ)) : ℂ) = ((x ^ (k - 1) : ℝ) : ℂ) :=
    fun x hx => (ofReal_cpow hx.le _).symm
  have hxk : ∀ x : ℝ, 0 < x → x ^ k = x * x ^ (k - 1) := fun x hx => by
    rw [Real.rpow_sub_one hx.ne', mul_div_cancel₀ _ hx.ne']
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := leftFactor k m)
    (u' := fun x => -((m : ℂ) + k + 1) * ((x : ℂ) + k) * ((x ^ (k - 1) : ℝ) : ℂ) *
      (laguerrePoly k m).eval (x : ℂ))
    (v := rightFactor k n)
    (v' := fun x => (excPoly k n).eval (x : ℂ) * ((Real.exp (-x) / (x + k) ^ 2 : ℝ) : ℂ))
    (fun x hx => hasDerivAt_leftFactor hk m hx) (fun x hx => hasDerivAt_rightFactor hk n hx)
    (by
      refine IntegrableOn.congr_fun (integrable_eval_mul_weight (X * excPoly k m * excPoly k n)
        hα (hmeas 2) (hbd 2)) (fun x (hx : 0 < x) => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, leftFactor, eval_mul, eval_X, hcp x hx, hxk x hx]
      push_cast
      ring)
    (by
      refine IntegrableOn.congr_fun (integrable_eval_mul_weight (C (-((m : ℂ) + k + 1)) *
        laguerrePoly k m * laguerrePoly k n) hα (hmeas 0) (hbd 0)) (fun x (hx : 0 < x) => ?_)
        measurableSet_Ioi
      have hx' : (x : ℂ) + k ≠ 0 := by exact_mod_cast (by positivity : x + k ≠ 0)
      simp only [Pi.mul_apply, rightFactor, eval_mul, eval_C, hcp x hx]
      push_cast
      field_simp)
    (tendsto_zero_leftFactor_mul_rightFactor hk m n)
    (tendsto_atTop_leftFactor_mul_rightFactor k m n)
  have hL : ∫ x : ℝ in Set.Ioi 0, exceptionalLaguerre k m x * exceptionalLaguerre k n x *
      exceptionalLaguerreWeight k x = ∫ x : ℝ in Set.Ioi 0, leftFactor k m x *
        ((excPoly k n).eval (x : ℂ) * ((Real.exp (-x) / (x + k) ^ 2 : ℝ) : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [exceptionalLaguerre_eq_eval hk, leftFactor, exceptionalLaguerreWeight]
    push_cast
    ring
  have hR : ∫ x : ℝ in Set.Ioi 0, -((m : ℂ) + k + 1) * ((x : ℂ) + k) *
      ((x ^ (k - 1) : ℝ) : ℂ) * (laguerrePoly k m).eval (x : ℂ) * rightFactor k n x =
      -((m : ℂ) + k + 1) * ∫ x : ℝ in Set.Ioi 0, laguerrePolyL ((k - 1 : ℝ) : ℂ) m x *
        laguerrePolyL ((k - 1 : ℝ) : ℂ) n x * (x : ℂ) ^ (((k - 1 : ℝ)) : ℂ) * exp (-(x : ℂ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
    have hx' : (x : ℂ) + k ≠ 0 := by exact_mod_cast (by positivity : x + k ≠ 0)
    simp only [rightFactor, eval_laguerrePoly, hcp x hx]
    push_cast
    field_simp
  rw [hL, hibp, hR]
  split_ifs with hmn
  · subst hmn
    have hN := laguerrePolyL_norm hα m
    rw [show (fun x : ℝ => laguerrePolyL ((k - 1 : ℝ) : ℂ) m x *
        laguerrePolyL ((k - 1 : ℝ) : ℂ) m x * (x : ℂ) ^ (((k - 1 : ℝ)) : ℂ) * exp (-(x : ℂ))) =
      fun x : ℝ => laguerrePolyL ((k - 1 : ℝ) : ℂ) m x ^ 2 * exp (-(x : ℂ)) *
        (x : ℂ) ^ (((k - 1 : ℝ)) : ℂ) by funext x; ring, hN]
    push_cast
    ring_nf
  · rw [laguerrePolyL_orthogonal hα hmn]
    simp

namespace ExceptionalHermite

/-- The polynomial `η = 2X² + 1`. -/
private abbrev eta : ℝ[X] := 2 * X ^ 2 + 1

/-- `η(x) > 0`. -/
private lemma eta_eval_pos (x : ℝ) : 0 < eta.eval x := by simp; positivity

/-- Numerator polynomial. -/
private abbrev num (n : ℕ) : ℝ[X] :=
  4 * X * (2 * X ^ 2 + 3) * hermitePolyHR n - 2 * eta * derivative (hermitePolyHR n)

/-- `H_{n+1}' = 2(n+1) H_n` for the real Hermite polynomials. -/
private lemma derivative_hermitePolyHR_succ (n : ℕ) :
    derivative (hermitePolyHR (n + 1)) = C (2 * (n + 1) : ℝ) * hermitePolyHR n := by
  rw [hermitePolyHR, derivative_map, hermitePolyH_derivative, Polynomial.map_mul, map_C]
  simp

/-- Hermite's differential equation `H_n'' = 2x H_n' - 2n H_n`. -/
private lemma hermitePolyHR_ode (n : ℕ) :
    derivative (derivative (hermitePolyHR n)) =
      2 * X * derivative (hermitePolyHR n) - C (2 * n : ℝ) * hermitePolyHR n := by
  have h1 := derivative_hermitePolyHR_succ n
  rw [hermitePolyHR_succ] at h1
  simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h1
  have : derivative (derivative (hermitePolyHR n)) =
      2 * hermitePolyHR n + 2 * X * derivative (hermitePolyHR n) -
        C (2 * (n + 1) : ℝ) * hermitePolyHR n := by
    rw [← h1]; ring
  rw [this, show (C (2 * (n + 1) : ℝ)) = C (2 * n : ℝ) + 2 by
    simp only [map_mul, map_add, map_natCast, map_one, map_ofNat]; ring]
  ring

/-- `num_n' = 4(n + 3) η H_n`. -/
private lemma derivative_num (n : ℕ) :
    derivative (num n) = C (4 * (n + 3) : ℝ) * eta * hermitePolyHR n := by
  simp only [num, eta, derivative_sub, derivative_mul, derivative_ofNat, derivative_X,
    derivative_add, derivative_X_pow, derivative_one, hermitePolyHR_ode]
  simp only [map_mul, map_add, map_natCast, map_ofNat]
  ring


/-- `H_n(x) e^{-x²} / η(x)`. -/
private def gaussQuotient (n : ℕ) (x : ℝ) : ℝ :=
  (hermitePolyHR n).eval x * Real.exp (-(x ^ 2)) / eta.eval x

/-- Derivative of `H_n(x) e^{-x²} / η(x)`. -/
private lemma hasDerivAt_gaussQuotient (n : ℕ) (x : ℝ) :
    HasDerivAt (gaussQuotient n)
      (-((num n).eval x * Real.exp (-(x ^ 2))) / (2 * eta.eval x ^ 2)) x := by
  have he : HasDerivAt (fun y => eta.eval y) ((derivative eta).eval x) x := eta.hasDerivAt x
  have h := (hasDerivAt_hermite_gauss n x).div he (eta_eval_pos x).ne'
  unfold gaussQuotient
  convert h using 1
  have hη := (eta_eval_pos x).ne'
  rw [hermitePolyHR_succ]
  simp only [num, eta, eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_ofNat, eval_one,
    derivative_add, derivative_mul, derivative_ofNat, derivative_X_pow, derivative_one,
    eval_C, eval_zero] at hη ⊢
  field_simp
  ring

/-- A polynomial times `e^{-x²} / η^k` is integrable. -/
private lemma integrable_eval_gauss_div (p : ℝ[X]) (k : ℕ) :
    Integrable fun x : ℝ => p.eval x * Real.exp (-(x ^ 2)) / eta.eval x ^ k := by
  have h := (TauCeti.integrable_eval_mul_exp_neg_sq p).mul_bdd
    (g := fun x : ℝ => (eta.eval x ^ k)⁻¹) (c := 1)
    ((eta.continuous.pow k).inv₀ fun x => (pow_pos (eta_eval_pos x) k).ne').aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [norm_inv, norm_pow, Real.norm_of_nonneg (eta_eval_pos x).le]
      refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
      simp; positivity)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp [div_eq_mul_inv]

/-- `Ĥ_{n+3}` in terms of `num n`. -/
private lemma exceptionalHermite_some_eq (n : ℕ) (x : ℝ) :
    exceptionalHermite (some n) x = (num n).eval x /
      (Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ (n + 1) * (n + 3) * n.factorial)) := by
  simp only [exceptionalHermite, aeval_hermitePolyH_eq_eval, hermitePolyHR_succ]
  congr 1
  simp only [num, eta, eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_ofNat, eval_one]
  ring

/-- The integration by parts reducing to Hermite orthogonality. -/
private lemma integral_num_mul_num (m n : ℕ) :
    ∫ x : ℝ, (num m).eval x * (num n).eval x * Real.exp (-(x ^ 2)) / (4 * eta.eval x ^ 2) =
      2 * (m + 3) * ∫ x : ℝ, (aeval x (hermitePolyH m) : ℝ) * aeval x (hermitePolyH n) *
        Real.exp (-(x ^ 2)) := by
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => (num m).eval x)
    (u' := fun x => (C (4 * (m + 3) : ℝ) * eta * hermitePolyHR m).eval x)
    (v := gaussQuotient n)
    (v' := fun x => -((num n).eval x * Real.exp (-(x ^ 2))) / (2 * eta.eval x ^ 2))
    (fun x _ => ((num m).hasDerivAt x).congr_deriv (by rw [derivative_num]))
    (fun x _ => hasDerivAt_gaussQuotient n x)
    (by
      refine ((integrable_eval_gauss_div (num m * num n) 2).const_mul (-1 / 2)).congr
        (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply, eval_mul]; ring)
    (by
      refine ((integrable_eval_gauss_div
        (C (4 * (m + 3) : ℝ) * hermitePolyHR m * hermitePolyHR n) 0)).congr
        (Eventually.of_forall fun x => ?_)
      have hη := (eta_eval_pos x).ne'
      simp only [Pi.mul_apply, eval_mul, gaussQuotient, pow_zero, div_one]
      field_simp)
    (by
      refine (integrable_eval_gauss_div (num m * hermitePolyHR n) 1).congr
        (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply, eval_mul, gaussQuotient, pow_one]; ring)
  have h1 : ∫ x : ℝ, (num m).eval x * (num n).eval x * Real.exp (-(x ^ 2)) /
      (4 * eta.eval x ^ 2) = -(1 / 2) * ∫ x : ℝ, (num m).eval x *
        (-((num n).eval x * Real.exp (-(x ^ 2))) / (2 * eta.eval x ^ 2)) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have h2 : ∫ x : ℝ, (C (4 * (m + 3) : ℝ) * eta * hermitePolyHR m).eval x * gaussQuotient n x =
      4 * (m + 3) * ∫ x : ℝ, (aeval x (hermitePolyH m) : ℝ) * aeval x (hermitePolyH n) *
        Real.exp (-(x ^ 2)) := by
    rw [← integral_const_mul]; congr 1; funext x
    have hη := (eta_eval_pos x).ne'
    simp only [eval_mul, eval_C, gaussQuotient, aeval_hermitePolyH_eq_eval]
    field_simp
  rw [h1, hibp, h2]; ring

/-- `num n` is orthogonal to the constant exceptional polynomial. -/
private lemma integral_num_div (n : ℕ) :
    ∫ x : ℝ, (num n).eval x * Real.exp (-(x ^ 2)) / (4 * eta.eval x ^ 2) = 0 := by
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun _ : ℝ => (1 : ℝ)) (u' := fun _ => 0) (v := gaussQuotient n)
    (v' := fun x => -((num n).eval x * Real.exp (-(x ^ 2))) / (2 * eta.eval x ^ 2))
    (fun x _ => hasDerivAt_const x 1) (fun x _ => hasDerivAt_gaussQuotient n x)
    (by
      refine ((integrable_eval_gauss_div (num n) 2).const_mul (-1 / 2)).congr
        (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by simp [Pi.mul_def])
    (by
      refine (integrable_eval_gauss_div (hermitePolyHR n) 1).congr
        (Eventually.of_forall fun x => ?_)
      simp [gaussQuotient])
  simp only [one_mul, zero_mul, integral_zero, neg_zero] at hibp
  rw [show (fun x : ℝ => (num n).eval x * Real.exp (-(x ^ 2)) / (4 * eta.eval x ^ 2)) =
    fun x => (-1 / 2) * (-((num n).eval x * Real.exp (-(x ^ 2))) / (2 * eta.eval x ^ 2)) by
      funext x; ring, integral_const_mul, hibp, mul_zero]

/-- `∫ e^{-x²} / η² = √π / 2`. -/
private lemma integral_gauss_div_eta_sq :
    ∫ x : ℝ, Real.exp (-(x ^ 2)) / eta.eval x ^ 2 = Real.sqrt π / 2 := by
  have hv : ∀ x : ℝ, HasDerivAt (fun y => y * Real.exp (-(y ^ 2)) / eta.eval y)
      (2 * (Real.exp (-(x ^ 2)) / eta.eval x ^ 2) - Real.exp (-(x ^ 2))) x := by
    intro x
    have hg : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2)))
        (Real.exp (-(x ^ 2)) * (-(2 * x))) x := by
      simpa using ((hasDerivAt_pow 2 x).neg).exp
    have h : HasDerivAt (fun y => y * Real.exp (-(y ^ 2)) / eta.eval y) _ x :=
      ((hasDerivAt_id' x).mul hg).div (eta.hasDerivAt x) (eta_eval_pos x).ne'
    refine h.congr_deriv ?_
    have hη := (eta_eval_pos x).ne'
    simp only [eta, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one, derivative_add,
      derivative_mul, derivative_ofNat, derivative_X_pow, derivative_one, eval_C, eval_zero,
      Pi.mul_apply] at hη ⊢
    field_simp
    ring
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun _ : ℝ => (1 : ℝ)) (u' := fun _ => 0)
    (v := fun y => y * Real.exp (-(y ^ 2)) / eta.eval y)
    (v' := fun x => 2 * (Real.exp (-(x ^ 2)) / eta.eval x ^ 2) - Real.exp (-(x ^ 2)))
    (fun x _ => hasDerivAt_const x 1) (fun x _ => hv x)
    (by
      have h1 := (integrable_eval_gauss_div 1 2).const_mul 2
      have h2 := integrable_eval_gauss_div 1 0
      refine (h1.sub h2).congr (Eventually.of_forall fun x => ?_)
      simp)
    (by simp [Pi.mul_def])
    (by
      refine (integrable_eval_gauss_div X 1).congr (Eventually.of_forall fun x => ?_)
      simp)
  simp only [one_mul, zero_mul, integral_zero, neg_zero] at hibp
  have h1 : Integrable fun x : ℝ => 2 * (Real.exp (-(x ^ 2)) / eta.eval x ^ 2) :=
    ((integrable_eval_gauss_div 1 2).const_mul 2).congr (Eventually.of_forall fun x => by simp)
  have h2 : Integrable fun x : ℝ => Real.exp (-(x ^ 2)) :=
    (integrable_eval_gauss_div 1 0).congr (Eventually.of_forall fun x => by simp)
  rw [integral_sub h1 h2, integral_const_mul, sub_eq_zero] at hibp
  have hg : ∫ x : ℝ, Real.exp (-(x ^ 2)) = Real.sqrt π := by
    rw [show (fun x : ℝ => Real.exp (-(x ^ 2))) = fun x => Real.exp (-1 * x ^ 2) by
      funext x; ring_nf, integral_gaussian, div_one]
  linarith

end ExceptionalHermite
open ExceptionalHermite in
/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ, exceptionalHermite m x *
exceptionalHermite n x * (Real.exp (-(x ^ 2)) / (4 * x ^ 2 + 2) ^ 2) = if m = n then 1 else
0`. -/
@[dlmf 18.36.E10]
theorem exceptionalHermite_orthonormal (m n : Option ℕ) :
    ∫ x : ℝ, exceptionalHermite m x * exceptionalHermite n x *
      (Real.exp (-(x ^ 2)) / (4 * x ^ 2 + 2) ^ 2) = if m = n then 1 else 0 := by
  have hw : ∀ x : ℝ, (4 * x ^ 2 + 2) ^ 2 = 4 * eta.eval x ^ 2 := fun x => by simp; ring
  have hc : ∀ k : ℕ, 0 < Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ (k + 1) * (k + 3) * k.factorial) :=
    fun k => mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.sqrt_pos.mpr (by positivity))
  have hc0 : ((2 : ℝ) ^ (3 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ)) ^ 2 * Real.sqrt π = 8 := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast
      (Real.pi ^ _), ← Real.rpow_mul Real.pi_pos.le, Real.sqrt_eq_rpow, mul_assoc,
      ← Real.rpow_add Real.pi_pos]
    norm_num
  rcases m with _ | m <;> rcases n with _ | n
  · simp only [exceptionalHermite, ite_true]
    simp_rw [hw]
    rw [show (fun x : ℝ => 2 ^ (3 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) * (2 ^ (3 / 2 : ℝ) *
        Real.pi ^ (-1 / 4 : ℝ)) * (Real.exp (-(x ^ 2)) / (4 * eta.eval x ^ 2))) =
      fun x => ((2 : ℝ) ^ (3 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ)) ^ 2 / 4 *
        (Real.exp (-(x ^ 2)) / eta.eval x ^ 2) by funext x; ring, integral_const_mul,
      integral_gauss_div_eta_sq]
    linear_combination hc0 / 8
  · simp only [exceptionalHermite_some_eq, reduceCtorEq, ite_false]
    simp_rw [hw]
    rw [← mul_zero ((2 : ℝ) ^ (3 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) /
      (Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ (n + 1) * (n + 3) * n.factorial))),
      ← integral_num_div n, ← integral_const_mul]
    congr 1; funext x; simp only [exceptionalHermite]; ring
  · simp only [exceptionalHermite_some_eq, reduceCtorEq, ite_false]
    simp_rw [hw]
    rw [← mul_zero ((2 : ℝ) ^ (3 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) /
      (Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ (m + 1) * (m + 3) * m.factorial))),
      ← integral_num_div m, ← integral_const_mul]
    congr 1; funext x; simp only [exceptionalHermite]; ring
  · simp only [exceptionalHermite_some_eq, Option.some.injEq]
    simp_rw [hw]
    set cm := Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ (m + 1) * (m + 3) * m.factorial)
    set cn := Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ (n + 1) * (n + 3) * n.factorial)
    rw [show (fun x : ℝ => (num m).eval x / cm * ((num n).eval x / cn) *
        (Real.exp (-(x ^ 2)) / (4 * eta.eval x ^ 2))) = fun x => (cm * cn)⁻¹ *
        ((num m).eval x * (num n).eval x * Real.exp (-(x ^ 2)) / (4 * eta.eval x ^ 2)) by
      funext x; field_simp, integral_const_mul, integral_num_mul_num,
      hermitePolyH_orthogonality]
    split_ifs with hmn
    · subst hmn
      have hcm : cm ^ 2 = Real.sqrt π * (2 ^ (m + 1) * (m + 3) * m.factorial) := by
        simp only [cm, mul_pow]
        rw [Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le,
          Real.sqrt_eq_rpow]
        norm_num
      rw [show cn = cm from rfl, ← sq, hcm]
      field_simp
      ring
    · simp

end DLMF.OrthogonalPolynomials
