/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.ClassicalInstances
public import DLMF.OrthogonalPolynomials.InequalityTools
public import DLMF.OrthogonalPolynomials.SoninePolyaApplications

/-!
# Pointwise bounds and zeros of classical polynomials

Sonine-Polya inequalities and Laguerre differential inequalities bound values and zeros of
classical orthogonal polynomials.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.BoundsZeros`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- The real Jacobi polynomial satisfies the Jacobi differential equation. -/
theorem jacobiPolyPR_ode {α : ℝ} (hα : -1 < α) (β : ℝ) (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * (derivative (derivative (jacobiPolyPR α β n))).eval x +
      (β - α - (α + β + 2) * x) * (derivative (jacobiPolyPR α β n)).eval x +
      n * (n + α + β + 1) * (jacobiPolyPR α β n).eval x = 0 := by
  set p := jacobiPolyPR α β n
  set q := p.map (algebraMap ℝ ℂ)
  have hfun : jacobiPolyP (α : ℂ) β n = fun z => q.eval z :=
    funext fun z => (eval_map_jacobiPolyPR hα β n z).symm
  have hd : deriv (fun z => q.eval z) = fun z => (derivative q).eval z :=
    funext fun z => Polynomial.deriv q
  have h := jacobi_differential_equation (α := (α : ℂ)) (β := (β : ℂ)) (by simpa using hα) n x
  rw [hfun, hd, Polynomial.deriv] at h
  simp only [q, derivative_map, eval_map_ofReal] at h
  exact_mod_cast h

/-- Positivity and monotonicity of real Pochhammer symbols. -/
theorem poch_ofReal_le {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (n : ℕ) :
    ∃ u v : ℝ, 0 < u ∧ u ≤ v ∧ poch (r : ℂ) n = u ∧ poch (s : ℂ) n = v := by
  induction n with
  | zero => exact ⟨1, 1, one_pos, le_rfl, by simp [poch_zero], by simp [poch_zero]⟩
  | succ k ih =>
    obtain ⟨u, v, hu, huv, h1, h2⟩ := ih
    refine ⟨u * (r + k), v * (s + k), by positivity, ?_, ?_, ?_⟩
    · exact mul_le_mul huv (by linarith) (by positivity) (by linarith)
    · rw [poch_succ, h1]; push_cast; ring
    · rw [poch_succ, h2]; push_cast; ring

/-- Estimate under the stated parameter and domain assumptions: `‖jacobiPolyP α β n x‖ ≤ (poch (α
+ 1) n).re / n.factorial`. -/
@[dlmf 18.14.E1]
theorem jacobi_bound_at_one {α β x : ℝ} (hαβ : β ≤ α) (hβ : -1 < β) (hα : -1 / 2 ≤ α) (hx : |x| ≤ 1) (n : ℕ) :
    ‖jacobiPolyP α β n x‖ ≤ (poch (α + 1) n).re / n.factorial := by
  have hα1 : -1 < α := by linarith
  obtain ⟨u, v, hu, huv, h1, h2⟩ := poch_ofReal_le (r := β + 1) (s := α + 1) (by linarith)
    (by linarith) n
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  set p := jacobiPolyPR α β n
  have hnorm : ∀ t : ℝ, ‖jacobiPolyP α β n t‖ = |p.eval t| := fun t => by
    rw [← eval_jacobiPolyPR hα1, Complex.norm_real, Real.norm_eq_abs]
  have hone : |p.eval 1| = (poch (α + 1) n).re / n.factorial := by
    rw [← hnorm, show ((1 : ℝ) : ℂ) = 1 by simp, jacobiPolyP_one ]
    have : ((α : ℂ) + 1) = ((α + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, h2, norm_div, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg
      (hu.le.trans huv)]
    simp
  have hneg : |p.eval (-1)| ≤ |p.eval 1| := by
    rw [← hnorm, ← hnorm, show ((-1 : ℝ) : ℂ) = -1 by simp,
      jacobi_reflection (by simpa using hα1) (by simpa using hβ),
      show ((1 : ℝ) : ℂ) = 1 by simp, jacobiPolyP_one,
      jacobiPolyP_one ]
    have e1 : ((β : ℂ) + 1) = ((β + 1 : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((α : ℂ) + 1) = ((α + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, h1, h2, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div,
      norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hu.le,
      Real.norm_of_nonneg (hu.le.trans huv)]
    exact div_le_div_of_nonneg_right huv (by positivity)
  rw [hnorm, ← hone]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [p, jacobiPolyPR]
  have hlam : 0 < (n : ℝ) * (n + α + β + 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 < (n : ℝ) + α + β + 1 := by linarith
    positivity
  have hy : ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt (fun t => p.eval t) ((derivative p).eval t) t :=
    fun t _ => p.hasDerivAt t
  have hy' : ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt (fun t => (derivative p).eval t)
      ((derivative (derivative p)).eval t) t := fun t _ => (derivative p).hasDerivAt t
  have hode : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, (1 - t ^ 2) * (derivative (derivative p)).eval t +
      (β - α - (α + β + 2) * t) * (derivative p).eval t +
        (n * (n + α + β + 1)) * p.eval t = 0 := fun t _ => by
    have := jacobiPolyPR_ode hα1 β n t
    linear_combination this
  have hxI : x ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hx
  rcases lt_or_ge 0 (α + β + 1) with hs | hs
  · exact (jacobi_ode_abs_le_max hlam hs hy hy' hode x hxI).trans (max_le hneg le_rfl)
  · refine jacobi_ode_abs_le_right hlam (fun t ht => ?_) hy hy' hode x hxI
    nlinarith [ht.2]

/-- Estimate under the stated parameter and domain assumptions: `‖jacobiPolyP α β n x‖ ≤ (poch (β
+ 1) n).re / n.factorial`. -/
@[dlmf 18.14.E2]
theorem jacobi_bound_at_neg_one {α β x : ℝ} (hαβ : α ≤ β) (hα : -1 < α) (hβ : -1 / 2 ≤ β) (hx : |x| ≤ 1) (n : ℕ) :
    ‖jacobiPolyP α β n x‖ ≤ (poch (β + 1) n).re / n.factorial := by
  rw [show (x : ℂ) = -((-x : ℝ) : ℂ) by push_cast; ring,
    jacobi_reflection (by simpa using hα) (by simpa using hα.trans_le hαβ), norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul]
  exact jacobi_bound_at_one hαβ hα hβ (by rwa [abs_neg]) n

/-- Estimate under the stated parameter and domain assumptions: `((1 - x) / 2) ^ (α / 2 + 1 / 4) *
((1 + x) / 2) ^ (β / 2 + 1 / 4) * ‖jacobiPolyP α β n x‖ ≤ Real.Gamma (max α β + n + 1) /
(Real.sqrt Real.pi * n.factorial * (n + (α + β + 1) / 2) ^ (max α β + 1 / 2))`. -/
@[dlmf 18.14.E3]
theorem jacobi_bernstein_bound {α β x : ℝ} (hα : α ∈ Set.Icc (-1 / 2) (1 / 2))
    (hβ : β ∈ Set.Icc (-1 / 2) (1 / 2)) (hx : |x| ≤ 1) (n : ℕ) :
    ((1 - x) / 2) ^ (α / 2 + 1 / 4) * ((1 + x) / 2) ^ (β / 2 + 1 / 4) * ‖jacobiPolyP α β n x‖ ≤
      Real.Gamma (max α β + n + 1) / (Real.sqrt Real.pi * n.factorial *
        (n + (α + β + 1) / 2) ^ (max α β + 1 / 2)) := by
  sorry

/-- Pochhammer symbols of a positive real are positive reals. -/
theorem exists_poch_ofReal_eq {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ∃ s : ℝ, 0 < s ∧ poch (r : ℂ) k = s := by
  induction k with
  | zero => exact ⟨1, one_pos, by simp [poch_zero]⟩
  | succ k ih =>
    obtain ⟨s, hs, hk⟩ := ih
    refine ⟨s * (r + k), by positivity, ?_⟩
    rw [poch_succ, hk]; push_cast; ring

/-- Estimate under the stated parameter and domain assumptions: `‖ultrasphPoly lam n x‖ ≤ (poch (2
* lam) n).re / n.factorial`. -/
@[dlmf 18.14.E4]
theorem ultrasphPoly_bound_at_one {lam x : ℝ} (hlam : 0 < lam) (hx : |x| ≤ 1) (n : ℕ) :
    ‖ultrasphPoly lam n x‖ ≤ (poch (2 * lam) n).re / n.factorial := by
  have hl : -1 / 2 < (lam : ℂ).re := by simp; linarith
  set θ := Real.arccos x
  have hcx : (x : ℂ) = cos (θ : ℂ) := by
    rw [← Complex.ofReal_cos, Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2]
  -- the coefficients of the trigonometric sum are positive reals
  have hc : ∀ k ≤ n, ∃ c : ℝ, 0 < c ∧ poch (lam : ℂ) k * poch (lam : ℂ) (n - k) /
      ((k.factorial : ℂ) * (n - k).factorial) = c := by
    intro k _
    obtain ⟨s, hs, h1⟩ := exists_poch_ofReal_eq hlam k
    obtain ⟨t, ht, h2⟩ := exists_poch_ofReal_eq hlam (n - k)
    refine ⟨s * t / (k.factorial * (n - k).factorial), by positivity, ?_⟩
    rw [h1, h2]; push_cast; ring
  choose! c hcpos hceq using hc
  have hone := ultrasphPoly_cos_sum hl n 0
  simp only [Complex.cos_zero, mul_zero] at hone
  have hval : ultrasphPoly (lam : ℂ) n 1 = poch (2 * (lam : ℂ)) n / n.factorial := by
    simp [ultrasphPoly]
  rw [hcx, ultrasphPoly_cos_sum hl n θ]
  calc ‖∑ k ∈ Finset.range (n + 1), poch (lam : ℂ) k * poch (lam : ℂ) (n - k) /
          ((k.factorial : ℂ) * (n - k).factorial) * cos (((n : ℂ) - 2 * k) * θ)‖
      ≤ ∑ k ∈ Finset.range (n + 1), c k := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [hceq k hkn, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hcpos k hkn).le]
        have : ‖cos (((n : ℂ) - 2 * k) * θ)‖ ≤ 1 := by
          rw [show ((n : ℂ) - 2 * k) * θ = (((n : ℝ) - 2 * k) * θ : ℝ) by push_cast; ring,
            ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
          exact Real.abs_cos_le_one _
        nlinarith [hcpos k hkn]
    _ = (poch (2 * (lam : ℂ)) n).re / n.factorial := by
        have h := congrArg Complex.re (hone.symm.trans hval)
        rw [Finset.sum_congr rfl fun k hk => by
          rw [hceq k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), mul_one]] at h
        rw [← Complex.ofReal_sum, Complex.ofReal_re] at h
        rw [h]
        simp

/-! ### Sonine–Pólya bounds for Gegenbauer polynomials with `-1/2 < λ < 0` -/

/-- Gegenbauer polynomials with `-1/2 < λ` as a real multiple of a real Jacobi polynomial. -/
theorem ultrasphPoly_eq_mul_jacobiPolyPR {lam : ℝ} (hlam : -1 / 2 < lam) (m : ℕ) :
    ∃ c : ℂ, ∀ z : ℂ, ultrasphPoly lam m z =
      c * (((jacobiPolyPR (lam - 1 / 2) (lam - 1 / 2) m).map (algebraMap ℝ ℂ)).eval z) := by
  obtain ⟨u, -, hu, -, h1, -⟩ := poch_ofReal_le (r := lam + 1 / 2) (s := lam + 1 / 2)
    (by linarith) le_rfl m
  have hp : poch ((lam : ℂ) + 1 / 2) m ≠ 0 := by
    have : ((lam : ℂ) + 1 / 2) = ((lam + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, h1]; exact_mod_cast hu.ne'
  refine ⟨poch (2 * (lam : ℂ)) m / poch ((lam : ℂ) + 1 / 2) m, fun z => ?_⟩
  rw [ultrasphPoly_eq_jacobiPolyP m z hp, eval_map_jacobiPolyPR (by linarith)]
  push_cast
  ring_nf

/-- An even polynomial has zero derivative at `0`. -/
theorem derivative_eval_zero_of_even {p : ℝ[X]} (h : ∀ t, p.eval (-t) = p.eval t) :
    (derivative p).eval 0 = 0 := by
  have h1 : HasDerivAt (fun t => p.eval (-t)) ((derivative p).eval (-0) * (-1)) 0 :=
    (p.hasDerivAt (-0)).comp 0 (hasDerivAt_neg 0)
  have h2 : (fun t => p.eval (-t)) = fun t => p.eval t := funext h
  rw [h2, neg_zero] at h1
  have := h1.unique (p.hasDerivAt 0)
  linarith

/-- Estimate under the stated parameter and domain assumptions: `‖ultrasphPoly lam (2 * n) x‖ ≤
‖poch lam n / (n.factorial : ℂ)‖`. -/
@[dlmf 18.14.E5]
theorem ultrasphPoly_even_bound {lam x : ℝ} (hlam : -1 / 2 < lam) (hlam0 : lam < 0) (hx : |x| ≤ 1)
    (n : ℕ) :
    ‖ultrasphPoly lam (2 * n) x‖ ≤ ‖poch lam n / (n.factorial : ℂ)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [poch_zero]
  set a := lam - 1 / 2 with ha
  have ha1 : -1 < a := by linarith
  obtain ⟨c, hc⟩ := ultrasphPoly_eq_mul_jacobiPolyPR hlam (2 * n)
  set p := jacobiPolyPR a a (2 * n)
  have hz : ‖poch (lam : ℂ) n / (n.factorial : ℂ)‖ = ‖ultrasphPoly lam (2 * n) 0‖ := by
    rw [ultrasphPoly_even_at_zero (by simpa using hlam), mul_div_assoc, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]
  rw [hz, hc, hc, eval_map_ofReal, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, eval_map_ofReal,
    norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have heven : ∀ t, p.eval (-t) = p.eval t := fun t => by
    have h := jacobi_reflection (α := (a : ℂ)) (β := (a : ℂ)) (by simpa using ha1)
      (by simpa using ha1) (2 * n) (t : ℂ)
    rw [← eval_jacobiPolyPR ha1, show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring,
      ← eval_jacobiPolyPR ha1, pow_mul, neg_one_sq, one_pow, one_mul] at h
    exact_mod_cast h
  have hd0 := derivative_eval_zero_of_even heven
  have hlamJ : 0 < ((2 * n : ℕ) : ℝ) * ((2 * n : ℕ) + a + a + 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    have : 0 < 2 * (n : ℝ) + a + a + 1 := by linarith
    positivity
  have key := jacobi_ode_sq_le_zero (a := a) (y := fun t => p.eval t)
    (y' := fun t => (derivative p).eval t)
    (y'' := fun t => (derivative (derivative p)).eval t) hlamJ (by linarith)
    (fun t _ => p.hasDerivAt t) (fun t _ => (derivative p).hasDerivAt t)
    (fun t _ => by linear_combination jacobiPolyPR_ode ha1 a (2 * n) t) x (abs_le.mp hx)
  simp only [hd0] at key
  have : p.eval x ^ 2 ≤ p.eval 0 ^ 2 := by
    have h0 : (0 : ℝ) ^ 2 / (((2 * n : ℕ) : ℝ) * ((2 * n : ℕ) + a + a + 1)) = 0 := by simp
    linarith [key, h0]
  exact sq_le_sq.mp this

/-- Estimate under the stated parameter and domain assumptions: `‖ultrasphPoly lam (2 * n + 1) x‖
< -2 * (poch lam (n + 1)).re / (Real.sqrt ((2 * n + 1) * (2 * lam + 2 * n + 1)) *
n.factorial)`. -/
@[dlmf 18.14.E6]
theorem ultrasphPoly_odd_bound {lam x : ℝ} (hlam : -1 / 2 < lam) (hlam0 : lam < 0) (hx : |x| ≤ 1)
    (n : ℕ) :
    ‖ultrasphPoly lam (2 * n + 1) x‖ < -2 * (poch lam (n + 1)).re /
      (Real.sqrt ((2 * n + 1) * (2 * lam + 2 * n + 1)) * n.factorial) := by
  set a := lam - 1 / 2 with ha
  have ha1 : -1 < a := by linarith
  obtain ⟨c, hc⟩ := ultrasphPoly_eq_mul_jacobiPolyPR hlam (2 * n + 1)
  set p := jacobiPolyPR a a (2 * n + 1)
  have hodd : ∀ t, p.eval (-t) = -p.eval t := fun t => by
    have h := jacobi_reflection (α := (a : ℂ)) (β := (a : ℂ)) (by simpa using ha1)
      (by simpa using ha1) (2 * n + 1) (t : ℂ)
    rw [← eval_jacobiPolyPR ha1, show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring,
      ← eval_jacobiPolyPR ha1, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul] at h
    exact_mod_cast (by linear_combination h : (((p.eval (-t)) : ℝ) : ℂ) = -((p.eval t : ℝ) : ℂ))
  have hp0 : p.eval 0 = 0 := by have := hodd 0; rw [neg_zero] at this; linarith
  -- the derivative at `0`
  obtain ⟨u, -, hu, -, hu1, -⟩ := poch_ofReal_le (r := lam + 1) (s := lam + 1) (by linarith)
    le_rfl n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  set q := p.map (algebraMap ℝ ℂ)
  have hfun : ultrasphPoly (lam : ℂ) (2 * n + 1) = fun z => c * q.eval z := funext hc
  have hder : deriv (ultrasphPoly (lam : ℂ) (2 * n + 1)) 0 =
      c * (((derivative p).eval 0 : ℝ) : ℂ) := by
    rw [hfun, ((q.hasDerivAt 0).const_mul c).deriv, derivative_map,
      show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, eval_map_ofReal]
  have hder' := ultrasphPoly_derivative (lam := (lam : ℂ)) (by simpa using hlam) (2 * n) 0
  rw [ultrasphPoly_even_at_zero (by simp; linarith), hder] at hder'
  have hlam1 : ((lam : ℂ) + 1) = ((lam + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hlam1, hu1] at hder'
  set D := (derivative p).eval 0
  have hK : ‖c‖ * |D| = 2 * (-lam) * u / n.factorial := by
    have := congrArg norm hder'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
    rw [this, mul_div_assoc, mul_div_assoc, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul, norm_div, Complex.norm_real, Complex.norm_natCast,
      Complex.norm_real, Real.norm_of_nonneg hu.le, Real.norm_eq_abs, abs_of_neg hlam0]
    norm_num
  have hKpos : 0 < 2 * (-lam) * u / n.factorial := by
    have : 0 < -lam := by linarith
    positivity
  have hD : D ≠ 0 := fun h => by rw [h, abs_zero, mul_zero] at hK; linarith
  have hc0 : 0 < ‖c‖ := by
    rcases (norm_nonneg c).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hK; linarith
  -- the Sonine bound
  set Lm := ((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) + a + a + 1) with hLm
  have hLmpos : 0 < Lm := by
    rw [hLm]; push_cast
    have : 0 < 2 * (n : ℝ) + 1 + a + a + 1 := by linarith
    positivity
  have hLmeq : (2 * n + 1) * (2 * lam + 2 * n + 1) = Lm := by rw [hLm, ha]; push_cast; ring
  have hpoch : (poch (lam : ℂ) (n + 1)).re = lam * u := by
    rw [poch_succ_left, hlam1, hu1]; simp
  rw [hpoch, hLmeq]
  have hRHS : -2 * (lam * u) / (Real.sqrt Lm * n.factorial) = ‖c‖ * |D| / Real.sqrt Lm := by
    rw [hK]; field_simp
  rw [hRHS, hc, eval_map_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsqrt : 0 < Real.sqrt Lm := Real.sqrt_pos.mpr hLmpos
  rw [mul_div_assoc]
  refine mul_lt_mul_of_pos_left ?_ hc0
  have habs : |p.eval x| = |p.eval (|x|)| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, hodd, abs_neg]
  rw [habs]
  rcases (abs_nonneg x).lt_or_eq with hx0 | hx0
  · have hnz : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ v ∈ Set.Ioo s t, (derivative p).eval v ≠ 0 := by
      intro s t _ hst _
      by_contra! hall
      have : derivative p = 0 := Polynomial.eq_zero_of_infinite_isRoot _
        ((Set.Ioo_infinite hst).mono fun v hv => hall v hv)
      exact hD (by simp [D, this])
    have key := jacobi_ode_sq_lt_zero (a := a) (y := fun t => p.eval t)
      (y' := fun t => (derivative p).eval t) (y'' := fun t => (derivative (derivative p)).eval t)
      hLmpos (by linarith) (fun t _ => p.hasDerivAt t) (fun t _ => (derivative p).hasDerivAt t)
      (fun t _ => by linear_combination jacobiPolyPR_ode ha1 a (2 * n + 1) t) hnz (|x|)
      ⟨hx0, hx⟩
    simp only [hp0] at key
    have h2 : p.eval (|x|) ^ 2 < (|D| / Real.sqrt Lm) ^ 2 := by
      rw [div_pow, sq_abs, Real.sq_sqrt hLmpos.le]; linarith
    exact abs_lt_of_sq_lt_sq' h2 (by positivity) |>.2 |> fun h => by
      rcases le_total 0 (p.eval (|x|)) with h' | h'
      · rw [abs_of_nonneg h']; exact h
      · rw [abs_of_nonpos h']; linarith [(abs_lt_of_sq_lt_sq' h2 (by positivity)).1]
  · rw [← hx0, hp0, abs_zero]
    exact div_pos (abs_pos.mpr hD) hsqrt

/-- The even-degree Gamma estimate behind Lorch's inequality:
`(2m+λ)^{1-λ} Γ(m+λ)/(Γ(λ) m!) < 2^{1-λ}/Γ(λ)` for `0 < λ < 1`. -/
private lemma bernstein_even_bound {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) (m : ℕ) :
    (2 * m + lam : ℝ) ^ (1 - lam) *
        (Real.Gamma (m + lam) / Real.Gamma lam / Real.Gamma (m + 1)) <
      (2 : ℝ) ^ (1 - lam) / Real.Gamma lam := by
  have hGl : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam
  have hG := opIneq_Gamma_even hlam hlam1 m
  have hN2 : (2 * m + lam : ℝ) = 2 * (m + lam / 2) := by ring
  have hmpos : 0 < (m : ℝ) + lam / 2 := by positivity
  rw [hN2, Real.mul_rpow (by norm_num) hmpos.le]
  have hpow : ((m : ℝ) + lam / 2) ^ (1 - lam) * ((m : ℝ) + lam / 2) ^ (lam - 1) = 1 := by
    rw [← Real.rpow_add hmpos]; norm_num
  have h2 : (0 : ℝ) < 2 ^ (1 - lam) := by positivity
  have h3 : (0 : ℝ) < ((m : ℝ) + lam / 2) ^ (1 - lam) := by positivity
  rw [div_div, mul_comm (Real.Gamma lam), ← div_div]
  rw [← mul_div_assoc, div_lt_div_iff_of_pos_right hGl]
  calc 2 ^ (1 - lam) * ((m : ℝ) + lam / 2) ^ (1 - lam) *
        (Real.Gamma (m + lam) / Real.Gamma (m + 1))
      < 2 ^ (1 - lam) * ((m : ℝ) + lam / 2) ^ (1 - lam) * ((m : ℝ) + lam / 2) ^ (lam - 1) := by
        gcongr
    _ = 2 ^ (1 - lam) := by rw [mul_assoc, hpow, mul_one]

/-- The odd-degree Gamma estimate behind Lorch's inequality, with `N = 2m+1+λ` and
`r = Γ(m+1+λ)/m!`: `N^{2-2λ} (2r/Γ(λ))²/(N² + λ(1-λ)) < (2^{1-λ}/Γ(λ))²` for `0 < λ < 1`. -/
private lemma bernstein_odd_bound {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) (m : ℕ) :
    (2 * m + 1 + lam : ℝ) ^ (2 - 2 * lam) *
      ((2 * (Real.Gamma (m + 1 + lam) / Real.Gamma (m + 1)) / Real.Gamma lam) ^ 2 /
        ((2 * m + 1 + lam : ℝ) ^ 2 + lam * (1 - lam))) <
      ((2 : ℝ) ^ (1 - lam) / Real.Gamma lam) ^ 2 := by
  set N : ℝ := 2 * m + 1 + lam with hNe
  have hNpos : 0 < N := by positivity
  set c := lam * (1 - lam) with hc
  have hc0 : 0 < c := by have : 0 < 1 - lam := by linarith
                         positivity
  set r := Real.Gamma (m + 1 + lam) / Real.Gamma (m + 1) with hr
  have hG := opIneq_Gamma_odd hlam hlam1 m
  have hNc : 0 < N ^ 2 + c := by positivity
  have hi2 : (N / 2) ^ (2 * lam) = N ^ (2 * lam) / 2 ^ (2 * lam) :=
    Real.div_rpow hNpos.le (by norm_num) _
  have hi3 : N ^ (2 - 2 * lam) * N ^ (2 * lam) = N ^ 2 := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hi4 : ((2 : ℝ) ^ (1 - lam)) ^ 2 * 2 ^ (2 * lam) = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    rw [show (1 - lam) * ((2 : ℕ) : ℝ) + 2 * lam = (2 : ℝ) by push_cast; ring]
    norm_num
  have h2l : (0 : ℝ) < 2 ^ (2 * lam) := by positivity
  have hNl : (0 : ℝ) < N ^ (2 * lam) := by positivity
  rw [hi2] at hG
  -- multiply out
  have key : N ^ (2 - 2 * lam) * (2 * r) ^ 2 * N ^ 2 <
      ((2 : ℝ) ^ (1 - lam)) ^ 2 * (N ^ 2 + c) * N ^ 2 := by
    have e : ((2 : ℝ) ^ (1 - lam)) ^ 2 = 4 / 2 ^ (2 * lam) := by
      rw [← hi4]; field_simp
    rw [e]
    have hpos : 0 < N ^ (2 - 2 * lam) := by positivity
    have := mul_lt_mul_of_pos_left hG (show 0 < 4 * N ^ (2 - 2 * lam) by positivity)
    calc N ^ (2 - 2 * lam) * (2 * r) ^ 2 * N ^ 2
        = 4 * N ^ (2 - 2 * lam) * (r ^ 2 * N ^ 2) := by ring
      _ < 4 * N ^ (2 - 2 * lam) * (N ^ (2 * lam) / 2 ^ (2 * lam) * (N ^ 2 + c)) := this
      _ = 4 / 2 ^ (2 * lam) * (N ^ 2 + c) * (N ^ (2 - 2 * lam) * N ^ (2 * lam)) := by ring
      _ = _ := by rw [hi3]
  have hN2 : 0 < N ^ 2 := by positivity
  have key2 : N ^ (2 - 2 * lam) * (2 * r) ^ 2 < ((2 : ℝ) ^ (1 - lam)) ^ 2 * (N ^ 2 + c) :=
    lt_of_mul_lt_mul_right key hN2.le
  calc N ^ (2 - 2 * lam) * ((2 * r / Real.Gamma lam) ^ 2 / (N ^ 2 + c))
      = N ^ (2 - 2 * lam) * (2 * r) ^ 2 / (N ^ 2 + c) / Real.Gamma lam ^ 2 := by ring
    _ < ((2 : ℝ) ^ (1 - lam)) ^ 2 * (N ^ 2 + c) / (N ^ 2 + c) / Real.Gamma lam ^ 2 := by
      gcongr
    _ = ((2 : ℝ) ^ (1 - lam) / Real.Gamma lam) ^ 2 := by
      field_simp

/-- Lorch's sharpened Bernstein inequality for Gegenbauer polynomials, `0 < λ < 1`.
Proof: the Sonine-type function of `opIneq_gegenbauer_sonine` bounds
`(1 - x²)^λ C_n^{(λ)}(x)²` by its value at `x = 0`, and the values `C_n^{(λ)}(0)`,
`C_n^{(λ)}′(0)` are controlled by the sharp Gamma-ratio bounds `opIneq_Gamma_even`,
`opIneq_Gamma_odd`. -/
@[dlmf 18.14.E7]
theorem ultrasphPoly_bernstein_bound {lam x : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) (hx : |x| ≤ 1)
    (n : ℕ) :
    (n + lam) ^ (1 - lam) * (1 - x ^ 2) ^ (lam / 2) * ‖ultrasphPoly lam n x‖ <
      (2 : ℝ) ^ (1 - lam) / Real.Gamma lam := by
  have hlamh : -1 / 2 < lam := by linarith
  have hGl : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam
  have hR : 0 < (2 : ℝ) ^ (1 - lam) / Real.Gamma lam := by positivity
  set q := ultrasphPolyR lam n with hqdef
  have hq (t : ℝ) : ultrasphPoly lam n t = ((q.eval t : ℝ) : ℂ) :=
    (eval_ultrasphPolyR hlamh n t).symm
  rw [hq, Complex.norm_real, Real.norm_eq_abs]
  -- boundary points
  rcases (abs_le.mp hx).1.lt_or_eq with hxl | hxl
  swap
  · rw [← hxl]; norm_num [Real.zero_rpow (by positivity : lam / 2 ≠ 0)]; exact hR
  rcases (abs_le.mp hx).2.lt_or_eq with hxr | hxr
  swap
  · rw [hxr]; norm_num [Real.zero_rpow (by positivity : lam / 2 ≠ 0)]; exact hR
  have hxa : |x| < 1 := abs_lt.mpr ⟨hxl, hxr⟩
  -- the differential equation for `q`
  have hode : ∀ t : ℝ, (1 - t ^ 2) * (derivative (derivative q)).eval t -
      (2 * lam + 1) * t * (derivative q).eval t + n * (n + 2 * lam) * q.eval t = 0 := by
    intro t
    have h := jacobiPolyPR_ode (α := lam - 1 / 2) (by linarith) (lam - 1 / 2) n t
    simp only [hqdef, ultrasphPolyR, derivative_C_mul, eval_mul, eval_C]
    linear_combination (ultrasphCoeffR lam n) * h
  have hS := opIneq_gegenbauer_sonine hlam hlam1 (n := n) (y := fun t => q.eval t)
    (y' := fun t => (derivative q).eval t) (y'' := fun t => (derivative (derivative q)).eval t)
    (fun t => q.hasDerivAt t) (fun t => (derivative q).hasDerivAt t) hode hxa

  set N : ℝ := n + lam with hN
  have hNpos : 0 < N := by positivity
  set c := lam * (1 - lam) with hc
  have hc0 : 0 < c := by have : 0 < 1 - lam := by linarith
                         positivity
  set S := q.eval 0 ^ 2 + (derivative q).eval 0 ^ 2 / (N ^ 2 + c) with hSdef
  have h1x : 0 < 1 - x ^ 2 := by nlinarith [abs_lt.mp hxa]
  set A := (1 - x ^ 2) ^ (lam / 2) * |q.eval x| with hA
  have hA0 : 0 ≤ A := by positivity
  have hA2 : A ^ 2 ≤ S := by
    have : ((1 - x ^ 2) ^ (lam / 2)) ^ 2 = (1 - x ^ 2) ^ lam := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h1x.le]; norm_num
    rw [hA, mul_pow, this, sq_abs]; exact hS
  -- it suffices to bound `N^(1-λ)² S`
  suffices key : (N ^ (1 - lam)) ^ 2 * S < ((2 : ℝ) ^ (1 - lam) / Real.Gamma lam) ^ 2 by
    rw [mul_assoc, ← hA]
    have hNA : 0 ≤ N ^ (1 - lam) * A := by positivity
    have : (N ^ (1 - lam) * A) ^ 2 < ((2 : ℝ) ^ (1 - lam) / Real.Gamma lam) ^ 2 := by
      rw [mul_pow]
      calc _ ≤ (N ^ (1 - lam)) ^ 2 * S := by gcongr
        _ < _ := key
    exact lt_of_pow_lt_pow_left₀ 2 hR.le this
  have hrefl (t : ℝ) : q.eval (-t) = (-1) ^ n * q.eval t := by
    have h := ultrasphPoly_reflection (lam := (lam : ℂ)) (by simpa using hlamh) n (t : ℂ)
    rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, hq, hq] at h
    exact_mod_cast h
  have hasc (a : ℝ) (ha : 0 < a) (k : ℕ) :
      (ascPochhammer ℝ k).eval a = Real.Gamma (k + a) / Real.Gamma a := by
    rw [add_comm, opIneq_Gamma_add_nat ha, mul_div_assoc, div_self (Real.Gamma_pos_of_pos ha).ne',
      mul_one]
  have hNsq : (N ^ (1 - lam)) ^ 2 = N ^ (2 - 2 * lam) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num; ring_nf
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · -- even degree
    subst hm
    have hev (t : ℝ) : q.eval (-t) = q.eval t := by
      rw [hrefl, pow_mul, neg_one_sq, one_pow, one_mul]
    have hd0 := derivative_eval_zero_of_even hev
    have hq0 : q.eval 0 = (-1) ^ m * ((ascPochhammer ℝ m).eval lam / m !) := by
      have h := ultrasphPoly_even_at_zero (lam := (lam : ℂ)) (by simpa using hlamh) m
      rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, hq, poch_ofReal] at h
      apply Complex.ofReal_injective
      rw [h]; push_cast; ring
    have hS0 : S = ((ascPochhammer ℝ m).eval lam / m !) ^ 2 := by
      rw [hSdef, hd0, hq0, mul_pow, ← pow_mul, mul_comm m 2, pow_mul, neg_one_sq, one_pow]
      ring
    rw [hasc lam hlam, ← Real.Gamma_nat_eq_factorial] at hS0
    have hlt : N ^ (1 - lam) * (Real.Gamma (m + lam) / Real.Gamma lam / Real.Gamma (m + 1)) <
        (2 : ℝ) ^ (1 - lam) / Real.Gamma lam := by
      rw [show N = 2 * m + lam by rw [hN]; push_cast; ring]
      exact bernstein_even_bound hlam hlam1 m
    rw [hS0, ← mul_pow]
    have h0 : 0 ≤ N ^ (1 - lam) * (Real.Gamma (m + lam) / Real.Gamma lam /
        Real.Gamma (m + 1)) := by
      have := Real.Gamma_pos_of_pos (show (0 : ℝ) < m + lam by positivity)
      have := Real.Gamma_pos_of_pos (show (0 : ℝ) < m + 1 by positivity)
      positivity
    exact pow_lt_pow_left₀ hlt h0 two_ne_zero
  · -- odd degree
    subst hm
    have hodd (t : ℝ) : q.eval (-t) = -q.eval t := by
      rw [hrefl, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul]
    have hq0 : q.eval 0 = 0 := by have := hodd 0; rw [neg_zero] at this; linarith
    -- the derivative at `0`
    have hfun : ultrasphPoly (lam : ℂ) (2 * m + 1) = fun z => (q.map (algebraMap ℝ ℂ)).eval z :=
      funext fun z => (eval_map_ultrasphPolyR hlamh _ z).symm
    have hder : deriv (ultrasphPoly (lam : ℂ) (2 * m + 1)) 0 =
        (((derivative q).eval 0 : ℝ) : ℂ) := by
      rw [hfun, ((q.map (algebraMap ℝ ℂ)).hasDerivAt 0).deriv, derivative_map,
        show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, eval_map_ofReal]
    have hder' := ultrasphPoly_derivative (lam := (lam : ℂ)) (by simpa using hlamh) (2 * m) 0
    rw [ultrasphPoly_even_at_zero (by simp; linarith), hder,
      show (lam : ℂ) + 1 = ((lam + 1 : ℝ) : ℂ) by push_cast; ring, poch_ofReal] at hder'
    have hlam1' : (0 : ℝ) < lam + 1 := by linarith
    have hGl1 : Real.Gamma (lam + 1) = lam * Real.Gamma lam := Real.Gamma_add_one hlam.ne'
    set r := Real.Gamma (m + 1 + lam) / Real.Gamma (m + 1) with hr
    have hq'0 : (derivative q).eval 0 = (-1) ^ m * (2 * r / Real.Gamma lam) := by
      apply Complex.ofReal_injective
      have hf : ((m ! : ℕ) : ℂ) = ((Real.Gamma (m + 1) : ℝ) : ℂ) := by
        rw [Real.Gamma_nat_eq_factorial]; push_cast; rfl
      rw [hder', hasc (lam + 1) hlam1', hGl1, hf, hr,
        show (m : ℝ) + (lam + 1) = m + 1 + lam by ring]
      push_cast
      have h1 : (Real.Gamma lam : ℂ) ≠ 0 := by exact_mod_cast hGl.ne'
      have h2 : (Real.Gamma (m + 1) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < m + 1)).ne'
      have h3 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
      field_simp
    have hS0 : S = (2 * r / Real.Gamma lam) ^ 2 / (N ^ 2 + c) := by
      rw [hSdef, hq0, hq'0, mul_pow, ← pow_mul, mul_comm m 2, pow_mul, neg_one_sq, one_pow]
      ring
    rw [hS0, hNsq]
    have hNe : N = 2 * m + 1 + lam := by rw [hN]; push_cast; ring
    rw [hNe]
    exact bernstein_odd_bound hlam hlam1 m

/-- The parameter-zero Laguerre estimate is the norm bound for a positive cosine transform. -/
theorem laguerrePolyL_zero_parameter_bound (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x / 2) * ‖laguerrePolyL 0 n x‖ ≤ 1 := by
  let y := Real.sqrt x
  let w : ℝ → ℝ := fun t => Real.exp (-(t ^ 2) / 2) * (aeval t (hermite n) : ℝ) ^ 2
  have hw : IntegrableOn w (Set.Ioi 0) := by
    have hi := (TauCeti.integrable_aeval_mul_gaussian ((hermite n) ^ 2)).restrict (s := Set.Ioi 0)
    apply hi.congr
    filter_upwards [] with t
    simp only [w, map_pow]
    rw [show -(t ^ 2 / 2) = -(t ^ 2) / 2 by ring]
    ring
  have hw0 (t : ℝ) : 0 ≤ w t := by dsimp [w]; positivity
  have hcast (t : ℝ) : (aeval (t : ℂ) (hermite n) : ℂ) =
      ((aeval t (hermite n) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) t (hermite n)
  have hF (v t : ℝ) : exp (-(t : ℂ) ^ 2 / 2) * (aeval (t : ℂ) (hermite n) : ℂ) *
      aeval (t : ℂ) (hermite n) * Real.cos (t * v) =
      ((w t : ℝ) : ℂ) * (Real.cos (t * v) : ℂ) := by
    rw [hcast]
    have he : exp (-(t : ℂ) ^ 2 / 2) = (Real.exp (-(t ^ 2) / 2) : ℂ) := by
      rw [ofReal_exp]; congr 1; push_cast; ring
    rw [he]
    simp only [w, ofReal_mul, ofReal_pow]
    ring
  have hT (v : ℝ) := hermite_product_cosine_transform 0 n v
  have hL0 : laguerrePolyL 0 n 0 = 1 := by
    rw [laguerrePolyL_at_zero]
    simp [Nat.factorial_ne_zero]
  have hzero := hT 0
  norm_num only [Nat.cast_zero, mul_zero, add_zero, zero_add, pow_zero, one_mul,
    Complex.ofReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    neg_zero, zero_div, exp_zero, mul_one, hL0, Real.cos_zero, ofReal_one] at hzero
  have hF0 (t : ℝ) := hF 0 t
  simp only [mul_zero, Real.cos_zero, ofReal_one, mul_one] at hF0
  simp_rw [hF0] at hzero
  have hwval : ∫ t : ℝ in Set.Ioi 0, w t = Real.sqrt (Real.pi / 2) * n.factorial := by
    apply Complex.ofReal_injective
    simpa only [integral_complex_ofReal, ofReal_mul, ofReal_natCast] using hzero
  have hbound : ‖∫ t : ℝ in Set.Ioi 0, ((w t : ℝ) : ℂ) * (Real.cos (t * y) : ℂ)‖ ≤
      ∫ t : ℝ in Set.Ioi 0, w t := by
    apply norm_integral_le_of_norm_le hw
    filter_upwards [] with t
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hw0 t),
      Real.norm_eq_abs]
    exact mul_le_of_le_one_right (hw0 t) (Real.abs_cos_le_one _)
  have hy := hT y
  norm_num only [Nat.cast_zero, mul_zero, add_zero, zero_add, pow_zero, one_mul, mul_one] at hy
  simp_rw [hF] at hy
  rw [hy, hwval] at hbound
  simp only [norm_mul, Complex.norm_real, Complex.norm_natCast,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hbound
  have hy2 : y ^ 2 = x := Real.sq_sqrt hx
  rw [← ofReal_pow, hy2, Complex.norm_exp] at hbound
  norm_num only [div_re, neg_re, ofReal_re, re_ofNat, im_ofNat,
    mul_zero, add_zero, Complex.normSq_ofNat] at hbound
  rw [show -x * 2 / 4 = -x / 2 by ring] at hbound
  have hpos : 0 < Real.sqrt (Real.pi / 2) * (n.factorial : ℝ) := by positivity
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `Real.exp (-x / 2) *
‖laguerrePolyL α n x‖ ≤ (poch (α + 1) n).re / n.factorial`. -/
@[dlmf 18.14.E8]
theorem laguerrePolyL_bound {α x : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ x) (n : ℕ) :
    Real.exp (-x / 2) * ‖laguerrePolyL α n x‖ ≤ (poch (α + 1) n).re / n.factorial := by
  have hc : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := by
    intro k hk
    have h := congrArg Complex.re hk
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hz : ∀ k : ℕ, (0 : ℂ) + 1 ≠ -(k : ℂ) := by
    intro k hk
    have h := congrArg Complex.re hk
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let c : ℕ → ℝ := fun k => (ascPochhammer ℝ (n - k)).eval α / (n - k).factorial
  have hc0 (k : ℕ) : 0 ≤ c k := div_nonneg (ascPochhammer_eval_nonneg hα _) (by positivity)
  have hcoeff (k : ℕ) : poch (α : ℂ) (n - k) / ((n - k).factorial : ℂ) = (c k : ℂ) := by
    rw [poch_ofReal]
    simp only [c, ofReal_div, ofReal_natCast]
  have hconn (t : ℂ) : laguerrePolyL α n t = ∑ k ∈ Finset.range (n + 1),
      (c k : ℂ) * laguerrePolyL 0 k t := by
    have hh := laguerrePolyL_connection 0 (α : ℂ) n t
    rw [laguerreExtended_eq hc] at hh
    simpa only [sub_zero, hcoeff, laguerreExtended_eq hz] using hh
  have hsum : ∑ k ∈ Finset.range (n + 1), c k = (poch (α + 1) n).re / n.factorial := by
    have hL0 (k : ℕ) : laguerrePolyL 0 k 0 = 1 := by
      rw [laguerrePolyL_at_zero]
      simp [Nat.factorial_ne_zero]
    have hh := congrArg Complex.re (hconn 0)
    simp only [hL0, mul_one, Complex.re_sum, ofReal_re] at hh
    rw [laguerrePolyL_at_zero] at hh
    simpa only [← ofReal_natCast, Complex.div_ofReal_re] using hh.symm
  rw [hconn]
  calc
    _ ≤ Real.exp (-x / 2) * ∑ k ∈ Finset.range (n + 1), ‖(c k : ℂ) * laguerrePolyL 0 k x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
    _ = ∑ k ∈ Finset.range (n + 1), c k *
        (Real.exp (-x / 2) * ‖laguerrePolyL 0 k x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 k)]
      ring
    _ ≤ ∑ k ∈ Finset.range (n + 1), c k := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_of_le_one_right (hc0 k) (laguerrePolyL_zero_parameter_bound k hx)
    _ = _ := hsum

/-- Estimate under the stated parameter and domain assumptions: `Real.exp (-(x ^ 2) / 2) * |aeval
x (hermitePolyH n)| ≤ Real.sqrt (2 ^ n * n.factorial)`. -/
@[dlmf 18.14.E9]
theorem hermitePolyH_bound (n : ℕ) (x : ℝ) :
    Real.exp (-(x ^ 2) / 2) * |aeval x (hermitePolyH n)| ≤ Real.sqrt (2 ^ n * n.factorial) := by
  sorry

/-- The stated relation follows from the given hypotheses: `(jacobiPolyP α β (n + 1) x /
jacobiPolyP α β (n + 1) 1).re ^ 2 ≥ (jacobiPolyP α β n x / jacobiPolyP α β n 1).re *
(jacobiPolyP α β (n + 2) x / jacobiPolyP α β (n + 2) 1).re`. -/
@[dlmf 18.14.E11]
theorem jacobi_turan {α β x : ℝ} (hα : -1 < α) (hαβ : α ≤ β) (hx : |x| ≤ 1) (n : ℕ) :
    (jacobiPolyP α β (n + 1) x / jacobiPolyP α β (n + 1) 1).re ^ 2 ≥
      (jacobiPolyP α β n x / jacobiPolyP α β n 1).re
          * (jacobiPolyP α β (n + 2) x / jacobiPolyP α β (n + 2) 1).re := by
  sorry

/-- Turán's inequality for Laguerre polynomials, via the identity
`(n+2)Δₙ = (L_{n+1} - Lₙ)² + (n+α)Δ_{n-1}` for `Δₙ = L_{n+1}² - Lₙ L_{n+2}`.
Stronger than DLMF: the hypothesis `0 ≤ x` is not used; the inequality holds for all real `x`. -/
@[dlmf 18.14.E12]
theorem laguerrePolyL_turan {α x : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ x) (n : ℕ) :
    (laguerrePolyL α (n + 1) x).re ^ 2 ≥ (laguerrePolyL α n x).re
        * (laguerrePolyL α (n + 2) x).re := by
  have _ := hx
  have hα' : -1 < ((α : ℂ)).re := by simp; linarith
  set L : ℕ → ℝ := fun k => (laguerrePolyLR α k).eval x with hL
  have hreal (k : ℕ) : laguerrePolyL α k x = (L k : ℂ) := (eval_laguerrePolyLR α k x).symm
  have hrec (k : ℕ) : ((k : ℝ) + 2) * L (k + 2) =
      (2 * k + α + 3 - x) * L (k + 1) - (k + α + 1) * L k := by
    have h := laguerrePolyL_recurrence hα' k x
    rw [hreal, hreal, hreal] at h
    apply Complex.ofReal_injective
    push_cast
    linear_combination h
  have h0 : L 0 = 1 := by
    apply Complex.ofReal_injective; rw [← hreal]; simp
  have h1 : L 1 = α + 1 - x := by
    apply Complex.ofReal_injective; rw [← hreal]
    unfold laguerrePolyL
    rw [DLMF.Confluent.kummerM_eq_sum_neg_nat]
    have : (α : ℂ) + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp [Finset.sum_range_succ, poch_one, poch_zero]
    field_simp
    ring
  have hD (k : ℕ) : ((k : ℝ) + 3) * (L (k + 2) ^ 2 - L (k + 1) * L (k + 3)) =
      (L (k + 2) - L (k + 1)) ^ 2 + (k + α + 1) * (L (k + 1) ^ 2 - L k * L (k + 2)) := by
    have e1 := hrec k
    have e2 := hrec (k + 1)
    push_cast at e2
    rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring] at e2
    linear_combination (-(L (k + 1))) * e2 + L (k + 2) * e1
  have key : ∀ k : ℕ, 0 ≤ L (k + 1) ^ 2 - L k * L (k + 2) := by
    intro k
    induction k with
    | zero =>
      have e := hrec 0
      simp only [Nat.cast_zero, zero_add, mul_zero, h0, h1] at e ⊢
      have : L 2 = ((3 + α - x) * (α + 1 - x) - (α + 1)) / 2 := by linarith
      rw [this]; nlinarith [sq_nonneg (α - x)]
    | succ k ih =>
      have h := hD k
      have hk : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      have : 0 ≤ ((k : ℝ) + 3) * (L (k + 1 + 1) ^ 2 - L (k + 1) * L (k + 1 + 2)) := by
        rw [show k + 1 + 1 = k + 2 by ring, show k + 1 + 2 = k + 3 by ring, h]
        have : (0 : ℝ) ≤ k + α + 1 := by positivity
        positivity
      exact (mul_nonneg_iff_of_pos_left hk).mp this
  simp only [hreal, Complex.ofReal_re]
  linarith [key n]

/-- The stated relation follows from the given hypotheses: `(aeval x (hermitePolyH (n + 1)) : ℝ) ^
2 ≥ aeval x (hermitePolyH n) * aeval x (hermitePolyH (n + 2))`. -/
@[dlmf 18.14.E13]
theorem hermitePolyH_turan (n : ℕ) (x : ℝ) :
    (aeval x (hermitePolyH (n + 1)) : ℝ) ^ 2 ≥ aeval x (hermitePolyH n)
        * aeval x (hermitePolyH (n + 2)) := by
  set H : ℕ → ℝ := fun k => (aeval x (hermitePolyH k) : ℝ) with hH
  have hrec : ∀ k : ℕ, H (k + 2) = 2 * x * H (k + 1) - 2 * (k + 1) * H k := by
    intro k
    simp only [hH]
    rw [hermitePolyH_recurrence k]
    simp only [map_sub, map_mul, map_add, aeval_X, map_ofNat, map_natCast, map_one]
  have hD : ∀ n : ℕ, H (n + 1 + 1) ^ 2 - H (n + 1) * H (n + 1 + 2) =
      2 * (n + 1) * (H (n + 1) ^ 2 - H n * H (n + 2)) + 2 * H (n + 1) ^ 2 := by
    intro n
    have h1 := hrec n
    have h2 := hrec (n + 1)
    push_cast at h2
    rw [show n + 1 + 2 = n + 1 + 1 + 1 by ring] at h2 ⊢
    rw [show n + 2 = n + 1 + 1 by ring] at h1 ⊢
    linear_combination (H (n + 1 + 1)) * h1 - H (n + 1) * h2
  have key : ∀ n : ℕ, 0 ≤ H (n + 1) ^ 2 - H n * H (n + 2) := by
    intro n
    induction n with
    | zero =>
      simp only [hH, Nat.zero_add, hermitePolyH_one, hermitePolyH_two, hermitePolyH_zero, map_sub,
        map_mul, map_pow, aeval_X, map_ofNat, map_one]
      nlinarith
    | succ n ih =>
      rw [hD n]
      have h1 : (0 : ℝ) ≤ 2 * (n + 1) := by positivity
      have h2 : (0 : ℝ) ≤ 2 * H (n + 1) ^ 2 := by positivity
      exact add_nonneg (mul_nonneg h1 ih) h2
  have := key n
  change 0 ≤ H (n + 1) ^ 2 - H n * H (n + 2) at this
  show H (n + 1) ^ 2 ≥ H n * H (n + 2)
  linarith

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ (∑ m ∈ Finset.range (n + 1),
poch (lam + 1) (n - m) / (n - m).factorial * (poch (lam + 1) m / m.factorial) * jacobiPolyP α
β m x / jacobiPolyP β α m 1).re`. -/
@[dlmf 18.14.E25]
theorem jacobi_positive_weighted_sum {α β lam x : ℝ} (hα : -1 < α) (hβ : -1 / 2 ≤ β)
    (hlam : 0 ≤ lam) (hαβ : lam ≤ α + β) (hx : -1 ≤ x) (n : ℕ) :
    0 ≤ (∑ m ∈ Finset.range (n + 1), poch (lam + 1) (n - m) / (n - m).factorial *
      (poch (lam + 1) m / m.factorial) * jacobiPolyP α β m x / jacobiPolyP β α m 1).re := by
  sorry

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ (∑ m ∈ Finset.range (n + 1),
jacobiPolyP α β m x / jacobiPolyP β α m 1).re`. -/
@[dlmf 18.14.E26]
theorem jacobi_positive_sum {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hparams : (0 ≤ α + β ∧ -1 / 2 ≤ β) ∨ (-2 ≤ α + β ∧ 0 ≤ β)) (hx : -1 ≤ x) (n : ℕ) :
    0 ≤ (∑ m ∈ Finset.range (n + 1), jacobiPolyP α β m x / jacobiPolyP β α m 1).re := by
  sorry

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ (∑ m ∈ Finset.range (n + 1),
poch (lam + 1) (n - m) / (n - m).factorial * (poch (lam + 1) m / m.factorial) * (-1 : ℂ) ^ m *
laguerrePolyL β m x / laguerrePolyL β m 0).re`. -/
@[dlmf 18.14.E27]
theorem laguerrePolyL_positive_weighted_sum {β lam x : ℝ} (hβ : -1 / 2 ≤ β) (hlam : -1 / 2 ≤ lam)
    (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ (∑ m ∈ Finset.range (n + 1), poch (lam + 1) (n - m) / (n - m).factorial *
      (poch (lam + 1) m / m.factorial) * (-1 : ℂ) ^ m * laguerrePolyL β m x
          / laguerrePolyL β m 0).re := by
  sorry

/-- Formula under the stated hypotheses: `∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, x i ∈ Set.Ioo (-1)
1) ∧ ∀ z : ℂ, jacobiPolyP α β n z = 0 ↔ ∃ i, z = (x i : ℂ)`. -/
@[dlmf 18.16.i]
theorem jacobi_zeros {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, x i ∈ Set.Ioo (-1) 1) ∧
      ∀ z : ℂ, jacobiPolyP α β n z = 0 ↔ ∃ i, z = (x i : ℂ) :=
  jacobiPolyP_zeros_Ioo hα hβ n

/-- Estimate under the stated parameter and domain assumptions: `∃ x : Fin n → ℝ, StrictMono x ∧
(∀ i, 0 < x i) ∧ ∀ z : ℂ, laguerrePolyL α n z = 0 ↔ ∃ i, z = (x i : ℂ)`. -/
@[dlmf 18.16.iv]
theorem laguerrePolyL_zeros {α : ℝ} (hα : -1 < α) (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, 0 < x i) ∧
      ∀ z : ℂ, laguerrePolyL α n z = 0 ↔ ∃ i, z = (x i : ℂ) :=
  laguerrePolyL_zeros_pos hα n

/-- Estimate under the stated parameter and domain assumptions: `∃ x : Fin n → ℝ, StrictMono x ∧
(∀ i, |x i| < Real.sqrt (2 * n + 1)) ∧ ∀ z : ℂ, (aeval z (hermitePolyH n) : ℂ) = 0 ↔ ∃ i, z =
(x i : ℂ)`. -/
@[dlmf 18.16.E16]
theorem hermitePolyH_zeros (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, |x i| < Real.sqrt (2 * n + 1)) ∧
      ∀ z : ℂ, (aeval z (hermitePolyH n) : ℂ) = 0 ↔ ∃ i, z = (x i : ℂ) :=
  hermitePolyH_zeros_bound n

/-- The map `(fun n : ℕ => Real.sqrt n * (Real.sin (θ / 2)) ^ (α + 1 / 2) * (Real.cos (θ / 2)) ^
(β + 1 / 2) * (jacobiPolyP α β n (Real.cos θ)).re - Real.cos ((n + (α + β + 1) / 2) * θ - (α +
1 / 2) * Real.pi / 2) / Real.sqrt Real.pi)` tends to `(𝓝 0)` along `atTop`. -/
@[dlmf 18.15.E4_5]
theorem jacobi_darboux_asymptotic {α β θ : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Tendsto (fun n : ℕ => Real.sqrt n * (Real.sin (θ / 2)) ^ (α + 1 / 2) *
      (Real.cos (θ / 2)) ^ (β + 1 / 2) * (jacobiPolyP α β n (Real.cos θ)).re -
      Real.cos ((n + (α + β + 1) / 2) * θ - (α + 1 / 2) * Real.pi / 2) / Real.sqrt Real.pi) atTop (𝓝 0) := by
  sorry

/-- Estimate under the stated parameter and domain assumptions: `((1 + x) / 2) ^ (β / 2) *
‖jacobiPolyP α β n x‖ ≤ (poch (α + 1) n).re / n.factorial`. -/
@[dlmf 18.14.E3_5]
theorem jacobi_weighted_bound {α β x : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hx : |x| ≤ 1) (n : ℕ) :
    ((1 + x) / 2) ^ (β / 2) * ‖jacobiPolyP α β n x‖ ≤ (poch (α + 1) n).re / n.factorial := by
  sorry

/-! ### Laguerre's inequality and the Laguerre zero bounds -/

/-- Cauchy–Schwarz for a multiset of reals: `(∑ a)² ≤ #t ∑ a²`. -/
theorem multiset_sq_sum_le_card_mul_sum_sq (t : Multiset ℝ) :
    t.sum ^ 2 ≤ t.card * (t.map (· ^ 2)).sum := by
  have hexp : ∀ c S : ℝ, (t.map fun a => (c * a - S) ^ 2).sum =
      c ^ 2 * (t.map (· ^ 2)).sum - 2 * c * S * t.sum + t.card * S ^ 2 := by
    intro c S
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
      push_cast; ring
  have h0 : 0 ≤ (t.map fun a => ((t.card : ℝ) * a - t.sum) ^ 2).sum :=
    Multiset.sum_nonneg fun x hx => by
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hx
      positivity
  rw [hexp] at h0
  rcases Nat.eq_zero_or_pos t.card with h | h
  · rw [Multiset.card_eq_zero.mp h]; simp
  · have hc : (0 : ℝ) < t.card := by exact_mod_cast h
    nlinarith

/-- Derivative of `t ↦ ∑_{z ∈ s} 1/(t - z)` away from `s`. -/
theorem hasDerivAt_multiset_sum_recip_sub (s : Multiset ℝ) {x : ℝ} (hx : x ∉ s) :
    HasDerivAt (fun t => (s.map fun z => 1 / (t - z)).sum)
      (-(s.map fun z => 1 / (x - z) ^ 2).sum) x := by
  induction s using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const x (0 : ℝ)
  | cons a s ih =>
    have ha : x - a ≠ 0 := sub_ne_zero.mpr fun h => hx (h ▸ Multiset.mem_cons_self _ _)
    have hs : x ∉ s := fun h => hx (Multiset.mem_cons_of_mem h)
    have h1 : HasDerivAt (fun t => 1 / (t - a)) (-(1 / (x - a) ^ 2)) x := by
      have := ((hasDerivAt_id x).sub_const a).inv ha
      convert this using 1
      · ext t; simp [one_div]
      · simp [neg_div, one_div]
    simp only [Multiset.map_cons, Multiset.sum_cons, neg_add]
    exact h1.add (ih hs)

/-- **Laguerre's inequality** for a real polynomial with only real zeros, at a point where it
does not vanish: `(m - 1) g'² - m g g'' ≥ 0` with `m = deg g`. -/
theorem laguerre_inequality {g : ℝ[X]} (hs : g.Splits) {x : ℝ} (hx : g.eval x ≠ 0) :
    0 ≤ ((g.natDegree : ℝ) - 1) * (derivative g).eval x ^ 2 -
      g.natDegree * g.eval x * (derivative (derivative g)).eval x := by
  set s := g.roots
  set L : ℝ → ℝ := fun t => (s.map fun z => 1 / (t - z)).sum
  set P : ℝ → ℝ := fun t => (s.map fun z => 1 / (t - z) ^ 2).sum
  have hxs : x ∉ s := fun h => hx ((mem_roots'.mp h).2)
  have h1 : (derivative g).eval x = g.eval x * L x := hs.eval_derivative_eq_eval_mul_sum hx
  -- second derivative
  have hev : ∀ᶠ t in 𝓝 x, (derivative g).eval t = g.eval t * L t := by
    filter_upwards [g.continuous.continuousAt.eventually_ne hx] with t ht
    exact hs.eval_derivative_eq_eval_mul_sum ht
  have hd1 : HasDerivAt (fun t => g.eval t * L t)
      ((derivative g).eval x * L x + g.eval x * (-P x)) x :=
    (g.hasDerivAt x).mul (hasDerivAt_multiset_sum_recip_sub s hxs)
  have hd2 : HasDerivAt (fun t => (derivative g).eval t)
      ((derivative (derivative g)).eval x) x := (derivative g).hasDerivAt x
  have h2 : (derivative (derivative g)).eval x =
      (derivative g).eval x * L x + g.eval x * (-P x) :=
    hd2.unique (hd1.congr_of_eventuallyEq hev)
  have hm : (g.natDegree : ℝ) = (s.card : ℝ) := by rw [hs.natDegree_eq_card_roots]
  have hCS : L x ^ 2 ≤ s.card * P x := by
    have := multiset_sq_sum_le_card_mul_sum_sq (s.map fun z => 1 / (x - z))
    simpa [L, P, Multiset.map_map, Function.comp_def, div_pow] using this
  rw [h2, h1, hm]
  have : ((s.card : ℝ) - 1) * (g.eval x * L x) ^ 2 -
      s.card * g.eval x * (g.eval x * L x * L x + g.eval x * -P x) =
        g.eval x ^ 2 * (s.card * P x - L x ^ 2) := by ring
  rw [this]
  exact mul_nonneg (sq_nonneg _) (by linarith)

/-- The real Laguerre polynomial satisfies Laguerre's differential equation. -/
theorem laguerrePolyLR_ode {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℝ) :
    x * (derivative (derivative (laguerrePolyLR α n))).eval x +
      (α + 1 - x) * (derivative (laguerrePolyLR α n)).eval x +
      n * (laguerrePolyLR α n).eval x = 0 := by
  set p := laguerrePolyLR α n
  set q := p.map (algebraMap ℝ ℂ)
  have hfun : laguerrePolyL (α : ℂ) n = fun z => q.eval z :=
    funext fun z => (eval_map_laguerrePolyLR α n z).symm
  have hd : deriv (fun z => q.eval z) = fun z => (derivative q).eval z :=
    funext fun z => Polynomial.deriv q
  have h := laguerrePolyL_differential_equation (α := (α : ℂ)) (by simpa using hα) n x
  rw [hfun, hd, Polynomial.deriv] at h
  simp only [q, derivative_map, eval_map_ofReal] at h
  exact_mod_cast h

/-- The quadratic inequality satisfied by every zero of `L_n^{(α)}`, from Laguerre's
inequality applied to `L_n^{(α)}(t)/(t - x)` and the differential equation. -/
theorem laguerrePolyL_zero_quadratic {α : ℝ} (hα : -1 < α) {n : ℕ} {x : ℝ}
    (hx : laguerrePolyL α n x = 0) :
    4 * ((n : ℝ) - 1) * ((x - α - 2) * (x - α - 1) + (1 - n) * x) -
      3 * ((n : ℝ) - 2) * (x - α - 1) ^ 2 ≤ 0 := by
  set p := laguerrePolyLR α n with hp
  have hpx : p.eval x = 0 := by
    have := eval_laguerrePolyLR α n x
    rw [hx] at this
    exact_mod_cast this
  have hODE := laguerrePolyLR_ode hα n
  -- the differentiated equation, as a polynomial identity
  have hQ : X * derivative (derivative p) + (C (α + 1) - X) * derivative p + C (n : ℝ) * p = 0 :=
    Polynomial.funext fun t => by
      simp only [eval_add, eval_mul, eval_X, eval_sub, eval_C, eval_zero]
      linear_combination hODE t
  have hQ' := congrArg (fun q => (derivative q).eval x) hQ
  simp only [derivative_add, derivative_mul, derivative_X, derivative_sub, derivative_C,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_one, eval_neg, eval_zero, derivative_zero,
    zero_mul, one_mul, zero_sub] at hQ'
  have E1 := hODE x
  rw [hpx, mul_zero, add_zero] at E1
  -- the cofactor `g = p / (X - x)`
  set g := p /ₘ (X - C x) with hg
  have hpg : (X - C x) * g = p := mul_divByMonic_eq_iff_isRoot.mpr hpx
  have hp0 : p ≠ 0 := laguerrePolyLR_ne_zero hα n
  have hg0 : g ≠ 0 := fun h => hp0 (by rw [← hpg, h, mul_zero])
  have d1 : (derivative p).eval x = g.eval x := by
    rw [← hpg]; simp [derivative_mul]
  have d2 : (derivative (derivative p)).eval x = 2 * (derivative g).eval x := by
    rw [← hpg]; simp [derivative_mul]; ring
  have d3 : (derivative (derivative (derivative p))).eval x =
      3 * (derivative (derivative g)).eval x := by
    rw [← hpg]; simp [derivative_mul]; ring
  obtain ⟨hcard, hnodup⟩ := orthogonal_polynomials_roots (laguerre_isOrthogonalPolynomials hα) n
  have hroots : p.roots = x ::ₘ g.roots := by
    rw [← hpg, roots_mul (by rw [hpg]; exact hp0), roots_X_sub_C, Multiset.singleton_add]
  rw [hroots, Multiset.nodup_cons] at hnodup
  have hgx : g.eval x ≠ 0 := fun h => hnodup.1 ((mem_roots hg0).mpr h)
  have hdeg : p.natDegree = 1 + g.natDegree := by
    rw [← hpg, natDegree_mul (X_sub_C_ne_zero x) hg0, natDegree_X_sub_C]
  have hpdeg : p.natDegree = n := laguerrePolyLR_natDegree hα n
  have hgcard : g.roots.card = g.natDegree := by
    have : p.roots.card = n := hcard
    rw [hroots, Multiset.card_cons] at this
    omega
  have hm : (g.natDegree : ℝ) = n - 1 := by
    have : g.natDegree + 1 = n := by omega
    rw [← this]; push_cast; ring
  have hL := laguerre_inequality (splits_iff_card_roots.mpr hgcard) hgx
  rw [hm] at hL
  set G0 := g.eval x
  set G1 := (derivative g).eval x
  set G2 := (derivative (derivative g)).eval x
  rw [d1, d2] at E1
  rw [d1, d2, d3] at hQ'
  have hT : 12 * x ^ 2 * (((n : ℝ) - 1 - 1) * G1 ^ 2 - (n - 1) * G0 * G2) +
      (4 * ((n : ℝ) - 1) * ((x - α - 2) * (x - α - 1) + (1 - n) * x) -
        3 * ((n : ℝ) - 2) * (x - α - 1) ^ 2) * G0 ^ 2 = 0 := by
    linear_combination
      (G0 * (α * n + 2 * α - n * x + 5 * n - 2 * x - 2) + 3 * (2 * G1) * x * (n - 2)) * E1 +
        (-4 * ((n : ℝ) - 1) * x * G0) * hQ'
  have hpos : 0 < G0 ^ 2 := by positivity
  by_contra! hc
  have : 0 ≤ 12 * x ^ 2 * (((n : ℝ) - 1 - 1) * G1 ^ 2 - (n - 1) * G0 * G2) :=
    mul_nonneg (by positivity) hL
  nlinarith [mul_pos hc hpos]

/-- Both Laguerre zero bounds as a two-sided inequality. -/
theorem laguerrePolyL_zero_bounds {α : ℝ} (hα : -1 < α) {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : laguerrePolyL α n x = 0) :
    ((n : ℝ) - 1 - Real.sqrt (n ^ 2 + (n + 2) * (α + 1))) ^ 2 - 1 ≤ (n + 2) * x ∧
      (n + 2) * x ≤ ((n : ℝ) - 1 + Real.sqrt (n ^ 2 + (n + 2) * (α + 1))) ^ 2 - 1 := by
  have hq := laguerrePolyL_zero_quadratic hα hx
  set r := Real.sqrt (n ^ 2 + (n + 2) * (α + 1))
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hα1 : (0 : ℝ) < α + 1 := by linarith
  have hr2 : r ^ 2 = n ^ 2 + (n + 2) * (α + 1) := Real.sq_sqrt (by positivity)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : ((n + 2) * x + 1 - ((n - 1) ^ 2 + r ^ 2)) ^ 2 ≤ (2 * (n - 1) * r) ^ 2 := by
    have hid : ((n + 2) * x + 1 - ((n - 1) ^ 2 + r ^ 2)) ^ 2 - (2 * (n - 1) * r) ^ 2 =
        (n + 2) * (4 * ((n : ℝ) - 1) * ((x - α - 2) * (x - α - 1) + (1 - n) * x) -
          3 * ((n : ℝ) - 2) * (x - α - 1) ^ 2) := by
      have : (2 * ((n : ℝ) - 1) * r) ^ 2 = 4 * (n - 1) ^ 2 * r ^ 2 := by ring
      rw [this]
      have e : ((n : ℝ) + 2) * x + 1 - ((n - 1) ^ 2 + r ^ 2) =
          (n + 2) * x + 1 - ((n - 1) ^ 2 + (n ^ 2 + (n + 2) * (α + 1))) := by rw [hr2]
      rw [e, hr2]; ring
    nlinarith
  obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' hsq (by positivity)
  constructor <;> nlinarith

/-- Estimate under the stated parameter and domain assumptions: `((n : ℝ) - 1 - Real.sqrt (n ^ 2 +
(n + 2) * (α + 1))) ^ 2 - 1 ≤ (n + 2) * x`. -/
@[dlmf 18.16.E12]
theorem laguerrePolyL_zero_lower_bound {α : ℝ} (hα : -1 < α) {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : laguerrePolyL α n x = 0) :
    ((n : ℝ) - 1 - Real.sqrt (n ^ 2 + (n + 2) * (α + 1))) ^ 2 - 1 ≤ (n + 2) * x :=
  (laguerrePolyL_zero_bounds hα hn hx).1

/-- The stated relation follows from the given hypotheses: `((n : ℝ) - 1 + Real.sqrt (n ^ 2 + (n +
2) * (α + 1))) ^ 2 - 1 ≥ (n + 2) * x`. -/
@[dlmf 18.16.E13]
theorem laguerrePolyL_zero_upper_bound {α : ℝ} (hα : -1 < α) {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : laguerrePolyL α n x = 0) :
    ((n : ℝ) - 1 + Real.sqrt (n ^ 2 + (n + 2) * (α + 1))) ^ 2 - 1 ≥ (n + 2) * x :=
  (laguerrePolyL_zero_bounds hα hn hx).2

/-- Discriminant expressed through a complete root list. The identities below
assume positive degree; this avoids conventions for the discriminant of a constant. -/
@[dlmf 18.2.E20]
def rootDiscriminant {n : ℕ} (leading : ℝ) (x : Fin n → ℝ) : ℝ :=
  leading ^ (2 * (n : ℤ) - 2) * ∏ i : Fin n, ∏ j : Fin n,
    if i < j then (x i - x j) ^ 2 else 1

end DLMF.OrthogonalPolynomials
end
end
