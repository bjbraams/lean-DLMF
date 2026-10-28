/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Elementary.AlgebraicValues

/-!
# Gauss values at cubic and sixth-root arguments

Exact evaluations at cubic and sixth-root arguments, obtained through contiguous identities and
branch calculations.

Source references and common attribution are retained in
`DLMF.Hypergeometric.Elementary`.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology Nat ComplexConjugate

noncomputable section

namespace DLMF.Hypergeometric

/-- Identity under the stated parameter and domain assumptions: `₂F₁ (3 * a) (1 / 3 + a) (2 / 3 +
2 * a) (exp (I * Real.pi / 3)) = (Real.sqrt Real.pi : ℂ) * exp (I * Real.pi * a / 2) * (16 /
27 : ℂ) ^ ((3 * a + 1) / 6) * Gamma (5 / 6 + a) / (Gamma (2 / 3 + a) * Gamma (2 / 3))`. -/
@[dlmf 15.4.E33]
theorem value_sixth_root
    {a : ℂ}
    (hc : ∀ k : ℕ, 2 / 3 + 2 * a ≠ -(k : ℂ))
    (hconv : a.re < 1 / 6)
    (hg : ∀ k : ℕ, 5 / 6 + a ≠ -(k : ℂ)) :
    ₂F₁ (3 * a) (1 / 3 + a) (2 / 3 + 2 * a) (exp (I * Real.pi / 3)) =
      (Real.sqrt Real.pi : ℂ) * exp (I * Real.pi * a / 2) * (16 / 27 : ℂ) ^ ((3 * a + 1) / 6) * Gamma (5 / 6
        + a) / (Gamma (2 / 3 + a) * Gamma (2 / 3)) := by
  set ω : ℂ := exp (I * Real.pi / 3) with hωdef
  have hs3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hω : ω = 1 / 2 + (Real.sqrt 3 / 2 : ℝ) * I := by
    rw [hωdef, show I * (Real.pi : ℂ) / 3 = ((Real.pi / 3 : ℝ) : ℂ) * I by push_cast; ring,
      exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hωn : ‖ω‖ = 1 := by
    rw [hωdef, show I * (Real.pi : ℂ) / 3 = ((Real.pi / 3 : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  have h2ω : 2 - ω ≠ 0 := by
    intro h; have := congrArg re h; rw [hω] at this; simp at this; norm_num at this
  have hsq : (ω / (2 - ω)) ^ 2 = -1 / 3 := by
    have hs3c : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast hs3
    rw [div_pow, div_eq_iff (pow_ne_zero 2 h2ω), hω]
    push_cast
    linear_combination ((Real.sqrt 3 : ℂ) ^ 2 / 3) * I_sq - (1 / 3) * hs3c
  set A : ℂ := a / 2 with hA
  have hcA : ∀ k : ℕ, 2 * A + 5 / 6 ≠ -(k : ℂ) := by
    rw [show 2 * A + 5 / 6 = 5 / 6 + a by rw [hA]; ring]; exact hg
  have hb : ∀ k : ℕ, 2 * (1 / 3 + a) ≠ -(k : ℂ) := by
    rw [show 2 * (1 / 3 + a) = 2 / 3 + 2 * a by ring]; exact hc
  have hb' : ∀ k : ℕ, 1 / 3 + a + 1 / 2 ≠ -(k : ℂ) := by
    rw [show 1 / 3 + a + 1 / 2 = 5 / 6 + a by ring]; exact hg
  set G : ℂ → ℂ := ₂F₁ (3 * A) (3 * A + 1 / 2) (2 * A + 5 / 6) with hG
  have hre : 0 < (2 / 3 + 2 * a - 3 * a - (1 / 3 + a)).re := by
    rw [show 2 / 3 + 2 * a - 3 * a - (1 / 3 + a) = 1 / 3 - 2 * a by ring]
    simp; linarith
  have hslit : 1 - ω / 2 ∈ slitPlane := by
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [hω]; simp; norm_num
  -- radial limit and the quadratic transformation
  have hL := hypSV_tendsto_ray (a := 3 * a) (b := 1 / 3 + a) (c := 2 / 3 + 2 * a) hωn hre
  have hcontR : ContinuousAt (fun r : ℝ => (1 - (r : ℂ) * ω / 2) ^ (-(3 * a)) *
      G (((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2)) 1 := by
    have h1 : ContinuousAt (fun r : ℝ => (1 - (r : ℂ) * ω / 2) ^ (-(3 * a))) 1 := by
      apply ContinuousAt.cpow (by fun_prop) continuousAt_const
      simpa using hslit
    have hden : (2 : ℂ) - ((1 : ℝ) : ℂ) * ω ≠ 0 := by simpa using h2ω
    have h2 : ContinuousAt (fun r : ℝ => ((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2) 1 :=
      ((by fun_prop : ContinuousAt (fun r : ℝ => (r : ℂ) * ω) 1).div (by fun_prop) hden).pow 2
    have hGa : ContinuousAt G ((fun r : ℝ => ((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2) 1) := by
      simp only [ofReal_one, one_mul]
      rw [hsq]
      exact (analyticAt_ordinaryHypergeometric (show ‖(-1 / 3 : ℂ)‖ < 1 by norm_num)).continuousAt
    exact h1.mul (ContinuousAt.comp (f := fun r : ℝ => ((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2)
      hGa h2)
  have hR := hcontR.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
  simp only [ofReal_one, one_mul, hsq] at hR
  have heq : ∀ᶠ r : ℝ in 𝓝[<] 1, ₂F₁ (3 * a) (1 / 3 + a) (2 / 3 + 2 * a) ((r : ℂ) * ω) =
      (1 - (r : ℂ) * ω / 2) ^ (-(3 * a)) * G (((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hrn : ‖(r : ℂ) * ω‖ < 1 := by
      rw [norm_mul, hωn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]; exact hr.2
    rw [show (2 / 3 + 2 * a : ℂ) = 2 * (1 / 3 + a) by ring,
      quadratic_double_denominator hb hb' hrn, hG,
      show 3 * a / 2 = 3 * A by rw [hA]; ring, show (3 * a + 1) / 2 = 3 * A + 1 / 2 by rw [hA]; ring,
      show 1 / 3 + a + 1 / 2 = 2 * A + 5 / 6 by rw [hA]; ring]
  have hlim := tendsto_nhds_unique hL (hR.congr' (by
    filter_upwards [heq] with r hr
    rw [hr]))
  rw [hlim, hG, hypSV_cubic_psi_neg_one_third hcA, gauss_summation hcA (by
    rw [show 2 * A + 5 / 6 - A - (A + 1 / 2) = 1 / 3 by ring]; norm_num)]
  have hsqπ : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hs3c : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast hs3
  have hdup : Gamma (2 * A + 5 / 6 - A) * Gamma (2 * A + 5 / 6 - (A + 1 / 2)) =
      Gamma (2 / 3 + a) * (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) * (Real.sqrt Real.pi : ℂ) := by
    rw [show 2 * A + 5 / 6 - A = A + 1 / 3 + 1 / 2 by ring,
      show 2 * A + 5 / 6 - (A + 1 / 2) = A + 1 / 3 by ring, mul_comm,
      Gamma_mul_Gamma_add_half, show 2 * (A + 1 / 3) = 2 / 3 + a by rw [hA]; ring]
  have hrefl : Gamma (1 / 3) * Gamma (2 / 3) = 2 * Real.pi / Real.sqrt 3 := by
    have := Gamma_mul_Gamma_one_sub (1 / 3)
    rw [show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num, show (Real.pi : ℂ) * (1 / 3) = ((Real.pi / 3 : ℝ) : ℂ)
      by push_cast; ring, ← ofReal_sin, Real.sin_pi_div_three] at this
    rw [this]
    have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    push_cast
    field_simp
  have hG23 : Gamma (2 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ13 : Gamma (1 / 3) = 2 * Real.pi / Real.sqrt 3 / Gamma (2 / 3) := by
    rw [← hrefl]; field_simp
  -- the power `(1 - ω/2)^(-3a)` through an explicit logarithm
  set Lr : ℝ := Real.log (Real.sqrt 3 / 2) with hLr
  have hexpL : exp ((Lr : ℂ) + ((-(Real.pi / 6) : ℝ) : ℂ) * I) = 1 - ω / 2 := by
    rw [exp_add, ← ofReal_exp, hLr, Real.exp_log (by positivity), exp_mul_I, ← ofReal_cos,
      ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six, hω]
    push_cast
    linear_combination (1 / 4 : ℂ) * hs3c
  have hpowω : (1 - ω / 2) ^ (-(3 * a)) =
      exp ((Lr : ℂ) * (-(3 * a))) * exp (I * Real.pi * a / 2) := by
    rw [cpow_eq_exp_of_exp_eq hexpL (by simp; linarith [Real.pi_pos])
      (by simp; linarith [Real.pi_pos]), ← exp_add]
    congr 1; push_cast; ring
  have h2ne : (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; norm_num
  have h3ne : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hnum : (16 / 27 : ℂ) ^ ((3 * a + 1) / 6) = exp ((Lr : ℂ) * (-(3 * a))) * (4 : ℂ) ^ (-2 * A) *
      exp (Real.log 2) / ((Real.sqrt 3 : ℝ) * (2 : ℂ) ^ (1 - 2 * (A + 1 / 3))) := by
    rw [eq_div_iff (mul_ne_zero h3ne h2ne)]
    have e1 : (16 / 27 : ℂ) ^ ((3 * a + 1) / 6) = exp (Real.log (16 / 27) * ((3 * a + 1) / 6)) := by
      have := ofReal_cpow_eq_exp_log (u := 16 / 27) (by norm_num) ((3 * a + 1) / 6)
      push_cast at this; exact this
    have e2 : (4 : ℂ) ^ (-2 * A) = exp (Real.log 4 * (-2 * A)) := by
      have := ofReal_cpow_eq_exp_log (u := 4) (by norm_num) (-2 * A); push_cast at this; exact this
    have e3 : (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) = exp (Real.log 2 * (1 - 2 * (A + 1 / 3))) := by
      have := ofReal_cpow_eq_exp_log (u := 2) (by norm_num) (1 - 2 * (A + 1 / 3))
      push_cast at this; exact this
    have e4 : ((Real.sqrt 3 : ℝ) : ℂ) = exp (Real.log 3 / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num), ofReal_exp]; push_cast; ring_nf
    rw [e1, e2, e3, e4]
    rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    have l1 : Real.log (16 / 27) = 4 * Real.log 2 - 3 * Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num,
        show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow, Real.log_pow]
      push_cast; ring
    have l2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have l3 : Lr = Real.log 3 / 2 - Real.log 2 := by
      rw [hLr, Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
    rw [l1, l2, l3, hA]
    push_cast
    ring
  rw [hdup, show 2 * A + 5 / 6 - A - (A + 1 / 2) = 1 / 3 by ring,
    show 2 * A + 5 / 6 = 5 / 6 + a by rw [hA]; ring, hΓ13, hpowω, hnum,
    show exp ((Real.log 2 : ℝ) : ℂ) = 2 by rw [← ofReal_exp, Real.exp_log (by norm_num)]; push_cast; ring]
  generalize exp (I * Real.pi * a / 2) = E2
  generalize exp ((Lr : ℂ) * (-(3 * a))) = E1
  rw [← hsqπ]
  by_cases hg2 : Gamma (2 / 3 + a) = 0
  · simp [hg2]
  · field_simp

/-- Coefficient form of `z F'(a,b;c+1;z) = c (F(a,b;c;z) - F(a,b;c+1;z))`. -/
theorem hypSV_gaussHGCoeff_shift_c {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n : ℂ) * gaussHGCoeff a b (c + 1) n =
      c * (gaussHGCoeff a b c n - gaussHGCoeff a b (c + 1) n) := by
  have hc1 : ∀ k : ℕ, c + 1 ≠ -k := fun k h => hc (k + 1) (by push_cast; linear_combination h)
  have hcp := poch_ne_zero_of_not_neg_nat hc n
  have hcp1 := poch_ne_zero_of_not_neg_nat hc1 n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hpoch := poch_succ_left_mul c n
  simp only [gaussHGCoeff]
  field_simp
  linear_combination (-(poch a n * poch b n)) * hpoch

/-- `z F'(a,b;c+1;z) = c (F(a,b;c;z) - F(a,b;c+1;z))` (DLMF 15.5.4 with `n = 1`). -/
theorem hypSV_mul_deriv_shift_c {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    z * deriv (₂F₁ a b (c + 1)) z = c * (₂F₁ a b c z - ₂F₁ a b (c + 1) z) := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric a b (c + 1)
  have hL := hf.hasSum_z_mul_deriv hz'
  have hs1 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow hz'
  have hs0 := hf.hasSum_mul_pow hz'
  have hR := (hs1.sub hs0).mul_left c
  have hfun : (fun n : ℕ => (n : ℂ) * gaussHGCoeff a b (c + 1) n * z ^ n) =
      fun n => c * (gaussHGCoeff a b c n * z ^ n - gaussHGCoeff a b (c + 1) n * z ^ n) := by
    funext n
    have hcoeff := hypSV_gaussHGCoeff_shift_c (a := a) (b := b) hc n
    linear_combination hcoeff * z ^ n
  rw [hfun] at hL
  exact hL.unique (by simpa [mul_sub] using hR)

/-- Power bookkeeping for `value_sixth_root_contiguous`: the powers of `2`, `3`, `4` and
`√3/2` that occur there combine as stated. -/
private lemma value_sixth_root_contiguous_pow₁ (a A : ℂ) (hA : A = 1 / 3 + a / 2) (Lr : ℝ)
    (hLr : Lr = Real.log (Real.sqrt 3 / 2)) :
    (2 : ℂ) ^ (2 * a) * ((Real.sqrt 3 : ℝ) : ℂ) * (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) =
      exp ((Lr : ℂ) * (-(3 * a))) * (4 : ℂ) ^ (-2 * A) * exp ((Real.log 2 : ℝ) : ℂ) *
        (3 : ℂ) ^ ((3 * a + 1) / 2) := by
  have e1 : (2 : ℂ) ^ (2 * a) = exp (Real.log 2 * (2 * a)) := by
    have := ofReal_cpow_eq_exp_log (u := 2) (by norm_num) (2 * a); push_cast at this; exact this
  have e2 : (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) = exp (Real.log 2 * (1 - 2 * (A + 1 / 3))) := by
    have := ofReal_cpow_eq_exp_log (u := 2) (by norm_num) (1 - 2 * (A + 1 / 3))
    push_cast at this; exact this
  have e3 : (4 : ℂ) ^ (-2 * A) = exp (Real.log 4 * (-2 * A)) := by
    have := ofReal_cpow_eq_exp_log (u := 4) (by norm_num) (-2 * A); push_cast at this; exact this
  have e4 : (3 : ℂ) ^ ((3 * a + 1) / 2) = exp (Real.log 3 * ((3 * a + 1) / 2)) := by
    have := ofReal_cpow_eq_exp_log (u := 3) (by norm_num) ((3 * a + 1) / 2)
    push_cast at this; exact this
  have e5 : ((Real.sqrt 3 : ℝ) : ℂ) = exp (Real.log 3 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num), ofReal_exp]; push_cast; ring_nf
  rw [e1, e2, e3, e4, e5, ← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add]
  congr 1
  have l2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have l3 : Lr = Real.log 3 / 2 - Real.log 2 := by
    rw [hLr, Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
  rw [l2, l3, hA]
  push_cast
  ring

/-- Power bookkeeping for `value_sixth_root_contiguous`:
`4 · 4^{-2/3} · 2^{1 - 2(A + 1/3)} = 2^{1 - 2A}`. -/
private lemma value_sixth_root_contiguous_pow₂ (A : ℂ) :
    4 * (4 : ℂ) ^ (-(2 / 3) : ℂ) * (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) = (2 : ℂ) ^ (1 - 2 * A) := by
  have e2 : (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) = exp (Real.log 2 * (1 - 2 * (A + 1 / 3))) := by
    have := ofReal_cpow_eq_exp_log (u := 2) (by norm_num) (1 - 2 * (A + 1 / 3))
    push_cast at this; exact this
  have e2' : (2 : ℂ) ^ (1 - 2 * A) = exp (Real.log 2 * (1 - 2 * A)) := by
    have := ofReal_cpow_eq_exp_log (u := 2) (by norm_num) (1 - 2 * A)
    push_cast at this; exact this
  have e3 : (4 : ℂ) ^ (-(2 / 3) : ℂ) = exp (Real.log 4 * (-(2 / 3))) := by
    have := ofReal_cpow_eq_exp_log (u := 4) (by norm_num) (-(2 / 3)); push_cast at this; exact this
  have e4 : (4 : ℂ) = exp (Real.log 4) := by
    rw [← ofReal_exp, Real.exp_log (by norm_num)]; push_cast; ring
  rw [e2, e2', e3]
  nth_rw 1 [e4]
  rw [← exp_add, ← exp_add]
  congr 1
  have l2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [l2]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `₂F₁ (3 * a) a (2 * a) (exp (I *
Real.pi / 3)) = (Real.sqrt Real.pi : ℂ) * exp (I * Real.pi * a / 2) * (2 : ℂ) ^ (2 * a) *
Gamma (1 / 2 + a) / (3 : ℂ) ^ ((3 * a + 1) / 2) * (1 / (Gamma (1 / 3 + a) * Gamma (2 / 3)) + 1
/ (Gamma (2 / 3 + a) * Gamma (1 / 3)))`. -/
@[dlmf 15.4.E34]
theorem value_sixth_root_contiguous
    {a : ℂ}
    (hc : ∀ k : ℕ, 2 * a ≠ -(k : ℂ))
    (hconv : a.re < 0)
    (hg : ∀ k : ℕ, 1 / 2 + a ≠ -(k : ℂ)) :
    ₂F₁ (3 * a) a (2 * a) (exp (I * Real.pi / 3)) =
      (Real.sqrt Real.pi : ℂ) * exp (I * Real.pi * a / 2) * (2 : ℂ) ^ (2 * a) * Gamma (1 / 2 + a) / (3 : ℂ)
        ^ ((3 * a + 1) / 2) * (1 / (Gamma (1 / 3 + a) * Gamma (2 / 3)) + 1 / (Gamma (2 / 3 + a) * Gamma (1 /
        3))) := by
  set ω : ℂ := exp (I * Real.pi / 3) with hωdef
  have hs3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hω : ω = 1 / 2 + (Real.sqrt 3 / 2 : ℝ) * I := by
    rw [hωdef, show I * (Real.pi : ℂ) / 3 = ((Real.pi / 3 : ℝ) : ℂ) * I by push_cast; ring,
      exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hωn : ‖ω‖ = 1 := by
    rw [hωdef, show I * (Real.pi : ℂ) / 3 = ((Real.pi / 3 : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  have h2ω : 2 - ω ≠ 0 := by
    intro h; have := congrArg re h; rw [hω] at this; simp at this; norm_num at this
  have hsq : (ω / (2 - ω)) ^ 2 = -1 / 3 := by
    have hs3c : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast hs3
    rw [div_pow, div_eq_iff (pow_ne_zero 2 h2ω), hω]
    push_cast
    linear_combination ((Real.sqrt 3 : ℂ) ^ 2 / 3) * I_sq - (1 / 3) * hs3c
  have hb' : ∀ k : ℕ, a + 1 / 2 ≠ -(k : ℂ) := by
    rw [show a + 1 / 2 = 1 / 2 + a by ring]; exact hg
  set G : ℂ → ℂ := ₂F₁ (3 * a / 2) ((3 * a + 1) / 2) (a + 1 / 2) with hG
  have hre : 0 < (2 * a - 3 * a - a).re := by
    rw [show 2 * a - 3 * a - a = -(2 * a) by ring]
    simp; linarith
  have hslit : 1 - ω / 2 ∈ slitPlane := by
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [hω]; simp; norm_num
  -- radial limit and the quadratic transformation
  have hL := hypSV_tendsto_ray (a := 3 * a) (b := a) (c := 2 * a) hωn hre
  have hcontR : ContinuousAt (fun r : ℝ => (1 - (r : ℂ) * ω / 2) ^ (-(3 * a)) *
      G (((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2)) 1 := by
    have h1 : ContinuousAt (fun r : ℝ => (1 - (r : ℂ) * ω / 2) ^ (-(3 * a))) 1 := by
      apply ContinuousAt.cpow (by fun_prop) continuousAt_const
      simpa using hslit
    have hden : (2 : ℂ) - ((1 : ℝ) : ℂ) * ω ≠ 0 := by simpa using h2ω
    have h2 : ContinuousAt (fun r : ℝ => ((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2) 1 :=
      ((by fun_prop : ContinuousAt (fun r : ℝ => (r : ℂ) * ω) 1).div (by fun_prop) hden).pow 2
    have hGa : ContinuousAt G ((fun r : ℝ => ((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2) 1) := by
      simp only [ofReal_one, one_mul]
      rw [hsq]
      exact (analyticAt_ordinaryHypergeometric (show ‖(-1 / 3 : ℂ)‖ < 1 by norm_num)).continuousAt
    exact h1.mul (ContinuousAt.comp (f := fun r : ℝ => ((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2)
      hGa h2)
  have hR := hcontR.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
  simp only [ofReal_one, one_mul, hsq] at hR
  have heq : ∀ᶠ r : ℝ in 𝓝[<] 1, ₂F₁ (3 * a) a (2 * a) ((r : ℂ) * ω) =
      (1 - (r : ℂ) * ω / 2) ^ (-(3 * a)) * G (((r : ℂ) * ω / (2 - (r : ℂ) * ω)) ^ 2) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hrn : ‖(r : ℂ) * ω‖ < 1 := by
      rw [norm_mul, hωn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]; exact hr.2
    rw [quadratic_double_denominator hc hb' hrn, hG]
  have hlim := tendsto_nhds_unique hL (hR.congr' (by
    filter_upwards [heq] with r hr
    rw [hr]))
  rw [hlim, hG]
  -- Euler's transformation at `-1/3`
  have hE : ₂F₁ (3 * a / 2) ((3 * a + 1) / 2) (a + 1 / 2) (-1 / 3) =
      (4 / 3 : ℂ) ^ (-(2 * a)) * ₂F₁ (-a / 2) (-a / 2 + 1 / 2) (a + 1 / 2) (-1 / 3) := by
    rw [euler_transformation_of_ne_neg_nat hb' (by norm_num),
      show a + 1 / 2 - 3 * a / 2 - (3 * a + 1) / 2 = -(2 * a) by ring,
      show (1 : ℂ) - -1 / 3 = 4 / 3 by norm_num,
      show a + 1 / 2 - 3 * a / 2 = -a / 2 + 1 / 2 by ring,
      show a + 1 / 2 - (3 * a + 1) / 2 = -a / 2 by ring, ordinaryHypergeometric_symm]
  rw [hE]
  -- lowering `c` by one through the derivative
  have hcK : ∀ k : ℕ, a + 1 / 2 + 1 ≠ -(k : ℂ) := fun k h =>
    hb' (k + 1) (by push_cast; linear_combination h)
  set K : ℂ → ℂ := ₂F₁ (-a / 2) (-a / 2 + 1 / 2) (a + 1 / 2 + 1) with hK
  have hc0 : a + 1 / 2 ≠ 0 := by simpa using hb' 0
  have hSK : ₂F₁ (-a / 2) (-a / 2 + 1 / 2) (a + 1 / 2) (-1 / 3) =
      K (-1 / 3) + (-1 / 3) * deriv K (-1 / 3) / (a + 1 / 2) := by
    have h := hypSV_mul_deriv_shift_c (a := -a / 2) (b := -a / 2 + 1 / 2) hb'
      (show ‖(-1 / 3 : ℂ)‖ < 1 by norm_num)
    rw [hK, h, mul_div_cancel_left₀ _ hc0]
    ring
  rw [hSK]
  -- `K` through the `ψ`-cubic family
  set A : ℂ := 1 / 3 + a / 2 with hA
  have hcA : ∀ k : ℕ, 2 * A + 5 / 6 ≠ -(k : ℂ) := by
    rw [show 2 * A + 5 / 6 = a + 1 / 2 + 1 by rw [hA]; ring]; exact hcK
  set FG : ℂ → ℂ := ₂F₁ (3 * A) (3 * A + 1 / 2) (2 * A + 5 / 6) with hFG
  have hKev : K =ᶠ[𝓝 (-1 / 3)] fun z => (1 + (-1) * z) ^ (2 * a + 1) * FG z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (-1 / 3 : ℂ) ∈ Metric.ball (0 : ℂ) 1 by
      simp; norm_num)] with z hz
    have hz1 : ‖z‖ < 1 := by simpa using hz
    rw [hK, euler_transformation_of_ne_neg_nat hcK hz1, hFG,
      show a + 1 / 2 + 1 - -a / 2 - (-a / 2 + 1 / 2) = 2 * a + 1 by ring,
      show a + 1 / 2 + 1 - -a / 2 = 3 * A + 1 / 2 by rw [hA]; ring,
      show a + 1 / 2 + 1 - (-a / 2 + 1 / 2) = 3 * A by rw [hA]; ring,
      show a + 1 / 2 + 1 = 2 * A + 5 / 6 by rw [hA]; ring, ordinaryHypergeometric_symm,
      show (1 : ℂ) - z = 1 + (-1) * z by ring]
  have h43 : (1 : ℂ) + (-1) * (-1 / 3) = 4 / 3 := by norm_num
  have hK0 : K (-1 / 3) = (4 / 3 : ℂ) ^ (2 * a + 1) * FG (-1 / 3) := by
    rw [hKev.eq_of_nhds, h43]
  have hFGa : AnalyticAt ℂ FG (-1 / 3 : ℂ) := analyticAt_ordinaryHypergeometric (by norm_num)
  have hK1 : deriv K (-1 / 3) = (2 * a + 1) * (4 / 3 : ℂ) ^ (2 * a) * (-1) * FG (-1 / 3) +
      (4 / 3 : ℂ) ^ (2 * a + 1) * deriv FG (-1 / 3) := by
    rw [hKev.deriv_eq]
    have h := ((((hasDerivAt_id (-1 / 3 : ℂ)).const_mul (-1 : ℂ)).const_add (1 : ℂ)).cpow_const
      (c := 2 * a + 1) (by
        rw [show (1 : ℂ) + (-1) * id (-1 / 3) = 4 / 3 by norm_num]
        exact mem_slitPlane_iff.mpr (Or.inl (by norm_num)))).mul hFGa.differentiableAt.hasDerivAt
    refine Eq.trans h.deriv ?_
    simp only [id, h43]
    rw [show 2 * a + 1 - 1 = 2 * a by ring]
    ring
  rw [hK0, hK1, hFG, hypSV_cubic_psi_neg_one_third hcA, hypSV_cubic_psi_deriv_neg_one_third hcA,
    gauss_summation hcA (by rw [show 2 * A + 5 / 6 - A - (A + 1 / 2) = 1 / 3 by ring]; norm_num)]
  have hsqπ : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hs3c : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast hs3
  set Lr : ℝ := Real.log (Real.sqrt 3 / 2) with hLr
  have hexpL : exp ((Lr : ℂ) + ((-(Real.pi / 6) : ℝ) : ℂ) * I) = 1 - ω / 2 := by
    rw [exp_add, ← ofReal_exp, hLr, Real.exp_log (by positivity), exp_mul_I, ← ofReal_cos,
      ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six, hω]
    push_cast
    linear_combination (1 / 4 : ℂ) * hs3c
  have hpowω : (1 - ω / 2) ^ (-(3 * a)) =
      exp ((Lr : ℂ) * (-(3 * a))) * exp (I * Real.pi * a / 2) := by
    rw [cpow_eq_exp_of_exp_eq hexpL (by simp; linarith [Real.pi_pos])
      (by simp; linarith [Real.pi_pos]), ← exp_add]
    congr 1; push_cast; ring
  have hsin : sin ((Real.pi : ℂ) * (1 / 3)) = ((Real.sqrt 3 : ℝ) : ℂ) / 2 := by
    rw [show (Real.pi : ℂ) * (1 / 3) = ((Real.pi / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
      Real.sin_pi_div_three]; push_cast; ring
  have hrefl : Gamma (1 / 3) * Gamma (2 / 3) = Real.pi / sin (Real.pi * (1 / 3)) := by
    have := Gamma_mul_Gamma_one_sub (1 / 3)
    rwa [show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num] at this
  have hG13 : Gamma (1 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hG23 : Gamma (2 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ43 : Gamma (4 / 3 : ℂ) = Gamma (1 / 3) / 3 := by
    rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Gamma_add_one _ (by norm_num)]; ring
  have hΓc : Gamma (2 * A + 5 / 6) = (a + 1 / 2) * Gamma (1 / 2 + a) := by
    rw [show 2 * A + 5 / 6 = (1 / 2 + a) + 1 by rw [hA]; ring, Gamma_add_one _ (by
      rw [show 1 / 2 + a = a + 1 / 2 by ring]; exact hc0)]; ring
  have hdup1 : Gamma (2 * A + 5 / 6 - A) * Gamma (2 * A + 5 / 6 - (A + 1 / 2)) =
      Gamma (a + 4 / 3) * (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) * (Real.sqrt Real.pi : ℂ) := by
    rw [show 2 * A + 5 / 6 - A = A + 1 / 3 + 1 / 2 by ring,
      show 2 * A + 5 / 6 - (A + 1 / 2) = A + 1 / 3 by ring, mul_comm,
      Gamma_mul_Gamma_add_half, show 2 * (A + 1 / 3) = a + 4 / 3 by rw [hA]; ring]
  have hdup1' : Gamma (A + 5 / 6) * Gamma (A + 1 / 3) =
      Gamma (a + 4 / 3) * (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) * (Real.sqrt Real.pi : ℂ) := by
    rw [← hdup1]; ring_nf
  have hdup2 : Gamma A * Gamma (A + 1 / 2) =
      Gamma (2 / 3 + a) * (2 : ℂ) ^ (1 - 2 * A) * (Real.sqrt Real.pi : ℂ) := by
    rw [Gamma_mul_Gamma_add_half, show 2 * A = 2 / 3 + a by rw [hA]; ring]
  have hinv : (Gamma (1 / 3 + a))⁻¹ = (a + 1 / 3) * (Gamma (a + 4 / 3))⁻¹ := by
    by_cases h0 : 1 / 3 + a = 0
    · rw [h0, Gamma_zero, inv_zero, show a + 1 / 3 = 0 by linear_combination h0, zero_mul]
    · rw [show a + 4 / 3 = (1 / 3 + a) + 1 by ring, Gamma_add_one _ h0, mul_inv,
        show a + 1 / 3 = 1 / 3 + a by ring, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
  have hN1 : (2 : ℂ) ^ (2 * a) * ((Real.sqrt 3 : ℝ) : ℂ) * (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) =
      exp ((Lr : ℂ) * (-(3 * a))) * (4 : ℂ) ^ (-2 * A) * exp ((Real.log 2 : ℝ) : ℂ) *
        (3 : ℂ) ^ ((3 * a + 1) / 2) :=
    value_sixth_root_contiguous_pow₁ a A hA Lr hLr
  have hN2 : 4 * (4 : ℂ) ^ (-(2 / 3) : ℂ) * (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) = (2 : ℂ) ^ (1 - 2 * A) :=
    value_sixth_root_contiguous_pow₂ A
  have hPne : (4 / 3 : ℂ) ^ (2 * a) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; norm_num
  have hT1ne : (2 : ℂ) ^ (1 - 2 * (A + 1 / 3)) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; norm_num
  have hR3ne : (3 : ℂ) ^ ((3 * a + 1) / 2) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; norm_num
  have h3ne : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hB : (2 : ℂ) ^ (2 * a) = exp ((Lr : ℂ) * (-(3 * a))) * (4 : ℂ) ^ (-2 * A) *
      exp ((Real.log 2 : ℝ) : ℂ) * (3 : ℂ) ^ ((3 * a + 1) / 2) /
      (((Real.sqrt 3 : ℝ) : ℂ) * (2 : ℂ) ^ (1 - 2 * (A + 1 / 3))) := by
    rw [eq_div_iff (mul_ne_zero h3ne hT1ne), ← hN1]; ring
  have hΓ13' : Gamma (1 / 3) = Real.pi / (((Real.sqrt 3 : ℝ) : ℂ) / 2) / Gamma (2 / 3) := by
    rw [← hsin, ← hrefl]; field_simp
  rw [show (1 : ℂ) / (Gamma (1 / 3 + a) * Gamma (2 / 3)) = (Gamma (1 / 3 + a))⁻¹ * (Gamma (2 / 3))⁻¹ by
      rw [one_div, mul_inv],
    show (1 : ℂ) / (Gamma (2 / 3 + a) * Gamma (1 / 3)) = (Gamma (2 / 3 + a))⁻¹ * (Gamma (1 / 3))⁻¹ by
      rw [one_div, mul_inv], hinv]
  rw [show (4 / 3 : ℂ) ^ (2 * a + 1) = (4 / 3) ^ (2 * a) * (4 / 3) by
      rw [cpow_add _ _ (by norm_num), cpow_one], hpowω,
    show (4 / 3 : ℂ) ^ (-(2 * a)) = ((4 / 3 : ℂ) ^ (2 * a))⁻¹ from cpow_neg _ _,
    show 2 * A + 5 / 6 - A - (A + 1 / 2) = 1 / 3 by ring, hdup1, hdup1', hdup2, hΓc, hΓ43, hsin,
    hB, ← hN2, hΓ13']
  generalize exp (I * Real.pi * a / 2) = E
  generalize exp ((Lr : ℂ) * (-(3 * a))) = Ex
  rw [show exp ((Real.log 2 : ℝ) : ℂ) = 2 by rw [← ofReal_exp, Real.exp_log (by norm_num)]; push_cast; ring,
    ← hsqπ]
  rw [hA]
  have h12 : (1 + a * 2 : ℂ) ≠ 0 := by
    intro h; apply hc0; linear_combination h / 2
  generalize hg1 : (Gamma (a + 4 / 3))⁻¹ = g1
  generalize hg2 : (Gamma (2 / 3 + a))⁻¹ = g2
  generalize hgh : Gamma (1 / 2 + a) = gh
  simp only [div_eq_mul_inv, mul_inv]
  field_simp
  ring_nf
  rw [show (4 / 3 : ℂ) + a = a + 4 / 3 by ring, hg1]
  subst hg2
  field_simp
  ring_nf

/-- The paired terms of the alternating series `∑ (-1)^k a/(a+k)`. -/
def altPair (a : ℂ) (j : ℕ) : ℂ := a / (a + 2 * j) - a / (a + 2 * j + 1)

/-- The paired term `a/(a + 2j) - a/(a + 2j + 1)` equals `a/((a + 2j)(a + 2j + 1))`. -/
theorem altPair_eq (a : ℂ) (j : ℕ) (h1 : a + 2 * j ≠ 0) (h2 : a + 2 * j + 1 ≠ 0) :
    altPair a j = a / ((a + 2 * j) * (a + 2 * j + 1)) := by
  unfold altPair; field_simp; ring

/-- Complex digamma at a positive real is the real digamma. -/
theorem digamma_ofReal_eq {x : ℝ} (hx : 0 < x) : Complex.digamma x = (Real.digamma x : ℂ) := by
  apply Complex.ext
  · simp [Real.digamma_eq_re_digamma hx]
  · have h := DLMF.Gamma.digamma_conj (x : ℂ)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    simp at this
    simp; linarith

/-- The real case: `∑ⱼ (x/(x+2j) - x/(x+2j+1)) = (x/2)(ψ((x+1)/2) - ψ(x/2))`. -/
theorem hasSum_altPair_ofReal {x : ℝ} (hx : 0 < x) :
    HasSum (altPair x) ((x / 2 : ℂ) * (Complex.digamma ((x + 1) / 2) - Complex.digamma (x / 2))) := by
  have h1 := Real.tendsto_deriv_log_GammaSeq (x := (x + 1) / 2) (by positivity)
  have h2 := Real.tendsto_deriv_log_GammaSeq (x := x / 2) (by positivity)
  have hd := (h1.sub h2).const_mul (x / 2)
  have hpartial : ∀ n : ℕ, x / 2 * ((Real.log n - ∑ k ∈ Finset.range (n + 1), ((x + 1) / 2 + k)⁻¹) -
      (Real.log n - ∑ k ∈ Finset.range (n + 1), (x / 2 + k)⁻¹)) =
      ∑ k ∈ Finset.range (n + 1), (x / (x + 2 * k) - x / (x + 2 * k + 1)) := by
    intro n
    rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    field_simp
    ring
  simp_rw [hpartial] at hd
  have hreal : HasSum (fun j : ℕ => x / (x + 2 * j) - x / (x + 2 * j + 1))
      (x / 2 * (Real.digamma ((x + 1) / 2) - Real.digamma (x / 2))) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · exact (hd.comp (tendsto_sub_atTop_nat 1)).congr' (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simp only [Function.comp_apply, Nat.sub_add_cancel hn])
    · intro j
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      rw [sub_nonneg]
      exact div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)
  have hc := (Complex.ofRealCLM.hasSum hreal)
  simp only [ofRealCLM_apply] at hc
  convert hc using 1
  · funext j; simp [altPair]
  · rw [show ((x : ℂ) + 1) / 2 = (((x + 1) / 2 : ℝ) : ℂ) by push_cast; ring,
      show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      digamma_ofReal_eq (by positivity), digamma_ofReal_eq (by positivity)]
    push_cast; ring

/-- `ψ` is analytic away from the nonpositive integers. -/
theorem analyticAt_digamma_of_not_neg_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.digamma s := by
  have hG : AnalyticAt ℂ Complex.Gamma s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_not_neg_nat.mem_nhds hs] with w hw
    exact Complex.differentiableAt_Gamma w hw
  rw [show Complex.digamma = fun s => deriv Complex.Gamma s / Complex.Gamma s from
    funext fun s => by rw [Complex.digamma_def, logDeriv_apply]]
  exact hG.deriv.div hG (Complex.Gamma_ne_zero hs)

/-- The paired alternating series for `Re a > 0`. -/
theorem hasSum_altPair {a : ℂ} (ha : 0 < a.re) :
    HasSum (altPair a) (a / 2 * (Complex.digamma ((a + 1) / 2) - Complex.digamma (a / 2))) := by
  set U : Set ℂ := {a : ℂ | 0 < a.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hden : ∀ b : ℂ, 0 < b.re → ∀ j : ℕ, b + 2 * j ≠ 0 ∧ b + 2 * j + 1 ≠ 0 := by
    intro b hb j
    constructor <;> intro h <;> have := congrArg re h <;> simp at this <;>
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- local domination of the paired series
  have hdom : ∀ a₀ ∈ U, ∃ V : Set ℂ, IsOpen V ∧ a₀ ∈ V ∧ V ⊆ U ∧ ∃ u : ℕ → ℝ, Summable u ∧
      ∀ j, ∀ b ∈ V, ‖altPair b j‖ ≤ u j := by
    intro a₀ ha₀
    set δ := a₀.re / 2 with hδ
    have hδ0 : 0 < δ := by simp only [hδ]; have : 0 < a₀.re := ha₀; linarith
    set m := min δ 1 with hm
    have hm0 : 0 < m := lt_min hδ0 one_pos
    set R := ‖a₀‖ + δ with hR
    refine ⟨Metric.ball a₀ δ, Metric.isOpen_ball, Metric.mem_ball_self hδ0, ?_, ?_⟩
    · intro b hb
      have := (abs_re_le_norm (b - a₀)).trans_lt (by simpa [dist_eq_norm] using hb)
      rw [abs_lt] at this
      simp only [sub_re] at this
      show 0 < b.re
      have : 0 < a₀.re := ha₀
      linarith
    refine ⟨fun j => R / (m ^ 2 * ((j : ℝ) + 1) ^ 2), ?_, ?_⟩
    · have h2 := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
      refine (h2.mul_left (R / m ^ 2)).congr fun j => ?_
      push_cast
      field_simp
    · intro j b hb
      have hbd : ‖b - a₀‖ < δ := by simpa [dist_eq_norm] using hb
      have hre : δ < b.re := by
        have hlt := (abs_re_le_norm (b - a₀)).trans_lt hbd
        rw [abs_lt, sub_re] at hlt
        have h2 : a₀.re = 2 * δ := by simp only [hδ]; ring
        linarith [hlt.1]
      have hbR : ‖b‖ ≤ R := by
        have h3 : ‖b‖ ≤ ‖a₀‖ + ‖b - a₀‖ := by
          have := norm_add_le a₀ (b - a₀); rwa [add_sub_cancel] at this
        simp only [hR]; linarith
      obtain ⟨h1, h2⟩ := hden b (by linarith) j
      rw [altPair_eq b j h1 h2, norm_div, norm_mul]
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hmδ : m ≤ δ := min_le_left _ _
      have hm1 : m ≤ 1 := min_le_right _ _
      have hA : m * ((j : ℝ) + 1) ≤ ‖b + 2 * j‖ := by
        refine le_trans ?_ (re_le_norm _)
        simp; nlinarith
      have hB : m * ((j : ℝ) + 1) ≤ ‖b + 2 * j + 1‖ := by
        refine le_trans ?_ (re_le_norm _)
        simp; nlinarith
      have hpos : 0 < m * ((j : ℝ) + 1) := by positivity
      rw [div_le_div_iff₀ (mul_pos (hpos.trans_le hA) (hpos.trans_le hB)) (by positivity)]
      calc ‖b‖ * (m ^ 2 * ((j : ℝ) + 1) ^ 2) = ‖b‖ * ((m * ((j : ℝ) + 1)) * (m * ((j : ℝ) + 1))) := by
            ring
        _ ≤ R * (‖b + 2 * j‖ * ‖b + 2 * j + 1‖) := by
            gcongr
  have hsum : ∀ b ∈ U, Summable (altPair b) := by
    intro b hb
    obtain ⟨V, -, hbV, -, u, hu, hle⟩ := hdom b hb
    exact Summable.of_norm_bounded hu fun j => hle j b hbV
  have hPan : AnalyticOnNhd ℂ (fun b => ∑' j, altPair b j) U := by
    intro a₀ ha₀
    obtain ⟨V, hVo, ha₀V, hVU, u, hu, hle⟩ := hdom a₀ ha₀
    have hdiff : DifferentiableOn ℂ (fun b => ∑' j, altPair b j) V := by
      refine differentiableOn_tsum_of_summable_norm hu (fun j => ?_) hVo hle
      intro b hb
      obtain ⟨h1, h2⟩ := hden b (hVU hb) j
      have hd : DifferentiableAt ℂ (fun b : ℂ => b / (b + 2 * j) - b / (b + 2 * j + 1)) b := by
        fun_prop (disch := assumption)
      exact hd.differentiableWithinAt
    exact hdiff.analyticAt (hVo.mem_nhds ha₀V)
  have hfan : AnalyticOnNhd ℂ (fun b => b / 2 * (Complex.digamma ((b + 1) / 2) -
      Complex.digamma (b / 2))) U := by
    intro b hb
    have hb' : 0 < b.re := hb
    have h1 : 0 < ((b + 1) / 2).re := by simp; linarith
    have h2 : 0 < (b / 2).re := by simp; linarith
    have hA1 : AnalyticAt ℂ (fun b : ℂ => (b + 1) / 2) b := by fun_prop
    have hA2 : AnalyticAt ℂ (fun b : ℂ => b / 2) b := by fun_prop
    have hD1 := (analyticAt_digamma_of_not_neg_nat (not_neg_nat_of_re_pos h1)).comp
      (f := fun b : ℂ => (b + 1) / 2) hA1
    have hD2 := (analyticAt_digamma_of_not_neg_nat (not_neg_nat_of_re_pos h2)).comp
      (f := fun b : ℂ => b / 2) hA2
    exact hA2.mul (hD1.sub hD2)
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ b in 𝓝[≠] (1 : ℂ), (∑' j, altPair b j) =
      b / 2 * (Complex.digamma ((b + 1) / 2) - Complex.digamma (b / 2)) := by
    have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      have hr0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
        refine h.congr fun n => ?_
        simp only [Function.comp_apply]; push_cast; ring
      have hr1 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
        simpa using hr0.const_add 1
      have hc : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
        have := (continuous_ofReal.tendsto (1 : ℝ)).comp hr1
        simpa [Function.comp_def] using this
      refine tendsto_nhdsWithin_iff.mpr ⟨hc, Eventually.of_forall fun n => ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      intro h
      have : (1 + 1 / ((n : ℝ) + 2) : ℝ) = 1 := by exact_mod_cast h
      linarith
    refine hseq.frequently (Frequently.of_forall fun n => ?_)
    have hx : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 2) := by positivity
    have h := hasSum_altPair_ofReal hx
    rw [h.tsum_eq]
  have heq := hPan.eqOn_of_preconnected_of_frequently_eq hfan hUc h1U hfreq (show a ∈ U from ha)
  have := (hsum a ha).hasSum
  simp only at heq
  rwa [heq] at this

/-- The coefficients of `₂F₁(1, a; a + 1; z)` are `a/(a + k)`. -/
theorem gaussHGCoeff_one_self_add_one {a : ℂ} (ha : 0 < a.re) (k : ℕ) :
    gaussHGCoeff 1 a (a + 1) k = a / (a + k) := by
  have hp : poch (a + 1) k ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) k
  have hak : a + k ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have e1 := poch_succ a k
  have e2 := poch_succ_left a k
  rw [gaussHGCoeff, poch_nat_one, div_eq_div_iff (mul_ne_zero hp hf) hak]
  linear_combination (k.factorial : ℂ) * (e1.symm.trans e2)

/-- Ordered partial sums are essential here: the series is only conditionally convergent. -/
@[dlmf 15.4.E27]
theorem alternating_digamma {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      gaussHGCoeff 1 a (a + 1) k * (-1 : ℂ) ^ k) atTop
      (𝓝 (a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)))) := by
  set t : ℕ → ℂ := fun k => gaussHGCoeff 1 a (a + 1) k * (-1 : ℂ) ^ k with ht
  have htk : ∀ k : ℕ, t k = (-1) ^ k * (a / (a + k)) := fun k => by
    simp only [ht]; rw [gaussHGCoeff_one_self_add_one ha]; ring
  have h2N : ∀ N : ℕ, ∑ k ∈ Finset.range (2 * N), t k = ∑ j ∈ Finset.range N, altPair a j := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ, htk, htk, altPair, pow_succ, pow_mul]
      push_cast
      ring
  have hdecomp : ∀ n : ℕ, ∑ k ∈ Finset.range n, t k = ∑ j ∈ Finset.range (n / 2), altPair a j +
      (if n % 2 = 1 then a / (a + (2 * (n / 2) : ℕ)) else 0) := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have : n = 2 * (n / 2) := by omega
      rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega)), add_zero]
      conv_lhs => rw [this]
      exact h2N _
    · have : n = 2 * (n / 2) + 1 := by omega
      rw [ite_eq_left_iff.mpr (fun h' => absurd h h')]
      conv_lhs => rw [this]
      rw [Finset.sum_range_succ, h2N, htk, pow_mul]
      simp
  simp_rw [hdecomp]
  rw [show a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) =
    a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) + 0 by ring]
  refine Tendsto.add ((hasSum_altPair ha).tendsto_sum_nat.comp (Nat.tendsto_div_const_atTop
    (by norm_num))) ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hb : Tendsto (fun n : ℕ => ‖a‖ / (2 * ((n / 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 * ((n / 2 : ℕ) : ℝ))) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp (Nat.tendsto_div_const_atTop (by norm_num))).const_mul_atTop
        (by norm_num)
    have := h1.inv_tendsto_atTop.const_mul ‖a‖
    rw [mul_zero] at this
    exact this.congr fun n => by rw [div_eq_mul_inv]; rfl
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hm : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by
    have : 1 ≤ n / 2 := by omega
    exact_mod_cast this
  split_ifs
  · rw [norm_div]
    have hre : 2 * ((n / 2 : ℕ) : ℝ) ≤ ‖a + ((2 * (n / 2) : ℕ) : ℂ)‖ := by
      refine le_trans ?_ (re_le_norm _)
      simp; linarith
    gcongr
  · simp; positivity

/-- Identity under the stated parameter and domain assumptions: `(2 : ℂ) ^ (-a) * ₂F₁ a a (a + 1)
(1 / 2) = a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2))`. -/
@[dlmf 15.4.E27]
theorem half_argument_digamma {a : ℂ} (ha : 0 < a.re) :
    (2 : ℂ) ^ (-a) * ₂F₁ a a (a + 1) (1 / 2) =
      a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) := by
  set L := a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) with hL
  have hc : ∀ k : ℕ, a + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  -- Abel's theorem for `∑ (-1)^k a/(a+k) x^k`
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt (alternating_digamma ha)
  rw [tendsto_map'_iff] at habel
  -- the same function through Pfaff's transformation
  have hF : ∀ x : ℝ, 0 < x → x < 1 →
      ((fun z : ℂ => ∑' n, gaussHGCoeff 1 a (a + 1) n * (-1 : ℂ) ^ n * z ^ n) ∘ ofReal) x =
        (1 + (x : ℂ)) ^ (-a) * ₂F₁ a a (a + 1) ((x : ℂ) / (1 + x)) := by
    intro x hx0 hx1
    have hxn : ‖-(x : ℂ)‖ < 1 := by
      rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
    have hq : -(x : ℂ) / (-(x : ℂ) - 1) = (x : ℂ) / (1 + x) := by
      have h1 : (1 : ℂ) + x ≠ 0 := by exact_mod_cast (show (1 + x : ℝ) ≠ 0 by linarith)
      have h2 : -(x : ℂ) - 1 ≠ 0 := by
        rw [show -(x : ℂ) - 1 = -(1 + x) by ring]; exact neg_ne_zero.mpr h1
      rw [div_eq_div_iff h2 h1]; ring
    have hqn : ‖-(x : ℂ) / (-(x : ℂ) - 1)‖ < 1 := by
      rw [hq, show (x : ℂ) / (1 + x) = ((x / (1 + x) : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one (by linarith)]
      linarith
    have hP := pfaff_transformation_of_ne_neg_nat (a := a) (b := 1) (c := a + 1) hc hxn hqn
    rw [ordinaryHypergeometric_symm, hq, show a + 1 - 1 = a by ring, sub_neg_eq_add] at hP
    simp only [Function.comp_apply]
    rw [← hP, ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul]
    refine tsum_congr fun n => ?_
    simp [gaussHGCoeff, poch, div_eq_mul_inv]
    ring
  have hlim : Tendsto (fun x : ℝ => (1 + (x : ℂ)) ^ (-a) * ₂F₁ a a (a + 1) ((x : ℂ) / (1 + x)))
      (𝓝[<] 1) (𝓝 ((2 : ℂ) ^ (-a) * ₂F₁ a a (a + 1) (1 / 2))) := by
    have h1 : Tendsto (fun x : ℝ => (1 + (x : ℂ))) (𝓝[<] 1) (𝓝 2) := by
      have : Tendsto (fun x : ℝ => (1 + (x : ℂ))) (𝓝 1) (𝓝 (1 + ((1 : ℝ) : ℂ))) :=
        (continuous_const.add continuous_ofReal).tendsto 1
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun x : ℝ => (x : ℂ) / (1 + x)) (𝓝[<] 1) (𝓝 (1 / 2)) := by
      have : Tendsto (fun x : ℝ => (x : ℂ) / (1 + x)) (𝓝 1) (𝓝 (((1 : ℝ) : ℂ) / (1 + ((1 : ℝ) : ℂ)))) :=
        (continuous_ofReal.tendsto 1).div ((continuous_const.add continuous_ofReal).tendsto 1)
          (by norm_num)
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    have hcp : ContinuousAt (fun w : ℂ => w ^ (-a)) 2 :=
      continuousAt_cpow_const (by simp)
    have hFc : ContinuousAt (₂F₁ a a (a + 1) : ℂ → ℂ) (1 / 2) :=
      (analyticAt_ordinaryHypergeometric (by norm_num)).continuousAt
    exact (hcp.tendsto.comp h1).mul (hFc.tendsto.comp h2)
  have hev : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have habel' : Tendsto (fun x : ℝ => (1 + (x : ℂ)) ^ (-a) * ₂F₁ a a (a + 1) ((x : ℂ) / (1 + x)))
      (𝓝[<] 1) (𝓝 L) := by
    refine habel.congr' ?_
    filter_upwards [hev] with x hx
    exact hF x hx.1 hx.2
  exact tendsto_nhds_unique hlim habel'

end DLMF.Hypergeometric

end
end
