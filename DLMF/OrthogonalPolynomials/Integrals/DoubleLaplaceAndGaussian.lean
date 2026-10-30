/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals.BesselAndLaguerreTransforms

/-!
# Double Laplace integrals and Gaussian polynomial identities

Angular Jacobi sums evaluate double Laplace integrals, followed by the associated Gaussian
polynomial convolution formulas.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Integrals`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

open DLMF.Bessel

open DLMF.Gamma (Gamma_add_nat_eq_poch_mul_Gamma)

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

section DoubleLaplaceIntegrals

open Set

set_option maxHeartbeats 1000000

/-- Homogenized symmetric Jacobi coefficients from the binomial formula. -/
def angularJacobiSum (β : ℂ) (n : ℕ) (x y : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (β + n - k + 1) k / k ! *
    (poch (β + k + 1) (n - k) / (n - k) !) * (-y ^ 2) ^ (n - k) * (x ^ 2) ^ k

/-- A normalized Gegenbauer polynomial is the corresponding normalized symmetric Jacobi polynomial. -/
theorem gegenbauer_normalized_jacobi {β : ℝ} (hβ : -1 / 2 < β) (n : ℕ) (z : ℂ) :
    ultrasphPoly (β + 1 / 2) n z / ultrasphPoly (β + 1 / 2) n 1 =
      jacobiPolyP β β n z / jacobiPolyP β β n 1 := by
  have hb : -1 < (β : ℂ).re := by simp; linarith
  have hp : poch ((β : ℂ) + 1) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n
  have hq : poch (2 * ((β : ℂ) + 1 / 2)) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n
  rw [ultrasphPoly_eq_jacobiPolyP n z (by convert hp using 1 ; congr 1 ; ring),
    ultrasphPoly_eq_jacobiPolyP n 1 (by convert hp using 1 ; congr 1 ; ring)]
  simp only [show (β : ℂ) + 1 / 2 - 1 / 2 = β by ring]
  have hp' : poch ((β : ℂ) + 1 / 2 + 1 / 2) n ≠ 0 := by convert hp using 1 ; congr 1 ; ring
  exact mul_div_mul_left _ _ (div_ne_zero hq hp')

/-- Homogenization of the finite Jacobi binomial sum. -/
theorem angularJacobiSum_eq {β : ℝ} (hβ : -1 / 2 < β) (n : ℕ) {x y : ℝ}
    (hs : 0 < x ^ 2 + y ^ 2) :
    (x ^ 2 + y ^ 2 : ℂ) ^ n * jacobiPolyP β β n ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) : ℂ) =
      angularJacobiSum β n x y := by
  have hs0 : (x ^ 2 + y ^ 2 : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [jacobi_binomial_sum (by simp; linarith), angularJacobiSum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have h1 : (x ^ 2 - y ^ 2 : ℂ) / (x ^ 2 + y ^ 2) - 1 = 2 * (-((y : ℂ) ^ 2)) / (x ^ 2 + y ^ 2) := by
    field_simp; ring
  have h2 : (x ^ 2 - y ^ 2 : ℂ) / (x ^ 2 + y ^ 2) + 1 = 2 * (x : ℂ) ^ 2 / (x ^ 2 + y ^ 2) := by
    field_simp; ring
  rw [h1, h2, div_pow, div_pow, mul_pow, mul_pow]
  have hpow : (2 : ℂ) ^ (n - k) * 2 ^ k = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hk']
  have hspow : (x ^ 2 + y ^ 2 : ℂ) ^ (n - k) * (x ^ 2 + y ^ 2) ^ k = (x ^ 2 + y ^ 2 : ℂ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))]
  linear_combination (poch ((β : ℂ) + n - k + 1) k * poch ((β : ℂ) + k + 1) (n - k) *
    (-((y : ℂ) ^ 2)) ^ (n - k) * ((x : ℂ) ^ 2) ^ k) *
    ((x ^ 2 + y ^ 2 : ℂ) ^ n * hpow - (2 : ℂ) ^ n * hspow)

/-- The angular weight is integrable, including the allowed singular endpoint exponents. -/
theorem angular_weight_integrable {β : ℝ} (hβ : -1 / 2 < β) :
    IntervalIntegrable (fun phi : ℝ => (Real.sin phi : ℂ) ^ (2 * β : ℂ)) volume 0 Real.pi := by
  have h := (integral_sin_rpow_aux (lam := β + 1 / 2) (by linarith)).1
  have hc : IntervalIntegrable (fun phi : ℝ => ((Real.sin phi ^ (2 * β) : ℝ) : ℂ)) volume 0 Real.pi := by
    have hh : IntervalIntegrable (fun phi : ℝ => Real.sin phi ^ (2 * β)) volume 0 Real.pi := by
      convert h using 1  ; ring
    exact ⟨hh.1.ofReal, hh.2.ofReal⟩
  apply hc.congr_uIoo
  intro phi hphi
  dsimp only
  rw [Set.uIoo_of_lt Real.pi_pos] at hphi
  rw [show (2 * (β : ℂ)) = ((2 * β : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_cpow (Real.sin_pos_of_pos_of_lt_pi hphi.1 hphi.2).le]

/-- Homogeneous angular Laplace integral, reduced to a finite symmetric Jacobi sum. -/
theorem angular_homogeneous {β : ℝ} (hβ : -1 / 2 < β) (n : ℕ) {x y : ℝ}
    (hs : 0 < x ^ 2 + y ^ 2) :
    (∫ phi : ℝ in (0 : ℝ)..Real.pi,
      ((x : ℂ) ^ 2 - y ^ 2 + 2 * I * x * y * Real.cos phi) ^ n *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) =
      (Real.sqrt Real.pi * Gamma (β + 1 / 2 : ℂ) * n ! / Gamma (β + n + 1 : ℂ)) *
        angularJacobiSum β n x y := by
  let q : ℂ := (x + y * I) ^ 2
  have hqnorm : ‖q‖ = x ^ 2 + y ^ 2 := by
    simp only [q, norm_pow, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hq : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hqnorm]; exact hs.ne')
  have hc : Real.cos q.arg = (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) := by
    rw [Complex.cos_arg hq, hqnorm]
    simp [q, pow_two]
  have hsin : Real.sin q.arg = 2 * x * y / (x ^ 2 + y ^ 2) := by
    rw [Complex.sin_arg, hqnorm]
    simp [q, pow_two] ; ring
  have hs0 : (x ^ 2 + y ^ 2 : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hβC : -1 < (β : ℂ).re := by simp; linarith
  have hG0 : Gamma (β + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG1 : Gamma (β + 1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hP : poch ((β : ℂ) + 1) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n
  have hF : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hG : Gamma (β + n + 1 : ℂ) = poch ((β : ℂ) + 1) n * Gamma (β + 1 : ℂ) := by
    rw [show (β : ℂ) + n + 1 = ((β : ℂ) + 1) + n by ring]
    exact Gamma_add_nat_eq_poch_mul_Gamma (by simp; linarith) n
  have hL := ultrasphPoly_laplace_integral (lam := β + 1 / 2) (by linarith) n q.arg
  rw [show ((β + 1 / 2 : ℝ) : ℂ) = (β : ℂ) + 1 / 2 by push_cast; ring,
    gegenbauer_normalized_jacobi hβ] at hL
  have hpow : ∀ phi : ℝ,
      ((x : ℂ) ^ 2 - y ^ 2 + 2 * I * x * y * Real.cos phi) ^ n =
      (x ^ 2 + y ^ 2 : ℂ) ^ n *
        (Real.cos q.arg + I * Real.sin q.arg * Real.cos phi : ℂ) ^ n := by
    intro phi
    rw [← mul_pow, hc, hsin]
    push_cast
    congr 1
    field_simp
  have hW : ∀ phi ∈ Set.uIcc (0 : ℝ) Real.pi,
      (Real.sin phi : ℂ) ^ (2 * β : ℂ) =
        ((Real.sin phi ^ (2 * (β + 1 / 2) - 1) : ℝ) : ℂ) := by
    intro phi hphi
    rw [Set.uIcc_of_le Real.pi_pos.le] at hphi
    rw [show (2 * (β : ℂ)) = ((2 * β : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (Real.sin_nonneg_of_mem_Icc hphi)]
    congr 2
    ring
  have hI : (∫ phi : ℝ in (0 : ℝ)..Real.pi,
      ((x : ℂ) ^ 2 - y ^ 2 + 2 * I * x * y * Real.cos phi) ^ n *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) =
      (x ^ 2 + y ^ 2 : ℂ) ^ n * ∫ phi : ℝ in (0 : ℝ)..Real.pi,
      (Real.cos q.arg + I * Real.sin q.arg * Real.cos phi : ℂ) ^ n *
        ((Real.sin phi ^ (2 * (β + 1 / 2) - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro phi hphi
    dsimp only
    rw [hpow, hW phi hphi]
    ring
  rw [hI]
  have hscaled := angularJacobiSum_eq hβ n hs
  have harg : ((Real.cos q.arg : ℝ) : ℂ) = (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) := by rw [hc]; push_cast; rfl
  conv_lhs at hL => rw [harg, jacobiPolyP_one ]
  have hGammaArgs : (β + 1 / 2 + 1 / 2 : ℂ) = β + 1 := by ring
  rw [show (β : ℂ) + 1 / 2 + 1 / 2 = β + 1 by ring] at hL
  rw [hG]
  let J : ℂ := ∫ phi : ℝ in (0 : ℝ)..Real.pi,
    (Real.cos q.arg + I * Real.sin q.arg * Real.cos phi : ℂ) ^ n *
      ((Real.sin phi ^ (2 * (β + 1 / 2) - 1) : ℝ) : ℂ)
  change _ = _ * J at hL
  change (x ^ 2 + y ^ 2 : ℂ) ^ n * J = _
  rw [div_div_eq_mul_div, div_mul_eq_mul_div] at hL
  have hLcross := (div_eq_div_iff hP (mul_ne_zero hπ hG1)).mp hL
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero hP hG0)).mpr
  linear_combination (Real.sqrt Real.pi * Gamma (β + 1 / 2 : ℂ) * (n ! : ℂ)) * hscaled -
    ((x ^ 2 + y ^ 2 : ℂ) ^ n) * hLcross

/-- Gaussian radial moments, including integrability at zero. -/
theorem gaussian_radial_moment {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun r : ℝ => exp (-(r : ℂ) ^ 2) * (r : ℂ) ^ (2 * s - 1 : ℂ)) (Ioi 0) ∧
    (∫ r : ℝ in Ioi 0, exp (-(r : ℂ) ^ 2) * (r : ℂ) ^ (2 * s - 1 : ℂ)) =
      (1 / 2) * Gamma (s : ℂ) := by
  have hi : IntegrableOn (fun r : ℝ => r ^ (2 * s - 1) * Real.exp (-r ^ 2)) (Ioi 0) := by
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, neg_mul, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := 2 * s - 1) (b := 1)
        (by linarith) (by norm_num) (by norm_num))
  have he : ∀ r : ℝ, 0 < r → exp (-(r : ℂ) ^ 2) * (r : ℂ) ^ (2 * s - 1 : ℂ) =
      ((r ^ (2 * s - 1) * Real.exp (-r ^ 2) : ℝ) : ℂ) := by
    intro r hr
    rw [show (2 * (s : ℂ) - 1) = ((2 * s - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hr.le]
    push_cast
    ring
  refine ⟨(hi.ofReal).congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => (he r hr).symm)), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_complex_ofReal]
  -- Mathlib's real Gaussian moment theorem fixes the radial Gamma normalization.
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2 * s - 1) (b := 1)
    (by norm_num) (by linarith) (by norm_num)
  simp only [neg_mul, one_mul, Real.one_rpow,
    show (2 * s - 1 + 1) / 2 = s by ring] at h
  have hr : (∫ x : ℝ in Ioi 0, x ^ (2 * s - 1) * Real.exp (-x ^ 2)) = (1 / 2) * Real.Gamma s := by
    convert h using 1
    congr 1
    funext x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hr, Complex.Gamma_ofReal]
  push_cast
  ring

/-- The square map takes the open unit interval bijectively to itself. -/
theorem square_image_Ioo : (fun r : ℝ => r ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨sq_pos_of_pos hr.1, by nlinarith [hr.1, hr.2]⟩
  · intro hx
    exact ⟨Real.sqrt x, ⟨Real.sqrt_pos.mpr hx.1, (Real.sqrt_lt' zero_lt_one).mpr (by simpa using hx.2)⟩,
      Real.sq_sqrt hx.1.le⟩

/-- Beta radial moments after the square substitution; endpoint singularities are retained. -/
theorem beta_radial_moment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun r : ℝ => (r : ℂ) ^ (2 * a - 1 : ℂ) * (1 - (r : ℂ) ^ 2) ^ (b - 1 : ℂ)) volume 0 1 ∧
    (∫ r : ℝ in (0 : ℝ)..1, (r : ℂ) ^ (2 * a - 1 : ℂ) * (1 - (r : ℂ) ^ 2) ^ (b - 1 : ℂ)) =
      (1 / 2) * (Gamma (a : ℂ) * Gamma (b : ℂ) / Gamma (a + b : ℂ)) := by
  let f : ℝ → ℂ := fun u => (u : ℂ) ^ (a - 1 : ℂ) * (1 - (u : ℂ)) ^ (b - 1 : ℂ)
  have hf : IntegrableOn f (Ioo 0 1) := by
    exact ((betaIntegral_convergent (by simpa using ha) (by simpa using hb)).1).mono_set Ioo_subset_Ioc_self
  have hd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * r) (Ioo 0 1) r := by
    intro r _
    simpa only [Nat.reduceSub, pow_one, mul_one, Nat.cast_ofNat] using
      (hasDerivAt_pow 2 r).hasDerivWithinAt (s := Ioo 0 1)
  have hinj : InjOn (fun r : ℝ => r ^ 2) (Ioo 0 1) := by
    intro r hr t ht hrt
    nlinarith [hr.1, ht.1]
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj f)
  rw [square_image_Ioo] at hi
  have ht : ∀ r ∈ Ioo (0 : ℝ) 1, |2 * r| • f (r ^ 2) =
      2 * ((r : ℂ) ^ (2 * a - 1 : ℂ) * (1 - (r : ℂ) ^ 2) ^ (b - 1 : ℂ)) := by
    intro r hr
    rw [abs_of_pos (by linarith [hr.1]), Complex.real_smul]
    dsimp only [f]
    push_cast
    have hsq : ((r : ℂ) ^ 2) ^ ((a : ℂ) - 1) = (r : ℂ) ^ (2 * ((a : ℂ) - 1)) := by
      rw [← Complex.ofReal_pow, ← Real.rpow_natCast]
      exact (Complex.cpow_mul_ofReal_nonneg hr.1.le 2 ((a : ℂ) - 1)).symm
    rw [hsq]
    rw [show (2 : ℂ) * ((a : ℂ) - 1) = (2 * (a : ℂ) - 1) - 1 by ring,
      cpow_sub _ _ (ofReal_ne_zero.mpr hr.1.ne'), cpow_one]
    field_simp [ofReal_ne_zero.mpr hr.1.ne']
  have hif : IntegrableOn (fun r : ℝ => (r : ℂ) ^ (2 * a - 1 : ℂ) *
      (1 - (r : ℂ) ^ 2) ^ (b - 1 : ℂ)) (Ioo 0 1) := by
    have htwo := (hi.mp hf).congr_fun ht measurableSet_Ioo
    have hh := htwo.const_mul (1 / 2 : ℂ)
    exact hh.congr (Filter.Eventually.of_forall fun r => by dsimp only; ring)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hif, ?_⟩
  -- Mathlib's Jacobian formula also applies to these integrable endpoint singularities.
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj f
  rw [square_image_Ioo, setIntegral_congr_fun measurableSet_Ioo ht, integral_const_mul] at hchange
  have hbval : (∫ u : ℝ in Ioo 0 1, f u) = Gamma (a : ℂ) * Gamma (b : ℂ) / Gamma (a + b : ℂ) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    have hgab : Gamma (a + b : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    apply (eq_div_iff hgab).mpr
    change betaIntegral (a : ℂ) (b : ℂ) * Gamma (a + b : ℂ) = _
    rw [mul_comm]
    exact (Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ)) (by simpa using ha) (by simpa using hb)).symm
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [hbval] at hchange
  linear_combination -(1 / 2 : ℂ) * hchange

/-- Gamma-normalized finite Jacobi expansion at a real angle. -/
theorem jacobi_half_angle_normalized {α β : ℝ} (hα : -1 < α) (n : ℕ) (θ : ℝ) :
    jacobiPolyP α β n (Real.cos θ) / jacobiPolyP α β n 1 =
      Gamma (α + 1 : ℂ) * n ! * ∑ k ∈ Finset.range (n + 1),
        poch ((β : ℂ) + k + 1) (n - k) /
          ((k ! : ℂ) * (n - k) ! * Gamma (α + (n - k : ℕ) + 1 : ℂ)) *
        (-((Real.sin (θ / 2) : ℂ) ^ 2)) ^ (n - k) * ((Real.cos (θ / 2) : ℂ) ^ 2) ^ k := by
  have hm : (Real.cos θ : ℂ) - 1 = 2 * (-((Real.sin (θ / 2) : ℂ) ^ 2)) := by
    have h := Real.cos_two_mul (θ / 2)
    have hcs := Real.cos_sq_add_sin_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact_mod_cast (by nlinarith : Real.cos θ - 1 = 2 * (-(Real.sin (θ / 2) ^ 2)))
  have hp : (Real.cos θ : ℂ) + 1 = 2 * ((Real.cos (θ / 2) : ℂ) ^ 2) := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact_mod_cast (by linarith : Real.cos θ + 1 = 2 * Real.cos (θ / 2) ^ 2)
  have hP : poch ((α : ℂ) + 1) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n
  rw [jacobi_binomial_sum (by simpa using hα), jacobiPolyP_one ]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hA : 0 < ((α : ℂ) + (n - k : ℕ) + 1).re := by
    simp; linarith [Nat.cast_nonneg (α := ℝ) (n - k)]
  have hG : Gamma (α + (n - k : ℕ) + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos hA
  have h0 : Gamma (α + n + 1 : ℂ) = poch ((α : ℂ) + 1) n * Gamma (α + 1 : ℂ) := by
    rw [show (α : ℂ) + n + 1 = ((α : ℂ) + 1) + n by ring]
    exact Gamma_add_nat_eq_poch_mul_Gamma (by simp; linarith) n
  have h1 : Gamma (α + n + 1 : ℂ) =
      poch ((α : ℂ) + n - k + 1) k * Gamma (α + (n - k : ℕ) + 1 : ℂ) := by
    have h := Gamma_add_nat_eq_poch_mul_Gamma hA k
    convert h using 1 <;> push_cast [Nat.cast_sub hk'] <;> congr 1 <;> ring
  have hratio : poch ((α : ℂ) + n - k + 1) k / poch ((α : ℂ) + 1) n =
      Gamma (α + 1 : ℂ) / Gamma (α + (n - k : ℕ) + 1 : ℂ) := by
    apply (div_eq_div_iff hP hG).mpr
    linear_combination h0 - h1
  have htwo : (2 : ℂ) ^ n = 2 ^ (n - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [hm, hp, mul_pow, mul_pow, htwo]
  calc
    _ = (poch ((β : ℂ) + k + 1) (n - k) / ((k ! : ℂ) * (n - k) !) * n ! *
        (-((Real.sin (θ / 2) : ℂ) ^ 2)) ^ (n - k) * ((Real.cos (θ / 2) : ℂ) ^ 2) ^ k) *
        (poch ((α : ℂ) + n - k + 1) k / poch ((α : ℂ) + 1) n) := by
      field_simp
    _ = _ := by rw [hratio]; ring

/-- Identity under the stated parameter and domain assumptions: `jacobiPolyP α β n (Real.cos θ) /
jacobiPolyP α β n 1 = 2 * Gamma (α + 1 : ℂ) / (Real.sqrt Real.pi * Gamma (α - β : ℂ) * Gamma
(β + 1 / 2 : ℂ)) * ∫ r : ℝ in (0 : ℝ)..1, ∫ phi : ℝ in (0 : ℝ)..Real.pi, ((Real.cos (θ / 2) :
ℂ) ^ 2 - r ^ 2 * (Real.sin (θ / 2) : ℂ) ^ 2 + I * r * Real.sin θ * Real.cos phi) ^ n * (1 - r
^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * β : ℂ)`. -/
@[dlmf 18.10.E3]
theorem jacobi_double_laplace_integral {α β : ℝ} (hαβ : β < α) (hβ : -1 / 2 < β)
    (n : ℕ) (θ : ℝ) :
    jacobiPolyP α β n (Real.cos θ) / jacobiPolyP α β n 1 =
      2 * Gamma (α + 1 : ℂ) / (Real.sqrt Real.pi * Gamma (α - β : ℂ) * Gamma (β + 1 / 2 : ℂ)) *
      ∫ r : ℝ in (0 : ℝ)..1, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((Real.cos (θ / 2) : ℂ) ^ 2 - r ^ 2 * (Real.sin (θ / 2) : ℂ) ^ 2 +
          I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ) := by
  let c : ℝ := Real.cos (θ / 2)
  let s : ℝ := Real.sin (θ / 2)
  let K : ℂ := Real.sqrt Real.pi * Gamma (β + 1 / 2 : ℂ) * n ! / Gamma (β + n + 1 : ℂ)
  let D : ℕ → ℂ := fun k => poch ((β : ℂ) + n - k + 1) k / k ! *
    (poch ((β : ℂ) + k + 1) (n - k) / (n - k) !) * (-((s : ℂ) ^ 2)) ^ (n - k) * ((c : ℂ) ^ 2) ^ k
  let F : ℕ → ℝ → ℂ := fun k r => (r : ℂ) ^ (2 * ((β : ℂ) + (n - k : ℕ) + 1) - 1) *
    (1 - (r : ℂ) ^ 2) ^ (α - β - 1 : ℂ)
  have hpos (k : ℕ) : 0 < β + (n - k : ℕ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (n - k)
    linarith
  have hF (k : ℕ) : IntervalIntegrable (F k) volume 0 1 ∧
      (∫ r : ℝ in (0 : ℝ)..1, F k r) = (1 / 2) *
        (Gamma (β + (n - k : ℕ) + 1 : ℂ) * Gamma (α - β : ℂ) /
          Gamma (α + (n - k : ℕ) + 1 : ℂ)) := by
    have h := beta_radial_moment (hpos k) (sub_pos.mpr hαβ)
    dsimp only [F]
    convert h using 1 <;> push_cast <;> ring
  have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hsin : Real.sin θ = 2 * s * c := by
    have h := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact h
  have hin (r : ℝ) (hr : r ∈ Set.Ioo 0 1) :
      (∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((c : ℂ) ^ 2 - r ^ 2 * (s : ℂ) ^ 2 + I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) = K * ∑ k ∈ Finset.range (n + 1), D k * F k r := by
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.1.ne'
    have hnorm : 0 < c ^ 2 + (r * s) ^ 2 := by
      by_cases hc : c = 0
      · have hs : s ≠ 0 := by intro h; simp [hc, h] at hcs
        rw [hc, zero_pow (by norm_num), zero_add]
        exact sq_pos_of_ne_zero (mul_ne_zero hr.1.ne' hs)
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hc) (sq_nonneg _)
    have h := angular_homogeneous hβ n (x := c) (y := r * s) hnorm
    have heq : (∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((c : ℂ) ^ 2 - r ^ 2 * (s : ℂ) ^ 2 + I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) =
      ((1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ)) *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((c : ℂ) ^ 2 - (r * s : ℝ) ^ 2 + 2 * I * c * ((r * s : ℝ) : ℂ) * Real.cos phi) ^ n *
          (Real.sin phi : ℂ) ^ (2 * β : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro phi _
      dsimp only
      rw [hsin]
      push_cast
      have he : (c : ℂ) ^ 2 - r ^ 2 * (s : ℂ) ^ 2 + I * r * ((2 * s * c : ℝ) : ℂ) * Real.cos phi =
          (c : ℂ) ^ 2 - ((r * s : ℝ) : ℂ) ^ 2 + 2 * I * c * ((r * s : ℝ) : ℂ) * Real.cos phi := by
        push_cast
        ring
      push_cast at he
      rw [he]
      ring
    rw [heq, h]
    simp only [angularJacobiSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hp : (r : ℂ) ^ (2 * β + 1 : ℂ) * (r : ℂ) ^ (2 * (n - k)) =
        (r : ℂ) ^ (2 * ((β : ℂ) + (n - k : ℕ) + 1) - 1) := by
      rw [← cpow_natCast, ← cpow_add _ _ hr0]
      congr 1
      push_cast
      ring
    dsimp only [K, D, F]
    push_cast
    rw [mul_pow, neg_pow, mul_pow, ← pow_mul]
    linear_combination
      (Real.sqrt Real.pi * Gamma (β + 1 / 2 : ℂ) * n ! / Gamma (β + n + 1 : ℂ) *
        (poch ((β : ℂ) + n - k + 1) k / k !) *
        (poch ((β : ℂ) + k + 1) (n - k) / (n - k) !) * (-1) ^ (n - k) *
        ((s : ℂ) ^ 2) ^ (n - k) * ((c : ℂ) ^ 2) ^ k * (1 - (r : ℂ) ^ 2) ^ (α - β - 1 : ℂ)) * hp
  have houter : (∫ r : ℝ in (0 : ℝ)..1, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((c : ℂ) ^ 2 - r ^ 2 * (s : ℂ) ^ 2 + I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) =
      K * ∑ k ∈ Finset.range (n + 1), D k *
        ((1 / 2) * (Gamma (β + (n - k : ℕ) + 1 : ℂ) * Gamma (α - β : ℂ) /
          Gamma (α + (n - k : ℕ) + 1 : ℂ))) := by
    have hfi (k : ℕ) : IntegrableOn (F k) (Set.Ioo 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (hF k).1
    have hval (k : ℕ) : (∫ r : ℝ in Set.Ioo 0 1, F k r) = (1 / 2) *
        (Gamma (β + (n - k : ℕ) + 1 : ℂ) * Gamma (α - β : ℂ) /
          Gamma (α + (n - k : ℕ) + 1 : ℂ)) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
      exact (hF k).2
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo hin, integral_const_mul,
      integral_finsetSum _ fun k _ => (hfi k).const_mul _]
    simp only [integral_const_mul]
    simp_rw [hval]
  rw [show (Real.cos (θ / 2) : ℂ) = (c : ℂ) from rfl,
    show (Real.sin (θ / 2) : ℂ) = (s : ℂ) from rfl, houter,
    jacobi_half_angle_normalized (by linarith : -1 < α)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hA : 0 < ((β : ℂ) + (n - k : ℕ) + 1).re := by simpa using hpos k
  have hg : Gamma (β + n + 1 : ℂ) =
      poch ((β : ℂ) + n - k + 1) k * Gamma (β + (n - k : ℕ) + 1 : ℂ) := by
    have h := Gamma_add_nat_eq_poch_mul_Gamma hA k
    convert h using 1 <;> push_cast [Nat.cast_sub hk'] <;> congr 1 <;> ring
  have hG : Gamma (β + n + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hGr : Gamma (α + (n - k : ℕ) + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; linarith [Nat.cast_nonneg (α := ℝ) (n - k)])
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hΓ : Gamma (β + 1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hΓ' : Gamma (((β : ℂ) * 2 + 1) / 2) ≠ 0 := by
    convert hΓ using 1 ; congr 1 ; ring
  have hΓab : Gamma (α - β : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hf (j : ℕ) : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  dsimp only [K, D, c, s]
  field_simp [hf k, hf (n - k), hf n, hΓ, hΓ', hG, hGr, hΓab, hπ]
  linear_combination (Gamma (α + 1 : ℂ) * poch ((β : ℂ) + k + 1) (n - k) *
    (-((Real.sin (θ / 2) : ℂ) ^ 2)) ^ (n - k) * ((Real.cos (θ / 2) : ℂ) ^ 2) ^ k) * hg

/-- Identity under the stated parameter and domain assumptions: `laguerrePolyL α n ((x : ℂ) ^ 2) =
2 * (-1 : ℂ) ^ n / (Real.sqrt Real.pi * Gamma (α + 1 / 2 : ℂ) * n.factorial) * ∫ r : ℝ in
Set.Ioi 0, ∫ phi : ℝ in (0 : ℝ)..Real.pi, ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi)
^ n * exp (-(r : ℂ) ^ 2) * (r : ℂ) ^ (2 * α + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * α : ℂ)`. -/
@[dlmf 18.10.E6]
theorem laguerrePolyL_double_laplace_integral {α : ℝ} (hα : -1 / 2 < α) (n : ℕ) (x : ℝ) :
    laguerrePolyL α n ((x : ℂ) ^ 2) =
      2 * (-1 : ℂ) ^ n / (Real.sqrt Real.pi * Gamma (α + 1 / 2 : ℂ) * n.factorial) *
      ∫ r : ℝ in Set.Ioi 0, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n * exp (-(r : ℂ) ^ 2) *
        (r : ℂ) ^ (2 * α + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * α : ℂ) := by
  let K : ℂ := Real.sqrt Real.pi * Gamma (α + 1 / 2 : ℂ) * n ! / Gamma (α + n + 1 : ℂ)
  let D : ℕ → ℂ := fun k => poch ((α : ℂ) + n - k + 1) k / k ! *
    (poch ((α : ℂ) + k + 1) (n - k) / (n - k) !) * (-1) ^ (n - k) * ((x : ℂ) ^ 2) ^ k
  let F : ℕ → ℝ → ℂ := fun k r => exp (-(r : ℂ) ^ 2) *
    (r : ℂ) ^ (2 * ((α : ℂ) + (n - k : ℕ) + 1) - 1)
  have hpos (k : ℕ) : 0 < α + (n - k : ℕ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (n - k)
    linarith
  have hF (k : ℕ) : IntegrableOn (F k) (Set.Ioi 0) ∧
      (∫ r : ℝ in Set.Ioi 0, F k r) = (1 / 2) * Gamma (α + (n - k : ℕ) + 1 : ℂ) := by
    dsimp only [F]
    have h := gaussian_radial_moment (hpos k)
    push_cast at h
    exact h
  have hin (r : ℝ) (hr : 0 < r) :
      (∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n * exp (-(r : ℂ) ^ 2) *
        (r : ℂ) ^ (2 * α + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * α : ℂ)) =
      K * ∑ k ∈ Finset.range (n + 1), D k * F k r := by
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    have h := angular_homogeneous hα n (x := x) (y := r) (by nlinarith [sq_nonneg x])
    have heq : (∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n * exp (-(r : ℂ) ^ 2) *
        (r : ℂ) ^ (2 * α + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * α : ℂ)) =
      (exp (-(r : ℂ) ^ 2) * (r : ℂ) ^ (2 * α + 1 : ℂ)) *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n *
          (Real.sin phi : ℂ) ^ (2 * α : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro phi _
      dsimp only
      ring
    rw [heq, h]
    simp only [angularJacobiSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hp : (r : ℂ) ^ (2 * α + 1 : ℂ) * (r : ℂ) ^ (2 * (n - k)) =
        (r : ℂ) ^ (2 * ((α : ℂ) + (n - k : ℕ) + 1) - 1) := by
      rw [← cpow_natCast, ← cpow_add _ _ hr0]
      congr 1
      push_cast
      ring
    dsimp only [K, D, F]
    rw [neg_pow, ← pow_mul]
    linear_combination
      (Real.sqrt Real.pi * Gamma (α + 1 / 2 : ℂ) * n ! / Gamma (α + n + 1 : ℂ) *
        (poch ((α : ℂ) + n - k + 1) k / k !) *
        (poch ((α : ℂ) + k + 1) (n - k) / (n - k) !) * (-1) ^ (n - k) *
        ((x : ℂ) ^ 2) ^ k * exp (-(r : ℂ) ^ 2)) * hp
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_const_mul,
    integral_finsetSum _ fun k _ => (hF k).1.const_mul _]
  simp only [integral_const_mul]
  simp_rw [(hF _).2]
  rw [laguerrePolyL_eq_sum (not_neg_nat_of_re_pos (by simp; linarith)), Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hA : 0 < ((α : ℂ) + (n - k : ℕ) + 1).re := by simpa using hpos k
  have hg : Gamma (α + n + 1 : ℂ) =
      poch ((α : ℂ) + n - k + 1) k * Gamma (α + (n - k : ℕ) + 1 : ℂ) := by
    have h := Gamma_add_nat_eq_poch_mul_Gamma hA k
    convert h using 1 <;> push_cast [Nat.cast_sub hk'] <;> congr 1 <;> ring
  have hG : Gamma (α + n + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hΓ : Gamma (α + 1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hf (j : ℕ) : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hsign : (-1 : ℂ) ^ n * (-1) ^ (n - k) = (-1) ^ k := by
    conv_lhs => arg 1; rw [show n = k + (n - k) by omega, pow_add]
    rw [mul_assoc, ← mul_pow]
    simp
  dsimp only [K, D]
  rw [neg_pow]
  rw [show (α : ℂ) + 1 + k = α + k + 1 by ring]
  have hΓ' : Gamma (((α : ℂ) * 2 + 1) / 2) ≠ 0 := by
    convert hΓ using 1 ; congr 1 ; ring
  field_simp [hf k, hf (n - k), hf n, hΓ, hΓ', hG, hπ]
  linear_combination (poch ((α : ℂ) + k + 1) (n - k) * ((x : ℂ) ^ 2) ^ k) *
    ((-1 : ℂ) ^ n * (-1) ^ (n - k) * hg - Gamma (α + n + 1 : ℂ) * hsign)

end DoubleLaplaceIntegrals

/-- Identity under the stated parameter and domain assumptions: `laguerrePolyL α n x = exp (x : ℂ)
* (x : ℂ) ^ (-α / 2 : ℂ) / n.factorial * ∫ t : ℝ in Set.Ioi 0, exp (-t : ℂ) * (t : ℂ) ^ (n + α
/ 2 : ℂ) * besselJ α (2 * Real.sqrt (x * t))`. -/
@[dlmf 18.10.E9]
theorem laguerrePolyL_bessel_integral {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerrePolyL α n x = exp (x : ℂ) * (x : ℂ) ^ (-α / 2 : ℂ) / n.factorial *
      ∫ t : ℝ in Set.Ioi 0, exp (-t : ℂ) * (t : ℂ) ^ (n + α / 2 : ℂ) *
        besselJ α (2 * Real.sqrt (x * t)) := by
  have hc : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := by
    intro k hk
    have h := congrArg Complex.re hk
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have ha : 0 < ((n : ℂ) + α + 1).re := by
    simp only [add_re, natCast_re, ofReal_re, one_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h := regularized_bessel_integral (a := (n : ℂ) + α + 1) (b := (α : ℂ) + 1)
    (z := (x : ℂ)) ha (by simpa using hx)
  rw [regularizedConfluent_kummer_transform] at h
  rw [show ((α : ℂ) + 1) - ((n : ℂ) + α + 1) = -(n : ℂ) by ring,
    neg_neg, show (1 - ((α : ℂ) + 1)) / 2 = -(α : ℂ) / 2 by ring] at h
  have hi : (∫ t : ℝ in Set.Ioi 0,
      exp (-(t : ℂ)) * (t : ℂ) ^ ((n : ℂ) + α + 1 - ((α : ℂ) + 1) / 2 - 1 / 2) *
        besselJ ((α : ℂ) + 1 - 1) (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ))) =
      ∫ t : ℝ in Set.Ioi 0, exp (-t : ℂ) * (t : ℂ) ^ (n + α / 2 : ℂ) *
        besselJ α (2 * Real.sqrt (x * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have ht0 : 0 < t := ht
    have hs : (((x * t : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = (Real.sqrt (x * t) : ℂ) := by
      rw [Real.sqrt_eq_rpow, ofReal_cpow (mul_nonneg hx.le ht0.le)]
      norm_num
    rw [show ((n : ℂ) + α + 1 - ((α : ℂ) + 1) / 2 - 1 / 2) = n + α / 2 by ring,
      show (α : ℂ) + 1 - 1 = α by ring, ← ofReal_mul, hs]
  rw [hi] at h
  rw [laguerrePolyL_eq_Gamma_mul_regularized hc]
  have hg : Gamma ((n : ℂ) + α + 1) ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have he : exp (x : ℂ) * exp (-(x : ℂ)) = 1 := by rw [← exp_add]; simp
  field_simp at h ⊢
  linear_combination (exp (x : ℂ)) * h -
    Gamma ((n : ℂ) + α + 1) * regularizedHGFun {-(n : ℂ)} {(α : ℂ) + 1} x * he

/-- For `g` even, the Fourier integral over `[-1, 1]` is twice the cosine integral over `[0, 1]`. -/
theorem integral_mul_exp_of_even {g : ℝ → ℂ} (hg : IntervalIntegrable g volume (-1) 1)
    (hev : ∀ x, g (-x) = g x) (y : ℝ) :
    ∫ x : ℝ in (-1 : ℝ)..1, g x * exp (I * x * y) =
      2 * ∫ x : ℝ in (0 : ℝ)..1, g x * Real.cos (x * y) := by
  have hs1 : Set.uIcc (-1 : ℝ) 0 ⊆ Set.uIcc (-1) 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have hs2 : Set.uIcc (0 : ℝ) 1 ⊆ Set.uIcc (-1) 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc (by norm_num) le_rfl
  have h1 : IntervalIntegrable g volume (-1) 0 := hg.mono_set hs1
  have h2 : IntervalIntegrable g volume 0 1 := hg.mono_set hs2
  have hc {a b : ℝ} {f : ℝ → ℂ} (h : IntervalIntegrable g volume a b) (hf : Continuous f) :
      IntervalIntegrable (fun x => g x * f x) volume a b := h.mul_continuousOn hf.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc h1 (by fun_prop)) (hc h2 (by fun_prop))]
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := 1)
    (fun x : ℝ => g x * exp (I * x * y))
  norm_num only [neg_zero] at hneg
  simp only [hev, ofReal_neg] at hneg
  rw [← hneg, ← intervalIntegral.integral_add
    (hc (f := fun x : ℝ => exp (I * -(x : ℂ) * y)) h2 (by fun_prop))
    (hc (f := fun x : ℝ => exp (I * (x : ℂ) * y)) h2 (by fun_prop)),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  push_cast
  rw [show I * (-(x : ℂ)) * y = -(x * y) * I by ring, show I * (x : ℂ) * y = (x * y) * I by ring]
  linear_combination (-g x) * Complex.two_cos ((x : ℂ) * y)

/-- For `g` odd, the Fourier integral over `[-1, 1]` is `2i` times the sine integral over
`[0, 1]`. -/
theorem integral_mul_exp_of_odd {g : ℝ → ℂ} (hg : IntervalIntegrable g volume (-1) 1)
    (hodd : ∀ x, g (-x) = -g x) (y : ℝ) :
    ∫ x : ℝ in (-1 : ℝ)..1, g x * exp (I * x * y) =
      2 * I * ∫ x : ℝ in (0 : ℝ)..1, g x * Real.sin (x * y) := by
  have hs1 : Set.uIcc (-1 : ℝ) 0 ⊆ Set.uIcc (-1) 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have hs2 : Set.uIcc (0 : ℝ) 1 ⊆ Set.uIcc (-1) 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc (by norm_num) le_rfl
  have h1 : IntervalIntegrable g volume (-1) 0 := hg.mono_set hs1
  have h2 : IntervalIntegrable g volume 0 1 := hg.mono_set hs2
  have hc {a b : ℝ} {f : ℝ → ℂ} (h : IntervalIntegrable g volume a b) (hf : Continuous f) :
      IntervalIntegrable (fun x => g x * f x) volume a b := h.mul_continuousOn hf.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc h1 (by fun_prop)) (hc h2 (by fun_prop))]
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := 1)
    (fun x : ℝ => g x * exp (I * x * y))
  norm_num only [neg_zero] at hneg
  simp only [hodd, ofReal_neg, neg_mul, ← mul_neg] at hneg
  rw [← hneg, ← intervalIntegral.integral_add
    (hc (f := fun x : ℝ => -exp (I * -(x : ℂ) * y)) h2 (by fun_prop))
    (hc (f := fun x : ℝ => exp (I * (x : ℂ) * y)) h2 (by fun_prop)),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  push_cast
  rw [show I * (-(x : ℂ)) * y = -(x * y) * I by ring, show I * (x : ℂ) * y = (x * y) * I by ring]
  linear_combination (-(g x * I)) * Complex.two_sin ((x : ℂ) * y) +
    (-(g x) * (exp (-(x * y) * I) - exp ((x * y) * I))) * I_sq

/-- The Gegenbauer weight times a continuous function is integrable on `[-1, 1]`. -/
theorem intervalIntegrable_ultrasph_weight_mul {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    IntervalIntegrable (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam N x) volume (-1) 1 := by
  have hw := intervalIntegrable_jacobi_weight_cpow (a := (lam : ℂ) - 1 / 2)
    (b := (lam : ℂ) - 1 / 2) (by simp; linarith) (by simp; linarith)
  have hC : Continuous fun x : ℝ => ultrasphPoly lam N (x : ℂ) :=
    ((analyticOnNhd_ultrasphPoly (lam : ℂ) N).continuousOn.comp_continuous
      continuous_ofReal (fun _ => Set.mem_univ _))
  refine (hw.mul_continuousOn hC.continuousOn).congr fun x hx => ?_
  rw [Set.uIoc_of_le (by norm_num)] at hx
  have h1 : (1 - (x : ℂ) ^ 2) = ((1 - x : ℝ) : ℂ) * ((1 + x : ℝ) : ℂ) := by push_cast; ring
  rw [h1, mul_cpow_ofReal_nonneg (by linarith [hx.2]) (by linarith [hx.1])]
  push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (0 : ℝ)..1, (1 - (x :
ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam (2 * n) x * Real.cos (x * y) = (-1 : ℂ) ^ n *
Real.pi * Gamma (2 * n + 2 * lam : ℂ) * besselJ (lam + 2 * n) y / ((2 * n).factorial * Gamma
(lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ))`. -/
@[dlmf 18.17.E17]
theorem ultrasphPoly_even_cosine_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * n) x * Real.cos (x * y) =
      (-1 : ℂ) ^ n * Real.pi * Gamma (2 * n + 2 * lam : ℂ) * besselJ (lam + 2 * n) y /
        ((2 * n).factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  have hev : ∀ x : ℝ, (1 - ((-x : ℝ) : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * n) ((-x : ℝ) : ℂ) =
      (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam (2 * n) x := by
    intro x
    rw [ofReal_neg, ultrasphPoly_reflection (by simp; linarith), pow_mul]
    norm_num
  have h := integral_mul_exp_of_even (intervalIntegrable_ultrasph_weight_mul hlam (2 * n))
    hev y
  rw [ultrasphPoly_fourier_transform hlam (2 * n) hy] at h
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0)
  rw [← h, pow_mul, I_sq]
  push_cast
  rw [add_comm (lam : ℂ) (2 * n)]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (0 : ℝ)..1, (1 - (x :
ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam (2 * n + 1) x * Real.sin (x * y) = (-1 : ℂ) ^ n
* Real.pi * Gamma (2 * n + 2 * lam + 1 : ℂ) * besselJ (2 * n + lam + 1) y / ((2 * n +
1).factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ))`. -/
@[dlmf 18.17.E18]
theorem ultrasphPoly_odd_sine_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * n + 1) x * Real.sin (x * y) =
      (-1 : ℂ) ^ n * Real.pi * Gamma (2 * n + 2 * lam + 1 : ℂ) * besselJ (2 * n + lam + 1) y /
        ((2 * n + 1).factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  have hodd : ∀ x : ℝ, (1 - ((-x : ℝ) : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * n + 1) ((-x : ℝ) : ℂ) =
      -((1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam (2 * n + 1) x) := by
    intro x
    rw [ofReal_neg, ultrasphPoly_reflection (by simp; linarith),
      show ((-1 : ℂ)) ^ (2 * n + 1) = -1 by rw [pow_succ, pow_mul]; norm_num, neg_sq]
    ring
  have h := integral_mul_exp_of_odd (intervalIntegrable_ultrasph_weight_mul hlam (2 * n + 1))
    hodd y
  rw [ultrasphPoly_fourier_transform hlam (2 * n + 1) hy] at h
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero : (2 : ℂ) * I ≠ 0)
  rw [← h, pow_succ, pow_mul, I_sq]
  push_cast
  rw [show (2 * n + 1 : ℂ) + lam = 2 * n + lam + 1 by ring,
    show (2 * n + 1 : ℂ) + 2 * lam = 2 * n + 2 * lam + 1 by ring]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (-1 : ℝ)..1,
legendrePolyP n x * exp (I * x * y) = I ^ n * Real.sqrt (2 * Real.pi / y) * besselJ (n + 1 / 2
: ℂ) y`. -/
@[dlmf 18.17.E19]
theorem legendre_fourier_transform (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (-1 : ℝ)..1, legendrePolyP n x * exp (I * x * y) =
      I ^ n * Real.sqrt (2 * Real.pi / y) * besselJ (n + 1 / 2 : ℂ) y := by
  have h := ultrasphPoly_fourier_transform (lam := 1 / 2) (by norm_num) n hy
  push_cast at h
  norm_num only [sub_self, cpow_zero, one_mul, mul_one] at h
  simp only [legendre_eq_ultrasphPoly]
  rw [h, Complex.Gamma_nat_eq_factorial, Complex.Gamma_one_half_eq]
  have hs : ((π : ℂ)) ^ (1 / 2 : ℂ) = ((√π : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; norm_num
  have hr : (2 * (y : ℂ)) ^ (1 / 2 : ℂ) = ((√(2 * y) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by positivity)]; norm_num
  have key : √(2 * π / y) * (√π * √(2 * y)) = 2 * π := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
      show 2 * π / y * (π * (2 * y)) = (2 * π) ^ 2 by field_simp,
      Real.sqrt_sq (by positivity)]
  have keyC := congrArg (fun r : ℝ => (r : ℂ)) key
  push_cast at keyC
  have h1 : ((√π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have h2 : ((√(2 * y) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have h3 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [hs, hr]
  set J := besselJ ((n : ℂ) + 1 / 2) (y : ℂ) with hJ
  field_simp
  linear_combination (-J) * keyC

/-- `1/Γ(y) = (y)_m/Γ(y+m)` for every `y` and every `m`, including poles. -/
theorem recip_Gamma_eq_poch_mul_recip_Gamma_add (m : ℕ) (y : ℂ) :
    (Gamma y)⁻¹ = poch y m * (Gamma (y + m))⁻¹ := by
  cases m with
  | zero => simp [poch_zero]
  | succ p => exact recip_Gamma_eq_poch_mul p y

/-- The Mellin transform `∫₀¹ (1-x²)^{λ-1/2} C_{2m}^{(λ)}(x) x^{z-1} dx` in closed form, for
`λ > 0` and `Re z > 0`. -/
theorem ultrasphPoly_mellin_transform_even {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.re)
    (m : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * m) x * (x : ℂ) ^ (z - 1) =
      Real.pi * (2 : ℂ) ^ (1 - 2 * lam - z) * Gamma (((2 * m : ℕ) : ℂ) + 2 * lam : ℂ) * Gamma z /
        ((2 * m).factorial * Gamma (lam : ℂ) *
          Gamma (1 / 2 + ((2 * m : ℕ) : ℂ) / 2 + lam + z / 2) *
          Gamma (1 / 2 + z / 2 - ((2 * m : ℕ) : ℂ) / 2)) := by
  set K0 : ℂ := poch (lam : ℂ) m / poch (1 / 2) m * (-1 : ℂ) ^ m with hK0
  have hrw : ∀ x : ℝ, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam (2 * m) x *
      (x : ℂ) ^ (z - 1) = (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) * (x : ℂ) ^ (z - 1) *
        (K0 * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m
          ((1 - 2 * x ^ 2 : ℝ) : ℂ)) := by
    intro x
    rw [ultrasphPoly_quadratic_even (by simp; linarith),
      show 2 * (x : ℂ) ^ 2 - 1 = -((1 - 2 * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      jacobi_reflection (by simp; linarith) (by norm_num), hK0]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr (fun x _ => hrw x),
    integral_one_sub_sq_cpow_mul_cpow ((lam : ℂ) - 1 / 2) (z - 1)
      (fun s => K0 * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s)]
  have hz2 : 0 < (z / 2).re := by simp; linarith
  have hJ := jacobi_mellin_transform (α := -1 / 2) (β := lam - 1 / 2) (by norm_num)
    (by linarith) hz2 m
  have hint : (∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ ((z - 1 - 1) / 2) *
      (1 + (s : ℂ)) ^ ((lam : ℂ) - 1 / 2) *
      (K0 * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s)) =
      K0 * ∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ (z / 2 - 1) *
        (1 + (s : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) *
        jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show (z - 1 - 1) / 2 = z / 2 - 1 by ring]
    push_cast
    ring
  rw [hint, hJ]
  have hl : (0 : ℝ) < (lam : ℂ).re := by simpa using hlam
  rw [show (1 : ℂ) + ((lam - 1 / 2 : ℝ) : ℂ) + z / 2 + m = lam + 1 / 2 + z / 2 + m by
      push_cast; ring,
    show (1 / 2 : ℂ) + ((2 * m : ℕ) : ℂ) / 2 + lam + z / 2 = lam + 1 / 2 + z / 2 + m by
      push_cast; ring,
    show (1 : ℂ) + ((lam - 1 / 2 : ℝ) : ℂ) + m = (m + lam) + 1 / 2 by push_cast; ring,
    show ((2 * m : ℕ) : ℂ) + 2 * lam = 2 * (m + lam) by push_cast; ring,
    show (1 / 2 : ℂ) + z / 2 - ((2 * m : ℕ) : ℂ) / 2 = 1 / 2 + z / 2 - m by push_cast; ring,
    show (1 : ℂ) + ((-1 / 2 : ℝ) : ℂ) - z / 2 = 1 / 2 - z / 2 by push_cast; ring]
  -- the reciprocal of `Γ(1/2 + z/2 - m)`, valid also at poles
  have hE : (Gamma (1 / 2 + z / 2 - m))⁻¹ =
      (-1 : ℂ) ^ m * poch (1 / 2 - z / 2) m * (Gamma (1 / 2 + z / 2))⁻¹ := by
    have h := DLMF.Gamma.poch_neg_eq ((m : ℂ) - 1 / 2 - z / 2) m
    rw [show -((m : ℂ) - 1 / 2 - z / 2) = 1 / 2 + z / 2 - m by ring,
      show (m : ℂ) - 1 / 2 - z / 2 - m + 1 = 1 / 2 - z / 2 by ring] at h
    rw [recip_Gamma_eq_poch_mul_recip_Gamma_add m, h, show 1 / 2 + z / 2 - (m : ℂ) + m = 1 / 2 + z / 2
      by ring]
  have F1 := Complex.Gamma_mul_Gamma_add_half (z / 2)
  rw [show 2 * (z / 2) = z by ring, show z / 2 + 1 / 2 = 1 / 2 + z / 2 by ring] at F1
  have F2 := Complex.Gamma_mul_Gamma_add_half ((m : ℂ) + lam)
  have F3 : Gamma ((m : ℂ) + lam) = poch (lam : ℂ) m * Gamma lam := by
    rw [add_comm, Gamma_add_nat_eq_poch_mul_Gamma hl]
  have F4 := two_pow_mul_poch_half m
  have hpi : (Real.pi : ℂ) = (Real.sqrt Real.pi : ℂ) * (Real.sqrt Real.pi : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hV : (2 : ℂ) ^ (1 - 2 * (lam : ℂ) - z) * 2 =
      (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam)) * (2 : ℂ) ^ (1 - z) * (2 : ℂ) ^ (2 * m) := by
    rw [← cpow_natCast, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero,
      show 1 - 2 * ((m : ℂ) + lam) + (1 - z) + ((2 * m : ℕ) : ℂ) = (1 - 2 * lam - z) + 1 by
        push_cast; ring, cpow_add _ _ two_ne_zero, cpow_one]
  have hPQ : (2 : ℂ) ^ (-((lam : ℂ) - 1 / 2 + (z - 1 - 1) / 2)) *
      (2 : ℂ) ^ (((lam - 1 / 2 : ℝ) : ℂ) + z / 2) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show -((lam : ℂ) - 1 / 2 + (z - 1 - 1) / 2) +
      (((lam - 1 / 2 : ℝ) : ℂ) + z / 2) = 1 by push_cast; ring, cpow_one]
  have hW : Gamma (1 / 2 + z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hD : Gamma (lam + 1 / 2 + z / 2 + m) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hGl : Gamma (lam : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos hl
  have hph : poch (1 / 2 : ℂ) m ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) m
  have hfm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hS : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam)) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hU : (2 : ℂ) ^ (1 - z) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hF : (2 : ℂ) ^ (2 * m) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [hpi, div_mul_eq_div_div _ _ (Gamma (1 / 2 + z / 2 - (m : ℂ))),
    div_eq_mul_inv _ (Gamma (1 / 2 + z / 2 - (m : ℂ))), hE, ← F4]
  simp only [hK0]
  generalize (2 : ℂ) ^ (-((lam : ℂ) - 1 / 2 + (z - 1 - 1) / 2)) = P at hPQ ⊢
  generalize (2 : ℂ) ^ (((lam - 1 / 2 : ℝ) : ℂ) + z / 2) = Q at hPQ ⊢
  generalize (2 : ℂ) ^ (1 - 2 * (lam : ℂ) - z) = V at hV ⊢
  generalize (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam)) = T at hV hT F2 ⊢
  generalize (2 : ℂ) ^ (1 - z) = U at hV hU F1 ⊢
  generalize (2 : ℂ) ^ (2 * m) = F at hV hF ⊢
  generalize (Real.sqrt Real.pi : ℂ) = S at hS F1 F2 ⊢
  generalize Gamma (1 / 2 + z / 2) = W at hW F1 ⊢
  generalize Gamma (z / 2) = Gz2 at F1 ⊢
  generalize Gamma z = Gz at F1 ⊢
  generalize Gamma (2 * ((m : ℂ) + lam)) = G2 at F2 ⊢
  generalize Gamma ((m : ℂ) + lam) = Gml at F2 F3 ⊢
  generalize Gamma ((m : ℂ) + lam + 1 / 2) = Gmlh at F2 ⊢
  generalize Gamma (lam + 1 / 2 + z / 2 + m) = D at hD ⊢
  generalize Gamma (lam : ℂ) = Gl at hGl F3 ⊢
  generalize poch (1 / 2 : ℂ) m = ph at hph ⊢
  generalize poch (lam : ℂ) m = pl at F3 ⊢
  generalize poch (1 / 2 - z / 2) m = R
  generalize (m ! : ℂ) = fm at hfm ⊢
  have hG2 : G2 = Gml * Gmlh / (T * S) := by field_simp; linear_combination -F2
  have hGz : Gz = Gz2 * W / (U * S) := by field_simp; linear_combination -F1
  have hV' : V = T * U * F / 2 := by field_simp; linear_combination hV
  rw [hG2, hGz, hV', F3]
  field_simp
  linear_combination 2 * pl * Gz2 * Gmlh * R * hPQ

/-- The Mellin transform `∫₀¹ (1-x²)^{λ-1/2} C_{2m+1}^{(λ)}(x) x^{z-1} dx` in closed form, for
`λ > 0` and `Re z > 0`. -/
theorem ultrasphPoly_mellin_transform_odd {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.re)
    (m : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * m + 1) x * (x : ℂ) ^ (z - 1) =
      Real.pi * (2 : ℂ) ^ (1 - 2 * lam - z) * Gamma (((2 * m + 1 : ℕ) : ℂ) + 2 * lam : ℂ) *
        Gamma z / ((2 * m + 1).factorial * Gamma (lam : ℂ) *
          Gamma (1 / 2 + ((2 * m + 1 : ℕ) : ℂ) / 2 + lam + z / 2) *
          Gamma (1 / 2 + z / 2 - ((2 * m + 1 : ℕ) : ℂ) / 2)) := by
  set K1 : ℂ := poch (lam : ℂ) (m + 1) / poch (1 / 2) (m + 1) * (-1 : ℂ) ^ m with hK1
  have hrw : Set.EqOn (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * m + 1) x * (x : ℂ) ^ (z - 1))
      (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) * (x : ℂ) ^ z *
        (K1 * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m
          ((1 - 2 * x ^ 2 : ℝ) : ℂ))) (Set.Ioo 0 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
    simp only
    rw [ultrasphPoly_quadratic_odd (by simp; linarith),
      show 2 * (x : ℂ) ^ 2 - 1 = -((1 - 2 * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      jacobi_reflection (by simp; linarith) (by norm_num), hK1,
      show z = (z - 1) + 1 by ring, cpow_add _ _ hx0, cpow_one,
      show z - 1 + 1 - 1 = z - 1 by ring]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hrw,
    integral_one_sub_sq_cpow_mul_cpow ((lam : ℂ) - 1 / 2) z
      (fun s => K1 * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s)]
  have hw : 0 < (1 / 2 + z / 2).re := by simp; linarith
  have hJ := jacobi_mellin_transform (α := 1 / 2) (β := lam - 1 / 2) (by norm_num)
    (by linarith) hw m
  have hint : (∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ ((z - 1) / 2) *
      (1 + (s : ℂ)) ^ ((lam : ℂ) - 1 / 2) *
      (K1 * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s)) =
      K1 * ∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ (1 / 2 + z / 2 - 1) *
        (1 + (s : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) *
        jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show (z - 1) / 2 = 1 / 2 + z / 2 - 1 by ring]
    push_cast
    ring
  rw [hint, hJ]
  have hl : (0 : ℝ) < (lam : ℂ).re := by simpa using hlam
  rw [show (1 : ℂ) + ((lam - 1 / 2 : ℝ) : ℂ) + (1 / 2 + z / 2) + m = lam + 1 + z / 2 + m by
      push_cast; ring,
    show (1 / 2 : ℂ) + ((2 * m + 1 : ℕ) : ℂ) / 2 + lam + z / 2 = lam + 1 + z / 2 + m by
      push_cast; ring,
    show (1 : ℂ) + ((lam - 1 / 2 : ℝ) : ℂ) + m = (m + lam) + 1 / 2 by push_cast; ring,
    show ((2 * m + 1 : ℕ) : ℂ) + 2 * lam = 2 * ((m + lam) + 1 / 2) by push_cast; ring,
    show (1 / 2 : ℂ) + z / 2 - ((2 * m + 1 : ℕ) : ℂ) / 2 = z / 2 - m by push_cast; ring,
    show (1 : ℂ) + ((1 / 2 : ℝ) : ℂ) - (1 / 2 + z / 2) = 1 - z / 2 by push_cast; ring]
  have hE : (Gamma (z / 2 - m))⁻¹ =
      (-1 : ℂ) ^ m * poch (1 - z / 2) m * (Gamma (z / 2))⁻¹ := by
    have h := DLMF.Gamma.poch_neg_eq ((m : ℂ) - z / 2) m
    rw [show -((m : ℂ) - z / 2) = z / 2 - m by ring,
      show (m : ℂ) - z / 2 - m + 1 = 1 - z / 2 by ring] at h
    rw [recip_Gamma_eq_poch_mul_recip_Gamma_add m, h, show z / 2 - (m : ℂ) + m = z / 2 by ring]
  have F1 := Complex.Gamma_mul_Gamma_add_half (z / 2)
  rw [show 2 * (z / 2) = z by ring, show z / 2 + 1 / 2 = 1 / 2 + z / 2 by ring] at F1
  have F2 := Complex.Gamma_mul_Gamma_add_half ((m : ℂ) + lam + 1 / 2)
  rw [show (m : ℂ) + lam + 1 / 2 + 1 / 2 = lam + (m + 1 : ℕ) by push_cast; ring] at F2
  have F3 : Gamma ((lam : ℂ) + (m + 1 : ℕ)) = poch (lam : ℂ) (m + 1) * Gamma lam :=
    Gamma_add_nat_eq_poch_mul_Gamma hl (m + 1)
  have F4 : (2 : ℂ) ^ (2 * m + 1) * poch (1 / 2) (m + 1) * m ! = (2 * m + 1).factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul, ← two_pow_mul_poch_half m, poch_succ, pow_succ]
    push_cast
    ring
  have hpi : (Real.pi : ℂ) = (Real.sqrt Real.pi : ℂ) * (Real.sqrt Real.pi : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hV : (2 : ℂ) ^ (1 - 2 * (lam : ℂ) - z) * 2 =
      (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam + 1 / 2)) * (2 : ℂ) ^ (1 - z) * (2 : ℂ) ^ (2 * m + 1) := by
    rw [← cpow_natCast, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero,
      show 1 - 2 * ((m : ℂ) + lam + 1 / 2) + (1 - z) + ((2 * m + 1 : ℕ) : ℂ) =
        (1 - 2 * lam - z) + 1 by push_cast; ring, cpow_add _ _ two_ne_zero, cpow_one]
  have hPQ : (2 : ℂ) ^ (-((lam : ℂ) - 1 / 2 + (z - 1) / 2)) *
      (2 : ℂ) ^ (((lam - 1 / 2 : ℝ) : ℂ) + (1 / 2 + z / 2)) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show -((lam : ℂ) - 1 / 2 + (z - 1) / 2) +
      (((lam - 1 / 2 : ℝ) : ℂ) + (1 / 2 + z / 2)) = 1 by push_cast; ring, cpow_one]
  have hz2 : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hD : Gamma (lam + 1 + z / 2 + m) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hGl : Gamma (lam : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos hl
  have hph : poch (1 / 2 : ℂ) (m + 1) ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) _
  have hfm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hS : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam + 1 / 2)) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hU : (2 : ℂ) ^ (1 - z) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hF : (2 : ℂ) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [hpi, div_mul_eq_div_div _ _ (Gamma (z / 2 - (m : ℂ))),
    div_eq_mul_inv _ (Gamma (z / 2 - (m : ℂ))), hE, ← F4]
  simp only [hK1]
  generalize (2 : ℂ) ^ (-((lam : ℂ) - 1 / 2 + (z - 1) / 2)) = P at hPQ ⊢
  generalize (2 : ℂ) ^ (((lam - 1 / 2 : ℝ) : ℂ) + (1 / 2 + z / 2)) = Q at hPQ ⊢
  generalize (2 : ℂ) ^ (1 - 2 * (lam : ℂ) - z) = V at hV ⊢
  generalize (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam + 1 / 2)) = T at hV hT F2 ⊢
  generalize (2 : ℂ) ^ (1 - z) = U at hV hU F1 ⊢
  generalize (2 : ℂ) ^ (2 * m + 1) = F at hV hF ⊢
  generalize (Real.sqrt Real.pi : ℂ) = S at hS F1 F2 ⊢
  generalize Gamma (1 / 2 + z / 2) = W at F1 ⊢
  generalize Gamma (z / 2) = Gz2 at hz2 F1 ⊢
  generalize Gamma z = Gz at F1 ⊢
  generalize Gamma (2 * ((m : ℂ) + lam + 1 / 2)) = G2 at F2 ⊢
  generalize Gamma ((lam : ℂ) + (m + 1 : ℕ)) = Gml1 at F2 F3 ⊢
  generalize Gamma ((m : ℂ) + lam + 1 / 2) = Gmlh at F2 ⊢
  generalize Gamma (lam + 1 + z / 2 + m) = D at hD ⊢
  generalize Gamma (lam : ℂ) = Gl at hGl F3 ⊢
  generalize poch (1 / 2 : ℂ) (m + 1) = ph at hph ⊢
  generalize poch (lam : ℂ) (m + 1) = pl at F3 ⊢
  generalize poch (1 - z / 2) m = R
  generalize (m ! : ℂ) = fm at hfm ⊢
  have hG2 : G2 = Gmlh * Gml1 / (T * S) := by field_simp; linear_combination -F2
  have hGz : Gz = Gz2 * W / (U * S) := by field_simp; linear_combination -F1
  have hV' : V = T * U * F / 2 := by field_simp; linear_combination hV
  rw [hG2, hGz, hV', F3]
  field_simp
  linear_combination 2 * pl * W * Gmlh * R * hPQ

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (0 : ℝ)..1, (1 - (x :
ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam n x * (x : ℂ) ^ (z - 1) = Real.pi * (2 : ℂ) ^
(1 - 2 * lam - z) * Gamma (n + 2 * lam : ℂ) * Gamma z / (n.factorial * Gamma (lam : ℂ) * Gamma
(1 / 2 + n / 2 + lam + z / 2) * Gamma (1 / 2 + z / 2 - n / 2))`. -/
@[dlmf 18.17.E37]
theorem ultrasphPoly_mellin_transform {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam n x * (x : ℂ) ^ (z - 1) =
      Real.pi * (2 : ℂ) ^ (1 - 2 * lam - z) * Gamma (n + 2 * lam : ℂ) * Gamma z /
        (n.factorial * Gamma (lam : ℂ) * Gamma (1 / 2 + n / 2 + lam + z / 2) *
          Gamma (1 / 2 + z / 2 - n / 2)) := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · exact ultrasphPoly_mellin_transform_even hlam hz m
  · exact ultrasphPoly_mellin_transform_odd hlam hz m

/-- Finite-sum version, including parameters where the displayed hypergeometric quotient
has removable singularities. -/
@[dlmf 18.17.E40]
theorem laguerrePolyL_mellin_laplace_transform {a : ℝ} (ha : 0 < a) {α : ℂ} (hα : -1 < α.re)
    (b : ℂ) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-a * x) * laguerrePolyL α n (b * x) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ Finset.range (n + 1), poch (α + k + 1) (n - k) * (-b) ^ k /
        ((n - k).factorial * (k.factorial : ℂ)) * Gamma (z + k) / (a : ℂ) ^ (z + k) := by
  have hα' : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp only [add_re, one_re]; linarith)
  have heq (x : ℝ) : laguerrePolyL α n (b * x) =
      ∑ k ∈ Finset.range (n + 1),
        (poch (α + k + 1) (n - k) * (-b) ^ k / ((n - k).factorial * (k.factorial : ℂ))) *
          (x : ℂ) ^ k := by
    rw [laguerrePolyL_eq_sum hα']
    apply Finset.sum_congr rfl
    intro k _
    rw [show -(b * (x : ℂ)) = -b * x by ring, mul_pow]
    rw [show α + 1 + (k : ℂ) = α + k + 1 by ring]
    ring
  simp_rw [heq]
  exact integral_finite_sum_mellin_laplace ha hz _ _ id

end DLMF.OrthogonalPolynomials

end
end
