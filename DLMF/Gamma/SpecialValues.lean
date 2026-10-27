/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Digamma
public import DLMF.Gamma.GaussDigamma
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.AbelLimit

/-!
# Special values and extrema (DLMF §5.4)

`Γ(1) = 1` and `Γ(n+1) = n!` are Mathlib. `Γ(1/2) = √π` is Mathlib
`Gamma_one_half_eq`. `ψ(1) = -γ` and `ψ(1/2) = -γ - 2 log 2` are already
tagged in `Digamma` and `GaussDigamma`. Decimal expansions 5.4.7–5.4.10 are
not transcribed. The large-`n` extrema expansion 5.4.20 is deferred.
-/

@[expose] public section

open Complex
open scoped Real ComplexConjugate

noncomputable section

namespace DLMF.Gamma

/-- Double factorial via Gamma, even case. -/
@[dlmf 5.4.E2]
theorem doubleFactorial_even (n : ℕ) :
    ((2 * n).doubleFactorial : ℂ) =
      (2 : ℂ) ^ n * Complex.Gamma (n + 1) := by
  simp [Nat.doubleFactorial_two_mul, Complex.Gamma_nat_eq_factorial]

@[dlmf 5.4.E2]
theorem doubleFactorial_odd (n : ℕ) :
    ((2 * n + 1).doubleFactorial : ℂ) =
      (π : ℂ) ^ (-(1 / 2 : ℂ)) * (2 : ℂ) ^ ((2 * n + 1 : ℂ) / 2 + 1 / 2) *
        Complex.Gamma ((2 * n + 1 : ℂ) / 2 + 1) := by
  have hexp : ((2 * n + 1 : ℂ) / 2 + 1 / 2) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  have harg : ((2 * n + 1 : ℂ) / 2 + 1) = ((((n + 1 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (2 * (n + 1) - 1 : ℕ) = 2 * n + 1 := by omega
  rw [hexp, harg, cpow_natCast, Complex.Gamma_ofReal, Real.Gamma_nat_add_half, h2]
  have hsqrt : ((Real.sqrt π : ℝ) : ℂ) = (π : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]; push_cast; rfl
  have hpi : (π : ℂ) ^ (-(1 / 2 : ℂ)) * (π : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr Real.pi_ne_zero)]; simp
  rw [ofReal_div, ofReal_mul, ofReal_pow, ofReal_natCast, ofReal_ofNat, hsqrt]
  have h2ne : (2 : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  linear_combination (-((2 * n + 1).doubleFactorial : ℂ)) * hpi

/-- `Γ(z) Γ(z̄) = |Γ(z)|²`. -/
theorem Gamma_mul_Gamma_conj (z : ℂ) :
    Complex.Gamma z * Complex.Gamma (conj z) = (‖Complex.Gamma z‖ : ℂ) ^ 2 := by
  rw [Complex.Gamma_conj, mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]

@[dlmf 5.4.E3]
theorem norm_Gamma_mul_I (y : ℝ) (hy : y ≠ 0) :
    ‖Complex.Gamma (I * y)‖ = Real.sqrt (π / (y * Real.sinh (π * y))) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hz : I * (y : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hy'
  have hconj : conj (I * (y : ℂ)) = -(I * y) := by simp [neg_mul]
  have hnorm : Complex.Gamma (I * y) * Complex.Gamma (-(I * y)) =
      ‖Complex.Gamma (I * y)‖ ^ 2 := by
    rw [← hconj]; exact Gamma_mul_Gamma_conj _
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (I * y)
  have h1 : Complex.Gamma (1 - I * y) = -(I * y) * Complex.Gamma (-(I * y)) := by
    have := Complex.Gamma_add_one (-(I * y)) (neg_ne_zero.mpr hz)
    rw [← this]; ring_nf
  have hsin : sin (π * (I * y)) = I * Real.sinh (π * y) := by
    have hsplit : (π : ℂ) * (I * y) = (0 : ℂ) + ((π * y : ℝ) : ℂ) * I := by push_cast; ring
    rw [hsplit, sin_add_mul_I]
    simp only [Complex.sin_zero, Complex.cos_zero, ← ofReal_sinh]
    ring
  have hsinh : (Real.sinh (π * y) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  rw [h1, hsin, eq_div_iff (mul_ne_zero I_ne_zero hsinh)] at hrefl
  have hsq : (‖Complex.Gamma (I * y)‖ ^ 2 : ℂ) = ((π / (y * Real.sinh (π * y)) : ℝ) : ℂ) := by
    rw [← hnorm, ofReal_div, ofReal_mul, eq_div_iff (mul_ne_zero hy' hsinh)]
    linear_combination hrefl +
      Complex.Gamma (I * y) * Complex.Gamma (-(I * y)) * Real.sinh (π * y) * y * I_sq
  have hsq' : ‖Complex.Gamma (I * y)‖ ^ 2 = π / (y * Real.sinh (π * y)) := by exact_mod_cast hsq
  rw [← hsq', Real.sqrt_sq (norm_nonneg _)]

@[dlmf 5.4.E4]
theorem Gamma_half_add_mul_I (y : ℝ) :
    Complex.Gamma (1 / 2 + I * y) * Complex.Gamma (1 / 2 - I * y) =
      ‖Complex.Gamma (1 / 2 + I * y)‖ ^ 2 ∧
    ‖Complex.Gamma (1 / 2 + I * y)‖ ^ 2 = π / Real.cosh (π * y) := by
  let z : ℂ := 1 / 2 + I * y
  have hstar : star z = 1 / 2 - I * y := by
    simp [z, star_add, star_mul]
    ring
  have harg : (1 : ℂ) - z = 1 / 2 - I * y := by
    simp [z]
    ring
  have hprod :
      Complex.Gamma z * Complex.Gamma (1 / 2 - I * y) = π / sin (π * z) := by
    simpa [harg] using Complex.Gamma_mul_Gamma_one_sub z
  have hnorm :
      Complex.Gamma z * Complex.Gamma (1 / 2 - I * y) =
        ‖Complex.Gamma z‖ ^ 2 := by
    rw [← hstar]; exact Gamma_mul_Gamma_conj z
  have hsin : sin (π * z) = Real.cosh (π * y) := by
    have hsplit : (π : ℂ) * z = (π / 2 : ℂ) + (↑(π * y) : ℂ) * I := by
      simp [z, mul_add]
      ring
    rw [hsplit, sin_add_mul_I]
    simp [Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.ofReal_cosh]
  refine ⟨hnorm, ?_⟩
  have hℂ : (‖Complex.Gamma z‖ ^ 2 : ℂ) = (π / Real.cosh (π * y) : ℂ) := by
    calc
      (‖Complex.Gamma z‖ ^ 2 : ℂ) =
          Complex.Gamma z * Complex.Gamma (1 / 2 - I * y) := hnorm.symm
      _ = π / sin (π * z) := hprod
      _ = π / Real.cosh (π * y) := by rw [hsin]
  exact_mod_cast hℂ

@[dlmf 5.4.E5]
theorem Gamma_quarter_mul_I (y : ℝ) :
    Complex.Gamma (1 / 4 + I * y) * Complex.Gamma (3 / 4 - I * y) =
      π * (Real.sqrt 2 : ℂ) / (Real.cosh (π * y) + I * Real.sinh (π * y)) := by
  have harg : (1 : ℂ) - (1 / 4 + I * y) = 3 / 4 - I * y := by ring
  rw [← harg, Complex.Gamma_mul_Gamma_one_sub]
  have hsplit : (π : ℂ) * (1 / 4 + I * y) = ((π / 4 : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hsplit, sin_add_mul_I, ← ofReal_sin, ← ofReal_cos, Real.sin_pi_div_four,
    Real.cos_pi_div_four, ← ofReal_cosh, ← ofReal_sinh]
  have hden : (Real.cosh (π * y) : ℂ) + I * Real.sinh (π * y) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re] at this
    linarith [Real.cosh_pos (π * y)]
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hsq : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hden' : ((Real.sqrt 2 : ℂ) / 2) * Real.cosh (π * y) +
      ((Real.sqrt 2 : ℂ) / 2) * Real.sinh (π * y) * I ≠ 0 := by
    have : ((Real.sqrt 2 : ℂ) / 2) * Real.cosh (π * y) +
        ((Real.sqrt 2 : ℂ) / 2) * Real.sinh (π * y) * I =
        (Real.sqrt 2 / 2) * (Real.cosh (π * y) + I * Real.sinh (π * y)) := by ring
    rw [this]
    exact mul_ne_zero (div_ne_zero hs2 two_ne_zero) hden
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [div_eq_div_iff hden' hden]
  linear_combination (-((π : ℂ) * (Real.cosh (π * y) + I * Real.sinh (π * y)) / 2)) * hsq

@[dlmf 5.4.E11]
theorem deriv_Gamma_one : deriv Complex.Gamma 1 = -Real.eulerMascheroniConstant := by
  exact Complex.hasDerivAt_Gamma_one.deriv

@[dlmf 5.4.E12]
theorem trigamma_one : Real.trigamma 1 = π ^ 2 / 6 := by
  rw [Real.trigamma_eq_tsum (by positivity : (0 : ℝ) < 1)]
  have hshift : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℝ) ^ 2)) (π ^ 2 / 6) := by
    have hiff :=
      hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (g := π ^ 2 / 6) 1
    simpa using (hiff.mpr hasSum_zeta_two)
  refine (tsum_congr fun n => ?_).trans hshift.tsum_eq
  simp [inv_pow, add_comm]

@[dlmf 5.4.E13]
theorem trigamma_one_div_two : Real.trigamma (1 / 2) = π ^ 2 / 2 := by
  rw [Real.trigamma_eq_tsum (by positivity : (0 : ℝ) < 1 / 2)]
  set f : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2 with hf
  have hall : HasSum f (π ^ 2 / 6) := hasSum_zeta_two
  have heven : HasSum (fun k : ℕ => f (2 * k)) (π ^ 2 / 24) := by
    have h := hall.mul_left (1 / 4)
    convert h using 1
    · funext k
      simp only [hf]
      push_cast
      ring
    · ring
  have hodd_s : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hall.summable.comp_injective
      ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  have hsum := heven.even_add_odd hodd_s.hasSum
  have hodd : ∑' k : ℕ, f (2 * k + 1) = π ^ 2 / 8 := by
    have := hall.unique hsum
    linarith
  have hterm : ∀ n : ℕ, ((1 / 2 : ℝ) + n)⁻¹ ^ 2 = 4 * f (2 * n + 1) := by
    intro n
    simp only [hf]
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, hodd]
  ring

@[dlmf 5.4.E15]
theorem digamma_nat_add_half (n : ℕ) (hn : 0 < n) :
    Real.digamma (n + 1 / 2) =
      -Real.eulerMascheroniConstant - 2 * Real.log 2 +
        2 * ∑ k ∈ Finset.range n, (1 / (2 * (k : ℝ) + 1)) := by
  have h := Real.digamma_add_nat (by norm_num : (0 : ℝ) < 1 / 2) n
  rw [add_comm (1 / 2 : ℝ), Real.digamma_one_div_two] at h
  rw [h, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  ring

/-- The digamma function commutes with complex conjugation. -/
theorem digamma_conj (s : ℂ) : Complex.digamma (conj s) = conj (Complex.digamma s) := by
  have hfun : (conj ∘ Complex.Gamma ∘ conj) = Complex.Gamma := by
    funext z
    simp [Function.comp_def, Complex.Gamma_conj]
  have hderiv : deriv Complex.Gamma (conj s) = conj (deriv Complex.Gamma s) := by
    have h := congrFun (deriv_conj_conj (f := Complex.Gamma)) s
    rw [hfun] at h
    simp only [Function.comp_def] at h
    rw [h, Complex.conj_conj]
  simp only [Complex.digamma_def, logDeriv_apply, hderiv, Complex.Gamma_conj, map_div₀]

theorem neg_I_mul_ofReal_im (r : ℝ) : (-I * (r : ℂ)).im = -r := by
  simp

theorem cot_pi_mul_I (y : ℝ) (hy : y ≠ 0) :
    cot ((π : ℂ) * (I * y)) = -I * (Real.cosh (π * y) / Real.sinh (π * y)) := by
  have hsplit : (π : ℂ) * (I * y) = (0 : ℂ) + ((π * y : ℝ) : ℂ) * I := by push_cast; ring
  have hsinh : (Real.sinh (π * y) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  have hc : cos ((π : ℂ) * (I * y)) = Real.cosh (π * y) := by
    rw [hsplit, cos_add_mul_I]
    simp only [Complex.sin_zero, Complex.cos_zero, ← ofReal_cosh, ← ofReal_sinh]
    ring
  have hs : sin ((π : ℂ) * (I * y)) = I * Real.sinh (π * y) := by
    rw [hsplit, sin_add_mul_I]
    simp only [Complex.sin_zero, Complex.cos_zero, ← ofReal_cosh, ← ofReal_sinh]
    ring
  rw [Complex.cot, hc, hs, div_eq_iff (mul_ne_zero I_ne_zero hsinh)]
  field_simp
  linear_combination (Real.cosh (π * y) : ℂ) * I_sq

@[dlmf 5.4.E16]
theorem digamma_mul_I_im (y : ℝ) (hy : y ≠ 0) :
    (Complex.digamma (I * y)).im =
      1 / (2 * y) + π / 2 * Real.cosh (π * y) / Real.sinh (π * y) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hint : ∀ n : ℤ, I * (y : ℂ) ≠ n := fun n h =>
    hy (by have := congrArg Complex.im h; simpa using this)
  have hneg : ∀ m : ℕ, -(I * (y : ℂ)) ≠ -(m : ℂ) := fun m h =>
    hy (by have := congrArg Complex.im h; simpa using this)
  have hconj : conj (I * (y : ℂ)) = -(I * y) := by simp [neg_mul]
  have h1 := Complex.digamma_one_sub hint
  have h2 := Complex.digamma_apply_add_one (-(I * (y : ℂ))) hneg
  rw [show -(I * (y : ℂ)) + 1 = 1 - I * y by ring] at h2
  have h3 : Complex.digamma (-(I * (y : ℂ))) = conj (Complex.digamma (I * y)) := by
    rw [← hconj, digamma_conj]
  have hcot := cot_pi_mul_I y hy
  have hinv : (-(I * (y : ℂ)))⁻¹ = I / y := by
    field_simp
    linear_combination (-1 : ℂ) * I_sq
  have hkey : conj (Complex.digamma (I * (y : ℂ))) - Complex.digamma (I * y) =
      -I * ((π * (Real.cosh (π * y) / Real.sinh (π * y)) + 1 / y : ℝ) : ℂ) := by
    rw [← h3]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one]
    linear_combination h1 - h2 + (π : ℂ) * hcot - hinv
  have him := congrArg Complex.im hkey
  rw [Complex.sub_im, Complex.conj_im, neg_I_mul_ofReal_im] at him
  have hsinh : Real.sinh (π * y) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  have hval : (Complex.digamma (I * y)).im =
      (π * (Real.cosh (π * y) / Real.sinh (π * y)) + 1 / y) / 2 := by linarith
  rw [hval]
  field_simp
  ring

@[dlmf 5.4.E17]
theorem digamma_half_add_mul_I_im (y : ℝ) :
    (Complex.digamma (1 / 2 + I * y)).im = π / 2 * Real.tanh (π * y) := by
  have hint : ∀ n : ℤ, (1 / 2 + I * (y : ℂ)) ≠ n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have h2 : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 : ℝ) * n = 1)
    omega
  have hconj : conj (1 / 2 + I * (y : ℂ)) = 1 - (1 / 2 + I * y) := by
    simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  have h1 := Complex.digamma_one_sub hint
  rw [← hconj, digamma_conj] at h1
  have hcot : cot ((π : ℂ) * (1 / 2 + I * y)) = -I * Real.tanh (π * y) := by
    have hsplit : (π : ℂ) * (1 / 2 + I * y) = ((π / 2 : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * I := by
      push_cast; ring
    have hcosh : (Real.cosh (π * y) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
    rw [Complex.cot, hsplit, sin_add_mul_I, cos_add_mul_I, ← ofReal_sin, ← ofReal_cos,
      Real.sin_pi_div_two, Real.cos_pi_div_two, ← ofReal_cosh, ← ofReal_sinh,
      Real.tanh_eq_sinh_div_cosh, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_zero]
    have hden : (1 : ℂ) * Real.cosh (π * y) + 0 * Real.sinh (π * y) * I ≠ 0 := by
      simpa using hcosh
    rw [div_eq_iff hden]
    field_simp
    ring
  have hkey : conj (Complex.digamma (1 / 2 + I * (y : ℂ))) - Complex.digamma (1 / 2 + I * y) =
      -I * ((π * Real.tanh (π * y) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
    linear_combination h1 + (π : ℂ) * hcot
  have him := congrArg Complex.im hkey
  rw [Complex.sub_im, Complex.conj_im, neg_I_mul_ofReal_im] at him
  linarith

@[dlmf 5.4.E18]
theorem digamma_one_add_mul_I_im (y : ℝ) (hy : y ≠ 0) :
    (Complex.digamma (1 + I * y)).im =
      -1 / (2 * y) + π / 2 * Real.cosh (π * y) / Real.sinh (π * y) := by
  have hneg : ∀ m : ℕ, I * (y : ℂ) ≠ -(m : ℂ) := fun m h =>
    hy (by have := congrArg Complex.im h; simpa using this)
  have h := Complex.digamma_apply_add_one (I * y) hneg
  rw [add_comm] at h
  rw [h, Complex.add_im, digamma_mul_I_im y hy]
  have hinv : (I * (y : ℂ))⁻¹ = -I * ((1 / y : ℝ) : ℂ) := by
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    rw [Complex.ofReal_div, Complex.ofReal_one]
    field_simp
    linear_combination I_sq
  rw [hinv, neg_I_mul_ofReal_im]
  ring

/-! ### Gauss's digamma theorem -/

section GaussDigammaTheorem

open Filter Topology Finset

/-- The primitive `q`-th root of unity `e^{2πi/q}`. -/
noncomputable def gaussRoot (q : ℕ) : ℂ := Complex.exp (2 * π * I / q)

theorem isPrimitiveRoot_gaussRoot {q : ℕ} (hq : q ≠ 0) : IsPrimitiveRoot (gaussRoot q) q :=
  Complex.isPrimitiveRoot_exp q hq

theorem norm_gaussRoot_pow (q k : ℕ) : ‖gaussRoot q ^ k‖ = 1 := by
  rw [norm_pow, gaussRoot, Complex.norm_exp]
  have : (2 * π * I / q : ℂ).re = 0 := by
    rw [show (2 * π * I / q : ℂ) = ((2 * π / q : ℝ) : ℂ) * I by push_cast; ring]
    simp
  simp [this]

theorem gaussRoot_pow_ne_one {q k : ℕ} (hk0 : 0 < k) (hkq : k < q) : gaussRoot q ^ k ≠ 1 := by
  rw [Ne, (isPrimitiveRoot_gaussRoot (by omega)).pow_eq_one_iff_dvd]
  exact Nat.not_dvd_of_pos_of_lt hk0 hkq

/-- Roots-of-unity filter. -/
theorem sum_gaussRoot_pow_mul {q : ℕ} (hq : q ≠ 0) (j : ℕ) :
    ∑ k ∈ range q, gaussRoot q ^ (k * j) = if q ∣ j then (q : ℂ) else 0 := by
  have hprim := isPrimitiveRoot_gaussRoot hq
  simp_rw [mul_comm _ j, pow_mul]
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    simp [pow_mul, hprim.pow_eq_one]
  · have hne : gaussRoot q ^ j ≠ 1 := by rwa [Ne, hprim.pow_eq_one_iff_dvd]
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow, sub_self,
      zero_div]

/-- One block of `q` consecutive terms of the filtered harmonic sum. -/
theorem sum_gaussRoot_block {q p : ℕ} (hp : 0 < p) (hpq : p < q) (n : ℕ) :
    ∑ r ∈ range q, (1 / ((q * n + r : ℕ) + 1 : ℂ)) *
        ∑ k ∈ range q, gaussRoot q ^ (k * (q * n + r + 1 + (q - p))) =
      q / (q * n + p) := by
  have hq : q ≠ 0 := by omega
  simp_rw [sum_gaussRoot_pow_mul hq]
  have hcond : ∀ r ∈ range q, (q ∣ q * n + r + 1 + (q - p) ↔ r = p - 1) := by
    intro r hr
    rw [mem_range] at hr
    constructor
    · intro h
      have h2 : q ∣ r + 1 + (q - p) := by
        have : q * n + r + 1 + (q - p) = q * n + (r + 1 + (q - p)) := by ring
        rw [this] at h
        exact (Nat.dvd_add_right (dvd_mul_right q n)).mp h
      obtain ⟨c, hc⟩ := h2
      have hc1 : c = 1 := by
        rcases c with _ | _ | c
        · omega
        · rfl
        · have : r + 1 + (q - p) < 2 * q := by omega
          nlinarith
      subst hc1
      omega
    · rintro rfl
      have : q * n + (p - 1) + 1 + (q - p) = q * (n + 1) := by
        rw [Nat.mul_succ]; omega
      rw [this]
      exact dvd_mul_right q _
  rw [Finset.sum_congr rfl fun r hr => by rw [if_congr (hcond r hr) rfl rfl]]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (range q) (p - 1)]
  have hmem : p - 1 ∈ range q := mem_range.mpr (by omega)
  simp only [hmem, ite_true]
  have : ((q * n + (p - 1) : ℕ) : ℂ) + 1 = q * n + p := by
    have : q * n + (p - 1) + 1 = q * n + p := by omega
    exact_mod_cast this
  rw [this]
  ring

/-- The filtered harmonic sum over `[1, qN]` collapses to `∑ q/(qn+p)`. -/
theorem sum_gaussRoot_filtered {q p : ℕ} (hp : 0 < p) (hpq : p < q) (N : ℕ) :
    ∑ m ∈ range (q * N), (1 / ((m : ℕ) + 1 : ℂ)) *
        ∑ k ∈ range q, gaussRoot q ^ (k * (m + 1 + (q - p))) =
      ∑ n ∈ range N, (q : ℂ) / (q * n + p) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ, ← sum_gaussRoot_block hp hpq N]

/-- The roots-of-unity decomposition of `∑_{n<N} q/(qn+p)`. -/
theorem sum_gaussRoot_filtered_eq {q p : ℕ} (hp : 0 < p) (hpq : p < q) (N : ℕ) :
    ∑ n ∈ range N, (q : ℂ) / (q * n + p) =
      ∑ k ∈ range q, gaussRoot q ^ (k * (q - p)) *
        ∑ m ∈ range (q * N), (gaussRoot q ^ k) ^ (m + 1) / ((m : ℂ) + 1) := by
  rw [← sum_gaussRoot_filtered hp hpq N]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun m _ => ?_
  rw [← pow_mul, show k * (m + 1 + (q - p)) = k * (q - p) + k * (m + 1) by ring, pow_add]
  ring
theorem re_lt_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : z.re < 1 := by
  rcases (Complex.re_le_norm z).lt_or_eq with h | h
  · linarith
  · exfalso
    have him : z.im = 0 := by
      have h2 := Complex.sq_norm z
      rw [Complex.normSq_apply, hz] at h2
      rw [hz] at h
      rw [h] at h2
      nlinarith [sq_nonneg z.im]
    exact hz1 (Complex.ext (by rw [h, hz]; simp) (by simp [him]))

/-- `∑ zᵐ/m = -log(1-z)` on the unit circle away from `1` (Dirichlet test plus Abel's
theorem). -/
theorem tendsto_sum_pow_div_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun M : ℕ => ∑ m ∈ range M, z ^ (m + 1) / (m + 1)) atTop
      (𝓝 (-Complex.log (1 - z))) := by
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hb : ∀ n, ‖∑ i ∈ range n, z ^ (i + 1)‖ ≤ 2 / ‖1 - z‖ := by
    intro n
    have : ∑ i ∈ range n, z ^ (i + 1) = z * (1 - z ^ n) / (1 - z) := by
      simp_rw [pow_succ', ← mul_sum]
      rw [mul_div_assoc]
      congr 1
      rw [eq_div_iff h1z, ← neg_sub, mul_neg, geom_sum_mul]
      ring
    rw [this, norm_div, norm_mul, hz, one_mul]
    gcongr
    calc ‖1 - z ^ n‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ n‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  have ha : Antitone fun i : ℕ => ((i : ℝ) + 1)⁻¹ := fun i j hij => by
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    simp only
    gcongr
  have h0 : Tendsto (fun i : ℕ => ((i : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hc := ha.cauchySeq_series_mul_of_tendsto_zero_of_bounded h0 hb
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hc
  have hterm : ∀ i : ℕ, ((i : ℝ) + 1)⁻¹ • z ^ (i + 1) = z ^ (i + 1) / ((i : ℂ) + 1) := by
    intro i
    rw [Complex.real_smul, div_eq_inv_mul]
    push_cast
    ring
  simp_rw [hterm] at hℓ
  suffices hl : ℓ = -Complex.log (1 - z) by rwa [hl] at hℓ
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hℓ
  -- the power series equals `-log (1 - z r) / r` for `0 < r < 1`
  have hg : Tendsto (fun r : ℂ => -Complex.log (1 - z * r) / r)
      ((𝓝[<] (1 : ℝ)).map ofReal) (𝓝 (-Complex.log (1 - z))) := by
    have hslit : 1 - z ∈ slitPlane := by
      left
      simp only [sub_re, one_re]
      linarith [re_lt_one_of_norm_eq_one hz hz1]
    have hcont : ContinuousAt (fun r : ℂ => -Complex.log (1 - z * r) / r) 1 := by
      refine ContinuousAt.div ?_ continuousAt_id one_ne_zero
      refine ContinuousAt.neg ?_
      refine ContinuousAt.clog ?_ (by simpa using hslit)
      fun_prop
    have hmap : (𝓝[<] (1 : ℝ)).map ofReal ≤ 𝓝 (1 : ℂ) := by
      refine (tendsto_nhdsWithin_of_tendsto_nhds ?_)
      simpa using (Complex.continuous_ofReal.tendsto 1)
    simpa using hcont.tendsto.mono_left hmap
  refine tendsto_nhds_unique (habel.congr' ?_) hg
  rw [Filter.EventuallyEq, Filter.eventually_map]
  have : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r := by
    exact eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds one_pos)
  filter_upwards [this, self_mem_nhdsWithin] with r hr hr1
  have hr1' : r < 1 := hr1
  have hzr : ‖z * r‖ < 1 := by
    rw [norm_mul, hz, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact hr1'
  have hs := Complex.hasSum_taylorSeries_neg_log' hzr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [← hs.tsum_eq, eq_div_iff hr0, ← tsum_mul_right]
  congr 1
  funext n
  rw [mul_pow, pow_succ (r : ℂ)]
  field_simp

/-- `H_N - H_{qN} → -log q`. -/
theorem tendsto_harmonic_sub_harmonic_mul {q : ℕ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) - harmonic (q * N)) atTop (𝓝 (-Real.log q)) := by
  have hqN : Tendsto (fun N : ℕ => q * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hq) tendsto_id
  have h := Real.tendsto_harmonic_sub_log.sub (Real.tendsto_harmonic_sub_log.comp hqN)
  have h2 := h.sub_const (Real.log q)
  rw [sub_self, zero_sub] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [Function.comp_apply, Nat.cast_mul, Real.log_mul hq0 hN0]
  ring

/-- Complex form of Gauss's digamma theorem:
`ψ(p/q) + γ = -log q + ∑_{k=1}^{q-1} ω^{-kp} log(1 - ωᵏ)`, `ω = e^{2πi/q}`. -/
theorem digamma_rat_complex (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    ((Real.digamma (p / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) =
      -(Real.log q : ℂ) + ∑ k ∈ Icc 1 (q - 1),
        gaussRoot q ^ (k * (q - p)) * Complex.log (1 - gaussRoot q ^ k) := by
  have hq : 0 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set x : ℝ := p / q with hxdef
  have hx : 0 < x := div_pos hp0 hq0
  set ω := gaussRoot q
  let S : ℕ → ℕ → ℂ := fun k M => ∑ m ∈ range M, (ω ^ k) ^ (m + 1) / ((m : ℂ) + 1)
  have hI : Icc 1 (q - 1) = Ico 1 q := by ext k; simp; omega
  -- the partial sums
  let T : ℕ → ℂ := fun N => ((∑ n ∈ range N, Real.digammaSeriesTerm x n : ℝ) : ℂ)
  have hT1 : Tendsto T atTop (𝓝 ((Real.digamma x + Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
    have hs := (Real.summable_digammaSeriesTerm hx).hasSum.tendsto_sum_nat
    have : Real.digamma x + Real.eulerMascheroniConstant = ∑' n, Real.digammaSeriesTerm x n := by
      rw [Real.digamma_eq_tsum hx]; ring
    rw [this]
    exact (Complex.continuous_ofReal.tendsto _).comp hs
  have hTeq : ∀ N, T N = ((harmonic N : ℝ) - harmonic (q * N) : ℝ) -
      ∑ k ∈ Icc 1 (q - 1), ω ^ (k * (q - p)) * S k (q * N) := by
    intro N
    have hsplit : ∑ n ∈ range N, (q : ℂ) / (q * n + p) =
        (harmonic (q * N) : ℝ) + ∑ k ∈ Icc 1 (q - 1), ω ^ (k * (q - p)) * S k (q * N) := by
      rw [sum_gaussRoot_filtered_eq hp hpq N, hI, sum_Ico_eq_sum_range,
        show q = q - 1 + 1 by omega, sum_range_succ']
      rw [show q - 1 + 1 = q by omega]
      rw [add_comm]
      congr 1
      · simp [harmonic]
      · refine sum_congr rfl fun k _ => ?_
        rw [add_comm 1 k]
    have key : T N = ((harmonic N : ℝ) : ℂ) - ∑ n ∈ range N, (q : ℂ) / (q * n + p) := by
      simp only [T]
      push_cast [Real.digammaSeriesTerm, harmonic]
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun n _ => ?_
      simp only [hxdef]
      push_cast
      have : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
      have h2 : (q * n + p : ℂ) ≠ 0 := by exact_mod_cast (show q * n + p ≠ 0 by omega)
      field_simp
      ring
    rw [key, hsplit]
    push_cast
    ring
  have hT2 : Tendsto T atTop (𝓝 ((-Real.log q : ℝ) -
      ∑ k ∈ Icc 1 (q - 1), ω ^ (k * (q - p)) * (-Complex.log (1 - ω ^ k)))) := by
    rw [show T = fun N => T N from rfl]
    simp_rw [hTeq]
    refine Tendsto.sub ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_harmonic_sub_harmonic_mul hq)) ?_
    refine tendsto_finsetSum _ fun k hk => Tendsto.const_mul _ ?_
    rw [mem_Icc] at hk
    have hqN : Tendsto (fun N : ℕ => q * N) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hq) tendsto_id
    exact (tendsto_sum_pow_div_of_norm_eq_one (norm_gaussRoot_pow q k)
      (gaussRoot_pow_ne_one (by omega) (by omega))).comp hqN
  rw [tendsto_nhds_unique hT1 hT2]
  push_cast
  simp only [mul_neg, sum_neg_distrib, sub_neg_eq_add]

theorem gaussRoot_pow_eq (q n : ℕ) :
    gaussRoot q ^ n = Complex.exp (((2 * π * n / q : ℝ) : ℂ) * I) := by
  rw [gaussRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem gaussRoot_pow_add_pow {p q : ℕ} (hq : 0 < q) (hpq : p ≤ q) (k : ℕ) :
    gaussRoot q ^ (k * (q - p)) + gaussRoot q ^ (k * p) =
      ((2 * Real.cos (2 * π * k * p / q) : ℝ) : ℂ) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have h1 : gaussRoot q ^ (k * (q - p)) =
      Complex.exp (-((2 * π * k * p / q : ℝ) : ℂ) * I) := by
    rw [gaussRoot, ← Complex.exp_nat_mul]
    have : ((k * (q - p) : ℕ) : ℂ) * (2 * π * I / q) =
        k * (2 * π * I) + -((2 * π * k * p / q : ℝ) : ℂ) * I := by
      rw [Nat.cast_mul, Nat.cast_sub hpq]
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul]
  have h2 : gaussRoot q ^ (k * p) = Complex.exp (((2 * π * k * p / q : ℝ) : ℂ) * I) := by
    rw [gaussRoot_pow_eq]
    push_cast
    ring_nf
  rw [h1, h2, add_comm, Complex.ofReal_mul, Complex.ofReal_cos, ← Complex.two_cos]
  push_cast
  ring

theorem log_one_sub_gaussRoot_pow_re (q k : ℕ) :
    (Complex.log (1 - gaussRoot q ^ k)).re =
      (1 / 2) * Real.log (2 - 2 * Real.cos (2 * π * k / q)) := by
  rw [Complex.log_re, gaussRoot_pow_eq]
  set θ : ℝ := 2 * π * k / q
  have hn : ‖1 - Complex.exp (θ * I)‖ ^ 2 = 2 - 2 * Real.cos θ := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [← hn, Real.log_pow]
  push_cast
  ring

@[dlmf 5.4.E19]
theorem digamma_rat (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    Real.digamma (p / q) =
      -Real.eulerMascheroniConstant - Real.log q -
        π / 2 * Real.cot (π * p / q) +
        (1 / 2) * ∑ k ∈ Finset.Icc 1 (q - 1),
          Real.cos (2 * π * k * p / q) *
            Real.log (2 - 2 * Real.cos (2 * π * k / q)) := by
  have hq : 0 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 := digamma_rat_complex p q hp hpq
  have h2 := digamma_rat_complex (q - p) q (by omega) (by omega)
  have hx : ((q - p : ℕ) : ℝ) / q = 1 - p / q := by
    rw [Nat.cast_sub hpq.le]; field_simp
  rw [hx, show q - (q - p) = p by omega] at h2
  have hsum := congrArg Complex.re (congrArg₂ (· + ·) h1 h2)
  rw [add_add_add_comm, ← sum_add_distrib] at hsum
  simp_rw [← add_mul, gaussRoot_pow_add_pow hq hpq.le] at hsum
  simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.re_sum,
    Complex.re_ofReal_mul, log_one_sub_gaussRoot_pow_re] at hsum
  have hrefl := Real.digamma_one_sub (x := p / q) (div_pos (by exact_mod_cast hp) hq0)
    ((div_lt_one hq0).mpr (by exact_mod_cast hpq))
  have hcot : π * (p / q : ℝ) = π * p / q := by ring
  rw [hcot] at hrefl
  have hs : ∑ k ∈ Icc 1 (q - 1), 2 * Real.cos (2 * π * k * p / q) *
      ((1 / 2) * Real.log (2 - 2 * Real.cos (2 * π * k / q))) =
      ∑ k ∈ Icc 1 (q - 1), Real.cos (2 * π * k * p / q) *
        Real.log (2 - 2 * Real.cos (2 * π * k / q)) :=
    sum_congr rfl fun k _ => by ring
  rw [hs] at hsum
  linarith

end GaussDigammaTheorem

end DLMF.Gamma
