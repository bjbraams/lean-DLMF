/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.RadialSeries
public import DLMF.Mathieu.FourierSeries
public import DLMF.Bessel.Modified

/-!
# Modified Mathieu functions at imaginary `h` (DLMF 28.24.6–28.24.13)

Proofs of the cross-product expansions DLMF 28.24.6–28.24.13 of `Ie_n`, `Io_n`, `Ke_n`, `Ko_n`
in modified Bessel functions, obtained from the cross-product series at imaginary `h`. The
continued `J_μ(ih e^z)` is expressed through `I_μ(h e^z)` (using `I_k(w) = i^{-k} J_k(iw)` for
integer `k`), and the continued `H^{(1)}_μ(ih e^z)` through `K_μ(h e^z)` for `|Im z| < π`
(DLMF 10.27.8, continued in `z`).

## Main results

* `cpow_ofReal_mul_exp`: `(r e^z)^μ = r^μ e^{μz}` for `r > 0`, `-π < Im z ≤ π`.
* `hasSum_modMathieuIe_even'`, `hasSum_modMathieuIo_even'`, `hasSum_modMathieuIe_odd'`,
  `hasSum_modMathieuIo_odd'`: DLMF 28.24.6–28.24.9.
* `hasSum_modMathieuKe_even'`, `hasSum_modMathieuKo_even'`, `hasSum_modMathieuKe_odd'`,
  `hasSum_modMathieuKo_odd'`: DLMF 28.24.10–28.24.13.
-/

@[expose] public noncomputable section

open Complex hiding besselI
open Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-- `(r e^z)^μ = r^μ e^{μz}` for `r > 0` and `-π < Im z ≤ π` (principal powers). -/
theorem cpow_ofReal_mul_exp (μ : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz₁ : -π < z.im)
    (hz₂ : z.im ≤ π) : ((r : ℂ) * Complex.exp z) ^ μ = (r : ℂ) ^ μ * Complex.exp (μ * z) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr' (Complex.exp_ne_zero z)),
    Complex.cpow_def_of_ne_zero hr', Complex.log_ofReal_mul hr (Complex.exp_ne_zero z),
    Complex.log_exp hz₁ hz₂, ← Complex.exp_add, Complex.ofReal_log hr.le]
  ring_nf

open DLMF.Bessel in
/-- `I_k(w) = i^{-k} J_k(iw)` for integer `k` and every `w` (DLMF 10.27.6). -/
private lemma besselI_intCast_eq_I_zpow_mul_besselJ (k : ℤ) (w : ℂ) :
    besselI k w = I ^ (-k) * besselJ k (I * w) := by
  rw [besselI, besselJ_eq_regularized, cpow_intCast, cpow_intCast,
    show I * w / 2 = I * (w / 2) by ring, mul_zpow, show -((I * w) ^ 2 / 4) = w ^ 2 / 4 by
      rw [mul_pow, I_sq]; ring, zpow_neg]
  field_simp

open DLMF.Bessel in
/-- `J_k(ih e^w) = i^k I_k(h e^w)` for the continued Bessel function of integer order. -/
private lemma besselJExp_intCast_I_mul (k : ℤ) (h w : ℂ) :
    besselJExp k (I * h) w = I ^ k * besselI k (h * Complex.exp w) := by
  rw [besselJExp_intCast, besselI_intCast_eq_I_zpow_mul_besselJ, ← mul_assoc, ← zpow_add₀ I_ne_zero,
    add_neg_cancel, zpow_zero, one_mul, mul_assoc]

open DLMF.Bessel in
/-- `J_μ(ih e^z) = e^{iμπ/2} I_μ(h e^z)` (continued in `z`, principal `I_μ`) for `h > 0` and
`-π < Im z ≤ π`. -/
private lemma besselJExp_I_mul_ofReal (μ : ℂ) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz₁ : -π < z.im)
    (hz₂ : z.im ≤ π) :
    besselJExp μ (I * h) z = Complex.exp (I * μ * π / 2) * besselI μ (h * Complex.exp z) := by
  have h2 : (0 : ℝ) < h / 2 := by positivity
  have hI : I * (h : ℂ) / 2 = ((h / 2 : ℝ) : ℂ) * Complex.exp ((π / 2 : ℝ) * I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]; push_cast; ring
  have hc1 := cpow_ofReal_mul_exp μ h2 (z := (π / 2 : ℝ) * I)
    (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])
  have hc2 := cpow_ofReal_mul_exp μ h2 hz₁ hz₂
  have harg : -(((I * h : ℂ) * Complex.exp z) ^ 2 / 4) = ((h : ℂ) * Complex.exp z) ^ 2 / 4 := by
    rw [mul_pow, mul_pow, I_sq]; ring
  rw [besselJExp, besselI, hI, hc1, harg, show (h : ℂ) * Complex.exp z / 2 =
    ((h / 2 : ℝ) : ℂ) * Complex.exp z by push_cast; ring, hc2,
    show (μ : ℂ) * ((π / 2 : ℝ) * I) = I * μ * π / 2 by push_cast; ring]
  ring

/-- `h e^z` lies in the slit plane for `h > 0` and `|Im z| < π`. -/
private lemma ofReal_mul_exp_mem_slitPlane_of_abs_im_lt {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : |z.im| < π) :
    (h : ℂ) * Complex.exp z ∈ slitPlane := by
  rw [show (h : ℂ) * Complex.exp z = Complex.exp ((Real.log h : ℂ) + z) by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hh]]
  rw [Complex.exp_mem_slitPlane]
  have h1 := (abs_lt.mp hz)
  have him : ((Real.log h : ℂ) + z).im = z.im := by simp
  rw [him, (toIocMod_eq_self _).mpr ⟨h1.1, by linarith⟩]
  exact h1.2.ne

open DLMF.Bessel in
/-- `H^{(1)}_μ(ih e^z) = (2/(πi)) e^{-iμπ/2} K_μ(h e^z)` (DLMF 10.27.8), with `H^{(1)}` continued
in `z` (`mathieuCylExp 3`), for `h > 0`, `|Im z| < π` and every order `μ`. -/
private lemma mathieuCylExp_three_I_mul_ofReal (μ : ℂ) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : |z.im| < π) :
    mathieuCylExp 3 μ (I * h) z =
      2 / (π * I) * Complex.exp (-(I * μ * π / 2)) * besselK μ (h * Complex.exp z) := by
  have hs := ofReal_mul_exp_mem_slitPlane_of_abs_im_lt hh hz
  have hIh : I * (h : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hh.ne')
  have h1 := abs_lt.mp hz
  refine Complex.eq_of_continuousAt_of_integerComplement
    (f := fun μ => mathieuCylExp 3 μ (I * h) z)
    (g := fun μ => 2 / (π * I) * Complex.exp (-(I * μ * π / 2)) * besselK μ (h * Complex.exp z))
    ?_ ?_ ?_
  · simp only [mathieuCylExp]
    exact (differentiable_besselJExp_order hIh z μ).continuousAt.add
      (continuousAt_const.mul (continuousAt_besselYExp_order hIh z μ))
  · exact (continuousAt_const.mul (by fun_prop)).mul
      (continuousAt_besselK_order (fun μ => μ) continuous_id μ hs)
  · intro c hc
    have hc' := Complex.forall_of_mem_integerComplement hc
    have hsin := DLMF.Bessel.sin_mul_pi_ne_zero hc'
    simp only [mathieuCylExp]
    rw [besselYExp_of_not_exists_int (fun ⟨k, hk⟩ => hc' k hk), besselJExp_I_mul_ofReal c hh h1.1 h1.2.le,
      besselJExp_I_mul_ofReal (-c) hh h1.1 h1.2.le, besselK_eq_of_not_int hc', besselE]
    set E := Complex.exp (I * c * π / 2) with hE
    have hE0 : E ≠ 0 := Complex.exp_ne_zero _
    have hEn : Complex.exp (I * (-c) * π / 2) = E⁻¹ := by
      rw [hE, ← Complex.exp_neg]; ring_nf
    have hEn' : Complex.exp (-(I * c * π / 2)) = E⁻¹ := by
      rw [hE, ← Complex.exp_neg]
    have hcos : Complex.cos (c * π) = (E ^ 2 + E⁻¹ ^ 2) / 2 := by
      rw [Complex.cos, hE, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
      ring_nf
    have hsin' : Complex.sin (c * π) = (E ^ 2 - E⁻¹ ^ 2) * I / 2 * (-1) := by
      rw [Complex.sin, hE, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
      ring_nf
    rw [hEn, hEn', hcos] at *
    rw [hsin'] at hsin ⊢
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hE4 : E ^ 4 - 1 ≠ 0 := by
      intro h0
      apply hsin
      have : E ^ 2 - E⁻¹ ^ 2 = (E ^ 4 - 1) / E ^ 2 := by field_simp
      rw [this, h0]; ring
    field_simp
    rw [I_sq]
    field_simp
    ring

/-- `i^{a-b} = i^a (i^b)⁻¹` for natural `a, b`. -/
private lemma I_zpow_natCast_sub (a b : ℕ) : I ^ ((a : ℤ) - b) = I ^ a * (I ^ b)⁻¹ := by
  rw [zpow_sub₀ I_ne_zero, zpow_natCast, zpow_natCast, div_eq_mul_inv]

/-- `i^{a+b} = i^a i^b` for natural `a, b`. -/
private lemma I_zpow_natCast_add (a b : ℕ) : I ^ ((a : ℤ) + b) = I ^ a * I ^ b := by
  rw [zpow_add₀ I_ne_zero, zpow_natCast, zpow_natCast]

/-- `i^{-2m} = ((-1)^m)⁻¹`. -/
private lemma I_zpow_neg_natCast_two_mul_eq_inv (m : ℕ) : I ^ (-((2 * m : ℕ) : ℤ)) = ((-1 : ℂ) ^ m)⁻¹ := by
  rw [zpow_neg, zpow_natCast, pow_mul, I_sq]

/-- `(i^a)² = (-1)^a`. -/
private lemma I_pow_sq_eq_neg_one_pow (a : ℕ) : (I ^ a) ^ 2 = (-1 : ℂ) ^ a := by
  rw [← pow_mul, mul_comm, pow_mul, I_sq]

/-- `((-1)^a)² = 1`. -/
private lemma neg_one_pow_sq_eq_one (a : ℕ) : ((-1 : ℂ) ^ a) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]; simp

open DLMF.Bessel in
/-- DLMF 28.24.6. -/
theorem hasSum_modMathieuIe_even' (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hA : mathieuFourierA (2 * m) (2 * s) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ s * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) / mathieuFourierA (2 * m) (2 * s) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselI ((ℓ + s : ℕ) : ℂ) (h * Complex.exp z) +
          besselI ((ℓ + s : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z))))
      (mathieuEpsilon s * modMathieuIe (2 * m) z h) := by
  have hIh : I * (h : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hh.ne')
  have hq : (I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; push_cast; ring
  have hA' : mathieuFourierA (2 * m) (2 * s) (-(h ^ 2)) ≠ 0 := by
    rw [mathieuFourierA_even_neg_q]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hA
  have G := (hasSum_radialMathieuMc_even_cross_of_sq_eq 1 le_rfl (by norm_num) m s hq hIh hA'
    z).mul_left (I ^ (-((2 * m : ℕ) : ℤ)))
  convert G using 1
  · funext ℓ
    simp only [mathieuCylExp]
    rw [show ((ℓ + s : ℕ) : ℂ) = (((ℓ : ℤ) + s : ℤ) : ℂ) by push_cast; ring,
      besselJExp_intCast_I_mul, besselJExp_intCast_I_mul, besselJExp_intCast_I_mul,
      besselJExp_intCast_I_mul, mathieuFourierA_even_neg_q, mathieuFourierA_even_neg_q,
      I_zpow_natCast_sub, I_zpow_natCast_add, I_zpow_neg_natCast_two_mul_eq_inv, neg_one_zpow_natCast_sub,
      neg_one_zpow_natCast_sub]
    have h1 := I_pow_sq_eq_neg_one_pow ℓ
    have h2 := I_pow_sq_eq_neg_one_pow s
    have h3 := neg_one_pow_sq_eq_one ℓ
    have h4 := neg_one_pow_sq_eq_one s
    have h5 := neg_one_pow_sq_eq_one m
    have hs0 : (-1 : ℂ) ^ s ≠ 0 := by simp
    have hm0 : (-1 : ℂ) ^ m ≠ 0 := by simp
    have hIs : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    rw [h1, h4]
    linear_combination (-(mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) *
      (besselI (((ℓ : ℤ) - s : ℤ) : ℂ) (h * Complex.exp (-z)) *
          besselI (((ℓ : ℤ) + s : ℤ) : ℂ) (h * Complex.exp z) +
        besselI (((ℓ : ℤ) + s : ℤ) : ℂ) (h * Complex.exp (-z)) *
          besselI (((ℓ : ℤ) - s : ℤ) : ℂ) (h * Complex.exp z)))) * h3
  · simp only [modMathieuIe, radialMathieuMc]; push_cast; ring

/-- `i^{-n} = (i^n)⁻¹`. -/
private lemma I_zpow_neg_natCast (n : ℕ) : I ^ (-(n : ℤ)) = (I ^ n)⁻¹ := by
  rw [zpow_neg, zpow_natCast]

/-- `i^{2m+1} = (-1)^m i`. -/
private lemma I_pow_two_mul_add_one (m : ℕ) : I ^ (2 * m + 1) = (-1 : ℂ) ^ m * I := by
  rw [pow_succ, pow_mul, I_sq]

/-- `i^{2m+2} = -(-1)^m`. -/
private lemma I_pow_two_mul_add_two (m : ℕ) : I ^ (2 * m + 2) = -(-1 : ℂ) ^ m := by
  rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, I_sq, pow_succ]; ring

open DLMF.Bessel in
/-- DLMF 28.24.7. -/
theorem hasSum_modMathieuIo_even' (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hB : mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ s * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) /
          mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselI ((ℓ + s + 2 : ℕ) : ℂ) (h * Complex.exp z) -
          besselI ((ℓ + s + 2 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z))))
      (modMathieuIo (2 * m + 2) z h) := by
  have hIh : I * (h : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hh.ne')
  have hq : (I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; push_cast; ring
  have hB' : mathieuFourierB (2 * m + 2) (2 * s + 2) (-(h ^ 2)) ≠ 0 := by
    rw [mathieuFourierB_even_neg_q]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hB
  have G := (hasSum_radialMathieuMs_even_cross_of_sq_eq 1 le_rfl (by norm_num) m s hq hIh hB'
    z).mul_left (I ^ (-((2 * m + 2 : ℕ) : ℤ)))
  convert G using 1
  · funext ℓ
    simp only [mathieuCylExp]
    rw [show ((ℓ + s + 2 : ℕ) : ℂ) = (((ℓ + s + 2 : ℕ) : ℤ) : ℂ) by push_cast; ring,
      besselJExp_intCast_I_mul, besselJExp_intCast_I_mul, besselJExp_intCast_I_mul,
      besselJExp_intCast_I_mul, mathieuFourierB_even_neg_q, mathieuFourierB_even_neg_q,
      I_zpow_natCast_sub, zpow_natCast, I_zpow_neg_natCast, I_pow_two_mul_add_two,
      neg_one_zpow_natCast_sub, neg_one_zpow_natCast_sub, pow_add, pow_add, I_sq]
    have h1 := I_pow_sq_eq_neg_one_pow ℓ
    have h2 := I_pow_sq_eq_neg_one_pow s
    have h3 := neg_one_pow_sq_eq_one ℓ
    have h4 := neg_one_pow_sq_eq_one s
    have h5 := neg_one_pow_sq_eq_one m
    have hs0 : (-1 : ℂ) ^ s ≠ 0 := by simp
    have hm0 : (-1 : ℂ) ^ m ≠ 0 := by simp
    have hIs : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    rw [h1, h4]
    rcases neg_one_pow_eq_or ℂ ℓ with e | e <;> rw [e] <;> ring
  · simp only [modMathieuIo, radialMathieuMs]

open DLMF.Bessel in
/-- DLMF 28.24.8. -/
theorem hasSum_modMathieuIe_odd' (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hB : mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ s * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp z) +
          besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z))))
      (modMathieuIe (2 * m + 1) z h) := by
  have hIh : I * (h : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hh.ne')
  have hq : (I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; push_cast; ring
  have hA' : mathieuFourierA (2 * m + 1) (2 * s + 1) (-(h ^ 2)) ≠ 0 := by
    rw [mathieuFourierA_odd_neg_q]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hB
  have G := (hasSum_radialMathieuMc_odd_cross_of_sq_eq 1 le_rfl (by norm_num) m s hq hIh hA'
    z).mul_left (I ^ (-((2 * m + 1 : ℕ) : ℤ)))
  convert G using 1
  · funext ℓ
    simp only [mathieuCylExp]
    rw [show ((ℓ + s + 1 : ℕ) : ℂ) = (((ℓ + s + 1 : ℕ) : ℤ) : ℂ) by push_cast; ring,
      besselJExp_intCast_I_mul, besselJExp_intCast_I_mul, besselJExp_intCast_I_mul,
      besselJExp_intCast_I_mul, mathieuFourierA_odd_neg_q, mathieuFourierA_odd_neg_q,
      I_zpow_natCast_sub, zpow_natCast, I_zpow_neg_natCast, I_pow_two_mul_add_one,
      neg_one_zpow_natCast_sub, neg_one_zpow_natCast_sub, pow_add, pow_add, pow_one]
    have h1 := I_pow_sq_eq_neg_one_pow ℓ
    have h2 := I_pow_sq_eq_neg_one_pow s
    have h3 := neg_one_pow_sq_eq_one ℓ
    have h4 := neg_one_pow_sq_eq_one s
    have h5 := neg_one_pow_sq_eq_one m
    have hs0 : (-1 : ℂ) ^ s ≠ 0 := by simp
    have hm0 : (-1 : ℂ) ^ m ≠ 0 := by simp
    have hIs : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    rw [h1, h4]
    rcases neg_one_pow_eq_or ℂ ℓ with e | e <;> rw [e] <;> ring
  · simp only [modMathieuIe, radialMathieuMc]

open DLMF.Bessel in
/-- DLMF 28.24.9. -/
theorem hasSum_modMathieuIo_odd' (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hA : mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ s * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp z) -
          besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z))))
      (modMathieuIo (2 * m + 1) z h) := by
  have hIh : I * (h : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hh.ne')
  have hq : (I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; push_cast; ring
  have hB' : mathieuFourierB (2 * m + 1) (2 * s + 1) (-(h ^ 2)) ≠ 0 := by
    rw [mathieuFourierB_odd_neg_q]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hA
  have G := (hasSum_radialMathieuMs_odd_cross_of_sq_eq 1 le_rfl (by norm_num) m s hq hIh hB'
    z).mul_left (I ^ (-((2 * m + 1 : ℕ) : ℤ)))
  convert G using 1
  · funext ℓ
    simp only [mathieuCylExp]
    rw [show ((ℓ + s + 1 : ℕ) : ℂ) = (((ℓ + s + 1 : ℕ) : ℤ) : ℂ) by push_cast; ring,
      besselJExp_intCast_I_mul, besselJExp_intCast_I_mul, besselJExp_intCast_I_mul,
      besselJExp_intCast_I_mul, mathieuFourierB_odd_neg_q, mathieuFourierB_odd_neg_q,
      I_zpow_natCast_sub, zpow_natCast, I_zpow_neg_natCast, I_pow_two_mul_add_one,
      neg_one_zpow_natCast_sub, neg_one_zpow_natCast_sub, pow_add, pow_add, pow_one]
    have h1 := I_pow_sq_eq_neg_one_pow ℓ
    have h2 := I_pow_sq_eq_neg_one_pow s
    have h3 := neg_one_pow_sq_eq_one ℓ
    have h4 := neg_one_pow_sq_eq_one s
    have h5 := neg_one_pow_sq_eq_one m
    have hs0 : (-1 : ℂ) ^ s ≠ 0 := by simp
    have hm0 : (-1 : ℂ) ^ m ≠ 0 := by simp
    have hIs : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    rw [h1, h4]
    rcases neg_one_pow_eq_or ℂ ℓ with e | e <;> rw [e] <;> ring
  · simp only [modMathieuIo, radialMathieuMs]

open DLMF.Bessel in
/-- `H^{(1)}_k(ih e^z) = (2/(πi)) i^{-k} K_k(h e^z)` for integer `k`, `h > 0`, `|Im z| < π`. -/
private lemma mathieuCylExp_three_intCast_I_mul_ofReal (k : ℤ) {h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz : |z.im| < π) :
    mathieuCylExp 3 k (I * h) z = 2 / (π * I) * I ^ (-k) * besselK k (h * Complex.exp z) := by
  rw [mathieuCylExp_three_I_mul_ofReal _ hh hz]
  congr 2
  rw [show -(I * (k : ℂ) * π / 2) = ((-k : ℤ) : ℂ) * ((π / 2 : ℝ) * I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `i^{2s} = (-1)^s` (integer exponent). -/
private lemma I_zpow_two_mul_natCast (s : ℕ) : I ^ (2 * (s : ℤ)) = (-1 : ℂ) ^ s := by
  rw [zpow_mul, show I ^ (2 : ℤ) = -1 by rw [zpow_two, I_mul_I], zpow_natCast]

/-- `i^{-2s} = (-1)^s` (integer exponent). -/
private lemma I_zpow_neg_two_mul_natCast (s : ℕ) : I ^ (-(2 * (s : ℤ))) = (-1 : ℂ) ^ s := by
  rw [zpow_neg, I_zpow_two_mul_natCast, inv_eq_of_mul_eq_one_right]
  rw [← mul_pow]; simp

/-- `i^{2s+1} = (-1)^s i` (integer exponent). -/
private lemma I_zpow_two_mul_natCast_add_one (s : ℕ) : I ^ (2 * (s : ℤ) + 1) = (-1 : ℂ) ^ s * I := by
  rw [zpow_add₀ I_ne_zero, I_zpow_two_mul_natCast, zpow_one]

/-- `i^{-(2s+1)} = -(-1)^s i` (integer exponent). -/
private lemma I_zpow_neg_two_mul_natCast_add_one (s : ℕ) :
    I ^ (-(2 * (s : ℤ) + 1)) = -((-1 : ℂ) ^ s * I) := by
  rw [neg_add, zpow_add₀ I_ne_zero, I_zpow_neg_two_mul_natCast, zpow_neg, zpow_one, inv_I]; ring

/-- `i^{2s+2} = -(-1)^s` (integer exponent). -/
private lemma I_zpow_two_mul_natCast_add_two (s : ℕ) : I ^ (2 * (s : ℤ) + 2) = -(-1 : ℂ) ^ s := by
  rw [zpow_add₀ I_ne_zero, I_zpow_two_mul_natCast, zpow_two, I_mul_I]; ring

/-- `i^{-(2s+2)} = -(-1)^s` (integer exponent). -/
private lemma I_zpow_neg_two_mul_natCast_add_two (s : ℕ) :
    I ^ (-(2 * (s : ℤ) + 2)) = -(-1 : ℂ) ^ s := by
  rw [neg_add, zpow_add₀ I_ne_zero, I_zpow_neg_two_mul_natCast, zpow_neg, zpow_two, I_mul_I]
  norm_num

open DLMF.Bessel in
/-- The product `J_a(ih e^{-z}) H^{(1)}_b(ih e^z)` in modified Bessel functions. -/
private lemma besselJExp_mul_mathieuCylExp_three_I_mul (a b : ℤ) {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : |z.im| < π) :
    besselJExp a (I * h) (-z) * mathieuCylExp 3 b (I * h) z =
      2 / (π * I) * I ^ (a - b) * (besselI a (h * Complex.exp (-z)) *
        besselK b (h * Complex.exp z)) := by
  rw [besselJExp_intCast_I_mul, mathieuCylExp_three_intCast_I_mul_ofReal _ hh hz,
    sub_eq_add_neg, zpow_add₀ I_ne_zero]
  ring

open DLMF.Bessel in
/-- DLMF 28.24.10. -/
theorem hasSum_modMathieuKe_even' (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hC : mathieuFourierA (2 * m) (2 * s) (h ^ 2) ≠ 0) {z : ℂ} (hz : |z.im| < π) :
    HasSum (fun ℓ : ℕ =>
        (mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) /
          mathieuFourierA (2 * m) (2 * s) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselK ((ℓ + s : ℕ) : ℂ) (h * Complex.exp z) +
          besselI ((ℓ + s : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselK ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z)))
      (mathieuEpsilon s * modMathieuKe (2 * m) z h) := by
  have hIh : I * (h : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hh.ne')
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq : (I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; push_cast; ring
  have hC' : mathieuFourierA (2 * m) (2 * s) (-(h ^ 2)) ≠ 0 := by
    rw [mathieuFourierA_even_neg_q]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hC
  have G := (hasSum_radialMathieuMc_even_cross_of_sq_eq 3 (by norm_num) (by norm_num) m s hq hIh hC'
    z).mul_left ((-1 : ℂ) ^ m * (π * I / 2))
  convert G using 1
  · funext ℓ
    rw [show ((ℓ + s : ℕ) : ℂ) = (((ℓ + s : ℕ) : ℤ) : ℂ) by push_cast; ring,
      besselJExp_mul_mathieuCylExp_three_I_mul _ _ hh hz, besselJExp_mul_mathieuCylExp_three_I_mul _ _ hh hz,
      show (ℓ : ℤ) - s - ((ℓ + s : ℕ) : ℤ) = -(2 * (s : ℤ)) by push_cast; ring,
      show ((ℓ + s : ℕ) : ℤ) - ((ℓ : ℤ) - s) = 2 * (s : ℤ) by push_cast; ring,
      I_zpow_neg_two_mul_natCast, I_zpow_two_mul_natCast,
      mathieuFourierA_even_neg_q, mathieuFourierA_even_neg_q, neg_one_zpow_natCast_sub,
      neg_one_zpow_natCast_sub]
    have h1 := I_pow_sq_eq_neg_one_pow ℓ
    have h2 := I_pow_sq_eq_neg_one_pow s
    have h3 := neg_one_pow_sq_eq_one ℓ
    have h4 := neg_one_pow_sq_eq_one s
    have h5 := neg_one_pow_sq_eq_one m
    have hs0 : (-1 : ℂ) ^ s ≠ 0 := by simp
    have hm0 : (-1 : ℂ) ^ m ≠ 0 := by simp
    have hl0 : (-1 : ℂ) ^ ℓ ≠ 0 := by simp
    have hIs : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    have hIl : I ^ ℓ ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    rcases neg_one_pow_eq_or ℂ m with e | e <;> rcases neg_one_pow_eq_or ℂ ℓ with e' | e' <;>
      simp only [e, e', pow_succ] <;> ring
  · simp only [modMathieuKe, radialMathieuMc]
    simp only [even_two_mul, ↓reduceIte, show 2 * m / 2 = m by omega]; ring

open DLMF.Bessel in
/-- DLMF 28.24.11. -/
theorem hasSum_modMathieuKo_even' (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hC : mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2) ≠ 0) {z : ℂ} (hz : |z.im| < π) :
    HasSum (fun ℓ : ℕ =>
        (mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) /
          mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselK ((ℓ + s + 2 : ℕ) : ℂ) (h * Complex.exp z) -
          besselI ((ℓ + s + 2 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselK ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z)))
      (modMathieuKo (2 * m + 2) z h) := by
  have hIh : I * (h : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hh.ne')
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq : (I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; push_cast; ring
  have hC' : mathieuFourierB (2 * m + 2) (2 * s + 2) (-(h ^ 2)) ≠ 0 := by
    rw [mathieuFourierB_even_neg_q]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hC
  have G := (hasSum_radialMathieuMs_even_cross_of_sq_eq 3 (by norm_num) (by norm_num) m s hq hIh hC'
    z).mul_left ((-1 : ℂ) ^ (m + 1) * (π * I / 2))
  convert G using 1
  · funext ℓ
    rw [show ((ℓ + s + 2 : ℕ) : ℂ) = (((ℓ + s + 2 : ℕ) : ℤ) : ℂ) by push_cast; ring,
      besselJExp_mul_mathieuCylExp_three_I_mul _ _ hh hz, besselJExp_mul_mathieuCylExp_three_I_mul _ _ hh hz,
      show (ℓ : ℤ) - s - ((ℓ + s + 2 : ℕ) : ℤ) = -(2 * (s : ℤ) + 2) by push_cast; ring,
      show ((ℓ + s + 2 : ℕ) : ℤ) - ((ℓ : ℤ) - s) = 2 * (s : ℤ) + 2 by push_cast; ring,
      I_zpow_neg_two_mul_natCast_add_two, I_zpow_two_mul_natCast_add_two,
      mathieuFourierB_even_neg_q, mathieuFourierB_even_neg_q, neg_one_zpow_natCast_sub,
      neg_one_zpow_natCast_sub]
    have h1 := I_pow_sq_eq_neg_one_pow ℓ
    have h2 := I_pow_sq_eq_neg_one_pow s
    have h3 := neg_one_pow_sq_eq_one ℓ
    have h4 := neg_one_pow_sq_eq_one s
    have h5 := neg_one_pow_sq_eq_one m
    have hs0 : (-1 : ℂ) ^ s ≠ 0 := by simp
    have hm0 : (-1 : ℂ) ^ m ≠ 0 := by simp
    have hl0 : (-1 : ℂ) ^ ℓ ≠ 0 := by simp
    have hIs : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    have hIl : I ^ ℓ ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    rcases neg_one_pow_eq_or ℂ m with e | e <;> rcases neg_one_pow_eq_or ℂ ℓ with e' | e' <;>
      simp only [e, e', pow_succ] <;> ring
  · simp only [modMathieuKo, radialMathieuMs]
    simp only [show Even (2 * m + 2) from ⟨m + 1, by ring⟩, ↓reduceIte,
      show (2 * m + 2) / 2 = m + 1 by omega]

open DLMF.Bessel in
/-- DLMF 28.24.12. -/
theorem hasSum_modMathieuKe_odd' (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hC : mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) {z : ℂ} (hz : |z.im| < π) :
    HasSum (fun ℓ : ℕ =>
        (mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselK ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp z) -
          besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselK ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z)))
      (modMathieuKe (2 * m + 1) z h) := by
  have hIh : I * (h : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hh.ne')
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq : (I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; push_cast; ring
  have hC' : mathieuFourierA (2 * m + 1) (2 * s + 1) (-(h ^ 2)) ≠ 0 := by
    rw [mathieuFourierA_odd_neg_q]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hC
  have G := (hasSum_radialMathieuMc_odd_cross_of_sq_eq 3 (by norm_num) (by norm_num) m s hq hIh hC'
    z).mul_left ((-1 : ℂ) ^ (m + 1) * (π / 2))
  convert G using 1
  · funext ℓ
    rw [show ((ℓ + s + 1 : ℕ) : ℂ) = (((ℓ + s + 1 : ℕ) : ℤ) : ℂ) by push_cast; ring,
      besselJExp_mul_mathieuCylExp_three_I_mul _ _ hh hz, besselJExp_mul_mathieuCylExp_three_I_mul _ _ hh hz,
      show (ℓ : ℤ) - s - ((ℓ + s + 1 : ℕ) : ℤ) = -(2 * (s : ℤ) + 1) by push_cast; ring,
      show ((ℓ + s + 1 : ℕ) : ℤ) - ((ℓ : ℤ) - s) = 2 * (s : ℤ) + 1 by push_cast; ring,
      I_zpow_neg_two_mul_natCast_add_one, I_zpow_two_mul_natCast_add_one,
      mathieuFourierA_odd_neg_q, mathieuFourierA_odd_neg_q, neg_one_zpow_natCast_sub,
      neg_one_zpow_natCast_sub]
    have h1 := I_pow_sq_eq_neg_one_pow ℓ
    have h2 := I_pow_sq_eq_neg_one_pow s
    have h3 := neg_one_pow_sq_eq_one ℓ
    have h4 := neg_one_pow_sq_eq_one s
    have h5 := neg_one_pow_sq_eq_one m
    have hs0 : (-1 : ℂ) ^ s ≠ 0 := by simp
    have hm0 : (-1 : ℂ) ^ m ≠ 0 := by simp
    have hl0 : (-1 : ℂ) ^ ℓ ≠ 0 := by simp
    have hIs : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    have hIl : I ^ ℓ ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    rcases neg_one_pow_eq_or ℂ m with e | e <;> rcases neg_one_pow_eq_or ℂ ℓ with e' | e' <;>
      simp only [e, e', pow_succ] <;> ring
  · simp only [modMathieuKe, radialMathieuMc]
    simp only [Nat.not_even_two_mul_add_one, ↓reduceIte, show (2 * m + 1) / 2 = m by omega]

open DLMF.Bessel in
/-- DLMF 28.24.13. -/
theorem hasSum_modMathieuKo_odd' (m s : ℕ) {h : ℝ} (hh : 0 < h)
    (hC : mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) {z : ℂ} (hz : |z.im| < π) :
    HasSum (fun ℓ : ℕ =>
        (mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselI ((ℓ : ℤ) - s : ℤ) (h * Complex.exp (-z)) *
            besselK ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp z) +
          besselI ((ℓ + s + 1 : ℕ) : ℂ) (h * Complex.exp (-z)) *
            besselK ((ℓ : ℤ) - s : ℤ) (h * Complex.exp z)))
      (modMathieuKo (2 * m + 1) z h) := by
  have hIh : I * (h : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hh.ne')
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq : (I * (h : ℂ)) ^ 2 = ((-(h ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; push_cast; ring
  have hC' : mathieuFourierB (2 * m + 1) (2 * s + 1) (-(h ^ 2)) ≠ 0 := by
    rw [mathieuFourierB_odd_neg_q]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hC
  have G := (hasSum_radialMathieuMs_odd_cross_of_sq_eq 3 (by norm_num) (by norm_num) m s hq hIh hC'
    z).mul_left ((-1 : ℂ) ^ (m + 1) * (π / 2))
  convert G using 1
  · funext ℓ
    rw [show ((ℓ + s + 1 : ℕ) : ℂ) = (((ℓ + s + 1 : ℕ) : ℤ) : ℂ) by push_cast; ring,
      besselJExp_mul_mathieuCylExp_three_I_mul _ _ hh hz, besselJExp_mul_mathieuCylExp_three_I_mul _ _ hh hz,
      show (ℓ : ℤ) - s - ((ℓ + s + 1 : ℕ) : ℤ) = -(2 * (s : ℤ) + 1) by push_cast; ring,
      show ((ℓ + s + 1 : ℕ) : ℤ) - ((ℓ : ℤ) - s) = 2 * (s : ℤ) + 1 by push_cast; ring,
      I_zpow_neg_two_mul_natCast_add_one, I_zpow_two_mul_natCast_add_one,
      mathieuFourierB_odd_neg_q, mathieuFourierB_odd_neg_q, neg_one_zpow_natCast_sub,
      neg_one_zpow_natCast_sub]
    have h1 := I_pow_sq_eq_neg_one_pow ℓ
    have h2 := I_pow_sq_eq_neg_one_pow s
    have h3 := neg_one_pow_sq_eq_one ℓ
    have h4 := neg_one_pow_sq_eq_one s
    have h5 := neg_one_pow_sq_eq_one m
    have hs0 : (-1 : ℂ) ^ s ≠ 0 := by simp
    have hm0 : (-1 : ℂ) ^ m ≠ 0 := by simp
    have hl0 : (-1 : ℂ) ^ ℓ ≠ 0 := by simp
    have hIs : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    have hIl : I ^ ℓ ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    rcases neg_one_pow_eq_or ℂ m with e | e <;> rcases neg_one_pow_eq_or ℂ ℓ with e' | e' <;>
      simp only [e, e', pow_succ] <;> ring
  · simp only [modMathieuKo, radialMathieuMs]
    simp only [Nat.not_even_two_mul_add_one, ↓reduceIte, show (2 * m + 1) / 2 = m by omega]

end DLMF.Mathieu
