/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Continuation
public import DLMF.OrthogonalPolynomials.Hahn

/-!
# Relations to other functions (DLMF §§13.6, 13.18)

Elementary, error-function, incomplete-gamma, Bessel, Hermite, Laguerre, and
Charlier identities are recorded against existing project definitions.
Parabolic-cylinder identities 13.6.12–13.6.15 and 13.18.11–13.18.13, Airy
identities 13.6.11 and 13.18.10, and Coulomb-wave identities in 13.6(vii) are
deferred here. Parabolic cylinder and Coulomb wave functions are now defined in
`DLMF.Confluent.ParabolicCylinder` and `DLMF.Confluent.Coulomb`.
The finite Kummer–Bessel proofs reuse the Mathlib contributors’ reciprocal-Gamma
recurrence, binomial identities and complex identity principle, with the local
regularized Kummer and Bessel APIs.
-/

@[expose] public section

open Complex Polynomial Filter
open scoped Real Topology ENNReal
open DLMF.OrthogonalPolynomials
open DLMF.Hypergeometric
open DLMF.Bessel

noncomputable section

namespace DLMF.Confluent

/-- Physicists' Hermite polynomial evaluated in `ℂ`. -/
def hermitePolyHEval (n : ℕ) (z : ℂ) : ℂ :=
  eval z ((hermitePolyH n).map (Int.castRingHom ℂ))

/-- `(-n)_{n-s} (-1)^{n-s} / (n-s)! = C(n,s)`. -/
theorem poch_neg_nat_sub_div (n s : ℕ) (hs : s ≤ n) :
    poch (-(n : ℂ)) (n - s) * (-1) ^ (n - s) / ((n - s).factorial : ℂ) = n.choose s := by
  rw [DLMF.Gamma.poch_neg_nat_eq]
  simp only [Nat.sub_le, ↓reduceIte]
  rw [Nat.sub_sub_self hs, Nat.cast_choose ℂ hs]
  have h1 : ((-1 : ℂ) ^ (n - s)) * (-1) ^ (n - s) = 1 := by rw [← mul_pow]; simp
  have hf1 : (s.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : ((n - s).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  linear_combination (n.factorial : ℂ) * h1

/-- Sign bookkeeping for reflected terminating sums. -/
theorem neg_one_pow_add_mul_pow (s t : ℕ) : ((-1 : ℂ) ^ (s + t) * (-1) ^ s) = (-1) ^ t := by
  rw [pow_add, mul_comm, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- On the right half-plane, `(z²)^w = z^{2w}`. -/
theorem sq_cpow_of_re_pos {z : ℂ} (hre : 0 < z.re) (w : ℂ) : (z ^ 2) ^ w = z ^ (2 * w) := by
  have harg : |z.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have him : (log z * 2).im = 2 * z.arg := by
    simp [Complex.log_im, mul_comm]
  rw [← cpow_ofNat, ← cpow_mul _ (by rw [him]; linarith [abs_lt.mp harg])
    (by rw [him]; linarith [abs_lt.mp harg])]

/-- Squares of right half-plane points lie in the slit plane. -/
theorem sq_mem_slitPlane_of_re_pos {z : ℂ} (hre : 0 < z.re) : z ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : z.im = 0
  · left
    simp [sq, him]
    positivity
  · right
    simp only [sq, mul_im]
    intro h
    have : 2 * z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact him h1

/-- `(r x)^w = r^w x^w` for positive real `r`. -/
theorem ofReal_mul_cpow_of_pos {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) (w : ℂ) :
    ((r : ℂ) * x) ^ w = (r : ℂ) ^ w * x ^ w := by
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr' hx), log_ofReal_mul hr hx, cpow_def_of_ne_zero hr',
    cpow_def_of_ne_zero hx, ← exp_add, ofReal_log hr.le]
  ring_nf

/-- `Γ(1/2) = √π`. -/
theorem Gamma_one_half_eq_sqrt : Gamma (1 / 2 : ℂ) = (Real.sqrt π : ℂ) := by
  rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  norm_num

@[dlmf 13.6.E2]
theorem kummerM_one_two (z : ℂ) (hz : z ≠ 0) :
    kummerM 1 2 (2 * z) = exp z * sinh z / z := by
  have h1 : ∀ k : ℕ, (1 : ℂ) ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h := DLMF.Confluent.kummerM_contiguous_shift_a (a := 1) (b := 1) h1 (z := 2 * z)
  rw [sub_self, kummerM_of_zero_param, kummerM_self h1, one_add_one_eq_two] at h
  have key : 2 * z * kummerM 1 2 (2 * z) = exp (2 * z) - 1 := by linear_combination -h
  have h2 := Complex.two_sinh z
  have hexp : exp (2 * z) = exp z * exp z := by rw [← exp_add]; ring_nf
  have hexpneg : exp z * exp (-z) = 1 := by rw [← exp_add]; simp
  rw [eq_div_iff hz]
  linear_combination (1 / 2 : ℂ) * key - (exp z / 2) * h2 + (1 / 2 : ℂ) * hexp +
    (1 / 2 : ℂ) * hexpneg

/-- Tricomi U at zero first parameter, including integer second parameters. -/
@[dlmf 13.6.E3]
theorem kummerU_of_zero_param (b z : ℂ) : kummerU 0 b z = 1 :=
  kummerU_zero b z

/-- The elementary shifted-parameter specialization of the continued Tricomi function. -/
@[dlmf 13.6.E4]
theorem kummerU_shift_one (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerU a (a + 1) z = z ^ (-a) := by
  rw [kummerU_kummer_transform_all a _ (slitPlane_ne_zero hz), show a - (a + 1) + 1 = 0 by ring, kummerU_zero,
    show (1 : ℂ) - (a + 1) = -a by ring, mul_one]

/-- Upper incomplete gamma via Tricomi's `U`, from DLMF 13.6.6. -/
def upperIncGamma (s z : ℂ) : ℂ := exp (-z) * kummerU (1 - s) (1 - s) z

/-- Lower incomplete-Gamma identities with a regular denominator for Kummer M. -/
@[dlmf 13.6.E5]
theorem kummerM_lowerIncGamma (a z : ℂ) (ha : a ≠ 0) {w : ℂ}
    (hw : w ∈ slitPlane) (hz : w = z) (hden : ∀ k : ℕ, a + 1 ≠ -k) :
    kummerM a (a + 1) (-z) = exp (-z) * kummerM 1 (a + 1) z ∧
      kummerM a (a + 1) (-z) = a * z ^ (-a) * lowerIncGamma a z := by
  subst hz
  have hw0 := slitPlane_ne_zero hw
  refine ⟨?_, ?_⟩
  · rw [kummerM_kummer_transform hden, show a + 1 - a = 1 by ring, neg_neg]
  · unfold lowerIncGamma
    have hp : w ^ (-a) * w ^ a = 1 := by
      rw [← cpow_add _ _ hw0, neg_add_cancel, cpow_zero]
    field_simp
    linear_combination (-kummerM a (a + 1) (-w)) * hp

/-- Incomplete-Gamma relations for U at noninteger parameter. -/
@[dlmf 13.6.E6]
theorem kummerU_upperIncGamma (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℤ, a ≠ k) :
    kummerU a a z = z ^ (1 - a) * kummerU 1 (2 - a) z ∧
      kummerU a a z = exp z * upperIncGamma (1 - a) z := by
  refine ⟨?_, ?_⟩
  · simpa using kummerU_kummer_transform a a hz ha
  · unfold upperIncGamma
    have : (1 : ℂ) - (1 - a) = a := by ring
    simp only [this]
    rw [← mul_assoc, ← exp_add]
    convert (one_mul (kummerU a a z)).symm using 2
    convert exp_zero using 2
    ring

@[dlmf 13.6.E7]
theorem kummerM_erf {z : ℂ} (hz : z ≠ 0) :
    kummerM (1 / 2) (3 / 2) (-(z ^ 2)) = (Real.sqrt π : ℂ) / (2 * z) * erf z := by
  unfold erf
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
  field_simp [hz, hπ]
  try ring

/-- Tricomi U at `a = b = 1/2` and complementary error function. The left side depends only on `z ^
2`, so the identity needs `0 < Re z`. -/
@[dlmf 13.6.E8]
theorem kummerU_erfc {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    kummerU (1 / 2) (1 / 2) (z ^ 2) = (Real.sqrt π : ℂ) * exp (z ^ 2) * erfc z := by
  have hz0 := slitPlane_ne_zero hz
  have hb : ∀ k : ℤ, (1 / 2 : ℂ) ≠ k := fun k h => by
    have := congrArg re h
    simp at this
    have h2 : (2 : ℝ) * k = 1 := by linarith
    have : (2 : ℤ) * k = 1 := by exact_mod_cast h2
    omega
  have h32 : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h12 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -k := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [kummerU_eq_connection _ _ _ hb]
  unfold kummerUConnection erfc
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring, show (1 / 2 : ℂ) - 1 / 2 + 1 = 1 by ring,
    show (1 / 2 : ℂ) - 1 = -1 / 2 by ring, show (2 : ℂ) - 1 / 2 = 3 / 2 by ring,
    kummerM_self h12, Complex.Gamma_one, sq_cpow_of_re_pos hre,
    show (2 : ℂ) * (1 / 2) = 1 by ring, cpow_one, kummerM_kummer_transform h32,
    show (3 / 2 : ℂ) - 1 = 1 / 2 by ring, kummerM_erf hz0, Gamma_one_half_eq_sqrt]
  have hGm : Gamma (-1 / 2 : ℂ) = -2 * (Real.sqrt π : ℂ) := by
    have h := Gamma_add_one (-1 / 2 : ℂ) (by norm_num)
    rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by ring, Gamma_one_half_eq_sqrt] at h
    linear_combination 2 * h
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
  rw [hGm]
  field_simp
  ring

@[dlmf 13.6.E9]
theorem kummerM_besselI (ν z : ℂ) (hz : z ∈ slitPlane) (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k) :
    kummerM (ν + 1 / 2) (2 * ν + 1) (2 * z) =
      Gamma (1 + ν) * exp z * (z / 2) ^ (-ν) * besselI ν z := by
  have hz0 := slitPlane_ne_zero hz
  have h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k := fun k h => hν k (by rw [← h]; ring)
  have hν1 : ∀ k : ℕ, ν + 1 ≠ -k := fun k h => hν (2 * k + 1) (by
    push_cast; linear_combination 2 * h)
  rw [kummerM_eq_exp_mul_regularized0F1 hν1 h2ν, besselI,
    show (2 * z) ^ 2 / 16 = z ^ 2 / 4 by ring, show 2 * z / 2 = z by ring,
    show (1 : ℂ) + ν = ν + 1 by ring]
  have hp : (z / 2) ^ (-ν) * (z / 2) ^ ν = 1 := by
    rw [← cpow_add _ _ (div_ne_zero hz0 two_ne_zero)]; simp
  linear_combination (-(Gamma (ν + 1) * exp z *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (z ^ 2 / 4))) * hp

theorem ofReal_mul_cpow' {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ((r : ℂ) * w) ^ s = (r : ℂ) ^ s * w ^ s := by
  rw [cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hr.ne') hw), log_ofReal_mul hr hw,
    cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), cpow_def_of_ne_zero hw, ← exp_add,
    ofReal_log hr.le]
  ring_nf

/-- DLMF 13.6.10 when `2ν` is not an integer, from the connection formula, 13.6.9, the
duplication formula and the reflection formula. -/
theorem kummerU_besselK_of_not_int (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (h2ν : ∀ k : ℤ, 2 * ν ≠ k) :
    kummerU (ν + 1 / 2) (2 * ν + 1) (2 * z) =
      1 / (Real.sqrt π : ℂ) * exp z * (2 * z) ^ (-ν) * besselK ν z := by
  have hz0 := slitPlane_ne_zero hz
  have hν : ∀ k : ℤ, ν ≠ k := fun k h => h2ν (2 * k) (by rw [h]; push_cast; ring)
  have hb : ∀ k : ℤ, 2 * ν + 1 ≠ k := fun k h => h2ν (k - 1) (by push_cast; linear_combination h)
  have hb1 : ∀ k : ℕ, 1 + 2 * ν ≠ -k := fun k h => hb (-k) (by push_cast; linear_combination h)
  have hb2 : ∀ k : ℕ, 1 + 2 * -ν ≠ -k := fun k h =>
    h2ν (k + 1) (by push_cast; linear_combination -h)
  have hhalf : ∀ k : ℤ, ν + 1 / 2 ≠ k := fun k h => h2ν (2 * k - 1) (by
    push_cast; linear_combination 2 * h)
  have hhalf' : ∀ k : ℤ, -ν + 1 / 2 ≠ k := fun k h => h2ν (1 - 2 * k) (by
    push_cast; linear_combination -2 * h)
  have hM1 := kummerM_besselI ν z hz hb1
  have hM2 := kummerM_besselI (-ν) z hz hb2
  rw [show -ν + 1 / 2 = ν + 1 / 2 - (2 * ν + 1) + 1 by ring,
    show 2 * -ν + 1 = 2 - (2 * ν + 1) by ring, neg_neg] at hM2
  rw [kummerU_eq_connection _ _ _ hb, kummerUConnection, hM1, hM2,
    besselK_eq_of_not_int hν, besselE]
  -- the Gamma coefficients
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsπ : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsπ2 : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hs := sin_mul_pi_ne_zero hν
  have hG : ∀ w : ℂ, (∀ k : ℤ, w ≠ k) → Gamma w ≠ 0 := fun w hw =>
    Gamma_ne_zero fun k h => hw (-k) (by rw [h]; push_cast; ring)
  have d1 := Complex.Gamma_mul_Gamma_add_half (-ν)
  have d2 := Complex.Gamma_mul_Gamma_add_half ν
  have r1 := Complex.Gamma_mul_Gamma_one_sub (-ν)
  have r2 := Complex.Gamma_mul_Gamma_one_sub ν
  rw [show 1 - -ν = 1 + ν by ring, mul_neg, Complex.sin_neg] at r1
  rw [show ν + 1 / 2 - (2 * ν + 1) + 1 = -ν + 1 / 2 by ring] at *
  -- the powers
  have hP : ((2 : ℂ) * z) ^ (-ν) = (2 : ℂ) ^ (-ν) * z ^ (-ν) := by
    have := ofReal_mul_cpow' (r := 2) (by norm_num) hz0 (-ν); simpa using this
  have hP2 : ((2 : ℂ) * z) ^ (1 - (2 * ν + 1)) = (2 : ℂ) ^ (-ν) * z ^ (-ν) * ((2 : ℂ) ^ (-ν) *
      z ^ (-ν)) := by
    rw [show 1 - (2 * ν + 1) = -ν + -ν by ring, cpow_add _ _ (mul_ne_zero two_ne_zero hz0), hP]
  have hQ : ∀ s : ℂ, (z / 2) ^ s = (2 : ℂ) ^ (-s) * z ^ s := fun s => by
    have := ofReal_mul_cpow' (r := 1 / 2) (by norm_num) hz0 s
    rw [show ((1 / 2 : ℝ) : ℂ) * z = z / 2 by push_cast; ring] at this
    rw [this, cpow_neg, show ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ by push_cast; ring,
      inv_cpow _ _ (by rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        arg_ofReal_of_nonneg (by norm_num)]; exact Real.pi_pos.ne)]
  rw [hP, hP2, hQ, hQ, neg_neg]
  have hG1 : Gamma (-ν) ≠ 0 := hG _ fun k h => hν (-k) (by push_cast; linear_combination -h)
  have hG2 : Gamma (-ν + 1 / 2) ≠ 0 := hG _ hhalf'
  have hG3 : Gamma ν ≠ 0 := hG _ hν
  have hG4 : Gamma (ν + 1 / 2) ≠ 0 := hG _ hhalf
  have hP1 : (2 : ℂ) ^ (-ν) = ((2 : ℂ) ^ ν)⁻¹ := cpow_neg _ _
  have hZ1 : z ^ (-ν) = (z ^ ν)⁻¹ := cpow_neg _ _
  have hpow1 : (2 : ℂ) ^ (1 - 2 * -ν) = 2 * ((2 : ℂ) ^ ν) ^ 2 := by
    rw [show 1 - 2 * -ν = 1 + (ν + ν) by ring, cpow_add _ _ two_ne_zero, cpow_add _ _ two_ne_zero,
      cpow_one]; ring
  have hpow2 : (2 : ℂ) ^ (1 - 2 * ν) = 2 * (((2 : ℂ) ^ ν)⁻¹) ^ 2 := by
    rw [show 1 - 2 * ν = 1 + (-ν + -ν) by ring, cpow_add _ _ two_ne_zero,
      cpow_add _ _ two_ne_zero, cpow_one, hP1]; ring
  rw [hpow1] at d1
  rw [hpow2] at d2
  rw [show 2 * -ν = 1 - (2 * ν + 1) by ring] at d1
  rw [show 2 * ν = 2 * ν + 1 - 1 by ring] at d2
  rw [show (1 : ℂ) + -ν = 1 - ν by ring, show sin (ν * π) = sin (π * ν) by ring_nf, hP1, hZ1]
  have hP0 : (2 : ℂ) ^ ν ≠ 0 := by rw [cpow_def_of_ne_zero two_ne_zero]; exact exp_ne_zero _
  have hZ0 : z ^ ν ≠ 0 := by rw [cpow_def_of_ne_zero hz0]; exact exp_ne_zero _
  generalize Gamma (1 - (2 * ν + 1)) = A at *
  generalize Gamma (2 * ν + 1 - 1) = B at *
  generalize (2 : ℂ) ^ ν = P at *
  generalize z ^ ν = Z at *
  generalize Gamma (-ν) = G1 at *
  generalize Gamma (-ν + 1 / 2) = G2 at *
  generalize Gamma ν = G3 at *
  generalize Gamma (ν + 1 / 2) = G4 at *
  generalize Gamma (1 + ν) = Gp at *
  generalize Gamma (1 - ν) = Gm at *
  rw [show sin (π * ν) = sin (ν * π) by ring_nf] at r1 r2 ⊢
  generalize sin (ν * π) = S at *
  generalize besselI ν z = Iν
  generalize besselI (-ν) z = Im
  have hA : A = G1 * G2 / (2 * P ^ 2 * Real.sqrt π) := by
    field_simp; linear_combination -d1
  have hB : B = G3 * G4 * P ^ 2 / (2 * Real.sqrt π) := by
    field_simp; field_simp at d2; linear_combination -d2
  rw [hA, hB]
  field_simp at r1 r2 ⊢
  linear_combination Iν * r1 + Im * r2

@[dlmf 13.6.E10]
theorem kummerU_besselK (ν z : ℂ) (hz : z ∈ slitPlane) :
    kummerU (ν + 1 / 2) (2 * ν + 1) (2 * z) =
      1 / (Real.sqrt π : ℂ) * exp z * (2 * z) ^ (-ν) * besselK ν z := by
  have hz0 := slitPlane_ne_zero hz
  have h2z : 2 * z ≠ 0 := mul_ne_zero two_ne_zero hz0
  -- both sides are continuous in the order; compare them along `t = 2ν`
  have key : ∀ t : ℂ, kummerU (t / 2 + 1 / 2) (t + 1) (2 * z) =
      1 / (Real.sqrt π : ℂ) * exp z * (2 * z) ^ (-(t / 2)) * besselK (t / 2) z := by
    intro t
    refine eq_of_continuousAt_of_integerComplement
      (f := fun t => kummerU (t / 2 + 1 / 2) (t + 1) (2 * z))
      (g := fun t => 1 / (Real.sqrt π : ℂ) * exp z * (2 * z) ^ (-(t / 2)) * besselK (t / 2) z)
      (continuousAt_kummerU_comp (by fun_prop) (by fun_prop) h2z)
      ((continuousAt_const.mul (((by fun_prop : ContinuousAt (fun t : ℂ => -(t / 2)) t).const_cpow
        (Or.inl h2z)))).mul
        (continuousAt_besselK_order (· / 2) (by fun_prop) t hz)) fun c hc => ?_
    have hcz := forall_of_mem_integerComplement hc
    have := kummerU_besselK_of_not_int (c / 2) hz (fun k h => hcz k (by linear_combination h))
    rwa [show 2 * (c / 2) = c by ring] at this
  have := key (2 * ν)
  rwa [show 2 * ν / 2 = ν by ring] at this

/-- Entire coefficient for the normalized finite Kummer–Bessel expansion. -/
noncomputable def kummerBesselCoeff (ν : ℂ) (n k : ℕ) : ℂ :=
  (-1) ^ k * (n.choose k : ℂ) * poch (2 * ν) k * (ν + k) *
    (1 / Gamma (2 * ν + 1 + n + k))

/-- Pascal's identity combined with the reciprocal-Gamma recurrence. -/
theorem kummerBesselCoeff_succ (ν : ℂ) (n k : ℕ) :
    kummerBesselCoeff ν n (k + 1) - 2 * ν * (2 * ν + 1) * kummerBesselCoeff (ν + 1) n k =
      (2 * ν + 1 + n) * kummerBesselCoeff ν (n + 1) (k + 1) := by
  have hG := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (2 * ν + 1 + n + (k + 1))
  have hP : 2 * ν * (2 * ν + 1) * poch (2 * (ν + 1)) k =
      poch (2 * ν) (k + 1) * (2 * ν + (k + 1)) := by
    calc
      _ = poch (2 * ν) (k + 2) := by
        rw [show k + 2 = k + 1 + 1 by omega, poch_succ_left (2 * ν) (k + 1),
          poch_succ_left (2 * ν + 1) k]
        rw [show 2 * ν + 1 + 1 = 2 * (ν + 1) by ring]
        ring
      _ = _ := by rw [show k + 2 = k + 1 + 1 by omega, poch_succ]; push_cast; ring
  have hc : (n.choose (k + 1) : ℂ) * (k + 1) = (n.choose k : ℂ) * ((n - k : ℕ) : ℂ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  have hcz : (n.choose (k + 1) : ℂ) * (k + 1) = (n.choose k : ℂ) * ((n : ℂ) - k) := by
    by_cases hk : k ≤ n
    · simpa only [Nat.cast_sub hk] using hc
    · have hk' : n < k := Nat.lt_of_not_ge hk
      simp [Nat.choose_eq_zero_of_lt hk', Nat.choose_eq_zero_of_lt (hk'.trans (Nat.lt_succ_self k))]
  simp only [kummerBesselCoeff, Nat.cast_add, Nat.cast_one, one_div]
  rw [Nat.choose_succ_succ, Nat.cast_add, hG]
  have harg : 2 * ν + 1 + n + (↑k + 1) + 1 = 2 * (ν + 1) + 1 + n + k := by ring
  rw [harg, show 2 * ν + 1 + (n + 1) + (k + 1) =
      2 * (ν + 1) + 1 + n + k by ring, pow_succ]
  have hp := hP
  linear_combination
    -((-1 : ℂ) ^ k * (ν + (k + 1)) * (1 / Gamma (2 * (ν + 1) + 1 + n + k)) * (n.choose k : ℂ)) * hp -
    ((-1 : ℂ) ^ k * (ν + (k + 1)) * (1 / Gamma (2 * (ν + 1) + 1 + n + k)) * poch (2 * ν) (k + 1)) * hcz

/-- The zero coefficient satisfies the same finite-sum recurrence. -/
theorem kummerBesselCoeff_succ_zero (ν : ℂ) (n : ℕ) :
    kummerBesselCoeff ν n 0 = (2 * ν + 1 + n) * kummerBesselCoeff ν (n + 1) 0 := by
  simp only [kummerBesselCoeff, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
    poch_zero, mul_one, Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one, one_div]
  rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (2 * ν + 1 + n)]
  ring

/-- The normalized finite expansion on a parameter half-plane. -/
theorem regularizedConfluent_bessel_sum_pos (n : ℕ) {ν : ℂ} (hν : 0 < ν.re) (z : ℂ) :
    regularizedHGFun {ν + 1 / 2} {2 * ν + 1 + n} (2 * z) * (1 / Gamma ν) =
      exp z * ∑ k ∈ Finset.range (n + 1), kummerBesselCoeff ν n k * (z / 2) ^ k *
        regularizedHGFun ∅ {ν + k + 1} (z ^ 2 / 4) := by
  induction n generalizing ν with
  | zero =>
    have hb : ∀ k : ℕ, 2 * ν + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
    have hb' : ∀ k : ℕ, ν + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
    have hv : ν ≠ 0 := by intro he; simp [he] at hν
    have h := kummerM_eq_exp_mul_regularized0F1 (ν := ν) (z := 2 * z) hb' hb
    rw [kummerM_eq_mul_regularizedHGFun hb] at h
    rw [Gamma_add_one ν hv] at h
    simp only [Nat.zero_add, Nat.cast_zero, add_zero, Finset.sum_range_one, kummerBesselCoeff, pow_zero,
      Nat.choose_zero_right, Nat.cast_one, one_mul, poch_zero, mul_one]
    have hG : Gamma (2 * ν + 1) ≠ 0 := Gamma_ne_zero hb
    have hGν : Gamma ν ≠ 0 := Gamma_ne_zero_of_re_pos hν
    rw [show (2 * z) ^ 2 / 16 = z ^ 2 / 4 by ring, show 2 * z / 2 = z by ring] at h
    field_simp at h ⊢
    linear_combination h
  | succ n ih =>
    have hν' : 0 < (ν + 1).re := by simp; linarith
    have hrec := regularizedConfluent_contiguous_mixed_b_pred (ν + 1 / 2)
      (2 * ν + 1 + (n + 1)) (2 * z)
    have hG := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one ν
    have h1 := ih hν
    have h2 := ih hν'
    have hβ : 2 * ν + 1 + n ≠ 0 := by
      intro he
      have hh := congrArg re he
      simp at hh
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hsum :
        (∑ k ∈ Finset.range (n + 1), kummerBesselCoeff ν n k * (z / 2) ^ k *
          regularizedHGFun ∅ {ν + k + 1} (z ^ 2 / 4)) -
        ν * (2 * ν + 1) * z *
        (∑ k ∈ Finset.range (n + 1), kummerBesselCoeff (ν + 1) n k * (z / 2) ^ k *
          regularizedHGFun ∅ {ν + 1 + k + 1} (z ^ 2 / 4)) =
        (2 * ν + 1 + n) *
        ∑ k ∈ Finset.range (n + 1 + 1), kummerBesselCoeff ν (n + 1) k * (z / 2) ^ k *
          regularizedHGFun ∅ {ν + k + 1} (z ^ 2 / 4) := by
      let f : ℂ → ℕ → ℕ → ℂ := fun v N k => kummerBesselCoeff v N k * (z / 2) ^ k *
        regularizedHGFun ∅ {v + k + 1} (z ^ 2 / 4)
      change (∑ k ∈ Finset.range (n + 1), f ν n k) - ν * (2 * ν + 1) * z *
        (∑ k ∈ Finset.range (n + 1), f (ν + 1) n k) =
        (2 * ν + 1 + n) * ∑ k ∈ Finset.range (n + 1 + 1), f ν (n + 1) k
      have hzcoef : f ν n (n + 1) = 0 := by
        simp [f, kummerBesselCoeff]
      have hleft : (∑ k ∈ Finset.range (n + 1), f ν n k) =
          (∑ k ∈ Finset.range (n + 1), f ν n (k + 1)) + f ν n 0 := by
        have he := Finset.sum_range_succ' (f := f ν n) (n := n + 1)
        rw [Finset.sum_range_succ, hzcoef, add_zero] at he
        exact he
      have hterm (k : ℕ) : f ν n (k + 1) - ν * (2 * ν + 1) * z * f (ν + 1) n k =
          (2 * ν + 1 + n) * f ν (n + 1) (k + 1) := by
        dsimp [f]
        push_cast
        rw [show ν + (k + 1) + 1 = ν + 1 + k + 1 by ring, pow_succ]
        linear_combination ((z / 2) ^ k * (z / 2) *
          regularizedHGFun ∅ {ν + 1 + k + 1} (z ^ 2 / 4)) * kummerBesselCoeff_succ ν n k
      have hhead : f ν n 0 = (2 * ν + 1 + n) * f ν (n + 1) 0 := by
        dsimp [f]
        rw [kummerBesselCoeff_succ_zero]
        ring
      rw [hleft, Finset.mul_sum, show (∑ k ∈ Finset.range (n + 1), f ν n (k + 1)) + f ν n 0 -
          (∑ k ∈ Finset.range (n + 1), ν * (2 * ν + 1) * z * f (ν + 1) n k) =
          (∑ k ∈ Finset.range (n + 1), (f ν n (k + 1) - ν * (2 * ν + 1) * z * f (ν + 1) n k)) + f ν n 0 by
        rw [Finset.sum_sub_distrib]; ring]
      simp_rw [hterm]
      rw [← Finset.mul_sum, hhead, ← mul_add, ← Finset.sum_range_succ']
    apply mul_left_cancel₀ hβ
    have hrec' := congrArg (fun v : ℂ => v * (1 / Gamma ν)) hrec
    simp only [Nat.cast_add, Nat.cast_one] at hrec' ⊢
    rw [show 2 * ν + 1 + (n + 1) - 1 = 2 * ν + 1 + n by ring,
      show ν + 1 / 2 + 1 = (ν + 1) + 1 / 2 by ring,
      show 2 * ν + 1 + (n + 1) + 1 = 2 * (ν + 1) + 1 + n by ring] at hrec'
    linear_combination hrec' + h1 - ν * (2 * ν + 1) * z * h2 + exp z * hsum -
      (2 * ν + 1) * z * regularizedHGFun {ν + 1 + 1 / 2} {2 * (ν + 1) + 1 + n} (2 * z) * hG

/-- The normalized finite expansion is entire in the order parameter. -/
theorem regularizedConfluent_bessel_sum_all (n : ℕ) (ν z : ℂ) :
    regularizedHGFun {ν + 1 / 2} {2 * ν + 1 + n} (2 * z) * (1 / Gamma ν) =
      exp z * ∑ k ∈ Finset.range (n + 1), kummerBesselCoeff ν n k * (z / 2) ^ k *
        regularizedHGFun ∅ {ν + k + 1} (z ^ 2 / 4) := by
  have hL : AnalyticOnNhd ℂ (fun v : ℂ => regularizedHGFun {v + 1 / 2} {2 * v + 1 + n}
      (2 * z) * (1 / Gamma v)) Set.univ := by
    intro v hv
    convert! ((differentiable_regularizedConfluent_comp
      (A := fun v : ℂ => v + 1 / 2) (B := fun v : ℂ => 2 * v + 1 + n)
      (by fun_prop) (by fun_prop) (2 * z)).mul differentiable_one_div_Gamma).analyticAt v using 1 <;> (funext v; simp only [one_div, Pi.mul_apply, Function.comp_apply, id_eq])
  have hR : AnalyticOnNhd ℂ (fun v : ℂ => exp z * ∑ k ∈ Finset.range (n + 1),
      kummerBesselCoeff v n k * (z / 2) ^ k *
        regularizedHGFun ∅ {v + k + 1} (z ^ 2 / 4)) Set.univ := by
    have hc (k : ℕ) : Differentiable ℂ (fun v : ℂ => kummerBesselCoeff v n k) := by
      have hp : Differentiable ℂ (fun v : ℂ => poch (2 * v) k) :=
        (Polynomial.differentiable (ascPochhammer ℂ k)).comp (by fun_prop)
      unfold kummerBesselCoeff
      convert! (((hp.const_mul ((-1 : ℂ) ^ k * (n.choose k : ℂ))).mul
        (differentiable_id.add_const (k : ℂ))).mul
        (differentiable_one_div_Gamma.comp
          (by fun_prop : Differentiable ℂ (fun v : ℂ => 2 * v + 1 + n + k)))) using 1 <;> (funext v; simp only [one_div, Pi.mul_apply, Function.comp_apply, id_eq])
    have hd : Differentiable ℂ (fun v : ℂ => exp z * ∑ k ∈ Finset.range (n + 1),
        kummerBesselCoeff v n k * (z / 2) ^ k *
          regularizedHGFun ∅ {v + k + 1} (z ^ 2 / 4)) := by
      apply Differentiable.const_mul
      apply Differentiable.fun_sum
      intro k hk
      exact ((hc k).mul_const _).mul ((differentiable_regularized0F1_param _).comp (by fun_prop))
    exact fun v hv => hd.analyticAt v
  have he : (fun v : ℂ => regularizedHGFun {v + 1 / 2} {2 * v + 1 + n} (2 * z) * (1 / Gamma v))
      =ᶠ[𝓝 (1 : ℂ)] (fun v : ℂ => exp z * ∑ k ∈ Finset.range (n + 1),
        kummerBesselCoeff v n k * (z / 2) ^ k *
          regularizedHGFun ∅ {v + k + 1} (z ^ 2 / 4)) := by
    filter_upwards [continuous_re.continuousAt.eventually
      (show Set.Ioi (0 : ℝ) ∈ 𝓝 (1 : ℂ).re by simpa using Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with v hv
    exact regularizedConfluent_bessel_sum_pos n hv z
  -- Mathlib’s complex identity principle extends the finite expansion in the order.
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_univ (Set.mem_univ 1) he (Set.mem_univ ν)

/-- Terminating Pochhammer coefficients as binomial coefficients, including zero tails. -/
theorem poch_neg_nat_div_factorial_eq (n k : ℕ) :
    poch (-(n : ℂ)) k / (k.factorial : ℂ) = (-1) ^ k * (n.choose k : ℂ) := by
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr k.factorial_ne_zero]

/-- A finite Kummer expansion in entire `₀F₁` functions of its argument. -/
theorem kummerM_finite_regularized0F1 (ν : ℂ) (n : ℕ) (z : ℂ)
    (hb : ∀ k : ℕ, 2 * ν + 1 + n ≠ -(k : ℂ)) (hΓ : ∀ k : ℕ, ν ≠ -(k : ℂ)) :
    kummerM (ν + 1 / 2) (2 * ν + 1 + n) (2 * z) =
      Gamma ν * exp z * ∑ k ∈ Finset.range (n + 1),
        poch (-(n : ℂ)) k * poch (2 * ν) k * (ν + k) /
          (poch (2 * ν + 1 + n) k * k.factorial) * (z / 2) ^ k *
            regularizedHGFun ∅ {ν + k + 1} (z ^ 2 / 4) := by
  have hGν := Gamma_ne_zero hΓ
  have hGβ := Gamma_ne_zero hb
  have h := regularizedConfluent_bessel_sum_all n ν z
  rw [kummerM_eq_mul_regularizedHGFun hb]
  have hsum : (∑ k ∈ Finset.range (n + 1),
        poch (-(n : ℂ)) k * poch (2 * ν) k * (ν + k) /
          (poch (2 * ν + 1 + n) k * k.factorial) * (z / 2) ^ k *
            regularizedHGFun ∅ {ν + k + 1} (z ^ 2 / 4)) =
      Gamma (2 * ν + 1 + n) * ∑ k ∈ Finset.range (n + 1),
        kummerBesselCoeff ν n k * (z / 2) ^ k * regularizedHGFun ∅ {ν + k + 1} (z ^ 2 / 4) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hG : Gamma (2 * ν + 1 + n + k) = poch (2 * ν + 1 + n) k * Gamma (2 * ν + 1 + n) := by
      have hh := Gamma_add_nat_div_Gamma_eq (n := k) (2 * ν + 1 + n) hb
      exact (div_eq_iff hGβ).mp hh
    have hp := poch_ne_zero_of_not_neg_nat hb k
    rw [kummerBesselCoeff, hG]
    have hbin := poch_neg_nat_div_factorial_eq n k
    field_simp at hbin ⊢
    linear_combination (poch (2 * ν) k * (ν + k) * (z / 2) ^ k *
      regularizedHGFun ∅ {ν + k + 1} (z ^ 2 / 4)) * hbin
  rw [hsum]
  rw [mul_one_div] at h
  rw [(div_eq_iff hGν).mp h]
  ring

/-- Remove the order power from a shifted modified Bessel function. -/
theorem cpow_neg_mul_besselI_shift (ν : ℂ) (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (z / 2) ^ (-ν) * besselI (ν + k) z = (z / 2) ^ k *
      regularizedHGFun ∅ {ν + k + 1} (z ^ 2 / 4) := by
  rw [besselI, ← mul_assoc, ← cpow_add _ _ (div_ne_zero hz two_ne_zero),
    show -ν + (ν + k) = (k : ℂ) by ring, cpow_natCast]


/-- Finite Kummer–Bessel expansion away from the Gamma-prefactor poles.
The former statement included `ν = 0, n = 0`, where totalized `Gamma 0`
made the right-hand side zero. -/
@[dlmf 13.6.E11_1]
theorem kummerM_besselI_sum (ν : ℂ) (n : ℕ) (z : ℂ)
    (hν : ∀ k : ℕ, 2 * ν + 1 + n ≠ -k)
    (hΓ : ∀ k : ℕ, ν ≠ -k) (hz : z ∈ slitPlane) :
    kummerM (ν + 1 / 2) (2 * ν + 1 + n) (2 * z) =
      Gamma ν * exp z * (z / 2) ^ (-ν) *
        ∑ k ∈ Finset.range (n + 1),
          poch (-(n : ℂ)) k * poch (2 * ν) k * (ν + k) /
            (poch (2 * ν + 1 + n) k * k.factorial) * besselI (ν + k) z := by
  rw [kummerM_finite_regularized0F1 ν n z hν hΓ]
  rw [mul_assoc (Gamma ν * exp z)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_left_comm _ _ (besselI _ _), cpow_neg_mul_besselI_shift ν k (slitPlane_ne_zero hz)]
  ring

/-- Negative-shift finite Kummer–Bessel expansion away from all poles of
`Gamma (ν - n)`; excluding only `ν = 0` would not suffice. -/
@[dlmf 13.6.E11_2]
theorem kummerM_besselI_sum_neg (ν : ℂ) (n : ℕ) (z : ℂ)
    (hν : ∀ k : ℕ, 2 * ν + 1 - n ≠ -k)
    (hΓ : ∀ k : ℕ, ν - n ≠ -k) (hz : z ∈ slitPlane) :
    kummerM (ν + 1 / 2) (2 * ν + 1 - n) (2 * z) =
      Gamma (ν - n) * exp z * (z / 2) ^ (n - ν : ℂ) *
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ k * poch (-(n : ℂ)) k * poch (2 * ν - 2 * n) k * (ν - n + k) /
            (poch (2 * ν + 1 - n) k * k.factorial) * besselI (ν + k - n) z := by
  have hβ : ∀ k : ℕ, 2 * (ν - n) + 1 + n ≠ -(k : ℂ) := by
    simpa only [show 2 * (ν - n) + 1 + n = 2 * ν + 1 - n by ring] using hν
  have h := kummerM_finite_regularized0F1 (ν - n) n (-z) hβ hΓ
  rw [show 2 * (ν - n) + 1 + n = 2 * ν + 1 - n by ring,
    show 2 * (ν - n) = 2 * ν - 2 * n by ring] at h
  rw [kummerM_kummer_transform hν,
    show 2 * ν + 1 - n - (ν + 1 / 2) = ν - n + 1 / 2 by ring,
    show -(2 * z) = 2 * -z by ring, h]
  have hE : exp (2 * z) * exp (-z) = exp z := by rw [← exp_add]; congr 1; ring
  have hassoc (s : ℂ) : exp (2 * z) * (Gamma (ν - n) * exp (-z) * s) =
      Gamma (ν - n) * (exp (2 * z) * exp (-z)) * s := by ring
  rw [hassoc, hE, mul_assoc (Gamma (ν - n) * exp z)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show ν + k - n = (ν - n) + k by ring,
    show (n : ℂ) - ν = -(ν - n) by ring]
  have hc := cpow_neg_mul_besselI_shift (ν - n) k (slitPlane_ne_zero hz)
  rw [show (-(z : ℂ)) ^ 2 / 4 = z ^ 2 / 4 by ring,
    show -z / 2 = -(z / 2) by ring, neg_pow]
  calc
    _ = ((-1 : ℂ) ^ k * poch (-(n : ℂ)) k * poch (2 * ν - 2 * n) k * (ν - n + k) /
          (poch (2 * ν + 1 - n) k * k.factorial)) *
        ((z / 2) ^ (-(ν - n)) * besselI (ν - n + k) z) := by rw [hc]; ring
    _ = _ := by ring

/-- `hermitePolyHEval` is the algebra evaluation. -/
theorem hermitePolyHEval_eq_aeval (n : ℕ) (z : ℂ) :
    hermitePolyHEval n z = Polynomial.aeval z (hermitePolyH n) := by
  rw [hermitePolyHEval, Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq]

theorem hermitePolyHEval_zero (z : ℂ) : hermitePolyHEval 0 z = 1 := by
  simp [hermitePolyHEval]

theorem hermitePolyHEval_one (z : ℂ) : hermitePolyHEval 1 z = 2 * z := by
  simp [hermitePolyHEval, hermitePolyH_one]

theorem hermitePolyHEval_two (z : ℂ) : hermitePolyHEval 2 z = 4 * z ^ 2 - 2 := by
  simp [hermitePolyHEval]
  ring

/-- The three-term recurrence `H_{k+2} = 2z H_{k+1} - 2(k+1) H_k`. -/
theorem hermitePolyHEval_succ_succ (k : ℕ) (z : ℂ) :
    hermitePolyHEval (k + 2) z =
      2 * z * hermitePolyHEval (k + 1) z - 2 * (k + 1) * hermitePolyHEval k z := by
  show hermitePolyHEval (k + 1 + 1) z = _
  unfold hermitePolyHEval
  rw [hermitePolyH_succ (k + 1), hermitePolyH_derivative]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_C, Int.coe_castRingHom]
  push_cast
  ring

theorem hermitePolyHEval_three (z : ℂ) : hermitePolyHEval 3 z = 8 * z ^ 3 - 12 * z := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, hermitePolyHEval_succ_succ, hermitePolyHEval_two,
    hermitePolyHEval_one]
  push_cast
  ring

/-- The two-step recurrence `H_{k+4} = (4z² - 4k - 10) H_{k+2} - 4(k+1)(k+2) H_k`. -/
theorem hermitePolyHEval_two_step (k : ℕ) (z : ℂ) :
    hermitePolyHEval (k + 4) z =
      (4 * z ^ 2 - (4 * k + 10)) * hermitePolyHEval (k + 2) z -
        4 * (k + 1) * (k + 2) * hermitePolyHEval k z := by
  have r1 := hermitePolyHEval_succ_succ (k + 2) z
  have r2 := hermitePolyHEval_succ_succ (k + 1) z
  have r3 := hermitePolyHEval_succ_succ k z
  rw [show k + 2 + 2 = k + 4 by ring, show k + 2 + 1 = k + 3 by ring] at r1
  rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring] at r2
  push_cast at r1 r2 r3
  linear_combination r1 + 2 * z * r2 + 2 * ((k : ℂ) + 2) * r3

theorem half_ne_neg_nat : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k hk => by
  have := congrArg Complex.re hk
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem three_half_ne_neg_nat : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k hk => by
  have := congrArg Complex.re hk
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- 13.6.16 in division-free form: `H_{2n}(z) · n! = (-1)^n (2n)! M(-n, 1/2, z²)`. -/
theorem hermitePolyHEval_even_mul (n : ℕ) (z : ℂ) :
    hermitePolyHEval (2 * n) z * n.factorial =
      (-1 : ℂ) ^ n * (2 * n).factorial * kummerM (-(n : ℂ)) (1 / 2) (z ^ 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermitePolyHEval_zero, kummerM_of_zero_param]
  | one =>
    rw [kummerM_eq_sum_neg_nat]
    simp [hermitePolyHEval_two, Finset.sum_range_succ, poch_zero, poch_one]
    ring
  | more n ih0 ih1 =>
    have K := kummerM_contiguous_a (a := -((n : ℂ) + 1)) (b := 1 / 2) (z := z ^ 2)
      half_ne_neg_nat
    rw [show -((n : ℂ) + 1) - 1 = -((n : ℂ) + 2) by ring,
      show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring] at K
    have hrec := hermitePolyHEval_two_step (2 * n) z
    rw [show 2 * n + 4 = 2 * (n + 2) by ring, show 2 * n + 2 = 2 * (n + 1) by ring] at hrec
    have hf4 : ((2 * (n + 2)).factorial : ℂ) =
        (2 * n + 4) * (2 * n + 3) * (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
      rw [show 2 * (n + 2) = 2 * n + 1 + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hf2 : ((2 * (n + 1)).factorial : ℂ) = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hn2 : ((n + 2).factorial : ℂ) = (n + 2) * (n + 1) * n.factorial := by
      rw [show n + 2 = n + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hn1 : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
      simp only [Nat.factorial_succ]
      push_cast
      ring
    rw [hf2, hn1] at ih1
    rw [hf4, hn2]
    push_cast at ih0 ih1 hrec ⊢
    linear_combination (((n : ℂ) + 2) * (n + 1) * (n.factorial : ℂ)) * hrec +
      (((n : ℂ) + 2) * (4 * z ^ 2 - 8 * n - 10)) * ih1 -
      (8 * ((n : ℂ) + 1) ^ 2 * (2 * n + 1) * (n + 2)) * ih0 -
      (4 * (-1 : ℂ) ^ n * ((2 * n).factorial : ℂ) * (2 * n + 1) * (n + 2) * (2 * n + 2)) * K

/-- 13.6.17 in division-free form: `H_{2n+1}(z) · n! = (-1)^n (2n+1)! (2z) M(-n, 3/2, z²)`. -/
theorem hermitePolyHEval_odd_mul (n : ℕ) (z : ℂ) :
    hermitePolyHEval (2 * n + 1) z * n.factorial =
      (-1 : ℂ) ^ n * (2 * n + 1).factorial * (2 * z) * kummerM (-(n : ℂ)) (3 / 2) (z ^ 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermitePolyHEval_one, kummerM_of_zero_param]
  | one =>
    rw [kummerM_eq_sum_neg_nat, show 2 * 1 + 1 = 3 from rfl, hermitePolyHEval_three]
    simp [Finset.sum_range_succ, poch_zero, poch_one]
    ring
  | more n ih0 ih1 =>
    have K := kummerM_contiguous_a (a := -((n : ℂ) + 1)) (b := 3 / 2) (z := z ^ 2)
      three_half_ne_neg_nat
    rw [show -((n : ℂ) + 1) - 1 = -((n : ℂ) + 2) by ring,
      show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring] at K
    have hrec := hermitePolyHEval_two_step (2 * n + 1) z
    rw [show 2 * n + 1 + 4 = 2 * (n + 2) + 1 by ring,
      show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by ring] at hrec
    have hf4 : ((2 * (n + 2) + 1).factorial : ℂ) =
        (2 * n + 5) * (2 * n + 4) * (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
      rw [show 2 * (n + 2) + 1 = 2 * n + 1 + 1 + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hf2 : ((2 * (n + 1) + 1).factorial : ℂ) =
        (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hn2 : ((n + 2).factorial : ℂ) = (n + 2) * (n + 1) * n.factorial := by
      rw [show n + 2 = n + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hn1 : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
      simp only [Nat.factorial_succ]
      push_cast
      ring
    rw [hf2, hn1] at ih1
    rw [hf4, hn2]
    push_cast at ih0 ih1 hrec ⊢
    linear_combination (((n : ℂ) + 2) * (n + 1) * (n.factorial : ℂ)) * hrec +
      (((n : ℂ) + 2) * (4 * z ^ 2 - 8 * n - 14)) * ih1 -
      (8 * ((n : ℂ) + 1) ^ 2 * (2 * n + 3) * (n + 2)) * ih0 -
      (4 * (-1 : ℂ) ^ n * ((2 * n + 1).factorial : ℂ) * (2 * z) * (2 * n + 3) * (n + 2) *
        (2 * n + 2)) * K

@[dlmf 13.6.E16]
theorem kummerM_hermite_even (n : ℕ) (z : ℂ) :
    kummerM (-(n : ℂ)) (1 / 2) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial / (2 * n).factorial * hermitePolyHEval (2 * n) z := by
  have h := hermitePolyHEval_even_mul n z
  have hsq : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  have hf : ((2 * n).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have this : ((2 * n).factorial : ℂ) * kummerM (-(n : ℂ)) (1 / 2) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial * hermitePolyHEval (2 * n) z := by
    linear_combination (-(-1 : ℂ) ^ n) * h -
      (((2 * n).factorial : ℂ) * kummerM (-(n : ℂ)) (1 / 2) (z ^ 2)) * hsq
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hf]
  linear_combination -this

@[dlmf 13.6.E17]
theorem kummerM_hermite_odd (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    kummerM (-(n : ℂ)) (3 / 2) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial / ((2 * n + 1).factorial * 2 * z) *
        hermitePolyHEval (2 * n + 1) z := by
  have h := hermitePolyHEval_odd_mul n z
  have hsq : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  have hf : ((2 * n + 1).factorial : ℂ) * 2 * z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) two_ne_zero) hz
  have this : ((2 * n + 1).factorial : ℂ) * 2 * z * kummerM (-(n : ℂ)) (3 / 2) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial * hermitePolyHEval (2 * n + 1) z := by
    linear_combination (-(-1 : ℂ) ^ n) * h -
      (((2 * n + 1).factorial : ℂ) * 2 * z * kummerM (-(n : ℂ)) (3 / 2) (z ^ 2)) * hsq
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hf]
  linear_combination -this

/-- Tricomi U and Hermite polynomials. The left side depends only on `z ^ 2`, so the identity needs
`0 < Re z`. -/
@[dlmf 13.6.E18]
theorem kummerU_hermite (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    kummerU (1 / 2 - n / 2) (3 / 2) (z ^ 2) =
      (2 : ℂ) ^ (-(n : ℂ)) * z⁻¹ * hermitePolyHEval n z := by
  have hz0 := slitPlane_ne_zero hz
  have hnp : ∀ (c : ℂ), 0 < c.re → ∀ k : ℕ, c ≠ -k := fun c hc k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h4 : ∀ m : ℕ, (2 : ℂ) ^ (-((2 * m : ℕ) : ℂ)) = ((4 : ℂ) ^ m)⁻¹ := fun m => by
    rw [cpow_neg, cpow_natCast, pow_mul]; norm_num
  have hf : ∀ k : ℕ, (k.factorial : ℂ) ≠ 0 := fun k => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsq : ∀ m : ℕ, ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := fun m => by rw [← mul_pow]; simp
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [kummerU_kummer_transform_all _ _ (slitPlane_ne_zero (sq_mem_slitPlane_of_re_pos hre)),
      show (1 : ℂ) / 2 - ((2 * m : ℕ) : ℂ) / 2 - 3 / 2 + 1 = -(m : ℂ) by push_cast; ring,
      show (2 : ℂ) - 3 / 2 = 1 / 2 by ring, show (1 : ℂ) - 3 / 2 = -1 / 2 by ring,
      sq_cpow_of_re_pos hre, show (2 : ℂ) * (-1 / 2) = -1 by ring, cpow_neg_one,
      kummerU_neg_nat m _ _ (hnp _ (by norm_num)), kummerM_hermite_even, poch_half, h4]
    have := hf (2 * m); have := hf m
    have hsq2 : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [sq, hsq]
    field_simp
    linear_combination hermitePolyHEval (2 * m) z * hsq2
  · rw [show (1 : ℂ) / 2 - ((2 * m + 1 : ℕ) : ℂ) / 2 = -(m : ℂ) by push_cast; ring,
      kummerU_neg_nat m _ _ (hnp _ (by norm_num)), kummerM_hermite_odd m hz0,
      poch_three_halves_factorial, cpow_neg, cpow_natCast, pow_succ, pow_mul]
    norm_num
    have := hf (2 * m + 1); have := hf m
    have hsq2 : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [sq, hsq]
    field_simp
    linear_combination hermitePolyHEval (2 * m + 1) z * hsq2

/-- Laguerre specialization of continued U, with a regular ordinary-M denominator. -/
@[dlmf 13.6.E19]
theorem kummerU_laguerrePolyL (n : ℕ) (α z : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k) :
    kummerU (-(n : ℂ)) (α + 1) z =
      (-1 : ℂ) ^ n * poch (α + 1) n * kummerM (-(n : ℂ)) (α + 1) z ∧
      kummerU (-(n : ℂ)) (α + 1) z = (-1 : ℂ) ^ n * n.factorial * laguerrePolyL α n z := by
  have h := kummerU_neg_nat n (α + 1) z hα
  refine ⟨h, ?_⟩
  rw [h, laguerrePolyL]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- Charlier specialization with nonzero scale and a regular ordinary-M denominator. -/
@[dlmf 13.6.E20]
theorem kummerU_charlier (n : ℕ) (z a : ℂ) (ha : a ≠ 0)
    (hz : ∀ k : ℕ, z - n + 1 ≠ -k) :
    kummerU (-(n : ℂ)) (z - n + 1) a =
      poch (-z) n * kummerM (-(n : ℂ)) (z - n + 1) a ∧
      kummerU (-(n : ℂ)) (z - n + 1) a = a ^ n * DLMF.OrthogonalPolynomials.charlier a n z := by
  refine ⟨?_, ?_⟩
  · rw [kummerU_neg_nat n _ a hz]
    have hp := poch_one_sub_sub_nat (-z) n
    rw [show 1 - -z - (n : ℂ) = z - n + 1 by ring] at hp
    have h1 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    rw [hp]
    linear_combination (poch (-z) n * kummerM (-(n : ℂ)) (z - n + 1) a) * h1
  · rw [kummerU_neg_nat_sum, DLMF.OrthogonalPolynomials.charlier,
      DLMF.OrthogonalPolynomials.terminatingHG, Finset.mul_sum, Finset.mul_sum]
    conv_rhs => rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show n + 1 - 1 - s = n - s by omega]
    have hc := poch_neg_nat_sub_div n s hs'
    obtain ⟨t, rfl⟩ : ∃ t, n = s + t := ⟨n - s, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc ⊢
    have hp := poch_one_sub_sub_nat (-z) t
    rw [show 1 - -z - (t : ℂ) = z - ((s + t : ℕ) : ℂ) + 1 + s by push_cast; ring] at hp
    have hapow : a ^ (s + t) * (-a⁻¹) ^ t = (-1) ^ t * a ^ s := by
      rw [neg_pow, pow_add, inv_pow]
      field_simp
    have hsgn := neg_one_pow_add_mul_pow s t
    have h1 : ((-1 : ℂ) ^ t) * (-1) ^ t = 1 := by rw [← mul_pow]; simp
    have hf2 : (t.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
    rw [neg_pow a s, ← hc, hp]
    calc (-1 : ℂ) ^ (s + t) * (poch (-((s + t : ℕ) : ℂ)) t * (-1) ^ t / t.factorial *
          ((-1) ^ t * poch (-z) t) * ((-1) ^ s * a ^ s))
        = ((-1 : ℂ) ^ (s + t) * (-1) ^ s) * ((-1) ^ t * (-1) ^ t) * poch (-((s + t : ℕ) : ℂ)) t /
          t.factorial * poch (-z) t * a ^ s := by ring
      _ = _ := by
        rw [hsgn, h1]
        linear_combination (-(poch (-((s + t : ℕ) : ℂ)) t * poch (-z) t / t.factorial)) * hapow

/-- The terminating `₂F₀` expression for polynomial Tricomi U.
A nonterminating `₂F₀` is generally divergent and cannot be interpreted as
Mathlib's ordinary regularized hypergeometric power-series sum. -/
@[dlmf 13.6.E21]
theorem kummerU_eq_twoFzero (n : ℕ) (b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerU (-(n : ℂ)) b z =
      z ^ n * regularizedHGFun {-(n : ℂ), -(n : ℂ) - b + 1}
        (∅ : Multiset ℂ) (-z⁻¹) := by
  have hz0 := slitPlane_ne_zero hz
  have hfin : regularizedHGFun {-(n : ℂ), -(n : ℂ) - b + 1} (∅ : Multiset ℂ) (-z⁻¹) =
      ∑ k ∈ Finset.range (n + 1),
        poch (-(n : ℂ)) k * poch (-(n : ℂ) - b + 1) k / k.factorial * (-z⁻¹) ^ k := by
    rw [regularizedHGFun_eq_tsum, tsum_eq_sum (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp [regularizedHGFunCoeff, poch]
    · intro k hk
      have hk' : n < k := by simpa using hk
      simp [regularizedHGFunCoeff, hk']
  rw [hfin, kummerU_neg_nat_sum, Finset.mul_sum, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [show n + 1 - 1 - s = n - s by omega]
  have hc := poch_neg_nat_sub_div n s hs'
  have hp := poch_one_sub_sub_nat (b + s) (n - s)
  rw [show (1 : ℂ) - (b + s) - ((n - s : ℕ) : ℂ) = -(n : ℂ) - b + 1 by
    push_cast [Nat.cast_sub hs']; ring] at hp
  obtain ⟨t, rfl⟩ : ∃ t, n = s + t := ⟨n - s, by omega⟩
  rw [Nat.add_sub_cancel_left] at hc hp ⊢
  have hzpow : z ^ (s + t) * (-z⁻¹) ^ t = (-1) ^ t * z ^ s := by
    rw [neg_pow, pow_add, inv_pow]
    field_simp
  have hsgn := neg_one_pow_add_mul_pow s t
  have hf2 : (t.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [neg_pow z s, ← hc, hp]
  calc (-1 : ℂ) ^ (s + t) * (poch (-((s + t : ℕ) : ℂ)) t * (-1) ^ t / t.factorial *
        poch (b + s) t * ((-1) ^ s * z ^ s))
      = ((-1 : ℂ) ^ (s + t) * (-1) ^ s) * poch (-((s + t : ℕ) : ℂ)) t * (-1) ^ t / t.factorial *
        poch (b + s) t * z ^ s := by ring
    _ = _ := by
      rw [hsgn]
      linear_combination (-(poch (-((s + t : ℕ) : ℂ)) t * (-1) ^ t * poch (b + s) t /
        t.factorial)) * hzpow

@[dlmf 13.18.E1]
theorem whittakerM_sinh {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerM 0 (1 / 2) (2 * z) = 2 * sinh z := by
  have hz0 : z ≠ 0 := by
    intro h
    exact slitPlane_ne_zero hz (by simp [h])
  unfold whittakerM
  have hμ : (1 / 2 : ℂ) - 0 + 1 / 2 = 1 := by ring
  have hb : (1 : ℂ) + 2 * (1 / 2) = 2 := by ring
  have hr : (1 / 2 : ℂ) + 1 / 2 = 1 := by ring
  rw [hμ, hb, hr, cpow_one, kummerM_one_two z hz0]
  have : exp (-(2 * z) / 2) = exp (-z) := by ring_nf
  rw [this]
  field_simp [hz0]
  rw [← exp_add, neg_add_cancel, exp_zero, one_mul]

@[dlmf 13.18.E2]
theorem whittakerM_exp (κ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerM κ (κ - 1 / 2) z = exp (-z / 2) * z ^ κ ∧
      whittakerW κ (κ - 1 / 2) z = exp (-z / 2) * z ^ κ ∧
      whittakerW κ (-κ + 1 / 2) z = exp (-z / 2) * z ^ κ := by
  have hz0 := slitPlane_ne_zero hz
  refine ⟨?_, ?_, ?_⟩
  · unfold whittakerM
    rw [show κ - 1 / 2 - κ + 1 / 2 = 0 by ring, kummerM_of_zero_param,
      show κ - 1 / 2 + 1 / 2 = κ by ring, mul_one]
  · unfold whittakerW
    rw [show 1 / 2 + (κ - 1 / 2) - κ = 0 by ring, kummerU_zero,
      show 1 / 2 + (κ - 1 / 2) = κ by ring, mul_one]
  · unfold whittakerW
    rw [show 1 / 2 + (-κ + 1 / 2) - κ = 1 - 2 * κ by ring,
      show 1 + 2 * (-κ + 1 / 2) = (1 - 2 * κ) + 1 by ring, kummerU_shift_one _ hz, mul_assoc,
      ← cpow_add _ _ hz0]
    congr 2
    ring

/-- An exponential Whittaker-M specialization with a regular denominator parameter. -/
@[dlmf 13.18.E3]
theorem whittakerM_exp_neg (κ : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hκ : ∀ k : ℕ, -2 * κ ≠ -k) :
    whittakerM κ (-κ - 1 / 2) z = exp (z / 2) * z ^ (-κ) := by
  unfold whittakerM
  rw [show -κ - 1 / 2 - κ + 1 / 2 = -2 * κ by ring, show 1 + 2 * (-κ - 1 / 2) = -2 * κ by ring,
    kummerM_self hκ, show -κ - 1 / 2 + 1 / 2 = -κ by ring]
  have : exp (-z / 2) * exp z = exp (z / 2) := by rw [← exp_add]; ring_nf
  rw [← this]
  ring

/-- Whittaker M and the lower incomplete Gamma function. At `μ = 0` the right side is the
removable limit `2μ γ(2μ,z) → 1`, which the totalized `lowerIncGamma` does not take. -/
@[dlmf 13.18.E4]
theorem whittakerM_lowerIncGamma (μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hμ0 : μ ≠ 0) :
    whittakerM (μ - 1 / 2) μ z =
      2 * μ * exp (z / 2) * z ^ (1 / 2 - μ) * lowerIncGamma (2 * μ) z := by
  have hz0 := slitPlane_ne_zero hz
  unfold whittakerM lowerIncGamma
  have hden : ∀ k : ℕ, 2 * μ + 1 ≠ -k := fun k h => hμ k (by rw [← h]; ring)
  rw [kummerM_kummer_transform hden, show 2 * μ + 1 - 2 * μ = 1 by ring, neg_neg,
    show μ - (μ - 1 / 2) + 1 / 2 = 1 by ring, show 2 * μ + 1 = 1 + 2 * μ by ring]
  have hp : z ^ (1 / 2 - μ) * z ^ (2 * μ) = z ^ (μ + 1 / 2) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  have he : exp (z / 2) * exp (-z) = exp (-z / 2) := by rw [← exp_add]; ring_nf
  have h2 : (2 : ℂ) * μ ≠ 0 := mul_ne_zero two_ne_zero hμ0
  rw [← hp, ← he]
  field_simp

@[dlmf 13.18.E5]
theorem whittakerW_upperIncGamma (μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW (μ - 1 / 2) μ z =
      exp (z / 2) * z ^ (1 / 2 - μ) * upperIncGamma (2 * μ) z := by
  have hz0 := slitPlane_ne_zero hz
  unfold whittakerW upperIncGamma
  rw [kummerU_kummer_transform_all (1 - 2 * μ) _ (slitPlane_ne_zero hz), show 1 / 2 + μ - (μ - 1 / 2) = 1 by ring,
    show 1 - 2 * μ - (1 - 2 * μ) + 1 = 1 by ring, show (2 : ℂ) - (1 - 2 * μ) = 1 + 2 * μ by ring,
    show (1 : ℂ) - (1 - 2 * μ) = 2 * μ by ring]
  have hp : z ^ (1 / 2 - μ) * z ^ (2 * μ) = z ^ (1 / 2 + μ) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  have he : exp (z / 2) * exp (-z) = exp (-z / 2) := by rw [← exp_add]; ring_nf
  rw [← hp, ← he]
  ring

/-- Whittaker function and error functions. The left side depends only on `z ^ 2`, so the identity
needs `0 < Re z`. -/
@[dlmf 13.18.E6]
theorem whittakerM_erf {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerM (-1 / 4) (1 / 4) (z ^ 2) =
      (1 / 2) * exp (z ^ 2 / 2) * (Real.sqrt π : ℂ) * z ^ (1 / 2 : ℂ) * erf z := by
  have hz0 := slitPlane_ne_zero hz
  have h32 : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  unfold whittakerM
  rw [show (1 / 4 : ℂ) - (-1 / 4) + 1 / 2 = 1 by ring,
    show (1 : ℂ) + 2 * (1 / 4) = 3 / 2 by ring, kummerM_kummer_transform h32,
    show (3 / 2 : ℂ) - 1 = 1 / 2 by ring, kummerM_erf hz0,
    sq_cpow_of_re_pos hre, show (2 : ℂ) * (1 / 4 + 1 / 2) = 1 + 1 / 2 by ring,
    cpow_add _ _ hz0, cpow_one]
  have he : exp (-z ^ 2 / 2) * exp (z ^ 2) = exp (z ^ 2 / 2) := by rw [← exp_add]; ring_nf
  rw [← he]
  field_simp

/-- Whittaker function and error functions. The left side depends only on `z ^ 2`, so the identity
needs `0 < Re z`. -/
@[dlmf 13.18.E7]
theorem whittakerW_erfc {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerW (-1 / 4) (1 / 4) (z ^ 2) =
      exp (z ^ 2 / 2) * (Real.sqrt π : ℂ) * z ^ (1 / 2 : ℂ) * erfc z := by
  have hz0 := slitPlane_ne_zero hz
  have hz2 := slitPlane_ne_zero (sq_mem_slitPlane_of_re_pos hre)
  unfold whittakerW
  rw [show (1 / 2 : ℂ) + 1 / 4 - -1 / 4 = 1 by ring, show (1 : ℂ) + 2 * (1 / 4) = 3 / 2 by ring,
    kummerU_kummer_transform_all 1 (3 / 2) hz2, show (1 : ℂ) - 3 / 2 + 1 = 1 / 2 by ring,
    show (2 : ℂ) - 3 / 2 = 1 / 2 by ring, kummerU_erfc hz hre, sq_cpow_of_re_pos hre,
    sq_cpow_of_re_pos hre, show (2 : ℂ) * (1 / 2 + 1 / 4) = 1 + 1 / 2 by ring,
    show (2 : ℂ) * (1 - 3 / 2) = -1 by ring, cpow_neg_one, cpow_add _ _ hz0, cpow_one]
  have he : exp (-z ^ 2 / 2) * exp (z ^ 2) = exp (z ^ 2 / 2) := by
    rw [← exp_add]; ring_nf
  rw [← he]
  field_simp

@[dlmf 13.18.E8]
theorem whittakerM_besselI (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k) :
    whittakerM 0 ν (2 * z) =
      (2 : ℂ) ^ (2 * ν + 1 / 2) * Gamma (1 + ν) * z ^ (1 / 2 : ℂ) * besselI ν z := by
  have hz0 := slitPlane_ne_zero hz
  unfold whittakerM
  rw [show ν - 0 + 1 / 2 = ν + 1 / 2 by ring, show 1 + 2 * ν = 2 * ν + 1 by ring,
    kummerM_besselI ν z hz hν]
  have h2 : (2 * z) ^ (ν + 1 / 2) = (2 : ℂ) ^ (ν + 1 / 2) * z ^ (ν + 1 / 2) := by
    have := ofReal_mul_cpow_of_pos (r := 2) two_pos hz0 (ν + 1 / 2)
    simpa using this
  have h3 : (z / 2) ^ (-ν) = (2 : ℂ) ^ ν * z ^ (-ν) := by
    have := ofReal_mul_cpow_of_pos (r := 1 / 2) (by norm_num) hz0 (-ν)
    rw [show ((1 / 2 : ℝ) : ℂ) * z = z / 2 by push_cast; ring] at this
    rw [this]
    have h2arg : (2 : ℂ).arg ≠ π := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_pos.ne
    have h12 : ((1 / 2 : ℝ) : ℂ) ^ (-ν) = (2 : ℂ) ^ ν := by
      rw [cpow_neg, show ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ by push_cast; ring,
        inv_cpow _ _ h2arg, inv_inv]
    rw [h12]
  have h4 : (2 : ℂ) ^ (ν + 1 / 2) * (2 : ℂ) ^ ν = (2 : ℂ) ^ (2 * ν + 1 / 2) := by
    rw [← cpow_add _ _ two_ne_zero]; ring_nf
  have h5 : z ^ (ν + 1 / 2) * z ^ (-ν) = z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  have he : exp (-(2 * z) / 2) * exp z = 1 := by rw [← exp_add]; ring_nf; simp
  rw [h2, h3, ← h4, ← h5]
  linear_combination (2 : ℂ) ^ (ν + 1 / 2) * 2 ^ ν * z ^ (ν + 1 / 2) * z ^ (-ν) *
    Gamma (1 + ν) * besselI ν z * he

@[dlmf 13.18.E9]
theorem whittakerW_besselK (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW 0 ν (2 * z) =
      ((2 * z) / π) ^ (1 / 2 : ℂ) * besselK ν z := by
  have hz0 := slitPlane_ne_zero hz
  have h2z : 2 * z ≠ 0 := mul_ne_zero two_ne_zero hz0
  have hU := kummerU_besselK ν z hz
  rw [whittakerW, show 1 / 2 + ν - 0 = ν + 1 / 2 by ring, show 1 + 2 * ν = 2 * ν + 1 by ring, hU]
  have hsplit :
      ((2 * z) / π) ^ (1 / 2 : ℂ) = ((1 / π : ℝ) : ℂ) ^ (1 / 2 : ℂ) * (2 * z) ^ (1 / 2 : ℂ) := by
    rw [← ofReal_mul_cpow' (by positivity) h2z]; push_cast; ring_nf
  have hsq : ((1 / π : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 1 / (Real.sqrt π : ℂ) := by
    rw [show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity : (0 : ℝ) ≤ 1 / π),
      ← Real.sqrt_eq_rpow, Real.sqrt_div' _ Real.pi_pos.le, Real.sqrt_one]
    push_cast; ring
  have hp : (2 * z) ^ (1 / 2 + ν) * (2 * z) ^ (-ν) = (2 * z) ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ h2z]; ring_nf
  have he : exp (-(2 * z) / 2) * exp z = 1 := by rw [← exp_add]; ring_nf; simp
  rw [hsplit, hsq]
  linear_combination (1 / (Real.sqrt π : ℂ) * (2 * z) ^ (1 / 2 + ν) * (2 * z) ^ (-ν) *
    besselK ν z) * he + (1 / (Real.sqrt π : ℂ) * besselK ν z) * hp

/-- Whittaker function and Hermite polynomials. The left side depends only on `z ^ 2`, so the
identity needs `0 < Re z`. -/
@[dlmf 13.18.E14]
theorem whittakerM_hermite_even (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerM (1 / 4 + n) (-1 / 4) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial / (2 * n).factorial * exp (-z ^ 2 / 2) *
        z ^ (1 / 2 : ℂ) * hermitePolyHEval (2 * n) z := by
  unfold whittakerM
  rw [show (-1 / 4 : ℂ) - (1 / 4 + n) + 1 / 2 = -(n : ℂ) by ring,
    show (1 : ℂ) + 2 * (-1 / 4) = 1 / 2 by ring, kummerM_hermite_even,
    sq_cpow_of_re_pos hre, show (2 : ℂ) * (-1 / 4 + 1 / 2) = 1 / 2 by ring]
  ring

/-- Whittaker function and Hermite polynomials. The left side depends only on `z ^ 2`, so the
identity needs `0 < Re z`. -/
@[dlmf 13.18.E15]
theorem whittakerM_hermite_odd (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerM (3 / 4 + n) (1 / 4) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial / (2 * n + 1).factorial *
        exp (-z ^ 2 / 2) * z ^ (1 / 2 : ℂ) / 2 * hermitePolyHEval (2 * n + 1) z := by
  have hz0 := slitPlane_ne_zero hz
  unfold whittakerM
  rw [show (1 / 4 : ℂ) - (3 / 4 + n) + 1 / 2 = -(n : ℂ) by ring,
    show (1 : ℂ) + 2 * (1 / 4) = 3 / 2 by ring, kummerM_hermite_odd n hz0,
    sq_cpow_of_re_pos hre, show (2 : ℂ) * (1 / 4 + 1 / 2) = 1 + 1 / 2 by ring,
    cpow_add _ _ hz0, cpow_one]
  have hf : ((2 * n + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- Whittaker function and Hermite polynomials. The left side depends only on `z ^ 2`, so the
identity needs `0 < Re z`. -/
@[dlmf 13.18.E16]
theorem whittakerW_hermite (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerW (1 / 4 + n / 2) (1 / 4) (z ^ 2) =
      (2 : ℂ) ^ (-(n : ℂ)) * exp (-z ^ 2 / 2) * z ^ (1 / 2 : ℂ) * hermitePolyHEval n z := by
  have hz0 := slitPlane_ne_zero hz
  unfold whittakerW
  rw [show (1 / 2 : ℂ) + 1 / 4 - (1 / 4 + n / 2) = 1 / 2 - n / 2 by ring,
    show (1 : ℂ) + 2 * (1 / 4) = 3 / 2 by ring, kummerU_hermite n hz hre, sq_cpow_of_re_pos hre,
    show (2 : ℂ) * (1 / 2 + 1 / 4) = 1 + 1 / 2 by ring, cpow_add _ _ hz0, cpow_one]
  field_simp

/-- Laguerre specialization of W with a regular Kummer-M denominator. -/
@[dlmf 13.18.E17]
theorem whittakerW_laguerrePolyL (α : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane)
    (hα : ∀ k : ℕ, α + 1 ≠ -k) :
    whittakerW (α / 2 + 1 / 2 + n) (α / 2) z =
      (-1 : ℂ) ^ n * poch (α + 1) n * whittakerM (α / 2 + 1 / 2 + n) (α / 2) z ∧
      whittakerW (α / 2 + 1 / 2 + n) (α / 2) z =
        (-1 : ℂ) ^ n * n.factorial * exp (-z / 2) * z ^ (α / 2 + 1 / 2) * laguerrePolyL α n z := by
  obtain ⟨h1, h2⟩ := kummerU_laguerrePolyL n α z hα
  unfold whittakerW whittakerM
  rw [show 1 / 2 + α / 2 - (α / 2 + 1 / 2 + n) = -(n : ℂ) by ring,
    show α / 2 - (α / 2 + 1 / 2 + n) + 1 / 2 = -(n : ℂ) by ring,
    show 1 + 2 * (α / 2) = α + 1 by ring, show 1 / 2 + α / 2 = α / 2 + 1 / 2 by ring]
  refine ⟨?_, ?_⟩
  · rw [h1]; ring
  · rw [h2]; ring

end DLMF.Confluent
