/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic
public import DLMF.Mathieu.Properties
public import DLMFMathlib.Analysis.Fourier.P1a2EntirePeriodic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Fourier series of the Mathieu functions (DLMF §28.4)

The Fourier coefficients `A^n_m(q) = mathieuFourierA n m q`, `B^n_m(q) = mathieuFourierB n m q`
of `ce_n`, `se_n` (real `q`) are defined in `DLMF.Mathieu.Basic` as the Fourier integrals.

Proved here (from the definitions and the admitted existence theorems of `DLMF.Mathieu.Basic`):
the expansions 28.4.1–28.4.4 for every complex `z` (from the Fourier series of entire periodic
functions, `DLMFMathlib.Analysis.Fourier.P1a2EntirePeriodic`, and the parity and periodicity of
`ce_n`, `se_n`), the recurrences 28.4.5–28.4.8 (integration by parts against `cos mx`, `sin mx`),
the normalizations 28.4.9–28.4.12 (Parseval together with 28.2.30), the sign convention of
§28.4(iii), the values 28.4.13–28.4.16 at `q = 0` (from 28.2.29) and the change of sign of `q`
28.4.17–28.4.20 (from 28.2.34–28.2.37), and the absolute and locally uniform convergence of
§28.4(i) (exponential decay of the coefficients and the Weierstrass M-test). The integration by
parts identities `p1a2_cos_rec`, `p1a2_sin_rec` and the decay bounds `p2f_cos_coeff_decay`,
`p2f_sin_coeff_decay` live in `DLMF.Mathieu.Properties` (used there for Ince's theorem). The
asymptotic forms 28.4.21–28.4.27 remain admitted.

Small-`q` forms such as 28.4.21, `A_{2s} = (c q^s + O(q^{s+2})) A_0`, are stated with an
explicit error function `ε` with `ε = O(q^{s+2})` as `q → 0`; the large-`m` forms 28.4.24–28.4.27
likewise with `ε = O(1/m)` as `m → ∞` (`q ≠ 0` fixed). This avoids dividing by `A_0`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Auxiliary lemmas -/

/-- `ce_n(z, q)` is `2π`-periodic. -/
theorem p1a2_mathieuCe_two_pi (n : ℕ) (q : ℝ) (z : ℂ) :
    mathieuCe n (z + 2 * π) q = mathieuCe n z q := by
  rw [show z + 2 * (π : ℂ) = z + π + π by ring]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [mathieuCe_even_add_pi, mathieuCe_even_add_pi]
  · rw [mathieuCe_odd_add_pi, mathieuCe_odd_add_pi, neg_neg]

/-- `se_n(z, q)` is `2π`-periodic for `n ≠ 0`. -/
theorem p1a2_mathieuSe_two_pi {n : ℕ} (hn : n ≠ 0) (q : ℝ) (z : ℂ) :
    mathieuSe n (z + 2 * π) q = mathieuSe n z q := by
  rw [show z + 2 * (π : ℂ) = z + π + π by ring]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, mathieuSe_even_add_pi, mathieuSe_even_add_pi]
  · rw [mathieuSe_odd_add_pi, mathieuSe_odd_add_pi, neg_neg]

/-- The recurrence identity for the cosine integrals of `ce_n` with natural indices. -/
theorem p1a2_ce_rec (n : ℕ) (q : ℝ) (k : ℤ) :
    ((mathieuA n q : ℂ) - (k : ℂ) ^ 2) *
        ∫ x in (0 : ℝ)..2 * π, mathieuCe n x q * Complex.cos (k * x) =
      q * ((∫ x in (0 : ℝ)..2 * π, mathieuCe n x q * Complex.cos (((k - 2 : ℤ) : ℂ) * x)) +
        ∫ x in (0 : ℝ)..2 * π, mathieuCe n x q * Complex.cos (((k + 2 : ℤ) : ℂ) * x)) :=
  p1a2_cos_rec (isMathieuSolution_mathieuCe n q) (p1a2_mathieuCe_two_pi n q) k

/-- The recurrence identity for the sine integrals of `se_n` with natural indices. -/
theorem p1a2_se_rec {n : ℕ} (hn : n ≠ 0) (q : ℝ) (k : ℤ) :
    ((mathieuB n q : ℂ) - (k : ℂ) ^ 2) *
        ∫ x in (0 : ℝ)..2 * π, mathieuSe n x q * Complex.sin (k * x) =
      q * ((∫ x in (0 : ℝ)..2 * π, mathieuSe n x q * Complex.sin (((k - 2 : ℤ) : ℂ) * x)) +
        ∫ x in (0 : ℝ)..2 * π, mathieuSe n x q * Complex.sin (((k + 2 : ℤ) : ℂ) * x)) :=
  p1a2_sin_rec (isMathieuSolution_mathieuSe n q) (p1a2_mathieuSe_two_pi hn q) k


/-- `cos((2j+1)(w + π)) = -cos((2j+1)w)`. -/
theorem p1a2_cos_odd_add_pi (j : ℕ) (w : ℂ) :
    Complex.cos (((2 * j + 1 : ℕ) : ℂ) * (w + π)) = -Complex.cos (((2 * j + 1 : ℕ) : ℂ) * w) := by
  rw [show (((2 * j + 1 : ℕ) : ℂ)) * (w + π) = (((2 * j + 1 : ℕ) : ℂ) * w + π) +
    (j : ℤ) * (2 * π) by push_cast; ring, Complex.cos_add_int_mul_two_pi, Complex.cos_add_pi]

/-- `sin((2j+1)(w + π)) = -sin((2j+1)w)`. -/
theorem p1a2_sin_odd_add_pi (j : ℕ) (w : ℂ) :
    Complex.sin (((2 * j + 1 : ℕ) : ℂ) * (w + π)) = -Complex.sin (((2 * j + 1 : ℕ) : ℂ) * w) := by
  rw [show (((2 * j + 1 : ℕ) : ℂ)) * (w + π) = (((2 * j + 1 : ℕ) : ℂ) * w + π) +
    (j : ℤ) * (2 * π) by push_cast; ring, Complex.sin_add_int_mul_two_pi, Complex.sin_add_pi]

/-- `cos(2j(w + π)) = cos(2jw)`. -/
theorem p1a2_cos_even_add_pi (j : ℕ) (w : ℂ) :
    Complex.cos (((2 * j : ℕ) : ℂ) * (w + π)) = Complex.cos (((2 * j : ℕ) : ℂ) * w) := by
  rw [show (((2 * j : ℕ) : ℂ)) * (w + π) = ((2 * j : ℕ) : ℂ) * w +
    (j : ℤ) * (2 * π) by push_cast; ring, Complex.cos_add_int_mul_two_pi]

/-- `sin(2j(w + π)) = sin(2jw)`. -/
theorem p1a2_sin_even_add_pi (j : ℕ) (w : ℂ) :
    Complex.sin (((2 * j : ℕ) : ℂ) * (w + π)) = Complex.sin (((2 * j : ℕ) : ℂ) * w) := by
  rw [show (((2 * j : ℕ) : ℂ)) * (w + π) = ((2 * j : ℕ) : ℂ) * w +
    (j : ℤ) * (2 * π) by push_cast; ring, Complex.sin_add_int_mul_two_pi]

/-- A Fourier coefficient `A^n_m` vanishes when the integrand is `π`-antiperiodic. -/
theorem p1a2_fourierA_eq_zero {n m : ℕ} {q : ℝ}
    (h : ∀ x : ℂ, mathieuCe n (x + π) q * Complex.cos (m * (x + π)) =
      -(mathieuCe n x q * Complex.cos (m * x))) : mathieuFourierA n m q = 0 := by
  rw [mathieuFourierA, p1a2_integral_antiperiodic, mul_zero]
  · have := (isMathieuSolution_mathieuCe n q).differentiable.continuous
    fun_prop
  · intro x; push_cast; exact h x

/-- A Fourier coefficient `B^n_m` vanishes when the integrand is `π`-antiperiodic. -/
theorem p1a2_fourierB_eq_zero {n m : ℕ} {q : ℝ}
    (h : ∀ x : ℂ, mathieuSe n (x + π) q * Complex.sin (m * (x + π)) =
      -(mathieuSe n x q * Complex.sin (m * x))) : mathieuFourierB n m q = 0 := by
  rw [mathieuFourierB, p1a2_integral_antiperiodic, mul_zero]
  · have := (isMathieuSolution_mathieuSe n q).differentiable.continuous
    fun_prop
  · intro x; push_cast; exact h x

/-- `A^{2n}_{2j+1}(q) = 0`. -/
theorem p1a2_fourierA_even_odd (n j : ℕ) (q : ℝ) : mathieuFourierA (2 * n) (2 * j + 1) q = 0 :=
  p1a2_fourierA_eq_zero fun x => by
    rw [mathieuCe_even_add_pi, p1a2_cos_odd_add_pi, mul_neg]

/-- `A^{2n+1}_{2j}(q) = 0`. -/
theorem p1a2_fourierA_odd_even (n j : ℕ) (q : ℝ) : mathieuFourierA (2 * n + 1) (2 * j) q = 0 :=
  p1a2_fourierA_eq_zero fun x => by
    rw [mathieuCe_odd_add_pi, p1a2_cos_even_add_pi, neg_mul]

/-- `B^{2n+1}_{2j}(q) = 0`. -/
theorem p1a2_fourierB_odd_even (n j : ℕ) (q : ℝ) : mathieuFourierB (2 * n + 1) (2 * j) q = 0 :=
  p1a2_fourierB_eq_zero fun x => by
    rw [mathieuSe_odd_add_pi, p1a2_sin_even_add_pi, neg_mul]

/-- `B^{2n+2}_{2j+1}(q) = 0`. -/
theorem p1a2_fourierB_even_odd (n j : ℕ) (q : ℝ) :
    mathieuFourierB (2 * n + 2) (2 * j + 1) q = 0 :=
  p1a2_fourierB_eq_zero fun x => by
    rw [mathieuSe_even_add_pi, p1a2_sin_odd_add_pi, mul_neg]

/-- `B^n_0(q) = 0`. -/
theorem p1a2_fourierB_zero (n : ℕ) (q : ℝ) : mathieuFourierB n 0 q = 0 := by
  simp [mathieuFourierB]

/-- The full cosine series of `ce_n` (all `m`). -/
theorem p1a2_hasSum_mathieuCe (n : ℕ) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierA n m q * Complex.cos (m * z)) (mathieuCe n z q) :=
  p1a2_hasSum_cos (F := fun z => mathieuCe n z q) (isMathieuSolution_mathieuCe n q).differentiable
    (p1a2_mathieuCe_two_pi n q) (fun z => mathieuCe_neg n z q) z

/-- The full sine series of `se_n`, `n ≥ 1` (all `m`). -/
theorem p1a2_hasSum_mathieuSe {n : ℕ} (hn : n ≠ 0) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierB n m q * Complex.sin (m * z)) (mathieuSe n z q) :=
  p1a2_hasSum_sin (F := fun z => mathieuSe n z q) (isMathieuSolution_mathieuSe n q).differentiable
    (p1a2_mathieuSe_two_pi hn q) (fun z => mathieuSe_neg n z q) z

/-- Parseval for `ce_n` over all indices. -/
theorem p1a2_hasSum_mathieuFourierA_sq (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => (if m = 0 then 2 else 1) * mathieuFourierA n m q ^ 2) 1 := by
  have h := p1a2_hasSum_cos_sq (F := fun z => mathieuCe n z q)
    (isMathieuSolution_mathieuCe n q).differentiable (p1a2_mathieuCe_two_pi n q)
    (fun z => mathieuCe_neg n z q)
  rw [integral_mathieuCe_sq] at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [one_div_mul_cancel hπ] at h
  exact h

/-- Parseval for `se_n`, `n ≥ 1`, over all indices. -/
theorem p1a2_hasSum_mathieuFourierB_sq {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    HasSum (fun m : ℕ => mathieuFourierB n m q ^ 2) 1 := by
  have h := p1a2_hasSum_sin_sq (F := fun z => mathieuSe n z q)
    (isMathieuSolution_mathieuSe n q).differentiable (p1a2_mathieuSe_two_pi hn q)
    (fun z => mathieuSe_neg n z q)
  rw [integral_mathieuSe_sq hn] at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [one_div_mul_cancel hπ] at h
  exact h


/-- `∫₀^{2π} cos kx dx = 2π [k = 0]` for integer `k`. -/
theorem p1a2_integral_cos_int (k : ℤ) :
    ∫ x in (0 : ℝ)..2 * π, Complex.cos (k * x) = if k = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.sin (k * x) / k)
        (Complex.cos (k * x)) x := by
      intro x
      have hl : HasDerivAt (fun x : ℝ => (k : ℂ) * (x : ℂ)) k x := by
        simpa using ((hasDerivAt_id (x : ℂ)).const_mul (k : ℂ)).comp_ofReal
      have := ((Complex.hasDerivAt_sin _).comp x hl).div_const (k : ℂ)
      simp only [Function.comp_def] at this
      convert this using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((by fun_prop : Continuous fun x : ℝ => Complex.cos (k * x)).intervalIntegrable _ _)]
    push_cast
    rw [show (k : ℂ) * (2 * π) = 0 + k * (2 * π) by ring, Complex.sin_add_int_mul_two_pi]
    simp

/-- `∫₀^{2π} cos ax cos bx dx` by the product formula. -/
theorem p1a2_integral_cos_mul_cos (a b : ℕ) :
    ∫ x in (0 : ℝ)..2 * π, Complex.cos (a * x) * Complex.cos (b * x) =
      ((if (a : ℤ) - b = 0 then (2 * π : ℂ) else 0) +
        if (a : ℤ) + b = 0 then (2 * π : ℂ) else 0) / 2 := by
  have e : ∀ x : ℝ, Complex.cos (a * x) * Complex.cos (b * x) =
      (Complex.cos ((((a : ℤ) - b : ℤ) : ℂ) * x) +
        Complex.cos ((((a : ℤ) + b : ℤ) : ℂ) * x)) / 2 := by
    intro x; push_cast
    rw [show ((a : ℂ) - b) * x = a * x - b * x by ring,
      show ((a : ℂ) + b) * x = a * x + b * x by ring,
      Complex.cos_sub, Complex.cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun x : ℝ =>
      Complex.cos ((((a : ℤ) - b : ℤ) : ℂ) * x)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ =>
      Complex.cos ((((a : ℤ) + b : ℤ) : ℂ) * x)).intervalIntegrable _ _),
    p1a2_integral_cos_int, p1a2_integral_cos_int]

/-- `∫₀^{2π} sin ax sin bx dx` by the product formula. -/
theorem p1a2_integral_sin_mul_sin (a b : ℕ) :
    ∫ x in (0 : ℝ)..2 * π, Complex.sin (a * x) * Complex.sin (b * x) =
      ((if (a : ℤ) - b = 0 then (2 * π : ℂ) else 0) -
        if (a : ℤ) + b = 0 then (2 * π : ℂ) else 0) / 2 := by
  have e : ∀ x : ℝ, Complex.sin (a * x) * Complex.sin (b * x) =
      (Complex.cos ((((a : ℤ) - b : ℤ) : ℂ) * x) -
        Complex.cos ((((a : ℤ) + b : ℤ) : ℂ) * x)) / 2 := by
    intro x; push_cast
    rw [show ((a : ℂ) - b) * x = a * x - b * x by ring,
      show ((a : ℂ) + b) * x = a * x + b * x by ring,
      Complex.cos_sub, Complex.cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun x : ℝ =>
      Complex.cos ((((a : ℤ) - b : ℤ) : ℂ) * x)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ =>
      Complex.cos ((((a : ℤ) + b : ℤ) : ℂ) * x)).intervalIntegrable _ _),
    p1a2_integral_cos_int, p1a2_integral_cos_int]

/-- `π⁻¹ ∫₀^{2π} cos ax cos bx dx = [a = b]` for `a, b ≥ 1`. -/
theorem p1a2_coef_cos_cos {a b : ℕ} (hb : b ≠ 0) :
    (1 / π : ℂ) * ∫ x in (0 : ℝ)..2 * π, Complex.cos (a * x) * Complex.cos (b * x) =
      if a = b then 1 else 0 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [p1a2_integral_cos_mul_cos]
  have h1 : ¬ (a : ℤ) + b = 0 := by omega
  simp only [h1, ↓reduceIte, add_zero]
  by_cases hab : a = b
  · subst hab; simp only [sub_self, ↓reduceIte]; field_simp
  · have h2 : ¬ (a : ℤ) - b = 0 := by omega
    simp [h2, hab]

/-- `π⁻¹ ∫₀^{2π} sin ax sin bx dx = [a = b]` for `a, b ≥ 1`. -/
theorem p1a2_coef_sin_sin {a b : ℕ} (hb : b ≠ 0) :
    (1 / π : ℂ) * ∫ x in (0 : ℝ)..2 * π, Complex.sin (a * x) * Complex.sin (b * x) =
      if a = b then 1 else 0 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [p1a2_integral_sin_mul_sin]
  have h1 : ¬ (a : ℤ) + b = 0 := by omega
  simp only [h1, ↓reduceIte, sub_zero]
  by_cases hab : a = b
  · subst hab; simp only [sub_self, ↓reduceIte]; field_simp
  · have h2 : ¬ (a : ℤ) - b = 0 := by omega
    simp [h2, hab]

/-- Reflection `x ↦ π/2 - x` preserves integrals over a period. -/
theorem p1a2_integral_half_pi_sub {g : ℝ → ℂ} (hg : Function.Periodic g (2 * π)) :
    ∫ x in (0 : ℝ)..2 * π, g (π / 2 - x) = ∫ x in (0 : ℝ)..2 * π, g x := by
  rw [intervalIntegral.integral_comp_sub_left, sub_zero]
  have h := hg.intervalIntegral_add_eq (π / 2 - 2 * π) 0
  rw [show π / 2 - 2 * π + 2 * π = π / 2 by ring, zero_add] at h
  exact h

/-- `cos(nπ) = (-1)^n` in `ℂ`. -/
theorem p1a2_cos_nat_mul_pi (n : ℕ) : Complex.cos (n * π) = (-1) ^ n := by
  rw [show (n : ℂ) * π = ((n * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    Real.cos_nat_mul_pi]; push_cast; ring

/-- `cos(2m(π/2 - u)) = (-1)^m cos(2mu)`. -/
theorem p1a2_cos_even_half_pi_sub (m : ℕ) (u : ℂ) :
    Complex.cos (((2 * m : ℕ) : ℂ) * (π / 2 - u)) =
      (-1) ^ m * Complex.cos (((2 * m : ℕ) : ℂ) * u) := by
  rw [show ((2 * m : ℕ) : ℂ) * (π / 2 - u) = m * π - ((2 * m : ℕ) : ℂ) * u by push_cast; ring,
    Complex.cos_sub, p1a2_cos_nat_mul_pi, Complex.sin_nat_mul_pi]; ring

/-- `sin(2m(π/2 - u)) = -(-1)^m sin(2mu)`. -/
theorem p1a2_sin_even_half_pi_sub (m : ℕ) (u : ℂ) :
    Complex.sin (((2 * m : ℕ) : ℂ) * (π / 2 - u)) =
      -((-1) ^ m * Complex.sin (((2 * m : ℕ) : ℂ) * u)) := by
  rw [show ((2 * m : ℕ) : ℂ) * (π / 2 - u) = m * π - ((2 * m : ℕ) : ℂ) * u by push_cast; ring,
    Complex.sin_sub, p1a2_cos_nat_mul_pi, Complex.sin_nat_mul_pi]; ring

/-- `cos((2m+1)(π/2 - u)) = (-1)^m sin((2m+1)u)`. -/
theorem p1a2_cos_odd_half_pi_sub (m : ℕ) (u : ℂ) :
    Complex.cos (((2 * m + 1 : ℕ) : ℂ) * (π / 2 - u)) =
      (-1) ^ m * Complex.sin (((2 * m + 1 : ℕ) : ℂ) * u) := by
  rw [show ((2 * m + 1 : ℕ) : ℂ) * (π / 2 - u) = (m * π + π / 2) - ((2 * m + 1 : ℕ) : ℂ) * u by
    push_cast; ring, Complex.cos_sub, Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two,
    p1a2_cos_nat_mul_pi, Complex.sin_nat_mul_pi]; ring

/-- `sin((2m+1)(π/2 - u)) = (-1)^m cos((2m+1)u)`. -/
theorem p1a2_sin_odd_half_pi_sub (m : ℕ) (u : ℂ) :
    Complex.sin (((2 * m + 1 : ℕ) : ℂ) * (π / 2 - u)) =
      (-1) ^ m * Complex.cos (((2 * m + 1 : ℕ) : ℂ) * u) := by
  rw [show ((2 * m + 1 : ℕ) : ℂ) * (π / 2 - u) = (m * π + π / 2) - ((2 * m + 1 : ℕ) : ℂ) * u by
    push_cast; ring, Complex.sin_sub, Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two,
    p1a2_cos_nat_mul_pi, Complex.sin_nat_mul_pi]; ring

/-- `(-1)^(n - m : ℤ) = (-1)^n (-1)^m` in `ℂ`. -/
theorem p1a2_neg_one_zpow_sub (n m : ℕ) :
    ((-1 : ℂ) ^ ((n : ℤ) - m)) = (-1) ^ n * (-1) ^ m := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  rw [div_eq_mul_inv]
  congr 1
  rcases neg_one_pow_eq_or ℂ m with h | h <;> rw [h] <;> norm_num

/-- Reflection of a Fourier-type integral: if `f(x, -q) k(x) = c g(π/2 - x)` with `g`
`2π`-periodic, the integral over a period is `c ∫ g`. -/
theorem p1a2_integral_reflect {f g : ℝ → ℂ} (c : ℂ) (hg : Function.Periodic g (2 * π))
    (h : ∀ x : ℝ, f x = c * g (π / 2 - x)) :
    ∫ x in (0 : ℝ)..2 * π, f x = c * ∫ x in (0 : ℝ)..2 * π, g x := by
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, p1a2_integral_half_pi_sub hg]

/-! ### Fourier expansions (§28.4(i)) -/

/-- **DLMF 28.4.1**: `ce_{2n}(z, q) = ∑_{m ≥ 0} A^{2n}_{2m}(q) cos 2mz`, real `q`, `z ∈ ℂ`. -/
@[dlmf 28.4.E1]
theorem hasSum_mathieuCe_even (n : ℕ) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierA (2 * n) (2 * m) q * Complex.cos (2 * m * z))
      (mathieuCe (2 * n) z q) := by
  have h := p1a2_hasSum_mathieuCe (2 * n) q z
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m)
    (fun a b h => by simpa using h) ?_)] at h
  · convert h using 2 with m; simp
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · exact absurd ⟨j, rfl⟩ hx
    · rw [p1a2_fourierA_even_odd, zero_mul]

/-- **DLMF 28.4.2**: `ce_{2n+1}(z, q) = ∑_{m ≥ 0} A^{2n+1}_{2m+1}(q) cos(2m+1)z`. -/
@[dlmf 28.4.E2]
theorem hasSum_mathieuCe_odd (n : ℕ) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierA (2 * n + 1) (2 * m + 1) q *
      Complex.cos ((2 * m + 1) * z)) (mathieuCe (2 * n + 1) z q) := by
  have h := p1a2_hasSum_mathieuCe (2 * n + 1) q z
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 1)
    (fun a b h => by simpa using h) ?_)] at h
  · convert h using 2 with m; simp
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · rw [p1a2_fourierA_odd_even, zero_mul]
    · exact absurd ⟨j, rfl⟩ hx

/-- **DLMF 28.4.3**: `se_{2n+1}(z, q) = ∑_{m ≥ 0} B^{2n+1}_{2m+1}(q) sin(2m+1)z`. -/
@[dlmf 28.4.E3]
theorem hasSum_mathieuSe_odd (n : ℕ) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierB (2 * n + 1) (2 * m + 1) q *
      Complex.sin ((2 * m + 1) * z)) (mathieuSe (2 * n + 1) z q) := by
  have h := p1a2_hasSum_mathieuSe (n := 2 * n + 1) (by omega) q z
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 1)
    (fun a b h => by simpa using h) ?_)] at h
  · convert h using 2 with m; simp
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · rw [p1a2_fourierB_odd_even, zero_mul]
    · exact absurd ⟨j, rfl⟩ hx

/-- **DLMF 28.4.4**: `se_{2n+2}(z, q) = ∑_{m ≥ 0} B^{2n+2}_{2m+2}(q) sin(2m+2)z`. -/
@[dlmf 28.4.E4]
theorem hasSum_mathieuSe_even (n : ℕ) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierB (2 * n + 2) (2 * m + 2) q *
      Complex.sin ((2 * m + 2) * z)) (mathieuSe (2 * n + 2) z q) := by
  have h := p1a2_hasSum_mathieuSe (n := 2 * n + 2) (by omega) q z
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 2)
    (fun a b h => by simpa using h) ?_)] at h
  · convert h using 2 with m; simp
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · rcases j with _ | j
      · rw [p1a2_fourierB_zero, zero_mul]
      · exact absurd ⟨j, by ring⟩ hx
    · rw [p1a2_fourierB_even_odd, zero_mul]

/-- `‖e^{iw}‖ ≤ e^{|ℑw|}`. -/
theorem p2f_norm_exp_mul_I_le (w : ℂ) : ‖Complex.exp (w * I)‖ ≤ Real.exp |w.im| := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub]
  exact neg_le_abs _

/-- `‖cos w‖ ≤ e^{|ℑw|}`. -/
theorem p2f_norm_cos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  have h1 := p2f_norm_exp_mul_I_le w
  have h2 := p2f_norm_exp_mul_I_le (-w)
  rw [show -w * I = -(w * I) by ring] at h2
  simp only [neg_im, abs_neg] at h2
  rw [norm_div, Complex.norm_ofNat, show -w * I = -(w * I) by ring]
  have := norm_add_le (Complex.exp (w * I)) (Complex.exp (-(w * I)))
  linarith

/-- `‖sin w‖ ≤ e^{|ℑw|}`. -/
theorem p2f_norm_sin_le (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin]
  have h1 := p2f_norm_exp_mul_I_le w
  have h2 := p2f_norm_exp_mul_I_le (-w)
  rw [show -w * I = -(w * I) by ring] at h2
  simp only [neg_im, abs_neg] at h2
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    show -w * I = -(w * I) by ring]
  have := norm_sub_le (Complex.exp (-(w * I))) (Complex.exp (w * I))
  linarith

/-- Absolute and locally uniform convergence of a trigonometric series with rapidly decaying
coefficients. -/
theorem p2f_trig_series {c : ℕ → ℂ} {g : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hc : ∀ R : ℝ, ∃ C, 0 ≤ C ∧ ∀ m : ℕ, ‖c m‖ ≤ C * Real.exp (-(R * m)))
    (hg : ∀ m z, ‖g m z‖ ≤ Real.exp (m * |z.im|)) (hF : ∀ z, HasSum (fun m => c m * g m z) (F z)) :
    (∀ z, Summable fun m => ‖c m * g m z‖) ∧
      TendstoLocallyUniformly (fun N z => ∑ m ∈ Finset.range N, c m * g m z) F atTop := by
  have key : ∀ Y : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ m z, |z.im| ≤ Y → ‖c m * g m z‖ ≤ u m := by
    intro Y
    obtain ⟨C, hC0, hC⟩ := hc (Y + 1)
    refine ⟨fun m => C * Real.exp (-(m : ℝ)), Real.summable_exp_neg_nat.mul_left C, ?_⟩
    intro m z hz
    rw [norm_mul]
    calc ‖c m‖ * ‖g m z‖ ≤ (C * Real.exp (-((Y + 1) * m))) * Real.exp (m * Y) := by
          apply mul_le_mul (hC m) ((hg m z).trans (Real.exp_le_exp.mpr ?_)) (norm_nonneg _)
            (by positivity)
          exact mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg m)
      _ = C * Real.exp (-(m : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨u, hu, hb⟩ := key |z.im|
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => hb m z le_rfl) hu
  · refine tendstoLocallyUniformly_of_forall_exists_nhds fun z₀ => ?_
    obtain ⟨u, hu, hb⟩ := key (|z₀.im| + 1)
    refine ⟨Metric.ball z₀ 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
    have h := tendstoUniformlyOn_tsum_nat hu (f := fun m z => c m * g m z)
      (s := Metric.ball z₀ 1) (fun m z hz => hb m z ?_)
    · refine h.congr_right fun z _ => (hF z).tsum_eq
    · have hz' : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      have := abs_im_le_norm (z - z₀)
      rw [sub_im] at this
      have := abs_sub_abs_le_abs_sub z.im z₀.im
      linarith

/-- Exponential decay of `A^n_m(q)` in `m`. -/
theorem p2f_fourierA_decay (n : ℕ) (q : ℝ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ m : ℕ, ‖mathieuFourierA n m q‖ ≤ C * Real.exp (-(R * m)) := by
  obtain ⟨C, hC0, hC⟩ := p2f_cos_coeff_decay (F := fun z => mathieuCe n z q)
    (isMathieuSolution_mathieuCe n q).differentiable (p1a2_mathieuCe_two_pi n q)
    (fun z => mathieuCe_neg n z q) R
  refine ⟨C, hC0, fun m => ?_⟩
  rw [mathieuFourierA, norm_mul]
  have hp : ‖(if m = 0 then 1 / (2 * π) else 1 / π : ℂ)‖ ≤ 1 := by
    have := Real.pi_gt_three
    split_ifs
    · rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_one (by positivity)]; linarith
    · rw [norm_div, norm_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_one (by positivity)]; linarith
  calc _ ≤ 1 * (C * Real.exp (-(R * m))) :=
        mul_le_mul hp (hC m) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Exponential decay of `B^n_m(q)` in `m`, `n ≥ 1`. -/
theorem p2f_fourierB_decay {n : ℕ} (hn : n ≠ 0) (q : ℝ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ m : ℕ, ‖mathieuFourierB n m q‖ ≤ C * Real.exp (-(R * m)) := by
  obtain ⟨C, hC0, hC⟩ := p2f_sin_coeff_decay (F := fun z => mathieuSe n z q)
    (isMathieuSolution_mathieuSe n q).differentiable (p1a2_mathieuSe_two_pi hn q)
    (fun z => mathieuSe_neg n z q) R
  refine ⟨C, hC0, fun m => ?_⟩
  rw [mathieuFourierB, norm_mul]
  have hp : ‖(1 / π : ℂ)‖ ≤ 1 := by
    have := Real.pi_gt_three
    rw [norm_div, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_one (by positivity)]; linarith
  calc _ ≤ 1 * (C * Real.exp (-(R * m))) :=
        mul_le_mul hp (hC m) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Absolute and locally uniform convergence** (DLMF §28.4(i)): the Fourier series
`∑ₘ A^n_m(q) cos mz` and `∑ₘ B^n_m(q) sin mz` converge absolutely and uniformly on compact
subsets of `ℂ`; the sine series only for `n ≥ 1`, since DLMF has no `se_0` (28.4.3–4 index
`se_{2n+1}`, `se_{2n+2}`). The guard `n ≠ 0` on the second conjunct was added on 2026-10-26
(transcription defect: for the junk `se_0` the series diverges off the real axis). -/
@[dlmf 28.4.i]
theorem mathieu_fourier_locallyUniform (n : ℕ) (q : ℝ) :
    (∀ z : ℂ, Summable fun m : ℕ => ‖mathieuFourierA n m q * Complex.cos (m * z)‖) ∧
      (n ≠ 0 → ∀ z : ℂ, Summable fun m : ℕ => ‖mathieuFourierB n m q * Complex.sin (m * z)‖) ∧
      TendstoLocallyUniformly (fun N z => ∑ m ∈ Finset.range N,
        mathieuFourierA n m q * Complex.cos (m * z)) (fun z => mathieuCe n z q) atTop ∧
      (n ≠ 0 → TendstoLocallyUniformly (fun N z => ∑ m ∈ Finset.range N,
        mathieuFourierB n m q * Complex.sin (m * z)) (fun z => mathieuSe n z q) atTop) := by
  have hg : ∀ (m : ℕ) (z : ℂ), ‖Complex.cos (m * z)‖ ≤ Real.exp (m * |z.im|) := fun m z => by
    refine (p2f_norm_cos_le _).trans (le_of_eq ?_)
    rw [show ((m : ℂ) * z).im = m * z.im by simp, abs_mul, Nat.abs_cast]
  have hg' : ∀ (m : ℕ) (z : ℂ), ‖Complex.sin (m * z)‖ ≤ Real.exp (m * |z.im|) := fun m z => by
    refine (p2f_norm_sin_le _).trans (le_of_eq ?_)
    rw [show ((m : ℂ) * z).im = m * z.im by simp, abs_mul, Nat.abs_cast]
  have hA := p2f_trig_series (g := fun m z => Complex.cos (m * z)) (p2f_fourierA_decay n q) hg
    (p1a2_hasSum_mathieuCe n q)
  have hB : n ≠ 0 → _ := fun hn => p2f_trig_series (g := fun m z => Complex.sin (m * z))
    (p2f_fourierB_decay hn q) hg' (p1a2_hasSum_mathieuSe hn q)
  exact ⟨hA.1, fun hn => (hB hn).1, hA.2, fun hn => (hB hn).2⟩


/-! ### Recurrence relations (§28.4(ii)) -/

/-- **DLMF 28.4.5** (first line): `a A_0 - q A_2 = 0`, `a = a_{2n}(q)`,
`A_{2m} = A^{2n}_{2m}(q)`. -/
@[dlmf 28.4.E5]
theorem mathieuFourierA_even_rec_zero (n : ℕ) (q : ℝ) :
    (mathieuA (2 * n) q : ℂ) * mathieuFourierA (2 * n) 0 q -
      q * mathieuFourierA (2 * n) 2 q = 0 := by
  have h := p1a2_ce_rec (2 * n) q 0
  simp only [mathieuFourierA]
  norm_num at h ⊢
  field_simp
  linear_combination h

/-- **DLMF 28.4.5** (second line): `(a - 4) A_2 - q(2A_0 + A_4) = 0`, `a = a_{2n}(q)`. -/
@[dlmf 28.4.E5]
theorem mathieuFourierA_even_rec_one (n : ℕ) (q : ℝ) :
    ((mathieuA (2 * n) q : ℂ) - 4) * mathieuFourierA (2 * n) 2 q -
      q * (2 * mathieuFourierA (2 * n) 0 q + mathieuFourierA (2 * n) 4 q) = 0 := by
  have h := p1a2_ce_rec (2 * n) q 2
  simp only [mathieuFourierA]
  norm_num at h ⊢
  field_simp
  linear_combination h

/-- **DLMF 28.4.5** (general line): `(a - 4m²) A_{2m} - q(A_{2m-2} + A_{2m+2}) = 0`, `m ≥ 2`. -/
@[dlmf 28.4.E5]
theorem mathieuFourierA_even_rec (n : ℕ) (q : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    ((mathieuA (2 * n) q : ℂ) - 4 * m ^ 2) * mathieuFourierA (2 * n) (2 * m) q -
      q * (mathieuFourierA (2 * n) (2 * m - 2) q + mathieuFourierA (2 * n) (2 * m + 2) q) =
      0 := by
  have h := p1a2_ce_rec (2 * n) q (2 * m)
  simp only [mathieuFourierA, (show 2 * m ≠ 0 by omega), ↓reduceIte,
    (show 2 * m - 2 ≠ 0 by omega), (show 2 * m + 2 ≠ 0 by omega)]
  have e : (((2 * m - 2 : ℕ) : ℂ)) = (((2 * m : ℤ) - 2 : ℤ) : ℂ) := by
    push_cast [Nat.cast_sub (show 2 ≤ 2 * m by omega)]; ring
  rw [e]
  push_cast at h ⊢
  linear_combination (1 / π : ℂ) * h

/-- **DLMF 28.4.6** (first line): `(a - 1 - q) A_1 - q A_3 = 0`, `a = a_{2n+1}(q)`. -/
@[dlmf 28.4.E6]
theorem mathieuFourierA_odd_rec_zero (n : ℕ) (q : ℝ) :
    ((mathieuA (2 * n + 1) q : ℂ) - 1 - q) * mathieuFourierA (2 * n + 1) 1 q -
      q * mathieuFourierA (2 * n + 1) 3 q = 0 := by
  have h := p1a2_ce_rec (2 * n + 1) q 1
  simp only [mathieuFourierA]
  norm_num at h ⊢
  linear_combination (1 / π : ℂ) * h

/-- **DLMF 28.4.6** (general line):
`(a - (2m+1)²) A_{2m+1} - q(A_{2m-1} + A_{2m+3}) = 0`, `m ≥ 1`, `a = a_{2n+1}(q)`. -/
@[dlmf 28.4.E6]
theorem mathieuFourierA_odd_rec (n : ℕ) (q : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ((mathieuA (2 * n + 1) q : ℂ) - (2 * m + 1) ^ 2) * mathieuFourierA (2 * n + 1) (2 * m + 1) q -
      q * (mathieuFourierA (2 * n + 1) (2 * m - 1) q +
        mathieuFourierA (2 * n + 1) (2 * m + 3) q) = 0 := by
  have h := p1a2_ce_rec (2 * n + 1) q (2 * m + 1)
  simp only [mathieuFourierA, (show 2 * m + 1 ≠ 0 by omega), ↓reduceIte,
    (show 2 * m - 1 ≠ 0 by omega), (show 2 * m + 3 ≠ 0 by omega)]
  have e : (((2 * m - 1 : ℕ) : ℂ)) = (((2 * m + 1 : ℤ) - 2 : ℤ) : ℂ) := by
    push_cast [Nat.cast_sub (show 1 ≤ 2 * m by omega)]; ring
  rw [e]
  push_cast at h ⊢
  rw [show (2 * (m : ℂ) + 1 + 2) = 2 * m + 3 by ring] at h
  linear_combination (1 / π : ℂ) * h

/-- **DLMF 28.4.7** (first line): `(a - 1 + q) B_1 - q B_3 = 0`, `a = b_{2n+1}(q)`. -/
@[dlmf 28.4.E7]
theorem mathieuFourierB_odd_rec_zero (n : ℕ) (q : ℝ) :
    ((mathieuB (2 * n + 1) q : ℂ) - 1 + q) * mathieuFourierB (2 * n + 1) 1 q -
      q * mathieuFourierB (2 * n + 1) 3 q = 0 := by
  have h := p1a2_se_rec (n := 2 * n + 1) (by omega) q 1
  simp only [mathieuFourierB]
  norm_num at h ⊢
  linear_combination (1 / π : ℂ) * h

/-- **DLMF 28.4.7** (general line):
`(a - (2m+1)²) B_{2m+1} - q(B_{2m-1} + B_{2m+3}) = 0`, `m ≥ 1`, `a = b_{2n+1}(q)`. -/
@[dlmf 28.4.E7]
theorem mathieuFourierB_odd_rec (n : ℕ) (q : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ((mathieuB (2 * n + 1) q : ℂ) - (2 * m + 1) ^ 2) * mathieuFourierB (2 * n + 1) (2 * m + 1) q -
      q * (mathieuFourierB (2 * n + 1) (2 * m - 1) q +
        mathieuFourierB (2 * n + 1) (2 * m + 3) q) = 0 := by
  have h := p1a2_se_rec (n := 2 * n + 1) (by omega) q (2 * m + 1)
  simp only [mathieuFourierB]
  have e : (((2 * m - 1 : ℕ) : ℂ)) = (((2 * m + 1 : ℤ) - 2 : ℤ) : ℂ) := by
    push_cast [Nat.cast_sub (show 1 ≤ 2 * m by omega)]; ring
  rw [e]
  push_cast at h ⊢
  rw [show (2 * (m : ℂ) + 1 + 2) = 2 * m + 3 by ring] at h
  linear_combination (1 / π : ℂ) * h

/-- **DLMF 28.4.8** (first line): `(a - 4) B_2 - q B_4 = 0`, `a = b_{2n+2}(q)`. -/
@[dlmf 28.4.E8]
theorem mathieuFourierB_even_rec_zero (n : ℕ) (q : ℝ) :
    ((mathieuB (2 * n + 2) q : ℂ) - 4) * mathieuFourierB (2 * n + 2) 2 q -
      q * mathieuFourierB (2 * n + 2) 4 q = 0 := by
  have h := p1a2_se_rec (n := 2 * n + 2) (by omega) q 2
  simp only [mathieuFourierB]
  norm_num at h ⊢
  linear_combination (1 / π : ℂ) * h

/-- **DLMF 28.4.8** (general line): `(a - 4m²) B_{2m} - q(B_{2m-2} + B_{2m+2}) = 0`, `m ≥ 2`,
`a = b_{2n+2}(q)`. (DLMF's last label `B_{2m+2} = B^{2n+2}_{2m+2}(q)` means
`B_{2m} = B^{2n+2}_{2m}(q)`.) -/
@[dlmf 28.4.E8]
theorem mathieuFourierB_even_rec (n : ℕ) (q : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    ((mathieuB (2 * n + 2) q : ℂ) - 4 * m ^ 2) * mathieuFourierB (2 * n + 2) (2 * m) q -
      q * (mathieuFourierB (2 * n + 2) (2 * m - 2) q +
        mathieuFourierB (2 * n + 2) (2 * m + 2) q) = 0 := by
  have h := p1a2_se_rec (n := 2 * n + 2) (by omega) q (2 * m)
  simp only [mathieuFourierB]
  have e : (((2 * m - 2 : ℕ) : ℂ)) = (((2 * m : ℤ) - 2 : ℤ) : ℂ) := by
    push_cast [Nat.cast_sub (show 2 ≤ 2 * m by omega)]; ring
  rw [e]
  push_cast at h ⊢
  linear_combination (1 / π : ℂ) * h

/-! ### Normalization (§28.4(iii)) -/

/-- **DLMF 28.4.9**: `2 (A^{2n}_0)² + ∑_{m ≥ 1} (A^{2n}_{2m})² = 1`. -/
@[dlmf 28.4.E9]
theorem hasSum_mathieuFourierA_even_sq (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => (if m = 0 then 2 else 1) * mathieuFourierA (2 * n) (2 * m) q ^ 2) 1 := by
  have h := p1a2_hasSum_mathieuFourierA_sq (2 * n) q
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m)
    (fun a b h => by simpa using h) ?_)] at h
  · convert h using 2 with m; simp
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · exact absurd ⟨j, rfl⟩ hx
    · rw [p1a2_fourierA_even_odd]; simp

/-- **DLMF 28.4.10**: `∑_{m ≥ 0} (A^{2n+1}_{2m+1})² = 1`. -/
@[dlmf 28.4.E10]
theorem hasSum_mathieuFourierA_odd_sq (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => mathieuFourierA (2 * n + 1) (2 * m + 1) q ^ 2) 1 := by
  have h := p1a2_hasSum_mathieuFourierA_sq (2 * n + 1) q
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 1)
    (fun a b h => by simpa using h) ?_)] at h
  · convert h using 2 with m; simp
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · rw [p1a2_fourierA_odd_even]; simp
    · exact absurd ⟨j, rfl⟩ hx

/-- **DLMF 28.4.11**: `∑_{m ≥ 0} (B^{2n+1}_{2m+1})² = 1`. -/
@[dlmf 28.4.E11]
theorem hasSum_mathieuFourierB_odd_sq (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => mathieuFourierB (2 * n + 1) (2 * m + 1) q ^ 2) 1 := by
  have h := p1a2_hasSum_mathieuFourierB_sq (n := 2 * n + 1) (by omega) q
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 1)
    (fun a b h => by simpa using h) ?_)] at h
  · exact h
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · rw [p1a2_fourierB_odd_even]; simp
    · exact absurd ⟨j, rfl⟩ hx

/-- **DLMF 28.4.12**: `∑_{m ≥ 0} (B^{2n+2}_{2m+2})² = 1`. -/
@[dlmf 28.4.E12]
theorem hasSum_mathieuFourierB_even_sq (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => mathieuFourierB (2 * n + 2) (2 * m + 2) q ^ 2) 1 := by
  have h := p1a2_hasSum_mathieuFourierB_sq (n := 2 * n + 2) (by omega) q
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 2)
    (fun a b h => by simpa using h) ?_)] at h
  · exact h
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · rcases j with _ | j
      · rw [p1a2_fourierB_zero]; simp
      · exact absurd ⟨j, by ring⟩ hx
    · rw [p1a2_fourierB_even_odd]; simp

/-- **Sign convention** (DLMF §28.4(iii)): the sign ambiguity left by 28.4.9–28.4.12 is resolved
by 28.4.13–28.4.16 at `q = 0` and by continuity in `q`; for real `q` this is equivalent to the
convention `ce_n(0, q) = ∑ₘ A^n_m(q) > 0` and `se_n'(0, q) = ∑ₘ m B^n_m(q) > 0` of
`mathieuCe`, `mathieuSe`. -/
@[dlmf 28.4.iii]
theorem mathieuFourier_sign (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => mathieuFourierA n m q) (mathieuCe n 0 q) ∧
      (n ≠ 0 → HasSum (fun m : ℕ => (m : ℂ) * mathieuFourierB n m q)
        (deriv (fun z => mathieuSe n z q) 0)) ∧
      0 < (mathieuCe n 0 q).re ∧ (mathieuCe n 0 q).im = 0 := by
  refine ⟨?_, fun hn => ?_, ?_, ?_⟩
  · simpa using p1a2_hasSum_mathieuCe n q 0
  · exact p1a2_hasSum_deriv_sin (F := fun z => mathieuSe n z q)
      (isMathieuSolution_mathieuSe n q).differentiable (p1a2_mathieuSe_two_pi hn q)
      (fun z => mathieuSe_neg n z q)
  · rw [mathieuCe_zero, Complex.ofReal_re]; exact mathieuCeZero_pos n q
  · rw [mathieuCe_zero, Complex.ofReal_im]

/-! ### The case `q = 0` (§28.4(iv)) -/

/-- **DLMF 28.4.13**: `A^0_0(0) = 1/√2`, `A^{2n}_{2n}(0) = 1` (`n > 0`), `A^{2n}_{2m}(0) = 0`
(`n ≠ m`). -/
@[dlmf 28.4.E13]
theorem mathieuFourierA_even_q_zero (n m : ℕ) :
    mathieuFourierA (2 * n) (2 * m) 0 =
      if n = m then (if n = 0 then 1 / Real.sqrt 2 else 1) else 0 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mathieuFourierA, Nat.mul_zero, mathieuCe_zero_zero]
    rw [intervalIntegral.integral_const_mul]
    have := p1a2_integral_cos_int ((2 * m : ℕ) : ℤ)
    push_cast at this ⊢
    rw [this]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp; field_simp
    · simp [hm.ne', hm.ne]
  · simp only [mathieuFourierA]
    simp_rw [mathieuCe_q_zero (by omega : 2 * n ≠ 0)]
    rw [p1a2_integral_cos_mul_cos]
    have h1 : ¬ ((2 * n : ℕ) : ℤ) + ((2 * m : ℕ) : ℤ) = 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have h2n : 2 * n ≠ 0 := by omega
    simp only [h1, ↓reduceIte]
    by_cases hnm : n = m
    · subst hnm
      simp only [sub_self, ↓reduceIte, h2n, hn0, add_zero]
      push_cast
      field_simp
    · have h2 : ¬ (2 * (n : ℤ) - 2 * m = 0) := by omega
      simp [h2, hnm]

/-- **DLMF 28.4.14**: `A^{2n+1}_{2n+1}(0) = 1`, `A^{2n+1}_{2m+1}(0) = 0` (`n ≠ m`). -/
@[dlmf 28.4.E14]
theorem mathieuFourierA_odd_q_zero (n m : ℕ) :
    mathieuFourierA (2 * n + 1) (2 * m + 1) 0 = if n = m then 1 else 0 := by
  simp only [mathieuFourierA, show 2 * m + 1 ≠ 0 by omega, ↓reduceIte]
  simp_rw [mathieuCe_q_zero (by omega : 2 * n + 1 ≠ 0)]
  rw [p1a2_coef_cos_cos (by omega)]
  simp

/-- **DLMF 28.4.15**: `B^{2n+1}_{2n+1}(0) = 1`, `B^{2n+1}_{2m+1}(0) = 0` (`n ≠ m`). -/
@[dlmf 28.4.E15]
theorem mathieuFourierB_odd_q_zero (n m : ℕ) :
    mathieuFourierB (2 * n + 1) (2 * m + 1) 0 = if n = m then 1 else 0 := by
  simp only [mathieuFourierB]
  simp_rw [mathieuSe_q_zero (by omega : 2 * n + 1 ≠ 0)]
  rw [p1a2_coef_sin_sin (by omega)]
  simp

/-- **DLMF 28.4.16**: `B^{2n+2}_{2n+2}(0) = 1`, `B^{2n+2}_{2m+2}(0) = 0` (`n ≠ m`). -/
@[dlmf 28.4.E16]
theorem mathieuFourierB_even_q_zero (n m : ℕ) :
    mathieuFourierB (2 * n + 2) (2 * m + 2) 0 = if n = m then 1 else 0 := by
  simp only [mathieuFourierB]
  simp_rw [mathieuSe_q_zero (by omega : 2 * n + 2 ≠ 0)]
  rw [p1a2_coef_sin_sin (by omega)]
  simp

/-! ### Change of sign of `q` (§28.4(v)) -/

/-- **DLMF 28.4.17**: `A^{2n}_{2m}(-q) = (-1)^{n-m} A^{2n}_{2m}(q)`. -/
@[dlmf 28.4.E17]
theorem mathieuFourierA_even_neg_q (n m : ℕ) (q : ℝ) :
    mathieuFourierA (2 * n) (2 * m) (-q) =
      (-1) ^ ((n : ℤ) - m) * mathieuFourierA (2 * n) (2 * m) q := by
  simp only [mathieuFourierA]
  rw [p1a2_integral_reflect ((-1) ^ n * (-1) ^ m)
    (g := fun x : ℝ => mathieuCe (2 * n) x q * Complex.cos (((2 * m : ℕ) : ℂ) * x))]
  · rw [p1a2_neg_one_zpow_sub]; ring
  · intro y; simp only; push_cast
    rw [p1a2_mathieuCe_two_pi, show 2 * (m : ℂ) * (y + 2 * π) =
      2 * m * y + ((2 * m : ℕ) : ℤ) * (2 * π) by
      push_cast; ring, Complex.cos_add_int_mul_two_pi]
  · intro x
    have e := p1a2_cos_even_half_pi_sub m (π / 2 - x)
    rw [sub_sub_cancel] at e
    rw [mathieuCe_even_neg_q, e]
    push_cast; ring

/-- **DLMF 28.4.18**: `B^{2n+2}_{2m+2}(-q) = (-1)^{n-m} B^{2n+2}_{2m+2}(q)`. -/
@[dlmf 28.4.E18]
theorem mathieuFourierB_even_neg_q (n m : ℕ) (q : ℝ) :
    mathieuFourierB (2 * n + 2) (2 * m + 2) (-q) =
      (-1) ^ ((n : ℤ) - m) * mathieuFourierB (2 * n + 2) (2 * m + 2) q := by
  simp only [mathieuFourierB]
  rw [p1a2_integral_reflect ((-1) ^ n * (-1) ^ m)
    (g := fun x : ℝ => mathieuSe (2 * n + 2) x q * Complex.sin (((2 * m + 2 : ℕ) : ℂ) * x))]
  · rw [p1a2_neg_one_zpow_sub]; ring
  · intro y; simp only; push_cast
    rw [p1a2_mathieuSe_two_pi (by omega), show (2 * (m : ℂ) + 2) * (y + 2 * π) =
      (2 * m + 2) * y + ((2 * m + 2 : ℕ) : ℤ) * (2 * π) by push_cast; ring,
      Complex.sin_add_int_mul_two_pi]
  · intro x
    have e := p1a2_sin_even_half_pi_sub (m + 1) (π / 2 - x)
    rw [sub_sub_cancel, show ((2 * (m + 1) : ℕ) : ℂ) = ((2 * m + 2 : ℕ) : ℂ) by push_cast; ring]
      at e
    rw [mathieuSe_even_neg_q, e]
    push_cast; ring

/-- **DLMF 28.4.19**: `A^{2n+1}_{2m+1}(-q) = (-1)^{n-m} B^{2n+1}_{2m+1}(q)`. -/
@[dlmf 28.4.E19]
theorem mathieuFourierA_odd_neg_q (n m : ℕ) (q : ℝ) :
    mathieuFourierA (2 * n + 1) (2 * m + 1) (-q) =
      (-1) ^ ((n : ℤ) - m) * mathieuFourierB (2 * n + 1) (2 * m + 1) q := by
  simp only [mathieuFourierA, mathieuFourierB, show 2 * m + 1 ≠ 0 by omega, ↓reduceIte]
  rw [p1a2_integral_reflect ((-1) ^ n * (-1) ^ m)
    (g := fun x : ℝ => mathieuSe (2 * n + 1) x q * Complex.sin (((2 * m + 1 : ℕ) : ℂ) * x))]
  · rw [p1a2_neg_one_zpow_sub]; ring
  · intro y; simp only; push_cast
    rw [p1a2_mathieuSe_two_pi (by omega), show (2 * (m : ℂ) + 1) * (y + 2 * π) =
      (2 * m + 1) * y + ((2 * m + 1 : ℕ) : ℤ) * (2 * π) by push_cast; ring,
      Complex.sin_add_int_mul_two_pi]
  · intro x
    have e := p1a2_cos_odd_half_pi_sub m (π / 2 - x)
    rw [sub_sub_cancel] at e
    rw [mathieuCe_odd_neg_q, e]
    push_cast; ring

/-- **DLMF 28.4.20**: `B^{2n+1}_{2m+1}(-q) = (-1)^{n-m} A^{2n+1}_{2m+1}(q)`. -/
@[dlmf 28.4.E20]
theorem mathieuFourierB_odd_neg_q (n m : ℕ) (q : ℝ) :
    mathieuFourierB (2 * n + 1) (2 * m + 1) (-q) =
      (-1) ^ ((n : ℤ) - m) * mathieuFourierA (2 * n + 1) (2 * m + 1) q := by
  simp only [mathieuFourierA, mathieuFourierB, show 2 * m + 1 ≠ 0 by omega, ↓reduceIte]
  rw [p1a2_integral_reflect ((-1) ^ n * (-1) ^ m)
    (g := fun x : ℝ => mathieuCe (2 * n + 1) x q * Complex.cos (((2 * m + 1 : ℕ) : ℂ) * x))]
  · rw [p1a2_neg_one_zpow_sub]; ring
  · intro y; simp only; push_cast
    rw [p1a2_mathieuCe_two_pi, show (2 * (m : ℂ) + 1) * (y + 2 * π) =
      (2 * m + 1) * y + ((2 * m + 1 : ℕ) : ℤ) * (2 * π) by push_cast; ring,
      Complex.cos_add_int_mul_two_pi]
  · intro x
    have e := p1a2_sin_odd_half_pi_sub m (π / 2 - x)
    rw [sub_sub_cancel] at e
    rw [mathieuSe_odd_neg_q, e]
    push_cast; ring

/-! ### Behavior for small `q` (§28.4(vi)) -/

/-- **DLMF 28.4.21**: for fixed `s ≥ 1`,
`A^0_{2s}(q) = ((-1)^s 2/(s!)² (q/4)^s + O(q^{s+2})) A^0_0(q)` as `q → 0`. -/
@[dlmf 28.4.E21]
theorem mathieuFourierA_zero_small_q {s : ℕ} (hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 2)) ∧ ∀ q : ℝ,
      mathieuFourierA 0 (2 * s) q = ((-1) ^ s * 2 / (s.factorial : ℂ) ^ 2 * ((q : ℂ) / 4) ^ s +
        ε q) * mathieuFourierA 0 0 q := by
  sorry

/-- **DLMF 28.4.22** (`A`): for fixed `s, m ≥ 1`,
`A^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E22]
theorem mathieuFourierA_up_small_q {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierA m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q := by
  sorry

/-- **DLMF 28.4.22** (`B`):
`B^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) B^m_m(q)`. -/
@[dlmf 28.4.E22]
theorem mathieuFourierB_up_small_q {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierB m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q := by
  sorry

/-- **DLMF 28.4.23** (`A`): for `1 ≤ s` and `2s ≤ m`,
`A^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E23]
theorem mathieuFourierA_down_small_q {m s : ℕ} (hs : 1 ≤ s) (hsm : 2 * s ≤ m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierA m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q := by
  sorry

/-- **DLMF 28.4.23** (`B`): for `1 ≤ s` and `2s < m`,
`B^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) B^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E23]
theorem mathieuFourierB_down_small_q {m s : ℕ} (hs : 1 ≤ s) (hsm : 2 * s < m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierB m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q := by
  sorry

/-! ### Asymptotic forms for large `m` (§28.4(vii)) -/

/-- **DLMF 28.4.24**: as `m → ∞`, fixed `q ≠ 0` and `n`,
`A^{2n}_{2m}(q) / A^{2n}_0(q) = (-1)^m/(m!)² (q/4)^m π(1 + O(1/m)) / w_II(π/2; a_{2n}(q), q)`. -/
@[dlmf 28.4.E24]
theorem mathieuFourierA_even_large_m (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    ∃ ε : ℕ → ℂ, ε =O[atTop] (fun m : ℕ => (1 : ℝ) / m) ∧ ∀ m : ℕ,
      mathieuFourierA (2 * n) (2 * m) q = mathieuFourierA (2 * n) 0 q *
        ((-1) ^ m / (m.factorial : ℂ) ^ 2 * ((q : ℂ) / 4) ^ m * (π * (1 + ε m)) /
          mathieuWII (mathieuA (2 * n) q) q (π / 2)) := by
  sorry

/-- **DLMF 28.4.25**: as `m → ∞`, fixed `q ≠ 0` and `n`,
`A^{2n+1}_{2m+1}/A^{2n+1}_1 = (-1)^{m+1}/((1/2)_{m+1})² (q/4)^{m+1} 2(1 + O(1/m)) /
w_II'(π/2; a_{2n+1}(q), q)`. -/
@[dlmf 28.4.E25]
theorem mathieuFourierA_odd_large_m (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    ∃ ε : ℕ → ℂ, ε =O[atTop] (fun m : ℕ => (1 : ℝ) / m) ∧ ∀ m : ℕ,
      mathieuFourierA (2 * n + 1) (2 * m + 1) q = mathieuFourierA (2 * n + 1) 1 q *
        ((-1) ^ (m + 1) / (ascPochhammer ℂ (m + 1)).eval (1 / 2) ^ 2 * ((q : ℂ) / 4) ^ (m + 1) *
          (2 * (1 + ε m)) / deriv (mathieuWII (mathieuA (2 * n + 1) q) q) (π / 2)) := by
  sorry

/-- **DLMF 28.4.26**: as `m → ∞`, fixed `q ≠ 0` and `n`,
`B^{2n+1}_{2m+1}/B^{2n+1}_1 = (-1)^m/((1/2)_{m+1})² (q/4)^{m+1} 2(1 + O(1/m)) /
w_I(π/2; b_{2n+1}(q), q)`. -/
@[dlmf 28.4.E26]
theorem mathieuFourierB_odd_large_m (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    ∃ ε : ℕ → ℂ, ε =O[atTop] (fun m : ℕ => (1 : ℝ) / m) ∧ ∀ m : ℕ,
      mathieuFourierB (2 * n + 1) (2 * m + 1) q = mathieuFourierB (2 * n + 1) 1 q *
        ((-1) ^ m / (ascPochhammer ℂ (m + 1)).eval (1 / 2) ^ 2 * ((q : ℂ) / 4) ^ (m + 1) *
          (2 * (1 + ε m)) / mathieuWI (mathieuB (2 * n + 1) q) q (π / 2)) := by
  sorry

/-- **DLMF 28.4.27**: as `m → ∞`, fixed `q ≠ 0` and `n`,
`B^{2n+2}_{2m}/B^{2n+2}_2 = (-1)^m/(m!)² (q/4)^m qπ(1 + O(1/m)) / w_I'(π/2; b_{2n+2}(q), q)`. -/
@[dlmf 28.4.E27]
theorem mathieuFourierB_even_large_m (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    ∃ ε : ℕ → ℂ, ε =O[atTop] (fun m : ℕ => (1 : ℝ) / m) ∧ ∀ m : ℕ,
      mathieuFourierB (2 * n + 2) (2 * m) q = mathieuFourierB (2 * n + 2) 2 q *
        ((-1) ^ m / (m.factorial : ℂ) ^ 2 * ((q : ℂ) / 4) ^ m * (q * π * (1 + ε m)) /
          deriv (mathieuWI (mathieuB (2 * n + 2) q) q) (π / 2)) := by
  sorry

end DLMF.Mathieu
