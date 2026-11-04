/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.Eigenvalues
public import DLMF.Lame.Polynomials.Identities
public import DLMF.Lame.Polynomials.Zeros

/-!
# Lamé polynomials: identification, algebraic form, zeros and Fourier series

The Lamé polynomials of the eight types of Table 29.12.1, defined in
`DLMF.Lame.Polynomials.Basic` by their Chebyshev series 29.15.43–29.15.50, are the Lamé
functions `Ec`, `Es` of §29.3 at integer order (DLMF 29.12.1–29.12.8); this file also gives
their eigenvalues, finite Fourier series, algebraic form and zeros (DLMF §§29.12, 29.15).

## Main results

* `chebyshevT_cos`, `sin_mul_chebyshevU_cos`, `jacobiSn_ofReal_eq_cos_lamePhi`: the Chebyshev
  identities of §29.15(ii) and `sn = cos φ`.
* `Real.lameUE_eq`, `Real.lameSE_eq`, `Real.lameCE_eq`, `Real.lameDE_eq`, `Real.lameSCE_eq`,
  `Real.lameSDE_eq`, `Real.lameCDE_eq`, `Real.lameSCDE_eq`: DLMF 29.12.1–29.12.8.
* `Real.lameA_eq_lamePolynomialH_uE`, `Real.lameA_eq_lamePolynomialH_sE`,
  `Real.lameB_eq_lamePolynomialH_cE`, …, `Real.lameB_eq_lamePolynomialH_scdE`: the eigenvalues
  `½(H_m + ν(ν+1)k²)`, DLMF 29.15.7, 29.15.12, …, 29.15.42.
* `Real.lameUE_fourier`, `Real.lameSE_fourier`, …, `Real.lameSCDE_fourier`: the finite
  Fourier series DLMF 29.15.1, 29.15.8, …, 29.15.38 in `φ = π/2 - am(x, k)` for real `x`.
* `lamePolynomialE_zeros`: the zero counts of §29.12(i).
* `lamePolynomialE_algebraic_form`: the algebraic form DLMF 29.12.9–29.12.10.
* `lamePolynomialE_zeros_maximize`, `lamePolynomialE_zeros_equilibrium`: the maximum principle and
  the electrostatic equilibrium of the zeros, DLMF 29.12.11–29.12.13.
* `Real.lameEc_even_fourierA_eq_zero`: for `ν = 2n` and `m ≤ n` the Fourier coefficients
  `A_{2p}` of `Ec^{2m}_{2n}` vanish for `p > n` (§29.6(i)).

## Implementation notes

The identification uses `DLMF.Lame.Polynomials.Identities`: the normalization integral 29.3.18
is `π/4` times the form 29.15.5 of the coefficients, by the trigonometric orthogonality in `φ`,
and the sign condition 29.15.6 gives the sign rule of §29.3(v). The eigenvalues come from
`DLMF.Lame.Polynomials.Eigenvalues` (Sturm's oscillation theorem; the real Lamé polynomial has
at most `n` zeros in `(0, K)`), and 29.15.3, the periods, parities and polynomial form of
Table 29.12.1 from `DLMF.Lame.Polynomials.Basis`. The Fourier series follow from the Chebyshev
identities and `cos φ = sn`, `sin φ = cn`.

The order `ν` is the nonnegative integer `t.order n` (§29.12(i)); the eigenvalue `H_m` is
`lamePolynomialH t n m k`. For `ρ, σ, τ` of 29.12.9: `ρ = ½` exactly for the types with a factor
`sn` (`sE, scE, sdE, scdE`), `σ = ½` for a factor `cn` (`cE, scE, cdE, scdE`) and `τ = ½` for
a factor `dn` (`dE, sdE, cdE, scdE`); these are written in place in the statements. The
equilibrium relation 29.12.13 has been checked numerically for all eight types.
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Polynomial Set
open scoped Real

noncomputable section

namespace DLMF.Lame

variable {k : ℝ}

/-! ### Chebyshev identities (§29.15(ii)) -/

/-- For real `x` and `0 < k < 1`, `sn(x, k) = cos φ` with `φ = π/2 - am(x, k)` (29.2.5). -/
@[dlmf 29.15.ii]
theorem jacobiSn_ofReal_eq_cos_lamePhi (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    jacobiSn (x : ℂ) k = (Real.cos (Real.lamePhi x k) : ℂ) := by
  rw [jacobiSn_ofReal hk0 hk1, Real.lamePhi, Real.cos_pi_div_two_sub, Real.jacobiSnOfParameter]

/-- For real `x` and `0 < k < 1`, `cn(x, k) = sin φ` with `φ = π/2 - am(x, k)` (29.2.5). -/
private lemma jacobiCn_ofReal_eq_sin_lamePhi (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    jacobiCn (x : ℂ) k = (Real.sin (Real.lamePhi x k) : ℂ) := by
  rw [jacobiCn_ofReal hk0 hk1, Real.lamePhi, Real.sin_pi_div_two_sub, Real.jacobiCnOfParameter]

/-- §29.15(ii): `cos(jθ) = T_j(cos θ)`. -/
@[dlmf 29.15.ii]
theorem chebyshevT_cos (j : ℕ) (θ : ℝ) :
    (Chebyshev.T ℂ (j : ℤ)).eval (Real.cos θ : ℂ) = (Real.cos (j * θ) : ℂ) := by
  have := Chebyshev.T_complex_cos (θ : ℂ) j
  push_cast at this ⊢
  exact this

/-- §29.15(ii): `sin((j+1)θ) = sin θ U_j(cos θ)`. -/
@[dlmf 29.15.ii]
theorem sin_mul_chebyshevU_cos (j : ℕ) (θ : ℝ) :
    (Real.sin θ : ℂ) * (Chebyshev.U ℂ (j : ℤ)).eval (Real.cos θ : ℂ) =
      (Real.sin ((j + 1) * θ) : ℂ) := by
  have := Chebyshev.U_complex_cos (θ : ℂ) j
  push_cast at this ⊢
  rw [mul_comm]
  exact this

/-! ### The eight types (29.12.1–29.12.8) and their Fourier series (§29.15(i)) -/

/-- 29.15.1: for real `x`, `uE^m(x, k²)` is a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E1]
theorem Real.lameUE_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameUE n m x k = ((∑ p ∈ Finset.range (n + 1),
        (if p = 0 then 1 / 2 else 1) * lamePolynomialCoeff .uE n m k p *
        Real.cos ((2 * p) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameUE, lamePolynomialE]
  simp only [LamePolynomialType.prefactor, LamePolynomialType.basis, one_mul,
      jacobiSn_ofReal_eq_cos_lamePhi hk0 hk1]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  have := chebyshevT_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [this]
  split_ifs <;> push_cast <;> ring

/-- 29.12.1: the Lamé polynomial `uE^m_{2n}(x, k²)` is the Lamé function
`Ec^{2m}_{2n}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18
(`lamePolynomialE_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E1]
theorem Real.lameUE_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameUE n m x k = (Real.lameEc ((2 * n : ℕ) : ℝ) (2 * m) x k : ℂ) := by
  have hw : ∀ y : ℝ, (lamePolynomialE .uE n m y k).re = ∑ p ∈ Finset.range (n + 1),
      ((if p = 0 then 1 / 2 else 1) * lamePolynomialCoeff .uE n m k p) *
        Real.cos (((2 * p : ℕ) : ℝ) * Real.lamePhi y k) :=
    fun y => by
      rw [show lamePolynomialE .uE n m y k = lameUE n m y k from rfl, Real.lameUE_fourier hk0 hk1,
        Complex.ofReal_re]
      push_cast; rfl
  have hid := lamePolynomialE_re_eq_lameEigenfunction hk0 hk1 .uE hm (σ := 1) ?_ one_pos ?_
  · have hreal : lameUE n m x k = ((lamePolynomialE .uE n m x k).re : ℂ) := by
      rw [show lamePolynomialE .uE n m x k = lameUE n m x k from rfl, Real.lameUE_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEc, show (2 * m).bodd = false by simp [Nat.bodd_mul],
      show 2 * m / 2 = m by omega]
    rfl
  · rw [integral_cos_series_lamePhi_sq hk0 hk1 (n + 1) _ (e := fun p => 2 * p)
      (fun a b h => by simpa using h) (fun p q => ⟨p + q, by ring⟩) hw]
    simp only [LamePolynomialType.normForm]
    rw [Finset.sum_range_succ',
        Finset.sum_range_succ' (fun p => lamePolynomialCoeff .uE n m k p ^ 2)]
    simp; ring_nf
    rw [Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by ring
  · simp only [lamePolyOddK, Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [cos_series_lamePhi_eval_K hk0 hk1 _ _ _ hw]
    simp only [LamePolynomialType.signForm]
    rw [Finset.sum_range_succ', sum_Ioc_zero_eq_sum_range_succ]
    simp; ring

/-- 29.15.7: the eigenvalue of `uE^m_{2n}` is
`a^{2m}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolynomialType_eq`). -/
@[dlmf 29.15.E7]
theorem Real.lameA_eq_lamePolynomialH_uE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameA ((2 * n : ℕ) : ℝ) (2 * m) k =
      (lamePolynomialH .uE n m k +
        ((2 * n : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolynomialType_eq hk0 hk1 .uE hm
  rw [Real.lameA, show (2 * m).bodd = false by simp [Nat.bodd_mul],
    show 2 * m / 2 = m by omega]
  exact this

/-- 29.15.8: for real `x`, `sE^m(x, k²)` is a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E8]
theorem Real.lameSE_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSE n m x k = ((∑ p ∈ Finset.range (n + 1),
        lamePolynomialCoeff .sE n m k p *
        Real.cos ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSE, lamePolynomialE]
  simp only [LamePolynomialType.prefactor, LamePolynomialType.basis, one_mul,
      jacobiSn_ofReal_eq_cos_lamePhi hk0 hk1]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  have := chebyshevT_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [this]

/-- 29.12.2: the Lamé polynomial `sE^m_{2n+1}(x, k²)` is the Lamé function
`Ec^{2m+1}_{2n+1}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18
(`lamePolynomialE_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E2]
theorem Real.lameSE_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSE n m x k = (Real.lameEc ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  have hw : ∀ y : ℝ, (lamePolynomialE .sE n m y k).re = ∑ p ∈ Finset.range (n + 1),
      lamePolynomialCoeff .sE n m k p * Real.cos (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi y k) :=
    fun y => by
      rw [show lamePolynomialE .sE n m y k = lameSE n m y k from rfl, Real.lameSE_fourier hk0 hk1,
        Complex.ofReal_re]
      push_cast; rfl
  have hid := lamePolynomialE_re_eq_lameEigenfunction hk0 hk1 .sE hm (σ := 1) ?_ one_pos ?_
  · have hreal : lameSE n m x k = ((lamePolynomialE .sE n m x k).re : ℂ) := by
      rw [show lamePolynomialE .sE n m x k = lameSE n m x k from rfl, Real.lameSE_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEc, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
      show (2 * m + 1) / 2 = m by omega]
    rfl
  · rw [integral_cos_series_lamePhi_sq hk0 hk1 (n + 1) _ (e := fun p => 2 * p + 1)
      (fun a b h => by simpa using h) (fun p q => ⟨p + q + 1, by ring⟩) hw]
    simp only [LamePolynomialType.normForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by simp; ring
  · simp only [lamePolyOddK, Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [cos_series_lamePhi_eval_K hk0 hk1 _ _ _ hw]
    rfl

/-- 29.15.12: the eigenvalue of `sE^m_{2n+1}` is
`a^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+1`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolynomialType_eq`). -/
@[dlmf 29.15.E12]
theorem Real.lameA_eq_lamePolynomialH_sE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameA ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolynomialH .sE n m k +
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolynomialType_eq hk0 hk1 .sE hm
  rw [Real.lameA, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
    show (2 * m + 1) / 2 = m by omega]
  exact this

/-- 29.15.13: for real `x`, `cE^m(x, k²)` is a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E13]
theorem Real.lameCE_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameCE n m x k = ((∑ p ∈ Finset.range (n + 1),
        lamePolynomialCoeff .cE n m k p *
        Real.sin ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameCE, lamePolynomialE]
  simp only [LamePolynomialType.prefactor, LamePolynomialType.basis,
      jacobiSn_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiCn_ofReal_eq_sin_lamePhi hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := sin_mul_chebyshevU_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 1 : ℂ)) = (2 * p : ℂ) + 1 by ring, ← this]
  ring

/-- 29.12.3: the Lamé polynomial `cE^m_{2n+1}(x, k²)` is the Lamé function
`Es^{2m+1}_{2n+1}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18
(`lamePolynomialE_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E3]
theorem Real.lameCE_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameCE n m x k = (Real.lameEs ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolynomialE .cE n m y k).re = ∑ p ∈ Finset.range (n + 1),
      lamePolynomialCoeff .cE n m k p * Real.sin (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi y k) :=
    fun y => by
      rw [show lamePolynomialE .cE n m y k = lameCE n m y k from rfl, Real.lameCE_fourier hk0 hk1,
        Complex.ofReal_re]
      push_cast; rfl
  have hid := lamePolynomialE_re_eq_lameEigenfunction hk0 hk1 .cE hm
    (σ := Real.jacobiDnOfParameter (Real.completeEllipticKOfParameter (k ^ 2)) (k ^ 2)) ?_
        (Real.jacobiDnOfParameter_pos hk _) ?_
  · have hreal : lameCE n m x k = ((lamePolynomialE .cE n m x k).re : ℂ) := by
      rw [show lamePolynomialE .cE n m x k = lameCE n m x k from rfl, Real.lameCE_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEs, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
      show (2 * m + 1 - 1) / 2 = m by omega]
    rfl
  · rw [integral_sin_series_lamePhi_sq hk0 hk1 (n + 1) _ (e := fun p => 2 * p + 1)
      (fun a b h => by simpa using h) (fun p q => ⟨p + q + 1, by ring⟩) hw]
    simp only [LamePolynomialType.normForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by simp; ring
  · simp only [lamePolyOddK, ↓reduceIte]
    rw [deriv_sin_series_lamePhi_K hk0 hk1 _ _ (fun p => ((2 * p + 1 : ℕ) : ℝ)) hw]
    simp only [LamePolynomialType.signForm]
    push_cast; rfl

/-- 29.15.17: the eigenvalue of `cE^m_{2n+1}` is
`b^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+1`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolynomialType_eq`). -/
@[dlmf 29.15.E17]
theorem Real.lameB_eq_lamePolynomialH_cE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameB ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolynomialH .cE n m k +
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolynomialType_eq hk0 hk1 .cE hm
  rw [Real.lameB, show (!(2 * m + 1).bodd) = false by simp [Nat.bodd_mul],
    show (2 * m + 1 - 1) / 2 = m by omega]
  exact this

/-- 29.15.18: for real `x`, `dE^m(x, k²)` is `dn(x, k)` times a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E18]
theorem Real.lameDE_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameDE n m x k = ((Real.jacobiDnOfParameter x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        (if p = 0 then 1 / 2 else 1) * lamePolynomialCoeff .dE n m k p *
        Real.cos ((2 * p) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameDE, lamePolynomialE]
  simp only [LamePolynomialType.prefactor, LamePolynomialType.basis,
      jacobiSn_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiDn_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := chebyshevT_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [this]
  split_ifs <;> push_cast <;> ring

/-- 29.12.4: the Lamé polynomial `dE^m_{2n+1}(x, k²)` is the Lamé function
`Ec^{2m}_{2n+1}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18
(`lamePolynomialE_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E4]
theorem Real.lameDE_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameDE n m x k = (Real.lameEc ((2 * n + 1 : ℕ) : ℝ) (2 * m) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolynomialE .dE n m y k).re = Real.jacobiDnOfParameter y (k ^ 2) *
      ∑ p ∈ Finset.range (n + 1), ((if p = 0 then 1 / 2 else 1) * lamePolynomialCoeff .dE n m k p) *
        Real.cos (((2 * p + 0 : ℕ) : ℝ) * Real.lamePhi y k) := fun y => by
    rw [show lamePolynomialE .dE n m y k = lameDE n m y k from rfl, Real.lameDE_fourier hk0 hk1,
      Complex.ofReal_re]
    push_cast; simp
  have hid := lamePolynomialE_re_eq_lameEigenfunction hk0 hk1 .dE hm
    (σ := Real.jacobiDnOfParameter (Real.completeEllipticKOfParameter (k ^ 2)) (k ^ 2)) ?_
        (Real.jacobiDnOfParameter_pos hk _) ?_
  · have hreal : lameDE n m x k = ((lamePolynomialE .dE n m x k).re : ℂ) := by
      rw [show lamePolynomialE .dE n m x k = lameDE n m x k from rfl, Real.lameDE_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEc, show (2 * m).bodd = false by simp [Nat.bodd_mul],
      show 2 * m / 2 = m by omega]
    rfl
  · rw [integral_dn_cos_series_lamePhi_sq hk0 hk1 (n + 1) _ 0 (by simp [lamePolynomialCoeff]) hw]
    set c := lamePolynomialCoeff .dE n m k with hc
    have hc1 : c (n + 1) = 0 := by simp [hc, lamePolynomialCoeff]
    rw [dnNorm_extraTerm_zero _ n (by simp [hc1])]
    have h1 : ∀ p, (if p = 0 then 1 / 2 else 1) * c p * ((if p + 1 = 0 then 1 / 2 else 1) *
        c (p + 1)) = c p * c (p + 1) - (if p = 0 then c 0 * c 1 / 2 else 0) := by
      intro p; rcases p with _ | p <;> simp; ring
    rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.sum_range_succ (fun p => c p * c (p + 1)), hc1]
    simp only [LamePolynomialType.normForm]
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun p => c p ^ 2)]
    simp
    rw [← Finset.sum_mul]
    ring
  · simp only [lamePolyOddK, Bool.false_eq_true, ↓reduceIte]
    rw [dn_cos_series_lamePhi_eval_K hk0 hk1 _ _ _ hw]
    simp only [LamePolynomialType.signForm]
    rw [Finset.sum_range_succ', sum_Ioc_zero_eq_sum_range_succ]
    congr 1
    simp [add_comm, div_eq_inv_mul]

/-- 29.15.22: the eigenvalue of `dE^m_{2n+1}` is
`a^{2m}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+1`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolynomialType_eq`). -/
@[dlmf 29.15.E22]
theorem Real.lameA_eq_lamePolynomialH_dE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameA ((2 * n + 1 : ℕ) : ℝ) (2 * m) k =
      (lamePolynomialH .dE n m k +
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolynomialType_eq hk0 hk1 .dE hm
  rw [Real.lameA, show (2 * m).bodd = false by simp [Nat.bodd_mul],
    show 2 * m / 2 = m by omega]
  exact this

/-- 29.15.23: for real `x`, `scE^m(x, k²)` is a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E23]
theorem Real.lameSCE_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSCE n m x k = ((∑ p ∈ Finset.range (n + 1),
        lamePolynomialCoeff .scE n m k p *
        Real.sin ((2 * p + 2) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSCE, lamePolynomialE]
  simp only [LamePolynomialType.prefactor, LamePolynomialType.basis,
      jacobiSn_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiCn_ofReal_eq_sin_lamePhi hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := sin_mul_chebyshevU_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 2 : ℂ)) = (2 * p + 1 : ℂ) + 1 by ring, ← this]
  ring

/-- 29.12.5: the Lamé polynomial `scE^m_{2n+2}(x, k²)` is the Lamé function
`Es^{2m+2}_{2n+2}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18
(`lamePolynomialE_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E5]
theorem Real.lameSCE_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSCE n m x k = (Real.lameEs ((2 * n + 2 : ℕ) : ℝ) (2 * m + 2) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolynomialE .scE n m y k).re = ∑ p ∈ Finset.range (n + 1),
      lamePolynomialCoeff .scE n m k p * Real.sin (((2 * p + 2 : ℕ) : ℝ) * Real.lamePhi y k) :=
    fun y => by
      rw [show lamePolynomialE .scE n m y k = lameSCE n m y k from rfl,
        Real.lameSCE_fourier hk0 hk1, Complex.ofReal_re]
      push_cast; rfl
  have hid := lamePolynomialE_re_eq_lameEigenfunction hk0 hk1 .scE hm
    (σ := Real.jacobiDnOfParameter (Real.completeEllipticKOfParameter (k ^ 2)) (k ^ 2)) ?_
        (Real.jacobiDnOfParameter_pos hk _) ?_
  · have hreal : lameSCE n m x k = ((lamePolynomialE .scE n m x k).re : ℂ) := by
      rw [show lamePolynomialE .scE n m x k = lameSCE n m x k from rfl,
          Real.lameSCE_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEs, show (2 * m + 2).bodd = false by simp [Nat.bodd_mul],
      show (2 * m + 2 - 1) / 2 = m by omega]
    rfl
  · rw [integral_sin_series_lamePhi_sq hk0 hk1 (n + 1) _ (e := fun p => 2 * p + 2)
      (fun a b h => by simpa using h) (fun p q => ⟨p + q + 2, by ring⟩) hw]
    simp only [LamePolynomialType.normForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by simp; ring
  · simp only [lamePolyOddK, ↓reduceIte]
    rw [deriv_sin_series_lamePhi_K hk0 hk1 _ _ (fun p => ((2 * p + 2 : ℕ) : ℝ)) hw]
    simp only [LamePolynomialType.signForm]
    push_cast; rfl

/-- 29.15.27: the eigenvalue of `scE^m_{2n+2}` is
`b^{2m+2}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+2`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolynomialType_eq`). -/
@[dlmf 29.15.E27]
theorem Real.lameB_eq_lamePolynomialH_scE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameB ((2 * n + 2 : ℕ) : ℝ) (2 * m + 2) k =
      (lamePolynomialH .scE n m k +
        ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolynomialType_eq hk0 hk1 .scE hm
  rw [Real.lameB, show (!(2 * m + 2).bodd) = true by simp [Nat.bodd_mul],
    show (2 * m + 2 - 1) / 2 = m by omega]
  exact this

/-- 29.15.28: for real `x`, `sdE^m(x, k²)` is `dn(x, k)` times a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E28]
theorem Real.lameSDE_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSDE n m x k = ((Real.jacobiDnOfParameter x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        lamePolynomialCoeff .sdE n m k p *
        Real.cos ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSDE, lamePolynomialE]
  simp only [LamePolynomialType.prefactor, LamePolynomialType.basis,
      jacobiSn_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiDn_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := chebyshevT_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [this]

/-- 29.12.6: the Lamé polynomial `sdE^m_{2n+2}(x, k²)` is the Lamé function
`Ec^{2m+1}_{2n+2}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18
(`lamePolynomialE_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E6]
theorem Real.lameSDE_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSDE n m x k = (Real.lameEc ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolynomialE .sdE n m y k).re = Real.jacobiDnOfParameter y (k ^ 2) *
      ∑ p ∈ Finset.range (n + 1), lamePolynomialCoeff .sdE n m k p *
        Real.cos (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi y k) := fun y => by
    rw [show lamePolynomialE .sdE n m y k = lameSDE n m y k from rfl,
      Real.lameSDE_fourier hk0 hk1, Complex.ofReal_re]
    push_cast; simp
  have hid := lamePolynomialE_re_eq_lameEigenfunction hk0 hk1 .sdE hm
    (σ := Real.jacobiDnOfParameter (Real.completeEllipticKOfParameter (k ^ 2)) (k ^ 2)) ?_
        (Real.jacobiDnOfParameter_pos hk _) ?_
  · have hreal : lameSDE n m x k = ((lamePolynomialE .sdE n m x k).re : ℂ) := by
      rw [show lamePolynomialE .sdE n m x k = lameSDE n m x k from rfl,
        Real.lameSDE_fourier hk0 hk1, Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEc, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
      show (2 * m + 1) / 2 = m by omega]
    rfl
  · rw [integral_dn_cos_series_lamePhi_sq hk0 hk1 (n + 1) _ 1 (by simp [lamePolynomialCoeff]) hw]
    set c := lamePolynomialCoeff .sdE n m k with hc
    have hc1 : c (n + 1) = 0 := by simp [hc, lamePolynomialCoeff]
    rw [dnNorm_extraTerm_one _ n, Finset.sum_range_succ (fun p => c p * c (p + 1)), hc1,
        mul_zero, add_zero]
    have h0 : ∀ p : ℕ, (2 * p + 1 = 0) = False := fun p => eq_false (by omega)
    simp only [LamePolynomialType.normForm, h0, ↓reduceIte, ← Finset.sum_mul]
    ring
  · simp only [lamePolyOddK, Bool.false_eq_true, ↓reduceIte]
    rw [dn_cos_series_lamePhi_eval_K hk0 hk1 _ _ _ hw]
    rfl

/-- 29.15.32: the eigenvalue of `sdE^m_{2n+2}` is
`a^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+2`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolynomialType_eq`). -/
@[dlmf 29.15.E32]
theorem Real.lameA_eq_lamePolynomialH_sdE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameA ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolynomialH .sdE n m k +
        ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolynomialType_eq hk0 hk1 .sdE hm
  rw [Real.lameA, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
    show (2 * m + 1) / 2 = m by omega]
  exact this

/-- 29.15.33: for real `x`, `cdE^m(x, k²)` is `dn(x, k)` times a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E33]
theorem Real.lameCDE_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameCDE n m x k = ((Real.jacobiDnOfParameter x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        lamePolynomialCoeff .cdE n m k p *
        Real.sin ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameCDE, lamePolynomialE]
  simp only [LamePolynomialType.prefactor, LamePolynomialType.basis,
      jacobiSn_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiCn_ofReal_eq_sin_lamePhi hk0 hk1, jacobiDn_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := sin_mul_chebyshevU_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 1 : ℂ)) = (2 * p : ℂ) + 1 by ring, ← this]
  ring

/-- 29.12.7: the Lamé polynomial `cdE^m_{2n+2}(x, k²)` is the Lamé function
`Es^{2m+1}_{2n+2}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18
(`lamePolynomialE_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E7]
theorem Real.lameCDE_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameCDE n m x k = (Real.lameEs ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolynomialE .cdE n m y k).re = Real.jacobiDnOfParameter y (k ^ 2) *
      ∑ p ∈ Finset.range (n + 1), lamePolynomialCoeff .cdE n m k p *
        Real.sin (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi y k) := fun y => by
    rw [show lamePolynomialE .cdE n m y k = lameCDE n m y k from rfl,
      Real.lameCDE_fourier hk0 hk1, Complex.ofReal_re]
    push_cast; simp
  have hid := lamePolynomialE_re_eq_lameEigenfunction hk0 hk1 .cdE hm
    (σ := Real.jacobiDnOfParameter (Real.completeEllipticKOfParameter (k ^ 2)) (k ^ 2) ^ 2) ?_
    (pow_pos (Real.jacobiDnOfParameter_pos hk _) 2) ?_
  · have hreal : lameCDE n m x k = ((lamePolynomialE .cdE n m x k).re : ℂ) := by
      rw [show lamePolynomialE .cdE n m x k = lameCDE n m x k from rfl,
        Real.lameCDE_fourier hk0 hk1, Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEs, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
      show (2 * m + 1 - 1) / 2 = m by omega]
    rfl
  · rw [integral_dn_sin_series_lamePhi_sq hk0 hk1 (n + 1) _ 1 (by simp [lamePolynomialCoeff]) hw]
    set c := lamePolynomialCoeff .cdE n m k with hc
    have hc1 : c (n + 1) = 0 := by simp [hc, lamePolynomialCoeff]
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [dnNorm_extraTerm_one _ n, Finset.sum_range_succ (fun p => c p * c (p + 1)), hc1,
        mul_zero, add_zero]
    have h0 : ∀ p : ℕ, (2 * p + 1 = 0) = False := fun p => eq_false (by omega)
    simp only [LamePolynomialType.normForm, h0, ↓reduceIte, ← Finset.sum_mul]
    ring
  · simp only [lamePolyOddK, ↓reduceIte]
    rw [deriv_dn_sin_series_lamePhi_K hk0 hk1 _ _ (fun p => ((2 * p + 1 : ℕ) : ℝ)) hw]
    simp only [LamePolynomialType.signForm]
    push_cast; rfl

/-- 29.15.37: the eigenvalue of `cdE^m_{2n+2}` is
`b^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+2`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolynomialType_eq`). -/
@[dlmf 29.15.E37]
theorem Real.lameB_eq_lamePolynomialH_cdE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameB ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolynomialH .cdE n m k +
        ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolynomialType_eq hk0 hk1 .cdE hm
  rw [Real.lameB, show (!(2 * m + 1).bodd) = false by simp [Nat.bodd_mul],
    show (2 * m + 1 - 1) / 2 = m by omega]
  exact this

/-- 29.15.38: for real `x`, `scdE^m(x, k²)` is `dn(x, k)` times a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E38]
theorem Real.lameSCDE_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSCDE n m x k = ((Real.jacobiDnOfParameter x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        lamePolynomialCoeff .scdE n m k p *
        Real.sin ((2 * p + 2) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSCDE, lamePolynomialE]
  simp only [LamePolynomialType.prefactor, LamePolynomialType.basis,
      jacobiSn_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiCn_ofReal_eq_sin_lamePhi hk0 hk1, jacobiDn_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := sin_mul_chebyshevU_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 2 : ℂ)) = (2 * p + 1 : ℂ) + 1 by ring, ← this]
  ring

/-- 29.12.8: the Lamé polynomial `scdE^m_{2n+3}(x, k²)` is the Lamé function
`Es^{2m+2}_{2n+3}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18
(`lamePolynomialE_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E8]
theorem Real.lameSCDE_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSCDE n m x k = (Real.lameEs ((2 * n + 3 : ℕ) : ℝ) (2 * m + 2) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolynomialE .scdE n m y k).re = Real.jacobiDnOfParameter y (k ^ 2) *
      ∑ p ∈ Finset.range (n + 1), lamePolynomialCoeff .scdE n m k p *
        Real.sin (((2 * p + 2 : ℕ) : ℝ) * Real.lamePhi y k) := fun y => by
    rw [show lamePolynomialE .scdE n m y k = lameSCDE n m y k from rfl,
      Real.lameSCDE_fourier hk0 hk1, Complex.ofReal_re]
    push_cast; simp
  have hid := lamePolynomialE_re_eq_lameEigenfunction hk0 hk1 .scdE hm
    (σ := Real.jacobiDnOfParameter (Real.completeEllipticKOfParameter (k ^ 2)) (k ^ 2) ^ 2) ?_
    (pow_pos (Real.jacobiDnOfParameter_pos hk _) 2) ?_
  · have hreal : lameSCDE n m x k = ((lamePolynomialE .scdE n m x k).re : ℂ) := by
      rw [show lamePolynomialE .scdE n m x k = lameSCDE n m x k from rfl,
        Real.lameSCDE_fourier hk0 hk1, Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEs, show (2 * m + 2).bodd = false by simp [Nat.bodd_mul],
      show (2 * m + 2 - 1) / 2 = m by omega]
    rfl
  · rw [integral_dn_sin_series_lamePhi_sq hk0 hk1 (n + 1) _ 2 (by simp [lamePolynomialCoeff]) hw]
    set c := lamePolynomialCoeff .scdE n m k with hc
    have hc1 : c (n + 1) = 0 := by simp [hc, lamePolynomialCoeff]
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [dnNorm_extraTerm_two _ (n + 1),
        Finset.sum_range_succ (fun p => c p * c (p + 1)), hc1, mul_zero,
      add_zero]
    have h0 : ∀ p : ℕ, (2 * p + 2 = 0) = False := fun p => eq_false (by omega)
    simp only [LamePolynomialType.normForm, h0, ↓reduceIte, ← Finset.sum_mul]
    ring
  · simp only [lamePolyOddK, ↓reduceIte]
    rw [deriv_dn_sin_series_lamePhi_K hk0 hk1 _ _ (fun p => ((2 * p + 2 : ℕ) : ℝ)) hw]
    simp only [LamePolynomialType.signForm]
    push_cast; rfl

/-- 29.15.42: the eigenvalue of `scdE^m_{2n+3}` is
`b^{2m+2}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+3`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolynomialType_eq`). -/
@[dlmf 29.15.E42]
theorem Real.lameB_eq_lamePolynomialH_scdE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameB ((2 * n + 3 : ℕ) : ℝ) (2 * m + 2) k =
      (lamePolynomialH .scdE n m k +
        ((2 * n + 3 : ℕ) : ℝ) * (((2 * n + 3 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolynomialType_eq hk0 hk1 .scdE hm
  rw [Real.lameB, show (!(2 * m + 2).bodd) = true by simp [Nat.bodd_mul],
    show (2 * m + 2 - 1) / 2 = m by omega]
  exact this

/-- §29.12(i): the Lamé polynomial `t^m` (`m ≤ n`) has exactly `m` zeros in `(0, K)` and
exactly `n - m` zeros on the open segment from `K` to `K + iK'`. Proved by Sturm oscillation
on both sides (`ncard_zeros_lamePolynomialE_real`, `ncard_zeros_lamePolynomialE_vertical`). -/
@[dlmf 29.12.i]
theorem lamePolynomialE_zeros (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType) {n m : ℕ}
    (hm : m ≤ n) :
    {x : ℝ | x ∈ Ioo 0 (Real.completeEllipticKOfParameter (k ^ 2)) ∧
        lamePolynomialE t n m x k = 0}.ncard = m ∧
      {y : ℝ | y ∈ Ioo 0 (Real.completeEllipticKOfParameter (1 - k ^ 2)) ∧
        lamePolynomialE t n m (Real.completeEllipticKOfParameter (k ^ 2) + I * y) k =
            0}.ncard = n - m :=
  ⟨ncard_zeros_lamePolynomialE_real hk0 hk1 t hm, ncard_zeros_lamePolynomialE_vertical hk0 hk1 t hm⟩

/-! ### Algebraic form and zeros (§§29.12(ii), 29.12(iii)) -/

/-- 29.12.9 and 29.12.10: with `ξ = sn²(z, k)` the Lamé polynomial is
`ξ^ρ (ξ - 1)^σ (ξ - k⁻²)^τ P(ξ)` (up to the choice of branches, i.e. up to the constant
factor `(-1)^σ (-k⁻²)^τ` relating `(ξ - 1)^σ (ξ - k⁻²)^τ` to `cn^{2σ} dn^{2τ}`), where `P`
has degree `n` and simple zeros, `m` of them in `(0, 1)` and `n - m` in `(1, k⁻²)`; it
satisfies the algebraic form 29.2.2 of Lamé's equation. Here the polynomial form is stated as
in `lamePolynomialE_polynomial_form`, and the zero locations are added. Proved from the zero counts
of §29.12(i) (`exists_poly_roots_lamePolynomialE`). -/
@[dlmf 29.12.E9, dlmf 29.12.E10]
theorem lamePolynomialE_algebraic_form (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], P.natDegree = n ∧ P.roots.Nodup ∧ P.roots.card = n ∧
      (P.roots.filter (· ∈ Ioo (0 : ℝ) 1)).card = m ∧
      (P.roots.filter (· ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹)).card = n - m ∧
      ∀ z : ℂ, lamePolynomialE t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSn z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSn z k ^ 2) :=
  exists_poly_roots_lamePolynomialE hk0 hk1 t hm

/-- Logarithmic derivative of `∏ (X - a)` at a point `r` that is not a root. -/
private lemma eval_derivative_prod_X_sub_C {T : Multiset ℝ} {r : ℝ} (hr : r ∉ T) :
    eval r (derivative (T.map fun a => X - C a).prod) =
      eval r (T.map fun a => X - C a).prod * (T.map fun a => 1 / (r - a)).sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | cons a T ih =>
    have ha : r - a ≠ 0 := sub_ne_zero.2 fun h => hr (h ▸ Multiset.mem_cons_self _ _)
    have hT : r ∉ T := fun h => hr (Multiset.mem_cons_of_mem h)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, derivative_mul,
      derivative_sub, derivative_X, derivative_C, eval_add, eval_mul, eval_sub, eval_X, eval_C,
      ih hT, sub_zero, one_mul]
    field_simp

/-- At a simple root `r` of a split real polynomial, `P'(r) ≠ 0` and
`P''(r) = 2P'(r) ∑_{η ≠ r} 1/(r - η)`. -/
private lemma eval_derivative_derivative_of_mem_roots {P : ℝ[X]}
    (hc : Multiset.card P.roots = P.natDegree) (hnd : P.roots.Nodup) {r : ℝ}
    (hr : r ∈ P.roots) :
    eval r (derivative P) ≠ 0 ∧ eval r (derivative (derivative P)) =
      2 * eval r (derivative P) * ((P.roots.erase r).map fun η => 1 / (r - η)).sum := by
  have hP0 : P ≠ 0 := ne_zero_of_mem_roots hr
  have hrT : r ∉ P.roots.erase r := hnd.notMem_erase
  set T := P.roots.erase r with hT
  set Q := (T.map fun a => X - C a).prod with hQdef
  have hPe : P = C P.leadingCoeff * ((X - C r) * Q) := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hc, ← Multiset.cons_erase hr]
    rw [Multiset.map_cons, Multiset.prod_cons]
  have hQ : eval r Q ≠ 0 := by
    rw [hQdef, eval_multiset_prod, Multiset.map_map]
    refine Multiset.prod_ne_zero fun h => ?_
    obtain ⟨a, ha, h0⟩ := Multiset.mem_map.1 h
    simp only [Function.comp, eval_sub, eval_X, eval_C] at h0
    exact hrT (sub_eq_zero.1 h0 ▸ ha)
  have hD := eval_derivative_prod_X_sub_C hrT
  rw [← hQdef] at hD
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
  rw [hPe]
  simp only [derivative_mul, derivative_add, derivative_C, derivative_sub, derivative_X,
    eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, zero_add, add_zero,
    sub_zero, one_mul]
  refine ⟨mul_ne_zero hlc hQ, ?_⟩
  rw [hD]; ring


/-- The algebra turning the differential equation at a zero into the relation 29.12.13. -/
private lemma lame_equilibrium_of_ode {ξ k e a b S : ℝ} (hξ : ξ ≠ 0) (h1 : ξ - 1 ≠ 0)
    (hk : 1 - k ^ 2 * ξ ≠ 0) (hk0 : k ≠ 0)
    (h : (1 - ξ) * (1 - k ^ 2 * ξ) * ((2 * e + 1) + 4 * ξ * S) =
      ξ * (1 + k ^ 2 - 2 * k ^ 2 * ξ + 2 * a * (1 - k ^ 2 * ξ) + 2 * b * k ^ 2 * (1 - ξ))) :
    (e / 2 + 1 / 4) / ξ + (a / 2 + 1 / 4) / (ξ - 1) + (b / 2 + 1 / 4) / (ξ - (k ^ 2)⁻¹) + S =
      0 := by
  have h2 : (b / 2 + 1 / 4) / (ξ - (k ^ 2)⁻¹) = -((b / 2 + 1 / 4) * k ^ 2) / (1 - k ^ 2 * ξ) := by
    rw [show ξ - (k ^ 2)⁻¹ = -(1 - k ^ 2 * ξ) / k ^ 2 by field_simp; ring]
    field_simp
  have h1' : 1 - ξ ≠ 0 := fun h0 => h1 (by linarith)
  have hk' : 1 - ξ * k ^ 2 ≠ 0 := by rwa [mul_comm]
  rw [h2, show ξ - 1 = -(1 - ξ) by ring]
  field_simp
  linear_combination 2 * h

/-- The polynomial form 29.12.9 with the explicit polynomial `lameSqPoly t n m k`. -/
private lemma lamePolynomialE_eq_lameSqPoly (t : LamePolynomialType) (n m : ℕ) (k : ℝ) (z : ℂ) :
    lamePolynomialE t n m z k = t.prefactor z k *
      (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSn z k else 1) *
      ((lameSqPoly t n m k).map (algebraMap ℝ ℂ)).eval (jacobiSn z k ^ 2) := by
  rw [lamePolynomialE, mul_assoc, sum_lamePolynomialCoeff_mul_basis]

/-- The zeros of `lameSqPoly t n m k`: `n` simple real zeros, `m` in `(0, 1)` and `n - m` in
`(1, k⁻²)`. -/
private lemma roots_lameSqPoly (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType) {n m : ℕ}
    (hm : m ≤ n) :
    (lameSqPoly t n m k).natDegree = n ∧ (lameSqPoly t n m k).roots.Nodup ∧
      (lameSqPoly t n m k).roots.card = n ∧
      ((lameSqPoly t n m k).roots.filter (· ∈ Ioo (0 : ℝ) 1)).card = m ∧
      ((lameSqPoly t n m k).roots.filter (· ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹)).card = n - m :=
  roots_of_lamePolynomialE_eq hk0 hk1 t hm (degree_lameSqPoly hk0 hk1 t hm)
    (lamePolynomialE_eq_lameSqPoly t n m k)

/-- Every zero of `lameSqPoly t n m k` lies in `(0, 1)` or in `(1, k⁻²)`. -/
private lemma mem_Ioo_of_mem_roots_lameSqPoly (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n m : ℕ} (hm : m ≤ n) {ξ : ℝ} (hξ : ξ ∈ (lameSqPoly t n m k).roots) :
    ξ ∈ Ioo (0 : ℝ) 1 ∨ ξ ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹ := by
  set P := lameSqPoly t n m k
  obtain ⟨-, -, hcard, hA, hB⟩ := roots_lameSqPoly hk0 hk1 t hm
  have hsum := Multiset.filter_add_filter (· ∈ Ioo (0 : ℝ) 1) (· ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹)
    P.roots
  have h0 : P.roots.filter (fun x => x ∈ Ioo (0 : ℝ) 1 ∧ x ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹) = 0 :=
    Multiset.filter_eq_nil.2 fun x _ hx => by linarith [hx.1.2, hx.2.1]
  rw [h0, add_zero] at hsum
  have hc := congrArg Multiset.card hsum
  rw [Multiset.card_add, hA, hB] at hc
  have hall := Multiset.filter_eq_self.1 (Multiset.eq_of_le_of_card_le
    (Multiset.filter_le _ P.roots) (by rw [← hc, hcard]; omega))
  exact hall ξ hξ

/-- The equilibrium relation 29.12.13 at a zero `ξ` of `lameSqPoly t n m k`. -/
private lemma lameSqPoly_equilibrium (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n m : ℕ} (hm : m ≤ n) {ξ : ℝ} (hξ : ξ ∈ (lameSqPoly t n m k).roots) :
    ((if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4) / ξ +
      ((if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4) / (ξ - 1) +
      ((if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4) /
        (ξ - (k ^ 2)⁻¹) +
      (((lameSqPoly t n m k).roots.erase ξ).map fun η => 1 / (ξ - η)).sum = 0 := by
  set P := lameSqPoly t n m k with hPdef
  obtain ⟨hnat, hnd, hcard, -, -⟩ := roots_lameSqPoly hk0 hk1 t hm
  have hloc := mem_Ioo_of_mem_roots_lameSqPoly hk0 hk1 t hm hξ
  have hξ0 : 0 < ξ := by rcases hloc with h | h <;> linarith [h.1]
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hξ1 : ξ - 1 ≠ 0 := by
    rcases hloc with h | h <;> [linarith [h.2]; linarith [h.1]]
  have hξk : 1 - k ^ 2 * ξ ≠ 0 := by
    rcases hloc with h | h
    · nlinarith [h.2]
    · have := h.2
      rw [lt_inv_comm₀ hξ0 (by positivity)] at this
      have : k ^ 2 * ξ < 1 := by
        calc k ^ 2 * ξ < ξ⁻¹ * ξ := by gcongr
          _ = 1 := inv_mul_cancel₀ hξ0.ne'
      linarith
  obtain ⟨hp1, hp2⟩ := eval_derivative_derivative_of_mem_roots (hcard.trans hnat.symm) hnd hξ
  set S := ((P.roots.erase ξ).map fun η => 1 / (ξ - η)).sum
  set p1 := eval ξ (derivative P)
  -- the differential equation at `s = √ξ`
  set G : ℂ[X] := (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then X else 1) *
    (P.map (algebraMap ℝ ℂ)).comp (X ^ 2) with hGdef
  have hG : ∀ s : ℂ, G.eval s =
      ∑ p ∈ Finset.range (n + 1), (lamePolynomialCoeff t n m k p : ℂ) * t.basis p s := fun s => by
    rw [sum_lamePolynomialCoeff_mul_basis, hGdef, eval_mul, eval_comp, eval_pow, eval_X]
    split_ifs <;> simp only [eval_X, eval_one, hPdef]
  obtain ⟨N, hN⟩ := exists_lameSnOperator_eq_zero hk0 t hm hG
  set s₀ : ℂ := ((Real.sqrt ξ : ℝ) : ℂ)
  have hs2 : s₀ ^ 2 = (ξ : ℂ) := by
    simp only [s₀]; rw [← Complex.ofReal_pow, Real.sq_sqrt hξ0.le]
  have hs0 : s₀ ≠ 0 := by
    simp only [s₀, ne_eq, Complex.ofReal_eq_zero]; exact (Real.sqrt_pos.2 hξ0).ne'
  have hev : ∀ Q : ℝ[X], (Q.map (algebraMap ℝ ℂ)).eval (s₀ ^ 2) = ((Q.eval ξ : ℝ) : ℂ) :=
    fun Q => by
      rw [hs2, eval_map_algebraMap, show (ξ : ℂ) = algebraMap ℝ ℂ ξ from rfl,
        aeval_algebraMap_apply, coe_aeval_eq_eval]; rfl
  have hP0 : (P.map (algebraMap ℝ ℂ)).eval (s₀ ^ 2) = 0 := by
    rw [hev, (mem_roots (ne_zero_of_mem_roots hξ)).1 hξ]; simp
  have hP1 : ((derivative P).map (algebraMap ℝ ℂ)).eval (s₀ ^ 2) = (p1 : ℂ) := hev _
  have hP2 : ((derivative (derivative P)).map (algebraMap ℝ ℂ)).eval (s₀ ^ 2) =
      ((2 * p1 * S : ℝ) : ℂ) := by rw [hev, hp2]
  have hop := hN s₀
  set e : ℝ := if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then 1 else 0 with he
  set a : ℝ := if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then 1 else 0 with ha
  set b : ℝ := if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then 1 else 0 with hb
  have hM : (1 + (k : ℂ) ^ 2 - 2 * k ^ 2 * s₀ ^ 2 +
      (if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then 2 * (1 - k ^ 2 * s₀ ^ 2) else 0) +
      (if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then 2 * k ^ 2 * (1 - s₀ ^ 2) else 0)) =
      ((1 + k ^ 2 - 2 * k ^ 2 * ξ + 2 * a * (1 - k ^ 2 * ξ) + 2 * b * k ^ 2 * (1 - ξ) : ℝ) :
        ℂ) := by
    rw [hs2, ha, hb]; split_ifs <;> push_cast <;> ring
  rw [hM] at hop
  set Mr : ℝ := 1 + k ^ 2 - 2 * k ^ 2 * ξ + 2 * a * (1 - k ^ 2 * ξ) + 2 * b * k ^ 2 * (1 - ξ)
  have hode : (1 - ξ) * (1 - k ^ 2 * ξ) * ((2 * e + 1) * p1 + 2 * ξ * (2 * p1 * S)) -
      ξ * Mr * p1 = 0 := by
    have key : s₀ ^ (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then 1 else 0) *
        ((1 - s₀ ^ 2) * (1 - k ^ 2 * s₀ ^ 2) *
          ((2 * e + 1) * p1 + 2 * s₀ ^ 2 * ((2 * p1 * S : ℝ) : ℂ)) - s₀ ^ 2 * Mr * p1) = 0 := by
      simp only [lameSnOperator, hGdef] at hop
      rw [he]
      split_ifs at hop ⊢ with ht
      · simp only [derivative_mul, derivative_add, derivative_X, derivative_C, derivative_comp,
          derivative_X_pow, derivative_map, eval_add, eval_mul, eval_comp, eval_X, eval_pow,
          eval_C, one_mul, zero_mul, zero_add, Nat.cast_ofNat, hP0, hP1, hP2] at hop
        push_cast at hop ⊢
        linear_combination (1 / 2) * hop
      · simp only [derivative_mul, derivative_C, derivative_comp, derivative_X_pow,
          derivative_map, eval_add, eval_mul, eval_comp, eval_X, eval_pow, eval_C, one_mul,
          zero_mul, zero_add, Nat.cast_ofNat, hP0, hP1, hP2] at hop
        push_cast at hop ⊢
        linear_combination (1 / 2) * hop
    rw [mul_eq_zero, hs2] at key
    rcases key with h | h
    · split_ifs at h <;> simp [hs0] at h
    · exact_mod_cast h
  have hode' : (1 - ξ) * (1 - k ^ 2 * ξ) * ((2 * e + 1) + 4 * ξ * S) = ξ * Mr := by
    apply mul_right_cancel₀ hp1
    linear_combination hode
  have := lame_equilibrium_of_ode hξ0.ne' hξ1 hξk hk0.ne' hode'
  convert this using 4 <;> simp only [e, a, b] <;> split_ifs <;> norm_num



/-- 29.12.13: the zeros `ξ_p` of `P` satisfy the equilibrium relations
`(ρ+¼)/ξ_p + (σ+¼)/(ξ_p - 1) + (τ+¼)/(ξ_p - k⁻²) + ∑_{q ≠ p} 1/(ξ_p - ξ_q) = 0`
(electrostatic interpretation, §29.12(iii)). Proved from Lamé's equation for the Chebyshev
series `G(s) = s^ε P(s²)` (`exists_lameSnOperator_eq_zero`), evaluated at `s = √ξ_p`, and
`P''(ξ_p) = 2P'(ξ_p) ∑_{q ≠ p} 1/(ξ_p - ξ_q)` at a simple zero. -/
@[dlmf 29.12.E13, dlmf 29.12.iii]
theorem lamePolynomialE_zeros_equilibrium (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], (P.natDegree = n ∧ P.roots.Nodup ∧ ∀ z : ℂ, lamePolynomialE t n m z k =
        t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSn z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSn z k ^ 2)) ∧
      ∀ ξ ∈ P.roots,
        ((if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4) / ξ +
          ((if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4) / (ξ - 1) +
          ((if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4) /
            (ξ - (k ^ 2)⁻¹) +
          ((P.roots.erase ξ).map fun η => 1 / (ξ - η)).sum = 0 :=
  ⟨lameSqPoly t n m k, ⟨(roots_lameSqPoly hk0 hk1 t hm).1, (roots_lameSqPoly hk0 hk1 t hm).2.1,
    lamePolynomialE_eq_lameSqPoly t n m k⟩, fun _ hξ => lameSqPoly_equilibrium hk0 hk1 t hm hξ⟩

section ZeroEnergy

variable {n m : ℕ} {c₀ c₁ c₂ K : ℝ}

open Finset

/-- Antisymmetrization of the gradient of `∑_{q<r} log(s_r - s_q)`. -/
private lemma sum_ite_lt_div_sub {n : ℕ} (d ξ : Fin n → ℝ) :
    ∑ q, ∑ r, (if q < r then (d r - d q) / (ξ r - ξ q) else 0) =
      ∑ p, d p * ∑ q, (if q ≠ p then 1 / (ξ p - ξ q) else 0) := by
  have h1 : ∀ p : Fin n, d p * ∑ q, (if q ≠ p then 1 / (ξ p - ξ q) else 0) =
      ∑ q, (if q < p then d p / (ξ p - ξ q) else 0) +
        ∑ q, (if p < q then d p / (ξ p - ξ q) else 0) := fun p => by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun q _ => ?_
    rcases lt_trichotomy q p with h | h | h
    · simp [h, h.ne, not_lt.2 h.le, div_eq_mul_inv]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le, div_eq_mul_inv]
  simp_rw [h1, sum_add_distrib]
  rw [sum_comm (f := fun p q => if q < p then d p / (ξ p - ξ q) else 0), ← sum_add_distrib]
  refine sum_congr rfl fun q _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  split_ifs
  · rw [show ξ q - ξ r = -(ξ r - ξ q) by ring, div_neg]; ring
  · simp

/-- `log y - log x ≤ (y - x)/x`, strictly unless `y = x`. -/
private lemma log_sub_log_le_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y - Real.log x ≤ (y - x) / x := by
  rw [← Real.log_div hy.ne' hx.ne']
  have := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rwa [sub_div, div_self hx.ne'] 

/-- `log y - log x < (y - x)/x` for `y ≠ x`. -/
private lemma log_sub_log_lt_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : y ≠ x) :
    Real.log y - Real.log x < (y - x) / x := by
  rw [← Real.log_div hy.ne' hx.ne']
  have := Real.log_lt_sub_one_of_pos (div_pos hy hx) (by
    rw [Ne, div_eq_one_iff_eq hx.ne']; exact hxy)
  rwa [sub_div, div_self hx.ne']



/-- The one-variable part of the logarithm of the energy. -/
private noncomputable def lameLogTerm (c₀ c₁ c₂ K x : ℝ) : ℝ :=
  c₀ * Real.log x + c₁ * Real.log |x - 1| + c₂ * Real.log (K - x)

/-- The concavity estimate for the one-variable part of the logarithm of the energy. -/
private lemma lameLogTerm_sub_le (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hK : 1 < K) {x y : ℝ}
    (hxy : (0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1) ∨ (1 < x ∧ x < K ∧ 1 < y ∧ y < K)) :
    lameLogTerm c₀ c₁ c₂ K y - lameLogTerm c₀ c₁ c₂ K x ≤
      (y - x) * (c₀ / x + c₁ / (x - 1) + c₂ / (x - K)) ∧
    (y ≠ x → lameLogTerm c₀ c₁ c₂ K y - lameLogTerm c₀ c₁ c₂ K x <
      (y - x) * (c₀ / x + c₁ / (x - 1) + c₂ / (x - K))) := by
  have hx0 : 0 < x := by rcases hxy with h | h <;> linarith [h.1]
  have hy0 : 0 < y := by rcases hxy with h | h <;> linarith [h.2.2.1]
  have hxK : 0 < K - x := by rcases hxy with h | h <;> linarith [h.2.1]
  have hyK : 0 < K - y := by rcases hxy with h | h <;> linarith [h.2.2.2]
  have hx1 : 0 < |x - 1| := abs_pos.2 (by rcases hxy with h | h <;> linarith [h.2.1, h.1])
  have hy1 : 0 < |y - 1| := abs_pos.2 (by rcases hxy with h | h <;> linarith [h.2.2.2, h.2.2.1])
  have e1 : (|y - 1| - |x - 1|) / |x - 1| = (y - x) / (x - 1) := by
    rcases hxy with h | h
    · rw [abs_of_neg (by linarith [h.2.2.2]), abs_of_neg (by linarith [h.2.1]),
        show x - 1 = -(-(x - 1)) by ring, div_neg (y - x)]
      ring
    · rw [abs_of_pos (by linarith [h.2.2.1]), abs_of_pos (by linarith [h.1])]; ring
  have e2 : ((K - y) - (K - x)) / (K - x) = (y - x) / (x - K) := by
    rw [show x - K = -(K - x) by ring, div_neg]; ring
  have b1 := mul_le_mul_of_nonneg_left (log_sub_log_le_div hx1 hy1) hc₁.le
  have b2 := mul_le_mul_of_nonneg_left (log_sub_log_le_div hxK hyK) hc₂.le
  rw [e1] at b1
  rw [e2] at b2
  have hexp : (y - x) * (c₀ / x + c₁ / (x - 1) + c₂ / (x - K)) =
      c₀ * ((y - x) / x) + c₁ * ((y - x) / (x - 1)) + c₂ * ((y - x) / (x - K)) := by ring
  rw [hexp]
  unfold lameLogTerm
  refine ⟨?_, fun hne => ?_⟩
  · have b0 := mul_le_mul_of_nonneg_left (log_sub_log_le_div hx0 hy0) hc₀.le
    nlinarith
  · have b0 := mul_lt_mul_of_pos_left (log_sub_log_lt_div hx0 hy0 hne) hc₀
    nlinarith


/-- The energy `g` of 29.12.11. -/
private noncomputable def lameEnergy (c₀ c₁ c₂ K : ℝ) (s : Fin n → ℝ) : ℝ :=
  (∏ p, s p ^ c₀ * |s p - 1| ^ c₁ * (K - s p) ^ c₂) * ∏ q, ∏ r, if q < r then s r - s q else 1

/-- The interior of the region of 29.12.11. -/
private def IsLameZeroInterior (m : ℕ) (K : ℝ) (s : Fin n → ℝ) : Prop :=
  StrictMono s ∧ ∀ j : Fin n, ((j : ℕ) < m → 0 < s j ∧ s j < 1) ∧ (m ≤ (j : ℕ) → 1 < s j ∧ s j < K)

/-- The factors of the energy are positive in the interior. -/
private lemma IsLameZeroInterior.pos (hK : 1 < K) {s : Fin n → ℝ}
    (hs : IsLameZeroInterior m K s) (p : Fin n) :
    0 < s p ∧ 0 < |s p - 1| ∧ 0 < K - s p := by
  rcases lt_or_ge (p : ℕ) m with h | h
  · obtain ⟨h1, h2⟩ := (hs.2 p).1 h
    exact ⟨h1, abs_pos.2 (by linarith), by linarith⟩
  · obtain ⟨h1, h2⟩ := (hs.2 p).2 h
    exact ⟨by linarith, abs_pos.2 (by linarith), by linarith⟩

/-- The energy is positive in the interior. -/
private lemma IsLameZeroInterior.lameEnergy_pos (hK : 1 < K) {s : Fin n → ℝ}
    (hs : IsLameZeroInterior m K s) :
    0 < lameEnergy c₀ c₁ c₂ K s := by
  refine mul_pos (prod_pos fun p _ => ?_) (prod_pos fun q _ => prod_pos fun r _ => ?_)
  · obtain ⟨h1, h2, h3⟩ := hs.pos hK p
    positivity
  · split_ifs with h
    · exact sub_pos.2 (hs.1 h)
    · exact one_pos

/-- The logarithm of the energy in the interior. -/
private lemma IsLameZeroInterior.log_lameEnergy (hK : 1 < K) {s : Fin n → ℝ}
    (hs : IsLameZeroInterior m K s) :
    Real.log (lameEnergy c₀ c₁ c₂ K s) = ∑ p, lameLogTerm c₀ c₁ c₂ K (s p) +
      ∑ q, ∑ r, (if q < r then Real.log (s r - s q) else 0) := by
  have hv : ∀ q r : Fin n, (if q < r then s r - s q else 1) ≠ 0 := fun q r => by
    split_ifs with h
    · exact (sub_pos.2 (hs.1 h)).ne'
    · exact one_ne_zero
  have hf : ∀ p, s p ^ c₀ * |s p - 1| ^ c₁ * (K - s p) ^ c₂ ≠ 0 := fun p => by
    obtain ⟨h1, h2, h3⟩ := hs.pos hK p
    positivity
  rw [lameEnergy, Real.log_mul (prod_ne_zero_iff.2 fun p _ => hf p)
    (prod_ne_zero_iff.2 fun q _ => prod_ne_zero_iff.2 fun r _ => hv q r),
    Real.log_prod (fun p _ => hf p)]
  rw [Real.log_prod (fun q _ => prod_ne_zero_iff.2 fun r _ => hv q r)]
  congr 1
  · refine sum_congr rfl fun p _ => ?_
    obtain ⟨h1, h2, h3⟩ := hs.pos hK p
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow h1, Real.log_rpow h2, Real.log_rpow h3, lameLogTerm]
  · refine sum_congr rfl fun q _ => ?_
    rw [Real.log_prod (fun r _ => hv q r)]
    refine sum_congr rfl fun r _ => ?_
    split_ifs <;> simp


/-- On the closed region of 29.12.11 the energy is nonnegative, and positive only inside. -/
private lemma lameEnergy_nonneg_of_mem (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hK : 1 < K)
    {s : Fin n → ℝ} (hmono : Monotone s)
    (hs : ∀ j : Fin n, ((j : ℕ) < m → 0 ≤ s j ∧ s j ≤ 1) ∧ (m ≤ (j : ℕ) → 1 ≤ s j ∧ s j ≤ K)) :
    0 ≤ lameEnergy c₀ c₁ c₂ K s ∧ (lameEnergy c₀ c₁ c₂ K s ≠ 0 → IsLameZeroInterior m K s) := by
  have hb : ∀ p, 0 ≤ s p ∧ s p ≤ K := fun p => by
    rcases lt_or_ge (p : ℕ) m with h | h
    · obtain ⟨h1, h2⟩ := (hs p).1 h; exact ⟨h1, by linarith⟩
    · obtain ⟨h1, h2⟩ := (hs p).2 h; exact ⟨by linarith, h2⟩
  refine ⟨mul_nonneg (prod_nonneg fun p _ => ?_) (prod_nonneg fun q _ => prod_nonneg fun r _ => ?_),
    fun hne => ?_⟩
  · have := hb p
    have : 0 ≤ K - s p := by linarith [this.2]
    have := (hb p).1
    positivity
  · split_ifs with h
    · exact sub_nonneg.2 (hmono h.le)
    · exact zero_le_one
  · obtain ⟨hne1, hne2⟩ := mul_ne_zero_iff.1 hne
    have hf := prod_ne_zero_iff.1 hne1
    have hv := prod_ne_zero_iff.1 hne2
    refine ⟨fun q r hqr => lt_of_le_of_ne (hmono hqr.le) fun he => ?_, fun j => ?_⟩
    · have := prod_ne_zero_iff.1 (hv q (mem_univ _)) r (mem_univ _)
      simp [hqr, he] at this
    · have h := hf j (mem_univ _)
      simp only [mul_ne_zero_iff] at h
      obtain ⟨⟨h0, h1⟩, h2⟩ := h
      have e0 : s j ≠ 0 := fun he => h0 (by rw [he, Real.zero_rpow hc₀.ne'])
      have e1 : s j ≠ 1 := fun he => h1 (by rw [he, sub_self, abs_zero, Real.zero_rpow hc₁.ne'])
      have e2 : s j ≠ K := fun he => h2 (by rw [he, sub_self, Real.zero_rpow hc₂.ne'])
      refine ⟨fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨a, b⟩ := (hs j).1 hj
        exact ⟨lt_of_le_of_ne a (Ne.symm e0), lt_of_le_of_ne b e1⟩
      · obtain ⟨a, b⟩ := (hs j).2 hj
        exact ⟨lt_of_le_of_ne a (Ne.symm e1), lt_of_le_of_ne b e2⟩

/-- The interior critical point is the strict maximum of the energy. -/
private lemma lameEnergy_le_of_equilibrium (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hK : 1 < K)
    {ξ s : Fin n → ℝ} (hξ : IsLameZeroInterior m K ξ) (hs : IsLameZeroInterior m K s)
    (heq : ∀ p, c₀ / ξ p + c₁ / (ξ p - 1) + c₂ / (ξ p - K) +
      ∑ q, (if q ≠ p then 1 / (ξ p - ξ q) else 0) = 0) :
    lameEnergy c₀ c₁ c₂ K s ≤ lameEnergy c₀ c₁ c₂ K ξ ∧
      (s ≠ ξ → lameEnergy c₀ c₁ c₂ K s < lameEnergy c₀ c₁ c₂ K ξ) := by
  have hside : ∀ p, (0 < ξ p ∧ ξ p < 1 ∧ 0 < s p ∧ s p < 1) ∨
      (1 < ξ p ∧ ξ p < K ∧ 1 < s p ∧ s p < K) := fun p => by
    rcases lt_or_ge (p : ℕ) m with h | h
    · exact Or.inl ⟨((hξ.2 p).1 h).1, ((hξ.2 p).1 h).2, ((hs.2 p).1 h).1, ((hs.2 p).1 h).2⟩
    · exact Or.inr ⟨((hξ.2 p).2 h).1, ((hξ.2 p).2 h).2, ((hs.2 p).2 h).1, ((hs.2 p).2 h).2⟩
  set F : Fin n → ℝ := fun p => c₀ / ξ p + c₁ / (ξ p - 1) + c₂ / (ξ p - K)
  have hV : ∑ q, ∑ r, ((if q < r then Real.log (s r - s q) else 0) -
      (if q < r then Real.log (ξ r - ξ q) else 0)) ≤
      ∑ q, ∑ r, (if q < r then ((s r - ξ r) - (s q - ξ q)) / (ξ r - ξ q) else 0) := by
    refine sum_le_sum fun q _ => sum_le_sum fun r _ => ?_
    split_ifs with h
    · have := log_sub_log_le_div (sub_pos.2 (hξ.1 h)) (sub_pos.2 (hs.1 h))
      convert this using 2; ring
    · simp
  have hsum : ∑ p, (s p - ξ p) * F p +
      ∑ q, ∑ r, (if q < r then ((s r - ξ r) - (s q - ξ q)) / (ξ r - ξ q) else 0) = 0 := by
    rw [sum_ite_lt_div_sub (fun p => s p - ξ p) ξ, ← sum_add_distrib]
    refine sum_eq_zero fun p _ => ?_
    rw [← mul_add, heq p, mul_zero]
  have hlog : Real.log (lameEnergy c₀ c₁ c₂ K s) - Real.log (lameEnergy c₀ c₁ c₂ K ξ) =
      ∑ p, (lameLogTerm c₀ c₁ c₂ K (s p) - lameLogTerm c₀ c₁ c₂ K (ξ p)) +
      ∑ q, ∑ r, ((if q < r then Real.log (s r - s q) else 0) -
        (if q < r then Real.log (ξ r - ξ q) else 0)) := by
    rw [hs.log_lameEnergy hK, hξ.log_lameEnergy hK, sum_sub_distrib]
    simp only [sum_sub_distrib]
    ring
  have hpos := hs.lameEnergy_pos (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) hK
  have hξpos := hξ.lameEnergy_pos (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) hK
  refine ⟨?_, fun hne => ?_⟩
  · have hT : ∑ p, (lameLogTerm c₀ c₁ c₂ K (s p) - lameLogTerm c₀ c₁ c₂ K (ξ p)) ≤
        ∑ p, (s p - ξ p) * F p :=
      sum_le_sum fun p _ => (lameLogTerm_sub_le hc₀ hc₁ hc₂ hK (hside p)).1
    rw [← Real.log_le_log_iff hpos hξpos]
    linarith
  · obtain ⟨p, hp⟩ := Function.ne_iff.1 hne
    have hT : ∑ p, (lameLogTerm c₀ c₁ c₂ K (s p) - lameLogTerm c₀ c₁ c₂ K (ξ p)) <
        ∑ p, (s p - ξ p) * F p :=
      sum_lt_sum (fun p _ => (lameLogTerm_sub_le hc₀ hc₁ hc₂ hK (hside p)).1)
        ⟨p, mem_univ _, (lameLogTerm_sub_le hc₀ hc₁ hc₂ hK (hside p)).2 hp⟩
    rw [← Real.log_lt_log_iff hpos hξpos]
    linarith

end ZeroEnergy

/-- 29.12.11–29.12.12: with `ξ₁ < ⋯ < ξₙ` the zeros of `P` (29.12.10) and `ρ, σ, τ` as in
29.12.9, the function
`g(t) = (∏_p t_p^{ρ+¼} |t_p - 1|^{σ+¼} (k⁻² - t_p)^{τ+¼}) ∏_{q<r} (t_r - t_q)` on the region
`0 ≤ t₁ ≤ ⋯ ≤ t_m ≤ 1 ≤ t_{m+1} ≤ ⋯ ≤ t_n ≤ k⁻²` attains its absolute maximum exactly at
`t = ξ`. Proved from the equilibrium relations 29.12.13: `g` vanishes on the boundary of the
region, and in the interior `log g` is a sum of logarithms of positive affine functions, so
`log y - log x ≤ (y - x)/x` bounds `log g(t) - log g(ξ)` by the gradient term, which vanishes
at `ξ`. -/
@[dlmf 29.12.E11, dlmf 29.12.E12]
theorem lamePolynomialE_zeros_maximize (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], (P.natDegree = n ∧ ∀ z : ℂ, lamePolynomialE t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSn z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSn z k ^ 2)) ∧
      ∃ ξ : Fin n → ℝ, StrictMono ξ ∧ (∀ j, P.IsRoot (ξ j)) ∧
        let ρ : ℝ := if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then 1 / 2 else 0
        let σ : ℝ := if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0
        let τ : ℝ := if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0
        let R : Set (Fin n → ℝ) := {s | Monotone s ∧ ∀ j : Fin n,
          ((j : ℕ) < m → 0 ≤ s j ∧ s j ≤ 1) ∧ (m ≤ (j : ℕ) → 1 ≤ s j ∧ s j ≤ (k ^ 2)⁻¹)}
        let g : (Fin n → ℝ) → ℝ := fun s =>
          (∏ p, s p ^ (ρ + 1 / 4) * |s p - 1| ^ (σ + 1 / 4) * ((k ^ 2)⁻¹ - s p) ^ (τ + 1 / 4)) *
            ∏ q, ∏ r, if q < r then s r - s q else 1
        ξ ∈ R ∧ ∀ s ∈ R, g s ≤ g ξ ∧ (g s = g ξ → s = ξ) := by
  set P := lameSqPoly t n m k with hPdef
  obtain ⟨hnat, hnd, hcard, hA, -⟩ := roots_lameSqPoly hk0 hk1 t hm
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hK : 1 < (k ^ 2)⁻¹ := by rw [lt_inv_comm₀ one_pos (by positivity), inv_one]; exact hk2
  have hcardF : P.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  set ξ : Fin n → ℝ := ⇑(P.roots.toFinset.orderEmbOfFin hcardF) with hξdef
  have hξmono : StrictMono ξ := (P.roots.toFinset.orderEmbOfFin hcardF).strictMono
  have hξmem : ∀ j, ξ j ∈ P.roots := fun j =>
    Multiset.mem_toFinset.1 (Finset.orderEmbOfFin_mem _ hcardF j)
  have hloc := fun j => mem_Ioo_of_mem_roots_lameSqPoly hk0 hk1 t hm (hξmem j)
  -- exactly the first `m` zeros lie in `(0, 1)`
  have hAc : (Finset.univ.filter fun j : Fin n => ξ j < 1).card = m := by
    rw [← Finset.card_image_of_injective _ hξmono.injective]
    have himg : (Finset.univ.filter fun j : Fin n => ξ j < 1).image ξ =
        P.roots.toFinset.filter (· ∈ Ioo (0 : ℝ) 1) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        refine ⟨Finset.orderEmbOfFin_mem _ hcardF j, ?_⟩
        rcases hloc j with h | h
        · exact h
        · exact absurd h.1 (not_lt.2 hj.le)
      · rintro ⟨hx, hx01⟩
        have : x ∈ Set.range ξ := by
          rw [hξdef, Finset.range_orderEmbOfFin]; exact hx
        obtain ⟨j, rfl⟩ := this
        exact ⟨j, hx01.2, rfl⟩
    rw [himg, ← Multiset.toFinset_filter, Multiset.toFinset_card_of_nodup (hnd.filter _), hA]
  have hlt : ∀ j : Fin n, ((j : ℕ) < m ↔ ξ j < 1) := fun j => by
    constructor
    · intro hj
      by_contra hc
      have hsub : (Finset.univ.filter fun i : Fin n => ξ i < 1) ⊆ Finset.Iio j := fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_Iio.2 (hξmono.lt_iff_lt.1 (lt_of_lt_of_le hi (not_lt.1 hc)))
      have := Finset.card_le_card hsub
      rw [hAc, Fin.card_Iio] at this
      omega
    · intro hj
      by_contra hc
      have hsub : Finset.Iic j ⊆ (Finset.univ.filter fun i : Fin n => ξ i < 1) := fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_le_of_lt (hξmono.monotone (Finset.mem_Iic.1 hi)) hj
      have := Finset.card_le_card hsub
      rw [hAc, Fin.card_Iic] at this
      omega
  have hint : IsLameZeroInterior m (k ^ 2)⁻¹ ξ := by
    refine ⟨hξmono, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
    · rcases hloc j with h | h
      · exact h
      · exact absurd ((hlt j).1 hj) (not_lt.2 h.1.le)
    · rcases hloc j with h | h
      · exact absurd ((hlt j).2 h.2) (not_lt.2 hj)
      · exact h
  -- the equilibrium relations in terms of `ξ`
  have hsumF : ∀ (p : Fin n) (f : ℝ → ℝ),
      ∑ q, (if q ≠ p then f (ξ q) else 0) = ((P.roots.erase (ξ p)).map f).sum := fun p f => by
    rw [← Finset.sum_filter, Finset.filter_ne']
    have hmap := Finset.sum_map (Finset.univ.erase p)
      (P.roots.toFinset.orderEmbOfFin hcardF).toEmbedding f
    rw [Finset.map_erase, Finset.map_orderEmbOfFin_univ] at hmap
    calc ∑ a ∈ Finset.univ.erase p, f (ξ a)
        = ∑ x ∈ P.roots.toFinset.erase (ξ p), f x := hmap.symm
      _ = _ := by
        rw [Finset.sum_eq_multiset_sum, Finset.erase_val, Multiset.toFinset_val, hnd.dedup]
  set c₀ : ℝ := (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4
  set c₁ : ℝ := (if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4
  set c₂ : ℝ := (if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4
  have hc₀ : 0 < c₀ := by simp only [c₀]; split_ifs <;> norm_num
  have hc₁ : 0 < c₁ := by simp only [c₁]; split_ifs <;> norm_num
  have hc₂ : 0 < c₂ := by simp only [c₂]; split_ifs <;> norm_num
  have heq : ∀ p, c₀ / ξ p + c₁ / (ξ p - 1) + c₂ / (ξ p - (k ^ 2)⁻¹) +
      ∑ q, (if q ≠ p then 1 / (ξ p - ξ q) else 0) = 0 := fun p => by
    rw [hsumF p (fun η => 1 / (ξ p - η))]
    exact lameSqPoly_equilibrium hk0 hk1 t hm (hξmem p)
  refine ⟨P, ⟨hnat, lamePolynomialE_eq_lameSqPoly t n m k⟩, ξ, hξmono,
    fun j => (mem_roots (ne_zero_of_mem_roots (hξmem j))).1 (hξmem j), ?_⟩
  intro ρ σ τ R g
  have hg : ∀ s, g s = lameEnergy c₀ c₁ c₂ (k ^ 2)⁻¹ s := fun s => rfl
  refine ⟨⟨hξmono.monotone, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩, fun s hs => ?_⟩
  · exact ⟨((hint.2 j).1 hj).1.le, ((hint.2 j).1 hj).2.le⟩
  · exact ⟨((hint.2 j).2 hj).1.le, ((hint.2 j).2 hj).2.le⟩
  rw [hg, hg]
  have hξpos := hint.lameEnergy_pos (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) hK
  obtain ⟨hs0, hsint⟩ := lameEnergy_nonneg_of_mem hc₀ hc₁ hc₂ hK hs.1 hs.2
  by_cases h0 : lameEnergy c₀ c₁ c₂ (k ^ 2)⁻¹ s = 0
  · rw [h0]
    exact ⟨hξpos.le, fun h => absurd h.symm hξpos.ne'⟩
  · have := lameEnergy_le_of_equilibrium hc₀ hc₁ hc₂ hK hint (hsint h0) heq
    refine ⟨this.1, fun he => ?_⟩
    by_contra hne
    exact (this.2 hne).ne he

/-! ### The terminating Fourier series of §29.6(i) -/

/-- §29.6(i): for `ν = 2n` and `m = 0, 1, …, n` the Fourier coefficients `A_{2p}` of
`Ec^{2m}_{2n}` vanish for `p > n`, so `Ec^{2m}_{2n}` reduces to a Lamé polynomial (compare
§§29.12(i), 29.15(i)). Proved from the finite Fourier series 29.15.1 (`Real.lameUE_eq`,
`Real.lameUE_fourier`) and the orthogonality of `cos(2qφ)` on `[0, π/2]`. -/
@[dlmf 29.6.i]
theorem Real.lameEc_even_fourierA_eq_zero (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n)
    {p : ℕ} (hp : n < p) :
    Real.lameCosCoeff (fun x => Real.lameEc (2 * n : ℕ) (2 * m) x k) k true (2 * p) = 0 := by
  set b : ℕ → ℝ := fun q => (if q = 0 then 1 / 2 else 1) * lamePolynomialCoeff .uE n m k q
  have hE : ∀ x : ℝ, Real.lameEc (2 * n : ℕ) (2 * m) x k =
      ∑ q ∈ Finset.range (n + 1), b q * Real.cos ((2 * q) * Real.lamePhi x k) := fun x => by
    have h := (Real.lameUE_eq hk0 hk1 hm x).symm.trans (Real.lameUE_fourier hk0 hk1 n m x)
    exact_mod_cast h
  rw [Real.lameCosCoeff]
  simp only [↓reduceIte]
  have e : ∀ x : ℝ, Real.lameEc (2 * n : ℕ) (2 * m) x k *
      Real.cos (((2 * p : ℕ) : ℝ) * Real.lamePhi x k) * Real.jacobiDnOfParameter x (k ^ 2) =
      Real.jacobiDnOfParameter x (k ^ 2) * (fun t => ∑ q ∈ Finset.range (n + 1),
        b q * (Real.cos (2 * (((q : ℤ) - p : ℤ) : ℝ) * t) / 2 +
          Real.cos (2 * (((q : ℤ) + p : ℤ) : ℝ) * t) / 2)) (Real.lamePhi x k) := fun x => by
    rw [hE x, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    rw [show 2 * ((q : ℝ) - p) * Real.lamePhi x k =
        2 * q * Real.lamePhi x k - 2 * p * Real.lamePhi x k by ring,
      show 2 * ((q : ℝ) + p) * Real.lamePhi x k =
        2 * q * Real.lamePhi x k + 2 * p * Real.lamePhi x k by ring, Real.cos_sub, Real.cos_add]
    ring
  rw [intervalIntegral.integral_congr (fun x _ => e x),
    integral_jacobiDnOfParameter_mul_comp_lamePhi (g := fun t => ∑ q ∈ Finset.range (n + 1),
        b q * (Real.cos (2 * (((q : ℤ) - p : ℤ) : ℝ) * t) / 2 +
          Real.cos (2 * (((q : ℤ) + p : ℤ) : ℝ) * t) / 2)) hk0 hk1 (by fun_prop)]
  rw [intervalIntegral.integral_finsetSum (fun q _ => by
    exact (Continuous.intervalIntegrable (by fun_prop) _ _))]
  rw [Finset.sum_eq_zero, mul_zero]
  intro q hq
  have hq' : q ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_div, intervalIntegral.integral_div]
  have e1 := integral_cos_two_mul_int_pi_div_two ((q : ℤ) - p)
  have e2 := integral_cos_two_mul_int_pi_div_two ((q : ℤ) + p)
  have h1 : (q : ℤ) - p ≠ 0 := by omega
  have h2 : (q : ℤ) + p ≠ 0 := by omega
  simp only [h1, h2, ↓reduceIte] at e1 e2
  rw [e1, e2]
  simp

end DLMF.Lame
