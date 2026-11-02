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

* `chebyshevT_cos`, `sin_mul_chebyshevU_cos`, `jacobiSnk_ofReal_eq_cos_lamePhi`: the Chebyshev
  identities of §29.15(ii) and `sn = cos φ`.
* `Real.lameUEk_eq`, `Real.lameSEk_eq`, `Real.lameCEk_eq`, `Real.lameDEk_eq`, `Real.lameSCEk_eq`,
  `Real.lameSDEk_eq`, `Real.lameCDEk_eq`, `Real.lameSCDEk_eq`: DLMF 29.12.1–29.12.8.
* `Real.lameAk_eq_lamePolyH_uE`, `Real.lameAk_eq_lamePolyH_sE`, `Real.lameBk_eq_lamePolyH_cE`,
  …, `Real.lameBk_eq_lamePolyH_scdE`: the eigenvalues `½(H_m + ν(ν+1)k²)`, DLMF 29.15.7,
  29.15.12, …, 29.15.42.
* `Real.lameUEk_fourier`, `Real.lameSEk_fourier`, …, `Real.lameSCDEk_fourier`: the finite
  Fourier series DLMF 29.15.1, 29.15.8, …, 29.15.38 in `φ = π/2 - am(x, k)` for real `x`.
* `lamePolyEk_zeros`: the zero counts of §29.12(i).
* `lamePolyEk_algebraic_form`: the algebraic form DLMF 29.12.9–29.12.10.
* `lamePolyEk_zeros_maximize`, `lamePolyEk_zeros_equilibrium`: the maximum principle and the
  electrostatic equilibrium of the zeros, DLMF 29.12.11–29.12.13.
* `Real.lameEck_even_fourierA_eq_zero`: for `ν = 2n` and `m ≤ n` the Fourier coefficients
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
`lamePolyH t n m k`. For `ρ, σ, τ` of 29.12.9: `ρ = ½` exactly for the types with a factor
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
theorem jacobiSnk_ofReal_eq_cos_lamePhi (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    jacobiSnk (x : ℂ) k = (Real.cos (Real.lamePhi x k) : ℂ) := by
  rw [jacobiSnk_ofReal hk0 hk1, Real.lamePhi, Real.cos_pi_div_two_sub, Real.jacobiSnm]

/-- For real `x` and `0 < k < 1`, `cn(x, k) = sin φ` with `φ = π/2 - am(x, k)` (29.2.5). -/
private lemma jacobiCnk_ofReal_eq_sin_lamePhi (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    jacobiCnk (x : ℂ) k = (Real.sin (Real.lamePhi x k) : ℂ) := by
  rw [jacobiCnk_ofReal hk0 hk1, Real.lamePhi, Real.sin_pi_div_two_sub, Real.jacobiCnm]

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
theorem Real.lameUEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameUEk n m x k = ((∑ p ∈ Finset.range (n + 1),
        (if p = 0 then 1 / 2 else 1) * lamePolyCoeff .uE n m k p *
        Real.cos ((2 * p) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameUEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, one_mul, jacobiSnk_ofReal_eq_cos_lamePhi hk0 hk1]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  have := chebyshevT_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [this]
  split_ifs <;> push_cast <;> ring

/-- 29.12.1: the Lamé polynomial `uE^m_{2n}(x, k²)` is the Lamé function
`Ec^{2m}_{2n}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18 (`lamePolyEk_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E1]
theorem Real.lameUEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameUEk n m x k = (Real.lameEck ((2 * n : ℕ) : ℝ) (2 * m) x k : ℂ) := by
  have hw : ∀ y : ℝ, (lamePolyEk .uE n m y k).re = ∑ p ∈ Finset.range (n + 1),
      ((if p = 0 then 1 / 2 else 1) * lamePolyCoeff .uE n m k p) *
        Real.cos (((2 * p : ℕ) : ℝ) * Real.lamePhi y k) :=
    fun y => by
      rw [show lamePolyEk .uE n m y k = lameUEk n m y k from rfl, Real.lameUEk_fourier hk0 hk1,
        Complex.ofReal_re]
      push_cast; rfl
  have hid := lamePolyEk_re_eq_lameEigenfunction hk0 hk1 .uE hm (σ := 1) ?_ one_pos ?_
  · have hreal : lameUEk n m x k = ((lamePolyEk .uE n m x k).re : ℂ) := by
      rw [show lamePolyEk .uE n m x k = lameUEk n m x k from rfl, Real.lameUEk_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEck, show (2 * m).bodd = false by simp [Nat.bodd_mul],
      show 2 * m / 2 = m by omega]
    rfl
  · rw [integral_cos_series_lamePhi_sq hk0 hk1 (n + 1) _ (e := fun p => 2 * p)
      (fun a b h => by simpa using h) (fun p q => ⟨p + q, by ring⟩) hw]
    simp only [LamePolyType.normForm]
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun p => lamePolyCoeff .uE n m k p ^ 2)]
    simp; ring_nf
    rw [Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by ring
  · simp only [lamePolyOddK, Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [cos_series_lamePhi_eval_K hk0 hk1 _ _ _ hw]
    simp only [LamePolyType.signForm]
    rw [Finset.sum_range_succ', sum_Ioc_zero_eq_sum_range_succ]
    simp; ring

/-- 29.15.7: the eigenvalue of `uE^m_{2n}` is
`a^{2m}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolyType_eq`). -/
@[dlmf 29.15.E7]
theorem Real.lameAk_eq_lamePolyH_uE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameAk ((2 * n : ℕ) : ℝ) (2 * m) k =
      (lamePolyH .uE n m k +
        ((2 * n : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolyType_eq hk0 hk1 .uE hm
  rw [Real.lameAk, show (2 * m).bodd = false by simp [Nat.bodd_mul],
    show 2 * m / 2 = m by omega]
  exact this

/-- 29.15.8: for real `x`, `sE^m(x, k²)` is a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E8]
theorem Real.lameSEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSEk n m x k = ((∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .sE n m k p *
        Real.cos ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, one_mul, jacobiSnk_ofReal_eq_cos_lamePhi hk0 hk1]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  have := chebyshevT_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [this]

/-- 29.12.2: the Lamé polynomial `sE^m_{2n+1}(x, k²)` is the Lamé function
`Ec^{2m+1}_{2n+1}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18 (`lamePolyEk_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E2]
theorem Real.lameSEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSEk n m x k = (Real.lameEck ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  have hw : ∀ y : ℝ, (lamePolyEk .sE n m y k).re = ∑ p ∈ Finset.range (n + 1),
      lamePolyCoeff .sE n m k p * Real.cos (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi y k) :=
    fun y => by
      rw [show lamePolyEk .sE n m y k = lameSEk n m y k from rfl, Real.lameSEk_fourier hk0 hk1,
        Complex.ofReal_re]
      push_cast; rfl
  have hid := lamePolyEk_re_eq_lameEigenfunction hk0 hk1 .sE hm (σ := 1) ?_ one_pos ?_
  · have hreal : lameSEk n m x k = ((lamePolyEk .sE n m x k).re : ℂ) := by
      rw [show lamePolyEk .sE n m x k = lameSEk n m x k from rfl, Real.lameSEk_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEck, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
      show (2 * m + 1) / 2 = m by omega]
    rfl
  · rw [integral_cos_series_lamePhi_sq hk0 hk1 (n + 1) _ (e := fun p => 2 * p + 1)
      (fun a b h => by simpa using h) (fun p q => ⟨p + q + 1, by ring⟩) hw]
    simp only [LamePolyType.normForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by simp; ring
  · simp only [lamePolyOddK, Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [cos_series_lamePhi_eval_K hk0 hk1 _ _ _ hw]
    rfl

/-- 29.15.12: the eigenvalue of `sE^m_{2n+1}` is
`a^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+1`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolyType_eq`). -/
@[dlmf 29.15.E12]
theorem Real.lameAk_eq_lamePolyH_sE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameAk ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolyH .sE n m k +
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolyType_eq hk0 hk1 .sE hm
  rw [Real.lameAk, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
    show (2 * m + 1) / 2 = m by omega]
  exact this

/-- 29.15.13: for real `x`, `cE^m(x, k²)` is a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E13]
theorem Real.lameCEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameCEk n m x k = ((∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .cE n m k p *
        Real.sin ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameCEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, jacobiSnk_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiCnk_ofReal_eq_sin_lamePhi hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := sin_mul_chebyshevU_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 1 : ℂ)) = (2 * p : ℂ) + 1 by ring, ← this]
  ring

/-- 29.12.3: the Lamé polynomial `cE^m_{2n+1}(x, k²)` is the Lamé function
`Es^{2m+1}_{2n+1}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18 (`lamePolyEk_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E3]
theorem Real.lameCEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameCEk n m x k = (Real.lameEsk ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolyEk .cE n m y k).re = ∑ p ∈ Finset.range (n + 1),
      lamePolyCoeff .cE n m k p * Real.sin (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi y k) :=
    fun y => by
      rw [show lamePolyEk .cE n m y k = lameCEk n m y k from rfl, Real.lameCEk_fourier hk0 hk1,
        Complex.ofReal_re]
      push_cast; rfl
  have hid := lamePolyEk_re_eq_lameEigenfunction hk0 hk1 .cE hm
    (σ := Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2)) ?_ (Real.jacobiDnm_pos hk _) ?_
  · have hreal : lameCEk n m x k = ((lamePolyEk .cE n m x k).re : ℂ) := by
      rw [show lamePolyEk .cE n m x k = lameCEk n m x k from rfl, Real.lameCEk_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEsk, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
      show (2 * m + 1 - 1) / 2 = m by omega]
    rfl
  · rw [integral_sin_series_lamePhi_sq hk0 hk1 (n + 1) _ (e := fun p => 2 * p + 1)
      (fun a b h => by simpa using h) (fun p q => ⟨p + q + 1, by ring⟩) hw]
    simp only [LamePolyType.normForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by simp; ring
  · simp only [lamePolyOddK, ↓reduceIte]
    rw [deriv_sin_series_lamePhi_K hk0 hk1 _ _ (fun p => ((2 * p + 1 : ℕ) : ℝ)) hw]
    simp only [LamePolyType.signForm]
    push_cast; rfl

/-- 29.15.17: the eigenvalue of `cE^m_{2n+1}` is
`b^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+1`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolyType_eq`). -/
@[dlmf 29.15.E17]
theorem Real.lameBk_eq_lamePolyH_cE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameBk ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolyH .cE n m k +
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolyType_eq hk0 hk1 .cE hm
  rw [Real.lameBk, show (!(2 * m + 1).bodd) = false by simp [Nat.bodd_mul],
    show (2 * m + 1 - 1) / 2 = m by omega]
  exact this

/-- 29.15.18: for real `x`, `dE^m(x, k²)` is `dn(x, k)` times a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E18]
theorem Real.lameDEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameDEk n m x k = ((Real.jacobiDnm x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        (if p = 0 then 1 / 2 else 1) * lamePolyCoeff .dE n m k p *
        Real.cos ((2 * p) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameDEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, jacobiSnk_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiDnk_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := chebyshevT_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [this]
  split_ifs <;> push_cast <;> ring

/-- 29.12.4: the Lamé polynomial `dE^m_{2n+1}(x, k²)` is the Lamé function
`Ec^{2m}_{2n+1}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18 (`lamePolyEk_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E4]
theorem Real.lameDEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameDEk n m x k = (Real.lameEck ((2 * n + 1 : ℕ) : ℝ) (2 * m) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolyEk .dE n m y k).re = Real.jacobiDnm y (k ^ 2) *
      ∑ p ∈ Finset.range (n + 1), ((if p = 0 then 1 / 2 else 1) * lamePolyCoeff .dE n m k p) *
        Real.cos (((2 * p + 0 : ℕ) : ℝ) * Real.lamePhi y k) := fun y => by
    rw [show lamePolyEk .dE n m y k = lameDEk n m y k from rfl, Real.lameDEk_fourier hk0 hk1,
      Complex.ofReal_re]
    push_cast; simp
  have hid := lamePolyEk_re_eq_lameEigenfunction hk0 hk1 .dE hm
    (σ := Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2)) ?_ (Real.jacobiDnm_pos hk _) ?_
  · have hreal : lameDEk n m x k = ((lamePolyEk .dE n m x k).re : ℂ) := by
      rw [show lamePolyEk .dE n m x k = lameDEk n m x k from rfl, Real.lameDEk_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEck, show (2 * m).bodd = false by simp [Nat.bodd_mul],
      show 2 * m / 2 = m by omega]
    rfl
  · rw [integral_dn_cos_series_lamePhi_sq hk0 hk1 (n + 1) _ 0 (by simp [lamePolyCoeff]) hw]
    set c := lamePolyCoeff .dE n m k with hc
    have hc1 : c (n + 1) = 0 := by simp [hc, lamePolyCoeff]
    rw [dnNorm_extraTerm_zero _ n (by simp [hc1])]
    have h1 : ∀ p, (if p = 0 then 1 / 2 else 1) * c p * ((if p + 1 = 0 then 1 / 2 else 1) *
        c (p + 1)) = c p * c (p + 1) - (if p = 0 then c 0 * c 1 / 2 else 0) := by
      intro p; rcases p with _ | p <;> simp; ring
    rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.sum_range_succ (fun p => c p * c (p + 1)), hc1]
    simp only [LamePolyType.normForm]
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun p => c p ^ 2)]
    simp
    rw [← Finset.sum_mul]
    ring
  · simp only [lamePolyOddK, Bool.false_eq_true, ↓reduceIte]
    rw [dn_cos_series_lamePhi_eval_K hk0 hk1 _ _ _ hw]
    simp only [LamePolyType.signForm]
    rw [Finset.sum_range_succ', sum_Ioc_zero_eq_sum_range_succ]
    congr 1
    simp [add_comm, div_eq_inv_mul]

/-- 29.15.22: the eigenvalue of `dE^m_{2n+1}` is
`a^{2m}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+1`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolyType_eq`). -/
@[dlmf 29.15.E22]
theorem Real.lameAk_eq_lamePolyH_dE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameAk ((2 * n + 1 : ℕ) : ℝ) (2 * m) k =
      (lamePolyH .dE n m k +
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolyType_eq hk0 hk1 .dE hm
  rw [Real.lameAk, show (2 * m).bodd = false by simp [Nat.bodd_mul],
    show 2 * m / 2 = m by omega]
  exact this

/-- 29.15.23: for real `x`, `scE^m(x, k²)` is a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E23]
theorem Real.lameSCEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSCEk n m x k = ((∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .scE n m k p *
        Real.sin ((2 * p + 2) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSCEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, jacobiSnk_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiCnk_ofReal_eq_sin_lamePhi hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := sin_mul_chebyshevU_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 2 : ℂ)) = (2 * p + 1 : ℂ) + 1 by ring, ← this]
  ring

/-- 29.12.5: the Lamé polynomial `scE^m_{2n+2}(x, k²)` is the Lamé function
`Es^{2m+2}_{2n+2}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18 (`lamePolyEk_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E5]
theorem Real.lameSCEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSCEk n m x k = (Real.lameEsk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 2) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolyEk .scE n m y k).re = ∑ p ∈ Finset.range (n + 1),
      lamePolyCoeff .scE n m k p * Real.sin (((2 * p + 2 : ℕ) : ℝ) * Real.lamePhi y k) :=
    fun y => by
      rw [show lamePolyEk .scE n m y k = lameSCEk n m y k from rfl,
        Real.lameSCEk_fourier hk0 hk1, Complex.ofReal_re]
      push_cast; rfl
  have hid := lamePolyEk_re_eq_lameEigenfunction hk0 hk1 .scE hm
    (σ := Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2)) ?_ (Real.jacobiDnm_pos hk _) ?_
  · have hreal : lameSCEk n m x k = ((lamePolyEk .scE n m x k).re : ℂ) := by
      rw [show lamePolyEk .scE n m x k = lameSCEk n m x k from rfl, Real.lameSCEk_fourier hk0 hk1,
        Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEsk, show (2 * m + 2).bodd = false by simp [Nat.bodd_mul],
      show (2 * m + 2 - 1) / 2 = m by omega]
    rfl
  · rw [integral_sin_series_lamePhi_sq hk0 hk1 (n + 1) _ (e := fun p => 2 * p + 2)
      (fun a b h => by simpa using h) (fun p q => ⟨p + q + 2, by ring⟩) hw]
    simp only [LamePolyType.normForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by simp; ring
  · simp only [lamePolyOddK, ↓reduceIte]
    rw [deriv_sin_series_lamePhi_K hk0 hk1 _ _ (fun p => ((2 * p + 2 : ℕ) : ℝ)) hw]
    simp only [LamePolyType.signForm]
    push_cast; rfl

/-- 29.15.27: the eigenvalue of `scE^m_{2n+2}` is
`b^{2m+2}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+2`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolyType_eq`). -/
@[dlmf 29.15.E27]
theorem Real.lameBk_eq_lamePolyH_scE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameBk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 2) k =
      (lamePolyH .scE n m k +
        ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolyType_eq hk0 hk1 .scE hm
  rw [Real.lameBk, show (!(2 * m + 2).bodd) = true by simp [Nat.bodd_mul],
    show (2 * m + 2 - 1) / 2 = m by omega]
  exact this

/-- 29.15.28: for real `x`, `sdE^m(x, k²)` is `dn(x, k)` times a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E28]
theorem Real.lameSDEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSDEk n m x k = ((Real.jacobiDnm x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .sdE n m k p *
        Real.cos ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSDEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, jacobiSnk_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiDnk_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := chebyshevT_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [this]

/-- 29.12.6: the Lamé polynomial `sdE^m_{2n+2}(x, k²)` is the Lamé function
`Ec^{2m+1}_{2n+2}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18 (`lamePolyEk_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E6]
theorem Real.lameSDEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSDEk n m x k = (Real.lameEck ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolyEk .sdE n m y k).re = Real.jacobiDnm y (k ^ 2) *
      ∑ p ∈ Finset.range (n + 1), lamePolyCoeff .sdE n m k p *
        Real.cos (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi y k) := fun y => by
    rw [show lamePolyEk .sdE n m y k = lameSDEk n m y k from rfl,
      Real.lameSDEk_fourier hk0 hk1, Complex.ofReal_re]
    push_cast; simp
  have hid := lamePolyEk_re_eq_lameEigenfunction hk0 hk1 .sdE hm
    (σ := Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2)) ?_ (Real.jacobiDnm_pos hk _) ?_
  · have hreal : lameSDEk n m x k = ((lamePolyEk .sdE n m x k).re : ℂ) := by
      rw [show lamePolyEk .sdE n m x k = lameSDEk n m x k from rfl,
        Real.lameSDEk_fourier hk0 hk1, Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEck, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
      show (2 * m + 1) / 2 = m by omega]
    rfl
  · rw [integral_dn_cos_series_lamePhi_sq hk0 hk1 (n + 1) _ 1 (by simp [lamePolyCoeff]) hw]
    set c := lamePolyCoeff .sdE n m k with hc
    have hc1 : c (n + 1) = 0 := by simp [hc, lamePolyCoeff]
    rw [dnNorm_extraTerm_one _ n, Finset.sum_range_succ (fun p => c p * c (p + 1)), hc1, mul_zero, add_zero]
    have h0 : ∀ p : ℕ, (2 * p + 1 = 0) = False := fun p => eq_false (by omega)
    simp only [LamePolyType.normForm, h0, ↓reduceIte, ← Finset.sum_mul]
    ring
  · simp only [lamePolyOddK, Bool.false_eq_true, ↓reduceIte]
    rw [dn_cos_series_lamePhi_eval_K hk0 hk1 _ _ _ hw]
    rfl

/-- 29.15.32: the eigenvalue of `sdE^m_{2n+2}` is
`a^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+2`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolyType_eq`). -/
@[dlmf 29.15.E32]
theorem Real.lameAk_eq_lamePolyH_sdE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameAk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolyH .sdE n m k +
        ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolyType_eq hk0 hk1 .sdE hm
  rw [Real.lameAk, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
    show (2 * m + 1) / 2 = m by omega]
  exact this

/-- 29.15.33: for real `x`, `cdE^m(x, k²)` is `dn(x, k)` times a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E33]
theorem Real.lameCDEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameCDEk n m x k = ((Real.jacobiDnm x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .cdE n m k p *
        Real.sin ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameCDEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, jacobiSnk_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiCnk_ofReal_eq_sin_lamePhi hk0 hk1, jacobiDnk_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := sin_mul_chebyshevU_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 1 : ℂ)) = (2 * p : ℂ) + 1 by ring, ← this]
  ring

/-- 29.12.7: the Lamé polynomial `cdE^m_{2n+2}(x, k²)` is the Lamé function
`Es^{2m+1}_{2n+2}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18 (`lamePolyEk_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E7]
theorem Real.lameCDEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameCDEk n m x k = (Real.lameEsk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolyEk .cdE n m y k).re = Real.jacobiDnm y (k ^ 2) *
      ∑ p ∈ Finset.range (n + 1), lamePolyCoeff .cdE n m k p *
        Real.sin (((2 * p + 1 : ℕ) : ℝ) * Real.lamePhi y k) := fun y => by
    rw [show lamePolyEk .cdE n m y k = lameCDEk n m y k from rfl,
      Real.lameCDEk_fourier hk0 hk1, Complex.ofReal_re]
    push_cast; simp
  have hid := lamePolyEk_re_eq_lameEigenfunction hk0 hk1 .cdE hm
    (σ := Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2) ^ 2) ?_
    (pow_pos (Real.jacobiDnm_pos hk _) 2) ?_
  · have hreal : lameCDEk n m x k = ((lamePolyEk .cdE n m x k).re : ℂ) := by
      rw [show lamePolyEk .cdE n m x k = lameCDEk n m x k from rfl,
        Real.lameCDEk_fourier hk0 hk1, Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEsk, show (2 * m + 1).bodd = true by simp [Nat.bodd_mul],
      show (2 * m + 1 - 1) / 2 = m by omega]
    rfl
  · rw [integral_dn_sin_series_lamePhi_sq hk0 hk1 (n + 1) _ 1 (by simp [lamePolyCoeff]) hw]
    set c := lamePolyCoeff .cdE n m k with hc
    have hc1 : c (n + 1) = 0 := by simp [hc, lamePolyCoeff]
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [dnNorm_extraTerm_one _ n, Finset.sum_range_succ (fun p => c p * c (p + 1)), hc1, mul_zero, add_zero]
    have h0 : ∀ p : ℕ, (2 * p + 1 = 0) = False := fun p => eq_false (by omega)
    simp only [LamePolyType.normForm, h0, ↓reduceIte, ← Finset.sum_mul]
    ring
  · simp only [lamePolyOddK, ↓reduceIte]
    rw [deriv_dn_sin_series_lamePhi_K hk0 hk1 _ _ (fun p => ((2 * p + 1 : ℕ) : ℝ)) hw]
    simp only [LamePolyType.signForm]
    push_cast; rfl

/-- 29.15.37: the eigenvalue of `cdE^m_{2n+2}` is
`b^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+2`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolyType_eq`). -/
@[dlmf 29.15.E37]
theorem Real.lameBk_eq_lamePolyH_cdE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameBk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolyH .cdE n m k +
        ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolyType_eq hk0 hk1 .cdE hm
  rw [Real.lameBk, show (!(2 * m + 1).bodd) = false by simp [Nat.bodd_mul],
    show (2 * m + 1 - 1) / 2 = m by omega]
  exact this

/-- 29.15.38: for real `x`, `scdE^m(x, k²)` is `dn(x, k)` times a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E38]
theorem Real.lameSCDEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSCDEk n m x k = ((Real.jacobiDnm x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .scdE n m k p *
        Real.sin ((2 * p + 2) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSCDEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, jacobiSnk_ofReal_eq_cos_lamePhi hk0 hk1,
    jacobiCnk_ofReal_eq_sin_lamePhi hk0 hk1, jacobiDnk_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := sin_mul_chebyshevU_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 2 : ℂ)) = (2 * p + 1 : ℂ) + 1 by ring, ← this]
  ring

/-- 29.12.8: the Lamé polynomial `scdE^m_{2n+3}(x, k²)` is the Lamé function
`Es^{2m+2}_{2n+3}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Proved
from the eigenvalue identification and the normalization 29.3.18 (`lamePolyEk_re_eq_lameEigenfunction`). -/
@[dlmf 29.12.E8]
theorem Real.lameSCDEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSCDEk n m x k = (Real.lameEsk ((2 * n + 3 : ℕ) : ℝ) (2 * m + 2) x k : ℂ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw : ∀ y : ℝ, (lamePolyEk .scdE n m y k).re = Real.jacobiDnm y (k ^ 2) *
      ∑ p ∈ Finset.range (n + 1), lamePolyCoeff .scdE n m k p *
        Real.sin (((2 * p + 2 : ℕ) : ℝ) * Real.lamePhi y k) := fun y => by
    rw [show lamePolyEk .scdE n m y k = lameSCDEk n m y k from rfl,
      Real.lameSCDEk_fourier hk0 hk1, Complex.ofReal_re]
    push_cast; simp
  have hid := lamePolyEk_re_eq_lameEigenfunction hk0 hk1 .scdE hm
    (σ := Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2) ^ 2) ?_
    (pow_pos (Real.jacobiDnm_pos hk _) 2) ?_
  · have hreal : lameSCDEk n m x k = ((lamePolyEk .scdE n m x k).re : ℂ) := by
      rw [show lamePolyEk .scdE n m x k = lameSCDEk n m x k from rfl,
        Real.lameSCDEk_fourier hk0 hk1, Complex.ofReal_re]
    have := congrFun hid x
    rw [hreal, this, Real.lameEsk, show (2 * m + 2).bodd = false by simp [Nat.bodd_mul],
      show (2 * m + 2 - 1) / 2 = m by omega]
    rfl
  · rw [integral_dn_sin_series_lamePhi_sq hk0 hk1 (n + 1) _ 2 (by simp [lamePolyCoeff]) hw]
    set c := lamePolyCoeff .scdE n m k with hc
    have hc1 : c (n + 1) = 0 := by simp [hc, lamePolyCoeff]
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [dnNorm_extraTerm_two _ (n + 1), Finset.sum_range_succ (fun p => c p * c (p + 1)), hc1, mul_zero,
      add_zero]
    have h0 : ∀ p : ℕ, (2 * p + 2 = 0) = False := fun p => eq_false (by omega)
    simp only [LamePolyType.normForm, h0, ↓reduceIte, ← Finset.sum_mul]
    ring
  · simp only [lamePolyOddK, ↓reduceIte]
    rw [deriv_dn_sin_series_lamePhi_K hk0 hk1 _ _ (fun p => ((2 * p + 2 : ℕ) : ℝ)) hw]
    simp only [LamePolyType.signForm]
    push_cast; rfl

/-- 29.15.42: the eigenvalue of `scdE^m_{2n+3}` is
`b^{2m+2}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+3`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Proved by Sturm's
oscillation theorem (`lameEigenvalue_lamePolyType_eq`). -/
@[dlmf 29.15.E42]
theorem Real.lameBk_eq_lamePolyH_scdE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameBk ((2 * n + 3 : ℕ) : ℝ) (2 * m + 2) k =
      (lamePolyH .scdE n m k +
        ((2 * n + 3 : ℕ) : ℝ) * (((2 * n + 3 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  have := lameEigenvalue_lamePolyType_eq hk0 hk1 .scdE hm
  rw [Real.lameBk, show (!(2 * m + 2).bodd) = true by simp [Nat.bodd_mul],
    show (2 * m + 2 - 1) / 2 = m by omega]
  exact this

/-- §29.12(i): the Lamé polynomial `t^m` (`m ≤ n`) has exactly `m` zeros in `(0, K)` and
exactly `n - m` zeros on the open segment from `K` to `K + iK'`. Proved by Sturm oscillation
on both sides (`ncard_zeros_lamePolyEk_real`, `ncard_zeros_lamePolyEk_vertical`). -/
@[dlmf 29.12.i]
theorem lamePolyEk_zeros (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) {n m : ℕ}
    (hm : m ≤ n) :
    {x : ℝ | x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2)) ∧ lamePolyEk t n m x k = 0}.ncard = m ∧
      {y : ℝ | y ∈ Ioo 0 (Real.compEllIntKm (1 - k ^ 2)) ∧
        lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + I * y) k = 0}.ncard = n - m :=
  ⟨ncard_zeros_lamePolyEk_real hk0 hk1 t hm, ncard_zeros_lamePolyEk_vertical hk0 hk1 t hm⟩

/-! ### Algebraic form and zeros (§§29.12(ii), 29.12(iii)) -/

/-- 29.12.9 and 29.12.10: with `ξ = sn²(z, k)` the Lamé polynomial is
`ξ^ρ (ξ - 1)^σ (ξ - k⁻²)^τ P(ξ)` (up to the choice of branches, i.e. up to the constant
factor `(-1)^σ (-k⁻²)^τ` relating `(ξ - 1)^σ (ξ - k⁻²)^τ` to `cn^{2σ} dn^{2τ}`), where `P`
has degree `n` and simple zeros, `m` of them in `(0, 1)` and `n - m` in `(1, k⁻²)`; it
satisfies the algebraic form 29.2.2 of Lamé's equation. Here the polynomial form is stated as
in `lamePolyEk_polynomial_form`, and the zero locations are added. Proved from the zero counts
of §29.12(i) (`exists_poly_roots_lamePolyEk`). -/
@[dlmf 29.12.E9, dlmf 29.12.E10]
theorem lamePolyEk_algebraic_form (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], P.natDegree = n ∧ P.roots.Nodup ∧ P.roots.card = n ∧
      (P.roots.filter (· ∈ Ioo (0 : ℝ) 1)).card = m ∧
      (P.roots.filter (· ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹)).card = n - m ∧
      ∀ z : ℂ, lamePolyEk t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSnk z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSnk z k ^ 2) :=
  exists_poly_roots_lamePolyEk hk0 hk1 t hm

/-- 29.12.11–29.12.12: with `ξ₁ < ⋯ < ξₙ` the zeros of `P` (29.12.10) and `ρ, σ, τ` as in
29.12.9, the function
`g(t) = (∏_p t_p^{ρ+¼} |t_p - 1|^{σ+¼} (k⁻² - t_p)^{τ+¼}) ∏_{q<r} (t_r - t_q)` on the region
`0 ≤ t₁ ≤ ⋯ ≤ t_m ≤ 1 ≤ t_{m+1} ≤ ⋯ ≤ t_n ≤ k⁻²` attains its absolute maximum exactly at
`t = ξ`. Admitted. -/
@[dlmf 29.12.E11, dlmf 29.12.E12]
theorem lamePolyEk_zeros_maximize (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], (P.natDegree = n ∧ ∀ z : ℂ, lamePolyEk t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSnk z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSnk z k ^ 2)) ∧
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
  sorry

/-- 29.12.13: the zeros `ξ_p` of `P` satisfy the equilibrium relations
`(ρ+¼)/ξ_p + (σ+¼)/(ξ_p - 1) + (τ+¼)/(ξ_p - k⁻²) + ∑_{q ≠ p} 1/(ξ_p - ξ_q) = 0`
(electrostatic interpretation, §29.12(iii)). Admitted. -/
@[dlmf 29.12.E13, dlmf 29.12.iii]
theorem lamePolyEk_zeros_equilibrium (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], (P.natDegree = n ∧ P.roots.Nodup ∧ ∀ z : ℂ, lamePolyEk t n m z k =
        t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSnk z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSnk z k ^ 2)) ∧
      ∀ ξ ∈ P.roots,
        ((if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4) / ξ +
          ((if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4) / (ξ - 1) +
          ((if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then 1 / 2 else 0) + 1 / 4) /
            (ξ - (k ^ 2)⁻¹) +
          ((P.roots.erase ξ).map fun η => 1 / (ξ - η)).sum = 0 := by
  sorry

/-! ### The terminating Fourier series of §29.6(i) -/

/-- §29.6(i): for `ν = 2n` and `m = 0, 1, …, n` the Fourier coefficients `A_{2p}` of
`Ec^{2m}_{2n}` vanish for `p > n`, so `Ec^{2m}_{2n}` reduces to a Lamé polynomial (compare
§§29.12(i), 29.15(i)). Proved from the finite Fourier series 29.15.1 (`Real.lameUEk_eq`,
`Real.lameUEk_fourier`) and the orthogonality of `cos(2qφ)` on `[0, π/2]`. -/
@[dlmf 29.6.i]
theorem Real.lameEck_even_fourierA_eq_zero (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n)
    {p : ℕ} (hp : n < p) :
    Real.lameCosCoeff (fun x => Real.lameEck (2 * n : ℕ) (2 * m) x k) k true (2 * p) = 0 := by
  set b : ℕ → ℝ := fun q => (if q = 0 then 1 / 2 else 1) * lamePolyCoeff .uE n m k q
  have hE : ∀ x : ℝ, Real.lameEck (2 * n : ℕ) (2 * m) x k =
      ∑ q ∈ Finset.range (n + 1), b q * Real.cos ((2 * q) * Real.lamePhi x k) := fun x => by
    have h := (Real.lameUEk_eq hk0 hk1 hm x).symm.trans (Real.lameUEk_fourier hk0 hk1 n m x)
    exact_mod_cast h
  rw [Real.lameCosCoeff]
  simp only [↓reduceIte]
  have e : ∀ x : ℝ, Real.lameEck (2 * n : ℕ) (2 * m) x k *
      Real.cos (((2 * p : ℕ) : ℝ) * Real.lamePhi x k) * Real.jacobiDnm x (k ^ 2) =
      Real.jacobiDnm x (k ^ 2) * (fun t => ∑ q ∈ Finset.range (n + 1),
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
    integral_jacobiDnm_mul_comp_lamePhi (g := fun t => ∑ q ∈ Finset.range (n + 1),
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
