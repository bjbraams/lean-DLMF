/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.Defs
public import DLMF.Lame.Eigenvalues
public import DLMF.JacobiElliptic.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Lamé polynomials: definitions, algebraic form, zeros and Fourier series (DLMF §§29.12, 29.15)

The Lamé polynomials of the eight types of Table 29.12.1 are defined in
`DLMF.Lame.Polynomials.Defs` by their Chebyshev series 29.15.43–29.15.50, with the
coefficients and eigenvalues of the finite matrix problems 29.15.2–29.15.6 (and the analogues
for the other seven types). This file states

* 29.12.1–29.12.8: these are the Lamé functions `Ec`, `Es` of §29.3 at integer order
  (admitted);
* 29.15.7, 29.15.12, …, 29.15.42: the eigenvalues are `½(H_m + ν(ν+1)k²)` (admitted), and
  29.15.3: the matrix eigenvalues are real and simple (admitted);
* 29.15.1, 29.15.8, …, 29.15.38: the finite Fourier series in `φ = π/2 - am(x, k)` for real
  `x` (proved from the Chebyshev identities of §29.15(ii) and `cos φ = sn`, `sin φ = cn`);
* Table 29.12.1 (polynomial form, periods and parities), 29.12.9 (algebraic form and location of
  the zeros of `P`), the zero counts of §29.12(i), and 29.12.10–29.12.13 (the maximum
  principle and the electrostatic equilibrium of the zeros) (admitted).

The order `ν` is the nonnegative integer `t.order n` (§29.12(i)); the eigenvalue `H_m` is
`lamePolyH t n m k`. For `ρ, σ, τ` of 29.12.9: `ρ = ½` exactly for the types with a factor
`sn` (`sE, scE, sdE, scdE`), `σ = ½` for a factor `cn` (`cE, scE, cdE, scdE`) and `τ = ½` for
a factor `dn` (`dE, sdE, cdE, scdE`); these are written in place in the statements. The
equilibrium relation 29.12.13 was checked numerically for all eight types.
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
lemma l29_sn_eq_cos (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    jacobiSnk (x : ℂ) k = (Real.cos (Real.lamePhi x k) : ℂ) := by
  rw [jacobiSnk_ofReal hk0 hk1, Real.lamePhi, Real.cos_pi_div_two_sub, Real.jacobiSnm]

/-- For real `x` and `0 < k < 1`, `cn(x, k) = sin φ` with `φ = π/2 - am(x, k)` (29.2.5). -/
lemma l29_cn_eq_sin (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    jacobiCnk (x : ℂ) k = (Real.sin (Real.lamePhi x k) : ℂ) := by
  rw [jacobiCnk_ofReal hk0 hk1, Real.lamePhi, Real.sin_pi_div_two_sub, Real.jacobiCnm]

/-- §29.15(ii): `cos(jθ) = T_j(cos θ)`. -/
@[dlmf 29.15.ii]
lemma l29_T_cos (j : ℕ) (θ : ℝ) :
    (Chebyshev.T ℂ (j : ℤ)).eval (Real.cos θ : ℂ) = (Real.cos (j * θ) : ℂ) := by
  have := Chebyshev.T_complex_cos (θ : ℂ) j
  push_cast at this ⊢
  exact this

/-- §29.15(ii): `sin((j+1)θ) = sin θ U_j(cos θ)`. -/
@[dlmf 29.15.ii]
lemma l29_U_cos (j : ℕ) (θ : ℝ) :
    (Real.sin θ : ℂ) * (Chebyshev.U ℂ (j : ℤ)).eval (Real.cos θ : ℂ) =
      (Real.sin ((j + 1) * θ) : ℂ) := by
  have := Chebyshev.U_complex_cos (θ : ℂ) j
  push_cast at this ⊢
  rw [mul_comm]
  exact this

/-! ### The eight types (29.12.1–29.12.8) and their Fourier series (§29.15(i)) -/

/-- 29.12.1: the Lamé polynomial `uE^m_{2n}(x, k²)` is the Lamé function
`Ec^{2m}_{2n}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.12.E1]
theorem Real.lameUEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameUEk n m x k = (Real.lameEck ((2 * n : ℕ) : ℝ) (2 * m) x k : ℂ) := by
  sorry

/-- 29.15.1: for real `x`, `uE^m(x, k²)` is a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E1]
theorem Real.lameUEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameUEk n m x k = ((∑ p ∈ Finset.range (n + 1),
        (if p = 0 then 1 / 2 else 1) * lamePolyCoeff .uE n m k p *
        Real.cos ((2 * p) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameUEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, one_mul, l29_sn_eq_cos hk0 hk1]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  have := l29_T_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [this]
  split_ifs <;> push_cast <;> ring

/-- 29.15.7: the eigenvalue of `uE^m_{2n}` is
`a^{2m}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.15.E7]
theorem Real.lameAk_eq_lamePolyH_uE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameAk ((2 * n : ℕ) : ℝ) (2 * m) k =
      (lamePolyH .uE n m k +
        ((2 * n : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  sorry

/-- 29.12.2: the Lamé polynomial `sE^m_{2n+1}(x, k²)` is the Lamé function
`Ec^{2m+1}_{2n+1}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.12.E2]
theorem Real.lameSEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSEk n m x k = (Real.lameEck ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  sorry

/-- 29.15.8: for real `x`, `sE^m(x, k²)` is a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E8]
theorem Real.lameSEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSEk n m x k = ((∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .sE n m k p *
        Real.cos ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, one_mul, l29_sn_eq_cos hk0 hk1]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  have := l29_T_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [this]

/-- 29.15.12: the eigenvalue of `sE^m_{2n+1}` is
`a^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+1`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.15.E12]
theorem Real.lameAk_eq_lamePolyH_sE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameAk ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolyH .sE n m k +
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  sorry

/-- 29.12.3: the Lamé polynomial `cE^m_{2n+1}(x, k²)` is the Lamé function
`Es^{2m+1}_{2n+1}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.12.E3]
theorem Real.lameCEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameCEk n m x k = (Real.lameEsk ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  sorry

/-- 29.15.13: for real `x`, `cE^m(x, k²)` is a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E13]
theorem Real.lameCEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameCEk n m x k = ((∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .cE n m k p *
        Real.sin ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameCEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, l29_sn_eq_cos hk0 hk1,
    l29_cn_eq_sin hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := l29_U_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 1 : ℂ)) = (2 * p : ℂ) + 1 by ring, ← this]
  ring

/-- 29.15.17: the eigenvalue of `cE^m_{2n+1}` is
`b^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+1`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.15.E17]
theorem Real.lameBk_eq_lamePolyH_cE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameBk ((2 * n + 1 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolyH .cE n m k +
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  sorry

/-- 29.12.4: the Lamé polynomial `dE^m_{2n+1}(x, k²)` is the Lamé function
`Ec^{2m}_{2n+1}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.12.E4]
theorem Real.lameDEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameDEk n m x k = (Real.lameEck ((2 * n + 1 : ℕ) : ℝ) (2 * m) x k : ℂ) := by
  sorry

/-- 29.15.18: for real `x`, `dE^m(x, k²)` is `dn(x, k)` times a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E18]
theorem Real.lameDEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameDEk n m x k = ((Real.jacobiDnm x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        (if p = 0 then 1 / 2 else 1) * lamePolyCoeff .dE n m k p *
        Real.cos ((2 * p) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameDEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, l29_sn_eq_cos hk0 hk1,
    jacobiDnk_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := l29_T_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [this]
  split_ifs <;> push_cast <;> ring

/-- 29.15.22: the eigenvalue of `dE^m_{2n+1}` is
`a^{2m}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+1`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.15.E22]
theorem Real.lameAk_eq_lamePolyH_dE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameAk ((2 * n + 1 : ℕ) : ℝ) (2 * m) k =
      (lamePolyH .dE n m k +
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  sorry

/-- 29.12.5: the Lamé polynomial `scE^m_{2n+2}(x, k²)` is the Lamé function
`Es^{2m+2}_{2n+2}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.12.E5]
theorem Real.lameSCEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSCEk n m x k = (Real.lameEsk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 2) x k : ℂ) := by
  sorry

/-- 29.15.23: for real `x`, `scE^m(x, k²)` is a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E23]
theorem Real.lameSCEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSCEk n m x k = ((∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .scE n m k p *
        Real.sin ((2 * p + 2) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSCEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, l29_sn_eq_cos hk0 hk1,
    l29_cn_eq_sin hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := l29_U_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 2 : ℂ)) = (2 * p + 1 : ℂ) + 1 by ring, ← this]
  ring

/-- 29.15.27: the eigenvalue of `scE^m_{2n+2}` is
`b^{2m+2}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+2`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.15.E27]
theorem Real.lameBk_eq_lamePolyH_scE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameBk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 2) k =
      (lamePolyH .scE n m k +
        ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  sorry

/-- 29.12.6: the Lamé polynomial `sdE^m_{2n+2}(x, k²)` is the Lamé function
`Ec^{2m+1}_{2n+2}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.12.E6]
theorem Real.lameSDEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSDEk n m x k = (Real.lameEck ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  sorry

/-- 29.15.28: for real `x`, `sdE^m(x, k²)` is `dn(x, k)` times a finite Fourier cos series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E28]
theorem Real.lameSDEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSDEk n m x k = ((Real.jacobiDnm x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .sdE n m k p *
        Real.cos ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSDEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, l29_sn_eq_cos hk0 hk1,
    jacobiDnk_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := l29_T_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [this]

/-- 29.15.32: the eigenvalue of `sdE^m_{2n+2}` is
`a^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+2`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.15.E32]
theorem Real.lameAk_eq_lamePolyH_sdE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameAk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolyH .sdE n m k +
        ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  sorry

/-- 29.12.7: the Lamé polynomial `cdE^m_{2n+2}(x, k²)` is the Lamé function
`Es^{2m+1}_{2n+2}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.12.E7]
theorem Real.lameCDEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameCDEk n m x k = (Real.lameEsk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) x k : ℂ) := by
  sorry

/-- 29.15.33: for real `x`, `cdE^m(x, k²)` is `dn(x, k)` times a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E33]
theorem Real.lameCDEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameCDEk n m x k = ((Real.jacobiDnm x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .cdE n m k p *
        Real.sin ((2 * p + 1) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameCDEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, l29_sn_eq_cos hk0 hk1,
    l29_cn_eq_sin hk0 hk1, jacobiDnk_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := l29_U_cos (2 * p) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 1 : ℂ)) = (2 * p : ℂ) + 1 by ring, ← this]
  ring

/-- 29.15.37: the eigenvalue of `cdE^m_{2n+2}` is
`b^{2m+1}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+2`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.15.E37]
theorem Real.lameBk_eq_lamePolyH_cdE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameBk ((2 * n + 2 : ℕ) : ℝ) (2 * m + 1) k =
      (lamePolyH .cdE n m k +
        ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 2 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  sorry

/-- 29.12.8: the Lamé polynomial `scdE^m_{2n+3}(x, k²)` is the Lamé function
`Es^{2m+2}_{2n+3}(x, k²)` of §29.3 (real `x`, `0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.12.E8]
theorem Real.lameSCDEk_eq (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) (x : ℝ) :
    lameSCDEk n m x k = (Real.lameEsk ((2 * n + 3 : ℕ) : ℝ) (2 * m + 2) x k : ℂ) := by
  sorry

/-- 29.15.38: for real `x`, `scdE^m(x, k²)` is `dn(x, k)` times a finite Fourier sin series in
`φ = π/2 - am(x, k)` (29.2.5) with the coefficients of §29.15(i). -/
@[dlmf 29.15.E38]
theorem Real.lameSCDEk_fourier (hk0 : 0 < k) (hk1 : k < 1) (n m : ℕ) (x : ℝ) :
    lameSCDEk n m x k = ((Real.jacobiDnm x (k ^ 2) * ∑ p ∈ Finset.range (n + 1),
        lamePolyCoeff .scdE n m k p *
        Real.sin ((2 * p + 2) * Real.lamePhi x k) : ℝ) : ℂ) := by
  rw [lameSCDEk, lamePolyEk]
  simp only [LamePolyType.prefactor, LamePolyType.basis, l29_sn_eq_cos hk0 hk1,
    l29_cn_eq_sin hk0 hk1, jacobiDnk_ofReal hk0 hk1]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := l29_U_cos (2 * p + 1) (Real.lamePhi x k)
  push_cast at this
  rw [show ((2 * p + 2 : ℂ)) = (2 * p + 1 : ℂ) + 1 by ring, ← this]
  ring

/-- 29.15.42: the eigenvalue of `scdE^m_{2n+3}` is
`b^{2m+2}_ν(k²) = ½(H_m + ν(ν+1)k²)`, `ν = 2n+3`, with `H_m` the
`m`th eigenvalue of the matrix 29.15.2 (`0 ≤ m ≤ n`). Admitted. -/
@[dlmf 29.15.E42]
theorem Real.lameBk_eq_lamePolyH_scdE (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameBk ((2 * n + 3 : ℕ) : ℝ) (2 * m + 2) k =
      (lamePolyH .scdE n m k +
        ((2 * n + 3 : ℕ) : ℝ) * (((2 * n + 3 : ℕ) : ℝ) + 1) * k ^ 2) / 2 := by
  sorry

/-! ### The matrix eigenvalues (29.15.3) -/

/-- 29.15.3: the eigenvalues of the tridiagonal matrix 29.15.2 (for any of the eight types)
are real and simple, `H₀ < H₁ < ⋯ < Hₙ`: the characteristic polynomial has `n + 1` distinct
real roots, and `lamePolyH` lists them increasingly. Admitted. -/
@[dlmf 29.15.E3]
theorem lamePolyH_strictMono (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) (n : ℕ) :
    (lameMatrix t.recurrence (t.order n) k n).charpoly.roots.card = n + 1 ∧
      (lameMatrix t.recurrence (t.order n) k n).charpoly.roots.Nodup ∧
      ∀ m < n, lamePolyH t n m k < lamePolyH t n (m + 1) k := by
  sorry

/-! ### Polynomial form, periods and parities (Table 29.12.1) -/

/-- Table 29.12.1, polynomial form: each Lamé polynomial of type `t` is
`sn^a cn^b dn^c P(sn²)` with `P` a polynomial of degree `n`, where `sn`, `cn`, `dn` occur as
indicated by the type (`cn`, `dn` through `t.prefactor`, and a factor `sn` exactly for
`sE, scE, sdE, scdE`); `m ≤ n`. In particular (§29.12(i)) it is a doubly-periodic meromorphic
function of `z`. Admitted. -/
@[dlmf 29.12.T1, dlmf 29.12.i]
theorem lamePolyEk_polynomial_form (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], P.natDegree = n ∧ ∀ z : ℂ,
      lamePolyEk t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSnk z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSnk z k ^ 2) := by
  sorry

/-- Table 29.12.1, periods: the real period of the Lamé polynomial is `2K` for
`uE, dE, scE` and `4K` otherwise (`w(z + rK) = w(z)` with `r = 2` resp. `4`), and its
imaginary period is `2iK'` for `uE, sE` and `4iK'` otherwise. Admitted. -/
@[dlmf 29.12.T1]
theorem lamePolyEk_periods (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) (n m : ℕ)
    (z : ℂ) :
    lamePolyEk t n m (z + (if t = .uE ∨ t = .dE ∨ t = .scE then 2 else 4) *
        Real.compEllIntKm (k ^ 2)) k = lamePolyEk t n m z k ∧
      lamePolyEk t n m (z + (if t = .uE ∨ t = .sE then 2 else 4) * I *
        Real.compEllIntKm (1 - k ^ 2)) k = lamePolyEk t n m z k := by
  sorry

/-- Table 29.12.1, parities: `w(-z) = ±w(z)` with sign `-` exactly when the type has a factor
`sn`; `w(K - z) = ±w(K + z)` with `-` exactly for a factor `cn`; and
`w(K + iK' - z) = ±w(K + iK' + z)` with `-` exactly for a factor `dn`. Admitted. -/
@[dlmf 29.12.T1]
theorem lamePolyEk_parities (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) (n m : ℕ)
    (z : ℂ) :
    lamePolyEk t n m (-z) k =
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then -1 else 1) * lamePolyEk t n m z k ∧
      lamePolyEk t n m (Real.compEllIntKm (k ^ 2) - z) k =
        (if t = .cE ∨ t = .scE ∨ t = .cdE ∨ t = .scdE then -1 else 1) *
          lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + z) k ∧
      lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + I * Real.compEllIntKm (1 - k ^ 2) - z) k =
        (if t = .dE ∨ t = .sdE ∨ t = .cdE ∨ t = .scdE then -1 else 1) *
          lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + I * Real.compEllIntKm (1 - k ^ 2) + z) k
      := by
  sorry

/-- §29.12(i): the Lamé polynomial `t^m` (`m ≤ n`) has exactly `m` zeros in `(0, K)` and
exactly `n - m` zeros on the open segment from `K` to `K + iK'`. Admitted. -/
@[dlmf 29.12.i]
theorem lamePolyEk_zeros (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) {n m : ℕ}
    (hm : m ≤ n) :
    {x : ℝ | x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2)) ∧ lamePolyEk t n m x k = 0}.ncard = m ∧
      {y : ℝ | y ∈ Ioo 0 (Real.compEllIntKm (1 - k ^ 2)) ∧
        lamePolyEk t n m (Real.compEllIntKm (k ^ 2) + I * y) k = 0}.ncard = n - m := by
  sorry

/-! ### Algebraic form and zeros (§§29.12(ii), 29.12(iii)) -/

/-- 29.12.9 and 29.12.10: with `ξ = sn²(z, k)` the Lamé polynomial is
`ξ^ρ (ξ - 1)^σ (ξ - k⁻²)^τ P(ξ)` (up to the choice of branches, i.e. up to the constant
factor `(-1)^σ (-k⁻²)^τ` relating `(ξ - 1)^σ (ξ - k⁻²)^τ` to `cn^{2σ} dn^{2τ}`), where `P`
has degree `n` and simple zeros, `m` of them in `(0, 1)` and `n - m` in `(1, k⁻²)`; it
satisfies the algebraic form 29.2.2 of Lamé's equation. Here the polynomial form is stated as
in `lamePolyEk_polynomial_form`, and the zero locations are added. Admitted. -/
@[dlmf 29.12.E9, dlmf 29.12.E10]
theorem lamePolyEk_algebraic_form (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], P.natDegree = n ∧ P.roots.Nodup ∧ P.roots.card = n ∧
      (P.roots.filter (· ∈ Ioo (0 : ℝ) 1)).card = m ∧
      (P.roots.filter (· ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹)).card = n - m ∧
      ∀ z : ℂ, lamePolyEk t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSnk z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSnk z k ^ 2) := by
  sorry

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

end DLMF.Lame
