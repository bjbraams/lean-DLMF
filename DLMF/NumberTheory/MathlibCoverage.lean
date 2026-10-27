/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import DLMF.NumberTheory.Functions
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.NumberTheory.CarmichaelNumber
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Convolution
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# DLMF Chapter 27 results already in Mathlib

The `dlmf_upstream` commands below are checked pointers to Mathlib declarations for
DLMF §§27.2–27.16, deliberately not duplicate local theorems. Mathlib's arithmetic functions are
`ArithmeticFunction R` (with `f 0 = 0`), its `LSeries f s = ∑' n, f n / n ^ s` is DLMF 27.4.4
with the `n = 0` term dropped, and its Dirichlet characters are `DirichletCharacter R n`,
monoid homomorphisms `ZMod n →* R` extended by zero. Mathlib's `ModularForm.discriminant` is
`η²⁴`, without DLMF's factor `(2π)¹²` (27.14.16).
-/

/- §27.2: Euclid's theorem, Euler–Fermat. -/
dlmf_upstream 27.2.i Nat.exists_infinite_primes
  "exact: there are infinitely many primes"
dlmf_upstream 27.2.i Nat.factorization_prod_pow_eq_self
  "exact: n = ∏ p^{a_p} (27.2.1), as a Finsupp product"
dlmf_upstream 27.2.E8 Nat.ModEq.pow_totient
  "exact: Euler–Fermat a^φ(n) ≡ 1 (mod n) for (a, n) = 1"
dlmf_upstream 27.2.E9 ArithmeticFunction.sigma_zero_apply
  "exact: d(n) = σ₀(n) is the number of divisors"
dlmf_upstream 27.2.E10 ArithmeticFunction.sigma_apply
  "partial: σ_k(n) = ∑_{d∣n} d^k for natural k"
dlmf_upstream 27.2.E14 ArithmeticFunction.vonMangoldt_apply
  "exact: Λ(n) = log p for n = p^a, else 0"

/- §27.3: multiplicative properties. -/
dlmf_upstream 27.3.E1 ArithmeticFunction.IsMultiplicative
  "exact: f(mn) = f(m)f(n) for (m, n) = 1, f(1) = 1"
dlmf_upstream 27.3.E3 Nat.totient_eq_mul_prod_factors
  "exact: φ(n) = n ∏_{p∣n} (1 - 1/p), over ℚ"
dlmf_upstream 27.3.E5 Nat.card_divisors
  "exact: d(n) = ∏ (a_p + 1)"
dlmf_upstream 27.3.E8 Nat.totient_gcd_mul_totient_mul
  "exact: φ(m)φ(n) = φ(mn)φ((m,n))/(m,n) in the form φ((m,n))φ(mn) = φ(m)φ(n)(m,n)"
dlmf_upstream 27.3.E9 ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
  "partial: a multiplicative function is determined by its values at prime powers"

/- §27.4: Dirichlet series and Euler products. -/
dlmf_upstream 27.4.E4 LSeries
  "exact: F(s) = ∑ f(n) n^{-s} (n = 0 term dropped)"
dlmf_upstream 27.4.E1 EulerProduct.eulerProduct_hasProd
  "exact: Euler product for a multiplicative f with ∑ |f(n)| < ∞"
dlmf_upstream 27.4.E2 EulerProduct.eulerProduct_completely_multiplicative_hasProd
  "exact: Euler product for a completely multiplicative f"
dlmf_upstream 27.4.E3 riemannZeta_eulerProduct_hasProd
  "exact: ζ(s) = ∏ (1 - p^{-s})⁻¹, ℜs > 1"
dlmf_upstream 27.4.E5 ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius
  "exact: ζ(s) ∑ μ(n) n^{-s} = 1, ℜs > 1"
dlmf_upstream 27.4.E12 ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
  "exact: ∑ Λ(n) n^{-s} = -ζ'(s)/ζ(s), ℜs > 1"

/- §27.5: inversion formulas. -/
dlmf_upstream 27.5.E1 ArithmeticFunction.mul_apply
  "exact: Dirichlet product (f * g)(n) = ∑_{d∣n} f(d) g(n/d)"
dlmf_upstream 27.5.E2 ArithmeticFunction.moebius_mul_coe_zeta
  "exact: μ * ζ = 1, i.e. ∑_{d∣n} μ(d) = ⌊1/n⌋"
dlmf_upstream 27.5.E3 ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
  "exact: Möbius inversion"
dlmf_upstream 27.5.E4 Nat.sum_totient
  "exact: ∑_{d∣n} φ(d) = n"
dlmf_upstream 27.5.E5 ArithmeticFunction.vonMangoldt_sum
  "exact: ∑_{d∣n} Λ(d) = ln n"
dlmf_upstream 27.5.E8 ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero
  "exact: multiplicative Möbius inversion"

/- §27.6: divisor sums. -/
dlmf_upstream 27.6.E2 ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
  "partial: ∑_{d∣n} μ(d) f(d) = ∏_{p∣n} (1 - f(p)) for squarefree n"

/- §27.7: Lambert series. -/
dlmf_upstream 27.7.E5 tsum_pow_div_one_sub_eq_tsum_sigma
  "partial: ∑ n^α xⁿ/(1 - xⁿ) = ∑ σ_α(n) xⁿ for natural α"

/- §27.8: Dirichlet characters. -/
dlmf_upstream 27.8.E1 DirichletCharacter
  "exact: χ as a monoid hom (ZMod k)ˣ-supported, extended by 0"
dlmf_upstream 27.8.E6 DirichletCharacter.sum_char_inv_mul_char_eq
  "exact: orthogonality ∑_χ χ(m) conj χ(n) = φ(k) or 0"
dlmf_upstream 27.8.ii DirichletCharacter.conductor
  "exact: conductor; primitive characters are DirichletCharacter.IsPrimitive"

/- §27.9: quadratic characters. -/
dlmf_upstream 27.9.E1 legendreSym.at_neg_one
  "exact: (-1|p) = (-1)^{(p-1)/2} (as χ₄)"
dlmf_upstream 27.9.E2 legendreSym.at_two
  "exact: (2|p) = (-1)^{(p²-1)/8} (as χ₈)"
dlmf_upstream 27.9.E3 legendreSym.quadratic_reciprocity
  "exact: quadratic reciprocity for odd primes p ≠ q"
dlmf_upstream 27.9.E3 jacobiSym.quadratic_reciprocity
  "exact: Jacobi reciprocity for odd coprime m, n"

/- §27.10: Gauss sums. -/
dlmf_upstream 27.10.E9 gaussSum
  "exact: G(χ, ψ) for an additive character ψ; DLMF's G(n, χ) with ψ = e^{2πin·/k}"
dlmf_upstream 27.10.E11 gaussSum_mulShift_of_isPrimitive
  "partial: separability of Gauss sums of primitive characters"

/- §27.11–27.12: primes. -/
dlmf_upstream 27.11 Nat.infinite_setOf_prime_and_eq_mod
  "exact: Dirichlet's theorem on primes in arithmetic progressions"
dlmf_upstream 27.12 Nat.IsCarmichael
  "exact: Carmichael numbers (Korselt's criterion)"
dlmf_upstream 27.12 Nat.bertrand
  "partial: Bertrand's postulate (a Chebyshev-type estimate, not in DLMF)"

/- §27.13: Lagrange and Fermat. -/
dlmf_upstream 27.13.iii Nat.sum_four_squares
  "exact: Lagrange's four-square theorem (g(2) ≤ 4)"
dlmf_upstream 27.13.E4 jacobiTheta_eq_tsum_nat
  "exact: ϑ(e^{πiτ}) = 1 + 2∑ e^{πin²τ} (Mathlib's jacobiTheta)"

/- §27.14: partitions, eta and Δ. -/
dlmf_upstream 27.14.E2 hasProd_eulerFunction
  "exact: f(x) = ∏ (1 - xⁿ), |x| < 1 (Mathlib's eulerFunction)"
dlmf_upstream 27.14.E4 hasSum_eulerFunction_pentagonal
  "exact: pentagonal number theorem as a sum over k ∈ ℤ"
dlmf_upstream 27.14.E4 PowerSeries.WithPiTopology.hasProd_one_sub_X_pow
  "exact: formal pentagonal number theorem"
dlmf_upstream 27.14.E5 pentagonal
  "exact: ω(k) = k(3k - 1)/2, k ∈ ℤ"
dlmf_upstream 27.14.E12 ModularForm.eta
  "exact: η(τ) = e^{πiτ/12} ∏ (1 - e^{2πinτ})"
dlmf_upstream 27.14.E16 ModularForm.discriminant
  "partial: η²⁴, without DLMF's factor (2π)¹²"
dlmf_upstream 27.14.E17 CuspForm.discriminant
  "exact: Δ is a weight-12 cusp form for SL(2, ℤ)"

/- §27.15–27.16 (applications, not acquired as statements). -/
dlmf_upstream 27.15 Nat.chineseRemainder
  "exact: the Chinese remainder theorem"
dlmf_upstream 27.15 ZMod.chineseRemainder
  "exact: ZMod (m n) ≃+* ZMod m × ZMod n for coprime m, n"
dlmf_upstream 27.16 Nat.ModEq.pow_totient
  "exact: Euler–Fermat, the basis of the RSA scheme"
