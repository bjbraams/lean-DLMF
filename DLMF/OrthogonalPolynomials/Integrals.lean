/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.Integrals.AngularRepresentations
public import DLMF.OrthogonalPolynomials.Integrals.GegenbauerAndLegendre
public import DLMF.OrthogonalPolynomials.Integrals.LaguerreAndHermite
public import DLMF.OrthogonalPolynomials.Integrals.ConvolutionsAndFourier
public import DLMF.OrthogonalPolynomials.Integrals.BesselAndLaguerreTransforms
public import DLMF.OrthogonalPolynomials.Integrals.DoubleLaplaceAndGaussian

/-!
# Classical orthogonality, Rodrigues formulas, and integral identities

The product Laguerre Laplace transform uses finite changes of scale and local
orthogonality; Mathlib’s polynomial induction and Gamma moments justify complex
Laplace rates. The two double Laplace integrals use the proved Gegenbauer angular
representation, finite Jacobi binomial coefficients, and Mathlib’s square-substitution,
Gaussian-moment and Beta-integrability APIs, retaining singular integrable endpoints.

Integral identities from NIST DLMF Chapter 18. The Hermite and weighted Jacobi antiderivatives
are proved by the fundamental theorem of calculus. The Laguerre squared norm
is obtained from the already proved monomial moments;
other declarations below still include admitted results.
Probabilists’ Hermite orthogonality and polynomial Gaussian integrability use
the corresponding results of the Tau Ceti contributors. The two Hermite Fourier
eigenfunction identities adapt their normalized Hermite Fourier theorem to the
positive phase and scales used in DLMF.
The Hermite cosine and sine transforms 18.17.23 and 18.17.27 integrate by parts
against `He_n(x) e^{-x²/2}`; they use the Tau Ceti contributors' Gaussian
integrability `integrable_aeval_mul_gaussian` and Hermite parity `hermite_aeval_neg`.
The product cosine and sine transforms use finite Hermite linearization followed
by the single-polynomial transforms. The Gaussian convolution transfers derivatives
by integration by parts and evaluates its base case with Hermite addition.
The Laguerre fractional integrals reuse the regularized Kummer parameter integral
and the Laguerre addition and moment formulas. Gamma normalization uses Mathlib's
Gamma/Pochhammer identity; the tail substitution uses its measure-preserving translation API.
The Jacobi fractional integral reuses the regularized Gauss fractional integral.
Both Rodrigues formulas iterate the proved weighted derivative identities, with
Mathlib's iterated-derivative and real-scalar APIs handling the real restrictions.
Jacobi norms reduce by weighted integration by parts to shifted parameters and
terminate at the Beta integral, using Mathlib's endpoint-continuity and FTC APIs.
Gegenbauer orthogonality reuses symmetric Jacobi orthogonality and these norms;
Mathlib's Gamma duplication formula fixes its normalization, including degree zero.
Legendre norms follow from the three-term recurrence and proved Jacobi orthogonality.
The unweighted Laguerre convolution uses Mathlib's interval integration by parts
and the project's Laguerre derivative recurrence, and retains arbitrary real endpoints.
The weighted Laguerre convolution expands the normalized polynomials into finite
Gamma-normalized sums and scales Mathlib's Beta integral. Its Vandermonde step
uses an additive functional on Mathlib polynomials and their binomial coefficients.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
Gegenbauer's product formula 18.17.5 is proved by induction on the degree for all `λ > 0` at
once: one integration by parts in the angle (Mathlib's FTC API) lowers `cos φ` times the integrand
to the derivative at parameter `λ + 1`, and the three-term recurrence together with the identity
`(1 - x²) C_{n}^{λ+1}` (DLMF 18.9.8) closes the induction.
The Legendre–Bessel integral 18.17.21 integrates the sine series termwise against `P_n(1 - 2x²)`,
evaluates the moments by the substitution `s = 1 - 2x²` and the Jacobi moments, and matches the
result with the product series of `J_{n+1/2}²` (DLMF 10.8.3, `besselJ_mul_besselJ`).
The Dirichlet–Mehler integrals 18.10.1–18.10.2 substitute `ψ = 2 arcsin(sin(θ/2) √t)` (Mathlib's
change-of-variables formula `integral_image_eq_integral_abs_deriv_smul`), write `cos(2(n+λ)x)/cos x`
as a Gauss function (DLMF 15.4.14), and close with the fractional integral 15.6.8 and Euler's
transformation 15.8.1, which turns `𝐅(n+λ+1/2, 1/2-n-λ; λ+1/2; sin²(θ/2))` into the Gegenbauer
polynomial.
-/
