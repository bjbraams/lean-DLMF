# DLMF errata and source corrections

This register collects, project-wide, every place where a formula of the NIST Digital Library
of Mathematical Functions (DLMF) could not be formalized exactly as printed, together with the
earlier defects in this project's own transcriptions that were found and fixed. It is meant for
readers who compare a Lean statement with the printed DLMF formula and find that the two
differ, and as a list of candidate errata reports for the DLMF editors.

Entries are grouped in three categories.

- (a) Genuine DLMF errata: the printed formula is false, or lacks a condition it needs, under
  DLMF's own definitions and conventions.
- (b) Project transcription defects that were fixed: DLMF is right, but an earlier Lean statement
  or definition in this project was wrong (wrong bracket, sign, binder, domain or set reading).
- (c) Formalization notes: DLMF is right in its own reading, but the Lean statement needs an
  extra hypothesis or a separate case because of Lean's conventions (`x / 0 = 0`, `Γ(0) = 0`,
  totalized `ζ(1)`, unordered sums), a branch choice, a removable point, or an implicit
  convention made explicit. DLMF's own published errata that the formalization follows are also
  listed here.

Each entry gives the DLMF ID (linked), what is printed against what is correct (plain words or
plain math), the evidence, the Lean declaration(s), the status (proved, admitted, definition, or
an upstream pointer) and the date found. "Admitted" means the corrected statement is in Lean
with a `sorry` proof. For entries found before 2026-10-25 the evidence is summarized from the
cited section of [REVIEW.md](REVIEW.md) or a chapter ledger and was not re-verified for this
register. The Chapter 19 entries were checked the same way (section "Chapter 19 (elliptic
integrals)" below). The Chapter 20–23 entries were found by the acquisition agents and confirmed by an
independent numerical check (REVIEW.md, section "Chapters 20–23 acquisition (2026-10-25)",
subsection "DLMF errata and source corrections"; ledgers DLMF20–DLMF23Acquisition.md).

Counts (2026-10-25): 62 entries in (a), 19 in (b), 32 in (c). Some entries group closely related
equation numbers.

## (a) Genuine DLMF errata

### Chapter 4 (elementary functions)

- [4.7.E13](https://dlmf.nist.gov/4.7.E13) (also 4.7.ii, paragraph 2)
  - Printed: the general solution of the linear first-order ODE is exp(F) + C. Correct:
    C exp(F), a multiplicative constant.
  - Evidence: proved in Lean.
  - Lean: `DLMF.Elementary.linear_ode_solution` (DLMF/Elementary/LogExpAnalysis.lean), proved.
  - Found: 2026-10-24 (DLMF4Acquisition.md, "Domains, conventions and source corrections").
- [4.8.E2](https://dlmf.nist.gov/4.8.E2)
  - Printed range −π ≤ ph z1 + ph z2 ≤ π; the identity fails at the endpoint −π (z1 = z2 = −i
    gives iπ against −iπ). Correct: −π < ph z1 + ph z2 ≤ π.
  - Lean: upstream pointer to Mathlib `Complex.log_mul` (DLMF/Elementary/MathlibCoverage.lean).
  - Found: 2026-10-21 (REVIEW.md, "Upstream pointers (2026-10-21)").
- [4.8.E9](https://dlmf.nist.gov/4.8.E9)
  - Printed: ln(exp z) = z for −π ≤ Im z ≤ π; fails at Im z = −π (z = −iπ gives iπ). Correct:
    −π < Im z ≤ π.
  - Lean: upstream pointer to Mathlib `Complex.log_exp`.
  - Found: 2026-10-21 (as 4.8.E2).
- [4.20.E13](https://dlmf.nist.gov/4.20.E13), [4.20.E14](https://dlmf.nist.gov/4.20.E14)
  (borderline (a)/(c): wording of "general solution")
  - Printed general solutions omit the constant solutions ±1/a (E13) and ±i/a (E14).
  - Lean: `trig_energy_ode_general`, `trig_riccati_ode_general` (DLMF/Elementary/Trigonometric.lean),
    proved.
  - Found: 2026-10-24 (DLMF4Acquisition.md, 4.20 rows).
- [4.26.E9](https://dlmf.nist.gov/4.26.E9), [4.26.E10](https://dlmf.nist.gov/4.26.E10)
  - Printed: integer-frequency orthogonality of sines (cosines) under m ≠ n only; false at
    m = −n. Correct: also m ≠ −n.
  - Lean: `integral_sin_integer_orthogonal`, `integral_cos_integer_orthogonal`
    (DLMF/Elementary/Trigonometric.lean), proved.
  - Found: 2026-10-24 (DLMF4Acquisition.md, 4.26 rows).
- [4.34.E12](https://dlmf.nist.gov/4.34.E12), [4.34.E13](https://dlmf.nist.gov/4.34.E13),
  [4.34.E14](https://dlmf.nist.gov/4.34.E14) (borderline (a)/(c), as 4.20.E13–E14)
  - Printed general solutions omit the constant equilibria (E14: ±1/a).
  - Lean: `hyperbolic_squared_ode_plus`, `hyperbolic_squared_ode_minus`, `hyperbolic_riccati_ode`
    (DLMF/Elementary/Hyperbolic.lean), admitted.
  - Found: 2026-10-24 (DLMF4Acquisition.md, 4.34 rows).
- [4.37.E11](https://dlmf.nist.gov/4.37.E11)
  - Printed sign pairing arccosh(−z) = arccosh(z) + sgn(Im z)πi. Correct: arccosh(−z) =
    arccosh(z) − sgn(Im z)πi.
  - Evidence: 4.37.E20 gives arccosh(i) = log(1+√2) + πi/2 and arccosh(−i) = log(1+√2) − πi/2,
    contradicting the printed sign; proved in Lean.
  - Lean: `DLMF.Elementary.arccosh_neg` (DLMF/Elementary/Hyperbolic.lean), proved.
  - Found: 2026-10-24 (DLMF4Acquisition.md, 4.37.E11 row).
- [4.37.E14](https://dlmf.nist.gov/4.37.E14)
  - Reciprocal of 4.37.E11: correct arcsech(−z) = arcsech(z) + sgn(Im z)πi; the printed pairing is
    reversed.
  - Lean: `DLMF.Elementary.arcsech_neg` (DLMF/Elementary/Hyperbolic.lean), proved.
  - Found: 2026-10-24.

### Chapter 8 (incomplete Gamma and related functions)

- [8.10.E11](https://dlmf.nist.gov/8.10.E11)
  - Printed: "equalities only for a = 1"; also needs x > 0 (at x = 0 both bounds are 0 for all a).
  - Lean: `normIncGammaP_exponential_bounds`, `normIncGammaP_exponential_bounds_strict`
    (DLMF/IncompleteGamma/BoundsFractions.lean), proved.
  - Found: 2026-10-19 (DLMF678Acquisition.md, "Source qualifications and a proved counterexample").
- [8.17](https://dlmf.nist.gov/8.17) (claim after 8.17.23)
  - Printed: the convergents of the incomplete-Beta continued fraction alternate as upper and
    lower bounds. False.
  - Evidence: a = 1, b = 1/2, x = 1/2: I = 1 − √2/2, while the two-level convergent √2/5 and the
    three-level convergent 23√2/112 are both below I; proved in Lean.
  - Lean: `incBeta_cf_upper_bound_counterexample`, `incBeta_cf_third_bound_counterexample` and
    value lemmas (DLMF/IncompleteGamma/Beta.lean), proved.
  - Found: 2026-10-19 (DLMF678Acquisition.md, same section).
- [8.19.E25](https://dlmf.nist.gov/8.19.E25)
  - Printed conditions are insufficient: Re b > 0 is needed for convergence at the zero endpoint.
  - Lean: `genExpIntE_mellin_laplace` (DLMF/IncompleteGamma/ExponentialIntegral.lean), proved.
  - Found: 2026-10-19 (DLMF678Acquisition.md, same section).

### Chapter 9 (Airy functions)

- [9.10.E7](https://dlmf.nist.gov/9.10.E7)
  - Printed leading term +π^(−1/2)(−x)^(−3/4) sin(...) for the integral of Bi; correct sign −.
  - Evidence: x = −10: integral −0.01504 against printed +0.01240; the derivative of the printed
    term is −Bi(x); proved in Lean.
  - Lean: `airyBi_negative_integral_asymptotic` (DLMF/Airy/Integrals.lean), proved.
  - Found: 2026-10-21 (REVIEW.md, "Round 7 statement corrections (2026-10-21, user-approved)").
- [9.13.E36](https://dlmf.nist.gov/9.13.E36)
  - Printed B3 − B1 = 2πi A2 for all integer p. Correct: 2πi(A2 + B0(z, p)); the printed form holds
    only for p ≤ 0.
  - Evidence: failure at p = 1 proved in Lean (`reidAiry_connection_36_ne_one`).
  - Lean: `reidAiry_connection_36`, `reidAiry_connection_36_of_nonpos`,
    `reidAiry_connection_36_ne_one` (DLMF/Airy/GeneralizedContours.lean), proved.
  - Found: 2026-10-20 (REVIEW.md, "Shared-helper round (priority 2, 2026-10-20)").

### Chapter 11 (Struve and related functions)

- [11.4.E15](https://dlmf.nist.gov/11.4.E15)
  - Printed bound (2/3) exp(|z|²/(4d) − 1). Correct: (2/3)(exp(|z|²/(4d)) − 1).
  - Evidence: ν = 1000, z = iy with y²/4 = |ν + 3/2| gives |θ| > 0.93.
  - Lean: `struveH_relative_bound` (DLMF/Struve/Properties.lean), admitted.
  - Found: 2026-10-20 (REVIEW.md, "Project-wide admission triage and statement corrections").
- [11.7.E12](https://dlmf.nist.gov/11.7.E12)
  - Printed condition Re(μ + ν) > 0 only; also needs Re μ > −3/2 and Re ν > −3/2 (μ = 3, ν = −2
    diverges).
  - Lean: `struveH_integral_product` (DLMF/Struve/Representations.lean), admitted.
  - Found: 2026-10-20 (as 11.4.E15).
- [11.11.E6](https://dlmf.nist.gov/11.11.E6)
  - Printed error O(ν^(−2)) for complex ν. Correct: e^(π|Im ν|) ν^(−2).
  - Evidence: at z = 1, |error|·|ν|² ≈ 1.05·10¹³ at ν = 1/2 + 10i.
  - Lean: `weberE_large_order` (DLMF/Struve/Asymptotics.lean), proved.
  - Found: 2026-10-21 (REVIEW.md, "Round 6 (2026-10-21)").
- [11.11.E18](https://dlmf.nist.gov/11.11.E18), [11.11.E19](https://dlmf.nist.gov/11.11.E19)
  - DLMF's 2021 clarification widens the condition to |ph ν| ≤ π − δ; correct only for real
    ν → +∞.
  - Evidence: the ratio is 1 for real ν but ≈ 2.8·10⁶ at ph ν = 0.3 (matching sin(πν)A_ν(ν)).
  - Lean: `angerJ_turning_equiv`, `weberE_turning_equiv` (DLMF/Struve/Asymptotics.lean), proved.
  - Found: 2026-10-21 (as 11.11.E6).

### Chapter 12 (parabolic cylinder functions)

- [12.13.E6](https://dlmf.nist.gov/12.13.E6)
  - Fails at n = 0, z = 0: the right side is 1 but U(1/2, 0) = √(π/2).
  - Lean: `pcfU_half_zero_ne_one`, `dlmf_12_13_6_counterexample`
    (DLMF/ParabolicCylinder/SourceChecks.lean), proved.
  - Found: 2026-10-19 (DLMF111214Acquisition.md, "Formally verified source discrepancies").

### Chapter 13 (confluent hypergeometric functions)

- [13.9.E6](https://dlmf.nist.gov/13.9.E6)
  - The positive-zero count needs a ∉ −ℕ: a = −1, b = −3/2 gives M = 1 + 2x/3 with no positive
    zero, while the formula gives one.
  - Lean: `kummerM_posZeros_ceil_swap`, counterexample `kummerM_posZeros_ceil_swap_ne`
    (DLMF/Confluent/Zeros.lean), proved.
  - Found: 2026-10-21 (REVIEW.md, "Round 7 statement corrections").
- [13.11.E3](https://dlmf.nist.gov/13.11.E3) (borderline (a)/(c): branch)
  - With principal branches the printed Bessel expansion is false when ph z + ph(b − 2a) > π.
  - Evidence: a = 0.2 − 0.5i, b = 1.4 + 0.4i, z = −1.2 + 0.3i: right side 2.8336 − 3.3899i against
    1.18529 + 0.46781i.
  - Lean: `regularizedHGFun_eq_besselExpansion` (branch-free, all a, b, z),
    `regularizedHGFun_besselJ_series` (printed form with the phase condition)
    (DLMF/Confluent/Series.lean), proved.
  - Found: 2026-10-20 (REVIEW.md, "Blocker round (2026-10-20, late evening)").

### Chapter 14 (Legendre and related functions)

- [14.14.E1](https://dlmf.nist.gov/14.14.E1)
  - Printed limit (1/2)(x²−1)^(1/2) P^μ_ν/P^(μ−1)_ν. Correct: the minimal-solution ratio
    (1/2)(x²−1)^(1/2)(ν+μ)(ν−μ+1) P^(−μ)_ν/P^(1−μ)_ν.
  - Evidence: (ν, μ, x) = (0.3, 0.4, 1.5): fraction 0.345161187628545, printed 0.812720708269563.
  - Lean: `associatedP_continued_fraction` (DLMF/Legendre/Series.lean), proved.
  - Found: 2026-10-21 (REVIEW.md, "Round 7 (2026-10-21)").
- [14.16(ii)](https://dlmf.nist.gov/14.16#ii), Ferrers P zeros
  - The extra-zero case needs n ≥ m, not n > m (the case n = m is uncovered).
  - Evidence: (ν, μ) = (1/4, 3/4), (0.3, 0.3), (1.6, 1.6) each have one zero against the base count 0.
  - Lean: `ferrersPExtraZero`, `ferrersP_zero_count` (DLMF/Legendre/Zeros.lean), proved.
  - Found: 2026-10-22 (REVIEW.md, "Round 9 DLMF errata in §14.16 (2026-10-22, user-approved)").
- [14.16(ii)](https://dlmf.nist.gov/14.16#ii), Ferrers Q zeros
  - The parity rule holds only for μ ≥ 0 (ν = −0.369, μ = −0.206: Q > 0 on (−1, 1)).
  - Lean: `ferrersQ_zero_count_range` (DLMF/Legendre/Zeros.lean), proved.
  - Found: 2026-10-22 (same section).
- [14.16(iii)](https://dlmf.nist.gov/14.16#iii), zeros of P on (1, ∞)
  - Case (b) needs μ > 0 (ν = 0.184, μ = −0.088: P > 0 on (1, ∞)).
  - Lean: `associatedPOneZero`, `associatedP_zero_count` (DLMF/Legendre/Zeros.lean), proved.
  - Found: 2026-10-22 (same section).
- [14.23.E7](https://dlmf.nist.gov/14.23.E7)
  - Printed second factor e^(−3μπi/2). Correct: e^(μπi/2) (the two terms are then conjugate).
  - Lean: `conicalQHat_boundary` (DLMF/Legendre/Continuation.lean), proved.
  - Found: 2026-10-20 (REVIEW.md, "Shared-helper round").
- [14.27](https://dlmf.nist.gov/14.27), left-cut zero rule
  - Predicts one zero for degree 1, order −1/2; there is none.
  - Lean: `associatedP_one_neg_half`, `dlmf_14_27_no_boundary_zero`
    (DLMF/Legendre/SourceChecks.lean), proved.
  - Found: 2026-10-19 (DLMF111214Acquisition.md, "Formally verified source discrepancies").

### Chapters 16, 17 and 24

- [16.19.E5](https://dlmf.nist.gov/16.19.E5) (borderline (a)/(c))
  - The plus-sign transformation needs n ≥ 1; for n = 0 the sign is opposite.
  - Lean: `meijerG_log_derivative` (hypothesis 0 < n)
    (DLMF/GeneralizedHypergeometric/MeijerGRelations.lean), admitted.
  - Found: 2026-10-24 (DLMF16Acquisition.md, 16.19.E5 row).
- [17.2.E34](https://dlmf.nist.gov/17.2.E34)
  - Printed r > s omits s > 0; at s = 0 the limit is 1/(q;q)_t.
  - Lean: `qBinom_two_growing_indices`, `qBinom_two_index_limit`
    (DLMF/QHypergeometric/Calculus.lean), proved.
  - Found: 2026-10-24 (DLMF17Acquisition.md, 17.2.E34 row).
- [17.7.E19](https://dlmf.nist.gov/17.7.E19)
  - Printed argument has an extra q. Correct: a^(−1) q^(−M) (Gasper–Rahman 1.9.7).
  - Evidence: exact counterexample r = 0, q = 1/2, a = 2, M = 0: printed value 1/2, not 0.
  - Lean: `karlsson_printed_counter` (proved), `q_karlsson_minton_zero_corrected` (admitted)
    (DLMF/QHypergeometric/HigherSummations.lean).
  - Found: 2026-10-24 (DLMF17Acquisition.md, "Domains and source corrections").
- [17.7.E23](https://dlmf.nist.gov/17.7.E23)
  - Printed (p;p)_n and (ap^k/b; q)_(n+1). Correct: (p;p)_k and (ap^k/b; p)_(n+1).
  - Evidence: printed expression at p = 1/2, q = 1/3, a = 1/4, b = 1, n = 1 equals −1884/1771.
  - Lean: `bibasic_printed_counter` (proved), `bibasic_difference_corrected` (admitted)
    (DLMF/QHypergeometric/HigherSummations.lean).
  - Found: 2026-10-24 (same section).
- [17.8.E8](https://dlmf.nist.gov/17.8.E8)
  - Printed |cq²| < |b²| is broader than convergence; the sum identity needs |c/b²| < 1.
  - Lean: `bilateral_even_sum` (DLMF/QHypergeometric/BilateralSummations.lean), admitted.
  - Found: 2026-10-24 (DLMF17Acquisition.md, 17.8.E8 row).
- [17.14.E3](https://dlmf.nist.gov/17.14.E3)
  - The printed left side repeats that of 17.14.E2; correct (−q;q²)_n instead of (−q;q²)_(n+1).
  - Evidence: coefficient comparison with the displayed constant term.
  - Lean: `rogers_constantTerm_G_corrected` (DLMF/QHypergeometric/ConstantTerms.lean), admitted.
  - Found: 2026-10-24 (same section as 17.7.E19).
- [24.4.E7](https://dlmf.nist.gov/24.4.E7) (borderline (a)/(c): 0⁰ convention)
  - The printed sum from k = 1 fails at n = 0; Mathlib's form from k = 0 holds.
  - Lean: upstream pointer to `Polynomial.sum_range_pow_eq_bernoulli_sub`.
  - Found: 2026-10-21 (REVIEW.md, "Upstream pointers (2026-10-21)").

### Chapter 19 (elliptic integrals)

Found by the Chapter 19 acquisition agents and checked by an independent mpmath verifier on
2026-10-25 against the printed formulas (DLMF 1.2.8); see DLMF19Acquisition.md.

- [19.7.E2](https://dlmf.nist.gov/19.7.E2) (second and fourth formulas)
  - Printed: K(−ik′/k) = kK(k′), E(−ik′/k) = E(k′)/k, with no condition. The left sides depend on
    k² only, the right sides are odd in k. DLMF's condition Re k > 0 (its erratum for V1.2.0)
    stands above 19.7.3 only. Correct for Re k > 0.
  - Evidence: at k = −0.6, K(−ik′/k) = 1.19718 but kK(k′) = −1.19718; at k = −0.6 + 0.3i the two
    sides are 1.2490 − 0.3256i and its negative.
  - Lean: `compEllInt_imaginary_comodulus` (DLMF/EllipticIntegrals/Connection.lean), admitted.
  - Found: 2026-10-25.
- [19.20.E3](https://dlmf.nist.gov/19.20.E3), [19.20.E23](https://dlmf.nist.gov/19.20.E23)
  - Printed: R_F(x, a, y) = R_{−1/4}(3/4, 1/2; a², xy) and R_D(x, y, a) = R_{−3/4}(5/4, 1/2; a², xy),
    a = (x + y)/2, under the 19.16(i) constraints. They fail inside that domain. Correct for
    Re x > 0 and Re y > 0 (sufficient).
  - Evidence: at x = −1 + i, y = −1 + 2i the ratio of right to left side is +i (E3) and −i (E23);
    at x = −2 + 2i, y = 1.5 − 1.5i it is 0.945 + 0.328i and −0.541 + 0.841i; no failure at 85
    random points with Re x, Re y > 0.
  - Lean: `symEllIntRF_lemniscatic`, `symEllIntRD_lemniscatic` (real x, y > 0) and
    `symEllIntRF_lemniscatic_complex`, `symEllIntRD_lemniscatic_complex` (Re x, Re y > 0)
    (DLMF/EllipticIntegrals/SymmetricSpecialCases.lean), admitted. The acquisition first described
    the failure as a factor −i for all complex arguments; the verifier showed that the factor varies
    and that the formulas hold in the right half-planes, and the complex forms were added.
  - Found: 2026-10-25.
- §19.25(i) ([19.25.E5](https://dlmf.nist.gov/19.25.E5), [19.25.E7](https://dlmf.nist.gov/19.25.E7), [19.25.E9](https://dlmf.nist.gov/19.25.E9), [19.25.E14](https://dlmf.nist.gov/19.25.E14))
  - Printed for complex φ in the strip 0 ≤ Re φ ≤ π/2 (DLMF erratum V1.1.7) and complex k. With
    Legendre's integral along [0, φ] and principal branches they fail when φ and k² are both
    nonreal; they hold for real φ, and for complex φ with real k².
  - Evidence: φ = 1.2 − 0.5i, k² = 1.2 + 0.5i gives F = 1.0173 − 1.3254i (continuous branch) or
    1.0876 − 1.1700i (principal) against R_F = 2.1714 + 0.0724i.
  - Lean: `incEllIntFk_eq_symEllIntRF`, `incEllIntEk_eq_symEllIntRG` and neighbours
    (DLMF/EllipticIntegrals/SymmetricRelations.lean), stated for real φ ∈ (0, π/2], admitted.
  - Found: 2026-10-25.
- [19.25.E30](https://dlmf.nist.gov/19.25.E30), [19.25.E31](https://dlmf.nist.gov/19.25.E31)
  - Printed: am(u, k) = R_C(cs², ns²) "if cs² ≥ 0", and u = R_F(ps², qs², rs²). The right sides are
    unchanged under u ↦ 2K − u and even in u. Correct for 0 < u ≤ K.
  - Evidence: k² = 0.5, u = 2.4 > K = 1.85407: am = 1.96619 against R_C = 1.17540, and R_F = 1.30815
    against u; at u = −0.7 the sign is wrong.
  - Lean: `jacobiAmm_eq_symEllIntRC`, `eq_symEllIntRF_jacobi`, admitted.
  - Found: 2026-10-25.
- [19.25.E32](https://dlmf.nist.gov/19.25.E32), [19.25.E34](https://dlmf.nist.gov/19.25.E34)
  - Printed with conditions on x² that allow negative x for arccs, arccn and arccd. The right sides
    are even in x and give 2K minus the true value for x < 0. Correct for x ≥ 0. (19.25.E33 is odd in
    x and correct as printed.)
  - Evidence: k² = 0.5: arccs(−0.6) = 2.58693 against 1.12121; arccn(−0.6) = 2.71424 against
    0.99391; arccd(−0.6) = 2.51992 against 1.18823.
  - Lean: `jacobiArcps_eq_symEllIntRF`, `jacobiArcpq_eq_symEllIntRF`, admitted.
  - Found: 2026-10-25.
- [19.26.E9](https://dlmf.nist.gov/19.26.E9)
  - Printed: the R_J addition theorem with λ, x, y, z positive and no condition on p. Fails for some
    p < 0. Correct for p > 0 (sufficient; it still holds for −0.2004 < p < 0 at the test point).
  - Evidence: (x, y, z, λ) = (1, 2, 4, 0.5), p = −3: −0.132073 against −0.291838;
    p = −1 + 2i: 0.15979 − 0.27854i against 0.08663 − 0.46930i.
  - Lean: `symEllIntRJ_add_symEllIntRJ`, admitted.
  - Found: 2026-10-25.
- [19.26.E13](https://dlmf.nist.gov/19.26.E13)
  - Printed: R_C(α², α² − θ) + R_C(β², β² − θ) = R_C(σ², σ² − θ), σ = (αβ + θ)/(α + β), with
    0 < γ² − θ < γ² for γ = α, β, σ; the signs of α, β are not fixed. Correct for α, β > 0.
  - Evidence: α = −2, β = 3, θ = 1 (all printed conditions hold): 0.895880 against 0.202733.
  - Lean: `symEllIntRC_addition_theta`, admitted.
  - Found: 2026-10-25.
- [19.26.E27](https://dlmf.nist.gov/19.26.E27)
  - Printed: R_C(x², x² − θ) = 2R_C(s², s² − θ), s = x + √(x² − θ). The section's standing assumption
    x > 0 is needed (a formalization note for complex x: Re x > 0), and, newly found by the
    verifier, θ < x²: for θ > x² the left side is a Cauchy principal value (19.2.20) but the right
    side is not. Correct for Re x > 0 and x² − θ ∈ ℂ \ (−∞, 0].
  - Evidence: x = 1, θ = 2: 0.623225 against 0.623225 − 1.110721i (difference −πi/(2√θ));
    x = −2, θ = −3: 0.41207 against 1.40173; no failure at 3000 random complex points under the
    corrected hypotheses.
  - Lean: `symEllIntRC_duplication_theta` (DLMF/EllipticIntegrals/SymmetricAddition.lean),
    admitted. The hypothesis x² − θ ∈ ℂ \ (−∞, 0] was added on 2026-10-25: the acquired statement
    without it was false.
  - Found: 2026-10-25.
- [19.27.E8](https://dlmf.nist.gov/19.27.E8)
  - Printed: R_D = 3/√(xyz) − (6/(xy)) R_G(x, y, 0)(1 + O(z/g)). The error term is O(√(z/g)).
  - Evidence: x = y = 1, z = 10⁻⁸: the relative error is −1.273·10⁻⁴; divided by z/g it grows
    without bound, divided by √(z/g) it tends to −1.273 (≈ −4/π).
  - Lean: `symEllIntRD_asymp_small_z` (DLMF/EllipticIntegrals/SymmetricAsymptotics.lean), admitted.
  - Found: 2026-10-25.
- [19.27.E12](https://dlmf.nist.gov/19.27.E12)
  - Printed: R_J = (3/(2√(xyz)))(ln(4f/p) − 2)(1 + O(p/f)). The constant is right only for
    x = y = z, so the relative error is of order 1/ln(1/p), not p/f. Replaced by Carlson and
    Gustafson (1994), eq. (42): R_J = (3/(2√(xyz)))(ln(4f/p) − 2 + r) with
    −ln(f/H) ≤ r ≤ (3p/(2(f − p))) ln(f/p), H = 3/(x⁻¹ + y⁻¹ + z⁻¹).
  - Evidence: at (1, 2, 4) the regularized constant tends to −0.015051, not ln(4f) − 2 = 0.079442;
    the bounds on r hold at 500 random triples (checked numerically, not against the paper).
  - Lean: `symEllIntRJ_small_p_bounds`, admitted.
  - Found: 2026-10-25.
- [19.28.E9](https://dlmf.nist.gov/19.28.E9)
  - Printed with x, y > 0 only. Correct for x + y ≤ π/2 (sufficient; the identity is also
    invariant under x ↦ π − x).
  - Evidence: (x, y) = (1, 1): 2.92136 against 4.35740; (0.4, 1.4): 3.77223 against 5.19321.
  - Lean: `integral_symEllIntRF_sin_cos` (DLMF/EllipticIntegrals/SymmetricIntegralsOfIntegrals.lean),
    admitted.
  - Found: 2026-10-25.

### Chapter 20 (theta functions)

- [20.7.E34](https://dlmf.nist.gov/20.7.E34)
  - Printed: θ1(z|2τ)θ3(z|2τ)/θ1(z|τ+1/2) = θ2(z|2τ)θ4(z|2τ)/θ2(z|τ+1/2) =
    i^(−1/4) (θ2(0|2τ)θ4(0|2τ)/2)^(1/2). With the principal root this holds only up to sign.
    Correct for all τ: the root is e^(−iπ/8) η(τ)η(4τ)/η(2τ) (Dedekind η), which equals the
    principal value for τ = it.
  - Evidence: the printed form has the opposite sign at τ = −2.19 + 1.29i, 2.03 + 0.90i,
    −2.85 + 0.88i; the eta form agrees at 200 random (z, τ) (mpmath).
  - Lean: `jacobiTheta_reduction_iq_sq` (squared form, all τ), `jacobiTheta_reduction_iq_rectangular`
    (printed form, τ = it), `jacobiTheta_reduction_iq_eta` (full-domain form)
    (DLMF/Theta/Identities.lean), all admitted.
  - Found: 2026-10-25.
- [20.9.E2](https://dlmf.nist.gov/20.9.E2)
  - Printed: K(k) = (π/2)θ3²(0|τ), K′(k) = −iτK(k), with no condition on τ. With the principal
    K this fails for some complex τ. Correct region: K = (π/2)θ3² exactly on the translates F + 2n
    of F = {|Re τ| < 1, |τ − 1/2| > 1/2, |τ + 1/2| > 1/2}; K′ = −iτK on F.
  - Evidence: 58 of 308 random τ fail; no failure at 676 points of F; the region matches the
    validity set at all of 500 random τ (mpmath).
  - Lean: `compEllIntK_eq_jacobiThetaThreeNullTau` (τ = it, real K),
    `compEllIntKk_eq_jacobiThetaThreeNullTau_fundamental` (complex principal K on F and F + 2n)
    (DLMF/Theta/Relations.lean), admitted.
  - Found: 2026-10-25.
- [20.9.E3](https://dlmf.nist.gov/20.9.E3)
  - Printed without a branch condition. The left side is π-periodic and even in real z, the right
    side z θ1′(0)/θ1(z) is not; a condition keeping the arguments of R_F off its cut is needed.
  - Evidence: fails at real z = 1.6, 2, 2.5 (τ = 0.8i); holds at z = 1.4 + 0.5i, τ = 0.3 + 0.6i.
  - Corrected complex forms (checked with mpmath): for τ = it the identity holds for complex
    z ≠ 0 in the open period rectangle |Re z| < π/2, |Im z| < πt/2 (no failure at 3500 points;
    fails at 373 of 500 points with πt/2 < |Im z| < 0.9πt); for general τ it holds in a punctured
    neighbourhood of z = 0. For non-rectangular τ the period parallelogram π(s + rτ),
    |s|, |r| < 1/2, is not a valid region (e.g. fails at τ = 0.448 + 0.520i, s = −0.400,
    r = −0.318).
  - Lean: `carlsonRF_jacobiTheta` (τ = it, real 0 < |z| ≤ π/2), `carlsonRF_jacobiTheta_rect`
    and `carlsonRF_jacobiTheta_eventually` (DLMF/Theta/Relations.lean), all admitted, with the
    complex Chapter 19 `R_F` (`DLMF.EllipticIntegrals.symEllIntRF`).
  - Found: 2026-10-25.

### Chapter 21 (Riemann theta functions)

- [21.5.E4](https://dlmf.nist.gov/21.5.E4)
  - Printed for every symplectic Γ; false in general (it contradicts 21.5.E7). Correct on the theta
    group (diag(CDᵀ) and diag(ABᵀ) even), with a continuous branch of √det(CΩ + D) and an eighth
    root of unity.
  - Evidence: g = 2, Γ = [[I, B], [0, I]], B = [[1, 3], [3, −1]]: the ratio θ(z|Ω+B)/θ(z|Ω) depends
    on z.
  - Lean: `riemannTheta_modular` (DLMF/RiemannTheta/Modular.lean), admitted.
  - Found: 2026-10-25.
- [21.5.E8](https://dlmf.nist.gov/21.5.E8)
  - The printed principal square root of det(−iΩ) is wrong for g ≥ 3. Correct: the continuous
    branch with value 1 at Ω = iI (the product of the principal roots of the eigenvalues).
  - Evidence: g = 3, Ω = τI₃, τ = −1.1√3 + i: the ratio is minus the principal root.
  - Lean: `riemannTheta_inversion` (continuous branch, admitted), `riemannTheta_inversion_principal`
    (g ≤ 2, admitted), `riemannTheta_inversion_fin_one` (g = 1, proved)
    (DLMF/RiemannTheta/Modular.lean).
  - Found: 2026-10-25.
- [21.6.E4](https://dlmf.nist.gov/21.6.E4)
  - Printed: c_j, d_j are h-dimensional. Correct: g-dimensional (characteristics of a genus-g theta
    function).
  - Evidence: dimension count; independent numerical check of the identity.
  - Lean: `riemann_identity_char` (DLMF/RiemannTheta/Products.lean), admitted.
  - Found: 2026-10-25.

### Chapter 22 (Jacobian elliptic functions)

- [Table 22.5.1](https://dlmf.nist.gov/22.5.T1)
  - Printed derivative of dc at K + iK′ is k. Correct: −k (= k′² sc nc there).
  - Evidence: numerical differentiation.
  - Lean: `jacobiDck_specialDerivs` (DLMF/JacobiElliptic/SpecialValues.lean), admitted.
  - Found: 2026-10-25.
- [22.8.E23](https://dlmf.nist.gov/22.8.E23)
  - The printed determinant (columns sn cn, cn dn, cn, dn; z1 + z2 + z3 + z4 = 2K) is nonzero.
    Corrected forms: third column sn, or second column sn dn.
  - Evidence: determinant ≈ −0.107 + 0.033i at k = 0.6 (≈ −0.03 + 0.04i in the independent check).
  - Lean: `jacobi_det_sum_two_K`, `jacobi_det_sum_two_K'` (DLMF/JacobiElliptic/Addition.lean),
    admitted.
  - Found: 2026-10-25.
- [22.9.E23](https://dlmf.nist.gov/22.9.E23)
  - The printed right side repeats s_(2,3) d_(2,3). Correct last summand: s_(3,3) d_(3,3).
  - Evidence: k = 0.6, z = 0.37 + 0.21i: printed right side ≈ 4.208 − 0.036i, left side
    ≈ 0.552 + 0.183i.
  - Lean: `jacobi_cyclic_sdcc_three` (DLMF/JacobiElliptic/Cyclic.lean), admitted.
  - Found: 2026-10-25.

### Chapter 23 (Weierstrass elliptic and modular functions)

- [23.6.E17](https://dlmf.nist.gov/23.6.E17)
  - Printed K² = ω1²(e1 − e3), K′² = ω3²(e3 − e1) with the principal K(k); fails for some generator
    pairs. Correct: with the lattice K = (π/2)θ3²(0|τ) for every pair, or with the principal K
    when τ = iK′(k)/K(k).
  - Evidence: generators 2ω1 + 4ω3, 2ω3: K² − ω1²(e1 − e3) ≈ 11.0 − 13.7i.
  - Lean: `HalfPeriods.quarterK_sq_eq`, `HalfPeriods.compEllIntKk_sq_eq`
    (DLMF/Weierstrass/Relations.lean), admitted.
  - Found: 2026-10-25.
- [23.6.E29](https://dlmf.nist.gov/23.6.E29)
  - Printed last term −ζ(2iK′|𝕃3). Correct: +ζ(2iK′|𝕃3).
  - Evidence: the printed form is off by about −0.49i at k² = 0.3.
  - Lean: `weierstrassZeta_cs` (DLMF/Weierstrass/Relations.lean), admitted.
  - Found: 2026-10-25.
- [23.8.E1](https://dlmf.nist.gov/23.8.E1)
  - Printed condition Im(z/ω1) < 2 Im(ω3/ω1). Correct: |Im(z/ω1)| < 2 Im(ω3/ω1).
  - Evidence: outside the corrected region the series diverges (terms 10⁵, 10¹¹, 10²¹ at
    n = 10, 20, 40).
  - Lean: `HalfPeriods.weierstrassP_fourier` (DLMF/Weierstrass/Series.lean), admitted.
  - Found: 2026-10-25.
- [23.8.E2](https://dlmf.nist.gov/23.8.E2)
  - Same condition correction as 23.8.E1.
  - Lean: `HalfPeriods.weierstrassZeta_fourier` (DLMF/Weierstrass/Series.lean), admitted.
  - Found: 2026-10-25.
- [23.10.E14](https://dlmf.nist.gov/23.10.E14)
  - Printed product over ℓ ≠ j. Correct: over (j, ℓ) ≠ (0, 0).
  - Evidence: the printed index set gives relative error 0.71 at n = 2.
  - Lean: `HalfPeriods.nTupleConst` (DLMF/Weierstrass/Addition.lean), definition.
  - Found: 2026-10-25.
- [23.10.E15](https://dlmf.nist.gov/23.10.E15)
  - Printed π². Correct: π.
  - Evidence: with π the two sides agree exactly; with π² they differ by the factor π^(n²−1)
    (n = 2, 3, 4 on three lattices).
  - Lean: `HalfPeriods.nTupleConst_eq` (DLMF/Weierstrass/Addition.lean), admitted.
  - Found: 2026-10-25.
- [23.11.E2](https://dlmf.nist.gov/23.11.E2)
  - Valid only for the normalization 2ω1 = 1, and the printed condition −1 < Re(z + τ) < 1 does not
    give convergence. Corrected: |Re z| + |Re τ| < 1, |Im z| < Im τ.
  - Evidence: τ = −0.6 + i, z = 0.6 + 0.1i: integrand 4.5, 68, 7452, 4.4·10⁷ at s = 10, 20, 40, 80.
  - Lean: `HalfPeriods.weierstrassP_integral` (DLMF/Weierstrass/Integrals.lean), admitted.
  - Found: 2026-10-25.
- [23.11.E3](https://dlmf.nist.gov/23.11.E3)
  - The printed integral lacks the factor 4; normalization and domain as in 23.11.E2.
  - Evidence: the printed form is off by about 0.08 at τ = 0.3 + 0.9i, z = 0.3 + 0.2i.
  - Lean: `HalfPeriods.weierstrassZeta_integral` (DLMF/Weierstrass/Integrals.lean), admitted.
  - Found: 2026-10-25.
- [23.18.E4](https://dlmf.nist.gov/23.18.E4) (terminology)
  - The text calls J a modular form of level zero. J has a pole at q = 0 (23.17.5), so it is a
    modular function, not a modular form in the sense of 23.15(i).
  - Lean: `kleinJ_smul`, `isModularFunction_kleinJ` (DLMF/Weierstrass/ModularFunctions.lean),
    admitted.
  - Found: 2026-10-25.

## (b) Project transcription defects that were fixed

- [4.19.E3](https://dlmf.nist.gov/4.19.E3), [4.19.E4](https://dlmf.nist.gov/4.19.E4),
  [4.22.E5](https://dlmf.nist.gov/4.22.E5): mistaken tags (the tangent series was tagged E4, the
  cosecant series E5). The statements were unchanged. `Complex.hasSum_pi_mul_tan_bernoulli`,
  `Complex.hasSum_pi_mul_div_sin_bernoulli` (DLMFMathlib/NumberTheory/BernoulliTaylor.lean), proved.
  Found 2026-10-24 (DLMF4Acquisition.md).
- [4.38.E5](https://dlmf.nist.gov/4.38.E5)
  - The earlier Lean statement asserted unordered `HasSum` of z^(2n+1)/(2n+1) to arctanh z on the
    closed disk |z| ≤ 1, z ≠ ±1. On the unit circle this is false: at z = i the term norms are
    1/(2n+1), so the series is not absolutely summable, and in ℂ unordered summability means
    absolute summability. DLMF's statement (|z| ≤ 1, z ≠ ±1) is right with ordinary convergence.
  - Fix: unordered `HasSum` for |z| < 1, plus natural-order convergence of the partial sums on
    DLMF's full domain.
  - Lean: `DLMF.Elementary.hasSum_arctanh`, `DLMF.Elementary.tendsto_arctanh_series`
    (DLMF/Elementary/Hyperbolic.lean), both proved (from the boundary logarithm series
    `logBoundary_odd`).
  - Found and fixed: 2026-10-25.
- [4.38.E6](https://dlmf.nist.gov/4.38.E6)
  - Same defect for the series of 1/((2n+1)z^(2n+1)) for |z| ≥ 1, Im z ≠ 0 (z = i again gives
    term norms 1/(2n+1)).
  - Fix: unordered `HasSum` for |z| > 1, natural-order convergence for |z| ≥ 1, Im z ≠ 0, with the
    sum arctanh z ∓ iπ/2 for Im z ≷ 0.
  - Lean: `DLMF.Elementary.hasSum_arctanh_large`, `DLMF.Elementary.tendsto_arctanh_large_series`
    (DLMF/Elementary/Hyperbolic.lean), both proved.
  - Found and fixed: 2026-10-25.
- [4.38.E15](https://dlmf.nist.gov/4.38.E15): the earlier full-set statements dropped the correlation
  between square-root choices and inverse branches (u = v = i: the right side contains w = 0).
  Fixed with shared roots and paired sinh/cosh equations. `arcsinh_values_add`,
  `arcsinh_values_sub` and Lean counterexamples to the former form
  (DLMF/Elementary/Hyperbolic.lean), proved. Found and fixed 2026-10-24 (REVIEW.md, Chapters 4, 16
  and 17 rounds).
- [4.38.E18](https://dlmf.nist.gov/4.38.E18): the same defect (the former sets fail at u = i,
  v = 1). `arcsinh_arccosh_values_add`, `arcsinh_arccosh_values_sub`, counterexample
  `arcsinh_arccosh_values_unrestricted_counterexample`, proved. Found and fixed 2026-10-24.
- [5.9.E4](https://dlmf.nist.gov/5.9.E4): an integral binder extended over the following sum, so the
  statement asserted Γ(z) = 0; fixed by parenthesizing. `Gamma_incomplete_sum`
  (DLMF/Gamma/IntegralRepresentations.lean), proved. Found 2026-10-15 (REVIEW.md, "Gamma pass
  from Temme's Chapter 3").
- [8.9–8.17](https://dlmf.nist.gov/8.9) continued fractions (borderline (b)/(c)): draft finite
  continued fractions used nested totalized division; replaced by ratios of continuants. Found
  2026-10-19 (DLMF678Acquisition.md).
- [9.6.E11](https://dlmf.nist.gov/9.6.E11): wrong bracket (copied from the shape of 9.6.13), false
  at z = 1. `besselJ_third_eq_airy_complex` (DLMF/Airy/Relations.lean), proved. Found 2026-10-19,
  fixed 2026-10-20 (REVIEW.md, "Project-wide admission triage").
- [9.7.E17](https://dlmf.nist.gov/9.7.E17) (borderline (b)/(c): caused by 0⁻¹ = 0): the error
  multiplier was 0 on |arg z| = 2π/3, so the bound asserted ‖R_N‖ ≤ 0. `airyErrorMultiplier`,
  `airy_ai_complex_error` (proved), `airy_aiDeriv_complex_error` (admitted)
  (DLMF/Airy/Asymptotics.lean). Found 2026-10-21 (REVIEW.md, "Round 8").
- [9.8.E22](https://dlmf.nist.gov/9.8.E22), [9.8.E23](https://dlmf.nist.gov/9.8.E23): the phase
  remainders were empty at N = 0. `airyPhase_asymptotic`, `airyDerivPhase_asymptotic`
  (DLMF/Airy/ModulusPhase.lean), proved. Found 2026-10-19 (REVIEW.md, "Airy acquisition and first
  proof batch").
- [9.13.E23](https://dlmf.nist.gov/9.13.E23), [9.13.E24](https://dlmf.nist.gov/9.13.E24): odd m was
  allowed, but W_m is defined only for even m. `smirnovAiryU1_olver`, `smirnovAiryU2_olver`
  (DLMF/Airy/Generalized.lean), proved. Found 2026-10-20 (REVIEW.md, "Project-wide admission
  triage").
- [11.10.E24](https://dlmf.nist.gov/11.10.E24): wrong upper limit in `weberM1` (empty sum at n = 1).
  `weberM1`, `weberE_zero` (DLMF/Struve/AngerWeber.lean). Found 2026-10-20 (same section).
- [11.11.E3](https://dlmf.nist.gov/11.11.E3): an auto-bound implicit `k` in the G_k term made the
  statement quantify over it; fixed by bracketing the summand. `weberE_large_argument`
  (DLMF/Struve/Asymptotics.lean), proved. Found 2026-10-21 (REVIEW.md, "Round 6").
- [12.10.E11](https://dlmf.nist.gov/12.10.E11): coefficient 3/2(s+1) instead of DLMF's 3(s+1) in
  `pcfOlverPair`. `pcfOlverU_spec`, `pcfOlverUV_initial` (DLMF/ParabolicCylinder/Uniform.lean),
  proved. Found 2026-10-20 (REVIEW.md, "Project-wide admission triage").
- [13.9.E11–E14](https://dlmf.nist.gov/13.9.E11): the sector-count formulas were misread as
  positive-zero counts ((a, b) = (−1.3, −2.2) has no positive zeros). `kummerU_sectorZeros_gamma_pos`,
  `kummerU_sectorZeros_gamma_neg` (admitted), `kummerU_posZeros_ceil` (proved)
  (DLMF/Confluent/Zeros.lean). Found 2026-10-20.
- [13.9.E15](https://dlmf.nist.gov/13.9.E15): `kummerU_negZeros_none` was tagged 13.9.15 but concerns
  the negative axis, and was false for nonpositive integer a; the tag was removed and DLMF 13.9.15
  is proved as `kummerU_posZeros_none_of_le` (DLMF/Confluent/Zeros.lean). Found 2026-10-16 and
  2026-10-20 (REVIEW.md, "Admission pass after the Temme and Duverney work" and "Project-wide
  admission triage").
- [14.15.E21–E22](https://dlmf.nist.gov/14.15.E21): `LegendreYRelation` admitted two roots
  (α = 0.6, x = 0.9: y = 0.177237 and −0.116411); fixed by sign conditions. `legendreDegreeY_spec`
  (DLMF/Legendre/UniformCoordinates.lean), proved. Found 2026-10-22 (REVIEW.md, "Round 8").
- [14.20(viii)](https://dlmf.nist.gov/14.20#viii) (borderline (b)/(c)): `conicalEta_mapping`
  allowed α = 0, where η → π² rather than ∞. Now 0 < α. Proved
  (DLMF/Legendre/ConicalAsymptotics.lean). Found 2026-10-20.
- [16.11.E4](https://dlmf.nist.gov/16.11.E4) (coefficients e_(k,m); definition
  `genAsymptoticEkm`, tagged 16.11.E5): `∏ i, a i - b j` parsed as (∏ a_i) − b_j; DLMF means
  ∏(a_i − b_j), and likewise in the denominator. Fixed by parenthesizing. `genAsymptoticC_limit`,
  `genAsymptoticC_recurrence` (DLMF/GeneralizedHypergeometric/Asymptotics.lean), admitted. Found
  2026-10-25 (REVIEW.md, "Parallel proofs in Chapters 4, 16 and 17 (2026-10-24, fourth round)").

## (c) Formalization notes

### Totalization, removable points and nonvanishing hypotheses

- [4.18.E3](https://dlmf.nist.gov/4.18.E3), [4.32.E1](https://dlmf.nist.gov/4.32.E1),
  [4.40.E9](https://dlmf.nist.gov/4.40.E9): removable values (sin x/x and sinh x/x at 0; the value
  4 at a = 0) are stated explicitly. `cos_le_sinc_le_one` (proved), `cosh_le_sinhc_cube` and
  `integral_exp_div_cosh_sq` (admitted). DLMF4Acquisition.md.
- [4.24.E15](https://dlmf.nist.gov/4.24.E15): the finite quotient needs 1 ∓ uv ≠ 0.
  `arctan_general_add`, proved. DLMF4Acquisition.md.
- [5.9.E7](https://dlmf.nist.gov/5.9.E7): at x = 0 the totalized right side vanishes; restated as
  π/(2Γ(1−x)cos(πx/2)). `Gamma_sin`, proved. Found 2026-10-07 (REVIEW.md, "Statement defects
  repaired on 2026-10-07").
- [5.12.E8](https://dlmf.nist.gov/5.12.E8): Mathlib's `betaIntegral` is the literal integral; the
  right side is written with Gamma functions. `beta_vertical`, proved. Found 2026-10-17
  (REVIEW.md, "Remaining Gamma admissions, second round").
- [8.10.E8](https://dlmf.nist.gov/8.10.E8) (borderline (a)/(c)): the integral needs a > 0; a = 0 as a
  limit. `incompleteGamma_positive_exponential_bounds`, `..._limit`, proved. DLMF678Acquisition.md.
- [11.4.E18](https://dlmf.nist.gov/11.4.E18): ν + 1/2 ∉ −ℕ added (removable term totalized to 0).
  `struveH_bessel_series_18`, proved. Found 2026-10-20.
- [11.10](https://dlmf.nist.gov/11.10), Anger scaled coefficients: removable limits at λ = 1 stated
  as limits. DLMF111214Acquisition.md.
- [13.6.E11](https://dlmf.nist.gov/13.6.E11): Γ(0) = 0 in Lean; nonpositive integer ν (ν − n)
  excluded. `kummerM_besselI_sum`, `kummerM_besselI_sum_neg`, proved. Found 2026-10-07.
- [13.16.E8](https://dlmf.nist.gov/13.16.E8) (borderline (a)/(c)): the Bochner integral also needs
  Re(−μ−κ) + 1/2 > 0. `whittakerW_integral_besselK`, proved. Found 2026-10-08 (REVIEW.md, "Further
  proofs and a statement correction").
- [13.17.E1](https://dlmf.nist.gov/13.17.E1), [13.17.E3](https://dlmf.nist.gov/13.17.E3): denominator
  ≠ 0 added (x/0 = 0 at the poles). `whittakerM_continued_fraction_limit`,
  `whittakerW_continued_fraction_limit`, proved. Found 2026-10-21.
- [13.23.E3](https://dlmf.nist.gov/13.23.E3), [13.23.E8](https://dlmf.nist.gov/13.23.E8),
  [13.23.E9](https://dlmf.nist.gov/13.23.E9), [13.23.E10](https://dlmf.nist.gov/13.23.E10),
  [13.23.E12](https://dlmf.nist.gov/13.23.E12): ordinary M divided by Γ(−n) = 0 replaced by the
  regularized Whittaker M. `mellin_whittakerM`, `cosine_whittakerM`, `bessel_whittakerM`,
  `bessel_whittakerM_W`, `bessel_whittakerW_M`, proved. Found 2026-10-18 (REVIEW.md, "Whittaker
  corrections and the first prioritized proof batch").
- [14.12.E4](https://dlmf.nist.gov/14.12.E4) (borderline (a)/(c)): Re(μ+ν) > −1 for convergence.
  `associatedP_cosh_integral`, proved. DLMF111214Acquisition.md.
- [14.15.E23](https://dlmf.nist.gov/14.15.E23) (borderline (a)/(c)): X_0 = 0 is degenerate; now
  0 < c → 0 < X_c. `cylinderEnvelopeCross_spec`, admitted. Found 2026-10-22 (REVIEW.md, "Round 9
  statement correction").
- [14.20.E10](https://dlmf.nist.gov/14.20.E10): the singular endpoint θ = π excluded.
  `conical_power_series`, proved. DLMF111214Acquisition.md.
- [17.6.E28](https://dlmf.nist.gov/17.6.E28): Gamma poles excluded, with a parameter-limit statement.
  `heine_jackson_integral`, `heine_jackson_parameter_limit`, admitted. DLMF17Acquisition.md.
- [17.13.E3](https://dlmf.nist.gov/17.13.E3): removable-limit values of a Gamma quotient, with a
  limit statement and a literal regular-strip statement (DLMF/QHypergeometric/Integrals.lean).
  DLMF17Acquisition.md.
- [20.7.E11](https://dlmf.nist.gov/20.7.E11), [20.7.E12](https://dlmf.nist.gov/20.7.E12),
  [20.7.E25](https://dlmf.nist.gov/20.7.E25), [20.7.E34](https://dlmf.nist.gov/20.7.E34),
  [20.8.E1](https://dlmf.nist.gov/20.8.E1), [20.11.E9](https://dlmf.nist.gov/20.11.E9)
  - Where DLMF divides by a theta function, a nonvanishing hypothesis is added; with Lean's
    x/0 = 0 the printed quotients are false at the zeros.
  - Lean: `jacobiTheta_reduction_two_mul`, `jacobiTheta_reduction_two_tau`,
    `hasDerivAt_jacobiThetaTwoTau_div_four`, the three 20.7.E34 forms,
    `jacobiTheta_watson_expansion` (DLMF/Theta/Identities.lean, admitted);
    `combinedTheta_symmetry` (DLMF/Theta/Generalizations.lean, proved).
  - Found: 2026-10-25.
- [20.10.E3](https://dlmf.nist.gov/20.10.E3)
  - The right side (1 − 2^(1−s)) π^(−s/2) Γ(s/2) ζ(s) is removable at s = 1, where Lean's totalized
    ζ(1) would make it 0. Stated for s ≠ 1, with the value ln 2 at s = 1 separately.
  - Evidence: mpmath at s = 0.6 + 0.2i, 1.5, 3, 2.5 + 0.3i and s = 1.
  - Lean: `mellin_one_sub_jacobiThetaFourNullTau`, `mellin_one_sub_jacobiThetaFourNullTau_one`
    (DLMF/Theta/Integrals.lean), admitted.
  - Found: 2026-10-25.

### Branches and multivalued sets

- [19.16.E11](https://dlmf.nist.gov/19.16.E11), [19.21.E4](https://dlmf.nist.gov/19.21.E4),
  [19.21.E5](https://dlmf.nist.gov/19.21.E5): unprinted branch conditions made explicit:
  ph λ + ph zⱼ ∈ (−π, π) for the homogeneity 19.16.E11, and the sign of Im z (`SignType.sign z.im`)
  in 19.21.E4–E5. `symEllIntR_mul` (proved) and the 19.21 connection formulas
  (DLMF/EllipticIntegrals/SymmetricConnection.lean). DLMF19Acquisition.md. Found 2026-10-25.
- [4.5.E3](https://dlmf.nist.gov/4.5.E3), [4.5.E14](https://dlmf.nist.gov/4.5.E14) (borderline
  (a)/(c)): strict below the exact nonzero root, weak at it; the decimal cutoff is excluded as
  numerical. `abs_log_one_sub_lt`, `abs_log_one_sub_le`, `exp_neg_lt_linear`, `exp_neg_le_linear`,
  proved. DLMF4Acquisition.md.
- [4.8.E5](https://dlmf.nist.gov/4.8.E5): n Ln z alone misses branches; all integer shifts of
  n log z are used. `generalLogValues_zpow`, proved. DLMF4Acquisition.md.
- [4.24.E13](https://dlmf.nist.gov/4.24.E13): the literal independent-root set equality is false
  (u = v = 1); the branch-compatible identity is proved (`arcsin_general_add`).
- [4.24.E16](https://dlmf.nist.gov/4.24.E16): square-root signs correlated with the inverse values
  (`arcsin_arccos_general_add`, proved).
- [8.7.E2](https://dlmf.nist.gov/8.7.E2): the segment from x to x + y must avoid the cut
  (a = 0.3, x = −1 + 0.1i, y = −0.2i otherwise fails). `incompleteGamma_increment_series`, proved.
  Found 2026-10-22 (REVIEW.md, "Round 8").
- [9.6.E11](https://dlmf.nist.gov/9.6.E11), [9.6.E13](https://dlmf.nist.gov/9.6.E13),
  [9.6.E15](https://dlmf.nist.gov/9.6.E15), [9.6.E17](https://dlmf.nist.gov/9.6.E17),
  [9.6.E19](https://dlmf.nist.gov/9.6.E19): (3/z)^(1/2) written as √3 z^(−1/2) to match the
  logarithmic ζ on the left. The `..._third_eq_airy_complex` family (DLMF/Airy/Relations.lean),
  proved. Found 2026-10-20.
- [9.13.E27](https://dlmf.nist.gov/9.13.E27), [9.13.E31](https://dlmf.nist.gov/9.13.E31),
  [9.13.E32](https://dlmf.nist.gov/9.13.E32) (borderline (a)/(c)): the ray integrals diverge at 0
  for positive integer p; a Hadamard finite part is used and the homogeneous equations are
  asserted for p ≤ 0. Proved (DLMF/Airy/GeneralizedContours.lean). AiryAcquisition.md.
- [12.13.E5](https://dlmf.nist.gov/12.13.E5): endpoint hypothesis for t = π/4 added; no
  counterexample claimed. `pcfU_rotational_addition`, admitted. DLMF111214Acquisition.md.

### Implicit conventions made explicit

- [21.2.E6](https://dlmf.nist.gov/21.2.E6): the hypothesis Ωᵀ = Ω is stated (DLMF's Ω is a Riemann
  matrix, hence symmetric). `riemannThetaChar_eq` (DLMF/RiemannTheta/Basic.lean), proved.
  Found 2026-10-25.
- [21.5.E5](https://dlmf.nist.gov/21.5.E5): A must be invertible over ℤ (A ∈ GL_g(ℤ), so that Γ is
  an integer symplectic matrix), not merely det A ≠ 0. `riemannTheta_unimodular`
  (DLMF/RiemannTheta/Modular.lean), proved. Found 2026-10-25.
- [21.6.E3](https://dlmf.nist.gov/21.6.E3), [21.6.E4](https://dlmf.nist.gov/21.6.E4): the
  representatives of 𝒦 are taken in ℤ^(g×h)T, as DLMF's definition 21.6.1 says; with arbitrary
  lifts modulo integer matrices the identity fails (g = 1, T = [[3/5, 4/5], [4/5, −3/5]]).
  `riemann_identity`, `riemann_identity_char` (DLMF/RiemannTheta/Products.lean), admitted.
  Found 2026-10-25.

### DLMF's own published errata followed

- [22.16.E14](https://dlmf.nist.gov/22.16.E14): the corrected form (DLMF erratum of 2010-07-08,
  Karney) is used. `Real.jacobiEpsilonk_eq_integral_sn` (DLMF/JacobiElliptic/Related.lean),
  admitted.
- [23.18.E7](https://dlmf.nist.gov/23.18.E7): the V1.0.11 erratum (no coprimality condition on r) is
  followed. `dedekindSum` (DLMF/Weierstrass/ModularFunctions.lean), definition.

## Outside the DLMF scope

Errors in the supporting sources, recorded in Lean docstrings or reviews:

- AAR (4.1.11): the right-hand denominator is printed a instead of c (DLMF 13.2.39 is right).
  `kummerM_kummer_transform` (DLMF/Confluent/Basic.lean), proved.
- AAR Theorem 8.9.1(a): the last denominator (α)_(2k) should be (α+1)_(2k) (k = 1, α = 1/2,
  β = 1 gives 8/15 against the printed 8/3). `nearly_poised_3F2` (DLMF/Selberg/Applications.lean),
  proved.
- Beals–Wong p. 407: the substitution φ(x) = ψ(i 2^(−1/2) x) needs a scale k with k³ = −1/2
  (REVIEW.md, "Beals–Wong Painlevé II").

Checked and cleared (not errata): 11.5.8 (`struveH_barnes`, the earlier quadrature disagreement
was truncation) and 11.11.16 (`angerA_turning_equiv`).
