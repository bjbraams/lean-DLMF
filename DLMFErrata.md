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
subsection "DLMF errata and source corrections"; ledgers DLMF20–DLMF23Acquisition.md). The Chapter 24–27 entries were found by the acquisition agents and
confirmed by an independent numerical and brute-force check (REVIEW.md, section "Chapters 24–27
acquisition (2026-10-25)"; ledgers DLMF24–DLMF27Acquisition.md); three suspected items that
the check did not confirm are listed under (c) or dropped.

Counts (2026-10-25): 89 entries in (a), 22 in (b), 37 in (c). Some entries group closely related
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
- [19.19.E3](https://dlmf.nist.gov/19.19.E3)
  - Printed: R₋ₐ(𝐛; 𝐳) = zₙ^(−a) Σ (a)_N/(c)_N T_N(b₁, …, bₙ₋₁; 1 − z₁/zₙ, …), |1 − zⱼ/zₙ| < 1.
    DLMF derives it from 19.16.11 and 19.19.2 but omits the condition of 19.16.11. Correct with
    ph zₙ + ph(zⱼ/zₙ) ∈ (−π, π) for every j.
  - Evidence: n = 2, a = 0.3, 𝐛 = (0.5, 0.7), z₁ = e^(−0.8πi), z₂ = e^(0.9πi) (|1 − z₁/z₂| ≈ 0.908):
    R = 1.8216 − 0.4034i by the integral 19.16.9, against 0.5763 − 0.8336i from the formula; the
    formula with the roles of z₁, z₂ exchanged gives a third value, 0.6147 + 0.8057i.
  - Lean: `symEllIntR_hasSum_T_last` (DLMF/EllipticIntegrals/SymmetricSeries.lean), with the
    hypothesis `harg` added on 2026-10-25 (the acquired statement without it was false); proved.
  - Found: 2026-10-25 (proof round 1).
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

### Chapter 24 (Bernoulli and Euler polynomials)

- [24.4.E24](https://dlmf.nist.gov/24.4.E24)
  - The printed multiplication formula with roots of unity is false for every n ≥ 1 (at n = 1 it
    is off by −(m − 1)). Correct: B_n(mx) = m^n B_n(x) − n Σ_{k=1}^n Σ_{j=0}^{k−1} (−1)^j C(k−1, j)
    (Σ_{r=1}^{m−1} ζ^r/(1 − ζ^r)^k) (j + mx)^(n−1), ζ = e^(2πi/m), derived by partial fractions.
  - Evidence: x = 0.37, m = 2, n = 1: printed −0.76, B_1(0.74) = 0.24; the corrected form agrees
    to about 1e-24 for n ≤ 8, m ≤ 6 at real and complex x.
  - Lean: `bernoulliPolyB_mul_eq_roots_of_unity` (DLMF/BernoulliEuler/Properties.lean), admitted.
  - Found: 2026-10-25.
- [24.4.E8](https://dlmf.nist.gov/24.4.E8), [24.4.E11](https://dlmf.nist.gov/24.4.E11)
  (missing conditions)
  - 24.4.8 fails at n = 0 (as 24.4.7 does, entry above; 24.4.26 received n > 0 in erratum V1.0.5,
    but these two did not). 24.4.11 fails at m = 1 for n ≥ 1 (left side 1, right side 0).
  - Lean: `sum_Icc_neg_one_pow_mul_pow_eq_euler` (n ≥ 1), `sum_coprime_pow` (m ≥ 2)
    (DLMF/BernoulliEuler/Properties.lean), admitted.
  - Found: 2026-10-25.
- [24.10.E3](https://dlmf.nist.gov/24.10.E3) (missing condition)
  - Kummer's congruence fails when m = 1 or n = 1: p = 3, m = 1, n = 3 gives B_1/1 = −1/2 ≢ 0 = B_3/3
    (mod 3). A scan of p < 30, m, n < 40 finds 92 failures, all with m = 1 or n = 1.
  - Lean: `kummer_congruence` (m, n ≥ 2) (DLMF/BernoulliEuler/Arithmetic.lean), admitted.
  - Found: 2026-10-25.
- [24.12.E11](https://dlmf.nist.gov/24.12.E11)
  - Printed: for odd n, y_{2m}^{(n)} → m − 1/2. Correct: y_m^{(n)} → m − 1/2 (the zeros of
    cos πx); y_{2m}^{(n)} tends to 2m − 1/2, so the printed form fails for every m ≥ 1, and
    already 24.12.9–24.12.10 place y_2^{(n)} near 3/2.
  - Evidence: the zeros of E_n in [1/2, ∞) for n = 21, 41, 61 are about 0.5, 1.50025, 2.49975,
    3.50025, 4.49975, 5.50025 (sign changes, mpmath; found by p24b, recomputed independently).
  - Lean: `r24b_tendsto_eulerRealZero_odd_counterexample` (proved), `tendsto_eulerRealZero_odd`
    (corrected statement, proved) (DLMF/BernoulliEuler/Zeros.lean).
  - Found: 2026-10-25 (proof round 2).
- [24.16.E9](https://dlmf.nist.gov/24.16.E9) (branch, borderline (a)/(c))
  - For complex t, t/(e^t − 1) is real and negative at t ≈ 2.0085 + 4.4072i (|t| ≈ 4.84 < 2π), so
    the principal power (t/(e^t − 1))^x is not the analytic branch on all of |t| < 2π.
  - Evidence: t = 1.9663 + 4.4315i, x = 1/2: principal power 0.0032 + 0.8049i, series −0.0032 − 0.8049i.
  - Lean: `hasSum_norlundPolynomial` (‖t‖ < π, complex), `hasSum_norlundPolynomial_real`
    (|t| < 2π, real) (DLMF/BernoulliEuler/Generalizations.lean), both proved (proof round 3,
    2026-10-26).
  - Found: 2026-10-25.

### Chapter 25 (zeta and related functions)

- [25.11.E23](https://dlmf.nist.gov/25.11.E23)
  - The first denominator must be 8n√3·3^(2n−1), not 8n√3(3^(2n−1) − 1).
  - Evidence: n = 1: ζ′(−1, 1/3) = 0.0937262017607794; printed 0.0433428…; corrected agrees to
    15 digits (also n = 2, 3, 4) and with 25.11.21 at h = 1, k = 3.
  - Lean: `deriv_hurwitzZeta_one_sub_two_mul_third` (DLMF/Zeta/Hurwitz.lean), admitted.
  - Found: 2026-10-25.
- [25.11.E37](https://dlmf.nist.gov/25.11.E37) (branch)
  - With principal logarithms the identity holds only modulo 2πi (off by exactly 2πi at n = 2,
    a = 4 − 9i, and at n = 3, a = 1 + 5i); it holds with the log-gamma function.
  - Lean: `hasSum_hurwitzZeta_log_gamma` (real a ≥ 1), `exp_tsum_hurwitzZeta_eq_prod_gamma`
    (exponentiated, Re a ≥ 1) (DLMF/Zeta/HurwitzIntegrals.lean), admitted.
  - Found: 2026-10-25.
- [25.12.E13](https://dlmf.nist.gov/25.12.E13)
  - With the principal ln z the formula fails for Im z < 0 (and contradicts 25.12.4 at s = 2,
    z = −2 − i); it holds with 0 < ph z < 2π, i.e. parameter 1/2 + ln(−z)/(2πi). The error was
    introduced by DLMF's own V1.2.3 modification (e^(2πia) replaced by z).
  - Evidence: s = 2.5 + 0.2i, z = 0.5 − 0.9i: left side −0.19501 − 0.80944i, printed right side
    4.3896 − 6.2751i.
  - Lean: `polylog_add_exp_mul_polylog_inv` (DLMF/Zeta/Polylog.lean), admitted.
  - Found: 2026-10-25.
- [25.14.E7](https://dlmf.nist.gov/25.14.E7) (missing condition)
  - DLMF states no conditions; the formula fails for a = 1.6 + 0.2i, a = 1.5, a = 1.2,
    a = −0.3 + 0.4i, and holds for about 0 < Re a ≤ 1, z ≠ 0, 1 (verified also at |z| = 1 and
    z = 1.5 + 0.5i).
  - Lean: `lerchPhi_transformation` (DLMF/Zeta/Lerch.lean), stated on the narrower verified domain
    0 < Re a < 1, 0 < |z| < 1, admitted.
  - Found: 2026-10-25.

- [25.15.ii](https://dlmf.nist.gov/25.15.ii) (prose)
  - "Infinitely many zeros in the critical strip 0 ≤ ℜs ≤ 1, located symmetrically about the
    critical line": for an even primitive χ the trivial zero s = 0 lies in that strip but
    L(1, χ) ≠ 0. The symmetry ρ ↦ 1 − ρ̄ holds for zeros ρ ≠ 0.
  - Lean: `q25b_LFunction_one_sub_conj_counterexample` (proved), `LFunction_one_sub_conj_eq_zero`
    (hypothesis ρ ≠ 0 added in proof round 1) (DLMF/Zeta/DirichletL.lean), admitted.
  - Found: 2026-10-25 (proof round 1).

### Chapter 26 (combinatorial analysis)

- [26.6.E12](https://dlmf.nist.gov/26.6.E12) (missing condition)
  - C(n) = Σ_{k=1}^n N(n, k) is printed without a condition; at n = 0 the sum is empty while
    C(0) = 1. Holds for n ≥ 1.
  - Lean: `q26a_not_catalan_eq_sum_narayana` (proved counterexample), `catalan_eq_sum_narayana`
    (n ≥ 1, restated in proof round 1) (DLMF/Combinatorics/LatticePaths.lean), proved.
  - Found: 2026-10-25 (proof round 1).
- [26.8.E31](https://dlmf.nist.gov/26.8.E31)
  - The hypothesis "f analytic for all x and the series converges" is insufficient:
    f(z) = sin(πz), x = 0, k = 1 has every Δ^n f(0) = 0 but f′(0) = π. A Newton-series hypothesis is
    needed; acquired for polynomials.
  - Lean: `not_forall_stirling_deriv_eq_fwdDiff_series` (proved),
    `hasSum_signedStirlingFirst_fwdDiff` (polynomials, admitted) (DLMF/Combinatorics/Stirling.lean).
  - Found: 2026-10-25.
- [26.9.E7](https://dlmf.nist.gov/26.9.E7)
  - The sum must run over k, n (printed m, n, with m free on the right), and the condition must be
    |x| < 1 (printed |xq| < 1, insufficient: q = 0.5, x = 1.5).
  - Evidence: power-series check for m ≤ 3, k < 6.
  - Lean: `hasSum_qBinom_mul_pow_x` (DLMF/Combinatorics/RestrictedPartitions.lean), admitted.
  - Found: 2026-10-25.
- [26.10.E9](https://dlmf.nist.gov/26.10.E9)
  - The printed recurrence p_m(D, n) = p_m(D, n − m) + p_(m−1)(D, n) is false (m = n = 2: 1 ≠ 2; 43
    failures for m ≤ 6, n < 15). Correct: p_m(D, n) = p_(m−1)(D, n) + p_m(D, n − m) − p_(m−2)(D, n − m),
    equivalently q_m(n) = q_m(n − m) + q_(m−1)(n − m) for exactly m distinct parts.
  - Lean: `partitionCountAtMostDistinct_recurrence`, `card_distinct_card_eq_recurrence`
    (DLMF/Combinatorics/PartitionIdentities.lean), admitted.
  - Found: 2026-10-25.
- [26.10.iv](https://dlmf.nist.gov/26.10.iv) (prose)
  - "p(D′3, n) ≤ p(D3, n), with strict inequality for n ≥ 9" is wrong: the inequality is strict at
    n = 9 and n ≥ 15 (checked to n = 30) but an equality for 10 ≤ n ≤ 14.
  - Lean: `partitionCountSchur_le`, `partitionCountSchur_lt_iff`
    (DLMF/Combinatorics/PartitionIdentities.lean).
  - Found: 2026-10-25.
- [26.10.E18](https://dlmf.nist.gov/26.10.E18)
  - The range must be 1 ≤ h ≤ k (printed 1 < h ≤ k gives A_1 = 0). With the correction 26.10.17
    gives 295.998 at n = 30 (p(D, 30) = 296); with the printed range 0.23 − 0.07i.
  - Lean: `distinctPartitionKloosterman` (DLMF/Combinatorics/PartitionIdentities.lean), definition.
  - Found: 2026-10-25.
- [26.12.E24](https://dlmf.nist.gov/26.12.E24)
  - The product must run over 1 ≤ h ≤ j ≤ r (printed h < j); at r = 2 the printed form gives
    (1 + q)(1 + q²)/(1 + q + q²) instead of 1 + q². Brute-force generating functions agree with the
    corrected form for r = 1..4.
  - Lean: `sum_descendingPPIn_pow` (DLMF/Combinatorics/PlanePartitions.lean), admitted.
  - Found: 2026-10-25.
- [26.12.E12](https://dlmf.nist.gov/26.12.E12) (prose definition)
  - "Transpose complement" read literally as reflection through the (x, y)-plane gives counts
    0, 0, 2, 2, …; the formula matches only with reflection in the plane x = y (h and j swapped):
    1, 1, 2, 3, 5, 14, 14.
  - Lean: `card_transposeComplement` (DLMF/Combinatorics/PlanePartitions.lean), admitted.
  - Found: 2026-10-25.
- [26.13.E4](https://dlmf.nist.gov/26.13.E4), [26.7.E3](https://dlmf.nist.gov/26.7.E3),
  [26.7.E4](https://dlmf.nist.gov/26.7.E4), [26.4.E10](https://dlmf.nist.gov/26.4.E10),
  [26.8.E10](https://dlmf.nist.gov/26.8.E10), [26.8.E29](https://dlmf.nist.gov/26.8.E29),
  [26.5.E1](https://dlmf.nist.gov/26.5.E1) (missing conditions at n = 0 or m = 0)
  - The floor form of 26.13.4 gives 0 at n = 0 (d(0) = 1); 26.7.3 needs n ≥ 1 (at n = 0, m = 2 it
    gives 1/2); the first (Dobiński) form of 26.7.4 gives 1 − e⁻¹ at n = 0; 26.4.10 fails at m = 0;
    26.8.10 (sum from k = 1) and 26.8.29 fail at n = 0; the fourth form of 26.5.1 fails at n = 0.
  - Lean: `numDerangements_eq_floor` (DLMF/Combinatorics/Permutations.lean), `bell_eq_sum_mul_sum`,
    `bell_eq_exp_neg_one_mul_tsum` (Bell.lean), `multinomial_eq_sum_update` (Multinomial.lean),
    `sum_Icc_stirlingSecond_mul_ascPochhammer`, `sum_neg_one_pow_mul_signedStirlingFirst`
    (Stirling.lean), `catalan_eq_choose_sub` (Catalan.lean); proved or admitted as the ledger says.
  - Found: 2026-10-25.
- [26.17.T1](https://dlmf.nist.gov/26.17.T1) (missing conditions)
  - The entry S(n, 1) + … + S(n, k) fails at n = 0 (count 1, table 0; the sum should start at
    j = 0); p_k(n) − p_(k−1)(n) is undefined at k = 0. The binomial entries need C(−1, 0) = 1.
  - Lean: `twelvefoldCount_*` (DLMF/Combinatorics/TwelvefoldWay.lean), with side conditions.
  - Found: 2026-10-25.
- [26.18.E4](https://dlmf.nist.gov/26.18.E4)
  - The upper limit must be k (printed n): n = 1, k = 3 gives −3, n = 2, k = 4 gives 4, and n = 0,
    k ≥ 1 gives 1 instead of 0. The corrected form holds for all n, k (0⁰ = 1).
  - Lean: `card_surjective_eq_sum` (DLMF/Combinatorics/CountingTechniques.lean), admitted.
  - Found: 2026-10-25.

### Chapter 27 (functions of number theory)

- [27.12.E3](https://dlmf.nist.gov/27.12.E3)
  - Legendre's formula as printed computes π(x) − π(√x). Correct:
    π(x) = π(√x) − 1 + ⌊x⌋ − Σ⌊x/p_j⌋ + Σ_{r≥2} (−1)^r Σ ⌊x/(p_{j1}⋯p_{jr})⌋.
  - Evidence: x = 10: printed 2, π(10) = 4, π(√10) = 2; corrected form checked for x up to 1000.
  - Lean: `primePi_legendre` (DLMF/NumberTheory/Primes.lean), admitted.
  - Found: 2026-10-25.
- [27.3](https://dlmf.nist.gov/27.3), first sentence
  - "Except for ν(n), Λ(n), p_n and π(x), the functions in §27.2 are multiplicative" is false for
    φ_k, k ≥ 1 (sum of k-th powers of the m ≤ n prime to n): φ₁(2)φ₁(3) = 3 ≠ φ₁(6) = 6,
    φ₂(2)φ₂(3) = 5 ≠ φ₂(6) = 26. The other §27.2 functions are multiplicative as claimed.
  - Lean: `totientPowerSum_one_not_multiplicative` (DLMF/NumberTheory/Functions.lean), proved.
  - Found: 2026-10-25.
- [27.3.E6](https://dlmf.nist.gov/27.3.E6) (missing condition)
  - For complex α, α ≠ 0 is insufficient: with α = 2πi/ln 2, 2^α = 1 and the p = 2 factor is 0/0
    (σ_α(8) = 4). The condition is p_r^α ≠ 1 for every prime p_r dividing n.
  - Lean: `sigmaC_eq_prod` (DLMF/NumberTheory/Functions.lean), proved.
  - Found: 2026-10-25.

### Chapters 28–31 (Mathieu, Lamé, spheroidal and Heun functions)

All entries below were found by the acquisition agents on 2026-10-26 and re-derived by an
independent verifier from the DLMF 1.2.8 page text with its own numerics; none is on the DLMF
errata page.

- [28.5.E6](https://dlmf.nist.gov/28.5.E6), second relation
  - Under DLMF's own sign rule (28.5.5–28.5.7) it must read C_{2m+1}(−q) = −S_{2m+1}(q).
  - Evidence: by 28.2.35 and uniqueness, f_{2m+1}(z,−q) = (−1)^{m+1} g_{2m+1}(½π−z,q);
    numerically C₁(−0.5) = −0.494187, S₁(0.5) = +0.494187 (also n = 3, q = 0.2, 1.0).
  - Lean: `mathieuFeC_even_neg` and its neighbours (DLMF/Mathieu/SecondSolutions.lean), admitted.
- [28.23.E2](https://dlmf.nist.gov/28.23.E2)–[28.23.E5](https://dlmf.nist.gov/28.23.E5)
  - "Valid for all z when j = 1" holds only for integer ν. For ν ∉ ℤ the terms with n → −∞
    behave like |cosh z|^{−2|n|} (|sinh z|^{−2|n|} in 28.23.4–5), so the series need the
    condition |cosh z| > 1 (resp. |sinh z| > 1).
  - Evidence: ν = 0.5, h = 1, z = 0.5i: terms at n = −5, −20, −40 are 0.027, 0.15, 9.8.
  - Lean: `hasSum_modMathieuM_cosh`, `hasSum_modMathieuM_cosh_deriv`, `hasSum_modMathieuM_sinh`,
    `hasSum_modMathieuM_sinh_deriv` (DLMF/Mathieu/Modified/BesselSeries.lean), admitted with the
    condition |cosh z| > 1 (resp. |sinh z| > 1) for every j.
- [28.28.E11](https://dlmf.nist.gov/28.28.E11)
  - The factor e^{iνπ} must be e^{iνπ/2}: right side ½πi e^{iνπ/2} ce_ν(0,h²) M_ν^{(3)}(z,h).
  - Evidence: term-by-term integration with 10.9.10 and 28.23.2 (j = 3); numerically at ν = 0.4,
    h = 0.8, z = 1 + 0.5i the left side is 0.13373867 − 0.12414858i, the corrected right side
    0.13373835 − 0.12414756i, the printed one 0.18117 − 0.02183i.
  - Lean: `integral_exp_cosh_modMathieuCe` (DLMF/Mathieu/Modified/Integrals.lean), admitted.
- [28.28.E16](https://dlmf.nist.gov/28.28.E16)
  - The overall sign is wrong, and the lower sign belongs to −π ≤ y ≤ 0, not π ≤ y ≤ 2π:
    ∫₀^∞ sin(2h cos y cosh t) Ce_{2n}(t,h²) dt = +πA₀^{2n}(h²)/(2ce_{2n}(½π,h²)) ·
    (ce_{2n}(y,h²) ∓ 2fe_{2n}(y,h²)/(πC_{2n}(h²))), upper sign for 0 ≤ y ≤ π.
  - Evidence: h = 0.8, y = 2: left side −0.1431816729, printed right side +0.1431816729 (n = 0;
    same for 2n = 2, 4); the left side is even in y and fe_{2n} is odd; at y = π + 0.3 the
    printed range gives ±2.05 against −0.4207.
  - Lean: `integral_sin_cosh_modMathieuCe` (DLMF/Mathieu/Modified/Integrals.lean), admitted.
- [28.31(iii)](https://dlmf.nist.gov/28.31.iii), Asymptotic Behavior, second paragraph
  - The powers are swapped: for ξ > 0, hc_p^m(z,−ξ) and hs_p^m(z,−ξ) behave like multiples of
    exp(¼ξ cos 2z)(sin z)^p as z → ½π ± i∞, and the other periodic solutions like
    exp(−¼ξ cos 2z)(sin z)^{−p−2}.
  - Evidence: 28.31.19–20 and the first paragraph; numerically the ratio to the corrected form
    converges (−0.416, −0.472, −0.480 for hc_2^0 at y = 2, 3, 4), the ratio to the printed form
    grows like e^{(2p+2)y}.
  - Lean: `paraboloidal_asymptotic_neg` (DLMF/Mathieu/Hill/Ince.lean), admitted.
- [30.11.E6](https://dlmf.nist.gov/30.11.E6), j = 1, 2
  - The error term must be O(z⁻² e^{|ℑ(γz)|}), not O(z⁻² e^{|ℑz|}) (false for γ > 1).
  - Evidence: m = n = 0, γ = 3, z = x(1 + 0.5i), x = 5, …, 40: |err||z|²e^{−|ℑz|} = 13.8, …,
    2.3·10¹⁶, while |err||z|²e^{−|ℑ(γz)|} = 0.093, …, 0.099.
  - Lean: `spheroidalRadial_isBigO_one_two` (DLMF/Spheroidal/Radial.lean), admitted, real γ > 0.
- [31.10.E8](https://dlmf.nist.gov/31.10.E8)
  - The coefficient of ∂𝒦/∂φ must be (2δ−1) cot φ − (2ε−1) tan φ.
  - Evidence: exact symbolic comparison with D_z − D_t on test polynomials (constant ratio only
    for the corrected coefficient); kernel 31.10.10 residual 10⁻³¹ against 1.18 as printed.
  - Lean: `heun_kernel_typeI_angles` (DLMF/Heun/Integral.lean), admitted.
- [31.10.E17](https://dlmf.nist.gov/31.10.E17)
  - u must be (stz/a)^{1/2}, not (stz)^{1/2}/a; then u² + v² + w² = s + t + z − 1 − a.
  - Evidence: 31.10.14 against 31.10.18 on test polynomials (sympy): constant ratio only with
    u² = stz/a.
  - Lean: `heun_kernel_typeII_uvw` (DLMF/Heun/Integral.lean), admitted.
- [31.10.E22](https://dlmf.nist.gov/31.10.E22)–[31.10.E23](https://dlmf.nist.gov/31.10.E23)
  - The printed cos²θ P-symbol violates Fuchs's relation (its exponents sum to γ/2). Correct:
    exponent 1 − γ at 0 (not ½(3 − γ)); p² + (α+β−γ)p − σ₂/4 = 0; a + b = α + β + 2p;
    ab = p² + (α+β)p − σ₁/4; c = γ − α − β − 2p. The m-equation and the a′, b′ relations
    are right.
  - Evidence: separation of 31.10.21 by hand; the corrected product kernel leaves a residual of
    2·10⁻³¹ in 31.10.21, the printed one 8.2.
  - Lean: `heun_kernel_typeII_separable` (DLMF/Heun/Integral.lean), admitted.
- [31.10](https://dlmf.nist.gov/31.10.i), Example 2 (31.10.11)
  - z^{−α} Hl(1/a, q_m; α, α−γ+1, α−β+1, δ; 1/z) does not solve Heun's equation; the accessory
    parameter must be q_m/a − α(β−ε) − (α/a)(β−δ), as in the corrected 31.3.10 (DLMF erratum,
    Karney 2022), which Example 2 was not brought in line with.
  - Evidence: a = 0.4, q = 0.37, (α, β, γ, δ) = (0.6, 1.9, 1.3, 0.7), z = 5: residual 2.2·10⁻³
    as printed, 1.5·10⁻³² corrected.
  - Lean: only the kernel equation is acquired (`heun_kernel_example₂_pde`,
    DLMF/Heun/Integral.lean); the representation is not.

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

- [19.8.E6](https://dlmf.nist.gov/19.8.E6): the summand `agmSeqC 1 g₀ n ^ 2` used the real square root
  cₙ = √(aₙ² − gₙ²), which is 0 at n = 0 when k² < 0 (then g₀ = k′ > a₀ = 1), whereas DLMF has
  c₀² = k². The first identity was false for k² < 0 (mpmath at k² = −1: 0.04305 against
  −0.45695). Fix: the summand is aₙ² − gₙ² (DLMF 19.8.2). `compEllIntEk_eq_agm`
  (DLMF/EllipticIntegrals/Quadratic.lean), proved for all real k² < 1. Found 2026-10-25 (proof
  round 1).
- [19.22.E9](https://dlmf.nist.gov/19.22.E9), [19.22.E10](https://dlmf.nist.gov/19.22.E10), [19.22.E12](https://dlmf.nist.gov/19.22.E12), [19.22.E14](https://dlmf.nist.gov/19.22.E14): the AGM sequences
  `agmA`, `agmG` (DLMF/EllipticIntegrals/SymmetricQuadratic.lean) took index n + 1 from Mathlib's
  `NNReal.agmSequences (n + 1)`, which already holds the (n + 2)-th means, so a₁ and g₁ were
  skipped and all four series were false (a₀ = 2, g₀ = 1: (4/π)R_G = 1.541964 against 1.714838).
  Fix: index n + 1 uses `agmSequences n`. `symEllIntRG_zero_agm`, `symEllIntRD_zero_agm` proved;
  19.22.E12, E14 admitted. Found 2026-10-25 (proof round 1).

- [20.2.ii](https://dlmf.nist.gov/20.2.ii): the earlier `jacobiThetaOneTau_div_sin_analytic` asked,
  for each fixed z, only for some analytic function of τ agreeing with θ₁(z|τ)/sin z where
  sin z ≠ 0 (and likewise θ₂/cos z). At the zeros of sin z this is vacuous, so the statement was
  trivially true and missed DLMF's meaning. Restated (user decision): one function F(z, τ), entire
  in z, analytic in τ on Im τ > 0, equal to the quotient where sin z ≠ 0, so that at the zeros it is
  the removable-singularity value. Proved (F is the Fourier series 20.2.1 divided termwise by
  sin z, via the Dirichlet kernel; G(z, τ) = F(π/2 − z, τ)). DLMF/Theta/Basic.lean. Found
  2026-10-25 (proof round 1), restated and proved the same day.

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

### Chapters 24–27

- Chapter 25 removable points: 25.4.2 (s ≠ 2, 3, …), 25.4.5 (s ≠ −1, −2, …), 25.5.13 (s ≠ 0),
  25.8.3 (s ≠ 0, −1, …), 25.8.6 (z ≠ 0) and 25.10.4 (cos √(2πt) ≠ 0) carry hypotheses because
  Lean's Γ vanishes at its poles, cot 0 = 0 and ζ(1) is a junk value; 25.2.3, 25.5.3, 25.5.4,
  25.5.10 and 25.5.21 are stated multiplied by 1 − 2^(1−s), which is stronger than DLMF.
  DLMF/Zeta (DLMF25Acquisition.md, part A).
- [25.10.E2](https://dlmf.nist.gov/25.10.E2): θ(t) uses the principal arg, as DLMF prescribes; it
  differs from the continuous Riemann–Siegel θ by multiples of 2π. `riemannSiegelTheta`
  (DLMF/Zeta/Zeros.lean), definition.
- Chapter 25 implicit conditions made explicit by the acquisition (not independently
  re-verified): s ≠ −m in 25.11.16; s ≠ 0 in 25.11.17 and 25.11.41; s ≠ 1 in 25.11.31 and 25.11.35;
  k ≥ 2 in 25.15.3, 25.15.6 and 25.15.10; z ≠ 0 and z ∉ [1, ∞) in 25.12.12 and 25.14.3_1.
  DLMF25Acquisition.md, part B.
- [25.11.E10](https://dlmf.nist.gov/25.11.E10): at s = 0, −1, −2, … the term with n + s = 1
  is DLMF's limit of (s)_n ζ(n + s), whereas Lean's `poch s n · ζ(1)` is 0; at s = 0, a = 1/2 the
  Lean series sums to −1/2 while ζ(0, 1/2) = 0. The hypothesis s ≠ 0, −1, −2, … was added.
  `r25b_hasSum_hurwitzZetaComplex_taylor_counterexample` (proved),
  `hasSum_hurwitzZetaComplex_taylor` (DLMF/Zeta/Hurwitz.lean), admitted. Found 2026-10-25
  (proof round 2).
- [26.8.E5](https://dlmf.nist.gov/26.8.E5), [26.8.E27](https://dlmf.nist.gov/26.8.E27),
  [26.8.E33](https://dlmf.nist.gov/26.8.E33): the hypothesis k ≤ n comes from Lean's truncated
  natural subtraction and from the left side's domain; DLMF is right as printed (independent check
  2026-10-25). DLMF/Combinatorics/Stirling.lean.

### Chapters 28–31

- [28.6.E16](https://dlmf.nist.gov/28.6.E16): the continued fraction holds for n ≥ 1; for
  n = 0 the first numerator is −2q² (a₀ = −2q²/(4 − a − q²/(16 − a − ⋯))). Both forms are
  acquired. `mathieuA_even_contFrac` (DLMF/Mathieu/SmallQ.lean).
- [28.5.E5](https://dlmf.nist.gov/28.5.E5), n = 0: the normalization forces C₀(q) → ∞ as q → 0,
  so fe₀ with this normalization is discontinuous at q = 0, where 28.5.7 sets fe₀(z, 0) = z by
  convention; the convention is built into `mathieuFe` (DLMF/Mathieu/Basic.lean).
- [28.6.E12](https://dlmf.nist.gov/28.6.E12)–[28.6.E13](https://dlmf.nist.gov/28.6.E13): no
  erratum. The q⁶ denominator is 92935987200000 as printed (grouped `9293 59872 00000`); an
  acquisition agent's first report misread the grouping.
- [29.8](https://dlmf.nist.gov/29.8): the kernels use the Ferrers function 𝖯_ν at arguments
  outside [−1, 1]; the analytic continuation F(ν+1, −ν; 1; ½ − ½x), i.e. the Legendre P_ν, is
  meant, and the Lean statements use `DLMF.Legendre.legendreP`. Notation, not an erratum.
- Domain choices: 28.12.2, 28.12.8, 28.12.9 and §28.14 are stated for ν ∉ ℤ (they fail for
  integer ν under DLMF's own completion, e.g. λ₁(−q) = b₁(q)); 28.23.2–5 are stated with the
  condition |cosh z| > 1 (|sinh z| > 1) for every j.

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
