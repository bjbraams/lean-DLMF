# DLMF Chapter 24 acquisition: Bernoulli and Euler Polynomials

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 24](https://dlmf.nist.gov/24), version 1.2.8, checked on 2026-10-25. It was
done in two parts: part A (ACQ24A) covers §§24.1–24.10 (definitions, basic properties,
recurrences, explicit formulas, integrals, series, inequalities and arithmetic properties);
part B (ACQ24B) covers §§24.11–24.21 in its own sections below. The modules are under
[DLMF/BernoulliEuler/](DLMF/BernoulliEuler); part A's Mathlib pointers are in
[DLMF/BernoulliEuler/MathlibCoverage.lean](DLMF/BernoulliEuler/MathlibCoverage.lean), part B's
in `DLMF/BernoulliEuler/MathlibCoverageB.lean`. Existing Chapter 24 pointers in
[DLMF/Core/UpstreamElementary.lean](DLMF/Core/UpstreamElementary.lean) (24.2.E2–E5, 24.4.E1,
E3, E7, E18, E25, E27, E34, 24.8.E1–E3) are kept and not repeated.

Bₙ is Mathlib's `bernoulli` (B₁ = -1/2, DLMF's convention; `bernoulli'` has B'₁ = +1/2), and
Bₙ(x) is `Polynomial.bernoulli n` in `ℚ[X]`, with real evaluation `bernoulliFun`. The Euler
polynomials `Polynomial.euler`, the Euler numbers `eulerNumber n = 2ⁿ Eₙ(1/2)` and the real
evaluation `eulerFun` come from
[DLMFMathlib/NumberTheory/EulerPolynomials.lean](DLMFMathlib/NumberTheory/EulerPolynomials.lean).
DLMF §24.1 lets x be real or complex; the project functions
`DLMF.BernoulliEuler.bernoulliPolyB n x` and `eulerPolyE n x` evaluate these polynomials at
complex x.

Part A: §§24.2, 24.4–24.10 have 112 numbered equations (24.2: 12, 24.4: 39, 24.5: 10, 24.6: 12,
24.7: 11, 24.8: 9, 24.9: 10, 24.10: 9), all in scope and all covered, and six tables, of which
24.2.T1 and 24.2.T2 (exact values) are covered in part and 24.2.T3–T6 are excluded: numerical.
§24.1 (notation) and §24.3 (graphics) have no numbered equations. Part A lives in `Basic`,
`GeneratingFunctions`, `Properties`, `Recurrences`, `Explicit`, `Integrals`, `Series`,
`Inequalities` and `Arithmetic` under `DLMF/BernoulliEuler/`, with 119 tagged declarations:
8 definitions, 51 proved theorems and **60 admissions** (`grep -c '\bsorry\b'`: Basic 0,
GeneratingFunctions 1, Properties 5, Recurrences 5, Explicit 12, Integrals 11, Series 8,
Inequalities 9, Arithmetic 9), plus 11 new `dlmf_upstream` pointers and 12 `@[dlmf]` tags added to
existing declarations of `DLMFMathlib/NumberTheory/` (EulerPolynomials, EulerNumbers); with
the two earlier tags (24.2.E1 in BernoulliTaylor, 24.2.E6 in EulerNumbers) these 14
DLMFMathlib declarations are all proved or definitions. No proved theorem depends on an admission.

**Status after proof round 1 (2026-10-25).** The 238 declarations tagged with Chapter 24 IDs are 28 definitions, 146 proved theorems and 64 theorems that still depend on admissions; direct admissions in DLMF/BernoulliEuler fell from 111 to 64. The per-line statuses in this ledger are regenerated from the compiled dump; the counts below record the acquisition. See REVIEW.md, "Proof round 1 for Chapters 24–27 (2026-10-25)".

**Status after proof round 2 (2026-10-25).** The 238 declarations tagged with Chapter 24 IDs are 28 definitions, 175 proved theorems and 35 theorems that still depend on admissions; direct admissions in DLMF/BernoulliEuler fell from 64 to 35. 24.12.11 as printed is false (y_{2m} → 2m − 1/2 for odd n); the corrected statement y_m → m − 1/2 is proved, with a proved counterexample to the printed form (the errata report (reports/DLMFErrata.tex) (a)). See REVIEW.md, "Proof round 2 for Chapters 24–27 (2026-10-25)".

**Status after proof round 3 (2026-10-26).** The 238 declarations tagged with Chapter 24 IDs are 28 definitions, 185 proved theorems and 25 theorems that still depend on admissions; direct admissions in DLMF/BernoulliEuler fell from 35 to 25. No statement was changed. See REVIEW.md, "Proof round 3 for Chapters 24–27 (2026-10-26)".

## Domains, conventions and source corrections (part A)

- Every in-scope formula of §§24.2–24.10 was checked before acquisition, in exact arithmetic
  (sympy) for the polynomial, recurrence, explicit and arithmetic identities and numerically
  (mpmath, 30 digits) for the integrals, series and inequalities, at real and complex sample
  points.
- **24.4.24 is false as printed** (suspected erratum). For n = 1 the printed right side is
  mx - m + 1/2 instead of B₁(mx) = mx - 1/2, because
  ∑_{r=1}^{m-1} ζ^r/(1 - ζ^r) = -(m-1)/2 for ζ = e^{2πi/m}; the identity also fails for
  n = 2, …, 5 and m = 2, 3, 4, and for every sign and exponent variant tried. The corrected form,
  derived from the generating function by the partial fractions
  m/(w^m - 1) = ∑_{r=0}^{m-1} ζ^r/(w - ζ^r), is
  Bₙ(mx) = mⁿBₙ(x) - n ∑_{k=1}^{n} ∑_{j=0}^{k-1} (-1)^j (k-1 choose j)
  (∑_{r=1}^{m-1} ζ^r/(1 - ζ^r)^k) (j + mx)^{n-1}, n ≥ 1, m ≥ 2, verified to working precision
  for n ≤ 7, 2 ≤ m ≤ 5 and complex x; it is the acquired statement (admitted).
- Range corrections (the printed formula fails at an edge of the range of §24.1): 24.4.7 and
  24.4.8 fail for n = 0 (acquired n ≥ 1); 24.4.11 fails for m = 1 (acquired m ≥ 2); Kummer's
  congruence 24.10.3 fails for m = 1 or n = 1 (p = 3, m = 1, n = 3: B₁/1 = -1/2 ≢ 0 = B₃/3
  (mod 3); acquired m, n ≥ 2), whereas 24.10.4 holds for all m, n since its factor 1 - p^{m-1}
  vanishes at m = 1. The small-n failures of 24.5.3 (n = 1), 24.5.4, 24.5.6, 24.5.7 (n = 0) and
  24.6.1–24.6.6 (n = 0) agree with DLMF's stated ranges.
- Stronger than DLMF: 24.5.1 holds for all n (DLMF: n ≥ 2); 24.6.9 for all n; 24.2.6 is proved
  on the full disc |t| < π/2; 24.4.18 (Raabe) is proved for complex x, and all polynomial
  identities of §24.4 are stated for complex x. 24.10.5 also holds for n = 1 and 24.9.4 for n = 1 (checked), but both are
  acquired as printed (n ≥ 2).
- Removable singularities: 24.2.1 and 24.2.3 are stated for 0 < |t| < 2π (the left sides are
  0/0 at t = 0). The generating functions are `HasSum` statements in the complex variable t.
- Periodic functions (§24.2(iii)): `periodicBernoulliB n x = bernoulliFun n (Int.fract x)` and
  `periodicEulerE n x = (-1)^⌊x⌋ eulerFun n (Int.fract x)` on ℝ; Mathlib's `periodizedBernoulli`
  lives on `UnitAddCircle` and the bridge is proved.
- Symbolic operations (§24.4(viii)): P(B(x)) is the ℂ-linear map `umbralBernoulli x` on ℂ[X]
  with Xⁿ ↦ Bₙ(x) (likewise `umbralEuler`); 24.4.36–24.4.39 are proved for every polynomial P.
- Integrals (§24.7) over (0, ∞) are Bochner integrals `∫ t in Set.Ioi 0`; all integrands are
  integrable on the stated ranges, so the totalization of non-integrable integrals plays no
  role. The Mellin–Barnes integral 24.7.11 is written along t = -c + is, so that
  (1/(2πi)) ∫ dt = (1/(2π)) ∫_ℝ ds; it holds for every complex x (checked numerically).
- Series (§24.8): the conditionally convergent boundary cases 24.8.2 with n = 0 and 24.8.3 with
  n = 1 (0 < x < 1) are limits of natural, respectively symmetric, partial sums. Series over
  k ≥ 1 are indexed by k + 1, k : ℕ. In 24.8.8 and 24.8.9 the summability of both series is
  part of the statement, so the `tsum`s are genuine sums.
- Arithmetic (§24.10): two rationals are congruent mod M when M divides the numerator of their
  difference (`RatModEq`, from the prose of §24.10(i)); N₂ₙ and D₂ₙ are `(bernoulli (2n)).num`
  and `.den`. The denominator assertion in the prose after 24.10.1 is
  `bernoulli_two_mul_den_eq_prod` (n ≥ 1).

## Numbered formulas and prose items (part A)

## [§24.2 Definitions and Generating Functions](https://dlmf.nist.gov/24.2)

- [24.2.i](https://dlmf.nist.gov/24.2.i): [`DLMF.BernoulliEuler.bernoulliPolyB`](DLMF/BernoulliEuler/Basic.lean#L52) (definition). Bₙ(x) for complex x is `aeval x (Polynomial.bernoulli n)`; Bₙ is Mathlib's `bernoulli` (B₁ = -1/2, DLMF's convention).
- [24.2.ii](https://dlmf.nist.gov/24.2.ii): [`DLMF.BernoulliEuler.eulerPolyE`](DLMF/BernoulliEuler/Basic.lean#L57) (definition); [`eulerFun`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L330) (definition). Eₙ(x) is `aeval x (Polynomial.euler n)` from DLMFMathlib; Eₙ = 2ⁿ Eₙ(1/2) is `eulerNumber`.
- [24.2.iii](https://dlmf.nist.gov/24.2.iii): [`DLMF.BernoulliEuler.periodicBernoulliB`](DLMF/BernoulliEuler/Basic.lean#L237) (definition); [`DLMF.BernoulliEuler.periodicEulerE`](DLMF/BernoulliEuler/Basic.lean#L241) (definition); Mathlib: [`periodizedBernoulli`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=periodizedBernoulli#doc). B̃ₙ(x) = Bₙ(x - ⌊x⌋) and Ẽₙ(x) = (-1)^⌊x⌋ Eₙ(x - ⌊x⌋) on ℝ; bridge to Mathlib's periodizedBernoulli on UnitAddCircle proved (`periodicBernoulliB_eq_periodizedBernoulli`).
- [24.2.E1](https://dlmf.nist.gov/24.2.E1): [`Complex.hasSum_bernoulli_mul_pow_div`](DLMFMathlib/NumberTheory/BernoulliTaylor.lean#L147) (proved). Generating function t/(eᵗ - 1) = ∑ Bₙ tⁿ/n! for 0 < |t| < 2π (complex t), tagged in place in DLMFMathlib (the removable point t = 0 excluded).
- [24.2.E2](https://dlmf.nist.gov/24.2.E2): [`DLMF.BernoulliEuler.bernoulli_two_mul_add_one_eq_zero_and_sign`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L84) (proved); Mathlib: [`bernoulli_eq_zero_of_odd`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=bernoulli_eq_zero_of_odd#doc). n ≥ 1: B₂ₙ₊₁ = 0 and (-1)ⁿ⁺¹B₂ₙ > 0, proved from Mathlib's ζ(2n) formula.
- [24.2.E3](https://dlmf.nist.gov/24.2.E3): [`DLMF.BernoulliEuler.hasSum_bernoulliPolyB_mul_pow_div`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L116) (proved); Mathlib: [`Polynomial.bernoulli_generating_function`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli_generating_function#doc). Complex x, 0 < |t| < 2π; proved from 24.2.1 and the Appell property.
- [24.2.E4](https://dlmf.nist.gov/24.2.E4): [`DLMF.BernoulliEuler.bernoulli_eq_bernoulliPolyB_zero`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L139) (proved); Mathlib: [`Polynomial.bernoulli_eval_zero`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli_eval_zero#doc). Bₙ = Bₙ(0), complex form.
- [24.2.E5](https://dlmf.nist.gov/24.2.E5): [`DLMF.BernoulliEuler.bernoulliPolyB_eq_sum`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L107) (proved); Mathlib: [`Polynomial.bernoulli`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli#doc). Bₙ(x) = ∑ (n choose k) Bₖ x^{n-k}, complex x.
- [24.2.E6](https://dlmf.nist.gov/24.2.E6): [`DLMF.BernoulliEuler.hasSum_eulerNumber_mul_pow_div'`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L146) (proved); [`Polynomial.hasSum_eulerNumber_mul_pow_div`](DLMFMathlib/NumberTheory/EulerNumbers.lean#L158) (proved). Full radius |t| < π/2 (DLMFMathlib's tagged version has radius 1/2), proved from the sech series `DLMF.Elementary.hasSum_sech`.
- [24.2.E7](https://dlmf.nist.gov/24.2.E7): [`DLMF.BernoulliEuler.eulerNumber_two_mul_add_one_eq_zero_and_sign`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L219) (proved); [`eulerNumber_eq_zero_of_odd`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L298) (proved). E₂ₙ₊₁ = 0 is proved; the sign (-1)ⁿE₂ₙ > 0 is admitted (the theorem carries one sorry).
- [24.2.E8](https://dlmf.nist.gov/24.2.E8): [`DLMF.BernoulliEuler.hasSum_eulerPolyE_mul_pow_div`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L249) (proved); [`Polynomial.euler`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L54) (definition). Complex x, |t| < π.
- [24.2.E9](https://dlmf.nist.gov/24.2.E9): [`DLMF.BernoulliEuler.eulerNumber_eq_two_pow_mul_and_integer`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L279) (proved); [`eulerNumber`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L291) (definition). Eₙ = 2ⁿEₙ(1/2) and Eₙ ∈ ℤ, proved.
- [24.2.E10](https://dlmf.nist.gov/24.2.E10): [`DLMF.BernoulliEuler.eulerPolyE_eq_sum`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L237) (proved). Complex x.
- [24.2.E11](https://dlmf.nist.gov/24.2.E11): [`DLMF.BernoulliEuler.periodic_eq_of_mem_Ico`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L311) (proved). Real x; B̃ₙ(x) = Bₙ(x), Ẽₙ(x) = Eₙ(x) for 0 ≤ x < 1.
- [24.2.E12](https://dlmf.nist.gov/24.2.E12): [`DLMF.BernoulliEuler.periodic_add_one`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L319) (proved). Real x; B̃ₙ(x+1) = B̃ₙ(x), Ẽₙ(x+1) = -Ẽₙ(x).
- [24.2.T1](https://dlmf.nist.gov/24.2.T1): [`DLMF.BernoulliEuler.table_24_2_1`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L331) (proved); Mathlib: [`bernoulli_two`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=bernoulli_two#doc); Mathlib: [`bernoulli'_four`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=bernoulli'_four#doc). Partial: the entries n ≤ 6 (B₀,…,B₆, E₀,…,E₆) proved by computation; the entries 8 ≤ n ≤ 16 are not acquired (they follow by evaluating the definitions).
- [24.2.T2](https://dlmf.nist.gov/24.2.T2): [`DLMF.BernoulliEuler.table_24_2_2`](DLMF/BernoulliEuler/GeneratingFunctions.lean#L370) (proved); Mathlib: [`Polynomial.bernoulli_one`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli_one#doc). Partial: B₂(x), B₃(x), E₁(x), E₂(x), E₃(x) proved as identities in ℚ[X] (B₀ = E₀ = 1 and B₁(x) are Polynomial.bernoulli_zero, Polynomial.euler_zero, Polynomial.bernoulli_one); the rows n = 4, 5 are not acquired.

## [§24.4 Basic Properties](https://dlmf.nist.gov/24.4)

- [24.4.E1](https://dlmf.nist.gov/24.4.E1): [`DLMF.BernoulliEuler.bernoulliPolyB_add_one_sub`](DLMF/BernoulliEuler/Properties.lean#L116) (proved); Mathlib: [`Polynomial.bernoulli_comp_one_add_X`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli_comp_one_add_X#doc). Complex x, all n.
- [24.4.E2](https://dlmf.nist.gov/24.4.E2): [`DLMF.BernoulliEuler.eulerPolyE_add_one_add`](DLMF/BernoulliEuler/Properties.lean#L125) (proved); [`Polynomial.euler_comp_X_add_one_add`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L171) (proved). Complex x, all n.
- [24.4.E3](https://dlmf.nist.gov/24.4.E3): [`DLMF.BernoulliEuler.bernoulliPolyB_one_sub`](DLMF/BernoulliEuler/Properties.lean#L136) (proved); Mathlib: [`Polynomial.bernoulli_comp_one_sub_X`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli_comp_one_sub_X#doc). Complex x.
- [24.4.E4](https://dlmf.nist.gov/24.4.E4): [`DLMF.BernoulliEuler.eulerPolyE_one_sub`](DLMF/BernoulliEuler/Properties.lean#L144) (proved); [`Polynomial.euler_comp_one_sub_X`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L240) (proved). Complex x.
- [24.4.E5](https://dlmf.nist.gov/24.4.E5): [`DLMF.BernoulliEuler.bernoulliPolyB_neg`](DLMF/BernoulliEuler/Properties.lean#L152) (proved); Mathlib: [`Polynomial.bernoulli_comp_neg_X`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli_comp_neg_X#doc). Complex x.
- [24.4.E6](https://dlmf.nist.gov/24.4.E6): [`DLMF.BernoulliEuler.eulerPolyE_neg`](DLMF/BernoulliEuler/Properties.lean#L161) (proved). Complex x.
- [24.4.E7](https://dlmf.nist.gov/24.4.E7): [`DLMF.BernoulliEuler.sum_Icc_pow_eq_bernoulli`](DLMF/BernoulliEuler/Properties.lean#L213) (proved); Mathlib: [`Polynomial.sum_range_pow_eq_bernoulli_sub`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.sum_range_pow_eq_bernoulli_sub#doc). Corrected range n ≥ 1 (fails for n = 0); all m ≥ 0, over ℚ.
- [24.4.E8](https://dlmf.nist.gov/24.4.E8): [`DLMF.BernoulliEuler.sum_Icc_neg_one_pow_mul_pow_eq_euler`](DLMF/BernoulliEuler/Properties.lean#L227) (proved); [`Polynomial.sum_range_neg_one_pow_mul_pow`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L271) (proved). Corrected range n ≥ 1 (fails for n = 0); all m ≥ 0, over ℚ.
- [24.4.E9](https://dlmf.nist.gov/24.4.E9): [`DLMF.BernoulliEuler.sum_range_add_mul_pow`](DLMF/BernoulliEuler/Properties.lean#L173) (proved). Complex a, d ≠ 0, all m, n.
- [24.4.E10](https://dlmf.nist.gov/24.4.E10): [`DLMF.BernoulliEuler.sum_range_neg_one_pow_mul_add_mul_pow`](DLMF/BernoulliEuler/Properties.lean#L188) (proved). Complex a, d ≠ 0, m ≥ 1 (the sum has m terms, m = 1, 2, …).
- [24.4.E11](https://dlmf.nist.gov/24.4.E11): [`DLMF.BernoulliEuler.sum_coprime_pow`](DLMF/BernoulliEuler/Properties.lean#L318) (proved). Corrected range m ≥ 2 (fails for m = 1); sum over 1 ≤ k < m with gcd(k, m) = 1.
- [24.4.E12](https://dlmf.nist.gov/24.4.E12): [`DLMF.BernoulliEuler.bernoulliPolyB_add`](DLMF/BernoulliEuler/Basic.lean#L193) (proved). Complex x, h.
- [24.4.E13](https://dlmf.nist.gov/24.4.E13): [`DLMF.BernoulliEuler.eulerPolyE_add`](DLMF/BernoulliEuler/Basic.lean#L200) (proved); [`Polynomial.euler_comp_X_add_C`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L206) (proved). Complex x, h.
- [24.4.E14](https://dlmf.nist.gov/24.4.E14): [`DLMF.BernoulliEuler.eulerPolyE_eq_sum_bernoulli`](DLMF/BernoulliEuler/Properties.lean#L529) (proved). Complex x.
- [24.4.E15](https://dlmf.nist.gov/24.4.E15): [`DLMF.BernoulliEuler.bernoulli_two_mul_eq_sum_euler`](DLMF/BernoulliEuler/Properties.lean#L1096) (proved). n ≥ 1.
- [24.4.E16](https://dlmf.nist.gov/24.4.E16): [`DLMF.BernoulliEuler.eulerNumber_two_mul_eq_sum_bernoulli`](DLMF/BernoulliEuler/Properties.lean#L1145) (proved). n ≥ 1.
- [24.4.E17](https://dlmf.nist.gov/24.4.E17): [`DLMF.BernoulliEuler.eulerNumber_two_mul_eq_one_sub_sum_bernoulli`](DLMF/BernoulliEuler/Properties.lean#L1190) (proved). n ≥ 1.
- [24.4.E18](https://dlmf.nist.gov/24.4.E18): [`DLMF.BernoulliEuler.bernoulliPolyB_mul`](DLMF/BernoulliEuler/Properties.lean#L391) (proved); Mathlib: [`bernoulliFun_mul`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=bernoulliFun_mul#doc). Raabe's multiplication theorem for complex x, m ≥ 1, extended from Mathlib's real `bernoulliFun_mul` by the identity theorem for polynomials.
- [24.4.E19](https://dlmf.nist.gov/24.4.E19): [`DLMF.BernoulliEuler.eulerPolyE_mul_of_even`](DLMF/BernoulliEuler/Properties.lean#L413) (proved). m even, complex x.
- [24.4.E20](https://dlmf.nist.gov/24.4.E20): [`DLMF.BernoulliEuler.eulerPolyE_mul_of_odd`](DLMF/BernoulliEuler/Properties.lean#L456) (proved). m odd, complex x.
- [24.4.E21](https://dlmf.nist.gov/24.4.E21): [`DLMF.BernoulliEuler.bernoulliPolyB_eq_half`](DLMF/BernoulliEuler/Properties.lean#L492) (proved). Complex x.
- [24.4.E22](https://dlmf.nist.gov/24.4.E22): [`DLMF.BernoulliEuler.eulerPolyE_eq_bernoulliPolyB_sub'`](DLMF/BernoulliEuler/Properties.lean#L519) (proved). Complex x.
- [24.4.E23](https://dlmf.nist.gov/24.4.E23): [`DLMF.BernoulliEuler.eulerPolyE_eq_bernoulliPolyB_sub`](DLMF/BernoulliEuler/Properties.lean#L503) (proved); [`Polynomial.euler_eq_bernoulli`](DLMFMathlib/NumberTheory/EulerNumbers.lean#L37) (proved). Complex x.
- [24.4.E24](https://dlmf.nist.gov/24.4.E24): [`DLMF.BernoulliEuler.bernoulliPolyB_mul_eq_roots_of_unity`](DLMF/BernoulliEuler/Properties.lean#L687) (proved). Erratum: the printed formula is false (already for n = 1); the corrected form is acquired, see Domains, conventions and source corrections.
- [24.4.E25](https://dlmf.nist.gov/24.4.E25): [`DLMF.BernoulliEuler.bernoulliPolyB_zero_one`](DLMF/BernoulliEuler/Properties.lean#L833) (proved); Mathlib: [`Polynomial.bernoulli_eval_zero`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli_eval_zero#doc); Mathlib: [`Polynomial.bernoulli_eval_one`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli_eval_one#doc). All n (Bₙ(1) = (-1)ⁿBₙ).
- [24.4.E26](https://dlmf.nist.gov/24.4.E26): [`DLMF.BernoulliEuler.eulerPolyE_zero_one`](DLMF/BernoulliEuler/Properties.lean#L847) (proved); [`Polynomial.euler_eval_one_add_eval_zero`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L110) (proved). All n.
- [24.4.E27](https://dlmf.nist.gov/24.4.E27): [`DLMF.BernoulliEuler.bernoulliPolyB_half`](DLMF/BernoulliEuler/Properties.lean#L872) (proved); Mathlib: [`bernoulliFun_eval_half`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=bernoulliFun_eval_half#doc); Mathlib: [`bernoulliFun_eval_half_eq_zero`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=bernoulliFun_eval_half_eq_zero#doc). All n.
- [24.4.E28](https://dlmf.nist.gov/24.4.E28): [`DLMF.BernoulliEuler.eulerPolyE_half'`](DLMF/BernoulliEuler/Properties.lean#L882) (proved). All n.
- [24.4.E29](https://dlmf.nist.gov/24.4.E29): [`DLMF.BernoulliEuler.bernoulliPolyB_third`](DLMF/BernoulliEuler/Properties.lean#L887) (proved). All n.
- [24.4.E30](https://dlmf.nist.gov/24.4.E30): [`DLMF.BernoulliEuler.eulerPolyE_third`](DLMF/BernoulliEuler/Properties.lean#L981) (proved). All n.
- [24.4.E31](https://dlmf.nist.gov/24.4.E31): [`DLMF.BernoulliEuler.bernoulliPolyB_quarter`](DLMF/BernoulliEuler/Properties.lean#L909) (proved); [`Polynomial.eulerNumber_two_mul`](DLMFMathlib/NumberTheory/EulerNumbers.lean#L68) (proved); Mathlib: [`Polynomial.bernoulli_three_eval_one_quarter`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli_three_eval_one_quarter#doc). All n.
- [24.4.E32](https://dlmf.nist.gov/24.4.E32): [`DLMF.BernoulliEuler.bernoulliPolyB_sixth`](DLMF/BernoulliEuler/Properties.lean#L935) (proved). All n.
- [24.4.E33](https://dlmf.nist.gov/24.4.E33): [`DLMF.BernoulliEuler.eulerPolyE_sixth`](DLMF/BernoulliEuler/Properties.lean#L960) (proved). All n.
- [24.4.E34](https://dlmf.nist.gov/24.4.E34): [`DLMF.BernoulliEuler.hasDerivAt_bernoulliPolyB`](DLMF/BernoulliEuler/Basic.lean#L207) (proved); Mathlib: [`Polynomial.derivative_bernoulli`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.derivative_bernoulli#doc). HasDerivAt in complex x.
- [24.4.E35](https://dlmf.nist.gov/24.4.E35): [`DLMF.BernoulliEuler.hasDerivAt_eulerPolyE`](DLMF/BernoulliEuler/Basic.lean#L217) (proved); [`Polynomial.derivative_euler`](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L104) (proved). HasDerivAt in complex x.
- [24.4.viii](https://dlmf.nist.gov/24.4.viii): [`DLMF.BernoulliEuler.umbralBernoulli`](DLMF/BernoulliEuler/Properties.lean#L1259) (definition); [`DLMF.BernoulliEuler.umbralEuler`](DLMF/BernoulliEuler/Properties.lean#L1265) (definition). The symbolic evaluation P(B(x)) is the linear map on ℂ[X] sending Xⁿ to Bₙ(x) (`umbralBernoulli`, `umbralEuler`).
- [24.4.E36](https://dlmf.nist.gov/24.4.E36): [`DLMF.BernoulliEuler.umbralBernoulli_comp_add_one_sub`](DLMF/BernoulliEuler/Properties.lean#L1269) (proved). Every polynomial P, complex x.
- [24.4.E37](https://dlmf.nist.gov/24.4.E37): [`DLMF.BernoulliEuler.umbralBernoulli_X_add_C_pow`](DLMF/BernoulliEuler/Properties.lean#L1287) (proved). Complex x, h.
- [24.4.E38](https://dlmf.nist.gov/24.4.E38): [`DLMF.BernoulliEuler.umbralEuler_comp_add_one_add`](DLMF/BernoulliEuler/Properties.lean#L1294) (proved). Every polynomial P, complex x.
- [24.4.E39](https://dlmf.nist.gov/24.4.E39): [`DLMF.BernoulliEuler.umbralEuler_X_add_C_pow`](DLMF/BernoulliEuler/Properties.lean#L1310) (proved). Complex x, h.

## [§24.5 Recurrence Relations](https://dlmf.nist.gov/24.5)

- [24.5.E1](https://dlmf.nist.gov/24.5.E1): [`DLMF.BernoulliEuler.sum_choose_mul_bernoulliPolyB`](DLMF/BernoulliEuler/Recurrences.lean#L31) (proved). All n (stronger than DLMF, which states n ≥ 2), complex x.
- [24.5.E2](https://dlmf.nist.gov/24.5.E2): [`DLMF.BernoulliEuler.sum_choose_mul_eulerPolyE_add`](DLMF/BernoulliEuler/Recurrences.lean#L42) (proved). All n, complex x.
- [24.5.E3](https://dlmf.nist.gov/24.5.E3): [`DLMF.BernoulliEuler.sum_choose_mul_bernoulli_eq_zero`](DLMF/BernoulliEuler/Recurrences.lean#L52) (proved); Mathlib: [`sum_bernoulli`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=sum_bernoulli#doc). n ≥ 2 (fails for n = 1).
- [24.5.E4](https://dlmf.nist.gov/24.5.E4): [`DLMF.BernoulliEuler.sum_choose_two_mul_mul_eulerNumber`](DLMF/BernoulliEuler/Recurrences.lean#L58) (proved). n ≥ 1.
- [24.5.E5](https://dlmf.nist.gov/24.5.E5): [`DLMF.BernoulliEuler.sum_choose_mul_two_pow_mul_eulerNumber`](DLMF/BernoulliEuler/Recurrences.lean#L86) (proved). All n.
- [24.5.E6](https://dlmf.nist.gov/24.5.E6): [`DLMF.BernoulliEuler.sum_choose_sub_two_mul_bernoulli_div`](DLMF/BernoulliEuler/Recurrences.lean#L217) (proved). n ≥ 1.
- [24.5.E7](https://dlmf.nist.gov/24.5.E7): [`DLMF.BernoulliEuler.sum_choose_mul_bernoulli_div`](DLMF/BernoulliEuler/Recurrences.lean#L267) (proved). n ≥ 1.
- [24.5.E8](https://dlmf.nist.gov/24.5.E8): [`DLMF.BernoulliEuler.sum_two_pow_mul_bernoulli_div_factorial`](DLMF/BernoulliEuler/Recurrences.lean#L298) (proved). n ≥ 1.
- [24.5.E9](https://dlmf.nist.gov/24.5.E9): [`DLMF.BernoulliEuler.bernoulli_inversion`](DLMF/BernoulliEuler/Recurrences.lean#L324) (proved). Both directions of the inversion stated (DLMF: each identity implies the other) for sequences aₙ, bₙ in ℂ.
- [24.5.E10](https://dlmf.nist.gov/24.5.E10): [`DLMF.BernoulliEuler.euler_inversion`](DLMF/BernoulliEuler/Recurrences.lean#L344) (proved). Both directions of the inversion stated for sequences in ℂ.

## [§24.6 Explicit Formulas](https://dlmf.nist.gov/24.6)

- [24.6.E1](https://dlmf.nist.gov/24.6.E1): [`DLMF.BernoulliEuler.bernoulli_two_mul_eq_explicit₁`](DLMF/BernoulliEuler/Explicit.lean#L328) (proved). n ≥ 1.
- [24.6.E2](https://dlmf.nist.gov/24.6.E2): [`DLMF.BernoulliEuler.bernoulli_eq_explicit₂`](DLMF/BernoulliEuler/Explicit.lean#L454) (proved). n ≥ 1.
- [24.6.E3](https://dlmf.nist.gov/24.6.E3): [`DLMF.BernoulliEuler.bernoulli_two_mul_eq_explicit₃`](DLMF/BernoulliEuler/Explicit.lean#L504) (admitted). n ≥ 1.
- [24.6.E4](https://dlmf.nist.gov/24.6.E4): [`DLMF.BernoulliEuler.eulerNumber_two_mul_eq_explicit₄`](DLMF/BernoulliEuler/Explicit.lean#L669) (proved). n ≥ 1.
- [24.6.E5](https://dlmf.nist.gov/24.6.E5): [`DLMF.BernoulliEuler.eulerNumber_two_mul_eq_explicit₅`](DLMF/BernoulliEuler/Explicit.lean#L695) (proved). n ≥ 1.
- [24.6.E6](https://dlmf.nist.gov/24.6.E6): [`DLMF.BernoulliEuler.eulerNumber_two_mul_eq_explicit₆`](DLMF/BernoulliEuler/Explicit.lean#L907) (proved). n ≥ 1.
- [24.6.E7](https://dlmf.nist.gov/24.6.E7): [`DLMF.BernoulliEuler.bernoulliPolyB_eq_explicit`](DLMF/BernoulliEuler/Explicit.lean#L916) (proved). All n, complex x.
- [24.6.E8](https://dlmf.nist.gov/24.6.E8): [`DLMF.BernoulliEuler.eulerPolyE_eq_explicit`](DLMF/BernoulliEuler/Explicit.lean#L937) (proved). All n, complex x.
- [24.6.E9](https://dlmf.nist.gov/24.6.E9): [`DLMF.BernoulliEuler.bernoulli_eq_explicit₉`](DLMF/BernoulliEuler/Explicit.lean#L441) (proved). All n (stronger than DLMF, which states n ≥ 1).
- [24.6.E10](https://dlmf.nist.gov/24.6.E10): [`DLMF.BernoulliEuler.eulerNumber_eq_explicit₁₀`](DLMF/BernoulliEuler/Explicit.lean#L978) (proved). All n.
- [24.6.E11](https://dlmf.nist.gov/24.6.E11): [`DLMF.BernoulliEuler.bernoulli_eq_explicit₁₁`](DLMF/BernoulliEuler/Explicit.lean#L999) (proved). n ≥ 1.
- [24.6.E12](https://dlmf.nist.gov/24.6.E12): [`DLMF.BernoulliEuler.eulerNumber_two_mul_eq_explicit₁₂`](DLMF/BernoulliEuler/Explicit.lean#L1037) (proved). All n.

## [§24.7 Integral Representations](https://dlmf.nist.gov/24.7)

- [24.7.E1](https://dlmf.nist.gov/24.7.E1): [`DLMF.BernoulliEuler.bernoulli_two_mul_eq_integral_exp_add_one`](DLMF/BernoulliEuler/Integrals.lean#L230) (proved). n ≥ 1; both integral forms.
- [24.7.E2](https://dlmf.nist.gov/24.7.E2): [`DLMF.BernoulliEuler.bernoulli_two_mul_eq_integral_exp_sub_one`](DLMF/BernoulliEuler/Integrals.lean#L275) (proved). n ≥ 1; both integral forms.
- [24.7.E3](https://dlmf.nist.gov/24.7.E3): [`DLMF.BernoulliEuler.bernoulli_two_mul_eq_integral_sech_sq`](DLMF/BernoulliEuler/Integrals.lean#L397) (proved). n ≥ 1.
- [24.7.E4](https://dlmf.nist.gov/24.7.E4): [`DLMF.BernoulliEuler.bernoulli_two_mul_eq_integral_csch_sq`](DLMF/BernoulliEuler/Integrals.lean#L440) (proved). n ≥ 1.
- [24.7.E5](https://dlmf.nist.gov/24.7.E5): [`DLMF.BernoulliEuler.bernoulli_two_mul_eq_integral_log`](DLMF/BernoulliEuler/Integrals.lean#L468) (proved). n ≥ 1.
- [24.7.E6](https://dlmf.nist.gov/24.7.E6): [`DLMF.BernoulliEuler.eulerNumber_two_mul_eq_integral_sech`](DLMF/BernoulliEuler/Integrals.lean#L503) (proved). All n ≥ 0.
- [24.7.E7](https://dlmf.nist.gov/24.7.E7): [`DLMF.BernoulliEuler.bernoulliPolyB_two_mul_eq_integral`](DLMF/BernoulliEuler/Integrals.lean#L565) (admitted). n ≥ 1, complex x with 0 < Re x < 1.
- [24.7.E8](https://dlmf.nist.gov/24.7.E8): [`DLMF.BernoulliEuler.bernoulliPolyB_two_mul_add_one_eq_integral`](DLMF/BernoulliEuler/Integrals.lean#L575) (admitted). n ≥ 0, complex x with 0 < Re x < 1.
- [24.7.E9](https://dlmf.nist.gov/24.7.E9): [`DLMF.BernoulliEuler.eulerPolyE_two_mul_eq_integral`](DLMF/BernoulliEuler/Integrals.lean#L585) (admitted). n ≥ 0, complex x with 0 < Re x < 1.
- [24.7.E10](https://dlmf.nist.gov/24.7.E10): [`DLMF.BernoulliEuler.eulerPolyE_two_mul_add_one_eq_integral`](DLMF/BernoulliEuler/Integrals.lean#L594) (admitted). n ≥ 0, complex x with 0 < Re x < 1.
- [24.7.E11](https://dlmf.nist.gov/24.7.E11): [`DLMF.BernoulliEuler.bernoulliPolyB_eq_mellinBarnes`](DLMF/BernoulliEuler/Integrals.lean#L604) (admitted). Along t = -c + is, 0 < c < 1; holds for every complex x (checked numerically).

## [§24.8 Series Expansions](https://dlmf.nist.gov/24.8)

- [24.8.E1](https://dlmf.nist.gov/24.8.E1): Mathlib: [`hasSum_one_div_nat_pow_mul_cos`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=hasSum_one_div_nat_pow_mul_cos#doc). n ≥ 1, 0 ≤ x ≤ 1, pointer in DLMF/Core/UpstreamElementary.lean.
- [24.8.E2](https://dlmf.nist.gov/24.8.E2): [`DLMF.BernoulliEuler.tendsto_sum_sin_div_eq_bernoulliFun_one`](DLMF/BernoulliEuler/Series.lean#L169) (proved); Mathlib: [`hasSum_one_div_nat_pow_mul_sin`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=hasSum_one_div_nat_pow_mul_sin#doc). n ≥ 1 is the Mathlib pointer (in DLMF/Core/UpstreamElementary.lean); the conditionally convergent case n = 0, 0 < x < 1 is acquired as the limit of the natural partial sums.
- [24.8.E3](https://dlmf.nist.gov/24.8.E3): [`DLMF.BernoulliEuler.tendsto_sum_exp_div_eq_bernoulliFun_one`](DLMF/BernoulliEuler/Series.lean#L195) (proved); Mathlib: [`hasSum_one_div_pow_mul_fourier_mul_bernoulliFun`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=hasSum_one_div_pow_mul_fourier_mul_bernoulliFun#doc). n ≥ 2 is the Mathlib pointer (in DLMF/Core/UpstreamElementary.lean); the case n = 1, 0 < x < 1 is acquired as the limit of the symmetric partial sums.
- [24.8.E4](https://dlmf.nist.gov/24.8.E4): [`DLMF.BernoulliEuler.hasSum_sin_odd_eulerFun`](DLMF/BernoulliEuler/Series.lean#L227) (proved). n ≥ 1, 0 ≤ x ≤ 1.
- [24.8.E5](https://dlmf.nist.gov/24.8.E5): [`DLMF.BernoulliEuler.hasSum_cos_odd_eulerFun`](DLMF/BernoulliEuler/Series.lean#L270) (proved). n ≥ 1, 0 ≤ x ≤ 1.
- [24.8.E6](https://dlmf.nist.gov/24.8.E6): [`DLMF.BernoulliEuler.hasSum_bernoulli_four_mul_add_two`](DLMF/BernoulliEuler/Series.lean#L322) (admitted). n ≥ 1.
- [24.8.E7](https://dlmf.nist.gov/24.8.E7): [`DLMF.BernoulliEuler.hasSum_bernoulli_two_mul_alt`](DLMF/BernoulliEuler/Series.lean#L329) (admitted). n ≥ 2.
- [24.8.E8](https://dlmf.nist.gov/24.8.E8): [`DLMF.BernoulliEuler.bernoulli_two_mul_alpha_beta`](DLMF/BernoulliEuler/Series.lean#L338) (admitted). α, β > 0 with αβ = π², n ≥ 2; summability of both series included.
- [24.8.E9](https://dlmf.nist.gov/24.8.E9): [`DLMF.BernoulliEuler.eulerNumber_two_mul_eq_series`](DLMF/BernoulliEuler/Series.lean#L351) (admitted). n ≥ 1; summability of both series included.

## [§24.9 Inequalities](https://dlmf.nist.gov/24.9)

- [24.9.E1](https://dlmf.nist.gov/24.9.E1): [`DLMF.BernoulliEuler.abs_bernoulliFun_two_mul_lt`](DLMF/BernoulliEuler/Inequalities.lean#L33) (proved). n ≥ 1, 0 < x < 1.
- [24.9.E2](https://dlmf.nist.gov/24.9.E2): [`DLMF.BernoulliEuler.abs_bernoulliFun_two_mul_sub_le`](DLMF/BernoulliEuler/Inequalities.lean#L296) (proved). n ≥ 1, 0 ≤ x ≤ 1.
- [24.9.E3](https://dlmf.nist.gov/24.9.E3): [`DLMF.BernoulliEuler.eulerFun_two_mul_bounds`](DLMF/BernoulliEuler/Inequalities.lean#L343) (proved). n ≥ 1, 0 < x < 1/2.
- [24.9.E4](https://dlmf.nist.gov/24.9.E4): [`DLMF.BernoulliEuler.bernoulliFun_two_mul_add_one_bounds`](DLMF/BernoulliEuler/Inequalities.lean#L366) (admitted). n ≥ 2, 0 < x < 1/2 (also true for n = 1 numerically; kept as printed).
- [24.9.E5](https://dlmf.nist.gov/24.9.E5): [`DLMF.BernoulliEuler.eulerFun_two_mul_sub_one_bounds`](DLMF/BernoulliEuler/Inequalities.lean#L374) (proved). n ≥ 1, 0 < x < 1/2.
- [24.9.E6](https://dlmf.nist.gov/24.9.E6): [`DLMF.BernoulliEuler.bernoulli_two_mul_stirling_bounds`](DLMF/BernoulliEuler/Inequalities.lean#L508) (proved). n ≥ 2.
- [24.9.E7](https://dlmf.nist.gov/24.9.E7): [`DLMF.BernoulliEuler.eulerNumber_two_mul_stirling_bounds`](DLMF/BernoulliEuler/Inequalities.lean#L729) (proved). n ≥ 2.
- [24.9.E8](https://dlmf.nist.gov/24.9.E8): [`DLMF.BernoulliEuler.bernoulli_two_mul_zeta_bounds`](DLMF/BernoulliEuler/Inequalities.lean#L591) (proved). n ≥ 1, non-strict as printed (equality in the upper bound at n = 1).
- [24.9.E9](https://dlmf.nist.gov/24.9.E9): [`DLMF.BernoulliEuler.bernoulliIneqBeta`](DLMF/BernoulliEuler/Inequalities.lean#L586) (definition). β = 2 + ln(1 - 6/π²)/ln 2 defined exactly; its decimal value 0.6491… is excluded: numerical.
- [24.9.E10](https://dlmf.nist.gov/24.9.E10): [`DLMF.BernoulliEuler.eulerNumber_two_mul_beta_bounds`](DLMF/BernoulliEuler/Inequalities.lean#L687) (proved). n ≥ 1.

## [§24.10 Arithmetic Properties](https://dlmf.nist.gov/24.10)

- [24.10.i](https://dlmf.nist.gov/24.10.i): [`DLMF.BernoulliEuler.RatModEq`](DLMF/BernoulliEuler/Arithmetic.lean#L43) (definition). Congruence of rationals: M divides the numerator of a - b (`RatModEq`).
- [24.10.E1](https://dlmf.nist.gov/24.10.E1): [`DLMF.BernoulliEuler.bernoulli_two_mul_den_eq_prod`](DLMF/BernoulliEuler/Arithmetic.lean#L62) (proved); Mathlib: [`Bernoulli.vonStaudt_clausen`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Bernoulli.vonStaudt_clausen#doc); Mathlib: [`Bernoulli.dvd_den_bernoulli`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Bernoulli.dvd_den_bernoulli#doc); Mathlib: [`Bernoulli.not_sq_dvd_den_bernoulli`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Bernoulli.not_sq_dvd_den_bernoulli#doc). First assertion is Mathlib's von Staudt–Clausen theorem; the denominator statement (prose) is acquired for n ≥ 1 as `bernoulli_two_mul_den_eq_prod`.
- [24.10.E2](https://dlmf.nist.gov/24.10.E2): [`DLMF.BernoulliEuler.prime_mul_bernoulli_two_mul_modEq`](DLMF/BernoulliEuler/Arithmetic.lean#L78) (admitted). n ≥ 2, ℓ ≥ 1, (p-1)pˡ ∣ 2n.
- [24.10.E3](https://dlmf.nist.gov/24.10.E3): [`DLMF.BernoulliEuler.kummer_congruence`](DLMF/BernoulliEuler/Arithmetic.lean#L87) (admitted). Corrected range m, n ≥ 2 (fails for m = 1 or n = 1).
- [24.10.E4](https://dlmf.nist.gov/24.10.E4): [`DLMF.BernoulliEuler.kummer_congruence_pow`](DLMF/BernoulliEuler/Arithmetic.lean#L95) (admitted). All m, n with the printed congruence conditions, ℓ ≥ 0.
- [24.10.E5](https://dlmf.nist.gov/24.10.E5): [`DLMF.BernoulliEuler.eulerNumber_modEq_add_prime_sub_one`](DLMF/BernoulliEuler/Arithmetic.lean#L145) (proved). p > 2, n ≥ 2 as printed (also true for n = 1, false for n = 0).
- [24.10.E6](https://dlmf.nist.gov/24.10.E6): [`DLMF.BernoulliEuler.eulerNumber_two_mul_modEq_two_pow`](DLMF/BernoulliEuler/Arithmetic.lean#L179) (admitted). All n, ℓ, w with 2ˡ ∣ w.
- [24.10.E7](https://dlmf.nist.gov/24.10.E7): [`DLMF.BernoulliEuler.voronoi_congruence`](DLMF/BernoulliEuler/Arithmetic.lean#L187) (admitted). M ≥ 2, b prime to M, n ≥ 1; N₂ₙ, D₂ₙ are `(bernoulli (2n)).num`, `.den`.
- [24.10.E8](https://dlmf.nist.gov/24.10.E8): [`DLMF.BernoulliEuler.prime_pow_dvd_bernoulli_num`](DLMF/BernoulliEuler/Arithmetic.lean#L200) (admitted). n ≥ 1, ℓ ≥ 1, p - 1 ∤ 2n, pˡ ∣ 2n.
- [24.10.E9](https://dlmf.nist.gov/24.10.E9): [`DLMF.BernoulliEuler.eulerNumber_two_mul_modEq_prime_pow`](DLMF/BernoulliEuler/Arithmetic.lean#L208) (admitted). n ≥ 1, ℓ ≥ 1, (p-1)p^{ℓ-1} ∣ 2n; both cases p ≡ 1, 3 (mod 4).

## Prose, informal and excluded items (part A)

- [§24.1](https://dlmf.nist.gov/24.1): notation and the convention "x real or complex, n ≥ 0"
  (encoded in the statements); the historical remarks on notation (Lucas, Nörlund, Saalschütz,
  Cajori, …) are excluded: bibliographic.
- [24.2.iv](https://dlmf.nist.gov/24.2.iv): Tables 24.2.3–24.2.6 (the numerators and
  denominators of Bₙ, the Euler numbers, and the coefficients of Bₙ(x) and Eₙ(x) for larger n)
  are tabulated values; excluded: numerical. The pointer to §§4.19 and 4.33 is a
  cross-reference (excluded).
- [§24.3](https://dlmf.nist.gov/24.3) (Graphs): excluded: graphics.
- [24.4.viii](https://dlmf.nist.gov/24.4.viii) p2 (Gessel 2003, umbral calculus): excluded:
  bibliographic.
- [24.4.ix](https://dlmf.nist.gov/24.4.ix): pointers to §25.6 and 26.14.11; excluded:
  cross-reference.
- [24.5.iii](https://dlmf.nist.gov/24.5.iii): "each identity implies the other" is encoded by
  stating both directions of 24.5.9 and 24.5.10.
- [§24.6](https://dlmf.nist.gov/24.6), [24.7.i](https://dlmf.nist.gov/24.7.i),
  [24.7.ii](https://dlmf.nist.gov/24.7.ii), [§24.8](https://dlmf.nist.gov/24.8),
  [§24.9](https://dlmf.nist.gov/24.9), [§24.10](https://dlmf.nist.gov/24.10): the range
  conditions in prose are encoded in the hypotheses of the statements.
- [24.7.iii](https://dlmf.nist.gov/24.7.iii) (Compendia: Prudnikov et al., Gradshteyn and
  Ryzhik): excluded: bibliographic.
- [24.9](https://dlmf.nist.gov/24.9): the decimal value β = 0.6491… of 24.9.9 is excluded:
  numerical (the exact definition is acquired).
- [24.10.iii](https://dlmf.nist.gov/24.10.iii) p2 (Porubský 1998): excluded: bibliographic.

## Validation (part A)

- `lake build` of `DLMF.BernoulliEuler.{Basic, GeneratingFunctions, Properties, Recurrences,
  Explicit, Integrals, Series, Inequalities, Arithmetic, MathlibCoverage}` succeeds; the strict
  check `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` of every changed file
  reports no errors and no warnings other than `declaration uses 'sorry'`.
- Admissions (`grep -c '\bsorry\b'`): Basic 0, GeneratingFunctions 1, Properties 5,
  Recurrences 5, Explicit 12, Integrals 11, Series 8, Inequalities 9, Arithmetic 9 (60). No
  definition or helper declaration (prefix `b24a_`) contains `sorry`; no axioms, no
  `native_decide`.
- `#print axioms` on all 83 proved theorems of part A (tagged theorems and helper lemmas):
  every one depends only on `[propext, Classical.choice, Quot.sound]`.

## Numbered formulas and prose items (part B: §§24.11–24.16)

Part B was acquired by ACQ24B on 2026-10-25 (DLMF version 1.2.8). Modules, in import order:
`DLMF.BernoulliEuler.{Asymptotics, Zeros, IntegralsSums, RelatedNumbers, Generalizations,
MathlibCoverageB}` (`Asymptotics` and `Generalizations` import part A's `DLMF.BernoulliEuler.Basic`
for the complex evaluations `bernoulliPolyB`, `eulerPolyE` and the Appell property). Helper prefix
`b24b_`.

Counts: 65 numbered equations and Table 24.15.1 in scope (24.11: 6, 24.12: 11, 24.13: 11,
24.14: 12, 24.15: 12 + T1, 24.16: 13), all covered (24.13.E1 by the existing Mathlib pointer,
24.13.E2 by a stronger local theorem in addition to the pointer); none is numerical. 105 tagged
declarations: 17 definitions, 37 proved theorems (one of them, 24.14.2, from the admitted 24.14.1)
and 51 direct admissions (`grep -c '\bsorry\b'`: Asymptotics 4, Zeros 16, IntegralsSums 13,
RelatedNumbers 7, Generalizations 11, MathlibCoverageB 0). Nine new `dlmf_upstream` pointers in
`MathlibCoverageB.lean` (24.12.i ×2, 24.15.iii ×2, 24.15.iv ×2, 24.16.ii ×3).

Conventions of part B:

- `Bₙ = bernoulli n` (Mathlib, `B₁ = -1/2`), `Bₙ(x)` = `Polynomial.bernoulli n`, on `ℝ`
  `bernoulliFun n`, on `ℂ` `bernoulliPolyB n` (part A); `Eₙ = eulerNumber n`, `Eₙ(x)` =
  `Polynomial.euler n`, `eulerFun n`, `eulerPolyE n`.
- 24.11: `~` is `Asymptotics.IsEquivalent atTop`; the uniform limits 24.11.5–24.11.6 are
  `TendstoUniformlyOn` on every compact `K ⊆ ℂ`, split into even and odd `n`. 24.11.1–24.11.4 are
  proved (via `ζ(2n)`, Dirichlet's `β(2n+1)`, `LSeries.tendsto_atTop` and Stirling's formula).
- 24.12: the ordered zeros `x_j^{(n)}`, `y_j^{(n)}` in `[1/2, ∞)` are the sorted real root
  multisets (`bernoulliRealZero n j`, `eulerRealZero n j`, 1-based, totalized by `0`); `R(n)` is
  `bernoulliRealZeroCount`. Limits "as `n → ∞` with `m` fixed" for even/odd `n` are along
  `n = 2k`, `n = 2k + 1`. "No multiple zeros" is `Polynomial.Separable`.
- 24.13: real integrals over `[a, b]` (`intervalIntegral`); indefinite integrals as `HasDerivAt`.
- 24.14: polynomial identities in an arbitrary commutative `ℚ`-algebra via `aeval`;
  `antidiagonalTuple` index sets; `(n+1) × (n+1)` Hankel matrices on `Fin (n + 1)`.
- 24.15: DLMF's signed `s(n, m)` written as `(-1)^{n-m}` times Mathlib's unsigned
  `Nat.stirlingFirst`; `S(n, m) = Nat.stirlingSecond`; congruences between rationals as
  `padicNorm p (a - b) ≤ p^{-k}`; `uₙ = Nat.fib n`, `vₙ = lucasNumber n` (new).
- 24.16: genuine finite definitions (module docstring of `Generalizations.lean`): Nörlund
  polynomials as polynomials in the order through `descPochhammer` and `bernoulliPowerSeries`,
  `bₙ` as `∫₀¹ (x choose n) dx`, `βₙ(λ)` as polynomials in `λ` through `PowerSeries.invOfUnit`,
  `B_{n,χ}` by the closed form `f^{n-1} ∑ χ(a) Bₙ(a/f)` (for every `χ` modulo `f ≥ 1`). The
  definitions were checked against the DLMF generating functions with sympy (orders `ℓ ≤ 3`,
  `n ≤ 8`; `χ₀`, `χ₄`), and `B_n^{(1)} = Bₙ` is proved (`bernoulliNumberOrder_one`).
- No DLMF errata were found in §§24.11–24.16: every numbered formula was checked before it was
  stated (sympy exact arithmetic for the finite identities, integrals, congruences (primes
  `p < 40`), Hankel determinants (`n ≤ 5`) and generating-function coefficients; mpmath for the
  asymptotics and the zero bounds). Domain qualifications, not errata: 24.14.10 needs positive
  `j, k, ℓ, m` as printed (it fails for nonnegative indices); in 24.16.9 the principal complex
  power is DLMF's branch only for `|t|` below about 4.8 (`t/(eᵗ-1)` crosses the negative axis
  inside `|t| < 2π`), so the complex statement is made for `‖t‖ < π` and a real statement for
  `|t| < 2π`.

## [§24.11 Asymptotic Approximations](https://dlmf.nist.gov/24.11)

- [24.11.E1](https://dlmf.nist.gov/24.11.E1): [`DLMF.BernoulliEuler.bernoulli_two_mul_isEquivalent`](DLMF/BernoulliEuler/Asymptotics.lean#L53) (proved)
- [24.11.E2](https://dlmf.nist.gov/24.11.E2): [`DLMF.BernoulliEuler.bernoulli_two_mul_isEquivalent_stirling`](DLMF/BernoulliEuler/Asymptotics.lean#L85) (proved)
- [24.11.E3](https://dlmf.nist.gov/24.11.E3): [`DLMF.BernoulliEuler.eulerNumber_two_mul_isEquivalent`](DLMF/BernoulliEuler/Asymptotics.lean#L108) (proved)
- [24.11.E4](https://dlmf.nist.gov/24.11.E4): [`DLMF.BernoulliEuler.eulerNumber_two_mul_isEquivalent_stirling`](DLMF/BernoulliEuler/Asymptotics.lean#L148) (proved)
- [24.11.E5](https://dlmf.nist.gov/24.11.E5): [`DLMF.BernoulliEuler.tendstoUniformlyOn_bernoulli_even`](DLMF/BernoulliEuler/Asymptotics.lean#L492) (proved); [`DLMF.BernoulliEuler.tendstoUniformlyOn_bernoulli_odd`](DLMF/BernoulliEuler/Asymptotics.lean#L504) (proved). Proof route: the generating function has its nearest poles at `±2πi`; the normalized polynomials are the residue contribution.
- [24.11.E6](https://dlmf.nist.gov/24.11.E6): [`DLMF.BernoulliEuler.tendstoUniformlyOn_euler_even`](DLMF/BernoulliEuler/Asymptotics.lean#L517) (proved); [`DLMF.BernoulliEuler.tendstoUniformlyOn_euler_odd`](DLMF/BernoulliEuler/Asymptotics.lean#L556) (proved)

Analytical prose:

- [24.11.p1](https://dlmf.nist.gov/24.11#p1): Introduces 24.11.1–24.11.4 ("as `n → ∞`"); the limits are `Asymptotics.IsEquivalent` along `atTop` on `ℕ`.
- [24.11.p2](https://dlmf.nist.gov/24.11#p2): Introduces 24.11.5–24.11.6; "uniformly for `x` on compact subsets of `ℂ`" is `TendstoUniformlyOn` on every compact `K ⊆ ℂ`, and the parity case split is acquired as separate even/odd limits (`n = 2m`, `n = 2m + 1`). The sign exponents `⌊n/2⌋ - 1`, `⌊(n+1)/2⌋` are evaluated exactly (in `ℤ`).
- [24.11.p3](https://dlmf.nist.gov/24.11#p3): Bibliographic pointer (Temme 1995b, López and Temme 1999c); no formula stated.

## [§24.12 Zeros](https://dlmf.nist.gov/24.12)

- [24.12.E1](https://dlmf.nist.gov/24.12.E1): [`DLMF.BernoulliEuler.bernoulliRealZerosGE`](DLMF/BernoulliEuler/Zeros.lean#L78) (definition); [`DLMF.BernoulliEuler.bernoulliRealZero`](DLMF/BernoulliEuler/Zeros.lean#L84) (definition); [`DLMF.BernoulliEuler.bernoulliRealZerosGE_sorted`](DLMF/BernoulliEuler/Zeros.lean#L126) (proved); [`DLMF.BernoulliEuler.mem_bernoulliRealZerosGE`](DLMF/BernoulliEuler/Zeros.lean#L131) (proved). Sorted with multiplicity; see 24.12.i.p2.
- [24.12.E2](https://dlmf.nist.gov/24.12.E2): [`DLMF.BernoulliEuler.bernoulliRealZero_one_bounds`](DLMF/BernoulliEuler/Zeros.lean#L803) (proved)
- [24.12.E3](https://dlmf.nist.gov/24.12.E3): [`DLMF.BernoulliEuler.bernoulliRealZero_one_sub_isEquivalent`](DLMF/BernoulliEuler/Zeros.lean#L823) (proved)
- [24.12.E4](https://dlmf.nist.gov/24.12.E4): [`DLMF.BernoulliEuler.tendsto_bernoulliRealZero_even`](DLMF/BernoulliEuler/Zeros.lean#L1535) (proved)
- [24.12.E5](https://dlmf.nist.gov/24.12.E5): [`DLMF.BernoulliEuler.tendsto_bernoulliRealZero_odd`](DLMF/BernoulliEuler/Zeros.lean#L1602) (proved)
- [24.12.E6](https://dlmf.nist.gov/24.12.E6): [`DLMF.BernoulliEuler.bernoulliRealZeroCount_isEquivalent`](DLMF/BernoulliEuler/Zeros.lean#L1668) (admitted)
- [24.12.E7](https://dlmf.nist.gov/24.12.E7): [`DLMF.BernoulliEuler.eulerRealZerosGE`](DLMF/BernoulliEuler/Zeros.lean#L94) (definition); [`DLMF.BernoulliEuler.eulerRealZero`](DLMF/BernoulliEuler/Zeros.lean#L100) (definition); [`DLMF.BernoulliEuler.eulerRealZerosGE_sorted`](DLMF/BernoulliEuler/Zeros.lean#L150) (proved); [`DLMF.BernoulliEuler.mem_eulerRealZerosGE`](DLMF/BernoulliEuler/Zeros.lean#L155) (proved)
- [24.12.E8](https://dlmf.nist.gov/24.12.E8): [`DLMF.BernoulliEuler.tendsto_eulerRealZero_even`](DLMF/BernoulliEuler/Zeros.lean#L1691) (proved)
- [24.12.E9](https://dlmf.nist.gov/24.12.E9): [`DLMF.BernoulliEuler.eulerRealZero_two_bounds_three`](DLMF/BernoulliEuler/Zeros.lean#L1949) (proved). Checked numerically (mpmath roots) for `n ≤ 39`.
- [24.12.E10](https://dlmf.nist.gov/24.12.E10): [`DLMF.BernoulliEuler.eulerRealZero_two_bounds_one`](DLMF/BernoulliEuler/Zeros.lean#L2011) (proved). Checked numerically for `n ≤ 37`.
- [24.12.E11](https://dlmf.nist.gov/24.12.E11): [`DLMF.BernoulliEuler.tendsto_eulerRealZero_odd`](DLMF/BernoulliEuler/Zeros.lean#L2087) (proved)

Analytical prose:

- [24.12.i.p1](https://dlmf.nist.gov/24.12#i.p1): `bernoulliFun_odd_zeros_Icc` (admitted): for `n ≥ 1` the zero set of `B₂ₙ₊₁` in `[0, 1]` is `{0, 1/2, 1}`; `bernoulliFun_even_sub_zeros_Icc` (admitted): the zero set of `B₂ₙ(x) - B₂ₙ` in `[0, 1]` is `{0, 1}`. Both checked exactly (sympy root isolation) for `2n + 1 ≤ 23` and `2n ≤ 24`.
- [24.12.i.p2](https://dlmf.nist.gov/24.12#i.p2): The zeros `x_j^{(n)}` in `[1/2, ∞)` (24.12.1) are the sorted multiset of real roots, `bernoulliRealZerosGE`/`bernoulliRealZero` (1-based `j`; totalized value `0` past the last zero), with `bernoulliRealZerosGE_sorted` and `mem_bernoulliRealZerosGE` (proved); the statement that the zeros in `(-∞, 1/2]` are the `1 - x_j^{(n)}` is `bernoulliFun_eq_zero_iff_of_le_half` (proved, from the reflection formula).
- [24.12.i.p3](https://dlmf.nist.gov/24.12#i.p3): Hypotheses of 24.12.2–24.12.4 (`n ≥ 2` even; `m ≥ 1` fixed); "as `n → ∞`" through even `n` is `n = 2k`, `k → ∞`.
- [24.12.i.p4](https://dlmf.nist.gov/24.12#i.p4): `bernoulliRealZero_one_of_odd` (proved: `x_1^{(n)} = 1/2` for odd `n`, also `n = 1`) and `bernoulliRealZero_two_of_odd` (admitted: `x_2^{(n)} = 1`, `n ≥ 3` odd); the limits 24.12.5 through odd `n = 2k + 1`.
- [24.12.i.p5](https://dlmf.nist.gov/24.12#i.p5): `bernoulliRealZeroCount` is `R(n)` (number of real zeros with multiplicity; the zeros are simple by §24.12(iv)); `R(n) = n` for `1 ≤ n ≤ 5` is `bernoulliRealZeroCount_eq_self` (admitted; checked exactly). 24.12.6 follows.
- [24.12.ii.p1](https://dlmf.nist.gov/24.12#ii.p1): The zeros `y_j^{(n)}` of `Eₙ` in `[1/2, ∞)` (24.12.7), `eulerRealZerosGE`/`eulerRealZero`, and the reflection statement for `(-∞, 1/2]`, `eulerFun_eq_zero_iff_of_le_half` (proved).
- [24.12.ii.p2](https://dlmf.nist.gov/24.12#ii.p2): `eulerRealZero_one_of_even` (admitted): `y_1^{(n)} = 1` for even `n ≥ 2`; introduces 24.12.8 (through even `n`).
- [24.12.ii.p3](https://dlmf.nist.gov/24.12#ii.p3): `eulerRealZero_one_of_odd` (proved): `y_1^{(n)} = 1/2` for odd `n`; introduces 24.12.9–24.12.11 (24.12.9 for `n ≡ 3 (mod 4)`, 24.12.10 for `n ≡ 1 (mod 4)`, `n ≥ 5`; 24.12.11 through odd `n`).
- [24.12.iii.p1](https://dlmf.nist.gov/24.12#iii.p1): Bibliographic pointers (complex zeros: Delange, Dilcher; irreducibility: Dilcher, Kimura, Adelberg); no formula stated.
- [24.12.iv.p1](https://dlmf.nist.gov/24.12#iv.p1): `bernoulli_separable` (admitted; Brillhart): `Bₙ` has no multiple zeros, stated as `Polynomial.Separable` over `ℚ` for all `n ≥ 0` (stronger than DLMF's `n ≥ 1`); `euler_five` (proved): `E₅(x) = (x - 1/2)(x² - x - 1)²`; `euler_separable_iff` (admitted): `Eₙ` is separable iff `n ≠ 5`. Checked with sympy square-free factorization for `n ≤ 24`.
- [24.12.i](https://dlmf.nist.gov/24.12.i): [`DLMF.BernoulliEuler.bernoulliRealZeroCount`](DLMF/BernoulliEuler/Zeros.lean#L89) (definition); [`DLMF.BernoulliEuler.bernoulliFun_eq_zero_iff_of_le_half`](DLMF/BernoulliEuler/Zeros.lean#L138) (proved); [`DLMF.BernoulliEuler.bernoulliFun_odd_zeros_Icc`](DLMF/BernoulliEuler/Zeros.lean#L412) (proved); [`DLMF.BernoulliEuler.bernoulliFun_even_sub_zeros_Icc`](DLMF/BernoulliEuler/Zeros.lean#L438) (proved); [`DLMF.BernoulliEuler.bernoulliRealZero_one_of_odd`](DLMF/BernoulliEuler/Zeros.lean#L1547) (proved); [`DLMF.BernoulliEuler.bernoulliRealZero_two_of_odd`](DLMF/BernoulliEuler/Zeros.lean#L1555) (proved); [`DLMF.BernoulliEuler.bernoulliRealZeroCount_eq_self`](DLMF/BernoulliEuler/Zeros.lean#L1614) (proved); Mathlib: [`bernoulliFun_eval_half_eq_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ZetaValues.html#bernoulliFun_eval_half_eq_zero); Mathlib: [`bernoulliFun_endpoints_eq_of_ne_one`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ZetaValues.html#bernoulliFun_endpoints_eq_of_ne_one).
- [24.12.ii](https://dlmf.nist.gov/24.12.ii): [`DLMF.BernoulliEuler.eulerFun_eq_zero_iff_of_le_half`](DLMF/BernoulliEuler/Zeros.lean#L162) (proved); [`DLMF.BernoulliEuler.eulerRealZero_one_of_even`](DLMF/BernoulliEuler/Zeros.lean#L1677) (proved); [`DLMF.BernoulliEuler.eulerRealZero_one_of_odd`](DLMF/BernoulliEuler/Zeros.lean#L1697) (proved).
- [24.12.iv](https://dlmf.nist.gov/24.12.iv): [`DLMF.BernoulliEuler.bernoulli_separable`](DLMF/BernoulliEuler/Zeros.lean#L2100) (admitted); [`DLMF.BernoulliEuler.euler_five`](DLMF/BernoulliEuler/Zeros.lean#L2106) (proved); [`DLMF.BernoulliEuler.euler_separable_iff`](DLMF/BernoulliEuler/Zeros.lean#L2111) (admitted).

## [§24.13 Integrals](https://dlmf.nist.gov/24.13)

- [24.13.E1](https://dlmf.nist.gov/24.13.E1): Mathlib: [`antideriv_bernoulliFun`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=antideriv_bernoulliFun#doc) (exact: real `t`; pointer in `DLMF.Core.UpstreamElementary`)
- [24.13.E2](https://dlmf.nist.gov/24.13.E2): [`DLMF.BernoulliEuler.integral_bernoulliFun_add_one`](DLMF/BernoulliEuler/IntegralsSums.lean#L225) (proved); Mathlib: [`integral_bernoulliFun_eq_zero`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=integral_bernoulliFun_eq_zero#doc) (special case `x = 0`; pointer in `DLMF.Core.UpstreamElementary`). Stated for all `n ≥ 0` and real `x` (stronger than DLMF: `n ≥ 1`).
- [24.13.E3](https://dlmf.nist.gov/24.13.E3): [`DLMF.BernoulliEuler.integral_bernoulliFun_add_half`](DLMF/BernoulliEuler/IntegralsSums.lean#L234) (proved)
- [24.13.E4](https://dlmf.nist.gov/24.13.E4): [`DLMF.BernoulliEuler.integral_bernoulliFun_zero_half`](DLMF/BernoulliEuler/IntegralsSums.lean#L244) (proved)
- [24.13.E5](https://dlmf.nist.gov/24.13.E5): [`DLMF.BernoulliEuler.integral_bernoulliFun_quarter`](DLMF/BernoulliEuler/IntegralsSums.lean#L255) (proved)
- [24.13.E6](https://dlmf.nist.gov/24.13.E6): [`DLMF.BernoulliEuler.integral_bernoulliFun_mul_bernoulliFun`](DLMF/BernoulliEuler/IntegralsSums.lean#L266) (proved)
- [24.13.E7](https://dlmf.nist.gov/24.13.E7): [`DLMF.BernoulliEuler.hasDerivAt_eulerFun_succ_div`](DLMF/BernoulliEuler/IntegralsSums.lean#L282) (proved)
- [24.13.E8](https://dlmf.nist.gov/24.13.E8): [`DLMF.BernoulliEuler.integral_eulerFun_zero_one`](DLMF/BernoulliEuler/IntegralsSums.lean#L288) (proved). Both equalities.
- [24.13.E9](https://dlmf.nist.gov/24.13.E9): [`DLMF.BernoulliEuler.integral_eulerFun_even_zero_half`](DLMF/BernoulliEuler/IntegralsSums.lean#L304) (proved). Both equalities.
- [24.13.E10](https://dlmf.nist.gov/24.13.E10): [`DLMF.BernoulliEuler.integral_eulerFun_odd_zero_half`](DLMF/BernoulliEuler/IntegralsSums.lean#L324) (proved)
- [24.13.E11](https://dlmf.nist.gov/24.13.E11): [`DLMF.BernoulliEuler.integral_eulerFun_mul_eulerFun`](DLMF/BernoulliEuler/IntegralsSums.lean#L339) (proved)

Analytical prose:

- [24.13.i.p1](https://dlmf.nist.gov/24.13#i.p1): Introduces 24.13.1–24.13.5 (real integrals; DLMF's indefinite integral 24.13.1 is an antiderivative statement).
- [24.13.i.p2](https://dlmf.nist.gov/24.13#i.p2): Hypothesis `m, n ≥ 1` of 24.13.6.
- [24.13.i.p3](https://dlmf.nist.gov/24.13#i.p3): Bibliographic pointer (Agoh and Dilcher 2011) for `∫₀ˣ BₙBₘ` and triple products; no formula stated.
- [24.13.ii.p1](https://dlmf.nist.gov/24.13#ii.p1): Introduces 24.13.7–24.13.10.
- [24.13.ii.p2](https://dlmf.nist.gov/24.13#ii.p2): Hypothesis `m, n ≥ 1` of 24.13.11.
- [24.13.iii.p1](https://dlmf.nist.gov/24.13#iii.p1): Bibliographic pointer (Prudnikov et al.: Laplace transforms and other integrals); no formula stated.

## [§24.14 Sums](https://dlmf.nist.gov/24.14)

- [24.14.E1](https://dlmf.nist.gov/24.14.E1): [`DLMF.BernoulliEuler.sum_choose_bernoulli_mul_bernoulli`](DLMF/BernoulliEuler/IntegralsSums.lean#L514) (proved). Arbitrary commutative `ℚ`-algebra; the `n B_{n-1}` term is `n • B_{n-1}`.
- [24.14.E2](https://dlmf.nist.gov/24.14.E2): [`DLMF.BernoulliEuler.sum_choose_bernoulli_mul_bernoulli_number`](DLMF/BernoulliEuler/IntegralsSums.lean#L251) (proved from the admitted sum_choose_bernoulli_mul_bernoulli (24.14.1))
- [24.14.E3](https://dlmf.nist.gov/24.14.E3): [`DLMF.BernoulliEuler.sum_choose_euler_mul_euler`](DLMF/BernoulliEuler/IntegralsSums.lean#L568) (proved)
- [24.14.E4](https://dlmf.nist.gov/24.14.E4): [`DLMF.BernoulliEuler.sum_choose_eulerNumber_mul_eulerNumber`](DLMF/BernoulliEuler/IntegralsSums.lean#L613) (proved); [`DLMF.BernoulliEuler.neg_two_pow_mul_euler_eval_zero`](DLMF/BernoulliEuler/IntegralsSums.lean#L632) (proved). First equality admitted (it follows from 24.14.3 at `x = h = 1/2`), second equality proved.
- [24.14.E5](https://dlmf.nist.gov/24.14.E5): [`DLMF.BernoulliEuler.sum_choose_euler_mul_bernoulli`](DLMF/BernoulliEuler/IntegralsSums.lean#L650) (proved). `(x+h)/2` written `(2⁻¹ : ℚ) • (x + h)`.
- [24.14.E6](https://dlmf.nist.gov/24.14.E6): [`DLMF.BernoulliEuler.sum_choose_two_pow_bernoulli_mul_eulerNumber`](DLMF/BernoulliEuler/IntegralsSums.lean#L693) (proved). `2^{n-1}` written `2ⁿ/2` (value `1/2` at `n = 0`).
- [24.14.E7](https://dlmf.nist.gov/24.14.E7): [`DLMF.BernoulliEuler.sum_choose_mul_bernoulli_mul_bernoulli_div`](DLMF/BernoulliEuler/IntegralsSums.lean#L746) (proved)
- [24.14.E8](https://dlmf.nist.gov/24.14.E8): [`DLMF.BernoulliEuler.sum_antidiagonal_bernoulli_triple`](DLMF/BernoulliEuler/IntegralsSums.lean#L930) (proved)
- [24.14.E9](https://dlmf.nist.gov/24.14.E9): [`DLMF.BernoulliEuler.sum_antidiagonal_eulerNumber_triple`](DLMF/BernoulliEuler/IntegralsSums.lean#L1000) (proved)
- [24.14.E10](https://dlmf.nist.gov/24.14.E10): [`DLMF.BernoulliEuler.sum_antidiagonal_bernoulli_quadruple`](DLMF/BernoulliEuler/IntegralsSums.lean#L1052) (proved)
- [24.14.E11](https://dlmf.nist.gov/24.14.E11): [`DLMF.BernoulliEuler.det_hankel_bernoulli`](DLMF/BernoulliEuler/IntegralsSums.lean#L1178) (admitted)
- [24.14.E12](https://dlmf.nist.gov/24.14.E12): [`DLMF.BernoulliEuler.det_hankel_eulerNumber`](DLMF/BernoulliEuler/IntegralsSums.lean#L1187) (admitted)

Analytical prose:

- [24.14.i.p1](https://dlmf.nist.gov/24.14#i.p1): Introduces 24.14.1–24.14.6; the polynomial identities are stated in an arbitrary commutative `ℚ`-algebra.
- [24.14.i.p2](https://dlmf.nist.gov/24.14#i.p2): Hypotheses of 24.14.7 (`m + n` even, `m, n ≥ 1`).
- [24.14.ii.p1](https://dlmf.nist.gov/24.14#ii.p1): Hypothesis `n ≥ 2` and the index set `j + k + ℓ = n` (`Finset.Nat.antidiagonalTuple 3 n`) of 24.14.8–24.14.9.
- [24.14.ii.p2](https://dlmf.nist.gov/24.14#ii.p2): Hypothesis `n ≥ 4` and the index set of positive `j + k + ℓ + m = n` (filtered `antidiagonalTuple 4 n`) of 24.14.10; checked: the identity holds for positive indices (and fails if zero indices are allowed).
- [24.14.ii.p3](https://dlmf.nist.gov/24.14#ii.p3): Definition of the `(n+1) × (n+1)` Hankel determinant `det[a_{r+s}]`, `r, s = 0, …, n` (`Matrix.of` on `Fin (n + 1)`); the bibliographic pointer (Al-Salam and Carlitz 1959) is commentary.
- [24.14.ii.p4](https://dlmf.nist.gov/24.14#ii.p4): Bibliographic pointer (Sachse 1882); no formula stated.
- [24.14.iii.p1](https://dlmf.nist.gov/24.14#iii.p1): Bibliographic pointer (Hansen 1975, Prudnikov et al. 1990); no formula stated.

## [§24.15 Related Sequences of Numbers](https://dlmf.nist.gov/24.15)

- [24.15.E1](https://dlmf.nist.gov/24.15.E1): [`DLMF.BernoulliEuler.hasSum_genocchiNumber`](DLMF/BernoulliEuler/RelatedNumbers.lean#L78) (proved). Proved for complex `‖t‖ < π` (also at `t = 0`), from the Bernoulli generating function at `t` and `2t`.
- [24.15.E2](https://dlmf.nist.gov/24.15.E2): [`DLMF.BernoulliEuler.genocchiNumber`](DLMF/BernoulliEuler/RelatedNumbers.lean#L58) (definition); [`DLMF.BernoulliEuler.genocchiNumber_eq`](DLMF/BernoulliEuler/RelatedNumbers.lean#L63) (proved)
- [24.15.E3](https://dlmf.nist.gov/24.15.E3): [`DLMF.BernoulliEuler.hasSum_tangentNumber`](DLMF/BernoulliEuler/RelatedNumbers.lean#L134) (proved). Proved for complex `‖t‖ < π/2` (also at `t = 0`), from the tangent Taylor series `hasSum_pi_mul_tan_bernoulli`.
- [24.15.E4](https://dlmf.nist.gov/24.15.E4): [`DLMF.BernoulliEuler.tangentNumber`](DLMF/BernoulliEuler/RelatedNumbers.lean#L107) (definition); [`DLMF.BernoulliEuler.tangentNumber_odd`](DLMF/BernoulliEuler/RelatedNumbers.lean#L115) (proved)
- [24.15.E5](https://dlmf.nist.gov/24.15.E5): [`DLMF.BernoulliEuler.tangentNumber_even`](DLMF/BernoulliEuler/RelatedNumbers.lean#L129) (proved)
- [24.15.T1](https://dlmf.nist.gov/24.15.T1): [`DLMF.BernoulliEuler.genocchiNumber_table`](DLMF/BernoulliEuler/RelatedNumbers.lean#L202) (proved); [`DLMF.BernoulliEuler.tangentNumber_table`](DLMF/BernoulliEuler/RelatedNumbers.lean#L212) (proved). Exact integer table (`G₀ … G₈`, `T₀ … T₈`), proved from the exact values `B₀ … B₉` (helper `b24b_bernoulli_values`).
- [24.15.E6](https://dlmf.nist.gov/24.15.E6): [`DLMF.BernoulliEuler.bernoulli_eq_sum_stirlingSecond`](DLMF/BernoulliEuler/RelatedNumbers.lean#L333) (proved)
- [24.15.E7](https://dlmf.nist.gov/24.15.E7): [`DLMF.BernoulliEuler.bernoulli_eq_sum_stirlingSecond_choose`](DLMF/BernoulliEuler/RelatedNumbers.lean#L370) (proved)
- [24.15.E8](https://dlmf.nist.gov/24.15.E8): [`DLMF.BernoulliEuler.sum_stirlingFirst_mul_bernoulli`](DLMF/BernoulliEuler/RelatedNumbers.lean#L427) (proved). Signed `s(n+1, k+1)` written as `(-1)^{n-k} |s(n+1, k+1)|`.
- [24.15.E9](https://dlmf.nist.gov/24.15.E9): [`DLMF.BernoulliEuler.padicNorm_bernoulli_sub_stirlingSecond`](DLMF/BernoulliEuler/RelatedNumbers.lean#L437) (admitted). Congruence in `ℤ_(p)` stated as `padicNorm p (a - b) ≤ p^{-2}`; checked for all primes `p < 40`.
- [24.15.E10](https://dlmf.nist.gov/24.15.E10): [`DLMF.BernoulliEuler.padicNorm_bernoulli_sub_stirlingSecond_cube`](DLMF/BernoulliEuler/RelatedNumbers.lean#L446) (admitted). Congruence stated as `padicNorm p (a - b) ≤ p^{-3}`; checked for all primes `p < 40`.
- [24.15.E11](https://dlmf.nist.gov/24.15.E11): [`DLMF.BernoulliEuler.sum_choose_bernoulli_fib`](DLMF/BernoulliEuler/RelatedNumbers.lean#L576) (proved)
- [24.15.E12](https://dlmf.nist.gov/24.15.E12): [`DLMF.BernoulliEuler.sum_choose_eulerNumber_lucas`](DLMF/BernoulliEuler/RelatedNumbers.lean#L665) (proved)

Analytical prose:

- [24.15.i.p1](https://dlmf.nist.gov/24.15#i.p1): Introduces the Genocchi numbers (24.15.1–24.15.2); `genocchiNumber` is defined by the closed form 24.15.2 and the generating function 24.15.1 is proved.
- [24.15.i.p2](https://dlmf.nist.gov/24.15#i.p2): Pointer to Table 24.15.1 (acquired as 24.15.T1).
- [24.15.ii.p1](https://dlmf.nist.gov/24.15#ii.p1): Introduces the tangent numbers (24.15.3–24.15.5); `tangentNumber` is defined by the closed forms 24.15.4–24.15.5 and the generating function 24.15.3 is proved.
- [24.15.iii.p1](https://dlmf.nist.gov/24.15#iii.p1): DLMF's Stirling numbers `s(n, m)`, `S(n, m)` of §26.8(i): Mathlib's `Nat.stirlingSecond` (exact) and `Nat.stirlingFirst` (unsigned; DLMF's signed `s(n, m) = (-1)^{n-m} |s(n, m)|` is written out); pointers in `MathlibCoverageB`.
- [24.15.iii.p2](https://dlmf.nist.gov/24.15#iii.p2): `p` denotes a prime in 24.15.9–24.15.10 (hypothesis `p.Prime`); the congruences between rationals are stated with `padicNorm p`; the reference (Horata 1991) is bibliographic.
- [24.15.iv.p1](https://dlmf.nist.gov/24.15#iv.p1): Fibonacci numbers `uₙ` = Mathlib's `Nat.fib` (pointer); the Lucas numbers `vₙ` are `lucasNumber` with `lucasNumber_add_two` and the bridge `lucasNumber_succ : v_{n+1} = u_n + u_{n+2}` (proved).
- [24.15.iv.p2](https://dlmf.nist.gov/24.15#iv.p2): Cross-reference to §26.11; no formula stated.
- [24.15.iv](https://dlmf.nist.gov/24.15.iv): [`DLMF.BernoulliEuler.lucasNumber`](DLMF/BernoulliEuler/RelatedNumbers.lean#L457) (definition); [`DLMF.BernoulliEuler.lucasNumber_add_two`](DLMF/BernoulliEuler/RelatedNumbers.lean#L465) (proved); [`DLMF.BernoulliEuler.lucasNumber_succ`](DLMF/BernoulliEuler/RelatedNumbers.lean#L470) (proved); Mathlib: [`Nat.fib`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Basic.html#Nat.fib); Mathlib: [`Nat.fib_add_two`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Basic.html#Nat.fib_add_two).

## [§24.16 Generalizations](https://dlmf.nist.gov/24.16)

- [24.16.E1](https://dlmf.nist.gov/24.16.E1): [`DLMF.BernoulliEuler.bernoulliOrder`](DLMF/BernoulliEuler/Generalizations.lean#L115) (definition); [`DLMF.BernoulliEuler.hasSum_bernoulliOrder`](DLMF/BernoulliEuler/Generalizations.lean#L249) (proved)
- [24.16.E2](https://dlmf.nist.gov/24.16.E2): [`DLMF.BernoulliEuler.eulerOrder`](DLMF/BernoulliEuler/Generalizations.lean#L143) (definition); [`DLMF.BernoulliEuler.hasSum_eulerOrder`](DLMF/BernoulliEuler/Generalizations.lean#L280) (proved)
- [24.16.E3](https://dlmf.nist.gov/24.16.E3): [`DLMF.BernoulliEuler.bernoulliNumberOrder`](DLMF/BernoulliEuler/Generalizations.lean#L111) (definition); [`DLMF.BernoulliEuler.eulerNumberOrder`](DLMF/BernoulliEuler/Generalizations.lean#L137) (definition); [`DLMF.BernoulliEuler.bernoulliOrder_eval_zero`](DLMF/BernoulliEuler/Generalizations.lean#L312) (proved); [`DLMF.BernoulliEuler.eulerOrder_eval_zero`](DLMF/BernoulliEuler/Generalizations.lean#L322) (proved)
- [24.16.E4](https://dlmf.nist.gov/24.16.E4): [`DLMF.BernoulliEuler.hasSum_log_div_pow`](DLMF/BernoulliEuler/Generalizations.lean#L579) (proved)
- [24.16.E5](https://dlmf.nist.gov/24.16.E5): [`DLMF.BernoulliEuler.bernoulliSecondKind`](DLMF/BernoulliEuler/Generalizations.lean#L618) (definition); [`DLMF.BernoulliEuler.hasSum_bernoulliSecondKind`](DLMF/BernoulliEuler/Generalizations.lean#L672) (proved)
- [24.16.E6](https://dlmf.nist.gov/24.16.E6): [`DLMF.BernoulliEuler.factorial_mul_bernoulliSecondKind`](DLMF/BernoulliEuler/Generalizations.lean#L722) (proved)
- [24.16.E7](https://dlmf.nist.gov/24.16.E7): [`DLMF.BernoulliEuler.degenerateBernoulli`](DLMF/BernoulliEuler/Generalizations.lean#L756) (definition); [`DLMF.BernoulliEuler.hasSum_degenerateBernoulli`](DLMF/BernoulliEuler/Generalizations.lean#L894) (proved)
- [24.16.E8](https://dlmf.nist.gov/24.16.E8): [`DLMF.BernoulliEuler.degenerateBernoulli_eq`](DLMF/BernoulliEuler/Generalizations.lean#L1329) (proved)
- [24.16.E9](https://dlmf.nist.gov/24.16.E9): [`DLMF.BernoulliEuler.norlundPolynomial`](DLMF/BernoulliEuler/Generalizations.lean#L105) (definition); [`DLMF.BernoulliEuler.hasSum_norlundPolynomial`](DLMF/BernoulliEuler/Generalizations.lean#L1702) (proved); [`DLMF.BernoulliEuler.hasSum_norlundPolynomial_real`](DLMF/BernoulliEuler/Generalizations.lean#L1723) (proved). The complex statement uses the principal power and `0 < ‖t‖ < π` (DLMF: `|t| < 2π`, branch equal to 1 at 0; the principal branch is the analytic one for `|t| ≲ 4.8` numerically); the real statement covers `0 < |t| < 2π`.
- [24.16.E10](https://dlmf.nist.gov/24.16.E10): [`DLMF.BernoulliEuler.bernoulliChar`](DLMF/BernoulliEuler/Generalizations.lean#L1792) (definition); [`DLMF.BernoulliEuler.hasSum_bernoulliChar`](DLMF/BernoulliEuler/Generalizations.lean#L1805) (proved). Definition by the closed form `B_{n,χ} = f^{n-1} ∑_{a=1}^{f} χ(a) Bₙ(a/f)`, generating function admitted (it follows from 24.2.3, ACQ24A's `hasSum_bernoulliPolyB_mul_pow_div`, termwise in `a`); stated for every `χ` modulo `f ≥ 1`.
- [24.16.E11](https://dlmf.nist.gov/24.16.E11): [`DLMF.BernoulliEuler.bernoulliCharPoly`](DLMF/BernoulliEuler/Generalizations.lean#L1800) (definition)
- [24.16.E12](https://dlmf.nist.gov/24.16.E12): [`DLMF.BernoulliEuler.bernoulli_eq_bernoulliCharPoly_one`](DLMF/BernoulliEuler/Generalizations.lean#L1838) (proved). Proved from the Appell property `bernoulliPolyB_add` (ACQ24A).
- [24.16.E13](https://dlmf.nist.gov/24.16.E13): [`DLMF.BernoulliEuler.euler_eq_bernoulliCharPoly_chi4`](DLMF/BernoulliEuler/Generalizations.lean#L1849) (proved). Proved from the Appell property and `euler_eq_bernoulli`.

Analytical prose:

- [24.16.Px1.p1](https://dlmf.nist.gov/24.16#Px1.p1): Definitions 24.16.1–24.16.3 (orders `ℓ = 0, 1, 2, …`) and 24.16.4 (`ℓ ≥ 1`); the pointer to Milne-Thomson and Nörlund is bibliographic. `bernoulliNumberOrder_one` (proved, untagged) checks `B_n^{(1)} = Bₙ`.
- [24.16.Px1.p2](https://dlmf.nist.gov/24.16#Px1.p2): Bibliographic pointer (Temme 1995b, López and Temme 1999b, 2010b) for complex `x, n, ℓ` and uniform asymptotics; no formula stated.
- [24.16.Px2.p1](https://dlmf.nist.gov/24.16#Px2.p1): Definition 24.16.5 of the Bernoulli numbers of the second kind; `bernoulliSecondKind` is the explicit integral `∫₀¹ (x choose n) dx` (written through the coefficients of `descPochhammer`), checked against the series of `t/ln(1+t)` for `n ≤ 8`.
- [24.16.Px2.p2](https://dlmf.nist.gov/24.16#Px2.p2): Hypothesis `n ≥ 2` of 24.16.6.
- [24.16.Px3.p1](https://dlmf.nist.gov/24.16#Px3.p1): "For sufficiently small `|t|`" of 24.16.7 is `∀ᶠ t in 𝓝[≠] 0`; `λ ≠ 0` and the principal power `(1 + λt)^{1/λ}` are hypotheses/conventions; the remark that `s(n, m)` is the Stirling number of the first kind (24.16.8) is a convention.
- [24.16.Px4.p1](https://dlmf.nist.gov/24.16#Px4.p1): 24.16.9 and the assertion that `B_n^{(x)}` is a polynomial in `x` of degree `n`: `norlundPolynomial n : ℚ[X]` is a polynomial by construction and `natDegree_norlundPolynomial` (admitted; leading coefficient `(-1/2)ⁿ`, checked for `n ≤ 8`); consistency with 24.16.3 at `x = ℓ` is `norlundPolynomial_eval_natCast` (proved, by definition).
- [24.16.ii.p1](https://dlmf.nist.gov/24.16#ii.p1): Definitions 24.16.10–24.16.11 for a primitive character `χ` with conductor `f` (Mathlib's `DirichletCharacter.IsPrimitive`, `conductor`; pointers); `χ₀` is the trivial character modulo `1` and `χ₄` is Mathlib's `ZMod.χ₄` composed with `ℤ → ℂ` (`b24b_chi4`); 24.16.12–24.16.13 follow.
- [24.16.ii.p2](https://dlmf.nist.gov/24.16#ii.p2): Bibliographic pointer (Berndt 1975a); no formula stated.
- [24.16.iii.p1](https://dlmf.nist.gov/24.16#iii.p1): List of further generalizations (complex index, `q`-analogs, poly-Bernoulli, `p`-adic, …) with bibliographic pointers only; no formula stated, not formalized.
- [24.16.i](https://dlmf.nist.gov/24.16.i): [`DLMF.BernoulliEuler.natDegree_norlundPolynomial`](DLMF/BernoulliEuler/Generalizations.lean#L1759) (proved); [`DLMF.BernoulliEuler.norlundPolynomial_eval_natCast`](DLMF/BernoulliEuler/Generalizations.lean#L1784) (proved).

## Excluded sections (part B: §§24.17–24.21)

- [§24.17](https://dlmf.nist.gov/24.17) Mathematical Applications (24.17.E1–E8): excluded: application. Purely mathematical content, for a later decision:
  the Euler–Maclaurin formula (24.17.i.Px1.p1, a pointer to §2.10(i); the project has it in
  `DLMFMathlib/Analysis/EulerMaclaurin.lean`); Boole's summation formula 24.17.1 with remainder
  24.17.2 (`0 ≤ h ≤ 1`, `f^{(m)}` absolutely integrable on `[a, n]`; the project has Boole
  summation in `DLMFMathlib/Analysis/BooleSummation.lean`); the Euler splines 24.17.3 and their
  characterization 24.17.4 (unique bounded cardinal spline of degree `n` with `Sₙ(k) = (-1)ᵏ`);
  the Bernoulli monosplines 24.17.5 with `Mₙ(k) = 0` (24.17.6, from 24.4.25 and 24.4.27), the
  uniqueness statement under the growth condition 24.17.7, and the minimal-norm property of
  `B̃ₙ(x) - 2⁻ⁿ Bₙ` (24.17.8). §24.17(iii) (number theory) has pointers only.
- [§24.18](https://dlmf.nist.gov/24.18) Physical Applications: excluded: application (pointers only; no numbered formulas).
- [§24.19](https://dlmf.nist.gov/24.19) Methods of Computation (24.19.E1–E3): excluded: computation. 24.19.1–24.19.2 are recurrences for the computation of `B₂ₙ`, `E₂ₙ` (cf. the recurrences of §24.5, part A), 24.19.3 a congruence algorithm (Tanner–Wagstaff) for `Bₙ mod p`.
- [§24.20](https://dlmf.nist.gov/24.20) Tables: excluded: numerical.
- [§24.21](https://dlmf.nist.gov/24.21) Software: excluded: software (pointers only).

## Validation (part B)

- The six part-B modules build with `lake build` and pass
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` with only `sorry` warnings;
  no axioms, no `native_decide`, no `sorry` in helper declarations (prefix `b24b_`).
- `#print axioms` for `bernoulli_two_mul_isEquivalent`, `eulerNumber_two_mul_isEquivalent_stirling`,
  `euler_five`, `eulerRealZero_one_of_odd`, `integral_bernoulliFun_add_half`,
  `integral_eulerFun_odd_zero_half`, `hasSum_genocchiNumber`, `hasSum_tangentNumber`,
  `tangentNumber_table`, `bernoulliNumberOrder_one`, `bernoulli_eq_bernoulliCharPoly_one`,
  `euler_eq_bernoulliCharPoly_chi4`: `[propext, Classical.choice, Quot.sound]`.
