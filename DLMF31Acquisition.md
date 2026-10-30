# DLMF Chapter 31 acquisition: Heun Functions

> Source paths and current layout notes were refreshed on 2026-10-30; generated per-entry
> statuses follow the compiled ledger refresh. Dated acquisition and proof counts
> describe their original batches.

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 31](https://dlmf.nist.gov/31), §§31.1–31.15, version 1.2.8, checked on
2026-10-26 (agent ACQ31). The applications §§31.16–31.17 and the computation section §31.18
are excluded; the pure mathematics of §31.16 is listed below. The Lean code is in
`DLMF/Heun/` (namespace `DLMF.Heun`, helper prefix `h31_`); the modules, in import order, are
[Basic](DLMF/Heun/Basic.lean) (all definitions),
[Equation](DLMF/Heun/Equation.lean) (§31.2(i)–(iii), (v); 31.10.4),
[LocalSolutions](DLMF/Heun/LocalSolutions.lean) (§31.3),
[HeunFunctions](DLMF/Heun/HeunFunctions.lean) (§§31.4–31.5, 31.9),
[Hypergeometric](DLMF/Heun/Hypergeometric.lean) (§31.7(i), §31.11),
[DoublyPeriodic](DLMF/Heun/DoublyPeriodic.lean) (§31.2(iv), §31.7(ii)),
[Integral](DLMF/Heun/Integral.lean) (§31.8, §31.10),
[Confluent](DLMF/Heun/Confluent.lean) (§31.12) and
[Fuchsian](DLMF/Heun/Fuchsian.lean) (§§31.14–31.15).

**Current layout (2026-10-30).**
`DLMF.Heun.Basic` contains the canonical definitions and uses Mathlib and TauCeti's
continuation definitions. The theorem developments use the foundation and import their
required result APIs explicitly. The hypergeometric and integral developments use the
Riemann-equation API, including the P-symbol operator `riemannNormalOperator`;
`DoublyPeriodic` uses Jacobi special-value and analytic-property
results together with Weierstrass invariant and relation theorems. There are no upstream
Heun-function pointers; Mathlib supplies the Gauss function `ordinaryHypergeometric`.

**Status after proof round 1 (2026-10-26).** Direct admissions in DLMF/Heun fell from 72 to 43. Proved: convergence of Hl and that it solves Heun's equation, the singularities, exponents, normal forms and homographies of §31.2, the local solutions of §31.3 (confirming DLMF's corrected 31.3.10–11), 31.3.13, the confluent forms' singularities and the Jacobi form. The normal form 31.14.3–5 gained the hypothesis that the singular points are distinct after a proved counterexample. Many results are proved only from the flagged existence theorems; see REVIEW.md, "Proof round 1 for Chapters 28–31 (2026-10-26)".

**Status after proof round 2 (2026-10-26).** Direct admissions in DLMF/Heun fell from 43 to 28. Proved: Heun polynomials 31.5.2 and that they solve the equation, 31.4.1 (from the admitted continuation lemma), the reductions 31.7.2–3, §31.7(ii) (Lamé, even and odd), the Fuchsian normal form 31.14.3–5, the Stieltjes equilibrium and critical-point results 31.15.2, 31.15.4, the Hermite–Darboux examples 31.8.4–5, and the kernel identities 31.10.9, 31.10.19 and the corrected 31.10.22–23. 31.11.2 was corrected after a proved counterexample (the errata report (reports/DLMFErrata.tex) (b)) and proved. 31.7.4 was false on the acquired domain (three components; numerical evidence); by user decision it now carries the phase condition |ph(1 − (3/2 − i√3/2)z)| < π/6 selecting the component containing 0 (errata report (b)); still admitted. See REVIEW.md, "Proof round 2 for Chapters 28–31 (2026-10-26)".

**Counts.** §§31.2–31.15 have 110 numbered equations (31.11.E3_1 and 31.11.E3_2 counted
separately); §31.1 is notation only and §31.13 consists of references only. In scope: all
110. Covered: all 110 by project declarations. In addition 11 prose IDs (31.2.i, 31.2.v,
31.3.i, 31.4, 31.5, 31.7.ii, 31.11.iii, 31.11.iv, 31.15.i, 31.15.ii, 31.15.iii) carry tags.
121 DLMF IDs are tagged on 139 declarations. The 168 declarations of `DLMF/Heun/` are 63
definitions (all in `Basic`), 32 proved theorems (of which 8 untagged helpers), 1 theorem
proved from admissions (`heun_lame`) and 72 direct admissions. Excluded: §31.16 and §31.17
(12 numbered equations, excluded: application), §31.18 (excluded: computation).

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Basic](DLMF/Heun/Basic.lean): 0 admissions; 63 definitions.
- [Equation](DLMF/Heun/Equation.lean): 12 admissions; 15 theorems: 3 proved, 12 admitted.
- [LocalSolutions](DLMF/Heun/LocalSolutions.lean): 11 admissions; 16 theorems: 5 proved,
  11 admitted.
- [HeunFunctions](DLMF/Heun/HeunFunctions.lean): 9 admissions; 10 theorems: 1 proved,
  9 admitted.
- [Hypergeometric](DLMF/Heun/Hypergeometric.lean): 10 admissions; 19 theorems: 9 proved,
  10 admitted.
- [DoublyPeriodic](DLMF/Heun/DoublyPeriodic.lean): 4 admissions; 6 theorems: 1 proved,
  1 proved from admissions, 4 admitted.
- [Integral](DLMF/Heun/Integral.lean): 14 admissions; 14 theorems, all admitted.
- [Confluent](DLMF/Heun/Confluent.lean): 3 admissions; 5 theorems: 2 proved, 3 admitted.
- [Fuchsian](DLMF/Heun/Fuchsian.lean): 9 admissions; 20 theorems: 11 proved, 9 admitted.

## Domains, conventions and source corrections

- Second-order equations are `IsLinearODE2On p r w s` (`w'' + p w' + r w = 0` on `s`, with
  genuine differentiability, so totalized derivatives cannot make a nonsolution satisfy the
  equation). Heun's equation 31.2.1 is `IsHeunSolOn a q α β γ δ ε`, with `ε` explicit;
  Fuchs's relation `α + β + 1 = γ + δ + ε` is a hypothesis of the theorems that need it, and
  `heunEps` gives the determined `ε`. Singularity classification uses the general API of
  `DLMFMathlib.Analysis.ODE.Singularities` (`heunODECoeff` indexes the coefficients as `r, p`);
  Poincaré ranks of irregular singularities are `HasIrregularRankAtInfinity` and
  `HasIrregularRankAt` (untagged definitions in `Basic`).
- `Hl(a, q; α, β, γ, δ; z)` (31.3.1) is `heunLocal`, the `tsum` of `heunLocalCoeff`, whose
  recurrence 31.3.3 divides by `R_j = a(j+1)(j+γ)`; the division is totalized, so the series
  is DLMF's only for `γ ∉ {0, -1, -2, …}` and `a ≠ 0`, which the theorems assume. The
  convergence radius `min(1, |a|)` is `heunLocalRadius`. DLMF's `Hl(0, 0; …)` is not defined
  by 31.3.1 with `a = 0`; it is acquired in its two readings (`a → 0` limit and `ε = 0`), see
  31.7.1.
- Heun functions (31.4): `IsHeunFunctionOn` (31.4.3) treats the two finite singular points
  `s₁, s₂`; `s = ∞` is not covered. `IsHeunEigenvalue01` is the eigenvalue condition for the
  pair `(0, 1)`, and `heunFunction01` (31.4.1) is **defined by choice**: an analytic function
  on `|z| < |a|` agreeing with `Hl` near `0` (unique by the identity theorem), `0` if none
  exists. DLMF's index `m` is not modelled: the eigenvalue `q_m` itself is the argument, and
  the infinitude and discreteness of the eigenvalues is a separate (admitted) theorem.
  `heunCFApprox` gives the continued fraction 31.4.2 by finite truncations.
- Heun polynomials (31.5): `heunPolyMatrix` is the tridiagonal matrix of 31.5.1 and
  `heunPoly` the polynomial 31.5.2.
- Contour integrals: `pochhammerLoop p₁ p₂ ζ` is the Pochhammer contour
  `(p₁+, p₂+, p₁-, p₂-)` made of four circles through the base point `ζ`;
  `continuedPathIntegral` (31.9.2, 31.10.1) is **defined by choice** of the TauCeti analytic
  continuation of the integrand's germ along the path (the continued values are unique); the
  integral is `0` if no continuation exists. Branches of `t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}` are
  `localBranchCpow`, principal at the start of the contour. The double integral 31.9.5 is
  stated in factorized form (a product of two contour integrals).
- Hypergeometric expansions (31.11): `heunHypK/L/M` (31.11.6–31.11.8, with DLMF's `λ` written
  `lam`), `heunHypP5` and `heunHypP6` (the two choices 31.11.3 of `P_j`), `heunHypCoeff` (the
  recurrence 31.11.5) and `heunHypCFApprox` (31.11.13). Type I series are stated for
  principal-branch `P_j`; for the pairs 31.11.15–31.11.17 only the general form 31.11.3 is
  acquired (with principal-branch `P_j^6` the Type II series is not a constant multiple of the
  `(0,1)` Heun function: the ratio varies with `z`; this is a remark on branches, not a claimed
  erratum).
- §31.8 and §31.10 are stated for arbitrary analytic branches of square roots and primitives
  (`S² = Ψ`, `R² = z(z-1)(z-a)`, `G' = integrand`) on an open set, or for a single-valued
  branch `ρ` of the weight given by its logarithmic derivative and a `C¹` path whose
  concomitant (31.10.5–31.10.6, 31.10.15–31.10.16) takes equal values at both ends. No
  branch is imposed. 31.8.1–31.8.3 are stated for `m_k ∈ ℕ` as in DLMF.
- Stieltjes polynomials (31.15): with `N + 1` real points `a_0 < ⋯ < a_N` (DLMF's `N`), the box
  `Q` has `N` factors and DLMF's count `(n+N-2 choose N-2)` reads `(n+N-1 choose N-1)`.
  `stieltjesPoly` (`S_𝐦`) is **defined by choice** when the polynomial with the prescribed zero
  distribution exists uniquely (`0` otherwise). Completeness of the products 31.15.8 in
  `L²_ρ(Q)` is stated as: a function orthogonal to all products vanishes a.e. on `Q`.
- Stronger than DLMF: 31.2.3 `A + B + C = 0` holds without Fuchs's relation
  (`heunNormal_A_add_B_add_C`); 31.3.12 and 31.7.1 hold for all `z` (the totalized series
  agree termwise); 31.14.4 `∑ q̃_j = -∑ q_j` with no condition on the `a_j`; 31.15.7 holds
  whenever `S(a_j) ≠ 0` (DLMF assumes 31.15.5–31.15.6).
- DLMF's own errata already applied in version 1.2.8 are followed (31.8.5 as corrected in
  1.0.7; the sign of 31.12.3 as corrected in 1.0.7).

Source corrections found in this acquisition (numerical evidence with mpmath at complex
parameters; scripts in the agent's scratch directory, not part of the project):

- **31.10.8**: the coefficient of `∂𝒦/∂φ` should be `(2δ-1)cot φ - (2ε-1)tan φ`; DLMF prints
  `(1-2δ)cot φ - (1-2ε)tan φ`. The kernel 31.10.10, which satisfies `(𝒟_z - 𝒟_t)𝒦 = 0` to
  `10⁻³²`, written in `(θ, φ)` by 31.10.7 satisfies the corrected equation to `10⁻³¹` and the
  printed one with residual `1.18` (`|𝒦| ≈ 0.056`); the separable product 31.10.9 of the two
  P-symbol solutions gives `4·10⁻²⁹` against `258`. The P-symbol 31.10.9 (exponents
  `{0, 1-ε}` at `cos²φ = 0`) is consistent only with the corrected sign. Acquired corrected
  (`heun_kernel_typeI_angles`, `heun_kernel_typeI_separable`).
- **31.10.17**: `u = (stz/a)^{1/2}`, not `(stz)^{1/2}/a`. With the printed `u` the kernels
  `u^{2-2γ}`, `u²/(2γ) - v²/(2δ)` and 31.10.19 (all solutions of 31.10.18) violate 31.10.14
  (residuals `2.7·10⁻⁴` and `10⁻²`); with the corrected `u` all three satisfy it to `10⁻³²`.
  Only with this `u` does the cubic term `stz` cancel in `u² + v² + w²`. Acquired corrected
  (`heun_kernel_typeII_uvw`).
- **31.10.22–31.10.23**: the printed P-symbol `P{0,1,∞; 0,0,a; ½(3-γ), c, b; cos²θ}` violates
  Fuchs's relation (its exponents sum to `γ/2`, not `1`) and the printed separable kernel does
  not satisfy 31.10.21 (residual `1.23`). The corrected data, derived from the indicial
  equations of 31.10.21 and checked numerically (residual `3·10⁻³⁰`): exponent `1-γ` at `0`;
  `p² + (α+β-γ)p - σ₂/4 = 0`; `a + b = α + β + 2p`; `ab = p² + (α+β)p - σ₁/4`;
  `c = γ - α - β - 2p`. The relations `m² + 2(α+β)m - σ₁ = 0`, `a' + b' = δ + ε - 1` and
  `a'b' = -σ₂/4` are correct as printed. Acquired corrected (`heun_kernel_typeII_separable`).
- **§31.10(i), Example 2**: `z^{-α}Hl(1/a, q_m; α, α-γ+1, α-β+1, δ; 1/z)` with accessory
  parameter `q_m` does not solve Heun's equation with parameter `q_m` (ODE residual
  `2.9·10⁻³` at `z = 5 + 3i`); the Fuchs–Frobenius solution at `∞` uses the transformed
  parameter of 31.3.10, `q_m/a - α(β-ε) - (α/a)(β-δ)`. The kernel equation of 31.10.11 is
  acquired (verified with the exponent-`0` branch `₂F₁(-1/2+δ+σ, -1/2+ε-σ; ε; ·)` of its
  P-symbol); the representation itself is not (along the contour the kernel's
  `₂F₁(…; a/(zt))` must be continued beyond its disk of convergence).

## Numbered formulas and prose items

## [§31.2 Differential Equations](https://dlmf.nist.gov/31.2)

- [31.2.i](https://dlmf.nist.gov/31.2.i): [`DLMF.Heun.heun_singularities`](DLMF/Heun/Equation.lean#L208) (proved); [`DLMF.Heun.heun_exponents_zero`](DLMF/Heun/Equation.lean#L339) (proved); [`DLMF.Heun.heun_exponents_one`](DLMF/Heun/Equation.lean#L371) (proved); [`DLMF.Heun.heun_exponents_a`](DLMF/Heun/Equation.lean#L400) (proved); [`DLMF.Heun.heun_exponents_infinity`](DLMF/Heun/Equation.lean#L428) (proved); [`DLMF.Heun.heun_indicial_infinity`](DLMF/Heun/Equation.lean#L464) (proved)
- [31.2.v](https://dlmf.nist.gov/31.2.v): [`DLMF.Heun.heun_fHomotopic_zero`](DLMF/Heun/Equation.lean#L595) (proved); [`DLMF.Heun.heun_fHomotopic_one`](DLMF/Heun/Equation.lean#L625) (proved); [`DLMF.Heun.heun_fHomotopic_a`](DLMF/Heun/Equation.lean#L652) (proved); [`DLMF.Heun.heun_homography_div`](DLMF/Heun/Equation.lean#L680) (proved); [`DLMF.Heun.heun_homography_mobius`](DLMF/Heun/Equation.lean#L707) (proved)
- [31.2.E1](https://dlmf.nist.gov/31.2.E1): [`DLMF.Heun.IsHeunSolOn`](DLMF/Heun/Basic.lean#L78) (definition)
- [31.2.E2](https://dlmf.nist.gov/31.2.E2): [`DLMF.Heun.heun_normalForm`](DLMF/Heun/Equation.lean#L483) (proved)
- [31.2.E3](https://dlmf.nist.gov/31.2.E3): [`DLMF.Heun.heunNormalCoeff`](DLMF/Heun/Basic.lean#L110) (definition); [`DLMF.Heun.heunNormal_A_add_B_add_C`](DLMF/Heun/Equation.lean#L473) (proved); [`DLMF.Heun.heun_normalForm`](DLMF/Heun/Equation.lean#L483) (proved)
- [31.2.E4](https://dlmf.nist.gov/31.2.E4): [`DLMF.Heun.heunNormalA`](DLMF/Heun/Basic.lean#L91) (definition); [`DLMF.Heun.heunNormalB`](DLMF/Heun/Basic.lean#L95) (definition); [`DLMF.Heun.heunNormalC`](DLMF/Heun/Basic.lean#L100) (definition); [`DLMF.Heun.heunNormalD`](DLMF/Heun/Basic.lean#L105) (definition); [`DLMF.Heun.heunNormal_A_add_B_add_C`](DLMF/Heun/Equation.lean#L473) (proved)
- [31.2.E5](https://dlmf.nist.gov/31.2.E5): [`DLMF.Heun.heun_trigonometricForm`](DLMF/Heun/Equation.lean#L555) (proved)
- [31.2.E6](https://dlmf.nist.gov/31.2.E6): [`DLMF.Heun.heun_trigonometricForm`](DLMF/Heun/Equation.lean#L555) (proved)
- [31.2.E7](https://dlmf.nist.gov/31.2.E7): [`DLMF.Heun.heun_jacobiForm`](DLMF/Heun/DoublyPeriodic.lean#L66) (proved)
- [31.2.E8](https://dlmf.nist.gov/31.2.E8): [`DLMF.Heun.heun_jacobiForm`](DLMF/Heun/DoublyPeriodic.lean#L66) (proved)
- [31.2.E9](https://dlmf.nist.gov/31.2.E9): [`DLMF.Heun.jacobiSnk_sq_eq_weierstrassP`](DLMF/Heun/DoublyPeriodic.lean#L187) (proved); [`DLMF.Heun.heun_weierstrassForm`](DLMF/Heun/DoublyPeriodic.lean#L283) (proved)
- [31.2.E10](https://dlmf.nist.gov/31.2.E10): [`DLMF.Heun.heun_weierstrassForm`](DLMF/Heun/DoublyPeriodic.lean#L283) (proved)
- [31.2.E11](https://dlmf.nist.gov/31.2.E11): [`DLMF.Heun.heun_weierstrassForm`](DLMF/Heun/DoublyPeriodic.lean#L283) (proved)
- [31.2.E12](https://dlmf.nist.gov/31.2.E12): [`DLMF.Heun.heun_weierstrassForm`](DLMF/Heun/DoublyPeriodic.lean#L283) (proved)

## [§31.3 Basic Solutions](https://dlmf.nist.gov/31.3)

- [31.3.i](https://dlmf.nist.gov/31.3.i): [`DLMF.Heun.heunLocal_zero`](DLMF/Heun/LocalSolutions.lean#L81) (proved); [`DLMF.Heun.heunLocal_isHeunSolOn`](DLMF/Heun/LocalSolutions.lean#L393) (proved); [`DLMF.Heun.eventuallyEq_heunLocal_of_analyticAt`](DLMF/Heun/LocalSolutions.lean#L597) (proved)
- [31.3.E1](https://dlmf.nist.gov/31.3.E1): [`DLMF.Heun.heunLocal`](DLMF/Heun/Basic.lean#L147) (definition); [`DLMF.Heun.hasSum_heunLocal`](DLMF/Heun/LocalSolutions.lean#L384) (proved); [`DLMF.Heun.heunLocal_isHeunSolOn`](DLMF/Heun/LocalSolutions.lean#L393) (proved)
- [31.3.E2](https://dlmf.nist.gov/31.3.E2): [`DLMF.Heun.heunLocalCoeff_rec_zero`](DLMF/Heun/LocalSolutions.lean#L61) (proved)
- [31.3.E3](https://dlmf.nist.gov/31.3.E3): [`DLMF.Heun.heunLocalCoeff_rec`](DLMF/Heun/LocalSolutions.lean#L69) (proved)
- [31.3.E4](https://dlmf.nist.gov/31.3.E4): [`DLMF.Heun.heunRecP`](DLMF/Heun/Basic.lean#L120) (definition); [`DLMF.Heun.heunRecQ`](DLMF/Heun/Basic.lean#L124) (definition); [`DLMF.Heun.heunRecR`](DLMF/Heun/Basic.lean#L129) (definition)
- [31.3.E5](https://dlmf.nist.gov/31.3.E5): [`DLMF.Heun.heunLocal_second_isHeunSolOn`](DLMF/Heun/LocalSolutions.lean#L673) (proved)
- [31.3.E6](https://dlmf.nist.gov/31.3.E6): [`DLMF.Heun.heunLocal_at_one_isHeunSolOn`](DLMF/Heun/LocalSolutions.lean#L695) (proved)
- [31.3.E7](https://dlmf.nist.gov/31.3.E7): [`DLMF.Heun.heunLocal_second_at_one_isHeunSolOn`](DLMF/Heun/LocalSolutions.lean#L716) (proved)
- [31.3.E8](https://dlmf.nist.gov/31.3.E8): [`DLMF.Heun.heunLocal_at_a_isHeunSolOn`](DLMF/Heun/LocalSolutions.lean#L741) (proved)
- [31.3.E9](https://dlmf.nist.gov/31.3.E9): [`DLMF.Heun.heunLocal_second_at_a_isHeunSolOn`](DLMF/Heun/LocalSolutions.lean#L764) (proved)
- [31.3.E10](https://dlmf.nist.gov/31.3.E10): [`DLMF.Heun.heunLocal_at_infinity_isHeunSolOn`](DLMF/Heun/LocalSolutions.lean#L795) (proved)
- [31.3.E11](https://dlmf.nist.gov/31.3.E11): [`DLMF.Heun.heunLocal_second_at_infinity_isHeunSolOn`](DLMF/Heun/LocalSolutions.lean#L818) (proved)
- [31.3.E12](https://dlmf.nist.gov/31.3.E12): [`DLMF.Heun.heunLocal_eq_heunLocal_inv`](DLMF/Heun/LocalSolutions.lean#L874) (proved)
- [31.3.E13](https://dlmf.nist.gov/31.3.E13): [`DLMF.Heun.heunLocal_eq_pfaff`](DLMF/Heun/LocalSolutions.lean#L930) (proved)

## [§31.4 Solutions Analytic at Two Singularities: Heun Functions](https://dlmf.nist.gov/31.4)

- [31.4](https://dlmf.nist.gov/31.4): [`DLMF.Heun.IsHeunEigenvalue01`](DLMF/Heun/Basic.lean#L166) (definition); [`DLMF.Heun.IsHeunEigenvalue01.analyticOn_ball`](DLMF/Heun/HeunFunctions.lean#L50) (admitted); [`DLMF.Heun.heunEigenvalue01_infinite_discrete`](DLMF/Heun/HeunFunctions.lean#L80) (admitted)
- [31.4.E1](https://dlmf.nist.gov/31.4.E1): [`DLMF.Heun.heunFunction01`](DLMF/Heun/Basic.lean#L175) (definition); [`DLMF.Heun.IsHeunEigenvalue01.analyticOn_ball`](DLMF/Heun/HeunFunctions.lean#L50) (admitted); [`DLMF.Heun.heunFunction01_eq_heunLocal`](DLMF/Heun/HeunFunctions.lean#L60) (proved from admissions)
- [31.4.E2](https://dlmf.nist.gov/31.4.E2): [`DLMF.Heun.heunCFApprox`](DLMF/Heun/Basic.lean#L194) (definition); [`DLMF.Heun.tendsto_heunCFApprox`](DLMF/Heun/HeunFunctions.lean#L91) (admitted)
- [31.4.E3](https://dlmf.nist.gov/31.4.E3): [`DLMF.Heun.IsHeunFunctionOn`](DLMF/Heun/Basic.lean#L157) (definition)

## [§31.5 Solutions Analytic at Three Singularities: Heun Polynomials](https://dlmf.nist.gov/31.5)

- [31.5](https://dlmf.nist.gov/31.5): [`DLMF.Heun.heunPoly_isHeunSolOn`](DLMF/Heun/HeunFunctions.lean#L397) (proved); [`DLMF.Heun.heunPolyMatrix_charpoly_natDegree`](DLMF/Heun/HeunFunctions.lean#L456) (proved)
- [31.5.E1](https://dlmf.nist.gov/31.5.E1): [`DLMF.Heun.heunPolyMatrix`](DLMF/Heun/Basic.lean#L200) (definition)
- [31.5.E2](https://dlmf.nist.gov/31.5.E2): [`DLMF.Heun.heunPoly`](DLMF/Heun/Basic.lean#L212) (definition); [`DLMF.Heun.heunLocal_eq_heunPoly`](DLMF/Heun/HeunFunctions.lean#L381) (proved); [`DLMF.Heun.heunPoly_isHeunSolOn`](DLMF/Heun/HeunFunctions.lean#L397) (proved)

## [§31.6 Path-Multiplicative Solutions](https://dlmf.nist.gov/31.6)

- [31.6.E1](https://dlmf.nist.gov/31.6.E1): [`DLMF.Heun.IsPathMultiplicative`](DLMF/Heun/Basic.lean#L316) (definition)

## [§31.7 Relations to Other Functions](https://dlmf.nist.gov/31.7)

- [31.7.ii](https://dlmf.nist.gov/31.7.ii): [`DLMF.Heun.heun_lame`](DLMF/Heun/DoublyPeriodic.lean#L395) (proved); [`DLMF.Heun.heunLocal_lame_even_odd`](DLMF/Heun/DoublyPeriodic.lean#L443) (proved)
- [31.7.E1](https://dlmf.nist.gov/31.7.E1): [`DLMF.Heun.heunLocal_one_eq_hypergeometric`](DLMF/Heun/Hypergeometric.lean#L124) (proved); [`DLMF.Heun.heunLocal_eps_zero_eq_hypergeometric`](DLMF/Heun/Hypergeometric.lean#L134) (proved); [`DLMF.Heun.tendsto_heunLocal_zero_eq_hypergeometric`](DLMF/Heun/Hypergeometric.lean#L146) (proved); [`DLMF.Heun.hypergeometric_isHeunSolOn_zero`](DLMF/Heun/Hypergeometric.lean#L156) (proved)
- [31.7.E2](https://dlmf.nist.gov/31.7.E2): [`DLMF.Heun.heunLocal_two_eq_hypergeometric`](DLMF/Heun/Hypergeometric.lean#L240) (proved)
- [31.7.E3](https://dlmf.nist.gov/31.7.E3): [`DLMF.Heun.heunLocal_four_eq_hypergeometric`](DLMF/Heun/Hypergeometric.lean#L339) (proved)
- [31.7.E4](https://dlmf.nist.gov/31.7.E4): [`DLMF.Heun.heunLocal_cubic_eq_hypergeometric`](DLMF/Heun/Hypergeometric.lean#L441) (admitted)
- [31.7.E5](https://dlmf.nist.gov/31.7.E5): [`DLMF.Heun.heun_lame`](DLMF/Heun/DoublyPeriodic.lean#L395) (proved)

## [§31.8 Solutions via Quadratures](https://dlmf.nist.gov/31.8)

- [31.8.E1](https://dlmf.nist.gov/31.8.E1): [`DLMF.Heun.heun_hermiteDarboux`](DLMF/Heun/Integral.lean#L76) (admitted)
- [31.8.E2](https://dlmf.nist.gov/31.8.E2): [`DLMF.Heun.heun_hermiteDarboux`](DLMF/Heun/Integral.lean#L76) (admitted); [`DLMF.Heun.heun_hermiteDarboux_example₁`](DLMF/Heun/Integral.lean#L140) (proved); [`DLMF.Heun.heun_hermiteDarboux_example₂`](DLMF/Heun/Integral.lean#L226) (proved)
- [31.8.E3](https://dlmf.nist.gov/31.8.E3): [`DLMF.Heun.heun_hermiteDarboux`](DLMF/Heun/Integral.lean#L76) (admitted)
- [31.8.E4](https://dlmf.nist.gov/31.8.E4): [`DLMF.Heun.heun_hermiteDarboux_example₁`](DLMF/Heun/Integral.lean#L140) (proved)
- [31.8.E5](https://dlmf.nist.gov/31.8.E5): [`DLMF.Heun.heun_hermiteDarboux_example₂`](DLMF/Heun/Integral.lean#L226) (proved). As corrected in DLMF 1.0.7.

## [§31.9 Orthogonality](https://dlmf.nist.gov/31.9)

- [31.9.E1](https://dlmf.nist.gov/31.9.E1): [`DLMF.Heun.heun_orthogonality_ne`](DLMF/Heun/HeunFunctions.lean#L465) (admitted)
- [31.9.E2](https://dlmf.nist.gov/31.9.E2): [`DLMF.Heun.heun_orthogonality_ne`](DLMF/Heun/HeunFunctions.lean#L465) (admitted); [`DLMF.Heun.heun_orthogonality_self`](DLMF/Heun/HeunFunctions.lean#L481) (admitted)
- [31.9.E3](https://dlmf.nist.gov/31.9.E3): [`DLMF.Heun.heun_orthogonality_self`](DLMF/Heun/HeunFunctions.lean#L481) (admitted)
- [31.9.E4](https://dlmf.nist.gov/31.9.E4): [`DLMF.Heun.heun_orthogonality_self`](DLMF/Heun/HeunFunctions.lean#L481) (admitted)
- [31.9.E5](https://dlmf.nist.gov/31.9.E5): [`DLMF.Heun.heunPoly_double_orthogonality`](DLMF/Heun/HeunFunctions.lean#L504) (admitted)
- [31.9.E6](https://dlmf.nist.gov/31.9.E6): [`DLMF.Heun.heunPoly_double_orthogonality`](DLMF/Heun/HeunFunctions.lean#L504) (admitted)

## [§31.10 Integral Equations and Representations](https://dlmf.nist.gov/31.10)

- [31.10.E1](https://dlmf.nist.gov/31.10.E1): [`DLMF.Heun.heun_integral_typeI`](DLMF/Heun/Integral.lean#L338) (admitted); [`DLMF.Heun.heun_integralEquation_example₁`](DLMF/Heun/Integral.lean#L528) (admitted)
- [31.10.E2](https://dlmf.nist.gov/31.10.E2): [`DLMF.Heun.heunWeight`](DLMF/Heun/Basic.lean#L335) (definition); [`DLMF.Heun.heun_integral_typeI`](DLMF/Heun/Integral.lean#L338) (admitted)
- [31.10.E3](https://dlmf.nist.gov/31.10.E3): [`DLMF.Heun.heun_integral_typeI`](DLMF/Heun/Integral.lean#L338) (admitted); [`DLMF.Heun.heun_kernel_example₁_pde`](DLMF/Heun/Integral.lean#L512) (admitted); [`DLMF.Heun.heun_kernel_example₂_pde`](DLMF/Heun/Integral.lean#L549) (admitted)
- [31.10.E4](https://dlmf.nist.gov/31.10.E4): [`DLMF.Heun.heunOperator`](DLMF/Heun/Basic.lean#L327) (definition); [`DLMF.Heun.isHeunSolOn_iff_heunOperator`](DLMF/Heun/Equation.lean#L119) (proved)
- [31.10.E5](https://dlmf.nist.gov/31.10.E5): [`DLMF.Heun.heun_integral_typeI`](DLMF/Heun/Integral.lean#L338) (admitted)
- [31.10.E6](https://dlmf.nist.gov/31.10.E6): [`DLMF.Heun.heunConcomitantP`](DLMF/Heun/Basic.lean#L341) (definition); [`DLMF.Heun.heun_integral_typeI`](DLMF/Heun/Integral.lean#L338) (admitted)
- [31.10.E7](https://dlmf.nist.gov/31.10.E7): [`DLMF.Heun.heun_kernel_typeI_angles`](DLMF/Heun/Integral.lean#L364) (admitted)
- [31.10.E8](https://dlmf.nist.gov/31.10.E8): [`DLMF.Heun.heun_kernel_typeI_angles`](DLMF/Heun/Integral.lean#L364) (admitted); [`DLMF.Heun.heun_kernel_typeI_separable`](DLMF/Heun/Integral.lean#L450) (proved). Corrected sign; see source corrections.
- [31.10.E9](https://dlmf.nist.gov/31.10.E9): [`DLMF.Heun.heun_kernel_typeI_separable`](DLMF/Heun/Integral.lean#L450) (proved)
- [31.10.E10](https://dlmf.nist.gov/31.10.E10): [`DLMF.Heun.heun_kernel_example₁_pde`](DLMF/Heun/Integral.lean#L512) (admitted); [`DLMF.Heun.heun_integralEquation_example₁`](DLMF/Heun/Integral.lean#L528) (admitted)
- [31.10.E11](https://dlmf.nist.gov/31.10.E11): [`DLMF.Heun.heun_kernel_example₂_pde`](DLMF/Heun/Integral.lean#L549) (admitted). Kernel equation only; the Example 2 representation is not acquired (see source corrections).
- [31.10.E12](https://dlmf.nist.gov/31.10.E12): [`DLMF.Heun.heun_integral_typeII`](DLMF/Heun/Integral.lean#L571) (admitted)
- [31.10.E13](https://dlmf.nist.gov/31.10.E13): [`DLMF.Heun.heun_integral_typeII`](DLMF/Heun/Integral.lean#L571) (admitted)
- [31.10.E14](https://dlmf.nist.gov/31.10.E14): [`DLMF.Heun.heun_integral_typeII`](DLMF/Heun/Integral.lean#L571) (admitted); [`DLMF.Heun.heun_kernel_typeII_uvw`](DLMF/Heun/Integral.lean#L604) (admitted)
- [31.10.E15](https://dlmf.nist.gov/31.10.E15): [`DLMF.Heun.heun_integral_typeII`](DLMF/Heun/Integral.lean#L571) (admitted)
- [31.10.E16](https://dlmf.nist.gov/31.10.E16): [`DLMF.Heun.heun_integral_typeII`](DLMF/Heun/Integral.lean#L571) (admitted)
- [31.10.E17](https://dlmf.nist.gov/31.10.E17): [`DLMF.Heun.heun_kernel_typeII_uvw`](DLMF/Heun/Integral.lean#L604) (admitted). Corrected `u`; see source corrections.
- [31.10.E18](https://dlmf.nist.gov/31.10.E18): [`DLMF.Heun.heun_kernel_typeII_uvw`](DLMF/Heun/Integral.lean#L604) (admitted); [`DLMF.Heun.heun_kernel_typeII_cylinder`](DLMF/Heun/Integral.lean#L673) (proved)
- [31.10.E19](https://dlmf.nist.gov/31.10.E19): [`DLMF.Heun.heun_kernel_typeII_cylinder`](DLMF/Heun/Integral.lean#L673) (proved)
- [31.10.E20](https://dlmf.nist.gov/31.10.E20): [`DLMF.Heun.heun_kernel_typeII_spherical`](DLMF/Heun/Integral.lean#L731) (admitted)
- [31.10.E21](https://dlmf.nist.gov/31.10.E21): [`DLMF.Heun.heun_kernel_typeII_spherical`](DLMF/Heun/Integral.lean#L731) (admitted)
- [31.10.E22](https://dlmf.nist.gov/31.10.E22): [`DLMF.Heun.heun_kernel_typeII_separable`](DLMF/Heun/Integral.lean#L833) (proved). Corrected P-symbol; see source corrections.
- [31.10.E23](https://dlmf.nist.gov/31.10.E23): [`DLMF.Heun.heun_kernel_typeII_separable`](DLMF/Heun/Integral.lean#L833) (proved). Corrected relations; see source corrections.

## [§31.11 Expansions in Series of Hypergeometric Functions](https://dlmf.nist.gov/31.11)

- [31.11.iv](https://dlmf.nist.gov/31.11.iv): [`DLMF.Heun.heunHypP6_typeII_polynomial`](DLMF/Heun/Hypergeometric.lean#L651) (proved); [`DLMF.Heun.hasSum_heunHyp_typeII`](DLMF/Heun/Hypergeometric.lean#L681) (admitted)
- [31.11.iii](https://dlmf.nist.gov/31.11.iii): [`DLMF.Heun.heunHypM_neg_one_eq_zero`](DLMF/Heun/Hypergeometric.lean#L481) (proved); [`DLMF.Heun.hasSum_heunHyp_typeI`](DLMF/Heun/Hypergeometric.lean#L609) (admitted); [`DLMF.Heun.tendsto_heunHypCFApprox`](DLMF/Heun/Hypergeometric.lean#L634) (admitted)
- [31.11.E1](https://dlmf.nist.gov/31.11.E1): [`DLMF.Heun.hasSum_heunHyp_typeI`](DLMF/Heun/Hypergeometric.lean#L609) (admitted); [`DLMF.Heun.hasSum_heunHyp_typeI'`](DLMF/Heun/Hypergeometric.lean#L623) (admitted)
- [31.11.E2](https://dlmf.nist.gov/31.11.E2): [`DLMF.Heun.heunHypP5_P6_riemann`](DLMF/Heun/Hypergeometric.lean#L539) (proved)
- [31.11.E3](https://dlmf.nist.gov/31.11.E3): [`DLMF.Heun.heunHyp_typeI_add`](DLMF/Heun/Hypergeometric.lean#L465) (proved); [`DLMF.Heun.heunHyp_typeII_add`](DLMF/Heun/Hypergeometric.lean#L473) (proved)
- [31.11.E3_1](https://dlmf.nist.gov/31.11.E3_1): [`DLMF.Heun.heunHypP5`](DLMF/Heun/Basic.lean#L256) (definition); [`DLMF.Heun.heunHypP5_P6_riemann`](DLMF/Heun/Hypergeometric.lean#L539) (proved)
- [31.11.E3_2](https://dlmf.nist.gov/31.11.E3_2): [`DLMF.Heun.heunHypP6`](DLMF/Heun/Basic.lean#L265) (definition); [`DLMF.Heun.heunHypP5_P6_riemann`](DLMF/Heun/Hypergeometric.lean#L539) (proved)
- [31.11.E4](https://dlmf.nist.gov/31.11.E4): [`DLMF.Heun.hasSum_heunHyp_typeI`](DLMF/Heun/Hypergeometric.lean#L609) (admitted)
- [31.11.E5](https://dlmf.nist.gov/31.11.E5): [`DLMF.Heun.hasSum_heunHyp_typeI`](DLMF/Heun/Hypergeometric.lean#L609) (admitted)
- [31.11.E6](https://dlmf.nist.gov/31.11.E6): [`DLMF.Heun.heunHypK`](DLMF/Heun/Basic.lean#L221) (definition)
- [31.11.E7](https://dlmf.nist.gov/31.11.E7): [`DLMF.Heun.heunHypL`](DLMF/Heun/Basic.lean#L229) (definition)
- [31.11.E8](https://dlmf.nist.gov/31.11.E8): [`DLMF.Heun.heunHypM`](DLMF/Heun/Basic.lean#L239) (definition)
- [31.11.E9](https://dlmf.nist.gov/31.11.E9): [`DLMF.Heun.heunHypM_neg_one_eq_zero`](DLMF/Heun/Hypergeometric.lean#L481) (proved)
- [31.11.E10](https://dlmf.nist.gov/31.11.E10): [`DLMF.Heun.heunHyp_typeI_add`](DLMF/Heun/Hypergeometric.lean#L465) (proved); [`DLMF.Heun.hasSum_heunHyp_typeI`](DLMF/Heun/Hypergeometric.lean#L609) (admitted)
- [31.11.E11](https://dlmf.nist.gov/31.11.E11): [`DLMF.Heun.heunHyp_typeI_add`](DLMF/Heun/Hypergeometric.lean#L465) (proved); [`DLMF.Heun.hasSum_heunHyp_typeI'`](DLMF/Heun/Hypergeometric.lean#L623) (admitted)
- [31.11.E12](https://dlmf.nist.gov/31.11.E12): [`DLMF.Heun.hasSum_heunHyp_typeI`](DLMF/Heun/Hypergeometric.lean#L609) (admitted)
- [31.11.E13](https://dlmf.nist.gov/31.11.E13): [`DLMF.Heun.heunHypCFApprox`](DLMF/Heun/Basic.lean#L281) (definition); [`DLMF.Heun.tendsto_heunHypCFApprox`](DLMF/Heun/Hypergeometric.lean#L634) (admitted)
- [31.11.E14](https://dlmf.nist.gov/31.11.E14): [`DLMF.Heun.heunHyp_typeII_add`](DLMF/Heun/Hypergeometric.lean#L473) (proved); [`DLMF.Heun.heunHypP6_typeII_polynomial`](DLMF/Heun/Hypergeometric.lean#L651) (proved); [`DLMF.Heun.hasSum_heunHyp_typeII`](DLMF/Heun/Hypergeometric.lean#L681) (admitted)
- [31.11.E15](https://dlmf.nist.gov/31.11.E15): [`DLMF.Heun.heunHyp_typeII_add`](DLMF/Heun/Hypergeometric.lean#L473) (proved). General form 31.11.3 only; see conventions.
- [31.11.E16](https://dlmf.nist.gov/31.11.E16): [`DLMF.Heun.heunHyp_typeII_add`](DLMF/Heun/Hypergeometric.lean#L473) (proved). General form 31.11.3 only; see conventions.
- [31.11.E17](https://dlmf.nist.gov/31.11.E17): [`DLMF.Heun.heunHyp_typeII_add`](DLMF/Heun/Hypergeometric.lean#L473) (proved). General form 31.11.3 only; see conventions.

## [§31.12 Confluent Forms of Heun’s Equation](https://dlmf.nist.gov/31.12)

- [31.12.E1](https://dlmf.nist.gov/31.12.E1): [`DLMF.Heun.IsConfluentHeunSolOn`](DLMF/Heun/Basic.lean#L347) (definition); [`DLMF.Heun.confluentHeun_singularities`](DLMF/Heun/Confluent.lean#L61) (proved)
- [31.12.E2](https://dlmf.nist.gov/31.12.E2): [`DLMF.Heun.IsDoublyConfluentHeunSolOn`](DLMF/Heun/Basic.lean#L353) (definition); [`DLMF.Heun.doublyConfluentHeun_singularities`](DLMF/Heun/Confluent.lean#L127) (proved)
- [31.12.E3](https://dlmf.nist.gov/31.12.E3): [`DLMF.Heun.IsBiconfluentHeunSolOn`](DLMF/Heun/Basic.lean#L359) (definition); [`DLMF.Heun.biconfluentHeun_singularities`](DLMF/Heun/Confluent.lean#L202) (proved). Sign as corrected in DLMF 1.0.7.
- [31.12.E4](https://dlmf.nist.gov/31.12.E4): [`DLMF.Heun.IsTriconfluentHeunSolOn`](DLMF/Heun/Basic.lean#L365) (definition); [`DLMF.Heun.triconfluentHeun_ordinary`](DLMF/Heun/Confluent.lean#L256) (proved); [`DLMF.Heun.triconfluentHeun_rank_infinity`](DLMF/Heun/Confluent.lean#L271) (proved)

## [§31.14 General Fuchsian Equation](https://dlmf.nist.gov/31.14)

- [31.14.E1](https://dlmf.nist.gov/31.14.E1): [`DLMF.Heun.IsFuchsianSolOn`](DLMF/Heun/Basic.lean#L400) (definition); [`DLMF.Heun.fuchsian_exponents_finite`](DLMF/Heun/Fuchsian.lean#L57) (proved); [`DLMF.Heun.fuchsian_exponents_infinity`](DLMF/Heun/Fuchsian.lean#L110) (proved); [`DLMF.Heun.isHeunSolOn_iff_isFuchsianSolOn`](DLMF/Heun/Fuchsian.lean#L155) (proved)
- [31.14.E2](https://dlmf.nist.gov/31.14.E2): [`DLMF.Heun.fuchsian_exponents_infinity`](DLMF/Heun/Fuchsian.lean#L110) (proved); [`DLMF.Heun.fuchsian_indicial_infinity`](DLMF/Heun/Fuchsian.lean#L147) (proved); [`DLMF.Heun.isHeunSolOn_iff_isFuchsianSolOn`](DLMF/Heun/Fuchsian.lean#L155) (proved)
- [31.14.E3](https://dlmf.nist.gov/31.14.E3): [`DLMF.Heun.fuchsian_normalForm`](DLMF/Heun/Fuchsian.lean#L289) (proved)
- [31.14.E4](https://dlmf.nist.gov/31.14.E4): [`DLMF.Heun.fuchsianNormalCoeff`](DLMF/Heun/Basic.lean#L417) (definition); [`DLMF.Heun.fuchsianNormalQ_sum`](DLMF/Heun/Fuchsian.lean#L193) (proved); [`DLMF.Heun.fuchsianNormalQ_sum_eq_zero`](DLMF/Heun/Fuchsian.lean#L215) (proved); [`DLMF.Heun.fuchsian_normalForm`](DLMF/Heun/Fuchsian.lean#L289) (proved)
- [31.14.E5](https://dlmf.nist.gov/31.14.E5): [`DLMF.Heun.fuchsianNormalQ`](DLMF/Heun/Basic.lean#L408) (definition); [`DLMF.Heun.fuchsianNormalGamma`](DLMF/Heun/Basic.lean#L413) (definition); [`DLMF.Heun.fuchsianNormalQ_sum`](DLMF/Heun/Fuchsian.lean#L193) (proved); [`DLMF.Heun.fuchsian_normalForm`](DLMF/Heun/Fuchsian.lean#L289) (proved)

## [§31.15 Stieltjes Polynomials](https://dlmf.nist.gov/31.15)

- [31.15.i](https://dlmf.nist.gov/31.15.i): [`DLMF.Heun.IsVanVleckStieltjes`](DLMF/Heun/Basic.lean#L437) (definition); [`DLMF.Heun.vanVleck_card_le`](DLMF/Heun/Fuchsian.lean#L370) (admitted)
- [31.15.ii](https://dlmf.nist.gov/31.15.ii): [`DLMF.Heun.stieltjes_zeros_critical`](DLMF/Heun/Fuchsian.lean#L552) (proved)
- [31.15.iii](https://dlmf.nist.gov/31.15.iii): [`DLMF.Heun.stieltjesPoly`](DLMF/Heun/Basic.lean#L461) (definition); [`DLMF.Heun.existsUnique_stieltjesOfIndex`](DLMF/Heun/Fuchsian.lean#L665) (admitted); [`DLMF.Heun.stieltjesProduct_norm_pos`](DLMF/Heun/Fuchsian.lean#L730) (admitted); [`DLMF.Heun.stieltjesProduct_complete`](DLMF/Heun/Fuchsian.lean#L738) (admitted)
- [31.15.E1](https://dlmf.nist.gov/31.15.E1): [`DLMF.Heun.IsStieltjesEquation`](DLMF/Heun/Basic.lean#L430) (definition); [`DLMF.Heun.vanVleck_card_le`](DLMF/Heun/Fuchsian.lean#L370) (admitted)
- [31.15.E2](https://dlmf.nist.gov/31.15.E2): [`DLMF.Heun.stieltjes_zeros_equilibrium`](DLMF/Heun/Fuchsian.lean#L427) (proved)
- [31.15.E3](https://dlmf.nist.gov/31.15.E3): [`DLMF.Heun.vanVleck_zeros`](DLMF/Heun/Fuchsian.lean#L479) (proved)
- [31.15.E4](https://dlmf.nist.gov/31.15.E4): [`DLMF.Heun.stieltjesG`](DLMF/Heun/Basic.lean#L443) (definition); [`DLMF.Heun.stieltjes_zeros_critical`](DLMF/Heun/Fuchsian.lean#L552) (proved)
- [31.15.E5](https://dlmf.nist.gov/31.15.E5): [`DLMF.Heun.existsUnique_stieltjesOfIndex`](DLMF/Heun/Fuchsian.lean#L665) (admitted); [`DLMF.Heun.stieltjes_card`](DLMF/Heun/Fuchsian.lean#L674) (admitted)
- [31.15.E6](https://dlmf.nist.gov/31.15.E6): [`DLMF.Heun.existsUnique_stieltjesOfIndex`](DLMF/Heun/Fuchsian.lean#L665) (admitted); [`DLMF.Heun.stieltjes_card`](DLMF/Heun/Fuchsian.lean#L674) (admitted)
- [31.15.E7](https://dlmf.nist.gov/31.15.E7): [`DLMF.Heun.stieltjes_accessory`](DLMF/Heun/Fuchsian.lean#L684) (proved)
- [31.15.E8](https://dlmf.nist.gov/31.15.E8): [`DLMF.Heun.stieltjesProduct`](DLMF/Heun/Basic.lean#L479) (definition); [`DLMF.Heun.stieltjesProduct_orthogonal`](DLMF/Heun/Fuchsian.lean#L722) (admitted)
- [31.15.E9](https://dlmf.nist.gov/31.15.E9): [`DLMF.Heun.stieltjesProduct_orthogonal`](DLMF/Heun/Fuchsian.lean#L722) (admitted)
- [31.15.E10](https://dlmf.nist.gov/31.15.E10): [`DLMF.Heun.stieltjesBox`](DLMF/Heun/Basic.lean#L467) (definition); [`DLMF.Heun.stieltjesProduct_orthogonal`](DLMF/Heun/Fuchsian.lean#L722) (admitted)
- [31.15.E11](https://dlmf.nist.gov/31.15.E11): [`DLMF.Heun.stieltjesInner`](DLMF/Heun/Basic.lean#L484) (definition); [`DLMF.Heun.stieltjesProduct_orthogonal`](DLMF/Heun/Fuchsian.lean#L722) (admitted)
- [31.15.E12](https://dlmf.nist.gov/31.15.E12): [`DLMF.Heun.stieltjesWeight`](DLMF/Heun/Basic.lean#L472) (definition); [`DLMF.Heun.stieltjesProduct_orthogonal`](DLMF/Heun/Fuchsian.lean#L722) (admitted)

## Prose, informal and excluded items

- [§31.1](https://dlmf.nist.gov/31.1) Special Notation: notation only; the conventions are
  recorded above.
- [31.2.v](https://dlmf.nist.gov/31.2.v), "Composite Transformations": the count of 192
  automorphisms generated by the eight `F`-homotopic and 24 homographic maps is a remark about
  the group; only its generators are acquired.
- [31.3.i](https://dlmf.nist.gov/31.3.i): the remark that for `γ ∈ ℤ` the second solution
  generally involves logarithms is informal; not acquired.
  [31.3.iii](https://dlmf.nist.gov/31.3.iii): the count `192/8 = 24` of equivalent expressions
  for each of the eight local solutions is not acquired; the examples 31.3.12–31.3.13 are.
- [§31.6](https://dlmf.nist.gov/31.6): the defining property of path-multiplicative
  solutions (multiplication by `e^{2νπi}` around a loop enclosing `s₁, s₂`) is the predicate
  `IsPathMultiplicative` tagged 31.6.1; the eigenvalue sets `{q_m}` themselves are not modelled.
- [§31.7(i)](https://dlmf.nist.gov/31.7.i): the pointers to further reductions (Maier 2005;
  Joyce 1994, an algebraic change of variable) are bibliographic; not acquired.
- [§31.8](https://dlmf.nist.gov/31.8): the remarks on Hermite's Lamé solutions, the
  finite-gap property, the behaviour at the gap ends and the construction by Kovacic's
  algorithm are informal; not acquired.
- [§31.11(i)](https://dlmf.nist.gov/31.11.i) Introduction and
  [§31.11(v)](https://dlmf.nist.gov/31.11.v) Doubly-Infinite Series: descriptive and
  bibliographic; not acquired. The convergence-domain remarks of 31.11(iii)–(iv) are folded into
  the hypotheses of the acquired series theorems.
- [§31.12](https://dlmf.nist.gov/31.12): the remark that Mathieu, spheroidal and Coulomb
  spheroidal functions are special cases of solutions of 31.12.1 is not attached to explicit
  transformations in DLMF; not acquired.
- [§31.13](https://dlmf.nist.gov/31.13) Asymptotic Approximations: references only; nothing to
  acquire.
- [§31.14(ii)](https://dlmf.nist.gov/31.14.ii) Kovacic's algorithm: an algorithm; not
  acquired. The parameter count `3N - 3` of §31.14(i) is a remark; not acquired.
- [§31.15(ii)](https://dlmf.nist.gov/31.15.ii): the Stieltjes electrostatic interpretation is
  the physical reading of 31.15.2 (acquired); the location-of-zeros references are not
  acquired.
- [§31.16](https://dlmf.nist.gov/31.16) Mathematical Applications: excluded: application. Its
  pure mathematics: the uniformization problem for Heun's equation (31.16(i)), and products of
  Heun polynomials (31.16(ii)): the expansion 31.16.1
  `Hp_{n,m}(x)Hp_{n,m}(y) = ∑_j A_j × (Jacobi polynomials)` with the relations 31.16.2, the
  first coefficient 31.16.3 and the three-term recurrence 31.16.4–31.16.7 for the `A_j`.
- [§31.17](https://dlmf.nist.gov/31.17) Physical Applications: excluded: application
  (addition of three quantum spins by separation of variables on the sphere, 31.17.1–31.17.5,
  and the survey of other applications in §31.17(ii)).
- [§31.18](https://dlmf.nist.gov/31.18) Methods of Computation: excluded: computation.
- Bibliographic paragraphs ("See Ronveaux (1995)", …) are not acquired.

## Validation

- All nine modules build with `lake build DLMF.Heun.<Module>` and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` with only `sorry` warnings
  (`Basic` with none). There are no axioms, no `native_decide`, and no `sorry` in definitions
  or helper declarations (prefix `h31_`). No line exceeds 100 characters.
- `#print axioms` for a sample of proved theorems (`isHeunSolOn_iff_heunOperator`,
  `heunNormal_A_add_B_add_C`, `heunLocal_eq_heunLocal_inv`, `heunLocalCoeff_rec`,
  `heunPolyMatrix_charpoly_natDegree`, `heunLocal_one_eq_hypergeometric`,
  `heunHypM_neg_one_eq_zero`, `triconfluentHeun_rank_infinity`, `triconfluentHeun_ordinary`,
  `isHeunSolOn_iff_isFuchsianSolOn`, `fuchsianNormalQ_sum`, `fuchsian_exponents_infinity`,
  `fuchsian_exponents_finite`, `stieltjes_accessory`, `vanVleck_zeros`) shows only `propext`,
  `Classical.choice` and `Quot.sound`. `heun_lame` (31.7.5) is proved from the admitted
  Jacobi form `heun_jacobiForm` and depends on `sorryAx`.
- Admitted statements were checked numerically before acquisition (mpmath, complex
  parameters): 31.2.3–31.2.4, 31.2.6, 31.2.8, 31.2.9–31.2.12, the `F`-homotopic and
  homographic maps, 31.3.1, 31.3.5–31.3.13, 31.4.2, 31.5, 31.7.1–31.7.4, 31.8.4–31.8.5,
  31.9.2–31.9.4 (normalization constants to ten digits), 31.10.10, 31.10.11 (kernel equations),
  31.10.19 in 31.10.18 and 31.10.14, 31.11 Type I and the Type II series 31.11.14, 31.14.5,
  31.15.2, 31.15.3, 31.15.7 and the orthogonality 31.15.10–31.15.12.
- DLMF.lean, the umbrella `DLMF/Heun.lean`, the lakefile and the other ledgers are unchanged.
