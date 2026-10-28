# DLMF Chapter 20 acquisition: Theta Functions

This acquisition covers mathematical definitions, numbered formulas and analytical assertions
in prose from [DLMF Chapter 20](https://dlmf.nist.gov/20), version 1.2.8, checked on
2026-10-25. Graphics (§20.3), applications (§§20.12–20.13), computation, tables and software
(§§20.14–20.16) are excluded. Of 113 numbered equation slots, 107 are in scope
(§§20.2, 20.4–20.11); 20.13.E1–E5 (application) and 20.15.E1 (tables) are excluded and
listed below. §20.1 notation is recorded through definitions and docstrings.

**Status after proof round 1 (2026-10-25).** The 143 declarations tagged with Chapter 20 IDs are 16 definitions, 105 proved theorems and 22 theorems that still depend on admissions (22 direct admissions in DLMF/Theta; the counts below record the acquisition and earlier states). The per-line statuses in this ledger are regenerated from the compiled dump. See REVIEW.md, "Proof round 1 for Chapters 19–23 (2026-10-25)".

The entry point is [DLMF/Theta.lean](DLMF/Theta.lean).
[MathlibCoverage.lean](DLMF/Theta/MathlibCoverage.lean) records 13 checked Mathlib pointers;
the existing pointer for `jacobiTheta₂` in [DLMF/Elliptic/MathlibCoverage.lean](DLMF/Elliptic/MathlibCoverage.lean)
is reused. The existing definitions `DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`
and their lemmas in [DLMF/Elliptic/Theta.lean](DLMF/Elliptic/Theta.lean) and
[DLMF/Elliptic/ThetaAGM.lean](DLMF/Elliptic/ThetaAGM.lean) were tagged in place, not
duplicated. Links and proof statuses below come from the compiled DLMF tag dump and a
`#print axioms` audit; a declaration whose proof uses an admitted lemma is marked
"proved modulo".

All 107 in-scope numbered IDs are covered by 124 tagged declarations (16 definitions, 42 proved, 1 proved modulo admitted lemmas, 65 admitted); 48 IDs carry no admission, two are partly proved (20.7.E11, 20.9.E2) and 57 are admitted. With the prose-tagged declarations the area has 143 tagged local declarations: 16 definitions, 51 proved, 2 proved modulo admitted lemmas and 74 direct admissions (two added 2026-10-25 as full-domain corrected forms of 20.7.E34 and 20.9.E2, and two for 20.9.E3 in terms of the complex R_F, `carlsonRF_jacobiTheta_rect` and `carlsonRF_jacobiTheta_eventually`, added by the Chapter 19 acquisition). Proved results include the Fourier series, lattice quasi-periodicity and half-period shifts (§20.2), the zeros (§20.2(iv)), the product forms 20.4.3–20.4.5 and 20.5.1–20.5.4 from the Jacobi triple product, the τ + 1 and −1/τ transformations 20.7.26–20.7.33, and the elliptic-modular properties of k².

## Domains, conventions and source corrections

- The lattice form `θⱼ(z|τ)` is primary. Statements written in the nome use
  `q = e^{iπτ}` and `q^α = e^{iαπτ}`; `q² ↔ 2τ` and `iq ↔ τ + 1/2`. The nome-argument
  functions `jacobiThetaOneQ … jacobiThetaFourQ` use the principal `q^{1/4}` and agree with
  the lattice form for `-1 < Re τ ≤ 1` (θ₁, θ₂) and for all τ (θ₃, θ₄).
- The project definitions are totalized: outside `Im τ > 0` the series are Mathlib's
  `jacobiTheta₂`, which is 0 there. Identities that are trivially true there are stated for
  all τ; the rest assume `Im τ > 0`.
- Infinite products are stated as `Multipliable f ∧ θ = c * ∏' k, f k`, and series as
  `HasSum` or with an explicit summability claim, so that the totalized `∏'`, `∑'`, `∫` do
  not hide divergence. The double products 20.5.14–20.5.17 and the lattice sums 20.6.6–20.6.9
  use the Eisenstein order (inner over `m`), as DLMF requires.
- Division: where DLMF divides by a theta function, a nonvanishing hypothesis is added
  (20.7.11, 20.7.12, 20.7.25, 20.7.34, 20.8.1, 20.11.9); with Lean's `x/0 = 0` the printed
  quotients are false at the zeros.
- **Correction (20.7.34).** With principal square roots and `i^{-1/4} = e^{-iπ/8}` the printed
  identity holds only up to sign; mpmath finds the opposite sign at τ = −2.19 + 1.29i,
  2.03 + 0.90i and −2.85 + 0.88i. The squared identity is acquired for all `Im τ > 0`, and the
  printed form for `τ = it`. The full-domain corrected form gives the root explicitly:
  `e^{-iπ/8} η(τ)η(4τ)/η(2τ)` with Dedekind's η (`jacobiTheta_reduction_iq_eta`).
- **Domain correction (20.9.3).** The left side is π-periodic and even in real `z`, the right
  side `z θ₁′(0)/θ₁(z)` is not; the identity holds for `0 < |z| ≤ π/2` and fails numerically at
  z = 1.6, 2, 2.5 (τ = 0.8i).
  An independent check (2026-10-25) shows the identity also holds for complex z near the real
  segment (e.g. z = 1.4+0.5i, and τ = 0.3+0.6i); the true condition is a branch condition
  (continuation of R_F from z = 0, where all three arguments are 1). Revisited 2026-10-25 with
  the complex Chapter 19 `R_F` (`DLMF.EllipticIntegrals.symEllIntRF`): two corrected complex
  forms are acquired, for τ = it with z in the open period rectangle |Re z| < π/2,
  |Im z| < πt/2 (mpmath: no failure at 3500 points, including points near the edges; fails at
  373 of 500 points with πt/2 < |Im z| < 0.9πt), and for general τ with z in a punctured
  neighbourhood of 0 (no failure at 1000 random τ). For non-rectangular τ the period
  parallelogram π(s + rτ), |s|, |r| < 1/2, is not a valid region (362 failures in 3000 samples
  with τ in the Γ(2) fundamental region).
- **Domain restriction (20.9.2).** For complex τ the identity `K(k) = (π/2)θ₃²(0|τ)` with the
  principal branch of `K` holds only on part of the upper half-plane; with the project's real
  `Real.compEllIntKm` it is acquired in the rectangular case `τ = it`. With the principal complex
  `K` of Chapter 22 (`JacobiElliptic.compEllIntKk`) the exact region of validity is the union of
  the translates `F + 2n` of the Γ(2) fundamental region
  `F = {|Re τ| < 1, |τ − 1/2| > 1/2, |τ + 1/2| > 1/2}` (K′ = −iτK holds on F itself); this
  full-domain form is `compEllIntKk_eq_jacobiThetaThreeNullTau_fundamental`.
- **Exceptional point (20.10.3).** The right side has a removable singularity at `s = 1`,
  where Mathlib's totalized `riemannZeta 1` would give 0. The identity is stated for `s ≠ 1`
  and the value `ln 2` at `s = 1` separately; both were checked numerically.
- Carlson's `R_F` in 20.9.3–20.9.5 is the complex Chapter 19 integral
  `DLMF.EllipticIntegrals.symEllIntRF` (DLMF 19.16.1); in the rectangular forms its arguments are
  nonnegative reals (cast to ℂ). It replaced the local real placeholder `th20_carlsonRF` on
  2026-10-25.

## Numbered formulas

## [§20.2 Definitions and Periodic Properties](https://dlmf.nist.gov/20.2)

- [20.2.E1](https://dlmf.nist.gov/20.2.E1): [`DLMF.Theta.jacobiThetaOneTau_hasSum_sin`](DLMF/Theta/Basic.lean#L246) (proved). Im τ > 0; `HasSum` over n ≥ 0 with q^{(n+1/2)²} = e^{iπτ(n+1/2)²}; the ℤ-series form `jacobiThetaOneTau_eq_tsum` holds for all τ.
- [20.2.E2](https://dlmf.nist.gov/20.2.E2): [`DLMF.Theta.jacobiThetaTwoTau_hasSum_cos`](DLMF/Theta/Basic.lean#L223) (proved). Im τ > 0; `HasSum` over n ≥ 0; ℤ-series form `jacobiThetaTwoTau_eq_tsum` for all τ.
- [20.2.E3](https://dlmf.nist.gov/20.2.E3): [`DLMF.Theta.jacobiThetaThreeTau_hasSum_cos`](DLMF/Theta/Basic.lean#L193) (proved); [`DLMF.Elliptic.jacobiThetaThreeTau_eq_tsum`](DLMF/Elliptic/Theta.lean#L47) (proved); Mathlib: [`jacobiTheta_eq_jacobiTheta₂`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=jacobiTheta_eq_jacobiTheta₂#doc) (special case z = 0: jacobiTheta τ = jacobiTheta₂ 0 τ = θ₃(0|τ)); Mathlib: [`hasSum_nat_jacobiTheta`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=hasSum_nat_jacobiTheta#doc) (special case z = 0: θ₃(0|τ) = 1 + 2 Σ_{n≥1} q^{n²}, Im τ > 0); Mathlib: [`jacobiTheta₂`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=jacobiTheta₂#doc) (different convention: jacobiTheta₂ z τ = θ₃(πz | τ) = Σ_{n∈ℤ} q^{n²} e^{2πinz},  q = e^{iπτ}, for Im τ > 0 (the tsum is totalized to 0 otherwise)). The ℤ-series (existing) and DLMF cosine form (`HasSum` of 2q^{n²}cos 2nz to θ₃ − 1, Im τ > 0).
- [20.2.E4](https://dlmf.nist.gov/20.2.E4): [`DLMF.Theta.jacobiThetaFourTau_hasSum_cos`](DLMF/Theta/Basic.lean#L211) (proved); [`DLMF.Elliptic.jacobiThetaFourTau_eq_tsum`](DLMF/Elliptic/Theta.lean#L58) (proved). As 20.2.E3.
- [20.2.E5](https://dlmf.nist.gov/20.2.E5): [`DLMF.Theta.latticePoint`](DLMF/Theta/Basic.lean#L321) (definition). Lattice points as a definition.
- [20.2.E6](https://dlmf.nist.gov/20.2.E6): [`DLMF.Theta.jacobiThetaOneTau_add_lattice`](DLMF/Theta/Basic.lean#L303) (proved). All m, n ∈ ℤ and all τ (both sides vanish when Im τ ≤ 0).
- [20.2.E7](https://dlmf.nist.gov/20.2.E7): [`DLMF.Theta.jacobiThetaTwoTau_add_lattice`](DLMF/Theta/Basic.lean#L291) (proved). All m, n ∈ ℤ and all τ.
- [20.2.E8](https://dlmf.nist.gov/20.2.E8): [`DLMF.Theta.jacobiThetaThreeTau_add_lattice`](DLMF/Theta/Basic.lean#L271) (proved); [`DLMF.Elliptic.jacobiThetaThreeTau_add_pi`](DLMF/Elliptic/Theta.lean#L68) (proved); [`DLMF.Elliptic.jacobiThetaThreeTau_add_pi_mul`](DLMF/Elliptic/Theta.lean#L81) (proved); Mathlib: [`jacobiTheta₂_add_left`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=jacobiTheta₂_add_left#doc) (special case m = 1, n = 0 in Mathlib's argument z/π: period π of θ₃); Mathlib: [`jacobiTheta₂_add_left'`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=jacobiTheta₂_add_left'#doc) (special case m = 0, n = 1 in Mathlib's argument z/π: θ₃(z + πτ|τ) = q⁻¹ e^{-2iz} θ₃(z|τ)). All m, n ∈ ℤ and all τ; the m = 1 and n = 1 cases are the existing lemmas.
- [20.2.E9](https://dlmf.nist.gov/20.2.E9): [`DLMF.Theta.jacobiThetaFourTau_add_lattice`](DLMF/Theta/Basic.lean#L278) (proved). All m, n ∈ ℤ and all τ.
- [20.2.E10](https://dlmf.nist.gov/20.2.E10): [`DLMF.Theta.thetaMultiplierM`](DLMF/Theta/Basic.lean#L699) (definition). Multiplier M as a definition.
- [20.2.E11](https://dlmf.nist.gov/20.2.E11): [`DLMF.Theta.jacobiThetaOneTau_half_periods`](DLMF/Theta/Basic.lean#L703) (proved); [`DLMF.Elliptic.jacobiThetaOneTau`](DLMF/Elliptic/Theta.lean#L40) (definition). All three equalities, all τ; the first is the project definition of θ₁.
- [20.2.E12](https://dlmf.nist.gov/20.2.E12): [`DLMF.Theta.jacobiThetaTwoTau_half_periods`](DLMF/Theta/Basic.lean#L723) (proved); [`DLMF.Elliptic.jacobiThetaTwoTau`](DLMF/Elliptic/Theta.lean#L35) (definition). All three equalities, all τ.
- [20.2.E13](https://dlmf.nist.gov/20.2.E13): [`DLMF.Theta.jacobiThetaThreeTau_half_periods`](DLMF/Theta/Basic.lean#L739) (proved). All three equalities, all τ.
- [20.2.E14](https://dlmf.nist.gov/20.2.E14): [`DLMF.Theta.jacobiThetaFourTau_half_periods`](DLMF/Theta/Basic.lean#L760) (proved); [`DLMF.Elliptic.jacobiThetaFourTau`](DLMF/Elliptic/Theta.lean#L31) (definition). All three equalities, all τ; the first is the project definition of θ₄.

## [§20.4 Values at z = 0](https://dlmf.nist.gov/20.4)

- [20.4.E1](https://dlmf.nist.gov/20.4.E1): [`DLMF.Theta.jacobiTheta_zero_values`](DLMF/Theta/ZeroValues.lean#L48) (proved). All τ; derivatives are `deriv` in z.
- [20.4.E2](https://dlmf.nist.gov/20.4.E2): [`DLMF.Theta.jacobiThetaOneDerivNullTau_prod`](DLMF/Theta/Products.lean#L1560) (proved). Product as `Multipliable ∧ θ₁′(0) = 2e^{iπτ/4}∏′`, plus the (q²;q²)_∞³ form via `qPochhammerInf`.
- [20.4.E3](https://dlmf.nist.gov/20.4.E3): [`DLMF.Theta.jacobiThetaTwoNullTau_prod`](DLMF/Theta/Products.lean#L1571) (proved). Proved from 20.5.E2 at z = 0.
- [20.4.E4](https://dlmf.nist.gov/20.4.E4): [`DLMF.Theta.jacobiThetaThreeNullTau_prod`](DLMF/Theta/Products.lean#L1588) (proved). Proved from 20.5.E3 at z = 0.
- [20.4.E5](https://dlmf.nist.gov/20.4.E5): [`DLMF.Theta.jacobiThetaFourNullTau_prod`](DLMF/Theta/Products.lean#L1604) (proved). Proved from 20.5.E4 at z = 0.
- [20.4.E6](https://dlmf.nist.gov/20.4.E6): [`DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul`](DLMF/Theta/Products.lean#L1620) (proved). Jacobi’s derivative formula, Im τ > 0.
- [20.4.E7](https://dlmf.nist.gov/20.4.E7): [`DLMF.Theta.jacobiTheta_iteratedDeriv_zero_values`](DLMF/Theta/ZeroValues.lean#L63) (proved). All τ; `iteratedDeriv`, from parity.
- [20.4.E8](https://dlmf.nist.gov/20.4.E8): [`DLMF.Theta.jacobiThetaOne_third_deriv_ratio`](DLMF/Theta/ZeroValues.lean#L443) (proved). `HasSum` form; θ₁′(0|τ) ≠ 0 for Im τ > 0, so DLMF’s quotient is used unchanged.
- [20.4.E9](https://dlmf.nist.gov/20.4.E9): [`DLMF.Theta.jacobiThetaTwo_second_deriv_ratio`](DLMF/Theta/ZeroValues.lean#L459) (proved). `HasSum` form, theta constant nonzero.
- [20.4.E10](https://dlmf.nist.gov/20.4.E10): [`DLMF.Theta.jacobiThetaThree_second_deriv_ratio`](DLMF/Theta/ZeroValues.lean#L476) (proved). `HasSum` form.
- [20.4.E11](https://dlmf.nist.gov/20.4.E11): [`DLMF.Theta.jacobiThetaFour_second_deriv_ratio`](DLMF/Theta/ZeroValues.lean#L495) (proved). `HasSum` form.
- [20.4.E12](https://dlmf.nist.gov/20.4.E12): [`DLMF.Theta.jacobiTheta_deriv_ratio_sum`](DLMF/Theta/ZeroValues.lean#L513) (proved). Quotients of nonvanishing constants.

## [§20.5 Infinite Products and Related Results](https://dlmf.nist.gov/20.5)

- [20.5.E1](https://dlmf.nist.gov/20.5.E1): [`DLMF.Theta.jacobiThetaOneTau_hasProd`](DLMF/Theta/Products.lean#L271) (proved). Proved from the triple product (17.8.E1) via 20.5.E2; `Multipliable ∧ θ = 2q^{1/4} sin z ∏′` (valid also at sin z = 0).
- [20.5.E2](https://dlmf.nist.gov/20.5.E2): [`DLMF.Theta.jacobiThetaTwoTau_hasProd`](DLMF/Theta/Products.lean#L227) (proved). Proved from the triple product and `qPochhammerInf_shift`.
- [20.5.E3](https://dlmf.nist.gov/20.5.E3): [`DLMF.Theta.jacobiThetaThreeTau_hasProd`](DLMF/Theta/Products.lean#L294) (proved). Proved from the triple product.
- [20.5.E4](https://dlmf.nist.gov/20.5.E4): [`DLMF.Theta.jacobiThetaFourTau_hasProd`](DLMF/Theta/Products.lean#L318) (proved). Proved from 20.5.E3 at z + π/2.
- [20.5.E5](https://dlmf.nist.gov/20.5.E5): [`DLMF.Theta.jacobiThetaOneTau_hasProd_sin`](DLMF/Theta/Products.lean#L339) (proved). Im τ > 0; factors sin(nπτ) ≠ 0.
- [20.5.E6](https://dlmf.nist.gov/20.5.E6): [`DLMF.Theta.jacobiThetaTwoTau_hasProd_cos`](DLMF/Theta/Products.lean#L371) (proved). Im τ > 0.
- [20.5.E7](https://dlmf.nist.gov/20.5.E7): [`DLMF.Theta.jacobiThetaThreeTau_hasProd_cos`](DLMF/Theta/Products.lean#L411) (proved). Im τ > 0.
- [20.5.E8](https://dlmf.nist.gov/20.5.E8): [`DLMF.Theta.jacobiThetaFourTau_hasProd_sin`](DLMF/Theta/Products.lean#L449) (proved). Im τ > 0.
- [20.5.E9](https://dlmf.nist.gov/20.5.E9): [`DLMF.Theta.jacobiThetaThreeTau_triple_product`](DLMF/Theta/Products.lean#L486) (proved). Both the bilateral series (`HasSum` over ℤ) and the product; p = e^{iπz}.
- [20.5.E10](https://dlmf.nist.gov/20.5.E10): [`DLMF.Theta.jacobiThetaOneTau_logDeriv`](DLMF/Theta/Products.lean#L822) (proved). Strip |Im z| < π Im τ; both series; at the real zeros of θ₁ both sides are 0 in Lean (removable singularity, see module docstring).
- [20.5.E11](https://dlmf.nist.gov/20.5.E11): [`DLMF.Theta.jacobiThetaTwoTau_logDeriv`](DLMF/Theta/Products.lean#L878) (proved). Strip |Im z| < π Im τ; both series.
- [20.5.E12](https://dlmf.nist.gov/20.5.E12): [`DLMF.Theta.jacobiThetaThreeTau_logDeriv`](DLMF/Theta/Products.lean#L933) (proved). Strip |Im z| < π Im τ/2; both series.
- [20.5.E13](https://dlmf.nist.gov/20.5.E13): [`DLMF.Theta.jacobiThetaFourTau_logDeriv`](DLMF/Theta/Products.lean#L980) (proved). Strip |Im z| < π Im τ/2; both series.
- [20.5.E14](https://dlmf.nist.gov/20.5.E14): [`DLMF.Theta.jacobiThetaOneTau_doubleProd`](DLMF/Theta/Products.lean#L1327) (proved). Eisenstein order: inner limits L(n) exist and the outer symmetric limit converges; stated as ∃ L with both `Tendsto`s.
- [20.5.E15](https://dlmf.nist.gov/20.5.E15): [`DLMF.Theta.jacobiThetaTwoTau_doubleProd`](DLMF/Theta/Products.lean#L1386) (proved). As 20.5.E14.
- [20.5.E16](https://dlmf.nist.gov/20.5.E16): [`DLMF.Theta.jacobiThetaThreeTau_doubleProd`](DLMF/Theta/Products.lean#L1427) (proved). As 20.5.E14.
- [20.5.E17](https://dlmf.nist.gov/20.5.E17): [`DLMF.Theta.jacobiThetaFourTau_doubleProd`](DLMF/Theta/Products.lean#L1463) (proved). As 20.5.E14.

## [§20.6 Power Series](https://dlmf.nist.gov/20.6)

- [20.6.E1](https://dlmf.nist.gov/20.6.E1): [`DLMF.Theta.thetaLatticeMinNorm`](DLMF/Theta/PowerSeries.lean#L55) (definition). The radius min_{(m,n)≠0} |(m+nτ)π| as a definition (`⨅`).
- [20.6.E2](https://dlmf.nist.gov/20.6.E2): [`DLMF.Theta.jacobiThetaOneTau_powerSeries`](DLMF/Theta/PowerSeries.lean#L61) (admitted). Hypothesis |πz| < radius; summability of the exponent series is part of the conclusion.
- [20.6.E3](https://dlmf.nist.gov/20.6.E3): [`DLMF.Theta.jacobiThetaTwoTau_powerSeries`](DLMF/Theta/PowerSeries.lean#L71) (admitted). As 20.6.E2.
- [20.6.E4](https://dlmf.nist.gov/20.6.E4): [`DLMF.Theta.jacobiThetaThreeTau_powerSeries`](DLMF/Theta/PowerSeries.lean#L81) (admitted). As 20.6.E2.
- [20.6.E5](https://dlmf.nist.gov/20.6.E5): [`DLMF.Theta.jacobiThetaFourTau_powerSeries`](DLMF/Theta/PowerSeries.lean#L91) (admitted). As 20.6.E2.
- [20.6.E6](https://dlmf.nist.gov/20.6.E6): [`DLMF.Theta.thetaDelta`](DLMF/Theta/PowerSeries.lean#L33) (definition). Iterated sum, inner over m (Eisenstein order); index k = 2j.
- [20.6.E7](https://dlmf.nist.gov/20.6.E7): [`DLMF.Theta.thetaAlpha`](DLMF/Theta/PowerSeries.lean#L40) (definition). Iterated sum.
- [20.6.E8](https://dlmf.nist.gov/20.6.E8): [`DLMF.Theta.thetaBeta`](DLMF/Theta/PowerSeries.lean#L45) (definition). Iterated sum.
- [20.6.E9](https://dlmf.nist.gov/20.6.E9): [`DLMF.Theta.thetaGamma`](DLMF/Theta/PowerSeries.lean#L50) (definition). Iterated sum.
- [20.6.E10](https://dlmf.nist.gov/20.6.E10): [`DLMF.Theta.thetaAlpha_thetaBeta_eq`](DLMF/Theta/PowerSeries.lean#L304) (proved). Both identities, j ≥ 1, Im τ > 0 (numerically checked for j = 1, 2).

## [§20.7 Identities](https://dlmf.nist.gov/20.7)

- [20.7.E1](https://dlmf.nist.gov/20.7.E1): [`DLMF.Theta.jacobiTheta_sq_three_three`](DLMF/Theta/Identities.lean#L418) (proved). Im τ > 0.
- [20.7.E2](https://dlmf.nist.gov/20.7.E2): [`DLMF.Theta.jacobiTheta_sq_three_four`](DLMF/Theta/Identities.lean#L428) (proved).
- [20.7.E3](https://dlmf.nist.gov/20.7.E3): [`DLMF.Theta.jacobiTheta_sq_two_four`](DLMF/Theta/Identities.lean#L439) (proved).
- [20.7.E4](https://dlmf.nist.gov/20.7.E4): [`DLMF.Theta.jacobiTheta_sq_two_three`](DLMF/Theta/Identities.lean#L449) (proved).
- [20.7.E5](https://dlmf.nist.gov/20.7.E5): [`DLMF.Theta.jacobiThetaNull_fourth_power`](DLMF/Theta/Identities.lean#L80) (proved modulo admitted lemmas). Derived from 20.7.E1 at z = 0 (inherits that admission).
- [20.7.E6](https://dlmf.nist.gov/20.7.E6): [`DLMF.Theta.jacobiThetaOneTau_add_mul_sub`](DLMF/Theta/Identities.lean#L466) (proved).
- [20.7.E7](https://dlmf.nist.gov/20.7.E7): [`DLMF.Theta.jacobiThetaTwoTau_add_mul_sub`](DLMF/Theta/Identities.lean#L483) (proved).
- [20.7.E8](https://dlmf.nist.gov/20.7.E8): [`DLMF.Theta.jacobiThetaThreeTau_add_mul_sub`](DLMF/Theta/Identities.lean#L500) (proved).
- [20.7.E9](https://dlmf.nist.gov/20.7.E9): [`DLMF.Theta.jacobiThetaFourTau_add_mul_sub`](DLMF/Theta/Identities.lean#L517) (proved).
- [20.7.E10](https://dlmf.nist.gov/20.7.E10): [`DLMF.Theta.jacobiThetaOneTau_two_mul`](DLMF/Theta/Identities.lean#L536) (proved).
- [20.7.E11](https://dlmf.nist.gov/20.7.E11): [`DLMF.Theta.jacobiTheta_reduction_two_mul`](DLMF/Theta/Identities.lean#L556) (proved); [`DLMF.Elliptic.Real.jacobiThetaThreeNullQ_mul_jacobiThetaFourNullQ`](DLMF/Elliptic/ThetaAGM.lean#L131) (proved). q² ↔ 2τ. **Corrected** (formalization): nonvanishing hypotheses on the denominators θ₁(2z|2τ), θ₄(2z|2τ), since the printed quotient is false at their zeros under x/0 = 0. The z = 0 real-nome case is the existing `Real.jacobiThetaThreeNullQ_mul_jacobiThetaFourNullQ`.
- [20.7.E12](https://dlmf.nist.gov/20.7.E12): [`DLMF.Theta.jacobiTheta_reduction_two_tau`](DLMF/Theta/Identities.lean#L572) (proved). q² ↔ 2τ. **Corrected** (formalization): nonvanishing hypotheses on θ₁(z|τ), θ₂(z|τ), since the quotients are false at their zeros under x/0 = 0.
- [20.7.E13](https://dlmf.nist.gov/20.7.E13): [`DLMF.Theta.jacobiThetaOneTau_mul_watson`](DLMF/Theta/Identities.lean#L589) (proved). q² ↔ 2τ.
- [20.7.E14](https://dlmf.nist.gov/20.7.E14): [`DLMF.Theta.jacobiThetaThreeTau_mul_watson`](DLMF/Theta/Identities.lean#L597) (proved). q² ↔ 2τ.
- [20.7.E15](https://dlmf.nist.gov/20.7.E15): [`DLMF.Theta.thetaLandenA`](DLMF/Theta/Identities.lean#L607) (definition). Definition A(τ).
- [20.7.E16](https://dlmf.nist.gov/20.7.E16): [`DLMF.Theta.jacobiThetaOneTau_landen`](DLMF/Theta/Identities.lean#L611) (proved).
- [20.7.E17](https://dlmf.nist.gov/20.7.E17): [`DLMF.Theta.jacobiThetaTwoTau_landen`](DLMF/Theta/Identities.lean#L619) (proved).
- [20.7.E18](https://dlmf.nist.gov/20.7.E18): [`DLMF.Theta.jacobiThetaThreeTau_landen`](DLMF/Theta/Identities.lean#L627) (proved).
- [20.7.E19](https://dlmf.nist.gov/20.7.E19): [`DLMF.Theta.jacobiThetaFourTau_landen`](DLMF/Theta/Identities.lean#L635) (proved).
- [20.7.E20](https://dlmf.nist.gov/20.7.E20): [`DLMF.Theta.thetaLandenB`](DLMF/Theta/Identities.lean#L643) (definition). Definition B(τ).
- [20.7.E21](https://dlmf.nist.gov/20.7.E21): [`DLMF.Theta.jacobiThetaOneTau_landen_four`](DLMF/Theta/Identities.lean#L648) (proved).
- [20.7.E22](https://dlmf.nist.gov/20.7.E22): [`DLMF.Theta.jacobiThetaTwoTau_landen_four`](DLMF/Theta/Identities.lean#L673) (proved).
- [20.7.E23](https://dlmf.nist.gov/20.7.E23): [`DLMF.Theta.jacobiThetaThreeTau_landen_four`](DLMF/Theta/Identities.lean#L701) (proved).
- [20.7.E24](https://dlmf.nist.gov/20.7.E24): [`DLMF.Theta.jacobiThetaFourTau_landen_four`](DLMF/Theta/Identities.lean#L729) (proved).
- [20.7.E25](https://dlmf.nist.gov/20.7.E25): [`DLMF.Theta.hasDerivAt_jacobiThetaTwoTau_div_four`](DLMF/Theta/Identities.lean#L889) (proved). **Corrected** (formalization): `HasDerivAt` at points with θ₄(z|τ) ≠ 0, where the quotient has no pole.
- [20.7.E26](https://dlmf.nist.gov/20.7.E26): [`DLMF.Theta.jacobiThetaOneTau_add_one`](DLMF/Theta/Identities.lean#L801) (proved). All τ, from the series.
- [20.7.E27](https://dlmf.nist.gov/20.7.E27): [`DLMF.Theta.jacobiThetaTwoTau_add_one`](DLMF/Theta/Identities.lean#L792) (proved). All τ.
- [20.7.E28](https://dlmf.nist.gov/20.7.E28): [`DLMF.Theta.jacobiThetaThreeTau_add_one`](DLMF/Theta/Identities.lean#L762) (proved); Mathlib: [`jacobiTheta₂_add_right`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=jacobiTheta₂_add_right#doc) (partial: only the period 2 in τ, i.e. 20.7.28 followed by 20.7.29); Mathlib: [`jacobiTheta_two_add`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=jacobiTheta_two_add#doc) (partial: θ₃(0|τ + 2) = θ₃(0|τ), i.e. 20.7.28 followed by 20.7.29 at z = 0). All τ.
- [20.7.E29](https://dlmf.nist.gov/20.7.E29): [`DLMF.Theta.jacobiThetaFourTau_add_one`](DLMF/Theta/Identities.lean#L778) (proved). All τ.
- [20.7.E30](https://dlmf.nist.gov/20.7.E30): [`DLMF.Theta.jacobiThetaOneTau_neg_inv`](DLMF/Theta/Identities.lean#L997) (proved). Im τ > 0, principal square root; from 20.7.E31 and 20.2.E11.
- [20.7.E31](https://dlmf.nist.gov/20.7.E31): [`DLMF.Theta.jacobiThetaTwoTau_neg_inv`](DLMF/Theta/Identities.lean#L983) (proved). Im τ > 0; from 20.7.E32 and the half-period shifts.
- [20.7.E32](https://dlmf.nist.gov/20.7.E32): [`DLMF.Theta.jacobiThetaThreeTau_neg_inv`](DLMF/Theta/Identities.lean#L957) (proved); [`DLMF.Elliptic.jacobiThetaThreeTau_zero_neg_recip`](DLMF/Elliptic/Theta.lean#L146) (proved); Mathlib: [`jacobiTheta₂_functional_equation`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=jacobiTheta₂_functional_equation#doc) (exact in Mathlib's argument z/π: θ₃(z|τ) = (-iτ)^{-1/2} exp(iτ'z²/π) θ₃(zτ'|τ');  principal square root; the local form is DLMF.Theta.jacobiThetaThreeTau_neg_inv); Mathlib: [`jacobiTheta_S_smul`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=jacobiTheta_S_smul#doc) (special case z = 0, τ ∈ ℍ: θ₃(0|-1/τ) = (-iτ)^{1/2} θ₃(0|τ)). Im τ > 0; from Mathlib’s `jacobiTheta₂_functional_equation`.
- [20.7.E33](https://dlmf.nist.gov/20.7.E33): [`DLMF.Theta.jacobiThetaFourTau_neg_inv`](DLMF/Theta/Identities.lean#L970) (proved). Im τ > 0; from 20.7.E32 and 20.2.E12.
- [20.7.E34](https://dlmf.nist.gov/20.7.E34): [`DLMF.Theta.jacobiTheta_reduction_iq_sq`](DLMF/Theta/Identities.lean#L1136) (proved); [`DLMF.Theta.jacobiTheta_reduction_iq_rectangular`](DLMF/Theta/Identities.lean#L1256) (proved); [`DLMF.Theta.jacobiTheta_reduction_iq_eta`](DLMF/Theta/Identities.lean#L1278) (proved). **Corrected**: with principal √ the printed identity holds only up to sign. iq ↔ τ + 1/2, q² ↔ 2τ. With principal √ and i^{-1/4} = e^{-iπ/8} the printed form fails e.g. at τ = −2.19 + 1.29i, 2.03 + 0.90i, −2.85 + 0.88i. Acquired: the squared identity for all Im τ > 0, the printed form for τ = it, and the full-domain form with the explicit root e^{-iπ/8} η(τ)η(4τ)/η(2τ) (Mathlib `ModularForm.eta`; mpmath: no failure at 200 random (z, τ)). Nonvanishing hypotheses on the denominators.

## [§20.8 Watson’s Expansions](https://dlmf.nist.gov/20.8)

- [20.8.E1](https://dlmf.nist.gov/20.8.E1): [`DLMF.Theta.jacobiTheta_watson_expansion`](DLMF/Theta/Identities.lean#L1303) (admitted). **Corrected** (formalization): hypothesis θ₂(z|τ) ≠ 0, since the left side is false at the zeros of θ₂ under x/0 = 0; `HasSum` over ℤ.

## [§20.9 Relations to Other Functions](https://dlmf.nist.gov/20.9)

- [20.9.E1](https://dlmf.nist.gov/20.9.E1): [`DLMF.Theta.thetaModulusK`](DLMF/Theta/Relations.lean#L52) (definition). Definition k(τ); k′ = θ₄²/θ₃² as a companion definition.
- [20.9.E2](https://dlmf.nist.gov/20.9.E2): [`DLMF.Theta.compEllIntK_eq_jacobiThetaThreeNullTau`](DLMF/Theta/Relations.lean#L82) (proved); [`DLMF.Theta.compEllIntKk_eq_jacobiThetaThreeNullTau_fundamental`](DLMF/Theta/Relations.lean#L103) (admitted); [`DLMF.Elliptic.Real.compEllIntKm_eq_jacobiThetaThreeNullQ`](DLMF/Elliptic/ThetaAGM.lean#L329) (proved). **Corrected**: with the principal complex K the printed identity holds only for τ in the translates F + 2n of the Γ(2) fundamental region F = {|Re τ| < 1, |τ ∓ 1/2| > 1/2} (fails at 58 of 308 random τ). Rectangular case τ = it (real `Real.compEllIntKm`), also K′ = −iτK; full-domain form with the principal `JacobiElliptic.compEllIntKk`: K = (π/2)θ₃² and K′ = −iτK on F, K = (π/2)θ₃² on every F + 2n (mpmath: no failure at 676 points of F; region agrees exactly with the validity set at 500 random τ). The existing real-nome theorem `Real.compEllIntKm_eq_jacobiThetaThreeNullQ` is the first equation with m = 1 − θ₄⁴/θ₃⁴.
- [20.9.E3](https://dlmf.nist.gov/20.9.E3): [`DLMF.Theta.carlsonRF_jacobiTheta`](DLMF/Theta/Relations.lean#L123) (admitted); [`DLMF.Theta.carlsonRF_jacobiTheta_rect`](DLMF/Theta/Relations.lean#L139) (admitted); [`DLMF.Theta.carlsonRF_jacobiTheta_eventually`](DLMF/Theta/Relations.lean#L157) (admitted). **Corrected** (domain): the printed identity needs a branch condition (continuation of R_F from z = 0). The left side is π-periodic and even, the right side is not; numerically the printed identity fails at z = 1.6, 2, 2.5 (τ = 0.8i). Acquired for τ = it and real 0 < |z| ≤ π/2; for τ = it and complex z ≠ 0 in the open period rectangle |Re z| < π/2, |Im z| < πt/2 (mpmath: no failure at 3500 points); and for general τ and z in a punctured neighbourhood of 0. R_F is the complex Chapter 19 `symEllIntRF`.
- [20.9.E4](https://dlmf.nist.gov/20.9.E4): [`DLMF.Theta.carlsonRF_zero_jacobiThetaNull`](DLMF/Theta/Relations.lean#L175) (proved). τ = it.
- [20.9.E5](https://dlmf.nist.gov/20.9.E5): [`DLMF.Theta.exp_carlsonRF_ratio_eq_nome`](DLMF/Theta/Relations.lean#L218) (proved). τ = it, q = e^{−πt}.

## [§20.10 Integrals](https://dlmf.nist.gov/20.10)

- [20.10.E1](https://dlmf.nist.gov/20.10.E1): [`DLMF.Theta.mellin_jacobiThetaTwoNullTau`](DLMF/Theta/Integrals.lean#L180) (proved). Re s > 1; integrability is part of the conclusion (numerically checked at s = 2.5 + 0.3i).
- [20.10.E2](https://dlmf.nist.gov/20.10.E2): [`DLMF.Theta.mellin_jacobiThetaThreeNullTau_sub_one`](DLMF/Theta/Integrals.lean#L253) (proved). Re s > 1.
- [20.10.E3](https://dlmf.nist.gov/20.10.E3): [`DLMF.Theta.mellin_one_sub_jacobiThetaFourNullTau`](DLMF/Theta/Integrals.lean#L570) (proved); [`DLMF.Theta.mellin_one_sub_jacobiThetaFourNullTau_one`](DLMF/Theta/Integrals.lean#L585) (proved). **Corrected** (removable point): Re s > 0, s ≠ 1, plus the removable value ∫(1 − θ₄(0|ix²))dx = ln 2 at s = 1 (Mathlib’s totalized ζ(1) would make the printed right side 0). Numerically checked at s = 0.6 + 0.2i, 1.5, 3, 2.5 + 0.3i and at s = 1.
- [20.10.E4](https://dlmf.nist.gov/20.10.E4): [`DLMF.Theta.laplace_jacobiThetaOneTau`](DLMF/Theta/Integrals.lean#L607) (admitted). Re s > 0, ℓ > 0, |Re β| + |Im β| ≤ ℓ, principal √s; both integrals and integrability (numerically checked at two choices of ℓ, β, s).
- [20.10.E5](https://dlmf.nist.gov/20.10.E5): [`DLMF.Theta.laplace_jacobiThetaThreeTau`](DLMF/Theta/Integrals.lean#L626) (admitted). As 20.10.E4.

## [§20.11 Generalizations and Analogs](https://dlmf.nist.gov/20.11)

- [20.11.E1](https://dlmf.nist.gov/20.11.E1): [`DLMF.Theta.thetaGaussSum`](DLMF/Theta/Generalizations.lean#L35) (definition). Definition G(m,n) for m ∈ ℤ, n ∈ ℕ.
- [20.11.E2](https://dlmf.nist.gov/20.11.E2): [`DLMF.Theta.thetaGaussSum_reciprocity`](DLMF/Theta/Generalizations.lean#L41) (admitted). m, n > 0 coprime, mn even; the second equality is proved, the reciprocity is admitted.
- [20.11.E3](https://dlmf.nist.gov/20.11.E3): [`DLMF.Theta.ramanujanThetaF`](DLMF/Theta/Generalizations.lean#L61) (definition). Definition f(a,b) (integer exponents).
- [20.11.E4](https://dlmf.nist.gov/20.11.E4): [`DLMF.Theta.ramanujanThetaF_eq_jacobiThetaThreeTau`](DLMF/Theta/Generalizations.lean#L66) (proved). All τ, termwise from the ℤ-series.
- [20.11.E5](https://dlmf.nist.gov/20.11.E5): [`DLMF.Theta.ordinaryHypergeometric_half_half_one_thetaModulusK`](DLMF/Theta/Generalizations.lean#L144) (proved). Rectangular case τ = it, Mathlib’s series ₂F₁.
- [20.11.E6](https://dlmf.nist.gov/20.11.E6): [`DLMF.Theta.combinedTheta`](DLMF/Theta/Generalizations.lean#L169) (definition); [`DLMF.Theta.combinedTheta_m_one`](DLMF/Theta/Generalizations.lean#L177) (proved). One definition `combinedTheta` covers 20.11.6–20.11.8; the three printed cases are proved as rewriting lemmas.
- [20.11.E7](https://dlmf.nist.gov/20.11.E7): [`DLMF.Theta.combinedTheta_one_n`](DLMF/Theta/Generalizations.lean#L184) (proved). Proved case lemma.
- [20.11.E8](https://dlmf.nist.gov/20.11.E8): [`DLMF.Theta.combinedTheta_m_n`](DLMF/Theta/Generalizations.lean#L191) (proved). Proved case lemma.
- [20.11.E9](https://dlmf.nist.gov/20.11.E9): [`DLMF.Theta.combinedTheta_symmetry`](DLMF/Theta/Generalizations.lean#L198) (proved). **Corrected** (formalization): at points with θ₁(z), θ_m(z), θ_n(z) ≠ 0, since the quotient identities are false at the zeros under x/0 = 0; given nonzero normalizing constants (`th20_combinedConst_ne_zero` proves them for Im τ > 0).

## Excluded numbered equations

- [20.13.E1](https://dlmf.nist.gov/20.13.E1)–[20.13.E5](https://dlmf.nist.gov/20.13.E5): excluded: application (§20.13 Physical Applications); see the prose list for the mathematical content.
- [20.15.E1](https://dlmf.nist.gov/20.15.E1): excluded: computation (§20.15 Tables). The modular angle `sin α = k` is the modulus 20.9.E1.

## Analytical prose and exclusions

The paragraph links record mathematical assertions and conventions as well as explicit exclusions.
A bibliographic pointer with no stated formula is not converted into an opaque axiom.

- [20.1.p1](https://dlmf.nist.gov/20.1#p1): Cross-reference to the general notation; no assertion.
- [20.1.p2](https://dlmf.nist.gov/20.1#p2): Notation: `z ∈ ℂ`, lattice parameter `Im τ > 0`, nome `q = e^{iπτ}`, `q^α = e^{iαπτ}`. Recorded in the module docstring of [DLMF/Theta/Basic.lean](DLMF/Theta/Basic.lean): statements use the lattice form, so `q^α` is always `e^{iαπτ}`; the nome forms [`DLMF.Theta.jacobiThetaOneQ`](DLMF/Theta/Basic.lean) … `jacobiThetaFourQ` (definitions) use the principal `q^{1/4}` and agree with the lattice form for `-1 < Re τ ≤ 1` ([`DLMF.Theta.jacobiThetaOneQ_cexp`](DLMF/Theta/Basic.lean), [`DLMF.Theta.jacobiThetaTwoQ_cexp`](DLMF/Theta/Basic.lean), proved) and for all τ for `θ₃, θ₄` ([`DLMF.Theta.jacobiThetaThreeQ_cexp`](DLMF/Theta/Basic.lean), [`DLMF.Theta.jacobiThetaFourQ_cexp`](DLMF/Theta/Basic.lean), proved). The quotient notation `S₁/S₂` is explanatory.
- [20.1.p3](https://dlmf.nist.gov/20.1#p3): The four functions `θⱼ(z|τ) = θⱼ(z,q)` are the project definitions `DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`; the indexed family [`DLMF.Theta.jacobiThetaTau`](DLMF/Theta/Basic.lean#L88) (definition) gives `θⱼ` for `j = 1,…,4`.
- [20.1.p4](https://dlmf.nist.gov/20.1#p4): Primes denote `z`-derivatives: `deriv`/`iteratedDeriv` in `z`; [`DLMF.Theta.jacobiThetaOneDerivNullTau`](DLMF/Theta/Basic.lean#L73) (definition) is `θ₁'(0|τ)`; theta constants `jacobiThetaTwoNullTau`, `jacobiThetaThreeNullTau`, `jacobiThetaFourNullTau` (definitions).
- [20.1.Px1.p1](https://dlmf.nist.gov/20.1#Px1.p1): Jacobi's original notation; notational, not acquired.
- [20.1.Px1.p2](https://dlmf.nist.gov/20.1#Px1.p2): Neville's notation; notational. Neville's normalized quotients are covered by Carlson's combined functions [`DLMF.Theta.combinedTheta`](DLMF/Theta/Generalizations.lean) (§20.11(v)).
- [20.1.Px1.p3](https://dlmf.nist.gov/20.1#Px1.p3): McKean–Moll `ϑⱼ(z|τ) = θⱼ(πz|τ)`; this is Mathlib's convention for `jacobiTheta₂` (see [DLMF/Theta/MathlibCoverage.lean](DLMF/Theta/MathlibCoverage.lean)).
- [20.1.Px1.p4](https://dlmf.nist.gov/20.1#Px1.p4): Bibliographic pointer; no assertion.
- [20.2.i.p1](https://dlmf.nist.gov/20.2#i.p1): Introduces 20.2.1–20.2.4; see the numbered entries.
- [20.2.i.p2](https://dlmf.nist.gov/20.2#i.p2): Termwise-differentiated Fourier series: [`DLMF.Theta.jacobiThetaTau_deriv_hasSum`](DLMF/Theta/Basic.lean#L659) (proved), Im τ > 0.
- [20.2.ii.p1](https://dlmf.nist.gov/20.2#ii.p1): Acquired: [`DLMF.Theta.jacobiThetaTau_add_two_pi`](DLMF/Theta/Basic.lean#L325) (proved); [`DLMF.Theta.differentiable_jacobiThetaTau`](DLMF/Theta/Basic.lean#L351) (proved); [`DLMF.Theta.differentiableAt_jacobiThetaThreeTau_tau`](DLMF/Theta/Basic.lean#L372) (proved); [`DLMF.Theta.differentiableAt_jacobiThetaFourTau_tau`](DLMF/Theta/Basic.lean#L378) (proved); [`DLMF.Theta.jacobiThetaOneTau_div_sin_analytic`](DLMF/Theta/Basic.lean#L548) (proved); [`DLMF.Theta.jacobiThetaThreeTau_natural_boundary`](DLMF/Theta/Basic.lean#L574) (admitted); [`DLMF.Elliptic.jacobiThetaThreeTau_neg`](DLMF/Elliptic/Theta.lean#L75) (proved); [`DLMF.Elliptic.jacobiThetaFourTau_neg`](DLMF/Elliptic/Theta.lean#L108) (proved); [`DLMF.Elliptic.jacobiThetaTwoTau_neg`](DLMF/Elliptic/Theta.lean#L124) (proved); [`DLMF.Elliptic.jacobiThetaOneTau_neg`](DLMF/Elliptic/Theta.lean#L139) (proved); Mathlib: [`jacobiTheta₂_neg_left`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=jacobiTheta₂_neg_left#doc) (θ₃ is even in z); Mathlib: [`differentiableAt_jacobiTheta₂_fst`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=differentiableAt_jacobiTheta₂_fst#doc) (θ₃(·|τ) is entire in z for Im τ > 0); Mathlib: [`differentiableAt_jacobiTheta₂_snd`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=differentiableAt_jacobiTheta₂_snd#doc) (θ₃(z|·) is analytic in τ on Im τ > 0); Mathlib: [`differentiableAt_jacobiTheta`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=differentiableAt_jacobiTheta#doc) (θ₃(0|·) is analytic in τ on Im τ > 0). Entire in `z`, period `2π`, `θ₁` odd and the others even (all proved); analyticity in `τ` of `θ₁…θ₄` proved (`differentiableAt_jacobiThetaOneTau_tau`, `…TwoTau_tau`, `…ThreeTau_tau`, `…FourTau_tau`); the analytic extension of `θ₁/sin z`, `θ₂/cos z` through the zeros of `sin z`, `cos z` and the natural boundary `Im τ = 0` are admitted. The analytic dependence on `q` for `|q| < 1` is the composition with `τ ↦ e^{iπτ}`; the statement that the natural boundary in `q` is `|q| = 1` is the same assertion and is not stated separately.
- [20.2.ii.p2](https://dlmf.nist.gov/20.2#ii.p2): Fundamental parallelogram and lattice points `z_{m,n}`; 20.2.E5 definition `latticePoint`. The figure is excluded: graphics.
- [20.2.iii.p1](https://dlmf.nist.gov/20.2#iii.p1): Introduces 20.2.10–20.2.14; see the numbered entries.
- [20.2.iv.p1](https://dlmf.nist.gov/20.2#iv.p1): Acquired: [`DLMF.Theta.jacobiThetaTau_eq_zero_iff`](DLMF/Theta/Basic.lean#L930) (proved). The zeros are exactly the stated lattice translates (both directions), Im τ > 0; proved from the triple product. Nonvanishing of the theta constants follows: [`DLMF.Theta.jacobiThetaNullTau_ne_zero`](DLMF/Theta/Basic.lean#L974) (proved).
- [20.2.i](https://dlmf.nist.gov/20.2.i): [`DLMF.Theta.jacobiThetaTau_deriv_hasSum`](DLMF/Theta/Basic.lean#L659) (proved).
- [20.2.ii](https://dlmf.nist.gov/20.2.ii): [`DLMF.Elliptic.jacobiThetaFourTau_neg`](DLMF/Elliptic/Theta.lean#L108) (proved); [`DLMF.Elliptic.jacobiThetaOneTau_neg`](DLMF/Elliptic/Theta.lean#L139) (proved); [`DLMF.Elliptic.jacobiThetaThreeTau_neg`](DLMF/Elliptic/Theta.lean#L75) (proved); [`DLMF.Elliptic.jacobiThetaTwoTau_neg`](DLMF/Elliptic/Theta.lean#L124) (proved); [`DLMF.Theta.differentiableAt_jacobiThetaFourTau_tau`](DLMF/Theta/Basic.lean#L378) (proved); [`DLMF.Theta.differentiableAt_jacobiThetaThreeTau_tau`](DLMF/Theta/Basic.lean#L372) (proved); [`DLMF.Theta.differentiable_jacobiThetaTau`](DLMF/Theta/Basic.lean#L351) (proved); [`DLMF.Theta.jacobiThetaOneTau_div_sin_analytic`](DLMF/Theta/Basic.lean#L548) (proved); [`DLMF.Theta.jacobiThetaTau_add_two_pi`](DLMF/Theta/Basic.lean#L325) (proved); [`DLMF.Theta.jacobiThetaThreeTau_natural_boundary`](DLMF/Theta/Basic.lean#L574) (admitted); Mathlib: [`jacobiTheta₂_neg_left`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂_neg_left); Mathlib: [`differentiableAt_jacobiTheta₂_fst`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#differentiableAt_jacobiTheta₂_fst); Mathlib: [`differentiableAt_jacobiTheta₂_snd`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#differentiableAt_jacobiTheta₂_snd).
- [20.2.iv](https://dlmf.nist.gov/20.2.iv): [`DLMF.Theta.jacobiThetaTau_eq_zero_iff`](DLMF/Theta/Basic.lean#L930) (proved).
- [20.4.i.p1](https://dlmf.nist.gov/20.4#i.p1), [20.4.Px1.p1](https://dlmf.nist.gov/20.4#Px1.p1), [20.4.ii.p1](https://dlmf.nist.gov/20.4#ii.p1): Introduce the numbered equations; see the numbered entries.
- [20.5.i.p1](https://dlmf.nist.gov/20.5#i.p1), [20.5.i.p2](https://dlmf.nist.gov/20.5#i.p2), [20.5.Px1.p1](https://dlmf.nist.gov/20.5#Px1.p1): Introduce 20.5.1–20.5.9; the substitution `p = e^{iπz}` is part of 20.5.E9.
- [20.5.ii.p1](https://dlmf.nist.gov/20.5#ii.p1), [20.5.ii.p2](https://dlmf.nist.gov/20.5#ii.p2): The strip conditions `|Im z| < π Im τ` and `|Im z| < π Im τ/2` are hypotheses of 20.5.E10–E13.
- [20.5.ii.p3](https://dlmf.nist.gov/20.5#ii.p3): Acquired: [`DLMF.Theta.jacobiTheta_logDeriv_series_uniform`](DLMF/Theta/Products.lean#L1026) (proved). Absolute and locally uniform convergence, in Weierstrass M-test form on compact subsets of the strips.
- [20.5.iii.p1](https://dlmf.nist.gov/20.5#iii.p1): Introduces 20.5.14–20.5.17.
- [20.5.iii.p2](https://dlmf.nist.gov/20.5#iii.p2): Acquired: [`DLMF.Theta.jacobiTheta_doubleProd_not_absolutely_convergent`](DLMF/Theta/Products.lean#L1495) (proved). The double products are not absolutely convergent (lattice sum of `|z/((m+nτ)π)|` diverges); the Eisenstein order is built into 20.5.E14–E17.
- [20.5.ii](https://dlmf.nist.gov/20.5.ii): [`DLMF.Theta.jacobiTheta_logDeriv_series_uniform`](DLMF/Theta/Products.lean#L1026) (proved).
- [20.5.iii](https://dlmf.nist.gov/20.5.iii): [`DLMF.Theta.jacobiTheta_doubleProd_not_absolutely_convergent`](DLMF/Theta/Products.lean#L1495) (proved).
- [20.6.p1](https://dlmf.nist.gov/20.6#p1): The hypothesis 20.6.1 and the coefficient definitions are numbered entries. Acquired: [`DLMF.Theta.thetaDelta_hasSum_lattice`](DLMF/Theta/PowerSeries.lean#L395) (proved); [`DLMF.Theta.thetaDelta_two_not_summable`](DLMF/Theta/PowerSeries.lean#L421) (proved). The remark that the order of summation matters only for `j = 1` is acquired as absolute summability for `2j ≥ 4` and non-summability for `j = 1`. The relation `δ_{2n} = c_n/(2n − 1)` (`n ≥ 2`) to the Weierstrass Laurent coefficients of §23.9 is left to the Chapter 23 acquisition (it needs `c_n`).
- [20.6](https://dlmf.nist.gov/20.6): [`DLMF.Theta.thetaDelta_hasSum_lattice`](DLMF/Theta/PowerSeries.lean#L395) (proved); [`DLMF.Theta.thetaDelta_two_not_summable`](DLMF/Theta/PowerSeries.lean#L421) (proved).
- [20.7.i.p1](https://dlmf.nist.gov/20.7#i.p1), [20.7.i.p2](https://dlmf.nist.gov/20.7#i.p2): Introduce 20.7.1–20.7.5.
- [20.7.i.p3](https://dlmf.nist.gov/20.7#i.p3), [20.7.iii.p2](https://dlmf.nist.gov/20.7#iii.p2), [20.7.vii.p2](https://dlmf.nist.gov/20.7#vii.p2): Bibliographic pointers (Carlson 2011); no assertion.
- [20.7.ii.p1](https://dlmf.nist.gov/20.7#ii.p1): Introduces 20.7.6–20.7.9; references.
- [20.7.ii.p2](https://dlmf.nist.gov/20.7#ii.p2): Remark on Carlson's symmetric recasting; qualitative, no formula. The combined functions of §20.11(v) are acquired.
- [20.7.iii.p1](https://dlmf.nist.gov/20.7#iii.p1), [20.7.iv.p1](https://dlmf.nist.gov/20.7#iv.p1), [20.7.v.p1](https://dlmf.nist.gov/20.7#v.p1), [20.7.vi.p1](https://dlmf.nist.gov/20.7#vi.p1)–[20.7.vi.p4](https://dlmf.nist.gov/20.7#vi.p4), [20.7.viii.p1](https://dlmf.nist.gov/20.7#viii.p1), [20.7.ix.p1](https://dlmf.nist.gov/20.7#ix.p1): Introduce the numbered equations; see the numbered entries.
- [20.7.vii.p1](https://dlmf.nist.gov/20.7#vii.p1): The eleven further identities for permutations of the theta functions are only cited (Lawden); not stated in DLMF, not acquired.
- [20.7.viii.p2](https://dlmf.nist.gov/20.7#viii.p2): `τ' = −1/τ` and principal square roots: built into 20.7.E30–E33 (`(-I * τ) ^ (1 / 2 : ℂ)` is Mathlib's principal power). The pointer to general modular transformations (§23.15, Rademacher) is a cross-reference.
- [20.8.p1](https://dlmf.nist.gov/20.8#p1): Introduces 20.8.1; further expansions are only cited.
- [20.9.i.p1](https://dlmf.nist.gov/20.9#i.p1), [20.9.i.p2](https://dlmf.nist.gov/20.9#i.p2): Introduce 20.9.1–20.9.5; the reference to 22.2.1 (`k` via theta constants) belongs to the Chapter 22 acquisition.
- [20.9.ii.p1](https://dlmf.nist.gov/20.9#ii.p1): Cross-reference to §§22.2 and 23.6(i) (theta quotients for Jacobian and Weierstrass functions); acquired in the Chapter 22 and 23 modules, which import `DLMF.Theta.Basic`.
- [20.9.ii.p2](https://dlmf.nist.gov/20.9#ii.p2): Acquired: [`DLMF.Theta.thetaModulusK_inversion`](DLMF/Theta/Relations.lean#L232) (proved); [`DLMF.Theta.thetaModulusK_sq_modular`](DLMF/Theta/Relations.lean#L176) (proved modulo admitted lemmas). Jacobi's inversion problem: existence and uniqueness of `t > 0` with `k(it) = k` for `0 < k < 1` (admitted).
- [20.9.ii.p3](https://dlmf.nist.gov/20.9#ii.p3): `k²` as the elliptic modular function: invariance under `τ ↦ τ + 2` and `λ(−1/τ) = 1 − λ(τ)` (proved from 20.7.E26–E33, modulo the admitted 20.7.E1 through 20.7.E5).
- [20.9.iii.p1](https://dlmf.nist.gov/20.9#iii.p1): Cross-references to the zeta function; the Mellin transforms 20.10.E1–E3 carry the content.
- [20.9.ii](https://dlmf.nist.gov/20.9.ii): [`DLMF.Theta.thetaModulusK_inversion`](DLMF/Theta/Relations.lean#L232) (proved); [`DLMF.Theta.thetaModulusK_sq_modular`](DLMF/Theta/Relations.lean#L256) (proved).
- [20.10.i.p1](https://dlmf.nist.gov/20.10#i.p1), [20.10.ii.p1](https://dlmf.nist.gov/20.10#ii.p1): Hypotheses `Re s > 1`, `Re s > 0`, `ℓ > 0`, `|Re β| + |Im β| ≤ ℓ` are built into 20.10.E1–E5.
- [20.10.i.p2](https://dlmf.nist.gov/20.10#i.p2), [20.10.ii.p2](https://dlmf.nist.gov/20.10#ii.p2), [20.10.iii.p1](https://dlmf.nist.gov/20.10#iii.p1): Bibliographic pointers; no assertion.
- [20.11.i.p1](https://dlmf.nist.gov/20.11#i.p1): Gauss sum definition and reciprocity: 20.11.E1–E2; "discrete analog of theta/Poisson" is a remark.
- [20.11.ii.p1](https://dlmf.nist.gov/20.11#ii.p1): Acquired: [`DLMF.Theta.summable_ramanujanThetaF`](DLMF/Theta/Generalizations.lean#L114) (proved). Ramanujan's `f(a,b)`: 20.11.E3–E4; absolute convergence for `|ab| < 1` is stated separately.
- [20.11.ii.p2](https://dlmf.nist.gov/20.11#ii.p2): Qualitative remark on `q`-identities with references; no formula.
- [20.11.iii.p1](https://dlmf.nist.gov/20.11#iii.p1): Remark that `q` is tied to `k` (Jacobi inversion); covered by `thetaModulusK_inversion`.
- [20.11.iii.p2](https://dlmf.nist.gov/20.11#iii.p2): 20.11.E5. The analogous changes of base for `₂F₁(1/3,2/3;1;k²)`, `₂F₁(1/4,3/4;1;k²)`, `₂F₁(1/6,5/6;1;k²)` are mentioned without formulas (Berndt et al.); not acquired.
- [20.11.iv.p1](https://dlmf.nist.gov/20.11#iv.p1): Theta functions with characteristics: cross-reference to Chapter 21 (multidimensional theta functions); acquired there.
- [20.11.v.p1](https://dlmf.nist.gov/20.11#v.p1), [20.11.v.p2](https://dlmf.nist.gov/20.11#v.p2): Definitions 20.11.6–20.11.8 and identity 20.11.9.
- [20.11.v.p3](https://dlmf.nist.gov/20.11#v.p3), [20.11.v.p4](https://dlmf.nist.gov/20.11#v.p4): Qualitative remark (sets of twelve equations reduce to three) and reference; no formula.
- [20.11.ii](https://dlmf.nist.gov/20.11.ii): [`DLMF.Theta.summable_ramanujanThetaF`](DLMF/Theta/Generalizations.lean#L114) (proved).
- [20.3](https://dlmf.nist.gov/20.3) (20.3.ii.p1, 20.3.iii.p1 and all figures): excluded: graphics.
- [20.12.i.p1](https://dlmf.nist.gov/20.12#i.p1), [20.12.i.p2](https://dlmf.nist.gov/20.12#i.p2), [20.12.ii.p1](https://dlmf.nist.gov/20.12#ii.p1), [20.12.ii.p2](https://dlmf.nist.gov/20.12#ii.p2): excluded: application. Mathematical content for a later decision: θ₃(0,q) and sums of squares (§27.13(iv)); the triple product and Euler's pentagonal number theorem; the embedding `z ↦ (θ₁(2z|τ) : θ₂(2z|τ) : θ₃(2z|τ) : θ₄(2z|τ))` of the torus `ℂ/(ℤ + τℤ)` into `P³` (uniformization).
- [20.13.p1](https://dlmf.nist.gov/20.13#p1)–[20.13.p3](https://dlmf.nist.gov/20.13#p3) and 20.13.E1–E5: excluded: application. Mathematical content for a later decision: the heat equation `∂θ/∂τ = −(iπ/4) ∂²θ/∂z²` (20.13.1) satisfied by all four `θⱼ`, its real-time form for `τ = it` (20.13.2), the Gaussian solution (20.13.3), and the periodized-Gaussian identities 20.13.4–20.13.5 (`θ₃(z|4iαt/π)`, `θ₂(z|4iαt/π)` as sums of Gaussians, consequences of 20.7.32–20.7.33).
- [20.14.p1](https://dlmf.nist.gov/20.14#p1), [20.14.p2](https://dlmf.nist.gov/20.14#p2): excluded: computation.
- [20.15.p1](https://dlmf.nist.gov/20.15#p1)–[20.15.p5](https://dlmf.nist.gov/20.15#p5) and 20.15.E1: excluded: computation (tables section). The modular angle `sin α = θ₂²(0,q)/θ₃²(0,q) = k` of 20.15.1 is the modulus 20.9.E1 (`thetaModulusK`).
- [20.16.i.p1](https://dlmf.nist.gov/20.16#i.p1), [20.16.ii.p1](https://dlmf.nist.gov/20.16#ii.p1), [20.16.iii.p1](https://dlmf.nist.gov/20.16#iii.p1): excluded: software listing.

## Validation

`lake build DLMF.Theta DLMF.Elliptic` and strict checks with `autoImplicit=false` and
`relaxedAutoImplicit=false` pass for every changed Lean file and the entry module. The
compiled tag dump and a `#print axioms` audit of every tagged declaration distinguish direct
admissions from inherited dependencies and report no axiom beyond `sorryAx` and `propext`,
`Classical.choice`, `Quot.sound`. The numbered inventory has no unexplained in-scope gap.
Before acquisition, the numbered formulas of §§20.2, 20.4–20.11 were checked numerically with
mpmath at generic complex τ and z (20.6.10 for j = 1, 2; 20.10.1–20.10.3 at several s, including the
value ln 2 at s = 1; 20.10.4–20.10.5 at two choices of ℓ, β, s); the checks found the corrections listed above and no other failure.
