# DLMF Chapter 33 acquisition: Coulomb Functions

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 33](https://dlmf.nist.gov/33), version 1.2.8, checked on 2026-10-26, by two
agents: part A (agent c1, helper prefix `c33a_`) covers §§33.1–33.13 (variables `ρ, η`), part B
(agent c2) covers §§33.14–33.26 (variables `r, ε`, and the excluded application and
computation sections) and appends its sections below. The Lean code is in `DLMF/Coulomb/`
(namespace `DLMF.Coulomb`).

**Move-down of the existing definitions.** The Coulomb functions were defined in theorem files
of the Confluent area. Per the import rule of AGENTS.md their definitions were moved down,
unchanged in name, namespace (`DLMF.Confluent`), statement and tags, into the new definitions
file [Basic](DLMF/Coulomb/Basic.lean): `coulombWave`, `coulombWaveDeriv` (from
`DLMF/Confluent/Coulomb.lean`), `coulombC`, `coulombF` (idem), `coulombSigma`, `coulombTheta`,
`coulombHPlus`, `coulombHMinus` (from `DLMF/Confluent/CoulombAsymptotics.lean`), `coulombAPlus`
and `coulombG` (from `DLMF/Confluent/CoulombIrregular.lean`). `Basic` imports only
`DLMF.Confluent.Basic` (where `kummerM`, `kummerU` live); `DLMF.Confluent.Coulomb` now imports
`DLMF.Coulomb.Basic`. The theorems about these functions stay in the three Confluent files.
After the move, `lake build DLMF.Confluent DLMF.ParabolicCylinder` completed without errors.

The part A modules, in import order, are
[Basic](DLMF/Coulomb/Basic.lean) (moved definitions and `turningPoint`; imports
`DLMF.Confluent.Basic`),
[Defs](DLMF/Coulomb/Defs.lean) (all other part A definitions; imports `Basic`),
[RhoEtaProperties](DLMF/Coulomb/RhoEtaProperties.lean) (§§33.2, 33.4, 33.13; imports `Defs`,
`DLMF.Confluent.CoulombIrregular`, `DLMF.Confluent.Whittaker`),
[RhoEtaLimits](DLMF/Coulomb/RhoEtaLimits.lean) (§§33.5, 33.10),
[RhoEtaSeries](DLMF/Coulomb/RhoEtaSeries.lean) (§§33.6, 33.9),
[RhoEtaRepresentations](DLMF/Coulomb/RhoEtaRepresentations.lean) (§§33.7–33.8) and
[RhoEtaAsymptotics](DLMF/Coulomb/RhoEtaAsymptotics.lean) (§§33.11–33.12); the last four import
`RhoEtaProperties` (and Bessel, Airy, `DLMF.Core.Framework`, `DLMF.Confluent.Relations` as
needed). There are no upstream pointers: Mathlib and TauCeti have no Coulomb functions.

**Counts (part A).** §§33.2, 33.4–33.13 have 76 numbered equations (33.2: 13, 33.4: 4,
33.5: 9, 33.6: 5, 33.7: 4, 33.8: 5, 33.9: 7, 33.10: 10, 33.11: 9, 33.12: 8, 33.13: 2); §33.1 is
notation only and §33.3 (33.3.E1) is excluded: graphics. In scope: 76; covered: all 76 by
project declarations. In addition 4 prose IDs (33.2.i, 33.2.ii, 33.2.iii, 33.13) carry tags.
80 DLMF IDs are tagged on 120 declarations: 24 definitions, 38 proved theorems, 9 theorems
proved from admissions and 49 direct admissions; 10 of the 120 are existing declarations in the
Confluent files (all proved). The 125 declarations of the seven new modules are
30 definitions, 36 proved theorems and lemmas (including untagged helpers), 10 proved from
admissions and 49 admissions.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Basic](DLMF/Coulomb/Basic.lean): 0 admissions; 11 definitions.
- [Defs](DLMF/Coulomb/Defs.lean): 0 admissions; 19 definitions.
- [RhoEtaProperties](DLMF/Coulomb/RhoEtaProperties.lean): 11 admissions; 41 theorems:
  20 proved, 10 proved from admissions, 11 admitted.
- [RhoEtaLimits](DLMF/Coulomb/RhoEtaLimits.lean): 16 admissions; 19 theorems: 3 proved,
  16 admitted.
- [RhoEtaSeries](DLMF/Coulomb/RhoEtaSeries.lean): 9 admissions; 15 theorems: 6 proved,
  9 admitted.
- [RhoEtaRepresentations](DLMF/Coulomb/RhoEtaRepresentations.lean): 7 admissions; 8 theorems:
  1 proved, 7 admitted.
- [RhoEtaAsymptotics](DLMF/Coulomb/RhoEtaAsymptotics.lean): 6 admissions; 12 theorems:
  6 proved, 6 admitted.

## Domains, conventions and source corrections

- **Variables.** `ℓ ∈ ℕ`, `η`, `ρ` real (DLMF §33.1). `F_ℓ` (`coulombF`) and `G_ℓ` (`coulombG`)
  are real functions, `H^±_ℓ` (`coulombHPlus`, `coulombHMinus`) complex functions of the real
  `ρ`. `G_ℓ`, `H^±_ℓ` involve `ln(2ρ)` and `(∓2iρ)^{iη}`, so every statement involving them, or
  dividing by `ρ`, assumes `ρ > 0`. Derivatives are `deriv` in `ρ`. Statements of 33.4 and
  33.2.13 that involve `ℓ - 1` are stated at `ℓ + 1` (no natural subtraction).
- **Phase shift.** The existing `coulombSigma` is the principal phase `arg Γ(ℓ+1+iη)`. It
  fixes `e^{iσ_ℓ}`, hence `θ_ℓ` modulo `2π` and `H^±_ℓ`, `G_ℓ` exactly, but not DLMF's branch
  ("zero when `η = 0` and continuous elsewhere"), which matters in 33.5.7, 33.10.6 and
  33.10.10 (mpmath: the principal phase misses 33.10.10 by about `38` at `η = -20`). The new
  `phaseShift` is DLMF's branch, defined by the Weierstrass product,
  `σ_ℓ(η) = -γη + ∑_{n ≥ 1} (η/n - arctan(η/n)) + ∑_{k=1}^{ℓ} arctan(η/k)` (checked against
  `Im loggamma` to `1e-29`); `phaseShift_spec` (admitted) records that it is a phase of
  `Γ(ℓ+1+iη)`, vanishes at `η = 0` and is continuous, and `exp_I_phaseShift` that
  `e^{iσ}` agrees for the two branches. `θ_ℓ` (`coulombTheta`) keeps the principal branch.
- **Recurrence coefficients.** `R_ℓ`, `S_ℓ`, `T_ℓ` of 33.4.1 are `recurrenceR`, `recurrenceS`,
  `recurrenceT` (meaningful for `ℓ ≥ 1`).
- **Series and expansions.** Coefficient sequences are defined by their recurrences with the
  printed initial values (`powerSeriesCoeff` for `A_k^ℓ`, `besselSeriesCoeffA`, `besselSeriesCoeffB`
  for `a_k`, `b_k`, `largeRhoTerm` for `(f_k, g_k, f̂_k, ĝ_k)`); the recurrences are then proved
  theorems. Series use `HasSum` over `ℕ`. Asymptotic expansions are stated in Poincaré form
  (`O` of the first omitted order) when all terms are known (33.11.5–33.11.6), and with the
  printed terms and an `O`/`o` remainder of the next or last printed order when only finitely
  many terms are printed (33.12.2–33.12.3, 33.12.6–33.12.7). In 33.9.6–33.9.7, where both
  `λ_ℓ(η)` and the `K`-series are asymptotic, the statement is the `∼` relation with the same
  number `N + 1` of terms in each truncation, for every `N`.
- **§33.10 limits** with `ηρ = c` fixed are limits of `η ↦ X(η, c/η)` along `atTop`/`atBot`.
  33.10.7 and 33.10.9 are acquired as printed with errors `o(|η|^{1/4})` (true, though the
  actual error is much smaller).
- **§33.13.** The extension to complex `ℓ`, `η`, `ρ` is `coulombWaveComplex` (principal power
  `ρ^{ℓ+1}`), which agrees with `coulombWave` for `ℓ ∈ ℕ` and solves 33.2.1 on the slit plane
  (admitted). 33.13.1–33.13.2 are proved for `ℓ ∈ ℕ` and real `η`, the case in which the
  quantities are defined in this library.
- **Source corrections** (all checked with mpmath at 30–40 digits; scripts in the agent's
  scratch directory):
  - **33.9.4** (`η < 0`): with the same `b_k` as in 33.9.3 the printed sum is wrong (printed
    right side minus `F_0` is `-0.110` at `ℓ = 0`, `η = -0.7`, `ρ = 1.2`, and `2.15` at
    `η = -1.5`, `ρ = 4`). The correct sum has `(-1)^{k+1} b_k` (error below `1e-30` for
    `ℓ = 0, 1, 3`); it follows from 33.9.3 under `t ↦ -t`. Acquired in corrected form.
  - **33.11.7**: printed `g f̂ - f ĝ = 1`; with `f, g, f̂, ĝ` of 33.11.2–33.11.3 the
    Wronskian gives `f ĝ - g f̂ = G_ℓ F_ℓ' - G_ℓ' F_ℓ = 1` (leading terms: `f_0 ĝ_0 = 1 - η/ρ`;
    mpmath: `g f̂ - f ĝ = -1.0`). Acquired and proved in corrected form.
  - **33.12.3**: the factor of `Ai'(x)` (`Bi'(x)`) is printed as `(B_1 + A_1')/μ + ⋯`; it must
    begin with `1` (differentiate the leading term of 33.12.2). With the `1` the remainder is
    `O((2η)^{-1/6} μ^{-4})` at `η = 20, 80, 320`, `x ∈ {-1.3, 0, 0.8}`. Acquired in corrected
    form.

## Numbered formulas and prose items

## [§33.1 Special Notation](https://dlmf.nist.gov/33.1)

- [33.1](https://dlmf.nist.gov/33.1): notation only; no statement.

## [§33.2 Definitions and Basic Properties](https://dlmf.nist.gov/33.2)

- [33.2.i](https://dlmf.nist.gov/33.2.i): [`DLMF.Coulomb.coulomb_indicial`](DLMF/Coulomb/RhoEtaProperties.lean#L73) (proved)
- [33.2.ii](https://dlmf.nist.gov/33.2.ii): [`DLMF.Coulomb.coulombC_pos`](DLMF/Coulomb/RhoEtaProperties.lean#L114) (proved); [`DLMF.Coulomb.analytic_coulombF`](DLMF/Coulomb/RhoEtaProperties.lean#L248) (admitted)
- [33.2.iii](https://dlmf.nist.gov/33.2.iii): [`DLMF.Coulomb.coulombHMinus_eq_conj_coulombHPlus`](DLMF/Coulomb/RhoEtaProperties.lean#L524) (proved); [`DLMF.Coulomb.analytic_coulombH`](DLMF/Coulomb/RhoEtaProperties.lean#L530) (admitted)
- [33.2.E1](https://dlmf.nist.gov/33.2.E1): [`DLMF.Coulomb.coulombF_deriv_deriv`](DLMF/Coulomb/RhoEtaProperties.lean#L51) (proved); [`DLMF.Coulomb.coulombG_deriv_deriv`](DLMF/Coulomb/RhoEtaProperties.lean#L815) (proved); [`DLMF.Confluent.hasDerivAt_coulombWaveDeriv`](DLMF/Confluent/Coulomb.lean#L85) (proved). The existing `hasDerivAt_coulombWaveDeriv` (unnormalized regular solution, multiplied form) and the equation for `F_ℓ` and `G_ℓ` in `deriv` form.
- [33.2.E2](https://dlmf.nist.gov/33.2.E2): [`DLMF.Coulomb.turningPoint`](DLMF/Coulomb/Basic.lean#L101) (definition); [`DLMF.Coulomb.turningPoint_isRoot`](DLMF/Coulomb/RhoEtaProperties.lean#L81) (proved); [`DLMF.Coulomb.coulomb_coeff_turningPoint`](DLMF/Coulomb/RhoEtaProperties.lean#L96) (proved). Root of `ρ² - 2ηρ - ℓ(ℓ+1)` and largest root; zero of the coefficient of 33.2.1.
- [33.2.E3](https://dlmf.nist.gov/33.2.E3): [`DLMF.Coulomb.ofReal_coulombF_eq_whittakerM`](DLMF/Coulomb/RhoEtaProperties.lean#L121) (proved); [`DLMF.Coulomb.ofReal_coulombF_eq_whittakerM_neg`](DLMF/Coulomb/RhoEtaProperties.lean#L142) (proved). Both sign choices; `M_{κ,μ}` is `DLMF.Confluent.whittakerM`.
- [33.2.E4](https://dlmf.nist.gov/33.2.E4): [`DLMF.Confluent.coulombF`](DLMF/Coulomb/Basic.lean#L61) (definition); [`DLMF.Confluent.coulombWave_eq_conj_form`](DLMF/Confluent/Coulomb.lean#L150) (proved). Definition (upper signs) and the lower-sign form by Kummer’s transformation (existing).
- [33.2.E5](https://dlmf.nist.gov/33.2.E5): [`DLMF.Confluent.coulombC`](DLMF/Coulomb/Basic.lean#L55) (definition)
- [33.2.E6](https://dlmf.nist.gov/33.2.E6): [`DLMF.Coulomb.coulombC_sq_eq_prod`](DLMF/Coulomb/RhoEtaProperties.lean#L199) (proved); [`DLMF.Coulomb.coulombC_eq_sqrt_prod`](DLMF/Coulomb/RhoEtaProperties.lean#L225) (proved). Proved for `η ≠ 0` (squared and printed forms); at `η = 0` the factor is read as its limit, see 33.5.6.
- [33.2.E7](https://dlmf.nist.gov/33.2.E7): [`DLMF.Coulomb.coulombHPlus_eq_whittakerW`](DLMF/Coulomb/RhoEtaProperties.lean#L258) (proved); [`DLMF.Coulomb.coulombHMinus_eq_whittakerW`](DLMF/Coulomb/RhoEtaProperties.lean#L282) (proved). `W_{κ,μ}` is `DLMF.Confluent.whittakerW`; `ρ > 0`.
- [33.2.E8](https://dlmf.nist.gov/33.2.E8): [`DLMF.Confluent.coulombHPlus`](DLMF/Coulomb/Basic.lean#L75) (definition); [`DLMF.Confluent.coulombHMinus`](DLMF/Coulomb/Basic.lean#L82) (definition)
- [33.2.E9](https://dlmf.nist.gov/33.2.E9): [`DLMF.Confluent.coulombTheta`](DLMF/Coulomb/Basic.lean#L71) (definition)
- [33.2.E10](https://dlmf.nist.gov/33.2.E10): [`DLMF.Confluent.coulombSigma`](DLMF/Coulomb/Basic.lean#L67) (definition); [`DLMF.Coulomb.phaseShift`](DLMF/Coulomb/Defs.lean#L58) (definition); [`DLMF.Coulomb.phaseShift_spec`](DLMF/Coulomb/RhoEtaProperties.lean#L483) (proved). `coulombSigma` is the principal phase (existing; it fixes `e^{iσ}` and hence `H^±`); `phaseShift` is DLMF’s continuous branch with zero at `η = 0`, used in 33.5.7, 33.10.6, 33.10.10. `phaseShift_spec` (admitted) states that it is a phase of `Γ(ℓ+1+iη)`, vanishes at 0 and is continuous.
- [33.2.E11](https://dlmf.nist.gov/33.2.E11): [`DLMF.Confluent.coulombG`](DLMF/Coulomb/Basic.lean#L93) (definition); [`DLMF.Confluent.coulombH_eq_G_add_I_mul_F`](DLMF/Confluent/CoulombIrregular.lean#L222) (proved)
- [33.2.E12](https://dlmf.nist.gov/33.2.E12): [`DLMF.Confluent.coulomb_wronskian`](DLMF/Confluent/CoulombIrregular.lean#L376) (proved); [`DLMF.Confluent.coulomb_wronskian_HPlus`](DLMF/Confluent/CoulombIrregular.lean#L383) (proved); [`DLMF.Confluent.coulomb_wronskian_HMinus`](DLMF/Confluent/CoulombIrregular.lean#L394) (proved)
- [33.2.E13](https://dlmf.nist.gov/33.2.E13): [`DLMF.Coulomb.coulombF_mul_coulombG_sub`](DLMF/Coulomb/RhoEtaProperties.lean#L947) (proved). Proved from the Wronskian 33.2.12 and the admitted 33.4.3.

## [§33.3 Graphics](https://dlmf.nist.gov/33.3)

- [33.3.E1](https://dlmf.nist.gov/33.3.E1): excluded: graphics.

## [§33.4 Recurrence Relations and Derivatives](https://dlmf.nist.gov/33.4)

- [33.4.E1](https://dlmf.nist.gov/33.4.E1): [`DLMF.Coulomb.recurrenceR`](DLMF/Coulomb/Defs.lean#L46) (definition); [`DLMF.Coulomb.recurrenceS`](DLMF/Coulomb/Defs.lean#L50) (definition); [`DLMF.Coulomb.recurrenceT`](DLMF/Coulomb/Defs.lean#L54) (definition). Definitions for `ℓ ≥ 1`.
- [33.4.E2](https://dlmf.nist.gov/33.4.E2): [`DLMF.Coulomb.coulombF_recurrence`](DLMF/Coulomb/RhoEtaProperties.lean#L853) (proved); [`DLMF.Coulomb.coulombG_recurrence`](DLMF/Coulomb/RhoEtaProperties.lean#L864) (proved); [`DLMF.Coulomb.coulombHPlus_recurrence`](DLMF/Coulomb/RhoEtaProperties.lean#L915) (proved); [`DLMF.Coulomb.coulombHMinus_recurrence`](DLMF/Coulomb/RhoEtaProperties.lean#L930) (proved). For `X = F, G, H^+, H^-`, stated at `ℓ+1`; proved from 33.4.3–33.4.4.
- [33.4.E3](https://dlmf.nist.gov/33.4.E3): [`DLMF.Coulomb.deriv_coulombF_lower`](DLMF/Coulomb/RhoEtaProperties.lean#L785) (proved); [`DLMF.Coulomb.deriv_coulombG_lower`](DLMF/Coulomb/RhoEtaProperties.lean#L801) (proved); [`DLMF.Coulomb.deriv_coulombHPlus_lower`](DLMF/Coulomb/RhoEtaProperties.lean#L711) (proved); [`DLMF.Coulomb.deriv_coulombHMinus_lower`](DLMF/Coulomb/RhoEtaProperties.lean#L893) (proved). For `X = F, G` admitted, for `X = H^±` proved from them; stated at `ℓ+1`, `ρ > 0`.
- [33.4.E4](https://dlmf.nist.gov/33.4.E4): [`DLMF.Coulomb.deriv_coulombF_upper`](DLMF/Coulomb/RhoEtaProperties.lean#L793) (proved); [`DLMF.Coulomb.deriv_coulombG_upper`](DLMF/Coulomb/RhoEtaProperties.lean#L808) (proved); [`DLMF.Coulomb.deriv_coulombHPlus_upper`](DLMF/Coulomb/RhoEtaProperties.lean#L677) (proved); [`DLMF.Coulomb.deriv_coulombHMinus_upper`](DLMF/Coulomb/RhoEtaProperties.lean#L904) (proved). As 33.4.3, `ℓ ≥ 0`.

## [§33.5 Limiting Forms for Small ρ, Small |η|, or Large ℓ](https://dlmf.nist.gov/33.5)

- [33.5.E1](https://dlmf.nist.gov/33.5.E1): [`DLMF.Coulomb.coulombF_isEquivalent_zero`](DLMF/Coulomb/RhoEtaLimits.lean#L59) (proved)
- [33.5.E2](https://dlmf.nist.gov/33.5.E2): [`DLMF.Coulomb.coulombG_isEquivalent_zero`](DLMF/Coulomb/RhoEtaLimits.lean#L306) (proved). The derivative part for `ℓ ≥ 1` as printed.
- [33.5.E3](https://dlmf.nist.gov/33.5.E3): [`DLMF.Coulomb.coulombF_zero_eq_sphericalJ`](DLMF/Coulomb/RhoEtaLimits.lean#L383) (proved); [`DLMF.Coulomb.coulombG_zero_eq_sphericalY`](DLMF/Coulomb/RhoEtaLimits.lean#L519) (proved). `j_ℓ` is `DLMF.sphericalJ`; `y_ℓ` is written out by 10.47.3.
- [33.5.E4](https://dlmf.nist.gov/33.5.E4): [`DLMF.Coulomb.coulombFG_zero_eq_bessel`](DLMF/Coulomb/RhoEtaLimits.lean#L533) (proved)
- [33.5.E5](https://dlmf.nist.gov/33.5.E5): [`DLMF.Coulomb.coulomb_zero_zero`](DLMF/Coulomb/RhoEtaLimits.lean#L544) (proved)
- [33.5.E6](https://dlmf.nist.gov/33.5.E6): [`DLMF.Coulomb.coulombC_zero`](DLMF/Coulomb/RhoEtaLimits.lean#L365) (proved)
- [33.5.E7](https://dlmf.nist.gov/33.5.E7): [`DLMF.Coulomb.phaseShift_zero_isEquivalent`](DLMF/Coulomb/RhoEtaLimits.lean#L644) (proved). Continuous branch `phaseShift`.
- [33.5.E8](https://dlmf.nist.gov/33.5.E8): [`DLMF.Coulomb.coulomb_isEquivalent_large_ell`](DLMF/Coulomb/RhoEtaLimits.lean#L795) (proved)
- [33.5.E9](https://dlmf.nist.gov/33.5.E9): [`DLMF.Coulomb.coulombC_isEquivalent_large_ell`](DLMF/Coulomb/RhoEtaLimits.lean#L993) (proved)

## [§33.6 Power-Series Expansions in ρ](https://dlmf.nist.gov/33.6)

- [33.6.E1](https://dlmf.nist.gov/33.6.E1): [`DLMF.Coulomb.hasSum_coulombF`](DLMF/Coulomb/RhoEtaSeries.lean#L276) (proved)
- [33.6.E2](https://dlmf.nist.gov/33.6.E2): [`DLMF.Coulomb.hasSum_deriv_coulombF`](DLMF/Coulomb/RhoEtaSeries.lean#L287) (proved)
- [33.6.E3](https://dlmf.nist.gov/33.6.E3): [`DLMF.Coulomb.powerSeriesCoeff`](DLMF/Coulomb/Defs.lean#L75) (definition); [`DLMF.Coulomb.powerSeriesCoeff_initial`](DLMF/Coulomb/RhoEtaSeries.lean#L48) (proved); [`DLMF.Coulomb.powerSeriesCoeff_recurrence`](DLMF/Coulomb/RhoEtaSeries.lean#L57) (proved). `powerSeriesCoeff` is defined by the recurrence with the initial values `A_{ℓ+1} = 1`, `A_{ℓ+2} = η/(ℓ+1)`; the recurrence itself is proved.
- [33.6.E4](https://dlmf.nist.gov/33.6.E4): [`DLMF.Coulomb.powerSeriesCoeff_eq_hyp2F1`](DLMF/Coulomb/RhoEtaSeries.lean#L330) (proved). The terminating `₂F₁` at `z = 2` written as its finite sum.
- [33.6.E5](https://dlmf.nist.gov/33.6.E5): [`DLMF.Coulomb.hasSum_coulombHPlus_log`](DLMF/Coulomb/RhoEtaSeries.lean#L385) (admitted); [`DLMF.Coulomb.hasSum_coulombHMinus_log`](DLMF/Coulomb/RhoEtaSeries.lean#L401) (admitted). Both signs; the infinite series is stated with `HasSum`, `ρ > 0`.

## [§33.7 Integral Representations](https://dlmf.nist.gov/33.7)

- [33.7.E1](https://dlmf.nist.gov/33.7.E1): [`DLMF.Coulomb.coulombF_eq_integral`](DLMF/Coulomb/RhoEtaRepresentations.lean#L39) (proved)
- [33.7.E2](https://dlmf.nist.gov/33.7.E2): [`DLMF.Coulomb.coulombHMinus_eq_integral`](DLMF/Coulomb/RhoEtaRepresentations.lean#L375) (proved)
- [33.7.E3](https://dlmf.nist.gov/33.7.E3): [`DLMF.Coulomb.coulombHMinus_eq_integral_tanh`](DLMF/Coulomb/RhoEtaRepresentations.lean#L444) (admitted)
- [33.7.E4](https://dlmf.nist.gov/33.7.E4): [`DLMF.Coulomb.coulombHPlus_eq_integral`](DLMF/Coulomb/RhoEtaRepresentations.lean#L459) (proved). Contour from `-1` to `-i∞` parametrized by `t = -1 - is`.

## [§33.8 Continued Fractions](https://dlmf.nist.gov/33.8)

- [33.8.E1](https://dlmf.nist.gov/33.8.E1): [`DLMF.Coulomb.coulombF_logDeriv_contFrac`](DLMF/Coulomb/RhoEtaRepresentations.lean#L795) (proved). `DLMF.HasContinuedFraction`; `ρ > 0`, `F_ℓ ≠ 0`.
- [33.8.E2](https://dlmf.nist.gov/33.8.E2): [`DLMF.Coulomb.coulombHPlus_logDeriv_contFrac`](DLMF/Coulomb/RhoEtaRepresentations.lean#L810) (admitted); [`DLMF.Coulomb.coulombHMinus_logDeriv_contFrac`](DLMF/Coulomb/RhoEtaRepresentations.lean#L821) (admitted)
- [33.8.E3](https://dlmf.nist.gov/33.8.E3): [`DLMF.Coulomb.coulombHPlus_logDeriv_contFrac`](DLMF/Coulomb/RhoEtaRepresentations.lean#L810) (admitted); [`DLMF.Coulomb.coulombHMinus_logDeriv_contFrac`](DLMF/Coulomb/RhoEtaRepresentations.lean#L821) (admitted). The constants `a`, `b`, `c` are written into the statements of 33.8.2.
- [33.8.E4](https://dlmf.nist.gov/33.8.E4): [`DLMF.Coulomb.coulomb_barnett`](DLMF/Coulomb/RhoEtaRepresentations.lean#L832) (proved). Stated as `F_ℓ² (q⁻¹(u-p)² + q) = 1` (both signs of the square root).
- [33.8.E5](https://dlmf.nist.gov/33.8.E5): [`DLMF.Coulomb.coulomb_barnett`](DLMF/Coulomb/RhoEtaRepresentations.lean#L832) (proved)

## [§33.9 Expansions in Series of Bessel Functions](https://dlmf.nist.gov/33.9)

- [33.9.E1](https://dlmf.nist.gov/33.9.E1): [`DLMF.Coulomb.hasSum_coulombF_sphericalJ`](DLMF/Coulomb/RhoEtaSeries.lean#L445) (admitted)
- [33.9.E2](https://dlmf.nist.gov/33.9.E2): [`DLMF.Coulomb.besselSeriesCoeffA`](DLMF/Coulomb/Defs.lean#L81) (definition); [`DLMF.Coulomb.besselSeriesCoeffA_initial`](DLMF/Coulomb/RhoEtaSeries.lean#L417) (proved); [`DLMF.Coulomb.besselSeriesCoeffA_recurrence`](DLMF/Coulomb/RhoEtaSeries.lean#L431) (proved)
- [33.9.E3](https://dlmf.nist.gov/33.9.E3): [`DLMF.Coulomb.coulombF_eq_besselI_series`](DLMF/Coulomb/RhoEtaSeries.lean#L478) (admitted)
- [33.9.E4](https://dlmf.nist.gov/33.9.E4): [`DLMF.Coulomb.coulombF_eq_besselJ_series`](DLMF/Coulomb/RhoEtaSeries.lean#L489) (admitted). **Corrected**: the printed formula lacks the factor `(-1)^{k+1}` (see "Domains, conventions and source corrections").
- [33.9.E5](https://dlmf.nist.gov/33.9.E5): [`DLMF.Coulomb.besselSeriesCoeffB`](DLMF/Coulomb/Defs.lean#L102) (definition); [`DLMF.Coulomb.besselSeriesCoeffB_initial`](DLMF/Coulomb/RhoEtaSeries.lean#L455) (proved); [`DLMF.Coulomb.besselSeriesCoeffB_recurrence`](DLMF/Coulomb/RhoEtaSeries.lean#L462) (proved)
- [33.9.E6](https://dlmf.nist.gov/33.9.E6): [`DLMF.Coulomb.coulombG_isEquivalent_besselK`](DLMF/Coulomb/RhoEtaSeries.lean#L502) (admitted). Ratio form with `N + 1` terms of both asymptotic series, for every `N`.
- [33.9.E7](https://dlmf.nist.gov/33.9.E7): [`DLMF.Coulomb.coulombG_isEquivalent_besselK`](DLMF/Coulomb/RhoEtaSeries.lean#L502) (admitted). With 33.9.6.

## [§33.10 Limiting Forms for Large ρ or Large |η|](https://dlmf.nist.gov/33.10)

- [33.10.E1](https://dlmf.nist.gov/33.10.E1): [`DLMF.Confluent.tendsto_coulombF_sub_sin_and_coulombG_sub_cos`](DLMF/Confluent/CoulombIrregular.lean#L431) (proved). Existing.
- [33.10.E2](https://dlmf.nist.gov/33.10.E2): [`DLMF.Coulomb.tendsto_coulombHMinus_sub_exp`](DLMF/Coulomb/RhoEtaLimits.lean#L1251) (proved); [`DLMF.Confluent.tendsto_coulombHPlus_sub_exp`](DLMF/Confluent/CoulombIrregular.lean#L410) (proved). Existing (upper sign); lower sign added by conjugation.
- [33.10.E3](https://dlmf.nist.gov/33.10.E3): [`DLMF.Coulomb.coulomb_isEquivalent_eta_atTop`](DLMF/Coulomb/RhoEtaLimits.lean#L1266) (admitted)
- [33.10.E4](https://dlmf.nist.gov/33.10.E4): [`DLMF.Coulomb.coulomb_zero_isEquivalent_eta_atTop`](DLMF/Coulomb/RhoEtaLimits.lean#L1279) (admitted)
- [33.10.E5](https://dlmf.nist.gov/33.10.E5): [`DLMF.Coulomb.coulomb_zero_deriv_isEquivalent_eta_atTop`](DLMF/Coulomb/RhoEtaLimits.lean#L1291) (admitted)
- [33.10.E6](https://dlmf.nist.gov/33.10.E6): [`DLMF.Coulomb.phaseShift_coulombC_eta_atTop`](DLMF/Coulomb/RhoEtaLimits.lean#L1304) (proved). Continuous branch `phaseShift`; the principal branch fails.
- [33.10.E7](https://dlmf.nist.gov/33.10.E7): [`DLMF.Coulomb.coulomb_eta_atBot`](DLMF/Coulomb/RhoEtaLimits.lean#L1314) (admitted). As printed (the `o(|η|^{1/4})` error is weak but true).
- [33.10.E8](https://dlmf.nist.gov/33.10.E8): [`DLMF.Coulomb.coulomb_zero_eta_atBot`](DLMF/Coulomb/RhoEtaLimits.lean#L1330) (admitted)
- [33.10.E9](https://dlmf.nist.gov/33.10.E9): [`DLMF.Coulomb.coulomb_zero_deriv_eta_atBot`](DLMF/Coulomb/RhoEtaLimits.lean#L1343) (admitted)
- [33.10.E10](https://dlmf.nist.gov/33.10.E10): [`DLMF.Coulomb.phaseShift_coulombC_eta_atBot`](DLMF/Coulomb/RhoEtaLimits.lean#L1356) (proved). Continuous branch `phaseShift`.

## [§33.11 Asymptotic Expansions for Large ρ](https://dlmf.nist.gov/33.11)

- [33.11.E1](https://dlmf.nist.gov/33.11.E1): [`DLMF.Confluent.hasAsymptoticExpansion_coulombHPlus`](DLMF/Confluent/CoulombAsymptotics.lean#L89) (proved); [`DLMF.Confluent.hasAsymptoticExpansion_coulombHMinus`](DLMF/Confluent/CoulombAsymptotics.lean#L119) (proved). Existing (`DLMF.Confluent.CoulombAsymptotics`).
- [33.11.E2](https://dlmf.nist.gov/33.11.E2): [`DLMF.Coulomb.largeRhoF`](DLMF/Coulomb/Defs.lean#L107) (definition); [`DLMF.Coulomb.largeRhoG`](DLMF/Coulomb/Defs.lean#L113) (definition); [`DLMF.Coulomb.coulombFG_eq_largeRho`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L50) (proved). `f`, `g` are defined by 33.11.2 (rotation by `θ_ℓ`).
- [33.11.E3](https://dlmf.nist.gov/33.11.E3): [`DLMF.Coulomb.largeRhoFHat`](DLMF/Coulomb/Defs.lean#L118) (definition); [`DLMF.Coulomb.largeRhoGHat`](DLMF/Coulomb/Defs.lean#L125) (definition); [`DLMF.Coulomb.deriv_coulombFG_eq_largeRho`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L63) (proved). `f̂`, `ĝ` are defined by 33.11.3.
- [33.11.E4](https://dlmf.nist.gov/33.11.E4): [`DLMF.Coulomb.coulombH_eq_largeRho`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L76) (proved)
- [33.11.E5](https://dlmf.nist.gov/33.11.E5): [`DLMF.Coulomb.largeRhoFG_isBigO`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L122) (proved). Poincaré form: remainder after `k ≤ K` is `O(ρ^{-K-1})`.
- [33.11.E6](https://dlmf.nist.gov/33.11.E6): [`DLMF.Coulomb.largeRhoFGHat_isBigO`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L292) (proved). Poincaré form.
- [33.11.E7](https://dlmf.nist.gov/33.11.E7): [`DLMF.Coulomb.largeRho_wronskian`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L385) (proved). **Corrected** sign: `f ĝ - g f̂ = 1` (DLMF prints `g f̂ - f ĝ = 1`).
- [33.11.E8](https://dlmf.nist.gov/33.11.E8): [`DLMF.Coulomb.largeRhoTerm`](DLMF/Coulomb/Defs.lean#L131) (definition); [`DLMF.Coulomb.largeRhoTerm_spec`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L396) (proved)
- [33.11.E9](https://dlmf.nist.gov/33.11.E9): [`DLMF.Coulomb.largeRhoTerm_spec`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L396) (proved)

## [§33.12 Asymptotic Expansions for Large η](https://dlmf.nist.gov/33.12)

- [33.12.E1](https://dlmf.nist.gov/33.12.E1): [`DLMF.Coulomb.transitionX`](DLMF/Coulomb/Defs.lean#L150) (definition); [`DLMF.Coulomb.transitionMu`](DLMF/Coulomb/Defs.lean#L154) (definition)
- [33.12.E2](https://dlmf.nist.gov/33.12.E2): [`DLMF.Coulomb.coulomb_zero_transition`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L415) (admitted). Three printed terms, remainder `O((2η)^{1/6} μ^{-4})` uniformly for `|x| ≤ X`.
- [33.12.E3](https://dlmf.nist.gov/33.12.E3): [`DLMF.Coulomb.coulomb_zero_deriv_transition`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L437) (admitted). **Corrected**: the factor of `Ai'(x)`, `Bi'(x)` begins with `1`; remainder `O((2η)^{-1/6} μ^{-4})`.
- [33.12.E4](https://dlmf.nist.gov/33.12.E4): [`DLMF.Coulomb.transitionA`](DLMF/Coulomb/Defs.lean#L158) (definition)
- [33.12.E5](https://dlmf.nist.gov/33.12.E5): [`DLMF.Coulomb.transitionB`](DLMF/Coulomb/Defs.lean#L167) (definition)
- [33.12.E6](https://dlmf.nist.gov/33.12.E6): [`DLMF.Coulomb.coulomb_zero_turningPoint`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L463) (admitted). Remainder `o(ω^{1/2-10})`.
- [33.12.E7](https://dlmf.nist.gov/33.12.E7): [`DLMF.Coulomb.coulomb_zero_deriv_turningPoint`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L485) (admitted). Remainder `o(ω^{-1/2-8})`.
- [33.12.E8](https://dlmf.nist.gov/33.12.E8): [`DLMF.Coulomb.coulomb_scaled_equation`](DLMF/Coulomb/RhoEtaAsymptotics.lean#L507) (proved). For any twice differentiable solution of 33.2.1.

## [§33.13 Complex Variable and Parameters](https://dlmf.nist.gov/33.13)

- [33.13](https://dlmf.nist.gov/33.13): [`DLMF.Coulomb.coulombWaveComplex_ode`](DLMF/Coulomb/RhoEtaProperties.lean#L1052) (proved)
- [33.13.E1](https://dlmf.nist.gov/33.13.E1): [`DLMF.Coulomb.coulombC_eq_exp_sigma_mul_Gamma`](DLMF/Coulomb/RhoEtaProperties.lean#L967) (proved). For `ℓ ∈ ℕ`, real `η` (principal `σ_ℓ`; any branch gives the same `e^{iσ_ℓ}`).
- [33.13.E2](https://dlmf.nist.gov/33.13.E2): [`DLMF.Coulomb.recurrenceR_eq_coulombC_div`](DLMF/Coulomb/RhoEtaProperties.lean#L998) (proved). For `ℓ ∈ ℕ`, real `η`, stated at `ℓ+1`.

## Prose, informal and excluded items (part A)

- [33.1](https://dlmf.nist.gov/33.1): notation; the alternative notations of 33.1.Px1 concern
  the functions of §33.14 (part B).
- [33.2.i](https://dlmf.nist.gov/33.2.i): the indices `ℓ + 1`, `-ℓ` of the regular singularity
  are `coulomb_indicial`; the irregular singularity of rank 1 at `∞` is not formalized (no
  project notion of rank); the turning points are 33.2.E2.
- [33.2.ii](https://dlmf.nist.gov/33.2.ii): the immateriality of the sign choice in 33.2.3–33.2.4
  is covered by proving both sign choices; reality of `F_ℓ` is built in (`coulombF` is the real
  part, `ofReal_coulombF` in `DLMF.Confluent.Coulomb` shows nothing is lost); analyticity in
  `ρ` and `η` is `analytic_coulombF` (admitted); positivity of `C_ℓ` is `coulombC_pos`.
- [33.2.iii](https://dlmf.nist.gov/33.2.iii): the branch of `σ_ℓ` (see conventions); `H^±`
  complex conjugates (`coulombHMinus_eq_conj_coulombHPlus`, proved); analyticity of `H^±_ℓ`,
  `G_ℓ` in `ρ` and of `e^{∓iσ_ℓ} H^±_ℓ` in `η` is `analytic_coulombH` (admitted).
- [33.3](https://dlmf.nist.gov/33.3): excluded: graphics (33.3.E1 is the plotted envelope
  `M_ℓ = (F_ℓ² + G_ℓ²)^{1/2}`).
- [33.4](https://dlmf.nist.gov/33.4): "`X_ℓ` any of `F_ℓ`, `G_ℓ`, `H^±_ℓ`": each of 33.4.2–33.4.4
  is stated for all four.
- [33.6](https://dlmf.nist.gov/33.6): convergence for all finite `ρ` is part of the `HasSum`
  statements; the remark that expansions of `H^±_ℓ'` follow from 33.6.5 with 33.4.3–33.4.4 is
  not a separate statement.
- [33.7](https://dlmf.nist.gov/33.7): principal values of powers and of `arctan` are the Lean
  defaults (`cpow`, `Real.arctan`).
- [33.8](https://dlmf.nist.gov/33.8): convergence of 33.8.1–33.8.2 is part of the
  `HasContinuedFraction` statements (for `ρ > 0`); the rule for the ambiguous sign in 33.8.4
  (agreement with the sign of the final denominator of 33.8.1 in a computation) is
  algorithmic and not formalized; 33.8.4 is stated for `F_ℓ²`. References only otherwise.
- [33.9](https://dlmf.nist.gov/33.9): convergence statements are part of the `HasSum`
  statements; 33.9.ii.p4 (other expansions of `G_ℓ`): no statement (references only).
- [33.12.i](https://dlmf.nist.gov/33.12.i): 33.12.i.p4 (further terms, Temme 2015 Ch. 31): no
  statement (references only).
- [33.12.ii](https://dlmf.nist.gov/33.12.ii): the scaled equation is 33.12.E8; the existence of
  uniform Airy-type (`δ ≤ z < ∞`) and Bessel-type (`0 ≤ z ≤ 1 - δ`) expansions is stated
  without explicit formulas and is not formalized.
- [33.13](https://dlmf.nist.gov/33.13): the continuation to complex parameters is
  `coulombWaveComplex` with `coulombWaveComplex_ode` (admitted); the consistent definition of
  `C_ℓ`, `σ_ℓ`, `R_ℓ` for complex parameters is not formalized beyond 33.13.1–33.13.2 for
  `ℓ ∈ ℕ`, real `η`; 33.13.p3: references only.
- Bibliographic paragraphs are not acquired.

## Validation (part A)

- The seven modules build with `lake build DLMF.Coulomb.<Module>` and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` without errors (`Basic`,
  `Defs` without admissions). After the move-down, `lake build DLMF.Confluent
  DLMF.ParabolicCylinder` succeeded. There are no axioms, no `native_decide`, and no `sorry` in
  definitions or helper declarations (prefix `c33a_`). No line exceeds 100 characters.
- `#print axioms` for all 46 proved theorems and lemmas of the new modules: the 36 proved ones
  (for example `coulombF_deriv_deriv`, `ofReal_coulombF_eq_whittakerM`, `coulombC_sq_eq_prod`,
  `coulombC_eq_exp_sigma_mul_Gamma`, `recurrenceR_eq_coulombC_div`, `coulomb_zero_zero`,
  `coulomb_barnett`, `largeRho_wronskian`, `coulomb_scaled_equation`,
  `powerSeriesCoeff_recurrence`) show only `propext`, `Classical.choice` and `Quot.sound`; the
  10 proved from admissions (the recurrences for `F`, `G`, `H^±`, the cross-product 33.2.13,
  `exp_I_phaseShift`) depend in addition on `sorryAx` through 33.4.3–33.4.4 and
  `phaseShift_spec`.
- Every acquired formula was checked numerically with mpmath (`coulombf`, `coulombg`,
  `coulombc`, `hyp1f1`, `hyperu`, `whitm`, `whitw`, `hyp2f1`, `quad`, `besselj`/`y`/`i`/`k`,
  `airyai`/`bi`) before acquisition: 33.2.3–33.2.13, 33.4.2–33.4.4 (for `F`, `G`, also
  `ℓ = 0` in 33.4.4), 33.5.1–33.5.9, 33.6.1–33.6.5, 33.7.1–33.7.4, 33.8.1–33.8.5, 33.9.1–33.9.7,
  33.10.3–33.10.10, 33.11.2–33.11.9, 33.12.2–33.12.7, `phaseShift`; the three corrections above
  are the only failures.
- DLMF.lean, the umbrella `DLMF/Coulomb.lean`, the lakefile and the other ledgers are
  unchanged; the three Confluent files changed only by deleting the moved definitions (and, in
  `DLMF.Confluent.Coulomb`, adding the import of `DLMF.Coulomb.Basic`).


## Part B: §§33.14–33.26 (variables `r`, `ε`)

Part B (agent c2, helper prefix `c33b_`) covers §§33.14–33.21 and records the exclusions of
§33.15 (graphics), §33.22 (application) and §§33.23–33.26 (computation). The modules, in
import order, are
[Energy/Defs](DLMF/Coulomb/Energy/Defs.lean) (all part B definitions; imports
`DLMF.Coulomb.Basic`),
[Energy/Properties](DLMF/Coulomb/Energy/Properties.lean) (§33.14; imports `Energy.Defs`,
`DLMF.Confluent.Coulomb`, `DLMF.Confluent.Whittaker`, `DLMF.OrthogonalPolynomials.Classical`),
[Energy/Connection](DLMF/Coulomb/Energy/Connection.lean) (§33.16; imports
`Energy.Properties`, `DLMF.Confluent.CoulombIrregular`),
[Energy/Recurrence](DLMF/Coulomb/Energy/Recurrence.lean) (§§33.17–33.18; imports
`Energy.Defs`),
[Energy/Series](DLMF/Coulomb/Energy/Series.lean) (§§33.19–33.20; imports `Energy.Defs`,
`DLMF.Bessel.Basic`, `DLMF.Bessel.Modified`) and
[Energy/Asymptotics](DLMF/Coulomb/Energy/Asymptotics.lean) (§33.21; imports `Energy.Defs`).
There are no upstream pointers: Mathlib and TauCeti have no Coulomb functions.

**Counts (part B).** §§33.14, 33.16–33.21 have 57 numbered equations (33.14: 16, 33.16: 18,
33.17: 4, 33.18: 1, 33.19: 7, 33.20: 9, 33.21: 2), all covered by project declarations;
in addition 4 prose IDs (33.14.i, 33.14.ii, 33.14.iii, 33.14.iv) carry tags. Excluded:
§33.15 (graphics, no numbered equations), §33.22 (application, 12 numbered equations
33.22.E1–33.22.E12), §§33.23–33.26 (computation, no numbered equations). The 100 declarations
of the six modules are 21 definitions (all in `Energy/Defs`) and 79 theorems: 40 proved (of
which 18 are untagged helper and API lemmas, and 2 are proved from admissions) and 39 direct
admissions.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Energy/Defs](DLMF/Coulomb/Energy/Defs.lean): 0 admissions; 21 definitions.
- [Energy/Properties](DLMF/Coulomb/Energy/Properties.lean): 13 admissions; 31 theorems: 18 proved,
  13 admitted.
- [Energy/Connection](DLMF/Coulomb/Energy/Connection.lean): 11 admissions; 21 theorems: 10 proved
  (2 from admissions), 11 admitted.
- [Energy/Recurrence](DLMF/Coulomb/Energy/Recurrence.lean): 5 admissions; 5 theorems: 5 admitted.
- [Energy/Series](DLMF/Coulomb/Energy/Series.lean): 8 admissions; 20 theorems: 12 proved,
  8 admitted.
- [Energy/Asymptotics](DLMF/Coulomb/Energy/Asymptotics.lean): 2 admissions; 2 theorems:
  2 admitted.

### Domains, conventions and source corrections (part B)

- **`κ` and `f`.** `coulombKappa ε r` is 33.14.6 with the upper sign `κ = iε^{-1/2}` for `ε > 0`.
  `coulombf ε ℓ r` is, for `ε ≠ 0`, the real part of the Kummer form 33.14.5
  (`coulombfKummer κ ℓ r`); `coulombfKummer_neg` proves the immateriality of the sign of `κ`
  (Kummer's transformation) and `ofReal_coulombf` the reality, so `(f : ℂ)` equals 33.14.5
  and 33.14.4 exactly. At `ε = 0` it is the confluent limit `(2r)^{ℓ+1} ₀F̃₁(;2ℓ+2;-2r)`;
  the Bessel forms 33.20.1–33.20.2 of `f(0,ℓ;r)` are proved from it.
- **`h`.** `coulombh` is the real part of 33.14.7 (`coulombhFormula`, with `W` and `M` written
  through Tricomi's `U` and Kummer's `M`), except at `ε = 0` and at the poles of `Γ(ℓ+1-κ)`
  (`ε = -1/n²`, `n ≥ ℓ+1`, `r > 0`), where 33.14.7 is a removable `∞ · 0` and `coulombh` is the
  limit in `ε` along punctured neighbourhoods. mpmath confirms that `h` is continuous there and
  that the limit at `ε = 0` is the Bessel value 33.20.1–33.20.2; the existence of the limits is
  part of the admitted `analyticAt_coulombh`. The value at `r = 0` is junk.
- **`s`, `c`.** Complex valued, `(B/2)^{1/2} f` and `(2B)^{-1/2} h` with principal powers, so they
  are imaginary when `B < 0`, as DLMF says (`coulombs_re_eq_zero_of_neg`, proved); the
  Wronskian 33.14.16 for `c`, `s` is stated for `B ≠ 0`. `φ_{n,ℓ}` (`hydrogenRadial`) is real,
  with the first equality of 33.14.14 proved for `n ≥ ℓ+1` (DLMF's "`n = ℓ, ℓ+1, …`" after
  33.14.15 should read `n = ℓ+1, ℓ+2, …`, since `A(-1/ℓ², ℓ) = 0`).
- **Distributional and completeness statements.** 33.14.13 is stated against smooth compactly
  supported test functions on `(0,∞)` with a cut-off `∫₀^R`, `R → ∞`; the incompleteness of
  `{φ_{n,ℓ}}` as the existence of a nonzero `L²(0,∞)` function orthogonal to all of them.
- **Whittaker functions of §33.16.** `coulombZeta`, `coulombXi` use Tricomi's `U` directly; the
  argument `e^{iπ}2r/ν` of `ξ_ℓ` is `-(2r/ν)` with the principal branch `ph = π`. (The mpmath
  value `exp(1j*pi)` has a negative imaginary part, which puts `whitw` on the wrong side of the
  cut; the checks use `-x + 0i` approached from above.)
- **Exceptional parameters.** Where DLMF divides by `Γ(ν-ℓ)` or multiplies by it, the
  statements assume `A(ε,ℓ) ≠ 0` (equivalently `ν - ℓ` not a nonpositive integer) and, for the
  square roots of 33.16.17–33.16.18, `A(ε,ℓ) > 0`; 33.14.12 assumes that `κ - ℓ` is not a
  nonpositive integer; 33.19.3 assumes `ε ≠ 0`, `r ≠ 0`, `A(ε,ℓ) ≠ 0`.
- **Source corrections** (confirmed numerically, mpmath 30–40 digits; for 33.16.15 also by the
  Lean proof of the corrected form from 33.16.6–33.16.7):
  - 33.16.15: `s = (-1)^{ℓ+1}e^{π/τ}(πτ)^{-1/2}F_ℓ(1/τ,-τr)`,
    `c = (-1)^ℓ e^{-π/τ}(πτ)^{-1/2}G_ℓ(1/τ,-τr)` (DLMF omits these factors);
  - 33.16.17: prefactor `(-1)^ℓ/(2ν)^{1/2}` instead of `(-1)^ℓ/(2ν^{1/2})`;
  - 33.16.18: `K(ν,ℓ)` and `1/K(ν,ℓ)` interchanged (three places);
  - 33.19.3: the finite sum must be doubled, and for `ε < 0`, `r < 0` the digamma terms use
    `κ = +(-ε)^{-1/2}`.
- **Verification.** mpmath (scripts in the agent scratch directory): 33.14.4–33.14.8 (including
  the sign immateriality and the reality of `f`, `h`), 33.14.12, 33.14.14–33.14.16, the ODE
  33.14.1, all of 33.16 (with the corrections above), 33.17.1–33.17.4 (`ε ∈ {0.3, -0.13, 0}`),
  33.18.1 (`ℓ` up to 40), 33.19.1–33.19.7 (`ℓ ≤ 3`), 33.20.1–33.20.9 and 33.21.1–33.21.2
  (`|r|` up to 300), and the continuity of `h` at `ε = 0` and at `ε = -1/n²`.

### Numbered formulas and prose items (part B)

## [§33.14 Definitions and Basic Properties](https://dlmf.nist.gov/33.14)
- [33.14.i](https://dlmf.nist.gov/33.14.i): [`DLMF.Coulomb.coulombf_coulombh_isEquivalent_zero`](DLMF/Coulomb/Energy/Properties.lean#L173) (admitted)
- [33.14.ii](https://dlmf.nist.gov/33.14.ii): [`DLMF.Coulomb.coulombfKummer_neg`](DLMF/Coulomb/Energy/Q2eRegular.lean#L92) (proved); [`DLMF.Coulomb.analyticAt_coulombf`](DLMF/Coulomb/Energy/Properties.lean#L95) (admitted)
- [33.14.iii](https://dlmf.nist.gov/33.14.iii): [`DLMF.Coulomb.coulombhKappa_neg`](DLMF/Coulomb/Energy/Properties.lean#L195) (admitted); [`DLMF.Coulomb.analyticAt_coulombh`](DLMF/Coulomb/Energy/Properties.lean#L203) (admitted)
- [33.14.iv](https://dlmf.nist.gov/33.14.iv): [`DLMF.Coulomb.coulombs_re_eq_zero_of_neg`](DLMF/Coulomb/Energy/Properties.lean#L276) (proved); [`DLMF.Coulomb.hydrogenRadial_eq_laguerre`](DLMF/Coulomb/Energy/Properties.lean#L393) (proved); [`DLMF.Coulomb.hydrogenRadial_not_complete`](DLMF/Coulomb/Energy/Properties.lean#L472) (admitted)
- [33.14.E1](https://dlmf.nist.gov/33.14.E1): [`DLMF.Coulomb.coulombf_ode`](DLMF/Coulomb/Energy/Properties.lean#L104) (proved); [`DLMF.Coulomb.coulombh_ode`](DLMF/Coulomb/Energy/Properties.lean#L127) (admitted)
- [33.14.E2](https://dlmf.nist.gov/33.14.E2): [`DLMF.Coulomb.coulomb_potential_substitution`](DLMF/Coulomb/Energy/Properties.lean#L135) (proved)
- [33.14.E3](https://dlmf.nist.gov/33.14.E3): [`DLMF.Coulomb.turningPointR`](DLMF/Coulomb/Energy/Defs.lean#L147) (definition); [`DLMF.Coulomb.turningPointR_spec`](DLMF/Coulomb/Energy/Properties.lean#L145) (proved); [`DLMF.Coulomb.turningPointR_pos`](DLMF/Coulomb/Energy/Properties.lean#L161) (proved)
- [33.14.E4](https://dlmf.nist.gov/33.14.E4): [`DLMF.Coulomb.coulombf_eq_whittakerM`](DLMF/Coulomb/Energy/Properties.lean#L80) (proved)
- [33.14.E5](https://dlmf.nist.gov/33.14.E5): [`DLMF.Coulomb.coulombf`](DLMF/Coulomb/Energy/Defs.lean#L76) (definition); [`DLMF.Coulomb.ofReal_coulombf`](DLMF/Coulomb/Energy/Properties.lean#L72) (proved)
- [33.14.E6](https://dlmf.nist.gov/33.14.E6): [`DLMF.Coulomb.coulombKappa`](DLMF/Coulomb/Energy/Defs.lean#L61) (definition) — upper sign `+i ε^{-1/2}` for `ε > 0`; `r = 0` with `ε < 0` takes the `r < 0` branch
- [33.14.E7](https://dlmf.nist.gov/33.14.E7): [`DLMF.Coulomb.coulombh`](DLMF/Coulomb/Energy/Defs.lean#L111) (definition); [`DLMF.Coulomb.ofReal_coulombh`](DLMF/Coulomb/Energy/Properties.lean#L183) (admitted) — `coulombh` is the limit in `ε` at `ε = 0` and at the poles of `Γ(ℓ+1-κ)` (`ε = -1/n²`, `n ≥ ℓ+1`, `r > 0`)
- [33.14.E8](https://dlmf.nist.gov/33.14.E8): [`DLMF.Coulomb.coulombSFactor`](DLMF/Coulomb/Energy/Defs.lean#L86) (definition)
- [33.14.E9](https://dlmf.nist.gov/33.14.E9): [`DLMF.Coulomb.coulombs`](DLMF/Coulomb/Energy/Defs.lean#L134) (definition); [`DLMF.Coulomb.coulombc`](DLMF/Coulomb/Energy/Defs.lean#L141) (definition) — complex valued with principal powers, imaginary when `B < 0`
- [33.14.E10](https://dlmf.nist.gov/33.14.E10): [`DLMF.Coulomb.coulombBFactor`](DLMF/Coulomb/Energy/Defs.lean#L127) (definition)
- [33.14.E11](https://dlmf.nist.gov/33.14.E11): [`DLMF.Coulomb.coulombAProd`](DLMF/Coulomb/Energy/Defs.lean#L123) (definition)
- [33.14.E12](https://dlmf.nist.gov/33.14.E12): [`DLMF.Coulomb.coulombAProd_eq_Gamma`](DLMF/Coulomb/Energy/Properties.lean#L245) (proved)
- [33.14.E13](https://dlmf.nist.gov/33.14.E13): [`DLMF.Coulomb.coulombs_orthogonality_dirac`](DLMF/Coulomb/Energy/Properties.lean#L297) (admitted) — Dirac delta in the distributional sense (test functions in `C_c^∞(0,∞)`, cut-off `∫₀^R`)
- [33.14.E14](https://dlmf.nist.gov/33.14.E14): [`DLMF.Coulomb.hydrogenRadial`](DLMF/Coulomb/Energy/Defs.lean#L152) (definition); [`DLMF.Coulomb.hydrogenRadial_eq_coulombs`](DLMF/Coulomb/Energy/Properties.lean#L326) (proved); [`DLMF.Coulomb.hydrogenRadial_eq_laguerre`](DLMF/Coulomb/Energy/Properties.lean#L393) (proved) — `n ≥ ℓ+1`
- [33.14.E15](https://dlmf.nist.gov/33.14.E15): [`DLMF.Coulomb.hydrogenRadial_orthonormal`](DLMF/Coulomb/Energy/Properties.lean#L466) (admitted) — `m, n ≥ ℓ+1`
- [33.14.E16](https://dlmf.nist.gov/33.14.E16): [`DLMF.Coulomb.coulomb_wronskian_hf`](DLMF/Coulomb/Energy/Properties.lean#L482) (admitted); [`DLMF.Coulomb.coulomb_wronskian_cs`](DLMF/Coulomb/Energy/Properties.lean#L489) (admitted)
- [33.14.v](https://dlmf.nist.gov/33.14.v): no prose statement beyond 33.14.E16.

## [§33.15 Graphics](https://dlmf.nist.gov/33.15)
- [33.15](https://dlmf.nist.gov/33.15): excluded: graphics.

## [§33.16 Connection Formulas](https://dlmf.nist.gov/33.16)
- [33.16.E1](https://dlmf.nist.gov/33.16.E1): [`DLMF.Coulomb.coulombF_eq_coulombf`](DLMF/Coulomb/Energy/Connection.lean#L71) (proved)
- [33.16.E2](https://dlmf.nist.gov/33.16.E2): [`DLMF.Coulomb.coulombG_eq_coulombh`](DLMF/Coulomb/Energy/Connection.lean#L91) (admitted)
- [33.16.E3](https://dlmf.nist.gov/33.16.E3): [`DLMF.Coulomb.coulombf_eq_coulombF_pos`](DLMF/Coulomb/Energy/Connection.lean#L151) (proved) — notation `τ = ε^{1/2}`, written inline as `Real.sqrt ε`
- [33.16.E4](https://dlmf.nist.gov/33.16.E4): [`DLMF.Coulomb.coulombf_eq_coulombF_pos`](DLMF/Coulomb/Energy/Connection.lean#L151) (proved)
- [33.16.E5](https://dlmf.nist.gov/33.16.E5): [`DLMF.Coulomb.coulombh_eq_coulombG_pos`](DLMF/Coulomb/Energy/Connection.lean#L192) (admitted)
- [33.16.E6](https://dlmf.nist.gov/33.16.E6): [`DLMF.Coulomb.coulombf_eq_coulombF_neg`](DLMF/Coulomb/Energy/Connection.lean#L201) (proved)
- [33.16.E7](https://dlmf.nist.gov/33.16.E7): [`DLMF.Coulomb.coulombh_eq_coulombG_neg`](DLMF/Coulomb/Energy/Connection.lean#L248) (admitted)
- [33.16.E8](https://dlmf.nist.gov/33.16.E8): [`DLMF.Coulomb.coulombf_eq_whittaker_pos`](DLMF/Coulomb/Energy/Connection.lean#L439) (proved) — notation `ν = (-ε)^{-1/2}`, written inline as a `let`
- [33.16.E9](https://dlmf.nist.gov/33.16.E9): [`DLMF.Coulomb.coulombZeta`](DLMF/Coulomb/Energy/Defs.lean#L161) (definition); [`DLMF.Coulomb.coulombXi`](DLMF/Coulomb/Energy/Defs.lean#L168) (definition)
- [33.16.E10](https://dlmf.nist.gov/33.16.E10): [`DLMF.Coulomb.coulombf_eq_whittaker_pos`](DLMF/Coulomb/Energy/Connection.lean#L439) (proved)
- [33.16.E11](https://dlmf.nist.gov/33.16.E11): [`DLMF.Coulomb.coulombh_eq_whittaker_pos`](DLMF/Coulomb/Energy/Connection.lean#L532) (admitted)
- [33.16.E12](https://dlmf.nist.gov/33.16.E12): [`DLMF.Coulomb.coulombf_eq_whittaker_neg`](DLMF/Coulomb/Energy/Connection.lean#L543) (proved)
- [33.16.E13](https://dlmf.nist.gov/33.16.E13): [`DLMF.Coulomb.coulombh_eq_whittaker_neg`](DLMF/Coulomb/Energy/Connection.lean#L645) (proved)
- [33.16.E14](https://dlmf.nist.gov/33.16.E14): [`DLMF.Coulomb.coulombs_coulombc_eq_pos`](DLMF/Coulomb/Energy/Connection.lean#L257) (proved from admissions)
- [33.16.E15](https://dlmf.nist.gov/33.16.E15): [`DLMF.Coulomb.coulombs_coulombc_eq_neg`](DLMF/Coulomb/Energy/Connection.lean#L284) (proved from admissions) — corrected: DLMF omits the factors `(-1)^{ℓ+1}e^{π/τ}` (for `s`) and `(-1)^ℓ e^{-π/τ}` (for `c`); the corrected form is proved from 33.16.6–33.16.7 and the definitions
- [33.16.E16](https://dlmf.nist.gov/33.16.E16): [`DLMF.Coulomb.coulombKNorm`](DLMF/Coulomb/Energy/Defs.lean#L178) (definition)
- [33.16.E17](https://dlmf.nist.gov/33.16.E17): [`DLMF.Coulomb.coulombs_coulombc_eq_whittaker_pos`](DLMF/Coulomb/Energy/Connection.lean#L700) (admitted) — corrected: prefactor `(-1)^ℓ/(2ν)^{1/2}`, not `(-1)^ℓ/(2ν^{1/2})`; hypothesis `A(ε,ℓ) > 0`
- [33.16.E18](https://dlmf.nist.gov/33.16.E18): [`DLMF.Coulomb.coulombs_coulombc_eq_whittaker_neg`](DLMF/Coulomb/Energy/Connection.lean#L718) (proved) — corrected: `K(ν,ℓ)` and `1/K(ν,ℓ)` interchanged in DLMF; hypothesis `A(ε,ℓ) > 0`
- [33.16](https://dlmf.nist.gov/33.16): the prose only introduces the notation `τ`, `ν`; no further statement.

## [§33.17 Recurrence Relations and Derivatives](https://dlmf.nist.gov/33.17)
- [33.17.E1](https://dlmf.nist.gov/33.17.E1): [`DLMF.Coulomb.coulombf_recurrence`](DLMF/Coulomb/Energy/Recurrence.lean#L28) (proved) — `ℓ ≥ 1`
- [33.17.E2](https://dlmf.nist.gov/33.17.E2): [`DLMF.Coulomb.coulombh_recurrence`](DLMF/Coulomb/Energy/Recurrence.lean#L44) (admitted) — `ℓ ≥ 1`, `r ≠ 0`
- [33.17.E3](https://dlmf.nist.gov/33.17.E3): [`DLMF.Coulomb.coulombf_deriv`](DLMF/Coulomb/Energy/Recurrence.lean#L52) (proved)
- [33.17.E4](https://dlmf.nist.gov/33.17.E4): [`DLMF.Coulomb.coulombh_deriv`](DLMF/Coulomb/Energy/Recurrence.lean#L68) (admitted)

## [§33.18 Limiting Forms for Large ℓ](https://dlmf.nist.gov/33.18)
- [33.18.E1](https://dlmf.nist.gov/33.18.E1): [`DLMF.Coulomb.coulombf_coulombh_isEquivalent_atTop`](DLMF/Coulomb/Energy/Recurrence.lean#L76) (admitted)

## [§33.19 Power-Series Expansions in r](https://dlmf.nist.gov/33.19)
- [33.19.E1](https://dlmf.nist.gov/33.19.E1): [`DLMF.Coulomb.coulombf_hasSum`](DLMF/Coulomb/Energy/Series.lean#L140) (proved)
- [33.19.E2](https://dlmf.nist.gov/33.19.E2): [`DLMF.Coulomb.coulombAlpha`](DLMF/Coulomb/Energy/Defs.lean#L184) (definition); [`DLMF.Coulomb.coulombAlpha_zero_one`](DLMF/Coulomb/Energy/Series.lean#L47) (proved); [`DLMF.Coulomb.coulombAlpha_recurrence`](DLMF/Coulomb/Energy/Series.lean#L54) (proved)
- [33.19.E3](https://dlmf.nist.gov/33.19.E3): [`DLMF.Coulomb.coulombh_hasSum`](DLMF/Coulomb/Energy/Series.lean#L151) (admitted) — corrected: the finite sum is doubled, and for `ε < 0` the digamma terms use `κ = +(-ε)^{-1/2}` for both signs of `r`; hypotheses `ε ≠ 0`, `r ≠ 0`, `A(ε,ℓ) ≠ 0`
- [33.19.E4](https://dlmf.nist.gov/33.19.E4): [`DLMF.Coulomb.coulombGammaCoeff`](DLMF/Coulomb/Energy/Defs.lean#L194) (definition); [`DLMF.Coulomb.coulombGammaCoeff_recurrence`](DLMF/Coulomb/Energy/Series.lean#L67) (proved)
- [33.19.E5](https://dlmf.nist.gov/33.19.E5): [`DLMF.Coulomb.coulombDeltaCoeff`](DLMF/Coulomb/Energy/Defs.lean#L213) (definition); [`DLMF.Coulomb.coulombDeltaCoeff_zero_one`](DLMF/Coulomb/Energy/Series.lean#L106) (proved)
- [33.19.E6](https://dlmf.nist.gov/33.19.E6): [`DLMF.Coulomb.coulombDeltaCoeff_recurrence`](DLMF/Coulomb/Energy/Series.lean#L91) (proved)
- [33.19.E7](https://dlmf.nist.gov/33.19.E7): [`DLMF.Coulomb.coulombBetaCoeff`](DLMF/Coulomb/Energy/Defs.lean#L203) (definition); [`DLMF.Coulomb.coulombBetaCoeff_recurrence`](DLMF/Coulomb/Energy/Series.lean#L79) (proved)
- [33.19](https://dlmf.nist.gov/33.19): the convergence statement (all finite `r`, except `r = 0` for 33.19.3) is part of the `HasSum` statements of 33.19.E1 and 33.19.E3.

## [§33.20 Expansions for Small |ε|](https://dlmf.nist.gov/33.20)
- [33.20.E1](https://dlmf.nist.gov/33.20.E1): [`DLMF.Coulomb.coulombf_zero_eq_besselJ`](DLMF/Coulomb/Energy/Series.lean#L182) (proved); [`DLMF.Coulomb.coulombh_zero_eq_besselY`](DLMF/Coulomb/Energy/Series.lean#L229) (admitted)
- [33.20.E2](https://dlmf.nist.gov/33.20.E2): [`DLMF.Coulomb.coulombf_zero_eq_besselI`](DLMF/Coulomb/Energy/Series.lean#L198) (proved); [`DLMF.Coulomb.coulombh_zero_eq_besselK`](DLMF/Coulomb/Energy/Series.lean#L235) (admitted)
- [33.20.E3](https://dlmf.nist.gov/33.20.E3): [`DLMF.Coulomb.coulombf_hasSum_eps_pos`](DLMF/Coulomb/Energy/Series.lean#L246) (admitted); [`DLMF.Coulomb.coulombf_hasSum_eps_neg`](DLMF/Coulomb/Energy/Series.lean#L257) (admitted)
- [33.20.E4](https://dlmf.nist.gov/33.20.E4): [`DLMF.Coulomb.coulombf_hasSum_eps_pos`](DLMF/Coulomb/Energy/Series.lean#L246) (admitted)
- [33.20.E5](https://dlmf.nist.gov/33.20.E5): [`DLMF.Coulomb.coulombf_hasSum_eps_neg`](DLMF/Coulomb/Energy/Series.lean#L257) (admitted)
- [33.20.E6](https://dlmf.nist.gov/33.20.E6): [`DLMF.Coulomb.coulombCkp`](DLMF/Coulomb/Energy/Defs.lean#L226) (definition); [`DLMF.Coulomb.coulombCkp_eq_zero`](DLMF/Coulomb/Energy/Series.lean#L116) (proved); [`DLMF.Coulomb.coulombCkp_recurrence`](DLMF/Coulomb/Energy/Series.lean#L127) (proved)
- [33.20.E7](https://dlmf.nist.gov/33.20.E7): [`DLMF.Coulomb.coulombh_asymptotic_eps_pos`](DLMF/Coulomb/Energy/Series.lean#L268) (admitted); [`DLMF.Coulomb.coulombh_asymptotic_eps_neg`](DLMF/Coulomb/Energy/Series.lean#L280) (admitted)
- [33.20.E8](https://dlmf.nist.gov/33.20.E8): [`DLMF.Coulomb.coulombh_asymptotic_eps_pos`](DLMF/Coulomb/Energy/Series.lean#L268) (admitted)
- [33.20.E9](https://dlmf.nist.gov/33.20.E9): [`DLMF.Coulomb.coulombh_asymptotic_eps_neg`](DLMF/Coulomb/Energy/Series.lean#L280) (admitted)
- [33.20.ii](https://dlmf.nist.gov/33.20.ii): the convergence of 33.20.3 for all `r` and `ε` is part of 33.20.E3.
- [33.20.iv](https://dlmf.nist.gov/33.20.iv): no statement (references only: Curtis 1964a, §7).

## [§33.21 Asymptotic Approximations for Large |r|](https://dlmf.nist.gov/33.21)
- [33.21.E1](https://dlmf.nist.gov/33.21.E1): [`DLMF.Coulomb.coulombZeta_coulombXi_isEquivalent_atTop`](DLMF/Coulomb/Energy/Asymptotics.lean#L30) (admitted)
- [33.21.E2](https://dlmf.nist.gov/33.21.E2): [`DLMF.Coulomb.coulombZeta_coulombXi_isEquivalent_atBot`](DLMF/Coulomb/Energy/Asymptotics.lean#L40) (admitted)
- [33.21.i](https://dlmf.nist.gov/33.21.i): methods (combine §33.16 with 33.10.1, 33.21.1–33.21.2 or §§10.7(ii), 10.30(ii)); no separate statement.
- [33.21.ii](https://dlmf.nist.gov/33.21.ii): no statement (references only: Curtis 1964a, §6).

## [§33.22 Particle Scattering and Atomic and Molecular Spectra](https://dlmf.nist.gov/33.22)
- [33.22](https://dlmf.nist.gov/33.22): excluded: application (33.22.E1–33.22.E12). Mathematical content: the radial Schrödinger equation 33.22.1 and its reduction 33.22.3 to the Coulomb equation; the scalings 33.22.4 (`ρ`, `η`), 33.22.5 (`r`, `ε`) and 33.22.6 (`z`, `κ`) and the tables of signs for attractive, zero and repulsive potentials; the conversion formulas 33.22.7–33.22.12 among `(η,ρ)`, `(ε,r)` and `(κ,z)` (33.22.7 is 33.14.2, formalized as `coulomb_potential_substitution`; 33.22.8 matches the Kummer form of `F_ℓ`; 33.22.11–33.22.12 restate 33.14.6); the remark that `φ_{n,ℓ}` of 33.14.14 are the hydrogenic bound states, and the penetrability `ρ/(F_ℓ² + G_ℓ²)`. No further theorem.

## [§33.23 Methods of Computation](https://dlmf.nist.gov/33.23)
- [33.23](https://dlmf.nist.gov/33.23): excluded: computation.

## [§33.24 Tables](https://dlmf.nist.gov/33.24)
- [33.24](https://dlmf.nist.gov/33.24): excluded: computation.

## [§33.25 Approximations](https://dlmf.nist.gov/33.25)
- [33.25](https://dlmf.nist.gov/33.25): excluded: computation.

## [§33.26 Software](https://dlmf.nist.gov/33.26)
- [33.26](https://dlmf.nist.gov/33.26): excluded: computation.
