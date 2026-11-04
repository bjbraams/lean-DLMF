# DLMF Chapter 13 acquisition inventory

Reviewed against the live [NIST DLMF Chapter 13](https://dlmf.nist.gov/13) on
2026-09-17 (Version 1.2.8, release 2026-09-15) and the project's local Mathlib
**v4.34.0** sources. The current toolchain and pinned Mathlib revision are listed in the
[README](../../README.md#dependencies-and-upstream-reuse); this acquisition inventory
was not re-reviewed in full against those newer sources.

This inventory covers numbered equations in §§13.2–13.26. Notation §13.1,
applications §§13.27–13.28, and computation §§13.29–13.32 were not acquired.
Graphics are excluded.

## What was added

New modules under `DLMF/Confluent/` record tagged statements for Kummer `M`,
Tricomi `U`, and Whittaker `M_{κ,μ}`, `W_{κ,μ}`. Tricomi's function is defined
by the connection formula [13.2.42](https://dlmf.nist.gov/13.2.E42). Olver's
regularized `𝐌` is Mathlib's `regularizedHGFun {a} {b}` and is not duplicated.
Existing project theorems were tagged rather than copied. Statements already
supplied by Mathlib are identified in [MathlibCoverage.lean](MathlibCoverage.lean)
and below, without duplicate project declarations.

At acquisition, the new identities were admitted (`sorry`) unless they were already
proved in `Basic.lean` or `Whittaker.lean`. Subsequent proof rounds have removed most
of those admissions. No AAR source statement was changed.

## Interpretation and domain restrictions

- `kummerM` is the totalized series. Nonpositive integer denominators are
  excluded by standing hypotheses `∀ k : ℕ, b ≠ -k`, matching AAR §2.1.
- `kummerU` is the Gamma connection formula, polar at integer `b`. Integer-`b`
  logarithmic cases are recorded as limits or explicit series.
- Complex powers use principal branches. Slit-plane hypotheses specify those
  branches. Several formulas are acquired on convenient real rays (`x > 0`) or
  real parameter ranges; those are restricted forms of the source statements.
- Continued fractions use Mathlib `GenContFract` on a real subdomain, as in
  DLMF Chapter 15.
- Remainders use Mathlib `Asymptotics.IsBigO`. Leading terms also appear as
  `Tendsto` statements.

“Deferred” means the equation was reviewed but no formal theorem was introduced
because the required function, contour, or turning-point API is absent.

## Mathlib coverage

In `Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean`:

- `regularizedHGFun {a} {b}` is Olver's `𝐌(a,b,z)` ([13.2.3](https://dlmf.nist.gov/13.2.E3)).
- Infinite radius for `p ≤ q` includes the confluent case.
- Empty-denominator series supplies `{}_2F_0` in [13.6.21](https://dlmf.nist.gov/13.6.E21).

Mathlib has no named Kummer `M`, Tricomi `U`, Whittaker pair, incomplete gamma,
or error function. Project definitions `erf`, `lowerIncompleteGamma`,
`erfc`, and `upperIncompleteGamma` are used in §13.6 and §13.18.

## Existing tagged project results

| Equation | Existing declaration |
| --- | --- |
| 13.2.E1 | `kummerM_ode` |
| 13.2.E2 | `kummerM` |
| 13.2.E4 | `kummerM_eq_mul_regularizedHGFun` |
| 13.2.E39 | `kummerM_kummer_transform` |
| 13.3.E15 | `DLMF.Confluent.deriv_kummerM` in `Confluent/Basic/KummerContiguous.lean` |
| 13.4.E1 | `kummerM_eq_euler_integral` (the `M` form); regularized form in `IntegralRepresentations.lean` |
| 13.6.E1 | `kummerM_self` |
| 13.6.E3 | `kummerM_of_zero_param`; `U` form in `Relations.lean` |
| 13.6.E5 | `lowerIncompleteGamma` |
| 13.6.E7 | `erf` |
| 13.14.E1 | `whittakerM_ode`, `whittakerW_ode` |
| 13.14.E2 | `whittakerM` |
| 13.14.E33 | `whittakerW` |

## Deferred infrastructure

| Equations | Reason |
| --- | --- |
| 13.2.E27–E32 | Integer-`b` second-kind logarithmic tables; generic case is 13.2.E9 |
| 13.4.E9–E15, 13.10.E8–E9, 13.16.E10, 13.23.E6–E7 | Hankel, Pochhammer, and loop contours |
| 13.7.E5–E9, 13.7.E11–E13 | Remainder-region constants `R₁,R₂,R₃`, `χ(n)`, incomplete-gamma remainder |
| 13.8.E4–E5, 13.8.E8–E16 | Uniform parabolic-cylinder / Bessel / `envelopeJ` approximations |
| 13.6.E11, 13.18.E10 | Airy function not in the project API |
| 13.6.E12–E15, 13.18.E11–E13 | Kummer forms of parabolic cylinder functions; `U(a,z)` and `V(a,z)` now exist (see the Chapter 12 index below) but these relations are not yet stated |
| 13.6(vii) Coulomb | Coulomb wave functions (DLMF Chapter 33) |
| 13.9.E8, 13.22.E1 | Indexed Bessel zeros `j_{ν,r}` |
| 13.20, 13.21 | Uniform Airy/Bessel turning-point expansions in `μ` and `κ` |
| 13.23.E13–E14 | Mellin inversion pair for a general transform `f` |

## Equation-by-equation index (summary)

Names introduced here live in `DLMF.Confluent` except the existing root-namespace
definitions in `Basic.lean` and `Whittaker.lean`.

### Kummer functions

| Section | Tagged / numbered | Notes |
| --- | ---: | --- |
| [13.2](https://dlmf.nist.gov/13.2) | 40 / 44 | E3 is Mathlib. E27–E32 deferred as the integer table. E24–E26 as Wronskian nonvanishing. |
| [13.3](https://dlmf.nist.gov/13.3) | 29 / 29 | Contiguous relations, derivatives, operator identity. |
| [13.4](https://dlmf.nist.gov/13.4) | 12 / 18 | E9–E15 contours deferred. Barnes vertical lines acquired. |
| [13.5](https://dlmf.nist.gov/13.5) | 4 / 4 | Real-domain continued fractions. |
| [13.6](https://dlmf.nist.gov/13.6) | 16 / 23 | Airy, parabolic cylinder, Coulomb deferred. |
| [13.7](https://dlmf.nist.gov/13.7) | 5 / 13 | Poincaré expansions; remainder regions deferred. |
| [13.8](https://dlmf.nist.gov/13.8) | 6 / 18 | Large-`b` series and transition; uniform Bessel deferred. |
| [13.9](https://dlmf.nist.gov/13.9) | 14 / 16 | Zero counts and large-zero asymptotics; Bessel-zero expansion deferred. |
| [13.10](https://dlmf.nist.gov/13.10) | 14 / 16 | Loop integrals deferred. |
| [13.11](https://dlmf.nist.gov/13.11) | 4 / 4 | Bessel series and coefficient recurrence. |
| [13.12](https://dlmf.nist.gov/13.12) | 1 / 1 | Product identity. |
| [13.13](https://dlmf.nist.gov/13.13) | 12 / 12 | Addition theorems. |

### Whittaker functions

| Section | Tagged / numbered | Notes |
| --- | ---: | --- |
| [13.14](https://dlmf.nist.gov/13.14) | 24 / 35 | Definitions, connections, Wronskians, leading limits. Logarithmic integer-order tables and some `z→0` cases overlap 13.2. |
| [13.15](https://dlmf.nist.gov/13.15) | 26 / 26 | Contiguous relations and derivatives. |
| [13.16](https://dlmf.nist.gov/13.16) | 10 / 12 | Real-line integrals; one Barnes contour deferred. |
| [13.17](https://dlmf.nist.gov/13.17) | 4 / 4 | Real-domain continued fractions. |
| [13.18](https://dlmf.nist.gov/13.18) | 12 / 17 | Airy and parabolic cylinder deferred. |
| [13.19](https://dlmf.nist.gov/13.19) | 2 / 3 | Poincaré expansions on the positive ray; sector form 13.19.2 recorded via 13.7.2 analogue. |
| [13.20](https://dlmf.nist.gov/13.20) | 0 / 19 | Deferred: uniform Airy/Bessel in `μ`. |
| [13.21](https://dlmf.nist.gov/13.21) | 0 / 25 | Deferred: uniform Airy/Bessel in `κ`. |
| [13.22](https://dlmf.nist.gov/13.22) | 0 / 1 | Deferred: Bessel-zero expansion. |
| [13.23](https://dlmf.nist.gov/13.23) | 10 / 14 | Loops and inversion pair deferred. |
| [13.24](https://dlmf.nist.gov/13.24) | 3 / 3 | Bessel series and generating function. |
| [13.25](https://dlmf.nist.gov/13.25) | 1 / 1 | Product identity. |
| [13.26](https://dlmf.nist.gov/13.26) | 12 / 12 | Addition theorems. |

## DLMF Chapter 12: parabolic cylinder functions

[ParabolicCylinder.lean](ParabolicCylinder.lean) defines `U(a,z)` through Tricomi's `U` (12.7.14),
`V(a,z)` through its initial values with reciprocal Gamma factors (entire in `a` and `z`), and
`D_ν`. All tagged statements below are proved (2026-10-17). The Wronskian 12.2.12 was checked
against the DLMF website. The connection formula for `U(-a, ±iz)` is 12.2.17; its classical
form needs `1/2 + a ∉ -ℕ`. Not yet stated: the large-`x` behaviour of `V` (12.9.2), the
remaining connection formulas 12.2.18–19, and the uniform expansions of §§12.10–12.11.

| DLMF | Declaration | Status |
| --- | --- | --- |
| [12.2.E2](https://dlmf.nist.gov/12.2.E2) | [hasDerivAt_parabolicCylinderUDeriv](ParabolicCylinder.lean) (line 161); [hasDerivAt_parabolicCylinderVDeriv](ParabolicCylinder.lean) (line 1072) | proved |
| [12.2.E5](https://dlmf.nist.gov/12.2.E5) | [parabolicCylinderD](ParabolicCylinder.lean) (line 154) | definition |
| [12.2.E6](https://dlmf.nist.gov/12.2.E6) | [parabolicCylinderU_zero](ParabolicCylinder.lean) (line 176) | proved |
| [12.2.E7](https://dlmf.nist.gov/12.2.E7) | [parabolicCylinderUDeriv_zero](ParabolicCylinder.lean) (line 184) | proved |
| [12.2.E8](https://dlmf.nist.gov/12.2.E8) | [parabolicCylinderV_zero](ParabolicCylinder.lean) (line 1093) | proved |
| [12.2.E9](https://dlmf.nist.gov/12.2.E9) | [parabolicCylinderVDeriv_zero](ParabolicCylinder.lean) (line 1102) | proved |
| [12.2.E10](https://dlmf.nist.gov/12.2.E10) | [parabolicCylinderV_wronskian](ParabolicCylinder.lean) (line 1154) | proved |
| [12.2.E11](https://dlmf.nist.gov/12.2.E11) | [parabolicCylinderU_wronskian_neg](ParabolicCylinder.lean) (line 813) | proved |
| [12.2.E12](https://dlmf.nist.gov/12.2.E12) | [parabolicCylinderU_wronskian_mul_I](ParabolicCylinder.lean) (line 869); [parabolicCylinderU_wronskian_mul_neg_I](ParabolicCylinder.lean) (line 907) | proved |
| [12.2.E13](https://dlmf.nist.gov/12.2.E13) | [parabolicCylinderU_neg_nat_sub_half_neg](ParabolicCylinder.lean) (line 1310) | proved |
| [12.2.E14](https://dlmf.nist.gov/12.2.E14) | [parabolicCylinderV_nat_add_half_neg](ParabolicCylinder.lean) (line 1321) | proved |
| [12.2.E15](https://dlmf.nist.gov/12.2.E15) | [parabolicCylinderU_neg_eq](ParabolicCylinder.lean) (line 1203) | proved |
| [12.2.E16](https://dlmf.nist.gov/12.2.E16) | [parabolicCylinderV_neg_eq](ParabolicCylinder.lean) (line 1252) | proved |
| [12.2.E17](https://dlmf.nist.gov/12.2.E17) | [parabolicCylinderU_connection_mul_I](ParabolicCylinder.lean) (line 957); [parabolicCylinderU_connection_mul_neg_I](ParabolicCylinder.lean) (line 1042) | proved |
| [12.2.E20](https://dlmf.nist.gov/12.2.E20) | [parabolicCylinderV_eq_mul_I](ParabolicCylinder.lean) (line 1357); [parabolicCylinderV_eq_mul_neg_I](ParabolicCylinder.lean) (line 1419) | proved |
| [12.4.E1](https://dlmf.nist.gov/12.4.E1) | [parabolicCylinderU](ParabolicCylinder.lean) (line 142) | definition |
| [12.4.E2](https://dlmf.nist.gov/12.4.E2) | [parabolicCylinderV](ParabolicCylinder.lean) (line 1062) | definition |
| [12.5.E1](https://dlmf.nist.gov/12.5.E1) | [parabolicCylinderU_eq_integral](ParabolicCylinder.lean) (line 694) | proved |
| [12.7.E1](https://dlmf.nist.gov/12.7.E1) | [parabolicCylinderU_neg_half](ParabolicCylinder.lean) (line 193) | proved |
| [12.7.E2](https://dlmf.nist.gov/12.7.E2) | [parabolicCylinderD_nat](ParabolicCylinder.lean) (line 494) | proved |
| [12.7.E12](https://dlmf.nist.gov/12.7.E12) | [parabolicCylinderEven](ParabolicCylinder.lean) (line 60) | definition |
| [12.7.E13](https://dlmf.nist.gov/12.7.E13) | [parabolicCylinderOdd](ParabolicCylinder.lean) (line 65) | definition |
| [12.7.E14](https://dlmf.nist.gov/12.7.E14) | [parabolicCylinderU_eq_kummerU](ParabolicCylinder.lean) (line 211) | proved |
| [12.8.E1](https://dlmf.nist.gov/12.8.E1) | [parabolicCylinderU_three_term](ParabolicCylinder.lean) (line 460) | proved |
| [12.8.E2](https://dlmf.nist.gov/12.8.E2) | [parabolicCylinderU_recurrence_add](ParabolicCylinder.lean) (line 425) | proved |
| [12.8.E3](https://dlmf.nist.gov/12.8.E3) | [parabolicCylinderU_recurrence_sub](ParabolicCylinder.lean) (line 391) | proved |
| [12.8.E4](https://dlmf.nist.gov/12.8.E4) | [parabolicCylinderU_deriv_recurrence](ParabolicCylinder.lean) (line 466) | proved |
| [12.8.E5](https://dlmf.nist.gov/12.8.E5) | [parabolicCylinderV_three_term](ParabolicCylinder.lean) (line 1562) | proved |
| [12.8.E6](https://dlmf.nist.gov/12.8.E6) | [parabolicCylinderV_recurrence_sub](ParabolicCylinder.lean) (line 1520) | proved |
| [12.8.E7](https://dlmf.nist.gov/12.8.E7) | [parabolicCylinderV_recurrence_add](ParabolicCylinder.lean) (line 1480) | proved |
| [12.8.E8](https://dlmf.nist.gov/12.8.E8) | [parabolicCylinderV_deriv_recurrence](ParabolicCylinder.lean) (line 1568) | proved |
| [12.9.E1](https://dlmf.nist.gov/12.9.E1) | [hasAsymptoticExpansion_parabolicCylinderU](ParabolicCylinder.lean) (line 266) | proved |

## Current proof status (2026-10-24)

There are **9 explicit source admissions** in `DLMF/Confluent/`. The Whittaker
series 13.24.2 now has proved absolute convergence and branch cancellation; its
Buchholz transform identity remains open. See the
[parallel proof round](../../REVIEW.md#parallel-admission-removal-and-reuse-round-2026-10-24)
for validation and the latest reuse work. The module counts and inline line
numbers below are historical acquisition data.

## Module snapshot (2026-10-17)

| Module | Theorems | Definitions | `sorry`s on 2026-10-17 |
| --- | ---: | ---: | ---: |
| [Basic.lean](Basic.lean) | 29 | 5 | 1 (pre-existing parabolic zero-free region) |
| [BasicProperties.lean](BasicProperties.lean) | 35 | 1 | 6 |
| [Whittaker.lean](Whittaker.lean) | 23 | 2 | 0 |
| [Recurrence.lean](Recurrence.lean) | 55 | 1 | 0 |
| [IntegralRepresentations.lean](IntegralRepresentations.lean) | 21 | 0 | 9 |
| [ContinuedFractions.lean](ContinuedFractions.lean) | 4 | 8 | 4 |
| [Relations.lean](Relations.lean) | 30 | 2 | 2 |
| [Asymptotics.lean](Asymptotics.lean) | 13 | 2 | 5 |
| [Zeros.lean](Zeros.lean) | 15 | 2 | 10 |
| [Integrals.lean](Integrals.lean) | 24 | 0 | 16 |
| [Series.lean](Series.lean) | 6 | 3 | 6 |
| [ProductsAddition.lean](ProductsAddition.lean) | 26 | 0 | 10 |
| [MathlibCoverage.lean](MathlibCoverage.lean) | 0 | 0 | 0 |

The last column was refreshed on 2026-10-17 from the build's `sorry` warnings (69 in this
directory); later modules (`ParabolicCylinder`, `ConnectionWronskians`, `Coulomb*`, `Regularized`,
`Confluence`, `TricomiRotated`, `AsymptoticConsequences`, `ExpIntegral`, `ErrorFunctions`,
`IncompleteGamma`, `FresnelAsymptotics`, `Continuation`, `Growth`) contain no admissions.

The acquisition introduced Tricomi's `U` and complementary error/incomplete-gamma helpers, together with about 250 tagged statements. All new identities are admitted except the previously proved theorems in `Basic` and `Whittaker`.

## Later additions (2026-10-21)

- [13.11.E3](https://dlmf.nist.gov/13.11.E3): `regularizedHGFun_eq_besselExpansion` in
  `Series.lean` (proved; all a, b, z, stronger than DLMF). The printed J form
  `regularizedHGFun_besselJ_series` was false as stated off the principal branch and is now
  proved under z ≠ 0, b − 2a ≠ 0 and ph z + ph(b − 2a) ∈ (−π, π] (REVIEW.md).
- [13.2.E9](https://dlmf.nist.gov/13.2.E9): `kummerU_nat_denom_recipGamma` and
  `kummerU_nat_log_recipGamma` in `BasicProperties.lean` (proved; all a, stronger than DLMF),
  via `tricomiLogSeriesRecipGamma` (`LogSeries.lean`) and
  `tricomi_numerator_nat_series_recipGamma` (`ParameterDerivatives.lean`).
- [13.2.E19](https://dlmf.nist.gov/13.2.E19): `isBigO_kummerU_at_zero_b_one_recipGamma`
  (proved; all a).
