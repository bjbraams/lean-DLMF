# DLMF Chapter 34 acquisition: 3j, 6j, 9j Symbols

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 34](https://dlmf.nist.gov/34), version 1.2.8, checked on 2026-10-26, by
agent wj (helper prefix `w34_`). The Lean code is in `DLMF/WignerSymbols/` (namespace
`DLMF.WignerSymbols`). The modules, in import order, are
[Basic](DLMF/WignerSymbols/Basic.lean) (all definitions and their API; imports Mathlib only),
[ThreeJ](DLMF/WignerSymbols/ThreeJ.lean) (§§34.2–34.3(vi); imports `Basic` and the
definitions file `DLMF.GeneralizedHypergeometric.Basic`),
[SixJ](DLMF/WignerSymbols/SixJ.lean) (§§34.4–34.5; imports `Basic` and
`DLMF.GeneralizedHypergeometric.Basic`),
[NineJ](DLMF/WignerSymbols/NineJ.lean) (§§34.6–34.7; imports `Basic`),
[ThreeJLegendre](DLMF/WignerSymbols/ThreeJLegendre.lean) (§34.3(vii); imports `Basic` and
`DLMF.Legendre.Harmonics`) and
[LargeParameters](DLMF/WignerSymbols/LargeParameters.lean) (§34.8; imports `Basic`).
There are no upstream pointers: Mathlib has no Wigner, Clebsch–Gordan or Racah
coefficients, and TauCeti has only the Clebsch–Gordan decomposition of `sl₂`-modules
(`TauCeti/Algebra/Lie/Sl2/ClebschGordan.lean`), without coefficients.

**Counts.** §§34.1–34.8 have 64 numbered equations (34.1: 1, 34.2: 6, 34.3: 22, 34.4: 3,
34.5: 23, 34.6: 2, 34.7: 5, 34.8: 2); §34.9 is excluded: graphics, §34.12 is an application
note without mathematical statements, §§34.13–34.15 are excluded: computation, tables and
software, and §34.11 is references only. In scope: 64; covered: 64. In addition 3 prose IDs
(34.4, 34.7.ii, 34.10) carry tags. 67 DLMF IDs are tagged on 76 declarations: 9 definitions,
22 proved theorems and 45 admitted theorems. The 144 declarations of the six modules are 21
definitions (all in `Basic`, 12 of them untagged predicates and helpers), 78 proved theorems
(of which 56 untagged API and helper lemmas) and 45 direct admissions; no proved theorem
depends on an admission.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Basic](DLMF/WignerSymbols/Basic.lean): 0 admissions; 21 definitions, 32 proved API
  lemmas.
- [ThreeJ](DLMF/WignerSymbols/ThreeJ.lean): 10 admissions; 41 theorems: 31 proved (15
  tagged), 10 admitted.
- [SixJ](DLMF/WignerSymbols/SixJ.lean): 19 admissions; 34 theorems: 15 proved (7 tagged),
  19 admitted.
- [NineJ](DLMF/WignerSymbols/NineJ.lean): 11 admissions; 11 theorems: 11 admitted.
- [ThreeJLegendre](DLMF/WignerSymbols/ThreeJLegendre.lean): 4 admissions; 4 theorems:
  4 admitted.
- [LargeParameters](DLMF/WignerSymbols/LargeParameters.lean): 1 admission; 1 theorem:
  1 admitted.

## Domains, conventions and source corrections

- **Quantum numbers.** Angular momenta `j` and projections `m` are rationals; values are
  real. DLMF's standing conditions are predicates: `IsNatQ x` (`x ∈ ℕ`), `IsProjection j m`
  (34.2.2: `j - m, j + m ∈ ℕ`), `IsTriad j₁ j₂ j₃` (34.2.1 with the parity condition:
  `j₁ + j₂ - j₃`, `j₁ - j₂ + j₃`, `-j₁ + j₂ + j₃ ∈ ℕ`; `isTriad_iff` proves the DLMF form),
  `IsAdmissible3j` (34.2.1–34.2.3) and `IsAdmissible6j` (the four triads of 34.4.1).
  Factorials, reciprocal factorials and signs at rational arguments are `factQ`, `invFactQ`
  (`0` at negative arguments) and `signPow` (`(-1)^⌊x⌋`); they are used at integers only.
- **Definitions.** `wigner3j` is Racah's formula 34.2.4 (with `triangleDelta`, 34.2.5) and is
  `0` outside the admissible range; DLMF says the symbol is zero when 34.2.1 or 34.2.3 fails,
  and the value `0` outside the projection ranges 34.2.2 is the convention implicit in all
  summation formulas of the chapter. `clebschGordan` is 34.1.1. `wigner6j` is the single sum
  34.4.2 (zero unless admissible, §34.10); the definition 34.4.1 as a sum of products of four
  `3j` symbols is the theorem `wigner6j_eq_sum_threeJ`. `wigner9j` is 34.6.2 (sum over
  `j ∈ ½ℕ` of products of three `6j` symbols); 34.6.1 is a theorem. `sixJRecursionE` is
  34.5.13 and `largeParameterAngle` is 34.8.2. Summation ranges are the finite sets
  `projections j` and `halfIntegersUpTo x`. The `₃F₂` and `₄F₃` of 34.2.6 and 34.4.3 are the
  terminating `DLMF.Hypergeometric.genFiniteHG` at unit argument, over ℂ.
- **Stronger than DLMF.** The recursions 34.3.13–34.3.15 hold for all arguments (both sides
  vanish outside the admissible ranges by the zero convention) and are stated without
  hypotheses; likewise the sums 34.5.15, 34.5.16, 34.5.23 and 34.7.3–34.7.5. 34.3.19 is
  stated for all complex `x`. 34.3.4 (odd `J`) is proved.
- **Large parameters.** 34.8.1 is stated as an iterated limit: for `δ, ε > 0` there is `L₀`
  such that for every `l₃ ≥ L₀` there is `K` with relative error at most `ε` for all triads
  with `j₁, j₂, j₃ ≥ K` and `sin θ ≥ δ`. The approximation was checked numerically up to
  `j ≈ 1600`.
- **Source corrections.** The prose of §34.4 asserts that the triangle conditions of the four
  triads of a `6j` symbol are equivalent to the existence of a tetrahedron with edges
  `j₁, j₂, j₃, l₁, l₂, l₃` "except in degenerate cases". The converse direction is false
  outside degenerate cases: `{3 2 2; 3 2 2}` satisfies all four triangle conditions and has the
  value `1/14 ≠ 0`, while the Cayley–Menger determinant of the six edges is `-324`
  (`V² = -9/8 < 0`), so no Euclidean tetrahedron exists. Only the necessity direction
  (tetrahedron ⇒ triangle conditions) is acquired, as `triangle_conditions_of_tetrahedron`.
  The 34.4.2 erratum of DLMF version 1.0.7 is already corrected in the current text.
- **Validation.** Every formula was checked in exact rational arithmetic with sympy
  (`wigner_3j`, `wigner_6j`, `wigner_9j`, `clebsch_gordan`, `gaunt`, `Ynm`) on ranges of
  admissible arguments, including the hypothesis-free forms above. Verified as printed: all
  of 34.1–34.8. Strict checks (`-DautoImplicit=false -DrelaxedAutoImplicit=false`) of all six
  modules report no warnings beyond the admissions; the proved theorems use only `propext`,
  `Classical.choice` and `Quot.sound`.

## Numbered formulas and prose items

## [§34.1 Special Notation](https://dlmf.nist.gov/34.1)

- [34.1.E1](https://dlmf.nist.gov/34.1.E1): [`DLMF.WignerSymbols.clebschGordan`](DLMF/WignerSymbols/Basic.lean#L133) (definition)

## [§34.2 Definition: 3j Symbol](https://dlmf.nist.gov/34.2)

- [34.2.E1](https://dlmf.nist.gov/34.2.E1): [`DLMF.WignerSymbols.IsTriad`](DLMF/WignerSymbols/Basic.lean#L72) (definition); [`DLMF.WignerSymbols.isTriad_iff`](DLMF/WignerSymbols/ThreeJ.lean#L141) (proved); [`DLMF.WignerSymbols.wigner3j_eq_zero_of_not_isTriad`](DLMF/WignerSymbols/ThreeJ.lean#L170) (proved). The triangle conditions with the parity condition of §34.2 (`IsTriad`); `isTriad_iff` gives the DLMF form.
- [34.2.E2](https://dlmf.nist.gov/34.2.E2): [`DLMF.WignerSymbols.IsProjection`](DLMF/WignerSymbols/Basic.lean#L67) (definition); [`DLMF.WignerSymbols.wigner3j_eq_zero_of_not_isProjection`](DLMF/WignerSymbols/ThreeJ.lean#L183) (proved). `IsProjection j m`: `j - m, j + m ∈ ℕ`.
- [34.2.E3](https://dlmf.nist.gov/34.2.E3): [`DLMF.WignerSymbols.wigner3j_eq_zero_of_sum_ne_zero`](DLMF/WignerSymbols/ThreeJ.lean#L177) (proved)
- [34.2.E4](https://dlmf.nist.gov/34.2.E4): [`DLMF.WignerSymbols.wigner3j`](DLMF/WignerSymbols/Basic.lean#L118) (definition). Racah's formula; the definition is `0` outside the admissible range (34.2.1–34.2.3).
- [34.2.E5](https://dlmf.nist.gov/34.2.E5): [`DLMF.WignerSymbols.triangleDelta`](DLMF/WignerSymbols/Basic.lean#L106) (definition)
- [34.2.E6](https://dlmf.nist.gov/34.2.E6): [`DLMF.WignerSymbols.wigner3j_eq_hyp3F2`](DLMF/WignerSymbols/ThreeJ.lean#L191) (admitted). `₃F₂` at unit argument as `DLMF.Hypergeometric.genFiniteHG` (terminating), over ℂ.

## [§34.3 Basic Properties: 3j Symbol](https://dlmf.nist.gov/34.3)

- [34.3.E1](https://dlmf.nist.gov/34.3.E1): [`DLMF.WignerSymbols.wigner3j_j_j_zero`](DLMF/WignerSymbols/ThreeJ.lean#L212) (proved)
- [34.3.E2](https://dlmf.nist.gov/34.3.E2): [`DLMF.WignerSymbols.wigner3j_j_j_one_zero`](DLMF/WignerSymbols/ThreeJ.lean#L334) (proved)
- [34.3.E3](https://dlmf.nist.gov/34.3.E3): [`DLMF.WignerSymbols.wigner3j_j_j_one_one`](DLMF/WignerSymbols/ThreeJ.lean#L395) (proved)
- [34.3.E4](https://dlmf.nist.gov/34.3.E4): [`DLMF.WignerSymbols.wigner3j_zero_zero_zero_of_even`](DLMF/WignerSymbols/ThreeJ.lean#L431) (admitted); [`DLMF.WignerSymbols.wigner3j_zero_zero_zero_of_odd`](DLMF/WignerSymbols/ThreeJ.lean#L657) (proved). Odd `J`: proved for all integer `j`s satisfying the triangle conditions.
- [34.3.E5](https://dlmf.nist.gov/34.3.E5): [`DLMF.WignerSymbols.wigner3j_zero_zero_zero_of_even`](DLMF/WignerSymbols/ThreeJ.lean#L431) (admitted); [`DLMF.WignerSymbols.wigner3j_zero_zero_zero_of_odd`](DLMF/WignerSymbols/ThreeJ.lean#L657) (proved). Even `J = 2n`: admitted.
- [34.3.E6](https://dlmf.nist.gov/34.3.E6): [`DLMF.WignerSymbols.wigner3j_stretched`](DLMF/WignerSymbols/ThreeJ.lean#L470) (proved)
- [34.3.E7](https://dlmf.nist.gov/34.3.E7): [`DLMF.WignerSymbols.wigner3j_top`](DLMF/WignerSymbols/ThreeJ.lean#L502) (proved)
- [34.3.E8](https://dlmf.nist.gov/34.3.E8): [`DLMF.WignerSymbols.wigner3j_cycle`](DLMF/WignerSymbols/ThreeJ.lean#L537) (proved); [`DLMF.WignerSymbols.wigner3j_cycle₂`](DLMF/WignerSymbols/ThreeJ.lean#L574) (proved)
- [34.3.E9](https://dlmf.nist.gov/34.3.E9): [`DLMF.WignerSymbols.wigner3j_swap`](DLMF/WignerSymbols/ThreeJ.lean#L580) (proved)
- [34.3.E10](https://dlmf.nist.gov/34.3.E10): [`DLMF.WignerSymbols.wigner3j_neg`](DLMF/WignerSymbols/ThreeJ.lean#L619) (proved)
- [34.3.E11](https://dlmf.nist.gov/34.3.E11): [`DLMF.WignerSymbols.wigner3j_regge₁`](DLMF/WignerSymbols/ThreeJ.lean#L668) (proved)
- [34.3.E12](https://dlmf.nist.gov/34.3.E12): [`DLMF.WignerSymbols.wigner3j_regge₂`](DLMF/WignerSymbols/ThreeJ.lean#L710) (proved)
- [34.3.E13](https://dlmf.nist.gov/34.3.E13): [`DLMF.WignerSymbols.wigner3j_recursion_half`](DLMF/WignerSymbols/ThreeJ.lean#L801) (proved). Stated for all arguments (both sides vanish outside the admissible ranges); stronger than DLMF.
- [34.3.E14](https://dlmf.nist.gov/34.3.E14): [`DLMF.WignerSymbols.wigner3j_recursion_m`](DLMF/WignerSymbols/ThreeJ.lean#L957) (admitted). Stated for all arguments; stronger than DLMF.
- [34.3.E15](https://dlmf.nist.gov/34.3.E15): [`DLMF.WignerSymbols.wigner3j_recursion_j`](DLMF/WignerSymbols/ThreeJ.lean#L968) (admitted). Stated for all arguments; stronger than DLMF.
- [34.3.E16](https://dlmf.nist.gov/34.3.E16): [`DLMF.WignerSymbols.wigner3j_orthogonality_m`](DLMF/WignerSymbols/ThreeJ.lean#L987) (admitted)
- [34.3.E17](https://dlmf.nist.gov/34.3.E17): [`DLMF.WignerSymbols.wigner3j_orthogonality_j`](DLMF/WignerSymbols/ThreeJ.lean#L996) (admitted)
- [34.3.E18](https://dlmf.nist.gov/34.3.E18): [`DLMF.WignerSymbols.wigner3j_sum_sq`](DLMF/WignerSymbols/ThreeJ.lean#L1005) (admitted)
- [34.3.E19](https://dlmf.nist.gov/34.3.E19): [`DLMF.WignerSymbols.legendrePolyP_mul_legendrePolyP`](DLMF/WignerSymbols/ThreeJLegendre.lean#L29) (admitted). Stated for all complex `x` (polynomial identity); stronger than DLMF.
- [34.3.E20](https://dlmf.nist.gov/34.3.E20): [`DLMF.WignerSymbols.sphericalHarmonic_mul_sphericalHarmonic`](DLMF/WignerSymbols/ThreeJLegendre.lean#L38) (admitted)
- [34.3.E21](https://dlmf.nist.gov/34.3.E21): [`DLMF.WignerSymbols.integral_legendrePolyP_mul_mul`](DLMF/WignerSymbols/ThreeJLegendre.lean#L49) (admitted)
- [34.3.E22](https://dlmf.nist.gov/34.3.E22): [`DLMF.WignerSymbols.integral_sphericalHarmonic_mul_mul`](DLMF/WignerSymbols/ThreeJLegendre.lean#L58) (admitted)
- [34.3.v](https://dlmf.nist.gov/34.3.v): no statement (references only).
- [34.3.vi](https://dlmf.nist.gov/34.3.vi): no statement (references only).

## [§34.4 Definition: 6j Symbol](https://dlmf.nist.gov/34.4)

- [34.4](https://dlmf.nist.gov/34.4): [`DLMF.WignerSymbols.triangle_conditions_of_tetrahedron`](DLMF/WignerSymbols/SixJ.lean#L118) (proved). Only the necessity direction is acquired (the tetrahedron edges satisfy the triangle conditions). The converse stated in DLMF prose is false; see "Source corrections".
- [34.4.E1](https://dlmf.nist.gov/34.4.E1): [`DLMF.WignerSymbols.wigner6j_eq_sum_threeJ`](DLMF/WignerSymbols/SixJ.lean#L104) (admitted). The defining sum over projections of 34.4.1 is a theorem; the definition is the single sum 34.4.2.
- [34.4.E2](https://dlmf.nist.gov/34.4.E2): [`DLMF.WignerSymbols.wigner6j`](DLMF/WignerSymbols/Basic.lean#L155) (definition). Version 1.0.7 erratum of DLMF (already corrected in the current DLMF) checked: the printed formula agrees with sympy `wigner_6j`.
- [34.4.E3](https://dlmf.nist.gov/34.4.E3): [`DLMF.WignerSymbols.wigner6j_eq_hyp4F3`](DLMF/WignerSymbols/SixJ.lean#L146) (admitted). `₄F₃` at unit argument as `DLMF.Hypergeometric.genFiniteHG`, over ℂ.

## [§34.5 Basic Properties: 6j Symbol](https://dlmf.nist.gov/34.5)

- [34.5.E1](https://dlmf.nist.gov/34.5.E1): [`DLMF.WignerSymbols.wigner6j_zero`](DLMF/WignerSymbols/SixJ.lean#L251) (proved)
- [34.5.E2](https://dlmf.nist.gov/34.5.E2): [`DLMF.WignerSymbols.wigner6j_half_plus`](DLMF/WignerSymbols/SixJ.lean#L280) (proved)
- [34.5.E3](https://dlmf.nist.gov/34.5.E3): [`DLMF.WignerSymbols.wigner6j_half_minus`](DLMF/WignerSymbols/SixJ.lean#L306) (proved)
- [34.5.E4](https://dlmf.nist.gov/34.5.E4): [`DLMF.WignerSymbols.wigner6j_one_minus_minus`](DLMF/WignerSymbols/SixJ.lean#L332) (proved)
- [34.5.E5](https://dlmf.nist.gov/34.5.E5): [`DLMF.WignerSymbols.wigner6j_one_minus_zero`](DLMF/WignerSymbols/SixJ.lean#L360) (proved)
- [34.5.E6](https://dlmf.nist.gov/34.5.E6): [`DLMF.WignerSymbols.wigner6j_one_minus_plus`](DLMF/WignerSymbols/SixJ.lean#L391) (proved)
- [34.5.E7](https://dlmf.nist.gov/34.5.E7): [`DLMF.WignerSymbols.wigner6j_one_zero_zero`](DLMF/WignerSymbols/SixJ.lean#L419) (proved)
- [34.5.E8](https://dlmf.nist.gov/34.5.E8): [`DLMF.WignerSymbols.wigner6j_swap_columns`](DLMF/WignerSymbols/SixJ.lean#L473) (proved); [`DLMF.WignerSymbols.wigner6j_flip`](DLMF/WignerSymbols/SixJ.lean#L496) (proved)
- [34.5.E9](https://dlmf.nist.gov/34.5.E9): [`DLMF.WignerSymbols.wigner6j_regge₁`](DLMF/WignerSymbols/SixJ.lean#L520) (proved)
- [34.5.E10](https://dlmf.nist.gov/34.5.E10): [`DLMF.WignerSymbols.wigner6j_regge₂`](DLMF/WignerSymbols/SixJ.lean#L546) (proved)
- [34.5.E11](https://dlmf.nist.gov/34.5.E11): [`DLMF.WignerSymbols.wigner6j_recursion`](DLMF/WignerSymbols/SixJ.lean#L610) (admitted). With 34.5.12 and 34.5.13 as one three-term recursion.
- [34.5.E12](https://dlmf.nist.gov/34.5.E12): [`DLMF.WignerSymbols.wigner6j_recursion`](DLMF/WignerSymbols/SixJ.lean#L610) (admitted)
- [34.5.E13](https://dlmf.nist.gov/34.5.E13): [`DLMF.WignerSymbols.sixJRecursionE`](DLMF/WignerSymbols/Basic.lean#L169) (definition)
- [34.5.E14](https://dlmf.nist.gov/34.5.E14): [`DLMF.WignerSymbols.wigner6j_orthogonality`](DLMF/WignerSymbols/SixJ.lean#L627) (admitted)
- [34.5.E15](https://dlmf.nist.gov/34.5.E15): [`DLMF.WignerSymbols.wigner6j_sum_rule`](DLMF/WignerSymbols/SixJ.lean#L641) (admitted). Stated without triangle hypotheses; stronger than DLMF.
- [34.5.E16](https://dlmf.nist.gov/34.5.E16): [`DLMF.WignerSymbols.wigner6j_biedenharn_elliott`](DLMF/WignerSymbols/SixJ.lean#L651) (admitted). Stated without triangle hypotheses; stronger than DLMF.
- [34.5.E17](https://dlmf.nist.gov/34.5.E17): [`DLMF.WignerSymbols.wigner6j_sum_17`](DLMF/WignerSymbols/SixJ.lean#L663) (admitted)
- [34.5.E18](https://dlmf.nist.gov/34.5.E18): [`DLMF.WignerSymbols.wigner6j_sum_18`](DLMF/WignerSymbols/SixJ.lean#L671) (admitted)
- [34.5.E19](https://dlmf.nist.gov/34.5.E19): [`DLMF.WignerSymbols.wigner6j_sum_19`](DLMF/WignerSymbols/SixJ.lean#L680) (admitted)
- [34.5.E20](https://dlmf.nist.gov/34.5.E20): [`DLMF.WignerSymbols.wigner6j_sum_20`](DLMF/WignerSymbols/SixJ.lean#L687) (admitted)
- [34.5.E21](https://dlmf.nist.gov/34.5.E21): [`DLMF.WignerSymbols.wigner6j_sum_21`](DLMF/WignerSymbols/SixJ.lean#L695) (admitted)
- [34.5.E22](https://dlmf.nist.gov/34.5.E22): [`DLMF.WignerSymbols.wigner6j_sum_22`](DLMF/WignerSymbols/SixJ.lean#L705) (admitted)
- [34.5.E23](https://dlmf.nist.gov/34.5.E23): [`DLMF.WignerSymbols.wigner3j_mul_wigner6j`](DLMF/WignerSymbols/SixJ.lean#L718) (admitted). Stated without triangle hypotheses; stronger than DLMF.
- [34.5.v](https://dlmf.nist.gov/34.5.v): no statement (references only).

## [§34.6 Definition: 9j Symbol](https://dlmf.nist.gov/34.6)

- [34.6.E1](https://dlmf.nist.gov/34.6.E1): [`DLMF.WignerSymbols.wigner9j_eq_sum_threeJ`](DLMF/WignerSymbols/NineJ.lean#L30) (admitted)
- [34.6.E2](https://dlmf.nist.gov/34.6.E2): [`DLMF.WignerSymbols.wigner9j`](DLMF/WignerSymbols/Basic.lean#L178) (definition)

## [§34.7 Basic Properties: 9j Symbol](https://dlmf.nist.gov/34.7)

- [34.7.ii](https://dlmf.nist.gov/34.7.ii): [`DLMF.WignerSymbols.wigner9j_transpose`](DLMF/WignerSymbols/NineJ.lean#L137) (proved); [`DLMF.WignerSymbols.wigner9j_cycle_rows`](DLMF/WignerSymbols/NineJ.lean#L157) (admitted); [`DLMF.WignerSymbols.wigner9j_cycle_columns`](DLMF/WignerSymbols/NineJ.lean#L164) (admitted); [`DLMF.WignerSymbols.wigner9j_swap_rows`](DLMF/WignerSymbols/NineJ.lean#L171) (admitted); [`DLMF.WignerSymbols.wigner9j_swap_columns`](DLMF/WignerSymbols/NineJ.lean#L179) (admitted). Invariance under the 72 permutations: generated by transposition, row and column cycles; odd row and column permutations give the sign `(-1)^R`.
- [34.7.E1](https://dlmf.nist.gov/34.7.E1): [`DLMF.WignerSymbols.wigner9j_zero`](DLMF/WignerSymbols/NineJ.lean#L53) (proved)
- [34.7.E2](https://dlmf.nist.gov/34.7.E2): [`DLMF.WignerSymbols.wigner9j_orthogonality`](DLMF/WignerSymbols/NineJ.lean#L189) (admitted)
- [34.7.E3](https://dlmf.nist.gov/34.7.E3): [`DLMF.WignerSymbols.wigner9j_sum_rule`](DLMF/WignerSymbols/NineJ.lean#L203) (admitted). Stated without triangle hypotheses; stronger than DLMF.
- [34.7.E4](https://dlmf.nist.gov/34.7.E4): [`DLMF.WignerSymbols.wigner3j_mul_wigner9j`](DLMF/WignerSymbols/NineJ.lean#L215) (admitted). Stated without triangle hypotheses; stronger than DLMF.
- [34.7.E5](https://dlmf.nist.gov/34.7.E5): [`DLMF.WignerSymbols.wigner9j_sum_wigner6j`](DLMF/WignerSymbols/NineJ.lean#L228) (admitted). Stated without triangle hypotheses; stronger than DLMF.
- [34.7.iii](https://dlmf.nist.gov/34.7.iii): no statement (references only).
- [34.7.v](https://dlmf.nist.gov/34.7.v): no statement (references only).

## [§34.8 Approximations for Large Parameters](https://dlmf.nist.gov/34.8)

- [34.8.E1](https://dlmf.nist.gov/34.8.E1): [`DLMF.WignerSymbols.wigner6j_large_parameters`](DLMF/WignerSymbols/LargeParameters.lean#L27) (admitted). Iterated limit: for `δ, ε > 0` there is `L₀` such that for `l₃ ≥ L₀` there is `K` with the relative error below `ε` whenever all `jᵣ ≥ K` (triads, `sin θ ≥ δ`).
- [34.8.E2](https://dlmf.nist.gov/34.8.E2): [`DLMF.WignerSymbols.largeParameterAngle`](DLMF/WignerSymbols/Basic.lean#L206) (definition); [`DLMF.WignerSymbols.wigner6j_large_parameters`](DLMF/WignerSymbols/LargeParameters.lean#L27) (admitted)
- [34.8](https://dlmf.nist.gov/34.8): no further statement (references only) beyond 34.8.1–34.8.2.

## [§34.9 Graphics](https://dlmf.nist.gov/34.9)

- [34.9](https://dlmf.nist.gov/34.9): excluded: graphics.

## [§34.10 Zeros](https://dlmf.nist.gov/34.10)

- [34.10](https://dlmf.nist.gov/34.10): [`DLMF.WignerSymbols.wigner6j_eq_zero_of_not`](DLMF/WignerSymbols/SixJ.lean#L731) (proved); [`DLMF.WignerSymbols.wigner3j_eq_zero_of_not_isTriad`](DLMF/WignerSymbols/ThreeJ.lean#L170) (proved); [`DLMF.WignerSymbols.wigner3j_eq_zero_of_sum_ne_zero`](DLMF/WignerSymbols/ThreeJ.lean#L177) (proved); [`DLMF.WignerSymbols.wigner3j_one_one_one_zero`](DLMF/WignerSymbols/ThreeJ.lean#L1014) (proved). The vanishing of symbols outside the triangle conditions, and the "nontrivial zero" `(1 1 1; 0 0 0) = 0`.

## [§34.11 Higher-Order 3nj Symbols](https://dlmf.nist.gov/34.11)

- [34.11](https://dlmf.nist.gov/34.11): no statement (references only).

## [§34.12 Physical Applications](https://dlmf.nist.gov/34.12)

- [34.12](https://dlmf.nist.gov/34.12): excluded: application note (no mathematical statement).

## [§34.13 Methods of Computation](https://dlmf.nist.gov/34.13)

- [34.13](https://dlmf.nist.gov/34.13): excluded: methods of computation.

## [§34.14 Tables](https://dlmf.nist.gov/34.14)

- [34.14](https://dlmf.nist.gov/34.14): excluded: tables (numerical).

## [§34.15 Software](https://dlmf.nist.gov/34.15)

- [34.15](https://dlmf.nist.gov/34.15): excluded: software.
