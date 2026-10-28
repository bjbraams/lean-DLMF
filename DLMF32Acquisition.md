# DLMF Chapter 32 acquisition: Painlevé Transcendents

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 32](https://dlmf.nist.gov/32), version 1.2.8, checked on 2026-10-26, by two
agents: part A (agent ACQ32A, helper prefix `a32_`) covers §§32.1–32.7, part B covers
§§32.8–32.17 and appends its sections below. The Lean code is in `DLMF/Painleve/` (namespace
`DLMF.Painleve`). The part A modules, in import order, are
[Defs](DLMF/Painleve/Defs.lean) (all part A definitions; imports `DLMF.Painleve.Basic`),
[Equations](DLMF/Painleve/Equations.lean) (§32.2; imports `Defs`),
[BacklundDLMF](DLMF/Painleve/BacklundDLMF.lean) (§32.7; imports `Equations` and the
Beals–Wong file `DLMF.Painleve.Backlund`),
[Hamiltonian](DLMF/Painleve/Hamiltonian.lean) (§32.6; imports `Defs`) and
[Isomonodromy](DLMF/Painleve/Isomonodromy.lean) (§§32.4–32.5; imports `Defs` and the
definitions file `DLMF.Airy.Basic`). There are no upstream pointers: Mathlib and TauCeti have
no Painlevé equations.

**Counts (part A).** §§32.2, 32.4–32.7 have 145 numbered equations (32.2: 37, 32.4: 16,
32.5: 3, 32.6: 39, 32.7: 50); §32.1 is notation only and §32.3 (6 numbered equations) is
excluded: graphics. In scope: 145. Covered: 144 by project declarations; 32.2.E8 (the Möbius
map of the Painlevé–Gambier classification) is recorded as not formalized. In addition 5 prose
IDs (32.2.i, 32.2.ii, 32.2.vi, 32.6.ii, 32.6.iii) carry tags. 149 DLMF IDs are tagged on 117
declarations. The 138 declarations of the five modules are 35 definitions (all in `Defs`),
69 proved theorems (of which 15 untagged helpers, bridge and API lemmas) and 34 direct admissions;
no proved theorem depends on an admission.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Defs](DLMF/Painleve/Defs.lean): 0 admissions; 35 definitions, 5 proved API lemmas.
- [Equations](DLMF/Painleve/Equations.lean): 13 admissions; 31 theorems: 18 proved,
  13 admitted.
- [BacklundDLMF](DLMF/Painleve/BacklundDLMF.lean): 15 admissions; 31 theorems: 16 proved,
  15 admitted.
- [Hamiltonian](DLMF/Painleve/Hamiltonian.lean): 3 admissions; 24 theorems: 21 proved,
  3 admitted.
- [Isomonodromy](DLMF/Painleve/Isomonodromy.lean): 3 admissions; 12 theorems: 9 proved,
  3 admitted.

## Domains, conventions and source corrections

- **Second-order equations.** 32.2.7 is `IsODE2SolutionOn F w U`: `w` is differentiable at
  every point of `U ⊆ ℂ` and `deriv w` has derivative `F z (w z) (deriv w z)` there, so
  totalized derivatives cannot make a nonsolution satisfy an equation. Solutions are
  meromorphic in general; the equations are stated on a set `U` where `w` is holomorphic
  (as Beals–Wong's `IsPIIOn` does). The right-hand sides are `painleveIRhs` …
  `painleveVIRhs`, `painleveIIIPrimeRhs`; the predicates are `IsPainleveIOn`,
  `IsPainleveIIOn α` and the structures `IsPainleveIIIOn α β γ δ`, `IsPainleveIVOn α β`,
  `IsPainleveVOn α β γ δ`, `IsPainleveVIOn α β γ δ`, `IsPainleveIIIPrimeOn`. Wherever DLMF
  divides (by `z`, `w`, `w - 1`, `w - z`, `z - 1`), the structure carries the nonvanishing
  hypothesis on `U`, so the Lean convention `x/0 = 0` never enters a solution.
- **DLMF ↔ Beals–Wong bridge.** The older files of the area (`Basic`, `Backlund`, `LaxPair`,
  `Tau`, …) follow Beals–Wong, whose `PII(c)` is `u'' = 2u³ + xu - c` (`IsPIIOn c`). DLMF's
  `PII` with parameter `α` (32.2.2, `w'' = 2w³ + zw + α`) is the same equation with `c = -α`:
  `isPainleveIIOn_iff_isPIIOn : IsPainleveIIOn α w U ↔ IsPIIOn (-α) w U`. DLMF statements
  for `PII` are proved in the DLMF normalization; the integral equation 32.5 is stated with
  `IsPIIOn (0 : ℝ)` (real variable, `α = 0`).
- **Branches.** Square and cube roots in DLMF formulas (`√2` in 32.2.11, `√(-2β)` in
  32.7.19–32.7.21, `2^{1/3}` in 32.7.3, `z^{1/4}`, `√w` in 32.7.49–32.7.50) are replaced by
  arbitrary roots (`r ^ 2 = 2`, `t ^ 3 = 2`, functions with `q ^ 4 = z`, `p ^ 2 = w` and the
  matching derivatives), so the statements are branch-free and cover every choice. The
  elliptic form 32.2.13–32.2.14 uses the principal square root along the ray from 0.
- **Bäcklund transformations** are stated as: if `w` solves the equation with the given
  parameters on an open `U` and the new function's denominators do not vanish, then the
  transformed function solves the equation with the transformed parameters. The `PII` maps
  32.7.2 and the recurrence 32.7.5 hold without DLMF's side conditions `α ≠ ∓1/2`.
- **Hamiltonian structure.** 32.6.1 is `IsHamiltonianSystemOn H q p U`
  (`q' = ∂H/∂p`, `p' = -∂H/∂q` with genuine derivatives); the Hamiltonians are
  `painleveHamiltonianI`, `…II`, `…III (κ₀ κ∞ θ₀ θ∞)`, `…IIIPrime (η₀ η∞ θ₀ θ∞)` and
  `…IIIGammaZero (κ₀ κ∞ θ)`. The σ-equations are proved in both directions where DLMF states
  both; the converse directions need nondegeneracy hypotheses where DLMF divides (and
  `σ'' ≠ 0` in 32.6.7–32.6.8, where `σ = 2c³ + cz` is a counterexample without it).
- **Lax pairs** (§32.4) are matrices over ℂ in the spectral parameter `λ`
  (`painleveILaxA/B`, `painleveIILaxA/B`, `painleveIIILaxM/A/B`, Pauli matrices `laxSigma1–3`);
  compatibility 32.4.3 is stated as the zero-curvature identity of the matrix entries, and its
  equivalence with the Painlevé equation is proved for `PI` and `PII`; for `PIII` the system
  32.4.10–32.4.13 implies compatibility (proved), the converse is admitted.
- **Source corrections** (all verified by sympy symbolic computation and mpmath evaluation at
  random complex points; scripts kept by the acquisition agent): 32.6.26 (`θ₁` should be
  `θ∞`); 32.6.30–32.6.31 (numerator `2ζσ''`, `p = (2σ' + η₀η∞)/(2η₀)`); 32.6.37 (stray
  factor `θ∞`); 32.6.38–32.6.39 (signs: `σ' = -2κ₀p`); 32.7.42–32.7.43 (`α = ½θ∞²`,
  `A = ½Θ∞²` in place of `½(θ∞ - 1)²`, `½(Θ∞ - 1)²`). Stronger than DLMF: 32.7.49–32.7.50 give
  the target parameters exactly. Verified as printed: 32.2.9–32.2.12, 32.2.15–32.2.23,
  32.2.25–32.2.37, the Lax pairs of §32.4 (with 32.4.14–32.4.16), the rest of §32.6 and
  32.7.1–32.7.41, 32.7.44–32.7.48.

## Numbered formulas and prose items

## [§32.1 Special Notation](https://dlmf.nist.gov/32.1)

- [32.1](https://dlmf.nist.gov/32.1): notation only; no statement.

## [§32.2 Differential Equations](https://dlmf.nist.gov/32.2)

- [32.2.i](https://dlmf.nist.gov/32.2.i): [`DLMF.Painleve.IsPainleveIOn.exists_meromorphic`](DLMF/Painleve/Equations.lean#L911) (admitted); [`DLMF.Painleve.IsPainleveIIOn.exists_meromorphic`](DLMF/Painleve/Equations.lean#L919) (admitted); [`DLMF.Painleve.IsPainleveIVOn.exists_meromorphic`](DLMF/Painleve/Equations.lean#L927) (admitted); [`DLMF.Painleve.IsPainleveIIIOn.exists_meromorphic_exp`](DLMF/Painleve/Equations.lean#L935) (admitted); [`DLMF.Painleve.IsPainleveVOn.exists_meromorphic_exp`](DLMF/Painleve/Equations.lean#L945) (admitted)
- [32.2.ii](https://dlmf.nist.gov/32.2.ii): [`DLMF.Painleve.painleveIII_renormalize_gamma_delta`](DLMF/Painleve/Equations.lean#L95) (proved); [`DLMF.Painleve.painleveIII_renormalize_alpha_delta`](DLMF/Painleve/Equations.lean#L111) (proved); [`DLMF.Painleve.painleveIII_renormalize_beta_gamma`](DLMF/Painleve/Equations.lean#L124) (proved); [`DLMF.Painleve.painleveV_renormalize_delta`](DLMF/Painleve/Equations.lean#L156) (proved); [`DLMF.Painleve.IsPainleveIIIOn.renormalize_gamma_delta`](DLMF/Painleve/Equations.lean#L168) (proved); [`DLMF.Painleve.IsPainleveIIIOn.renormalize_alpha_delta`](DLMF/Painleve/Equations.lean#L179) (proved); [`DLMF.Painleve.IsPainleveIIIOn.renormalize_beta_gamma`](DLMF/Painleve/Equations.lean#L190) (proved); [`DLMF.Painleve.IsPainleveVOn.renormalize_delta`](DLMF/Painleve/Equations.lean#L201) (proved)
- [32.2.vi](https://dlmf.nist.gov/32.2.vi): [`DLMF.Painleve.painleveII_coalescence_I_tendsto`](DLMF/Painleve/Equations.lean#L679) (proved)
- [32.2.E1](https://dlmf.nist.gov/32.2.E1): [`DLMF.Painleve.painleveIRhs`](DLMF/Painleve/Defs.lean#L102) (definition); [`DLMF.Painleve.IsPainleveIOn`](DLMF/Painleve/Defs.lean#L139) (definition)
- [32.2.E2](https://dlmf.nist.gov/32.2.E2): [`DLMF.Painleve.painleveIIRhs`](DLMF/Painleve/Defs.lean#L106) (definition); [`DLMF.Painleve.IsPainleveIIOn`](DLMF/Painleve/Defs.lean#L144) (definition)
- [32.2.E3](https://dlmf.nist.gov/32.2.E3): [`DLMF.Painleve.painleveIIIRhs`](DLMF/Painleve/Defs.lean#L110) (definition); [`DLMF.Painleve.IsPainleveIIIOn`](DLMF/Painleve/Defs.lean#L150) (definition)
- [32.2.E4](https://dlmf.nist.gov/32.2.E4): [`DLMF.Painleve.painleveIVRhs`](DLMF/Painleve/Defs.lean#L116) (definition); [`DLMF.Painleve.IsPainleveIVOn`](DLMF/Painleve/Defs.lean#L158) (definition)
- [32.2.E5](https://dlmf.nist.gov/32.2.E5): [`DLMF.Painleve.painleveVRhs`](DLMF/Painleve/Defs.lean#L122) (definition); [`DLMF.Painleve.IsPainleveVOn`](DLMF/Painleve/Defs.lean#L164) (definition)
- [32.2.E6](https://dlmf.nist.gov/32.2.E6): [`DLMF.Painleve.painleveVIRhs`](DLMF/Painleve/Defs.lean#L130) (definition); [`DLMF.Painleve.IsPainleveVIOn`](DLMF/Painleve/Defs.lean#L173) (definition)
- [32.2.E7](https://dlmf.nist.gov/32.2.E7): [`DLMF.Painleve.IsODE2SolutionOn`](DLMF/Painleve/Defs.lean#L57) (definition)
- [32.2.E8](https://dlmf.nist.gov/32.2.E8): not formalized. The Möbius transformation of the classification of the fifty equations with the Painlevé property (Painlevé–Gambier); the classification theorem is not acquired (see "Prose, informal and excluded items").
- [32.2.E9](https://dlmf.nist.gov/32.2.E9): [`DLMF.Painleve.painleveIIIPrimeRhs`](DLMF/Painleve/Defs.lean#L184) (definition); [`DLMF.Painleve.IsPainleveIIIPrimeOn`](DLMF/Painleve/Defs.lean#L190) (definition); [`DLMF.Painleve.IsPainleveIIIPrimeOn.isPainleveIIIOn`](DLMF/Painleve/Equations.lean#L213) (proved)
- [32.2.E10](https://dlmf.nist.gov/32.2.E10): [`DLMF.Painleve.isPainleveIIIOn_exp_of_sineGordon`](DLMF/Painleve/Equations.lean#L248) (proved)
- [32.2.E11](https://dlmf.nist.gov/32.2.E11): [`DLMF.Painleve.isPainleveIVOn_of_quintic`](DLMF/Painleve/Equations.lean#L279) (proved). Any `r` with `r² = 2` (both signs).
- [32.2.E12](https://dlmf.nist.gov/32.2.E12): [`DLMF.Painleve.isPainleveVOn_coth_sq`](DLMF/Painleve/Equations.lean#L316) (proved)
- [32.2.E13](https://dlmf.nist.gov/32.2.E13): [`DLMF.Painleve.IsPainleveVIOn.ellipticForm`](DLMF/Painleve/Equations.lean#L504) (admitted). Branch convention: ray path from 0 and the principal square root in the elliptic integral.
- [32.2.E14](https://dlmf.nist.gov/32.2.E14): [`DLMF.Painleve.IsPainleveVIOn.ellipticForm`](DLMF/Painleve/Equations.lean#L504) (admitted)
- [32.2.E15](https://dlmf.nist.gov/32.2.E15): [`DLMF.Painleve.isPainleveIVOn_of_symmetric`](DLMF/Painleve/Equations.lean#L530) (proved)
- [32.2.E16](https://dlmf.nist.gov/32.2.E16): [`DLMF.Painleve.isPainleveIVOn_of_symmetric`](DLMF/Painleve/Equations.lean#L530) (proved)
- [32.2.E17](https://dlmf.nist.gov/32.2.E17): [`DLMF.Painleve.isPainleveIVOn_of_symmetric`](DLMF/Painleve/Equations.lean#L530) (proved)
- [32.2.E18](https://dlmf.nist.gov/32.2.E18): [`DLMF.Painleve.isPainleveIVOn_of_symmetric`](DLMF/Painleve/Equations.lean#L530) (proved)
- [32.2.E19](https://dlmf.nist.gov/32.2.E19): [`DLMF.Painleve.isPainleveVOn_of_symmetric`](DLMF/Painleve/Equations.lean#L559) (proved)
- [32.2.E20](https://dlmf.nist.gov/32.2.E20): [`DLMF.Painleve.isPainleveVOn_of_symmetric`](DLMF/Painleve/Equations.lean#L559) (proved)
- [32.2.E21](https://dlmf.nist.gov/32.2.E21): [`DLMF.Painleve.isPainleveVOn_of_symmetric`](DLMF/Painleve/Equations.lean#L559) (proved)
- [32.2.E22](https://dlmf.nist.gov/32.2.E22): [`DLMF.Painleve.isPainleveVOn_of_symmetric`](DLMF/Painleve/Equations.lean#L559) (proved)
- [32.2.E23](https://dlmf.nist.gov/32.2.E23): [`DLMF.Painleve.isPainleveVOn_of_symmetric`](DLMF/Painleve/Equations.lean#L559) (proved)
- [32.2.E24](https://dlmf.nist.gov/32.2.E24): [`DLMF.Painleve.painleveIII_coalescence_II_tendsto`](DLMF/Painleve/Equations.lean#L705) (proved); [`DLMF.Painleve.painleveIV_coalescence_II_tendsto`](DLMF/Painleve/Equations.lean#L733) (proved); [`DLMF.Painleve.painleveV_coalescence_III_tendsto`](DLMF/Painleve/Equations.lean#L776) (proved); [`DLMF.Painleve.painleveV_coalescence_IV_tendsto`](DLMF/Painleve/Equations.lean#L808) (proved); [`DLMF.Painleve.painleveVI_coalescence_V_tendsto`](DLMF/Painleve/Equations.lean#L855) (proved). The limit statements of the cascade are stated per coalescence (32.2.28–32.2.37).
- [32.2.E25](https://dlmf.nist.gov/32.2.E25): [`DLMF.Painleve.IsPainleveIIOn.coalescence_I`](DLMF/Painleve/Equations.lean#L658) (proved)
- [32.2.E26](https://dlmf.nist.gov/32.2.E26): [`DLMF.Painleve.IsPainleveIIOn.coalescence_I`](DLMF/Painleve/Equations.lean#L658) (proved)
- [32.2.E27](https://dlmf.nist.gov/32.2.E27): [`DLMF.Painleve.IsPainleveIIOn.coalescence_I`](DLMF/Painleve/Equations.lean#L658) (proved)
- [32.2.E28](https://dlmf.nist.gov/32.2.E28): [`DLMF.Painleve.painleveIII_coalescence_II_tendsto`](DLMF/Painleve/Equations.lean#L705) (proved)
- [32.2.E29](https://dlmf.nist.gov/32.2.E29): [`DLMF.Painleve.painleveIII_coalescence_II_tendsto`](DLMF/Painleve/Equations.lean#L705) (proved)
- [32.2.E30](https://dlmf.nist.gov/32.2.E30): [`DLMF.Painleve.painleveIV_coalescence_II_tendsto`](DLMF/Painleve/Equations.lean#L733) (proved)
- [32.2.E31](https://dlmf.nist.gov/32.2.E31): [`DLMF.Painleve.painleveIV_coalescence_II_tendsto`](DLMF/Painleve/Equations.lean#L733) (proved)
- [32.2.E32](https://dlmf.nist.gov/32.2.E32): [`DLMF.Painleve.painleveV_coalescence_III_tendsto`](DLMF/Painleve/Equations.lean#L776) (proved)
- [32.2.E33](https://dlmf.nist.gov/32.2.E33): [`DLMF.Painleve.painleveV_coalescence_III_tendsto`](DLMF/Painleve/Equations.lean#L776) (proved)
- [32.2.E34](https://dlmf.nist.gov/32.2.E34): [`DLMF.Painleve.painleveV_coalescence_IV_tendsto`](DLMF/Painleve/Equations.lean#L808) (proved)
- [32.2.E35](https://dlmf.nist.gov/32.2.E35): [`DLMF.Painleve.painleveV_coalescence_IV_tendsto`](DLMF/Painleve/Equations.lean#L808) (proved)
- [32.2.E36](https://dlmf.nist.gov/32.2.E36): [`DLMF.Painleve.painleveVI_coalescence_V_tendsto`](DLMF/Painleve/Equations.lean#L855) (proved)
- [32.2.E37](https://dlmf.nist.gov/32.2.E37): [`DLMF.Painleve.painleveVI_coalescence_V_tendsto`](DLMF/Painleve/Equations.lean#L855) (proved)

## [§32.4 Isomonodromy Problems](https://dlmf.nist.gov/32.4)

- [32.4.E1](https://dlmf.nist.gov/32.4.E1): [`DLMF.Painleve.lax_mixed_derivatives`](DLMF/Painleve/Isomonodromy.lean#L31) (proved)
- [32.4.E2](https://dlmf.nist.gov/32.4.E2): [`DLMF.Painleve.lax_mixed_derivatives`](DLMF/Painleve/Isomonodromy.lean#L31) (proved); [`DLMF.Painleve.lax_mixed_derivatives_eq`](DLMF/Painleve/Isomonodromy.lean#L41) (proved)
- [32.4.E3](https://dlmf.nist.gov/32.4.E3): [`DLMF.Painleve.lax_mixed_derivatives`](DLMF/Painleve/Isomonodromy.lean#L31) (proved); [`DLMF.Painleve.lax_mixed_derivatives_eq`](DLMF/Painleve/Isomonodromy.lean#L41) (proved)
- [32.4.E4](https://dlmf.nist.gov/32.4.E4): [`DLMF.Painleve.painleveILaxA`](DLMF/Painleve/Defs.lean#L263) (definition); [`DLMF.Painleve.painleveI_lax_compatibility_iff`](DLMF/Painleve/Isomonodromy.lean#L71) (proved)
- [32.4.E5](https://dlmf.nist.gov/32.4.E5): [`DLMF.Painleve.painleveILaxB`](DLMF/Painleve/Defs.lean#L272) (definition); [`DLMF.Painleve.painleveI_lax_compatibility_iff`](DLMF/Painleve/Isomonodromy.lean#L71) (proved)
- [32.4.E6](https://dlmf.nist.gov/32.4.E6): [`DLMF.Painleve.painleveIILaxA`](DLMF/Painleve/Defs.lean#L277) (definition); [`DLMF.Painleve.painleveII_lax_compatibility_iff`](DLMF/Painleve/Isomonodromy.lean#L112) (proved)
- [32.4.E7](https://dlmf.nist.gov/32.4.E7): [`DLMF.Painleve.painleveIILaxB`](DLMF/Painleve/Defs.lean#L284) (definition); [`DLMF.Painleve.painleveII_lax_compatibility_iff`](DLMF/Painleve/Isomonodromy.lean#L112) (proved)
- [32.4.E8](https://dlmf.nist.gov/32.4.E8): [`DLMF.Painleve.painleveIIILaxA`](DLMF/Painleve/Defs.lean#L294) (definition); [`DLMF.Painleve.painleveIII_lax_compatibility`](DLMF/Painleve/Isomonodromy.lean#L132) (proved)
- [32.4.E9](https://dlmf.nist.gov/32.4.E9): [`DLMF.Painleve.painleveIIILaxB`](DLMF/Painleve/Defs.lean#L301) (definition); [`DLMF.Painleve.painleveIII_lax_compatibility`](DLMF/Painleve/Isomonodromy.lean#L132) (proved)
- [32.4.E10](https://dlmf.nist.gov/32.4.E10): [`DLMF.Painleve.painleveIII_lax_compatibility`](DLMF/Painleve/Isomonodromy.lean#L132) (proved); [`DLMF.Painleve.painleveIII_lax_system_of_compatibility`](DLMF/Painleve/Isomonodromy.lean#L154) (proved)
- [32.4.E11](https://dlmf.nist.gov/32.4.E11): [`DLMF.Painleve.painleveIII_lax_compatibility`](DLMF/Painleve/Isomonodromy.lean#L132) (proved); [`DLMF.Painleve.painleveIII_lax_system_of_compatibility`](DLMF/Painleve/Isomonodromy.lean#L154) (proved)
- [32.4.E12](https://dlmf.nist.gov/32.4.E12): [`DLMF.Painleve.painleveIII_lax_compatibility`](DLMF/Painleve/Isomonodromy.lean#L132) (proved); [`DLMF.Painleve.painleveIII_lax_system_of_compatibility`](DLMF/Painleve/Isomonodromy.lean#L154) (proved)
- [32.4.E13](https://dlmf.nist.gov/32.4.E13): [`DLMF.Painleve.painleveIII_lax_compatibility`](DLMF/Painleve/Isomonodromy.lean#L132) (proved); [`DLMF.Painleve.painleveIII_lax_system_of_compatibility`](DLMF/Painleve/Isomonodromy.lean#L154) (proved)
- [32.4.E14](https://dlmf.nist.gov/32.4.E14): [`DLMF.Painleve.painleveIII_lax_riccati`](DLMF/Painleve/Isomonodromy.lean#L194) (proved)
- [32.4.E15](https://dlmf.nist.gov/32.4.E15): [`DLMF.Painleve.painleveIII_lax_isPainleveIIIOn`](DLMF/Painleve/Isomonodromy.lean#L240) (proved)
- [32.4.E16](https://dlmf.nist.gov/32.4.E16): [`DLMF.Painleve.painleveIII_lax_firstIntegral`](DLMF/Painleve/Isomonodromy.lean#L214) (proved); [`DLMF.Painleve.painleveIII_lax_isPainleveIIIOn`](DLMF/Painleve/Isomonodromy.lean#L240) (proved). The first integral is proved; the derivation of `PIII` (32.4.15) is admitted.

## [§32.5 Integral Equations](https://dlmf.nist.gov/32.5)

- [32.5.E1](https://dlmf.nist.gov/32.5.E1): [`DLMF.Painleve.painleveII_integralEquation`](DLMF/Painleve/Isomonodromy.lean#L287) (admitted). Real form (`IsPIIOn (0 : ℝ)`); **added hypotheses** `|k| ≤ 1` (for `|k| > 1` the solution has real poles) and continuity of `K`.
- [32.5.E2](https://dlmf.nist.gov/32.5.E2): [`DLMF.Painleve.painleveII_integralEquation`](DLMF/Painleve/Isomonodromy.lean#L287) (admitted)
- [32.5.E3](https://dlmf.nist.gov/32.5.E3): [`DLMF.Painleve.painleveII_integralEquation`](DLMF/Painleve/Isomonodromy.lean#L287) (admitted)

## [§32.6 Hamiltonian Structure](https://dlmf.nist.gov/32.6)

- [32.6.ii](https://dlmf.nist.gov/32.6.ii): [`DLMF.Painleve.IsHamiltonianSystemOn.isPainleveIOn`](DLMF/Painleve/Hamiltonian.lean#L93) (proved)
- [32.6.iii](https://dlmf.nist.gov/32.6.iii): [`DLMF.Painleve.IsHamiltonianSystemOn.isPainleveIIOn`](DLMF/Painleve/Hamiltonian.lean#L173) (proved)
- [32.6.E1](https://dlmf.nist.gov/32.6.E1): [`DLMF.Painleve.IsHamiltonianSystemOn`](DLMF/Painleve/Defs.lean#L200) (definition)
- [32.6.E2](https://dlmf.nist.gov/32.6.E2): [`DLMF.Painleve.painleveHamiltonianI`](DLMF/Painleve/Defs.lean#L208) (definition)
- [32.6.E3](https://dlmf.nist.gov/32.6.E3): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianI_iff`](DLMF/Painleve/Hamiltonian.lean#L76) (proved)
- [32.6.E4](https://dlmf.nist.gov/32.6.E4): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianI_iff`](DLMF/Painleve/Hamiltonian.lean#L76) (proved)
- [32.6.E5](https://dlmf.nist.gov/32.6.E5): [`DLMF.Painleve.IsHamiltonianSystemOn.sigma_painleveI`](DLMF/Painleve/Hamiltonian.lean#L103) (proved)
- [32.6.E6](https://dlmf.nist.gov/32.6.E6): [`DLMF.Painleve.IsHamiltonianSystemOn.sigma_painleveI`](DLMF/Painleve/Hamiltonian.lean#L103) (proved)
- [32.6.E7](https://dlmf.nist.gov/32.6.E7): [`DLMF.Painleve.painleveI_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L122) (proved). **Added hypothesis** `σ'' ≠ 0`: `σ = 2c³ + cz` solves 32.6.6 but gives no solution of 32.6.3–32.6.4.
- [32.6.E8](https://dlmf.nist.gov/32.6.E8): [`DLMF.Painleve.painleveI_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L122) (proved)
- [32.6.E9](https://dlmf.nist.gov/32.6.E9): [`DLMF.Painleve.painleveHamiltonianII`](DLMF/Painleve/Defs.lean#L212) (definition)
- [32.6.E10](https://dlmf.nist.gov/32.6.E10): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianII_iff`](DLMF/Painleve/Hamiltonian.lean#L150) (proved)
- [32.6.E11](https://dlmf.nist.gov/32.6.E11): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianII_iff`](DLMF/Painleve/Hamiltonian.lean#L150) (proved)
- [32.6.E12](https://dlmf.nist.gov/32.6.E12): [`DLMF.Painleve.IsHamiltonianSystemOn.momentum_painleveII`](DLMF/Painleve/Hamiltonian.lean#L187) (proved)
- [32.6.E13](https://dlmf.nist.gov/32.6.E13): [`DLMF.Painleve.IsHamiltonianSystemOn.sigma_painleveII`](DLMF/Painleve/Hamiltonian.lean#L203) (proved)
- [32.6.E14](https://dlmf.nist.gov/32.6.E14): [`DLMF.Painleve.painleveII_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L223) (proved). **Added hypotheses** `σ' ≠ 0`, `σ'' ≠ 0` (DLMF divides by them).
- [32.6.E15](https://dlmf.nist.gov/32.6.E15): [`DLMF.Painleve.painleveII_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L223) (proved)
- [32.6.E16](https://dlmf.nist.gov/32.6.E16): [`DLMF.Painleve.painleveHamiltonianIII`](DLMF/Painleve/Defs.lean#L218) (definition)
- [32.6.E17](https://dlmf.nist.gov/32.6.E17): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianIII_iff`](DLMF/Painleve/Hamiltonian.lean#L265) (proved)
- [32.6.E18](https://dlmf.nist.gov/32.6.E18): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianIII_iff`](DLMF/Painleve/Hamiltonian.lean#L265) (proved)
- [32.6.E19](https://dlmf.nist.gov/32.6.E19): [`DLMF.Painleve.IsHamiltonianSystemOn.isPainleveIIIOn`](DLMF/Painleve/Hamiltonian.lean#L298) (proved)
- [32.6.E20](https://dlmf.nist.gov/32.6.E20): [`DLMF.Painleve.IsHamiltonianSystemOn.sigma_painleveIII`](DLMF/Painleve/Hamiltonian.lean#L328) (proved)
- [32.6.E21](https://dlmf.nist.gov/32.6.E21): [`DLMF.Painleve.IsHamiltonianSystemOn.sigma_painleveIII`](DLMF/Painleve/Hamiltonian.lean#L328) (proved)
- [32.6.E22](https://dlmf.nist.gov/32.6.E22): [`DLMF.Painleve.painleveIII_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L376) (proved). Nondegeneracy hypotheses added where DLMF divides.
- [32.6.E23](https://dlmf.nist.gov/32.6.E23): [`DLMF.Painleve.painleveIII_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L376) (proved)
- [32.6.E24](https://dlmf.nist.gov/32.6.E24): [`DLMF.Painleve.painleveHamiltonianIIIPrime`](DLMF/Painleve/Defs.lean#L226) (definition)
- [32.6.E25](https://dlmf.nist.gov/32.6.E25): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianIIIPrime_iff`](DLMF/Painleve/Hamiltonian.lean#L450) (proved)
- [32.6.E26](https://dlmf.nist.gov/32.6.E26): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianIIIPrime_iff`](DLMF/Painleve/Hamiltonian.lean#L450) (proved). **Corrected** (DLMF erratum): the printed `θ₁` must be `θ∞` (symbolic check of the Hamiltonian equations from 32.6.24).
- [32.6.E27](https://dlmf.nist.gov/32.6.E27): [`DLMF.Painleve.IsHamiltonianSystemOn.isPainleveIIIPrimeOn`](DLMF/Painleve/Hamiltonian.lean#L482) (proved)
- [32.6.E28](https://dlmf.nist.gov/32.6.E28): [`DLMF.Painleve.IsHamiltonianSystemOn.sigma_painleveIIIPrime`](DLMF/Painleve/Hamiltonian.lean#L513) (proved)
- [32.6.E29](https://dlmf.nist.gov/32.6.E29): [`DLMF.Painleve.IsHamiltonianSystemOn.sigma_painleveIIIPrime`](DLMF/Painleve/Hamiltonian.lean#L513) (proved)
- [32.6.E30](https://dlmf.nist.gov/32.6.E30): [`DLMF.Painleve.painleveIIIPrime_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L558) (proved). **Corrected** (DLMF erratum): the numerator is `2ζσ''` (printed `ζσ''`); sympy check against 32.6.25–32.6.29.
- [32.6.E31](https://dlmf.nist.gov/32.6.E31): [`DLMF.Painleve.painleveIIIPrime_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L558) (proved). **Corrected** (DLMF erratum): `p = (2σ' + η₀η∞)/(2η₀)` (printed `η₀η∞ζ`); sympy check. Nondegeneracy hypotheses added.
- [32.6.E32](https://dlmf.nist.gov/32.6.E32): [`DLMF.Painleve.painleveHamiltonianIIIGammaZero`](DLMF/Painleve/Defs.lean#L233) (definition)
- [32.6.E33](https://dlmf.nist.gov/32.6.E33): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianIIIGammaZero_iff`](DLMF/Painleve/Hamiltonian.lean#L625) (proved)
- [32.6.E34](https://dlmf.nist.gov/32.6.E34): [`DLMF.Painleve.isHamiltonianSystemOn_painleveHamiltonianIIIGammaZero_iff`](DLMF/Painleve/Hamiltonian.lean#L625) (proved)
- [32.6.E35](https://dlmf.nist.gov/32.6.E35): [`DLMF.Painleve.IsHamiltonianSystemOn.isPainleveIIIOn_gammaZero`](DLMF/Painleve/Hamiltonian.lean#L651) (proved)
- [32.6.E36](https://dlmf.nist.gov/32.6.E36): [`DLMF.Painleve.IsHamiltonianSystemOn.sigma_painleveIII_gammaZero`](DLMF/Painleve/Hamiltonian.lean#L681) (proved)
- [32.6.E37](https://dlmf.nist.gov/32.6.E37): [`DLMF.Painleve.IsHamiltonianSystemOn.sigma_painleveIII_gammaZero`](DLMF/Painleve/Hamiltonian.lean#L681) (proved). **Corrected** (DLMF erratum): the term `-4κ₀κ∞(θ+1)θ∞zσ'` has a stray `θ∞`; the correct term is `-4κ₀κ∞(θ+1)zσ'` (with the printed form the residual is `8κ₀²κ∞pz(θ+1)(θ∞-1)`).
- [32.6.E38](https://dlmf.nist.gov/32.6.E38): [`DLMF.Painleve.painleveIIIGammaZero_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L724) (proved). **Corrected** (DLMF erratum): from 32.6.36, `σ' = -2κ₀p`, so `p = -σ'/(2κ₀)`; the printed signs fail.
- [32.6.E39](https://dlmf.nist.gov/32.6.E39): [`DLMF.Painleve.painleveIIIGammaZero_of_sigma`](DLMF/Painleve/Hamiltonian.lean#L724) (proved). **Corrected** (DLMF erratum): `q = κ₀(zσ'' + θσ' + 2κ₀κ∞z)/σ'²` (sign errors in the print). Nondegeneracy hypotheses added (`κ₀ ≠ 0`, `z ≠ 0`, `σ' ≠ 0`, `zσ'' - σ' ≠ 0`).

## [§32.7 Bäcklund Transformations](https://dlmf.nist.gov/32.7)

- [32.7.E1](https://dlmf.nist.gov/32.7.E1): [`DLMF.Painleve.IsPainleveIIOn.neg`](DLMF/Painleve/BacklundDLMF.lean#L30) (proved)
- [32.7.E2](https://dlmf.nist.gov/32.7.E2): [`DLMF.Painleve.painleveIITPlus`](DLMF/Painleve/Defs.lean#L241) (definition); [`DLMF.Painleve.painleveIITMinus`](DLMF/Painleve/Defs.lean#L247) (definition); [`DLMF.Painleve.IsPainleveIIOn.tPlus`](DLMF/Painleve/BacklundDLMF.lean#L37) (proved); [`DLMF.Painleve.IsPainleveIIOn.tMinus`](DLMF/Painleve/BacklundDLMF.lean#L57) (proved). Proved without the side conditions `α ≠ ∓1/2` (the transformed function solves the equation wherever the denominator is nonzero).
- [32.7.E3](https://dlmf.nist.gov/32.7.E3): [`DLMF.Painleve.IsPainleveIIOn.special`](DLMF/Painleve/BacklundDLMF.lean#L95) (proved). Any `t` with `t³ = 2`, `ε = ±1`.
- [32.7.E4](https://dlmf.nist.gov/32.7.E4): [`DLMF.Painleve.IsPainleveIIOn.special_sq`](DLMF/Painleve/BacklundDLMF.lean#L129) (proved)
- [32.7.E5](https://dlmf.nist.gov/32.7.E5): [`DLMF.Painleve.painleveII_recurrence`](DLMF/Painleve/BacklundDLMF.lean#L151) (proved). Proved without denominator hypotheses (Lean totalization `x/0 = 0`).
- [32.7.E6](https://dlmf.nist.gov/32.7.E6): [`DLMF.Painleve.IsPainleveIIIOn.neg`](DLMF/Painleve/BacklundDLMF.lean#L176) (proved)
- [32.7.E7](https://dlmf.nist.gov/32.7.E7): [`DLMF.Painleve.IsPainleveIIIOn.inv`](DLMF/Painleve/BacklundDLMF.lean#L192) (proved)
- [32.7.E8](https://dlmf.nist.gov/32.7.E8): [`DLMF.Painleve.IsPainleveIIIOn.neg`](DLMF/Painleve/BacklundDLMF.lean#L176) (proved)
- [32.7.E9](https://dlmf.nist.gov/32.7.E9): [`DLMF.Painleve.IsPainleveIIIOn.inv`](DLMF/Painleve/BacklundDLMF.lean#L192) (proved)
- [32.7.E10](https://dlmf.nist.gov/32.7.E10): [`DLMF.Painleve.IsPainleveIIIOn.t₁`](DLMF/Painleve/BacklundDLMF.lean#L210) (proved); [`DLMF.Painleve.IsPainleveIIIOn.t₂`](DLMF/Painleve/BacklundDLMF.lean#L292) (proved); [`DLMF.Painleve.IsPainleveIIIOn.t₃`](DLMF/Painleve/BacklundDLMF.lean#L374) (proved); [`DLMF.Painleve.IsPainleveIIIOn.t₄`](DLMF/Painleve/BacklundDLMF.lean#L456) (proved)
- [32.7.E11](https://dlmf.nist.gov/32.7.E11): [`DLMF.Painleve.IsPainleveIIIOn.t₁`](DLMF/Painleve/BacklundDLMF.lean#L210) (proved)
- [32.7.E12](https://dlmf.nist.gov/32.7.E12): [`DLMF.Painleve.IsPainleveIIIOn.t₂`](DLMF/Painleve/BacklundDLMF.lean#L292) (proved)
- [32.7.E13](https://dlmf.nist.gov/32.7.E13): [`DLMF.Painleve.IsPainleveIIIOn.t₃`](DLMF/Painleve/BacklundDLMF.lean#L374) (proved)
- [32.7.E14](https://dlmf.nist.gov/32.7.E14): [`DLMF.Painleve.IsPainleveIIIOn.t₄`](DLMF/Painleve/BacklundDLMF.lean#L456) (proved)
- [32.7.E15](https://dlmf.nist.gov/32.7.E15): [`DLMF.Painleve.IsPainleveIIIOn.t₅`](DLMF/Painleve/BacklundDLMF.lean#L538) (proved); [`DLMF.Painleve.IsPainleveIIIOn.t₆`](DLMF/Painleve/BacklundDLMF.lean#L593) (proved)
- [32.7.E16](https://dlmf.nist.gov/32.7.E16): [`DLMF.Painleve.IsPainleveIIIOn.t₅`](DLMF/Painleve/BacklundDLMF.lean#L538) (proved)
- [32.7.E17](https://dlmf.nist.gov/32.7.E17): [`DLMF.Painleve.IsPainleveIIIOn.t₆`](DLMF/Painleve/BacklundDLMF.lean#L593) (proved)
- [32.7.E18](https://dlmf.nist.gov/32.7.E18): [`DLMF.Painleve.isPainleveIIIOn_sq_of_isPainleveIIIOn`](DLMF/Painleve/BacklundDLMF.lean#L648) (proved)
- [32.7.E19](https://dlmf.nist.gov/32.7.E19): [`DLMF.Painleve.IsPainleveIVOn.t₁`](DLMF/Painleve/BacklundDLMF.lean#L713) (proved); [`DLMF.Painleve.IsPainleveIVOn.t₂`](DLMF/Painleve/BacklundDLMF.lean#L773) (proved); [`DLMF.Painleve.IsPainleveIVOn.t₃`](DLMF/Painleve/BacklundDLMF.lean#L833) (proved); [`DLMF.Painleve.IsPainleveIVOn.t₄`](DLMF/Painleve/BacklundDLMF.lean#L912) (proved). Square root branch-free: any `r` with `r² = -2β`.
- [32.7.E20](https://dlmf.nist.gov/32.7.E20): [`DLMF.Painleve.IsPainleveIVOn.t₁`](DLMF/Painleve/BacklundDLMF.lean#L713) (proved)
- [32.7.E21](https://dlmf.nist.gov/32.7.E21): [`DLMF.Painleve.IsPainleveIVOn.t₂`](DLMF/Painleve/BacklundDLMF.lean#L773) (proved)
- [32.7.E22](https://dlmf.nist.gov/32.7.E22): [`DLMF.Painleve.IsPainleveIVOn.t₃`](DLMF/Painleve/BacklundDLMF.lean#L833) (proved)
- [32.7.E23](https://dlmf.nist.gov/32.7.E23): [`DLMF.Painleve.IsPainleveIVOn.t₄`](DLMF/Painleve/BacklundDLMF.lean#L912) (proved)
- [32.7.E24](https://dlmf.nist.gov/32.7.E24): [`DLMF.Painleve.IsPainleveVOn.comp_neg`](DLMF/Painleve/BacklundDLMF.lean#L992) (proved); [`DLMF.Painleve.IsPainleveVOn.inv`](DLMF/Painleve/BacklundDLMF.lean#L1013) (proved)
- [32.7.E25](https://dlmf.nist.gov/32.7.E25): [`DLMF.Painleve.IsPainleveVOn.comp_neg`](DLMF/Painleve/BacklundDLMF.lean#L992) (proved)
- [32.7.E26](https://dlmf.nist.gov/32.7.E26): [`DLMF.Painleve.IsPainleveVOn.inv`](DLMF/Painleve/BacklundDLMF.lean#L1013) (proved)
- [32.7.E27](https://dlmf.nist.gov/32.7.E27): [`DLMF.Painleve.IsPainleveVOn.t_eps`](DLMF/Painleve/BacklundDLMF.lean#L1035) (proved)
- [32.7.E28](https://dlmf.nist.gov/32.7.E28): [`DLMF.Painleve.IsPainleveVOn.t_eps`](DLMF/Painleve/BacklundDLMF.lean#L1035) (proved)
- [32.7.E29](https://dlmf.nist.gov/32.7.E29): [`DLMF.Painleve.IsPainleveVOn.t_eps`](DLMF/Painleve/BacklundDLMF.lean#L1035) (proved)
- [32.7.E30](https://dlmf.nist.gov/32.7.E30): [`DLMF.Painleve.IsPainleveIIIOn.toPainleveV`](DLMF/Painleve/BacklundDLMF.lean#L1240) (proved)
- [32.7.E31](https://dlmf.nist.gov/32.7.E31): [`DLMF.Painleve.IsPainleveIIIOn.toPainleveV`](DLMF/Painleve/BacklundDLMF.lean#L1240) (proved)
- [32.7.E32](https://dlmf.nist.gov/32.7.E32): [`DLMF.Painleve.IsPainleveIIIOn.toPainleveV`](DLMF/Painleve/BacklundDLMF.lean#L1240) (proved)
- [32.7.E33](https://dlmf.nist.gov/32.7.E33): [`DLMF.Painleve.IsPainleveVIOn.s₁`](DLMF/Painleve/BacklundDLMF.lean#L1426) (proved)
- [32.7.E34](https://dlmf.nist.gov/32.7.E34): [`DLMF.Painleve.IsPainleveVIOn.s₂`](DLMF/Painleve/BacklundDLMF.lean#L1510) (proved)
- [32.7.E35](https://dlmf.nist.gov/32.7.E35): [`DLMF.Painleve.IsPainleveVIOn.s₃`](DLMF/Painleve/BacklundDLMF.lean#L1558) (proved)
- [32.7.E36](https://dlmf.nist.gov/32.7.E36): [`DLMF.Painleve.IsPainleveVIOn.s₁`](DLMF/Painleve/BacklundDLMF.lean#L1426) (proved)
- [32.7.E37](https://dlmf.nist.gov/32.7.E37): [`DLMF.Painleve.IsPainleveVIOn.s₂`](DLMF/Painleve/BacklundDLMF.lean#L1510) (proved)
- [32.7.E38](https://dlmf.nist.gov/32.7.E38): [`DLMF.Painleve.IsPainleveVIOn.s₃`](DLMF/Painleve/BacklundDLMF.lean#L1558) (proved)
- [32.7.E39](https://dlmf.nist.gov/32.7.E39): [`DLMF.Painleve.IsPainleveVIOn.s₁`](DLMF/Painleve/BacklundDLMF.lean#L1426) (proved)
- [32.7.E40](https://dlmf.nist.gov/32.7.E40): [`DLMF.Painleve.IsPainleveVIOn.s₂`](DLMF/Painleve/BacklundDLMF.lean#L1510) (proved)
- [32.7.E41](https://dlmf.nist.gov/32.7.E41): [`DLMF.Painleve.IsPainleveVIOn.s₃`](DLMF/Painleve/BacklundDLMF.lean#L1558) (proved)
- [32.7.E42](https://dlmf.nist.gov/32.7.E42): [`DLMF.Painleve.IsPainleveVIOn.okamoto`](DLMF/Painleve/BacklundDLMF.lean#L1642) (proved). **Corrected** (DLMF erratum): DLMF prints `α = ½(θ∞ - 1)²`; with it 32.7.46 fails (residual about 0.16–0.6 at random points); `α = ½θ∞²` makes both equalities of 32.7.46 hold (residual about 1e-15).
- [32.7.E43](https://dlmf.nist.gov/32.7.E43): [`DLMF.Painleve.IsPainleveVIOn.okamoto`](DLMF/Painleve/BacklundDLMF.lean#L1642) (proved). **Corrected** (DLMF erratum): `A = ½Θ∞²` (printed `½(Θ∞ - 1)²`), as for 32.7.E42.
- [32.7.E44](https://dlmf.nist.gov/32.7.E44): [`DLMF.Painleve.IsPainleveVIOn.okamoto`](DLMF/Painleve/BacklundDLMF.lean#L1642) (proved)
- [32.7.E45](https://dlmf.nist.gov/32.7.E45): [`DLMF.Painleve.IsPainleveVIOn.okamoto`](DLMF/Painleve/BacklundDLMF.lean#L1642) (proved)
- [32.7.E46](https://dlmf.nist.gov/32.7.E46): [`DLMF.Painleve.IsPainleveVIOn.okamoto`](DLMF/Painleve/BacklundDLMF.lean#L1642) (proved)
- [32.7.E47](https://dlmf.nist.gov/32.7.E47): [`DLMF.Painleve.IsPainleveVIOn.quadratic`](DLMF/Painleve/BacklundDLMF.lean#L1862) (proved)
- [32.7.E48](https://dlmf.nist.gov/32.7.E48): [`DLMF.Painleve.IsPainleveVIOn.quartic`](DLMF/Painleve/BacklundDLMF.lean#L2076) (proved)
- [32.7.E49](https://dlmf.nist.gov/32.7.E49): [`DLMF.Painleve.IsPainleveVIOn.quartic_root`](DLMF/Painleve/BacklundDLMF.lean#L2179) (proved). **Stronger than DLMF**: the target parameters are exactly `(0, 0, γ, 1/2 - γ)`.
- [32.7.E50](https://dlmf.nist.gov/32.7.E50): [`DLMF.Painleve.IsPainleveVIOn.quartic_root`](DLMF/Painleve/BacklundDLMF.lean#L2179) (proved)
## Prose, informal and excluded items (part A)

- [32.2.i](https://dlmf.nist.gov/32.2.i): the Painlevé property is formalized as existence of
  a meromorphic continuation: for `PI`, `PII`, `PIV`, every local solution extends to a
  meromorphic function on ℂ, for `PIII` and `PV` after the substitution `z = e^ζ` (tags on
  `IsPainleveIOn.exists_meromorphic` and its siblings, admitted). The definition of the
  Painlevé property (movable branch points) in 32.2.i.p4, the classification of the fifty
  equations (32.2.i.p5, 32.2.E8) and the transcendence of the general solutions
  (32.2.i.p6) are not formalized: the classification and the irreducibility theory are
  outside the present development.
- [32.2.ii](https://dlmf.nist.gov/32.2.ii): renormalizations of `PIII` (`γ = 1, δ = -1`;
  `α = 1, δ = 0`, `β = 1, γ = 0`) and `PV` (`δ = -½`) are proved, both as scaling lemmas and
  as existence statements.
- [32.2.vi](https://dlmf.nist.gov/32.2.vi): the coalescence cascade; the `PII → PI` limit is
  proved (`painleveII_coalescence_I_tendsto`), the other limits are admitted.
- [32.3](https://dlmf.nist.gov/32.3): excluded: graphics (32.3.E1–32.3.E6 are the initial
  conditions of plotted solutions).
- [32.4.i](https://dlmf.nist.gov/32.4.i): the definition of an isomonodromy problem is prose;
  the compatibility condition is 32.4.E1–32.4.E3.
- [32.4.v](https://dlmf.nist.gov/32.4.v): no statement (references only).
- [32.6.i](https://dlmf.nist.gov/32.6.i): definition prose; formalized as 32.6.E1.
- [32.6.v](https://dlmf.nist.gov/32.6.v): no statement (references only).
- [32.7.i](https://dlmf.nist.gov/32.7.i): definition of Bäcklund transformations (prose); each
  transformation is a theorem below.
- [32.7.vii](https://dlmf.nist.gov/32.7.vii): the statement that the transformations
  32.7.33–32.7.41 generate a group of order 24 is not formalized (the individual maps are).
- [32.7.viii](https://dlmf.nist.gov/32.7.viii): affine Weyl groups; no statement (references
  only).
- Bibliographic paragraphs ("See Jimbo and Miwa (1981)", …) are not acquired.

## Validation (part A)

- The five modules build with `lake build DLMF.Painleve.<Module>` and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` without errors (`Defs`
  without admissions). There are no axioms, no `native_decide`, and no `sorry` in definitions
  or helper declarations (prefix `a32_`). No line exceeds 100 characters.
- `#print axioms` for all 68 public proved theorems (for example
  `isPainleveIIOn_iff_isPIIOn`, `IsPainleveIIOn.tPlus`, `IsPainleveIIOn.special`,
  `painleveII_recurrence`, `isPainleveIVOn_of_symmetric`, `IsPainleveIIOn.coalescence_I`,
  `IsPainleveVIOn.s₂`, `painleveII_of_sigma`, `IsHamiltonianSystemOn.sigma_painleveIIIPrime`,
  `painleveIII_lax_compatibility`) shows only `propext`, `Classical.choice` and `Quot.sound`.
- Admitted statements were checked numerically or symbolically before acquisition (sympy,
  mpmath): 32.2.12, 32.2.19–32.2.23, the coalescence limits 32.2.28–32.2.37, the `PIII`
  maps 32.7.10–32.7.14, 32.7.18, the `PIV` maps 32.7.22–32.7.23, 32.7.27–32.7.32, the `PVI`
  maps 32.7.33–32.7.50 (with the corrections above), and the σ-equation converses of §32.6.
- DLMF.lean, the umbrella `DLMF/Painleve.lean`, the lakefile and the other ledgers are
  unchanged.


## Part B: §§32.8–32.17 (agent ACQ32B, 2026-10-26)

This part covers [§32.8](https://dlmf.nist.gov/32.8)–[§32.17](https://dlmf.nist.gov/32.17),
DLMF version 1.2.8. The Lean code is in `DLMF/Painleve/` (namespace `DLMF.Painleve`, helper
prefix `b32_`); the modules, in import order, are
[SolutionsDefs](DLMF/Painleve/SolutionsDefs.lean) (all part-B definitions; imports
`DLMF.Painleve.Defs`),
[RationalDLMF](DLMF/Painleve/RationalDLMF.lean) (§32.8; imports `SolutionsDefs` and the
Beals–Wong file `DLMF.Painleve.Rational`),
[ElementarySolutions](DLMF/Painleve/ElementarySolutions.lean) (§32.9),
[SpecialSolutions](DLMF/Painleve/SpecialSolutions.lean) (§32.10; imports `RationalDLMF`,
`DLMF.Painleve.Airy`, `DLMF.Bessel.Basic`, `DLMF.Confluent.ParabolicCylinder`,
`DLMF.Confluent.Whittaker`, `DLMF.ErrorFunctions.Basic`, `DLMF.OrthogonalPolynomials.Differential`
and Mathlib's `OrdinaryHypergeometric`),
[RealAsymptotics](DLMF/Painleve/RealAsymptotics.lean) (§32.11; imports `DLMF.Airy.Framework`,
`DLMF.Confluent.ParabolicCylinder`),
[Reductions](DLMF/Painleve/Reductions.lean) (§32.13) and
[Combinatorics](DLMF/Painleve/Combinatorics.lean) (§§32.14–32.15; imports `DLMF.Airy.Framework`).
Cross-area imports are of definitions/basic files except `DLMF.Painleve.Airy`,
`DLMF.Painleve.Rational` (same area), `DLMF.Confluent.Whittaker`,
`DLMF.ErrorFunctions.Basic` and `DLMF.OrthogonalPolynomials.Differential` (theorem files of
other areas, for `whittakerM/W`, `hasDerivAt_erf_complex` and
`hermitePolyH_differential_equation`). There are no upstream pointers: Mathlib has no
Painlevé transcendents; `₂F₁` is Mathlib's `ordinaryHypergeometric`.

**Counts.** §§32.8–32.11 and §§32.13–32.15 have 135 numbered equations (32.8: 33, 32.9: 13,
32.10: 34, 32.11: 38, 32.13: 10, 32.14: 4, 32.15: 3). In scope: 135. Covered: 133 by
project declarations; 32.10.1 is excluded (informal) and 32.10.24 is not formalized (informal
"iff" classification). In addition 12 prose IDs carry tags (32.8.ii, 32.8.v, 32.9.i, 32.9.ii,
32.11.i, 32.11.ii, 32.11.v, 32.13.i, 32.13.ii, 32.13.iii, 32.14, 32.15); 145 DLMF IDs are
tagged on 117 declarations. The 145 declarations of part B are 22 definitions (all in
`SolutionsDefs`, 14 tagged), 73 proved theorems (53 tagged, 20 untagged helpers),
1 tagged theorem proved from an admission (`rationalPainleveII_isPainleveIIOn_int`) and
49 direct admissions. Excluded: §32.12 (no statement: references only), §32.16 (excluded:
application; its three paragraphs, on statistical physics and spin models, integrable
dynamical systems, the Ising model, 2D quantum gravity and string theory, contain no
mathematical statement beyond references), §32.17 (excluded: computation), and the bounds
`-0.451428 < k₁ < -0.451427`, `1.851853 < k₂ < 1.851855` of §32.11(i) (excluded: numerical).
Not formalized (informal or prose without a precise statement): "expressible in terms of
special functions" in 32.10.1 and the "iff" directions of 32.10.2, 32.10.11, 32.10.15–16,
32.10.23–24, 32.10.28; the transcendence of Picard's solution (§32.10(vi), last sentence);
§32.9(i) "similar results when `δ = 0`"; the GUE interpretation of `F(s)` (§32.14, second
paragraph); the Weierstrass case `A = 0` of §32.13(iii).

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [SolutionsDefs](DLMF/Painleve/SolutionsDefs.lean): 0 admissions; 22 definitions.
- [RationalDLMF](DLMF/Painleve/RationalDLMF.lean): 11 admissions; 50 theorems: 39 proved
  (26 tagged, of which 1 from an admission; 13 helpers), 11 admitted.
- [ElementarySolutions](DLMF/Painleve/ElementarySolutions.lean): 4 admissions; 16 theorems:
  12 proved (10 tagged), 4 admitted.
- [SpecialSolutions](DLMF/Painleve/SpecialSolutions.lean): 6 admissions; 26 theorems:
  20 proved (15 tagged), 6 admitted.
- [RealAsymptotics](DLMF/Painleve/RealAsymptotics.lean): 20 admissions; 20 theorems, all
  admitted.
- [Reductions](DLMF/Painleve/Reductions.lean): 5 admissions; 8 theorems: 3 proved, 5 admitted.
- [Combinatorics](DLMF/Painleve/Combinatorics.lean): 3 admissions; 3 theorems, all admitted.

### Domains, conventions and source corrections (part B)

- DLMF normalization of `DLMF.Painleve.Defs`; `PII` solutions bridge to Beals–Wong's
  `IsPIIOn c` with `c = -α` (`isPainleveIIOn_iff_isPIIOn` in `DLMF.Painleve.Equations`; a
  duplicate written in part B was removed at integration). Complex solutions are stated on arbitrary
  open sets avoiding the singular points of the equation; branches are principal (slit plane).
- Rational solutions (§32.8): `yablonskiiVorobievQ` (32.8.6) is defined by the recurrence
  with polynomial division; exactness and monicity are the admitted
  `yablonskiiVorobievQ_recurrence`, while `Q₂`–`Q₆` (32.8.7) are proved by computation.
  `rationalPainleveII n` (32.8.5) is ℤ-indexed. `IsRationalOn`, `IsAlgebraicOn` (ℂ[X][X])
  express "rational/algebraic solution"; the classification "iff" theorems are admitted.
- Real-variable results (§32.11) use `IsRealODE2SolutionOn` with `realPainleveIRhs`,
  `realPainleveIIRhs`, `modifiedPainleveIIRhs`, `realPainleveIIIRhs`, `realPainleveIVRhs`,
  `Asymptotics.IsEquivalent`, `IsLittleO`, `IsBigO`; `ph` is `Complex.arg`, `Ai` is
  `airyAiReal`, `U` is `(pcfU a x).re`. The pairs `(d, θ₀)`, `(d, χ)` are fixed by `d > 0`
  (needed for the connection formulas 32.11.9, 32.11.17, 32.11.21 to be well defined).
  32.11.6–9 and 32.11.10 are stated with the solution global on ℝ (stronger than DLMF).
  `painleveIII_connection` assumes `ν > -1/2`; the `PIV` statements assume `Γ(ν + 1) > 0`
  so that `h* > 0`.
- PDE reductions (§32.13) use `IsMKdVOn`, `IsKdVOn`, `IsSineGordonOn`, `IsBoussinesqOn`
  (functions of `(x, t) ∈ ℂ²`, iterated derivatives of sections).
- §32.14: `longestIncreasingLength`, probability as a count over `Equiv.Perm (Fin N)` divided
  by `N!`, `tracyWidomF` (a Bochner integral over `(s, ∞)`). §32.15: `freudMoment`,
  `freudHankel` and `freudRecurrenceSq` (`u_n = D_{n-1}D_{n+1}/D_n²`, `u_0 = 0`).
- **32.10.29 (erratum).** DLMF introduces the Riccati equation of `PVI` with "If `n = 1`"; it is
  the case `n = 0` of 32.10.28 (`a + b + c + d = 1`). sympy: the Riccati equation implies
  `PVI` exactly when `(1 - a - b - c)² = 1 - 2δ`; with `a + b + c + d = 3` the residual is
  nonzero.
- **§32.9(ii) (clarification).** "`w = C exp(±√(-2δ) z)`" solves `PV` (α = β = 0) only with
  the sign of `γ` (`w = Ce^{γz}`, `γ² = -2δ`); the other sign leaves the residual
  `-2Cγe^{-γz}/z` (sympy).
- **§32.9(i) (clarification).** The "similar result" for `α = γ = 0` is the first integral
  `z²w'² - 2zww' + 2βzw + δz² = Cw²` (verified symbolically and proved).
- **32.10.20.** For `m = 1` the formula gives `w ≡ 0`, which is not a solution of `PIV` (the
  equation divides by `w`); the statement keeps `m ≥ 1` on the set where `H_{m-1}' ≠ 0`.
- **§32.11 sign convention.** With `d < 0` the parity rule `sign k = (-1)ⁿ` of 32.11.17 and the
  sign `σ` of 32.11.21 would flip, so `d > 0` is implicit (DLMF states it only in 32.11.34).
- Verification. sympy: 32.8.1–7, 32.8.9 (`n ≤ 5`, `τ_n = Q_n/c_n`), 32.8.11–13, 16–18,
  24–26, 28–32, 32.9.1–3, 6–8, 12–13, the Riccati-to-Painlevé implications of §32.10,
  32.10.6–8 (`n ≤ 3`), 32.13.2 and 32.13.4. mpmath: 32.10.13, 18, 20–22, 26, 30 (residuals
  about `10⁻³⁰`), 32.15.3 and the `PIV` claim of §32.15 (`n ≤ 3`, residuals below `10⁻³⁹`).
  scipy ODE integration: 32.11.8–9, 32.11.15–17, 32.11.19–24 and 32.11.25–28.

### Numbered formulas and prose items (part B)

## [§32.8 Rational Solutions](https://dlmf.nist.gov/32.8)

- [32.8.ii](https://dlmf.nist.gov/32.8.ii): [`DLMF.Painleve.painleveII_exists_rational_int`](DLMF/Painleve/RationalDLMF.lean#L70) (proved)
- [32.8.v](https://dlmf.nist.gov/32.8.v): [`DLMF.Painleve.painleveV_exists_rational_iff`](DLMF/Painleve/RationalDLMF.lean#L894) (admitted)
- [32.8.E1](https://dlmf.nist.gov/32.8.E1): [`DLMF.Painleve.painleveII_rational_one`](DLMF/Painleve/RationalDLMF.lean#L80) (proved)
- [32.8.E2](https://dlmf.nist.gov/32.8.E2): [`DLMF.Painleve.painleveII_rational_two`](DLMF/Painleve/RationalDLMF.lean#L233) (proved)
- [32.8.E3](https://dlmf.nist.gov/32.8.E3): [`DLMF.Painleve.painleveII_rational_three`](DLMF/Painleve/RationalDLMF.lean#L248) (proved)
- [32.8.E4](https://dlmf.nist.gov/32.8.E4): [`DLMF.Painleve.painleveII_rational_four`](DLMF/Painleve/RationalDLMF.lean#L268) (proved)
- [32.8.E5](https://dlmf.nist.gov/32.8.E5): [`DLMF.Painleve.rationalPainleveII`](DLMF/Painleve/SolutionsDefs.lean#L67) (definition); [`DLMF.Painleve.rationalPainleveII_isPainleveIIOn`](DLMF/Painleve/RationalDLMF.lean#L546) (proved); [`DLMF.Painleve.rationalPainleveII_isPainleveIIOn_int`](DLMF/Painleve/RationalDLMF.lean#L571) (proved)
- [32.8.E6](https://dlmf.nist.gov/32.8.E6): [`DLMF.Painleve.yablonskiiVorobievQ`](DLMF/Painleve/SolutionsDefs.lean#L55) (definition); [`DLMF.Painleve.yablonskiiVorobievQ_recurrence`](DLMF/Painleve/RationalDLMF.lean#L525) (proved)
- [32.8.E7](https://dlmf.nist.gov/32.8.E7): [`DLMF.Painleve.yablonskiiVorobievQ_two`](DLMF/Painleve/RationalDLMF.lean#L110) (proved); [`DLMF.Painleve.yablonskiiVorobievQ_three`](DLMF/Painleve/RationalDLMF.lean#L117) (proved); [`DLMF.Painleve.yablonskiiVorobievQ_four`](DLMF/Painleve/RationalDLMF.lean#L148) (proved); [`DLMF.Painleve.yablonskiiVorobievQ_five`](DLMF/Painleve/RationalDLMF.lean#L158) (proved); [`DLMF.Painleve.yablonskiiVorobievQ_six`](DLMF/Painleve/RationalDLMF.lean#L171) (proved)
- [32.8.E8](https://dlmf.nist.gov/32.8.E8): [`DLMF.Painleve.yablonskiiVorobievP`](DLMF/Painleve/SolutionsDefs.lean#L84) (definition); [`DLMF.Painleve.hasSum_yablonskiiVorobievP`](DLMF/Painleve/RationalDLMF.lean#L601) (proved)
- [32.8.E9](https://dlmf.nist.gov/32.8.E9): [`DLMF.Painleve.yablonskiiVorobievTau_isPainleveIIOn`](DLMF/Painleve/RationalDLMF.lean#L657) (admitted)
- [32.8.E10](https://dlmf.nist.gov/32.8.E10): [`DLMF.Painleve.yablonskiiVorobievTau`](DLMF/Painleve/SolutionsDefs.lean#L92) (definition)
- [32.8.E11](https://dlmf.nist.gov/32.8.E11): [`DLMF.Painleve.painleveIII_rational_const`](DLMF/Painleve/RationalDLMF.lean#L671) (proved)
- [32.8.E12](https://dlmf.nist.gov/32.8.E12): [`DLMF.Painleve.painleveIII_rational_linear`](DLMF/Painleve/RationalDLMF.lean#L685) (proved)
- [32.8.E13](https://dlmf.nist.gov/32.8.E13): [`DLMF.Painleve.painleveIII_rational_mobius`](DLMF/Painleve/RationalDLMF.lean#L700) (proved)
- [32.8.E14](https://dlmf.nist.gov/32.8.E14): [`DLMF.Painleve.painleveIII_exists_rational_iff`](DLMF/Painleve/RationalDLMF.lean#L723) (admitted)
- [32.8.E15](https://dlmf.nist.gov/32.8.E15): [`DLMF.Painleve.painleveIII_rational_form`](DLMF/Painleve/RationalDLMF.lean#L733) (admitted)
- [32.8.E16](https://dlmf.nist.gov/32.8.E16): [`DLMF.Painleve.painleveIV_rational_inv`](DLMF/Painleve/RationalDLMF.lean#L744) (proved); [`DLMF.Painleve.painleveIV_rational_neg_inv`](DLMF/Painleve/RationalDLMF.lean#L760) (proved)
- [32.8.E17](https://dlmf.nist.gov/32.8.E17): [`DLMF.Painleve.painleveIV_rational_neg_two_mul`](DLMF/Painleve/RationalDLMF.lean#L787) (proved)
- [32.8.E18](https://dlmf.nist.gov/32.8.E18): [`DLMF.Painleve.painleveIV_rational_neg_two_thirds_mul`](DLMF/Painleve/RationalDLMF.lean#L794) (proved)
- [32.8.E19](https://dlmf.nist.gov/32.8.E19): [`DLMF.Painleve.painleveIV_rational_form`](DLMF/Painleve/RationalDLMF.lean#L802) (admitted)
- [32.8.E20](https://dlmf.nist.gov/32.8.E20): [`DLMF.Painleve.painleveIV_rational_form`](DLMF/Painleve/RationalDLMF.lean#L802) (admitted)
- [32.8.E21](https://dlmf.nist.gov/32.8.E21): [`DLMF.Painleve.painleveIV_rational_form`](DLMF/Painleve/RationalDLMF.lean#L802) (admitted)
- [32.8.E22](https://dlmf.nist.gov/32.8.E22): [`DLMF.Painleve.painleveIV_exists_rational_iff`](DLMF/Painleve/RationalDLMF.lean#L815) (admitted)
- [32.8.E23](https://dlmf.nist.gov/32.8.E23): [`DLMF.Painleve.painleveIV_exists_rational_iff`](DLMF/Painleve/RationalDLMF.lean#L815) (admitted)
- [32.8.E24](https://dlmf.nist.gov/32.8.E24): [`DLMF.Painleve.painleveV_rational_linear`](DLMF/Painleve/RationalDLMF.lean#L826) (proved)
- [32.8.E25](https://dlmf.nist.gov/32.8.E25): [`DLMF.Painleve.painleveV_rational_mobius`](DLMF/Painleve/RationalDLMF.lean#L841) (proved)
- [32.8.E26](https://dlmf.nist.gov/32.8.E26): [`DLMF.Painleve.painleveV_rational_mobius'`](DLMF/Painleve/RationalDLMF.lean#L867) (proved)
- [32.8.E27](https://dlmf.nist.gov/32.8.E27): [`DLMF.Painleve.painleveV_rational_form`](DLMF/Painleve/RationalDLMF.lean#L915) (admitted)
- [32.8.E28](https://dlmf.nist.gov/32.8.E28): [`DLMF.Painleve.painleveVI_rational_linear`](DLMF/Painleve/RationalDLMF.lean#L928) (proved)
- [32.8.E29](https://dlmf.nist.gov/32.8.E29): [`DLMF.Painleve.painleveVI_rational_sq`](DLMF/Painleve/RationalDLMF.lean#L948) (proved)
- [32.8.E30](https://dlmf.nist.gov/32.8.E30): [`DLMF.Painleve.painleveVI_rational_inv`](DLMF/Painleve/RationalDLMF.lean#L967) (proved)
- [32.8.E31](https://dlmf.nist.gov/32.8.E31): [`DLMF.Painleve.painleveVI_rational_inv_sq`](DLMF/Painleve/RationalDLMF.lean#L990) (proved)
- [32.8.E32](https://dlmf.nist.gov/32.8.E32): [`DLMF.Painleve.painleveVI_rational_mobius`](DLMF/Painleve/RationalDLMF.lean#L1015) (proved)
- [32.8.E33](https://dlmf.nist.gov/32.8.E33): [`DLMF.Painleve.painleveVI_exists_rational`](DLMF/Painleve/RationalDLMF.lean#L1042) (admitted)

## [§32.9 Other Elementary Solutions](https://dlmf.nist.gov/32.9)

- [32.9.i](https://dlmf.nist.gov/32.9.i): [`DLMF.Painleve.painleveIII_firstIntegral'`](DLMF/Painleve/ElementarySolutions.lean#L215) (proved); [`DLMF.Painleve.painleveIII_zero_power`](DLMF/Painleve/ElementarySolutions.lean#L244) (proved); [`DLMF.Painleve.painleveIII_zero_eq_power`](DLMF/Painleve/ElementarySolutions.lean#L264) (proved) — includes the first integral for `α = γ = 0`
- [32.9.ii](https://dlmf.nist.gov/32.9.ii): [`DLMF.Painleve.painleveV_exp'`](DLMF/Painleve/ElementarySolutions.lean#L349) (proved) — clarification: only `w = Ce^{γz}`, `γ² = -2δ`, works
- [32.9.E1](https://dlmf.nist.gov/32.9.E1): [`DLMF.Painleve.painleveIII_cbrt`](DLMF/Painleve/ElementarySolutions.lean#L46) (proved)
- [32.9.E2](https://dlmf.nist.gov/32.9.E2): [`DLMF.Painleve.painleveIII_log`](DLMF/Painleve/ElementarySolutions.lean#L73) (proved)
- [32.9.E3](https://dlmf.nist.gov/32.9.E3): [`DLMF.Painleve.painleveIII_power`](DLMF/Painleve/ElementarySolutions.lean#L105) (proved)
- [32.9.E4](https://dlmf.nist.gov/32.9.E4): [`DLMF.Painleve.painleveIII_algebraic_iff`](DLMF/Painleve/ElementarySolutions.lean#L162) (admitted)
- [32.9.E5](https://dlmf.nist.gov/32.9.E5): [`DLMF.Painleve.painleveIII_algebraic_iff`](DLMF/Painleve/ElementarySolutions.lean#L162) (admitted)
- [32.9.E6](https://dlmf.nist.gov/32.9.E6): [`DLMF.Painleve.painleveIII_firstIntegral`](DLMF/Painleve/ElementarySolutions.lean#L184) (proved)
- [32.9.E7](https://dlmf.nist.gov/32.9.E7): [`DLMF.Painleve.painleveV_sqrt`](DLMF/Painleve/ElementarySolutions.lean#L299) (proved)
- [32.9.E8](https://dlmf.nist.gov/32.9.E8): [`DLMF.Painleve.painleveV_exp`](DLMF/Painleve/ElementarySolutions.lean#L328) (proved)
- [32.9.E9](https://dlmf.nist.gov/32.9.E9): [`DLMF.Painleve.painleveV_exists_algebraic`](DLMF/Painleve/ElementarySolutions.lean#L361) (admitted)
- [32.9.E10](https://dlmf.nist.gov/32.9.E10): [`DLMF.Painleve.painleveV_exists_algebraic`](DLMF/Painleve/ElementarySolutions.lean#L361) (admitted)
- [32.9.E11](https://dlmf.nist.gov/32.9.E11): [`DLMF.Painleve.painleveV_exists_algebraic`](DLMF/Painleve/ElementarySolutions.lean#L361) (admitted)
- [32.9.E12](https://dlmf.nist.gov/32.9.E12): [`DLMF.Painleve.painleveV_firstIntegral`](DLMF/Painleve/ElementarySolutions.lean#L375) (proved)
- [32.9.E13](https://dlmf.nist.gov/32.9.E13): [`DLMF.Painleve.painleveVI_sqrt`](DLMF/Painleve/ElementarySolutions.lean#L408) (proved)

## [§32.10 Special Function Solutions](https://dlmf.nist.gov/32.10)

- [32.10.E1](https://dlmf.nist.gov/32.10.E1): excluded: informal (first-order equation satisfied by all solutions "expressible in terms of special functions"; the notion is not formalized)
- [32.10.E2](https://dlmf.nist.gov/32.10.E2): [`DLMF.Painleve.painleveII_exists_airy`](DLMF/Painleve/SpecialSolutions.lean#L112) (proved)
- [32.10.E3](https://dlmf.nist.gov/32.10.E3): [`DLMF.Painleve.painleveII_of_riccati`](DLMF/Painleve/SpecialSolutions.lean#L61) (proved)
- [32.10.E4](https://dlmf.nist.gov/32.10.E4): [`DLMF.Painleve.painleveII_airy`](DLMF/Painleve/SpecialSolutions.lean#L80) (proved)
- [32.10.E5](https://dlmf.nist.gov/32.10.E5): [`DLMF.Painleve.painleveII_airy`](DLMF/Painleve/SpecialSolutions.lean#L80) (proved)
- [32.10.E6](https://dlmf.nist.gov/32.10.E6): [`DLMF.Painleve.painleveII_three_halves`](DLMF/Painleve/SpecialSolutions.lean#L134) (proved); [`DLMF.Painleve.painleveII_airy_three_halves`](DLMF/Painleve/SpecialSolutions.lean#L240) (proved)
- [32.10.E7](https://dlmf.nist.gov/32.10.E7): [`DLMF.Painleve.painleveII_five_halves`](DLMF/Painleve/SpecialSolutions.lean#L167) (proved)
- [32.10.E8](https://dlmf.nist.gov/32.10.E8): [`DLMF.Painleve.painleveII_airy_wronskian`](DLMF/Painleve/SpecialSolutions.lean#L260) (admitted)
- [32.10.E9](https://dlmf.nist.gov/32.10.E9): [`DLMF.Painleve.wronskianTau`](DLMF/Painleve/SolutionsDefs.lean#L100) (definition)
- [32.10.E10](https://dlmf.nist.gov/32.10.E10): [`DLMF.Painleve.painleveII_neg`](DLMF/Painleve/SpecialSolutions.lean#L274) (proved)
- [32.10.E11](https://dlmf.nist.gov/32.10.E11): [`DLMF.Painleve.painleveIII_of_riccati`](DLMF/Painleve/SpecialSolutions.lean#L283) (proved)
- [32.10.E12](https://dlmf.nist.gov/32.10.E12): [`DLMF.Painleve.painleveIII_of_riccati`](DLMF/Painleve/SpecialSolutions.lean#L283) (proved)
- [32.10.E13](https://dlmf.nist.gov/32.10.E13): [`DLMF.Painleve.painleveIII_bessel_riccati`](DLMF/Painleve/SpecialSolutions.lean#L332) (proved)
- [32.10.E14](https://dlmf.nist.gov/32.10.E14): [`DLMF.Painleve.painleveIII_bessel_riccati`](DLMF/Painleve/SpecialSolutions.lean#L332) (proved)
- [32.10.E15](https://dlmf.nist.gov/32.10.E15): [`DLMF.Painleve.painleveIV_of_riccati`](DLMF/Painleve/SpecialSolutions.lean#L410) (proved)
- [32.10.E16](https://dlmf.nist.gov/32.10.E16): [`DLMF.Painleve.painleveIV_erfc_plus`](DLMF/Painleve/SpecialSolutions.lean#L564) (proved)
- [32.10.E17](https://dlmf.nist.gov/32.10.E17): [`DLMF.Painleve.painleveIV_of_riccati`](DLMF/Painleve/SpecialSolutions.lean#L410) (proved)
- [32.10.E18](https://dlmf.nist.gov/32.10.E18): [`DLMF.Painleve.painleveIV_pcf_riccati`](DLMF/Painleve/SpecialSolutions.lean#L426) (proved)
- [32.10.E19](https://dlmf.nist.gov/32.10.E19): [`DLMF.Painleve.painleveIV_pcf_riccati`](DLMF/Painleve/SpecialSolutions.lean#L426) (proved)
- [32.10.E20](https://dlmf.nist.gov/32.10.E20): [`DLMF.Painleve.painleveIV_hermite`](DLMF/Painleve/SpecialSolutions.lean#L496) (proved) — `m ≥ 1`; `m = 1` gives `w ≡ 0` (excluded)
- [32.10.E21](https://dlmf.nist.gov/32.10.E21): [`DLMF.Painleve.painleveIV_hermite'`](DLMF/Painleve/SpecialSolutions.lean#L531) (proved)
- [32.10.E22](https://dlmf.nist.gov/32.10.E22): [`DLMF.Painleve.painleveIV_erfc_plus`](DLMF/Painleve/SpecialSolutions.lean#L564) (proved); [`DLMF.Painleve.painleveIV_erfc_minus`](DLMF/Painleve/SpecialSolutions.lean#L600) (proved)
- [32.10.E23](https://dlmf.nist.gov/32.10.E23): [`DLMF.Painleve.painleveV_of_riccati`](DLMF/Painleve/SpecialSolutions.lean#L631) (proved)
- [32.10.E24](https://dlmf.nist.gov/32.10.E24): not formalized: alternative condition `(a - n)(b - n) = 0` of the informal "iff" classification of Whittaker-type solutions of `PV`; the case `n = 0` of 32.10.23 is `painleveV_of_riccati`
- [32.10.E25](https://dlmf.nist.gov/32.10.E25): [`DLMF.Painleve.painleveV_of_riccati`](DLMF/Painleve/SpecialSolutions.lean#L631) (proved)
- [32.10.E26](https://dlmf.nist.gov/32.10.E26): [`DLMF.Painleve.painleveV_whittaker_riccati`](DLMF/Painleve/SpecialSolutions.lean#L650) (proved)
- [32.10.E27](https://dlmf.nist.gov/32.10.E27): [`DLMF.Painleve.painleveV_whittaker_riccati`](DLMF/Painleve/SpecialSolutions.lean#L650) (proved)
- [32.10.E28](https://dlmf.nist.gov/32.10.E28): [`DLMF.Painleve.painleveVI_of_riccati`](DLMF/Painleve/SpecialSolutions.lean#L759) (proved)
- [32.10.E29](https://dlmf.nist.gov/32.10.E29): [`DLMF.Painleve.painleveVI_of_riccati`](DLMF/Painleve/SpecialSolutions.lean#L759) (proved) — DLMF erratum: "if n = 1" should read "n = 0"
- [32.10.E30](https://dlmf.nist.gov/32.10.E30): [`DLMF.Painleve.painleveVI_hypergeometric_riccati`](DLMF/Painleve/SpecialSolutions.lean#L791) (proved)
- [32.10.E31](https://dlmf.nist.gov/32.10.E31): [`DLMF.Painleve.painleveVI_hypergeometric_riccati`](DLMF/Painleve/SpecialSolutions.lean#L791) (proved)
- [32.10.E32](https://dlmf.nist.gov/32.10.E32): [`DLMF.Painleve.painleveVI_picard`](DLMF/Painleve/SpecialSolutions.lean#L1063) (admitted)
- [32.10.E33](https://dlmf.nist.gov/32.10.E33): [`DLMF.Painleve.painleveVI_picard`](DLMF/Painleve/SpecialSolutions.lean#L1063) (admitted)
- [32.10.E34](https://dlmf.nist.gov/32.10.E34): [`DLMF.Painleve.painleveVI_picard`](DLMF/Painleve/SpecialSolutions.lean#L1063) (admitted)

## [§32.11 Asymptotic Approximations for Real Variables](https://dlmf.nist.gov/32.11)

- [32.11.i](https://dlmf.nist.gov/32.11.i): [`DLMF.Painleve.painleveI_not_global`](DLMF/Painleve/RealAsymptotics.lean#L65) (admitted); [`DLMF.Painleve.painleveI_trichotomy`](DLMF/Painleve/RealAsymptotics.lean#L72) (admitted) — numerical bounds on `k₁`, `k₂` excluded: numerical
- [32.11.ii](https://dlmf.nist.gov/32.11.ii): [`DLMF.Painleve.painleveII_decaying_airy`](DLMF/Painleve/RealAsymptotics.lean#L100) (admitted); [`DLMF.Painleve.painleveII_existsUnique_airy`](DLMF/Painleve/RealAsymptotics.lean#L110) (admitted)
- [32.11.v](https://dlmf.nist.gov/32.11.v): [`DLMF.Painleve.painleveIV_decaying_pcf`](DLMF/Painleve/RealAsymptotics.lean#L237) (admitted); [`DLMF.Painleve.painleveIV_existsUnique_pcf`](DLMF/Painleve/RealAsymptotics.lean#L248) (admitted); [`DLMF.Painleve.painleveIV_pole`](DLMF/Painleve/RealAsymptotics.lean#L321) (admitted)
- [32.11.E1](https://dlmf.nist.gov/32.11.E1): [`DLMF.Painleve.painleveI_oscillating`](DLMF/Painleve/RealAsymptotics.lean#L47) (admitted)
- [32.11.E2](https://dlmf.nist.gov/32.11.E2): [`DLMF.Painleve.painleveI_oscillating`](DLMF/Painleve/RealAsymptotics.lean#L47) (admitted)
- [32.11.E3](https://dlmf.nist.gov/32.11.E3): [`DLMF.Painleve.painleveI_sqrt`](DLMF/Painleve/RealAsymptotics.lean#L58) (admitted)
- [32.11.E4](https://dlmf.nist.gov/32.11.E4): [`DLMF.Painleve.painleveII_decaying_airy`](DLMF/Painleve/RealAsymptotics.lean#L100) (admitted)
- [32.11.E5](https://dlmf.nist.gov/32.11.E5): [`DLMF.Painleve.painleveII_decaying_airy`](DLMF/Painleve/RealAsymptotics.lean#L100) (admitted)
- [32.11.E6](https://dlmf.nist.gov/32.11.E6): [`DLMF.Painleve.painleveII_ablowitzSegur`](DLMF/Painleve/RealAsymptotics.lean#L123) (admitted) — stronger than DLMF (global on ℝ); `d > 0`
- [32.11.E7](https://dlmf.nist.gov/32.11.E7): [`DLMF.Painleve.painleveII_ablowitzSegur`](DLMF/Painleve/RealAsymptotics.lean#L123) (admitted)
- [32.11.E8](https://dlmf.nist.gov/32.11.E8): [`DLMF.Painleve.painleveII_ablowitzSegur`](DLMF/Painleve/RealAsymptotics.lean#L123) (admitted)
- [32.11.E9](https://dlmf.nist.gov/32.11.E9): [`DLMF.Painleve.painleveII_ablowitzSegur`](DLMF/Painleve/RealAsymptotics.lean#L123) (admitted)
- [32.11.E10](https://dlmf.nist.gov/32.11.E10): [`DLMF.Painleve.painleveII_hastingsMcLeod`](DLMF/Painleve/RealAsymptotics.lean#L141) (admitted) — stronger than DLMF (global on ℝ)
- [32.11.E11](https://dlmf.nist.gov/32.11.E11): [`DLMF.Painleve.painleveII_pole`](DLMF/Painleve/RealAsymptotics.lean#L150) (admitted)
- [32.11.E12](https://dlmf.nist.gov/32.11.E12): [`DLMF.Painleve.modifiedPainleveIIRhs`](DLMF/Painleve/SolutionsDefs.lean#L134) (definition)
- [32.11.E13](https://dlmf.nist.gov/32.11.E13): [`DLMF.Painleve.modifiedPainleveII_negInfty`](DLMF/Painleve/RealAsymptotics.lean#L161) (admitted)
- [32.11.E14](https://dlmf.nist.gov/32.11.E14): [`DLMF.Painleve.modifiedPainleveII_negInfty`](DLMF/Painleve/RealAsymptotics.lean#L161) (admitted)
- [32.11.E15](https://dlmf.nist.gov/32.11.E15): [`DLMF.Painleve.modifiedPainleveII_airy`](DLMF/Painleve/RealAsymptotics.lean#L173) (admitted)
- [32.11.E16](https://dlmf.nist.gov/32.11.E16): [`DLMF.Painleve.modifiedPainleveII_airy`](DLMF/Painleve/RealAsymptotics.lean#L173) (admitted)
- [32.11.E17](https://dlmf.nist.gov/32.11.E17): [`DLMF.Painleve.modifiedPainleveII_airy`](DLMF/Painleve/RealAsymptotics.lean#L173) (admitted) — requires `d > 0`
- [32.11.E18](https://dlmf.nist.gov/32.11.E18): [`DLMF.Painleve.modifiedPainleveII_generic`](DLMF/Painleve/RealAsymptotics.lean#L188) (admitted)
- [32.11.E19](https://dlmf.nist.gov/32.11.E19): [`DLMF.Painleve.modifiedPainleveII_generic`](DLMF/Painleve/RealAsymptotics.lean#L188) (admitted)
- [32.11.E20](https://dlmf.nist.gov/32.11.E20): [`DLMF.Painleve.modifiedPainleveII_generic`](DLMF/Painleve/RealAsymptotics.lean#L188) (admitted)
- [32.11.E21](https://dlmf.nist.gov/32.11.E21): [`DLMF.Painleve.modifiedPainleveII_generic`](DLMF/Painleve/RealAsymptotics.lean#L188) (admitted)
- [32.11.E22](https://dlmf.nist.gov/32.11.E22): [`DLMF.Painleve.modifiedPainleveII_generic`](DLMF/Painleve/RealAsymptotics.lean#L188) (admitted)
- [32.11.E23](https://dlmf.nist.gov/32.11.E23): [`DLMF.Painleve.modifiedPainleveII_generic`](DLMF/Painleve/RealAsymptotics.lean#L188) (admitted)
- [32.11.E24](https://dlmf.nist.gov/32.11.E24): [`DLMF.Painleve.modifiedPainleveII_generic`](DLMF/Painleve/RealAsymptotics.lean#L188) (admitted)
- [32.11.E25](https://dlmf.nist.gov/32.11.E25): [`DLMF.Painleve.painleveIII_connection`](DLMF/Painleve/RealAsymptotics.lean#L217) (admitted)
- [32.11.E26](https://dlmf.nist.gov/32.11.E26): [`DLMF.Painleve.painleveIII_connection`](DLMF/Painleve/RealAsymptotics.lean#L217) (admitted)
- [32.11.E27](https://dlmf.nist.gov/32.11.E27): [`DLMF.Painleve.painleveIII_connection`](DLMF/Painleve/RealAsymptotics.lean#L217) (admitted)
- [32.11.E28](https://dlmf.nist.gov/32.11.E28): [`DLMF.Painleve.painleveIII_connection`](DLMF/Painleve/RealAsymptotics.lean#L217) (admitted)
- [32.11.E29](https://dlmf.nist.gov/32.11.E29): [`DLMF.Painleve.painleveIV_decaying_pcf`](DLMF/Painleve/RealAsymptotics.lean#L237) (admitted)
- [32.11.E30](https://dlmf.nist.gov/32.11.E30): [`DLMF.Painleve.painleveIV_decaying_pcf`](DLMF/Painleve/RealAsymptotics.lean#L237) (admitted)
- [32.11.E31](https://dlmf.nist.gov/32.11.E31): [`DLMF.Painleve.painleveIV_noPoles`](DLMF/Painleve/RealAsymptotics.lean#L266) (admitted)
- [32.11.E32](https://dlmf.nist.gov/32.11.E32): [`DLMF.Painleve.painleveIV_hermiteAsymptotics`](DLMF/Painleve/RealAsymptotics.lean#L277) (admitted)
- [32.11.E33](https://dlmf.nist.gov/32.11.E33): [`DLMF.Painleve.painleveIV_oscillating`](DLMF/Painleve/RealAsymptotics.lean#L287) (admitted)
- [32.11.E34](https://dlmf.nist.gov/32.11.E34): [`DLMF.Painleve.painleveIV_oscillating`](DLMF/Painleve/RealAsymptotics.lean#L287) (admitted)
- [32.11.E35](https://dlmf.nist.gov/32.11.E35): [`DLMF.Painleve.painleveIV_oscillating`](DLMF/Painleve/RealAsymptotics.lean#L287) (admitted)
- [32.11.E36](https://dlmf.nist.gov/32.11.E36): [`DLMF.Painleve.painleveIV_oscillating`](DLMF/Painleve/RealAsymptotics.lean#L287) (admitted)
- [32.11.E37](https://dlmf.nist.gov/32.11.E37): [`DLMF.Painleve.painleveIV_oscillating`](DLMF/Painleve/RealAsymptotics.lean#L287) (admitted)
- [32.11.E38](https://dlmf.nist.gov/32.11.E38): [`DLMF.Painleve.painleveIV_critical`](DLMF/Painleve/RealAsymptotics.lean#L310) (admitted)

## [§32.12 Asymptotic Approximations for Complex Variables](https://dlmf.nist.gov/32.12)

- [32.12](https://dlmf.nist.gov/32.12): no statement (references only).

## [§32.13 Reductions of Partial Differential Equations](https://dlmf.nist.gov/32.13)

- [32.13.i](https://dlmf.nist.gov/32.13.i): [`DLMF.Painleve.kdV_similarity_painleveI`](DLMF/Painleve/Reductions.lean#L242) (proved)
- [32.13.ii](https://dlmf.nist.gov/32.13.ii): [`DLMF.Painleve.painleveIII_of_sineGordon`](DLMF/Painleve/Reductions.lean#L289) (proved)
- [32.13.iii](https://dlmf.nist.gov/32.13.iii): [`DLMF.Painleve.boussinesq_painleveI`](DLMF/Painleve/Reductions.lean#L384) (proved)
- [32.13.E1](https://dlmf.nist.gov/32.13.E1): [`DLMF.Painleve.IsMKdVOn`](DLMF/Painleve/SolutionsDefs.lean#L153) (definition)
- [32.13.E2](https://dlmf.nist.gov/32.13.E2): [`DLMF.Painleve.mKdV_scalingReduction`](DLMF/Painleve/Reductions.lean#L85) (proved)
- [32.13.E3](https://dlmf.nist.gov/32.13.E3): [`DLMF.Painleve.IsKdVOn`](DLMF/Painleve/SolutionsDefs.lean#L163) (definition)
- [32.13.E4](https://dlmf.nist.gov/32.13.E4): [`DLMF.Painleve.kdV_scalingReduction`](DLMF/Painleve/Reductions.lean#L134) (proved)
- [32.13.E5](https://dlmf.nist.gov/32.13.E5): [`DLMF.Painleve.kdV_similarityReduction`](DLMF/Painleve/Reductions.lean#L208) (proved)
- [32.13.E6](https://dlmf.nist.gov/32.13.E6): [`DLMF.Painleve.IsSineGordonOn`](DLMF/Painleve/SolutionsDefs.lean#L172) (definition)
- [32.13.E7](https://dlmf.nist.gov/32.13.E7): [`DLMF.Painleve.sineGordon_scalingReduction`](DLMF/Painleve/Reductions.lean#L263) (proved)
- [32.13.E8](https://dlmf.nist.gov/32.13.E8): [`DLMF.Painleve.IsBoussinesqOn`](DLMF/Painleve/SolutionsDefs.lean#L180) (definition)
- [32.13.E9](https://dlmf.nist.gov/32.13.E9): [`DLMF.Painleve.boussinesq_travellingWave`](DLMF/Painleve/Reductions.lean#L317) (proved)
- [32.13.E10](https://dlmf.nist.gov/32.13.E10): [`DLMF.Painleve.boussinesq_travellingWave`](DLMF/Painleve/Reductions.lean#L317) (proved)

## [§32.14 Combinatorics](https://dlmf.nist.gov/32.14)

- [32.14](https://dlmf.nist.gov/32.14): [`DLMF.Painleve.longestIncreasingLength`](DLMF/Painleve/SolutionsDefs.lean#L193) (definition)
- [32.14.E1](https://dlmf.nist.gov/32.14.E1): [`DLMF.Painleve.longestIncreasing_tracyWidom`](DLMF/Painleve/Combinatorics.lean#L37) (admitted)
- [32.14.E2](https://dlmf.nist.gov/32.14.E2): [`DLMF.Painleve.tracyWidomF`](DLMF/Painleve/SolutionsDefs.lean#L202) (definition)
- [32.14.E3](https://dlmf.nist.gov/32.14.E3): [`DLMF.Painleve.longestIncreasing_tracyWidom`](DLMF/Painleve/Combinatorics.lean#L37) (admitted)
- [32.14.E4](https://dlmf.nist.gov/32.14.E4): [`DLMF.Painleve.longestIncreasing_tracyWidom`](DLMF/Painleve/Combinatorics.lean#L37) (admitted)

## [§32.15 Orthogonal Polynomials](https://dlmf.nist.gov/32.15)

- [32.15](https://dlmf.nist.gov/32.15): [`DLMF.Painleve.freudRecurrenceSq_painleveIV`](DLMF/Painleve/Combinatorics.lean#L61) (admitted)
- [32.15.E1](https://dlmf.nist.gov/32.15.E1): [`DLMF.Painleve.freudMoment`](DLMF/Painleve/SolutionsDefs.lean#L211) (definition)
- [32.15.E2](https://dlmf.nist.gov/32.15.E2): [`DLMF.Painleve.freudRecurrenceSq`](DLMF/Painleve/SolutionsDefs.lean#L221) (definition)
- [32.15.E3](https://dlmf.nist.gov/32.15.E3): [`DLMF.Painleve.freudRecurrenceSq_discretePainleveI`](DLMF/Painleve/Combinatorics.lean#L52) (admitted)

## [§32.16 Physical Applications](https://dlmf.nist.gov/32.16)

- [32.16](https://dlmf.nist.gov/32.16): excluded: application (statistical physics and spin models, integrable dynamical systems, the Ising model, 2D quantum gravity, string theory; references only, no mathematical statement).

## [§32.17 Methods of Computation](https://dlmf.nist.gov/32.17)

- [32.17](https://dlmf.nist.gov/32.17): excluded: computation.

