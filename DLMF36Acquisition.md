# DLMF Chapter 36 acquisition: Integrals with Coalescing Saddles

> Source paths and current layout notes were refreshed on 2026-10-30; generated per-entry
> statuses follow the compiled ledger refresh. Dated acquisition and proof counts
> describe their original batches.

**Current layout (2026-10-30).** `DLMF.CoalescingSaddles.Basic` exports the canonical definitions in
`Basic.CanonicalIntegrals` and `Basic.AuxiliaryData`. The `CanonicalIntegrals`,
`BifurcationSets`, `StokesSets` and `Scaling` files are theorem developments outside that
foundation.

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 36](https://dlmf.nist.gov/36), version 1.2.8, checked on 2026-10-26, by two
agents: part A (agent cs1, helper prefix `s36a_`) covers §§36.1–36.6, part B covers
§§36.7–36.15 and appends its sections below. The Lean code is in `DLMF/CoalescingSaddles/`
(namespace `DLMF.CoalescingSaddles`). The part A modules, in import order, are
[Basic](DLMF/CoalescingSaddles/Basic.lean) (the foundational umbrella),
[CanonicalIntegrals](DLMF/CoalescingSaddles/CanonicalIntegrals.lean) (§36.2; imports `Basic`,
`DLMF.Core.Framework` and `DLMF.Airy.IntegralRepresentations`),
[BifurcationSets](DLMF/CoalescingSaddles/BifurcationSets.lean) (§36.4; imports `Basic`),
[StokesSets](DLMF/CoalescingSaddles/StokesSets.lean) (§36.5; imports `Basic`) and
[Scaling](DLMF/CoalescingSaddles/Scaling.lean) (§36.6; imports `Basic`). There are no upstream
pointers: Mathlib and TauCeti have no catastrophe integrals, bifurcation sets or Stokes sets
(the Airy and Bessel functions used in 36.2.7, 36.2.9, 36.2.13, 36.2.19, 36.2.20 and 36.2.28
come from the project's `DLMF.Airy` area and from `Complex.besselJ`).

**Counts (part A).** §§36.2, 36.4–36.6 have 68 numbered equations (36.2: 29, 36.4: 13,
36.5: 21, 36.6: 5) and one table (36.6.T1); §36.1 is notation only and §36.3 is excluded:
graphics. Excluded as numerical: 36.2.E16 and 36.5.E5. In scope: 67 IDs (66 equations and
the table); all 67 are covered by project declarations. In addition the prose IDs 36.5.ii
(the fold Stokes set) and 36.5.iii carry tags, so 69 DLMF IDs are tagged on 88 declarations.
The 195 declarations of the five modules are 48 definitions (all in `Basic`), 123 proved
theorems and lemmas (of which 91 untagged helpers, API and bridge lemmas, among them one
instance) and 24 direct admissions. One proved theorem depends on an admission:
`hasIntegralWholeLine_pearcey` (36.2.14) is derived from `hasIntegralWholeLine_cuspoidIntegral`
(36.2.4).

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Basic](DLMF/CoalescingSaddles/Basic.lean): 0 admissions; 48 definitions.
- [CanonicalIntegrals](DLMF/CoalescingSaddles/CanonicalIntegrals.lean): 16 admissions;
  76 theorems: 60 proved, 16 admitted.
- [BifurcationSets](DLMF/CoalescingSaddles/BifurcationSets.lean): 2 admissions; 41 theorems:
  39 proved, 2 admitted.
- [StokesSets](DLMF/CoalescingSaddles/StokesSets.lean): 6 admissions; 8 theorems: 2 proved,
  6 admitted.
- [Scaling](DLMF/CoalescingSaddles/Scaling.lean): 0 admissions; 22 theorems (one an
  instance), all proved.

## Domains, conventions and source corrections

- **Parameters.** `cuspoidPotential K t x` takes complex `t` and real `x : Fin K → ℝ`; `x m` is
  DLMF's `x_{m+1}`, the coefficient of `t^{m+1}`. The swallowtail coordinates `(x, y, z)` are
  `(x 0, x 1, x 2)`. The umbilic potentials take complex `s, t` and real `x, y, z`. The
  canonical integrals take real parameters, the diffraction catastrophes also `k`, with DLMF's
  `k > 0` as a hypothesis wherever it matters.
- **Canonical integrals as contour integrals.** DLMF's integrals over `ℝ` or `ℝ²` (36.2.4,
  36.2.5, 36.2.10, 36.2.11) are oscillatory and not absolutely convergent; following DLMF's
  remark in §36.2(i) they are defined as absolutely convergent Bochner integrals over rotated
  contours. Cuspoids: `t = r d(r)` with `d(r) = e^{iπ/(2(K+2))}` for `r ≥ 0` and, for `r < 0`,
  the same direction (`K` even, a straight line) or `e^{-iπ/(2(K+2))}` (`K` odd, a V through 0).
  Hyperbolic umbilic: the product of two cubic V-contours. Elliptic umbilic: in
  `a = s + it`, `b = s - it` (Jacobian `ds dt = (i/2) da db`) the 2-cycle `∑ ε_{jk} ρ_j × ρ_k`
  of products of rays `ρ_j = e^{i(π/6 + 2πj/3)}[0, ∞)`, `ε = [[-1,0,1],[0,1,-1],[1,-1,0]]`
  (`ellipticUmbilicCycle`). This cycle was checked numerically against 36.2.6, 36.2.7,
  36.2.18, 36.2.20, 36.2.24–36.2.26 and 36.2.28 (agreement to about 12 digits). The agreement
  with DLMF's improper integrals is stated separately: `hasIntegralWholeLine_cuspoidIntegral`,
  `hasIntegralWholeLine_cuspoidDiffraction` (limits of `∫_{-R}^{R}`) and
  `hasIteratedIntegral_…` (iterated limits for the umbilics); these are admitted.
- **One-dimensional representations.** The contour integrals in 36.2.6 and 36.2.8 use
  `DLMF.Airy.contourIntegral` (rays at the stated angles joined by an arc of radius 1); the
  integrals over `[0, ∞)` in 36.2.7 and 36.2.9 are Bochner integrals.
- **Critical points and bifurcation sets.** Derivatives are complex derivatives (`deriv`,
  `iteratedDeriv`) of the polynomial potentials; real critical points are real arguments where
  they vanish (36.4.1, 36.4.2). The bifurcation sets 36.4.3–36.4.4 are sets of parameters with a
  degenerate real critical point. The cusp lines (ribs, 36.4.9, 36.4.11, 36.4.13) are
  `cuspoidCuspLines` (also `∂³Φ/∂t³ = 0`) and `umbilicCuspLines` (a real kernel direction
  `(u, v) ≠ 0` of the Hessian along which the third derivative vanishes); the swallowtail
  self-intersection is `cuspoidSelfIntersection` (two distinct degenerate real critical points).
  All of 36.4.5–36.4.13 are proved as set equalities.
- **Stokes sets.** `cuspoidStokesSet` and `umbilicStokesSet` follow 36.5.1 and the text after
  it: a real critical point connected to a nonreal critical point by a path on which `Re Φ` is
  constant (`IsSaddleConnection`, `IsSaddleConnection₂`). The parts connecting two nonreal
  critical points that are not complex conjugates (36.5.10, 36.5.18) are
  `cuspoidComplexStokesSet` and `umbilicComplexStokesSet`. Where DLMF uses a decimal threshold
  (`Y₁`, `X₂`) the statement asserts the existence of a positive threshold. Square roots in
  36.5.9, 36.5.11–36.5.13, 36.5.16, 36.5.21 are `Real.sqrt`, with the radicand conditions as
  hypotheses where needed; `sign z` is `Real.sign z`.
- **Scaling.** 36.6.1 is proved for `k > 0` for cuspoids and both umbilics by linear changes of
  variables; the rotated contours are invariant under positive scaling.
- **Restricted domains** (no errata): 36.2.19 is stated for `y ≠ 0` and 36.2.28 for `z > 0`
  (the right sides are limits at `0`); 36.4.8 is stated with `z < 0` where DLMF prints `z ≤ 0`
  (at `z = 0` the two degenerate critical points coincide, so the origin is only a limit point
  of the self-intersection line); 36.4.12 is stated for `z ≠ 0` (the slice `z = 0` of the
  hyperbolic umbilic bifurcation set is the pair of half-lines `x = 0, y ≤ 0` and `y = 0,
  x ≤ 0`, which the parametrization, even with DLMF's `τ = -∞`, does not produce).
- **Fold Stokes set** (36.5.ii). For complex `x` the dominance condition
  `Re(Φ₁(t) - Φ₁(-t)) = 0` holds exactly when `x³` is real and nonnegative, that is on the rays
  `ph x ∈ {0, ±2π/3}` (`fold_dominance_iff`, proved). DLMF's Stokes set is the pair of rays
  `ph x = ±2π/3`; on the positive axis only the subdominant saddle contributes to `Ai`, so no
  switching occurs there.
- **Source corrections.** None. Verified numerically as printed (mpmath): 36.2.6–36.2.9,
  36.2.13, 36.2.15, 36.2.17–36.2.29, 36.5.2–36.5.4 and 36.5.6–36.5.21 (at sample points the
  real parts of `Φ` at the connected critical points agree to working precision); 36.4.5–36.4.13,
  36.6.1, 36.6.5 and Table 36.6.1 are proved as printed (apart from the domain remarks above). For the swallowtail with `z < 0`, 36.5.8 has spurious roots unless
  `|Y| > (2/5)^{1/2}`, the condition DLMF states; it is a hypothesis of
  `cuspoidStokesSet_three_param`.

## Numbered formulas and prose items

## [§36.1 Special Notation](https://dlmf.nist.gov/36.1)

- [36.1](https://dlmf.nist.gov/36.1): notation only; no statement.

## [§36.2 Catastrophes and Canonical Integrals](https://dlmf.nist.gov/36.2)

- [36.2.E1](https://dlmf.nist.gov/36.2.E1): [`DLMF.CoalescingSaddles.cuspoidPotential`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L71) (definition)
- [36.2.E2](https://dlmf.nist.gov/36.2.E2): [`DLMF.CoalescingSaddles.ellipticUmbilicPotential`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L78) (definition)
- [36.2.E3](https://dlmf.nist.gov/36.2.E3): [`DLMF.CoalescingSaddles.hyperbolicUmbilicPotential`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L85) (definition)
- [36.2.E4](https://dlmf.nist.gov/36.2.E4): [`DLMF.CoalescingSaddles.cuspoidIntegral`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L126) (definition); [`DLMF.CoalescingSaddles.hasIntegralWholeLine_cuspoidIntegral`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L279) (proved)
- [36.2.E5](https://dlmf.nist.gov/36.2.E5): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L134) (definition); [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L150) (definition); [`DLMF.CoalescingSaddles.hasIteratedIntegral_hyperbolicUmbilicIntegral`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L287) (admitted); [`DLMF.CoalescingSaddles.hasIteratedIntegral_ellipticUmbilicIntegral`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L296) (admitted)
- [36.2.E6](https://dlmf.nist.gov/36.2.E6): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_eq_contour`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L577) (admitted)
- [36.2.E7](https://dlmf.nist.gov/36.2.E7): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_eq_airy`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L589) (admitted)
- [36.2.E8](https://dlmf.nist.gov/36.2.E8): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_eq_contour`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L605) (admitted)
- [36.2.E9](https://dlmf.nist.gov/36.2.E9): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_eq_airy`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L674) (proved)
- [36.2.E10](https://dlmf.nist.gov/36.2.E10): [`DLMF.CoalescingSaddles.cuspoidDiffraction`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L159) (definition); [`DLMF.CoalescingSaddles.hasIntegralWholeLine_cuspoidDiffraction`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L320) (proved)
- [36.2.E11](https://dlmf.nist.gov/36.2.E11): [`DLMF.CoalescingSaddles.hyperbolicUmbilicDiffraction`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L167) (definition); [`DLMF.CoalescingSaddles.ellipticUmbilicDiffraction`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L175) (definition); [`DLMF.CoalescingSaddles.hasIteratedIntegral_hyperbolicUmbilicDiffraction`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L328) (admitted); [`DLMF.CoalescingSaddles.hasIteratedIntegral_ellipticUmbilicDiffraction`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L337) (admitted)
- [36.2.E12](https://dlmf.nist.gov/36.2.E12): [`DLMF.CoalescingSaddles.cuspoidIntegral_zero_dim`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L206) (proved)
- [36.2.E13](https://dlmf.nist.gov/36.2.E13): [`DLMF.CoalescingSaddles.cuspoidIntegral_one`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L376) (proved)
- [36.2.E14](https://dlmf.nist.gov/36.2.E14): [`DLMF.CoalescingSaddles.pearcey`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L182) (definition); [`DLMF.CoalescingSaddles.hasIntegralWholeLine_pearcey`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L738) (proved)
- [36.2.E15](https://dlmf.nist.gov/36.2.E15): [`DLMF.CoalescingSaddles.cuspoidIntegral_at_zero`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L245) (proved)
- [36.2.E16](https://dlmf.nist.gov/36.2.E16): excluded: numerical (decimal values of `Ψ₁(0)`, …, `Ψ₄(0)`; the exact values are 36.2.15).
- [36.2.E17](https://dlmf.nist.gov/36.2.E17): [`DLMF.CoalescingSaddles.iteratedDeriv_cuspoidIntegral_odd`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L226) (proved); [`DLMF.CoalescingSaddles.iteratedDeriv_cuspoidIntegral_even`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L249) (proved)
- [36.2.E18](https://dlmf.nist.gov/36.2.E18): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_zero`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L477) (proved); [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_zero`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L770) (proved)
- [36.2.E19](https://dlmf.nist.gov/36.2.E19): [`DLMF.CoalescingSaddles.cuspoidIntegral_two_zero_left`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L831) (admitted) Stated for `y ≠ 0`: at `y = 0` the right side is a `0 · ∞` limit (equal to `Ψ₂(0)`).
- [36.2.E20](https://dlmf.nist.gov/36.2.E20): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_z_zero`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L965) (proved)
- [36.2.E21](https://dlmf.nist.gov/36.2.E21): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_z_zero`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L465) (proved)
- [36.2.E22](https://dlmf.nist.gov/36.2.E22): [`DLMF.CoalescingSaddles.cuspoidIntegral_even_symm`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L313) (proved)
- [36.2.E23](https://dlmf.nist.gov/36.2.E23): [`DLMF.CoalescingSaddles.cuspoidIntegral_odd_conj`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L326) (proved)
- [36.2.E24](https://dlmf.nist.gov/36.2.E24): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_conj`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L492) (proved); [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_conj`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L699) (proved)
- [36.2.E25](https://dlmf.nist.gov/36.2.E25): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_neg_y`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L572) (proved)
- [36.2.E26](https://dlmf.nist.gov/36.2.E26): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_rotate`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L597) (proved)
- [36.2.E27](https://dlmf.nist.gov/36.2.E27): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_swap`](DLMF/CoalescingSaddles/CanonicalIntegrals/ContoursAndSymmetries.lean#L510) (proved)
- [36.2.E28](https://dlmf.nist.gov/36.2.E28): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_axis`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L1034) (admitted) Stated for `z > 0`: at `z = 0` the right side is read as its limit `Ψ^{(E)}(0)`.
- [36.2.E29](https://dlmf.nist.gov/36.2.E29): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_axis`](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L1045) (admitted)

## [§36.3 Visualizations of Canonical Integrals](https://dlmf.nist.gov/36.3)

- [36.3](https://dlmf.nist.gov/36.3): excluded: graphics.

## [§36.4 Bifurcation Sets](https://dlmf.nist.gov/36.4)

- [36.4.E1](https://dlmf.nist.gov/36.4.E1): [`DLMF.CoalescingSaddles.cuspoidCriticalPoints`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L189) (definition); [`DLMF.CoalescingSaddles.cuspoidCriticalPoints_finite_ncard_le`](DLMF/CoalescingSaddles/BifurcationSets.lean#L871) (proved)
- [36.4.E2](https://dlmf.nist.gov/36.4.E2): [`DLMF.CoalescingSaddles.umbilicCriticalPoints`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L228) (definition); [`DLMF.CoalescingSaddles.umbilicCriticalPoints_finite_ncard_le`](DLMF/CoalescingSaddles/BifurcationSets.lean#L901) (proved)
- [36.4.E3](https://dlmf.nist.gov/36.4.E3): [`DLMF.CoalescingSaddles.cuspoidBifurcationSet`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L195) (definition)
- [36.4.E4](https://dlmf.nist.gov/36.4.E4): [`DLMF.CoalescingSaddles.umbilicBifurcationSet`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L234) (definition)
- [36.4.E5](https://dlmf.nist.gov/36.4.E5): [`DLMF.CoalescingSaddles.cuspoidBifurcationSet_one`](DLMF/CoalescingSaddles/BifurcationSets.lean#L220) (proved)
- [36.4.E6](https://dlmf.nist.gov/36.4.E6): [`DLMF.CoalescingSaddles.cuspoidBifurcationSet_two`](DLMF/CoalescingSaddles/BifurcationSets.lean#L234) (proved)
- [36.4.E7](https://dlmf.nist.gov/36.4.E7): [`DLMF.CoalescingSaddles.cuspoidBifurcationSet_three`](DLMF/CoalescingSaddles/BifurcationSets.lean#L287) (proved)
- [36.4.E8](https://dlmf.nist.gov/36.4.E8): [`DLMF.CoalescingSaddles.cuspoidSelfIntersection_three`](DLMF/CoalescingSaddles/BifurcationSets.lean#L296) (proved) DLMF prints `z ≤ 0`; acquired with `z < 0` (at `z = 0` there are no two distinct degenerate critical points).
- [36.4.E9](https://dlmf.nist.gov/36.4.E9): [`DLMF.CoalescingSaddles.cuspoidCuspLines_three`](DLMF/CoalescingSaddles/BifurcationSets.lean#L337) (proved)
- [36.4.E10](https://dlmf.nist.gov/36.4.E10): [`DLMF.CoalescingSaddles.umbilicBifurcationSet_elliptic`](DLMF/CoalescingSaddles/BifurcationSets.lean#L575) (proved)
- [36.4.E11](https://dlmf.nist.gov/36.4.E11): [`DLMF.CoalescingSaddles.umbilicCuspLines_elliptic`](DLMF/CoalescingSaddles/BifurcationSets.lean#L697) (proved)
- [36.4.E12](https://dlmf.nist.gov/36.4.E12): [`DLMF.CoalescingSaddles.umbilicBifurcationSet_hyperbolic`](DLMF/CoalescingSaddles/BifurcationSets.lean#L512) (proved) Stated for `z ≠ 0`; the slice `z = 0` (two half-lines) is not given by the parametrization.
- [36.4.E13](https://dlmf.nist.gov/36.4.E13): [`DLMF.CoalescingSaddles.umbilicCuspLines_hyperbolic`](DLMF/CoalescingSaddles/BifurcationSets.lean#L472) (proved)

## [§36.5 Stokes Sets](https://dlmf.nist.gov/36.5)

- [36.5.ii](https://dlmf.nist.gov/36.5.ii): [`DLMF.CoalescingSaddles.fold_dominance_iff`](DLMF/CoalescingSaddles/StokesSets.lean#L54) (proved) The fold (`K = 1`) prose statement, as the dominance condition for complex `x`.
- [36.5.iii](https://dlmf.nist.gov/36.5.iii): [`DLMF.CoalescingSaddles.umbilicStokesSet_elliptic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L327) (admitted); [`DLMF.CoalescingSaddles.umbilicStokesSet_hyperbolic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L347) (admitted)
- [36.5.E1](https://dlmf.nist.gov/36.5.E1): [`DLMF.CoalescingSaddles.cuspoidStokesSet`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L270) (definition); [`DLMF.CoalescingSaddles.umbilicStokesSet`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L284) (definition)
- [36.5.E2](https://dlmf.nist.gov/36.5.E2): [`DLMF.CoalescingSaddles.cuspoidStokesSet_two`](DLMF/CoalescingSaddles/StokesSets.lean#L276) (proved)
- [36.5.E3](https://dlmf.nist.gov/36.5.E3): [`DLMF.CoalescingSaddles.swallowtailStokesB`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L306) (definition); [`DLMF.CoalescingSaddles.cuspoidStokesSet_three_z_zero`](DLMF/CoalescingSaddles/StokesSets.lean#L286) (admitted)
- [36.5.E4](https://dlmf.nist.gov/36.5.E4): [`DLMF.CoalescingSaddles.swallowtailStokesQuintic`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L300) (definition); [`DLMF.CoalescingSaddles.cuspoidStokesSet_three_z_zero`](DLMF/CoalescingSaddles/StokesSets.lean#L286) (admitted)
- [36.5.E5](https://dlmf.nist.gov/36.5.E5): excluded: numerical (decimal values of `B_±`; the exact form is 36.5.3–36.5.4).
- [36.5.E6](https://dlmf.nist.gov/36.5.E6): [`DLMF.CoalescingSaddles.cuspoidStokesSet_three_param`](DLMF/CoalescingSaddles/StokesSets.lean#L298) (admitted)
- [36.5.E7](https://dlmf.nist.gov/36.5.E7): [`DLMF.CoalescingSaddles.swallowtailStokesX`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L318) (definition); [`DLMF.CoalescingSaddles.cuspoidStokesSet_three_param`](DLMF/CoalescingSaddles/StokesSets.lean#L298) (admitted)
- [36.5.E8](https://dlmf.nist.gov/36.5.E8): [`DLMF.CoalescingSaddles.swallowtailStokesEq`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L324) (definition); [`DLMF.CoalescingSaddles.cuspoidStokesSet_three_param`](DLMF/CoalescingSaddles/StokesSets.lean#L298) (admitted)
- [36.5.E9](https://dlmf.nist.gov/36.5.E9): [`DLMF.CoalescingSaddles.swallowtailStokesT`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L312) (definition); [`DLMF.CoalescingSaddles.cuspoidStokesSet_three_param`](DLMF/CoalescingSaddles/StokesSets.lean#L298) (admitted)
- [36.5.E10](https://dlmf.nist.gov/36.5.E10): [`DLMF.CoalescingSaddles.cuspoidComplexStokesSet_three_param`](DLMF/CoalescingSaddles/StokesSets.lean#L313) (admitted)
- [36.5.E11](https://dlmf.nist.gov/36.5.E11): [`DLMF.CoalescingSaddles.umbilicStokesSet_elliptic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L327) (admitted)
- [36.5.E12](https://dlmf.nist.gov/36.5.E12): [`DLMF.CoalescingSaddles.umbilicStokesSet_elliptic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L327) (admitted)
- [36.5.E13](https://dlmf.nist.gov/36.5.E13): [`DLMF.CoalescingSaddles.ellipticStokesW`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L333) (definition)
- [36.5.E14](https://dlmf.nist.gov/36.5.E14): [`DLMF.CoalescingSaddles.umbilicStokesSet_elliptic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L327) (admitted)
- [36.5.E15](https://dlmf.nist.gov/36.5.E15): [`DLMF.CoalescingSaddles.umbilicStokesSet_hyperbolic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L347) (admitted)
- [36.5.E16](https://dlmf.nist.gov/36.5.E16): [`DLMF.CoalescingSaddles.hyperbolicStokesY`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L339) (definition); [`DLMF.CoalescingSaddles.hyperbolicStokesF`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L345) (definition)
- [36.5.E17](https://dlmf.nist.gov/36.5.E17): [`DLMF.CoalescingSaddles.umbilicStokesSet_hyperbolic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L347) (admitted)
- [36.5.E18](https://dlmf.nist.gov/36.5.E18): [`DLMF.CoalescingSaddles.umbilicStokesSet_hyperbolic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L347) (admitted)
- [36.5.E19](https://dlmf.nist.gov/36.5.E19): [`DLMF.CoalescingSaddles.umbilicStokesSet_hyperbolic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L347) (admitted)
- [36.5.E20](https://dlmf.nist.gov/36.5.E20): [`DLMF.CoalescingSaddles.umbilicStokesSet_hyperbolic_param`](DLMF/CoalescingSaddles/StokesSets.lean#L347) (admitted)
- [36.5.E21](https://dlmf.nist.gov/36.5.E21): [`DLMF.CoalescingSaddles.hyperbolicStokesW`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L351) (definition)

## [§36.6 Scaling Relations](https://dlmf.nist.gov/36.6)

- [36.6.E1](https://dlmf.nist.gov/36.6.E1): [`DLMF.CoalescingSaddles.cuspoidDiffraction_eq_scale`](DLMF/CoalescingSaddles/Scaling.lean#L79) (proved); [`DLMF.CoalescingSaddles.hyperbolicUmbilicDiffraction_eq_scale`](DLMF/CoalescingSaddles/Scaling.lean#L174) (proved); [`DLMF.CoalescingSaddles.ellipticUmbilicDiffraction_eq_scale`](DLMF/CoalescingSaddles/Scaling.lean#L243) (proved)
- [36.6.E2](https://dlmf.nist.gov/36.6.E2): [`DLMF.CoalescingSaddles.cuspoidScaledCoords`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L386) (definition)
- [36.6.E3](https://dlmf.nist.gov/36.6.E3): [`DLMF.CoalescingSaddles.cuspoidSingularityIndex`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L361) (definition); [`DLMF.CoalescingSaddles.umbilicSingularityIndex`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L365) (definition)
- [36.6.E4](https://dlmf.nist.gov/36.6.E4): [`DLMF.CoalescingSaddles.cuspoidCoordinateIndex`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L369) (definition); [`DLMF.CoalescingSaddles.umbilicCoordinateIndex`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L374) (definition)
- [36.6.E5](https://dlmf.nist.gov/36.6.E5): [`DLMF.CoalescingSaddles.cuspoidVolumeIndex`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L378) (definition); [`DLMF.CoalescingSaddles.umbilicVolumeIndex`](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L382) (definition); [`DLMF.CoalescingSaddles.cuspoidVolumeIndex_eq`](DLMF/CoalescingSaddles/Scaling.lean#L268) (proved); [`DLMF.CoalescingSaddles.umbilicVolumeIndex_eq`](DLMF/CoalescingSaddles/Scaling.lean#L279) (proved)
- [36.6.T1](https://dlmf.nist.gov/36.6.T1): [`DLMF.CoalescingSaddles.scalingExponents_fold`](DLMF/CoalescingSaddles/Scaling.lean#L284) (proved); [`DLMF.CoalescingSaddles.scalingExponents_cusp`](DLMF/CoalescingSaddles/Scaling.lean#L295) (proved); [`DLMF.CoalescingSaddles.scalingExponents_swallowtail`](DLMF/CoalescingSaddles/Scaling.lean#L307) (proved)

## Prose, informal and excluded items (part A)

- [36.1](https://dlmf.nist.gov/36.1): notation only.
- [36.2.i](https://dlmf.nist.gov/36.2.i): the definitions of the catastrophes and canonical
  integrals are 36.2.1–36.2.11; the remark that convergence follows by rotating the integration
  paths is the basis of the contour definitions (see above). The names of the catastrophes
  (fold, cusp, swallowtail, elliptic and hyperbolic umbilic) are recorded in docstrings.
- [36.2.ii](https://dlmf.nist.gov/36.2.ii), [36.2.iii](https://dlmf.nist.gov/36.2.iii): no
  further statements beyond 36.2.12–36.2.27.
- [36.2.iv](https://dlmf.nist.gov/36.2.iv): the bibliographic attribution (Berry and Howls)
  is not acquired; its formulas are 36.2.28–36.2.29.
- [36.2.E16](https://dlmf.nist.gov/36.2.E16), the decimal values quoted with 36.2.18, and
  [36.5.E5](https://dlmf.nist.gov/36.5.E5), `X₁ = 6.95643`, `|Y₁| = 6.81337`, `X₂ = 0.45148`,
  `Y₂ = 0.59693` and the coefficient `1.32403` in 36.5.2: excluded: numerical.
- [36.3](https://dlmf.nist.gov/36.3): excluded: graphics.
- [36.4.i](https://dlmf.nist.gov/36.4.i): the definitions are 36.4.1–36.4.4; the descriptive
  phrases (fold point, cusp point, cusp-edged sheets, astroid) are in docstrings.
- [36.4.ii](https://dlmf.nist.gov/36.4.ii): excluded: graphics.
- [36.5.i](https://dlmf.nist.gov/36.5.i): definition prose (exponentially small contributions
  across Stokes sets); formalized through 36.5.1 as above. The asymptotic meaning (acquisition
  of an exponentially small contribution) is not formalized.
- [36.5.ii](https://dlmf.nist.gov/36.5.ii): the fold statement is `fold_dominance_iff`; the
  descriptive statements (the cusp Stokes set is a cusped curve connected to the cusp; the
  swallowtail sheets for `z < 0` are cusp-edged and connected to the bifurcation set; the
  second sheet for `z > 0` meets the bifurcation set smoothly along the line `X = X₁`,
  `|Y| = |Y₁|`) are not formalized beyond the parametrizations.
- [36.5.iii](https://dlmf.nist.gov/36.5.iii): the elliptic umbilic Stokes set has three
  sheets related by rotation by `2π/3` (this follows from 36.2.26, proved); the hyperbolic
  umbilic Stokes set intersects the smooth sheet of the bifurcation set along `|X| = X₂`,
  `Y = Y₂` (not formalized beyond the threshold statement).
- [36.5.iv](https://dlmf.nist.gov/36.5.iv): excluded: graphics (the region counts of real
  and complex critical points in the figures are not acquired).
- Bibliographic paragraphs ("See Wright (1980)", "Berry and Howls (1990)", …) are not acquired.

## Validation (part A)

- The five modules build with `lake build DLMF.CoalescingSaddles.<Module>` and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` without errors or warnings
  other than the admissions (`Basic` and `Scaling` without admissions). There are no axioms,
  no `native_decide`, and no `sorry` in definitions or helper declarations (prefix `s36a_`).
  No line exceeds 100 characters.
- `#print axioms` for all 32 tagged proved theorems (for example `cuspoidIntegral_one`,
  `cuspoidIntegral_at_zero`, `ellipticUmbilicIntegral_zero`, `ellipticUmbilicIntegral_rotate`,
  `umbilicBifurcationSet_elliptic`, `umbilicCuspLines_elliptic`,
  `umbilicBifurcationSet_hyperbolic`, `cuspoidSelfIntersection_three`, `fold_dominance_iff`,
  `cuspoidDiffraction_eq_scale`, `ellipticUmbilicDiffraction_eq_scale`) shows only `propext`,
  `Classical.choice` and `Quot.sound`, except `hasIntegralWholeLine_pearcey`, which uses the
  admitted 36.2.4.
- Admitted statements were checked numerically before acquisition (mpmath quadrature of the
  contour integrals, polynomial roots and critical values): 36.2.6–36.2.9, 36.2.17, 36.2.19,
  36.2.20, 36.2.28, 36.2.29 and the Stokes parametrizations 36.5.2–36.5.21. The agreement
  statements 36.2.4, 36.2.5, 36.2.10, 36.2.11 (improper integrals equal the contour integrals)
  rest on DLMF's own remark in §36.2(i); the bounds 36.4.1–36.4.2 follow from the degrees of
  the critical-point equations (a polynomial of degree `K + 1`; two conics, Bézout).
- DLMF.lean, the umbrella `DLMF/CoalescingSaddles.lean`, the lakefile and the other ledgers are
  unchanged by part A.


## Part B: §§36.7–36.15 (agent cs2, 2026-10-26)

The part B modules, in import order, are
[AuxiliaryData](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean) (part-B definitions; uses `Basic.CanonicalIntegrals` and
the Airy definition layer `DLMF.Airy.Basic`),
[DifferentialEquations](DLMF/CoalescingSaddles/DifferentialEquations.lean) (§36.10; imports
`Basic` and `CanonicalIntegrals`),
[Zeros](DLMF/CoalescingSaddles/Zeros.lean) (§36.7; imports `Basic` and `CanonicalIntegrals`),
[Series](DLMF/CoalescingSaddles/Series.lean) (§36.8; imports `Basic`),
[IntegralIdentities](DLMF/CoalescingSaddles/IntegralIdentities.lean) (§36.9; imports `Basic`)
and [Asymptotics](DLMF/CoalescingSaddles/Asymptotics.lean) (§36.11; imports `Basic` and
`CanonicalIntegrals`). There are no upstream pointers: Mathlib and TauCeti have no cuspoid or
umbilic canonical integrals (the fold case `Ψ₁` is the Airy function of `DLMF.Airy`).

**Counts (part B).** §§36.7–36.11 have 49 numbered equations (36.7: 8, 36.8: 6, 36.9: 9,
36.10: 18, 36.11: 8); all 49 are in scope and covered by project declarations. In addition the
prose IDs 36.7.i and 36.7.ii carry tags. §§36.12 (12 equations) and 36.13 (8 equations) are
excluded: application; §36.14 is excluded: application (prose only) and §36.15 excluded:
computation; Table 36.7.1 and the decimal values in §36.7 are excluded: numerical. 51 DLMF IDs
are tagged on 66 declarations. The 123 declarations of the six modules are 19 definitions (all
in `Defs`; 16 tagged, 3 untagged helpers), 76 proved theorems (of which 54 untagged helpers,
bridge and API lemmas) and 28 direct admissions. Two proved tagged theorems depend on an
admission: `ellipticUmbilicIntegral_z_atBot` and `hyperbolicUmbilicIntegral_z_atBot` (the
corrected `z → -∞` forms of 36.11.7–36.11.8, derived from the admitted `z → +∞` forms by
36.2.24).

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [AuxiliaryData](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean): 0 admissions; 19 definitions.
- [DifferentialEquations](DLMF/CoalescingSaddles/DifferentialEquations.lean): 3 admissions;
  66 theorems: 63 proved, 3 admitted.
- [Zeros](DLMF/CoalescingSaddles/Zeros.lean): 2 admissions; 6 theorems: 4 proved, 2 admitted.
- [Series](DLMF/CoalescingSaddles/Series.lean): 4 admissions; 10 theorems: 6 proved,
  4 admitted.
- [IntegralIdentities](DLMF/CoalescingSaddles/IntegralIdentities.lean): 9 admissions;
  9 theorems, all admitted.
- [Asymptotics](DLMF/CoalescingSaddles/Asymptotics.lean): 10 admissions; 13 theorems:
  3 proved, 10 admitted.

### Domains, conventions and source corrections (part B)

- **Partial derivatives.** `∂ⁿΨ_K/∂x_mⁿ` is `iteratedDeriv n` of `s ↦ Ψ_K(update x m s)` at
  `x m` (Lean index `m` is DLMF's `x_{m+1}`). Differentiation under the integral sign is proved
  for all moments `∫ tᵖ exp(iΦ_K)` (`cuspoidMoment`, `hasDerivAt_cuspoidMoment_update`) and for
  the hyperbolic umbilic moments `∫∫ sᵃ tᵇ exp(iΦ^{(H)})` (`hyperbolicUmbilicMoment`,
  `hasDerivAt_hyperbolicUmbilicMoment_x/_y/_z`), so `deriv` is never evaluated at a
  non-differentiable point in the proved equations.
- **36.10.11–36.10.12** (the general form of the umbilic equations, `∂Φ/∂s = ∂Φ/∂t = 0`
  under the integral) are tagged on the four umbilic equations 36.10.13–36.10.16 that
  instantiate them.
- **36.10.14** is stated in its corrected form (DLMF version 1.0.1 erratum: the term
  `2iz ∂Ψ^{(E)}/∂x`, originally printed with `Ψ^{(H)}`).
- **Zeros (36.7).** 36.7.1, 36.7.2 and 36.7.5–36.7.7 are approximate formulas (`≈`); their
  right-hand sides are recorded as definitions (`cuspInnerZeroX`, `cuspOuterZeroX`,
  `ellipticUmbilicLatticeDz`, …) and the approximation claims are not formalized (DLMF gives no
  error term). 36.7.3 is the transcendental equation for the outer-zero parameter; existence
  and uniqueness of its root is proved (`existsUnique_cuspOuterZeroParam`). 36.7.4 has an exact
  form (`ellipticUmbilicRingPlane_eq`). 36.7.8 carries an `O(1/n)` and is stated as an
  existence statement for zeros along the three symmetry rays (admitted).
- **Series (36.8).** All series are `HasSum` statements. The four series of 36.8.3 (from
  `n = 0, 2, 2, 1`) are stated as one series from `n = 0`; the omitted terms vanish since
  `d₀ = c₁ = 0` (`umbilicSeriesD_zero`, `umbilicSeriesC_one`). The recurrences 36.8.2 and 36.8.6
  are the definitions (proved as equations).
- **Integral identities (36.9).** Absolutely convergent identities include the integrability
  of the right-hand side as a conjunct; 36.9.3 and 36.9.9 (conditionally convergent outer
  integrals) are stated as limits of `∫_0^R` as `R → ∞`.
- **Asymptotics (36.11).** 36.11.1–36.11.2 are stated along `cuspoidScaledCoords K x k`
  (`k → ∞`) for `x` off the bifurcation set, with remainder `o(k^{1/(K+2)-1/2})`; the sign
  factor `(-1)^{j+K+1}` of DLMF is the sign of `Φ''` at the critical point
  (`cuspoidStationaryPhaseSum`, a finite sum over the real critical points). 36.11.6 for
  `z → +∞` is stated with remainder `o(|z|^{-1/3})`: stronger than DLMF.
- **Errata.** 36.11.7 and 36.11.8 are valid only for `z → +∞`. For `z → -∞` the correct forms
  are `Ψ^{(E)}(0,0,z) = (π/z)(i − √3 e^{4iz³/27} + o(1))` and
  `Ψ^{(H)}(0,0,z) = (2π/z)(−1 − (i/√3) e^{iz³/27} + o(1))`; they follow from the `+∞` forms
  by 36.2.24 (`Ψ(x,y,z) = conj Ψ(x,y,−z)`), which is how they are proved
  (`ellipticUmbilicIntegral_z_atBot`, `hyperbolicUmbilicIntegral_z_atBot`). Evidence (direct
  mpmath quadrature of the contour integrals): `Ψ^{(E)}(0,0,−6) = 0.75621 − 1.01820i` against
  the printed form `−0.75656 − 0.02351i` and the corrected form `0.75656 − 1.02369i`;
  `Ψ^{(H)}(0,0,−12) = 0.80126 + 0.11760i` against printed `−0.24548 + 0.11846i` and corrected
  `0.80172 + 0.11846i`; `Ψ^{(H)}(0,0,−6) = 1.6419 − 0.0997i` against printed
  `−0.449 − 0.088i`.

### Numbered formulas and prose items (part B)

## [§36.7 Zeros](https://dlmf.nist.gov/36.7)

- [36.7.E1](https://dlmf.nist.gov/36.7.E1): [`DLMF.CoalescingSaddles.cuspInnerZeroY`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L100) (definition); [`DLMF.CoalescingSaddles.cuspInnerZeroX`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L105) (definition)
- [36.7.E2](https://dlmf.nist.gov/36.7.E2): [`DLMF.CoalescingSaddles.cuspOuterZeroY`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L122) (definition); [`DLMF.CoalescingSaddles.cuspOuterZeroX`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L127) (definition)
- [36.7.E3](https://dlmf.nist.gov/36.7.E3): [`DLMF.CoalescingSaddles.IsCuspOuterZeroParam`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L113) (definition); [`DLMF.CoalescingSaddles.existsUnique_cuspOuterZeroParam`](DLMF/CoalescingSaddles/Zeros.lean#L87) (proved)
- [36.7.E4](https://dlmf.nist.gov/36.7.E4): [`DLMF.CoalescingSaddles.ellipticUmbilicRingPlane`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L133) (definition); [`DLMF.CoalescingSaddles.ellipticUmbilicRingPlane_eq`](DLMF/CoalescingSaddles/Zeros.lean#L161) (proved)
- [36.7.E5](https://dlmf.nist.gov/36.7.E5): [`DLMF.CoalescingSaddles.ellipticUmbilicLatticeDz`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L139) (definition); [`DLMF.CoalescingSaddles.ellipticUmbilicLatticeDx`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L144) (definition)
- [36.7.E6](https://dlmf.nist.gov/36.7.E6): [`DLMF.CoalescingSaddles.ellipticUmbilicRingEquation`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L148) (definition)
- [36.7.E7](https://dlmf.nist.gov/36.7.E7): [`DLMF.CoalescingSaddles.ellipticUmbilicRingCount`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L161) (definition)
- [36.7.E8](https://dlmf.nist.gov/36.7.E8): [`DLMF.CoalescingSaddles.ellipticUmbilicPlaneZeroRadius`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L166) (definition); [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_plane_zeros`](DLMF/CoalescingSaddles/Zeros.lean#L171) (admitted)
- [36.7.i](https://dlmf.nist.gov/36.7.i): [`DLMF.CoalescingSaddles.cuspoidIntegral_one_eq_zero_iff`](DLMF/CoalescingSaddles/Zeros.lean#L39) (proved)
- [36.7.ii](https://dlmf.nist.gov/36.7.ii): [`DLMF.CoalescingSaddles.cuspoidIntegral_two_ne_zero_of_nonneg`](DLMF/CoalescingSaddles/Zeros.lean#L53) (admitted)
- [36.7.iii](https://dlmf.nist.gov/36.7.iii): the descriptive prose (the zeros are lines in
  `(x, y, z)`-space where the phase of `Ψ^{(E)}` is singular, forming rings near the `z`-axis
  arranged in a lattice) is not formalized beyond 36.7.4–36.7.8.
- [36.7.iv](https://dlmf.nist.gov/36.7.iv): the zeros of `Ψ₃` and `Ψ^{(H)}` are curves in
  `(x, y, z)`-space; descriptive statement with references only, not formalized.
- [Table 36.7.1](https://dlmf.nist.gov/36.7.T1) and the decimal value `3.48734` in 36.7.8:
  excluded: numerical.

## [§36.8 Convergent Series](https://dlmf.nist.gov/36.8)

- [36.8.E1](https://dlmf.nist.gov/36.8.E1): [`DLMF.CoalescingSaddles.hasSum_cuspoidIntegral_even`](DLMF/CoalescingSaddles/Series.lean#L608) (proved); [`DLMF.CoalescingSaddles.hasSum_cuspoidIntegral_odd`](DLMF/CoalescingSaddles/Series.lean#L637) (proved)
- [36.8.E2](https://dlmf.nist.gov/36.8.E2): [`DLMF.CoalescingSaddles.cuspoidSeriesCoeff`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L58) (definition); [`DLMF.CoalescingSaddles.cuspoidSeriesCoeff_zero`](DLMF/CoalescingSaddles/Series.lean#L40) (proved); [`DLMF.CoalescingSaddles.cuspoidSeriesCoeff_succ`](DLMF/CoalescingSaddles/Series.lean#L45) (proved)
- [36.8.E3](https://dlmf.nist.gov/36.8.E3): [`DLMF.CoalescingSaddles.hasSum_hyperbolicUmbilicIntegral`](DLMF/CoalescingSaddles/Series.lean#L660) (proved)
- [36.8.E4](https://dlmf.nist.gov/36.8.E4): [`DLMF.CoalescingSaddles.hasSum_ellipticUmbilicIntegral`](DLMF/CoalescingSaddles/Series.lean#L704) (admitted)
- [36.8.E5](https://dlmf.nist.gov/36.8.E5): [`DLMF.CoalescingSaddles.ellipticUmbilicSeriesF`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L84) (definition)
- [36.8.E6](https://dlmf.nist.gov/36.8.E6): [`DLMF.CoalescingSaddles.umbilicSeriesC`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L76) (definition); [`DLMF.CoalescingSaddles.umbilicSeriesD`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L80) (definition); [`DLMF.CoalescingSaddles.umbilicSeries_recurrence`](DLMF/CoalescingSaddles/Series.lean#L53) (proved)
- The reference to Connor and Curtis (1982) for multinomial series is not acquired.

## [§36.9 Integral Identities](https://dlmf.nist.gov/36.9)

- [36.9.E1](https://dlmf.nist.gov/36.9.E1): [`DLMF.CoalescingSaddles.normSq_cuspoidIntegral_one_eq_integral`](DLMF/CoalescingSaddles/IntegralIdentities.lean#L38) (admitted)
- [36.9.E2](https://dlmf.nist.gov/36.9.E2): [`DLMF.CoalescingSaddles.airyAi_sq_eq_integral`](DLMF/CoalescingSaddles/IntegralIdentities.lean#L47) (admitted)
- [36.9.E3](https://dlmf.nist.gov/36.9.E3): [`DLMF.CoalescingSaddles.normSq_cuspoidIntegral_one_eq_improper`](DLMF/CoalescingSaddles/IntegralIdentities.lean#L56) (admitted)
- [36.9.E4](https://dlmf.nist.gov/36.9.E4): [`DLMF.CoalescingSaddles.normSq_cuspoidIntegral_two_eq_integral`](DLMF/CoalescingSaddles/IntegralIdentities.lean#L65) (admitted)
- [36.9.E5](https://dlmf.nist.gov/36.9.E5): [`DLMF.CoalescingSaddles.normSq_cuspoidIntegral_two_eq_integral_cos`](DLMF/CoalescingSaddles/IntegralIdentities.lean#L79) (admitted)
- [36.9.E6](https://dlmf.nist.gov/36.9.E6): [`DLMF.CoalescingSaddles.normSq_cuspoidIntegral_three_eq_integral`](DLMF/CoalescingSaddles/IntegralIdentities.lean#L89) (admitted)
- [36.9.E7](https://dlmf.nist.gov/36.9.E7): [`DLMF.CoalescingSaddles.normSq_cuspoidIntegral_three_eq_integral_re`](DLMF/CoalescingSaddles/IntegralIdentities.lean#L102) (admitted)
- [36.9.E8](https://dlmf.nist.gov/36.9.E8): [`DLMF.CoalescingSaddles.normSq_hyperbolicUmbilicIntegral_eq_integral`](DLMF/CoalescingSaddles/IntegralIdentities.lean#L115) (admitted)
- [36.9.E9](https://dlmf.nist.gov/36.9.E9): [`DLMF.CoalescingSaddles.normSq_ellipticUmbilicIntegral_eq_integral`](DLMF/CoalescingSaddles/IntegralIdentities.lean#L128) (admitted)

## [§36.10 Differential Equations](https://dlmf.nist.gov/36.10)

- [36.10.E1](https://dlmf.nist.gov/36.10.E1): [`DLMF.CoalescingSaddles.cuspoidIntegral_operator_eq`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L451) (proved)
- [36.10.E2](https://dlmf.nist.gov/36.10.E2): [`DLMF.CoalescingSaddles.cuspoidIntegral_ode`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L479) (proved)
- [36.10.E3](https://dlmf.nist.gov/36.10.E3): [`DLMF.CoalescingSaddles.cuspoidIntegral_one_ode`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L519) (proved)
- [36.10.E4](https://dlmf.nist.gov/36.10.E4): [`DLMF.CoalescingSaddles.cuspoidIntegral_two_ode`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L534) (proved)
- [36.10.E5](https://dlmf.nist.gov/36.10.E5): [`DLMF.CoalescingSaddles.cuspoidIntegral_three_ode`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L554) (proved)
- [36.10.E6](https://dlmf.nist.gov/36.10.E6): [`DLMF.CoalescingSaddles.cuspoidIntegral_iteratedDeriv_swap`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L581) (proved)
- [36.10.E7](https://dlmf.nist.gov/36.10.E7): [`DLMF.CoalescingSaddles.cuspoidIntegral_two_iteratedDeriv`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L594) (proved)
- [36.10.E8](https://dlmf.nist.gov/36.10.E8): [`DLMF.CoalescingSaddles.cuspoidIntegral_three_iteratedDeriv_xy`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L609) (proved)
- [36.10.E9](https://dlmf.nist.gov/36.10.E9): [`DLMF.CoalescingSaddles.cuspoidIntegral_three_iteratedDeriv_xz`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L624) (proved)
- [36.10.E10](https://dlmf.nist.gov/36.10.E10): [`DLMF.CoalescingSaddles.cuspoidIntegral_three_iteratedDeriv_yz`](DLMF/CoalescingSaddles/DifferentialEquations/Cuspoid.lean#L641) (proved)
- [36.10.E11](https://dlmf.nist.gov/36.10.E11): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_pde_xy`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L682) (proved); [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_pde_xx_yy`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L705) (proved); [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_pde_x`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L739) (proved); [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_pde_y`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L753) (proved)
- [36.10.E12](https://dlmf.nist.gov/36.10.E12): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_pde_xy`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L682) (proved); [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_pde_xx_yy`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L705) (proved); [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_pde_x`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L739) (proved); [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_pde_y`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L753) (proved)
- [36.10.E13](https://dlmf.nist.gov/36.10.E13): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_pde_xy`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L682) (proved)
- [36.10.E14](https://dlmf.nist.gov/36.10.E14): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_pde_xx_yy`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L705) (proved)
- [36.10.E15](https://dlmf.nist.gov/36.10.E15): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_pde_x`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L739) (proved)
- [36.10.E16](https://dlmf.nist.gov/36.10.E16): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_pde_y`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L753) (proved)
- [36.10.E17](https://dlmf.nist.gov/36.10.E17): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_pde_z`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L767) (proved)
- [36.10.E18](https://dlmf.nist.gov/36.10.E18): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_pde_z`](DLMF/CoalescingSaddles/DifferentialEquations/EllipticUmbilic.lean#L784) (proved)

## [§36.11 Leading-Order Asymptotics](https://dlmf.nist.gov/36.11)

- [36.11.E1](https://dlmf.nist.gov/36.11.E1): [`DLMF.CoalescingSaddles.cuspoidStationaryPhaseSum`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L174) (definition)
- [36.11.E2](https://dlmf.nist.gov/36.11.E2): [`DLMF.CoalescingSaddles.cuspoidStationaryPhaseSum`](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L174) (definition); [`DLMF.CoalescingSaddles.cuspoidIntegral_sub_stationaryPhaseSum_isLittleO`](DLMF/CoalescingSaddles/Asymptotics.lean#L59) (admitted)
- [36.11.E3](https://dlmf.nist.gov/36.11.E3): [`DLMF.CoalescingSaddles.cuspoidIntegral_two_zero_atTop`](DLMF/CoalescingSaddles/Asymptotics.lean#L533) (proved); [`DLMF.CoalescingSaddles.cuspoidIntegral_two_zero_atBot`](DLMF/CoalescingSaddles/Asymptotics.lean#L560) (admitted)
- [36.11.E4](https://dlmf.nist.gov/36.11.E4): [`DLMF.CoalescingSaddles.cuspoidIntegral_three_x_atTop`](DLMF/CoalescingSaddles/Asymptotics.lean#L570) (admitted); [`DLMF.CoalescingSaddles.cuspoidIntegral_three_x_atBot`](DLMF/CoalescingSaddles/Asymptotics.lean#L582) (admitted)
- [36.11.E5](https://dlmf.nist.gov/36.11.E5): [`DLMF.CoalescingSaddles.cuspoidIntegral_three_y_conj`](DLMF/CoalescingSaddles/Asymptotics.lean#L592) (proved); [`DLMF.CoalescingSaddles.cuspoidIntegral_three_y_atTop`](DLMF/CoalescingSaddles/Asymptotics.lean#L601) (admitted)
- [36.11.E6](https://dlmf.nist.gov/36.11.E6): [`DLMF.CoalescingSaddles.cuspoidIntegral_three_z_atTop`](DLMF/CoalescingSaddles/Asymptotics.lean#L612) (proved); [`DLMF.CoalescingSaddles.cuspoidIntegral_three_z_atBot`](DLMF/CoalescingSaddles/Asymptotics.lean#L653) (admitted)
- [36.11.E7](https://dlmf.nist.gov/36.11.E7): [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_z_atTop`](DLMF/CoalescingSaddles/Asymptotics.lean#L665) (admitted); [`DLMF.CoalescingSaddles.ellipticUmbilicIntegral_z_atBot`](DLMF/CoalescingSaddles/Asymptotics.lean#L674) (proved from admissions)
- [36.11.E8](https://dlmf.nist.gov/36.11.E8): [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_z_atTop`](DLMF/CoalescingSaddles/Asymptotics.lean#L694) (admitted); [`DLMF.CoalescingSaddles.hyperbolicUmbilicIntegral_z_atBot`](DLMF/CoalescingSaddles/Asymptotics.lean#L703) (proved from admissions)

## [§36.12 Uniform Approximation of Integrals](https://dlmf.nist.gov/36.12)

- Excluded: application. 36.12.1–36.12.12: the uniform asymptotic approximation of integrals
  `I(y, k) = ∫ exp(ik f(u; y)) g(u, y) du` with coalescing stationary points by a smooth map of
  `f` to the cuspoid normal form `Φ_K(t; x)` (36.12.2–36.12.10), with the resulting expansion in
  `Ψ_K` and its derivatives; for `K = 1` this is the Airy-type uniform approximation
  36.12.11–36.12.12 (Chester–Friedman–Ursell). Not acquired.

## [§36.13 Kelvin's Ship-Wave Pattern](https://dlmf.nist.gov/36.13)

- Excluded: application. 36.13.1–36.13.8: the ship-wave integral as a superposition over
  directions `θ`, its stationary points `θ±` (two coalescing at the critical angle
  `arcsin(1/3)`, about 19.47°), and the Airy-type uniform approximation of the wake near the
  critical angle. Not acquired.

## [§36.14 Other Physical Applications](https://dlmf.nist.gov/36.14)

- Excluded: application (prose and references only).

## [§36.15 Methods of Computation](https://dlmf.nist.gov/36.15)

- Excluded: computation.

### Validation (part B)

- The six modules build with `lake build DLMF.CoalescingSaddles.<Module>` and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` without errors or warnings
  other than the admissions (`Defs` without admissions). There are no axioms, no
  `native_decide`, and no `sorry` in definitions or helper declarations (prefix `s36b_`).
  No line exceeds 100 characters.
- `#print axioms` for proved theorems (for example `cuspoidIntegral_ode`,
  `cuspoidIntegral_three_iteratedDeriv_yz`, `hyperbolicUmbilicIntegral_pde_x`,
  `hyperbolicUmbilicIntegral_pde_y`, `hyperbolicUmbilicIntegral_pde_z`,
  `existsUnique_cuspOuterZeroParam`, `cuspoidIntegral_one_eq_zero_iff`,
  `umbilicSeries_recurrence`, `cuspoidIntegral_three_y_conj`, `ellipticUmbilicRingPlane_eq`)
  shows only `propext`, `Classical.choice` and `Quot.sound`.
- Admitted statements were checked numerically before acquisition (mpmath, rotated-contour
  quadrature of the canonical integrals): 36.8.1 for `K = 1, …, 4`, 36.8.3 and 36.8.4 (about
  19 digits); 36.10.2–36.10.10 for `K = 1, …, 4` and 36.10.13–36.10.18 (residuals below
  `10^{-26}`); 36.9.1–36.9.8 (6–15 digits; 36.9.7 to `10^{-4}` with a cutoff); 36.11.2 for
  `K = 1, 2, 3` and 36.11.3–36.11.8 (leading to the errata above); 36.7.1–36.7.3 against
  Table 36.7.1; 36.7.8 along the rays `θ = π/3, π/5, −2π/5`. For 36.9.9 the check was
  inconclusive: the inner `θ`-integral involves cancellation from about `10^{50}` and the
  partial `u`-integrals oscillate; no evidence against the formula was found.
- DLMF.lean, the umbrella `DLMF/CoalescingSaddles.lean`, the lakefile, part A's files and the
  other ledgers are unchanged by part B. The umbrella should add
  `DLMF.CoalescingSaddles.Basic.AuxiliaryData`, `.DifferentialEquations`, `.Zeros`, `.Series`,
  `.IntegralIdentities` and `.Asymptotics`.
