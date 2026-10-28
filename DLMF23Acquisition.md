# DLMF Chapter 23 acquisition: Weierstrass Elliptic and Modular Functions

This acquisition covers definitions, numbered formulas and analytical assertions in prose from
[DLMF Chapter 23](https://dlmf.nist.gov/23), version 1.2.8, checked on 2026-10-25. In scope are
§§23.2, 23.3, 23.5–23.15 and 23.17–23.19: **150 numbered equations**, all covered (146 by local
declarations, four by Mathlib pointers only). Graphics (§§23.4, 23.16), applications
(§§23.20–23.21) and computation, tables and software (§§23.22–23.24) are excluded; §23.1 is
notation only. The pure-mathematics content of the application sections is listed below for a
later round.

**Status after proof round 1 (2026-10-25).** The 198 declarations tagged with Chapter 23 IDs are 25 definitions, 117 proved theorems and 56 theorems that still depend on admissions (53 direct admissions in DLMF/Weierstrass; the counts below record the acquisition and earlier states). The per-line statuses in this ledger are regenerated from the compiled dump. See REVIEW.md, "Proof round 1 for Chapters 19–23 (2026-10-25)".

The entry point is [DLMF/Weierstrass.lean](DLMF/Weierstrass.lean).
[MathlibCoverage.lean](DLMF/Weierstrass/MathlibCoverage.lean) records 20 checked Mathlib pointers.
The area has 261 declarations (198 carrying DLMF tags): 54 definitions and
structures, 84 proved theorems (15 of them through admitted dependencies) and
**123 direct admissions**. Proved results include the
locally uniform convergence and derivative of ζ (23.2.7), the quasi-periodicity of ζ and
η₁ + η₂ + η₃ = 0 (23.2.11, 23.2.13), the cubic for the lattice roots (23.3.3), the derivative
identities 23.3.13 and 23.14.1–3, homogeneity 23.10.17–19 and the scaling of the invariants,
the Laurent coefficients c₂, c₃ (23.9.4), the product form of η (23.17.8), the SL(2, ℤ) bridge
for 23.15.3 and the wrappers 23.15.1, 23.15.2, 23.15.8, 23.18.3. Links and statuses below come
from the source files; "proved from admitted dependencies" means `#print axioms` shows
`sorryAx` through an admitted lemma.

## Domains, conventions and source corrections

- Lattices are described by `HalfPeriods` (`ω₁, ω₃` with ℑ(ω₃/ω₁) > 0, `ω₂ = -ω₁ - ω₃`); the
  Mathlib `PeriodPair` has the full periods `2ω₁, 2ω₃`. Functions of a lattice (`℘`, `ζ`, `σ`,
  `g₂`, `g₃`, Δ) are stated on `PeriodPair` where they do not depend on the generators.
  Functions of given invariants 23.3.8 use a choice of lattice; uniqueness is admitted.
- `τ = ω₃/ω₁` and `q = e^{iπτ}`; all theta relations use the lattice-parameter form
  `θⱼ(z|τ)`, which avoids the branch of `q^{1/4}` and holds for every pair of generators.
  The limit `q → 0` (§§23.12, 23.17) is `τ → i∞` (`UpperHalfPlane.atImInfty`) with ω₁ fixed.
- `λ` and `J` are defined from `θⱼ(0|τ)` and `θ₁'(0|τ)`; the branch of `q^{1/4}` in DLMF's
  nome form drops out of their fourth and eighth powers. η is Mathlib's `ModularForm.eta`.
- The level ℓ of 23.15.5 is encoded by the integer `ℓ₂ = 2ℓ`; "analytic at q = 0" means
  `f(τ) = F(e^{iπτ})` with `F` analytic at 0.
- **23.6.17** with the principal K(k) of §19.2 fails for some generator pairs; the lattice form
  K = (π/2)θ₃²(0|τ) holds for all. The literal form assumes τ = iK'/K.
- **23.6.29** (erratum): the sign of the last term is +, not −.
- **23.7.1–3** are stated in their Jacobian forms; the square-root forms hold only up to branch.
- **23.8.1–2** (source correction): the condition must be |ℑ(z/ω₁)| < 2ℑτ.
- **23.10.14** (erratum): the index set is (j, ℓ) ≠ (0, 0). **23.10.15** (erratum): π² should
  be π.
- **23.11.2–3** (source corrections): valid only for 2ω₁ = 1; 23.11.3 needs a factor 4 on the
  integral; the printed convergence condition is insufficient and is replaced by
  |ℜz| + |ℜτ| < 1, |ℑz| < ℑτ.
- **23.18.4** (terminology): J is a modular function, not a modular form in the sense of
  23.15(i), because of its pole at q = 0.
- 23.18.7 follows the V1.0.11 erratum (no coprimality condition). In 23.5(iv) the condition
  Δ < 0 follows from the other conditions.

Every correction was checked numerically with mpmath. The uncorrected formulas checked the same
way (§§23.2–23.3, 23.5–23.7, 23.9–23.10, 23.12 and 23.15–23.19) agree with the printed forms.

## Numbered formulas

## [§23.2 Definitions and Periodic Properties](https://dlmf.nist.gov/23.2)

- [23.2.E1](https://dlmf.nist.gov/23.2.E1): [`DLMF.Weierstrass.HalfPeriods.ω₂`](DLMF/Weierstrass/Basic.lean#L63) (definition); [`DLMF.Weierstrass.HalfPeriods.ω₁_add_ω₂_add_ω₃`](DLMF/Weierstrass/Basic.lean#L67) (proved). ω₂ = -ω₁ - ω₃ for DLMF half-periods; Mathlib's PeriodPair uses full periods 2ω₁, 2ω₃.
- [23.2.E2](https://dlmf.nist.gov/23.2.E2): [`DLMF.Weierstrass.HalfPeriods.generators_iff`](DLMF/Weierstrass/Basic.lean#L195) (proved).
- [23.2.E3](https://dlmf.nist.gov/23.2.E3): [`DLMF.Weierstrass.HalfPeriods.generators_iff`](DLMF/Weierstrass/Basic.lean#L195) (proved).
- [23.2.E4](https://dlmf.nist.gov/23.2.E4): Mathlib: [`PeriodPair.weierstrassP`](DLMF/Weierstrass/MathlibCoverage.lean#L26) (exact: ℘(z) = 1/z² + Σ' ((z-w)⁻² - w⁻²), written as one lattice sum (the w = 0 term is 1/z²)); Mathlib: [`PeriodPair.hasSum_weierstrassP`](DLMF/Weierstrass/MathlibCoverage.lean#L29) (exact: the lattice series 23.2.4 converges).
- [23.2.E5](https://dlmf.nist.gov/23.2.E5): [`DLMF.Weierstrass.weierstrassZeta`](DLMF/Weierstrass/Basic.lean#L264) (definition).
- [23.2.E6](https://dlmf.nist.gov/23.2.E6): [`DLMF.Weierstrass.weierstrassSigma`](DLMF/Weierstrass/Basic.lean#L272) (definition).
- [23.2.E7](https://dlmf.nist.gov/23.2.E7): [`DLMF.Weierstrass.hasDerivAt_weierstrassZeta`](DLMF/Weierstrass/Basic.lean#L508) (proved).
- [23.2.E8](https://dlmf.nist.gov/23.2.E8): [`DLMF.Weierstrass.weierstrassZeta_eq_deriv_div`](DLMF/Weierstrass/Basic.lean#L570) (proved).
- [23.2.E9](https://dlmf.nist.gov/23.2.E9): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_add_two_mul_halfPeriod`](DLMF/Weierstrass/Basic.lean#L1060) (proved); Mathlib: [`PeriodPair.weierstrassP_add_coe`](DLMF/Weierstrass/MathlibCoverage.lean#L31) (exact: ℘(z + 2ω_j) = ℘(z); stated for every lattice vector). local half-period form plus the Mathlib lattice-vector form.
- [23.2.E10](https://dlmf.nist.gov/23.2.E10): [`DLMF.Weierstrass.HalfPeriods.derivWeierstrassP_halfPeriod`](DLMF/Weierstrass/Basic.lean#L1067) (proved).
- [23.2.E11](https://dlmf.nist.gov/23.2.E11): [`DLMF.Weierstrass.HalfPeriods.weierstrassZeta_add_two_mul_halfPeriod`](DLMF/Weierstrass/Basic.lean#L1078) (proved).
- [23.2.E12](https://dlmf.nist.gov/23.2.E12): [`DLMF.Weierstrass.HalfPeriods.eta`](DLMF/Weierstrass/Basic.lean#L1037) (definition).
- [23.2.E13](https://dlmf.nist.gov/23.2.E13): [`DLMF.Weierstrass.HalfPeriods.eta_one_add_eta_two_add_eta_three`](DLMF/Weierstrass/Basic.lean#L1092) (proved).
- [23.2.E14](https://dlmf.nist.gov/23.2.E14): [`DLMF.Weierstrass.HalfPeriods.legendre_relation`](DLMF/Weierstrass/Relations.lean#L393) (proved).
- [23.2.E15](https://dlmf.nist.gov/23.2.E15): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_add_two_mul_halfPeriod`](DLMF/Weierstrass/Basic.lean#L1120) (proved).
- [23.2.E16](https://dlmf.nist.gov/23.2.E16): [`DLMF.Weierstrass.HalfPeriods.deriv_weierstrassSigma_two_mul_halfPeriod`](DLMF/Weierstrass/Basic.lean#L1151) (proved).
- [23.2.E17](https://dlmf.nist.gov/23.2.E17): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_add_lattice`](DLMF/Weierstrass/Relations.lean#L443) (proved).

## [§23.3 Differential Equations](https://dlmf.nist.gov/23.3)

- [23.3.E1](https://dlmf.nist.gov/23.3.E1): Mathlib: [`PeriodPair.g₂`](DLMF/Weierstrass/MathlibCoverage.lean#L49) (exact: g₂ = 60 Σ' w⁻⁴).
- [23.3.E2](https://dlmf.nist.gov/23.3.E2): Mathlib: [`PeriodPair.g₃`](DLMF/Weierstrass/MathlibCoverage.lean#L51) (exact: g₃ = 140 Σ' w⁻⁶).
- [23.3.E3](https://dlmf.nist.gov/23.3.E3): [`DLMF.Weierstrass.HalfPeriods.e_isRoot`](DLMF/Weierstrass/Basic.lean#L1185) (proved).
- [23.3.E4](https://dlmf.nist.gov/23.3.E4): [`DLMF.Weierstrass.latticeDiscriminant`](DLMF/Weierstrass/Basic.lean#L1284) (definition); [`DLMF.Weierstrass.HalfPeriods.latticeDiscriminant_eq`](DLMF/Weierstrass/Basic.lean#L696) (proved from admitted dependencies).
- [23.3.E5](https://dlmf.nist.gov/23.3.E5): [`DLMF.Weierstrass.HalfPeriods.e_sum`](DLMF/Weierstrass/Basic.lean#L616) (proved from admitted dependencies).
- [23.3.E6](https://dlmf.nist.gov/23.3.E6): [`DLMF.Weierstrass.HalfPeriods.g₂_eq_e`](DLMF/Weierstrass/Basic.lean#L653) (proved from admitted dependencies).
- [23.3.E7](https://dlmf.nist.gov/23.3.E7): [`DLMF.Weierstrass.HalfPeriods.g₃_eq_e`](DLMF/Weierstrass/Basic.lean#L663) (proved from admitted dependencies).
- [23.3.E8](https://dlmf.nist.gov/23.3.E8): [`DLMF.Weierstrass.weierstrassPInvariants`](DLMF/Weierstrass/Basic.lean#L1725) (definition); [`DLMF.Weierstrass.weierstrassPInvariants_eq`](DLMF/Weierstrass/Basic.lean#L847) (proved from admitted dependencies). ℘(z; g₂, g₃) uses a choice of lattice with the given invariants; independence of the choice is proved modulo the admitted uniqueness of the lattice.
- [23.3.E9](https://dlmf.nist.gov/23.3.E9): [`DLMF.Weierstrass.HalfPeriods.e`](DLMF/Weierstrass/Basic.lean#L1033) (definition).
- [23.3.E10](https://dlmf.nist.gov/23.3.E10): Mathlib: [`PeriodPair.derivWeierstrassP_sq`](DLMF/Weierstrass/MathlibCoverage.lean#L53) (exact: ℘'² = 4℘³ - g₂℘ - g₃ off the lattice).
- [23.3.E11](https://dlmf.nist.gov/23.3.E11): [`DLMF.Weierstrass.HalfPeriods.derivWeierstrassP_sq_eq_prod`](DLMF/Weierstrass/DifferentialEquations.lean#L31) (proved from admitted dependencies).
- [23.3.E12](https://dlmf.nist.gov/23.3.E12): [`DLMF.Weierstrass.deriv_derivWeierstrassP`](DLMF/Weierstrass/DifferentialEquations.lean#L65) (proved). planned route: identity theorem from 23.3.10.
- [23.3.E13](https://dlmf.nist.gov/23.3.E13): [`DLMF.Weierstrass.deriv_deriv_derivWeierstrassP`](DLMF/Weierstrass/DifferentialEquations.lean#L47) (proved from admitted dependencies).

## [§23.5 Special Lattices](https://dlmf.nist.gov/23.5)

- [23.5.E1](https://dlmf.nist.gov/23.5.E1): [`DLMF.Weierstrass.HalfPeriods.IsRectangular.roots`](DLMF/Weierstrass/SpecialLattices.lean#L247) (proved).
- [23.5.E2](https://dlmf.nist.gov/23.5.E2): [`DLMF.Weierstrass.HalfPeriods.IsLemniscatic.eta`](DLMF/Weierstrass/SpecialLattices.lean#L322) (proved).
- [23.5.E3](https://dlmf.nist.gov/23.5.E3): [`DLMF.Weierstrass.HalfPeriods.IsLemniscatic.roots`](DLMF/Weierstrass/SpecialLattices.lean#L347) (proved).
- [23.5.E4](https://dlmf.nist.gov/23.5.E4): [`DLMF.Weierstrass.HalfPeriods.IsLemniscatic.invariants`](DLMF/Weierstrass/SpecialLattices.lean#L406) (proved).
- [23.5.E5](https://dlmf.nist.gov/23.5.E5): [`DLMF.Weierstrass.HalfPeriods.IsLemniscatic.modulus_sq`](DLMF/Weierstrass/SpecialLattices.lean#L126) (proved from admitted dependencies); [`DLMF.Weierstrass.HalfPeriods.compEllIntKm_lemniscatic`](DLMF/Weierstrass/SpecialLattices.lean#L443) (proved). derived from the admitted root formula 23.5.3.
- [23.5.E6](https://dlmf.nist.gov/23.5.E6): [`DLMF.Weierstrass.HalfPeriods.IsEquianharmonic.eta`](DLMF/Weierstrass/SpecialLattices.lean#L532) (proved).
- [23.5.E7](https://dlmf.nist.gov/23.5.E7): [`DLMF.Weierstrass.HalfPeriods.IsEquianharmonic.roots`](DLMF/Weierstrass/SpecialLattices.lean#L572) (admitted).
- [23.5.E8](https://dlmf.nist.gov/23.5.E8): [`DLMF.Weierstrass.HalfPeriods.IsEquianharmonic.invariants`](DLMF/Weierstrass/SpecialLattices.lean#L580) (admitted).
- [23.5.E9](https://dlmf.nist.gov/23.5.E9): [`DLMF.Weierstrass.HalfPeriods.IsEquianharmonic.modulus_sq`](DLMF/Weierstrass/SpecialLattices.lean#L210) (proved from admitted dependencies); [`DLMF.Weierstrass.HalfPeriods.compEllIntKk_equianharmonic`](DLMF/Weierstrass/SpecialLattices.lean#L647) (admitted). the lattice-side identity is derived from the admitted 23.5.7; the principal-K form compEllIntKk_equianharmonic is admitted.

## [§23.6 Relations to Other Functions](https://dlmf.nist.gov/23.6)

- [23.6.E1](https://dlmf.nist.gov/23.6.E1): [`DLMF.Weierstrass.HalfPeriods.tau`](DLMF/Weierstrass/Basic.lean#L72) (definition); [`DLMF.Weierstrass.HalfPeriods.nome`](DLMF/Weierstrass/Basic.lean#L76) (definition).
- [23.6.E2](https://dlmf.nist.gov/23.6.E2): [`DLMF.Weierstrass.HalfPeriods.e_one_eq_theta`](DLMF/Weierstrass/Relations.lean#L885) (proved).
- [23.6.E3](https://dlmf.nist.gov/23.6.E3): [`DLMF.Weierstrass.HalfPeriods.e_two_eq_theta`](DLMF/Weierstrass/Relations.lean#L892) (proved).
- [23.6.E4](https://dlmf.nist.gov/23.6.E4): [`DLMF.Weierstrass.HalfPeriods.e_three_eq_theta`](DLMF/Weierstrass/Relations.lean#L905) (proved).
- [23.6.E5](https://dlmf.nist.gov/23.6.E5): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_sub_e_one_eq_theta`](DLMF/Weierstrass/Relations.lean#L918) (proved).
- [23.6.E6](https://dlmf.nist.gov/23.6.E6): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_sub_e_two_eq_theta`](DLMF/Weierstrass/Relations.lean#L928) (proved).
- [23.6.E7](https://dlmf.nist.gov/23.6.E7): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_sub_e_three_eq_theta`](DLMF/Weierstrass/Relations.lean#L938) (proved).
- [23.6.E8](https://dlmf.nist.gov/23.6.E8): [`DLMF.Weierstrass.HalfPeriods.eta_one_eq_theta`](DLMF/Weierstrass/Relations.lean#L948) (proved).
- [23.6.E9](https://dlmf.nist.gov/23.6.E9): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_eq_theta`](DLMF/Weierstrass/Relations.lean#L955) (proved).
- [23.6.E10](https://dlmf.nist.gov/23.6.E10): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_ω₁_eq_theta`](DLMF/Weierstrass/Relations.lean#L962) (proved). q^{1/4} read as e^{iπτ/4}.
- [23.6.E11](https://dlmf.nist.gov/23.6.E11): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_ω₂_eq_theta`](DLMF/Weierstrass/Relations.lean#L973) (proved). q^{1/4} read as e^{iπτ/4}.
- [23.6.E12](https://dlmf.nist.gov/23.6.E12): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_ω₃_eq_theta`](DLMF/Weierstrass/Relations.lean#L994) (proved). q^{1/4} read as e^{iπτ/4}.
- [23.6.E13](https://dlmf.nist.gov/23.6.E13): [`DLMF.Weierstrass.HalfPeriods.weierstrassZeta_eq_theta`](DLMF/Weierstrass/Relations.lean#L1015) (proved).
- [23.6.E14](https://dlmf.nist.gov/23.6.E14): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_eq_theta`](DLMF/Weierstrass/Relations.lean#L1024) (proved).
- [23.6.E15](https://dlmf.nist.gov/23.6.E15): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_add_halfPeriod_eq_theta`](DLMF/Weierstrass/Relations.lean#L1038) (proved).
- [23.6.E16](https://dlmf.nist.gov/23.6.E16): [`DLMF.Weierstrass.HalfPeriods.modulus_sq_eq`](DLMF/Weierstrass/Relations.lean#L1143) (proved).
- [23.6.E17](https://dlmf.nist.gov/23.6.E17): [`DLMF.Weierstrass.HalfPeriods.quarterK_sq_eq`](DLMF/Weierstrass/Relations.lean#L1162) (proved); [`DLMF.Weierstrass.HalfPeriods.compEllIntKk_sq_eq`](DLMF/Weierstrass/Relations.lean#L1180) (proved). **Corrected** (DLMF erratum, principal K): with the principal K(k) of §19.2 the identity fails for some generator pairs (for 2ω₁+4ω₃, 2ω₃: K² - ω₁²(e₁-e₃) ≈ 11.0 - 13.7i). It holds for every pair in the lattice form K = (π/2)θ₃²(0|τ) (quarterK_sq_eq); the literal form compEllIntKk_sq_eq assumes τ = iK'/K.
- [23.6.E18](https://dlmf.nist.gov/23.6.E18): [`DLMF.Weierstrass.HalfPeriods.e_one_eq_jacobi`](DLMF/Weierstrass/Relations.lean#L1204) (proved).
- [23.6.E19](https://dlmf.nist.gov/23.6.E19): [`DLMF.Weierstrass.HalfPeriods.e_two_eq_jacobi`](DLMF/Weierstrass/Relations.lean#L1218) (proved).
- [23.6.E20](https://dlmf.nist.gov/23.6.E20): [`DLMF.Weierstrass.HalfPeriods.e_three_eq_jacobi`](DLMF/Weierstrass/Relations.lean#L1232) (proved).
- [23.6.E21](https://dlmf.nist.gov/23.6.E21): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_sub_e_one_eq_cs`](DLMF/Weierstrass/Relations.lean#L1262) (proved).
- [23.6.E22](https://dlmf.nist.gov/23.6.E22): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_sub_e_two_eq_ds`](DLMF/Weierstrass/Relations.lean#L1275) (proved).
- [23.6.E23](https://dlmf.nist.gov/23.6.E23): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_sub_e_three_eq_ns`](DLMF/Weierstrass/Relations.lean#L1288) (proved).
- [23.6.E24](https://dlmf.nist.gov/23.6.E24): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_add_ω₁_sub_e_one_eq_sc`](DLMF/Weierstrass/Relations.lean#L1301) (proved).
- [23.6.E25](https://dlmf.nist.gov/23.6.E25): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_add_ω₂_sub_e_two_eq_sd`](DLMF/Weierstrass/Relations.lean#L1322) (proved).
- [23.6.E26](https://dlmf.nist.gov/23.6.E26): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_add_ω₃_sub_e_three_eq_sn`](DLMF/Weierstrass/Relations.lean#L1354) (proved).
- [23.6.E27](https://dlmf.nist.gov/23.6.E27): [`DLMF.Weierstrass.weierstrassZeta_ns`](DLMF/Weierstrass/Relations.lean#L1378) (admitted).
- [23.6.E28](https://dlmf.nist.gov/23.6.E28): [`DLMF.Weierstrass.weierstrassZeta_ds`](DLMF/Weierstrass/Relations.lean#L1389) (admitted).
- [23.6.E29](https://dlmf.nist.gov/23.6.E29): [`DLMF.Weierstrass.weierstrassZeta_cs`](DLMF/Weierstrass/Relations.lean#L1400) (admitted). **Corrected** (DLMF erratum): the sign is +ζ(2iK'|𝕃₃); the printed - fails (difference about -0.49i at k² = 0.3).
- [23.6.E30](https://dlmf.nist.gov/23.6.E30): [`DLMF.Weierstrass.HalfPeriods.rectangular_integral_one`](DLMF/Weierstrass/Relations.lean#L1421) (admitted).
- [23.6.E31](https://dlmf.nist.gov/23.6.E31): [`DLMF.Weierstrass.HalfPeriods.rectangular_integral_two`](DLMF/Weierstrass/Relations.lean#L1432) (admitted).
- [23.6.E32](https://dlmf.nist.gov/23.6.E32): [`DLMF.Weierstrass.HalfPeriods.rectangular_integral_three`](DLMF/Weierstrass/Relations.lean#L1443) (admitted).
- [23.6.E33](https://dlmf.nist.gov/23.6.E33): [`DLMF.Weierstrass.HalfPeriods.rectangular_integral_four`](DLMF/Weierstrass/Relations.lean#L1454) (admitted).
- [23.6.E34](https://dlmf.nist.gov/23.6.E34): [`DLMF.Weierstrass.HalfPeriods.rectangular_two_ω₁`](DLMF/Weierstrass/Relations.lean#L1464) (admitted).
- [23.6.E35](https://dlmf.nist.gov/23.6.E35): [`DLMF.Weierstrass.HalfPeriods.rectangular_two_ω₃`](DLMF/Weierstrass/Relations.lean#L1475) (admitted).
- [23.6.E36](https://dlmf.nist.gov/23.6.E36): [`DLMF.Weierstrass.weierstrassP_inverse_integral`](DLMF/Weierstrass/Relations.lean#L1489) (admitted).

## [§23.7 Quarter Periods](https://dlmf.nist.gov/23.7)

- [23.7.E1](https://dlmf.nist.gov/23.7.E1): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_half_ω₁`](DLMF/Weierstrass/QuarterPeriods.lean#L54) (proved); [`DLMF.Weierstrass.HalfPeriods.weierstrassP_half_sq`](DLMF/Weierstrass/QuarterPeriods.lean#L140) (proved); [`DLMF.Weierstrass.HalfPeriods.IsRectangular.weierstrassP_half`](DLMF/Weierstrass/QuarterPeriods.lean#L169) (proved). stated in the Jacobian lattice form; the printed square-root forms hold only up to branch for general generators.
- [23.7.E2](https://dlmf.nist.gov/23.7.E2): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_half_ω₂`](DLMF/Weierstrass/QuarterPeriods.lean#L78) (proved); [`DLMF.Weierstrass.HalfPeriods.weierstrassP_half_sq`](DLMF/Weierstrass/QuarterPeriods.lean#L140) (proved); [`DLMF.Weierstrass.HalfPeriods.IsRectangular.weierstrassP_half`](DLMF/Weierstrass/QuarterPeriods.lean#L169) (proved). Jacobian lattice form, as 23.7.E1.
- [23.7.E3](https://dlmf.nist.gov/23.7.E3): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_half_ω₃`](DLMF/Weierstrass/QuarterPeriods.lean#L109) (proved); [`DLMF.Weierstrass.HalfPeriods.weierstrassP_half_sq`](DLMF/Weierstrass/QuarterPeriods.lean#L140) (proved); [`DLMF.Weierstrass.HalfPeriods.IsRectangular.weierstrassP_half`](DLMF/Weierstrass/QuarterPeriods.lean#L169) (proved). Jacobian lattice form, as 23.7.E1.

## [§23.8 Trigonometric Series and Products](https://dlmf.nist.gov/23.8)

- [23.8.E1](https://dlmf.nist.gov/23.8.E1): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_fourier`](DLMF/Weierstrass/Series.lean#L43) (admitted). **Corrected** (DLMF erratum): the condition must be |ℑ(z/ω₁)| < 2ℑτ (the series diverges otherwise: terms 10⁵, 10¹¹, 10²¹ at n = 10, 20, 40).
- [23.8.E2](https://dlmf.nist.gov/23.8.E2): [`DLMF.Weierstrass.HalfPeriods.weierstrassZeta_fourier`](DLMF/Weierstrass/Series.lean#L57) (admitted). **Corrected** (DLMF erratum): condition corrected as in 23.8.E1.
- [23.8.E3](https://dlmf.nist.gov/23.8.E3): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_csc_series`](DLMF/Weierstrass/Series.lean#L73) (admitted).
- [23.8.E4](https://dlmf.nist.gov/23.8.E4): [`DLMF.Weierstrass.HalfPeriods.weierstrassZeta_cot_series`](DLMF/Weierstrass/Series.lean#L81) (admitted). the conditionally convergent sum brackets the terms n and -n (Eisenstein summation).
- [23.8.E5](https://dlmf.nist.gov/23.8.E5): [`DLMF.Weierstrass.HalfPeriods.eta_one_csc_series`](DLMF/Weierstrass/Series.lean#L92) (admitted).
- [23.8.E6](https://dlmf.nist.gov/23.8.E6): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_prod`](DLMF/Weierstrass/Series.lean#L102) (admitted).
- [23.8.E7](https://dlmf.nist.gov/23.8.E7): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_sin_prod`](DLMF/Weierstrass/Series.lean#L116) (admitted).

## [§23.9 Laurent and Other Power Series](https://dlmf.nist.gov/23.9)

- [23.9.E1](https://dlmf.nist.gov/23.9.E1): [`DLMF.Weierstrass.laurentCoeff`](DLMF/Weierstrass/Series.lean#L134) (definition).
- [23.9.E2](https://dlmf.nist.gov/23.9.E2): [`DLMF.Weierstrass.weierstrassP_laurent`](DLMF/Weierstrass/Series.lean#L149) (proved).
- [23.9.E3](https://dlmf.nist.gov/23.9.E3): [`DLMF.Weierstrass.weierstrassZeta_laurent`](DLMF/Weierstrass/Series.lean#L188) (proved).
- [23.9.E4](https://dlmf.nist.gov/23.9.E4): [`DLMF.Weierstrass.laurentCoeff_two`](DLMF/Weierstrass/Series.lean#L139) (proved); [`DLMF.Weierstrass.laurentCoeff_three`](DLMF/Weierstrass/Series.lean#L144) (proved).
- [23.9.E5](https://dlmf.nist.gov/23.9.E5): [`DLMF.Weierstrass.laurentCoeff_recursion`](DLMF/Weierstrass/Series.lean#L354) (proved).
- [23.9.E6](https://dlmf.nist.gov/23.9.E6): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_halfPeriod_expansion`](DLMF/Weierstrass/Series.lean#L478) (proved). stated as a big-O remainder O(t⁸) as t → 0.
- [23.9.E7](https://dlmf.nist.gov/23.9.E7): [`DLMF.Weierstrass.weierstrassSigma_series`](DLMF/Weierstrass/Series.lean#L544) (admitted).
- [23.9.E8](https://dlmf.nist.gov/23.9.E8): [`DLMF.Weierstrass.sigmaCoeff`](DLMF/Weierstrass/Series.lean#L530) (definition). the recursion is a well-founded definition on 2m + 3n.

## [§23.10 Addition Theorems and Other Identities](https://dlmf.nist.gov/23.10)

- [23.10.E1](https://dlmf.nist.gov/23.10.E1): [`DLMF.Weierstrass.weierstrassP_add`](DLMF/Weierstrass/Addition.lean#L541) (proved).
- [23.10.E2](https://dlmf.nist.gov/23.10.E2): [`DLMF.Weierstrass.weierstrassZeta_add`](DLMF/Weierstrass/Addition.lean#L549) (proved).
- [23.10.E3](https://dlmf.nist.gov/23.10.E3): [`DLMF.Weierstrass.weierstrassSigma_add_mul_sub`](DLMF/Weierstrass/Addition.lean#L561) (proved).
- [23.10.E4](https://dlmf.nist.gov/23.10.E4): [`DLMF.Weierstrass.weierstrassSigma_three_term`](DLMF/Weierstrass/Addition.lean#L572) (proved).
- [23.10.E5](https://dlmf.nist.gov/23.10.E5): [`DLMF.Weierstrass.weierstrassP_det_eq_zero`](DLMF/Weierstrass/Addition.lean#L614) (proved).
- [23.10.E6](https://dlmf.nist.gov/23.10.E6): [`DLMF.Weierstrass.weierstrassZeta_sum_sq`](DLMF/Weierstrass/Addition.lean#L639) (proved).
- [23.10.E7](https://dlmf.nist.gov/23.10.E7): [`DLMF.Weierstrass.weierstrassP_two_mul`](DLMF/Weierstrass/Addition.lean#L686) (proved).
- [23.10.E8](https://dlmf.nist.gov/23.10.E8): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_two_mul_sub_e`](DLMF/Weierstrass/Addition.lean#L715) (proved).
- [23.10.E9](https://dlmf.nist.gov/23.10.E9): [`DLMF.Weierstrass.weierstrassZeta_two_mul`](DLMF/Weierstrass/Addition.lean#L744) (proved).
- [23.10.E10](https://dlmf.nist.gov/23.10.E10): [`DLMF.Weierstrass.weierstrassSigma_two_mul`](DLMF/Weierstrass/Addition.lean#L776) (proved).
- [23.10.E11](https://dlmf.nist.gov/23.10.E11): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_nsmul`](DLMF/Weierstrass/Addition.lean#L828) (admitted).
- [23.10.E12](https://dlmf.nist.gov/23.10.E12): [`DLMF.Weierstrass.HalfPeriods.weierstrassZeta_nsmul`](DLMF/Weierstrass/Addition.lean#L835) (admitted).
- [23.10.E13](https://dlmf.nist.gov/23.10.E13): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_nsmul`](DLMF/Weierstrass/Addition.lean#L853) (admitted).
- [23.10.E14](https://dlmf.nist.gov/23.10.E14): [`DLMF.Weierstrass.HalfPeriods.nTupleConst`](DLMF/Weierstrass/Addition.lean#L844) (definition). **Corrected** (DLMF erratum): the product runs over (j, ℓ) ≠ (0, 0); the printed ℓ ≠ j gives relative error 0.71 at n = 2.
- [23.10.E15](https://dlmf.nist.gov/23.10.E15): [`DLMF.Weierstrass.HalfPeriods.nTupleConst_eq`](DLMF/Weierstrass/Addition.lean#L866) (admitted). **Corrected** (DLMF erratum): π² should be π; the corrected ratio is exactly π^{-(n²-1)} for n = 2, 3, 4 on three lattices.
- [23.10.E16](https://dlmf.nist.gov/23.10.E16): [`DLMF.Weierstrass.HalfPeriods.nTupleG`](DLMF/Weierstrass/Addition.lean#L862) (definition).
- [23.10.E17](https://dlmf.nist.gov/23.10.E17): [`DLMF.Weierstrass.weierstrassP_scale`](DLMF/Weierstrass/Addition.lean#L883) (proved).
- [23.10.E18](https://dlmf.nist.gov/23.10.E18): [`DLMF.Weierstrass.weierstrassZeta_scale`](DLMF/Weierstrass/Addition.lean#L895) (proved).
- [23.10.E19](https://dlmf.nist.gov/23.10.E19): [`DLMF.Weierstrass.weierstrassSigma_scale`](DLMF/Weierstrass/Addition.lean#L907) (proved).

## [§23.11 Integral Representations](https://dlmf.nist.gov/23.11)

- [23.11.E1](https://dlmf.nist.gov/23.11.E1): [`DLMF.Weierstrass.integralKernelOne`](DLMF/Weierstrass/Integrals.lean#L35) (definition); [`DLMF.Weierstrass.integralKernelTwo`](DLMF/Weierstrass/Integrals.lean#L40) (definition).
- [23.11.E2](https://dlmf.nist.gov/23.11.E2): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_integral`](DLMF/Weierstrass/Integrals.lean#L49) (admitted). **Corrected** (DLMF erratum): holds only for the normalization 2ω₁ = 1; the convergence condition -1 < ℜ(z+τ) < 1 is insufficient (τ = -0.6+i, z = 0.6+0.1i: integrand 4.5, 68, 7452, 4.4·10⁷ at s = 10, 20, 40, 80); we assume |ℜz| + |ℜτ| < 1, |ℑz| < ℑτ.
- [23.11.E3](https://dlmf.nist.gov/23.11.E3): [`DLMF.Weierstrass.HalfPeriods.weierstrassZeta_integral`](DLMF/Weierstrass/Integrals.lean#L68) (admitted). **Corrected** (DLMF erratum): the integral needs the factor 4 (printed form off by about 0.08 at τ = 0.3+0.9i, z = 0.3+0.2i); same normalization and domain as 23.11.E2.

## [§23.12 Asymptotic Approximations](https://dlmf.nist.gov/23.12)

- [23.12.E1](https://dlmf.nist.gov/23.12.E1): [`DLMF.Weierstrass.HalfPeriods.weierstrassP_isBigO_nome`](DLMF/Weierstrass/Asymptotics.lean#L30) (admitted). q → 0 is τ → i∞ (UpperHalfPlane.atImInfty) with ω₁ fixed.
- [23.12.E2](https://dlmf.nist.gov/23.12.E2): [`DLMF.Weierstrass.HalfPeriods.weierstrassZeta_isBigO_nome`](DLMF/Weierstrass/Asymptotics.lean#L40) (admitted).
- [23.12.E3](https://dlmf.nist.gov/23.12.E3): [`DLMF.Weierstrass.HalfPeriods.weierstrassSigma_isBigO_nome`](DLMF/Weierstrass/Asymptotics.lean#L50) (admitted).
- [23.12.E4](https://dlmf.nist.gov/23.12.E4): [`DLMF.Weierstrass.HalfPeriods.eta_one_isBigO_nome`](DLMF/Weierstrass/Asymptotics.lean#L61) (admitted).

## [§23.13 Zeros](https://dlmf.nist.gov/23.13)


## [§23.14 Integrals](https://dlmf.nist.gov/23.14)

- [23.14.E1](https://dlmf.nist.gov/23.14.E1): [`DLMF.Weierstrass.hasDerivAt_neg_weierstrassZeta`](DLMF/Weierstrass/Integrals.lean#L90) (proved).
- [23.14.E2](https://dlmf.nist.gov/23.14.E2): [`DLMF.Weierstrass.hasDerivAt_weierstrassP_sq_primitive`](DLMF/Weierstrass/Integrals.lean#L108) (proved from admitted dependencies). proved from the admitted 23.3.E12.
- [23.14.E3](https://dlmf.nist.gov/23.14.E3): [`DLMF.Weierstrass.hasDerivAt_weierstrassP_cube_primitive`](DLMF/Weierstrass/Integrals.lean#L122) (proved from admitted dependencies). proved from the admitted 23.3.E12.

## [§23.15 Definitions](https://dlmf.nist.gov/23.15)

- [23.15.E1](https://dlmf.nist.gov/23.15.E1): [`DLMF.Weierstrass.nome_eq_modulus`](DLMF/Weierstrass/ModularFunctions.lean#L51) (proved).
- [23.15.E2](https://dlmf.nist.gov/23.15.E2): [`DLMF.Weierstrass.modulus_eq_theta`](DLMF/Weierstrass/ModularFunctions.lean#L65) (proved from admitted dependencies). proved from the admitted Chapter 22 inversion theorem jacobi_inversion_k.
- [23.15.E3](https://dlmf.nist.gov/23.15.E3): [`DLMF.Weierstrass.mobius`](DLMF/Weierstrass/ModularFunctions.lean#L69) (definition); [`DLMF.Weierstrass.mobius_coe`](DLMF/Weierstrass/ModularFunctions.lean#L81) (proved); Mathlib: [`UpperHalfPlane.coe_specialLinearGroup_apply`](DLMF/Weierstrass/MathlibCoverage.lean#L56) (exact: the SL(2,ℤ) action on ℍ is τ ↦ (aτ+b)/(cτ+d)).
- [23.15.E4](https://dlmf.nist.gov/23.15.E4): [`DLMF.Weierstrass.mobius_det`](DLMF/Weierstrass/ModularFunctions.lean#L75) (proved); Mathlib: [`Matrix.SpecialLinearGroup`](DLMF/Weierstrass/MathlibCoverage.lean#L59) (exact: SL(2,ℤ), integer matrices with ad - bc = 1).
- [23.15.E5](https://dlmf.nist.gov/23.15.E5): [`DLMF.Weierstrass.IsModularFunction`](DLMF/Weierstrass/ModularFunctions.lean#L87) (definition). the level ℓ is encoded as ℓ₂ = 2ℓ with the principal power (cτ+d)^ℓ.
- [23.15.E6](https://dlmf.nist.gov/23.15.E6): [`DLMF.Weierstrass.modularLambda`](DLMF/Weierstrass/ModularFunctions.lean#L111) (definition); [`DLMF.Weierstrass.modularLambda_eq_modulus_sq`](DLMF/Weierstrass/ModularFunctions.lean#L115) (proved). the θ₂⁴ branch of q^{1/4} in DLMF's nome form does not matter.
- [23.15.E7](https://dlmf.nist.gov/23.15.E7): [`DLMF.Weierstrass.kleinJ`](DLMF/Weierstrass/ModularFunctions.lean#L120) (definition). eighth powers remove the q^{1/4} branch of the nome form.
- [23.15.E8](https://dlmf.nist.gov/23.15.E8): [`DLMF.Weierstrass.jacobiThetaOneDerivNullTau_eq`](DLMF/Weierstrass/ModularFunctions.lean#L127) (proved).
- [23.15.E9](https://dlmf.nist.gov/23.15.E9): [`DLMF.Weierstrass.eta_pow_three_eq_theta`](DLMF/Weierstrass/ModularFunctions.lean#L286) (proved); [`DLMF.Weierstrass.eta_pos_of_re_eq_zero`](DLMF/Weierstrass/ModularFunctions.lean#L295) (proved); Mathlib: [`ModularForm.eta`](DLMF/Weierstrass/MathlibCoverage.lean#L61) (definition: η(τ) = e^{2πiτ/24} ∏ (1 - e^{2πi(n+1)τ}); equals DLMF 23.17.8). η³ = θ₁'(0|τ)/2 fixes the cube-root branch as DLMF requires.

## [§23.17 Elementary Properties](https://dlmf.nist.gov/23.17)

- [23.17.E1](https://dlmf.nist.gov/23.17.E1): [`DLMF.Weierstrass.modularLambda_special`](DLMF/Weierstrass/ModularFunctions.lean#L347) (proved).
- [23.17.E2](https://dlmf.nist.gov/23.17.E2): [`DLMF.Weierstrass.kleinJ_special`](DLMF/Weierstrass/ModularFunctions.lean#L401) (proved).
- [23.17.E3](https://dlmf.nist.gov/23.17.E3): [`DLMF.Weierstrass.eta_special`](DLMF/Weierstrass/ModularFunctions.lean#L419) (admitted). values from DLMF, numerically checked.
- [23.17.E4](https://dlmf.nist.gov/23.17.E4): [`DLMF.Weierstrass.modularLambda_isBigO`](DLMF/Weierstrass/ModularFunctions.lean#L429) (admitted).
- [23.17.E5](https://dlmf.nist.gov/23.17.E5): [`DLMF.Weierstrass.kleinJ_isBigO`](DLMF/Weierstrass/ModularFunctions.lean#L437) (admitted).
- [23.17.E6](https://dlmf.nist.gov/23.17.E6): [`DLMF.Weierstrass.eta_hasSum`](DLMF/Weierstrass/ModularFunctions.lean#L446) (proved).
- [23.17.E7](https://dlmf.nist.gov/23.17.E7): [`DLMF.Weierstrass.modularLambda_hasProd`](DLMF/Weierstrass/ModularFunctions.lean#L462) (proved).
- [23.17.E8](https://dlmf.nist.gov/23.17.E8): [`DLMF.Weierstrass.eta_hasProd`](DLMF/Weierstrass/ModularFunctions.lean#L140) (proved); Mathlib: [`ModularForm.eta`](DLMF/Weierstrass/MathlibCoverage.lean#L64) (exact: q^{1/12} ∏ (1 - q^{2n}) with q = e^{iπτ}, q^{1/12} = e^{iπτ/12}); Mathlib: [`ModularForm.eta_ne_zero`](DLMF/Weierstrass/MathlibCoverage.lean#L67) (related: η has no zeros in ℍ). proved directly from Mathlib's definition of η.

## [§23.18 Modular Transformations](https://dlmf.nist.gov/23.18)

- [23.18.E1](https://dlmf.nist.gov/23.18.E1): [`DLMF.Weierstrass.modularLambda_smul`](DLMF/Weierstrass/ModularFunctions.lean#L636) (proved).
- [23.18.E2](https://dlmf.nist.gov/23.18.E2): [`DLMF.Weierstrass.modularLambda_smul`](DLMF/Weierstrass/ModularFunctions.lean#L636) (proved).
- [23.18.E3](https://dlmf.nist.gov/23.18.E3): [`DLMF.Weierstrass.modularLambda_smul_of_even`](DLMF/Weierstrass/ModularFunctions.lean#L259) (proved from admitted dependencies); [`DLMF.Weierstrass.isCuspForm_modularLambda`](DLMF/Weierstrass/ModularFunctions.lean#L670) (proved). the subgroup is the principal congruence subgroup Γ(2).
- [23.18.E4](https://dlmf.nist.gov/23.18.E4): [`DLMF.Weierstrass.kleinJ_smul`](DLMF/Weierstrass/ModularFunctions.lean#L1011) (proved); [`DLMF.Weierstrass.isModularFunction_kleinJ`](DLMF/Weierstrass/ModularFunctions.lean#L1016) (proved). **Corrected** (DLMF terminology): DLMF calls J a modular form, but J has the pole q⁻²/1728 (23.17.5), so it is a modular function in the sense of 23.15(i).
- [23.18.E5](https://dlmf.nist.gov/23.18.E5): [`DLMF.Weierstrass.eta_smul`](DLMF/Weierstrass/ModularFunctions.lean#L763) (admitted); [`DLMF.Weierstrass.isModularFunction_eta`](DLMF/Weierstrass/ModularFunctions.lean#L791) (proved). c > 0; principal square root.
- [23.18.E6](https://dlmf.nist.gov/23.18.E6): [`DLMF.Weierstrass.etaMultiplier`](DLMF/Weierstrass/ModularFunctions.lean#L757) (definition).
- [23.18.E7](https://dlmf.nist.gov/23.18.E7): [`DLMF.Weierstrass.dedekindSum`](DLMF/Weierstrass/ModularFunctions.lean#L751) (definition). follows the V1.0.11 erratum: no coprimality condition on r.

## [§23.19 Interrelations](https://dlmf.nist.gov/23.19)

- [23.19.E1](https://dlmf.nist.gov/23.19.E1): [`DLMF.Weierstrass.modularLambda_eq_eta`](DLMF/Weierstrass/ModularFunctions.lean#L923) (proved).
- [23.19.E2](https://dlmf.nist.gov/23.19.E2): [`DLMF.Weierstrass.kleinJ_eq_modularLambda`](DLMF/Weierstrass/ModularFunctions.lean#L945) (proved).
- [23.19.E3](https://dlmf.nist.gov/23.19.E3): [`DLMF.Weierstrass.kleinJ_eq_invariants`](DLMF/Weierstrass/ModularFunctions.lean#L952) (proved). lattice with generators 1, τ: HalfPeriods.ofTau (1/2) τ.
- [23.19.E4](https://dlmf.nist.gov/23.19.E4): [`DLMF.Weierstrass.latticeDiscriminant_eq_eta`](DLMF/Weierstrass/ModularFunctions.lean#L1034) (proved); Mathlib: [`ModularForm.discriminant`](DLMF/Weierstrass/MathlibCoverage.lean#L69) (normalized: Mathlib's Δ(τ) = η(τ)²⁴, i.e. DLMF's Δ/(2π)¹² for the lattice 1, τ); Mathlib: [`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`](DLMF/Weierstrass/MathlibCoverage.lean#L72) (related: η²⁴ = (E₄³ - E₆²)/1728, the Eisenstein-series form of g₂³ - 27g₃²). lattice with generators 1, τ; Mathlib's discriminant is the normalized η²⁴.

## Analytical prose and exclusions

Section headings and paragraphs that only introduce a displayed equation are listed with the
equations they introduce.

- [23.2.i.p1](https://dlmf.nist.gov/23.2#i.p1): Definition of the lattice 𝕃 generated by 2ω₁, 2ω₃ with ℑ(ω₃/ω₁) > 0: [`DLMF.Weierstrass.HalfPeriods`](DLMF/Weierstrass/Basic.lean#L51) (definition); [`DLMF.Weierstrass.HalfPeriods.lattice`](DLMF/Weierstrass/Basic.lean#L122) (definition); [`DLMF.Weierstrass.HalfPeriods.mem_lattice_iff`](DLMF/Weierstrass/Basic.lean#L124) (proved).
- [23.2.i.p2](https://dlmf.nist.gov/23.2#i.p2): Non-uniqueness of generators: [`DLMF.Weierstrass.HalfPeriods.span_two_ω₂_two_ω₃`](DLMF/Weierstrass/Basic.lean#L139) (proved); [`DLMF.Weierstrass.HalfPeriods.span_two_ω₂_two_ω₁`](DLMF/Weierstrass/Basic.lean#L155) (proved); [`DLMF.Weierstrass.HalfPeriods.generators_iff`](DLMF/Weierstrass/Basic.lean#L195) (proved).
- [23.2.ii.p1](https://dlmf.nist.gov/23.2#ii.p1): Introduces 23.2.E4–E6; covered there.
- [23.2.ii.p2](https://dlmf.nist.gov/23.2#ii.p2): Introduces 23.2.E7–E8 (condition z ∉ 𝕃); covered there.
- [23.2.ii.p3](https://dlmf.nist.gov/23.2#ii.p3): Meromorphy, parity, poles and residues of ℘ and ζ; σ entire and odd with simple zeros at the lattice points: [`DLMF.Weierstrass.weierstrassZeta_neg`](DLMF/Weierstrass/Basic.lean#L302) (proved); [`DLMF.Weierstrass.weierstrassSigma_neg`](DLMF/Weierstrass/Basic.lean#L313) (proved); [`DLMF.Weierstrass.weierstrassSigma_eq_zero_of_mem`](DLMF/Weierstrass/Basic.lean#L323) (proved); [`DLMF.Weierstrass.hasSumLocallyUniformly_weierstrassZeta`](DLMF/Weierstrass/Basic.lean#L332) (proved); [`DLMF.Weierstrass.multipliable_weierstrassSigma`](DLMF/Weierstrass/Basic.lean#L484) (proved); [`DLMF.Weierstrass.differentiableOn_weierstrassZeta`](DLMF/Weierstrass/Basic.lean#L499) (proved); [`DLMF.Weierstrass.differentiable_weierstrassSigma`](DLMF/Weierstrass/Basic.lean#L541) (proved); [`DLMF.Weierstrass.weierstrassSigma_eq_zero_iff`](DLMF/Weierstrass/Basic.lean#L557) (proved); [`DLMF.Weierstrass.deriv_weierstrassSigma_ne_zero`](DLMF/Weierstrass/Basic.lean#L781) (proved); [`DLMF.Weierstrass.analyticAt_weierstrassZeta_sub`](DLMF/Weierstrass/Basic.lean#L615) (proved); [`DLMF.Weierstrass.analyticOnNhd_weierstrassZeta`](DLMF/Weierstrass/Basic.lean#L663) (proved); [`DLMF.Weierstrass.analyticAt_weierstrassP_sub`](DLMF/Weierstrass/Basic.lean#L669) (proved); Mathlib: [`PeriodPair.weierstrassP_neg`](DLMF/Weierstrass/MathlibCoverage.lean#L38); Mathlib: [`PeriodPair.derivWeierstrassP_neg`](DLMF/Weierstrass/MathlibCoverage.lean#L40); Mathlib: [`PeriodPair.meromorphic_weierstrassP`](DLMF/Weierstrass/MathlibCoverage.lean#L42); Mathlib: [`PeriodPair.analyticOnNhd_weierstrassP`](DLMF/Weierstrass/MathlibCoverage.lean#L44); Mathlib: [`PeriodPair.order_weierstrassP`](DLMF/Weierstrass/MathlibCoverage.lean#L46).
- [23.2.iii.p1](https://dlmf.nist.gov/23.2#iii.p1): Periodicity for any pair of generators: 23.2.E9–E10; Mathlib: [`PeriodPair.periodic_weierstrassP`](DLMF/Weierstrass/MathlibCoverage.lean#L34); Mathlib: [`PeriodPair.periodic_derivWeierstrassP`](DLMF/Weierstrass/MathlibCoverage.lean#L36).
- [23.2.iii.p2](https://dlmf.nist.gov/23.2#iii.p2): Introduces 23.2.E11–E14; covered there.
- [23.2.iii.p3](https://dlmf.nist.gov/23.2#iii.p3): Introduces 23.2.E15–E17; covered there.
- [23.2.iii.p4](https://dlmf.nist.gov/23.2#iii.p4): excluded: reference only (Lawden).
- [23.2.i](https://dlmf.nist.gov/23.2.i): [`DLMF.Weierstrass.HalfPeriods.mem_lattice_iff`](DLMF/Weierstrass/Basic.lean#L124) (proved); [`DLMF.Weierstrass.HalfPeriods.span_two_ω₂_two_ω₁`](DLMF/Weierstrass/Basic.lean#L155) (proved); [`DLMF.Weierstrass.HalfPeriods.span_two_ω₂_two_ω₃`](DLMF/Weierstrass/Basic.lean#L139) (proved).
- [23.2.ii](https://dlmf.nist.gov/23.2.ii): [`DLMF.Weierstrass.analyticAt_weierstrassP_sub`](DLMF/Weierstrass/Basic.lean#L669) (proved); [`DLMF.Weierstrass.analyticAt_weierstrassZeta_sub`](DLMF/Weierstrass/Basic.lean#L615) (proved); [`DLMF.Weierstrass.analyticOnNhd_weierstrassZeta`](DLMF/Weierstrass/Basic.lean#L663) (proved); [`DLMF.Weierstrass.deriv_weierstrassSigma_ne_zero`](DLMF/Weierstrass/Basic.lean#L781) (proved); [`DLMF.Weierstrass.differentiableOn_weierstrassZeta`](DLMF/Weierstrass/Basic.lean#L499) (proved); [`DLMF.Weierstrass.differentiable_weierstrassSigma`](DLMF/Weierstrass/Basic.lean#L541) (proved); [`DLMF.Weierstrass.hasSumLocallyUniformly_weierstrassZeta`](DLMF/Weierstrass/Basic.lean#L332) (proved); [`DLMF.Weierstrass.multipliable_weierstrassSigma`](DLMF/Weierstrass/Basic.lean#L484) (proved); [`DLMF.Weierstrass.weierstrassSigma_eq_zero_iff`](DLMF/Weierstrass/Basic.lean#L557) (proved); [`DLMF.Weierstrass.weierstrassSigma_eq_zero_of_mem`](DLMF/Weierstrass/Basic.lean#L323) (proved); [`DLMF.Weierstrass.weierstrassSigma_neg`](DLMF/Weierstrass/Basic.lean#L313) (proved); [`DLMF.Weierstrass.weierstrassZeta_neg`](DLMF/Weierstrass/Basic.lean#L302) (proved); Mathlib: [`PeriodPair.weierstrassP_neg`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.html#PeriodPair.weierstrassP_neg); Mathlib: [`PeriodPair.derivWeierstrassP_neg`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.html#PeriodPair.derivWeierstrassP_neg); Mathlib: [`PeriodPair.meromorphic_weierstrassP`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.html#PeriodPair.meromorphic_weierstrassP); Mathlib: [`PeriodPair.analyticOnNhd_weierstrassP`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.html#PeriodPair.analyticOnNhd_weierstrassP); Mathlib: [`PeriodPair.order_weierstrassP`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.html#PeriodPair.order_weierstrassP).
- [23.3.i.p1](https://dlmf.nist.gov/23.3#i.p1): Introduces 23.3.E1–E2 (Mathlib pointers).
- [23.3.i.p2](https://dlmf.nist.gov/23.3#i.p2): Introduces 23.3.E3–E7; covered there.
- [23.3.i.p3](https://dlmf.nist.gov/23.3#i.p3): Δ ≠ 0, distinct roots, and the unique lattice with given invariants: [`DLMF.Weierstrass.HalfPeriods.e_distinct`](DLMF/Weierstrass/Basic.lean#L1197) (proved); [`DLMF.Weierstrass.HalfPeriods.latticeDiscriminant_ne_zero`](DLMF/Weierstrass/Basic.lean#L710) (proved from admitted dependencies); [`DLMF.Weierstrass.latticeDiscriminant_ne_zero'`](DLMF/Weierstrass/Basic.lean#L1391) (proved); [`DLMF.Weierstrass.exists_periodPair_invariants`](DLMF/Weierstrass/Basic.lean#L1481) (proved); [`DLMF.Weierstrass.lattice_eq_of_invariants_eq`](DLMF/Weierstrass/Basic.lean#L1708) (proved); [`DLMF.Weierstrass.periodPairOfInvariants`](DLMF/Weierstrass/Basic.lean#L1722) (definition); [`DLMF.Weierstrass.weierstrassZetaInvariants`](DLMF/Weierstrass/Basic.lean#L1730) (definition); [`DLMF.Weierstrass.weierstrassSigmaInvariants`](DLMF/Weierstrass/Basic.lean#L1734) (definition); [`DLMF.Weierstrass.exists_entire_weierstrassSigmaInvariants`](DLMF/Weierstrass/Basic.lean#L1770) (admitted); 23.3.E8.
- [23.3.i.p4](https://dlmf.nist.gov/23.3#i.p4): Invariants and root set determined by the lattice, independent of generators: [`DLMF.Weierstrass.HalfPeriods.invariants_roots_eq_of_lattice_eq`](DLMF/Weierstrass/Basic.lean#L1317) (proved); [`DLMF.Weierstrass.HalfPeriods.cubic_eq_mul`](DLMF/Weierstrass/Basic.lean#L676) (proved from admitted dependencies).
- [23.3.i.p5](https://dlmf.nist.gov/23.3#i.p5): Convention that 23.3.E9 applies: definition `HalfPeriods.e`.
- [23.3.ii.p1](https://dlmf.nist.gov/23.3#ii.p1): Introduces 23.3.E10–E13; covered there.
- [23.3.i](https://dlmf.nist.gov/23.3.i): [`DLMF.Weierstrass.HalfPeriods.cubic_eq_mul`](DLMF/Weierstrass/Basic.lean#L1272) (proved); [`DLMF.Weierstrass.HalfPeriods.e_distinct`](DLMF/Weierstrass/Basic.lean#L1197) (proved); [`DLMF.Weierstrass.HalfPeriods.invariants_roots_eq_of_lattice_eq`](DLMF/Weierstrass/Basic.lean#L1317) (proved); [`DLMF.Weierstrass.HalfPeriods.latticeDiscriminant_ne_zero`](DLMF/Weierstrass/Basic.lean#L1306) (proved); [`DLMF.Weierstrass.exists_entire_weierstrassSigmaInvariants`](DLMF/Weierstrass/Basic.lean#L1770) (admitted); [`DLMF.Weierstrass.exists_periodPair_invariants`](DLMF/Weierstrass/Basic.lean#L1481) (proved); [`DLMF.Weierstrass.latticeDiscriminant_ne_zero'`](DLMF/Weierstrass/Basic.lean#L1391) (proved); [`DLMF.Weierstrass.lattice_eq_of_invariants_eq`](DLMF/Weierstrass/Basic.lean#L1708) (proved); [`DLMF.Weierstrass.weierstrassSigmaInvariants`](DLMF/Weierstrass/Basic.lean#L1734) (definition); [`DLMF.Weierstrass.weierstrassZetaInvariants`](DLMF/Weierstrass/Basic.lean#L1730) (definition).
- [23.5.i.p1](https://dlmf.nist.gov/23.5#i.p1): Real values on the real axis iff 𝕃 = conj 𝕃 iff g₂, g₃ real: [`DLMF.Weierstrass.weierstrassP_real_iff`](DLMF/Weierstrass/SpecialLattices.lean#L88) (proved).
- [23.5.ii.p1](https://dlmf.nist.gov/23.5#ii.p1): Rectangular lattice, Δ > 0: [`DLMF.Weierstrass.HalfPeriods.IsRectangular`](DLMF/Weierstrass/SpecialLattices.lean#L169) (definition); [`DLMF.Weierstrass.HalfPeriods.rectangular`](DLMF/Weierstrass/SpecialLattices.lean#L269) (definition); [`DLMF.Weierstrass.HalfPeriods.IsRectangular.discriminant_pos`](DLMF/Weierstrass/SpecialLattices.lean#L229) (proved).
- [23.5.ii.p2](https://dlmf.nist.gov/23.5#ii.p2): Real distinct roots, ordering 23.5.E1: [`DLMF.Weierstrass.HalfPeriods.IsRectangular.e_two_g₃`](DLMF/Weierstrass/SpecialLattices.lean#L260) (admitted); 23.5.E1.
- [23.5.ii.p3](https://dlmf.nist.gov/23.5#ii.p3): Monotonicity of e₁, e₂, e₃ in ℑω₃: [`DLMF.Weierstrass.HalfPeriods.rectangular_roots_monotone`](DLMF/Weierstrass/SpecialLattices.lean#L273) (admitted).
- [23.5.iii.p1](https://dlmf.nist.gov/23.5#iii.p1): Lemniscatic lattice: [`DLMF.Weierstrass.HalfPeriods.IsLemniscatic`](DLMF/Weierstrass/SpecialLattices.lean#L173) (definition); 23.5.E2–E4.
- [23.5.iii.p2](https://dlmf.nist.gov/23.5#iii.p2): τ = i: [`DLMF.Weierstrass.HalfPeriods.IsLemniscatic.tau`](DLMF/Weierstrass/SpecialLattices.lean#L417) (proved); 23.5.E5.
- [23.5.iv.p1](https://dlmf.nist.gov/23.5#iv.p1): Rhombic lattice; the printed condition Δ < 0 is a consequence of the other conditions, not an extra hypothesis: [`DLMF.Weierstrass.HalfPeriods.IsRhombic`](DLMF/Weierstrass/SpecialLattices.lean#L178) (definition); [`DLMF.Weierstrass.HalfPeriods.rhombic`](DLMF/Weierstrass/SpecialLattices.lean#L520) (definition); [`DLMF.Weierstrass.HalfPeriods.IsRhombic.discriminant_neg`](DLMF/Weierstrass/SpecialLattices.lean#L484) (proved).
- [23.5.iv.p2](https://dlmf.nist.gov/23.5#iv.p2): e₁ real, e₃ = conj e₂, sign of e₁ and g₃, pseudo-lemniscatic case, monotonicity: [`DLMF.Weierstrass.HalfPeriods.IsRhombic.roots`](DLMF/Weierstrass/SpecialLattices.lean#L509) (admitted); [`DLMF.Weierstrass.HalfPeriods.rhombic_e_one_monotone`](DLMF/Weierstrass/SpecialLattices.lean#L524) (admitted).
- [23.5.v.p1](https://dlmf.nist.gov/23.5#v.p1): Equianharmonic lattice: [`DLMF.Weierstrass.HalfPeriods.IsEquianharmonic`](DLMF/Weierstrass/SpecialLattices.lean#L182) (definition); 23.5.E6–E8.
- [23.5.v.p2](https://dlmf.nist.gov/23.5#v.p2): Introduces 23.5.E6–E8.
- [23.5.v.p3](https://dlmf.nist.gov/23.5#v.p3): τ = e^{iπ/3}: [`DLMF.Weierstrass.HalfPeriods.IsEquianharmonic.tau`](DLMF/Weierstrass/SpecialLattices.lean#L586) (proved); 23.5.E9.
- [23.5.i](https://dlmf.nist.gov/23.5.i): [`DLMF.Weierstrass.weierstrassP_real_iff`](DLMF/Weierstrass/SpecialLattices.lean#L88) (proved).
- [23.5.ii](https://dlmf.nist.gov/23.5.ii): [`DLMF.Weierstrass.HalfPeriods.IsRectangular.discriminant_pos`](DLMF/Weierstrass/SpecialLattices.lean#L229) (proved); [`DLMF.Weierstrass.HalfPeriods.IsRectangular.e_two_g₃`](DLMF/Weierstrass/SpecialLattices.lean#L260) (admitted); [`DLMF.Weierstrass.HalfPeriods.rectangular_roots_monotone`](DLMF/Weierstrass/SpecialLattices.lean#L273) (admitted).
- [23.5.iii](https://dlmf.nist.gov/23.5.iii): [`DLMF.Weierstrass.HalfPeriods.IsLemniscatic.tau`](DLMF/Weierstrass/SpecialLattices.lean#L417) (proved).
- [23.5.iv](https://dlmf.nist.gov/23.5.iv): [`DLMF.Weierstrass.HalfPeriods.IsRhombic.discriminant_neg`](DLMF/Weierstrass/SpecialLattices.lean#L484) (proved); [`DLMF.Weierstrass.HalfPeriods.IsRhombic.roots`](DLMF/Weierstrass/SpecialLattices.lean#L509) (admitted); [`DLMF.Weierstrass.HalfPeriods.rhombic_e_one_monotone`](DLMF/Weierstrass/SpecialLattices.lean#L524) (admitted).
- [23.5.v](https://dlmf.nist.gov/23.5.v): [`DLMF.Weierstrass.HalfPeriods.IsEquianharmonic.tau`](DLMF/Weierstrass/SpecialLattices.lean#L586) (proved).
- [23.6.i.p1](https://dlmf.nist.gov/23.6#i.p1): Convention: arbitrary generators, roots by 23.3.E9; built into the statements of 23.6.E1–E15.
- [23.6.i.p2](https://dlmf.nist.gov/23.6#i.p2): excluded: reference only (Lawden).
- [23.6.ii.p1](https://dlmf.nist.gov/23.6#ii.p1): Convention for 23.6.E16–E26; built into the statements.
- [23.6.ii.p2](https://dlmf.nist.gov/23.6#ii.p2): Lattices 𝕃₁, 𝕃₂, 𝕃₃ of the modulus k for 23.6.E27–E29; built into those statements.
- [23.6.ii.p3](https://dlmf.nist.gov/23.6#ii.p3): excluded: reference only (the nine other Jacobi functions via Table 22.4.3 are not stated).
- [23.6.ii.p4](https://dlmf.nist.gov/23.6#ii.p4): excluded: reference only (Lawden).
- [23.6.iii.p1](https://dlmf.nist.gov/23.6#iii.p1): excluded: reference only (Lawden).
- [23.6.Px1.p1](https://dlmf.nist.gov/23.6#Px1.p1): Rectangle perimeter with t = ℘(z) real; introduces 23.6.E30–E35: [`DLMF.Weierstrass.HalfPeriods.eRe`](DLMF/Weierstrass/Relations.lean#L1419) (definition).
- [23.6.Px1.p2](https://dlmf.nist.gov/23.6#Px1.p2): excluded: reference only.
- [23.6.Px1.p3](https://dlmf.nist.gov/23.6#Px1.p3): excluded: reference only (§19.25(vi)).
- [23.6.Px2.p1](https://dlmf.nist.gov/23.6#Px2.p1): Introduces 23.6.E36; covered there.
- [23.7.p1](https://dlmf.nist.gov/23.7#p1): Introduces 23.7.E1–E3; covered there.
- [23.8.i.p1](https://dlmf.nist.gov/23.8#i.p1): Hypotheses of 23.8.E1–E2 (corrected); covered there.
- [23.8.ii.p1](https://dlmf.nist.gov/23.8#ii.p1): Introduces 23.8.E3–E5.
- [23.8.iii.p1](https://dlmf.nist.gov/23.8#iii.p1): Introduces 23.8.E6–E7.
- [23.9.p1](https://dlmf.nist.gov/23.9#p1): Nearest lattice point z₀ and the disk |z| < |z₀| of 23.9.E2–E3; built into those statements.
- [23.9.p2](https://dlmf.nist.gov/23.9#p2): Introduces 23.9.E6.
- [23.9.p3](https://dlmf.nist.gov/23.9#p3): Introduces 23.9.E7–E8.
- [23.10.i.p1](https://dlmf.nist.gov/23.10#i.p1): Introduces 23.10.E1–E4.
- [23.10.i.p2](https://dlmf.nist.gov/23.10#i.p2): Hypothesis u + v + w = 0 of 23.10.E5–E6; built into those statements.
- [23.10.ii.p1](https://dlmf.nist.gov/23.10#ii.p1): Introduces 23.10.E7–E10.
- [23.10.iii.p1](https://dlmf.nist.gov/23.10#iii.p1): Introduces 23.10.E11–E14 (n ≥ 2); definition [`DLMF.Weierstrass.HalfPeriods.divisionPoint`](DLMF/Weierstrass/Addition.lean#L826) (definition).
- [23.10.iii.p2](https://dlmf.nist.gov/23.10#iii.p2): Introduces 23.10.E15.
- [23.10.iii.p3](https://dlmf.nist.gov/23.10#iii.p3): Introduces 23.10.E16.
- [23.10.iv.p1](https://dlmf.nist.gov/23.10#iv.p1): Homogeneity for c ≠ 0, 23.10.E17–E19; also the scaling of the invariants: [`DLMF.Weierstrass.scalePeriodPair`](DLMF/Weierstrass/Basic.lean#L1402) (definition); [`DLMF.Weierstrass.invariants_scale`](DLMF/Weierstrass/Basic.lean#L1434) (proved).
- [23.10.iv.p2](https://dlmf.nist.gov/23.10#iv.p2): excluded: reference only (Lawden, Apostol).
- [23.10.iv](https://dlmf.nist.gov/23.10.iv): [`DLMF.Weierstrass.invariants_scale`](DLMF/Weierstrass/Basic.lean#L1434) (proved).
- [23.11.p1](https://dlmf.nist.gov/23.11#p1): τ = ω₃/ω₁ and the kernels 23.11.E1.
- [23.11.p2](https://dlmf.nist.gov/23.11#p2): Introduces 23.11.E2–E3.
- [23.12.p1](https://dlmf.nist.gov/23.12#p1): q → 0 with ω₁ and z fixed: τ → i∞ (`UpperHalfPlane.atImInfty`); built into 23.12.E1–E4.
- [23.13.p1](https://dlmf.nist.gov/23.13#p1): excluded: reference only (Eichler and Zagier); no formula.
- [23.14.p1](https://dlmf.nist.gov/23.14#p1): Introduces 23.14.E1–E3.
- [23.14.p2](https://dlmf.nist.gov/23.14#p2): excluded: reference only (integral tables).
- [23.15.i.p1](https://dlmf.nist.gov/23.15#i.p1): Notation k, k′, q = e^{iπτ}: 23.15.E1–E2.
- [23.15.i.p2](https://dlmf.nist.gov/23.15#i.p2): SL(2, ℤ) and bilinear transformations: [`DLMF.Weierstrass.mobius`](DLMF/Weierstrass/ModularFunctions.lean#L69) (definition); [`DLMF.Weierstrass.mobius_coe`](DLMF/Weierstrass/ModularFunctions.lean#L81) (proved); Mathlib: [`UpperHalfPlane.coe_specialLinearGroup_apply`](DLMF/Weierstrass/MathlibCoverage.lean#L56); Mathlib: [`Matrix.SpecialLinearGroup`](DLMF/Weierstrass/MathlibCoverage.lean#L59).
- [23.15.i.p3](https://dlmf.nist.gov/23.15#i.p3): Modular function, level, modular form, cusp form: [`DLMF.Weierstrass.IsModularFunction`](DLMF/Weierstrass/ModularFunctions.lean#L87) (definition); [`DLMF.Weierstrass.IsModularForm`](DLMF/Weierstrass/ModularFunctions.lean#L96) (definition); [`DLMF.Weierstrass.IsCuspForm`](DLMF/Weierstrass/ModularFunctions.lean#L103) (definition).
- [23.15.Px1.p1](https://dlmf.nist.gov/23.15#Px1.p1): Heading for 23.15.E6.
- [23.15.Px2.p1](https://dlmf.nist.gov/23.15#Px2.p1): Heading for 23.15.E7–E8.
- [23.15.Px3.p1](https://dlmf.nist.gov/23.15#Px3.p1): Heading for 23.15.E9; the cube-root branch statement (real and positive on the imaginary axis): [`DLMF.Weierstrass.eta_pos_of_re_eq_zero`](DLMF/Weierstrass/ModularFunctions.lean#L295) (proved).
- [23.15.i](https://dlmf.nist.gov/23.15.i): [`DLMF.Weierstrass.IsCuspForm`](DLMF/Weierstrass/ModularFunctions.lean#L103) (definition); [`DLMF.Weierstrass.IsModularForm`](DLMF/Weierstrass/ModularFunctions.lean#L96) (definition).
- [23.17.i.p1](https://dlmf.nist.gov/23.17#i.p1): Introduces 23.17.E1–E3.
- [23.17.i.p2](https://dlmf.nist.gov/23.17#i.p2): excluded: reference only (Cohen).
- [23.17.ii.p1](https://dlmf.nist.gov/23.17#ii.p1): Condition |q| < 1 for 23.17.E4–E6; formalized as big-O at τ → i∞ (E4–E5) and HasSum for ℑτ > 0 (E6).
- [23.17.ii.p2](https://dlmf.nist.gov/23.17#ii.p2): excluded: reference only (higher coefficients of 1728J; numerical tables).
- [23.17.iii.p1](https://dlmf.nist.gov/23.17#iii.p1): Introduces 23.17.E7–E8.
- [23.18.Px1.p1](https://dlmf.nist.gov/23.18#Px1.p1): Introduces 23.18.E1–E3; the cusp-form statement after 23.18.E3: [`DLMF.Weierstrass.isCuspForm_modularLambda`](DLMF/Weierstrass/ModularFunctions.lean#L670) (proved).
- [23.18.Px2.p1](https://dlmf.nist.gov/23.18#Px2.p1): 23.18.E4 and "J is a modular form of level zero": [`DLMF.Weierstrass.isModularFunction_kleinJ`](DLMF/Weierstrass/ModularFunctions.lean#L1016) (proved) (modular function; see the terminology note at 23.18.E4).
- [23.18.Px3.p1](https://dlmf.nist.gov/23.18#Px3.p1): 23.18.E5–E7 and "η is of level 1/2": [`DLMF.Weierstrass.isModularFunction_eta`](DLMF/Weierstrass/ModularFunctions.lean#L791) (proved).
- [23.19.p1](https://dlmf.nist.gov/23.19#p1): Introduces 23.19.E1–E3 (lattice with generators 1, τ).
- [23.19.p2](https://dlmf.nist.gov/23.19#p2): Introduces 23.19.E4.

### Excluded sections

- [§23.1](https://dlmf.nist.gov/23.1): notation; no mathematical content.
- [§23.4](https://dlmf.nist.gov/23.4), [§23.16](https://dlmf.nist.gov/23.16): excluded: graphics.
- [§23.20](https://dlmf.nist.gov/23.20): excluded: application. Pure-mathematics content for a later
  round: 23.20.E1–E2 (Weierstrass form of an elliptic curve) and 23.20.ii.p2 (parametrization
  x = ℘(z; g₂, g₃), 2y = ℘'(z; g₂, g₃) with g₂ = -4a, g₃ = -4b, P(z₁) + P(z₂) = P(z₁ + z₂));
  23.20.ii.p3 with 23.20.E3–E4 (chord–tangent addition law); 23.20.ii.p4 (real components
  according to the sign of 4a³ + 27b²); 23.20.ii.p5 (Nagell–Lutz and Mazur on torsion; Mordell);
  23.20.i (conformal mapping of rectangles by ℘, Px1.p1, Px2.p1, Px2.p2); 23.20.iv.p1 with
  23.20.E5–E8 (modular equations of degrees 2, 3, 5, 7 for λ). References only: 23.20.Px2.p3,
  Px2.p4, ii.p6, iii.p1, iv.p2, v.p1.
- [§23.21](https://dlmf.nist.gov/23.21): excluded: application. Pure-mathematics content:
  23.21.E1–E3 (ellipsoidal coordinates and the Laplacian) and 23.21.E4–E5 (the same in terms of
  ℘(u), ℘(v), ℘(w)). Physical discussion and references only: 23.21.i.p1, ii.p1, iii.p3, iv.p1,
  I1.i1.p1–I1.i3.p1.
- [§23.22](https://dlmf.nist.gov/23.22), [§23.23](https://dlmf.nist.gov/23.23),
  [§23.24](https://dlmf.nist.gov/23.24): excluded: computation, numerical tables and software.

## Validation

`lake build DLMF.Weierstrass` succeeds, and strict checks with `autoImplicit=false` and
`relaxedAutoImplicit=false` pass for every file of the area. No definition or helper lemma is
admitted, and there are no axioms or `native_decide`. `#print axioms` over all proved tagged
declarations reports only `propext`, `Classical.choice` and `Quot.sound`, plus `sorryAx` for the
15 declarations marked "proved from admitted dependencies".
