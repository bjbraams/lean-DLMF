# DLMF Chapter 21 acquisition: Multidimensional Theta Functions

This acquisition covers mathematical definitions, numbered formulas and analytical
assertions in prose from [DLMF Chapter 21](https://dlmf.nist.gov/21), version 1.2.8,
checked on 2026-10-25. The scope is §§21.1–21.6. Graphics (§21.4 figures), the purely
numerical period matrix 21.4.E1, applications (§§21.7–21.9) and computation
(§§21.10–21.11) are excluded; the exact matrices 21.4.E2 and 21.4.E3 are retained.
Of the 38 numbered equations in §§21.2–21.6, 37 are in scope and all 37 are covered;
21.4.E1 is excluded as numerical. The application equations 21.7.E1–E17 and 21.9.E1–E4
(21 in all) are excluded, and their purely mathematical theorems are listed below.

The entry point is [DLMF/RiemannTheta.lean](DLMF/RiemannTheta.lean), a new area
with five modules: [Basic](DLMF/RiemannTheta/Basic.lean) (Siegel space, θ, θ with
characteristics, convergence and analyticity, reductions to Jacobi theta),
[Symmetry](DLMF/RiemannTheta/Symmetry.lean) (§21.3),
[Modular](DLMF/RiemannTheta/Modular.lean) (§21.5),
[Products](DLMF/RiemannTheta/Products.lean) (§21.6) and
[MathlibCoverage](DLMF/RiemannTheta/MathlibCoverage.lean) with 13 `dlmf_upstream`
pointers. Neither Mathlib nor TauCeti has the Siegel upper half-space or a
multivariable theta function; their genus-one theta `jacobiTheta₂` is the g = 1 case.
The acquisition has **10 direct admissions** (Basic 1, Symmetry 1, Modular 6,
Products 2). Proved results include absolute and locally uniform convergence,
analyticity in each variable, boundedness of the scaled function, all of §21.3, the
unimodular and integer-shift modular formulas 21.5.E5–E7, the genus-one inversion,
the addition formula 21.6.E8 and the four-product formulas 21.6.E6 and 21.6.E7.

## Domains, conventions and source corrections

- The index set is an arbitrary `Fintype ι` (g = card ι), and z ∈ ι → ℂ. The Siegel
  upper half-space `siegelUpperHalfSpace ι` is the set of Ω with Ωᵀ = Ω and Im Ω
  positive definite (`Matrix.PosDef`). The series `riemannTheta z Ω` is a `tsum` over
  ι → ℤ and is defined for all Ω; theorems carry the Siegel hypothesis. The
  convergence result `tendstoLocallyUniformlyOn_riemannTheta` holds on the larger open
  set where only the quadratic form of Im Ω is positive (stronger than DLMF).
- Characteristics α, β are real vectors ι → ℝ; DLMF's convention α, β ∈ [0,1)
  (21.3.ii) is not imposed, since the formulas hold without it.
- `symplecticJ` is DLMF's J_{2g}; Mathlib's `Matrix.J` is its negative. The predicate
  `IsSymplectic` is bridged to `Matrix.symplecticGroup` by
  `isSymplectic_iff_mem_symplecticGroup`.
- 21.2.E6 needs Ω symmetric (it is stated for Ω in the Siegel space).
- 21.5.E5 needs A invertible over ℤ (A ∈ GL_g(ℤ)), not only det A ≠ 0.
- **Erratum, 21.5.E4.** As printed for every symplectic Γ it is false. For
  Γ = [[I, B], [0, I]] with B = [[1, 3], [3, −1]] (odd diagonal) the ratio
  θ(z|Ω+B)/θ(z|Ω) depends on z (numerical check, g = 2). The formula holds on the theta
  group, where diag(CDᵀ) and diag(ABᵀ) are even; the general case is 21.5.E9 with
  α = β = 0. The acquired `riemannTheta_modular` assumes the theta-group condition, uses a
  continuous branch of √det(CΩ+D) on the Siegel space, and asserts an eighth root of
  unity ξ.
- **Erratum, 21.5.E8.** The principal branch is wrong for g ≥ 3. With Ω = τI₃,
  τ = −1.1√3 + i, the ratio equals minus the principal square root of det(−iΩ). It
  agrees with the product of the eigenvalue roots, that is, with the continuous branch
  equal to 1 at Ω = iI. `riemannTheta_inversion` uses that branch,
  `riemannTheta_inversion_principal` records the principal-value form for g ≤ 2, and
  `riemannTheta_inversion_fin_one` proves g = 1.
- 21.5.E9: the sign of the square root is absorbed into κ, which is independent of z
  and Ω; a continuous branch is used.
- **21.6.E3/E4: representatives and a typo.** DLMF 21.6.1 defines 𝒦 as ℤ^{g×h}T modulo
  ℤ^{g×h}T ∩ ℤ^{g×h}, so its representatives lie in ℤ^{g×h}T; the predicate
  `IsRiemannKRepresentatives` encodes this. This is a formalization note, not an erratum:
  with arbitrary lifts modulo integer matrices the identity fails (g = 1,
  T = [[3/5, 4/5], [4/5, −3/5]]). The genuine typo is in 21.6.E4: c_j, d_j are
  g-dimensional (characteristics of a genus-g theta function), not h-dimensional as printed.
  Both points were confirmed by an independent numerical check (2026-10-25).
- 21.3.E6 is proved in a stronger form (stronger than DLMF): for all integer vectors
  a, b with α = a/2 and β = b/2, the factor being (−1)^{a·b}.
- Numerically verified without correction: 21.2.E3, E4, E6, E8–E12, 21.3.E1–E6,
  21.5.E5–E7, 21.5.E9 (κ constant), 21.6.E6–E8.

## Numbered formulas and exact matrices

## [§21.1 Special Notation](https://dlmf.nist.gov/21.1)

- [21.1](https://dlmf.nist.gov/21.1): [`DLMF.RiemannTheta.siegelUpperHalfSpace`](DLMF/RiemannTheta/Basic.lean#L51) (definition). Riemann matrix: complex symmetric with strictly positive definite imaginary part.
- [21.1](https://dlmf.nist.gov/21.1): [`DLMF.RiemannTheta.symplecticJ`](DLMF/RiemannTheta/Modular.lean#L54) (definition). J_{2g}.
- [21.1](https://dlmf.nist.gov/21.1): [`DLMF.RiemannTheta.riemannThetaBig`](DLMF/RiemannTheta/Basic.lean#L87) (definition). Θ(φ|B) = θ(φ/(2πi)|B/(2πi)); the series form is riemannThetaBig_eq_tsum.
- [21.1](https://dlmf.nist.gov/21.1): [`DLMF.RiemannTheta.riemannThetaBig_eq_tsum`](DLMF/RiemannTheta/Basic.lean#L514) (proved). Series form of Θ(φ|B).

## [§21.2 Definitions](https://dlmf.nist.gov/21.2)

- [21.2.E1](https://dlmf.nist.gov/21.2.E1): [`DLMF.RiemannTheta.riemannTheta`](DLMF/RiemannTheta/Basic.lean#L62) (definition); [`DLMF.RiemannTheta.hasSum_riemannTheta`](DLMF/RiemannTheta/Basic.lean#L297) (proved); Mathlib: [`jacobiTheta₂`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂).
- [21.2.E1](https://dlmf.nist.gov/21.2.E1): [`DLMF.RiemannTheta.hasSum_riemannTheta`](DLMF/RiemannTheta/Basic.lean#L297) (proved); [`DLMF.RiemannTheta.riemannTheta`](DLMF/RiemannTheta/Basic.lean#L62) (definition); Mathlib: [`jacobiTheta₂`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂).
- [21.2.E2](https://dlmf.nist.gov/21.2.E2): [`DLMF.RiemannTheta.riemannThetaScaled`](DLMF/RiemannTheta/Basic.lean#L80) (definition).
- [21.2.E3](https://dlmf.nist.gov/21.2.E3): [`DLMF.RiemannTheta.riemannMatrixExample`](DLMF/RiemannTheta/Basic.lean#L533) (definition). The example Riemann matrix; [`DLMF.RiemannTheta.riemannMatrixExample_mem`](DLMF/RiemannTheta/Basic.lean#L546) (proved); [`DLMF.RiemannTheta.riemannTheta_example`](DLMF/RiemannTheta/Basic.lean#L566) (proved).
- [21.2.E3](https://dlmf.nist.gov/21.2.E3): [`DLMF.RiemannTheta.riemannMatrixExample_mem`](DLMF/RiemannTheta/Basic.lean#L546) (proved). The example matrix lies in the Siegel upper half-space; [`DLMF.RiemannTheta.riemannTheta_example`](DLMF/RiemannTheta/Basic.lean#L566) (proved).
- [21.2.E3](https://dlmf.nist.gov/21.2.E3): [`DLMF.RiemannTheta.riemannTheta_example`](DLMF/RiemannTheta/Basic.lean#L566) (proved); [`DLMF.RiemannTheta.riemannMatrixExample`](DLMF/RiemannTheta/Basic.lean#L533) (definition); [`DLMF.RiemannTheta.riemannMatrixExample_mem`](DLMF/RiemannTheta/Basic.lean#L546) (proved).
- [21.2.E4](https://dlmf.nist.gov/21.2.E4): [`DLMF.RiemannTheta.riemannThetaScaled_example`](DLMF/RiemannTheta/Basic.lean#L580) (proved).
- [21.2.E5](https://dlmf.nist.gov/21.2.E5): [`DLMF.RiemannTheta.riemannThetaChar`](DLMF/RiemannTheta/Basic.lean#L75) (definition).
- [21.2.E6](https://dlmf.nist.gov/21.2.E6): [`DLMF.RiemannTheta.riemannThetaChar_eq`](DLMF/RiemannTheta/Basic.lean#L656) (proved). **Corrected** (hypothesis): needs Ω symmetric (Ωᵀ = Ω), used to swap n·Ω·α = α·Ω·n.
- [21.2.E7](https://dlmf.nist.gov/21.2.E7): [`DLMF.RiemannTheta.riemannThetaChar_zero`](DLMF/RiemannTheta/Basic.lean#L668) (proved).
- [21.2.E8](https://dlmf.nist.gov/21.2.E8): [`DLMF.RiemannTheta.riemannTheta_fin_one`](DLMF/RiemannTheta/Basic.lean#L735) (proved).
- [21.2.E9](https://dlmf.nist.gov/21.2.E9): [`DLMF.RiemannTheta.jacobiThetaOneTau_eq_riemannThetaChar`](DLMF/RiemannTheta/Basic.lean#L759) (proved).
- [21.2.E10](https://dlmf.nist.gov/21.2.E10): [`DLMF.RiemannTheta.jacobiThetaTwoTau_eq_riemannThetaChar`](DLMF/RiemannTheta/Basic.lean#L771) (proved).
- [21.2.E11](https://dlmf.nist.gov/21.2.E11): [`DLMF.RiemannTheta.jacobiThetaThreeTau_eq_riemannThetaChar`](DLMF/RiemannTheta/Basic.lean#L783) (proved).
- [21.2.E12](https://dlmf.nist.gov/21.2.E12): [`DLMF.RiemannTheta.jacobiThetaFourTau_eq_riemannThetaChar`](DLMF/RiemannTheta/Basic.lean#L790) (proved).
- [21.2.i](https://dlmf.nist.gov/21.2#i): [`DLMF.RiemannTheta.summable_norm_riemannThetaTerm`](DLMF/RiemannTheta/Basic.lean#L290) (proved). Absolute convergence of the g-tuple Fourier series.
- [21.2.i](https://dlmf.nist.gov/21.2#i): [`DLMF.RiemannTheta.tendstoLocallyUniformlyOn_riemannTheta`](DLMF/RiemannTheta/Basic.lean#L303) (proved). Stronger than DLMF: locally uniform where the imaginary quadratic form is positive.
- [21.2.i](https://dlmf.nist.gov/21.2#i): [`DLMF.RiemannTheta.tendstoUniformlyOn_riemannTheta`](DLMF/RiemannTheta/Basic.lean#L315) (proved). Uniform convergence on compact sets of the z and Ω spaces.
- [21.2.i](https://dlmf.nist.gov/21.2#i): [`DLMF.RiemannTheta.continuousOn_riemannTheta`](DLMF/RiemannTheta/Basic.lean#L330) (proved). Continuity of the locally uniform limit.
- [21.2.i](https://dlmf.nist.gov/21.2#i): [`DLMF.RiemannTheta.differentiableAt_riemannTheta_update`](DLMF/RiemannTheta/Basic.lean#L351) (proved). Analytic in each element of z.
- [21.2.i](https://dlmf.nist.gov/21.2#i): [`DLMF.RiemannTheta.differentiableAt_riemannTheta_entry`](DLMF/RiemannTheta/Basic.lean#L368) (proved). Analytic in each element of Ω.
- [21.2.i](https://dlmf.nist.gov/21.2#i): [`DLMF.RiemannTheta.riemannThetaScaled_bounded`](DLMF/RiemannTheta/Basic.lean#L455) (proved). The scaled theta function is bounded in z.
- [21.2.i](https://dlmf.nist.gov/21.2#i): [`DLMF.RiemannTheta.not_differentiable_riemannThetaScaled`](DLMF/RiemannTheta/Basic.lean#L506) (admitted). The scaled theta function is nonanalytic in z.
- [21.2.ii](https://dlmf.nist.gov/21.2#ii): [`DLMF.RiemannTheta.summable_norm_riemannThetaCharTerm`](DLMF/RiemannTheta/Basic.lean#L676) (proved). Absolute convergence of the series with characteristics.
- [21.2.ii](https://dlmf.nist.gov/21.2#ii): [`DLMF.RiemannTheta.halfPeriodCharacteristics`](DLMF/RiemannTheta/Basic.lean#L684) (definition). Half-period characteristics.
- [21.2.ii](https://dlmf.nist.gov/21.2#ii): [`DLMF.RiemannTheta.ncard_halfPeriodCharacteristics`](DLMF/RiemannTheta/Basic.lean#L689) (proved). There are 2^(2g) half-period characteristics.

## [§21.3 Symmetry Properties and Quasi-Periodicity](https://dlmf.nist.gov/21.3)

- [21.3.E1](https://dlmf.nist.gov/21.3.E1): [`DLMF.RiemannTheta.riemannTheta_neg`](DLMF/RiemannTheta/Symmetry.lean#L51) (proved); Mathlib: [`jacobiTheta₂_neg_left`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂_neg_left).
- [21.3.E2](https://dlmf.nist.gov/21.3.E2): [`DLMF.RiemannTheta.riemannTheta_add_int`](DLMF/RiemannTheta/Symmetry.lean#L60) (proved); Mathlib: [`jacobiTheta₂_add_left`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂_add_left).
- [21.3.E3](https://dlmf.nist.gov/21.3.E3): [`DLMF.RiemannTheta.riemannTheta_add_lattice`](DLMF/RiemannTheta/Symmetry.lean#L71) (proved); Mathlib: [`jacobiTheta₂_add_left'`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂_add_left').
- [21.3.E4](https://dlmf.nist.gov/21.3.E4): [`DLMF.RiemannTheta.riemannThetaChar_add_int`](DLMF/RiemannTheta/Symmetry.lean#L119) (proved).
- [21.3.E5](https://dlmf.nist.gov/21.3.E5): [`DLMF.RiemannTheta.riemannThetaChar_add_lattice`](DLMF/RiemannTheta/Symmetry.lean#L146) (proved).
- [21.3.E6](https://dlmf.nist.gov/21.3.E6): [`DLMF.RiemannTheta.riemannThetaChar_neg_half`](DLMF/RiemannTheta/Symmetry.lean#L186) (proved). Stronger than DLMF: all integer a, b with α = a/2, β = b/2.
- [21.3.i](https://dlmf.nist.gov/21.3#i): [`DLMF.RiemannTheta.riemannThetaPeriodLattice`](DLMF/RiemannTheta/Symmetry.lean#L100) (definition). The period lattice of the Riemann theta function.
- [21.3.i](https://dlmf.nist.gov/21.3#i): [`DLMF.RiemannTheta.eq_const_mul_riemannTheta_of_quasiPeriodic`](DLMF/RiemannTheta/Symmetry.lean#L106) (admitted). Quasi-periodicity determines θ up to a constant factor.

## [§21.4 Graphics](https://dlmf.nist.gov/21.4)

- [21.4.E1](https://dlmf.nist.gov/21.4.E1): excluded: numerical (decimal entries of a period matrix used for the plots).
- [21.4.E2](https://dlmf.nist.gov/21.4.E2): [`DLMF.RiemannTheta.riemannMatrixExample_eq_omegaOne`](DLMF/RiemannTheta/Basic.lean#L537) (proved).
- [21.4.E3](https://dlmf.nist.gov/21.4.E3): [`DLMF.RiemannTheta.riemannMatrixOmegaTwo`](DLMF/RiemannTheta/Basic.lean#L602) (definition); [`DLMF.RiemannTheta.riemannMatrixOmegaTwo_mem`](DLMF/RiemannTheta/Basic.lean#L609) (proved).
- [21.4.E3](https://dlmf.nist.gov/21.4.E3): [`DLMF.RiemannTheta.riemannMatrixOmegaTwo_mem`](DLMF/RiemannTheta/Basic.lean#L609) (proved). Ω₂ lies in the Siegel upper half-space.

## [§21.5 Modular Transformations](https://dlmf.nist.gov/21.5)

- [21.5.E1](https://dlmf.nist.gov/21.5.E1): [`DLMF.RiemannTheta.IsSymplecticBlocks`](DLMF/RiemannTheta/Modular.lean#L65) (definition).
- [21.5.E2](https://dlmf.nist.gov/21.5.E2): [`DLMF.RiemannTheta.IsSymplectic`](DLMF/RiemannTheta/Modular.lean#L60) (definition); [`DLMF.RiemannTheta.isSymplectic_iff_mem_symplecticGroup`](DLMF/RiemannTheta/Modular.lean#L75) (proved); Mathlib: [`Matrix.symplecticGroup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SymplecticGroup.html#Matrix.symplecticGroup).
- [21.5.E2](https://dlmf.nist.gov/21.5.E2): [`DLMF.RiemannTheta.isSymplectic_iff_mem_symplecticGroup`](DLMF/RiemannTheta/Modular.lean#L75) (proved). Bridge to Matrix.symplecticGroup; [`DLMF.RiemannTheta.IsSymplectic`](DLMF/RiemannTheta/Modular.lean#L60) (definition).
- [21.5.E3](https://dlmf.nist.gov/21.5.E3): [`DLMF.RiemannTheta.det_eq_one_of_isSymplectic`](DLMF/RiemannTheta/Modular.lean#L83) (proved); Mathlib: [`SymplecticGroup.det_eq_one`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SymplecticGroup.html#SymplecticGroup.det_eq_one).
- [21.5.E4](https://dlmf.nist.gov/21.5.E4): [`DLMF.RiemannTheta.riemannTheta_modular`](DLMF/RiemannTheta/Modular.lean#L114) (admitted). **Corrected**: false for general symplectic Γ (z-dependent ratio for g = 2); requires the theta-group condition (even diag(CDᵀ) and diag(ABᵀ)) and a continuous square-root branch.
- [21.5.E5](https://dlmf.nist.gov/21.5.E5): [`DLMF.RiemannTheta.riemannTheta_unimodular`](DLMF/RiemannTheta/Modular.lean#L136) (proved). **Corrected** (hypothesis): A ∈ GL_g(ℤ) (invertible over ℤ), not only det A ≠ 0.
- [21.5.E6](https://dlmf.nist.gov/21.5.E6): [`DLMF.RiemannTheta.riemannTheta_add_symm_int_even`](DLMF/RiemannTheta/Modular.lean#L230) (proved); Mathlib: [`jacobiTheta₂_add_right`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂_add_right).
- [21.5.E7](https://dlmf.nist.gov/21.5.E7): [`DLMF.RiemannTheta.riemannTheta_add_symm_int`](DLMF/RiemannTheta/Modular.lean#L205) (proved).
- [21.5.E8](https://dlmf.nist.gov/21.5.E8): [`DLMF.RiemannTheta.riemannTheta_inversion`](DLMF/RiemannTheta/Modular.lean#L245) (admitted). **Corrected**: the printed principal root of det(−iΩ) is wrong for g ≥ 3 (Ω = τI₃, τ = −1.1√3 + i gives minus it); continuous square root with value 1 at Ω = iI; [`DLMF.RiemannTheta.riemannTheta_inversion_fin_one`](DLMF/RiemannTheta/Modular.lean#L280) (proved); [`DLMF.RiemannTheta.riemannTheta_inversion_principal`](DLMF/RiemannTheta/Modular.lean#L259) (admitted); Mathlib: [`jacobiTheta₂_functional_equation`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂_functional_equation).
- [21.5.E8](https://dlmf.nist.gov/21.5.E8): [`DLMF.RiemannTheta.riemannTheta_inversion_principal`](DLMF/RiemannTheta/Modular.lean#L259) (admitted). **Corrected** (restricted): principal square root valid only for g ≤ 2 (false for g ≥ 3); [`DLMF.RiemannTheta.riemannTheta_inversion_fin_one`](DLMF/RiemannTheta/Modular.lean#L280) (proved); Mathlib: [`jacobiTheta₂_functional_equation`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂_functional_equation).
- [21.5.E8](https://dlmf.nist.gov/21.5.E8): [`DLMF.RiemannTheta.riemannTheta_inversion_fin_one`](DLMF/RiemannTheta/Modular.lean#L280) (proved). g = 1, principal square root; [`DLMF.RiemannTheta.riemannTheta_inversion_principal`](DLMF/RiemannTheta/Modular.lean#L259) (admitted); Mathlib: [`jacobiTheta₂_functional_equation`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#jacobiTheta₂_functional_equation).
- [21.5.E9](https://dlmf.nist.gov/21.5.E9): [`DLMF.RiemannTheta.riemannThetaChar_modular`](DLMF/RiemannTheta/Modular.lean#L311) (admitted). Continuous square-root branch; κ independent of z and Ω.
- [21.5.i](https://dlmf.nist.gov/21.5#i): [`DLMF.RiemannTheta.modular_mem_siegel`](DLMF/RiemannTheta/Modular.lean#L95) (admitted). The modular action preserves the Siegel space and CΩ+D is invertible.
- [21.5.i](https://dlmf.nist.gov/21.5#i): [`DLMF.RiemannTheta.exists_continuous_sqrt_det`](DLMF/RiemannTheta/Modular.lean#L105) (admitted). Existence of a continuous branch of the square root of det(CΩ+D).

## [§21.6 Products](https://dlmf.nist.gov/21.6)

- [21.6.E1](https://dlmf.nist.gov/21.6.E1): [`DLMF.RiemannTheta.riemannK`](DLMF/RiemannTheta/Products.lean#L60) (definition).
- [21.6.E2](https://dlmf.nist.gov/21.6.E2): [`DLMF.RiemannTheta.riemannD`](DLMF/RiemannTheta/Products.lean#L76) (definition).
- [21.6.E3](https://dlmf.nist.gov/21.6.E3): [`DLMF.RiemannTheta.riemann_identity`](DLMF/RiemannTheta/Products.lean#L91) (admitted). Representatives of 𝒦 taken in ℤ^{g×h}T.
- [21.6.E4](https://dlmf.nist.gov/21.6.E4): [`DLMF.RiemannTheta.riemann_identity_char`](DLMF/RiemannTheta/Products.lean#L108) (admitted). **Corrected**: c_j, d_j are g-dimensional columns, not h-dimensional as printed. Representatives of 𝒦 in ℤ^{g×h}T follow DLMF's own definition 21.6.1 (formalization note, not an erratum).
- [21.6.E5](https://dlmf.nist.gov/21.6.E5): [`DLMF.RiemannTheta.riemannTExample`](DLMF/RiemannTheta/Products.lean#L131) (definition); [`DLMF.RiemannTheta.riemannTExample_mul_transpose`](DLMF/RiemannTheta/Products.lean#L138) (proved); [`DLMF.RiemannTheta.riemannTExample_rat`](DLMF/RiemannTheta/Products.lean#L146) (proved).
- [21.6.E5](https://dlmf.nist.gov/21.6.E5): [`DLMF.RiemannTheta.riemannTExample_mul_transpose`](DLMF/RiemannTheta/Products.lean#L138) (proved). T is orthogonal; [`DLMF.RiemannTheta.riemannTExample_rat`](DLMF/RiemannTheta/Products.lean#L146) (proved).
- [21.6.E5](https://dlmf.nist.gov/21.6.E5): [`DLMF.RiemannTheta.riemannTExample_rat`](DLMF/RiemannTheta/Products.lean#L146) (proved). T has rational entries; [`DLMF.RiemannTheta.riemannTExample_mul_transpose`](DLMF/RiemannTheta/Products.lean#L138) (proved).
- [21.6.E6](https://dlmf.nist.gov/21.6.E6): [`DLMF.RiemannTheta.riemannTheta_four_product`](DLMF/RiemannTheta/Products.lean#L457) (proved).
- [21.6.E7](https://dlmf.nist.gov/21.6.E7): [`DLMF.RiemannTheta.riemannThetaChar_four_product`](DLMF/RiemannTheta/Products.lean#L603) (proved).
- [21.6.E8](https://dlmf.nist.gov/21.6.E8): [`DLMF.RiemannTheta.riemannThetaChar_mul_addition`](DLMF/RiemannTheta/Products.lean#L242) (proved).

## Analytical prose and exclusions

- [21.1.p1](https://dlmf.nist.gov/21.1#p1)–[21.1.p5](https://dlmf.nist.gov/21.1#p5) and table 21.1.T1: notation. Covered by `siegelUpperHalfSpace`, `symplecticJ`, `riemannThetaBig` and `riemannThetaBig_eq_tsum`; ‖·‖, transpose and the integer lattice use Mathlib notation.
- [21.1](https://dlmf.nist.gov/21.1): [`DLMF.RiemannTheta.riemannThetaBig`](DLMF/RiemannTheta/Basic.lean#L87) (definition); [`DLMF.RiemannTheta.riemannThetaBig_eq_tsum`](DLMF/RiemannTheta/Basic.lean#L514) (proved); [`DLMF.RiemannTheta.siegelUpperHalfSpace`](DLMF/RiemannTheta/Basic.lean#L51) (definition); [`DLMF.RiemannTheta.symplecticJ`](DLMF/RiemannTheta/Modular.lean#L54) (definition).
- [21.1](https://dlmf.nist.gov/21.1): [`DLMF.RiemannTheta.riemannThetaBig`](DLMF/RiemannTheta/Basic.lean#L87) (definition); [`DLMF.RiemannTheta.riemannThetaBig_eq_tsum`](DLMF/RiemannTheta/Basic.lean#L514) (proved); [`DLMF.RiemannTheta.siegelUpperHalfSpace`](DLMF/RiemannTheta/Basic.lean#L51) (definition); [`DLMF.RiemannTheta.symplecticJ`](DLMF/RiemannTheta/Modular.lean#L54) (definition).
- [21.2.i.p1](https://dlmf.nist.gov/21.2#i.p1): absolute and uniform convergence on compact sets, analyticity in each element of z and Ω. Covered by `summable_norm_riemannThetaTerm`, `tendstoUniformlyOn_riemannTheta`, `tendstoLocallyUniformlyOn_riemannTheta`, `continuousOn_riemannTheta`, `differentiableAt_riemannTheta_update` and `differentiableAt_riemannTheta_entry` (all proved).
- [21.2.i.p2](https://dlmf.nist.gov/21.2#i.p2): the scaled θ̂ is bounded and nonanalytic in z. `riemannThetaScaled_bounded` (proved), `not_differentiable_riemannThetaScaled` (admitted).
- [21.2.Px1.p1](https://dlmf.nist.gov/21.2#Px1.p1): the example 21.2.E3/E4. Covered by `riemannMatrixExample_mem`, `riemannTheta_example` and `riemannThetaScaled_example`.
- [21.2.ii.p1](https://dlmf.nist.gov/21.2#ii.p1): theta functions with characteristics and the 2^{2g} half-period characteristics. Covered by `summable_norm_riemannThetaCharTerm`, `halfPeriodCharacteristics` and `ncard_halfPeriodCharacteristics`.
- [21.2.iii.p1](https://dlmf.nist.gov/21.2#iii.p1): relation to the classical theta functions. Covered by 21.2.E8–E12.
- [21.2.i](https://dlmf.nist.gov/21.2.i): [`DLMF.RiemannTheta.continuousOn_riemannTheta`](DLMF/RiemannTheta/Basic.lean#L330) (proved); [`DLMF.RiemannTheta.differentiableAt_riemannTheta_entry`](DLMF/RiemannTheta/Basic.lean#L368) (proved); [`DLMF.RiemannTheta.differentiableAt_riemannTheta_update`](DLMF/RiemannTheta/Basic.lean#L351) (proved); [`DLMF.RiemannTheta.not_differentiable_riemannThetaScaled`](DLMF/RiemannTheta/Basic.lean#L506) (admitted); [`DLMF.RiemannTheta.riemannThetaScaled_bounded`](DLMF/RiemannTheta/Basic.lean#L455) (proved); [`DLMF.RiemannTheta.summable_norm_riemannThetaTerm`](DLMF/RiemannTheta/Basic.lean#L290) (proved); [`DLMF.RiemannTheta.tendstoLocallyUniformlyOn_riemannTheta`](DLMF/RiemannTheta/Basic.lean#L303) (proved); [`DLMF.RiemannTheta.tendstoUniformlyOn_riemannTheta`](DLMF/RiemannTheta/Basic.lean#L315) (proved); Mathlib: [`hasSum_jacobiTheta₂_term`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#hasSum_jacobiTheta₂_term); Mathlib: [`differentiableAt_jacobiTheta₂_fst`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#differentiableAt_jacobiTheta₂_fst); Mathlib: [`differentiableAt_jacobiTheta₂_snd`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html#differentiableAt_jacobiTheta₂_snd).
- [21.2.ii](https://dlmf.nist.gov/21.2.ii): [`DLMF.RiemannTheta.halfPeriodCharacteristics`](DLMF/RiemannTheta/Basic.lean#L684) (definition); [`DLMF.RiemannTheta.ncard_halfPeriodCharacteristics`](DLMF/RiemannTheta/Basic.lean#L689) (proved); [`DLMF.RiemannTheta.summable_norm_riemannThetaCharTerm`](DLMF/RiemannTheta/Basic.lean#L676) (proved).
- [21.3.i.p1](https://dlmf.nist.gov/21.3#i.p1): the period lattice and the quasi-periodicity that determines θ up to a constant. `riemannThetaPeriodLattice` (definition), `eq_const_mul_riemannTheta_of_quasiPeriodic` (admitted).
- [21.3.ii.p1](https://dlmf.nist.gov/21.3#ii.p1): the convention α, β ∈ [0,1). Not imposed; see the conventions above.
- [21.3.i](https://dlmf.nist.gov/21.3.i): [`DLMF.RiemannTheta.eq_const_mul_riemannTheta_of_quasiPeriodic`](DLMF/RiemannTheta/Symmetry.lean#L106) (admitted); [`DLMF.RiemannTheta.riemannThetaPeriodLattice`](DLMF/RiemannTheta/Symmetry.lean#L100) (definition).
- [21.5.i.p1](https://dlmf.nist.gov/21.5#i.p1), [21.5.i.p2](https://dlmf.nist.gov/21.5#i.p2): the modular action preserves the Siegel space, and the square-root branch. `modular_mem_siegel` and `exists_continuous_sqrt_det` (both admitted).
- [21.5.ii.p1](https://dlmf.nist.gov/21.5#ii.p1), [21.5.ii.p2](https://dlmf.nist.gov/21.5#ii.p2): characteristics under modular transformations, κ independent of z and Ω. Covered by `riemannThetaChar_modular`.
- [21.5.i](https://dlmf.nist.gov/21.5.i): [`DLMF.RiemannTheta.exists_continuous_sqrt_det`](DLMF/RiemannTheta/Modular.lean#L105) (admitted); [`DLMF.RiemannTheta.modular_mem_siegel`](DLMF/RiemannTheta/Modular.lean#L95) (admitted).
- [21.6.i.p1](https://dlmf.nist.gov/21.6#i.p1): the setting of Riemann's identity (rational T with TTᵀ = hI). Covered by `riemannK`, `riemannD` and `IsRiemannKRepresentatives`.
- [21.6.Px1.p1](https://dlmf.nist.gov/21.6#Px1.p1), [21.6.Px1.p2](https://dlmf.nist.gov/21.6#Px1.p2): the example T of 21.6.E5 and its consequences 21.6.E6/E7. Covered by `riemannTExample`, `riemannTExample_mul_transpose`, `riemannTExample_rat`, `riemannTheta_four_product` and `riemannThetaChar_four_product`.
- [21.6.ii.p1](https://dlmf.nist.gov/21.6#ii.p1): the addition formula. Covered by `riemannThetaChar_mul_addition`.
- [21.4.E1](https://dlmf.nist.gov/21.4.E1): excluded: numerical. The figures of §21.4: excluded: graphics.
- [§21.7](https://dlmf.nist.gov/21.7), 21.7.E1–E17: excluded: application (Riemann surfaces). The mathematical theorems it states are: the period matrix of a compact Riemann surface with a canonical homology basis is a Riemann matrix (21.7.E6); a genus-g surface depends on 3g − 3 complex moduli for g ≥ 2; Fay's trisecant identity (21.7.E10); Frobenius' identity (21.7.E17) for hyperelliptic surfaces, with the properties 21.7.E13–E16 of the map η.
- [§21.8](https://dlmf.nist.gov/21.8) (21.8.p1): excluded: application. Theorem stated: every Abelian function is a ratio of homogeneous polynomials in theta functions with characteristics.
- [§21.9](https://dlmf.nist.gov/21.9), 21.9.E1–E4: excluded: application (integrable equations). Theorems stated: Krichever's quasi-periodic KP solutions (21.9.E4), and the Novikov conjecture (Shiota's theorem) characterizing Jacobians among Riemann matrices.
- [§21.10](https://dlmf.nist.gov/21.10), [§21.11](https://dlmf.nist.gov/21.11): excluded: computation and software.

## Validation

`lake build DLMF.RiemannTheta` and the strict checks with `autoImplicit=false` and
`relaxedAutoImplicit=false` pass for all six files. The theorem-axiom audit of the proved
samples reports only `propext`, `Classical.choice` and `Quot.sound`. The numbered source
inventory for §§21.2–21.6 has no unexplained gap. The numerical checks behind the
errata were Python evaluations of truncated lattice sums.
