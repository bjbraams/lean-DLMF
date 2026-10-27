# DLMF Chapter 10 index (Bessel functions)

Generated on 2026-10-17 from the `@[dlmf 10.…]` attributes in the project. Unlike the Chapter
13 and 18 inventories, this is an index of tagged declarations, not an equation-by-equation
acquisition review: untagged DLMF equations are not listed. `J_ν` is Mathlib's
`Complex.besselJ`; `Y_ν`, `H^{(1,2)}_ν`, `I_ν` and `K_ν` are project definitions in
[SecondKind.lean](SecondKind.lean) and [Modified.lean](Modified.lean).

49 DLMF labels in 20 sections are tagged on 72 declarations; 1 of the tagged declarations are admitted.
Paths are relative to this directory.

| DLMF | Declarations | Status |
| --- | --- | --- |
| [10.2.E1](https://dlmf.nist.gov/10.2.E1) | [besselJ_ode](Basic.lean) (line 213); [besselY_ode](Basic.lean) (line 244); [besselY_ode_all](SecondKind.lean) (line 360) | proved |
| [10.2.E2](https://dlmf.nist.gov/10.2.E2) | [besselJ_eq_regularized](Basic.lean) (line 43) | proved |
| [10.2.E3](https://dlmf.nist.gov/10.2.E3) | [besselY](Basic.lean) (line 51) | definition |
| [10.2.E4](https://dlmf.nist.gov/10.2.E4) | [besselY_int_eq_deriv](WeberSeries.lean) (line 75) | proved |
| [10.2.E5](https://dlmf.nist.gov/10.2.E5) | [hankelH1_sub_exp_isBigO](Elementary.lean) (line 473) | proved |
| [10.4.E1](https://dlmf.nist.gov/10.4.E1) | [besselJ_neg_int](Generating.lean) (line 26); [besselY_neg_int](WeberSeries.lean) (line 69) | proved |
| [10.4.E3](https://dlmf.nist.gov/10.4.E3) | [hankelH1](SecondKind.lean) (line 484); [hankelH2](SecondKind.lean) (line 488) | definition |
| [10.4.E6](https://dlmf.nist.gov/10.4.E6) | [hankelH1_neg](Elementary.lean) (line 152); [hankelH2_neg](Elementary.lean) (line 162) | proved |
| [10.5.E1](https://dlmf.nist.gov/10.5.E1) | [wronskian_besselJ_neg](SecondKind.lean) (line 420) | proved |
| [10.5.E2](https://dlmf.nist.gov/10.5.E2) | [wronskian_besselJ_besselY](SecondKind.lean) (line 476) | proved |
| [10.5.E5](https://dlmf.nist.gov/10.5.E5) | [wronskian_hankelH1_hankelH2](SecondKind.lean) (line 506) | proved |
| [10.6.E1](https://dlmf.nist.gov/10.6.E1) | [hankelH1_add_sub](Elementary.lean) (line 172); [hankelH2_add_sub](Elementary.lean) (line 181); [besselJ_add_sub](Theorems.lean) (line 34); [two_deriv_besselJ](Theorems.lean) (line 45) | proved |
| [10.6.E6](https://dlmf.nist.gov/10.6.E6) | [iterate_zRecipDeriv_cpow_mul_besselJ](Elementary.lean) (line 562); [iterate_zRecipDeriv_cpow_neg_mul_besselJ](Elementary.lean) (line 579) | proved |
| [10.7.E8](https://dlmf.nist.gov/10.7.E8) | [besselJ_sub_cos_isBigO](Asymptotics.lean) (line 370); [besselY_sub_sin_isBigO](Elementary.lean) (line 519) | proved |
| [10.8.E1](https://dlmf.nist.gov/10.8.E1) | [besselY_nat_eq_series](WeberSeries.lean) (line 203) | proved |
| [10.8.E2](https://dlmf.nist.gov/10.8.E2) | [besselY_zero_eq_series](WeberSeries.lean) (line 164) | proved |
| [10.8.E3](https://dlmf.nist.gov/10.8.E3) | [besselJ_mul_besselJ](WeberSeries.lean) (line 386) | proved |
| [10.9.E1](https://dlmf.nist.gov/10.9.E1) | [besselJ_zero_eq_integral_cos](BesselIntegral.lean) (line 142) | proved |
| [10.9.E2](https://dlmf.nist.gov/10.9.E2) | [besselJ_int_eq_integral_cos](BesselIntegral.lean) (line 106) | proved |
| [10.9.E4](https://dlmf.nist.gov/10.9.E4) | [besselJ_eq_poisson_integral](Theorems.lean) (line 52) | proved |
| [10.12.E1](https://dlmf.nist.gov/10.12.E1) | [hasSum_besselJ_jacobiAnger](BesselIntegral.lean) (line 31); [besselJ_generating_function](Theorems.lean) (line 122) | proved |
| [10.12.E2](https://dlmf.nist.gov/10.12.E2) | [hasSum_besselJ_cos](WeberSeries.lean) (line 451) | proved |
| [10.12.E3](https://dlmf.nist.gov/10.12.E3) | [hasSum_besselJ_sin](WeberSeries.lean) (line 486) | proved |
| [10.14.E1](https://dlmf.nist.gov/10.14.E1) | [norm_besselJ_int_le_one](Elementary.lean) (line 192) | proved |
| [10.16.E1](https://dlmf.nist.gov/10.16.E1) | [besselJ_half](Basic.lean) (line 480); [besselJ_neg_half](Basic.lean) (line 491); [besselY_half](Elementary.lean) (line 84); [besselY_neg_half](Elementary.lean) (line 90); [hankelH1_half](Elementary.lean) (line 96); [hankelH2_half](Elementary.lean) (line 106); [hankelH1_neg_half](Elementary.lean) (line 116); [hankelH2_neg_half](Elementary.lean) (line 124) | proved |
| [10.16.E5](https://dlmf.nist.gov/10.16.E5) | [besselJ_eq_kummerM](Basic.lean) (line 568) | proved |
| [10.17.E5](https://dlmf.nist.gov/10.17.E5) | [hasAsymptoticExpansion_hankelH1](Asymptotics.lean) (line 317) | proved |
| [10.22.E5](https://dlmf.nist.gov/10.22.E5) | [integral_mul_besselJ_mul_besselJ](Lommel.lean) (line 225) | proved |
| [10.22.E37](https://dlmf.nist.gov/10.22.E37) | [integral_besselJ_orthogonal](Lommel.lean) (line 260); [integral_mul_besselJ_sq](Lommel.lean) (line 355) | proved |
| [10.22.E51](https://dlmf.nist.gov/10.22.E51) | [sonine_integral](Sonine.lean) (line 131) | proved |
| [10.23.E3](https://dlmf.nist.gov/10.23.E3) | [hasSum_besselJ_add](Elementary.lean) (line 210) | proved |
| [10.23.E7](https://dlmf.nist.gov/10.23.E7) | [hasSum_besselJ_graf](P3mGraf.lean) | proved for J at integer order, stronger than DLMF (no restriction ‖v e^{±iα}‖ < ‖u‖; 2026-10-26); Y, H and general order open |
| [10.23.E8](https://dlmf.nist.gov/10.23.E8) | [besselJ_addition](../SphericalHarmonics/BesselAddition.lean) | proved (moved 2026-10-22) |
| [10.25.E1](https://dlmf.nist.gov/10.25.E1) | [besselI_ode](Modified.lean) (line 78); [besselK_ode](Modified.lean) (line 97); [besselK_ode_all](SecondKind.lean) (line 769) | proved |
| [10.25.E2](https://dlmf.nist.gov/10.25.E2) | [besselI](Modified.lean) (line 29) | definition |
| [10.27.E1](https://dlmf.nist.gov/10.27.E1) | [besselI_neg_int](SecondKind.lean) (line 554) | proved |
| [10.27.E3](https://dlmf.nist.gov/10.27.E3) | [besselK_neg](SecondKind.lean) (line 854) | proved |
| [10.27.E4](https://dlmf.nist.gov/10.27.E4) | [besselK](Modified.lean) (line 35) | definition |
| [10.27.E6](https://dlmf.nist.gov/10.27.E6) | [besselI_eq_besselJ](Modified.lean) (line 55) | proved |
| [10.27.E8](https://dlmf.nist.gov/10.27.E8) | [hankelH1_eq_besselK](Asymptotics.lean) (line 245) | proved |
| [10.28.E1](https://dlmf.nist.gov/10.28.E1) | [wronskian_besselI_neg](SecondKind.lean) (line 795) | proved |
| [10.28.E2](https://dlmf.nist.gov/10.28.E2) | [wronskian_besselK_besselI](SecondKind.lean) (line 844) | proved |
| [10.29.E1](https://dlmf.nist.gov/10.29.E1) | [besselI_sub_add](SecondKind.lean) (line 533); [besselK_add_sub](SecondKind.lean) (line 701) | proved |
| [10.29.E2](https://dlmf.nist.gov/10.29.E2) | [hasDerivAt_besselK](SecondKind.lean) (line 744) | proved |
| [10.32.E2](https://dlmf.nist.gov/10.32.E2) | [besselI_eq_poisson_integral](Elementary.lean) (line 602) | proved |
| [10.32.E8](https://dlmf.nist.gov/10.32.E8) | [besselK_eq_integral_Ioi_one](KIntegrals.lean) (line 82) | proved |
| [10.35.E1](https://dlmf.nist.gov/10.35.E1) | [hasSum_besselI_generating_function](Elementary.lean) (line 300) | proved |
| [10.35.E3](https://dlmf.nist.gov/10.35.E3) | [hasSum_besselI_cos](Elementary.lean) (line 329) | proved |
| [10.40.E1](https://dlmf.nist.gov/10.40.E1) | [besselI_sub_exp_isBigO](SturmZeros.lean) (line 288); [besselI_isEquivalent](SturmZeros.lean) (line 328) | proved |
| [10.40.E2](https://dlmf.nist.gov/10.40.E2) | [hasAsymptoticExpansion_besselK](Asymptotics.lean) (line 71) | proved |
