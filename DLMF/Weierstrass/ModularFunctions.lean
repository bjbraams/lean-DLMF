/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic.Modular
public import DLMF.Weierstrass.EllipticFunctionsAndInvariants
public import DLMF.JacobiElliptic.AnalyticProperties
public import DLMF.Weierstrass.SpecialLattices
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Elliptic modular functions

The elliptic modular function `λ(τ)`, Klein's complete invariant `J(τ)` and Dedekind's eta
function (DLMF §§23.15–23.19): special values, `q`-expansions, products, transformations under
`SL(2, ℤ)` and the relations with the lattice invariants. The definitions of `λ`, `J`, the
bilinear transformations, the notions of §23.15(i), the Dedekind sum and the eta multiplier are
in `DLMF.Weierstrass.Basic.Modular`; `J` is `ModularForm.kleinJ = E₄³/(E₄³ - E₆²)`.

## Main results

* `nome_eq_modulus`, `modulus_eq_theta`: DLMF 23.15.1–23.15.2.
* `kleinJ_eq_jacobiTheta`: the theta-function formula for `J` (DLMF 23.15.7).
* `eta_hasProd`, `eta_pow_three_eq_theta`, `eta_hasSum`: DLMF 23.17.8, 23.15.9, 23.17.6.
* `modularLambda_special`, `kleinJ_special`, `eta_special`: values at `i` and `e^{πi/3}`
  (DLMF 23.17.1–23.17.3).
* `modularLambda_isBigO`, `kleinJ_isBigO`, `modularLambda_hasProd`: DLMF 23.17.4, 23.17.5,
  23.17.7.
* `modularLambda_smul`, `modularLambda_smul_of_even`, `isCuspForm_modularLambda`: DLMF
  23.18.1–23.18.3.
* `isModularFunction_kleinJ`: DLMF 23.18.4 (the invariance itself is
  `ModularForm.kleinJ_smul`).
* `eta_smul`, `isModularFunction_eta`: DLMF 23.18.5.
* `modularLambda_eq_eta`, `kleinJ_eq_modularLambda`, `kleinJ_eq_invariants`,
  `latticeDiscriminant_eq_eta`: DLMF 23.19.1–23.19.4.

## Implementation notes

`λ` is defined from the project's theta functions in lattice-parameter form `θⱼ(0|τ)`
(`DLMF.Theta.jacobiThetaTwoNullTau` etc.), and the theta formula 23.15.7 for `J` is proved from
the lattice form 23.19.3 and Mathlib's Eisenstein series; Dedekind's eta function is Mathlib's
`ModularForm.eta`. DLMF writes `θⱼ(0, q)` with `q = e^{iπτ}`; the nome form of `θ₂` and of `θ₁'`
carries a branch of `q^{1/4}` which only changes them by a fourth root of unity, and `λ`
(fourth powers) and `J` (eighth powers) are unaffected by it.

The transformation 23.15.3 is the Möbius action of `SL(2, ℤ)` on the upper half-plane
(`A • τ` for `A : SL(2, ℤ)`, `τ : ℍ`); `mobius_coe` is the bridge to the explicit formula.

The general notions of §23.15(i) are formalized literally: the level `ℓ` is an integer or half
an odd integer, which we encode by the integer `ℓ₂ = 2ℓ`, with `(cτ + d)^ℓ` the principal
power. "Analytic at `q = 0` as a function of `q`" means that `f(τ) = F(e^{iπτ})` with `F`
analytic at `0`.

Terminology in §23.18: DLMF calls `J` "a modular form of level zero for `SL(2, ℤ)`", but by
23.17.5 `J` has a pole `q⁻²/1728` at `q = 0`, so it is not a modular form in the sense of
§23.15(i); it is a modular function (`isModularFunction_kleinJ`).
-/

@[expose] public section

open Complex Asymptotics Matrix
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

noncomputable section

namespace DLMF.Weierstrass

open DLMF.EllipticIntegrals (compEllIntKk compEllIntKpk)

open DLMF.Elliptic DLMF.Theta DLMF.JacobiElliptic
open ModularForm (kleinJ)

/-! ### §23.15(i) General modular functions -/

/-- DLMF 23.15.1: the nome of the modulus `k` is `q = exp(-πK'(k)/K(k)) = e^{iπτ}` with
`τ = iK'(k)/K(k)` (stated for every complex `k`, with the project's principal `K`, `K'`). -/
@[dlmf 23.15.E1]
theorem nome_eq_modulus (k : ℂ) :
    jacobiNomek k = cexp (-(π * compEllIntKpk k / compEllIntKk k)) ∧
      jacobiNomek k = cexp (π * I * jacobiTauk k) :=
  ⟨rfl, jacobiNomek_eq_exp_tau k⟩

/-- DLMF 23.15.2: for `k` in the modulus domain of DLMF 22.2 (`ℜk > 0`, and `k < 1` if `k` is
real) and `τ = iK'(k)/K(k)`, `k = θ₂²(0|τ)/θ₃²(0|τ)` and `k' = θ₄²(0|τ)/θ₃²(0|τ)`. -/
@[dlmf 23.15.E2]
theorem modulus_eq_theta {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    k = jacobiThetaTwoTau 0 (jacobiTauk k) ^ 2 / jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 ∧
      jacobiComodulusk k =
        jacobiThetaFourTau 0 (jacobiTauk k) ^ 2 / jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 := by
  obtain ⟨h1, h2, -⟩ := jacobi_inversion_k hk
  exact ⟨h1.symm, h2.symm⟩

/-! ### §23.15(ii) `λ(τ)`, `J(τ)`, `η(τ)` -/

/-- `e^{2πiτ} = (e^{iπτ})²`. -/
private lemma exp_two_pi_I_mul_eq_sq (τ : ℂ) : cexp (2 * π * I * τ) = cexp (π * I * τ) ^ 2 := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- DLMF 23.17.8: `η(τ) = q^{1/12} ∏_{n≥1} (1 - q^{2n})` with `q^{1/12} = e^{iπτ/12}`,
`ℑτ > 0`; the product converges. -/
@[dlmf 23.17.E8]
theorem eta_hasProd (τ : ℍ) :
    HasProd (fun n : ℕ ↦ 1 - cexp (π * I * τ) ^ (2 * (n + 1)))
        (∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * (n + 1)))) ∧
      η (τ : ℂ) = cexp (π * I * τ / 12) *
        ∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * (n + 1))) := by
  have hq : ∀ n : ℕ, cexp (π * I * τ) ^ (2 * (n + 1)) = cexp (2 * π * I * τ) ^ (n + 1) := by
    intro n
    rw [pow_mul, exp_two_pi_I_mul_eq_sq]
  simp_rw [hq]
  refine ⟨(ModularForm.multipliable_one_sub_pow ?_).hasProd, ?_⟩
  · rw [Complex.norm_exp]
    rw [Real.exp_lt_one_iff]
    have : (2 * π * I * (τ : ℂ)).re = -(2 * π * τ.im) := by simp
    rw [this]
    have := τ.im_pos
    have := Real.pi_pos
    nlinarith
  · rw [ModularForm.eta, Function.Periodic.qParam]
    simp_rw [ModularForm.eta_q_eq_pow]
    congr 2
    push_cast
    ring

/-- `η³ = θ₁'(0|τ)/2`. -/
private lemma eta_pow_three_eq_jacobiThetaOneDerivNullTau (τ : ℍ) : η (τ : ℂ) ^ 3 =
    jacobiThetaOneDerivNullTau τ / 2 := by
  obtain ⟨hm, he⟩ := eta_hasProd τ
  obtain ⟨-, h1, -⟩ := jacobiThetaOneDerivNullTau_prod (τ := (τ : ℂ)) τ.im_pos
  rw [he, mul_pow, ← hm.multipliable.tprod_pow, h1, ← exp_nat_mul]
  push_cast
  ring_nf

/-- Regrouping an infinite product in blocks of three. -/
private lemma tprod_blocks_three {f : ℕ → ℂ} (hf : Multipliable f)
    (hg : Multipliable (fun k : ℕ => f (3 * k) * f (3 * k + 1) * f (3 * k + 2))) :
    ∏' k : ℕ, (f (3 * k) * f (3 * k + 1) * f (3 * k + 2)) = ∏' n, f n := by
  have t1 := hg.hasProd.tendsto_prod_nat
  have h3 : Filter.Tendsto (fun N : ℕ => 3 * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have t2 := hf.hasProd.tendsto_prod_nat.comp h3
  have e : ∀ N : ℕ, ∏ i ∈ Finset.range (3 * N), f i =
      ∏ k ∈ Finset.range N, (f (3 * k) * f (3 * k + 1) * f (3 * k + 2)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ]
      ring
  simp only [Function.comp_def, e] at t2
  exact tendsto_nhds_unique t1 t2

/-- `η(τ) = e^{iπτ/12} θ₃(π(1 + τ)/2 | 3τ)`. -/
private lemma eta_eq_exp_mul_jacobiThetaThreeTau (τ : ℍ) :
    η (τ : ℂ) = cexp (π * I * τ / 12) * jacobiThetaThreeTau (π * (1 + τ) / 2) (3 * τ) := by
  have hτ' : 0 < (3 * (τ : ℂ)).im := by simpa using τ.im_pos
  obtain ⟨-, hm3, ht⟩ := jacobiThetaThreeTau_triple_product ((1 + τ) / 2) hτ'
  obtain ⟨hm, he⟩ := eta_hasProd τ
  set q := cexp (π * I * τ) with hq
  have hq0 : q ≠ 0 := exp_ne_zero _
  have hQ : cexp (π * I * (3 * τ)) = q ^ 3 := by rw [hq, ← exp_nat_mul]; congr 1; push_cast; ring
  have hz : cexp (π * I * ((1 + τ) / 2)) ^ 2 = -q := by
    rw [← exp_nat_mul, hq, show ((2 : ℕ) : ℂ) * (π * I * ((1 + τ) / 2)) = π * I + π * I * τ by
      push_cast; ring, exp_add, exp_pi_mul_I]; ring
  rw [hQ, hz] at hm3 ht
  rw [show π * ((1 + (τ : ℂ)) / 2) = π * (1 + τ) / 2 by ring] at ht
  set f : ℕ → ℂ := fun n => 1 - q ^ (2 * (n + 1)) with hf
  have key : ∀ k : ℕ, (1 - (q ^ 3) ^ (2 * (k + 1))) * (1 + (q ^ 3) ^ (2 * k + 1) * -q) *
      (1 + (q ^ 3) ^ (2 * k + 1) * (-q)⁻¹) = f (3 * k) * f (3 * k + 1) * f (3 * k + 2) := by
    intro k
    simp only [hf]
    have : (q ^ 3) ^ (2 * k + 1) * (-q)⁻¹ = -q ^ (6 * k + 2) := by
      field_simp; ring
    rw [this]; ring
  simp_rw [key] at hm3 ht
  rw [ht, tprod_blocks_three hm.multipliable hm3, he]

/-- The right-hand side `(θ₂⁸ + θ₃⁸ + θ₄⁸)³/(54 θ₁'⁸)` of DLMF 23.15.7. -/
private def thetaKleinJ (τ : ℂ) : ℂ :=
  (jacobiThetaTwoNullTau τ ^ 8 + jacobiThetaThreeNullTau τ ^ 8 + jacobiThetaFourNullTau τ ^ 8) ^ 3 /
    (54 * jacobiThetaOneDerivNullTau τ ^ 8)

/-- `J` and `λ` in terms of `A = θ₂⁴`, `C = θ₄⁴` (with `θ₃⁴ = A + C`). -/
private lemma thetaKleinJ_eq_jacobiThetaNull {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ ^ 4 ≠ 0 ∧ jacobiThetaFourNullTau τ ^ 4 ≠ 0 ∧
    jacobiThetaTwoNullTau τ ^ 4 + jacobiThetaFourNullTau τ ^ 4 ≠ 0 ∧
    thetaKleinJ τ = ((jacobiThetaTwoNullTau τ ^ 4) ^ 2 +
        (jacobiThetaTwoNullTau τ ^ 4 + jacobiThetaFourNullTau τ ^ 4) ^ 2 +
        (jacobiThetaFourNullTau τ ^ 4) ^ 2) ^ 3 /
      (54 * (jacobiThetaTwoNullTau τ ^ 4) ^ 2 *
        (jacobiThetaTwoNullTau τ ^ 4 + jacobiThetaFourNullTau τ ^ 4) ^ 2 *
        (jacobiThetaFourNullTau τ ^ 4) ^ 2) ∧
    modularLambda τ = jacobiThetaTwoNullTau τ ^ 4 /
      (jacobiThetaTwoNullTau τ ^ 4 + jacobiThetaFourNullTau τ ^ 4) := by
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero hτ
  have hJ := jacobiThetaNull_fourth_power τ hτ
  have h3 : jacobiThetaThreeNullTau τ ^ 4 ≠ 0 := pow_ne_zero _ n3
  refine ⟨pow_ne_zero _ n2, pow_ne_zero _ n4, hJ ▸ h3, ?_, ?_⟩
  · rw [thetaKleinJ, jacobiThetaOneDerivNullTau_eq_mul hτ, ← hJ]
    ring
  · rw [modularLambda, ← hJ]

/-- The algebraic identity behind DLMF 23.19.2. -/
private lemma thetaKleinJ_modularLambda_algebra {A C : ℂ} (hA : A ≠ 0) (hC : C ≠ 0)
    (hAC : A + C ≠ 0) :
    (A ^ 2 + (A + C) ^ 2 + C ^ 2) ^ 3 / (54 * A ^ 2 * (A + C) ^ 2 * C ^ 2) =
      4 / 27 * (1 - A / (A + C) + (A / (A + C)) ^ 2) ^ 3 /
        (A / (A + C) * (1 - A / (A + C))) ^ 2 := by
  have h1 : 1 - A / (A + C) = C / (A + C) := by field_simp; ring
  rw [h1]
  field_simp
  ring

/-- DLMF 23.19.2 for the theta form of `J`. -/
private lemma thetaKleinJ_eq_modularLambda (τ : ℍ) :
    thetaKleinJ τ = 4 / 27 * (1 - modularLambda τ + modularLambda τ ^ 2) ^ 3 /
      (modularLambda τ * (1 - modularLambda τ)) ^ 2 := by
  obtain ⟨hA, hC, hAC, hJ, hl⟩ := thetaKleinJ_eq_jacobiThetaNull (τ := (τ : ℂ)) τ.im_pos
  rw [hJ, hl]
  exact thetaKleinJ_modularLambda_algebra hA hC hAC

/-- DLMF 23.19.3 for the theta form of `J`. -/
private lemma thetaKleinJ_eq_invariants (τ : ℍ) :
    thetaKleinJ τ = (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).g₂ ^ 3 /
      ((HalfPeriods.ofTau (1 / 2) (by norm_num) τ).g₂ ^ 3 -
        27 * (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).g₃ ^ 2) := by
  set H := HalfPeriods.ofTau (1 / 2) (by norm_num) τ
  have hτH : H.tau = τ := by
    simp only [HalfPeriods.tau, H, HalfPeriods.ofTau_ω₁, HalfPeriods.ofTau_ω₃]; field_simp
  obtain ⟨hA, hC, hAC, hJ, -⟩ := thetaKleinJ_eq_jacobiThetaNull (τ := (τ : ℂ)) τ.im_pos
  obtain ⟨d3, d2⟩ := H.e_one_sub_e_three_and_e_one_sub_e_two
  have hj := jacobiThetaNull_fourth_power τ τ.im_pos
  simp only [jacobiThetaThreeNullTau, jacobiThetaFourNullTau, jacobiThetaTwoNullTau]
      at hj hJ hA hC hAC
  rw [hτH] at d3 d2
  rw [hj] at d3
  have hs := H.e_sum
  have hD : H.g₂ ^ 3 - 27 * H.g₃ ^ 2 =
      16 * (H.e 2 - H.e 3) ^ 2 * (H.e 3 - H.e 1) ^ 2 * (H.e 1 - H.e 2) ^ 2 :=
    H.latticeDiscriminant_eq
  rw [hD, hJ]
  set A := jacobiThetaTwoTau 0 τ ^ 4
  set C := jacobiThetaFourTau 0 τ ^ 4
  set c := (π / (2 * H.ω₁)) ^ 2
  have hc : c ≠ 0 := by
    simp only [c, H, HalfPeriods.ofTau_ω₁]
    have := Real.pi_ne_zero
    exact pow_ne_zero _ (div_ne_zero (by exact_mod_cast this) (by norm_num))
  have e1 : H.e 1 = c * (2 * C + A) / 3 := by linear_combination (d3 + d2 + hs) / 3
  have e2 : H.e 2 = H.e 1 - c * C := by linear_combination -d2
  have e3 : H.e 3 = H.e 1 - c * (A + C) := by linear_combination -d3
  have hg : H.g₂ = 2 / 3 * c ^ 2 * (A ^ 2 + (A + C) ^ 2 + C ^ 2) := by
    rw [H.g₂_eq_e.1, e2, e3, e1]; ring
  have f1 : H.e 2 - H.e 3 = c * A := by rw [e2, e3]; ring
  have f2 : H.e 3 - H.e 1 = -(c * (A + C)) := by rw [e3]; ring
  rw [hg, f1, f2, d2]
  field_simp
  ring

open ModularForm EisensteinSeries in
/-- The theta form of `J` is `E₄³/(E₄³ - E₆²)`. -/
private lemma thetaKleinJ_eq_kleinJ (τ : ℍ) : thetaKleinJ τ = kleinJ τ := by
  rw [thetaKleinJ_eq_invariants]
  set L0 := (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).periodPair
  have z4 : riemannZeta ((4 : ℕ) : ℂ) = π ^ 4 / 90 := by exact_mod_cast riemannZeta_four
  have z6 : riemannZeta ((6 : ℕ) : ℂ) = π ^ 6 / 945 := by exact_mod_cast riemannZeta_six_eq_pi_pow
  have ha : L0.g₂ = 4 * π ^ 4 / 3 * E₄ τ := by
    rw [PeriodPair.g₂, G_ofTau_eq_two_mul_riemannZeta_mul_E τ (k := 4) (by norm_num), z4]; ring
  have hb : L0.g₃ = 8 * π ^ 6 / 27 * E₆ τ := by
    rw [PeriodPair.g₃, G_ofTau_eq_two_mul_riemannZeta_mul_E τ (k := 6) (by norm_num), z6]; ring
  have hD := E₄_cube_sub_E₆_sq_ne_zero τ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [HalfPeriods.g₂, HalfPeriods.g₃]
  rw [ha, hb, ModularForm.kleinJ,
    show (4 * π ^ 4 / 3 * E₄ τ) ^ 3 - 27 * (8 * π ^ 6 / 27 * E₆ τ) ^ 2 =
    64 * (π : ℂ) ^ 12 / 27 * (E₄ τ ^ 3 - E₆ τ ^ 2) by ring]
  rw [div_eq_div_iff (mul_ne_zero (by simp [hπ]) hD) hD]
  ring

/-- DLMF 23.15.7: `J(τ) = (θ₂⁸(0|τ) + θ₃⁸(0|τ) + θ₄⁸(0|τ))³/(54 θ₁'(0|τ)⁸)`, `ℑτ > 0`. -/
@[dlmf 23.15.E7]
theorem kleinJ_eq_jacobiTheta (τ : ℍ) :
    kleinJ τ = (jacobiThetaTwoNullTau τ ^ 8 + jacobiThetaThreeNullTau τ ^ 8 +
        jacobiThetaFourNullTau τ ^ 8) ^ 3 / (54 * jacobiThetaOneDerivNullTau τ ^ 8) :=
  (thetaKleinJ_eq_kleinJ τ).symm

/-- The lattice of an equianharmonic `H` is invariant under multiplication by `e^{πi/3}`. -/
private lemma mem_lattice_iff_div_exp_pi_I_div_three {H : HalfPeriods}
    (h3 : H.ω₃ = cexp (π * I / 3) * H.ω₁) :
    ∀ z, z ∈ H.lattice ↔ z / cexp (π * I / 3) ∈ H.lattice := by
  set ρ := cexp (π * I / 3) with hρ
  have hρ0 : ρ ≠ 0 := Complex.exp_ne_zero _
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hρ2 : ρ ^ 2 = ρ - 1 := by
    rw [hρ, HalfPeriods.exp_pi_I_div_three_eq]; ring_nf; rw [I_sq, hs]; ring
  have hρi : ρ⁻¹ = 1 - ρ := by
    apply inv_eq_of_mul_eq_one_right; linear_combination -hρ2
  intro z
  simp only [H.mem_lattice_iff, h3]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m + n, -m, ?_⟩
    rw [div_eq_mul_inv, hρi]; push_cast; linear_combination (-2 * n * H.ω₁) * hρ2
  · rintro ⟨m, n, hmn⟩
    refine ⟨-n, m + n, ?_⟩
    have : z = ρ * (2 * m * H.ω₁ + 2 * n * (ρ * H.ω₁)) := by rw [← hmn]; field_simp
    rw [this]; push_cast; linear_combination (2 * n * H.ω₁) * hρ2

/-- The point `i` of `ℍ`. -/
def upperHalfPlaneI : ℍ := ⟨I, by simp⟩

/-- The point `e^{πi/3}` of `ℍ`. -/
noncomputable def upperHalfPlaneRho : ℍ := ⟨cexp (π * I / 3), by
  rw [HalfPeriods.exp_pi_I_div_three_eq]; simp⟩

/-- DLMF 23.15.9: for `ℑτ > 0`, `η(τ)³ = θ₁'(0|τ)/2` (the cube root of DLMF being the branch
fixed by the second equality) and `η(τ) = e^{iπτ/12} θ₃(π(1 + τ)/2 | 3τ)`; `η` is Mathlib's
Dedekind eta function `ModularForm.eta`. -/
@[dlmf 23.15.E9]
theorem eta_pow_three_eq_theta (τ : ℍ) :
    η (τ : ℂ) ^ 3 = jacobiThetaOneDerivNullTau τ / 2 ∧
      η (τ : ℂ) = cexp (π * I * τ / 12) * jacobiThetaThreeTau (π * (1 + τ) / 2) (3 * τ) := by
  exact ⟨eta_pow_three_eq_jacobiThetaOneDerivNullTau τ, eta_eq_exp_mul_jacobiThetaThreeTau τ⟩

/-- 23.15.9, branch statement: on the positive imaginary axis `η` is real and positive. -/
@[dlmf 23.15.E9]
theorem eta_pos_of_re_eq_zero (τ : ℍ) (hτ : (τ : ℂ).re = 0) :
    (η (τ : ℂ)).im = 0 ∧ 0 < (η (τ : ℂ)).re := by
  set t := (τ : ℂ).im
  have ht : 0 < t := τ.im_pos
  have hτI : (τ : ℂ) = I * t := Complex.ext (by simpa using hτ) (by simp [t])
  -- reality
  obtain ⟨hm, he⟩ := eta_hasProd τ
  have hq : cexp (π * I * τ) = ((Real.exp (-(π * t)) : ℝ) : ℂ) := by
    rw [hτI, ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  have hq12 : cexp (π * I * τ / 12) = ((Real.exp (-(π * t) / 12) : ℝ) : ℂ) := by
    rw [hτI, ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  rw [hq] at hm he
  rw [hq12] at he
  have hc := hm.map (starRingEnd ℂ) continuous_conj
  have hfix : (starRingEnd ℂ) ∘ (fun n : ℕ => 1 - ((Real.exp (-(π * t)) : ℝ) : ℂ) ^ (2 * (n + 1))) =
      fun n : ℕ => 1 - ((Real.exp (-(π * t)) : ℝ) : ℂ) ^ (2 * (n + 1)) := by
    funext n; simp only [Function.comp_apply, map_sub, map_one, map_pow, conj_ofReal]
  rw [hfix] at hc
  have hP := hc.unique hm
  have hreal : (starRingEnd ℂ) (η (τ : ℂ)) = η (τ : ℂ) := by
    rw [he, map_mul, conj_ofReal, hP]
  have him : (η (τ : ℂ)).im = 0 := Complex.conj_eq_iff_im.mp hreal
  refine ⟨him, ?_⟩
  -- positivity from η³ = θ₂θ₃θ₄/2
  have h3 := eta_pow_three_eq_jacobiThetaOneDerivNullTau τ
  rw [jacobiThetaOneDerivNullTau_eq_mul (τ := (τ : ℂ)) τ.im_pos] at h3
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at h3
  have t2 : jacobiThetaTwoTau 0 (τ : ℂ) =
      ((jacobiThetaFourImag (1 / t) / Real.sqrt t : ℝ) : ℂ) := by
    rw [hτI, jacobiThetaTwoTau_zero_I_mul_eq_div_sqrt ht]
  have t3 : jacobiThetaThreeTau 0 (τ : ℂ) = (jacobiThetaThreeImag t : ℂ) :=
      by rw [hτI, jacobiThetaThreeTau_zero_I_mul_eq_imag]
  have t4 : jacobiThetaFourTau 0 (τ : ℂ) = (jacobiThetaFourImag t : ℂ) :=
      by rw [hτI, jacobiThetaFourTau_zero_I_mul_eq_imag]
  rw [t2, t3, t4] at h3
  have hA := jacobiThetaTwoImag_pos ht
  have hB := one_le_jacobiThetaThreeImag ht
  have hC := jacobiThetaFourImag_pos ht
  have hη : η (τ : ℂ) = ((η (τ : ℂ)).re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hη] at h3
  have h3r : (η (τ : ℂ)).re ^ 3 = jacobiThetaFourImag (1 / t) / Real.sqrt t *
      jacobiThetaThreeImag t * jacobiThetaFourImag t / 2 := by
    exact_mod_cast h3
  have hpos : 0 < jacobiThetaFourImag (1 / t) / Real.sqrt t * jacobiThetaThreeImag t *
      jacobiThetaFourImag t / 2 := by
    have := jacobiThetaFourImag_pos (t := 1 / t) (by positivity)
    have := Real.sqrt_pos.mpr ht
    positivity
  by_contra hn
  push_neg at hn
  have : (η (τ : ℂ)).re ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) hn
  linarith

/-! ### §23.17 Elementary properties -/

/-- DLMF 23.17.1: `λ(i) = 1/2` and `λ(e^{πi/3}) = e^{πi/3}`. -/
@[dlmf 23.17.E1]
theorem modularLambda_special :
    modularLambda I = 1 / 2 ∧ modularLambda (cexp (π * I / 3)) = cexp (π * I / 3) := by
  constructor
  · set H := HalfPeriods.ofTau (1 / 2) (by norm_num) upperHalfPlaneI
    have hL : H.IsLemniscatic := ⟨by simp [H], by simp [H], by simp [H, upperHalfPlaneI]; ring⟩
    have hτ : H.tau = I := hL.tau
    rw [modularLambda_eq_modulus_sq, ← hτ, ← HalfPeriods.modulus, H.modulus_sq_eq.1]
    exact hL.modulus_sq
  · set ρ := cexp (π * I / 3) with hρ
    set H := HalfPeriods.ofTau (1 / 2) (by norm_num) upperHalfPlaneRho
    have h3 : H.ω₃ = ρ * H.ω₁ := by simp [H, upperHalfPlaneRho, hρ]; ring
    have hτ : H.tau = ρ := by
      rw [HalfPeriods.tau, h3, mul_div_assoc, div_self H.ω₁_ne_zero, mul_one]
    have hρ0 : ρ ≠ 0 := Complex.exp_ne_zero _
    have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
    have hρ2 : ρ ^ 2 = ρ - 1 := by
      rw [hρ, HalfPeriods.exp_pi_I_div_three_eq]; ring_nf; rw [I_sq, hs]; ring
    have hp := H.weierstrassP_mul_of_lattice_invariant ρ hρ0
        (mem_lattice_iff_div_exp_pi_I_div_three h3)
    have e3 : H.e 3 = ρ⁻¹ ^ 2 * H.e 1 := by
      rw [HalfPeriods.e, HalfPeriods.e, HalfPeriods.halfPeriod_three, HalfPeriods.halfPeriod_one,
        h3, hp]
    have e2 : H.e 2 = ρ⁻¹ ^ 2 * H.e 3 := by
      have h1 := hp (ρ * H.ω₁)
      have hper : H.weierstrassP (ρ * (ρ * H.ω₁)) = H.weierstrassP H.ω₂ := by
        have hz : ρ * (ρ * H.ω₁) = -H.ω₂ - 2 * H.halfPeriod 1 := by
          rw [HalfPeriods.halfPeriod_one, HalfPeriods.ω₂, h3]; linear_combination H.ω₁ * hρ2
        have := H.weierstrassP_add_two_mul_halfPeriod (-H.ω₂ - 2 * H.halfPeriod 1) (j := 1)
          (by simp)
        rw [hz, ← this, show -H.ω₂ - 2 * H.halfPeriod 1 + 2 * H.halfPeriod 1 = -H.ω₂ by ring]
        exact H.periodPair.weierstrassP_neg H.ω₂
      have : H.e 3 = H.weierstrassP (ρ * H.ω₁) := by
        rw [HalfPeriods.e, HalfPeriods.halfPeriod_three, h3]
      rw [this, ← h1, hper]; rfl
    obtain ⟨-, -, d13⟩ := H.e_distinct
    have he1 : H.e 1 ≠ 0 := by
      intro h0; apply d13; rw [e3, h0]; ring
    rw [modularLambda_eq_modulus_sq, ← hτ, ← HalfPeriods.modulus, H.modulus_sq_eq.1, e2, e3]
    have hρ3 : ρ ^ 3 = -1 := by linear_combination (ρ + 1) * hρ2
    have hden : 1 - ρ⁻¹ ^ 2 ≠ 0 := by
      intro h0
      have h1 : ρ ^ 2 = 1 := by field_simp at h0; linear_combination h0
      have h2 : ρ = 2 := by linear_combination h1 - hρ2
      rw [h2] at h1; norm_num at h1
    have hne : H.e 1 - ρ⁻¹ ^ 2 * H.e 1 ≠ 0 := by
      rw [show H.e 1 - ρ⁻¹ ^ 2 * H.e 1 = (1 - ρ⁻¹ ^ 2) * H.e 1 by ring]
      exact mul_ne_zero hden he1
    have hi : ρ⁻¹ = 1 - ρ := by
      apply inv_eq_of_mul_eq_one_right; linear_combination -hρ2
    rw [div_eq_iff hne, hτ, hi]
    linear_combination (H.e 1 * (ρ ^ 2 - 2 * ρ)) * hρ2

/-- DLMF 23.17.2: `J(i) = 1` and `J(e^{πi/3}) = 0`. -/
@[dlmf 23.17.E2]
theorem kleinJ_special : kleinJ upperHalfPlaneI = 1 ∧ kleinJ upperHalfPlaneRho = 0 := by
  obtain ⟨l1, l2⟩ := modularLambda_special
  refine ⟨?_, ?_⟩
  · have := thetaKleinJ_eq_modularLambda upperHalfPlaneI
    simp only [show ((upperHalfPlaneI : ℍ) : ℂ) = I from rfl] at this
    rw [← thetaKleinJ_eq_kleinJ, show ((upperHalfPlaneI : ℍ) : ℂ) = I from rfl, this, l1]
    norm_num
  · have := thetaKleinJ_eq_modularLambda upperHalfPlaneRho
    simp only [show ((upperHalfPlaneRho : ℍ) : ℂ) = cexp (π * I / 3) from rfl] at this
    have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
    have hρ2 : cexp (π * I / 3) ^ 2 = cexp (π * I / 3) - 1 := by
      rw [HalfPeriods.exp_pi_I_div_three_eq]; ring_nf; rw [I_sq, hs]; ring
    rw [← thetaKleinJ_eq_kleinJ, show ((upperHalfPlaneRho : ℍ) : ℂ) = cexp (π * I / 3) from rfl,
      this, l2, show 1 - cexp (π * I / 3) + cexp (π * I / 3) ^ 2 = 0 by
      linear_combination hρ2]
    simp

/-- DLMF 23.17.3: `η(i) = Γ(1/4)/(2π^{3/4})` and
`η(e^{πi/3}) = 3^{1/8}Γ(1/3)^{3/2}e^{πi/24}/(2π)`. -/
@[dlmf 23.17.E3]
theorem eta_special :
    η I = ((Real.Gamma (1 / 4) / (2 * π ^ (3 / 4 : ℝ)) : ℝ) : ℂ) ∧
      η (cexp (π * I / 3)) =
        ((3 ^ (1 / 8 : ℝ) * Real.Gamma (1 / 3) ^ (3 / 2 : ℝ) / (2 * π) : ℝ) : ℂ) *
        cexp (π * I / 24) := by
  sorry

/-- Tail bound for a lacunary `q`-series `∑ₙ q^{e(n)}`: dropping the finitely many terms with
`e(n) < N` leaves `O(‖q‖^N)` for `‖q‖ ≤ 1/2`. -/
private lemma norm_tsum_pow_sub_sum_le {e : ℤ → ℕ} {N : ℕ} (F : Finset ℤ)
    (hF : ∀ n ∉ F, N ≤ e n) (hs : Summable fun n => (1 / 2 : ℝ) ^ e n) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 2) :
    ‖∑' n, q ^ e n - ∑ n ∈ F, q ^ e n‖ ≤ 2 ^ N * (∑' n, (1 / 2 : ℝ) ^ e n) * ‖q‖ ^ N := by
  have hle : ∀ n, ‖q ^ e n‖ ≤ (1 / 2 : ℝ) ^ e n := fun n => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hq _
  have hsum : Summable fun n => q ^ e n := Summable.of_norm_bounded hs hle
  have hpt : ∀ n ∉ F, ‖q ^ e n‖ ≤ ‖q‖ ^ N * (2 ^ N * (1 / 2 : ℝ) ^ e n) := by
    intro n hn
    have h1 := hF n hn
    rw [norm_pow, ← Nat.add_sub_cancel' h1, pow_add, pow_add]
    have h2 : ‖q‖ ^ (e n - N) ≤ (1 / 2 : ℝ) ^ (e n - N) :=
      pow_le_pow_left₀ (norm_nonneg _) hq _
    have h3 : (2 : ℝ) ^ N * ((1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ (e n - N)) =
        (1 / 2 : ℝ) ^ (e n - N) := by
      rw [← mul_assoc, ← mul_pow]; norm_num
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 (pow_nonneg (norm_nonneg _) _)
  rw [← hsum.sum_add_tsum_compl (s := F), add_sub_cancel_left]
  have hsc : Summable fun n : ((F : Set ℤ)ᶜ : Set ℤ) => (1 / 2 : ℝ) ^ e n :=
    hs.subtype _
  have hb : Summable fun n : ((F : Set ℤ)ᶜ : Set ℤ) =>
      ‖q‖ ^ N * (2 ^ N * (1 / 2 : ℝ) ^ e n) := (hsc.mul_left _).mul_left _
  calc ‖∑' n : ((F : Set ℤ)ᶜ : Set ℤ), q ^ e n‖
      ≤ ∑' n : ((F : Set ℤ)ᶜ : Set ℤ), ‖q‖ ^ N * (2 ^ N * (1 / 2 : ℝ) ^ e n) :=
        tsum_of_norm_bounded hb.hasSum fun n => hpt n n.2
    _ = ‖q‖ ^ N * (2 ^ N * ∑' n : ((F : Set ℤ)ᶜ : Set ℤ), (1 / 2 : ℝ) ^ e n) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ ≤ ‖q‖ ^ N * (2 ^ N * ∑' n, (1 / 2 : ℝ) ^ e n) := by
        gcongr
        exact hs.tsum_subtype_le _ _ (fun n => by positivity)
    _ = _ := by ring

open Filter Topology in
/-- The nome `q = e^{iπτ}` tends to `0` at `i∞`. -/
private lemma tendsto_nome_atImInfty :
    Tendsto (fun τ : ℍ => cexp (π * I * τ)) atImInfty (𝓝 0) := by
  refine (qParam_tendsto_atImInfty (h := 2) (by norm_num)).congr fun τ => ?_
  simp only [Function.Periodic.qParam]
  congr 1; push_cast; ring

/-- `θ₃(0|τ) = ∑ₙ q^{n²}`. -/
private lemma jacobiTheta₂_zero_eq_tsum (τ : ℂ) :
    jacobiTheta₂ 0 τ = ∑' n : ℤ, cexp (π * I * τ) ^ (n.natAbs ^ 2) := by
  simp only [jacobiTheta₂, jacobiTheta₂_term]
  congr 1; funext n
  rw [← Complex.exp_nat_mul]
  congr 1
  have : ((n.natAbs ^ 2 : ℕ) : ℂ) = (n : ℂ) ^ 2 := by
    have h : ((n.natAbs : ℤ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by exact_mod_cast Int.natAbs_sq n
    rw [Nat.cast_pow, ← h, Int.cast_natCast]
  rw [this]; ring

private lemma int_mul_add_nonneg (n : ℤ) : 0 ≤ n * n + n := by
  rcases le_or_gt 0 n with h | h <;> nlinarith

/-- `e^{-iπτ/4}θ₂(0|τ) = ∑ₙ q^{n(n+1)}`. -/
private lemma jacobiTheta₂_half_eq_tsum (τ : ℂ) :
    jacobiTheta₂ (τ / 2) τ = ∑' n : ℤ, cexp (π * I * τ) ^ (n * n + n).toNat := by
  simp only [jacobiTheta₂, jacobiTheta₂_term]
  congr 1; funext n
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (((n * n + n).toNat : ℕ) : ℂ) = (n : ℂ) ^ 2 + n := by
    have h := Int.toNat_of_nonneg (int_mul_add_nonneg n)
    have h' : (((n * n + n).toNat : ℤ) : ℂ) = ((n * n + n : ℤ) : ℂ) := by rw [h]
    push_cast at h'; rw [h']; ring
  rw [this]; ring

private lemma summable_half_pow_natAbs :
    Summable fun n : ℤ => (1 / 2 : ℝ) ^ n.natAbs := by
  have hg : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact Summable.of_nat_of_neg (by simpa using hg) (by simpa using hg)

private lemma summable_half_pow_natAbs_sq :
    Summable fun n : ℤ => (1 / 2 : ℝ) ^ (n.natAbs ^ 2) :=
  Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_self_pow two_ne_zero _))
    summable_half_pow_natAbs

private lemma summable_half_pow_toNat :
    Summable fun n : ℤ => (1 / 2 : ℝ) ^ (n * n + n).toNat := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_half_pow_natAbs.mul_left 2)
  have h : n.natAbs ≤ (n * n + n).toNat + 1 := by
    rcases le_or_gt 0 n with h | h
    · have : n ≤ n * n + n := by nlinarith
      omega
    · have : -n - 1 ≤ n * n + n := by nlinarith
      omega
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) h
  rw [pow_succ] at this
  linarith

open Filter in
private lemma eventually_norm_exp_pi_I_mul_le :
    ∀ᶠ τ : ℍ in atImInfty, ‖cexp (π * I * τ)‖ ≤ 1 / 2 := by
  have := tendsto_nome_atImInfty.norm
  rw [norm_zero] at this
  exact this.eventually (ge_mem_nhds (by norm_num))

/-- `θ₃(0|τ) = 1 + 2q + O(q⁴)`. -/
private lemma jacobiTheta₂_zero_isBigO :
    (fun τ : ℍ => jacobiTheta₂ 0 τ - (1 + 2 * cexp (π * I * τ))) =O[atImInfty]
      fun τ => cexp (π * I * τ) ^ 4 := by
  refine IsBigO.of_bound (2 ^ 4 * ∑' n : ℤ, (1 / 2 : ℝ) ^ (n.natAbs ^ 2)) ?_
  filter_upwards [eventually_norm_exp_pi_I_mul_le] with τ hτ
  have h := norm_tsum_pow_sub_sum_le (e := fun n : ℤ => n.natAbs ^ 2) (N := 4) {-1, 0, 1}
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have : 2 ≤ n.natAbs := by omega
      exact (Nat.pow_le_pow_left this 2).trans' (by norm_num))
    summable_half_pow_natAbs_sq hτ
  have hF : ∑ n ∈ ({-1, 0, 1} : Finset ℤ), cexp (π * I * τ) ^ (n.natAbs ^ 2) =
      1 + 2 * cexp (π * I * τ) := by
    simp; ring
  rw [jacobiTheta₂_zero_eq_tsum, ← hF, norm_pow]
  exact h

/-- `e^{-iπτ/4}θ₂(0|τ) = 2 + 2q² + O(q⁶)`. -/
private lemma jacobiTheta₂_half_isBigO :
    (fun τ : ℍ => jacobiTheta₂ ((τ : ℂ) / 2) τ - (2 + 2 * cexp (π * I * τ) ^ 2)) =O[atImInfty]
      fun τ => cexp (π * I * τ) ^ 6 := by
  refine IsBigO.of_bound (2 ^ 6 * ∑' n : ℤ, (1 / 2 : ℝ) ^ (n * n + n).toNat) ?_
  filter_upwards [eventually_norm_exp_pi_I_mul_le] with τ hτ
  have h := norm_tsum_pow_sub_sum_le (e := fun n : ℤ => (n * n + n).toNat) (N := 6)
    {-2, -1, 0, 1}
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have : 6 ≤ n * n + n := by
        rcases le_or_gt 2 n with h | h
        · nlinarith
        · have : n ≤ -3 := by omega
          nlinarith
      omega)
    summable_half_pow_toNat hτ
  have hF : ∑ n ∈ ({-2, -1, 0, 1} : Finset ℤ), cexp (π * I * τ) ^ (n * n + n).toNat =
      2 + 2 * cexp (π * I * τ) ^ 2 := by
    simp; ring
  rw [jacobiTheta₂_half_eq_tsum, ← hF, norm_pow]
  exact h

/-- `λ(τ) = q B⁴/T⁴` with `B = e^{-iπτ/4}θ₂(0|τ)` and `T = θ₃(0|τ)`. -/
private lemma modularLambda_eq_nome_mul (τ : ℂ) :
    modularLambda τ = cexp (π * I * τ) * jacobiTheta₂ (τ / 2) τ ^ 4 / jacobiTheta₂ 0 τ ^ 4 := by
  simp only [modularLambda, jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaTwoTau,
    jacobiThetaThreeTau, mul_zero, add_zero, zero_div, zero_add]
  have h1 : cexp (π * I * τ / 4) ^ 4 = cexp (π * I * τ) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : (π : ℂ) * τ / 2 / π = τ / 2 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [mul_pow, h1, h2]

/-- DLMF 23.17.4: `λ(τ) = 16q(1 - 8q + 44q² + O(q³))` as `q = e^{iπτ} → 0`. -/
@[dlmf 23.17.E4]
theorem modularLambda_isBigO :
    (fun τ : ℍ ↦ modularLambda τ - 16 * cexp (π * I * τ) *
        (1 - 8 * cexp (π * I * τ) + 44 * cexp (π * I * τ) ^ 2)) =O[atImInfty]
      fun τ ↦ cexp (π * I * τ) ^ 4 := by
  open Filter Topology in
  set q : ℍ → ℂ := fun τ => cexp (π * I * τ) with hq
  set B : ℍ → ℂ := fun τ => jacobiTheta₂ ((τ : ℂ) / 2) τ
  set T : ℍ → ℂ := fun τ => jacobiTheta₂ 0 τ
  set a : ℍ → ℂ := fun τ => B τ - (2 + 2 * q τ ^ 2)
  set b : ℍ → ℂ := fun τ => T τ - (1 + 2 * q τ)
  have hq0 : Tendsto q atImInfty (𝓝 0) := tendsto_nome_atImInfty
  have ha : a =O[atImInfty] fun τ => q τ ^ 6 := jacobiTheta₂_half_isBigO
  have hb : b =O[atImInfty] fun τ => q τ ^ 4 := jacobiTheta₂_zero_isBigO
  have hq6 : (fun τ => q τ ^ 6) =O[atImInfty] fun τ => q τ ^ 4 := by
    have : (fun τ => q τ ^ 6) = fun τ => q τ ^ 4 * q τ ^ 2 := funext fun τ => by ring
    rw [this]
    simpa using (isBigO_refl (fun τ => q τ ^ 4) atImInfty).mul
      ((hq0.pow 2).isBigO_one ℂ)
  have ha0 : Tendsto a atImInfty (𝓝 0) :=
    ha.trans_tendsto (by simpa using hq0.pow 6)
  have hb0 : Tendsto b atImInfty (𝓝 0) :=
    hb.trans_tendsto (by simpa using hq0.pow 4)
  have hB : Tendsto B atImInfty (𝓝 2) := by
    have : B = fun τ => a τ + (2 + 2 * q τ ^ 2) := funext fun τ => by simp [a]
    rw [this]; simpa using ha0.add ((hq0.pow 2).const_mul 2 |>.const_add 2)
  have hT : Tendsto T atImInfty (𝓝 1) := by
    have : T = fun τ => b τ + (1 + 2 * q τ) := funext fun τ => by simp [b]
    rw [this]; simpa using hb0.add ((hq0.const_mul 2).const_add 1)
  have hT4 : Tendsto (fun τ => T τ ^ 4) atImInfty (𝓝 1) := by simpa using hT.pow 4
  have hTne : ∀ᶠ τ in atImInfty, T τ ≠ 0 :=
    hT.eventually (isOpen_ne.mem_nhds one_ne_zero)
  set r : ℂ → ℂ := fun x => 16 * (-192 - 810 * x - 1280 * x ^ 2 - 700 * x ^ 3 + x ^ 5)
  set c : ℍ → ℂ := fun τ => 2 + 2 * q τ ^ 2
  set d : ℍ → ℂ := fun τ => 1 + 2 * q τ
  set P : ℍ → ℂ := fun τ => 1 - 8 * q τ + 44 * q τ ^ 2
  have key : ∀ᶠ τ : ℍ in atImInfty, modularLambda (τ : ℂ) - 16 * q τ * P τ =
      q τ ^ 4 * (r (q τ) / T τ ^ 4) +
      a τ * (q τ * (B τ ^ 3 + B τ ^ 2 * c τ + B τ * c τ ^ 2 + c τ ^ 3) / T τ ^ 4) +
      b τ * (q τ * (-16 * P τ * (T τ ^ 3 + T τ ^ 2 * d τ + T τ * d τ ^ 2 + d τ ^ 3)) /
        T τ ^ 4) := by
    filter_upwards [hTne] with τ hτ
    rw [modularLambda_eq_nome_mul]
    simp only [a, b, c, d, P, r, B, T, q] at hτ ⊢
    field_simp
    ring
  have hV : Tendsto (fun τ => (q τ, B τ, T τ)) atImInfty (𝓝 ((0 : ℂ), (2 : ℂ), (1 : ℂ))) :=
    hq0.prodMk_nhds (hB.prodMk_nhds hT)
  have bdd : ∀ Φ : ℂ × ℂ × ℂ → ℂ, ContinuousAt Φ ((0 : ℂ), (2 : ℂ), (1 : ℂ)) →
      (fun τ => Φ (q τ, B τ, T τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    fun Φ hΦ => (hΦ.tendsto.comp hV).isBigO_one ℂ
  have h1 := (isBigO_refl (fun τ => q τ ^ 4) atImInfty).mul
    (bdd (fun p => r p.1 / p.2.2 ^ 4) (by fun_prop (disch := norm_num)))
  have h2 := (ha.trans hq6).mul (bdd (fun p => p.1 * (p.2.1 ^ 3 + p.2.1 ^ 2 * (2 + 2 * p.1 ^ 2) +
      p.2.1 * (2 + 2 * p.1 ^ 2) ^ 2 + (2 + 2 * p.1 ^ 2) ^ 3) / p.2.2 ^ 4)
    (by fun_prop (disch := norm_num)))
  have h3 := hb.mul (bdd (fun p => p.1 * (-16 * (1 - 8 * p.1 + 44 * p.1 ^ 2) *
      (p.2.2 ^ 3 + p.2.2 ^ 2 * (1 + 2 * p.1) + p.2.2 * (1 + 2 * p.1) ^ 2 + (1 + 2 * p.1) ^ 3)) /
      p.2.2 ^ 4) (by fun_prop (disch := norm_num)))
  simp only [mul_one] at h1 h2 h3
  exact ((h1.add h2).add h3).congr' (key.mono fun τ h => h.symm) EventuallyEq.rfl


/-- DLMF 23.17.5: `1728J(τ) = q⁻² + 744 + 196884q² + 21493760q⁴ + O(q⁶)` as
`q = e^{iπτ} → 0`. -/
@[dlmf 23.17.E5]
theorem kleinJ_isBigO :
    (fun τ : ℍ ↦ 1728 * kleinJ τ - (cexp (π * I * τ) ^ (-2 : ℤ) + 744 +
        196884 * cexp (π * I * τ) ^ 2 + 21493760 * cexp (π * I * τ) ^ 4)) =O[atImInfty]
      fun τ ↦ cexp (π * I * τ) ^ 6 := by
  sorry

/-- DLMF 23.17.6: `η(τ) = ∑_{n∈ℤ} (-1)ⁿ q^{(6n+1)²/12}` with `q^{(6n+1)²/12} = e^{iπτ(6n+1)²/12}`,
for `ℑτ > 0` (Euler's pentagonal number theorem). -/
@[dlmf 23.17.E6]
theorem eta_hasSum (τ : ℍ) :
    HasSum (fun n : ℤ ↦ (-1) ^ n * cexp (π * I * τ * (6 * n + 1) ^ 2 / 12)) (η (τ : ℂ)) := by
  have hτ' : 0 < (3 * (τ : ℂ)).im := by simpa using τ.im_pos
  obtain ⟨hs, -, -⟩ := jacobiThetaThreeTau_triple_product ((1 + τ) / 2) hτ'
  rw [eta_eq_exp_mul_jacobiThetaThreeTau, show π * (1 + (τ : ℂ)) / 2 = π * ((1 + τ) / 2) by ring]
  convert hs.mul_left (cexp (π * I * τ / 12)) using 1
  funext n
  rw [← exp_int_mul, ← exp_int_mul, ← exp_add, ← exp_add,
    show (-1 : ℂ) = cexp (π * I) from exp_pi_mul_I.symm, ← exp_int_mul, ← exp_add]
  congr 1
  push_cast
  ring

/-- DLMF 23.17.7: `λ(τ) = 16q ∏_{n≥1} ((1 + q^{2n})/(1 + q^{2n-1}))⁸`, `q = e^{iπτ}`, `ℑτ > 0`. -/
@[dlmf 23.17.E7]
theorem modularLambda_hasProd (τ : ℍ) :
    HasProd (fun n : ℕ ↦ ((1 + cexp (π * I * τ) ^ (2 * (n + 1))) /
        (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 8)
      (modularLambda τ / (16 * cexp (π * I * τ))) := by
  set q := cexp (π * I * τ) with hq
  have hτ := τ.im_pos
  obtain ⟨m2, e2⟩ := jacobiThetaTwoNullTau_prod hτ
  obtain ⟨m3, e3⟩ := jacobiThetaThreeNullTau_prod hτ
  obtain ⟨-, n3, -⟩ := jacobiThetaNullTau_ne_zero hτ
  have hq1 : ‖q‖ < 1 := by
    rw [hq, Complex.norm_exp, Real.exp_lt_one_iff]
    have : (↑π * I * (τ : ℂ)).re = -(π * (τ : ℂ).im) := by simp
    rw [this, neg_lt_zero]
    exact mul_pos Real.pi_pos hτ
  have hx : ∀ k : ℕ, 1 - q ^ (2 * (k + 1)) ≠ 0 := fun k h => by
    have h1 : q ^ (2 * (k + 1)) = 1 := by linear_combination -h
    have := congrArg norm h1
    rw [norm_pow, norm_one] at this
    exact absurd this (pow_lt_one₀ (norm_nonneg _) hq1 (by omega)).ne
  have hP3 : ∏' k : ℕ, ((1 - q ^ (2 * (k + 1))) * (1 + q ^ (2 * k + 1)) ^ 2) ≠ 0 := by
    rw [← e3]; exact n3
  have h := (m2.hasProd.pow 4).div₀ (m3.hasProd.pow 4) (pow_ne_zero 4 hP3)
  have hq4 : cexp (π * I * τ / 4) ^ 4 = q := by
    rw [← Complex.exp_nat_mul, hq]; congr 1; push_cast; ring
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  convert h using 1
  · funext k
    rw [← div_pow, mul_div_mul_left _ _ (hx k), div_pow, div_pow, ← pow_mul, ← pow_mul]
  · rw [modularLambda, e2, ← e3, mul_pow, mul_pow, hq4]
    field_simp
    ring

/-! ### §23.18 Modular transformations -/

/-- The anharmonic map attached to a matrix mod 2. -/
noncomputable def anharmonicMap (a b c d : ZMod 2) (l : ℂ) : ℂ :=
  if b = 0 ∧ c = 0 then l
  else if a = 0 ∧ d = 0 then 1 - l
  else if b = 0 then 1 / l
  else if a = 0 then 1 / (1 - l)
  else if c = 0 then -l / (1 - l)
  else 1 - 1 / l

/-- The six elements of `SL(2, ZMod 2)`. -/
private lemma zmod_two_sl2_cases (a b c d : ZMod 2) (h : a * d - b * c = 1) :
    (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0) ∨
    (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
    (a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨ (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 0) := by
  revert a b c d; decide

/-- The anharmonic maps compose like the matrices mod 2. -/
private lemma anharmonicMap_mul (a b c d a' b' c' d' : ZMod 2) (h : a * d - b * c = 1)
    (h' : a' * d' - b' * c' = 1) {l : ℂ} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    anharmonicMap (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') l =
      anharmonicMap a b c d (anharmonicMap a' b' c' d' l) := by
  have h1' : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : l - 1 ≠ 0 := sub_ne_zero.mpr h1
  rcases zmod_two_sl2_cases a b c d h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  rcases zmod_two_sl2_cases a' b' c' d' h' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  (try simp (config := {decide := true}) only [anharmonicMap, ite_true, ite_false]) <;>
  first | ring1 | (field_simp; done) | (field_simp; ring1) |
    (simp only [sub_sub_cancel]; field_simp; ring1) |
    (rw [show 1 - 1 / (1 - l) = -l / (1 - l) by field_simp; ring]; field_simp; ring1) |
    (rw [show 1 - 1 / (1 - l) = -l / (1 - l) by field_simp; ring]; field_simp)

/-- The anharmonic map of `A ∈ SL(2, ℤ)`, through its reduction mod 2. -/
noncomputable def anharmonicMapSL (A : SL(2, ℤ)) (l : ℂ) : ℂ :=
  anharmonicMap (A 0 0) (A 0 1) (A 1 0) (A 1 1) l

/-- The determinant condition mod 2. -/
private lemma det_cast_zmod_two (A : SL(2, ℤ)) :
    ((A 0 0 : ℤ) : ZMod 2) * (A 1 1 : ℤ) - (A 0 1 : ℤ) * (A 1 0 : ℤ) = 1 := by
  have h := A.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun x : ℤ => (x : ZMod 2)) h
  push_cast at this
  exact this

/-- `ψ_{AB} = ψ_A ∘ ψ_B` away from `0, 1`. -/
private lemma anharmonicMapSL_mul (A B : SL(2, ℤ)) {l : ℂ} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    anharmonicMapSL (A * B) l = anharmonicMapSL A (anharmonicMapSL B l) := by
  have e : ∀ i j, ((A * B) i j : ZMod 2) = (A i 0 : ZMod 2) * (B 0 j) + (A i 1) * (B 1 j) := by
    intro i j
    have : (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]; push_cast; rfl
  unfold anharmonicMapSL
  rw [e, e, e, e]
  exact anharmonicMap_mul _ _ _ _ _ _ _ _ (det_cast_zmod_two A) (det_cast_zmod_two B) h0 h1

/-- `ψ_1 = id`. -/
private lemma anharmonicMapSL_one (l : ℂ) : anharmonicMapSL 1 l = l := by
  simp [anharmonicMapSL, anharmonicMap]

/-- `λ(τ) ≠ 0, 1` on `ℍ`. -/
private lemma modularLambda_ne_zero_and_ne_one (τ : ℍ) : modularLambda τ ≠ 0 ∧
    modularLambda τ ≠ 1 := by
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero τ.im_pos
  have hj := jacobiThetaNull_fourth_power τ τ.im_pos
  refine ⟨div_ne_zero (pow_ne_zero _ n2) (pow_ne_zero _ n3), fun h => ?_⟩
  rw [modularLambda, div_eq_one_iff_eq (pow_ne_zero _ n3)] at h
  exact pow_ne_zero 4 n4 (by linear_combination -hj - h)

/-- `λ(τ + 1) = -λ/(1 - λ)`. -/
private lemma modularLambda_T_smul (τ : ℍ) :
    modularLambda (ModularGroup.T • τ : ℍ) = -modularLambda τ / (1 - modularLambda τ) := by
  have hc : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
    rw [modular_T_smul, coe_vadd]; push_cast; ring
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero τ.im_pos
  have hj := jacobiThetaNull_fourth_power τ τ.im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4 hj
  rw [hc, modularLambda, modularLambda]
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau]
  rw [jacobiThetaTwoTau_add_one, jacobiThetaThreeTau_add_one]
  have he : cexp (π * I / 4) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul]; push_cast
    rw [show (4 : ℂ) * (π * I / 4) = π * I by ring, exp_pi_mul_I]
  have h1 : 1 - jacobiThetaTwoTau 0 τ ^ 4 / jacobiThetaThreeTau 0 τ ^ 4 =
      jacobiThetaFourTau 0 τ ^ 4 / jacobiThetaThreeTau 0 τ ^ 4 := by
    field_simp; linear_combination hj
  rw [h1, mul_pow, he]
  field_simp

/-- `λ(-1/τ) = 1 - λ`. -/
private lemma modularLambda_S_smul (τ : ℍ) :
    modularLambda (ModularGroup.S • τ : ℍ) = 1 - modularLambda τ := by
  have hc : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / τ := by
    rw [modular_S_smul, coe_mk, inv_neg, neg_div, one_div]
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero τ.im_pos
  have hj := jacobiThetaNull_fourth_power τ τ.im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4 hj
  have t3 := jacobiThetaThreeTau_neg_inv τ.im_pos 0
  have t4 := jacobiThetaFourTau_neg_inv τ.im_pos 0
  simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, Complex.exp_zero, one_mul] at t3 t4
  have hs : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0))
  rw [hc, modularLambda, modularLambda]
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau]
  rw [← t3, ← t4, mul_pow, mul_pow]
  set s := (-I * (τ : ℂ)) ^ (1 / 2 : ℂ)
  field_simp
  linear_combination -hj

/-- `λ(Aτ) = ψ_A(λ(τ))` for all `A ∈ SL(2, ℤ)` (induction over the generators `S`, `T`). -/
private lemma modularLambda_smul_eq_anharmonicMapSL (A : SL(2, ℤ)) (τ : ℍ) :
    modularLambda (A • τ : ℍ) = anharmonicMapSL A (modularLambda τ) := by
  have hA : A ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  revert τ
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    intro τ
    rcases hx with rfl | rfl
    · rw [modularLambda_S_smul]
      simp (config := {decide := true}) [anharmonicMapSL, anharmonicMap]
    · rw [modularLambda_T_smul]
      simp (config := {decide := true}) [anharmonicMapSL, anharmonicMap]
  | one => intro τ; rw [one_smul, anharmonicMapSL_one]
  | mul x y _ _ hx hy =>
    intro τ
    obtain ⟨h0, h1⟩ := modularLambda_ne_zero_and_ne_one τ
    rw [mul_smul, hx, hy, anharmonicMapSL_mul x y h0 h1]
  | inv x _ hx =>
    intro τ
    obtain ⟨h0, h1⟩ := modularLambda_ne_zero_and_ne_one (x⁻¹ • τ)
    have := hx (x⁻¹ • τ)
    rw [smul_inv_smul] at this
    rw [this, ← anharmonicMapSL_mul _ _ h0 h1, inv_mul_cancel, anharmonicMapSL_one]

/-- DLMF 23.18.1–23.18.2: `λ(𝒜τ)` equals `λ`, `1 - λ`, `1/λ`, `1/(1 - λ)`, `λ/(λ - 1)`,
`1 - 1/λ` according as `[a b; c d]` has parities `[o e; e o]`, `[e o; o e]`, `[o e; o o]`,
`[e o; o o]`, `[o o; e o]`, `[o o; o e]` (`e` even, `o` odd), for `ℑτ > 0`. -/
@[dlmf 23.18.E1, dlmf 23.18.E2]
theorem modularLambda_smul (A : SL(2, ℤ)) (τ : ℍ) :
    let a := A 0 0; let b := A 0 1; let c := A 1 0; let d := A 1 1
    let l := modularLambda τ; let l' := modularLambda (A • τ : ℍ)
    (Odd a → Even b → Even c → Odd d → l' = l) ∧
    (Even a → Odd b → Odd c → Even d → l' = 1 - l) ∧
    (Odd a → Even b → Odd c → Odd d → l' = 1 / l) ∧
    (Even a → Odd b → Odd c → Odd d → l' = 1 / (1 - l)) ∧
    (Odd a → Odd b → Even c → Odd d → l' = l / (l - 1)) ∧
    (Odd a → Odd b → Odd c → Even d → l' = 1 - 1 / l) := by
  intro a b c d l l'
  have key : l' = anharmonicMap (a : ZMod 2) b c d l := modularLambda_smul_eq_anharmonicMapSL A τ
  have hl1 : l - 1 = -(1 - l) := by ring
  simp only [← ZMod.intCast_eq_one_iff_odd, ← ZMod.intCast_eq_zero_iff_even]
  refine ⟨fun ha hb hc hd => ?_, fun ha hb hc hd => ?_, fun ha hb hc hd => ?_,
    fun ha hb hc hd => ?_, fun ha hb hc hd => ?_, fun ha hb hc hd => ?_⟩ <;>
  rw [key, ha, hb, hc, hd] <;> simp (config := {decide := true}) [anharmonicMap] <;>
  rw [hl1, div_neg, neg_div]

/-- DLMF 23.18.3: if `a - 1, b, c, d - 1` are all even then `λ(𝒜τ) = λ(τ)`. -/
@[dlmf 23.18.E3]
theorem modularLambda_smul_of_even (A : SL(2, ℤ)) (τ : ℍ) (ha : Even (A 0 0 - 1))
    (hb : Even (A 0 1)) (hc : Even (A 1 0)) (hd : Even (A 1 1 - 1)) :
    modularLambda (A • τ : ℍ) = modularLambda τ := by
  have hao : Odd (A 0 0) := by
    obtain ⟨r, hr⟩ := ha; exact ⟨r, by omega⟩
  have hdo : Odd (A 1 1) := by
    obtain ⟨r, hr⟩ := hd; exact ⟨r, by omega⟩
  exact (modularLambda_smul A τ).1 hao hb hc hdo

open Topology in
/-- §23.18 after 23.18.3: `λ` is a cusp form of level zero for the subgroup of 23.18.3, which is
the principal congruence subgroup `Γ(2)`. -/
@[dlmf 23.18.E3]
theorem isCuspForm_modularLambda : IsCuspForm (CongruenceSubgroup.Gamma 2) 0 modularLambda := by
  have hdiff : ∀ τ : ℂ, 0 < τ.im → DifferentiableAt ℂ modularLambda τ := fun τ hτ => by
    obtain ⟨-, n3, -⟩ := jacobiThetaNullTau_ne_zero hτ
    exact ((differentiableAt_jacobiThetaTwoTau_zero hτ).pow 4).div
        ((differentiableAt_jacobiThetaThreeTau_zero hτ).pow 4)
      (pow_ne_zero 4 n3)
  have hper : Function.Periodic modularLambda 2 := fun τ => by
    simp only [modularLambda, jacobiThetaTwoNullTau, jacobiThetaThreeNullTau]
    rw [show τ + 2 = τ + 1 + 1 by ring, jacobiThetaTwoTau_add_one, jacobiThetaTwoTau_add_one,
      jacobiThetaThreeTau_add_one, jacobiThetaFourTau_add_one, mul_pow, mul_pow, ← mul_assoc,
      ← mul_pow, ← Complex.exp_add,
      show π * I / 4 + π * I / 4 = π * I / 2 by ring, ← Complex.exp_nat_mul]
    rw [show ((4 : ℕ) : ℂ) * (π * I / 2) = 2 * π * I by push_cast; ring, Complex.exp_two_pi_mul_I,
      one_mul]
  set Iinf : Filter ℂ := Filter.comap Complex.im Filter.atTop with hI
  have hev : ∀ᶠ τ in Iinf, 0 < τ.im := by
    rw [hI]; exact Filter.preimage_mem_comap (Filter.Ioi_mem_atTop 0)
  have hθ3 : Filter.Tendsto (fun τ => jacobiThetaThreeTau 0 τ) Iinf (𝓝 1) := by
    have h1 := isBigO_at_im_infty_jacobiTheta_sub_one
    have h2 : Filter.Tendsto (fun τ : ℂ => Real.exp (-π * τ.im)) Iinf (𝓝 0) := by
      have : Filter.Tendsto (fun τ : ℂ => π * τ.im) Iinf Filter.atTop :=
        Filter.tendsto_comap.const_mul_atTop Real.pi_pos
      refine (Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp this)).congr
        fun τ => ?_
      simp [neg_mul]
    have h3 := (h1.trans_tendsto h2)
    have h4 := h3.add_const 1
    simp only [sub_add_cancel, zero_add] at h4
    refine h4.congr fun τ => ?_
    simp [jacobiThetaThreeTau, jacobiTheta_eq_jacobiTheta₂]
  have hθ4 : Filter.Tendsto (fun τ => jacobiThetaFourTau 0 τ) Iinf (𝓝 1) := by
    have hs : Filter.Tendsto (fun τ : ℂ => τ + 1) Iinf Iinf := by
      rw [hI, Filter.tendsto_comap_iff]
      simpa [Function.comp_def] using Filter.tendsto_comap
    refine (hθ3.comp hs).congr fun τ => ?_
    simp [jacobiThetaThreeTau_add_one]
  have hzero : Filter.Tendsto modularLambda Iinf (𝓝 0) := by
    have := ((hθ3.pow 4).sub (hθ4.pow 4)).div (hθ3.pow 4) (by norm_num)
    simp only [one_pow, sub_self, zero_div] at this
    refine this.congr' ?_
    filter_upwards [hev] with τ hτ
    have hj := jacobiThetaNull_fourth_power τ hτ
    simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at hj
    simp only [Pi.div_apply, modularLambda, jacobiThetaTwoNullTau, jacobiThetaThreeNullTau]
    rw [hj]; ring
  have hhol : ∀ᶠ τ in Iinf, DifferentiableAt ℂ modularLambda τ := hev.mono hdiff
  have hbd : Filter.BoundedAtFilter Iinf modularLambda :=
    Filter.ZeroAtFilter.boundedAtFilter hzero
  set F := Function.Periodic.cuspFunction 2 modularLambda
  have hF0 : DifferentiableAt ℂ F 0 :=
    Function.Periodic.differentiableAt_cuspFunction_zero (by norm_num) hper hhol hbd
  have hFn : ∀ᶠ q in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ F q :=
    Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero (by norm_num) hper
      hhol
  have hFa : AnalyticAt ℂ F 0 := by
    refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
    have := hFn
    rw [eventually_nhdsWithin_iff] at this
    filter_upwards [this] with q hq
    by_cases h0 : q = 0
    · rw [h0]; exact hF0
    · exact hq h0
  refine ⟨⟨?_, fun A hA => ⟨1, fun τ => ?_⟩⟩, F, hFa,
    Function.Periodic.cuspFunction_zero_of_zero_at_inf (by norm_num) hzero, fun τ => ?_⟩
  · have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
    exact (DifferentiableOn.analyticOnNhd (fun z hz => (hdiff z hz).differentiableWithinAt)
      hU).meromorphicOn
  · simp only [Int.cast_zero, zero_div, cpow_zero, one_mul]
    rw [CongruenceSubgroup.Gamma_mem] at hA
    obtain ⟨h1, h2, h3, h4⟩ := hA
    rw [modularLambda_smul_eq_anharmonicMapSL, anharmonicMapSL, h1, h2, h3, h4]
    simp [anharmonicMap]
  · rw [← Function.Periodic.eq_cuspFunction (by norm_num) hper τ]
    congr 1
    simp only [Function.Periodic.qParam]
    congr 1
    push_cast
    ring

/-- DLMF 23.18.5: for `𝒜 ∈ SL(2, ℤ)` with `c > 0` and `ℑτ > 0`,
`η(𝒜τ) = ε(𝒜)(-i(cτ + d))^{1/2} η(τ)` with the principal square root. -/
@[dlmf 23.18.E5]
theorem eta_smul (A : SL(2, ℤ)) (hc : 0 < A 1 0) (τ : ℍ) :
    η (A • τ : ℍ) = etaMultiplier A * (-I * ((A 1 0 : ℂ) * τ + A 1 1)) ^ (1 / 2 : ℂ) *
      η (τ : ℂ) := by
  sorry

/-- `η(Aτ)²⁴ = (cτ + d)¹² η(τ)²⁴`. -/
private lemma eta_smul_pow_twentyFour (A : SL(2, ℤ)) (τ : ℍ) :
    η (A • τ : ℍ) ^ 24 = ((A 1 0 : ℂ) * τ + A 1 1) ^ 12 * η (τ : ℂ) ^ 24 := by
  have hg : (Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    MonoidHom.mem_range.mpr ⟨A, rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hg τ
  have hs : (Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) • τ = A • τ := rfl
  rw [hs] at h
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) τ =
      (A 1 0 : ℂ) * τ + A 1 1 := by
    simp [denom, Matrix.SpecialLinearGroup.mapGL]
  rw [hd] at h
  simpa [CuspForm.coe_discriminant, ModularForm.discriminant] using h

/-- `η` is continuous on `ℍ`. -/
private lemma continuous_eta_upperHalfPlane : Continuous fun τ : ℍ => η (τ : ℂ) :=
  continuous_iff_continuousAt.mpr fun τ =>
    ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).continuousAt).comp
      UpperHalfPlane.continuous_coe.continuousAt

/-- §23.18, last sentence: `η` is a modular function of level `1/2` for `SL(2, ℤ)`. -/
@[dlmf 23.18.E5]
theorem isModularFunction_eta : IsModularFunction ⊤ 1 ModularForm.eta := by
  refine ⟨?_, fun A _ => ?_⟩
  · have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
    exact (DifferentiableOn.analyticOnNhd (fun z hz =>
      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt)
      hU).meromorphicOn
  set s : ℍ → ℂ := fun τ => ((A 1 0 : ℂ) * τ + A 1 1) ^ (1 / 2 : ℂ) with hs
  have hden : ∀ τ : ℍ, (A 1 0 : ℂ) * τ + A 1 1 ≠ 0 := fun τ => by
    have := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) τ
    simpa [denom, Matrix.SpecialLinearGroup.mapGL] using this
  have hs0 : ∀ τ, s τ ≠ 0 := fun τ => by
    simp only [hs]; exact cpow_ne_zero_iff.mpr (Or.inl (hden τ))
  have hη0 : ∀ τ : ℍ, η (τ : ℂ) ≠ 0 := fun τ => ModularForm.eta_ne_zero τ.im_pos
  set g : ℍ → ℂ := fun τ => η (A • τ : ℍ) / (s τ * η (τ : ℂ)) with hgdef
  have hg24 : ∀ τ, g τ ^ 24 = 1 := fun τ => by
    simp only [hgdef, div_pow, mul_pow, eta_smul_pow_twentyFour]
    have : s τ ^ 24 = ((A 1 0 : ℂ) * τ + A 1 1) ^ 12 := by
      simp only [hs]
      rw [← cpow_nat_mul]; norm_num
    rw [this, div_self (mul_ne_zero (pow_ne_zero _ (hden τ)) (pow_ne_zero _ (hη0 τ)))]
  have hscont : Continuous s := by
    by_cases hc : (A 1 0 : ℂ) = 0
    · simp only [hs, hc, zero_mul, zero_add]; exact continuous_const
    · refine continuous_iff_continuousAt.mpr fun τ => ?_
      have hslit : (A 1 0 : ℂ) * τ + A 1 1 ∈ Complex.slitPlane := by
        refine Or.inr ?_
        have hc' : (A 1 0 : ℝ) ≠ 0 := by exact_mod_cast (by exact_mod_cast hc : (A 1 0 : ℤ) ≠ 0)
        simp [hc', τ.im_pos.ne']
      exact (continuousAt_cpow_const hslit).comp (f := fun τ : ℍ => (A 1 0 : ℂ) * τ + A 1 1)
        ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const).continuousAt
  have hgcont : Continuous g := by
    refine Continuous.div ?_ (hscont.mul continuous_eta_upperHalfPlane) fun τ =>
        mul_ne_zero (hs0 τ) (hη0 τ)
    have he : (fun τ : ℍ => η ((A • τ : ℍ) : ℂ)) = fun τ : ℍ => η (mobius A τ) :=
      funext fun τ => by rw [mobius_coe]
    rw [he]
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    have hpos : 0 < (mobius A τ).im := by rw [← mobius_coe]; exact (A • τ).im_pos
    refine (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hpos).continuousAt.comp
      (f := fun τ : ℍ => mobius A τ) ?_
    simp only [mobius]
    exact (((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const).div
      ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const) hden).continuousAt
  have hT : IsDiscrete {w : ℂ | w ^ 24 = 1} := by
    refine Set.Finite.isDiscrete ?_
    have := Polynomial.finite_setOfPred_isRoot (p := (Polynomial.X ^ 24 - Polynomial.C (1 : ℂ)))
      (Polynomial.X_pow_sub_C_ne_zero (by norm_num) 1)
    simpa [sub_eq_zero] using this
  have hconst : ∀ τ, g τ = g UpperHalfPlane.I := fun τ =>
    isPreconnected_univ.constant_of_mapsTo hT hgcont.continuousOn (fun τ _ => hg24 τ)
      (Set.mem_univ _) (Set.mem_univ _)
  refine ⟨g UpperHalfPlane.I, fun τ => ?_⟩
  rw [← hconst τ]
  simp only [hgdef, Int.cast_one]
  rw [show ((1 : ℂ) / 2) = 1 / 2 from rfl]
  field_simp [hs0 τ, hη0 τ]
  rfl

/-! ### §23.19 Interrelations -/

/-- `|e^{iπτ}| < 1` on `ℍ`. -/
private lemma norm_exp_pi_I_mul_lt_one (τ : ℍ) : ‖cexp (π * I * τ)‖ < 1 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  have : (↑π * I * (τ : ℂ)).re = -(π * (τ : ℂ).im) := by simp
  rw [this, neg_lt_zero]
  exact mul_pos Real.pi_pos τ.im_pos

/-- `η(2τ)² = θ₂(0|τ)η(τ)/2`. -/
private lemma eta_two_mul_sq (τ : ℍ) :
    η (2 * (τ : ℂ)) ^ 2 = jacobiThetaTwoTau 0 τ * η (τ : ℂ) / 2 := by
  set τ2 : ℍ := ⟨2 * (τ : ℂ), by simpa using τ.im_pos⟩
  obtain ⟨hm2, he2⟩ := eta_hasProd τ2
  obtain ⟨hm, he⟩ := eta_hasProd τ
  obtain ⟨mθ, eθ⟩ := jacobiThetaTwoNullTau_prod τ.im_pos
  set q := cexp (π * I * τ) with hq
  have hq2 : cexp (π * I * (τ2 : ℂ)) = q ^ 2 := by
    rw [hq, ← Complex.exp_nat_mul]; congr 1; simp [τ2]; ring
  rw [hq2] at hm2 he2
  have h2 : η (2 * (τ : ℂ)) = η (τ2 : ℂ) := rfl
  rw [h2, he2]
  simp only [jacobiThetaTwoNullTau] at eθ
  rw [eθ, he]
  have hprod := (mθ.hasProd.mul hm).tprod_eq
  have e1 : cexp (π * I * (τ2 : ℂ) / 12) ^ 2 = cexp (π * I * τ / 4) * cexp (π * I * τ / 12) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; simp [τ2]; ring
  rw [mul_pow, e1, ← hm2.multipliable.tprod_pow]
  rw [show ∀ a b c d : ℂ, 2 * a * c * (b * d) / 2 = a * b * (c * d) by intros; ring]
  congr 1
  rw [← hprod]
  refine tprod_congr fun n => ?_
  rw [← pow_mul, show 2 * (2 * (n + 1)) = 2 * (n + 1) * 2 by ring, pow_mul]
  ring

/-- `η(τ/2)² = θ₄(0|τ)η(τ)`. -/
private lemma eta_div_two_sq (τ : ℍ) :
    η ((τ : ℂ) / 2) ^ 2 = jacobiThetaFourTau 0 τ * η (τ : ℂ) := by
  set τh : ℍ := ⟨(τ : ℂ) / 2, by simpa using τ.im_pos⟩
  obtain ⟨hmh, heh⟩ := eta_hasProd τh
  obtain ⟨hm, he⟩ := eta_hasProd τ
  obtain ⟨-, eθ⟩ := jacobiThetaFourNullTau_prod τ.im_pos
  set q := cexp (π * I * τ) with hq
  have hqh : ∀ n : ℕ, cexp (π * I * (τh : ℂ)) ^ (2 * (n + 1)) = q ^ (n + 1) := by
    intro n
    rw [pow_mul, hq, ← Complex.exp_nat_mul]; congr 2; simp [τh]; ring
  simp_rw [hqh] at heh
  have h2 : η ((τ : ℂ) / 2) = η (τh : ℂ) := rfl
  have hq1 : ‖q‖ < 1 := norm_exp_pi_I_mul_lt_one τ
  have hA : Multipliable (fun k : ℕ => 1 - q ^ (2 * k + 1)) := by
    have hs : Summable (fun k : ℕ => -q ^ (2 * k + 1)) := by
      have : Summable (fun k : ℕ => q * (q ^ 2) ^ k) :=
        (summable_geometric_of_norm_lt_one (by rw [norm_pow]; nlinarith [norm_nonneg q])).mul_left q
      refine this.neg.congr fun k => ?_
      rw [← pow_mul, ← pow_succ']
    simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hs
  have hB : Multipliable (fun k : ℕ => 1 - q ^ (2 * (k + 1))) := hm.multipliable
  have hsplit : ∏' n : ℕ, (1 - q ^ (n + 1)) =
      (∏' k : ℕ, (1 - q ^ (2 * k + 1))) * ∏' k : ℕ, (1 - q ^ (2 * (k + 1))) := by
    rw [← tprod_even_mul_odd (f := fun n : ℕ => 1 - q ^ (n + 1)) hA
      (by simpa [show ∀ k : ℕ, 2 * k + 1 + 1 = 2 * (k + 1) by intro k; ring] using hB)]
    congr 1
  have hθ : jacobiThetaFourTau 0 τ =
      (∏' k : ℕ, (1 - q ^ (2 * (k + 1)))) * (∏' k : ℕ, (1 - q ^ (2 * k + 1))) ^ 2 := by
    simp only [jacobiThetaFourNullTau] at eθ
    rw [eθ, ← (hB.hasProd.mul (hA.hasProd.pow 2)).tprod_eq]
  rw [h2, heh, hsplit, hθ, he]
  have e1 : cexp (π * I * (τh : ℂ) / 12) ^ 2 = cexp (π * I * τ / 12) := by
    rw [← Complex.exp_nat_mul]; congr 1; simp [τh]; ring
  rw [mul_pow, e1]
  ring

/-- DLMF 23.19.1: `λ(τ) = 16(η²(2τ)η(τ/2)/η³(τ))⁸`, `ℑτ > 0`. -/
@[dlmf 23.19.E1]
theorem modularLambda_eq_eta (τ : ℍ) :
    modularLambda τ = 16 * (η (2 * τ) ^ 2 * η ((τ : ℂ) / 2) / η (τ : ℂ) ^ 3) ^ 8 := by
  have hA := eta_two_mul_sq τ
  have hB := eta_div_two_sq τ
  have hC := eta_pow_three_eq_jacobiThetaOneDerivNullTau τ
  rw [jacobiThetaOneDerivNullTau_eq_mul τ.im_pos] at hC
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero τ.im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4 hC
  have hη : η (τ : ℂ) ≠ 0 := by
    intro h; rw [h] at hC
    exact mul_ne_zero (mul_ne_zero n2 n3) n4 (by linear_combination -2 * hC)
  rw [show (η (2 * τ) ^ 2 * η ((τ : ℂ) / 2) / η (τ : ℂ) ^ 3) ^ 8 =
      (η (2 * (τ : ℂ)) ^ 2) ^ 8 * (η ((τ : ℂ) / 2) ^ 2) ^ 4 / (η (τ : ℂ) ^ 3) ^ 8 by ring,
    hA, hB, hC, modularLambda]
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau]
  field_simp
  rw [show η (τ : ℂ) ^ 12 = (η (τ : ℂ) ^ 3) ^ 4 by ring, hC]
  ring

/-- DLMF 23.19.2: `J(τ) = (4/27)(1 - λ + λ²)³/(λ(1 - λ))²`, `ℑτ > 0`. -/
@[dlmf 23.19.E2]
theorem kleinJ_eq_modularLambda (τ : ℍ) :
    kleinJ τ = 4 / 27 * (1 - modularLambda τ + modularLambda τ ^ 2) ^ 3 /
      (modularLambda τ * (1 - modularLambda τ)) ^ 2 := by
  rw [← thetaKleinJ_eq_kleinJ, thetaKleinJ_eq_modularLambda]

/-- DLMF 23.19.3: `J(τ) = g₂³/(g₂³ - 27g₃²)` for the invariants of the lattice with generators
`1` and `τ` (half-periods `ω₁ = 1/2`, `ω₃ = τ/2`), `ℑτ > 0`. -/
@[dlmf 23.19.E3]
theorem kleinJ_eq_invariants (τ : ℍ) :
    kleinJ τ = (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).g₂ ^ 3 /
      ((HalfPeriods.ofTau (1 / 2) (by norm_num) τ).g₂ ^ 3 -
        27 * (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).g₃ ^ 2) := by
  rw [← thetaKleinJ_eq_kleinJ, thetaKleinJ_eq_invariants]

/-- §23.18 after 23.18.4: `J` is a modular function of level zero for `SL(2, ℤ)`.
Corrected from the printed DLMF statement: DLMF calls `J` a "modular form of level zero", but `J`
has a pole at `q = 0`, so it is not a modular form in the sense of DLMF 23.15(i) (which requires
analyticity at `q = 0`); it is a modular function. -/
@[dlmf 23.18.E4]
theorem isModularFunction_kleinJ : IsModularFunction ⊤ 0 (kleinJ ∘ ofComplex) := by
  refine ⟨ModularForm.analyticOnNhd_kleinJ_comp_ofComplex.meromorphicOn,
    fun A _ => ⟨1, fun τ => ?_⟩⟩
  simp only [Function.comp_apply, ofComplex_apply, Int.cast_zero, zero_div, cpow_zero, one_mul]
  exact ModularForm.kleinJ_smul A τ

open ModularForm in
/-- DLMF 23.19.4: `Δ = (2π)¹²η²⁴(τ)` for the lattice with generators `1` and `τ`, `ℑτ > 0`. -/
@[dlmf 23.19.E4]
theorem latticeDiscriminant_eq_eta (τ : ℍ) :
    latticeDiscriminant (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).periodPair =
      (2 * π) ^ 12 * η (τ : ℂ) ^ 24 := by
  have h4 := G_ofTau_eq_two_mul_riemannZeta_mul_E τ (k := 4) (by norm_num)
  have h6 := G_ofTau_eq_two_mul_riemannZeta_mul_E τ (k := 6) (by norm_num)
  have hΔ := discriminant_eq_E₄_cube_sub_E₆_sq τ
  simp only [latticeDiscriminant, PeriodPair.g₂, PeriodPair.g₃]
  rw [h4, h6]
  have z4 : riemannZeta ((4 : ℕ) : ℂ) = π ^ 4 / 90 := by exact_mod_cast riemannZeta_four
  have z6 : riemannZeta ((6 : ℕ) : ℂ) = π ^ 6 / 945 := by exact_mod_cast riemannZeta_six_eq_pi_pow
  rw [z4, z6]
  have : η (τ : ℂ) ^ 24 = discriminant τ := rfl
  rw [this, hΔ]
  ring

end DLMF.Weierstrass
