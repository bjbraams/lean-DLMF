/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.SolutionsDefs
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Other elementary solutions of the Painlevé equations (DLMF §32.9)

DLMF normalization (`DLMF.Painleve.Defs`). The nonrational elementary solutions 32.9.1–32.9.3,
32.9.7, 32.9.8 and 32.9.13 involve powers and logarithms; they are stated with the principal
branches (`Complex.cpow`, `Complex.log`) on open subsets of the slit plane `ℂ ∖ (-∞, 0]`,
where these are holomorphic. Any other branch differs by a constant factor (a root of unity)
or a constant shift of `ln z`, which is absorbed into the arbitrary constants. The first
integrals 32.9.6 and 32.9.12 are proved on preconnected open sets. The classification of
algebraic solutions (32.9.4–32.9.5, 32.9.9–32.9.11) is admitted.
-/

@[expose] public noncomputable section

open Set Filter Complex
open scoped Topology

namespace DLMF.Painleve

/-- The derivative of the principal power `z^a` on the slit plane, written as `a z^a / z`. -/
private lemma b32_hasDerivAt_cpow {a z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z ^ a) (a * z ^ a / z) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  refine (hasDerivAt_id z |>.cpow_const (c := a) (by simpa using hz)).congr_deriv ?_
  simp only [id_eq, mul_one]
  rw [cpow_sub _ _ hz0, cpow_one]
  ring

/-! ## `PIII` (§32.9(i)) -/

/-- DLMF 32.9.1: `w = κz^{1/3}` solves `PIII` with parameters `(μ, 0, 0, -μκ³)` on every open
subset of the slit plane, for `κ ≠ 0` (principal cube root; another branch multiplies `κ` by a
cube root of unity, which leaves `κ³` unchanged). -/
@[dlmf 32.9.E1]
theorem painleveIII_cbrt {κ μ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hUs : U ⊆ slitPlane)
    (hκ : κ ≠ 0) :
    IsPainleveIIIOn μ 0 0 (-μ * κ ^ 3) (fun z => κ * z ^ (1 / 3 : ℂ)) U := by
  have hz0 : ∀ z ∈ U, z ≠ 0 := fun z hz => slitPlane_ne_zero (hUs hz)
  have ht0 : ∀ z ∈ U, z ^ (1 / 3 : ℂ) ≠ 0 := fun z hz =>
    (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr (hz0 z hz)
  have ht3 : ∀ z : ℂ, (z ^ (1 / 3 : ℂ)) ^ 3 = z := fun z => by
    rw [one_div]; exact_mod_cast cpow_nat_inv_pow z (n := 3) (by norm_num)
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => κ * (1 / 3 * z ^ (1 / 3 : ℂ) / z)) (fun z hz => ?_) (fun z hz => ?_), hz0,
    fun z hz => mul_ne_zero hκ (ht0 z hz)⟩
  · exact (b32_hasDerivAt_cpow (hUs hz)).const_mul κ
  · have hzU := hz
    have ht := ht0 z hzU
    have hz := hz0 z hzU
    have h := (((b32_hasDerivAt_cpow (a := 1 / 3) (hUs hzU)).const_mul (1 / 3 : ℂ)).div
      (hasDerivAt_id z) hz).const_mul κ
    refine h.congr_deriv ?_
    have h3 := ht3 z
    simp only [painleveIIIRhs, id_eq]
    field_simp
    linear_combination (-9 * κ ^ 2 * μ * z) * h3

/-- DLMF 32.9.2: `w = z(κ(ln z)² + λ ln z + μ)` solves `PIII` with parameters
`(0, -2κ, 0, 4κμ - λ²)` on every open subset of the slit plane where `w ≠ 0` (principal
logarithm; another branch shifts `ln z` by a constant, which changes `λ, μ` but not
`4κμ - λ²`). -/
@[dlmf 32.9.E2]
theorem painleveIII_log {κ l μ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hUs : U ⊆ slitPlane)
    (hw : ∀ z ∈ U, z * (κ * log z ^ 2 + l * log z + μ) ≠ 0) :
    IsPainleveIIIOn 0 (-2 * κ) 0 (4 * κ * μ - l ^ 2)
      (fun z => z * (κ * log z ^ 2 + l * log z + μ)) U := by
  have hz0 : ∀ z ∈ U, z ≠ 0 := fun z hz => slitPlane_ne_zero (hUs hz)
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => κ * log z ^ 2 + (l + 2 * κ) * log z + (μ + l)) (fun z hz => ?_)
    (fun z hz => ?_), hz0, hw⟩
  · have hL := hasDerivAt_log (hUs hz)
    have hz := hz0 z hz
    refine ((hasDerivAt_id z).mul ((((hL.pow 2).const_mul κ).add (hL.const_mul l)).add_const
      μ)).congr_deriv ?_
    simp only [id_eq, Pi.add_apply, Pi.pow_apply]
    field_simp
    ring
  · have hL := hasDerivAt_log (hUs hz)
    have hwz := hw z hz
    have hD := right_ne_zero_of_mul hwz
    have hz := hz0 z hz
    refine ((((hL.pow 2).const_mul κ).add (hL.const_mul (l + 2 * κ))).add_const
      (μ + l)).congr_deriv ?_
    simp only [painleveIIIRhs]
    generalize log z = L at hD hwz ⊢
    generalize hE : κ * L ^ 2 + l * L + μ = D at hD hwz ⊢
    field_simp
    linear_combination (-(κ * L ^ 2 + (4 * κ + l) * L + 4 * κ + 2 * l + μ)) * hE

/-- DLMF 32.9.3: `w = z^{ν-1}/(κz^{2ν} + λz^ν + μ)` solves `PIII` with parameters
`(-ν²λ, 0, ν²(λ² - 4κμ), 0)` on every open subset of the slit plane where the denominator does
not vanish (principal powers). -/
@[dlmf 32.9.E3]
theorem painleveIII_power {κ l μ ν : ℂ} {U : Set ℂ} (hU : IsOpen U) (hUs : U ⊆ slitPlane)
    (hD : ∀ z ∈ U, κ * z ^ (2 * ν) + l * z ^ ν + μ ≠ 0) :
    IsPainleveIIIOn (-ν ^ 2 * l) 0 (ν ^ 2 * (l ^ 2 - 4 * κ * μ)) 0
      (fun z => z ^ (ν - 1) / (κ * z ^ (2 * ν) + l * z ^ ν + μ)) U := by
  sorry

/-- DLMF §32.9(i), 32.9.4–32.9.5: with `γ = 0`, `α = 1`, `δ = -1` (the normalization of
§32.2(ii) when `γ = 0`, `αδ ≠ 0`), `PIII` has algebraic solutions iff `β = 2n`, `n ∈ ℤ`; these
are rational in `ζ = z^{1/3}`, `w = P_{n²+1}(ζ)/Q_{n²}(ζ)` with polynomials of degrees `n² + 1`
and `n²` without common zeros (for some holomorphic cube root `ζ` on the domain). -/
@[dlmf 32.9.E4, dlmf 32.9.E5]
theorem painleveIII_algebraic_iff (β : ℂ) :
    ((∃ (w : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧ U.Nonempty ∧ IsAlgebraicOn w U ∧
        IsPainleveIIIOn 1 β 0 (-1) w U) ↔ ∃ n : ℤ, β = 2 * n) ∧
      ∀ (w : ℂ → ℂ) (U : Set ℂ) (n : ℤ), IsOpen U → IsPreconnected U → U.Nonempty →
        IsAlgebraicOn w U → β = 2 * n → IsPainleveIIIOn 1 β 0 (-1) w U →
        ∃ (ζ : ℂ → ℂ) (P Q : Polynomial ℂ), P.natDegree = n.natAbs ^ 2 + 1 ∧
          Q.natDegree = n.natAbs ^ 2 ∧ IsCoprime P Q ∧
          ∀ z ∈ U, ζ z ^ 3 = z ∧ Q.eval (ζ z) ≠ 0 ∧ w z = P.eval (ζ z) / Q.eval (ζ z) := by
  sorry

/-- The derivative of a first integral along a solution vanishes, so it is constant on a
preconnected open set. -/
private lemma b32_const_of_hasDerivAt_zero {I : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (hI : ∀ z ∈ U, HasDerivAt I 0 z) : ∃ C, ∀ z ∈ U, I z = C :=
  hU.exists_is_const_of_deriv_eq_zero hc
    (fun z hz => (hI z hz).differentiableAt.differentiableWithinAt) fun z hz => (hI z hz).deriv

/-- DLMF 32.9.6: for `PIII` with `β = δ = 0`, the first integral
`z²(w')² + 2zww' = (C + 2αzw + γz²w²)w²` holds with a constant `C` on every preconnected open
set. -/
@[dlmf 32.9.E6]
theorem painleveIII_firstIntegral {α γ : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (h : IsPainleveIIIOn α 0 γ 0 w U) :
    ∃ C : ℂ, ∀ z ∈ U, z ^ 2 * deriv w z ^ 2 + 2 * z * w z * deriv w z =
      (C + 2 * α * z * w z + γ * z ^ 2 * w z ^ 2) * w z ^ 2 := by
  obtain ⟨C, hC⟩ := b32_const_of_hasDerivAt_zero (I := fun z =>
      (z ^ 2 * deriv w z ^ 2 + 2 * z * w z * deriv w z) / w z ^ 2 - 2 * α * z * w z -
        γ * z ^ 2 * w z ^ 2) hU hc fun z hz => by
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hw0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hA := ((hasDerivAt_id z).pow 2).mul (hv.pow 2)
    have hB := (((hasDerivAt_id z).const_mul 2).mul hw).mul hv
    have hD := (hA.add hB).div (hw.pow 2) (pow_ne_zero 2 hw0)
    have hE := ((hasDerivAt_id z).const_mul (2 * α)).mul hw
    have hF := (((hasDerivAt_id z).pow 2).const_mul γ).mul (hw.pow 2)
    refine ((hD.sub hE).sub hF).congr_deriv ?_
    simp only [painleveIIIRhs, id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
    field_simp
    ring
  refine ⟨C, fun z hz => ?_⟩
  have := hC z hz
  have hw0 := h.w_ne_zero z hz
  rw [← this]
  field_simp
  ring

/-- DLMF §32.9(i): for `PIII` with `α = γ = 0` the analogous first integral is
`z²(w')² - 2zww' + 2βzw + δz² = Cw²` (obtained from 32.9.6 by `w ↦ 1/w`), with a constant `C`
on every preconnected open set. -/
@[dlmf 32.9.i]
theorem painleveIII_firstIntegral' {β δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (h : IsPainleveIIIOn 0 β 0 δ w U) :
    ∃ C : ℂ, ∀ z ∈ U, z ^ 2 * deriv w z ^ 2 - 2 * z * w z * deriv w z + 2 * β * z * w z +
      δ * z ^ 2 = C * w z ^ 2 := by
  obtain ⟨C, hC⟩ := b32_const_of_hasDerivAt_zero (I := fun z =>
      (z ^ 2 * deriv w z ^ 2 - 2 * z * w z * deriv w z + 2 * β * z * w z + δ * z ^ 2) /
        w z ^ 2) hU hc fun z hz => by
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hw0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hA := ((hasDerivAt_id z).pow 2).mul (hv.pow 2)
    have hB := (((hasDerivAt_id z).const_mul 2).mul hw).mul hv
    have hE := ((hasDerivAt_id z).const_mul (2 * β)).mul hw
    have hF := ((hasDerivAt_id z).pow 2).const_mul δ
    refine ((((hA.sub hB).add hE).add hF).div (hw.pow 2) (pow_ne_zero 2 hw0)).congr_deriv ?_
    simp only [painleveIIIRhs, id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
    field_simp
    ring
  refine ⟨C, fun z hz => ?_⟩
  have := hC z hz
  have hw0 := h.w_ne_zero z hz
  rw [← this]
  field_simp

/-- DLMF §32.9(i): `PIII` with `α = β = γ = δ = 0` has the solutions `w = Cz^μ` (principal
power, on every open subset of the slit plane, `C ≠ 0`). -/
@[dlmf 32.9.i]
theorem painleveIII_zero_power {C μ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hUs : U ⊆ slitPlane)
    (hC : C ≠ 0) : IsPainleveIIIOn 0 0 0 0 (fun z => C * z ^ μ) U := by
  have hz0 : ∀ z ∈ U, z ≠ 0 := fun z hz => slitPlane_ne_zero (hUs hz)
  have hw0 : ∀ z ∈ U, C * z ^ μ ≠ 0 := fun z hz =>
    mul_ne_zero hC (by rw [Ne, cpow_eq_zero_iff]; exact fun h => hz0 z hz h.1)
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => C * (μ * z ^ μ / z))
    (fun z hz => (b32_hasDerivAt_cpow (hUs hz)).const_mul C) (fun z hz => ?_), hz0, hw0⟩
  have hzU := hz
  have hz := hz0 z hzU
  have hw := hw0 z hzU
  have ht : z ^ μ ≠ 0 := right_ne_zero_of_mul hw
  refine ((((b32_hasDerivAt_cpow (a := μ) (hUs hzU)).const_mul μ).div (hasDerivAt_id z)
    hz).const_mul C).congr_deriv ?_
  simp only [painleveIIIRhs, id_eq]
  field_simp
  ring

/-- DLMF §32.9(i): conversely, every solution of `PIII` with `α = β = γ = δ = 0` on a
preconnected open subset of the slit plane is `w = Cz^μ` for constants `C`, `μ`. -/
@[dlmf 32.9.i]
theorem painleveIII_zero_eq_power {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (hUs : U ⊆ slitPlane) (h : IsPainleveIIIOn 0 0 0 0 w U) :
    ∃ C μ : ℂ, ∀ z ∈ U, w z = C * z ^ μ := by
  sorry

/-! ## `PV` (§32.9(ii)) -/

/-- DLMF 32.9.7: `w = 1 + κz^{1/2}` solves `PV` with parameters `(μ, -1/8, -μκ², 0)` on every
open subset of the slit plane where `w ≠ 0`, for `κ ≠ 0` (principal square root; the other
branch replaces `κ` by `-κ`). -/
@[dlmf 32.9.E7]
theorem painleveV_sqrt {κ μ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hUs : U ⊆ slitPlane)
    (hκ : κ ≠ 0) (hw : ∀ z ∈ U, 1 + κ * z ^ (1 / 2 : ℂ) ≠ 0) :
    IsPainleveVOn μ (-1 / 8) (-μ * κ ^ 2) 0 (fun z => 1 + κ * z ^ (1 / 2 : ℂ)) U := by
  have hz0 : ∀ z ∈ U, z ≠ 0 := fun z hz => slitPlane_ne_zero (hUs hz)
  have ht0 : ∀ z ∈ U, z ^ (1 / 2 : ℂ) ≠ 0 := fun z hz =>
    (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr (hz0 z hz)
  have ht2 : ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z := fun z => by
    rw [one_div]; exact_mod_cast cpow_nat_inv_pow z (n := 2) (by norm_num)
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => κ * (1 / 2 * z ^ (1 / 2 : ℂ) / z)) (fun z hz => ?_) (fun z hz => ?_), hz0,
    hw, fun z hz h => mul_ne_zero hκ (ht0 z hz) (by linear_combination h)⟩
  · exact ((b32_hasDerivAt_cpow (hUs hz)).const_mul κ).const_add 1
  · have hzU := hz
    have ht := ht0 z hzU
    have hz := hz0 z hzU
    have hwz := hw z hzU
    have h := (((b32_hasDerivAt_cpow (a := 1 / 2) (hUs hzU)).const_mul (1 / 2 : ℂ)).div
      (hasDerivAt_id z) hz).const_mul κ
    refine h.congr_deriv ?_
    have h2 := ht2 z
    simp only [painleveVRhs, id_eq, add_sub_cancel_left]
    field_simp
    linear_combination (-(64 * κ ^ 3 * μ * z ^ (1 / 2 : ℂ) + 128 * κ ^ 4 * μ * (z ^ (1 / 2 : ℂ)) ^ 2
      + 64 * κ ^ 5 * μ * (z ^ (1 / 2 : ℂ)) ^ 3)) * h2

/-- DLMF 32.9.8: `w = κe^{μz}` solves `PV` with parameters `(0, 0, μ, -μ²/2)` on every open set
avoiding `z = 0` and the points where `w = 1`, for `κ ≠ 0`. -/
@[dlmf 32.9.E8]
theorem painleveV_exp {κ μ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hκ : κ ≠ 0)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, κ * exp (μ * z) ≠ 1) :
    IsPainleveVOn 0 0 μ (-μ ^ 2 / 2) (fun z => κ * exp (μ * z)) U := by
  have hd : ∀ z : ℂ, HasDerivAt (fun z => κ * exp (μ * z)) (μ * (κ * exp (μ * z))) z :=
    fun z => by
      have := (((hasDerivAt_id z).const_mul μ).cexp).const_mul κ
      exact this.congr_deriv (by simp only [id_eq]; ring)
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => μ * (κ * exp (μ * z)))
    (fun z _ => hd z) (fun z hz => ?_), h0, fun z _ => mul_ne_zero hκ (exp_ne_zero _), h1⟩
  have hzU := hz
  have hz := h0 z hzU
  have hw1 := sub_ne_zero.mpr (h1 z hzU)
  have he := exp_ne_zero (μ * z)
  refine ((hd z).const_mul μ).congr_deriv ?_
  simp only [painleveVRhs]
  field_simp
  ring

/-- DLMF §32.9(ii): `PV` with `α = β = 0` and `γ² + 2δ = 0` has the solutions `w = Ce^{γz}`
(DLMF writes `C exp(±√(-2δ) z)`; the sign must be that of `γ = ±√(-2δ)`, the other sign does
not give a solution when `γ ≠ 0`). Corollary of 32.9.8. -/
@[dlmf 32.9.ii]
theorem painleveV_exp' {C γ δ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hC : C ≠ 0)
    (hγδ : γ ^ 2 + 2 * δ = 0)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, C * exp (γ * z) ≠ 1) :
    IsPainleveVOn 0 0 γ δ (fun z => C * exp (γ * z)) U := by
  have hδ : δ = -γ ^ 2 / 2 := by linear_combination hγδ / 2
  rw [hδ]
  exact painleveV_exp hU hC h0 h1

/-- DLMF 32.9.9–32.9.11: `PV` with `δ = 0` has algebraic solutions if
`(α, β, γ) = (μ²/2, -(2n - 1)²/8, -1)` or `(α, β, γ) = ((2n - 1)²/8, -μ²/2, 1)` (`n ∈ ℤ`,
`μ` arbitrary); these are rational in `ζ = z^{1/2}`, `w = P_{n²-n+1}(ζ)/Q_{n²-n}(ζ)` with
polynomials of degrees `n² - n + 1` and `n² - n` without common zeros. -/
@[dlmf 32.9.E9, dlmf 32.9.E10, dlmf 32.9.E11]
theorem painleveV_exists_algebraic {α β γ μ : ℂ} {n : ℤ}
    (h : (α = μ ^ 2 / 2 ∧ β = -(2 * n - 1) ^ 2 / 8 ∧ γ = -1) ∨
      (α = (2 * n - 1) ^ 2 / 8 ∧ β = -μ ^ 2 / 2 ∧ γ = 1)) :
    ∃ (w ζ : ℂ → ℂ) (U : Set ℂ) (P Q : Polynomial ℂ), IsOpen U ∧ U.Nonempty ∧
      IsPainleveVOn α β γ 0 w U ∧ P.natDegree = (n ^ 2 - n + 1).toNat ∧
      Q.natDegree = (n ^ 2 - n).toNat ∧ IsCoprime P Q ∧
      ∀ z ∈ U, ζ z ^ 2 = z ∧ Q.eval (ζ z) ≠ 0 ∧ w z = P.eval (ζ z) / Q.eval (ζ z) := by
  sorry

/-- DLMF 32.9.12: for `PV` with `γ = δ = 0`, the first integral
`z²(w')² = (w - 1)²(2αw² + Cw - 2β)` holds with a constant `C` on every preconnected open
set. -/
@[dlmf 32.9.E12]
theorem painleveV_firstIntegral {α β : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (h : IsPainleveVOn α β 0 0 w U) :
    ∃ C : ℂ, ∀ z ∈ U, z ^ 2 * deriv w z ^ 2 = (w z - 1) ^ 2 * (2 * α * w z ^ 2 + C * w z -
      2 * β) := by
  obtain ⟨C, hC⟩ := b32_const_of_hasDerivAt_zero (I := fun z =>
      (z ^ 2 * deriv w z ^ 2 / (w z - 1) ^ 2 - 2 * α * w z ^ 2 + 2 * β) / w z) hU hc
    fun z hz => by
      have hw := h.ode.hasDerivAt hz
      have hv := h.ode.hasDerivAt_deriv z hz
      have hw0 := h.w_ne_zero z hz
      have hw1 := sub_ne_zero.mpr (h.w_ne_one z hz)
      have hz0 := h.ne_zero z hz
      have hA := ((hasDerivAt_id z).pow 2).mul (hv.pow 2)
      have hD := hA.div ((hw.sub_const 1).pow 2) (pow_ne_zero 2 hw1)
      have hE := (hw.pow 2).const_mul (2 * α)
      refine (((hD.sub hE).add_const (2 * β)).div hw hw0).congr_deriv ?_
      simp only [painleveVRhs, id_eq, Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
      field_simp
      ring
  refine ⟨C, fun z hz => ?_⟩
  have := hC z hz
  have hw0 := h.w_ne_zero z hz
  have hw1 := sub_ne_zero.mpr (h.w_ne_one z hz)
  rw [← this]
  field_simp
  ring

/-! ## `PVI` (§32.9(iii)) -/

/-- DLMF 32.9.13: `w = z^{1/2}` solves `PVI` with parameters `(κ²/2, -κ²/2, μ²/2, (1 - μ²)/2)`
on every open subset of the slit plane avoiding `z = 1` (principal square root). -/
@[dlmf 32.9.E13]
theorem painleveVI_sqrt {κ μ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hUs : U ⊆ slitPlane)
    (h1 : ∀ z ∈ U, z ≠ 1) :
    IsPainleveVIOn (κ ^ 2 / 2) (-κ ^ 2 / 2) (μ ^ 2 / 2) ((1 - μ ^ 2) / 2)
      (fun z => z ^ (1 / 2 : ℂ)) U := by
  have hz0 : ∀ z ∈ U, z ≠ 0 := fun z hz => slitPlane_ne_zero (hUs hz)
  have ht0 : ∀ z ∈ U, z ^ (1 / 2 : ℂ) ≠ 0 := fun z hz =>
    (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr (hz0 z hz)
  have ht2 : ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z := fun z => by
    rw [one_div]; exact_mod_cast cpow_nat_inv_pow z (n := 2) (by norm_num)
  have ht1 : ∀ z ∈ U, z ^ (1 / 2 : ℂ) ≠ 1 := fun z hz h =>
    h1 z hz (by rw [← ht2 z, h, one_pow])
  have htz : ∀ z ∈ U, z ^ (1 / 2 : ℂ) ≠ z := fun z hz h => by
    have h2 := ht2 z
    rw [h] at h2
    have hzz : z * z = z * 1 := by rw [← pow_two, h2, mul_one]
    exact h1 z hz (mul_left_cancel₀ (hz0 z hz) hzz)
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => 1 / 2 * z ^ (1 / 2 : ℂ) / z) (fun z hz => b32_hasDerivAt_cpow (hUs hz))
    (fun z hz => ?_), hz0, h1, ht0, ht1, htz⟩
  have hzU := hz
  have ht := ht0 z hzU
  have hz := hz0 z hzU
  have hta := sub_ne_zero.mpr (ht1 z hzU)
  have htb := sub_ne_zero.mpr (htz z hzU)
  have hz1 := sub_ne_zero.mpr (h1 z hzU)
  have h := ((b32_hasDerivAt_cpow (a := 1 / 2) (hUs hzU)).const_mul (1 / 2 : ℂ)).div
    (hasDerivAt_id z) hz
  refine h.congr_deriv ?_
  have h2 := ht2 z
  simp only [painleveVIRhs, id_eq]
  field_simp
  set T := z ^ (1 / 2 : ℂ) with hT
  linear_combination (-4 * κ ^ 2 * T ^ 4 + 8 * κ ^ 2 * T ^ 3 * z + 8 * κ ^ 2 * T ^ 3
    - 4 * κ ^ 2 * T ^ 2 * z ^ 2 - 16 * κ ^ 2 * T ^ 2 * z - 4 * κ ^ 2 * T ^ 2 + 8 * κ ^ 2 * T * z ^ 2
    + 8 * κ ^ 2 * T * z - 4 * κ ^ 2 * z ^ 2 + 4 * μ ^ 2 * T ^ 2 * z ^ 2 - 8 * μ ^ 2 * T ^ 2 * z
    + 4 * μ ^ 2 * T ^ 2 - T ^ 2 * z ^ 2 + 2 * T ^ 2 * z - T ^ 2) * h2

end DLMF.Painleve
