/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Eigenvalues
public import DLMF.Heun.Basic
public import DLMFMathlib.Analysis.ODE.Singularities

/-!
# Lamé's equation: singularities and other forms (DLMF §§29.2, 29.10, 29.11)

* §29.2(i): the singularities `2pK + (2q+1)iK'` of 29.2.1 are regular singular points, all
  other points are ordinary (admitted).
* §29.2(ii): the algebraic form 29.2.2 in `ξ = sn²` (admitted), the trigonometric form 29.2.4
  in `φ = π/2 - am` (proved), the Weierstrass forms 29.2.9 and 29.2.10 (admitted), and the
  identification of 29.2.2 as Heun's equation 31.2.1 (proved; DLMF states this for the
  equivalent 29.2.10).
* §29.10: the substitution `h = ν(ν+1) - h'`, `z' = i(z - K - iK')` maps Lamé's equation with
  modulus `k'` to that with modulus `k` (admitted); the functions 29.10.4 on the line
  `Re z = K` and their imaginary periods (periods proved from Table 29.3.2).
* §29.11: the Lamé wave equation reduces to 29.2.1 for `ω = 0` (proved).
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Lame

variable {h ν k : ℝ}

/-! ### Singularities (§29.2(i)) -/

/-- §29.2(i): for `0 < k < 1` and `ν(ν+1) ≠ 0` the points `2pK + (2q+1)iK'`, `p, q ∈ ℤ`, are
regular singularities of Lamé's equation 29.2.1. Admitted. -/
@[dlmf 29.2.i]
theorem lame_regularSingularAt (hk0 : 0 < k) (hk1 : k < 1) (hν : ν * (ν + 1) ≠ 0) (h : ℂ)
    (p q : ℤ) :
    Complex.linearODERegularSingularAt (lameODECoeff h ν k)
      (2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)) := by
  sorry

/-- §29.2(i): every other point is an ordinary point of 29.2.1. Admitted. -/
@[dlmf 29.2.i]
theorem lame_ordinaryAt (hk0 : 0 < k) (hk1 : k < 1) (h z : ℂ)
    (hz : ∀ p q : ℤ,
      z ≠ 2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)) :
    Complex.linearODEOrdinaryAt (lameODECoeff h ν k) z := by
  sorry

/-! ### Other forms (§29.2(ii)) -/

/-- 29.2.2–29.2.3: if `w` solves the algebraic form 29.2.2 on an open set `V` not containing
`0, 1, k⁻²`, then `z ↦ w(sn²(z, k))` solves Lamé's equation 29.2.1 on `{z | sn²(z, k) ∈ V}`.
Admitted. -/
@[dlmf 29.2.E2, dlmf 29.2.E3]
theorem isLameSolutionOn_comp_sn_sq (hk0 : 0 < k) (hk1 : k < 1) {w : ℂ → ℂ} {V : Set ℂ}
    (hV : IsOpen V) (h0 : (0 : ℂ) ∉ V) (h1 : (1 : ℂ) ∉ V) (h2 : ((k : ℂ) ^ 2)⁻¹ ∉ V)
    (hw : IsLameAlgebraicSolutionOn h ν k w V) :
    IsLameSolutionOn h ν k (fun z => w (jacobiSnk z k ^ 2)) {z | jacobiSnk z k ^ 2 ∈ V} := by
  sorry

/-- 29.2.4–29.2.5: if `W` solves the trigonometric form 29.2.4 on `ℝ`, then
`x ↦ W(φ(x))`, `φ = π/2 - am(x, k)`, solves Lamé's equation 29.2.1 on `ℝ`. -/
@[dlmf 29.2.E4, dlmf 29.2.E5]
theorem Real.isLameSolution_comp_lamePhi (hk0 : 0 < k) (hk1 : k < 1) {W : ℝ → ℝ}
    (hW : Real.IsLameTrigSolution h ν k W) :
    Real.IsLameSolution h ν k (fun x => W (Real.lamePhi x k)) := by
  have hm : k ^ 2 < 1 := l29_sq_lt_one hk0 hk1
  have hφ : ∀ x, HasDerivAt (fun x => Real.lamePhi x k) (-Real.jacobiDnm x (k ^ 2)) x := by
    intro x
    have := (Real.hasDerivAt_jacobiAmm hm x).const_sub (π / 2)
    simpa [Real.lamePhi, Real.jacobiDnm, Real.jacobiSnm] using this
  have h1 : ∀ x, HasDerivAt (fun x => W (Real.lamePhi x k))
      (deriv W (Real.lamePhi x k) * -Real.jacobiDnm x (k ^ 2)) x :=
    fun x => (hW.differentiable _).hasDerivAt.comp x (hφ x)
  have hderiv : deriv (fun x => W (Real.lamePhi x k)) =
      fun x => deriv W (Real.lamePhi x k) * -Real.jacobiDnm x (k ^ 2) :=
    funext fun x => (h1 x).deriv
  refine ⟨fun x => (h1 x).differentiableAt, fun x => ?_⟩
  rw [hderiv]
  have h2 := ((hW.differentiable_deriv _).hasDerivAt.comp x (hφ x)).mul
    (Real.hasDerivAt_jacobiDnm hm x).neg
  refine h2.congr_deriv ?_
  have hode := hW.ode (Real.lamePhi x k)
  have hcos : Real.cos (Real.lamePhi x k) = Real.jacobiSnm x (k ^ 2) := by
    simp [Real.lamePhi, Real.cos_pi_div_two_sub, Real.jacobiSnm]
  have hsin : Real.sin (Real.lamePhi x k) = Real.jacobiCnm x (k ^ 2) := by
    simp [Real.lamePhi, Real.sin_pi_div_two_sub, Real.jacobiCnm]
  have hdn := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm x
  rw [hcos, hsin] at hode
  simp only [Function.comp_apply, Pi.neg_apply]
  linear_combination hode + deriv (deriv W) (Real.lamePhi x k) * hdn

/-- 29.2.6–29.2.9 and 29.2.12: let `e₁ > e₂ > e₃` be real with `e₁ + e₂ + e₃ = 0` and
`(e₂ - e₃)/(e₁ - e₃) = k²`, `g = (e₁ - e₃)h + ν(ν+1)e₃` (29.2.7), `η = (e₁-e₃)^{-1/2}(z - iK')`
(29.2.8) and `g₂ = -4(e₂e₃ + e₃e₁ + e₁e₂)`, `g₃ = 4e₁e₂e₃` (29.2.12). If `w` solves Lamé's
equation 29.2.1 on `U`, then `η ↦ w((e₁-e₃)^{1/2} η + iK')` solves the Weierstrass form 29.2.9
on the corresponding set. Admitted. -/
@[dlmf 29.2.E6, dlmf 29.2.E7, dlmf 29.2.E8, dlmf 29.2.E9, dlmf 29.2.E12]
theorem isLameWeierstrassSolutionOn_of_isLameSolutionOn (hk0 : 0 < k) (hk1 : k < 1)
    {e₁ e₂ e₃ : ℝ} (h12 : e₂ < e₁) (h23 : e₃ < e₂) (hsum : e₁ + e₂ + e₃ = 0)
    (hk2 : (e₂ - e₃) / (e₁ - e₃) = k ^ 2) {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : IsLameSolutionOn h ν k w U) :
    IsLameWeierstrassSolutionOn ((e₁ - e₃) * h + ν * (ν + 1) * e₃) ν
      (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂)) (4 * e₁ * e₂ * e₃)
      (fun η => w (Real.sqrt (e₁ - e₃) * η + I * Real.compEllIntKm (1 - k ^ 2)))
      {η | (Real.sqrt (e₁ - e₃) : ℂ) * η + I * Real.compEllIntKm (1 - k ^ 2) ∈ U} := by
  sorry

/-- 29.2.10–29.2.11: if `v` solves the algebraic Weierstrass form 29.2.10 on an open set `V`
not containing `e₁, e₂, e₃`, then `η ↦ v(℘(η; g₂, g₃))` (`ζ = ℘(η)`, 29.2.11) solves 29.2.9 on
any open set `U` on which `℘` is holomorphic with values in `V`. Admitted. -/
@[dlmf 29.2.E10, dlmf 29.2.E11]
theorem isLameWeierstrassSolutionOn_comp_wp {e₁ e₂ e₃ : ℝ} (h12 : e₂ < e₁) (h23 : e₃ < e₂)
    (hsum : e₁ + e₂ + e₃ = 0) {g : ℂ} {v : ℂ → ℂ} {V U : Set ℂ} (hV : IsOpen V)
    (he : (e₁ : ℂ) ∉ V ∧ (e₂ : ℂ) ∉ V ∧ (e₃ : ℂ) ∉ V) (hU : IsOpen U)
    (hwp : ∀ η ∈ U, DifferentiableAt ℂ
      (DLMF.Weierstrass.weierstrassPInvariants (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂))
        (4 * e₁ * e₂ * e₃)) η ∧
      DLMF.Weierstrass.weierstrassPInvariants (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂))
        (4 * e₁ * e₂ * e₃) η ∈ V)
    (hv : IsLameWeierstrassAlgebraicSolutionOn g ν e₁ e₂ e₃ v V) :
    IsLameWeierstrassSolutionOn g ν (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂)) (4 * e₁ * e₂ * e₃)
      (fun η => v (DLMF.Weierstrass.weierstrassPInvariants
        (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂)) (4 * e₁ * e₂ * e₃) η)) U := by
  sorry

/-- §29.2(ii): the algebraic form 29.2.2 is Heun's equation 31.2.1 with `a = k⁻²`,
`q = -hk⁻²/4`, `α = -ν/2`, `β = (ν+1)/2`, `γ = δ = ε = 1/2`. DLMF states this for 29.2.10,
which is 29.2.2 after the affine change `ζ = e₃ + (e₁ - e₃)ξ`. -/
@[dlmf 29.2.ii "29.2.2 as Heun's equation (DLMF states it for the equivalent 29.2.10)"]
theorem isLameAlgebraicSolutionOn_iff_isHeunSolOn {h ν k : ℂ} {w : ℂ → ℂ} {U : Set ℂ} :
    IsLameAlgebraicSolutionOn h ν k w U ↔
      DLMF.Heun.IsHeunSolOn (k ^ 2)⁻¹ (-(h * (k ^ 2)⁻¹) / 4) (-ν / 2) ((ν + 1) / 2) (1 / 2)
        (1 / 2) (1 / 2) w U := by
  constructor
  · intro hw
    refine ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv ?_⟩
    simp only [DLMF.Heun.heunCoeffP, DLMF.Heun.heunCoeffR]
    rw [show ∀ x : ℂ, x / (4 * z * (z - 1) * (z - (k ^ 2)⁻¹)) =
      x / 4 / (z * (z - 1) * (z - (k ^ 2)⁻¹)) from fun x => by rw [div_div]; congr 1; ring]
    ring
  · intro hw
    refine ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv ?_⟩
    simp only [DLMF.Heun.heunCoeffP, DLMF.Heun.heunCoeffR]
    rw [show ∀ x : ℂ, x / (4 * z * (z - 1) * (z - (k ^ 2)⁻¹)) =
      x / 4 / (z * (z - 1) * (z - (k ^ 2)⁻¹)) from fun x => by rw [div_div]; congr 1; ring]
    ring

/-! ### Imaginary periods (§29.10) -/

/-- 29.10.1–29.10.3: with `h = ν(ν+1) - h'` and `z' = i(z - K - iK')`, a solution `w` of
Lamé's equation with modulus `k' = √(1 - k²)` and eigenparameter `h'` (29.10.3) gives the
solution `z ↦ w(i(z - K - iK'))` of 29.2.1 with modulus `k` and parameter `h`. Admitted (it
rests on `k'² sn²(z', k') = 1 - k² sn²(z, k)`, checked numerically). -/
@[dlmf 29.10.E1, dlmf 29.10.E2, dlmf 29.10.E3]
theorem isLameSolutionOn_imaginary (hk0 : 0 < k) (hk1 : k < 1) {h' : ℂ} {w : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hw : IsLameSolutionOn h' ν (Real.sqrt (1 - k ^ 2)) w U) :
    IsLameSolutionOn (ν * (ν + 1) - h') ν k
      (fun z => w (I * (z - Real.compEllIntKm (k ^ 2) - I * Real.compEllIntKm (1 - k ^ 2))))
      {z | I * (z - Real.compEllIntKm (k ^ 2) - I * Real.compEllIntKm (1 - k ^ 2)) ∈ U} := by
  sorry

/-- 29.10.4, `Ec`: on the line `z = K + is`, `s ∈ ℝ`, the function
`Ec^m_ν(i(z - K - iK'), k'²) = Ec^m_ν(K' - s, k'²)` solves Lamé's equation 29.2.1 with
`h = ν(ν+1) - a^m_ν(k'²)`: `-v''(s) + (h - ν(ν+1)k² sn²(K + is, k)) v(s) = 0`.
Special case: DLMF's complex `z`, here restricted to the line `Re z = K` on which the
argument is real. Admitted. -/
@[dlmf 29.10.E4 "special case: on the line Re z = K"]
theorem Real.lameEck_imaginary_solution (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ)
    (s : ℝ) :
    -(deriv (deriv fun s => Real.lameEck ν m (Real.compEllIntKm (1 - k ^ 2) - s)
        (Real.sqrt (1 - k ^ 2))) s : ℂ) +
      ((ν * (ν + 1) - Real.lameAk ν m (Real.sqrt (1 - k ^ 2)) : ℝ) -
        ν * (ν + 1) * k ^ 2 * jacobiSnk (Real.compEllIntKm (k ^ 2) + I * s) k ^ 2) *
      Real.lameEck ν m (Real.compEllIntKm (1 - k ^ 2) - s) (Real.sqrt (1 - k ^ 2)) = 0 := by
  sorry

/-- 29.10.4, `Es`: as `Real.lameEck_imaginary_solution` with `h = ν(ν+1) - b^m_ν(k'²)`.
Special case: on the line `Re z = K`. Admitted. -/
@[dlmf 29.10.E4 "special case: on the line Re z = K"]
theorem Real.lameEsk_imaginary_solution (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ)
    (s : ℝ) :
    -(deriv (deriv fun s => Real.lameEsk ν m (Real.compEllIntKm (1 - k ^ 2) - s)
        (Real.sqrt (1 - k ^ 2))) s : ℂ) +
      ((ν * (ν + 1) - Real.lameBk ν m (Real.sqrt (1 - k ^ 2)) : ℝ) -
        ν * (ν + 1) * k ^ 2 * jacobiSnk (Real.compEllIntKm (k ^ 2) + I * s) k ^ 2) *
      Real.lameEsk ν m (Real.compEllIntKm (1 - k ^ 2) - s) (Real.sqrt (1 - k ^ 2)) = 0 := by
  sorry

lemma l29_comodulus (hk0 : 0 < k) (hk1 : k < 1) :
    0 < Real.sqrt (1 - k ^ 2) ∧ Real.sqrt (1 - k ^ 2) < 1 ∧
      Real.sqrt (1 - k ^ 2) ^ 2 = 1 - k ^ 2 := by
  have h1 : 0 < 1 - k ^ 2 := by nlinarith
  refine ⟨Real.sqrt_pos.2 h1, ?_, Real.sq_sqrt h1.le⟩
  rw [Real.sqrt_lt' one_pos]; nlinarith

/-- §29.10, periods: on the line `z = K + is`, the functions 29.10.4 built from `Ec^{2m}_ν`
and `Es^{2m+2}_ν` have period `2iK'` (period `2K'` in `s`), those from `Ec^{2m+1}_ν` and
`Es^{2m+1}_ν` have period `4iK'`. Proved from Table 29.3.2 for the modulus `k'`. -/
@[dlmf 29.10 "periods along the line Re z = K"]
theorem Real.lame_imaginary_periods (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ)
    (s : ℝ) :
    Real.lameEck ν m (Real.compEllIntKm (1 - k ^ 2) - (s + 2 * Real.compEllIntKm (1 - k ^ 2)))
        (Real.sqrt (1 - k ^ 2)) =
      (-1) ^ m * Real.lameEck ν m (Real.compEllIntKm (1 - k ^ 2) - s) (Real.sqrt (1 - k ^ 2)) ∧
    Real.lameEsk ν m (Real.compEllIntKm (1 - k ^ 2) - (s + 2 * Real.compEllIntKm (1 - k ^ 2)))
        (Real.sqrt (1 - k ^ 2)) =
      (-1) ^ m * Real.lameEsk ν m (Real.compEllIntKm (1 - k ^ 2) - s) (Real.sqrt (1 - k ^ 2)) := by
  obtain ⟨h0, h1, h2⟩ := l29_comodulus hk0 hk1
  have hK : Real.compEllIntKm (Real.sqrt (1 - k ^ 2) ^ 2) = Real.compEllIntKm (1 - k ^ 2) := by
    rw [h2]
  set K' := Real.compEllIntKm (1 - k ^ 2)
  have hc := (Real.lameEck_parity hν h0 h1 m (K' - s - 2 * K')).2.2.2.1
  have hs := (Real.lameEsk_parity hν h0 h1 m (K' - s - 2 * K')).2.2.2.1
  rw [hK, show K' - s - 2 * K' + 2 * K' = K' - s by ring] at hc hs
  rw [show K' - (s + 2 * K') = K' - s - 2 * K' by ring]
  constructor
  · rw [hc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [hs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

/-! ### The Lamé wave equation (§29.11) -/

/-- §29.11: for `ω = 0` the Lamé wave equation 29.11.1 reduces to Lamé's equation 29.2.1. -/
@[dlmf 29.11]
theorem isLameWaveSolutionOn_zero_iff {h ν k : ℂ} {w : ℂ → ℂ} {U : Set ℂ} :
    IsLameWaveSolutionOn h ν k 0 w U ↔ IsLameSolutionOn h ν k w U := by
  constructor
  · intro hw
    exact ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv (by ring)⟩
  · intro hw
    exact ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv (by ring)⟩

end DLMF.Lame
