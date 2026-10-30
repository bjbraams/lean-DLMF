/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Toroidal

/-!
# Conical functions, Mehler–Fock transforms and special identities

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- The conical Ferrers function `𝖯^{-μ}_{-1/2+iτ}(x)`, i.e. `ferrersP (-1/2 + iτ) (-μ) x`, for real
`τ, μ, x`. -/
def conicalP (τ μ x : ℝ) : ℂ :=
  ferrersP (-1/2+I*τ) (-μ) x

/-- Dunster’s conical companion; the order is minus the parameter μ. -/
@[dlmf 14.20.E2]
def conicalQHat (τ μ x : ℝ) : ℂ :=
  ((exp (μ*π*I)*ferrersQ (-1/2+I*τ) (-μ) x).re:ℂ)-π/2*Real.sin (μ*π)*conicalP τ μ x

/-- DLMF 14.20.1: for `μ, τ ≥ 0`, the conical function `w = 𝖯^{-μ}_{-1/2+iτ}(x)` satisfies `(1-x²)
w'' - 2x w' - (τ² + 1/4 + μ²/(1-x²)) w = 0` on `-1 < x < 1`. -/
@[dlmf 14.20.E1]
theorem conical_ode (τ μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*iteratedDeriv 2 (conicalP τ μ) x-2*x*deriv (conicalP τ μ) x-(τ^2+1/4+μ^2/(1-x^2):ℂ)*conicalP τ μ x=0 := by
  have h := ferrersP_ode (-1/2+I*τ) (-(μ:ℂ)) hx
  have e : conicalP τ μ = ferrersP (-1/2+I*τ) (-(μ:ℂ)) := rfl
  rw [e]
  linear_combination h + (-(τ:ℂ)^2 * ferrersP (-1/2+I*τ) (-(μ:ℂ)) x) * I_sq

/-- The conical Ferrers function is real-valued on `(-1,1)`. -/
theorem conicalP_ofReal_re (τ μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ((conicalP τ μ x).re : ℂ) = conicalP τ μ x := by
  rw [Complex.conj_eq_iff_re.mp]
  show (starRingEnd ℂ) (ferrersP (-1/2+I*τ) (-(μ:ℂ)) x) = ferrersP (-1/2+I*τ) (-(μ:ℂ)) x
  rw [ferrersP_conj _ _ hx]
  have e1 : (starRingEnd ℂ) (-1/2+I*(τ:ℂ)) = -(-1/2+I*τ)-1 := by
    apply Complex.ext
    · simp [map_ofNat]; norm_num
    · simp [map_ofNat]
  have e2 : (starRingEnd ℂ) (-(μ:ℂ)) = -(μ:ℂ) := by simp
  rw [e1, e2, ferrers_connection_5 _ _ hx]

/-- Differentiability of the conical function on `(-1,1)`. -/
theorem conicalP_differentiableAt (τ μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    DifferentiableAt ℝ (conicalP τ μ) x :=
  (((hasDerivAt_ferrersEven _ _ hx).const_mul _).add ((hasDerivAt_ferrersOdd _ _ hx).const_mul _)
    ).differentiableAt.congr_of_eventuallyEq
    ((ferrersP_eqOn_even_odd _ _).eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx))

/-- DLMF 14.20.3: for `τ, μ ≥ 0` (excluding `τ = 0` with `μ` a positive half-odd integer) and `-1 <
x < 1`, `𝖰̂^{-μ}_{-1/2+iτ}(x) = (π e^{-τπ} sin(μπ) sinh(τπ) 𝖯^{-μ}_{-1/2+iτ}(x) + π (e^{-τπ}
cos²(μπ) + sinh(τπ)) 𝖯^{-μ}_{-1/2+iτ}(-x))/(2(cosh²(τπ) - sin²(μπ)))`. -/
@[dlmf 14.20.E3]
theorem conicalQHat_connection {τ μ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    conicalQHat τ μ x=π*Real.exp (-τ*π)*Real.sin (μ*π)*Real.sinh (τ*π)/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))*conicalP τ μ x+π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))*conicalP τ μ (-x) := by
  have hxm : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  set ν : ℂ := -1/2+I*τ with hν
  have hreg1 : LegendreQRegular ν (μ:ℂ) := by
    intro n hn
    have := congrArg Complex.re hn
    simp [hν] at this
    linarith
  have hreg2 : LegendreQRegular ν (-(μ:ℂ)) := by
    intro n hn
    have hr := congrArg Complex.re hn
    have hi := congrArg Complex.im hn
    simp [hν] at hr hi
    rcases hex with h | h
    · exact h hi
    · exact h n (by linarith)
  have h10 := ferrers_connection_10 ν (μ:ℂ) hreg1 hreg2 hx
  have hw : (ν-μ)*π = ((-(μ*π) - π/2 : ℝ):ℂ) + ((τ*π:ℝ):ℂ)*I := by rw [hν]; push_cast; ring
  have hsw : sin ((ν-μ)*π) = ((-(Real.cos (μ*π)*Real.cosh (τ*π))):ℝ) + (-(Real.sin (μ*π)*Real.sinh (τ*π)):ℝ)*I := by
    rw [hw, Complex.sin_add_mul_I, ← ofReal_sin, ← ofReal_cos, ← ofReal_sinh, ← ofReal_cosh,
      Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two, Real.cos_neg, Real.sin_neg]
    simp only [ofReal_neg, ofReal_mul]; ring
  have hcw : cos ((ν-μ)*π) = (-(Real.sin (μ*π)*Real.cosh (τ*π)):ℝ) + (Real.cos (μ*π)*Real.sinh (τ*π):ℝ)*I := by
    rw [hw, Complex.cos_add_mul_I, ← ofReal_sin, ← ofReal_cos, ← ofReal_sinh, ← ofReal_cosh,
      Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two, Real.cos_neg, Real.sin_neg]
    simp only [ofReal_neg, ofReal_mul]; ring
  have he : exp (μ*π*I) = (Real.cos (μ*π):ℂ) + (Real.sin (μ*π):ℂ)*I := by
    rw [show (μ:ℂ)*π*I = ((μ*π:ℝ):ℂ)*I by push_cast; ring, exp_mul_I, ← ofReal_sin, ← ofReal_cos]
  have hexp : Real.exp (-τ*π) = Real.cosh (τ*π) - Real.sinh (τ*π) := by
    rw [show -τ*π = -(τ*π) by ring, Real.cosh_eq, Real.sinh_eq]; ring
  have hc0 : τ = 0 → Real.cos (μ*π) ≠ 0 := by
    intro h0 hc0
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc0
    have hk' : μ = k + 1/2 := by
      have := Real.pi_pos
      field_simp at hk; linarith
    rcases hex with h | h
    · exact h h0
    · have hk0 : (0:ℤ) ≤ k := by
        have : (-1:ℝ) < k := by linarith
        exact_mod_cast (show (-1:ℤ) < k by exact_mod_cast this)
      apply h k.toNat
      rw [hk']; congr 1; exact_mod_cast (Int.toNat_of_nonneg hk0).symm
  have hS0 : τ ≠ 0 → Real.sinh (τ*π) ≠ 0 := by
    intro h; rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero h Real.pi_ne_zero
  unfold conicalQHat
  rw [← conicalP_ofReal_re τ μ hx, ← conicalP_ofReal_re τ μ hxm]
  have hp : ferrersP ν (-(μ:ℂ)) x = (conicalP τ μ x).re := (conicalP_ofReal_re τ μ hx).symm
  have hq : ferrersP ν (-(μ:ℂ)) (-x) = (conicalP τ μ (-x)).re := (conicalP_ofReal_re τ μ hxm).symm
  rw [hp, hq, hsw, hcw] at h10
  rw [he, hexp]
  generalize (conicalP τ μ x).re = p at h10 ⊢
  generalize (conicalP τ μ (-x)).re = q at h10 ⊢
  generalize ferrersQ ν (-(μ:ℂ)) x = Q at h10 ⊢
  have pyth : Real.sin (μ*π)^2+Real.cos (μ*π)^2 = 1 := Real.sin_sq_add_cos_sq _
  have hyp : Real.cosh (τ*π)^2 - Real.sinh (τ*π)^2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have hC : 1 ≤ Real.cosh (τ*π) := Real.one_le_cosh _
  generalize Real.cos (μ*π) = c at *
  generalize Real.sin (μ*π) = s at *
  generalize Real.cosh (τ*π) = C at *
  generalize Real.sinh (τ*π) = S at *
  have hD : 0 < C^2 - s^2 := by
    by_cases h0 : τ = 0
    · nlinarith [sq_pos_of_ne_zero (hc0 h0), sq_nonneg S]
    · nlinarith [sq_pos_of_ne_zero (hS0 h0), sq_nonneg c]
  have hPi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : (((-(c*C)):ℝ) + (-(s*S):ℝ)*I) * ((-(c*C):ℝ) - (-(s*S):ℝ)*I) = ((C^2-s^2:ℝ):ℂ) := by
    have e : ((c*C)^2 + (s*S)^2 : ℝ) = C^2-s^2 := by linear_combination C^2*pyth - s^2*hyp
    rw [← e]; apply Complex.ext <;> simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im] <;> ring
  have h2 : (2/π*(C^2-s^2:ℝ):ℂ) * Q = (((-(s*C):ℝ) + (c*S:ℝ)*I) * p - q) * ((-(c*C):ℝ) - (-(s*S):ℝ)*I) := by
    linear_combination ((-(c*C):ℝ) - (-(s*S):ℝ)*I) * h10 - (2/π*Q) * key
  have hQ : Q = ((π/2/(C^2-s^2) : ℝ):ℂ) * ((((-(s*C):ℝ) + (c*S:ℝ)*I) * p - q) * ((-(c*C):ℝ) - (-(s*S):ℝ)*I)) := by
    rw [← h2]
    have : ((C^2-s^2:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr hD.ne'
    push_cast at this ⊢
    field_simp
  have hre : (((c:ℂ) + (s:ℂ)*I) * Q).re = π/2/(C^2-s^2) * ((-(c^2*C+s^2*S))*(-(s*C*p)-q) - c*s*(S-C)*(c*S*p)) := by
    rw [hQ]; simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im]; ring
  rw [hre]
  have hfin : π/2/(C^2-s^2) * ((-(c^2*C+s^2*S))*(-(s*C*p)-q) - c*s*(S-C)*(c*S*p)) - π/2*s*p
      - (π*(C-S)*s*S/(2*(C^2-s^2))*p + π*((C-S)*c^2+S)/(2*(C^2-s^2))*q)
      = π/(2*(C^2-s^2)) * (p*((s*S*C+s)*(s^2+c^2-1) + s*(c^2-1)*(C^2-S^2-1)) + q*(S*(s^2+c^2-1))) := by
    field_simp; ring
  rw [show s^2+c^2-1 = 0 by linarith, show C^2-S^2-1 = 0 by linarith] at hfin
  have : π/2/(C^2-s^2) * ((-(c^2*C+s^2*S))*(-(s*C*p)-q) - c*s*(S-C)*(c*S*p)) - π/2*s*p
      = π*(C-S)*s*S/(2*(C^2-s^2))*p + π*((C-S)*c^2+S)/(2*(C^2-s^2))*q := by linarith [hfin]
  rw [← sub_eq_zero]
  have h3 := congrArg (fun r : ℝ => (r:ℂ)) this
  push_cast at h3 ⊢
  linear_combination h3

/-- DLMF 14.20.4: for `τ, μ ≥ 0` and `-1 < x < 1`, `𝒲{𝖯^{-μ}_{-1/2+iτ}(x), 𝖯^{-μ}_{-1/2+iτ}(-x)} =
2/(|Γ(μ+1/2+iτ)|² (1-x²))`. -/
@[dlmf 14.20.E4]
theorem conical_wronskian (τ μ : ℝ) (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ODE.wronskian (conicalP τ μ) (fun x => conicalP τ μ (-x)) x=2/((‖Gamma (μ+1/2+I*τ)‖^2:ℂ)*(1-x^2)) := by
  show ODE.wronskian (fun x => ferrersP (-1/2+I*τ) (-(μ:ℂ)) x)
    (fun x => ferrersP (-1/2+I*τ) (-(μ:ℂ)) (-x)) x = _
  rw [ferrers_wronskian_3 _ _ hx]
  congr 2
  rw [show (μ:ℂ)-(-1/2+I*τ) = (starRingEnd ℂ) ((μ:ℂ)+1/2+I*τ) by simp [map_ofNat]; ring,
    show -1/2+I*(τ:ℂ)+μ+1 = (μ:ℂ)+1/2+I*τ by ring, Gamma_conj, mul_comm, mul_conj,
    normSq_eq_norm_sq]
  push_cast; ring

/-- DLMF 14.20.5: for `τ, μ ≥ 0` (excluding `τ = 0` with `μ` a positive half-odd integer) and `-1 <
x < 1`, `𝒲{𝖯^{-μ}_{-1/2+iτ}, 𝖰̂^{-μ}_{-1/2+iτ}}(x) = π (e^{-τπ} cos²(μπ) + sinh(τπ))/(|Γ(μ+1/2+iτ)|²
(cosh²(τπ) - sin²(μπ)) (1-x²))`. -/
@[dlmf 14.20.E5]
theorem conicalQHat_wronskian {τ μ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ODE.wronskian (conicalP τ μ) (conicalQHat τ μ) x=π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/((‖Gamma (μ+1/2+I*τ)‖^2:ℂ)*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2)*(1-x^2)) := by
  set A : ℂ := π*Real.exp (-τ*π)*Real.sin (μ*π)*Real.sinh (τ*π)/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))
  set B : ℂ := π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))
  have hev : conicalQHat τ μ =ᶠ[nhds x] fun y => A*conicalP τ μ y+B*conicalP τ μ (-y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact conicalQHat_connection hτ hμ hex hy
  have hxm : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hd1 : DifferentiableAt ℝ (conicalP τ μ) x := conicalP_differentiableAt τ μ hx
  have hd2 : DifferentiableAt ℝ (fun y => conicalP τ μ (-y)) x :=
    (conicalP_differentiableAt τ μ hxm).comp x differentiableAt_id.neg
  have hW := conical_wronskian τ μ hτ hμ hx
  unfold ODE.wronskian at hW ⊢
  have hder : deriv (fun y => A*conicalP τ μ y+B*conicalP τ μ (-y)) x =
      A*deriv (conicalP τ μ) x + B*deriv (fun y => conicalP τ μ (-y)) x :=
    ((hd1.hasDerivAt.const_mul A).add (hd2.hasDerivAt.const_mul B)).deriv
  rw [hev.deriv_eq, hev.eq_of_nhds, hder]
  have hW' : conicalP τ μ x * deriv (fun x => conicalP τ μ (-x)) x - conicalP τ μ (-x) * deriv (conicalP τ μ) x =
      2 / (↑‖Gamma (↑μ + 1 / 2 + I * ↑τ)‖ ^ 2 * (1 - ↑x ^ 2)) := hW
  have hfin : B * (2 / (↑‖Gamma (↑μ + 1 / 2 + I * ↑τ)‖ ^ 2 * (1 - ↑x ^ 2))) =
      π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/((‖Gamma (μ+1/2+I*τ)‖^2:ℂ)*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2)*(1-x^2)) := by
    simp only [B]
    generalize ((Real.cosh (τ*π):ℂ)^2-(Real.sin (μ*π):ℂ)^2) = D
    generalize ((‖Gamma (μ+1/2+I*τ)‖:ℂ)^2) = G
    generalize (1-(x:ℂ)^2) = X
    ring
  rw [← hfin]
  linear_combination B * hW'

/-- DLMF 14.20.6: for `τ > 0`, `μ ≥ 0` and `x > 1`, `P^{-μ}_{-1/2+iτ}(x) = i e^{-μπi}/(sinh(τπ)
|Γ(μ+1/2+iτ)|²) (Q^μ_{-1/2+iτ}(x) - Q^μ_{-1/2-iτ}(x))`. -/
@[dlmf 14.20.E6]
theorem conical_associated_connection {τ μ : ℝ} (hτ : 0 < τ) {x : ℝ} (hx : 1 < x) :
    associatedP (-1/2+I*τ) (-μ) x=I*exp (-μ*π*I)/(Real.sinh (τ*π)*(‖Gamma (μ+1/2+I*τ)‖^2:ℂ))*(associatedQ (-1/2+I*τ) μ x-associatedQ (-1/2-I*τ) μ x) := by
  have hz : (x:ℂ)-1 ∈ slitPlane := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring]; exact Or.inl (by simp; linarith)
  have h12 := associated_connection_12 (-1/2+I*τ) μ hz
  rw [show -(-1/2+I*(τ:ℂ))-1 = -1/2-I*τ by ring, show (μ:ℂ)-(-1/2+I*τ) = μ+1/2-I*τ by ring,
    show -1/2+I*(τ:ℂ)+μ+1 = μ+1/2+I*τ by ring] at h12
  have hr1 : LegendreQRegular (-1/2+I*τ) μ := legendreQRegular_of_im_ne_zero (by simp; exact hτ.ne')
  have hr2 : LegendreQRegular (-1/2-I*τ) μ := legendreQRegular_of_im_ne_zero (by simp; exact hτ.ne')
  rw [olverQ_normalization hr1, olverQ_normalization hr2] at h12
  rw [show -1/2+I*(τ:ℂ)+μ+1 = μ+1/2+I*τ by ring, show -1/2-I*(τ:ℂ)+μ+1 = μ+1/2-I*τ by ring] at h12
  have hc : (μ:ℂ)+1/2-I*τ = (starRingEnd ℂ) ((μ:ℂ)+1/2+I*τ) := by simp [map_ofNat]; ring
  have hn : ((‖Gamma (μ+1/2+I*τ)‖^2 : ℝ) : ℂ) = Gamma (μ+1/2+I*τ)*Gamma (μ+1/2-I*τ) := by
    rw [hc, Gamma_conj, mul_conj, normSq_eq_norm_sq]
  have hcos : cos ((-1/2+I*τ)*π) = I*Real.sinh (τ*π) := by
    rw [show (-1/2+I*(τ:ℂ))*π = (τ*π)*I - π/2 by ring, cos_sub_pi_div_two, sin_mul_I]
    push_cast; ring
  have hG1 : Gamma (μ+1/2+I*τ) ≠ 0 := Gamma_ne_zero (fun n hn => by
    have := congrArg Complex.im hn; simp at this; exact hτ.ne' this)
  have hG2 : Gamma (μ+1/2-I*τ) ≠ 0 := Gamma_ne_zero (fun n hn => by
    have := congrArg Complex.im hn; simp at this; exact hτ.ne' this)
  have hsh : (Real.sinh (τ*π):ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr (by positivity)).ne'
  rw [hcos] at h12
  have hn' : (‖Gamma (μ+1/2+I*τ)‖^2:ℂ) = Gamma (μ+1/2+I*τ)*Gamma (μ+1/2-I*τ) := by
    rw [← hn]; push_cast; ring
  rw [hn', div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hsh (mul_ne_zero hG1 hG2))]
  have h12' : I*(Real.sinh (τ*π):ℂ)*associatedP (-1/2+I*τ) (-μ) x*(Gamma (μ+1/2+I*τ)*Gamma (μ+1/2-I*τ)) =
      exp (-μ*π*I)*(associatedQ (-1/2-I*τ) μ x-associatedQ (-1/2+I*τ) μ x) := by
    rw [h12]
    generalize Gamma (μ+1/2+I*τ) = G1 at hG1 ⊢
    generalize Gamma (μ+1/2-I*τ) = G2 at hG2 ⊢
    field_simp
    ring
  linear_combination (-I)*h12' + ((Real.sinh (τ*π):ℂ)*associatedP (-1/2+I*τ) (-μ) x*
    (Gamma (μ+1/2+I*τ)*Gamma (μ+1/2-I*τ)))*I_sq

/-! ### Boundary behaviour at `x = 1⁻` (prefix `legCon_`) -/

/-- `π sin(μπ)/Γ(1-μ) = Γ(μ) sin²(μπ)` for `μ > 0`, including integer `μ`. -/
theorem legCon_reflect {μ : ℝ} (hμ : 0 < μ) :
    π * Real.sin (μ*π) * (Real.Gamma (1-μ))⁻¹ = Real.Gamma μ * Real.sin (μ*π)^2 := by
  by_cases h : Real.Gamma (1-μ) = 0
  · obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff _).mp h
    have hs : Real.sin (μ*π) = 0 := by
      rw [show μ = ((m+1:ℕ):ℝ) by push_cast; linarith, Real.sin_nat_mul_pi]
    rw [hs]; ring
  · have hr := Real.Gamma_mul_Gamma_one_sub μ
    have hG := Real.Gamma_pos_of_pos hμ
    have hs : Real.sin (π*μ) ≠ 0 := by
      intro hs; rw [hs, div_zero] at hr
      exact h ((mul_eq_zero.mp hr).resolve_left hG.ne')
    rw [mul_comm π μ] at hs hr
    rw [eq_div_iff hs] at hr
    set s := Real.sin (μ*π)
    field_simp
    linear_combination -hr

/-- `(1-x²)^{μ/2} 𝖯^μ_ν(x) → 2^μ/Γ(1-μ)` as `x → 1⁻`, for every `μ`. -/
theorem legCon_tendsto_P (ν μ : ℂ) :
    Tendsto (fun x : ℝ => (1-(x:ℂ)^2)^(μ/2) * ferrersP ν μ x) (𝓝[<] 1)
      (𝓝 ((2:ℂ)^μ * (Gamma (1-μ))⁻¹)) := by
  have hc : ContinuousAt (fun x : ℝ => (1+(x:ℂ))^μ *
      regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-(x:ℂ))/2)) 1 :=
    (ContinuousAt.cpow (by fun_prop) continuousAt_const (Or.inl (by norm_num))).mul
      (continuousAt_regularizedGaussHG_half_one _ _ _)
  have h1 : (1+((1:ℝ):ℂ))^μ * regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-((1:ℝ):ℂ))/2) =
      (2:ℂ)^μ * (Gamma (1-μ))⁻¹ := by
    rw [show (1-((1:ℝ):ℂ))/2 = 0 by simp, regularizedGaussHG_at_zero]; norm_num
  rw [← h1]
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have h0 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  simp only [ferrersP]
  rw [← mul_assoc]
  congr 1
  rw [show (1-(x:ℂ)^2) = ((1-x^2:ℝ):ℂ) by push_cast; ring,
    ← mul_cpow_ofReal_nonneg (by nlinarith) (by positivity), ← ofReal_mul,
    show (1-x^2)*((1+x)/(1-x)) = (1+x)^2 by field_simp; ring,
    legTor_cpow_real (by positivity), show (1:ℂ)+x = ((1+x:ℝ):ℂ) by push_cast; ring,
    legTor_cpow_real h0, Real.log_pow]
  push_cast; ring_nf

/-- `(1-x²)^{μ/2} 𝖯^{-μ}_ν(-x) → 2^μ Γ(μ)/(Γ(μ-ν)Γ(μ+ν+1))` as `x → 1⁻`, for `Re μ > 0`. -/
theorem legCon_tendsto_P_neg (ν : ℂ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun x : ℝ => (1-(x:ℂ)^2)^((μ:ℂ)/2) * ferrersP ν (-(μ:ℂ)) (-x)) (𝓝[<] 1)
      (𝓝 ((2:ℂ)^(μ:ℂ) * (Gamma (μ:ℂ) * ((Gamma ((μ:ℂ)-ν))⁻¹ * (Gamma ((μ:ℂ)+ν+1))⁻¹)))) := by
  have hF := legBd_tendsto_rGHG_one (a := ν+1) (b := -ν) (c := 1-(-(μ:ℂ)))
    (by simp only [sub_re, neg_re, add_re, one_re, ofReal_re]; linarith)
  rw [show 1-(-(μ:ℂ))-(ν+1)-(-ν) = (μ:ℂ) by ring, show 1-(-(μ:ℂ))-(ν+1) = (μ:ℂ)-ν by ring,
    show 1-(-(μ:ℂ))-(-ν) = (μ:ℂ)+ν+1 by ring] at hF
  have hτ : Tendsto (fun x : ℝ => (1+x)/2) (𝓝[<] 1) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => (1+x)/2) (𝓝 1) (𝓝 ((1+1)/2)) :=
        ((continuous_const.add continuous_id).div_const 2).tendsto 1
      rw [show ((1:ℝ)+1)/2 = 1 by norm_num] at this; exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1); show (1+x)/2 < 1; linarith
  have hc : Tendsto (fun x : ℝ => (1+(x:ℂ))^(μ:ℂ)) (𝓝[<] 1) (𝓝 ((2:ℂ)^(μ:ℂ))) := by
    have : ContinuousAt (fun x : ℝ => (1+(x:ℂ))^(μ:ℂ)) 1 :=
      ContinuousAt.cpow (by fun_prop) continuousAt_const (Or.inl (by norm_num))
    have h := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    rwa [show (1+((1:ℝ):ℂ)) = 2 by norm_num] at h
  refine (hc.mul (hF.comp hτ)).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have h0 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  simp only [ferrersP, Function.comp]
  rw [show (1-((-x:ℝ):ℂ))/2 = (((1+x)/2:ℝ):ℂ) by push_cast; ring,
    show (1 + -x) / (1 - -x) = (1-x)/(1+x) by ring, ← mul_assoc]
  congr 1
  rw [show (1-(x:ℂ)^2) = ((1-x^2:ℝ):ℂ) by push_cast; ring, show (1:ℂ)+x = ((1+x:ℝ):ℂ) by push_cast; ring,
    legTor_cpow_real h0, legTor_cpow_real (by nlinarith), legTor_cpow_real (by positivity), ← exp_add,
    show 1-x^2 = (1-x)*(1+x) by ring, Real.log_mul h2.ne' h0.ne', Real.log_div h2.ne' h0.ne']
  congr 1; push_cast; ring

/-- DLMF 14.20.7: for `τ ≥ 0` and `μ > 0` (excluding `τ = 0` with `μ` a positive half-odd integer),
`𝖰̂^{μ}_{-1/2+iτ}(x) ~ (Γ(μ)/2) (2/(1-x))^{μ/2}` as `x → 1⁻`. -/
@[dlmf 14.20.E7]
theorem conical_singular_7 {τ μ : ℝ} (hμ : 0 < μ) :
    (fun x : ℝ => conicalQHat τ (-1*μ) x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => Gamma (μ:ℂ)/2*(2/(1-x):ℂ)^((μ:ℂ)/2)) := by
  set ν : ℂ := -1/2+I*τ with hνdef
  have hreg : LegendreQRegular ν (μ:ℂ) := fun n hn => by
    have := congrArg Complex.re hn; simp [hνdef] at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hQ := legBd_ferrersQ_tendsto hreg (by simpa using hμ)
  have hP := legCon_tendsto_P ν μ
  set E : ℂ := exp ((((-1*μ)*π:ℝ):ℂ)*I)
  set c : ℂ := ((π/2*Real.sin (μ*π):ℝ):ℂ)
  have hF : Tendsto (fun x : ℝ => (((E * ((1-(x:ℂ)^2)^((μ:ℂ)/2) * ferrersQ ν μ x)).re:ℝ):ℂ) +
      c * ((1-(x:ℂ)^2)^((μ:ℂ)/2) * ferrersP ν μ x)) (𝓝[<] 1)
      (𝓝 ((((E * (2^((μ:ℂ)-1) * Gamma (μ:ℂ) * cos ((μ:ℂ)*π))).re:ℝ):ℂ) +
        c * ((2:ℂ)^(μ:ℂ) * (Gamma (1-(μ:ℂ)))⁻¹))) :=
    ((continuous_ofReal.comp continuous_re).continuousAt.tendsto.comp (hQ.const_mul E)).add
      (hP.const_mul c)
  have hval : (((E * (2^((μ:ℂ)-1) * Gamma (μ:ℂ) * cos ((μ:ℂ)*π))).re:ℝ):ℂ) +
      c * ((2:ℂ)^(μ:ℂ) * (Gamma (1-(μ:ℂ)))⁻¹) = 2^((μ:ℂ)-1) * Gamma (μ:ℂ) := by
    have e1 : (2:ℂ)^((μ:ℂ)-1) = (((2:ℝ)^(μ-1):ℝ):ℂ) := by
      rw [ofReal_cpow (by norm_num)]; push_cast; ring_nf
    have e2 : (2:ℂ)^(μ:ℂ) = (((2:ℝ)^μ:ℝ):ℂ) := by rw [ofReal_cpow (by norm_num)]; push_cast; ring_nf
    have e3 : Gamma (1-(μ:ℂ)) = ((Real.Gamma (1-μ):ℝ):ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
    have e4 : cos ((μ:ℂ)*π) = ((Real.cos (μ*π):ℝ):ℂ) := by push_cast; ring_nf
    rw [e1, e2, e3, e4, Complex.Gamma_ofReal, show (((2:ℝ)^(μ-1):ℝ):ℂ) * ((Real.Gamma μ:ℝ):ℂ) *
      ((Real.cos (μ*π):ℝ):ℂ) = (((2:ℝ)^(μ-1) * Real.Gamma μ * Real.cos (μ*π):ℝ):ℂ) by push_cast; ring,
      mul_comm E, re_ofReal_mul, exp_ofReal_mul_I_re]
    have h2 : (2:ℝ)^μ = 2 * 2^(μ-1) := by
      rw [show μ = (μ-1)+1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]; ring_nf
    have hr := legCon_reflect hμ
    have hr' : (π:ℂ) * sin ((μ:ℂ)*π) * ((Real.Gamma (1-μ):ℝ):ℂ)⁻¹ =
        ((Real.Gamma μ:ℝ):ℂ) * sin ((μ:ℂ)*π)^2 := by
      have := congrArg (fun r : ℝ => (r:ℂ)) hr; push_cast at this; exact this
    simp only [c]
    push_cast
    rw [h2]
    push_cast
    rw [show cos (-1*(μ:ℂ)*π) = cos ((μ:ℂ)*π) by
      rw [show -1*(μ:ℂ)*π = -((μ:ℂ)*π) by ring, Complex.cos_neg]]
    linear_combination (((2:ℝ)^(μ-1):ℝ):ℂ) * hr' +
      (((2:ℝ)^(μ-1):ℝ):ℂ) * ((Real.Gamma μ:ℝ):ℂ) * Complex.sin_sq_add_cos_sq ((μ:ℂ)*π)
  have hu : Tendsto (fun x : ℝ => (1-(x:ℂ)^2)^((μ:ℂ)/2) * conicalQHat τ (-1*μ) x) (𝓝[<] 1)
      (𝓝 (2^((μ:ℂ)-1) * Gamma (μ:ℂ))) := by
    rw [← hval]
    refine hF.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
    have h0 : 0 ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
    have hr : (1-(x:ℂ)^2)^((μ:ℂ)/2) = (((1-x^2)^(μ/2):ℝ):ℂ) := by
      rw [ofReal_cpow h0]; push_cast; ring_nf
    unfold conicalQHat conicalP
    rw [show -(((-1*μ:ℝ)):ℂ) = (μ:ℂ) by push_cast; ring,
      show (((-1*μ:ℝ)):ℂ)*π*I = (((-1*μ)*π:ℝ):ℂ)*I by push_cast; ring, hr]
    rw [mul_left_comm E, re_ofReal_mul]
    simp only [c, E, ← hνdef]
    rw [show Real.sin ((-1*μ)*π) = -Real.sin (μ*π) by
      rw [show (-1*μ)*π = -(μ*π) by ring, Real.sin_neg]]
    push_cast; ring
  have hK : (2:ℂ)^((μ:ℂ)-1) * Gamma (μ:ℂ) ≠ 0 :=
    mul_ne_zero (by simp) (Gamma_ne_zero_of_re_pos (by simpa using hμ))
  have := legBd_isEquivalent_of_tendsto hu (legBd_tendsto_weight_left (μ:ℂ)) hK (by simp)
  refine this.congr_right (Eventually.of_forall fun x => ?_)
  simp only
  rw [show (2:ℂ)^((μ:ℂ)-1) * Gamma (μ:ℂ) / 2^(μ:ℂ) = (2:ℂ)^((μ:ℂ)-1) / 2^(μ:ℂ) * Gamma (μ:ℂ) by ring,
    legBd_two_cpow_sub_one_div]
  ring

/-- DLMF 14.20.8: for `τ ≥ 0` and `μ > 0` (excluding `τ = 0` with `μ` a positive half-odd integer),
`𝖰̂^{-μ}_{-1/2+iτ}(x) ~ π Γ(μ) (e^{-τπ} cos²(μπ) + sinh(τπ))/(2(cosh²(τπ) - sin²(μπ))
|Γ(μ+1/2+iτ)|²) (2/(1-x))^{μ/2}` as `x → 1⁻`. -/
@[dlmf 14.20.E8]
theorem conical_singular_8 {τ μ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 < μ) (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) :
    (fun x : ℝ => conicalQHat τ (1*μ) x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => π*Gamma (μ:ℂ)*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2)*(‖Gamma (μ+1/2+I*τ)‖^2:ℂ))*(2/(1-x):ℂ)^((μ:ℂ)/2)) := by
  set ν : ℂ := -1/2+I*τ with hνdef
  set A : ℂ := π*Real.exp (-τ*π)*Real.sin (μ*π)*Real.sinh (τ*π)/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))
  set B : ℂ := π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))
  -- first term tends to zero
  have h1 : Tendsto (fun x : ℝ => (1-(x:ℂ)^2)^((μ:ℂ)/2) * conicalP τ μ x) (𝓝[<] 1) (𝓝 0) := by
    have hP := legCon_tendsto_P ν (-(μ:ℂ))
    have hz : Tendsto (fun x : ℝ => (((1-x^2)^μ:ℝ):ℂ)) (𝓝[<] 1) (𝓝 0) := by
      have : ContinuousAt (fun x : ℝ => (((1-x^2)^μ:ℝ):ℂ)) 1 :=
        continuous_ofReal.continuousAt.comp ((Real.continuousAt_rpow_const _ _ (Or.inr hμ.le)).comp
          (by fun_prop))
      have h := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
      rwa [show (1:ℝ)-1^2 = 0 by norm_num, Real.zero_rpow hμ.ne', ofReal_zero] at h
    have := hz.mul hP
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
    have h0 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
    simp only [conicalP, ← hνdef]
    rw [← mul_assoc]; congr 1
    rw [show (1-(x:ℂ)^2) = ((1-x^2:ℝ):ℂ) by push_cast; ring, legTor_cpow_real h0,
      legTor_cpow_real h0, ofReal_cpow h0.le, legTor_cpow_real h0, ← exp_add]
    congr 1; ring
  have h2 := legCon_tendsto_P_neg ν hμ
  have hsum : Tendsto (fun x : ℝ => (1-(x:ℂ)^2)^((μ:ℂ)/2) * conicalQHat τ (1*μ) x) (𝓝[<] 1)
      (𝓝 (A*0 + B*((2:ℂ)^(μ:ℂ) * (Gamma (μ:ℂ) * ((Gamma ((μ:ℂ)-ν))⁻¹ * (Gamma ((μ:ℂ)+ν+1))⁻¹))))) := by
    refine ((h1.const_mul A).add (h2.const_mul B)).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
    rw [one_mul, conicalQHat_connection hτ hμ.le hex hx]
    simp only [conicalP, ← hνdef, A, B]
    ring
  simp only [mul_zero, zero_add] at hsum
  set N : ℝ := Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π) with hNdef
  set D : ℝ := (Real.cosh (τ*π))^2-(Real.sin (μ*π))^2 with hDdef
  have hcos : τ = 0 → Real.cos (μ*π) ≠ 0 := by
    intro h0
    have hh : ∀ n : ℕ, μ ≠ n+1/2 := hex.resolve_left (fun h => h h0)
    have := legBd_cos_ne_zero (μ := (μ:ℂ)) (by simpa using hμ)
      (fun n hn => hh n (by have := congrArg Complex.re hn; simpa using this))
    intro hc; apply this; rw [show (μ:ℂ)*π = ((μ*π:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, hc, ofReal_zero]
  have hN : 0 < N := by
    rcases eq_or_lt_of_le hτ with h0 | hpos
    · rw [hNdef, ← h0]; simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, Real.sinh_zero, add_zero]
      have := hcos h0.symm
      positivity
    · have := Real.sinh_pos_iff.mpr (mul_pos hpos Real.pi_pos)
      have : 0 ≤ Real.exp (-τ*π)*(Real.cos (μ*π))^2 := by positivity
      linarith
  have hD : 0 < D := by
    rcases eq_or_lt_of_le hτ with h0 | hpos
    · rw [hDdef, ← h0]; simp only [zero_mul, Real.cosh_zero, one_pow]
      have := hcos h0.symm
      have h1 := Real.sin_sq_add_cos_sq (μ*π)
      have : 0 < Real.cos (μ*π)^2 := by positivity
      linarith
    · have h1 : 1 < Real.cosh (τ*π) := Real.one_lt_cosh.mpr (mul_pos hpos Real.pi_pos).ne'
      have h2 := Real.sin_sq_le_one (μ*π)
      nlinarith
  have hB : B = ((π*N/(2*D):ℝ):ℂ) := by simp only [B, hNdef, hDdef]; push_cast; ring
  have hB0 : B ≠ 0 := by rw [hB]; exact ofReal_ne_zero.mpr (by positivity)
  have hre1 : 0 < ((μ:ℂ)-ν).re := by simp [hνdef]; linarith
  have hre2 : 0 < ((μ:ℂ)+ν+1).re := by simp [hνdef]; linarith
  have hG1 := Gamma_ne_zero_of_re_pos hre1
  have hG2 := Gamma_ne_zero_of_re_pos hre2
  have hGm : Gamma (μ:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hμ)
  have hK : B*((2:ℂ)^(μ:ℂ) * (Gamma (μ:ℂ) * ((Gamma ((μ:ℂ)-ν))⁻¹ * (Gamma ((μ:ℂ)+ν+1))⁻¹))) ≠ 0 := by
    refine mul_ne_zero hB0 (mul_ne_zero (by simp) (mul_ne_zero hGm (mul_ne_zero ?_ ?_))) <;>
      exact inv_ne_zero (by assumption)
  have := legBd_isEquivalent_of_tendsto hsum (legBd_tendsto_weight_left (μ:ℂ)) hK (by simp)
  refine this.congr_right (Eventually.of_forall fun x => ?_)
  have hg : Gamma ((μ:ℂ)-ν) * Gamma ((μ:ℂ)+ν+1) = (‖Gamma ((μ:ℂ)+1/2+I*τ)‖:ℂ)^2 := by
    rw [show (μ:ℂ)+ν+1 = (μ:ℂ)+1/2+I*τ by rw [hνdef]; ring,
      show (μ:ℂ)-ν = (starRingEnd ℂ) ((μ:ℂ)+1/2+I*τ) by
        apply Complex.ext <;> (simp [hνdef]; try norm_num),
      Complex.Gamma_conj, Complex.conj_mul']
  have h2 : (2:ℂ)^(μ:ℂ) ≠ 0 := by simp
  simp only
  rw [show B*((2:ℂ)^(μ:ℂ) * (Gamma (μ:ℂ) * ((Gamma ((μ:ℂ)-ν))⁻¹ * (Gamma ((μ:ℂ)+ν+1))⁻¹))) / 2^(μ:ℂ)
      = B * Gamma (μ:ℂ) / (Gamma ((μ:ℂ)-ν) * Gamma ((μ:ℂ)+ν+1)) by field_simp, hg, hB]
  have eN : ((Real.exp (-τ*π):ℂ)*(Real.cos (μ*π):ℂ)^2+(Real.sinh (τ*π):ℂ)) = (N:ℂ) := by
    simp only [hNdef]; push_cast; ring
  have eD : ((Real.cosh (τ*π):ℂ)^2-(Real.sin (μ*π):ℂ)^2) = (D:ℂ) := by
    simp only [hDdef]; push_cast; ring
  rw [eN, eD]
  push_cast
  ring

/-- DLMF 14.20.9 (Mehler's integral): for real `τ` and `0 < θ < π`, `𝖯_{-1/2+iτ}(cos θ) = (2/π) ∫₀^θ
cosh(τt)/√(2(cos t - cos θ)) dt`. -/
@[dlmf 14.20.E9]
theorem conical_mehler_integral (τ : ℝ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    conicalP τ 0 (Real.cos θ)=2/π*∫ t : ℝ in 0..θ, (Real.cosh (τ*t)/Real.sqrt (2*(Real.cos t-Real.cos θ)):ℂ) := by
  sorry

/-- The conical Pochhammer product `(1/2+iτ)ₖ(1/2-iτ)ₖ = ∏ (4τ²+(2j+1)²)/4ᵏ`. -/
theorem poch_conical (τ : ℝ) (k : ℕ) :
    poch (1/2+I*τ) k * poch (1/2-I*τ) k = (∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2:ℂ))/4^k := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, poch_succ, Finset.prod_range_succ, pow_succ,
      show poch (1/2+I*τ) k * (1/2+I*τ+k) * (poch (1/2-I*τ) k * (1/2-I*τ+k)) =
        (poch (1/2+I*τ) k * poch (1/2-I*τ) k) * ((1/2+I*τ+k)*(1/2-I*τ+k)) by ring, ih]
    have : (1/2+I*τ+k)*(1/2-I*τ+k) = (4*τ^2+(2*k+1)^2:ℂ)/4 := by
      linear_combination (-(τ:ℂ)^2) * I_sq
    rw [this]; field_simp; ring

/-- The singular endpoint θ=π is excluded from a finite-valued convergence assertion. -/
@[dlmf 14.20.E10]
theorem conical_power_series (τ : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < π) :
    HasSum (fun k : ℕ => (∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2:ℂ))/(4^k*(k.factorial:ℂ)^2)*(Real.sin (θ/2):ℂ)^(2*k)) (conicalP τ 0 (Real.cos θ)) := by
  have hs : (1-(Real.cos θ:ℂ))/2 = (Real.sin (θ/2):ℂ)^2 := by
    have h1 := Real.cos_two_mul (θ/2)
    have h2 := Real.sin_sq_add_cos_sq (θ/2)
    rw [show 2*(θ/2) = θ by ring] at h1
    have h3 : (Real.cos θ:ℂ) = 1 - 2*(Real.sin (θ/2):ℂ)^2 := by
      exact_mod_cast (by linear_combination h1 + 2*h2 : Real.cos θ = 1 - 2*Real.sin (θ/2)^2)
    rw [h3]; ring
  have hw : ‖(Real.sin (θ/2):ℂ)^2‖ < 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h1 : Real.sin (θ/2) < 1 := by
      rw [← Real.sin_pi_div_two]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have h2 : 0 ≤ Real.sin (θ/2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    nlinarith
  have h := hasSum_regularizedGaussHGFun_coeff (1/2+I*τ) (1/2-I*τ) 1 hw
  have e : conicalP τ 0 (Real.cos θ) = regularizedGaussHGFun (1/2+I*τ) (1/2-I*τ) 1 ((Real.sin (θ/2):ℂ)^2) := by
    unfold conicalP ferrersP
    rw [hs, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw]
    simp only [ofReal_zero, neg_zero, zero_div, cpow_zero, one_mul, sub_zero]
    congr 1 <;> ring
  rw [e]
  refine h.congr_fun fun k => ?_
  rw [poch_conical, add_comm (1:ℂ), Gamma_nat_eq_factorial, ← pow_mul]
  field_simp

/-- Positivity stated in DLMF 14.20(v). -/
theorem conical_positive (τ : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < π) :
    0 < (conicalP τ 0 (Real.cos θ)).re := by
  have h := Complex.reCLM.hasSum (conical_power_series τ h0 hπ)
  set g : ℕ → ℝ := fun k => (∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2))/(4^k*(k.factorial:ℝ)^2)*
    (Real.sin (θ/2))^(2*k) with hg
  have he : ∀ k : ℕ, Complex.reCLM ((∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2:ℂ))/(4^k*(k.factorial:ℂ)^2)*
      (Real.sin (θ/2):ℂ)^(2*k)) = g k := by
    intro k
    have : ((∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2:ℂ))/(4^k*(k.factorial:ℂ)^2)*
      (Real.sin (θ/2):ℂ)^(2*k)) = ((g k : ℝ) : ℂ) := by simp only [hg]; push_cast; rfl
    rw [this]; simp
  simp only [he] at h
  have hnn : ∀ k, 0 ≤ g k := fun k => by
    simp only [hg]
    refine mul_nonneg (div_nonneg (Finset.prod_nonneg fun j _ => by positivity) (by positivity)) ?_
    rw [pow_mul]; positivity
  have h1 := le_hasSum h 0 (fun j _ => hnn j)
  simp [hg] at h1
  simpa using lt_of_lt_of_le one_pos h1

/-- DLMF 14.20.11: the generalized Mehler–Fock transform `f(τ) = (τ/π) sinh(τπ) Γ(1/2-μ+iτ)
Γ(1/2-μ-iτ) ∫₁^∞ P^μ_{-1/2+iτ}(x) g(x) dx`, taken as an improper integral at `+∞`. -/
@[dlmf 14.20.E11]
def mehlerFockTransform (μ : ℝ) (g : ℝ → ℂ) (τ : ℝ) : ℂ :=
  τ/π*Real.sinh (τ*π)*Gamma (1/2-μ+I*τ)*Gamma (1/2-μ-I*τ)*improperAtTop (fun x : ℝ => associatedP (-1/2+I*τ) μ x*g x) 1

/-- DLMF 14.20.12: the inverse Mehler–Fock transform `g(x) = ∫₀^∞ P^μ_{-1/2+iτ}(x) f(τ) dτ`, taken
as an improper integral at `+∞`. -/
@[dlmf 14.20.E12]
def mehlerFockInverse (μ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  improperAtTop (fun τ : ℝ => associatedP (-1/2+I*τ) μ x*f τ) 0

/-- DLMF 14.20.13: for real `τ` and `x > 1`, the improper integral `(cosh(τπ)/π) ∫₁^∞
P_{-1/2+iτ}(t)/(x+t) dt` converges to `P_{-1/2+iτ}(x)`. -/
@[dlmf 14.20.E13]
theorem conical_stieltjes_integral (τ : ℝ) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => Real.cosh (τ*π)/π*associatedP (-1/2+I*τ) 0 t/(x+t)) 1 (associatedP (-1/2+I*τ) 0 x) := by
  sorry

/-- DLMF 14.20.14: for `x, y > 1`, the improper integral `∫₀^∞ π τ tanh(τπ)/cosh(τπ) P_{-1/2+iτ}(x)
P_{-1/2+iτ}(y) dτ` converges to `1/(x+y)`. -/
@[dlmf 14.20.E14]
theorem conical_product_transform {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    HasIntegralAtTop (fun τ : ℝ => π*τ*Real.tanh (τ*π)/Real.cosh (τ*π)*associatedP (-1/2+I*τ) 0 x*associatedP (-1/2+I*τ) 0 y) 0 (1/(y+x:ℂ)) := by
  sorry

end DLMF.Legendre
