/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.BesselIntegral
public import ToMathlib.Analysis.SpecialFunctions.Bessel

/-!
# Graf's addition theorem (DLMF 10.23.7)

With `u - v cos α = w cos χ`, `v sin α = w sin χ` (DLMF 10.23.8) we have
`w e^{±iχ} = u - v e^{∓iα}`, so on the circle `t = e^{iθ}` the generating functions combine:
`e^{(w/2)(e^{iχ}t - e^{-iχ}/t)} = e^{(u/2)(t - 1/t)} e^{(v/2)(s - 1/s)}`, `s = -e^{-iα} t`.
Comparing Fourier coefficients (term-by-term integration against `e^{-inθ}`, with Bessel's
integral for the factor `e^{iu sin θ}`) gives `J_n(w) e^{inχ} = ∑_k J_{n+k}(u) J_k(v) e^{ikα}`
for every integer `n` and all complex `u`, `v`, `α` (no restriction `|v e^{±iα}| < |u|` is needed
at integer order of `J`).
-/

@[expose] public section

open Complex
open scoped Real Nat

noncomputable section

namespace DLMF.Bessel

/-- `‖e^{imχ}‖ ≤ (e^{|Im χ|})^{|m|}`. -/
lemma p3m_norm_exp_I_mul_int (m : ℤ) (χ : ℂ) :
    ‖exp (I * m * χ)‖ ≤ Real.exp |χ.im| ^ m.natAbs := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have : (I * (m : ℂ) * χ).re = -((m : ℝ) * χ.im) := by simp
  rw [this, Nat.cast_natAbs]
  have h1 : -((m : ℝ) * χ.im) ≤ |(m : ℝ) * χ.im| := neg_le_abs _
  rw [abs_mul] at h1
  push_cast at h1 ⊢
  exact h1

/-- `∑_m ‖J_m(z)‖ R^{|m|} < ∞`. -/
lemma p3m_summable_besselJ_weight (z : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun m : ℤ => ‖besselJ m z‖ * R ^ m.natAbs := by
  have hs : Summable fun m : ℤ => Real.exp (‖z‖ ^ 2 / 4) *
      ((‖z‖ / 2 * R) ^ m.natAbs / (m.natAbs ! : ℝ)) := by
    refine Summable.mul_left _ ?_
    refine Summable.of_nat_of_neg ?_ ?_
    · simpa using Real.summable_pow_div_factorial (‖z‖ / 2 * R)
    · simpa using Real.summable_pow_div_factorial (‖z‖ / 2 * R)
  refine hs.of_nonneg_of_le (fun m => by positivity) fun m => ?_
  have hb := Complex.norm_besselJ_intCast_le m z
  calc ‖besselJ m z‖ * R ^ m.natAbs ≤ Real.exp (‖z‖ ^ 2 / 4) *
        ((‖z‖ / 2) ^ m.natAbs / (m.natAbs ! : ℝ)) * R ^ m.natAbs := by gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Term-by-term integration over a period under a summable uniform bound. -/
lemma p3m_hasSum_integral {F : ℤ → ℝ → ℂ} {f : ℝ → ℂ} {b : ℤ → ℝ}
    (hcont : ∀ m, Continuous (F m)) (hb : ∀ m θ, ‖F m θ‖ ≤ b m) (hbs : Summable b)
    (hlim : ∀ θ, HasSum (fun m => F m θ) (f θ)) :
    HasSum (fun m => ∫ θ in (0 : ℝ)..2 * π, F m θ) (∫ θ in (0 : ℝ)..2 * π, f θ) :=
  intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π) (F := F) (f := f)
    (fun m _ => b m) (fun m => (hcont m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall fun θ _ => hb m θ)
    (Filter.Eventually.of_forall fun _ _ => hbs) intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => hlim θ)

/-- `(z/2)(e^{iθ} - e^{-iθ}) = iz sin θ`. -/
lemma p3m_gen_sin (z : ℂ) (θ : ℝ) :
    z / 2 * (exp (I * θ) - (exp (I * θ))⁻¹) = I * z * sin θ := by
  rw [← exp_neg, sin, show -(I * (θ : ℂ)) = -(θ : ℂ) * I by ring,
    show I * (θ : ℂ) = (θ : ℂ) * I by ring]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Graf's addition theorem** (DLMF 10.23.7) for `J` at integer order, with the geometry of
DLMF 10.23.8 (`u - v cos α = w cos χ`, `v sin α = w sin χ`):
`J_n(w) e^{inχ} = ∑_{k∈ℤ} J_{n+k}(u) J_k(v) e^{ikα}`. Stronger than DLMF: all complex `u`, `v`,
`α`, without the condition `|v e^{±iα}| < |u|`. -/
@[dlmf 10.23.E7]
theorem hasSum_besselJ_graf (n : ℤ) {u v w α χ : ℂ} (hc : w * cos χ = u - v * cos α)
    (hs : w * sin χ = v * sin α) :
    HasSum (fun k : ℤ => besselJ (n + k : ℤ) u * besselJ k v * exp (I * k * α))
      (besselJ n w * exp (I * n * χ)) := by
  have hA : w * exp (I * χ) = u - v * exp (-(I * α)) := by
    rw [show I * χ = χ * I by ring, exp_mul_I, show -(I * α) = -α * I by ring, exp_mul_I,
      cos_neg, sin_neg]
    linear_combination hc + I * hs
  have hB : w * exp (-(I * χ)) = u - v * exp (I * α) := by
    rw [show -(I * χ) = -χ * I by ring, exp_mul_I, show I * α = α * I by ring, exp_mul_I,
      cos_neg, sin_neg]
    linear_combination hc - I * hs
  set E := exp (I * χ)
  set Ea := exp (-(I * α))
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hEa0 : Ea ≠ 0 := exp_ne_zero _
  have hEinv : E⁻¹ = exp (-(I * χ)) := by rw [exp_neg]
  have hEainv : Ea⁻¹ = exp (I * α) := by simp only [Ea]; rw [exp_neg, inv_inv]
  set τ : ℝ → ℂ := fun θ => exp (I * θ)
  have hτ0 : ∀ θ, τ θ ≠ 0 := fun θ => exp_ne_zero _
  have hτpow : ∀ (m : ℤ) θ, τ θ ^ m = exp (I * m * θ) := by
    intro m θ; simp only [τ]; rw [← exp_int_mul]; ring_nf
  -- the combined generating function
  set G : ℝ → ℂ := fun θ => exp (w / 2 * (E * τ θ - (E * τ θ)⁻¹))
  have hG : ∀ θ, G θ = exp (I * u * sin θ) *
      exp (v / 2 * (-Ea * τ θ - (-Ea * τ θ)⁻¹)) := by
    intro θ
    have h1 := hτ0 θ
    have key : w / 2 * (E * τ θ - (E * τ θ)⁻¹) =
        u / 2 * (τ θ - (τ θ)⁻¹) + v / 2 * (-Ea * τ θ - (-Ea * τ θ)⁻¹) := by
      rw [mul_inv, mul_inv, ← neg_inv, hEinv, hEainv]
      linear_combination (τ θ / 2) * hA - ((τ θ)⁻¹ / 2) * hB
    have hs' : u / 2 * (τ θ - (τ θ)⁻¹) = I * u * sin θ := p3m_gen_sin u θ
    simp only [G]
    rw [key, exp_add, hs']
  have hπ : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  -- first evaluation of `∫ G e^{-inθ}`
  set F1 : ℤ → ℝ → ℂ := fun m θ => besselJ m w * E ^ m * exp (I * (m - n : ℤ) * θ)
  have h1 : HasSum (fun m => ∫ θ in (0 : ℝ)..2 * π, F1 m θ)
      (∫ θ in (0 : ℝ)..2 * π, G θ * exp (-(I * n * θ))) := by
    refine p3m_hasSum_integral (b := fun m => ‖besselJ m w‖ * Real.exp |χ.im| ^ m.natAbs)
      (fun m => by simp only [F1]; fun_prop) (fun m θ => ?_)
      (p3m_summable_besselJ_weight w (Real.exp_pos _).le) (fun θ => ?_)
    · simp only [F1]
      rw [norm_mul, norm_mul, show I * ((m - n : ℤ) : ℂ) * (θ : ℂ) =
        ((((m - n : ℤ) : ℝ) * θ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I,
        mul_one]
      gcongr
      simp only [E]
      rw [← exp_int_mul, show (m : ℂ) * (I * χ) = I * m * χ by ring]
      exact p3m_norm_exp_I_mul_int m χ
    · have h := (hasSum_besselJ_generating_function w (E * τ θ)
        (mul_ne_zero hE0 (hτ0 θ))).mul_right (exp (-(I * n * θ)))
      convert h using 1
      funext m
      simp only [F1]
      rw [mul_zpow, hτpow]
      have : exp (I * ((m - n : ℤ) : ℂ) * θ) = exp (I * m * θ) * exp (-(I * n * θ)) := by
        rw [← exp_add]; congr 1; push_cast; ring
      rw [this]; ring
  have h1' : HasSum (fun m => ∫ θ in (0 : ℝ)..2 * π, F1 m θ)
      (2 * π * (besselJ n w * E ^ n)) := by
    have e : (fun m => ∫ θ in (0 : ℝ)..2 * π, F1 m θ) =
        fun m => if m = n then 2 * π * (besselJ n w * E ^ n) else 0 := by
      funext m
      simp only [F1]
      rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
      split_ifs with h2 h3 h3
      · rw [h3]; push_cast; ring
      · exact absurd (by omega) h3
      · exact absurd (by omega) h2
      · simp
    rw [e]
    exact hasSum_ite_eq n _
  -- second evaluation
  set F2 : ℤ → ℝ → ℂ := fun k θ => besselJ k v * (-1) ^ k * Ea ^ k *
    exp (I * (k - n : ℤ) * θ) * exp (I * u * sin θ)
  have h2 : HasSum (fun k => ∫ θ in (0 : ℝ)..2 * π, F2 k θ)
      (∫ θ in (0 : ℝ)..2 * π, G θ * exp (-(I * n * θ))) := by
    refine p3m_hasSum_integral
      (b := fun k => ‖besselJ k v‖ * Real.exp |(-α).im| ^ k.natAbs * Real.exp ‖u‖)
      (fun m => by simp only [F2]; fun_prop) (fun k θ => ?_)
      ((p3m_summable_besselJ_weight v (Real.exp_pos _).le).mul_right _) (fun θ => ?_)
    · simp only [F2]
      rw [norm_mul, norm_mul, norm_mul, norm_mul, show I * ((k - n : ℤ) : ℂ) * (θ : ℂ) =
        ((((k - n : ℤ) : ℝ) * θ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I,
        mul_one, norm_zpow, norm_neg, norm_one, one_zpow, mul_one]
      gcongr
      · simp only [Ea]
        rw [← exp_int_mul, show (k : ℂ) * -(I * α) = I * k * (-α) by ring]
        exact p3m_norm_exp_I_mul_int k (-α)
      · refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_mul, norm_mul, norm_I, one_mul]
        have hs : ‖sin (θ : ℂ)‖ ≤ 1 := by
          rw [← ofReal_sin, norm_real, Real.norm_eq_abs]
          exact Real.abs_sin_le_one θ
        calc ‖u‖ * ‖sin (θ : ℂ)‖ ≤ ‖u‖ * 1 := by gcongr
          _ = ‖u‖ := mul_one _
    · have h := (hasSum_besselJ_generating_function v (-Ea * τ θ)
        (mul_ne_zero (neg_ne_zero.mpr hEa0) (hτ0 θ))).mul_right
          (exp (I * u * sin θ) * exp (-(I * n * θ)))
      rw [hG]
      convert h using 1
      · funext k
        simp only [F2]
        rw [mul_zpow, hτpow,
          show (-Ea) ^ k = (-1) ^ k * Ea ^ k by rw [neg_eq_neg_one_mul, mul_zpow]]
        have : exp (I * ((k - n : ℤ) : ℂ) * θ) = exp (I * k * θ) * exp (-(I * n * θ)) := by
          rw [← exp_add]; congr 1; push_cast; ring
        rw [this]; ring
      · ring
  have h2' : HasSum (fun k => ∫ θ in (0 : ℝ)..2 * π, F2 k θ)
      (2 * π * (besselJ n w * E ^ n)) := by
    rw [h1.unique h1'] at h2; exact h2
  have e2 : ∀ k : ℤ, ∫ θ in (0 : ℝ)..2 * π, F2 k θ =
      2 * π * (besselJ (n - k : ℤ) u * (besselJ k v * (-1) ^ k * Ea ^ k)) := by
    intro k
    have he : (fun θ : ℝ => F2 k θ) = fun θ : ℝ => besselJ k v * (-1) ^ k * Ea ^ k *
        exp (I * (u * sin θ - ((n - k : ℤ) : ℂ) * θ)) := by
      funext θ
      simp only [F2]
      rw [mul_assoc _ (exp _), ← exp_add]
      congr 2
      push_cast; ring
    rw [he, intervalIntegral.integral_const_mul, besselJ_int_eq_integral_exp (n - k) u]
    field_simp
  simp only [e2] at h2'
  have h3 := (h2'.div_const (2 * π))
  have h4 : HasSum (fun k : ℤ => besselJ (n - k : ℤ) u * (besselJ k v * (-1) ^ k * Ea ^ k))
      (besselJ n w * E ^ n) := by
    convert h3 using 1
    · funext k; field_simp
    · field_simp
  have h5 := (Equiv.neg ℤ).hasSum_iff.mpr h4
  convert h5 using 1
  · funext k
    simp only [Function.comp_apply, Equiv.neg_apply, sub_neg_eq_add]
    rw [Int.cast_neg, besselJ_neg_int, zpow_neg, zpow_neg]
    simp only [Ea]
    rw [← exp_int_mul, ← exp_neg, show -((k : ℂ) * -(I * α)) = I * k * α by ring]
    have : ((-1 : ℂ) ^ k)⁻¹ = (-1) ^ k := by
      rw [← inv_zpow, inv_neg, inv_one]
    rw [this]
    have hk : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
      rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
    linear_combination -(besselJ ((n + k : ℤ) : ℂ) u * besselJ (k : ℂ) v * exp (I * k * α)) * hk
  · simp only [E]; rw [← exp_int_mul]; ring_nf

end DLMF.Bessel
