/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals.AngularRepresentations

/-!
# Gegenbauer and Legendre product integrals

Laplace representations and angular product formulas for Gegenbauer and Legendre polynomials.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Integrals`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

open DLMF.Bessel

open DLMF.Gamma (Gamma_add_nat_eq_poch_mul_Gamma)

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

section GegenbauerLaplace

open Set

/-- `∫₀^π sin^{2λ-1} = √π Γ(λ)/Γ(λ+1/2)` for `λ > 0`, from the trigonometric Beta integral,
together with the integrability of `sin^{2λ-1}` on `[0, π]`. -/
theorem integral_sin_rpow_aux {lam : ℝ} (hlam : 0 < lam) :
    IntervalIntegrable (fun t : ℝ => Real.sin t ^ (2 * lam - 1)) volume 0 π ∧
    ∫ t in (0 : ℝ)..π, Real.sin t ^ (2 * lam - 1) =
      Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) := by
  have hB := DLMF.Gamma.beta_sin_cos (a := lam) (b := 1 / 2) hlam (by norm_num)
  simp only [show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, mul_one,
    Real.Gamma_one_half_eq] at hB
  set f : ℝ → ℝ := fun t => Real.sin t ^ (2 * lam - 1) with hf
  have hpos : 0 < (1 / 2) * (Real.Gamma lam * Real.sqrt π / Real.Gamma (lam + 1 / 2)) := by
    have := Real.Gamma_pos_of_pos hlam
    have := Real.Gamma_pos_of_pos (show 0 < lam + 1 / 2 by linarith)
    have := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  have hI1 : IntervalIntegrable f volume 0 (π / 2) := by
    by_contra h
    rw [intervalIntegral.integral_undef h] at hB
    linarith
  have hsymm : ∀ t, f (π - t) = f t := fun t => by simp [hf, Real.sin_pi_sub]
  have hI2 : IntervalIntegrable f volume (π / 2) π := by
    have := hI1.comp_sub_left π
    simp only [hsymm, sub_zero, show π - π / 2 = π / 2 by ring] at this
    exact this.symm
  refine ⟨hI1.trans hI2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  have h2 := intervalIntegral.integral_comp_sub_left f (a := 0) (b := π / 2) π
  rw [show π - π / 2 = π / 2 by ring, sub_zero] at h2
  simp only [hsymm] at h2
  rw [← h2, hB]
  ring

/-- The weighted Laplace integral `∫₀^π (cos θ + i sin θ cos φ)ⁿ sin^{2λ-1} φ dφ`. -/
def gegenbauerLaplace (lam θ : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n *
    ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)

/-- The weighted Laplace integrals satisfy the normalized Gegenbauer recurrence. -/
theorem gegenbauerLaplace_recurrence {lam : ℝ} (hlam : 0 < lam) (θ : ℝ) (n : ℕ) :
    (n + 1 + 2 * lam : ℂ) * gegenbauerLaplace lam θ (n + 2) =
      2 * (n + 1 + lam) * Real.cos θ * gegenbauerLaplace lam θ (n + 1) -
        (n + 1) * gegenbauerLaplace lam θ n := by
  set c : ℂ := (Real.cos θ : ℂ) with hc
  set s : ℂ := (Real.sin θ : ℂ) with hs
  set w : ℝ → ℂ := fun t => c + I * s * Real.cos t with hw
  set ρ : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
  have hρi : IntervalIntegrable ρ volume 0 π := by
    have := (integral_sin_rpow_aux hlam).1
    exact ⟨this.1.ofReal, this.2.ofReal⟩
  have hU : uIcc (0 : ℝ) π = Icc 0 π := uIcc_of_le Real.pi_pos.le
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq]; simp
  have hsplit : ∀ x : ℝ, 0 ≤ x → x ^ (2 * lam) = x * x ^ (2 * lam - 1) := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst h; rw [Real.zero_rpow (by positivity), zero_mul]
    · rw [← Real.rpow_one_add' h.le (by linarith)]; ring_nf
  -- `F' = ρ g` is the derivative of `F = w^{n+1} sin^{2λ}` on `(0, π)`
  set g : ℝ → ℂ := fun t => (n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) * Real.sin t +
    w t ^ (n + 1) * (2 * lam * Real.cos t) with hg
  have hgc : Continuous g := by fun_prop
  have hD : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivAt (fun t : ℝ => w t ^ (n + 1) *
      ((Real.sin t ^ (2 * lam) : ℝ) : ℂ)) (ρ t * g t) t := by
    intro t ht
    have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hwd : HasDerivAt w (-(I * s) * Real.sin t) t := by
      have := ((Real.hasDerivAt_cos t).ofReal_comp).const_mul (I * s)
      exact (this.const_add c).congr_deriv (by push_cast; ring)
    have hr := ((Real.hasDerivAt_sin t).rpow_const (p := 2 * lam) (Or.inl hst.ne')).ofReal_comp
    have := (hwd.pow (n + 1)).mul hr
    refine this.congr_deriv ?_
    simp only [hρ, hg, Nat.add_sub_cancel, Pi.pow_apply]
    rw [hsplit _ hst.le]
    push_cast
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
    ((by fun_prop : Continuous fun t : ℝ => w t ^ (n + 1)).continuousOn.mul
      (Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by positivity)).comp
        Real.continuous_sin)).continuousOn) hD (hρi.mul_continuousOn (hU ▸ hgc.continuousOn))
  simp only [Pi.mul_apply, Function.comp_apply, Real.sin_pi, Real.sin_zero,
    Real.zero_rpow (by positivity : 2 * lam ≠ 0), Complex.ofReal_zero, mul_zero, sub_zero] at hFTC
  -- multiply by `i s`
  have hpt : ∀ t : ℝ, I * s * (ρ t * g t) = ρ t * ((n + 1) * w t ^ n -
      2 * (n + 1 + lam) * c * w t ^ (n + 1) + (n + 1 + 2 * lam) * w t ^ (n + 2)) := by
    intro t
    have htrig : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.sin_sq_add_cos_sq]; simp
    simp only [hg, hw]
    linear_combination (ρ t * (n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * (-I ^ 2 * s ^ 2)) *
      htrig - (ρ t * (n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * s ^ 2) * Complex.I_sq +
      (ρ t * (n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n) * hcs
  have h0 : ∫ t : ℝ in (0 : ℝ)..π, I * s * (ρ t * g t) = 0 := by
    rw [intervalIntegral.integral_const_mul, hFTC]; simp
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)] at h0
  have hk : ∀ k : ℕ, IntervalIntegrable (fun t => w t ^ k * ρ t) volume 0 π :=
    fun k => hρi.continuousOn_mul (hU ▸ (by fun_prop : Continuous fun t : ℝ => w t ^ k).continuousOn)
  have hsplit3 : ∀ t : ℝ, ρ t * ((n + 1) * w t ^ n - 2 * (n + 1 + lam) * c * w t ^ (n + 1) +
      (n + 1 + 2 * lam) * w t ^ (n + 2)) = (n + 1) * (w t ^ n * ρ t) -
      2 * (n + 1 + lam) * c * (w t ^ (n + 1) * ρ t) + (n + 1 + 2 * lam) * (w t ^ (n + 2) * ρ t) :=
    fun t => by ring
  rw [intervalIntegral.integral_congr (fun t _ => hsplit3 t),
    intervalIntegral.integral_add (((hk n).const_mul _).sub ((hk (n + 1)).const_mul _))
      ((hk (n + 2)).const_mul _),
    intervalIntegral.integral_sub ((hk n).const_mul _) ((hk (n + 1)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  simp only [gegenbauerLaplace]
  linear_combination h0

/-- Identity under the stated parameter and domain assumptions: `ultrasphPoly lam n (Real.cos θ) /
ultrasphPoly lam n 1 = Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) * ∫ phi
: ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n * (Real.rpow
(Real.sin phi) (2 * lam - 1) : ℂ)`. -/
@[dlmf 18.10.E4]
theorem ultrasphPoly_laplace_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (θ : ℝ) :
    ultrasphPoly lam n (Real.cos θ) / ultrasphPoly lam n 1 =
      Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) *
        ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ) := by
  obtain ⟨hρi', hρint⟩ := integral_sin_rpow_aux hlam
  set K : ℂ := ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) with hK
  have hG1 : 0 < Real.Gamma (lam + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam
  have hsq : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hK0 : K ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hlamC : 0 < (lam : ℂ).re := by simpa using hlam
  -- the normalized polynomials
  set R : ℕ → ℂ := fun n => ultrasphPoly lam n (Real.cos θ) / ultrasphPoly lam n 1 with hR
  have hbase0 : gegenbauerLaplace lam θ 0 = K := by
    simp only [gegenbauerLaplace, pow_zero, one_mul, hK]
    rw [intervalIntegral.integral_ofReal, hρint]
  have hcos0 : ∫ t : ℝ in (0 : ℝ)..π, (Real.cos t * Real.sin t ^ (2 * lam - 1) : ℝ) = 0 := by
    have hD : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivAt (fun t : ℝ => Real.sin t ^ (2 * lam) / (2 * lam))
        (Real.cos t * Real.sin t ^ (2 * lam - 1)) t := by
      intro t ht
      have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
      have := ((Real.hasDerivAt_sin t).rpow_const (p := 2 * lam) (Or.inl hst.ne')).div_const
        (2 * lam)
      refine this.congr_deriv ?_
      field_simp
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
      (((Real.continuous_rpow_const (by positivity)).comp Real.continuous_sin).div_const
        (2 * lam)).continuousOn hD (hρi'.continuousOn_mul Real.continuous_cos.continuousOn)
    rw [h]
    simp [Real.zero_rpow (by positivity : 2 * lam ≠ 0)]
  have hbase1 : gegenbauerLaplace lam θ 1 = Real.cos θ * K := by
    simp only [gegenbauerLaplace, pow_one]
    have hsplit : ∀ t : ℝ, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) = Real.cos θ * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) +
          I * Real.sin θ * ((Real.cos t * Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) := by
      intro t; push_cast; ring
    have hρC : IntervalIntegrable (fun t : ℝ => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π :=
      ⟨hρi'.1.ofReal, hρi'.2.ofReal⟩
    have hψ := hρi'.continuousOn_mul Real.continuous_cos.continuousOn
    have hψC : IntervalIntegrable (fun t : ℝ => ((Real.cos t * Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ))
        volume 0 π := ⟨hψ.1.ofReal, hψ.2.ofReal⟩
    rw [intervalIntegral.integral_congr (fun t _ => hsplit t),
      intervalIntegral.integral_add (hρC.const_mul _) (hψC.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hρint, hcos0, hK]
    simp
  -- induction
  have hind : ∀ n : ℕ, gegenbauerLaplace lam θ n = K * R n ∧
      gegenbauerLaplace lam θ (n + 1) = K * R (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [hbase0]; simp [hR, ultrasphPoly_zero]
      · rw [hbase1]; simp only [hR, zero_add, ultrasphPoly_normalized_one hlamC]; ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hr := gegenbauerLaplace_recurrence hlam θ n
      have hP := ultrasphPoly_normalized_recurrence hlamC n (Real.cos θ)
      rw [ih.1, ih.2] at hr
      have hn : (n + 1 + 2 * lam : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      apply mul_left_cancel₀ hn
      rw [show n + 1 + 1 = n + 2 by ring, hr]
      simp only [hR]
      linear_combination (-K) * hP
  have hmain := (hind n).1
  have hGam : Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) = K⁻¹ := by
    rw [hK, show (lam + 1 / 2 : ℂ) = ((lam + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast
    field_simp
  rw [hGam, show (∫ phi : ℝ in (0 : ℝ)..Real.pi, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos phi) ^ n *
      (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ)) = gegenbauerLaplace lam θ n from rfl, hmain]
  field_simp
  rfl

end GegenbauerLaplace

/-- The Laplace integral `∫₀^π (cos θ + i sin θ cos t)^n dt`. -/
def legendreLaplace (θ : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n

/-- The Laplace integrals satisfy the Legendre recurrence. -/
theorem legendreLaplace_recurrence (θ : ℝ) (n : ℕ) :
    (n + 2 : ℂ) * legendreLaplace θ (n + 2) =
      (2 * n + 3) * Real.cos θ * legendreLaplace θ (n + 1) - (n + 1) * legendreLaplace θ n := by
  set c : ℂ := (Real.cos θ : ℂ) with hc
  set s : ℂ := (Real.sin θ : ℂ) with hs
  set w : ℝ → ℂ := fun t => c + I * s * Real.cos t with hw
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq]; simp
  -- the exact derivative `d/dt [w^{n+1} sin t]`
  have hD : ∀ t : ℝ, HasDerivAt (fun t : ℝ => w t ^ (n + 1) * (Real.sin t : ℂ))
      ((n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) * Real.sin t +
        w t ^ (n + 1) * Real.cos t) t := by
    intro t
    have hwd : HasDerivAt w (-(I * s) * Real.sin t) t := by
      have := ((Real.hasDerivAt_cos t).ofReal_comp).const_mul (I * s)
      exact (this.const_add c).congr_deriv (by push_cast; ring)
    have := (hwd.pow (n + 1)).mul (Real.hasDerivAt_sin t).ofReal_comp
    exact this.congr_deriv (by simp only [Pi.pow_apply, Nat.add_sub_cancel]; push_cast; ring)
  have hcont : Continuous fun t : ℝ => (n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) *
      Real.sin t + w t ^ (n + 1) * Real.cos t := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t)
    (hcont.intervalIntegrable 0 π)
  simp only [Real.sin_pi, Real.sin_zero, Complex.ofReal_zero, mul_zero, sub_zero] at hint
  -- multiply by `i s` and use the pointwise identity
  have hpt : ∀ t : ℝ, I * s * ((n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) * Real.sin t +
      w t ^ (n + 1) * Real.cos t) = (n + 1) * w t ^ n - (2 * n + 3) * c * w t ^ (n + 1) +
        (n + 2) * w t ^ (n + 2) := by
    intro t
    have htrig : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.sin_sq_add_cos_sq]; simp
    simp only [hw]
    linear_combination ((n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * (-I ^ 2 * s ^ 2)) * htrig -
      ((n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * s ^ 2) * Complex.I_sq +
      ((n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n) * hcs
  have h0 : ∫ t : ℝ in (0 : ℝ)..π, I * s * ((n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) *
      Real.sin t + w t ^ (n + 1) * Real.cos t) = 0 := by
    rw [intervalIntegral.integral_const_mul, hint]; simp
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)] at h0
  have hc' : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => w t ^ k) volume 0 π :=
    fun k => (by fun_prop : Continuous fun t : ℝ => w t ^ k).intervalIntegrable 0 π
  rw [intervalIntegral.integral_add (((hc' n).const_mul _).sub ((hc' (n + 1)).const_mul _))
    ((hc' (n + 2)).const_mul _), intervalIntegral.integral_sub ((hc' n).const_mul _)
    ((hc' (n + 1)).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
  simp only [legendreLaplace]
  linear_combination h0

/-- Identity under the stated parameter and domain assumptions: `legendrePolyP n (Real.cos θ) =
(Real.pi : ℂ)⁻¹ * ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi)
^ n`. -/
@[dlmf 18.10.E5]
theorem legendre_laplace_integral (n : ℕ) (θ : ℝ) :
    legendrePolyP n (Real.cos θ) = (Real.pi : ℂ)⁻¹ *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  suffices h : ∀ n : ℕ, legendreLaplace θ n = π * legendrePolyP n (Real.cos θ) ∧
      legendreLaplace θ (n + 1) = π * legendrePolyP (n + 1) (Real.cos θ) by
    rw [show (∫ t : ℝ in (0 : ℝ)..Real.pi, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n)
      = legendreLaplace θ n from rfl, (h n).1]
    field_simp
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [legendreLaplace, legendrePolyP_zero]
    · simp only [legendreLaplace, zero_add, pow_one, legendrePolyP_one]
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((by fun_prop : Continuous fun t : ℝ => I * (Real.sin θ : ℂ) * Real.cos t
          ).intervalIntegrable 0 π), intervalIntegral.integral_const_mul,
        show ∫ x in (0 : ℝ)..π, ((Real.cos x : ℝ) : ℂ) = ((∫ x in (0 : ℝ)..π, Real.cos x : ℝ) : ℂ)
          from intervalIntegral.integral_ofReal, integral_cos]
      simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hr := legendreLaplace_recurrence θ n
    have hP := legendrePolyP_recurrence n (Real.cos θ)
    rw [ih.1, ih.2] at hr
    have hn : (n + 2 : ℂ) ≠ 0 := by norm_cast
    apply mul_left_cancel₀ hn
    rw [hr]
    linear_combination (-(π : ℂ)) * hP

/-- `x^k e^{-xz} e^{-x²}` is integrable for every complex `z`. -/
theorem integrable_pow_mul_cexp_gauss (k : ℕ) (z : ℂ) :
    Integrable fun x : ℝ => (x : ℂ) ^ k * (cexp (-x * z) * cexp (-(x : ℂ) ^ 2)) := by
  have hreal : Integrable fun x : ℝ => x ^ k * Real.exp (-(1 / 2) * x ^ 2) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
      (s := (k : ℝ)) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.rpow_natCast]
  have hg : Integrable fun x : ℝ => (x : ℂ) ^ k * cexp (-(x : ℂ) ^ 2 / 2) := by
    refine hreal.norm.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, norm_pow,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply le_of_eq
    congr 2
    simp [sq]; ring
  set a := z.re
  have hbd : ∀ x : ℝ, ‖cexp (-x * z - (x : ℂ) ^ 2 / 2)‖ ≤ Real.exp (a ^ 2 / 2) := by
    intro x
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (-x * z - (x : ℂ) ^ 2 / 2).re = -x * a - x ^ 2 / 2 := by
      simp [a, sq]
    rw [this]
    nlinarith [sq_nonneg (x + a)]
  have hm : AEStronglyMeasurable (fun x : ℝ => cexp (-x * z - (x : ℂ) ^ 2 / 2)) volume :=
    (by fun_prop : Continuous fun x : ℝ => cexp (-x * z - (x : ℂ) ^ 2 / 2)).aestronglyMeasurable
  refine (hg.bdd_mul hm (Eventually.of_forall hbd)).congr (Eventually.of_forall fun x => ?_)
  beta_reduce
  have e : cexp (-↑x * z - (x : ℂ) ^ 2 / 2) * cexp (-(x : ℂ) ^ 2 / 2) =
      cexp (-↑x * z) * cexp (-(x : ℂ) ^ 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  linear_combination (x : ℂ) ^ k * e

/-- A polynomial times `e^{-xz} e^{-x²}` is integrable. -/
theorem integrable_eval_mul_cexp_gauss (q : ℝ[X]) (z : ℂ) :
    Integrable fun x : ℝ => cexp (-x * z) * ((q.eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) := by
  have hq : ∀ x : ℝ, cexp (-x * z) * ((q.eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      ∑ i ∈ Finset.range (q.natDegree + 1),
        (q.coeff i : ℂ) * ((x : ℂ) ^ i * (cexp (-x * z) * cexp (-(x : ℂ) ^ 2))) := fun x => by
    rw [eval_eq_sum_range, Finset.sum_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hq]
  exact integrable_finsetSum _ fun i _ => (integrable_pow_mul_cexp_gauss i z).const_mul _

/-- Repeated integration by parts against `e^{-xz}`. -/
theorem integral_cexp_mul_hermite_gauss (z : ℂ) (n : ℕ) :
    ∫ x : ℝ, cexp (-x * z) * (((hermitePolyHR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      (-z) ^ n * ∫ x : ℝ, cexp (-x * z) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) := by
  induction n with
  | zero => simp [hermitePolyHR]
  | succ n ih =>
    have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => cexp (-y * z)) (cexp (-x * z) * (-z)) x := by
      intro x
      have := ((hasDerivAt_id (x : ℂ)).neg.mul_const z).cexp.comp_ofReal (z := x)
      simpa using this
    have hv : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => (((hermitePolyHR n).eval y * Real.exp (-(y ^ 2)) : ℝ) : ℂ))
        (-((((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2))) : ℝ) : ℂ)) x := by
      intro x
      have := (hasDerivAt_hermite_gauss n x).ofReal_comp
      simpa using this
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hu x) (fun x _ => hv x)
      ((integrable_eval_mul_cexp_gauss (hermitePolyHR (n + 1)) z).neg.congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.neg_apply]; ring))
      (((integrable_eval_mul_cexp_gauss (hermitePolyHR n) z).const_mul (-z)).congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring))
      (integrable_eval_mul_cexp_gauss (hermitePolyHR n) z)
    have h1 : ∫ x : ℝ,
        cexp (-x * z) * (((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
        -∫ x : ℝ, cexp (-x * z)
            * -((((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2))) : ℝ) : ℂ) := by
      rw [← integral_neg]; congr 1; funext x; ring
    rw [h1, hibp, neg_neg]
    have h2 : ∫ x : ℝ,
        cexp (-x * z) * (-z) * (((hermitePolyHR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
        -z * ∫ x : ℝ,
            cexp (-x * z) * (((hermitePolyHR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [h2, ih, pow_succ]
    ring

/-- `∫ e^{-xz} e^{-x²} dx = √π e^{z²/4}`. -/
theorem integral_cexp_gauss (z : ℂ) :
    ∫ x : ℝ, cexp (-x * z) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      (Real.sqrt Real.pi : ℂ) * cexp (z ^ 2 / 4) := by
  have h := integral_cexp_quadratic (b := -1) (by simp) (-z) 0
  have heq : ∀ x : ℝ, cexp (-x * z) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      cexp (-1 * (x : ℂ) ^ 2 + -z * x + 0) := fun x => by
    rw [ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf
  simp_rw [heq, h]
  rw [neg_neg, div_one, show (0 : ℂ) - (-z) ^ 2 / (4 * -1) = z ^ 2 / 4 by ring]
  congr 1
  rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
  norm_num

/-- The Laplace transform of `Hₙ(x) e^{-x²}` over `ℝ` is `√π (-z)ⁿ e^{z²/4}`
(DLMF 18.17.35). -/
@[dlmf 18.17.E35]
theorem hermitePolyH_laplace_transform (n : ℕ) (z : ℂ) :
    ∫ x : ℝ, exp (-x * z) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (-(x : ℂ) ^ 2) =
      Real.sqrt Real.pi * (-z) ^ n * exp (z ^ 2 / 4) := by
  have heq : ∀ x : ℝ, exp (-x * z) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (-(x : ℂ) ^ 2) =
      cexp (-x * z) * (((hermitePolyHR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) := fun x => by
    have : (aeval (x : ℂ) (hermitePolyH n) : ℂ) = (((hermitePolyHR n).eval x : ℝ) : ℂ) := by
      rw [← aeval_hermitePolyH_eq_eval]
      exact aeval_algebraMap_apply ℂ x (hermitePolyH n)
    rw [this, ofReal_mul, ofReal_exp]; push_cast; ring
  simp_rw [heq]
  rw [integral_cexp_mul_hermite_gauss, integral_cexp_gauss]
  ring

/-- `(x+it)^n t^j e^{-t²}` is integrable. -/
theorem integrable_add_I_pow_mul_pow_gauss (x : ℂ) (n j : ℕ) :
    Integrable fun t : ℝ => (x + I * t) ^ n * ((t : ℂ) ^ j * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) := by
  have hq : ∀ t : ℝ, (x + I * t) ^ n * ((t : ℂ) ^ j * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) =
      ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℂ) * x ^ (n - k) * I ^ k) *
        ((t : ℂ) ^ (k + j) * (cexp (-t * 0) * cexp (-(t : ℂ) ^ 2))) := fun t => by
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ofReal_exp]; push_cast; simp; ring
  simp_rw [hq]
  exact integrable_finsetSum _ fun k _ => (integrable_pow_mul_cexp_gauss (k + j) 0).const_mul _

/-- `(x+it)^n e^{-t²}` is integrable. -/
theorem integrable_add_I_pow_gauss (x : ℂ) (n : ℕ) :
    Integrable fun t : ℝ => (x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
  simpa using integrable_add_I_pow_mul_pow_gauss x n 0

/-- One integration by parts: `∫ t (x+it)^n e^{-t²} = (i n / 2) ∫ (x+it)^{n-1} e^{-t²}`. -/
theorem integral_t_mul_add_I_pow (x : ℂ) (n : ℕ) :
    ∫ t : ℝ, (x + I * t) ^ (n + 1) * ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) =
      I * (n + 1) / 2 * ∫ t : ℝ, (x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (x + I * s) ^ (n + 1))
      ((n + 1 : ℂ) * (x + I * t) ^ n * I) t := by
    intro t
    have := (((hasDerivAt_id (t : ℂ)).const_mul I).const_add x).pow (n + 1) |>.comp_ofReal (z := t)
    simpa using this
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((-(Real.exp (-(s ^ 2))) / 2 : ℝ) : ℂ))
      (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Real.exp (-(s ^ 2))) / 2) (t * Real.exp (-(t ^ 2))) t := by
      have := (((hasDerivAt_pow 2 t).neg).exp.neg).div_const 2
      convert this using 1; simp; ring
    exact h1.ofReal_comp
  have hI := integrable_add_I_pow_gauss x n
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    ?_ ?_ ?_
  · rw [hibp]
    rw [show (fun t : ℝ => (n + 1 : ℂ) * (x + I * t) ^ n * I * ((-(Real.exp (-(t ^ 2))) / 2 : ℝ) : ℂ))
      = fun t => -(I * (n + 1) / 2) * ((x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) by
        funext t; push_cast; ring, integral_const_mul]
    ring
  · refine (integrable_add_I_pow_mul_pow_gauss x (n + 1) 1).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; push_cast; ring
  · refine ((integrable_add_I_pow_gauss x n).const_mul (-(I * (n + 1) / 2))).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; push_cast; ring
  · refine ((integrable_add_I_pow_gauss x (n + 1)).const_mul (-(1 / 2))).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `aeval x (hermitePolyH n) = (2 :
ℂ) ^ n / Real.sqrt Real.pi * ∫ t : ℝ, (x + I * t) ^ n * Real.exp (-(t ^ 2))`. -/
@[dlmf 18.10.E7]
theorem hermitePolyH_laplace_integral (n : ℕ) (x : ℂ) :
    aeval x (hermitePolyH n) = (2 : ℂ) ^ n / Real.sqrt Real.pi *
      ∫ t : ℝ, (x + I * t) ^ n * Real.exp (-(t ^ 2)) := by
  set F : ℕ → ℂ := fun n => ∫ t : ℝ, (x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) with hF
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hF0 : F 0 = Real.sqrt Real.pi := by
    simp only [hF, pow_zero, one_mul]
    rw [integral_complex_ofReal, show (fun t : ℝ => Real.exp (-(t ^ 2))) =
      fun t => Real.exp (-1 * t ^ 2) by funext t; ring_nf, integral_gaussian, div_one]
  have hodd : ∫ t : ℝ, ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) = 0 := by
    have h := integral_neg_eq_self (fun t : ℝ => ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ)) volume
    simp only [neg_mul, neg_sq, ofReal_neg, integral_neg] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hF1 : F 1 = x * Real.sqrt Real.pi := by
    have : F 1 = x * F 0 + I * ∫ t : ℝ, ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
      simp only [hF, pow_one, pow_zero, one_mul]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
      · congr 1; funext t; push_cast; try ring
      · exact (integrable_add_I_pow_gauss x 0).const_mul x |>.congr
          (Eventually.of_forall fun t => by simp)
      · exact ((integrable_add_I_pow_mul_pow_gauss 0 0 1).const_mul I).congr
          (Eventually.of_forall fun t => by simp)
    rw [this, hodd, hF0]; ring
  have hrec : ∀ n : ℕ, F (n + 2) = x * F (n + 1) - (n + 1) / 2 * F n := by
    intro n
    have hsplit : F (n + 2) = x * F (n + 1) +
        I * ∫ t : ℝ, (x + I * t) ^ (n + 1) * ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
      simp only [hF]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        ((integrable_add_I_pow_gauss x (n + 1)).const_mul x)
        (((integrable_add_I_pow_mul_pow_gauss x (n + 1) 1).const_mul I).congr
          (Eventually.of_forall fun t => by simp only; push_cast; ring))]
      congr 1; funext t; push_cast; ring
    rw [hsplit, integral_t_mul_add_I_pow]
    simp only [hF]
    rw [show I * (I * ((n : ℂ) + 1) / 2 * ∫ t : ℝ, (x + I * t) ^ n *
      ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) = I ^ 2 * (((n : ℂ) + 1) / 2) * ∫ t : ℝ, (x + I * t) ^ n *
      ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) by ring, I_sq]
    ring
  have key : ∀ n : ℕ, (2 : ℂ) ^ n * F n = Real.sqrt Real.pi * aeval x (hermitePolyH n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [hF0]
    | one => rw [hF1, hermitePolyH_one, map_mul, aeval_X, map_ofNat]; ring
    | more n ih0 ih1 =>
      rw [hrec, aeval_hermitePolyH_succ_succ]
      linear_combination 2 * x * ih1 - 2 * ((n : ℂ) + 1) * ih0
  have hn := key n
  simp only [hF] at hn
  field_simp
  linear_combination -hn

/-- `e^{-t²} tⁿ e^{2ixt}` is integrable. -/
theorem integrable_gauss_pow_cexp (x : ℝ) (n : ℕ) :
    Integrable fun t : ℝ => ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n * cexp (2 * I * x * t) := by
  refine (integrable_pow_mul_cexp_gauss n (-2 * I * x)).congr (Eventually.of_forall fun t => ?_)
  simp only [ofReal_exp]
  push_cast
  rw [show -(t : ℂ) * (-2 * I * x) = 2 * I * x * t by ring]
  ring

/-- The moment recurrence for `∫ e^{-t²} tⁿ e^{2ixt} dt`. -/
theorem integral_K_succ_succ (x : ℝ) (n : ℕ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 2) * cexp (2 * I * x * t) =
      I * x * (∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 1) * cexp (2 * I * x * t)) +
      (n + 1) / 2 * ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n * cexp (2 * I * x * t) := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ) ^ (n + 1) * cexp (2 * I * x * s))
      (((n + 1 : ℂ) * (t : ℂ) ^ n) * cexp (2 * I * x * t) +
        (t : ℂ) ^ (n + 1) * (cexp (2 * I * x * t) * (2 * I * x))) t := by
    intro t
    have h1 := (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal
    have h2 := ((hasDerivAt_id (t : ℂ)).const_mul (2 * I * x)).cexp.comp_ofReal (z := t)
    simp only [id, mul_one] at h2
    refine (h1.mul h2).congr_deriv ?_
    push_cast; ring
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((-(Real.exp (-(s ^ 2))) / 2 : ℝ) : ℂ))
      (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Real.exp (-(s ^ 2))) / 2) (t * Real.exp (-(t ^ 2))) t := by
      have := (((hasDerivAt_pow 2 t).neg).exp.neg).div_const 2
      convert this using 1; simp; ring
    exact h1.ofReal_comp
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    ((integrable_gauss_pow_cexp x (n + 2)).congr (Eventually.of_forall fun t => by
      simp only [Pi.mul_apply]; push_cast; ring))
    ((((integrable_gauss_pow_cexp x n).const_mul (-((n : ℂ) + 1) / 2)).add
      ((integrable_gauss_pow_cexp x (n + 1)).const_mul (-(I * x)))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply, Pi.add_apply]; push_cast; ring))
    (((integrable_gauss_pow_cexp x (n + 1)).const_mul (-(1 / 2))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
  have e1 : ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 2) * cexp (2 * I * x * t) =
      ∫ t : ℝ, (t : ℂ) ^ (n + 1) * cexp (2 * I * x * t) * (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) := by
    congr 1; funext t; push_cast; ring
  rw [e1, hibp]
  rw [show (fun t : ℝ => (((n + 1 : ℂ) * (t : ℂ) ^ n) * cexp (2 * I * x * t) +
      (t : ℂ) ^ (n + 1) * (cexp (2 * I * x * t) * (2 * I * x))) * ((-(Real.exp (-(t ^ 2))) / 2 : ℝ) : ℂ))
      = fun t => (-((n : ℂ) + 1) / 2) * (((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n *
          cexp (2 * I * x * t)) + (-(I * x)) * (((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 1) *
          cexp (2 * I * x * t)) by funext t; push_cast; ring]
  rw [integral_add ((integrable_gauss_pow_cexp x n).const_mul _)
    ((integrable_gauss_pow_cexp x (n + 1)).const_mul _), integral_const_mul, integral_const_mul]
  ring

/-- The Fourier transform of the Gaussian. -/
theorem integral_K_zero (x : ℝ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 0 * cexp (2 * I * x * t) =
      Real.sqrt Real.pi * cexp (-(x : ℂ) ^ 2) := by
  have h := integral_cexp_gauss (-2 * I * x)
  rw [show (-2 * I * (x : ℂ)) ^ 2 / 4 = -(x : ℂ) ^ 2 by ring_nf; rw [I_sq]; ring] at h
  rw [← h]
  congr 1; funext t
  rw [show -(t : ℂ) * (-2 * I * x) = 2 * I * x * t by ring]
  ring

/-- The first moment of the Gaussian Fourier kernel. -/
theorem integral_K_one (x : ℝ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 1 * cexp (2 * I * x * t) =
      I * x * ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 0 * cexp (2 * I * x * t) := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => cexp (2 * I * x * s))
      (cexp (2 * I * x * t) * (2 * I * x)) t := by
    intro t
    have h2 := ((hasDerivAt_id (t : ℂ)).const_mul (2 * I * x)).cexp.comp_ofReal (z := t)
    simpa using h2
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((-(Real.exp (-(s ^ 2))) / 2 : ℝ) : ℂ))
      (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Real.exp (-(s ^ 2))) / 2) (t * Real.exp (-(t ^ 2))) t := by
      have := (((hasDerivAt_pow 2 t).neg).exp.neg).div_const 2
      convert this using 1; simp; ring
    exact h1.ofReal_comp
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    ((integrable_gauss_pow_cexp x 1).congr (Eventually.of_forall fun t => by
      simp only [Pi.mul_apply]; push_cast; ring))
    (((integrable_gauss_pow_cexp x 0).const_mul (-(I * x))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
    (((integrable_gauss_pow_cexp x 0).const_mul (-(1 / 2))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
  have e1 : ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 1 * cexp (2 * I * x * t) =
      ∫ t : ℝ, cexp (2 * I * x * t) * (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) := by
    congr 1; funext t; push_cast; ring
  rw [e1, hibp, show (fun t : ℝ => cexp (2 * I * x * t) * (2 * I * x) *
      ((-(Real.exp (-(t ^ 2))) / 2 : ℝ) : ℂ)) = fun t => (-(I * x)) *
      (((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 0 * cexp (2 * I * x * t)) by
      funext t; push_cast; ring, integral_const_mul]
  ring

/-- Identity under the stated parameter and domain assumptions: `(aeval (x : ℂ) (hermitePolyH n) :
ℂ) = (-2 * I) ^ n * exp ((x : ℂ) ^ 2) / Real.sqrt Real.pi * ∫ t : ℝ, Real.exp (-(t ^ 2)) * (t
: ℂ) ^ n * exp (2 * I * x * t)`. -/
@[dlmf 18.10.E10]
theorem hermitePolyH_fourier_integral (n : ℕ) (x : ℝ) :
    (aeval (x : ℂ) (hermitePolyH n) : ℂ) = (-2 * I) ^ n * exp ((x : ℂ) ^ 2) / Real.sqrt Real.pi *
      ∫ t : ℝ, Real.exp (-(t ^ 2)) * (t : ℂ) ^ n * exp (2 * I * x * t) := by
  set K : ℕ → ℂ := fun n => ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n *
    cexp (2 * I * x * t) with hK
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hE : cexp ((x : ℂ) ^ 2) * cexp (-(x : ℂ) ^ 2) = 1 := by rw [← Complex.exp_add]; simp
  have key : ∀ n : ℕ, (-2 * I) ^ n * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi * K n =
      aeval (x : ℂ) (hermitePolyH n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      simp only [hK]
      rw [integral_K_zero]
      field_simp
      simp [hE]
    | one =>
      simp only [hK]
      rw [integral_K_one, integral_K_zero, hermitePolyH_one, map_mul, aeval_X, map_ofNat]
      generalize (Real.sqrt Real.pi : ℂ) = sp at hπ ⊢
      field_simp
      linear_combination (-(x : ℂ) * I ^ 2) * hE + (-(x : ℂ)) * I_sq
    | more n ih0 ih1 =>
      simp only [hK] at ih0 ih1 ⊢
      rw [integral_K_succ_succ, aeval_hermitePolyH_succ_succ, ← ih0, ← ih1]
      generalize (∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 1) *
        cexp (2 * I * x * t)) = A
      generalize (∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n *
        cexp (2 * I * x * t)) = B
      set P := (-2 * I) ^ n * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi
      rw [show (-2 * I) ^ (n + 2) * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi = P * (-2 * I) ^ 2 by
        simp only [P]; ring,
        show (-2 * I) ^ (n + 1) * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi = P * (-2 * I) by
        simp only [P]; ring]
      linear_combination (4 * P * I * x * A + 2 * P * ((n : ℂ) + 1) * B) * I_sq
  rw [← key n]

/-- An interval antiderivative of the physicists’ Hermite polynomial. -/
@[dlmf 18.17.E3]
theorem hermitePolyH_integral (n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, (aeval y (hermitePolyH n) : ℝ) =
      (aeval x (hermitePolyH (n + 1)) - aeval (0 : ℝ) (hermitePolyH (n + 1))) / (2 * (n + 1)) := by
  have hd (t : ℝ) : HasDerivAt (fun y : ℝ => aeval y (hermitePolyH (n + 1)))
      (2 * (n + 1) * aeval t (hermitePolyH n)) t := by
    have h := (hermitePolyH (n + 1)).hasDerivAt_aeval t
    rw [hermitePolyH_derivative] at h
    simpa only [map_mul, aeval_C, map_ofNat, map_add, map_natCast, map_one] using h
  have hi : IntervalIntegrable (fun t : ℝ => 2 * (n + 1) * aeval t (hermitePolyH n))
      volume 0 x := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at h
  apply (eq_div_iff (by positivity : (2 * (n + 1) : ℝ) ≠ 0)).mpr
  nlinarith [h]

/-- An interval antiderivative of a Gaussian-weighted physicists’ Hermite polynomial. -/
@[dlmf 18.17.E4]
theorem hermitePolyH_weighted_integral (n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, Real.exp (-(y ^ 2)) * (aeval y (hermitePolyH (n + 1)) : ℝ) =
      aeval (0 : ℝ) (hermitePolyH n) - Real.exp (-(x ^ 2)) * aeval x (hermitePolyH n) := by
  let g : ℝ → ℝ := fun t => Real.exp (-(t ^ 2)) * aeval t (hermitePolyH n)
  have hd (t : ℝ) : HasDerivAt (fun y => -g y)
      (Real.exp (-(t ^ 2)) * aeval t (hermitePolyH (n + 1))) t := by
    have hg : DifferentiableAt ℝ g t :=
      (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => Real.exp (-(t ^ 2))) t).mul
        ((hermitePolyH n).hasDerivAt_aeval t).differentiableAt
    have ht := hg.hasDerivAt.neg
    change HasDerivAt (fun y => -g y) (-deriv g t) t at ht
    simpa only [g, DLMF.OrthogonalPolynomials.hermitePolyH_weighted_derivative, neg_mul, neg_neg]
      using ht
  have hi : IntervalIntegrable
      (fun y : ℝ => Real.exp (-(y ^ 2)) * (aeval y (hermitePolyH (n + 1)) : ℝ)) volume 0 x :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa only [g, zero_pow (by decide : 2 ≠ 0), neg_zero, Real.exp_zero, one_mul,
    neg_sub_neg] using h

/-- Positive integer cosine frequencies integrate to zero on the half-circle. -/
theorem integral_cos_nat_pi {k : ℕ} (hk : 0 < k) :
    (∫ phi : ℝ in (0 : ℝ)..π, (Real.cos (k*phi) : ℂ)) = 0 := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hh := integral_cos_mul_complex hk0 0 π
  have he : (fun phi : ℝ => Complex.cos ((k : ℂ)*phi)) = fun phi : ℝ => (Real.cos (k*phi) : ℂ) := by
    funext phi
    push_cast
    rfl
  rw [he] at hh
  simpa only [mul_zero, sin_zero, zero_div, sub_zero, ← ofReal_natCast, ← ofReal_mul,
    ← ofReal_sin, Real.sin_nat_mul_pi, ofReal_zero, zero_div] using hh

/-- Identity under the stated parameter and domain assumptions: `legendrePolyP n (Real.cos θ) *
legendrePolyP n (Real.cos ψ) = (Real.pi : ℂ)⁻¹ * ∫ phi : ℝ in (0 : ℝ)..Real.pi, legendrePolyP
n (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi)`. -/
@[dlmf 18.17.E6]
theorem legendre_product_integral (n : ℕ) (θ ψ : ℝ) :
    legendrePolyP n (Real.cos θ) * legendrePolyP n (Real.cos ψ) = (Real.pi : ℂ)⁻¹ *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, legendrePolyP n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) := by
  let c (k : ℕ) : ℂ := ((n-k)! : ℂ) * (n+k)! / (2^(2*k)*(n ! : ℂ)^2) *
    (Real.sin θ : ℂ)^k * jacobiPolyP k k (n-k) (Real.cos θ) *
    (Real.sin ψ : ℂ)^k * jacobiPolyP k k (n-k) (Real.cos ψ)
  have he : (fun phi : ℝ => legendrePolyP n
      (Real.cos θ*Real.cos ψ + Real.sin θ*Real.sin ψ*Real.cos phi)) =
      fun phi => legendrePolyP n (Real.cos θ)*legendrePolyP n (Real.cos ψ) +
        2*∑ k ∈ Finset.Icc 1 n, c k*(Real.cos (k*phi) : ℂ) := by
    funext phi
    exact legendre_addition n θ ψ phi
  have hsum : (∫ phi : ℝ in (0 : ℝ)..π, 2*∑ k ∈ Finset.Icc 1 n, c k*(Real.cos (k*phi) : ℂ)) =
      2*∑ k ∈ Finset.Icc 1 n, ∫ phi : ℝ in (0 : ℝ)..π, c k*(Real.cos (k*phi) : ℂ) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun k _ =>
        (show Continuous (fun phi : ℝ => c k*(Real.cos (k*phi) : ℂ)) by fun_prop).intervalIntegrable _ _)]
  rw [he, intervalIntegral.integral_add intervalIntegrable_const
    ((show Continuous (fun phi : ℝ => ∑ k ∈ Finset.Icc 1 n, c k*(Real.cos (k*phi) : ℂ)) by fun_prop).intervalIntegrable _ _ |>.const_mul _), hsum]
  have hz : ∑ k ∈ Finset.Icc 1 n, ∫ phi : ℝ in (0 : ℝ)..π, c k*(Real.cos (k*phi) : ℂ) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_cos_nat_pi (by simp at hk; omega), mul_zero]
  rw [hz, mul_zero, add_zero, intervalIntegral.integral_const]
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  rw [real_smul]
  push_cast
  field_simp
  ring

end DLMF.OrthogonalPolynomials
end
end
