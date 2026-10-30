/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Coulomb
public import DLMF.Confluent.CoulombAsymptotics

/-!
# The irregular Coulomb function and the Wronskian (DLMF 33.2.11–33.2.12, 33.10.1–33.10.2)

For `ρ > 0`, the logarithmic part of the phase `θ_ℓ` cancels against the power in DLMF 33.2.8.
This gives `H^+_ℓ = A^+ ρ^{ℓ+1} e^{iρ} U(ℓ+1+iη, 2ℓ+2, -2iρ)` with a constant `A^+`
(`coulombHPlus_eq`). Tricomi's function commutes with conjugation on the slit plane, so
`H^-_ℓ = conj H^+_ℓ`. The connection formula 13.2.41 at `z = 2iρ` then gives
`F_ℓ = (H^+_ℓ - H^-_ℓ)/(2i)`. The irregular function is defined by DLMF 33.2.11 as
`G_ℓ = Re H^+_ℓ`, so that `H^±_ℓ = G_ℓ ± i F_ℓ`.

The Wronskian `W{H^+_ℓ, F_ℓ}` reduces to `W{𝐌, U}` at `-2iρ`
(`wronskian_regularizedHGFun_kummerU_all`), whose constant evaluates to `1`.

## Main results

* `conj_kummerU`: `conj U(a,b,z) = U(conj a, conj b, conj z)` on the slit plane.
* `coulombHMinus_eq_conj`, `coulombF_eq_sub_div`, `coulombF_eq_im`.
* `coulombG`, `coulombH_eq_G_add_I_mul_F`: DLMF 33.2.11.
* `coulomb_wronskian`, `coulomb_wronskian_HPlus`, `coulomb_wronskian_HMinus`: DLMF 33.2.12.
* `tendsto_coulombHPlus_sub_exp`, `tendsto_coulombF_sub_sin_and_coulombG_sub_cos`:
  DLMF 33.10.2 and 33.10.1.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Topology Nat ComplexConjugate
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Tricomi's function commutes with complex conjugation on the slit plane. -/
theorem conj_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    conj (kummerU a b z) = kummerU (conj a) (conj b) (conj z) := by
  have hz0 := slitPlane_ne_zero hz
  have hcz : conj z ≠ 0 := (map_ne_zero _).mpr hz0
  have harg : z.arg ≠ π := slitPlane_arg_ne_pi hz
  have key : ∀ c ∈ integerComplement,
      conj (kummerU a c z) = kummerU (conj a) (conj c) (conj z) := by
    intro c hc
    have hcz' := forall_of_mem_integerComplement hc
    have hcc : ∀ k : ℤ, conj c ≠ k := fun k h => hcz' k (by
      simpa using congrArg conj h)
    rw [kummerU_eq_connection _ _ _ hcz', kummerU_eq_connection _ _ _ hcc,
      kummerUConnection, kummerUConnection]
    simp only [map_add, map_mul, map_div₀, map_sub, map_one, map_ofNat, ← Gamma_conj,
      conj_kummerM, conj_cpow _ _ harg, Complex.conj_conj]
  refine eq_of_continuousAt_of_integerComplement (f := fun c => conj (kummerU a c z))
    (g := fun c => kummerU (conj a) (conj c) (conj z)) ?_ ?_ key
  · exact continuous_conj.continuousAt.comp
      (continuousAt_kummerU_comp continuousAt_const continuousAt_id hz0)
  · exact continuousAt_kummerU_comp continuousAt_const continuous_conj.continuousAt hcz

/-- `exp(-iπ/2) = -i`. -/
theorem exp_neg_I_mul_pi_div_two : exp (-(I * π / 2)) = -I := by
  rw [show -(I * π / 2) = ((-(π / 2) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- For `ρ > 0`, `log(-2iρ) = log(2ρ) - iπ/2`. -/
theorem log_neg_two_I_mul {ρ : ℝ} (hρ : 0 < ρ) :
    log (-2 * I * ρ) = Real.log (2 * ρ) - π / 2 * I := by
  have he : (-2 * I * ρ : ℂ) = ((2 * ρ : ℝ) : ℂ) * (-I) := by push_cast; ring
  apply Complex.ext
  · rw [log_re, he, norm_mul, norm_neg, norm_I, mul_one, norm_real,
      Real.norm_of_nonneg (by positivity)]
    simp
  · rw [log_im, he, arg_real_mul _ (by positivity), arg_neg_I]
    simp

/-- For `ρ > 0`, `-2iρ` lies in the slit plane. -/
theorem neg_two_I_mul_mem_slitPlane {ρ : ℝ} (hρ : 0 < ρ) : (-2 * I * ρ : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff]; right; simp [hρ.ne']

/-- For `ρ > 0`, `2iρ` lies in the slit plane. -/
theorem two_I_mul_mem_slitPlane {ρ : ℝ} (hρ : 0 < ρ) : (2 * I * ρ : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff]; right; simp [hρ.ne']

/-- `H^+_ℓ` without the logarithmic phase: `H^+_ℓ = A^+ ρ^{ℓ+1} e^{iρ} U(ℓ+1+iη, 2ℓ+2, -2iρ)`. -/
theorem coulombHPlus_eq (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHPlus ℓ η ρ = coulombAPlus ℓ η * (ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ) *
      kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ) := by
  have hz : (-2 * I * ρ : ℂ) ≠ 0 := slitPlane_ne_zero (neg_two_I_mul_mem_slitPlane hρ)
  rw [coulombHPlus, coulombAPlus, coulombTheta,
    show (ℓ : ℂ) + 1 + I * η = ((ℓ + 1 : ℕ) : ℂ) + I * η by push_cast; ring, cpow_add _ _ hz,
    cpow_natCast, cpow_def_of_ne_zero hz, log_neg_two_I_mul hρ]
  have hx : exp (I * ((ρ - η * Real.log (2 * ρ) - ℓ * π / 2 + coulombSigma ℓ η : ℝ) : ℂ)) *
      exp ((Real.log (2 * ρ) - π / 2 * I) * (I * η)) =
      exp (I * ρ) * exp (coulombSigma ℓ η * I) * exp ((π * η / 2 : ℝ) : ℂ) *
        exp (-(I * π / 2)) ^ ℓ := by
    rw [← exp_nat_mul, ← exp_add, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    push_cast
    linear_combination (-(π * η / 2) : ℂ) * I_sq
  rw [exp_neg_I_mul_pi_div_two] at hx
  have hpow : (-2 : ℂ) ^ (ℓ + 1) * I ^ (ℓ + 1) * (-I) ^ ℓ = 2 ^ (ℓ + 1) * (-1) ^ ℓ * (-I) := by
    have h : (-2 : ℂ) ^ ℓ * I ^ ℓ * (-I) ^ ℓ = 2 ^ ℓ * (-1) ^ ℓ := by
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      congr 1
      linear_combination 2 * I_sq
    rw [pow_succ, pow_succ, pow_succ]
    linear_combination (-2 * I) * h
  rw [ofReal_exp, show ∀ A B C D : ℂ, A * (B * C) * D = B * (A * C) * D from
    fun _ _ _ _ => by ring, hx, mul_pow, mul_pow]
  linear_combination ((ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ) * exp (coulombSigma ℓ η * I) *
    exp ((π * η / 2 : ℝ) : ℂ) *
    kummerU (((ℓ + 1 : ℕ) : ℂ) + I * η) (2 * ℓ + 2) (-2 * I * ρ)) * hpow

/-- **`H^-_ℓ` is the complex conjugate of `H^+_ℓ`** (DLMF §33.2(iii)). -/
theorem coulombHMinus_eq_conj (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHMinus ℓ η ρ = conj (coulombHPlus ℓ η ρ) := by
  have hs := neg_two_I_mul_mem_slitPlane hρ
  have hcp : ∀ w : ℂ, conj ((-2 * I * ρ : ℂ) ^ w) = (conj (-2 * I * ρ : ℂ)) ^ (conj w) := by
    intro w; rw [conj_cpow _ _ (slitPlane_arg_ne_pi hs), conj_conj]
  rw [coulombHPlus, coulombHMinus, map_mul, map_mul, conj_kummerU _ _ hs, ← exp_conj, hcp]
  simp only [map_mul, map_add, map_neg, map_ofNat, conj_ofReal, conj_I, map_natCast, map_one]
  ring_nf

/-- For `ρ > 0`, `arg(2iρ) = π/2`. -/
theorem arg_two_I_mul {ρ : ℝ} (hρ : 0 < ρ) : arg (2 * I * ρ) = π / 2 := by
  rw [show (2 * I * ρ : ℂ) = ((2 * ρ : ℝ) : ℂ) * I by push_cast; ring,
    arg_real_mul _ (by positivity), arg_I]

/-- `H^-_ℓ = conj(A^+) ρ^{ℓ+1} e^{-iρ} U(ℓ+1-iη, 2ℓ+2, 2iρ)`. -/
theorem coulombHMinus_eq (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHMinus ℓ η ρ = conj (coulombAPlus ℓ η) * (ρ : ℂ) ^ (ℓ + 1) * exp (-I * ρ) *
      kummerU ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ) := by
  rw [coulombHMinus_eq_conj ℓ η hρ, coulombHPlus_eq ℓ η hρ, map_mul, map_mul, map_mul,
    conj_kummerU _ _ (neg_two_I_mul_mem_slitPlane hρ), ← exp_conj]
  simp only [map_mul, map_add, map_neg, map_ofNat, conj_ofReal, conj_I, map_natCast, map_one,
    map_pow]
  ring_nf

/-- **The regular function from the irregular ones**: `F_ℓ = (H^+_ℓ - H^-_ℓ)/(2i)`, from the
connection formula 13.2.41 at `z = 2iρ`. -/
theorem coulombF_eq_sub_div (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (coulombF ℓ η ρ : ℂ) = (coulombHPlus ℓ η ρ - coulombHMinus ℓ η ρ) / (2 * I) := by
  set a : ℂ := (ℓ : ℂ) + 1 - I * η with ha
  have hconn := kummerM_eq_kummerU_connection a (2 * ℓ + 2) (two_I_mul_mem_slitPlane hρ)
    false (by simp [arg_two_I_mul hρ, Real.pi_pos]) (two_mul_nat_add_two_ne_neg_nat ℓ)
  simp only [Bool.false_eq_true, ↓reduceIte] at hconn
  rw [show 2 * (ℓ : ℂ) + 2 - a = ℓ + 1 + I * η by rw [ha]; ring,
    show exp ((-1 : ℂ) * π * I) * (2 * I * ρ) = -2 * I * ρ by
      rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; ring] at hconn
  have he1 : exp (-(-1) * a * π * I) = (-1) ^ (ℓ + 1) * exp ((π * η : ℝ) : ℂ) := by
    rw [show -(-1) * a * π * I = ((ℓ + 1 : ℕ) : ℂ) * (π * I) + ((π * η : ℝ) : ℂ) by
      rw [ha]; push_cast; linear_combination (-(π * η) : ℂ) * I_sq, exp_add, exp_nat_mul,
      exp_pi_mul_I]
  have he2 : exp ((-1) * ((ℓ : ℂ) + 1 + I * η) * π * I) =
      (-1) ^ (ℓ + 1) * exp ((π * η : ℝ) : ℂ) := by
    rw [show (-1) * ((ℓ : ℂ) + 1 + I * η) * π * I =
        ((ℓ + 1 : ℕ) : ℂ) * (-(π * I)) + ((π * η : ℝ) : ℂ) by
      push_cast; linear_combination (-(π * η) : ℂ) * I_sq, exp_add, exp_nat_mul, exp_neg,
      exp_pi_mul_I]
    norm_num
  rw [he1, he2] at hconn
  set g := Gamma ((ℓ : ℂ) + 1 + I * η) with hg
  have hgc : Gamma a = conj g := by
    rw [hg, ← Gamma_conj]; congr 1; simp [ha]; ring
  have hfact : Gamma (2 * (ℓ : ℂ) + 2) = ((2 * ℓ + 1)! : ℂ) := by
    rw [show 2 * (ℓ : ℂ) + 2 = ((2 * ℓ + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial]
  rw [hgc, hfact] at hconn
  have hgN : g = (‖g‖ : ℂ) * exp (arg g * I) := (norm_mul_exp_arg_mul_I g).symm
  have hgne : g ≠ 0 := Gamma_ne_zero fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ),
      (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hN : (‖g‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hgne
  have hgcN : conj g = (‖g‖ : ℂ) * (exp (arg g * I))⁻¹ := by
    conv_lhs => rw [hgN]
    rw [map_mul, conj_ofReal, ← exp_conj, map_mul, conj_ofReal, conj_I, ← exp_neg]; ring_nf
  rw [ofReal_coulombF, coulombHPlus_eq ℓ η hρ, coulombHMinus_eq ℓ η hρ, coulombWave, coulombC,
    coulombAPlus, show coulombSigma ℓ η = arg g from rfl, ← hg]
  have hF : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [div_eq_iff hF] at hconn
  rw [hconn]
  have h1 : Real.exp (-π * η / 2) = (Real.exp (π * η / 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  have h2 : exp ((π * η : ℝ) : ℂ) = (Real.exp (π * η / 2) : ℂ) ^ 2 := by
    rw [← ofReal_exp, ← ofReal_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hu1 : exp (-I * ρ) = (exp (I * ρ))⁻¹ := by rw [← exp_neg]; ring_nf
  have hu2 : exp (2 * I * ρ) = exp (I * ρ) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have hE : exp ((arg g : ℂ) * -I) = (exp (arg g * I))⁻¹ := by rw [← exp_neg]; ring_nf
  have hr : Real.exp (π * η / 2) ≠ 0 := (Real.exp_pos _).ne'
  rw [h1, h2, hu1, hu2]
  simp only [map_mul, map_neg, map_pow, map_ofNat, map_one, conj_ofReal, conj_I, ← exp_conj, hE]
  rw [hgcN]
  have hEne := exp_ne_zero (arg g * I)
  have hune := exp_ne_zero (I * ρ)
  have hr' : (Real.exp (π * η / 2) : ℂ) ≠ 0 := by exact_mod_cast hr
  push_cast
  generalize exp (arg g * I) = E at *
  generalize exp (I * ρ) = u at *
  generalize (Real.exp (π * η / 2) : ℂ) = r at *
  generalize (‖g‖ : ℂ) = N at *
  rw [hgN, ha]
  field_simp
  ring

/-- `F_ℓ = Im H^+_ℓ` for `ρ > 0`. -/
theorem coulombF_eq_im (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombF ℓ η ρ = (coulombHPlus ℓ η ρ).im := by
  have h := coulombF_eq_sub_div ℓ η hρ
  rw [coulombHMinus_eq_conj ℓ η hρ, sub_conj] at h
  have : ((coulombF ℓ η ρ : ℝ) : ℂ) = ((coulombHPlus ℓ η ρ).im : ℂ) := by
    rw [h]; field_simp; push_cast; ring
  exact_mod_cast this

/-- **DLMF 33.2.11**: `H^±_ℓ = G_ℓ ± i F_ℓ` for `ρ > 0`. -/
@[dlmf 33.2.E11]
theorem coulombH_eq_G_add_I_mul_F (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHPlus ℓ η ρ = coulombG ℓ η ρ + I * coulombF ℓ η ρ ∧
      coulombHMinus ℓ η ρ = coulombG ℓ η ρ - I * coulombF ℓ η ρ := by
  rw [coulombHMinus_eq_conj ℓ η hρ, coulombF_eq_im ℓ η hρ, coulombG]
  constructor
  · conv_lhs => rw [← re_add_im (coulombHPlus ℓ η ρ)]
    ring
  · apply Complex.ext <;> simp

/-- `F_ℓ = C_ℓ (2ℓ+1)! ρ^{ℓ+1} e^{iρ} 𝐌(ℓ+1+iη, 2ℓ+2, -2iρ)`, for every real `ρ`. -/
theorem ofReal_coulombF_eq_regularized (ℓ : ℕ) (η ρ : ℝ) :
    (coulombF ℓ η ρ : ℂ) = (coulombC ℓ η : ℂ) * ((2 * ℓ + 1)! : ℂ) *
      ((ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ)) *
        regularizedHGFun {(ℓ : ℂ) + 1 + I * η} {2 * (ℓ : ℂ) + 2} (-2 * I * ρ) := by
  rw [ofReal_coulombF, coulombWave_eq_conj_form,
    kummerM_eq_mul_regularizedHGFun (two_mul_nat_add_two_ne_neg_nat ℓ),
    show 2 * (ℓ : ℂ) + 2 = ((2 * ℓ + 1 : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial,
    show -(2 * I * (ρ : ℂ)) = -2 * I * ρ by ring]
  push_cast
  ring

/-- The real part of a differentiable complex function of a real variable has derivative `Re f'`. -/
theorem hasDerivAt_re_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x := by
  have := reCLM.hasFDerivAt.comp_hasDerivAt x h
  convert this using 1
  · funext y; simp
  · simp

/-- The imaginary part of a differentiable complex function of a real variable has derivative `Im
f'`. -/
theorem hasDerivAt_im_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).im) f'.im x := by
  have := imCLM.hasFDerivAt.comp_hasDerivAt x h
  convert this using 1
  · funext y; simp
  · simp

/-- The constant in the Coulomb Wronskian. -/
theorem coulomb_wronskian_const (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    2 * I * coulombAPlus ℓ η * ((coulombC ℓ η : ℂ) * ((2 * ℓ + 1)! : ℂ)) *
      ((ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ)) ^ 2 *
      (-((-2 * I * ρ) ^ (-(2 * (ℓ : ℂ) + 2)) * exp (-2 * I * ρ)) /
        Gamma ((ℓ : ℂ) + 1 + I * η)) = 1 := by
  set g := Gamma ((ℓ : ℂ) + 1 + I * η) with hg
  have hgN : g = (‖g‖ : ℂ) * exp (arg g * I) := (norm_mul_exp_arg_mul_I g).symm
  have hgne : g ≠ 0 := Gamma_ne_zero fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ),
      (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hN : (‖g‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hgne
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hw : (-2 * I * (ρ : ℂ)) ^ (-(2 * (ℓ : ℂ) + 2)) =
      ((-1) ^ (ℓ + 1) * 2 ^ (ℓ + 1) * 2 ^ (ℓ + 1) * ((ρ : ℂ) ^ (ℓ + 1)) ^ 2)⁻¹ := by
    rw [show -(2 * (ℓ : ℂ) + 2) = -((2 * (ℓ + 1) : ℕ) : ℂ) by push_cast; ring, cpow_neg,
      cpow_natCast]
    congr 1
    rw [pow_mul, show (-2 * I * (ρ : ℂ)) ^ 2 = (-1) * 2 * 2 * ρ ^ 2 by
      linear_combination 4 * (ρ : ℂ) ^ 2 * I_sq, mul_pow, mul_pow, mul_pow, ← pow_mul,
      ← pow_mul, mul_comm 2 (ℓ + 1)]
  have he : exp (-2 * I * ρ) = (exp (I * ρ) ^ 2)⁻¹ := by
    rw [← exp_nat_mul, ← exp_neg]; push_cast; ring_nf
  have hC : (coulombC ℓ η : ℂ) * ((2 * ℓ + 1)! : ℂ) =
      2 ^ ℓ * ((Real.exp (π * η / 2) : ℝ) : ℂ)⁻¹ * ‖g‖ := by
    rw [coulombC, ← hg]
    have hF : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [show Real.exp (-π * η / 2) = (Real.exp (π * η / 2))⁻¹ by rw [← Real.exp_neg]; ring_nf]
    push_cast
    field_simp
  have hr : ((Real.exp (π * η / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have hsq : ((-1 : ℂ) ^ ℓ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [hw, he, hC, coulombAPlus, show coulombSigma ℓ η = arg g from rfl]
  have hEne := exp_ne_zero (arg g * I)
  have hune := exp_ne_zero (I * ρ)
  nth_rewrite 3 [hgN]
  generalize exp (arg g * I) = E at *
  generalize exp (I * ρ) = u at *
  generalize ((Real.exp (π * η / 2) : ℝ) : ℂ) = r at *
  generalize (‖g‖ : ℂ) = N at *
  field_simp
  linear_combination ((-1 : ℂ) ^ ℓ * 2 ^ ℓ * 2) * I_sq

/-- The complex Wronskian `H^+_ℓ F_ℓ' - (H^+_ℓ)' F_ℓ = 1`, with explicit derivatives. -/
lemma coulomb_wronskian_aux (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ h' f' : ℂ, HasDerivAt (fun x : ℝ => coulombHPlus ℓ η x) h' ρ ∧
      HasDerivAt (fun x : ℝ => (coulombF ℓ η x : ℂ)) f' ρ ∧
      coulombHPlus ℓ η ρ * f' - h' * coulombF ℓ η ρ = 1 := by
  set α : ℂ := (ℓ : ℂ) + 1 + I * η with hα
  set b : ℂ := 2 * (ℓ : ℂ) + 2 with hb
  set A := coulombAPlus ℓ η with hA
  set K : ℂ := (coulombC ℓ η : ℂ) * ((2 * ℓ + 1)! : ℂ) with hK
  have hs := neg_two_I_mul_mem_slitPlane hρ
  have hU := hasDerivAt_kummerU α b hs
  have hM := (differentiableAt_regularizedConfluent α b (-2 * I * ρ)).hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => -2 * I * w) (-2 * I) (ρ : ℂ) := by
    simpa using (hasDerivAt_id (ρ : ℂ)).const_mul (-2 * I)
  have hp : HasDerivAt (fun w : ℂ => w ^ (ℓ + 1) * exp (I * w))
      (((ℓ + 1 : ℕ) : ℂ) * (ρ : ℂ) ^ ℓ * exp (I * ρ) + (ρ : ℂ) ^ (ℓ + 1) * (I * exp (I * ρ)))
      (ρ : ℂ) := by
    have he : HasDerivAt (fun w : ℂ => exp (I * w)) (I * exp (I * ρ)) (ρ : ℂ) := by
      have := ((hasDerivAt_id (ρ : ℂ)).const_mul I).cexp
      exact this.congr_deriv (by simp only [mul_one, id]; ring)
    have := (hasDerivAt_pow (ℓ + 1) (ρ : ℂ)).mul he
    convert this using 1
    push_cast; ring
  set dp := ((ℓ + 1 : ℕ) : ℂ) * (ρ : ℂ) ^ ℓ * exp (I * ρ) + (ρ : ℂ) ^ (ℓ + 1) * (I * exp (I * ρ))
  set p0 := (ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ) with hp0
  have h1 := ((hp.const_mul A).mul (hU.comp (ρ : ℂ) hlin)).comp_ofReal
  have h2 := ((hp.const_mul K).mul (hM.comp (ρ : ℂ) hlin)).comp_ofReal
  refine ⟨_, _, h1.congr_of_eventuallyEq ?_, h2.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [eventually_gt_nhds hρ] with x hx
    rw [coulombHPlus_eq ℓ η hx]
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  · exact Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Function.comp_apply]
      rw [ofReal_coulombF_eq_regularized]
  · have hW := wronskian_regularizedHGFun_kummerU_all α b hs
    rw [ODE.wronskian, hU.deriv] at hW
    rw [coulombHPlus_eq ℓ η hρ, ofReal_coulombF_eq_regularized]
    simp only [Function.comp_apply]
    rw [← hα, ← hb, ← hA, ← hK, ← hp0]
    have hval := coulomb_wronskian_const ℓ η hρ
    rw [← hα, ← hb, ← hA, ← hK, ← hp0] at hval
    linear_combination (2 * I * A * K * p0 ^ 2) * hW + hval

/-- Derivatives of `F_ℓ` and `G_ℓ` and the Wronskian in real form. -/
theorem coulomb_wronskian_real_aux (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g' f' : ℝ, HasDerivAt (coulombG ℓ η) g' ρ ∧ HasDerivAt (coulombF ℓ η) f' ρ ∧
      HasDerivAt (fun x : ℝ => coulombHPlus ℓ η x) (g' + I * f') ρ ∧
      coulombG ℓ η ρ * f' - g' * coulombF ℓ η ρ = 1 := by
  obtain ⟨h', f', hH, hF, hW⟩ := coulomb_wronskian_aux ℓ η hρ
  have hFr : HasDerivAt (coulombF ℓ η) f'.re ρ := by
    simpa using hasDerivAt_re_comp hF
  have hfim : f'.im = 0 := by
    have h := hasDerivAt_im_comp hF
    simp only [ofReal_im] at h
    exact h.unique (hasDerivAt_const ρ 0)
  have hf' : f' = (f'.re : ℂ) := Complex.ext (by simp) (by simp [hfim])
  have hG : HasDerivAt (coulombG ℓ η) h'.re ρ := hasDerivAt_re_comp hH
  refine ⟨h'.re, f'.re, hG, hFr, ?_, ?_⟩
  · have hHim : HasDerivAt (fun x : ℝ => (coulombHPlus ℓ η x).im) h'.im ρ := hasDerivAt_im_comp hH
    have hHim' : HasDerivAt (fun x : ℝ => (coulombHPlus ℓ η x).im) f'.re ρ :=
      hFr.congr_of_eventuallyEq (by
        filter_upwards [eventually_gt_nhds hρ] with x hx
        exact (coulombF_eq_im ℓ η hx).symm)
    have him : h'.im = f'.re := hHim.unique hHim'
    convert hH using 1
    apply Complex.ext <;> simp [him]
  · have := congrArg re hW
    rw [hf'] at this
    simpa [mul_re, coulombG, coulombF_eq_im ℓ η hρ] using this

/-- **The Coulomb Wronskian** (DLMF 33.2.12): `W{G_ℓ, F_ℓ} = G_ℓ F_ℓ' - G_ℓ' F_ℓ = 1`. -/
@[dlmf 33.2.E12]
theorem coulomb_wronskian (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombG ℓ η ρ * deriv (coulombF ℓ η) ρ - deriv (coulombG ℓ η) ρ * coulombF ℓ η ρ = 1 := by
  obtain ⟨g', f', hG, hF, -, hW⟩ := coulomb_wronskian_real_aux ℓ η hρ
  rw [hG.deriv, hF.deriv, hW]

/-- **DLMF 33.2.12** for `H^+_ℓ`: `W{H^+_ℓ, F_ℓ} = 1`. -/
@[dlmf 33.2.E12]
theorem coulomb_wronskian_HPlus (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHPlus ℓ η ρ * deriv (fun x : ℝ => (coulombF ℓ η x : ℂ)) ρ -
      deriv (fun x : ℝ => coulombHPlus ℓ η x) ρ * coulombF ℓ η ρ = 1 := by
  obtain ⟨g', f', hG, hF, hH, hW⟩ := coulomb_wronskian_real_aux ℓ η hρ
  rw [hH.deriv, hF.ofReal_comp.deriv, (coulombH_eq_G_add_I_mul_F ℓ η hρ).1]
  have : ((coulombG ℓ η ρ * f' - g' * coulombF ℓ η ρ : ℝ) : ℂ) = 1 := by rw [hW]; simp
  push_cast at this
  linear_combination this

/-- **DLMF 33.2.12** for `H^-_ℓ`: `W{H^-_ℓ, F_ℓ} = 1`. -/
@[dlmf 33.2.E12]
theorem coulomb_wronskian_HMinus (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHMinus ℓ η ρ * deriv (fun x : ℝ => (coulombF ℓ η x : ℂ)) ρ -
      deriv (fun x : ℝ => coulombHMinus ℓ η x) ρ * coulombF ℓ η ρ = 1 := by
  obtain ⟨g', f', hG, hF, -, hW⟩ := coulomb_wronskian_real_aux ℓ η hρ
  have hHm : HasDerivAt (fun x : ℝ => coulombHMinus ℓ η x) (g' - I * f') ρ := by
    have h := hG.ofReal_comp.sub (hF.ofReal_comp.const_mul I)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hρ] with x hx
    exact (coulombH_eq_G_add_I_mul_F ℓ η hx).2
  rw [hHm.deriv, hF.ofReal_comp.deriv, (coulombH_eq_G_add_I_mul_F ℓ η hρ).2]
  have : ((coulombG ℓ η ρ * f' - g' * coulombF ℓ η ρ : ℝ) : ℂ) = 1 := by rw [hW]; simp
  push_cast at this
  linear_combination this

/-- **DLMF 33.10.2** (upper sign): `H^+_ℓ(η,ρ) - e^{iθ_ℓ} → 0` as `ρ → ∞`. -/
@[dlmf 33.10.E2]
theorem tendsto_coulombHPlus_sub_exp (ℓ : ℕ) (η : ℝ) :
    Tendsto (fun ρ : ℝ => coulombHPlus ℓ η ρ - exp (I * coulombTheta ℓ η ρ)) atTop (𝓝 0) := by
  have h := hasAsymptoticExpansion_coulombHPlus ℓ η 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, inv_one, poch_zero,
    Nat.factorial_zero,
    Nat.cast_one, mul_one, div_one, one_smul, pow_one] at h
  have h0 : Tendsto (fun ρ : ℝ => exp (-I * coulombTheta ℓ η ρ) * coulombHPlus ℓ η ρ - 1)
      atTop (𝓝 0) :=
    h.trans_tendsto (tendsto_inv_atTop_zero.ofReal.congr' (Eventually.of_forall fun x => by simp))
  have hb : ∀ ρ : ℝ, ‖exp (I * coulombTheta ℓ η ρ)‖ = 1 := fun ρ => by
    rw [mul_comm]; exact norm_exp_ofReal_mul_I _
  refine (tendsto_zero_iff_norm_tendsto_zero.mpr ?_)
  refine (tendsto_zero_iff_norm_tendsto_zero.mp h0).congr fun ρ => ?_
  have he : exp (I * coulombTheta ℓ η ρ) * exp (-I * coulombTheta ℓ η ρ) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  rw [show coulombHPlus ℓ η ρ - exp (I * coulombTheta ℓ η ρ) =
      exp (I * coulombTheta ℓ η ρ) * (exp (-I * coulombTheta ℓ η ρ) * coulombHPlus ℓ η ρ - 1) by
    linear_combination -(coulombHPlus ℓ η ρ) * he, norm_mul, hb, one_mul]

/-- **DLMF 33.10.1**: `F_ℓ(η,ρ) = sin θ_ℓ + o(1)` and `G_ℓ(η,ρ) = cos θ_ℓ + o(1)` as `ρ → ∞`. -/
@[dlmf 33.10.E1]
theorem tendsto_coulombF_sub_sin_and_coulombG_sub_cos (ℓ : ℕ) (η : ℝ) :
    Tendsto (fun ρ => coulombF ℓ η ρ - Real.sin (coulombTheta ℓ η ρ)) atTop (𝓝 0) ∧
      Tendsto (fun ρ => coulombG ℓ η ρ - Real.cos (coulombTheta ℓ η ρ)) atTop (𝓝 0) := by
  have h := tendsto_coulombHPlus_sub_exp ℓ η
  have hre := (continuous_re.tendsto 0).comp h
  have him := (continuous_im.tendsto 0).comp h
  have hexp : ∀ ρ : ℝ, exp (I * coulombTheta ℓ η ρ) =
      Real.cos (coulombTheta ℓ η ρ) + Real.sin (coulombTheta ℓ η ρ) * I := fun ρ => by
    rw [mul_comm, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [Function.comp_def, zero_re, zero_im, sub_re, sub_im, hexp, add_re, add_im,
    ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im] at hre him
  constructor
  · refine him.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    rw [coulombF_eq_im ℓ η hρ]; ring
  · refine hre.congr' (Eventually.of_forall fun ρ => ?_)
    simp only [coulombG]; ring

end DLMF.Confluent
