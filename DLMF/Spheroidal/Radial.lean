/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersProperties
public import DLMF.Bessel.RegularizedSeries
public import DLMF.Bessel.SphericalSeriesTools
public import DLMF.Spheroidal.FerrersSeries.RatiosAndSecondKind

/-!
# Radial spheroidal wave functions (DLMF §30.11)

This file proves the properties of the radial spheroidal functions `S^{m(j)}_n(z, γ)`: the
functions `ψ^{(j)}_k`, convergence of the series 30.11.3 and the equation they satisfy, the
connection formulas, the asymptotic behavior, the Wronskian, the connection with `𝑃s`, `𝑄s` and
the integral representation.

## Main results

* `spheroidalPsi_one_eq`, `spheroidalPsi_three_four`: `ψ^{(1)}_k = j_k` off the cut and
  `ψ^{(3),(4)}_k = ψ^{(1)}_k ± iψ^{(2)}_k` (DLMF 30.11.1–30.11.2).
* `summable_spheroidalRadial_series`, `isSpheroidalSolutionOn_spheroidalRadial`: convergence of
  the series 30.11.3 and the radial functions as solutions of 30.2.1.
* `spheroidalRadial_three_four`: the connection formulas DLMF 30.11.5.
* `spheroidalRadial_isBigO_one_two`, `spheroidalRadial_isBigO_three_four`: the asymptotic
  behavior DLMF 30.11.6 (corrected for `j = 1, 2`).
* `wronskian_spheroidalRadial`: the Wronskian DLMF 30.11.7.
* `spheroidalRadial_one_eq`, `spheroidalRadial_two_eq`: the connection with `𝑃s`, `𝑄s`
  (DLMF 30.11.8–30.11.11).
* `spheroidalRadial_one_integral`: the integral representation DLMF 30.11.12.

## Implementation notes

The radial functions take complex `z`, `γ` with `γ²` real; statements assume `(γ^2).im = 0`.

For `j = 1, 2` DLMF 30.11.6 prints the error term `O(z⁻² e^{|ℑz|})`. The correct term is
`O(z⁻² e^{|ℑ(γz)|})` (the two agree for `γ = 1`; DLMF's form is too strong for `γ > 1`):
numerically, for `n = m = 0`, `γ = 2`, `z = iy`, the quantity
`|S^{0(1)}_0(iy, 2) - ψ^{(1)}_0(2iy)| y² e^{-y}` is `3.9·10³, 8.7·10⁷, 4.2·10¹⁶` at
`y = 10, 20, 40`, while `|S - ψ| y² e^{-2y} → 0.179`. The corrected form is stated for real
`γ > 0` (the sector condition `|ph z| ≤ π - δ` refers to real `γ`).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Spheroidal

/-! ### §30.11(i) Definitions -/

/-- **`ψ^{(1)}_k` by the principal-branch formula** (DLMF 30.11.1, 10.47.3): for `z` off
`(-∞, 0]`, `j_k(z) = (π/(2z))^{1/2} J_{k+1/2}(z)`. -/
@[dlmf 30.11.E1]
theorem spheroidalPsi_one_eq (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    spheroidalPsi 1 k z = ((π : ℂ) / (2 * z)) ^ (1 / 2 : ℂ) * besselJ ((k : ℂ) + 1 / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set w : ℂ := z / 2
  have hw : w ∈ slitPlane := by
    have : w = ((1 / 2 : ℝ) : ℂ) * z := by simp [w]; ring
    rw [this, mem_slitPlane_iff] at *
    rcases hz with h | h
    · left; simp; linarith
    · right; simpa using h
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hwarg : w.arg ≠ π := by
    intro h; exact (mem_slitPlane_iff_arg.mp hw).1 h
  have hr : (0 : ℝ) < π / 4 := by positivity
  have e1 : (π : ℂ) / (2 * z) = ((π / 4 : ℝ) : ℂ) * w⁻¹ := by
    simp only [w]; push_cast; field_simp; ring
  have hwi : w⁻¹ ≠ 0 := inv_ne_zero hw0
  have hp : ((π : ℂ) / (2 * z)) ^ (1 / 2 : ℂ) * w ^ ((1 / 2 : ℂ)) = (Real.sqrt π / 2 : ℝ) := by
    rw [e1, Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hr.ne') hwi),
      Complex.cpow_def_of_ne_zero hw0, ← Complex.exp_add,
      Complex.log_ofReal_mul hr hwi, Complex.log_inv w hwarg]
    rw [show ((Real.log (π / 4) : ℂ) + -Complex.log w) * (1 / 2) + Complex.log w * (1 / 2) =
      ((Real.log (π / 4) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
    congr 1
    rw [Real.sqrt_eq_rpow, show π / 4 = (π ^ (1 / 2 : ℝ) / 2) ^ (2 : ℝ) by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul (by positivity)]
      norm_num]
    rw [Real.log_rpow (by positivity), mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.exp_log (by positivity)]
  simp only [spheroidalPsi, ↓reduceIte, DLMF.sphericalJ]
  rw [DLMF.Bessel.besselJ_eq_regularized,
    Complex.cpow_add _ _ (by simpa [w] using hw0), Complex.cpow_natCast]
  rw [show (k : ℂ) + 1 / 2 + 1 = (k : ℂ) + 3 / 2 by ring]
  have : z / 2 = w := rfl
  rw [this]
  calc _ = (((π : ℂ) / (2 * z)) ^ (1 / 2 : ℂ) * w ^ ((1 / 2 : ℂ))) * w ^ k *
        regularizedHGFun ∅ {(k : ℂ) + 3 / 2} (-(z ^ 2 / 4)) := by
          rw [hp]; simp only [w]; push_cast; rw [div_pow]; field_simp; ring_nf
    _ = _ := by ring

/-- `ψ^{(3)}_k = ψ^{(1)}_k + iψ^{(2)}_k` and `ψ^{(4)}_k = ψ^{(1)}_k - iψ^{(2)}_k` off `(-∞, 0]`
(DLMF 30.11.1–30.11.2 with `H^{(1),(2)}_ν = J_ν ± iY_ν`). Proved from `spheroidalPsi_one_eq`. -/
@[dlmf 30.11.E2]
theorem spheroidalPsi_three_four (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    spheroidalPsi 3 k z = spheroidalPsi 1 k z + I * spheroidalPsi 2 k z ∧
      spheroidalPsi 4 k z = spheroidalPsi 1 k z - I * spheroidalPsi 2 k z := by
  rw [spheroidalPsi_one_eq k hz]
  simp only [spheroidalPsi, spheroidalCylinder]
  norm_num
  constructor <;> ring

/-! ### Convergence of the series 30.11.3 -/

/-- The recurrence 10.6.1 for `Y_ν` at non-integer `ν`, for every `z ≠ 0`. -/
private lemma besselY_add_sub_of_not_int {ν z : ℂ} (hν : ∀ k : ℤ, ν ≠ k) (hz : z ≠ 0) :
    (2 * ν / z) * DLMF.Bessel.besselY ν z =
      DLMF.Bessel.besselY (ν - 1) z + DLMF.Bessel.besselY (ν + 1) z := by
  have hν1 : ∀ k : ℤ, ν - 1 ≠ k := fun k h => hν (k + 1) (by push_cast; linear_combination h)
  have hν2 : ∀ k : ℤ, ν + 1 ≠ k := fun k h => hν (k - 1) (by push_cast; linear_combination h)
  have hs : sin (ν * π) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h
    exact hν k (by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp at hk; exact hk)
  rw [DLMF.Bessel.besselY_eq_of_not_int hν, DLMF.Bessel.besselY_eq_of_not_int hν1,
    DLMF.Bessel.besselY_eq_of_not_int hν2]
  simp only [DLMF.Bessel.besselD]
  have e1 : sin ((ν - 1) * π) = -sin (ν * π) := by
    rw [sub_mul, one_mul, Complex.sin_sub_pi]
  have e2 : sin ((ν + 1) * π) = -sin (ν * π) := by
    rw [add_mul, one_mul, Complex.sin_add_pi]
  have e3 : cos ((ν - 1) * π) = -cos (ν * π) := by
    rw [sub_mul, one_mul, Complex.cos_sub_pi]
  have e4 : cos ((ν + 1) * π) = -cos (ν * π) := by
    rw [add_mul, one_mul, Complex.cos_add_pi]
  rw [e1, e2, e3, e4]
  have hJ := DLMF.Bessel.besselJ_add_sub (ν := ν) hz
  have hJ' := DLMF.Bessel.besselJ_add_sub (ν := -ν) hz
  rw [show -ν - 1 = -(ν + 1) by ring, show -ν + 1 = -(ν - 1) by ring] at hJ'
  have key : (2 * ν / z) * (besselJ ν z * cos (ν * π) - besselJ (-ν) z) =
      -((besselJ (ν - 1) z * -cos (ν * π) - besselJ (-(ν - 1)) z) +
        (besselJ (ν + 1) z * -cos (ν * π) - besselJ (-(ν + 1)) z)) := by
    linear_combination cos (ν * π) * hJ + hJ'
  rw [div_neg, div_neg, ← mul_div_assoc, key]
  ring


/-- The recurrence of the spherical Bessel functions `ψ^{(j)}`, `j = 2, 3, 4` (DLMF 10.51.1). -/
private lemma spheroidalPsi_recurrence {j : ℕ} (hj : j = 2 ∨ j = 3 ∨ j = 4) (N : ℕ) {w : ℂ}
    (hw : w ≠ 0) :
    spheroidalPsi j N w + spheroidalPsi j (N + 2) w =
      (2 * N + 3) / w * spheroidalPsi j (N + 1) w := by
  set ν : ℂ := ((N + 1 : ℕ) : ℂ) + 1 / 2 with hν
  have hνZ : ∀ k : ℤ, ν ≠ k := by
    intro k h
    have h2 := congrArg (fun x : ℂ => 2 * x) h
    simp only [hν] at h2
    have : ((2 * (N + 1) + 1 : ℤ) : ℂ) = ((2 * k : ℤ) : ℂ) := by
      push_cast at h2 ⊢; linear_combination h2
    have := Int.cast_injective this
    omega
  have e1 : ((N : ℕ) : ℂ) + 1 / 2 = ν - 1 := by simp only [hν]; push_cast; ring
  have e2 : ((N + 2 : ℕ) : ℂ) + 1 / 2 = ν + 1 := by simp only [hν]; push_cast; ring
  have e3 : (2 * (N : ℂ) + 3) = 2 * ν := by simp only [hν]; push_cast; ring
  have hj1 : j ≠ 1 := by omega
  simp only [spheroidalPsi, hj1, ↓reduceIte]
  rw [e1, e2, ← hν, e3]
  have hJ := DLMF.Bessel.besselJ_add_sub (ν := ν) hw
  have hY := besselY_add_sub_of_not_int hνZ hw
  rcases hj with rfl | rfl | rfl <;> simp only [spheroidalCylinder]
  · linear_combination (-((π : ℂ) / (2 * w)) ^ (1 / 2 : ℂ)) * hY
  · linear_combination (-((π : ℂ) / (2 * w)) ^ (1 / 2 : ℂ)) * (hJ + I * hY)
  · linear_combination (-((π : ℂ) / (2 * w)) ^ (1 / 2 : ℂ)) * (hJ - I * hY)

/-- A majorant for solutions of `f_N + f_{N+2} = ((2N+3)/w) f_{N+1}`. -/
private lemma norm_le_of_recurrence {f : ℕ → ℂ} {w : ℂ} (hw : w ≠ 0)
    (hf : ∀ N : ℕ, f N + f (N + 2) = (2 * N + 3) / w * f (N + 1)) (N : ℕ) :
    ‖f N‖ ≤ max ‖f 0‖ ‖f 1‖ * ∏ i ∈ Finset.range N, ((2 * i + 1) / ‖w‖ + 1) := by
  set r := ‖w‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hw
  set C := max ‖f 0‖ ‖f 1‖
  have hC : 0 ≤ C := le_max_of_le_left (norm_nonneg _)
  set u : ℕ → ℝ := fun N => C * ∏ i ∈ Finset.range N, ((2 * i + 1) / r + 1) with hu
  have hfac : ∀ i : ℕ, 1 ≤ (2 * (i : ℝ) + 1) / r + 1 := fun i => by
    have : 0 ≤ (2 * (i : ℝ) + 1) / r := by positivity
    linarith
  have husucc : ∀ N, u (N + 1) = u N * ((2 * N + 1) / r + 1) := fun N => by
    simp only [hu, Finset.prod_range_succ]; ring
  have hu0 : ∀ N, 0 ≤ u N := fun N => by
    simp only [hu]
    exact mul_nonneg hC (Finset.prod_nonneg fun i _ => by linarith [hfac i])
  have humono : ∀ N, u N ≤ u (N + 1) := fun N => by
    rw [husucc]; nlinarith [hu0 N, hfac N]
  have key : ∀ N, ‖f N‖ ≤ u N ∧ ‖f (N + 1)‖ ≤ u (N + 1) := by
    intro N
    induction N with
    | zero =>
      refine ⟨by simp [hu, C], ?_⟩
      rw [husucc]
      simp only [hu, Finset.range_zero, Finset.prod_empty, mul_one, CharP.cast_eq_zero, mul_zero,
        zero_add]
      have : 0 ≤ 1 / r := by positivity
      nlinarith [le_max_right ‖f 0‖ ‖f 1‖]
    | succ N ih =>
      refine ⟨ih.2, ?_⟩
      have h := hf N
      have e : f (N + 2) = (2 * N + 3) / w * f (N + 1) - f N := by linear_combination h
      rw [e]
      calc ‖(2 * N + 3) / w * f (N + 1) - f N‖
          ≤ ‖(2 * N + 3) / w * f (N + 1)‖ + ‖f N‖ := norm_sub_le _ _
        _ = (2 * N + 3) / r * ‖f (N + 1)‖ + ‖f N‖ := by
          rw [norm_mul, norm_div]
          congr 2
          rw [show (2 * (N : ℂ) + 3) = ((2 * N + 3 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        _ ≤ (2 * N + 3) / r * u (N + 1) + u (N + 1) := by
          gcongr
          · exact ih.2
          · exact ih.1.trans (humono N)
        _ = u (N + 1 + 1) := by
          rw [husucc (N + 1)]; push_cast; ring
  exact (key N).1


/-- The ratio limit 30.8.7 in the form `(k+1)² a_{k+1}/a_k → γ²/16`. -/
private lemma tendsto_spheroidalCoeff_ratio {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * spheroidalCoeff n m γ2 ((k + 1 : ℕ) : ℤ) /
      spheroidalCoeff n m γ2 (k : ℤ)) atTop (𝓝 (γ2 / 16)) := by
  have h := (spheroidalCoeff_ratio_isBigO hmn γ2).trans_tendsto
    tendsto_inv_atTop_nhds_zero_nat
  have h2 := h.add_const (γ2 / 16)
  simp only [sub_add_cancel, zero_add] at h2
  have h3 := (tendsto_add_atTop_iff_nat 1).2 h2
  refine h3.congr fun k => ?_
  push_cast
  rw [show ((k : ℤ) + 1 - 1) = (k : ℤ) by ring]

/-- `x ↦ 1/(k+1)` tends to `0`. -/
private lemma tendsto_inv_succ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Rational limits used in the ratio test: `(a + 2(k+1))(b + 2(k+1))/(k+1)² → 4`. -/
private lemma tendsto_quad_div (a b : ℝ) :
    Tendsto (fun k : ℕ => (a + 2 * ((k : ℝ) + 1)) * (b + 2 * ((k : ℝ) + 1)) / ((k : ℝ) + 1) ^ 2)
      atTop (𝓝 4) := by
  have h := ((tendsto_inv_succ.const_mul a).const_add 2).mul
    ((tendsto_inv_succ.const_mul b).const_add 2)
  simp only [mul_zero, add_zero] at h
  norm_num at h
  refine h.congr fun k => ?_
  have : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring


/-- Summability of `|a^{-m}_{n,k}| B_{n+2k}` by the ratio test, for a positive sequence `B` with
`B_{N+2}/(B_N (k+1)²) → L`, `N = n + 2k`, and `|γ²| L/16 < 1`. -/
private lemma summable_abs_spheroidalCoeffNeg_mul {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ}
    (hγ : γ2 ≠ 0) {B : ℕ → ℝ} (hB : ∀ N, 0 < B N) {L : ℝ}
    (hL : Tendsto (fun k : ℕ => B (n + 2 * (k + 1)) / B (n + 2 * k) / ((k : ℝ) + 1) ^ 2) atTop
      (𝓝 L))
    (hl : |γ2| / 16 * L < 1) :
    Summable (fun k : ℕ => |spheroidalCoeffNeg n m γ2 k| * B (n + 2 * k)) := by
  set a : ℕ → ℝ := fun k => spheroidalCoeff n m γ2 (k : ℤ) with ha
  set F : ℕ → ℝ := fun k => ((n - m).factorial * (n + m + 2 * k).factorial : ℝ) /
    ((n + m).factorial * (n - m + 2 * k).factorial) with hF
  have hFpos : ∀ k, 0 < F k := fun k => by simp only [hF]; positivity
  have hc : ∀ k : ℕ, spheroidalCoeffNeg n m γ2 k = F k * a k := fun k => by
    rw [spheroidalCoeffNeg_of_le γ2 (by omega)]
    simp only [hF, ha]
    have e1 : ((n : ℤ) + m + 2 * (k : ℤ)).toNat = n + m + 2 * k := by omega
    have e2 : ((n : ℤ) - m + 2 * (k : ℤ)).toNat = n - m + 2 * k := by omega
    rw [e1, e2]
  have hFs : ∀ k, F (k + 1) / F k =
      (((n : ℝ) + m - 1) + 2 * ((k : ℝ) + 1)) * (((n : ℝ) + m) + 2 * ((k : ℝ) + 1)) /
        ((k : ℝ) + 1) ^ 2 /
      ((((n : ℝ) - m - 1) + 2 * ((k : ℝ) + 1)) * (((n : ℝ) - m) + 2 * ((k : ℝ) + 1)) /
        ((k : ℝ) + 1) ^ 2) := fun k => by
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have h1 : ((n : ℝ) - m - 1) + 2 * ((k : ℝ) + 1) ≠ 0 := by
      have : (0 : ℝ) < ((n : ℝ) - m - 1) + 2 * ((k : ℝ) + 1) := by
        have := k.cast_nonneg (α := ℝ); linarith
      exact this.ne'
    have h2 : ((n : ℝ) - m) + 2 * ((k : ℝ) + 1) ≠ 0 := by
      have : (0 : ℝ) < ((n : ℝ) - m) + 2 * ((k : ℝ) + 1) := by
        have := k.cast_nonneg (α := ℝ); linarith
      exact this.ne'
    have f1 : ((n + m + 2 * (k + 1)).factorial : ℝ) =
        (((n : ℝ) + m - 1) + 2 * ((k : ℝ) + 1)) * (((n : ℝ) + m) + 2 * ((k : ℝ) + 1)) *
          (n + m + 2 * k).factorial := by
      rw [show n + m + 2 * (k + 1) = (n + m + 2 * k + 1) + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast; ring
    have f2 : ((n - m + 2 * (k + 1)).factorial : ℝ) =
        (((n : ℝ) - m - 1) + 2 * ((k : ℝ) + 1)) * (((n : ℝ) - m) + 2 * ((k : ℝ) + 1)) *
          (n - m + 2 * k).factorial := by
      rw [show n - m + 2 * (k + 1) = (n - m + 2 * k + 1) + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast
      rw [Nat.cast_sub hmn]; ring
    simp only [hF]
    rw [f1, f2]
    have : ((n - m + 2 * k).factorial : ℝ) ≠ 0 := by positivity
    have : ((n + m + 2 * k).factorial : ℝ) ≠ 0 := by positivity
    have : ((n + m).factorial : ℝ) ≠ 0 := by positivity
    have : ((n - m).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have hG : Tendsto (fun k => F (k + 1) / F k) atTop (𝓝 1) := by
    have := (tendsto_quad_div ((n : ℝ) + m - 1) ((n : ℝ) + m)).div
      (tendsto_quad_div ((n : ℝ) - m - 1) ((n : ℝ) - m)) (by norm_num)
    norm_num at this
    exact this.congr fun k => (hFs k).symm
  have hR := tendsto_spheroidalCoeff_ratio hmn γ2
  have hane : ∀ᶠ k in atTop, a k ≠ 0 := by
    filter_upwards [hR.eventually_ne (by positivity : γ2 / 16 ≠ 0)] with k hk h0
    apply hk
    simp only [ha] at h0
    rw [h0, div_zero]
  refine summable_of_ratio_test_tendsto_lt_one hl ?_ ?_
  · filter_upwards [hane] with k hk
    rw [hc]
    exact mul_ne_zero (abs_ne_zero.2 (mul_ne_zero (hFpos k).ne' hk)) (hB _).ne'
  · have hlim := (hG.mul (continuous_abs.tendsto _ |>.comp hR)).mul hL
    rw [one_mul, Function.comp_def, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16)] at hlim
    refine hlim.congr' ?_
    filter_upwards [hane] with k hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    simp only [hc, Real.norm_eq_abs, abs_mul, abs_abs, abs_div, abs_pow,
      abs_of_pos (hFpos _), abs_of_pos (hB _)]
    rw [abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    have hak : |a k| ≠ 0 := abs_ne_zero.2 hk
    have hB1 := (hB (n + 2 * k)).ne'
    have hF1 := (hFpos k).ne'
    simp only [ha]
    push_cast
    field_simp


/-- **Convergence of the series 30.11.3**: for `γ ≠ 0` with `γ²` real, the series
`∑_{2k ≥ m-n} a^{-m}_{n,k}(γ²) ψ^{(j)}_{n+2k}(γz)` converges for `z ≠ 0` (`j = 1`) and for
`|z| > 1` (`j = 2, 3, 4`). Proved by the ratio test on a majorant: `k² a_k/a_{k-1} → γ²/16`
(30.8.7), the bound of `j_N` by its series, and for `j = 2, 3, 4` the three-term recurrence of
`ψ^{(j)}_N`, which gives `|ψ^{(j)}_N(w)| ≤ C ∏_{i<N} ((2i+1)/|w| + 1)`; the ratio of the majorant
tends to `0` (`j = 1`) or `1/|z|²` (`j = 2, 3, 4`). -/
@[dlmf 30.11.E3]
theorem summable_spheroidalRadial_series {j n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hj : j ∈ ({1, 2, 3, 4} : Finset ℕ))
    (hz : if j = 1 then z ≠ 0 else 1 < ‖z‖) :
    Summable (fun k : ℤ => (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
      spheroidalPsi j ((n : ℤ) + 2 * k).toNat (γ * z)) := by
  set γ2 := (γ ^ 2).re with hγ2def
  have hγ2c : (γ2 : ℂ) = γ ^ 2 := Complex.ext (by simp [γ2]) (by simp [hγ2])
  have hγ2n : |γ2| = ‖γ‖ ^ 2 := by
    rw [← norm_pow, ← hγ2c, Complex.norm_real, Real.norm_eq_abs]
  have hγ20 : γ2 ≠ 0 := by
    intro h; rw [h] at hγ2n; simp at hγ2n; exact hγ (by simpa using hγ2n.symm)
  have hz0 : z ≠ 0 := by
    split_ifs at hz with h
    · exact hz
    · intro h0; rw [h0, norm_zero] at hz; linarith
  set w := γ * z with hwdef
  have hw : w ≠ 0 := mul_ne_zero hγ hz0
  set r := ‖w‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 hw
  refine Summable.of_nat_of_neg ?_ ?_
  swap
  · refine summable_of_ne_finset_zero (s := Finset.range ((n - m) / 2 + 1)) fun k hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    have : spheroidalCoeffNeg n m γ2 (-(k : ℤ)) = 0 := by
      have hlt : ¬(-(((n - m) / 2 : ℕ) : ℤ) ≤ -(k : ℤ)) := by omega
      unfold spheroidalCoeffNeg; simp only [hlt, ↓reduceIte]
    simp [this]
  -- the majorant
  obtain ⟨B, hB, hBle, L, hL, hl⟩ : ∃ B : ℕ → ℝ, (∀ N, 0 < B N) ∧
      (∀ N, ‖spheroidalPsi j N w‖ ≤ B N) ∧ ∃ L : ℝ,
      Tendsto (fun k : ℕ => B (n + 2 * (k + 1)) / B (n + 2 * k) / ((k : ℝ) + 1) ^ 2) atTop
        (𝓝 L) ∧ |γ2| / 16 * L < 1 := by
    by_cases hj1 : j = 1
    · subst hj1
      set B : ℕ → ℝ := fun N => Real.sqrt π * r ^ N / 2 ^ (N + 1) *
        (Real.exp (r ^ 2 / 4) / Real.Gamma (N + 3 / 2)) with hBdef
      have hBpos : ∀ N, 0 < B N := fun N => by
        have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < N + 3 / 2)
        have := Real.sqrt_pos.2 Real.pi_pos
        positivity
      refine ⟨B, hBpos, fun N => ?_, 0, ?_, by simp⟩
      · simpa [spheroidalPsi] using DLMF.sphSeries_norm_sphericalJ_le N w
      have key : ∀ k : ℕ, B (n + 2 * (k + 1)) / B (n + 2 * k) / ((k : ℝ) + 1) ^ 2 =
          r ^ 2 / 4 * (1 / ((k : ℝ) + 1)) ^ 4 /
            ((((n : ℝ) - 1 / 2) + 2 * ((k : ℝ) + 1)) * (((n : ℝ) + 1 / 2) + 2 * ((k : ℝ) + 1)) /
              ((k : ℝ) + 1) ^ 2) := by
        intro k
        have hN : (0 : ℝ) < (n + 2 * k : ℕ) + 3 / 2 := by positivity
        have hg : Real.Gamma (((n + 2 * (k + 1) : ℕ) : ℝ) + 3 / 2) =
            ((((n + 2 * k : ℕ) : ℝ) + 3 / 2) + 1) * (((n + 2 * k : ℕ) : ℝ) + 3 / 2) *
              Real.Gamma (((n + 2 * k : ℕ) : ℝ) + 3 / 2) := by
          rw [show ((n + 2 * (k + 1) : ℕ) : ℝ) + 3 / 2 =
              ((((n + 2 * k : ℕ) : ℝ) + 3 / 2) + 1) + 1 by push_cast; ring,
            Real.Gamma_add_one (by positivity), Real.Gamma_add_one (by positivity)]
          ring
        have hG0 := (Real.Gamma_pos_of_pos hN).ne'
        have hπ := (Real.sqrt_pos.2 Real.pi_pos).ne'
        have he := (Real.exp_pos (r ^ 2 / 4)).ne'
        have hk : (k : ℝ) + 1 ≠ 0 := by positivity
        set P : ℝ := ((n + 2 * k : ℕ) : ℝ) + 3 / 2 with hP
        have hP0 : P ≠ 0 := hN.ne'
        have hP1 : P + 1 ≠ 0 := by positivity
        have hr0 := hr.ne'
        have s1 : B (n + 2 * (k + 1)) / B (n + 2 * k) = r ^ 2 / (4 * ((P + 1) * P)) := by
          simp only [hBdef]
          rw [hg, ← hP]
          rw [show n + 2 * (k + 1) = (n + 2 * k) + 2 by ring, pow_add, pow_add,
            show n + 2 * k + 2 + 1 = (n + 2 * k + 1) + 2 by ring, pow_add]
          field_simp
          ring
        have e1 : ((n : ℝ) - 1 / 2) + 2 * ((k : ℝ) + 1) = P := by rw [hP]; push_cast; ring
        have e2 : ((n : ℝ) + 1 / 2) + 2 * ((k : ℝ) + 1) = P + 1 := by rw [hP]; push_cast; ring
        rw [s1, e1, e2]
        field_simp
      have h0 : Tendsto (fun k : ℕ => r ^ 2 / 4 * (1 / ((k : ℝ) + 1)) ^ 4 /
          ((((n : ℝ) - 1 / 2) + 2 * ((k : ℝ) + 1)) * (((n : ℝ) + 1 / 2) + 2 * ((k : ℝ) + 1)) /
            ((k : ℝ) + 1) ^ 2)) atTop (𝓝 (r ^ 2 / 4 * 0 ^ 4 / 4)) :=
        ((tendsto_inv_succ.pow 4).const_mul (r ^ 2 / 4)).div
          (tendsto_quad_div ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2)) (by norm_num)
      rw [show r ^ 2 / 4 * (0 : ℝ) ^ 4 / 4 = 0 by ring] at h0
      exact h0.congr fun k => (key k).symm
    · have hj' : j = 2 ∨ j = 3 ∨ j = 4 := by simp at hj; omega
      have hz1 : 1 < ‖z‖ := by simpa [hj1] using hz
      set f : ℕ → ℂ := fun N => spheroidalPsi j N w with hf
      set C := max ‖f 0‖ ‖f 1‖
      have hC : 0 ≤ C := le_max_of_le_left (norm_nonneg _)
      set B : ℕ → ℝ := fun N => (C + 1) * ∏ i ∈ Finset.range N, ((2 * i + 1) / r + 1) with hBdef
      have hfac : ∀ i : ℕ, 0 < (2 * (i : ℝ) + 1) / r + 1 := fun i => by positivity
      have hBpos : ∀ N, 0 < B N := fun N =>
        mul_pos (by linarith) (Finset.prod_pos fun i _ => hfac i)
      refine ⟨B, hBpos, fun N => ?_, 16 / r ^ 2, ?_, ?_⟩
      · refine (norm_le_of_recurrence hw (fun N => spheroidalPsi_recurrence hj' N hw) N).trans ?_
        exact mul_le_mul_of_nonneg_right (by linarith)
          (Finset.prod_nonneg fun i _ => (hfac i).le)
      · have key : ∀ k : ℕ, B (n + 2 * (k + 1)) / B (n + 2 * k) / ((k : ℝ) + 1) ^ 2 =
            4 / r ^ 2 * ((((2 * n - 3 + r) / 2) + 2 * ((k : ℝ) + 1)) *
              (((2 * n - 1 + r) / 2) + 2 * ((k : ℝ) + 1)) / ((k : ℝ) + 1) ^ 2) := by
          intro k
          have hP := (Finset.prod_pos (s := Finset.range (n + 2 * k)) fun i _ => hfac i).ne'
          simp only [hBdef]
          rw [show n + 2 * (k + 1) = (n + 2 * k + 1) + 1 by ring, Finset.prod_range_succ,
            Finset.prod_range_succ]
          have hk : (k : ℝ) + 1 ≠ 0 := by positivity
          have hC1 : C + 1 ≠ 0 := by linarith
          have hr0 := hr.ne'
          field_simp
          push_cast
          ring
        have := (tendsto_quad_div ((2 * n - 3 + r) / 2) ((2 * n - 1 + r) / 2)).const_mul
          (4 / r ^ 2)
        rw [show 4 / r ^ 2 * 4 = 16 / r ^ 2 by ring] at this
        exact this.congr fun k => (key k).symm
      · have hrz : r = ‖γ‖ * ‖z‖ := by rw [hrdef, hwdef, norm_mul]
        have hγ0 : 0 < ‖γ‖ := norm_pos_iff.2 hγ
        rw [hγ2n, hrz]
        have : ‖γ‖ ^ 2 / 16 * (16 / (‖γ‖ * ‖z‖) ^ 2) = 1 / ‖z‖ ^ 2 := by
          field_simp
        rw [this, div_lt_one (by positivity)]
        nlinarith
  have hsum := summable_abs_spheroidalCoeffNeg_mul hmn hγ20 hB hL hl
  refine Summable.of_norm_bounded hsum fun k => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show ((n : ℤ) + 2 * (k : ℤ)).toNat = n + 2 * k by omega]
  exact mul_le_mul_of_nonneg_left (hBle _) (abs_nonneg _)

/-- **The radial functions solve 30.2.1** (DLMF 30.11.3) with `μ = m`, `λ = λ^m_n(γ²)`, on the
open set where the principal powers in 30.11.1, 30.11.3 are analytic: `1 - z⁻²` off `(-∞, 0]`,
and, for `j = 2, 3, 4`, `|z| > 1` and `γz` off `(-∞, 0]`. -/
@[dlmf 30.11.E3]
theorem isSpheroidalSolutionOn_spheroidalRadial {j n m : ℕ} (hmn : m ≤ n) {γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hj : j ∈ ({1, 2, 3, 4} : Finset ℕ)) :
    IsSpheroidalSolutionOn (spheroidalEigenvalue n m (γ ^ 2).re) (γ ^ 2).re m
      {z : ℂ | z ≠ 0 ∧ 1 - z ^ (-2 : ℤ) ∈ slitPlane ∧
        (j = 1 ∨ (1 < ‖z‖ ∧ γ * z ∈ slitPlane))}
      (fun z => spheroidalRadial j n m z γ) := by
  sorry

/-- **Connection formulas** (DLMF 30.11.5): `S^{m(3)}_n = S^{m(1)}_n + iS^{m(2)}_n` and
`S^{m(4)}_n = S^{m(1)}_n - iS^{m(2)}_n` for `|z| > 1`, `γz` off `(-∞, 0]`. Proved from the
convergence of 30.11.3 and `spheroidalPsi_three_four`. -/
@[dlmf 30.11.E5]
theorem spheroidalRadial_three_four {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hz : 1 < ‖z‖) (hγz : γ * z ∈ slitPlane) :
    spheroidalRadial 3 n m z γ = spheroidalRadial 1 n m z γ + I * spheroidalRadial 2 n m z γ ∧
      spheroidalRadial 4 n m z γ = spheroidalRadial 1 n m z γ - I * spheroidalRadial 2 n m z γ := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have h1 := summable_spheroidalRadial_series (j := 1) hmn hγ hγ2 (by simp) (by simpa using hz0)
  have h2 := summable_spheroidalRadial_series (j := 2) hmn hγ hγ2 (by simp) (by simpa using hz)
  have h2' := h2.mul_left I
  have key : ∀ k : ℤ, (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
      spheroidalPsi 3 ((n : ℤ) + 2 * k).toNat (γ * z) =
        (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
          spheroidalPsi 1 ((n : ℤ) + 2 * k).toNat (γ * z) +
        I * ((spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
          spheroidalPsi 2 ((n : ℤ) + 2 * k).toNat (γ * z)) := by
    intro k; rw [(spheroidalPsi_three_four _ hγz).1]; ring
  have key' : ∀ k : ℤ, (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
      spheroidalPsi 4 ((n : ℤ) + 2 * k).toNat (γ * z) =
        (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
          spheroidalPsi 1 ((n : ℤ) + 2 * k).toNat (γ * z) -
        I * ((spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
          spheroidalPsi 2 ((n : ℤ) + 2 * k).toNat (γ * z)) := by
    intro k; rw [(spheroidalPsi_three_four _ hγz).2]; ring
  constructor
  · simp only [spheroidalRadial]
    rw [tsum_congr key, h1.tsum_add h2', tsum_mul_left]
    ring
  · simp only [spheroidalRadial]
    rw [tsum_congr key', h1.tsum_sub h2', tsum_mul_left]
    ring

/-! ### §30.11(iii) Asymptotic behaviour -/

/-- **Asymptotic behaviour** (DLMF 30.11.6, `j = 1, 2`, corrected): for real `γ > 0`, as
`z → ∞` in `|ph z| ≤ π - δ`, `S^{m(j)}_n(z, γ) = ψ^{(j)}_n(γz) + O(z⁻² e^{|ℑ(γz)|})`. DLMF prints
`e^{|ℑz|}`, which is wrong for `γ > 1` (see the module docstring). -/
@[dlmf 30.11.E6]
theorem spheroidalRadial_isBigO_one_two {j n m : ℕ} (hmn : m ≤ n) {γ δ : ℝ} (hγ : 0 < γ)
    (hδ : 0 < δ) (hj : j = 1 ∨ j = 2) :
    (fun z : ℂ => spheroidalRadial j n m z γ - spheroidalPsi j n (γ * z)) =O[DLMF.sector (π - δ)]
      (fun z : ℂ => z ^ (-2 : ℤ) * Real.exp |(γ * z).im|) := by
  sorry

/-- **Asymptotic behaviour** (DLMF 30.11.6, `j = 3, 4`): for real `γ > 0`, as `z → ∞` in
`|ph z| ≤ π - δ`, `S^{m(j)}_n(z, γ) = ψ^{(j)}_n(γz)(1 + O(z⁻¹))`. -/
@[dlmf 30.11.E6]
theorem spheroidalRadial_isBigO_three_four {j n m : ℕ} (hmn : m ≤ n) {γ δ : ℝ} (hγ : 0 < γ)
    (hδ : 0 < δ) (hj : j = 3 ∨ j = 4) :
    (fun z : ℂ => spheroidalRadial j n m z γ - spheroidalPsi j n (γ * z)) =O[DLMF.sector (π - δ)]
      (fun z : ℂ => spheroidalPsi j n (γ * z) * z⁻¹) := by
  sorry

/-! ### §30.11(iv) Wronskian -/

/-- **Wronskian** (DLMF 30.11.7): `𝒲{S^{m(1)}_n(z, γ), S^{m(2)}_n(z, γ)} = 1/(γ(z²-1))`, for
`|z| > 1` with `1 - z⁻²` and `γz` off `(-∞, 0]`. -/
@[dlmf 30.11.E7]
theorem wronskian_spheroidalRadial {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hz : 1 < ‖z‖) (hz' : 1 - z ^ (-2 : ℤ) ∈ slitPlane)
    (hγz : γ * z ∈ slitPlane) :
    spheroidalRadial 1 n m z γ * deriv (fun t => spheroidalRadial 2 n m t γ) z -
        deriv (fun t => spheroidalRadial 1 n m t γ) z * spheroidalRadial 2 n m z γ =
      1 / (γ * (z ^ 2 - 1)) := by
  sorry

/-! ### §30.11(v) Connection with `𝑃s` and `𝑄s` -/

/-- **Connection with `𝑃s`** (DLMF 30.11.8, with `K^m_n(γ)` from 30.11.10–30.11.11):
`S^{m(1)}_n(z, γ) = K^m_n(γ) 𝑃s^m_n(z, γ²)` for `z ∈ ℂ ∖ (-∞, 1]`, `γ ≠ 0`, `γ²` real. -/
@[dlmf 30.11.E8, dlmf 30.11.E10, dlmf 30.11.E11]
theorem spheroidalRadial_one_eq {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hz : z ∈ spheroidalCutPlane) :
    spheroidalRadial 1 n m z γ = spheroidalK n m γ * spheroidalPsC n m z (γ ^ 2).re := by
  sorry

/-- **Connection with `𝑄s`** (DLMF 30.11.9):
`S^{m(2)}_n(z, γ) = (n-m)!/(n+m)! (-1)^{m+1} 𝑄s^m_n(z, γ²)/(γ K^m_n(γ) A^m_n(γ²) A^{-m}_n(γ²))`
for `z ∈ ℂ ∖ (-∞, 1]` with `|z| > 1` and `γz` off `(-∞, 0]`. -/
@[dlmf 30.11.E9]
theorem spheroidalRadial_two_eq {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0)
    (hf : spheroidalFwd n m (γ ^ 2).re ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0)
    (hz : z ∈ spheroidalCutPlane) (hz1 : 1 < ‖z‖) (hγz : γ * z ∈ slitPlane) :
    spheroidalRadial 2 n m z γ = ((n - m).factorial : ℂ) / (n + m).factorial *
      ((-1) ^ (m + 1) * spheroidalQsC n m z (γ ^ 2).re) /
        (γ * spheroidalK n m γ * spheroidalA n m (γ ^ 2).re * spheroidalANeg n m (γ ^ 2).re) := by
  sorry

/-! ### §30.11(vi) Integral representation -/

/-- **Integral representation** (DLMF 30.11.12): for `z ∈ ℂ ∖ (-∞, 1]`,
`A^{-m}_n(γ²) S^{m(1)}_n(z, γ) = ½ i^{m+n} γ^m (n-m)!/(n+m)! z^m (1-z⁻²)^{m/2}
  ∫_{-1}^1 e^{-iγzt} (1-t²)^{m/2} 𝖯s^m_n(t, γ²) dt`. -/
@[dlmf 30.11.E12]
theorem spheroidalRadial_one_integral {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hz : z ∈ spheroidalCutPlane) :
    spheroidalANeg n m (γ ^ 2).re * spheroidalRadial 1 n m z γ =
      1 / 2 * I ^ (m + n) * γ ^ m * (((n - m).factorial : ℂ) / (n + m).factorial) * z ^ m *
        (1 - z ^ (-2 : ℤ)) ^ ((m : ℂ) / 2) *
        ∫ t in (-1 : ℝ)..1, Complex.exp (-(I * γ * z * t)) *
          (((1 - t ^ 2) ^ ((m : ℝ) / 2) * spheroidalPs n m t (γ ^ 2).re : ℝ) : ℂ) := by
  sorry

end DLMF.Spheroidal
