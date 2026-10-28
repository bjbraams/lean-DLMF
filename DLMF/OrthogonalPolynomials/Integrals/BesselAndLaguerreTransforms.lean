/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals.ConvolutionsAndFourier

/-!
# Bessel-square and Laguerre product transforms

Legendre-Bessel square moments, Hermite Fourier transforms and Laguerre product Laplace
transforms.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Integrals`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
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

/-- Moments of `P_n(1 - 2x²)` on `[0, 1]`, from the substitution `s = 1 - 2x²` and the
Jacobi moments: `∫₀¹ x^{2k+1} P_n(1-2x²) dx = k! (-k)_n / (2 (k+n+1)!)`. -/
private lemma lbsq_moment (n k : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ (2 * k + 1) * legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) =
      (1 / 2 : ℂ) * k ! * poch (-(k : ℂ)) n / ((k + n + 1) ! : ℂ) := by
  set F : ℝ → ℂ := fun s => legendrePolyP n (s : ℂ) * ((1 - (s : ℂ)) / 2) ^ k with hF
  have h1 : (∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ (2 * k + 1) *
      legendrePolyP n (1 - 2 * (x : ℂ) ^ 2)) =
        ∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) * F (1 - 2 * x ^ 2) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hF]; push_cast
    rw [show ((1 : ℂ) - (1 - 2 * (x : ℂ) ^ 2)) / 2 = (x : ℂ) ^ 2 by ring, ← pow_mul]
    ring
  have hJ := jacobi_moment (α := 0) (β := 0) (by norm_num) (by norm_num) n k
  have hneg := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) F
  norm_num only [neg_neg] at hneg
  have h2 : (∫ s : ℝ in (-1 : ℝ)..1, F s) = (2 : ℂ)⁻¹ ^ k * (-1 : ℂ) ^ n *
      ∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + 1) ^ k *
        (jacobiPolyP ((0:ℝ):ℂ) ((0:ℝ):ℂ) n x * (1 - (x : ℂ)) ^ ((0:ℝ) : ℂ) *
          (1 + (x : ℂ)) ^ ((0:ℝ) : ℂ)) := by
    rw [← hneg, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hF, ofReal_zero, cpow_zero, mul_one]
    push_cast
    rw [legendrePolyP, jacobi_reflection (by norm_num) (by norm_num)]
    rw [show ((1 : ℂ) - -(s : ℂ)) / 2 = 2⁻¹ * ((s : ℂ) + 1) by ring, mul_pow]
    ring
  rw [h1, integral_mul_comp_one_sub_two_sq, h2, hJ]
  have hG1 : Gamma ((0:ℝ) + k + 1 : ℂ) = k ! := by
    rw [show ((0:ℝ) : ℂ) + k + 1 = (k : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hG2 : Gamma (1 + ((0:ℝ):ℂ) + n) = n ! := by
    rw [show 1 + ((0:ℝ) : ℂ) + n = (n : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hG3 : Gamma (1 + ((0:ℝ):ℂ) + (((0:ℝ):ℂ) + k + 1) + n) = (k + n + 1) ! := by
    rw [show 1 + ((0:ℝ) : ℂ) + (((0:ℝ):ℂ) + k + 1) + n = ((k + n + 1 : ℕ) : ℂ) + 1 by
      push_cast; ring, Gamma_nat_eq_factorial]
  have hP : (2 : ℂ) ^ (((0:ℝ):ℂ) + (((0:ℝ):ℂ) + k + 1)) = 2 ^ (k + 1) := by
    rw [show ((0:ℝ) : ℂ) + (((0:ℝ):ℂ) + k + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
      cpow_natCast]
  rw [hG1, hG2, hG3, hP]
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hkn : ((k + n + 1) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  rw [inv_pow, pow_succ]
  field_simp
  ring_nf
  rw [pow_mul]
  norm_num
  rw [sq, hs, mul_one]

/-- `x ↦ P_n(1 - 2x²)` is continuous. -/
private lemma lbsq_continuous (n : ℕ) :
    Continuous fun x : ℝ => legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) := by
  simp_rw [legendre_eq_ultrasphPoly]
  exact (continuousOn_univ.1 (analyticOnNhd_ultrasphPoly _ n).continuousOn).comp (by fun_prop)

/-- Termwise integration of the sine series against `P_n(1 - 2x²)` on `[0, 1]`. -/
private lemma lbsq_hasSum_integral (n : ℕ) (y : ℝ) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * (y : ℂ) ^ (2 * k + 1) / ((2 * k + 1) ! : ℂ) *
        ∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ (2 * k + 1) * legendrePolyP n (1 - 2 * (x : ℂ) ^ 2))
      (∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y)) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (lbsq_continuous n).continuousOn (s := Set.Icc (0 : ℝ) 1)
  set F : ℕ → ℝ → ℂ := fun k x => (-1 : ℂ) ^ k * (y : ℂ) ^ (2 * k + 1) / ((2 * k + 1) ! : ℂ) *
    ((x : ℂ) ^ (2 * k + 1) * legendrePolyP n (1 - 2 * (x : ℂ) ^ 2)) with hF
  have hc : ∀ k, Continuous (F k) := fun k => by
    simp only [hF]; exact continuous_const.mul ((by fun_prop : Continuous fun x : ℝ =>
      (x : ℂ) ^ (2 * k + 1)).mul (lbsq_continuous n))
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := F) (a := 0) (b := 1) (μ := volume)
    (f := fun x => legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y))
    (fun k _ => |y| ^ (2 * k + 1) / ((2 * k + 1) ! : ℝ) * B)
    (fun k => (hc k).aestronglyMeasurable)
    (fun k => ae_of_all _ fun x hx => by
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hx1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      simp only [hF, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      have hxa : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx1.1, hx1.2]
      have h1 : |x| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hxa
      have h2 := hB x hx1
      have hf : (0 : ℝ) < ((2 * k + 1) ! : ℝ) := by positivity
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hf]
      calc |y| ^ (2 * k + 1) * (|x| ^ (2 * k + 1) * ‖legendrePolyP n (1 - 2 * (x : ℂ) ^ 2)‖)
          ≤ |y| ^ (2 * k + 1) * (1 * B) := by
            gcongr
      _ = _ := by ring)
    (ae_of_all _ fun x _ => ((Real.hasSum_sinh |y|).summable.mul_right B))
    intervalIntegrable_const
    (ae_of_all _ fun x _ => by
      have hs := (Complex.hasSum_ofReal.mpr (Real.hasSum_sin (x * y))).mul_left
        (legendrePolyP n (1 - 2 * (x : ℂ) ^ 2))
      refine hs.congr_fun fun k => ?_
      simp only [hF]; push_cast; ring)
  refine h.congr_fun fun k => ?_
  simp only [hF]
  rw [intervalIntegral.integral_const_mul]

/-- Coefficient identity matching the moment series with the series of `J_{n+1/2}²`
(DLMF 10.8.3). -/
private lemma lbsq_coeff (n m : ℕ) (y : ℝ) :
    (-1 : ℂ) ^ (m + n) * (y : ℂ) ^ (2 * (m + n) + 1) / ((2 * (m + n) + 1) ! : ℂ) *
      ((1 / 2 : ℂ) * (m + n) ! * poch (-((m + n : ℕ) : ℂ)) n / ((m + n + n + 1) ! : ℂ)) =
    (Real.pi : ℂ) / 2 * ((y : ℂ) / 2 / 2) ^ ((n + 1 / 2 : ℂ) + (n + 1 / 2 : ℂ)) *
      (poch ((n + 1 / 2 : ℂ) + (n + 1 / 2 : ℂ) + m + 1) m * (-(((y : ℂ) / 2) ^ 2 / 4)) ^ m /
        (m ! : ℂ) * (Gamma ((n + 1 / 2 : ℂ) + m + 1))⁻¹ * (Gamma ((n + 1 / 2 : ℂ) + m + 1))⁻¹) := by
  set k := m + n with hk
  have hexp : (n + 1 / 2 : ℂ) + (n + 1 / 2 : ℂ) = ((2 * n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hexp, cpow_natCast]
  have hP : poch (-((k : ℕ) : ℂ)) n * (m ! : ℂ) = (-1) ^ n * (k ! : ℂ) := by
    rw [poch_neg_coe_nat]
    have h := Nat.factorial_mul_descFactorial (show n ≤ k by omega)
    rw [show k - n = m by omega] at h
    have h' : (m ! : ℂ) * (k.descFactorial n : ℂ) = k ! := by exact_mod_cast h
    linear_combination (-1 : ℂ) ^ n * h'
  have hQ : poch (((2 * n + 1 : ℕ) : ℂ) + m + 1) m * ((2 * n + m + 1) ! : ℂ) = (2 * k + 1) ! := by
    have h := poch_nat_succ_eq_choose_mul_factorial (2 * n + m + 1) m
    push_cast at h ⊢
    rw [show (2 * (n : ℂ) + 1 + m + 1) = 2 * n + m + 1 + 1 by ring, h]
    have hc := Nat.choose_mul_factorial_mul_factorial
      (show 2 * n + m + 1 ≤ 2 * n + m + 1 + m by omega)
    rw [show 2 * n + m + 1 + m - (2 * n + m + 1) = m by omega,
      show 2 * n + m + 1 + m = 2 * k + 1 by omega] at hc
    rw [show 2 * n + m + 1 + m = 2 * k + 1 by omega]
    have hc' : ((2 * k + 1).choose (2 * n + m + 1) : ℂ) * ((2 * n + m + 1) ! : ℂ) * (m ! : ℂ) =
      ((2 * k + 1) ! : ℂ) := by exact_mod_cast hc
    linear_combination hc'
  have hG : Gamma ((n + 1 / 2 : ℂ) + m + 1) =
      ((2 * k + 2) * (2 * k + 1) ! : ℂ) / (4 ^ (k + 1) * ((k + 1) * k ! : ℂ)) * Gamma (1 / 2) := by
    rw [show (n + 1 / 2 : ℂ) + m + 1 = 1 / 2 + ((k + 1 : ℕ) : ℂ) by rw [hk]; push_cast; ring,
      Gamma_nat_add_half, show 2 * (k + 1) = (2 * k + 1) + 1 by ring,
      Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ k]
    push_cast; ring
  have hpi : Gamma (1 / 2 : ℂ) ^ 2 = Real.pi := by
    rw [Complex.Gamma_one_half_eq, ← cpow_nat_mul]; norm_num
  have hk' : m + n + n + 1 = 2 * n + m + 1 := by omega
  rw [hk', hG]
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hf1 : ((2 * k + 1) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : ((k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : ((m) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf4 : ((2 * n + m + 1) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hk2 : (2 * (k : ℂ) + 2) ≠ 0 := by
    have h : ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at h; exact h
  rw [← hpi]
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  rw [eq_div_of_mul_eq hf3 hP, eq_div_of_mul_eq hf4 hQ]
  field_simp
  ring_nf
  rw [hk, show (-1 / 16 : ℂ) = -1 * 4⁻¹ ^ 2 by norm_num, mul_pow, ← pow_mul, one_div, inv_pow,
    inv_pow]
  field_simp
  ring_nf
  rw [show ((-1 : ℂ)) ^ (n * 2) = 1 by rw [mul_comm, pow_mul]; simp, mul_one]

/-- DLMF 18.17.21 for `y > 0`. -/
private lemma lbsq_pos (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y) =
      Real.pi / 2 * besselJ (n + 1 / 2 : ℂ) ((y : ℂ) / 2) ^ 2 := by
  have hL := lbsq_hasSum_integral n y
  simp_rw [lbsq_moment] at hL
  rw [← hasSum_nat_add_iff' n] at hL
  rw [Finset.sum_eq_zero (fun k hk => by
    rw [poch_neg_nat_eq_zero (Finset.mem_range.mp hk)]; simp), sub_zero] at hL
  have hz : ((y : ℂ) / 2) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp; linarith
  rw [sq, besselJ_mul_besselJ _ _ hz]
  have hR := hL.congr_fun (fun m => (lbsq_coeff n m y).symm)
  rw [← hR.tsum_eq, tsum_mul_left, mul_assoc]

/-- `J_{n+1/2}(w)² = (w/2)^{2n+1} 𝐅(;n+3/2;-w²/4)²` for all `w`, without a branch condition. -/
private lemma lbsq_bessel_sq (n : ℕ) (w : ℂ) :
    besselJ (n + 1 / 2 : ℂ) w ^ 2 = (w / 2) ^ (2 * n + 1) *
      regularizedHGFun (∅ : Multiset ℂ) {(n + 1 / 2 : ℂ) + 1} (-(w ^ 2 / 4)) ^ 2 := by
  rw [besselJ_eq_regularized, mul_pow, ← cpow_nat_mul,
    show ((2 : ℕ) : ℂ) * (n + 1 / 2 : ℂ) = ((2 * n + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (0 : ℝ)..1,
legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y) = Real.pi / 2 * besselJ (n + 1 / 2 :
ℂ) ((y : ℂ) / 2) ^ 2`. -/
@[dlmf 18.17.E21]
theorem legendre_bessel_square_integral (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y) =
      Real.pi / 2 * besselJ (n + 1 / 2 : ℂ) ((y : ℂ) / 2) ^ 2 := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have h := lbsq_pos n (neg_pos.mpr hy)
    rw [lbsq_bessel_sq] at h ⊢
    have hl : (∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y)) =
        -∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * -y) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [mul_neg, Real.sin_neg]; push_cast; ring
    rw [hl, h]
    push_cast
    rw [show -(y : ℂ) / 2 / 2 = -((y : ℂ) / 2 / 2) by ring, Odd.neg_pow (by exact ⟨n, rfl⟩),
      neg_div, neg_sq]
    ring
  · simp only [mul_zero, Real.sin_zero, ofReal_zero, zero_div, intervalIntegral.integral_zero]
    rw [lbsq_bessel_sq]; simp
  · exact lbsq_pos n hy

/-- Identity under the stated parameter and domain assumptions: `(∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 4)
* (aeval (x : ℂ) (hermite n) : ℂ) * exp (I * x * y / 2)) / (2 * Real.sqrt Real.pi) = I ^ n *
exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n)`. -/
@[dlmf 18.17.E22]
theorem hermite_fourier_eigenfunction (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 4) * (aeval (x : ℂ) (hermite n) : ℂ) * exp (I * x * y / 2)) /
      (2 * Real.sqrt Real.pi) = I ^ n * exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n) := by
  let r := Real.sqrt 2
  have hr : 0 < r := Real.sqrt_pos.mpr two_pos
  have hr0 : r ≠ 0 := hr.ne'
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let c := Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)
  let F : ℝ → ℂ := fun x => exp (-(x : ℂ) ^ 2 / 4) * aeval (x : ℂ) (hermite n) * exp (I * x * y / 2)
  have hscale := Measure.integral_comp_mul_left F r
  have hx (x : ℝ) : F (r * x) = (c : ℂ) *
      (exp (I * x * ↑(y / r)) * (TauCeti.hermiteFunction n x : ℂ)) := by
    dsimp [F]
    rw [hermite_envelope]
    change (c : ℂ) * (TauCeti.hermiteFunction n (r * x / r) : ℂ) * exp (I * ↑(r * x) * y / 2) = _
    rw [mul_div_cancel_left₀ x hr0]
    have he : I * ↑(r * x) * y / 2 = I * x * ↑(y / r) := by
      push_cast
      have hrc : (r : ℂ) ^ 2 = 2 := by exact_mod_cast hr2
      have hr0c : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0
      field_simp
      linear_combination (x : ℂ) * y * hrc
    rw [he]
    ring
  simp_rw [hx] at hscale
  rw [integral_const_mul, hermiteFunction_integral, abs_of_pos (inv_pos.mpr hr), Complex.real_smul] at hscale
  have hrs : (r : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) = 2 * (Real.sqrt Real.pi : ℂ) := by
    norm_cast
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    change r * (r * Real.sqrt Real.pi) = _
    rw [← mul_assoc, ← pow_two, hr2]
  rw [show I ^ n * exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n) =
    I ^ n * (exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n)) by ring, hermite_envelope]
  change (∫ x, F x) / (2 * ↑(Real.sqrt Real.pi)) = I ^ n * ((c : ℂ) * ↑(TauCeti.hermiteFunction n (y / r)))
  have hr0c : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0
  have hp0 : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [ofReal_inv] at hscale
  field_simp [hr0c] at hscale
  apply (div_eq_iff (mul_ne_zero two_ne_zero hp0)).mpr
  calc
    _ = (c : ℂ) * (r * ↑(Real.sqrt (2 * Real.pi))) * I ^ n * ↑(TauCeti.hermiteFunction n (y / r)) := by
      linear_combination -hscale
    _ = _ := by rw [hrs]; ring

/-! ### Fourier transforms of `He_n(x) e^{-x²/2}` -/

/-- The Hermite–Gaussian function `He_n(x) e^{-x²/2}`. -/
def hermiteGauss (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))

/-- `He_n(x) e^{-x²/2} = (-1)^n dⁿ/dxⁿ e^{-x²/2}`. -/
theorem hermiteGauss_eq_iterate (n : ℕ) (x : ℝ) :
    hermiteGauss n x = (-1) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x := by
  rw [deriv_gaussian_eq_hermite_mul_gaussian, hermiteGauss, ← mul_assoc, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- `(He_n e^{-x²/2})' = -He_{n+1} e^{-x²/2}`. -/
theorem hasDerivAt_hermiteGauss (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteGauss n) (-hermiteGauss (n + 1) x) x := by
  have hg : ContDiff ℝ ⊤ fun y : ℝ => Real.exp (-(y ^ 2 / 2)) := by fun_prop
  have hd : Differentiable ℝ (deriv^[n] fun y : ℝ => Real.exp (-(y ^ 2 / 2))) := by
    rw [← iteratedDeriv_eq_iterate]
    exact hg.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)
  have hfun : hermiteGauss n = fun x =>
      (-1) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x :=
    funext (hermiteGauss_eq_iterate n)
  rw [hfun, hermiteGauss_eq_iterate, Function.iterate_succ_apply', pow_succ]
  convert ((hd x).hasDerivAt.const_mul ((-1 : ℝ) ^ n)) using 1
  ring

/-- `He_n(x) e^{-x²/2}` is integrable (Tau Ceti `integrable_aeval_mul_gaussian`). -/
theorem integrable_hermiteGauss (n : ℕ) : Integrable (hermiteGauss n) :=
  TauCeti.integrable_aeval_mul_gaussian (hermite n)

/-- The positive-phase Fourier transform of `He_n(x) e^{-x²/2}`. -/
theorem integral_exp_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    ∫ x : ℝ, cexp (I * y * x) * (hermiteGauss n x : ℂ) =
      (I * y) ^ n * (Real.sqrt (2 * π) * Real.exp (-(y ^ 2 / 2)) : ℝ) := by
  induction n with
  | zero =>
    have h := fourierIntegral_gaussian (b := 1 / 2) (by norm_num) (y : ℂ)
    simp only [hermiteGauss, hermite_zero, map_one, one_mul, pow_zero]
    convert h using 1
    · congr 1; funext x; congr 1; push_cast; congr 1; ring
    · rw [show (π : ℂ) / (1 / 2) = 2 * π by ring, Complex.ofReal_mul, Real.sqrt_eq_rpow,
        Complex.ofReal_cpow (by positivity), Complex.ofReal_exp]
      push_cast
      congr 2
      ring
  | succ n ih =>
    have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (I * y * x)) (I * y * cexp (I * y * x)) x :=
      fun x => by
        have := ((hasDerivAt_id (x : ℂ)).const_mul (I * y)).cexp.comp_ofReal
        simpa [mul_comm] using this
    have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (hermiteGauss n x : ℂ))
        ((-hermiteGauss (n + 1) x : ℝ) : ℂ) x :=
      fun x => (hasDerivAt_hermiteGauss n x).ofReal_comp
    have hint : ∀ m, Integrable fun x : ℝ => cexp (I * y * x) * (hermiteGauss m x : ℂ) := by
      intro m
      refine (integrable_hermiteGauss m).ofReal.bdd_mul (c := 1) ?_ ?_
      · exact (by fun_prop : Continuous fun x : ℝ => cexp (I * y * x)).aestronglyMeasurable
      · refine Eventually.of_forall fun x => le_of_eq ?_
        rw [Complex.norm_exp]
        simp
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x)
      (fun x _ => hv x)
      ((hint (n + 1)).neg.congr (Eventually.of_forall fun x => by simp))
      (((hint n).const_mul (I * y)).congr (Eventually.of_forall fun x => by simp; ring))
      (hint n)
    simp only [ofReal_neg, mul_neg, integral_neg, neg_inj] at hibp
    rw [hibp, show (fun x : ℝ => I * y * cexp (I * y * x) * (hermiteGauss n x : ℂ)) =
      fun x : ℝ => I * y * (cexp (I * y * x) * (hermiteGauss n x : ℂ)) by funext x; ring,
      integral_const_mul, ih, pow_succ]
    ring

/-- `e^{iyx} He_n(x) e^{-x²/2}` is integrable. -/
theorem integrable_exp_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    Integrable fun x : ℝ => cexp (I * y * x) * (hermiteGauss n x : ℂ) := by
  refine (integrable_hermiteGauss n).ofReal.bdd_mul (c := 1) ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ => cexp (I * y * x)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [Complex.norm_exp]
    simp

/-- Rewriting `e^{iyx}` as `e^{(yx) i}`. -/
theorem exp_I_mul_eq (y x : ℝ) : cexp (I * y * x) = cexp (((y * x : ℝ) : ℂ) * I) := by
  push_cast; ring_nf

/-- The cosine transform of `He_n(x) e^{-x²/2}` over `ℝ`. -/
theorem integral_cos_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    ∫ x : ℝ, Real.cos (y * x) * hermiteGauss n x =
      ((I * y) ^ n).re * (Real.sqrt (2 * π) * Real.exp (-(y ^ 2 / 2))) := by
  have h := congrArg Complex.re (integral_exp_mul_hermiteGauss n y)
  have hr := integral_re (integrable_exp_mul_hermiteGauss n y)
  simp only [RCLike.re_to_complex] at hr
  rw [← hr, Complex.re_mul_ofReal] at h
  rw [← h]
  congr 1; funext x
  rw [exp_I_mul_eq, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]

/-- The sine transform of `He_n(x) e^{-x²/2}` over `ℝ`. -/
theorem integral_sin_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    ∫ x : ℝ, Real.sin (y * x) * hermiteGauss n x =
      ((I * y) ^ n).im * (Real.sqrt (2 * π) * Real.exp (-(y ^ 2 / 2))) := by
  have h := congrArg Complex.im (integral_exp_mul_hermiteGauss n y)
  have hi := integral_im (integrable_exp_mul_hermiteGauss n y)
  simp only [RCLike.im_to_complex] at hi
  rw [← hi, Complex.im_mul_ofReal] at h
  rw [← h]
  congr 1; funext x
  rw [exp_I_mul_eq, Complex.im_mul_ofReal, Complex.exp_ofReal_mul_I_im]

/-- `√(2π)/2 = √(π/2)`. -/
theorem sqrt_two_pi_div_two : Real.sqrt (2 * π) / 2 = Real.sqrt (π / 2) := by
  rw [show π / 2 = (2 * π) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq (by norm_num)]

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Set.Ioi 0, Real.exp
(-(x ^ 2) / 2) * (aeval x (hermite (2 * n)) : ℝ) * Real.cos (x * y) = (-1 : ℝ) ^ n * Real.sqrt
(Real.pi / 2) * y ^ (2 * n) * Real.exp (-(y ^ 2) / 2)`. -/
@[dlmf 18.17.E23]
theorem hermite_even_cosine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n)) : ℝ) * Real.cos (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n) * Real.exp (-(y ^ 2) / 2) := by
  set f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n)) : ℝ) *
    Real.cos (x * y) with hf
  have heven : ∀ x, f |x| = f x := by
    intro x
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hf]
      simp only [hermite_aeval_neg, pow_mul, one_pow, one_mul, neg_mul, Real.cos_neg,
        even_two, Even.neg_pow]
  have habs := integral_comp_abs (f := f)
  simp_rw [heven] at habs
  have hfull : ∫ x, f x = ∫ x : ℝ, Real.cos (y * x) * hermiteGauss (2 * n) x := by
    congr 1; funext x
    simp only [hf, hermiteGauss, neg_div, mul_comm x y]
    ring
  rw [hfull, integral_cos_mul_hermiteGauss, mul_pow, pow_mul, I_sq] at habs
  have hre : (((-1 : ℂ) ^ n) * (y : ℂ) ^ (2 * n)).re = (-1 : ℝ) ^ n * y ^ (2 * n) := by
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
    norm_cast
  rw [hre] at habs
  rw [← sqrt_two_pi_div_two, neg_div]
  linarith

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Set.Ioi 0, Real.exp
(-(x ^ 2) / 2) * (aeval x (hermite (2 * n + 1)) : ℝ) * Real.sin (x * y) = (-1 : ℝ) ^ n *
Real.sqrt (Real.pi / 2) * y ^ (2 * n + 1) * Real.exp (-(y ^ 2) / 2)`. -/
@[dlmf 18.17.E27]
theorem hermite_odd_sine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n + 1)) : ℝ) * Real.sin (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n + 1) * Real.exp (-(y ^ 2) / 2) := by
  set f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n + 1)) : ℝ) *
    Real.sin (x * y) with hf
  have heven : ∀ x, f |x| = f x := by
    intro x
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hf]
      simp only [hermite_aeval_neg, neg_mul, Real.sin_neg, neg_sq]
      rw [pow_succ (-1 : ℝ), pow_mul (-1 : ℝ), neg_one_sq, one_pow]
      ring
  have habs := integral_comp_abs (f := f)
  simp_rw [heven] at habs
  have hfull : ∫ x, f x = ∫ x : ℝ, Real.sin (y * x) * hermiteGauss (2 * n + 1) x := by
    congr 1; funext x
    simp only [hf, hermiteGauss, neg_div, mul_comm x y]
    ring
  rw [hfull, integral_sin_mul_hermiteGauss, mul_pow, pow_succ, pow_mul, I_sq] at habs
  have him : ((-1 : ℂ) ^ n * I * (y : ℂ) ^ (2 * n + 1)).im =
      (-1 : ℝ) ^ n * y ^ (2 * n + 1) := by
    rw [show (-1 : ℂ) ^ n * I * (y : ℂ) ^ (2 * n + 1) =
      (((-1 : ℝ) ^ n * y ^ (2 * n + 1) : ℝ) : ℂ) * I by push_cast; ring, Complex.mul_I_im,
      Complex.ofReal_re]
  rw [him] at habs
  rw [← sqrt_two_pi_div_two, neg_div]
  linarith

/-- The product formula for Mathlib's probabilists' Hermite normalization. -/
theorem hermite_linearization (m n : ℕ) (x : ℝ) :
    (aeval x (hermite m) : ℝ) * aeval x (hermite n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℝ) * n.choose k * k.factorial *
        aeval x (hermite (m + n - 2 * k)) := by
  let s := Real.sqrt 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 2 := by simp [s]
  have hscale (j : ℕ) : (aeval (x / s) (hermitePolyH j) : ℝ) =
      s ^ j * aeval x (hermite j) := by
    rw [aeval_hermitePolyH_eq_hermite]
    have hpow : (2 : ℝ) ^ (j / 2 : ℝ) = s ^ j := by
      rw [show s = (2 : ℝ) ^ (1 / 2 : ℝ) by dsimp [s]; rw [Real.sqrt_eq_rpow],
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hpow, show Real.sqrt 2 * (x / s) = x by dsimp [s]; field_simp]
  have hcast (j : ℕ) : (aeval ((x / s : ℝ) : ℂ) (hermitePolyH j) : ℂ) =
      ((aeval (x / s) (hermitePolyH j) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) (x / s) (hermitePolyH j)
  have hc := hermitePolyH_linearization m n ((x / s : ℝ) : ℂ)
  simp_rw [hcast] at hc
  have hr : (aeval (x / s) (hermitePolyH m) : ℝ) * aeval (x / s) (hermitePolyH n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℝ) * n.choose k * 2 ^ k * k.factorial *
        aeval (x / s) (hermitePolyH (m + n - 2 * k)) := by exact_mod_cast hc
  simp_rw [hscale] at hr
  have hpow (k : ℕ) (hk : k ∈ Finset.range (min m n + 1)) :
      (2 : ℝ) ^ k * s ^ (m + n - 2 * k) = s ^ (m + n) := by
    have hle : 2 * k ≤ m + n := by have := Finset.mem_range.mp hk; omega
    rw [← hs2, ← pow_mul, ← pow_add, Nat.add_sub_of_le hle]
  apply mul_left_cancel₀ (pow_ne_zero (m + n) hs.ne')
  calc
    _ = (s ^ m * (aeval x (hermite m) : ℝ)) * (s ^ n * aeval x (hermite n)) := by
      rw [pow_add]; ring
    _ = _ := hr
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have := hpow k hk
      linear_combination (m.choose k : ℝ) * n.choose k * k.factorial *
        (aeval x (hermite (m + n - 2 * k)) : ℝ) * this

/-- The finite contraction sum in a Hermite transform is a Laguerre polynomial. -/
theorem hermite_laguerrePolyL_sum (n l : ℕ) (u : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + l).choose k * k.factorial *
      (-1 : ℂ) ^ (n - k) * u ^ (2 * (n - k) + l) =
      n.factorial * u ^ l * laguerrePolyL l n (u ^ 2) := by
  have hl : ∀ k : ℕ, (l : ℂ) + 1 ≠ -k :=
    not_neg_nat_of_re_pos (by simp; positivity)
  rw [laguerrePolyL_eq_sum hl, Finset.mul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [show n + 1 - 1 - j = n - j by omega, Nat.sub_sub_self hjn]
  have hN : (n.choose (n - j) : ℂ) * (n - j).factorial * j.factorial = n.factorial := by
    exact_mod_cast (by simpa [Nat.sub_sub_self hjn] using
      Nat.choose_mul_factorial_mul_factorial (Nat.sub_le n j))
  have hL : ((n + l).choose (n - j) : ℂ) * (n - j).factorial * (l + j).factorial =
      (n + l).factorial := by
    exact_mod_cast (by simpa [show n + l - (n - j) = l + j by omega] using
      Nat.choose_mul_factorial_mul_factorial (show n - j ≤ n + l by omega))
  have hP : ((l + j).factorial : ℂ) * poch ((l : ℂ) + 1 + j) (n - j) = (n + l).factorial := by
    have he := factorial_mul_ascPochhammer ℂ (l + j) (n - j)
    simpa only [poch, Nat.add_sub_of_le (show j ≤ n + l by omega),
      show l + j + (n - j) = n + l by omega, Nat.cast_add,
      show (l : ℂ) + j + 1 = l + 1 + j by ring] using he
  have hcoeff : (n.choose (n - j) : ℂ) * (n + l).choose (n - j) * (n - j).factorial =
      n.factorial * (poch ((l : ℂ) + 1 + j) (n - j) /
        ((n - j).factorial * j.factorial : ℂ)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (n - j).factorial_ne_zero)
      (Nat.cast_ne_zero.mpr j.factorial_ne_zero))).mpr
    calc
      _ = ((n.choose (n - j) : ℂ) * (n - j).factorial * j.factorial) *
          (((n + l).choose (n - j) : ℂ) * (n - j).factorial) := by ring
      _ = n.factorial * poch ((l : ℂ) + 1 + j) (n - j) := by
        rw [hN]
        congr 1
        apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr (l + j).factorial_ne_zero)
        rw [hL]
        simpa [mul_comm] using hP.symm
  rw [hcoeff, neg_pow (u ^ 2), pow_add, pow_mul]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Set.Ioi 0, exp (-(x :
ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) * aeval (x : ℂ) (hermite (n + 2 * m)) * Real.cos
(x * y) = (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m) * exp (-(y
: ℂ) ^ 2 / 2) * laguerrePolyL (2 * m) n ((y : ℂ) ^ 2)`. -/
@[dlmf 18.17.E25]
theorem hermite_product_cosine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m)) * Real.cos (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerrePolyL (2 * m) n ((y : ℂ) ^ 2) := by
  have hcast (j : ℕ) (x : ℝ) : (aeval (x : ℂ) (hermite j) : ℂ) =
      ((aeval x (hermite j) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x (hermite j)
  have hexp (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) = (Real.exp (-(x ^ 2) / 2) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  let G (j : ℕ) (x : ℝ) : ℂ := exp (-(x : ℂ) ^ 2 / 2) *
    aeval (x : ℂ) (hermite j) * Real.cos (x * y)
  have hi (j : ℕ) : Integrable (G j) := by
    have ht := (integrable_hermiteGauss j).mul_bdd
      (by fun_prop : Continuous (fun x : ℝ => Real.cos (x * y))).aestronglyMeasurable
      (Eventually.of_forall fun x => show ‖Real.cos (x * y)‖ ≤ (1 : ℝ) by
        simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (x * y))
    apply ht.ofReal.congr
    filter_upwards [] with x
    dsimp only [G]
    rw [hexp, hcast]
    simp only [hermiteGauss, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, neg_div]
    ring_nf
  have hlin (x : ℝ) : (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m)) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
          aeval (x : ℂ) (hermite (n + (n + 2 * m) - 2 * k)) := by
    simp_rw [hcast]
    have hr := hermite_linearization n (n + 2 * m) x
    rw [min_eq_left (by omega)] at hr
    exact_mod_cast hr
  have he : (∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) *
      (aeval (x : ℂ) (hermite n) : ℂ) * aeval (x : ℂ) (hermite (n + 2 * m)) *
        Real.cos (x * y)) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
        ∫ x : ℝ in Set.Ioi 0, G (n + (n + 2 * m) - 2 * k) x := by
    have he (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
        aeval (x : ℂ) (hermite (n + 2 * m)) * Real.cos (x * y) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
          G (n + (n + 2 * m) - 2 * k) x := by
      rw [mul_assoc (exp _) _ _, hlin]
      simp only [Finset.mul_sum, Finset.sum_mul, G]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun k _ => (hi _).integrableOn.const_mul _)]
    simp_rw [integral_const_mul]
  have htrans (j : ℕ) : (∫ x : ℝ in Set.Ioi 0, G (2 * j) x) =
      (-1 : ℂ) ^ j * Real.sqrt (Real.pi / 2) * (y : ℂ) ^ (2 * j) *
        exp (-(y : ℂ) ^ 2 / 2) := by
    simp only [G, hexp, hcast, ← ofReal_mul, _root_.integral_complex_ofReal]
    rw [hermite_even_cosine_transform j y]
    push_cast
    ring
  rw [he]
  have hsum := hermite_laguerrePolyL_sum n (2 * m) (y : ℂ)
  calc
    _ = ((-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * exp (-(y : ℂ) ^ 2 / 2)) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
          (-1 : ℂ) ^ (n - k) * (y : ℂ) ^ (2 * (n - k) + 2 * m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [show n + (n + 2 * m) - 2 * k = 2 * (n - k + m) by omega,
        htrans, pow_add, show 2 * (n - k + m) = 2 * (n - k) + 2 * m by omega]
      ring
    _ = _ := by
      try simp only [← Nat.add_assoc] at hsum
      rw [hsum]
      push_cast
      ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Set.Ioi 0, exp (-(x :
ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) * aeval (x : ℂ) (hermite (n + 2 * m + 1)) *
Real.sin (x * y) = (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m +
1) * exp (-(y : ℂ) ^ 2 / 2) * laguerrePolyL (2 * m + 1) n ((y : ℂ) ^ 2)`. -/
@[dlmf 18.17.E26]
theorem hermite_product_sine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m + 1)) * Real.sin (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m + 1) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerrePolyL (2 * m + 1) n ((y : ℂ) ^ 2) := by
  have hcast (j : ℕ) (x : ℝ) : (aeval (x : ℂ) (hermite j) : ℂ) =
      ((aeval x (hermite j) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x (hermite j)
  have hexp (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) = (Real.exp (-(x ^ 2) / 2) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  let G (j : ℕ) (x : ℝ) : ℂ := exp (-(x : ℂ) ^ 2 / 2) *
    aeval (x : ℂ) (hermite j) * Real.sin (x * y)
  have hi (j : ℕ) : Integrable (G j) := by
    have ht := (integrable_hermiteGauss j).mul_bdd
      (by fun_prop : Continuous (fun x : ℝ => Real.sin (x * y))).aestronglyMeasurable
      (Eventually.of_forall fun x => show ‖Real.sin (x * y)‖ ≤ (1 : ℝ) by
        simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (x * y))
    apply ht.ofReal.congr
    filter_upwards [] with x
    dsimp only [G]
    rw [hexp, hcast]
    simp only [hermiteGauss, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, neg_div]
    ring_nf
  have hlin (x : ℝ) : (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m + 1)) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
          aeval (x : ℂ) (hermite (n + (n + 2 * m + 1) - 2 * k)) := by
    simp_rw [hcast]
    have hr := hermite_linearization n (n + 2 * m + 1) x
    rw [min_eq_left (by omega)] at hr
    exact_mod_cast hr
  have he : (∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) *
      (aeval (x : ℂ) (hermite n) : ℂ) * aeval (x : ℂ) (hermite (n + 2 * m + 1)) *
        Real.sin (x * y)) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
        ∫ x : ℝ in Set.Ioi 0, G (n + (n + 2 * m + 1) - 2 * k) x := by
    have he (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
        aeval (x : ℂ) (hermite (n + 2 * m + 1)) * Real.sin (x * y) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
          G (n + (n + 2 * m + 1) - 2 * k) x := by
      rw [mul_assoc (exp _) _ _, hlin]
      simp only [Finset.mul_sum, Finset.sum_mul, G]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun k _ => (hi _).integrableOn.const_mul _)]
    simp_rw [integral_const_mul]
  have htrans (j : ℕ) : (∫ x : ℝ in Set.Ioi 0, G (2 * j + 1) x) =
      (-1 : ℂ) ^ j * Real.sqrt (Real.pi / 2) * (y : ℂ) ^ (2 * j + 1) *
        exp (-(y : ℂ) ^ 2 / 2) := by
    simp only [G, hexp, hcast, ← ofReal_mul, _root_.integral_complex_ofReal]
    rw [hermite_odd_sine_transform j y]
    push_cast
    ring
  rw [he]
  have hsum := hermite_laguerrePolyL_sum n (2 * m + 1) (y : ℂ)
  calc
    _ = ((-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * exp (-(y : ℂ) ^ 2 / 2)) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
          (-1 : ℂ) ^ (n - k) * (y : ℂ) ^ (2 * (n - k) + 2 * m + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [show n + (n + 2 * m + 1) - 2 * k = 2 * (n - k + m) + 1 by omega,
        htrans, pow_add, show 2 * (n - k + m) + 1 = 2 * (n - k) + 2 * m + 1 by omega]
      ring
    _ = _ := by
      try simp only [← Nat.add_assoc] at hsum
      rw [hsum]
      push_cast
      ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (-1 : ℝ)..1, exp (-((x
: ℂ) + 1) * z) * jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) = (-1
: ℂ) ^ n * (2 : ℂ) ^ (α + β + n + 1 : ℂ) * Gamma (α + n + 1 : ℂ) * Gamma (β + n + 1 : ℂ) /
(Gamma (α + β + 2 * n + 2 : ℂ) * n.factorial) * z ^ n * kummerM (β + n + 1 : ℂ) (α + β + 2 * n
+ 2 : ℂ) (-2 * z)`. -/
@[dlmf 18.17.E33]
theorem jacobi_laplace_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (z : ℂ) :
    ∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * z) * jacobiPolyP α β n x *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) =
      (-1 : ℂ) ^ n * (2 : ℂ) ^ (α + β + n + 1 : ℂ) * Gamma (α + n + 1 : ℂ) *
      Gamma (β + n + 1 : ℂ) / (Gamma (α + β + 2 * n + 2 : ℂ) * n.factorial) *
      z ^ n * kummerM (β + n + 1 : ℂ) (α + β + 2 * n + 2 : ℂ) (-2 * z) := by
  convert jacobi_laplace_aux hα hβ n z using 1
  exact intervalIntegral.integral_congr fun x _ => by ring

section LaguerreProductLaplace

set_option maxHeartbeats 1000000

/-- Complex scaling of a finite Gamma moment. -/
theorem scaled_monomial_moment {α : ℝ} (hα : -1 < α) {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    IntegrableOn (fun x : ℝ => (w * x) ^ n * (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) (Set.Ioi 0) ∧
    (∫ x : ℝ in Set.Ioi 0, (w * x) ^ n * (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) =
      w ^ (-((α : ℂ) + 1)) * Gamma ((α : ℂ) + n + 1) := by
  have hs : 0 < ((α : ℂ) + n + 1).re := by simp; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hw0 : w ≠ 0 := ne_zero_of_re_pos hw
  have he : ∀ x : ℝ, 0 < x → (w * x) ^ n * (x : ℂ) ^ (α : ℂ) * exp (-(w * x)) =
      w ^ n * ((x : ℂ) ^ (((α : ℂ) + n + 1) - 1) * exp (-(w * x))) := by
    intro x hx
    rw [mul_pow, add_sub_cancel_right, cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_natCast]
    ring
  have hi := (integrableOn_cpow_mul_cexp_neg hs hw).const_mul (w ^ n)
  refine ⟨hi.congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => (he x hx).symm)), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi hs hw]
  have hp : w ^ n * w ^ (-((α : ℂ) + n + 1)) = w ^ (-((α : ℂ) + 1)) := by
    rw [← cpow_natCast, ← cpow_add _ _ hw0]
    congr 1
    ring
  linear_combination Gamma ((α : ℂ) + n + 1) * hp

/-- A polynomial's scaled Laplace integral differs from its Gamma integral by one power. -/
theorem scaled_polynomial_moment {α : ℝ} (hα : -1 < α) {w : ℂ} (hw : 0 < w.re) (p : ℂ[X]) :
    IntegrableOn (fun x : ℝ => p.eval (w * x) * (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) (Set.Ioi 0) ∧
    (∫ x : ℝ in Set.Ioi 0, p.eval (w * x) * (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) =
      w ^ (-((α : ℂ) + 1)) *
      ∫ x : ℝ in Set.Ioi 0, p.eval (x : ℂ) * (x : ℂ) ^ (α : ℂ) * exp (-x) := by
  have hi1 : ∀ q : ℂ[X], IntegrableOn
      (fun x : ℝ => q.eval (x : ℂ) * (x : ℂ) ^ (α : ℂ) * exp (-x)) (Set.Ioi 0) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      convert hp.add hq using 1
      ext x
      simp only [Pi.add_apply, eval_add]
      ring
    | monomial n c =>
      simpa only [IntegrableOn, eval_monomial, mul_assoc] using ((laguerrePolyL_weight_moment hα n).1.const_mul c)
  -- Mathlib's monomial induction reduces complex scaling to the Gamma moments.
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨?_, ?_⟩
    · convert hp.1.add hq.1 using 1
      ext x
      simp only [Pi.add_apply, eval_add]
      ring
    · simp only [eval_add, add_mul]
      rw [integral_add hp.1 hq.1, integral_add (hi1 p) (hi1 q), hp.2, hq.2]
      ring
  | monomial n c =>
    refine ⟨by simpa only [IntegrableOn, eval_monomial, mul_assoc] using (scaled_monomial_moment hα hw n).1.const_mul c, ?_⟩
    simp only [eval_monomial, mul_assoc]
    rw [integral_const_mul, integral_const_mul]
    have h1 := (scaled_monomial_moment hα hw n).2
    have h2 := (laguerrePolyL_weight_moment hα n).2
    simp only [mul_assoc] at h1 h2
    rw [h1, h2]
    ring

/-- The finite Laguerre expansion is a complex polynomial. -/
theorem laguerre_exists_poly (α : ℂ) (n : ℕ) :
    ∃ p : ℂ[X], ∀ x, p.eval x = laguerrePolyL α n x := by
  refine ⟨∑ j ∈ Finset.range (n + 1), monomial j
    (poch (α + 1) n / n.factorial * kummerMCoeff (-(n : ℂ)) (α + 1) j), ?_⟩
  intro x
  simp [eval_finsetSum, laguerrePolyL_eq_sum_coeff]

/-- Scaled Laguerre orthogonality for a complex Laplace rate. -/
theorem scaled_laguerre_inner {α : ℝ} (hα : -1 < α) {w : ℂ} (hw : 0 < w.re) (m n : ℕ) :
    IntegrableOn (fun x : ℝ => laguerrePolyL α m (w * x) * laguerrePolyL α n (w * x) *
      (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) (Set.Ioi 0) ∧
    (∫ x : ℝ in Set.Ioi 0, laguerrePolyL α m (w * x) * laguerrePolyL α n (w * x) *
      (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) =
      if m = n then w ^ (-((α : ℂ) + 1)) * Gamma (n + (α : ℂ) + 1) / n ! else 0 := by
  obtain ⟨p, hp⟩ := laguerre_exists_poly α m
  obtain ⟨q, hq⟩ := laguerre_exists_poly α n
  have h := scaled_polynomial_moment hα hw (p * q)
  simp only [eval_mul, hp, hq] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  split_ifs with he
  · subst m
    have hn := laguerrePolyL_norm hα n
    have heq : (∫ x : ℝ in Set.Ioi 0, laguerrePolyL α n x * laguerrePolyL α n x *
        (x : ℂ) ^ (α : ℂ) * exp (-x)) = Gamma (n + (α : ℂ) + 1) / n ! := by
      convert hn using 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    rw [heq]; ring
  · rw [laguerrePolyL_orthogonal hα he, mul_zero]

/-- Finite change-of-scale coefficient for the Laguerre basis. -/
def laguerreScaleCoeff (α w : ℂ) (n k : ℕ) : ℂ :=
  laguerrePolyL α n 0 * (n.choose k : ℂ) * (w⁻¹) ^ k * (1 - w⁻¹) ^ (n - k) /
    laguerrePolyL α k 0

/-- Expansion in the Laguerre basis evaluated at a scaled argument. -/
theorem laguerre_scale_sum {α w : ℂ} (hα : -1 < α.re) (hw : w ≠ 0) (n : ℕ) (x : ℂ) :
    laguerrePolyL α n x = ∑ k ∈ Finset.range (n + 1),
      laguerreScaleCoeff α w n k * laguerrePolyL α k (w * x) := by
  have he : laguerrePolyL α n 0 ≠ 0 := by
    rw [laguerrePolyL_at_zero]
    exact div_ne_zero (poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n)
      (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have h := laguerrePolyL_multiplication hα w⁻¹ (w * x) n
  rw [inv_mul_cancel_left₀ hw] at h
  rw [div_eq_iff he] at h
  rw [h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [laguerreScaleCoeff]
  ring

/-- Orthogonality contracts the two finite change-of-scale expansions. -/
theorem laguerre_product_contraction {α : ℝ} (hα : -1 < α) {w : ℂ} (hw : 0 < w.re) (m n : ℕ) :
    (∫ x : ℝ in Set.Ioi 0, laguerrePolyL α m x * laguerrePolyL α n x *
      (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) =
      ∑ k ∈ Finset.range (m + 1), laguerreScaleCoeff α w m k * laguerreScaleCoeff α w n k *
        (w ^ (-((α : ℂ) + 1)) * Gamma (k + (α : ℂ) + 1) / k !) := by
  have hw0 := ne_zero_of_re_pos hw
  have heq : (fun x : ℝ => laguerrePolyL α m x * laguerrePolyL α n x *
      (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) = fun x : ℝ =>
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (laguerreScaleCoeff α w m i * laguerreScaleCoeff α w n j) *
        (laguerrePolyL α i (w * x) * laguerrePolyL α j (w * x) *
          (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) := by
    funext x
    conv_lhs => arg 1; arg 1; arg 1; rw [laguerre_scale_sum (by simpa using hα) hw0 m]
    conv_lhs => arg 1; arg 1; arg 2; rw [laguerre_scale_sum (by simpa using hα) hw0 n]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (scaled_laguerre_inner hα hw i j).1.const_mul _]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ => (scaled_laguerre_inner hα hw i j).1.const_mul _]
  simp only [integral_const_mul]
  simp_rw [(scaled_laguerre_inner hα hw i _).2]
  by_cases hi : i ∈ Finset.range (n + 1)
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      rw [ite_eq_right (Ne.symm hji), mul_zero]
    · exact fun h => (h hi).elim
  · have hn : n < i := by simpa using hi
    have hc : laguerreScaleCoeff α w n i = 0 := by
      simp [laguerreScaleCoeff, Nat.choose_eq_zero_of_lt hn]
    rw [hc, mul_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by intro h; subst j; exact hi hj), mul_zero]

/-- Terminating Gauss coefficients in binomial form. -/
theorem gauss_neg_nat_choose (m n k : ℕ) (a : ℂ) :
    gaussHGCoeff (-(m : ℂ)) (-(n : ℂ)) a k =
      (m.choose k : ℂ) * (n.choose k : ℂ) * k ! / poch a k := by
  simp only [gaussHGCoeff, poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hs : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  by_cases hp : poch a k = 0
  · simp [hp]
  · field_simp
    ring_nf at hs ⊢
    rw [hs]
    ring

/-- The elementary power cancellation in a Laguerre change of scale. -/
theorem laguerre_scale_power {z : ℂ} (hz : z ≠ 0) (hw : z + 1 ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    ((z + 1)⁻¹) ^ k * (1 - (z + 1)⁻¹) ^ (n - k) =
      z ^ n / (z + 1) ^ n / z ^ k := by
  have he : 1 - (z + 1)⁻¹ = z / (z + 1) := by field_simp; ring
  rw [he, div_pow, pow_sub₀ z hz hk, pow_sub₀ (z + 1) hw hk, inv_pow]
  field_simp

/-- The diagonal contraction has exactly the terminating Gauss coefficients. -/
theorem laguerre_product_contraction_term {α : ℝ} (hα : -1 < α) {z : ℂ}
    (hz : z ≠ 0) (hw : z + 1 ≠ 0) {m n k : ℕ} (hk : k ≤ m) :
    laguerreScaleCoeff α (z + 1) m k * laguerreScaleCoeff α (z + 1) n k *
      ((z + 1) ^ (-((α : ℂ) + 1)) * Gamma (k + (α : ℂ) + 1) / k !) =
    (Gamma (α + m + 1 : ℂ) * Gamma (α + n + 1 : ℂ) /
      (Gamma (α + 1 : ℂ) * m ! * n !) * z ^ (m + n) /
      (z + 1) ^ (α + m + n + 1 : ℂ)) *
      (gaussHGCoeff (-(m : ℂ)) (-(n : ℂ)) (α + 1) k * (z⁻¹ ^ 2) ^ k) := by
  by_cases hkn : k ≤ n
  · have hA : 0 < ((α : ℂ) + 1).re := by simp; linarith
    have hP (j : ℕ) : poch ((α : ℂ) + 1) j ≠ 0 :=
      poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hA) j
    have hG := Gamma_ne_zero_of_re_pos hA
    have hF (j : ℕ) : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hgamma (j : ℕ) : Gamma ((α : ℂ) + j + 1) = poch ((α : ℂ) + 1) j * Gamma ((α : ℂ) + 1) := by
      rw [show (α : ℂ) + j + 1 = ((α : ℂ) + 1) + j by ring]
      exact Gamma_add_nat_eq_poch_mul_Gamma hA j
    have hgk : Gamma (k + (α : ℂ) + 1) = poch ((α : ℂ) + 1) k * Gamma ((α : ℂ) + 1) := by
      rw [add_comm (k : ℂ) (α : ℂ)]; exact hgamma k
    have hwP : (z + 1) ^ ((α : ℂ) + 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hw)
    have he : (z + 1) ^ (α + m + n + 1 : ℂ) =
        (z + 1) ^ ((α : ℂ) + 1) * (z + 1) ^ m * (z + 1) ^ n := by
      rw [show (α : ℂ) + m + n + 1 = (((α : ℂ) + 1) + m) + n by ring,
        cpow_add _ _ hw, cpow_add _ _ hw, cpow_natCast, cpow_natCast]
    have hd (j : ℕ) (hkj : k ≤ j) : laguerreScaleCoeff α (z + 1) j k =
        (poch ((α : ℂ) + 1) j / j !) * (j.choose k : ℂ) *
          (z ^ j / (z + 1) ^ j / z ^ k) / (poch ((α : ℂ) + 1) k / k !) := by
      unfold laguerreScaleCoeff
      rw [laguerrePolyL_at_zero, laguerrePolyL_at_zero]
      rw [show (poch ((α : ℂ) + 1) j / j ! * (j.choose k : ℂ) * ((z + 1)⁻¹) ^ k *
          (1 - (z + 1)⁻¹) ^ (j - k)) =
          (poch ((α : ℂ) + 1) j / j ! * (j.choose k : ℂ)) *
          (((z + 1)⁻¹) ^ k * (1 - (z + 1)⁻¹) ^ (j - k)) by ring,
        laguerre_scale_power hz hw hkj]
    rw [hd m hk, hd n hkn, hgk, hgamma m, hgamma n, he, gauss_neg_nat_choose,
      cpow_neg, pow_add, ← pow_mul, mul_comm 2 k, pow_mul, inv_pow]
    field_simp

  · have hnk : n < k := by omega
    rw [gauss_neg_nat_choose, Nat.choose_eq_zero_of_lt hnk]
    simp [laguerreScaleCoeff, Nat.choose_eq_zero_of_lt hnk]

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Set.Ioi 0, exp (-x *
z) * laguerrePolyL α m x * laguerrePolyL α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) = Gamma (α + m +
1 : ℂ) * Gamma (α + n + 1 : ℂ) / (Gamma (α + 1 : ℂ) * m.factorial * n.factorial) * z ^ (m + n)
/ (z + 1) ^ (α + m + n + 1 : ℂ) * ₂F₁ (-(m : ℂ)) (-(n : ℂ)) (α + 1 : ℂ) (z⁻¹ ^ 2)`. -/
@[dlmf 18.17.E34_5]
theorem laguerrePolyL_product_laplace_transform {α : ℝ} (hα : -1 < α) (m n : ℕ) {z : ℂ}
    (hz : -1 < z.re) (hz0 : z ≠ 0) :
    ∫ x : ℝ in Set.Ioi 0,
        exp (-x * z) * laguerrePolyL α m x * laguerrePolyL α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (α + m + 1 : ℂ) * Gamma (α + n + 1 : ℂ) /
      (Gamma (α + 1 : ℂ) * m.factorial * n.factorial) * z ^ (m + n) /
      (z + 1) ^ (α + m + n + 1 : ℂ) * ₂F₁ (-(m : ℂ)) (-(n : ℂ)) (α + 1 : ℂ) (z⁻¹ ^ 2) := by
  have hw : 0 < (z + 1).re := by simp; linarith
  have heq : (∫ x : ℝ in Set.Ioi 0,
        exp (-x * z) * laguerrePolyL α m x * laguerrePolyL α n x * exp (-x) * (x : ℂ) ^ (α : ℂ)) =
      ∫ x : ℝ in Set.Ioi 0, laguerrePolyL α m x * laguerrePolyL α n x *
        (x : ℂ) ^ (α : ℂ) * exp (-((z + 1) * x)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [show -((z + 1) * (x : ℂ)) = -x * z + -x by ring, exp_add]
      ring
  rw [heq, laguerre_product_contraction hα hw,
    ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact laguerre_product_contraction_term hα hz0 (ne_zero_of_re_pos hw)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

end LaguerreProductLaplace

/-- Corrected finite-sum form of DLMF 18.17.41 (checked 2026-09-16).
The displayed DLMF formula is incorrect: at `n = 0` its power `a^(-n-2)`
would give `Γ(z)/a²`, whereas the integral is `Γ(z)/a^z`.
The terminating ₂F₂ denominator parameters also require a shift: they should be
`(1-z-n)/2` and `(2-z-n)/2`. This sum avoids their removable singularities. -/
@[dlmf 18.17.E41]
theorem hermite_mellin_laplace_transform {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-a * x) * (aeval (x : ℂ) (hermite n) : ℂ) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ Finset.range (n / 2 + 1), (-1 : ℂ) ^ k * n.factorial /
        (2 ^ k * (k.factorial : ℂ) * (n - 2 * k).factorial) *
        Gamma (z + (n - 2 * k : ℕ)) / (a : ℂ) ^ (z + (n - 2 * k : ℕ)) := by
  simp_rw [hermite_finite_sum]
  exact integral_finite_sum_mellin_laplace ha hz _ _ (fun k => n - 2 * k)

end DLMF.OrthogonalPolynomials
end
end
