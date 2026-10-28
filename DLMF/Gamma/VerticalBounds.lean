/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Products
public import DLMF.Gamma.SpecialValues

/-!
# Bounds for the Gamma function on vertical lines

From the product `|Γ(x)/Γ(x+iy)|² = ∏ₖ (1 + y²/(x+k)²)` (DLMF 5.8.3) and its exact values
`sinh(πy)/(πy)` at `x = 1` and `cosh(πy)` at `x = 1/2` (DLMF 5.4.3–5.4.4) we obtain

* `exists_norm_Gamma_le`: `|Γ(x+iy)| ≤ C (1+|y|)^K e^{-π|y|/2}` for fixed `x > 0`;
* `exists_norm_recip_Gamma_le`: `|1/Γ(x+iy)| ≤ C (1+|y|)^K e^{π|y|/2}`, uniformly for `x` in a
  bounded interval.

These are the estimates needed for Mellin–Barnes integrals.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Topology Real

noncomputable section

namespace DLMF.Gamma

/-- The product `P(x,y) = ∏ₖ (1 + y²/(x+k)²)` of DLMF 5.8.3. -/
def gammaVertProd (x y : ℝ) : ℝ := ∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2)

/-- The partial products `∏_{k<n} (1 + y²/(x + k)²)` tend to `gammaVertProd x y`. -/
theorem tendsto_prod_gammaVertProd (x y : ℝ) :
    Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, (1 + y ^ 2 / (x + k) ^ 2)) atTop
      (𝓝 (gammaVertProd x y)) :=
  (multipliable_one_add_sq_div_add_sq x y).hasProd.tendsto_prod_nat

/-- `gammaVertProd x y ≥ 1`. -/
theorem one_le_gammaVertProd (x y : ℝ) : 1 ≤ gammaVertProd x y :=
  ge_of_tendsto' (tendsto_prod_gammaVertProd x y) fun n =>
    Finset.one_le_prod₀ fun k _ => le_add_of_nonneg_right (by positivity)

/-- The product decreases in `x > 0`. -/
theorem gammaVertProd_anti {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (y : ℝ) :
    gammaVertProd x' y ≤ gammaVertProd x y := by
  refine le_of_tendsto_of_tendsto' (tendsto_prod_gammaVertProd x' y)
    (tendsto_prod_gammaVertProd x y) fun n => ?_
  refine Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
  have h1 : 0 < x + k := by positivity
  gcongr

/-- For `x > 0`, `|Γ(x + iy)|² = Γ(x)² / ∏ₖ (1 + y²/(x + k)²)`. -/
theorem norm_Gamma_sq_eq {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖Complex.Gamma (x + I * y)‖ ^ 2 = Real.Gamma x ^ 2 / gammaVertProd x y := by
  have hxk : ∀ k : ℕ, (x : ℂ) ≠ -k := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h := Gamma_div_Gamma_add_mul_I_sq (y := y) hxk
  have hne : Complex.Gamma (x + I * y) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hx])
  rw [gammaVertProd, ← h, norm_div, div_pow, norm_real, Real.norm_of_nonneg
    (Real.Gamma_pos_of_pos hx).le]
  have : ‖Complex.Gamma (x + I * y)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  field_simp

/-- `∏ₖ (1 + y²/(1 + k)²) = sinh(π y)/(π y)` for `y ≠ 0`. -/
theorem gammaVertProd_one {y : ℝ} (hy : y ≠ 0) :
    gammaVertProd 1 y = Real.sinh (π * y) / (π * y) := by
  have h := norm_Gamma_sq_eq one_pos y
  rw [Real.Gamma_one, one_pow] at h
  have hI : (I * (y : ℂ)) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hy)
  have hG : Complex.Gamma ((1 : ℝ) + I * y) = I * y * Complex.Gamma (I * y) := by
    rw [ofReal_one, add_comm, Complex.Gamma_add_one _ hI]
  rw [hG, norm_mul, norm_mul, norm_I, one_mul, norm_real, norm_Gamma_mul_I y hy, mul_pow,
    Real.sq_sqrt, Real.norm_eq_abs, sq_abs] at h
  · have hs : 0 < y * Real.sinh (π * y) := by
      rcases lt_or_gt_of_ne hy with h' | h'
      · exact mul_pos_of_neg_of_neg h'
          (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos h'))
      · exact mul_pos h' (Real.sinh_pos_iff.mpr (by positivity))
    have hP := one_le_gammaVertProd 1 y
    have hP0 : gammaVertProd 1 y ≠ 0 := (by linarith : (0 : ℝ) < _).ne'
    field_simp at h
    have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    field_simp
    rw [mul_comm π y, ← h]; ring
  · rcases lt_or_gt_of_ne hy with h' | h'
    · exact (div_pos Real.pi_pos (mul_pos_of_neg_of_neg h'
        (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos h')))).le
    · exact (div_pos Real.pi_pos (mul_pos h' (Real.sinh_pos_iff.mpr (by positivity)))).le

/-- `∏ₖ (1 + y²/(1/2 + k)²) = cosh(π y)`. -/
theorem gammaVertProd_half (y : ℝ) : gammaVertProd (1 / 2) y = Real.cosh (π * y) := by
  have h := norm_Gamma_sq_eq (one_half_pos) y
  rw [show (((1 / 2 : ℝ)) : ℂ) = 1 / 2 by push_cast; ring, (Gamma_half_add_mul_I y).2,
    Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le] at h
  · have hP := one_le_gammaVertProd (1 / 2) y
    have hc := Real.cosh_pos (π * y)
    field_simp at h
    nlinarith [h]

/-- `gammaVertProd x 0 = 1`. -/
theorem gammaVertProd_zero (x : ℝ) : gammaVertProd x 0 = 1 := by
  simp [gammaVertProd]

/-- `gammaVertProd x y` is even in `y`. -/
theorem gammaVertProd_neg (x y : ℝ) : gammaVertProd x (-y) = gammaVertProd x y := by
  simp [gammaVertProd]

/-- `1/P(1,y) = π|y|/sinh(π|y|) ≤ 2(1+π|y|) e^{-π|y|}`. -/
theorem recip_gammaVertProd_one_le (y : ℝ) :
    (gammaVertProd 1 y)⁻¹ ≤ 2 * (1 + π * |y|) * Real.exp (-(π * |y|)) := by
  by_cases hy : y = 0
  · subst hy; simp [gammaVertProd_zero]
  have hP : gammaVertProd 1 y = gammaVertProd 1 |y| := by
    rcases abs_choice y with h | h <;> rw [h]; rw [gammaVertProd_neg]
  have hay : 0 < |y| := abs_pos.mpr hy
  rw [hP, gammaVertProd_one hay.ne']
  set t := π * |y| with ht
  have htp : 0 < t := by positivity
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr htp
  rw [inv_div, div_le_iff₀ hs, Real.sinh_eq]
  have hu := Real.exp_pos t
  have h2 : 1 + 2 * t ≤ Real.exp t ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast
    linarith [Real.add_one_le_exp (2 * t)]
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have k1 : (1 + t) * Real.exp (-t) ^ 2 ≤ Real.exp t ^ 2 * Real.exp (-t) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have k2 : Real.exp t ^ 2 * Real.exp (-t) ^ 2 = 1 := by
    rw [← mul_pow, mul_comm, he, one_pow]
  nlinarith [k1, k2, he]

/-- For `0 < x ≤ 1`, `|Γ(x + iy)|² ≤ Γ(x)² · 2(1 + π|y|) e^(-π|y|)`. -/
theorem norm_Gamma_sq_le_of_le_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (y : ℝ) :
    ‖Complex.Gamma (x + I * y)‖ ^ 2 ≤
      Real.Gamma x ^ 2 * (2 * (1 + π * |y|) * Real.exp (-(π * |y|))) := by
  rw [norm_Gamma_sq_eq hx]
  have hP1 := one_le_gammaVertProd 1 y
  have hPx := gammaVertProd_anti hx hx1 y
  calc Real.Gamma x ^ 2 / gammaVertProd x y ≤ Real.Gamma x ^ 2 / gammaVertProd 1 y :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hPx
    _ = Real.Gamma x ^ 2 * (gammaVertProd 1 y)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (recip_gammaVertProd_one_le y) (by positivity)

/-- **Vertical decay of `Γ`**: for fixed `x > 0`, `|Γ(x+iy)| ≤ C (1+|y|)^K e^{-π|y|/2}`. -/
theorem exists_norm_Gamma_le {x : ℝ} (hx : 0 < x) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖Complex.Gamma (x + I * y)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  suffices h : ∀ n : ℕ, ∀ x : ℝ, 0 < x → x ≤ n + 1 → ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖Complex.Gamma (x + I * y)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) by
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact h n x hx (by linarith)
  intro n
  induction n with
  | zero =>
    intro x hx hx1
    refine ⟨2 * π * Real.Gamma x, 1, fun y => ?_⟩
    have h := norm_Gamma_sq_le_of_le_one hx (by simpa using hx1) y
    have hG := Real.Gamma_pos_of_pos hx
    have hE : Real.exp (-(π * |y|)) = Real.exp (-(π * |y|) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [hE] at h
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h.trans ?_)
    have hy := abs_nonneg y
    have hpi := Real.two_le_pi
    have : 2 * (1 + π * |y|) ≤ (2 * π * (1 + |y|)) ^ 2 := by nlinarith
    calc Real.Gamma x ^ 2 * (2 * (1 + π * |y|) * Real.exp (-(π * |y|) / 2) ^ 2)
        ≤ Real.Gamma x ^ 2 * ((2 * π * (1 + |y|)) ^ 2 * Real.exp (-(π * |y|) / 2) ^ 2) := by
          gcongr
      _ = _ := by ring
  | succ n ih =>
    intro x hx hxn
    by_cases hx1 : x ≤ n + 1
    · exact ih x hx hx1
    push Not at hx1
    obtain ⟨C, K, hC⟩ := ih (x - 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (by push_cast at hxn; linarith)
    refine ⟨x * C, K + 1, fun y => ?_⟩
    have hs : ((x - 1 : ℝ) : ℂ) + I * y ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hG := Complex.Gamma_add_one _ hs
    rw [show ((x - 1 : ℝ) : ℂ) + I * y + 1 = x + I * y by push_cast; ring] at hG
    rw [hG, norm_mul]
    have hn1 : ‖((x - 1 : ℝ) : ℂ) + I * y‖ ≤ x * (1 + |y|) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_real, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]
      have : (1 : ℝ) ≤ x := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith [abs_nonneg y]
    have h2 := hC y
    have hC0 : 0 ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) :=
      (norm_nonneg _).trans h2
    calc ‖((x - 1 : ℝ) : ℂ) + I * y‖ * ‖Complex.Gamma (((x - 1 : ℝ) : ℂ) + I * y)‖
        ≤ (x * (1 + |y|)) * (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) :=
          mul_le_mul hn1 h2 (norm_nonneg _) (by nlinarith [abs_nonneg y])
      _ = _ := by ring

/-- `cosh t ≤ e^|t|`. -/
theorem cosh_le_exp_abs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_le_exp.mpr (le_abs_self t)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs t)
  linarith

/-- For `x ≥ 1/2`: `|1/Γ(x+iy)|² = P(x,y)/Γ(x)² ≤ cosh(πy)/Γ(x)²`. -/
theorem norm_recip_Gamma_sq_le {x : ℝ} (hx : 1 / 2 ≤ x) (y : ℝ) :
    ‖(Complex.Gamma (x + I * y))⁻¹‖ ^ 2 ≤ Real.exp (π * |y|) / Real.Gamma x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hG := Real.Gamma_pos_of_pos hx0
  have hP := gammaVertProd_anti (by norm_num : (0 : ℝ) < 1 / 2) hx y
  rw [gammaVertProd_half] at hP
  have hP1 := one_le_gammaVertProd x y
  rw [norm_inv, inv_pow, norm_Gamma_sq_eq hx0, inv_div]
  have hc : Real.cosh (π * y) ≤ Real.exp (π * |y|) := by
    have := cosh_le_exp_abs (π * y); rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  gcongr
  linarith

/-- **Growth of `1/Γ` on vertical lines**, uniformly for `x` in a bounded interval:
`|1/Γ(x+iy)| ≤ C (1+|y|)^K e^{π|y|/2}`. -/
theorem exists_norm_recip_Gamma_le (X : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ x ∈ Icc (-X) X, ∀ y : ℝ,
      ‖(Complex.Gamma (x + I * y))⁻¹‖ ≤ C * (1 + |y|) ^ K * Real.exp (π * |y| / 2) := by
  set B : ℝ := max X 2 with hB
  have hB2 : 2 ≤ B := le_max_right _ _
  -- the minimum of `Γ` on `[1/2, B]`
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc (1 / 2 : ℝ) B, m ≤ Real.Gamma x := by
    have hcont : ContinuousOn Real.Gamma (Icc (1 / 2 : ℝ) B) := fun x hx =>
      (Real.differentiableAt_Gamma fun k h => by
        have := hx.1; rw [h] at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        ).continuousAt.continuousWithinAt
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (by linarith)) hcont
    exact ⟨Real.Gamma x₀, Real.Gamma_pos_of_pos (by linarith [hx₀.1]), fun x hx => hmin hx⟩
  have base : ∀ x ∈ Icc (1 / 2 : ℝ) B, ∀ y : ℝ,
      ‖(Complex.Gamma (x + I * y))⁻¹‖ ≤ m⁻¹ * Real.exp (π * |y| / 2) := by
    intro x hx y
    have h := norm_recip_Gamma_sq_le hx.1 y
    have hGm := hmin x hx
    have hE : Real.exp (π * |y|) = Real.exp (π * |y| / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h.trans ?_)
    rw [hE, mul_pow, div_eq_mul_inv, mul_comm, inv_pow]
    gcongr
  have step : ∀ n : ℕ, ∀ x ∈ Icc (1 / 2 - n : ℝ) B, ∀ y : ℝ,
      ‖(Complex.Gamma (x + I * y))⁻¹‖ ≤
        m⁻¹ * (B + n) ^ n * (1 + |y|) ^ n * Real.exp (π * |y| / 2) := by
    intro n
    induction n with
    | zero => intro x hx y; simpa using base x (by simpa using hx) y
    | succ n ih =>
      intro x hx y
      by_cases hx' : 1 / 2 - (n : ℝ) ≤ x
      · refine (ih x ⟨hx', hx.2⟩ y).trans ?_
        have h1 : (B + n) ^ n ≤ (B + (n + 1 : ℕ)) ^ (n + 1) := by
          push_cast
          calc (B + n) ^ n ≤ (B + (n + 1)) ^ n := by gcongr; linarith
            _ ≤ (B + (n + 1)) ^ (n + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ n)
        have h2 : (1 + |y|) ^ n ≤ (1 + |y|) ^ (n + 1) :=
          pow_le_pow_right₀ (by linarith [abs_nonneg y]) (Nat.le_succ n)
        have hm0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
        calc m⁻¹ * (B + n) ^ n * (1 + |y|) ^ n * Real.exp (π * |y| / 2)
            ≤ m⁻¹ * (B + (n + 1 : ℕ)) ^ (n + 1) * (1 + |y|) ^ (n + 1) *
                Real.exp (π * |y| / 2) := by gcongr
          _ = _ := by push_cast; ring
      push Not at hx'
      have hx1 : x + 1 ∈ Icc (1 / 2 - n : ℝ) B := by
        constructor
        · push_cast at hx; linarith [hx.1]
        · linarith
      have h := ih (x + 1) hx1 y
      by_cases hw : (x : ℂ) + I * y = 0
      · rw [hw, Complex.Gamma_zero, inv_zero, norm_zero]
        have hm0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
        have : 0 ≤ B + (n + 1 : ℕ) := by positivity
        positivity
      have hG := Complex.Gamma_add_one _ hw
      rw [show (x : ℂ) + I * y + 1 = ((x + 1 : ℝ) : ℂ) + I * y by push_cast; ring] at hG
      have hinv : (Complex.Gamma (x + I * y))⁻¹ =
          ((x : ℂ) + I * y) * (Complex.Gamma (((x + 1 : ℝ) : ℂ) + I * y))⁻¹ := by
        rw [hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hw, one_mul]
      rw [hinv, norm_mul]
      have hn1 : ‖(x : ℂ) + I * y‖ ≤ (B + (n + 1 : ℕ)) * (1 + |y|) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_real, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        have hxa : |x| ≤ B + (n + 1 : ℕ) := by
          rw [abs_le]; push_cast at hx ⊢; constructor <;> linarith [hx.1, hx.2]
        have : (1 : ℝ) ≤ B + (n + 1 : ℕ) := by push_cast; linarith
        nlinarith [abs_nonneg y, abs_nonneg x]
      have hB' : (B + n) ^ n ≤ (B + (n + 1 : ℕ)) ^ n := by gcongr; linarith
      have hm0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
      calc ‖(x : ℂ) + I * y‖ * ‖(Complex.Gamma (((x + 1 : ℝ) : ℂ) + I * y))⁻¹‖
          ≤ ((B + (n + 1 : ℕ)) * (1 + |y|)) *
              (m⁻¹ * (B + n) ^ n * (1 + |y|) ^ n * Real.exp (π * |y| / 2)) :=
            mul_le_mul hn1 h (norm_nonneg _) (by positivity)
        _ ≤ ((B + (n + 1 : ℕ)) * (1 + |y|)) *
              (m⁻¹ * (B + (n + 1 : ℕ)) ^ n * (1 + |y|) ^ n * Real.exp (π * |y| / 2)) := by
            gcongr
        _ = _ := by ring
  obtain ⟨n, hn⟩ := exists_nat_ge (X + 1)
  refine ⟨m⁻¹ * (B + n) ^ n, n, fun x hx y => ?_⟩
  refine (step n x ⟨by linarith [hx.1], hx.2.trans (le_max_left _ _)⟩ y).trans (le_of_eq ?_)
  ring

/-- `e^(-b|y|)` is integrable on `ℝ` for `b > 0`. -/
theorem integrable_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : ℝ => Real.exp (-(b * |y|))) := by
  have h1 : IntegrableOn (fun y : ℝ => Real.exp (-(b * |y|))) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hb).congr_fun (fun y hy => by
      simp [abs_of_pos (mem_Ioi.mp hy)]) measurableSet_Ioi
  have h2 : IntegrableOn (fun y : ℝ => Real.exp (-(b * |y|))) (Iic 0) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi] at h1
    have := h1.comp_neg
    simpa [abs_neg] using this
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact h2.union h1

/-- Polynomial times `e^{-c|y|}` is integrable on `ℝ`. -/
theorem integrable_one_add_abs_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) (K : ℕ) :
    Integrable (fun y : ℝ => (1 + |y|) ^ K * Real.exp (-(c * |y|))) := by
  -- `(1+t)^K e^{-ct/2}` is bounded on `t ≥ 0`
  have hlim : Tendsto (fun t : ℝ => (1 + t) ^ K * Real.exp (-(c / 2 * t))) atTop (𝓝 0) := by
    have hu : Tendsto (fun t : ℝ => c / 2 * (1 + t)) atTop atTop :=
      (tendsto_atTop_add_const_left _ 1 tendsto_id).const_mul_atTop (half_pos hc)
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp hu
    have h' := h.const_mul ((2 / c) ^ K * Real.exp (c / 2))
    rw [mul_zero] at h'
    refine h'.congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply]
    have hc' : c ≠ 0 := hc.ne'
    rw [show -(c / 2 * (1 + t)) = -(c / 2 * t) + -(c / 2) by ring, Real.exp_add, mul_pow]
    have h1 : Real.exp (c / 2) * Real.exp (-(c / 2)) = 1 := by rw [← Real.exp_add]; simp
    have h2 : (2 / c) ^ K * (c / 2) ^ K = 1 := by rw [← mul_pow]; field_simp; simp
    linear_combination ((1 + t) ^ K * Real.exp (-(c / 2 * t))) *
      ((2 / c) ^ K * (c / 2) ^ K * h1 + h2)
  obtain ⟨M, hM⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists_forall_of_atTop
  have hbd : ∃ D : ℝ, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ K * Real.exp (-(c / 2 * t)) ≤ D := by
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max M 0)).exists_bound_of_continuousOn
      (f := fun t : ℝ => (1 + t) ^ K * Real.exp (-(c / 2 * t))) (by fun_prop)
    refine ⟨max D 1, fun t ht => ?_⟩
    by_cases htM : t ≤ max M 0
    · have := hD t ⟨ht, htM⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
      exact this.trans (le_max_left _ _)
    · push Not at htM
      exact (hM t (le_of_lt (lt_of_le_of_lt (le_max_left _ _) htM))).le.trans (le_max_right _ _)
  obtain ⟨D, hD⟩ := hbd
  refine ((integrable_exp_neg_mul_abs (half_pos hc)).const_mul D).mono'
    (by fun_prop) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := hD |y| (abs_nonneg y)
  have he : Real.exp (-(c * |y|)) = Real.exp (-(c / 2 * |y|)) * Real.exp (-(c / 2 * |y|)) := by
    rw [← Real.exp_add]; ring_nf
  rw [he, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

end DLMF.Gamma
