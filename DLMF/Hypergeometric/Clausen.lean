/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Data.Nat.Choose.Cast

public import DLMF.Hypergeometric.Continuation
public import DLMF.Bessel.RegularizedSeries
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Clausen's formula (Duverney §4.4.2; DLMF 16.12.2)

`F(a, b; a+b+1/2; z)² = ₃F₂(2a, 2b, a+b; a+b+1/2, 2a+2b; z)`. With the Euler operator
`θ = X d/dX` on formal power series, the Gauss equation `θ(θ+c-1)F = X(θ+a)(θ+b)F` with
`c = a+b+1/2` implies that `w = F²` satisfies the generalized equation
`θ(θ+c-1)(θ+2a+2b-1)w = X(θ+2a)(θ+2b)(θ+a+b)w`. In fact
`T(w) = 2F·θE + (4aF + 4bF - 2F + 6θF)·E`, where `E` is the Gauss equation; the multipliers
were found by computer algebra and the identity is checked by `linear_combination`. Comparing
coefficients gives the `₃F₂` recurrence for the coefficients of `F²`, hence Clausen's formula.

Corollaries: Euler's series `2 arcsin² x = ∑ (2x)^{2n}/(n² C(2n,n))` (Duverney (4.45)–(4.46)) and
`π² = 18 ∑ 1/(n² C(2n,n))` (Duverney Ex. 4.6).
-/

@[expose] public section

open PowerSeries Complex
open scoped Nat Real
open DLMF.Bessel

noncomputable section

namespace DLMF.Hypergeometric

/-- The Euler operator `θ = X d/dX` on formal power series, coefficientwise. -/
def thetaPS (g : PowerSeries ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => (n : ℂ) * coeff n g

/-- Coefficients of `θ g`. -/
@[simp] theorem coeff_thetaPS (g : PowerSeries ℂ) (n : ℕ) : coeff n (thetaPS g) = n * coeff n g := by
  simp [thetaPS]

/-- `θ` is additive. -/
theorem thetaPS_add (g h : PowerSeries ℂ) : thetaPS (g + h) = thetaPS g + thetaPS h := by
  ext n; simp [mul_add]

/-- `θ` commutes with subtraction. -/
theorem thetaPS_sub (g h : PowerSeries ℂ) : thetaPS (g - h) = thetaPS g - thetaPS h := by
  ext n; simp [mul_sub]

/-- `θ` is `ℂ`-linear. -/
theorem thetaPS_C_mul (c : ℂ) (g : PowerSeries ℂ) : thetaPS (C c * g) = C c * thetaPS g := by
  ext n; simp [coeff_C_mul]; ring

/-- `θ` is a derivation. -/
theorem thetaPS_mul (g h : PowerSeries ℂ) :
    thetaPS (g * h) = thetaPS g * h + g * thetaPS h := by
  ext n
  simp only [coeff_thetaPS, map_add, coeff_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [← hp]; push_cast; ring

/-- `θ(X g) = X g + X θ g`. -/
theorem thetaPS_X_mul (g : PowerSeries ℂ) : thetaPS (X * g) = X * g + X * thetaPS g := by
  ext n
  rcases n with _ | n
  · simp
  · simp only [coeff_thetaPS, map_add, coeff_succ_X_mul]; push_cast; ring

/-- The Gauss series as a formal power series. -/
def gaussPS (a b c : ℂ) : PowerSeries ℂ := PowerSeries.mk (gaussHGCoeff a b c)

/-- The hypergeometric equation in `θ`-form for the formal Gauss series:
`θ(θ+c-1) F = X (θ+a)(θ+b) F`. -/
theorem gaussPS_ode {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    thetaPS (thetaPS (gaussPS a b c)) + C (c - 1) * thetaPS (gaussPS a b c) -
      X * (thetaPS (thetaPS (gaussPS a b c)) + C (a + b) * thetaPS (gaussPS a b c) +
        C (a * b) * gaussPS a b c) = 0 := by
  ext n
  rcases n with _ | n
  · simp only [LinearMap.map_sub, LinearMap.map_add, coeff_thetaPS, coeff_C_mul,
      coeff_zero_X_mul, map_zero]
    push_cast; ring
  · simp only [LinearMap.map_sub, LinearMap.map_add, coeff_thetaPS, coeff_C_mul,
      coeff_succ_X_mul, gaussPS, coeff_mk, map_zero]
    have h := gaussHGCoeff_recurrence (a := a) (b := b) hc n
    push_cast
    linear_combination h

/-- Clausen's coefficient recurrence: with `D = coeff (F²)`, `c = a + b + 1/2`,
`(n+1)(n+c)(n+2a+2b) D_{n+1} = (n+2a)(n+2b)(n+a+b) D_n`. -/
theorem clausen_recurrence {a b : ℂ} (hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -k) (n : ℕ) :
    ((n : ℂ) + 1) * (n + (a + b + 1 / 2)) * (n + (2 * a + 2 * b)) *
        coeff (n + 1) (gaussPS a b (a + b + 1 / 2) * gaussPS a b (a + b + 1 / 2)) =
      (n + 2 * a) * (n + 2 * b) * (n + (a + b)) *
        coeff n (gaussPS a b (a + b + 1 / 2) * gaussPS a b (a + b + 1 / 2)) := by
  set f := gaussPS a b (a + b + 1 / 2)
  set f1 := thetaPS f
  set f2 := thetaPS f1
  set f3 := thetaPS f2
  have E := gaussPS_ode (a := a) (b := b) hc
  have E1 := congrArg thetaPS E
  simp only [thetaPS_add, thetaPS_sub, thetaPS_C_mul, thetaPS_X_mul] at E1
  rw [show thetaPS (0 : PowerSeries ℂ) = 0 by ext n; simp] at E1
  set w := f * f
  have w1 : thetaPS w = 2 * f * f1 := by rw [thetaPS_mul]; ring
  have w2 : thetaPS (thetaPS w) = 2 * f1 * f1 + 2 * f * f2 := by
    rw [w1, show (2 : PowerSeries ℂ) * f * f1 = C 2 * (f * f1) by simp [map_ofNat]; ring,
      thetaPS_C_mul, thetaPS_mul]; simp [map_ofNat]; ring
  have w3 : thetaPS (thetaPS (thetaPS w)) = 6 * f1 * f2 + 2 * f * f3 := by
    rw [w2, show (2 : PowerSeries ℂ) * f1 * f1 + 2 * f * f2 = C 2 * (f1 * f1) + C 2 * (f * f2) by
      simp [map_ofNat]; ring, thetaPS_add, thetaPS_C_mul, thetaPS_C_mul, thetaPS_mul, thetaPS_mul]
    simp [map_ofNat]; ring
  have T : thetaPS (thetaPS (thetaPS w)) + C (a + b - 1 / 2 + (2 * a + 2 * b - 1)) *
        thetaPS (thetaPS w) + C ((a + b - 1 / 2) * (2 * a + 2 * b - 1)) * thetaPS w -
      X * (thetaPS (thetaPS (thetaPS w)) + C (2 * a + 2 * b + (a + b)) * thetaPS (thetaPS w) +
        C (2 * a * (2 * b) + 2 * b * (a + b) + (a + b) * (2 * a)) * thetaPS w +
        C (2 * a * (2 * b) * (a + b)) * w) = 0 := by
    rw [w3, w2, w1]
    have hC : ∀ x y : ℂ, C (x + y) = C x + C y := fun x y => map_add C x y
    have hM : ∀ x y : ℂ, C (x * y) = C x * C y := fun x y => map_mul C x y
    simp only [hC, hM, map_sub, map_ofNat, map_one] at E E1 ⊢
    have hh : C (1 / 2 : ℂ) * 2 = 1 := by rw [← map_ofNat C 2, ← map_mul]; norm_num
    linear_combination (2 * f) * E1 + (4 * C a * f + 4 * C b * f - 2 * f + 6 * f1) * E -
      (2 * f2 * f + 4 * f1 ^ 2 + f1 * f * (4 * C a + 4 * C b - 2)) * hh
  have hT := congrArg (coeff (n + 1)) T
  simp only [LinearMap.map_sub, LinearMap.map_add, coeff_thetaPS, coeff_C_mul,
    coeff_succ_X_mul, map_zero] at hT
  push_cast at hT
  linear_combination hT

/-- The coefficients of `₃F₂(2a, 2b, a+b; a+b+1/2, 2a+2b; z)`. -/
def clausenCoeff (a b : ℂ) (n : ℕ) : ℂ :=
  poch (2 * a) n * poch (2 * b) n * poch (a + b) n /
    (poch (a + b + 1 / 2) n * poch (2 * a + 2 * b) n * n.factorial)

/-- The coefficients of `F(a,b;a+b+1/2;·)²` are those of the Clausen `₃F₂`. -/
theorem coeff_gaussPS_sq_eq_clausenCoeff {a b : ℂ} (hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -k)
    (hd : ∀ k : ℕ, 2 * a + 2 * b ≠ -k) (n : ℕ) :
    coeff n (gaussPS a b (a + b + 1 / 2) * gaussPS a b (a + b + 1 / 2)) = clausenCoeff a b n := by
  induction n with
  | zero => simp [gaussPS, clausenCoeff, gaussHGCoeff, poch_zero, coeff_mul]
  | succ n ih =>
    have hr := clausen_recurrence hc n
    rw [ih] at hr
    have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h2 : (n : ℂ) + (a + b + 1 / 2) ≠ 0 := fun h => hc n (by linear_combination h)
    have h3 : (n : ℂ) + (2 * a + 2 * b) ≠ 0 := fun h => hd n (by linear_combination h)
    have hp1 := poch_ne_zero_of_not_neg_nat hc n
    have hp2 := poch_ne_zero_of_not_neg_nat hd n
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2' : a + b + 1 / 2 + (n : ℂ) ≠ 0 := by rw [add_comm]; exact h2
    have h3' : 2 * a + 2 * b + (n : ℂ) ≠ 0 := by rw [add_comm]; exact h3
    have hB : clausenCoeff a b (n + 1) * (((n : ℂ) + 1) * (n + (a + b + 1 / 2)) *
        (n + (2 * a + 2 * b))) =
          (n + 2 * a) * (n + 2 * b) * (n + (a + b)) * clausenCoeff a b n := by
      simp only [clausenCoeff, poch_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      generalize poch (a + b + 1 / 2) n = q1 at *
      generalize poch (2 * a + 2 * b) n = q2 at *
      generalize poch (2 * a) n = p1
      generalize poch (2 * b) n = p2
      generalize poch (a + b) n = p3
      generalize (n.factorial : ℂ) = F at *
      rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hp1 h2') (mul_ne_zero hp2 h3')) (mul_ne_zero h1 hf))
        (mul_ne_zero (mul_ne_zero hp1 hp2) hf)]
      ring
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h1 h2) h3) (hr.trans ?_)
    rw [← hB]; ring

/-- **Clausen's formula** (Duverney (4.40); DLMF 16.12.2): for `|z| < 1`,
`F(a, b; a+b+1/2; z)² = ₃F₂(2a, 2b, a+b; a+b+1/2, 2a+2b; z)`. -/
@[dlmf 16.12.E2]
theorem clausen_formula {a b : ℂ} (hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -k)
    (hd : ∀ k : ℕ, 2 * a + 2 * b ≠ -k) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => clausenCoeff a b n * z ^ n) (₂F₁ a b (a + b + 1 / 2) z ^ 2) := by
  have hs := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b (a + b + 1 / 2)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz)
  have hprod := hasSum_sum_range_mul_of_summable_norm hs.summable.norm hs.summable.norm
  rw [hs.tsum_eq, ← pow_two] at hprod
  refine hprod.congr_fun fun n => ?_
  rw [← coeff_gaussPS_sq_eq_clausenCoeff hc hd n, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [gaussPS, coeff_mk]
  rw [show z ^ n = z ^ k * z ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hk']]
  ring

/-- `(3/2)ₙ = (2n+1)!/(4ⁿ n!)`. -/
theorem poch_three_halves' (n : ℕ) :
    poch (3 / 2 : ℂ) n = ((2 * n + 1)! : ℂ) / (4 ^ n * n !) := by
  have hG : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hs : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero (fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
  have h1 := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (3 / 2 : ℂ) hG
  have e1 : Gamma ((3 / 2 : ℂ) + n) = ((2 * (n + 1))! : ℂ) / (4 ^ (n + 1) * (n + 1)!) *
      Gamma (1 / 2) := by
    rw [show (3 / 2 : ℂ) + n = 1 / 2 + ((n + 1 : ℕ) : ℂ) by push_cast; ring, Gamma_nat_add_half]
  have e0 : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]; ring
  rw [poch, ← h1, e1, e0, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ,
    Nat.factorial_succ n]
  have hf : ((2 * n + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp
  ring

/-- The Clausen coefficients at `a = b = 1/2`. -/
theorem clausenCoeff_half (n : ℕ) :
    clausenCoeff (1 / 2) (1 / 2) n = 4 ^ n * (n ! : ℂ) ^ 2 / (((n : ℂ) + 1) * (2 * n + 1)!) := by
  rw [clausenCoeff, show 2 * (1 / 2 : ℂ) = 1 by norm_num, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
    show (1 : ℂ) + 1 / 2 = 3 / 2 by norm_num, show (1 : ℂ) + 1 = 2 by norm_num,
    poch_nat_one, poch_three_halves', poch_nat_two, Nat.factorial_succ n]
  have hf : ((2 * n + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/-- `F(1/2,1/2;3/2;x²)` is real for real `|x| < 1`. -/
theorem ordinaryHypergeometric_half_im {x : ℝ} (hx : |x| < 1) :
    (₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) ((x : ℂ) ^ 2)).im = 0 := by
  have hz : ‖(x : ℂ) ^ 2‖ < 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs]; nlinarith [abs_nonneg x]
  have hs := ((hasFPowerSeriesOnBall_ordinaryHypergeometric (1 / 2 : ℂ) (1 / 2)
    (3 / 2)).hasSum_mul_pow (mem_eball_one_of_norm_lt_one hz)).mapL Complex.imCLM
  refine hs.unique (hasSum_zero.congr_fun fun n => ?_)
  simp only [imCLM_apply, gaussHGCoeff, poch]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, ascPochhammer_eval_ofReal,
    ascPochhammer_eval_ofReal, ← ofReal_pow, ← ofReal_pow]
  norm_cast

/-- **Euler's series for `arcsin²`** (Duverney (4.45)–(4.46)), from Clausen's formula with
`a = b = 1/2`: `2 arcsin² x = ∑_{n ≥ 1} (2x)^{2n} / (n² C(2n,n))` for `|x| < 1`. -/
theorem hasSum_arcsin_sq {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (2 * x) ^ (2 * n) / ((n : ℝ) ^ 2 * (2 * n).choose n))
      (2 * Real.arcsin x ^ 2) := by
  have hz : ‖(x : ℂ) ^ 2‖ < 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs]; nlinarith [abs_nonneg x]
  have hc : ∀ k : ℕ, (1 / 2 : ℂ) + 1 / 2 + 1 / 2 ≠ -k := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hd : ∀ k : ℕ, 2 * (1 / 2 : ℂ) + 2 * (1 / 2) ≠ -k := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hcl := clausen_formula hc hd hz
  rw [show (1 / 2 : ℂ) + 1 / 2 + 1 / 2 = 3 / 2 by norm_num] at hcl
  have hre := ordinaryHypergeometric_half_im hx
  set F := ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) ((x : ℂ) ^ 2)
  have hF : F = (F.re : ℂ) := Complex.ext rfl (by simp [hre])
  have harc := arcsin_eq_ordinaryHypergeometric hx
  -- `2 x² F² = 2 arcsin² x` as a series in `x`
  have h2 := hcl.mul_left (2 * (x : ℂ) ^ 2)
  have hv : 2 * (x : ℂ) ^ 2 * F ^ 2 = ((2 * Real.arcsin x ^ 2 : ℝ) : ℂ) := by
    rw [hF, harc]; push_cast; ring
  rw [hv] at h2
  rw [← Complex.hasSum_ofReal]
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, pow_zero, zero_pow two_ne_zero,
    zero_mul, div_zero, ofReal_zero, sub_zero]
  refine h2.congr_fun fun n => ?_
  rw [clausenCoeff_half]
  have hch : ((2 * (n + 1)).choose (n + 1) : ℂ) = ((2 * n + 2)! : ℂ) / ((n + 1)! * (n + 1)!) := by
    rw [show 2 * (n + 1) = (n + 1) + (n + 1) by ring, Nat.choose_symm_add,
      Nat.cast_choose ℂ (Nat.le_add_right (n + 1) (n + 1))]
    rw [show (n + 1) + (n + 1) = 2 * n + 2 by ring, show 2 * n + 2 - (n + 1) = n + 1 by omega]
  push_cast
  rw [hch, show 2 * n + 2 = (2 * n + 1) + 1 by ring, Nat.factorial_succ (2 * n + 1),
    Nat.factorial_succ n]
  have hf : ((2 * n + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (2 : ℂ) + n * 2 ≠ 0 := by
    rw [show (2 : ℂ) + n * 2 = 2 * ((n : ℂ) + 1) by ring]; exact mul_ne_zero two_ne_zero hn1
  have h4 : (4 : ℂ) ^ n = 2 ^ (n * 2) := by rw [pow_mul']; norm_num
  push_cast
  field_simp
  rw [h4]
  have hinv : ((2 : ℂ) + n * 2)⁻¹ * ((n : ℂ) + 1) = 1 / 2 := by
    rw [show (2 : ℂ) + n * 2 = 2 * ((n : ℂ) + 1) by ring]; field_simp
  linear_combination (4 * (x : ℂ) ^ 2 * (x : ℂ) ^ (n * 2) * 2 ^ (n * 2)) * hinv

/-- **`π² = 18 ∑_{n≥1} 1/(n² C(2n,n))`** (Duverney Ex. 4.6), the case `x = 1/2` of
`hasSum_arcsin_sq`. -/
theorem hasSum_recip_sq_mul_centralBinom :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) ^ 2 * (2 * n).choose n)) (π ^ 2 / 18) := by
  have h := hasSum_arcsin_sq (x := 1 / 2) (by rw [abs_of_pos (by norm_num)]; norm_num)
  have harc : Real.arcsin (1 / 2) = π / 6 := by
    rw [← Real.sin_pi_div_six, Real.arcsin_sin (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])]
  rw [harc] at h
  convert h using 1
  · funext n; norm_num
  · ring

end DLMF.Hypergeometric

end
