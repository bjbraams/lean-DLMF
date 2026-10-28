/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Recurrences
public import DLMF.Legendre.SecondKind
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# Recurrence of `Q_ν` and Legendre functions of integer degree (Temme §8.5)

The parameters of `Q_{ν±1}` are integer shifts of those of `Q_ν`. A three-term identity for
`𝐅(a,b;a+b;u)`, proved from the series and lifted to the cut plane, gives
`(ν+1) Q_{ν+1} - (2ν+1) z Q_ν + ν Q_{ν-1} = 0` for `ν ≠ 0`, and `Q₁ = z Q₀ - 1`. By induction,
`Q_n = P_n Q₀ - R_n` with polynomials `R_n` (Temme (8.25)). Since `(1-z²)𝒲{P_n, Q_n}` is constant by
Legendre's equation and tends to `P_n(1)² = 1` as `z → 1`, `𝒲{P_n, Q_n} = 1/(1-z²)`.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology Real
open DLMF.OrthogonalPolynomials

noncomputable section

namespace DLMF.Legendre

/-- `(x)ₙ₊₁ = x (x+1)ₙ`. -/
theorem poch_succ_left (x : ℂ) (n : ℕ) :
    (ascPochhammer ℂ (n + 1)).eval x = x * (ascPochhammer ℂ n).eval (x + 1) := by
  rw [ascPochhammer_succ_left]; simp [Polynomial.eval_comp]

/-- The regularized series identity behind the recurrence of `Q_ν`: for `c = a + b`,
`𝐅(a-1,b;c-1;u) - (c-1)𝐅(a,b;c;u) + b² u 𝐅(a,b+1;c+1;u) = 0` on the unit disk. -/
theorem regularizedGaussHGFun_legendreQ (a b : ℂ) {u : ℂ} (hu : ‖u‖ < 1) :
    regularizedGaussHGFun (a - 1) b (a + b - 1) u -
        (a + b - 1) * regularizedGaussHGFun a b (a + b) u +
      b ^ 2 * u * regularizedGaussHGFun a (b + 1) (a + b + 1) u = 0 := by
  set c := a + b with hc
  have s1 := summable_regularizedGaussHGFun_term (a - 1) b (c - 1) hu
  have s2 := summable_regularizedGaussHGFun_term a b c hu
  have s3 := summable_regularizedGaussHGFun_term a (b + 1) (c + 1) hu
  rw [regularizedGaussHGFun_eq_tsum, regularizedGaussHGFun_eq_tsum,
    regularizedGaussHGFun_eq_tsum]
  have h1 := (hasSum_nat_add_iff' 1).mpr s1.hasSum
  have h2 := (hasSum_nat_add_iff' 1).mpr s2.hasSum
  have h := (h1.sub (h2.mul_left (c - 1))).add (s3.hasSum.mul_left (b ^ 2 * u))
  have hz : (fun n : ℕ =>
      (ascPochhammer ℂ (n + 1)).eval (a - 1) * (ascPochhammer ℂ (n + 1)).eval b * u ^ (n + 1) /
          ((n + 1).factorial : ℂ) * (Gamma (c - 1 + ((n + 1 : ℕ) : ℂ)))⁻¹ -
        (c - 1) * ((ascPochhammer ℂ (n + 1)).eval a * (ascPochhammer ℂ (n + 1)).eval b *
          u ^ (n + 1) / ((n + 1).factorial : ℂ) * (Gamma (c + ((n + 1 : ℕ) : ℂ)))⁻¹) +
        b ^ 2 * u * ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval (b + 1) * u ^ n /
          (n.factorial : ℂ) * (Gamma (c + 1 + n))⁻¹)) = fun _ => 0 := by
    funext n
    have hG : (Gamma (c - 1 + ((n + 1 : ℕ) : ℂ)))⁻¹ = (c + n) * (Gamma (c + 1 + n))⁻¹ := by
      rw [show c - 1 + ((n + 1 : ℕ) : ℂ) = c + n by push_cast; ring,
          Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + n),
        show c + n + 1 = c + 1 + n by ring]
    have hG' : (Gamma (c + ((n + 1 : ℕ) : ℂ)))⁻¹ = (Gamma (c + 1 + n))⁻¹ := by
      rw [show c + ((n + 1 : ℕ) : ℂ) = c + 1 + n by push_cast; ring]
    rw [hG, hG', poch_succ_left (a - 1), poch_succ_left b, show a - 1 + 1 = a by ring,
      ascPochhammer_succ_eval, Nat.factorial_succ]
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast
    field_simp
    simp only [hc]
    ring
  simp only [Finset.sum_range_one] at h
  rw [hz] at h
  have h0 := h.unique hasSum_zero
  have hT : (ascPochhammer ℂ 0).eval (a - 1) * (ascPochhammer ℂ 0).eval b * u ^ 0 /
        ((0 : ℕ).factorial : ℂ) * (Gamma (c - 1 + ((0 : ℕ) : ℂ)))⁻¹ -
      (c - 1) * ((ascPochhammer ℂ 0).eval a * (ascPochhammer ℂ 0).eval b * u ^ 0 /
        ((0 : ℕ).factorial : ℂ) * (Gamma (c + ((0 : ℕ) : ℂ)))⁻¹) = 0 := by
    simp only [ascPochhammer_zero, Polynomial.eval_one, pow_zero, Nat.factorial_zero,
      Nat.cast_one, Nat.cast_zero, add_zero, div_one, one_mul]
    rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c - 1), sub_add_cancel]; ring
  linear_combination h0 + hT


/-- The identity `regularizedGaussHGFun_legendreQ` on the cut plane. -/
theorem regularizedGaussHG_legendreQ (a b : ℂ) {u : ℂ} (hu : u ∈ cutPlane) :
    regularizedGaussHG (a - 1) b (a + b - 1) u - (a + b - 1) * regularizedGaussHG a b (a + b) u +
      b ^ 2 * u * regularizedGaussHG a (b + 1) (a + b + 1) u = 0 :=
  eqOn_cutPlane_of_eqOn_disk
    (f := fun u => regularizedGaussHG (a - 1) b (a + b - 1) u - (a + b - 1)
        * regularizedGaussHG a b (a + b) u +
      b ^ 2 * u * regularizedGaussHG a (b + 1) (a + b + 1) u) (g := fun _ => 0)
    (by intro u hu; fun_prop (disch := assumption)) analyticOnNhd_const
    (fun u hu => by
      rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu,
          regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu,
        regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu]
      exact regularizedGaussHGFun_legendreQ a b hu) hu

/-- The three-term recurrence `(ν+1) Q_{ν+1} - (2ν+1) z Q_ν + ν Q_{ν-1} = 0` for `ν ≠ 0`
(DLMF 14.10.3 with `μ = 0`). At `ν = 0` it is replaced by `Q₁ = z Q₀ - 1`. -/
theorem legendreQ_recurrence {ν : ℂ} (hν : ν ≠ 0) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    (ν + 1) * legendreQ (ν + 1) z - (2 * ν + 1) * z * legendreQ ν z +
      ν * legendreQ (ν - 1) z = 0 := by
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have hu := recip_sq_mem_cutPlane hz
  set a := (ν + 2) / 2
  set b := (ν + 1) / 2
  have hid := regularizedGaussHG_legendreQ a b hu
  have e1 : regularizedGaussHG ((ν + 1 + 2) / 2) ((ν + 1 + 1) / 2) (ν + 1 + 3 / 2) (1 / z ^ 2) =
      regularizedGaussHG a (b + 1) (a + b + 1) (1 / z ^ 2) := by
    rw [regularizedGaussHG_symm _ _ _ hu]; congr 1 <;> simp only [a, b] <;> ring
  have e2 : regularizedGaussHG ((ν - 1 + 2) / 2) ((ν - 1 + 1) / 2) (ν - 1 + 3 / 2) (1 / z ^ 2) =
      regularizedGaussHG (a - 1) b (a + b - 1) (1 / z ^ 2) := by
    rw [regularizedGaussHG_symm _ _ _ hu]; congr 1 <;> simp only [a, b] <;> ring
  have e0 : regularizedGaussHG ((ν + 2) / 2) ((ν + 1) / 2) (ν + 3 / 2) (1 / z ^ 2) =
      regularizedGaussHG a b (a + b) (1 / z ^ 2) := by
    congr 1; simp only [a, b]; ring
  simp only [legendreQ]
  rw [e1, e2, e0]
  have hΓ1 : (ν + 1) * Gamma (ν + 1 + 1) = (ν + 1) * ((ν + 1) * Gamma (ν + 1)) := by
    rcases eq_or_ne (ν + 1) 0 with h | h
    · rw [h]; ring
    · rw [Gamma_add_one _ h]
  have hΓ0 : ν * Gamma (ν - 1 + 1) = Gamma (ν + 1) := by
    rw [sub_add_cancel, Gamma_add_one _ hν]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have c1 : (2 : ℂ) ^ (-(ν + 1 + 1)) = 2 ^ (-(ν + 1)) / 2 := by
    rw [show -(ν + 1 + 1) = -(ν + 1) - 1 by ring, cpow_sub _ _ h2, cpow_one]
  have c2 : (2 : ℂ) ^ (-(ν - 1 + 1)) = 2 ^ (-(ν + 1)) * 2 := by
    rw [show -(ν - 1 + 1) = -(ν + 1) + 1 by ring, cpow_add _ _ h2, cpow_one]
  have c3 : z ^ (-(ν + 1 + 1)) = z ^ (-(ν + 1)) / z := by
    rw [show -(ν + 1 + 1) = -(ν + 1) - 1 by ring, cpow_sub _ _ hz0, cpow_one]
  have c4 : z ^ (-(ν - 1 + 1)) = z ^ (-(ν + 1)) * z := by
    rw [show -(ν - 1 + 1) = -(ν + 1) + 1 by ring, cpow_add _ _ hz0, cpow_one]
  rw [c1, c2, c3, c4]
  have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  generalize regularizedGaussHG a (b + 1) (a + b + 1) (1 / z ^ 2) = Gp at *
  generalize regularizedGaussHG (a - 1) b (a + b - 1) (1 / z ^ 2) = Gm at *
  generalize regularizedGaussHG a b (a + b) (1 / z ^ 2) = G at *
  generalize (2 : ℂ) ^ (-(ν + 1)) = A
  generalize z ^ (-(ν + 1)) = Z
  simp only [a, b] at hid
  linear_combination (Real.sqrt π * Gamma (ν + 1) * A * Z * z * 2) * hid +
    (Real.sqrt π * A / 2 * Z / z * Gp) * hΓ1 + (Real.sqrt π * A * 2 * Z * z * Gm) * hΓ0 +
    (-(ν + 1) ^ 2 / 2 * (Real.sqrt π * A * Z * Gp * Gamma (ν + 1)) * z⁻¹) * hzz

/-- `𝐅(0,b;c;u) = 1/Γ(c)` on the cut plane. -/
theorem regularizedGaussHG_zero_left (b c : ℂ) {u : ℂ} (hu : u ∈ cutPlane) :
    regularizedGaussHG 0 b c u = (Gamma c)⁻¹ :=
  eqOn_cutPlane_of_eqOn_disk (f := regularizedGaussHG 0 b c) (g := fun _ => (Gamma c)⁻¹)
    (analyticOnNhd_regularizedGaussHG _ _ _) analyticOnNhd_const (fun u hu => by
      rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu, regularizedGaussHGFun_eq_tsum,
        tsum_eq_single 0 (fun n hn => by
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          simp [ascPochhammer_succ_left])]
      simp) hu

/-- `Q₁(z) = z Q₀(z) - 1` (Temme (8.24)). -/
theorem legendreQ_one {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    legendreQ 1 z = z * legendreQ 0 z - 1 := by
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have hu := recip_sq_mem_cutPlane hz
  have hid := regularizedGaussHG_legendreQ 1 (1 / 2) hu
  rw [show (1 : ℂ) - 1 = 0 by ring, show (1 : ℂ) + 1 / 2 - 1 = 1 / 2 by norm_num,
    regularizedGaussHG_zero_left _ _ hu, show (1 : ℂ) + 1 / 2 = 3 / 2 by norm_num,
    show (1 : ℂ) / 2 + 1 = 3 / 2 by norm_num, show (3 / 2 : ℂ) + 1 = 5 / 2 by norm_num,
    Complex.Gamma_one_half_eq] at hid
  have hsq : (π : ℂ) ^ (1 / 2 : ℂ) = Real.sqrt π := by
    rw [show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  rw [hsq] at hid
  simp only [legendreQ]
  rw [regularizedGaussHG_symm ((1 + 2) / 2) _ _ hu]
  norm_num [cpow_neg_one]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [show (2 : ℂ) ^ (-2 : ℂ) = 1 / 4 by
      rw [show (-2 : ℂ) = ((-2 : ℤ) : ℂ) by norm_num, cpow_intCast]; norm_num,
    show z ^ (-2 : ℂ) = 1 / z ^ 2 by
      rw [show (-2 : ℂ) = ((-2 : ℤ) : ℂ) by norm_num, cpow_intCast]; simp [zpow_neg]]
  rw [show (1 : ℂ) / z ^ 2 = (z ^ 2)⁻¹ from one_div _] at hid
  have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  have hsi : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs
  rw [show (1 : ℂ) / z ^ 2 = (z ^ 2)⁻¹ from one_div _]
  generalize regularizedGaussHG 1 (3 / 2) (5 / 2) (z ^ 2)⁻¹ = Gp at *
  generalize regularizedGaussHG 1 (1 / 2) (3 / 2) (z ^ 2)⁻¹ = G at *
  linear_combination (Real.sqrt π : ℂ) * hid - ((Real.sqrt π : ℂ) / 2 * G) * hzz - hsi

/-- The polynomials `R_n` with `Q_n = P_n Q₀ - R_n` (Temme's `W_{n-1}`, (8.25)), defined by the
Legendre recurrence with `R₀ = 0`, `R₁ = 1`. -/
noncomputable def legendreQPoly : ℕ → Polynomial ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 => Polynomial.C ((n + 2 : ℂ)⁻¹) *
      (Polynomial.C (2 * n + 3 : ℂ) * Polynomial.X * legendreQPoly (n + 1) -
        Polynomial.C (n + 1 : ℂ) * legendreQPoly n)

/-- `z ∉ (-∞, 1]` implies `z ∉ (-∞, -1]`. -/
theorem one_add_mem_slitPlane_of_sub_one {z : ℂ} (hz : z - 1 ∈ slitPlane) : 1 + z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp at h ⊢; linarith
  · right; simpa using h

/-- `Q_n = P_n Q₀ - R_n` with a polynomial `R_n` (Temme (8.25)). -/
theorem legendreQ_nat (n : ℕ) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    legendreQ n z = legendreP n z * legendreQ 0 z - (legendreQPoly n).eval z := by
  have hz' := one_add_mem_slitPlane_of_sub_one hz
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      have h := legendreP_nat 0 hz'
      rw [Nat.cast_zero, legendrePolyP_zero] at h
      simp [legendreQPoly, h]
    | 1, _ =>
      have h := legendreP_nat 1 hz'
      rw [Nat.cast_one] at h
      rw [legendreQPoly, Polynomial.eval_one, Nat.cast_one, legendreQ_one hz, h]
      have hF : ₂F₁ (-((1 : ℕ) : ℂ)) ((1 : ℕ) + 0 + 0 + 1) (0 + 1) ((1 - z) / 2) = z := by
        rw [ordinaryHypergeometric_eq_sum_neg_nat]
        simp [Finset.sum_range_succ, gaussHGCoeff, poch]
        ring
      simp only [legendrePolyP, jacobiPolyP] at *
      rw [hF]
      simp [poch]
    | n + 2, ih =>
      have hQ := legendreQ_recurrence (ν := (n + 1 : ℂ))
        (by exact_mod_cast Nat.succ_ne_zero n) hz
      have hP := legendreP_recurrence (n + 1 : ℂ) hz'
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      push_cast at h1 hQ hP ⊢
      rw [show (n : ℂ) + 1 + 1 = n + 2 by ring, show (n : ℂ) + 1 - 1 = n by ring] at hQ hP
      simp only [legendreQPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X]
      have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      field_simp
      linear_combination hQ - legendreQ 0 z * hP + (2 * ((n : ℂ) + 1) + 1) * z * h1 -
        ((n : ℂ) + 1) * h0

/-- Legendre polynomials are entire. -/
theorem differentiable_legendrePolyP (n : ℕ) : Differentiable ℂ (legendrePolyP n) := by
  have h : legendrePolyP n = fun x => poch (0 + 1) n / n.factorial *
      ∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) ((n : ℂ) + 0 + 0 + 1) (0 + 1) k *
        ((1 - x) / 2) ^ k := by
    funext x; simp only [legendrePolyP, jacobiPolyP, ordinaryHypergeometric_eq_sum_neg_nat]
  rw [h]; fun_prop

/-- `P_n(1) = 1`. -/
theorem legendrePolyP_one_eq (n : ℕ) : legendrePolyP n 1 = 1 := by
  have h := legendreP_nat n (z := 1) (by norm_num)
  rw [legendreP_one] at h
  exact h.symm

/-- `d/dz ½ log((z+1)/(z-1)) = 1/(1-z²)`. -/
theorem hasDerivAt_legendreQ_zero {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => 1 / 2 * log ((w + 1) / (w - 1))) (1 / (1 - z ^ 2)) z := by
  have hz1 : z - 1 ≠ 0 := slitPlane_ne_zero hz
  have hz2 : z + 1 ≠ 0 := slitPlane_ne_zero (by
    have := one_add_mem_slitPlane_of_sub_one hz; rwa [add_comm] at this)
  have hq : HasDerivAt (fun w : ℂ => (w + 1) / (w - 1)) (((z - 1) - (z + 1)) / (z - 1) ^ 2) z :=
    ((hasDerivAt_id' z).add_const 1).div ((hasDerivAt_id' z).sub_const 1) hz1 |>.congr_deriv
      (by ring)
  have h := ((hasDerivAt_log (div_mem_slitPlane hz)).comp z hq).const_mul (1 / 2 : ℂ)
  refine h.congr_deriv ?_
  have h3 : (1 - z ^ 2) ≠ 0 := by
    rw [show 1 - z ^ 2 = -((z - 1) * (z + 1)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hz1 hz2)
  field_simp
  ring

/-- `P_ν` is analytic off `(-∞, -1]`. -/
theorem analyticAt_legendreP (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    AnalyticAt ℂ (legendreP ν) z :=
  (analyticAt_regularizedGaussHG _ _ _ (mem_cutPlane_of_one_add hz)).comp_of_eq (by fun_prop) rfl

/-- The Wronskian `𝒲{P_n, Q_n}(z) = 1/(1 - z²)` for integer degree (Temme §8.5). -/
theorem wronskian_legendreP_legendreQ_nat (n : ℕ) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    legendreP n z * deriv (legendreQ n) z - deriv (legendreP n) z * legendreQ n z =
      1 / (1 - z ^ 2) := by
  set D : Set ℂ := {w | w - 1 ∈ slitPlane}
  have hD : IsOpen D := isOpen_sub_one_mem_slitPlane
  set P := legendreP (n : ℂ)
  set Q := legendreQ (n : ℂ)
  have hPa (w : ℂ) (hw : w ∈ D) : AnalyticAt ℂ P w :=
    analyticAt_legendreP _ (one_add_mem_slitPlane_of_sub_one hw)
  have hQa (w : ℂ) (hw : w ∈ D) : AnalyticAt ℂ Q w := analyticAt_legendreQ _ hw
  have hne (w : ℂ) (hw : w ∈ D) : 1 - w ^ 2 ≠ 0 := by
    intro h
    have hw1 : w - 1 ≠ 0 := slitPlane_ne_zero hw
    have hw2 : w + 1 ≠ 0 := slitPlane_ne_zero (by
      have := one_add_mem_slitPlane_of_sub_one hw; rwa [add_comm] at this)
    exact mul_ne_zero hw1 hw2 (by linear_combination -h)
  set F : ℂ → ℂ := fun w => (1 - w ^ 2) * (P w * deriv Q w - deriv P w * Q w) with hF
  -- `F` has zero derivative on `D`
  have hFd (w : ℂ) (hw : w ∈ D) : HasDerivAt F 0 w := by
    have hP1 := (hPa w hw).differentiableAt.hasDerivAt
    have hQ1 := (hQa w hw).differentiableAt.hasDerivAt
    have hP2 := (hPa w hw).deriv.differentiableAt.hasDerivAt
    have hQ2 := (hQa w hw).deriv.differentiableAt.hasDerivAt
    have hsq : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * w)) w := by
      simpa using ((hasDerivAt_id w).pow 2).const_sub 1
    have h := hsq.mul ((hP1.mul hQ2).sub (hP2.mul hQ1))
    refine h.congr_deriv ?_
    have eP := legendreP_ode (n : ℂ) (one_add_mem_slitPlane_of_sub_one hw)
    have eQ := legendreQ_ode (n : ℂ) hw
    rw [iteratedDeriv_succ, iteratedDeriv_one] at eP eQ
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination (-(Q w)) * eP + P w * eQ
  have hconst : ∀ w ∈ D, F w = F 2 := by
    intro w hw
    exact hD.is_const_of_deriv_eq_zero isPreconnected_sub_one_mem_slitPlane
      (fun v hv => (hFd v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hFd v hv).deriv) hw (show (2 : ℂ) - 1 ∈ slitPlane by norm_num)
  -- the polynomial form of `F`
  set L := legendrePolyP n
  set R : ℂ → ℂ := fun w => (legendreQPoly n).eval w
  have hL : Differentiable ℂ L := differentiable_legendrePolyP n
  have hR : Differentiable ℂ R := (legendreQPoly n).differentiable
  set g : ℂ → ℂ := fun w => L w ^ 2 + (1 - w ^ 2) * (deriv L w * R w - L w * deriv R w)
  have hFg (w : ℂ) (hw : w ∈ D) : F w = g w := by
    have hw' := one_add_mem_slitPlane_of_sub_one hw
    have ePL : P =ᶠ[𝓝 w] L := by
      filter_upwards [isOpen_one_add_mem_slitPlane.mem_nhds hw'] with v hv
      exact legendreP_nat n hv
    have eQ : Q =ᶠ[𝓝 w] fun v => L v * (1 / 2 * log ((v + 1) / (v - 1))) - R v := by
      filter_upwards [hD.mem_nhds hw] with v hv
      have h := legendreQ_nat n hv
      rw [legendreP_nat n (one_add_mem_slitPlane_of_sub_one hv), legendreQ_zero hv] at h
      exact h
    have hQd : HasDerivAt (fun v => L v * (1 / 2 * log ((v + 1) / (v - 1))) - R v)
        (deriv L w * (1 / 2 * log ((w + 1) / (w - 1))) + L w * (1 / (1 - w ^ 2)) -
          deriv R w) w :=
      ((hL w).hasDerivAt.mul (hasDerivAt_legendreQ_zero hw)).sub (hR w).hasDerivAt
    simp only [F, g]
    rw [ePL.deriv_eq, eQ.deriv_eq, hQd.deriv, ePL.eq_of_nhds, eQ.eq_of_nhds]
    have := hne w hw
    field_simp
    ring
  have hg1 : g 1 = 1 := by simp [g, L, legendrePolyP_one_eq n]
  have hgc : Continuous g := by
    have h1 : Continuous (deriv L) := (hL.contDiff (n := 1)).continuous_deriv le_rfl
    have h2 : Continuous (deriv R) := (hR.contDiff (n := 1)).continuous_deriv le_rfl
    simp only [g]
    exact (hL.continuous.pow 2).add ((continuous_const.sub (continuous_pow 2)).mul
      ((h1.mul hR.continuous).sub (hL.continuous.mul h2)))
  -- evaluate the constant along `1 + 1/(k+1) → 1`
  have hseq : Tendsto (fun k : ℕ => (1 : ℂ) + 1 / ((k : ℂ) + 1)) atTop (𝓝 1) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
    simpa using tendsto_const_nhds.add this
  have hmem (k : ℕ) : (1 : ℂ) + 1 / ((k : ℂ) + 1) ∈ D := by
    show (1 : ℂ) + 1 / ((k : ℂ) + 1) - 1 ∈ slitPlane
    rw [add_sub_cancel_left]
    left
    rw [show (1 : ℂ) / ((k : ℂ) + 1) = ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
    positivity
  have hlim := (hgc.tendsto 1).comp hseq
  have hc : F 2 = 1 := by
    rw [← hg1]
    refine tendsto_nhds_unique (tendsto_const_nhds.congr fun k => ?_) hlim
    simp only [Function.comp]
    rw [← hFg _ (hmem k), hconst _ (hmem k)]
  have hFz := hconst z hz
  rw [hc] at hFz
  have := hne z hz
  simp only [F] at hFz
  field_simp
  linear_combination hFz

end DLMF.Legendre

end
