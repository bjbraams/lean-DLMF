/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.ScalarSeries
public import DLMF.OrthogonalPolynomials.Classical
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Data.Nat.Choose.Multinomial
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
# Mehler's Hermite kernel

The closed Gaussian kernel is holomorphic on the unit disk. Its first-order
ordinary differential equation determines its Taylor coefficients uniquely.
The Hermite recurrence verifies the same coefficient relation for the products
of Hermite polynomials. Convergence follows from Mathlib's complex Taylor theorem.
-/

@[expose] public section
open Complex Polynomial Filter
open scoped Nat Topology
noncomputable section
namespace DLMF.OrthogonalPolynomials.Mehler

/-- The closed form of Mehler's bilinear kernel. -/
def kernel (x y z : ℂ) : ℂ :=
  (1 - z ^ 2) ^ (-1 / 2 : ℂ) * exp ((2 * x * y * z - (x ^ 2 + y ^ 2) * z ^ 2) / (1 - z ^ 2))

/-- The denominator stays in the right half-plane on the unit disk. -/
theorem re_den_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (1 - z ^ 2).re := by
  have h : ‖z ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  simp only [sub_re, one_re]
  linarith [re_le_norm (z ^ 2)]

/-- The derivative equation for the Gaussian kernel. -/
theorem hasDerivAt_kernel (x y : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (kernel x y)
      ((2 * x * y + (1 - 2 * (x ^ 2 + y ^ 2)) * z + 2 * x * y * z ^ 2 - z ^ 3) /
        (1 - z ^ 2) ^ 2 * kernel x y z) z := by
  have hr := re_den_pos hz
  have hd : 1 - z ^ 2 ≠ 0 := slitPlane_ne_zero (Or.inl hr)
  have hden : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-2 * z) z := by
    convert ((hasDerivAt_id z).pow 2).const_sub 1 using 1 <;> simp
  have hnum : HasDerivAt (fun w : ℂ => 2 * x * y * w - (x ^ 2 + y ^ 2) * w ^ 2)
      (2 * x * y - 2 * (x ^ 2 + y ^ 2) * z) z := by
    have hh := ((hasDerivAt_id z).const_mul (2 * x * y)).sub
      (((hasDerivAt_id z).pow 2).const_mul (x ^ 2 + y ^ 2))
    change HasDerivAt (fun w : ℂ => 2 * x * y * w - (x ^ 2 + y ^ 2) * w ^ 2) _ z at hh
    convert hh using 1
    simp
    ring
  have hp := hden.cpow_const (c := (-1 / 2 : ℂ)) (Or.inl hr : 1 - z ^ 2 ∈ slitPlane)
  have he := (hnum.div hden hd).cexp
  have hh := hp.mul he
  change HasDerivAt (kernel x y) _ z at hh
  convert hh using 1
  dsimp only [kernel, Pi.div_apply]
  rw [cpow_sub (x := 1 - z ^ 2) (-1 / 2) 1 hd, cpow_one]
  field_simp [hd]
  ring

/-- The recurrence for Taylor coefficients of the Mehler equation. -/
def Rec (x y : ℂ) (c : ℕ → ℂ) (n : ℕ) : Prop :=
  (n + 1 : ℂ) * c (n + 1) = 2 * x * y * c n +
    (if 1 ≤ n then (2 * n - 1 - 2 * (x ^ 2 + y ^ 2)) * c (n - 1) else 0) +
    (if 2 ≤ n then 2 * x * y * c (n - 2) else 0) -
    (if 3 ≤ n then (n - 2 : ℂ) * c (n - 3) else 0)

/-- The Mehler coefficient recurrence and the constant coefficient determine the sequence. -/
theorem rec_unique {x y : ℂ} {c d : ℕ → ℂ} (h0 : c 0 = d 0)
    (hc : ∀ n, Rec x y c n) (hd : ∀ n, Rec x y d n) : c = d := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      have hprev (k : ℕ) (hk : k ≤ n) : c k = d k := ih k (by omega)
      have h1 : (if 1 ≤ n then (2 * n - 1 - 2 * (x ^ 2 + y ^ 2)) * c (n - 1) else 0) =
          (if 1 ≤ n then (2 * n - 1 - 2 * (x ^ 2 + y ^ 2)) * d (n - 1) else 0) := by
        split_ifs <;> simp [hprev (n - 1) (by omega)]
      have h2 : (if 2 ≤ n then 2 * x * y * c (n - 2) else 0) =
          (if 2 ≤ n then 2 * x * y * d (n - 2) else 0) := by
        split_ifs <;> simp [hprev (n - 2) (by omega)]
      have h3 : (if 3 ≤ n then (n - 2 : ℂ) * c (n - 3) else 0) =
          (if 3 ≤ n then (n - 2 : ℂ) * d (n - 3) else 0) := by
        split_ifs <;> simp [hprev (n - 3) (by omega)]
      have he := hc n
      dsimp only [Rec] at he
      rw [hprev n le_rfl, h1, h2, h3] at he
      exact mul_left_cancel₀ (show (n + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
        (he.trans (hd n).symm)

/-- Holomorphy of the kernel supplies a convergent sequence satisfying the recurrence. -/
theorem exists_coefficients (x y : ℂ) :
    ∃ c : ℕ → ℂ, c 0 = 1 ∧ (∀ n, Rec x y c n) ∧
      ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => c n * z ^ n) (kernel x y z) := by
  let c : ℕ → ℂ := fun n => iteratedDeriv n (kernel x y) 0 / n.factorial
  have hf : DifferentiableOn ℂ (kernel x y) (Metric.ball 0 1) := fun z hz =>
    (hasDerivAt_kernel x y (by simpa using hz)).differentiableAt.differentiableWithinAt
  have ha := hf.analyticOnNhd Metric.isOpen_ball
  have hdf : DifferentiableOn ℂ (deriv (kernel x y)) (Metric.ball 0 1) := fun z hz =>
    (ha z hz).deriv.differentiableAt.differentiableWithinAt
  have hs (z : ℂ) (hz : ‖z‖ < 1) : HasSum (fun n => c n * z ^ n) (kernel x y z) := by
    convert Complex.hasSum_taylorSeries_on_ball hf (z := z) (by simpa using hz) using 1
    funext n
    simp only [c, sub_zero, smul_eq_mul]
    ring
  let d : ℕ → ℂ := fun n => (n + 1 : ℂ) * c (n + 1)
  have hds (z : ℂ) (hz : ‖z‖ < 1) : HasSum (fun n => d n * z ^ n) (deriv (kernel x y) z) := by
    convert Complex.hasSum_taylorSeries_on_ball hdf (z := z) (by simpa using hz) using 1
    funext n
    simp only [d, c, sub_zero, smul_eq_mul, ← iteratedDeriv_succ', Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  have heq := scalarSeries_unique
    (c := fun n => d n - 2 * (if 2 ≤ n then d (n - 2) else 0) +
      (if 4 ≤ n then d (n - 4) else 0))
    (d := fun n => 2 * x * y * c n + (1 - 2 * (x ^ 2 + y ^ 2)) *
      (if 1 ≤ n then c (n - 1) else 0) + 2 * x * y * (if 2 ≤ n then c (n - 2) else 0) -
      (if 3 ≤ n then c (n - 3) else 0))
    (f := fun z => (2 * x * y + (1 - 2 * (x ^ 2 + y ^ 2)) * z + 2 * x * y * z ^ 2 - z ^ 3) * kernel x y z)
    (fun z hz => by
      have ht := ((hds z hz).sub ((hasSum_scalar_shift (hds z hz) 2).mul_left 2)).add
        (hasSum_scalar_shift (hds z hz) 4)
      have hde := (hasDerivAt_kernel x y hz).deriv
      have hden : 1 - z ^ 2 ≠ 0 := slitPlane_ne_zero (Or.inl (re_den_pos hz))
      convert ht using 1
      · funext n; ring
      · rw [hde]; field_simp; ring)
    (fun z hz => by
      have ht := ((((hs z hz).mul_left (2 * x * y)).add
        ((hasSum_scalar_shift (hs z hz) 1).mul_left (1 - 2 * (x ^ 2 + y ^ 2)))).add
        ((hasSum_scalar_shift (hs z hz) 2).mul_left (2 * x * y))).sub
        (hasSum_scalar_shift (hs z hz) 3)
      convert ht using 1
      · funext n; ring
      · simp only [pow_one]; ring)
  refine ⟨c, ?_, ?_, hs⟩
  · simp [c, kernel]
  · intro n
    have hh := congrFun heq n
    dsimp only [d] at hh
    rcases n with _ | _ | _ | _ | n
    · simpa [Rec] using hh
    · dsimp [Rec]; norm_num at hh ⊢; linear_combination hh
    · dsimp [Rec]; norm_num at hh ⊢; linear_combination hh
    · dsimp [Rec]; norm_num at hh ⊢; linear_combination hh
    · simp only [Rec, show 1 ≤ n + 4 by omega, show 2 ≤ n + 4 by omega,
        show 3 ≤ n + 4 by omega, show 4 ≤ n + 4 by omega, ite_true,
        show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega,
        show n + 4 - 3 = n + 1 by omega, show n + 4 - 4 = n by omega] at hh ⊢
      push_cast at hh ⊢
      linear_combination hh

/-- The products of Hermite polynomials, with their exponential generating normalization. -/
def coeff (x y : ℂ) (n : ℕ) : ℂ :=
  (aeval x (hermitePolyH n) : ℂ) * aeval y (hermitePolyH n) / (2 ^ n * (n.factorial : ℂ))

/-- The Hermite three-term recurrence implies the Mehler coefficient recurrence. -/
theorem rec_coeff (x y : ℂ) (n : ℕ) : Rec x y (coeff x y) n := by
  rcases n with _ | _ | _ | n
  · norm_num [Rec, coeff, hermitePolyH_zero, hermitePolyH_one, map_ofNat]; ring
  · norm_num [Rec, coeff, aeval_hermitePolyH_succ_succ, hermitePolyH_zero, hermitePolyH_one, map_ofNat]; ring
  · norm_num [Rec, coeff, aeval_hermitePolyH_succ_succ, hermitePolyH_zero, hermitePolyH_one, map_ofNat]; ring
  · simp only [Rec, show 1 ≤ n + 3 by omega, show 2 ≤ n + 3 by omega,
      show 3 ≤ n + 3 by omega, ite_true, show n + 3 - 1 = n + 2 by omega,
      show n + 3 - 2 = n + 1 by omega, show n + 3 - 3 = n by omega]
    have hfac (k : ℕ) : ((n + (k + 1)).factorial : ℂ) =
        ((n : ℂ) + ((k + 1 : ℕ) : ℂ)) * ((n + k).factorial : ℂ) := by
      rw [show n + (k + 1) = (n + k) + 1 by omega, Nat.factorial_succ]
      push_cast; ring
    simp only [coeff, pow_add, hfac 3, hfac 2, hfac 1, hfac 0, Nat.add_zero]
    norm_num1
    have h1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
    have h3 : (n + 3 : ℂ) ≠ 0 := by exact_mod_cast (show n + 3 ≠ 0 by omega)
    have h4 : (n + 4 : ℂ) ≠ 0 := by exact_mod_cast (show n + 4 ≠ 0 by omega)
    field_simp [h1, h2, h3, h4, Nat.cast_ne_zero.mpr n.factorial_ne_zero]
    simp only [aeval_hermitePolyH_succ_succ]
    push_cast
    ring

/-- Mehler's formula holds for arbitrary complex spatial arguments on the open unit disk. -/
theorem hasSum_kernel (x y : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => coeff x y n * z ^ n) (kernel x y z) := by
  obtain ⟨c, hc0, hc, hs⟩ := exists_coefficients x y
  have he : c = coeff x y := rec_unique (by simpa [coeff, hermitePolyH_zero] using hc0) hc (rec_coeff x y)
  rw [← he]
  exact hs z hz

end DLMF.OrthogonalPolynomials.Mehler
