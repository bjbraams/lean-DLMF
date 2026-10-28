/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Differential

/-!
# The finite Legendre addition kernel

Derivative ladders and the differentiated Legendre equation prove the three-term
recurrence of the finite angular kernel. Identifying its first two values gives
Legendre's addition theorem, including vanishing sines and all boundary indices.
The proof uses the Mathlib contributors’ analytic differentiation, finite-sum,
and trigonometric APIs. The angle-free kernel permits complex coordinates
satisfying `s² = 1-x²` and `t² = 1-y²`.
-/

@[expose] public section

open Complex Polynomial Filter Set
open scoped Nat Topology
open DLMF.Hypergeometric
noncomputable section

namespace DLMF.OrthogonalPolynomials.LegendreAddition
/-- Derivatives of the Legendre polynomial. -/
def jet (n k : ℕ) : ℂ → ℂ := iteratedDeriv k (legendrePolyP n)
/-- The zeroth derivative. -/
theorem jet_zero (n : ℕ) : jet n 0 = legendrePolyP n := rfl
/-- The first derivative. -/
theorem jet_one (n : ℕ) : jet n 1 = deriv (legendrePolyP n) := iteratedDeriv_one
/-- Differentiation advances the derivative order. -/
theorem deriv_jet (n k : ℕ) : deriv (jet n k) = jet n (k+1) := by
  exact (iteratedDeriv_succ).symm
/-- Every derivative is entire. -/
theorem analytic_jet (n k : ℕ) : AnalyticOnNhd ℂ (jet n k) univ := by
  induction k with
  | zero => exact analyticOnNhd_jacobiPolyP 0 0 n
  | succ k ih => simpa only [← deriv_jet] using ih.deriv
/-- Every derivative is differentiable. -/
theorem diff_jet (n k : ℕ) : Differentiable ℂ (jet n k) :=
  fun z => ((analytic_jet n k) z (mem_univ z)).differentiableAt
/-- The derivative in HasDerivAt form. -/
theorem hderiv_jet (n k : ℕ) (z : ℂ) : HasDerivAt (jet n k) (jet n (k+1) z) z := by
  simpa only [deriv_jet] using (diff_jet n k z).hasDerivAt

/-- Weighted derivative ladders, valid also at the endpoints. -/
theorem weighted_ladders (n : ℕ) (z : ℂ) :
      (1-z^2) * deriv (legendrePolyP n) z = (n+1) * (z * legendrePolyP n z - legendrePolyP (n+1) z) ∧
      (1-z^2) * deriv (legendrePolyP (n+1)) z = (n+1) * (legendrePolyP n z-z*legendrePolyP (n+1) z) := by
  have h0 := jacobi_raising_derivative (α := 0) (β := 0) (by norm_num) n z
  have h1 := jacobi_lowering_derivative (α := 0) (β := 0) (by norm_num) n z
  change (2*n+0+0+2) * (1-z^2) * deriv (legendrePolyP n) z = _ at h0
  change (2*n+0+0+2) * (1-z^2) * deriv (legendrePolyP (n+1)) z = _ at h1
  change (2*n+0+0+2) * (1-z^2) * deriv (legendrePolyP n) z =
    (n+0+0+1) * (0-0+(2*n+0+0+2)*z) * legendrePolyP n z -
      2*(n+1)*(n+0+0+1)*legendrePolyP (n+1) z at h0
  change (2*n+0+0+2) * (1-z^2) * deriv (legendrePolyP (n+1)) z =
    (n+1)*(0-0-(2*n+0+0+2)*z)*legendrePolyP (n+1) z +
      2*(n+0+1)*(n+0+1)*legendrePolyP n z at h1
  have hn : (2*(n : ℂ)+2) ≠ 0 := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    intro h; have := congrArg re h; simp at this; linarith
  constructor
  · apply mul_left_cancel₀ hn
    linear_combination h0
  · apply mul_left_cancel₀ hn
    linear_combination h1

/-- The two derivative ladders at order one. -/
theorem base_ladders (n : ℕ) :
    deriv (legendrePolyP (n+1)) = (fun z => z * deriv (legendrePolyP n) z + (n+1) * legendrePolyP n z) ∧
    deriv (legendrePolyP n) = (fun z => z * deriv (legendrePolyP (n+1)) z - (n+1) * legendrePolyP (n+1) z) := by
  have hmul := weighted_ladders n
  have hne {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : 1-z^2 ≠ 0 := by
    have hz' : ‖z‖ < 1 := by simpa using hz
    have hn : ‖z^2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
    intro h
    have he : z^2 = 1 := (sub_eq_zero.mp h).symm
    simp [he] at hn
  have hA : AnalyticOnNhd ℂ (deriv (legendrePolyP n)) univ := (analytic_jet n 0).deriv
  have hB : AnalyticOnNhd ℂ (deriv (legendrePolyP (n+1))) univ := (analytic_jet (n+1) 0).deriv
  constructor
  · refine eq_of_analyticOnNhd_univ_of_eqOn (U := Metric.ball (0 : ℂ) 1) hB ?_
      Metric.isOpen_ball ⟨0, by simp⟩ ?_
    · intro z _
      exact (analyticAt_id.mul (hA z (mem_univ z))).add
        (analyticAt_const.mul ((analytic_jet n 0) z (mem_univ z)))
    · intro z hz
      apply mul_left_cancel₀ (hne hz)
      linear_combination (hmul z).2 - z * (hmul z).1
  · refine eq_of_analyticOnNhd_univ_of_eqOn (U := Metric.ball (0 : ℂ) 1) hA ?_
      Metric.isOpen_ball ⟨0, by simp⟩ ?_
    · intro z _
      exact (analyticAt_id.mul (hB z (mem_univ z))).sub
        (analyticAt_const.mul ((analytic_jet (n+1) 0) z (mem_univ z)))
    · intro z hz
      apply mul_left_cancel₀ (hne hz)
      linear_combination (hmul z).1 - z * (hmul z).2

/-- The raising ladder for every derivative order. -/
theorem jet_raise (n k : ℕ) (z : ℂ) :
    jet (n+1) (k+1) z = z * jet n (k+1) z + (n+k+1) * jet n k z := by
  induction k generalizing z with
  | zero => simpa [jet, iteratedDeriv_one] using congrFun (base_ladders n).1 z
  | succ k ih =>
    have he : jet (n+1) (k+1) = fun z => z * jet n (k+1) z + (n+k+1) * jet n k z := funext ih
    have hd := congrArg (fun f : ℂ → ℂ => deriv f z) he
    rw [deriv_jet] at hd
    have hh := ((hasDerivAt_id z).mul (hderiv_jet n (k+1) z)).add
      ((hderiv_jet n k z).const_mul ((n : ℂ)+k+1))
    change HasDerivAt (fun w : ℂ => w * jet n (k+1) w + ((n : ℂ)+k+1)*jet n k w) _ z at hh
    rw [hh.deriv] at hd
    simp only [id_eq] at hd
    push_cast
    linear_combination hd

/-- The lowering ladder for every derivative order. -/
theorem jet_lower (n k : ℕ) (z : ℂ) :
    jet n (k+1) z = z * jet (n+1) (k+1) z - ((n : ℂ)+1-k) * jet (n+1) k z := by
  induction k generalizing z with
  | zero => simpa [jet, iteratedDeriv_one] using congrFun (base_ladders n).2 z
  | succ k ih =>
    have he : jet n (k+1) = fun z => z * jet (n+1) (k+1) z - ((n : ℂ)+1-k) * jet (n+1) k z := funext ih
    have hd := congrArg (fun f : ℂ → ℂ => deriv f z) he
    rw [deriv_jet] at hd
    have hh := ((hasDerivAt_id z).mul (hderiv_jet (n+1) (k+1) z)).sub
      ((hderiv_jet (n+1) k z).const_mul ((n : ℂ)+1-k))
    change HasDerivAt (fun w : ℂ => w * jet (n+1) (k+1) w - ((n : ℂ)+1-k)*jet (n+1) k w) _ z at hh
    rw [hh.deriv] at hd
    simp only [id_eq] at hd
    push_cast
    linear_combination hd

/-- The differentiated Legendre equation. -/
theorem jet_ode (n k : ℕ) (z : ℂ) :
    (1-z^2) * jet n (k+2) z - 2*(k+1)*z*jet n (k+1) z +
      ((n : ℂ)-k)*(n+k+1)*jet n k z = 0 := by
  induction k generalizing z with
  | zero => simpa [jet, iteratedDeriv_succ, iteratedDeriv_zero] using legendre_differential_equation n z
  | succ k ih =>
    have he : (fun z : ℂ => (1-z^2) * jet n (k+2) z - 2*(k+1)*z*jet n (k+1) z +
        ((n : ℂ)-k)*(n+k+1)*jet n k z) = fun _ => 0 := funext ih
    have hd := congrArg (fun f : ℂ → ℂ => deriv f z) he
    have hh := ((((hasDerivAt_id z).pow 2).const_sub 1).mul (hderiv_jet n (k+2) z)).sub
      ((((hasDerivAt_id z).const_mul (2*((k : ℂ)+1))).mul (hderiv_jet n (k+1) z)))
    have hh' := hh.add ((hderiv_jet n k z).const_mul (((n : ℂ)-k)*(n+k+1)))
    change HasDerivAt (fun w : ℂ => (1-w^2)*jet n (k+2) w -
      2*((k : ℂ)+1)*w*jet n (k+1) w + ((n : ℂ)-k)*(n+k+1)*jet n k w) _ z at hh'
    rw [hh'.deriv, deriv_const] at hd
    simp only [id_eq, Pi.pow_apply] at hd
    push_cast
    linear_combination hd
end DLMF.OrthogonalPolynomials.LegendreAddition
namespace DLMF.OrthogonalPolynomials.LegendreAddition
/-- The Jacobi form of the derivatives, including the top derivative. -/
theorem jet_eq_jacobi (n k : ℕ) (hk : k ≤ n) (z : ℂ) :
    jet n k z = poch (n+1) k / 2^k * jacobiPolyP k k (n-k) z := by
  induction k generalizing n z with
  | zero => simp [jet, legendrePolyP, poch_zero]
  | succ k ih =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
    have he : jet (k+1+r) k = fun z => poch ((k+1+r : ℕ)+1) k / 2^k *
        jacobiPolyP k k ((k+1+r)-k) z := funext fun z => ih _ (by omega) z
    rw [← deriv_jet, he, deriv_const_mul_field', show k+1+r-k = r+1 by omega]
    dsimp only
    rw [jacobi_derivative (show -1 < ((k : ℂ)).re by change -1 < (k : ℝ); linarith [Nat.cast_nonneg (α := ℝ) k])]
    rw [show k+1+r-(k+1) = r by omega, poch_succ, pow_succ]
    push_cast
    field_simp
    ring

/-- The derivatives above the degree vanish. -/
theorem jet_eq_zero {n k : ℕ} (hk : n < k) : jet n k = 0 := by
  have hz : jet n (n+1) = 0 := by
    rw [← deriv_jet]
    have he : jet n n = fun _ => poch (n+1) n / 2^n := by
      funext z
      rw [jet_eq_jacobi n n le_rfl, Nat.sub_self, jacobiPolyP_zero, mul_one]
    rw [he]
    ext z
    simp
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show n+1 ≤ k by omega)
  induction r with
  | zero => simpa using hz
  | succ r ih =>
    rw [show n+1+(r+1) = (n+1+r)+1 by omega, ← deriv_jet, ih (by omega)]
    ext z
    simp

/-- The elementary coefficient of the angular expansion. -/
def weight (n k : ℕ) : ℂ := (n-k)! / ((n+k)! : ℂ)
/-- The factorial-weighted product of associated Legendre derivatives. -/
def coeff (n k : ℕ) (x y s t : ℂ) : ℂ :=
  weight n k * (s*t)^k * jet n k x * jet n k y
/-- The coefficient `coeff n k` vanishes for `k > n`. -/
theorem coeff_eq_zero {n k : ℕ} (hk : n < k) (x y s t : ℂ) : coeff n k x y s t = 0 := by
  simp [coeff, jet_eq_zero hk]

/-- Ratios of the factorial weights at an interior index. -/
theorem weight_shifts {n k : ℕ} (hk : k < n) :
    weight (n+1) k = weight n k * (n-k+1) / (n+k+1) ∧
    weight (n-1) k = weight n k * (n+k) / (n-k) ∧
    weight n (k+1) = weight n k / ((n-k)*(n+k+1)) := by
  have hkn : k ≤ n := hk.le
  have hn0 : 0 < n := by omega
  have h0 : ((n+k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n+k).factorial_ne_zero
  have hnk : (n-k : ℂ) ≠ 0 := by
    rw [← Nat.cast_sub hkn]
    exact Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hk).ne'
  have hnp : (n+k+1 : ℂ) ≠ 0 := by exact_mod_cast (n+k).succ_ne_zero
  dsimp only [weight]
  rw [show n+1-k = (n-k)+1 by omega, show n+1+k = (n+k)+1 by omega,
    show n-1-k = n-k-1 by omega, show n-1+k = n+k-1 by omega,
    show n-(k+1) = n-k-1 by omega, show n+(k+1) = n+k+1 by omega]
  have hnf : ((n-k)! : ℂ) = (n-k : ℂ) * (n-k-1)! := by
    conv_lhs => rw [show n-k = (n-k-1)+1 by omega, Nat.factorial_succ]
    push_cast [Nat.cast_sub (show 1 ≤ n-k by omega), Nat.cast_sub hk.le]
    ring
  have hpf : ((n+k)! : ℂ) = (n+k : ℂ) * (n+k-1)! := by
    conv_lhs => rw [show n+k = (n+k-1)+1 by omega, Nat.factorial_succ]
    push_cast [Nat.cast_sub (show 1 ≤ n+k by omega)]
    ring
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [hnf, hpf]
  have hsum : (n+k : ℂ) ≠ 0 := by exact_mod_cast (show n+k ≠ 0 by omega)
  push_cast [Nat.cast_sub hk.le]
  constructor
  · field_simp
  constructor <;> field_simp [hsum]
end DLMF.OrthogonalPolynomials.LegendreAddition
namespace DLMF.OrthogonalPolynomials.LegendreAddition
/-- The previous angular weight. -/
theorem weight_prev {n k : ℕ} (hk0 : 0 < k) (hk : k ≤ n) :
    weight n (k-1) = weight n k * (n+k) * (n-k+1) := by
  have hp : ((n+k)! : ℂ) = (n+k : ℂ) * (n+k-1)! := by
    conv_lhs => rw [show n+k = (n+k-1)+1 by omega, Nat.factorial_succ]
    push_cast [Nat.cast_sub (show 1 ≤ n+k by omega)]
    ring
  dsimp only [weight]
  rw [show n-(k-1) = n-k+1 by omega, show n+(k-1) = n+k-1 by omega,
    Nat.factorial_succ, hp]
  push_cast [Nat.cast_sub hk]
  have hsum : (n+k : ℂ) ≠ 0 := by exact_mod_cast (show n+k ≠ 0 by omega)
  field_simp [hsum]

/-- Degree and derivative neighbors at a positive angular index. -/
theorem jet_neighbors {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (x : ℂ) :
    jet (n+1) k x = x * jet n k x + (n+k)*jet n (k-1) x ∧
    jet (n-1) k x = x * jet n k x - ((n : ℂ)-k+1)*jet n (k-1) x ∧
    (1-x^2)*jet n (k+1) x = 2*k*x*jet n k x - (n+k)*((n : ℂ)-k+1)*jet n (k-1) x := by
  have hA := jet_raise n (k-1) x
  have hB := jet_lower (n-1) (k-1) x
  have hC := jet_ode n (k-1) x
  rw [show k-1+1 = k by omega] at hA hB hC
  rw [show k-1+2 = k+1 by omega] at hC
  rw [show n-1+1 = n by omega] at hB
  push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 1 ≤ n by omega)] at hA hB hC
  constructor
  · linear_combination hA
  constructor
  · linear_combination hB
  · linear_combination hC

/-- The bilinear algebra of the associated Legendre recurrence. -/
theorem bilinear_identity (n k x y u v U V : ℂ) (h0 : n-k ≠ 0) (h1 : n+k+1 ≠ 0) :
    (n+1)*(n-k+1)/(n+k+1) * (x*u+(n+k)*v)*(y*U+(n+k)*V) +
      n*(n+k)/(n-k) * (x*u-(n-k+1)*v)*(y*U-(n-k+1)*V) =
    (2*n+1) * (x*y*u*U + 1/2*((n+k)*(n-k+1)*v*V +
      (2*k*x*u-(n+k)*(n-k+1)*v)*(2*k*y*U-(n+k)*(n-k+1)*V)/((n-k)*(n+k+1)))) := by
  field_simp; ring

/-- The angular coefficient recurrence at an interior positive index. -/
theorem coeff_recurrence_interior {n k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (x y s t : ℂ) (hs : s^2 = 1-x^2) (ht : t^2 = 1-y^2) :
    (n+1)*coeff (n+1) k x y s t + n*coeff (n-1) k x y s t =
      (2*n+1)*(x*y*coeff n k x y s t + s*t/2*(coeff n (k-1) x y s t + coeff n (k+1) x y s t)) := by
  have hn : 0 < n := by omega
  have hx := jet_neighbors hn hk0 x
  have hy := jet_neighbors hn hk0 y
  have h0 : (n : ℂ)-k ≠ 0 := by
    rw [← Nat.cast_sub hk.le]
    exact Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hk).ne'
  have h1 : (n : ℂ)+k+1 ≠ 0 := by exact_mod_cast (n+k).succ_ne_zero
  have hh := bilinear_identity (n : ℂ) k x y (jet n k x) (jet n (k-1) x)
    (jet n k y) (jet n (k-1) y) h0 h1
  have hpx : (2*k*x*jet n k x - (n+k)*((n : ℂ)-k+1)*jet n (k-1) x) = s^2*jet n (k+1) x := by
    rw [hs]; exact hx.2.2.symm
  have hpy : (2*k*y*jet n k y - (n+k)*((n : ℂ)-k+1)*jet n (k-1) y) = t^2*jet n (k+1) y := by
    rw [ht]; exact hy.2.2.symm
  rw [hpx, hpy] at hh
  dsimp only [coeff]
  rw [(weight_shifts hk).1, (weight_shifts hk).2.1, (weight_shifts hk).2.2,
    weight_prev hk0 hk.le, hx.1, hx.2.1, hy.1, hy.2.1]
  have hp : (s*t)^(k+1) = (s*t)^(k-1)*(s*t)^2 := by
    rw [← pow_add]; congr 1; omega
  have hp0 : (s*t)^k = (s*t)^(k-1)*(s*t) := by
    rw [← pow_succ]; congr 1; omega
  rw [hp, hp0] at *
  linear_combination (weight n k * (s*t)^(k-1) * (s*t)) * hh
end DLMF.OrthogonalPolynomials.LegendreAddition
namespace DLMF.OrthogonalPolynomials.LegendreAddition
/-- The zero angular weight is one. -/
theorem weight_zero (n : ℕ) : weight n 0 = 1 := by
  simp [weight, Nat.cast_ne_zero.mpr n.factorial_ne_zero]
/-- The weight just below the top at the next degree. -/
theorem weight_succ_diag (n : ℕ) : weight (n+1) n = weight n n / (2*n+1) := by
  dsimp only [weight]
  rw [show n+1-n = 1 by omega, show n+1+n = (n+n)+1 by omega, Nat.sub_self]
  simp only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_one, Nat.cast_mul, Nat.cast_add]
  have hp : (2*n+1 : ℂ) ≠ 0 := by exact_mod_cast (show 2*n+1 ≠ 0 by omega)
  field_simp; ring
/-- The ratio of consecutive top weights. -/
theorem weight_succ_top (n : ℕ) :
    weight (n+1) (n+1) = weight n n / ((2*n+2)*(2*n+1)) := by
  dsimp only [weight]
  rw [Nat.sub_self, Nat.sub_self, show n+1+(n+1) = (n+n+1)+1 by omega]
  simp only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_one, Nat.cast_mul, Nat.cast_add]
  have hp : (2*n+1 : ℂ) ≠ 0 := by exact_mod_cast (show 2*n+1 ≠ 0 by omega)
  have hq : (2*n+2 : ℂ) ≠ 0 := by exact_mod_cast (show 2*n+2 ≠ 0 by omega)
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
/-- The next top derivative. -/
theorem jet_succ_top (n : ℕ) (z : ℂ) :
    jet (n+1) (n+1) z = (2*n+1) * jet n n z := by
  rw [jet_raise, jet_eq_zero (show n < n+1 by omega)]
  simp only [Pi.zero_apply, mul_zero, zero_add]
  ring
/-- The derivative just below the top. -/
theorem jet_below_top {n : ℕ} (hn : 0 < n) (z : ℂ) :
    jet n (n-1) z = z * jet n n z := by
  have hh := (jet_neighbors hn hn z).2.2
  rw [jet_eq_zero (show n < n+1 by omega)] at hh
  simp only [Pi.zero_apply, mul_zero] at hh
  have hne : (2*n : ℂ) ≠ 0 := by exact_mod_cast (show 2*n ≠ 0 by omega)
  apply mul_left_cancel₀ hne
  linear_combination hh
/-- Angular recurrence at the last nonzero index of the middle degree. -/
theorem coeff_recurrence_diag {n : ℕ} (hn : 0 < n) (x y s t : ℂ) :
    (n+1)*coeff (n+1) n x y s t + n*coeff (n-1) n x y s t =
      (2*n+1)*(x*y*coeff n n x y s t + s*t/2*(coeff n (n-1) x y s t + coeff n (n+1) x y s t)) := by
  rw [coeff_eq_zero (show n-1 < n by omega), coeff_eq_zero (show n < n+1 by omega)]
  have hnx : jet (n+1) n x = (2*n+1)*x*jet n n x := by
    rw [(jet_neighbors hn hn x).1, jet_below_top hn]
    ring
  have hny : jet (n+1) n y = (2*n+1)*y*jet n n y := by
    rw [(jet_neighbors hn hn y).1, jet_below_top hn]
    ring
  dsimp only [coeff]
  rw [weight_succ_diag, weight_prev hn le_rfl, hnx, hny, jet_below_top hn, jet_below_top hn]
  have hp : (s*t)^n = (s*t)^(n-1)*(s*t) := by rw [← pow_succ]; congr 1; omega
  rw [hp]
  have hne : (2*n+1 : ℂ) ≠ 0 := by exact_mod_cast (show 2*n+1 ≠ 0 by omega)
  field_simp; ring
/-- Angular recurrence at the new top index. -/
theorem coeff_recurrence_top (n : ℕ) (x y s t : ℂ) :
    (n+1)*coeff (n+1) (n+1) x y s t + n*coeff (n-1) (n+1) x y s t =
      (2*n+1)*(x*y*coeff n (n+1) x y s t + s*t/2*(coeff n n x y s t + coeff n (n+2) x y s t)) := by
  rw [coeff_eq_zero (show n-1 < n+1 by omega), coeff_eq_zero (show n < n+1 by omega),
    coeff_eq_zero (show n < n+2 by omega)]
  dsimp only [coeff]
  rw [weight_succ_top, jet_succ_top, jet_succ_top, pow_succ]
  have hne : (2*n+1 : ℂ) ≠ 0 := by exact_mod_cast (show 2*n+1 ≠ 0 by omega)
  have hne' : (2*n+2 : ℂ) ≠ 0 := by exact_mod_cast (show 2*n+2 ≠ 0 by omega)
  field_simp; ring
/-- Angular recurrence at index zero. -/
theorem coeff_recurrence_zero {n : ℕ} (hn : 0 < n) (x y s t : ℂ)
    (hs : s^2 = 1-x^2) (ht : t^2 = 1-y^2) :
    (n+1)*coeff (n+1) 0 x y s t + n*coeff (n-1) 0 x y s t =
      (2*n+1)*(x*y*coeff n 0 x y s t + s*t*coeff n 1 x y s t) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn1 : (n+1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hp (z : ℂ) : jet (n+1) 0 z = z*jet n 0 z - (1-z^2)*jet n 1 z/(n+1) := by
    have hh := (weighted_ladders n z).1
    rw [← jet_one] at hh
    change (1-z^2)*jet n 1 z = (n+1)*(z*jet n 0 z - jet (n+1) 0 z) at hh
    field_simp
    linear_combination hh
  have hm (z : ℂ) : jet (n-1) 0 z = z*jet n 0 z + (1-z^2)*jet n 1 z/n := by
    have hh := (weighted_ladders (n-1) z).2
    rw [show n-1+1 = n by omega, ← jet_one] at hh
    change (1-z^2)*jet n 1 z = ((n-1 : ℕ)+1)*(jet (n-1) 0 z-z*jet n 0 z) at hh
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)] at hh
    field_simp
    linear_combination -hh
  dsimp only [coeff]
  simp only [weight_zero, pow_zero, one_mul, pow_one]
  rw [(weight_shifts hn).2.2, weight_zero]
  simp only [Nat.cast_zero, sub_zero, add_zero]
  rw [hp, hp, hm, hm, ← hs, ← ht]
  field_simp; ring
end DLMF.OrthogonalPolynomials.LegendreAddition
namespace DLMF.OrthogonalPolynomials.LegendreAddition
/-- The positive-index coefficient recurrence, including the top and the zero tail. -/
theorem coeff_recurrence {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (x y s t : ℂ) (hs : s^2 = 1-x^2) (ht : t^2 = 1-y^2) :
    (n+1)*coeff (n+1) k x y s t + n*coeff (n-1) k x y s t =
      (2*n+1)*(x*y*coeff n k x y s t + s*t/2*(coeff n (k-1) x y s t + coeff n (k+1) x y s t)) := by
  rcases lt_trichotomy k n with h | h | h
  · exact coeff_recurrence_interior hk h x y s t hs ht
  · subst k; exact coeff_recurrence_diag hn x y s t
  · by_cases he : k = n+1
    · subst k
      simpa only [Nat.add_sub_cancel] using coeff_recurrence_top n x y s t
    · rw [coeff_eq_zero (show n+1 < k by omega), coeff_eq_zero (show n-1 < k by omega),
        coeff_eq_zero h, coeff_eq_zero (show n < k-1 by omega), coeff_eq_zero (show n < k+1 by omega)]
      ring

/-- The elementary cosine recurrence. -/
theorem cosine_step (k : ℕ) (phi : ℂ) :
    2*cos phi*cos ((k+1)*phi) = cos ((k+2)*phi) + cos (k*phi) := by
  have h0 := cos_add (((k : ℂ)+1)*phi) phi
  have h1 := cos_sub (((k : ℂ)+1)*phi) phi
  rw [show ((k : ℂ)+1)*phi+phi = (k+2)*phi by ring] at h0
  rw [show ((k : ℂ)+1)*phi-phi = k*phi by ring] at h1
  linear_combination -h0-h1

/-- Multiplication of a finite cosine sum by its first cosine. -/
theorem cosine_neighbor_sum (f : ℕ → ℂ) (n : ℕ) (phi : ℂ)
    (h1 : f (n+1) = 0) (h2 : f (n+2) = 0) :
    f 1 + ∑ k ∈ Finset.range (n+1), (f k + f (k+2)) * cos ((k+1)*phi) =
      cos phi * (f 0 + 2 * ∑ k ∈ Finset.range n, f (k+1)*cos ((k+1)*phi)) := by
  have hshift : f 1 + ∑ k ∈ Finset.range (n+1), f (k+2)*cos ((k+1)*phi) =
      ∑ k ∈ Finset.range n, f (k+1)*cos (k*phi) := by
    have hh := Finset.sum_range_succ' (fun k => f (k+1)*cos (k*phi)) (n+1)
    simp only [zero_add, Nat.cast_zero, zero_mul, cos_zero, mul_one] at hh
    rw [Finset.sum_range_succ, Finset.sum_range_succ, h1, h2, zero_mul, zero_mul, add_zero, add_zero] at hh
    simpa only [Nat.cast_add, Nat.cast_one, show ∀ k : ℕ, k+1+1 = k+2 by intro k; omega, add_comm] using hh.symm
  rw [Finset.sum_congr rfl (fun k _ => show (f k + f (k+2)) * cos ((k+1)*phi) =
    f k * cos ((k+1)*phi) + f (k+2)*cos ((k+1)*phi) by ring)]
  rw [Finset.sum_add_distrib]
  rw [show f 1 + ((∑ k ∈ Finset.range (n+1), f k*cos ((k+1)*phi)) +
      ∑ k ∈ Finset.range (n+1), f (k+2)*cos ((k+1)*phi)) =
      (∑ k ∈ Finset.range (n+1), f k*cos ((k+1)*phi)) +
        (f 1 + ∑ k ∈ Finset.range (n+1), f (k+2)*cos ((k+1)*phi)) by ring, hshift,
    Finset.sum_range_succ']
  simp only [zero_add, Nat.cast_zero, zero_add, one_mul]
  have he : (∑ k ∈ Finset.range n, f (k+1)*cos ((k+2)*phi)) +
      (∑ k ∈ Finset.range n, f (k+1)*cos (k*phi)) =
      2*cos phi * ∑ k ∈ Finset.range n, f (k+1)*cos ((k+1)*phi) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    linear_combination -(f (k+1)) * cosine_step k phi
  push_cast
  simp only [show ∀ k : ℂ, k+1+1 = k+2 by intro k; ring]
  linear_combination he

/-- The finite Legendre angular kernel. -/
def kernel (n : ℕ) (x y s t phi : ℂ) : ℂ :=
  coeff n 0 x y s t + 2*∑ k ∈ Finset.range n, coeff n (k+1) x y s t * cos ((k+1)*phi)
/-- A larger finite cutoff gives the same kernel. -/
theorem kernel_eq_sum (n N : ℕ) (hn : n ≤ N) (x y s t phi : ℂ) :
    kernel n x y s t phi = coeff n 0 x y s t +
      2*∑ k ∈ Finset.range N, coeff n (k+1) x y s t * cos ((k+1)*phi) := by
  rw [kernel, ← Finset.sum_range_add_sum_Ico _ hn]
  have hz : ∑ k ∈ Finset.Ico n N, coeff n (k+1) x y s t * cos ((k+1)*phi) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [coeff_eq_zero (by simp at hk; omega : n < k+1), zero_mul]
  rw [hz, add_zero]
end DLMF.OrthogonalPolynomials.LegendreAddition
namespace DLMF.OrthogonalPolynomials.LegendreAddition
/-- The angular kernel satisfies the Legendre degree recurrence. -/
theorem kernel_recurrence {n : ℕ} (hn : 0 < n) (x y s t phi : ℂ)
    (hs : s^2 = 1-x^2) (ht : t^2 = 1-y^2) :
    (n+1)*kernel (n+1) x y s t phi + n*kernel (n-1) x y s t phi =
      (2*n+1)*(x*y+s*t*cos phi)*kernel n x y s t phi := by
  have hzero := coeff_recurrence_zero hn x y s t hs ht
  have hsum :
      (∑ k ∈ Finset.range (n+1), ((n+1)*coeff (n+1) (k+1) x y s t + n*coeff (n-1) (k+1) x y s t) * cos ((k+1)*phi)) =
      ∑ k ∈ Finset.range (n+1), ((2*n+1)*(x*y*coeff n (k+1) x y s t + s*t/2*(coeff n k x y s t + coeff n (k+2) x y s t))) * cos ((k+1)*phi) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff_recurrence hn (show 0 < k+1 by omega) x y s t hs ht, Nat.add_sub_cancel]
  have hc := cosine_neighbor_sum (fun k => coeff n k x y s t) n phi
    (coeff_eq_zero (show n < n+1 by omega) _ _ _ _) (coeff_eq_zero (show n < n+2 by omega) _ _ _ _)
  have hcut : (∑ k ∈ Finset.range (n+1), coeff n (k+1) x y s t * cos ((k+1)*phi)) =
      ∑ k ∈ Finset.range n, coeff n (k+1) x y s t * cos ((k+1)*phi) := by
    rw [Finset.sum_range_succ, coeff_eq_zero (show n < n+1 by omega), zero_mul, add_zero]
  rw [kernel_eq_sum (n-1) (n+1) (by omega)]
  dsimp only [kernel] at *
  simp only [add_mul, mul_add, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hsum hc hcut ⊢
  rw [hcut] at hsum
  linear_combination hzero + 2*hsum + (2*n+1)*s*t*hc

/-- The first two angular kernels. -/
theorem kernel_initial (x y s t phi : ℂ) :
    kernel 0 x y s t phi = 1 ∧ kernel 1 x y s t phi = x*y+s*t*cos phi := by
  have h0 (z : ℂ) : jet 0 0 z = 1 := by simp [jet_zero, legendrePolyP_zero]
  have h1 (z : ℂ) : jet 1 0 z = z := by simp [jet_zero]
  have h11 (z : ℂ) : jet 1 1 z = 1 := by rw [jet_succ_top]; simp [h0]
  constructor
  · simp [kernel, coeff, weight_zero, h0]
  · norm_num [kernel, coeff, weight, h1, h11]
    ring

/-- The finite angular kernel is the Legendre polynomial of the inner product. -/
theorem legendre_eq_kernel (n : ℕ) (x y s t phi : ℂ)
    (hs : s^2 = 1-x^2) (ht : t^2 = 1-y^2) :
    legendrePolyP n (x*y+s*t*cos phi) = kernel n x y s t phi := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [(kernel_initial x y s t phi).1, legendrePolyP_zero]
    | 1 => rw [(kernel_initial x y s t phi).2, legendrePolyP_one]
    | n+2 =>
      have hp := legendrePolyP_recurrence n (x*y+s*t*cos phi)
      have hk := kernel_recurrence (n := n+1) (by omega) x y s t phi hs ht
      rw [show n+1-1 = n by omega] at hk
      rw [ih (n+1) (by omega), ih n (by omega)] at hp
      have hn : (n+2 : ℂ) ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
      apply mul_left_cancel₀ hn
      push_cast at hp hk
      linear_combination hp-hk
end DLMF.OrthogonalPolynomials.LegendreAddition
namespace DLMF.OrthogonalPolynomials.LegendreAddition
/-- The angular coefficient in the Jacobi normalization. -/
theorem coeff_eq_jacobi (n k : ℕ) (hk : k ≤ n) (x y s t : ℂ) :
    coeff n k x y s t =
      ((n-k)! : ℂ) * (n+k)! / (2^(2*k)*(n ! : ℂ)^2) * s^k * jacobiPolyP k k (n-k) x *
        t^k * jacobiPolyP k k (n-k) y := by
  have hf : (n ! : ℂ)*poch (n+1) k = (n+k)! := by
    simpa [poch] using factorial_mul_ascPochhammer ℂ n k
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hnk : ((n+k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n+k).factorial_ne_zero
  have hp : poch (n+1) k = (n+k)! / (n ! : ℂ) := by
    apply (eq_div_iff hn).2
    linear_combination hf
  dsimp only [coeff, weight]
  rw [jet_eq_jacobi n k hk, jet_eq_jacobi n k hk, hp, mul_pow,
    show (2 : ℂ)^(2*k) = (2^k)^2 by rw [Nat.mul_comm 2 k, pow_mul]]
  field_simp
end DLMF.OrthogonalPolynomials.LegendreAddition