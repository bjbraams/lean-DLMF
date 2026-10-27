/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import DLMF.Gamma.Polygamma
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Series expansions (DLMF §5.7)

The Weierstrass/digamma series 5.7.6 is `digamma_eq_tsum` in `Digamma.lean` (real) and
`digamma_eq_cDigammaSeries` in `Polygamma.lean` (complex); the expansions below use the
complex form.
The Taylor coefficients of `1/Γ` and the ζ-expansions of `log Γ` and `ψ` are
described here. The reciprocal Gamma Taylor series converges on all of `ℂ`;
the logarithmic and digamma expansions retain their disk and pole restrictions.
The alternating half-argument digamma series is grouped into absolutely summable pairs.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

/-- Taylor coefficients of `1/Γ` at zero, DLMF 5.7.1. -/
@[dlmf 5.7.E1]
def recipGammaCoeff (k : ℕ) : ℂ :=
  iteratedDeriv k (fun z : ℂ => (Complex.Gamma z)⁻¹) 0 / k.factorial

/-- The reciprocal Gamma Taylor series at zero converges at every complex argument. -/
@[dlmf 5.7.E1]
theorem hasSum_recipGammaCoeff (z : ℂ) :
    HasSum (fun k : ℕ => recipGammaCoeff k * z ^ k) (Complex.Gamma z)⁻¹ := by
  simpa [recipGammaCoeff, div_eq_mul_inv, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using
    Complex.hasSum_taylorSeries_of_entire Complex.differentiable_one_div_Gamma 0 z

/-- The ζ-expansion of `ψ(1+z) + γ` as a `HasSum`, from the complex digamma series
`digamma_eq_cDigammaSeries` by expanding each term geometrically and summing by columns. -/
theorem hasSum_digamma_one_add_zeta {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * z ^ (k + 1))
      (Complex.digamma (1 + z) + Real.eulerMascheroniConstant) := by
  have hre : -1 < z.re := by
    have := Complex.abs_re_le_norm z
    linarith [neg_abs_le z.re]
  have hU : 1 + z ∈ notNegNat := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [digamma_eq_cDigammaSeries hU, cDigammaSeries, neg_add_cancel_comm]
  set a : ℕ → ℕ → ℂ := fun n k => (-1 : ℂ) ^ k * z ^ (k + 1) / ((n : ℂ) + 1) ^ (k + 2)
    with ha
  have hn1 : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => by exact_mod_cast Nat.succ_ne_zero n
  have hnorm1 : ∀ n : ℕ, (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := fun n => by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos n
  -- summability of the double series
  have hsum : Summable (Function.uncurry a) := by
    have hg : Summable fun p : ℕ × ℕ =>
        (1 / ((p.1 : ℝ) + 1) ^ 2) * ‖z‖ ^ (p.2 + 1) := by
      have h1 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        exact_mod_cast (summable_nat_add_iff 1).mpr
          (Real.summable_one_div_nat_pow.mpr one_lt_two)
      have h2 : Summable fun k : ℕ => ‖z‖ ^ (k + 1) := by
        simpa [pow_succ] using
          (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right ‖z‖
      exact h1.mul_of_nonneg h2 (fun _ => by positivity) (fun _ => by positivity)
    refine hg.of_norm_bounded fun ⟨n, k⟩ => ?_
    simp only [Function.uncurry_apply_pair, ha, norm_div, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul]
    have hn : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := hnorm1 n
    rw [div_le_iff₀ (by positivity)]
    have hnn : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [hnn] at hn ⊢
    calc ‖z‖ ^ (k + 1) = 1 / ((n : ℝ) + 1) ^ 2 * ‖z‖ ^ (k + 1) * ((n : ℝ) + 1) ^ 2 := by
          field_simp
      _ ≤ 1 / ((n : ℝ) + 1) ^ 2 * ‖z‖ ^ (k + 1) * ((n : ℝ) + 1) ^ (k + 2) := by
          gcongr
          omega
  -- inner sums over `k`
  have hinner : ∀ n : ℕ, ∑' k : ℕ, a n k = cDigammaTerm n (1 + z) := by
    intro n
    have hq : ‖-z / ((n : ℂ) + 1)‖ < 1 := by
      rw [norm_div, norm_neg, div_lt_one (by linarith [hnorm1 n])]
      linarith [hnorm1 n]
    have hgeo := tsum_geometric_of_norm_lt_one hq
    have hz1 : 1 + z + n ≠ 0 := add_nat_ne_zero_of_not_neg_nat hU n
    have hne : (1 : ℂ) - -z / ((n : ℂ) + 1) = (1 + z + n) / ((n : ℂ) + 1) := by
      field_simp; ring
    have hterm : ∀ k : ℕ, a n k = z / ((n : ℂ) + 1) ^ 2 * (-z / ((n : ℂ) + 1)) ^ k := by
      intro k
      simp only [ha, div_pow, neg_pow z]
      field_simp
      ring
    simp_rw [hterm]
    rw [tsum_mul_left, hgeo, hne, cDigammaTerm]
    have := hn1 n
    field_simp
    ring
  have hrow : ∀ k : ℕ, ∑' n : ℕ, a n k =
      (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * z ^ (k + 1) := by
    intro k
    rw [show ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) by push_cast; ring,
      riemannZeta_nat_eq_tsum_succ (by omega), ← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext n
    simp only [ha, pow_add (-1 : ℂ) k 2]
    ring
  have hcol : Summable fun k : ℕ => ∑' n : ℕ, a n k := by
    simpa using hsum.prod_symm.prod
  simp_rw [← hinner, ← hrow]
  rw [← hsum.tsum_comm]
  exact hcol.hasSum

@[dlmf 5.7.E4]
theorem digamma_one_add_zeta {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.digamma (1 + z) =
      -Real.eulerMascheroniConstant +
        ∑' k : ℕ, (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * z ^ (k + 1) := by
  rw [(hasSum_digamma_one_add_zeta hz).tsum_eq]
  ring

/-! ### The recurrence for the coefficients of `1/Γ` and the ζ-series of `log Γ(1+z)` -/

/-- Absolute convergence inside the disc of convergence. -/
theorem summable_norm_mul_pow_of_summable {b : ℕ → ℂ} {r : ℝ} (e : ℕ)
    (h : ∀ w : ℂ, ‖w‖ < r → Summable fun n => b n * w ^ (n + e)) {z : ℂ} (hz : ‖z‖ < r) :
    Summable fun n => ‖b n * z ^ (n + e)‖ := by
  set ρ : ℝ := (‖z‖ + r) / 2 with hρ
  have hz0 := norm_nonneg z
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hzρ : ‖z‖ < ρ := by rw [hρ]; linarith
  have hs := h (ρ : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg hρ0.le, hρ]; linarith)
  obtain ⟨C, hC⟩ := (hs.tendsto_atTop_zero.norm.isBoundedUnder_le).eventually_le
  set q := ‖z‖ / ρ
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one hρ0).mpr hzρ
  have hg : Summable fun n : ℕ => C * q ^ (n + e) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hq0 hq1).mul_right _).mul_left _
  refine hg.of_norm_bounded_eventually_nat ?_
  filter_upwards [hC] with n hn
  rw [norm_norm, norm_mul, norm_pow]
  have h1 : ‖z‖ ^ (n + e) = ρ ^ (n + e) * q ^ (n + e) := by
    rw [← mul_pow]; congr 1; simp only [q]; field_simp
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0.le] at hn
  rw [h1, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hn (by positivity)

/-- Uniqueness of power-series coefficients. -/
theorem eq_zero_of_hasSum_pow {d : ℕ → ℂ} {r : ℝ} (hr : 0 < r) (h0 : d 0 = 0)
    (h : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → HasSum (fun n => d n * z ^ n) 0) (n : ℕ) : d n = 0 := by
  have h' : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => d n * z ^ n) 0 := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · convert hasSum_single (f := fun n => d n * (0 : ℂ) ^ n) 0 (fun m hm => by
        simp [zero_pow hm]) using 1
      simp [h0]
    · exact h z hz0 hz
  set p := FormalMultilinearSeries.ofScalars ℂ d
  set ρ : NNReal := ⟨r / 2, by positivity⟩
  have hρ : (ρ : ℝ) = r / 2 := rfl
  have hrad : (ρ : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_tendsto (l := 0) ?_
    have hs := (h' ((r / 2 : ℝ) : ℂ) (by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]; linarith)).summable
    convert hs.tendsto_atTop_zero.norm using 2 with n
    · rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), hρ]
    · simp
  have hp : HasFPowerSeriesOnBall (fun _ : ℂ => (0 : ℂ)) p 0 ρ :=
    { r_le := hrad
      r_pos := ENNReal.coe_pos.mpr (by rw [← NNReal.coe_pos, hρ]; positivity)
      hasSum := fun {y} hy => by
        have hy' : ‖y‖ < r := by
          rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe] at hy
          have : ‖y‖₊ < ρ := hy
          have : ‖y‖ < r / 2 := by exact_mod_cast this
          linarith
        simpa [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
          h' y hy' }
  have := hp.hasFPowerSeriesAt.eq_zero
  have hd := (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).mp this
  exact congrFun hd n

theorem differentiable_recip_Gamma' : Differentiable ℂ fun z : ℂ => (Complex.Gamma z)⁻¹ := by
  simpa [one_div] using Complex.differentiable_one_div_Gamma

theorem recipGammaCoeff_zero : recipGammaCoeff 0 = 0 := by
  simp [recipGammaCoeff, Complex.Gamma_zero]

/-- Taylor series of the derivative of `1/Γ`. -/
theorem hasSum_deriv_recipGamma (z : ℂ) :
    HasSum (fun k : ℕ => ((k : ℂ) + 1) * recipGammaCoeff (k + 1) * z ^ k)
      (deriv (fun w : ℂ => (Complex.Gamma w)⁻¹) z) := by
  have hd : Differentiable ℂ (deriv fun w : ℂ => (Complex.Gamma w)⁻¹) := by
    simpa [iteratedDeriv_one] using
      (differentiable_recip_Gamma'.contDiff (n := ⊤)).differentiable_iteratedDeriv 1
        (by exact_mod_cast WithTop.coe_lt_top _)
  convert Complex.hasSum_taylorSeries_of_entire hd 0 z using 1
  funext k
  rw [← iteratedDeriv_succ', recipGammaCoeff, sub_zero, smul_eq_mul, smul_eq_mul,
    Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  field_simp

/-- `z (1/Γ)'(z) = (1/Γ)(z) - z ψ(1+z) (1/Γ)(z)` in the punctured unit disc. -/
theorem mul_deriv_recipGamma {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    z * deriv (fun w : ℂ => (Complex.Gamma w)⁻¹) z =
      (Complex.Gamma z)⁻¹ - z * (Complex.digamma (1 + z) + Real.eulerMascheroniConstant) *
        (Complex.Gamma z)⁻¹ + Real.eulerMascheroniConstant * z * (Complex.Gamma z)⁻¹ := by
  have hs : ∀ m : ℕ, z ≠ -m := by
    intro m h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact hz0 (by simpa using h)
    · rw [h, norm_neg, Complex.norm_natCast] at hz
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hs
  have hd : HasDerivAt (fun w : ℂ => (Complex.Gamma w)⁻¹)
      (-deriv Complex.Gamma z / Complex.Gamma z ^ 2) z :=
    ((Complex.differentiableAt_Gamma z hs).hasDerivAt).inv hG
  rw [hd.deriv, add_comm 1 z, Complex.digamma_apply_add_one z hs, Complex.digamma_def,
    logDeriv_apply]
  field_simp
  ring

@[dlmf 5.7.E2]
theorem recipGammaCoeff_recurrence {k : ℕ} (hk : 1 < k) :
    (k - 1 : ℂ) * recipGammaCoeff k =
      Real.eulerMascheroniConstant * recipGammaCoeff (k - 1) -
        ∑ j ∈ Finset.Icc 2 (k - 1),
          (-1 : ℂ) ^ j * (riemannZeta j) * recipGammaCoeff (k - j) := by
  set c := recipGammaCoeff
  set γ : ℂ := (Real.eulerMascheroniConstant : ℂ)
  set a : ℕ → ℂ := fun m => (-1 : ℂ) ^ (m + 2) * riemannZeta (m + 2)
  set P4 : ℕ → ℂ := fun n =>
    if n < 2 then 0 else ∑ kl ∈ Finset.antidiagonal (n - 2), a kl.1 * c kl.2
  set P3 : ℕ → ℂ := fun n => if n = 0 then 0 else γ * c (n - 1)
  set D : ℕ → ℂ := fun n => n * c n - c n + P4 n - P3 n
  have hD : ∀ n, D n = 0 := by
    refine eq_zero_of_hasSum_pow one_pos (by simp [D, P4, P3, c, recipGammaCoeff_zero]) ?_
    intro z hz0 hz
    -- the four pieces
    have h1 : HasSum (fun n : ℕ => n * c n * z ^ n)
        (z * deriv (fun w : ℂ => (Complex.Gamma w)⁻¹) z) := by
      refine (hasSum_nat_add_iff' 1).mp ?_
      simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
      convert (hasSum_deriv_recipGamma z).mul_left z using 1
      funext n
      push_cast
      ring
    have h2 : HasSum (fun n : ℕ => c n * z ^ n) (Complex.Gamma z)⁻¹ := hasSum_recipGammaCoeff z
    have h3 : HasSum (fun n : ℕ => P3 n * z ^ n) (γ * z * (Complex.Gamma z)⁻¹) := by
      refine (hasSum_nat_add_iff' 1).mp ?_
      simp only [Finset.range_one, Finset.sum_singleton, P3, ↓reduceIte, zero_mul, sub_zero]
      convert ((hasSum_recipGammaCoeff z).mul_left (γ * z)) using 1
      funext n
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, c]
      ring
    have hA : Summable fun m => ‖a m * z ^ (m + 1)‖ :=
      summable_norm_mul_pow_of_summable 1
        (fun w hw => (hasSum_digamma_one_add_zeta hw).summable) hz
    have hC : Summable fun m => ‖c m * z ^ m‖ := by
      simpa using summable_norm_mul_pow_of_summable (r := ‖z‖ + 1) 0
        (fun w _ => by simpa using (hasSum_recipGammaCoeff w).summable) (by linarith)
    have hprod := (summable_norm_sum_mul_antidiagonal_of_summable_norm hA hC).of_norm.hasSum
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA hC,
      (hasSum_digamma_one_add_zeta hz).tsum_eq, (hasSum_recipGammaCoeff z).tsum_eq] at hprod
    have h4 : HasSum (fun n : ℕ => P4 n * z ^ n)
        (z * (Complex.digamma (1 + z) + γ) * (Complex.Gamma z)⁻¹) := by
      refine (hasSum_nat_add_iff' 2).mp ?_
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, P4,
        show (0 : ℕ) < 2 by norm_num, show (1 : ℕ) < 2 by norm_num, ↓reduceIte, zero_mul,
        add_zero, sub_zero]
      convert hprod.mul_left z using 1
      · funext n
        simp only [show ¬ n + 2 < 2 by omega, ↓reduceIte, Nat.add_sub_cancel, Finset.sum_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun kl hkl => ?_
        rw [Finset.mem_antidiagonal] at hkl
        rw [← hkl]
        ring
      · ring
    have htot := ((h1.sub h2).add h4).sub h3
    rw [mul_deriv_recipGamma hz0 hz] at htot
    convert htot using 1
    · funext n
      simp only [D]
      ring
    · ring
  have hk2 : k = (k - 2) + 2 := by omega
  have := hD k
  simp only [D, P4, P3, show ¬ k < 2 by omega, show k ≠ 0 by omega, ↓reduceIte] at this
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] at this
  simp only [Nat.sub_self, c, recipGammaCoeff_zero, mul_zero, add_zero] at this
  have hsum : ∑ j ∈ Finset.Icc 2 (k - 1), (-1 : ℂ) ^ j * (riemannZeta j) * recipGammaCoeff (k - j) =
      ∑ i ∈ Finset.range (k - 2), a i * recipGammaCoeff (k - 2 - i) := by
    rw [show Finset.Icc 2 (k - 1) = Finset.Ico 2 (k - 2 + 2) by
      ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [a]
    rw [show k - (2 + i) = k - 2 - i by omega]
    push_cast
    ring_nf
  rw [hsum]
  linear_combination this

/-- `0 ≤ ζ(k+2) - 1 ≤ 2^{-k}`, in norm. -/
theorem norm_riemannZeta_add_two_sub_one_le (k : ℕ) :
    ‖riemannZeta (k + 2) - 1‖ ≤ (1 / 2 : ℝ) ^ k := by
  have hz := riemannZeta_nat_eq_tsum_succ (p := k + 2) (by omega)
  push_cast at hz
  have hsr : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (k + 2) := by
    exact_mod_cast (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k + 2))
  have hs : Summable fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ (k + 2) := by
    refine Summable.of_norm ?_
    convert hsr using 2 with n
    rw [norm_div, norm_one, norm_pow]
    congr 2
    exact_mod_cast Complex.norm_natCast (n + 1)
  rw [hz, hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, one_pow, div_one, add_sub_cancel_left]
  have h2 : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2) ^ 2) (π ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simpa [Finset.sum_range_succ] using this
  refine (tsum_of_norm_bounded (h2.mul_left ((1 / 2 : ℝ) ^ k)) fun n => ?_).trans ?_
  · rw [norm_div, norm_one, norm_pow]
    have hn : ‖((n + 1 : ℕ) : ℂ) + 1‖ = (n : ℝ) + 2 := by
      rw [show ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast; ring
    rw [hn, pow_add]
    rw [show (1 : ℝ) / (((n : ℝ) + 2) ^ k * ((n : ℝ) + 2) ^ 2) =
      1 / ((n : ℝ) + 2) ^ k * (1 / ((n : ℝ) + 2) ^ 2) by rw [one_div_mul_one_div]]
    gcongr
    rw [one_div_pow]
    gcongr
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have := Real.pi_lt_d2
    have hπ : π ^ 2 / 6 - 1 ≤ 1 := by nlinarith [Real.pi_pos]
    calc (1 / 2 : ℝ) ^ k * (π ^ 2 / 6 - 1) ≤ (1 / 2 : ℝ) ^ k * 1 := by gcongr
      _ = _ := mul_one _

/-- The ζ-series in DLMF 5.7.3. -/
def logGammaZetaSeries (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ) ^ (k + 2) * (riemannZeta (k + 2) - 1) * z ^ (k + 2) / (k + 2)

theorem norm_logGammaZetaSeries_le {z : ℂ} (hz : ‖z‖ < 1) : ‖logGammaZetaSeries z‖ ≤ 1 := by
  have hg : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k * (1 / 2)) 1 := by
    convert hasSum_geometric_two.mul_right (1 / 2 : ℝ) using 1; norm_num
  refine tsum_of_norm_bounded hg fun k => ?_
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hk : ‖((k : ℂ) + 2)‖ = (k : ℝ) + 2 := by
    rw [show ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [hk, div_le_iff₀ (by positivity)]
  have h1 := norm_riemannZeta_add_two_sub_one_le k
  have h2 : ‖z‖ ^ (k + 2) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz.le
  have h3 : (1 : ℝ) ≤ ((k : ℝ) + 2) * (1 / 2) := by
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  calc ‖riemannZeta (k + 2) - 1‖ * ‖z‖ ^ (k + 2) ≤ (1 / 2 : ℝ) ^ k * 1 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ k * (((k : ℝ) + 2) * (1 / 2)) := by gcongr
    _ = _ := by ring

theorem hasDerivAt_logGammaZetaSeries {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt logGammaZetaSeries
      (Complex.digamma (1 + z) + Real.eulerMascheroniConstant - z / (1 + z)) z := by
  set e : ℕ → ℂ := fun k => (-1 : ℂ) ^ (k + 2) * (riemannZeta (k + 2) - 1)
  have hz' : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz
  have hd := hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => (1 / 2 : ℝ) ^ k)
    (g := fun k w => e k * w ^ (k + 2) / (k + 2)) (g' := fun k w => e k * w ^ (k + 1))
    (summable_geometric_two) Metric.isOpen_ball (convex_ball _ _).isPreconnected
    (fun k w _ => by
      have hk : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
      convert ((hasDerivAt_pow (k + 2) w).const_mul (e k)).div_const ((k : ℂ) + 2) using 1
      push_cast
      field_simp)
    (fun k w hw => by
      rw [norm_mul, norm_pow]
      have hw' : ‖w‖ < 1 := by simpa using hw
      have he : ‖e k‖ ≤ (1 / 2 : ℝ) ^ k := by
        simp only [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact norm_riemannZeta_add_two_sub_one_le k
      calc ‖e k‖ * ‖w‖ ^ (k + 1) ≤ (1 / 2 : ℝ) ^ k * 1 :=
            mul_le_mul he (pow_le_one₀ (norm_nonneg _) hw'.le) (by positivity) (by positivity)
        _ = _ := mul_one _)
    (Metric.mem_ball_self one_pos) (by simp) hz'
  have hgeo : HasSum (fun k : ℕ => (-1 : ℂ) ^ (k + 2) * z ^ (k + 1)) (z / (1 + z)) := by
    have hq : ‖-z‖ < 1 := by rwa [norm_neg]
    convert (hasSum_geometric_of_norm_lt_one hq).mul_left z using 1
    · funext k; rw [neg_pow, pow_succ]; ring
    · rw [sub_neg_eq_add, div_eq_mul_inv]
  have hs := (hasSum_digamma_one_add_zeta hz).sub hgeo
  have heq : ∑' k : ℕ, e k * z ^ (k + 1) =
      Complex.digamma (1 + z) + Real.eulerMascheroniConstant - z / (1 + z) := by
    rw [← hs.tsum_eq]; congr 1; funext k; simp only [e]; ring
  rw [← heq]
  exact hd

@[dlmf 5.7.E3]
theorem log_Gamma_one_add {z : ℂ} (hz : ‖z‖ < 1) :
    log (Complex.Gamma (1 + z)) =
      -log (1 + z) + z * (1 - Real.eulerMascheroniConstant) +
        ∑' k : ℕ, (-1 : ℂ) ^ (k + 2) * (riemannZeta (k + 2) - 1) * z ^ (k + 2) / (k + 2) := by
  set γ : ℂ := (Real.eulerMascheroniConstant : ℂ)
  set R : ℂ → ℂ := fun w => -log (1 + w) + w * (1 - γ) + logGammaZetaSeries w with hR
  change log (Complex.Gamma (1 + z)) = R z
  have hre : ∀ w : ℂ, ‖w‖ < 1 → 0 < (1 + w).re := fun w hw => by
    have := Complex.abs_re_le_norm w
    simp only [Complex.add_re, Complex.one_re]
    linarith [neg_abs_le w.re]
  have hpole : ∀ w : ℂ, ‖w‖ < 1 → ∀ m : ℕ, 1 + w ≠ -m := fun w hw m h => by
    have := hre w hw
    rw [h] at this
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hR' : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt R (Complex.digamma (1 + w)) w := by
    intro w hw
    have h1w : (1 : ℂ) + w ≠ 0 := fun h => by
      have := hre w hw; rw [h] at this; simp at this
    have hslit : (1 : ℂ) + w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (hre w hw))
    have hlog := ((hasDerivAt_id w).const_add 1).clog hslit
    have hlin := (hasDerivAt_id w).mul_const (1 - γ)
    convert (hlog.neg.add hlin).add (hasDerivAt_logGammaZetaSeries hw) using 1
    · funext v; simp only [R, id, Pi.add_apply, Pi.neg_apply]
    · simp only [id, γ]
      field_simp
      ring
  have hG : ∀ w : ℂ, ‖w‖ < 1 → Complex.Gamma (1 + w) ≠ 0 := fun w hw =>
    Complex.Gamma_ne_zero (hpole w hw)
  -- `exp R / Γ(1 + ·)` is constant on the disc
  set H : ℂ → ℂ := fun w => exp (R w) * (Complex.Gamma (1 + w))⁻¹
  have hH : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt H 0 w := by
    intro w hw
    have hΓ : HasDerivAt (fun v => Complex.Gamma (1 + v)) (deriv Complex.Gamma (1 + w)) w :=
      ((Complex.differentiableAt_Gamma _ (hpole w hw)).hasDerivAt).comp_const_add 1 w
    convert ((hR' w hw).cexp).mul (hΓ.inv (hG w hw)) using 1
    rw [Complex.digamma_def, logDeriv_apply]
    simp only [Pi.inv_apply]
    have := hG w hw
    field_simp
    ring
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖w‖ < 1 := fun w hw => by simpa using hw
  have hconst := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun w hw => (hH w (hball w hw)).differentiableAt.differentiableWithinAt)
    (fun w hw => (hH w (hball w hw)).deriv) (show z ∈ Metric.ball (0 : ℂ) 1 by simpa using hz)
    (Metric.mem_ball_self one_pos)
  have hR0 : R 0 = 0 := by simp [R, logGammaZetaSeries]
  have hexp : exp (R z) = Complex.Gamma (1 + z) := by
    have h1 : H z = 1 := by rw [hconst]; simp [H, hR0]
    have := hG z hz
    simp only [H] at h1
    field_simp at h1
    exact h1
  -- the imaginary part of `R z` lies in `(-π, π)`
  have him : |(R z).im| < π := by
    have ha : |arg (1 + z)| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hre z hz))
    have hγ1 := Real.one_half_lt_eulerMascheroniConstant
    have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
    have hb : |(z * (1 - γ)).im| ≤ 1 / 2 := by
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, show (1 : ℂ) - γ = ((1 - Real.eulerMascheroniConstant : ℝ) : ℂ) by
        push_cast; rfl, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      nlinarith [norm_nonneg z]
    have hc : |(logGammaZetaSeries z).im| ≤ 1 :=
      (Complex.abs_im_le_norm _).trans (norm_logGammaZetaSeries_le hz)
    have hR : (R z).im = -arg (1 + z) + (z * (1 - γ)).im + (logGammaZetaSeries z).im := by
      simp [R, Complex.log_im]
    rw [hR]
    have := Real.pi_gt_three
    calc |-arg (1 + z) + (z * (1 - γ)).im + (logGammaZetaSeries z).im|
        ≤ |arg (1 + z)| + |(z * (1 - γ)).im| + |(logGammaZetaSeries z).im| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ < π := by linarith
  rw [← hexp, Complex.log_exp (by linarith [(abs_lt.mp him).1]) (abs_lt.mp him).2.le]

@[dlmf 5.7.E5]
theorem digamma_one_add_odd_zeta {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hzm : z ≠ -1) :
    Complex.digamma (1 + z) =
      1 / (2 * z) - π / 2 * cot (π * z) + 1 / (z ^ 2 - 1) + 1 -
        Real.eulerMascheroniConstant -
        ∑' k : ℕ, (riemannZeta (2 * k + 3) - 1) * z ^ (2 * k + 2) := by
  -- the odd part, from the recurrence and reflection formulas
  have hzint : ∀ n : ℤ, z ≠ n := by
    intro n hn
    have hn' : ‖(n : ℂ)‖ < 1 := hn ▸ hz
    rw [Complex.norm_intCast] at hn'
    have : n = 0 := by
      have : |(n : ℝ)| < 1 := hn'
      exact_mod_cast (show (n : ℝ) = 0 by
        rcases abs_lt.mp this with ⟨h1, h2⟩
        have : (-1 : ℤ) < n := by exact_mod_cast h1
        have : n < 1 := by exact_mod_cast h2
        have : n = 0 := by omega
        exact_mod_cast this)
    exact hz0 (by rw [hn, this]; simp)
  have hnat : ∀ m : ℕ, z ≠ -(m : ℂ) := fun m h => hzint (-m) (by rw [h]; push_cast; ring)
  have hodd : Complex.digamma (1 + z) - Complex.digamma (1 - z) = 1 / z - π * cot (π * z) := by
    rw [Complex.digamma_one_sub hzint, add_comm, Complex.digamma_apply_add_one z hnat]
    ring
  -- the even part, from the ζ-expansion at `z` and `-z`
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have hsum := (hasSum_digamma_one_add_zeta hz).add (hasSum_digamma_one_add_zeta hz')
  rw [← sub_eq_add_neg] at hsum
  set c : ℕ → ℂ := fun j => -2 * (riemannZeta (2 * j + 3) * z ^ (2 * j + 2)) with hc
  have hF : (fun k : ℕ => (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * z ^ (k + 1) +
      (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * (-z) ^ (k + 1)) =
      Function.extend (fun j : ℕ => 2 * j + 1) c 0 := by
    funext k
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => by omega]
      simp [pow_succ, pow_mul, neg_pow z]
    · rw [(show Function.Injective fun j : ℕ => 2 * j + 1 from
        fun a b h => by simpa using h).extend_apply]
      simp only [hc]
      push_cast
      rw [show (2 * j + 1 + 2 : ℕ) = 2 * (j + 1) + 1 by ring, neg_pow z, pow_add (-1 : ℂ),
        pow_mul]
      ring_nf
      rw [show (-1 : ℂ) ^ (j * 2) = 1 from Even.neg_one_pow ⟨j, by ring⟩]
      ring
  rw [hF, hasSum_extend_zero (fun a b h => by simpa using h)] at hsum
  have hgeo : HasSum (fun j : ℕ => z ^ (2 * j + 2)) (z ^ 2 / (1 - z ^ 2)) := by
    have hz2 : ‖z ^ 2‖ < 1 := by
      rw [norm_pow]; nlinarith [norm_nonneg z]
    have := (hasSum_geometric_of_norm_lt_one hz2).mul_left (z ^ 2)
    simp_rw [← pow_mul, ← pow_add] at this
    convert this using 2
    · ring_nf
    · rw [div_eq_mul_inv]
  have heven := (hsum.div_const (-2)).sub hgeo
  have h1z : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : (1 - z) * (1 + z) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact hz1 (by linear_combination -h)
    · exact hzm (by linear_combination h)
  have hz2' : z ^ 2 - 1 ≠ 0 := fun h => h1z (by linear_combination -h)
  have htsum : ∑' k : ℕ, (riemannZeta (2 * k + 3) - 1) * z ^ (2 * k + 2) =
      (Complex.digamma (1 + z) + Real.eulerMascheroniConstant +
        (Complex.digamma (1 - z) + Real.eulerMascheroniConstant)) / -2 -
        z ^ 2 / (1 - z ^ 2) := by
    rw [← heven.tsum_eq]
    congr 1; funext j
    simp only [hc]
    ring
  have hB : Complex.digamma (1 - z) = Complex.digamma (1 + z) - (1 / z - π * cot (π * z)) := by
    linear_combination -hodd
  rw [htsum, hB]
  generalize cot (π * z) = C
  generalize Complex.digamma (1 + z) = D
  field_simp
  ring

/-- The half-argument digamma difference as an absolutely convergent series.
Adjacent terms of the classical alternating series are paired before taking `tsum`. -/
@[dlmf 5.7.E7]
theorem digamma_half_diff (z : ℂ) (hz : ∀ k : ℕ, z ≠ -k) :
    Complex.digamma ((z + 1) / 2) - Complex.digamma (z / 2) =
      2 * ∑' k : ℕ, (1 / (2 * k + z) - 1 / (2 * k + 1 + z)) := by
  have h1 : (z + 1) / 2 ∈ notNegNat := fun m h => hz (2 * m + 1) (by
    push_cast; linear_combination 2 * h)
  have h2 : z / 2 ∈ notNegNat := fun m h => hz (2 * m) (by
    push_cast; linear_combination 2 * h)
  rw [digamma_eq_cDigammaSeries h1, digamma_eq_cDigammaSeries h2, cDigammaSeries,
    cDigammaSeries, add_sub_add_left_eq_sub,
    ← (summable_cDigammaTerm h1).tsum_sub (summable_cDigammaTerm h2), ← tsum_mul_left]
  congr 1; funext k
  have ha : (2 * k + z : ℂ) ≠ 0 := fun h => hz (2 * k) (by
    push_cast; linear_combination h)
  have hb : (2 * k + 1 + z : ℂ) ≠ 0 := fun h => hz (2 * k + 1) (by
    push_cast; linear_combination h)
  have ha' : z / 2 + k ≠ 0 := fun h => ha (by linear_combination 2 * h)
  have hb' : (z + 1) / 2 + k ≠ 0 := fun h => hb (by linear_combination 2 * h)
  simp only [cDigammaTerm]
  field_simp
  ring

@[dlmf 5.7.E8]
theorem digamma_one_add_mul_I_im_series (y : ℝ) :
    (Complex.digamma (1 + I * y)).im = ∑' k : ℕ, y / ((k + 1 : ℝ) ^ 2 + y ^ 2) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Complex.digamma_one]
  have hx : (I * (y : ℂ)) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    simp at this
    exact hy this.symm
  have h := cot_series_rep' hx
  have hs : Summable fun n : ℕ => 1 / (I * (y : ℂ) - (n + 1)) + 1 / (I * (y : ℂ) + (n + 1)) :=
    summable_cotTerm hx
  have hcot := DLMF.Gamma.cot_pi_mul_I y hy
  have hsinh : (Real.sinh (π * y) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hL : ((π : ℂ) * cot (π * (I * y)) - 1 / (I * y)).im =
      1 / y - π * (Real.cosh (π * y) / Real.sinh (π * y)) := by
    rw [hcot]
    have : (π : ℂ) * (-I * (Real.cosh (π * y) / Real.sinh (π * y))) - 1 / (I * y) =
        ((1 / y - π * (Real.cosh (π * y) / Real.sinh (π * y)) : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      linear_combination (-1 : ℂ) * I_sq
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hterm : ∀ n : ℕ, (1 / (I * (y : ℂ) - (n + 1)) + 1 / (I * (y : ℂ) + (n + 1))).im =
      -2 * (y / ((n + 1 : ℝ) ^ 2 + y ^ 2)) := by
    intro n
    have hd : ((n + 1 : ℝ) ^ 2 + y ^ 2) ≠ 0 := by positivity
    have hd' : ((n : ℂ) + 1) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd
    have h1 : I * (y : ℂ) - (n + 1) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; exact hy this
    have h2 : I * (y : ℂ) + (n + 1) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; exact hy this
    have : 1 / (I * (y : ℂ) - (n + 1)) + 1 / (I * (y : ℂ) + (n + 1)) =
        ((-2 * (y / ((n + 1 : ℝ) ^ 2 + y ^ 2)) : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      linear_combination (2 * I * (y : ℂ) ^ 3) * I_sq
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him := congrArg Complex.im h
  rw [hL, Complex.im_tsum hs] at him
  simp_rw [hterm] at him
  rw [tsum_mul_left] at him
  rw [DLMF.Gamma.digamma_one_add_mul_I_im y hy]
  linear_combination (-1 / 2 : ℝ) * him

end DLMF.Gamma
