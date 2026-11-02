/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Generalizations.HigherOrder
public import Carlson.Elliptic.Addition

/-!
# Complex-order, degenerate and character Bernoulli numbers

This file covers the rest of DLMF §24.16: the generating function of the Nörlund polynomials of
complex order, the identity 24.16.8 for the degenerate Bernoulli numbers, and the Bernoulli
numbers and polynomials belonging to a Dirichlet character (§24.16(iii)).

## Main definitions

* `bernoulliChar χ n`: `B_{n,χ}` for a Dirichlet character `χ` modulo `f` (DLMF 24.16.10),
  by the closed form `B_{n,χ} = f^{n-1} ∑_{a=1}^{f} χ(a) Bₙ(a/f)`.
* `bernoulliCharPoly`: `B_{n,χ}(x)` (DLMF 24.16.11).
* `bernoulliGenFunLog`: a holomorphic logarithm of `t/(eᵗ - 1)` on `|t| < 2π`.

## Main results

* `degenerateBernoulli_eq`: DLMF 24.16.8.
* `hasSum_norlundPolynomial`, `hasSum_norlundPolynomial_real`: the generating function
  DLMF 24.16.9 for complex and for real order.
* `natDegree_norlundPolynomial`, `norlundPolynomial_eval_natCast`: `B_n^{(x)}` has degree `n`
  in `x` and agrees with `B_n^{(ℓ)}` at `x = ℓ` (DLMF §24.16(i)).
* `hasSum_bernoulliChar`: the generating function DLMF 24.16.10.
* `bernoulli_eq_bernoulliCharPoly_one`, `euler_eq_bernoulliCharPoly_chi4`: DLMF 24.16.12,
  24.16.13.

## Implementation notes

For the Nörlund polynomials of complex order (24.16.9) DLMF's power `(t/(eᵗ-1))^x` is the
branch analytic in `|t| < 2π` and equal to `1` at `0`; the principal power `cpow` agrees with
it only while `t/(eᵗ-1)` has not crossed the negative axis. Numerically the principal argument
stays below `π` for `|t| < 4.8`; 24.16.9 is stated for complex `x` and `0 < ‖t‖ < π`, and for
real `x` and real `0 < |t| < 2π` (where `t/(eᵗ-1) > 0`). It is proved from the holomorphic
logarithm `bernoulliGenFunLog` (a primitive of the logarithmic derivative): the Taylor
coefficients of `e^{xL}` are polynomials in `x` that agree with `B_n^{(ℓ)}` at `x = ℓ ∈ ℕ`.

The identity 24.16.8 is proved for real `0 < λ < 1/4` by writing `(1+λt)^{1/λ} = eᵘ`,
`u = ln(1+λt)/λ`, expanding `t/(eᵘ-1)` with 24.2.1, 24.16.5 and the Stirling generating
function 26.8.8 (`DLMF.Combinatorics.Stirling`), rearranging the absolutely convergent double
series and comparing coefficients with 24.16.7; agreement for infinitely many `λ` gives the
identity in `ℚ[λ]`.

DLMF requires `χ` primitive (with `f` its conductor); the definition of `bernoulliChar` and the
generating function 24.16.10 make sense, and are stated, for every `χ` modulo `f ≥ 1`. The
generating function is proved by summing Cauchy products of absolutely convergent series.

## References

* NIST DLMF §24.16; Nörlund (1924), Milne-Thomson (1933), Carlitz (1979), Berndt (1975a).
-/

@[expose] public noncomputable section

open Polynomial Finset Filter Topology

open scoped Nat Real

namespace DLMF.BernoulliEuler

/-! ### Helpers for 24.16.8: composing `t/(eᵘ-1)` with `u = ln(1+λt)/λ`

For real `0 < λ < 1/4` and real `0 < |t| < 1`, `(1+λt)^{1/λ} = eᵘ` and
`t/(eᵘ-1) = t/u + ∑_{m ≥ 0} t B_{m+1} u^m/(m+1)!`; expanding `u^m = λ^{-m} m! ∑ⱼ s(j,m)(λt)ʲ/j!`
(26.8.8) gives an absolutely convergent double series whose `tⁿ` coefficients are compared with
24.16.7. Agreement for infinitely many `λ` gives the polynomial identity. -/

section Degenerate
open DLMF.Combinatorics

/-- Coefficients of two real power series with the same sum on a punctured neighbourhood of `0`
are equal. -/
private lemma coeff_eq_of_hasSum_pow_eventually {a b : ℕ → ℝ} {f : ℝ → ℝ}
    (ha : ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum (fun n => a n * t ^ n) (f t))
    (hb : ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum (fun n => b n * t ^ n) (f t)) : a = b := by
  have hser : ∀ c : ℕ → ℝ, (∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum (fun n => c n * t ^ n) (f t)) →
      HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℝ c).sum
        (FormalMultilinearSeries.ofScalars ℝ c) 0 ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), (FormalMultilinearSeries.ofScalars ℝ c).sum t = f t := by
    intro c hc
    set P := FormalMultilinearSeries.ofScalars ℝ c
    have hsumP : ∀ t : ℝ, P.sum t = ∑' n, c n * t ^ n := fun t => by
      change FormalMultilinearSeries.ofScalarsSum _ t = _
      rw [FormalMultilinearSeries.ofScalars_sum_eq]; simp [smul_eq_mul]
    obtain ⟨t0, ht0, ht00⟩ := (hc.and self_mem_nhdsWithin).exists
    have hrad : ((‖t0‖₊ : NNReal) : ENNReal) ≤ P.radius := by
      refine P.le_radius_of_tendsto (l := 0) ?_
      have := ht0.summable.tendsto_atTop_zero.norm
      simpa [P, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using this
    have hpos : 0 < P.radius := lt_of_lt_of_le (by
      simpa [ENNReal.coe_pos, nnnorm_pos] using ht00) hrad
    refine ⟨(P.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt, ?_⟩
    filter_upwards [hc] with t ht
    rw [hsumP]; exact ht.tsum_eq
  obtain ⟨h1, e1⟩ := hser a ha
  obtain ⟨h2, e2⟩ := hser b hb
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℝ),
      (FormalMultilinearSeries.ofScalars ℝ a).sum z =
        (FormalMultilinearSeries.ofScalars ℝ b).sum z := by
    refine Eventually.frequently ?_
    filter_upwards [e1, e2] with z hz1 hz2
    rw [hz1, hz2]
  have hev := (h1.analyticAt.frequently_eq_iff_eventually_eq h2.analyticAt).mp hfr
  exact FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ
    (h1.eq_formalMultilinearSeries_of_eventually h2 hev)

/-- `u/(eᵘ - 1) = ∑ Bₙ uⁿ/n!` for real `0 < |u| < 2π`. -/
private lemma hasSum_bernoulli_mul_pow_div_real {u : ℝ} (hu : |u| < 2 * π) (hu0 : u ≠ 0) :
    HasSum (fun n : ℕ => (bernoulli n : ℝ) * u ^ n / n !) (u / (Real.exp u - 1)) := by
  have h := Complex.hasSum_bernoulli_mul_pow_div (z := (u : ℂ))
    (by rwa [Complex.norm_real, Real.norm_eq_abs]) (by exact_mod_cast hu0)
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · ext n; push_cast; rfl
  · push_cast; rfl

/-- `∑ |Bₙ| vⁿ/n!` converges for `0 ≤ v < 2π`. -/
private lemma summable_abs_bernoulli_mul_pow_div {v : ℝ} (hv0 : 0 ≤ v) (hv : v < 2 * π) :
    Summable (fun n : ℕ => |(bernoulli n : ℝ)| * v ^ n / n !) := by
  have hsum : ∀ z : ℂ, ‖z‖ < 2 * π →
      Summable (fun n => ((bernoulli n : ℂ) / n !) * z ^ n) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      exact (hasSum_single 0 (fun n hn => by simp [zero_pow hn])).summable
    · exact ((Complex.hasSum_bernoulli_mul_pow_div hz hz0).congr_fun
        fun n => by ring).summable
  have h := summable_norm_mul_pow_of_summable hsum (z := (v : ℂ))
    (by rwa [Complex.norm_real, Real.norm_of_nonneg hv0])
  refine h.congr fun n => ?_
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv0,
    Complex.norm_natCast, Complex.norm_ratCast]
  ring

/-- `∑ⱼ |s(j, m)| xʲ/j! = (-ln(1-x))^m/m!` for `|x| < 1`. -/
private lemma hasSum_stirlingFirst_mul_pow_div (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j : ℕ => (Nat.stirlingFirst j m : ℝ) * x ^ j / j !)
      ((-Real.log (1 - x)) ^ m / m !) := by
  have h := hasSum_signedStirlingFirst_div_factorial m (x := -x) (by rwa [abs_neg])
  have h2 := h.mul_left ((-1) ^ m)
  rw [show 1 + -x = 1 - x by ring] at h2
  convert h2 using 1
  · ext j
    rcases lt_or_ge j m with hjm | hjm
    · simp [Nat.stirlingFirst_eq_zero_of_lt hjm, signedStirlingFirst_eq_zero_of_lt hjm]
    · simp only [signedStirlingFirst, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, neg_pow x j]
      obtain ⟨d, rfl⟩ : ∃ d, j = m + d := ⟨j - m, by omega⟩
      rw [Nat.add_sub_cancel_left, pow_add]
      have : ((-1 : ℝ) ^ m) ^ 2 * ((-1) ^ d) ^ 2 = 1 := by
        rw [← pow_mul, ← pow_mul, mul_comm m 2, mul_comm d 2, pow_mul, pow_mul]; simp
      field_simp
      linear_combination (-(Nat.stirlingFirst (m + d) m : ℝ) * x ^ (m + d)) * this
  · rw [neg_pow]; ring

/-- `|ln(1+y)| ≤ |y|/(1-|y|)` for `|y| < 1`. -/
private lemma abs_log_one_add_le {y : ℝ} (hy : |y| < 1) : |Real.log (1 + y)| ≤ |y| / (1 - |y|) := by
  have h1 : 0 < 1 + y := by linarith [neg_abs_le y]
  have h2 : 0 < 1 - |y| := by linarith
  have hup := Real.log_le_sub_one_of_pos h1
  have hlo := Real.one_sub_inv_le_log_of_pos h1
  rw [abs_le]
  constructor
  · refine le_trans ?_ hlo
    have e : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
    rw [e]
    rcases le_or_gt 0 y with hy0 | hy0
    · have : 0 ≤ y / (1 + y) := div_nonneg hy0 h1.le
      have : 0 ≤ |y| / (1 - |y|) := div_nonneg (abs_nonneg _) h2.le
      linarith
    · rw [abs_of_neg hy0, show 1 - -y = 1 + y by ring, neg_div, neg_neg]
  · refine hup.trans ?_
    rw [le_div_iff₀ h2]
    nlinarith [le_abs_self y, abs_nonneg y]

/-- `0 ≤ -ln(1-x) ≤ x/(1-x)` for `0 ≤ x < 1`. -/
private lemma neg_log_one_sub_nonneg_and_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    0 ≤ -Real.log (1 - x) ∧ -Real.log (1 - x) ≤ x / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  refine ⟨neg_nonneg.mpr (Real.log_nonpos h1.le (by linarith)), ?_⟩
  have hlo := Real.one_sub_inv_le_log_of_pos h1
  rw [inv_eq_one_div, one_sub_div h1.ne'] at hlo
  rw [show x / (1 - x) = -((1 - x - 1) / (1 - x)) by ring]
  linarith

/-- The coefficients `e₀ = 0`, `e_{j+1} = (1/j!) ∑_{m ≤ j} (B_{m+1}/(m+1)) s(j, m) λ^{j-m}`. -/
noncomputable def degenerateBernoulliCorrection (l : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => (∑ m ∈ range (j + 1), (bernoulli (m + 1) : ℝ) / (m + 1) *
      (signedStirlingFirst j m : ℝ) * l ^ (j - m)) / j !

/-- For `0 < λ < 1/4` and `0 < |t| < 1`, with `u = ln(1+λt)/λ`,
`t/(eᵘ - 1) = ∑ₙ (bₙ λⁿ + eₙ) tⁿ`. -/
private lemma hasSum_bernoulliSecondKind_add_correction {l : ℝ} (hl0 : 0 < l) (hl : l < 1 / 4)
    {t : ℝ} (ht : |t| < 1)
    (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ =>
        ((bernoulliSecondKind n : ℝ) * l ^ n + degenerateBernoulliCorrection l n) * t ^ n)
      (t / (Real.exp (Real.log (1 + l * t) / l) - 1)) := by
  have hl' : l ≠ 0 := hl0.ne'
  set y := l * t with hy
  have hyabs : |y| = l * |t| := by rw [hy, abs_mul, abs_of_pos hl0]
  have hy4 : |y| < 1 / 4 := by
    rw [hyabs]; nlinarith [abs_nonneg t]
  have hy1 : |y| < 1 := by linarith
  have hy0 : y ≠ 0 := mul_ne_zero hl0.ne' ht0
  have hyp : 0 < |y| := abs_pos.mpr hy0
  have h1y : 0 < 1 + y := by linarith [neg_abs_le y]
  set L := Real.log (1 + y) with hLdef
  have hL0 : L ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one h1y (by
    intro h; exact hy0 (by linarith))
  set u := L / l with hu
  have hu0 : u ≠ 0 := div_ne_zero hL0 hl0.ne'
  have hpi : (4 : ℝ) / 3 < 2 * π := by linarith [Real.pi_gt_three]
  have hd : (3 : ℝ) / 4 < 1 - |y| := by linarith
  have hut : |t| / (1 - |y|) < 4 / 3 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith [abs_nonneg t]
  have hu2 : |u| < 2 * π := by
    rw [hu, abs_div, abs_of_pos hl0, div_lt_iff₀ hl0]
    have := abs_log_one_add_le hy1
    have h3 : |y| / (1 - |y|) = l * (|t| / (1 - |y|)) := by rw [hyabs]; ring
    rw [h3] at this
    nlinarith
  set W := -Real.log (1 - |y|) with hW
  obtain ⟨hW0, hW1⟩ := neg_log_one_sub_nonneg_and_le (abs_nonneg y) hy1
  have hWp : 0 < W := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
  set V := W / l with hV
  have hVp : 0 < V := div_pos hWp hl0
  have hV2 : V < 2 * π := by
    rw [hV, div_lt_iff₀ hl0]
    have h3 : |y| / (1 - |y|) = l * (|t| / (1 - |y|)) := by rw [hyabs]; ring
    rw [h3] at hW1
    nlinarith
  -- the double family
  set c : ℕ → ℝ := fun m => (bernoulli (m + 1) : ℝ) / (m + 1) with hc
  set F : ℕ × ℕ → ℝ := fun p => t * c p.1 / l ^ p.1 *
    ((signedStirlingFirst p.2 p.1 : ℝ) * y ^ p.2 / p.2 !) with hF
  have habsrow : ∀ m : ℕ, HasSum (fun j => |F (m, j)|) (|t| * |c m| / l ^ m * (W ^ m / m !)) := by
    intro m
    have h := (hasSum_stirlingFirst_mul_pow_div m (x := |y|) (by rwa [abs_abs])).mul_left
      (|t| * |c m| / l ^ m)
    refine h.congr_fun fun j => ?_
    simp only [hF, abs_mul, abs_div, abs_pow, abs_of_pos hl0, Nat.abs_cast]
    congr 2
    have e : ((Nat.stirlingFirst j m : ℕ) : ℝ) = |(signedStirlingFirst j m : ℝ)| := by
      rw [signedStirlingFirst]; push_cast
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    rw [e]
  have hrowsum : Summable fun m : ℕ => |t| * |c m| / l ^ m * (W ^ m / m !) := by
    have h0 := summable_abs_bernoulli_mul_pow_div hVp.le hV2
    have h1 := ((summable_nat_add_iff 1).mpr h0).mul_left (|t| / V)
    refine h1.congr fun m => ?_
    simp only [hc, abs_div, Nat.factorial_succ]
    rw [show W = V * l by rw [hV]; field_simp]
    have : |((m : ℝ) + 1)| = m + 1 := abs_of_pos (by positivity)
    rw [this]
    push_cast
    field_simp
    ring
  have hFabs : Summable fun p : ℕ × ℕ => |F p| := by
    refine (summable_prod_of_nonneg fun _ => abs_nonneg _).mpr
      ⟨fun m => (habsrow m).summable, ?_⟩
    simp_rw [fun m => (habsrow m).tsum_eq]
    exact hrowsum
  have hFs : Summable F := Summable.of_norm (by simpa only [Real.norm_eq_abs] using hFabs)
  -- row sums
  have hrow : ∀ m : ℕ, HasSum (fun j => F (m, j)) (t * c m / l ^ m * (L ^ m / m !)) := by
    intro m
    have h := (hasSum_signedStirlingFirst_div_factorial m (x := y) hy1).mul_left
      (t * c m / l ^ m)
    exact h
  have hR := hFs.hasSum.prod_fiberwise hrow
  have hBer := (hasSum_nat_add_iff' 1).mpr (hasSum_bernoulli_mul_pow_div_real hu2 hu0)
  have hBer2 := hBer.mul_left (t / u)
  have hS : ∑' p, F p = t / u * (u / (Real.exp u - 1) - 1) := by
    refine hR.unique (hBer2.congr_fun fun m => ?_) |>.trans ?_
    · simp only [hc, hu, Nat.factorial_succ, div_pow]
      push_cast
      field_simp
      ring
    · simp
  -- column sums
  have hC := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hFs.hasSum
  have hcol : ∀ j : ℕ, HasSum (fun m => F (m, j)) (∑ m ∈ range (j + 1), F (m, j)) := by
    intro j
    exact hasSum_sum_of_ne_finset_zero fun m hm => by
      rw [hF]; dsimp only
      rw [signedStirlingFirst_eq_zero_of_lt (by simp at hm; omega)]; simp
  have hC2 := hC.prod_fiberwise fun j => hcol j
  have hGj : ∀ j : ℕ, ∑ m ∈ range (j + 1), F (m, j) = degenerateBernoulliCorrection l (j + 1) *
      t ^ (j + 1) := by
    intro j
    simp only [degenerateBernoulliCorrection, sum_div, sum_mul]
    refine sum_congr rfl fun m hm => ?_
    have hmj : m ≤ j := by simp at hm; omega
    simp only [hF, hc, hy]
    obtain ⟨d, rfl⟩ : ∃ d, j = m + d := ⟨j - m, by omega⟩
    rw [Nat.add_sub_cancel_left]
    field_simp
    ring
  simp_rw [hGj] at hC2
  have hE : HasSum (fun n => degenerateBernoulliCorrection l n * t ^ n) (∑' p, F p) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simpa [degenerateBernoulliCorrection] using hC2
  -- second kind
  have hb2 := hasSum_bernoulliSecondKind (t := (y : ℂ))
    (by rwa [Complex.norm_real, Real.norm_eq_abs]) (by exact_mod_cast hy0)
  rw [show (1 : ℂ) + (y : ℂ) = ((1 + y : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log h1y.le] at hb2
  have hb3 : HasSum (fun n : ℕ => (bernoulliSecondKind n : ℝ) * l ^ n * t ^ n) (t / u) := by
    rw [← Complex.hasSum_ofReal]
    convert hb2 using 1
    · ext n; simp only [hy, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ratCast,
        mul_pow]; ring
    · simp only [hu, hLdef, hy, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv,
        mul_inv, inv_inv]; ring
  have htot := hb3.add hE
  rw [hS] at htot
  convert htot using 1
  · ext n; ring
  · have e : t / u * (u / (Real.exp u - 1)) = t / (Real.exp u - 1) := by
      rw [div_mul_div_comm, mul_comm t u, mul_div_mul_left _ _ hu0]
    rw [mul_sub, e]; ring

/-- 24.16.7 restricted to real `0 < λ` and real `t`. -/
private lemma hasSum_degenerateBernoulli_real {l : ℝ} (hl0 : 0 < l) (hl : l < 1 / 4) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum (fun n : ℕ => aeval l (degenerateBernoulli n) / n ! * t ^ n)
      (t / (Real.exp (Real.log (1 + l * t) / l) - 1)) := by
  have h := hasSum_degenerateBernoulli (lam := (l : ℂ)) (by exact_mod_cast hl0.ne')
  have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Complex.continuous_ofReal.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
      simpa using this
    · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
  have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [hT.eventually h, hball] with t ht ht1
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht1
  have h1 : 0 < 1 + l * t := by
    have : |l * t| < 1 := by
      rw [abs_mul, abs_of_pos hl0]; nlinarith [abs_nonneg t]
    linarith [neg_abs_le (l * t)]
  rw [← Complex.hasSum_ofReal]
  convert ht using 1
  · ext n
    have := aeval_algebraMap_apply ℂ l (degenerateBernoulli n)
    simp only [Complex.coe_algebraMap] at this
    push_cast
    rw [this]; ring
  · rw [show (1 : ℂ) + (l : ℂ) * (t : ℂ) = ((1 + l * t : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) / (l : ℂ) = ((1 / l : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow h1.le, Real.rpow_def_of_pos h1]
    push_cast
    ring_nf

/-- The reindexing of the Bernoulli–Stirling sum in 24.16.8. -/
private lemma sum_bernoulli_stirlingFirst_reindex {j : ℕ} (hj : 1 ≤ j) (l : ℝ) :
    ∑ k ∈ Icc 1 ((j + 1) / 2), ((j : ℝ) + 1) / (2 * k) * (bernoulli (2 * k) : ℝ) *
        ((-1) ^ (j + 1 - 2 * k) * (Nat.stirlingFirst j (2 * k - 1) : ℝ)) * l ^ (j + 1 - 2 * k) =
      ((j : ℝ) + 1) * ∑ m ∈ range (j + 1), (bernoulli (m + 1) : ℝ) / (m + 1) *
        (signedStirlingFirst j m : ℝ) * l ^ (j - m) := by
  set g : ℕ → ℝ := fun m => (bernoulli (m + 1) : ℝ) / (m + 1) *
    (signedStirlingFirst j m : ℝ) * l ^ (j - m) with hg
  have hinj : Set.InjOn (fun k : ℕ => 2 * k - 1) (Icc 1 ((j + 1) / 2) : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_Icc, Set.mem_Icc] at ha hb
    simp only at hab
    omega
  have hsub : (Icc 1 ((j + 1) / 2)).image (fun k : ℕ => 2 * k - 1) ⊆ range (j + 1) := by
    intro m hm
    simp only [mem_image, mem_Icc] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    simp only [mem_range]; omega
  rw [← sum_subset hsub, sum_image hinj, mul_sum]
  · refine sum_congr rfl fun k hk => ?_
    simp only [mem_Icc] at hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e2 : j - (2 * k + 1) = j + 1 - 2 * (k + 1) := by omega
    simp only [e1, e2, signedStirlingFirst]
    push_cast
    ring_nf
  · intro m hm hnot
    simp only [mem_range] at hm
    simp only [mem_image, mem_Icc, not_exists, not_and] at hnot
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp [signedStirlingFirst, Nat.stirlingFirst_succ_zero]
    · have hodd : Odd (m + 1) := by
        rcases Nat.even_or_odd (m + 1) with ⟨r, hr⟩ | h
        · exact (hnot r (by omega) (by omega)).elim
        · exact h
      simp [bernoulli_eq_zero_of_odd hodd (by omega)]

/-- The coefficient identity behind 24.16.8, for real `0 < λ < 1/4`. -/
private lemma aeval_degenerateBernoulli_div_factorial {l : ℝ} (hl0 : 0 < l)
    (hl : l < 1 / 4) (n : ℕ) :
    aeval l (degenerateBernoulli n) / n ! =
      (bernoulliSecondKind n : ℝ) * l ^ n + degenerateBernoulliCorrection l n := by
  have hm : ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasSum
      (fun n : ℕ => ((bernoulliSecondKind n : ℝ) * l ^ n +
          degenerateBernoulliCorrection l n) * t ^ n)
      (t / (Real.exp (Real.log (1 + l * t) / l) - 1)) := by
    have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [hball, self_mem_nhdsWithin] with t ht ht0
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    exact hasSum_bernoulliSecondKind_add_correction hl0 hl ht ht0
  exact congrFun (coeff_eq_of_hasSum_pow_eventually (hasSum_degenerateBernoulli_real hl0 hl) hm) n

end Degenerate
/-- DLMF 24.16.8: for `n ≥ 2`,
`βₙ(λ) = n! bₙ λⁿ + ∑_{k=1}^{⌊n/2⌋} (n/(2k)) B₂ₖ s(n-1, 2k-1) λ^{n-2k}`, with the signed
Stirling number `s(n-1, 2k-1) = (-1)^{n-2k} |s(n-1, 2k-1)|` (Mathlib's unsigned
`Nat.stirlingFirst`). -/
@[dlmf 24.16.E8]
theorem degenerateBernoulli_eq {n : ℕ} (hn : 2 ≤ n) :
    degenerateBernoulli n =
      C ((n ! : ℚ) * bernoulliSecondKind n) * X ^ n +
        ∑ k ∈ Icc 1 (n / 2), C ((n : ℚ) / (2 * k) * _root_.bernoulli (2 * k) *
          ((-1) ^ (n - 2 * k) * (Nat.stirlingFirst (n - 1) (2 * k - 1) : ℚ))) *
            X ^ (n - 2 * k) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hj : 1 ≤ j := by omega
  apply Polynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.Ioo_infinite (show (0 : ℝ) < 1 / 4 by norm_num))
  rintro l ⟨hl0, hl1⟩
  simp only [Set.mem_ofPred_eq, eval_map_algebraMap]
  have h := aeval_degenerateBernoulli_div_factorial hl0 hl1 (j + 1)
  rw [div_eq_iff (by positivity)] at h
  rw [h, Nat.add_sub_cancel]
  simp only [map_add, map_sum, map_mul, aeval_C, map_pow, aeval_X, eq_ratCast]
  push_cast
  rw [sum_bernoulli_stirlingFirst_reindex hj l, degenerateBernoulliCorrection, Nat.factorial_succ]
  push_cast
  field_simp

/-! ### Helpers for 24.16.9: a holomorphic logarithm of `t/(eᵗ-1)` on `|t| < 2π`

`H(t) = t/(eᵗ-1)` (with `H(0) = 1`) is holomorphic and zero-free on `|t| < 2π`, so `H'/H` has a
primitive `L` with `L(0) = 0` (Morera on a disk) and `e^L = H`. `F_x = e^{xL}` is holomorphic on
the disk, so its Taylor series at `0` converges there; its `n`-th derivative at `0` is a
polynomial in `x` which at `x = ℓ ∈ ℕ` equals `B_n^{(ℓ)}` (24.16.1), hence equals `B_n^{(x)}`.
On `|t| < π`, `H(t) = e^{-t/2} (t/2)/sinh(t/2)` is a product of two numbers with positive real
part, so it lies in the slit plane and `L = log H` there; for real `t` the same holds as `H > 0`.
-/

section NorlundSums
open Metric

/-- `t/(eᵗ - 1)`, with its limit `1` at `t = 0`. -/
noncomputable def bernoulliGenFun : ℂ → ℂ := Function.update (fun t => t / (Complex.exp t - 1)) 0 1

/-- Nonvanishing under the stated hypotheses: `Complex.exp t - 1 ≠ 0`. -/
private lemma exp_sub_one_ne_zero_of_norm_lt {t : ℂ} (ht : ‖t‖ < 2 * π) (ht0 : t ≠ 0) :
    Complex.exp t - 1 ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp h)
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn; exact ht0 hn
  rw [hn, norm_mul, norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one] at ht
  have : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  nlinarith [Real.pi_pos]

/-- Identity under the stated parameter and domain assumptions:
`bernoulliGenFun t = t / (Complex.exp t - 1)`. -/
private lemma bernoulliGenFun_of_ne_zero {t : ℂ} (ht0 : t ≠ 0) : bernoulliGenFun t = t /
    (Complex.exp t - 1) :=
  Function.update_of_ne ht0 _ _

/-- Identity under the stated parameter and domain assumptions: `bernoulliGenFun 0 = 1`. -/
private lemma bernoulliGenFun_zero : bernoulliGenFun 0 = 1 := Function.update_self _ _ _

/-- The map `(fun t : ℂ => t / (Complex.exp t - 1))` tends to `(𝓝 1)` along `(𝓝[≠] 0)`. -/
private lemma tendsto_div_exp_sub_one_nhdsNE_zero : Tendsto (fun t : ℂ => t / (Complex.exp t - 1))
    (𝓝[≠] 0) (𝓝 1) := by
  have h := (Complex.hasDerivAt_exp 0).tendsto_slope_zero
  simp only [zero_add, Complex.exp_zero, smul_eq_mul] at h
  have h2 := h.inv₀ one_ne_zero
  simp only [inv_one] at h2
  refine h2.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  simp [div_eq_mul_inv, mul_comm]

/-- Differentiability throughout the specified domain:
`DifferentiableOn ℂ bernoulliGenFun (ball 0 (2 * π))`. -/
private lemma differentiableOn_bernoulliGenFun : DifferentiableOn ℂ bernoulliGenFun
    (ball 0 (2 * π)) := by
  rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (ball_mem_nhds _ (by positivity))]
  refine ⟨fun t ht => ?_, ?_⟩
  · have ht0 : t ≠ 0 := ht.2
    have hb : ‖t‖ < 2 * π := by simpa using ht.1
    have hd : DifferentiableAt ℂ (fun t : ℂ => t / (Complex.exp t - 1)) t :=
      differentiableAt_id.div (Complex.differentiableAt_exp.sub_const 1)
        (exp_sub_one_ne_zero_of_norm_lt hb ht0)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [isOpen_ne.mem_nhds ht0] with z hz using bernoulliGenFun_of_ne_zero hz
  · rw [bernoulliGenFun, continuousAt_update_same]; exact tendsto_div_exp_sub_one_nhdsNE_zero

/-- Nonvanishing under the stated hypotheses: `bernoulliGenFun t ≠ 0`. -/
private lemma bernoulliGenFun_ne_zero {t : ℂ} (ht : ‖t‖ < 2 * π) : bernoulliGenFun t ≠ 0 := by
  by_cases ht0 : t = 0
  · rw [ht0, bernoulliGenFun_zero]; exact one_ne_zero
  · rw [bernoulliGenFun_of_ne_zero ht0];
        exact div_ne_zero ht0 (exp_sub_one_ne_zero_of_norm_lt ht ht0)

/-- Estimate under the stated parameter and domain assumptions: `6 ^ (n + 1) ≤ (2 * n + 3)!`. -/
private lemma six_pow_succ_le_factorial (n : ℕ) : 6 ^ (n + 1) ≤ (2 * n + 3)! := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 2 * (n + 1) + 3 = (2 * n + 3 + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, pow_succ]
    calc 6 ^ (n + 1) * 6 ≤ (2 * n + 3)! * ((2 * n + 3 + 1 + 1) * (2 * n + 3 + 1)) :=
          Nat.mul_le_mul ih (by nlinarith)
      _ = _ := by ring

/-- `‖sinh w - w‖ < ‖w‖` for `0 < ‖w‖ < π/2`. -/
private lemma norm_sinh_sub_self_lt {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ < π / 2) :
    ‖Complex.sinh w - w‖ < ‖w‖ := by
  set r := ‖w‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr hw0
  set ρ := r ^ 2 / 6 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 / 2 := by
    have := Real.pi_lt_d2
    rw [hρ]; nlinarith
  have hs := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_sinh w)
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, zero_add, pow_one,
    Nat.factorial_one, Nat.cast_one, div_one] at hs
  have hg := (hasSum_geometric_of_lt_one hρ0 (by linarith)).mul_left (r * ρ)
  have hb : ∀ n : ℕ, ‖w ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1)! : ℂ)‖ ≤ r * ρ * ρ ^ n := by
    intro n
    rw [norm_div, norm_pow, Complex.norm_natCast, ← hr,
      show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    rw [div_le_iff₀ (by positivity)]
    have h6 : ((6 : ℝ) ^ (n + 1)) ≤ ((2 * n + 3)! : ℝ) := by
                                                            exact_mod_cast six_pow_succ_le_factorial
                                                              n
    have : r * ρ * ρ ^ n = r ^ (2 * n + 3) / 6 ^ (n + 1) := by
      rw [hρ, div_pow, ← pow_mul]; field_simp; ring
    rw [this, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left h6 (by positivity)
  have hle := hs.norm_le_of_bounded hg hb
  calc ‖Complex.sinh w - w‖ ≤ r * ρ * (1 - ρ)⁻¹ := hle
    _ < r := by
      rw [mul_assoc]
      refine mul_lt_of_lt_one_right hr0 ?_
      rw [← div_eq_mul_inv, div_lt_one (by linarith)]; linarith

/-- Formula under the stated hypotheses: `bernoulliGenFun t ∈ Complex.slitPlane`. -/
private lemma bernoulliGenFun_mem_slitPlane {t : ℂ} (ht : ‖t‖ < π) : bernoulliGenFun t ∈
    Complex.slitPlane := by
  by_cases ht0 : t = 0
  · rw [ht0, bernoulliGenFun_zero]; exact Complex.one_mem_slitPlane
  rw [bernoulliGenFun_of_ne_zero ht0]
  set w := t / 2 with hw
  have hw0 : w ≠ 0 := div_ne_zero ht0 two_ne_zero
  have hwn : ‖w‖ < π / 2 := by
    rw [hw, norm_div, Complex.norm_ofNat]; linarith
  have hsh : Complex.exp t - 1 = 2 * Complex.exp w * Complex.sinh w := by
    have e1 : Complex.exp t = Complex.exp w * Complex.exp w := by
      rw [← Complex.exp_add, hw, add_halves]
    have e2 : Complex.exp w * Complex.exp (-w) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    rw [Complex.sinh, e1]; linear_combination e2
  have hne := exp_sub_one_ne_zero_of_norm_lt (show ‖t‖ < 2 * π by linarith [Real.pi_pos]) ht0
  have hsinh : Complex.sinh w ≠ 0 := by
    intro h; rw [hsh, h, mul_zero] at hne; exact hne rfl
  have heq : t / (Complex.exp t - 1) = Complex.exp (-w) * (Complex.sinh w / w)⁻¹ := by
    rw [hsh, inv_div, Complex.exp_neg]
    have : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
    rw [hw]; field_simp
  rw [heq]
  refine Carlson.mul_mem_slitPlane_of_re_pos ?_ ?_
  · rw [Complex.exp_re]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;>
    · have := Complex.abs_im_le_norm (-w)
      rw [norm_neg] at this
      rw [abs_le] at this; linarith [this.1, this.2]
  · set q := Complex.sinh w / w
    have hq : ‖q - 1‖ < 1 := by
      rw [show q - 1 = (Complex.sinh w - w) / w by rw [div_sub_one hw0], norm_div,
        div_lt_one (norm_pos_iff.mpr hw0)]
      exact norm_sinh_sub_self_lt hw0 hwn
    have hqre : 0 < q.re := by
      have := Complex.abs_re_le_norm (q - 1)
      rw [Complex.sub_re, Complex.one_re, abs_le] at this; linarith [this.1]
    rw [Complex.inv_re]
    exact div_pos hqre (Complex.normSq_pos.mpr fun h => by rw [h] at hqre; simp at hqre)

/-- The logarithmic derivative `H'/H`. -/
noncomputable def bernoulliGenFunLogDeriv (t : ℂ) : ℂ := deriv bernoulliGenFun t / bernoulliGenFun t

/-- Differentiability throughout the specified domain:
`DifferentiableOn ℂ bernoulliGenFunLogDeriv (ball 0 (2 * π))`. -/
private lemma differentiableOn_bernoulliGenFunLogDeriv : DifferentiableOn ℂ bernoulliGenFunLogDeriv
    (ball 0 (2 * π)) :=
  (differentiableOn_bernoulliGenFun.deriv isOpen_ball).div differentiableOn_bernoulliGenFun
    fun t ht => bernoulliGenFun_ne_zero (by simpa using ht)

/-- Formula under the stated hypotheses: `∃ L : ℂ → ℂ, L 0 = 0 ∧ ∀ t ∈ ball (0 : ℂ) (2 * π),
HasDerivAt L (bernoulliGenFunLogDeriv t) t`. -/
lemma exists_hasDerivAt_bernoulliGenFunLogDeriv : ∃ L : ℂ → ℂ, L 0 = 0 ∧
    ∀ t ∈ ball (0 : ℂ) (2 * π), HasDerivAt L (bernoulliGenFunLogDeriv t) t :=
  differentiableOn_bernoulliGenFunLogDeriv.isExactOn_ball.with_val_at 0 0

/-- A holomorphic logarithm of `t/(eᵗ - 1)` on `|t| < 2π`, vanishing at `0`. -/
noncomputable def bernoulliGenFunLog : ℂ → ℂ := exists_hasDerivAt_bernoulliGenFunLogDeriv.choose

/-- Identity under the stated parameter and domain assumptions: `bernoulliGenFunLog 0 = 0`. -/
private lemma bernoulliGenFunLog_zero : bernoulliGenFunLog 0 = 0 :=
    exists_hasDerivAt_bernoulliGenFunLogDeriv.choose_spec.1

/-- At `t`, the function `bernoulliGenFunLog` has derivative `(bernoulliGenFunLogDeriv t)`. -/
private lemma hasDerivAt_bernoulliGenFunLog {t : ℂ} (ht : t ∈ ball (0 : ℂ) (2 * π)) :
    HasDerivAt bernoulliGenFunLog (bernoulliGenFunLogDeriv t) t :=
  exists_hasDerivAt_bernoulliGenFunLogDeriv.choose_spec.2 t ht

/-- Identity under the stated parameter and domain assumptions:
`Complex.exp (bernoulliGenFunLog t) = bernoulliGenFun t`. -/
private lemma exp_bernoulliGenFunLog {t : ℂ} (ht : t ∈ ball (0 : ℂ) (2 * π)) :
    Complex.exp (bernoulliGenFunLog t) = bernoulliGenFun t := by
  set g := fun z => bernoulliGenFun z * Complex.exp (-bernoulliGenFunLog z)
  have hd : ∀ z ∈ ball (0 : ℂ) (2 * π), HasDerivAt g 0 z := by
    intro z hz
    have hH := (differentiableOn_bernoulliGenFun.differentiableAt
        (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hE := ((hasDerivAt_bernoulliGenFunLog hz).neg).cexp
    convert hH.mul hE using 1
    have := bernoulliGenFun_ne_zero (by simpa using hz : ‖z‖ < 2 * π)
    simp only [bernoulliGenFunLogDeriv]; field_simp; ring
  have hc := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) ht (mem_ball_self (by positivity))
  simp only [g, bernoulliGenFunLog_zero, Complex.exp_zero, bernoulliGenFun_zero,
    Complex.exp_neg, inv_one, mul_one] at hc
  exact ((mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp hc).symm

/-- Differentiability throughout the specified domain: `DifferentiableOn ℂ (fun z => Complex.exp
(x * bernoulliGenFunLog z)) (ball 0 (2 * π))`. -/
private lemma differentiableOn_exp_mul_bernoulliGenFunLog (x : ℂ) :
    DifferentiableOn ℂ (fun z => Complex.exp (x * bernoulliGenFunLog z)) (ball 0 (2 * π)) :=
  fun _ hz => (((hasDerivAt_bernoulliGenFunLog hz).differentiableAt.const_mul
      x).cexp).differentiableWithinAt

/-- Formula under the stated hypotheses: `∃ c : ℕ → ℂ → ℂ, (∀ k, DifferentiableOn ℂ (c k) (ball 0
(2 * π))) ∧ ∀ x : ℂ, ∀ t ∈ ball (0 : ℂ) (2 * π), iteratedDeriv n (fun z => Complex.exp (x *
bernoulliGenFunLog z)) t = (∑ k ∈ range (n + 1), x ^ k * c k t) * Complex.exp (x *
bernoulliGenFunLog t)`. -/
private lemma iteratedDeriv_exp_mul_bernoulliGenFunLog_eq_sum (n : ℕ) : ∃ c : ℕ → ℂ → ℂ,
    (∀ k, DifferentiableOn ℂ (c k) (ball 0 (2 * π))) ∧
    ∀ x : ℂ, ∀ t ∈ ball (0 : ℂ) (2 * π),
      iteratedDeriv n (fun z => Complex.exp (x * bernoulliGenFunLog z)) t =
        (∑ k ∈ range (n + 1), x ^ k * c k t) * Complex.exp (x * bernoulliGenFunLog t) := by
  induction n with
  | zero => exact ⟨fun _ _ => 1, fun _ => differentiableOn_const _, fun x t _ => by simp⟩
  | succ n ih =>
    obtain ⟨c, hc, hF⟩ := ih
    refine ⟨fun k t => (if k = n + 1 then 0 else deriv (c k) t) +
      (if k = 0 then 0 else bernoulliGenFunLogDeriv t * c (k - 1) t), fun k => ?_, fun x t ht => ?_⟩
    · refine DifferentiableOn.add ?_ ?_
      · split_ifs
        · exact differentiableOn_const _
        · exact (hc k).deriv isOpen_ball
      · split_ifs
        · exact differentiableOn_const _
        · exact differentiableOn_bernoulliGenFunLogDeriv.mul (hc (k - 1))
    · rw [iteratedDeriv_succ]
      have hev : iteratedDeriv n (fun z => Complex.exp (x * bernoulliGenFunLog z)) =ᶠ[𝓝 t]
          fun z => (∑ k ∈ range (n + 1), x ^ k * c k z) *
              Complex.exp (x * bernoulliGenFunLog z) := by
        filter_upwards [isOpen_ball.mem_nhds ht] with z hz using hF x z hz
      rw [hev.deriv_eq]
      have hS : HasDerivAt (fun z => ∑ k ∈ range (n + 1), x ^ k * c k z)
          (∑ k ∈ range (n + 1), x ^ k * deriv (c k) t) t := by
        refine HasDerivAt.fun_sum fun k _ => ?_
        exact ((hc k).differentiableAt (isOpen_ball.mem_nhds ht)).hasDerivAt.const_mul _
      have hE : HasDerivAt (fun z => Complex.exp (x * bernoulliGenFunLog z))
          (Complex.exp (x * bernoulliGenFunLog t) * (x * bernoulliGenFunLogDeriv t)) t :=
        ((hasDerivAt_bernoulliGenFunLog ht).const_mul x).cexp
      rw [(hS.fun_mul hE).deriv]
      have key : ∑ k ∈ range (n + 1 + 1), x ^ k * ((if k = n + 1 then 0 else deriv (c k) t) +
          (if k = 0 then 0 else bernoulliGenFunLogDeriv t * c (k - 1) t)) =
          ∑ k ∈ range (n + 1), x ^ k * deriv (c k) t +
            x * bernoulliGenFunLogDeriv t * ∑ k ∈ range (n + 1), x ^ k * c k t := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        · rw [sum_range_succ, ite_eq_left (rfl : n + 1 = n + 1), mul_zero, add_zero]
          exact sum_congr rfl fun k hk => by rw [ite_eq_right_iff.mpr (by simp at hk; omega)]
        · rw [sum_range_succ', mul_sum]
          simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, ite_true, mul_zero,
            add_zero]
          exact sum_congr rfl fun k _ => by ring
      rw [key]; ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun z =>
Complex.exp ((ℓ : ℂ) * bernoulliGenFunLog z)) 0 = (((norlundPolynomial n).eval (ℓ : ℚ) : ℚ) :
ℂ)`. -/
private lemma iteratedDeriv_exp_natCast_mul_bernoulliGenFunLog_zero (ℓ n : ℕ) :
    iteratedDeriv n (fun z => Complex.exp ((ℓ : ℂ) * bernoulliGenFunLog z)) 0 =
      (((norlundPolynomial n).eval (ℓ : ℚ) : ℚ) : ℂ) := by
  have hev : (fun z => Complex.exp ((ℓ : ℂ) * bernoulliGenFunLog z)) =ᶠ[𝓝 0] fun z =>
      bernoulliGenFun z ^ ℓ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show (0 : ℝ) < 2 * π by positivity))]
      with z hz
    rw [Complex.exp_nat_mul, exp_bernoulliGenFunLog hz]
  rw [hev.iteratedDeriv_eq]
  set c : ℕ → ℂ := fun n => aeval (0 : ℂ) (bernoulliOrder ℓ n) / (n ! : ℂ)
  have h0 : ∀ m, aeval (0 : ℂ) (bernoulliOrder ℓ m) = ((bernoulliNumberOrder ℓ m : ℚ) : ℂ) := by
    intro m
    rw [show (0 : ℂ) = algebraMap ℚ ℂ 0 by simp, aeval_algebraMap_apply_eq_algebraMap_eval,
      bernoulliOrder_eval_zero]
    rfl
  have hsum : ∀ y : ℂ, ‖y‖ < 2 * π → HasSum (fun n => c n * y ^ n) (bernoulliGenFun y ^ ℓ) := by
    intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      rw [bernoulliGenFun_zero, one_pow]
      convert hasSum_single (f := fun n => c n * (0 : ℂ) ^ n) 0
        (fun n (hn : n ≠ 0) => by simp only [zero_pow hn, mul_zero]) using 1
      show (1 : ℂ) = aeval 0 (bernoulliOrder ℓ 0) / ((0 ! : ℕ) : ℂ) * 0 ^ 0
      rw [h0, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one,
        bernoulliNumberOrder_eq_factorial_mul_coeff]
      simp [bernoulliPowerSeries]
    · have := hasSum_bernoulliOrder ℓ 0 hy hy0
      simp only [zero_mul, Complex.exp_zero, mul_one] at this
      rw [bernoulliGenFun_of_ne_zero hy0]
      exact this.congr_fun fun n => by simp only [c]; ring
  set p := FormalMultilinearSeries.ofScalars ℂ c
  have hrad : (1 : ENNReal) ≤ p.radius := by
    have h1 := (hsum 1 (by simp; linarith [Real.pi_gt_three])).summable.tendsto_atTop_zero
    have := p.le_radius_of_tendsto (r := 1) (l := 0) ?_
    · simpa using this
    simp only [NNReal.coe_one, one_pow, mul_one, p, FormalMultilinearSeries.ofScalars_norm]
    simpa using h1.norm
  have hp : HasFPowerSeriesOnBall (fun z => bernoulliGenFun z ^ ℓ) p 0 1 :=
    { r_le := hrad
      r_pos := one_pos
      hasSum := fun {y} hy => by
        rw [zero_add]
        have hy' : ‖y‖ < 2 * π := by
          have : ‖y‖ < 1 := by
            simpa [← ofReal_norm] using hy
          linarith [Real.pi_gt_three]
        simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
        exact hsum y hy' }
  rw [iteratedDeriv_eq_iteratedFDeriv, ← hp.factorial_smul 1 n,
    FormalMultilinearSeries.ofScalars_apply_eq]
  simp only [c, h0, one_pow, smul_eq_mul, mul_one, nsmul_eq_mul]
  have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp
  rfl

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun z =>
Complex.exp (x * bernoulliGenFunLog z)) 0 = aeval x (norlundPolynomial n)`. -/
private lemma iteratedDeriv_exp_mul_bernoulliGenFunLog_zero (x : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => Complex.exp (x * bernoulliGenFunLog z)) 0 =
        aeval x (norlundPolynomial n) := by
  obtain ⟨c, -, hF⟩ := iteratedDeriv_exp_mul_bernoulliGenFunLog_eq_sum n
  have h0 : ∀ y : ℂ, iteratedDeriv n (fun z => Complex.exp (y * bernoulliGenFunLog z)) 0 =
      ∑ k ∈ range (n + 1), y ^ k * c k 0 := by
    intro y
    rw [hF y 0 (mem_ball_self (by positivity)), bernoulliGenFunLog_zero, mul_zero,
        Complex.exp_zero, mul_one]
  set P : ℂ[X] := ∑ k ∈ range (n + 1), C (c k 0) * X ^ k
  have hP : ∀ y, P.eval y = ∑ k ∈ range (n + 1), y ^ k * c k 0 := by
    intro y
    simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact sum_congr rfl fun k _ => mul_comm _ _
  have hQ : P = (norlundPolynomial n).map (algebraMap ℚ ℂ) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun ℓ : ℕ => (ℓ : ℂ)) Nat.cast_injective
      fun ℓ => ?_
    simp only [Set.mem_ofPred_eq]
    rw [hP, ← h0, iteratedDeriv_exp_natCast_mul_bernoulliGenFunLog_zero, eval_map_algebraMap,
      show (ℓ : ℂ) = algebraMap ℚ ℂ ℓ by simp, aeval_algebraMap_apply_eq_algebraMap_eval]
    rfl
  rw [h0, ← hP, hQ, eval_map_algebraMap]

/-- Identity under the stated parameter and domain assumptions:
`bernoulliGenFunLog t = Complex.log (bernoulliGenFun t)`. -/
private lemma bernoulliGenFunLog_eq_log {t : ℂ} (ht : ‖t‖ < 2 * π)
    (hs : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → bernoulliGenFun (s * t) ∈ Complex.slitPlane) :
    bernoulliGenFunLog t = Complex.log (bernoulliGenFun t) := by
  set ψ : ℝ → ℂ := fun s => bernoulliGenFunLog (s * t) - Complex.log (bernoulliGenFun (s * t))
  have hball : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) * t ∈ ball (0 : ℂ) (2 * π) := by
    intro s hs
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖t‖ ≤ 1 * ‖t‖ := by gcongr; exact hs.2
      _ < _ := by simpa
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ψ 0 s := by
    intro s hs'
    have hz := hball s hs'
    have hH := (differentiableOn_bernoulliGenFun.differentiableAt
        (isOpen_ball.mem_nhds hz)).hasDerivAt
    have e : HasDerivAt (fun z : ℂ => bernoulliGenFunLog (z * t) -
        Complex.log (bernoulliGenFun (z * t))) 0
        (s : ℂ) := by
      have hm : HasDerivAt (fun z : ℂ => z * t) t (s : ℂ) := by
        simpa using (hasDerivAt_id (s : ℂ)).mul_const t
      have h1 := (hasDerivAt_bernoulliGenFunLog hz).comp (s : ℂ) hm
      have h2 := (hH.clog (hs s hs')).comp (s : ℂ) hm
      convert h1.sub h2 using 1 <;> first | rfl | simp only [bernoulliGenFunLogDeriv, sub_self]
    exact e.comp_ofReal
  have hc := constant_of_has_deriv_right_zero (f := ψ) (a := 0) (b := 1)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt) 1
    (Set.right_mem_Icc.mpr zero_le_one)
  simp only [ψ, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, bernoulliGenFunLog_zero,
    bernoulliGenFun_zero, Complex.log_one, sub_zero] at hc
  exact sub_eq_zero.mp hc

end NorlundSums
/-- DLMF 24.16.9 (complex order): `(t/(eᵗ - 1))^x = ∑ₙ B_n^{(x)} tⁿ/n!`, principal power, for
complex `x` and `0 < |t| < π` (DLMF: `|t| < 2π` with the branch equal to `1` at `t = 0`; see
the module docstring). -/
@[dlmf 24.16.E9]
theorem hasSum_norlundPolynomial (x : ℂ) {t : ℂ} (ht : ‖t‖ < π) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => aeval x (norlundPolynomial n) * t ^ n / n !)
      ((t / (Complex.exp t - 1)) ^ x) := by
  have hb : t ∈ Metric.ball (0 : ℂ) (2 * π) := by rw [mem_ball_zero_iff]; linarith [Real.pi_pos]
  have hT := Complex.hasSum_taylorSeries_on_ball (differentiableOn_exp_mul_bernoulliGenFunLog x) hb
  have hL := bernoulliGenFunLog_eq_log (t := t) (by linarith [Real.pi_pos]) fun s hs => by
    refine bernoulliGenFun_mem_slitPlane ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖t‖ ≤ 1 * ‖t‖ := by gcongr; exact hs.2
      _ < _ := by simpa
  simp only [sub_zero, iteratedDeriv_exp_mul_bernoulliGenFunLog_zero, smul_eq_mul] at hT
  rw [hL] at hT
  rw [← bernoulliGenFun_of_ne_zero ht0,
    Complex.cpow_def_of_ne_zero (bernoulliGenFun_ne_zero (by linarith [Real.pi_pos])),
    mul_comm (Complex.log _)]
  exact hT.congr_fun fun n => by ring

/-- DLMF 24.16.9 (real order and argument): `(t/(eᵗ - 1))^x = ∑ₙ B_n^{(x)} tⁿ/n!` for real `x`
and real `0 < |t| < 2π`. -/
@[dlmf 24.16.E9]
theorem hasSum_norlundPolynomial_real (x : ℝ) {t : ℝ} (ht : |t| < 2 * π) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => aeval x (norlundPolynomial n) * t ^ n / n !)
      ((t / (Real.exp t - 1)) ^ x) := by
  have hpos : ∀ r : ℝ, r ≠ 0 → 0 < r / (Real.exp r - 1) := by
    intro r hr
    rcases lt_or_gt_of_ne hr with h | h
    · have := Real.exp_lt_exp.mpr h
      rw [Real.exp_zero] at this
      exact div_pos_of_neg_of_neg h (by linarith)
    · have := Real.exp_lt_exp.mpr h
      rw [Real.exp_zero] at this
      exact div_pos h (by linarith)
  have hHr : ∀ r : ℝ, r ≠ 0 → bernoulliGenFun (r : ℂ) = ((r / (Real.exp r - 1) : ℝ) : ℂ) := by
    intro r hr
    rw [bernoulliGenFun_of_ne_zero (Complex.ofReal_ne_zero.mpr hr)]; push_cast; rfl
  have htn : ‖(t : ℂ)‖ < 2 * π := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hb : (t : ℂ) ∈ Metric.ball (0 : ℂ) (2 * π) := by rwa [mem_ball_zero_iff]
  have hT := Complex.hasSum_taylorSeries_on_ball
      (differentiableOn_exp_mul_bernoulliGenFunLog (x : ℂ)) hb
  have hL := bernoulliGenFunLog_eq_log htn fun s hs => by
    rw [← Complex.ofReal_mul]
    by_cases h0 : s * t = 0
    · rw [h0, Complex.ofReal_zero, bernoulliGenFun_zero]; exact Complex.one_mem_slitPlane
    · rw [hHr _ h0, Complex.ofReal_mem_slitPlane]; exact hpos _ h0
  have hR : Complex.exp ((x : ℂ) * bernoulliGenFunLog t) =
      (((t / (Real.exp t - 1)) ^ x : ℝ) : ℂ) := by
    rw [hL, hHr t ht0, ← Complex.ofReal_log (hpos t ht0).le, ← Complex.ofReal_mul,
      ← Complex.ofReal_exp, Real.rpow_def_of_pos (hpos t ht0), mul_comm]
  simp only [sub_zero, iteratedDeriv_exp_mul_bernoulliGenFunLog_zero, smul_eq_mul, hR] at hT
  rw [← Complex.hasSum_ofReal]
  refine hT.congr_fun fun n => ?_
  rw [show (x : ℂ) = algebraMap ℝ ℂ x from rfl, aeval_algebraMap_apply]
  simp only [Complex.coe_algebraMap]
  push_cast; ring

/-- DLMF §24.16(i): `B_n^{(x)}` is a polynomial in `x` of degree `n`. -/
@[dlmf 24.16.i]
theorem natDegree_norlundPolynomial (n : ℕ) : (norlundPolynomial n).natDegree = n := by
  set g := bernoulliPowerSeries ℚ - 1
  have hg : PowerSeries.constantCoeff g = 0 := by simp [g, bernoulliPowerSeries]
  have hg1 : PowerSeries.coeff 1 g = -1 / 2 := by simp [g, bernoulliPowerSeries]
  have hterm : ∀ j ∈ range (n + 1), (C (PowerSeries.coeff n (g ^ j) / j !) *
      descPochhammer ℚ j).natDegree ≤ n := fun j hj =>
    (natDegree_C_mul_le _ _).trans ((descPochhammer_natDegree ℚ j).le.trans
      (Nat.lt_succ_iff.mp (mem_range.mp hj)))
  have hcoeff : (norlundPolynomial n).coeff n = (-1 / 2) ^ n := by
    rw [norlundPolynomial, binomialSeriesCoeff, coeff_smul, finsetSum_coeff, sum_range_succ,
      Finset.sum_eq_zero, zero_add, coeff_C_mul, coeff_pow_self_of_constantCoeff_eq_zero g hg, hg1]
    · have hm := (monic_descPochhammer ℚ n).leadingCoeff
      rw [leadingCoeff, descPochhammer_natDegree ℚ n] at hm
      rw [hm, smul_eq_mul]
      have : (n ! : ℚ) ≠ 0 := by positivity
      field_simp
    · intro j hj
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [descPochhammer_natDegree ℚ]; exact mem_range.mp hj
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcoeff]; positivity)
  rw [norlundPolynomial, binomialSeriesCoeff]
  exact (natDegree_smul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ hterm)

/-- DLMF §24.16(i): the notation is consistent with 24.16.3, `B_n^{(x)}` at `x = ℓ` being
`B_n^{(ℓ)}`. -/
@[dlmf 24.16.i]
theorem norlundPolynomial_eval_natCast (ℓ n : ℕ) :
    (norlundPolynomial n).eval (ℓ : ℚ) = bernoulliNumberOrder ℓ n := rfl

/-! ### §24.16(ii) Character analogs -/

/-- DLMF 24.16.10: the generalized Bernoulli numbers belonging to a Dirichlet character `χ`
modulo `f`, by the closed form `B_{n,χ} = f^{n-1} ∑_{a=1}^{f} χ(a) Bₙ(a/f)` (DLMF: `χ`
primitive with conductor `f`; the generating function is `hasSum_bernoulliChar`). -/
@[dlmf 24.16.E10]
def bernoulliChar {f : ℕ} (χ : DirichletCharacter ℂ f) (n : ℕ) : ℂ :=
  (f : ℂ) ^ ((n : ℤ) - 1) *
    ∑ a ∈ Icc 1 f, χ a * bernoulliPolyB n ((a : ℂ) / f)

/-- DLMF 24.16.11: `B_{n,χ}(x) = ∑ₖ (n choose k) B_{k,χ} x^{n-k}`. -/
@[dlmf 24.16.E11]
def bernoulliCharPoly {f : ℕ} (χ : DirichletCharacter ℂ f) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ range (n + 1), (n.choose k : ℂ) * bernoulliChar χ k * x ^ (n - k)

/-- DLMF 24.16.10: `∑_{a=1}^{f} χ(a) t e^{at}/(e^{ft} - 1) = ∑ₙ B_{n,χ} tⁿ/n!` for
`0 < |t| < 2π/f` (stated for every `χ` modulo `f ≥ 1`, which includes DLMF's primitive `χ`). -/
@[dlmf 24.16.E10]
theorem hasSum_bernoulliChar {f : ℕ} (hf : 1 ≤ f) (χ : DirichletCharacter ℂ f) {t : ℂ}
    (ht : ‖t‖ < 2 * π / f) (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ => bernoulliChar χ n * t ^ n / n !)
      (∑ a ∈ Icc 1 f, χ a * t * Complex.exp (a * t) / (Complex.exp (f * t) - 1)) := by
  have hf0 : (f : ℂ) ≠ 0 := by exact_mod_cast (show f ≠ 0 by omega)
  have hfr : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have hft : ‖(f : ℂ) * t‖ < 2 * π := by
    rw [norm_mul, Complex.norm_natCast, ← lt_div_iff₀' hfr]; exact ht
  have hft0 : (f : ℂ) * t ≠ 0 := mul_ne_zero hf0 ht0
  have key : ∀ a ∈ Icc 1 f, HasSum (fun n : ℕ => χ a * ((f : ℂ) ^ ((n : ℤ) - 1) *
      bernoulliPolyB n ((a : ℂ) / f)) * t ^ n / n !)
      (χ a * t * Complex.exp (a * t) / (Complex.exp (f * t) - 1)) := by
    intro a _
    have h := (hasSum_bernoulliPolyB_mul_pow_div ((a : ℂ) / f) hft hft0).mul_left (χ a / f)
    convert h using 1
    · funext n
      rw [zpow_sub₀ hf0, zpow_one, zpow_natCast, mul_pow]
      field_simp
    · rw [show (a : ℂ) / f * (f * t) = a * t by field_simp]
      field_simp
  convert hasSum_sum key using 1
  funext n
  rw [bernoulliChar, mul_sum, sum_mul, sum_div]
  refine sum_congr rfl fun a _ => ?_
  ring

/-- The character `χ₄` modulo `4` (`χ₄(1) = 1`, `χ₄(3) = -1`, `χ₄(2) = χ₄(4) = 0`) as a
complex Dirichlet character (Mathlib's `ZMod.χ₄` composed with `ℤ → ℂ`). -/
def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- DLMF 24.16.12: `Bₙ(x) = B_{n,χ₀}(x - 1)`, `χ₀` the trivial character (`f = 1`). -/
@[dlmf 24.16.E12]
theorem bernoulli_eq_bernoulliCharPoly_one (n : ℕ) (x : ℂ) :
    bernoulliPolyB n x = bernoulliCharPoly (1 : DirichletCharacter ℂ 1) n (x - 1) := by
  have h := bernoulliPolyB_add n 1 (x - 1)
  rw [add_sub_cancel] at h
  rw [h, bernoulliCharPoly]
  refine sum_congr rfl fun k _ => ?_
  congr 2
  simp [bernoulliChar, MulChar.one_apply (isUnit_of_subsingleton _)]

/-- DLMF 24.16.13: `Eₙ(x) = -(2^{1-n}/(n+1)) B_{n+1,χ₄}(2x - 1)`. -/
@[dlmf 24.16.E13]
theorem euler_eq_bernoulliCharPoly_chi4 (n : ℕ) (x : ℂ) :
    eulerPolyE n x =
      -((2 : ℂ) ^ (1 - (n : ℤ)) / (n + 1)) * bernoulliCharPoly chi4 (n + 1) (2 * x - 1) := by
  have hchi : ∀ k, bernoulliChar chi4 k =
      (4 : ℂ) ^ ((k : ℤ) - 1) * (bernoulliPolyB k (1 / 4) - bernoulliPolyB k (3 / 4)) := by
    intro k
    rw [bernoulliChar]
    simp [Finset.sum_Icc_succ_top, chi4, MulChar.ringHomComp_apply]
    ring_nf
    simp
  have hpoly : bernoulliCharPoly chi4 (n + 1) (2 * x - 1) =
      4 ^ n * (bernoulliPolyB (n + 1) (x / 2) - bernoulliPolyB (n + 1) (x / 2 + 1 / 2)) := by
    have h1 := bernoulliPolyB_add (n + 1) (1 / 4) ((2 * x - 1) / 4)
    have h3 := bernoulliPolyB_add (n + 1) (3 / 4) ((2 * x - 1) / 4)
    rw [show (1 / 4 : ℂ) + (2 * x - 1) / 4 = x / 2 by ring] at h1
    rw [show (3 / 4 : ℂ) + (2 * x - 1) / 4 = x / 2 + 1 / 2 by ring] at h3
    rw [h1, h3, bernoulliCharPoly, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [hchi, div_pow]
    have h4 : (4 : ℂ) ^ n = (4 : ℂ) ^ ((k : ℤ) - 1) * 4 ^ (n + 1 - k) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1; push_cast [hk']; ring
    rw [h4]
    have : (4 : ℂ) ^ (n + 1 - k) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have he := congrArg (aeval x) (euler_eq_bernoulli n)
  simp only [map_mul, map_add, map_natCast, map_one, aeval_C, aeval_comp, aeval_X, map_sub,
    eq_ratCast] at he
  rw [hpoly]
  change ((n : ℂ) + 1) * eulerPolyE n x = _ at he
  have ha : ((1 / 2 : ℚ) : ℂ) * x + ((1 / 2 : ℚ) : ℂ) = x / 2 + 1 / 2 := by push_cast; ring
  have hb : ((1 / 2 : ℚ) : ℂ) * x = x / 2 := by push_cast; ring
  rw [ha, hb] at he
  change _ = ((2 ^ (n + 1) : ℚ) : ℂ) * (bernoulliPolyB (n + 1) (x / 2 + 1 / 2) -
    bernoulliPolyB (n + 1) (x / 2)) at he
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have h2 : (2 : ℂ) ^ (1 - (n : ℤ)) * 4 ^ n = 2 ^ (n + 1) := by
    rw [show (4 : ℂ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num, ← zpow_natCast (2 : ℂ) (2 * n),
      ← zpow_add₀ (by norm_num), ← zpow_natCast]
    congr 1; push_cast; ring
  have hE : eulerPolyE n x = (2 : ℂ) ^ (n + 1) * (bernoulliPolyB (n + 1) (x / 2 + 1 / 2) -
      bernoulliPolyB (n + 1) (x / 2)) / (n + 1) := by
    rw [eq_div_iff hn]; push_cast at he; linear_combination he
  rw [hE, ← h2]
  field_simp
  ring

end DLMF.BernoulliEuler

end
