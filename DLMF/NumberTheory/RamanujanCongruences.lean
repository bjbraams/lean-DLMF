/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Products.LogDerivativesAndDoubleProducts
public import DLMF.Theta.Basic.Series
public import DLMFMathlib.Analysis.Analytic.OfScalarsUnique
public import DLMFMathlib.RingTheory.PowerSeriesEvaluation
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Jacobi's identity and Ramanujan's congruences modulo 5 and 7 (DLMF §27.14(v))

Jacobi's identity `∏_{m≥1} (1 - xᵐ)³ = ∑_{n≥0} (-1)ⁿ (2n+1) x^{n(n+1)/2}` is obtained from the
product formula for `θ₁'(0|τ)` (DLMF 20.4.2) and the termwise derivative of the sine series of
`θ₁` (DLMF 20.2.1), and is turned into an identity of formal power series in `ℤ⟦X⟧` by the
uniqueness of power series coefficients. Together with Euler's pentagonal number theorem
(Mathlib) and the Frobenius identity `f^ℓ = f(X^ℓ)` in `(ZMod ℓ)⟦X⟧`, it gives Ramanujan's
congruences `p(5m + 4) ≡ 0 (mod 5)` and `p(7m + 5) ≡ 0 (mod 7)`, the classical proofs through
`∏ (1 - xᵐ)⁴ = ∏ (1 - xᵐ) · ∏ (1 - xᵐ)³` and `∏ (1 - xᵐ)⁶ = (∏ (1 - xᵐ)³)²`.

## Main results

* `DLMF.Theta.hasSum_jacobiThetaOneDerivNullTau`: `θ₁'(0|τ) = 2∑ (-1)ⁿ (2n+1) q^{(n+1/2)²}`.
* `DLMF.Theta.hasSum_eulerFunction_pow_three`: Jacobi's identity in the unit disc.
* `DLMF.NumberTheory.RamanujanCongruences.hasSumAt_pentagonalSeries`: the series
  `∏ (1 - Xᵐ) ∈ ℤ⟦X⟧` converges to Euler's function in the unit disc.
* `DLMF.NumberTheory.RamanujanCongruences.pentagonalSeries_pow_three`: Jacobi's identity in
  `ℤ⟦X⟧`.
* `DLMF.NumberTheory.RamanujanCongruences.prime_dvd_card_partition_of_dvd_coeff`: the reduction
  of a congruence `ℓ ∣ p(ℓm + r)` to the coefficients of `∏ (1 - Xᵐ)^{ℓ-1}`.
* `DLMF.NumberTheory.RamanujanCongruences.five_dvd_card_partition`,
  `DLMF.NumberTheory.RamanujanCongruences.seven_dvd_card_partition`: Ramanujan's congruences
  modulo 5 and 7, used for `DLMF.Partitions.ramanujan_mod_five` and
  `DLMF.Partitions.ramanujan_mod_seven`.
-/

@[expose] public section

open Complex Filter Topology DLMF.Elliptic
open scoped Real

namespace DLMF.Theta

private lemma norm_sin_le_exp_norm (w : ℂ) : ‖sin w‖ ≤ Real.exp ‖w‖ := by
  have h1 : ‖cexp (w * I)‖ ≤ Real.exp ‖w‖ := by
    rw [norm_exp]; gcongr
    calc (w * I).re = -w.im := by simp
      _ ≤ |w.im| := neg_le_abs _
      _ ≤ ‖w‖ := abs_im_le_norm w
  have h2 : ‖cexp (-w * I)‖ ≤ Real.exp ‖w‖ := by
    rw [norm_exp]; gcongr
    calc (-w * I).re = w.im := by simp
      _ ≤ |w.im| := le_abs_self _
      _ ≤ ‖w‖ := abs_im_le_norm w
  rw [sin, norm_div, norm_mul, Complex.norm_two, norm_I, mul_one]
  have := norm_sub_le (cexp (-w * I)) (cexp (w * I))
  linarith

/-- The derivative series `θ₁'(0|τ) = 2∑ (-1)ⁿ (2n+1) q^{(n+1/2)²}`. -/
theorem hasSum_jacobiThetaOneDerivNullTau {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
      (2 * n + 1)) (jacobiThetaOneDerivNullTau τ) := by
  set F : ℕ → ℂ → ℂ := fun n w => 2 * (-1 : ℂ) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
      sin ((2 * n + 1) * w) with hF
  have hθ : (fun z => jacobiThetaOneTau z τ) = fun w => ∑' n, F n w := by
    funext w; exact (jacobiThetaOneTau_hasSum_sin w hτ).tsum_eq.symm
  set u : ℕ → ℝ := fun n => 2 * Real.exp 1 *
    Real.exp (-π * (τ.im * (n : ℝ) ^ 2 - 2 * (1 / π) * n)) with hu
  have hus : Summable u := by
    have h := summable_pow_mul_jacobiTheta₂_term_bound (1 / π) hτ 0
    have h' := h.comp_injective Nat.cast_injective
    simp only [pow_zero, one_mul, Function.comp_def, Int.cast_natCast, Nat.abs_cast] at h'
    exact h'.mul_left _
  have hle : ∀ n w, w ∈ Metric.ball (0 : ℂ) 1 → ‖F n w‖ ≤ u n := by
    intro n w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hc : ‖cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2)‖ ≤ Real.exp (-π * τ.im * n ^ 2) := by
      rw [norm_exp]
      gcongr
      have : (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2).re = -π * τ.im * ((n : ℝ) + 1 / 2) ^ 2 := by
        have e : ((n : ℂ) + 1 / 2) ^ 2 = (((n : ℝ) + 1 / 2) ^ 2 : ℝ) := by push_cast; ring
        rw [e, show (π : ℂ) * I * τ * (((n : ℝ) + 1 / 2) ^ 2 : ℝ) =
          ((π * ((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) * (I * τ) by push_cast; ring, re_ofReal_mul]
        simp; ring
      rw [this]
      have : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1 / 2) ^ 2 := by nlinarith [n.cast_nonneg (α := ℝ)]
      have := Real.pi_pos
      nlinarith [mul_pos this hτ]
    have hs : ‖sin ((2 * n + 1) * w)‖ ≤ Real.exp (2 * n + 1) := by
      refine (norm_sin_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul]
      have : ‖(2 * (n : ℂ) + 1)‖ = 2 * n + 1 := by
        rw [show (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [this]
      have : (0 : ℝ) ≤ 2 * n + 1 := by positivity
      nlinarith
    calc ‖F n w‖ = 2 * ‖cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2)‖ * ‖sin ((2 * n + 1) * w)‖ := by
          simp [hF]
      _ ≤ 2 * Real.exp (-π * τ.im * n ^ 2) * Real.exp (2 * n + 1) := by gcongr
      _ = u n := by
          rw [mul_assoc, ← Real.exp_add, hu]
          simp only
          rw [mul_assoc 2 (Real.exp 1), ← Real.exp_add]
          congr 2
          field_simp
          ring
  have hd := hasSum_deriv_of_summable_norm hus (U := Metric.ball 0 1)
    (fun n => by fun_prop) Metric.isOpen_ball hle (Metric.mem_ball_self one_pos)
  rw [← hθ] at hd
  convert hd using 1
  swap; · rfl
  funext n
  have : HasDerivAt (F n) (2 * (-1 : ℂ) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
      (cos ((2 * n + 1) * 0) * (2 * n + 1))) 0 := by
    refine HasDerivAt.const_mul _ ?_
    have := ((hasDerivAt_id (0 : ℂ)).const_mul (2 * (n : ℂ) + 1)).csin
    simpa using this
  rw [this.deriv]
  simp


/-- Jacobi's identity `∏ (1 - xᵐ)³ = ∑ (-1)ⁿ (2n+1) x^{n(n+1)/2}` for `0 < |x| < 1`. -/
private theorem hasSum_eulerFunction_pow_three_of_ne_zero {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * (2 * n + 1) * x ^ (n * (n + 1) / 2))
      (eulerFunction x ^ 3) := by
  set τ : ℂ := Complex.log x / (2 * π * I) with hτdef
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hτI : 2 * π * I * τ = Complex.log x := by
    rw [hτdef]; field_simp
  have hτ : 0 < τ.im := by
    have : τ = -(I * Complex.log x) / (2 * π) := by
      rw [hτdef]; field_simp; rw [show I ^ 2 = -1 from I_sq]; ring
    rw [this, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, div_ofReal_im]
    simp only [neg_im, mul_im, I_re, zero_mul, I_im, one_mul, zero_add, log_re]
    have hl : Real.log ‖x‖ < 0 := Real.log_neg (norm_pos_iff.mpr hx0) hx
    have := Real.pi_pos
    exact div_pos (by linarith) (by positivity)
  set E := cexp (π * I * τ) with hE
  have hE2 : E ^ 2 = x := by
    rw [hE, ← exp_nat_mul, show ((2 : ℕ) : ℂ) * (π * I * τ) = 2 * π * I * τ by push_cast; ring,
      hτI, exp_log hx0]
  obtain ⟨-, hprod, -⟩ := jacobiThetaOneDerivNullTau_prod hτ
  have hser := hasSum_jacobiThetaOneDerivNullTau hτ
  have hP : ∏' k : ℕ, (1 - E ^ (2 * (k + 1))) ^ 3 = eulerFunction x ^ 3 := by
    have h := (hasProd_eulerFunction hx).pow 3
    rw [← h.tprod_eq]
    congr 1; funext k; rw [pow_mul, hE2]
  rw [hprod, hP] at hser
  set C : ℂ := 2 * cexp (π * I * τ / 4) with hC
  have hC0 : C ≠ 0 := mul_ne_zero two_ne_zero (exp_ne_zero _)
  have hterm : ∀ n : ℕ, 2 * (-1 : ℂ) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
      (2 * n + 1) = C * ((-1 : ℂ) ^ n * (2 * n + 1) * x ^ (n * (n + 1) / 2)) := by
    intro n
    have hm : n * (n + 1) / 2 * 2 = n * (n + 1) :=
      Nat.div_mul_cancel (Nat.even_mul_succ_self n).two_dvd
    have : x ^ (n * (n + 1) / 2) = cexp (π * I * τ * ((n : ℂ) * (n + 1))) := by
      rw [← hE2, ← pow_mul, mul_comm 2, hm, hE, ← exp_nat_mul]; push_cast; ring_nf
    rw [this, hC]
    have e : cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) =
        cexp (π * I * τ / 4) * cexp (π * I * τ * ((n : ℂ) * (n + 1))) := by
      rw [← exp_add]; congr 1; ring
    rw [e]; ring
  simp_rw [hterm] at hser
  rw [show C * eulerFunction x ^ 3 = C * (eulerFunction x ^ 3) from rfl] at hser
  exact (hasSum_mul_left_iff hC0).mp hser

/-- Jacobi's identity `∏_{m≥1} (1 - xᵐ)³ = ∑_{n≥0} (-1)ⁿ (2n+1) x^{n(n+1)/2}` for `|x| < 1`. -/
theorem hasSum_eulerFunction_pow_three {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * (2 * n + 1) * x ^ (n * (n + 1) / 2))
      (eulerFunction x ^ 3) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have h1 : eulerFunction (0 : ℂ) = 1 := by
      rw [← (hasProd_eulerFunction hx).tprod_eq]; simp
    rw [h1, one_pow]
    convert hasSum_ite_eq 0 (1 : ℂ) using 1
    funext n
    rcases n with _ | n
    · simp
    · have : (n + 1) * (n + 1 + 1) / 2 ≠ 0 := by
        rw [Nat.div_ne_zero_iff_of_dvd (Nat.even_mul_succ_self _).two_dvd]; simp
      simp [this]
  · exact hasSum_eulerFunction_pow_three_of_ne_zero hx0 hx

end DLMF.Theta

namespace DLMF.NumberTheory.RamanujanCongruences

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- Triangular numbers `n(n+1)/2`. -/
private def tri (n : ℕ) : ℕ := n * (n + 1) / 2

private lemma two_mul_tri (n : ℕ) : 2 * tri n = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

private lemma tri_strictMono : StrictMono tri := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have h1 := two_mul_tri n
  have h2 := two_mul_tri (n + 1)
  nlinarith

/-- The Jacobi series `∑ (-1)ⁿ (2n+1) X^{n(n+1)/2}` in `ℤ⟦X⟧`. -/
noncomputable def jacobiCubeSeries : PowerSeries ℤ :=
  PowerSeries.mk (Function.extend (fun n : ℕ ↦ n * (n + 1) / 2)
    (fun n : ℕ ↦ (-1 : ℤ) ^ n * (2 * n + 1)) 0)

private lemma coeff_jacobiCubeSeries_tri (n : ℕ) :
    coeff (tri n) jacobiCubeSeries = (-1) ^ n * (2 * n + 1) := by
  rw [jacobiCubeSeries, coeff_mk]
  exact tri_strictMono.injective.extend_apply _ _ _

private lemma coeff_jacobiCubeSeries_eq_zero {m : ℕ} (h : m ∉ Set.range tri) :
    coeff m jacobiCubeSeries = 0 := by
  rw [jacobiCubeSeries, coeff_mk]
  exact Function.extend_apply' (f := tri) _ _ _ (by simpa using h)

/-- The pentagonal series `∏ (1 - Xᵐ) ∈ ℤ⟦X⟧` converges to Euler's function in the unit disc. -/
theorem hasSumAt_pentagonalSeries {x : ℂ} (hx : ‖x‖ < 1) :
    PowerSeries.HasSumAt (pentagonalSeries ℤ) x (eulerFunction x) := by
  have hc : ∀ n, ((coeff n (pentagonalSeries ℤ) : ℤ) : ℂ) = coeff n (pentagonalSeries ℂ) := by
    intro n
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨k, rfl⟩ := hn
      simp only [coeff_pentagonalSeries_pentagonal]
      rcases Int.even_or_odd k with h | h <;> simp [Int.negOnePow_even, Int.negOnePow_odd, h]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  have hb := PowerSeries.hasSumAt_of_bounded (P := pentagonalSeries ℤ) (C := 1) (fun n ↦ by
    rw [algebraMap_int_eq, eq_intCast, Complex.norm_intCast]
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨k, rfl⟩ := hn
      simp only [coeff_pentagonalSeries_pentagonal]
      rcases Int.even_or_odd k with h | h <;> simp [Int.negOnePow_even, Int.negOnePow_odd, h]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]) hx
  simp only [PowerSeries.hasSumAt_int_iff, algebraMap_int_eq, eq_intCast, hc] at hb ⊢
  rwa [← eulerFunction_def] at hb

/-- Jacobi's identity as a formal power series identity:
`∏ (1 - Xᵐ)³ = ∑ (-1)ⁿ (2n+1) X^{n(n+1)/2}` in `ℤ⟦X⟧`. -/
theorem pentagonalSeries_pow_three : pentagonalSeries ℤ ^ 3 = jacobiCubeSeries := by
  have key := Complex.eq_of_hasSum_mul_pow_ball (ρ := 1) one_pos
    (c := fun n ↦ ((coeff n (pentagonalSeries ℤ ^ 3) : ℤ) : ℂ))
    (d := fun n ↦ ((coeff n jacobiCubeSeries : ℤ) : ℂ)) (g := fun x ↦ eulerFunction x ^ 3)
    (fun x hx ↦ by
      simpa [PowerSeries.hasSumAt_int_iff] using (hasSumAt_pentagonalSeries hx).pow 3)
    (fun x hx ↦ by
      have h := DLMF.Theta.hasSum_eulerFunction_pow_three hx
      rw [← tri_strictMono.injective.hasSum_iff]
      · convert h using 1
        funext n
        simp only [Function.comp_apply, coeff_jacobiCubeSeries_tri]
        push_cast; rfl
      · intro m hm
        simp [coeff_jacobiCubeSeries_eq_zero hm])
  ext n
  exact_mod_cast congr_fun key n


/-- The partition generating function in `ℤ⟦X⟧`. -/
private noncomputable def partitionSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ (Fintype.card (Nat.Partition n) : ℤ)

private lemma partitionSeries_mul_pentagonalSeries :
    partitionSeries * pentagonalSeries ℤ = 1 := by
  have h1 := Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℤ (fun _ ↦ True)
  have h2 : partitionSeries = PowerSeries.mk fun n ↦
      ((Nat.Partition.restricted n (fun _ ↦ True)).card : ℤ) := by
    ext n; simp [partitionSeries, Nat.Partition.restricted]
  rw [h2, h1, ← PowerSeries.WithPiTopology.tprod_one_sub_X_pow ℤ]
  simp only [ite_true]
  rw [← Multipliable.tprod_mul ?_ (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ)]
  · convert tprod_one with i
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  · simpa using Nat.Partition.multipliable_powerSeriesMk_card_restricted ℤ (fun _ ↦ True)

/-- If the coefficients of `∏ (1 - Xᵐ)^{ℓ-1}` in the residue class `r` modulo a prime `ℓ` are
divisible by `ℓ`, then so are the partition numbers `p(ℓm + r)`. -/
theorem prime_dvd_card_partition_of_dvd_coeff {ℓ r : ℕ} [hℓ : Fact ℓ.Prime] (hr : r < ℓ)
    (h : ∀ i, i % ℓ = r → (ℓ : ℤ) ∣ coeff i (pentagonalSeries ℤ ^ (ℓ - 1))) (m : ℕ) :
    ℓ ∣ Fintype.card (Nat.Partition (ℓ * m + r)) := by
  have hℓ0 : ℓ ≠ 0 := hℓ.out.ne_zero
  set φ := PowerSeries.map (Int.castRingHom (ZMod ℓ))
  set e := φ (pentagonalSeries ℤ)
  set pp := φ partitionSeries
  have hpe : pp * e = 1 := by
    rw [← map_mul, partitionSeries_mul_pentagonalSeries, map_one]
  have hfrob : expand ℓ hℓ0 e = e ^ ℓ := by
    convert FiniteField.PowerSeries.expand_card e using 2 <;> simp [ZMod.card]
  set Q := expand ℓ hℓ0 pp
  have hQ : expand ℓ hℓ0 e * Q = 1 := by
    rw [mul_comm, ← map_mul, hpe, map_one]
  have hpp : pp = e ^ (ℓ - 1) * Q := by
    calc pp = pp * (expand ℓ hℓ0 e * Q) := by rw [hQ, mul_one]
      _ = (pp * e) * e ^ (ℓ - 1) * Q := by
          rw [hfrob, mul_assoc pp e, ← pow_succ', Nat.sub_add_cancel hℓ.out.one_lt.le]
          ring
      _ = e ^ (ℓ - 1) * Q := by rw [hpe, one_mul]
  have hc : coeff (ℓ * m + r) pp = 0 := by
    rw [hpp, coeff_mul]
    refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
    rw [Finset.mem_antidiagonal] at hij
    by_cases hj : ℓ ∣ j
    · have hi : i % ℓ = r := by
        obtain ⟨t, rfl⟩ := hj
        have : i = ℓ * (m - t) + r := by
          have : ℓ * t ≤ ℓ * m := by
            by_contra hcon
            push Not at hcon
            have : m < t := lt_of_mul_lt_mul_left hcon (Nat.zero_le _)
            nlinarith
          rw [Nat.mul_sub]; omega
        rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      have : coeff i (e ^ (ℓ - 1)) = 0 := by
        rw [← map_pow, coeff_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact h i hi
      simp [this]
    · simp [Q, coeff_expand_of_not_dvd ℓ hℓ0 _ hj]
  have : coeff (ℓ * m + r) pp = ((Fintype.card (Nat.Partition (ℓ * m + r)) : ℤ) : ZMod ℓ) := by
    simp [pp, φ, partitionSeries]
  rw [this] at hc
  exact (ZMod.natCast_eq_zero_iff _ _).mp (by exact_mod_cast hc)


private lemma natCast_mod_eq {p i r : ℕ} (h : i % p = r) : (i : ZMod p) = r := by
  rw [← h, ZMod.natCast_mod]

/-- The coefficients of `∏ (1 - Xᵐ)⁴` in degrees `≡ 4 (mod 5)` are divisible by `5`. -/
private lemma five_dvd_coeff_pentagonalSeries_pow_four {i : ℕ} (hi : i % 5 = 4) :
    (5 : ℤ) ∣ coeff i (pentagonalSeries ℤ ^ 4) := by
  rw [pow_succ', pentagonalSeries_pow_three, coeff_mul]
  refine Finset.dvd_sum fun ⟨a, b⟩ hab ↦ ?_
  rw [Finset.mem_antidiagonal] at hab
  by_cases ha : a ∈ Set.range pentagonal
  swap; · simp [coeff_pentagonalSeries_eq_zero _ ha]
  by_cases hb : b ∈ Set.range tri
  swap; · simp [coeff_jacobiCubeSeries_eq_zero hb]
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  rw [coeff_jacobiCubeSeries_tri]
  refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2p : 2 * ((pentagonal k : ℤ) : ZMod 5) = (k : ZMod 5) * (3 * k - 1) := by
    exact_mod_cast congrArg (fun z : ℤ ↦ (z : ZMod 5)) (two_mul_natCast_pentagonal k)
  have h2t : 2 * ((tri n : ℕ) : ZMod 5) = (n : ZMod 5) * (n + 1) := by
    exact_mod_cast congrArg (fun z : ℕ ↦ (z : ZMod 5)) (two_mul_tri n)
  have hs : ((pentagonal k : ℕ) : ZMod 5) + ((tri n : ℕ) : ZMod 5) = 4 := by
    have := natCast_mod_eq (p := 5) (hab ▸ hi)
    exact_mod_cast this
  have key : ∀ K N : ZMod 5, K * (3 * K - 1) + N * (N + 1) = 8 → 2 * N + 1 = 0 := by decide
  push_cast
  refine key (k : ZMod 5) (n : ZMod 5) ?_
  push_cast at h2p
  linear_combination 2 * hs - h2p - h2t

/-- The coefficients of `∏ (1 - Xᵐ)⁶` in degrees `≡ 5 (mod 7)` are divisible by `7`. -/
private lemma seven_dvd_coeff_pentagonalSeries_pow_six {i : ℕ} (hi : i % 7 = 5) :
    (7 : ℤ) ∣ coeff i (pentagonalSeries ℤ ^ 6) := by
  rw [show 6 = 3 * 2 from rfl, pow_mul, pentagonalSeries_pow_three, sq, coeff_mul]
  refine Finset.dvd_sum fun ⟨a, b⟩ hab ↦ ?_
  rw [Finset.mem_antidiagonal] at hab
  by_cases ha : a ∈ Set.range tri
  swap; · simp [coeff_jacobiCubeSeries_eq_zero ha]
  by_cases hb : b ∈ Set.range tri
  swap; · simp [coeff_jacobiCubeSeries_eq_zero hb]
  obtain ⟨n, rfl⟩ := ha
  obtain ⟨n', rfl⟩ := hb
  rw [coeff_jacobiCubeSeries_tri, coeff_jacobiCubeSeries_tri]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
  rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) from rfl, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2t : 2 * ((tri n : ℕ) : ZMod 7) = (n : ZMod 7) * (n + 1) := by
    exact_mod_cast congrArg (fun z : ℕ ↦ (z : ZMod 7)) (two_mul_tri n)
  have h2t' : 2 * ((tri n' : ℕ) : ZMod 7) = (n' : ZMod 7) * (n' + 1) := by
    exact_mod_cast congrArg (fun z : ℕ ↦ (z : ZMod 7)) (two_mul_tri n')
  have hs : ((tri n : ℕ) : ZMod 7) + ((tri n' : ℕ) : ZMod 7) = 5 := by
    have := natCast_mod_eq (p := 7) (hab ▸ hi)
    exact_mod_cast this
  have key : ∀ N N' : ZMod 7, N * (N + 1) + N' * (N' + 1) = 10 → 2 * N + 1 = 0 := by decide
  push_cast
  refine key (n : ZMod 7) (n' : ZMod 7) ?_
  linear_combination 2 * hs - h2t - h2t'

/-- Ramanujan's congruence `p(5m + 4) ≡ 0 (mod 5)`. -/
theorem five_dvd_card_partition (m : ℕ) : 5 ∣ Fintype.card (Nat.Partition (5 * m + 4)) :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  prime_dvd_card_partition_of_dvd_coeff (by norm_num)
    (fun _ hi ↦ by exact_mod_cast five_dvd_coeff_pentagonalSeries_pow_four hi) m

/-- Ramanujan's congruence `p(7m + 5) ≡ 0 (mod 7)`. -/
theorem seven_dvd_card_partition (m : ℕ) : 7 ∣ Fintype.card (Nat.Partition (7 * m + 5)) :=
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  prime_dvd_card_partition_of_dvd_coeff (by norm_num)
    (fun _ hi ↦ by exact_mod_cast seven_dvd_coeff_pentagonalSeries_pow_six hi) m

end DLMF.NumberTheory.RamanujanCongruences
