/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Asymptotics.LargeOrder

/-!
# Binomial remainders in Anger asymptotics

Binomial remainder estimates and paired Anger-function kernels give the fixed-argument
expansions.

Source references and common attribution are retained in
`DLMF.Struve.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Airy

section BinomialRemainder

open scoped Interval

/-- The binomial remainder `(1+u)^a - ∑_{k<m} (a choose k) u^k`. -/
def struveBinomRem (a : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ a - ∑ k ∈ Finset.range m, Ring.choose a k * u ^ k

/-- `(k+1) (a choose k+1) = a (a-1 choose k)`. -/
theorem succ_mul_ring_choose_succ (a : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Ring.choose a (k + 1) = a * Ring.choose (a - 1) k := by
  have h1 := DLMF.Confluent.ring_choose_neg_eq_poch (-(a : ℂ)) (k + 1)
  have h2 := DLMF.Confluent.ring_choose_neg_eq_poch (-(a : ℂ) + 1) k
  rw [neg_neg] at h1
  rw [show -(-(a : ℂ) + 1) = (a : ℂ) - 1 by ring] at h2
  apply Complex.ofReal_injective
  push_cast
  rw [h1, h2, poch_succ_left, Nat.factorial_succ]
  push_cast
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp
  ring

/-- `d/du` of the binomial remainder lowers `a` and `m` by one. -/
theorem hasDerivAt_struveBinomRem (a : ℝ) (m : ℕ) {u : ℝ} (hu : -1 < u) :
    HasDerivAt (struveBinomRem a (m + 1)) (a * struveBinomRem (a - 1) m u) u := by
  have h1 : HasDerivAt (fun u : ℝ => (1 + u) ^ a) (1 * a * (1 + u) ^ (a - 1)) u :=
    ((hasDerivAt_id u).const_add 1).rpow_const (Or.inl (by simp; linarith))
  have h2 : HasDerivAt (fun u : ℝ => ∑ k ∈ Finset.range (m + 1), Ring.choose a k * u ^ k)
      (∑ k ∈ Finset.range (m + 1), Ring.choose a k * (k * u ^ (k - 1))) u :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_pow k u).const_mul _
  convert h1.sub h2 using 1
  · funext v; rfl
  unfold struveBinomRem
  rw [Finset.sum_range_succ', mul_sub, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel, Nat.cast_succ]
  rw [one_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← succ_mul_ring_choose_succ]
  ring

/-- The binomial remainder is continuous on `[0, ∞)`. -/
theorem continuousOn_struveBinomRem (a : ℝ) (m : ℕ) : ContinuousOn (struveBinomRem a m) (Ici 0) := by
  refine ((continuousOn_const.add continuousOn_id).rpow_const fun x hx => Or.inl ?_).sub
    (by fun_prop)
  have : (0 : ℝ) ≤ x := hx
  simp; linarith

/-- The remainder after at least one term vanishes at `0`. -/
theorem struveBinomRem_succ_zero (a : ℝ) (m : ℕ) : struveBinomRem a (m + 1) 0 = 0 := by
  simp [struveBinomRem, Finset.sum_range_succ']

/-- Integral form of the binomial remainder. -/
theorem struveBinomRem_succ_eq_integral (a : ℝ) (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    struveBinomRem a (m + 1) u = a * ∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s := by
  rw [← intervalIntegral.integral_const_mul]
  have hint : IntervalIntegrable (fun s => a * struveBinomRem (a - 1) m s) volume 0 u :=
    ((continuousOn_struveBinomRem (a - 1) m).mono (by
      rw [uIcc_of_le hu]; exact Icc_subset_Ici_self)).intervalIntegrable.const_mul a
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := struveBinomRem a (m + 1)) (fun s hs => ?_)
    hint, struveBinomRem_succ_zero, sub_zero]
  rw [uIcc_of_le hu] at hs
  exact hasDerivAt_struveBinomRem a m (by linarith [hs.1])

/-- Sign and size of the binomial remainder for `a ≤ m` and `u ≥ 0`. -/
theorem struveBinomRem_bound (m : ℕ) : ∀ a : ℝ, a ≤ m → ∀ u : ℝ, 0 ≤ u →
    0 ≤ Ring.choose a m * struveBinomRem a m u ∧ |struveBinomRem a m u| ≤ |Ring.choose a m| * u ^ m := by
  induction m with
  | zero =>
    intro a ha u hu
    simp only [struveBinomRem, Finset.range_zero, Finset.sum_empty, sub_zero, Ring.choose_zero_right,
      one_mul, pow_zero, abs_one, mul_one]
    have h0 : 0 ≤ (1 + u) ^ a := Real.rpow_nonneg (by linarith) _
    refine ⟨h0, ?_⟩
    rw [abs_of_nonneg h0]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simpa using ha)
  | succ m ih =>
    intro a ha u hu
    have ih' := ih (a - 1) (by push_cast at ha; linarith)
    have hc := succ_mul_ring_choose_succ a m
    have hm1 : (0 : ℝ) < m + 1 := by positivity
    have hc' : Ring.choose a (m + 1) = a * Ring.choose (a - 1) m / (m + 1) := by
      field_simp; linarith
    have hcont := (continuousOn_struveBinomRem (a - 1) m).mono (show Icc 0 u ⊆ Ici 0 from
      Icc_subset_Ici_self)
    have hint : IntervalIntegrable (struveBinomRem (a - 1) m) volume 0 u :=
      (hcont.mono (by rw [uIcc_of_le hu])).intervalIntegrable
    rw [struveBinomRem_succ_eq_integral a m hu, hc']
    constructor
    · have : a * Ring.choose (a - 1) m / (m + 1) * (a * ∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s)
          = a ^ 2 / (m + 1) * ∫ s in (0 : ℝ)..u, Ring.choose (a - 1) m * struveBinomRem (a - 1) m s := by
        rw [intervalIntegral.integral_const_mul]; ring
      rw [this]
      refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hu fun s hs => ?_)
      exact (ih' s hs.1).1
    · rw [abs_mul, abs_div, abs_mul, abs_of_pos hm1]
      have hb : |∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s| ≤
          |Ring.choose (a - 1) m| * (u ^ (m + 1) / (m + 1)) := by
        refine (intervalIntegral.abs_integral_le_integral_abs hu).trans ?_
        have hmono : ∫ s in (0 : ℝ)..u, |struveBinomRem (a - 1) m s| ≤
            ∫ s in (0 : ℝ)..u, |Ring.choose (a - 1) m| * s ^ m :=
          intervalIntegral.integral_mono_on hu hint.abs ((by fun_prop : Continuous fun s : ℝ =>
            |Ring.choose (a - 1) m| * s ^ m).intervalIntegrable _ _) fun s hs => (ih' s hs.1).2
        refine hmono.trans (le_of_eq ?_)
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp
      calc |a| * |∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s|
          ≤ |a| * (|Ring.choose (a - 1) m| * (u ^ (m + 1) / (m + 1))) := by gcongr
        _ = _ := by ring

end BinomialRemainder

/-- First omitted term bounds the real positive-argument remainder. -/
theorem struveK_remainder_sign {ν x : ℝ} (hx : 0 < x) (m : ℕ) (hm : ν ≤ m+1/2) :
    let R := struveK ν x-∑ k ∈ Finset.range m, struveAsymptoticTerm ν x k; R.im=0 ∧ R.re*(struveAsymptoticTerm ν x m).re ≥ 0 ∧ ‖R‖ ≤ ‖struveAsymptoticTerm ν x m‖ := by
  intro R
  set a : ℝ := ν - 1 / 2 with ha
  have hxC : 0 < ((x : ℂ)).re := by simpa using hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set p : ℝ := 2 * (x / 2) ^ ν / (Real.sqrt π * Real.Gamma (ν + 1 / 2)) with hpdef
  have hp : 2 * ((x : ℂ) / 2) ^ (ν : ℂ) / (Real.sqrt π * Gamma ((ν : ℂ) + 1 / 2)) = (p : ℂ) := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), show (ν : ℂ) + 1 / 2 = ((ν + 1 / 2 : ℝ) : ℂ) by
        push_cast; ring, Complex.Gamma_ofReal, hpdef]
    push_cast; ring
  set e : ℝ → ℝ := fun t => Real.exp (-x * t) with he
  set L : ℕ → ℝ := fun k => ((2 * k) ! : ℝ) / x ^ (2 * k + 1) with hLdef
  have hpow : ∀ (k : ℕ) (t : ℝ), 0 < t → t ^ (((2 * k + 1 : ℕ) : ℝ) - 1) = (t ^ 2) ^ k := by
    intro k t ht
    rw [show ((2 * k + 1 : ℕ) : ℝ) - 1 = ((2 * k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
  have hLint : ∀ k : ℕ, IntegrableOn (fun t => e t * (t ^ 2) ^ k) (Ioi 0) := fun k =>
    (integrableOn_exp_neg_mul_mul_rpow_sub_one (s := ((2 * k + 1 : ℕ) : ℝ)) (by positivity)
      hx).congr_fun (fun t ht => by simp only [he, hpow k t ht]) measurableSet_Ioi
  have hL : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), e t * (t ^ 2) ^ k = L k := by
    intro k
    have h := integral_exp_neg_mul_mul_rpow_sub_one (s := ((2 * k + 1 : ℕ) : ℝ))
      (by positivity) hx
    rw [show (∫ t in Ioi (0 : ℝ), e t * (t ^ 2) ^ k) = ∫ t in Ioi (0 : ℝ),
      Real.exp (-x * t) * t ^ (((2 * k + 1 : ℕ) : ℝ) - 1) from
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simp only [he, hpow k t ht]), h, show ((2 * k + 1 : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial, Real.rpow_neg hx.le, show ((2 * k : ℕ) : ℝ) + 1 =
      ((2 * k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, hLdef]
    rfl
  have hpt : ∀ t : ℝ, ((e t * (1 + t ^ 2) ^ a : ℝ) : ℂ) =
      exp (-(x : ℂ) * t) * (1 + (t : ℂ) ^ 2) ^ ((ν : ℂ) - 1 / 2) := by
    intro t
    rw [show (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (ν : ℂ) - 1 / 2 = ((ν - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity)]
    simp only [he, ha]
    push_cast
    ring_nf
  have hI0int : IntegrableOn (fun t => e t * (1 + t ^ 2) ^ a) (Ioi 0) := by
    refine (DLMF.Bessel.integrableOn_yLaplaceKernel (ν : ℂ) hxC).norm.mono'
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-x * t)).aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable (by
          exact (continuous_const.add (continuous_pow 2)).rpow_const fun t =>
            Or.inl (by simp only [Pi.add_apply]; positivity)))) ?_
    refine Eventually.of_forall fun t => le_of_eq ?_
    rw [DLMF.Bessel.yLaplaceKernel, ← hpt, Complex.norm_real]
  have hK : struveK ν x = (p : ℂ) * ((∫ t in Ioi (0 : ℝ), e t * (1 + t ^ 2) ^ a : ℝ) : ℂ) := by
    rw [DLMF.Bessel.struveK_eq_integral _ hxC, hp]
    have h := integral_complex_ofReal (f := fun t => e t * (1 + t ^ 2) ^ a)
      (μ := volume.restrict (Ioi 0))
    rw [← h]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [hpt]
  have hT : ∀ k : ℕ, struveAsymptoticTerm ν x k = ((p * (Ring.choose a k * L k) : ℝ) : ℂ) := by
    intro k
    rw [← struveK_coeff_eq (ν : ℂ) hx0 k, hp, Complex.Gamma_nat_eq_factorial,
      show (ν : ℂ) - 1 / 2 = (a : ℂ) by rw [ha]; push_cast; ring,
      ← Complex.ofReal_choose, hLdef]
    push_cast
    field_simp
  have hsumint : IntegrableOn (fun t => ∑ k ∈ Finset.range m,
      Ring.choose a k * (e t * (t ^ 2) ^ k)) (Ioi 0) :=
    integrable_finsetSum _ fun k _ => (hLint k).const_mul _
  have hJ : (∫ t in Ioi (0 : ℝ), e t * (1 + t ^ 2) ^ a) -
      ∑ k ∈ Finset.range m, Ring.choose a k * L k =
      ∫ t in Ioi (0 : ℝ), e t * struveBinomRem a m (t ^ 2) := by
    have h1 : ∑ k ∈ Finset.range m, Ring.choose a k * L k =
        ∫ t in Ioi (0 : ℝ), ∑ k ∈ Finset.range m, Ring.choose a k * (e t * (t ^ 2) ^ k) := by
      rw [integral_finsetSum _ fun k _ => (hLint k).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, hL]
    rw [h1, ← integral_sub hI0int hsumint]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [struveBinomRem, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  set J := ∫ t in Ioi (0 : ℝ), e t * struveBinomRem a m (t ^ 2) with hJdef
  have hJint : IntegrableOn (fun t => e t * struveBinomRem a m (t ^ 2)) (Ioi 0) := by
    refine (hI0int.sub hsumint).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, struveBinomRem, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hR : R = ((p * J : ℝ) : ℂ) := by
    simp only [R]
    rw [hK, Finset.sum_congr rfl fun k _ => hT k, ← hJ]
    push_cast
    rw [mul_sub, Finset.mul_sum]
  have ham : a ≤ m := by rw [ha]; linarith
  have hbd := struveBinomRem_bound m a ham
  have hL0 : 0 ≤ L m := by rw [hLdef]; positivity
  refine ⟨by rw [hR, ofReal_im], ?_, ?_⟩
  · rw [hR, hT m, ofReal_re, ofReal_re]
    have hcJ : 0 ≤ Ring.choose a m * J := by
      rw [hJdef, ← integral_const_mul]
      refine setIntegral_nonneg measurableSet_Ioi fun t _ => ?_
      have := (hbd (t ^ 2) (sq_nonneg t)).1
      have he0 : 0 ≤ e t := (Real.exp_pos _).le
      nlinarith
    have : p * J * (p * (Ring.choose a m * L m)) = p ^ 2 * L m * (Ring.choose a m * J) := by ring
    rw [this]; exact mul_nonneg (mul_nonneg (sq_nonneg _) hL0) hcJ
  · rw [hR, hT m, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul, abs_of_nonneg hL0]
    gcongr
    rw [hJdef, ← hL m, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hJint.abs
      ((hLint m).const_mul _) measurableSet_Ioi fun t _ => ?_)
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have := (hbd (t ^ 2) (sq_nonneg t)).2
    have he0 : 0 ≤ e t := (Real.exp_pos _).le
    calc e t * |struveBinomRem a m (t ^ 2)| ≤ e t * (|Ring.choose a m| * (t ^ 2) ^ m) :=
          mul_le_mul_of_nonneg_left this he0
      _ = _ := by ring

/-- The product of the first `k` factors `ν²-(2j+1)²` in the even Anger asymptotic coefficients. -/
@[dlmf 11.11.E1]
def angerF (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+1)^2)

/-- The product of the first `k` factors `ν²-(2j+2)²` in the odd Anger asymptotic coefficients. -/
@[dlmf 11.11.E1]
def angerG (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+2)^2)

/-- Identity under the stated parameter and domain assumptions: `angerF ν k = (-4)^k*poch
(1/2-ν/2) k*poch (1/2+ν/2) k ∧ angerG ν k = (-4)^k*poch (1-ν/2) k*poch (1+ν/2) k`. -/
@[dlmf 11.11.E1]
theorem angerFG_poch (ν : ℂ) (k : ℕ) :
    angerF ν k = (-4)^k*poch (1/2-ν/2) k*poch (1/2+ν/2) k ∧ angerG ν k = (-4)^k*poch (1-ν/2) k*poch (1+ν/2) k := by
  induction k with
  | zero => simp [angerF, angerG, poch_zero]
  | succ k ih =>
    rcases ih with ⟨ihF, ihG⟩
    have hF : angerF ν (k+1)=angerF ν k*(ν^2-(2*k+1)^2) := by
      simp [angerF, Finset.prod_range_succ]
    have hG : angerG ν (k+1)=angerG ν k*(ν^2-(2*k+2)^2) := by
      simp [angerG, Finset.prod_range_succ]
    rw [hF,hG,ihF,ihG,poch_succ,poch_succ,poch_succ,poch_succ,pow_succ]
    push_cast
    constructor <;> ring

/-- The Taylor data of the Anger kernel in terms of `F_k`, `G_k`. -/
theorem struveAs_coeffD_even_odd (ν : ℂ) (k : ℕ) :
    struveAs_coeffD ν (2 * k) = angerF ν k ∧ struveAs_coeffD ν (2 * k + 1) = -ν * angerG ν k := by
  induction k with
  | zero => simp [struveAs_coeffD, angerF, angerG]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = (2 * k + 1) + 2 by ring,
      struveAs_coeffD, struveAs_coeffD, ih.1, ih.2]
    simp only [angerF, angerG, Finset.prod_range_succ]
    push_cast
    constructor <;> ring

/-- Points of a closed sector `|arg z| ≤ π - δ` near infinity are nonzero and in the slit plane. -/
theorem struveAs_eventually_sector {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z in sector (π - δ), z ≠ 0 ∧ z ∈ slitPlane := by
  rw [sector, eventually_inf_principal]
  refine Eventually.of_forall fun z hz => ⟨hz.1, ?_⟩
  rw [mem_slitPlane_iff_arg]
  refine ⟨fun h => ?_, hz.1⟩
  have := hz.2
  rw [h, abs_of_pos Real.pi_pos] at this
  linarith

/-- DLMF 11.11.4 in the form of an asymptotic expansion in `z^{-n-1}`. -/
theorem struveAs_angerA_sector (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    HasAsymptoticExpansion (sector (π - δ)) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + 1)))
      (fun n => struveAs_coeffD ν n / π) (angerA ν) := by
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hα : |(π - δ) / 2| < π / 2 := by rw [abs_lt]; constructor <;> linarith
  have hα' : |-((π - δ) / 2)| < π / 2 := by rwa [abs_neg]
  exact ((struveAs_angerA_hasAsymptoticExpansion ν hs hα').sup
    (struveAs_angerA_hasAsymptoticExpansion ν hs hα)).mono (sector_le_sup_rotSectorAtTop hδ hδπ)

/-- Pairing consecutive terms of a finite sum. -/
theorem struveAs_sum_range_two_mul (c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N), c n = ∑ k ∈ Finset.range N, (c (2 * k) + c (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- The paired form of the `A_ν` expansion. -/
theorem struveAs_angerA_paired (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerA ν z-(∑ k ∈ Finset.range N, 1/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  have h := struveAs_angerA_sector ν hδ hδπ (2 * N)
  refine (h.congr' ?_ ?_)
  · filter_upwards [struveAs_eventually_sector hδ] with z hz
    congr 1
    have hterm : ∀ m : ℕ, z ^ (-((m : ℂ) + 1)) • (struveAs_coeffD ν m / π) =
        1 / π * (struveAs_coeffD ν m / z ^ (m + 1)) := by
      intro m
      rw [cpow_neg, show (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
        smul_eq_mul]
      field_simp
    simp_rw [hterm]
    rw [struveAs_sum_range_two_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(struveAs_coeffD_even_odd ν k).1, (struveAs_coeffD_even_odd ν k).2,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring]
    ring
  · filter_upwards [struveAs_eventually_sector hδ] with z hz
    rw [cpow_neg, show ((2 * N : ℕ) : ℂ) + 1 = ((2 * N + 1 : ℕ) : ℂ) by push_cast; ring,
      cpow_natCast, zpow_neg, show ((2 * N + 1 : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]

/-- Asymptotic bound with the indicated comparison function: `(fun z : ℂ => angerJ ν z-besselJ ν
z-(∑ k ∈ Finset.range N, sin (π*ν)/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector
(π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ)))`. -/
@[dlmf 11.11.E2]
theorem angerJ_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerJ ν z-besselJ ν z-(∑ k ∈ Finset.range N, sin (π*ν)/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  refine ((struveAs_angerA_paired ν hδ hδπ N).const_mul_left (sin (π * ν))).congr' ?_
    EventuallyEq.rfl
  filter_upwards [struveAs_eventually_sector hδ] with z hz
  rw [anger_bessel ν hz.2, mul_sub, Finset.mul_sum]
  have : ∀ k ∈ Finset.range N, sin (π * ν) * (1 / π * (angerF ν k / z ^ (2 * k + 1) -
      ν * angerG ν k / z ^ (2 * k + 2))) = sin (π * ν) / π * (angerF ν k / z ^ (2 * k + 1) -
      ν * angerG ν k / z ^ (2 * k + 2)) := fun k _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

/-- weberE large argument, DLMF 11.11.3. The sum runs over both terms of the summand; an earlier
transcription bound only the `F_k` terms, leaving an auto-bound `k` in the `G_k` term. -/
@[dlmf 11.11.E3]
theorem weberE_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => weberE ν z+besselY ν z-(∑ k ∈ Finset.range N, (-(1+cos (π*ν))/π*angerF ν k/z^(2*k+1)-ν*(1-cos (π*ν))/π*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  have h1 := (struveAs_angerA_paired ν hδ hδπ N).const_mul_left (-cos (π * ν))
  have h2 := (struveAs_angerA_paired (-ν) hδ hδπ N).neg_left
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [struveAs_eventually_sector hδ] with z hz
  have hF : ∀ k, angerF (-ν) k = angerF ν k := fun k => by simp [angerF]
  have hG : ∀ k, angerG (-ν) k = angerG ν k := fun k => by simp [angerG]
  simp only [hF, hG]
  rw [weber_bessel ν hz.2]
  have : ∑ k ∈ Finset.range N, (-(1+cos (π*ν))/π*angerF ν k/z^(2*k+1) -
      ν*(1-cos (π*ν))/π*angerG ν k/z^(2*k+2)) =
      ∑ k ∈ Finset.range N, (-cos (π * ν) * (1 / π * (angerF ν k / z ^ (2 * k + 1) -
        ν * angerG ν k / z ^ (2 * k + 2))) - 1 / π * (angerF ν k / z ^ (2 * k + 1) -
        -ν * angerG ν k / z ^ (2 * k + 2))) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum (a := -cos (π * ν))]
  set S1 := ∑ k ∈ Finset.range N, 1 / (π : ℂ) * (angerF ν k / z ^ (2 * k + 1) -
    ν * angerG ν k / z ^ (2 * k + 2))
  set S2 := ∑ k ∈ Finset.range N, 1 / (π : ℂ) * (angerF ν k / z ^ (2 * k + 1) -
    -ν * angerG ν k / z ^ (2 * k + 2))
  ring

/-- Asymptotic bound with the indicated comparison function: `(fun z : ℂ => angerA ν z-(∑ k ∈
Finset.range N, 1/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z :
ℂ => z^(-(2*N+1:ℤ)))`. -/
@[dlmf 11.11.E4]
theorem angerA_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerA ν z-(∑ k ∈ Finset.range N, 1/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) :=
  struveAs_angerA_paired ν hδ hδπ N

/-- Large orders separated from all integers. -/
def nonintegerOrderSector (ε : ℝ) : Filter ℂ :=
  sector π ⊓ 𝓟 {ν : ℂ | ∀ n : ℤ, ε ≤ ‖ν-n‖}

/-- `Γ(a+k)⁻¹ Γ(b+k)⁻¹ ∏_{j<k} (a+j)(b+j) = Γ(a)⁻¹ Γ(b)⁻¹`, valid for all `a`, `b`. -/
theorem struveAs_recipGamma_mul_prod (a b : ℂ) (k : ℕ) :
    (Gamma (a + k))⁻¹ * (Gamma (b + k))⁻¹ * ∏ j ∈ Finset.range k, ((a + j) * (b + j)) =
      (Gamma a)⁻¹ * (Gamma b)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a + k)
    have hb := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b + k)
    rw [Finset.prod_range_succ, ← ih, ha, hb]
    push_cast
    rw [show a + k + 1 = a + (k + 1) by ring, show b + k + 1 = b + (k + 1) by ring]
    ring

/-- The product `∏_{j<k} ((j+1)² - (ν/2)²)`. -/
def struveAs_P1 (ν : ℂ) (k : ℕ) : ℂ := ∏ j ∈ Finset.range k, (((j : ℂ) + 1) ^ 2 - (ν / 2) ^ 2)

/-- The product `∏_{j≤k} ((j+1/2)² - (ν/2)²)`. -/
def struveAs_P2 (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range (k + 1), (((j : ℂ) + 1 / 2) ^ 2 - (ν / 2) ^ 2)

/-- Reflection: `Γ(1+x)⁻¹ Γ(1-x)⁻¹ = sin(πx)/(πx)`. -/
theorem struveAs_recipGamma_one_add_mul {x : ℂ} (hx : x ≠ 0) :
    (Gamma (x + 1))⁻¹ * (Gamma (1 - x))⁻¹ = sin (π * x) / (π * x) := by
  have h := Complex.Gamma_mul_Gamma_one_sub x
  rw [Complex.Gamma_add_one x hx]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  by_cases hs : sin (π * x) = 0
  · rw [hs, div_zero] at h
    rcases mul_eq_zero.mp h with h | h <;> simp [h, hs]
  · have hG : Gamma x ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact (div_ne_zero hπ hs) h.symm
    have hG' : Gamma (1 - x) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h; exact (div_ne_zero hπ hs) h.symm
    field_simp
    rw [h, mul_comm x (π : ℂ)]
    field_simp

/-- Reflection: `Γ(1/2+x)⁻¹ Γ(1/2-x)⁻¹ = cos(πx)/π`. -/
theorem struveAs_recipGamma_half_add_mul (x : ℂ) :
    (Gamma (x + 1 / 2))⁻¹ * (Gamma (1 / 2 - x))⁻¹ = cos (π * x) / π := by
  have h := Complex.Gamma_mul_Gamma_one_sub (x + 1 / 2)
  rw [show 1 - (x + 1 / 2) = 1 / 2 - x by ring,
    show (π : ℂ) * (x + 1 / 2) = π * x + π / 2 by ring, Complex.sin_add_pi_div_two] at h
  rw [← mul_inv, h, inv_div]

/-- Nonvanishing under the stated hypotheses: `struveAs_P1 ν k ≠ 0`. -/
theorem struveAs_P1_ne_zero {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (k : ℕ) : struveAs_P1 ν k ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ h => ?_
  have h' : ((j : ℂ) + 1 - ν / 2) * ((j : ℂ) + 1 + ν / 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h | h
  · exact hν (2 * j + 2) (by push_cast; linear_combination -2 * h)
  · exact hν (-(2 * j + 2)) (by push_cast; linear_combination 2 * h)

/-- Nonvanishing under the stated hypotheses: `struveAs_P2 ν k ≠ 0`. -/
theorem struveAs_P2_ne_zero {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (k : ℕ) : struveAs_P2 ν k ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ h => ?_
  have h' : ((j : ℂ) + 1 / 2 - ν / 2) * ((j : ℂ) + 1 / 2 + ν / 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h | h
  · exact hν (2 * j + 1) (by push_cast; linear_combination -2 * h)
  · exact hν (-(2 * j + 1)) (by push_cast; linear_combination 2 * h)

/-- The series with terms `(fun k : ℕ => (-1) ^ k * (z / 2) ^ (2 * k) / struveAs_P1 ν k)`
converges to `(π * (ν / 2) / sin (π * (ν / 2)) * angerS1 ν z)`. -/
theorem struveAs_hasSum_S1 {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (z : ℂ) :
    HasSum (fun k : ℕ => (-1) ^ k * (z / 2) ^ (2 * k) / struveAs_P1 ν k)
      (π * (ν / 2) / sin (π * (ν / 2)) * angerS1 ν z) := by
  have hx : ν / 2 ≠ 0 := fun h => hν 0 (by push_cast; linear_combination 2 * h)
  have hs : sin (π * (ν / 2)) ≠ 0 := sin_pi_mul_ne_zero_of_not_int (not_int_half hν)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  refine ((hasSum_angerS1 ν z).mul_left _).congr_fun fun k => ?_
  have h := struveAs_recipGamma_mul_prod (ν / 2 + 1) (1 - ν / 2) k
  rw [struveAs_recipGamma_one_add_mul hx] at h
  have hP : ∏ j ∈ Finset.range k, ((ν / 2 + 1 + j) * (1 - ν / 2 + j)) = struveAs_P1 ν k :=
    Finset.prod_congr rfl fun j _ => by ring
  rw [hP] at h
  have hP0 := struveAs_P1_ne_zero hν k
  have e : (Gamma (k + ν / 2 + 1) * Gamma (k - ν / 2 + 1))⁻¹ =
      sin (π * (ν / 2)) / (π * (ν / 2)) / struveAs_P1 ν k := by
    rw [← h, mul_inv, show ν / 2 + 1 + (k : ℂ) = k + ν / 2 + 1 by ring,
      show 1 - ν / 2 + (k : ℂ) = k - ν / 2 + 1 by ring]
    field_simp
  have e' : (-1) ^ k * (z / 2) ^ (2 * k) / (Gamma (k + ν / 2 + 1) * Gamma (k - ν / 2 + 1)) =
      (-1) ^ k * (z / 2) ^ (2 * k) * (sin (π * (ν / 2)) / (π * (ν / 2)) / struveAs_P1 ν k) := by
    rw [div_eq_mul_inv, e]
  rw [e']
  have hs' : sin (π * ν / 2) ≠ 0 := by rwa [mul_div_assoc]
  have hν0 : ν ≠ 0 := fun h0 => hx (by rw [h0, zero_div])
  field_simp

/-- The series with terms `(fun k : ℕ => (-1) ^ k * (z / 2) ^ (2 * k + 1) / struveAs_P2 ν k)`
converges to `(π / cos (π * (ν / 2)) * angerS2 ν z)`. -/
theorem struveAs_hasSum_S2 {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (z : ℂ) :
    HasSum (fun k : ℕ => (-1) ^ k * (z / 2) ^ (2 * k + 1) / struveAs_P2 ν k)
      (π / cos (π * (ν / 2)) * angerS2 ν z) := by
  have hs : sin (π * ν) ≠ 0 := sin_pi_mul_ne_zero_of_not_int hν
  have hc : cos (π * (ν / 2)) ≠ 0 := by
    intro h; apply hs
    rw [show (π : ℂ) * ν = 2 * (π * (ν / 2)) by ring, Complex.sin_two_mul, h, mul_zero]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  refine ((hasSum_angerS2 ν z).mul_left _).congr_fun fun k => ?_
  have h := struveAs_recipGamma_mul_prod (ν / 2 + 1 / 2) (1 / 2 - ν / 2) (k + 1)
  rw [struveAs_recipGamma_half_add_mul] at h
  have hP : ∏ j ∈ Finset.range (k + 1), ((ν / 2 + 1 / 2 + j) * (1 / 2 - ν / 2 + j)) =
      struveAs_P2 ν k := Finset.prod_congr rfl fun j _ => by ring
  rw [hP] at h
  have hP0 := struveAs_P2_ne_zero hν k
  have e : (Gamma (k + ν / 2 + 3 / 2) * Gamma (k - ν / 2 + 3 / 2))⁻¹ =
      cos (π * (ν / 2)) / π / struveAs_P2 ν k := by
    rw [← h, mul_inv]
    push_cast
    rw [show ν / 2 + 1 / 2 + ((k : ℂ) + 1) = k + ν / 2 + 3 / 2 by ring,
      show 1 / 2 - ν / 2 + ((k : ℂ) + 1) = k - ν / 2 + 3 / 2 by ring]
    field_simp
  have e' : (-1) ^ k * (z / 2) ^ (2 * k + 1) /
      (Gamma (k + ν / 2 + 3 / 2) * Gamma (k - ν / 2 + 3 / 2)) =
      (-1) ^ k * (z / 2) ^ (2 * k + 1) * (cos (π * (ν / 2)) / π / struveAs_P2 ν k) := by
    rw [div_eq_mul_inv, e]
  rw [e']
  have hc' : cos (π * ν / 2) ≠ 0 := by rwa [mul_div_assoc]
  field_simp

/-- `π ν / sin(π ν) · 𝐉_ν(z)` as a pair of series rational in `ν`. -/
theorem struveAs_angerJ_scaled_eq {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (z : ℂ) :
    π * ν / sin (π * ν) * angerJ ν z =
      π * (ν / 2) / sin (π * (ν / 2)) * angerS1 ν z +
        ν / 2 * (π / cos (π * (ν / 2)) * angerS2 ν z) := by
  have hs : sin (π * ν) ≠ 0 := sin_pi_mul_ne_zero_of_not_int hν
  have h2 : sin (π * ν) = 2 * sin (π * (ν / 2)) * cos (π * (ν / 2)) := by
    rw [show (π : ℂ) * ν = 2 * (π * (ν / 2)) by ring, Complex.sin_two_mul]
  have hs2 : sin (π * (ν / 2)) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have hc2 : cos (π * (ν / 2)) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  rw [angerJ_series, h2, show (π : ℂ) * ν / 2 = π * (ν / 2) by ring]
  set sn := sin (π * (ν / 2))
  set cs := cos (π * (ν / 2))
  field_simp

/-- Estimate under the stated parameter and domain assumptions: `e * m ≤ ‖u * v‖`. -/
theorem struveAs_norm_mul_ge {u v : ℂ} {e m : ℝ} (he : 0 ≤ e) (hu : e ≤ ‖u‖)
    (hv : e ≤ ‖v‖) (huv : 2 * m ≤ ‖u‖ + ‖v‖) : e * m ≤ ‖u * v‖ := by
  rw [norm_mul]
  rcases le_total ‖u‖ ‖v‖ with h | h
  · have : m ≤ ‖v‖ := by linarith
    nlinarith [norm_nonneg u]
  · have : m ≤ ‖u‖ := by linarith
    nlinarith [norm_nonneg v]

/-- Estimate under the stated parameter and domain assumptions: `ε / 2 * ((a : ℝ) / 2) ≤ ‖((a : ℂ)
/ 2) ^ 2 - (ν / 2) ^ 2‖ ∨ (a : ℝ) < 0`. -/
theorem struveAs_factor_ge {ν : ℂ} {ε : ℝ} (hε : 0 < ε) (hν : ∀ n : ℤ, ε ≤ ‖ν - n‖) (a : ℤ) :
    ε / 2 * ((a : ℝ) / 2) ≤ ‖((a : ℂ) / 2) ^ 2 - (ν / 2) ^ 2‖ ∨ (a : ℝ) < 0 := by
  rcases lt_or_ge (a : ℝ) 0 with h | h
  · exact Or.inr h
  left
  have hu : ε / 2 ≤ ‖(a : ℂ) / 2 - ν / 2‖ := by
    rw [show (a : ℂ) / 2 - ν / 2 = -(ν - a) / 2 by ring, norm_div, norm_neg, Complex.norm_two]
    linarith [hν a]
  have hv : ε / 2 ≤ ‖(a : ℂ) / 2 + ν / 2‖ := by
    rw [show (a : ℂ) / 2 + ν / 2 = (ν - ((-a : ℤ) : ℂ)) / 2 by push_cast; ring, norm_div,
      Complex.norm_two]
    linarith [hν (-a)]
  have huv : 2 * ((a : ℝ) / 2) ≤ ‖(a : ℂ) / 2 - ν / 2‖ + ‖(a : ℂ) / 2 + ν / 2‖ := by
    have := norm_add_le ((a : ℂ) / 2 - ν / 2) ((a : ℂ) / 2 + ν / 2)
    rw [show (a : ℂ) / 2 - ν / 2 + ((a : ℂ) / 2 + ν / 2) = ((a : ℝ) : ℂ) by push_cast; ring,
      norm_real, Real.norm_eq_abs, abs_of_nonneg h] at this
    linarith
  have := struveAs_norm_mul_ge (by linarith) hu hv huv
  rw [show ((a : ℂ) / 2 - ν / 2) * ((a : ℂ) / 2 + ν / 2) = ((a : ℂ) / 2) ^ 2 - (ν / 2) ^ 2 by
    ring] at this
  exact this

/-- Estimate under the stated parameter and domain assumptions: `‖x‖ ^ 2 - ‖c‖ ^ 2 ≤ ‖c ^ 2 - x ^
2‖`. -/
theorem struveAs_factor_ge_sq (c x : ℂ) : ‖x‖ ^ 2 - ‖c‖ ^ 2 ≤ ‖c ^ 2 - x ^ 2‖ := by
  have := norm_sub_norm_le (x ^ 2) (c ^ 2)
  rw [norm_pow, norm_pow, norm_sub_rev] at this
  exact this

/-- Estimate under the stated parameter and domain assumptions: `‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k *
k !) ≤ ‖struveAs_P1 ν (k + 1)‖`. -/
theorem struveAs_P1_tail_ge {ν : ℂ} {ε : ℝ} (hε : 0 < ε) (hν : ∀ n : ℤ, ε ≤ ‖ν - n‖)
    (hx : 2 ≤ ‖ν / 2‖) (k : ℕ) :
    ‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !) ≤ ‖struveAs_P1 ν (k + 1)‖ := by
  rw [struveAs_P1, Finset.prod_range_succ', norm_mul, norm_prod, mul_comm (‖ν / 2‖ ^ 2 / 4)]
  refine mul_le_mul ?_ ?_ (by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  rotate_left
  · have := struveAs_factor_ge_sq (((0 : ℕ) : ℂ) + 1) (ν / 2)
    simp only [Nat.cast_zero, zero_add, norm_one, one_pow] at this ⊢
    nlinarith
  · rw [show (ε / 2) ^ k * (k ! : ℝ) = ∏ i ∈ Finset.range k, (ε / 2 * ((i : ℝ) + 1)) by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      congr 1
      rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    rcases struveAs_factor_ge hε hν (2 * ((i + 1 : ℕ) : ℤ) + 2) with h | h
    · push_cast at h ⊢
      rw [show (2 * ((i : ℂ) + 1) + 2) / 2 = (i : ℂ) + 1 + 1 by ring] at h
      refine le_trans ?_ h
      gcongr
      linarith
    · push_cast at h; linarith

/-- Estimate under the stated parameter and domain assumptions: `(‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2)
^ k * k !) ≤ ‖struveAs_P2 ν (k + 1)‖`. -/
theorem struveAs_P2_tail_ge {ν : ℂ} {ε : ℝ} (hε : 0 < ε) (hν : ∀ n : ℤ, ε ≤ ‖ν - n‖)
    (hx : 2 ≤ ‖ν / 2‖) (k : ℕ) :
    (‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !) ≤ ‖struveAs_P2 ν (k + 1)‖ := by
  rw [struveAs_P2, Finset.prod_range_succ', Finset.prod_range_succ', norm_mul, norm_mul,
    norm_prod]
  have h0 := struveAs_factor_ge_sq (((0 : ℕ) : ℂ) + 1 / 2) (ν / 2)
  have h1 := struveAs_factor_ge_sq ((((0 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2) (ν / 2)
  have hc0 : ‖(((0 : ℕ) : ℂ) + 1 / 2)‖ = 1 / 2 := by simp
  have hc1 : ‖((((0 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2)‖ = 3 / 2 := by
    rw [show (((0 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2 = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [hc0] at h0; rw [hc1] at h1
  have hP : (ε / 2) ^ k * (k ! : ℝ) ≤
      ∏ i ∈ Finset.range k, ‖((((i + 1 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2) ^ 2 - (ν / 2) ^ 2‖ := by
    rw [show (ε / 2) ^ k * (k ! : ℝ) = ∏ i ∈ Finset.range k, (ε / 2 * ((i : ℝ) + 1)) by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      congr 1
      rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    rcases struveAs_factor_ge hε hν (2 * ((i + 1 + 1 : ℕ) : ℤ) + 1) with h | h
    · push_cast at h ⊢
      rw [show (2 * ((i : ℂ) + 1 + 1) + 1) / 2 = (i : ℂ) + 1 + 1 + 1 / 2 by ring] at h
      refine le_trans ?_ h
      gcongr
      linarith
    · push_cast at h; linarith
  have hx2 : 4 ≤ ‖ν / 2‖ ^ 2 := by nlinarith
  have e0 : ‖ν / 2‖ ^ 2 / 4 ≤ ‖(((0 : ℕ) : ℂ) + 1 / 2) ^ 2 - (ν / 2) ^ 2‖ := by nlinarith
  have e1 : ‖ν / 2‖ ^ 2 / 4 ≤ ‖((((0 + 1 : ℕ) : ℕ) : ℂ) + 1 / 2) ^ 2 - (ν / 2) ^ 2‖ := by
    nlinarith
  calc (‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !)
      = (((ε / 2) ^ k * k !) * (‖ν / 2‖ ^ 2 / 4)) * (‖ν / 2‖ ^ 2 / 4) := by ring
    _ ≤ _ := by
      refine mul_le_mul (mul_le_mul hP e1 (by positivity) (by positivity)) e0 (by positivity)
        (by positivity)

/-- The quantitative form of DLMF 11.11.5: for `|ν| ≥ 4` at distance `≥ ε` from the integers,
`|πν/sin(πν) 𝐉_ν(z) - 1 + νz/(ν²-1)| ≤ K/|ν/2|²`. -/
theorem struveAs_angerJ_large_order_bound (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ ν : ℂ, (∀ n : ℤ, ε ≤ ‖ν - n‖) → 2 ≤ ‖ν / 2‖ →
      ‖π * ν / sin (π * ν) * angerJ ν z - 1 + ν * z / (ν ^ 2 - 1)‖ ≤ K / ‖ν / 2‖ ^ 2 := by
  set c := ‖z / 2‖ ^ 2 * (2 / ε)
  have hE := (Real.summable_pow_div_factorial c).hasSum
  set E := ∑' k : ℕ, c ^ k / (k ! : ℝ)
  refine ⟨4 * ‖z / 2‖ ^ 2 * E + 16 * ‖z / 2‖ ^ 3 * E, fun ν hν hx => ?_⟩
  have hν' : ∀ n : ℤ, ν ≠ n := fun n h => by
    have := hν n; rw [h, sub_self, norm_zero] at this; linarith
  have hx0 : 0 < ‖ν / 2‖ := by linarith
  have hε0 : ε ≠ 0 := hε.ne'
  have h1 := struveAs_hasSum_S1 hν' z
  have h2 := struveAs_hasSum_S2 hν' z
  rw [← hasSum_nat_add_iff' 1] at h1 h2
  have e1 : struveAs_P1 ν 0 = 1 := by simp [struveAs_P1]
  have e2 : struveAs_P2 ν 0 = (1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2 := by simp [struveAs_P2]
  simp only [Finset.range_one, Finset.sum_singleton, e1, e2, pow_zero, mul_zero, div_one,
    one_mul] at h1 h2
  -- the identity
  have hP20 : ((1 / 2 : ℂ)) ^ 2 - (ν / 2) ^ 2 ≠ 0 := by
    have := struveAs_P2_ne_zero hν' 0
    simpa [struveAs_P2] using this
  have hν2 : ν ^ 2 - 1 ≠ 0 := fun h => hP20 (by linear_combination (-1 / 4 : ℂ) * h)
  have hid : π * ν / sin (π * ν) * angerJ ν z - 1 + ν * z / (ν ^ 2 - 1) =
      (π * (ν / 2) / sin (π * (ν / 2)) * angerS1 ν z - 1) +
        ν / 2 * (π / cos (π * (ν / 2)) * angerS2 ν z - (z / 2) ^ (0 + 1) /
          ((1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2)) := by
    have h1ν : 1 - ν ^ 2 ≠ 0 := fun h => hν2 (by linear_combination -h)
    rw [struveAs_angerJ_scaled_eq hν' z]
    field_simp
    ring
  rw [hid]
  -- the bounds
  have hb1 : ∀ k : ℕ, ‖(-1) ^ (k + 1) * (z / 2) ^ (2 * (k + 1)) / struveAs_P1 ν (k + 1)‖ ≤
      4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2 * (c ^ k / k !) := by
    intro k
    have hP := struveAs_P1_tail_ge hε hν hx k
    have hpos : 0 < ‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !) := by positivity
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖z / 2‖ ^ (2 * (k + 1)) / ‖struveAs_P1 ν (k + 1)‖
        ≤ ‖z / 2‖ ^ (2 * (k + 1)) / (‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !)) :=
          div_le_div_of_nonneg_left (by positivity) hpos hP
      _ = _ := by
          simp only [c]
          rw [mul_pow, div_pow, div_pow]
          field_simp
          ring
  have hb2 : ∀ k : ℕ, ‖ν / 2 * ((-1) ^ (k + 1) * (z / 2) ^ (2 * (k + 1) + 1) /
      struveAs_P2 ν (k + 1))‖ ≤ 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2 * (c ^ k / k !) := by
    intro k
    have hP := struveAs_P2_tail_ge hε hν hx k
    have hpos : 0 < (‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !) := by positivity
    rw [norm_mul (ν / 2), norm_div ((-1 : ℂ) ^ (k + 1) * (z / 2) ^ (2 * (k + 1) + 1)),
      norm_mul ((-1 : ℂ) ^ (k + 1)), norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖ν / 2‖ * (‖z / 2‖ ^ (2 * (k + 1) + 1) / ‖struveAs_P2 ν (k + 1)‖)
        ≤ ‖ν / 2‖ * (‖z / 2‖ ^ (2 * (k + 1) + 1) /
            ((‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !))) := by
          gcongr
      _ = 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 3 * (c ^ k / k !) := by
          have hεk : ε ^ k * ε⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hε0, one_pow]
          simp only [c]
          rw [mul_pow, div_pow, div_pow]
          field_simp
          linear_combination (-(‖z / 2‖ ^ 3 * ‖z / 2‖ ^ (k * 2) * 2 ^ k * 16)) * hεk
      _ ≤ _ := by
          have : ‖ν / 2‖ ^ 2 ≤ ‖ν / 2‖ ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
            (by positivity) this) (by positivity)
  have n1 := h1.norm_le_of_bounded (hE.mul_left (4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2)) hb1
  have n2 := (h2.mul_left (ν / 2)).norm_le_of_bounded
    (hE.mul_left (16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2)) hb2
  refine (norm_add_le _ _).trans ?_
  have : 4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2 * E + 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2 * E =
      (4 * ‖z / 2‖ ^ 2 * E + 16 * ‖z / 2‖ ^ 3 * E) / ‖ν / 2‖ ^ 2 := by ring
  rw [← this]
  exact add_le_add n1 n2

/-- Asymptotic bound with the indicated comparison function: `(fun ν : ℂ => π*ν/sin (π*ν)*angerJ ν
z-1+ν*z/(ν^2-1)) =O[nonintegerOrderSector ε] (fun ν : ℂ => ν^(-2:ℤ))`. -/
@[dlmf 11.11.E5]
theorem angerJ_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/sin (π*ν)*angerJ ν z-1+ν*z/(ν^2-1)) =O[nonintegerOrderSector ε] (fun ν : ℂ => ν^(-2:ℤ)) := by
  obtain ⟨K, hK⟩ := struveAs_angerJ_large_order_bound z hε
  have hev : ∀ᶠ ν : ℂ in nonintegerOrderSector ε, 4 ≤ ‖ν‖ ∧ ∀ n : ℤ, ε ≤ ‖ν - n‖ := by
    rw [nonintegerOrderSector, sector, eventually_inf_principal, eventually_inf_principal]
    exact (tendsto_comap.eventually (eventually_ge_atTop 4)).mono fun ν h4 _ hn => ⟨h4, hn⟩
  refine IsBigO.of_bound (4 * K) ?_
  filter_upwards [hev] with ν hν
  have hx : 2 ≤ ‖ν / 2‖ := by rw [norm_div, Complex.norm_two]; linarith [hν.1]
  have hν0 : 0 < ‖ν‖ := by linarith [hν.1]
  refine (hK ν hν.2 hx).trans (le_of_eq ?_)
  rw [norm_zpow, norm_div, Complex.norm_two, zpow_neg, zpow_two]
  field_simp
  ring

end DLMF.Struve
end
