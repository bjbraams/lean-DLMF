/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.Pochhammer

public import DLMF.Hypergeometric.Series
public import Mathlib.Analysis.Normed.Group.Tannery
public import Carlson.TwoVariable.GaussHypergeometric

/-!
# Euler's integral representation (AAR §2.2)

AAR Theorem 2.2.1: for `Re c > Re b > 0` and `|z| < 1`,

$$
{}_2F_1(a,b;c;z)=\frac{\Gamma(c)}{\Gamma(b)\Gamma(c-b)}
\int_0^1 t^{b-1}(1-t)^{c-b-1}(1-zt)^{-a}\,dt.
$$

Gauss's summation theorem (the case `z = 1`) is recorded as `gauss_summation`; its proof is
`Carlson.ordinaryHypergeometric_one` from lean-codes.
-/

@[expose] public section

open Complex intervalIntegral MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.Hypergeometric

/-- Helper lemma for `ordinaryHypergeometric_eq_integral`. -/
theorem re_c_pos_of {b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re) : 0 < c.re := by
  have : c.re = b.re + (c - b).re := by simp [sub_re]
  linarith

/-- Helper lemma for `ordinaryHypergeometric_eq_integral`. -/
theorem not_neg_nat_of_re_pos {w : ℂ} (hw : 0 < w.re) : ∀ k : ℕ, w ≠ -k := by
  intro k hk
  have : w.re = -k := by simpa using congrArg Complex.re hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- Helper lemma for `ordinaryHypergeometric_eq_integral`.
AAR's binomial expansion of `(1-zt)^{-a}` on `t ∈ [0,1]`. -/
theorem hasSum_one_sub_mul_cpow {a z : ℂ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch a n / n.factorial * (z * t) ^ n) ((1 - z * t) ^ (-a)) := by
  have hzt : ‖z * (t : ℂ)‖ < 1 := by
    rw [norm_mul]
    have htnorm : ‖(t : ℂ)‖ = |t| := by simp
    rw [htnorm]
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    nlinarith [norm_nonneg z, hz, abs_nonneg t]
  simpa using hasSum_poch_div_factorial (β := a) (z := z * t) hzt

/-- Helper lemma for `ordinaryHypergeometric_eq_integral`. -/
theorem euler_term_eq_gaussHGCoeff {a b c : ℂ} (n : ℕ)
    (hb : 0 < b.re) (hcb : 0 < (c - b).re) :
    Gamma c / (Gamma b * Gamma (c - b)) *
        (poch a n / n.factorial * betaIntegral (b + n) (c - b)) =
      gaussHGCoeff a b c n := by
  have hb' : 0 < (b + n).re := by
    have : (b + n).re = b.re + n := by simp
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hGamma := Gamma_mul_Gamma_eq_betaIntegral hb' hcb
  have hcpos := re_c_pos_of hb hcb
  have hc : ∀ k : ℕ, c ≠ -k := not_neg_nat_of_re_pos hcpos
  have hbn : ∀ k : ℕ, b ≠ -k := not_neg_nat_of_re_pos hb
  have hcn : Gamma (c + n) ≠ 0 := Gamma_ne_zero (not_neg_nat_add_nat hc n)
  have hb0 : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hc0 : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hcpos
  have hcb0 : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hbeta : betaIntegral (b + n) (c - b) =
      Gamma (b + n) * Gamma (c - b) / Gamma (c + n) := by
    have hsum : b + n + (c - b) = c + n := by ring
    rw [hsum] at hGamma
    exact eq_div_of_mul_eq hcn (by rw [mul_comm]; exact hGamma.symm)
  have hpochb : Gamma (b + n) / Gamma b = poch b n := Gamma_add_nat_div_Gamma_eq b hbn
  have hpochc : Gamma (c + n) / Gamma c = poch c n := Gamma_add_nat_div_Gamma_eq c hc
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hcp : poch c n ≠ 0 := poch_ne_zero_of_not_neg_nat hc n
  have hbmul : Gamma (b + n) = poch b n * Gamma b := (div_eq_iff hb0).mp hpochb
  have hcmul : Gamma (c + n) = poch c n * Gamma c := (div_eq_iff hc0).mp hpochc
  rw [hbeta, gaussHGCoeff, hbmul, hcmul]
  field [hb0, hc0, hcb0, hcn, hf, hcp]

/-- Euler's integral representation of `₂F₁`, AAR Theorem 2.2.1. -/
@[dlmf 15.6.E1]
theorem ordinaryHypergeometric_eq_integral {a b c z : ℂ}
    (hb : 0 < b.re) (hcb : 0 < (c - b).re) (hz : ‖z‖ < 1) :
    ₂F₁ a b c z =
      Gamma c / (Gamma b * Gamma (c - b)) *
        ∫ t : ℝ in (0 : ℝ)..1,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)
  let d : ℕ → ℂ := fun n => poch a n / n.factorial * z ^ n
  let F : ℕ → ℝ → ℂ := fun n t => w t * (d n * (t : ℂ) ^ n)
  have hw : IntervalIntegrable w volume 0 1 := betaIntegral_convergent hb hcb
  have hd : Summable (fun n => ‖d n‖) := (hasSum_poch_div_factorial (β := a) hz).summable.norm
  have hFi (n : ℕ) : IntervalIntegrable (F n) volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := volume)
    (F := F) (f := fun t => w t * (1 - z * t) ^ (-a))
    (fun n t => ‖d n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => hd.mul_right ‖w t‖)
    (by
      simp_rw [tsum_mul_right]
      exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t ht => ?_)
  · have hterm (n : ℕ) :
        ∫ t : ℝ in (0 : ℝ)..1, F n t =
          (poch a n / n.factorial * betaIntegral (b + n) (c - b)) * z ^ n := by
      rw [betaIntegral, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht.1)
      have hp : (t : ℂ) ^ (b + n - 1) = (t : ℂ) ^ (b - 1) * (t : ℂ) ^ n := by
        rw [show b + n - 1 = (b - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast]
      dsimp [F, w, d]
      rw [hp]
      ring
    have hs' := hs.mul_left (Gamma c / (Gamma b * Gamma (c - b)))
    have hscaled (n : ℕ) : Gamma c / (Gamma b * Gamma (c - b)) *
        (∫ t : ℝ in (0 : ℝ)..1, F n t) = gaussHGCoeff a b c n * z ^ n := by
      rw [hterm, ← mul_assoc, euler_term_eq_gaussHGCoeff n hb hcb]
    simp_rw [hscaled] at hs'
    exact ((hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow
      (mem_eball_one_of_norm_lt_one hz)).unique hs'
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    calc
      ‖F n t‖ = ‖w t‖ * (‖d n‖ * ‖(t : ℂ)‖ ^ n) := by
        simp only [F, norm_mul, norm_pow]
      _ ≤ ‖w t‖ * (‖d n‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ht1) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have h := (hasSum_one_sub_mul_cpow (a := a) ht' hz).mul_left (w t)
    simpa only [F, d, mul_pow, mul_assoc] using h

section GaussSummation

open Filter Nat
open scoped Topology

/-- The value of `₂F₁(a, b; c; 1)` as the sum of the Gauss coefficients. -/
theorem ordinaryHypergeometric_one_eq_tsum (a b c : ℂ) :
    ₂F₁ a b c (1 : ℂ) = ∑' n, gaussHGCoeff a b c n := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul, one_pow, mul_one]
  congr 1
  funext n
  simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- For `Re z ≥ 0`, `(Re z)ₖ ≤ ‖(z)ₖ‖`. -/
theorem poch_eval_re_le_norm_poch {z : ℂ} (hz : 0 ≤ z.re) (k : ℕ) :
    (ascPochhammer ℝ k).eval z.re ≤ ‖poch z k‖ := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, norm_mul, ascPochhammer_succ_eval]
    have hle : z.re + k ≤ ‖z + k‖ := by
      simpa using re_le_norm (z + k)
    exact mul_le_mul ih hle (by positivity) (norm_nonneg _)

/-- Gauss's summation theorem: `₂F₁(a,b;c;1) = Γ(c)Γ(c-a-b)/(Γ(c-a)Γ(c-b))`
when `Re(c-a-b) > 0` and `c` is not a nonpositive integer. -/
@[dlmf 15.4.E20]
theorem gauss_summation {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (h : 0 < (c - a - b).re) :
    ₂F₁ a b c (1 : ℂ) =
      Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) :=
  Carlson.ordinaryHypergeometric_one hc h

end GaussSummation

/-- Helper lemma for `chu_vandermonde`: the Pochhammer form of the Chu–Vandermonde identity. -/
theorem chu_vandermonde_sum (n : ℕ) (b c : ℂ) :
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ k * n.choose k * poch b k * poch (c + k) (n - k) = poch (c - b) n := by
  induction n generalizing b c with
  | zero => simp [poch_zero]
  | succ n ih =>
    let f : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * poch b k * poch (c + k) (n + 1 - k)
    have hf0 : f 0 = poch c (n + 1) := by
      simp [f, poch_zero]
    have hf_succ (k : ℕ) : f (k + 1) =
        -b * ((-1 : ℂ) ^ k * poch (b + 1) k * poch (c + 1 + k) (n - k)) := by
      have hk : n + 1 - (k + 1) = n - k := by omega
      have harg : (c + (k + 1 : ℕ) : ℂ) = c + 1 + k := by push_cast; ring
      simp only [f, pow_succ, hk, harg, poch_succ_left b k]
      ring
    have hsplit :
        ∑ k ∈ Finset.range (n + 2), (n + 1).choose k * f k =
          ∑ k ∈ Finset.range (n + 1), n.choose k * f k +
            ∑ k ∈ Finset.range (n + 1), n.choose k * f (k + 1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
      have hch : ∀ i ∈ Finset.range (n + 1),
          ((n + 1).choose (i + 1) : ℂ) = n.choose i + n.choose (i + 1) := by
        intro i _
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one]
        simp
      have hsum := Finset.sum_congr (s₁ := Finset.range (n + 1)) rfl
        (fun i hi => show ((n + 1).choose (i + 1) : ℂ) * f (i + 1) =
            (n.choose i + n.choose (i + 1) : ℂ) * f (i + 1) by rw [hch i hi])
      rw [hsum]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have htail :
          ∑ i ∈ Finset.range (n + 1), (n.choose (i + 1) : ℂ) * f (i + 1) =
            ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * f k - f 0 := by
        rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
        -- ∑_{i=0}^{n-1} C(n,i+1) f(i+1) = ∑_{j=1}^{n} C(n,j) f j
        have hreindex :=
          Finset.sum_range_succ' (fun j => (n.choose j : ℂ) * f j) n
        -- hreindex: ∑ range (n+1) C(n,j) f j = C(n,0) f 0 + ∑ range n C(n,j+1) f(j+1)
        have : ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℂ) * f (i + 1) =
            ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * f k - f 0 := by
          rw [hreindex]
          simp [Nat.choose_zero_right]
        simpa using this
      rw [htail]
      ring
    have hfirst :
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * f k =
          (c + n) * poch (c - b) n := by
      have hterm : ∀ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * f k =
            (c + n) * ((-1 : ℂ) ^ k * n.choose k * poch b k * poch (c + k) (n - k)) := by
        intro k hk
        have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hsub : n + 1 - k = (n - k) + 1 := by omega
        simp only [f, hsub, poch_succ (c + k) (n - k)]
        have : (c + k + (n - k : ℕ) : ℂ) = c + n := by
          rw [Nat.cast_sub hk']
          ring
        rw [this]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih]
    have hsecond :
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * f (k + 1) =
          -b * poch (c - b) n := by
      have hterm : ∀ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * f (k + 1) =
            -b * ((-1 : ℂ) ^ k * n.choose k * poch (b + 1) k *
              poch ((c + 1) + k) (n - k)) := by
        intro k _
        rw [hf_succ]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih (b + 1) (c + 1)]
      simp
    -- Reassemble.
    have hsum := hsplit
    -- The left-hand side of `hsplit` is the `n.succ` instance of the claimed sum.
    have hgoal :
        ∑ k ∈ Finset.range (n + 2),
          (-1 : ℂ) ^ k * (n + 1).choose k * poch b k * poch (c + k) (n + 1 - k) =
          ∑ k ∈ Finset.range (n + 2), (n + 1).choose k * f k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [f]
      ring
    rw [hgoal, hsum, hfirst, hsecond, poch_succ]
    ring

/-- Chu–Vandermonde: the terminating Gauss sum, AAR as the case `a = -n` of Gauss summation. -/
@[dlmf 15.4.E24]
theorem chu_vandermonde (n : ℕ) {b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    ₂F₁ (-n : ℂ) b c (1 : ℂ) = poch (c - b) n / poch c n := by
  have hcn := poch_ne_zero_of_not_neg_nat hc n
  rw [ordinaryHypergeometric_eq_sum_neg_nat, eq_div_iff hcn]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      gaussHGCoeff (-(n : ℂ)) b c k * (1 : ℂ) ^ k * poch c n =
        (-1 : ℂ) ^ k * n.choose k * poch b k * poch (c + k) (n - k) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hck := poch_ne_zero_of_not_neg_nat hc k
    have hadd := poch_add c k (n - k)
    rw [Nat.add_sub_of_le hk'] at hadd
    rw [one_pow, mul_one, gaussHGCoeff_neg_nat]
    field_simp [hck]
    rw [hadd]
    ring
  rw [mul_comm, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun k hk => ?_).trans (chu_vandermonde_sum n b c)
  convert hterm k hk using 1
  ring



/-- The binomial theorem for rising factorials (Chu–Vandermonde). -/
theorem poch_add_binomial_sum (u v : ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * poch u j * poch v (n - j) = poch (u + v) n := by
  have hchu := chu_vandermonde_sum n v (1 - u - n)
  have href := poch_reflect (u + v) n
  rw [show 1 - (u + v) - (n : ℂ) = 1 - u - n - v by ring] at href
  rw [← hchu] at href
  have hs : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [← Finset.sum_range_reflect]
  have key : poch (u + v) n = (-1) ^ n * ∑ k ∈ Finset.range (n + 1),
      (-1) ^ k * (n.choose k : ℂ) * poch v k * poch (1 - u - n + k) (n - k) := by
    rw [href]; linear_combination (-(poch (u + v) n)) * hs
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm hkn, Nat.sub_sub_self hkn]
  have hr := poch_reflect u (n - k)
  rw [show 1 - u - ((n - k : ℕ) : ℂ) = 1 - u - n + k by push_cast [Nat.cast_sub hkn]; ring] at hr
  rw [hr]
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add]
  have h2 : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hm2 : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-(((k + m).choose k : ℂ) * poch u m * poch v k)) * hm2 +
    (-(((k + m).choose k : ℂ) * poch u m * poch v k * ((-1 : ℂ) ^ m) ^ 2)) * h2

end DLMF.Hypergeometric
