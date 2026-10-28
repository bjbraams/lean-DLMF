/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.BasicProperties.Continuity

/-!
# Integer Tricomi parameters and endpoint limits

Finite and logarithmic formulas at integer parameters and estimates near the origin.

Source references and common attribution are retained in
`DLMF.Confluent.BasicProperties`.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- The connection quotient at a natural second parameter is a numerator derivative. -/
theorem kummerU_nat_eq_deriv (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    kummerU a n z = (-1 : ℂ) ^ n * deriv (fun c => tricomiD a c z) n := by
  have h := kummerU_eq_dslope a hz (n : ℤ) (b := (n : ℂ)) (by simp)
  simp only [Int.cast_natCast, dslope_same] at h
  have hs : HasDerivAt (fun c : ℂ => sin (π * c)) (cos (π * n) * π) n := by
    simpa using ((hasDerivAt_id (n : ℂ)).const_mul (π : ℂ)).csin
  have hcos : cos (π * (n : ℂ)) = (-1 : ℂ) ^ n := by
    rw [mul_comm, show (n : ℂ) * π = ((n * π : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cos, Real.cos_nat_mul_pi]
    push_cast; rfl
  rw [hs.deriv, hcos] at h
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hσ : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm n 2, pow_mul]; simp
  rw [h]
  field_simp
  linear_combination -(deriv (fun c => tricomiD a c z) n) * hσ

/-- Reindexing the finite singular part in descending powers of the argument. -/
theorem tricomi_finite_sum_eq (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (-1 : ℂ) ^ (n + 1) * z ^ (-(n : ℂ)) * ∑ j ∈ Finset.range n,
      poch (a - n) j * z ^ j / j.factorial *
        ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) =
    ∑ k ∈ Finset.Icc 1 n, ((k - 1).factorial : ℂ) * poch (1 - a + k) (n - k) /
      ((n - k).factorial : ℂ) * z ^ (-(k : ℂ)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    omega
  · intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact ⟨n - k, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    have hjn : j ≤ n := (Finset.mem_range.mp hj).le
    have hpow : z ^ (-(n : ℂ)) * z ^ j = z ^ (-((n - j : ℕ) : ℂ)) := by
      rw [← cpow_natCast z j, ← cpow_add _ _ hz]
      congr 1
      rw [Nat.cast_sub hjn]; ring
    have hp : poch (a - n) j = (-1 : ℂ) ^ j * poch (1 - a + ((n - j : ℕ) : ℂ)) j := by
      rw [show a - (n : ℂ) = 1 - (1 - a + ((n - j : ℕ) : ℂ)) - j by
        rw [Nat.cast_sub hjn]; ring, DLMF.Hypergeometric.poch_reflect]
    have hsign : (-1 : ℂ) ^ (n + 1) * (-1 : ℂ) ^ j * (-1 : ℂ) ^ (n - 1 - j) = 1 := by
      rw [← pow_add, ← pow_add, show n + 1 + j + (n - 1 - j) = 2 * n by
        have := Finset.mem_range.mp hj; omega, pow_mul]
      simp
    rw [show n - (n - j) = j by omega, show n - 1 - j = n - j - 1 by omega, hp]
    calc
      _ = ((n - j - 1).factorial : ℂ) * poch (1 - a + ((n - j : ℕ) : ℂ)) j /
          (j.factorial : ℂ) * (z ^ (-(n : ℂ)) * z ^ j) *
            ((-1 : ℂ) ^ (n + 1) * (-1 : ℂ) ^ j * (-1 : ℂ) ^ (n - 1 - j)) := by
              rw [show n - 1 - j = n - j - 1 by omega]; ring
      _ = _ := by rw [hpow, hsign, mul_one]

/-- At a positive integer second parameter, U is a logarithm times an analytic function,
an analytic remainder, and a finite singular part. -/
theorem kummerU_nat_log (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    kummerU a ((n : ℂ) + 1) z =
      (-1 : ℂ) ^ (n + 1) * (Gamma (a - n))⁻¹ *
        (log z * regularizedHGFun {a} {(n : ℂ) + 1} z + tricomiLogSeries a n z) +
      (-1 : ℂ) ^ (n + 1) * z ^ (-(n : ℂ)) * (Gamma a)⁻¹ *
        ∑ j ∈ Finset.range n, poch (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) := by
  have h := kummerU_nat_eq_deriv a (n + 1) hz
  push_cast at h
  rw [show (fun c => tricomiD a c z) = (fun c =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹) from rfl,
    deriv_tricomi_numerator_nat a n hz ha, tricomi_log_series_split a n hz ha] at h
  rw [h]
  ring

open DLMF.Gamma in
/-- `kummerU_nat_log` with `ψ(a+k)/Γ(a-n)` written through `(1/Γ)'`.
Stronger than `kummerU_nat_log`: valid for all `a`. -/
theorem kummerU_nat_log_recipGamma (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    kummerU a ((n : ℂ) + 1) z =
      (-1 : ℂ) ^ (n + 1) *
        ((Gamma (a - n))⁻¹ * log z * regularizedHGFun {a} {(n : ℂ) + 1} z +
          tricomiLogSeriesRecipGamma a n z) +
      (-1 : ℂ) ^ (n + 1) * z ^ (-(n : ℂ)) * (Gamma a)⁻¹ *
        ∑ j ∈ Finset.range n, poch (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) := by
  have h := kummerU_nat_eq_deriv a (n + 1) hz
  push_cast at h
  rw [show (fun c => tricomiD a c z) = (fun c =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹) from rfl,
    deriv_tricomi_numerator_nat_recipGamma a n hz, tricomi_log_series_split_recipGamma a n hz] at h
  rw [h]
  ring

/-- A logarithm dominates constants in a punctured complex neighborhood of zero. -/
theorem isBigO_one_log_zero :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun _ : ℂ => (1 : ℂ)) log := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-1)))] with z hz hzn
  rw [Metric.mem_ball, dist_zero_right] at hzn
  have hlog : Real.log ‖z‖ < -1 := by
    calc Real.log ‖z‖ < Real.log (Real.exp (-1)) :=
      Real.log_lt_log (norm_pos_iff.mpr hz) hzn
      _ = -1 := Real.log_exp _
  have hle := (le_abs_self (log z).re).trans (abs_re_le_norm (log z))
  have hle' := (neg_le_abs (log z).re).trans (abs_re_le_norm (log z))
  rw [log_re] at hle'
  simp only [norm_one, one_mul]
  linarith

/-- Formula under the stated hypotheses: `kummerU a (n + 1) z = (-1 : ℂ) ^ (n + 1) / ((n.factorial
: ℂ) * Gamma (a - n)) * ∑' k : ℕ, poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k * (log
z + digamma (a + k) - digamma (1 + k) - digamma (n + k + 1)) + 1 / Gamma a * ∑ k ∈ Finset.Icc
1 n, ((k - 1).factorial : ℂ) * poch (1 - a + k) (n - k) / ((n - k).factorial : ℂ) * z ^ (-(k :
ℂ))`. -/
@[dlmf 13.2.E9]
theorem kummerU_nat_denom (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℕ, a - n ≠ -k) :
    kummerU a (n + 1) z =
      (-1 : ℂ) ^ (n + 1) / ((n.factorial : ℂ) * Gamma (a - n)) *
        ∑' k : ℕ, poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k *
          (log z + digamma (a + k) - digamma (1 + k) - digamma (n + k + 1)) +
        1 / Gamma a * ∑ k ∈ Finset.Icc 1 n,
          ((k - 1).factorial : ℂ) * poch (1 - a + k) (n - k) /
            ((n - k).factorial : ℂ) * z ^ (-(k : ℂ)) := by
  have hz0 := slitPlane_ne_zero hz
  have h := deriv_tricomi_numerator_nat a n hz0 ha
  change deriv (fun c => tricomiD a c z) ((n : ℂ) + 1) = _ at h
  have hU := kummerU_nat_eq_deriv a (n + 1) hz0
  push_cast at hU
  rw [h] at hU
  have hΓ : ∀ k : ℕ, Gamma ((n : ℂ) + 1 + k) =
      (n.factorial : ℂ) * poch ((n : ℂ) + 1) k := by
    intro k
    have hn : ∀ j : ℕ, (n : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hG := Gamma_add_nat_div_Gamma_eq (n := k) ((n : ℂ) + 1) hn
    rw [div_eq_iff (Gamma_ne_zero hn), Gamma_nat_eq_factorial] at hG
    rw [hG]; ring
  have htail : (∑' k : ℕ, (poch a k * z ^ k / k.factorial *
      (Gamma ((n : ℂ) + 1 + k))⁻¹) *
        (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))) =
      (n.factorial : ℂ)⁻¹ * ∑' k : ℕ,
        poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k *
          (log z + digamma (a + k) - digamma (1 + k) - digamma (n + k + 1)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [hΓ, show (k : ℂ) + 1 = 1 + k by ring,
      show (n : ℂ) + 1 + k = n + k + 1 by ring]
    simp only [mul_inv, div_eq_mul_inv]
    ring
  rw [htail, mul_add] at hU
  rw [hU]
  have hf := tricomi_finite_sum_eq a n hz0
  linear_combination (Gamma a)⁻¹ * hf

open DLMF.Gamma in
/-- DLMF 13.2.9 with each product `ψ(a+k)/Γ(a-n)` written as `-(a-n)_{n+k} (1/Γ)'(a+k)`.
Stronger than DLMF: valid for all `a` (the digamma form needs `a - n ∉ {0, -1, -2, …}`
because Mathlib's `ψ` is `0` at its poles). -/
@[dlmf 13.2.E9]
theorem kummerU_nat_denom_recipGamma (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerU a (n + 1) z =
      (-1 : ℂ) ^ (n + 1) / (n.factorial : ℂ) *
        ∑' k : ℕ, poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k *
          ((Gamma (a - n))⁻¹ * (log z - digamma (1 + k) - digamma (n + k + 1)) -
            poch (a - n) (n + k) * recipGammaDeriv 1 (a + k)) +
        1 / Gamma a * ∑ k ∈ Finset.Icc 1 n,
          ((k - 1).factorial : ℂ) * poch (1 - a + k) (n - k) /
            ((n - k).factorial : ℂ) * z ^ (-(k : ℂ)) := by
  have hz0 := slitPlane_ne_zero hz
  have h := deriv_tricomi_numerator_nat_recipGamma a n hz0
  change deriv (fun c => tricomiD a c z) ((n : ℂ) + 1) = _ at h
  have hU := kummerU_nat_eq_deriv a (n + 1) hz0
  push_cast at hU
  rw [h] at hU
  have hΓ : ∀ k : ℕ, Gamma ((n : ℂ) + 1 + k) =
      (n.factorial : ℂ) * poch ((n : ℂ) + 1) k := by
    intro k
    have hn : ∀ j : ℕ, (n : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hG := Gamma_add_nat_div_Gamma_eq (n := k) ((n : ℂ) + 1) hn
    rw [div_eq_iff (Gamma_ne_zero hn), Gamma_nat_eq_factorial] at hG
    rw [hG]; ring
  have htail : (∑' k : ℕ, (poch a k * z ^ k / k.factorial *
      (Gamma ((n : ℂ) + 1 + k))⁻¹) *
        ((Gamma (a - n))⁻¹ * (log z - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) -
          poch (a - n) (n + k) * recipGammaDeriv 1 (a + k))) =
      (n.factorial : ℂ)⁻¹ * ∑' k : ℕ,
        poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k *
          ((Gamma (a - n))⁻¹ * (log z - digamma (1 + k) - digamma (n + k + 1)) -
            poch (a - n) (n + k) * recipGammaDeriv 1 (a + k)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [hΓ, show (k : ℂ) + 1 = 1 + k by ring,
      show (n : ℂ) + 1 + k = n + k + 1 by ring]
    simp only [mul_inv, div_eq_mul_inv]
    ring
  rw [htail] at hU
  rw [hU]
  have hf := tricomi_finite_sum_eq a n hz0
  linear_combination (Gamma a)⁻¹ * hf

/-- Polynomial specialization at positive integer second parameter, using the continued U. -/
@[dlmf 13.2.E10]
theorem kummerU_neg_nat_nat_denom (m n : ℕ) (z : ℂ) :
    kummerU (-(m : ℂ)) (n + 1) z =
      (-1 : ℂ) ^ m * poch (n + 1 : ℂ) m * kummerM (-(m : ℂ)) (n + 1) z := by
  refine kummerU_neg_nat m _ z fun k hk => ?_
  have := congrArg re hk
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- Identity under the stated parameter and domain assumptions: `kummerU a (-(n : ℂ)) z = z ^ (n +
1 : ℂ) * kummerU (a + n + 1) (n + 2) z`. -/
@[dlmf 13.2.E11]
theorem kummerU_neg_nat_shift (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerU a (-(n : ℂ)) z = z ^ (n + 1 : ℂ) * kummerU (a + n + 1) (n + 2) z := by
  rw [kummerU_kummer_transform_all a _ (slitPlane_ne_zero hz)]
  congr 2 <;> ring

/-- Exponential form of the sine factor occurring in monodromy. -/
theorem one_sub_exp_neg_two_mul_I (t : ℂ) :
    1 - exp (-2 * t * I) = 2 * I * exp (-t * I) * sin t := by
  have he : exp (-t * I) * exp (t * I) = 1 := by rw [← exp_add]; ring_nf; simp
  have h2 : exp (-2 * t * I) = exp (-t * I) * exp (-t * I) := by
    rw [← exp_add]; congr 1; ring
  rw [h2, sin]
  linear_combination -he - (exp (-t * I) * (exp (-t * I) - exp (t * I))) * I_sq

/-- Monodromy on the logarithmic argument plane for noninteger second parameter. -/
@[dlmf 13.2.E12]
theorem kummerU_analytic_continuation (a b z : ℂ) (m : ℤ) {w : ℂ}
    (hw : w = log z + 2 * π * I * m) (hz : z ∈ slitPlane)
    (hb : ∀ n : ℤ, b ≠ n) :
    kummerUOnLog a b w =
      (2 * π * I * exp (-π * I * b * m) * sin (π * b * m)) /
          (Gamma (1 + a - b) * sin (π * b)) * regularizedHGFun {a} {b} z +
        exp (-2 * π * I * b * m) * kummerU a b z := by
  subst w
  have hz0 := slitPlane_ne_zero hz
  have hbk : ∀ k : ℕ, b ≠ -(k : ℂ) := not_neg_nat_of_mem_integerComplement
    (mem_integerComplement_of_forall hb)
  have he : exp (log z + 2 * π * I * m) = z := by
    rw [exp_add, show (2 : ℂ) * π * I * m = (m : ℂ) * (2 * π * I) by ring,
      exp_int_mul_two_pi_mul_I, mul_one, exp_log hz0]
  have hp : exp ((1 - b) * (log z + 2 * π * I * m)) =
      z ^ (1 - b) * exp (-2 * π * I * b * m) := by
    rw [show (1 - b) * (log z + 2 * π * I * m) =
      log z * (1 - b) + (m * (2 * π * I) + (-2 * π * I * b * m)) by ring,
      exp_add, exp_add, exp_int_mul_two_pi_mul_I, one_mul, cpow_def_of_ne_zero hz0]
  have hc : Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z =
      π / (Gamma (1 + a - b) * sin (π * b)) * regularizedHGFun {a} {b} z := by
    rw [kummerM_eq_mul_regularizedHGFun hbk,
      show 1 + a - b = a - b + 1 by ring]
    have hg := Gamma_mul_Gamma_one_sub b
    calc _ = (Gamma b * Gamma (1 - b)) / Gamma (a - b + 1) *
        regularizedHGFun {a} {b} z := by ring
      _ = _ := by rw [hg]; ring
  have ht := one_sub_exp_neg_two_mul_I (π * b * m)
  rw [show -2 * (π * b * (m : ℂ)) * I = -2 * π * I * b * m by ring,
    show -(π * b * (m : ℂ)) * I = -π * I * b * m by ring] at ht
  rw [kummerUOnLog, he, hp, kummerU_eq_connection a b z hb]
  unfold kummerUConnection
  calc _ = (1 - exp (-2 * π * I * b * m)) *
        (Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z) +
      exp (-2 * π * I * b * m) *
        (Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z +
          Gamma (b - 1) / Gamma a * z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z) := by ring
    _ = _ := by rw [hc, ht]; ring

/-- For `c = -n`, the totalized Kummer series `M(a,-n,z)` reduces to its terms of index `≤ n`. -/
theorem kummerM_eq_sum_neg_nat_denom (n : ℕ) (a z : ℂ) :
    kummerM a (-(n : ℂ)) z =
      ∑ k ∈ Finset.range (n + 1),
        poch a k / (poch (-(n : ℂ)) k * k.factorial) * z ^ k := by
  unfold kummerM
  refine tsum_eq_sum fun k hk => ?_
  have hkn : n < k := by
    rw [Finset.mem_range, not_lt] at hk
    exact Nat.lt_of_succ_le hk
  rw [poch_neg_nat_eq_zero hkn, zero_mul, div_zero, zero_mul]

/-- The totalized Kummer function `M(a,b,·)` is complex differentiable at `0`. -/
theorem differentiableAt_kummerM (a b : ℂ) :
    DifferentiableAt ℂ (kummerM a b) 0 := by
  by_cases hb : ∀ k : ℕ, b ≠ -k
  · exact ((hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem
      (by simp : (0 : ℂ) ∈ Metric.eball (0 : ℂ) ⊤)).differentiableAt
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, b = -n := by
      push Not at hb
      simpa using hb
    have hfun : kummerM a b =
        fun z => ∑ k ∈ Finset.range (n + 1),
          poch a k / (poch (-(n : ℂ)) k * k.factorial) * z ^ k := by
      funext z
      rw [hn, kummerM_eq_sum_neg_nat_denom]
    rw [hfun]
    refine (Differentiable.fun_sum fun k _ => ?_).differentiableAt
    exact ((differentiable_id (𝕜 := ℂ)).pow k).const_mul _

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO (𝓝 (0 : ℂ))
(fun z => kummerM a b z - 1) id`. -/
@[dlmf 13.2.E13]
theorem isBigO_kummerM_sub_one (a b : ℂ) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) (fun z => kummerM a b z - 1) id := by
  refine (differentiableAt_kummerM a b).isBigO_sub.congr ?_ ?_
  · intro x
    simp [kummerM_zero]
  · intro x
    simp [id]

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO (𝓝 (0 : ℂ))
(fun z => kummerU (-(n : ℂ)) b z - (-1 : ℂ) ^ n * poch b n) id`. -/
@[dlmf 13.2.E14]
theorem isBigO_kummerU_neg_nat (n : ℕ) (b : ℂ) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun z => kummerU (-(n : ℂ)) b z - (-1 : ℂ) ^ n * poch b n) id := by
  set P : ℂ → ℂ := fun z => (-1 : ℂ) ^ n * ∑ s ∈ Finset.range (n + 1),
    (n.choose s : ℂ) * poch (b + s) (n - s) * (-z) ^ s with hP
  have hU : ∀ z, kummerU (-(n : ℂ)) b z = P z := fun z => kummerU_neg_nat_sum n b z
  have hP0 : P 0 = (-1 : ℂ) ^ n * poch b n := by
    simp only [hP, neg_zero]
    rw [Finset.sum_range_succ']
    simp
  have hd : DifferentiableAt ℂ P 0 := by
    simp only [hP]
    fun_prop
  refine (hd.isBigO_sub).congr (fun z => ?_) (fun z => ?_)
  · rw [hU, hP0]
  · simp

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
(fun z => kummerU (-(n : ℂ) + b - 1) b z - (-1 : ℂ) ^ n * poch (2 - b) n * z ^ (1 - b)) (fun z
=> z ^ (2 - b))`. -/
@[dlmf 13.2.E15]
theorem isBigO_kummerU_neg_nat_shift (n : ℕ) (b : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU (-(n : ℂ) + b - 1) b z -
        (-1 : ℂ) ^ n * poch (2 - b) n * z ^ (1 - b))
      (fun z => z ^ (2 - b)) := by
  have h := (isBigO_kummerU_neg_nat n (2 - b)).mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hb : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z ^ (1 - b)) (fun z => z ^ (1 - b)) :=
    Asymptotics.isBigO_refl _ _
  refine (hb.mul h).congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [kummerU_kummer_transform_all (-(n : ℂ) + b - 1) b hz,
      show -(n : ℂ) + b - 1 - b + 1 = -(n : ℂ) by ring]
    ring
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [id]
    rw [show (2 : ℂ) - b = (1 - b) + 1 by ring, cpow_add _ _ hz, cpow_one]

/-- `‖z^w‖ ≤ ‖z‖^{Re w} e^{π |Im w|}` for `z ≠ 0`. -/
private lemma norm_cpow_le_exp_pi {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ‖z ^ w‖ ≤ ‖z‖ ^ w.re * Real.exp (Real.pi * |w.im|) := by
  rw [norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  calc -(arg z * w.im) ≤ |arg z * w.im| := neg_le_abs _
    _ = |arg z| * |w.im| := abs_mul _ _
    _ ≤ Real.pi * |w.im| := by gcongr; exact abs_arg_le_pi z

/-- `z^w = O(‖z‖^{Re w})` near `0`. -/
private lemma isBigO_cpow_norm_rpow (w : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z ^ w) (fun z => ‖z‖ ^ w.re) := by
  refine Asymptotics.IsBigO.of_bound (Real.exp (Real.pi * |w.im|)) ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [Real.norm_of_nonneg (by positivity), mul_comm]
  exact norm_cpow_le_exp_pi hz w

/-- `z = O(‖z‖^r)` near `0` for `r ≤ 1`. -/
private lemma isBigO_id_norm_rpow {r : ℝ} (hr : r ≤ 1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z) (fun z => ‖z‖ ^ r) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [one_mul, Real.norm_of_nonneg (by positivity)]
  exact Real.self_le_rpow_of_le_one (norm_nonneg z) hz hr

/-- `‖z‖^r = O(z^r)` near `0` for real `r`. -/
private lemma isBigO_norm_rpow_cpow (r : ℝ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => ‖z‖ ^ r) (fun z => z ^ (r : ℂ)) :=
  Asymptotics.isBigO_of_le _ fun z => by
    rw [norm_cpow_real, Real.norm_of_nonneg (by positivity)]

/-- A noninteger `b` from a strip of width one containing at most the integer `n`. -/
private lemma not_int_of_re_mem {b : ℂ} {n : ℤ} (h0 : (n : ℝ) ≤ b.re) (h1 : b.re < n + 1)
    (hb : b ≠ n) : ∀ k : ℤ, b ≠ k := by
  intro k hk
  have hre : b.re = k := by rw [hk]; simp
  have hkn : k = n := by
    have h0' : (n : ℝ) ≤ k := hre ▸ h0
    have h1' : (k : ℝ) < n + 1 := hre ▸ h1
    have : n ≤ k := by exact_mod_cast h0'
    have : k < n + 1 := by exact_mod_cast h1'
    omega
  exact hb (hk.trans (by rw [hkn]))

/-- Constants are `O(‖z‖^r)` near `0` for `r ≤ 0`. -/
private lemma isBigO_one_norm_rpow {r : ℝ} (hr : r ≤ 0) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun _ : ℂ => (1 : ℝ)) (fun z => ‖z‖ ^ r) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with z hz0 hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [one_mul, norm_one, Real.norm_of_nonneg (by positivity)]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (norm_pos_iff.mpr hz0) hz hr

/-- `log z = O(‖z‖^r)` near `0` for `r ≤ -1`. -/
private lemma isBigO_log_norm_rpow {r : ℝ} (hr : r ≤ -1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) log (fun z => ‖z‖ ^ r) := by
  refine Asymptotics.IsBigO.of_bound (1 + π) ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with z hz0 hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  have hx : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [Real.norm_of_nonneg (by positivity)]
  have hinv : ‖z‖⁻¹ ≤ ‖z‖ ^ r := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hx hz hr
  have h1 : 1 ≤ ‖z‖⁻¹ := one_le_inv_iff₀.mpr ⟨hx, hz⟩
  have hl : |Real.log ‖z‖| ≤ ‖z‖⁻¹ := by
    rw [abs_of_nonpos (Real.log_nonpos hx.le hz), ← Real.log_inv]
    linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr hx)]
  have hn : ‖log z‖ ≤ |Real.log ‖z‖| + π := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    rw [log_re, log_im]
    gcongr
    exact abs_arg_le_pi z
  calc ‖log z‖ ≤ ‖z‖⁻¹ + π * ‖z‖⁻¹ := by nlinarith [Real.pi_pos]
    _ = (1 + π) * ‖z‖⁻¹ := by ring
    _ ≤ (1 + π) * ‖z‖ ^ r := by gcongr

/-- `z^{-m}(P z - P 0) = O(‖z‖^{1-m})` near `0` for `P` differentiable at `0`. -/
private lemma isBigO_cpow_neg_nat_mul_sub (m : ℕ) {P : ℂ → ℂ}
    (hP : DifferentiableAt ℂ P 0) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => z ^ (-(m : ℂ)) * (P z - P 0))
      (fun z => ‖z‖ ^ (1 - (m : ℝ))) := by
  have h := (isBigO_cpow_norm_rpow (-(m : ℂ))).mul
    ((hP.isBigO_sub.mono (nhdsWithin_le_nhds (s := {0}ᶜ))).norm_right)
  refine h.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he : ‖z‖ ^ (-(m : ℂ)).re * ‖z - 0‖ = ‖z‖ ^ (1 - (m : ℝ)) := by
    rw [sub_zero, show 1 - (m : ℝ) = (-(m : ℂ)).re + 1 by simp; ring, Real.rpow_add hz0,
      Real.rpow_one]
  rw [he, one_mul]

/-- `(-1)^k (1-m)_k = Γ(m)/Γ(m-k)`. -/
private lemma neg_one_pow_mul_poch_one_sub_nat (m k : ℕ) (hm : 1 ≤ m) :
    (-1 : ℂ) ^ k * poch (1 - m) k = Gamma m / Gamma ((m : ℂ) - k) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [show (1 : ℂ) - ((n + 1 : ℕ) : ℂ) = -(n : ℂ) by push_cast; ring, poch_neg_coe_nat,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  rcases lt_or_ge n k with hk | hk
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk,
      show ((n + 1 : ℕ) : ℂ) - k = -((k - (n + 1) : ℕ) : ℂ) by
        rw [Nat.cast_sub (by omega)]; push_cast; ring, Gamma_neg_nat_eq_zero]
    simp
  · rw [show ((n + 1 : ℕ) : ℂ) - k = ((n - k : ℕ) : ℂ) + 1 by
        rw [Nat.cast_sub hk]; push_cast; ring, Gamma_nat_eq_factorial,
      show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial,
      eq_div_iff (by exact_mod_cast (Nat.factorial_ne_zero _)), mul_comm]
    exact_mod_cast (Nat.factorial_mul_descFactorial hk)

/-- Behaviour of `U` at zero for `Re b ≥ 2`, `b ≠ 2`; at `b = 2` a `log z` term appears
(see `isBigO_kummerU_at_zero_b_two`). -/
@[dlmf 13.2.E16]
theorem isBigO_kummerU_at_zero_re_ge_two (a b : ℂ) (hb : 2 ≤ b.re) (hb2 : b ≠ 2) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a b z - Gamma (b - 1) / Gamma a * z ^ (1 - b))
      (fun z => z ^ (2 - b.re : ℂ)) := by
  refine Asymptotics.IsBigO.trans ?_ (by simpa using isBigO_norm_rpow_cpow (2 - b.re))
  by_cases hbZ : ∀ k : ℤ, b ≠ k
  · have hM : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => kummerM a b z)
        (fun _ => (1 : ℝ)) :=
      ((differentiableAt_kummerM a b).continuousAt.tendsto.isBigO_one ℝ).mono
        nhdsWithin_le_nhds
    have h1 := hM.trans (isBigO_one_norm_rpow (r := 2 - b.re) (by linarith))
    have h2 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
        (fun z => z ^ (1 - b) * (kummerM (a - b + 1) (2 - b) z - 1))
        (fun z => ‖z‖ ^ (2 - b.re)) := by
      refine ((isBigO_cpow_norm_rpow (1 - b)).mul
        ((isBigO_kummerM_sub_one (a - b + 1) (2 - b)).mono
          (nhdsWithin_le_nhds (s := {0}ᶜ))).norm_right).trans ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have he : ‖z‖ ^ (1 - b).re * ‖id z‖ = ‖z‖ ^ (2 - b.re) := by
        rw [id, show 2 - b.re = (1 - b).re + 1 by simp; ring, Real.rpow_add hz0, Real.rpow_one]
      rw [he, one_mul]
    have hsum := (h1.const_mul_left (Gamma (1 - b) / Gamma (a - b + 1))).add
      (h2.const_mul_left (Gamma (b - 1) / Gamma a))
    refine hsum.congr (fun z => ?_) (fun z => rfl)
    rw [kummerU_eq_connection a b z hbZ, kummerUConnection]
    ring
  push Not at hbZ
  obtain ⟨n, rfl⟩ := hbZ
  have hn2 : (2 : ℝ) ≤ n := by simpa using hb
  have hn3 : n ≠ 2 := fun h => hb2 (by rw [h]; norm_num)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by
    have : (2 : ℤ) ≤ n := by exact_mod_cast hn2
    omega⟩
  have hm : 2 ≤ m := by
    have : (2 : ℤ) ≤ (m : ℤ) + 1 := by exact_mod_cast hn2
    omega
  have hb' : (((m : ℤ) + 1 : ℤ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hre : 2 - ((m : ℂ) + 1).re = 1 - (m : ℝ) := by simp; ring
  simp only [hb']
  simp only [hre]
  have hpow : ∀ z : ℂ, z ^ (1 - ((m : ℂ) + 1)) = z ^ (-(m : ℂ)) := fun z => by
    congr 1; ring
  simp only [hpow, show (m : ℂ) + 1 - 1 = m by ring]
  by_cases ha : ∀ k : ℕ, a - m ≠ -(k : ℂ)
  · set P : ℂ → ℂ := fun z => ∑ j ∈ Finset.range m, poch (a - m) j * z ^ j / j.factorial *
        ((-1 : ℂ) ^ (m - 1 - j) * ((m - 1 - j).factorial : ℂ)) with hPdef
    have hP : DifferentiableAt ℂ P 0 := by rw [hPdef]; fun_prop
    have hP0 : (-1 : ℂ) ^ (m + 1) * P 0 = Gamma m := by
      obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
      rw [hPdef]
      simp only [Finset.sum_range_succ', ne_eq, Nat.add_one_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, zero_div, zero_mul, Finset.sum_const_zero, zero_add,
        poch_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      rw [show ((p + 1 : ℕ) : ℂ) = (p : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial,
        show p + 1 - 1 - 0 = p by omega, ← mul_assoc, ← pow_add,
        show p + 1 + 1 + p = 2 * (p + 1) by ring, pow_mul]
      simp
    have hM := ((differentiableAt_regularizedConfluent a ((m : ℂ) + 1) 0).continuousAt.tendsto.isBigO_one ℝ).mono
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hT := ((analyticAt_tricomiLogSeries a m ha).continuousAt.tendsto.isBigO_one ℝ).mono
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hr1 : 1 - (m : ℝ) ≤ -1 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hLM := ((isBigO_log_norm_rpow hr1).mul hM)
    simp only [mul_one] at hLM
    have h := ((hLM.add (hT.trans (isBigO_one_norm_rpow (by linarith)))).const_mul_left
        ((-1 : ℂ) ^ (m + 1) * (Gamma (a - m))⁻¹)).add
      ((isBigO_cpow_neg_nat_mul_sub m hP).const_mul_left ((-1 : ℂ) ^ (m + 1) * (Gamma a)⁻¹))
    refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [kummerU_nat_log a m hz ha, ← hP0]
    simp only [hPdef]
    ring
  · push Not at ha
    obtain ⟨k, hk⟩ := ha
    have hak : a = (m : ℂ) - k := by linear_combination hk
    have hQ : Differentiable ℂ (kummerU (-(k : ℂ)) (1 - m)) := by
      rw [show kummerU (-(k : ℂ)) (1 - m) = fun z => (-1 : ℂ) ^ k *
          ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * poch (1 - m + j) (k - j) * (-z) ^ j from
        funext fun z => kummerU_neg_nat_sum k _ z]
      fun_prop
    have hQ0 : kummerU (-(k : ℂ)) (1 - m) 0 = Gamma m / Gamma a := by
      rw [kummerU_neg_nat_sum, hak, ← neg_one_pow_mul_poch_one_sub_nat m k (by omega)]
      simp [Finset.sum_range_succ']
    refine (isBigO_cpow_neg_nat_mul_sub m (hQ 0)).congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [kummerU_kummer_transform_all a _ hz, hpow, hQ0,
      show a - ((m : ℂ) + 1) + 1 = -(k : ℂ) by rw [hak]; ring,
      show (2 : ℂ) - ((m : ℂ) + 1) = 1 - m by ring]
    ring

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
(fun z => kummerU a 2 z - 1 / Gamma a * z⁻¹) (fun z => log z)`. -/
@[dlmf 13.2.E17]
theorem isBigO_kummerU_at_zero_b_two (a : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a 2 z - 1 / Gamma a * z⁻¹)
      (fun z => log z) := by
  by_cases ha : ∀ k : ℕ, a - (1 : ℕ) ≠ -(k : ℂ)
  · have hM := ((differentiableAt_regularizedConfluent a ((1 : ℂ) + 1) 0).continuousAt.tendsto.isBigO_one ℂ).mono
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hT := ((analyticAt_tricomiLogSeries a 1 ha).continuousAt.tendsto.isBigO_one ℂ).mono
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hLM := (Asymptotics.isBigO_refl log (𝓝[≠] (0 : ℂ))).mul hM
    simp only [mul_one] at hLM
    have h := (hLM.add (hT.trans isBigO_one_log_zero)).const_mul_left (Gamma (a - 1))⁻¹
    refine h.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      rw [show (2 : ℂ) = (1 : ℕ) + 1 by norm_num, kummerU_nat_log a 1 hz ha]
      simp only [Nat.cast_one, one_add_one_eq_two, pow_two,
        Finset.sum_range_one, poch_zero, pow_zero, Nat.factorial_zero, Nat.sub_self,
        Nat.cast_one, div_one, mul_one, cpow_neg_one]
      ring
    · filter_upwards with z
      simp
  · push Not at ha
    obtain ⟨k, hk⟩ := ha
    cases k with
    | zero =>
      have ha1 : a = 1 := by push_cast at hk; linear_combination hk
      subst a
      refine Asymptotics.isBigO_zero _ _ |>.congr' ?_ (Filter.EventuallyEq.refl _ _)
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [kummerU_kummer_transform_all 1 2 hz]
      norm_num [kummerU_zero, cpow_neg_one]
    | succ k =>
      have hak : a = -(k : ℂ) := by push_cast at hk; linear_combination hk
      subst a
      have hc : Continuous (kummerU (-(k : ℂ)) 2) := by
        have heq : kummerU (-(k : ℂ)) 2 = fun z => (-1 : ℂ) ^ k *
            ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * poch (2 + j) (k - j) * (-z) ^ j :=
          funext fun z => kummerU_neg_nat_sum k 2 z
        rw [heq]
        fun_prop
      simpa [Gamma_neg_nat_eq_zero] using
        ((hc.continuousAt.tendsto.isBigO_one ℂ).mono
          (nhdsWithin_le_nhds (s := {0}ᶜ))).trans isBigO_one_log_zero

/-- Behaviour of `U` at zero for `1 ≤ Re b < 2`, `b ≠ 1`; at `b = 1` a `log z` term
appears (see `isBigO_kummerU_at_zero_b_one`). -/
@[dlmf 13.2.E18]
theorem isBigO_kummerU_at_zero_re_one_to_two (a b : ℂ)
    (hb0 : 1 ≤ b.re) (hb1 : b.re < 2) (hb2 : b ≠ 1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a b z - Gamma (b - 1) / Gamma a * z ^ (1 - b) -
        Gamma (1 - b) / Gamma (a - b + 1))
      (fun z => z ^ (2 - b.re : ℂ)) := by
  have hbZ : ∀ k : ℤ, b ≠ k :=
    not_int_of_re_mem (n := 1) (by simpa using hb0) (by norm_num; linarith) (by simpa using hb2)
  have h1 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => kummerM a b z - 1)
      (fun z => ‖z‖ ^ (2 - b.re)) :=
    ((isBigO_kummerM_sub_one a b).mono nhdsWithin_le_nhds).trans
      (isBigO_id_norm_rpow (by linarith))
  have h2 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => z ^ (1 - b) * (kummerM (a - b + 1) (2 - b) z - 1))
      (fun z => ‖z‖ ^ (2 - b.re)) := by
    refine ((isBigO_cpow_norm_rpow (1 - b)).mul
      ((isBigO_kummerM_sub_one (a - b + 1) (2 - b)).mono
        (nhdsWithin_le_nhds (s := {0}ᶜ))).norm_right).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have he : ‖z‖ ^ (1 - b).re * ‖id z‖ = ‖z‖ ^ (2 - b.re) := by
      rw [id, show 2 - b.re = (1 - b).re + 1 by simp; ring, Real.rpow_add hz0, Real.rpow_one]
    rw [he, one_mul]
  have hsum := ((h1.const_mul_left (Gamma (1 - b) / Gamma (a - b + 1))).add
    (h2.const_mul_left (Gamma (b - 1) / Gamma a))).trans
      (by simpa using isBigO_norm_rpow_cpow (2 - b.re))
  refine hsum.congr (fun z => ?_) (fun z => rfl)
  rw [kummerU_eq_connection a b z hbZ, kummerUConnection]
  ring

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
(fun z => kummerU a 1 z + 1 / Gamma a * (log z + digamma a + 2 * (Real.eulerMascheroniConstant
: ℂ))) (fun z => z * log z)`. -/
@[dlmf 13.2.E19]
/- At nonpositive integer a the Gamma/digamma product must be continued jointly.
The old statement at a = 0 asserted 1 = O(z log z). -/
theorem isBigO_kummerU_at_zero_b_one (a : ℂ) (ha : ∀ k : ℕ, a ≠ -k) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a 1 z +
        1 / Gamma a * (log z + digamma a + 2 * (Real.eulerMascheroniConstant : ℂ)))
      (fun z => z * log z) := by
  have ha0 : ∀ k : ℕ, a - (0 : ℕ) ≠ -(k : ℂ) := by simpa using ha
  have hM0 : regularizedHGFun {a} {(0 : ℂ) + 1} 0 = 1 := by
    simp [regularizedHGFunCoeff_singleton, poch_zero]
  have hT0 : tricomiLogSeries a 0 0 = digamma a + 2 * (Real.eulerMascheroniConstant : ℂ) := by
    rw [tricomiLogSeries_zero]; simp [digamma_one]; ring
  have hM := ((differentiableAt_regularizedConfluent a ((0 : ℂ) + 1) 0).isBigO_sub).mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hT := ((analyticAt_tricomiLogSeries a 0 ha0).differentiableAt.isBigO_sub).mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [sub_zero] at hM hT
  have hid : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z) (fun z => z * log z) := by
    simpa using (Asymptotics.isBigO_refl (fun z : ℂ => z) (𝓝[≠] (0 : ℂ))).mul
      isBigO_one_log_zero
  have h := ((hM.mul (Asymptotics.isBigO_refl log (𝓝[≠] (0 : ℂ)))).add
    (hT.trans hid)).const_mul_left (-(Gamma a)⁻¹)
  refine h.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hUz := kummerU_nat_log a 0 hz ha0
    norm_num only [Nat.cast_zero, zero_add] at hUz
    rw [hUz]
    simp only [hM0, hT0]
    simp only [sub_zero, mul_zero, add_zero]
    ring
  · filter_upwards with z
    simp

open DLMF.Gamma in
/-- DLMF 13.2.19 with `ψ(a)/Γ(a)` written as `-(1/Γ)'(a)`:
`U(a,1,z) + (log z + 2γ)/Γ(a) - (1/Γ)'(a) = O(z log z)`.
Stronger than DLMF: valid for all `a`, including `a ∈ {0, -1, -2, …}`. -/
@[dlmf 13.2.E19]
theorem isBigO_kummerU_at_zero_b_one_recipGamma (a : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a 1 z +
        ((Gamma a)⁻¹ * (log z + 2 * (Real.eulerMascheroniConstant : ℂ)) -
          recipGammaDeriv 1 a))
      (fun z => z * log z) := by
  have hM0 : regularizedHGFun {a} {(0 : ℂ) + 1} 0 = 1 := by
    simp [regularizedHGFunCoeff_singleton, poch_zero]
  have hT0 : tricomiLogSeriesRecipGamma a 0 0 =
      2 * (Real.eulerMascheroniConstant : ℂ) * (Gamma a)⁻¹ - recipGammaDeriv 1 a := by
    rw [tricomiLogSeriesRecipGamma_zero]; simp [digamma_one, poch_zero]; ring
  have hM := ((differentiableAt_regularizedConfluent a ((0 : ℂ) + 1) 0).isBigO_sub).mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hT := ((analyticAt_tricomiLogSeriesRecipGamma a 0).differentiableAt.isBigO_sub).mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [sub_zero] at hM hT
  have hid : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z) (fun z => z * log z) := by
    simpa using (Asymptotics.isBigO_refl (fun z : ℂ => z) (𝓝[≠] (0 : ℂ))).mul
      isBigO_one_log_zero
  have h := ((((hM.mul (Asymptotics.isBigO_refl log (𝓝[≠] (0 : ℂ)))).const_mul_left
    (Gamma a)⁻¹).add (hT.trans hid))).const_mul_left (-1 : ℂ)
  refine h.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hUz := kummerU_nat_log_recipGamma a 0 hz
    norm_num only [Nat.cast_zero, zero_add, sub_zero] at hUz
    rw [hUz]
    simp only [hM0, hT0]
    simp only [mul_zero, add_zero]
    ring_nf
  · filter_upwards with z
    simp

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
(fun z => kummerU a b z - Gamma (1 - b) / Gamma (a - b + 1)) (fun z => z ^ (1 - b.re : ℂ))`. -/
@[dlmf 13.2.E20]
theorem isBigO_kummerU_at_zero_re_zero_to_one (a b : ℂ)
    (hb0 : 0 < b.re) (hb1 : b.re < 1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a b z - Gamma (1 - b) / Gamma (a - b + 1))
      (fun z => z ^ (1 - b.re : ℂ)) := by
  have hbZ : ∀ k : ℤ, b ≠ k := by
    refine not_int_of_re_mem (n := 0) (by simpa using hb0.le) (by simpa using hb1) ?_
    intro h
    rw [h] at hb0
    simp at hb0
  have h1 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => kummerM a b z - 1)
      (fun z => ‖z‖ ^ (1 - b.re)) :=
    ((isBigO_kummerM_sub_one a b).mono nhdsWithin_le_nhds).trans
      (isBigO_id_norm_rpow (by linarith))
  have hM : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => kummerM (a - b + 1) (2 - b) z)
      (fun _ => (1 : ℝ)) :=
    ((differentiableAt_kummerM (a - b + 1) (2 - b)).continuousAt.tendsto.isBigO_one ℝ).mono
      nhdsWithin_le_nhds
  have h2 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z)
      (fun z => ‖z‖ ^ (1 - b.re)) := by
    refine ((isBigO_cpow_norm_rpow (1 - b)).mul hM).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with z
    simp
  have hsum := ((h1.const_mul_left (Gamma (1 - b) / Gamma (a - b + 1))).add
    (h2.const_mul_left (Gamma (b - 1) / Gamma a))).trans
      (by simpa using isBigO_norm_rpow_cpow (1 - b.re))
  refine hsum.congr (fun z => ?_) (fun z => rfl)
  rw [kummerU_eq_connection a b z hbZ, kummerUConnection]
  ring

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
(fun z => kummerU a 0 z - 1 / Gamma (a + 1)) (fun z => z * log z)`. -/
@[dlmf 13.2.E21]
theorem isBigO_kummerU_at_zero_b_zero (a : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a 0 z - 1 / Gamma (a + 1))
      (fun z => z * log z) := by
  have h := (Asymptotics.isBigO_refl (fun z : ℂ => z) (𝓝[≠] (0 : ℂ))).mul
    (isBigO_kummerU_at_zero_b_two (a + 1))
  refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [kummerU_kummer_transform_all a 0 hz]
  simp only [sub_zero, cpow_one, show (2 : ℂ) - 0 = 2 by ring]
  have hz0 : z ≠ 0 := hz
  field_simp [hz0]

/-- At the origin, `U(a,b,0) = Γ(1-b)/Γ(a-b+1)` for `Re b < 1`, including integer `b`. -/
theorem kummerU_zero_arg (a b : ℂ) (hb : b.re < 1) :
    kummerU a b 0 = Gamma (1 - b) / Gamma (a - b + 1) := by
  have hconn : ∀ c : ℂ, c.re < 1 →
      kummerUConnection a c 0 = Gamma (1 - c) / Gamma (a - c + 1) := by
    intro c hc
    have h1 : (1 : ℂ) - c ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    simp [kummerUConnection, kummerM_zero, zero_cpow h1]
  by_cases hbZ : ∀ k : ℤ, b ≠ k
  · rw [kummerU_eq_connection a b 0 hbZ, hconn b hb]
  · have hne := integerComplement_nhdsWithin_neBot b
    simp only [kummerU, hbZ, ite_false]
    refine Tendsto.limUnder_eq ?_
    have hG : ContinuousAt (fun c : ℂ => Gamma (1 - c) * (Gamma (a - c + 1))⁻¹) b := by
      refine ContinuousAt.mul ?_ ?_
      · refine (differentiableAt_Gamma _ fun m h => ?_).continuousAt.comp
          (continuousAt_const.sub continuousAt_id)
        have := congrArg re h; simp at this
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      · exact (differentiable_one_div_Gamma.continuous.comp
          (by fun_prop : Continuous fun c : ℂ => a - c + 1)).continuousAt
    refine (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    have hopen : {c : ℂ | c.re < 1} ∈ 𝓝 b :=
      (isOpen_lt continuous_re continuous_const).mem_nhds hb
    filter_upwards [nhdsWithin_le_nhds hopen] with c hc
    rw [hconn c hc, div_eq_mul_inv]

/-- Behaviour of `U` at zero for `Re b ≤ 0`, `b ≠ 0`; at `b = 0` a `z log z` term
appears (see `isBigO_kummerU_at_zero_b_zero`). -/
@[dlmf 13.2.E22]
theorem isBigO_kummerU_at_zero_re_nonpos (a b : ℂ) (hb : b.re ≤ 0) (hb0 : b ≠ 0) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun z => kummerU a b z - Gamma (1 - b) / Gamma (a - b + 1)) id := by
  have hb2 : 2 - b ≠ 2 := fun h => hb0 (by linear_combination -h)
  have h := (isBigO_cpow_norm_rpow (1 - b)).mul
    ((isBigO_kummerU_at_zero_re_ge_two (a - b + 1) (2 - b) (by simp; linarith) hb2).trans
      (isBigO_cpow_norm_rpow _))
  have h' : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a b z - Gamma (1 - b) / Gamma (a - b + 1)) id := by
    refine (h.trans (Asymptotics.IsBigO.of_bound 1 ?_)).congr' ?_ (Filter.EventuallyEq.refl _ _)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have he : ‖z‖ ^ (1 - b).re * ‖z‖ ^ ((2 : ℂ) - ((2 - b).re : ℂ)).re = ‖id z‖ := by
        rw [← Real.rpow_add hz0, id]
        simp
      rw [Real.norm_of_nonneg (by positivity), he, one_mul]
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : z ≠ 0 := hz
      have hne : z ^ (1 - b) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
      rw [kummerU_kummer_transform_all a b hz0, show 2 - b - 1 = 1 - b by ring,
        show (1 : ℂ) - (2 - b) = -(1 - b) by ring, cpow_neg, mul_sub, mul_left_comm,
        mul_inv_cancel₀ hne, mul_one]
  obtain ⟨C, hC⟩ := h'.isBigOWith
  have hC' := hC.insert (x := (0 : ℂ)) (by
    rw [kummerU_zero_arg a b (by linarith), sub_self, norm_zero, id, norm_zero, mul_zero])
  rw [show insert (0 : ℂ) ({0}ᶜ) = Set.univ by ext; simp [em], nhdsWithin_univ] at hC'
  exact hC'.isBigO

end DLMF.Confluent
end
end
