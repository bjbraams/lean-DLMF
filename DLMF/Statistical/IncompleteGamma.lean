/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Statistical.Basic.IncompleteGamma
public import DLMF.Confluent.IncompleteGamma

/-!
# Regularized incomplete Gamma functions (Temme §11.2; DLMF §§8.2–8.8)

The normalized functions `P(a,z) = γ(a,z)/Γ(a)` and `Q(a,z) = Γ(a,z)/Γ(a)` (DLMF 8.2.4) are the
distribution function of the Gamma distribution and its complement. This file defines them for
complex `a` and `z` from the project's `lowerIncGamma` and `upperIncGamma`.

## Main results

* `normIncGammaP_add_normIncGammaQ`: `P(a,z) + Q(a,z) = 1` (DLMF 8.2.5).
* `lowerIncGamma_add_one`: `γ(a+1,z) = a γ(a,z) - z^a e^{-z}` (DLMF 8.8.1).
* `normIncGammaP_add_one`, `normIncGammaQ_add_one`: the recurrences DLMF 8.8.5–8.8.6.
* `normIncGammaQ_nat_succ`, `normIncGammaP_nat_succ`: `Q(n+1,z) = e^{-z} ∑_{k ≤ n} z^k/k!`
  (DLMF 8.4.10), the Poisson tail.
* `lowerIncGamma_eq_tsum`: `γ(a,z) = z^a e^{-z} ∑ zⁿ/(a (a+1)ₙ)` (DLMF 8.7.1).
* `normIncGammaP_ofReal`, `normIncGammaQ_ofReal`: `P` restricts to TauCeti's `regularizedGamma`.
* `hasDerivAt_lowerIncGamma_ofReal`: `∂ₓ γ(a,x) = x^{a-1} e^{-x}` (DLMF 8.8.13).
* `scIncGamma`: Tricomi's entire function `γ*(a,z) = e^{-z} 𝐌(1, a+1, z)`, with the series
  `e^{-z} ∑ zᵏ/Γ(a+k+1)` (DLMF 8.7.1), `γ* = z^{-a} γ(a,z)/Γ(a) = z^{-a} P(a,z)` (DLMF 8.2.6–8.2.7)
  and `γ*(-n,z) = zⁿ` (DLMF 8.4.12).
-/

@[expose] public section

open Complex Filter Set MeasureTheory DLMF.Confluent
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Statistical

/-- `P(a,z) + Q(a,z) = 1` (DLMF 8.2.5) for `z ≠ 0` and `a` not a nonpositive integer. -/
@[dlmf 8.2.E5]
theorem normIncGammaP_add_normIncGammaQ {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaP a z + normIncGammaQ a z = 1 := by
  rw [normIncGammaP, normIncGammaQ, ← add_div, lowerIncGamma_add_upperIncGamma ha hz,
    div_self (Gamma_ne_zero ha)]

/-- If `a` is not a nonpositive integer, then neither is `a + 1`. -/
theorem add_one_ne_neg_nat {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) : ∀ k : ℕ, a + 1 ≠ -k :=
  fun k hk => ha (k + 1) (by push_cast; linear_combination hk)

/-- The recurrence `γ(a+1,z) = a γ(a,z) - z^a e^{-z}` (DLMF 8.8.1). -/
@[dlmf 8.8.E1]
theorem lowerIncGamma_add_one {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma (a + 1) z = a * lowerIncGamma a z - z ^ a * exp (-z) := by
  have h1 := lowerIncGamma_add_upperIncGamma (add_one_ne_neg_nat ha) hz
  have h0 := lowerIncGamma_add_upperIncGamma ha hz
  have ha0 : a ≠ 0 := by simpa using ha 0
  rw [upperIncGamma_add_one a hz, Complex.Gamma_add_one a ha0] at h1
  linear_combination h1 - a * h0

/-- `Q(a+1,z) = Q(a,z) + z^a e^{-z}/Γ(a+1)` (DLMF 8.8.6). -/
@[dlmf 8.8.E6]
theorem normIncGammaQ_add_one {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaQ (a + 1) z = normIncGammaQ a z + z ^ a * exp (-z) / Gamma (a + 1) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have hG := Gamma_ne_zero ha
  rw [normIncGammaQ, normIncGammaQ, upperIncGamma_add_one a hz, Complex.Gamma_add_one a ha0]
  field_simp

/-- `P(a+1,z) = P(a,z) - z^a e^{-z}/Γ(a+1)` (DLMF 8.8.5). -/
@[dlmf 8.8.E5]
theorem normIncGammaP_add_one {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaP (a + 1) z = normIncGammaP a z - z ^ a * exp (-z) / Gamma (a + 1) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have hG := Gamma_ne_zero ha
  rw [normIncGammaP, normIncGammaP, lowerIncGamma_add_one ha hz, Complex.Gamma_add_one a ha0]
  field_simp

/-- For natural `n`, `n + 1` is not a nonpositive integer. -/
theorem natCast_add_one_ne_neg_nat (n : ℕ) : ∀ k : ℕ, ((n : ℂ) + 1) ≠ -k := fun k hk => by
  have := congrArg re hk
  simp at this
  linarith [(k.cast_nonneg : (0 : ℝ) ≤ k), (n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- The Poisson tail `Q(n+1,z) = e^{-z} ∑_{k ≤ n} z^k/k!` (DLMF 8.4.10). -/
@[dlmf 8.4.E10]
theorem normIncGammaQ_nat_succ (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaQ ((n : ℂ) + 1) z = exp (-z) * ∑ k ∈ Finset.range (n + 1), z ^ k / k ! := by
  induction n with
  | zero => simp [normIncGammaQ, upperIncGamma_one]
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℂ) + 1 = ((n : ℂ) + 1) + 1 by push_cast; ring,
      normIncGammaQ_add_one (natCast_add_one_ne_neg_nat n) hz, ih, Finset.sum_range_succ _ (n + 1),
      show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      Complex.Gamma_nat_eq_factorial]
    ring

/-- `P(n+1,z) = 1 - e^{-z} ∑_{k ≤ n} z^k/k!` (DLMF 8.4.11 with 8.2.5). -/
@[dlmf 8.4.E11]
theorem normIncGammaP_nat_succ (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaP ((n : ℂ) + 1) z = 1 - exp (-z) * ∑ k ∈ Finset.range (n + 1), z ^ k / k ! := by
  have h := normIncGammaP_add_normIncGammaQ (natCast_add_one_ne_neg_nat n) hz
  rw [normIncGammaQ_nat_succ n hz] at h
  linear_combination h

/-- The series `γ(a,z) = z^a e^{-z} ∑ zⁿ / (a (a+1)ₙ)` (DLMF 8.7.1, Temme (11.13)): Kummer's
transformation of `γ(a,z) = z^a/a · M(a, a+1, -z)`. -/
@[dlmf 8.7.E1]
theorem lowerIncGamma_eq_tsum {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (z : ℂ) :
    lowerIncGamma a z = z ^ a * exp (-z) * ∑' n : ℕ, z ^ n / (a * poch (a + 1) n) := by
  rw [lowerIncGamma, kummerM_kummer_transform (add_one_ne_neg_nat ha),
    show a + 1 - a = 1 by ring, neg_neg, kummerM]
  have hn (n : ℕ) : poch 1 n / (poch (a + 1) n * n !) * z ^ n =
      a * (z ^ n / (a * poch (a + 1) n)) := by
    have ha0 : a ≠ 0 := by simpa using ha 0
    have hp : poch (a + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat (add_one_ne_neg_nat ha) n
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    rw [poch_nat_one]
    field_simp
  simp_rw [hn, tsum_mul_left]
  have ha0 : a ≠ 0 := by simpa using ha 0
  field_simp

/-- For real `s > 0` and `x > 0`, `P(s,x)` is TauCeti's regularized Gamma function. -/
theorem normIncGammaP_ofReal {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    normIncGammaP s x = (TauCeti.regularizedGamma s x : ℂ) := by
  rw [normIncGammaP, lowerIncGamma_ofReal hs hx, TauCeti.regularizedGamma_eq_div,
    Complex.ofReal_div, Complex.Gamma_ofReal]

/-- For real `s > 0` and `x > 0`, `Q(s,x) = 1 - P(s,x)` with TauCeti's `P`. -/
theorem normIncGammaQ_ofReal {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    normIncGammaQ s x = 1 - (TauCeti.regularizedGamma s x : ℂ) := by
  have hs' : ∀ k : ℕ, (s : ℂ) ≠ -k := fun k hk => by
    have := congrArg re hk
    simp at this
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  rw [← normIncGammaP_ofReal hs hx, ← normIncGammaP_add_normIncGammaQ hs'
    (Complex.ofReal_ne_zero.mpr hx.ne')]
  ring

/-- `∂ₓ γ(a,x) = x^{a-1} e^{-x}` for `re a > 0` and `x > 0` (DLMF 8.8.13). -/
@[dlmf 8.8.E13]
theorem hasDerivAt_lowerIncGamma_ofReal {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => lowerIncGamma a y) ((x : ℂ) ^ (a - 1) * Real.exp (-x)) x := by
  have hev : (fun y : ℝ => lowerIncGamma a y) =ᶠ[𝓝 x]
      fun y => ∫ t in (0 : ℝ)..y, (t : ℂ) ^ (a - 1) * Real.exp (-t) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact lowerIncGamma_eq_integral ha hy
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (a - 1) * Real.exp (-t))
      volume 0 x := by
    have h := (Complex.GammaIntegral_convergent ha).mono_set
      (Ioc_subset_Ioi_self : Ioc (0 : ℝ) x ⊆ Ioi 0)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    exact h.congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioc
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * Real.exp (-t)) (Ioi 0) := by
    intro y hy
    have hs : (y : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hy
    exact ((ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const hs).mul
      (by fun_prop)).continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right hint
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx)
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hx))

/-- The series `γ*(a,z) = e^{-z} ∑ₖ zᵏ / Γ(a+k+1)` (DLMF 8.7.1), valid for all complex `a, z`. -/
@[dlmf 8.7.E1]
theorem scIncGamma_eq_tsum (a z : ℂ) :
    scIncGamma a z = exp (-z) * ∑' k : ℕ, z ^ k / Gamma (a + k + 1) := by
  rw [scIncGamma, regularizedHGFun_eq_tsum]
  congr 1
  refine tsum_congr fun k => ?_
  rw [regularizedHGFunCoeff_singleton, poch_nat_one, show a + 1 + k = a + k + 1 by ring]
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

/-- `γ*(a,z)` is entire in `z`. -/
theorem analyticAt_scIncGamma (a z : ℂ) : AnalyticAt ℂ (scIncGamma a) z :=
  ((analyticAt_id.neg).cexp).mul (analyticAt_regularizedHGFun_of_card_le (by simp) z)

/-- `γ*(a,z) = z^{-a} γ(a,z)/Γ(a)` (DLMF 8.2.6) away from the poles of `Γ(a)` and `z = 0`. -/
@[dlmf 8.2.E6]
theorem scIncGamma_eq {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    scIncGamma a z = z ^ (-a) * lowerIncGamma a z / Gamma a := by
  have ha1 : ∀ k : ℕ, a + 1 ≠ -k := fun k hk => ha (k + 1) (by push_cast; linear_combination hk)
  have hΓ : Gamma a ≠ 0 := Gamma_ne_zero ha
  have hΓ1 : Gamma (a + 1) ≠ 0 := Gamma_ne_zero ha1
  have hK := kummerM_kummer_transform (a := a) (z := -z) ha1
  rw [show a + 1 - a = 1 by ring, neg_neg, kummerM_eq_mul_regularizedHGFun ha1,
    kummerM_eq_mul_regularizedHGFun ha1] at hK
  rw [lowerIncGamma_eq_regularized ha, scIncGamma]
  have hzz : z ^ (-a) * z ^ a = 1 := by
    rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hz))]
  have h1 : regularizedHGFun {a} {a + 1} (-z) = exp (-z) * regularizedHGFun {1} {a + 1} z :=
    mul_left_cancel₀ hΓ1 (by rw [hK]; ring)
  calc exp (-z) * regularizedHGFun {1} {a + 1} z = regularizedHGFun {a} {a + 1} (-z) := h1.symm
    _ = z ^ (-a) * z ^ a * regularizedHGFun {a} {a + 1} (-z) * (Gamma a / Gamma a) := by
        rw [hzz, div_self hΓ]; ring
    _ = _ := by ring

/-- `γ*(a,z) = z^{-a} P(a,z)` (DLMF 8.2.7). -/
@[dlmf 8.2.E7]
theorem scIncGamma_eq_normIncGammaP {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    scIncGamma a z = z ^ (-a) * normIncGammaP a z := by
  rw [scIncGamma_eq ha hz, normIncGammaP]; ring

/-- `γ*(-n, z) = zⁿ` (DLMF 8.4.12). -/
@[dlmf 8.4.E12]
theorem scIncGamma_neg_nat (n : ℕ) (z : ℂ) : scIncGamma (-n) z = z ^ n := by
  rw [scIncGamma_eq_tsum]
  set f : ℕ → ℂ := fun k => z ^ k / Gamma (-(n : ℂ) + k + 1)
  have hshift (j : ℕ) : f (j + n) = z ^ n * (z ^ j / j !) := by
    simp only [f]
    rw [show -(n : ℂ) + ((j + n : ℕ) : ℂ) + 1 = (j : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial, pow_add]
    ring
  have hexp : HasSum (fun j : ℕ => z ^ j / j !) (exp z) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z
  have hzero : ∀ k ∈ Finset.range n, f k = 0 := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    simp only [f]
    rw [show -(n : ℂ) + k + 1 = -((n - k - 1 : ℕ) : ℂ) by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring,
      Gamma_neg_nat_eq_zero, div_zero]
  have hs : HasSum (fun j => f (j + n)) (z ^ n * exp z) := by
    simp_rw [hshift]; exact hexp.mul_left _
  have hf : HasSum f (z ^ n * exp z) := by
    rw [← hasSum_nat_add_iff' n]
    simpa [Finset.sum_eq_zero hzero] using hs
  rw [hf.tsum_eq, ← mul_assoc, mul_comm (exp (-z)), mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

end DLMF.Statistical
