/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Distributional.Basic
public import DLMF.Gamma.BetaFunction
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import DLMF.Gamma.ComplexBinet
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import DLMFMathlib.Analysis.Complex.IteratedDeriv

/-!
# Divergent integrals and the Stieltjes transform (DLMF §2.6(i)–(ii))

The example `S(x) = ∫₀^∞ (1+t)^{-1/3}/(x+t) dt` of DLMF §2.6(i) and the distributional
derivation of the asymptotic expansion of a Stieltjes transform (§2.6(ii)).

## Main results

* `one_add_rpow_neg_third_hasSum`, `not_integrableOn_rpow_div_add`: the binomial expansion
  2.6.2 and the divergence of the termwise integrals 2.6.3.
* `integral_rpow_div_add_cpow`, `gamma_two_thirds_sub_mul_gamma`: the Beta integral 2.6.4 and
  its generalized value 2.6.5.
* `not_stieltjesCubeRootExample_naive`, `stieltjesCubeRootExample_expansion`: the failure of the
  naive expansion 2.6.6 and the correct expansion 2.6.7.
* `functionPairing_eq_of_lt_one`, `functionPairing_eq_of_eq_one`: the distributional
  identities 2.6.17 (`0 < α < 1`) and 2.6.20 (`α = 1`).
* `tendsto_powPairing_stieltjesTestFunction`, `tendsto_logPowPairing_stieltjesTestFunction`,
  `tendsto_functionPairing_stieltjesTestFunction`, `tendsto_functionPairing_stieltjesTestFunction'`,
  `tendsto_remainderPairing_stieltjesTestFunction`: the limits 2.6.23–2.6.26.
* `stieltjesTransform_eq_of_lt_one`, `stieltjesTransform_eq_of_eq_one`: the expansions with
  exact remainder 2.6.27–2.6.30.

## Implementation notes

The Mellin transform of `f` and its analytic continuation (DLMF §2.5(ii)) enter through a
function `M` that is holomorphic on the right half-plane minus the poles `k + α` and agrees
with Mathlib's `mellin f` on the strip of convergence `0 < ℜz < α`; such an `M` is unique.
The test functions are Mathlib's Schwartz functions `𝓢(ℝ, ℂ)` (DLMF's space `𝒯`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Real Filter Asymptotics Finset
open scoped Topology Nat

namespace DLMF.AsymptoticApproximations

/-! ### §2.6(i) Divergent integrals -/

/-- DLMF 2.6.2: `(1+t)^{-1/3} = ∑_{s≥0} (-1/3 choose s) t^{-s-1/3}` for `t > 1`, with Mathlib's
generalized binomial coefficient `Ring.choose`. -/
@[dlmf 2.6.E2]
theorem one_add_rpow_neg_third_hasSum {t : ℝ} (ht : 1 < t) :
    HasSum (fun s : ℕ => Ring.choose (-(1 / 3) : ℝ) s * t ^ (-(s : ℝ) - 1 / 3))
      ((1 + t) ^ (-(1 / 3 : ℝ))) := by
  have ht0 : 0 < t := by linarith
  have hy : t⁻¹ ∈ Metric.eball (0 : ℝ) 1 := by
    have : ‖t⁻¹‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0)]; exact inv_lt_one_of_one_lt₀ ht
    rw [Metric.mem_eball, edist_zero_right]
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_one.2 this
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -(1 / 3 : ℝ))).hasSum hy
  simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
    zero_add] at h
  have h2 := h.mul_left (t ^ (-(1 / 3 : ℝ)))
  have e : t ^ (-(1 / 3 : ℝ)) * (1 + t⁻¹) ^ (-(1 / 3 : ℝ)) = (1 + t) ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.mul_rpow ht0.le (by positivity), mul_add, mul_one, mul_inv_cancel₀ ht0.ne',
      add_comm]
  rw [e] at h2
  refine h2.congr_fun fun s => ?_
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg ht0.le,
    show -(s : ℝ) - 1 / 3 = -(1 / 3) + -(s : ℝ) by ring, Real.rpow_add ht0]
  ring

/-- DLMF 2.6.3: the termwise integrals `∫₀^∞ t^{-s-1/3}/(x+t) dt`, `s = 1, 2, …`, diverge
(here: the integrand is not integrable on `(0, ∞)`), for every `x > 0`. -/
@[dlmf 2.6.E3]
theorem not_integrableOn_rpow_div_add {x : ℝ} (hx : 0 < x) {s : ℕ} (hs : 1 ≤ s) :
    ¬ IntegrableOn (fun t : ℝ => t ^ (-(s : ℝ) - 1 / 3) / (x + t)) (Ioi 0) := by
  intro h
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (-(s : ℝ) - 1 / 3) / (x + t))
      volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (h.mono_set Ioo_subset_Ioi_self)
  have hp := hi.mul_continuousOn
    ((continuous_const.add continuous_id : Continuous (fun t : ℝ => x + t)).continuousOn)
  have hpow : IntervalIntegrable (fun t : ℝ => t ^ (-(s : ℝ) - 1 / 3)) volume 0 1 := by
    refine hp.congr_uIoo fun t ht => ?_
    rw [uIoo_of_le zero_le_one] at ht
    exact div_mul_cancel₀ _ (by linarith [ht.1] : x + t ≠ 0)
  have hcrit := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hpow)
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

/-- DLMF 2.6.4: `∫₀^∞ t^{α-1}/(x+t)^{α+β} dt = Γ(α)Γ(β)/Γ(α+β) · x^{-β}` for `x > 0`,
`ℜα > 0`, `ℜβ > 0` (principal powers). -/
@[dlmf 2.6.E4]
theorem integral_rpow_div_add_cpow {x : ℝ} (hx : 0 < x) {α β : ℂ} (hα : 0 < α.re)
    (hβ : 0 < β.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (α - 1) / ((x : ℂ) + t) ^ (α + β) =
      Complex.Gamma α * Complex.Gamma β / Complex.Gamma (α + β) / (x : ℂ) ^ β := by
  have hsub := integral_comp_mul_left_Ioi
    (fun t : ℝ => (t : ℂ) ^ (α - 1) / ((x : ℂ) + t) ^ (α + β)) 0 hx
  rw [mul_zero] at hsub
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      (((x * u : ℝ) : ℂ) ^ (α - 1) / ((x : ℂ) + ((x * u : ℝ) : ℂ)) ^ (α + β)) =
        ((x : ℂ) ^ (α - 1) / (x : ℂ) ^ (α + β)) *
          ((u : ℂ) ^ (α - 1) / (1 + (u : ℂ)) ^ (α + β)) := by
    intro u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    rw [show (x : ℂ) + ((x * u : ℝ) : ℂ) = ((x : ℝ) : ℂ) * ((1 + u : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le hu0,
      Complex.mul_cpow_ofReal_nonneg hx.le (by linarith)]
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    DLMF.Gamma.beta_on_Ioi] at hsub
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral hα hβ
  have hG : Complex.Gamma (α + β) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos; simp; linarith
  have e : (x : ℂ) ^ (α - 1) / (x : ℂ) ^ (α + β) = (x : ℂ)⁻¹ / (x : ℂ) ^ β := by
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_add _ _ hx0, Complex.cpow_one]
    have : (x : ℂ) ^ α ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hx0]
    have : (x : ℂ) ^ β ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hx0]
    field_simp
  rw [e] at hsub
  have hsub' : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (α - 1) / ((x : ℂ) + t) ^ (α + β) =
      (x : ℂ) * ((x : ℂ)⁻¹ / (x : ℂ) ^ β * Complex.betaIntegral α β) := by
    rw [hsub]; simp only [Complex.real_smul, Complex.ofReal_inv]; field_simp
  rw [hsub', hB]
  field_simp

/-- DLMF 2.6.5: the generalized value of `∫₀^∞ t^{-s-1/3}/(x+t) dt` obtained from the
right-hand side of 2.6.4 with `α = 2/3 - s`, `β = s + 1/3`:
`Γ(2/3 - s) Γ(s + 1/3)/Γ(1) · x^{-s-1/3} = (2π/√3) (-1)^s x^{-s-1/3}`, `s = 0, 1, 2, …`. -/
@[dlmf 2.6.E5]
theorem gamma_two_thirds_sub_mul_gamma (s : ℕ) {x : ℝ} :
    Real.Gamma (2 / 3 - s) * Real.Gamma (s + 1 / 3) / Real.Gamma 1 * x ^ (-(s : ℝ) - 1 / 3) =
      2 * π / √3 * (-1) ^ s * x ^ (-(s : ℝ) - 1 / 3) := by
  have h := Real.Gamma_mul_Gamma_one_sub ((s : ℝ) + 1 / 3)
  rw [show (1 : ℝ) - (s + 1 / 3) = 2 / 3 - s by ring] at h
  have hsin : Real.sin (π * (s + 1 / 3)) = (-1) ^ s * (√3 / 2) := by
    rw [show π * (s + 1 / 3) = π / 3 + s * π by ring, Real.sin_add_nat_mul_pi,
      Real.sin_pi_div_three]
  rw [mul_comm (Real.Gamma _), h, hsin, Real.Gamma_one, div_one]
  congr 1
  have h3 : (√3 : ℝ) ≠ 0 := by positivity
  rcases neg_one_pow_eq_or ℝ s with h1 | h1 <;> rw [h1] <;> field_simp

/-- The value `∫₀^∞ t^{-1/3}/(t+x) dt = (2π/√3) x^{-1/3}` (2.6.4 with `α = 2/3`, `β = 1/3`). -/
private lemma integral_rpow_neg_third_div {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 3 : ℝ)) / (t + x) = 2 * π / √3 * x ^ (-(1 / 3 : ℝ)) := by
  have h := integral_rpow_div_add_cpow hx (α := (2 / 3 : ℝ)) (β := (1 / 3 : ℝ))
    (by norm_num) (by norm_num)
  have h5 := gamma_two_thirds_sub_mul_gamma 0 (x := x)
  simp only [CharP.cast_eq_zero, sub_zero, zero_add, neg_zero, zero_sub, pow_zero,
    mul_one] at h5
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hl : ∫ t in Ioi (0 : ℝ), (((t ^ (-(1 / 3 : ℝ)) / (t + x) : ℝ)) : ℂ) =
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (((2 / 3 : ℝ) : ℂ) - 1) /
        ((x : ℂ) + t) ^ (((2 / 3 : ℝ) : ℂ) + ((1 / 3 : ℝ) : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [show ((2 / 3 : ℝ) : ℂ) + ((1 / 3 : ℝ) : ℂ) = 1 by push_cast; norm_num, Complex.cpow_one,
      show ((2 / 3 : ℝ) : ℂ) - 1 = ((-(1 / 3) : ℝ) : ℂ) by push_cast; norm_num,
      ← Complex.ofReal_cpow ht.le]
    push_cast; ring
  rw [hl, h, ← Complex.ofReal_cpow hx.le,
    show ((2 / 3 : ℝ) : ℂ) + ((1 / 3 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) by push_cast; norm_num,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  have h' : 2 * π / √3 * x ^ (-(1 / 3 : ℝ)) =
      Real.Gamma (2 / 3) * Real.Gamma (1 / 3) / Real.Gamma 1 / x ^ (1 / 3 : ℝ) := by
    rw [← h5, Real.rpow_neg hx.le]; ring
  rw [h']; push_cast; ring


/-- The real form of `S(x)`. -/
private lemma stieltjesCubeRootExample_eq_ofReal (x : ℝ) :
    stieltjesCubeRootExample x =
      ((∫ t in Ioi (0 : ℝ), (1 + t) ^ (-(1 / 3 : ℝ)) / (t + x) : ℝ) : ℂ) := by
  rw [stieltjesCubeRootExample, stieltjesTransform_eq, ← integral_complex_ofReal]
  push_cast; rfl

/-- `x (P(x) - S(x)) ≥ c/2` for `x ≥ 1`, where `P(x) = ∫ t^{-1/3}/(t+x)` and `c` is the
integral of `t^{-1/3} - (1+t)^{-1/3}` over `(0, 1)`. -/
private lemma half_le_mul_sub {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2) * ∫ t in (0 : ℝ)..1, (t ^ (-(1 / 3 : ℝ)) - (1 + t) ^ (-(1 / 3 : ℝ))) ≤
      x * ((∫ t in Ioi (0 : ℝ), t ^ (-(1 / 3 : ℝ)) / (t + x)) -
        ∫ t in Ioi (0 : ℝ), (1 + t) ^ (-(1 / 3 : ℝ)) / (t + x)) := by
  have hx0 : 0 < x := by linarith
  have hP := integral_rpow_neg_third_div hx0
  have hPi : IntegrableOn (fun t : ℝ => t ^ (-(1 / 3 : ℝ)) / (t + x)) (Ioi 0) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hP]; have := Real.rpow_pos_of_pos hx0 (-(1 / 3 : ℝ)); positivity
  have hle : ∀ t ∈ Ioi (0 : ℝ), (1 + t) ^ (-(1 / 3 : ℝ)) ≤ t ^ (-(1 / 3 : ℝ)) := fun t ht =>
    Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
  have hSi : IntegrableOn (fun t : ℝ => (1 + t) ^ (-(1 / 3 : ℝ)) / (t + x)) (Ioi 0) := by
    refine Integrable.mono' hPi ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.div ?_ (by fun_prop) (by linarith)
      exact (continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (by simp only [Pi.add_apply, id]; linarith))
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht' : (0 : ℝ) < t := ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (hle t ht) (by linarith)
  set h : ℝ → ℝ := fun t => x * (t ^ (-(1 / 3 : ℝ)) / (t + x) - (1 + t) ^ (-(1 / 3 : ℝ)) / (t + x))
  have hhi : IntegrableOn h (Ioi 0) := (hPi.sub hSi).const_mul x
  have hh0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ h t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have := hle t ht
    have : (1 + t) ^ (-(1 / 3 : ℝ)) / (t + x) ≤ t ^ (-(1 / 3 : ℝ)) / (t + x) :=
      div_le_div_of_nonneg_right this (by linarith)
    exact mul_nonneg hx0.le (by linarith)
  have e1 : x * ((∫ t in Ioi (0 : ℝ), t ^ (-(1 / 3 : ℝ)) / (t + x)) -
        ∫ t in Ioi (0 : ℝ), (1 + t) ^ (-(1 / 3 : ℝ)) / (t + x)) = ∫ t in Ioi (0 : ℝ), h t := by
    rw [← integral_sub hPi hSi, ← integral_const_mul]
  rw [e1]
  have hgi : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 3 : ℝ)) - (1 + t) ^ (-(1 / 3 : ℝ)))
      volume 0 1 := by
    refine (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).sub ?_
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact ((continuousAt_const.add continuousAt_id).rpow_const
      (Or.inl (by simp only [Pi.add_apply, id]; linarith [ht.1]))).continuousWithinAt
  have hgi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hgi
  calc (1 / 2) * ∫ t in (0 : ℝ)..1, (t ^ (-(1 / 3 : ℝ)) - (1 + t) ^ (-(1 / 3 : ℝ)))
      = ∫ t in Ioc (0 : ℝ) 1, (1 / 2) * (t ^ (-(1 / 3 : ℝ)) - (1 + t) ^ (-(1 / 3 : ℝ))) := by
        rw [intervalIntegral.integral_of_le zero_le_one, integral_const_mul]
    _ ≤ ∫ t in Ioc (0 : ℝ) 1, h t := by
        refine setIntegral_mono_on (hgi'.const_mul _) (hhi.mono_set Ioc_subset_Ioi_self)
          measurableSet_Ioc fun t ht => ?_
        have hle' := hle t ht.1
        have hpos : 0 < t + x := by linarith [ht.1]
        simp only [h]
        rw [← sub_div, mul_div_assoc', le_div_iff₀ hpos]
        have : 0 ≤ t ^ (-(1 / 3 : ℝ)) - (1 + t) ^ (-(1 / 3 : ℝ)) := by linarith
        nlinarith [ht.2]
    _ ≤ ∫ t in Ioi (0 : ℝ), h t :=
        setIntegral_mono_set hhi ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall hh0)) (Eventually.of_forall Ioc_subset_Ioi_self)


/-- DLMF 2.6.7: the correct asymptotic expansion of `S(x)` as `x → +∞`,
`S(x) ∼ (2π/√3) ∑ (-1)^s (-1/3 choose s) x^{-s-1/3} - ∑_{s≥1} 3^s (s-1)!/(2·5⋯(3s-1)) x^{-s}`,
in the form: for every `n`, the remainder after the terms with `s < n` in the first sum and
`s ≤ n` in the second is `O(x^{-n-1/3})`. (DLMF also states validity for complex `x` with
`|ph x| ≤ π - δ`; the real case is formalized.) -/
@[dlmf 2.6.E7, dlmf 2.6.E1]
theorem stieltjesCubeRootExample_expansion (n : ℕ) :
    (fun x : ℝ => stieltjesCubeRootExample x -
        ((stieltjesCubeRootNaiveSum n x - stieltjesCubeRootMissingSum n x : ℝ) : ℂ))
      =O[atTop] (fun x : ℝ => x ^ (-(n : ℝ) - 1 / 3)) := by
  sorry

/-- DLMF 2.6.6 is incorrect: the formal termwise expansion
`S(x) ∼ (2π/√3) ∑ (-1)^s (-1/3 choose s) x^{-s-1/3}` does not hold; already with two terms
the remainder is not `O(x^{-4/3})` (the missing term `-(3/2) x^{-1}` of 2.6.7 dominates). -/
@[dlmf 2.6.E6]
theorem not_stieltjesCubeRootExample_naive :
    ¬ (fun x : ℝ => stieltjesCubeRootExample x - ((stieltjesCubeRootNaiveSum 2 x : ℝ) : ℂ))
      =O[atTop] (fun x : ℝ => x ^ (-(1 : ℝ) - 1 / 3)) := by
  intro hO
  set c : ℝ := ∫ t in (0 : ℝ)..1, (t ^ (-(1 / 3 : ℝ)) - (1 + t) ^ (-(1 / 3 : ℝ)))
  have hc : 0 < c := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht => ?_) zero_lt_one
    · refine (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).sub ?_
      refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact ((continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (by simp only [Pi.add_apply, id]; linarith [ht.1]))).continuousWithinAt
    · have := Real.rpow_lt_rpow_of_neg ht.1 (by linarith : t < 1 + t)
        (by norm_num : (-(1 / 3 : ℝ)) < 0)
      linarith
  obtain ⟨C, hC⟩ := hO.bound
  have hlim : Tendsto (fun x : ℝ => x ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  set K : ℝ := 2 * π / √3 * (1 / 3) + |C|
  have hev := (hlim.const_mul K).eventually (gt_mem_nhds (show K * 0 < c / 2 by
    rw [mul_zero]; positivity))
  obtain ⟨x, hx, hxK, hx1⟩ := (hC.and (hev.and (eventually_ge_atTop 1))).exists
  have hx0 : 0 < x := by linarith
  have hkey := half_le_mul_sub hx1
  rw [integral_rpow_neg_third_div hx0] at hkey
  set Sr := ∫ t in Ioi (0 : ℝ), (1 + t) ^ (-(1 / 3 : ℝ)) / (t + x)
  rw [stieltjesCubeRootExample_eq_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hx
  have hN : stieltjesCubeRootNaiveSum 2 x =
      2 * π / √3 * (x ^ (-(1 / 3 : ℝ)) + 1 / 3 * x ^ (-(1 : ℝ) - 1 / 3)) := by
    simp [stieltjesCubeRootNaiveSum, Finset.sum_range_succ]
  have hpow : x * x ^ (-(1 : ℝ) - 1 / 3) = x ^ (-(1 / 3 : ℝ)) := by
    rw [show -(1 : ℝ) - 1 / 3 = -1 + -(1 / 3) by norm_num, Real.rpow_add hx0, Real.rpow_neg_one,
      ← mul_assoc, mul_inv_cancel₀ hx0.ne', one_mul]
  rw [hN] at hx
  have hxp : 0 < x ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hb : x * |Sr - 2 * π / √3 * (x ^ (-(1 / 3 : ℝ)) + 1 / 3 * x ^ (-(1 : ℝ) - 1 / 3))| ≤
      |C| * x ^ (-(1 / 3 : ℝ)) := by
    have h1 := hx.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (Real.rpow_pos_of_pos hx0 (-(1 : ℝ) - 1 / 3)).le)
    calc _ ≤ x * (|C| * x ^ (-(1 : ℝ) - 1 / 3)) := mul_le_mul_of_nonneg_left h1 hx0.le
      _ = |C| * x ^ (-(1 / 3 : ℝ)) := by rw [← hpow]; ring
  have hab := neg_abs_le (Sr - 2 * π / √3 * (x ^ (-(1 / 3 : ℝ)) + 1 / 3 * x ^ (-(1 : ℝ) - 1 / 3)))
  have : c / 2 ≤ K * x ^ (-(1 / 3 : ℝ)) := by
    have e : x * (2 * π / √3 * x ^ (-(1 / 3 : ℝ)) - Sr) =
        -(2 * π / √3 * (1 / 3) * (x * x ^ (-(1 : ℝ) - 1 / 3))) -
        x * (Sr - 2 * π / √3 * (x ^ (-(1 / 3 : ℝ)) + 1 / 3 * x ^ (-(1 : ℝ) - 1 / 3))) := by ring
    rw [hpow] at e
    have hm := mul_le_mul_of_nonneg_left hab hx0.le
    have hpi : 0 < 2 * π / √3 * (1 / 3) * x ^ (-(1 / 3 : ℝ)) := by positivity
    have hK : |C| * x ^ (-(1 / 3 : ℝ)) ≤ K * x ^ (-(1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by
        have : 0 < 2 * π / √3 * (1 / 3) := by positivity
        simp only [K]; linarith) hxp.le
    linarith
  linarith

/-! ### §2.6(ii) Stieltjes transform -/

/-- DLMF 2.6.17 (with 2.6.18 and 2.6.19): for `0 < α < 1` and `n ≥ 1`, the distribution
associated with `f` decomposes as
`⟨f, φ⟩ = ∑_{s<n} a_s ⟨t^{-s-α}, φ⟩ - ∑_{s=1}^{n} c_s ⟨δ^{(s-1)}, φ⟩ + ⟨f_n, φ⟩`
for every Schwartz function `φ`, with `c_s = (-1)^s 𝓜f(s)/(s-1)!`. In the language of
distributions this is DLMF 2.6.41. -/
@[dlmf 2.6.E17, dlmf 2.6.E41]
theorem functionPairing_eq_of_lt_one {f : ℝ → ℂ} {α : ℝ} {a : ℕ → ℂ}
    (hf : IsStieltjesExpansion f α a) (hα : α < 1) {M : ℂ → ℂ} (hM : IsMellinContinuation f α M)
    {n : ℕ} (hn : 1 ≤ n) (u : SchwartzMap ℝ ℂ) :
    functionPairing f u =
      ∑ s ∈ range n, a s * powPairing α s u -
        ∑ s ∈ Icc 1 n, stieltjesDeltaCoeff M s * diracDerivPairing (s - 1) u +
        remainderPairing n (stieltjesRemainder f α a n) u := by
  sorry

/-- DLMF 2.6.20 (with 2.6.21): for `α = 1` and `n ≥ 1`,
`⟨f, φ⟩ = ∑_{s<n} a_s ⟨t^{-s-1}, φ⟩ - ∑_{s=1}^{n} d_s ⟨δ^{(s-1)}, φ⟩ + ⟨f_n, φ⟩`
for every Schwartz function `φ`, with `d_{s+1}` as in 2.6.21. In the language of
distributions this is DLMF 2.6.42. -/
@[dlmf 2.6.E20, dlmf 2.6.E42]
theorem functionPairing_eq_of_eq_one {f : ℝ → ℂ} {a : ℕ → ℂ}
    (hf : IsStieltjesExpansion f 1 a) {M : ℂ → ℂ} (hM : IsMellinContinuation f 1 M)
    {n : ℕ} (hn : 1 ≤ n) (u : SchwartzMap ℝ ℂ) :
    functionPairing f u =
      ∑ s ∈ range n, a s * logPowPairing s u -
        ∑ s ∈ range n, stieltjesLogDeltaCoeff M a s * diracDerivPairing s u +
        remainderPairing n (stieltjesRemainder f 1 a n) u := by
  sorry

/-- The iterated derivatives of `φ_ε(t) = e^{-εt}/(t+z)` (Leibniz rule). -/
private lemma iteratedDeriv_stieltjesTestFunction (ε : ℝ) {z : ℂ} (n : ℕ) {t : ℝ}
    (ht : (t : ℂ) + z ≠ 0) :
    iteratedDeriv n (stieltjesTestFunction ε z) t = ∑ i ∈ range (n + 1),
      (n.choose i : ℂ) * ((-(ε : ℂ)) ^ i * Complex.exp (-(ε : ℂ) * t)) *
        ((-1) ^ (n - i) * ((n - i)! : ℂ) * ((t : ℂ) + z) ^ (-1 - ((n - i : ℕ) : ℤ))) := by
  set U : Set ℂ := {w | w + z ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (by fun_prop) continuous_const
  set f : ℂ → ℂ := fun w => Complex.exp (-(ε : ℂ) * w)
  set g : ℂ → ℂ := fun w => (1 * w + z)⁻¹
  have hΨ : DifferentiableOn ℂ (f * g) U := fun w hw =>
    ((by fun_prop : DifferentiableAt ℂ f w).mul
      ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1 * w + z) w).inv
        (by have hw2 : w + z ≠ 0 := hw; simpa using hw2))).differentiableWithinAt
  have he : stieltjesTestFunction ε z = fun x : ℝ => (f * g) x := by
    funext x
    simp only [stieltjesTestFunction, Pi.mul_apply, f, g, one_mul]
    rw [div_eq_mul_inv, neg_mul]
  rw [he, Complex.iteratedDeriv_comp_ofReal_of_differentiableOn hU hΨ n ht]
  have hfc : ContDiffAt ℂ n f t := by fun_prop
  have hgc : ContDiffAt ℂ n g t :=
    (contDiffAt_inv ℂ (by simpa using ht)).comp _ (by fun_prop)
  rw [iteratedDeriv_mul hfc hgc]
  refine sum_congr rfl fun i _ => ?_
  have h1 : iteratedDeriv i f t = (-(ε : ℂ)) ^ i * Complex.exp (-(ε : ℂ) * t) := by
    simp only [f]
    rw [iteratedDeriv_cexp_const_mul]
  have h2 : iteratedDeriv (n - i) g t =
      (-1) ^ (n - i) * ((n - i)! : ℂ) * ((t : ℂ) + z) ^ (-1 - ((n - i : ℕ) : ℤ)) := by
    simp only [g]
    rw [iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
    simp
  rw [h1, h2]

/-- `t^{-α}/(1+t)` is integrable on `(0, ∞)` for `0 < α < 1`. -/
private lemma integrableOn_rpow_neg_div_one_add {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntegrableOn (fun t : ℝ => t ^ (-α) / (1 + t)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hi : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (r := -α) (by linarith)
        (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    refine hi.mono' ?_ ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall
      fun t ht => ?_))
    · exact ((continuousOn_id.rpow_const fun t (ht : t ∈ Ioc (0 : ℝ) 1) =>
        Or.inl (show t ≠ 0 from ht.1.ne')).div (by fun_prop)
        fun t (ht : t ∈ Ioc (0 : ℝ) 1) => by linarith [ht.1]).aestronglyMeasurable
        measurableSet_Ioc
    · have h0 := Real.rpow_pos_of_pos ht.1 (-α)
      rw [Real.norm_of_nonneg (by have := ht.1; positivity)]
      exact div_le_self h0.le (by linarith [ht.1])
  · have hi := integrableOn_Ioi_rpow_of_lt (a := -α - 1) (by linarith) one_pos
    refine hi.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
      fun t (ht : 1 < t) => ?_))
    · exact ((continuousOn_id.rpow_const fun t (ht : 1 < t) =>
        Or.inl (show t ≠ 0 by linarith)).div
        (by fun_prop) fun t (ht : 1 < t) => by linarith).aestronglyMeasurable measurableSet_Ioi
    · have ht0 : 0 < t := by linarith
      rw [Real.norm_of_nonneg (by positivity), Real.rpow_sub ht0, Real.rpow_one]
      exact div_le_div_of_nonneg_left (by positivity) ht0 (by linarith)

/-- The Beta integral `∫₀^∞ t^{-α} (t+x)^{-s-1} dt` for real `x > 0`. -/
private lemma integral_rpow_neg_div_add_pow_ofReal {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (s : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), ((t ^ (-α) : ℝ) : ℂ) * (((t : ℂ) + x) ^ (s + 1))⁻¹ =
      Complex.Gamma (1 - α) * Complex.Gamma (s + α) / Complex.Gamma (s + 1) *
        (x : ℂ) ^ (-((s : ℂ) + α)) := by
  have h := integral_rpow_div_add_cpow hx (α := 1 - α) (β := s + α) (by simp; linarith)
    (by simp; positivity)
  rw [show (1 - (α : ℂ)) + ((s : ℂ) + α) = ((s + 1 : ℕ) : ℂ) by push_cast; ring] at h
  rw [show (((s + 1 : ℕ) : ℂ)) = (s : ℂ) + 1 by push_cast; ring, Complex.cpow_neg] at *
  rw [← div_eq_mul_inv, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  rw [show (1 - (α : ℂ)) - 1 = ((-α : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow ht.le,
    show (s : ℂ) + 1 = ((s + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast,
    add_comm (x : ℂ), div_eq_mul_inv]

/-- `t + z` lies in the slit plane for `t ≥ 0`, `z` in the slit plane. -/
private lemma ofReal_add_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) {t : ℝ}
    (ht : 0 ≤ t) : (t : ℂ) + z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp; linarith
  · right; simpa using h

/-- The Beta integral `∫₀^∞ t^{-α} (t+z)^{-s-1} dt = Γ(1-α)Γ(s+α)/s! · z^{-s-α}` on the slit
plane, by analytic continuation from `z > 0`. -/
private lemma integral_rpow_neg_div_add_pow {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (s : ℕ)
    {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ∫ t in Ioi (0 : ℝ), ((t ^ (-α) : ℝ) : ℂ) * (((t : ℂ) + z) ^ (s + 1))⁻¹ =
      Complex.Gamma (1 - α) * Complex.Gamma (s + α) / Complex.Gamma (s + 1) *
        z ^ (-((s : ℂ) + α)) := by
  set F : ℂ → ℂ := fun z => ∫ t in Ioi (0 : ℝ), ((t ^ (-α) : ℝ) : ℂ) *
    (((t : ℂ) + z) ^ (s + 1))⁻¹
  set G : ℂ → ℂ := fun z => Complex.Gamma (1 - α) * Complex.Gamma (s + α) /
    Complex.Gamma (s + 1) * z ^ (-((s : ℂ) + α))
  have hne : ∀ y ∈ Complex.slitPlane, ∀ t : ℝ, 0 ≤ t → (t : ℂ) + y ≠ 0 := fun y hy t ht =>
    Complex.slitPlane_ne_zero (ofReal_add_mem_slitPlane hy ht)
  have hF : DifferentiableOn ℂ F Complex.slitPlane := by
    refine Complex.differentiableOn_integral_Ioi_of_locally_dominated
      Complex.isOpen_slitPlane 0 (fun y hy => ?_) ?_ (fun y hy => ?_)
    · exact (by fun_prop : Measurable fun t : ℝ => ((t ^ (-α) : ℝ) : ℂ) *
        (((t : ℂ) + y) ^ (s + 1))⁻¹).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht y hy => ?_)
      exact (((differentiableAt_const _).mul ((by fun_prop : DifferentiableAt ℂ
        (fun y : ℂ => ((t : ℂ) + y) ^ (s + 1)) y).inv
        (pow_ne_zero _ (hne y hy t (le_of_lt ht))))).differentiableWithinAt)
    · obtain ⟨κ, hκ, hκt'⟩ := DLMF.Gamma.exists_mul_one_add_le_norm_add hy
      have hκt : ∀ t : ℝ, 0 ≤ t → κ * (1 + t) ≤ ‖(t : ℂ) + y‖ := fun t ht => by
        rw [add_comm (t : ℂ)]; exact hκt' t ht
      refine ⟨Metric.ball y (κ / 2), Metric.ball_mem_nhds _ (by positivity),
        fun t => (2 / κ) ^ (s + 1) * (t ^ (-α) / (1 + t)),
        (integrableOn_rpow_neg_div_one_add hα0 hα1).const_mul _, ?_⟩
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
        fun t (ht : 0 < t) w hw => ?_)
      have hw' : ‖w - y‖ < κ / 2 := by simpa [dist_eq_norm] using hw
      have hlow : κ / 2 * (1 + t) ≤ ‖(t : ℂ) + w‖ := by
        have h1 := hκt t ht.le
        have h2 : ‖(t : ℂ) + y‖ ≤ ‖(t : ℂ) + w‖ + ‖w - y‖ := by
          calc ‖(t : ℂ) + y‖ = ‖((t : ℂ) + w) - (w - y)‖ := by ring_nf
            _ ≤ _ := norm_sub_le _ _
        nlinarith
      have hpos : 0 < κ / 2 * (1 + t) := by positivity
      have htp := Real.rpow_pos_of_pos ht (-α)
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg htp.le]
      have hp : (κ / 2 * (1 + t)) ^ (s + 1) ≤ ‖(t : ℂ) + w‖ ^ (s + 1) :=
        pow_le_pow_left₀ hpos.le hlow _
      have hq : (1 + t) ≤ (1 + t) ^ (s + 1) := le_self_pow₀ (by linarith) (by omega)
      calc t ^ (-α) * (‖(t : ℂ) + w‖ ^ (s + 1))⁻¹
          ≤ t ^ (-α) * ((κ / 2 * (1 + t)) ^ (s + 1))⁻¹ := by
            gcongr
        _ = (2 / κ) ^ (s + 1) * (t ^ (-α) / (1 + t) ^ (s + 1)) := by
            rw [mul_pow, mul_inv, div_pow, div_pow]; field_simp
        _ ≤ (2 / κ) ^ (s + 1) * (t ^ (-α) / (1 + t)) := by
            gcongr
  have hG : DifferentiableOn ℂ G Complex.slitPlane := fun y hy =>
    ((differentiableAt_const _).mul (differentiableAt_id.cpow_const hy)).differentiableWithinAt
  have hpre : IsPreconnected Complex.slitPlane :=
    (Complex.starConvex_one_slitPlane.isPathConnected
      Complex.one_mem_slitPlane).isConnected.isPreconnected
  have heq := (hF.analyticOnNhd Complex.isOpen_slitPlane).eqOn_of_preconnected_of_frequently_eq
    (hG.analyticOnNhd Complex.isOpen_slitPlane) hpre Complex.one_mem_slitPlane ?_
  · exact heq hz
  · have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
      simpa using hx.ne'
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    exact integral_rpow_neg_div_add_pow_ofReal hα0 hα1 s (by linarith)

/-- The real ascending Pochhammer polynomial at a real point, cast to `ℂ`. -/
private lemma ofReal_eval_ascPochhammer (s : ℕ) (x : ℝ) :
    (((ascPochhammer ℝ s).eval x : ℝ) : ℂ) = (ascPochhammer ℂ s).eval (x : ℂ) := by
  induction s with
  | zero => simp
  | succ n ih => simp [ascPochhammer_succ_eval, ih]

/-- DLMF 2.6.23: for `0 < α < 1`, `z ∉ (-∞, 0]` and `s = 0, 1, 2, …`,
`lim_{ε → 0+} ⟨t^{-s-α}, φ_ε⟩ = π/sin(πα) · (-1)^s / z^{s+α}` (principal power). -/
@[dlmf 2.6.E23]
theorem tendsto_powPairing_stieltjesTestFunction {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {z : ℂ} (hz : z ∈ Complex.slitPlane) (s : ℕ) :
    Tendsto (fun ε : ℝ => powPairing α s (stieltjesTestFunction ε z)) (𝓝[>] 0)
      (𝓝 (π / Real.sin (π * α) * (-1 : ℂ) ^ s / z ^ ((s : ℂ) + α))) := by
  obtain ⟨κ, hκ, hκt'⟩ := DLMF.Gamma.exists_mul_one_add_le_norm_add hz
  have hκt : ∀ t : ℝ, 0 ≤ t → κ * (1 + t) ≤ ‖(t : ℂ) + z‖ := fun t ht => by
    rw [add_comm (t : ℂ)]; exact hκt' t ht
  have hne : ∀ t : ℝ, 0 ≤ t → (t : ℂ) + z ≠ 0 := fun t ht =>
    Complex.slitPlane_ne_zero (ofReal_add_mem_slitPlane hz ht)
  set D : ℝ → ℝ → ℂ := fun ε t => ∑ i ∈ range (s + 1),
    (s.choose i : ℂ) * ((-(ε : ℂ)) ^ i * Complex.exp (-(ε : ℂ) * t)) *
      ((-1) ^ (s - i) * ((s - i)! : ℂ) * (((t : ℂ) + z) ^ (s - i + 1))⁻¹) with hD
  have hform : ∀ ε : ℝ, ∀ t : ℝ, 0 ≤ t → iteratedDeriv s (stieltjesTestFunction ε z) t = D ε t := by
    intro ε t ht
    rw [iteratedDeriv_stieltjesTestFunction ε s (hne t ht)]
    refine sum_congr rfl fun i _ => ?_
    rw [show (-1 - ((s - i : ℕ) : ℤ)) = -((s - i + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast]
  set A : ℂ := (((ascPochhammer ℝ s).eval α : ℝ) : ℂ)
  have hpair : ∀ ε : ℝ, powPairing α s (stieltjesTestFunction ε z) =
      A⁻¹ * ∫ t in Ioi (0 : ℝ), ((t ^ (-α) : ℝ) : ℂ) * D ε t := by
    intro ε
    unfold powPairing
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => by rw [hform ε t ht.le]
  simp_rw [hpair]
  set L : ℝ → ℂ := fun t => (-1) ^ s * (s ! : ℂ) * (((t : ℂ) + z) ^ (s + 1))⁻¹
  have hD0 : ∀ t : ℝ, D 0 t = L t := by
    intro t
    simp only [hD, L]
    rw [sum_eq_single 0]
    · simp
    · intro i _ hi
      simp [zero_pow hi]
    · intro h; simp at h
  set K : ℝ := ∑ i ∈ range (s + 1), (s.choose i : ℝ) * (s - i)! * (1 / κ) ^ (s - i)
  have hlim : Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), ((t ^ (-α) : ℝ) : ℂ) * D ε t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), ((t ^ (-α) : ℝ) : ℂ) * L t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => K / κ * (t ^ (-α) / (1 + t))) ?_ ?_
      ((integrableOn_rpow_neg_div_one_add hα0 hα1).const_mul _) ?_
    · exact Eventually.of_forall fun ε => (by fun_prop : Measurable fun t : ℝ =>
        ((t ^ (-α) : ℝ) : ℂ) * D ε t).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
        fun t (ht : 0 < t) => ?_)
      have htz := hκt t ht.le
      have hκ1 : κ ≤ ‖(t : ℂ) + z‖ := le_trans (by nlinarith) htz
      have hn0 : 0 < ‖(t : ℂ) + z‖ := hκ.trans_le hκ1
      have htp := Real.rpow_pos_of_pos ht (-α)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg htp.le]
      have hDb : ‖D ε t‖ ≤ K / κ / (1 + t) := by
        refine (norm_sum_le _ _).trans ?_
        rw [show K / κ / (1 + t) = ∑ i ∈ range (s + 1),
            (s.choose i : ℝ) * (s - i)! * (1 / κ) ^ (s - i) / κ / (1 + t) by
          simp only [K, sum_div]]
        refine sum_le_sum fun i _ => ?_
        have he : ‖Complex.exp (-(ε : ℂ) * t)‖ ≤ 1 := by
          rw [Complex.norm_exp]
          simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, mul_zero, sub_zero, Real.exp_le_one_iff, Left.neg_nonpos_iff]
          exact mul_nonneg hε.1.le ht.le
        have hεi : ‖(-(ε : ℂ)) ^ i‖ ≤ 1 := by
          rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hε.1.le]
          exact pow_le_one₀ hε.1.le hε.2
        have hpow : κ ^ (s - i) * ‖(t : ℂ) + z‖ ≤ ‖(t : ℂ) + z‖ ^ (s - i + 1) := by
          rw [pow_succ]
          gcongr
        have hm : ‖(((t : ℂ) + z) ^ (s - i + 1))⁻¹‖ ≤ (1 / κ) ^ (s - i) / κ / (1 + t) := by
          rw [norm_inv, norm_pow, show (1 / κ) ^ (s - i) / κ / (1 + t) =
            (κ ^ (s - i) * (κ * (1 + t)))⁻¹ by rw [one_div_pow]; field_simp]
          refine inv_anti₀ (by positivity) ?_
          calc κ ^ (s - i) * (κ * (1 + t)) ≤ κ ^ (s - i) * ‖(t : ℂ) + z‖ := by gcongr
            _ ≤ _ := hpow
        calc ‖(s.choose i : ℂ) * ((-(ε : ℂ)) ^ i * Complex.exp (-(ε : ℂ) * t)) *
              ((-1) ^ (s - i) * ((s - i)! : ℂ) * (((t : ℂ) + z) ^ (s - i + 1))⁻¹)‖
            = (s.choose i : ℝ) * (‖(-(ε : ℂ)) ^ i‖ * ‖Complex.exp (-(ε : ℂ) * t)‖) *
              ((s - i)! * ‖(((t : ℂ) + z) ^ (s - i + 1))⁻¹‖) := by
              simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
                Complex.norm_natCast]
          _ ≤ (s.choose i : ℝ) * (1 * 1) * ((s - i)! * ((1 / κ) ^ (s - i) / κ / (1 + t))) := by
              gcongr
          _ = _ := by ring
      calc t ^ (-α) * ‖D ε t‖ ≤ t ^ (-α) * (K / κ / (1 + t)) := by gcongr
        _ = _ := by ring
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
        fun t (ht : 0 < t) => ?_)
      rw [← hD0]
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine Continuous.tendsto' ?_ 0 _ rfl
      fun_prop
  have hint : ∫ t in Ioi (0 : ℝ), ((t ^ (-α) : ℝ) : ℂ) * L t =
      (-1) ^ s * (s ! : ℂ) * ∫ t in Ioi (0 : ℝ), ((t ^ (-α) : ℝ) : ℂ) *
        (((t : ℂ) + z) ^ (s + 1))⁻¹ := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp only [L]; ring
  rw [hint, integral_rpow_neg_div_add_pow hα0 hα1 s hz] at hlim
  convert hlim.const_mul A⁻¹ using 2
  have hαne : ∀ k : ℕ, (α : ℂ) ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hGα : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hαne
  have hA : A * Complex.Gamma α = Complex.Gamma (s + α) := by
    have h := Complex.Gamma_add_nat_div_Gamma_eq (n := s) (α : ℂ) hαne
    simp only [A, ofReal_eval_ascPochhammer, ← h, add_comm (α : ℂ)]
    field_simp
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hA
    exact Complex.Gamma_ne_zero_of_re_pos (s := (s : ℂ) + α) (by simp; positivity) hA.symm
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (α : ℂ)
  have hsin : ((Real.sin (π * α) : ℝ) : ℂ) = Complex.sin (π * α) := by push_cast; ring_nf
  have hzp : z ^ ((s : ℂ) + α) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
      intro h; have := congrArg Complex.re h; simp at this
      linarith [(s.cast_nonneg : (0 : ℝ) ≤ s)])]
    exact Complex.slitPlane_ne_zero hz
  have hfact : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero s)
  rw [Complex.Gamma_nat_eq_factorial, Complex.cpow_neg, ← hA, hsin, ← hrefl]
  field_simp

/-- The primitive `t log t/(z(t+z)) - log(t+z)/z` tends to `0` at infinity. -/
private lemma tendsto_logPrimitive_atTop {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Tendsto (fun t : ℝ => ((t * Real.log t : ℝ) : ℂ) / (z * ((t : ℂ) + z)) -
      Complex.log ((t : ℂ) + z) / z) atTop (𝓝 0) := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hzt : Tendsto (fun t : ℝ => z / (t : ℂ)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ))
      have := (Complex.continuous_ofReal.tendsto 0).comp h
      simpa [Function.comp_def] using this
    simpa [div_eq_mul_inv] using this.const_mul z
  have hlogt : Tendsto (fun t : ℝ => ((Real.log t / t : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have := (Complex.continuous_ofReal.tendsto 0).comp h
    simpa [Function.comp_def] using this
  have hlog1 : Tendsto (fun t : ℝ => Complex.log (1 + z / t)) atTop (𝓝 0) := by
    have hc : ContinuousAt Complex.log 1 :=
      continuousAt_clog Complex.one_mem_slitPlane
    have := hc.tendsto.comp (by simpa using hzt.const_add 1)
    simpa [Function.comp_def] using this
  have hlim : Tendsto (fun t : ℝ => (-(z * ((Real.log t / t : ℝ) : ℂ) / (1 + z / t)) -
      Complex.log (1 + z / t)) / z) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 1 + z / (t : ℂ)) atTop (𝓝 1) := by
      simpa using hzt.const_add 1
    have := ((((hlogt.const_mul z).div h1 one_ne_zero).neg).sub hlog1).div_const z
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have htz : (t : ℂ) + z ≠ 0 := Complex.slitPlane_ne_zero (ofReal_add_mem_slitPlane hz ht.le)
  have h1 : 1 + z / t ≠ 0 := by
    intro h; apply htz
    have : (t : ℂ) + z = t * (1 + z / t) := by field_simp
    rw [this, h, mul_zero]
  have hlog : Complex.log ((t : ℂ) + z) = (Real.log t : ℂ) + Complex.log (1 + z / t) := by
    have : (t : ℂ) + z = t * (1 + z / t) := by field_simp
    rw [this, Complex.log_ofReal_mul ht h1]
  rw [hlog]
  have h1' : (1 + z / t) = ((t : ℂ) + z) / t := by field_simp
  rw [h1']
  push_cast
  field_simp
  ring

private lemma integrableOn_abs_log_div_one_add_sq :
    IntegrableOn (fun t : ℝ => |Real.log t| / (1 + t) ^ 2) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hi : IntegrableOn (fun t : ℝ => |Real.log t|) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).norm
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
      simpa using this
    refine hi.mono' ?_ ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall
      fun t ht => ?_))
    · exact (by fun_prop : Measurable fun t : ℝ => |Real.log t| / (1 + t) ^ 2).aestronglyMeasurable
    · have h1 : 1 ≤ (1 + t) ^ 2 := one_le_pow₀ (by linarith [ht.1])
      rw [Real.norm_of_nonneg (by positivity)]
      exact div_le_self (abs_nonneg _) h1
  · have hi := (integrableOn_Ioi_rpow_of_lt (a := -(3 / 2)) (by norm_num) one_pos).const_mul 2
    refine hi.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
      fun t (ht : 1 < t) => ?_))
    · exact (by fun_prop : Measurable fun t : ℝ => |Real.log t| / (1 + t) ^ 2).aestronglyMeasurable
    · have ht0 : 0 < t := by linarith
      have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
      have hl := Real.log_le_rpow_div ht0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [Real.norm_of_nonneg (by positivity), abs_of_nonneg hl0]
      have hsq : t ^ (2 : ℝ) ≤ (1 + t) ^ 2 := by
        rw [Real.rpow_two]; nlinarith
      have hsplit : t ^ (-(3 / 2) : ℝ) = t ^ (1 / 2 : ℝ) / t ^ (2 : ℝ) := by
        rw [← Real.rpow_sub ht0]; norm_num
      rw [hsplit]
      calc Real.log t / (1 + t) ^ 2 ≤ (t ^ (1 / 2 : ℝ) / (1 / 2)) / t ^ (2 : ℝ) := by
            gcongr
        _ = _ := by ring

/-- A point of the slit plane stays at distance `≥ κ (1 + t)` from `-t`, `t ≥ 0`. -/
private lemma exists_mul_one_add_le_norm_ofReal_add {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ∃ κ > 0, ∀ t : ℝ, 0 ≤ t → κ * (1 + t) ≤ ‖(t : ℂ) + z‖ := by
  obtain ⟨κ, hκ, hκt'⟩ := DLMF.Gamma.exists_mul_one_add_le_norm_add hz
  exact ⟨κ, hκ, fun t ht => by rw [add_comm (t : ℂ)]; exact hκt' t ht⟩

/-- `log t · (t+z)^{-m}` is integrable on `(0, ∞)` for `m ≥ 2`, `z` in the slit plane. -/
private lemma integrableOn_log_mul_inv_add_pow {z : ℂ} (hz : z ∈ Complex.slitPlane) {m : ℕ}
    (hm : 2 ≤ m) :
    IntegrableOn (fun t : ℝ => (Real.log t : ℂ) * (((t : ℂ) + z) ^ m)⁻¹) (Ioi 0) := by
  obtain ⟨κ, hκ, hκt⟩ := exists_mul_one_add_le_norm_ofReal_add hz
  refine (integrableOn_abs_log_div_one_add_sq.const_mul ((1 / κ) ^ m)).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_))
  · exact (by fun_prop : Measurable fun t : ℝ =>
      (Real.log t : ℂ) * (((t : ℂ) + z) ^ m)⁻¹).aestronglyMeasurable
  · have h1 := hκt t ht.le
    have hpos : 0 < κ * (1 + t) := by positivity
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hp : (κ * (1 + t)) ^ m ≤ ‖(t : ℂ) + z‖ ^ m := pow_le_pow_left₀ hpos.le h1 m
    have hq : (1 + t) ^ 2 ≤ (1 + t) ^ m := pow_le_pow_right₀ (by linarith) hm
    calc |Real.log t| * (‖(t : ℂ) + z‖ ^ m)⁻¹ ≤ |Real.log t| * ((κ * (1 + t)) ^ m)⁻¹ := by
          gcongr
      _ = (1 / κ) ^ m * (|Real.log t| / (1 + t) ^ m) := by
          rw [mul_pow, one_div_pow]; field_simp
      _ ≤ (1 / κ) ^ m * (|Real.log t| / (1 + t) ^ 2) := by gcongr

/-- `∫₀^∞ log t/(t+z)² dt = log z/z` on the slit plane. -/
private lemma integral_log_mul_inv_add_sq {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * (((t : ℂ) + z) ^ 2)⁻¹ = Complex.log z / z := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  set F : ℝ → ℂ := fun t => ((t * Real.log t : ℝ) : ℂ) / (z * ((t : ℂ) + z)) -
      Complex.log ((t : ℂ) + z) / z
  have hne : ∀ t : ℝ, 0 ≤ t → (t : ℂ) + z ≠ 0 := fun t ht =>
    Complex.slitPlane_ne_zero (ofReal_add_mem_slitPlane hz ht)
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun t : ℝ => ((t * Real.log t : ℝ) : ℂ)) 0 :=
      (Complex.continuous_ofReal.comp Real.continuous_mul_log).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => z * ((t : ℂ) + z)) 0 := by fun_prop
    have h3 : ContinuousAt (fun t : ℝ => Complex.log ((t : ℂ) + z)) 0 := by
      refine (continuousAt_clog ?_).comp (by fun_prop)
      simpa using hz
    exact (h1.div h2 (mul_ne_zero hz0 (by simpa using hne 0 le_rfl))).sub (h3.div_const z)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F
      ((Real.log t : ℂ) * (((t : ℂ) + z) ^ 2)⁻¹) t := by
    intro t (ht : 0 < t)
    have htz := hne t ht.le
    have h1 : HasDerivAt (fun t : ℝ => ((t * Real.log t : ℝ) : ℂ))
        ((Real.log t + 1 : ℝ) : ℂ) t := (Real.hasDerivAt_mul_log ht.ne').ofReal_comp
    have h2 : HasDerivAt (fun t : ℝ => z * ((t : ℂ) + z)) z t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).add_const z).const_mul z
      simpa using this
    have h3 : HasDerivAt (fun t : ℝ => Complex.log ((t : ℂ) + z)) (1 / ((t : ℂ) + z)) t := by
      have := (Complex.ofRealCLM.hasDerivAt (x := t)).add_const z
      have h := this.clog_real (ofReal_add_mem_slitPlane hz ht.le)
      simpa using h
    have h4 := (h1.div h2 (mul_ne_zero hz0 htz)).sub (h3.div_const z)
    convert h4 using 1
    push_cast
    field_simp
    ring
  have hlim := tendsto_logPrimitive_atTop hz
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_log_mul_inv_add_pow hz le_rfl) hlim]
  simp [F]

/-- The parameter derivative of `∫₀^∞ log t (t+z)^{-s-2} dt`. -/
private lemma hasDerivAt_integral_log_mul_inv_add_pow {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (s : ℕ) :
    HasDerivAt (fun w => ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * (((t : ℂ) + w) ^ (s + 2))⁻¹)
      (-((s : ℂ) + 2) * ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * (((t : ℂ) + z) ^ (s + 3))⁻¹)
      z := by
  have hne : ∀ y ∈ Complex.slitPlane, ∀ t : ℝ, 0 ≤ t → (t : ℂ) + y ≠ 0 := fun y hy t ht =>
    Complex.slitPlane_ne_zero (ofReal_add_mem_slitPlane hy ht)
  have h := Complex.hasDerivAt_integral_of_locally_dominated (μ := volume.restrict (Ioi (0 : ℝ)))
    (Φ := fun w (t : ℝ) => (Real.log t : ℂ) * (((t : ℂ) + w) ^ (s + 2))⁻¹)
    Complex.isOpen_slitPlane (fun y hy => ?_) ?_ (fun y hy => ?_) hz
  · convert h using 1
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have htz := hne z hz t ht.le
    have hd : HasDerivAt (fun w : ℂ => (Real.log t : ℂ) * (((t : ℂ) + w) ^ (s + 2))⁻¹)
        ((Real.log t : ℂ) * (-(((s + 2 : ℕ) : ℂ) * ((t : ℂ) + z) ^ (s + 1)) /
          (((t : ℂ) + z) ^ (s + 2)) ^ 2)) z := by
      refine HasDerivAt.const_mul _ ?_
      have hp : HasDerivAt (fun w : ℂ => ((t : ℂ) + w) ^ (s + 2))
          (((s + 2 : ℕ) : ℂ) * ((t : ℂ) + z) ^ (s + 1)) z := by
        have := (hasDerivAt_pow (s + 2) ((t : ℂ) + z)).comp z
          ((hasDerivAt_id z).const_add (t : ℂ))
        exact this.congr_deriv (by rw [mul_one, show s + 2 - 1 = s + 1 by omega])
      exact hp.inv (pow_ne_zero _ htz)
    rw [hd.deriv]
    push_cast
    field_simp
    ring
  · exact (by fun_prop : Measurable fun t : ℝ => (Real.log t : ℂ) *
      (((t : ℂ) + y) ^ (s + 2))⁻¹).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht y hy => ?_)
    exact ((differentiableAt_const _).mul ((by fun_prop : DifferentiableAt ℂ
      (fun y : ℂ => ((t : ℂ) + y) ^ (s + 2)) y).inv
      (pow_ne_zero _ (hne y hy t (le_of_lt ht))))).differentiableWithinAt
  · obtain ⟨κ, hκ, hκt⟩ := exists_mul_one_add_le_norm_ofReal_add hy
    refine ⟨Metric.ball y (κ / 2), Metric.ball_mem_nhds _ (by positivity),
      fun t => (2 / κ) ^ (s + 2) * (|Real.log t| / (1 + t) ^ 2),
      integrableOn_abs_log_div_one_add_sq.const_mul _, ?_⟩
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
      fun t (ht : 0 < t) w hw => ?_)
    have hw' : ‖w - y‖ < κ / 2 := by simpa [dist_eq_norm] using hw
    have hlow : κ / 2 * (1 + t) ≤ ‖(t : ℂ) + w‖ := by
      have h1 := hκt t ht.le
      have h2 : ‖(t : ℂ) + y‖ ≤ ‖(t : ℂ) + w‖ + ‖w - y‖ := by
        calc ‖(t : ℂ) + y‖ = ‖((t : ℂ) + w) - (w - y)‖ := by ring_nf
          _ ≤ _ := norm_sub_le _ _
      nlinarith
    have hpos : 0 < κ / 2 * (1 + t) := by positivity
    simp only
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hp : (κ / 2 * (1 + t)) ^ (s + 2) ≤ ‖(t : ℂ) + w‖ ^ (s + 2) :=
      pow_le_pow_left₀ hpos.le hlow _
    have hq : (1 + t) ^ 2 ≤ (1 + t) ^ (s + 2) := pow_le_pow_right₀ (by linarith) (by omega)
    calc |Real.log t| * (‖(t : ℂ) + w‖ ^ (s + 2))⁻¹
        ≤ |Real.log t| * ((κ / 2 * (1 + t)) ^ (s + 2))⁻¹ := by gcongr
      _ = (2 / κ) ^ (s + 2) * (|Real.log t| / (1 + t) ^ (s + 2)) := by
          rw [mul_pow, div_pow, div_pow]; field_simp
      _ ≤ (2 / κ) ^ (s + 2) * (|Real.log t| / (1 + t) ^ 2) := by gcongr

/-- The closed form of `∫₀^∞ log t (t+z)^{-s-2} dt`. -/
private noncomputable def logIntegralClosedForm (s : ℕ) (z : ℂ) : ℂ :=
  (z ^ (s + 1))⁻¹ * (Complex.log z - (harmonic s : ℂ)) / ((s : ℂ) + 1)

/-- The closed forms satisfy `Φ_s' = -(s+2) Φ_{s+1}`, as the integrals do. -/
private lemma hasDerivAt_logIntegralClosedForm {z : ℂ} (hz : z ∈ Complex.slitPlane) (s : ℕ) :
    HasDerivAt (logIntegralClosedForm s) (-((s : ℂ) + 2) * logIntegralClosedForm (s + 1) z) z := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hp : HasDerivAt (fun w : ℂ => w ^ (s + 1)) (((s + 1 : ℕ) : ℂ) * z ^ s) z := by
    simpa using hasDerivAt_pow (s + 1) z
  have h1 : HasDerivAt (fun w : ℂ => (w ^ (s + 1))⁻¹)
      (-(((s + 1 : ℕ) : ℂ) * z ^ s) / (z ^ (s + 1)) ^ 2) z := hp.inv (pow_ne_zero _ hz0)
  have h2 : HasDerivAt (fun w : ℂ => Complex.log w - (harmonic s : ℂ)) z⁻¹ z := by
    simpa using ((hasDerivAt_id z).clog hz).sub_const (harmonic s : ℂ)
  have h3 : HasDerivAt (fun w : ℂ => (w ^ (s + 1))⁻¹ * (Complex.log w - (harmonic s : ℂ)) /
      ((s : ℂ) + 1)) ((-(((s + 1 : ℕ) : ℂ) * z ^ s) / (z ^ (s + 1)) ^ 2 *
        (Complex.log z - (harmonic s : ℂ)) + (z ^ (s + 1))⁻¹ * z⁻¹) / ((s : ℂ) + 1)) z :=
    (h1.mul h2).div_const _
  unfold logIntegralClosedForm
  refine h3.congr_deriv ?_
  have hs1 : (s : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  have hs2 : (s : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (s + 1)
  rw [harmonic_succ]
  push_cast
  field_simp
  ring

/-- `∫₀^∞ log t (t+z)^{-s-2} dt = z^{-s-1}(log z - H_s)/(s+1)` on the slit plane. -/
private lemma integral_log_mul_inv_add_pow {z : ℂ} (hz : z ∈ Complex.slitPlane) (s : ℕ) :
    ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * (((t : ℂ) + z) ^ (s + 2))⁻¹ =
      logIntegralClosedForm s z := by
  induction s generalizing z with
  | zero =>
    rw [integral_log_mul_inv_add_sq hz, logIntegralClosedForm]
    simp [div_eq_mul_inv, mul_comm]
  | succ s ih =>
    have hev : (fun w => ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * (((t : ℂ) + w) ^ (s + 2))⁻¹)
        =ᶠ[𝓝 z] logIntegralClosedForm s :=
      Filter.eventually_of_mem (Complex.isOpen_slitPlane.mem_nhds hz) fun w hw => ih hw
    have h1 := (hasDerivAt_integral_log_mul_inv_add_pow hz s).congr_of_eventuallyEq hev.symm
    have h2 := hasDerivAt_logIntegralClosedForm hz s
    have heq := h1.unique h2
    have hs2 : -((s : ℂ) + 2) ≠ 0 := neg_ne_zero.2 (by exact_mod_cast Nat.succ_ne_zero (s + 1))
    exact mul_left_cancel₀ hs2 heq

/-- `ε^i e^{-εt} ≤ 2/(1+t)` for `0 < ε ≤ 1`, `t ≥ 0`, `i ≥ 1`. -/
private lemma pow_mul_exp_neg_le {ε t : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) {i : ℕ}
    (hi : 1 ≤ i) : ε ^ i * Real.exp (-(ε * t)) ≤ 2 / (1 + t) := by
  have hεi : ε ^ i ≤ ε := by
    calc ε ^ i ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le hε1 hi
      _ = ε := pow_one ε
  have he := Real.add_one_le_exp (ε * t)
  have hpos := Real.exp_pos (ε * t)
  have hexp : Real.exp (-(ε * t)) = (Real.exp (ε * t))⁻¹ := Real.exp_neg _
  rw [le_div_iff₀ (by linarith), hexp]
  have h1 : ε ^ i * (Real.exp (ε * t))⁻¹ * (1 + t) ≤ ε * (Real.exp (ε * t))⁻¹ * (1 + t) := by
    gcongr
  refine h1.trans ?_
  rw [show ε * (Real.exp (ε * t))⁻¹ * (1 + t) = (ε + ε * t) / Real.exp (ε * t) by ring,
    div_le_iff₀ hpos]
  have : 1 ≤ Real.exp (ε * t) := by nlinarith [mul_nonneg hε0.le ht]
  nlinarith

/-- One term of the Leibniz expansion of `φ_ε^{(s+1)}` is `O(1/(1+t)²)` uniformly in
`0 < ε ≤ 1`. -/
private lemma norm_leibnizTerm_le {ε t κ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t)
    (hκ : 0 < κ) {z : ℂ} (hκt : κ * (1 + t) ≤ ‖(t : ℂ) + z‖) {i m : ℕ} (hm : 1 ≤ m)
    (him : i = 0 → 2 ≤ m) :
    ‖(-(ε : ℂ)) ^ i * Complex.exp (-(ε : ℂ) * t)‖ * ‖(((t : ℂ) + z) ^ m)⁻¹‖ ≤
      2 * (1 / κ) ^ m / (1 + t) ^ 2 := by
  have hpos : 0 < κ * (1 + t) := by positivity
  have hinv : ‖(((t : ℂ) + z) ^ m)⁻¹‖ ≤ (1 / κ) ^ m / (1 + t) ^ m := by
    rw [norm_inv, norm_pow, div_pow, one_pow, div_div, ← mul_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hκt m) |>.trans_eq (by simp)
  have hnorm : ‖(-(ε : ℂ)) ^ i * Complex.exp (-(ε : ℂ) * t)‖ = ε ^ i * Real.exp (-(ε * t)) := by
    rw [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hε0.le,
      Complex.norm_exp]
    congr 2
    simp
  rw [hnorm]
  have h1t : 1 ≤ 1 + t := by linarith
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hm2 := him rfl
    have he : Real.exp (-(ε * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hq : (1 + t) ^ 2 ≤ (1 + t) ^ m := pow_le_pow_right₀ h1t hm2
    calc ε ^ 0 * Real.exp (-(ε * t)) * ‖(((t : ℂ) + z) ^ m)⁻¹‖
        ≤ 1 * ((1 / κ) ^ m / (1 + t) ^ m) := by
          rw [pow_zero, one_mul]; gcongr
      _ ≤ 1 * ((1 / κ) ^ m / (1 + t) ^ 2) := by gcongr
      _ ≤ _ := by
          rw [one_mul, mul_div_assoc]
          have : 0 ≤ (1 / κ) ^ m / (1 + t) ^ 2 := by positivity
          linarith
  · have he := pow_mul_exp_neg_le hε0 hε1 ht hi
    have hq : (1 + t) ^ 1 ≤ (1 + t) ^ m := pow_le_pow_right₀ h1t hm
    calc ε ^ i * Real.exp (-(ε * t)) * ‖(((t : ℂ) + z) ^ m)⁻¹‖
        ≤ 2 / (1 + t) * ((1 / κ) ^ m / (1 + t) ^ m) := by gcongr
      _ ≤ 2 / (1 + t) * ((1 / κ) ^ m / (1 + t) ^ 1) := by gcongr
      _ = _ := by field_simp

/-- DLMF 2.6.24: for `z ∉ (-∞, 0]` and `s = 0, 1, 2, …`,
`lim_{ε → 0+} ⟨t^{-s-1}, φ_ε⟩ = (-1)^{s+1} z^{-s-1} ∑_{k=1}^{s} 1/k + (-1)^s z^{-s-1} ln z`. -/
@[dlmf 2.6.E24]
theorem tendsto_logPowPairing_stieltjesTestFunction {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (s : ℕ) :
    Tendsto (fun ε : ℝ => logPowPairing s (stieltjesTestFunction ε z)) (𝓝[>] 0)
      (𝓝 ((-1 : ℂ) ^ (s + 1) / z ^ (s + 1) * (harmonic s : ℂ) +
        (-1 : ℂ) ^ s / z ^ (s + 1) * Complex.log z)) := by
  obtain ⟨κ, hκ, hκt⟩ := exists_mul_one_add_le_norm_ofReal_add hz
  have hne : ∀ t : ℝ, 0 ≤ t → (t : ℂ) + z ≠ 0 := fun t ht =>
    Complex.slitPlane_ne_zero (ofReal_add_mem_slitPlane hz ht)
  set n := s + 1 with hn
  set D : ℝ → ℝ → ℂ := fun ε t => ∑ i ∈ range (n + 1),
    (n.choose i : ℂ) * ((-(ε : ℂ)) ^ i * Complex.exp (-(ε : ℂ) * t)) *
      ((-1) ^ (n - i) * ((n - i)! : ℂ) * (((t : ℂ) + z) ^ (n - i + 1))⁻¹) with hD
  have hform : ∀ ε : ℝ, ∀ t : ℝ, 0 ≤ t →
      iteratedDeriv n (stieltjesTestFunction ε z) t = D ε t := by
    intro ε t ht
    rw [iteratedDeriv_stieltjesTestFunction ε n (hne t ht)]
    refine sum_congr rfl fun i _ => ?_
    rw [show (-1 - ((n - i : ℕ) : ℤ)) = -((n - i + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast]
  have hpair : ∀ ε : ℝ, logPowPairing s (stieltjesTestFunction ε z) =
      -((s ! : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * D ε t) := by
    intro ε
    unfold logPowPairing
    congr 2
    exact setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => by rw [hform ε t ht.le]
  simp_rw [hpair]
  set L : ℝ → ℂ := fun t => (-1) ^ n * (n ! : ℂ) * (((t : ℂ) + z) ^ (n + 1))⁻¹
  have hD0 : ∀ t : ℝ, D 0 t = L t := by
    intro t
    simp only [hD, L]
    rw [sum_eq_single 0]
    · simp
    · intro i _ hi
      simp [zero_pow hi]
    · intro h; simp at h
  set K : ℝ := ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (n - i)! * (2 * (1 / κ) ^ (n - i + 1))
  have hlim : Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * D ε t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * L t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => K * (|Real.log t| / (1 + t) ^ 2)) ?_ ?_
      (integrableOn_abs_log_div_one_add_sq.const_mul _) ?_
    · exact Eventually.of_forall fun ε => (by fun_prop : Measurable fun t : ℝ =>
        (Real.log t : ℂ) * D ε t).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
        fun t (ht : 0 < t) => ?_)
      have htz := hκt t ht.le
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hDb : ‖D ε t‖ ≤ K / (1 + t) ^ 2 := by
        refine (norm_sum_le _ _).trans ?_
        rw [show K / (1 + t) ^ 2 = ∑ i ∈ range (n + 1),
            (n.choose i : ℝ) * (n - i)! * (2 * (1 / κ) ^ (n - i + 1) / (1 + t) ^ 2) by
          simp only [K, sum_div, mul_div_assoc]]
        refine sum_le_sum fun i hi => ?_
        have hb := norm_leibnizTerm_le hε.1 hε.2 ht.le hκ htz (i := i) (m := n - i + 1)
          le_add_self (fun h => by subst h; omega)
        calc ‖(n.choose i : ℂ) * ((-(ε : ℂ)) ^ i * Complex.exp (-(ε : ℂ) * t)) *
              ((-1) ^ (n - i) * ((n - i)! : ℂ) * (((t : ℂ) + z) ^ (n - i + 1))⁻¹)‖
            = (n.choose i : ℝ) * (n - i)! * (‖(-(ε : ℂ)) ^ i * Complex.exp (-(ε : ℂ) * t)‖ *
              ‖(((t : ℂ) + z) ^ (n - i + 1))⁻¹‖) := by
              simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
                Complex.norm_natCast]
              ring
          _ ≤ _ := by gcongr
      calc |Real.log t| * ‖D ε t‖ ≤ |Real.log t| * (K / (1 + t) ^ 2) := by gcongr
        _ = _ := by ring
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
        fun t (ht : 0 < t) => ?_)
      rw [← hD0]
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine Continuous.tendsto' ?_ 0 _ rfl
      fun_prop
  have hint : ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * L t =
      (-1) ^ n * (n ! : ℂ) * ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) *
        (((t : ℂ) + z) ^ (s + 2))⁻¹ := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp only [L, hn]; ring
  rw [hint, integral_log_mul_inv_add_pow hz s] at hlim
  convert (hlim.const_mul (s ! : ℂ)⁻¹).neg using 2
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hfact : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero s)
  have hs1 : (s : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  simp only [logIntegralClosedForm, hn, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- DLMF 2.6.25: `lim_{ε → 0+} ⟨f, φ_ε⟩ = 𝒮f(z)` whenever `f(t)/(t+z)` is integrable on
`(0, ∞)` (dominated convergence). This is stronger than DLMF, which assumes `z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 2.6.E25]
theorem tendsto_functionPairing_stieltjesTestFunction' {f : ℝ → ℂ} {z : ℂ}
    (hf : IntegrableOn (fun t : ℝ => f t / ((t : ℂ) + z)) (Ioi 0)) :
    Tendsto (fun ε : ℝ => functionPairing f (stieltjesTestFunction ε z)) (𝓝[>] 0)
      (𝓝 (AlgebraicAnalytic.stieltjesTransform f z)) := by
  rw [stieltjesTransform_eq]
  unfold functionPairing stieltjesTestFunction
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t / ((t : ℂ) + z)‖)
    ?_ ?_ hf.norm ?_
  · refine Eventually.of_forall fun ε => ?_
    have hm : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(ε * t : ℂ)))
        (volume.restrict (Ioi 0)) := by fun_prop
    refine (hf.aestronglyMeasurable.mul hm).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]
    ring
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [mul_div_assoc', norm_div, norm_mul, norm_div]
    have he : ‖Complex.exp (-(ε * t : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, Real.exp_le_one_iff, Left.neg_nonpos_iff]
      positivity
    have : 0 ≤ ‖f t‖ / ‖(t : ℂ) + z‖ := by positivity
    calc ‖f t‖ * ‖Complex.exp (-(ε * t : ℂ))‖ / ‖(t : ℂ) + z‖
        = ‖f t‖ / ‖(t : ℂ) + z‖ * ‖Complex.exp (-(ε * t : ℂ))‖ := by ring
      _ ≤ ‖f t‖ / ‖(t : ℂ) + z‖ * 1 := by gcongr
      _ = _ := mul_one _
  · refine Eventually.of_forall fun t => ?_
    have hc : Continuous fun ε : ℝ => f t * (Complex.exp (-(ε * t : ℂ)) / ((t : ℂ) + z)) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [mul_div_assoc', div_eq_mul_inv] using this

/-- DLMF 2.6.25: `lim_{ε → 0+} ⟨f, φ_ε⟩ = 𝒮f(z)` whenever `f(t)/(t+z)` is integrable on
`(0, ∞)` (dominated convergence). -/
@[dlmf 2.6.E25]
theorem tendsto_functionPairing_stieltjesTestFunction {f : ℝ → ℂ} {z : ℂ}
    (_hz : z ∈ Complex.slitPlane)
    (hf : IntegrableOn (fun t : ℝ => f t / ((t : ℂ) + z)) (Ioi 0)) :
    Tendsto (fun ε : ℝ => functionPairing f (stieltjesTestFunction ε z)) (𝓝[>] 0)
      (𝓝 (AlgebraicAnalytic.stieltjesTransform f z)) :=
  tendsto_functionPairing_stieltjesTestFunction' hf

/-- DLMF 2.6.26 and the display following it: under the hypotheses of §2.6(ii),
`lim_{ε → 0+} ⟨f_n, φ_ε⟩ = n! ∫₀^∞ f_{n,n}(t)/(t+z)^{n+1} dt`, and interchanging the order of
integration this equals `(-1)ⁿ z⁻ⁿ ∫₀^∞ τⁿ f_n(τ)/(τ+z) dτ = R_n(z)` (2.6.30). -/
@[dlmf 2.6.E26]
theorem tendsto_remainderPairing_stieltjesTestFunction {f : ℝ → ℂ} {α : ℝ} {a : ℕ → ℂ}
    (hf : IsStieltjesExpansion f α a) {z : ℂ} (hz : z ∈ Complex.slitPlane) {n : ℕ}
    (hn : 1 ≤ n) :
    Tendsto (fun ε : ℝ => remainderPairing n (stieltjesRemainder f α a n)
        (stieltjesTestFunction ε z)) (𝓝[>] 0)
      (𝓝 ((n ! : ℂ) * ∫ t in Ioi (0 : ℝ),
        repeatedTailIntegral n (stieltjesRemainder f α a n) t / ((t : ℂ) + z) ^ (n + 1))) ∧
    (n ! : ℂ) * ∫ t in Ioi (0 : ℝ),
        repeatedTailIntegral n (stieltjesRemainder f α a n) t / ((t : ℂ) + z) ^ (n + 1) =
      stieltjesRemainderTerm (stieltjesRemainder f α a n) n z := by
  sorry

/-- DLMF 2.6.27 (with 2.6.18 and 2.6.30): for `0 < α < 1`, `n ≥ 1` and `z ∉ (-∞, 0]`,
`𝒮f(z) = π/sin(πα) ∑_{s<n} (-1)^s a_s z^{-s-α} - ∑_{s=1}^{n} (s-1)! c_s z^{-s} + R_n(z)`,
an exact identity with the remainder `R_n(z) = (-1)ⁿ z⁻ⁿ ∫₀^∞ τⁿ f_n(τ)/(τ+z) dτ`. -/
@[dlmf 2.6.E27, dlmf 2.6.E30]
theorem stieltjesTransform_eq_of_lt_one {f : ℝ → ℂ} {α : ℝ} {a : ℕ → ℂ}
    (hf : IsStieltjesExpansion f α a) (hα : α < 1) {M : ℂ → ℂ} (hM : IsMellinContinuation f α M)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AlgebraicAnalytic.stieltjesTransform f z =
      π / Real.sin (π * α) * ∑ s ∈ range n, (-1 : ℂ) ^ s * a s / z ^ ((s : ℂ) + α) -
        ∑ s ∈ Icc 1 n, ((s - 1)! : ℂ) * stieltjesDeltaCoeff M s / z ^ s +
        stieltjesRemainderTerm (stieltjesRemainder f α a n) n z := by
  sorry

/-- DLMF 2.6.28 (with 2.6.29 and 2.6.30): for `α = 1`, `n ≥ 1` and `z ∉ (-∞, 0]`,
`𝒮f(z) = ln z ∑_{s<n} (-1)^s a_s z^{-s-1} + ∑_{s<n} (-1)^s d̃_s z^{-s-1} + R_n(z)`. -/
@[dlmf 2.6.E28, dlmf 2.6.E29]
theorem stieltjesTransform_eq_of_eq_one {f : ℝ → ℂ} {a : ℕ → ℂ}
    (hf : IsStieltjesExpansion f 1 a) {M : ℂ → ℂ} (hM : IsMellinContinuation f 1 M)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AlgebraicAnalytic.stieltjesTransform f z =
      Complex.log z * ∑ s ∈ range n, (-1 : ℂ) ^ s * a s / z ^ (s + 1) +
        ∑ s ∈ range n, (-1 : ℂ) ^ s * stieltjesLogCoeff M a s / z ^ (s + 1) +
        stieltjesRemainderTerm (stieltjesRemainder f 1 a n) n z := by
  sorry

end DLMF.AsymptoticApproximations
