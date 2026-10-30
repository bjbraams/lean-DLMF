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

/-!
# Divergent integrals and the Stieltjes transform (DLMF §2.6(i)–(ii))

* §2.6(i): the integral `S(x) = ∫₀^∞ (1+t)^{-1/3}/(x+t) dt` (2.6.1), the binomial expansion
  2.6.2, the divergence of the termwise integrals 2.6.3, the Beta integral 2.6.4 and its
  generalized value 2.6.5, the failure of the naive expansion 2.6.6 and the correct
  expansion 2.6.7.
* §2.6(ii): the distributional identities 2.6.17 (`0 < α < 1`) and 2.6.20 (`α = 1`), the
  limits 2.6.23–2.6.26 for the test functions `φ_ε` of 2.6.22, and the expansions with exact
  remainder 2.6.27–2.6.30 of the Stieltjes transform.

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
    DLMF.Gamma.beta_on_Ioi hα hβ] at hsub
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
theorem gamma_two_thirds_sub_mul_gamma (s : ℕ) {x : ℝ} (_hx : 0 < x) :
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

/-- DLMF 2.6.7: the correct asymptotic expansion of `S(x)` as `x → +∞`,
`S(x) ∼ (2π/√3) ∑ (-1)^s (-1/3 choose s) x^{-s-1/3} - ∑_{s≥1} 3^s (s-1)!/(2·5⋯(3s-1)) x^{-s}`,
in the form: for every `n`, the remainder after the terms with `s < n` in the first sum and
`s ≤ n` in the second is `O(x^{-n-1/3})`. (DLMF also states validity for complex `x` with
`|ph x| ≤ π - δ`; the real case is formalized.) -/
@[dlmf 2.6.E7, dlmf 2.6.E1]
theorem stieltjesCubeRootExample_expansion (n : ℕ) :
    (fun x : ℝ => stieltjesCubeRootExample x - ((g2b_naiveSum n x - g2b_missingSum n x : ℝ) : ℂ))
      =O[atTop] (fun x : ℝ => x ^ (-(n : ℝ) - 1 / 3)) := by
  sorry

/-- DLMF 2.6.6 is incorrect: the formal termwise expansion
`S(x) ∼ (2π/√3) ∑ (-1)^s (-1/3 choose s) x^{-s-1/3}` does not hold; already with two terms
the remainder is not `O(x^{-4/3})` (the missing term `-(3/2) x^{-1}` of 2.6.7 dominates). -/
@[dlmf 2.6.E6]
theorem not_stieltjesCubeRootExample_naive :
    ¬ (fun x : ℝ => stieltjesCubeRootExample x - ((g2b_naiveSum 2 x : ℝ) : ℂ))
      =O[atTop] (fun x : ℝ => x ^ (-(1 : ℝ) - 1 / 3)) := by
  sorry

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

/-- DLMF 2.6.23: for `0 < α < 1`, `z ∉ (-∞, 0]` and `s = 0, 1, 2, …`,
`lim_{ε → 0+} ⟨t^{-s-α}, φ_ε⟩ = π/sin(πα) · (-1)^s / z^{s+α}` (principal power). -/
@[dlmf 2.6.E23]
theorem tendsto_powPairing_stieltjesTestFunction {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {z : ℂ} (hz : z ∈ Complex.slitPlane) (s : ℕ) :
    Tendsto (fun ε : ℝ => powPairing α s (stieltjesTestFunction ε z)) (𝓝[>] 0)
      (𝓝 (π / Real.sin (π * α) * (-1 : ℂ) ^ s / z ^ ((s : ℂ) + α))) := by
  sorry

/-- DLMF 2.6.24: for `z ∉ (-∞, 0]` and `s = 0, 1, 2, …`,
`lim_{ε → 0+} ⟨t^{-s-1}, φ_ε⟩ = (-1)^{s+1} z^{-s-1} ∑_{k=1}^{s} 1/k + (-1)^s z^{-s-1} ln z`. -/
@[dlmf 2.6.E24]
theorem tendsto_logPowPairing_stieltjesTestFunction {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (s : ℕ) :
    Tendsto (fun ε : ℝ => logPowPairing s (stieltjesTestFunction ε z)) (𝓝[>] 0)
      (𝓝 ((-1 : ℂ) ^ (s + 1) / z ^ (s + 1) * (harmonic s : ℂ) +
        (-1 : ℂ) ^ s / z ^ (s + 1) * Complex.log z)) := by
  sorry

/-- DLMF 2.6.25: `lim_{ε → 0+} ⟨f, φ_ε⟩ = 𝒮f(z)` whenever `f(t)/(t+z)` is integrable on
`(0, ∞)` (dominated convergence). -/
@[dlmf 2.6.E25]
theorem tendsto_functionPairing_stieltjesTestFunction {f : ℝ → ℂ} {z : ℂ}
    (hz : z ∈ Complex.slitPlane)
    (hf : IntegrableOn (fun t : ℝ => f t / ((t : ℂ) + z)) (Ioi 0)) :
    Tendsto (fun ε : ℝ => functionPairing f (stieltjesTestFunction ε z)) (𝓝[>] 0)
      (𝓝 (stieltjesTransform f z)) := by
  sorry

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
    stieltjesTransform f z =
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
    stieltjesTransform f z =
      Complex.log z * ∑ s ∈ range n, (-1 : ℂ) ^ s * a s / z ^ (s + 1) +
        ∑ s ∈ range n, (-1 : ℂ) ^ s * stieltjesLogCoeff M a s / z ^ (s + 1) +
        stieltjesRemainderTerm (stieltjesRemainder f 1 a n) n z := by
  sorry

end DLMF.AsymptoticApproximations
