/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Remainders.Basic
public import DLMF.AsymptoticApproximations.ODE.Basic
public import DLMF.ExpIntegrals.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Remainder terms; Stokes phenomenon

This file covers DLMF §2.11: the example `I(m) = ∫_0^π cos(mt)/(t²+1) dt`, the generalized
exponential integral `E_p(z)` (`DLMF.Confluent.genExpIntE`, on the logarithmic plane
`genExpIntEOnLog`), exponentially improved expansions with the terminant
`F_{n+p}(z) = Γ(n+p)/(2π) E_{n+p}(z)/z^{n+p-1}`, and re-expansion in terminants.

## Main results

* `cosRationalIntegral_asymptotic`, `cosRationalCoeff_explicit`: the asymptotic expansion of
  `I(m)` and its first coefficients (DLMF 2.11.1–2.11.3).
* `genExpIntE_eq_integral`, `genExpIntE_asymptotic`, `genExpIntE_compound_asymptotic`: the
  Stieltjes representation, Poincaré expansion and compound expansion of `E_p(z)`
  (DLMF 2.11.5–2.11.7; corollaries of DLMF 8.19.4, 8.20.2 and 8.20.3).
* `genExpIntE_eq_sum_add_terminant`, `terminant_eq_integral`, `terminant_eq_saddle_integral`:
  the expansion with terminant remainder and the integral forms of the terminant
  (DLMF 2.11.8–2.11.12).
* `terminant_reexpansions`: re-expansion of the terminant (DLMF 2.11.13–2.11.15, 2.11.17).
* `stokesC_sq`, `stokesC_continuous_tendsto`, `stokesH_zero`, `stokesC_re_sign`: properties of
  `c(θ)` and `h₀` (DLMF 2.11.16, 2.11.18, §2.11(iv)).
* `rankOne_terminant_reexpansion`: re-expansion of the remainders of the rank-one formal
  solutions 2.7.14 in terminants, on the logarithmic plane `z = e^ζ` with `λ₂ - λ₁ = 1`
  (DLMF 2.11.19–2.11.23).
* `expIntE1_asymptotic`: DLMF 2.11.24 (from DLMF 6.12.1).
* `whittakerW_asymptotic`: the Whittaker expansion for real `x → +∞` (DLMF 2.11.29–2.11.30,
  from DLMF 13.19.3).

## Implementation notes

Excluded as numerical: DLMF 2.11.4, 2.11.25–2.11.28, 2.11.31 and Table 2.11.1.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics MeasureTheory Complex
open scoped Topology Real Nat

namespace DLMF.AsymptoticApproximations

open DLMF.Confluent DLMF.Hypergeometric

/-! ### §2.11(i) Numerical use of asymptotic expansions -/

/-- DLMF 2.11.1–2.11.2: as the integer `m → ∞`, `I(m) ∼ (-1)^m ∑_{s ≥ 1} q_s(π)/m^{2s}`
(scale `(-1)^m m^{-2s}`, `s = 0, 1, …`, with zero coefficient for `s = 0`). -/
@[dlmf 2.11.E1, dlmf 2.11.E2]
theorem cosRationalIntegral_asymptotic :
    HasAsymptoticExpansion atTop (fun (s m : ℕ) => ((-1 : ℝ) ^ m / (m : ℝ) ^ (2 * s)))
      (fun s => if s = 0 then 0 else cosRationalCoeff s π)
      (fun m : ℕ => cosRationalIntegral m) := by
  sorry

/-- DLMF 2.11.3: `q₁(t) = -2t/(t²+1)²`, `q₂(t) = 24(t³-t)/(t²+1)⁴`,
`q₃(t) = -240(3t⁵-10t³+3t)/(t²+1)⁶`. -/
@[dlmf 2.11.E3]
theorem cosRationalCoeff_explicit (t : ℝ) :
    cosRationalCoeff 1 t = -(2 * t) / (t ^ 2 + 1) ^ 2 ∧
      cosRationalCoeff 2 t = 24 * (t ^ 3 - t) / (t ^ 2 + 1) ^ 4 ∧
      cosRationalCoeff 3 t = -(240 * (3 * t ^ 5 - 10 * t ^ 3 + 3 * t)) / (t ^ 2 + 1) ^ 6 := by
  have hden (x : ℝ) : x ^ 2 + 1 ≠ 0 := by positivity
  have h₁ (x : ℝ) : HasDerivAt (fun t : ℝ => (t ^ 2 + 1)⁻¹)
      (-(2 * x) / (x ^ 2 + 1) ^ 2) x := by
    convert! (((hasDerivAt_id x).pow 2).add_const 1).inv (hden x) using 1 <;>
      simp only [id_eq, Pi.pow_apply, Pi.inv_apply] <;> ring
  have h₂ (x : ℝ) : HasDerivAt (fun t : ℝ => -(2 * t) / (t ^ 2 + 1) ^ 2)
      ((6 * x ^ 2 - 2) / (x ^ 2 + 1) ^ 3) x := by
    convert! (((hasDerivAt_id x).const_mul 2).neg).div
      ((((hasDerivAt_id x).pow 2).add_const 1).pow 2) (pow_ne_zero 2 (hden x)) using 1
    simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Pi.sub_apply]
    field_simp [hden x]
    ring
  have h₃ (x : ℝ) : HasDerivAt (fun t : ℝ => (6 * t ^ 2 - 2) / (t ^ 2 + 1) ^ 3)
      (-(24 * (x ^ 3 - x)) / (x ^ 2 + 1) ^ 4) x := by
    convert! ((((hasDerivAt_id x).pow 2).const_mul 6).sub_const 2).div
      ((((hasDerivAt_id x).pow 2).add_const 1).pow 3) (pow_ne_zero 3 (hden x)) using 1
    simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Pi.sub_apply]
    field_simp [hden x]
    ring
  have h₄ (x : ℝ) : HasDerivAt (fun t : ℝ => -(24 * (t ^ 3 - t)) / (t ^ 2 + 1) ^ 4)
      ((120 * x ^ 4 - 240 * x ^ 2 + 24) / (x ^ 2 + 1) ^ 5) x := by
    convert! (((((hasDerivAt_id x).pow 3).sub (hasDerivAt_id x)).const_mul 24).neg).div
      ((((hasDerivAt_id x).pow 2).add_const 1).pow 4) (pow_ne_zero 4 (hden x)) using 1
    simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Pi.sub_apply]
    field_simp [hden x]
    ring
  have h₅ (x : ℝ) : HasDerivAt
      (fun t : ℝ => (120 * t ^ 4 - 240 * t ^ 2 + 24) / (t ^ 2 + 1) ^ 5)
      (-(240 * (3 * x ^ 5 - 10 * x ^ 3 + 3 * x)) / (x ^ 2 + 1) ^ 6) x := by
    convert! (((((hasDerivAt_id x).pow 4).const_mul 120).sub
      (((hasDerivAt_id x).pow 2).const_mul 240)).add_const 24).div
      ((((hasDerivAt_id x).pow 2).add_const 1).pow 5) (pow_ne_zero 5 (hden x)) using 1
    simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Pi.sub_apply]
    field_simp [hden x]
    ring
  have hd₁ : deriv (fun t : ℝ => (t ^ 2 + 1)⁻¹) =
      fun t : ℝ => -(2 * t) / (t ^ 2 + 1) ^ 2 := funext fun x => (h₁ x).deriv
  have hd₂ : deriv (fun t : ℝ => -(2 * t) / (t ^ 2 + 1) ^ 2) =
      fun t : ℝ => (6 * t ^ 2 - 2) / (t ^ 2 + 1) ^ 3 := funext fun x => (h₂ x).deriv
  have hd₃ : deriv (fun t : ℝ => (6 * t ^ 2 - 2) / (t ^ 2 + 1) ^ 3) =
      fun t : ℝ => -(24 * (t ^ 3 - t)) / (t ^ 2 + 1) ^ 4 := funext fun x => (h₃ x).deriv
  have hd₄ : deriv (fun t : ℝ => -(24 * (t ^ 3 - t)) / (t ^ 2 + 1) ^ 4) =
      fun t : ℝ => (120 * t ^ 4 - 240 * t ^ 2 + 24) / (t ^ 2 + 1) ^ 5 :=
    funext fun x => (h₄ x).deriv
  simp only [cosRationalCoeff, one_div]
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, hd₁, hd₂, hd₃, hd₄, (h₅ t).deriv]
  norm_num
  ring

/-! ### §2.11(ii) Connection formulas -/

/-- DLMF 2.11.5: for `ℜp > 0` and `|ph z| < π/2`,
`E_p(z) = e^{-z} z^{p-1}/Γ(p) ∫_0^∞ e^{-zt} t^{p-1}/(1+t) dt`. Corollary of the project's
8.19.4. -/
@[dlmf 2.11.E5]
theorem genExpIntE_eq_integral {p z : ℂ} (hp : 0 < p.re) (hz : 0 < z.re) :
    genExpIntE p z = exp (-z) * z ^ (p - 1) / Gamma p *
      ∫ t : ℝ in Ioi 0, exp (-z * t) * (t : ℂ) ^ (p - 1) / (1 + t) := by
  rw [genExpIntE_stieltjes hp hz]
  have : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (p - 1) * exp (-z * t) / (1 + t)) =
      ∫ t : ℝ in Ioi 0, exp (-z * t) * (t : ℂ) ^ (p - 1) / (1 + t) := by
    congr 1; funext t; ring
  rw [this]
  ring

/-- DLMF 2.11.6: for fixed `p`, `E_p(z) ∼ e^{-z}/z ∑ (-1)^s (p)_s/z^s` as `z → ∞` in
`|ph z| ≤ 3π/2 - δ`, on the logarithmic plane (`z = e^w`). The project's 8.20.2. -/
@[dlmf 2.11.E6]
theorem genExpIntE_asymptotic (p : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3 * π / 2) :
    HasAsymptoticExpansion (logSector (3 * π / 2 - δ))
      (fun k w => exp (-exp w - (k + 1 : ℂ) * w)) (fun k => (-1 : ℂ) ^ k * poch p k)
      (genExpIntEOnLog p) :=
  genExpIntE_log_sector_asymptotic p hδ hδ1

/-- DLMF 2.11.7: `E_p(z) ∼ 2πi e^{-pπi}/Γ(p) z^{p-1} + e^{-z}/z ∑ (-1)^s (p)_s/z^s` as
`z → ∞` in `π/2 + δ ≤ ph z ≤ 7π/2 - δ`, on the logarithmic plane. The project's 8.20.3
(`ε = 1`). -/
@[dlmf 2.11.E7]
theorem genExpIntE_compound_asymptotic (p : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3 * π / 2) :
    HasAsymptoticExpansion
      (comap (fun w : ℂ => Real.exp w.re) atTop ⊓
        𝓟 {w : ℂ | π / 2 + δ ≤ (1 : ℝ) * w.im ∧ (1 : ℝ) * w.im ≤ 7 * π / 2 - δ})
      (fun k w => exp (-exp w - (k + 1 : ℂ) * w)) (fun k => (-1 : ℂ) ^ k * poch p k)
      (fun w => genExpIntEOnLog p w -
        ((1 : ℝ) : ℂ) * 2 * π * I / Gamma p * exp (-((1 : ℝ) : ℂ) * p * π * I + (p - 1) * w)) :=
  genExpIntE_extended_sector_asymptotic p (Or.inl rfl) hδ hδ1

/-! ### §2.11(iii) Exponentially improved expansions -/

/-- DLMF 2.11.9: `1/(1+t) = ∑_{s<n} (-1)^s t^s + (-1)^n tⁿ/(1+t)` for `t ≠ -1`. -/
@[dlmf 2.11.E9]
theorem inv_one_add_eq_sum {t : ℂ} (ht : 1 + t ≠ 0) (n : ℕ) :
    1 / (1 + t) = ∑ s ∈ Finset.range n, (-1) ^ s * t ^ s + (-1) ^ n * t ^ n / (1 + t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ]
    field_simp
    ring

/-- DLMF 2.11.10: for `ℜp > 0`, `z` in the cut plane and `n ≥ 0`,
`E_p(z) = e^{-z}/z ∑_{s<n} (-1)^s (p)_s/z^s + (-1)ⁿ 2π/Γ(p) z^{p-1} F_{n+p}(z)` with the
terminant `F_{n+p}(z) = Γ(n+p)/(2π) E_{n+p}(z)/z^{n+p-1}` (2.11.11). -/
@[dlmf 2.11.E10]
theorem genExpIntE_eq_sum_add_terminant {p z : ℂ} (hp : 0 < p.re) (hz : z ∈ slitPlane)
    (n : ℕ) :
    genExpIntE p z = exp (-z) / z * ∑ s ∈ Finset.range n, (-1) ^ s * poch p s / z ^ s +
      (-1) ^ n * (2 * π) / Gamma p * z ^ (p - 1) *
        (Gamma (n + p) / (2 * π) * genExpIntE (n + p) z / z ^ (n + p - 1)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have key : ∀ m : ℕ, genExpIntE p z = exp (-z) / z * ∑ s ∈ Finset.range m,
      (-1) ^ s * poch p s / z ^ s + (-1) ^ m * poch p m / z ^ m * genExpIntE (m + p) z := by
    intro m
    induction m with
    | zero => simp [poch_zero]
    | succ m ih =>
      have hr := genExpIntE_add_one ((m : ℂ) + p) hz0
      rw [ih, Finset.sum_range_succ, poch_succ]
      push_cast
      rw [show (m : ℂ) + 1 + p = (m : ℂ) + p + 1 by ring]
      field_simp
      linear_combination (-1) ^ m * poch p m * z * z ^ m * hr
  rw [key n]
  congr 1
  have hΓ : Gamma p ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hp
  have hG : Gamma ((n : ℂ) + p) = poch p n * Gamma p := by
    rw [add_comm]; exact Gamma_add_nat_eq_poch_mul_Gamma hp n
  have hzp : z ^ ((n : ℂ) + p - 1) = z ^ n * z ^ (p - 1) := by
    rw [show (n : ℂ) + p - 1 = (n : ℂ) + (p - 1) by ring, Complex.cpow_add _ _ hz0,
      Complex.cpow_natCast]
  have hz1 : z ^ (p - 1) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hG, hzp]
  field_simp

/-- DLMF 2.11.11: for `ℜ(n+p) > 0` and `ℜz > 0` the two forms of the terminant agree:
`F_{n+p}(z) = e^{-z}/(2π) ∫_0^∞ e^{-zt} t^{n+p-1}/(1+t) dt = Γ(n+p)/(2π) E_{n+p}(z)/z^{n+p-1}`.
Proved from the project's 8.19.4. -/
@[dlmf 2.11.E11]
theorem terminant_eq_integral {ν z : ℂ} (hν : 0 < ν.re) (hz : 0 < z.re) :
    Gamma ν / (2 * π) * genExpIntE ν z / z ^ (ν - 1) =
      exp (-z) / (2 * π) * ∫ t : ℝ in Ioi 0, exp (-z * t) * (t : ℂ) ^ (ν - 1) / (1 + t) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hzp : z ^ (ν - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hz0 h.1
  have hΓ : Gamma ν ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hν
  have hπ : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [genExpIntE_eq_integral hν hz]
  field_simp

/-- DLMF 2.11.12 (with 2.11.8): with `z = ρe^{iθ}` (`ρ`, `θ` real) and `n = ρ - p + α`,
`F_{n+p}(z) = e^{-z}/(2π) ∫_0^∞ exp(-ρ(te^{iθ} - ln t)) t^{α-1}/(1+t) dt`; here
`ℜ(n+p) > 0` and `ℜz > 0`. -/
@[dlmf 2.11.E12, dlmf 2.11.E8]
theorem terminant_eq_saddle_integral {p : ℂ} {n : ℕ} {ρ θ : ℝ}
    (hν : 0 < ((n : ℂ) + p).re) (hz : 0 < ((ρ : ℂ) * exp (I * θ)).re) :
    Gamma (n + p) / (2 * π) * genExpIntE (n + p) (ρ * exp (I * θ)) /
        (ρ * exp (I * θ)) ^ ((n : ℂ) + p - 1) =
      exp (-(ρ * exp (I * θ))) / (2 * π) * ∫ t : ℝ in Ioi 0,
        exp (-(ρ * (t * exp (I * θ) - Real.log t))) * (t : ℂ) ^ ((n - ρ + p : ℂ) - 1) /
          (1 + t) := by
  rw [terminant_eq_integral hν hz]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hsplit : (t : ℂ) ^ ((n : ℂ) + p - 1) =
      (t : ℂ) ^ (ρ : ℂ) * (t : ℂ) ^ ((n - ρ + p : ℂ) - 1) := by
    rw [← Complex.cpow_add _ _ ht0]; congr 1; ring
  have hρpow : (t : ℂ) ^ (ρ : ℂ) = exp (ρ * Real.log t) := by
    rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]; ring_nf
  rw [hsplit, hρpow, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- DLMF 2.11.13–2.11.15 and 2.11.17 (re-expansion of the terminant): fix `p`, `δ ∈ (0, π)` and
`A ≥ 0`. There are coefficients `a_{2s}(θ, α)` (here `a s θ α`) with `a₀ = 1` and `a₂` as in
2.11.14 such that, with `z = ρe^{iθ}`, `n = ρ - p + α` (2.11.8) and `|α| ≤ A`, as `ρ → ∞`:
(2.11.13) uniformly in `θ ∈ [-π+δ, π-δ]`,
`F_{n+p}(z) ∼ e^{-i(ρ+α)θ}/(1+e^{-iθ}) e^{-ρ-z}/(2πρ)^{1/2} ∑ a_{2s}(θ,α)/ρ^s`; and
(2.11.15) uniformly in `θ ∈ [-π+δ, 3π-δ]` (on the logarithmic plane, `w = ln ρ + iθ`),
`F_{n+p}(z) ∼ (-1)ⁿ i e^{-pπi} (½ erfc((ρ/2)^{1/2} c(θ))
  - i e^{iρ(π-θ)} e^{-ρ-z}/(2πρ)^{1/2} ∑ h_{2s}(θ,α)/ρ^s)` with `h_{2s}` from 2.11.17. -/
@[dlmf 2.11.E13, dlmf 2.11.E14, dlmf 2.11.E15, dlmf 2.11.E17, dlmf 2.11.iii]
theorem terminant_reexpansions (p : ℂ) {δ A : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (hA : 0 ≤ A) :
    ∃ a : ℕ → ℝ → ℂ → ℂ, (∀ θ α, a 0 θ α = 1) ∧ (∀ θ α, a 1 θ α = stokesA2 θ α) ∧
      ∀ N : ℕ, ∃ C ρ₀ : ℝ, ∀ (n : ℕ) (ρ θ : ℝ), ρ₀ ≤ ρ → ‖(n : ℂ) - ρ + p‖ ≤ A →
        let α : ℂ := n - ρ + p
        let w : ℂ := Real.log ρ + I * θ
        let z : ℂ := exp w
        let F : ℂ := Gamma (n + p) / (2 * π) * genExpIntEOnLog (n + p) w /
          exp (((n : ℂ) + p - 1) * w)
        let P : ℂ := exp (-(I * (ρ + α) * θ)) / (1 + exp (-(I * θ))) * exp (-ρ - z) /
          ((2 * π * ρ : ℝ) : ℂ) ^ (1 / 2 : ℂ)
        let Q : ℂ := exp (I * ρ * (π - θ)) * exp (-ρ - z) / ((2 * π * ρ : ℝ) : ℂ) ^ (1 / 2 : ℂ)
        (θ ∈ Icc (-π + δ) (π - δ) →
          ‖F - P * ∑ s ∈ Finset.range N, a s θ α / (ρ : ℂ) ^ s‖ ≤ C * ‖P‖ / ρ ^ N) ∧
        (θ ∈ Icc (-π + δ) (3 * π - δ) →
          ‖F - (-1) ^ n * I * exp (-(p * π * I)) *
              (1 / 2 * erfc (((ρ / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) * stokesC θ) -
                I * Q * ∑ s ∈ Finset.range N, stokesH a s θ α / (ρ : ℂ) ^ s)‖ ≤
            C * ‖Q‖ / ρ ^ N) := by
  sorry

/-- DLMF 2.11.16: `c(θ)² = 2(1 + e^{iθ} + i(θ - π))`. -/
@[dlmf 2.11.E16]
theorem stokesC_sq (θ : ℝ) : stokesC θ ^ 2 = 2 * (1 + exp (I * θ) + I * (θ - π)) := by
  by_cases hθ : θ = π
  · rw [hθ]
    have h1 : exp (I * (π : ℂ)) = -1 := by
      rw [show I * (π : ℂ) = (π : ℂ) * I by ring, Complex.exp_pi_mul_I]
    simp [stokesC, h1]
  · have h0 : ((π - θ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.2 (Ne.symm hθ)
    rw [stokesC, mul_pow, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num,
      Complex.cpow_nat_inv_pow _ (by norm_num)]
    field_simp

/-- The normalized square of the Stokes coordinate lies in the closed right half-plane. -/
lemma stokesQuotient_re_nonneg (θ : ℝ) :
    0 ≤ (2 * (1 + exp (I * θ) + I * (θ - π)) / ((π - θ : ℝ) : ℂ) ^ 2).re := by
  rw [← ofReal_pow, div_ofReal_re]
  have he : exp (I * θ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    rw [mul_comm I (θ : ℂ), exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hn : 0 ≤ (2 * (1 + exp (I * θ) + I * (θ - π))).re := by
    simp [he]
    change 0 ≤ 1 + Real.cos θ
    linarith [Real.neg_one_le_cos θ]
  exact div_nonneg hn (sq_nonneg _)

/-- The normalized square of the Stokes coordinate tends to one at the transition.
Uses `Complex.exp_sub_sum_range_succ_isLittleO_pow`, Mathlib’s exponential remainder. -/
lemma stokesQuotient_tendsto :
    Tendsto (fun θ : ℝ => 2 * (1 + exp (I * θ) + I * (θ - π)) /
      ((π - θ : ℝ) : ℂ) ^ 2) (𝓝[≠] π) (𝓝 1) := by
  let z : ℝ → ℂ := fun θ => I * (θ - π)
  have hz : Tendsto z (𝓝[≠] π) (𝓝 0) := by
    have h : ContinuousAt z π := by fun_prop
    simpa [z] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hr := (Complex.exp_sub_sum_range_succ_isLittleO_pow 2).comp_tendsto hz
  have hlim := hr.tendsto_div_nhds_zero
  have hlim' := tendsto_const_nhds.add (hlim.const_mul 2) (a := (1 : ℂ))
  simp only [mul_zero, add_zero] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθne : θ ≠ π := hθ
  have hden : ((π - θ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hθne))
  have hexp : exp (I * θ) = -exp (I * (θ - π)) := by
    rw [show I * (θ : ℂ) = I * (θ - π) + π * I by ring, exp_add, exp_pi_mul_I]
    ring
  simp only [Function.comp_def, z]
  norm_num [Finset.sum_range_succ]
  rw [hexp]
  have hzsq : (I * (θ - π : ℂ)) ^ 2 = -(((π - θ : ℝ) : ℂ) ^ 2) := by
    push_cast
    rw [mul_pow, I_sq]
    ring
  simp only [hzsq]
  push_cast at hden ⊢
  field_simp
  ring

/-- DLMF 2.11.16 (branch): `c` is continuous on `(-π, 3π)` and `c(θ) ∼ π - θ` as `θ → π`. -/
@[dlmf 2.11.E16]
theorem stokesC_continuous_tendsto :
    ContinuousOn stokesC (Ioo (-π) (3 * π)) ∧
      Tendsto (fun θ : ℝ => stokesC θ / ((π - θ : ℝ) : ℂ)) (𝓝[≠] π) (𝓝 1) := by
  let q : ℝ → ℂ := fun θ => 2 * (1 + exp (I * θ) + I * (θ - π)) /
    ((π - θ : ℝ) : ℂ) ^ 2
  have hroot : Tendsto (fun θ => q θ ^ (1 / 2 : ℂ)) (𝓝[≠] π) (𝓝 1) := by
    have hc := Complex.continuousAt_cpow_const_of_re_pos
      (z := (1 : ℂ)) (w := (1 / 2 : ℂ)) (Or.inl (by norm_num)) (by norm_num)
    simpa [q, Function.comp_def] using hc.tendsto.comp stokesQuotient_tendsto
  constructor
  · intro θ hθ
    suffices hc : ContinuousAt stokesC θ from hc.continuousWithinAt
    by_cases hθπ : θ = π
    · subst θ
      apply continuousAt_iff_punctured_nhds.mpr
      have hf : Tendsto (fun θ : ℝ => ((π - θ : ℝ) : ℂ)) (𝓝[≠] π) (𝓝 0) := by
        have hc : ContinuousAt (fun θ : ℝ => ((π - θ : ℝ) : ℂ)) π := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      have heq : stokesC = fun θ : ℝ => ((π - θ : ℝ) : ℂ) * q θ ^ (1 / 2 : ℂ) := rfl
      rw [heq]
      simpa using hf.mul hroot
    · have hden : ((π - θ : ℝ) : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hθπ))
      have hcq : ContinuousAt q θ := by
        dsimp [q]
        apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · exact pow_ne_zero 2 hden
      exact (by fun_prop : ContinuousAt (fun θ : ℝ => ((π - θ : ℝ) : ℂ)) θ).mul
        ((Complex.continuousAt_cpow_const_of_re_pos (z := q θ) (w := (1 / 2 : ℂ))
          (Or.inl (stokesQuotient_re_nonneg θ))
          (by norm_num : 0 < (1 / 2 : ℂ).re)).comp hcq)
  · refine hroot.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hden : ((π - θ : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hθ))
    change q θ ^ (1 / 2 : ℂ) = _
    rw [stokesC]
    change q θ ^ (1 / 2 : ℂ) = ((π - θ : ℝ) : ℂ) * q θ ^ (1 / 2 : ℂ) / ((π - θ : ℝ) : ℂ)
    field_simp


/-- DLMF 2.11.18: `h₀(θ, α) = e^{iα(π-θ)}/(1 + e^{-iθ}) - i/c(θ)` (from 2.11.17 with
`a₀ = 1`). -/
@[dlmf 2.11.E18]
theorem stokesH_zero {a : ℕ → ℝ → ℂ → ℂ} (ha : ∀ θ α, a 0 θ α = 1) (θ : ℝ) (α : ℂ) :
    stokesH a 0 θ α = exp (I * α * (π - θ)) / (1 + exp (-(I * θ))) - I / stokesC θ := by
  simp only [stokesH, ha, mul_one, mul_zero, zero_add, pow_one]
  simp
  ring

/-! ### §2.11(iv) Stokes phenomenon -/

/-- DLMF §2.11(iv): `c(θ)` lies in the right half-plane for `-π < θ < π` and in the left
half-plane for `π < θ < 3π`; hence `erfc((ρ/2)^{1/2} c(θ))` is exponentially small in the first
case and exponentially close to `2` in the second. -/
@[dlmf 2.11.iv]
theorem stokesC_re_sign :
    (∀ θ ∈ Ioo (-π) π, 0 < (stokesC θ).re) ∧ ∀ θ ∈ Ioo π (3 * π), (stokesC θ).re < 0 := by
  have hsqrt (θ : ℝ) (hne : θ ≠ π) :
      0 < ((2 * (1 + exp (I * θ) + I * (θ - π)) /
        ((π - θ : ℝ) : ℂ) ^ 2) ^ (1 / 2 : ℂ)).re := by
    let q : ℂ := 2 * (1 + exp (I * θ) + I * (θ - π)) / ((π - θ : ℝ) : ℂ) ^ 2
    have he : exp (I * θ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
      rw [mul_comm I (θ : ℂ), exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    have hnum : 2 * (1 + exp (I * θ) + I * (θ - π)) ≠ 0 := by
      intro hz
      have hr := congrArg Complex.re hz
      have hi := congrArg Complex.im hz
      simp [he] at hr hi
      change 1 + Real.cos θ = 0 at hr
      change Real.sin θ + (θ - π) = 0 at hi
      have hc : Real.cos θ = -1 := by linarith
      have hs : Real.sin θ = 0 := by
        have h := Real.sin_sq_add_cos_sq θ
        rw [hc] at h
        nlinarith [sq_nonneg (Real.sin θ)]
      apply hne
      linarith
    have hden : ((π - θ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have hq0 : q ≠ 0 := div_ne_zero hnum (pow_ne_zero 2 hden)
    have hqr : 0 ≤ q.re := stokesQuotient_re_nonneg θ
    change 0 < (q ^ (1 / 2 : ℂ)).re
    rw [show (1 / 2 : ℂ) = 2⁻¹ by norm_num, cpow_inv_two_re, Real.sqrt_pos]
    exact div_pos (add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hq0) hqr) (by norm_num)
  constructor
  · intro θ hθ
    have hpos := hsqrt θ hθ.2.ne
    simpa only [stokesC, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using
      mul_pos (sub_pos.mpr hθ.2) hpos
  · intro θ hθ
    have hpos := hsqrt θ hθ.1.ne'
    simpa only [stokesC, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using
      mul_neg_of_neg_of_pos (sub_neg.mpr hθ.1) hpos

/-! ### §2.11(v) Re-expansion of the remainders of 2.7.14 -/

/-- DLMF 2.11.19–2.11.23 (re-expansion in terminants): let 2.7.1 have a rank-one irregular
singularity at infinity with `λ₂ - λ₁ = 1`, solutions `w₁, w₂` with the expansions 2.7.14
(here on the logarithmic plane, `z = e^ζ`) and Stokes multipliers `C₁, C₂` (2.7.17). Define
`R_n^{(j)}` by 2.11.19 and `R_{m,n}^{(j)}` by 2.11.20–2.11.21 with the terminants
`F_ν(z) = Γ(ν)/(2π) E_ν(z)/z^{ν-1}`. Then for fixed `m` and `δ`, and `|n - |z||` bounded:
`R_{m,n}^{(1)}(z) = O(e^{-|z|-z} z^{-m})` for `|ph z| ≤ π`, `= O(z^{-m})` for
`π ≤ |ph z| ≤ 5π/2 - δ` (2.11.22); and `R_{m,n}^{(2)}(z) = O(e^{-|z|+z} z^{-m})` for
`0 ≤ ph z ≤ 2π`, `= O(z^{-m})` for `-3π/2 + δ ≤ ph z ≤ 0` and `2π ≤ ph z ≤ 7π/2 - δ`
(2.11.23), uniformly in `ph z`. -/
@[dlmf 2.11.E19, dlmf 2.11.E20, dlmf 2.11.E21, dlmf 2.11.E22, dlmf 2.11.E23, dlmf 2.11.v]
theorem rankOne_terminant_reexpansion {f g : ℂ → ℂ} {fs gs : ℕ → ℂ} {a : ℝ} {l₁ l₂ : ℂ}
    (h : IsRankOneAtInfinity f g fs gs a l₁ l₂) (h12 : l₂ - l₁ = 1) {W₁ W₂ : ℂ → ℂ}
    (hW₁ : IsLogPlaneSolOn f g W₁ (logExterior a))
    (hW₂ : IsLogPlaneSolOn f g W₂ (logExterior a))
    (hE₁ : HasAsymptoticExpansion (logSectorFilter (-π) π 0)
      (rankOneScale l₁ (rankOneExponent fs gs l₁) 0) (rankOneCoeff fs gs l₁) W₁)
    (hE₂ : HasAsymptoticExpansion (logSectorFilter 0 (2 * π) 0)
      (rankOneScale l₂ (rankOneExponent fs gs l₂) 0) (rankOneCoeff fs gs l₂) W₂)
    {C₁ C₂ : ℂ} (hC : ∀ ζ ∈ logExterior a,
      W₁ ζ = exp (2 * π * I * rankOneExponent fs gs l₁) * W₁ (ζ - 2 * π * I) + C₁ * W₂ ζ ∧
      W₂ ζ = exp (-(2 * π * I * rankOneExponent fs gs l₂)) * W₂ (ζ + 2 * π * I) + C₂ * W₁ ζ)
    (m : ℕ) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    let μ₁ := rankOneExponent fs gs l₁
    let μ₂ := rankOneExponent fs gs l₂
    let term : ℂ → ℂ → ℂ := fun ν ζ =>
      Gamma ν / (2 * π) * genExpIntEOnLog ν ζ / exp ((ν - 1) * ζ)
    let R₁ : ℕ → ℂ → ℂ := fun n ζ => W₁ ζ - exp (l₁ * exp ζ + μ₁ * ζ) *
      ∑ s ∈ Finset.range n, rankOneCoeff fs gs l₁ s * exp (-(s * ζ))
    let R₂ : ℕ → ℂ → ℂ := fun n ζ => W₂ ζ - exp (l₂ * exp ζ + μ₂ * ζ) *
      ∑ s ∈ Finset.range n, rankOneCoeff fs gs l₂ s * exp (-(s * ζ))
    let Rm₁ : ℕ → ℂ → ℂ := fun n ζ =>
      R₁ n ζ / ((-1) ^ (n - 1) * I * exp ((μ₂ - μ₁) * π * I) * exp (l₂ * exp ζ + μ₂ * ζ)) -
        C₁ * ∑ s ∈ Finset.range m, (-1) ^ s * rankOneCoeff fs gs l₂ s *
          term (n + μ₂ - μ₁ - s) ζ * exp (-(s * ζ))
    let Rm₂ : ℕ → ℂ → ℂ := fun n ζ =>
      R₂ n ζ / ((-1) ^ n * I * exp ((μ₂ - μ₁) * π * I) * exp (l₁ * exp ζ + μ₁ * ζ)) -
        C₂ * ∑ s ∈ Finset.range m, (-1) ^ s * rankOneCoeff fs gs l₁ s *
          term (n + μ₁ - μ₂ - s) (ζ - π * I) * exp (-(s * ζ))
    ∃ C r₀ : ℝ, ∀ (n : ℕ) (ζ : ℂ), r₀ ≤ Real.exp ζ.re → |(n : ℝ) - Real.exp ζ.re| ≤ B →
      (|ζ.im| ≤ π →
        ‖Rm₁ n ζ‖ ≤ C * ‖exp (-(Real.exp ζ.re : ℂ) - exp ζ - m * ζ)‖) ∧
      (π ≤ |ζ.im| → |ζ.im| ≤ 5 * π / 2 - δ → ‖Rm₁ n ζ‖ ≤ C * ‖exp (-(m * ζ))‖) ∧
      (0 ≤ ζ.im → ζ.im ≤ 2 * π →
        ‖Rm₂ n ζ‖ ≤ C * ‖exp (-(Real.exp ζ.re : ℂ) + exp ζ - m * ζ)‖) ∧
      ((-(3 * π / 2) + δ ≤ ζ.im ∧ ζ.im ≤ 0 ∨ 2 * π ≤ ζ.im ∧ ζ.im ≤ 7 * π / 2 - δ) →
        ‖Rm₂ n ζ‖ ≤ C * ‖exp (-(m * ζ))‖) := by
  sorry

/-! ### §2.11(vi) Direct numerical transformations -/

/-- DLMF 2.11.24: `e^x E₁(x) ∼ ∑ (-1)^s s!/x^{s+1}` as `x → +∞`; on the logarithmic plane in
`|ph z| ≤ 3π/2 - δ`, the project's 6.12.1. -/
@[dlmf 2.11.E24]
theorem expIntE1_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3 * π / 2) :
    HasAsymptoticExpansion (logSector (3 * π / 2 - δ))
      (fun n w => exp (-exp w - (n + 1 : ℂ) * w)) (fun n => (-1 : ℂ) ^ n * n.factorial)
      expIntE1OnLog :=
  expIntE1_logSector_asymptotic hδ hδ1

/-- The Pochhammer product `(½+μ-κ)_s (½-μ-κ)_s = (-1)^s ∏_{k=1}^{s} (μ² - (κ-k+½)²)`. -/
private lemma poch_mul_poch_eq_prod_sq_sub (κ μ : ℂ) (s : ℕ) :
    poch (1 / 2 + μ - κ) s * poch (1 / 2 - μ - κ) s =
      (-1) ^ s * ∏ k ∈ Finset.Icc 1 s, (μ ^ 2 - (κ - k + 1 / 2) ^ 2) := by
  induction s with
  | zero => simp [poch_zero]
  | succ s ih =>
    rw [poch_succ, poch_succ, Finset.prod_Icc_succ_top (by omega), pow_succ]
    have : poch (1 / 2 + μ - κ) s * (1 / 2 + μ - κ + s) *
        (poch (1 / 2 - μ - κ) s * (1 / 2 - μ - κ + s)) =
        (poch (1 / 2 + μ - κ) s * poch (1 / 2 - μ - κ) s) *
          ((1 / 2 + μ - κ + s) * (1 / 2 - μ - κ + s)) := by ring
    rw [this, ih]
    push_cast
    ring

/-- DLMF 2.11.29–2.11.30 for real `x → +∞`: `W_{κ,μ}(x) ∼ ∑ a_n` with `a_n` as in 2.11.30;
the remainder after `N` terms is `O(e^{-x/2} x^{κ-N})`. Corollary of the project's 13.19.3;
DLMF states the expansion for complex `z` with `|ph z| ≤ 3π/2 - δ`. -/
@[dlmf 2.11.E29, dlmf 2.11.E30]
theorem whittakerW_asymptotic (κ μ : ℂ) (N : ℕ) :
    (fun x : ℝ => whittakerW κ μ x - ∑ n ∈ Finset.range N, whittakerTerm κ μ x n) =O[atTop]
      fun x : ℝ => exp (-x / 2) * (x : ℂ) ^ (κ - N) := by
  refine (whittakerW_poincare κ μ N).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hxs : (x : ℂ) ^ s ≠ 0 := pow_ne_zero _ hx0
  have hxκ : (x : ℂ) ^ κ ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hx0 h.1
  have hneg : (-(x : ℂ)) ^ (-(s : ℂ)) = ((-1) ^ s * (x : ℂ) ^ s)⁻¹ := by
    rw [Complex.cpow_neg, Complex.cpow_natCast, neg_pow]
  have hsub : (x : ℂ) ^ ((s : ℂ) - κ) = (x : ℂ) ^ s / (x : ℂ) ^ κ := by
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_natCast]
  rw [whittakerTerm, hsub, hneg, poch_mul_poch_eq_prod_sq_sub]
  have hf : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
  have h1 : ((-1 : ℂ) ^ s) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

end DLMF.AsymptoticApproximations
