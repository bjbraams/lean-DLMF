/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Integrals.Basic
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Laplace's method and saddle points (DLMF §§2.3(iii), 2.4(iii)–(iv))

* 2.3.13–2.3.18: Laplace's method for `∫ₐᵇ e^{-xp(t)} q(t) dt` with the minimum of `p` at the
  left endpoint, `p(t) - p(a) ∼ ∑ pₛ (t-a)^{s+μ}`, `q(t) ∼ ∑ qₛ (t-a)^{s+λ-1}`. The coefficients
  `bₛ` are `laplaceCoeff` (the residue formula 2.3.18); 2.3.16 identifies them with the
  expansion of `q/p'` in powers of `v = p(t) - p(a)`, and 2.3.17 (proved) gives `b₀, b₁, b₂`.
  The formula 2.3.15 was checked numerically (`p = t² + t³`, `q = 1 + 2t`).
* 2.4.10–2.4.13: Laplace's method for contour integrals. The path `𝒫` from `a` is
  parametrized as `t = γ(u)`, `u ∈ (0, ∞)` (finite and infinite `b` alike), and the powers
  `(t - a)^ν` are `|t - a|^ν e^{iνθ(u)}` for a continuous branch `θ(u)` of `ph(γ(u) - a)` with
  `θ(u) → ω`. The variable `z = r e^{iθ}` ranges over the annular sector `θ₁ ≤ θ ≤ θ₂`, `r → ∞`,
  written as the filter `atTop ×ˢ 𝓟 [θ₁, θ₂]` on `(r, θ)` with `z^ν = r^ν e^{iνθ}`, so no
  branch cut of `ph z` enters.
* 2.4.14–2.4.16: saddle points.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real Nat

namespace DLMF.AsymptoticApproximations

/-! ### §2.3(iii): Laplace's method -/

/-- DLMF 2.3.13–2.3.15 (**Laplace's method**): let `a < b`, and assume
(a) `p` is differentiable with continuous `p'` and `q` is continuous on `(a, a + δ)`, and the
minimum of `p` on `[a, b)` is approached only at `a` (for each `ε > 0`, `p ≥ p(a) + η` on
`[a + ε, b)` for some `η > 0`);
(b) as `t → a⁺`, `p(t) ∼ p(a) + ∑ pₛ (t-a)^{s+μ}` with the differentiated expansion for `p'`,
and `q(t) ∼ ∑ qₛ (t-a)^{s+λ-1}` (2.3.14), with `λ, μ, p₀ > 0`;
(c) the integral 2.3.13 converges absolutely for large `x`.
Then `∫ₐᵇ e^{-xp(t)} q(t) dt ∼ e^{-xp(a)} ∑ Γ((s+λ)/μ) bₛ x^{-(s+λ)/μ}` as `x → +∞` (2.3.15),
with `bₛ = laplaceCoeff (ln p₀) p q λ μ s` (2.3.16–2.3.18). -/
@[dlmf 2.3.E13, dlmf 2.3.E14, dlmf 2.3.E15, dlmf 2.3.iii]
theorem laplace_method {p : ℝ → ℝ} {q : ℝ → ℂ} {pc : ℕ → ℝ} {qc : ℕ → ℂ} {a b δ lam mu x₀ : ℝ}
    (hab : a < b) (hδ : 0 < δ) (hlam : 0 < lam) (hmu : 0 < mu) (hp0 : 0 < pc 0)
    (hpd : ∀ t ∈ Ioo a (a + δ), DifferentiableAt ℝ p t)
    (hpc : ContinuousOn (deriv p) (Ioo a (a + δ))) (hqc : ContinuousOn q (Ioo a (a + δ)))
    (hmin : ∀ ε > 0, ∃ η > 0, ∀ t ∈ Ico (a + ε) b, p a + η ≤ p t)
    (hpexp : HasAsymptoticExpansion (𝓝[>] a) (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + mu)) pc
      fun t => p t - p a)
    (hp'exp : HasAsymptoticExpansion (𝓝[>] a) (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + mu - 1))
      (fun s => ((s : ℝ) + mu) * pc s) (deriv p))
    (hqexp : HasAsymptoticExpansion (𝓝[>] a) (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + lam - 1)) qc q)
    (hint : IntegrableOn (fun t => Real.exp (-x₀ * p t) • q t) (Ioo a b)) :
    HasAsymptoticExpansion atTop
      (fun (s : ℕ) (x : ℝ) => Real.exp (-x * p a) * x ^ (-(((s : ℝ) + lam) / mu)))
      (fun s => (Real.Gamma (((s : ℝ) + lam) / mu) : ℂ) *
        laplaceCoeff (Real.log (pc 0)) (fun s => (pc s : ℂ)) qc lam mu s)
      (fun x => ∫ t in Ioo a b, Real.exp (-x * p t) • q t) := by
  sorry

/-- DLMF 2.3.15 with `b = ∞`: Laplace's method on `(a, ∞)`, with the hypotheses of
`laplace_method` for `b = ∞`. -/
@[dlmf 2.3.E13, dlmf 2.3.E15, dlmf 2.3.iii]
theorem laplace_method_Ioi {p : ℝ → ℝ} {q : ℝ → ℂ} {pc : ℕ → ℝ} {qc : ℕ → ℂ} {a δ lam mu x₀ : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hmu : 0 < mu) (hp0 : 0 < pc 0)
    (hpd : ∀ t ∈ Ioo a (a + δ), DifferentiableAt ℝ p t)
    (hpc : ContinuousOn (deriv p) (Ioo a (a + δ))) (hqc : ContinuousOn q (Ioo a (a + δ)))
    (hmin : ∀ ε > 0, ∃ η > 0, ∀ t ∈ Ici (a + ε), p a + η ≤ p t)
    (hpexp : HasAsymptoticExpansion (𝓝[>] a) (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + mu)) pc
      fun t => p t - p a)
    (hp'exp : HasAsymptoticExpansion (𝓝[>] a) (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + mu - 1))
      (fun s => ((s : ℝ) + mu) * pc s) (deriv p))
    (hqexp : HasAsymptoticExpansion (𝓝[>] a) (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + lam - 1)) qc q)
    (hint : IntegrableOn (fun t => Real.exp (-x₀ * p t) • q t) (Ioi a)) :
    HasAsymptoticExpansion atTop
      (fun (s : ℕ) (x : ℝ) => Real.exp (-x * p a) * x ^ (-(((s : ℝ) + lam) / mu)))
      (fun s => (Real.Gamma (((s : ℝ) + lam) / mu) : ℂ) *
        laplaceCoeff (Real.log (pc 0)) (fun s => (pc s : ℂ)) qc lam mu s)
      (fun x => ∫ t in Ioi a, Real.exp (-x * p t) • q t) := by
  sorry

/-- DLMF 2.3.16 (with 2.3.18): under hypothesis (b) of Laplace's method, `q(t)/p'(t)` has the
expansion `∑ bₛ v^{(s+λ-μ)/μ}` in powers of `v = p(t) - p(a)` as `t → a⁺` (equivalently
`v → 0⁺`), with `bₛ = laplaceCoeff (ln p₀) p q λ μ s`. -/
@[dlmf 2.3.E16, dlmf 2.3.E18]
theorem laplaceCoeff_hasAsymptoticExpansion {p : ℝ → ℝ} {q : ℝ → ℂ} {pc : ℕ → ℝ} {qc : ℕ → ℂ}
    {a lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) (hp0 : 0 < pc 0)
    (hpexp : HasAsymptoticExpansion (𝓝[>] a) (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + mu)) pc
      fun t => p t - p a)
    (hp'exp : HasAsymptoticExpansion (𝓝[>] a) (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + mu - 1))
      (fun s => ((s : ℝ) + mu) * pc s) (deriv p))
    (hqexp : HasAsymptoticExpansion (𝓝[>] a) (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + lam - 1))
      qc q) :
    HasAsymptoticExpansion (𝓝[>] a)
      (fun (s : ℕ) t => (p t - p a) ^ (((s : ℝ) + lam - mu) / mu))
      (fun s => laplaceCoeff (Real.log (pc 0)) (fun s => (pc s : ℂ)) qc lam mu s)
      (fun t => q t / Complex.ofReal (deriv p t)) := by
  sorry

section Coefficients

variable {L₀ : ℂ} {p q : ℕ → ℂ} {lam mu : ℂ}

/-- Identity under the stated parameter and domain assumptions: `binomSeriesCoeff p β 0 = 1`. -/
theorem binomSeriesCoeff_zero (β : ℂ) : binomSeriesCoeff p β 0 = 1 := by
  simp [binomSeriesCoeff, cbinom]

/-- Identity under the stated parameter and domain assumptions: `binomSeriesCoeff p β 1 = β * (p 1
/ p 0)`. -/
theorem binomSeriesCoeff_one (β : ℂ) : binomSeriesCoeff p β 1 = β * (p 1 / p 0) := by
  simp [binomSeriesCoeff, cbinom, sum_range_succ, PowerSeries.coeff_one]

/-- Identity under the stated parameter and domain assumptions: `binomSeriesCoeff p β 2 = β * (p 2
/ p 0) + β * (β - 1) / 2 * (p 1 / p 0) ^ 2`. -/
theorem binomSeriesCoeff_two (β : ℂ) :
    binomSeriesCoeff p β 2 = β * (p 2 / p 0) + β * (β - 1) / 2 * (p 1 / p 0) ^ 2 := by
  simp only [binomSeriesCoeff, cbinom, sum_range_succ, range_zero, sum_empty, pow_zero,
    pow_one, zero_add]
  simp [descPochhammer_succ_right, pow_two, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
    PowerSeries.coeff_one]

/-- DLMF 2.3.17: `b₀ = q₀/(μ p₀^{λ/μ})`, with `p₀^{α} = exp(α L₀)`. -/
@[dlmf 2.3.E17]
theorem laplaceCoeff_zero :
    laplaceCoeff L₀ p q lam mu 0 = q 0 / (mu * Complex.exp (lam / mu * L₀)) := by
  simp only [laplaceCoeff, Nat.cast_zero, add_zero, zero_add, range_one, sum_singleton,
    Nat.sub_self, binomSeriesCoeff_zero, mul_one]
  rw [neg_mul, Complex.exp_neg]
  field_simp

/-- DLMF 2.3.17: `b₁ = (q₁/μ - (λ+1)p₁q₀/(μ²p₀)) / p₀^{(λ+1)/μ}`. -/
@[dlmf 2.3.E17]
theorem laplaceCoeff_one (hp : p 0 ≠ 0) (hmu : mu ≠ 0) :
    laplaceCoeff L₀ p q lam mu 1 = (q 1 / mu - (lam + 1) * p 1 * q 0 / (mu ^ 2 * p 0)) /
      Complex.exp ((lam + 1) / mu * L₀) := by
  simp only [laplaceCoeff, sum_range_succ, range_zero, sum_empty, zero_add, Nat.cast_one,
    Nat.sub_zero, Nat.sub_self, binomSeriesCoeff_zero, binomSeriesCoeff_one]
  rw [neg_mul, Complex.exp_neg]
  field_simp
  ring

/-- DLMF 2.3.17: `b₂ = (q₂/μ - (λ+2)(p₁q₁ + p₂q₀)/(μ²p₀) + (λ+2)(λ+μ+2)p₁²q₀/(2μ³p₀²))
/ p₀^{(λ+2)/μ}`. -/
@[dlmf 2.3.E17]
theorem laplaceCoeff_two (hp : p 0 ≠ 0) (hmu : mu ≠ 0) :
    laplaceCoeff L₀ p q lam mu 2 = (q 2 / mu - (lam + 2) * (p 1 * q 1 + p 2 * q 0) / (mu ^ 2 * p 0)
      + (lam + 2) * (lam + mu + 2) * p 1 ^ 2 * q 0 / (2 * mu ^ 3 * p 0 ^ 2)) /
      Complex.exp ((lam + 2) / mu * L₀) := by
  simp only [laplaceCoeff, sum_range_succ, range_zero, sum_empty, zero_add, Nat.cast_ofNat,
    Nat.sub_zero, Nat.sub_self, binomSeriesCoeff_zero, binomSeriesCoeff_one,
    show 2 - 1 = 1 from rfl, binomSeriesCoeff_two]
  rw [neg_mul, Complex.exp_neg]
  field_simp
  ring

end Coefficients

/-! ### §2.4(iii): Laplace's method for contour integrals -/

/-- DLMF 2.4.10–2.4.13 (**Laplace's method for contour integrals**): let the path `𝒫` from `a`
be `t = γ(u)`, `u ∈ (0, ∞)`, with `γ(u) → a` as `u → 0⁺`, `γ(u) ≠ a`, `γ` differentiable, and let
`θγ` be a continuous branch of `ph(γ(u) - a)` with limit `ω` (the slope at `a`). Assume
(a) near `a`, `p(t) = p(a) + ∑ pₛ (t-a)^{s+μ}` and `q(t) = ∑ qₛ (t-a)^{s+λ-1}` as convergent
series along `𝒫` (2.4.11), with `ℜλ > 0`, `μ > 0`, `p₀ ≠ 0`, powers by the branch `θγ`;
(b) `z = r e^{iθ}` ranges over `θ₁ ≤ θ ≤ θ₂`, `r ≥ Z`, `θ₂ - θ₁ < π`, and `I(z)` converges at
`b` absolutely and uniformly;
(c) `ℜ(e^{iθ}(p(t) - p(a))) > 0` on `𝒫 \ {a}`, bounded away from `0` uniformly in `θ` as
`t → b` along `𝒫`.
Then `I(z) = ∫ₐᵇ e^{-zp(t)} q(t) dt ∼ e^{-zp(a)} ∑ Γ((s+λ)/μ) bₛ z^{-(s+λ)/μ}` as `z → ∞` in the
sector (2.4.12), where `bₛ = laplaceCoeff L₀ p q λ μ s` with `exp L₀ = p₀` and
`ph p₀ = ℑL₀` chosen so that `|θ + μω + ph p₀| ≤ ½π` (2.4.13). -/
@[dlmf 2.4.E10, dlmf 2.4.E11, dlmf 2.4.E12, dlmf 2.4.E13, dlmf 2.4.iii]
theorem laplace_method_contour {p q : ℂ → ℂ} {γ : ℝ → ℂ} {θγ : ℝ → ℝ} {a : ℂ} {pc qc : ℕ → ℂ}
    {lam : ℂ} {mu ω θ₁ θ₂ Z u₀ L₀re L₀im : ℝ}
    (hγ0 : Tendsto γ (𝓝[>] 0) (𝓝 a)) (hγa : ∀ u, 0 < u → γ u ≠ a)
    (hγd : ∀ u, 0 < u → DifferentiableAt ℝ γ u)
    (hθγ : ContinuousOn θγ (Ioi 0)) (hθγa : ∀ u, 0 < u → γ u - a = ‖γ u - a‖ * exp (θγ u * I))
    (hω : Tendsto θγ (𝓝[>] 0) (𝓝 ω))
    (hlam : 0 < lam.re) (hmu : 0 < mu) (hp0 : pc 0 ≠ 0) (hu₀ : 0 < u₀)
    (hpser : ∀ u ∈ Ioo 0 u₀,
      HasSum (fun s => pc s * pathPow γ θγ a ((s : ℂ) + mu) u) (p (γ u) - p a))
    (hqser : ∀ u ∈ Ioo 0 u₀,
      HasSum (fun s => qc s * pathPow γ θγ a ((s : ℂ) + lam - 1) u) (q (γ u)))
    (hθ : θ₁ ≤ θ₂) (hθπ : θ₂ - θ₁ < π) (hZ : 0 < Z)
    (hint : ∀ r θ, Z ≤ r → θ ∈ Icc θ₁ θ₂ → Integrable (fun u =>
      Complex.exp (-(r * Complex.exp (θ * I)) * p (γ u)) * q (γ u) * deriv γ u)
      (volume.restrict (Ioi 0)))
    (hunif : ∀ ε > 0, ∃ U, ∀ r θ, Z ≤ r → θ ∈ Icc θ₁ θ₂ → ∫ u in Ioi U,
      ‖Complex.exp (-(r * Complex.exp (θ * I)) * p (γ u)) * q (γ u) * deriv γ u‖ < ε)
    (hpos : ∀ u θ, 0 < u → θ ∈ Icc θ₁ θ₂ → 0 < (Complex.exp (θ * I) * (p (γ u) - p a)).re)
    (hbdd : ∃ η > 0, ∃ U, ∀ u θ, U ≤ u → θ ∈ Icc θ₁ θ₂ →
      η ≤ (Complex.exp (θ * I) * (p (γ u) - p a)).re)
    (hL₀ : Complex.exp (L₀re + L₀im * I) = pc 0)
    (hbranch : ∀ θ ∈ Icc θ₁ θ₂, |θ + mu * ω + L₀im| ≤ π / 2) :
    HasAsymptoticExpansion (atTop ×ˢ 𝓟 (Icc θ₁ θ₂))
      (fun (s : ℕ) => polarScale (p a) (((s : ℂ) + lam) / mu))
      (fun s => Complex.Gamma (((s : ℂ) + lam) / mu) *
        laplaceCoeff (L₀re + L₀im * I) pc qc lam mu s)
      (fun rθ => ∫ u in Ioi (0 : ℝ),
        Complex.exp (-(rθ.1 * Complex.exp (rθ.2 * I)) * p (γ u)) * q (γ u) * deriv γ u) := by
  sorry

/-! ### §2.4(iv): saddle points -/

/-- DLMF 2.4.14: subdivision of the path at an interior point `t₀ = γ(u₀)`:
`∫ₐᵇ = ∫_{t₀}^b - ∫_{t₀}^a`, for a path parametrized by `u ∈ (0, ∞)`. -/
@[dlmf 2.4.E14]
theorem integral_path_split {F : ℝ → ℂ} {u₀ : ℝ} (hu₀ : 0 < u₀)
    (hF : IntegrableOn F (Ioi 0)) :
    ∫ u in Ioi (0 : ℝ), F u = (∫ u in Ioi u₀, F u) - ∫ u in u₀..0, F u := by
  rw [intervalIntegral.integral_symm, sub_neg_eq_add,
    intervalIntegral.integral_of_le hu₀.le, add_comm,
    ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hF.mono_set Ioc_subset_Ioi_self) (hF.mono_set (Ioi_subset_Ioi hu₀.le)),
    Ioc_union_Ioi_eq_Ioi hu₀.le]

/-- DLMF 2.4.15 (**saddle point**): let the path `𝒫` be `t = γ(u)`, `u ∈ ℝ` (from `a` at
`u → -∞` to `b` at `u → +∞`), through a simple saddle point `t₀ = γ(0)`: `p`, `q` analytic on an
open set containing `𝒫`, `p'(t₀) = 0 ≠ p''(t₀)`, `γ` differentiable with `γ'(0) ≠ 0` and
`ph γ'(0) = ω` (the limiting value of `ph(t - t₀)` as `t → t₀` from `b`); for `z = re^{iθ}`,
`θ₁ ≤ θ ≤ θ₂` (`θ₂ - θ₁ < π`), `ℜ(e^{iθ}(p(t) - p(t₀))) > 0` on `𝒫 \ {t₀}`, bounded away from
zero at both ends, and the integral converges absolutely and uniformly. Then
`∫ₐᵇ e^{-zp(t)} q(t) dt ∼ 2 e^{-zp(t₀)} ∑ Γ(s + ½) b₂ₛ z^{-s-1/2}`, with
`b₂ₛ = laplaceCoeff L₀ P Q 1 2 (2s)` for `P k = p^{(k+2)}(t₀)/(k+2)!`, `Q k = q^{(k)}(t₀)/k!`
(2.3.18 with `λ = 1`, `μ = 2`, §2.4(iv)), and `exp L₀ = p''(t₀)/2` with `ω₀ = ph p''(t₀) = ℑL₀`
satisfying `|θ + 2ω + ω₀| ≤ ½π`. -/
@[dlmf 2.4.E15, dlmf 2.4.iv]
theorem saddle_point {p q : ℂ → ℂ} {γ : ℝ → ℂ} {T : Set ℂ} {ω θ₁ θ₂ Z L₀re L₀im : ℝ}
    (hT : IsOpen T) (hγT : ∀ u, γ u ∈ T) (hp : DifferentiableOn ℂ p T)
    (hq : DifferentiableOn ℂ q T) (hγd : Differentiable ℝ γ) (hγinj : Function.Injective γ)
    (hγ' : deriv γ 0 ≠ 0) (hω : deriv γ 0 = ‖deriv γ 0‖ * exp (ω * I))
    (hp1 : deriv p (γ 0) = 0) (hp2 : iteratedDeriv 2 p (γ 0) ≠ 0)
    (hθ : θ₁ ≤ θ₂) (hθπ : θ₂ - θ₁ < π) (hZ : 0 < Z)
    (hint : ∀ r θ, Z ≤ r → θ ∈ Icc θ₁ θ₂ → Integrable (fun u =>
      Complex.exp (-(r * Complex.exp (θ * I)) * p (γ u)) * q (γ u) * deriv γ u))
    (hunif : ∀ ε > 0, ∃ U, ∀ r θ, Z ≤ r → θ ∈ Icc θ₁ θ₂ → ∫ u in {u | U ≤ |u|},
      ‖Complex.exp (-(r * Complex.exp (θ * I)) * p (γ u)) * q (γ u) * deriv γ u‖ < ε)
    (hpos : ∀ u θ, u ≠ 0 → θ ∈ Icc θ₁ θ₂ →
      0 < (Complex.exp (θ * I) * (p (γ u) - p (γ 0))).re)
    (hbdd : ∃ η > 0, ∃ U, ∀ u θ, U ≤ |u| → θ ∈ Icc θ₁ θ₂ →
      η ≤ (Complex.exp (θ * I) * (p (γ u) - p (γ 0))).re)
    (hL₀ : Complex.exp (L₀re + L₀im * I) = iteratedDeriv 2 p (γ 0) / 2)
    (hbranch : ∀ θ ∈ Icc θ₁ θ₂, |θ + 2 * ω + L₀im| ≤ π / 2) :
    HasAsymptoticExpansion (atTop ×ˢ 𝓟 (Icc θ₁ θ₂))
      (fun (s : ℕ) => polarScale (p (γ 0)) ((s : ℂ) + 1 / 2))
      (fun s => 2 * Complex.Gamma ((s : ℂ) + 1 / 2) *
        laplaceCoeff (L₀re + L₀im * I) (fun k => iteratedDeriv (k + 2) p (γ 0) / (k + 2)!)
          (fun k => iteratedDeriv k q (γ 0) / k !) 1 2 (2 * s))
      (fun rθ => ∫ u : ℝ,
        Complex.exp (-(rθ.1 * Complex.exp (rθ.2 * I)) * p (γ u)) * q (γ u) * deriv γ u) := by
  sorry

/-- DLMF 2.4.16: the first two coefficients of the saddle-point expansion 2.4.15:
`b₀ = q/(2p'')^{1/2}`, with `(2p'')^{1/2} = 2 exp(L₀/2)` for `exp L₀ = p''/2`. -/
@[dlmf 2.4.E16]
theorem saddle_coeff_zero {P Q : ℕ → ℂ} {L₀ : ℂ} :
    laplaceCoeff L₀ (fun k => P (k + 2) / (k + 2)!) (fun k => Q k / k !) 1 2 0 =
      Q 0 / (2 * Complex.exp (L₀ / 2)) := by
  rw [laplaceCoeff_zero]
  simp only [Nat.factorial_zero, Nat.cast_one, div_one]
  congr 3
  ring

/-- DLMF 2.4.16: `b₂ = (2q'' - 2p'''q'/p'' + (5p'''²/(6p''²) - p⁗/(2p''))q)/(2p'')^{3/2}`, with
`P k = p^{(k)}(t₀)`, `Q k = q^{(k)}(t₀)`, and `(2p'')^{3/2} = 8 exp(3L₀/2)` for
`exp L₀ = p''/2`. -/
@[dlmf 2.4.E16]
theorem saddle_coeff_two {P Q : ℕ → ℂ} {L₀ : ℂ} (hP : P 2 ≠ 0) :
    laplaceCoeff L₀ (fun k => P (k + 2) / (k + 2)!) (fun k => Q k / k !) 1 2 2 =
      (2 * Q 2 - 2 * P 3 * Q 1 / P 2 + (5 * P 3 ^ 2 / (6 * P 2 ^ 2) - P 4 / (2 * P 2)) * Q 0) /
        (8 * Complex.exp (3 * L₀ / 2)) := by
  rw [laplaceCoeff_two (by simpa using hP) two_ne_zero]
  simp only [Nat.factorial, Nat.cast_ofNat, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul,
    Nat.cast_one, zero_add, Nat.mul_one]
  have h3 : Complex.exp ((1 + 2) / 2 * L₀) = Complex.exp (3 * L₀ / 2) := by ring_nf
  rw [h3]
  have he : Complex.exp (3 * L₀ / 2) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

end DLMF.AsymptoticApproximations
