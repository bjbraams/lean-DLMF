/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Integrals.Defs
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The method of stationary phase (DLMF §2.3(iv))

* 2.3.20: the analogue of Watson's lemma for `∫₀^∞ e^{ixt} q(t) dt`;
* 2.3.19, 2.3.21–2.3.23: `∫ₐᵇ e^{ixp(t)} q(t) dt` with the stationary point (if any) at `a`,
  with the functions `Pₛ = stationaryPhaseP p q s` of 2.3.21.

"Infinitely differentiable expansions" (DLMF) are expansions whose termwise derivatives of every
order are expansions of the derivatives; the derivative of `t^ν` of order `k` is
`ν(ν-1)⋯(ν-k+1) t^{ν-k}` (`descPochhammer`). Integrals over infinite ranges, and integrals that
DLMF requires to converge "uniformly for all sufficiently large `x`", are limits of integrals
over `[c, T]` as `T → ∞`, uniformly in `x ≥ x₀`. When two endpoint series appear (2.3.23), each
is interpreted separately (§2.1(iii)): the remainder after `N` terms of the first and `M` terms
of the second is `O(x^{-(N+λ)/μ}) + O(x^{-M-1})`.

Restriction: in 2.3.23 with `p(b)` finite, `b` is finite here; in case (d) (`p(b) = ∞`) the
range is `(a, ∞)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real ContDiff

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.3.20: let `q` be infinitely differentiable on `(0, ∞)` with the infinitely
differentiable expansion `q(t) ∼ ∑ aₛ t^{(s+λ-μ)/μ}` as `t → 0⁺` (2.3.7, `λ, μ > 0`), and let each
`∫^∞ e^{ixt} q^{(s)}(t) dt` converge at `∞` uniformly for `x ≥ x₀`. Then the (improper) integral
`I(x) = ∫₀^∞ e^{ixt} q(t) dt` satisfies
`I(x) ∼ ∑ exp((s+λ)πi/(2μ)) Γ((s+λ)/μ) aₛ x^{-(s+λ)/μ}` as `x → +∞`. Here
`I(x) = ∫₀¹ e^{ixt} q(t) dt + lim_{T→∞} ∫₁ᵀ e^{ixt} q(t) dt`. -/
@[dlmf 2.3.E20, dlmf 2.3.iv]
theorem stationaryPhase_watson {q : ℝ → ℂ} {a : ℕ → ℂ} {lam mu x₀ : ℝ} (hlam : 0 < lam)
    (hmu : 0 < mu) (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    (hexp : ∀ k : ℕ, HasAsymptoticExpansion (𝓝[>] 0)
      (fun (s : ℕ) (t : ℝ) => t ^ (((s : ℝ) + lam - mu) / mu - k))
      (fun s => (descPochhammer ℝ k).eval (((s : ℝ) + lam - mu) / mu) • a s) (iteratedDeriv k q))
    {L : ℕ → ℝ → ℂ}
    (hunif : ∀ s : ℕ, TendstoUniformlyOn (fun (T x : ℝ) =>
      ∫ t in (1 : ℝ)..T, Complex.exp (I * x * t) * iteratedDeriv s q t) (L s) atTop (Ici x₀)) :
    HasAsymptoticExpansion atTop (fun (s : ℕ) (x : ℝ) => x ^ (-(((s : ℝ) + lam) / mu)))
      (fun s => Complex.exp (((s : ℂ) + lam) * π * I / (2 * mu)) *
        Real.Gamma (((s : ℝ) + lam) / mu) * a s)
      (fun x => (∫ t in (0 : ℝ)..1, Complex.exp (I * x * t) * q t) + L 0 x) := by
  sorry

/-- DLMF 2.3.19, 2.3.21, 2.3.23 (stationary phase, `p(b)` finite): let `a < b`, and assume
(a) on `(a, b)`, `p` and `q` are infinitely differentiable and `p' > 0`;
(b) as `t → a⁺`, the expansions 2.3.14 hold and are infinitely differentiable, `λ, μ, p₀ > 0`;
(c) `p(t) → p(b)` as `t → b⁻`, and each `Pₛ(t)` of 2.3.21 tends to a finite limit `Pₛ(b)`.
Then, with `bₛ` as in §2.3(iii),
`∫ₐᵇ e^{ixp(t)} q(t) dt ∼ e^{ixp(a)} ∑ exp((s+λ)πi/(2μ)) Γ((s+λ)/μ) bₛ x^{-(s+λ)/μ}
- e^{ixp(b)} ∑ Pₛ(b) (i/x)^{s+1}` as `x → +∞`, each series interpreted separately. -/
@[dlmf 2.3.E19, dlmf 2.3.E21, dlmf 2.3.E23, dlmf 2.3.iv]
theorem stationaryPhase_endpoint {p : ℝ → ℝ} {q : ℝ → ℂ} {pc : ℕ → ℝ} {qc : ℕ → ℂ}
    {a b lam mu pb : ℝ} {Pb : ℕ → ℂ} (hab : a < b) (hlam : 0 < lam) (hmu : 0 < mu)
    (hp0 : 0 < pc 0) (hp : ContDiffOn ℝ ∞ p (Ioo a b)) (hq : ContDiffOn ℝ ∞ q (Ioo a b))
    (hp' : ∀ t ∈ Ioo a b, 0 < deriv p t)
    (hpexp : ∀ k : ℕ, HasAsymptoticExpansion (𝓝[>] a)
      (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + mu - k))
      (fun s => (descPochhammer ℝ k).eval ((s : ℝ) + mu) * pc s)
      (iteratedDeriv k fun t => p t - p a))
    (hqexp : ∀ k : ℕ, HasAsymptoticExpansion (𝓝[>] a)
      (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + lam - 1 - k))
      (fun s => (descPochhammer ℝ k).eval ((s : ℝ) + lam - 1) • qc s) (iteratedDeriv k q))
    (hpb : Tendsto p (𝓝[<] b) (𝓝 pb))
    (hPb : ∀ s, Tendsto (stationaryPhaseP p q s) (𝓝[<] b) (𝓝 (Pb s))) (N M : ℕ) :
    (fun x : ℝ => (∫ t in Ioo a b, Complex.exp (I * x * p t) * q t) -
        Complex.exp (I * x * p a) * ∑ s ∈ range N,
          Complex.exp (((s : ℂ) + lam) * π * I / (2 * mu)) *
          Real.Gamma (((s : ℝ) + lam) / mu) *
          laplaceCoeff (Real.log (pc 0)) (fun s => (pc s : ℂ)) qc lam mu s *
          (x : ℂ) ^ (-(((s : ℂ) + lam) / mu)) +
        Complex.exp (I * x * pb) * ∑ s ∈ range M, Pb s * (I / x) ^ (s + 1))
      =O[atTop] fun x => x ^ (-(((N : ℝ) + lam) / mu)) + x ^ (-((M : ℝ) + 1)) := by
  sorry

/-- DLMF 2.3.22–2.3.23, case (d): under (a), (b) of `stationaryPhase_endpoint` on `(a, ∞)`, if
`p(t) → ∞`, `P₀(t) → 0` as `t → ∞` and each integral `∫^∞ e^{ixp(t)} Pₛ(t) p'(t) dt` (2.3.22)
converges uniformly for `x ≥ x₀`, then the second sum in 2.3.23 is absent:
`I(x) ∼ e^{ixp(a)} ∑ exp((s+λ)πi/(2μ)) Γ((s+λ)/μ) bₛ x^{-(s+λ)/μ}`, where
`I(x) = ∫ₐ^{a+1} e^{ixp} q + lim_{T→∞} ∫_{a+1}^T e^{ixp} q`. -/
@[dlmf 2.3.E22, dlmf 2.3.E23, dlmf 2.3.iv]
theorem stationaryPhase_endpoint_infinite {p : ℝ → ℝ} {q : ℝ → ℂ} {pc : ℕ → ℝ} {qc : ℕ → ℂ}
    {a lam mu x₀ : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hp0 : 0 < pc 0) (hp : ContDiffOn ℝ ∞ p (Ioi a)) (hq : ContDiffOn ℝ ∞ q (Ioi a))
    (hp' : ∀ t ∈ Ioi a, 0 < deriv p t)
    (hpexp : ∀ k : ℕ, HasAsymptoticExpansion (𝓝[>] a)
      (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + mu - k))
      (fun s => (descPochhammer ℝ k).eval ((s : ℝ) + mu) * pc s)
      (iteratedDeriv k fun t => p t - p a))
    (hqexp : ∀ k : ℕ, HasAsymptoticExpansion (𝓝[>] a)
      (fun (s : ℕ) t => (t - a) ^ ((s : ℝ) + lam - 1 - k))
      (fun s => (descPochhammer ℝ k).eval ((s : ℝ) + lam - 1) • qc s) (iteratedDeriv k q))
    (hpinf : Tendsto p atTop atTop) (hP0 : Tendsto (stationaryPhaseP p q 0) atTop (𝓝 0))
    {L : ℕ → ℝ → ℂ}
    (hunif : ∀ s : ℕ, TendstoUniformlyOn (fun (T x : ℝ) => ∫ t in (a + 1)..T,
      Complex.exp (I * x * p t) * stationaryPhaseP p q s t * deriv p t) (L s) atTop (Ici x₀)) :
    HasAsymptoticExpansion atTop
      (fun (s : ℕ) (x : ℝ) => Complex.exp (I * x * p a) * (x : ℂ) ^ (-(((s : ℂ) + lam) / mu)))
      (fun s => Complex.exp (((s : ℂ) + lam) * π * I / (2 * mu)) *
        Real.Gamma (((s : ℝ) + lam) / mu) *
        laplaceCoeff (Real.log (pc 0)) (fun s => (pc s : ℂ)) qc lam mu s)
      (fun x => (∫ t in Ioo a (a + 1), Complex.exp (I * x * p t) * q t) + L 0 x) := by
  sorry

end DLMF.AsymptoticApproximations
