/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.RingTheory.Binomial

/-!
# Distributional methods: definitions (DLMF §2.6)

Definitions for DLMF §2.6 (namespace `DLMF.AsymptoticApproximations`).

DLMF assigns distributions (continuous linear functionals on the space `𝒯` of rapidly
decreasing functions) to the functions `t^{-s-α}` and to the remainders `f_n` of an
asymptotic expansion. We record the *values* of these functionals as explicit integrals,
`φ ↦ ⟨·, φ⟩`, for an arbitrary function `φ : ℝ → ℂ`: the formulas only use `φ` and its
derivatives on `[0, ∞)`, and they are applied in DLMF both to Schwartz functions and to the
functions `φ_ε(t) = e^{-εt}/(t+z)` of 2.6.22, which are not Schwartz functions on `ℝ`.
Continuity of these functionals on the Schwartz space is not asserted by the definitions.
All integrals use Lean's totalization (the integral of a non-integrable function is `0`), so
every statement using them carries integrability hypotheses or conclusions where needed.

* `stieltjesTransform f z = ∫₀^∞ f(t)/(t+z) dt` (2.6.8) and its generalization
  `generalizedStieltjesTransform ρ f z` (2.6.32).
* `functionPairing f φ = ∫₀^∞ f φ` (2.6.11, 2.6.12).
* `powPairing α s φ = (α)_s⁻¹ ∫₀^∞ t^{-α} φ^{(s)}(t) dt` (2.6.13), `0 < α < 1`.
* `logPowPairing s φ = -(1/s!) ∫₀^∞ ln t φ^{(s+1)}(t) dt` (2.6.14), the case `α = 1`.
* `tPowPairing λ φ`: the distribution `t^λ` for real `λ`, as selected by 2.6.12–2.6.14.
* `diracDerivPairing s φ = (-1)^s φ^{(s)}(0)` (2.6.19).
* `repeatedTailIntegral n f t` (2.6.15) and `remainderPairing n f φ` (2.6.16).
* `riemannLiouvilleIntegral μ f x` (2.6.33) and `halfLineConvolution f g x` (2.6.34).
* `kPlusPairing n f φ = ⟨Dⁿ f, φ⟩` for the elements `Dⁿ f` of `K⁺` (2.6.37).
-/

@[expose] public noncomputable section

open MeasureTheory Set Real

namespace DLMF.AsymptoticApproximations

/-- The **Stieltjes transform** `𝒮f(z) = ∫₀^∞ f(t)/(t+z) dt` (DLMF 2.6.8). For `f` locally
integrable on `[0, ∞)` with `f(t) = O(t^{-α})`, `α > 0`, at infinity, the integral converges
for `z ∉ (-∞, 0]`; outside its domain of convergence the value is Lean's totalized integral. -/
@[dlmf 2.6.E8]
def stieltjesTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), f t / ((t : ℂ) + z)

/-- The **generalized Stieltjes transform** `∫₀^∞ f(t)/(t+z)^ρ dt`, `ρ > 0` (DLMF 2.6.32),
with the principal branch of `(t+z)^ρ` (`z ∉ (-∞, 0]`). -/
@[dlmf 2.6.E32]
def generalizedStieltjesTransform (ρ : ℝ) (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), f t / ((t : ℂ) + z) ^ (ρ : ℂ)

/-- The distribution `⟨f, φ⟩ = ∫₀^∞ f(t) φ(t) dt` associated with a function `f` locally
integrable on `[0, ∞)` (DLMF 2.6.11; for `f = t^{-α}`, `0 < α < 1`, this is 2.6.12). -/
@[dlmf 2.6.E11, dlmf 2.6.E12]
def functionPairing (f : ℝ → ℂ) (φ : ℝ → ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), f t * φ t

/-- The distribution assigned to `t^{-s-α}`, `0 < α < 1`, `s = 0, 1, 2, …` (DLMF 2.6.13):
`⟨t^{-s-α}, φ⟩ = (α)_s⁻¹ ∫₀^∞ t^{-α} φ^{(s)}(t) dt`, with `(α)_s = α(α+1)⋯(α+s-1)`. For `s = 0`
this is the pairing 2.6.12 with the locally integrable function `t^{-α}`. -/
@[dlmf 2.6.E13]
def powPairing (α : ℝ) (s : ℕ) (φ : ℝ → ℂ) : ℂ :=
  (((ascPochhammer ℝ s).eval α : ℝ) : ℂ)⁻¹ *
    ∫ t in Ioi (0 : ℝ), ((t ^ (-α) : ℝ) : ℂ) * iteratedDeriv s φ t

/-- The distribution assigned to `t^{-s-1}`, `s = 0, 1, 2, …` (DLMF 2.6.14):
`⟨t^{-s-1}, φ⟩ = -(1/s!) ∫₀^∞ (ln t) φ^{(s+1)}(t) dt`. -/
@[dlmf 2.6.E14]
def logPowPairing (s : ℕ) (φ : ℝ → ℂ) : ℂ :=
  -((s.factorial : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), ((Real.log t : ℝ) : ℂ) * iteratedDeriv (s + 1) φ t)

/-- The distribution `t^λ`, `t > 0`, for real `λ`, as defined by DLMF 2.6.12–2.6.14 according
to the value of `λ`: for `λ > -1` it is the locally integrable function `t^λ` (2.6.11); for a
negative integer `λ = -s-1` it is `logPowPairing s` (2.6.14); otherwise `λ = -s-α` with
`s = ⌊-λ⌋` and `0 < α < 1`, and it is `powPairing α s` (2.6.13). -/
@[dlmf 2.6.E12, dlmf 2.6.E13, dlmf 2.6.E14]
def tPowPairing (lam : ℝ) (φ : ℝ → ℂ) : ℂ :=
  if -1 < lam then functionPairing (fun t => ((t ^ lam : ℝ) : ℂ)) φ
  else if lam = ⌊lam⌋ then logPowPairing (Int.toNat (-⌊lam⌋ - 1)) φ
  else powPairing (-lam - ⌊-lam⌋) (Int.toNat ⌊-lam⌋) φ

/-- The derivatives of the Dirac delta, `⟨δ^{(s)}, φ⟩ = (-1)^s φ^{(s)}(0)` (DLMF 2.6.19). -/
@[dlmf 2.6.E19]
def diracDerivPairing (s : ℕ) (φ : ℝ → ℂ) : ℂ :=
  (-1 : ℂ) ^ s * iteratedDeriv s φ 0

/-- The `n`th repeated tail integral of `f` (DLMF 2.6.15):
`f_{n,n}(t) = (-1)ⁿ/(n-1)! ∫_t^∞ (τ-t)^{n-1} f(τ) dτ`; its `n`th derivative is `f`
(DLMF §1.4(v)). Intended for `n ≥ 1`; for `n = 0` the formula gives `∫_t^∞ f`. -/
@[dlmf 2.6.E15]
def repeatedTailIntegral (n : ℕ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (-1 : ℂ) ^ n / ((n - 1).factorial : ℂ) * ∫ τ in Ioi t, ((τ - t) ^ (n - 1) : ℝ) * f τ

/-- The distribution associated with the remainder `f_n` (DLMF 2.6.16):
`⟨f_n, φ⟩ = (-1)ⁿ ∫₀^∞ f_{n,n}(t) φ^{(n)}(t) dt`, with `f_{n,n}` the repeated tail
integral 2.6.15. -/
@[dlmf 2.6.E16]
def remainderPairing (n : ℕ) (f : ℝ → ℂ) (φ : ℝ → ℂ) : ℂ :=
  (-1 : ℂ) ^ n * ∫ t in Ioi (0 : ℝ), repeatedTailIntegral n f t * iteratedDeriv n φ t

/-- The test functions `φ_ε(t) = e^{-εt}/(t+z)` of DLMF 2.6.22 (used for `t > 0`,
`ε > 0` and `z ∉ (-∞, 0]`). -/
@[dlmf 2.6.E22]
def stieltjesTestFunction (ε : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(ε * t : ℂ)) / ((t : ℂ) + z)

/-- The **Riemann–Liouville fractional integral** of order `μ > 0` (DLMF 2.6.33, §1.15(vi)):
`I^μ f(x) = Γ(μ)⁻¹ ∫₀^x (x-t)^{μ-1} f(t) dt`. -/
@[dlmf 2.6.E33]
def riemannLiouvilleIntegral (μ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.Gamma μ : ℂ)⁻¹ * ∫ t in (0 : ℝ)..x, (((x - t) ^ (μ - 1) : ℝ) : ℂ) * f t

/-- The convolution product `(f ∗ g)(x) = ∫₀^x f(x-t) g(t) dt` of two functions locally
integrable on `[0, ∞)` (DLMF 2.6.34). -/
@[dlmf 2.6.E34]
def halfLineConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..x, f (x - t) * g t

/-- The value `⟨Dⁿ f, φ⟩ = (-1)ⁿ ∫₀^∞ f(t) φ^{(n)}(t) dt` of the element `Dⁿ f` of the space
`K⁺` of DLMF §2.6(iii), for `f` locally integrable and vanishing on `(-∞, 0]` (only the values
of `f` on `(0, ∞)` enter). The convolution of DLMF 2.6.37 acts on representatives,
`Dⁿ f ∗ Dᵐ g = D^{n+m} (f ∗ g)` (`halfLineConvolution`). -/
@[dlmf 2.6.iii]
def kPlusPairing (n : ℕ) (f : ℝ → ℂ) (φ : ℝ → ℂ) : ℂ :=
  (-1 : ℂ) ^ n * ∫ t in Ioi (0 : ℝ), f t * iteratedDeriv n φ t

/-- The standing hypotheses of DLMF §2.6(ii): `f` is locally integrable on `[0, ∞)` and has
the asymptotic expansion `f(t) ∼ ∑ a_s t^{-s-α}` as `t → +∞` (DLMF 2.6.9), that is, for every
`n` the remainder `f_n(t) = f(t) - ∑_{s<n} a_s t^{-s-α}` (DLMF 2.6.10) is `O(t^{-n-α})`. The
exponent satisfies `0 < α ≤ 1`. -/
@[dlmf 2.6.E9, dlmf 2.6.E10]
structure IsStieltjesExpansion (f : ℝ → ℂ) (α : ℝ) (a : ℕ → ℂ) : Prop where
  /-- The Stieltjes exponent is strictly positive. -/
  alpha_pos : 0 < α
  /-- The Stieltjes exponent is at most one. -/
  alpha_le_one : α ≤ 1
  /-- The remainder kernel is locally integrable on its prescribed domain. -/
  locallyIntegrable : ∀ R : ℝ, 0 < R → IntegrableOn f (Ioc 0 R)
  /-- At positive infinity, the remainder after n terms is `O(t^(-n-α))`. -/
  expansion : ∀ n : ℕ, (fun t : ℝ => f t - ∑ s ∈ Finset.range n, a s * ((t ^ (-(s + α)) : ℝ) : ℂ))
    =O[Filter.atTop] (fun t : ℝ => t ^ (-(n + α)))

/-- The remainder `f_n(t) = f(t) - ∑_{s<n} a_s t^{-s-α}` of DLMF 2.6.10. -/
@[dlmf 2.6.E10]
def stieltjesRemainder (f : ℝ → ℂ) (α : ℝ) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  f t - ∑ s ∈ Finset.range n, a s * ((t ^ (-(s + α)) : ℝ) : ℂ)

/-- The remainder term `R_n(z) = (-1)ⁿ z⁻ⁿ ∫₀^∞ τⁿ f_n(τ)/(τ+z) dτ` of DLMF 2.6.30. -/
@[dlmf 2.6.E30]
def stieltjesRemainderTerm (fn : ℝ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ n / z ^ n * ∫ τ in Ioi (0 : ℝ), ((τ ^ n : ℝ) : ℂ) * fn τ / ((τ : ℂ) + z)

/-- `M` is an analytic continuation of the Mellin transform of `f` to the open preconnected set
`U` (DLMF §2.5(ii)): `M` is holomorphic on `U`, and on a nonempty open subset `V ⊆ U` the Mellin
integral of `f` converges and equals `M`. By the identity theorem `M` is then unique on `U`. -/
def IsMellinContinuationOn (f : ℝ → ℂ) (M : ℂ → ℂ) (U : Set ℂ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧ DifferentiableOn ℂ M U ∧
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ z ∈ V, MellinConvergent f z ∧ M z = mellin f z

/-- The convolution integral `I(x) = ∫₀^∞ f(t) h(xt) dt` of DLMF 2.6.54. -/
@[dlmf 2.6.E54]
def mellinConvolutionIntegral (f h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), f t * h (x * t)

section

open Filter Asymptotics Finset
open scoped Nat Topology

/-- The product `2 · 5 ⋯ (3s-1)` of DLMF 2.6.7. -/
def g2b_prod25 (s : ℕ) : ℝ := ∏ k ∈ Icc 1 s, (3 * (k : ℝ) - 1)

/-- The integral `S(x) = ∫₀^∞ (1+t)^{-1/3}/(x+t) dt` of DLMF 2.6.1, a Stieltjes transform. -/
@[dlmf 2.6.E1]
def stieltjesCubeRootExample (x : ℝ) : ℂ :=
  stieltjesTransform (fun t => (((1 + t) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)) x

/-- The first sum of DLMF 2.6.6–2.6.7, `(2π/√3) ∑_{s<n} (-1)^s (-1/3 choose s) x^{-s-1/3}`. -/
def g2b_naiveSum (n : ℕ) (x : ℝ) : ℝ :=
  2 * π / √3 * ∑ s ∈ range n, (-1) ^ s * Ring.choose (-(1 / 3) : ℝ) s * x ^ (-(s : ℝ) - 1 / 3)

/-- The second sum of DLMF 2.6.7, `∑_{s=1}^{n} 3^s (s-1)!/(2·5⋯(3s-1)) x^{-s}`. -/
def g2b_missingSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ s ∈ Icc 1 n, 3 ^ s * ((s - 1)! : ℝ) / g2b_prod25 s * x ^ (-(s : ℝ))

/-- The coefficients `c_s = (-1)^s/(s-1)! · 𝓜f(s)` of DLMF 2.6.18, where `M` is the Mellin
transform of `f` or its analytic continuation. -/
@[dlmf 2.6.E18]
def stieltjesDeltaCoeff (M : ℂ → ℂ) (s : ℕ) : ℂ :=
  (-1 : ℂ) ^ s / ((s - 1)! : ℂ) * M s

/-- The constants `d̃_s = lim_{z → s+1} (𝓜f(z) + a_s/(z-s-1))` of DLMF 2.6.29. -/
@[dlmf 2.6.E29]
def stieltjesLogCoeff (M : ℂ → ℂ) (a : ℕ → ℂ) (s : ℕ) : ℂ :=
  limUnder (𝓝[≠] ((s : ℂ) + 1)) (fun z => M z + a s / (z - (s + 1)))

/-- The coefficients `d_{s+1}` of DLMF 2.6.21:
`(-1)^{s+1} d_{s+1} = (a_s/s!) ∑_{k=1}^{s} 1/k + (1/s!) d̃_s`. -/
@[dlmf 2.6.E21]
def stieltjesLogDeltaCoeff (M : ℂ → ℂ) (a : ℕ → ℂ) (s : ℕ) : ℂ :=
  (-1 : ℂ) ^ s * (a s / (s ! : ℂ) * (harmonic s : ℂ) + stieltjesLogCoeff M a s / (s ! : ℂ))

/-- The analytic continuation hypothesis on `M`: holomorphic on `ℜz > 0` minus the points
`k + α` (`k = 0, 1, …`), and equal to the Mellin transform `𝓜f(z)` on the strip of convergence
`0 < ℜz < α` (DLMF §2.5(ii)). -/
def IsMellinContinuation (f : ℝ → ℂ) (α : ℝ) (M : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ M {z : ℂ | 0 < z.re ∧ ∀ k : ℕ, z ≠ (k : ℂ) + α} ∧
    ∀ z : ℂ, 0 < z.re → z.re < α → M z = mellin f z

end

section

open Filter Finset

/-- Smooth compactly supported test functions on `ℝ`. -/
def IsCompactTest (u : ℝ → ℂ) : Prop := ContDiff ℝ ⊤ u ∧ HasCompactSupport u

/-- The power kernel `t ↦ t^{μ-1}` (real power, cast to `ℂ`). -/
def g2b_powKernel (μ : ℝ) (t : ℝ) : ℂ := ((t ^ (μ - 1) : ℝ) : ℂ)

/-- The function `t^μ (ln t - γ - ψ(μ+1))` of DLMF 2.6.40, 2.6.44 and 2.6.46. -/
def g2b_logKernel (μ : ℝ) (t : ℝ) : ℂ :=
  ((t ^ μ : ℝ) : ℂ) * ((Real.log t : ℂ) - Real.eulerMascheroniConstant -
    Complex.digamma (μ + 1))

/-- The `j`th repeated integral `f_{n,j}` of `f_n` (DLMF 2.6.47; `f_{n,0} = f_n`). -/
def g2b_repeated (j : ℕ) (fn : ℝ → ℂ) (t : ℝ) : ℂ :=
  if j = 0 then fn t else repeatedTailIntegral j fn t

/-- The remainder `δ_n(x) = ∑_{j=0}^{n} (n choose j) Γ(μ+1)/Γ(μ+1-j) I^μ(t^{n-j} f_{n,j})(x)`
of DLMF 2.6.47. -/
@[dlmf 2.6.E47]
def fractionalRemainder (μ : ℝ) (fn : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range (n + 1), ((n.choose j : ℝ) * (Real.Gamma (μ + 1) / Real.Gamma (μ + 1 - j)) : ℝ) *
    riemannLiouvilleIntegral μ (fun t => ((t ^ (n - j) : ℝ) : ℂ) * g2b_repeated j fn t) x

/-- The function `f(t) = t^{1-α}/(1+t)` of the example in DLMF §2.6(iii). -/
def g2b_exampleF (α : ℝ) (t : ℝ) : ℂ := ((t ^ (1 - α) / (1 + t) : ℝ) : ℂ)

end

end DLMF.AsymptoticApproximations
