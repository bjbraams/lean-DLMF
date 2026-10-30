/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenExpansion
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenFinite

/-!
# Differential equations with a parameter (DLMF §2.8)

Uniform asymptotic solutions of `w'' = (u² f(z) + g(z)) w` (2.8.1) for large `u`.

* §2.8(i): the Liouville transformation 2.8.2–2.8.4 and the normalizations 2.8.5–2.8.8 of the
  three cases; the Bessel-type approximating equation 2.8.9.
* §2.8(ii), Case I (no transition points): the expansions 2.8.10–2.8.13, proved for real `ξ`
  as corollaries of DLMFMathlib's Liouville–Green expansions with error bounds
  (`LiouvilleGreen.lg2_exists_solution_expansion_exp_dom` and
  `LiouvilleGreen.exists_solution_expansion_exp`, Olver Ch. 10, Thm. 3.1) with amplitude `1`;
  they are stronger than DLMF in that the error bounds are explicit.
* §2.8(iii), Case II (simple turning point, Airy functions): 2.8.14–2.8.18, 2.8.22–2.8.23.
* §2.8(iv), Case III (simple pole, Bessel functions): 2.8.24–2.8.31, 2.8.35–2.8.36.

The approximants are DLMF's `Ai`, `Bi` (`DLMF.Airy.airyAi`, …), `I_ν`, `K_ν`
(`DLMF.Bessel.besselI`, `DLMF.Bessel.besselK`), `J_ν` (Mathlib's `Complex.besselJ`) and `Y_ν`
(`DLMF.Bessel.besselY`), evaluated at real arguments. "As `u → ∞`, uniformly in `ξ`" is
expressed by explicit constants: `∃ C U₀, ∀ u ≥ U₀, ∀ ξ, |error| ≤ C u^{-k}`. The uniform
expansions are also differentiable in `ξ` (DLMF); differentiability is not formalized.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics MeasureTheory
open scoped Topology

namespace DLMF.AsymptoticApproximations

open LiouvilleGreen

/-! ### §2.8(i) Liouville transformation and classification of cases -/

/-- DLMF 2.8.2–2.8.4 (the Liouville transformation, real form): let `z = Z(ξ)` with `Z' > 0`,
and let `w` solve `w'' = (u² f + g) w` (2.8.1) near `Z(ξ)`. Then `W = ż^{-1/2} w` satisfies
`W'' = (u² ż² f(z) + ψ(ξ)) W` with `ψ = ż² g(z) + ż^{1/2} (ż^{-1/2})''` (dots are
`d/dξ`). Here `A = ż^{-1/2}`, `A'` and `A''` are its first two derivatives, so
`ż^{1/2} (ż^{-1/2})'' = A''/A`. -/
@[dlmf 2.8.E1, dlmf 2.8.E2, dlmf 2.8.E3, dlmf 2.8.E4]
theorem liouville_transformation {u : ℝ} {f g w w' Z Z' Z'' A' A'' : ℝ → ℝ} {S : Set ℝ}
    (hZ : ∀ ξ ∈ S, HasDerivAt Z (Z' ξ) ξ) (hZ' : ∀ ξ ∈ S, HasDerivAt Z' (Z'' ξ) ξ)
    (hpos : ∀ ξ ∈ S, 0 < Z' ξ)
    (hA' : ∀ ξ ∈ S, A' ξ = -(1 / 2) * Z' ξ ^ (-(3 / 2) : ℝ) * Z'' ξ)
    (hA'' : ∀ ξ ∈ S, HasDerivAt A' (A'' ξ) ξ)
    (hw : ∀ ξ ∈ S, HasDerivAt w (w' (Z ξ)) (Z ξ))
    (hw' : ∀ ξ ∈ S, HasDerivAt w' ((u ^ 2 * f (Z ξ) + g (Z ξ)) * w (Z ξ)) (Z ξ)) :
    ∃ W' : ℝ → ℝ, ∀ ξ ∈ S,
      HasDerivAt (fun ξ => Z' ξ ^ (-(1 / 2) : ℝ) * w (Z ξ)) (W' ξ) ξ ∧
      HasDerivAt W' ((u ^ 2 * Z' ξ ^ 2 * f (Z ξ) +
          (Z' ξ ^ 2 * g (Z ξ) + A'' ξ / Z' ξ ^ (-(1 / 2) : ℝ))) *
        (Z' ξ ^ (-(1 / 2) : ℝ) * w (Z ξ))) ξ := by
  sorry

/-- DLMF 2.8.5 (Case I): with `ξ = ∫ f^{1/2} dz`, `ż² f(z) = 1`, where `ż = 1/ξ'(z)`; the
transformed equation is 2.8.8 with `m = 0`. -/
@[dlmf 2.8.E5, dlmf 2.8.E8, dlmf 2.8.i]
theorem liouville_caseI {f ξ : ℝ → ℝ} {z : ℝ} (hf : 0 < f z)
    (_hξ : HasDerivAt ξ (√(f z)) z) :
    (√(f z))⁻¹ ^ 2 * f z = 1 := by
  rw [inv_pow, Real.sq_sqrt hf.le, inv_mul_cancel₀ hf.ne']

/-- DLMF 2.8.6 (Case II): if `(2/3) ξ^{3/2} = ∫_{z₀}^z f^{1/2}`, that is, `(2/3) ξ^{3/2}` has
derivative `f^{1/2}` in `z`, and `ξ > 0` with `ξ'(z) = d`, then `ż² f(z) = ξ` with
`ż = 1/d`; the transformed equation is 2.8.8 with `m = 1`. -/
@[dlmf 2.8.E6, dlmf 2.8.E8]
theorem liouville_caseII {f ξ : ℝ → ℝ} {z d : ℝ} (hf : 0 < f z) (hξp : 0 < ξ z)
    (hξ : HasDerivAt ξ d z)
    (hF : HasDerivAt (fun z => 2 / 3 * ξ z ^ (3 / 2 : ℝ)) (√(f z)) z) :
    d⁻¹ ^ 2 * f z = ξ z := by
  have h1 := (hξ.rpow_const (p := 3 / 2) (Or.inl hξp.ne')).const_mul (2 / 3)
  have h2 := hF.unique h1
  have e : ξ z ^ ((3 / 2 : ℝ) - 1) = √(ξ z) := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [e] at h2
  have hs : 0 < √(ξ z) := Real.sqrt_pos.2 hξp
  have hd : d = √(f z) / √(ξ z) := by
    field_simp
    linarith
  have hfs : 0 < √(f z) := Real.sqrt_pos.2 hf
  rw [hd, inv_div, div_pow, Real.sq_sqrt hf.le, Real.sq_sqrt hξp.le]
  field_simp

/-- DLMF 2.8.7 (Case III): if `2 ξ^{1/2} = ∫_{z₀}^z f^{1/2}`, that is, `2 ξ^{1/2}` has
derivative `f^{1/2}` in `z`, and `ξ > 0` with `ξ'(z) = d`, then `ż² f(z) = 1/ξ` with `ż = 1/d`;
the transformed equation is 2.8.8 with `m = -1`. -/
@[dlmf 2.8.E7, dlmf 2.8.E8]
theorem liouville_caseIII {f ξ : ℝ → ℝ} {z d : ℝ} (hf : 0 < f z) (hξp : 0 < ξ z)
    (hξ : HasDerivAt ξ d z)
    (hF : HasDerivAt (fun z => 2 * ξ z ^ (1 / 2 : ℝ)) (√(f z)) z) :
    d⁻¹ ^ 2 * f z = 1 / ξ z := by
  have h1 := (hξ.rpow_const (p := 1 / 2) (Or.inl hξp.ne')).const_mul 2
  have h2 := hF.unique h1
  have e : ξ z ^ ((1 / 2 : ℝ) - 1) = (√(ξ z))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hξp.le]; norm_num
  rw [e] at h2
  have hs : 0 < √(ξ z) := Real.sqrt_pos.2 hξp
  have hd : d = √(f z) * √(ξ z) := by
    field_simp at h2
    linarith
  rw [hd, inv_pow, mul_pow, Real.sq_sqrt hf.le, Real.sq_sqrt hξp.le]
  field_simp

/-- DLMF 2.8.9: the Case III approximating equation `W'' = (u²/ξ + ρ/ξ²) W` has the solutions
`ξ^{1/2} I_ν(2uξ^{1/2})` and `ξ^{1/2} K_ν(2uξ^{1/2})` for `ξ > 0`, with `ν = (1 + 4ρ)^{1/2}`
(equivalently `ν² = 1 + 4ρ`). -/
@[dlmf 2.8.E9]
theorem bessel_approximating_equation {u ρ ν : ℝ} (hν : ν ^ 2 = 1 + 4 * ρ) :
    (∃ W' : ℝ → ℂ, ∀ ξ : ℝ, 0 < ξ →
      HasDerivAt (fun ξ : ℝ => ((√ξ : ℝ) : ℂ) * DLMF.Bessel.besselI ν (2 * u * √ξ)) (W' ξ) ξ ∧
      HasDerivAt W' ((u ^ 2 / ξ + ρ / ξ ^ 2 : ℝ) *
        (((√ξ : ℝ) : ℂ) * DLMF.Bessel.besselI ν (2 * u * √ξ))) ξ) ∧
    (∃ W' : ℝ → ℂ, ∀ ξ : ℝ, 0 < ξ →
      HasDerivAt (fun ξ : ℝ => ((√ξ : ℝ) : ℂ) * DLMF.Bessel.besselK ν (2 * u * √ξ)) (W' ξ) ξ ∧
      HasDerivAt W' ((u ^ 2 / ξ + ρ / ξ ^ 2 : ℝ) *
        (((√ξ : ℝ) : ℂ) * DLMF.Bessel.besselK ν (2 * u * √ξ))) ξ) := by
  sorry

/-! ### §2.8(ii) Case I: no transition points -/

/-- `lgSeries (-u)` is the series `∑_{s<n} A_s/u^s` of DLMF 2.8.11. -/
lemma g2b_lgSeries_neg (u : ℝ) (As : ℕ → ℝ → ℝ) (n : ℕ) (y : ℝ) :
    lgSeries (-u) As n y = ∑ s ∈ Finset.range n, As s y / u ^ s := by
  unfold lgSeries
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [neg_pow u, mul_div_mul_left _ _ (pow_ne_zero s (by norm_num : (-1 : ℝ) ≠ 0))]

/-- `lgSeries u` is the series `∑_{s<n} (-1)^s A_s/u^s` of DLMF 2.8.12. -/
lemma g2b_lgSeries_pos (u : ℝ) (As : ℕ → ℝ → ℝ) (n : ℕ) (y : ℝ) :
    lgSeries u As n y = ∑ s ∈ Finset.range n, (-1) ^ s * As s y / u ^ s := rfl

/-- DLMF 2.8.10–2.8.11 with 2.8.13 (Case I, `j = 1`, real `ξ`): let `S` be an open interval
containing the reference point `α₁`, `ψ` continuous on `S`, and let `A_0 = 1`, `A_1, …, A_n`
satisfy `A_{s+1}' = -½ A_s'' + ½ ψ A_s` (2.8.13 differentiated). Then for `u > 0` the equation
`W'' = (u² + ψ) W` has a solution
`W_{n,1}(u, ξ) = e^{uξ} (∑_{s<n} A_s(ξ)/u^s + ε(u, ξ))` on `S ∩ (α₁, ∞)` with
`|ε| ≤ u^{-n} 𝒱_{α₁,ξ}(A_n) exp(𝒱_{α₁,ξ}(ψ)/(2u))`; in particular `ε = O(u^{-n})` uniformly
where the variations are bounded. Stronger than DLMF (explicit error bound). -/
@[dlmf 2.8.E10, dlmf 2.8.E11, dlmf 2.8.E13, dlmf 2.8.ii]
theorem caseI_dominant_expansion {S : Set ℝ} {α₁ u : ℝ} (hS : IsOpen S) (hSc : S.OrdConnected)
    (ha : α₁ ∈ S) (hu : 0 < u) {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ S) {n : ℕ}
    {As Ad Ad2 : ℕ → ℝ → ℝ}
    (hAs : ∀ s < n, ∀ x ∈ S, HasDerivAt (As s) (Ad s x) x)
    (hAd : ∀ s < n, ∀ x ∈ S, HasDerivAt (Ad s) (Ad2 s x) x)
    (hAd2c : ∀ s < n, ContinuousOn (Ad2 s) S) (h0 : ∀ x ∈ S, Ad 0 x = 0)
    (hrec : ∀ s < n, ∀ x ∈ S, Ad (s + 1) x = -(1 / 2) * Ad2 s x + 1 / 2 * ψ x * As s x) :
    ∃ ε ε' W' : ℝ → ℝ, ∀ x ∈ S, α₁ < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => Real.exp (u * y) *
        (∑ s ∈ Finset.range n, As s y / u ^ s + ε y)) (W' x) x ∧
      HasDerivAt W' ((u ^ 2 + ψ x) *
        (Real.exp (u * x) * (∑ s ∈ Finset.range n, As s x / u ^ s + ε x))) x ∧
      |ε x| ≤ (∫ t in α₁..x, |Ad n t|) / u ^ n * Real.exp ((∫ t in α₁..x, |ψ t|) / (2 * u)) := by
  obtain ⟨ε, ε', W', H⟩ := lg2_exists_solution_expansion_exp_dom hS hSc ha hu
    (A := fun _ => 1) (A' := fun _ => 0) (A'' := fun _ => 0) (ξ := id) (g := ψ)
    (fun _ _ => one_ne_zero) (fun x _ => hasDerivAt_const x 1) (fun x _ => hasDerivAt_const x 0)
    continuousOn_const hψ (fun x _ => by simpa using hasDerivAt_id x) hAs hAd hAd2c h0
    (fun s hs x hx => by rw [hrec s hs x hx]; ring)
  refine ⟨ε, ε', W', fun x hx hax => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := H x hx hax
  have hsum : ∀ y, lgSeries (-u) As n y = ∑ s ∈ Finset.range n, As s y / u ^ s :=
    g2b_lgSeries_neg u As n
  simp only [hsum, one_mul, id, one_pow, inv_one, mul_one] at h2 h3
  refine ⟨h1, h2, h3, ?_⟩
  have hV : (∫ t in α₁..x, |(1 : ℝ) * 0 - ψ t * 1 ^ 2|) = ∫ t in α₁..x, |ψ t| := by
    congr 1; funext t; simp
  rw [hV] at h4
  exact h4

/-- DLMF 2.8.12 with 2.8.13 (Case I, `j = 2`, real `ξ`, reference point `α₂ = +∞`): for `u > 0`
the equation `W'' = (u² + ψ) W` on `(a, ∞)` has a solution
`W_{n,2}(u, ξ) = e^{-uξ} (∑_{s<n} (-1)^s A_s(ξ)/u^s + ε(u, ξ))` with
`|ε| ≤ u^{-n} 𝒱_{ξ,∞}(A_n) exp(𝒱_{ξ,∞}(ψ)/(2u))`. Stronger than DLMF (explicit bound). -/
@[dlmf 2.8.E12, dlmf 2.8.E13, dlmf 2.8.ii]
theorem caseI_recessive_expansion {a u : ℝ} (hu : 0 < u) {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Ioi a)) (hψi : ∀ c, a < c → IntegrableOn (fun t => |ψ t|) (Ioi c))
    {n : ℕ} {As Ad Ad2 : ℕ → ℝ → ℝ}
    (hAs : ∀ s < n, ∀ x, a < x → HasDerivAt (As s) (Ad s x) x)
    (hAd : ∀ s < n, ∀ x, a < x → HasDerivAt (Ad s) (Ad2 s x) x)
    (hAd2c : ∀ s < n, ContinuousOn (Ad2 s) (Ioi a)) (h0 : ∀ x, a < x → Ad 0 x = 0)
    (hrec : ∀ s < n, ∀ x, a < x → Ad (s + 1) x = -(1 / 2) * Ad2 s x + 1 / 2 * ψ x * As s x)
    (hAni : ∀ c, a < c → IntegrableOn (fun t => |Ad n t|) (Ioi c)) :
    ∃ ε ε' W' : ℝ → ℝ, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => Real.exp (-(u * y)) *
        (∑ s ∈ Finset.range n, (-1) ^ s * As s y / u ^ s + ε y)) (W' x) x ∧
      HasDerivAt W' ((u ^ 2 + ψ x) * (Real.exp (-(u * x)) *
        (∑ s ∈ Finset.range n, (-1) ^ s * As s x / u ^ s + ε x))) x ∧
      |ε x| ≤ (∫ t in Ioi x, |Ad n t|) / u ^ n *
        Real.exp ((∫ t in Ioi x, |ψ t|) / (2 * u)) := by
  obtain ⟨ε, ε', W', H⟩ := exists_solution_expansion_exp (a := a) hu
    (A := fun _ => 1) (A' := fun _ => 0) (A'' := fun _ => 0) (ξ := id) (g := ψ)
    (fun _ _ => one_ne_zero) (fun x _ => hasDerivAt_const x 1) (fun x _ => hasDerivAt_const x 0)
    continuousOn_const hψ (fun x _ => by simpa using hasDerivAt_id x)
    (fun c hc => by simpa using hψi c hc) hAs hAd hAd2c h0
    (fun s hs x hx => by rw [hrec s hs x hx]; ring) hAni
  refine ⟨ε, ε', W', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := H x hx
  simp only [g2b_lgSeries_pos, one_mul, id, one_pow, inv_one, mul_one] at h2 h3
  refine ⟨h1, h2, h3, ?_⟩
  have hV : (∫ t in Ioi x, |(1 : ℝ) * 0 - ψ t * 1 ^ 2|) = ∫ t in Ioi x, |ψ t| := by
    congr 1; funext t; simp
  rw [hV] at h4
  exact h4

/-! ### §2.8(iii) Case II: simple turning point -/

/-- DLMF 2.8.14–2.8.18 (Case II, simple turning point): for `W'' = (u²ξ + ψ(ξ)) W` on
`(α₁, α₂)`, `α₁ < 0 < α₂`, `ψ` smooth, with coefficients as in 2.8.17–2.8.18 and finite
variations `𝒱(|ξ|^{1/2} B_0)`, `𝒱(|ξ|^{1/2} B_{n-1})`, there are solutions
`W_{n,1} = Ai(u^{2/3}ξ)(∑_{s<n} A_s u^{-2s} + O(u^{1-2n}))
  + Ai'(u^{2/3}ξ)(∑_{s<n-1} B_s u^{-2s-4/3} + O(u^{1-2n}))`
and the same with `Bi` (`W_{n,2}`), uniformly in `ξ`. -/
@[dlmf 2.8.E14, dlmf 2.8.E15, dlmf 2.8.E16, dlmf 2.8.E17, dlmf 2.8.E18, dlmf 2.8.iii]
theorem caseII_airy_expansion {α₁ α₂ : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) {ψ : ℝ → ℝ}
    (hψ : ContDiffOn ℝ ⊤ ψ (Ioo α₁ α₂)) {A Ad Ad2 B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsAiryCoeffs ψ α₁ α₂ A Ad Ad2 B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √|v| * B s v) ξ|) (Ioo α₁ α₂)) :
    ∃ W₁ W₂ : ℝ → ℝ → ℂ, ∃ e₁ e₂ e₃ e₄ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₁' W₂' : ℝ → ℂ, ∀ ξ ∈ Ioo α₁ α₂,
        HasDerivAt (W₁ u) (W₁' ξ) ξ ∧ HasDerivAt W₁' ((u ^ 2 * ξ + ψ ξ : ℝ) * W₁ u ξ) ξ ∧
        HasDerivAt (W₂ u) (W₂' ξ) ξ ∧ HasDerivAt W₂' ((u ^ 2 * ξ + ψ ξ : ℝ) * W₂ u ξ) ξ) ∧
      (∀ u, 0 < u → ∀ ξ ∈ Ioo α₁ α₂,
        W₁ u ξ = DLMF.Airy.airyAi ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            ((∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) + e₁ u ξ) +
          DLMF.Airy.airyAiDeriv ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            ((∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 4 / 3 : ℝ) : ℝ) + e₂ u ξ) ∧
        W₂ u ξ = DLMF.Airy.airyBi ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            ((∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) + e₃ u ξ) +
          DLMF.Airy.airyBiDeriv ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            ((∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 4 / 3 : ℝ) : ℝ) + e₄ u ξ)) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo α₁ α₂,
        ‖e₁ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧ ‖e₂ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧
        ‖e₃ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧ ‖e₄ u ξ‖ ≤ C / u ^ (2 * n - 1) := by
  sorry

/-- DLMF 2.8.22–2.8.23 (Case II with envelope functions): with the solutions of
`caseII_airy_expansion`, as `u → ∞` uniformly in `ξ ∈ (α₁, α₂)`,
`W_{n,1} = Ai(u^{2/3}ξ) ∑_{s<n} A_s u^{-2s} + Ai'(u^{2/3}ξ) ∑_{s<n-1} B_s u^{-2s-4/3}
  + envAi(u^{2/3}ξ) O(u^{1-2n})`, and the same with `Bi`, `envBi`. -/
@[dlmf 2.8.E22, dlmf 2.8.E23]
theorem caseII_airy_envelope {α₁ α₂ : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) {ψ : ℝ → ℝ}
    (hψ : ContDiffOn ℝ ⊤ ψ (Ioo α₁ α₂)) {A Ad Ad2 B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsAiryCoeffs ψ α₁ α₂ A Ad Ad2 B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √|v| * B s v) ξ|) (Ioo α₁ α₂)) :
    ∃ W₁ W₂ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₁' W₂' : ℝ → ℂ, ∀ ξ ∈ Ioo α₁ α₂,
        HasDerivAt (W₁ u) (W₁' ξ) ξ ∧ HasDerivAt W₁' ((u ^ 2 * ξ + ψ ξ : ℝ) * W₁ u ξ) ξ ∧
        HasDerivAt (W₂ u) (W₂' ξ) ξ ∧ HasDerivAt W₂' ((u ^ 2 * ξ + ψ ξ : ℝ) * W₂ u ξ) ξ) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo α₁ α₂,
        ‖W₁ u ξ - (DLMF.Airy.airyAi ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) +
          DLMF.Airy.airyAiDeriv ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 4 / 3 : ℝ) : ℝ))‖ ≤
          envAi (u ^ (2 / 3 : ℝ) * ξ) * (C / u ^ (2 * n - 1)) ∧
        ‖W₂ u ξ - (DLMF.Airy.airyBi ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) +
          DLMF.Airy.airyBiDeriv ((u ^ (2 / 3 : ℝ) * ξ : ℝ)) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 4 / 3 : ℝ) : ℝ))‖ ≤
          envBi (u ^ (2 / 3 : ℝ) * ξ) * (C / u ^ (2 * n - 1)) := by
  sorry

/-! ### §2.8(iv) Case III: simple pole -/

/-- DLMF 2.8.24–2.8.28 (Case III, `ξ ∈ (0, α₂)`): for
`W'' = (u²/(4ξ) + (ν²-1)/(4ξ²) + ψ(ξ)/ξ) W`, `ν ≥ 0`, with coefficients as in 2.8.27–2.8.28
and finite variations `𝒱_{0,α₂}(ξ^{1/2} B_0)`, `𝒱_{0,α₂}(ξ^{1/2} B_{n-1})`, there are solutions
`W_{n,1} = ξ^{1/2} I_ν(uξ^{1/2}) ∑_{s<n} A_s u^{-2s} + ξ I_{ν+1}(uξ^{1/2}) ∑_{s<n-1} B_s u^{-2s-1}
  + ξ^{1/2} I_ν(uξ^{1/2}) O(u^{1-2n})` and
`W_{n,2} = ξ^{1/2} K_ν(uξ^{1/2}) ∑ A_s u^{-2s} - ξ K_{ν+1}(uξ^{1/2}) ∑ B_s u^{-2s-1}
  + ξ^{1/2} K_ν(uξ^{1/2}) O(u^{1-2n})`, uniformly in `ξ ∈ (0, α₂)`. -/
@[dlmf 2.8.E24, dlmf 2.8.E25, dlmf 2.8.E26, dlmf 2.8.E27, dlmf 2.8.E28, dlmf 2.8.iv]
theorem caseIII_bessel_expansion_pos {α₁ α₂ ν : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) (hν : 0 ≤ ν)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ ⊤ ψ (Ioo α₁ α₂)) {A Ad B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsBesselCoeffs ψ ν α₁ α₂ A Ad B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √v * B s v) ξ|) (Ioo 0 α₂)) :
    ∃ W₁ W₂ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₁' W₂' : ℝ → ℂ, ∀ ξ ∈ Ioo 0 α₂,
        HasDerivAt (W₁ u) (W₁' ξ) ξ ∧ HasDerivAt W₁'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₁ u ξ) ξ ∧
        HasDerivAt (W₂ u) (W₂' ξ) ξ ∧ HasDerivAt W₂'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₂ u ξ) ξ) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo 0 α₂,
        ‖W₁ u ξ - ((√ξ : ℝ) * DLMF.Bessel.besselI ν (u * √ξ : ℝ) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) +
          (ξ : ℂ) * DLMF.Bessel.besselI (ν + 1) (u * √ξ : ℝ) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ))‖ ≤
          ‖(√ξ : ℝ) * DLMF.Bessel.besselI ν (u * √ξ : ℝ)‖ * (C / u ^ (2 * n - 1)) ∧
        ‖W₂ u ξ - ((√ξ : ℝ) * DLMF.Bessel.besselK ν (u * √ξ : ℝ) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) -
          (ξ : ℂ) * DLMF.Bessel.besselK (ν + 1) (u * √ξ : ℝ) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ))‖ ≤
          ‖(√ξ : ℝ) * DLMF.Bessel.besselK ν (u * √ξ : ℝ)‖ * (C / u ^ (2 * n - 1)) := by
  sorry

/-- DLMF 2.8.29–2.8.31 (Case III, `ξ ∈ (α₁, 0)`): with coefficients as in 2.8.31 and 2.8.28 and
finite variations `𝒱_{α₁,0}(|ξ|^{1/2} B_0)`, `𝒱_{α₁,0}(|ξ|^{1/2} B_{n-1})`, there are solutions
`W_{n,3} = |ξ|^{1/2} J_ν(u|ξ|^{1/2}) (∑_{s<n} A_s u^{-2s} + O(u^{1-2n}))
  - |ξ| J_{ν+1}(u|ξ|^{1/2}) (∑_{s<n-1} B_s u^{-2s-1} + O(u^{2-2n}))`
and the same with `Y_ν`, `Y_{ν+1}` (`W_{n,4}`), uniformly in `ξ ∈ (α₁, 0)`. -/
@[dlmf 2.8.E29, dlmf 2.8.E30, dlmf 2.8.E31]
theorem caseIII_bessel_expansion_neg {α₁ α₂ ν : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) (hν : 0 ≤ ν)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ ⊤ ψ (Ioo α₁ α₂)) {A Ad B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsBesselCoeffs ψ ν α₁ α₂ A Ad B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √|v| * B s v) ξ|) (Ioo α₁ 0)) :
    ∃ W₃ W₄ : ℝ → ℝ → ℂ, ∃ e₁ e₂ e₃ e₄ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₃' W₄' : ℝ → ℂ, ∀ ξ ∈ Ioo α₁ 0,
        HasDerivAt (W₃ u) (W₃' ξ) ξ ∧ HasDerivAt W₃'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₃ u ξ) ξ ∧
        HasDerivAt (W₄ u) (W₄' ξ) ξ ∧ HasDerivAt W₄'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₄ u ξ) ξ) ∧
      (∀ u, 0 < u → ∀ ξ ∈ Ioo α₁ 0,
        W₃ u ξ = (√|ξ| : ℝ) * Complex.besselJ ν (u * √|ξ| : ℝ) *
            ((∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) + e₁ u ξ) -
          ((|ξ| : ℝ) : ℂ) * Complex.besselJ (ν + 1) (u * √|ξ| : ℝ) *
            ((∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ) + e₂ u ξ) ∧
        W₄ u ξ = (√|ξ| : ℝ) * DLMF.Bessel.besselY ν (u * √|ξ| : ℝ) *
            ((∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) + e₃ u ξ) -
          ((|ξ| : ℝ) : ℂ) * DLMF.Bessel.besselY (ν + 1) (u * √|ξ| : ℝ) *
            ((∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ) + e₄ u ξ)) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo α₁ 0,
        ‖e₁ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧ ‖e₂ u ξ‖ ≤ C / u ^ (2 * n - 2) ∧
        ‖e₃ u ξ‖ ≤ C / u ^ (2 * n - 1) ∧ ‖e₄ u ξ‖ ≤ C / u ^ (2 * n - 2) := by
  sorry

/-- DLMF 2.8.35–2.8.36 (Case III, `ξ ∈ (α₁, 0)`, with envelope functions): with the solutions of
`caseIII_bessel_expansion_neg`, uniformly in `ξ ∈ (α₁, 0)` as `u → ∞`,
`W_{n,3} = |ξ|^{1/2} J_ν(u|ξ|^{1/2}) ∑ A_s u^{-2s} - |ξ| J_{ν+1}(u|ξ|^{1/2}) ∑ B_s u^{-2s-1}
  + |ξ|^{1/2} env J_ν(u|ξ|^{1/2}) O(u^{1-2n})`, and the same with `Y`, `env Y_ν`. -/
@[dlmf 2.8.E35, dlmf 2.8.E36]
theorem caseIII_bessel_envelope {α₁ α₂ ν : ℝ} (h₁ : α₁ < 0) (h₂ : 0 < α₂) (hν : 0 ≤ ν)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ ⊤ ψ (Ioo α₁ α₂)) {A Ad B Bd Bd2 : ℕ → ℝ → ℝ}
    (hc : IsBesselCoeffs ψ ν α₁ α₂ A Ad B Bd Bd2) {n : ℕ} (hn : 1 ≤ n)
    (hV : ∀ s ∈ ({0, n - 1} : Finset ℕ), IntegrableOn
      (fun ξ => |deriv (fun v => √|v| * B s v) ξ|) (Ioo α₁ 0)) :
    ∃ W₃ W₄ : ℝ → ℝ → ℂ,
      (∀ u, 0 < u → ∃ W₃' W₄' : ℝ → ℂ, ∀ ξ ∈ Ioo α₁ 0,
        HasDerivAt (W₃ u) (W₃' ξ) ξ ∧ HasDerivAt W₃'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₃ u ξ) ξ ∧
        HasDerivAt (W₄ u) (W₄' ξ) ξ ∧ HasDerivAt W₄'
          ((u ^ 2 / (4 * ξ) + (ν ^ 2 - 1) / (4 * ξ ^ 2) + ψ ξ / ξ : ℝ) * W₄ u ξ) ξ) ∧
      ∃ C U₀ : ℝ, ∀ u, U₀ ≤ u → ∀ ξ ∈ Ioo α₁ 0,
        ‖W₃ u ξ - ((√|ξ| : ℝ) * Complex.besselJ ν (u * √|ξ| : ℝ) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) -
          ((|ξ| : ℝ) : ℂ) * Complex.besselJ (ν + 1) (u * √|ξ| : ℝ) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ))‖ ≤
          √|ξ| * envJ ν (u * √|ξ|) * (C / u ^ (2 * n - 1)) ∧
        ‖W₄ u ξ - ((√|ξ| : ℝ) * DLMF.Bessel.besselY ν (u * √|ξ| : ℝ) *
            (∑ s ∈ Finset.range n, A s ξ / u ^ (2 * s) : ℝ) -
          ((|ξ| : ℝ) : ℂ) * DLMF.Bessel.besselY (ν + 1) (u * √|ξ| : ℝ) *
            (∑ s ∈ Finset.range (n - 1), B s ξ / u ^ (2 * s + 1) : ℝ))‖ ≤
          √|ξ| * envY ν (u * √|ξ|) * (C / u ^ (2 * n - 1)) := by
  sorry

end DLMF.AsymptoticApproximations
