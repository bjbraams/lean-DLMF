/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.UniformCoordinates
public import DLMF.Legendre.IntegralRepresentations
public import DLMF.Hypergeometric.Identities.CarlsonTools
public import DLMF.Hypergeometric.Saalschutz

/-!
# Uniform asymptotic approximations of Legendre functions

Uniform approximations of Ferrers and associated Legendre functions for large order `μ`, for
large degree `ν`, and for both large together (DLMF §14.15), in terms of elementary functions,
Bessel functions and parabolic cylinder functions.

## Main definitions

* `legendreOrderPrefactor`: the leading factor of DLMF 14.15.4.

## Main results

* `ferrersP_large_order_uniform`, `associatedP_large_order_uniform`,
  `olverQ_large_order_uniform`: large `μ` with fixed `ν` (DLMF 14.15.1–14.15.3).
* `ferrersP_two_large_parameters`, `associatedP_two_large_order_uniform`,
  `olverQ_two_large_order_uniform`: large `μ` with `ν + 1/2 ≤ (1-δ)μ`
  (DLMF 14.15.4, 14.15.8, 14.15.9).
* `ferrersP_large_degree_uniform`, `ferrersQ_large_degree_uniform`,
  `associatedP_large_degree_uniform`, `olverQ_large_degree_uniform`: large `ν` with fixed `μ`, in
  terms of Bessel functions (DLMF 14.15.11–14.15.14).
* `ferrersP_two_large_degree_uniform`, `ferrersQ_two_large_degree_uniform`,
  `associatedP_two_large_degree_modified`, `olverQ_two_large_degree_modified`: large `ν` with
  `μ ≤ (1-δ)(ν+1/2)` (DLMF 14.15.15–14.15.18).
* `ferrersP_cylinder_uniform`, `ferrersQ_cylinder_uniform`,
  `ferrersP_cylinder_exponential_uniform`: approximations by parabolic cylinder functions
  (DLMF 14.15.24, 14.15.25, 14.15.30).

## Implementation notes

The `O`-terms are stated with `=O[…]` along filters that encode the uniformity regions; where
DLMF writes `f = g (1 + O(ε))`, the statement bounds `f/g - 1`. Oscillatory error terms are
measured against the Bessel envelope functions `env J_μ`, `env Y_μ`. The coordinates and
envelopes of DLMF §14.15 are defined in `DLMF.Legendre.UniformCoordinates`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

open DLMF.Bessel DLMF.Confluent

/-- `Γ(J+1+μ) (J+k+1)! ≤ Γ(J+k+1+μ) (J+1)!` for `μ ≥ 1`. -/
private theorem LargeOrder.Gamma_mul_factorial_le (J : ℕ) {μ : ℝ} (hμ : 1 ≤ μ) (k : ℕ) :
    Real.Gamma (J + 1 + μ) * ((J + k + 1).factorial : ℝ) ≤
      Real.Gamma (J + k + 1 + μ) * ((J + 1).factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < (J:ℝ) + k + 1 + μ := by positivity
    have hG : 0 < Real.Gamma (J + k + 1 + μ) := Real.Gamma_pos_of_pos hpos
    have e1 : Real.Gamma ((J:ℝ) + (k + 1 : ℕ) + 1 + μ) =
        ((J:ℝ) + k + 1 + μ) * Real.Gamma (J + k + 1 + μ) := by
      rw [show ((J:ℝ) + (k + 1 : ℕ) + 1 + μ) = (J + k + 1 + μ) + 1 by push_cast; ring,
        Real.Gamma_add_one hpos.ne']
    have e2 : ((J + (k + 1) + 1).factorial : ℝ) = ((J:ℝ) + k + 2) * (J + k + 1).factorial := by
      rw [show J + (k + 1) + 1 = (J + k + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [e1, e2]
    have hJ : (0:ℝ) ≤ ((J + 1).factorial : ℝ) := by positivity
    have hΓ : 0 ≤ Real.Gamma (J + 1 + μ) := (Real.Gamma_pos_of_pos (by positivity)).le
    calc Real.Gamma (J + 1 + μ) * (((J:ℝ) + k + 2) * (J + k + 1).factorial)
        = ((J:ℝ) + k + 2) * (Real.Gamma (J + 1 + μ) * (J + k + 1).factorial) := by ring
      _ ≤ ((J:ℝ) + k + 2) * (Real.Gamma (J + k + 1 + μ) * (J + 1).factorial) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ ((J:ℝ) + k + 1 + μ) * (Real.Gamma (J + k + 1 + μ) * (J + 1).factorial) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring

/-- `(2)ₙ = (n+1)!`. -/
private theorem LargeOrder.pochhammer_two (n : ℕ) : pochhammer 2 n = ((n + 1).factorial : ℂ) := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih => rw [pochhammer_succ, ih, Nat.factorial_succ (n + 1)]; push_cast; ring

/-- DLMF 14.15.1: for fixed `ν` and `J ∈ ℕ`, `((1+x)/(1−x))^{μ/2} 𝖯^{−μ}_ν(x) = Σ_{j<J} (ν+1)_j
(−ν)_j/(j! Γ(j+1+μ)) ((1−x)/2)^j + O(1/Γ(J+1+μ))` as `μ → ∞`, uniformly for `-1 < x < 1`. -/
@[dlmf 14.15.E1]
theorem ferrersP_large_order_uniform (ν : ℂ) (J : ℕ) :
    (fun p : ℝ × ℝ => ((1+p.2)/(1-p.2):ℂ)^((p.1:ℂ)/2)*ferrersP ν (-p.1) p.2-∑ j ∈ Finset.range J,
        pochhammer (ν+1) j*pochhammer (-ν) j/((j.factorial:ℂ)*Gamma (j+1+p.1))*((1-p.2)/2:ℂ)^j)
        =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | p.2 ∈ Ioo (-1:ℝ) 1}]
        (fun p : ℝ × ℝ => 1/Gamma (J+1+p.1)) := by
  set gc : ℕ → ℂ := gaussHypergeometricCoeff (ν + 1) (-ν) 2 with hgc
  have hsum : Summable fun n => ‖gc n‖ := by
    have h := CarlsonTheorem.isBigO_gaussHypergeometricCoeff (ν + 1) (-ν) 2 (fun k h => by
      have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    have he : (ν + 1 + -ν - 2 - 1 : ℂ).re = -2 := by ring_nf; simp
    rw [he] at h
    exact summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by norm_num)) h.norm_left
  set C : ℝ := ((J + 1).factorial : ℝ) * ∑' n, ‖gc n‖ with hC
  refine IsBigO.of_bound C ?_
  have h1 : ∀ᶠ p : ℝ × ℝ in comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | p.2 ∈ Ioo (-1:ℝ) 1},
      1 ≤ p.1 ∧ p.2 ∈ Ioo (-1:ℝ) 1 :=
    ((tendsto_comap.eventually (eventually_ge_atTop 1)).filter_mono inf_le_left).and
      (mem_inf_of_right (mem_principal_self _))
  filter_upwards [h1] with p ⟨hμ, hx⟩
  obtain ⟨μ, x⟩ := p
  simp only at hμ hx ⊢
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hx2 : 0 < 1 + x := by linarith [hx.1]
  set z : ℂ := (1 - (x:ℂ)) / 2 with hzdef
  have hzr : z = (((1 - x) / 2 : ℝ) : ℂ) := by rw [hzdef]; push_cast; ring
  have hz1 : ‖z‖ ≤ 1 := by
    rw [hzr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith [hx.1]
  have hz : ‖z‖ < 1 := by
    rw [hzr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith [hx.1]
  have hpre : ((1 + (x:ℂ)) / (1 - x)) ^ ((μ:ℂ) / 2) * ferrersP ν (-μ) x =
      regularizedGaussHGFun (ν + 1) (-ν) (1 - -(μ:ℂ)) z := by
    have hw : (1 + (x:ℂ)) / (1 - x) = (((1 + x) / (1 - x) : ℝ) : ℂ) := by push_cast; ring
    have hw0 : ((((1 + x) / (1 - x) : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    rw [ferrersP, ← regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hz,
        hw, ← mul_assoc,
      ← cpow_add _ _ hw0, show (μ:ℂ) / 2 + -(μ:ℂ) / 2 = 0 by ring, cpow_zero, one_mul]
  set s : ℕ → ℂ := fun n => pochhammer (ν + 1) n * pochhammer (-ν) n /
      (n ! * Gamma (1 - -(μ:ℂ) + n)) *
    z ^ n with hs
  have hS : HasSum s _ :=
      hasSum_regularizedGaussHypergeometricFun_coeff (ν + 1) (-ν) (1 - -(μ:ℂ)) hz
  have htail := (hasSum_nat_add_iff' J).mpr hS
  have hfin : ∑ j ∈ Finset.range J, pochhammer (ν+1) j * pochhammer (-ν) j / ((j.factorial:ℂ) *
      Gamma (j + 1 + μ)) * ((1 - x) / 2 : ℂ) ^ j = ∑ j ∈ Finset.range J, s j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hs, hzdef]
    rw [show (j:ℂ) + 1 + μ = 1 - -(μ:ℂ) + j by ring]
  rw [hpre, hfin]
  have hΓ : ∀ m : ℕ, Gamma (1 - -(μ:ℂ) + m) = ((Real.Gamma (m + 1 + μ) : ℝ) : ℂ) := fun m => by
    rw [show 1 - -(μ:ℂ) + m = ((m + 1 + μ : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
  have hΓJ : Gamma ((J:ℂ) + 1 + μ) = ((Real.Gamma (J + 1 + μ) : ℝ) : ℂ) := by
    rw [show (J:ℂ) + 1 + μ = ((J + 1 + μ : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
  have hGJ : 0 < Real.Gamma (J + 1 + μ) := Real.Gamma_pos_of_pos (by positivity)
  set g : ℕ → ℝ := fun n => ((J + 1).factorial : ℝ) * ‖gc (n + J)‖ / Real.Gamma (J + 1 + μ)
  have hg : HasSum g (((J + 1).factorial : ℝ) * (∑' n, ‖gc (n + J)‖) / Real.Gamma (J + 1 + μ)) :=
    (((summable_nat_add_iff J).mpr hsum).hasSum.mul_left _).div_const _
  have hbound : ∀ n, ‖s (n + J)‖ ≤ g n := by
    intro n
    have hGm : 0 < Real.Gamma ((n + J : ℕ) + 1 + μ) := Real.Gamma_pos_of_pos (by positivity)
    have key := LargeOrder.Gamma_mul_factorial_le J hμ n
    rw [show (J:ℝ) + n + 1 + μ = ((n + J : ℕ) : ℝ) + 1 + μ by push_cast; ring,
      show J + n + 1 = (n + J) + 1 by omega] at key
    simp only [hs, g, hgc, gaussHypergeometricCoeff, LargeOrder.pochhammer_two]
    rw [hΓ]
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hGm, Complex.norm_natCast]
    set A := ‖pochhammer (ν + 1) (n + J)‖ * ‖pochhammer (-ν) (n + J)‖
    have hA : 0 ≤ A := by positivity
    have hm1 : (0:ℝ) < ((n + J) ! : ℝ) := by positivity
    have hm2 : (0:ℝ) < ((n + J + 1).factorial : ℝ) := by positivity
    have hinv : 1 / ((n + J) ! * Real.Gamma ((n + J : ℕ) + 1 + μ)) ≤
        ((J + 1).factorial : ℝ) / (((n + J + 1).factorial : ℝ) * (n + J) !) /
          Real.Gamma (J + 1 + μ) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc A / ((n + J) ! * Real.Gamma ((n + J : ℕ) + 1 + μ)) * ‖z‖ ^ (n + J)
        ≤ A / ((n + J) ! * Real.Gamma ((n + J : ℕ) + 1 + μ)) * 1 := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) hz1
      _ = A * (1 / ((n + J) ! * Real.Gamma ((n + J : ℕ) + 1 + μ))) := by ring
      _ ≤ A * (((J + 1).factorial : ℝ) / (((n + J + 1).factorial : ℝ) * (n + J) !) /
          Real.Gamma (J + 1 + μ)) := mul_le_mul_of_nonneg_left hinv hA
      _ = _ := by ring
  have hle := htail.norm_le_of_bounded hg hbound
  have htl : ∑' n, ‖gc (n + J)‖ ≤ ∑' n, ‖gc n‖ := by
    rw [← hsum.sum_add_tsum_nat_add J]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  rw [one_div, norm_inv, hΓJ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGJ, hC]
  calc _ ≤ _ := hle
    _ ≤ ((J + 1).factorial : ℝ) * (∑' n, ‖gc n‖) / Real.Gamma (J + 1 + μ) := by gcongr

/-- DLMF 14.15.2: for fixed real `ν ≥ −1/2`, `P^{−μ}_ν(x) = (1/Γ(μ+1)) (2μu/π)^{1/2} K_{ν+1/2}(μu)
(1 + O(1/μ))` as `μ → ∞`, uniformly for `x > 1`, where `u = ½ ln((x+1)/(x−1))`. -/
@[dlmf 14.15.E2]
theorem associatedP_large_order_uniform {ν : ℝ} (hν : -1/2 ≤ ν) :
    (fun p : ℝ × ℝ => associatedP ν (-p.1)
        p.2/(1/Gamma (p.1+1)*(2*p.1*legendreUCoordinate p.2/π:ℂ)^(1/2:ℂ)*besselK (ν+1/2)
        (p.1*legendreUCoordinate p.2))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.2}]
        (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.3: for fixed real `ν ≥ −1/2`, `𝑸^μ_ν(x) = μ^{−ν−1/2} (πu/2)^{1/2} I_{ν+1/2}(μu) (1 +
O(1/μ))` as `μ → ∞`, uniformly for `x > 1`, where `u = ½ ln((x+1)/(x−1))`. -/
@[dlmf 14.15.E3]
theorem olverQ_large_order_uniform {ν : ℝ} (hν : -1/2 ≤ ν) :
    (fun p : ℝ × ℝ => olverQ ν p.1
        p.2/((p.1:ℂ)^(-(ν:ℂ)-1/2)*(π*legendreUCoordinate p.2/2:ℂ)^(1/2:ℂ)*besselI (ν+1/2)
        (p.1*legendreUCoordinate p.2))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.2}]
        (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- The leading factor of DLMF 14.15.4: `(1/Γ(μ+1)) (1−α²)^{−μ/2} ((1−α)/(1+α))^{ν/2+1/4} (α²x² + 1
− α²)^{−1/4} e^{−μρ}`, with `α = (ν+1/2)/μ` (14.15.5) and `ρ` from 14.15.7. -/
def legendreOrderPrefactor (ν μ x : ℝ) : ℂ :=
  let α:=legendreOrderAlpha ν μ
  1/Gamma (μ+1)*(1-α^2:ℂ)^(-(μ:ℂ)/2)*((1-α)/(1+α):ℂ)^((ν:ℂ)/2+1/4)
    *(α^2*x^2+1-α^2:ℂ)^(-1/4:ℂ)*exp (-μ*legendreOrderRho α x)

/-- DLMF 14.15.4: for fixed `δ ∈ (0,1)`, `𝖯^{−μ}_ν(x) = legendreOrderPrefactor ν μ x · (1 + O(1/μ))`
as `μ → ∞`, uniformly for `-1 < x < 1` and `0 ≤ ν + 1/2 ≤ (1−δ)μ`. -/
@[dlmf 14.15.E4]
theorem ferrersP_two_large_parameters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => ferrersP p.2.1 (-p.1) p.2.2/legendreOrderPrefactor p.2.1 p.1 p.2.2-1)
        =O[legendreUniformFilter
        {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (-1:ℝ) 1 ∧ 0 ≤ p.2.1+1/2 ∧ p.2.1+1/2 ≤ (1-δ)*p.1}]
        (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.8: for fixed `δ ∈ (0,1)`, `P^{−μ}_ν(x) = (2μ/π)^{1/2}/Γ(μ+1) ·
((1−α)/(1+α))^{ν/2+1/4} (1−α²)^{−μ/2} ((α²+η²)/(α²(x²−1)+1))^{1/4} K_{ν+1/2}(μη) (1 + O(1/μ))`
as `μ → ∞`, uniformly for `x > 1` and `0 ≤ ν + 1/2 ≤ (1−δ)μ`, with `α = (ν+1/2)/μ` and `η` from
14.15.10. -/
@[dlmf 14.15.E8]
theorem associatedP_two_large_order_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ =>
      let μ:=p.1; let ν:=p.2.1; let x:=p.2.2; let α:=legendreOrderAlpha ν μ
      let η:=legendreOrderEta α x
      associatedP ν (-μ) x/((2*μ/π:ℂ)^(1/2:ℂ)/Gamma (μ+1)*((1-α)/(1+α):ℂ)^((ν:ℂ)/2+1/4)
        *(1-α^2:ℂ)^(-(μ:ℂ)/2)*((α^2+η^2)/(α^2*(x^2-1)+1):ℂ)^(1/4:ℂ)*besselK (ν+1/2) (μ*η))-1)
      =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1+1/2 ∧ p.2.1+1/2 ≤ (1-δ)*p.1}]
      (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.9: for fixed `δ ∈ (0,1)`, `𝑸^μ_ν(x) = (π/2)^{1/2} (e/μ)^{ν+1/2} ((1−α)/(1+α))^{μ/2}
(1−α²)^{−ν/2−1/4} ((α²+η²)/(α²(x²−1)+1))^{1/4} I_{ν+1/2}(μη) (1 + O(1/μ))` as `μ → ∞`, uniformly for
`x > 1` and `0 ≤ ν + 1/2 ≤ (1−δ)μ`, with `α = (ν+1/2)/μ` and `η` from 14.15.10. -/
@[dlmf 14.15.E9]
theorem olverQ_two_large_order_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ =>
      let μ:=p.1; let ν:=p.2.1; let x:=p.2.2; let α:=legendreOrderAlpha ν μ
      let η:=legendreOrderEta α x
      olverQ ν μ x/((π/2:ℂ)^(1/2:ℂ)*(Real.exp 1/μ:ℂ)^(ν+1/2:ℂ)*((1-α)/(1+α):ℂ)^((μ:ℂ)/2)
        *(1-α^2:ℂ)^(-(ν:ℂ)/2-1/4)*((α^2+η^2)/(α^2*(x^2-1)+1):ℂ)^(1/4:ℂ)
        *besselI (ν+1/2) (μ*η))-1)
      =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1+1/2 ∧ p.2.1+1/2 ≤ (1-δ)*p.1}]
      (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.11: for fixed `μ ≥ 0` and `δ ∈ (0, π)`, `𝖯^{−μ}_ν(cos θ) = ν^{−μ} (θ/sin θ)^{1/2}
(J_μ((ν+1/2)θ) + env J_μ((ν+1/2)θ) · O(1/ν))` as `ν → ∞`, uniformly for `0 < θ ≤ π − δ`. -/
@[dlmf 14.15.E11]
theorem ferrersP_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun p : ℝ × ℝ => ferrersP p.1 (-μ)
        (Real.cos p.2)/((p.1:ℂ)^(-(μ:ℂ))*(p.2/Real.sin p.2:ℂ)^(1/2:ℂ))-besselJ μ ((p.1+1/2)*p.2))
        =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ π-δ}]
        (fun p : ℝ × ℝ => legendreBesselEnvelope false μ ((p.1+1/2)*p.2)/p.1) := by
  sorry

/-- DLMF 14.15.12: for fixed `μ ≥ 0` and `δ ∈ (0, π)`, `𝖰^{−μ}_ν(cos θ) = −(π/2) ν^{−μ} (θ/sin
θ)^{1/2} (Y_μ((ν+1/2)θ) + env Y_μ((ν+1/2)θ) · O(1/ν))` as `ν → ∞`, uniformly for `0 < θ ≤ π − δ`. -/
@[dlmf 14.15.E12]
theorem ferrersQ_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun p : ℝ × ℝ => ferrersQ p.1 (-μ)
        (Real.cos p.2)/(-π/2*(p.1:ℂ)^(-(μ:ℂ))*(p.2/Real.sin p.2:ℂ)^(1/2:ℂ))-besselY μ
        ((p.1+1/2)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ π-δ}]
        (fun p : ℝ × ℝ => legendreBesselEnvelope true μ ((p.1+1/2)*p.2)/p.1) := by
  sorry

/-- DLMF 14.15.13: for fixed `μ ≥ 0`, `P^{−μ}_ν(cosh ξ) = ν^{−μ} (ξ/sinh ξ)^{1/2} I_μ((ν+1/2)ξ) (1 +
O(1/ν))` as `ν → ∞`, uniformly for `ξ > 0`. -/
@[dlmf 14.15.E13]
theorem associatedP_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) :
    (fun p : ℝ × ℝ => let ν:=p.1; let ξ:=p.2;
        associatedP ν (-μ) (Real.cosh ξ)/((ν:ℂ)^(-(μ:ℂ))*(ξ/Real.sinh ξ:ℂ)^(1/2:ℂ)*besselI μ
        ((ν+1/2)*ξ))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2}]
        (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.14: for fixed `μ ≥ 0`, `𝑸^μ_ν(cosh ξ) = ν^μ/Γ(ν+μ+1) · (ξ/sinh ξ)^{1/2} K_μ((ν+1/2)ξ)
(1 + O(1/ν))` as `ν → ∞`, uniformly for `ξ > 0`. -/
@[dlmf 14.15.E14]
theorem olverQ_large_degree_uniform {μ : ℝ} (hμ : 0 ≤ μ) :
    (fun p : ℝ × ℝ => let ν:=p.1; let ξ:=p.2;
        olverQ ν μ (Real.cosh ξ)/((ν:ℂ)^(μ:ℂ)/Gamma (ν+μ+1)*(ξ/Real.sinh ξ:ℂ)^(1/2:ℂ)*besselK μ
        ((ν+1/2)*ξ))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2}]
        (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.15: for fixed `δ ∈ (0,1)`, `𝖯^{−μ}_ν(x) = β ((y−α²)/(1−α²−x²))^{1/4} (J_μ((ν+1/2)
y^{1/2}) + env J_μ((ν+1/2) y^{1/2}) · O(1/ν))` as `ν → ∞`, uniformly for `0 ≤ x < 1` and `0 ≤ μ ≤
(1−δ)(ν+1/2)`, with `α`, `β`, `y` from 14.15.19–14.15.21. -/
@[dlmf 14.15.E15]
theorem ferrersP_two_large_degree_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ;
        ferrersP ν (-μ) x/(legendreDegreeBeta ν μ*legendreDegreeAmplitude α x)-besselJ μ
        ((ν+1/2)*Real.sqrt (legendreDegreeY α x)))
        =O[legendreUniformFilter
        {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}]
        (fun p : ℝ × ℝ × ℝ =>
        legendreBesselEnvelope false p.2.1
        ((p.1+1/2)*Real.sqrt (legendreDegreeY (legendreDegreeAlpha p.1 p.2.1) p.2.2))/p.1) := by
  sorry

/-- DLMF 14.15.16: for fixed `δ ∈ (0,1)`, `𝖰^{−μ}_ν(x) = −(π/2) β ((y−α²)/(1−α²−x²))^{1/4}
(Y_μ((ν+1/2) y^{1/2}) + env Y_μ((ν+1/2) y^{1/2}) · O(1/ν))` as `ν → ∞`, uniformly for `0 ≤ x < 1`
and `0 ≤ μ ≤ (1−δ)(ν+1/2)`, with `α`, `β`, `y` from 14.15.19–14.15.21. -/
@[dlmf 14.15.E16]
theorem ferrersQ_two_large_degree_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ;
        ferrersQ ν (-μ) x/(-π/2*legendreDegreeBeta ν μ*legendreDegreeAmplitude α x)-besselY μ
        ((ν+1/2)*Real.sqrt (legendreDegreeY α x)))
        =O[legendreUniformFilter
        {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}]
        (fun p : ℝ × ℝ × ℝ =>
        legendreBesselEnvelope true p.2.1
        ((p.1+1/2)*Real.sqrt (legendreDegreeY (legendreDegreeAlpha p.1 p.2.1) p.2.2))/p.1) := by
  sorry

/-- DLMF 14.15.17: for fixed `δ ∈ (0,1)`, `P^{−μ}_ν(x) = β ((α²−y)/(x²−1+α²))^{1/4}
I_μ((ν+1/2)|y|^{1/2}) (1 + O(1/ν))` as `ν → ∞`, uniformly for `x > 1` and `0 ≤ μ ≤ (1−δ)(ν+1/2)`,
with `α`, `β`, `y` from 14.15.19, 14.15.20, 14.15.22. -/
@[dlmf 14.15.E17]
theorem associatedP_two_large_degree_modified {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ;
        let y:=legendreDegreeY α x;
        associatedP ν (-μ) x/(legendreDegreeBeta ν μ*((α^2-y)/(x^2-1+α^2):ℂ)^(1/4:ℂ)*besselI μ
        ((ν+1/2)*Real.sqrt |y|))-1)
        =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}]
        (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.18: for fixed `δ ∈ (0,1)`, `𝑸^μ_ν(x) = 1/(β Γ(ν+μ+1)) · ((α²−y)/(x²−1+α²))^{1/4}
K_μ((ν+1/2)|y|^{1/2}) (1 + O(1/ν))` as `ν → ∞`, uniformly for `x > 1` and `0 ≤ μ ≤ (1−δ)(ν+1/2)`,
with `α`, `β`, `y` from 14.15.19, 14.15.20, 14.15.22. -/
@[dlmf 14.15.E18]
theorem olverQ_two_large_degree_modified {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=legendreDegreeAlpha ν μ;
        let y:=legendreDegreeY α x;
        olverQ ν μ x/(1/(legendreDegreeBeta ν μ*Gamma
        (ν+μ+1))*((α^2-y)/(x^2-1+α^2):ℂ)^(1/4:ℂ)*besselK μ ((ν+1/2)*Real.sqrt |y|))-1)
        =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | 1 < p.2.2 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ (1-δ)*(p.1+1/2)}]
        (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- DLMF 14.15.24: for fixed `δ ∈ (0,1)`, `𝖯^{−μ}_ν(x) = A(x) U(μ−ν−1/2, (2ν+1)^{1/2}
ζ)/((ν+1/2)^{1/4} 2^{(ν+μ)/2} Γ((ν+μ)/2+3/4)) + O(ν^{−2/3}) · env U(μ−ν−1/2, (2ν+1)^{1/2} ζ)` as `ν
→ ∞`, uniformly for `0 ≤ x < 1` and `δ(ν+1/2) ≤ μ ≤ ν+1/2`, with `ζ` from 14.15.27–14.15.29 and
amplitude `A = ((ζ²−α²)/(x²−a²))^{1/4}` (`legendreCylinderAmplitude`); the error is stated for the
quotient by the prefactor. -/
@[dlmf 14.15.E24]
theorem ferrersP_cylinder_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2;
        ferrersP ν (-μ) x/(1/((ν+1/2:ℂ)^(1/4:ℂ)*2^((ν+μ:ℂ)/2)*Gamma
        ((ν+μ:ℂ)/2+3/4))*legendreCylinderAmplitude ν μ x)-parabolicCylinderU (μ-ν-1/2)
        (Real.sqrt (2*ν+1)*legendreCylinderZeta ν μ x))
        =O[legendreUniformFilter
        {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ δ*(p.1+1/2) ≤ p.2.1 ∧ p.2.1 ≤ p.1+1/2}]
        (fun p : ℝ × ℝ × ℝ =>
        p.1^(-2/3:ℝ)*legendreCylinderEnvelope false (p.1+1/2-p.2.1)
        (Real.sqrt (2*p.1+1)*legendreCylinderZeta p.1 p.2.1 p.2.2)) := by
  sorry

/-- DLMF 14.15.25: for fixed `δ ∈ (0,1)`, `𝖰^{−μ}_ν(x) = (π/2) A(x) Ū(μ−ν−1/2, (2ν+1)^{1/2}
ζ)/((ν+1/2)^{1/4} 2^{(ν+μ)/2} Γ((ν+μ)/2+3/4)) + O(ν^{−2/3}) · env Ū(μ−ν−1/2, (2ν+1)^{1/2} ζ)` as `ν
→ ∞`, uniformly for `0 ≤ x < 1` and `δ(ν+1/2) ≤ μ ≤ ν+1/2`, with `ζ` and the amplitude `A` as in
14.15.24; the error is stated for the quotient by the prefactor. -/
@[dlmf 14.15.E25]
theorem ferrersQ_cylinder_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2;
        ferrersQ ν (-μ) x/(π/2*1/((ν+1/2:ℂ)^(1/4:ℂ)*2^((ν+μ:ℂ)/2)*Gamma
        ((ν+μ:ℂ)/2+3/4))*legendreCylinderAmplitude ν μ x)-parabolicCylinderUBar (μ-ν-1/2)
        (Real.sqrt (2*ν+1)*legendreCylinderZeta ν μ x))
        =O[legendreUniformFilter
        {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico 0 1 ∧ δ*(p.1+1/2) ≤ p.2.1 ∧ p.2.1 ≤ p.1+1/2}]
        (fun p : ℝ × ℝ × ℝ =>
        p.1^(-2/3:ℝ)*legendreCylinderEnvelope true (p.1+1/2-p.2.1)
        (Real.sqrt (2*p.1+1)*legendreCylinderZeta p.1 p.2.1 p.2.2)) := by
  sorry

/-- DLMF 14.15.30: for fixed `δ ∈ (0,1)`, `𝖯^{−μ}_ν(x) = A(x) U(μ−ν−1/2, (2ν+1)^{1/2}
ζ)/((ν+1/2)^{1/4} 2^{(ν+μ)/2} Γ((ν+μ)/2+3/4)) · (1 + O(ln ν/ν))` as `ν → ∞`, uniformly for `-1
< x < 1` and `ν+1/2 ≤ μ ≤ (ν+1/2)/δ`, with `ζ` from 14.15.31 and amplitude `A =
((ζ²+α²)/(x²+a²))^{1/4}`. -/
@[dlmf 14.15.E30]
theorem ferrersP_cylinder_exponential_uniform {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (fun p : ℝ × ℝ × ℝ => let ν:=p.1; let μ:=p.2.1; let x:=p.2.2;
        ferrersP ν (-μ) x/(1/((ν+1/2:ℂ)^(1/4:ℂ)*2^((ν+μ:ℂ)/2)*Gamma
        ((ν+μ:ℂ)/2+3/4))*legendreCylinderAmplitude ν μ x*parabolicCylinderU (μ-ν-1/2)
        (Real.sqrt (2*ν+1)*legendreCylinderZeta ν μ x))-1)
        =O[legendreUniformFilter
        {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (-1:ℝ) 1 ∧ p.1+1/2 ≤ p.2.1 ∧ p.2.1 ≤ (p.1+1/2)/δ}]
        (fun p : ℝ × ℝ × ℝ => Real.log p.1/p.1) := by
  sorry

end DLMF.Legendre
