/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.BoundaryAsymptotics
public import DLMF.Legendre.Singularities
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import DLMF.Legendre.IntegerTheory
public import DLMF.Legendre.IntegralTools

/-!
# Green identities and Ferrers product integrals

This file proves the Barnes-type integral DLMF 14.17.5 and the orthogonality relations
DLMF 14.17.6–14.17.9 of Ferrers functions of integer degree and order, and prepares the
off-diagonal integrals of products of order-zero Ferrers functions over `(-1, 1)`. The latter
use Green's identity together with the logarithmic expansions of `𝖯_α` and `𝖰_α` at `±1`
(DLMF 14.8.3) and the domination of Ferrers functions by `(1-x²)^{-1/4}`. Helper names live in the
namespace `FerrersGreen`.

## Main definitions

* `FerrersGreen.weight`: the weight `(1-x²)^{-1/4}` that dominates Ferrers functions on `(-1, 1)`.
* `FerrersGreen.logCoeff`, `FerrersGreen.constTerm`: the logarithmic coefficient and the constant
  term of `𝖯_α` at `-1`.
* `FerrersGreen.constPos`, `FerrersGreen.constNeg`: the constant terms of `𝖰_α` at `+1` and `-1`.
* `FerrersGreen.boundaryRemainder`, `FerrersGreen.boundaryRemainderPos`: the polynomial remainders
  of the Green boundary form at `-1` and `+1`.

## Main results

* `ferrers_barnes_integral`: DLMF 14.17.5.
* `ferrers_orthogonality_6`, `ferrers_orthogonality_7`: DLMF 14.17.6, 14.17.7.
* `ferrers_orthogonality_8`, `ferrers_orthogonality_9`: DLMF 14.17.8, 14.17.9.
* `FerrersGreen.ferrersP_neg_one_isBigO`, `FerrersGreen.ferrersQ_pos_isBigO`,
  `FerrersGreen.ferrersQ_neg_isBigO`: logarithmic expansions of `𝖯_α` and `𝖰_α` at the endpoints.
* `FerrersGreen.ferrersQ_neg`: DLMF 14.9.10 solved for `𝖰_ν(-x)`, for every regular `ν`.
* `FerrersGreen.boundary_neg`, `FerrersGreen.boundary_pos`, `FerrersGreen.integral_green`: Green's
  identity on `[-1, 1]` with the limits of the boundary form at `±1`.
* `FerrersGreen.integral_PP`, `FerrersGreen.integral_QQ`, `FerrersGreen.integral_PQ`: the Green
  integrals of `𝖯_ν 𝖯_λ`, `𝖰_ν 𝖰_λ` and `𝖯_ν 𝖰_λ`.
* `FerrersGreen.boundary_const`: closed form of the boundary constant `K_ν C_λ - K_λ C_ν`.

## Implementation notes

DLMF 14.17.6 assumes `m ≤ l` as well as `m ≤ n`; `ferrers_orthogonality_6` needs only `m ≤ n`.
In `ferrers_orthogonality_8` and `ferrers_orthogonality_9` (DLMF 14.17.8, 14.17.9, with weight
`1/(1-x²)`) one of the orders is assumed positive, since the integral diverges when both orders
vanish.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Legendre

/-- DLMF 14.17.5: for `Re σ > -1` and `Re μ > -1`, `∫₀¹ x^σ (1-x²)^{μ/2} 𝖯^{-μ}_ν(x) dx = Γ((σ+1)/2)
Γ(σ/2+1)/(2^{μ+1} Γ((σ-ν+μ)/2+1) Γ((σ+ν+μ+3)/2))`. -/
@[dlmf 14.17.E5]
theorem ferrers_barnes_integral {σ μ : ℂ} (hσ : -1 < σ.re) (hμ : -1 < μ.re) (ν : ℂ) :
    (∫ x : ℝ in 0..1, (x:ℂ)^σ*(1-x^2:ℂ)^(μ/2)*ferrersP ν (-μ) x)=Gamma ((σ+1)/2)*Gamma
        (σ/2+1)/(2^(μ+1)*Gamma ((σ-ν+μ)/2+1)*Gamma ((σ+ν+μ+3)/2)) := by
  sorry

/-- DLMF 14.17.6: for natural numbers `m ≤ n` (DLMF also assumes `m ≤ l`, which is not needed),
`∫_{-1}^{1} 𝖯^m_l(x) 𝖯^m_n(x) dx = (n+m)!/((n-m)! (n+1/2)) δ_{l,n}`. -/
@[dlmf 14.17.E6]
theorem ferrers_orthogonality_6 (l m n : ℕ) (hn : m ≤ n) :
    ∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (m) x=if l=n then
        ((n+m).factorial:ℂ)/((n-m).factorial*(n+1/2:ℂ)) else 0 := by
  have hI : (∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (m) x) =
      OrthogonalityIntegrals.weightedMoment m l n := by
    refine intervalIntegral.integral_congr_ae ?_
    have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le (by norm_num)] at htm
    rw [one_mul, OrthogonalityIntegrals.ferrersP_mul l n m ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩]
  rw [hI, OrthogonalityIntegrals.weightedMoment_eq]
  split_ifs with h
  · have hp := OrthogonalityIntegrals.prod_factorial hn
    have hf : ((n-m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (2*(n:ℂ)+1) ≠ 0 := by
      have : (0:ℝ) < 2*n+1 := by positivity
      exact_mod_cast this.ne'
    rw [← hp]
    field_simp
  · simp

/-- For natural numbers `m ≤ n` (no condition on `l`),
`∫_{-1}^{1} 𝖯^m_l(x) 𝖯^{-m}_n(x) dx = (-1)^m/(l+1/2) δ_{l,n}`. -/
@[dlmf 14.17.E7]
theorem ferrers_orthogonality_7 (l m n : ℕ) (hn : m ≤ n) :
    ∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (-m) x=if l=n then (-1)^m/(l+1/2:ℂ) else 0 := by
  have hk : ((n:ℂ)-m+1) = ((n-m:ℕ):ℂ)+1 := by rw [Nat.cast_sub hn]
  have hreg : ∀ k : ℕ, (n:ℂ)-m+1 ≠ -k := fun k h => by
    rw [hk] at h; have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hI : (∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (-m) x) =
      (-1)^m*Gamma ((n:ℂ)-m+1)/Gamma ((n:ℂ)+m+1) *
        ∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n m x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le (by norm_num)] at htm
    rw [ferrersP_negative_integer_order (n:ℂ) m hreg ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩]
    ring
  rw [hI, ferrers_orthogonality_6 l m n hn, hk, show (n:ℂ)+m+1 = ((n+m:ℕ):ℂ)+1 by push_cast; ring,
    Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
  split_ifs with h
  · subst h
    have hf : ((l-m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf' : ((l+m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : ((l:ℂ)+1/2) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [(l.cast_nonneg : (0:ℝ) ≤ l)]
    field_simp
  · simp

/-- Nonzero polynomial degrees and integrability are explicit; singular-weight integrals retain
their integrability conditions. -/
@[dlmf 14.17.E8]
theorem ferrers_orthogonality_8 (l m n : ℕ) (hl : l ≤ n) (hm : m ≤ n) (hp : 0 < m) :
    ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n (l) x*ferrersP n (m) x=if l=m then
        ((n+m).factorial:ℂ)/((n-m).factorial*m) else 0 := by
  split_ifs with h
  · subst h
    obtain ⟨k, rfl⟩ : ∃ k, l = k+1 := ⟨l-1, by omega⟩
    have hJ := OrthogonalityIntegrals.squareMoment_eq hm
    have hd := OrthogonalityIntegrals.ferrers_diag n k
    push_cast at hd ⊢
    rw [hd]
    have hf : ((n-(k+1)).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk : ((k:ℂ)+1) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    rw [← hJ]; field_simp
  · exact OrthogonalityIntegrals.ferrers_offDiag n l m h (by omega)

/-- Nonzero polynomial degrees and integrability are explicit; singular-weight integrals retain
their integrability conditions. -/
@[dlmf 14.17.E9]
theorem ferrers_orthogonality_9 (l m n : ℕ) (hl : l ≤ n) (hm : m ≤ n) (hp : 0 < l) :
    ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n (l) x*ferrersP n (-m) x=if l=m then
        (-1)^l/(l:ℂ) else 0 := by
  have hk : ((n:ℂ)-m+1) = ((n-m:ℕ):ℂ)+1 := by rw [Nat.cast_sub hm]
  have hreg : ∀ k : ℕ, (n:ℂ)-m+1 ≠ -k := fun k h => by
    rw [hk] at h; have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hI : (∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n (l) x*ferrersP n (-m) x) =
      (-1)^m*Gamma ((n:ℂ)-m+1)/Gamma ((n:ℂ)+m+1) *
        ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n l x*ferrersP n m x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le (by norm_num)] at htm
    rw [ferrersP_negative_integer_order (n:ℂ) m hreg ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩]
    ring
  rw [hI]
  split_ifs with h
  · subst h
    rw [ferrers_orthogonality_8 l l n hl hm hp]
    simp only [↓reduceIte]
    rw [hk, show (n:ℂ)+l+1 = ((n+l:ℕ):ℂ)+1 by push_cast; ring,
      Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
    have hf : ((n-l).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf' : ((n+l).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hl0 : (l:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  · rw [OrthogonalityIntegrals.ferrers_offDiag n l m h (by omega), mul_zero]

/-! ### Green's identity for order-zero Ferrers functions of general degree

The products `𝖯_ν 𝖯_λ` are integrated through Green's identity
`((1-x²)(f g' - g f'))' = (ν(ν+1) - λ(λ+1)) f g`, with the boundary form rewritten by the
recurrence 14.10.4 and evaluated at `-1` from the logarithmic behaviour of `𝖯_α` there
(DLMF 15.8.10 at `m = 0`, `BoundaryAsymptotics.zeroBalanced_isBigO`). Helper names live in the
namespace `FerrersGreen`. -/
/-- `𝖯_α(x) = 𝐅(α+1,-α;1;(1-x)/2)`. -/
theorem FerrersGreen.ferrersP_zero_eq_regularizedGaussHypergeometric (α : ℂ) (x : ℝ) :
    ferrersP α 0 x = regularizedGaussHypergeometric (α+1) (-α) 1 ((1-(x:ℂ))/2) := by
  simp [ferrersP]

/-- `𝖯_α` is continuous on `(-1,∞)`. -/
theorem FerrersGreen.continuousAt_ferrersP (α : ℂ) {x : ℝ} (hx : -1 < x) :
    ContinuousAt (ferrersP α 0) x := by
  have hw := OrthogonalityIntegrals.half_mem_cutPlane hx
  have : ferrersP α 0 = fun y : ℝ => regularizedGaussHypergeometric (α+1) (-α) 1 ((1-(y:ℂ))/2) :=
    funext (FerrersGreen.ferrersP_zero_eq_regularizedGaussHypergeometric α)
  rw [this]
  exact ContinuousAt.comp (g := regularizedGaussHypergeometric (α+1) (-α) 1)
    (differentiableAt_regularizedGaussHypergeometric _ _ _ hw).continuousAt (by fun_prop)

/-- The Ferrers function satisfies `ferrersP α 0 1 = 1` for every complex degree `α`. -/
theorem FerrersGreen.ferrersP_one (α : ℂ) : ferrersP α 0 1 = 1 := by
  rw [FerrersGreen.ferrersP_zero_eq_regularizedGaussHypergeometric]
  have h1 : ∀ k : ℕ, (1:ℂ) ≠ -(k:ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  simpa using regularizedGaussHypergeometric_zero_of_regular (a := α+1) (b := -α) h1

/-- `ferrersP α 0 x → 1` as `x → 1⁻`. -/
theorem FerrersGreen.tendsto_ferrersP_one (α : ℂ) :
    Tendsto (ferrersP α 0) (𝓝[<] (1:ℝ)) (𝓝 1) := by
  have := (FerrersGreen.continuousAt_ferrersP α (show (-1:ℝ) < 1 by norm_num)).tendsto
  rw [FerrersGreen.ferrersP_one] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The map `x ↦ (1+x)/2` sends `x → -1⁺` to `τ → 0⁺`. -/
theorem FerrersGreen.tendsto_half :
    Tendsto (fun x : ℝ => (1+x)/2) (𝓝[>] (-1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => (1+x)/2) (𝓝 (-1)) (𝓝 ((1+(-1))/2)) :=
      (tendsto_const_nhds.add tendsto_id).div_const 2
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi (-1)))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : -1 < x)
    simp only [mem_Ioi]; linarith

/-- Behaviour of `𝖯_α` at `-1`: `𝖯_α(x) = -K ln((1+x)/2) + C + O(t ln t)`, `t = (1+x)/2`,
with `K = 1/(Γ(α+1)Γ(-α))`, for every `α`. -/
theorem FerrersGreen.ferrersP_neg_one_isBigO (α : ℂ) :
    (fun x : ℝ => ferrersP α 0 x + BoundaryAsymptotics.zeroBalancedConst (α+1) (-α) *
        Real.log ((1+x)/2) -
      (BoundaryAsymptotics.zeroBalancedConstDeriv (α+1) (-α) - 2 * Real.eulerMascheroniConstant *
          BoundaryAsymptotics.zeroBalancedConst (α+1) (-α))) =O[𝓝[>] (-1:ℝ)]
      (fun x : ℝ => (1+x)/2 * Real.log ((1+x)/2)) := by
  have h := (BoundaryAsymptotics.zeroBalanced_isBigO (α+1) (-α)).comp_tendsto
      FerrersGreen.tendsto_half
  refine h.congr_left fun x => ?_
  simp only [Function.comp_apply]
  rw [FerrersGreen.ferrersP_zero_eq_regularizedGaussHypergeometric, show α + 1 + -α = 1 by ring]
  congr 3
  push_cast; ring

/-- The weight `(1-x²)^{-1/4}` used to dominate Ferrers functions on `(-1,1)`. -/
def FerrersGreen.weight (x : ℝ) : ℝ := ((1-x^2)/4)^(-(1/4:ℝ))

/-- On `(-1,1)` the weight satisfies `1 ≤ FerrersGreen.weight x`. -/
theorem FerrersGreen.weight_one_le {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : 1 ≤ FerrersGreen.weight x :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by nlinarith [hx.1, hx.2]) (by nlinarith)
    (by norm_num)

/-- On `(-1,1)` the weight `FerrersGreen.weight x` is positive. -/
theorem FerrersGreen.weight_pos {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : 0 < FerrersGreen.weight x :=
  lt_of_lt_of_le one_pos (FerrersGreen.weight_one_le hx)

/-- On `(-1,1)`, `FerrersGreen.weight x = ((1+x)/2)^(-1/4) * ((1-x)/2)^(-1/4)`. -/
theorem FerrersGreen.weight_eq {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    FerrersGreen.weight x = ((1+x)/2)^(-(1/4:ℝ)) * ((1-x)/2)^(-(1/4:ℝ)) := by
  rw [FerrersGreen.weight, ← Real.mul_rpow (by linarith [hx.1]) (by linarith [hx.2])]
  congr 1; ring

/-- `|ln y| ≤ 4 y^{-1/4}` on `(0,1]`. -/
theorem FerrersGreen.abs_log_le {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    |Real.log y| ≤ 4 * y^(-(1/4:ℝ)) := by
  have h := Real.abs_log_mul_self_rpow_lt y (1/4) hy0 hy1 (by norm_num)
  have hp : 0 < y^(1/4:ℝ) := Real.rpow_pos_of_pos hy0 _
  rw [abs_mul, abs_of_pos hp, show (1:ℝ)/(1/4) = 4 by norm_num] at h
  rw [Real.rpow_neg hy0.le, ← div_eq_mul_inv, le_div_iff₀ hp]
  exact h.le

/-- For `0 < y ≤ 1`, `1 ≤ y^(-1/4)`. -/
theorem FerrersGreen.rpow_ge_one {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) : 1 ≤ y^(-(1/4:ℝ)) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 (by norm_num)

/-- `ln((1+x)/2) = O((1-x²)^{-1/4})` as `x → -1⁺`. -/
theorem FerrersGreen.log_isBigO_left :
    (fun x : ℝ => Real.log ((1+x)/2)) =O[𝓝[>] (-1:ℝ)] FerrersGreen.weight := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have ht0 : 0 < (1+x)/2 := by linarith [hx.1]
  have ht1 : (1+x)/2 ≤ 1 := by linarith [hx.2]
  have hs0 : 0 < (1-x)/2 := by linarith [hx.2]
  have hs1 : (1-x)/2 ≤ 1 := by linarith [hx.1]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (FerrersGreen.weight_pos hx),
      FerrersGreen.weight_eq hx]
  calc |Real.log ((1+x)/2)| ≤ 4 * ((1+x)/2)^(-(1/4:ℝ)) := FerrersGreen.abs_log_le ht0 ht1
    _ ≤ 4 * (((1+x)/2)^(-(1/4:ℝ)) * ((1-x)/2)^(-(1/4:ℝ))) := by
      gcongr
      exact le_mul_of_one_le_right (Real.rpow_nonneg ht0.le _) (FerrersGreen.rpow_ge_one hs0 hs1)

/-- `ln((1-x)/2) = O((1-x²)^{-1/4})` as `x → 1⁻`. -/
theorem FerrersGreen.log_isBigO_right :
    (fun x : ℝ => Real.log ((1-x)/2)) =O[𝓝[<] (1:ℝ)] FerrersGreen.weight := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have ht0 : 0 < (1+x)/2 := by linarith [hx.1]
  have ht1 : (1+x)/2 ≤ 1 := by linarith [hx.2]
  have hs0 : 0 < (1-x)/2 := by linarith [hx.2]
  have hs1 : (1-x)/2 ≤ 1 := by linarith [hx.1]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (FerrersGreen.weight_pos hx),
      FerrersGreen.weight_eq hx]
  calc |Real.log ((1-x)/2)| ≤ 4 * ((1-x)/2)^(-(1/4:ℝ)) := FerrersGreen.abs_log_le hs0 hs1
    _ ≤ 4 * (((1+x)/2)^(-(1/4:ℝ)) * ((1-x)/2)^(-(1/4:ℝ))) := by
      gcongr
      exact le_mul_of_one_le_left (Real.rpow_nonneg hs0.le _) (FerrersGreen.rpow_ge_one ht0 ht1)

/-- The constant `1` is `O(FerrersGreen.weight)` as `x → -1⁺`. -/
theorem FerrersGreen.one_isBigO_left : (fun _ : ℝ => (1:ℝ)) =O[𝓝[>] (-1:ℝ)]
    FerrersGreen.weight := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (FerrersGreen.weight_pos hx), abs_one, one_mul]
  exact FerrersGreen.weight_one_le hx

/-- The constant `1` is `O(FerrersGreen.weight)` as `x → 1⁻`. -/
theorem FerrersGreen.one_isBigO_right : (fun _ : ℝ => (1:ℝ)) =O[𝓝[<] (1:ℝ)]
    FerrersGreen.weight := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (FerrersGreen.weight_pos hx), abs_one, one_mul]
  exact FerrersGreen.weight_one_le hx

/-- A function continuous on `(-1,1)` and `O((1-x²)^{-1/4})` at both ends is globally bounded by a
multiple of `(1-x²)^{-1/4}`. -/
theorem FerrersGreen.bound {f : ℝ → ℂ} (hc : ContinuousOn f (Ioo (-1) 1))
    (h1 : f =O[𝓝[>] (-1:ℝ)] FerrersGreen.weight) (h2 : f =O[𝓝[<] (1:ℝ)] FerrersGreen.weight) :
    ∃ M, ∀ x ∈ Ioo (-1:ℝ) 1, ‖f x‖ ≤ M * FerrersGreen.weight x := by
  obtain ⟨c1, -, hc1⟩ := h1.exists_pos
  obtain ⟨c2, -, hc2⟩ := h2.exists_pos
  obtain ⟨u, hu, hU⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hc1.bound
  obtain ⟨v, hv, hV⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hc2.bound
  have hK : Icc (min u 0) (max v 0) ⊆ Ioo (-1:ℝ) 1 := by
    intro x hx
    simp only [mem_Ioi, mem_Iio] at hu hv
    constructor
    · exact lt_of_lt_of_le (lt_min hu (by norm_num)) hx.1
    · exact lt_of_le_of_lt hx.2 (max_lt hv (by norm_num))
  obtain ⟨B, hB⟩ := (isCompact_Icc).exists_bound_of_continuousOn (hc.mono hK)
  refine ⟨max (max c1 c2) (max B 0), fun x hx => ?_⟩
  have hw1 := FerrersGreen.weight_one_le hx
  have hw0 := FerrersGreen.weight_pos hx
  by_cases hxu : x < u
  · have := hU ⟨hx.1, hxu⟩
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos hw0] at this
    calc ‖f x‖ ≤ c1 * FerrersGreen.weight x := this
      _ ≤ _ := by gcongr; exact le_trans (le_max_left _ _) (le_max_left _ _)
  by_cases hxv : v < x
  · have := hV ⟨hxv, hx.2⟩
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos hw0] at this
    calc ‖f x‖ ≤ c2 * FerrersGreen.weight x := this
      _ ≤ _ := by gcongr; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hxK : x ∈ Icc (min u 0) (max v 0) :=
    ⟨le_trans (min_le_left _ _) (not_lt.mp hxu), le_trans (not_lt.mp hxv) (le_max_left _ _)⟩
  calc ‖f x‖ ≤ B := hB x hxK
    _ ≤ max B 0 := le_max_left _ _
    _ ≤ max B 0 * FerrersGreen.weight x := le_mul_of_one_le_right (le_max_right _ _) hw1
    _ ≤ max (max c1 c2) (max B 0) * FerrersGreen.weight x :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hw0.le

/-- The product of two functions dominated by `(1-x²)^{-1/4}` is integrable on `[-1,1]`. -/
theorem FerrersGreen.intervalIntegrable_mul {f g : ℝ → ℂ} (hf : ContinuousOn f (Ioo (-1) 1))
    (hg : ContinuousOn g (Ioo (-1) 1)) {M N : ℝ}
        (hfM : ∀ x ∈ Ioo (-1:ℝ) 1, ‖f x‖ ≤ M * FerrersGreen.weight x)
    (hgN : ∀ x ∈ Ioo (-1:ℝ) 1, ‖g x‖ ≤ N * FerrersGreen.weight x) :
    IntervalIntegrable (fun x => f x * g x) volume (-1) 1 := by
  have hI := (OrthogonalityIntegrals.intervalIntegrable_rpow (r := -1/2) (Or.inl rfl)).const_mul
      (M*N/4^(-1/2:ℝ))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at hI ⊢
  refine hI.mono' ((hf.mul hg).aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [norm_mul]
  have h0 : 0 ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hw : FerrersGreen.weight x * FerrersGreen.weight x = (1-x^2)^(-1/2:ℝ) / 4^(-1/2:ℝ) := by
    rw [FerrersGreen.weight, ← Real.rpow_add' (by positivity) (by norm_num),
        Real.div_rpow h0 (by norm_num)]
    norm_num
  calc ‖f x‖ * ‖g x‖ ≤ (M * FerrersGreen.weight x) * (N * FerrersGreen.weight x) :=
        mul_le_mul (hfM x hx) (hgN x hx) (norm_nonneg _)
          (le_trans (norm_nonneg _) (hfM x hx))
    _ = M*N/4^(-1/2:ℝ)*(1-x^2)^(-1/2:ℝ) := by rw [mul_mul_mul_comm, hw]; ring

/-- `t ln t → 0`, so `t ln t = O(1)`, as `x → -1⁺`, `t = (1+x)/2`. -/
theorem FerrersGreen.mul_log_isBigO_left :
    (fun x : ℝ => (1+x)/2 * Real.log ((1+x)/2)) =O[𝓝[>] (-1:ℝ)] FerrersGreen.weight := by
  have h : Tendsto (fun x : ℝ => (1+x)/2 * Real.log ((1+x)/2)) (𝓝[>] (-1:ℝ)) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).comp
      (FerrersGreen.tendsto_half.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def] using this
  exact (h.isBigO_one ℝ).trans FerrersGreen.one_isBigO_left

/-- `𝖯_α = O((1-x²)^{-1/4})` at `-1`. -/
theorem FerrersGreen.ferrersP_isBigO_left (α : ℂ) : ferrersP α 0 =O[𝓝[>] (-1:ℝ)]
    FerrersGreen.weight := by
  have h1 := (FerrersGreen.ferrersP_neg_one_isBigO α).trans FerrersGreen.mul_log_isBigO_left
  have h2 := (isBigO_ofReal_left.mpr FerrersGreen.log_isBigO_left).const_mul_left
      (BoundaryAsymptotics.zeroBalancedConst (α+1) (-α))
  have h3 := ((isBigO_const_one ℝ
      (BoundaryAsymptotics.zeroBalancedConstDeriv (α+1) (-α) - 2 * Real.eulerMascheroniConstant *
    BoundaryAsymptotics.zeroBalancedConst (α+1) (-α)) (𝓝[>] (-1:ℝ))).trans
        FerrersGreen.one_isBigO_left)
  exact ((h1.sub h2).add h3).congr_left fun _ => by ring

/-- `𝖯_α = O((1-x²)^{-1/4})` at `1`. -/
theorem FerrersGreen.ferrersP_isBigO_right (α : ℂ) : ferrersP α 0 =O[𝓝[<] (1:ℝ)]
    FerrersGreen.weight :=
  ((FerrersGreen.tendsto_ferrersP_one α).isBigO_one ℝ).trans FerrersGreen.one_isBigO_right

/-- `ferrersP α 0` is continuous on `(-1,1)`. -/
theorem FerrersGreen.continuousOn_ferrersP (α : ℂ) : ContinuousOn (ferrersP α 0) (Ioo (-1) 1) :=
  fun _ hx => (FerrersGreen.continuousAt_ferrersP α hx.1).continuousWithinAt

/-- `𝖯_ν 𝖯_λ` is integrable on `[-1,1]`. -/
theorem FerrersGreen.intervalIntegrable_PP (ν lam : ℂ) :
    IntervalIntegrable (fun x => ferrersP ν 0 x * ferrersP lam 0 x) volume (-1) 1 := by
  obtain ⟨M, hM⟩ := FerrersGreen.bound (FerrersGreen.continuousOn_ferrersP ν)
      (FerrersGreen.ferrersP_isBigO_left ν)
    (FerrersGreen.ferrersP_isBigO_right ν)
  obtain ⟨N, hN⟩ := FerrersGreen.bound (FerrersGreen.continuousOn_ferrersP lam)
      (FerrersGreen.ferrersP_isBigO_left lam)
    (FerrersGreen.ferrersP_isBigO_right lam)
  exact FerrersGreen.intervalIntegrable_mul (FerrersGreen.continuousOn_ferrersP ν)
    (FerrersGreen.continuousOn_ferrersP lam) hM hN

section Constants
open DLMF.Gamma

/-- Derivative of `Γ(s)⁻¹ = s Γ(s+1)⁻¹`: `(1/Γ)'(s) = 1/Γ(s+1) + s (1/Γ)'(s+1)`. -/
theorem FerrersGreen.recipGammaDeriv_recurrence (s : ℂ) :
    recipGammaDeriv 1 s = (Gamma (s+1))⁻¹ + s * recipGammaDeriv 1 (s+1) := by
  have hfun : (fun w : ℂ => (Gamma w)⁻¹) = fun w => w * (Gamma (w+1))⁻¹ :=
    funext Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
  have h1 := hasDerivAt_recip_Gamma' s
  rw [hfun] at h1
  have h2 : HasDerivAt (fun w : ℂ => w * (Gamma (w+1))⁻¹)
      (1 * (Gamma (s+1))⁻¹ + s * recipGammaDeriv 1 (s+1)) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_recip_Gamma' (s+1)).comp_add_const s 1)
  rw [h1.unique h2, one_mul]

/-- `K_{α+1} = -K_α` for the constant `K_α = 1/(Γ(α+1)Γ(-α))`. -/
theorem FerrersGreen.logCoeff_succ (α : ℂ) : BoundaryAsymptotics.zeroBalancedConst (α+1+1) (-(α+1))
    = -BoundaryAsymptotics.zeroBalancedConst (α+1) (-α) := by
  unfold BoundaryAsymptotics.zeroBalancedConst
  rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (α+1),
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (-(α+1)), show -(α+1)+1 = -α by ring]
  ring

/-- `(α+1)(K'_{α+1} + K'_α) = 2K_α`. -/
theorem FerrersGreen.logCoeffDeriv_succ (α : ℂ) :
    (α+1) * (BoundaryAsymptotics.zeroBalancedConstDeriv (α+1+1) (-(α+1)) +
        BoundaryAsymptotics.zeroBalancedConstDeriv (α+1) (-α)) = 2 *
        BoundaryAsymptotics.zeroBalancedConst (α+1) (-α) := by
  unfold BoundaryAsymptotics.zeroBalancedConstDeriv BoundaryAsymptotics.zeroBalancedConst
  have r1 := FerrersGreen.recipGammaDeriv_recurrence (-(α+1))
  have r2 := FerrersGreen.recipGammaDeriv_recurrence (α+1)
  have r3 := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (α+1)
  have r4 := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (-(α+1))
  rw [show -(α+1)+1 = -α by ring] at r1 r4
  linear_combination (α+1)*(Gamma (α+1+1))⁻¹ * r1 + (α+1)*recipGammaDeriv 1 (α+1+1) * r4 +
    ((α+1)*recipGammaDeriv 1 (-α) - 2*(Gamma (-α))⁻¹) * r3 + (α+1)*(Gamma (-α))⁻¹ * r2

/-- `π K_α = -sin(πα)`. -/
theorem FerrersGreen.logCoeff_eq (α : ℂ) : (π:ℂ) *
    BoundaryAsymptotics.zeroBalancedConst (α+1) (-α) = -sin (π*α) := by
  have := legendre_recip_Gamma_reflection (-α)
  rw [show (1:ℂ) - -α = α+1 by ring, mul_neg, sin_neg] at this
  unfold BoundaryAsymptotics.zeroBalancedConst; rw [← this]; ring

/-- `K'_α = cos(πα) - 2ψ(α+1)K_α` when `α+1` is not a pole. -/
theorem FerrersGreen.logCoeffDeriv_eq {α : ℂ} (hα : ∀ m : ℕ, α+1 ≠ -(m:ℂ)) :
    BoundaryAsymptotics.zeroBalancedConstDeriv (α+1) (-α) = cos (π*α) -
        2*digamma (α+1)*BoundaryAsymptotics.zeroBalancedConst (α+1) (-α) := by
  have hr := BoundaryAsymptotics.reflection_deriv (-α)
  rw [show (1:ℂ) - -α = α+1 by ring, mul_neg, cos_neg] at hr
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' := mul_left_cancel₀ hpi hr
  have hd := recipGammaDeriv_one_eq hα
  unfold BoundaryAsymptotics.zeroBalancedConstDeriv BoundaryAsymptotics.zeroBalancedConst
  rw [← hr', hd]
  ring

end Constants

/-- Green's identity for two order-zero Legendre solutions:
`((1-x²)(f g' - g f'))' = (ν(ν+1) - λ(λ+1)) f g`. -/
theorem FerrersGreen.green {ν lam : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν 0 f)
    (hg : IsFerrersSolution lam 0 g) {y : ℝ} (hy : y ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun y : ℝ => (1-(y:ℂ)^2)*(f y*deriv g y-g y*deriv f y))
      ((ν*(ν+1) - lam*(lam+1)) * (f y * g y)) y := by
  obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
  obtain ⟨hg1, g2, hg2, eg⟩ := hg y hy
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero] at ef eg
  have hsq : HasDerivAt (fun y : ℝ => 1-(y:ℂ)^2) (-(2*(y:ℂ))) y := by
    have := ((hasDerivAt_id y).ofReal_comp.pow 2).const_sub 1
    simpa using this
  refine (hsq.mul ((hf1.hasDerivAt.mul hg2).sub (hg1.hasDerivAt.mul hf2))).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply]
  linear_combination (f y)*eg-(g y)*ef

/-- The logarithmic coefficient `K_α = 1/(Γ(α+1)Γ(-α))` of `𝖯_α` at `-1`. -/
def FerrersGreen.logCoeff (α : ℂ) : ℂ := BoundaryAsymptotics.zeroBalancedConst (α+1) (-α)

/-- The constant term `C_α` of `𝖯_α` at `-1`. -/
def FerrersGreen.constTerm (α : ℂ) : ℂ :=
  BoundaryAsymptotics.zeroBalancedConstDeriv (α+1) (-α) - 2 * Real.eulerMascheroniConstant *
      BoundaryAsymptotics.zeroBalancedConst (α+1) (-α)

/-- The polynomial remainder in the boundary form at `-1`. -/
def FerrersGreen.boundaryRemainder (Kn Kl Cn Cl rn rl n l : ℂ) (v : Fin 11 → ℂ) : ℂ :=
  (2*Kl*Kn*l - 2*Kl*Kn*n)*v 2 +
    (-2*Kl*l + 2*Kl*n)*v 7*v 0 +
    (-2*Kn*l + 2*Kn*n)*v 8*v 0 +
    (-2*Cl*Kn*l + 2*Cl*Kn*n - 2*Cn*Kl*l + 2*Cn*Kl*n)*v 1 +
    (2*l - 2*n)*v 0*v 3*v 4 +
    (2*Cl*l - 2*Cl*n)*v 0*v 3 +
    (2*Cn*l - 2*Cn*n)*v 0*v 4 +
    (2*Cl*Cn*l - 2*Cl*Cn*n)*v 0 +
    (-Kl*n - Kl)*v 7 +
    (Kn*l + Kn)*v 8 +
    (Kn*l + Kn)*v 9 +
    (-Kl*n - Kl)*v 10 +
    (-l + n)*v 3*v 4 +
    (-l - 1)*v 3*v 5 +
    (Cl*n + Cl - l*rl - rl)*v 3 +
    (n + 1)*v 4*v 6 +
    (-Cn*l - Cn + n*rn + rn)*v 4 +
    (-Cn*l - Cn)*v 5 +
    (Cl*n + Cl)*v 6

/-- The boundary-form remainder `FerrersGreen.boundaryRemainder Kn Kl Cn Cl rn rl n l` is continuous
in `v`. -/
theorem FerrersGreen.continuous_boundaryRemainder (Kn Kl Cn Cl rn rl n l : ℂ) : Continuous
    (FerrersGreen.boundaryRemainder Kn Kl Cn Cl rn rl n l) := by
  unfold FerrersGreen.boundaryRemainder; fun_prop

/-- The polynomial remainder in the boundary form at `+1`. -/
def FerrersGreen.boundaryRemainderPos (kf kg cf cg rf rg n l : ℂ) (v : Fin 11 → ℂ) : ℂ :=
  (-2*kf*kg*l + 2*kf*kg*n)*v 2 +
    (2*kg*l - 2*kg*n)*v 7*v 0 +
    (2*kf*l - 2*kf*n)*v 8*v 0 +
    (2*cf*kg*l - 2*cf*kg*n + 2*cg*kf*l - 2*cg*kf*n)*v 1 +
    (-2*l + 2*n)*v 0*v 3*v 4 +
    (-2*cg*l + 2*cg*n)*v 0*v 3 +
    (-2*cf*l + 2*cf*n)*v 0*v 4 +
    (-2*cf*cg*l + 2*cf*cg*n)*v 0 +
    (kg*n + kg)*v 7 +
    (-kf*l - kf)*v 8 +
    (kf*l + kf)*v 9 +
    (-kg*n - kg)*v 10 +
    (l - n)*v 3*v 4 +
    (-l - 1)*v 3*v 5 +
    (-cg*n - cg - l*rg - rg)*v 3 +
    (n + 1)*v 4*v 6 +
    (cf*l + cf + n*rf + rf)*v 4 +
    (-cf*l - cf)*v 5 +
    (cg*n + cg)*v 6

/-- The boundary-form remainder `FerrersGreen.boundaryRemainderPos kf kg cf cg rf rg n l` is
continuous in `v`. -/
theorem FerrersGreen.continuous_boundaryRemainderPos (kf kg cf cg rf rg n l : ℂ) : Continuous
    (FerrersGreen.boundaryRemainderPos kf kg cf cg rf rg n l) := by
  unfold FerrersGreen.boundaryRemainderPos; fun_prop

/-- Basic limits at a boundary point where `τ → 0⁺`. -/
theorem FerrersGreen.basic_limits {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) :
    Tendsto (fun x => ((τ x : ℝ) : ℂ)) l (𝓝 0) ∧
    Tendsto (fun x => ((τ x : ℝ) : ℂ) * ((Real.log (τ x) : ℝ) : ℂ)) l (𝓝 0) ∧
    Tendsto (fun x => ((τ x : ℝ) : ℂ) * ((Real.log (τ x) : ℝ) : ℂ) * ((Real.log (τ x) : ℝ) : ℂ))
      l (𝓝 0) ∧
    Tendsto (fun x => τ x * Real.log (τ x)) l (𝓝 0) ∧
    Tendsto (fun x => Real.log (τ x) * (τ x * Real.log (τ x))) l (𝓝 0) := by
  have h1 : Tendsto (fun x => τ x * Real.log (τ x)) l (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).comp (hτ.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun x => Real.log (τ x) * (τ x * Real.log (τ x))) l (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1/2) (by norm_num)).pow 2
    rw [show (0:ℝ)^2 = 0 by norm_num] at h
    refine (h.comp hτ).congr' ?_
    filter_upwards [hτ self_mem_nhdsWithin] with x (hx : 0 < τ x)
    have h2 : ((τ x)^(1/2:ℝ))^2 = τ x := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le]
    simp only [Function.comp_apply]
    rw [mul_pow, h2]; ring
  refine ⟨?_, ?_, ?_, h1, h2⟩
  · have := (continuous_ofReal.tendsto 0).comp (hτ.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def] using this
  · have := (continuous_ofReal.tendsto 0).comp h1
    simpa [Function.comp_def] using this
  · have := (continuous_ofReal.tendsto 0).comp h2
    have h3 : Tendsto (fun x => ((Real.log (τ x) : ℝ) : ℂ) * (((τ x : ℝ) : ℂ) *
        ((Real.log (τ x) : ℝ) : ℂ))) l (𝓝 0) := by simpa [Function.comp_def] using this
    exact h3.congr fun x => by ring

/-- `E → 0` and `ln τ · E → 0` when `E = O(τ ln τ)`. -/
theorem FerrersGreen.error_limits {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) {E : ℝ → ℂ}
    (hE : E =O[l] (fun x => τ x * Real.log (τ x))) :
    Tendsto E l (𝓝 0) ∧ Tendsto (fun x => ((Real.log (τ x) : ℝ) : ℂ) * E x) l (𝓝 0) := by
  obtain ⟨-, -, -, h1, h2⟩ := FerrersGreen.basic_limits hτ
  refine ⟨hE.trans_tendsto h1, ?_⟩
  have hU : (fun x => ((Real.log (τ x) : ℝ) : ℂ)) =O[l] (fun x => Real.log (τ x)) :=
    isBigO_ofReal_left.mpr (isBigO_refl _ _)
  exact (hU.mul hE).trans_tendsto h2

/-- Limit of the Green boundary form at an endpoint `x = -1 + 2τ`, `τ → 0⁺`, for functions with
expansions `f = -k_f ln τ + c_f + O(τ ln τ)` etc. whose degree-shifted partners satisfy
`k_{f₁} = -k_f`, `c_{f₁} = -c_f + r_f`, `(ν+1) r_f = 2 k_f`. -/
theorem FerrersGreen.boundary_neg {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0))
    (hx : ∀ᶠ x : ℝ in l, (x:ℂ) = -1 + 2*τ x) {f g g1 f1 : ℝ → ℂ} {ν lam kf kg cf cg rf rg : ℂ}
    (hf : (fun x => f x + kf * Real.log (τ x) - cf) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg : (fun x => g x + kg * Real.log (τ x) - cg) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg1 : (fun x => g1 x - kg * Real.log (τ x) - (-cg + rg)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hf1 : (fun x => f1 x - kf * Real.log (τ x) - (-cf + rf)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hrg : (lam+1)*rg = 2*kg) (hrf : (ν+1)*rf = 2*kf) :
    Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x)) l
      (𝓝 (2*(kf*cg - kg*cf))) := by
  obtain ⟨cT, cTU, cTUU, -, -⟩ := FerrersGreen.basic_limits hτ
  obtain ⟨c1, d1⟩ := FerrersGreen.error_limits hτ hf
  obtain ⟨c2, d2⟩ := FerrersGreen.error_limits hτ hg
  obtain ⟨c3, d3⟩ := FerrersGreen.error_limits hτ hg1
  obtain ⟨c4, d4⟩ := FerrersGreen.error_limits hτ hf1
  set U : ℝ → ℂ := fun x => ((Real.log (τ x) : ℝ) : ℂ) with hU
  set V : ℝ → Fin 11 → ℂ := fun x => ![(τ x : ℂ), (τ x : ℂ) * U x, (τ x : ℂ) * U x * U x,
    f x + kf * U x - cf, g x + kg * U x - cg, g1 x - kg * U x - (-cg + rg),
    f1 x - kf * U x - (-cf + rf), U x * (f x + kf * U x - cf), U x * (g x + kg * U x - cg),
    U x * (g1 x - kg * U x - (-cg + rg)), U x * (f1 x - kf * U x - (-cf + rf))] with hV
  have cV : Tendsto V l (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · exact cT
    · exact cTU
    · exact cTUU
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  have cR := ((FerrersGreen.continuous_boundaryRemainder kf kg cf cg rf rg ν lam).tendsto 0).comp cV
  have hR0 : FerrersGreen.boundaryRemainder kf kg cf cg rf rg ν lam 0 = 0 := by
      simp [FerrersGreen.boundaryRemainder]
  rw [hR0] at cR
  have key := (tendsto_const_nhds (x := 2*(kf*cg - kg*cf))).add cR
  rw [add_zero] at key
  refine key.congr' ?_
  filter_upwards [hx] with x hx
  simp only [Function.comp_apply, hV, FerrersGreen.boundaryRemainder, Matrix.cons_val, hU]
  rw [hx]
  linear_combination (cf - kf*U x) * hrg - (cg - kg*U x) * hrf

/-- Limit of the Green boundary form at an endpoint `x = 1 - 2τ`, `τ → 0⁺`, for expansions with
`k_{f₁} = k_f`, `c_{f₁} = c_f + r_f`, `(ν+1) r_f = -2 k_f`. -/
theorem FerrersGreen.boundary_pos {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0))
    (hx : ∀ᶠ x : ℝ in l, (x:ℂ) = 1 - 2*τ x) {f g g1 f1 : ℝ → ℂ} {ν lam kf kg cf cg rf rg : ℂ}
    (hf : (fun x => f x + kf * Real.log (τ x) - cf) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg : (fun x => g x + kg * Real.log (τ x) - cg) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg1 : (fun x => g1 x + kg * Real.log (τ x) - (cg + rg)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hf1 : (fun x => f1 x + kf * Real.log (τ x) - (cf + rf)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hrg : (lam+1)*rg = -2*kg) (hrf : (ν+1)*rf = -2*kf) :
    Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x)) l
      (𝓝 (2*(kg*cf - kf*cg))) := by
  obtain ⟨cT, cTU, cTUU, -, -⟩ := FerrersGreen.basic_limits hτ
  obtain ⟨c1, d1⟩ := FerrersGreen.error_limits hτ hf
  obtain ⟨c2, d2⟩ := FerrersGreen.error_limits hτ hg
  obtain ⟨c3, d3⟩ := FerrersGreen.error_limits hτ hg1
  obtain ⟨c4, d4⟩ := FerrersGreen.error_limits hτ hf1
  set U : ℝ → ℂ := fun x => ((Real.log (τ x) : ℝ) : ℂ) with hU
  set V : ℝ → Fin 11 → ℂ := fun x => ![(τ x : ℂ), (τ x : ℂ) * U x, (τ x : ℂ) * U x * U x,
    f x + kf * U x - cf, g x + kg * U x - cg, g1 x + kg * U x - (cg + rg),
    f1 x + kf * U x - (cf + rf), U x * (f x + kf * U x - cf), U x * (g x + kg * U x - cg),
    U x * (g1 x + kg * U x - (cg + rg)), U x * (f1 x + kf * U x - (cf + rf))] with hV
  have cV : Tendsto V l (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · exact cT
    · exact cTU
    · exact cTUU
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  have cR := ((FerrersGreen.continuous_boundaryRemainderPos kf kg cf cg rf rg ν
      lam).tendsto 0).comp cV
  have hR0 : FerrersGreen.boundaryRemainderPos kf kg cf cg rf rg ν lam 0 = 0 := by
      simp [FerrersGreen.boundaryRemainderPos]
  rw [hR0] at cR
  have key := (tendsto_const_nhds (x := 2*(kg*cf - kf*cg))).add cR
  rw [add_zero] at key
  refine key.congr' ?_
  filter_upwards [hx] with x hx
  simp only [Function.comp_apply, hV, FerrersGreen.boundaryRemainderPos, Matrix.cons_val, hU]
  rw [hx]
  linear_combination (cf - kf*U x) * hrg - (cg - kg*U x) * hrf

/-- `𝖰_ν(-x) = -cos(νπ) 𝖰_ν(x) - (π/2) sin(νπ) 𝖯_ν(x)` (DLMF 14.9.10 solved for `𝖰_ν(-x)`), valid
for every regular `ν`, integers included. -/
theorem FerrersGreen.ferrersQ_neg {ν : ℂ} (h : LegendreQRegular ν 0) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν 0 (-x) = -cos (ν*π)*ferrersQ ν 0 x - π/2*sin (ν*π)*ferrersP ν 0 x := by
  have pyth := sin_sq_add_cos_sq (ν*π/2)
  rw [ferrersQ_even_odd, ferrersQ_even_odd, ferrersP_regular h hx, ferrersEven_neg, ferrersOdd_neg,
    legendre_sin_two_mul_half, legendre_cos_two_mul_half]
  simp only [add_zero, sub_zero, cpow_zero, one_mul]
  linear_combination (π:ℂ) * (Gamma ((ν+2)/2) * (Gamma ((ν+1)/2))⁻¹) * cos (ν*π/2) *
    ferrersOdd ν 0 x * pyth

/-- Any solution `f` of the Ferrers (Legendre, `μ = 0`) equation on `(-1,1)` is continuous on
`(-1,1)`. -/
theorem FerrersGreen.continuousOn_of_solution {α : ℂ} {f : ℝ → ℂ} (hf : IsFerrersSolution α 0 f) :
    ContinuousOn f (Ioo (-1) 1) :=
  fun y hy => (hf y hy).1.continuousAt.continuousWithinAt

/-- The map `x ↦ (1-x)/2` sends `x → 1⁻` to `τ → 0⁺`. -/
theorem FerrersGreen.tendsto_half_right :
    Tendsto (fun x : ℝ => (1-x)/2) (𝓝[<] (1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => (1-x)/2) (𝓝 1) (𝓝 ((1-1)/2)) :=
      (tendsto_const_nhds.sub tendsto_id).div_const 2
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Iio 1))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
    simp only [mem_Ioi]; linarith

/-- `(1-x) ln(1-x) = O(τ ln τ)` with `τ = (1-x)/2`, as `x → 1⁻`. -/
theorem FerrersGreen.one_sub_log_isBigO :
    (fun x : ℝ => (1-x)*Real.log (1-x)) =O[𝓝[<] (1:ℝ)] (fun x => (1-x)/2 * Real.log ((1-x)/2)) := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
  have ht0 : 0 < (1-x)/2 := by linarith [hx.2]
  have ht1 : (1-x)/2 ≤ 1/2 := by linarith [hx.1]
  have hl2 : Real.log 2 ≤ |Real.log ((1-x)/2)| := by
    rw [abs_of_nonpos (Real.log_nonpos ht0.le (by linarith)), ← Real.log_inv]
    exact Real.log_le_log (by norm_num) (by rw [le_inv_comm₀ (by norm_num) ht0]; linarith)
  have hL : (1-x)*Real.log (1-x) = 2*((1-x)/2)*(Real.log 2 + Real.log ((1-x)/2)) := by
    rw [← Real.log_mul (by norm_num) ht0.ne']; ring_nf
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hL, abs_mul, abs_mul, abs_mul, abs_of_pos ht0, abs_two]
  have h2 : |Real.log 2 + Real.log ((1-x)/2)| ≤ 2 * |Real.log ((1-x)/2)| := by
    calc _ ≤ |Real.log 2| + |Real.log ((1-x)/2)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_pos (Real.log_pos (by norm_num))]; linarith
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2*((1-x)/2))
  linarith

/-- DLMF 14.8.3 in the variable `τ = (1-x)/2`: `𝖰_α + ½ ln τ - (-γ - ψ(α+1)) = O(τ ln τ)`. -/
theorem FerrersGreen.ferrersQ_pos_isBigO {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => ferrersQ α 0 x + (1/2:ℂ) * Real.log ((1-x)/2) -
      (-Real.eulerMascheroniConstant - digamma (α+1))) =O[𝓝[<] (1:ℝ)]
      (fun x => (1-x)/2 * Real.log ((1-x)/2)) := by
  refine ((BoundaryAsymptotics.ferrersQ_log_isBigO h).trans
      FerrersGreen.one_sub_log_isBigO).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
  have h1 : (0:ℝ) < 1 - x := by linarith [hx.2]
  have hl : log (2/(1-x):ℂ) = -(Real.log ((1-x)/2) : ℂ) := by
    rw [show (2/(1-x):ℂ) = ((2/(1-x):ℝ):ℂ) by push_cast; rfl, ← ofReal_log (by positivity),
      show 2/(1-x) = ((1-x)/2)⁻¹ by field_simp, Real.log_inv]
    push_cast; ring
  rw [hl]; ring

/-- Negation sends `x → -1⁺` to `x → 1⁻`. -/
theorem FerrersGreen.tendsto_neg_left : Tendsto (fun x : ℝ => -x) (𝓝[>] (-1:ℝ)) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => -x) (𝓝 (-1)) (𝓝 (-(-1))) := tendsto_id.neg
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi (-1)))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : -1 < x)
    simp only [mem_Iio]; linarith

/-- `𝖯_α - 1 = O(τ ln τ)` with `τ = (1-x)/2`, as `x → 1⁻`. -/
theorem FerrersGreen.ferrersP_pos_isBigO (α : ℂ) :
    (fun x : ℝ => ferrersP α 0 x + (0:ℂ) * Real.log ((1-x)/2) - 1) =O[𝓝[<] (1:ℝ)]
      (fun x => (1-x)/2 * Real.log ((1-x)/2)) := by
  have hfun : ferrersP α 0 = fun y : ℝ =>
      regularizedGaussHypergeometric (α+1) (-α) 1 ((1-(y:ℂ))/2) :=
    funext (FerrersGreen.ferrersP_zero_eq_regularizedGaussHypergeometric α)
  have hw := OrthogonalityIntegrals.half_mem_cutPlane (show (-1:ℝ) < 1 by norm_num)
  have hd : DifferentiableAt ℝ (ferrersP α 0) 1 := by
    rw [hfun]
    exact ((differentiableAt_regularizedGaussHypergeometric _ _ _ hw).restrictScalars ℝ).comp (1:ℝ)
      (by fun_prop)
  have h1 := hd.isBigO_sub.mono (nhdsWithin_le_nhds (s := Iio (1:ℝ)))
  rw [FerrersGreen.ferrersP_one] at h1
  have h2 : (fun x : ℝ => x - 1) =O[𝓝[<] (1:ℝ)] (fun x : ℝ => (((1-x)/2 : ℝ) : ℂ)) := by
    refine Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_two, abs_sub_comm]
    linarith [abs_nonneg (1-x)]
  have h3 := BoundaryAsymptotics.isBigO_self_mul_log.comp_tendsto FerrersGreen.tendsto_half_right
  refine (h1.trans (h2.trans h3)).congr_left fun x => ?_
  ring

/-- `𝖰_α` at `-1`: `𝖰_α - ½cos(απ) ln τ - c = O(τ ln τ)`, `τ = (1+x)/2`, with
`c = cos(απ)(γ + ψ(α+1)) - (π/2) sin(απ)`. -/
theorem FerrersGreen.ferrersQ_neg_isBigO {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => ferrersQ α 0 x + (-(1/2)*cos (α*π)) * Real.log ((1+x)/2) -
      (-cos (α*π)*(-Real.eulerMascheroniConstant - digamma (α+1)) - π/2*sin (α*π))) =O[𝓝[>] (-1:ℝ)]
      (fun x => (1+x)/2 * Real.log ((1+x)/2)) := by
  have hQ := (FerrersGreen.ferrersQ_pos_isBigO h).comp_tendsto FerrersGreen.tendsto_neg_left
  have hP := (FerrersGreen.ferrersP_pos_isBigO α).comp_tendsto FerrersGreen.tendsto_neg_left
  have hc := (hQ.const_mul_left (-cos (α*π))).add (hP.const_mul_left (-(π/2*sin (α*π))))
  have hr : (fun x : ℝ => (1-(-x))/2 * Real.log ((1-(-x))/2)) =
      (fun x : ℝ => (1+x)/2 * Real.log ((1+x)/2)) := by
    funext x; ring_nf
  simp only [Function.comp_def] at hc
  rw [hr] at hc
  refine hc.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hq := FerrersGreen.ferrersQ_neg h hx'
  rw [neg_neg] at hq
  rw [hq, show (1-(-x))/2 = (1+x)/2 by ring]
  ring

/-- `τ ln τ = O((1-x²)^{-1/4})` along any filter on which `τ → 0⁺`. -/
theorem FerrersGreen.mul_log_isBigO_weight {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0))
    (h1 : (fun _ : ℝ => (1:ℝ)) =O[l] FerrersGreen.weight) :
    (fun x => τ x * Real.log (τ x)) =O[l] FerrersGreen.weight :=
  (((FerrersGreen.basic_limits hτ).2.2.2.1).isBigO_one ℝ).trans h1

/-- `𝖰_α = O((1-x²)^{-1/4})` at `1`. -/
theorem FerrersGreen.ferrersQ_isBigO_right {α : ℂ} (h : LegendreQRegular α 0) :
    ferrersQ α 0 =O[𝓝[<] (1:ℝ)] FerrersGreen.weight := by
  have h1 := (FerrersGreen.ferrersQ_pos_isBigO h).trans
    (FerrersGreen.mul_log_isBigO_weight FerrersGreen.tendsto_half_right
        FerrersGreen.one_isBigO_right)
  have h2 := (isBigO_ofReal_left.mpr FerrersGreen.log_isBigO_right).const_mul_left (1/2:ℂ)
  have h3 := (isBigO_const_one ℝ (-Real.eulerMascheroniConstant - digamma (α+1) : ℂ)
    (𝓝[<] (1:ℝ))).trans FerrersGreen.one_isBigO_right
  exact ((h1.sub h2).add h3).congr_left fun _ => by ring

/-- `𝖰_α = O((1-x²)^{-1/4})` at `-1`. -/
theorem FerrersGreen.ferrersQ_isBigO_left {α : ℂ} (h : LegendreQRegular α 0) :
    ferrersQ α 0 =O[𝓝[>] (-1:ℝ)] FerrersGreen.weight := by
  have h1 := (FerrersGreen.ferrersQ_neg_isBigO h).trans FerrersGreen.mul_log_isBigO_left
  have h2 := (isBigO_ofReal_left.mpr FerrersGreen.log_isBigO_left).const_mul_left (-(1/2)*cos (α*π))
  have h3 := (isBigO_const_one ℝ (-cos (α*π)*(-Real.eulerMascheroniConstant - digamma (α+1)) -
    π/2*sin (α*π) : ℂ) (𝓝[>] (-1:ℝ))).trans FerrersGreen.one_isBigO_left
  exact ((h1.sub h2).add h3).congr_left fun _ => by ring

/-- Constant term of `𝖰_α` at `+1` (in the variable `τ = (1-x)/2`). -/
def FerrersGreen.constPos (α : ℂ) : ℂ := -Real.eulerMascheroniConstant - digamma (α+1)

/-- Constant term of `𝖰_α` at `-1` (in the variable `τ = (1+x)/2`). -/
def FerrersGreen.constNeg (α : ℂ) : ℂ := -cos (α*π)*FerrersGreen.constPos α - π/2*sin (α*π)

/-- If `LegendreQRegular α 0` (that is, `α ≠ -1, -2, …`), then also `LegendreQRegular (α+1) 0`. -/
theorem FerrersGreen.regular_succ {α : ℂ} (h : LegendreQRegular α 0) : LegendreQRegular (α+1) 0 :=
  fun n hn => h (n+1) (by push_cast; linear_combination hn)

/-- If `LegendreQRegular α 0`, then `α + 1 ≠ 0`. -/
theorem FerrersGreen.regular_ne {α : ℂ} (h : LegendreQRegular α 0) : α + 1 ≠ 0 :=
  fun h' => h 0 (by push_cast; linear_combination h')

/-- For `LegendreQRegular α 0`, the constant terms at `+1` satisfy
`(α+1)(FerrersGreen.constPos (α+1) - FerrersGreen.constPos α) = -1` (from
`ψ(α+2) = ψ(α+1) + 1/(α+1)`). -/
theorem FerrersGreen.constPos_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (α+1)*(FerrersGreen.constPos (α+1) - FerrersGreen.constPos α) = -1 := by
  unfold FerrersGreen.constPos
  rw [Complex.digamma_apply_add_one (α+1) (DegreeDerivative.add_one_ne_neg_nat h)]
  have := FerrersGreen.regular_ne h
  field_simp; ring

/-- For `LegendreQRegular α 0`, the constant terms at `-1` satisfy
`(α+1)(FerrersGreen.constNeg (α+1) + FerrersGreen.constNeg α) = -cos(απ)`. -/
theorem FerrersGreen.constNeg_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (α+1)*(FerrersGreen.constNeg (α+1) + FerrersGreen.constNeg α) = -cos (α*π) := by
  have hc := FerrersGreen.constPos_succ h
  unfold FerrersGreen.constNeg
  rw [show (α+1)*π = α*π + π by ring, cos_add_pi, sin_add_pi]
  linear_combination cos (α*π) * hc

/-- Green's identity on `[-1,1]` for two order-zero solutions obeying the recurrence 14.10.4, in
terms of the limits of the boundary form at `±1`. -/
theorem FerrersGreen.integral_green {f g f1 g1 : ℝ → ℂ} {ν lam Bm Bp : ℂ}
    (hf : IsFerrersSolution ν 0 f) (hg : IsFerrersSolution lam 0 g)
    (hrf : ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*deriv f x = (ν+1)*(x*f x - f1 x))
    (hrg : ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*deriv g x = (lam+1)*(x*g x - g1 x))
    (hint : IntervalIntegrable (fun x => f x * g x) volume (-1) 1)
    (hm : Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x))
      (𝓝[>] (-1)) (𝓝 Bm))
    (hp : Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x))
      (𝓝[<] 1) (𝓝 Bp))
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    (∫ x : ℝ in -1..1, f x * g x) = (Bp - Bm) / (ν*(ν+1) - lam*(lam+1)) := by
  set F : ℝ → ℂ := fun y => (1-(y:ℂ)^2)*(f y*deriv g y - g y*deriv f y) with hF
  have hd : ∀ y ∈ Ioo (-1:ℝ) 1, HasDerivAt F ((ν*(ν+1) - lam*(lam+1)) * (f y * g y)) y :=
    fun y hy => FerrersGreen.green hf hg hy
  have hint' := hint.const_mul (ν*(ν+1) - lam*(lam+1))
  have hB : ∀ y ∈ Ioo (-1:ℝ) 1,
      (lam+1)*f y*(y*g y - g1 y) - (ν+1)*g y*(y*f y - f1 y) = F y := by
    intro y hy
    simp only [hF]
    linear_combination -(f y * hrg y hy) + g y * hrf y hy
  have ha := hm.congr' (by
    filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with y hy using hB y hy)
  have hb := hp.congr' (by
    filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with y hy using hB y hy)
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) hd hint' ha hb
  rw [intervalIntegral.integral_const_mul] at hI
  rw [eq_div_iff hc, ← hI]; ring

/-- The identity `x = -1 + 2·((1+x)/2)` (as complex numbers), stated eventually as `x → -1⁺`. -/
theorem FerrersGreen.eventually_ofReal_eq_neg : ∀ᶠ x : ℝ in 𝓝[>] (-1:ℝ), (x:ℂ) = -1 +
    2*(((1+x)/2 : ℝ) : ℂ) :=
  Eventually.of_forall fun x => by push_cast; ring

/-- The identity `x = 1 - 2·((1-x)/2)` (as complex numbers), stated eventually as `x → 1⁻`. -/
theorem FerrersGreen.eventually_ofReal_eq_pos : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), (x:ℂ) = 1 -
    2*(((1-x)/2 : ℝ) : ℂ) :=
  Eventually.of_forall fun x => by push_cast; ring

/-- Expansion of `𝖰_{α+1}` at `-1` in the shape required by `FerrersGreen.boundary_neg`. -/
theorem FerrersGreen.ferrersQ_neg_isBigO_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => ferrersQ (α+1) 0 x - (-(1/2)*cos (α*π)) * Real.log ((1+x)/2) -
      (-FerrersGreen.constNeg α + (FerrersGreen.constNeg (α+1) + FerrersGreen.constNeg α)))
          =O[𝓝[>] (-1:ℝ)]
      (fun x => (1+x)/2 * Real.log ((1+x)/2)) := by
  refine (FerrersGreen.ferrersQ_neg_isBigO (FerrersGreen.regular_succ h)).congr_left fun x => ?_
  unfold FerrersGreen.constNeg FerrersGreen.constPos
  rw [show (α+1)*π = α*π + π by ring, cos_add_pi, sin_add_pi]
  ring

/-- Expansion of `𝖰_{α+1}` at `+1` in the shape required by `FerrersGreen.boundary_pos`. -/
theorem FerrersGreen.ferrersQ_pos_isBigO_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => ferrersQ (α+1) 0 x + (1/2:ℂ) * Real.log ((1-x)/2) -
      (FerrersGreen.constPos α +
          (FerrersGreen.constPos (α+1) - FerrersGreen.constPos α))) =O[𝓝[<] (1:ℝ)]
      (fun x => (1-x)/2 * Real.log ((1-x)/2)) := by
  refine (FerrersGreen.ferrersQ_pos_isBigO (FerrersGreen.regular_succ h)).congr_left fun x => ?_
  unfold FerrersGreen.constPos; ring

/-- For `LegendreQRegular α 0` and `x ∈ (-1,1)`, `(1-x²) 𝖰_α'(x) = (α+1)(x 𝖰_α(x) - 𝖰_{α+1}(x))` (`μ
= 0` case of DLMF 14.10.5). -/
theorem FerrersGreen.ferrersQ_recurrence {α : ℂ} (h : LegendreQRegular α 0) :
    ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*deriv (ferrersQ α 0) x =
      (α+1)*(x*ferrersQ α 0 x - ferrersQ (α+1) 0 x) := fun x hx => by
  rw [ferrersQ_recurrence_4 α 0 h hx]; ring

/-- For `x ∈ (-1,1)`, `(1-x²) 𝖯_α'(x) = (α+1)(x 𝖯_α(x) - 𝖯_{α+1}(x))` (`μ = 0` case of DLMF
14.10.5). -/
theorem FerrersGreen.ferrersP_recurrence (α : ℂ) :
    ∀ x ∈ Ioo (-1:ℝ) 1, (1-(x:ℂ)^2)*deriv (ferrersP α 0) x =
      (α+1)*(x*ferrersP α 0 x - ferrersP (α+1) 0 x) := fun x hx => by
  rw [ferrersP_recurrence_4 α 0 hx]; ring

/-- For `ν`, `λ` with `LegendreQRegular ν 0` and `LegendreQRegular λ 0`, the product `𝖰_ν(x) 𝖰_λ(x)`
is interval integrable on `[-1,1]`. -/
theorem FerrersGreen.intervalIntegrable_QQ {ν lam : ℂ} (hν : LegendreQRegular ν 0)
    (hlam : LegendreQRegular lam 0) :
    IntervalIntegrable (fun x => ferrersQ ν 0 x * ferrersQ lam 0 x) volume (-1) 1 := by
  have c1 := FerrersGreen.continuousOn_of_solution (ferrersQ_isFerrersSolution ν 0)
  have c2 := FerrersGreen.continuousOn_of_solution (ferrersQ_isFerrersSolution lam 0)
  obtain ⟨M, hM⟩ := FerrersGreen.bound c1 (FerrersGreen.ferrersQ_isBigO_left hν)
      (FerrersGreen.ferrersQ_isBigO_right hν)
  obtain ⟨N, hN⟩ := FerrersGreen.bound c2 (FerrersGreen.ferrersQ_isBigO_left hlam)
    (FerrersGreen.ferrersQ_isBigO_right hlam)
  exact FerrersGreen.intervalIntegrable_mul c1 c2 hM hN

/-- For any `ν` and `λ` with `LegendreQRegular λ 0`, the product `𝖯_ν(x) 𝖰_λ(x)` is interval
integrable on `[-1,1]`. -/
theorem FerrersGreen.intervalIntegrable_PQ {lam : ℂ} (ν : ℂ) (hlam : LegendreQRegular lam 0) :
    IntervalIntegrable (fun x => ferrersP ν 0 x * ferrersQ lam 0 x) volume (-1) 1 := by
  have c2 := FerrersGreen.continuousOn_of_solution (ferrersQ_isFerrersSolution lam 0)
  obtain ⟨M, hM⟩ := FerrersGreen.bound (FerrersGreen.continuousOn_ferrersP ν)
      (FerrersGreen.ferrersP_isBigO_left ν)
    (FerrersGreen.ferrersP_isBigO_right ν)
  obtain ⟨N, hN⟩ := FerrersGreen.bound c2 (FerrersGreen.ferrersQ_isBigO_left hlam)
    (FerrersGreen.ferrersQ_isBigO_right hlam)
  exact FerrersGreen.intervalIntegrable_mul (FerrersGreen.continuousOn_ferrersP ν) c2 hM hN

/-- The Green integral of `𝖰_ν 𝖰_λ`. -/
theorem FerrersGreen.integral_QQ {ν lam : ℂ} (hν : LegendreQRegular ν 0)
    (hlam : LegendreQRegular lam 0)
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    (∫ x : ℝ in -1..1, ferrersQ ν 0 x * ferrersQ lam 0 x) =
      (2*((1/2)*FerrersGreen.constPos ν - (1/2)*FerrersGreen.constPos lam) -
        2*((-(1/2)*cos (ν*π))*FerrersGreen.constNeg lam -
            (-(1/2)*cos (lam*π))*FerrersGreen.constNeg ν)) /
        (ν*(ν+1) - lam*(lam+1)) := by
  refine FerrersGreen.integral_green (ferrersQ_isFerrersSolution ν 0)
    (ferrersQ_isFerrersSolution lam 0) (FerrersGreen.ferrersQ_recurrence hν)
        (FerrersGreen.ferrersQ_recurrence hlam)
    (FerrersGreen.intervalIntegrable_QQ hν hlam) ?_ ?_ hc
  · refine FerrersGreen.boundary_neg FerrersGreen.tendsto_half FerrersGreen.eventually_ofReal_eq_neg
        (FerrersGreen.ferrersQ_neg_isBigO hν)
      (FerrersGreen.ferrersQ_neg_isBigO hlam) (FerrersGreen.ferrersQ_neg_isBigO_succ hlam)
      (FerrersGreen.ferrersQ_neg_isBigO_succ hν) ?_ ?_
    · rw [FerrersGreen.constNeg_succ hlam]; ring
    · rw [FerrersGreen.constNeg_succ hν]; ring
  · refine FerrersGreen.boundary_pos FerrersGreen.tendsto_half_right
        FerrersGreen.eventually_ofReal_eq_pos (FerrersGreen.ferrersQ_pos_isBigO hν)
      (FerrersGreen.ferrersQ_pos_isBigO hlam) (FerrersGreen.ferrersQ_pos_isBigO_succ hlam)
      (FerrersGreen.ferrersQ_pos_isBigO_succ hν) ?_ ?_
    · rw [FerrersGreen.constPos_succ hlam]; ring
    · rw [FerrersGreen.constPos_succ hν]; ring

/-- Expansion of `𝖯_{α+1}` at `-1` in the shape required by `FerrersGreen.boundary_neg`. -/
theorem FerrersGreen.ferrersP_neg_one_isBigO_succ (α : ℂ) :
    (fun x : ℝ => ferrersP (α+1) 0 x - FerrersGreen.logCoeff α * Real.log ((1+x)/2) -
      (-FerrersGreen.constTerm α +
          (BoundaryAsymptotics.zeroBalancedConstDeriv (α+1+1) (-(α+1)) +
          BoundaryAsymptotics.zeroBalancedConstDeriv (α+1) (-α)))) =O[𝓝[>] (-1:ℝ)]
      (fun x => (1+x)/2 * Real.log ((1+x)/2)) := by
  refine (FerrersGreen.ferrersP_neg_one_isBigO (α+1)).congr_left fun x => ?_
  have hK := FerrersGreen.logCoeff_succ α
  unfold FerrersGreen.constTerm FerrersGreen.logCoeff
  rw [hK]; ring

/-- Expansion of `𝖯_{α+1}` at `+1` in the shape required by `FerrersGreen.boundary_pos`. -/
theorem FerrersGreen.ferrersP_pos_isBigO_succ (α : ℂ) :
    (fun x : ℝ => ferrersP (α+1) 0 x + (0:ℂ) * Real.log ((1-x)/2) - (1 + 0)) =O[𝓝[<] (1:ℝ)]
      (fun x => (1-x)/2 * Real.log ((1-x)/2)) :=
  (FerrersGreen.ferrersP_pos_isBigO (α+1)).congr_left fun x => by ring

/-- The Green integral of `𝖯_ν 𝖰_λ`. -/
theorem FerrersGreen.integral_PQ {ν lam : ℂ} (hlam : LegendreQRegular lam 0)
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x * ferrersQ lam 0 x) =
      (2*((1/2)*1 - 0*FerrersGreen.constPos lam) -
        2*(FerrersGreen.logCoeff ν * FerrersGreen.constNeg lam - (-(1/2)*cos (lam*π)) *
            FerrersGreen.constTerm ν)) /
        (ν*(ν+1) - lam*(lam+1)) := by
  refine FerrersGreen.integral_green (ferrersP_isFerrersSolution ν 0)
    (ferrersQ_isFerrersSolution lam 0) (FerrersGreen.ferrersP_recurrence ν)
        (FerrersGreen.ferrersQ_recurrence hlam)
    (FerrersGreen.intervalIntegrable_PQ ν hlam) ?_ ?_ hc
  · refine FerrersGreen.boundary_neg FerrersGreen.tendsto_half FerrersGreen.eventually_ofReal_eq_neg
        (FerrersGreen.ferrersP_neg_one_isBigO ν)
      (FerrersGreen.ferrersQ_neg_isBigO hlam) (FerrersGreen.ferrersQ_neg_isBigO_succ hlam)
      (FerrersGreen.ferrersP_neg_one_isBigO_succ ν) ?_ (FerrersGreen.logCoeffDeriv_succ ν)
    rw [FerrersGreen.constNeg_succ hlam]; ring
  · refine FerrersGreen.boundary_pos FerrersGreen.tendsto_half_right
        FerrersGreen.eventually_ofReal_eq_pos (FerrersGreen.ferrersP_pos_isBigO ν)
      (FerrersGreen.ferrersQ_pos_isBigO hlam) (FerrersGreen.ferrersQ_pos_isBigO_succ hlam)
      (FerrersGreen.ferrersP_pos_isBigO_succ ν) ?_ ?_
    · rw [FerrersGreen.constPos_succ hlam]; ring
    · ring

/-- If `0 < re α`, then `LegendreQRegular α 0`. -/
theorem FerrersGreen.regular_of_re_pos {α : ℂ} (h : 0 < α.re) : LegendreQRegular α 0 := by
  intro n hn
  have := congrArg Complex.re hn
  simp at this
  linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- The Green integral of `𝖯_ν 𝖯_λ` on `[-1,1]` in terms of the boundary constants, for all `ν, λ`
with `(ν-λ)(ν+λ+1) ≠ 0`. -/
theorem FerrersGreen.integral_PP (ν lam : ℂ) (h : (ν*(ν+1) - lam*(lam+1)) ≠ 0) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersP lam 0 x) =
      -(2*(FerrersGreen.logCoeff ν * FerrersGreen.constTerm lam - FerrersGreen.logCoeff lam *
          FerrersGreen.constTerm ν)) / (ν*(ν+1) - lam*(lam+1)) := by
  rw [FerrersGreen.integral_green (ferrersP_isFerrersSolution ν 0)
    (ferrersP_isFerrersSolution lam 0) (FerrersGreen.ferrersP_recurrence ν)
        (FerrersGreen.ferrersP_recurrence lam)
    (FerrersGreen.intervalIntegrable_PP ν lam)
    (FerrersGreen.boundary_neg FerrersGreen.tendsto_half FerrersGreen.eventually_ofReal_eq_neg
        (FerrersGreen.ferrersP_neg_one_isBigO ν)
      (FerrersGreen.ferrersP_neg_one_isBigO lam) (FerrersGreen.ferrersP_neg_one_isBigO_succ lam)
      (FerrersGreen.ferrersP_neg_one_isBigO_succ ν) (FerrersGreen.logCoeffDeriv_succ lam)
          (FerrersGreen.logCoeffDeriv_succ ν))
    (FerrersGreen.boundary_pos FerrersGreen.tendsto_half_right FerrersGreen.eventually_ofReal_eq_pos
        (FerrersGreen.ferrersP_pos_isBigO ν)
      (FerrersGreen.ferrersP_pos_isBigO lam) (FerrersGreen.ferrersP_pos_isBigO_succ lam)
      (FerrersGreen.ferrersP_pos_isBigO_succ ν) (by ring) (by ring)) h]
  unfold FerrersGreen.constTerm FerrersGreen.logCoeff
  ring

/-- Closed form of the boundary constant `K_ν C_λ - K_λ C_ν`. -/
theorem FerrersGreen.boundary_const {ν lam : ℂ} (hν : LegendreQRegular ν 0)
    (hlam : LegendreQRegular lam 0) :
    (π:ℂ)^2 * (FerrersGreen.logCoeff ν * FerrersGreen.constTerm lam - FerrersGreen.logCoeff lam *
        FerrersGreen.constTerm ν) =
      π*sin ((lam-ν)*π) + 2*sin (ν*π)*sin (lam*π)*(digamma (ν+1)-digamma (lam+1)) := by
  have hr : ∀ {α : ℂ}, LegendreQRegular α 0 → ∀ m : ℕ, α+1 ≠ -(m:ℂ) := by
    intro α hα m hm
    exact hα m (by linear_combination hm)
  have e1 := FerrersGreen.logCoeffDeriv_eq (hr hν)
  have e2 := FerrersGreen.logCoeffDeriv_eq (hr hlam)
  have k1 := FerrersGreen.logCoeff_eq ν
  have k2 := FerrersGreen.logCoeff_eq lam
  unfold FerrersGreen.constTerm FerrersGreen.logCoeff
  rw [e1, e2]
  rw [show (lam-ν)*π = π*lam - π*ν by ring, sin_sub, mul_comm ν, mul_comm lam]
  linear_combination ((π:ℂ)*cos (π*lam) + 2*(digamma (ν+1) - digamma (lam+1))*π*
      BoundaryAsymptotics.zeroBalancedConst (lam+1) (-lam)) * k1 +
    (-(π:ℂ)*cos (π*ν) - 2*(digamma (ν+1) - digamma (lam+1))*sin (π*ν)) * k2

/-- `K'_α = cos(πα) + 2 (1/Γ)'(α+1)/Γ(-α)` for every `α`. -/
theorem FerrersGreen.logCoeffDeriv_eq_all (α : ℂ) :
    BoundaryAsymptotics.zeroBalancedConstDeriv (α+1) (-α) = cos (π*α) +
        2*(DLMF.Gamma.recipGammaDeriv 1 (α+1) * (Gamma (-α))⁻¹) := by
  have hr := BoundaryAsymptotics.reflection_deriv (-α)
  rw [show (1:ℂ) - -α = α+1 by ring, mul_neg, cos_neg] at hr
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' := mul_left_cancel₀ hpi hr
  unfold BoundaryAsymptotics.zeroBalancedConstDeriv
  rw [← hr']
  ring

/-- Closed form of the boundary constant for all degrees, with `S(α) = π (1/Γ)'(α+1)/Γ(-α)`
(the removable extension of `sin(πα) ψ(α+1)`). -/
theorem FerrersGreen.boundary_const_all (ν lam : ℂ) :
    (π:ℂ)^2 * (FerrersGreen.logCoeff ν * FerrersGreen.constTerm lam - FerrersGreen.logCoeff lam *
        FerrersGreen.constTerm ν) =
      π*sin ((lam-ν)*π) + 2*(sin (π*lam) *
          (π * DLMF.Gamma.recipGammaDeriv 1 (ν+1) * (Gamma (-ν))⁻¹) -
        sin (π*ν) * (π * DLMF.Gamma.recipGammaDeriv 1 (lam+1) * (Gamma (-lam))⁻¹)) := by
  have e1 := FerrersGreen.logCoeffDeriv_eq_all ν
  have e2 := FerrersGreen.logCoeffDeriv_eq_all lam
  have k1 := FerrersGreen.logCoeff_eq ν
  have k2 := FerrersGreen.logCoeff_eq lam
  unfold FerrersGreen.constTerm FerrersGreen.logCoeff
  rw [e1, e2]
  rw [show (lam-ν)*π = π*lam - π*ν by ring, sin_sub]
  linear_combination ((π:ℂ)*cos (π*lam) +
      2*π*(DLMF.Gamma.recipGammaDeriv 1 (lam+1) * (Gamma (-lam))⁻¹)) * k1 +
    (-(π:ℂ)*cos (π*ν) - 2*π*(DLMF.Gamma.recipGammaDeriv 1 (ν+1) * (Gamma (-ν))⁻¹)) * k2

end DLMF.Legendre
end
