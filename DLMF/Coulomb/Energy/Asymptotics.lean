/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Energy.Basic
public import DLMF.Confluent.AsymptoticConsequences
public import DLMF.Confluent.BasicProperties.Wronskians

/-!
# Coulomb functions `f`, `h`, `s`, `c`: large `|r|`

This file proves the limiting forms of the Whittaker functions `ζ_ℓ`, `ξ_ℓ` as `r → ±∞`
(DLMF 33.21.1–33.21.2).

## Main results

* `coulombZeta_coulombXi_isEquivalent_atTop`: for `ν > 0`, as `r → ∞`,
  `ζ_ℓ(ν,r) ~ e^{-r/ν} (2r/ν)^ν` and the companion form for `ξ_ℓ` (DLMF 33.21.1).
* `coulombZeta_coulombXi_isEquivalent_atBot`: for `ν > 0`, as `r → -∞`,
  `ζ_ℓ(-ν,r) ~ e^{r/ν} (-2r/ν)^{-ν}` and the companion form for `ξ_ℓ` (DLMF 33.21.2).

## Implementation notes

DLMF §33.21(i) describes how the limiting forms of `f`, `h`, `s`, `c` as `r → ±∞` follow from
the connection formulas of §33.16 and the limiting forms of `F_ℓ`, `G_ℓ` (33.10.1), of `ζ_ℓ`,
`ξ_ℓ` and of the Bessel functions (§§10.7(ii), 10.30(ii)). §33.21(ii) cites Curtis (1964a, §6)
for asymptotic expansions. The convergence of `ξ_ℓ` requires the principal branch
`ph(e^{iπ} 2r/ν) = π` built into `coulombXi`; the limits were also checked numerically
(mpmath, 40 digits, `ν = 2.3`, `ℓ = 1`, `|r|` up to 300).
-/

@[expose] public section

open Complex Filter Asymptotics
open scoped Real Topology Nat

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent DLMF.Hypergeometric

/-- The Whittaker combination on the negative axis behind `ξ_ℓ(-ν, r)`. -/
private lemma tendsto_xi_ratio (ℓ : ℕ) {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun x : ℝ => exp (-(I * π * ν)) * (exp (x / 2) * (-(x : ℂ)) ^ (ℓ + 1) *
        kummerU ((ℓ : ℂ) + 1 - ν) (2 * ℓ + 2) (-(x : ℂ))) /
        ((Real.exp (x / 2) * x ^ ν : ℝ) : ℂ)) atTop (𝓝 1) := by
  set a : ℂ := (ℓ : ℂ) + 1 + ν with ha
  set B : ℂ := 2 * (ℓ : ℂ) + 2 with hB
  have haP : ∀ k : ℕ, a ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp [ha] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have h1 := tendsto_regularizedHGFun_mul_exp_neg_atTop a B haP
  have h2 := tendsto_kummerU_mul_cpow_atTop a B
  have h3 : Tendsto (fun x : ℝ => ((x ^ (-2 * ν) * Real.exp (-1 * x) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-2 * ν) 1 one_pos).ofReal
    simpa using this
  set C : ℂ := Gamma a * exp (-a * π * I) / Gamma (B - a) with hC
  have hlim := h1.sub ((h2.const_mul C).mul h3)
  rw [mul_one, mul_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  -- the connection formula at `x`
  have hs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have hBn : ∀ k : ℕ, B ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp [hB] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have hconn := kummerM_eq_kummerU_connection a B hs true
    (by simp [Complex.arg_ofReal_of_nonneg hx.le]) hBn
  simp only [↓reduceIte, neg_mul, one_mul] at hconn
  have hM : kummerM a B x / Gamma B = regularizedHGFun {a} {B} x := by
    rw [kummerM_eq_mul_regularizedHGFun hBn]; field_simp [Gamma_ne_zero hBn]
  rw [exp_pi_mul_I, neg_one_mul, hM] at hconn
  have hBa : B - a = (ℓ : ℂ) + 1 - ν := by rw [hB, ha]; ring
  rw [hBa] at hconn
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set P : ℂ := (x : ℂ) ^ (ν : ℂ) with hP
  have hP0 : P ≠ 0 := by rw [hP, cpow_def_of_ne_zero hx0]; exact exp_ne_zero _
  have e1 : (x : ℂ) ^ (a - B) = P / (x : ℂ) ^ (ℓ + 1) := by
    rw [show a - B = (ν : ℂ) - ((ℓ + 1 : ℕ) : ℂ) by rw [ha, hB]; push_cast; ring,
      cpow_sub _ _ hx0, cpow_natCast]
  have e2 : (x : ℂ) ^ a = (x : ℂ) ^ (ℓ + 1) * P := by
    rw [show a = ((ℓ + 1 : ℕ) : ℂ) + ν by rw [ha]; push_cast; ring, cpow_add _ _ hx0,
      cpow_natCast]
  have e3 : ((x ^ (-2 * ν) * Real.exp (-1 * x) : ℝ) : ℂ) = (P ^ 2)⁻¹ * exp (-x) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.le]
    push_cast
    rw [show (-2 * (ν : ℂ)) = -((ν : ℂ) + ν) by ring, cpow_neg, cpow_add _ _ hx0, ← hP,
      show -1 * (x : ℂ) = -x by ring]
    ring
  have e4 : ((Real.exp (x / 2) * x ^ ν : ℝ) : ℂ) = exp (x / 2) * P := by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.le]
    push_cast
    rfl
  have e5 : (-(x : ℂ)) ^ (ℓ + 1) = (-1) ^ (ℓ + 1) * (x : ℂ) ^ (ℓ + 1) := by
    rw [neg_pow]
  have e6 : exp (((ℓ : ℂ) + 1 - ν) * π * I) = (-1) ^ (ℓ + 1) * exp (-(I * π * ν)) := by
    rw [show ((ℓ : ℂ) + 1 - ν) * π * I = ((ℓ + 1 : ℕ) : ℂ) * (π * I) + -(I * π * ν) by
      push_cast; ring, exp_add, exp_nat_mul, exp_pi_mul_I]
  have e7 : exp (x : ℂ) = exp ((x : ℂ) / 2) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero haP
  have hm : ((-1 : ℂ) ^ (ℓ + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [hconn, e1, e2, e3, e4, e5, e6, hC, hBa, exp_neg (x : ℂ), e7]
  have he := exp_ne_zero ((x : ℂ) / 2)
  field_simp
  ring

/-- **DLMF 33.21.1**: for `ν > 0`, as `r → ∞`, `ζ_ℓ(ν,r) ~ e^{-r/ν} (2r/ν)^ν` and
`ξ_ℓ(ν,r) ~ e^{r/ν} (2r/ν)^{-ν}`. -/
@[dlmf 33.21.E1]
theorem coulombZeta_coulombXi_isEquivalent_atTop (ℓ : ℕ) {ν : ℝ} (hν : 0 < ν) :
    (fun r : ℝ => coulombZeta ℓ ν r) ~[atTop]
        (fun r : ℝ => ((Real.exp (-r / ν) * (2 * r / ν) ^ ν : ℝ) : ℂ)) ∧
      (fun r : ℝ => coulombXi ℓ ν r) ~[atTop]
        (fun r : ℝ => Real.exp (r / ν) * (2 * r / ν) ^ (-ν)) := by
  sorry

/-- **DLMF 33.21.2**: for `ν > 0`, as `r → -∞`, `ζ_ℓ(-ν,r) ~ e^{r/ν} (-2r/ν)^{-ν}` and
`ξ_ℓ(-ν,r) ~ e^{-r/ν} (-2r/ν)^ν`. -/
@[dlmf 33.21.E2]
theorem coulombZeta_coulombXi_isEquivalent_atBot (ℓ : ℕ) {ν : ℝ} (hν : 0 < ν) :
    (fun r : ℝ => coulombZeta ℓ (-ν) r) ~[atBot]
        (fun r : ℝ => ((Real.exp (r / ν) * (-2 * r / ν) ^ (-ν) : ℝ) : ℂ)) ∧
      (fun r : ℝ => coulombXi ℓ (-ν) r) ~[atBot]
        (fun r : ℝ => Real.exp (-r / ν) * (-2 * r / ν) ^ ν) := by
  have hx : Tendsto (fun r : ℝ => -2 * r / ν) atBot atTop := by
    have : Tendsto (fun r : ℝ => -r * (2 / ν)) atBot atTop :=
      tendsto_neg_atBot_atTop.atTop_mul_const (by positivity)
    exact this.congr fun r => by ring
  have hν0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hev : ∀ᶠ r : ℝ in atBot, 0 < -2 * r / ν := by
    filter_upwards [eventually_lt_atBot 0] with r hr
    have : 0 < -2 * r := by linarith
    positivity
  -- reparametrize by `x = -2r/ν`
  have key : ∀ r : ℝ, ∃ x : ℝ, r = -(ν * x) / 2 ∧ -2 * r / ν = x := fun r =>
    ⟨-2 * r / ν, by field_simp, rfl⟩
  constructor
  · refine isEquivalent_of_tendsto_one ?_
    refine ((tendsto_kummerU_mul_cpow_atTop ((ℓ : ℂ) + 1 + ν) (2 * ℓ + 2)).comp hx).congr' ?_
    filter_upwards [hev] with r hr
    obtain ⟨x, rfl, hxr⟩ := key r
    rw [hxr] at hr
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    simp only [Function.comp_apply, Pi.div_apply, hxr]
    unfold coulombZeta
    have hc : 2 * ((-(ν * x) / 2 : ℝ) : ℂ) / ((-ν : ℝ) : ℂ) = x := by push_cast; field_simp
    have he : Real.exp (-(ν * x) / 2 / ν) = Real.exp (-x / 2) := by
      congr 1; field_simp
    rw [hc, he, Complex.ofReal_mul, Complex.ofReal_cpow hr.le, Complex.ofReal_exp]
    push_cast
    rw [show (ℓ : ℂ) + 1 + ν = ((ℓ + 1 : ℕ) : ℂ) + ν by push_cast; ring, cpow_add _ _ hx0,
      cpow_natCast, cpow_neg]
    have hP0 : (x : ℂ) ^ (ν : ℂ) ≠ 0 := by rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _
    have := exp_ne_zero (-(x : ℂ) / 2)
    rw [show (ℓ : ℂ) + 1 - -(ν : ℂ) = ((ℓ + 1 : ℕ) : ℂ) + ν by push_cast; ring]
    field_simp
  · refine isEquivalent_of_tendsto_one ?_
    have h := (continuous_re.tendsto (1 : ℂ)).comp ((tendsto_xi_ratio ℓ hν).comp hx)
    rw [one_re] at h
    refine h.congr' ?_
    filter_upwards [hev] with r hr
    obtain ⟨x, rfl, hxr⟩ := key r
    simp only [Function.comp_apply, Pi.div_apply, hxr]
    rw [Complex.div_ofReal_re]
    have he : Real.exp (-(-(ν * x) / 2) / ν) = Real.exp (x / 2) := by
      congr 1; field_simp
    rw [he]
    congr 1
    unfold coulombXi
    have hc : 2 * ((-(ν * x) / 2 : ℝ) : ℂ) / ((-ν : ℝ) : ℂ) = x := by push_cast; field_simp
    rw [hc]
    push_cast
    ring_nf

end DLMF.Coulomb
