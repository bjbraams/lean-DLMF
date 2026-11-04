/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Regularized
public import DLMF.Hypergeometric.ConnectionFormulas
public import DLMF.Gamma.RecipGammaDeriv

/-!
# Parameter derivatives of the regularized Kummer series

This file differentiates the regularized Kummer series termwise in its parameters and derives
the logarithmic series of the Tricomi connection numerator at positive integer second
parameters.

## Main results

* `hasSum_deriv_regularizedConfluent_comp`: termwise differentiation of the regularized Kummer
  series along entire parameter curves.
* `deriv_pochhammer_mul_recip_Gamma_add_nat`: the derivative of `(x)_m / Γ(x+m)` through the entire
  function `(1/Γ)'`, valid for every argument.
* `deriv_tricomi_numerator_nat`, `tricomi_numerator_nat_series`: the derivative of the
  regularized connection numerator at a positive integer parameter, split into a finite
  singular part and a convergent series.
* `deriv_tricomi_numerator_nat_recipGamma`, `tricomi_numerator_nat_series_recipGamma`: the same
  with `ψ(a+k)/Γ(a-n)` written through `(1/Γ)'`; stronger than DLMF, valid for all `a`.

## Implementation notes

The domination argument adapts `hasSum_deriv_regularizedGaussHypergeometricFun_comp` from
`DLMF.Hypergeometric.ConnectionFormulas`, using the entire confluent majorant.
-/

@[expose] public section

open Complex Filter Set FormalMultilinearSeries DLMF.Hypergeometric
open scoped Real Nat Topology ENNReal

noncomputable section
set_option autoImplicit false

namespace DLMF.Confluent

open DLMF.Gamma

/-- Termwise differentiation of the regularized Kummer series along entire parameter curves. -/
theorem hasSum_deriv_regularizedConfluent_comp {A B : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (z : ℂ) (w₀ : ℂ) :
    HasSum (fun n : ℕ => deriv (fun w => pochhammer (A w) n * z ^ n / n.factorial *
        (Gamma (B w + n))⁻¹) w₀)
      (deriv (fun w => regularizedHGFun {A w} {B w} z) w₀) := by
  set T : ℕ → ℂ → ℂ := fun n w => pochhammer (A w) n * z ^ n / n.factorial *
    (Gamma (B w + n))⁻¹ with hT
  have hTd : ∀ n, Differentiable ℂ (T n) := by
    intro n
    have h1 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (A w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hA
    exact ((h1.mul_const _).div_const _).mul
      (differentiable_one_div_Gamma.comp (hB.add_const _))
  have hfun : (fun w => regularizedHGFun {A w} {B w} z) = fun w => ∑' n, T n w := by
    funext w; rw [regularizedConfluent_eq_tsum]
  rw [hfun]
  -- domination near `w₀`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - (B w₀).re ≤ N := exists_nat_ge _
  have hre0 : 2 ≤ (B w₀ + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  obtain ⟨V, hVopen, hc₀V, hV⟩ := exists_open_norm_Gamma_add_nat_gt hre0
  have hevA : ∀ᶠ w in 𝓝 w₀, ‖A w‖ < ‖A w₀‖ + 1 :=
    hA.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  have hevC : ∀ᶠ w in 𝓝 w₀, (B w₀).re - 1 < (B w).re :=
    (Complex.continuous_re.comp hB.continuous).continuousAt.eventually
      (lt_mem_nhds (by show (B w₀).re - 1 < (B w₀).re; linarith))
  have hevV : ∀ᶠ w in 𝓝 w₀, B w ∈ V := hB.continuous.continuousAt (hVopen.mem_nhds hc₀V)
  have hevF : ∀ᶠ w in 𝓝 w₀, ∀ n ∈ Finset.range N, ‖T n w‖ < ‖T n w₀‖ + 1 := by
    rw [Finset.eventually_all]
    intro n _
    exact (hTd n).continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨U, hU, hUopen, hw₀U⟩ :=
    eventually_nhds_iff.mp (hevA.and (hevC.and (hevV.and hevF)))
  set p := regularizedHGFunSeries {((‖A w₀‖ + 1 : ℝ) : ℂ)} {1 - (N : ℂ)} with hp
  have hz' : (‖z‖₊ : ENNReal) < p.radius := by
    rw [hp, radius_regularizedConfluentSeries]
    exact ENNReal.coe_lt_top
  have hm : 0 < ‖Gamma (B w₀ + N)‖ / 2 := by
    have hpole : ∀ k : ℕ, B w₀ + N ≠ -k := fun k h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
    positivity
  set u : ℕ → ℝ := fun n => if n < N then ‖T n w₀‖ + 1 else
    (‖Gamma (B w₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (‖z‖₊ : ℝ) ^ n) with hu
  have hus : Summable u := by
    refine (summable_nat_add_iff N).mp ?_
    have := ((p.summable_norm_mul_pow hz').mul_left ((‖Gamma (B w₀ + N)‖ / 2)⁻¹))
    refine ((summable_nat_add_iff N).mpr this).congr fun n => ?_
    simp only [hu, show ¬ n + N < N by omega, ite_false]
  refine hasSum_deriv_of_summable_norm hus (fun n => (hTd n).differentiableOn) hUopen
    (fun n w hw => ?_) hw₀U
  obtain ⟨hAw, hCw, hVw, hFw⟩ := hU w hw
  by_cases hn : n < N
  · simp only [hu, hn, ite_true]
    exact (hFw n (Finset.mem_range.mpr hn)).le
  · simp only [hu, hn, ite_false]
    have hre : 1 ≤ (B w + N).re := by
      simp only [Complex.add_re, Complex.natCast_re] at hre0 ⊢
      linarith
    simpa only [coe_nnnorm] using
      norm_confluent_term_le_majorant hAw.le hre hm (hV _ hVw).le (not_lt.mp hn)

/-- The derivative of `x ↦ (x)_m` times `1/Γ(x+m)`, through the entire function `(1/Γ)'`.
Valid for every `y`, including the poles of `Γ`. -/
theorem deriv_pochhammer_mul_recip_Gamma_add_nat (y : ℂ) (m : ℕ) :
    deriv (fun x : ℂ => pochhammer x m) y * (Gamma (y + m))⁻¹ =
      recipGammaDeriv 1 y - pochhammer y m * recipGammaDeriv 1 (y + m) := by
  have hp : HasDerivAt (fun x : ℂ => pochhammer x m) (deriv (fun x : ℂ => pochhammer x m) y) y :=
    (Polynomial.differentiable (ascPochhammer ℂ m) y).hasDerivAt
  have hg := (hasDerivAt_recip_Gamma' (y + m)).comp y ((hasDerivAt_id y).add_const (m : ℂ))
  have h := hp.mul hg
  change HasDerivAt (fun x : ℂ => pochhammer x m * (Gamma (x + m))⁻¹) _ y at h
  have heq : (fun x : ℂ => pochhammer x m * (Gamma (x + m))⁻¹) = fun x => (Gamma x)⁻¹ :=
    funext fun x => pochhammer_mul_recip_Gamma_add_nat x m
  rw [heq] at h
  have := h.unique (hasDerivAt_recip_Gamma' y)
  simp only [Function.comp_apply, _root_.id] at this
  linear_combination this

/-- Derivative of the regularized connection numerator at a positive integer parameter, with the
products `ψ(a+k)/Γ(a-n)` written through the entire function `(1/Γ)'`:
`ψ(a+k)/Γ(a-n) = -(a-n)_{n+k} (1/Γ)'(a+k)`. Valid for all `a`; the digamma form
`tricomi_numerator_nat_series` follows when `a - n` is not a pole.
Stronger than `tricomi_numerator_nat_series`: valid for all `a`. -/
theorem tricomi_numerator_nat_series_recipGamma (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    Summable (fun k : ℕ =>
      (pochhammer a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
        ((Gamma (a - n))⁻¹ * (log z - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) -
          pochhammer (a - n) (n + k) * recipGammaDeriv 1 (a + k))) ∧
    deriv (fun c : ℂ =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹)
      ((n : ℂ) + 1) =
      ∑' k : ℕ,
        (pochhammer a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
          ((Gamma (a - n))⁻¹ * (log z - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) -
            pochhammer (a - n) (n + k) * recipGammaDeriv 1 (a + k)) +
      z ^ (-(n : ℂ)) * (Gamma a)⁻¹ * ∑ j ∈ Finset.range n,
        pochhammer (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) := by
  set c₀ : ℂ := n + 1 with hc₀
  set β : ℂ := a - n with hβ
  set Q : ℂ → ℂ := fun c => regularizedHGFun {a} {c} z with hQ
  set S : ℂ → ℂ := fun c => regularizedHGFun {a - c + 1} {2 - c} z with hS
  set q : ℕ → ℂ := fun k => pochhammer a k * z ^ k / k.factorial *
    (Gamma ((n : ℂ) + 1 + k))⁻¹ with hq
  set P : ℂ := pochhammer β n with hP
  set D : ℕ → ℂ := fun j => deriv (fun y : ℂ => pochhammer y j) β with hD
  have eβ : a - c₀ + 1 = β := by rw [hc₀, hβ]; ring
  have eC : 2 - c₀ = 1 - (n : ℂ) := by rw [hc₀]; ring
  have hQd : Differentiable ℂ Q :=
    differentiable_regularizedConfluent_comp (differentiable_const _) differentiable_id z
  have hSd : Differentiable ℂ S :=
    differentiable_regularizedConfluent_comp (by fun_prop) (by fun_prop) z
  have hQ0 : HasSum q (Q c₀) := by
    simpa [hq, hQ, hc₀, regularizedConfluent_eq_tsum] using
      (summable_regularizedConfluent_term a ((n : ℂ) + 1) z).hasSum
  have hQsum := hasSum_deriv_regularizedConfluent_comp (A := fun _ => a)
    (B := fun c => c) (differentiable_const _) differentiable_id z c₀
  have hSsum := hasSum_deriv_regularizedConfluent_comp (A := fun c => a - c + 1)
    (B := fun c => 2 - c) (by fun_prop) (by fun_prop) z c₀
  have hmn : ∀ k : ℕ, ∀ j : ℕ, (n : ℂ) + 1 + k ≠ -(j : ℂ) := by
    intro k j hj
    have := congrArg re hj
    simp at this
    linarith [Nat.cast_nonneg n (α := ℝ), Nat.cast_nonneg k (α := ℝ),
      Nat.cast_nonneg j (α := ℝ)]
  have hqd : ∀ k : ℕ, deriv (fun c : ℂ => pochhammer a k * z ^ k / k.factorial *
      (Gamma (c + k))⁻¹) c₀ = -q k * digamma ((n : ℂ) + 1 + k) := by
    intro k
    have hg := ((hasDerivAt_recip_Gamma (hmn k)).comp c₀
      ((hasDerivAt_id c₀).add_const (k : ℂ))).const_mul (pochhammer a k * z ^ k / k.factorial)
    change HasDerivAt (fun c : ℂ => pochhammer a k * z ^ k / k.factorial *
      (Gamma (c + k))⁻¹) _ c₀ at hg
    rw [hg.deriv]
    simp only [hq]
    ring
  set dt : ℕ → ℂ := fun j => deriv (fun c : ℂ => pochhammer (a - c + 1) j * z ^ j / j.factorial *
    (Gamma (2 - c + j))⁻¹) c₀ with hdt
  have htd : ∀ j : ℕ, dt j = z ^ j / j.factorial *
      (-(D j) * (Gamma (1 - (n : ℂ) + j))⁻¹ -
        pochhammer β j * recipGammaDeriv 1 (1 - (n : ℂ) + j)) := by
    intro j
    have hp : HasDerivAt (fun y => pochhammer y j) (D j) (a - c₀ + 1) := by
      rw [eβ]; exact (Polynomial.differentiable (ascPochhammer ℂ j) β).hasDerivAt
    have hl1 : HasDerivAt (fun c : ℂ => a - c + 1) (-1) c₀ := by
      simpa using ((hasDerivAt_id c₀).const_sub a).add_const (1 : ℂ)
    have hl2 : HasDerivAt (fun c : ℂ => 2 - c + j) (-1) c₀ := by
      simpa using ((hasDerivAt_id c₀).const_sub (2 : ℂ)).add_const (j : ℂ)
    have hg := (hasDerivAt_recip_Gamma' (2 - c₀ + j)).comp c₀ hl2
    have h := (((hp.comp c₀ hl1).mul_const (z ^ j)).div_const (j.factorial : ℂ)).mul hg
    change HasDerivAt (fun c : ℂ => pochhammer (a - c + 1) j * z ^ j / j.factorial *
      (Gamma (2 - c + j))⁻¹) _ c₀ at h
    change deriv (fun c : ℂ => pochhammer (a - c + 1) j * z ^ j / j.factorial *
      (Gamma (2 - c + j))⁻¹) c₀ = _
    rw [h.deriv]
    simp only [Function.comp_apply, eβ, eC]
    ring
  have hGk : ∀ k : ℕ, Gamma ((n : ℂ) + 1 + k) = ((k + n).factorial : ℂ) := by
    intro k
    rw [show (n : ℂ) + 1 + k = ((k + n : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial]
  have hG1k : ∀ k : ℕ, Gamma (1 - (n : ℂ) + ((k + n : ℕ) : ℂ)) = (k.factorial : ℂ) := by
    intro k
    rw [show 1 - (n : ℂ) + ((k + n : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial]
  set s : ℕ → ℂ := fun j => pochhammer β j * z ^ j / j.factorial *
    (Gamma (1 - (n : ℂ) + j))⁻¹ with hs
  have hS0 : HasSum s (S c₀) := by
    simpa [hs, hS, eβ, eC, regularizedConfluent_eq_tsum] using
      (summable_regularizedConfluent_term β (1 - (n : ℂ)) z).hasSum
  have hs_shift : ∀ k : ℕ, s (k + n) = P * z ^ n * q k := by
    intro k
    simp only [hs, hq, hP, hGk, hG1k]
    rw [add_comm k n, pochhammer_add β n k, show β + (n : ℂ) = a by rw [hβ]; ring,
      pow_add, add_comm n k]
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hkn : ((k + n).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  have hpole : ∀ j : ℕ, j < n → 1 - (n : ℂ) + j = -((n - 1 - j : ℕ) : ℂ) := by
    intro j hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hS0eq : S c₀ = P * z ^ n * Q c₀ := by
    have h := (hasSum_nat_add_iff' n).mpr hS0
    have hlow : ∑ j ∈ Finset.range n, s j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [hs, hpole j (Finset.mem_range.mp hj), Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
    rw [hlow, sub_zero] at h
    exact h.unique ((hQ0.mul_left (P * z ^ n)).congr_fun fun k => (hs_shift k).symm ▸ rfl)
  have hJP : (Gamma a)⁻¹ * P = (Gamma β)⁻¹ := by
    rw [mul_comm, hP, ← pochhammer_mul_recip_Gamma_add_nat β n, show β + (n : ℂ) =
        a by rw [hβ]; ring]
  have hZ : z ^ (-(n : ℂ)) * z ^ n = 1 := by
    rw [cpow_neg, cpow_natCast]; exact inv_mul_cancel₀ (pow_ne_zero _ hz)
  have hdt_shift : ∀ k : ℕ, (Gamma a)⁻¹ * z ^ (-(n : ℂ)) * dt (k + n) = q k *
      (-(recipGammaDeriv 1 β - pochhammer β (n + k) * recipGammaDeriv 1 (a + k)) +
        (Gamma β)⁻¹ * digamma (k + 1)) := by
    intro k
    have hk1 : ∀ j : ℕ, (k : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [Nat.cast_nonneg k (α := ℝ), Nat.cast_nonneg j (α := ℝ)]
    have e0 : 1 - (n : ℂ) + ((k + n : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
    have e1 : (Gamma a)⁻¹ = pochhammer a k * (Gamma (a + k))⁻¹ :=
      (pochhammer_mul_recip_Gamma_add_nat a k).symm
    have e2 : D (k + n) * (Gamma (a + k))⁻¹ =
        recipGammaDeriv 1 β - pochhammer β (n + k) * recipGammaDeriv 1 (a + k) := by
      have h := deriv_pochhammer_mul_recip_Gamma_add_nat β (k + n)
      rw [show β + ((k + n : ℕ) : ℂ) = a + k by rw [hβ]; push_cast; ring, add_comm k n] at h
      rw [add_comm k n]; exact h
    have e3 : (Gamma a)⁻¹ * pochhammer β (k + n) = (Gamma β)⁻¹ * pochhammer a k := by
      rw [add_comm k n, pochhammer_add β n k, show β + (n : ℂ) = a by rw [hβ]; ring, ← hJP, hP]
      ring
    have e4 : z ^ (-(n : ℂ)) * z ^ (k + n) = z ^ k := by
      rw [pow_add]; linear_combination z ^ k * hZ
    have e5 := recipGammaDeriv_one_eq hk1
    have e6 := Gamma_nat_eq_factorial k
    have e7 : pochhammer β (n + k) = pochhammer β (k + n) := by rw [add_comm]
    rw [htd, e0, e5]
    simp only [hq, hGk]
    rw [e6, add_comm n k]
    linear_combination
      ((Gamma a)⁻¹ * ((k + n).factorial : ℂ)⁻¹ * (-(D (k + n)) * (k.factorial : ℂ)⁻¹ -
        pochhammer β (k + n) * (-digamma (k + 1) * (k.factorial : ℂ)⁻¹))) * e4 +
      (z ^ k * ((k + n).factorial : ℂ)⁻¹ * (-(D (k + n)) * (k.factorial : ℂ)⁻¹)) * e1 +
      (z ^ k * ((k + n).factorial : ℂ)⁻¹ * (-(k.factorial : ℂ)⁻¹) * pochhammer a k) * e2 +
      (z ^ k * ((k + n).factorial : ℂ)⁻¹ * (digamma (k + 1) * (k.factorial : ℂ)⁻¹)) * e3 +
      (z ^ k * ((k + n).factorial : ℂ)⁻¹ * (k.factorial : ℂ)⁻¹ * pochhammer a k *
        recipGammaDeriv 1 (a + k)) * e7
  have hdt_low : ∀ j ∈ Finset.range n, dt j =
      -(pochhammer β j * z ^ j / j.factorial *
        ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ))) := by
    intro j hj
    rw [htd, hpole j (Finset.mem_range.mp hj), recipGammaDeriv_one_neg_nat,
      Gamma_neg_nat_eq_zero, inv_zero]
    ring
  have hG : HasDerivAt (fun c : ℂ => (Gamma (a - c + 1))⁻¹) (-recipGammaDeriv 1 β) c₀ := by
    have hg : HasDerivAt (fun y : ℂ => (Gamma y)⁻¹) (recipGammaDeriv 1 β) (a - c₀ + 1) := by
      rw [eβ]; exact hasDerivAt_recip_Gamma' β
    have hh := hg.comp c₀ (((hasDerivAt_id c₀).const_sub a).add_const (1 : ℂ))
    change HasDerivAt (fun c : ℂ => (Gamma (a - c + 1))⁻¹) _ c₀ at hh
    convert hh using 1; simp
  have hpow : HasDerivAt (fun c : ℂ => z ^ (1 - c))
      (-(z ^ (-(n : ℂ)) * log z)) c₀ := by
    have h := ((hasDerivAt_id c₀).const_sub (1 : ℂ)).const_cpow (c := z) (Or.inl hz)
    simpa only [_root_.id, hc₀, show 1 - ((n : ℂ) + 1) = -(n : ℂ) by ring,
      neg_mul, mul_neg, mul_one] using h
  have hR := ((hQd c₀).hasDerivAt.mul hG).sub
    ((hpow.mul (hSd c₀).hasDerivAt).mul_const (Gamma a)⁻¹)
  have hRderiv := hR.deriv
  change deriv (fun c : ℂ => regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
      z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹) c₀ = _ at hRderiv
  simp only [eβ, show 1 - c₀ = -(n : ℂ) by rw [hc₀]; ring] at hRderiv
  rw [hS0eq] at hRderiv
  have hRsimple : deriv (fun c : ℂ => regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
      z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹) c₀ =
      deriv Q c₀ * (Gamma β)⁻¹ - Q c₀ * recipGammaDeriv 1 β + log z * (Gamma β)⁻¹ * Q c₀ -
        (Gamma a)⁻¹ * z ^ (-(n : ℂ)) * deriv S c₀ := by
    rw [hRderiv]
    linear_combination (log z * Q c₀ * (Gamma a)⁻¹ * P) * hZ + log z * Q c₀ * hJP
  have hTail : HasSum (fun k => q k *
      ((Gamma β)⁻¹ * (log z - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) -
        pochhammer β (n + k) * recipGammaDeriv 1 (a + k)))
      (deriv Q c₀ * (Gamma β)⁻¹ - Q c₀ * recipGammaDeriv 1 β + log z * (Gamma β)⁻¹ * Q c₀ -
        (Gamma a)⁻¹ * z ^ (-(n : ℂ)) * (deriv S c₀ - ∑ j ∈ Finset.range n, dt j)) := by
    have h := (((hQsum.mul_right (Gamma β)⁻¹).sub (hQ0.mul_left (recipGammaDeriv 1 β))).add
      (hQ0.mul_left (log z * (Gamma β)⁻¹))).sub
      (((hasSum_nat_add_iff' n).mpr hSsum).mul_left ((Gamma a)⁻¹ * z ^ (-(n : ℂ))))
    convert h using 1
    · funext k
      rw [hqd, ← mul_assoc, hdt_shift]
      ring
    · simp only [hQ, hS]
      ring
  refine ⟨hTail.summable, ?_⟩
  change _ = (∑' k : ℕ, q k *
      ((Gamma β)⁻¹ * (log z - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) -
        pochhammer β (n + k) * recipGammaDeriv 1 (a + k))) + _
  rw [hTail.tsum_eq]
  have hFin : ∑ j ∈ Finset.range n, dt j = -(∑ j ∈ Finset.range n,
      pochhammer β j * z ^ j / j.factorial *
        ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ))) := by
    simp_rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hdt_low
  rw [hFin, hRsimple]
  ring

/-- Derivative of the regularized connection numerator at a positive integer parameter.
The finite sum is the singular part; the infinite sum supplies the logarithmic part. -/
theorem tricomi_numerator_nat_series (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    Summable (fun k : ℕ =>
      (pochhammer a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
        (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))) ∧
    deriv (fun c : ℂ =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹)
      ((n : ℂ) + 1) =
      (Gamma (a - n))⁻¹ * ∑' k : ℕ,
        (pochhammer a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
          (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) +
      z ^ (-(n : ℂ)) * (Gamma a)⁻¹ * ∑ j ∈ Finset.range n,
        pochhammer (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) := by
  obtain ⟨hsum, hderiv⟩ := tricomi_numerator_nat_series_recipGamma a n hz
  have hG : Gamma (a - n) ≠ 0 := Gamma_ne_zero ha
  have hk : ∀ k : ℕ,
      (pochhammer a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
        ((Gamma (a - n))⁻¹ * (log z - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) -
          pochhammer (a - n) (n + k) * recipGammaDeriv 1 (a + k)) =
      (Gamma (a - n))⁻¹ * ((pochhammer a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
        (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))) := by
    intro k
    have hpole : ∀ m : ℕ, a - n + ((n + k : ℕ) : ℂ) ≠ -(m : ℂ) :=
      not_neg_nat_add_nat ha (n + k)
    have h := recip_Gamma_mul_digamma_add_nat (x := a - n) (n + k) hpole
    rw [show a - n + ((n + k : ℕ) : ℂ) = a + k by push_cast; ring] at h
    linear_combination (-(pochhammer a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹)) * h
  refine ⟨?_, ?_⟩
  · refine (hsum.mul_left (Gamma (a - n))).congr fun k => ?_
    rw [hk, ← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  · rw [hderiv, ← tsum_mul_left]
    simp only [hk]

/-- Derivative of the regularized connection numerator at a positive integer parameter.
The finite sum is the singular part; the infinite sum supplies the logarithmic part. -/
theorem deriv_tricomi_numerator_nat (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    deriv (fun c : ℂ =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹)
      ((n : ℂ) + 1) =
      (Gamma (a - n))⁻¹ * ∑' k : ℕ,
        (pochhammer a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
          (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) +
      z ^ (-(n : ℂ)) * (Gamma a)⁻¹ * ∑ j ∈ Finset.range n,
        pochhammer (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) :=
  (tricomi_numerator_nat_series a n hz ha).2

/-- `deriv_tricomi_numerator_nat` with `ψ(a+k)/Γ(a-n)` written through `(1/Γ)'`.
Stronger than DLMF: valid for all `a`. -/
theorem deriv_tricomi_numerator_nat_recipGamma (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    deriv (fun c : ℂ =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹)
      ((n : ℂ) + 1) =
      ∑' k : ℕ,
        (pochhammer a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
          ((Gamma (a - n))⁻¹ * (log z - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) -
            pochhammer (a - n) (n + k) * recipGammaDeriv 1 (a + k)) +
      z ^ (-(n : ℂ)) * (Gamma a)⁻¹ * ∑ j ∈ Finset.range n,
        pochhammer (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) :=
  (tricomi_numerator_nat_series_recipGamma a n hz).2

end DLMF.Confluent
