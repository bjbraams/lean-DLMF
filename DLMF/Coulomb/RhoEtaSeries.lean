/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Modified
public import DLMF.Core.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
public import DLMF.Confluent.CoulombIrregular
public import DLMF.Confluent.BasicProperties.IntegerParametersAndLimits
public import DLMF.Coulomb.Basic.AuxiliaryData

/-!
# Coulomb functions: series expansions

This file proves the power series of `F_ℓ` and `F_ℓ'` in `ρ` and the logarithmic series of
`H^±_ℓ` (DLMF §33.6), and the expansions of `F_ℓ` in spherical Bessel functions and in Bessel
functions `I_k`, `J_k`, with the asymptotic form of `G_ℓ` in functions `K_k` (DLMF §33.9).

## Main results

* `powerSeriesCoeff_initial`, `powerSeriesCoeff_recurrence`: the coefficients `A_k^ℓ(η)`
  (DLMF 33.6.3).
* `hasSum_coulombF`, `hasSum_deriv_coulombF`: the power series of `F_ℓ` and `F_ℓ'`
  (DLMF 33.6.1–33.6.2).
* `powerSeriesCoeff_eq_matrixHypergeometric2F1`: `A_k^ℓ` as a terminating `₂F₁` (DLMF 33.6.4).
* `hasSum_coulombHPlus_log`, `hasSum_coulombHMinus_log`: the logarithmic series of `H^±_ℓ`
  (DLMF 33.6.5), for `η ≠ 0`.
* `hasSum_coulombHPlus_log_recipGamma`, `hasSum_coulombHMinus_log_recipGamma`: the pole-free
  form of DLMF 33.6.5, valid for all `η` (stronger than DLMF).
* `besselSeriesCoeffA_initial`, `besselSeriesCoeffA_recurrence`: the coefficients `a_k`
  (DLMF 33.9.2).
* `hasSum_coulombF_sphericalJ`: `F_ℓ(η,ρ) = ρ ∑_{k ≥ 0} a_k j_{ℓ+k}(ρ)` (DLMF 33.9.1).
* `besselSeriesCoeffB_initial`, `besselSeriesCoeffB_recurrence`: the coefficients `b_k`
  (DLMF 33.9.5).
* `coulombF_eq_besselI_series`: the `I`-Bessel expansion for `η > 0` (DLMF 33.9.3).
* `coulombF_eq_besselJ_series`: the `J`-Bessel expansion for `η < 0` (DLMF 33.9.4, corrected).
* `coulombG_isEquivalent_besselK`: the `K`-Bessel asymptotic form of `G_ℓ` as `η → +∞`
  (DLMF 33.9.6–33.9.7).

## Implementation notes

Series are stated with `HasSum` over all `k ∈ ℕ`; the coefficient functions vanish below the
first index of DLMF's sums. The statements were also checked numerically with mpmath.

DLMF 33.9.4 (`η < 0`) as printed, with the same coefficients `b_k` as 33.9.3, fails numerically
(for example `ℓ = 0`, `η = -0.7`, `ρ = 1.2`: the printed right side minus `F_0` is `-0.11`). The
correct expansion has the factor `(-1)^{k+1}`:
`F_ℓ = C_ℓ (2ℓ+1)!/(2|η|)^{2ℓ+1} ρ^{-ℓ} ∑_k (-1)^{k+1} b_k t^{k/2} J_k(2√t)` (residual `1e-31`
for `ℓ = 0, 1, 3`); it follows from 33.9.3 by `t ↦ -t`. Equivalently, `b_k` for `η < 0` obeys
33.9.5 with `+b_{k-2}` replaced by `-b_{k-2}`.
-/

@[expose] public section

open Complex Filter Set Asymptotics
open scoped Real Topology Nat

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent DLMF.Bessel DLMF.Hypergeometric

/-! ### §33.6 Power-series expansions in `ρ` -/

/-- The initial values `A_{ℓ+1}^ℓ = 1`, `A_{ℓ+2}^ℓ = η/(ℓ+1)` of DLMF 33.6.3. -/
@[dlmf 33.6.E3]
theorem powerSeriesCoeff_initial (ℓ : ℕ) (η : ℝ) :
    powerSeriesCoeff ℓ η (ℓ + 1) = 1 ∧ powerSeriesCoeff ℓ η (ℓ + 2) = η / (ℓ + 1) := by
  refine ⟨?_, ?_⟩
  · simp [powerSeriesCoeff, powerSeriesCoeffTerm]
  · rw [powerSeriesCoeff, ite_eq_left (by omega), show ℓ + 2 - (ℓ + 1) = 1 by omega,
      powerSeriesCoeffTerm]

/-- **The recurrence for `A_k^ℓ`** (DLMF 33.6.3):
`(k+ℓ)(k-ℓ-1) A_k^ℓ = 2η A_{k-1}^ℓ - A_{k-2}^ℓ` for `k = ℓ+3, ℓ+4, …`. -/
@[dlmf 33.6.E3]
theorem powerSeriesCoeff_recurrence (ℓ : ℕ) (η : ℝ) {k : ℕ} (hk : ℓ + 3 ≤ k) :
    ((k : ℝ) + ℓ) * ((k : ℝ) - ℓ - 1) * powerSeriesCoeff ℓ η k =
      2 * η * powerSeriesCoeff ℓ η (k - 1) - powerSeriesCoeff ℓ η (k - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = ℓ + 3 + n := ⟨k - (ℓ + 3), by omega⟩
  rw [powerSeriesCoeff, powerSeriesCoeff, powerSeriesCoeff, ite_eq_left (by omega),
    ite_eq_left (by omega), ite_eq_left (by omega), show ℓ + 3 + n - (ℓ + 1) = n + 2 by omega,
    show ℓ + 3 + n - 1 - (ℓ + 1) = n + 1 by omega, show ℓ + 3 + n - 2 - (ℓ + 1) = n by omega,
    powerSeriesCoeffTerm]
  have h : ((n : ℝ) + 2 * ℓ + 3) * ((n : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The `n`-times differentiated equation `w² f'' + (w² - 2ηw - L) f = 0`. -/
private lemma iteratedDeriv_coulomb_ode {f : ℂ → ℂ} (hf : Differentiable ℂ f) {η L : ℂ}
    (hode : ∀ w, w ^ 2 * deriv (deriv f) w + (w ^ 2 - 2 * η * w - L) * f w = 0) (n : ℕ) (w : ℂ) :
    w ^ 2 * iteratedDeriv (n + 2) f w + 2 * n * w * iteratedDeriv (n + 1) f w +
      n * (n - 1) * iteratedDeriv n f w + w ^ 2 * iteratedDeriv n f w +
      2 * n * w * iteratedDeriv (n - 1) f w + n * (n - 1) * iteratedDeriv (n - 2) f w -
      2 * η * (w * iteratedDeriv n f w + n * iteratedDeriv (n - 1) f w) -
      L * iteratedDeriv n f w = 0 := by
  have ha (k : ℕ) (z : ℂ) : AnalyticAt ℂ (iteratedDeriv k f) z := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hf.analyticAt z
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hd (k : ℕ) (z : ℂ) : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f z) z := by
    simpa only [iteratedDeriv_succ] using (ha k z).differentiableAt.hasDerivAt
  induction n generalizing w with
  | zero =>
    have h := hode w
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_zero] at h ⊢
    linear_combination h
  | succ n ih =>
    have hz : ∀ x, (fun x => x ^ 2 * iteratedDeriv (n + 2) f x +
      2 * n * x * iteratedDeriv (n + 1) f x +
      n * (n - 1) * iteratedDeriv n f x + x ^ 2 * iteratedDeriv n f x +
      2 * n * x * iteratedDeriv (n - 1) f x + n * (n - 1) * iteratedDeriv (n - 2) f x -
      2 * η * (x * iteratedDeriv n f x + n * iteratedDeriv (n - 1) f x) -
      L * iteratedDeriv n f x) x = 0 := ih
    have hD : HasDerivAt (fun x => x ^ 2 * iteratedDeriv (n + 2) f x +
      2 * n * x * iteratedDeriv (n + 1) f x +
      n * (n - 1) * iteratedDeriv n f x + x ^ 2 * iteratedDeriv n f x +
      2 * n * x * iteratedDeriv (n - 1) f x + n * (n - 1) * iteratedDeriv (n - 2) f x -
      2 * η * (x * iteratedDeriv n f x + n * iteratedDeriv (n - 1) f x) -
      L * iteratedDeriv n f x)
      ((2 * w * iteratedDeriv (n + 2) f w + w ^ 2 * iteratedDeriv (n + 2 + 1) f w) +
        (2 * n * iteratedDeriv (n + 1) f w + 2 * n * w * iteratedDeriv (n + 1 + 1) f w) +
        n * (n - 1) * iteratedDeriv (n + 1) f w +
        (2 * w * iteratedDeriv n f w + w ^ 2 * iteratedDeriv (n + 1) f w) +
        (2 * n * iteratedDeriv (n - 1) f w + 2 * n * w * iteratedDeriv (n - 1 + 1) f w) +
        n * (n - 1) * iteratedDeriv (n - 2 + 1) f w -
        2 * η * ((iteratedDeriv n f w + w * iteratedDeriv (n + 1) f w) +
          n * iteratedDeriv (n - 1 + 1) f w) -
        L * iteratedDeriv (n + 1) f w) w := by
      have hw : HasDerivAt (fun x : ℂ => x) 1 w := hasDerivAt_id w
      have hw2 : HasDerivAt (fun x : ℂ => x ^ 2) (2 * w) w := by
        simpa using hasDerivAt_pow 2 w
      have := ((((((((hw2.mul (hd (n + 2) w)).add
        ((hw.const_mul (2 * (n : ℂ))).mul (hd (n + 1) w))).add
        ((hd n w).const_mul ((n : ℂ) * (n - 1)))).add (hw2.mul (hd n w))).add
        ((hw.const_mul (2 * (n : ℂ))).mul (hd (n - 1) w))).add
        ((hd (n - 2) w).const_mul ((n : ℂ) * (n - 1)))).sub
        (((hw.mul (hd n w)).add ((hd (n - 1) w).const_mul (n : ℂ))).const_mul (2 * η))).sub
        ((hd n w).const_mul L))
      convert this using 1
      ring
    have h0 := hD.unique (by
      have : (fun x => x ^ 2 * iteratedDeriv (n + 2) f x +
        2 * n * x * iteratedDeriv (n + 1) f x +
        n * (n - 1) * iteratedDeriv n f x + x ^ 2 * iteratedDeriv n f x +
        2 * n * x * iteratedDeriv (n - 1) f x + n * (n - 1) * iteratedDeriv (n - 2) f x -
        2 * η * (x * iteratedDeriv n f x + n * iteratedDeriv (n - 1) f x) -
        L * iteratedDeriv n f x) = fun _ => 0 := funext hz
      rw [this]; exact hasDerivAt_const w (0 : ℂ))
    rw [show n + 1 + 2 = n + 2 + 1 by ring, show n + 1 + 1 = n + 2 by ring,
      show n + 1 - 1 = n by omega, show n + 1 - 2 = n - 1 by omega]
    rcases n with _ | _ | m
    · simp at h0 ⊢; linear_combination h0
    · simp at h0 ⊢; linear_combination h0
    · simp only [
        show m + 1 + 1 - 1 = m + 1 by omega, show m + 1 + 1 - 2 = m by omega] at h0 ⊢
      push_cast at h0 ⊢
      linear_combination h0


/-- `coulombWave` is entire. -/
private lemma differentiable_coulombWave (ℓ : ℕ) (η : ℂ) : Differentiable ℂ (coulombWave ℓ η) :=
  fun z => (hasDerivAt_coulombWave ℓ η z).differentiableAt

/-- The Coulomb equation for `coulombWave` multiplied by `w²`, for all `w`. -/
private lemma coulombWave_ode_mul_sq (ℓ : ℕ) (η : ℂ) (w : ℂ) :
    w ^ 2 * deriv (deriv (coulombWave ℓ η)) w +
      (w ^ 2 - 2 * η * w - ((ℓ : ℂ) * (ℓ + 1))) * coulombWave ℓ η w = 0 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [coulombWave]
  · have h := deriv_deriv_coulombWave ℓ η hw
    have : w ^ 2 * (deriv (deriv (coulombWave ℓ η)) w +
      (1 - 2 * η / w - ℓ * (ℓ + 1) / w ^ 2) * coulombWave ℓ η w) = 0 := by rw [h, mul_zero]
    rw [← this]
    field_simp

/-- The regular part `e^{-iz} M(ℓ+1-iη, 2ℓ+2, 2iz)` of `coulombWave`. -/
private lemma differentiable_exp_mul_kummerM_coulomb (ℓ : ℕ) (η : ℂ) :
    Differentiable ℂ (fun z : ℂ => exp (-I * z) *
      kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z)) := by
  intro z
  have hE : HasDerivAt (fun z : ℂ => exp (-I * z)) (-I * exp (-I * z)) z := by
    have := ((hasDerivAt_id z).const_mul (-I)).cexp
    exact this.congr_deriv (by simp only [mul_one, id]; ring)
  exact (hE.mul (hasDerivAt_kummerM_two_I_mul (α := ℓ + 1 - I * η)
    (two_mul_nat_add_two_ne_neg_nat ℓ) z)).differentiableAt

/-- The derivatives of `coulombWave` at `0` of order `≤ ℓ + 1`. -/
private lemma iteratedDeriv_coulombWave_zero_of_le (ℓ : ℕ) (η : ℂ) {k : ℕ} (hk : k ≤ ℓ + 1) :
    iteratedDeriv k (coulombWave ℓ η) 0 = if k = ℓ + 1 then ((ℓ + 1)! : ℂ) else 0 := by
  obtain ⟨t, ht⟩ : ∃ t, ℓ + 1 = k + t := ⟨ℓ + 1 - k, by omega⟩
  obtain ⟨R₂, -, hR⟩ := iteratedDeriv_mul_pow_sub_of_analytic (k := k) (t := t) (z₀ := (0 : ℂ))
    (R := coulombWave ℓ η) (R₁ := fun z : ℂ => exp (-I * z) *
      kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z))
    (fun z => (differentiable_exp_mul_kummerM_coulomb ℓ η).analyticAt z)
    (fun z => by rw [coulombWave, sub_zero, ← ht]; ring)
  rw [hR 0]
  rcases t with _ | t
  · have hk' : k = ℓ + 1 := by omega
    subst hk'
    simp
  · simp [show k ≠ ℓ + 1 by omega]


/-- The Taylor coefficients of `coulombWave` at `0` are the `A_k^ℓ(η)`. -/
private lemma iteratedDeriv_coulombWave_zero_div_factorial (ℓ : ℕ) (η : ℝ) (k : ℕ) :
    iteratedDeriv k (coulombWave ℓ (η : ℂ)) 0 / (k ! : ℂ) = (powerSeriesCoeff ℓ η k : ℂ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  have hf := differentiable_coulombWave ℓ (η : ℂ)
  rcases le_or_gt k (ℓ + 1) with hk | hk
  · rw [iteratedDeriv_coulombWave_zero_of_le ℓ (η : ℂ) hk]
    split_ifs with h
    · subst h
      rw [(powerSeriesCoeff_initial ℓ η).1, div_self (by exact_mod_cast Nat.factorial_ne_zero _)]
      simp
    · simp [powerSeriesCoeff, show ¬ (ℓ + 1 ≤ k) by omega]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have h := iteratedDeriv_coulomb_ode hf (η := (η : ℂ)) (L := (ℓ : ℂ) * (ℓ + 1))
      (coulombWave_ode_mul_sq ℓ η) (m + 2) 0
    simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega] at h
    have h1 := ih (m + 1) (by omega)
    have h0 := ih m (by omega)
    have hf1 : ((m + 1) ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hf0 : (m ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [div_eq_iff hf1] at h1
    rw [div_eq_iff hf0] at h0
    have hfac : ((m + 2) ! : ℂ) = (m + 2) * (m + 1) * m ! := by
      push_cast [Nat.factorial_succ]; ring
    have hfac1 : ((m + 1) ! : ℂ) = (m + 1) * m ! := by
      push_cast [Nat.factorial_succ]; ring
    rw [h1, h0, hfac1] at h
    -- recurrence for the powerSeriesCoeff
    have hrec : ((m + 2 : ℕ) * ((m + 2 : ℕ) - 1) - (ℓ : ℂ) * (ℓ + 1)) *
        (powerSeriesCoeff ℓ η (m + 2) : ℂ) =
        2 * η * powerSeriesCoeff ℓ η (m + 1) - powerSeriesCoeff ℓ η m := by
      rcases eq_or_lt_of_le (show ℓ + 2 ≤ m + 2 by omega) with he | hlt
      · have hm : m = ℓ := by omega
        subst hm
        rw [(powerSeriesCoeff_initial m η).2, (powerSeriesCoeff_initial m η).1]
        simp only [powerSeriesCoeff, show ¬ (m + 1 ≤ m) by omega, ite_false]
        have : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        push_cast
        field_simp
        ring
      · have := powerSeriesCoeff_recurrence ℓ η (k := m + 2) (by omega)
        simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega] at this
        have hc := congrArg (fun x : ℝ => (x : ℂ)) this
        push_cast at hc ⊢
        linear_combination hc
    have hne : ((m + 2 : ℕ) * ((m + 2 : ℕ) - 1) - (ℓ : ℂ) * (ℓ + 1)) ≠ 0 := by
      have : ((m + 2 : ℕ) * ((m + 2 : ℕ) - 1) - (ℓ : ℂ) * (ℓ + 1)) =
          (((m + 2 + ℓ : ℕ) * (m + 1 - ℓ : ℕ) : ℕ) : ℂ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]
      exact_mod_cast Nat.mul_ne_zero (by omega) (by omega)
    rw [hfac, div_eq_iff (by rw [← hfac]; exact_mod_cast Nat.factorial_ne_zero _)]
    apply mul_left_cancel₀ hne
    push_cast at h hrec hne ⊢
    linear_combination h - (m + 2) * (m + 1) * (m ! : ℂ) * hrec


/-- The power series of `coulombWave` with the coefficients `A_k^ℓ(η)`. -/
private lemma hasSum_powerSeriesCoeff_coulombWave (ℓ : ℕ) (η : ℝ) (z : ℂ) :
    HasSum (fun k : ℕ => (powerSeriesCoeff ℓ η k : ℂ) * z ^ k) (coulombWave ℓ η z) := by
  have ht := Complex.hasSum_taylorSeries_of_entire (differentiable_coulombWave ℓ (η : ℂ)) 0 z
  convert ht using 1
  funext n
  rw [← iteratedDeriv_coulombWave_zero_div_factorial ℓ η n, sub_zero, smul_eq_mul, smul_eq_mul]
  ring

/-- Leibniz's rule for the derivatives at `0` of `M(a, 2ℓ+2, 2iz) e^{-iz}`. -/
private lemma iteratedDeriv_kummerM_mul_exp_zero (ℓ : ℕ) (η : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z) *
      exp (-I * z)) 0 = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
        ((2 * I) ^ j * (pochhammer ((ℓ : ℂ) + 1 - I * η) j / pochhammer (2 * (ℓ : ℂ) + 2) j)) *
        (-I) ^ (n - j) := by
  have hb := two_mul_nat_add_two_ne_neg_nat ℓ
  have hMd : Differentiable ℂ (kummerM ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2)) := fun z =>
    (analyticOnNhd_kummerM hb z (Set.mem_univ _)).differentiableAt
  have hM : ContDiff ℂ ⊤ (fun z : ℂ => kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z)) :=
    (hMd.comp (differentiable_id.const_mul (2 * I))).contDiff
  have hE : ContDiff ℂ ⊤ (fun z : ℂ => exp (-I * z)) := by fun_prop
  rw [show (fun z : ℂ => kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z) * exp (-I * z)) =
    (fun z : ℂ => kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z)) * (fun z => exp (-I * z))
    from rfl, iteratedDeriv_mul (hM.contDiffAt.of_le le_top) (hE.contDiffAt.of_le le_top)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedDeriv_comp_const_mul (hMd.contDiff) (2 * I), iteratedDeriv_kummerM j hb,
    iteratedDeriv_cexp_const_mul]
  simp

/-- **The power series of `F_ℓ`** (DLMF 33.6.1): `F_ℓ(η,ρ) = C_ℓ(η) ∑_{k ≥ ℓ+1} A_k^ℓ(η) ρ^k`,
convergent for all real `ρ` (DLMF §33.6). -/
@[dlmf 33.6.E1]
theorem hasSum_coulombF (ℓ : ℕ) (η ρ : ℝ) :
    HasSum (fun k : ℕ => coulombC ℓ η * powerSeriesCoeff ℓ η k * ρ ^ k) (coulombF ℓ η ρ) := by
  rw [← Complex.hasSum_ofReal, ofReal_coulombF]
  convert (hasSum_powerSeriesCoeff_coulombWave ℓ η ρ).mul_left (coulombC ℓ η : ℂ) using 1
  funext k
  push_cast
  ring

/-- **The power series of `F_ℓ'`** (DLMF 33.6.2):
`F_ℓ'(η,ρ) = C_ℓ(η) ∑_{k ≥ ℓ+1} k A_k^ℓ(η) ρ^{k-1}`, convergent for all real `ρ`. -/
@[dlmf 33.6.E2]
theorem hasSum_deriv_coulombF (ℓ : ℕ) (η ρ : ℝ) :
    HasSum (fun k : ℕ => coulombC ℓ η * k * powerSeriesCoeff ℓ η k * ρ ^ (k - 1))
      (deriv (coulombF ℓ η) ρ) := by
  have hd : deriv (coulombF ℓ η) ρ = ((coulombC ℓ η : ℂ) * coulombWaveDeriv ℓ η ρ).re := by
    have h := hasDerivAt_re_comp
      (((hasDerivAt_coulombWave ℓ η (ρ : ℂ)).comp_ofReal).const_mul (coulombC ℓ η : ℂ))
    have he : (fun y : ℝ => ((coulombC ℓ η : ℂ) * coulombWave ℓ η (y : ℂ)).re) = coulombF ℓ η := by
      funext y; rfl
    rw [he] at h
    exact h.deriv
  have hdiff : Differentiable ℂ (coulombWaveDeriv ℓ (η : ℂ)) := by
    have : deriv (coulombWave ℓ (η : ℂ)) = coulombWaveDeriv ℓ (η : ℂ) :=
      funext fun w => (hasDerivAt_coulombWave ℓ η w).deriv
    rw [← this]
    intro z
    exact ((differentiable_coulombWave ℓ (η : ℂ)).analyticAt z).deriv.differentiableAt
  have hD : deriv (coulombWave ℓ (η : ℂ)) = coulombWaveDeriv ℓ (η : ℂ) :=
    funext fun w => (hasDerivAt_coulombWave ℓ η w).deriv
  have ht := Complex.hasSum_taylorSeries_of_entire hdiff 0 (ρ : ℂ)
  have ht' : HasSum (fun n : ℕ => (coulombC ℓ η : ℂ) * ((n + 1 : ℕ) : ℂ) *
      powerSeriesCoeff ℓ η (n + 1) * (ρ : ℂ) ^ n)
      ((coulombC ℓ η : ℂ) * coulombWaveDeriv ℓ η ρ) := by
    convert ht.mul_left (coulombC ℓ η : ℂ) using 1
    funext n
    rw [← hD, ← iteratedDeriv_succ',
        ← iteratedDeriv_coulombWave_zero_div_factorial ℓ η (n + 1), sub_zero,
      smul_eq_mul, smul_eq_mul, Nat.factorial_succ]
    have : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp
  have hr : HasSum (fun n : ℕ => (((coulombC ℓ η * ((n + 1 : ℕ) : ℝ) *
      powerSeriesCoeff ℓ η (n + 1) * ρ ^ n : ℝ)) : ℂ))
      ((coulombC ℓ η : ℂ) * coulombWaveDeriv ℓ η ρ) := by
    convert ht' using 1; funext n; push_cast; ring
  have hre := Complex.hasSum_re hr
  simp only [Complex.ofReal_re] at hre
  rw [hd, ← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_mul, sub_zero,
    Nat.add_sub_cancel]
  convert hre using 1

/-- **`A_k^ℓ` as a terminating `₂F₁`** (DLMF 33.6.4), `k ≥ ℓ + 1`:
`A_k^ℓ(η) = (-i)^{k-ℓ-1}/(k-ℓ-1)! ₂F₁(ℓ+1-k, ℓ+1-iη; 2ℓ+2; 2)`, the `₂F₁` written as its
finite sum (the series terminates after the term `j = k-ℓ-1`). -/
@[dlmf 33.6.E4]
theorem powerSeriesCoeff_eq_matrixHypergeometric2F1 (ℓ : ℕ) (η : ℝ) {k : ℕ} (hk : ℓ + 1 ≤ k) :
    (powerSeriesCoeff ℓ η k : ℂ) = (-I) ^ (k - ℓ - 1) / ((k - ℓ - 1)! : ℂ) *
      ∑ j ∈ Finset.range (k - ℓ), pochhammer ((ℓ : ℂ) + 1 - k) j *
          pochhammer ((ℓ : ℂ) + 1 - I * η) j /
        (pochhammer (2 * (ℓ : ℂ) + 2) j * j !) * 2 ^ j := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + ℓ + 1 := ⟨k - ℓ - 1, by omega⟩
  rw [show n + ℓ + 1 - ℓ - 1 = n by omega, show n + ℓ + 1 - ℓ = n + 1 by omega,
    show (ℓ : ℂ) + 1 - ((n + ℓ + 1 : ℕ) : ℂ) = -(n : ℂ) by push_cast; ring,
    ← iteratedDeriv_coulombWave_zero_div_factorial]
  set Φ : ℂ → ℂ := fun z => kummerM (ℓ + 1 - I * (η : ℂ)) (2 * ℓ + 2) (2 * I * z) *
    exp (-I * z) with hΦ
  have hψ : coulombWave ℓ (η : ℂ) = (fun z : ℂ => z ^ (ℓ + 1)) * Φ := by
    funext z; simp only [coulombWave, Pi.mul_apply, hΦ]; ring
  have hΦd : ContDiff ℂ ⊤ Φ := by
    have h1 := (differentiable_exp_mul_kummerM_coulomb ℓ (η : ℂ)).contDiff (n := ⊤)
    convert h1 using 1; funext z; simp only [hΦ]; ring
  rw [hψ, iteratedDeriv_mul (by fun_prop) (hΦd.contDiffAt.of_le le_top),
    Finset.sum_eq_single (ℓ + 1)]
  · rw [iteratedDeriv_fun_pow_zero, ite_eq_left rfl, show n + ℓ + 1 - (ℓ + 1) = n by omega, hΦ,
      iteratedDeriv_kummerM_mul_exp_zero, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    rw [pochhammer_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
    have hpow : (-I) ^ n = (-I) ^ (n - j) * (-I) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjn]
    have hc : ((n + ℓ + 1).choose (ℓ + 1) : ℂ) * (ℓ + 1)! / (n + ℓ + 1)! = 1 / n ! := by
      have h := Nat.choose_mul_factorial_mul_factorial (show ℓ + 1 ≤ n + ℓ + 1 by omega)
      rw [show n + ℓ + 1 - (ℓ + 1) = n by omega] at h
      have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hk : ((n + ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      rw [div_eq_div_iff hk hn, one_mul, ← h]
      push_cast; ring
    have hb := two_mul_nat_add_two_ne_neg_nat ℓ
    have hq : pochhammer (2 * (ℓ : ℂ) + 2) j ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hb j
    have hjf : (j ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hnf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [hpow]
    calc _ = ((n + ℓ + 1).choose (ℓ + 1) : ℂ) * (ℓ + 1)! / (n + ℓ + 1)! *
          ((n.choose j : ℂ) * ((2 * I) ^ j * (pochhammer ((ℓ : ℂ) + 1 - I * η) j /
            pochhammer (2 * (ℓ : ℂ) + 2) j)) * (-I) ^ (n - j)) := by ring
      _ = _ := by
        rw [hc]
        field_simp
        rw [mul_pow, neg_pow I]
        push_cast
        ring_nf
        rw [show (-1 : ℂ) ^ (j * 2) = 1 by rw [mul_comm, pow_mul]; simp]
        ring
  · intro i _ hi
    rw [iteratedDeriv_fun_pow_zero]; simp [hi]
  · intro h; simp at h

/-- `Γ(n+1+k) = n! (n+1)_k`. -/
private lemma Gamma_natCast_add_one_add (n k : ℕ) :
    Gamma ((n : ℂ) + 1 + k) = (n ! : ℂ) * pochhammer ((n : ℂ) + 1) k := by
  have hn' : ∀ j : ℕ, (n : ℂ) + 1 ≠ -(j : ℂ) := by
    intro j hj
    have := congrArg re hj
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hG := Gamma_add_nat_div_Gamma_eq (n := k) ((n : ℂ) + 1) hn'
  rw [div_eq_iff (Gamma_ne_zero hn'), Gamma_nat_eq_factorial] at hG
  rw [hG]; ring

/-- The parameter `2ℓ+2` of the Coulomb `U`-function as `n + 1` with `n = 2ℓ+1`. -/
private lemma two_mul_add_two_eq (ℓ : ℕ) :
    (2 * (ℓ : ℂ) + 2) = ((2 * ℓ + 1 : ℕ) : ℂ) + 1 := by push_cast; ring

/-- DLMF 13.2.9 at `b = 2ℓ+2`, multiplied by `(2ℓ+1)! Γ(a-2ℓ-1) z^a`. -/
private lemma hasSum_log_aux (ℓ : ℕ) {a z : ℂ} (hzs : z ∈ slitPlane)
    (han : ∀ k : ℕ, a - ((2 * ℓ + 1 : ℕ) : ℂ) ≠ -(k : ℂ)) (hare : 0 < a.re) :
    HasSum (fun k : ℕ => pochhammer a k / (pochhammer (2 * (ℓ : ℂ) + 2) k * k !) * z ^ (a + k) *
        (log z + Complex.digamma (a + k) - Complex.digamma (1 + k) -
          Complex.digamma (2 * ℓ + 2 + k)))
      ((2 * ℓ + 1)! * Gamma (a - ((2 * ℓ + 1 : ℕ) : ℂ)) *
          (z ^ a * kummerU a (2 * ℓ + 2) z) +
        ∑ k ∈ Finset.Icc 1 (2 * ℓ + 1), ((2 * ℓ + 1)! * (k - 1)! : ℂ) /
          ((2 * ℓ + 1 - k)! * pochhammer (1 - a) k) * z ^ (a - k)) := by
  have hb := two_mul_add_two_eq ℓ
  set n := 2 * ℓ + 1 with hn
  have hz0 : z ≠ 0 := slitPlane_ne_zero hzs
  obtain ⟨hsum, -⟩ := tricomi_numerator_nat_series a n hz0 han
  have hU := kummerU_nat_denom a n hzs han
  have hn0 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  set f : ℕ → ℂ := fun k => pochhammer a k / (pochhammer (n + 1 : ℂ) k * k.factorial) * z ^ k *
    (log z + digamma (a + k) - digamma (1 + k) - digamma (n + k + 1)) with hf_def
  have hf : Summable f := by
    refine (hsum.mul_left (n ! : ℂ)).congr fun k => ?_
    rw [Gamma_natCast_add_one_add, hf_def]
    simp only
    rw [show (k : ℂ) + 1 = 1 + k by ring, show (n : ℂ) + 1 + k = n + k + 1 by ring]
    field_simp
  have hn1 : (-1 : ℂ) ^ (n + 1) = 1 := by
    rw [hn, show 2 * ℓ + 1 + 1 = 2 * (ℓ + 1) by ring, pow_mul]; norm_num
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos hare
  have hGan : Gamma (a - n) ≠ 0 := Gamma_ne_zero han
  have hpochn : pochhammer (1 - a) n * Gamma (a - n) = - Gamma a := by
    have h1 := pochhammer_reflect (a - n) n
    rw [show 1 - (a - n) - n = 1 - a by ring] at h1
    have h2 := Gamma_add_nat_div_Gamma_eq (n := n) (a - n) han
    rw [sub_add_cancel, div_eq_iff hGan] at h2
    rw [h1, show (-1 : ℂ) ^ n = -1 by rw [hn, pow_succ, pow_mul]; norm_num]
    linear_combination h2
  have hT : tsum f = n ! * Gamma (a - n) * (kummerU a ((n : ℂ) + 1) z -
      1 / Gamma a * ∑ k ∈ Finset.Icc 1 n, ((k - 1).factorial : ℂ) * pochhammer (1 - a + k) (n - k) /
        ((n - k).factorial : ℂ) * z ^ (-(k : ℂ))) := by
    rw [hU, hn1]; field_simp; ring
  have hS : ∑ k ∈ Finset.Icc 1 n, ((n ! * (k - 1)! : ℂ)) /
      (((n - k)! : ℂ) * pochhammer (1 - a) k) * z ^ (a - k) =
      -(n ! * Gamma (a - n) / Gamma a) * z ^ a * ∑ k ∈ Finset.Icc 1 n,
        ((k - 1).factorial : ℂ) * pochhammer (1 - a + k) (n - k) /
        ((n - k).factorial : ℂ) * z ^ (-(k : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hp := pochhammer_add (1 - a) k (n - k)
    rw [Nat.add_sub_cancel' (Finset.mem_Icc.mp hk).2] at hp
    have hpk : pochhammer (1 - a) k ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hp
      rw [hp, zero_mul] at hpochn
      exact hGa (neg_eq_zero.mp hpochn.symm)
    rw [sub_eq_add_neg a (k : ℂ), cpow_add _ _ hz0]
    have : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    rw [hp] at hpochn
    linear_combination ((k - 1)! * z ^ a * z ^ (-(k : ℂ)) : ℂ) * hpochn
  convert (hf.hasSum.mul_left (z ^ a)) using 1
  · funext k
    rw [hf_def, cpow_add _ _ hz0, cpow_natCast, hb]
    simp only
    ring_nf
  · rw [hb, hS, hT]
    field_simp
    ring

/-- DLMF 13.2.9 in the pole-free form, at `b = 2ℓ+2`, multiplied by `(2ℓ+1)! z^a`. -/
private lemma hasSum_log_recipGamma_aux (ℓ : ℕ) {a z : ℂ} (hzs : z ∈ slitPlane) :
    HasSum (fun k : ℕ => pochhammer a k / (pochhammer (2 * (ℓ : ℂ) + 2) k * k !) * z ^ (a + k) *
        ((Gamma (a - ((2 * ℓ + 1 : ℕ) : ℂ)))⁻¹ *
            (log z - Complex.digamma (1 + k) - Complex.digamma (2 * ℓ + 2 + k)) -
          pochhammer (a - ((2 * ℓ + 1 : ℕ) : ℂ)) (2 * ℓ + 1 + k) *
            DLMF.Gamma.recipGammaDeriv 1 (a + k)))
      ((2 * ℓ + 1)! * (z ^ a * kummerU a (2 * ℓ + 2) z) -
        ∑ k ∈ Finset.Icc 1 (2 * ℓ + 1), ((2 * ℓ + 1)! * (k - 1)! : ℂ) *
          pochhammer (1 - a + k) (2 * ℓ + 1 - k) / ((2 * ℓ + 1 - k)! * Gamma a) * z ^ (a - k)) := by
  have hb := two_mul_add_two_eq ℓ
  set n := 2 * ℓ + 1 with hn
  have hz0 : z ≠ 0 := slitPlane_ne_zero hzs
  obtain ⟨hsum, -⟩ := tricomi_numerator_nat_series_recipGamma a n hz0
  have hU := kummerU_nat_denom_recipGamma a n hzs
  have hn0 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  set f : ℕ → ℂ := fun k => pochhammer a k / (pochhammer (n + 1 : ℂ) k * k.factorial) * z ^ k *
    ((Gamma (a - n))⁻¹ * (log z - digamma (1 + k) - digamma (n + k + 1)) -
      pochhammer (a - n) (n + k) * DLMF.Gamma.recipGammaDeriv 1 (a + k)) with hf_def
  have hf : Summable f := by
    refine (hsum.mul_left (n ! : ℂ)).congr fun k => ?_
    rw [Gamma_natCast_add_one_add, hf_def]
    simp only
    rw [show (k : ℂ) + 1 = 1 + k by ring, show (n : ℂ) + 1 + k = n + k + 1 by ring]
    field_simp
  have hn1 : (-1 : ℂ) ^ (n + 1) = 1 := by
    rw [hn, show 2 * ℓ + 1 + 1 = 2 * (ℓ + 1) by ring, pow_mul]; norm_num
  have hT : tsum f = n ! * (kummerU a ((n : ℂ) + 1) z -
      1 / Gamma a * ∑ k ∈ Finset.Icc 1 n, ((k - 1).factorial : ℂ) * pochhammer (1 - a + k) (n - k) /
        ((n - k).factorial : ℂ) * z ^ (-(k : ℂ))) := by
    rw [hU, hn1]; field_simp; ring
  convert (hf.hasSum.mul_left (z ^ a)) using 1
  · funext k
    rw [hf_def, cpow_add _ _ hz0, cpow_natCast, hb]
    simp only
    ring_nf
  · rw [hb, hT]
    simp only [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sub_eq_add_neg a (k : ℂ), cpow_add _ _ hz0]
    ring

/-- `e^{-iθ_ℓ} H^+_ℓ = z^a U(a, 2ℓ+2, z)` with `a = 1+ℓ+iη`, `z = -2iρ`. -/
private lemma exp_neg_mul_coulombHPlus (ℓ : ℕ) (η ρ : ℝ) {a z : ℂ} (ha : a = 1 + ℓ + I * η)
    (hz : z = -2 * I * ρ) :
    exp (-(I * coulombTheta ℓ η ρ)) * coulombHPlus ℓ η ρ =
      z ^ a * kummerU a (2 * ℓ + 2) z := by
  rw [coulombHPlus, show (ℓ : ℂ) + 1 + I * η = a by rw [ha]; ring, ← hz,
    ← mul_assoc, ← mul_assoc, ← exp_add]
  simp

/-- `e^{iθ_ℓ} H^-_ℓ = z^a U(a, 2ℓ+2, z)` with `a = 1+ℓ-iη`, `z = 2iρ`. -/
private lemma exp_mul_coulombHMinus (ℓ : ℕ) (η ρ : ℝ) {a z : ℂ} (ha : a = 1 + ℓ - I * η)
    (hz : z = 2 * I * ρ) :
    exp (I * coulombTheta ℓ η ρ) * coulombHMinus ℓ η ρ =
      z ^ a * kummerU a (2 * ℓ + 2) z := by
  rw [coulombHMinus, show (ℓ : ℂ) + 1 - I * η = a by rw [ha]; ring, ← hz,
    ← mul_assoc, ← mul_assoc, ← exp_add]
  simp

/-- **The logarithmic series of `H^+_ℓ`** (DLMF 33.6.5, upper signs), `ρ > 0`, with
`a = 1 + ℓ + iη`, `z = -2iρ`:
`H^+_ℓ = e^{iθ_ℓ}/((2ℓ+1)! Γ(-ℓ+iη)) (∑_{k ≥ 0} … - ∑_{k=1}^{2ℓ+1} …)`, stated as the sum of
the convergent series. The formula needs `η ≠ 0`: at `η = 0` it holds only as a limit, since
`1/Γ(-ℓ)` vanishes while the finite sum has poles. -/
@[dlmf 33.6.E5]
theorem hasSum_coulombHPlus_log (ℓ : ℕ) (η : ℝ) (hη : η ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    {a z : ℂ} (ha : a = 1 + ℓ + I * η) (hz : z = -2 * I * ρ) :
    HasSum (fun k : ℕ => pochhammer a k / (pochhammer (2 * (ℓ : ℂ) + 2) k * k !) * z ^ (a + k) *
        (log z + Complex.digamma (a + k) - Complex.digamma (1 + k) -
          Complex.digamma (2 * ℓ + 2 + k)))
      ((2 * ℓ + 1)! * Gamma (-(ℓ : ℂ) + I * η) * exp (-(I * coulombTheta ℓ η ρ)) *
          coulombHPlus ℓ η ρ +
        ∑ k ∈ Finset.Icc 1 (2 * ℓ + 1), ((2 * ℓ + 1)! * (k - 1)! : ℂ) /
          ((2 * ℓ + 1 - k)! * pochhammer (1 - a) k) * z ^ (a - k)) := by
  have hzs : z ∈ slitPlane := by
    rw [hz]; refine Or.inr ?_; simp; exact hρ.ne'
  have han : ∀ k : ℕ, a - ((2 * ℓ + 1 : ℕ) : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have := congrArg im hk
    simp [ha] at this
    exact hη this
  have hare : 0 < a.re := by simp [ha]; linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  rw [show -(ℓ : ℂ) + I * η = a - ((2 * ℓ + 1 : ℕ) : ℂ) by rw [ha]; push_cast; ring,
    mul_assoc _ (exp _), exp_neg_mul_coulombHPlus ℓ η ρ ha hz]
  exact hasSum_log_aux ℓ hzs han hare

/-- **The logarithmic series of `H^-_ℓ`** (DLMF 33.6.5, lower signs), `ρ > 0`, with
`a = 1 + ℓ - iη`, `z = 2iρ`, for `η ≠ 0`. -/
@[dlmf 33.6.E5]
theorem hasSum_coulombHMinus_log (ℓ : ℕ) (η : ℝ) (hη : η ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    {a z : ℂ} (ha : a = 1 + ℓ - I * η) (hz : z = 2 * I * ρ) :
    HasSum (fun k : ℕ => pochhammer a k / (pochhammer (2 * (ℓ : ℂ) + 2) k * k !) * z ^ (a + k) *
        (log z + Complex.digamma (a + k) - Complex.digamma (1 + k) -
          Complex.digamma (2 * ℓ + 2 + k)))
      ((2 * ℓ + 1)! * Gamma (-(ℓ : ℂ) - I * η) * exp (I * coulombTheta ℓ η ρ) *
          coulombHMinus ℓ η ρ +
        ∑ k ∈ Finset.Icc 1 (2 * ℓ + 1), ((2 * ℓ + 1)! * (k - 1)! : ℂ) /
          ((2 * ℓ + 1 - k)! * pochhammer (1 - a) k) * z ^ (a - k)) := by
  have hzs : z ∈ slitPlane := by
    rw [hz]; refine Or.inr ?_; simp; exact hρ.ne'
  have han : ∀ k : ℕ, a - ((2 * ℓ + 1 : ℕ) : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have := congrArg im hk
    simp [ha] at this
    exact hη this
  have hare : 0 < a.re := by simp [ha]; linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  rw [show -(ℓ : ℂ) - I * η = a - ((2 * ℓ + 1 : ℕ) : ℂ) by rw [ha]; push_cast; ring,
    mul_assoc _ (exp _), exp_mul_coulombHMinus ℓ η ρ ha hz]
  exact hasSum_log_aux ℓ hzs han hare

/-- **The logarithmic series of `H^+_ℓ`, pole-free form** (DLMF 33.6.5, upper signs), `ρ > 0`,
with `a = 1 + ℓ + iη`, `z = -2iρ`. Each product `ψ(a+k)/Γ(-ℓ+iη)` is written as
`-(-ℓ+iη)_{2ℓ+1+k} (1/Γ)'(a+k)`, and the coefficient `1/(Γ(-ℓ+iη) (1-a)_k)` of the finite sum
as `-(1-a+k)_{2ℓ+1-k}/Γ(a) = -e^{-2iσ_ℓ}/Γ(k-ℓ-iη)`. Stronger than DLMF: valid for all real `η`,
including `η = 0`, where the series vanishes and the formula gives `H^+_ℓ` as a finite sum. -/
@[dlmf 33.6.E5]
theorem hasSum_coulombHPlus_log_recipGamma (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {a z : ℂ} (ha : a = 1 + ℓ + I * η) (hz : z = -2 * I * ρ) :
    HasSum (fun k : ℕ => pochhammer a k / (pochhammer (2 * (ℓ : ℂ) + 2) k * k !) * z ^ (a + k) *
        ((Gamma (-(ℓ : ℂ) + I * η))⁻¹ *
            (log z - Complex.digamma (1 + k) - Complex.digamma (2 * ℓ + 2 + k)) -
          pochhammer (-(ℓ : ℂ) + I * η) (2 * ℓ + 1 + k) * DLMF.Gamma.recipGammaDeriv 1 (a + k)))
      ((2 * ℓ + 1)! * exp (-(I * coulombTheta ℓ η ρ)) * coulombHPlus ℓ η ρ -
        ∑ k ∈ Finset.Icc 1 (2 * ℓ + 1), ((2 * ℓ + 1)! * (k - 1)! : ℂ) *
          pochhammer (1 - a + k) (2 * ℓ + 1 - k) / ((2 * ℓ + 1 - k)! * Gamma a) * z ^ (a - k)) := by
  have hzs : z ∈ slitPlane := by
    rw [hz]; refine Or.inr ?_; simp; exact hρ.ne'
  rw [show -(ℓ : ℂ) + I * η = a - ((2 * ℓ + 1 : ℕ) : ℂ) by rw [ha]; push_cast; ring,
    mul_assoc _ (exp _), exp_neg_mul_coulombHPlus ℓ η ρ ha hz]
  exact hasSum_log_recipGamma_aux ℓ hzs

/-- **The logarithmic series of `H^-_ℓ`, pole-free form** (DLMF 33.6.5, lower signs), `ρ > 0`,
with `a = 1 + ℓ - iη`, `z = 2iρ`; see `hasSum_coulombHPlus_log_recipGamma`. Stronger than
DLMF: valid for all real `η`, including `η = 0`. -/
@[dlmf 33.6.E5]
theorem hasSum_coulombHMinus_log_recipGamma (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {a z : ℂ} (ha : a = 1 + ℓ - I * η) (hz : z = 2 * I * ρ) :
    HasSum (fun k : ℕ => pochhammer a k / (pochhammer (2 * (ℓ : ℂ) + 2) k * k !) * z ^ (a + k) *
        ((Gamma (-(ℓ : ℂ) - I * η))⁻¹ *
            (log z - Complex.digamma (1 + k) - Complex.digamma (2 * ℓ + 2 + k)) -
          pochhammer (-(ℓ : ℂ) - I * η) (2 * ℓ + 1 + k) * DLMF.Gamma.recipGammaDeriv 1 (a + k)))
      ((2 * ℓ + 1)! * exp (I * coulombTheta ℓ η ρ) * coulombHMinus ℓ η ρ -
        ∑ k ∈ Finset.Icc 1 (2 * ℓ + 1), ((2 * ℓ + 1)! * (k - 1)! : ℂ) *
          pochhammer (1 - a + k) (2 * ℓ + 1 - k) / ((2 * ℓ + 1 - k)! * Gamma a) * z ^ (a - k)) := by
  have hzs : z ∈ slitPlane := by
    rw [hz]; refine Or.inr ?_; simp; exact hρ.ne'
  rw [show -(ℓ : ℂ) - I * η = a - ((2 * ℓ + 1 : ℕ) : ℂ) by rw [ha]; push_cast; ring,
    mul_assoc _ (exp _), exp_mul_coulombHMinus ℓ η ρ ha hz]
  exact hasSum_log_recipGamma_aux ℓ hzs

/-! ### §33.9(i) Spherical Bessel functions -/

/-- **The recurrence for `a_k`** (DLMF 33.9.2) at `k = 1`, where `a_{-1} = 0`:
`(2ℓ+2)/(2ℓ+3) a_1 - 2η a_0 = 0`, and the value `a_0 = (2ℓ+1)!! C_ℓ(η)`. -/
@[dlmf 33.9.E2]
theorem besselSeriesCoeffA_initial (ℓ : ℕ) (η : ℝ) :
    besselSeriesCoeffA ℓ η 0 = ((2 * ℓ + 1)‼ : ℝ) * coulombC ℓ η ∧
      (1 : ℝ) * (1 + 2 * ℓ + 1) / (2 * 1 + 2 * ℓ + 1) * besselSeriesCoeffA ℓ η 1 -
        2 * η * besselSeriesCoeffA ℓ η 0 = 0 := by
  refine ⟨rfl, ?_⟩
  simp only [besselSeriesCoeffA]
  have h1 : (2 * (ℓ : ℝ) + 2) ≠ 0 := by positivity
  have h2 : (2 * 1 + 2 * (ℓ : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The recurrence for `a_k`** (DLMF 33.9.2), stated at `k + 2`:
`(k+2)(k+2ℓ+3)/(2k+2ℓ+5) a_{k+2} - 2η a_{k+1} + k(k+2ℓ+1)/(2k+2ℓ+1) a_k = 0`. -/
@[dlmf 33.9.E2]
theorem besselSeriesCoeffA_recurrence (ℓ : ℕ) (η : ℝ) (k : ℕ) :
    ((k : ℝ) + 2) * (k + 2 * ℓ + 3) / (2 * k + 2 * ℓ + 5) * besselSeriesCoeffA ℓ η (k + 2) -
      2 * η * besselSeriesCoeffA ℓ η (k + 1) +
      (k : ℝ) * (k + 2 * ℓ + 1) / (2 * k + 2 * ℓ + 1) * besselSeriesCoeffA ℓ η k = 0 := by
  rw [besselSeriesCoeffA]
  have h1 : ((k : ℝ) + 2) * (k + 2 * ℓ + 3) ≠ 0 := by positivity
  have h2 : (2 * (k : ℝ) + 2 * ℓ + 5) ≠ 0 := by positivity
  have h3 : (2 * (k : ℝ) + 2 * ℓ + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The spherical Bessel expansion of `F_ℓ`** (DLMF 33.9.1):
`F_ℓ(η,ρ) = ρ ∑_{k ≥ 0} a_k j_{ℓ+k}(ρ)`, convergent for all real `η`, `ρ`. -/
@[dlmf 33.9.E1]
theorem hasSum_coulombF_sphericalJ (ℓ : ℕ) (η ρ : ℝ) :
    HasSum (fun k : ℕ => (ρ : ℂ) * besselSeriesCoeffA ℓ η k * DLMF.Bessel.sphericalJ (ℓ + k) ρ)
      (coulombF ℓ η ρ) := by
  sorry

/-! ### §33.9(ii) Bessel functions and modified Bessel functions -/

/-- The initial values `b_{2ℓ} = b_{2ℓ+2} = 0`, `b_{2ℓ+1} = 1` of DLMF 33.9.3–33.9.5. -/
@[dlmf 33.9.E5]
theorem besselSeriesCoeffB_initial (ℓ : ℕ) (η : ℝ) :
    besselSeriesCoeffB ℓ η (2 * ℓ) = 0 ∧ besselSeriesCoeffB ℓ η (2 * ℓ + 1) = 1 ∧
      besselSeriesCoeffB ℓ η (2 * ℓ + 2) = 0 := by
  simp [besselSeriesCoeffB, besselSeriesCoeffBTerm]

/-- **The recurrence for `b_k`** (DLMF 33.9.5): `4η²(k-2ℓ) b_{k+1} + k b_{k-1} + b_{k-2} = 0`
for `k = 2ℓ+2, 2ℓ+3, …`, `η ≠ 0`. -/
@[dlmf 33.9.E5]
theorem besselSeriesCoeffB_recurrence (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) {k : ℕ} (hk : 2 * ℓ + 2 ≤ k) :
    4 * η ^ 2 * ((k : ℝ) - 2 * ℓ) * besselSeriesCoeffB ℓ η (k + 1) +
      k * besselSeriesCoeffB ℓ η (k - 1) + besselSeriesCoeffB ℓ η (k - 2) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = 2 * ℓ + 2 + n := ⟨k - (2 * ℓ + 2), by omega⟩
  rw [besselSeriesCoeffB, besselSeriesCoeffB, besselSeriesCoeffB, ite_eq_left (by omega),
    ite_eq_left (by omega), ite_eq_left (by omega), show 2 * ℓ + 2 + n + 1 - 2 * ℓ = n + 3 by omega,
    show 2 * ℓ + 2 + n - 1 - 2 * ℓ = n + 1 by omega, show 2 * ℓ + 2 + n - 2 - 2 * ℓ = n by omega,
    besselSeriesCoeffBTerm]
  have h : 4 * η ^ 2 * ((n : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The `I`-Bessel expansion of `F_ℓ`** (DLMF 33.9.3), `η > 0`, `ρ > 0`, `t = 2ηρ`:
`F_ℓ(η,ρ) = C_ℓ(η) (2ℓ+1)!/(2η)^{2ℓ+1} ρ^{-ℓ} ∑_{k ≥ 2ℓ+1} b_k t^{k/2} I_k(2√t)`. -/
@[dlmf 33.9.E3]
theorem coulombF_eq_besselI_series (ℓ : ℕ) {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    HasSum (fun k : ℕ => if 2 * ℓ + 1 ≤ k then
        (besselSeriesCoeffB ℓ η k * Real.sqrt (2 * η * ρ) ^ k : ℝ) *
          besselI k (2 * Real.sqrt (2 * η * ρ)) else 0)
      ((coulombF ℓ η ρ : ℂ) /
        ((coulombC ℓ η * (2 * ℓ + 1)! / (2 * η) ^ (2 * ℓ + 1) * (ρ ^ ℓ)⁻¹ : ℝ) : ℂ)) := by
  sorry

/-- **The `J`-Bessel expansion of `F_ℓ`** (DLMF 33.9.4, corrected), `η < 0`, `ρ > 0`,
`t = 2|η|ρ`: `F_ℓ(η,ρ) = C_ℓ(η) (2ℓ+1)!/(2|η|)^{2ℓ+1} ρ^{-ℓ}
∑_{k ≥ 2ℓ+1} (-1)^{k+1} b_k t^{k/2} J_k(2√t)`. DLMF prints the sum without the factor
`(-1)^{k+1}`, which is false (see the module docstring). -/
@[dlmf 33.9.E4]
theorem coulombF_eq_besselJ_series (ℓ : ℕ) {η ρ : ℝ} (hη : η < 0) (hρ : 0 < ρ) :
    HasSum (fun k : ℕ => if 2 * ℓ + 1 ≤ k then
        ((-1) ^ (k + 1) * besselSeriesCoeffB ℓ η k * Real.sqrt (2 * |η| * ρ) ^ k : ℝ) *
          Complex.besselJ k (2 * Real.sqrt (2 * |η| * ρ)) else 0)
      ((coulombF ℓ η ρ : ℂ) /
        ((coulombC ℓ η * (2 * ℓ + 1)! / (2 * |η|) ^ (2 * ℓ + 1) * (ρ ^ ℓ)⁻¹ : ℝ) : ℂ)) := by
  sorry

/-- **The `K`-Bessel asymptotic form of `G_ℓ`** (DLMF 33.9.6–33.9.7): as `η → +∞` with `ρ > 0`
fixed, `G_ℓ(η,ρ) ∼ ρ^{-ℓ}/((ℓ+1/2) λ_ℓ(η) C_ℓ(η)) ∑_{k ≥ 2ℓ+1} (-1)^k b_k t^{k/2} K_k(2√t)`
with `λ_ℓ(η) ∼ ∑_{k ≥ 2ℓ+1} (-1)^k (k-1)! b_k`. Both series are asymptotic in `η`; the
statement takes the same number `N + 1` of terms in each, for every `N`. -/
@[dlmf 33.9.E6, dlmf 33.9.E7]
theorem coulombG_isEquivalent_besselK (ℓ N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (fun η : ℝ => (coulombG ℓ η ρ : ℂ)) ~[atTop]
      (fun η => (((ρ ^ ℓ)⁻¹ / ((ℓ + 1 / 2) *
          (∑ k ∈ Finset.Icc (2 * ℓ + 1) (2 * ℓ + 1 + N),
            (-1) ^ k * ((k - 1)! : ℝ) * besselSeriesCoeffB ℓ η k) * coulombC ℓ η) : ℝ) : ℂ) *
        ∑ k ∈ Finset.Icc (2 * ℓ + 1) (2 * ℓ + 1 + N),
          ((-1) ^ k * besselSeriesCoeffB ℓ η k * Real.sqrt (2 * η * ρ) ^ k : ℝ) *
            besselK k (2 * Real.sqrt (2 * η * ρ))) := by
  sorry

end DLMF.Coulomb
