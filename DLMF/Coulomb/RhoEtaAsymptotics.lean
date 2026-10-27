/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.RhoEtaProperties
public import DLMF.Airy.Basic

/-!
# Coulomb functions: asymptotic expansions (DLMF §§33.11–33.12)

* §33.11, large `ρ`: the expansion 33.11.1 of `H^±_ℓ` is `hasAsymptoticExpansion_coulombHPlus`
  and `hasAsymptoticExpansion_coulombHMinus` in `DLMF.Confluent.CoulombAsymptotics`. Here the
  equivalent amplitude–phase form 33.11.2–33.11.9: the amplitudes `f, g, f̂, ĝ` are
  `largeRhoF`, `largeRhoG`, `largeRhoFHat`, `largeRhoGHat` (defined by 33.11.2–33.11.3), their
  expansions use the terms `largeRhoTerm` (33.11.8–33.11.9), and the expansions 33.11.5–33.11.6
  are stated in Poincaré form: the remainder after the terms `k ≤ K` is `O(ρ^{-K-1})`.
* §33.12, large `η`: the transition-region expansions 33.12.2–33.12.3 (uniform for bounded
  `x = (2η-ρ)/(2η)^{1/3}`; three terms are given, so the remainder is `O(μ^{-4})`), the values
  at the turning point 33.12.6–33.12.7 (remainder `o` of the last printed term), and the scaled
  equation 33.12.8.

**Source corrections.**
* DLMF 33.11.7 prints `g f̂ - f ĝ = 1`. With `f, g, f̂, ĝ` defined by 33.11.2–33.11.3 one has
  `f ĝ - g f̂ = G_ℓ F_ℓ' - G_ℓ' F_ℓ = 1` (the Wronskian 33.2.12); the printed sign is wrong.
  Already the leading terms show it: `f_0 ĝ_0 - g_0 f̂_0 = 1 - η/ρ → 1`. mpmath at `ℓ = 2`,
  `η = 0.7`, `ρ = 30`: `g f̂ - f ĝ = -1.0`. The corrected form is acquired.
* DLMF 33.12.3 prints the factor of `Ai'(x)` (`Bi'(x)`) as `(B_1 + A_1')/μ + ⋯` without the
  leading `1`. Differentiating the leading term of 33.12.2 (`dx/dρ = -(2η)^{-1/3}`) gives
  `F_0' ∼ -π^{1/2}(2η)^{-1/6} Ai'(x)`, so the factor is `1 + (B_1 + A_1')/μ + ⋯`. mpmath at
  `η = 20, 80, 320` and `x ∈ {-1.3, 0, 0.8}` confirms the corrected form with remainder
  `O((2η)^{-1/6} μ^{-4})`.
-/

@[expose] public section

open Complex Filter Set Asymptotics
open scoped Real Topology Nat

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent DLMF.Airy DLMF.Hypergeometric

/-! ### §33.11 Asymptotic expansions for large `ρ` -/

/-- **DLMF 33.11.2**: `F_ℓ = g cos θ_ℓ + f sin θ_ℓ`, `G_ℓ = f cos θ_ℓ - g sin θ_ℓ`. -/
@[dlmf 33.11.E2]
theorem coulombFG_eq_largeRho (ℓ : ℕ) (η ρ : ℝ) :
    coulombF ℓ η ρ = largeRhoG ℓ η ρ * Real.cos (coulombTheta ℓ η ρ) +
        largeRhoF ℓ η ρ * Real.sin (coulombTheta ℓ η ρ) ∧
      coulombG ℓ η ρ = largeRhoF ℓ η ρ * Real.cos (coulombTheta ℓ η ρ) -
        largeRhoG ℓ η ρ * Real.sin (coulombTheta ℓ η ρ) := by
  have h := Real.sin_sq_add_cos_sq (coulombTheta ℓ η ρ)
  simp only [largeRhoF, largeRhoG]
  constructor
  · linear_combination (-coulombF ℓ η ρ) * h
  · linear_combination (-coulombG ℓ η ρ) * h

/-- **DLMF 33.11.3**: `F_ℓ' = ĝ cos θ_ℓ + f̂ sin θ_ℓ`, `G_ℓ' = f̂ cos θ_ℓ - ĝ sin θ_ℓ`. -/
@[dlmf 33.11.E3]
theorem deriv_coulombFG_eq_largeRho (ℓ : ℕ) (η ρ : ℝ) :
    deriv (coulombF ℓ η) ρ = largeRhoGHat ℓ η ρ * Real.cos (coulombTheta ℓ η ρ) +
        largeRhoFHat ℓ η ρ * Real.sin (coulombTheta ℓ η ρ) ∧
      deriv (coulombG ℓ η) ρ = largeRhoFHat ℓ η ρ * Real.cos (coulombTheta ℓ η ρ) -
        largeRhoGHat ℓ η ρ * Real.sin (coulombTheta ℓ η ρ) := by
  have h := Real.sin_sq_add_cos_sq (coulombTheta ℓ η ρ)
  simp only [largeRhoFHat, largeRhoGHat]
  constructor
  · linear_combination (-deriv (coulombF ℓ η) ρ) * h
  · linear_combination (-deriv (coulombG ℓ η) ρ) * h

/-- **DLMF 33.11.4**: `H^±_ℓ = e^{±iθ_ℓ} (f ± i g)`, `ρ > 0`. -/
@[dlmf 33.11.E4]
theorem coulombH_eq_largeRho (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHPlus ℓ η ρ = exp (I * coulombTheta ℓ η ρ) * (largeRhoF ℓ η ρ + I * largeRhoG ℓ η ρ) ∧
      coulombHMinus ℓ η ρ =
        exp (-(I * coulombTheta ℓ η ρ)) * (largeRhoF ℓ η ρ - I * largeRhoG ℓ η ρ) := by
  obtain ⟨hF, hG⟩ := coulombFG_eq_largeRho ℓ η ρ
  obtain ⟨hP, hM⟩ := coulombH_eq_G_add_I_mul_F ℓ η hρ
  set θ := coulombTheta ℓ η ρ
  have hE : exp (I * θ) = Real.cos θ + I * Real.sin θ := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring
  have hE' : exp (-(I * θ)) = Real.cos θ - I * Real.sin θ := by
    rw [show -(I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  rw [hP, hM, hE, hE', hF, hG]
  constructor <;> (push_cast; ring_nf; rw [I_sq]; ring)

/-- The terms `f_k + i g_k` are the terms of the expansion 33.11.1 of `e^{-iθ_ℓ} H^+_ℓ`. -/
lemma q2b_largeRhoTerm_eq (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (k : ℕ) :
    ((largeRhoTerm ℓ η ρ k).1 : ℂ) + I * (largeRhoTerm ℓ η ρ k).2.1 =
      ((ρ : ℂ) ^ k)⁻¹ * (poch (I * η - ℓ) k * poch (I * η + ℓ + 1) k / (k ! * (2 * I) ^ k)) := by
  induction k with
  | zero => simp [largeRhoTerm, poch]
  | succ k ih =>
    have hs : ((largeRhoTerm ℓ η ρ (k + 1)).1 : ℂ) + I * (largeRhoTerm ℓ η ρ (k + 1)).2.1 =
        (((2 * k + 1) * η / ((2 * k + 2) * ρ) : ℝ) +
          I * (((ℓ : ℝ) * (ℓ + 1) - k * (k + 1) + η ^ 2) / ((2 * k + 2) * ρ) : ℝ)) *
        (((largeRhoTerm ℓ η ρ k).1 : ℂ) + I * (largeRhoTerm ℓ η ρ k).2.1) := by
      simp only [largeRhoTerm]
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [hs, ih, poch_succ, poch_succ, Nat.factorial_succ]
    have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
    have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hk2 : (2 * (k : ℂ) + 2) ≠ 0 := by
      rw [show (2 * (k : ℂ) + 2) = 2 * ((k : ℂ) + 1) by ring]; exact mul_ne_zero two_ne_zero hk
    have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring

/-- **The large-`ρ` expansions of `f` and `g`** (DLMF 33.11.5): `f ∼ ∑ f_k`, `g ∼ ∑ g_k` as
`ρ → ∞`, in Poincaré form: the remainder after the terms `k ≤ K` is `O(ρ^{-K-1})`. -/
@[dlmf 33.11.E5]
theorem largeRhoFG_isBigO (ℓ : ℕ) (η : ℝ) (K : ℕ) :
    (fun ρ => largeRhoF ℓ η ρ - ∑ k ∈ Finset.range (K + 1), (largeRhoTerm ℓ η ρ k).1)
        =O[atTop] (fun ρ : ℝ => (ρ ^ (K + 1))⁻¹) ∧
      (fun ρ => largeRhoG ℓ η ρ - ∑ k ∈ Finset.range (K + 1), (largeRhoTerm ℓ η ρ k).2.1)
        =O[atTop] (fun ρ : ℝ => (ρ ^ (K + 1))⁻¹) := by
  set D : ℝ → ℂ := fun ρ => exp (-I * coulombTheta ℓ η ρ) * coulombHPlus ℓ η ρ -
    ∑ k ∈ Finset.range (K + 1), ((ρ : ℂ) ^ k)⁻¹ •
      (poch (I * η - ℓ) k * poch (I * η + ℓ + 1) k / (k ! * (2 * I) ^ k)) with hD
  have h : D =O[atTop] (fun ρ : ℝ => (ρ ^ (K + 1))⁻¹) := by
    rw [← isBigO_norm_right]
    refine ((hasAsymptoticExpansion_coulombHPlus ℓ η (K + 1)).norm_right).congr_right ?_
    intro ρ; simp
  have hDe : ∀ᶠ ρ in atTop, D ρ =
      ((largeRhoF ℓ η ρ - ∑ k ∈ Finset.range (K + 1), (largeRhoTerm ℓ η ρ k).1 : ℝ) : ℂ) +
      I * ((largeRhoG ℓ η ρ - ∑ k ∈ Finset.range (K + 1), (largeRhoTerm ℓ η ρ k).2.1 : ℝ) : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    rw [hD]
    simp only
    rw [(coulombH_eq_largeRho ℓ η hρ).1, ← mul_assoc, ← Complex.exp_add,
      show -I * (coulombTheta ℓ η ρ : ℂ) + I * coulombTheta ℓ η ρ = 0 by ring, Complex.exp_zero,
      one_mul]
    simp only [smul_eq_mul, ← q2b_largeRhoTerm_eq ℓ η hρ.ne']
    push_cast
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  constructor
  · refine IsBigO.trans ?_ h
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hDe] with ρ hρ
    rw [hρ, one_mul]
    refine le_trans ?_ (abs_re_le_norm _)
    simp
  · refine IsBigO.trans ?_ h
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hDe] with ρ hρ
    rw [hρ, one_mul]
    refine le_trans ?_ (abs_im_le_norm _)
    simp

/-- The ray expansion of `z^a U(a,b,z)` along `z = -2iρ`. -/
lemma q2b_expansion_ray (a b : ℂ) :
    HasAsymptoticExpansion atTop (fun (k : ℕ) (ρ : ℝ) => ((ρ : ℂ) ^ k)⁻¹)
      (fun k => poch a k * poch (a - b + 1) k / (k ! * (2 * I) ^ k))
      (fun ρ : ℝ => ((ρ : ℂ) * (-2 * I)) ^ a * kummerU a b ((ρ : ℂ) * (-2 * I))) := by
  have h := hasAsymptoticExpansion_ray_cpow_mul_kummerU a b
    (c := -2 * I) (by simp [I_ne_zero]) (δ := 1 / 2) (α := π / 4) (by norm_num)
    (by rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos]) ?_
  · refine h.congr_coeff (funext fun k => ?_)
    simp only [neg_mul, neg_neg]
  · rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    have hn : ‖(-2 * I : ℂ)‖ = 2 := by simp
    rw [hn]
    simp only [mul_re, mul_im, neg_re, neg_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
      re_ofNat, im_ofNat]
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt] <;> norm_num
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- `f̂_k + iĝ_k = i(f_k + ig_k) - (iη + k)(f_k + ig_k)/ρ`. -/
lemma q2b_largeRhoTermHat_eq (ℓ : ℕ) (η ρ : ℝ) (k : ℕ) :
    ((largeRhoTerm ℓ η ρ k).2.2.1 : ℂ) + I * (largeRhoTerm ℓ η ρ k).2.2.2 =
      I * (((largeRhoTerm ℓ η ρ k).1 : ℂ) + I * (largeRhoTerm ℓ η ρ k).2.1) -
        (I * η + k) * (((largeRhoTerm ℓ η ρ k).1 : ℂ) + I * (largeRhoTerm ℓ η ρ k).2.1) / ρ := by
  induction k with
  | zero => simp [largeRhoTerm]; ring
  | succ k ih =>
    set L : ℂ := (((2 * k + 1) * η / ((2 * k + 2) * ρ) : ℝ) +
          I * (((ℓ : ℝ) * (ℓ + 1) - k * (k + 1) + η ^ 2) / ((2 * k + 2) * ρ) : ℝ))
    have hs : ((largeRhoTerm ℓ η ρ (k + 1)).1 : ℂ) + I * (largeRhoTerm ℓ η ρ (k + 1)).2.1 =
        L * (((largeRhoTerm ℓ η ρ k).1 : ℂ) + I * (largeRhoTerm ℓ η ρ k).2.1) := by
      simp only [largeRhoTerm, L]
      push_cast
      ring_nf
      rw [I_sq]
      ring
    have hs2 : ((largeRhoTerm ℓ η ρ (k + 1)).2.2.1 : ℂ) + I * (largeRhoTerm ℓ η ρ (k + 1)).2.2.2 =
        L * (((largeRhoTerm ℓ η ρ k).2.2.1 : ℂ) + I * (largeRhoTerm ℓ η ρ k).2.2.2) -
          (((largeRhoTerm ℓ η ρ (k + 1)).1 : ℂ) + I * (largeRhoTerm ℓ η ρ (k + 1)).2.1) / ρ := by
      simp only [largeRhoTerm, L]
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [hs2, ih, hs]
    push_cast
    ring

/-- `f̂ + iĝ = i(1 - η/ρ) E₁ + (A/ρ)(E₁ - E₂)` with `E₁ = z^A U(A,B,z)`,
`E₂ = z^{A+1} U(A+1,B+1,z)`, `z = -2iρ`, `A = ℓ+1+iη`, `B = 2ℓ+2`. -/
lemma q2b_hat_eq (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ((largeRhoFHat ℓ η ρ : ℝ) : ℂ) + I * largeRhoGHat ℓ η ρ =
      I * (1 - η / ρ) * (((ρ : ℂ) * (-2 * I)) ^ ((ℓ : ℂ) + 1 + I * η) *
        kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) ((ρ : ℂ) * (-2 * I))) +
      ((ℓ : ℂ) + 1 + I * η) / ρ *
        ((((ρ : ℂ) * (-2 * I)) ^ ((ℓ : ℂ) + 1 + I * η) *
          kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) ((ρ : ℂ) * (-2 * I))) -
         (((ρ : ℂ) * (-2 * I)) ^ ((ℓ : ℂ) + 1 + I * η + 1) *
          kummerU ((ℓ : ℂ) + 1 + I * η + 1) (2 * ℓ + 2 + 1) ((ρ : ℂ) * (-2 * I)))) := by
  set A : ℂ := (ℓ : ℂ) + 1 + I * η
  set B : ℂ := 2 * ℓ + 2
  set z : ℂ := (ρ : ℂ) * (-2 * I) with hz
  have hzs : z ∈ slitPlane := by
    rw [hz, show (ρ : ℂ) * (-2 * I) = -2 * I * ρ by ring]; exact neg_two_I_mul_mem_slitPlane hρ
  have hz0 : z ≠ 0 := slitPlane_ne_zero hzs
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  -- the complex function `W(w) = (w (-2i))^A U(A,B,w (-2i))`
  have hlin : HasDerivAt (fun w : ℂ => w * (-2 * I)) (-2 * I) (ρ : ℂ) := by
    simpa using (hasDerivAt_id (ρ : ℂ)).mul_const (-2 * I)
  have hW : HasDerivAt (fun w : ℂ => (w * (-2 * I)) ^ A * kummerU A B (w * (-2 * I)))
      (A * z ^ (A - 1) * (-2 * I) * kummerU A B z +
        z ^ A * (-A * kummerU (A + 1) (B + 1) z * (-2 * I))) (ρ : ℂ) :=
    have hU : HasDerivAt (kummerU A B) (-A * kummerU (A + 1) (B + 1) z) ((ρ : ℂ) * (-2 * I)) :=
      hasDerivAt_kummerU A B hzs
    have hc : HasDerivAt (fun w : ℂ => kummerU A B (w * (-2 * I)))
        (-A * kummerU (A + 1) (B + 1) z * (-2 * I)) (ρ : ℂ) := by
      have := HasDerivAt.comp (ρ : ℂ) hU hlin
      exact this
    (hlin.cpow_const hzs).mul hc
  -- the phase
  have hθ : HasDerivAt (fun x : ℝ => coulombTheta ℓ η x) (1 - η / ρ) ρ := by
    have h1 : HasDerivAt (fun x : ℝ => Real.log (2 * x)) (1 / ρ) ρ := by
      have := ((hasDerivAt_id ρ).const_mul 2).log (by simp [hρ.ne'])
      convert this using 1
      · rfl
      · simp only [id]; field_simp
    have := (((hasDerivAt_id ρ).sub (h1.const_mul η)).sub_const (ℓ * π / 2)).add_const
      (coulombSigma ℓ η)
    convert this using 1
    · funext x; simp [coulombTheta]
    · field_simp
  have hE : HasDerivAt (fun x : ℝ => exp (I * coulombTheta ℓ η x))
      (exp (I * coulombTheta ℓ η ρ) * (I * ((1 - η / ρ : ℝ) : ℂ))) ρ :=
    (hθ.ofReal_comp.const_mul I).cexp
  have hH := hE.mul hW.comp_ofReal
  have hH' : HasDerivAt (fun x : ℝ => coulombHPlus ℓ η x)
      (exp (I * coulombTheta ℓ η ρ) * (I * ((1 - η / ρ : ℝ) : ℂ)) *
          ((z) ^ A * kummerU A B z) +
        exp (I * coulombTheta ℓ η ρ) * (A * z ^ (A - 1) * (-2 * I) * kummerU A B z +
          z ^ A * (-A * kummerU (A + 1) (B + 1) z * (-2 * I)))) ρ := by
    refine hH.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hρ] with x hx
    simp only [coulombHPlus, A, B, Pi.mul_apply]
    rw [show (-2 * I * (x : ℂ)) = x * (-2 * I) by ring, mul_assoc]
  have hd := (c33a_hasDerivAt_coulombHPlus ℓ η hρ).unique hH'
  set θ := coulombTheta ℓ η ρ
  have hl : ((largeRhoFHat ℓ η ρ : ℝ) : ℂ) + I * largeRhoGHat ℓ η ρ =
      exp (-I * θ) * (((deriv (coulombG ℓ η) ρ : ℝ) : ℂ) + I * (deriv (coulombF ℓ η) ρ : ℝ)) := by
    rw [show -I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
    simp only [largeRhoFHat, largeRhoGHat]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hinv : exp (-I * θ) * exp (I * θ) = 1 := by
    rw [← Complex.exp_add, show -I * (θ : ℂ) + I * θ = 0 by ring, Complex.exp_zero]
  have hsub : z ^ (A - 1) = z ^ A / z := by rw [cpow_sub _ _ hz0, cpow_one]
  have hadd : z ^ (A + 1) = z ^ A * z := by rw [cpow_add _ _ hz0, cpow_one]
  have hzi : z⁻¹ * (-2 * I) = (ρ : ℂ)⁻¹ := by rw [hz]; field_simp
  have hzr : z * (ρ : ℂ)⁻¹ = -2 * I := by rw [hz]; field_simp
  rw [hl, hd, hsub, hadd]
  push_cast
  linear_combination (I * (1 - η / ρ) * (z ^ A * kummerU A B z) +
    A * (z ^ A / z) * (-2 * I) * kummerU A B z +
    z ^ A * (-A * kummerU (A + 1) (B + 1) z * (-2 * I))) * hinv +
    A * z ^ A * kummerU A B z * hzi + A * z ^ A * kummerU (A + 1) (B + 1) z * hzr

/-- **The large-`ρ` expansions of `f̂` and `ĝ`** (DLMF 33.11.6): `f̂ ∼ ∑ f̂_k`, `ĝ ∼ ∑ ĝ_k`
as `ρ → ∞`, in Poincaré form. -/
@[dlmf 33.11.E6]
theorem largeRhoFGHat_isBigO (ℓ : ℕ) (η : ℝ) (K : ℕ) :
    (fun ρ => largeRhoFHat ℓ η ρ - ∑ k ∈ Finset.range (K + 1), (largeRhoTerm ℓ η ρ k).2.2.1)
        =O[atTop] (fun ρ : ℝ => (ρ ^ (K + 1))⁻¹) ∧
      (fun ρ => largeRhoGHat ℓ η ρ - ∑ k ∈ Finset.range (K + 1), (largeRhoTerm ℓ η ρ k).2.2.2)
        =O[atTop] (fun ρ : ℝ => (ρ ^ (K + 1))⁻¹) := by
  set A : ℂ := (ℓ : ℂ) + 1 + I * η with hA
  set B : ℂ := 2 * ℓ + 2 with hB
  set c : ℕ → ℂ := fun k => poch A k * poch (A - B + 1) k / (k ! * (2 * I) ^ k) with hc
  set c' : ℕ → ℂ := fun k => poch (A + 1) k * poch (A + 1 - (B + 1) + 1) k /
    (k ! * (2 * I) ^ k) with hc'
  set E1 : ℝ → ℂ := fun ρ => ((ρ : ℂ) * (-2 * I)) ^ A * kummerU A B ((ρ : ℂ) * (-2 * I))
  set E2 : ℝ → ℂ := fun ρ => ((ρ : ℂ) * (-2 * I)) ^ (A + 1) *
    kummerU (A + 1) (B + 1) ((ρ : ℂ) * (-2 * I))
  set S1 : ℝ → ℂ := fun ρ => ∑ k ∈ Finset.range (K + 1), ((ρ : ℂ) ^ k)⁻¹ • c k
  set S2 : ℝ → ℂ := fun ρ => ∑ k ∈ Finset.range (K + 1), ((ρ : ℂ) ^ k)⁻¹ • c' k
  have hR1 : (fun ρ => E1 ρ - S1 ρ) =O[atTop] (fun ρ : ℝ => ((ρ : ℂ) ^ (K + 1))⁻¹) :=
    q2b_expansion_ray A B (K + 1)
  have hR2 : (fun ρ => E2 ρ - S2 ρ) =O[atTop] (fun ρ : ℝ => ((ρ : ℂ) ^ (K + 1))⁻¹) :=
    q2b_expansion_ray (A + 1) (B + 1) (K + 1)
  have hcc : ∀ k, A * c' k = (A + k) * c k := by
    intro k
    have h1 := poch_succ A k
    have h2 := poch_succ_left A k
    simp only [hc, hc', show A + 1 - (B + 1) + 1 = A - B + 1 by ring]
    rw [mul_div_assoc', ← mul_assoc, ← h2, h1]
    ring
  have hw : ∀ ρ : ℝ, ρ ≠ 0 → ∀ k, ((largeRhoTerm ℓ η ρ k).1 : ℂ) + I * (largeRhoTerm ℓ η ρ k).2.1 =
      ((ρ : ℂ) ^ k)⁻¹ * c k := by
    intro ρ hρ k
    rw [q2b_largeRhoTerm_eq ℓ η hρ k]
    simp only [hc, hA, hB]
    congr 2
    rw [mul_comm]
    congr 2 <;> ring
  set D : ℝ → ℂ := fun ρ => ((largeRhoFHat ℓ η ρ - ∑ k ∈ Finset.range (K + 1),
      (largeRhoTerm ℓ η ρ k).2.2.1 : ℝ) : ℂ) + I * ((largeRhoGHat ℓ η ρ -
      ∑ k ∈ Finset.range (K + 1), (largeRhoTerm ℓ η ρ k).2.2.2 : ℝ) : ℂ) with hD
  have hDe : ∀ᶠ ρ : ℝ in atTop, D ρ =
      (I - I * η / ρ + A / ρ) * (E1 ρ - S1 ρ) - A / ρ * (E2 ρ - S2 ρ) := by
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    have hsum : ∑ k ∈ Finset.range (K + 1), (((largeRhoTerm ℓ η ρ k).2.2.1 : ℂ) +
        I * (largeRhoTerm ℓ η ρ k).2.2.2) = I * (1 - η / ρ) * S1 ρ + A / ρ * (S1 ρ - S2 ρ) := by
      simp only [S1, S2, smul_eq_mul]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [q2b_largeRhoTermHat_eq, hw ρ hρ.ne' k]
      linear_combination (((ρ : ℂ) ^ k)⁻¹ / ρ) * hcc k
    have he := q2b_hat_eq ℓ η hρ
    simp only [hD]
    push_cast
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have : ((largeRhoFHat ℓ η ρ : ℝ) : ℂ) + I * largeRhoGHat ℓ η ρ =
      I * (1 - η / ρ) * E1 ρ + A / ρ * (E1 ρ - E2 ρ) := he
    linear_combination this - hsum
  have hb : (fun ρ : ℝ => I - I * η / ρ + A / ρ) =O[atTop] (fun _ => (1 : ℂ)) := by
    have : Tendsto (fun ρ : ℝ => I - I * η / ρ + A / ρ) atTop (𝓝 (I - I * η * 0 + A * 0)) := by
      have h0 : Tendsto (fun ρ : ℝ => ((ρ : ℂ))⁻¹) atTop (𝓝 0) := by
        have := ((continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ)))
        simpa [Function.comp_def] using this
      simp only [div_eq_mul_inv]
      exact ((tendsto_const_nhds.sub (tendsto_const_nhds.mul h0)).add
        (tendsto_const_nhds.mul h0))
    exact this.isBigO_one ℂ
  have hb2 : (fun ρ : ℝ => A / ρ) =O[atTop] (fun _ => (1 : ℂ)) := by
    have h0 : Tendsto (fun ρ : ℝ => A / ρ) atTop (𝓝 (A * 0)) := by
      simp only [div_eq_mul_inv]
      refine tendsto_const_nhds.mul ?_
      have := ((continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ)))
      simpa [Function.comp_def] using this
    exact h0.isBigO_one ℂ
  have hDc : D =O[atTop] (fun ρ : ℝ => ((ρ : ℂ) ^ (K + 1))⁻¹) := by
    refine IsBigO.congr' ?_ (hDe.mono fun ρ h => h.symm) EventuallyEq.rfl
    refine ((hb.mul hR1).sub (hb2.mul hR2)).congr_right fun ρ => ?_
    simp
  have h : D =O[atTop] (fun ρ : ℝ => (ρ ^ (K + 1))⁻¹) := by
    rw [← isBigO_norm_right]
    refine hDc.norm_right.congr_right ?_
    intro ρ; simp
  constructor
  · refine IsBigO.trans ?_ h
    refine IsBigO.of_bound 1 (Eventually.of_forall fun ρ => ?_)
    rw [one_mul]
    refine le_trans ?_ (abs_re_le_norm _)
    simp [D]
  · refine IsBigO.trans ?_ h
    refine IsBigO.of_bound 1 (Eventually.of_forall fun ρ => ?_)
    rw [one_mul]
    refine le_trans ?_ (abs_im_le_norm _)
    simp [D]

/-- **The amplitude Wronskian** (DLMF 33.11.7, corrected): `f ĝ - f̂ g = 1` for `ρ > 0`.
DLMF prints `g f̂ - f ĝ = 1`, which has the wrong sign (see the module docstring). -/
@[dlmf 33.11.E7]
theorem largeRho_wronskian (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    largeRhoF ℓ η ρ * largeRhoGHat ℓ η ρ - largeRhoG ℓ η ρ * largeRhoFHat ℓ η ρ = 1 := by
  have hW := coulomb_wronskian ℓ η hρ
  have h := Real.sin_sq_add_cos_sq (coulombTheta ℓ η ρ)
  simp only [largeRhoF, largeRhoG, largeRhoFHat, largeRhoGHat]
  linear_combination (coulombG ℓ η ρ * deriv (coulombF ℓ η) ρ -
    deriv (coulombG ℓ η) ρ * coulombF ℓ η ρ) * h + hW

/-- **The recurrence for the terms** (DLMF 33.11.8–33.11.9):
`f_{k+1} = λ_k f_k - μ_k g_k`, `g_{k+1} = λ_k g_k + μ_k f_k`,
`f̂_{k+1} = λ_k f̂_k - μ_k ĝ_k - f_{k+1}/ρ`, `ĝ_{k+1} = λ_k ĝ_k + μ_k f̂_k - g_{k+1}/ρ` with
`λ_k = (2k+1)η/((2k+2)ρ)`, `μ_k = (ℓ(ℓ+1) - k(k+1) + η²)/((2k+2)ρ)`, and
`f_0 = 1`, `g_0 = 0`, `f̂_0 = 0`, `ĝ_0 = 1 - η/ρ`. -/
@[dlmf 33.11.E8, dlmf 33.11.E9]
theorem largeRhoTerm_spec (ℓ : ℕ) (η ρ : ℝ) (k : ℕ) :
    largeRhoTerm ℓ η ρ 0 = (1, 0, 0, 1 - η / ρ) ∧
    let t := largeRhoTerm ℓ η ρ k
    let s := largeRhoTerm ℓ η ρ (k + 1)
    let lam : ℝ := (2 * k + 1) * η / ((2 * k + 2) * ρ)
    let mu : ℝ := ((ℓ : ℝ) * (ℓ + 1) - k * (k + 1) + η ^ 2) / ((2 * k + 2) * ρ)
    s.1 = lam * t.1 - mu * t.2.1 ∧ s.2.1 = lam * t.2.1 + mu * t.1 ∧
      s.2.2.1 = lam * t.2.2.1 - mu * t.2.2.2 - s.1 / ρ ∧
      s.2.2.2 = lam * t.2.2.2 + mu * t.2.2.1 - s.2.1 / ρ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### §33.12 Asymptotic expansions for large `η` -/

/-- **The transition-region expansion of `F_0`, `G_0`** (DLMF 33.12.2): as `η → ∞`, uniformly
for bounded `x = (2η-ρ)/(2η)^{1/3}`,
`F_0 ∼ π^{1/2}(2η)^{1/6} (Ai(x)(1 + B_1/μ + B_2/μ² + ⋯) + Ai'(x)(A_1/μ + A_2/μ² + ⋯))` and the
same with `Bi` for `G_0`, `μ = (2η)^{2/3}`. Stated with the three printed terms and remainder
`O((2η)^{1/6} μ^{-4})`. -/
@[dlmf 33.12.E2]
theorem coulomb_zero_transition (X : ℝ) :
    ∃ K : ℝ, ∀ᶠ η in atTop, ∀ ρ : ℝ, |transitionX η ρ| ≤ X →
      ‖(coulombF 0 η ρ : ℂ) - ((Real.sqrt π * (2 * η) ^ (1 / 6 : ℝ) : ℝ) : ℂ) *
          (airyAi (transitionX η ρ) * (1 + ∑ k ∈ Finset.Icc 1 3,
              transitionB k (transitionX η ρ) / transitionMu η ^ k) +
            airyAiDeriv (transitionX η ρ) * ∑ k ∈ Finset.Icc 1 3,
              transitionA k (transitionX η ρ) / transitionMu η ^ k)‖ ≤
        K * (2 * η) ^ (1 / 6 : ℝ) / transitionMu η ^ 4 ∧
      ‖(coulombG 0 η ρ : ℂ) - ((Real.sqrt π * (2 * η) ^ (1 / 6 : ℝ) : ℝ) : ℂ) *
          (airyBi (transitionX η ρ) * (1 + ∑ k ∈ Finset.Icc 1 3,
              transitionB k (transitionX η ρ) / transitionMu η ^ k) +
            airyBiDeriv (transitionX η ρ) * ∑ k ∈ Finset.Icc 1 3,
              transitionA k (transitionX η ρ) / transitionMu η ^ k)‖ ≤
        K * (2 * η) ^ (1 / 6 : ℝ) / transitionMu η ^ 4 := by
  sorry

/-- **The transition-region expansion of `F_0'`, `G_0'`** (DLMF 33.12.3, corrected): as
`η → ∞`, uniformly for bounded `x`,
`F_0' ∼ -π^{1/2}(2η)^{-1/6} (Ai(x)((B_1'+xA_1)/μ + ⋯) + Ai'(x)(1 + (B_1+A_1')/μ + ⋯))`
(primes on `A_k`, `B_k` are `d/dx`), and the same with `Bi` for `G_0'`; three terms, remainder
`O((2η)^{-1/6} μ^{-4})`. DLMF omits the leading `1` in the factor of `Ai'(x)`. -/
@[dlmf 33.12.E3]
theorem coulomb_zero_deriv_transition (X : ℝ) :
    ∃ K : ℝ, ∀ᶠ η in atTop, ∀ ρ : ℝ, |transitionX η ρ| ≤ X →
      ‖((deriv (coulombF 0 η) ρ : ℝ) : ℂ) + ((Real.sqrt π * (2 * η) ^ (-(1 / 6) : ℝ) : ℝ) : ℂ) *
          (airyAi (transitionX η ρ) * ∑ k ∈ Finset.Icc 1 3,
              (deriv (transitionB k) (transitionX η ρ) +
                transitionX η ρ * transitionA k (transitionX η ρ)) / transitionMu η ^ k +
            airyAiDeriv (transitionX η ρ) * (1 + ∑ k ∈ Finset.Icc 1 3,
              (transitionB k (transitionX η ρ) + deriv (transitionA k) (transitionX η ρ)) /
                transitionMu η ^ k))‖ ≤
        K * (2 * η) ^ (-(1 / 6) : ℝ) / transitionMu η ^ 4 ∧
      ‖((deriv (coulombG 0 η) ρ : ℝ) : ℂ) + ((Real.sqrt π * (2 * η) ^ (-(1 / 6) : ℝ) : ℝ) : ℂ) *
          (airyBi (transitionX η ρ) * ∑ k ∈ Finset.Icc 1 3,
              (deriv (transitionB k) (transitionX η ρ) +
                transitionX η ρ * transitionA k (transitionX η ρ)) / transitionMu η ^ k +
            airyBiDeriv (transitionX η ρ) * (1 + ∑ k ∈ Finset.Icc 1 3,
              (transitionB k (transitionX η ρ) + deriv (transitionA k) (transitionX η ρ)) /
                transitionMu η ^ k))‖ ≤
        K * (2 * η) ^ (-(1 / 6) : ℝ) / transitionMu η ^ 4 := by
  sorry

/-- **`F_0`, `G_0` at the turning point `ρ = 2η`** (DLMF 33.12.6): with `ω = (2η/3)^{1/3}` and
`r = Γ(2/3)/Γ(1/3)`, as `η → ∞`,
`F_0(η,2η), 3^{-1/2} G_0(η,2η) ∼ Γ(1/3) ω^{1/2}/(2√π) (1 ∓ (2/35) r ω^{-4} - (8/2025) ω^{-6}
∓ (5792/4606875) r ω^{-10} - ⋯)`; stated with remainder `o(ω^{1/2-10})`. -/
@[dlmf 33.12.E6]
theorem coulomb_zero_turningPoint :
    (fun η : ℝ => coulombF 0 η (2 * η) -
        Real.Gamma (1 / 3) * ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) / (2 * Real.sqrt π) *
          (1 - 2 / 35 * (Real.Gamma (2 / 3) / Real.Gamma (1 / 3)) /
              ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 4 - 8 / 2025 / ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 6 -
            5792 / 4606875 * (Real.Gamma (2 / 3) / Real.Gamma (1 / 3)) /
              ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 10))
      =o[atTop] (fun η : ℝ => ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ (1 / 2 - 10 : ℝ)) ∧
    (fun η : ℝ => coulombG 0 η (2 * η) / Real.sqrt 3 -
        Real.Gamma (1 / 3) * ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) / (2 * Real.sqrt π) *
          (1 + 2 / 35 * (Real.Gamma (2 / 3) / Real.Gamma (1 / 3)) /
              ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 4 - 8 / 2025 / ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 6 +
            5792 / 4606875 * (Real.Gamma (2 / 3) / Real.Gamma (1 / 3)) /
              ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 10))
      =o[atTop] (fun η : ℝ => ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ (1 / 2 - 10 : ℝ)) := by
  sorry

/-- **`F_0'`, `G_0'` at the turning point `ρ = 2η`** (DLMF 33.12.7): with `ω = (2η/3)^{1/3}`
and `s = Γ(1/3)/Γ(2/3)`, as `η → ∞`,
`F_0'(η,2η), 3^{-1/2} G_0'(η,2η) ∼ Γ(2/3)/(2√π ω^{1/2}) (±1 + (1/15) s ω^{-2} ± (2/14175) ω^{-6}
+ (1436/2338875) s ω^{-8} ± ⋯)`; stated with remainder `o(ω^{-1/2-8})`. -/
@[dlmf 33.12.E7]
theorem coulomb_zero_deriv_turningPoint :
    (fun η : ℝ => deriv (coulombF 0 η) (2 * η) -
        Real.Gamma (2 / 3) / (2 * Real.sqrt π * ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ)) *
          (1 + 1 / 15 * (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)) /
              ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 2 + 2 / 14175 / ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 6 +
            1436 / 2338875 * (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)) /
              ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 8))
      =o[atTop] (fun η : ℝ => ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ (-(1 / 2) - 8 : ℝ)) ∧
    (fun η : ℝ => deriv (coulombG 0 η) (2 * η) / Real.sqrt 3 -
        Real.Gamma (2 / 3) / (2 * Real.sqrt π * ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ)) *
          (-1 + 1 / 15 * (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)) /
              ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 2 - 2 / 14175 / ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 6 +
            1436 / 2338875 * (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)) /
              ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ 8))
      =o[atTop] (fun η : ℝ => ((2 * η / 3) ^ (1 / 3 : ℝ)) ^ (-(1 / 2) - 8 : ℝ)) := by
  sorry

/-- **The scaled Coulomb equation** (DLMF 33.12.8): if `W` solves 33.2.1,
`W'' = -(1 - 2η/ρ - ℓ(ℓ+1)/ρ²) W`, at `ρ = 2ηz`, then `w(z) = W(2ηz)` satisfies
`d²w/dz² = (4η²(1-z)/z + ℓ(ℓ+1)/z²) w` at `z ≠ 0` (`η ≠ 0`). The derivative of `w` is
`2η W'(2ηz)`. -/
@[dlmf 33.12.E8]
theorem coulomb_scaled_equation (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) {W W' : ℝ → ℝ}
    (hW : ∀ x, HasDerivAt W (W' x) x) {z : ℝ} (hz : z ≠ 0)
    (hW'' : HasDerivAt W'
      (-(1 - 2 * η / (2 * η * z) - ℓ * (ℓ + 1) / (2 * η * z) ^ 2) * W (2 * η * z)) (2 * η * z)) :
    (∀ y, HasDerivAt (fun y => W (2 * η * y)) (2 * η * W' (2 * η * y)) y) ∧
      HasDerivAt (fun y => 2 * η * W' (2 * η * y))
        ((4 * η ^ 2 * ((1 - z) / z) + ℓ * (ℓ + 1) / z ^ 2) * W (2 * η * z)) z := by
  have hlin : ∀ y : ℝ, HasDerivAt (fun y : ℝ => 2 * η * y) (2 * η) y := fun y => by
    simpa using (hasDerivAt_id y).const_mul (2 * η)
  refine ⟨fun y => ?_, ?_⟩
  · have := (hW (2 * η * y)).comp y (hlin y)
    rw [show 2 * η * W' (2 * η * y) = W' (2 * η * y) * (2 * η) by ring]
    exact this
  · refine ((hW''.comp z (hlin z)).const_mul (2 * η)).congr_deriv ?_
    field_simp
    ring

end DLMF.Coulomb
