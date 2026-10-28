/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.RhoEtaProperties
public import DLMF.Bessel.Modified
public import DLMF.Bessel.Asymptotics
public import DLMF.Core.Framework
public import DLMF.Gamma.ComplexBinet
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Coulomb functions: limiting forms (DLMF §§33.5, 33.10)

Limiting forms of `F_ℓ(η,ρ)`, `G_ℓ(η,ρ)`, `H^±_ℓ(η,ρ)` and of `C_ℓ(η)`, `σ_ℓ(η)`:

* §33.5(i)–(iv): small `ρ` (33.5.1–33.5.2), `η = 0` (33.5.3–33.5.6), small `|η|` (33.5.7),
  large `ℓ` (33.5.8–33.5.9);
* §33.10(ii)–(iii): `η → ±∞` with `ηρ` fixed (33.10.3–33.10.10). The large-`ρ` limits
  33.10.1–33.10.2 are `tendsto_coulombF_sub_sin_and_coulombG_sub_cos` and
  `tendsto_coulombHPlus_sub_exp` in `DLMF.Confluent.CoulombIrregular`; `H^-` is added here.

`∼` is `Asymptotics.IsEquivalent`. In §33.10 the limit `η → ±∞` with `ηρ = c` fixed is the limit
of the function `η ↦ X(η, c/η)` along `atTop` (`atBot`); derivatives are in `ρ`, evaluated at
`ρ = c/η`. The phase shift in 33.5.7, 33.10.6 and 33.10.10 is DLMF's continuous branch
`phaseShift`; the principal-branch `coulombSigma` does not satisfy 33.10.6 or 33.10.10.
Bessel functions: Mathlib's `Complex.besselJ`, the project's `DLMF.Bessel.besselY`,
`besselI`, `besselK`; the spherical `j_ℓ` is `DLMF.sphericalJ`, and the spherical `y_ℓ` is
written out by DLMF 10.47.3, `y_ℓ(ρ) = (π/(2ρ))^{1/2} Y_{ℓ+1/2}(ρ)`.
-/

@[expose] public section

open Complex Filter Set Asymptotics
open scoped Real Topology Nat

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent DLMF.Bessel

/-! ### §33.5(i) Small `ρ` -/

/-- Kummer's `M(a,b,·)` is continuous. -/
lemma q2b_continuous_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) : Continuous (kummerM a b) :=
  continuous_iff_continuousAt.mpr fun z => (hasDerivAt_kummerM_shift (a := a) hb z).continuousAt

/-- `F_ℓ'(η,x) = Re(C_ℓ(η) · coulombWaveDeriv)`. -/
lemma q2b_deriv_coulombF (ℓ : ℕ) (η x : ℝ) :
    deriv (coulombF ℓ η) x = ((coulombC ℓ η : ℂ) * coulombWaveDeriv ℓ η x).re :=
  (hasDerivAt_re_comp
    (((hasDerivAt_coulombWave ℓ η (x : ℂ)).comp_ofReal).const_mul (coulombC ℓ η : ℂ))).deriv

/-- **DLMF 33.5.1**: `F_ℓ(η,ρ) ∼ C_ℓ(η) ρ^{ℓ+1}` and `F_ℓ'(η,ρ) ∼ (ℓ+1) C_ℓ(η) ρ^ℓ` as
`ρ → 0+`. -/
@[dlmf 33.5.E1]
theorem coulombF_isEquivalent_zero (ℓ : ℕ) (η : ℝ) :
    coulombF ℓ η ~[𝓝[>] 0] (fun ρ => coulombC ℓ η * ρ ^ (ℓ + 1)) ∧
      deriv (coulombF ℓ η) ~[𝓝[>] 0] (fun ρ => (ℓ + 1) * coulombC ℓ η * ρ ^ ℓ) := by
  set a : ℂ := ℓ + 1 - I * η
  set b : ℂ := 2 * ℓ + 2
  have hb : ∀ k : ℕ, b ≠ -k := two_mul_nat_add_two_ne_neg_nat ℓ
  have hC := coulombC_pos ℓ η
  have hM := q2b_continuous_kummerM (a := a) hb
  have hM1 := q2b_continuous_kummerM (a := a + 1) (b := b + 1) (by
    intro k hk; apply hb (k + 1); push_cast; linear_combination hk)
  constructor
  · set g : ℝ → ℂ := fun ρ => exp (-I * ρ) * kummerM a b (2 * I * ρ)
    have hg : Continuous g := by fun_prop
    have hg0 : g 0 = 1 := by simp [g]
    have ht : Tendsto (fun ρ => (g ρ).re) (𝓝[>] 0) (𝓝 1) := by
      have := ((Complex.continuous_re.comp hg).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      have hv : (Complex.re ∘ g) 0 = 1 := by rw [Function.comp_apply, hg0, one_re]
      rw [hv] at this
      exact this
    refine isEquivalent_of_tendsto_one (ht.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρ0 : (0 : ℝ) < ρ := hρ
    have hu : coulombF ℓ η ρ = coulombC ℓ η * ρ ^ (ℓ + 1) * (g ρ).re := by
      have h := ofReal_coulombF ℓ η ρ
      rw [coulombWave] at h
      have h2 := congrArg Complex.re h
      rw [Complex.ofReal_re] at h2
      rw [h2, show (coulombC ℓ η : ℂ) * ((ρ : ℂ) ^ (ℓ + 1) * exp (-I * ρ) *
          kummerM (↑ℓ + 1 - I * ↑η) (2 * ↑ℓ + 2) (2 * I * ↑ρ)) =
          ((coulombC ℓ η * ρ ^ (ℓ + 1) : ℝ) : ℂ) * g ρ by simp [g, a, b]; ring, re_ofReal_mul]
    rw [Pi.div_apply, hu]
    have : coulombC ℓ η * ρ ^ (ℓ + 1) ≠ 0 := by positivity
    field_simp
  · set h : ℝ → ℂ := fun ρ => exp (-I * ρ) * (((ℓ + 1 : ℕ) : ℂ) * kummerM a b (2 * I * ρ) -
        I * ρ * kummerM a b (2 * I * ρ) + 2 * I * (a / b) * ρ * kummerM (a + 1) (b + 1) (2 * I * ρ))
    have hh : Continuous h := by fun_prop
    have hh0 : h 0 = ((ℓ + 1 : ℕ) : ℂ) := by simp [h]
    have hl : ((ℓ : ℝ) + 1) ≠ 0 := by positivity
    have ht : Tendsto (fun ρ => (h ρ).re / (ℓ + 1)) (𝓝[>] 0) (𝓝 1) := by
      have := (((Complex.continuous_re.comp hh).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))).div_const ((ℓ : ℝ) + 1)
      have hv : (Complex.re ∘ h) 0 / ((ℓ : ℝ) + 1) = 1 := by
        rw [Function.comp_apply, hh0, natCast_re]; push_cast; exact div_self hl
      rw [hv] at this
      exact this
    refine isEquivalent_of_tendsto_one (ht.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρ0 : (0 : ℝ) < ρ := hρ
    have hu : deriv (coulombF ℓ η) ρ = coulombC ℓ η * ρ ^ ℓ * (h ρ).re := by
      rw [q2b_deriv_coulombF, show (coulombC ℓ η : ℂ) * coulombWaveDeriv ℓ η ρ =
          ((coulombC ℓ η * ρ ^ ℓ : ℝ) : ℂ) * h ρ by
            simp only [coulombWaveDeriv, h, a, b]; push_cast; ring, re_ofReal_mul]
    rw [Pi.div_apply, hu]
    have : coulombC ℓ η * ρ ^ ℓ ≠ 0 := by positivity
    field_simp

/-- The leading term of `H^+_ℓ` at `ρ → 0+`, from `U(a,b,z) ∼ Γ(b-1)/Γ(a) z^{1-b}`:
it is `e^{iρ} ρ^{-ℓ}/((2ℓ+1) C_ℓ(η))`. -/
lemma q2b_lead_eq (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombAPlus ℓ η * (ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ) *
      (Gamma ((2 * ℓ + 2 : ℂ) - 1) / Gamma ((ℓ : ℂ) + 1 + I * η) *
        (-2 * I * ρ : ℂ) ^ (1 - (2 * ℓ + 2 : ℂ))) =
      exp (I * ρ) * (((ρ ^ ℓ)⁻¹ / ((2 * ℓ + 1) * coulombC ℓ η) : ℝ) : ℂ) := by
  have hz : (-2 * I * ρ : ℂ) ≠ 0 := by simp [hρ.ne', I_ne_zero]
  have hG := c33a_Gamma_ne_zero ℓ η
  have hGn : (‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hG).ne'
  have hpolar := norm_mul_exp_arg_mul_I (Gamma ((ℓ : ℂ) + 1 + I * η))
  rw [show (1 - (2 * ℓ + 2 : ℂ)) = -((2 * ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
    cpow_natCast, show (2 * ℓ + 2 : ℂ) - 1 = ((2 * ℓ : ℕ) : ℂ) + 1 by push_cast; ring,
    Complex.Gamma_nat_eq_factorial, ← hpolar, coulombAPlus, coulombC]
  have hp : (-2 * I * (ρ : ℂ)) ^ (2 * ℓ + 1) =
      (-2 * I) * ((-1) ^ ℓ * (2 ^ ℓ * 2 ^ ℓ)) * ((ρ : ℂ) ^ (ℓ + 1) * (ρ : ℂ) ^ ℓ) := by
    rw [mul_pow, show (ρ : ℂ) ^ (ℓ + 1) * (ρ : ℂ) ^ ℓ = (ρ : ℂ) ^ (2 * ℓ + 1) by
      rw [← pow_add]; congr 1; ring, pow_succ, pow_mul, show (-2 * I : ℂ) ^ 2 = -4 by
      ring_nf; rw [I_sq]; ring, show (-4 : ℂ) = -1 * (2 * 2) by norm_num, mul_pow, mul_pow]
    ring
  rw [hp, coulombSigma]
  have hm : ((-1 : ℂ)) ^ ℓ ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (Real.exp (π * η / 2) : ℂ) * (Real.exp (-π * η / 2) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.exp_add, show π * η / 2 + -π * η / 2 = 0 by ring, Real.exp_zero,
      ofReal_one]
  have hf : ((2 * ℓ + 1)! : ℂ) = (2 * ℓ + 1) * (2 * ℓ)! := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hE : exp ((arg (Gamma ((ℓ : ℂ) + 1 + I * η)) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hl : (2 * (ℓ : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < 2 * ℓ + 1 := by positivity
    exact_mod_cast this.ne'
  have he' : (Real.exp (-π * η / 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  push_cast
  rw [hf]
  field_simp
  have hl2 : (ℓ : ℂ) * 2 + 1 ≠ 0 := by rw [mul_comm]; exact hl
  rw [mul_div_cancel_right₀ _ hl2]
  rw [show ∀ A B C D : ℂ, A * B * C * D = (A * D) * (B * C) from fun _ _ _ _ => by ring,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  ring

/-- `ρ ↦ -2iρ` maps `0+` into the punctured neighbourhood of `0`. -/
lemma q2b_tendsto_neg_two_I :
    Tendsto (fun ρ : ℝ => (-2 * I * ρ : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Continuous (fun ρ : ℝ => (-2 * I * ρ : ℂ)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have : (0 : ℝ) < ρ := hρ
    simp [this.ne', I_ne_zero]

/-- The remainder `U(a,b,z) - Γ(b-1)/Γ(a) z^{1-b}` at `z = -2iρ`, times the prefactor. -/
lemma q2b_rem_isLittleO (ℓ : ℕ) (η : ℝ) :
    (fun ρ : ℝ => coulombAPlus ℓ η * (ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ) *
      (kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ) -
        Gamma ((2 * ℓ + 2 : ℂ) - 1) / Gamma ((ℓ : ℂ) + 1 + I * η) *
          (-2 * I * ρ : ℂ) ^ (1 - (2 * ℓ + 2 : ℂ))))
      =o[𝓝[>] 0] (fun ρ : ℝ => (ρ ^ ℓ)⁻¹) := by
  have hpre : (fun ρ : ℝ => coulombAPlus ℓ η * (ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ))
      =O[𝓝[>] 0] (fun ρ : ℝ => (ρ : ℂ) ^ (ℓ + 1)) := by
    refine IsBigO.of_bound ‖coulombAPlus ℓ η‖ (Eventually.of_forall fun ρ => ?_)
    rw [norm_mul, norm_mul, mul_comm (I : ℂ), norm_exp_ofReal_mul_I, mul_one]
  have hρ0 : (fun ρ : ℝ => ρ) =o[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    exact (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have h := (isBigO_kummerU_at_zero_b_two ((0 : ℕ) + 1 + I * η)).comp_tendsto
      q2b_tendsto_neg_two_I
    have hlog : (fun ρ : ℝ => (ρ : ℂ) * log (-2 * I * ρ : ℂ)) =o[𝓝[>] 0]
        (fun _ : ℝ => (1 : ℝ)) := by
      rw [isLittleO_one_iff]
      have hc : Continuous (fun ρ : ℝ => (((2 * ρ) * Real.log (2 * ρ) / 2 : ℝ) : ℂ) -
          π / 2 * I * ρ) := by
        have : Continuous fun ρ : ℝ => (2 * ρ) * Real.log (2 * ρ) :=
          Real.continuous_mul_log.comp (by fun_prop : Continuous fun ρ : ℝ => 2 * ρ)
        fun_prop
      have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simp only [mul_zero, Real.log_zero, zero_div, ofReal_zero, sub_zero] at ht
      refine ht.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ' : (0 : ℝ) < ρ := hρ
      rw [log_neg_two_I_mul hρ']
      push_cast
      ring
    refine IsBigO.trans_isLittleO (g := fun ρ : ℝ => (ρ : ℂ) ^ (0 + 1) *
        log (-2 * I * ρ : ℂ)) ?_ ?_
    · refine (hpre.mul h).congr' ?_ EventuallyEq.rfl
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < ρ from hρ).ne'
      simp only [Function.comp_apply, Nat.cast_zero, mul_zero, zero_add]
      rw [show (2 : ℂ) - 1 = 1 by norm_num, Complex.Gamma_one, show (1 : ℂ) - 2 = -1 by norm_num,
        cpow_neg_one]
    · simpa using hlog
  · have hb : 2 ≤ (2 * (ℓ : ℂ) + 2).re := by simp
    have hb2 : (2 * (ℓ : ℂ) + 2) ≠ 2 := by
      intro h; have := congrArg Complex.re h; simp at this; omega
    have h := (isBigO_kummerU_at_zero_re_ge_two ((ℓ : ℂ) + 1 + I * η) _ hb hb2).comp_tendsto
      q2b_tendsto_neg_two_I
    have hz : ((fun z : ℂ => z ^ (2 - (2 * (ℓ : ℂ) + 2).re : ℂ)) ∘ fun ρ : ℝ => (-2 * I * ρ : ℂ))
        =O[𝓝[>] 0] (fun ρ : ℝ => ((ρ : ℂ) ^ (2 * ℓ))⁻¹) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ' : (0 : ℝ) < ρ := hρ
      simp only [Function.comp_apply]
      rw [show (2 - (2 * (ℓ : ℂ) + 2).re : ℂ) = -((2 * ℓ : ℕ) : ℂ) by simp, cpow_neg,
        cpow_natCast, norm_inv, norm_inv, norm_pow, norm_pow, one_mul]
      have h1 : ‖(-2 * I * ρ : ℂ)‖ = 2 * ρ := by
        simp [abs_of_pos hρ']
      have h2 : ‖(ρ : ℂ)‖ = ρ := by simp [abs_of_pos hρ']
      rw [h1, h2]
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hρ'.le (by linarith) _
    have hO := hpre.mul (h.trans hz)
    have hC0 : (fun ρ : ℝ => (ρ : ℂ)) =o[𝓝[>] 0] (fun _ : ℝ => (1 : ℂ)) := by
      rw [isLittleO_one_iff]
      exact ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds).trans
        (by simp)
    have hw : (fun ρ : ℝ => ((ρ : ℂ) ^ ℓ)⁻¹) =O[𝓝[>] 0] (fun ρ : ℝ => (ρ ^ ℓ)⁻¹) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun ρ => by simp)
    have hl0 := hC0.mul_isBigO (isBigO_refl (fun ρ : ℝ => ((ρ : ℂ) ^ ℓ)⁻¹) (𝓝[>] (0 : ℝ)))
    simp only [one_mul] at hl0
    have hl := hl0.trans_isBigO hw
    refine (hO.trans_isLittleO ?_)
    refine IsBigO.trans_isLittleO ?_ hl
    refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < ρ from hρ).ne'
    rw [one_mul]
    apply le_of_eq
    congr 1
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    field_simp
    ring

/-- `ρ^{-m} = o(ρ^{-(m+j)})` as `ρ → 0+`, `j ≥ 1`. -/
lemma q2b_inv_pow_isLittleO (m j : ℕ) (hj : 1 ≤ j) :
    (fun ρ : ℝ => (ρ ^ m)⁻¹) =o[𝓝[>] 0] (fun ρ : ℝ => (ρ ^ (m + j))⁻¹) := by
  have h1 : (fun ρ : ℝ => ρ ^ j) =o[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    have := ((continuous_pow j).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [zero_pow (by omega : j ≠ 0)] using this
  have := h1.mul_isBigO (isBigO_refl (fun ρ : ℝ => (ρ ^ (m + j))⁻¹) (𝓝[>] (0 : ℝ)))
  simp only [one_mul] at this
  refine this.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have : ρ ≠ 0 := (show (0 : ℝ) < ρ from hρ).ne'
  rw [pow_add]; field_simp

/-- DLMF 33.5.2 for `G_ℓ` itself. -/
lemma q2b_coulombG_isEquivalent_zero (ℓ : ℕ) (η : ℝ) :
    coulombG ℓ η ~[𝓝[>] 0] (fun ρ => (ρ ^ ℓ)⁻¹ / ((2 * ℓ + 1) * coulombC ℓ η)) := by
  set v : ℝ → ℝ := fun ρ => (ρ ^ ℓ)⁻¹ / ((2 * ℓ + 1) * coulombC ℓ η) with hv
  have hC := coulombC_pos ℓ η
  have hk : 0 < (2 * (ℓ : ℝ) + 1) * coulombC ℓ η := by positivity
  have hvO : (fun ρ : ℝ => (ρ ^ ℓ)⁻¹) =O[𝓝[>] 0] v := by
    refine IsBigO.of_bound ((2 * ℓ + 1) * coulombC ℓ η) (Eventually.of_forall fun ρ => ?_)
    simp only [hv, norm_div, Real.norm_eq_abs, abs_of_pos hk]
    rw [mul_div_cancel₀ _ hk.ne']
  have hrem := ((q2b_rem_isLittleO ℓ η).trans_isBigO hvO)
  set r : ℝ → ℂ := fun ρ => coulombAPlus ℓ η * (ρ : ℂ) ^ (ℓ + 1) * exp (I * ρ) *
      (kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ) -
        Gamma ((2 * ℓ + 2 : ℂ) - 1) / Gamma ((ℓ : ℂ) + 1 + I * η) *
          (-2 * I * ρ : ℂ) ^ (1 - (2 * ℓ + 2 : ℂ))) with hr
  have h1 : (fun ρ => (r ρ).re) =o[𝓝[>] 0] v :=
    (IsBigO.of_bound 1 (Eventually.of_forall fun ρ => by
      rw [one_mul, Real.norm_eq_abs]; exact abs_re_le_norm _)).trans_isLittleO hrem
  have hcos : (fun ρ : ℝ => Real.cos ρ - 1) =o[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    have hc : Continuous (fun ρ : ℝ => Real.cos ρ - 1) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [Real.cos_zero, sub_self] at this
    exact this
  have h2 := hcos.mul_isBigO (isBigO_refl v (𝓝[>] (0 : ℝ)))
  simp only [one_mul] at h2
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have hρ' : (0 : ℝ) < ρ := hρ
  have hH := coulombHPlus_eq ℓ η hρ'
  have hL := q2b_lead_eq ℓ η hρ'
  have : coulombHPlus ℓ η ρ = r ρ + exp (I * ρ) * (v ρ : ℂ) := by
    rw [hH, hr, hv]; simp only; rw [← hL]; ring
  simp only [Pi.sub_apply]
  rw [coulombG, this, add_re, mul_comm (exp _), re_ofReal_mul, mul_comm I, exp_ofReal_mul_I_re]
  ring

/-- **DLMF 33.5.2**: `G_ℓ(η,ρ) ∼ ρ^{-ℓ}/((2ℓ+1) C_ℓ(η))` (`ℓ ≥ 0`) and
`G_ℓ'(η,ρ) ∼ -ℓ ρ^{-ℓ-1}/((2ℓ+1) C_ℓ(η))` (`ℓ ≥ 1`) as `ρ → 0+`. -/
@[dlmf 33.5.E2]
theorem coulombG_isEquivalent_zero (ℓ : ℕ) (η : ℝ) :
    coulombG ℓ η ~[𝓝[>] 0] (fun ρ => (ρ ^ ℓ)⁻¹ / ((2 * ℓ + 1) * coulombC ℓ η)) ∧
      (1 ≤ ℓ → deriv (coulombG ℓ η) ~[𝓝[>] 0]
        (fun ρ => -(ℓ * (ρ ^ (ℓ + 1))⁻¹) / ((2 * ℓ + 1) * coulombC ℓ η))) := by
  refine ⟨q2b_coulombG_isEquivalent_zero ℓ η, fun hℓ => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hGl := q2b_coulombG_isEquivalent_zero (m + 1) η
  have hGm := q2b_coulombG_isEquivalent_zero m η
  have hl : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  -- `S_ℓ ∼ ℓ/ρ`
  have hS : (fun ρ => recurrenceS (m + 1) η ρ) ~[𝓝[>] 0]
      (fun ρ : ℝ => ((m + 1 : ℕ) : ℝ) / ρ) := by
    have h0 : (fun _ : ℝ => η / ((m + 1 : ℕ) : ℝ)) =o[𝓝[>] 0]
        (fun ρ : ℝ => ((m + 1 : ℕ) : ℝ) / ρ) := by
      have := (q2b_inv_pow_isLittleO 0 1 le_rfl).const_mul_left (η / ((m + 1 : ℕ) : ℝ))
      refine (this.const_mul_right' (c := ((m + 1 : ℕ) : ℝ)) (isUnit_iff_ne_zero.mpr hl.ne')
        ).congr' (Eventually.of_forall fun ρ => by simp) (Eventually.of_forall fun ρ => ?_)
      simp [div_eq_mul_inv]
    refine (IsEquivalent.refl.add_isLittleO h0).congr_left ?_
    filter_upwards with ρ
    simp [recurrenceS]
  have hprod := (hS.mul hGl).neg
  have hw : (fun ρ : ℝ => recurrenceR (m + 1) η * coulombG m η ρ) =o[𝓝[>] 0]
      (fun ρ => -(((m + 1 : ℕ) : ℝ) * (ρ ^ (m + 1 + 1))⁻¹) /
        ((2 * ((m + 1 : ℕ) : ℝ) + 1) * coulombC (m + 1) η)) := by
    have hC := coulombC_pos (m + 1) η
    have hc : -(((m + 1 : ℕ) : ℝ)) / ((2 * ((m + 1 : ℕ) : ℝ) + 1) * coulombC (m + 1) η) ≠ 0 := by
      apply div_ne_zero (by linarith) (by positivity)
    refine (hGm.isBigO.const_mul_left (recurrenceR (m + 1) η)).trans_isLittleO ?_
    have h1 : (fun ρ : ℝ => (ρ ^ m)⁻¹ / ((2 * m + 1) * coulombC m η)) =o[𝓝[>] 0]
        (fun ρ : ℝ => (ρ ^ (m + 2))⁻¹) :=
      (q2b_inv_pow_isLittleO m 2 (by norm_num)).const_mul_left
        ((2 * m + 1) * coulombC m η)⁻¹ |>.congr_left (fun ρ => by ring)
    refine (h1.const_mul_right' (c := -(((m + 1 : ℕ) : ℝ)) /
      ((2 * ((m + 1 : ℕ) : ℝ) + 1) * coulombC (m + 1) η)) (isUnit_iff_ne_zero.mpr hc)).congr'
      EventuallyEq.rfl (Eventually.of_forall fun ρ => ?_)
    simp only
    ring
  have hprod' := hprod.congr_right (w := fun ρ => -(((m + 1 : ℕ) : ℝ) * (ρ ^ (m + 1 + 1))⁻¹) /
        ((2 * ((m + 1 : ℕ) : ℝ) + 1) * coulombC (m + 1) η)) (by
    filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ρ hρ
    have hρ' : ρ ≠ 0 := (show (0 : ℝ) < ρ from hρ).ne'
    have hC := coulombC_pos (m + 1) η
    have hk : (2 * ((m + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    show -((((m + 1 : ℕ) : ℝ)) / ρ * ((ρ ^ (m + 1))⁻¹ /
      ((2 * ((m + 1 : ℕ) : ℝ) + 1) * coulombC (m + 1) η))) = _
    field_simp
    ring)
  refine (hprod'.add_isLittleO hw).congr_left ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  rw [deriv_coulombG_lower m η (show (0 : ℝ) < ρ from hρ)]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

/-! ### §33.5(ii) `η = 0` -/

/-- **DLMF 33.5.6**: `C_ℓ(0) = 2^ℓ ℓ!/(2ℓ+1)! = 1/(2ℓ+1)!!`. -/
@[dlmf 33.5.E6]
theorem coulombC_zero (ℓ : ℕ) :
    coulombC ℓ 0 = 2 ^ ℓ * ℓ ! / (2 * ℓ + 1)! ∧ coulombC ℓ 0 = 1 / ((2 * ℓ + 1)‼ : ℝ) := by
  have h1 : coulombC ℓ 0 = 2 ^ ℓ * ℓ ! / (2 * ℓ + 1)! := by
    rw [coulombC]
    simp only [mul_zero, zero_div, Real.exp_zero, mul_one, Complex.ofReal_zero,
      add_zero]
    rw [show ((ℓ : ℂ) + 1) = ((ℓ : ℕ) : ℂ) + 1 from rfl, Complex.Gamma_nat_eq_factorial,
      Complex.norm_natCast]
  refine ⟨h1, ?_⟩
  rw [h1, Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  have h0 : ((2 * ℓ + 1)‼ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have h2 : (ℓ ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp

/-- **DLMF 33.5.3, regular function**: `F_ℓ(0,ρ) = ρ j_ℓ(ρ)`. -/
@[dlmf 33.5.E3]
theorem coulombF_zero_eq_sphericalJ (ℓ : ℕ) (ρ : ℝ) :
    (coulombF ℓ 0 ρ : ℂ) = ρ * DLMF.sphericalJ ℓ ρ := by
  set ν : ℂ := (ℓ : ℂ) + 1 / 2
  have hν : ∀ k : ℕ, ν + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp [ν] at this
    linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp [ν] at this
    linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hK := kummerM_eq_exp_mul_regularized0F1 hν h2ν (2 * I * ρ)
  rw [show ν + 1 / 2 = (ℓ : ℂ) + 1 - I * ((0 : ℝ) : ℂ) by simp [ν]; ring,
    show 2 * ν + 1 = 2 * (ℓ : ℂ) + 2 by simp [ν]; ring,
    show (2 * I * (ρ : ℂ)) ^ 2 / 16 = -(ρ : ℂ) ^ 2 / 4 by ring_nf; rw [I_sq]; ring,
    show ν + 1 = (ℓ : ℂ) + 3 / 2 by simp [ν]; ring] at hK
  have hG : Gamma ((ℓ : ℂ) + 3 / 2) = (((2 * (ℓ + 1) - 1 : ℕ)‼ : ℝ) * √π / 2 ^ (ℓ + 1) : ℝ) := by
    rw [← Real.Gamma_nat_add_half, ← Complex.Gamma_ofReal]; congr 1; push_cast; ring
  rw [ofReal_coulombF, coulombWave, hK, (coulombC_zero ℓ).2, DLMF.sphericalJ, hG,
    show 2 * (ℓ + 1) - 1 = 2 * ℓ + 1 by omega]
  have he : exp (-I * ρ) * exp (2 * I * ρ / 2) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  have hd : (((2 * ℓ + 1)‼ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  generalize regularizedHGFun ∅ {(ℓ : ℂ) + 3 / 2} (-(ρ : ℂ) ^ 2 / 4) = R
  generalize exp (-I * ρ) = E1 at he ⊢
  generalize exp (2 * I * ρ / 2) = E2 at he ⊢
  push_cast
  field_simp
  linear_combination ((ρ : ℂ) ^ (ℓ + 1) * R) * he

/-- `θ_ℓ(0,ρ) = ρ - ℓπ/2`. -/
lemma q2b_coulombTheta_zero (ℓ : ℕ) (ρ : ℝ) : coulombTheta ℓ 0 ρ = ρ - ℓ * π / 2 := by
  have : coulombSigma ℓ 0 = 0 := by
    rw [coulombSigma]
    simp only [ofReal_zero, mul_zero, add_zero]
    rw [show (ℓ : ℂ) + 1 = ((ℓ : ℕ) : ℂ) + 1 from rfl, Complex.Gamma_nat_eq_factorial]
    rw [← ofReal_natCast, arg_ofReal_of_nonneg (by positivity)]
  rw [coulombTheta, this]; ring

/-- `√(2ρ) π/(2√π) = √(πρ/2)`. -/
lemma q2b_sqrt_identity {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt (2 * ρ) * π / (2 * Real.sqrt π) = Real.sqrt (π * ρ / 2) := by
  have hπ := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : Real.sqrt (π * ρ / 2) * Real.sqrt 2 = Real.sqrt π * Real.sqrt ρ := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul Real.pi_pos.le]; congr 1; ring
  have h3 : Real.sqrt (2 * ρ) = Real.sqrt 2 * Real.sqrt ρ := Real.sqrt_mul (by norm_num) _
  have h4 := Real.sq_sqrt Real.pi_pos.le
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h6 : 0 < Real.sqrt 2 := by positivity
  rw [h3]
  field_simp
  apply mul_left_cancel₀ h6.ne'
  linear_combination Real.sqrt ρ * π * h5 - 2 * Real.sqrt ρ * h4 - 2 * Real.sqrt π * h2

/-- `H^+_ℓ(0,ρ) = (πρ/2)^{1/2} (i J_{ℓ+1/2}(ρ) - Y_{ℓ+1/2}(ρ))`, `ρ > 0`, via DLMF 13.6.10
and 10.27.8. -/
lemma q2b_coulombHPlus_zero (ℓ : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHPlus ℓ 0 ρ = Real.sqrt (π * ρ / 2) *
      (I * Complex.besselJ (ℓ + 1 / 2) ρ - besselY (ℓ + 1 / 2) ρ) := by
  set ν : ℂ := (ℓ : ℂ) + 1 / 2
  have hz : (-I * ρ : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simp [hρ.ne']
  have hU := kummerU_besselK ν (-I * ρ) hz
  have hH := hankelH1_eq_besselK ν (z := (ρ : ℂ)) (by simp [hρ]) (by
    rw [arg_ofReal_of_nonneg hρ.le]; linarith [Real.pi_pos])
  have hw : (-2 * I * ρ : ℂ) ≠ 0 := by simp [hρ.ne', I_ne_zero]
  rw [coulombHPlus, q2b_coulombTheta_zero]
  simp only [ofReal_zero, mul_zero, add_zero]
  rw [show (ℓ : ℂ) + 1 = ν + 1 / 2 by simp [ν]; ring, show 2 * (ℓ : ℂ) + 2 = 2 * ν + 1 by
    simp [ν]; ring, show (-2 * I * ρ : ℂ) = 2 * (-I * ρ) by ring, hU]
  have hw2 : (2 * (-I * ρ) : ℂ) ≠ 0 := by
    rw [← show (-2 * I * ρ : ℂ) = 2 * (-I * ρ) by ring]; exact hw
  have hpow : (2 * (-I * ρ) : ℂ) ^ (ν + 1 / 2) * (2 * (-I * ρ) : ℂ) ^ (-ν) =
      (Real.sqrt (2 * ρ) : ℂ) * exp (-(π / 4) * I) := by
    rw [← cpow_add _ _ hw2, show ν + 1 / 2 + -ν = (1 / 2 : ℂ) by ring,
      show (2 * (-I * ρ) : ℂ) = ((2 * ρ : ℝ) : ℂ) * (-I) by push_cast; ring,
      ofReal_mul_cpow' (by positivity) (neg_ne_zero.mpr I_ne_zero),
      cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), log_neg_I,
      Real.sqrt_eq_rpow, ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have hK : besselK ν (-I * ρ) = π * I / 2 * exp (I * ν * π / 2) *
      (Complex.besselJ ν ρ + I * besselY ν ρ) := by
    rw [← hankelH1, hH]
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have he : exp (I * ν * π / 2) * exp (-(I * ν * π / 2)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    field_simp
    simp only [show -(I * (ρ : ℂ)) = -I * ρ by ring]
    have he2 : exp (I * π * ν / 2) * exp (-(I * π * ν / 2)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    linear_combination (-(besselK ν (-I * ρ))) * he2
  have hE : exp (I * ((ρ - ℓ * π / 2 : ℝ) : ℂ)) * exp (-(π / 4) * I) * exp (-I * ρ) *
      exp (I * ν * π / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    simp only [ν]; push_cast; ring_nf; exact Complex.exp_zero
  have hS : ((Real.sqrt (2 * ρ) : ℝ) : ℂ) * π / (2 * (Real.sqrt π : ℂ)) =
      (Real.sqrt (π * ρ / 2) : ℂ) := by
    rw [← q2b_sqrt_identity hρ]; push_cast; ring
  have hsπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc exp (I * ((ρ - ℓ * π / 2 : ℝ) : ℂ)) * (2 * (-I * ρ) : ℂ) ^ (ν + 1 / 2) *
        (1 / (Real.sqrt π : ℂ) * exp (-I * ρ) * (2 * (-I * ρ) : ℂ) ^ (-ν) * besselK ν (-I * ρ))
      = exp (I * ((ρ - ℓ * π / 2 : ℝ) : ℂ)) * ((2 * (-I * ρ) : ℂ) ^ (ν + 1 / 2) *
          (2 * (-I * ρ) : ℂ) ^ (-ν)) * (1 / (Real.sqrt π : ℂ) * exp (-I * ρ) *
            besselK ν (-I * ρ)) := by ring
    _ = (exp (I * ((ρ - ℓ * π / 2 : ℝ) : ℂ)) * exp (-(π / 4) * I) * exp (-I * ρ) *
          exp (I * ν * π / 2)) * (((Real.sqrt (2 * ρ) : ℝ) : ℂ) * π / (2 * (Real.sqrt π : ℂ))) *
          (I * (Complex.besselJ ν ρ + I * besselY ν ρ)) := by
        rw [hpow, hK]; field_simp
    _ = _ := by
        rw [hE, hS, one_mul]
        ring_nf; rw [I_sq]; ring

/-- `F_ℓ(0,ρ) = (πρ/2)^{1/2} J_{ℓ+1/2}(ρ)`, `ρ > 0`. -/
lemma q2b_coulombF_zero_bessel (ℓ : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (coulombF ℓ 0 ρ : ℂ) = Real.sqrt (π * ρ / 2) * Complex.besselJ (ℓ + 1 / 2) ρ := by
  rw [coulombF_zero_eq_sphericalJ, DLMF.sphericalJ, DLMF.Bessel.besselJ_eq_regularized]
  have hρ2 : (0 : ℝ) < ρ / 2 := by positivity
  have hc : ((ρ : ℂ) / 2) ^ ((ℓ : ℂ) + 1 / 2) =
      ((ρ : ℂ) / 2) ^ ℓ * (Real.sqrt (ρ / 2) : ℂ) := by
    rw [cpow_add _ _ (by simp [hρ.ne']), cpow_natCast, Real.sqrt_eq_rpow,
      ofReal_cpow hρ2.le]
    push_cast; ring_nf
  rw [hc, show (ℓ : ℂ) + 1 / 2 + 1 = (ℓ : ℂ) + 3 / 2 by ring,
    show -((ρ : ℂ) ^ 2 / 4) = -(ρ : ℂ) ^ 2 / 4 by ring]
  have h1 : Real.sqrt (π * ρ / 2) * Real.sqrt (ρ / 2) = Real.sqrt π * (ρ / 2) := by
    rw [← Real.sqrt_mul (by positivity), show π * ρ / 2 * (ρ / 2) = π * (ρ / 2) ^ 2 by ring,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hρ2.le]
  have h1' : (Real.sqrt (π * ρ / 2) : ℂ) * (Real.sqrt (ρ / 2) : ℂ) =
      (Real.sqrt π : ℂ) * ((ρ : ℂ) / 2) := by exact_mod_cast h1
  generalize regularizedHGFun ∅ {(ℓ : ℂ) + 3 / 2} (-(ρ : ℂ) ^ 2 / 4) = R
  rw [show ∀ A B C D : ℂ, A * (B * C * D) = (A * C) * (B * D) from fun _ _ _ _ => by ring, h1',
    div_pow]
  field_simp
  ring

/-- **DLMF 33.5.3, irregular function**: `G_ℓ(0,ρ) = -ρ y_ℓ(ρ)` with
`y_ℓ(ρ) = (π/(2ρ))^{1/2} Y_{ℓ+1/2}(ρ)` (DLMF 10.47.3), `ρ > 0`. -/
@[dlmf 33.5.E3]
theorem coulombG_zero_eq_sphericalY (ℓ : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (coulombG ℓ 0 ρ : ℂ) = -(ρ * (Real.sqrt (π / (2 * ρ)) * besselY (ℓ + 1 / 2) ρ)) := by
  have h := (coulombH_eq_G_add_I_mul_F ℓ 0 hρ).1
  rw [q2b_coulombHPlus_zero ℓ hρ, q2b_coulombF_zero_bessel ℓ hρ] at h
  have hs : ρ * Real.sqrt (π / (2 * ρ)) = Real.sqrt (π * ρ / 2) := by
    rw [show Real.sqrt (π * ρ / 2) = Real.sqrt (ρ ^ 2 * (π / (2 * ρ))) by
      congr 1; field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hρ.le]
  have hs' : (ρ : ℂ) * (Real.sqrt (π / (2 * ρ)) : ℂ) = (Real.sqrt (π * ρ / 2) : ℂ) := by
    exact_mod_cast hs
  linear_combination -h + besselY (ℓ + 1 / 2) ρ * hs'

/-- **DLMF 33.5.4**: `F_ℓ(0,ρ) = (πρ/2)^{1/2} J_{ℓ+1/2}(ρ)` and
`G_ℓ(0,ρ) = -(πρ/2)^{1/2} Y_{ℓ+1/2}(ρ)`, `ρ > 0`. -/
@[dlmf 33.5.E4]
theorem coulombFG_zero_eq_bessel (ℓ : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (coulombF ℓ 0 ρ : ℂ) = Real.sqrt (π * ρ / 2) * Complex.besselJ (ℓ + 1 / 2) ρ ∧
      (coulombG ℓ 0 ρ : ℂ) = -(Real.sqrt (π * ρ / 2) * besselY (ℓ + 1 / 2) ρ) := by
  refine ⟨q2b_coulombF_zero_bessel ℓ hρ, ?_⟩
  have h := (coulombH_eq_G_add_I_mul_F ℓ 0 hρ).1
  rw [q2b_coulombHPlus_zero ℓ hρ, q2b_coulombF_zero_bessel ℓ hρ] at h
  linear_combination -h

/-- **DLMF 33.5.5**: `F_0(0,ρ) = sin ρ`, `G_0(0,ρ) = cos ρ`, `H^±_0(0,ρ) = e^{±iρ}`
(`ρ > 0` for `G` and `H^±`). -/
@[dlmf 33.5.E5]
theorem coulomb_zero_zero (ρ : ℝ) :
    coulombF 0 0 ρ = Real.sin ρ ∧ (0 < ρ → coulombG 0 0 ρ = Real.cos ρ ∧
      coulombHPlus 0 0 ρ = exp (I * ρ) ∧ coulombHMinus 0 0 ρ = exp (-(I * ρ))) := by
  have hC : coulombC 0 0 = 1 := by
    rw [(coulombC_zero 0).2]; simp
  have hF : coulombF 0 0 ρ = Real.sin ρ := by
    rcases eq_or_ne ρ 0 with rfl | hρ
    · simp [coulombF, coulombWave]
    have hρ' : (I * ρ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hρ)
    have h := ofReal_coulombF 0 0 ρ
    rw [hC, coulombWave] at h
    simp only [Nat.cast_zero, zero_add, Complex.ofReal_zero, mul_zero, sub_zero,
      pow_one, Complex.ofReal_one, one_mul] at h
    rw [show (2 : ℂ) * I * ρ = 2 * (I * ρ) by ring, kummerM_one_two _ hρ',
      mul_comm I (ρ : ℂ), Complex.sinh_mul_I, ← Complex.ofReal_sin] at h
    have he : exp (-I * ρ) * exp (ρ * I) = 1 := by
      rw [← Complex.exp_add, show -I * (ρ : ℂ) + ρ * I = 0 by ring, Complex.exp_zero]
    have hρ'' : (ρ : ℂ) * I ≠ 0 := by rwa [mul_comm]
    have : (coulombF 0 0 ρ : ℂ) = Real.sin ρ := by
      calc (coulombF 0 0 ρ : ℂ)
          = (exp (-I * ρ) * exp (ρ * I)) * ((Real.sin ρ : ℂ) * (ρ * I)) / (ρ * I) := by
            rw [h]; ring
        _ = Real.sin ρ := by rw [he, one_mul, mul_div_cancel_right₀ _ hρ'']
    exact_mod_cast this
  refine ⟨hF, fun hρ => ?_⟩
  have hz : (-2 * I * ρ : ℂ) ∈ slitPlane := neg_two_I_mul_mem_slitPlane hρ
  have hz0 := slitPlane_ne_zero hz
  have hθ : coulombTheta 0 0 ρ = ρ := by
    simp [coulombTheta, coulombSigma]
  have hP : coulombHPlus 0 0 ρ = exp (I * ρ) := by
    rw [coulombHPlus, hθ]
    simp only [Nat.cast_zero, zero_add, Complex.ofReal_zero, mul_zero, add_zero, cpow_one]
    have hU := kummerU_shift_one 1 hz
    rw [show (1 : ℂ) + 1 = 2 by norm_num, cpow_neg_one] at hU
    rw [hU, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
  have hM : coulombHMinus 0 0 ρ = exp (-(I * ρ)) := by
    rw [coulombHMinus_eq_conj 0 0 hρ, hP, ← Complex.exp_conj]
    simp
  refine ⟨?_, hP, hM⟩
  rw [coulombG, hP, mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
  ring

/-! ### §33.5(iii) Small `|η|` -/

/-- `0 ≤ x - arctan x ≤ x³/3` for `x ≥ 0`. -/
lemma q2b_arctan_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x - Real.arctan x ∧ x - Real.arctan x ≤ x ^ 3 / 3 := by
  have hg : Monotone (fun x : ℝ => x - Real.arctan x) := by
    refine monotone_of_deriv_nonneg ((differentiable_id).sub Real.differentiable_arctan) ?_
    intro t
    have : HasDerivAt (fun x : ℝ => x - Real.arctan x) (1 - 1 / (1 + t ^ 2)) t :=
      (hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)
    rw [this.deriv]
    have h1 : 0 < 1 + t ^ 2 := by positivity
    rw [sub_nonneg, div_le_one h1]; nlinarith [sq_nonneg t]
  have hh : Monotone (fun x : ℝ => x ^ 3 / 3 - x + Real.arctan x) := by
    refine monotone_of_deriv_nonneg (((differentiable_pow 3).div_const 3).sub differentiable_id
      |>.add Real.differentiable_arctan) ?_
    intro t
    have : HasDerivAt (fun x : ℝ => x ^ 3 / 3 - x + Real.arctan x)
        ((3 : ℕ) * t ^ (3 - 1) / 3 - 1 + 1 / (1 + t ^ 2)) t :=
      (((hasDerivAt_pow 3 t).div_const 3).sub (hasDerivAt_id t)).add (Real.hasDerivAt_arctan t)
    rw [this.deriv]
    have h1 : 0 < 1 + t ^ 2 := by positivity
    have : ((3 : ℕ) * t ^ (3 - 1) / 3 - 1 + 1 / (1 + t ^ 2) : ℝ) = t ^ 4 / (1 + t ^ 2) := by
      field_simp; ring
    rw [this]; positivity
  constructor
  · have := hg hx; simpa using this
  · have := hh hx; simp at this; linarith

/-- `|x - arctan x| ≤ |x|³/3`. -/
lemma q2b_abs_sub_arctan_le (x : ℝ) : |x - Real.arctan x| ≤ |x| ^ 3 / 3 := by
  rcases le_total 0 x with hx | hx
  · obtain ⟨h1, h2⟩ := q2b_arctan_bounds hx
    rw [abs_of_nonneg h1, abs_of_nonneg hx]; exact h2
  · obtain ⟨h1, h2⟩ := q2b_arctan_bounds (neg_nonneg.mpr hx)
    rw [Real.arctan_neg] at h1 h2
    rw [abs_of_nonpos hx, ← abs_neg, abs_of_nonneg (by linarith)]
    linarith

/-- The Weierstrass series in `phaseShift` is `O(|η|³)`. -/
lemma q2b_abs_tsum_sub_arctan_le (η : ℝ) :
    |∑' n : ℕ, (η / (n + 1) - Real.arctan (η / (n + 1)))| ≤
      |η| ^ 3 / 3 * ∑' n : ℕ, (1 / ((n : ℝ) + 1) ^ 3) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))).congr
      fun n => by push_cast; rfl
  rw [← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm (q2a_summable_phase η).norm).trans ?_
  refine (q2a_summable_phase η).norm.tsum_le_tsum (fun n => ?_) (hs.mul_left _)
  rw [Real.norm_eq_abs]
  refine (q2b_abs_sub_arctan_le _).trans_eq ?_
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  field_simp

/-- **DLMF 33.5.7**: `σ_0(η) ∼ -γη` as `η → 0` (continuous branch). -/
@[dlmf 33.5.E7]
theorem phaseShift_zero_isEquivalent :
    phaseShift 0 ~[𝓝[≠] 0] (fun η => -Real.eulerMascheroniConstant * η) := by
  have hγ : Real.eulerMascheroniConstant ≠ 0 :=
    (lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant).ne'
  set C := ∑' n : ℕ, (1 / ((n : ℝ) + 1) ^ 3)
  have hO : (fun η => phaseShift 0 η - -Real.eulerMascheroniConstant * η)
      =O[𝓝[≠] 0] (fun η : ℝ => η ^ 3) := by
    refine IsBigO.of_bound (1 / 3 * C) (Eventually.of_forall fun η => ?_)
    simp only [phaseShift, Finset.range_zero, Finset.sum_empty, add_zero,
      add_sub_cancel_left, Real.norm_eq_abs, abs_pow]
    refine (q2b_abs_tsum_sub_arctan_le η).trans_eq ?_
    ring
  refine hO.trans_isLittleO ?_
  have h3 : (fun η : ℝ => η ^ 3) =o[𝓝 0] (fun η : ℝ => η ^ 1) := isLittleO_pow_pow (by norm_num)
  simpa using (h3.mono nhdsWithin_le_nhds).const_mul_right (neg_ne_zero.mpr hγ)


/-! ### §33.5(iv) Large `ℓ` -/

section q2bPoch

open DLMF.Hypergeometric

/-- `(a)_n = ∏_{j<n} (a + j)`. -/
lemma q2b_poch_eq_prod (a : ℂ) (n : ℕ) : poch a n = ∏ j ∈ Finset.range n, (a + j) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih => rw [poch_succ, ih, Finset.prod_range_succ]

/-- The terms of `M(ℓ+1-iη, 2ℓ+2, z)` as products of ratios. -/
lemma q2b_term_eq (ℓ n : ℕ) (η : ℝ) (z : ℂ) :
    poch ((ℓ : ℂ) + 1 - I * η) n / (poch (2 * ℓ + 2) n * n !) * z ^ n =
      (∏ j ∈ Finset.range n, (((ℓ : ℂ) + 1 - I * η + j) / (2 * ℓ + 2 + j))) * (z ^ n / n !) := by
  have hb : ∀ j ∈ Finset.range n, (2 * (ℓ : ℂ) + 2 + j) ≠ 0 := fun j _ => by
    have : (0 : ℝ) < 2 * ℓ + 2 + j := by positivity
    exact_mod_cast this.ne'
  rw [Finset.prod_div_distrib, q2b_poch_eq_prod, q2b_poch_eq_prod]
  have : ∏ j ∈ Finset.range n, (2 * (ℓ : ℂ) + 2 + j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hb
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- `M(ℓ+1-iη, 2ℓ+2, 2iρ) → e^{iρ}` as `ℓ → ∞` (Tannery's theorem). -/
lemma q2b_tendsto_kummerM_large (η ρ : ℝ) :
    Tendsto (fun ℓ : ℕ => kummerM ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ)) atTop
      (𝓝 (exp (I * ρ))) := by
  have hexp : exp (I * ρ) = ∑' n : ℕ, (I * ρ) ^ n / n ! := by
    simpa [exp_eq_exp_ℂ] using (congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℂ)) (I * ρ))
  rw [hexp]
  unfold kummerM
  simp_rw [q2b_term_eq]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖(2 * I * ρ : ℂ)‖ ^ n / n !)
    (Real.summable_pow_div_factorial _) (fun n => ?_) ?_
  · have hj : ∀ j ∈ Finset.range n, Tendsto (fun ℓ : ℕ => ((ℓ : ℂ) + 1 - I * η + j) /
        (2 * ℓ + 2 + j)) atTop (𝓝 (1 / 2)) := by
      intro j _
      have hinv : Tendsto (fun ℓ : ℕ => (((2 * (2 * ℓ + 2 + j) : ℝ) : ℂ))⁻¹) atTop (𝓝 0) := by
        have : Tendsto (fun ℓ : ℕ => (2 * (2 * (ℓ : ℝ) + 2 + j))⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _
            (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop
              (by norm_num))) |>.const_mul_atTop (by norm_num))
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
        rw [ofReal_zero] at h2
        exact h2.congr fun ℓ => by simp
      have := (hinv.const_mul ((j : ℂ) - 2 * I * η)).const_add (1 / 2 : ℂ)
      rw [mul_zero, add_zero] at this
      refine this.congr fun ℓ => ?_
      have : (2 * (ℓ : ℂ) + 2 + j) ≠ 0 := by
        have : (0 : ℝ) < 2 * ℓ + 2 + j := by positivity
        exact_mod_cast this.ne'
      rw [show ((2 * (2 * (ℓ : ℝ) + 2 + j) : ℝ) : ℂ) = 2 * (2 * (ℓ : ℂ) + 2 + j) by
        push_cast; ring]
      set D : ℂ := 2 * (ℓ : ℂ) + 2 + j with hD
      rw [show (ℓ : ℂ) + 1 - I * η + j = (D + (j - 2 * I * η)) / 2 by rw [hD]; ring, mul_inv,
        div_div]
      field_simp
    have hp := (tendsto_finsetProd _ hj).mul_const ((2 * I * ρ : ℂ) ^ n / n !)
    rw [Finset.prod_const, Finset.card_range] at hp
    convert hp using 2
    rw [show (2 * I * ρ : ℂ) = 2 * (I * ρ) by ring, mul_pow, div_pow, one_pow]
    have : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
    rw [mul_pow, mul_pow]; ring
  · filter_upwards [eventually_ge_atTop (Nat.ceil (η ^ 2))] with ℓ hℓ n
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have hle : ‖∏ j ∈ Finset.range n, (((ℓ : ℂ) + 1 - I * η + j) / (2 * ℓ + 2 + j))‖ ≤ 1 := by
      rw [norm_prod]
      refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
      have hpos : (0 : ℝ) < 2 * ℓ + 2 + j := by positivity
      rw [norm_div, div_le_one (by
        rw [show (2 * (ℓ : ℂ) + 2 + j) = ((2 * ℓ + 2 + j : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real]; simp; positivity)]
      rw [show (2 * (ℓ : ℂ) + 2 + j) = ((2 * ℓ + 2 + j : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg hpos.le,
        show ((ℓ : ℂ) + 1 - I * η + j) = ((ℓ + 1 + j : ℝ) : ℂ) + (-η : ℝ) * I by push_cast; ring,
        norm_add_mul_I]
      have hη : η ^ 2 ≤ ℓ := (Nat.le_ceil _).trans (by exact_mod_cast hℓ)
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
    calc _ ≤ 1 * (‖(2 * I * ρ : ℂ)‖ ^ n / n !) := by
          apply mul_le_mul hle le_rfl (by positivity) zero_le_one
      _ = _ := one_mul _

/-- `F_ℓ(η,ρ)/(C_ℓ(η) ρ^{ℓ+1}) → 1` as `ℓ → ∞`. -/
lemma q2b_tendsto_coulombF_ratio (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun ℓ : ℕ => coulombF ℓ η ρ / (coulombC ℓ η * ρ ^ (ℓ + 1))) atTop (𝓝 1) := by
  have h := ((Complex.continuous_re.tendsto _).comp
    ((q2b_tendsto_kummerM_large η ρ).const_mul (exp (-I * ρ))))
  rw [Function.comp_def, ← Complex.exp_add, show -I * (ρ : ℂ) + I * ρ = 0 by ring,
    Complex.exp_zero, one_re] at h
  refine h.congr fun ℓ => ?_
  have hc : coulombC ℓ η * ρ ^ (ℓ + 1) ≠ 0 := (mul_pos (coulombC_pos ℓ η) (by positivity)).ne'
  rw [eq_div_iff hc]
  have h1 := ofReal_coulombF ℓ η ρ
  rw [coulombWave] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.ofReal_re] at h2
  rw [h2, show (coulombC ℓ η : ℂ) * ((ρ : ℂ) ^ (ℓ + 1) * exp (-I * ρ) *
      kummerM (↑ℓ + 1 - I * ↑η) (2 * ↑ℓ + 2) (2 * I * ↑ρ)) =
      ((coulombC ℓ η * ρ ^ (ℓ + 1) : ℝ) : ℂ) *
        (exp (-I * ρ) * kummerM (↑ℓ + 1 - I * ↑η) (2 * ↑ℓ + 2) (2 * I * ↑ρ)) by
      push_cast; ring, re_ofReal_mul]
  ring

/-- If `ε_n → 0` and `g_{n+1} = 1 + ε_n g_n`, then `g_n → 1`. -/
lemma q2b_tendsto_of_rec {g ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hg : ∀ n, g (n + 1) = 1 + ε n * g n) : Tendsto g atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hε.eventually (Metric.ball_mem_nhds 0
    (by norm_num : (0 : ℝ) < 1 / 2)))
  set B := max |g N| 2
  have hB : ∀ n, N ≤ n → |g n| ≤ B := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ n hn ih =>
      have he : |ε n| < 1 / 2 := by simpa [Real.dist_eq] using hN n hn
      rw [hg n]
      calc |1 + ε n * g n| ≤ 1 + |ε n| * |g n| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_one, abs_mul]
        _ ≤ 1 + 1 / 2 * B := by gcongr
        _ ≤ B := by have := le_max_right |g N| 2; linarith
  have hbd : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖g n‖) :=
    ⟨B, eventually_map.mpr (eventually_atTop.mpr ⟨N, fun n hn => hB n hn⟩)⟩
  have := (hε.zero_mul_isBoundedUnder_le hbd).const_add 1
  rw [add_zero] at this
  rw [← tendsto_add_atTop_iff_nat 1]
  exact this.congr fun n => (hg n).symm

end q2bPoch

/-- **DLMF 33.5.8**: as `ℓ → ∞` with `η` and `ρ > 0` fixed, `F_ℓ(η,ρ) ∼ C_ℓ(η) ρ^{ℓ+1}` and
`G_ℓ(η,ρ) ∼ ρ^{-ℓ}/((2ℓ+1) C_ℓ(η))`. -/
@[dlmf 33.5.E8]
theorem coulomb_isEquivalent_large_ell (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (fun ℓ : ℕ => coulombF ℓ η ρ) ~[atTop] (fun ℓ => coulombC ℓ η * ρ ^ (ℓ + 1)) ∧
      (fun ℓ : ℕ => coulombG ℓ η ρ) ~[atTop]
        (fun ℓ => (ρ ^ ℓ)⁻¹ / ((2 * ℓ + 1) * coulombC ℓ η)) := by
  have hq := q2b_tendsto_coulombF_ratio η hρ
  refine ⟨isEquivalent_of_tendsto_one hq, ?_⟩
  set q : ℕ → ℝ := fun ℓ => coulombF ℓ η ρ / (coulombC ℓ η * ρ ^ (ℓ + 1)) with hqdef
  set R : ℕ → ℝ := fun ℓ => recurrenceR (ℓ + 1) η with hRdef
  set g : ℕ → ℝ := fun ℓ => R ℓ * coulombF ℓ η ρ * coulombG (ℓ + 1) η ρ with hgdef
  have hRpos : ∀ ℓ, 0 < R ℓ := fun ℓ => c33a_recurrenceR_pos ℓ η
  have hR : ∀ ℓ, R ℓ * ((ℓ + 1) / Real.sqrt (((ℓ : ℝ) + 1) ^ 2 + η ^ 2)) = 1 := fun ℓ => by
    simp only [hRdef]
    rw [c33a_recurrenceR_succ]
    have : 0 < Real.sqrt (((ℓ : ℝ) + 1) ^ 2 + η ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  have hRC : ∀ ℓ, R ℓ * coulombC ℓ η = (2 * ((ℓ + 1 : ℕ) : ℝ) + 1) * coulombC (ℓ + 1) η :=
    fun ℓ => by
      simp only [hRdef]; rw [recurrenceR_eq_coulombC_div]
      field_simp [(coulombC_pos ℓ η).ne']
  have hF : ∀ ℓ, coulombF ℓ η ρ = q ℓ * (coulombC ℓ η * ρ ^ (ℓ + 1)) := fun ℓ => by
    simp only [hqdef]
    rw [div_mul_cancel₀ _ (mul_pos (coulombC_pos ℓ η) (pow_pos hρ (ℓ + 1))).ne']
  have hcross : ∀ ℓ, g ℓ = 1 + R ℓ * coulombF (ℓ + 1) η ρ * coulombG ℓ η ρ := fun ℓ => by
    have h := coulombF_mul_coulombG_sub ℓ η hρ
    have := hR ℓ
    rw [← h] at this
    simp only [hgdef]
    linear_combination this
  -- `R ℓ → 1`
  have hRt : Tendsto R atTop (𝓝 1) := by
    have h1 : Tendsto (fun ℓ : ℕ => η ^ 2 / ((ℓ + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
    have := ((Real.continuous_sqrt.tendsto _).comp (h1.const_add 1))
    rw [add_zero, Real.sqrt_one] at this
    exact this.congr fun ℓ => rfl
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hq.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  set ε : ℕ → ℝ := fun ℓ => R (ℓ + 1) ^ 2 * q (ℓ + 2) * ρ ^ 2 /
    (q ℓ * ((2 * ℓ + 3) * (2 * ℓ + 5))) with hεdef
  have hCl : ∀ ℓ, coulombC (ℓ + 1) η = R ℓ * coulombC ℓ η / (2 * ((ℓ + 1 : ℕ) : ℝ) + 1) :=
    fun ℓ => by rw [hRC]; field_simp
  have hrec : ∀ n, g (n + N + 1) = 1 + ε (n + N) * g (n + N) := by
    intro n
    set ℓ := n + N
    have hqℓ : 0 < q ℓ := hN ℓ (by omega)
    have h1 := hcross (ℓ + 1)
    have hG : coulombG (ℓ + 1) η ρ = g ℓ / (R ℓ * coulombF ℓ η ρ) := by
      have : R ℓ * coulombF ℓ η ρ ≠ 0 := by
        rw [hF]; have := hRpos ℓ; have := coulombC_pos ℓ η; positivity
      rw [eq_div_iff this]; simp only [hgdef]; ring
    rw [h1, hG, hF (ℓ + 1 + 1), hF ℓ, hCl (ℓ + 1), hCl ℓ]
    simp only [hεdef]
    have := hRpos ℓ; have := coulombC_pos ℓ η; have := hRpos (ℓ + 1)
    push_cast
    field_simp
    ring
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have hinv : Tendsto (fun ℓ : ℕ => ((2 * (ℓ : ℝ) + 3) * (2 * ℓ + 5))⁻¹) atTop (𝓝 0) := by
      refine tendsto_inv_atTop_zero.comp ?_
      refine Tendsto.atTop_mul_atTop₀ ?_ ?_ <;>
        exact tendsto_atTop_add_const_right _ _
          (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    have h := ((((hRt.comp (tendsto_add_atTop_nat 1)).pow 2).mul
      (hq.comp (tendsto_add_atTop_nat 2))).mul_const (ρ ^ 2)).div hq one_ne_zero |>.mul hinv
    rw [mul_zero] at h
    refine h.congr fun ℓ => ?_
    simp only [hεdef, Function.comp_apply, Pi.div_apply, div_eq_mul_inv, mul_inv]
    ring
  have hgt : Tendsto g atTop (𝓝 1) := by
    rw [← tendsto_add_atTop_iff_nat N]
    exact q2b_tendsto_of_rec ((tendsto_add_atTop_iff_nat N).mpr hεt) fun n => by
      rw [show n + 1 + N = n + N + 1 by ring]; exact hrec n
  refine isEquivalent_of_tendsto_one ?_
  rw [← tendsto_add_atTop_iff_nat 1]
  have := hgt.div hq one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop N] with ℓ hℓ
  have hqℓ : 0 < q ℓ := hN ℓ hℓ
  have hG : coulombG (ℓ + 1) η ρ = g ℓ / (R ℓ * coulombF ℓ η ρ) := by
    have : R ℓ * coulombF ℓ η ρ ≠ 0 := by
      rw [hF]; have := hRpos ℓ; have := coulombC_pos ℓ η; positivity
    rw [eq_div_iff this]; simp only [hgdef]; ring
  simp only [Pi.div_apply]
  rw [hG, hF, hCl ℓ]
  have := hRpos ℓ; have := coulombC_pos ℓ η
  push_cast
  field_simp

/-- Asymptotic equivalence of positive functions from their squares. -/
lemma q2b_isEquivalent_of_sq {α : Type*} {l : Filter α} {u v : α → ℝ}
    (hu : ∀ᶠ x in l, 0 < u x) (hv : ∀ᶠ x in l, 0 < v x)
    (h : Tendsto (fun x => u x ^ 2 / v x ^ 2) l (𝓝 1)) : u ~[l] v := by
  refine isEquivalent_of_tendsto_one ?_
  have := (Real.continuous_sqrt.tendsto 1).comp h
  rw [Real.sqrt_one] at this
  refine this.congr' ?_
  filter_upwards [hu, hv] with x hux hvx
  simp only [Function.comp_apply, Pi.div_apply, ← div_pow]
  exact Real.sqrt_sq (div_pos hux hvx).le

/-- Euler's product for `sinh(πη)/(πη)`. -/
lemma q2b_tendsto_prod_sinh {η : ℝ} (hη : η ≠ 0) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1 + η ^ 2 / ((j : ℝ) + 1) ^ 2)) atTop
      (𝓝 (Real.sinh (π * η) / (π * η))) := by
  have h := (Complex.tendsto_euler_sin_prod (I * η)).div_const (π * (I * η))
  have hne : (π : ℂ) * (I * η) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (mul_ne_zero I_ne_zero (by exact_mod_cast hη))
  have h2 : Tendsto (fun n : ℕ => ((∏ j ∈ Finset.range n, (1 + η ^ 2 / ((j : ℝ) + 1) ^ 2) : ℝ) : ℂ))
      atTop (𝓝 ((Real.sinh (π * η) / (π * η) : ℝ) : ℂ)) := by
    convert h using 1
    · funext n
      rw [mul_comm, mul_div_assoc, div_self hne, mul_one]
      push_cast
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [mul_pow, I_sq]; ring
    · rw [show (π : ℂ) * (I * η) = ((π * η : ℝ) : ℂ) * I by push_cast; ring, Complex.sin_mul_I,
        ← Complex.ofReal_sinh]
      have : ((π * η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero Real.pi_ne_zero hη
      push_cast
      field_simp
  have := (Complex.continuous_re.tendsto _).comp h2
  simp only [Function.comp_def, Complex.ofReal_re] at this
  exact this

/-- `∏_{k=1}^ℓ (η²+k²) = (ℓ!)² ∏_{k=1}^ℓ (1 + η²/k²)`. -/
lemma q2b_prod_Icc_eq (η : ℝ) (ℓ : ℕ) :
    ∏ k ∈ Finset.Icc 1 ℓ, (η ^ 2 + (k : ℝ) ^ 2) =
      (ℓ ! : ℝ) ^ 2 * ∏ j ∈ Finset.range ℓ, (1 + η ^ 2 / ((j : ℝ) + 1) ^ 2) := by
  induction ℓ with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ, Nat.factorial_succ]
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- `|Γ(ℓ+1+iη)|/ℓ! → 1` as `ℓ → ∞` (squared form). -/
lemma q2b_tendsto_norm_Gamma_div_factorial (η : ℝ) :
    Tendsto (fun ℓ : ℕ => (‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ / ℓ !) ^ 2) atTop (𝓝 1) := by
  have hrw : ∀ ℓ : ℕ, (‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ / ℓ !) ^ 2 =
      ‖Gamma (1 + I * η)‖ ^ 2 * ∏ j ∈ Finset.range ℓ, (1 + η ^ 2 / ((j : ℝ) + 1) ^ 2) := by
    intro ℓ
    have hf : (ℓ ! : ℝ) ≠ 0 := by positivity
    rw [div_pow, c33a_normSq_Gamma_succ, q2b_prod_Icc_eq]
    field_simp
  simp_rw [hrw]
  rcases eq_or_ne η 0 with rfl | hη
  · simp
  have := (q2b_tendsto_prod_sinh hη).const_mul (‖Gamma (1 + I * η)‖ ^ 2)
  rw [c33a_normSq_Gamma_one η hη] at this ⊢
  convert this using 2
  have hs : Real.sinh (π * η) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero hη
  have hx : π * η ≠ 0 := mul_ne_zero Real.pi_ne_zero hη
  field_simp

/-- `C_ℓ(η) = e^{-πη/2}/(2ℓ+1)!! · |Γ(ℓ+1+iη)|/ℓ!`. -/
lemma q2b_coulombC_eq (ℓ : ℕ) (η : ℝ) :
    coulombC ℓ η = Real.exp (-π * η / 2) / (2 * ℓ + 1)‼ *
      (‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ / ℓ !) := by
  rw [coulombC, Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  have h1 : ((2 * ℓ + 1)‼ : ℝ) ≠ 0 := by exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have h2 : (ℓ ! : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp


/-- The ratio in DLMF 33.5.9 in terms of Stirling's sequence. -/
lemma q2b_doubleFactorial_ratio {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Real.sqrt 2 * (2 * (ℓ : ℝ)) ^ (ℓ + 1) / ((2 * ℓ + 1)‼ * Real.exp ℓ) =
      Stirling.stirlingSeq ℓ / Stirling.stirlingSeq (2 * ℓ) * (2 * ℓ / (2 * ℓ + 1)) := by
  have h1 : ((2 * ℓ + 1)‼ : ℝ) = (2 * ℓ + 1) * (2 * ℓ)! / (2 ^ ℓ * ℓ !) := by
    have := Nat.factorial_eq_mul_doubleFactorial (2 * ℓ)
    rw [Nat.doubleFactorial_two_mul, Nat.factorial_succ] at this
    have h2 : (2 ^ ℓ * ℓ ! : ℝ) ≠ 0 := by positivity
    rw [eq_div_iff h2]
    exact_mod_cast this.symm
  have hl : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hs : Real.sqrt (2 * ((2 * ℓ : ℕ) : ℝ)) = Real.sqrt 2 * Real.sqrt (2 * ℓ) := by
    rw [← Real.sqrt_mul (by norm_num)]; push_cast; ring_nf
  have ha : 0 < Real.sqrt (2 * ℓ) := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [Stirling.stirlingSeq, h1, hs, div_pow, Real.exp_one_pow]
  have hf1 : (ℓ ! : ℝ) ≠ 0 := by positivity
  have hf2 : ((2 * ℓ)! : ℝ) ≠ 0 := by positivity
  have he : Real.exp ℓ ≠ 0 := (Real.exp_pos _).ne'
  have he2 : Real.exp ((2 * ℓ : ℕ) : ℝ) = Real.exp ℓ ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [he2]
  push_cast
  field_simp
  ring

/-- **DLMF 33.5.9**: `C_ℓ(η) ∼ e^{-πη/2}/(2ℓ+1)!! ∼ e^{-πη/2} e^ℓ/(√2 (2ℓ)^{ℓ+1})` as
`ℓ → ∞`. -/
@[dlmf 33.5.E9]
theorem coulombC_isEquivalent_large_ell (η : ℝ) :
    (fun ℓ : ℕ => coulombC ℓ η) ~[atTop] (fun ℓ => Real.exp (-π * η / 2) / (2 * ℓ + 1)‼) ∧
      (fun ℓ : ℕ => Real.exp (-π * η / 2) / ((2 * ℓ + 1)‼ : ℝ)) ~[atTop]
        (fun ℓ => Real.exp (-π * η / 2) *
          (Real.exp ℓ / (Real.sqrt 2 * (2 * (ℓ : ℝ)) ^ (ℓ + 1)))) := by
  constructor
  · refine q2b_isEquivalent_of_sq (Eventually.of_forall fun ℓ => coulombC_pos ℓ η)
      (Eventually.of_forall fun ℓ => by positivity) ?_
    refine (q2b_tendsto_norm_Gamma_div_factorial η).congr fun ℓ => ?_
    rw [q2b_coulombC_eq, mul_pow]
    have : (Real.exp (-π * η / 2) / ((2 * ℓ + 1)‼ : ℝ)) ^ 2 ≠ 0 := by positivity
    field_simp
  · refine isEquivalent_of_tendsto_one ?_
    have hs := Stirling.tendsto_stirlingSeq_sqrt_pi
    have hs2 := hs.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    have hq : Tendsto (fun ℓ : ℕ => 2 * (ℓ : ℝ) / (2 * ℓ + 1)) atTop (𝓝 1) := by
      have := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 / 2 : ℝ)
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
      field_simp
    have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have := (hs.div hs2 hπ).mul hq
    rw [div_self hπ, one_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
    simp only [Pi.div_apply, Function.comp_apply, id]
    rw [← q2b_doubleFactorial_ratio hℓ]
    have he := Real.exp_pos (-π * η / 2)
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have : (0 : ℝ) < (2 * ℓ : ℝ) := by linarith
    have h2 : ((2 * ℓ + 1)‼ : ℝ) ≠ 0 := by positivity
    field_simp

/-! ### The phase shift and `C_0` for large `|η|` (via Binet's formula) -/

section q2bBinet

open DLMF.Gamma

/-- `1 + iη` lies in the slit plane. -/
lemma q2b_mem_slitPlane (η : ℝ) : (1 + I * η : ℂ) ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (by simp))

/-- `η ↦ Im` of Binet's exponent at `1 + iη` is continuous. -/
lemma q2b_continuous_im_binet :
    Continuous (fun η : ℝ => (binetExponent (1 + I * η)).im) := by
  refine continuous_im.comp ?_
  rw [continuous_iff_continuousAt]
  intro η
  have h := (differentiableOn_binetExponent.differentiableAt
    (isOpen_slitPlane.mem_nhds (q2b_mem_slitPlane η))).continuousAt
  exact ContinuousAt.comp (g := binetExponent) h
    ((by fun_prop : Continuous fun η : ℝ => (1 + I * η : ℂ)).continuousAt)

/-- Binet's exponent is real at `1`. -/
lemma q2b_binetExponent_one_im : (binetExponent (1 + I * ((0 : ℝ) : ℂ))).im = 0 := by
  have := binetExponent_ofReal (x := 1) one_pos
  simp only [ofReal_zero, mul_zero, add_zero]
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp, this, ofReal_im]

/-- The continuous-branch phase shift `σ_0(η)` is the imaginary part of Binet's Stirling
exponent at `1 + iη`. -/
lemma q2b_phaseShift_zero_eq_im (η : ℝ) :
    phaseShift 0 η = (binetExponent (1 + I * η)).im := by
  obtain ⟨hspec, h0, hc⟩ := phaseShift_spec 0
  set f : ℝ → ℝ := fun η => phaseShift 0 η - (binetExponent (1 + I * η)).im with hf
  have hmaps : MapsTo f univ (AddSubgroup.zmultiples (2 * π) : Set ℝ) := by
    intro t _
    have hs := hspec t
    simp only [Nat.cast_zero, zero_add] at hs
    rw [Gamma_eq_exp_binetExponent (q2b_mem_slitPlane t)] at hs
    set B := binetExponent (1 + I * t)
    have hB : exp B = (Real.exp B.re : ℂ) * exp (I * B.im) := by
      rw [ofReal_exp, ← Complex.exp_add]; congr 1; apply Complex.ext <;> simp
    rw [Complex.norm_exp, hB] at hs
    have hne : (Real.exp B.re : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    have he := mul_left_cancel₀ hne hs
    have h1 : exp (I * (phaseShift 0 t : ℂ) - I * B.im) = 1 := by
      rw [Complex.exp_sub, ← he, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    simp only [hf, zsmul_eq_mul]
    linarith
  have hcont : Continuous f := hc.sub q2b_continuous_im_binet
  have hdisc : IsDiscrete (AddSubgroup.zmultiples (2 * π) : Set ℝ) :=
    isDiscrete_iff_discreteTopology.mpr
      (inferInstanceAs (DiscreteTopology (AddSubgroup.zmultiples (2 * π))))
  have := (isPreconnected_univ (α := ℝ)).constant_of_mapsTo hdisc hcont.continuousOn hmaps
    (mem_univ η) (mem_univ 0)
  have hf0 : f 0 = 0 := by simp only [hf, h0, q2b_binetExponent_one_im, sub_zero]
  rw [hf0] at this
  simp only [hf] at this
  linarith


/-- The imaginary part of Binet's exponent at `1 + iη`. -/
lemma q2b_im_binet (η : ℝ) :
    (binetExponent (1 + I * η)).im = arg (1 + I * η) / 2 + η * Real.log ‖1 + I * (η : ℂ)‖ - η +
      (binetMu (1 + I * η)).im := by
  have h2 : (log (2 * π : ℂ)).im = 0 := by
    rw [log_im, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      arg_ofReal_of_nonneg (by positivity)]
  simp only [binetExponent, add_im, sub_im, mul_im, h2, log_re, log_im]
  simp
  ring

/-- `ph(1 + iη) = arctan η`. -/
lemma q2b_arg_one_add_I_mul (η : ℝ) : arg (1 + I * η) = Real.arctan η := by
  have hre : 0 < (1 + I * (η : ℂ)).re := by simp
  have habs := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  rw [abs_lt] at habs
  have ht : Real.tan (arg (1 + I * η)) = η := by rw [tan_arg]; simp
  calc arg (1 + I * η) = Real.arctan (Real.tan (arg (1 + I * η))) :=
        (Real.arctan_tan habs.1 habs.2).symm
    _ = Real.arctan η := by rw [ht]

/-- `|1 + iη| = √(1 + η²)`. -/
lemma q2b_norm_one_add_I_mul (η : ℝ) : ‖1 + I * (η : ℂ)‖ = Real.sqrt (1 + η ^ 2) := by
  rw [show (1 + I * η : ℂ) = ((1 : ℝ) : ℂ) + η * I by push_cast; ring, norm_add_mul_I]
  norm_num

/-- Stieltjes' bound at `1 + iη`. -/
lemma q2b_norm_binetMu_le {η : ℝ} (hη : η ≠ 0) : ‖binetMu (1 + I * η)‖ ≤ 1 / (6 * |η|) := by
  refine (norm_binetMu_le (q2b_mem_slitPlane η)).trans ?_
  have hre : (1 + I * (η : ℂ)).re = 1 := by simp
  have : |η| ≤ ‖1 + I * (η : ℂ)‖ := by
    rw [q2b_norm_one_add_I_mul]
    exact Real.abs_le_sqrt (by linarith)
  rw [hre]
  apply one_div_le_one_div_of_le (by positivity)
  linarith

/-- The phase part of DLMF 33.10.6. -/
lemma q2b_tendsto_phaseShift_zero_atTop :
    Tendsto (fun η => phaseShift 0 η - (η * (Real.log η - 1) + π / 4)) atTop (𝓝 0) := by
  have hA : Tendsto (fun η : ℝ => Real.arctan η / 2 - π / 4) atTop (𝓝 0) := by
    have := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).div_const 2 |>.sub_const
      (π / 4)
    convert this using 2; ring
  have hL : Tendsto (fun η : ℝ => η * (Real.log (Real.sqrt (1 + η ^ 2)) - Real.log η))
      atTop (𝓝 0) := by
    have hup : Tendsto (fun η : ℝ => 1 / η) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with η hη
      apply mul_nonneg hη.le
      rw [sub_nonneg]
      apply Real.log_le_log hη
      exact (le_abs_self η).trans (Real.abs_le_sqrt (by linarith))
    · filter_upwards [eventually_gt_atTop 0] with η hη
      have hs : 0 < Real.sqrt (1 + η ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [← Real.log_div hs.ne' hη.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hs hη)
      have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + η ^ 2)
      have hge : η ≤ Real.sqrt (1 + η ^ 2) :=
        (le_abs_self η).trans (Real.abs_le_sqrt (by linarith))
      calc η * Real.log (Real.sqrt (1 + η ^ 2) / η)
          ≤ η * (Real.sqrt (1 + η ^ 2) / η - 1) := mul_le_mul_of_nonneg_left h1 hη.le
        _ = Real.sqrt (1 + η ^ 2) - η := by field_simp
        _ ≤ 1 / η := by
          rw [le_div_iff₀ hη]
          nlinarith
  have hM : Tendsto (fun η : ℝ => (binetMu (1 + I * η)).im) atTop (𝓝 0) := by
    have hup : Tendsto (fun η : ℝ => 1 / (6 * |η|)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_abs_atTop_atTop.comp tendsto_id).const_mul_atTop (by norm_num))
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun η => abs_nonneg _) ?_
    filter_upwards [eventually_gt_atTop 0] with η hη
    exact (abs_im_le_norm _).trans (q2b_norm_binetMu_le hη.ne')
  have := (hA.add hL).add hM
  rw [add_zero, add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with η hη
  rw [q2b_phaseShift_zero_eq_im, q2b_im_binet, q2b_arg_one_add_I_mul, q2b_norm_one_add_I_mul]
  ring


/-- `σ_0` is odd. -/
lemma q2b_phaseShift_zero_neg (η : ℝ) : phaseShift 0 (-η) = -phaseShift 0 η := by
  simp only [phaseShift, Finset.range_zero, Finset.sum_empty, add_zero, neg_div,
    Real.arctan_neg, sub_neg_eq_add]
  rw [show (fun n : ℕ => -(η / (n + 1)) + Real.arctan (η / (n + 1))) =
    fun n : ℕ => -(η / (n + 1) - Real.arctan (η / (n + 1))) by funext n; ring, tsum_neg]
  ring

/-- The phase part of DLMF 33.10.10. -/
lemma q2b_tendsto_phaseShift_zero_atBot :
    Tendsto (fun η => phaseShift 0 η - (η * (Real.log (-η) - 1) - π / 4)) atBot (𝓝 0) := by
  have := (q2b_tendsto_phaseShift_zero_atTop.comp tendsto_neg_atBot_atTop).neg
  rw [neg_zero] at this
  refine this.congr fun η => ?_
  simp only [Function.comp_apply, q2b_phaseShift_zero_neg]
  ring

/-- `C_0(η)² = 2πη/(e^{2πη} - 1)`, `η ≠ 0`. -/
lemma q2b_coulombC_zero_sq {η : ℝ} (hη : η ≠ 0) :
    coulombC 0 η ^ 2 = 2 * π * η / (Real.exp (π * η) ^ 2 - 1) := by
  rw [coulombC_sq_eq_prod 0 hη, ← Real.exp_nat_mul]
  simp
  ring_nf

/-- The `C_0` part of DLMF 33.10.6. -/
lemma q2b_coulombC_zero_atTop :
    (fun η => coulombC 0 η) ~[atTop] (fun η => Real.sqrt (2 * π * η) * Real.exp (-π * η)) := by
  refine q2b_isEquivalent_of_sq (Eventually.of_forall fun η => coulombC_pos 0 η) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with η hη
    exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _)
  have he : Tendsto (fun η : ℝ => Real.exp (-π * η)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos]) |>.congr fun η => rfl)
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (he.pow 2)).inv₀ (by norm_num)
  rw [zero_pow two_ne_zero, sub_zero, inv_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with η hη
  rw [q2b_coulombC_zero_sq hη.ne', mul_pow, Real.sq_sqrt (by positivity)]
  rw [show -π * η = -(π * η) by ring, Real.exp_neg]
  have hE1 : Real.exp (π * η) ^ 2 - 1 ≠ 0 := by
    have : 1 < Real.exp (π * η) := Real.one_lt_exp_iff.mpr (by positivity)
    nlinarith
  have hp : 2 * π * η ≠ 0 := by positivity
  have hE2 : Real.exp (π * η) ≠ 0 := (Real.exp_pos _).ne'
  have hE3 : 1 - (Real.exp (π * η))⁻¹ ^ 2 ≠ 0 := by
    rw [inv_pow, sub_ne_zero, ne_comm, inv_ne_one]
    intro h; apply hE1; rw [h]; ring
  field_simp

/-- The `C_0` part of DLMF 33.10.10. -/
lemma q2b_coulombC_zero_atBot :
    (fun η => coulombC 0 η) ~[atBot] (fun η => Real.sqrt (-2 * π * η)) := by
  refine q2b_isEquivalent_of_sq (Eventually.of_forall fun η => coulombC_pos 0 η) ?_ ?_
  · filter_upwards [eventually_lt_atBot 0] with η hη
    exact Real.sqrt_pos.mpr (by nlinarith [Real.pi_pos])
  have he : Tendsto (fun η : ℝ => Real.exp (π * η)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot Real.pi_pos)
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (he.pow 2)).inv₀ (by norm_num)
  rw [zero_pow two_ne_zero, sub_zero, inv_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with η hη
  rw [q2b_coulombC_zero_sq hη.ne, Real.sq_sqrt (by nlinarith [Real.pi_pos])]
  have hE1 : Real.exp (π * η) ^ 2 - 1 ≠ 0 := by
    have : Real.exp (π * η) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    nlinarith [Real.exp_pos (π * η)]
  have hE3 : 1 - Real.exp (π * η) ^ 2 ≠ 0 := by
    intro h; apply hE1; linarith
  have hp : η ≠ 0 := hη.ne
  field_simp
  ring

end q2bBinet

/-! ### §33.10(i) Large `ρ` -/

/-- **DLMF 33.10.2**, lower sign: `H^-_ℓ(η,ρ) ∼ e^{-iθ_ℓ(η,ρ)}` as `ρ → ∞`, in the form
`H^-_ℓ - e^{-iθ_ℓ} → 0` (`|e^{-iθ_ℓ}| = 1`). -/
@[dlmf 33.10.E2]
theorem tendsto_coulombHMinus_sub_exp (ℓ : ℕ) (η : ℝ) :
    Tendsto (fun ρ : ℝ => coulombHMinus ℓ η ρ - exp (-(I * coulombTheta ℓ η ρ))) atTop (𝓝 0) := by
  have h := (continuous_conj.tendsto 0).comp (tendsto_coulombHPlus_sub_exp ℓ η)
  rw [map_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ρ hρ
  simp only [Function.comp_apply, map_sub, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  rw [coulombHMinus_eq_conj ℓ η hρ, neg_mul]

/-! ### §33.10(ii) Large positive `η` -/

/-- **DLMF 33.10.3**: as `η → ∞` with `ηρ = c > 0` fixed,
`F_ℓ ∼ (2ℓ+1)! C_ℓ(η)/(2η)^{ℓ+1} (2ηρ)^{1/2} I_{2ℓ+1}((8ηρ)^{1/2})` and
`G_ℓ ∼ 2(2η)^ℓ/((2ℓ+1)! C_ℓ(η)) (2ηρ)^{1/2} K_{2ℓ+1}((8ηρ)^{1/2})`. -/
@[dlmf 33.10.E3]
theorem coulomb_isEquivalent_eta_atTop (ℓ : ℕ) {c : ℝ} (hc : 0 < c) :
    (fun η : ℝ => (coulombF ℓ η (c / η) : ℂ)) ~[atTop]
      (fun η => ((2 * ℓ + 1)! * coulombC ℓ η / (2 * η) ^ (ℓ + 1) * Real.sqrt (2 * c) : ℝ) *
        besselI (2 * ℓ + 1) (Real.sqrt (8 * c))) ∧
    (fun η : ℝ => (coulombG ℓ η (c / η) : ℂ)) ~[atTop]
      (fun η => (2 * (2 * η) ^ ℓ / ((2 * ℓ + 1)! * coulombC ℓ η) * Real.sqrt (2 * c) : ℝ) *
        besselK (2 * ℓ + 1) (Real.sqrt (8 * c))) := by
  sorry

/-- **DLMF 33.10.4**: as `η → ∞` with `ηρ = c > 0` fixed,
`F_0 ∼ e^{-πη} (πρ)^{1/2} I_1((8ηρ)^{1/2})` and `G_0 ∼ 2 e^{πη} (ρ/π)^{1/2} K_1((8ηρ)^{1/2})`. -/
@[dlmf 33.10.E4]
theorem coulomb_zero_isEquivalent_eta_atTop {c : ℝ} (hc : 0 < c) :
    (fun η : ℝ => (coulombF 0 η (c / η) : ℂ)) ~[atTop]
      (fun η => (Real.exp (-π * η) * Real.sqrt (π * (c / η)) : ℝ) *
        besselI 1 (Real.sqrt (8 * c))) ∧
    (fun η : ℝ => (coulombG 0 η (c / η) : ℂ)) ~[atTop]
      (fun η => (2 * Real.exp (π * η) * Real.sqrt (c / η / π) : ℝ) *
        besselK 1 (Real.sqrt (8 * c))) := by
  sorry

/-- **DLMF 33.10.5**: as `η → ∞` with `ηρ = c > 0` fixed,
`F_0' ∼ e^{-πη} (2πη)^{1/2} I_0((8ηρ)^{1/2})` and
`G_0' ∼ -2 e^{πη} (2η/π)^{1/2} K_0((8ηρ)^{1/2})` (derivatives in `ρ` at `ρ = c/η`). -/
@[dlmf 33.10.E5]
theorem coulomb_zero_deriv_isEquivalent_eta_atTop {c : ℝ} (hc : 0 < c) :
    (fun η : ℝ => ((deriv (coulombF 0 η) (c / η) : ℝ) : ℂ)) ~[atTop]
      (fun η => (Real.exp (-π * η) * Real.sqrt (2 * π * η) : ℝ) *
        besselI 0 (Real.sqrt (8 * c))) ∧
    (fun η : ℝ => ((deriv (coulombG 0 η) (c / η) : ℝ) : ℂ)) ~[atTop]
      (fun η => (-2 * Real.exp (π * η) * Real.sqrt (2 * η / π) : ℝ) *
        besselK 0 (Real.sqrt (8 * c))) := by
  sorry

/-- **DLMF 33.10.6**: `σ_0(η) = η(ln η - 1) + π/4 + o(1)` and `C_0(η) ∼ (2πη)^{1/2} e^{-πη}`
as `η → ∞` (continuous branch of `σ_0`). -/
@[dlmf 33.10.E6]
theorem phaseShift_coulombC_eta_atTop :
    Tendsto (fun η => phaseShift 0 η - (η * (Real.log η - 1) + π / 4)) atTop (𝓝 0) ∧
      (fun η => coulombC 0 η) ~[atTop] (fun η => Real.sqrt (2 * π * η) * Real.exp (-π * η)) :=
  ⟨q2b_tendsto_phaseShift_zero_atTop, q2b_coulombC_zero_atTop⟩

/-! ### §33.10(iii) Large negative `η` -/

/-- **DLMF 33.10.7**: as `η → -∞` with `ηρ = c < 0` fixed,
`F_ℓ = (2ℓ+1)! C_ℓ(η)/(-2η)^{ℓ+1} ((-2ηρ)^{1/2} J_{2ℓ+1}((-8ηρ)^{1/2}) + o(|η|^{1/4}))` and
`G_ℓ = -π(-2η)^ℓ/((2ℓ+1)! C_ℓ(η)) ((-2ηρ)^{1/2} Y_{2ℓ+1}((-8ηρ)^{1/2}) + o(|η|^{1/4}))`
(as printed; numerically the bracketed error is much smaller). -/
@[dlmf 33.10.E7]
theorem coulomb_eta_atBot (ℓ : ℕ) {c : ℝ} (hc : c < 0) :
    (fun η : ℝ => (coulombF ℓ η (c / η) : ℂ) /
        (((2 * ℓ + 1)! * coulombC ℓ η / (-2 * η) ^ (ℓ + 1) : ℝ) : ℂ) -
        Real.sqrt (-2 * c) * Complex.besselJ (2 * ℓ + 1) (Real.sqrt (-8 * c)))
      =o[atBot] (fun η => |η| ^ (1 / 4 : ℝ)) ∧
    (fun η : ℝ => (coulombG ℓ η (c / η) : ℂ) /
        ((-π * (-2 * η) ^ ℓ / ((2 * ℓ + 1)! * coulombC ℓ η) : ℝ) : ℂ) -
        Real.sqrt (-2 * c) * besselY (2 * ℓ + 1) (Real.sqrt (-8 * c)))
      =o[atBot] (fun η => |η| ^ (1 / 4 : ℝ)) := by
  sorry

/-- **DLMF 33.10.8**: as `η → -∞` with `ηρ = c < 0` fixed,
`F_0 = (πρ)^{1/2} J_1((-8ηρ)^{1/2}) + o(|η|^{-1/4})` and
`G_0 = -(πρ)^{1/2} Y_1((-8ηρ)^{1/2}) + o(|η|^{-1/4})`. -/
@[dlmf 33.10.E8]
theorem coulomb_zero_eta_atBot {c : ℝ} (hc : c < 0) :
    (fun η : ℝ => (coulombF 0 η (c / η) : ℂ) -
        Real.sqrt (π * (c / η)) * Complex.besselJ 1 (Real.sqrt (-8 * c)))
      =o[atBot] (fun η => |η| ^ (-(1 / 4) : ℝ)) ∧
    (fun η : ℝ => (coulombG 0 η (c / η) : ℂ) +
        Real.sqrt (π * (c / η)) * besselY 1 (Real.sqrt (-8 * c)))
      =o[atBot] (fun η => |η| ^ (-(1 / 4) : ℝ)) := by
  sorry

/-- **DLMF 33.10.9**: as `η → -∞` with `ηρ = c < 0` fixed,
`F_0' = (-2πη)^{1/2} J_0((-8ηρ)^{1/2}) + o(|η|^{1/4})` and
`G_0' = -(-2πη)^{1/2} Y_0((-8ηρ)^{1/2}) + o(|η|^{1/4})` (derivatives in `ρ` at `ρ = c/η`). -/
@[dlmf 33.10.E9]
theorem coulomb_zero_deriv_eta_atBot {c : ℝ} (hc : c < 0) :
    (fun η : ℝ => ((deriv (coulombF 0 η) (c / η) : ℝ) : ℂ) -
        Real.sqrt (-2 * π * η) * Complex.besselJ 0 (Real.sqrt (-8 * c)))
      =o[atBot] (fun η => |η| ^ (1 / 4 : ℝ)) ∧
    (fun η : ℝ => ((deriv (coulombG 0 η) (c / η) : ℝ) : ℂ) +
        Real.sqrt (-2 * π * η) * besselY 0 (Real.sqrt (-8 * c)))
      =o[atBot] (fun η => |η| ^ (1 / 4 : ℝ)) := by
  sorry

/-- **DLMF 33.10.10**: `σ_0(η) = η(ln(-η) - 1) - π/4 + o(1)` and `C_0(η) ∼ (-2πη)^{1/2}` as
`η → -∞` (continuous branch of `σ_0`). -/
@[dlmf 33.10.E10]
theorem phaseShift_coulombC_eta_atBot :
    Tendsto (fun η => phaseShift 0 η - (η * (Real.log (-η) - 1) - π / 4)) atBot (𝓝 0) ∧
      (fun η => coulombC 0 η) ~[atBot] (fun η => Real.sqrt (-2 * π * η)) :=
  ⟨q2b_tendsto_phaseShift_zero_atBot, q2b_coulombC_zero_atBot⟩

end DLMF.Coulomb
