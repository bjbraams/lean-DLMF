/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.UniformLG2.ExpansionAlgebra

/-!
# Uniform parabolic cylinder expansions and their derivatives

Positive- and negative-parameter uniform expansions for U and its derivative, with the error and
normalizer conditions explicit.

Source references and common attribution are retained in
`DLMF.ParabolicCylinder.UniformLG2`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open Polynomial

/-! ### Positive parameter: the uniform expansions (DLMF 12.10(v)) -/

/-- `A² = (t²+1)^{-1/2}`. -/
lemma pcfLG2_PA_sq (t : ℝ) : pcfLG2_PA t ^ 2 = (t^2+1) ^ (-(1/2):ℝ) := by
  have hy : 0 < t^2+1 := by positivity
  rw [pcfLG2_PA, ← Real.rpow_natCast ((t^2+1) ^ (-1/4:ℝ)), ← Real.rpow_mul hy.le]; norm_num

/-- `A A' = -(t/2)(t²+1)^{-3/2}`. -/
lemma pcfLG2_PA_mul_PA1 (t : ℝ) : pcfLG2_PA t * pcfLG2_PA1 t = -(t/2) * (t^2+1) ^ (-(3/2):ℝ) := by
  have hy : 0 < t^2+1 := by positivity
  unfold pcfLG2_PA pcfLG2_PA1
  rw [mul_left_comm, pcfLG_rpow_mul hy (c := -(3/2)) (by norm_num)]

/-- `|A A'| ≤ 1/2`. -/
lemma pcfLG2_abs_PA_mul_PA1 (t : ℝ) : |pcfLG2_PA t * pcfLG2_PA1 t| ≤ 1/2 := by
  have hy : 0 < t^2+1 := by positivity
  rw [pcfLG2_PA_mul_PA1, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _), abs_neg, abs_div,
    abs_two]
  have h1 : |t| ≤ (t^2+1) ^ (1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : (t^2+1) ^ (1/2:ℝ) * (t^2+1) ^ (-(3/2):ℝ) ≤ 1 := by
    rw [pcfLG_rpow_mul hy (c := -1) (by norm_num), Real.rpow_neg_one]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])
  have h3 := Real.rpow_pos_of_pos hy (-(3/2):ℝ)
  calc |t| / 2 * (t^2+1) ^ (-(3/2):ℝ) ≤ (t^2+1) ^ (1/2:ℝ) / 2 * (t^2+1) ^ (-(3/2):ℝ) := by
        gcongr
    _ ≤ 1/2 := by nlinarith

/-- `0 < A² ≤ 1`. -/
lemma pcfLG2_PA_sq_le_one (t : ℝ) : pcfLG2_PA t ^ 2 ≤ 1 := by
  have h := pcfLG2_PA_sq_recip t
  have hp : 0 < pcfLG2_PA t ^ 2 := by have := pcfLG2_PA_pos t; positivity
  have h1 : 1 ≤ Real.sqrt (t^2+1) := by
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (t^2+1) := Real.sqrt_le_sqrt (by nlinarith)
  rw [← h] at h1
  exact (one_le_inv₀ hp).1 h1

/-- The barred Olver coefficient is real: `Ū_s(t)/(t²+1)^{3s/2} = Ā_s(t)`. -/
lemma pcfLG2_olverUBar_eq (s : ℕ) (t : ℝ) :
    pcfOlverUBar s t / ((t:ℂ)^2+1)^(3*(s:ℂ)/2) = (pcfLG2_Pa s t : ℂ) := by
  have hy : 0 < t^2+1 := by positivity
  have e1 : ((t:ℂ)^2+1)^(3*(s:ℂ)/2) = (((t^2+1) ^ (3*(s:ℝ)/2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hy.le]; push_cast; rfl
  have e0 : I^s * aeval (-I * t) (pcfOlverU s) = (((pcfLG2_Q s).eval t : ℝ) : ℂ) :=
    pcfLG2_bar_real (pcfLG_olverPair_inv s).1 t
  rw [pcfOlverUBar, e0, e1, pcfLG2_Pa,
    Real.rpow_neg hy.le]
  push_cast
  rw [div_eq_mul_inv]

/-- The barred derivative coefficient `B̄_s = Ā_s - AA'Ā_{s-1} - A²Ā_{s-1}'`. -/
noncomputable def pcfLG2_Pb (s : ℕ) (t : ℝ) : ℝ :=
  if s = 0 then 1 else pcfLG2_Pa s t - pcfLG2_PA t * pcfLG2_PA1 t * pcfLG2_Pa (s-1) t -
    pcfLG2_PA t ^ 2 * pcfLG2_Pad (s-1) t

/-- The barred Olver coefficient `V̄_s(t)/(t²+1)^{3s/2}` (DLMF 12.10.30) is `B̄_s(t)`. -/
lemma pcfLG2_olverVBar_eq (s : ℕ) (t : ℝ) :
    pcfOlverVBar s t / ((t:ℂ)^2+1)^(3*(s:ℂ)/2) = (pcfLG2_Pb s t : ℂ) := by
  have hy : 0 < t^2+1 := by positivity
  rcases s with _ | m
  · simp [pcfOlverVBar, pcfLG2_Pb, pcfOlverV]
  · have hV : pcfOlverV (m+1) = pcfOlverU (m+1) + C (1/2:ℝ)*X*pcfOlverU m - (pcfOlverPair m).2 := by
      simp [pcfOlverV]
    have e1 : I^(m+1) * aeval (-I * t) (pcfOlverU (m+1)) = (((pcfLG2_Q (m+1)).eval t : ℝ) : ℂ) :=
      pcfLG2_bar_real (pcfLG_olverPair_inv (m+1)).1 t
    have e2 : I^m * aeval (-I * t) (pcfOlverU m) = (((pcfLG2_Q m).eval t : ℝ) : ℂ) :=
      pcfLG2_bar_real (pcfLG_olverPair_inv m).1 t
    have e3 : I^(m+1) * aeval (-I * t) (pcfOlverPair m).2 = (((pcfLG2_R m).eval t : ℝ) : ℂ) :=
      pcfLG2_bar_real (pcfLG_olverPair_inv m).2 t
    have hnum : pcfOlverVBar (m+1) t = (((pcfLG2_Q (m+1)).eval t + t/2 * (pcfLG2_Q m).eval t -
        (pcfLG2_R m).eval t : ℝ) : ℂ) := by
      rw [pcfOlverVBar, hV]
      simp only [map_add, map_sub, map_mul, aeval_C, aeval_X]
      push_cast
      linear_combination e1 + ((t:ℂ)/2) * e2 - e3 +
        (-(t:ℂ)/2 * I^m * aeval (-I * (t:ℂ)) (pcfOlverU m)) * Complex.I_sq
    have e4 : ((t:ℂ)^2+1)^(3*((m+1:ℕ):ℂ)/2) = (((t^2+1) ^ (3*((m+1:ℕ):ℝ)/2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hy.le]; push_cast; rfl
    rw [hnum, e4]
    have hPb : pcfLG2_Pb (m+1) t = ((pcfLG2_Q (m+1)).eval t + t/2 * (pcfLG2_Q m).eval t -
        (pcfLG2_R m).eval t) * ((t^2+1) ^ (3*((m+1:ℕ):ℝ)/2))⁻¹ := by
      simp only [pcfLG2_Pb, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [pcfLG2_PA_mul_PA1, pcfLG2_PA_sq, pcfLG2_Pa, pcfLG2_Pa, pcfLG2_Pad, ← Real.rpow_neg hy.le]
      have a1 : (t^2+1) ^ (-(3/2):ℝ) * (t^2+1) ^ (-(3*(m:ℝ)/2)) = (t^2+1) ^ (-(3*((m+1:ℕ):ℝ)/2)) :=
        pcfLG_rpow_mul hy (by push_cast; ring)
      have a2 : (t^2+1) ^ (-(1/2):ℝ) * (t^2+1) ^ (-((3*(m:ℝ)+2)/2)) =
          (t^2+1) ^ (-(3*((m+1:ℕ):ℝ)/2)) := pcfLG_rpow_mul hy (by push_cast; ring)
      have a3 : (3*((m+1:ℕ):ℝ)/2) = 3*((m+1 : ℕ) : ℝ)/2 := rfl
      push_cast at a1 a2 ⊢
      linear_combination ((t/2) * (pcfLG2_Q m).eval t) * a1 + (-(pcfLG2_R m).eval t) * a2
    rw [hPb]
    push_cast
    rw [div_eq_mul_inv]

/-- `T_{N+1}(B̄) = T_{N+1}(Ā) - AA'u^{-1}T_N(Ā) - A²u^{-1}T_N(Ā')`. -/
lemma pcfLG2_ser_Pb (M : ℕ) (u t : ℝ) (hu : u ≠ 0) :
    pcfLG2_ser pcfLG2_Pb (M+1) u t = pcfLG2_ser pcfLG2_Pa (M+1) u t -
      pcfLG2_PA t * pcfLG2_PA1 t / u * pcfLG2_ser pcfLG2_Pa M u t -
      pcfLG2_PA t ^ 2 / u * pcfLG2_ser pcfLG2_Pad M u t := by
  induction M with
  | zero =>
    simp [pcfLG2_ser, pcfLG2_Pb, pcfLG2_Pa, pcfLG2_Q, pcfLG2_bar, pcfOlverU, pcfOlverPair]
  | succ M ih =>
    simp only [pcfLG2_ser] at ih ⊢
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (M+1), Finset.sum_range_succ _ M,
      Finset.sum_range_succ _ M]
    simp only [pcfLG2_Pb, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    field_simp
    ring

/-- A bound for the truncated series. -/
lemma pcfLG2_abs_ser_le {a : ℕ → ℝ → ℝ} {K : ℕ → ℝ} (ha : ∀ s t, |a s t| ≤ K s) (M : ℕ)
    {u : ℝ} (hu : 1 ≤ u) (t : ℝ) : |pcfLG2_ser a M u t| ≤ ∑ s ∈ Finset.range M, K s := by
  unfold pcfLG2_ser
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [abs_div, abs_of_pos (pow_pos (by linarith : (0:ℝ) < u) s)]
  exact (div_le_self (abs_nonneg _) (one_le_pow₀ hu)).trans (ha s t)

/-- Borel bound for the Borel sum of real coefficients, composed with `u = μ²`. -/
lemma pcfLG2_borel_bound (c : ℕ → ℝ) {Φ : ℝ → ℝ} (hΦ : ∀ N : ℕ,
    (fun u : ℝ => Φ u - ∑ s ∈ Finset.range N, c s / u^s) =O[atTop] (fun u : ℝ => (u^N)⁻¹))
    (N : ℕ) : ∃ B μ₁ : ℝ, 0 ≤ B ∧ 1 ≤ μ₁ ∧ ∀ μ, μ₁ ≤ μ →
      |Φ (μ^2) - pcfLG2_ser (fun s _ => c s) N (μ^2) 0| ≤ B / (μ^2)^N := by
  obtain ⟨B, hB⟩ := (hΦ N).bound
  obtain ⟨u₁, hu₁⟩ := eventually_atTop.1 (hB.and (eventually_ge_atTop (1:ℝ)))
  refine ⟨max B 0, max 1 u₁, le_max_right _ _, le_max_left _ _, fun μ hμ => ?_⟩
  have hμ1 : 1 ≤ μ := (le_max_left _ _).trans hμ
  have hμu : u₁ ≤ μ^2 := by nlinarith [le_max_right 1 u₁]
  obtain ⟨h1, h2⟩ := hu₁ (μ^2) hμu
  have hpos : 0 < (μ^2)^N := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hpos] at h1
  rw [pcfLG2_ser]
  calc _ ≤ B * ((μ^2)^N)⁻¹ := h1
    _ ≤ max B 0 * ((μ^2)^N)⁻¹ := by gcongr; exact le_max_left _ _
    _ = max B 0 / (μ^2)^N := by rw [div_eq_mul_inv]

/-- The denominator `G e^{-μ²ξ̄}(t²+1)^{-1/4}` in real form. -/
lemma pcfLG2_denom_eq (μ t : ℝ) (G : ℂ) :
    G * cexp (-(μ:ℂ)^2 * (pcfXiBar t : ℂ)) / ((t:ℂ)^2+1)^(1/4:ℂ) =
      G * ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) := by
  have hy : 0 < t^2+1 := by positivity
  have e1 : ((t:ℂ)^2+1)^(1/4:ℂ) = (((t^2+1) ^ (1/4:ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hy.le]; push_cast; rfl
  have hp : 0 < (t^2+1) ^ (1/4:ℝ) := Real.rpow_pos_of_pos hy _
  rw [e1, pcfLG2_PA, show (-1/4:ℝ) = -(1/4) by norm_num, Real.rpow_neg hy.le]
  have hp' : (((t^2+1) ^ (1/4:ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

/-- The denominator `G (t²+1)^{1/4} e^{-μ²ξ̄}` in real form. -/
lemma pcfLG2_denom'_eq (μ t : ℝ) (G : ℂ) :
    G * ((t:ℂ)^2+1)^(1/4:ℂ) * cexp (-(μ:ℂ)^2 * (pcfXiBar t : ℂ)) =
      G * (((pcfLG2_PA t)⁻¹ * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) := by
  have hy : 0 < t^2+1 := by positivity
  have e1 : ((t:ℂ)^2+1)^(1/4:ℂ) = (((t^2+1) ^ (1/4:ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hy.le]; push_cast; rfl
  rw [e1, pcfLG2_PA, show (-1/4:ℝ) = -(1/4) by norm_num, Real.rpow_neg hy.le, inv_inv]
  push_cast
  ring_nf

/-- The series of `Ū_s/(t²+1)^{3s/2}` is the real series of `Ā_s`. -/
lemma pcfLG2_sum_UBar_eq (N : ℕ) (μ t : ℝ) :
    ∑ s ∈ Finset.range N, pcfOlverUBar s t / ((t:ℂ)^2+1)^(3*(s:ℂ)/2) / (μ:ℂ)^(2*s) =
      (pcfLG2_ser pcfLG2_Pa N (μ^2) t : ℂ) := by
  rw [pcfLG2_ser]; push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pcfLG2_olverUBar_eq, pow_mul]

/-- The series of `V̄_s/(t²+1)^{3s/2}` is the real series of `B̄_s`. -/
lemma pcfLG2_sum_VBar_eq (N : ℕ) (μ t : ℝ) :
    ∑ s ∈ Finset.range N, pcfOlverVBar s t / ((t:ℂ)^2+1)^(3*(s:ℂ)/2) / (μ:ℂ)^(2*s) =
      (pcfLG2_ser pcfLG2_Pb N (μ^2) t : ℂ) := by
  rw [pcfLG2_ser]; push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pcfLG2_olverVBar_eq, pow_mul]

/-- The series `∑ c̄_s μ^{-2s}` is real. -/
lemma pcfLG2_sum_cbar_eq (N : ℕ) (μ : ℝ) :
    ∑ s ∈ Finset.range N, (pcfLG2_cbar s : ℂ) / (μ:ℂ)^(2*s) =
      (pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0 : ℂ) := by
  rw [pcfLG2_ser]; push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pow_mul]

/-- A uniform expansion holds for all `N` once it holds for `N ≥ 1` and the leading
coefficient is `1`. -/
lemma pcfLG2_expansion_of_one_le {F : ℝ → ℝ → ℂ} {Cf : ℕ → ℝ → ℂ} {S : Set ℝ}
    (h0 : ∀ t, Cf 0 t = 1)
    (h : ∀ N : ℕ, 1 ≤ N → (fun p : ℝ × ℝ => F p.1 p.2 -
      ∑ s ∈ Finset.range N, Cf s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter S]
      (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ)))) :
    HasCylinderUniformExpansion F Cf S := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 := h 1 le_rfl
    have hb : (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*(1:ℕ):ℤ))) =O[pcfUniformFilter S]
        (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*(0:ℕ):ℤ))) := by
      refine IsBigO.of_bound 1 (pcfLG_eventually_uniform 1 fun μ hμ t _ => ?_)
      rw [pcfLG_norm_zpow (by linarith), pcfLG_norm_zpow (by linarith)]
      simp only [pow_zero, inv_one, one_mul, pow_one]
      exact inv_le_one_of_one_le₀ (by nlinarith)
    have hc : (fun _ : ℝ × ℝ => (1:ℂ)) =O[pcfUniformFilter S]
        (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*(0:ℕ):ℤ))) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun p => by simp)
    refine ((h1.trans hb).add hc).congr_left fun p => ?_
    simp [h0]
  · exact h N hN

/-- A Borel sum with leading coefficient one stays between one half and two along `μ²`.
These bounds justify dividing by the normalizing function in the uniform cylinder expansions. -/
private lemma borel_sum_bounds_near_one {c : ℕ → ℝ} {Φ : ℝ → ℝ} (hc0 : c 0 = 1)
    (hΦ : ∀ N : ℕ, (fun u : ℝ => Φ u - ∑ s ∈ Finset.range N, c s / u ^ s)
      =O[atTop] (fun u : ℝ => (u ^ N)⁻¹)) :
    ∃ μ₁ : ℝ, 1 ≤ μ₁ ∧ ∀ μ, μ₁ ≤ μ → 1 / 2 ≤ Φ (μ ^ 2) ∧ Φ (μ ^ 2) ≤ 2 := by
  obtain ⟨B, μ₁, hB, hμ₁, hb⟩ := pcfLG2_borel_bound c hΦ 1
  refine ⟨max μ₁ (2*B+1), le_trans hμ₁ (le_max_left _ _), fun μ hμ => ?_⟩
  have hμ1 : μ₁ ≤ μ := (le_max_left _ _).trans hμ
  have h := hb μ hμ1
  have hS : pcfLG2_ser (fun s _ => c s) 1 (μ^2) 0 = 1 := by simp [pcfLG2_ser, hc0]
  rw [hS, pow_one] at h
  have hμB : 2*B+1 ≤ μ := (le_max_right _ _).trans hμ
  have hμ2 : 2*B ≤ μ^2 := by nlinarith
  have : B / μ^2 ≤ 1/2 := by rw [div_le_iff₀ (by nlinarith)]; linarith
  have := abs_le.1 (h.trans this)
  constructor <;> linarith [this.1, this.2]

/-- **DLMF 12.10.25 and 12.10.29 with the normalizer of DLMF 12.10.28** (Olver's uniform
expansions of `U(½μ², μt√2)` and its derivative, uniformly for all real `t`). The normalizer is
`g(μ) = 1/(μ√2 h(μ) Φ(μ²))`, where `Φ` is a Borel sum of `∑ c̄_s u^{-s}`; the whole-line
Liouville–Green expansion (`pcfLG2_pos_core`) gives both expansions, and the formal identity
`(∑ (-1)^s c_s u^{-s}) · ½(1 + ∑ (-1)^s γ_s (u/2)^{-s}) = 1` (`pcfLG2_twc_mul_d`) gives
`IsCylinderGBarNormalizer g`. -/
@[dlmf 12.10.E25, dlmf 12.10.E29]
theorem pcf_positive_parameter_uniform :
    ∃ g : ℝ → ℂ, IsCylinderGBarNormalizer g ∧ HasCylinderUniformExpansion (fun μ t => pcfU (μ^2/2) (μ*t*Real.sqrt 2)/(g μ*exp (-μ^2*pcfXiBar t)/(t^2+1:ℂ)^(1/4:ℂ))) (fun s t => pcfOlverUBar s t/(t^2+1:ℂ)^(3*(s:ℂ)/2)) univ ∧ HasCylinderUniformExpansion (fun μ t => pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2)/(-(μ:ℂ)/Real.sqrt 2*g μ*(t^2+1:ℂ)^(1/4:ℂ)*exp (-μ^2*pcfXiBar t))) (fun s t => pcfOlverVBar s t/(t^2+1:ℂ)^(3*(s:ℂ)/2)) univ := by
  obtain ⟨Φ, hΦ⟩ := pcfLG_exists_asymptotic pcfLG2_cbar
  have hc0 : pcfLG2_cbar 0 = 1 := by rw [pcfLG2_cbar, pcfLG2_Q_coeff]; simp [pcfLG_c_zero]
  obtain ⟨μ₁, hμ₁, hΦb⟩ := borel_sum_bounds_near_one hc0 hΦ

  set g : ℝ → ℂ := fun μ => (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) / (Φ (μ^2) : ℂ) with hg
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
  have hgH : ∀ μ, 0 < μ → (Φ (μ^2) : ℂ) ≠ 0 →
      g μ * μ * Real.sqrt 2 * pcfH μ = 1 / (Φ (μ^2) : ℂ) := by
    intro μ hμ hΦ0
    have hh : (pcfLG_h μ : ℂ) ≠ 0 := by exact_mod_cast (pcfLG_h_pos hμ).ne'
    have hμ' : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
    rw [pcfLG_pcfH_eq hμ]; simp only [g]; push_cast; field_simp
  refine ⟨g, fun N => ?_, ?_, ?_⟩
  · -- the normalizer
    have had : pcfLG2_cauchy (fun s => (pcfLG2_cbar s : ℂ))
        (fun n => 1/2 * (pcfLG2_delta n + (-1)^n * (pcfGammaCoeff n * 2^n))) = pcfLG2_delta := by
      have e : (fun s => (pcfLG2_cbar s : ℂ)) = pcfLG2_tw (fun s => (pcfLG_c s : ℂ)) := by
        funext s; simp [pcfLG2_tw, pcfLG2_cbar, pcfLG2_Q_coeff]
      rw [e]; exact pcfLG2_twc_mul_d
    have hG : ∀ M : ℕ, (fun μ : ℝ => (g μ * μ * Real.sqrt 2 * pcfH μ) *
        (∑ s ∈ Finset.range M, (pcfLG2_cbar s : ℂ) / (μ:ℂ)^(2*s)) - 1) =O[atTop]
        (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ))) := by
      intro M
      obtain ⟨B, μ₂, hB, hμ₂, hb⟩ := pcfLG2_borel_bound pcfLG2_cbar hΦ M
      refine IsBigO.of_bound (2*B) ?_
      filter_upwards [eventually_ge_atTop (max μ₁ μ₂)] with μ hμ
      have hμ0 : 0 < μ := by linarith [le_max_left μ₁ μ₂]
      obtain ⟨hΦl, -⟩ := hΦb μ ((le_max_left _ _).trans hμ)
      have hΦ0 : (Φ (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < Φ (μ^2)).ne'
      rw [hgH μ hμ0 hΦ0, pcfLG2_sum_cbar_eq, pcfLG_norm_zpow hμ0]
      set L := pcfLG2_ser (fun s _ => pcfLG2_cbar s) M (μ^2) 0
      have heq : 1 / (Φ (μ^2) : ℂ) * (L : ℂ) - 1 = (((L - Φ (μ^2)) / Φ (μ^2) : ℝ) : ℂ) := by
        push_cast; field_simp
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos (show (0:ℝ) < Φ (μ^2) by linarith), abs_sub_comm]
      have := hb μ ((le_max_right _ _).trans hμ)
      rw [div_le_iff₀ (by linarith)]
      calc |Φ (μ^2) - L| ≤ B / (μ^2)^M := this
        _ = 2*B * ((μ^2)^M)⁻¹ * (1/2) := by ring
        _ ≤ 2*B * ((μ^2)^M)⁻¹ * Φ (μ^2) := by gcongr
    have h := pcfLG2_recip_sq had hG (N+1)
    have hγ0 : pcfGammaCoeff 0 = 1 := pcfGammaCoeff_initial.1
    refine h.congr' ?_ (Eventually.of_forall fun μ => by push_cast; ring_nf)
    filter_upwards [eventually_ne_atTop 0] with μ hμ
    have hμ' : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ
    rw [Finset.sum_range_succ']
    simp only [pcfLG2_delta, hγ0, ite_true, Nat.succ_ne_zero, ite_false, pow_zero, mul_zero,
      zero_add, div_one, Finset.mul_sum, mul_one]
    have : ∀ j : ℕ, 1/2 * ((-1)^(j+1) * (pcfGammaCoeff (j+1) * 2^(j+1))) / (μ:ℂ)^(2*(j+1)) =
        1/2 * ((-1)^(j+1) * pcfGammaCoeff (j+1) / ((μ:ℂ)^2/2)^(j+1)) := fun j => by
      rw [div_pow, pow_mul]; field_simp
    simp only [this]
    ring
  · -- the expansion of `U`
    refine pcfLG2_expansion_of_one_le (fun t => by
      show pcfOlverUBar 0 t / _ = 1
      rw [pcfLG2_olverUBar_eq]
      simp [pcfLG2_Pa, pcfLG2_Q, pcfLG2_bar, pcfOlverU, pcfOlverPair]) fun N hN => ?_
    obtain ⟨C, μ₀, hC, hμ₀, hcore⟩ := pcfLG2_pos_core hN
    obtain ⟨B, μ₂, hB, hμ₂, hb⟩ := pcfLG2_borel_bound pcfLG2_cbar hΦ N
    refine IsBigO.of_bound (4*C + 3*B) (pcfLG_eventually_uniform (max μ₀ (max μ₁ μ₂))
      fun μ hμ t _ => ?_)
    have hμ0 : 0 < μ := by linarith [le_max_left μ₀ (max μ₁ μ₂)]
    obtain ⟨hL, hct⟩ := hcore μ ((le_max_left _ _).trans hμ)
    obtain ⟨hS, e, e', he, -, hU, -⟩ := hct t
    obtain ⟨hΦl, hΦu⟩ := hΦb μ ((le_max_left _ _).trans ((le_max_right _ _).trans hμ))
    have hbo := hb μ ((le_max_right _ _).trans ((le_max_right _ _).trans hμ))
    set L := pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0
    set S := pcfLG2_ser pcfLG2_Pa N (μ^2) t
    have hLpos : 1/2 ≤ L := by linarith [(abs_le.1 hL).1]
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < L).ne'
    have hΦ0 : (Φ (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < Φ (μ^2)).ne'
    have hH0 : (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have := pcfLG_h_pos hμ0
      exact_mod_cast (by positivity : (0:ℝ) < (μ * Real.sqrt 2 * pcfLG_h μ)⁻¹).ne'
    have hAe : ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pcfLG2_PA_pos t) (Real.exp_pos _)).ne'
    simp only
    rw [pcfLG2_denom_eq, pcfLG2_sum_UBar_eq, pcfLG_norm_zpow hμ0, hU]
    have hF : (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) / (L : ℂ) *
        ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) * (S + e) : ℝ) : ℂ) /
        (g μ * ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ)) - (S : ℂ) =
        ((Φ (μ^2) / L * e + (Φ (μ^2) - L) / L * S : ℝ) : ℂ) := by
      have h1 : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ0.ne'
      have h2 : (pcfLG_h μ : ℂ) ≠ 0 := by exact_mod_cast (pcfLG_h_pos hμ0).ne'
      have h3 : (pcfLG2_PA t : ℂ) ≠ 0 := by exact_mod_cast (pcfLG2_PA_pos t).ne'
      have h4 : ((Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.exp_pos _).ne'
      simp only [g]
      push_cast at h4 ⊢
      field_simp
      ring
    rw [hF, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos (by linarith : (0:ℝ) < L),
      abs_of_pos (by linarith : (0:ℝ) < Φ (μ^2))]
    have hp : 0 < (μ^2)^N := by positivity
    have h1 : Φ (μ^2) / L ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hS3 : |S| ≤ 3/2 := abs_le.2 ⟨by linarith [(abs_le.1 hS).1], by linarith [(abs_le.1 hS).2]⟩
    calc Φ (μ^2) / L * |e| + |Φ (μ^2) - L| / L * |S|
        ≤ 4 * (C / (μ^2)^N) + (B / (μ^2)^N) / (1/2) * (3/2) := by
          gcongr
      _ = (4*C + 3*B) * ((μ^2)^N)⁻¹ := by ring
  · -- the expansion of `U'`
    refine pcfLG2_expansion_of_one_le (fun t => by
      show pcfOlverVBar 0 t / _ = 1
      rw [pcfLG2_olverVBar_eq]; simp [pcfLG2_Pb]) fun N hN => ?_
    obtain ⟨M, rfl⟩ : ∃ M, N = M+1 := ⟨N-1, by omega⟩
    obtain ⟨C, μ₀, hC, hμ₀, hcore⟩ := pcfLG2_pos_core hN
    obtain ⟨B, μ₂, hB, hμ₂, hb⟩ := pcfLG2_borel_bound pcfLG2_cbar hΦ (M+1)
    choose Kd hKd using pcfLG2_abs_Pad_le
    have hKd0 : ∀ s, 0 ≤ Kd s := fun s => by
      have := (abs_nonneg _).trans (hKd s 0); norm_num at this; exact this
    have hKd' : ∀ s t, |pcfLG2_Pad s t| ≤ Kd s := fun s t =>
      (hKd s t).trans (mul_le_of_le_one_right (hKd0 s)
        (inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])))
    set K : ℕ → ℝ := fun s => ∑ i ∈ Finset.range (3*s+1), |(pcfLG2_Q s).coeff i| with hKdef
    have hK0 : ∀ s, 0 ≤ K s := fun s => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hK : ∀ s t, |pcfLG2_Pa s t| ≤ K s := pcfLG2_abs_Pa_le
    set KW := 3/2 + (∑ s ∈ Finset.range M, K s) + ∑ s ∈ Finset.range M, Kd s with hKW
    refine IsBigO.of_bound (4*(4*C + K M + Kd M) + 2*B*KW)
      (pcfLG_eventually_uniform (max μ₀ (max μ₁ μ₂)) fun μ hμ t _ => ?_)
    have hμ0 : 0 < μ := by linarith [le_max_left μ₀ (max μ₁ μ₂)]
    have hμ1 : 1 ≤ μ := by linarith [le_max_left μ₀ (max μ₁ μ₂)]
    have hu1 : 1 ≤ μ^2 := by nlinarith
    have hu0 : 0 < μ^2 := by positivity
    obtain ⟨hL, hct⟩ := hcore μ ((le_max_left _ _).trans hμ)
    obtain ⟨hS, e, e', he, he', -, hU'⟩ := hct t
    obtain ⟨hΦl, hΦu⟩ := hΦb μ ((le_max_left _ _).trans ((le_max_right _ _).trans hμ))
    have hbo := hb μ ((le_max_right _ _).trans ((le_max_right _ _).trans hμ))
    rw [Nat.add_sub_cancel] at he'
    set L := pcfLG2_ser (fun s _ => pcfLG2_cbar s) (M+1) (μ^2) 0
    set Sa := pcfLG2_ser pcfLG2_Pa (M+1) (μ^2) t
    set Sd := pcfLG2_ser pcfLG2_Pad (M+1) (μ^2) t
    set a := pcfLG2_PA t with ha
    set a1 := pcfLG2_PA1 t with ha1
    set Ex := Real.exp (-(μ^2 * pcfXiBar t)) with hEx
    set W := pcfLG2_ser pcfLG2_Pb (M+1) (μ^2) t with hWdef
    set H : ℝ := (μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ with hH
    set Y := (Sa + e) - a*a1*(Sa+e)/μ^2 - a^2*(Sd+e')/μ^2 with hY
    have hLpos : 1/2 ≤ L := by linarith [(abs_le.1 hL).1]
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < L).ne'
    have hΦ0 : (Φ (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < Φ (μ^2)).ne'
    have hh := pcfLG_h_pos hμ0
    have hH0 : (H : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (0:ℝ) < (μ * Real.sqrt 2 * pcfLG_h μ)⁻¹).ne'
    have h1 : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ0.ne'
    have h2 : (pcfLG_h μ : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have ha0 : 0 < a := pcfLG2_PA_pos t
    have h3 : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have h4 : (Ex : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    simp only
    rw [pcfLG2_denom'_eq, pcfLG2_sum_VBar_eq, pcfLG_norm_zpow hμ0]
    have hU'' : pcfUDeriv ((μ:ℂ)^2/2) ((μ:ℂ)*t*Real.sqrt 2) = (H:ℂ)/(L:ℂ) *
        ((Ex * ((a1 - μ^2 * a⁻¹) * (Sa + e) + a * (Sd + e')) : ℝ) : ℂ) / ((μ:ℂ)*Real.sqrt 2) := by
      rw [← hU']; field_simp
    rw [hU'']
    have hF : (H:ℂ)/(L:ℂ) * ((Ex * ((a1 - μ^2 * a⁻¹) * (Sa + e) + a * (Sd + e')) : ℝ) : ℂ) /
        ((μ:ℂ)*Real.sqrt 2) / (-(μ:ℂ)/Real.sqrt 2 * g μ * ((a⁻¹ * Ex : ℝ) : ℂ)) - (W:ℂ) =
        ((Φ (μ^2) / L * (Y - W) + (Φ (μ^2) - L) / L * W : ℝ) : ℂ) := by
      simp only [g, hY]
      rw [← hH]
      push_cast
      field_simp
      ring
    rw [hF, Complex.norm_real, Real.norm_eq_abs]
    -- bounds
    have hr : 0 < (μ^2)^(M+1) := by positivity
    have hrM : 0 < (μ^2)^M := by positivity
    have hrr : (μ^2)^(M+1) = (μ^2)^M * μ^2 := pow_succ _ _
    have hW : W = Sa - a*a1/μ^2 * pcfLG2_ser pcfLG2_Pa M (μ^2) t -
        a^2/μ^2 * pcfLG2_ser pcfLG2_Pad M (μ^2) t := pcfLG2_ser_Pb M (μ^2) t hu0.ne'
    have hSa : Sa = pcfLG2_ser pcfLG2_Pa M (μ^2) t + pcfLG2_Pa M t / (μ^2)^M := by
      simp only [Sa, pcfLG2_ser, Finset.sum_range_succ]
    have hSd : Sd = pcfLG2_ser pcfLG2_Pad M (μ^2) t + pcfLG2_Pad M t / (μ^2)^M := by
      simp only [Sd, pcfLG2_ser, Finset.sum_range_succ]
    have hD : Y - W = e - a*a1*e/μ^2 - a^2*e'/μ^2 - a*a1*pcfLG2_Pa M t/(μ^2)^(M+1) -
        a^2*pcfLG2_Pad M t/(μ^2)^(M+1) := by
      rw [hW, hY, hSa, hSd, hrr]; field_simp; ring
    have haa1 : |a*a1| ≤ 1/2 := pcfLG2_abs_PA_mul_PA1 t
    have ha2 : a^2 ≤ 1 := pcfLG2_PA_sq_le_one t
    have ha2' : 0 ≤ a^2 := sq_nonneg a
    have b2 : |a*a1*e/μ^2| ≤ C/(μ^2)^(M+1) := by
      rw [abs_div, abs_mul, abs_of_pos hu0, div_le_iff₀ hu0]
      calc |a*a1| * |e| ≤ 1/2 * (C/(μ^2)^(M+1)) := by gcongr
        _ ≤ C/(μ^2)^(M+1) * μ^2 := by
          have : 0 ≤ C/(μ^2)^(M+1) := by positivity
          nlinarith
    have b3 : |a^2*e'/μ^2| ≤ 2*C/(μ^2)^(M+1) := by
      rw [abs_div, abs_of_pos hu0, hrr, div_le_iff₀ hu0]
      calc |a^2*e'| ≤ 2*C/(μ^2)^M := he'
        _ = 2*C/((μ^2)^M * μ^2) * μ^2 := by field_simp
    have b4 : |a*a1*pcfLG2_Pa M t/(μ^2)^(M+1)| ≤ K M/(μ^2)^(M+1) := by
      rw [abs_div, abs_mul, abs_of_pos hr]
      gcongr
      calc |a*a1| * |pcfLG2_Pa M t| ≤ 1/2 * K M := by gcongr; exact hK M t
        _ ≤ K M := by linarith [hK0 M]
    have b5 : |a^2*pcfLG2_Pad M t/(μ^2)^(M+1)| ≤ Kd M/(μ^2)^(M+1) := by
      rw [abs_div, abs_mul, abs_of_pos hr, abs_of_nonneg ha2']
      gcongr
      calc a^2 * |pcfLG2_Pad M t| ≤ 1 * Kd M := by gcongr; exact hKd' M t
        _ = Kd M := one_mul _
    have hDb : |Y - W| ≤ (4*C + K M + Kd M)/(μ^2)^(M+1) := by
      rw [hD]
      have e1 := abs_le.1 he
      have e2 := abs_le.1 b2
      have e3 := abs_le.1 b3
      have e4 := abs_le.1 b4
      have e5 := abs_le.1 b5
      have : (4*C + K M + Kd M)/(μ^2)^(M+1) = C/(μ^2)^(M+1) + C/(μ^2)^(M+1) +
          2*C/(μ^2)^(M+1) + K M/(μ^2)^(M+1) + Kd M/(μ^2)^(M+1) + 0 := by ring
      have hz : 0 ≤ C/(μ^2)^(M+1) := by positivity
      rw [this]
      refine abs_le.2 ⟨by linarith only [e1.1, e2.2, e3.2, e4.2, e5.2],
        by linarith only [e1.2, e2.1, e3.1, e4.1, e5.1]⟩
    have hWb : |W| ≤ KW := by
      rw [hW]
      have hSa3 : |Sa| ≤ 3/2 := abs_le.2 ⟨by linarith [(abs_le.1 hS).1], by linarith [(abs_le.1 hS).2]⟩
      have c1 : |a*a1/μ^2 * pcfLG2_ser pcfLG2_Pa M (μ^2) t| ≤ ∑ s ∈ Finset.range M, K s := by
        rw [abs_mul, abs_div, abs_of_pos hu0]
        have := pcfLG2_abs_ser_le hK M hu1 t
        have hq : |a*a1|/μ^2 ≤ 1 := by rw [div_le_iff₀ hu0]; linarith
        calc |a*a1|/μ^2 * |pcfLG2_ser pcfLG2_Pa M (μ^2) t| ≤ 1 * ∑ s ∈ Finset.range M, K s := by
              gcongr
          _ = _ := one_mul _
      have c2 : |a^2/μ^2 * pcfLG2_ser pcfLG2_Pad M (μ^2) t| ≤ ∑ s ∈ Finset.range M, Kd s := by
        rw [abs_mul, abs_div, abs_of_pos hu0, abs_of_nonneg ha2']
        have := pcfLG2_abs_ser_le hKd' M hu1 t
        have hq : a^2/μ^2 ≤ 1 := by rw [div_le_iff₀ hu0]; linarith
        calc a^2/μ^2 * |pcfLG2_ser pcfLG2_Pad M (μ^2) t| ≤ 1 * ∑ s ∈ Finset.range M, Kd s := by
              gcongr
          _ = _ := one_mul _
      have f1 := abs_le.1 hSa3
      have f2 := abs_le.1 c1
      have f3 := abs_le.1 c2
      exact abs_le.2 ⟨by linarith only [f1.1, f2.2, f3.2, hKW], by linarith only [f1.2, f2.1, f3.1, hKW]⟩
    have hLp : 0 < L := by linarith only [hLpos]
    have hΦp : 0 < Φ (μ^2) := by linarith only [hΦl]
    have hq1 : Φ (μ^2) / L ≤ 4 := by rw [div_le_iff₀ hLp]; linarith only [hLpos, hΦu]
    have hq2 : |Φ (μ^2) - L| / L ≤ 2*B/(μ^2)^(M+1) := by
      rw [div_le_iff₀ hLp]
      calc |Φ (μ^2) - L| ≤ B/(μ^2)^(M+1) := hbo
        _ = 2*B/(μ^2)^(M+1) * (1/2) := by ring
        _ ≤ 2*B/(μ^2)^(M+1) * L := by gcongr
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos hLp, abs_of_pos hΦp]
    calc Φ (μ^2) / L * |Y - W| + |Φ (μ^2) - L| / L * |W|
        ≤ 4 * ((4*C + K M + Kd M)/(μ^2)^(M+1)) + 2*B/(μ^2)^(M+1) * KW := by
          gcongr
      _ = (4*(4*C + K M + Kd M) + 2*B*KW) * ((μ^2)^(M+1))⁻¹ := by ring

/-! ### Negative parameter: the expansions of `U` and `U'` (DLMF 12.10(ii)) -/

/-- **Recessive Liouville–Green core for negative parameter**: `pcfLG2_core` applied on
`(1+δ/2, ∞)` to `A = (t²-1)^{-1/4}`, `ξ` of DLMF 12.10.7 and Olver's coefficients `A_s`, giving
for `μ ≥ μ₀` and `t ≥ 1+δ` the representations of `U(-½μ², μt√2)` and of its `t`-derivative. -/
lemma pcfLG2_neg_core {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) : ∃ C μ₀ : ℝ, 0 ≤ C ∧ 1 ≤ μ₀ ∧
    ∀ μ, μ₀ ≤ μ →
    |pcfLG2_ser (fun s _ => pcfLG_c s) N (μ^2) 0 - 1| ≤ 1/2 ∧ ∀ t : ℝ, 1 + δ ≤ t →
      |pcfLG2_ser pcfLG_hatA N (μ^2) t - 1| ≤ 1/2 ∧ ∃ e e' : ℝ,
      |e| ≤ C / (μ^2)^N ∧ |pcfLG_A t ^ 2 * e'| ≤ 2 * C / (μ^2)^(N-1) ∧
      pcfU (-μ^2/2) (μ*t*Real.sqrt 2) = pcfH μ /
        (pcfLG2_ser (fun s _ => pcfLG_c s) N (μ^2) 0 : ℂ) *
        ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) * (pcfLG2_ser pcfLG_hatA N (μ^2) t + e) : ℝ) : ℂ) ∧
      (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2) =
        pcfH μ / (pcfLG2_ser (fun s _ => pcfLG_c s) N (μ^2) 0 : ℂ) *
        ((Real.exp (-(μ^2 * pcfXi t)) * ((pcfLG_A1 t - μ^2 * (pcfLG_A t)⁻¹) *
          (pcfLG2_ser pcfLG_hatA N (μ^2) t + e) +
          pcfLG_A t * (pcfLG2_ser pcfLG_hatAd N (μ^2) t + e')) : ℝ) : ℂ) := by
  set c : ℝ := 1 + δ/2 with hcdef
  have hc : 1 < c := by linarith
  choose KA hKA0 hKA using fun s => pcfLG_bound_hatA s hc
  set KS := ∑ s ∈ Finset.range N, KA s
  have hKS : 0 ≤ KS := Finset.sum_nonneg fun s _ => hKA0 s
  obtain ⟨I, hI0, hI⟩ := pcfLG_tail_hatAd N hc
  obtain ⟨V0, hV00, hV⟩ := pcfLG_tail_V hc
  set C := I * Real.exp (V0/2) with hCdef
  have hC0 : 0 ≤ C := by positivity
  set μ₀ := max 1 (2*(KS+C)+1)
  have hμ₀ : 1 ≤ μ₀ := le_max_left _ _
  have hμ₀C : 2*((∑ s ∈ Finset.range N, KA s) + C) ≤ μ₀^2 := by
    have := le_max_right 1 (2*(KS+C)+1); nlinarith
  refine ⟨C, μ₀, hC0, hμ₀, fun μ hμ => ?_⟩
  have hcore := pcfLG2_core (b := c) (A := pcfLG_A) (A1 := pcfLG_A1)
    (A2 := pcfLG_A2) (ξ := pcfXi) (fun t ht => pcfLG_A_pos (hc.trans ht))
    (fun t ht => pcfLG_hasDerivAt_A (hc.trans ht)) (fun t ht => pcfLG_hasDerivAt_A1 (hc.trans ht))
    (pcfLG_continuousOn_A2.mono fun t ht => hc.trans ht)
    (fun t ht => by rw [pcfLG_A_sq_recip (hc.trans ht)]; exact pcfLG_hasDerivAt_xi (hc.trans ht))
    (fun c' hc' => pcfLG_integrableOn_V (hc.trans hc'))
    (fun t ht => hV t ht.le)
    pcfLG_tendsto_A hN (a := pcfLG_hatA) (ad := pcfLG_hatAd) (ad2 := pcfLG_hatAd2)
    (l := pcfLG_c)
    (fun s _ t ht => pcfLG_hasDerivAt_hatA s (hc.trans ht))
    (fun s _ t ht => pcfLG_hasDerivAt_hatAd s (hc.trans ht))
    (fun s _ => (pcfLG_continuousOn_hatAd2 s).mono fun t ht => hc.trans ht)
    pcfLG_hatA_zero
    (fun t _ => by simp [pcfLG_hatAd, pcfOlverPair])
    (fun s _ t ht => pcfLG_recursion s (hc.trans ht))
    (fun c' hc' => pcfLG_integrableOn_hatAd N (hc.trans hc'))
    (fun t ht => by
      have h1 := hI t ht.le
      have h2 : t ^ (-2:ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      nlinarith)
    (K := KA)
    (fun s _ t ht => hKA s t ht.le)
    (fun s _ => pcfLG_tendsto_hatA s)
    (U := fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2))
    (U' := fun μ t => (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2))
    (H := fun μ : ℝ => pcfH μ) (fun μ t _ => pcfLG_hasDerivAt_U μ t)
    (fun μ t ht => (pcfLG_hasDerivAt_U' μ t).congr_deriv (by
      rw [pcfLG_A_pow_four_recip (hc.trans ht)]))
    (fun μ hμ => pcfLG_tendsto_U_div (by linarith)) le_rfl hμ₀ hμ₀C
  obtain ⟨hL, ε, ε', hε⟩ := hcore μ hμ
  refine ⟨hL, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hε t (by linarith)
  refine ⟨?_, ε t, ε' t, h1, h2, h3, h4⟩
  have hu1 : 1 ≤ μ^2 := by nlinarith
  have hser := pcfLG2_abs_sum_sub_one_le hN (f := fun s => pcfLG_hatA s t)
    (pcfLG_hatA_zero t) (fun s _ => hKA s t (by linarith)) hu1
  refine hser.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have : μ₀^2 ≤ μ^2 := by nlinarith
  nlinarith

/-- `A A' = -(t/2)(t²-1)^{-3/2}` for `t > 1`. -/
lemma pcfLG2_neg_A_mul_A1 {t : ℝ} (ht : 1 < t) :
    pcfLG_A t * pcfLG_A1 t = -(t/2) * (t^2-1) ^ (-(3/2):ℝ) := by
  have hy : 0 < t^2-1 := by nlinarith
  unfold pcfLG_A pcfLG_A1
  rw [show (t^2-1) ^ (-1/4:ℝ) * (-(t/2) * (t^2-1) ^ (-5/4:ℝ)) =
    -(t/2) * ((t^2-1) ^ (-1/4:ℝ) * (t^2-1) ^ (-5/4:ℝ)) by ring,
    pcfLG_rpow_mul hy (c := -(3/2)) (by norm_num)]

/-- `A² = (t²-1)^{-1/2}` for `t > 1`. -/
lemma pcfLG2_neg_A_sq {t : ℝ} (ht : 1 < t) : pcfLG_A t ^ 2 = (t^2-1) ^ (-(1/2):ℝ) := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfLG_A, ← Real.rpow_natCast ((t^2-1) ^ (-1/4:ℝ)), ← Real.rpow_mul hy.le]; norm_num

/-- Olver's derivative coefficient `B_s = A_s - AA'A_{s-1} - A²A_{s-1}'` for `t > 1`. -/
noncomputable def pcfLG2_negB (s : ℕ) (t : ℝ) : ℝ :=
  if s = 0 then 1 else pcfLG_hatA s t - pcfLG_A t * pcfLG_A1 t * pcfLG_hatA (s-1) t -
    pcfLG_A t ^ 2 * pcfLG_hatAd (s-1) t

/-- `B_s(t) = v_s(t)/(t²-1)^{3s/2}` (DLMF 12.10.8) is the real coefficient `pcfLG2_negB`. -/
lemma pcfLG2_neg_olverB_eq (s : ℕ) {t : ℝ} (ht : 1 < t) :
    pcfOlverB s t = (pcfLG2_negB s t : ℂ) := by
  have hy : 0 < t^2-1 := by nlinarith
  rcases s with _ | m
  · simp [pcfOlverB, pcfLG2_negB, pcfOlverV]
  · have hV : pcfOlverV (m+1) = pcfOlverU (m+1) + C (1/2:ℝ)*X*pcfOlverU m - (pcfOlverPair m).2 := by
      simp [pcfOlverV]
    have e4 : ((t:ℂ)^2-1)^(3*((m+1:ℕ):ℂ)/2) = (((t^2-1) ^ (3*((m+1:ℕ):ℝ)/2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hy.le]; push_cast; rfl
    have hB : pcfLG2_negB (m+1) t = ((pcfOlverU (m+1)).eval t + t/2 * (pcfOlverU m).eval t -
        (pcfOlverPair m).2.eval t) * ((t^2-1) ^ (3*((m+1:ℕ):ℝ)/2))⁻¹ := by
      simp only [pcfLG2_negB, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [pcfLG2_neg_A_mul_A1 ht, pcfLG2_neg_A_sq ht, pcfLG_hatA, pcfLG_hatA, pcfLG_hatAd,
        ← Real.rpow_neg hy.le]
      have a1 : (t^2-1) ^ (-(3/2):ℝ) * (t^2-1) ^ (-(3*(m:ℝ)/2)) =
          (t^2-1) ^ (-(3*((m+1:ℕ):ℝ)/2)) := pcfLG_rpow_mul hy (by push_cast; ring)
      have a2 : (t^2-1) ^ (-(1/2):ℝ) * (t^2-1) ^ (-((3*(m:ℝ)+2)/2)) =
          (t^2-1) ^ (-(3*((m+1:ℕ):ℝ)/2)) := pcfLG_rpow_mul hy (by push_cast; ring)
      have a0 : (t^2-1) ^ (-(3*((m+1:ℕ):ℝ)/2)) = (t^2-1) ^ (-(3*((m+1:ℕ):ℝ)/2)) := rfl
      push_cast at a1 a2 ⊢
      linear_combination ((t/2) * (pcfOlverU m).eval t) * a1 +
        (-(pcfOlverPair m).2.eval t) * a2
    rw [pcfOlverB, hV, e4, hB]
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X]
    push_cast
    rw [div_eq_mul_inv]; ring

/-- `T_{N+1}(B) = T_{N+1}(A) - AA'u^{-1}T_N(A) - A²u^{-1}T_N(A')`. -/
lemma pcfLG2_neg_ser_B (M : ℕ) (u t : ℝ) (hu : u ≠ 0) :
    pcfLG2_ser pcfLG2_negB (M+1) u t = pcfLG2_ser pcfLG_hatA (M+1) u t -
      pcfLG_A t * pcfLG_A1 t / u * pcfLG2_ser pcfLG_hatA M u t -
      pcfLG_A t ^ 2 / u * pcfLG2_ser pcfLG_hatAd M u t := by
  induction M with
  | zero =>
    simp [pcfLG2_ser, pcfLG2_negB, pcfLG_hatA_zero]
  | succ M ih =>
    simp only [pcfLG2_ser] at ih ⊢
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (M+1), Finset.sum_range_succ _ M,
      Finset.sum_range_succ _ M]
    simp only [pcfLG2_negB, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    field_simp
    ring

/-- Uniform bounds on `[c, ∞)`, `c > 1`, for `|AA'|`, `A²` and `|A_s'|`. -/
lemma pcfLG2_neg_bounds {c : ℝ} (hc : 1 < c) : ∃ Q1 Q2 : ℝ, 0 ≤ Q1 ∧ 0 ≤ Q2 ∧ ∀ t, c ≤ t →
    |pcfLG_A t * pcfLG_A1 t| ≤ Q1 ∧ pcfLG_A t ^ 2 ≤ Q2 := by
  obtain ⟨K1, hK1, h1⟩ := pcfLG_poly_rpow_bound (C (1/2:ℝ) * X) (d := 1) (by compute_degree)
    (e := 3/2) (by norm_num) hc
  obtain ⟨K2, hK2, h2⟩ := pcfLG_poly_rpow_bound (1 : Polynomial ℝ) (d := 0) (by simp)
    (e := 1/2) (by norm_num) hc
  refine ⟨K1, K2, hK1, hK2, fun t ht => ⟨?_, ?_⟩⟩
  · have ht1 : 1 < t := lt_of_lt_of_le hc ht
    have := h1 t ht
    have hp : t ^ ((1:ℕ) - 2*(3/2:ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by norm_num)
    rw [pcfLG2_neg_A_mul_A1 ht1]
    simp only [eval_mul, eval_C, eval_X] at this
    rw [show -(t/2) * (t^2-1) ^ (-(3/2):ℝ) = -(1/2 * t * (t^2-1) ^ (-(3/2):ℝ)) by ring, abs_neg]
    nlinarith
  · have ht1 : 1 < t := lt_of_lt_of_le hc ht
    have := h2 t ht
    have hp : t ^ ((0:ℕ) - 2*(1/2:ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by norm_num)
    rw [pcfLG2_neg_A_sq ht1]
    simp only [eval_one, one_mul] at this
    have := le_abs_self ((t^2-1) ^ (-(1/2):ℝ))
    nlinarith

/-- `A_s'` is bounded on `[c, ∞)`, `c > 1`. -/
lemma pcfLG2_neg_bound_hatAd (s : ℕ) {c : ℝ} (hc : 1 < c) : ∃ K, 0 ≤ K ∧ ∀ t, c ≤ t →
    |pcfLG_hatAd s t| ≤ K := by
  rcases s with _ | m
  · exact ⟨0, le_rfl, fun t _ => by simp [pcfLG_hatAd, pcfOlverPair]⟩
  · obtain ⟨K, hK, hb⟩ := pcfLG_poly_rpow_bound (pcfOlverPair (m+1)).2 (d := 3*m+2)
      (pcfLG_natDegree_olverPair_snd m) (e := (3*((m+1:ℕ):ℝ)+2)/2) (by positivity) hc
    refine ⟨K, hK, fun t ht => ?_⟩
    have := hb t ht
    have hp : t ^ (((3*m+2:ℕ):ℝ) - 2*((3*((m+1:ℕ):ℝ)+2)/2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by push_cast; linarith)
    have h0 : 0 ≤ t ^ (((3*m+2:ℕ):ℝ) - 2*((3*((m+1:ℕ):ℝ)+2)/2)) :=
      Real.rpow_nonneg (by linarith) _
    unfold pcfLG_hatAd
    calc _ ≤ K * t ^ (((3*m+2:ℕ):ℝ) - 2*((3*((m+1:ℕ):ℝ)+2)/2)) := by simpa using this
      _ ≤ K * 1 := by gcongr
      _ = K := mul_one K

/-- The complex denominator `G (t²-1)^{1/4} e^{-μ²ξ}` in real form, `t > 1`. -/
lemma pcfLG2_neg_denom'_eq (μ : ℝ) {t : ℝ} (ht : 1 < t) (G : ℂ) :
    G * ((t:ℂ)^2-1)^(1/4:ℂ) * cexp (-(μ:ℂ)^2 * (pcfXi t : ℂ)) =
      G * (((pcfLG_A t)⁻¹ * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ) := by
  have hy : 0 < t^2-1 := by nlinarith
  have e1 : ((t:ℂ)^2-1)^(1/4:ℂ) = (((t^2-1) ^ (1/4:ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hy.le]; push_cast; rfl
  rw [e1, pcfLG_A, show (-1/4:ℝ) = -(1/4) by norm_num, Real.rpow_neg hy.le, inv_inv]
  push_cast
  ring_nf

/-- The series of `pcfOlverB` is the real series of `pcfLG2_negB`, `t > 1`. -/
lemma pcfLG2_neg_sum_olverB_eq (N : ℕ) (μ : ℝ) {t : ℝ} (ht : 1 < t) :
    ∑ s ∈ Finset.range N, pcfOlverB s t / (μ:ℂ)^(2*s) =
      (pcfLG2_ser pcfLG2_negB N (μ^2) t : ℂ) := by
  rw [pcfLG2_ser]; push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pcfLG2_neg_olverB_eq s ht, pow_mul]

/-- The `U`-expansion of DLMF 12.10.3 with the normalizer `h(μ)/Φ(μ²)`, `Φ` a Borel sum of
`∑ c_s u^{-s}`. -/
lemma pcfLG2_neg_U_expansion {Φ : ℝ → ℝ} (hΦ : ∀ N : ℕ, (fun u : ℝ => Φ u - ∑ s ∈ Finset.range N, pcfLG_c s / u^s) =O[atTop]
      (fun u : ℝ => (u^N)⁻¹)) {μ₁ : ℝ} (hΦb : ∀ μ, μ₁ ≤ μ → 1/2 ≤ Φ (μ^2) ∧ Φ (μ^2) ≤ 2)
    {δ : ℝ} (hδ : 0 < δ) :
    HasCylinderUniformExpansion (fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2)/((pcfH μ / (Φ (μ^2) : ℂ))*exp (-μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ))) (fun s t => pcfOlverA s t) (Ici (1+δ)) := by
  -- the expansion of `U`
  refine pcfLG2_expansion_of_one_le (fun t => by
    simp [pcfOlverA, pcfOlverU, pcfOlverPair]) fun N hN => ?_
  obtain ⟨C, μ₀, hμ₀, hC, hcore⟩ := pcfLG_core hδ hN
  obtain ⟨B, μ₂, hB, hμ₂, hb⟩ := pcfLG_borel_bound hΦ N
  refine IsBigO.of_bound (4*C + 3*B) (pcfLG_eventually_uniform (max μ₀ (max μ₁ μ₂))
    fun μ hμ t ht => ?_)
  have hμ0 : 0 < μ := by linarith [le_max_left μ₀ (max μ₁ μ₂)]
  have ht1 : 1 < t := by have : 1 + δ ≤ t := ht; linarith
  obtain ⟨hS, hct⟩ := hcore μ ((le_max_left _ _).trans hμ)
  obtain ⟨hX, hser⟩ := hct t ht
  obtain ⟨hΦl, hΦu⟩ := hΦb μ ((le_max_left _ _).trans ((le_max_right _ _).trans hμ))
  have hbo := hb μ ((le_max_right _ _).trans ((le_max_right _ _).trans hμ))
  have hh0 : pcfH μ ≠ 0 := by rw [pcfLG_pcfH_eq hμ0]; exact_mod_cast (pcfLG_h_pos hμ0).ne'
  have hSpos : 1/2 ≤ pcfLG_S N (μ^2) := by linarith [(abs_le.1 hS).1]
  have hS0 : (pcfLG_S N (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < _).ne'
  have hΦ0 : (Φ (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < Φ (μ^2)).ne'
  have hAe : ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (pcfLG_A_pos ht1) (Real.exp_pos _)).ne'
  rw [pcfLG_denom_eq ht1, pcfLG_sum_olverA_eq N μ ht1, pcfLG_norm_zpow hμ0]
  set X := pcfU (-μ^2/2) (μ*t*Real.sqrt 2) * (pcfLG_S N (μ^2) : ℂ) /
    (pcfH μ * ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ)) with hXdef
  have hF : pcfU (-μ^2/2) (μ*t*Real.sqrt 2) / (pcfH μ / (Φ (μ^2) : ℂ) *
      ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ)) - (pcfLG_ser N (μ^2) t : ℂ) =
      (Φ (μ^2) / pcfLG_S N (μ^2) : ℂ) * (X - pcfLG_ser N (μ^2) t) +
      (((Φ (μ^2) - pcfLG_S N (μ^2)) / pcfLG_S N (μ^2) : ℝ) : ℂ) * (pcfLG_ser N (μ^2) t : ℂ) := by
    rw [hXdef]; push_cast; field_simp; ring
  rw [hF]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0:ℝ) < pcfLG_S N (μ^2))]
  have hn1 : ‖(Φ (μ^2) / pcfLG_S N (μ^2) : ℂ)‖ ≤ 4 := by
    rw [show (Φ (μ^2) / pcfLG_S N (μ^2) : ℂ) = ((Φ (μ^2) / pcfLG_S N (μ^2) : ℝ) : ℂ) by
      push_cast; rfl, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by linarith : (0:ℝ) < Φ (μ^2)), abs_of_pos (by linarith : (0:ℝ) < _),
      div_le_iff₀ (by linarith)]
    linarith
  have hp : 0 < (μ^2)^N := by positivity
  have h2 : |Φ (μ^2) - pcfLG_S N (μ^2)| / pcfLG_S N (μ^2) * |pcfLG_ser N (μ^2) t| ≤
      3*B / (μ^2)^N := by
    calc |Φ (μ^2) - pcfLG_S N (μ^2)| / pcfLG_S N (μ^2) * |pcfLG_ser N (μ^2) t|
        ≤ (B / (μ^2)^N) / (1/2) * (3/2) := by
          gcongr
      _ = 3*B / (μ^2)^N := by ring
  calc ‖(Φ (μ^2) / pcfLG_S N (μ^2) : ℂ)‖ * ‖X - (pcfLG_ser N (μ^2) t : ℂ)‖ +
        |Φ (μ^2) - pcfLG_S N (μ^2)| / pcfLG_S N (μ^2) * |pcfLG_ser N (μ^2) t|
      ≤ 4 * (C / (μ^2)^N) + 3*B / (μ^2)^N := by
        gcongr
  _ = (4*C + 3*B) * ((μ^2)^N)⁻¹ := by ring

/-- The `U'`-expansion of DLMF 12.10.4 with the normalizer `h(μ)/Φ(μ²)`, `Φ` a Borel sum of
`∑ c_s u^{-s}`. -/
lemma pcfLG2_neg_UDeriv_expansion {Φ : ℝ → ℝ} (hΦ : ∀ N : ℕ, (fun u : ℝ => Φ u - ∑ s ∈ Finset.range N, pcfLG_c s / u^s) =O[atTop]
      (fun u : ℝ => (u^N)⁻¹)) {μ₁ : ℝ} (hΦb : ∀ μ, μ₁ ≤ μ → 1/2 ≤ Φ (μ^2) ∧ Φ (μ^2) ≤ 2)
    {δ : ℝ} (hδ : 0 < δ) :
    HasCylinderUniformExpansion (fun μ t => pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2)/(-(μ:ℂ)/Real.sqrt 2*(pcfH μ / (Φ (μ^2) : ℂ))*(t^2-1:ℂ)^(1/4:ℂ)*exp (-μ^2*pcfXi t))) (fun s t => pcfOlverB s t) (Ici (1+δ)) := by
  have hΦ' := hΦ
  -- the expansion of `U'`
  refine pcfLG2_expansion_of_one_le (fun t => by
    simp [pcfOlverB, pcfOlverV]) fun N hN => ?_
  obtain ⟨M, rfl⟩ : ∃ M, N = M+1 := ⟨N-1, by omega⟩
  set c : ℝ := 1 + δ with hcdef
  have hc : 1 < c := by linarith
  obtain ⟨C, μ₀, hC, hμ₀, hcore⟩ := pcfLG2_neg_core hδ hN
  obtain ⟨B, μ₂, hB, hμ₂, hb⟩ := pcfLG2_borel_bound pcfLG_c hΦ' (M+1)
  choose Kd hKd0 hKd' using fun s => pcfLG2_neg_bound_hatAd s hc
  choose K hK0 hK using fun s => pcfLG_bound_hatA s hc
  obtain ⟨Q1, Q2, hQ1, hQ2, hQ⟩ := pcfLG2_neg_bounds hc
  set KW := 3/2 + Q1 * (∑ s ∈ Finset.range M, K s) + Q2 * ∑ s ∈ Finset.range M, Kd s with hKW
  refine IsBigO.of_bound (4*((3 + Q1)*C + Q1 * K M + Q2 * Kd M) + 2*B*KW)
    (pcfLG_eventually_uniform (max μ₀ (max μ₁ μ₂)) fun μ hμ t ht => ?_)
  have ht' : c ≤ t := ht
  have ht1 : 1 < t := by linarith
  have hμ0 : 0 < μ := by linarith [le_max_left μ₀ (max μ₁ μ₂)]
  have hμ1 : 1 ≤ μ := by linarith [le_max_left μ₀ (max μ₁ μ₂)]
  have hu1 : 1 ≤ μ^2 := by nlinarith
  have hu0 : 0 < μ^2 := by positivity
  obtain ⟨hL, hct⟩ := hcore μ ((le_max_left _ _).trans hμ)
  obtain ⟨hS, e, e', he, he', -, hU'⟩ := hct t ht'
  obtain ⟨hΦl, hΦu⟩ := hΦb μ ((le_max_left _ _).trans ((le_max_right _ _).trans hμ))
  have hbo := hb μ ((le_max_right _ _).trans ((le_max_right _ _).trans hμ))
  rw [Nat.add_sub_cancel] at he'
  set L := pcfLG2_ser (fun s _ => pcfLG_c s) (M+1) (μ^2) 0
  set Sa := pcfLG2_ser pcfLG_hatA (M+1) (μ^2) t
  set Sd := pcfLG2_ser pcfLG_hatAd (M+1) (μ^2) t
  set a := pcfLG_A t with ha
  set a1 := pcfLG_A1 t with ha1
  set Ex := Real.exp (-(μ^2 * pcfXi t)) with hEx
  set W := pcfLG2_ser pcfLG2_negB (M+1) (μ^2) t with hWdef
  set H : ℝ := pcfLG_h μ with hH
  set Y := (Sa + e) - a*a1*(Sa+e)/μ^2 - a^2*(Sd+e')/μ^2 with hY
  have hLpos : 1/2 ≤ L := by linarith [(abs_le.1 hL).1]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < L).ne'
  have hΦ0 : (Φ (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < Φ (μ^2)).ne'
  have hh := pcfLG_h_pos hμ0
  have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have h1 : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ0.ne'
  have ha0 : 0 < a := pcfLG_A_pos ht1
  have h3 : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have h4 : (Ex : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
  rw [pcfLG2_neg_denom'_eq μ ht1, pcfLG2_neg_sum_olverB_eq _ μ ht1, pcfLG_norm_zpow hμ0,
    pcfLG_pcfH_eq hμ0]
  rw [pcfLG_pcfH_eq hμ0] at hU'
  have hU'' : pcfUDeriv (-(μ:ℂ)^2/2) ((μ:ℂ)*t*Real.sqrt 2) = (H:ℂ)/(L:ℂ) *
      ((Ex * ((a1 - μ^2 * a⁻¹) * (Sa + e) + a * (Sd + e')) : ℝ) : ℂ) / ((μ:ℂ)*Real.sqrt 2) := by
    rw [← hU']; field_simp
  rw [hU'']
  have hF : (H:ℂ)/(L:ℂ) * ((Ex * ((a1 - μ^2 * a⁻¹) * (Sa + e) + a * (Sd + e')) : ℝ) : ℂ) /
      ((μ:ℂ)*Real.sqrt 2) / (-(μ:ℂ)/Real.sqrt 2 * ((H:ℂ) / (Φ (μ^2) : ℂ)) *
        ((a⁻¹ * Ex : ℝ) : ℂ)) - (W:ℂ) =
      ((Φ (μ^2) / L * (Y - W) + (Φ (μ^2) - L) / L * W : ℝ) : ℂ) := by
    simp only [hY]
    push_cast
    field_simp
    ring
  rw [hF, Complex.norm_real, Real.norm_eq_abs]
  -- bounds
  have hr : 0 < (μ^2)^(M+1) := by positivity
  have hrM : 0 < (μ^2)^M := by positivity
  have hrr : (μ^2)^(M+1) = (μ^2)^M * μ^2 := pow_succ _ _
  have hW : W = Sa - a*a1/μ^2 * pcfLG2_ser pcfLG_hatA M (μ^2) t -
      a^2/μ^2 * pcfLG2_ser pcfLG_hatAd M (μ^2) t := pcfLG2_neg_ser_B M (μ^2) t hu0.ne'
  have hSa : Sa = pcfLG2_ser pcfLG_hatA M (μ^2) t + pcfLG_hatA M t / (μ^2)^M := by
    simp only [Sa, pcfLG2_ser, Finset.sum_range_succ]
  have hSd : Sd = pcfLG2_ser pcfLG_hatAd M (μ^2) t + pcfLG_hatAd M t / (μ^2)^M := by
    simp only [Sd, pcfLG2_ser, Finset.sum_range_succ]
  have hD : Y - W = e - a*a1*e/μ^2 - a^2*e'/μ^2 - a*a1*pcfLG_hatA M t/(μ^2)^(M+1) -
      a^2*pcfLG_hatAd M t/(μ^2)^(M+1) := by
    rw [hW, hY, hSa, hSd, hrr]; field_simp; ring
  obtain ⟨haa1, ha2⟩ := hQ t ht'
  have ha2' : 0 ≤ a^2 := sq_nonneg a
  have hCu : 0 ≤ C/(μ^2)^(M+1) := by positivity
  have b2 : |a*a1*e/μ^2| ≤ Q1*C/(μ^2)^(M+1) := by
    rw [abs_div, abs_mul, abs_of_pos hu0, div_le_iff₀ hu0]
    calc |a*a1| * |e| ≤ Q1 * (C/(μ^2)^(M+1)) := by gcongr
      _ ≤ Q1*C/(μ^2)^(M+1) * μ^2 := by
        rw [mul_div_assoc]; nlinarith [mul_nonneg hQ1 hCu]
  have b3 : |a^2*e'/μ^2| ≤ 2*C/(μ^2)^(M+1) := by
    rw [abs_div, abs_of_pos hu0, hrr, div_le_iff₀ hu0]
    calc |a^2*e'| ≤ 2*C/(μ^2)^M := he'
      _ = 2*C/((μ^2)^M * μ^2) * μ^2 := by field_simp
  have b4 : |a*a1*pcfLG_hatA M t/(μ^2)^(M+1)| ≤ Q1 * K M/(μ^2)^(M+1) := by
    rw [abs_div, abs_mul, abs_of_pos hr]
    gcongr
    exact hK M t ht'
  have b5 : |a^2*pcfLG_hatAd M t/(μ^2)^(M+1)| ≤ Q2 * Kd M/(μ^2)^(M+1) := by
    rw [abs_div, abs_mul, abs_of_pos hr, abs_of_nonneg ha2']
    gcongr
    exact hKd' M t ht'
  have hDb : |Y - W| ≤ ((3 + Q1)*C + Q1 * K M + Q2 * Kd M)/(μ^2)^(M+1) := by
    rw [hD]
    have e1 := abs_le.1 he
    have e2 := abs_le.1 b2
    have e3 := abs_le.1 b3
    have e4 := abs_le.1 b4
    have e5 := abs_le.1 b5
    have : ((3 + Q1)*C + Q1 * K M + Q2 * Kd M)/(μ^2)^(M+1) = C/(μ^2)^(M+1) +
        Q1*C/(μ^2)^(M+1) + 2*C/(μ^2)^(M+1) + Q1 * K M/(μ^2)^(M+1) +
        Q2 * Kd M/(μ^2)^(M+1) := by ring
    rw [this]
    refine abs_le.2 ⟨by linarith only [e1.1, e2.2, e3.2, e4.2, e5.2],
      by linarith only [e1.2, e2.1, e3.1, e4.1, e5.1]⟩
  have hWb : |W| ≤ KW := by
    rw [hW]
    have hSa3 : |Sa| ≤ 3/2 := abs_le.2 ⟨by linarith [(abs_le.1 hS).1], by linarith [(abs_le.1 hS).2]⟩
    have c1 : |a*a1/μ^2 * pcfLG2_ser pcfLG_hatA M (μ^2) t| ≤ Q1 * ∑ s ∈ Finset.range M, K s := by
      rw [abs_mul, abs_div, abs_of_pos hu0]
      have : |pcfLG2_ser pcfLG_hatA M (μ^2) t| ≤ ∑ s ∈ Finset.range M, K s := by
        unfold pcfLG2_ser
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        rw [abs_div, abs_of_pos (pow_pos hu0 s)]
        exact (div_le_self (abs_nonneg _) (one_le_pow₀ hu1)).trans (hK s t ht')
      have hq : |a*a1|/μ^2 ≤ Q1 := by
        rw [div_le_iff₀ hu0]; exact haa1.trans (le_mul_of_one_le_right hQ1 hu1)
      exact mul_le_mul hq this (abs_nonneg _) hQ1
    have c2 : |a^2/μ^2 * pcfLG2_ser pcfLG_hatAd M (μ^2) t| ≤ Q2 * ∑ s ∈ Finset.range M, Kd s := by
      rw [abs_mul, abs_div, abs_of_pos hu0, abs_of_nonneg ha2']
      have : |pcfLG2_ser pcfLG_hatAd M (μ^2) t| ≤ ∑ s ∈ Finset.range M, Kd s := by
        unfold pcfLG2_ser
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        rw [abs_div, abs_of_pos (pow_pos hu0 s)]
        exact (div_le_self (abs_nonneg _) (one_le_pow₀ hu1)).trans (hKd' s t ht')
      have hq : a^2/μ^2 ≤ Q2 := by
        rw [div_le_iff₀ hu0]; exact ha2.trans (le_mul_of_one_le_right hQ2 hu1)
      exact mul_le_mul hq this (abs_nonneg _) hQ2
    have f1 := abs_le.1 hSa3
    have f2 := abs_le.1 c1
    have f3 := abs_le.1 c2
    exact abs_le.2 ⟨by linarith only [f1.1, f2.2, f3.2, hKW], by linarith only [f1.2, f2.1, f3.1, hKW]⟩
  have hLp : 0 < L := by linarith only [hLpos]
  have hΦp : 0 < Φ (μ^2) := by linarith only [hΦl]
  have hq1 : Φ (μ^2) / L ≤ 4 := by rw [div_le_iff₀ hLp]; linarith only [hLpos, hΦu]
  have hq2 : |Φ (μ^2) - L| / L ≤ 2*B/(μ^2)^(M+1) := by
    rw [div_le_iff₀ hLp]
    calc |Φ (μ^2) - L| ≤ B/(μ^2)^(M+1) := hbo
      _ = 2*B/(μ^2)^(M+1) * (1/2) := by ring
      _ ≤ 2*B/(μ^2)^(M+1) * L := by gcongr
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos hLp, abs_of_pos hΦp]
  calc Φ (μ^2) / L * |Y - W| + |Φ (μ^2) - L| / L * |W|
      ≤ 4 * (((3 + Q1)*C + Q1 * K M + Q2 * Kd M)/(μ^2)^(M+1)) +
          2*B/(μ^2)^(M+1) * KW := by
        gcongr
    _ = (4*((3 + Q1)*C + Q1 * K M + Q2 * Kd M) + 2*B*KW) * ((μ^2)^(M+1))⁻¹ := by ring

/-- **DLMF 12.10.3 and 12.10.4 with the normalizer of DLMF 12.10.14**: Olver's uniform
expansions of `U(-½μ², μt√2)` and of its derivative for `t ≥ 1+δ`, with one normalizer `g`
satisfying `IsCylinderGNormalizer`. These are the `U`- and `U'`-parts of
`pcf_negative_parameter_uniform`. The `U'`-expansion follows from the recessive
Liouville–Green core `pcfLG2_core` (via `pcfLG2_neg_core`), with
`B_s = A_s - AA'A_{s-1} - A²A_{s-1}'` (DLMF 12.10.13). -/
@[dlmf 12.10.E3, dlmf 12.10.E4, dlmf 12.10.E14]
theorem pcf_negative_parameter_uniform_U_UDeriv :
    ∃ g : ℝ → ℂ, IsCylinderGNormalizer g ∧ ∀ δ : ℝ, 0 < δ → HasCylinderUniformExpansion (fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2)/(g μ*exp (-μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ))) (fun s t => pcfOlverA s t) (Ici (1+δ)) ∧ HasCylinderUniformExpansion (fun μ t => pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2)/(-(μ:ℂ)/Real.sqrt 2*g μ*(t^2-1:ℂ)^(1/4:ℂ)*exp (-μ^2*pcfXi t))) (fun s t => pcfOlverB s t) (Ici (1+δ)) := by
  obtain ⟨Φ, hΦ⟩ := pcfLG_exists_asymptotic pcfLG_c
  have hΦ' : ∀ N : ℕ, (fun u : ℝ => Φ u - ∑ s ∈ Finset.range N, pcfLG_c s / u^s) =O[atTop]
      (fun u : ℝ => (u^N)⁻¹) := hΦ
  -- `Φ(μ²)` stays near `1`
  have hΦ1 : ∃ μ₁ : ℝ, 1 ≤ μ₁ ∧ ∀ μ, μ₁ ≤ μ → 1/2 ≤ Φ (μ^2) ∧ Φ (μ^2) ≤ 2 := by
    obtain ⟨B, μ₁, hB, hμ₁, hb⟩ := pcfLG_borel_bound hΦ 1
    refine ⟨max μ₁ (2*B+1), le_trans hμ₁ (le_max_left _ _), fun μ hμ => ?_⟩
    have hμ1 : μ₁ ≤ μ := (le_max_left _ _).trans hμ
    have h := hb μ hμ1
    have hS : pcfLG_S 1 (μ^2) = 1 := by simp [pcfLG_S, pcfLG_c_zero]
    rw [hS, pow_one] at h
    have hμB : 2*B+1 ≤ μ := (le_max_right _ _).trans hμ
    have hμ2 : 2*B ≤ μ^2 := by nlinarith
    have : B / μ^2 ≤ 1/2 := by rw [div_le_iff₀ (by nlinarith)]; linarith
    have := abs_le.1 (h.trans this)
    constructor <;> linarith [this.1, this.2]
  obtain ⟨μ₁, hμ₁, hΦb⟩ := hΦ1
  set g : ℝ → ℂ := fun μ => pcfH μ / (Φ (μ^2) : ℂ) with hg
  -- `g/h · ∑ c_s μ^{-2s} ∼ 1`
  have hgN : ∀ N : ℕ, (fun μ : ℝ => g μ / pcfH μ *
      (∑ s ∈ Finset.range N, (pcfLG_c s : ℂ) / (μ:ℂ)^(2*s)) - 1) =O[atTop]
      (fun μ : ℝ => (μ:ℂ)^(-(2*N:ℤ))) := by
    intro N
    obtain ⟨B, μ₂, hB, hμ₂, hb⟩ := pcfLG_borel_bound hΦ N
    refine IsBigO.of_bound (2*B) ?_
    filter_upwards [eventually_ge_atTop (max μ₁ μ₂)] with μ hμ
    have hμ0 : 0 < μ := by linarith [le_max_left μ₁ μ₂]
    obtain ⟨hΦl, -⟩ := hΦb μ ((le_max_left _ _).trans hμ)
    have hh0 : pcfH μ ≠ 0 := by rw [pcfLG_pcfH_eq hμ0]; exact_mod_cast (pcfLG_h_pos hμ0).ne'
    have hΦ0 : (Φ (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < Φ (μ^2)).ne'
    rw [pcfLG_sum_c_eq, pcfLG_norm_zpow hμ0]
    have heq : pcfH μ / (Φ (μ^2) : ℂ) / pcfH μ * (pcfLG_S N (μ^2) : ℂ) - 1 =
        (((pcfLG_S N (μ^2) - Φ (μ^2)) / Φ (μ^2) : ℝ) : ℂ) := by
      push_cast; field_simp
    simp only [g]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (show (0:ℝ) < Φ (μ^2) by linarith), abs_sub_comm]
    have := hb μ ((le_max_right _ _).trans hμ)
    rw [div_le_iff₀ (by linarith)]
    calc |Φ (μ^2) - pcfLG_S N (μ^2)| ≤ B / (μ^2)^N := this
      _ = 2*B * ((μ^2)^N)⁻¹ * (1/2) := by ring
      _ ≤ 2*B * ((μ^2)^N)⁻¹ * Φ (μ^2) := by gcongr
  refine ⟨g, fun N => ?_, fun δ hδ => ⟨pcfLG2_neg_U_expansion hΦ hΦb hδ,
    pcfLG2_neg_UDeriv_expansion hΦ hΦb hδ⟩⟩
  · -- the normalizer
    have h := pcfLG2_recip_sq (G := fun μ => g μ / pcfH μ) (a := fun s => (pcfLG_c s : ℂ))
      pcfLG2_c_mul_d (fun M => hgN M) (N+1)
    have hγ0 : pcfGammaCoeff 0 = 1 := pcfGammaCoeff_initial.1
    refine h.congr' ?_ (Eventually.of_forall fun μ => by push_cast; ring_nf)
    filter_upwards [eventually_ne_atTop 0] with μ hμ
    have hμ' : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ
    rw [Finset.sum_range_succ']
    simp only [pcfLG2_delta, hγ0, ite_true, Nat.succ_ne_zero, ite_false, pow_zero, mul_zero,
      zero_add, div_one, Finset.mul_sum]
    have : ∀ j : ℕ, 1/2 * (pcfGammaCoeff (j+1) * 2^(j+1)) / (μ:ℂ)^(2*(j+1)) =
        1/2 * (pcfGammaCoeff (j+1) / ((μ:ℂ)^2/2)^(j+1)) := fun j => by
      rw [div_pow, pow_mul]; field_simp
    simp only [this]
    ring

end DLMF.Confluent

end
