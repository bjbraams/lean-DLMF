/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.LogSeries

/-!
# Kummer `M` and Tricomi `U`: remaining basic properties (DLMF §13.2)

Olver's regularized function `𝐌(a,b,z)` is Mathlib's `regularizedHGFun {a} {b}`.
The series `kummerM` is entire in `z` at regular denominator parameters; `kummerU`
uses the connection formula 13.2.42 and parameter limits at integer `b`.
The Kummer transformation includes integer parameters by parameter continuity.
The integer-denominator logarithmic expansion and its small-argument consequences follow
from termwise differentiation of the regularized series. Complex powers use the principal branch
on the slit plane. Numerically satisfactory pairs (13.2.24–13.2.26) are recorded as Wronskian
identities on the indicated argument sectors.

The connection formula 13.2.41 is proved for every `b`, in regularized form, as
`regularizedHGFun_eq_kummerU_connection`, from 13.2.42, Kummer's transformation 13.2.39 and the
reflection formula, then by continuity in `b`. The Wronskians 13.2.24, 13.2.25, 13.2.35, 13.2.37
and 13.2.38 that follow from it are in `DLMF.Confluent.ConnectionWronskians`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Wronskian `f g' - g f'`. -/
def wronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * deriv g z - g z * deriv f z

@[dlmf 13.2.E5]
theorem regularizedHGFun_of_neg_nat (a : ℂ) (n : ℕ) (z : ℂ) :
    regularizedHGFun {a} {(-(n : ℂ))} z =
      poch a (n + 1) / (n + 1).factorial * z ^ (n + 1) *
        kummerM (a + n + 1) (n + 2) z := by
  rw [regularizedHGFun_eq_tsum]
  have hs : Summable fun k : ℕ => regularizedHGFunCoeff {a} {(-(n : ℂ))} k * z ^ k := by
    have hr : (regularizedHGFunSeries {a} {(-(n : ℂ))}).radius = ⊤ :=
      radius_regularizedHGFunSeries_eq_top (by simp)
    have hp : HasFPowerSeriesOnBall (regularizedHGFun {a} {(-(n : ℂ))})
        (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff {a} {(-(n : ℂ))})) 0 ⊤ := by
      change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {(-(n : ℂ))}).sum
        (regularizedHGFunSeries {a} {(-(n : ℂ))}) 0 ⊤
      simpa only [hr] using
        (regularizedHGFunSeries {a} {(-(n : ℂ))}).hasFPowerSeriesOnBall (by rw [hr]; simp)
    exact (hp.hasSum_mul_pow (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)).summable
  rw [← hs.sum_add_tsum_nat_add (n + 1)]
  have hzero : ∀ k ∈ Finset.range (n + 1),
      regularizedHGFunCoeff {a} {(-(n : ℂ))} k * z ^ k = 0 := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : (-(n : ℂ) + k) = -((n - k : ℕ) : ℂ) := by push_cast [Nat.cast_sub hk']; ring
    rw [regularizedHGFunCoeff_singleton, this, Complex.Gamma_neg_nat_eq_zero, mul_zero, div_zero,
      zero_mul]
  rw [Finset.sum_eq_zero hzero, zero_add]
  have hpole : ∀ k : ℕ, ((n : ℂ) + 2) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.re_ofNat, Complex.neg_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hF := (hasFPowerSeriesOnBall_kummerM (a := a + n + 1) hpole).hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)
  rw [← hF.tsum_eq, ← tsum_mul_left]
  congr 1
  funext j
  have hΓ : Gamma ((n : ℂ) + 2 + j) = (ascPochhammer ℂ j).eval ((n : ℂ) + 2) * Gamma ((n : ℂ) + 2) := by
    rw [← Gamma_add_nat_div_Gamma_eq (n := j) ((n : ℂ) + 2) hpole]
    field_simp [Gamma_ne_zero hpole]
  have hΓ1 : Gamma ((n : ℂ) + 2 + j) = ((n + 1 + j).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 + j = ((n + 1 + j : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ2 : Gamma ((n : ℂ) + 2) = ((n + 1).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ3 : Gamma (-(n : ℂ) + ((j + (n + 1) : ℕ) : ℂ)) = (j.factorial : ℂ) := by
    rw [show -(n : ℂ) + ((j + (n + 1) : ℕ) : ℂ) = (j : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hp : (ascPochhammer ℂ j).eval ((n : ℂ) + 2) ≠ 0 := poch_ne_zero_of_not_neg_nat hpole j
  have hf1 : ((n + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : ((n + 1 + j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hΓ1, hΓ2] at hΓ
  rw [regularizedHGFunCoeff_singleton, hΓ3]
  simp only [kummerMCoeff, poch]
  rw [add_comm j (n + 1), DLMF.Hypergeometric.ascPochhammer_eval_add a,
    show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring, pow_add]
  field_simp
  rw [hΓ]
  ring

/-! ### Existence of Tricomi's function at integer second parameters -/

/-- The entire numerator of Tricomi's connection formula:
`U(a,c,z) = π/sin(πc) · tricomiD a c z` for noninteger `c`. -/
def tricomiD (a c z : ℂ) : ℂ :=
  regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
    z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹

/-- A noninteger complex number is not a nonpositive integer. -/
theorem not_neg_nat_of_mem_integerComplement {c : ℂ} (hc : c ∈ integerComplement) :
    ∀ k : ℕ, c ≠ -(k : ℂ) := fun k h => hc ⟨-k, by rw [h]; push_cast; ring⟩

/-- A complex number different from every integer lies in `ℂ \ ℤ`. -/
theorem mem_integerComplement_of_forall {c : ℂ} (hc : ∀ k : ℤ, c ≠ k) : c ∈ integerComplement :=
  fun ⟨k, hk⟩ => hc k hk.symm

/-- A point of `ℂ \ ℤ` differs from every integer. -/
theorem forall_of_mem_integerComplement {c : ℂ} (hc : c ∈ integerComplement) : ∀ k : ℤ, c ≠ k :=
  fun k hk => hc ⟨k, hk.symm⟩

/-- For noninteger `c`, the connection formula equals `π / sin(πc)` times the regularized
combination `tricomiD a c z` (DLMF 13.2.42 with the reflection formula). -/
theorem kummerUConnection_eq_tricomiD {a c z : ℂ} (hc : c ∈ integerComplement) :
    kummerUConnection a c z = π / sin (π * c) * tricomiD a c z := by
  have hc0 := not_neg_nat_of_mem_integerComplement hc
  have hc2 : 2 - c ∈ integerComplement := by
    have := (add_intCast_mem_integerComplement (x := -c) 2).mpr (by
      intro ⟨k, hk⟩; exact hc ⟨-k, by push_cast; linear_combination -hk⟩)
    simpa [sub_eq_neg_add, add_comm] using this
  have hsin : sin (π * c) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    exact hc ⟨k, by
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hk; linear_combination -hk⟩
  have h1 := Gamma_mul_Gamma_one_sub c
  have h2 := Gamma_mul_Gamma_one_sub (c - 1)
  rw [show 1 - (c - 1) = 2 - c by ring, show (π : ℂ) * (c - 1) = π * c - π by ring,
    Complex.sin_sub_pi] at h2
  unfold kummerUConnection tricomiD
  rw [kummerM_eq_mul_regularizedHGFun hc0,
    kummerM_eq_mul_regularizedHGFun (not_neg_nat_of_mem_integerComplement hc2)]
  rw [div_eq_mul_inv (Gamma (1 - c)), div_eq_mul_inv (Gamma (c - 1))]
  calc Gamma (1 - c) * (Gamma (a - c + 1))⁻¹ * (Gamma c * regularizedHGFun {a} {c} z) +
        Gamma (c - 1) * (Gamma a)⁻¹ * z ^ (1 - c) *
          (Gamma (2 - c) * regularizedHGFun {a - c + 1} {2 - c} z)
      = (Gamma c * Gamma (1 - c)) * ((Gamma (a - c + 1))⁻¹ * regularizedHGFun {a} {c} z) +
        (Gamma (c - 1) * Gamma (2 - c)) * ((Gamma a)⁻¹ * z ^ (1 - c) *
          regularizedHGFun {a - c + 1} {2 - c} z) := by ring
    _ = _ := by rw [h1, h2]; field_simp; ring

/-- The numerator vanishes at every integer second parameter. -/
theorem tricomiD_intCast (a z : ℂ) (hz : z ≠ 0) (n : ℤ) : tricomiD a n z = 0 := by
  -- the regularized function at a nonpositive integer denominator
  have hneg : ∀ (x : ℂ) (k : ℕ), regularizedHGFun {x} {(-(k : ℂ))} z =
      poch x (k + 1) * z ^ (k + 1) * regularizedHGFun {x + k + 1} {(k + 2 : ℂ)} z := by
    intro x k
    have hp : ∀ j : ℕ, ((k : ℂ) + 2) ≠ -(j : ℂ) := fun j h => by
      have := congrArg re h; simp at this
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [regularizedHGFun_of_neg_nat, kummerM_eq_mul_regularizedHGFun hp,
      show (k : ℂ) + 2 = ((k + 1 : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
    have hf : (((k + 1).factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  unfold tricomiD
  rcases le_or_gt n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨n.natAbs, by omega⟩
    push_cast
    rw [hneg, DLMF.Hypergeometric.recip_Gamma_eq_poch_mul k a, show 1 - -(k : ℂ) = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
      cpow_natCast, show a - -(k : ℂ) + 1 = a + ((k + 1 : ℕ) : ℂ) by push_cast; ring,
      show 2 - -(k : ℂ) = (k + 2 : ℂ) by ring]
    push_cast
    ring_nf
  · rcases eq_or_lt_of_le (show 1 ≤ n by omega) with h1 | h2
    · subst h1
      norm_num
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 2 := ⟨(n - 2).toNat, by omega⟩
      push_cast
      rw [show (2 : ℂ) - ((k : ℂ) + 2) = -(k : ℂ) by ring, hneg,
        show a - ((k : ℂ) + 2) + 1 + k + 1 = a by ring,
        DLMF.Hypergeometric.recip_Gamma_eq_poch_mul k (a - ((k : ℂ) + 2) + 1),
        show a - ((k : ℂ) + 2) + 1 + ((k + 1 : ℕ) : ℂ) = a by push_cast; ring]
      have hzk : z ^ (1 - ((k : ℂ) + 2)) * z ^ (k + 1) = 1 := by
        rw [show (1 : ℂ) - ((k : ℂ) + 2) = -((k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
          cpow_natCast]
        exact inv_mul_cancel₀ (pow_ne_zero _ hz)
      linear_combination (-(poch (a - (↑k + 2) + 1) (k + 1) * regularizedHGFun {a} {(k + 2 : ℂ)} z *
        (Gamma a)⁻¹)) * hzk

/-- The numerator is entire in the second parameter, for `z ≠ 0`. -/
theorem differentiable_tricomiD (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ (fun c => tricomiD a c z) := by
  unfold tricomiD
  have h1 : Differentiable ℂ (fun c => regularizedHGFun {a} {c} z) :=
    differentiable_regularizedConfluent_comp (differentiable_const a) differentiable_id z
  have h2 : Differentiable ℂ (fun c => regularizedHGFun {a - c + 1} {2 - c} z) :=
    differentiable_regularizedConfluent_comp (by fun_prop) (by fun_prop) z
  have h3 : Differentiable ℂ (fun c : ℂ => (Gamma (a - c + 1))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have h4 : Differentiable ℂ (fun c : ℂ => z ^ (1 - c)) := fun c =>
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hz)
  exact (h1.mul h3).sub ((h4.mul h2).mul_const _)

/-- Every complex `b` is an accumulation point of `ℂ \ ℤ`. -/
theorem integerComplement_nhdsWithin_neBot (b : ℂ) : (𝓝[integerComplement] b).NeBot := by
  have hd : Dense integerComplement :=
    (Set.countable_range (fun k : ℤ => (k : ℂ))).dense_compl ℂ
  exact mem_closure_iff_nhdsWithin_neBot.mp (hd b)

/-- `sin(πc) ≠ 0` for noninteger `c`. -/
theorem sin_pi_mul_ne_zero_of_mem {c : ℂ} (hc : c ∈ integerComplement) : sin (π * c) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro k hk
  exact hc ⟨k, by
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp at hk; linear_combination -hk⟩

/-- **Existence of Tricomi's function at every second parameter**: for `z ≠ 0`, the
connection formula converges along noninteger parameters to `U(a,b,z)`. -/
theorem tendsto_kummerUConnection (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => kummerUConnection a c z) (𝓝[integerComplement] b)
      (𝓝 (kummerU a b z)) := by
  have hD := differentiable_tricomiD a hz
  have hev : (fun c => π / sin (π * c) * tricomiD a c z) =ᶠ[𝓝[integerComplement] b]
      fun c => kummerUConnection a c z :=
    eventually_nhdsWithin_of_forall fun c hc => (kummerUConnection_eq_tricomiD hc).symm
  have := integerComplement_nhdsWithin_neBot b
  by_cases hb : b ∈ integerComplement
  · rw [kummerU_eq_connection a b z (forall_of_mem_integerComplement hb),
      kummerUConnection_eq_tricomiD hb]
    have hc1 : ContinuousAt (fun c : ℂ => sin (π * c)) b :=
      (continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
    have hc2 : ContinuousAt (fun c : ℂ => π / sin (π * c) * tricomiD a c z) b :=
      (continuousAt_const.div hc1 (sin_pi_mul_ne_zero_of_mem hb)).mul (hD b).continuousAt
    exact (hc2.tendsto.mono_left nhdsWithin_le_nhds).congr' hev
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ℂ) = b := by
      by_contra h; exact hb fun ⟨k, hk⟩ => h ⟨k, hk⟩
    set S : ℂ → ℂ := fun c => sin (π * c) with hS
    have hSd : HasDerivAt S (cos (π * n) * π) n := by
      have := ((hasDerivAt_id (n : ℂ)).const_mul (π : ℂ)).csin
      simpa [hS] using this
    have hS0 : S n = 0 := by
      simp only [hS]
      rw [mul_comm]; exact Complex.sin_int_mul_pi n
    have hcos : cos (π * n) ≠ 0 := by
      intro h
      have := Complex.cos_sq_add_sin_sq (π * (n : ℂ))
      simp only [hS] at hS0
      rw [h, hS0] at this
      norm_num at this
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hD0 : tricomiD a n z = 0 := tricomiD_intCast a z hz n
    have hcD : ContinuousAt (dslope (fun c => tricomiD a c z) n) n :=
      continuousAt_dslope_same.mpr (hD n)
    have hcS : ContinuousAt (dslope S n) n := continuousAt_dslope_same.mpr hSd.differentiableAt
    have hSn : dslope S n n ≠ 0 := by
      rw [dslope_same, hSd.deriv]; exact mul_ne_zero hcos hπ
    have hL : Tendsto (fun c => π / sin (π * c) * tricomiD a c z) (𝓝[integerComplement] (n : ℂ))
        (𝓝 (π * dslope (fun c => tricomiD a c z) n n / dslope S n n)) := by
      have ht := ((hcD.const_mul (π : ℂ)).div hcS hSn).tendsto
      refine (ht.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with c hc
      have hcn : c - n ≠ 0 := sub_ne_zero.mpr fun h => hc ⟨n, h.symm⟩
      have e1 := sub_smul_dslope (fun c => tricomiD a c z) (n : ℂ) c
      have e2 := sub_smul_dslope S (n : ℂ) c
      rw [hD0, sub_zero, smul_eq_mul] at e1
      rw [hS0, sub_zero, smul_eq_mul] at e2
      have hsc : sin (π * c) ≠ 0 := sin_pi_mul_ne_zero_of_mem hc
      have hd2 : dslope S n c ≠ 0 := by
        intro h0; apply hsc; simp only [hS] at e2; rw [← e2, h0, mul_zero]
      simp only [hS] at e2 hd2
      rw [← e1, ← e2]
      simp only [Pi.div_apply, hS]
      field_simp
    have hU : kummerU a n z = π * dslope (fun c => tricomiD a c z) n n / dslope S n n := by
      unfold kummerU
      simp only [show ¬ (∀ k : ℤ, (n : ℂ) ≠ k) from fun h => h n rfl, ↓reduceIte]
      exact (hL.congr' hev).limUnder_eq
    rw [hU]
    exact hL.congr' hev

/-- Shifting a noninteger parameter by an integer keeps it noninteger. -/
theorem tendsto_add_intCast_integerComplement (b : ℂ) (k : ℤ) :
    Tendsto (fun c => c + (k : ℂ)) (𝓝[integerComplement] b) (𝓝[integerComplement] (b + k)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun c hc => ?_⟩
  · exact ((continuous_id.add continuous_const).tendsto b).mono_left nhdsWithin_le_nhds
  · exact (add_intCast_mem_integerComplement k).mpr hc

/-- `U(a, c + k, z) → U(a, b + k, z)` along noninteger `c → b`. -/
theorem tendsto_kummerU_add_intCast (a b : ℂ) (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => kummerU a (c + k) z) (𝓝[integerComplement] b)
      (𝓝 (kummerU a (b + k) z)) := by
  refine ((tendsto_kummerUConnection a (b + k) hz).comp
    (tendsto_add_intCast_integerComplement b k)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  simp only [Function.comp_apply]
  exact (kummerU_eq_connection a (c + k) z (forall_of_mem_integerComplement
    ((add_intCast_mem_integerComplement k).mpr hc))).symm

/-- `U(a, c, z) → U(a, b, z)` along noninteger `c → b`. -/
theorem tendsto_kummerU (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => kummerU a c z) (𝓝[integerComplement] b) (𝓝 (kummerU a b z)) := by
  simpa using tendsto_kummerU_add_intCast a b 0 hz

/-! ### Joint continuity of Tricomi's function -/

section TricomiContinuity

open Set Metric

/-- Cauchy's formula for the difference quotient of an entire function. -/
theorem dslope_eq_circleIntegral {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℂ) {R : ℝ}
    {c : ℂ} (hc : c ∈ ball n R) :
    dslope f n c = (2 * π * I : ℂ)⁻¹ • ∫ θ : ℝ in 0..2 * π,
      circleMap 0 R θ * I * ((circleMap n R θ - c)⁻¹ *
        ((f (circleMap n R θ) - f n) / (circleMap n R θ - n))) := by
  have hR : 0 < R := pos_of_mem_ball hc
  have hd : Differentiable ℂ (dslope f n) := by
    rw [← differentiableOn_univ, differentiableOn_dslope univ_mem]
    exact hf.differentiableOn
  rw [← (hd.diffContOnCl (s := ball n R)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hc]
  congr 1
  unfold circleIntegral
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hne : circleMap n R θ ≠ n := by
    intro h
    have := circleMap_sub_center n R θ
    rw [h, sub_self] at this
    exact (circleMap_ne_center hR.ne') h
  simp only [smul_eq_mul]
  rw [deriv_circleMap, dslope_of_ne _ hne, slope_def_field]

/-- The difference quotient of a family of entire functions depends continuously on the
parameter and the point. -/
theorem continuousOn_dslope_param {X : Type*} [TopologicalSpace X] {f : X → ℂ → ℂ} {s : Set X}
    (hs : IsOpen s) (hf : ContinuousOn (fun p : X × ℂ => f p.1 p.2) (s ×ˢ univ))
    (hd : ∀ x ∈ s, Differentiable ℂ (f x)) (n : ℂ) :
    ContinuousOn (fun p : X × ℂ => dslope (f p.1) n p.2) (s ×ˢ univ) := by
  rintro ⟨x₀, c₀⟩ ⟨hx₀, -⟩
  set R : ℝ := ‖c₀ - n‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  set T : Set (X × ℂ) := s ×ˢ ball c₀ (1 / 2) with hT
  have hTo : IsOpen T := hs.prod isOpen_ball
  have hmem : (x₀, c₀) ∈ T := ⟨hx₀, mem_ball_self (by norm_num)⟩
  have hcball : ∀ p ∈ T, p.2 ∈ ball n R := by
    intro p hp
    have h1 := mem_ball.mp hp.2
    rw [mem_ball, dist_eq_norm] at *
    calc ‖p.2 - n‖ ≤ ‖p.2 - c₀‖ + ‖c₀ - n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < R := by linarith
  set F : X × ℂ → ℝ → ℂ := fun p θ => circleMap 0 R θ * I * ((circleMap n R θ - p.2)⁻¹ *
      ((f p.1 (circleMap n R θ) - f p.1 n) / (circleMap n R θ - n))) with hF
  have heq : EqOn (fun p : X × ℂ => dslope (f p.1) n p.2)
      (fun p => (2 * π * I : ℂ)⁻¹ • ∫ θ : ℝ in 0..2 * π, F p θ) T := fun p hp =>
    dslope_eq_circleIntegral (hd p.1 hp.1) n (hcball p hp)
  have hcont : ContinuousOn (fun p => (2 * π * I : ℂ)⁻¹ • ∫ θ : ℝ in 0..2 * π, F p θ) T := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous fun q : T => (2 * π * I : ℂ)⁻¹ • ∫ θ : ℝ in 0..2 * π, F q.1 θ
    refine Continuous.smul (continuous_const (y := (2 * π * I : ℂ)⁻¹)) ?_
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    have hfc : Continuous fun r : T × ℝ => f r.1.1.1 (circleMap n R r.2) := by
      refine hf.comp_continuous (f := fun r : T × ℝ => (r.1.1.1, circleMap n R r.2))
        (by fun_prop) fun r => ⟨r.1.2.1, mem_univ _⟩
    have hfn : Continuous fun r : T × ℝ => f r.1.1.1 n := by
      refine hf.comp_continuous (f := fun r : T × ℝ => (r.1.1.1, n))
        (by fun_prop) fun r => ⟨r.1.2.1, mem_univ _⟩
    have hne1 : ∀ r : T × ℝ, circleMap n R r.2 - r.1.1.2 ≠ 0 := by
      intro r h
      have h1 := hcball r.1.1 r.1.2
      rw [sub_eq_zero] at h
      rw [← h, mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos hR] at h1
      exact lt_irrefl _ h1
    have hne2 : ∀ r : T × ℝ, circleMap n R r.2 - n ≠ 0 := fun r =>
      sub_ne_zero.mpr (circleMap_ne_center hR.ne')
    simp only [hF]
    refine Continuous.mul (by fun_prop) (Continuous.mul ?_ ?_)
    · exact Continuous.inv₀ (by fun_prop) hne1
    · exact Continuous.div (hfc.sub hfn) (by fun_prop) hne2
  exact ((hcont.congr heq).continuousAt (hTo.mem_nhds hmem)).continuousWithinAt

/-- The regularized connection combination `tricomiD a c z` is jointly continuous in `(a, c, z)` for
`z` in the slit plane. -/
theorem continuousAt_tricomiD {a c z : ℂ} (hz : z ∈ slitPlane) :
    ContinuousAt (fun q : ℂ × ℂ × ℂ => tricomiD q.1 q.2.1 q.2.2) (a, c, z) := by
  have hM := continuous_regularizedConfluent
  have h1 : Continuous fun q : ℂ × ℂ × ℂ => regularizedHGFun {q.1} {q.2.1} q.2.2 := hM
  have h2 : Continuous fun q : ℂ × ℂ × ℂ =>
      regularizedHGFun {q.1 - q.2.1 + 1} {2 - q.2.1} q.2.2 :=
    hM.comp (f := fun q : ℂ × ℂ × ℂ => (q.1 - q.2.1 + 1, 2 - q.2.1, q.2.2)) (by fun_prop)
  have hG := differentiable_one_div_Gamma.continuous
  have h3 : Continuous fun q : ℂ × ℂ × ℂ => (Gamma (q.1 - q.2.1 + 1))⁻¹ :=
    (hG.comp (by fun_prop : Continuous fun q : ℂ × ℂ × ℂ => q.1 - q.2.1 + 1)).congr
      fun q => by simp
  have h4 : Continuous fun q : ℂ × ℂ × ℂ => (Gamma q.1)⁻¹ :=
    (hG.comp (by fun_prop : Continuous fun q : ℂ × ℂ × ℂ => q.1)).congr
      fun q => by simp
  have h5 : ContinuousAt (fun q : ℂ × ℂ × ℂ => q.2.2 ^ (1 - q.2.1)) (a, c, z) :=
    ContinuousAt.cpow (by fun_prop) (by fun_prop) hz
  unfold tricomiD
  exact (h1.continuousAt.mul h3.continuousAt).sub ((h5.mul h2.continuousAt).mul h4.continuousAt)

/-- A point within distance `1` of an integer `n`, other than `n`, is not an integer. -/
theorem mem_integerComplement_of_norm_sub_lt_one {n : ℤ} {c : ℂ} (hc : ‖c - n‖ < 1)
    (hcn : c ≠ n) : c ∈ integerComplement := by
  rintro ⟨k, rfl⟩
  have hk : k ≠ n := fun h => hcn (by rw [h])
  rw [← Int.cast_sub, Complex.norm_intCast] at hc
  have : (1 : ℝ) ≤ |((k - n : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hk)
  push_cast at this hc
  linarith

/-- Near an integer `n`, Tricomi's function is a quotient of difference quotients. -/
theorem kummerU_eq_dslope (a : ℂ) {z : ℂ} (hz : z ≠ 0) (n : ℤ) {b : ℂ} (hb : ‖b - n‖ < 1) :
    kummerU a b z = π * dslope (fun c => tricomiD a c z) n b /
      dslope (fun c => sin (π * c)) n b := by
  set S : ℂ → ℂ := fun c => sin (π * c) with hS
  set D : ℂ → ℂ := fun c => tricomiD a c z with hDdef
  have hSd : HasDerivAt S (cos (π * n) * π) n := by
    have := ((hasDerivAt_id (n : ℂ)).const_mul (π : ℂ)).csin
    simpa [hS] using this
  have hS0 : S n = 0 := by
    simp only [hS]
    rw [mul_comm]; exact Complex.sin_int_mul_pi n
  have hD0 : D n = 0 := tricomiD_intCast a z hz n
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  -- the formula off `n`
  have hoff : ∀ c : ℂ, c ∈ integerComplement →
      kummerU a c z = π * dslope D n c / dslope S n c := by
    intro c hc
    have hcn : c - n ≠ 0 := sub_ne_zero.mpr fun h => hc ⟨n, h.symm⟩
    have e1 := sub_smul_dslope D (n : ℂ) c
    have e2 := sub_smul_dslope S (n : ℂ) c
    rw [hD0, sub_zero, smul_eq_mul] at e1
    rw [hS0, sub_zero, smul_eq_mul] at e2
    have hsc : sin (π * c) ≠ 0 := sin_pi_mul_ne_zero_of_mem hc
    have hd2 : dslope S n c ≠ 0 := by
      intro h0; apply hsc; simp only [hS] at e2; rw [← e2, h0, mul_zero]
    rw [kummerU_eq_connection a c z (forall_of_mem_integerComplement hc),
      kummerUConnection_eq_tricomiD hc]
    simp only [hS, hDdef] at e1 e2 hd2 ⊢
    rw [← e1, ← e2]
    field_simp
  by_cases hbn : b = n
  · subst hbn
    have hcos : cos (π * n) ≠ 0 := by
      intro h
      have := Complex.cos_sq_add_sin_sq (π * (n : ℂ))
      simp only [hS] at hS0
      rw [h, hS0] at this
      norm_num at this
    have hcD : ContinuousAt (dslope D n) n :=
      continuousAt_dslope_same.mpr (differentiable_tricomiD a hz n)
    have hcS : ContinuousAt (dslope S n) n := continuousAt_dslope_same.mpr hSd.differentiableAt
    have hSn : dslope S n n ≠ 0 := by
      rw [dslope_same, hSd.deriv]; exact mul_ne_zero hcos hπ
    have := integerComplement_nhdsWithin_neBot (n : ℂ)
    have hL : Tendsto (fun c => kummerU a c z) (𝓝[integerComplement] (n : ℂ))
        (𝓝 (π * dslope D n n / dslope S n n)) :=
      ((((hcD.const_mul (π : ℂ)).div hcS hSn).tendsto).mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun c hc => (hoff c hc).symm)
    exact tendsto_nhds_unique (tendsto_kummerU a n hz) hL
  · exact hoff b (mem_integerComplement_of_norm_sub_lt_one hb hbn)

/-- **Joint continuity of Tricomi's function** in both parameters and the argument on the slit
plane, including integer second parameters. -/
theorem continuousAt_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    ContinuousAt (fun q : ℂ × ℂ × ℂ => kummerU q.1 q.2.1 q.2.2) (a, b, z) := by
  have hz0 := slitPlane_ne_zero hz
  by_cases hb : b ∈ integerComplement
  · have hev : (fun q : ℂ × ℂ × ℂ => π / sin (π * q.2.1) * tricomiD q.1 q.2.1 q.2.2) =ᶠ[𝓝 (a, b, z)]
        fun q => kummerU q.1 q.2.1 q.2.2 := by
      have hopen : IsOpen ((fun q : ℂ × ℂ × ℂ => q.2.1) ⁻¹' integerComplement) :=
        (Complex.isOpen_compl_range_intCast).preimage (by fun_prop)
      filter_upwards [hopen.mem_nhds hb] with q hq
      rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hq),
        kummerUConnection_eq_tricomiD hq]
    refine ContinuousAt.congr ?_ hev
    have hs : ContinuousAt (fun q : ℂ × ℂ × ℂ => sin (π * q.2.1)) (a, b, z) := by fun_prop
    exact (continuousAt_const.div hs (sin_pi_mul_ne_zero_of_mem hb)).mul
      (continuousAt_tricomiD hz)
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ℂ) = b := by
      by_contra h; exact hb fun ⟨k, hk⟩ => h ⟨k, hk⟩
    set S : ℂ → ℂ := fun c => sin (π * c) with hS
    have hW : IsOpen ({q : ℂ × ℂ × ℂ | ‖q.2.1 - n‖ < 1} ∩ {q | q.2.2 ∈ slitPlane}) :=
      (isOpen_lt (by fun_prop) continuous_const).inter (isOpen_slitPlane.preimage (by fun_prop))
    have hev : (fun q : ℂ × ℂ × ℂ => π * dslope (fun c => tricomiD q.1 c q.2.2) n q.2.1 /
        dslope S n q.2.1) =ᶠ[𝓝 ((a, n, z) : ℂ × ℂ × ℂ)] fun q => kummerU q.1 q.2.1 q.2.2 := by
      filter_upwards [hW.mem_nhds (⟨by simp, hz⟩ :
        ((a, n, z) : ℂ × ℂ × ℂ) ∈ {q : ℂ × ℂ × ℂ | ‖q.2.1 - n‖ < 1} ∩ {q | q.2.2 ∈ slitPlane})]
        with q hq
      exact (kummerU_eq_dslope q.1 (slitPlane_ne_zero hq.2) n hq.1).symm
    refine ContinuousAt.congr ?_ hev
    -- the numerator
    have hX : IsOpen (univ ×ˢ slitPlane : Set (ℂ × ℂ)) := isOpen_univ.prod isOpen_slitPlane
    have hnum := continuousOn_dslope_param (f := fun x : ℂ × ℂ => fun c => tricomiD x.1 c x.2)
      hX ?_ (fun x hx => differentiable_tricomiD x.1 (slitPlane_ne_zero hx.2)) (n : ℂ)
    · have hnumA : ContinuousAt (fun q : ℂ × ℂ × ℂ =>
          dslope (fun c => tricomiD q.1 c q.2.2) n q.2.1) (a, n, z) := by
        have := (hnum.continuousAt ((hX.prod isOpen_univ).mem_nhds
          (⟨⟨mem_univ _, hz⟩, mem_univ _⟩ : ((a, z), (n : ℂ)) ∈ (univ ×ˢ slitPlane) ×ˢ univ)))
        have hcomp : ContinuousAt (fun q : ℂ × ℂ × ℂ => ((q.1, q.2.2), q.2.1)) (a, (n : ℂ), z) := by
          fun_prop
        exact ContinuousAt.comp (f := fun q : ℂ × ℂ × ℂ => ((q.1, q.2.2), q.2.1)) this hcomp
      have hSd : Differentiable ℂ (dslope S n) := by
        rw [← differentiableOn_univ, differentiableOn_dslope univ_mem]
        exact (Complex.differentiable_sin.comp (differentiable_id.const_mul _)).differentiableOn
      have hSn : dslope S n n ≠ 0 := by
        have hSd' : HasDerivAt S (cos (π * n) * π) n := by
          have := ((hasDerivAt_id (n : ℂ)).const_mul (π : ℂ)).csin
          simpa [hS] using this
        have hS0 : S n = 0 := by
          simp only [hS]
          rw [mul_comm]; exact Complex.sin_int_mul_pi n
        have hcos : cos (π * n) ≠ 0 := by
          intro h
          have := Complex.cos_sq_add_sin_sq (π * (n : ℂ))
          simp only [hS] at hS0
          rw [h, hS0] at this
          norm_num at this
        rw [dslope_same, hSd'.deriv]
        exact mul_ne_zero hcos (ofReal_ne_zero.mpr Real.pi_ne_zero)
      exact (continuousAt_const.mul hnumA).div
        ((hSd.continuous.comp (f := fun q : ℂ × ℂ × ℂ => q.2.1) (by fun_prop)).continuousAt) hSn
    · rintro ⟨⟨a', z'⟩, c'⟩ ⟨⟨-, hz'⟩, -⟩
      have hcomp : ContinuousAt (fun p : (ℂ × ℂ) × ℂ => (p.1.1, p.2, p.1.2)) ((a', z'), c') := by
        fun_prop
      exact (ContinuousAt.comp (f := fun p : (ℂ × ℂ) × ℂ => (p.1.1, p.2, p.1.2))
        (continuousAt_tricomiD hz') hcomp).continuousWithinAt

/-- For fixed `z ≠ 0`, the Tricomi numerator is jointly continuous in the parameters. -/
theorem continuous_tricomiD_param {z : ℂ} (hz : z ≠ 0) :
    Continuous (fun p : ℂ × ℂ => tricomiD p.1 p.2 z) := by
  have hM := continuous_regularizedConfluent
  have h1 : Continuous fun p : ℂ × ℂ => regularizedHGFun {p.1} {p.2} z :=
    hM.comp (f := fun p : ℂ × ℂ => (p.1, p.2, z)) (by fun_prop)
  have h2 : Continuous fun p : ℂ × ℂ => regularizedHGFun {p.1 - p.2 + 1} {2 - p.2} z :=
    hM.comp (f := fun p : ℂ × ℂ => (p.1 - p.2 + 1, 2 - p.2, z)) (by fun_prop)
  have hG := differentiable_one_div_Gamma.continuous
  have h3 : Continuous fun p : ℂ × ℂ => (Gamma (p.1 - p.2 + 1))⁻¹ :=
    (hG.comp (by fun_prop : Continuous fun p : ℂ × ℂ => p.1 - p.2 + 1)).congr
      fun p => by simp
  have h4 : Continuous fun p : ℂ × ℂ => (Gamma p.1)⁻¹ :=
    (hG.comp (by fun_prop : Continuous fun p : ℂ × ℂ => p.1)).congr fun p => by simp
  have h5 : Continuous fun p : ℂ × ℂ => z ^ (1 - p.2) :=
    continuous_iff_continuousAt.mpr fun p =>
      ((continuousAt_const.sub continuousAt_snd).const_cpow (Or.inl hz))
  unfold tricomiD
  exact (h1.mul h3).sub ((h5.mul h2).mul h4)

/-- **Joint continuity of Tricomi's function in the parameters** at a fixed `z ≠ 0`. -/
theorem continuousAt_kummerU_param (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => kummerU p.1 p.2 z) (a, b) := by
  by_cases hb : b ∈ integerComplement
  · have hev : (fun p : ℂ × ℂ => π / sin (π * p.2) * tricomiD p.1 p.2 z) =ᶠ[𝓝 (a, b)]
        fun p => kummerU p.1 p.2 z := by
      have hopen : IsOpen ((fun p : ℂ × ℂ => p.2) ⁻¹' integerComplement) :=
        (Complex.isOpen_compl_range_intCast).preimage (by fun_prop)
      filter_upwards [hopen.mem_nhds hb] with p hp
      rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hp),
        kummerUConnection_eq_tricomiD hp]
    refine ContinuousAt.congr ?_ hev
    have hs : ContinuousAt (fun p : ℂ × ℂ => sin (π * p.2)) (a, b) := by fun_prop
    exact (continuousAt_const.div hs (sin_pi_mul_ne_zero_of_mem hb)).mul
      (continuous_tricomiD_param hz).continuousAt
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ℂ) = b := by
      by_contra h; exact hb fun ⟨k, hk⟩ => h ⟨k, hk⟩
    set S : ℂ → ℂ := fun c => sin (π * c) with hS
    have hW : IsOpen {p : ℂ × ℂ | ‖p.2 - n‖ < 1} := isOpen_lt (by fun_prop) continuous_const
    have hev : (fun p : ℂ × ℂ => π * dslope (fun c => tricomiD p.1 c z) n p.2 /
        dslope S n p.2) =ᶠ[𝓝 ((a, n) : ℂ × ℂ)] fun p => kummerU p.1 p.2 z := by
      filter_upwards [hW.mem_nhds (show ((a, n) : ℂ × ℂ) ∈ {p : ℂ × ℂ | ‖p.2 - n‖ < 1} by simp)]
        with p hp
      exact (kummerU_eq_dslope p.1 hz n hp).symm
    refine ContinuousAt.congr ?_ hev
    have hnum := continuousOn_dslope_param (f := fun x : ℂ => fun c => tricomiD x c z)
      isOpen_univ ((continuous_tricomiD_param hz).continuousOn)
      (fun x _ => differentiable_tricomiD x hz) (n : ℂ)
    have hnumA : ContinuousAt (fun p : ℂ × ℂ => dslope (fun c => tricomiD p.1 c z) n p.2)
        (a, n) :=
      hnum.continuousAt ((isOpen_univ.prod isOpen_univ).mem_nhds (by simp))
    have hSd : Differentiable ℂ (dslope S n) := by
      rw [← differentiableOn_univ, differentiableOn_dslope univ_mem]
      exact (Complex.differentiable_sin.comp (differentiable_id.const_mul _)).differentiableOn
    have hSn : dslope S n n ≠ 0 := by
      have hSd' : HasDerivAt S (cos (π * n) * π) n := by
        have := ((hasDerivAt_id (n : ℂ)).const_mul (π : ℂ)).csin
        simpa [hS] using this
      have hS0 : S n = 0 := by
        simp only [hS]
        rw [mul_comm]; exact Complex.sin_int_mul_pi n
      have hcos : cos (π * n) ≠ 0 := by
        intro h
        have := Complex.cos_sq_add_sin_sq (π * (n : ℂ))
        simp only [hS] at hS0
        rw [h, hS0] at this
        norm_num at this
      rw [dslope_same, hSd'.deriv]
      exact mul_ne_zero hcos (ofReal_ne_zero.mpr Real.pi_ne_zero)
    exact (continuousAt_const.mul hnumA).div
      ((hSd.continuous.comp (f := fun p : ℂ × ℂ => p.2) (by fun_prop)).continuousAt) hSn

end TricomiContinuity

/-- Kummer's transformation at noninteger second parameter, for every `z ≠ 0`. -/
theorem kummerU_kummer_transform_of_ne_zero (a b : ℂ) {z : ℂ} (hz0 : z ≠ 0)
    (hb : ∀ k : ℤ, b ≠ k) :
    kummerU a b z = z ^ (1 - b) * kummerU (a - b + 1) (2 - b) z := by
  have hb' : ∀ k : ℤ, (2 : ℂ) - b ≠ k := by
    intro k hk
    apply hb (2 - k)
    push_cast
    linear_combination -hk
  rw [kummerU_eq_connection a b z hb,
    kummerU_eq_connection (a - b + 1) (2 - b) z hb']
  unfold kummerUConnection
  have h1 : (1 : ℂ) - (2 - b) = b - 1 := by ring
  have h2 : (a - b + 1 : ℂ) - (2 - b) + 1 = a := by ring
  have h3 : (2 - b : ℂ) - 1 = 1 - b := by ring
  have h4 : (1 : ℂ) - (2 - b) = b - 1 := h1
  have h5 : (2 : ℂ) - (2 - b) = b := by ring
  have hpow : z ^ (1 - b) * z ^ (b - 1) = 1 := by
    rw [← cpow_add _ _ hz0]
    ring_nf
    simp
  simp only [h1, h2, h3, h5]
  rw [mul_add]
  have hswap :
      z ^ (1 - b) * (Gamma (1 - b) / Gamma (a - b + 1) * z ^ (b - 1) * kummerM a b z) =
        Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z := by
    calc
      _ = (z ^ (1 - b) * z ^ (b - 1)) *
            (Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z) := by ring
      _ = _ := by rw [hpow, one_mul]
  rw [hswap]
  ring

/-- Kummer transformation for U at noninteger second parameter; see
`kummerU_kummer_transform_all` for every second parameter. -/
@[dlmf 13.2.E40]
theorem kummerU_kummer_transform (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hb : ∀ k : ℤ, b ≠ k) :
    kummerU a b z = z ^ (1 - b) * kummerU (a - b + 1) (2 - b) z :=
  kummerU_kummer_transform_of_ne_zero a b (slitPlane_ne_zero hz) hb

/-- Two functions continuous at `b` that agree at all noninteger points agree at `b`. -/
theorem eq_of_continuousAt_of_integerComplement {f g : ℂ → ℂ} {b : ℂ} (hf : ContinuousAt f b)
    (hg : ContinuousAt g b) (h : ∀ c ∈ integerComplement, f c = g c) : f b = g b := by
  have := integerComplement_nhdsWithin_neBot b
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun c hc => (h c hc).symm))

/-- `U` is continuous along any continuous curve in the parameters, at fixed `z ≠ 0`. -/
theorem continuousAt_kummerU_comp {A B : ℂ → ℂ} {b : ℂ} (hA : ContinuousAt A b)
    (hB : ContinuousAt B b) {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun c => kummerU (A c) (B c) z) b := by
  have h := continuousAt_kummerU_param (A b) (B b) hz
  have hc : ContinuousAt (fun c => (A c, B c)) b := hA.prodMk hB
  exact ContinuousAt.comp (f := fun c => (A c, B c)) h hc

/-- **Kummer's transformation** `U(a,b,z) = z^{1-b} U(a-b+1,2-b,z)` for every `b`. -/
@[dlmf 13.2.E40]
theorem kummerU_kummer_transform_all (a b : ℂ) {z : ℂ} (hz0 : z ≠ 0) :
    kummerU a b z = z ^ (1 - b) * kummerU (a - b + 1) (2 - b) z := by
  refine eq_of_continuousAt_of_integerComplement (f := fun c => kummerU a c z)
    (g := fun c => z ^ (1 - c) * kummerU (a - c + 1) (2 - c) z)
    (continuousAt_kummerU_comp continuousAt_const continuousAt_id hz0) ?_
    (fun c hc => kummerU_kummer_transform_of_ne_zero a c hz0
      (forall_of_mem_integerComplement hc))
  have hpow : ContinuousAt (fun c : ℂ => z ^ (1 - c)) b :=
    (continuousAt_const.sub continuousAt_id).const_cpow (Or.inl hz0)
  exact hpow.mul (continuousAt_kummerU_comp (by fun_prop) (by fun_prop) hz0)

/- The punctured parameter-limit theorem is proved in `DLMF.Confluent.Continuation`. -/

/-- The polynomial `(-1)^m ∑ C(m,s) (b+s)_{m-s} (-z)^s` equals `(-1)^m (b)_m M(-m,b,z)`. -/
theorem neg_nat_sum_eq (m : ℕ) {b : ℂ} (hb : ∀ k : ℕ, b ≠ -(k : ℂ)) (z : ℂ) :
    (-1 : ℂ) ^ m * ∑ s ∈ Finset.range (m + 1), (m.choose s : ℂ) * poch (b + s) (m - s) * (-z) ^ s =
      (-1 : ℂ) ^ m * poch b m * kummerM (-(m : ℂ)) b z := by
  rw [kummerM_eq_sum_neg_nat, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hps : poch b s ≠ 0 := poch_ne_zero_of_not_neg_nat hb s
  have hf : (s.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
  have e1 : poch b m = poch b s * poch (b + s) (m - s) := by
    rw [← poch_add, Nat.add_sub_cancel' (by omega)]
  have e2 : poch (-(m : ℂ)) s = (-1) ^ s * (m.choose s : ℂ) * s.factorial := by
    rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  rw [e1, e2, neg_pow]
  field_simp
  ring

/-- The connection formula at `a = -m`, for noninteger `c`. -/
theorem kummerUConnection_neg_nat (m : ℕ) {c : ℂ} (hc : c ∈ integerComplement) (z : ℂ) :
    kummerUConnection (-(m : ℂ)) c z =
      (-1 : ℂ) ^ m * ∑ s ∈ Finset.range (m + 1), (m.choose s : ℂ) * poch (c + s) (m - s) * (-z) ^ s := by
  have hc0 := not_neg_nat_of_mem_integerComplement hc
  rw [neg_nat_sum_eq m hc0, kummerUConnection, Gamma_neg_nat_eq_zero, div_zero, zero_mul,
    zero_mul, add_zero]
  have h1 : ∀ k : ℕ, 1 - c - m ≠ -(k : ℂ) := by
    intro k hk
    exact hc ⟨1 + k - m, by push_cast; linear_combination hk⟩
  have hG := Gamma_add_nat_div_Gamma_eq (n := m) (1 - c - m) h1
  rw [show 1 - c - (m : ℂ) + m = 1 - c by ring] at hG
  rw [show -(m : ℂ) - c + 1 = 1 - c - m by ring, ← DLMF.Hypergeometric.poch_reflect, poch, ← hG]

/-- DLMF 13.2.7 in polynomial form, valid for every second parameter `b`:
`U(-m, b, z) = (-1)^m ∑_s C(m,s) (b+s)_{m-s} (-z)^s`. -/
@[dlmf 13.2.E7]
theorem kummerU_neg_nat_sum (m : ℕ) (b z : ℂ) :
    kummerU (-(m : ℂ)) b z =
      (-1 : ℂ) ^ m * ∑ s ∈ Finset.range (m + 1),
        (m.choose s : ℂ) * poch (b + s) (m - s) * (-z) ^ s := by
  set P : ℂ → ℂ := fun c => (-1 : ℂ) ^ m * ∑ s ∈ Finset.range (m + 1),
    (m.choose s : ℂ) * poch (c + s) (m - s) * (-z) ^ s with hP
  have hPc : Continuous P := by
    refine continuous_const.mul (continuous_finsetSum _ fun s _ => ?_)
    exact (continuous_const.mul ((Polynomial.differentiable (ascPochhammer ℂ (m - s))).continuous.comp
      (continuous_id.add continuous_const))).mul continuous_const
  by_cases hb : ∀ k : ℤ, b ≠ k
  · rw [kummerU_eq_connection _ _ _ hb,
      kummerUConnection_neg_nat m (mem_integerComplement_of_forall hb)]
  · unfold kummerU
    simp only [hb, ↓reduceIte]
    have := integerComplement_nhdsWithin_neBot b
    refine Tendsto.limUnder_eq ?_
    refine (hPc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (kummerUConnection_neg_nat m hc z).symm

@[dlmf 13.2.E7]
theorem kummerU_neg_nat (m : ℕ) (b z : ℂ) (hb : ∀ k : ℕ, b ≠ -k) :
    kummerU (-(m : ℂ)) b z =
      (-1 : ℂ) ^ m * poch b m * kummerM (-(m : ℂ)) b z := by
  rw [kummerU_neg_nat_sum, neg_nat_sum_eq m hb]

/-- Kummer's transformation at `b = a + n + 1`. -/
lemma kummerU_shift_nat_aux (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerU a (a + n + 1) z = z ^ (-a - n) * kummerU (-(n : ℂ)) (1 - a - n) z := by
  rw [kummerU_kummer_transform_all a _ (slitPlane_ne_zero hz)]
  congr 2 <;> ring

/-- A shifted Tricomi identity with a regular denominator in ordinary Kummer M. -/
@[dlmf 13.2.E8]
theorem kummerU_shift_nat (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℕ, 1 - a - n ≠ -k) :
    kummerU a (a + n + 1) z =
      (-1 : ℂ) ^ n * poch (1 - a - n) n / z ^ (a + n) *
        kummerM (-(n : ℂ)) (1 - a - n) z := by
  rw [kummerU_shift_nat_aux a n hz, kummerU_neg_nat n _ z ha,
    show -a - (n : ℂ) = -(a + n) by ring, cpow_neg]
  ring

@[dlmf 13.2.E8]
theorem kummerU_shift_nat_sum (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerU a (a + n + 1) z =
      z ^ (-a) * ∑ s ∈ Finset.range (n + 1),
        (n.choose s : ℂ) * poch a s * z ^ (-(s : ℂ)) := by
  have hz0 := slitPlane_ne_zero hz
  rw [kummerU_shift_nat_aux a n hz, kummerU_neg_nat_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [show n + 1 - 1 - s = n - s by omega, Nat.choose_symm hs', Nat.sub_sub_self hs',
    show (1 : ℂ) - a - n + ((n - s : ℕ) : ℂ) = 1 - a - ((s : ℕ) : ℂ) by
      push_cast [Nat.cast_sub hs']; ring, DLMF.Hypergeometric.poch_reflect a s]
  have e1 : z ^ (-a - n) = z ^ (-a) * (z ^ n)⁻¹ := by
    rw [sub_eq_add_neg, cpow_add _ _ hz0, cpow_neg z (n : ℂ), cpow_natCast]
  have e2 : z ^ (-(s : ℂ)) = (z ^ s)⁻¹ := by rw [cpow_neg, cpow_natCast]
  have e3 : z ^ n = z ^ s * z ^ (n - s) := by rw [← pow_add, Nat.add_sub_cancel' hs']
  have e4 : (-z) ^ (n - s) = (-1) ^ (n - s) * z ^ (n - s) := by rw [neg_pow]
  have e5 : ((-1 : ℂ) ^ n * (-1) ^ s * (-1) ^ (n - s)) = 1 := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hs', ← pow_add, ← two_mul, pow_mul]; simp
  have hzs : z ^ s ≠ 0 := pow_ne_zero _ hz0
  have hzns : z ^ (n - s) ≠ 0 := pow_ne_zero _ hz0
  rw [e1, e2, e3, e4]
  field_simp
  linear_combination (z ^ (-a) * (n.choose s : ℂ) * poch a s) * e5

/-- The connection quotient at a natural second parameter is a numerator derivative. -/
theorem kummerU_nat_eq_deriv (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    kummerU a n z = (-1 : ℂ) ^ n * deriv (fun c => tricomiD a c z) n := by
  have h := kummerU_eq_dslope a hz (n : ℤ) (b := (n : ℂ)) (by simp)
  simp only [Int.cast_natCast, dslope_same] at h
  have hs : HasDerivAt (fun c : ℂ => sin (π * c)) (cos (π * n) * π) n := by
    simpa using ((hasDerivAt_id (n : ℂ)).const_mul (π : ℂ)).csin
  have hcos : cos (π * (n : ℂ)) = (-1 : ℂ) ^ n := by
    rw [mul_comm, show (n : ℂ) * π = ((n * π : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cos, Real.cos_nat_mul_pi]
    push_cast; rfl
  rw [hs.deriv, hcos] at h
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hσ : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm n 2, pow_mul]; simp
  rw [h]
  field_simp
  linear_combination -(deriv (fun c => tricomiD a c z) n) * hσ

/-- Reindexing the finite singular part in descending powers of the argument. -/
theorem tricomi_finite_sum_eq (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (-1 : ℂ) ^ (n + 1) * z ^ (-(n : ℂ)) * ∑ j ∈ Finset.range n,
      poch (a - n) j * z ^ j / j.factorial *
        ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) =
    ∑ k ∈ Finset.Icc 1 n, ((k - 1).factorial : ℂ) * poch (1 - a + k) (n - k) /
      ((n - k).factorial : ℂ) * z ^ (-(k : ℂ)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    omega
  · intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact ⟨n - k, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    have hjn : j ≤ n := (Finset.mem_range.mp hj).le
    have hpow : z ^ (-(n : ℂ)) * z ^ j = z ^ (-((n - j : ℕ) : ℂ)) := by
      rw [← cpow_natCast z j, ← cpow_add _ _ hz]
      congr 1
      rw [Nat.cast_sub hjn]; ring
    have hp : poch (a - n) j = (-1 : ℂ) ^ j * poch (1 - a + ((n - j : ℕ) : ℂ)) j := by
      rw [show a - (n : ℂ) = 1 - (1 - a + ((n - j : ℕ) : ℂ)) - j by
        rw [Nat.cast_sub hjn]; ring, DLMF.Hypergeometric.poch_reflect]
    have hsign : (-1 : ℂ) ^ (n + 1) * (-1 : ℂ) ^ j * (-1 : ℂ) ^ (n - 1 - j) = 1 := by
      rw [← pow_add, ← pow_add, show n + 1 + j + (n - 1 - j) = 2 * n by
        have := Finset.mem_range.mp hj; omega, pow_mul]
      simp
    rw [show n - (n - j) = j by omega, show n - 1 - j = n - j - 1 by omega, hp]
    calc
      _ = ((n - j - 1).factorial : ℂ) * poch (1 - a + ((n - j : ℕ) : ℂ)) j /
          (j.factorial : ℂ) * (z ^ (-(n : ℂ)) * z ^ j) *
            ((-1 : ℂ) ^ (n + 1) * (-1 : ℂ) ^ j * (-1 : ℂ) ^ (n - 1 - j)) := by
              rw [show n - 1 - j = n - j - 1 by omega]; ring
      _ = _ := by rw [hpow, hsign, mul_one]

/-- At a positive integer second parameter, U is a logarithm times an analytic function,
an analytic remainder, and a finite singular part. -/
theorem kummerU_nat_log (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    kummerU a ((n : ℂ) + 1) z =
      (-1 : ℂ) ^ (n + 1) * (Gamma (a - n))⁻¹ *
        (log z * regularizedHGFun {a} {(n : ℂ) + 1} z + tricomiLogSeries a n z) +
      (-1 : ℂ) ^ (n + 1) * z ^ (-(n : ℂ)) * (Gamma a)⁻¹ *
        ∑ j ∈ Finset.range n, poch (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) := by
  have h := kummerU_nat_eq_deriv a (n + 1) hz
  push_cast at h
  rw [show (fun c => tricomiD a c z) = (fun c =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹) from rfl,
    deriv_tricomi_numerator_nat a n hz ha, tricomi_log_series_split a n hz ha] at h
  rw [h]
  ring

open DLMF.Gamma in
/-- `kummerU_nat_log` with `ψ(a+k)/Γ(a-n)` written through `(1/Γ)'`.
Stronger than `kummerU_nat_log`: valid for all `a`. -/
theorem kummerU_nat_log_recipGamma (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    kummerU a ((n : ℂ) + 1) z =
      (-1 : ℂ) ^ (n + 1) *
        ((Gamma (a - n))⁻¹ * log z * regularizedHGFun {a} {(n : ℂ) + 1} z +
          tricomiLogSeriesRecipGamma a n z) +
      (-1 : ℂ) ^ (n + 1) * z ^ (-(n : ℂ)) * (Gamma a)⁻¹ *
        ∑ j ∈ Finset.range n, poch (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) := by
  have h := kummerU_nat_eq_deriv a (n + 1) hz
  push_cast at h
  rw [show (fun c => tricomiD a c z) = (fun c =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹) from rfl,
    deriv_tricomi_numerator_nat_recipGamma a n hz, tricomi_log_series_split_recipGamma a n hz] at h
  rw [h]
  ring

/-- A logarithm dominates constants in a punctured complex neighborhood of zero. -/
theorem isBigO_one_log_zero :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun _ : ℂ => (1 : ℂ)) log := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-1)))] with z hz hzn
  rw [Metric.mem_ball, dist_zero_right] at hzn
  have hlog : Real.log ‖z‖ < -1 := by
    calc Real.log ‖z‖ < Real.log (Real.exp (-1)) :=
      Real.log_lt_log (norm_pos_iff.mpr hz) hzn
      _ = -1 := Real.log_exp _
  have hle := (le_abs_self (log z).re).trans (abs_re_le_norm (log z))
  have hle' := (neg_le_abs (log z).re).trans (abs_re_le_norm (log z))
  rw [log_re] at hle'
  simp only [norm_one, one_mul]
  linarith


@[dlmf 13.2.E9]
theorem kummerU_nat_denom (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℕ, a - n ≠ -k) :
    kummerU a (n + 1) z =
      (-1 : ℂ) ^ (n + 1) / ((n.factorial : ℂ) * Gamma (a - n)) *
        ∑' k : ℕ, poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k *
          (log z + digamma (a + k) - digamma (1 + k) - digamma (n + k + 1)) +
        1 / Gamma a * ∑ k ∈ Finset.Icc 1 n,
          ((k - 1).factorial : ℂ) * poch (1 - a + k) (n - k) /
            ((n - k).factorial : ℂ) * z ^ (-(k : ℂ)) := by
  have hz0 := slitPlane_ne_zero hz
  have h := deriv_tricomi_numerator_nat a n hz0 ha
  change deriv (fun c => tricomiD a c z) ((n : ℂ) + 1) = _ at h
  have hU := kummerU_nat_eq_deriv a (n + 1) hz0
  push_cast at hU
  rw [h] at hU
  have hΓ : ∀ k : ℕ, Gamma ((n : ℂ) + 1 + k) =
      (n.factorial : ℂ) * poch ((n : ℂ) + 1) k := by
    intro k
    have hn : ∀ j : ℕ, (n : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hG := Gamma_add_nat_div_Gamma_eq (n := k) ((n : ℂ) + 1) hn
    rw [div_eq_iff (Gamma_ne_zero hn), Gamma_nat_eq_factorial] at hG
    rw [hG]; ring
  have htail : (∑' k : ℕ, (poch a k * z ^ k / k.factorial *
      (Gamma ((n : ℂ) + 1 + k))⁻¹) *
        (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))) =
      (n.factorial : ℂ)⁻¹ * ∑' k : ℕ,
        poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k *
          (log z + digamma (a + k) - digamma (1 + k) - digamma (n + k + 1)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [hΓ, show (k : ℂ) + 1 = 1 + k by ring,
      show (n : ℂ) + 1 + k = n + k + 1 by ring]
    simp only [mul_inv, div_eq_mul_inv]
    ring
  rw [htail, mul_add] at hU
  rw [hU]
  have hf := tricomi_finite_sum_eq a n hz0
  linear_combination (Gamma a)⁻¹ * hf

open DLMF.Gamma in
/-- DLMF 13.2.9 with each product `ψ(a+k)/Γ(a-n)` written as `-(a-n)_{n+k} (1/Γ)'(a+k)`.
Stronger than DLMF: valid for all `a` (the digamma form needs `a - n ∉ {0, -1, -2, …}`
because Mathlib's `ψ` is `0` at its poles). -/
@[dlmf 13.2.E9]
theorem kummerU_nat_denom_recipGamma (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerU a (n + 1) z =
      (-1 : ℂ) ^ (n + 1) / (n.factorial : ℂ) *
        ∑' k : ℕ, poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k *
          ((Gamma (a - n))⁻¹ * (log z - digamma (1 + k) - digamma (n + k + 1)) -
            poch (a - n) (n + k) * recipGammaDeriv 1 (a + k)) +
        1 / Gamma a * ∑ k ∈ Finset.Icc 1 n,
          ((k - 1).factorial : ℂ) * poch (1 - a + k) (n - k) /
            ((n - k).factorial : ℂ) * z ^ (-(k : ℂ)) := by
  have hz0 := slitPlane_ne_zero hz
  have h := deriv_tricomi_numerator_nat_recipGamma a n hz0
  change deriv (fun c => tricomiD a c z) ((n : ℂ) + 1) = _ at h
  have hU := kummerU_nat_eq_deriv a (n + 1) hz0
  push_cast at hU
  rw [h] at hU
  have hΓ : ∀ k : ℕ, Gamma ((n : ℂ) + 1 + k) =
      (n.factorial : ℂ) * poch ((n : ℂ) + 1) k := by
    intro k
    have hn : ∀ j : ℕ, (n : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hG := Gamma_add_nat_div_Gamma_eq (n := k) ((n : ℂ) + 1) hn
    rw [div_eq_iff (Gamma_ne_zero hn), Gamma_nat_eq_factorial] at hG
    rw [hG]; ring
  have htail : (∑' k : ℕ, (poch a k * z ^ k / k.factorial *
      (Gamma ((n : ℂ) + 1 + k))⁻¹) *
        ((Gamma (a - n))⁻¹ * (log z - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) -
          poch (a - n) (n + k) * recipGammaDeriv 1 (a + k))) =
      (n.factorial : ℂ)⁻¹ * ∑' k : ℕ,
        poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k *
          ((Gamma (a - n))⁻¹ * (log z - digamma (1 + k) - digamma (n + k + 1)) -
            poch (a - n) (n + k) * recipGammaDeriv 1 (a + k)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [hΓ, show (k : ℂ) + 1 = 1 + k by ring,
      show (n : ℂ) + 1 + k = n + k + 1 by ring]
    simp only [mul_inv, div_eq_mul_inv]
    ring
  rw [htail] at hU
  rw [hU]
  have hf := tricomi_finite_sum_eq a n hz0
  linear_combination (Gamma a)⁻¹ * hf

/-- Polynomial specialization at positive integer second parameter, using the continued U. -/
@[dlmf 13.2.E10]
theorem kummerU_neg_nat_nat_denom (m n : ℕ) (z : ℂ) :
    kummerU (-(m : ℂ)) (n + 1) z =
      (-1 : ℂ) ^ m * poch (n + 1 : ℂ) m * kummerM (-(m : ℂ)) (n + 1) z := by
  refine kummerU_neg_nat m _ z fun k hk => ?_
  have := congrArg re hk
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

@[dlmf 13.2.E11]
theorem kummerU_neg_nat_shift (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerU a (-(n : ℂ)) z = z ^ (n + 1 : ℂ) * kummerU (a + n + 1) (n + 2) z := by
  rw [kummerU_kummer_transform_all a _ (slitPlane_ne_zero hz)]
  congr 2 <;> ring

/-- Exponential form of the sine factor occurring in monodromy. -/
theorem one_sub_exp_neg_two_mul_I (t : ℂ) :
    1 - exp (-2 * t * I) = 2 * I * exp (-t * I) * sin t := by
  have he : exp (-t * I) * exp (t * I) = 1 := by rw [← exp_add]; ring_nf; simp
  have h2 : exp (-2 * t * I) = exp (-t * I) * exp (-t * I) := by
    rw [← exp_add]; congr 1; ring
  rw [h2, sin]
  linear_combination -he - (exp (-t * I) * (exp (-t * I) - exp (t * I))) * I_sq

/-- Monodromy on the logarithmic argument plane for noninteger second parameter. -/
@[dlmf 13.2.E12]
theorem kummerU_analytic_continuation (a b z : ℂ) (m : ℤ) {w : ℂ}
    (hw : w = log z + 2 * π * I * m) (hz : z ∈ slitPlane)
    (hb : ∀ n : ℤ, b ≠ n) :
    kummerUOnLog a b w =
      (2 * π * I * exp (-π * I * b * m) * sin (π * b * m)) /
          (Gamma (1 + a - b) * sin (π * b)) * regularizedHGFun {a} {b} z +
        exp (-2 * π * I * b * m) * kummerU a b z := by
  subst w
  have hz0 := slitPlane_ne_zero hz
  have hbk : ∀ k : ℕ, b ≠ -(k : ℂ) := not_neg_nat_of_mem_integerComplement
    (mem_integerComplement_of_forall hb)
  have he : exp (log z + 2 * π * I * m) = z := by
    rw [exp_add, show (2 : ℂ) * π * I * m = (m : ℂ) * (2 * π * I) by ring,
      exp_int_mul_two_pi_mul_I, mul_one, exp_log hz0]
  have hp : exp ((1 - b) * (log z + 2 * π * I * m)) =
      z ^ (1 - b) * exp (-2 * π * I * b * m) := by
    rw [show (1 - b) * (log z + 2 * π * I * m) =
      log z * (1 - b) + (m * (2 * π * I) + (-2 * π * I * b * m)) by ring,
      exp_add, exp_add, exp_int_mul_two_pi_mul_I, one_mul, cpow_def_of_ne_zero hz0]
  have hc : Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z =
      π / (Gamma (1 + a - b) * sin (π * b)) * regularizedHGFun {a} {b} z := by
    rw [kummerM_eq_mul_regularizedHGFun hbk,
      show 1 + a - b = a - b + 1 by ring]
    have hg := Gamma_mul_Gamma_one_sub b
    calc _ = (Gamma b * Gamma (1 - b)) / Gamma (a - b + 1) *
        regularizedHGFun {a} {b} z := by ring
      _ = _ := by rw [hg]; ring
  have ht := one_sub_exp_neg_two_mul_I (π * b * m)
  rw [show -2 * (π * b * (m : ℂ)) * I = -2 * π * I * b * m by ring,
    show -(π * b * (m : ℂ)) * I = -π * I * b * m by ring] at ht
  rw [kummerUOnLog, he, hp, kummerU_eq_connection a b z hb]
  unfold kummerUConnection
  calc _ = (1 - exp (-2 * π * I * b * m)) *
        (Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z) +
      exp (-2 * π * I * b * m) *
        (Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z +
          Gamma (b - 1) / Gamma a * z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z) := by ring
    _ = _ := by rw [hc, ht]; ring

/-- For `c = -n`, the totalized Kummer series `M(a,-n,z)` reduces to its terms of index `≤ n`. -/
theorem kummerM_eq_sum_neg_nat_denom (n : ℕ) (a z : ℂ) :
    kummerM a (-(n : ℂ)) z =
      ∑ k ∈ Finset.range (n + 1),
        poch a k / (poch (-(n : ℂ)) k * k.factorial) * z ^ k := by
  unfold kummerM
  refine tsum_eq_sum fun k hk => ?_
  have hkn : n < k := by
    rw [Finset.mem_range, not_lt] at hk
    exact Nat.lt_of_succ_le hk
  rw [poch_neg_nat_eq_zero hkn, zero_mul, div_zero, zero_mul]

/-- The totalized Kummer function `M(a,b,·)` is complex differentiable at `0`. -/
theorem differentiableAt_kummerM (a b : ℂ) :
    DifferentiableAt ℂ (kummerM a b) 0 := by
  by_cases hb : ∀ k : ℕ, b ≠ -k
  · exact ((hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem
      (by simp : (0 : ℂ) ∈ Metric.eball (0 : ℂ) ⊤)).differentiableAt
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, b = -n := by
      push Not at hb
      simpa using hb
    have hfun : kummerM a b =
        fun z => ∑ k ∈ Finset.range (n + 1),
          poch a k / (poch (-(n : ℂ)) k * k.factorial) * z ^ k := by
      funext z
      rw [hn, kummerM_eq_sum_neg_nat_denom]
    rw [hfun]
    refine (Differentiable.fun_sum fun k _ => ?_).differentiableAt
    exact ((differentiable_id (𝕜 := ℂ)).pow k).const_mul _

@[dlmf 13.2.E13]
theorem isBigO_kummerM_sub_one (a b : ℂ) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) (fun z => kummerM a b z - 1) id := by
  refine (differentiableAt_kummerM a b).isBigO_sub.congr ?_ ?_
  · intro x
    simp [kummerM_zero]
  · intro x
    simp [id]

@[dlmf 13.2.E14]
theorem isBigO_kummerU_neg_nat (n : ℕ) (b : ℂ) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun z => kummerU (-(n : ℂ)) b z - (-1 : ℂ) ^ n * poch b n) id := by
  set P : ℂ → ℂ := fun z => (-1 : ℂ) ^ n * ∑ s ∈ Finset.range (n + 1),
    (n.choose s : ℂ) * poch (b + s) (n - s) * (-z) ^ s with hP
  have hU : ∀ z, kummerU (-(n : ℂ)) b z = P z := fun z => kummerU_neg_nat_sum n b z
  have hP0 : P 0 = (-1 : ℂ) ^ n * poch b n := by
    simp only [hP, neg_zero]
    rw [Finset.sum_range_succ']
    simp
  have hd : DifferentiableAt ℂ P 0 := by
    simp only [hP]
    fun_prop
  refine (hd.isBigO_sub).congr (fun z => ?_) (fun z => ?_)
  · rw [hU, hP0]
  · simp

@[dlmf 13.2.E15]
theorem isBigO_kummerU_neg_nat_shift (n : ℕ) (b : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU (-(n : ℂ) + b - 1) b z -
        (-1 : ℂ) ^ n * poch (2 - b) n * z ^ (1 - b))
      (fun z => z ^ (2 - b)) := by
  have h := (isBigO_kummerU_neg_nat n (2 - b)).mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hb : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z ^ (1 - b)) (fun z => z ^ (1 - b)) :=
    Asymptotics.isBigO_refl _ _
  refine (hb.mul h).congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [kummerU_kummer_transform_all (-(n : ℂ) + b - 1) b hz,
      show -(n : ℂ) + b - 1 - b + 1 = -(n : ℂ) by ring]
    ring
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [id]
    rw [show (2 : ℂ) - b = (1 - b) + 1 by ring, cpow_add _ _ hz, cpow_one]

/-- `‖z^w‖ ≤ ‖z‖^{Re w} e^{π |Im w|}` for `z ≠ 0`. -/
private lemma norm_cpow_le_exp_pi {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ‖z ^ w‖ ≤ ‖z‖ ^ w.re * Real.exp (Real.pi * |w.im|) := by
  rw [norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  calc -(arg z * w.im) ≤ |arg z * w.im| := neg_le_abs _
    _ = |arg z| * |w.im| := abs_mul _ _
    _ ≤ Real.pi * |w.im| := by gcongr; exact abs_arg_le_pi z

/-- `z^w = O(‖z‖^{Re w})` near `0`. -/
private lemma isBigO_cpow_norm_rpow (w : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z ^ w) (fun z => ‖z‖ ^ w.re) := by
  refine Asymptotics.IsBigO.of_bound (Real.exp (Real.pi * |w.im|)) ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [Real.norm_of_nonneg (by positivity), mul_comm]
  exact norm_cpow_le_exp_pi hz w

/-- `z = O(‖z‖^r)` near `0` for `r ≤ 1`. -/
private lemma isBigO_id_norm_rpow {r : ℝ} (hr : r ≤ 1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z) (fun z => ‖z‖ ^ r) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [one_mul, Real.norm_of_nonneg (by positivity)]
  exact Real.self_le_rpow_of_le_one (norm_nonneg z) hz hr

/-- `‖z‖^r = O(z^r)` near `0` for real `r`. -/
private lemma isBigO_norm_rpow_cpow (r : ℝ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => ‖z‖ ^ r) (fun z => z ^ (r : ℂ)) :=
  Asymptotics.isBigO_of_le _ fun z => by
    rw [norm_cpow_real, Real.norm_of_nonneg (by positivity)]

/-- A noninteger `b` from a strip of width one containing at most the integer `n`. -/
private lemma not_int_of_re_mem {b : ℂ} {n : ℤ} (h0 : (n : ℝ) ≤ b.re) (h1 : b.re < n + 1)
    (hb : b ≠ n) : ∀ k : ℤ, b ≠ k := by
  intro k hk
  have hre : b.re = k := by rw [hk]; simp
  have hkn : k = n := by
    have h0' : (n : ℝ) ≤ k := hre ▸ h0
    have h1' : (k : ℝ) < n + 1 := hre ▸ h1
    have : n ≤ k := by exact_mod_cast h0'
    have : k < n + 1 := by exact_mod_cast h1'
    omega
  exact hb (hk.trans (by rw [hkn]))

/-- Constants are `O(‖z‖^r)` near `0` for `r ≤ 0`. -/
private lemma isBigO_one_norm_rpow {r : ℝ} (hr : r ≤ 0) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun _ : ℂ => (1 : ℝ)) (fun z => ‖z‖ ^ r) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with z hz0 hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [one_mul, norm_one, Real.norm_of_nonneg (by positivity)]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (norm_pos_iff.mpr hz0) hz hr

/-- `log z = O(‖z‖^r)` near `0` for `r ≤ -1`. -/
private lemma isBigO_log_norm_rpow {r : ℝ} (hr : r ≤ -1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) log (fun z => ‖z‖ ^ r) := by
  refine Asymptotics.IsBigO.of_bound (1 + π) ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with z hz0 hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  have hx : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [Real.norm_of_nonneg (by positivity)]
  have hinv : ‖z‖⁻¹ ≤ ‖z‖ ^ r := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hx hz hr
  have h1 : 1 ≤ ‖z‖⁻¹ := one_le_inv_iff₀.mpr ⟨hx, hz⟩
  have hl : |Real.log ‖z‖| ≤ ‖z‖⁻¹ := by
    rw [abs_of_nonpos (Real.log_nonpos hx.le hz), ← Real.log_inv]
    linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr hx)]
  have hn : ‖log z‖ ≤ |Real.log ‖z‖| + π := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    rw [log_re, log_im]
    gcongr
    exact abs_arg_le_pi z
  calc ‖log z‖ ≤ ‖z‖⁻¹ + π * ‖z‖⁻¹ := by nlinarith [Real.pi_pos]
    _ = (1 + π) * ‖z‖⁻¹ := by ring
    _ ≤ (1 + π) * ‖z‖ ^ r := by gcongr

/-- `z^{-m}(P z - P 0) = O(‖z‖^{1-m})` near `0` for `P` differentiable at `0`. -/
private lemma isBigO_cpow_neg_nat_mul_sub (m : ℕ) {P : ℂ → ℂ}
    (hP : DifferentiableAt ℂ P 0) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => z ^ (-(m : ℂ)) * (P z - P 0))
      (fun z => ‖z‖ ^ (1 - (m : ℝ))) := by
  have h := (isBigO_cpow_norm_rpow (-(m : ℂ))).mul
    ((hP.isBigO_sub.mono (nhdsWithin_le_nhds (s := {0}ᶜ))).norm_right)
  refine h.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he : ‖z‖ ^ (-(m : ℂ)).re * ‖z - 0‖ = ‖z‖ ^ (1 - (m : ℝ)) := by
    rw [sub_zero, show 1 - (m : ℝ) = (-(m : ℂ)).re + 1 by simp; ring, Real.rpow_add hz0,
      Real.rpow_one]
  rw [he, one_mul]

/-- `(-1)^k (1-m)_k = Γ(m)/Γ(m-k)`. -/
private lemma neg_one_pow_mul_poch_one_sub_nat (m k : ℕ) (hm : 1 ≤ m) :
    (-1 : ℂ) ^ k * poch (1 - m) k = Gamma m / Gamma ((m : ℂ) - k) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [show (1 : ℂ) - ((n + 1 : ℕ) : ℂ) = -(n : ℂ) by push_cast; ring, poch_neg_coe_nat,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  rcases lt_or_ge n k with hk | hk
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk,
      show ((n + 1 : ℕ) : ℂ) - k = -((k - (n + 1) : ℕ) : ℂ) by
        rw [Nat.cast_sub (by omega)]; push_cast; ring, Gamma_neg_nat_eq_zero]
    simp
  · rw [show ((n + 1 : ℕ) : ℂ) - k = ((n - k : ℕ) : ℂ) + 1 by
        rw [Nat.cast_sub hk]; push_cast; ring, Gamma_nat_eq_factorial,
      show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial,
      eq_div_iff (by exact_mod_cast (Nat.factorial_ne_zero _)), mul_comm]
    exact_mod_cast (Nat.factorial_mul_descFactorial hk)

/-- Behaviour of `U` at zero for `Re b ≥ 2`, `b ≠ 2`; at `b = 2` a `log z` term appears
(see `isBigO_kummerU_at_zero_b_two`). -/
@[dlmf 13.2.E16]
theorem isBigO_kummerU_at_zero_re_ge_two (a b : ℂ) (hb : 2 ≤ b.re) (hb2 : b ≠ 2) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a b z - Gamma (b - 1) / Gamma a * z ^ (1 - b))
      (fun z => z ^ (2 - b.re : ℂ)) := by
  refine Asymptotics.IsBigO.trans ?_ (by simpa using isBigO_norm_rpow_cpow (2 - b.re))
  by_cases hbZ : ∀ k : ℤ, b ≠ k
  · have hM : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => kummerM a b z)
        (fun _ => (1 : ℝ)) :=
      ((differentiableAt_kummerM a b).continuousAt.tendsto.isBigO_one ℝ).mono
        nhdsWithin_le_nhds
    have h1 := hM.trans (isBigO_one_norm_rpow (r := 2 - b.re) (by linarith))
    have h2 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
        (fun z => z ^ (1 - b) * (kummerM (a - b + 1) (2 - b) z - 1))
        (fun z => ‖z‖ ^ (2 - b.re)) := by
      refine ((isBigO_cpow_norm_rpow (1 - b)).mul
        ((isBigO_kummerM_sub_one (a - b + 1) (2 - b)).mono
          (nhdsWithin_le_nhds (s := {0}ᶜ))).norm_right).trans ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have he : ‖z‖ ^ (1 - b).re * ‖id z‖ = ‖z‖ ^ (2 - b.re) := by
        rw [id, show 2 - b.re = (1 - b).re + 1 by simp; ring, Real.rpow_add hz0, Real.rpow_one]
      rw [he, one_mul]
    have hsum := (h1.const_mul_left (Gamma (1 - b) / Gamma (a - b + 1))).add
      (h2.const_mul_left (Gamma (b - 1) / Gamma a))
    refine hsum.congr (fun z => ?_) (fun z => rfl)
    rw [kummerU_eq_connection a b z hbZ, kummerUConnection]
    ring
  push Not at hbZ
  obtain ⟨n, rfl⟩ := hbZ
  have hn2 : (2 : ℝ) ≤ n := by simpa using hb
  have hn3 : n ≠ 2 := fun h => hb2 (by rw [h]; norm_num)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by
    have : (2 : ℤ) ≤ n := by exact_mod_cast hn2
    omega⟩
  have hm : 2 ≤ m := by
    have : (2 : ℤ) ≤ (m : ℤ) + 1 := by exact_mod_cast hn2
    omega
  have hb' : (((m : ℤ) + 1 : ℤ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hre : 2 - ((m : ℂ) + 1).re = 1 - (m : ℝ) := by simp; ring
  simp only [hb']
  simp only [hre]
  have hpow : ∀ z : ℂ, z ^ (1 - ((m : ℂ) + 1)) = z ^ (-(m : ℂ)) := fun z => by
    congr 1; ring
  simp only [hpow, show (m : ℂ) + 1 - 1 = m by ring]
  by_cases ha : ∀ k : ℕ, a - m ≠ -(k : ℂ)
  · set P : ℂ → ℂ := fun z => ∑ j ∈ Finset.range m, poch (a - m) j * z ^ j / j.factorial *
        ((-1 : ℂ) ^ (m - 1 - j) * ((m - 1 - j).factorial : ℂ)) with hPdef
    have hP : DifferentiableAt ℂ P 0 := by rw [hPdef]; fun_prop
    have hP0 : (-1 : ℂ) ^ (m + 1) * P 0 = Gamma m := by
      obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
      rw [hPdef]
      simp only [Finset.sum_range_succ', ne_eq, Nat.add_one_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, zero_div, zero_mul, Finset.sum_const_zero, zero_add,
        poch_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      rw [show ((p + 1 : ℕ) : ℂ) = (p : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial,
        show p + 1 - 1 - 0 = p by omega, ← mul_assoc, ← pow_add,
        show p + 1 + 1 + p = 2 * (p + 1) by ring, pow_mul]
      simp
    have hM := ((differentiableAt_regularizedConfluent a ((m : ℂ) + 1) 0).continuousAt.tendsto.isBigO_one ℝ).mono
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hT := ((analyticAt_tricomiLogSeries a m ha).continuousAt.tendsto.isBigO_one ℝ).mono
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hr1 : 1 - (m : ℝ) ≤ -1 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hLM := ((isBigO_log_norm_rpow hr1).mul hM)
    simp only [mul_one] at hLM
    have h := ((hLM.add (hT.trans (isBigO_one_norm_rpow (by linarith)))).const_mul_left
        ((-1 : ℂ) ^ (m + 1) * (Gamma (a - m))⁻¹)).add
      ((isBigO_cpow_neg_nat_mul_sub m hP).const_mul_left ((-1 : ℂ) ^ (m + 1) * (Gamma a)⁻¹))
    refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [kummerU_nat_log a m hz ha, ← hP0]
    simp only [hPdef]
    ring
  · push Not at ha
    obtain ⟨k, hk⟩ := ha
    have hak : a = (m : ℂ) - k := by linear_combination hk
    have hQ : Differentiable ℂ (kummerU (-(k : ℂ)) (1 - m)) := by
      rw [show kummerU (-(k : ℂ)) (1 - m) = fun z => (-1 : ℂ) ^ k *
          ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * poch (1 - m + j) (k - j) * (-z) ^ j from
        funext fun z => kummerU_neg_nat_sum k _ z]
      fun_prop
    have hQ0 : kummerU (-(k : ℂ)) (1 - m) 0 = Gamma m / Gamma a := by
      rw [kummerU_neg_nat_sum, hak, ← neg_one_pow_mul_poch_one_sub_nat m k (by omega)]
      simp [Finset.sum_range_succ']
    refine (isBigO_cpow_neg_nat_mul_sub m (hQ 0)).congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [kummerU_kummer_transform_all a _ hz, hpow, hQ0,
      show a - ((m : ℂ) + 1) + 1 = -(k : ℂ) by rw [hak]; ring,
      show (2 : ℂ) - ((m : ℂ) + 1) = 1 - m by ring]
    ring

@[dlmf 13.2.E17]
theorem isBigO_kummerU_at_zero_b_two (a : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a 2 z - 1 / Gamma a * z⁻¹)
      (fun z => log z) := by
  by_cases ha : ∀ k : ℕ, a - (1 : ℕ) ≠ -(k : ℂ)
  · have hM := ((differentiableAt_regularizedConfluent a ((1 : ℂ) + 1) 0).continuousAt.tendsto.isBigO_one ℂ).mono
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hT := ((analyticAt_tricomiLogSeries a 1 ha).continuousAt.tendsto.isBigO_one ℂ).mono
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hLM := (Asymptotics.isBigO_refl log (𝓝[≠] (0 : ℂ))).mul hM
    simp only [mul_one] at hLM
    have h := (hLM.add (hT.trans isBigO_one_log_zero)).const_mul_left (Gamma (a - 1))⁻¹
    refine h.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      rw [show (2 : ℂ) = (1 : ℕ) + 1 by norm_num, kummerU_nat_log a 1 hz ha]
      simp only [Nat.cast_one, one_add_one_eq_two, pow_two,
        Finset.sum_range_one, poch_zero, pow_zero, Nat.factorial_zero, Nat.sub_self,
        Nat.cast_one, div_one, mul_one, cpow_neg_one]
      ring
    · filter_upwards with z
      simp
  · push Not at ha
    obtain ⟨k, hk⟩ := ha
    cases k with
    | zero =>
      have ha1 : a = 1 := by push_cast at hk; linear_combination hk
      subst a
      refine Asymptotics.isBigO_zero _ _ |>.congr' ?_ (Filter.EventuallyEq.refl _ _)
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [kummerU_kummer_transform_all 1 2 hz]
      norm_num [kummerU_zero, cpow_neg_one]
    | succ k =>
      have hak : a = -(k : ℂ) := by push_cast at hk; linear_combination hk
      subst a
      have hc : Continuous (kummerU (-(k : ℂ)) 2) := by
        have heq : kummerU (-(k : ℂ)) 2 = fun z => (-1 : ℂ) ^ k *
            ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * poch (2 + j) (k - j) * (-z) ^ j :=
          funext fun z => kummerU_neg_nat_sum k 2 z
        rw [heq]
        fun_prop
      simpa [Gamma_neg_nat_eq_zero] using
        ((hc.continuousAt.tendsto.isBigO_one ℂ).mono
          (nhdsWithin_le_nhds (s := {0}ᶜ))).trans isBigO_one_log_zero

/-- Behaviour of `U` at zero for `1 ≤ Re b < 2`, `b ≠ 1`; at `b = 1` a `log z` term
appears (see `isBigO_kummerU_at_zero_b_one`). -/
@[dlmf 13.2.E18]
theorem isBigO_kummerU_at_zero_re_one_to_two (a b : ℂ)
    (hb0 : 1 ≤ b.re) (hb1 : b.re < 2) (hb2 : b ≠ 1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a b z - Gamma (b - 1) / Gamma a * z ^ (1 - b) -
        Gamma (1 - b) / Gamma (a - b + 1))
      (fun z => z ^ (2 - b.re : ℂ)) := by
  have hbZ : ∀ k : ℤ, b ≠ k :=
    not_int_of_re_mem (n := 1) (by simpa using hb0) (by norm_num; linarith) (by simpa using hb2)
  have h1 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => kummerM a b z - 1)
      (fun z => ‖z‖ ^ (2 - b.re)) :=
    ((isBigO_kummerM_sub_one a b).mono nhdsWithin_le_nhds).trans
      (isBigO_id_norm_rpow (by linarith))
  have h2 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => z ^ (1 - b) * (kummerM (a - b + 1) (2 - b) z - 1))
      (fun z => ‖z‖ ^ (2 - b.re)) := by
    refine ((isBigO_cpow_norm_rpow (1 - b)).mul
      ((isBigO_kummerM_sub_one (a - b + 1) (2 - b)).mono
        (nhdsWithin_le_nhds (s := {0}ᶜ))).norm_right).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have he : ‖z‖ ^ (1 - b).re * ‖id z‖ = ‖z‖ ^ (2 - b.re) := by
      rw [id, show 2 - b.re = (1 - b).re + 1 by simp; ring, Real.rpow_add hz0, Real.rpow_one]
    rw [he, one_mul]
  have hsum := ((h1.const_mul_left (Gamma (1 - b) / Gamma (a - b + 1))).add
    (h2.const_mul_left (Gamma (b - 1) / Gamma a))).trans
      (by simpa using isBigO_norm_rpow_cpow (2 - b.re))
  refine hsum.congr (fun z => ?_) (fun z => rfl)
  rw [kummerU_eq_connection a b z hbZ, kummerUConnection]
  ring

@[dlmf 13.2.E19]
/- At nonpositive integer a the Gamma/digamma product must be continued jointly.
The old statement at a = 0 asserted 1 = O(z log z). -/
theorem isBigO_kummerU_at_zero_b_one (a : ℂ) (ha : ∀ k : ℕ, a ≠ -k) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a 1 z +
        1 / Gamma a * (log z + digamma a + 2 * (Real.eulerMascheroniConstant : ℂ)))
      (fun z => z * log z) := by
  have ha0 : ∀ k : ℕ, a - (0 : ℕ) ≠ -(k : ℂ) := by simpa using ha
  have hM0 : regularizedHGFun {a} {(0 : ℂ) + 1} 0 = 1 := by
    simp [regularizedHGFunCoeff_singleton, poch_zero]
  have hT0 : tricomiLogSeries a 0 0 = digamma a + 2 * (Real.eulerMascheroniConstant : ℂ) := by
    rw [tricomiLogSeries_zero]; simp [digamma_one]; ring
  have hM := ((differentiableAt_regularizedConfluent a ((0 : ℂ) + 1) 0).isBigO_sub).mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hT := ((analyticAt_tricomiLogSeries a 0 ha0).differentiableAt.isBigO_sub).mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [sub_zero] at hM hT
  have hid : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z) (fun z => z * log z) := by
    simpa using (Asymptotics.isBigO_refl (fun z : ℂ => z) (𝓝[≠] (0 : ℂ))).mul
      isBigO_one_log_zero
  have h := ((hM.mul (Asymptotics.isBigO_refl log (𝓝[≠] (0 : ℂ)))).add
    (hT.trans hid)).const_mul_left (-(Gamma a)⁻¹)
  refine h.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hUz := kummerU_nat_log a 0 hz ha0
    norm_num only [Nat.cast_zero, zero_add] at hUz
    rw [hUz]
    simp only [hM0, hT0]
    simp only [sub_zero, mul_zero, add_zero]
    ring
  · filter_upwards with z
    simp

open DLMF.Gamma in
/-- DLMF 13.2.19 with `ψ(a)/Γ(a)` written as `-(1/Γ)'(a)`:
`U(a,1,z) + (log z + 2γ)/Γ(a) - (1/Γ)'(a) = O(z log z)`.
Stronger than DLMF: valid for all `a`, including `a ∈ {0, -1, -2, …}`. -/
@[dlmf 13.2.E19]
theorem isBigO_kummerU_at_zero_b_one_recipGamma (a : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a 1 z +
        ((Gamma a)⁻¹ * (log z + 2 * (Real.eulerMascheroniConstant : ℂ)) -
          recipGammaDeriv 1 a))
      (fun z => z * log z) := by
  have hM0 : regularizedHGFun {a} {(0 : ℂ) + 1} 0 = 1 := by
    simp [regularizedHGFunCoeff_singleton, poch_zero]
  have hT0 : tricomiLogSeriesRecipGamma a 0 0 =
      2 * (Real.eulerMascheroniConstant : ℂ) * (Gamma a)⁻¹ - recipGammaDeriv 1 a := by
    rw [tricomiLogSeriesRecipGamma_zero]; simp [digamma_one, poch_zero]; ring
  have hM := ((differentiableAt_regularizedConfluent a ((0 : ℂ) + 1) 0).isBigO_sub).mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hT := ((analyticAt_tricomiLogSeriesRecipGamma a 0).differentiableAt.isBigO_sub).mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [sub_zero] at hM hT
  have hid : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z : ℂ => z) (fun z => z * log z) := by
    simpa using (Asymptotics.isBigO_refl (fun z : ℂ => z) (𝓝[≠] (0 : ℂ))).mul
      isBigO_one_log_zero
  have h := ((((hM.mul (Asymptotics.isBigO_refl log (𝓝[≠] (0 : ℂ)))).const_mul_left
    (Gamma a)⁻¹).add (hT.trans hid))).const_mul_left (-1 : ℂ)
  refine h.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hUz := kummerU_nat_log_recipGamma a 0 hz
    norm_num only [Nat.cast_zero, zero_add, sub_zero] at hUz
    rw [hUz]
    simp only [hM0, hT0]
    simp only [mul_zero, add_zero]
    ring_nf
  · filter_upwards with z
    simp

@[dlmf 13.2.E20]
theorem isBigO_kummerU_at_zero_re_zero_to_one (a b : ℂ)
    (hb0 : 0 < b.re) (hb1 : b.re < 1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a b z - Gamma (1 - b) / Gamma (a - b + 1))
      (fun z => z ^ (1 - b.re : ℂ)) := by
  have hbZ : ∀ k : ℤ, b ≠ k := by
    refine not_int_of_re_mem (n := 0) (by simpa using hb0.le) (by simpa using hb1) ?_
    intro h
    rw [h] at hb0
    simp at hb0
  have h1 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => kummerM a b z - 1)
      (fun z => ‖z‖ ^ (1 - b.re)) :=
    ((isBigO_kummerM_sub_one a b).mono nhdsWithin_le_nhds).trans
      (isBigO_id_norm_rpow (by linarith))
  have hM : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => kummerM (a - b + 1) (2 - b) z)
      (fun _ => (1 : ℝ)) :=
    ((differentiableAt_kummerM (a - b + 1) (2 - b)).continuousAt.tendsto.isBigO_one ℝ).mono
      nhdsWithin_le_nhds
  have h2 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z)
      (fun z => ‖z‖ ^ (1 - b.re)) := by
    refine ((isBigO_cpow_norm_rpow (1 - b)).mul hM).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with z
    simp
  have hsum := ((h1.const_mul_left (Gamma (1 - b) / Gamma (a - b + 1))).add
    (h2.const_mul_left (Gamma (b - 1) / Gamma a))).trans
      (by simpa using isBigO_norm_rpow_cpow (1 - b.re))
  refine hsum.congr (fun z => ?_) (fun z => rfl)
  rw [kummerU_eq_connection a b z hbZ, kummerUConnection]
  ring

@[dlmf 13.2.E21]
theorem isBigO_kummerU_at_zero_b_zero (a : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a 0 z - 1 / Gamma (a + 1))
      (fun z => z * log z) := by
  have h := (Asymptotics.isBigO_refl (fun z : ℂ => z) (𝓝[≠] (0 : ℂ))).mul
    (isBigO_kummerU_at_zero_b_two (a + 1))
  refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [kummerU_kummer_transform_all a 0 hz]
  simp only [sub_zero, cpow_one, show (2 : ℂ) - 0 = 2 by ring]
  have hz0 : z ≠ 0 := hz
  field_simp [hz0]

/-- At the origin, `U(a,b,0) = Γ(1-b)/Γ(a-b+1)` for `Re b < 1`, including integer `b`. -/
theorem kummerU_zero_arg (a b : ℂ) (hb : b.re < 1) :
    kummerU a b 0 = Gamma (1 - b) / Gamma (a - b + 1) := by
  have hconn : ∀ c : ℂ, c.re < 1 →
      kummerUConnection a c 0 = Gamma (1 - c) / Gamma (a - c + 1) := by
    intro c hc
    have h1 : (1 : ℂ) - c ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    simp [kummerUConnection, kummerM_zero, zero_cpow h1]
  by_cases hbZ : ∀ k : ℤ, b ≠ k
  · rw [kummerU_eq_connection a b 0 hbZ, hconn b hb]
  · have hne := integerComplement_nhdsWithin_neBot b
    simp only [kummerU, hbZ, ite_false]
    refine Tendsto.limUnder_eq ?_
    have hG : ContinuousAt (fun c : ℂ => Gamma (1 - c) * (Gamma (a - c + 1))⁻¹) b := by
      refine ContinuousAt.mul ?_ ?_
      · refine (differentiableAt_Gamma _ fun m h => ?_).continuousAt.comp
          (continuousAt_const.sub continuousAt_id)
        have := congrArg re h; simp at this
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      · exact (differentiable_one_div_Gamma.continuous.comp
          (by fun_prop : Continuous fun c : ℂ => a - c + 1)).continuousAt
    refine (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    have hopen : {c : ℂ | c.re < 1} ∈ 𝓝 b :=
      (isOpen_lt continuous_re continuous_const).mem_nhds hb
    filter_upwards [nhdsWithin_le_nhds hopen] with c hc
    rw [hconn c hc, div_eq_mul_inv]

/-- Behaviour of `U` at zero for `Re b ≤ 0`, `b ≠ 0`; at `b = 0` a `z log z` term
appears (see `isBigO_kummerU_at_zero_b_zero`). -/
@[dlmf 13.2.E22]
theorem isBigO_kummerU_at_zero_re_nonpos (a b : ℂ) (hb : b.re ≤ 0) (hb0 : b ≠ 0) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun z => kummerU a b z - Gamma (1 - b) / Gamma (a - b + 1)) id := by
  have hb2 : 2 - b ≠ 2 := fun h => hb0 (by linear_combination -h)
  have h := (isBigO_cpow_norm_rpow (1 - b)).mul
    ((isBigO_kummerU_at_zero_re_ge_two (a - b + 1) (2 - b) (by simp; linarith) hb2).trans
      (isBigO_cpow_norm_rpow _))
  have h' : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => kummerU a b z - Gamma (1 - b) / Gamma (a - b + 1)) id := by
    refine (h.trans (Asymptotics.IsBigO.of_bound 1 ?_)).congr' ?_ (Filter.EventuallyEq.refl _ _)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have he : ‖z‖ ^ (1 - b).re * ‖z‖ ^ ((2 : ℂ) - ((2 - b).re : ℂ)).re = ‖id z‖ := by
        rw [← Real.rpow_add hz0, id]
        simp
      rw [Real.norm_of_nonneg (by positivity), he, one_mul]
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : z ≠ 0 := hz
      have hne : z ^ (1 - b) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
      rw [kummerU_kummer_transform_all a b hz0, show 2 - b - 1 = 1 - b by ring,
        show (1 : ℂ) - (2 - b) = -(1 - b) by ring, cpow_neg, mul_sub, mul_left_comm,
        mul_inv_cancel₀ hne, mul_one]
  obtain ⟨C, hC⟩ := h'.isBigOWith
  have hC' := hC.insert (x := (0 : ℂ)) (by
    rw [kummerU_zero_arg a b (by linarith), sub_self, norm_zero, id, norm_zero, mul_zero])
  rw [show insert (0 : ℂ) ({0}ᶜ) = Set.univ by ext; simp [em], nhdsWithin_univ] at hC'
  exact hC'.isBigO

/-! ### Wronskians -/

/-- For `b` not a nonpositive integer, `M(a,b,·)` is entire. -/
theorem analyticOnNhd_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    AnalyticOnNhd ℂ (kummerM a b) Set.univ := fun z _ =>
  (hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem (by simp)

/-- The entire part of the Wronskian of Kummer's pair `M(a,b,z)`, `z^{1-b} M(a-b+1,2-b,z)`
equals `(1-b) e^z`. -/
theorem kummer_pair_wronskian_core {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k)
    (hB : ∀ k : ℕ, 2 - b ≠ -k) (z : ℂ) :
    (1 - b) * kummerM a b z * kummerM (a - b + 1) (2 - b) z +
      z * (kummerM a b z * deriv (kummerM (a - b + 1) (2 - b)) z -
        kummerM (a - b + 1) (2 - b) z * deriv (kummerM a b) z) = (1 - b) * exp z := by
  set u := kummerM a b with hu
  set v := kummerM (a - b + 1) (2 - b) with hv
  have hua := analyticOnNhd_kummerM (a := a) hb
  have hva := analyticOnNhd_kummerM (a := a - b + 1) hB
  have hud : Differentiable ℂ u := fun w => (hua w (Set.mem_univ _)).differentiableAt
  have hvd : Differentiable ℂ v := fun w => (hva w (Set.mem_univ _)).differentiableAt
  have hud' : Differentiable ℂ (deriv u) := fun w => (hua.deriv w (Set.mem_univ _)).differentiableAt
  have hvd' : Differentiable ℂ (deriv v) := fun w => (hva.deriv w (Set.mem_univ _)).differentiableAt
  set F : ℂ → ℂ := fun w => (1 - b) * u w * v w + w * (u w * deriv v w - v w * deriv u w) with hF
  have hFd : ∀ w, HasDerivAt F ((1 - b) * deriv u w * v w + (1 - b) * u w * deriv v w +
      (u w * deriv v w - v w * deriv u w) + w * (deriv u w * deriv v w + u w * deriv (deriv v) w -
        (deriv v w * deriv u w + v w * deriv (deriv u) w))) w := by
    intro w
    have h1 := ((hud w).hasDerivAt.const_mul (1 - b)).mul (hvd w).hasDerivAt
    have h2 := ((hud w).hasDerivAt.mul (hvd' w).hasDerivAt).sub
      ((hvd w).hasDerivAt.mul (hud' w).hasDerivAt)
    have h3 := (hasDerivAt_id w).mul h2
    refine ((h1.add h3).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
    · simp only [hF, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id]
    · simp only [id, Pi.mul_apply, Pi.sub_apply]
      ring
  set E : ℂ → ℂ := fun w => (1 - b) * deriv u w * v w + (1 - b) * u w * deriv v w +
      (u w * deriv v w - v w * deriv u w) + w * (deriv u w * deriv v w + u w * deriv (deriv v) w -
        (deriv v w * deriv u w + v w * deriv (deriv u) w)) with hE
  have hud'' : Continuous (deriv (deriv u)) :=
    continuous_iff_continuousAt.mpr fun w =>
      (hua.deriv.deriv w (Set.mem_univ _)).continuousAt
  have hvd'' : Continuous (deriv (deriv v)) :=
    continuous_iff_continuousAt.mpr fun w =>
      (hva.deriv.deriv w (Set.mem_univ _)).continuousAt
  have hEc : Continuous E := by
    simp only [hE]
    have := hud.continuous; have := hvd.continuous; have := hud'.continuous
    have := hvd'.continuous
    fun_prop
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun w => (hFd w).continuousAt
  have hEF : E = F := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hEc hFc fun w hw => ?_
    have hw' : w ≠ 0 := hw
    have hU := kummerM_ode (a := a) hb hw'
    have hV := kummerM_ode (a := a - b + 1) hB hw'
    rw [iteratedDeriv_succ, iteratedDeriv_one] at hU hV
    rw [← hu] at hU
    rw [← hv] at hV
    simp only [hE, hF]
    linear_combination u w * hV - v w * hU
  have hFF : ∀ w, deriv F w = F w := by
    intro w
    rw [(hFd w).deriv]
    exact congrFun hEF w
  have hG : ∀ w, deriv (fun w => F w * exp (-w)) w = 0 := by
    intro w
    have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-w) * -1) w := (hasDerivAt_id w).neg.cexp
    rw [HasDerivAt.deriv (f := fun w => F w * exp (-w)) ((hFd w).mul he), ← (hFd w).deriv, hFF]
    ring
  have hGd : Differentiable ℂ (fun w => F w * exp (-w)) := fun w =>
    ((hFd w).differentiableAt.mul (by fun_prop))
  have hc := is_const_of_deriv_eq_zero hGd hG z 0
  have hF0 : F 0 = 1 - b := by simp [hF, hu, hv, kummerM_zero]
  simp only [neg_zero, exp_zero, mul_one, hF0] at hc
  have hez : exp (-z) * exp z = 1 := by rw [← exp_add]; simp
  change F z = (1 - b) * exp z
  linear_combination exp z * hc - F z * hez

/-- The Wronskian of Kummer's pair `M(a,b,z)`, `z^{1-b} M(a-b+1,2-b,z)`, at regular
denominators. -/
theorem wronskian_kummer_pair_of_nonpole (a b : ℂ) {z : ℂ} (hbk : ∀ k : ℕ, b ≠ -k)
    (hBk : ∀ k : ℕ, 2 - b ≠ -k) (hz : z ∈ slitPlane) :
    wronskian (kummerM a b) (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z =
      (1 - b) * z ^ (-b) * exp z := by
  have hz0 := slitPlane_ne_zero hz
  have hv := ((analyticOnNhd_kummerM (a := a - b + 1) hBk) z (Set.mem_univ _)).differentiableAt
  have hp := (hasDerivAt_id z).cpow_const (c := 1 - b) hz
  have hy := hp.mul hv.hasDerivAt
  simp only [id, mul_one] at hy
  unfold wronskian
  rw [HasDerivAt.deriv (f := fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) hy]
  have hcore := kummer_pair_wronskian_core (a := a) hbk hBk z
  have e1 : z ^ (1 - b - 1) = z ^ (-b) := by ring_nf
  have e2 : z ^ (1 - b) = z * z ^ (-b) := by
    rw [show (1 : ℂ) - b = 1 + -b by ring, cpow_add _ _ hz0, cpow_one]
  beta_reduce
  rw [e1, e2]
  linear_combination z ^ (-b) * hcore

/-- The Wronskian of Kummer's pair `M(a,b,z)`, `z^{1-b} M(a-b+1,2-b,z)`. -/
theorem wronskian_kummer_pair (a b : ℂ) {z : ℂ} (hb : ∀ n : ℤ, b ≠ n) (hz : z ∈ slitPlane) :
    wronskian (kummerM a b) (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z =
      (1 - b) * z ^ (-b) * exp z :=
  wronskian_kummer_pair_of_nonpole a b (fun k h => hb (-k) (by push_cast; exact h))
    (fun k h => hb (2 + k) (by push_cast; linear_combination -h)) hz

/-- Joint continuity at `(b, x)` gives uniform convergence near `x` as the parameter tends
to `b`. -/
theorem tendstoUniformlyOnFilter_of_continuousAt {F : ℂ → ℂ → ℂ} {b x : ℂ}
    (h : ContinuousAt (fun p : ℂ × ℂ => F p.1 p.2) (b, x)) {l : Filter ℂ} (hl : l ≤ 𝓝 b) :
    TendstoUniformlyOnFilter F (F b) l (𝓝 x) := by
  rw [Metric.tendstoUniformlyOnFilter_iff]
  intro ε hε
  have h1 : ∀ᶠ p : ℂ × ℂ in 𝓝 (b, x), dist (F p.1 p.2) (F b x) < ε / 2 :=
    Metric.tendsto_nhds.mp h (ε / 2) (by positivity)
  have h2 : ∀ᶠ w in 𝓝 x, dist (F b w) (F b x) < ε / 2 := by
    have hc : ContinuousAt (fun w => F b w) x :=
      ContinuousAt.comp (f := fun w => (b, w)) h (by fun_prop)
    exact Metric.tendsto_nhds.mp hc (ε / 2) (by positivity)
  have h1' : ∀ᶠ p : ℂ × ℂ in l ×ˢ 𝓝 x, dist (F p.1 p.2) (F b x) < ε / 2 := by
    rw [nhds_prod_eq] at h1
    exact Filter.Eventually.filter_mono (Filter.prod_mono hl le_rfl) h1
  filter_upwards [h1', h2.prod_inr l] with p hp1 hp2
  calc dist (F b p.2) (F p.1 p.2) ≤ dist (F b p.2) (F b x) + dist (F p.1 p.2) (F b x) :=
        dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hp2 hp1
    _ = ε := by ring

/-- At noninteger `c`, `U(a,c,·)` is differentiable on the slit plane. -/
theorem differentiableOn_kummerU_of_mem (a : ℂ) {c : ℂ} (hc : c ∈ integerComplement) :
    DifferentiableOn ℂ (kummerU a c) slitPlane := by
  have hcz := forall_of_mem_integerComplement hc
  have hck := not_neg_nat_of_mem_integerComplement hc
  have h2c : ∀ k : ℕ, 2 - c ≠ -k := fun k h => hcz (2 + k) (by push_cast; linear_combination -h)
  have hfun : kummerU a c = fun w => kummerUConnection a c w :=
    funext fun w => kummerU_eq_connection a c w hcz
  rw [hfun]
  intro w hw
  have hu := ((analyticOnNhd_kummerM (a := a) hck) w (Set.mem_univ _)).differentiableAt
  have hv := ((analyticOnNhd_kummerM (a := a - c + 1) h2c) w (Set.mem_univ _)).differentiableAt
  have hp := ((hasDerivAt_id w).cpow_const (c := 1 - c) hw).differentiableAt
  unfold kummerUConnection
  exact ((hu.const_mul _).add (((hp.const_mul _).mul hv))).differentiableWithinAt

/-- `U(a,c,·) → U(a,b,·)` locally uniformly on the slit plane along noninteger `c → b`. -/
theorem tendstoLocallyUniformlyOn_kummerU (a b : ℂ) :
    TendstoLocallyUniformlyOn (fun c => kummerU a c) (kummerU a b)
      (𝓝[integerComplement] b) slitPlane := by
  rw [tendstoLocallyUniformlyOn_iff_filter]
  intro x hx
  have hc : ContinuousAt (fun p : ℂ × ℂ => kummerU a p.1 p.2) (b, x) := by
    have h := continuousAt_kummerU a b hx
    have hf : ContinuousAt (fun p : ℂ × ℂ => (a, p.1, p.2)) (b, x) := by fun_prop
    exact ContinuousAt.comp (g := fun q : ℂ × ℂ × ℂ => kummerU q.1 q.2.1 q.2.2)
      (f := fun p : ℂ × ℂ => (a, p.1, p.2)) h hf
  exact (tendstoUniformlyOnFilter_of_continuousAt (F := fun c w => kummerU a c w) hc
    nhdsWithin_le_nhds).mono_right nhdsWithin_le_nhds

/-- **`U(a,b,·)` is holomorphic on the slit plane** for every `b`, including integers. -/
theorem differentiableOn_kummerU (a b : ℂ) : DifferentiableOn ℂ (kummerU a b) slitPlane := by
  have := integerComplement_nhdsWithin_neBot b
  exact (tendstoLocallyUniformlyOn_kummerU a b).differentiableOn
    (eventually_nhdsWithin_of_forall fun c hc => differentiableOn_kummerU_of_mem a hc)
    isOpen_slitPlane

/-- The `z`-derivative of `U(a,c,z)` converges along noninteger `c → b`. -/
theorem tendsto_deriv_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun c => deriv (kummerU a c) z) (𝓝[integerComplement] b)
      (𝓝 (deriv (kummerU a b) z)) := by
  have hd : ∀ᶠ c in 𝓝[integerComplement] b, DifferentiableOn ℂ (kummerU a c) slitPlane :=
    eventually_nhdsWithin_of_forall fun c hc => differentiableOn_kummerU_of_mem a hc
  exact ((tendstoLocallyUniformlyOn_kummerU a b).deriv hd isOpen_slitPlane).tendsto_at hz

/-- A nonzero base has nonzero complex powers. -/
private lemma cpow_ne_zero_of_ne_zero' {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z ^ s ≠ 0 := by
  rw [cpow_def_of_ne_zero hz]; exact exp_ne_zero _

/-- `Γ(b) Γ(2-b) = (1-b) π / sin(πb)`. -/
theorem Gamma_mul_Gamma_two_sub (b : ℂ) (hb1 : (1 : ℂ) - b ≠ 0) :
    Gamma b * Gamma (2 - b) = (1 - b) * (π / sin (π * b)) := by
  rw [show (2 : ℂ) - b = (1 - b) + 1 by ring, Gamma_add_one _ hb1, ← Gamma_mul_Gamma_one_sub b]
  ring

/-- The connection formula as an identity of functions, with its derivative. -/
theorem hasDerivAt_kummerU_connection (a : ℂ) {c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ∈ slitPlane) :
    HasDerivAt (kummerU a c)
      (Gamma (1 - c) / Gamma (a - c + 1) * deriv (kummerM a c) z +
        Gamma (c - 1) / Gamma a *
          deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z) z := by
  have hcz := forall_of_mem_integerComplement hc
  have hck := not_neg_nat_of_mem_integerComplement hc
  have h2c : ∀ k : ℕ, 2 - c ≠ -k := fun k h => hcz (2 + k) (by push_cast; linear_combination -h)
  have hfun : kummerU a c = fun w => Gamma (1 - c) / Gamma (a - c + 1) * kummerM a c w +
      Gamma (c - 1) / Gamma a * (w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) := by
    funext w
    rw [kummerU_eq_connection a c w hcz]
    unfold kummerUConnection
    ring
  have hu := ((analyticOnNhd_kummerM (a := a) hck) z (Set.mem_univ _)).differentiableAt
  have hv := ((analyticOnNhd_kummerM (a := a - c + 1) h2c) z (Set.mem_univ _)).differentiableAt
  have hy : DifferentiableAt ℂ (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - c) hz).differentiableAt.mul hv
  rw [hfun]
  exact (hu.hasDerivAt.const_mul _).add (hy.hasDerivAt.const_mul _)

/-- For noninteger `c`, the Wronskian of `M̃(a,c,z) = ₁F̃₁(a;c;z)` and `U(a,c,z)` is `-z^{-c} eᶻ /
Γ(a)` (DLMF 13.2.34). -/
theorem wronskian_regularized_kummerU_of_mem (a : ℂ) {c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ∈ slitPlane) :
    regularizedHGFun {a} {c} z * deriv (kummerU a c) z -
      kummerU a c z * deriv (regularizedHGFun {a} {c}) z = -(z ^ (-c) * exp z) / Gamma a := by
  have hcz := forall_of_mem_integerComplement hc
  have hck := not_neg_nat_of_mem_integerComplement hc
  have h1 : regularizedHGFun {a} {c} = fun w => (Gamma c)⁻¹ * kummerM a c w := by
    funext w; rw [regularizedConfluent_eq_div_Gamma hck, div_eq_inv_mul]
  have hu := ((analyticOnNhd_kummerM (a := a) hck) z (Set.mem_univ _)).differentiableAt
  have hW := wronskian_kummer_pair a c hcz hz
  unfold wronskian at hW
  rw [(hasDerivAt_kummerU_connection a hc hz).deriv, h1, deriv_const_mul _ hu,
    kummerU_eq_connection a c z hcz]
  unfold kummerUConnection
  have hc1 : c - 1 ≠ 0 := fun h => hcz 1 (by push_cast; linear_combination h)
  have hGc : Gamma c = (c - 1) * Gamma (c - 1) := by
    rw [← Gamma_add_one _ hc1]; ring_nf
  have hGc1 : Gamma (c - 1) ≠ 0 := Gamma_ne_zero fun k h => hcz (-k + 1) (by
    push_cast; linear_combination h)
  rw [hGc]
  calc ((c - 1) * Gamma (c - 1))⁻¹ * kummerM a c z *
        (Gamma (1 - c) / Gamma (a - c + 1) * deriv (kummerM a c) z +
          Gamma (c - 1) / Gamma a *
            deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z) -
      (Gamma (1 - c) / Gamma (a - c + 1) * kummerM a c z +
          Gamma (c - 1) / Gamma a * z ^ (1 - c) * kummerM (a - c + 1) (2 - c) z) *
        (((c - 1) * Gamma (c - 1))⁻¹ * deriv (kummerM a c) z)
      = ((c - 1) * Gamma (c - 1))⁻¹ * (Gamma (c - 1) / Gamma a) *
          (kummerM a c z * deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z -
            z ^ (1 - c) * kummerM (a - c + 1) (2 - c) z * deriv (kummerM a c) z) := by ring
    _ = _ := by
      rw [hW]
      field_simp
      ring

/-- For noninteger `c`, the Wronskian of `z^{1-c} M̃(a-c+1,2-c,z)` and `U(a,c,z)` is `-z^{-c} eᶻ /
Γ(a-c+1)` (DLMF 13.2.35). -/
theorem wronskian_shifted_kummerU_of_mem (a : ℂ) {c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ∈ slitPlane) :
    z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * deriv (kummerU a c) z -
      kummerU a c z * deriv (fun w => w ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} w) z =
      -(z ^ (-c) * exp z) / Gamma (a - c + 1) := by
  have hcz := forall_of_mem_integerComplement hc
  have hck := not_neg_nat_of_mem_integerComplement hc
  have h2c : ∀ k : ℕ, 2 - c ≠ -k := fun k h => hcz (2 + k) (by push_cast; linear_combination -h)
  have h2 : (fun w => w ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} w) =
      fun w => (Gamma (2 - c))⁻¹ * (w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) := by
    funext w; rw [regularizedConfluent_eq_div_Gamma h2c, div_eq_inv_mul]; ring
  have hv := ((analyticOnNhd_kummerM (a := a - c + 1) h2c) z (Set.mem_univ _)).differentiableAt
  have hy : DifferentiableAt ℂ (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - c) hz).differentiableAt.mul hv
  have hW := wronskian_kummer_pair a c hcz hz
  unfold wronskian at hW
  rw [(hasDerivAt_kummerU_connection a hc hz).deriv, h2, deriv_const_mul _ hy,
    regularizedConfluent_eq_div_Gamma h2c, kummerU_eq_connection a c z hcz]
  unfold kummerUConnection
  have hc1 : (1 : ℂ) - c ≠ 0 := fun h => hcz 1 (by push_cast; linear_combination -h)
  have hG2 : Gamma (2 - c) = (1 - c) * Gamma (1 - c) := by
    rw [show (2 : ℂ) - c = (1 - c) + 1 by ring, Gamma_add_one _ hc1]
  have hG1 : Gamma (1 - c) ≠ 0 := Gamma_ne_zero fun k h => hcz (k + 1) (by
    push_cast; linear_combination -h)
  rw [hG2]
  calc z ^ (1 - c) * (kummerM (a - c + 1) (2 - c) z / ((1 - c) * Gamma (1 - c))) *
        (Gamma (1 - c) / Gamma (a - c + 1) * deriv (kummerM a c) z +
          Gamma (c - 1) / Gamma a *
            deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z) -
      (Gamma (1 - c) / Gamma (a - c + 1) * kummerM a c z +
          Gamma (c - 1) / Gamma a * z ^ (1 - c) * kummerM (a - c + 1) (2 - c) z) *
        (((1 - c) * Gamma (1 - c))⁻¹ *
          deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z)
      = -(((1 - c) * Gamma (1 - c))⁻¹ * (Gamma (1 - c) / Gamma (a - c + 1))) *
          (kummerM a c z * deriv (fun w => w ^ (1 - c) * kummerM (a - c + 1) (2 - c) w) z -
            z ^ (1 - c) * kummerM (a - c + 1) (2 - c) z * deriv (kummerM a c) z) := by ring
    _ = _ := by
      rw [hW]
      field_simp

/-- The regularized `₁F̃₁(A(c); B(c); z)` is continuous in a parameter `c` entering through
continuous `A` and `B`. -/
theorem tendsto_regularizedConfluent_param (A B : ℂ → ℂ) (hA : Continuous A) (hB : Continuous B)
    (b z : ℂ) (l : Filter ℂ) (hl : l ≤ 𝓝 b) :
    Tendsto (fun c => regularizedHGFun {A c} {B c} z) l (𝓝 (regularizedHGFun {A b} {B b} z)) := by
  have h := continuous_regularizedConfluent.comp
    (f := fun c => (A c, B c, z)) (by fun_prop)
  exact (h.continuousAt.tendsto).mono_left hl

@[dlmf 13.2.E26]
theorem wronskian_kummerM_pair {a b z : ℂ} (hb : ∀ n : ℤ, b ≠ n)
    (hz : z ∈ slitPlane) :
    wronskian (kummerM a b)
      (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z ≠ 0 := by
  rw [wronskian_kummer_pair a b hb hz]
  have hb1 : (1 : ℂ) - b ≠ 0 := fun h => hb 1 (by push_cast; linear_combination -h)
  exact mul_ne_zero (mul_ne_zero hb1 (cpow_ne_zero_of_ne_zero' (slitPlane_ne_zero hz) _))
    (exp_ne_zero _)

@[dlmf 13.2.E33]
theorem wronskian_regularizedHGFun (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hb : ∀ n : ℤ, b ≠ n) :
    wronskian (regularizedHGFun {a} {b})
      (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w) z =
      sin (π * b) * z ^ (-b) * exp z / π := by
  have hbk : ∀ k : ℕ, b ≠ -k := fun k h => hb (-k) (by push_cast; exact h)
  have hBk : ∀ k : ℕ, 2 - b ≠ -k := fun k h => hb (2 + k) (by push_cast; linear_combination -h)
  have hb1 : (1 : ℂ) - b ≠ 0 := fun h => hb 1 (by push_cast; linear_combination -h)
  have hbc : b ∈ integerComplement := mem_integerComplement_of_forall hb
  have hsin := sin_pi_mul_ne_zero_of_mem hbc
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz0 := slitPlane_ne_zero hz
  have h1 : regularizedHGFun {a} {b} = fun w => (Gamma b)⁻¹ * kummerM a b w := by
    funext w; rw [regularizedConfluent_eq_div_Gamma hbk, div_eq_inv_mul]
  have h2 : (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w) =
      fun w => (Gamma (2 - b))⁻¹ * (w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) := by
    funext w; rw [regularizedConfluent_eq_div_Gamma hBk, div_eq_inv_mul]; ring
  have hW := wronskian_kummer_pair a b hb hz
  have hu := ((analyticOnNhd_kummerM (a := a) hbk) z (Set.mem_univ _)).differentiableAt
  have hv := ((analyticOnNhd_kummerM (a := a - b + 1) hBk) z (Set.mem_univ _)).differentiableAt
  have hy : DifferentiableAt ℂ (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - b) hz).differentiableAt.mul hv
  unfold wronskian at hW ⊢
  rw [h1, h2, deriv_const_mul _ hu, deriv_const_mul _ hy]
  have hG := Gamma_mul_Gamma_two_sub b hb1
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero hbk
  have hGB : Gamma (2 - b) ≠ 0 := Gamma_ne_zero hBk
  calc (Gamma b)⁻¹ * kummerM a b z * ((Gamma (2 - b))⁻¹ *
        deriv (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z) -
      (Gamma (2 - b))⁻¹ * (z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z) *
        ((Gamma b)⁻¹ * deriv (kummerM a b) z)
      = (Gamma b * Gamma (2 - b))⁻¹ * (kummerM a b z *
          deriv (fun w => w ^ (1 - b) * kummerM (a - b + 1) (2 - b) w) z -
        (z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z) * deriv (kummerM a b) z) := by
          rw [mul_inv]; ring
    _ = _ := by
      rw [hW, hG]
      field_simp

/-- 13.2.34 without the hypothesis on `a`. -/
theorem wronskian_regularizedHGFun_kummerU_all (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    wronskian (regularizedHGFun {a} {b}) (kummerU a b) z =
      -(z ^ (-b) * exp z) / Gamma a := by
  have hz0 := slitPlane_ne_zero hz
  have := integerComplement_nhdsWithin_neBot b
  unfold wronskian
  have key : ∀ c, regularizedHGFun {a} {c} z * deriv (kummerU a c) z -
      kummerU a c z * deriv (regularizedHGFun {a} {c}) z =
      regularizedHGFun {a} {c} z * deriv (kummerU a c) z -
        kummerU a c z * (a * regularizedHGFun {a + 1} {c + 1} z) := fun c => by
    rw [deriv_regularizedConfluent]
  rw [key]
  have hL : Tendsto (fun c => regularizedHGFun {a} {c} z * deriv (kummerU a c) z -
      kummerU a c z * (a * regularizedHGFun {a + 1} {c + 1} z)) (𝓝[integerComplement] b)
      (𝓝 (regularizedHGFun {a} {b} z * deriv (kummerU a b) z -
        kummerU a b z * (a * regularizedHGFun {a + 1} {b + 1} z))) := by
    have h1 := tendsto_regularizedConfluent_param (fun _ => a) id continuous_const continuous_id
      b z (𝓝[integerComplement] b) nhdsWithin_le_nhds
    have h2 := tendsto_regularizedConfluent_param (fun _ => a + 1) (fun c => c + 1)
      continuous_const (by fun_prop) b z (𝓝[integerComplement] b) nhdsWithin_le_nhds
    exact (h1.mul (tendsto_deriv_kummerU a b hz)).sub
      ((tendsto_kummerU a b hz0).mul (h2.const_mul a))
  have hR : Tendsto (fun c : ℂ => -(z ^ (-c) * exp z) / Gamma a) (𝓝[integerComplement] b)
      (𝓝 (-(z ^ (-b) * exp z) / Gamma a)) := by
    have hc : ContinuousAt (fun c : ℂ => z ^ (-c)) b :=
      continuousAt_id.neg.const_cpow (Or.inl hz0)
    exact ((((hc.mul continuousAt_const).neg).div_const _).tendsto).mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [← key]
  exact (wronskian_regularized_kummerU_of_mem a hc hz).symm

@[dlmf 13.2.E34]
theorem wronskian_regularizedHGFun_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℕ, a ≠ -k) :
    wronskian (regularizedHGFun {a} {b}) (kummerU a b) z =
      -(z ^ (-b) * exp z) / Gamma a := by
  exact wronskian_regularizedHGFun_kummerU_all a b hz

/-- `(-z)^w = z^w e^{επiw}` when `-z = z e^{επi}` with `arg z + επ ∈ (-π, π]`. -/
theorem neg_cpow_of_arg {z : ℂ} (hz : z ≠ 0) (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (h1 : -π < arg z + ε.re * π) (h2 : arg z + ε.re * π ≤ π) (w : ℂ) :
    (-z) ^ w = z ^ w * exp (ε * π * I * w) := by
  have hn : -z = exp (log z + ε * π * I) := by
    rw [exp_add, exp_log hz]
    rcases hε with rfl | rfl
    · rw [one_mul, exp_pi_mul_I]; ring
    · rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; ring
  have hre : ε = (ε.re : ℂ) := by rcases hε with rfl | rfl <;> simp
  have hlog : log (-z) = log z + ε * π * I := by
    rw [hn, log_exp]
    · rw [hre]; simp [log_im]; linarith
    · rw [hre]; simp [log_im]; linarith
  rw [cpow_def_of_ne_zero (neg_ne_zero.mpr hz), hlog, cpow_def_of_ne_zero hz, add_mul, exp_add]

/-- The reciprocal reflection formula, valid for all `s` with the totalized `Γ`. -/
theorem recip_Gamma_mul_Gamma_one_sub (s : ℂ) : (Gamma s * Gamma (1 - s))⁻¹ = sin (π * s) / π := by
  rw [Gamma_mul_Gamma_one_sub, inv_div]

/-- The reflection formula in the form `1/Γ(1-z) = Γ(z) sin(πz)/π`, valid whenever
`Γ(z) ≠ 0` (at poles of `Γ(1-z)` both sides vanish). -/
theorem recip_Gamma_one_sub_eq {z : ℂ} (hz : Complex.Gamma z ≠ 0) :
    (Complex.Gamma (1 - z))⁻¹ = Complex.Gamma z * Complex.sin (π * z) / π := by
  rw [mul_div_assoc, ← recip_Gamma_mul_Gamma_one_sub, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ hz, one_mul]

/-- The trigonometric identity behind the `M(a,b,z)` coefficient in DLMF 13.2.41. -/
theorem exp_sin_connection (a b ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    exp (-ε * a * π * I) * sin (π * (b - a)) + exp (ε * (b - a) * π * I) * sin (π * a) =
      sin (π * b) := by
  have hu := exp_ne_zero (a * π * I)
  have hv := exp_ne_zero (b * π * I)
  have e1 : ∀ x : ℂ, sin (π * x) = (exp (-(x * π * I)) - exp (x * π * I)) * I / 2 := fun x => by
    rw [Complex.sin]; ring_nf
  rw [e1, e1, e1]
  rcases hε with rfl | rfl
  · rw [show -1 * a * π * I = -(a * π * I) by ring,
      show (1 : ℂ) * (b - a) * π * I = b * π * I - a * π * I by ring,
      show -((b - a) * π * I) = a * π * I - b * π * I by ring,
      show (b - a) * π * I = b * π * I - a * π * I by ring]
    simp only [exp_neg, exp_sub]
    field_simp
    ring
  · rw [show -(-1) * a * π * I = a * π * I by ring,
      show (-1 : ℂ) * (b - a) * π * I = a * π * I - b * π * I by ring,
      show -((b - a) * π * I) = a * π * I - b * π * I by ring,
      show (b - a) * π * I = b * π * I - a * π * I by ring]
    simp only [exp_neg, exp_sub]
    field_simp
    ring

/-- The cancellation of the `z^{1-b}` terms in DLMF 13.2.41. -/
theorem exp_connection_cancel (a b ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    exp (-ε * a * π * I) + exp (ε * (b - a) * π * I) * exp (ε * π * I * (1 - b)) = 0 := by
  rw [← exp_add, show ε * (b - a) * π * I + ε * π * I * (1 - b) = -ε * a * π * I + ε * π * I by
    ring, exp_add]
  rcases hε with rfl | rfl
  · rw [one_mul, exp_pi_mul_I]; ring
  · rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; ring

/-- DLMF 13.2.41 for noninteger `b`, with `-z = z e^{επi}` and `ε = ±1`. -/
theorem kummerM_div_Gamma_connection_of_not_int (a b : ℂ) {z : ℂ} (hb : ∀ k : ℤ, b ≠ k)
    (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (hc : (-z) ^ (1 - b) = z ^ (1 - b) * exp (ε * π * I * (1 - b))) :
    kummerM a b z / Gamma b =
      exp (-ε * a * π * I) / Gamma (b - a) * kummerU a b z +
        exp (ε * (b - a) * π * I) / Gamma a * exp z * kummerU (b - a) b (-z) := by
  have hbn : ∀ k : ℕ, b ≠ -k := fun k h => hb (-k) (by simp [h])
  have h2b : ∀ k : ℕ, 2 - b ≠ -k := fun k h => hb (k + 2) (by push_cast; linear_combination -h)
  rw [kummerU_eq_connection _ _ _ hb, kummerU_eq_connection _ _ _ hb, kummerUConnection,
    kummerUConnection, hc, show b - a - b + 1 = 1 - a by ring]
  have hk1 := kummerM_kummer_transform (a := a) (z := z) hbn
  have hk2 := kummerM_kummer_transform (a := a - b + 1) (z := z) h2b
  rw [show 2 - b - (a - b + 1) = 1 - a by ring] at hk2
  rw [hk1, hk2]
  have hG1 := recip_Gamma_mul_Gamma_one_sub (b - a)
  have hG2 := recip_Gamma_mul_Gamma_one_sub a
  have hG3 := recip_Gamma_mul_Gamma_one_sub b
  rw [show 1 - (b - a) = a - b + 1 by ring] at hG1
  have hg : Gamma (1 - b) ≠ 0 :=
    Gamma_ne_zero fun k h => hb (k + 1) (by push_cast; linear_combination -h)
  have hgb : (Gamma b)⁻¹ = Gamma (1 - b) * (sin (π * b) / π) := by
    rw [← hG3, mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀ hg, mul_one]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [div_eq_mul_inv]
  rw [hgb]
  rw [mul_inv] at hG1 hG2
  have hS1 := exp_sin_connection a b ε hε
  have hS2 := exp_connection_cancel a b ε hε
  set E := exp z
  set Mb := kummerM (b - a) b (-z)
  set Mc := kummerM (1 - a) (2 - b) (-z)
  set Z := z ^ (1 - b)
  linear_combination (-(E * Mb * Gamma (1 - b) * exp (-ε * a * π * I))) * hG1 -
    E * Mb * Gamma (1 - b) * exp (ε * (b - a) * π * I) * hG2 -
    E * Mb * Gamma (1 - b) / π * hS1 -
    E * Mc * Z * Gamma (b - 1) * (Gamma a)⁻¹ * (Gamma (b - a))⁻¹ * hS2

/-- 13.2.36 without the hypothesis on `a - b + 1`. -/
theorem wronskian_shifted_regularized_kummerU_all (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    wronskian (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)
      (kummerU a b) z =
      -(z ^ (-b) * exp z) / Gamma (a - b + 1) := by
  have hz0 := slitPlane_ne_zero hz
  have := integerComplement_nhdsWithin_neBot b
  unfold wronskian
  have hD : ∀ c, HasDerivAt (fun w => w ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} w)
      ((1 - c) * z ^ (-c) * regularizedHGFun {a - c + 1} {2 - c} z +
        z ^ (1 - c) * ((a - c + 1) * regularizedHGFun {a - c + 1 + 1} {2 - c + 1} z)) z := by
    intro c
    have hp := (hasDerivAt_id z).cpow_const (c := 1 - c) hz
    have hm := (differentiableAt_regularizedConfluent (a - c + 1) (2 - c) z).hasDerivAt
    rw [deriv_regularizedConfluent] at hm
    have h := hp.mul hm
    simp only [id, mul_one] at h
    convert h using 2
    ring_nf
  have key : ∀ c, z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * deriv (kummerU a c) z -
      kummerU a c z * deriv (fun w => w ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} w) z =
      z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * deriv (kummerU a c) z -
      kummerU a c z * ((1 - c) * z ^ (-c) * regularizedHGFun {a - c + 1} {2 - c} z +
        z ^ (1 - c) * ((a - c + 1) * regularizedHGFun {a - c + 1 + 1} {2 - c + 1} z)) :=
    fun c => by rw [(hD c).deriv]
  rw [key]
  have hpow : ∀ s : ℂ → ℂ, Continuous s → Tendsto (fun c => z ^ s c) (𝓝[integerComplement] b)
      (𝓝 (z ^ s b)) := fun s hs =>
    ((hs.continuousAt.const_cpow (Or.inl hz0)).tendsto).mono_left nhdsWithin_le_nhds
  have h1 := tendsto_regularizedConfluent_param (fun c => a - c + 1) (fun c => 2 - c)
    (by fun_prop) (by fun_prop) b z (𝓝[integerComplement] b) nhdsWithin_le_nhds
  have h2 := tendsto_regularizedConfluent_param (fun c => a - c + 1 + 1) (fun c => 2 - c + 1)
    (by fun_prop) (by fun_prop) b z (𝓝[integerComplement] b) nhdsWithin_le_nhds
  have hid : Tendsto (fun c : ℂ => c) (𝓝[integerComplement] b) (𝓝 b) := nhdsWithin_le_nhds
  have c1 : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝[integerComplement] b) (𝓝 1) := tendsto_const_nhds
  have ca : Tendsto (fun _ : ℂ => a) (𝓝[integerComplement] b) (𝓝 a) := tendsto_const_nhds
  have hL := (((hpow (fun c => 1 - c) (by fun_prop)).mul h1).mul
    (tendsto_deriv_kummerU a b hz)).sub ((tendsto_kummerU a b hz0).mul
      ((((c1.sub hid).mul (hpow (fun c => -c) (by fun_prop))).mul h1).add
        ((hpow (fun c => 1 - c) (by fun_prop)).mul
          (((ca.sub hid).add c1).mul h2))))
  have hR : Tendsto (fun c : ℂ => -(z ^ (-c) * exp z) / Gamma (a - c + 1))
      (𝓝[integerComplement] b) (𝓝 (-(z ^ (-b) * exp z) / Gamma (a - b + 1))) := by
    have hc : ContinuousAt (fun c : ℂ => z ^ (-c)) b :=
      continuousAt_id.neg.const_cpow (Or.inl hz0)
    have hG : ContinuousAt (fun c : ℂ => (Gamma (a - c + 1))⁻¹) b :=
      (differentiable_one_div_Gamma.continuous.comp
        (by fun_prop : Continuous fun c : ℂ => a - c + 1)).continuousAt.congr
        (Eventually.of_forall fun c => by simp)
    have hcc : ContinuousAt (fun c : ℂ => -(z ^ (-c) * exp z)) b :=
      (hc.mul continuousAt_const).neg
    have := (hcc.mul hG).tendsto.mono_left (nhdsWithin_le_nhds (s := integerComplement))
    convert this using 2 <;> simp [div_eq_mul_inv]
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [← key]
  exact (wronskian_shifted_kummerU_of_mem a hc hz).symm

@[dlmf 13.2.E36]
theorem wronskian_shifted_regularized_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hab : ∀ k : ℕ, a - b + 1 ≠ -k) :
    wronskian (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)
      (kummerU a b) z =
      -(z ^ (-b) * exp z) / Gamma (a - b + 1) := by
  exact wronskian_shifted_regularized_kummerU_all a b hz

/-- **DLMF 13.2.41 in regularized form**, valid for every `b`:
`𝐌(a,b,z) = e^{∓πia}/Γ(b-a) U(a,b,z) + e^{±πi(b-a)}/Γ(a) e^z U(b-a,b,z e^{±πi})`. -/
theorem regularizedHGFun_eq_kummerU_connection (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg ≤ 0 else 0 < z.arg) :
    regularizedHGFun {a} {b} z =
      exp (-(if sign then 1 else -1) * a * π * I) / Gamma (b - a) * kummerU a b z +
        exp ((if sign then 1 else -1) * (b - a) * π * I) / Gamma a *
          exp z * kummerU (b - a) b (exp ((if sign then 1 else -1) * π * I) * z) := by
  have hz0 := slitPlane_ne_zero hz
  set ε : ℂ := if sign then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by cases sign <;> simp [hεdef]
  have hw : exp (ε * π * I) * z = -z := by
    rcases hε with h | h <;> rw [h]
    · rw [one_mul, exp_pi_mul_I]; ring
    · rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; ring
  have hc : ∀ w : ℂ, (-z) ^ w = z ^ w * exp (ε * π * I * w) := by
    have harg := arg_le_pi z
    have harg' := neg_pi_lt_arg z
    refine neg_cpow_of_arg hz0 ε hε ?_ ?_ <;> cases sign <;> simp_all <;> linarith
  rw [hw]
  have hiG : Continuous fun s : ℂ => (Gamma s)⁻¹ := by
    simpa [one_div] using differentiable_one_div_Gamma.continuous
  have hnz : -z ≠ 0 := neg_ne_zero.mpr hz0
  refine eq_of_continuousAt_of_integerComplement
    (f := fun c => regularizedHGFun {a} {c} z)
    (g := fun c => exp (-ε * a * π * I) / Gamma (c - a) * kummerU a c z +
      exp (ε * (c - a) * π * I) / Gamma a * exp z * kummerU (c - a) c (-z)) ?_ ?_ ?_
  · exact (continuous_regularizedConfluent.comp (by fun_prop :
      Continuous fun c : ℂ => (a, c, z))).continuousAt
  · simp only [div_eq_mul_inv]
    refine ContinuousAt.add (ContinuousAt.mul (continuousAt_const.mul
      (hiG.comp (by fun_prop : Continuous fun c : ℂ => c - a)).continuousAt)
      (continuousAt_kummerU_comp continuousAt_const continuousAt_id hz0)) ?_
    refine ContinuousAt.mul ((ContinuousAt.mul (by fun_prop) continuousAt_const).mul
      continuousAt_const) (continuousAt_kummerU_comp (by fun_prop) continuousAt_id hnz)
  · intro c hc'
    have hcz := forall_of_mem_integerComplement hc'
    have hcn : ∀ k : ℕ, c ≠ -k := fun k h => hcz (-k) (by simp [h])
    rw [regularizedConfluent_eq_div_Gamma hcn]
    exact kummerM_div_Gamma_connection_of_not_int a c hcz ε hε (hc _)

/-- DLMF's `U(b-a,b,z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z ≤ 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.2.E41]
theorem kummerM_eq_kummerU_connection (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hsign : if sign then z.arg ≤ 0 else 0 < z.arg) (hb : ∀ k : ℕ, b ≠ -k) :
    kummerM a b z / Gamma b =
      exp (-(if sign then 1 else -1) * a * π * I) / Gamma (b - a) * kummerU a b z +
        exp ((if sign then 1 else -1) * (b - a) * π * I) / Gamma a *
          exp z * kummerU (b - a) b (exp ((if sign then 1 else -1) * π * I) * z) := by
  rw [← regularizedConfluent_eq_div_Gamma hb]
  exact regularizedHGFun_eq_kummerU_connection a b hz sign hsign

/-- Exponential form of a sine jump. -/
theorem exp_sub_exp_neg_mul_I (t : ℂ) :
    exp (t * I) - exp (-t * I) = 2 * I * sin t := by
  rw [sin]
  linear_combination (exp (t * I) - exp (-t * I)) * I_sq

/-- Reciprocal form of Gamma reflection, valid also at integer arguments. -/
theorem sin_pi_mul_eq_recip_Gamma (t : ℂ) :
    sin (π * t) = π / (Gamma t * Gamma (1 - t)) := by
  rw [Gamma_mul_Gamma_one_sub, div_div_eq_mul_div]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The phase algebra shared by the jump identities. -/
theorem exp_weighted_jump (a b u v : ℂ) :
    exp (a * I) * (u - exp (-b * I) * v) -
      exp (-a * I) * (u - exp (b * I) * v) =
        2 * I * sin a * u - 2 * I * sin (a - b) * v := by
  have hp : exp ((a - b) * I) = exp (a * I) * exp (-b * I) := by
    rw [← exp_add]; congr 1; ring
  have hm : exp (-(a - b) * I) = exp (-a * I) * exp (b * I) := by
    rw [← exp_add]; congr 1; ring
  calc _ = (exp (a * I) - exp (-a * I)) * u -
      (exp ((a - b) * I) - exp (-(a - b) * I)) * v := by rw [hp, hm]; ring
    _ = _ := by simp only [exp_sub_exp_neg_mul_I]

/-- The half-turn of U, with its branch recorded in the logarithmic argument. -/
theorem kummerUOnLog_half_turn (a b : ℂ) {z : ℂ} (hz : z ≠ 0) (sign : Bool) :
    kummerUOnLog a b (log z + (if sign then 1 else -1) * π * I) =
      Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (-z) -
        Gamma (b - 1) / Gamma a * z ^ (1 - b) *
          exp (-(if sign then 1 else -1) * b * π * I) *
            kummerM (a - b + 1) (2 - b) (-z) := by
  set s : ℂ := if sign then 1 else -1 with hs
  have he : exp (s * π * I) = -1 := by
    cases sign <;> simp [hs, exp_neg, exp_pi_mul_I]
  have hz' : exp (log z + s * π * I) = -z := by
    rw [exp_add, exp_log hz, he]; ring
  have hp : exp ((1 - b) * (log z + s * π * I)) =
      -z ^ (1 - b) * exp (-s * b * π * I) := by
    rw [show (1 - b) * (log z + s * π * I) =
      log z * (1 - b) + (s * π * I + (-s * b * π * I)) by ring,
      exp_add, exp_add, he, cpow_def_of_ne_zero hz]
    ring
  rw [kummerUOnLog, hz', hp]
  ring

/-- The jump of `U` across the negative axis, with both continuations `z e^{±πi}` taken on
the logarithmic argument plane. `kummerUOnLog` represents `U` there for noninteger `b`. -/
@[dlmf 13.2.E43]
theorem kummerM_eq_kummerU_jump (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hbi : ∀ k : ℤ, b ≠ k) (hab : ∀ k : ℕ, a - b + 1 ≠ -k) :
    2 * π * I * exp (-z) / (Gamma b * Gamma (a - b + 1)) * kummerM (b - a) b z =
      exp (b * π * I) * kummerUOnLog a b (log z + π * I) -
        exp (-b * π * I) * kummerUOnLog a b (log z - π * I) := by
  have hz0 := slitPlane_ne_zero hz
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := not_neg_nat_of_mem_integerComplement
    (mem_integerComplement_of_forall hbi)
  have hGb := Gamma_ne_zero hb
  have hsin := sin_pi_mul_ne_zero_of_mem (mem_integerComplement_of_forall hbi)
  have hG : Gamma (1 - b) * sin (π * b) = π / Gamma b := by
    have h := Gamma_mul_Gamma_one_sub b
    apply (eq_div_iff hGb).mpr
    linear_combination (eq_div_iff hsin).mp h
  have hp := kummerUOnLog_half_turn a b hz0 true
  have hm := kummerUOnLog_half_turn a b hz0 false
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, neg_neg, neg_mul,
    ← sub_eq_add_neg] at hp hm
  rw [hp, hm]
  have ht := exp_sub_exp_neg_mul_I (π * b)
  rw [show (π : ℂ) * b * I = b * π * I by ring,
    show -(π * b) * I = -b * π * I by ring] at ht
  have hM : kummerM a b (-z) = exp (-z) * kummerM (b - a) b z := by
    rw [kummerM_kummer_transform hb, neg_neg]
  calc _ = 2 * I * (Gamma (1 - b) * sin (π * b)) / Gamma (a - b + 1) *
      kummerM a b (-z) := by rw [hG, hM]; ring
    _ = _ := by
      simp only [neg_mul] at ht ⊢
      linear_combination -(Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (-z)) * ht

/-- The U jump identity without nonpole assumptions on the first parameter. -/
theorem kummerU_jump_all (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (hbi : ∀ k : ℤ, b ≠ k) :
    2 * π * I * exp (-z) / (Gamma a * Gamma (a - b + 1)) * kummerU (b - a) b z =
      exp (a * π * I) * kummerUOnLog a b (log z + π * I) -
        exp (-a * π * I) * kummerUOnLog a b (log z - π * I) := by
  have hz0 := slitPlane_ne_zero hz
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := not_neg_nat_of_mem_integerComplement
    (mem_integerComplement_of_forall hbi)
  have hB : ∀ k : ℕ, 2 - b ≠ -(k : ℂ) := fun k hk =>
    hbi (2 + k) (by push_cast; linear_combination -hk)
  have hp := kummerUOnLog_half_turn a b hz0 true
  have hm := kummerUOnLog_half_turn a b hz0 false
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, neg_neg, neg_mul,
    ← sub_eq_add_neg] at hp hm
  have hphase := exp_weighted_jump (a * π) (b * π)
    (Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (-z))
    (Gamma (b - 1) / Gamma a * z ^ (1 - b) * kummerM (a - b + 1) (2 - b) (-z))
  simp only [neg_mul] at hphase
  have hs1 : sin (a * π) = π / (Gamma a * Gamma (1 - a)) := by
    rw [mul_comm a, sin_pi_mul_eq_recip_Gamma]
  have hs2 : sin (a * π - b * π) =
      -π / (Gamma (a - b + 1) * Gamma (b - a)) := by
    have h := sin_pi_mul_eq_recip_Gamma (a - b + 1)
    rw [show (π : ℂ) * (a - b + 1) = (a * π - b * π) + π by ring,
      sin_add_pi, show 1 - (a - b + 1) = b - a by ring] at h
    rw [neg_div]
    linear_combination -h
  have hM : kummerM a b (-z) = exp (-z) * kummerM (b - a) b z := by
    rw [kummerM_kummer_transform hb, neg_neg]
  have hN : kummerM (a - b + 1) (2 - b) (-z) =
      exp (-z) * kummerM (1 - a) (2 - b) z := by
    rw [kummerM_kummer_transform hB, neg_neg]
    congr 2; ring
  rw [hp, hm, kummerU_eq_connection (b - a) b z hbi]
  unfold kummerUConnection
  rw [show b - a - b + 1 = 1 - a by ring]
  symm
  calc
    _ = 2 * I * sin (a * π) *
        (Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (-z)) -
      2 * I * sin (a * π - b * π) *
        (Gamma (b - 1) / Gamma a * z ^ (1 - b) * kummerM (a - b + 1) (2 - b) (-z)) := by
      simp only [neg_mul] at *
      linear_combination hphase
    _ = _ := by rw [hs1, hs2, hM, hN]; ring

/-- The jump of `U` across the negative axis, with both continuations `z e^{±πi}` taken on
the logarithmic argument plane. `kummerUOnLog` represents `U` there for noninteger `b`. -/
@[dlmf 13.2.E44]
theorem kummerU_jump (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (hbi : ∀ k : ℤ, b ≠ k)
    (ha : ∀ k : ℕ, a ≠ -k) (hab : ∀ k : ℕ, a - b + 1 ≠ -k) :
    2 * π * I * exp (-z) / (Gamma a * Gamma (a - b + 1)) * kummerU (b - a) b z =
      exp (a * π * I) * kummerUOnLog a b (log z + π * I) -
        exp (-a * π * I) * kummerUOnLog a b (log z - π * I) := by
  exact kummerU_jump_all a b hz hbi

end DLMF.Confluent
