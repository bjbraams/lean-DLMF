/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.LogSeries

/-!
# Existence and continuity of Tricomi functions

Parameter limits at integer second parameters and joint continuity of Tricomi functions.

Source references and common attribution are retained in
`DLMF.Confluent.BasicProperties`.
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

/-- Identity under the stated parameter and domain assumptions: `regularizedHGFun {a} {(-(n : ℂ))}
z = poch a (n + 1) / (n + 1).factorial * z ^ (n + 1) * kummerM (a + n + 1) (n + 2) z`. -/
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

/-- Identity under the stated parameter and domain assumptions: `kummerU (-(m : ℂ)) b z = (-1 : ℂ)
^ m * poch b m * kummerM (-(m : ℂ)) b z`. -/
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

/-- Formula under the stated hypotheses: `kummerU a (a + n + 1) z = z ^ (-a) * ∑ s ∈ Finset.range
(n + 1), (n.choose s : ℂ) * poch a s * z ^ (-(s : ℂ))`. -/
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

end DLMF.Confluent
end
end
