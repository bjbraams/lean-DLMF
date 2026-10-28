/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.UniformLG

/-!
# Uniform cylinder estimates for negative parameters

Liouville-Green estimates and Temme normalization for negative-parameter parabolic cylinder
functions.

Source references and common attribution are retained in
`DLMF.ParabolicCylinder.UniformLG2`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open Polynomial

/-- A truncated series `∑_{s<N} a_s(t)/u^s`. -/
noncomputable def pcfLG2_ser (a : ℕ → ℝ → ℝ) (N : ℕ) (u t : ℝ) : ℝ := ∑ s ∈ Finset.range N, a s t / u^s

/-- The Liouville–Green series with coefficients `(-1)^s a_s` is `pcfLG2_ser`. -/
lemma pcfLG2_lgSeries_eq (a : ℕ → ℝ → ℝ) (N : ℕ) (u t : ℝ) :
    LiouvilleGreen.lgSeries u (fun s t => (-1)^s * a s t) N t = pcfLG2_ser a N u t := by
  unfold LiouvilleGreen.lgSeries pcfLG2_ser
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, ← mul_pow]; norm_num

/-- The Liouville–Green series with parameter `-u` is `pcfLG2_ser`. -/
lemma pcfLG2_lgSeries_neg_eq (a : ℕ → ℝ → ℝ) (N : ℕ) (u t : ℝ) :
    LiouvilleGreen.lgSeries (-u) a N t = pcfLG2_ser a N u t := by
  unfold LiouvilleGreen.lgSeries pcfLG2_ser
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [neg_pow u s, mul_comm ((-1:ℝ)^s) (u^s), ← div_div, mul_div_assoc, mul_div_assoc,
    ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero s (by norm_num : (-1:ℝ) ≠ 0))]

/-- A truncated series with leading term `1` and bounded coefficients is within `K/u` of `1`. -/
lemma pcfLG2_abs_sum_sub_one_le {N : ℕ} (hN : 1 ≤ N) {f : ℕ → ℝ} (hf0 : f 0 = 1) {K : ℕ → ℝ}
    (hK : ∀ s < N, |f s| ≤ K s) {u : ℝ} (hu : 1 ≤ u) :
    |∑ s ∈ Finset.range N, f s / u^s - 1| ≤ (∑ s ∈ Finset.range N, K s) / u := by
  have h := pcfLG_abs_sum_sub_one_le hN (f := fun s => if s < N then f s else 0)
    (K := fun s => if s < N then K s else 0) (by simp [hf0, show 0 < N by omega])
    (fun s => by split_ifs with hs; exacts [hK s hs, by simp]) hu
  have e1 : ∑ s ∈ Finset.range N, (if s < N then f s else 0) / u^s =
      ∑ s ∈ Finset.range N, f s / u^s :=
    Finset.sum_congr rfl fun s hs => by simp [Finset.mem_range.1 hs]
  have e2 : ∑ s ∈ Finset.range N, (if s < N then K s else 0) = ∑ s ∈ Finset.range N, K s :=
    Finset.sum_congr rfl fun s hs => by simp [Finset.mem_range.1 hs]
  rwa [e1, e2] at h

/-- Termwise derivative of a truncated series. -/
lemma pcfLG2_hasDerivAt_ser {b : ℝ} {a ad : ℕ → ℝ → ℝ} {N : ℕ}
    (ha : ∀ s < N, ∀ t, b < t → HasDerivAt (a s) (ad s t) t) (u : ℝ) {t : ℝ} (ht : b < t) :
    HasDerivAt (fun t => pcfLG2_ser a N u t) (pcfLG2_ser ad N u t) t := by
  unfold pcfLG2_ser
  exact HasDerivAt.fun_sum fun s hs => (ha s (Finset.mem_range.1 hs) t ht).div_const _

/-- **General recessive core.** Let `A > 0` on `(b, ∞)` with `ξ' = A⁻²`, `A → 0`, and let
coefficients `a_s` satisfy the Liouville–Green recursion `A² a_s'' + 2AA' a_s' + AA'' a_s = 2 a_{s+1}'`
with `a_0 = 1`, uniform bounds on `(b, ∞)` and limits `l_s` at `+∞`. Let `U` solve
`U'' = μ⁴ A⁻⁴ U` with `U/(A e^{-μ²ξ}) → H(μ)`. Then for `μ ≥ μ₀` (explicitly), with `u = μ²`,
`U = (H/L) A e^{-uξ} (∑_{s<N} a_s/u^s + ε)`, `L = ∑_{s<N} l_s/u^s`, where
`|ε| ≤ C u^{-N}` and `|A² ε'| ≤ 2 C u^{1-N}`, together with the corresponding formula for `U'`. -/
lemma pcfLG2_core {b : ℝ} {A A1 A2 ξ : ℝ → ℝ}
    (hA : ∀ t, b < t → 0 < A t) (hA1 : ∀ t, b < t → HasDerivAt A (A1 t) t)
    (hA2 : ∀ t, b < t → HasDerivAt A1 (A2 t) t) (hA2c : ContinuousOn A2 (Ioi b))
    (hξ : ∀ t, b < t → HasDerivAt ξ ((A t ^ 2)⁻¹) t)
    (hVi : ∀ c, b < c → IntegrableOn (fun t => |A t * A2 t - (fun _ => (0:ℝ)) t * A t ^ 2|)
      (Ioi c))
    {V0 : ℝ} (hV : ∀ t, b < t → ∫ x in Ioi t, |A x * A2 x - (fun _ => (0:ℝ)) x * A x ^ 2| ≤ V0)
    (hAl : Tendsto A atTop (𝓝 0))
    {N : ℕ} (hN : 1 ≤ N) {a ad ad2 : ℕ → ℝ → ℝ} {l : ℕ → ℝ}
    (ha : ∀ s < N, ∀ t, b < t → HasDerivAt (a s) (ad s t) t)
    (had : ∀ s < N, ∀ t, b < t → HasDerivAt (ad s) (ad2 s t) t)
    (had2 : ∀ s < N, ContinuousOn (ad2 s) (Ioi b))
    (ha0 : ∀ t, a 0 t = 1) (h0 : ∀ t, b < t → ad 0 t = 0)
    (hrec : ∀ s < N, ∀ t, b < t → A t ^ 2 * ad2 s t + 2 * A t * A1 t * ad s t +
      A t * A2 t * a s t = 2 * ad (s+1) t)
    (hNi : ∀ c, b < c → IntegrableOn (fun t => |ad N t|) (Ioi c))
    {I : ℝ} (hI : ∀ t, b < t → ∫ x in Ioi t, |ad N x| ≤ I)
    {K : ℕ → ℝ} (hK : ∀ s < N, ∀ t, b < t → |a s t| ≤ K s)
    (hl : ∀ s < N, Tendsto (a s) atTop (𝓝 (l s)))
    {U U' : ℝ → ℝ → ℂ} {H : ℝ → ℂ}
    (hU : ∀ μ t, b < t → HasDerivAt (U μ) (U' μ t) t)
    (hU' : ∀ μ t, b < t → HasDerivAt (U' μ) (((μ^4 * (A t ^ 4)⁻¹ : ℝ) : ℂ) * U μ t) t)
    (hUl : ∀ μ, 1 ≤ μ → Tendsto (fun t => U μ t / ((A t * Real.exp (-(μ^2 * ξ t)) : ℝ) : ℂ))
      atTop (𝓝 (H μ)))
    {C μ₀ : ℝ} (hC : I * Real.exp (V0/2) ≤ C) (hμ₀ : 1 ≤ μ₀)
    (hμ₀C : 2 * ((∑ s ∈ Finset.range N, K s) + C) ≤ μ₀^2) :
    ∀ μ, μ₀ ≤ μ →
      |pcfLG2_ser (fun s _ => l s) N (μ^2) 0 - 1| ≤ 1/2 ∧
      ∃ ε ε' : ℝ → ℝ, ∀ t, b < t →
        |ε t| ≤ C / (μ^2)^N ∧ |A t ^ 2 * ε' t| ≤ 2 * C / (μ^2)^(N-1) ∧
        U μ t = H μ / (pcfLG2_ser (fun s _ => l s) N (μ^2) 0 : ℂ) *
          ((A t * Real.exp (-(μ^2 * ξ t)) * (pcfLG2_ser a N (μ^2) t + ε t) : ℝ) : ℂ) ∧
        U' μ t = H μ / (pcfLG2_ser (fun s _ => l s) N (μ^2) 0 : ℂ) *
          ((Real.exp (-(μ^2 * ξ t)) * ((A1 t - μ^2 * (A t)⁻¹) * (pcfLG2_ser a N (μ^2) t + ε t) +
            A t * (pcfLG2_ser ad N (μ^2) t + ε' t)) : ℝ) : ℂ) := by
  intro μ hμ
  have hμ1 : 1 ≤ μ := hμ₀.trans hμ
  have hμ0 : 0 < μ := by linarith
  have hμμ : μ₀^2 ≤ μ^2 := by nlinarith
  set u := μ^2 with hu
  have hu1 : 1 ≤ u := by nlinarith
  have hu0 : 0 < u := by linarith
  have hb1 : b < b + 1 := by linarith
  have hK0 : ∀ s < N, 0 ≤ K s := fun s hs => (abs_nonneg _).trans (hK s hs (b+1) hb1)
  set KS := ∑ s ∈ Finset.range N, K s with hKSdef
  have hKS : 0 ≤ KS := Finset.sum_nonneg fun s hs => hK0 s (Finset.mem_range.1 hs)
  have hI0 : 0 ≤ I :=
    (setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _).trans (hI _ hb1)
  have hV00 : 0 ≤ V0 :=
    (setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _).trans (hV _ hb1)
  have hC0 : 0 ≤ C := (by positivity : 0 ≤ I * Real.exp (V0/2)).trans hC
  have huK : 2*(KS+C) ≤ u := hμ₀C.trans hμμ
  have hsmall : (KS + C)/u ≤ 1/2 := by rw [div_le_iff₀ hu0]; linarith
  have hKSu : KS/u ≤ 1/2 := le_trans (div_le_div_of_nonneg_right (by linarith) hu0.le) hsmall
  have hser : ∀ t, b < t → |pcfLG2_ser a N u t - 1| ≤ KS/u := fun t ht =>
    pcfLG2_abs_sum_sub_one_le hN (ha0 t) (fun s hs => hK s hs t ht) hu1
  have hlK : ∀ s < N, |l s| ≤ K s := fun s hs =>
    le_of_tendsto ((hl s hs).abs) ((eventually_gt_atTop b).mono fun t ht => hK s hs t ht)
  have hl0 : l 0 = 1 := by
    have h := hl 0 hN
    rw [show a 0 = fun _ => 1 from funext ha0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  set L := pcfLG2_ser (fun s _ => l s) N u 0 with hLdef
  have hS : |L - 1| ≤ KS/u := pcfLG2_abs_sum_sub_one_le hN hl0 hlK hu1
  have hL0 : L ≠ 0 := by
    have := abs_le.1 (hS.trans hKSu); intro h; rw [h] at this; linarith [this.1]
  have hL0' : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
  -- the Liouville–Green solution
  obtain ⟨ε, ε', w', HLG⟩ := LiouvilleGreen.exists_solution_expansion_exp (a := b) hu0
    (A := A) (A' := A1) (A'' := A2) (ξ := ξ) (g := fun _ => 0)
    (fun x hx => (hA x hx).ne') hA1 hA2 hA2c continuousOn_const hξ hVi (n := N)
    (As := fun s t => (-1)^s * a s t) (Ad := fun s t => (-1)^s * ad s t)
    (Ad2 := fun s t => (-1)^s * ad2 s t)
    (fun s hs x hx => (ha s hs x hx).const_mul _)
    (fun s hs x hx => (had s hs x hx).const_mul _)
    (fun s hs => continuousOn_const.mul (had2 s hs))
    (fun x hx => by simp [h0 x hx])
    (fun s hs x hx => by
      have := hrec s hs x hx
      simp only [zero_mul, sub_zero]
      rw [pow_succ]
      linear_combination (-1:ℝ)^s * this)
    (fun c' hc' => by simpa [abs_mul] using hNi c' hc')
  simp only [pcfLG2_lgSeries_eq] at HLG
  -- error bounds
  have hεb : ∀ t, b < t → |ε t| ≤ (∫ x in Ioi t, |ad N x|) * Real.exp (V0/2) / u^N ∧
      |A t ^ 2 * ε' t| ≤ 2 * u * ((∫ x in Ioi t, |ad N x|) * Real.exp (V0/2) / u^N) := by
    intro t ht
    have h4 := (HLG t ht).2.2.2.1
    have h5 := (HLG t ht).2.2.2.2
    set Vt := ∫ x in Ioi t, |A x * A2 x - 0 * A x ^ 2| with hVt
    have e1 : Real.exp (Vt / (2*u)) ≤ Real.exp (V0/2) := by
      refine Real.exp_le_exp.2 ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 0 ≤ Vt := setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _
      have := hV t ht
      nlinarith
    have hab : (fun x => |(fun s t => (-1:ℝ)^s * ad s t) N x|) = fun x => |ad N x| := by
      funext x; simp [abs_mul]
    simp only [hab] at h4 h5
    have hnn : 0 ≤ ∫ x in Ioi t, |ad N x| :=
      setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _
    constructor
    · calc |ε t| ≤ (∫ x in Ioi t, |ad N x|) / u^N * Real.exp (Vt/(2*u)) := h4
        _ ≤ (∫ x in Ioi t, |ad N x|) / u^N * Real.exp (V0/2) := by gcongr
        _ = _ := by ring
    · calc |A t ^ 2 * ε' t| ≤ 2 * u * ((∫ x in Ioi t, |ad N x|) / u^N) *
            Real.exp (Vt/(2*u)) := h5
        _ ≤ 2 * u * ((∫ x in Ioi t, |ad N x|) / u^N) * Real.exp (V0/2) := by gcongr
        _ = _ := by ring
  have hpow : u^N = u^(N-1) * u := by rw [← pow_succ, Nat.sub_add_cancel hN]
  have hεC : ∀ t, b < t → |ε t| ≤ C / u^N ∧ |A t ^ 2 * ε' t| ≤ 2 * C / u^(N-1) := by
    intro t ht
    have h1 : (∫ x in Ioi t, |ad N x|) * Real.exp (V0/2) ≤ C :=
      (mul_le_mul_of_nonneg_right (hI t ht) (Real.exp_pos _).le).trans hC
    have hp : 0 < u^N := by positivity
    obtain ⟨e1, e2⟩ := hεb t ht
    refine ⟨e1.trans (div_le_div_of_nonneg_right h1 hp.le), e2.trans ?_⟩
    have : 2 * u * ((∫ x in Ioi t, |ad N x|) * Real.exp (V0/2) / u^N) ≤ 2 * u * (C / u^N) := by
      gcongr
    refine this.trans (le_of_eq ?_)
    rw [hpow]; field_simp
  have hεC1 : ∀ t, b < t → |ε t| ≤ C / u := fun t ht => by
    refine (hεC t ht).1.trans (div_le_div_of_nonneg_left hC0 hu0 ?_)
    calc u = u^1 := (pow_one u).symm
      _ ≤ u^N := pow_le_pow_right₀ hu1 hN
  have hsum : ∀ t, b < t → |pcfLG2_ser a N u t + ε t - 1| ≤ 1/2 := by
    intro t ht
    have := hser t ht; have := hεC1 t ht
    have : |pcfLG2_ser a N u t + ε t - 1| ≤ |pcfLG2_ser a N u t - 1| + |ε t| := by
      rw [show pcfLG2_ser a N u t + ε t - 1 = (pcfLG2_ser a N u t - 1) + ε t by ring]
      exact abs_add_le _ _
    have : KS/u + C/u ≤ 1/2 := by rw [← add_div]; exact hsmall
    linarith
  have hpos : ∀ t, b < t → 1/2 ≤ pcfLG2_ser a N u t + ε t := fun t ht => by
    have := abs_le.1 (hsum t ht); linarith [this.1]
  set W : ℝ → ℝ := fun t => A t * Real.exp (-(u * ξ t)) * (pcfLG2_ser a N u t + ε t)
    with hWdef
  set q : ℝ → ℝ := fun t => u^2 * (A t ^ 4)⁻¹ + (fun _ => (0:ℝ)) t with hq
  have hAe : ∀ t, b < t → 0 < A t * Real.exp (-(u * ξ t)) := fun t ht =>
    mul_pos (hA t ht) (Real.exp_pos _)
  have hξm : ∀ x t, b < x → x ≤ t → ξ x ≤ ξ t := fun x t hx hxt =>
    LiouvilleGreen.lg_le_of_hasDerivAt_nonneg hξ (fun y _ => inv_nonneg.2 (sq_nonneg _)) hx hxt
  -- `W → 0`
  have hWl : Tendsto W atTop (𝓝 0) := by
    have hb : Tendsto (fun t => (3/2 * Real.exp (-(u * ξ (b+1)))) * A t) atTop (𝓝 0) := by
      simpa using hAl.const_mul (3/2 * Real.exp (-(u * ξ (b+1))))
    refine squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_gt_atTop b] with t ht
      exact (mul_pos (hAe t ht) (by linarith [hpos t ht])).le
    · filter_upwards [eventually_ge_atTop (b+1)] with t ht
      have htb : b < t := by linarith
      have h1 : Real.exp (-(u * ξ t)) ≤ Real.exp (-(u * ξ (b+1))) :=
        Real.exp_le_exp.2 (by nlinarith [hξm (b+1) t hb1 ht])
      have h2 : pcfLG2_ser a N u t + ε t ≤ 3/2 := by
        have := abs_le.1 (hsum t htb); linarith [this.2]
      have hA' := (hA t htb).le
      simp only [hWdef]
      calc A t * Real.exp (-(u * ξ t)) * (pcfLG2_ser a N u t + ε t)
          ≤ A t * Real.exp (-(u * ξ (b+1))) * (3/2) := by
            gcongr
            linarith [hpos t htb]
        _ = 3/2 * Real.exp (-(u * ξ (b+1))) * A t := by ring
  -- `ε → 0` and the limit of the series
  have hεl : Tendsto ε atTop (𝓝 0) := by
    have hb : Tendsto (fun t => (∫ x in Ioi t, |ad N x|) * Real.exp (V0/2) / u^N) atTop (𝓝 0) := by
      simpa using ((LiouvilleGreen.lg_tendsto_integral_Ioi (hNi (b+1) hb1)).mul_const
        (Real.exp (V0/2))).div_const (u^N)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop b] with t ht
    rw [Real.norm_eq_abs]; exact (hεb t ht).1
  have hserl : Tendsto (fun t => pcfLG2_ser a N u t) atTop (𝓝 L) :=
    tendsto_finsetSum _ fun s hs => (hl s (Finset.mem_range.1 hs)).div_const _
  have hsl : Tendsto (fun t => ((pcfLG2_ser a N u t + ε t : ℝ) : ℂ)) atTop (𝓝 (L : ℂ)) := by
    have := (hserl.add hεl); rw [add_zero] at this
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hUl' : Tendsto (fun t => U μ t / ((A t * Real.exp (-(u * ξ t)) : ℝ) : ℂ)) atTop
      (𝓝 (H μ)) := hUl μ hμ1
  have hlim : Tendsto (fun t : ℝ => U μ t / (W t : ℂ)) atTop (𝓝 (H μ / L)) := by
    refine (hUl'.div hsl hL0').congr' ?_
    filter_upwards [eventually_gt_atTop b] with t ht
    simp only [Pi.div_apply, hWdef]
    push_cast
    rw [div_div]
  -- identification with `U`
  obtain ⟨κ, hκ⟩ := pcfLG_eq_mul_of_tendsto (b := b) (q := q) (U := U μ) (U' := U' μ)
    (W := W) (W' := w') (fun t ht => hU μ t ht)
    (fun t ht => (hU' μ t ht).congr_deriv (by simp only [hq, hu]; push_cast; ring))
    (fun t ht => (HLG t ht).2.1) (fun t ht => (HLG t ht).2.2.1)
    (fun t ht => (mul_pos (hAe t ht) (by linarith [hpos t ht])).ne') hWl hlim
  have hκL : κ * L = H μ := by
    refine tendsto_nhds_unique ((hsl.const_mul κ).congr' ?_) hUl'
    filter_upwards [eventually_gt_atTop b] with t ht
    have hne : ((A t * Real.exp (-(u * ξ t)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (hAe t ht).ne'
    rw [hκ t ht]
    simp only [hWdef]
    push_cast
    have hA0 : (A t : ℂ) ≠ 0 := by exact_mod_cast (hA t ht).ne'
    field_simp
  have hκ' : κ = H μ / L := by rw [← hκL]; field_simp
  refine ⟨hS.trans hKSu, ε, ε', fun t ht => ⟨(hεC t ht).1, (hεC t ht).2, ?_, ?_⟩⟩
  · rw [hκ t ht, hκ']
  · -- the derivative
    have hWd : HasDerivAt W (Real.exp (-(u * ξ t)) * ((A1 t - u * (A t)⁻¹) *
        (pcfLG2_ser a N u t + ε t) + A t * (pcfLG2_ser ad N u t + ε' t))) t := by
      have he := ((hξ t ht).const_mul u).neg.exp
      have hs := (pcfLG2_hasDerivAt_ser ha u ht).add (HLG t ht).1
      have := ((hA1 t ht).mul he).mul hs
      convert this using 1
      have hA0 : A t ≠ 0 := (hA t ht).ne'
      simp only [Pi.add_apply, Pi.neg_apply, Pi.mul_apply]
      field_simp
      ring
    have hw := (HLG t ht).2.1.unique hWd
    have hUd : HasDerivAt (U μ) (κ * ((w' t : ℝ) : ℂ)) t := by
      refine (((HLG t ht).2.1.ofReal_comp).const_mul κ).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht] with y hy
      exact hκ y hy
    rw [(hU μ t ht).unique hUd, hκ', hw]

/-! ### Temme's form of the expansion (DLMF 12.10.31) -/

/-- `p(t) = (t²-1)^{-1/2}`. -/
noncomputable def pcfLG2_p (t : ℝ) : ℝ := (t^2-1) ^ (-(1/2):ℝ)

/-- `p(t) > 0` for `t > 1`. -/
lemma pcfLG2_p_pos {t : ℝ} (ht : 1 < t) : 0 < pcfLG2_p t :=
  Real.rpow_pos_of_pos (by nlinarith) _

/-- Powers of `p` as real powers of `t²-1`. -/
lemma pcfLG2_p_pow (n : ℕ) {t : ℝ} (ht : 1 < t) : pcfLG2_p t ^ n = (t^2-1) ^ (-(n/2:ℝ)) := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfLG2_p, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]; ring_nf

/-- `p² (t²-1) = 1`. -/
lemma pcfLG2_p_sq_mul {t : ℝ} (ht : 1 < t) : pcfLG2_p t ^ 2 * (t^2-1) = 1 := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfLG2_p_pow 2 ht, show -((2:ℕ)/2:ℝ) = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- `τ(t) = (t p(t) - 1)/2` (DLMF 12.10.32). -/
lemma pcfLG2_tau_eq {t : ℝ} (ht : 1 < t) : pcfTau t = (t * pcfLG2_p t - 1)/2 := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfTau, pcfLG2_p, Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]; ring

/-- `p' = -t p³`. -/
lemma pcfLG2_hasDerivAt_p {t : ℝ} (ht : 1 < t) :
    HasDerivAt pcfLG2_p (-t * pcfLG2_p t ^ 3) t := by
  have hy : 0 < t^2-1 := by nlinarith
  have h1 : HasDerivAt (fun t : ℝ => t^2-1) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).sub_const 1
  have := h1.rpow_const (p := -(1/2)) (Or.inl hy.ne')
  rw [pcfLG2_p_pow 3 ht]
  refine this.congr_deriv ?_
  rw [show (-(1/2):ℝ) - 1 = -((3:ℕ)/2:ℝ) by norm_num]; ring

/-- `τ' = -p³/2`. -/
lemma pcfLG2_hasDerivAt_tau {t : ℝ} (ht : 1 < t) :
    HasDerivAt pcfTau (-(pcfLG2_p t ^ 3)/2) t := by
  have h := (((hasDerivAt_id' t).mul (pcfLG2_hasDerivAt_p ht)).sub_const 1).div_const 2
  have hev : pcfTau =ᶠ[𝓝 t] fun x => (x * pcfLG2_p x - 1)/2 := by
    filter_upwards [Ioi_mem_nhds ht] with x hx; exact pcfLG2_tau_eq hx
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  have hr := pcfLG2_p_sq_mul ht
  linear_combination (-(pcfLG2_p t)/2) * hr

/-- `A² = p` for `A = (t²-1)^{-1/4}`. -/
lemma pcfLG2_A_sq {t : ℝ} (ht : 1 < t) : pcfLG_A t ^ 2 = pcfLG2_p t := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfLG_A, pcfLG2_p, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num

/-- `A A' = -(t/2) p³`. -/
lemma pcfLG2_A_mul_A1 {t : ℝ} (ht : 1 < t) :
    pcfLG_A t * pcfLG_A1 t = -(t/2) * pcfLG2_p t ^ 3 := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfLG2_p_pow 3 ht, pcfLG_A, pcfLG_A1, mul_left_comm,
    pcfLG_rpow_mul hy (c := -((3:ℕ)/2:ℝ)) (by norm_num)]

/-- `A A'' = (3t²+2)/4 · p⁵`. -/
lemma pcfLG2_A_mul_A2 {t : ℝ} (ht : 1 < t) :
    pcfLG_A t * pcfLG_A2 t = (3*t^2+2)/4 * pcfLG2_p t ^ 5 := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfLG2_p_pow 5 ht, pcfLG_A, pcfLG_A2, mul_left_comm,
    pcfLG_rpow_mul hy (c := -((5:ℕ)/2:ℝ)) (by norm_num)]

/-- `τ(τ+1) = p²/4`. -/
lemma pcfLG2_tau_mul {t : ℝ} (ht : 1 < t) :
    pcfTau t * (pcfTau t + 1) = pcfLG2_p t ^ 2 / 4 := by
  rw [pcfLG2_tau_eq ht]; linear_combination (pcfLG2_p_sq_mul ht)/4

/-- `τ(t) ≥ 0` for `t > 1`. -/
lemma pcfLG2_tau_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ pcfTau t := by
  have hr := pcfLG2_p_sq_mul ht
  have hp := pcfLG2_p_pos ht
  rw [pcfLG2_tau_eq ht]
  have h1 : 1 ≤ (t * pcfLG2_p t)^2 := by nlinarith
  have h2 : 0 < t * pcfLG2_p t := by positivity
  nlinarith

/-- `τ(t) ≤ p(t)/2` for `t > 1`. -/
lemma pcfLG2_tau_le {t : ℝ} (ht : 1 < t) : pcfTau t ≤ pcfLG2_p t / 2 := by
  have h1 := pcfLG2_tau_mul ht
  have h2 := pcfLG2_tau_nonneg ht
  have h3 := pcfLG2_p_pos ht
  nlinarith

/-- `p` is antitone on `(1, ∞)`. -/
lemma pcfLG2_p_anti {c t : ℝ} (hc : 1 < c) (ht : c ≤ t) : pcfLG2_p t ≤ pcfLG2_p c :=
  Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith) (by norm_num)

/-- `p(t) → 0` as `t → ∞`. -/
lemma pcfLG2_tendsto_p : Tendsto pcfLG2_p atTop (𝓝 0) := by
  have hy : Tendsto (fun t : ℝ => t^2-1) atTop atTop := by
    have := (tendsto_pow_atTop (two_ne_zero (α := ℕ))).atTop_add
      (tendsto_const_nhds (x := (-1:ℝ)))
    simpa [sub_eq_add_neg] using this
  exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).comp hy

/-- `τ(t) → 0` as `t → ∞`. -/
lemma pcfLG2_tendsto_tau : Tendsto pcfTau atTop (𝓝 0) := by
  have hb : Tendsto (fun t => pcfLG2_p t / 2) atTop (𝓝 0) := by
    simpa using pcfLG2_tendsto_p.div_const 2
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_gt_atTop 1] with t ht using pcfLG2_tau_nonneg ht
  · filter_upwards [eventually_gt_atTop 1] with t ht using pcfLG2_tau_le ht

/-- A polynomial is bounded on `[0, M]`. -/
lemma pcfLG2_poly_bound (P : Polynomial ℝ) (M : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ Icc 0 M, |P.eval x| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0:ℝ)) (b := M)).exists_bound_of_continuousOn
    P.continuous.continuousOn
  exact ⟨max K 0, le_max_right _ _, fun x hx => (hK x hx).trans (le_max_left _ _)⟩

/-- `φ_s(0) = 0` for `s ≥ 1`. -/
lemma pcfLG2_temme_eval_zero (s : ℕ) : (pcfTemmePoly (s+1)).eval 0 = 0 := by
  rw [pcfTemmePoly]; simp [eval_zero_pcfPolyPrimitive]

/-- The differentiated Temme recursion (from DLMF 12.10.33). -/
lemma pcfLG2_temme_deriv_succ (s : ℕ) (x : ℝ) : (derivative (pcfTemmePoly (s+1))).eval x =
    -4*x^2*(x+1)^2*(derivative (derivative (pcfTemmePoly s))).eval x -
      8*x*(x+1)*(2*x+1)*(derivative (pcfTemmePoly s)).eval x -
      1/4*(20*x^2+20*x+3)*(pcfTemmePoly s).eval x := by
  rw [pcfTemmePoly]
  simp only [derivative_sub, derivative_mul, derivative_C, derivative_X, derivative_pow,
    derivative_add, derivative_one, derivative_pcfPolyPrimitive]
  simp
  ring

/-- Temme's coefficient `φ_s(τ(t))`. -/
noncomputable def pcfLG2_Ta (s : ℕ) (t : ℝ) : ℝ := (pcfTemmePoly s).eval (pcfTau t)
/-- Its derivative. -/
noncomputable def pcfLG2_Tad (s : ℕ) (t : ℝ) : ℝ :=
  (derivative (pcfTemmePoly s)).eval (pcfTau t) * (-(pcfLG2_p t ^ 3)/2)
/-- Its second derivative. -/
noncomputable def pcfLG2_Tad2 (s : ℕ) (t : ℝ) : ℝ :=
  (derivative (derivative (pcfTemmePoly s))).eval (pcfTau t) * (pcfLG2_p t ^ 6/4) +
    (derivative (pcfTemmePoly s)).eval (pcfTau t) * (3/2 * t * pcfLG2_p t ^ 5)

/-- Derivative of `φ_s(τ(t))`. -/
lemma pcfLG2_hasDerivAt_Ta (s : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (pcfLG2_Ta s) (pcfLG2_Tad s t) t :=
  ((pcfTemmePoly s).hasDerivAt (pcfTau t)).comp t (pcfLG2_hasDerivAt_tau ht)

/-- Second derivative of `φ_s(τ(t))`. -/
lemma pcfLG2_hasDerivAt_Tad (s : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (pcfLG2_Tad s) (pcfLG2_Tad2 s t) t := by
  have h1 := ((derivative (pcfTemmePoly s)).hasDerivAt (pcfTau t)).comp t
    (pcfLG2_hasDerivAt_tau ht)
  have h2 := (((pcfLG2_hasDerivAt_p ht).pow 3).neg).div_const 2
  refine (h1.mul h2).congr_deriv ?_
  simp only [pcfLG2_Tad2, Function.comp]
  norm_num
  ring

/-- Continuity of the second derivative of `φ_s(τ(t))`. -/
lemma pcfLG2_continuousOn_Tad2 (s : ℕ) : ContinuousOn (pcfLG2_Tad2 s) (Ioi 1) := by
  intro t ht
  have hp := (pcfLG2_hasDerivAt_p ht).continuousAt
  have hτ := (pcfLG2_hasDerivAt_tau ht).continuousAt
  have hP : ∀ Q : Polynomial ℝ, ContinuousAt (fun x => Q.eval (pcfTau x)) t := fun Q =>
    Q.continuous.continuousAt.comp hτ
  have hl : ContinuousAt (fun x : ℝ => 3/2 * x) t := continuousAt_const.mul continuousAt_id
  exact (((hP _).mul ((hp.pow 6).div_const 4)).add
    ((hP _).mul (hl.mul (hp.pow 5)))).continuousWithinAt

/-- **The Liouville–Green recursion for Temme's coefficients** `φ_s(τ(t))`, with `A = (t²-1)^{-1/4}`. -/
lemma pcfLG2_temme_rec (s : ℕ) {t : ℝ} (ht : 1 < t) :
    pcfLG_A t ^ 2 * pcfLG2_Tad2 s t + 2 * pcfLG_A t * pcfLG_A1 t * pcfLG2_Tad s t +
      pcfLG_A t * pcfLG_A2 t * pcfLG2_Ta s t = 2 * pcfLG2_Tad (s+1) t := by
  have e1 := pcfLG2_A_sq ht
  have e2 := pcfLG2_A_mul_A1 ht
  have e3 := pcfLG2_A_mul_A2 ht
  have hr := pcfLG2_p_sq_mul ht
  have hpoly := pcfLG2_temme_deriv_succ s (pcfTau t)
  simp only [pcfLG2_Ta, pcfLG2_Tad, pcfLG2_Tad2] at *
  rw [pcfLG2_tau_eq ht] at hpoly ⊢
  set p := pcfLG2_p t
  set F0 := (pcfTemmePoly s).eval ((t * p - 1)/2)
  set F1 := (derivative (pcfTemmePoly s)).eval ((t * p - 1)/2)
  set F2 := (derivative (derivative (pcfTemmePoly s))).eval ((t * p - 1)/2)
  linear_combination (F2 * (p^6/4) + F1 * (3/2 * t * p^5)) * e1 +
    2 * (F1 * (-(p^3)/2)) * e2 + F0 * e3 + p^3 * hpoly +
    (-p^3*(2*F0 + 8*F1*p*t + F2*p^2*t^2 + F2*p^2 - F2)/4) * hr

/-- The Temme series tends to `1` at `t = ∞`: `∑_{s<N} φ_s(0) u^{-s} = 1`. -/
lemma pcfLG2_temme_L {N : ℕ} (hN : 1 ≤ N) (u : ℝ) :
    pcfLG2_ser (fun s _ => (pcfTemmePoly s).eval 0) N u 0 = 1 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  unfold pcfLG2_ser
  rw [Finset.sum_range_succ']
  simp only [pcfLG2_temme_eval_zero, zero_div, Finset.sum_const_zero, zero_add,
    show pcfTemmePoly 0 = 1 from rfl, eval_one, pow_zero, div_one]

/-- The complex Temme series is the real series `pcfLG2_ser`. -/
lemma pcfLG2_sum_temme_eq (N : ℕ) (μ t : ℝ) :
    ∑ s ∈ Finset.range N, (((pcfTemmePoly s).eval (pcfTau t) : ℝ) : ℂ) / (μ:ℂ)^(2*s) =
      (pcfLG2_ser pcfLG2_Ta N (μ^2) t : ℂ) := by
  rw [pcfLG2_ser]; push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pow_mul]; rfl

/-- Bound `|d/dt φ_N(τ(t))| ≤ K'/2 · (t²-1)^{-3/2}`. -/
lemma pcfLG2_abs_Tad_le {N : ℕ} {M K' : ℝ}
    (hK' : ∀ x ∈ Icc 0 M, |(derivative (pcfTemmePoly N)).eval x| ≤ K') {t : ℝ} (ht : 1 < t)
    (hτ : pcfTau t ∈ Icc 0 M) :
    |pcfLG2_Tad N t| ≤ K'/2 * |(1 : Polynomial ℝ).eval t * (t^2-1) ^ (-(3/2:ℝ))| := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfLG2_Tad, eval_one, one_mul, abs_mul, pcfLG2_p_pow 3 ht,
    abs_div, abs_neg, abs_two, abs_of_pos (Real.rpow_pos_of_pos hy _),
    abs_of_pos (Real.rpow_pos_of_pos hy _)]
  have := hK' _ hτ
  have h0 : 0 ≤ (t^2-1) ^ (-((3:ℕ)/2:ℝ)) := (Real.rpow_pos_of_pos hy _).le
  rw [show (-((3:ℕ)/2:ℝ)) = -(3/2:ℝ) by norm_num] at h0 ⊢
  nlinarith

/-- **Temme's form of the uniform expansion** (DLMF 12.10.31), proved through the general
recessive core with coefficients `φ_s(τ(t))`. -/
@[dlmf 12.10.E31]
theorem pcfU_temme_uniform {δ : ℝ} (hδ : 0 < δ) :
    HasCylinderUniformExpansion (fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2)/(pcfH μ*exp (-μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ))) (fun s t => (((pcfTemmePoly s).eval (pcfTau t):ℝ):ℂ)) (Ici (1+δ)) := by
  set b : ℝ := 1 + δ/2 with hbdef
  have hb : 1 < b := by linarith
  have key : ∀ N : ℕ, 1 ≤ N → (fun p : ℝ × ℝ => pcfU (-p.1^2/2) (p.1*p.2*Real.sqrt 2) /
      (pcfH p.1 * exp (-p.1^2*pcfXi p.2) / (p.2^2-1:ℂ)^(1/4:ℂ)) -
      ∑ s ∈ Finset.range N, (((pcfTemmePoly s).eval (pcfTau p.2):ℝ):ℂ) / (p.1:ℂ)^(2*s))
      =O[pcfUniformFilter (Ici (1+δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) := by
    intro N hN
    set M := pcfLG2_p b / 2
    have hτb : ∀ t, b < t → pcfTau t ∈ Icc 0 M := fun t ht => by
      have ht1 : 1 < t := hb.trans ht
      exact ⟨pcfLG2_tau_nonneg ht1, (pcfLG2_tau_le ht1).trans
        (div_le_div_of_nonneg_right (pcfLG2_p_anti hb ht.le) (by norm_num))⟩
    choose K hK0 hK using fun s => pcfLG2_poly_bound (pcfTemmePoly s) M
    obtain ⟨K', hK'0, hK'⟩ := pcfLG2_poly_bound (derivative (pcfTemmePoly N)) M
    have hP1 : (1 : Polynomial ℝ).natDegree ≤ 0 := by simp
    have hint1 := fun c (hc : 1 < c) => pcfLG_integrableOn_poly_rpow 1 hP1 (e := 3/2)
      (by norm_num) (by norm_num) hc
    obtain ⟨J, hJ0, hJ⟩ := pcfLG_tail_poly_rpow 1 hP1 (e := 3/2) (by norm_num) (by norm_num) hb
    have hNi : ∀ c, b < c → IntegrableOn (fun t => |pcfLG2_Tad N t|) (Ioi c) := by
      intro c hc
      refine Integrable.mono' ((hint1 c (hb.trans hc)).const_mul (K'/2)) ?_
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
      · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
        have ht1 : 1 < t := hb.trans (hc.trans ht)
        exact (pcfLG2_hasDerivAt_Ta N ht1 |> fun _ =>
          (pcfLG2_hasDerivAt_Tad N ht1).continuousAt.abs).continuousWithinAt
      · rw [Real.norm_eq_abs, abs_abs]
        have ht' : b < t := hc.trans ht
        exact pcfLG2_abs_Tad_le hK' (hb.trans ht') (hτb t ht')
    set I := K'/2 * J
    have hI : ∀ t, b < t → ∫ x in Ioi t, |pcfLG2_Tad N x| ≤ I := by
      intro t ht
      calc ∫ x in Ioi t, |pcfLG2_Tad N x|
          ≤ ∫ x in Ioi t, K'/2 * |(1 : Polynomial ℝ).eval x * (x^2-1) ^ (-(3/2:ℝ))| := by
            refine setIntegral_mono_on (hNi t ht) ((hint1 t (hb.trans ht)).const_mul _)
              measurableSet_Ioi fun x hx => ?_
            have hx' : b < x := ht.trans hx
            exact pcfLG2_abs_Tad_le hK' (hb.trans hx') (hτb x hx')
        _ = K'/2 * ∫ x in Ioi t, |(1 : Polynomial ℝ).eval x * (x^2-1) ^ (-(3/2:ℝ))| :=
            integral_const_mul _ _
        _ ≤ K'/2 * (J * t ^ (((0:ℕ):ℝ) - 2*(3/2) + 1)) := by
            gcongr; exact hJ t ht.le
        _ ≤ I := by
            have : t ^ (((0:ℕ):ℝ) - 2*(3/2) + 1) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
            have : J * t ^ (((0:ℕ):ℝ) - 2*(3/2) + 1) ≤ J := by nlinarith
            simp only [I]; gcongr
    obtain ⟨V0, hV00, hV⟩ := pcfLG_tail_V hb
    set C := I * Real.exp (V0/2) with hCdef
    set KS := ∑ s ∈ Finset.range N, K s
    have hKS : 0 ≤ KS := Finset.sum_nonneg fun s _ => hK0 s
    have hC0 : 0 ≤ C := by positivity
    set μ₀ := max 1 (2*(KS+C)+1)
    have hμ₀ : 1 ≤ μ₀ := le_max_left _ _
    have hμ₀C : 2*((∑ s ∈ Finset.range N, K s) + C) ≤ μ₀^2 := by
      have := le_max_right 1 (2*(KS+C)+1); nlinarith
    have hcore := pcfLG2_core (b := b) (A := pcfLG_A) (A1 := pcfLG_A1) (A2 := pcfLG_A2)
      (ξ := pcfXi) (fun t ht => pcfLG_A_pos (hb.trans ht))
      (fun t ht => pcfLG_hasDerivAt_A (hb.trans ht))
      (fun t ht => pcfLG_hasDerivAt_A1 (hb.trans ht))
      (pcfLG_continuousOn_A2.mono (Ioi_subset_Ioi hb.le))
      (fun t ht => by rw [pcfLG_A_sq_recip (hb.trans ht)]; exact pcfLG_hasDerivAt_xi (hb.trans ht))
      (fun c hc => pcfLG_integrableOn_V (hb.trans hc)) (fun t ht => hV t ht.le)
      pcfLG_tendsto_A hN (a := pcfLG2_Ta) (ad := pcfLG2_Tad) (ad2 := pcfLG2_Tad2)
      (l := fun s => (pcfTemmePoly s).eval 0)
      (fun s _ t ht => pcfLG2_hasDerivAt_Ta s (hb.trans ht))
      (fun s _ t ht => pcfLG2_hasDerivAt_Tad s (hb.trans ht))
      (fun s _ => (pcfLG2_continuousOn_Tad2 s).mono (Ioi_subset_Ioi hb.le))
      (fun t => by simp [pcfLG2_Ta, pcfTemmePoly])
      (fun t _ => by simp [pcfLG2_Tad, pcfTemmePoly])
      (fun s _ t ht => pcfLG2_temme_rec s (hb.trans ht)) hNi hI (K := K)
      (fun s _ t ht => hK s _ (hτb t ht))
      (fun s _ => ((pcfTemmePoly s).continuous.tendsto 0).comp pcfLG2_tendsto_tau)
      (U := fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2))
      (U' := fun μ t => (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2))
      (H := fun μ => pcfH μ) (fun μ t _ => pcfLG_hasDerivAt_U μ t)
      (fun μ t ht => (pcfLG_hasDerivAt_U' μ t).congr_deriv (by
        rw [pcfLG_A_pow_four_recip (hb.trans ht)]))
      (fun μ hμ => pcfLG_tendsto_U_div (by linarith)) le_rfl hμ₀ hμ₀C
    refine IsBigO.of_bound C (pcfLG_eventually_uniform μ₀ fun μ hμ t ht => ?_)
    have hμ0 : 0 < μ := by linarith
    have ht1 : 1 < t := by have : 1 + δ ≤ t := ht; linarith
    have htb : b < t := by have : 1 + δ ≤ t := ht; linarith
    obtain ⟨-, ε, ε', hε⟩ := hcore μ hμ
    obtain ⟨hεb, -, hU, -⟩ := hε t htb
    rw [pcfLG2_temme_L hN] at hU
    have hh0 : pcfH μ ≠ 0 := by rw [pcfLG_pcfH_eq hμ0]; exact_mod_cast (pcfLG_h_pos hμ0).ne'
    have hAe : ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pcfLG_A_pos ht1) (Real.exp_pos _)).ne'
    simp only
    rw [pcfLG_denom_eq ht1, pcfLG2_sum_temme_eq, pcfLG_norm_zpow hμ0, hU]
    have heq : pcfH μ / ((1:ℝ):ℂ) * ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) *
        (pcfLG2_ser pcfLG2_Ta N (μ^2) t + ε t) : ℝ) : ℂ) /
        (pcfH μ * ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ)) -
        (pcfLG2_ser pcfLG2_Ta N (μ^2) t : ℂ) = (ε t : ℂ) := by
      push_cast
      have hA0 : (pcfLG_A t : ℂ) ≠ 0 := by exact_mod_cast (pcfLG_A_pos ht1).ne'
      field_simp
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, ← div_eq_mul_inv]
    exact hεb
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 := key 1 le_rfl
    have hb : (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*(1:ℕ):ℤ))) =O[pcfUniformFilter (Ici (1+δ))]
        (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*(0:ℕ):ℤ))) := by
      refine IsBigO.of_bound 1 (pcfLG_eventually_uniform 1 fun μ hμ t _ => ?_)
      rw [pcfLG_norm_zpow (by linarith), pcfLG_norm_zpow (by linarith)]
      simp only [pow_zero, inv_one, one_mul, pow_one]
      exact inv_le_one_of_one_le₀ (by nlinarith)
    have hc : (fun _ : ℝ × ℝ => (1:ℂ)) =O[pcfUniformFilter (Ici (1+δ))]
        (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*(0:ℕ):ℤ))) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun p => by simp)
    refine ((h1.trans hb).add hc).congr_left fun p => ?_
    simp [pcfTemmePoly]
  · exact key N hN

end DLMF.Confluent
end
