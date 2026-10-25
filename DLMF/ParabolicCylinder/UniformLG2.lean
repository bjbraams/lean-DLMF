/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.UniformLG
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenFinite

/-!
# Uniform expansions of parabolic cylinder functions: second stage

A general form of the recessive Liouville–Green core of `DLMF.ParabolicCylinder.UniformLG`
(`pcfLG2_core`): for any amplitude `A` with `ξ' = A⁻²` on `(b, ∞)`, any coefficient family
satisfying the Liouville–Green recursion with uniform bounds and limits at `+∞`, and any solution
`U` of `U'' = μ⁴A⁻⁴U` normalised at `+∞`, the expansion of `U` and of `U'` holds with explicit
constants. It is applied here to Temme's form of the expansion of `U(-½μ², μt√2)` (DLMF 12.10.31),
whose coefficients `φ_s(τ(t))` satisfy the Liouville–Green recursion by the polynomial recursion
DLMF 12.10.33 (`pcfLG2_temme_rec`) and tend to `0` at `t = ∞` for `s ≥ 1`, so that the
normalizer is exactly `h(μ)`.

For positive parameter `a = ½μ²` the equation `w'' = μ⁴(t²+1)w` has no turning points, and the
core applies on every half-line `(b, ∞)` with constants uniform in `b`
(`pcfLG2_pos_core`), with the real coefficients `Ā_s = Re(i^s u_s(-it))/(t²+1)^{3s/2}`
(DLMF 12.10.27). Comparing the limits at `+∞` (DLMF 12.9.1) and at `-∞` (DLMF 12.2.15 with
DLMF 12.9.1–12.9.2) gives the formal identity `(∑ γ_j (u/2)^{-j})(∑ c_s u^{-s}) =
∑ (-1)^s c_s u^{-s}` (`pcfLG2_gamma_identity`), where `c_s` is the coefficient of `t^{3s}` in
`u_s`. Since the even `c_s`, `s ≥ 2`, vanish, this yields DLMF 12.10.14 for the normalizer of
DLMF 12.10.3.

## Main results

* `pcfLG2_core`: the general recessive Liouville–Green core.
* `pcfU_temme_uniform`: DLMF 12.10.31.
* `pcfLG2_gamma_identity`: the normalizer identity in formal form.
* `pcf_negative_parameter_uniform_U_normalizer`: DLMF 12.10.3 with a normalizer satisfying
  DLMF 12.10.14 (`IsCylinderGNormalizer`).
* `pcf_positive_parameter_uniform`: DLMF 12.10.25 and 12.10.29 with a normalizer satisfying
  DLMF 12.10.28.
* `pcf_negative_parameter_uniform_U_UDeriv`: DLMF 12.10.3 and 12.10.4 (the `U`- and `U'`-parts
  of `pcf_negative_parameter_uniform`) with one normalizer satisfying DLMF 12.10.14.
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

/-! ### Positive parameter: the whole-line expansion and the normalizer identity -/

/-- The barred polynomial `t ↦ Re(i^e P(-it))`, as a real polynomial. -/
noncomputable def pcfLG2_bar (e : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n * (I^e * (-I)^n).re) * X^n

/-- Evaluation of the barred polynomial. -/
lemma pcfLG2_bar_eval (e : ℕ) (P : Polynomial ℝ) (t : ℝ) :
    (pcfLG2_bar e P).eval t = (I^e * aeval (-I * t) P).re := by
  rw [pcfLG2_bar, eval_finsetSum, aeval_eq_sum_range, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [Complex.real_smul, show I^e * ((P.coeff n : ℂ) * (-I * t)^n) =
    ((P.coeff n * t^n : ℝ) : ℂ) * (I^e * (-I)^n) by push_cast; ring, Complex.re_ofReal_mul]
  ring

/-- `i^e (-i)^n` is real when `n + e` is even. -/
lemma pcfLG2_im_I_pow {e n : ℕ} (h : Even (n + e)) : (I^e * (-I)^n).im = 0 := by
  obtain ⟨k, hk⟩ := h
  have : I^e * (-I)^n = (((-1)^n * (-1)^k : ℝ) : ℂ) := by
    rw [neg_pow, show I^e * ((-1)^n * I^n) = (-1)^n * I^(n+e) by ring, hk, ← two_mul,
      pow_mul, I_sq]
    push_cast; ring
  rw [this, Complex.ofReal_im]

/-- For a polynomial of parity `e`, `i^e P(-it)` is real. -/
lemma pcfLG2_bar_real {e D : ℕ} {P : Polynomial ℝ} (hP : pcfLG_good e D P) (t : ℝ) :
    I^e * aeval (-I * t) P = (((pcfLG2_bar e P).eval t : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · rw [pcfLG2_bar_eval, Complex.ofReal_re]
  · rw [Complex.ofReal_im, aeval_eq_sum_range, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [Complex.real_smul, show I^e * ((P.coeff n : ℂ) * (-I * t)^n) =
      ((P.coeff n * t^n : ℝ) : ℂ) * (I^e * (-I)^n) by push_cast; ring, Complex.im_ofReal_mul]
    by_cases hc : P.coeff n = 0
    · simp [hc]
    · rw [pcfLG2_im_I_pow (hP n hc).1, mul_zero]

/-- The barred polynomial has degree at most that of `P`. -/
lemma pcfLG2_natDegree_bar (e : ℕ) (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) :
    (pcfLG2_bar e P).natDegree ≤ d := by
  refine (natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Finset.mem_range.1 hn; omega

/-- Coefficients of the barred polynomial. -/
lemma pcfLG2_bar_coeff (e : ℕ) (P : Polynomial ℝ) (n : ℕ) :
    (pcfLG2_bar e P).coeff n = P.coeff n * (I^e * (-I)^n).re := by
  rw [pcfLG2_bar, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hn
    have : P.natDegree < n := by simpa using hn
    simp [coeff_eq_zero_of_natDegree_lt this]

/-- The barred polynomial keeps the parity class. -/
lemma pcfLG2_bar_good {e D : ℕ} {P : Polynomial ℝ} (hP : pcfLG_good e D P) (e' : ℕ) :
    pcfLG_good e D (pcfLG2_bar e' P) := fun n hn => by
  rw [pcfLG2_bar_coeff] at hn
  exact hP n (left_ne_zero_of_mul hn)

/-- Parity: `P(-t) = (-1)^e P(t)` for `P` of parity `e`. -/
lemma pcfLG2_eval_neg {e D : ℕ} {P : Polynomial ℝ} (hP : pcfLG_good e D P) (t : ℝ) :
    P.eval (-t) = (-1)^e * P.eval t := by
  rw [eval_eq_sum_range, eval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hc : P.coeff n = 0
  · simp [hc]
  · have h2 : (-1:ℝ)^(n+e) = 1 := (hP n hc).1.neg_one_pow
    have : (-1:ℝ)^n = (-1)^e := by
      calc (-1:ℝ)^n = (-1)^n * ((-1)^e)^2 := by
            rw [← pow_mul, mul_comm e 2, pow_mul]; norm_num
        _ = (-1)^(n+e) * (-1)^e := by ring
        _ = (-1)^e := by rw [h2, one_mul]
    rw [neg_pow, this]; ring

/-- Derivative of `t ↦ i^e P(-it)` (complex-valued). -/
lemma pcfLG2_hasDerivAt_aeval (e : ℕ) (P : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => I^e * aeval (-I * t) P)
      (I^(e+3) * aeval (-I * t) (derivative P)) t := by
  have h1 : HasDerivAt (fun t : ℝ => -I * (t:ℂ)) (-I) t := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_mul (-I)).comp_ofReal
  have := ((P.hasDerivAt_aeval (-I * (t:ℂ))).comp t h1).const_mul (I^e)
  refine this.congr_deriv ?_
  rw [pow_add, show I^3 = -I by rw [pow_succ, I_sq]; ring]; ring

/-- Derivative of the barred polynomial. -/
lemma pcfLG2_hasDerivAt_bar (e : ℕ) (P : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun t => (pcfLG2_bar e P).eval t) ((pcfLG2_bar (e+3) (derivative P)).eval t) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (pcfLG2_hasDerivAt_aeval e P t)
  simp only [Function.comp_def, Complex.reCLM_apply] at h
  rw [pcfLG2_bar_eval]
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun x => pcfLG2_bar_eval e P x)

/-- `Q_s(t) = Re(i^s u_s(-it))` (DLMF 12.10.27). -/
noncomputable def pcfLG2_Q (s : ℕ) : Polynomial ℝ := pcfLG2_bar s (pcfOlverU s)
/-- `R_s(t) = Re(i^{s+1} r_{s-1}(-it))`. -/
noncomputable def pcfLG2_R (s : ℕ) : Polynomial ℝ := pcfLG2_bar (s+1) (pcfOlverPair s).2

/-- The barred form of DLMF 12.10.11: `(t²+1)Q_s' - 3stQ_s = R_s`. -/
lemma pcfLG2_QR_eq (s : ℕ) (t : ℝ) :
    (t^2+1) * (pcfLG2_bar (s+3) (derivative (pcfOlverU s))).eval t -
      3*s*t*(pcfLG2_Q s).eval t = (pcfLG2_R s).eval t := by
  have h := congrArg (aeval (-I * (t:ℂ))) (pcfLG_olverU_eq s)
  simp only [map_sub, map_mul, map_pow, aeval_X, map_one, aeval_C] at h
  simp only [pcfLG2_Q, pcfLG2_R, pcfLG2_bar_eval]
  set U' := aeval (-I * (t:ℂ)) (derivative (pcfOlverU s))
  set U := aeval (-I * (t:ℂ)) (pcfOlverU s)
  set ρ := aeval (-I * (t:ℂ)) (pcfOlverPair s).2
  have hI2 : I^2 = -1 := I_sq
  have hc : ((t^2+1 : ℝ) : ℂ) * (I^(s+3) * U') - ((3*s*t : ℝ) : ℂ) * (I^s * U) =
      I^(s+1) * ρ := by
    rw [← h]
    push_cast
    rw [pow_add, pow_add]
    linear_combination (-(3*(t:ℂ)*(s:ℂ)*I^s*U) + I*I^s*U') * hI2
  have := congrArg Complex.re hc
  simp only [Complex.sub_re, Complex.re_ofReal_mul] at this
  linarith

/-- The barred form of DLMF 12.10.12. -/
lemma pcfLG2_R_succ (s : ℕ) (t : ℝ) :
    (pcfLG2_R (s+1)).eval t = 1/8*(3*t^2-2)*(pcfLG2_Q s).eval t -
      3/2*(s+1)*t*(pcfLG2_R s).eval t +
      1/2*(t^2+1)*(pcfLG2_bar (s+1+3) (derivative (pcfOlverPair s).2)).eval t := by
  have h := congrArg (aeval (-I * (t:ℂ))) (pcfLG_olverPair_snd_succ s)
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_one, aeval_C] at h
  simp only [pcfLG2_Q, pcfLG2_R, pcfLG2_bar_eval]
  have hU : pcfOlverU s = (pcfOlverPair s).1 := rfl
  rw [hU]
  set U := aeval (-I * (t:ℂ)) (pcfOlverPair s).1
  set ρ := aeval (-I * (t:ℂ)) (pcfOlverPair s).2
  set ρ' := aeval (-I * (t:ℂ)) (derivative (pcfOlverPair s).2)
  set ρ1 := aeval (-I * (t:ℂ)) (pcfOlverPair (s+1)).2
  have hI2 : I^2 = -1 := I_sq
  have hc : I^(s+1+1) * ρ1 = ((1/8*(3*t^2-2) : ℝ) : ℂ) * (I^s * U) -
      ((3/2*(s+1)*t : ℝ) : ℂ) * (I^(s+1) * ρ) + ((1/2*(t^2+1) : ℝ) : ℂ) * (I^(s+1+3) * ρ') := by
    rw [h]
    push_cast
    simp only [pow_add, pow_one]
    linear_combination (3/2*(t:ℂ)*(s:ℂ)*I^s*ρ*I + 3/2*(t:ℂ)*I^s*ρ*I + 1/4*I^s*U -
      1/2*I^s*ρ'*I^2 + 3/8*(t:ℂ)^2*I^s*U*(I^2-1)) * hI2
  have := congrArg Complex.re hc
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul] at this
  linarith

/-- Derivative of `q(t) (t²+1)^c`. -/
lemma pcfLG2_hasDerivAt_mul_rpow {q : ℝ → ℝ} {d t : ℝ} (hq : HasDerivAt q d t) (c : ℝ) :
    HasDerivAt (fun t => q t * (t^2+1) ^ c) ((d * (t^2+1) + 2*c*t*q t) * (t^2+1) ^ (c-1)) t := by
  have hy : 0 < t^2+1 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => t^2+1) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const 1
  have h2 := h1.rpow_const (p := c) (Or.inl hy.ne')
  have := hq.mul h2
  convert this using 1
  have e : (t^2+1) ^ c = (t^2+1) * (t^2+1) ^ (c-1) := by
    conv_lhs => rw [show c = 1 + (c-1) by ring]
    rw [Real.rpow_add hy, Real.rpow_one]
  rw [e]; ring

/-- The amplitude `A = (t²+1)^{-1/4}` for positive parameter. -/
noncomputable def pcfLG2_PA (t : ℝ) : ℝ := (t^2+1) ^ (-1/4:ℝ)
/-- `A'`. -/
noncomputable def pcfLG2_PA1 (t : ℝ) : ℝ := -(t/2) * (t^2+1) ^ (-5/4:ℝ)
/-- `A''`. -/
noncomputable def pcfLG2_PA2 (t : ℝ) : ℝ := (3*t^2-2)/4 * (t^2+1) ^ (-9/4:ℝ)

/-- `A' = -(t/2)(t²+1)^{-5/4}`. -/
lemma pcfLG2_hasDerivAt_PA (t : ℝ) : HasDerivAt pcfLG2_PA (pcfLG2_PA1 t) t := by
  have := pcfLG2_hasDerivAt_mul_rpow (hasDerivAt_const t (1:ℝ)) (-1/4) (t := t)
  simp only [one_mul] at this
  unfold pcfLG2_PA pcfLG2_PA1
  convert this using 1
  rw [show (-1/4:ℝ) - 1 = -5/4 by norm_num]; ring

/-- `A'' = (3t²-2)/4 · (t²+1)^{-9/4}`. -/
lemma pcfLG2_hasDerivAt_PA1 (t : ℝ) : HasDerivAt pcfLG2_PA1 (pcfLG2_PA2 t) t := by
  have := pcfLG2_hasDerivAt_mul_rpow ((hasDerivAt_id' t).const_mul (-1/2:ℝ)) (-5/4) (t := t)
  unfold pcfLG2_PA1 pcfLG2_PA2
  convert this using 1
  · funext t; ring
  · rw [show (-5/4:ℝ) - 1 = -9/4 by norm_num]; ring

/-- `A > 0`. -/
lemma pcfLG2_PA_pos (t : ℝ) : 0 < pcfLG2_PA t := Real.rpow_pos_of_pos (by positivity) _

/-- `A⁻² = √(t²+1)`. -/
lemma pcfLG2_PA_sq_recip (t : ℝ) : (pcfLG2_PA t ^ 2)⁻¹ = Real.sqrt (t^2+1) := by
  have hy : 0 < t^2+1 := by positivity
  rw [pcfLG2_PA, ← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_neg hy.le,
    Real.sqrt_eq_rpow]
  norm_num

/-- `A⁻⁴ = t²+1`. -/
lemma pcfLG2_PA_pow_four_recip (t : ℝ) : (pcfLG2_PA t ^ 4)⁻¹ = t^2+1 := by
  have hy : 0 < t^2+1 := by positivity
  rw [pcfLG2_PA, ← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_neg hy.le]
  norm_num

/-- `ξ̄' = √(t²+1)` (DLMF 12.10.26). -/
lemma pcfLG2_hasDerivAt_xiBar (t : ℝ) : HasDerivAt pcfXiBar (Real.sqrt (t^2+1)) t := by
  have hy : 0 < t^2+1 := by positivity
  set r := Real.sqrt (t^2+1) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hy
  have hr2 : r^2 = t^2+1 := Real.sq_sqrt hy.le
  have h1 : HasDerivAt (fun t : ℝ => t^2+1) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const 1
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (t^2+1)) (2*t / (2 * r)) t := h1.sqrt hy.ne'
  have htr : 0 < t + r := by
    have : |t| < r := by
      rw [hr, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
    linarith [neg_abs_le t]
  have hl : HasDerivAt (fun t : ℝ => Real.log (t + Real.sqrt (t^2+1))) ((1 + 2*t/(2*r)) / (t + r)) t :=
    ((hasDerivAt_id t).add hs).log htr.ne'
  have := (((hasDerivAt_id t).mul hs).add hl).div_const 2
  have e : pcfXiBar = fun x => ((((id : ℝ → ℝ) * fun t : ℝ => Real.sqrt (t^2+1)) +
      fun t : ℝ => Real.log (t + Real.sqrt (t^2+1))) : ℝ → ℝ) x / 2 := by
    funext x; simp [pcfXiBar]
  rw [e]
  convert this using 1
  simp only [id]
  field_simp
  rw [← hr]
  nlinarith [hr2]

/-- Coefficient `Ā_s(t) = Q_s(t)/(t²+1)^{3s/2}`. -/
noncomputable def pcfLG2_Pa (s : ℕ) (t : ℝ) : ℝ := (pcfLG2_Q s).eval t * (t^2+1) ^ (-(3*s/2:ℝ))
/-- `Ā_s' = R_s(t)/(t²+1)^{(3s+2)/2}`. -/
noncomputable def pcfLG2_Pad (s : ℕ) (t : ℝ) : ℝ :=
  (pcfLG2_R s).eval t * (t^2+1) ^ (-((3*s+2)/2:ℝ))
/-- `Ā_s''`. -/
noncomputable def pcfLG2_Pad2 (s : ℕ) (t : ℝ) : ℝ :=
  ((pcfLG2_bar (s+1+3) (derivative (pcfOlverPair s).2)).eval t * (t^2+1) -
    (3*s+2)*t*(pcfLG2_R s).eval t) * (t^2+1) ^ (-((3*s+4)/2):ℝ)

/-- `Ā_s'`. -/
lemma pcfLG2_hasDerivAt_Pa (s : ℕ) (t : ℝ) : HasDerivAt (pcfLG2_Pa s) (pcfLG2_Pad s t) t := by
  have := pcfLG2_hasDerivAt_mul_rpow (pcfLG2_hasDerivAt_bar s (pcfOlverU s) t) (-(3*s/2))
  unfold pcfLG2_Pa pcfLG2_Pad
  refine this.congr_deriv ?_
  rw [← pcfLG2_QR_eq s t, show -(3*(s:ℝ)/2) - 1 = -((3*s+2)/2) by ring, pcfLG2_Q]; ring

/-- `Ā_s''`. -/
lemma pcfLG2_hasDerivAt_Pad (s : ℕ) (t : ℝ) : HasDerivAt (pcfLG2_Pad s) (pcfLG2_Pad2 s t) t := by
  have := pcfLG2_hasDerivAt_mul_rpow (pcfLG2_hasDerivAt_bar (s+1) (pcfOlverPair s).2 t)
    (-((3*s+2)/2))
  unfold pcfLG2_Pad pcfLG2_Pad2
  refine this.congr_deriv ?_
  rw [show -((3*(s:ℝ)+2)/2) - 1 = -((3*s+4)/2) by ring, pcfLG2_R]; ring

/-- Continuity of `Ā_s''`. -/
lemma pcfLG2_continuous_Pad2 (s : ℕ) : Continuous (pcfLG2_Pad2 s) := by
  unfold pcfLG2_Pad2
  refine Continuous.mul (by fun_prop) ?_
  exact Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity)

/-- **The Liouville–Green recursion for the barred coefficients** with `A = (t²+1)^{-1/4}`. -/
lemma pcfLG2_P_recursion (s : ℕ) (t : ℝ) :
    pcfLG2_PA t ^ 2 * pcfLG2_Pad2 s t + 2 * pcfLG2_PA t * pcfLG2_PA1 t * pcfLG2_Pad s t +
      pcfLG2_PA t * pcfLG2_PA2 t * pcfLG2_Pa s t = 2 * pcfLG2_Pad (s+1) t := by
  have hy : 0 < t^2+1 := by positivity
  set y := t^2+1
  set Z := y ^ (-((3*(s:ℝ)+5)/2))
  have e1 : pcfLG2_PA t ^ 2 * y ^ (-((3*(s:ℝ)+4)/2)) = Z := by
    rw [pcfLG2_PA, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    exact pcfLG_rpow_mul hy (by push_cast; ring)
  have e2 : pcfLG2_PA t * y ^ (-5/4:ℝ) * y ^ (-((3*(s:ℝ)+2)/2)) = Z := by
    rw [pcfLG2_PA, pcfLG_rpow_mul hy (c := -3/2) (by norm_num)]
    exact pcfLG_rpow_mul hy (by ring)
  have e3 : pcfLG2_PA t * y ^ (-9/4:ℝ) * y ^ (-(3*(s:ℝ)/2)) = Z := by
    rw [pcfLG2_PA, pcfLG_rpow_mul hy (c := -5/2) (by norm_num)]
    exact pcfLG_rpow_mul hy (by ring)
  have e4 : y ^ (-((3*((s+1:ℕ):ℝ)+2)/2)) = Z := by simp only [Z]; congr 1; push_cast; ring
  have hp := pcfLG2_R_succ s t
  simp only [pcfLG2_Pad2, pcfLG2_Pad, pcfLG2_Pa, pcfLG2_PA1, pcfLG2_PA2]
  rw [e4, hp]
  linear_combination
    ((pcfLG2_bar (s+1+3) (derivative (pcfOlverPair s).2)).eval t * y -
      (3*s+2)*t*(pcfLG2_R s).eval t) * e1 +
    (-t * (pcfLG2_R s).eval t) * e2 + ((3*t^2-2)/4 * (pcfLG2_Q s).eval t) * e3

/-- `|P(t)| ≤ (∑|coeff|)·(t²+1)^{d/2}` for `deg P ≤ d`. -/
lemma pcfLG2_abs_eval_le (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) (t : ℝ) :
    |P.eval t| ≤ (∑ i ∈ Finset.range (d+1), |P.coeff i|) * (t^2+1) ^ ((d:ℝ)/2) := by
  have hy : 1 ≤ t^2+1 := by nlinarith [sq_nonneg t]
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hi : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : |t| ≤ (t^2+1) ^ (1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  calc |t|^i ≤ ((t^2+1) ^ (1/2:ℝ))^i := pow_le_pow_left₀ (abs_nonneg _) h1 i
    _ = (t^2+1) ^ ((i:ℝ)/2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf
    _ ≤ (t^2+1) ^ ((d:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hy (by
        have : (i:ℝ) ≤ d := by exact_mod_cast hi
        linarith)

/-- `(t²+1)^{-3/2} ≤ (1+t²)⁻¹`. -/
lemma pcfLG2_rpow_le_recip (t : ℝ) : (t^2+1) ^ (-(3/2):ℝ) ≤ (1+t^2)⁻¹ := by
  have hy : 1 ≤ t^2+1 := by nlinarith [sq_nonneg t]
  calc (t^2+1) ^ (-(3/2):ℝ) ≤ (t^2+1) ^ (-1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    _ = (1+t^2)⁻¹ := by rw [Real.rpow_neg_one, add_comm]

/-- Domination by `K (1+t²)⁻¹` gives integrability. -/
lemma pcfLG2_integrable_of_le {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hK : ∀ t, |f t| ≤ K * (1 + t^2)⁻¹) : Integrable (fun t => |f t|) :=
  (integrable_inv_one_add_sq.const_mul K).mono' hf.abs.aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_abs]; exact hK t)

/-- Domination by `K (1+t²)⁻¹` gives the tail bound `K π`. -/
lemma pcfLG2_tail_le {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hK : ∀ t, |f t| ≤ K * (1 + t^2)⁻¹) (t : ℝ) : ∫ x in Ioi t, |f x| ≤ K * π := by
  refine (setIntegral_le_integral (pcfLG2_integrable_of_le hf hK)
    (Eventually.of_forall fun _ => abs_nonneg _)).trans ?_
  calc ∫ x, |f x| ≤ ∫ x, K * (1 + x^2)⁻¹ :=
        integral_mono (pcfLG2_integrable_of_le hf hK) (integrable_inv_one_add_sq.const_mul K) hK
    _ = K * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- Parity and degree of `Q_s`. -/
lemma pcfLG2_Q_good (s : ℕ) : pcfLG_good s (3*s) (pcfLG2_Q s) :=
  pcfLG2_bar_good (pcfLG_olverPair_inv s).1 s

/-- `|Ā_s(t)| ≤ K_s` on `ℝ`. -/
lemma pcfLG2_abs_Pa_le (s : ℕ) (t : ℝ) :
    |pcfLG2_Pa s t| ≤ ∑ i ∈ Finset.range (3*s+1), |(pcfLG2_Q s).coeff i| := by
  have hy : 0 < t^2+1 := by positivity
  have h := pcfLG2_abs_eval_le (pcfLG2_Q s) (pcfLG_good_natDegree (pcfLG2_Q_good s)) t
  rw [pcfLG2_Pa, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]
  have e : (t^2+1) ^ (((3*s:ℕ):ℝ)/2) * (t^2+1) ^ (-(3*s/2:ℝ)) = 1 := by
    rw [← Real.rpow_add hy]; push_cast; ring_nf; exact Real.rpow_zero _
  calc |(pcfLG2_Q s).eval t| * (t^2+1) ^ (-(3*s/2:ℝ))
      ≤ (∑ i ∈ Finset.range (3*s+1), |(pcfLG2_Q s).coeff i|) * (t^2+1) ^ (((3*s:ℕ):ℝ)/2) *
          (t^2+1) ^ (-(3*s/2:ℝ)) := by gcongr
    _ = _ := by rw [mul_assoc, e, mul_one]

/-- `|Ā_N'(t)| ≤ K (1+t²)⁻¹` on `ℝ`. -/
lemma pcfLG2_abs_Pad_le (N : ℕ) : ∃ K, ∀ t, |pcfLG2_Pad N t| ≤ K * (1 + t^2)⁻¹ := by
  rcases N with _ | m
  · refine ⟨0, fun t => ?_⟩
    simp [pcfLG2_Pad, pcfLG2_R, pcfLG2_bar, pcfOlverPair]
  · have hd : (pcfLG2_R (m+1)).natDegree ≤ 3*m+2 :=
      pcfLG2_natDegree_bar _ _ (pcfLG_natDegree_olverPair_snd m)
    refine ⟨∑ i ∈ Finset.range (3*m+2+1), |(pcfLG2_R (m+1)).coeff i|, fun t => ?_⟩
    have hy : 0 < t^2+1 := by positivity
    have h := pcfLG2_abs_eval_le (pcfLG2_R (m+1)) hd t
    rw [pcfLG2_Pad, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]
    have e : (t^2+1) ^ (((3*m+2:ℕ):ℝ)/2) * (t^2+1) ^ (-((3*((m+1:ℕ):ℝ)+2)/2)) =
        (t^2+1) ^ (-(3/2):ℝ) := by
      rw [← Real.rpow_add hy]; push_cast; ring_nf
    have hS : 0 ≤ ∑ i ∈ Finset.range (3*m+2+1), |(pcfLG2_R (m+1)).coeff i| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc |(pcfLG2_R (m+1)).eval t| * (t^2+1) ^ (-((3*((m+1:ℕ):ℝ)+2)/2))
        ≤ (∑ i ∈ Finset.range (3*m+2+1), |(pcfLG2_R (m+1)).coeff i|) *
            (t^2+1) ^ (((3*m+2:ℕ):ℝ)/2) * (t^2+1) ^ (-((3*((m+1:ℕ):ℝ)+2)/2)) := by gcongr
      _ = (∑ i ∈ Finset.range (3*m+2+1), |(pcfLG2_R (m+1)).coeff i|) * (t^2+1) ^ (-(3/2):ℝ) := by
          rw [mul_assoc, e]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pcfLG2_rpow_le_recip t) hS

/-- `A A'' = (3t²-2)/4 · (t²+1)^{-5/2}`. -/
lemma pcfLG2_PA_mul_PA2 (t : ℝ) :
    pcfLG2_PA t * pcfLG2_PA2 t = (3*t^2-2)/4 * (t^2+1) ^ (-(5/2):ℝ) := by
  have hy : 0 < t^2+1 := by positivity
  unfold pcfLG2_PA pcfLG2_PA2
  rw [mul_left_comm, pcfLG_rpow_mul hy (c := -(5/2)) (by norm_num)]

/-- The error-control integrand is dominated by `(3/4)(1+t²)⁻¹`. -/
lemma pcfLG2_abs_V_le (t : ℝ) :
    |pcfLG2_PA t * pcfLG2_PA2 t - (fun _ => (0:ℝ)) t * pcfLG2_PA t ^ 2| ≤ 3/4 * (1 + t^2)⁻¹ := by
  have hy : 0 < t^2+1 := by positivity
  simp only [zero_mul, sub_zero]
  rw [pcfLG2_PA_mul_PA2, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]
  have h1 : |(3*t^2-2)/4| ≤ 3/4 * (t^2+1) := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg t]
  have e : (t^2+1) * (t^2+1) ^ (-(5/2):ℝ) = (t^2+1) ^ (-(3/2):ℝ) := by
    conv_lhs => arg 1; rw [← Real.rpow_one (t^2+1)]
    rw [← Real.rpow_add hy]; norm_num
  calc |(3*t^2-2)/4| * (t^2+1) ^ (-(5/2):ℝ) ≤ 3/4 * (t^2+1) * (t^2+1) ^ (-(5/2):ℝ) := by
        gcongr
    _ = 3/4 * (t^2+1) ^ (-(3/2):ℝ) := by rw [mul_assoc, e]
    _ ≤ _ := by gcongr; exact pcfLG2_rpow_le_recip t

/-- Continuity of the error-control integrand. -/
lemma pcfLG2_continuous_V :
    Continuous (fun t => pcfLG2_PA t * pcfLG2_PA2 t - (fun _ => (0:ℝ)) t * pcfLG2_PA t ^ 2) := by
  have h1 : Continuous pcfLG2_PA := continuous_iff_continuousAt.2 fun t =>
    (pcfLG2_hasDerivAt_PA t).continuousAt
  have h2 : Continuous pcfLG2_PA2 := by
    unfold pcfLG2_PA2
    exact Continuous.mul (by fun_prop)
      (Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity))
  exact (h1.mul h2).sub (continuous_const.mul (h1.pow 2))

/-- `A(t) → 0` as `t → ∞`. -/
lemma pcfLG2_tendsto_PA : Tendsto pcfLG2_PA atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t^2+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
  have := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).comp h
  refine this.congr fun t => ?_
  simp only [Function.comp, pcfLG2_PA]; norm_num

/-- `t²/(t²+1) → 1`. -/
lemma pcfLG2_tendsto_sq_div : Tendsto (fun t : ℝ => t^2/(t^2+1)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => 1/(1 + (t^2)⁻¹)) atTop (𝓝 (1/(1+0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add
      ((tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop)) (by norm_num)
  rw [show (1:ℝ)/(1+0) = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have : t^2 ≠ 0 := by positivity
  field_simp

/-- `Ā_s(t) → c̄_s` as `t → ∞`. -/
lemma pcfLG2_tendsto_Pa (s : ℕ) :
    Tendsto (pcfLG2_Pa s) atTop (𝓝 ((pcfLG2_Q s).coeff (3*s))) := by
  have h1 := pcfLG_tendsto_eval_div_pow (pcfLG2_Q s) (pcfLG_good_natDegree (pcfLG2_Q_good s))
  have h2 : Tendsto (fun t : ℝ => (t^2/(t^2+1)) ^ (3*s/2:ℝ)) atTop (𝓝 1) := by
    have := pcfLG2_tendsto_sq_div.rpow_const (p := 3*s/2) (Or.inl one_ne_zero)
    simpa using this
  have := h1.mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht0
  have hy : 0 < t^2+1 := by positivity
  rw [pcfLG2_Pa, Real.div_rpow (by positivity) hy.le, Real.rpow_neg hy.le,
    show (t^2) ^ (3*(s:ℝ)/2) = t ^ (3*s) by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast]; push_cast; ring_nf]
  have : t ^ (3*s) ≠ 0 := by positivity
  field_simp

/-- Parity of `Ā_s`. -/
lemma pcfLG2_Pa_neg (s : ℕ) (t : ℝ) : pcfLG2_Pa s (-t) = (-1)^s * pcfLG2_Pa s t := by
  rw [pcfLG2_Pa, pcfLG2_Pa, pcfLG2_eval_neg (pcfLG2_Q_good s), neg_sq]; ring

/-- `Ā_s(t) → (-1)^s c̄_s` as `t → -∞`. -/
lemma pcfLG2_tendsto_Pa_atBot (s : ℕ) :
    Tendsto (pcfLG2_Pa s) atBot (𝓝 ((-1)^s * (pcfLG2_Q s).coeff (3*s))) := by
  have := ((pcfLG2_tendsto_Pa s).const_mul ((-1:ℝ)^s)).comp tendsto_neg_atBot_atTop
  refine this.congr fun t => ?_
  simp only [Function.comp, pcfLG2_Pa_neg]
  rw [← mul_assoc, ← mul_pow]; norm_num

/-- `c̄_s = (-1)^s c_s`. -/
lemma pcfLG2_Q_coeff (s : ℕ) : (pcfLG2_Q s).coeff (3*s) = (-1)^s * pcfLG_c s := by
  rw [pcfLG2_Q, pcfLG2_bar_coeff, pcfLG_c, pcfOlverU]
  have : I^s * (-I)^(3*s) = (((-1)^s : ℝ) : ℂ) := by
    have h3 : (-I)^3 = I := by rw [show (-I)^3 = -(I^2*I) by ring, I_sq]; ring
    rw [pow_mul, h3, ← mul_pow, I_mul_I]
    push_cast; ring
  rw [this, Complex.ofReal_re]; ring

/-- `U(μ²/2, μt√2)` as a function of `t`: first derivative. -/
lemma pcfLG2_hasDerivAt_PU (μ t : ℝ) :
    HasDerivAt (fun t : ℝ => pcfU (μ^2/2) (μ*t*Real.sqrt 2))
      ((μ:ℂ) * Real.sqrt 2 * pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2)) t := by
  have h1 : HasDerivAt (fun w : ℂ => (μ:ℂ) * w * Real.sqrt 2) ((μ:ℂ) * Real.sqrt 2) (t:ℂ) := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_mul (μ:ℂ)).mul_const ((Real.sqrt 2 : ℝ) : ℂ)
  have := ((hasDerivAt_pcfU ((μ:ℂ)^2/2) ((μ:ℂ) * t * Real.sqrt 2)).comp (t:ℂ) h1).comp_ofReal
  exact this.congr_deriv (by ring)

/-- `U(μ²/2, μt√2)` as a function of `t`: Weber's equation `w'' = μ⁴(t²+1) w`. -/
lemma pcfLG2_hasDerivAt_PU' (μ t : ℝ) :
    HasDerivAt (fun t : ℝ => (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2))
      (((μ^4*(t^2+1) : ℝ) : ℂ) * pcfU (μ^2/2) (μ*t*Real.sqrt 2)) t := by
  have h1 : HasDerivAt (fun w : ℂ => (μ:ℂ) * w * Real.sqrt 2) ((μ:ℂ) * Real.sqrt 2) (t:ℂ) := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_mul (μ:ℂ)).mul_const ((Real.sqrt 2 : ℝ) : ℂ)
  have := (((hasDerivAt_pcfUDeriv ((μ:ℂ)^2/2) ((μ:ℂ) * t * Real.sqrt 2)).comp (t:ℂ)
    h1).comp_ofReal).const_mul ((μ:ℂ) * Real.sqrt 2)
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  refine this.congr_deriv ?_
  push_cast
  linear_combination (((μ:ℂ)^4*(t:ℂ)^2/4) * (((Real.sqrt 2 : ℝ) : ℂ)^2 + 2) + (μ:ℂ)^4/2) *
    pcfU ((μ:ℂ)^2/2) ((μ:ℂ) * t * Real.sqrt 2) * hs2

/-- `√(t²+1)/t → 1`. -/
lemma pcfLG2_tendsto_sqrt_div : Tendsto (fun t : ℝ => Real.sqrt (t^2+1) / t) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => Real.sqrt (1 + (t^2)⁻¹)) atTop (𝓝 (Real.sqrt (1 + 0))) :=
    (tendsto_const_nhds.add ((tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop)).sqrt
  rw [add_zero, Real.sqrt_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht0
  rw [show 1 + (t^2)⁻¹ = (t^2+1)/t^2 by field_simp, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq ht0.le]

/-- `(t²+1)/t² → 1`. -/
lemma pcfLG2_tendsto_sq_div' : Tendsto (fun t : ℝ => (t^2+1)/t^2) atTop (𝓝 1) := by
  have := pcfLG2_tendsto_sq_div.inv₀ one_ne_zero
  rw [inv_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp

/-- **The normalization at `+∞` for positive parameter**: with `z = μ t √2`, `a = μ²/2`,
`e^{z²/4} z^{a+1/2} A(t) e^{-μ²ξ̄(t)} → μ√2 h(μ)` as `t → ∞`. -/
lemma pcfLG2_tendsto_PR {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => Real.exp ((μ*t*Real.sqrt 2)^2/4) * (μ*t*Real.sqrt 2) ^ (1/2+μ^2/2) *
      pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t))) atTop
      (𝓝 (μ * Real.sqrt 2 * pcfLG_h μ)) := by
  set p : ℝ := 1/2+μ^2/2
  set C₀ : ℝ := p * Real.log μ + p/2 * Real.log 2
  set r : ℝ → ℝ := fun t => Real.sqrt (t^2+1)
  set E : ℝ → ℝ := fun t => C₀ - 1/4 * Real.log ((t^2+1)/t^2) - μ^2/2 * (1 / (1 + r t / t)) -
    μ^2/2 * Real.log (1 + r t / t)
  have hlim : Tendsto E atTop (𝓝 (C₀ - 1/4 * Real.log 1 - μ^2/2 * (1/(1+1)) -
      μ^2/2 * Real.log (1+1))) := by
    have hq := pcfLG2_tendsto_sqrt_div
    exact ((tendsto_const_nhds.sub (tendsto_const_nhds.mul
      (pcfLG2_tendsto_sq_div'.log one_ne_zero))).sub (tendsto_const_nhds.mul
      (tendsto_const_nhds.div (tendsto_const_nhds.add hq) (by norm_num)))).sub
      (tendsto_const_nhds.mul ((tendsto_const_nhds.add hq).log (by norm_num)))
  have hval : C₀ - 1/4 * Real.log 1 - μ^2/2 * (1/(1+1)) - μ^2/2 * Real.log (1+1) =
      Real.log (μ * Real.sqrt 2 * pcfLG_h μ) := by
    rw [pcfLG_h, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow hμ, Real.log_exp, Real.log_sqrt (by norm_num)]
    simp only [C₀, p]; norm_num; ring
  rw [hval] at hlim
  have := (Real.continuous_exp.tendsto _).comp hlim
  rw [Real.exp_log (by have := pcfLG_h_pos hμ; positivity)] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht0
  have hy : 0 < t^2+1 := by positivity
  have hr0 : 0 < r t := Real.sqrt_pos.2 hy
  have hr2 : r t ^ 2 = t^2+1 := Real.sq_sqrt hy.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : 0 < μ*t*Real.sqrt 2 := by positivity
  simp only [Function.comp, pcfLG2_PA]
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hy, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  simp only [E, C₀, pcfXiBar]
  have e1 : 1 / (1 + r t / t) = t * r t - t^2 := by
    have : r t + t ≠ 0 := by positivity
    field_simp
    nlinarith [hr2]
  have e2 : Real.log (1 + r t / t) = Real.log (t + r t) - Real.log t := by
    rw [show 1 + r t / t = (t + r t)/t by field_simp, Real.log_div (by positivity) ht0.ne']
  have e3 : Real.log ((t^2+1)/t^2) = Real.log (t^2+1) - 2 * Real.log t := by
    rw [Real.log_div hy.ne' (by positivity), Real.log_pow]; push_cast; ring
  have e4 : Real.log (μ*t*Real.sqrt 2) = Real.log μ + Real.log t + 1/2 * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hμ.ne' ht0.ne',
      Real.log_sqrt (by norm_num)]; ring
  rw [e1, e2, e3, e4]
  have : (μ*t*Real.sqrt 2)^2 = 2*μ^2*t^2 := by rw [mul_pow, mul_pow, hs2]; ring
  rw [this]
  simp only [r]
  ring

/-- **The normalization of `U` at `+∞` for positive parameter** (from DLMF 12.9.1):
`U(μ²/2, μ t √2) / (A(t) e^{-μ² ξ̄(t)}) → 1/(μ√2 h(μ))` as `t → ∞`. -/
lemma pcfLG2_tendsto_PU_div {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => pcfU (μ^2/2) (μ*t*Real.sqrt 2) /
      ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ)) atTop
      (𝓝 (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ)) := by
  set a : ℂ := (μ:ℂ)^2/2
  have hO := pcfU_sector_asymptotic a (δ := π/4) (by positivity) (by linarith [Real.pi_pos]) 1
  have hz2 : Tendsto (fun z : ℂ => z ^ (-(2*(1:ℕ):ℤ))) (sector (3*π/4-π/4)) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z‖) (sector (3*π/4-π/4)) atTop :=
      tendsto_comap.mono_left inf_le_left
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    have h2 := (tendsto_pow_atTop (two_ne_zero)).comp this |>.inv_tendsto_atTop
    refine h2.congr fun z => ?_
    simp
  have hE := (hO.trans_tendsto hz2).add_const 1
  simp only [zero_add, Finset.sum_range_one] at hE
  have hE' : Tendsto (fun z : ℂ => cexp (z^2/4) * z^(a+1/2) * pcfU a z) (sector (3*π/4-π/4))
      (𝓝 1) := by
    refine hE.congr fun z => ?_
    simp [pcfUTerm, poch_zero]
  have hT := hE'.comp (pcfLG_tendsto_sector (α := 3*π/4-π/4) (by linarith [Real.pi_pos]) hμ)
  have hR := (Complex.continuous_ofReal.tendsto _).comp (pcfLG2_tendsto_PR hμ)
  have hRne : (μ * Real.sqrt 2 * pcfLG_h μ : ℝ) ≠ 0 := by
    have := pcfLG_h_pos hμ; positivity
  have := hT.div hR (by exact_mod_cast hRne)
  rw [show (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) =
    1 / ((μ * Real.sqrt 2 * pcfLG_h μ : ℝ) : ℂ) by push_cast; field_simp]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hx : 0 < μ*t*Real.sqrt 2 := by positivity
  have hcp : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(a+1/2) = (((μ*t*Real.sqrt 2)^(1/2+μ^2/2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx.le]; congr 1; simp only [a]; push_cast; ring
  have hp : 0 < (μ*t*Real.sqrt 2)^(1/2+μ^2/2) := Real.rpow_pos_of_pos hx _
  have hA : 0 < pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) :=
    mul_pos (pcfLG2_PA_pos t) (Real.exp_pos _)
  have hden : ((Real.exp ((μ*t*Real.sqrt 2)^2/4) * (μ*t*Real.sqrt 2)^(1/2+μ^2/2) * pcfLG2_PA t *
      Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) = cexp (((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) *
      ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(a+1/2) *
      ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) := by
    rw [hcp]; push_cast; ring
  have hp' : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(a+1/2) ≠ 0 := by rw [hcp]; exact_mod_cast hp.ne'
  have hA' : ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hA.ne'
  have he : cexp (((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) ≠ 0 := Complex.exp_ne_zero _
  simp only [Function.comp, Pi.div_apply]
  rw [hden, mul_div_mul_left _ _ (mul_ne_zero he hp')]
  push_cast; ring

/-- `ξ̄` is odd. -/
lemma pcfLG2_xiBar_neg (s : ℝ) : pcfXiBar (-s) = -pcfXiBar s := by
  have hy : 0 < s^2+1 := by positivity
  set r := Real.sqrt (s^2+1) with hr
  have hr2 : r^2 = s^2+1 := Real.sq_sqrt hy.le
  have h1 : |s| < r := by
    rw [hr, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hp : 0 < s + r := by linarith [neg_abs_le s]
  have hm : 0 < -s + r := by linarith [le_abs_self s]
  have e : -s + r = (s + r)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by nlinarith [hr2])
  unfold pcfXiBar
  rw [neg_sq, ← hr, e, Real.log_inv]; ring

/-- `A` is even. -/
lemma pcfLG2_PA_neg (s : ℝ) : pcfLG2_PA (-s) = pcfLG2_PA s := by simp [pcfLG2_PA]

/-- `ξ̄(t) → ∞`. -/
lemma pcfLG2_tendsto_xiBar : Tendsto pcfXiBar atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ ((tendsto_pow_atTop two_ne_zero).atTop_div_const
    (by norm_num : (0:ℝ) < 2))
  filter_upwards [eventually_ge_atTop 0] with s hs
  have hy : 0 < s^2+1 := by positivity
  have h1 : s ≤ Real.sqrt (s^2+1) := by
    have := Real.sqrt_le_sqrt (show s^2 ≤ s^2+1 by linarith); rwa [Real.sqrt_sq hs] at this
  have h2 : 0 ≤ Real.log (s + Real.sqrt (s^2+1)) := by
    apply Real.log_nonneg
    have : 1 ≤ Real.sqrt (s^2+1) := by
      have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ s^2+1 by nlinarith); rwa [Real.sqrt_one] at this
    linarith
  unfold pcfXiBar
  nlinarith

/-- With `z = μ s √2`, `a = μ²/2`: `e^{-z²/4} z^{1/2-a} A(s) e^{μ²ξ̄(s)} → 1/h(μ)` as `s → ∞`. -/
lemma pcfLG2_tendsto_PRV {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => Real.exp (-((μ*t*Real.sqrt 2)^2/4)) * (μ*t*Real.sqrt 2) ^ (1/2-μ^2/2) *
      pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t)) atTop (𝓝 (pcfLG_h μ)⁻¹) := by
  set p : ℝ := 1/2-μ^2/2
  set C₀ : ℝ := p * Real.log μ + p/2 * Real.log 2
  set r : ℝ → ℝ := fun t => Real.sqrt (t^2+1)
  set E : ℝ → ℝ := fun t => C₀ - 1/4 * Real.log ((t^2+1)/t^2) + μ^2/2 * (1 / (1 + r t / t)) +
    μ^2/2 * Real.log (1 + r t / t)
  have hlim : Tendsto E atTop (𝓝 (C₀ - 1/4 * Real.log 1 + μ^2/2 * (1/(1+1)) +
      μ^2/2 * Real.log (1+1))) := by
    have hq := pcfLG2_tendsto_sqrt_div
    exact ((tendsto_const_nhds.sub (tendsto_const_nhds.mul
      (pcfLG2_tendsto_sq_div'.log one_ne_zero))).add (tendsto_const_nhds.mul
      (tendsto_const_nhds.div (tendsto_const_nhds.add hq) (by norm_num)))).add
      (tendsto_const_nhds.mul ((tendsto_const_nhds.add hq).log (by norm_num)))
  have hval : C₀ - 1/4 * Real.log 1 + μ^2/2 * (1/(1+1)) + μ^2/2 * Real.log (1+1) =
      Real.log (pcfLG_h μ)⁻¹ := by
    rw [Real.log_inv, pcfLG_h, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow hμ, Real.log_exp]
    simp only [C₀, p]; norm_num; ring
  rw [hval] at hlim
  have := (Real.continuous_exp.tendsto _).comp hlim
  rw [Real.exp_log (inv_pos.2 (pcfLG_h_pos hμ))] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht0
  have hy : 0 < t^2+1 := by positivity
  have hr0 : 0 < r t := Real.sqrt_pos.2 hy
  have hr2 : r t ^ 2 = t^2+1 := Real.sq_sqrt hy.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : 0 < μ*t*Real.sqrt 2 := by positivity
  simp only [Function.comp, pcfLG2_PA]
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hy, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  simp only [E, C₀, pcfXiBar]
  have e1 : 1 / (1 + r t / t) = t * r t - t^2 := by
    have : r t + t ≠ 0 := by positivity
    field_simp
    nlinarith [hr2]
  have e2 : Real.log (1 + r t / t) = Real.log (t + r t) - Real.log t := by
    rw [show 1 + r t / t = (t + r t)/t by field_simp, Real.log_div (by positivity) ht0.ne']
  have e3 : Real.log ((t^2+1)/t^2) = Real.log (t^2+1) - 2 * Real.log t := by
    rw [Real.log_div hy.ne' (by positivity), Real.log_pow]; push_cast; ring
  have e4 : Real.log (μ*t*Real.sqrt 2) = Real.log μ + Real.log t + 1/2 * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hμ.ne' ht0.ne',
      Real.log_sqrt (by norm_num)]; ring
  rw [e1, e2, e3, e4]
  have : (μ*t*Real.sqrt 2)^2 = 2*μ^2*t^2 := by rw [mul_pow, mul_pow, hs2]; ring
  rw [this]
  simp only [r]
  ring

/-- `V(μ²/2, μ s √2) / (A(s) e^{μ²ξ̄(s)}) → h(μ)/√(π/2)` as `s → ∞` (from DLMF 12.9.2). -/
lemma pcfLG2_tendsto_PV_div {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => pcfV (μ^2/2) (μ*t*Real.sqrt 2) /
      ((pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t)) : ℝ)) atTop
      (𝓝 ((pcfLG_h μ / Real.sqrt (π/2) : ℝ) : ℂ)) := by
  set a : ℂ := (μ:ℂ)^2/2
  have hO := pcfV_sector_asymptotic a (δ := π/8) (by positivity) (by linarith [Real.pi_pos]) 1
  have hz2 : Tendsto (fun z : ℂ => z ^ (-(2*(1:ℕ):ℤ))) (sector (π/4-π/8)) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z‖) (sector (π/4-π/8)) atTop :=
      tendsto_comap.mono_left inf_le_left
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    have h2 := (tendsto_pow_atTop (two_ne_zero)).comp this |>.inv_tendsto_atTop
    refine h2.congr fun z => ?_
    simp
  have hE := (hO.trans_tendsto hz2).add_const 1
  simp only [zero_add, Finset.sum_range_one] at hE
  have hE' : Tendsto (fun z : ℂ => (Real.sqrt (π/2):ℂ) * cexp (-z^2/4) * z^(-a+1/2) * pcfV a z)
      (sector (π/4-π/8)) (𝓝 1) := by
    refine hE.congr fun z => ?_
    simp [pcfVTerm, poch_zero]
  have hT := hE'.comp (pcfLG_tendsto_sector (α := π/4-π/8) (by linarith [Real.pi_pos]) hμ)
  have hR := (Complex.continuous_ofReal.tendsto _).comp
    ((pcfLG2_tendsto_PRV hμ).const_mul (Real.sqrt (π/2)))
  have hs : 0 < Real.sqrt (π/2) := Real.sqrt_pos.2 (by positivity)
  have hRne : (Real.sqrt (π/2) * (pcfLG_h μ)⁻¹ : ℝ) ≠ 0 := by
    have := pcfLG_h_pos hμ; positivity
  have := hT.div hR (by exact_mod_cast hRne)
  rw [show ((pcfLG_h μ / Real.sqrt (π/2) : ℝ) : ℂ) =
    1 / ((Real.sqrt (π/2) * (pcfLG_h μ)⁻¹ : ℝ) : ℂ) by
      have := (pcfLG_h_pos hμ).ne'
      push_cast; field_simp]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hx : 0 < μ*t*Real.sqrt 2 := by positivity
  have hcp : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(-a+1/2) = (((μ*t*Real.sqrt 2)^(1/2-μ^2/2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx.le]; congr 1; simp only [a]; push_cast; ring
  have hp : 0 < (μ*t*Real.sqrt 2)^(1/2-μ^2/2) := Real.rpow_pos_of_pos hx _
  have hA : 0 < pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t) :=
    mul_pos (pcfLG2_PA_pos t) (Real.exp_pos _)
  have hden : ((Real.sqrt (π/2) * (Real.exp (-((μ*t*Real.sqrt 2)^2/4)) *
      (μ*t*Real.sqrt 2)^(1/2-μ^2/2) * pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t)) : ℝ) : ℂ) =
      (Real.sqrt (π/2):ℂ) * cexp (-((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) *
      ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(-a+1/2) *
      ((pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t) : ℝ) : ℂ) := by
    rw [hcp]; push_cast; ring_nf
  have hp' : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(-a+1/2) ≠ 0 := by rw [hcp]; exact_mod_cast hp.ne'
  have he : cexp (-((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) ≠ 0 := Complex.exp_ne_zero _
  have hs' : (Real.sqrt (π/2):ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [Function.comp, Pi.div_apply]
  rw [hden, mul_div_mul_left _ _ (mul_ne_zero (mul_ne_zero hs' he) hp')]
  push_cast; ring

/-- **The behaviour of `U(μ²/2, μt√2)` at `-∞`** (from DLMF 12.2.15 and 12.9.1–12.9.2):
`U / (A e^{-μ²ξ̄}) → √(2π) h(μ)/Γ(1/2+μ²/2)` as `t → -∞`. -/
lemma pcfLG2_tendsto_PU_div_atBot {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => pcfU (μ^2/2) (μ*t*Real.sqrt 2) /
      ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ)) atBot
      (𝓝 (((Real.sqrt (2*π) * pcfLG_h μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2))) := by
  set a : ℂ := (μ:ℂ)^2/2 with ha
  have hU := pcfLG2_tendsto_PU_div hμ
  have hV := pcfLG2_tendsto_PV_div hμ
  have he : Tendsto (fun s => ((Real.exp (-(2*μ^2 * pcfXiBar s)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s => -(2*μ^2 * pcfXiBar s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (pcfLG2_tendsto_xiBar.const_mul_atTop (by positivity))
    have h2 := (Real.tendsto_exp_atBot.comp h1).ofReal
    rw [Complex.ofReal_zero] at h2
    exact h2
  have hsum := ((hU.mul he).const_mul (-Complex.sin (π*a))).add (hV.const_mul (π / Gamma (1/2+a)))
  have hval : -Complex.sin (π*a) * ((((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) * 0) +
      π / Gamma (1/2+a) * ((pcfLG_h μ / Real.sqrt (π/2) : ℝ) : ℂ) =
      ((Real.sqrt (2*π) * pcfLG_h μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2) := by
    have hs : Real.sqrt (π/2) * Real.sqrt (2*π) = π := by
      rw [← Real.sqrt_mul (by positivity), show π/2*(2*π) = π^2 by ring,
        Real.sqrt_sq Real.pi_pos.le]
    have hs0 : Real.sqrt (π/2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    have hs' : (Real.sqrt (π/2) : ℂ) * (Real.sqrt (2*π) : ℂ) = (π : ℂ) := by exact_mod_cast hs
    have hs0' : (Real.sqrt (π/2) : ℂ) ≠ 0 := by exact_mod_cast hs0
    rw [mul_zero, mul_zero, zero_add, ← hs', ha]
    push_cast
    field_simp
  rw [hval] at hsum
  have key : Tendsto (fun s : ℝ => pcfU a (-((μ*s*Real.sqrt 2 : ℝ) : ℂ)) /
      ((pcfLG2_PA s * Real.exp (μ^2 * pcfXiBar s) : ℝ) : ℂ)) atTop
      (𝓝 (((Real.sqrt (2*π) * pcfLG_h μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2))) := by
    refine hsum.congr' (Eventually.of_forall fun s => ?_)
    have hA1 : ((pcfLG2_PA s * Real.exp (μ^2 * pcfXiBar s) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pcfLG2_PA_pos s) (Real.exp_pos _)).ne'
    have hA2 : ((pcfLG2_PA s * Real.exp (-(μ^2 * pcfXiBar s)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pcfLG2_PA_pos s) (Real.exp_pos _)).ne'
    beta_reduce
    rw [pcfU_neg_eq]
    have hx : ((μ*s*Real.sqrt 2 : ℝ) : ℂ) = (μ:ℂ) * s * Real.sqrt 2 := by push_cast; ring
    rw [hx]
    have hexp : Real.exp (-(2*μ^2 * pcfXiBar s)) =
        Real.exp (-(μ^2 * pcfXiBar s)) / Real.exp (μ^2 * pcfXiBar s) := by
      rw [← Real.exp_sub]; ring_nf
    rw [hexp]
    have h1 : (Real.exp (μ^2 * pcfXiBar s) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    have h2 : (Real.exp (-(μ^2 * pcfXiBar s)) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    have h3 : (pcfLG2_PA s : ℂ) ≠ 0 := by exact_mod_cast (pcfLG2_PA_pos s).ne'
    push_cast
    field_simp
    ring
  refine (key.comp tendsto_neg_atBot_atTop).congr fun t => ?_
  simp only [Function.comp, pcfLG2_PA_neg, pcfLG2_xiBar_neg]
  have : -(((μ*(-t)*Real.sqrt 2 : ℝ)) : ℂ) = (μ:ℂ) * t * Real.sqrt 2 := by push_cast; ring
  rw [this, ha]
  congr 2
  ring_nf

/-- The limits `c̄_s` of the barred coefficients at `+∞`. -/
noncomputable def pcfLG2_cbar (s : ℕ) : ℝ := (pcfLG2_Q s).coeff (3*s)

/-- **Whole-line Liouville–Green core for positive parameter**: for `μ ≥ μ₀` and every real `t`,
`U(μ²/2, μt√2) = H₊/L₊ · A e^{-μ²ξ̄}(S + e)` with `|e| ≤ C μ^{-2N}`, and the corresponding
formula for the derivative. -/
lemma pcfLG2_pos_core {N : ℕ} (hN : 1 ≤ N) : ∃ C μ₀ : ℝ, 0 ≤ C ∧ 1 ≤ μ₀ ∧ ∀ μ, μ₀ ≤ μ →
    |pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0 - 1| ≤ 1/2 ∧ ∀ t : ℝ,
      |pcfLG2_ser pcfLG2_Pa N (μ^2) t - 1| ≤ 1/2 ∧ ∃ e e' : ℝ,
      |e| ≤ C / (μ^2)^N ∧ |pcfLG2_PA t ^ 2 * e'| ≤ 2 * C / (μ^2)^(N-1) ∧
      pcfU (μ^2/2) (μ*t*Real.sqrt 2) = (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) /
        (pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0 : ℂ) *
        ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) * (pcfLG2_ser pcfLG2_Pa N (μ^2) t + e) : ℝ) : ℂ) ∧
      (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2) =
        (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) /
        (pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0 : ℂ) *
        ((Real.exp (-(μ^2 * pcfXiBar t)) * ((pcfLG2_PA1 t - μ^2 * (pcfLG2_PA t)⁻¹) *
          (pcfLG2_ser pcfLG2_Pa N (μ^2) t + e) +
          pcfLG2_PA t * (pcfLG2_ser pcfLG2_Pad N (μ^2) t + e')) : ℝ) : ℂ) := by
  set K : ℕ → ℝ := fun s => ∑ i ∈ Finset.range (3*s+1), |(pcfLG2_Q s).coeff i|
  have hK0 : ∀ s, 0 ≤ K s := fun s => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨Kd, hKd⟩ := pcfLG2_abs_Pad_le N
  have hcPad : Continuous (pcfLG2_Pad N) := continuous_iff_continuousAt.2 fun t =>
    (pcfLG2_hasDerivAt_Pa N t).continuousAt |> fun _ => (pcfLG2_hasDerivAt_Pad N t).continuousAt
  set I := Kd * π
  set V0 := 3/4 * π
  set C := I * Real.exp (V0/2) with hCdef
  set KS := ∑ s ∈ Finset.range N, K s
  have hKS : 0 ≤ KS := Finset.sum_nonneg fun s _ => hK0 s
  have hKd0 : 0 ≤ Kd := by
    have := (abs_nonneg _).trans (hKd 0)
    have h1 : 0 < (1 + (0:ℝ)^2)⁻¹ := by norm_num
    nlinarith
  have hC0 : 0 ≤ C := by positivity
  set μ₀ := max 1 (2*(KS+C)+1)
  have hμ₀ : 1 ≤ μ₀ := le_max_left _ _
  have hμ₀C : 2*((∑ s ∈ Finset.range N, K s) + C) ≤ μ₀^2 := by
    have := le_max_right 1 (2*(KS+C)+1); nlinarith
  refine ⟨C, μ₀, hC0, hμ₀, fun μ hμ => ?_⟩
  have hμ0 : 0 < μ := by linarith
  have hcore : ∀ b : ℝ, _ := fun b => pcfLG2_core (b := b) (A := pcfLG2_PA) (A1 := pcfLG2_PA1)
    (A2 := pcfLG2_PA2) (ξ := pcfXiBar) (fun t _ => pcfLG2_PA_pos t)
    (fun t _ => pcfLG2_hasDerivAt_PA t) (fun t _ => pcfLG2_hasDerivAt_PA1 t)
    (continuous_iff_continuousAt.2 fun t => (pcfLG2_hasDerivAt_PA1 t).continuousAt |>
      fun _ => by
        unfold pcfLG2_PA2
        exact (Continuous.mul (by fun_prop)
          (Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity))).continuousAt).continuousOn
    (fun t _ => by rw [pcfLG2_PA_sq_recip]; exact pcfLG2_hasDerivAt_xiBar t)
    (fun c _ => (pcfLG2_integrable_of_le pcfLG2_continuous_V pcfLG2_abs_V_le).integrableOn)
    (fun t _ => pcfLG2_tail_le pcfLG2_continuous_V pcfLG2_abs_V_le t)
    pcfLG2_tendsto_PA hN (a := pcfLG2_Pa) (ad := pcfLG2_Pad) (ad2 := pcfLG2_Pad2)
    (l := pcfLG2_cbar)
    (fun s _ t _ => pcfLG2_hasDerivAt_Pa s t)
    (fun s _ t _ => pcfLG2_hasDerivAt_Pad s t)
    (fun s _ => (pcfLG2_continuous_Pad2 s).continuousOn)
    (fun t => by simp [pcfLG2_Pa, pcfLG2_Q, pcfLG2_bar, pcfOlverU, pcfOlverPair])
    (fun t _ => by simp [pcfLG2_Pad, pcfLG2_R, pcfLG2_bar, pcfOlverPair])
    (fun s _ t _ => pcfLG2_P_recursion s t)
    (fun c _ => (pcfLG2_integrable_of_le hcPad hKd).integrableOn)
    (fun t _ => pcfLG2_tail_le hcPad hKd t) (K := K)
    (fun s _ t _ => pcfLG2_abs_Pa_le s t)
    (fun s _ => pcfLG2_tendsto_Pa s)
    (U := fun μ t => pcfU (μ^2/2) (μ*t*Real.sqrt 2))
    (U' := fun μ t => (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2))
    (H := fun μ => (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ)) (fun μ t _ => pcfLG2_hasDerivAt_PU μ t)
    (fun μ t _ => (pcfLG2_hasDerivAt_PU' μ t).congr_deriv (by rw [pcfLG2_PA_pow_four_recip]))
    (fun μ hμ => pcfLG2_tendsto_PU_div (by linarith)) le_rfl hμ₀ hμ₀C
  refine ⟨((hcore 0) μ hμ).1, fun t => ?_⟩
  obtain ⟨-, ε, ε', hε⟩ := (hcore (t-1)) μ hμ
  obtain ⟨h1, h2, h3, h4⟩ := hε t (by linarith)
  refine ⟨?_, ε t, ε' t, h1, h2, h3, h4⟩
  have hu1 : 1 ≤ μ^2 := by nlinarith
  have hser := pcfLG2_abs_sum_sub_one_le hN (f := fun s => pcfLG2_Pa s t)
    (by simp [pcfLG2_Pa, pcfLG2_Q, pcfLG2_bar, pcfOlverU, pcfOlverPair])
    (fun s _ => pcfLG2_abs_Pa_le s t) hu1
  refine hser.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have : μ₀^2 ≤ μ^2 := by nlinarith
  nlinarith

/-! ### Asymptotic expansions in reciprocal powers: algebra -/

/-- `f(u) ∼ ∑ a_s u^{-s}` as `u → ∞`. -/
def pcfLG2_HasExp (f : ℝ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ N : ℕ, (fun u : ℝ => f u - ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) =O[atTop]
    (fun u : ℝ => (u:ℂ)^(-(N:ℤ)))

/-- The truncation polynomial `∑_{s<N} a_s X^s`. -/
noncomputable def pcfLG2_trunc (N : ℕ) (a : ℕ → ℂ) : ℂ[X] :=
  ∑ s ∈ Finset.range N, C (a s) * X^s

/-- The Cauchy product of coefficient sequences. -/
def pcfLG2_cauchy (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ x ∈ Finset.antidiagonal n, a x.1 * b x.2

/-- The sign twist `a_n ↦ (-1)^n a_n` (the substitution `u ↦ -u`). -/
def pcfLG2_tw (a : ℕ → ℂ) (n : ℕ) : ℂ := (-1)^n * a n

/-- The unit sequence. -/
def pcfLG2_delta (n : ℕ) : ℂ := if n = 0 then 1 else 0

lemma pcfLG2_trunc_eval (N : ℕ) (a : ℕ → ℂ) {u : ℝ} (_hu : u ≠ 0) :
    (pcfLG2_trunc N a).eval ((u:ℂ)⁻¹) = ∑ s ∈ Finset.range N, a s / (u:ℂ)^s := by
  rw [pcfLG2_trunc, eval_finsetSum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [div_eq_mul_inv, inv_pow]

lemma pcfLG2_trunc_coeff (N : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    (pcfLG2_trunc N a).coeff n = if n < N then a n else 0 := by
  rw [pcfLG2_trunc, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hn; exact absurd (Finset.mem_range.2 h) hn
  · refine Finset.sum_eq_zero fun s hs => ?_
    have : s ≠ n := by rintro rfl; exact h (Finset.mem_range.1 hs)
    simp [Ne.symm this]

/-- A polynomial with vanishing coefficients below `N`, evaluated at `1/u`, is `O(u^{-N})`. -/
lemma pcfLG2_isBigO_eval_recip {Q : ℂ[X]} {N : ℕ} (hQ : ∀ n < N, Q.coeff n = 0) :
    (fun u : ℝ => Q.eval ((u:ℂ)⁻¹)) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
  obtain ⟨Q', hQ'⟩ := (X_pow_dvd_iff).2 hQ
  have hb : (fun u : ℝ => Q'.eval ((u:ℂ)⁻¹)) =O[atTop] (fun _ => (1:ℂ)) := by
    have h1 : Tendsto (fun u : ℝ => ((u:ℂ)⁻¹)) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
      simpa using this
    exact ((Q'.continuous.tendsto 0).comp h1).isBigO_one ℂ
  refine (hb.mul (isBigO_refl (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) atTop)).congr' ?_ ?_
  · filter_upwards with u
    rw [hQ', eval_mul, eval_pow, eval_X, zpow_neg, zpow_natCast, inv_pow]; ring
  · filter_upwards with u; ring

/-- A truncation is eventually bounded. -/
lemma pcfLG2_trunc_isBigO_one (N : ℕ) (a : ℕ → ℂ) :
    (fun u : ℝ => ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) =O[atTop] (fun _ => (1:ℂ)) := by
  have h1 : Tendsto (fun u : ℝ => ((u:ℂ)⁻¹)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
    simpa using this
  refine (((pcfLG2_trunc N a).continuous.tendsto 0).comp h1).isBigO_one ℂ |>.congr' ?_
    EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with u hu
  exact pcfLG2_trunc_eval N a hu

/-- An expansion gives boundedness. -/
lemma pcfLG2_HasExp.isBigO_one {f : ℝ → ℂ} {a : ℕ → ℂ} (h : pcfLG2_HasExp f a) :
    f =O[atTop] (fun _ => (1:ℂ)) := by
  have := h 0
  simpa using this

/-- Uniqueness of asymptotic expansions. -/
lemma pcfLG2_HasExp.unique {f : ℝ → ℂ} {a b : ℕ → ℂ} (ha : pcfLG2_HasExp f a)
    (hb : pcfLG2_HasExp f b) : a = b := by
  funext n
  rw [← pcfLG_asymptoticCoeff_eq ha n, pcfLG_asymptoticCoeff_eq hb n]

/-- Products of expansions. -/
lemma pcfLG2_HasExp.mul {f g : ℝ → ℂ} {a b : ℕ → ℂ} (ha : pcfLG2_HasExp f a)
    (hb : pcfLG2_HasExp g b) : pcfLG2_HasExp (fun u => f u * g u) (pcfLG2_cauchy a b) := by
  intro N
  have hQ : ∀ n < N, (pcfLG2_trunc N a * pcfLG2_trunc N b - pcfLG2_trunc N (pcfLG2_cauchy a b)).coeff n = 0 := by
    intro n hn
    rw [coeff_sub, coeff_mul, pcfLG2_trunc_coeff]
    simp only [hn, ↓reduceIte]
    rw [pcfLG2_cauchy, sub_eq_zero]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_antidiagonal.1 hx
    rw [pcfLG2_trunc_coeff, pcfLG2_trunc_coeff]
    simp [show x.1 < N by omega, show x.2 < N by omega]
  have h3 := pcfLG2_isBigO_eval_recip hQ
  have h1 : (fun u : ℝ => (f u - ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) * g u) =O[atTop]
      (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    simpa only [mul_one] using (ha N).mul hb.isBigO_one
  have h2 : (fun u : ℝ => (∑ s ∈ Finset.range N, a s / (u:ℂ)^s) *
      (g u - ∑ s ∈ Finset.range N, b s / (u:ℂ)^s)) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    simpa only [one_mul] using (pcfLG2_trunc_isBigO_one N a).mul (hb N)
  refine ((h1.add h2).add h3).congr' ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with u hu
    simp only [eval_sub, eval_mul, pcfLG2_trunc_eval _ _ hu]
    ring
  · filter_upwards with u; ring

/-- Sums of expansions. -/
lemma pcfLG2_HasExp.sub {f g : ℝ → ℂ} {a b : ℕ → ℂ} (ha : pcfLG2_HasExp f a)
    (hb : pcfLG2_HasExp g b) : pcfLG2_HasExp (fun u => f u - g u) (fun n => a n - b n) := by
  intro N
  refine ((ha N).sub (hb N)).congr' (Eventually.of_forall fun u => ?_) EventuallyEq.rfl
  simp only [sub_div, Finset.sum_sub_distrib]; ring

/-- Expansion of a function that is `O(u^{-N})` for every `N`. -/
lemma pcfLG2_HasExp.of_isBigO {f : ℝ → ℂ}
    (h : ∀ N : ℕ, f =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ)))) : pcfLG2_HasExp f 0 := by
  intro N; simpa using h N

/-- **Reciprocals of expansions.** -/
lemma pcfLG2_HasExp.recip {f : ℝ → ℂ} {a d : ℕ → ℂ} (ha : pcfLG2_HasExp f a)
    (had : pcfLG2_cauchy a d = pcfLG2_delta) (hf : (fun u => (f u)⁻¹) =O[atTop] (fun _ => (1:ℂ)))
    (hf0 : ∀ᶠ u in atTop, f u ≠ 0) :
    pcfLG2_HasExp (fun u => (f u)⁻¹) d := by
  intro N
  have hQ : ∀ n < N, (pcfLG2_trunc N a * pcfLG2_trunc N d - 1).coeff n = 0 := by
    intro n hn
    rw [coeff_sub, coeff_mul, coeff_one, sub_eq_zero]
    have h := congrFun had n
    rw [pcfLG2_cauchy, pcfLG2_delta] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_antidiagonal.1 hx
    rw [pcfLG2_trunc_coeff, pcfLG2_trunc_coeff]
    simp [show x.1 < N by omega, show x.2 < N by omega]
  have h3 := pcfLG2_isBigO_eval_recip hQ
  have h1 : (fun u : ℝ => (f u - ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) *
      ∑ s ∈ Finset.range N, d s / (u:ℂ)^s) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    simpa only [mul_one] using (ha N).mul (pcfLG2_trunc_isBigO_one N d)
  -- `1 - f T_N d = -(f - T_N a) T_N d - (T_N a T_N d - 1)`
  have hk : (fun u : ℝ => -((f u)⁻¹ * ((f u - ∑ s ∈ Finset.range N, a s / (u:ℂ)^s) *
      ∑ s ∈ Finset.range N, d s / (u:ℂ)^s + (pcfLG2_trunc N a * pcfLG2_trunc N d - 1).eval
        ((u:ℂ)⁻¹)))) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    simpa only [one_mul] using (hf.mul (h1.add h3)).neg_left
  refine (hk.congr' ?_ ?_)
  · filter_upwards [eventually_ne_atTop 0, hf0] with u hu hfu
    simp only [eval_sub, eval_mul, eval_one, pcfLG2_trunc_eval _ _ hu]
    field_simp
    ring
  · filter_upwards with u; ring

/-- The sign twist is multiplicative. -/
lemma pcfLG2_cauchy_tw (a b : ℕ → ℂ) :
    pcfLG2_cauchy (pcfLG2_tw a) (pcfLG2_tw b) = pcfLG2_tw (pcfLG2_cauchy a b) := by
  funext n
  simp only [pcfLG2_cauchy, pcfLG2_tw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.mem_antidiagonal.1 hx, pow_add]; ring

/-- The twist is an involution. -/
lemma pcfLG2_tw_tw (a : ℕ → ℂ) : pcfLG2_tw (pcfLG2_tw a) = a := by
  funext n; simp only [pcfLG2_tw]; rw [← mul_assoc, ← mul_pow]; norm_num

/-- Cauchy product is commutative. -/
lemma pcfLG2_cauchy_comm (a b : ℕ → ℂ) : pcfLG2_cauchy a b = pcfLG2_cauchy b a := by
  funext n
  simp only [pcfLG2_cauchy]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp [mul_comm]

/-- Cauchy product is additive. -/
lemma pcfLG2_cauchy_add (a b c : ℕ → ℂ) :
    pcfLG2_cauchy a (fun n => b n + c n) = fun n => pcfLG2_cauchy a b n + pcfLG2_cauchy a c n := by
  funext n; simp only [pcfLG2_cauchy, mul_add, Finset.sum_add_distrib]

/-- Cauchy product with the unit. -/
lemma pcfLG2_cauchy_delta (a : ℕ → ℂ) : pcfLG2_cauchy a pcfLG2_delta = a := by
  funext n
  simp only [pcfLG2_cauchy, pcfLG2_delta]
  rw [Finset.sum_eq_single (n, 0)]
  · simp
  · intro x hx hne
    have h := Finset.mem_antidiagonal.1 hx
    have : x.2 ≠ 0 := by
      intro h2; apply hne; ext <;> simp_all
    simp [this]
  · intro h; exact absurd (Finset.mem_antidiagonal.2 (by simp)) h

/-- Cauchy product with a scalar multiple. -/
lemma pcfLG2_cauchy_smul (a b : ℕ → ℂ) (k : ℂ) :
    pcfLG2_cauchy a (fun n => k * b n) = fun n => k * pcfLG2_cauchy a b n := by
  funext n; simp only [pcfLG2_cauchy, Finset.mul_sum]; congr 1; funext x; ring

/-- **The expansion of `Γ(1/2+z)/(√(2π)e^{-z}z^z)` at `z = u/2`** (DLMF 12.10.16). -/
lemma pcfLG2_HasExp_gamma : pcfLG2_HasExp
    (fun u : ℝ => Gamma (1/2+((u/2:ℝ):ℂ))/((Real.sqrt (2*π):ℂ)*exp (-((u/2:ℝ):ℂ))*
      (((u/2:ℝ):ℂ))^(((u/2:ℝ):ℂ))))
    (fun j => pcfGammaCoeff j * 2^j) := by
  intro N
  have h2 : Tendsto (fun u : ℝ => u/2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have h := (pcfGammaCoeff_expansion N).comp_tendsto h2
  have hb : (fun u : ℝ => ((u/2:ℝ):ℂ)^(-(N:ℤ))) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
    refine IsBigO.of_bound (2^N) (Eventually.of_forall fun u => ?_)
    rw [norm_zpow, norm_zpow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_div, abs_two, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
      div_pow, inv_div]
    rw [div_eq_mul_inv]
  refine (h.trans hb).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with u hu
  have hu' : (u:ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  simp only [Function.comp]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [div_pow]
  field_simp

/-- **Borel's lemma** in the form of `pcfLG2_HasExp`, for real coefficients. -/
lemma pcfLG2_exists_HasExp (c : ℕ → ℝ) :
    ∃ Φ : ℝ → ℝ, pcfLG2_HasExp (fun u => (Φ u : ℂ)) (fun s => (c s : ℂ)) := by
  obtain ⟨Φ, hΦ⟩ := pcfLG_exists_asymptotic c
  refine ⟨Φ, fun N => ?_⟩
  obtain ⟨B, hB⟩ := (hΦ N).bound
  refine IsBigO.of_bound B ?_
  filter_upwards [hB, eventually_gt_atTop 0] with u hu hu0
  have e : (Φ u : ℂ) - ∑ s ∈ Finset.range N, (c s : ℂ) / (u:ℂ)^s =
      ((Φ u - ∑ s ∈ Finset.range N, c s / u^s : ℝ) : ℂ) := by push_cast; rfl
  rw [e, Complex.norm_real, norm_zpow, Complex.norm_real, zpow_neg, zpow_natCast]
  rwa [norm_inv, norm_pow] at hu

/-- An expansion in `u` gives one in `μ²`. -/
lemma pcfLG2_HasExp.comp_sq {f : ℝ → ℂ} {a : ℕ → ℂ} (h : pcfLG2_HasExp f a) (N : ℕ) :
    (fun μ : ℝ => f (μ^2) - ∑ s ∈ Finset.range N, a s / (μ^2:ℂ)^s) =O[atTop]
      (fun μ : ℝ => (μ:ℂ)^(-(2*N:ℤ))) := by
  have h2 : Tendsto (fun μ : ℝ => μ^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  refine ((h N).comp_tendsto h2).congr' (Eventually.of_forall fun μ => ?_)
    (Eventually.of_forall fun μ => ?_)
  · simp only [Function.comp]; push_cast; rfl
  · simp only [Function.comp]; push_cast
    rw [show (2*N:ℤ) = ((2*N:ℕ):ℤ) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
      zpow_natCast, pow_mul]

/-- `μ√2 h(μ)² = e^{-z} z^z` with `z = μ²/2`. -/
lemma pcfLG2_h_sq {μ : ℝ} (hμ : 0 < μ) :
    μ * Real.sqrt 2 * pcfLG_h μ ^ 2 = Real.exp (-(μ^2/2)) * (μ^2/2) ^ (μ^2/2) := by
  have hz : 0 < μ^2/2 := by positivity
  have hh := pcfLG_h_pos hμ
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_rpow hz, Real.log_div (by positivity) (by norm_num), Real.log_pow,
    Real.log_sqrt (by norm_num), pcfLG_h, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
    Real.log_rpow hμ, Real.log_exp]
  push_cast; ring

/-- `H₋/H₊ = 1/R̃(μ²/2)`, with `R̃(z) = Γ(1/2+z)/(√(2π)e^{-z}z^z)`. -/
lemma pcfLG2_ratio_eq {μ : ℝ} (hμ : 0 < μ) :
    ((Real.sqrt (2*π) * pcfLG_h μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2) /
      (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) =
    (Gamma (1/2+((μ^2/2:ℝ):ℂ))/((Real.sqrt (2*π):ℂ)*exp (-((μ^2/2:ℝ):ℂ))*
      (((μ^2/2:ℝ):ℂ))^(((μ^2/2:ℝ):ℂ))))⁻¹ := by
  have hz : 0 < μ^2/2 := by positivity
  have hh := pcfLG_h_pos hμ
  have hG : Gamma (1/2 + ((μ^2/2:ℝ):ℂ)) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    rw [add_re, ofReal_re]; norm_num; positivity)
  have hcp : (((μ^2/2:ℝ):ℂ))^(((μ^2/2:ℝ):ℂ)) = (((μ^2/2) ^ (μ^2/2) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow hz.le _).symm
  have he : exp (-((μ^2/2:ℝ):ℂ)) = ((Real.exp (-(μ^2/2)) : ℝ) : ℂ) := by push_cast; rfl
  have hsq := pcfLG2_h_sq hμ
  have h1 : (((μ^2/2:ℝ):ℂ)) = (μ:ℂ)^2/2 := by push_cast; ring
  rw [hcp, he, ← h1, inv_div]
  have hs : (Real.sqrt (2*π) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have hsq' : ((μ * Real.sqrt 2 * pcfLG_h μ ^ 2 : ℝ) : ℂ) =
      ((Real.exp (-(μ^2/2)) * (μ^2/2) ^ (μ^2/2) : ℝ) : ℂ) := by rw [hsq]
  push_cast at hsq' ⊢
  rw [mul_assoc (Real.sqrt (2*π) : ℂ), ← hsq']
  have : (pcfLG_h μ : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
  field_simp

/-- **The connection relation between `+∞` and `-∞`**: comparing the whole-line expansion with
the behaviour of `U` at `-∞` gives `|L₊ H₋/H₊ - L₋| ≤ C μ^{-2N}`. -/
lemma pcfLG2_F1 {N : ℕ} (hN : 1 ≤ N) : ∃ C μ₀ : ℝ, 1 ≤ μ₀ ∧ ∀ μ, μ₀ ≤ μ →
    ‖(pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0 : ℂ) *
      (((Real.sqrt (2*π) * pcfLG_h μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2) /
        (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ)) -
      (pcfLG2_ser (fun s _ => (-1)^s * pcfLG2_cbar s) N (μ^2) 0 : ℂ)‖ ≤ C / (μ^2)^N := by
  obtain ⟨C, μ₀, hC, hμ₀, hcore⟩ := pcfLG2_pos_core hN
  refine ⟨C, μ₀, hμ₀, fun μ hμ => ?_⟩
  have hμ0 : 0 < μ := by linarith
  obtain ⟨hL, hct⟩ := hcore μ hμ
  set L := pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0 with hLdef
  set Hp : ℂ := (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) with hHpdef
  have hL0 : (L:ℂ) ≠ 0 := by exact_mod_cast (by linarith [(abs_le.1 hL).1] : (0:ℝ) < L).ne'
  have hHp : Hp ≠ 0 := by
    have := pcfLG_h_pos hμ0
    simp only [Hp]; exact_mod_cast (by positivity : (0:ℝ) < (μ * Real.sqrt 2 * pcfLG_h μ)⁻¹).ne'
  set F : ℝ → ℂ := fun t => pcfU (μ^2/2) (μ*t*Real.sqrt 2) /
    ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) * L / Hp -
      (pcfLG2_ser pcfLG2_Pa N (μ^2) t : ℂ) with hFdef
  have hF : ∀ t, ‖F t‖ ≤ C/(μ^2)^N := by
    intro t
    obtain ⟨-, e, e', he, -, hU, -⟩ := hct t
    have hA : ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pcfLG2_PA_pos t) (Real.exp_pos _)).ne'
    have : F t = (e : ℂ) := by
      simp only [F]; rw [hU]
      rw [show (((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) *
        (pcfLG2_ser pcfLG2_Pa N (μ^2) t + e) : ℝ)) : ℂ) =
        ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) *
        ((pcfLG2_ser pcfLG2_Pa N (μ^2) t : ℂ) + e) by push_cast; ring]
      field_simp
      ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]; exact he
  have hser : Tendsto (fun t => (pcfLG2_ser pcfLG2_Pa N (μ^2) t : ℂ)) atBot
      (𝓝 (pcfLG2_ser (fun s _ => (-1)^s * pcfLG2_cbar s) N (μ^2) 0 : ℂ)) := by
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    exact tendsto_finsetSum _ fun s _ => (pcfLG2_tendsto_Pa_atBot s).div_const _
  have hFl := ((((pcfLG2_tendsto_PU_div_atBot hμ0).mul_const (L:ℂ)).div_const Hp).sub hser)
  have := le_of_tendsto hFl.norm (Eventually.of_forall hF)
  convert this using 2
  ring

/-- The function `R̃(u/2) = Γ(1/2+u/2)/(√(2π)e^{-u/2}(u/2)^{u/2})`. -/
noncomputable def pcfLG2_Rf (u : ℝ) : ℂ :=
  Gamma (1/2+((u/2:ℝ):ℂ))/((Real.sqrt (2*π):ℂ)*exp (-((u/2:ℝ):ℂ))*(((u/2:ℝ):ℂ))^(((u/2:ℝ):ℂ)))

/-- `u^{-(N+1)} = O(u^{-N})`. -/
lemma pcfLG2_isBigO_zpow_succ (N : ℕ) :
    (fun u : ℝ => (u:ℂ)^(-((N+1:ℕ):ℤ))) =O[atTop] (fun u : ℝ => (u:ℂ)^(-(N:ℤ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with u hu
  rw [one_mul, norm_zpow, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact zpow_le_zpow_right₀ hu (by push_cast; omega)

/-- **The normalizer identity, formal form**: with `c_s` the coefficient of `t^{3s}` in `u_s`
and `γ_s` the coefficients of DLMF 12.10.16,
`(∑ γ_j (u/2)^{-j}) (∑ c_s u^{-s}) = ∑ (-1)^s c_s u^{-s}` as formal series. -/
lemma pcfLG2_gamma_identity :
    pcfLG2_cauchy (fun j => pcfGammaCoeff j * 2^j) (fun s => (pcfLG_c s : ℂ)) =
      pcfLG2_tw (fun s => (pcfLG_c s : ℂ)) := by
  obtain ⟨Φ, hΦ⟩ := pcfLG2_exists_HasExp pcfLG_c
  obtain ⟨Ψ, hΨ⟩ := pcfLG2_exists_HasExp pcfLG2_cbar
  have hR : pcfLG2_HasExp pcfLG2_Rf (fun j => pcfGammaCoeff j * 2^j) := pcfLG2_HasExp_gamma
  have hcb : (fun s => (pcfLG2_cbar s : ℂ)) = pcfLG2_tw (fun s => (pcfLG_c s : ℂ)) := by
    funext s; simp [pcfLG2_cbar, pcfLG2_Q_coeff, pcfLG2_tw]
  have hdiff : pcfLG2_HasExp (fun u => (Ψ u : ℂ) - pcfLG2_Rf u * Φ u) 0 := by
    refine pcfLG2_HasExp.of_isBigO fun N => ?_
    obtain ⟨C, μ₀, hμ₀, hF⟩ := pcfLG2_F1 (N := N+1) (by omega)
    obtain ⟨B, hB⟩ := hR.isBigO_one.bound
    have h3 : (fun u : ℝ => (∑ s ∈ Finset.range (N+1), (pcfLG2_cbar s : ℂ) / (u:ℂ)^s) -
        pcfLG2_Rf u * ∑ s ∈ Finset.range (N+1), (pcfLG_c s : ℂ) / (u:ℂ)^s) =O[atTop]
        (fun u : ℝ => (u:ℂ)^(-((N+1:ℕ):ℤ))) := by
      refine IsBigO.of_bound (B*C) ?_
      filter_upwards [hB, eventually_ge_atTop (μ₀^2)] with u hBu hu
      have hu1 : 1 ≤ u := le_trans (by nlinarith) hu
      have hu0 : 0 < u := by linarith
      set μ := Real.sqrt u
      have hμu : μ^2 = u := Real.sq_sqrt hu0.le
      have hμ : μ₀ ≤ μ := by
        rw [← Real.sqrt_sq (by linarith : (0:ℝ) ≤ μ₀)]; exact Real.sqrt_le_sqrt hu
      have hμ0 : 0 < μ := Real.sqrt_pos.2 hu0
      have h := hF μ hμ
      rw [pcfLG2_ratio_eq hμ0, hμu] at h
      have hRf : pcfLG2_Rf u ≠ 0 := by
        unfold pcfLG2_Rf
        refine div_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by
          rw [add_re, ofReal_re]; norm_num; positivity)) ?_
        refine mul_ne_zero (mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne')
          (Complex.exp_ne_zero _)) ?_
        rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
          exact_mod_cast (by positivity : (0:ℝ) < u/2).ne')]
        exact_mod_cast (by positivity : (0:ℝ) < u/2).ne'
      have e1 : ((pcfLG2_ser (fun s _ => pcfLG2_cbar s) (N+1) u 0 : ℝ) : ℂ) =
          ∑ s ∈ Finset.range (N+1), (pcfLG2_cbar s : ℂ) / (u:ℂ)^s := by
        rw [pcfLG2_ser]; push_cast; rfl
      have e2 : ((pcfLG2_ser (fun s _ => (-1)^s * pcfLG2_cbar s) (N+1) u 0 : ℝ) : ℂ) =
          ∑ s ∈ Finset.range (N+1), (pcfLG_c s : ℂ) / (u:ℂ)^s := by
        rw [pcfLG2_ser]; push_cast
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [pcfLG2_cbar, pcfLG2_Q_coeff]; push_cast
        rw [← mul_assoc, ← mul_pow]; norm_num
      have e3 : pcfLG2_Rf u = Gamma (1/2+((u/2:ℝ):ℂ))/((Real.sqrt (2*π):ℂ)*exp (-((u/2:ℝ):ℂ))*
          (((u/2:ℝ):ℂ))^(((u/2:ℝ):ℂ))) := rfl
      rw [e1, e2, ← e3] at h
      have heq : (∑ s ∈ Finset.range (N+1), (pcfLG2_cbar s : ℂ) / (u:ℂ)^s) -
          pcfLG2_Rf u * ∑ s ∈ Finset.range (N+1), (pcfLG_c s : ℂ) / (u:ℂ)^s =
          pcfLG2_Rf u * ((∑ s ∈ Finset.range (N+1), (pcfLG2_cbar s : ℂ) / (u:ℂ)^s) *
            (pcfLG2_Rf u)⁻¹ - ∑ s ∈ Finset.range (N+1), (pcfLG_c s : ℂ) / (u:ℂ)^s) := by
        field_simp
      rw [heq, norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
        zpow_neg, zpow_natCast]
      have hBu' : ‖pcfLG2_Rf u‖ ≤ B := by simpa using hBu
      have hB0 : 0 ≤ B := (norm_nonneg _).trans hBu'
      calc ‖pcfLG2_Rf u‖ * ‖_‖ ≤ B * (C / u^(N+1)) := mul_le_mul hBu' h (norm_nonneg _) hB0
        _ = B * C * (u^(N+1))⁻¹ := by ring
    have h1 := hΨ (N+1)
    have h2 := hR.isBigO_one.mul (hΦ (N+1))
    simp only [one_mul] at h2
    refine (((h1.sub h2).add h3).trans (pcfLG2_isBigO_zpow_succ N)).congr'
      (Eventually.of_forall fun u => ?_) EventuallyEq.rfl
    simp only; ring
  have h := (hΨ.sub (hR.mul hΦ)).unique hdiff
  funext n
  have := congrFun h n
  simp only [Pi.zero_apply, sub_eq_zero] at this
  rw [← this]
  exact congrFun hcb n

/-- The even coefficients `c_s`, `s ≥ 2`, vanish (degree bound DLMF 12.10.11), so
`c + tw c = 2δ`. -/
lemma pcfLG2_c_add_tw : (fun n => (pcfLG_c n : ℂ) + pcfLG2_tw (fun s => (pcfLG_c s : ℂ)) n) =
    fun n => 2 * pcfLG2_delta n := by
  funext n
  rcases n with _ | m
  · simp [pcfLG2_tw, pcfLG2_delta, pcfLG_c_zero]; norm_num
  · simp only [pcfLG2_tw, pcfLG2_delta, Nat.succ_ne_zero, ite_false, mul_zero]
    rcases Nat.even_or_odd (m+1) with he | ho
    · have hd := (pcfOlverU_spec m).2
      simp only [he, ↓reduceIte] at hd
      have : pcfLG_c (m+1) = 0 := by
        rw [pcfLG_c]; exact coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
    · rw [ho.neg_one_pow]; ring

/-- `c · (δ + γ̃)/2 = δ`. -/
lemma pcfLG2_c_mul_d : pcfLG2_cauchy (fun s => (pcfLG_c s : ℂ))
    (fun n => 1/2 * (pcfLG2_delta n + pcfGammaCoeff n * 2^n)) = pcfLG2_delta := by
  rw [pcfLG2_cauchy_smul, pcfLG2_cauchy_add, pcfLG2_cauchy_delta, pcfLG2_cauchy_comm _
    (fun j => pcfGammaCoeff j * 2^j), pcfLG2_gamma_identity]
  funext n
  have := congrFun pcfLG2_c_add_tw n
  beta_reduce
  rw [this]; ring

/-- `tw c · (δ + tw γ̃)/2 = δ`. -/
lemma pcfLG2_twc_mul_d : pcfLG2_cauchy (pcfLG2_tw (fun s => (pcfLG_c s : ℂ)))
    (fun n => 1/2 * (pcfLG2_delta n + (-1)^n * (pcfGammaCoeff n * 2^n))) = pcfLG2_delta := by
  have h := congrArg pcfLG2_tw pcfLG2_gamma_identity
  rw [← pcfLG2_cauchy_tw, pcfLG2_tw_tw] at h
  rw [pcfLG2_cauchy_smul, pcfLG2_cauchy_add, pcfLG2_cauchy_delta]
  have h2 : pcfLG2_cauchy (pcfLG2_tw fun s => (pcfLG_c s : ℂ))
      (fun n => (-1)^n * (pcfGammaCoeff n * 2^n)) = fun s => (pcfLG_c s : ℂ) := by
    rw [pcfLG2_cauchy_comm]; exact h
  rw [h2]
  funext n
  have := congrFun pcfLG2_c_add_tw n
  beta_reduce
  rw [add_comm (pcfLG2_tw _ n), this]; ring

/-- **Reciprocal expansions in `μ²`**: if `G(μ) T_M(a)(μ²) - 1 = O(μ^{-2M})` for all `M` and
`a · d = δ`, then `G(μ) - T_M(d)(μ²) = O(μ^{-2M})` for all `M`. -/
lemma pcfLG2_recip_sq {G : ℝ → ℂ} {a d : ℕ → ℂ} (had : pcfLG2_cauchy a d = pcfLG2_delta)
    (hG : ∀ M : ℕ, (fun μ : ℝ => G μ * (∑ s ∈ Finset.range M, a s / (μ:ℂ)^(2*s)) - 1) =O[atTop]
      (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ)))) (M : ℕ) :
    (fun μ : ℝ => G μ - ∑ s ∈ Finset.range M, d s / (μ:ℂ)^(2*s)) =O[atTop]
      (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ))) := by
  have h2 : Tendsto (fun μ : ℝ => μ^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  -- conversions from `u` to `μ²`
  have hT : ∀ (b : ℕ → ℂ) (K : ℕ) (μ : ℝ), μ ≠ 0 →
      (pcfLG2_trunc K b).eval (((μ^2:ℝ):ℂ)⁻¹) = ∑ s ∈ Finset.range K, b s / (μ:ℂ)^(2*s) := by
    intro b K μ hμ
    rw [pcfLG2_trunc_eval K b (by positivity)]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast; rw [pow_mul]
  have hz : ∀ K : ℕ, ((fun u : ℝ => (u:ℂ)^(-(K:ℤ))) ∘ fun μ : ℝ => μ^2) =ᶠ[atTop]
      fun μ : ℝ => (μ:ℂ)^(-(2*K:ℤ)) := fun K => Eventually.of_forall fun μ => by
    simp only [Function.comp]; push_cast
    rw [show (2*K:ℤ) = ((2*K:ℕ):ℤ) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
      zpow_natCast, pow_mul]
  have hQ : ∀ n < M, (pcfLG2_trunc M a * pcfLG2_trunc M d - 1).coeff n = 0 := by
    intro n hn
    rw [coeff_sub, coeff_mul, coeff_one, sub_eq_zero]
    have h := congrFun had n
    rw [pcfLG2_cauchy, pcfLG2_delta] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_antidiagonal.1 hx
    rw [pcfLG2_trunc_coeff, pcfLG2_trunc_coeff]
    simp [show x.1 < M by omega, show x.2 < M by omega]
  have h3 := ((pcfLG2_isBigO_eval_recip hQ).comp_tendsto h2).trans_eventuallyEq (hz M)
  have hb : ∀ (b : ℕ → ℂ) (K : ℕ), (fun μ : ℝ => ∑ s ∈ Finset.range K, b s / (μ:ℂ)^(2*s)) =O[atTop]
      (fun _ => (1:ℂ)) := by
    intro b K
    refine ((pcfLG2_trunc_isBigO_one K b).comp_tendsto h2).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ne_atTop 0] with μ hμ
    simp only [Function.comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast; rw [pow_mul]
  -- `G` is bounded
  have ha0 : a 0 * d 0 = 1 := by
    have := congrFun had 0
    simpa [pcfLG2_cauchy, pcfLG2_delta] using this
  have ha0' : a 0 ≠ 0 := left_ne_zero_of_mul_eq_one ha0
  have hc : (fun μ : ℝ => (μ:ℂ)^(-(2*(1:ℕ):ℤ))) =O[atTop] (fun _ => (1:ℂ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with μ hμ
    rw [one_mul, norm_one, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact zpow_le_one_of_nonpos₀ hμ (by norm_num)
  have hG1 : G =O[atTop] (fun _ => (1:ℂ)) := by
    have := ((((hG 1).trans hc).add (isBigO_refl (fun _ => (1:ℂ)) atTop)).const_mul_left (a 0)⁻¹)
    refine this.congr' (Eventually.of_forall fun μ => ?_) EventuallyEq.rfl
    simp only [Finset.sum_range_one, pow_zero, mul_zero, div_one]
    field_simp
    ring
  have h4 : (fun μ : ℝ => -(G μ * (pcfLG2_trunc M a * pcfLG2_trunc M d - 1).eval
      (((μ^2:ℝ):ℂ)⁻¹)) + (∑ s ∈ Finset.range M, d s / (μ:ℂ)^(2*s)) *
      (G μ * (∑ s ∈ Finset.range M, a s / (μ:ℂ)^(2*s)) - 1)) =O[atTop]
      (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ))) := by
    have e1 : (fun μ : ℝ => G μ * (pcfLG2_trunc M a * pcfLG2_trunc M d - 1).eval
        (((μ^2:ℝ):ℂ)⁻¹)) =O[atTop] (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ))) := by
      simpa only [one_mul, Function.comp_def] using hG1.mul h3
    have e2 : (fun μ : ℝ => (∑ s ∈ Finset.range M, d s / (μ:ℂ)^(2*s)) *
        (G μ * (∑ s ∈ Finset.range M, a s / (μ:ℂ)^(2*s)) - 1)) =O[atTop]
        (fun μ : ℝ => (μ:ℂ)^(-(2*M:ℤ))) := by
      simpa only [one_mul] using (hb d M).mul (hG M)
    exact e1.neg_left.add e2
  refine h4.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with μ hμ
  simp only [eval_sub, eval_mul, eval_one, hT a M μ hμ, hT d M μ hμ]
  ring

/-- **DLMF 12.10.3 with the normalizer of DLMF 12.10.14**: the normalizer `g` of Olver's
expansion of `U(-½μ², μt√2)` for `t ≥ 1+δ` satisfies
`g(μ)/h(μ) ∼ 1 + ½ ∑ γ_s (½μ²)^{-s}` (`IsCylinderGNormalizer`). The proof combines
`pcf_negative_parameter_uniform_U` (`g/h · ∑ c_s μ^{-2s} ∼ 1`) with the formal identity
`(∑ c_s u^{-s})(1 + ∑ γ_s (u/2)^{-s}) = 2` (`pcfLG2_c_mul_d`), obtained from the whole-line
expansion for positive parameter. This is the `U`-part of `pcf_negative_parameter_uniform`. -/
@[dlmf 12.10.E3, dlmf 12.10.E14]
theorem pcf_negative_parameter_uniform_U_normalizer :
    ∃ g : ℝ → ℂ, IsCylinderGNormalizer g ∧ ∀ δ : ℝ, 0 < δ → HasCylinderUniformExpansion
      (fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2)/(g μ*exp (-μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ)))
      (fun s t => pcfOlverA s t) (Ici (1+δ)) := by
  obtain ⟨g, hg, hexp⟩ := pcf_negative_parameter_uniform_U
  refine ⟨g, fun N => ?_, hexp⟩
  have h := pcfLG2_recip_sq (G := fun μ => g μ / pcfH μ) (a := fun s => (pcfLG_c s : ℂ))
    pcfLG2_c_mul_d (fun M => hg M) (N+1)
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
  -- `Φ(μ²)` stays near `1`
  have hΦ1 : ∃ μ₁ : ℝ, 1 ≤ μ₁ ∧ ∀ μ, μ₁ ≤ μ → 1/2 ≤ Φ (μ^2) ∧ Φ (μ^2) ≤ 2 := by
    obtain ⟨B, μ₁, hB, hμ₁, hb⟩ := pcfLG2_borel_bound pcfLG2_cbar hΦ 1
    refine ⟨max μ₁ (2*B+1), le_trans hμ₁ (le_max_left _ _), fun μ hμ => ?_⟩
    have hμ1 : μ₁ ≤ μ := (le_max_left _ _).trans hμ
    have h := hb μ hμ1
    have hS : pcfLG2_ser (fun s _ => pcfLG2_cbar s) 1 (μ^2) 0 = 1 := by simp [pcfLG2_ser, hc0]
    rw [hS, pow_one] at h
    have hμB : 2*B+1 ≤ μ := (le_max_right _ _).trans hμ
    have hμ2 : 2*B ≤ μ^2 := by nlinarith
    have : B / μ^2 ≤ 1/2 := by rw [div_le_iff₀ (by nlinarith)]; linarith
    have := abs_le.1 (h.trans this)
    constructor <;> linarith [this.1, this.2]
  obtain ⟨μ₁, hμ₁, hΦb⟩ := hΦ1
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
