/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics

/-!
# Decay of Kummer's function on the negative real axis (DLMF 13.2.23, 13.7.2)

On the negative real axis the regularized Kummer function decays algebraically:
`𝐌(a,b,-t) ~ ∑ₛ (a)ₛ (a-b+1)ₛ / (s! Γ(b-a)) · t^{-a-s}` as `t → +∞`, for all complex `a, b`.
This is the ray `ph z = π` of DLMF 13.7.2 (where the exponentially small companion series is
dropped) and its leading term is DLMF 13.2.23 on that ray. The proof is Kummer's transformation
13.2.39, `𝐌(a,b,-t) = e^{-t} 𝐌(b-a,b,t)`, combined with the positive-axis expansion 13.7.1
(`hasAsymptoticExpansion_regularizedConfluent`).

Consequences proved here:

* `isBigO_regularizedHGFun_neg`: `𝐌(a,b,-t) = O(t^{-Re a})`;
* `exists_norm_regularizedHGFun_neg_le`: `‖𝐌(a,b,-t)‖ ≤ C (1+t)^{-Re a}` for all `t ≥ 0`;
* `exists_eventually_norm_regularizedHGFun_neg_le`: the same bound, with exponent loss `ε > 0`,
  locally uniformly in both parameters. The base case is Euler's integral 13.4.1 in its
  convergence region, compared with a fixed real-parameter Euler integral; the bound spreads
  to all parameters through the contiguous relations 13.3.4 and 13.3.20 (`n = 1`), which keep
  the decay exponent.

The locally uniform bound is what holomorphy of parametric integrals of `𝐌(a,b,-t)` in the
parameters requires.
-/

@[expose] public section

open Complex Filter Set Asymptotics MeasureTheory
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-! ### Fixed parameters -/

/-- **Expansion of `𝐌` on the negative real axis** (DLMF 13.7.2 on the ray `ph z = π`, where
the exponential series is exponentially small): for all complex `a, b`, as `t → +∞`,
`𝐌(a,b,-t) ~ ∑ₛ (a)ₛ (a-b+1)ₛ / (s! Γ(b-a)) · t^{-a-s}`; the coefficients are
`kummerCoeff (b - a) b s`. -/
@[dlmf 13.7.E2]
theorem hasAsymptoticExpansion_regularizedHGFun_neg (a b : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (t : ℝ) => (t : ℂ) ^ (-a - n))
      (kummerCoeff (b - a) b) (fun t : ℝ => regularizedHGFun {a} {b} (-(t : ℂ))) := by
  have h := (hasAsymptoticExpansion_regularizedConfluent (b - a) b).mul_left
    (fun t : ℝ => exp (-(t : ℂ)))
  refine (h.congr_scale fun n => Eventually.of_forall fun t => ?_).congr'
    (Eventually.of_forall fun t => ?_)
  · simp only
    rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
    congr 1
    ring
  · simp only [smul_eq_mul]
    rw [regularizedConfluent_kummer_transform a b (-(t : ℂ)), neg_neg]

/-- `t^s ≤ 2^{|s|} (1+t)^s` for `t ≥ 1` and every real `s`. -/
theorem kumDec_rpow_le_one_add {t : ℝ} (ht : 1 ≤ t) (s : ℝ) :
    t ^ s ≤ 2 ^ |s| * (1 + t) ^ s := by
  have ht0 : 0 < t := by linarith
  rcases le_or_gt 0 s with hs | hs
  · calc t ^ s ≤ (1 + t) ^ s := Real.rpow_le_rpow ht0.le (by linarith) hs
      _ ≤ 2 ^ |s| * (1 + t) ^ s := le_mul_of_one_le_left (by positivity)
          (Real.one_le_rpow (by norm_num) (abs_nonneg s))
  · have h1 : t ^ s ≤ ((1 + t) / 2) ^ s :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hs.le
    rw [Real.div_rpow (by linarith) (by norm_num), abs_of_neg hs, Real.rpow_neg (by norm_num)] at *
    calc t ^ s ≤ (1 + t) ^ s / 2 ^ s := h1
      _ = (2 ^ s)⁻¹ * (1 + t) ^ s := by ring

/-- **Algebraic decay of `𝐌` on the negative real axis**: `𝐌(a,b,-t) = O(t^{-Re a})`. -/
theorem isBigO_regularizedHGFun_neg (a b : ℂ) :
    (fun t : ℝ => regularizedHGFun {a} {b} (-(t : ℂ))) =O[atTop] fun t => t ^ (-a.re) := by
  have h1 := hasAsymptoticExpansion_regularizedHGFun_neg a b 1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero,
    Nat.cast_one] at h1
  have hp : ∀ c : ℂ, (fun t : ℝ => (t : ℂ) ^ c) =O[atTop] fun t => t ^ c.re := fun c =>
    IsBigO.of_bound 1 (by
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_cpow_eq_rpow_re_of_pos ht, Real.norm_of_nonneg (by positivity), one_mul])
  have h2 : (fun t : ℝ => (t : ℂ) ^ (-a - 1)) =O[atTop] fun t => t ^ (-a.re) := by
    refine (hp _).trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le ht (by simp)
  have h3 : (fun t : ℝ => (t : ℂ) ^ (-a) • kummerCoeff (b - a) b 0) =O[atTop]
      fun t => t ^ (-a.re) := by
    refine ((hp (-a)).const_mul_left (kummerCoeff (b - a) b 0)).congr_left fun t => ?_
    simp only [smul_eq_mul]
    ring
  exact ((h1.trans h2).add h3).congr_left fun t => by simp

/-- **Leading behaviour of `𝐌` on the negative real axis** (DLMF 13.2.23 on the ray
`ph z = π`): `t^a 𝐌(a,b,-t) → 1/Γ(b-a)` as `t → +∞`, for all complex `a, b`. -/
@[dlmf 13.2.E23]
theorem tendsto_cpow_mul_regularizedHGFun_neg (a b : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ a * regularizedHGFun {a} {b} (-(t : ℂ))) atTop
      (𝓝 (Gamma (b - a))⁻¹) := by
  have h := ((hasAsymptoticExpansion_regularizedHGFun_neg a b).mul_left
    (fun t : ℝ => (t : ℂ) ^ a)) 1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero, kummerCoeff_zero,
    smul_eq_mul, Nat.cast_one] at h
  have hT : Tendsto (fun t : ℝ => (t : ℂ) ^ a * (t : ℂ) ^ (-a - 1)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [← cpow_add _ _ ht0, show a + (-a - 1) = -1 by ring, cpow_neg_one]
  have := (h.trans_tendsto hT).add_const (Gamma (b - a))⁻¹
  simp only [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have h1 : (t : ℂ) ^ a * (t : ℂ) ^ (-a) = 1 := by
    rw [← cpow_add _ _ ht0, add_neg_cancel, cpow_zero]
  rw [h1]
  ring

/-- A function continuous on `[0,∞)` and `O(g)` at infinity, with `g` continuous and positive on
`[0,∞)`, is bounded by a multiple of `g` on `[0,∞)`. -/
theorem kumDec_exists_bound_of_isBigO {f : ℝ → ℂ} {g : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    (hg : ContinuousOn g (Ici 0)) (hgpos : ∀ t, 0 ≤ t → 0 < g t) (h : f =O[atTop] g) :
    ∃ C, ∀ t, 0 ≤ t → ‖f t‖ ≤ C * g t := by
  obtain ⟨C1, hC1⟩ := h.bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC1
  have hq : ContinuousOn (fun t => ‖f t‖ / g t) (Icc 0 (max T 0)) :=
    (hf.norm.div hg fun t ht => (hgpos t ht).ne').mono (fun t ht => ht.1)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  refine ⟨max C1 K, fun t ht => ?_⟩
  have hg0 := hgpos t ht
  rcases le_or_gt t (max T 0) with htT | htT
  · have h1 := hK t ⟨ht, htT⟩
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hg0.le), div_le_iff₀ hg0] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hg0.le)
  · have h1 := hT t (le_of_lt (lt_of_le_of_lt (le_max_left _ _) htT))
    rw [Real.norm_of_nonneg hg0.le] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0.le)

/-- `t ↦ M̃(a,b,-t)` is continuous on the real line. -/
theorem kumDec_continuous_neg (a b : ℂ) :
    Continuous fun t : ℝ => regularizedHGFun {a} {b} (-(t : ℂ)) :=
  continuous_regularizedConfluent.comp (by fun_prop :
    Continuous fun t : ℝ => (a, b, -(t : ℂ)))

/-- **Global decay bound on the negative real axis**: `‖𝐌(a,b,-t)‖ ≤ C (1+t)^{-Re a}` for all
`t ≥ 0`. -/
theorem exists_norm_regularizedHGFun_neg_le (a b : ℂ) :
    ∃ C, ∀ t : ℝ, 0 ≤ t → ‖regularizedHGFun {a} {b} (-(t : ℂ))‖ ≤ C * (1 + t) ^ (-a.re) := by
  refine kumDec_exists_bound_of_isBigO (kumDec_continuous_neg a b).continuousOn
    ((continuousOn_const.add continuousOn_id).rpow_const fun t ht => Or.inl (by
      simp only [mem_Ici] at ht; simp only [Pi.add_apply, id_eq]; linarith))
    (fun t ht => by positivity) ((isBigO_regularizedHGFun_neg a b).trans ?_)
  refine IsBigO.of_bound (2 ^ |-a.re|) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact kumDec_rpow_le_one_add ht _

/-! ### Locally uniform bounds in the parameters -/

/-- The Euler kernel of 13.4.1 at the argument `-t`. -/
def kumDec_eulerKernel (a b : ℂ) (t s : ℝ) : ℂ :=
  exp (-(t : ℂ) * s) * (s : ℂ) ^ (a - 1) * (1 - (s : ℂ)) ^ (b - a - 1)

/-- For `Re a > 0` and `Re(b-a) > 0`, the Euler kernel `e^{-ts} s^{a-1} (1-s)^{b-a-1}` is integrable
on `[0,1]`. -/
theorem kumDec_intervalIntegrable_eulerKernel {a b : ℂ} (ha : 0 < a.re) (hba : 0 < (b - a).re)
    (t : ℝ) : IntervalIntegrable (kumDec_eulerKernel a b t) volume 0 1 := by
  have h := (Complex.betaIntegral_convergent (u := a) (v := b - a) ha hba).continuousOn_mul
    (g := fun s : ℝ => exp (-(t : ℂ) * s)) (by fun_prop)
  refine h.congr fun s _ => ?_
  simp only [kumDec_eulerKernel]
  ring

/-- The modulus of the Euler kernel on `(0,1)` is `e^{-ts} s^{Re a - 1} (1-s)^{Re(b-a) - 1}`. -/
theorem kumDec_norm_eulerKernel (a b : ℂ) {t s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖kumDec_eulerKernel a b t s‖ =
      Real.exp (-(t * s)) * s ^ (a.re - 1) * (1 - s) ^ ((b - a).re - 1) := by
  have h1 : (1 - (s : ℂ)) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  simp only [kumDec_eulerKernel, norm_mul, Complex.norm_exp]
  rw [norm_cpow_eq_rpow_re_of_pos hs.1, h1, norm_cpow_eq_rpow_re_of_pos (by linarith [hs.2])]
  simp

/-- Euler's integral (DLMF 13.4.1) at negative real argument: `M̃(a,b,-t) = (Γ(a)Γ(b-a))⁻¹ ∫₀¹
e^{-ts} s^{a-1} (1-s)^{b-a-1} ds`. -/
theorem kumDec_regularizedHGFun_neg_eq {a b : ℂ} (ha : 0 < a.re) (hba : 0 < (b - a).re) (t : ℝ) :
    regularizedHGFun {a} {b} (-(t : ℂ)) =
      1 / (Gamma a * Gamma (b - a)) * ∫ s : ℝ in (0 : ℝ)..1, kumDec_eulerKernel a b t s := by
  rw [regularized_euler_integral ha hba]
  rfl

/-- Base case of the locally uniform bound: the Euler region `0 < re a < re b`. -/
theorem kumDec_bound_base {α₀ β₀ : ℂ} (ha : 0 < α₀.re) (hba : 0 < (β₀ - α₀).re) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C, ∀ᶠ p : ℂ × ℂ in 𝓝 (α₀, β₀), ∀ t : ℝ, 0 ≤ t →
      ‖regularizedHGFun {p.1} {p.2} (-(t : ℂ))‖ ≤ C * (1 + t) ^ (-α₀.re + ε) := by
  set σ := max (α₀.re - ε) (α₀.re / 2) with hσdef
  set τ := (β₀ - α₀).re / 2 with hτdef
  have hσ0 : 0 < σ := lt_max_of_lt_right (by linarith)
  have hσa : σ < α₀.re := max_lt (by linarith) (by linarith)
  have hσe : α₀.re - ε ≤ σ := le_max_left _ _
  have hτ0 : 0 < τ := by positivity
  have hτ : τ < (β₀ - α₀).re := by linarith
  obtain ⟨C0, hC0⟩ := exists_norm_regularizedHGFun_neg_le (σ : ℂ) ((σ + τ : ℝ) : ℂ)
  set G : ℂ × ℂ → ℂ := fun p => (Gamma p.1)⁻¹ * (Gamma (p.2 - p.1))⁻¹ with hGdef
  have hGc : Continuous G := by
    have h1 : Continuous fun w : ℂ => (Gamma w)⁻¹ := by
      simpa [one_div] using Complex.differentiable_one_div_Gamma.continuous
    exact (h1.comp continuous_fst).mul (h1.comp (continuous_snd.sub continuous_fst))
  set K := ‖G (α₀, β₀)‖ + 1 with hK
  have hev : ∀ᶠ p : ℂ × ℂ in 𝓝 (α₀, β₀), σ < p.1.re ∧ τ < (p.2 - p.1).re ∧ ‖G p‖ < K := by
    have c1 : Continuous fun p : ℂ × ℂ => p.1.re := by fun_prop
    have c2 : Continuous fun p : ℂ × ℂ => (p.2 - p.1).re := by fun_prop
    have hKl : ‖G (α₀, β₀)‖ < K := by rw [hK]; linarith
    refine ((continuousAt_const.eventually_lt c1.continuousAt hσa).and
      ((continuousAt_const.eventually_lt c2.continuousAt hτ).and
      (hGc.norm.continuousAt.eventually_lt continuousAt_const hKl))).mono ?_
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  have hστ : ((σ + τ : ℝ) : ℂ) - (σ : ℂ) = (τ : ℂ) := by push_cast; ring
  refine ⟨K * (‖Gamma (σ : ℂ) * Gamma (τ : ℂ)‖ * C0), ?_⟩
  filter_upwards [hev] with p hp t ht
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hpa : 0 < p.1.re := hσ0.trans hp1
  have hpb : 0 < (p.2 - p.1).re := hτ0.trans hp2
  have hσc : 0 < (σ : ℂ).re := by simpa using hσ0
  have hτc : 0 < (((σ + τ : ℝ) : ℂ) - (σ : ℂ)).re := by rw [hστ]; simpa using hτ0
  -- the real-parameter majorant
  have hI1 := kumDec_intervalIntegrable_eulerKernel hσc hτc t
  have hIp := kumDec_intervalIntegrable_eulerKernel hpa hpb t
  have hle : ∫ s : ℝ in (0 : ℝ)..1, ‖kumDec_eulerKernel p.1 p.2 t s‖ ≤
      ∫ s : ℝ in (0 : ℝ)..1, ‖kumDec_eulerKernel (σ : ℂ) ((σ + τ : ℝ) : ℂ) t s‖ := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hIp.norm hI1.norm ?_
    intro s hs
    rw [kumDec_norm_eulerKernel _ _ hs, kumDec_norm_eulerKernel _ _ hs, hστ]
    simp only [ofReal_re]
    have h1 : s ^ (p.1.re - 1) ≤ s ^ (σ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le (by linarith)
    have h2 : (1 - s) ^ ((p.2 - p.1).re - 1) ≤ (1 - s) ^ (τ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith [hs.2]) (by linarith [hs.1]) (by linarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) h2
      (Real.rpow_nonneg (by linarith [hs.2]) _)
      (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs.1.le _))
  have heq1 : ∫ s : ℝ in (0 : ℝ)..1, ‖kumDec_eulerKernel (σ : ℂ) ((σ + τ : ℝ) : ℂ) t s‖ =
      ‖∫ s : ℝ in (0 : ℝ)..1, kumDec_eulerKernel (σ : ℂ) ((σ + τ : ℝ) : ℂ) t s‖ := by
    have hc : ∫ s : ℝ in (0 : ℝ)..1, kumDec_eulerKernel (σ : ℂ) ((σ + τ : ℝ) : ℂ) t s =
        ((∫ s : ℝ in (0 : ℝ)..1, ‖kumDec_eulerKernel (σ : ℂ) ((σ + τ : ℝ) : ℂ) t s‖ : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun s hs => ?_
      rw [kumDec_norm_eulerKernel _ _ hs, hστ]
      have h1 : (1 - (s : ℂ)) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
      simp only [kumDec_eulerKernel, hστ, h1, ofReal_re]
      rw [show -(t : ℂ) * s = ((-(t * s) : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp,
        show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
        show (τ : ℂ) - 1 = ((τ - 1 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow hs.1.le, ← ofReal_cpow (by linarith [hs.2])]
      push_cast
      ring
    rw [hc, norm_real, Real.norm_of_nonneg (intervalIntegral.integral_nonneg (by norm_num)
      fun s _ => norm_nonneg _)]
  have hM1 := kumDec_regularizedHGFun_neg_eq hσc hτc t
  rw [hστ] at hM1
  have hΓ : Gamma (σ : ℂ) * Gamma (τ : ℂ) ≠ 0 :=
    mul_ne_zero (Gamma_ne_zero_of_re_pos hσc) (Gamma_ne_zero_of_re_pos (by simpa using hτ0))
  have hI1eq : ∫ s : ℝ in (0 : ℝ)..1, kumDec_eulerKernel (σ : ℂ) ((σ + τ : ℝ) : ℂ) t s =
      Gamma (σ : ℂ) * Gamma (τ : ℂ) * regularizedHGFun {(σ : ℂ)} {((σ + τ : ℝ) : ℂ)} (-(t : ℂ)) := by
    rw [hM1, ← mul_assoc, one_div, mul_inv_cancel₀ hΓ, one_mul]
  have hpow : (1 + t) ^ (-σ) ≤ (1 + t) ^ (-α₀.re + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc ‖regularizedHGFun {p.1} {p.2} (-(t : ℂ))‖
      = ‖G p‖ * ‖∫ s : ℝ in (0 : ℝ)..1, kumDec_eulerKernel p.1 p.2 t s‖ := by
        rw [kumDec_regularizedHGFun_neg_eq hpa hpb t, norm_mul, hGdef]
        simp only [one_div, mul_inv, norm_mul, norm_inv]
    _ ≤ K * ∫ s : ℝ in (0 : ℝ)..1, ‖kumDec_eulerKernel (σ : ℂ) ((σ + τ : ℝ) : ℂ) t s‖ := by
        gcongr
        exact (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans hle
    _ ≤ K * (‖Gamma (σ : ℂ) * Gamma (τ : ℂ)‖ * (C0 * (1 + t) ^ (-σ))) := by
        rw [heq1, hI1eq, norm_mul]
        gcongr
        simpa using hC0 t ht
    _ ≤ K * (‖Gamma (σ : ℂ) * Gamma (τ : ℂ)‖ * C0) * (1 + t) ^ (-α₀.re + ε) := by
        have hC0n : 0 ≤ C0 := by
          have h0 := hC0 0 le_rfl
          rw [add_zero, Real.one_rpow, mul_one] at h0
          exact (norm_nonneg _).trans h0
        have hK0 : 0 ≤ K := by positivity
        calc K * (‖Gamma (σ : ℂ) * Gamma (τ : ℂ)‖ * (C0 * (1 + t) ^ (-σ)))
            = K * (‖Gamma (σ : ℂ) * Gamma (τ : ℂ)‖ * C0) * (1 + t) ^ (-σ) := by ring
          _ ≤ _ := by gcongr

/-- The locally uniform decay property of `𝐌(·,·,-t)` near `(α₀, β₀)`, with exponent loss `ε`. -/
def kumDec_Bnd (α₀ β₀ : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C, ∀ᶠ p : ℂ × ℂ in 𝓝 (α₀, β₀), ∀ t : ℝ, 0 ≤ t →
    ‖regularizedHGFun {p.1} {p.2} (-(t : ℂ))‖ ≤ C * (1 + t) ^ (-α₀.re + ε)

/-- For `t ≥ 0`, `t (1+t)^{e-1} ≤ (1+t)^e`. -/
theorem kumDec_t_mul_rpow_le {t : ℝ} (ht : 0 ≤ t) (e : ℝ) :
    t * (1 + t) ^ (e - 1) ≤ (1 + t) ^ e := by
  have h : (1 + t) ^ e = (1 + t) ^ (e - 1) * (1 + t) := by
    rw [← Real.rpow_add_one (by linarith)]; ring_nf
  rw [h, mul_comm t]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- For `t ≥ 0`, `(1+t)^{e-1} ≤ (1+t)^e`. -/
theorem kumDec_rpow_sub_one_le {t : ℝ} (ht : 0 ≤ t) (e : ℝ) :
    (1 + t) ^ (e - 1) ≤ (1 + t) ^ e :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- A property eventually true near `(α₀+u, β₀+v)` holds eventually near `(α₀, β₀)` for the shifted
pair. -/
theorem kumDec_eventually_shift {P : ℂ × ℂ → Prop} (α₀ β₀ u v : ℂ)
    (h : ∀ᶠ p : ℂ × ℂ in 𝓝 (α₀ + u, β₀ + v), P p) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (α₀, β₀), P (p.1 + u, p.2 + v) := by
  have hc : Continuous fun p : ℂ × ℂ => (p.1 + u, p.2 + v) := by fun_prop
  exact hc.continuousAt.eventually h

/-- Near `(α₀, β₀)`, both coordinates are bounded by `|α₀| + 1` and `|β₀| + 1`. -/
theorem kumDec_eventually_norm_le (α₀ β₀ : ℂ) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (α₀, β₀), ‖p.1‖ ≤ ‖α₀‖ + 1 ∧ ‖p.2‖ ≤ ‖β₀‖ + 1 := by
  have c1 : Continuous fun p : ℂ × ℂ => ‖p.1‖ := by fun_prop
  have c2 : Continuous fun p : ℂ × ℂ => ‖p.2‖ := by fun_prop
  refine ((c1.continuousAt.eventually_lt continuousAt_const (by simp : ‖α₀‖ < ‖α₀‖ + 1)).and
    (c2.continuousAt.eventually_lt continuousAt_const (by simp : ‖β₀‖ < ‖β₀‖ + 1))).mono ?_
  exact fun p hp => ⟨hp.1.le, hp.2.le⟩

/-- Lowering `re (b - a)` by one: 13.3.20 with `n = 1`,
`𝐌(a,b,z) = b 𝐌(a,b+1,z) + a z 𝐌(a+1,b+2,z)`, keeps the decay exponent. -/
theorem kumDec_bnd_step_b {α₀ β₀ : ℂ} (h1 : kumDec_Bnd α₀ (β₀ + 1))
    (h2 : kumDec_Bnd (α₀ + 1) (β₀ + 2)) : kumDec_Bnd α₀ β₀ := by
  intro ε hε
  obtain ⟨C1, hC1⟩ := h1 ε hε
  obtain ⟨C2, hC2⟩ := h2 ε hε
  have hC1' := kumDec_eventually_shift α₀ β₀ 0 1 (by simpa using hC1)
  have hC2' := kumDec_eventually_shift α₀ β₀ 1 2 hC2
  refine ⟨(‖β₀‖ + 1) * |C1| + (‖α₀‖ + 1) * |C2|, ?_⟩
  filter_upwards [hC1', hC2', kumDec_eventually_norm_le α₀ β₀] with p hp1 hp2 hpn t ht
  simp only [add_zero] at hp1 hp2
  have hrel := regularizedConfluent_contiguous_mixed_b_pred p.1 (p.2 + 1) (-(t : ℂ))
  rw [add_sub_cancel_right, show p.2 + 1 + 1 = p.2 + 2 by ring] at hrel
  have he : regularizedHGFun {p.1} {p.2} (-(t : ℂ)) =
      p.2 * regularizedHGFun {p.1} {p.2 + 1} (-(t : ℂ)) +
        p.1 * (-(t : ℂ)) * regularizedHGFun {p.1 + 1} {p.2 + 2} (-(t : ℂ)) := by
    linear_combination -hrel
  set e := -α₀.re + ε with he_def
  have hb1 := hp1 t ht
  have hb2 : ‖regularizedHGFun {p.1 + 1} {p.2 + 2} (-(t : ℂ))‖ ≤ C2 * (1 + t) ^ (e - 1) := by
    convert hp2 t ht using 3; simp only [he_def, add_re, one_re]; ring
  have hx : 0 ≤ (1 + t) ^ e := by positivity
  have hx1 : 0 ≤ (1 + t) ^ (e - 1) := by positivity
  have hnt : ‖(-(t : ℂ))‖ = t := by rw [norm_neg, norm_real, Real.norm_of_nonneg ht]
  calc ‖regularizedHGFun {p.1} {p.2} (-(t : ℂ))‖
      ≤ ‖p.2‖ * ‖regularizedHGFun {p.1} {p.2 + 1} (-(t : ℂ))‖ +
          ‖p.1‖ * (t * ‖regularizedHGFun {p.1 + 1} {p.2 + 2} (-(t : ℂ))‖) := by
        rw [he]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, hnt, mul_assoc]
    _ ≤ (‖β₀‖ + 1) * (|C1| * (1 + t) ^ e) + (‖α₀‖ + 1) * (|C2| * (t * (1 + t) ^ (e - 1))) := by
        have hX := hb1.trans (mul_le_mul_of_nonneg_right (le_abs_self C1) hx)
        have hY : t * ‖regularizedHGFun {p.1 + 1} {p.2 + 2} (-(t : ℂ))‖ ≤
            |C2| * (t * (1 + t) ^ (e - 1)) := by
          calc t * ‖regularizedHGFun {p.1 + 1} {p.2 + 2} (-(t : ℂ))‖
              ≤ t * (|C2| * (1 + t) ^ (e - 1)) := mul_le_mul_of_nonneg_left
                (hb2.trans (mul_le_mul_of_nonneg_right (le_abs_self C2) hx1)) ht
            _ = |C2| * (t * (1 + t) ^ (e - 1)) := by ring
        exact add_le_add (mul_le_mul hpn.2 hX (norm_nonneg _) (by positivity))
          (mul_le_mul hpn.1 hY (by positivity) (by positivity))
    _ ≤ (‖β₀‖ + 1) * (|C1| * (1 + t) ^ e) + (‖α₀‖ + 1) * (|C2| * (1 + t) ^ e) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (kumDec_t_mul_rpow_le ht e) (abs_nonneg C2)) (by positivity))
    _ = _ := by ring

/-- Lowering `re a` by one: 13.3.4, `𝐌(a,b,z) = 𝐌(a+1,b,z) - z 𝐌(a+1,b+1,z)`, keeps the decay
exponent. -/
theorem kumDec_bnd_step_a {α₀ β₀ : ℂ} (h1 : kumDec_Bnd (α₀ + 1) β₀)
    (h2 : kumDec_Bnd (α₀ + 1) (β₀ + 1)) : kumDec_Bnd α₀ β₀ := by
  intro ε hε
  obtain ⟨C1, hC1⟩ := h1 ε hε
  obtain ⟨C2, hC2⟩ := h2 ε hε
  have hC1' := kumDec_eventually_shift α₀ β₀ 1 0 (by simpa using hC1)
  have hC2' := kumDec_eventually_shift α₀ β₀ 1 1 hC2
  refine ⟨|C1| + |C2|, ?_⟩
  filter_upwards [hC1', hC2'] with p hp1 hp2 t ht
  simp only [add_zero] at hp1 hp2
  have hrel := regularizedConfluent_contiguous_shift_a (p.1 + 1) p.2 (-(t : ℂ))
  rw [add_sub_cancel_right] at hrel
  have he : regularizedHGFun {p.1} {p.2} (-(t : ℂ)) =
      regularizedHGFun {p.1 + 1} {p.2} (-(t : ℂ)) -
        (-(t : ℂ)) * regularizedHGFun {p.1 + 1} {p.2 + 1} (-(t : ℂ)) := by
    linear_combination -hrel
  set e := -α₀.re + ε with he_def
  have hb1 : ‖regularizedHGFun {p.1 + 1} {p.2} (-(t : ℂ))‖ ≤ C1 * (1 + t) ^ (e - 1) := by
    convert hp1 t ht using 3; simp only [he_def]; ring
  have hb2 : ‖regularizedHGFun {p.1 + 1} {p.2 + 1} (-(t : ℂ))‖ ≤ C2 * (1 + t) ^ (e - 1) := by
    convert hp2 t ht using 3; simp only [he_def, add_re, one_re]; ring
  have hx1 : 0 ≤ (1 + t) ^ (e - 1) := by positivity
  have hnt : ‖(-(t : ℂ))‖ = t := by rw [norm_neg, norm_real, Real.norm_of_nonneg ht]
  calc ‖regularizedHGFun {p.1} {p.2} (-(t : ℂ))‖
      ≤ ‖regularizedHGFun {p.1 + 1} {p.2} (-(t : ℂ))‖ +
          t * ‖regularizedHGFun {p.1 + 1} {p.2 + 1} (-(t : ℂ))‖ := by
        rw [he]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, hnt]
    _ ≤ |C1| * (1 + t) ^ (e - 1) + t * (|C2| * (1 + t) ^ (e - 1)) :=
        add_le_add (hb1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hx1))
          (mul_le_mul_of_nonneg_left (hb2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hx1))
            ht)
    _ = |C1| * (1 + t) ^ (e - 1) + |C2| * (t * (1 + t) ^ (e - 1)) := by ring
    _ ≤ |C1| * (1 + t) ^ e + |C2| * (1 + t) ^ e :=
        add_le_add (mul_le_mul_of_nonneg_left (kumDec_rpow_sub_one_le ht e) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (kumDec_t_mul_rpow_le ht e) (abs_nonneg _))
    _ = _ := by ring

/-- The locally uniform decay bound `|M̃(α,β,-t)| ≤ C (1+t)^{-Re α₀ + ε}` holds at every `(α₀, β₀)`,
by induction on the shifts needed to reach `Re α > 0`, `Re(β-α) > 0`. -/
theorem kumDec_bnd_all : ∀ (m k : ℕ) (α₀ β₀ : ℂ), -(m : ℝ) < α₀.re → -(k : ℝ) < (β₀ - α₀).re →
    kumDec_Bnd α₀ β₀ := by
  intro m
  induction m with
  | zero =>
    intro k
    induction k with
    | zero =>
      intro α₀ β₀ ha hb
      simp only [CharP.cast_eq_zero, neg_zero] at ha hb
      exact fun ε hε => kumDec_bound_base ha hb hε
    | succ k ih =>
      intro α₀ β₀ ha hb
      refine kumDec_bnd_step_b (ih α₀ (β₀ + 1) ha ?_) (ih (α₀ + 1) (β₀ + 2) ?_ ?_)
      · simp only [sub_re, add_re, one_re] at hb ⊢; push_cast at hb; linarith
      · simp only [CharP.cast_eq_zero, neg_zero, add_re, one_re] at ha ⊢; linarith
      · simp only [sub_re, add_re, one_re] at hb ⊢
        rw [show (2 : ℂ).re = 2 by norm_num]; push_cast at hb; linarith
  | succ m ih =>
    intro k α₀ β₀ ha hb
    refine kumDec_bnd_step_a (ih (k + 1) (α₀ + 1) β₀ ?_ ?_) (ih (k + 1) (α₀ + 1) (β₀ + 1) ?_ ?_)
    · simp only [add_re, one_re] at ha ⊢; push_cast at ha; linarith
    · simp only [sub_re, add_re, one_re] at hb ⊢; push_cast; linarith
    · simp only [add_re, one_re] at ha ⊢; push_cast at ha; linarith
    · simp only [sub_re, add_re, one_re] at hb ⊢; push_cast; linarith

/-- **Locally uniform decay of `𝐌` on the negative real axis**: for all `α₀, β₀` and `ε > 0`
there are `C` and a neighbourhood of `(α₀, β₀)` on which
`‖𝐌(a,b,-t)‖ ≤ C (1+t)^{-re α₀ + ε}` for all `t ≥ 0`. -/
theorem exists_eventually_norm_regularizedHGFun_neg_le (α₀ β₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ᶠ p : ℂ × ℂ in 𝓝 (α₀, β₀), ∀ t : ℝ, 0 ≤ t →
      ‖regularizedHGFun {p.1} {p.2} (-(t : ℂ))‖ ≤ C * (1 + t) ^ (-α₀.re + ε) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-α₀.re)
  obtain ⟨k, hk⟩ := exists_nat_gt (-(β₀ - α₀).re)
  exact kumDec_bnd_all m k α₀ β₀ (by linarith) (by linarith) ε hε

/-! ### Integrability -/

/-- Integrability of `t^{c-1} 𝐌(a,b,-t) h(t)` on `(0,∞)` when `h` is continuous and
`O((1+t)^{-r})`, for `0 < re c < re a + r`. -/
theorem integrableOn_cpow_mul_regularizedHGFun_neg_mul {a b c : ℂ} {h : ℝ → ℂ} {K r : ℝ}
    (hh : ContinuousOn h (Ioi 0)) (hbd : ∀ t : ℝ, 0 < t → ‖h t‖ ≤ K * (1 + t) ^ (-r))
    (hc : 0 < c.re) (hca : c.re < a.re + r) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (c - 1) * regularizedHGFun {a} {b} (-(t : ℂ)) * h t)
      (Ioi 0) := by
  obtain ⟨C, hC⟩ := exists_norm_regularizedHGFun_neg_le a b
  have hmaj := (DLMF.Gamma.integrableOn_rpow_mul_one_add_rpow hc hca).const_mul (|C| * |K|)
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (c - 1) * regularizedHGFun {a} {b} (-(t : ℂ)) *
      h t) (Ioi 0) := by
    refine ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const fun t ht =>
      ofReal_mem_slitPlane.mpr ht).mul (kumDec_continuous_neg a b).continuousOn).mul hh
  refine hmaj.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have h1 := hC t ht0.le
  have h2 := hbd t ht0
  have hp : (1 + t) ^ (-a.re) * (1 + t) ^ (-r) = (1 + t) ^ (-(a.re + r)) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
  calc t ^ (c.re - 1) * ‖regularizedHGFun {a} {b} (-(t : ℂ))‖ * ‖h t‖
      ≤ t ^ (c.re - 1) * (|C| * (1 + t) ^ (-a.re)) * (|K| * (1 + t) ^ (-r)) := by
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        · exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    _ = |C| * |K| * (t ^ (c.re - 1) * (1 + t) ^ (-(a.re + r))) := by rw [← hp]; ring

end DLMF.Confluent
