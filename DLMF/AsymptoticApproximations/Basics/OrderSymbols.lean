/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Basics.Defs
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Order symbols and asymptotic expansions (DLMF §2.1)

The definitions 2.1.1–2.1.3 of `∼`, `o` and `O` are Mathlib's `Asymptotics.IsEquivalent`,
`Asymptotics.IsLittleO` and `Asymptotics.IsBigO` (pointers in
`DLMF.AsymptoticApproximations.Basics.MathlibCoverage`). This file proves the examples
2.1.4–2.1.9, states the integration rules 2.1.11–2.1.12 and Ritt's theorem (§2.1(ii)), and
develops the Poincaré expansions of §2.1(iii)–(iv) and the generalized expansions of §2.1(v):
the characterization 2.1.15, convergent series as asymptotic expansions, the algebra of
expansions (through the project's `Asymptotics.HasAsymptoticPowerSeries`), uniqueness, null
expansions 2.1.17, and the explicit form of uniformity 2.1.18.
-/

@[expose] public noncomputable section

open Filter Finset Asymptotics Bornology Complex
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

/-! ### §2.1(i): examples -/

/-- DLMF 2.1.4: `tanh x ∼ x` as `x → 0` in `ℂ`. Stated along the full neighbourhood filter
`𝓝 0` (at `x = 0` both sides vanish), which is stronger than along `𝓝[≠] 0`. -/
@[dlmf 2.1.E4]
theorem tanh_isEquivalent_id : (fun x : ℂ => Complex.tanh x) ~[𝓝 0] fun x => x := by
  have hd : HasDerivAt Complex.tanh 1 0 := by
    have h := (Complex.hasDerivAt_sinh 0).div (Complex.hasDerivAt_cosh 0) (by simp)
    simp only [Complex.cosh_zero, Complex.sinh_zero, mul_zero, sub_zero, one_pow, div_one,
      mul_one] at h
    have he : Complex.sinh / Complex.cosh = Complex.tanh :=
      funext fun x => (Complex.tanh_eq_sinh_div_cosh x).symm
    rwa [he] at h
  have h := hd.isLittleO
  simp only [Complex.tanh_zero, sub_zero, smul_eq_mul, mul_one] at h
  exact h

/-- DLMF 2.1.5: `e^{-x} = o(1)` as `x → +∞` in `ℝ`. -/
@[dlmf 2.1.E5]
theorem exp_neg_isLittleO_one :
    (fun x : ℝ => Real.exp (-x)) =o[atTop] fun _ => (1 : ℝ) :=
  (isLittleO_one_iff ℝ).mpr Real.tendsto_exp_neg_atTop_nhds_zero

/-- DLMF §2.1(i), after 2.1.7: 2.1.5 holds as `x → ∞` in the whole closed sector
`|ph x| ≤ ½π - δ`, written here as `δ' |x| ≤ ℜx` with `δ' = sin δ > 0` (the filter
`Asymptotics.sectorAtTop δ'`); this covers every fixed ray in `|ph x| < ½π`. -/
@[dlmf 2.1.i]
theorem cexp_neg_isLittleO_one_sector {δ : ℝ} (hδ : 0 < δ) :
    (fun z : ℂ => Complex.exp (-z)) =o[sectorAtTop δ] fun _ => (1 : ℂ) := by
  refine (isLittleO_one_iff ℂ).mpr ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun z : ℂ => Real.exp (-(δ * ‖z‖))) (sectorAtTop δ) (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_norm_sectorAtTop δ).const_mul_atTop hδ)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [show ∀ᶠ z in sectorAtTop δ, δ * ‖z‖ ≤ z.re from
    eventually_inf_principal.mpr (Eventually.of_forall fun z hz => hz)] with z hz
  rw [Complex.norm_exp, neg_re]
  exact Real.exp_le_exp.mpr (by linarith)

/-- DLMF §2.1(i), after 2.1.7: 2.1.5 does not hold as `x → ∞` in the open half-plane
`|ph x| < ½π`: along `x = 1 + it`, `|e^{-x}| = e^{-1}`. -/
@[dlmf 2.1.i]
theorem not_cexp_neg_isLittleO_one_halfPlane :
    ¬ (fun z : ℂ => Complex.exp (-z)) =o[comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | 0 < z.re}]
      fun _ => (1 : ℂ) := by
  intro h
  have ht := ((isLittleO_one_iff ℂ).mp h).norm
  set γ : ℝ → ℂ := fun t => 1 + t * I with hγ
  have hγt : Tendsto γ atTop (comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | 0 < z.re}) := by
    refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr
      (Eventually.of_forall fun t => by simp [hγ])⟩
    refine tendsto_atTop_mono (fun t => ?_) tendsto_id
    calc t ≤ |t| := le_abs_self t
      _ = |(γ t).im| := by simp [hγ]
      _ ≤ ‖γ t‖ := Complex.abs_im_le_norm _
  have h2 := ht.comp hγt
  have h3 : (fun t => ‖Complex.exp (-γ t)‖) = fun _ => Real.exp (-1) := by
    funext t; simp [hγ, Complex.norm_exp]
  simp only [Function.comp_def, h3, norm_zero] at h2
  exact (Real.exp_pos (-1)).ne' (tendsto_nhds_unique tendsto_const_nhds h2)

/-- DLMF 2.1.6: `sin(πx + x⁻¹) = O(x⁻¹)` as `x → ±∞` in `ℤ` (the bound holds for every
integer, with constant `1`). -/
@[dlmf 2.1.E6]
theorem sin_pi_mul_add_inv_isBigO :
    (fun n : ℤ => Real.sin (π * n + (n : ℝ)⁻¹)) =O[atTop ⊔ atBot] fun n => (n : ℝ)⁻¹ := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have h1 : |((-1 : ℝ) ^ n)| = 1 := by simp
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    show π * n + (n : ℝ)⁻¹ = (n : ℝ)⁻¹ + n * π by ring, Real.sin_add_int_mul_pi, abs_mul, h1,
    one_mul]
  exact Real.abs_sin_le_abs

/-- DLMF 2.1.7: `e^{ix} = O(1)` for `x ∈ ℝ`, on the whole real line (the filter `⊤`; see the
remark after 2.1.3). -/
@[dlmf 2.1.E7]
theorem cexp_mul_I_isBigO_one :
    (fun x : ℝ => Complex.exp (x * I)) =O[⊤] fun _ => (1 : ℝ) :=
  isBigO_top.mpr ⟨1, fun x => by simp [Complex.norm_exp_ofReal_mul_I]⟩

/-- DLMF 2.1.8: if `∑ aₛ zˢ` converges for all sufficiently small `|z|`, then for each
`n ≥ 0`, `∑_{s ≥ n} aₛ zˢ = O(zⁿ)` as `z → 0` in `ℂ`. -/
@[dlmf 2.1.E8]
theorem tsum_tail_isBigO_pow {a : ℕ → ℂ}
    (ha : ∃ r > 0, ∀ z : ℂ, ‖z‖ < r → Summable fun s => a s * z ^ s) (n : ℕ) :
    (fun z : ℂ => ∑' s, a (s + n) * z ^ (s + n)) =O[𝓝 0] fun z => z ^ n := by
  obtain ⟨r, hr, hs⟩ := ha
  set ρ : ℝ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hsρ : Summable fun s => a s * (ρ : ℂ) ^ s :=
    hs ρ (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]; linarith)
  clear_value ρ
  obtain ⟨C, hC⟩ : ∃ C, ∀ s, ‖a s‖ * ρ ^ s ≤ C := by
    have ht := hsρ.tendsto_atTop_zero.norm
    rw [← Nat.cofinite_eq_atTop] at ht
    obtain ⟨C, hC⟩ := ht.bddAbove_range_of_cofinite
    refine ⟨C, fun s => ?_⟩
    have := hC ⟨s, rfl⟩
    simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0] using this
  have hC0 : 0 ≤ C := (by positivity : 0 ≤ ‖a 0‖ * ρ ^ 0).trans (hC 0)
  refine IsBigO.of_bound (2 * C / ρ ^ n) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (half_pos hρ0)] with z hz
  rw [mem_ball_zero_iff] at hz
  have hq : ‖z‖ / ρ < 1 / 2 := by rw [div_lt_iff₀ hρ0]; linarith
  have hq0 : 0 ≤ ‖z‖ / ρ := by positivity
  have hgeom : HasSum (fun s : ℕ => C / ρ ^ n * ‖z‖ ^ n * (‖z‖ / ρ) ^ s)
      (C / ρ ^ n * ‖z‖ ^ n * (1 - ‖z‖ / ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left _
  have hb : ∀ s, ‖a (s + n) * z ^ (s + n)‖ ≤ C / ρ ^ n * ‖z‖ ^ n * (‖z‖ / ρ) ^ s := by
    intro s
    have h1 : ‖a (s + n)‖ ≤ C / ρ ^ (s + n) := by
      rw [le_div_iff₀ (by positivity)]; exact hC _
    rw [norm_mul, norm_pow]
    calc ‖a (s + n)‖ * ‖z‖ ^ (s + n) ≤ C / ρ ^ (s + n) * ‖z‖ ^ (s + n) := by gcongr
      _ = C / ρ ^ n * ‖z‖ ^ n * (‖z‖ / ρ) ^ s := by
        rw [div_pow, pow_add, pow_add]; ring
  refine (tsum_of_norm_bounded hgeom hb).trans ?_
  rw [norm_pow]
  have h2 : (1 - ‖z‖ / ρ)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc C / ρ ^ n * ‖z‖ ^ n * (1 - ‖z‖ / ρ)⁻¹ ≤ C / ρ ^ n * ‖z‖ ^ n * 2 := by gcongr
    _ = 2 * C / ρ ^ n * ‖z‖ ^ n := by ring

/-- DLMF 2.1.9: `e^z = 1 + z + O(z²)` as `z → 0` in `ℂ`. -/
@[dlmf 2.1.E9]
theorem cexp_sub_one_sub_isBigO_sq :
    (fun z : ℂ => Complex.exp z - 1 - z) =O[𝓝 0] fun z => z ^ 2 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with z hz
  rw [mem_closedBall_zero_iff] at hz
  simpa [norm_pow] using Complex.norm_exp_sub_one_sub_id_le hz

/-! ### §2.1(ii): integration and differentiation -/

/-- DLMF 2.1.11: if `f` is continuous on `[x₀, ∞)` and `f(x) ∼ x^ν` as `x → +∞`, with
`ℜν < -1`, then `∫ₓ^∞ f(t) dt ∼ -x^{ν+1}/(ν+1)`. The integrals converge absolutely (a
consequence of the hypotheses). -/
@[dlmf 2.1.E11]
theorem integral_Ioi_isEquivalent_of_isEquivalent_cpow {f : ℝ → ℂ} {ν : ℂ} {x₀ : ℝ}
    (hx₀ : 0 < x₀) (hf : ContinuousOn f (Set.Ici x₀)) (hν : ν.re < -1)
    (hfν : f ~[atTop] fun x => (x : ℂ) ^ ν) :
    (fun x => ∫ t in Set.Ioi x, f t) ~[atTop] fun x => -(x : ℂ) ^ (ν + 1) / (ν + 1) := by
  sorry

/-- DLMF 2.1.12, case `ℜν < -1`: under the hypotheses of 2.1.11 the integral `∫_{x₀}^x f`
tends to a constant (DLMF: `∫ f(x) dx ∼` a constant). -/
@[dlmf 2.1.E12]
theorem exists_tendsto_intervalIntegral_of_isEquivalent_cpow {f : ℝ → ℂ} {ν : ℂ} {x₀ : ℝ}
    (hx₀ : 0 < x₀) (hf : ContinuousOn f (Set.Ici x₀)) (hν : ν.re < -1)
    (hfν : f ~[atTop] fun x => (x : ℂ) ^ ν) :
    ∃ C : ℂ, Tendsto (fun x => ∫ t in x₀..x, f t) atTop (𝓝 C) := by
  sorry

/-- DLMF 2.1.12, case `ν = -1`: if `f` is continuous and `f(x) ∼ x⁻¹`, then
`∫_{x₀}^x f(t) dt ∼ ln x`. -/
@[dlmf 2.1.E12]
theorem intervalIntegral_isEquivalent_log {f : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hf : ContinuousOn f (Set.Ici x₀)) (hfν : f ~[atTop] fun x => (x : ℂ)⁻¹) :
    (fun x => ∫ t in x₀..x, f t) ~[atTop] fun x => (Real.log x : ℂ) := by
  sorry

/-- DLMF 2.1.12, case `ℜν > -1`: if `f` is continuous and `f(x) ∼ x^ν`, then
`∫_{x₀}^x f(t) dt ∼ x^{ν+1}/(ν+1)`. -/
@[dlmf 2.1.E12]
theorem intervalIntegral_isEquivalent_cpow {f : ℝ → ℂ} {ν : ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hf : ContinuousOn f (Set.Ici x₀)) (hν : -1 < ν.re)
    (hfν : f ~[atTop] fun x => (x : ℂ) ^ ν) :
    (fun x => ∫ t in x₀..x, f t) ~[atTop] fun x => (x : ℂ) ^ (ν + 1) / (ν + 1) := by
  sorry

/-- DLMF §2.1(ii), **Ritt's theorem**: if `f` is analytic in the sector
`𝐒 = {R < |z|, |ph(z e^{-iθ})| < ω}` and `f(z) = O(z^ν)` as `z → ∞` in `𝐒` (`ν` real, so
`|z^ν| = |z|^ν`), then `f'(z) = O(z^{ν-1})` as `z → ∞` in every closed sector
`|ph(z e^{-iθ})| ≤ ω'`, `ω' < ω`, properly interior to `𝐒` with the same vertex. -/
@[dlmf 2.1.ii]
theorem ritt_isBigO {f : ℂ → ℂ} {θ ω ω' R ν : ℝ} (hω : ω ≤ π) (hω' : 0 ≤ ω') (hωω' : ω' < ω)
    (hf : DifferentiableOn ℂ f (rittSector θ ω R))
    (hfν : f =O[comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 (rittSector θ ω R)] fun z => ‖z‖ ^ ν) :
    deriv f =O[comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 (rittClosedSector θ ω')]
      fun z => ‖z‖ ^ (ν - 1) := by
  sorry

/-- DLMF §2.1(ii): Ritt's theorem with both `O`'s replaced by `o`'s. -/
@[dlmf 2.1.ii]
theorem ritt_isLittleO {f : ℂ → ℂ} {θ ω ω' R ν : ℝ} (hω : ω ≤ π) (hω' : 0 ≤ ω')
    (hωω' : ω' < ω) (hf : DifferentiableOn ℂ f (rittSector θ ω R))
    (hfν : f =o[comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 (rittSector θ ω R)] fun z => ‖z‖ ^ ν) :
    deriv f =o[comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 (rittClosedSector θ ω')]
      fun z => ‖z‖ ^ (ν - 1) := by
  sorry

/-! ### §2.1(iii): Poincaré asymptotic expansions -/

section Poincare

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Nonvanishing under the stated hypotheses: `∀ᶠ x in cobounded 𝕜 ⊓ 𝓟 X, x ≠ 0`. -/
private lemma g2a_eventually_ne_zero (X : Set 𝕜) :
    ∀ᶠ x in cobounded 𝕜 ⊓ 𝓟 X, x ≠ 0 :=
  (eventually_ne_cobounded (0 : 𝕜)).filter_mono inf_le_left

/-- Identity under the stated parameter and domain assumptions: `PowerSeries.mk (fun n =>
PowerSeries.coeff n P) = P`. -/
private lemma g2a_mk_coeff (P : PowerSeries 𝕜) :
    PowerSeries.mk (fun n => PowerSeries.coeff n P) = P :=
  PowerSeries.ext fun n => by simp

/-- The map `(fun x : 𝕜 => x⁻¹)` tends to `(𝓝 0)` along `(cobounded 𝕜 ⊓ 𝓟 X)`. -/
private lemma g2a_tendsto_inv (X : Set 𝕜) :
    Tendsto (fun x : 𝕜 => x⁻¹) (cobounded 𝕜 ⊓ 𝓟 X) (𝓝 0) :=
  tendsto_inv₀_cobounded.mono_left inf_le_left

/-- DLMF 2.1.15: the Poincaré expansion 2.1.13 is equivalent to
`xⁿ (f(x) - ∑_{s<n} aₛ x⁻ˢ) → aₙ` as `x → ∞` in `𝐗`, for each `n = 0, 1, 2, …`. -/
@[dlmf 2.1.E15]
theorem hasPoincareExpansion_iff_tendsto {X : Set 𝕜} {a : ℕ → E} {f : 𝕜 → E} :
    HasPoincareExpansion X a f ↔
      ∀ n : ℕ, Tendsto (fun x => x ^ n • poincareRemainder a f n x) (cobounded 𝕜 ⊓ 𝓟 X)
        (𝓝 (a n)) := by
  set l := cobounded 𝕜 ⊓ 𝓟 X
  have hne := g2a_eventually_ne_zero X
  have hrec : ∀ n x, poincareRemainder a f n x =
      x⁻¹ ^ n • a n + poincareRemainder a f (n + 1) x := fun n x => by
    simp only [poincareRemainder, sum_range_succ]; abel
  constructor
  · intro h n
    have h1 : (fun x => x ^ n • poincareRemainder a f (n + 1) x) =O[l] fun x => x⁻¹ := by
      have := (isBigO_refl (fun x : 𝕜 => x ^ n) l).smul (h (n + 1))
      refine this.congr' EventuallyEq.rfl ?_
      filter_upwards [hne] with x hx
      rw [smul_eq_mul, inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx),
        one_mul]
    have h2 : Tendsto (fun x => x ^ n • poincareRemainder a f (n + 1) x) l (𝓝 0) :=
      h1.trans_tendsto (g2a_tendsto_inv X)
    have h3 := h2.const_add (a n)
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [hne] with x hx
    rw [hrec n x, smul_add, smul_smul, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hx), one_smul]
  · intro h n
    have h1 := (isBigO_refl (fun x : 𝕜 => x⁻¹ ^ n) l).smul ((h n).isBigO_one 𝕜)
    refine (h1.congr' ?_ ?_)
    · filter_upwards [hne] with x hx
      rw [smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hx), one_smul]; rfl
    · exact Eventually.of_forall fun x => by simp

/-- DLMF §2.1(iii), after 2.1.15: if `∑ aₛ x⁻ˢ` converges for all sufficiently large `|x|`,
then it is the asymptotic expansion of its sum as `x → ∞` in `ℂ`. -/
@[dlmf 2.1.iii]
theorem hasPoincareExpansion_of_hasSum {a : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ}
    (hf : ∀ x : ℂ, R < ‖x‖ → HasSum (fun s => a s * x⁻¹ ^ s) (f x)) :
    HasPoincareExpansion Set.univ a f := by
  intro n
  set R' := max R 0 + 1
  have hR' : 0 < R' := by positivity
  have hsum : ∃ r > 0, ∀ z : ℂ, ‖z‖ < r → Summable fun s => a s * z ^ s := by
    refine ⟨R'⁻¹, inv_pos.mpr hR', fun z hz => ?_⟩
    rcases eq_or_ne z 0 with rfl | hz0
    · exact summable_of_ne_finset_zero (s := {0}) fun s hs => by
        simp only [Finset.mem_singleton] at hs; simp [zero_pow hs]
    · have hlt : R < ‖z⁻¹‖ := by
        rw [norm_inv]
        have : R' < ‖z‖⁻¹ := by
          rw [lt_inv_comm₀ hR' (norm_pos_iff.mpr hz0)]; exact hz
        linarith [le_max_left R 0]
      simpa using (hf z⁻¹ hlt).summable
  have h8 := (tsum_tail_isBigO_pow hsum n).comp_tendsto (g2a_tendsto_inv (𝕜 := ℂ) Set.univ)
  refine (h8.congr' ?_ (Eventually.of_forall fun x => rfl))
  have hev : ∀ᶠ x in cobounded ℂ ⊓ 𝓟 Set.univ, R < ‖x‖ :=
    ((tendsto_norm_cobounded_atTop).eventually (eventually_gt_atTop R)).filter_mono inf_le_left
  filter_upwards [hev] with x hx
  have hs := (hf x hx)
  rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add n]
  simp [mul_comm]

/-- Poincaré expansions are asymptotic power series in the variable `x⁻¹`, so the algebra of
`Asymptotics.HasAsymptoticPowerSeries` applies (DLMF §2.1(iii)). -/
theorem hasPoincareExpansion_iff_hasAsymptoticPowerSeries {X : Set 𝕜} {a : ℕ → 𝕜}
    {f : 𝕜 → 𝕜} :
    HasPoincareExpansion X a f ↔
      HasAsymptoticPowerSeries (cobounded 𝕜 ⊓ 𝓟 X) (fun x => x⁻¹) (PowerSeries.mk a) f := by
  simp [HasPoincareExpansion, HasAsymptoticPowerSeries]

/-- DLMF §2.1(iii): Poincaré expansions can be added. -/
@[dlmf 2.1.iii]
theorem HasPoincareExpansion.add {X : Set 𝕜} {a b : ℕ → E} {f g : 𝕜 → E}
    (hf : HasPoincareExpansion X a f) (hg : HasPoincareExpansion X b g) :
    HasPoincareExpansion X (a + b) (f + g) :=
  HasAsymptoticExpansion.add hf hg

/-- DLMF §2.1(iii): Poincaré expansions can be subtracted. -/
@[dlmf 2.1.iii]
theorem HasPoincareExpansion.sub {X : Set 𝕜} {a b : ℕ → E} {f g : 𝕜 → E}
    (hf : HasPoincareExpansion X a f) (hg : HasPoincareExpansion X b g) :
    HasPoincareExpansion X (a - b) (f - g) :=
  HasAsymptoticExpansion.sub hf hg

/-- DLMF §2.1(iii): Poincaré expansions can be multiplied, the coefficients of the product
being those of the Cauchy product of the formal series. -/
@[dlmf 2.1.iii]
theorem HasPoincareExpansion.mul {X : Set 𝕜} {a b : ℕ → 𝕜} {f g : 𝕜 → 𝕜}
    (hf : HasPoincareExpansion X a f) (hg : HasPoincareExpansion X b g) :
    HasPoincareExpansion X (fun n => PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b))
      (fun x => f x * g x) := by
  rw [hasPoincareExpansion_iff_hasAsymptoticPowerSeries] at hf hg ⊢
  rw [g2a_mk_coeff]; exact hf.mul (g2a_tendsto_inv X) hg

/-- DLMF §2.1(iii): division (reciprocal) of a Poincaré expansion with `a₀ ≠ 0`; the
coefficients are those of the reciprocal formal series. -/
@[dlmf 2.1.iii]
theorem HasPoincareExpansion.inv {X : Set 𝕜} {a : ℕ → 𝕜} {f : 𝕜 → 𝕜}
    (hf : HasPoincareExpansion X a f) (ha : a 0 ≠ 0) :
    HasPoincareExpansion X (fun n => PowerSeries.coeff n (PowerSeries.mk a)⁻¹)
      (fun x => (f x)⁻¹) := by
  rw [hasPoincareExpansion_iff_hasAsymptoticPowerSeries] at hf ⊢
  rw [g2a_mk_coeff]; exact hf.recip (g2a_tendsto_inv X) (by simpa using ha)

/-- DLMF §2.1(iii): natural powers of a Poincaré expansion. -/
@[dlmf 2.1.iii]
theorem HasPoincareExpansion.pow {X : Set 𝕜} {a : ℕ → 𝕜} {f : 𝕜 → 𝕜}
    (hf : HasPoincareExpansion X a f) (m : ℕ) :
    HasPoincareExpansion X (fun n => PowerSeries.coeff n (PowerSeries.mk a ^ m))
      (fun x => f x ^ m) := by
  rw [hasPoincareExpansion_iff_hasAsymptoticPowerSeries] at hf ⊢
  rw [g2a_mk_coeff]; exact hf.pow (g2a_tendsto_inv X) m

/-- DLMF §2.1(iii): uniqueness of Poincaré expansions (2.1.14) as `x → ∞` in an unbounded
set `𝐗`. -/
@[dlmf 2.1.iii]
theorem HasPoincareExpansion.unique {X : Set 𝕜} {a b : ℕ → E} {f : 𝕜 → E}
    (hX : (cobounded 𝕜 ⊓ 𝓟 X).NeBot) (ha : HasPoincareExpansion X a f)
    (hb : HasPoincareExpansion X b f) : a = b := by
  refine HasAsymptoticExpansion.unique ?_ (fun n => ?_) ha hb
  · intro n
    have h := (isLittleO_one_iff 𝕜).mpr (g2a_tendsto_inv (𝕜 := 𝕜) X)
    have := h.mul_isBigO (isBigO_refl (fun x : 𝕜 => x⁻¹ ^ n) (cobounded 𝕜 ⊓ 𝓟 X))
    simpa [pow_succ, mul_comm] using this
  · exact ((g2a_eventually_ne_zero X).mono fun x hx => pow_ne_zero n (inv_ne_zero hx)).frequently

/-- DLMF 2.1.16 (uniqueness, §2.1(iii)): expansions at a finite point `c` are unique when `c`
is a limit point of `𝐗`. -/
@[dlmf 2.1.iii]
theorem HasPoincareExpansionAt.unique {X : Set 𝕜} {c : 𝕜} {a b : ℕ → E} {f : 𝕜 → E}
    (hX : (𝓝[X \ {c}] c).NeBot) (ha : HasPoincareExpansionAt X c a f)
    (hb : HasPoincareExpansionAt X c b f) : a = b := by
  have hle : 𝓝[X \ {c}] c ≤ 𝓝[X] c := nhdsWithin_mono _ Set.sdiff_subset
  have ha' := fun N => (ha N).mono hle
  have hb' := fun N => (hb N).mono hle
  refine HasAsymptoticExpansion.unique (l := 𝓝[X \ {c}] c) ?_ (fun n => ?_) ha' hb'
  · intro n
    have h0 : Tendsto (fun x : 𝕜 => x - c) (𝓝[X \ {c}] c) (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
    have h := ((isLittleO_one_iff 𝕜).mpr h0).mul_isBigO
      (isBigO_refl (fun x : 𝕜 => (x - c) ^ n) (𝓝[X \ {c}] c))
    simpa [pow_succ, mul_comm] using h
  · refine (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_ne_zero n (sub_ne_zero.mpr hx.2)

end Poincare

/-- DLMF 2.1.17: in the sector `|ph z| ≤ ½π - δ` (here `δ' |z| ≤ ℜz`, `δ' > 0`) the function
`0` has the null asymptotic expansion `0 + 0·z⁻¹ + 0·z⁻² + ⋯`. -/
@[dlmf 2.1.E17]
theorem hasPoincareExpansion_zero {δ : ℝ} :
    HasPoincareExpansion (𝕜 := ℂ) {z : ℂ | δ * ‖z‖ ≤ z.re} (fun _ => (0 : ℂ)) fun _ => 0 :=
  fun n => by simpa using isBigO_zero _ _

/-- DLMF 2.1.17: `e^{-z}` has the null asymptotic expansion as `z → ∞` in the sector
`δ |z| ≤ ℜz` (`|ph z| ≤ arccos δ < ½π`). -/
@[dlmf 2.1.E17, dlmf 2.1.iii]
theorem hasPoincareExpansion_cexp_neg {δ : ℝ} (hδ : 0 < δ) :
    HasPoincareExpansion (𝕜 := ℂ) {z : ℂ | δ * ‖z‖ ≤ z.re} (fun _ => (0 : ℂ))
      fun z => Complex.exp (-z) := by
  intro n
  simp only [smul_zero, sum_const_zero, sub_zero]
  set l := cobounded ℂ ⊓ 𝓟 {z : ℂ | δ * ‖z‖ ≤ z.re}
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) l atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have hlim : Tendsto (fun z : ℂ => (δ * ‖z‖) ^ n * Real.exp (-(δ * ‖z‖))) l (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (hnorm.const_mul_atTop hδ)
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ z in l, (δ * ‖z‖) ^ n * Real.exp (-(δ * ‖z‖)) ≤ C :=
    ⟨1, hlim.eventually (ge_mem_nhds one_pos)⟩
  refine IsBigO.of_bound (C / δ ^ n) ?_
  have hsec : ∀ᶠ z in l, δ * ‖z‖ ≤ z.re := eventually_inf_principal.mpr
    (Eventually.of_forall fun z hz => hz)
  have hne : ∀ᶠ z in l, z ≠ 0 := (eventually_ne_cobounded (0 : ℂ)).filter_mono inf_le_left
  filter_upwards [hC, hsec, hne] with z hz hzs hz0
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [Complex.norm_exp, neg_re, norm_pow, norm_inv]
  have h1 : Real.exp (-z.re) ≤ Real.exp (-(δ * ‖z‖)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(δ * ‖z‖)) ≤ C / δ ^ n * ‖z‖⁻¹ ^ n := by
    rw [mul_pow] at hz
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), inv_pow]
    calc Real.exp (-(δ * ‖z‖)) * δ ^ n
        = δ ^ n * ‖z‖ ^ n * Real.exp (-(δ * ‖z‖)) * (‖z‖ ^ n)⁻¹ := by
          field_simp
      _ ≤ C * (‖z‖ ^ n)⁻¹ := by gcongr
  linarith

/-- DLMF 2.1.17: `e^{-√z}` (principal value) has the null asymptotic expansion as `z → ∞` in
the sector `δ |z| ≤ ℜz`. -/
@[dlmf 2.1.E17, dlmf 2.1.iii]
theorem hasPoincareExpansion_cexp_neg_sqrt {δ : ℝ} (hδ : 0 < δ) :
    HasPoincareExpansion (𝕜 := ℂ) {z : ℂ | δ * ‖z‖ ≤ z.re} (fun _ => (0 : ℂ))
      fun z => Complex.exp (-z ^ (1 / 2 : ℂ)) := by
  sorry

/-- DLMF §2.1(iii): for any coefficients `aₛ` and any open sector `|ph z| < θ` (`0 < θ ≤ π`)
there is a function analytic in `{|z| > 1, |ph z| < θ}` with the Poincaré expansion `∑ aₛ z⁻ˢ`
there (Borel–Ritt); adding `c e^{-z}`-type null terms (2.1.17) gives infinitely many. -/
@[dlmf 2.1.iii]
theorem exists_hasPoincareExpansion_sector (a : ℕ → ℂ) {θ : ℝ} (hθ : 0 < θ) (hθπ : θ ≤ π) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f {z | 1 < ‖z‖ ∧ |arg z| < θ} ∧
      HasPoincareExpansion {z | 1 < ‖z‖ ∧ |arg z| < θ} a f := by
  sorry

/-! ### §2.1(iv): uniform expansions -/

/-- DLMF 2.1.18 and §2.1(iv): the uniform expansion `f(u, x) ~ ∑ aₛ(u) x⁻ˢ` means that for each
`n` the quantity `|xⁿ (f(u, x) - ∑_{s<n} aₛ(u) x⁻ˢ)|` is bounded as `x → ∞` in `𝐗`, uniformly
for `u ∈ 𝐔`: there are `C` and `R` with the bound `C` for all `u ∈ 𝐔` and `x ∈ 𝐗`, `|x| ≥ R`. -/
@[dlmf 2.1.E18, dlmf 2.1.iv]
theorem hasUniformPoincareExpansion_iff {ι 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {U : Set ι} {X : Set 𝕜} {a : ℕ → ι → E}
    {f : ι → 𝕜 → E} :
    HasUniformPoincareExpansion U X a f ↔ ∀ n : ℕ, ∃ C R : ℝ, ∀ u ∈ U, ∀ x ∈ X, R ≤ ‖x‖ →
      ‖x ^ n • (f u x - ∑ s ∈ range n, x⁻¹ ^ s • a s u)‖ ≤ C := by
  sorry

/-! ### §2.1(v): generalized asymptotic expansions -/

/-- DLMF §2.1(v): a generalized asymptotic expansion may converge without its sum being the
function represented: `0 ∼ e^{-x} + 0 + 0 + ⋯; {x⁻ˢ}` as `x → +∞`, while the series sums to
`e^{-x} ≠ 0`. -/
@[dlmf 2.1.v]
theorem hasGeneralizedAsymptoticExpansion_convergent_ne :
    HasGeneralizedAsymptoticExpansion atTop (fun n (x : ℝ) => x ^ (-(n : ℝ)))
      (fun s x => if s = 0 then Real.exp (-x) else 0) (fun _ => 0) ∧
      ∀ x : ℝ, HasSum (fun s => if s = 0 then Real.exp (-x) else 0) (Real.exp (-x)) ∧
        Real.exp (-x) ≠ 0 := by
  refine ⟨⟨by simpa using isAsymptoticScale_rpow_neg 0, fun n => ?_⟩, fun x =>
    ⟨hasSum_ite_eq 0 _, (Real.exp_pos _).ne'⟩⟩
  rcases n with _ | n
  · exact (isBigO_zero _ _).congr_left fun x => by simp
  · have h : (fun x : ℝ => (0 : ℝ) - ∑ s ∈ range (n + 1), if s = 0 then Real.exp (-x) else 0)
        = fun x => -Real.exp (-x) := by
      funext x; simp [sum_ite_eq']
    rw [h, isBigO_neg_left]
    exact (isLittleO_exp_neg_mul_rpow_atTop one_pos _).isBigO.congr_left fun x => by
      simp

end DLMF.AsymptoticApproximations
