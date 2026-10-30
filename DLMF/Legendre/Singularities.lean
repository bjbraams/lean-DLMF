/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.RecipGammaDeriv
public import DLMF.Legendre.BoundaryAsymptotics
public import DLMF.Legendre.Hypergeometric
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Associated Legendre behavior at singularities

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- The regularized Gauss pullback `x ↦ 𝐅(a,b;c;(1-x)/2)` is continuous at `x = 1`. -/
theorem continuousAt_regularizedGaussHG_half_one (a b c : ℂ) :
    ContinuousAt (fun x : ℝ => regularizedGaussHG a b c ((1-(x:ℂ))/2)) 1 := by
  have hG := (analyticAt_regularizedGaussHG a b c zero_mem_cutPlane).continuousAt
  exact hG.comp_of_eq (by fun_prop) (by simp)

/-- The factor `((1+x)/2)^p K 𝐅(a,b;c;(1-x)/2)` tends to `1` at `x = 1` when `K 𝐅(a,b;c;0) = 1`. -/
theorem tendsto_legendre_singular_factor (a b c p K : ℂ) (hK : K * regularizedGaussHG a b c 0 = 1)
    (l : Filter ℝ) (hl : l ≤ 𝓝 1) :
    Tendsto (fun x : ℝ => ((1+(x:ℂ))/2)^p * (K * regularizedGaussHG a b c ((1-(x:ℂ))/2)))
      l (𝓝 1) := by
  have hc : ContinuousAt (fun x : ℝ => ((1+(x:ℂ))/2)^p *
      (K * regularizedGaussHG a b c ((1-(x:ℂ))/2))) 1 := by
    refine ContinuousAt.mul ?_ (continuousAt_const.mul (continuousAt_regularizedGaussHG_half_one _ _ _))
    exact ContinuousAt.cpow (by fun_prop) continuousAt_const (by norm_num)
  have h1 : ((1+((1:ℝ):ℂ))/2)^p * (K * regularizedGaussHG a b c ((1-((1:ℝ):ℂ))/2)) = 1 := by
    rw [show (1-((1:ℝ):ℂ))/2 = 0 by simp, hK]
    norm_num
  have h := hc.tendsto.mono_left hl
  rwa [h1] at h

/-- `(1-x²)^(m/2)/2^m = ((1-x)/2)^(m/2) ((1+x)/2)^(m/2)` on `(-1,1)`. -/
theorem one_sub_sq_cpow_half_div (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-(x:ℂ)^2)^((m:ℂ)/2)/2^m = ((1-(x:ℂ))/2)^((m:ℂ)/2) * ((1+(x:ℂ))/2)^((m:ℂ)/2) := by
  have h1 : (0:ℝ) ≤ (1-x)/2 := by linarith [hx.2]
  have h2 : (0:ℝ) ≤ (1+x)/2 := by linarith [hx.1]
  have h3 : (0:ℝ) ≤ 1-x^2 := by nlinarith [hx.1, hx.2]
  have hm : ((m:ℂ)/2) = (((m:ℝ)/2 : ℝ) : ℂ) := by push_cast; ring
  have h4 : (4:ℝ)^((m:ℝ)/2) = 2^m := by
    rw [show (4:ℝ) = 2^(2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      show (2:ℝ)*((m:ℝ)/2) = (m:ℝ) by ring, Real.rpow_natCast]
  have h5 : ((4:ℝ):ℂ)^((m:ℂ)/2) = 2^m := by
    rw [hm, ← ofReal_cpow (by norm_num), h4]; push_cast; rfl
  calc (1-(x:ℂ)^2)^((m:ℂ)/2)/2^m = ((1-x^2:ℝ):ℂ)^((m:ℂ)/2) / ((4:ℝ):ℂ)^((m:ℂ)/2) := by
        rw [h5]; push_cast; rfl
    _ = (((1-x^2:ℝ):ℂ) / ((4:ℝ):ℂ))^((m:ℂ)/2) := (div_cpow_ofReal_nonneg h3 (by norm_num) _).symm
    _ = ((((1-x)/2 * ((1+x)/2)):ℝ):ℂ)^((m:ℂ)/2) := by
        congr 1; push_cast; ring
    _ = _ := by rw [ofReal_mul, mul_cpow_ofReal_nonneg h1 h2]; push_cast; rfl

/-- For `x > 1`, `(x²-1)^(m/2)/2^m = ((x-1)/2)^(m/2) ((1+x)/2)^(m/2)` through the inherited branch. -/
theorem legendreBranchPower_div_two_pow (m : ℕ) {x : ℝ} (hx : 1 < x) :
    legendreBranchPower m x / 2^m = (((x:ℂ)-1)/2)^((m:ℂ)/2) * ((1+(x:ℂ))/2)^((m:ℂ)/2) := by
  have h1 : (0:ℝ) < x-1 := by linarith
  have h2 : (0:ℝ) < x+1 := by linarith
  have ha : ((x:ℂ)-1)/2 = (((x-1)/2:ℝ):ℂ) := by push_cast; ring
  have hb : (1+(x:ℂ))/2 = (((x+1)/2:ℝ):ℂ) := by push_cast; ring
  have l1 : log (((x:ℂ)-1)/2) = log ((x:ℂ)-1) - log 2 := by
    rw [ha, ← ofReal_log (by positivity), Real.log_div h1.ne' (by norm_num), ofReal_sub,
      ofReal_log h1.le, ofReal_log (by norm_num)]
    push_cast; rfl
  have l2 : log ((1+(x:ℂ))/2) = log ((x:ℂ)+1) - log 2 := by
    rw [hb, ← ofReal_log (by positivity), Real.log_div h2.ne' (by norm_num), ofReal_sub,
      ofReal_log h2.le, ofReal_log (by norm_num)]
    push_cast; rfl
  have h2m : (2:ℂ)^m = exp (m * log 2) := by rw [exp_nat_mul, exp_log (by norm_num)]
  rw [cpow_def_of_ne_zero (by rw [ha]; exact ofReal_ne_zero.mpr (by positivity)),
    cpow_def_of_ne_zero (by rw [hb]; exact ofReal_ne_zero.mpr (by positivity)), ← exp_add,
    legendreBranchPower, l1, l2, h2m, ← exp_sub]
  congr 1; ring

/-- DLMF 14.8.1: for `μ ∉ {1, 2, 3, …}`, `𝖯^μ_ν(x) ~ (2/(1−x))^{μ/2}/Γ(1−μ)` as `x → 1⁻` (asymptotic
equivalence). -/
@[dlmf 14.8.E1]
theorem legendre_singular_1 (ν μ : ℂ) (hμ : ∀ n : ℕ, μ ≠ n+1) :
    (fun x : ℝ => ferrersP ν μ x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => 1/Gamma (1-μ)*(2/(1-x):ℂ)^(μ/2)) := by
  have hΓ : Gamma (1-μ) ≠ 0 := Gamma_ne_zero fun n hn => hμ n (by linear_combination -hn)
  refine legBd_isEquivalent_of_eventuallyEq_mul ?_ (tendsto_legendre_singular_factor (ν+1) (-ν)
      (1-μ)
    (μ/2) (Gamma (1-μ)) (by rw [regularizedGaussHG_zero_of_regular fun n hn => hμ n
      (by linear_combination -hn)]; field_simp) _ nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have h1 : (0:ℝ) < 1+x := by linarith [hx.1]
  have h2 : (0:ℝ) < 1-x := by linarith [hx.2]
  have e : (((1+x)/(1-x):ℝ):ℂ) = ((2/(1-x):ℝ):ℂ) * (((1+x)/2:ℝ):ℂ) := by
    push_cast; field_simp
  simp only [ferrersP]
  rw [e, mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  push_cast
  field_simp

/-- DLMF 14.8.2: for `m ≥ 1` with `(ν−m+1)_{2m} ≠ 0`, `𝖯^m_ν(x) ~ (−1)^m (ν−m+1)_{2m}/m! ·
((1−x)/2)^{m/2}` as `x → 1⁻`. -/
@[dlmf 14.8.E2]
theorem legendre_singular_2 (ν : ℂ) (m : ℕ) (hm : 0 < m) (hν : poch (ν-m+1) (2*m) ≠ 0) :
    (fun x : ℝ => ferrersP ν m x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => (-1)^m*poch (ν-m+1) (2*m)/(m.factorial:ℂ)*((1-x)/2:ℂ)^((m:ℂ)/2)) := by
  have hf : (m.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hc : ∀ n : ℕ, (m:ℂ)+1 ≠ -n := fun n hn => by
    have := congrArg re hn; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  refine legBd_isEquivalent_of_eventuallyEq_mul ?_ (tendsto_legendre_singular_factor (ν+m+1) (m-ν)
      (m+1)
    ((m:ℂ)/2) (m.factorial) (by rw [regularizedGaussHG_zero_of_regular hc,
      show (m:ℂ)+1 = ((m:ℕ):ℂ)+1 by rfl, Gamma_nat_eq_factorial]; field_simp) _ nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  rw [ferrersP_integer_hypergeometric_4 ν m hx]
  have e := one_sub_sq_cpow_half_div m hx
  have e' : (1-(x:ℂ)^2)^((m:ℂ)/2) = 2^m*((((1-(x:ℂ))/2)^((m:ℂ)/2) * ((1+(x:ℂ))/2)^((m:ℂ)/2))) := by
    rw [← e]; field_simp
  rw [e']
  field_simp

/-- DLMF 14.8.4: for `Re μ > 0`, `μ ∉ {1/2, 3/2, …}` and `ν + μ ∉ {−1, −2, …}`, `𝖰^μ_ν(x) ~ ½
cos(μπ) Γ(μ) (2/(1−x))^{μ/2}` as `x → 1⁻`. -/
@[dlmf 14.8.E4]
theorem legendre_singular_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) (hμ : 0 < μ.re) (hh : ∀ n : ℕ, μ ≠ n+1/2) :
    (fun x : ℝ => ferrersQ ν μ x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => 1/2*cos (μ*π)*Gamma μ*(2/(1-x):ℂ)^(μ/2)) := by
  have hcos := legBd_cos_ne_zero hμ hh
  have hΓ : Gamma μ ≠ 0 := Gamma_ne_zero_of_re_pos hμ
  have hK : (2:ℂ)^(μ-1) * Gamma μ * cos (μ*π) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by simp) hΓ) hcos
  have := legBd_isEquivalent_of_tendsto (legBd_ferrersQ_tendsto h hμ) (legBd_tendsto_weight_left μ)
    hK (by simp)
  refine this.congr_right (Eventually.of_forall fun x => ?_)
  simp only
  rw [show (2:ℂ)^(μ-1) * Gamma μ * cos (μ*π) / 2^μ = (2:ℂ)^(μ-1) / 2^μ * Gamma μ * cos (μ*π) by ring,
    legBd_two_cpow_sub_one_div μ]
  ring

/-- DLMF 14.8.5: for `n ∈ ℕ` and `ν ± (n+1/2) ∉ {−1, −2, …}`, `𝖰^{n+1/2}_ν(x) ~ (−1)^{n+1} π
Γ(ν+n+3/2)/(2 Γ(n+3/2) Γ(ν−n+1/2)) · ((1−x)/2)^{n/2+1/4}` as `x → 1⁻`. -/
@[dlmf 14.8.E5]
theorem legendre_singular_5 (ν : ℂ) (n : ℕ) (hp : LegendreQRegular ν (n+1/2)) :
    (fun x : ℝ => ferrersQ ν (n+1/2) x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => (-1)^(n+1)*π*Gamma (ν+n+3/2)/(2*Gamma (n+3/2)*Gamma (ν-n+1/2))*((1-x)/2:ℂ)^((n+1/2:ℂ)/2)) := by
  set μ : ℂ := n+1/2 with hμdef
  have hμ : ∀ k : ℤ, μ ≠ k := fun k hk => by
    have h2 : (2*n+1 : ℂ) = 2*k := by rw [← show (2:ℂ)*μ = 2*n+1 by rw [hμdef]; ring, hk]
    have h3 : (2*n+1 : ℤ) = 2*k := by exact_mod_cast h2
    omega
  have hcn : cos ((n:ℂ)*π) = (-1)^n := by
    have := legendre_cos_sub_nat_mul_pi 0 n
    rwa [zero_sub, cos_neg, cos_zero, mul_one] at this
  have hs : sin (μ*π) = (-1)^n := by
    rw [hμdef, show ((n:ℂ)+1/2)*π = n*π + π/2 by ring, sin_add_pi_div_two, hcn]
  have hc : cos (μ*π) = 0 := by
    rw [hμdef, show ((n:ℂ)+1/2)*π = n*π + π/2 by ring, cos_add_pi_div_two, Complex.sin_nat_mul_pi,
      neg_zero]
  have h1 := legendre_singular_1 ν (-μ) (fun k hk => by
    have := congrArg re hk; simp [hμdef] at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
  set C : ℂ := -π/(2*(-1)^n)*(Gamma (ν+μ+1)/Gamma (ν-μ+1)) with hC
  have hQ : (fun x : ℝ => ferrersQ ν μ x) =ᶠ[𝓝[<] (1:ℝ)] fun x => C * ferrersP ν (-μ) x := by
    filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
    rw [ferrersQ_hypergeometric hp hμ hx, hs, hc, hC]
    ring
  have hE := ((IsEquivalent.refl (u := fun _ : ℝ => C) (l := 𝓝[<] (1:ℝ))).mul h1).congr_left
    (hQ.symm.trans (Eventually.of_forall fun x => rfl))
  refine hE.congr_right ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
  have hpos : (0:ℝ) < 2/(1-x) := div_pos (by norm_num) (by linarith)
  have hb : (2/(1-(x:ℂ))) = ((2/(1-x):ℝ):ℂ) := by push_cast; rfl
  have harg : (((2/(1-x):ℝ):ℂ)).arg ≠ π := by
    rw [arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne
  have hinv : ((1-(x:ℂ))/2) = (((2/(1-x):ℝ):ℂ))⁻¹ := by
    have : (1:ℂ)-x ≠ 0 := by exact_mod_cast (show (1:ℝ)-x ≠ 0 by linarith)
    push_cast; field_simp
  have hpow : (2/(1-(x:ℂ)))^((-μ)/2) = ((1-(x:ℂ))/2)^(μ/2) := by
    rw [hinv, inv_cpow _ _ harg, hb, neg_div, cpow_neg]
  show C * (1 / Gamma (1-(-μ)) * (2/(1-(x:ℂ)))^((-μ)/2)) = _
  rw [hpow, show (1:ℂ)-(-μ) = n+3/2 by rw [hμdef]; ring, hC, hμdef,
    show ν+((n:ℂ)+1/2)+1 = ν+n+3/2 by ring, show ν-((n:ℂ)+1/2)+1 = ν-n+1/2 by ring]
  have h1n : ((-1:ℂ)^n)⁻¹ = (-1)^n := by rw [← inv_pow, inv_neg, inv_one]
  rw [div_eq_mul_inv (-(π:ℂ)), mul_inv, h1n, pow_succ]
  ring

/-- DLMF 14.8.6: for `Re μ > 0` and `ν ± μ ∉ {−1, −2, …}`, `𝖰^{−μ}_ν(x) ~ Γ(μ) Γ(ν−μ+1)/(2 Γ(ν+μ+1))
· (2/(1−x))^{μ/2}` as `x → 1⁻`. -/
@[dlmf 14.8.E6]
theorem legendre_singular_6 (ν μ : ℂ) (hμ : 0 < μ.re) (hp : LegendreQRegular ν μ) (hm : LegendreQRegular ν (-μ)) :
    (fun x : ℝ => ferrersQ ν (-μ) x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => Gamma μ*Gamma (ν-μ+1)/(2*Gamma (ν+μ+1))*(2/(1-x):ℂ)^(μ/2)) := by
  have hΓ : Gamma μ ≠ 0 := Gamma_ne_zero_of_re_pos hμ
  have hG1 : Gamma (ν-μ+1) ≠ 0 := Gamma_ne_zero fun n hn => hm n (by linear_combination hn)
  have hG2 : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero fun n hn => hp n (by linear_combination hn)
  have hK : (2:ℂ)^(μ-1) * Gamma μ * Gamma (ν-μ+1) / Gamma (ν+μ+1) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by simp) hΓ) hG1) hG2
  have := legBd_isEquivalent_of_tendsto (legBd_ferrersQ_neg_tendsto hp hm hμ)
    (legBd_tendsto_weight_left μ) hK (by simp)
  refine this.congr_right (Eventually.of_forall fun x => ?_)
  simp only
  rw [show (2:ℂ)^(μ-1) * Gamma μ * Gamma (ν-μ+1) / Gamma (ν+μ+1) / 2^μ =
    (2:ℂ)^(μ-1) / 2^μ * (Gamma μ * Gamma (ν-μ+1) / Gamma (ν+μ+1)) by ring,
    legBd_two_cpow_sub_one_div μ]
  field_simp

/-- DLMF 14.8.7: for `μ ∉ {1, 2, 3, …}`, `P^μ_ν(x) ~ (2/(x−1))^{μ/2}/Γ(1−μ)` as `x → 1⁺`. -/
@[dlmf 14.8.E7]
theorem legendre_singular_7 (ν μ : ℂ) (hμ : ∀ n : ℕ, μ ≠ n+1) :
    (fun x : ℝ => associatedP ν μ x) ~[𝓝[>] (1:ℝ)] (fun x : ℝ => 1/Gamma (1-μ)*(2/(x-1):ℂ)^(μ/2)) := by
  have hΓ : Gamma (1-μ) ≠ 0 := Gamma_ne_zero fun n hn => hμ n (by linear_combination -hn)
  refine legBd_isEquivalent_of_eventuallyEq_mul ?_ (tendsto_legendre_singular_factor (ν+1) (-ν)
      (1-μ)
    (μ/2) (Gamma (1-μ)) (by rw [regularizedGaussHG_zero_of_regular fun n hn => hμ n
      (by linear_combination -hn)]; field_simp) _ nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  have h1 : (0:ℝ) < x+1 := by linarith
  have h2 : (0:ℝ) < x-1 := by linarith
  have e : ((2/(x-1):ℝ):ℂ) * (((1+x)/2:ℝ):ℂ) = (((x+1)/(x-1):ℝ):ℂ) := by
    push_cast; field_simp; ring
  have hlog : log ((x:ℂ)+1) - log ((x:ℂ)-1) = log (((x+1)/(x-1):ℝ):ℂ) := by
    rw [← ofReal_log (by positivity), Real.log_div h1.ne' h2.ne', ofReal_sub,
      ofReal_log h1.le, ofReal_log h2.le]
    push_cast; ring
  have hr : (((x+1)/(x-1):ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have key : exp (μ/2*(log ((x:ℂ)+1) - log ((x:ℂ)-1))) =
      (2/((x:ℂ)-1))^(μ/2) * ((1+(x:ℂ))/2)^(μ/2) := by
    have := mul_cpow_ofReal_nonneg (a := 2/(x-1)) (b := (1+x)/2) (by positivity) (by positivity) (μ/2)
    push_cast at this e
    rw [← this, e, hlog, cpow_def_of_ne_zero (by push_cast at hr ⊢; exact hr)]
    push_cast; ring_nf
  simp only [associatedP]
  rw [key]
  field_simp

/-- DLMF 14.8.8: for `m ≥ 1` and `ν ± m ∉ {−1, −2, …}`, `P^m_ν(x) ~ Γ(ν+m+1)/(m! Γ(ν−m+1)) ·
((x−1)/2)^{m/2}` as `x → 1⁺`. -/
@[dlmf 14.8.E8]
theorem legendre_singular_8 (ν : ℂ) (m : ℕ) (hn : LegendreQRegular ν (-m)) :
    (fun x : ℝ => associatedP ν m x) ~[𝓝[>] (1:ℝ)] (fun x : ℝ => Gamma (ν+m+1)/((m.factorial:ℂ)*Gamma (ν-m+1))*((x-1)/2:ℂ)^((m:ℂ)/2)) := by
  have hf : (m.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hc : ∀ n : ℕ, (m:ℂ)+1 ≠ -n := fun n hn => by
    have := congrArg re hn; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hreg : ∀ k : ℕ, ν-m+1 ≠ -k := fun k hk => hn k (by linear_combination hk)
  have hQ : poch (ν-m+1) (2*m) = Gamma (ν+m+1)/Gamma (ν-m+1) := by
    have h3 := Gamma_add_nat_div_Gamma_eq (n := 2*m) (ν-m+1) hreg
    rw [show ν-m+1+((2*m:ℕ):ℂ) = ν+m+1 by push_cast; ring] at h3
    rw [h3]
  have hG : Gamma (ν-m+1) ≠ 0 := Gamma_ne_zero hreg
  refine legBd_isEquivalent_of_eventuallyEq_mul ?_ (tendsto_legendre_singular_factor (ν+m+1) (m-ν)
      (m+1)
    ((m:ℂ)/2) (m.factorial) (by rw [regularizedGaussHG_zero_of_regular hc,
      show (m:ℂ)+1 = ((m:ℕ):ℂ)+1 by rfl, Gamma_nat_eq_factorial]; field_simp) _ nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  have hz : (x:ℂ)-1 ∈ slitPlane := Or.inl (by simp; linarith)
  have e := legendreBranchPower_div_two_pow m hx
  have e' : legendreBranchPower m x = 2^m*((((x:ℂ)-1)/2)^((m:ℂ)/2) * ((1+(x:ℂ))/2)^((m:ℂ)/2)) := by
    rw [← e]; field_simp
  rw [associatedP_integer_hypergeometric_8 ν m hz, e', hQ]
  field_simp

/-- DLMF 14.8.11: for `Re μ > 0` and `ν + μ ∉ {−1, −2, …}`, `𝑸^μ_ν(x) ~ Γ(μ)/(2 Γ(ν+μ+1)) ·
(2/(x−1))^{μ/2}` as `x → 1⁺`. -/
@[dlmf 14.8.E11]
theorem legendre_singular_11 (ν μ : ℂ) (hμ : 0 < μ.re) (hp : LegendreQRegular ν μ) :
    (fun x : ℝ => olverQ ν μ x) ~[𝓝[>] (1:ℝ)] (fun x : ℝ => Gamma μ/(2*Gamma (ν+μ+1))*(2/(x-1):ℂ)^(μ/2)) := by
  have hΓ : Gamma μ ≠ 0 := Gamma_ne_zero_of_re_pos hμ
  have hG2 : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero fun n hn => hp n (by linear_combination hn)
  have hK : (2:ℂ)^(μ-1) * Gamma μ * (Gamma (ν+μ+1))⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by simp) hΓ) (inv_ne_zero hG2)
  have := legBd_isEquivalent_of_tendsto (legBd_olverQ_tendsto ν hμ) (legBd_tendsto_weight_right μ)
    hK (by simp)
  refine this.congr_right (Eventually.of_forall fun x => ?_)
  simp only
  have e := legBd_two_cpow_sub_one_div μ
  rw [show (2:ℂ)^(μ-1) * Gamma μ * (Gamma (ν+μ+1))⁻¹ / 2^μ =
    (2:ℂ)^(μ-1) / 2^μ * (Gamma μ * (Gamma (ν+μ+1))⁻¹) by ring, e]
  field_simp

/-- DLMF 14.8.12: for `Re ν > −1/2` and `μ − ν ∉ {1, 2, 3, …}`, `P^μ_ν(x) ~ Γ(ν+1/2)/(π^{1/2}
Γ(ν−μ+1)) · (2x)^ν` as `x → ∞`. -/
@[dlmf 14.8.E12]
theorem legendre_singular_12 (ν μ : ℂ) (hν : -1/2 < ν.re) (hμ : ∀ n : ℕ, μ-ν ≠ n+1) :
    (fun x : ℝ => associatedP ν μ x) ~[atTop] (fun x : ℝ => Gamma (ν+1/2)/(Real.sqrt π*Gamma (ν-μ+1))*(2*x:ℂ)^ν) := by
  have hΓ : Gamma (ν+1/2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG : Gamma (ν-μ+1) ≠ 0 := Gamma_ne_zero fun n hn => hμ n (by linear_combination -hn)
  have hsq : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hK : (2:ℂ)^ν * Gamma (ν+1/2) * (Gamma (ν-μ+1))⁻¹ / (Real.sqrt π : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by simp) hΓ) (inv_ne_zero hG)) hsq
  have hM : Tendsto (fun x : ℝ => (x:ℂ)^(-ν) * (2*(x:ℂ))^ν) atTop (𝓝 (2^ν)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have e := mul_cpow_ofReal_nonneg (a := 2) (b := x) (by norm_num) hx.le ν
    push_cast at e
    rw [e, cpow_neg]
    have : (x:ℂ)^ν ≠ 0 := by simp [hx.ne']
    field_simp
  have := legBd_isEquivalent_of_tendsto (legBd_associatedP_tendsto_atTop hν μ) hM hK (by simp)
  refine this.congr_right (Eventually.of_forall fun x => ?_)
  simp only
  have : (2:ℂ)^ν ≠ 0 := by simp
  field_simp

/-- DLMF 14.8.13: for `Re ν < −1/2` and `ν + μ ∉ {0, 1, 2, …}`, `P^μ_ν(x) ~ Γ(−ν−1/2)/(π^{1/2}
Γ(−μ−ν) (2x)^{ν+1})` as `x → ∞`. -/
@[dlmf 14.8.E13]
theorem legendre_singular_13 (ν μ : ℂ) (hν : ν.re < -1/2) (hμ : ∀ n : ℕ, ν+μ ≠ n) :
    (fun x : ℝ => associatedP ν μ x) ~[atTop] (fun x : ℝ => Gamma (-ν-1/2)/(Real.sqrt π*Gamma (-μ-ν)*(2*x:ℂ)^(ν+1))) := by
  have h := legendre_singular_12 (-ν-1) μ (by simp; linarith) (fun n hn => hμ n (by linear_combination hn))
  refine (h.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop 1] with x hx
    exact associatedP_reflect_degree ν μ (Or.inl (by simp; linarith))
  · filter_upwards [eventually_gt_atTop 0] with x hx
    rw [show -ν-1+1/2 = -ν-1/2 by ring, show -ν-1-μ+1 = -μ-ν by ring,
      show (-ν-1 : ℂ) = -(ν+1) by ring, cpow_neg]
    ring

/-- DLMF 14.8.14: for `μ ∉ {1/2, 3/2, 5/2, …}`, `P^μ_{−1/2}(x) ~ (2/(πx))^{1/2} ln x/Γ(1/2−μ)` as `x
→ ∞`. -/
@[dlmf 14.8.E14]
theorem legendre_singular_14 (μ : ℂ) (hμ : ∀ n : ℕ, μ ≠ n+1/2) :
    (fun x : ℝ => associatedP (-1/2) μ x) ~[atTop] (fun x : ℝ => 1/Gamma (1/2-μ)*(2/(π*x):ℂ)^(1/2:ℂ)*Real.log x) := by
  have hG : Gamma (1/2-μ) ≠ 0 := Gamma_ne_zero fun n hn => hμ n (by linear_combination -hn)
  have hsq : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hK : (2:ℂ)^(1/2:ℂ) * (Gamma (1/2-μ))⁻¹ / (Real.sqrt π : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by simp) (inv_ne_zero hG)) hsq
  have hM : Tendsto (fun x : ℝ => (x:ℂ)^(1/2:ℂ) / (Real.log x : ℂ) *
      ((2/(π*x):ℂ)^(1/2:ℂ) * Real.log x)) atTop (𝓝 (((2/π:ℝ):ℂ)^(1/2:ℂ))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have h0 : (0:ℝ) < x := by linarith
    have hl : (Real.log x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.log_pos hx).ne'
    have e := mul_cpow_ofReal_nonneg (a := x) (b := 2/(π*x)) h0.le (by positivity) (1/2:ℂ)
    have e2 : (x:ℂ) * ((2/(π*x) : ℝ) : ℂ) = ((2/π:ℝ):ℂ) := by
      rw [← ofReal_mul]; congr 1; field_simp
    rw [e2] at e
    rw [e, show (2/(π*x):ℂ) = ((2/(π*x) : ℝ) : ℂ) by push_cast; rfl]
    field_simp
  have hM0 : ((2/π:ℝ):ℂ)^(1/2:ℂ) ≠ 0 := by
    rw [← legBd_sqrt_two_div_sqrt_pi]; exact div_ne_zero (by simp) hsq
  have := legBd_isEquivalent_of_tendsto (legBd_associatedP_half_tendsto_atTop μ) hM hK hM0
  refine this.congr_right (Eventually.of_forall fun x => ?_)
  simp only
  rw [← legBd_sqrt_two_div_sqrt_pi]
  have : (2:ℂ)^(1/2:ℂ) ≠ 0 := by simp
  field_simp

/-- `1/x² → 0` at infinity, as a complex function of real `x`. -/
theorem tendsto_one_div_sq_atTop : Tendsto (fun x : ℝ => 1/(x:ℂ)^2) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => ((1/x^2 : ℝ) : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
    (continuous_ofReal.tendsto 0).comp (by
      simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (two_ne_zero))))
  simpa using h

/-- DLMF 14.8.15: for `ν ∉ {−3/2, −5/2, …}`, `𝑸^μ_ν(x) ~ π^{1/2}/(Γ(ν+3/2) (2x)^{ν+1})` as `x →
∞`. -/
@[dlmf 14.8.E15]
theorem legendre_singular_15 (ν μ : ℂ) (hν : ∀ n : ℕ, ν ≠ -n-3/2) :
    (fun x : ℝ => olverQ ν μ x) ~[atTop] (fun x : ℝ => Real.sqrt π/(Gamma (ν+3/2)*(2*x:ℂ)^(ν+1))) := by
  have hc : ∀ k : ℕ, ν+3/2 ≠ -k := fun k hk => hν k (by linear_combination hk)
  have hΓ : Gamma (ν+3/2) ≠ 0 := Gamma_ne_zero hc
  set G := regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2)
  have hcont : ContinuousAt (fun w : ℂ => (1-w)^(μ/2) * (Gamma (ν+3/2) * G w)) 0 := by
    refine ContinuousAt.mul ?_ (continuousAt_const.mul
      (analyticAt_regularizedGaussHG _ _ _ zero_mem_cutPlane).continuousAt)
    exact ContinuousAt.cpow (by fun_prop) continuousAt_const (by norm_num)
  have h1 : (1-(0:ℂ))^(μ/2) * (Gamma (ν+3/2) * G 0) = 1 := by
    simp only [G, sub_zero, one_cpow, one_mul]; rw [regularizedGaussHG_zero_of_regular hc, mul_one_div_cancel hΓ]
  have hg := hcont.tendsto.comp tendsto_one_div_sq_atTop
  rw [h1] at hg
  refine legBd_isEquivalent_of_eventuallyEq_mul ?_ hg
  filter_upwards [eventually_gt_atTop 1] with x hx
  have h0 : (0:ℝ) < x := by linarith
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr h0.ne'
  have hp : (x:ℂ)^(ν+μ+1) = (x:ℂ)^μ * (x:ℂ)^(ν+1) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  have h2x : ((2:ℂ)*x)^(ν+1) = 2^(ν+1) * (x:ℂ)^(ν+1) := by
    have := mul_cpow_ofReal_nonneg (a := 2) (b := x) (by norm_num) h0.le (ν+1)
    push_cast at this; exact this
  have hxm : (x:ℂ)^μ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hxn : (x:ℂ)^(ν+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have h2n : (2:ℂ)^(ν+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  simp only [olverQ, Function.comp_apply]
  rw [legBd_branchPower_eq μ hx, hp, h2x]
  simp only [G]
  generalize regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(x:ℂ)^2) = R
  generalize (1-1/(x:ℂ)^2)^(μ/2) = P
  generalize Gamma (ν+3/2) = Γ0 at hΓ ⊢
  field_simp

/-- DLMF 14.8.16: for `n ≥ 1` and `μ − n + 1/2 ∉ {0, −1, −2, …}`, `𝑸^μ_{−n−1/2}(x) ~ π^{1/2}
Γ(μ+n+1/2)/(n! Γ(μ−n+1/2) (2x)^{n+1/2})` as `x → ∞`. -/
@[dlmf 14.8.E16]
theorem legendre_singular_16 (μ : ℂ) (n : ℕ) (hn : 0 < n) (hμ : ∀ k : ℕ, μ-n+1/2 ≠ -k) :
    (fun x : ℝ => olverQ (-n-1/2) μ x) ~[atTop] (fun x : ℝ => Real.sqrt π*Gamma (μ+n+1/2)/((n.factorial:ℂ)*Gamma (μ-n+1/2)*(2*x:ℂ)^(n+1/2:ℂ))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  have hf : ((k+1).factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (k+1).factorial_ne_zero
  have hc : ∀ j : ℕ, ((k+1:ℕ):ℂ)+1 ≠ -j := fun j hj => by
    have := congrArg re hj; simp at this; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
  have hΓ : Gamma (μ-((k+1:ℕ):ℂ)+1/2) ≠ 0 := Gamma_ne_zero hμ
  have hP : poch ((-((k+1:ℕ):ℂ)-1/2+μ+2)/2) (k+1) * poch ((-((k+1:ℕ):ℂ)-1/2+μ+1)/2) (k+1) =
      Gamma (μ+((k+1:ℕ):ℂ)+1/2) / Gamma (μ-((k+1:ℕ):ℂ)+1/2) / 4^(k+1) := by
    have h2 := DLMF.Legendre.poch_two_mul (μ-((k+1:ℕ):ℂ)+1/2) (k+1)
    have h3 := Gamma_add_nat_div_Gamma_eq (n := 2*(k+1)) (μ-((k+1:ℕ):ℂ)+1/2) hμ
    rw [show μ-((k+1:ℕ):ℂ)+1/2+((2*(k+1):ℕ):ℂ) = μ+((k+1:ℕ):ℂ)+1/2 by push_cast; ring] at h3
    rw [h3, ← poch, h2, show (μ-((k+1:ℕ):ℂ)+1/2)/2 = (-((k+1:ℕ):ℂ)-1/2+μ+1)/2 by ring,
      show (μ-((k+1:ℕ):ℂ)+1/2+1)/2 = (-((k+1:ℕ):ℂ)-1/2+μ+2)/2 by ring]
    field_simp
  set G := regularizedGaussHG ((-((k+1:ℕ):ℂ)-1/2+μ+2)/2+k+1) ((-((k+1:ℕ):ℂ)-1/2+μ+1)/2+k+1)
    (k+2)
  have hcont : ContinuousAt (fun w : ℂ => (1-w)^(μ/2) * (((k+1).factorial:ℂ) * G w)) 0 := by
    refine ContinuousAt.mul ?_ (continuousAt_const.mul
      (analyticAt_regularizedGaussHG _ _ _ zero_mem_cutPlane).continuousAt)
    exact ContinuousAt.cpow (by fun_prop) continuousAt_const (by norm_num)
  have h1 : (1-(0:ℂ))^(μ/2) * (((k+1).factorial:ℂ) * G 0) = 1 := by
    simp only [G, sub_zero, one_cpow, one_mul]
    rw [show (k:ℂ)+2 = ((k+1:ℕ):ℂ)+1 by push_cast; ring, regularizedGaussHG_zero_of_regular hc,
      Gamma_nat_eq_factorial, mul_one_div_cancel hf]
  have hg := hcont.tendsto.comp tendsto_one_div_sq_atTop
  rw [h1] at hg
  refine legBd_isEquivalent_of_eventuallyEq_mul ?_ hg
  filter_upwards [eventually_gt_atTop 1] with x hx
  have h0 : (0:ℝ) < x := by linarith
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr h0.ne'
  have hw : 1/(x:ℂ)^2 ∈ cutPlane := mem_cutPlane_of_norm_lt_one (by
    rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
    rw [div_lt_one (by positivity)]; nlinarith)
  set s : ℂ := 1/2 - ((k+1:ℕ):ℂ)
  have hp : (x:ℂ)^(-((k+1:ℕ):ℂ)-1/2+μ+1) = (x:ℂ)^μ * (x:ℂ)^s := by
    rw [← cpow_add _ _ hx0]; congr 1; simp only [s]; ring
  have hq : (x:ℂ)^(((k+1:ℕ):ℂ)+1/2) = (x:ℂ)^(2*(k+1)) * (x:ℂ)^s := by
    rw [← cpow_natCast, ← cpow_add _ _ hx0]; congr 1; simp only [s]; push_cast; ring
  have h2q : (2:ℂ)^(((k+1:ℕ):ℂ)+1/2) = 4^(k+1) * (2:ℂ)^s := by
    rw [show (4:ℂ)^(k+1) = (2:ℂ)^(2*(k+1)) by rw [pow_mul]; norm_num, ← cpow_natCast,
      ← cpow_add _ _ two_ne_zero]; congr 1; simp only [s]; push_cast; ring
  have h2x : ((2:ℂ)*x)^(((k+1:ℕ):ℂ)+1/2) = 2^(((k+1:ℕ):ℂ)+1/2) * (x:ℂ)^(((k+1:ℕ):ℂ)+1/2) := by
    have := mul_cpow_ofReal_nonneg (a := 2) (b := x) (by norm_num) h0.le (((k+1:ℕ):ℂ)+1/2)
    push_cast at this ⊢; exact this
  have hxm : (x:ℂ)^μ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hxs : (x:ℂ)^s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have h2s : (2:ℂ)^s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hc' : -((k+1:ℕ):ℂ)-1/2+3/2 = -(k:ℂ) := by push_cast; ring
  have hν1 : -((k+1:ℕ):ℂ)-1/2+1 = s := by simp only [s]; ring
  simp only [olverQ, Function.comp_apply]
  rw [hc', regularizedGaussHG_neg_nat _ _ _ hw, legBd_branchPower_eq μ hx, hp, hν1, h2x,
    h2q, hq, hP]
  simp only [G]
  generalize regularizedGaussHG ((-((k+1:ℕ):ℂ)-1/2+μ+2)/2+k+1) ((-((k+1:ℕ):ℂ)-1/2+μ+1)/2+k+1)
    (k+2) (1/(x:ℂ)^2) = R
  generalize (1-1/(x:ℂ)^2)^(μ/2) = P
  rw [div_pow, one_pow, ← pow_mul]
  field_simp

/-- DLMF 14.8.3: for `ν ∉ {−1, −2, …}`, `𝖰_ν(x) = ½ ln(2/(1−x)) − γ − ψ(ν+1) + O((1−x) ln(1−x))` as
`x → 1⁻`. -/
@[dlmf 14.8.E3]
theorem ferrersQ_log_singular {ν : ℂ} (hν : LegendreQRegular ν 0) :
    (fun x : ℝ => ferrersQ ν 0 x-1/2*log (2/(1-x):ℂ)+Real.eulerMascheroniConstant+digamma (ν+1)) =O[𝓝[<] (1:ℝ)] (fun x : ℝ => (1-x)*Real.log (1-x)) :=
  legBd_ferrersQ_log_isBigO hν

/-- DLMF 14.8.9 with `ψ(ν+1)/Γ(ν+1)` written as `-(1/Γ)'(ν+1)`. Stronger than DLMF: valid for
all `ν`, including `ν = -1, -2, …`. -/
@[dlmf 14.8.E9]
theorem olverQ_log_singular_recipGamma (ν : ℂ) :
    (fun x : ℝ => olverQ ν 0 x+log (x-1:ℂ)/(2*Gamma (ν+1))-(log 2/2-Real.eulerMascheroniConstant)/Gamma (ν+1)-DLMF.Gamma.recipGammaDeriv 1 (ν+1)) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (x-1)*Real.log (x-1)) :=
  legBd_olverQ_log_isBigO ν

/-- DLMF 14.8.9: for `ν ∉ {−1, −2, …}`, `𝑸_ν(x) = −ln(x−1)/(2Γ(ν+1)) + (½ ln 2 − γ − ψ(ν+1))/Γ(ν+1)
+ O((x−1) ln(x−1))` as `x → 1⁺`. -/
@[dlmf 14.8.E9]
theorem olverQ_log_singular {ν : ℂ} (hν : LegendreQRegular ν 0) :
    (fun x : ℝ => olverQ ν 0 x+log (x-1:ℂ)/(2*Gamma (ν+1))-(log 2/2-Real.eulerMascheroniConstant-digamma (ν+1))/Gamma (ν+1)) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (x-1)*Real.log (x-1)) := by
  have hp : ∀ m : ℕ, ν + 1 ≠ -(m : ℂ) := fun m h => hν m (by linear_combination h)
  refine (olverQ_log_singular_recipGamma ν).congr_left fun x => ?_
  rw [DLMF.Gamma.recipGammaDeriv_one_eq hp]
  ring

/-- DLMF 14.8.10: for `n ≥ 1`, `𝑸_{−n}(x) → (−1)^{n+1} (n−1)!` as `x → 1⁺`. -/
@[dlmf 14.8.E10]
theorem olverQ_negative_degree_singular (n : ℕ) (hn : 0 < n) :
    Tendsto (fun x : ℝ => olverQ (-n) 0 x) (𝓝[>] (1:ℝ)) (𝓝 ((-1)^(n+1)*((n-1).factorial:ℂ))) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hG : (Gamma ((-((m+1:ℕ):ℂ)) + 1))⁻¹ = 0 := by
    rw [show (-((m+1:ℕ):ℂ)) + 1 = -(m:ℂ) by push_cast; ring, inv_eq_zero]
    exact Complex.Gamma_neg_nat_eq_zero m
  have hD : DLMF.Gamma.recipGammaDeriv 1 ((-((m+1:ℕ):ℂ)) + 1) = (-1)^(m+1+1)*((m+1-1).factorial:ℂ) := by
    rw [show (-((m+1:ℕ):ℂ)) + 1 = -(m:ℂ) by push_cast; ring, DLMF.Gamma.recipGammaDeriv_one_neg_nat,
      Nat.add_sub_cancel, pow_succ, pow_succ]
    ring
  have hB := olverQ_log_singular_recipGamma (-((m+1:ℕ):ℂ))
  have hT : Tendsto (fun x : ℝ => (x-1)*Real.log (x-1)) (𝓝[>] (1:ℝ)) (𝓝 0) := by
    have hc := (Real.continuous_mul_log.tendsto 0).comp
      ((tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun _ => trivial⟩ :
        Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1:ℝ)) (𝓝[univ] 0)).mono_right nhdsWithin_le_nhds)
    · simpa [Function.comp_def] using hc
    · have h : Tendsto (fun x : ℝ => x - 1) (𝓝 1) (𝓝 (1-1)) := tendsto_id.sub tendsto_const_nhds
      simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
  have h0 := hB.trans_tendsto hT
  have e : ∀ x : ℝ, olverQ (-((m+1:ℕ):ℂ)) 0 x + log (x-1:ℂ)/(2*Gamma (-((m+1:ℕ):ℂ)+1)) -
      (log 2/2-Real.eulerMascheroniConstant)/Gamma (-((m+1:ℕ):ℂ)+1) -
      DLMF.Gamma.recipGammaDeriv 1 (-((m+1:ℕ):ℂ)+1) =
      olverQ (-((m+1:ℕ):ℂ)) 0 x - (-1)^(m+1+1)*((m+1-1).factorial:ℂ) := by
    intro x
    rw [hD, div_eq_mul_inv, div_eq_mul_inv, mul_inv, hG]
    ring
  simp only [e] at h0
  simpa using h0.add_const ((-1)^(m+1+1)*((m+1-1).factorial:ℂ))

end DLMF.Legendre
