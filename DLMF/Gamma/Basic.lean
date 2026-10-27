/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The Gamma and Beta functions, after AAR Chapter 1, §1.1

Andrews–Askey–Roy (AAR), *Special Functions*, Chapter 1, §1.1 takes Gauss's product
as the definition of `Γ`. Mathlib instead defines `Complex.Gamma` / `Real.Gamma` by Euler's
integral on `{s | 0 < re s}` and meromorphic continuation. The two definitions agree:
Euler's limit formula is `Complex.GammaSeq_tendsto_Gamma` (and the real analogue), which
lives in `Mathlib.Analysis.SpecialFunctions.Gamma.Beta` together with the reflection
formula `Complex.Gamma_mul_Gamma_one_sub`.

## Correspondence with AAR §1.1

* **Definition 1.1.1** (Gauss product). Mathlib: `Complex.GammaSeq` and
  `Complex.GammaSeq_tendsto_Gamma` in `Gamma.Beta`.
* **Theorem 1.1.2** (Weierstrass product). Proved below as
  `Complex.one_div_Gamma_eq_tprod`.
* **Definition 1.1.3** (Beta integral). Mathlib: `Complex.betaIntegral`.
* **Theorem 1.1.4** (`B(x,y) = Γ(x)Γ(y)/Γ(x+y)`). Mathlib:
  `Complex.betaIntegral_eq_Gamma_mul_div` and
  `Complex.Gamma_mul_Gamma_eq_betaIntegral`.
* **Corollary 1.1.5** (Euler's integral). Mathlib: `Complex.Gamma_eq_integral`,
  `Real.Gamma_eq_integral`.
* Recurrence `Γ(x+1) = x Γ(x)` and `Γ(n+1) = n!`: `Complex.Gamma_add_one`,
  `Complex.Gamma_nat_eq_factorial`.

The statements below use Mathlib's convention that `Γ` vanishes at non-positive integers
and that `0⁻¹ = 0` in a field, so `1 / Γ` is an entire function
(`Complex.differentiable_one_div_Gamma`) and the Weierstrass formula holds at the poles
as well.
-/

@[expose] public section

open Filter Finset

open scoped Topology Real

noncomputable section

namespace Complex

local notation "γ" => Real.eulerMascheroniConstant

/-- The general factor in the Weierstrass infinite product for `1 / Γ`. Indexed from `0`,
so the `n`-th term is `(1 + s/(n+1)) e^{-s/(n+1)}`. -/
def weierstrassGammaTerm (s : ℂ) (n : ℕ) : ℂ :=
  (1 + s / (n + 1)) * exp (-s / (n + 1))

theorem harmonic_coe_eq_sum (n : ℕ) :
    (harmonic n : ℂ) = ∑ i ∈ range n, (1 : ℂ) / (i + 1) := by
  unfold harmonic
  push_cast
  simp [one_div]

private lemma norm_one_add_mul_exp_neg_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(1 + z) * exp (-z) - 1‖ ≤ 3 * ‖z‖ ^ 2 := by
  have hz' : ‖-z‖ ≤ 1 := by simpa
  have h1 : ‖exp (-z) - 1 - (-z)‖ ≤ ‖z‖ ^ 2 := by
    simpa using norm_exp_sub_one_sub_id_le hz'
  have h2 : ‖exp (-z) - 1‖ ≤ 2 * ‖z‖ := by
    simpa using norm_exp_sub_one_le hz'
  have hEq : (1 + z) * exp (-z) - 1 =
      (exp (-z) - 1 - (-z)) + z * (exp (-z) - 1) := by ring
  calc
    ‖(1 + z) * exp (-z) - 1‖
      = ‖(exp (-z) - 1 - (-z)) + z * (exp (-z) - 1)‖ := by rw [hEq]
    _ ≤ ‖exp (-z) - 1 - (-z)‖ + ‖z * (exp (-z) - 1)‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ 2 + ‖z‖ * (2 * ‖z‖) := by
        grw [h1, norm_mul z, h2]
    _ = 3 * ‖z‖ ^ 2 := by ring

theorem summable_weierstrassGammaTerm_sub_one (s : ℂ) :
    Summable fun n : ℕ => weierstrassGammaTerm s n - 1 := by
  have hbase : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
  have hshift : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 :=
    (summable_nat_add_iff (G := ℝ) (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hbase
  have hsum : Summable fun n : ℕ => (3 * ‖s‖ ^ 2) * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    hshift.mul_left (3 * ‖s‖ ^ 2)
  refine Summable.of_norm_bounded_eventually_nat hsum ?_
  filter_upwards [eventually_ge_atTop ⌈‖s‖⌉₊] with n hn
  have hs : ‖s‖ ≤ n := Nat.ceil_le.mp hn
  have hn1 : ‖(n + 1 : ℂ)‖ = ((n + 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_add_one, norm_natCast]
  have hz : ‖s / (n + 1)‖ ≤ 1 := by
    rw [norm_div, hn1]
    refine div_le_one_of_le₀ (hs.trans ?_) (by positivity)
    exact_mod_cast n.le_succ
  have hnorm : ‖s / (n + 1)‖ ^ 2 = ‖s‖ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [norm_div, hn1, div_pow]
  calc
    ‖weierstrassGammaTerm s n - 1‖
      = ‖(1 + s / (n + 1)) * exp (-(s / (n + 1))) - 1‖ := by
        simp [weierstrassGammaTerm, neg_div]
    _ ≤ 3 * ‖s / (n + 1)‖ ^ 2 := norm_one_add_mul_exp_neg_sub_one_le hz
    _ = (3 * ‖s‖ ^ 2) * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
        rw [hnorm]; field

theorem multipliable_weierstrassGammaTerm (s : ℂ) :
    Multipliable (weierstrassGammaTerm s) := by
  have h := Complex.multipliable_one_add_of_summable (summable_weierstrassGammaTerm_sub_one s)
  convert h using 1
  ext n
  simp [weierstrassGammaTerm]

private lemma cpow_mul_recip_GammaSeq (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ) ^ s * (GammaSeq s n)⁻¹ =
      (∏ j ∈ range (n + 1), (s + j)) / n.factorial := by
  have hpow : (n : ℂ) ^ s ≠ 0 := by
    simp [cpow_eq_zero_iff, Nat.cast_ne_zero.mpr hn]
  rw [GammaSeq, inv_div]
  field [hpow]

private lemma prod_weierstrassGammaTerm (s : ℂ) (n : ℕ) :
    ∏ j ∈ range n, weierstrassGammaTerm s j =
      (∏ j ∈ range n, (s + (j + 1 : ℂ))) / n.factorial *
        exp (-s * (harmonic n : ℂ)) := by
  simp_rw [weierstrassGammaTerm, prod_mul_distrib]
  have hdiv :
      ∏ j ∈ range n, (1 + s / (j + 1)) =
        (∏ j ∈ range n, (s + (j + 1 : ℂ))) / n.factorial := by
    have hfac : (∏ j ∈ range n, (j + 1 : ℂ)) = n.factorial := by
      simp_rw [← Nat.cast_add_one]
      rw [← Nat.cast_prod, prod_range_add_one_eq_factorial]
    have hne : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h1 : ∀ j ∈ range n, 1 + s / (j + 1) = (s + (j + 1 : ℂ)) / (j + 1) := by
      intro j _
      rw [one_add_div (Nat.cast_add_one_ne_zero j), add_comm]
    rw [prod_congr rfl h1, eq_div_iff hne, ← hfac, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero j)
  have hexp :
      ∏ j ∈ range n, exp (-s / (j + 1)) = exp (-s * (harmonic n : ℂ)) := by
    rw [← exp_sum, harmonic_coe_eq_sum]
    congr 1
    simp_rw [neg_div]
    rw [sum_neg_distrib]
    simp [div_eq_mul_inv, mul_sum]
  rw [hdiv, hexp, mul_comm]

theorem weierstrassGamma_partial_eq (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    s * exp (γ * s) * ∏ j ∈ range n, weierstrassGammaTerm s j =
      exp (s * ((γ : ℂ) - ((harmonic n : ℝ) - Real.log n))) * (GammaSeq s n)⁻¹ := by
  have hnℂ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hshift : s * ∏ j ∈ range n, (s + (j + 1 : ℂ)) =
      ∏ j ∈ range (n + 1), (s + j) := by
    rw [prod_range_succ' (fun j => s + j)]
    simp [Nat.cast_add, Nat.cast_one, add_zero, mul_comm]
  have hpow : (n : ℂ) ^ s = exp (s * log n) := by
    rw [cpow_def_of_ne_zero hnℂ, mul_comm]
  have hlog : log (n : ℂ) = (Real.log n : ℂ) :=
    (ofReal_log (Nat.cast_nonneg n)).symm
  set P := ∏ j ∈ range n, (s + (j + 1 : ℂ))
  rw [prod_weierstrassGammaTerm]
  have hrearr :
      s * exp (γ * s) * (P / n.factorial * exp (-s * (harmonic n : ℂ))) =
        exp (γ * s) * exp (-s * (harmonic n : ℂ)) * (s * P / n.factorial) := by
    ring
  rw [hrearr, hshift, ← cpow_mul_recip_GammaSeq s hn, hpow]
  have hexp_combine :
      exp (γ * s) * exp (-s * (harmonic n : ℂ)) * exp (s * log n) =
        exp (s * ((γ : ℂ) - ((harmonic n : ℝ) - Real.log n))) := by
    rw [← exp_add, ← exp_add, hlog]
    congr 1
    push_cast
    ring
  rw [← mul_assoc, hexp_combine]

private lemma tendsto_recip_GammaSeq (s : ℂ) :
    Tendsto (fun n : ℕ => (GammaSeq s n)⁻¹) atTop (𝓝 (Gamma s)⁻¹) := by
  rcases eq_or_ne (Gamma s) 0 with hs0 | hs0
  · obtain ⟨m, rfl⟩ := (Gamma_eq_zero_iff s).mp hs0
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have hmem : m ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le hn)
    have hprod : ∏ j ∈ range (n + 1), ((-m : ℂ) + j) = 0 :=
      prod_eq_zero hmem (by simp)
    rw [GammaSeq, hprod, div_zero, inv_zero, Gamma_neg_nat_eq_zero, inv_zero]
  · exact (GammaSeq_tendsto_Gamma s).inv₀ hs0

/-- Sequential form of the Weierstrass product for `1 / Γ` (AAR Theorem 1.1.2). -/
theorem tendsto_weierstrassGamma_prod (s : ℂ) :
    Tendsto (fun n : ℕ => s * exp (γ * s) * ∏ j ∈ range n, weierstrassGammaTerm s j)
      atTop (𝓝 (Gamma s)⁻¹) := by
  have h0 : Tendsto (fun n : ℕ => γ - ((harmonic n : ℝ) - Real.log n)) atTop (𝓝 0) := by
    simpa using Filter.Tendsto.const_sub γ Real.tendsto_harmonic_sub_log
  have h0c : Tendsto (fun n : ℕ =>
      ((γ - ((harmonic n : ℝ) - Real.log n) : ℝ) : ℂ)) atTop (𝓝 0) :=
    (continuous_ofReal.tendsto 0).comp h0
  have harg : Tendsto (fun n : ℕ =>
      s * ((γ - ((harmonic n : ℝ) - Real.log n) : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul h0c
  have harg' : Tendsto (fun n : ℕ =>
      s * ((γ : ℂ) - ((harmonic n : ℝ) - Real.log n))) atTop (𝓝 0) := by
    convert harg using 1
    ext n
    push_cast
    ring
  have hexp : Tendsto (fun n : ℕ =>
      exp (s * ((γ : ℂ) - ((harmonic n : ℝ) - Real.log n)))) atTop (𝓝 1) := by
    simpa [exp_zero, Function.comp_def] using (continuous_exp.tendsto 0).comp harg'
  have hmul := hexp.mul (tendsto_recip_GammaSeq s)
  have : Tendsto (fun n : ℕ => s * exp (γ * s) * ∏ j ∈ range n, weierstrassGammaTerm s j)
      atTop (𝓝 (1 * (Gamma s)⁻¹)) := by
    refine hmul.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (weierstrassGamma_partial_eq s hn).symm
  simpa using this

/-- **Weierstrass's infinite product** for the reciprocal Gamma function (AAR Theorem 1.1.2).

\[
\frac{1}{\Gamma(s)} = s\, e^{\gamma s} \prod_{n=1}^\infty \Bigl(1+\frac{s}{n}\Bigr) e^{-s/n}.
\]
The identity holds for every complex `s`, including the poles of `Γ`, where both sides
are zero by Mathlib's convention `0⁻¹ = 0`. -/
@[dlmf 5.8.E2]
theorem one_div_Gamma_eq_tprod (s : ℂ) :
    (Gamma s)⁻¹ = s * exp (γ * s) * ∏' n : ℕ, weierstrassGammaTerm s n := by
  have hp := (multipliable_weierstrassGammaTerm s).hasProd.tendsto_prod_nat
  exact tendsto_nhds_unique (tendsto_weierstrassGamma_prod s) (tendsto_const_nhds.mul hp)

end Complex

namespace Real

local notation "γ" => eulerMascheroniConstant

/-- The general factor in the real Weierstrass product for `1 / Γ`. -/
def weierstrassGammaTerm (s : ℝ) (n : ℕ) : ℝ :=
  (1 + s / (n + 1)) * exp (-s / (n + 1))

theorem ofReal_weierstrassGammaTerm (s : ℝ) (n : ℕ) :
    (weierstrassGammaTerm s n : ℂ) = Complex.weierstrassGammaTerm s n := by
  simp [weierstrassGammaTerm, Complex.weierstrassGammaTerm, Complex.ofReal_exp]

theorem multipliable_weierstrassGammaTerm (s : ℝ) :
    Multipliable (weierstrassGammaTerm s) := by
  have hc : Summable fun n : ℕ => ((weierstrassGammaTerm s n - 1 : ℝ) : ℂ) := by
    convert Complex.summable_weierstrassGammaTerm_sub_one s using 1
    ext n
    simp [ofReal_weierstrassGammaTerm]
  have h : Summable fun n : ℕ => weierstrassGammaTerm s n - 1 :=
    Complex.summable_ofReal.mp hc
  have hmul := Real.multipliable_one_add_of_summable h
  convert hmul using 1
  ext n
  simp [weierstrassGammaTerm]

theorem tendsto_weierstrassGamma_prod (s : ℝ) :
    Tendsto (fun n : ℕ => s * exp (γ * s) * ∏ j ∈ range n, weierstrassGammaTerm s j)
      atTop (𝓝 (Gamma s)⁻¹) := by
  have hC : Tendsto (fun n : ℕ =>
      ((s * exp (γ * s) * ∏ j ∈ range n, weierstrassGammaTerm s j : ℝ) : ℂ))
      atTop (𝓝 (((Gamma s)⁻¹ : ℝ) : ℂ)) := by
    convert Complex.tendsto_weierstrassGamma_prod s using 1
    · ext n
      simp [ofReal_weierstrassGammaTerm, Complex.ofReal_exp, Complex.ofReal_prod,
        Complex.ofReal_mul]
    · rw [Complex.ofReal_inv, Complex.Gamma_ofReal]
  have hre := (Complex.continuous_re.tendsto _).comp hC
  have : Tendsto (fun n : ℕ =>
      s * exp (γ * s) * ∏ j ∈ range n, weierstrassGammaTerm s j)
      atTop (𝓝 ((↑((Gamma s)⁻¹ : ℝ) : ℂ).re)) :=
    hre.congr fun _ => Complex.ofReal_re _
  simpa [Complex.ofReal_re] using this

@[dlmf 5.8.E2]
theorem one_div_Gamma_eq_tprod (s : ℝ) :
    (Gamma s)⁻¹ = s * exp (γ * s) * ∏' n : ℕ, weierstrassGammaTerm s n := by
  have hp := (multipliable_weierstrassGammaTerm s).hasProd.tendsto_prod_nat
  exact tendsto_nhds_unique (tendsto_weierstrassGamma_prod s) (tendsto_const_nhds.mul hp)

end Real
