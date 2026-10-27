/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Asymptotics
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import DLMF.Hypergeometric.Continuation
public import Mathlib.Analysis.Complex.SummableUniformlyOn

/-!
# Polygamma functions (DLMF §5.15)

The trigamma series 5.15.1 is `trigamma_eq_tsum` in `Digamma.lean` (real
positive argument). Complex polygamma is the iterated derivative of Mathlib's
`Complex.digamma`.

The complex digamma series 5.7.6 (`digamma_eq_cDigammaSeries`) is obtained from the
real one by the identity theorem on the complement of the poles, which is connected.
Termwise differentiation (Mathlib's `iteratedDerivWithin_tsum`) gives the polygamma
series 5.15.1 for all non-pole arguments (`polygamma_eq_tsum`). From this follow the
values at `1` and `1/2` and the multiplication formula.
-/

@[expose] public section

open Complex Filter
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Gamma

/-- Polygamma `ψ^{(n)}(z)`. -/
def polygamma (n : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv n Complex.digamma z

/-- The trigamma recurrence `ψ'(x+1) = ψ'(x) - 1/x²` for `x > 0`. -/
theorem trigamma_add_one {x : ℝ} (hx : 0 < x) :
    Real.trigamma (x + 1) = Real.trigamma x - x⁻¹ ^ 2 := by
  rw [Real.trigamma_eq_tsum hx, Real.trigamma_eq_tsum (by linarith),
    (Real.summable_trigamma hx).tsum_eq_zero_add]
  have h : ∀ n : ℕ, (x + ((n + 1 : ℕ) : ℝ))⁻¹ ^ 2 = (x + 1 + n)⁻¹ ^ 2 := by
    intro n; push_cast; ring_nf
  simp only [h, Nat.cast_zero, add_zero]
  ring

@[dlmf 5.15.E4]
theorem trigamma_nat_sub_half (n : ℕ) (hn : 1 ≤ n) :
    Real.trigamma (n - 1 / 2) =
      π ^ 2 / 2 - 4 * ∑ k ∈ Finset.range (n - 1), (1 / (2 * (k : ℝ) + 1) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  simp only [Nat.add_sub_cancel]
  induction m with
  | zero =>
    rw [show ((0 + 1 : ℕ) : ℝ) - 1 / 2 = 1 / 2 by norm_num, trigamma_one_div_two]
    simp
  | succ m ih =>
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) - 1 / 2 := by
      push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have h := trigamma_add_one hpos
    have h3 : (((m + 1 : ℕ) : ℝ) - 1 / 2)⁻¹ ^ 2 = 4 / (2 * (m : ℝ) + 1) ^ 2 := by
      push_cast
      rw [show (m : ℝ) + 1 - 1 / 2 = (2 * m + 1) / 2 by ring, inv_div, div_pow]
      norm_num
    rw [show ((m + 1 + 1 : ℕ) : ℝ) - 1 / 2 = ((m + 1 : ℕ) : ℝ) - 1 / 2 + 1 by push_cast; ring,
      h, ih, Finset.sum_range_succ, h3]
    ring

/-- The complement of the nonpositive integers is open in `ℂ`. -/
theorem isOpen_not_neg_nat : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} :=
  DLMF.Hypergeometric.isOpen_not_neg_nat

/-- `Γ` is analytic away from the nonpositive integers. -/
theorem analyticAt_Gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.Gamma s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_not_neg_nat.mem_nhds hs] with w hw
  exact Complex.differentiableAt_Gamma w hw

/-- `ψ` is analytic away from the nonpositive integers. -/
theorem analyticAt_digamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.digamma s := by
  have hG := analyticAt_Gamma hs
  exact hG.deriv.div hG (Complex.Gamma_ne_zero hs)

/-! ### Complex digamma and polygamma series -/

/-- The general term of the complex digamma series, `1/(n+1) - 1/(z+n)`. -/
def cDigammaTerm (n : ℕ) (z : ℂ) : ℂ := 1 / (n + 1) - 1 / (z + n)

/-- `z + n ≠ 0` when `z` is not a nonpositive integer. -/
theorem add_nat_ne_zero_of_not_neg_nat {z : ℂ} (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) (n : ℕ) :
    z + n ≠ 0 := fun h => hz n (eq_neg_of_add_eq_zero_left h)

/-- `‖z + n‖ ≥ n / 2` once `n ≥ 2 ‖z‖`. -/
theorem half_le_norm_add_nat {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) {n : ℕ} (hn : 2 * R ≤ n) :
    (n : ℝ) / 2 ≤ ‖z + n‖ := by
  have h := norm_sub_norm_le (n : ℂ) (-z)
  rw [sub_neg_eq_add, norm_neg, Complex.norm_natCast, add_comm] at h
  linarith

/-- A uniform `O(1/n²)` bound for the digamma series terms on `‖z‖ ≤ R`. -/
theorem norm_cDigammaTerm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) {n : ℕ} (hn : 2 * R ≤ n)
    (hn1 : 1 ≤ n) : ‖cDigammaTerm n z‖ ≤ 2 * (R + 1) * (1 / (n : ℝ) ^ 2) := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hzn := half_le_norm_add_nat hz hn
  have hzn0 : z + n ≠ 0 := by
    intro h; rw [h, norm_zero] at hzn; linarith
  have hn10 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have heq : cDigammaTerm n z = (z - 1) / ((n + 1) * (z + n)) := by
    unfold cDigammaTerm; field_simp; ring
  rw [heq, norm_div, norm_mul]
  have h1 : ‖z - 1‖ ≤ R + 1 := (norm_sub_le _ _).trans (by simp [hz])
  have h2 : ‖(n + 1 : ℂ)‖ = n + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
  rw [h2, div_le_iff₀ (by positivity)]
  calc ‖z - 1‖ ≤ R + 1 := h1
    _ ≤ 2 * (R + 1) * (1 / (n : ℝ) ^ 2) * ((n + 1) * ((n : ℝ) / 2)) := by
        rw [show 2 * (R + 1) * (1 / (n : ℝ) ^ 2) * ((n + 1) * ((n : ℝ) / 2)) =
          (R + 1) * ((n + 1) / n) by field_simp]
        have : (1 : ℝ) ≤ (n + 1) / n := by rw [le_div_iff₀ hnpos]; linarith
        nlinarith
    _ ≤ _ := by gcongr


/-- The complement of the nonpositive integers. -/
abbrev notNegNat : Set ℂ := {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)}

/-- Compact subsets of `ℂ` are bounded in norm. -/
theorem exists_norm_le_of_isCompact {K : Set ℂ} (hK : IsCompact K) : ∃ R : ℝ, ∀ z ∈ K, ‖z‖ ≤ R := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  exact ⟨R, hR⟩

/-- Cofinitely many `n` satisfy `2R ≤ n` and `1 ≤ n`. -/
theorem eventually_two_mul_le_nat (R : ℝ) : ∀ᶠ n : ℕ in cofinite, 2 * R ≤ n ∧ 1 ≤ n := by
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (⌈2 * R⌉₊ + 1)] with n hn
  refine ⟨(Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hn), by omega⟩

/-- The digamma series converges locally uniformly off the poles. -/
theorem summableLocallyUniformlyOn_cDigammaTerm :
    SummableLocallyUniformlyOn cDigammaTerm notNegNat := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    DLMF.Gamma.isOpen_not_neg_nat
  intro K _ hKc
  obtain ⟨R, hR⟩ := exists_norm_le_of_isCompact hKc
  refine ⟨fun n => 2 * (R + 1) * (1 / (n : ℝ) ^ 2),
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _, ?_⟩
  filter_upwards [eventually_two_mul_le_nat R] with n hn z hz
  exact norm_cDigammaTerm_le (hR z hz) hn.1 hn.2

/-- The digamma series converges off the poles. -/
theorem summable_cDigammaTerm {z : ℂ} (hz : z ∈ notNegNat) : Summable (cDigammaTerm · z) :=
  summableLocallyUniformlyOn_cDigammaTerm.summable hz

/-- Each digamma series term is differentiable off the poles. -/
theorem differentiableAt_cDigammaTerm (n : ℕ) {z : ℂ} (hz : z ∈ notNegNat) :
    DifferentiableAt ℂ (cDigammaTerm n) z := by
  unfold cDigammaTerm
  have := add_nat_ne_zero_of_not_neg_nat hz n
  fun_prop (disch := assumption)

/-- The digamma series as a function on `ℂ`. -/
def cDigammaSeries (z : ℂ) : ℂ := -Real.eulerMascheroniConstant + ∑' n, cDigammaTerm n z

/-- The digamma series is holomorphic off the poles. -/
theorem differentiableOn_cDigammaSeries : DifferentiableOn ℂ cDigammaSeries notNegNat :=
  (differentiableOn_const _).add (summableLocallyUniformlyOn_cDigammaTerm.differentiableOn
    DLMF.Gamma.isOpen_not_neg_nat fun n _ hr => differentiableAt_cDigammaTerm n hr)

/-- The complement of the nonpositive integers is preconnected. -/
theorem isPreconnected_notNegNat : IsPreconnected notNegNat := by
  have : notNegNat = (Set.range fun m : ℕ => -(m : ℂ))ᶜ := by
    ext s; simp [eq_comm]
  rw [this]
  exact ((Set.countable_range _).isPathConnected_compl_of_one_lt_rank
    (rank_real_complex ▸ Nat.one_lt_ofNat)).isConnected.isPreconnected

/-- Positive reals are not poles of `Γ`. -/
theorem ofReal_mem_notNegNat {x : ℝ} (hx : 0 < x) : (x : ℂ) ∈ notNegNat := fun m h => by
  have : x = -(m : ℝ) := by exact_mod_cast h
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- The complex digamma function extends the real one. -/
theorem digamma_ofReal {x : ℝ} (hx : 0 < x) : Complex.digamma x = Real.digamma x := by
  have hG : DifferentiableAt ℂ Complex.Gamma x :=
    Complex.differentiableAt_Gamma _ (ofReal_mem_notNegNat hx)
  have hGr : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma fun m => by
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h1 : HasDerivAt (fun y : ℝ => Complex.Gamma y) (deriv Complex.Gamma x) x :=
    hG.hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => (Real.Gamma y : ℂ)) ((deriv Real.Gamma x : ℝ) : ℂ) x :=
    hGr.hasDerivAt.ofReal_comp
  simp_rw [← Complex.Gamma_ofReal] at h2
  rw [Complex.digamma_def, logDeriv_apply, h1.unique h2, Complex.Gamma_ofReal, Real.digamma]
  push_cast; rfl

/-- The complex digamma series extends the real one. -/
theorem cDigammaSeries_ofReal {x : ℝ} (hx : 0 < x) : cDigammaSeries x = Real.digamma x := by
  rw [Real.digamma_eq_tsum hx, cDigammaSeries]
  push_cast
  congr 2
  funext n
  simp [cDigammaTerm, Real.digammaSeriesTerm]

/-- The digamma series, DLMF 5.7.6, for all complex arguments that are not poles. -/
theorem digamma_eq_cDigammaSeries {z : ℂ} (hz : z ∈ notNegNat) :
    Complex.digamma z = cDigammaSeries z := by
  have hU := DLMF.Gamma.isOpen_not_neg_nat
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (z₀ := 1)
    (fun w hw => analyticAt_digamma hw)
    (differentiableOn_cDigammaSeries.analyticOnNhd hU) isPreconnected_notNegNat
    (fun m h => ofReal_mem_notNegNat (x := 1) one_pos m (by simpa using h)) ?_ hz
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] 1, Complex.digamma x = cDigammaSeries x := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds one_pos)] with x hx
    rw [digamma_ofReal hx, cDigammaSeries_ofReal hx]
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by
      simpa using hx
  simpa using ht.frequently hev.frequently


/-- Higher derivatives of a digamma series term. -/
theorem iteratedDeriv_cDigammaTerm {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    iteratedDeriv k (cDigammaTerm n) =
      fun w => -((-1 : ℂ) ^ k * (k ! : ℂ) * (w + n) ^ (-1 - k : ℤ)) := by
  funext w
  have h := congrFun (iter_deriv_inv_linear (𝕜 := ℂ) k 1 n) w
  simp only [one_mul, one_pow, mul_one] at h
  have hfun : cDigammaTerm n = fun w : ℂ => 1 / ((n : ℂ) + 1) - (w + n)⁻¹ := by
    funext w; simp [cDigammaTerm]
  rw [hfun, iteratedDeriv_const_sub hk]
  simp only [Pi.neg_def, iteratedDeriv_fun_neg, iteratedDeriv_eq_iterate, h]


/-- Higher derivatives of a digamma series term within the pole complement. -/
theorem iteratedDerivWithin_cDigammaTerm {k : ℕ} (hk : 1 ≤ k) (n : ℕ) {w : ℂ}
    (hw : w ∈ notNegNat) :
    iteratedDerivWithin k (cDigammaTerm n) notNegNat w =
      -((-1 : ℂ) ^ k * (k ! : ℂ) * (w + n) ^ (-1 - k : ℤ)) := by
  rw [iteratedDerivWithin_of_isOpen DLMF.Gamma.isOpen_not_neg_nat hw,
    iteratedDeriv_cDigammaTerm hk]

/-- Differentiability of the derivatives of the digamma series terms. -/
theorem differentiableAt_iteratedDerivWithin_cDigammaTerm (k n : ℕ) {r : ℂ}
    (hr : r ∈ notNegNat) :
    DifferentiableAt ℂ (iteratedDerivWithin k (cDigammaTerm n) notNegNat) r := by
  have hU := DLMF.Gamma.isOpen_not_neg_nat
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using differentiableAt_cDigammaTerm n hr
  · have heq : iteratedDerivWithin k (cDigammaTerm n) notNegNat =ᶠ[𝓝 r]
        fun w => -((-1 : ℂ) ^ k * (k ! : ℂ) * (w + n) ^ (-1 - k : ℤ)) := by
      filter_upwards [hU.mem_nhds hr] with w hw
      exact iteratedDerivWithin_cDigammaTerm hk n hw
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    have := add_nat_ne_zero_of_not_neg_nat hr n
    fun_prop (disch := simp [this])

/-- The differentiated digamma series converge locally uniformly off the poles. -/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_cDigammaTerm {k : ℕ} (hk : 1 ≤ k) :
    SummableLocallyUniformlyOn
      (fun n => iteratedDerivWithin k (cDigammaTerm n) notNegNat) notNegNat := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    DLMF.Gamma.isOpen_not_neg_nat
  intro K hKU hKc
  obtain ⟨R, hR⟩ := exists_norm_le_of_isCompact hKc
  refine ⟨fun n => (k ! : ℝ) * 2 ^ (k + 1) * (1 / (n : ℝ) ^ (k + 1)),
    (Real.summable_one_div_nat_pow.mpr (by omega)).mul_left _, ?_⟩
  filter_upwards [eventually_two_mul_le_nat R] with n hn z hz
  rw [iteratedDerivWithin_cDigammaTerm hk n (hKU hz), norm_neg, norm_mul, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast, norm_zpow,
    mul_assoc]
  gcongr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.2
  have hzn := half_le_norm_add_nat (hR z hz) hn.1
  rw [show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    show (2 : ℝ) ^ (k + 1) * (1 / (n : ℝ) ^ (k + 1)) = (((n : ℝ) / 2) ^ (k + 1))⁻¹ by
      field_simp; rw [← mul_pow]; ring_nf]
  gcongr

/-- The polygamma series, DLMF 5.15.1, for positive order. -/
theorem polygamma_eq_tsum {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z ∈ notNegNat) :
    polygamma n z = (-1 : ℂ) ^ (n + 1) * n ! * ∑' k : ℕ, (z + k) ^ (-1 - n : ℤ) := by
  have hU := DLMF.Gamma.isOpen_not_neg_nat
  have heq : Complex.digamma =ᶠ[𝓝 z] cDigammaSeries := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact digamma_eq_cDigammaSeries hw
  unfold polygamma
  rw [heq.iteratedDeriv_eq, show cDigammaSeries = fun w =>
      -(Real.eulerMascheroniConstant : ℂ) + ∑' n, cDigammaTerm n w from rfl,
    iteratedDeriv_const_add hn,
    ← iteratedDerivWithin_of_isOpen hU hz,
    iteratedDerivWithin_tsum n hU hz (fun t ht => summable_cDigammaTerm ht)
      (fun k hk _ => summableLocallyUniformlyOn_iteratedDerivWithin_cDigammaTerm hk)
      (fun m k r _ hr => differentiableAt_iteratedDerivWithin_cDigammaTerm k m hr)]
  simp_rw [iteratedDerivWithin_cDigammaTerm hn _ hz]
  rw [tsum_neg, tsum_mul_left, pow_succ]
  ring


/-- `∑ (w + k)^{-1-n}` converges for `n ≥ 1` off the poles. -/
theorem summable_add_nat_zpow {n : ℕ} (hn : 0 < n) {w : ℂ} (hw : w ∈ notNegNat) :
    Summable fun k : ℕ => (w + k) ^ (-1 - n : ℤ) := by
  have h := (summableLocallyUniformlyOn_iteratedDerivWithin_cDigammaTerm hn).summable hw
  simp_rw [iteratedDerivWithin_cDigammaTerm hn _ hw] at h
  have hc : (-1 : ℂ) ^ n * (n ! : ℂ) ≠ 0 := by
    have := Nat.factorial_ne_zero n
    simp [this]
  refine (h.neg.mul_left ((-1 : ℂ) ^ n * (n ! : ℂ))⁻¹).congr fun k => ?_
  simp only [neg_neg, ← mul_assoc]
  rw [mul_assoc _ ((-1 : ℂ) ^ n), inv_mul_cancel₀ hc, one_mul]

/-- `a^{-1-n} = 1/a^{n+1}`. -/
theorem zpow_neg_one_sub_nat_eq (a : ℂ) (n : ℕ) :
    a ^ (-1 - n : ℤ) = 1 / a ^ (n + 1) := by
  rw [show (-1 - n : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    one_div]

/-- `∑ 1/k^p` converges in `ℂ` for `p > 1`. -/
theorem summable_one_div_nat_pow_complex {p : ℕ} (hp : 1 < p) :
    Summable fun k : ℕ => 1 / (k : ℂ) ^ p := by
  refine Summable.of_norm ?_
  simpa using Real.summable_one_div_nat_pow.mpr hp

/-- `ζ(p) = ∑ 1/(k+1)^p` for natural `p > 1`. -/
theorem riemannZeta_nat_eq_tsum_succ {p : ℕ} (hp : 1 < p) :
    riemannZeta p = ∑' k : ℕ, 1 / ((k : ℂ) + 1) ^ p := by
  rw [zeta_nat_eq_tsum_of_gt_one hp, (summable_one_div_nat_pow_complex hp).tsum_eq_zero_add]
  simp [Nat.cast_add_one, zero_pow (by omega : p ≠ 0)]

@[dlmf 5.15.E2]
theorem polygamma_one (n : ℕ) (hn : 0 < n) :
    polygamma n 1 = (-1 : ℂ) ^ (n + 1) * n.factorial * riemannZeta (n + 1) := by
  rw [polygamma_eq_tsum hn (fun m h => ofReal_mem_notNegNat (x := 1) one_pos m (by simpa using h)),
    show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
    riemannZeta_nat_eq_tsum_succ (by omega)]
  congr 2
  funext k
  rw [zpow_neg_one_sub_nat_eq, add_comm]

@[dlmf 5.15.E3]
theorem polygamma_one_div_two (n : ℕ) (hn : 0 < n) :
    polygamma n (1 / 2) =
      (-1 : ℂ) ^ (n + 1) * n.factorial * ((2 : ℂ) ^ (n + 1) - 1) * riemannZeta (n + 1) := by
  have hhalf : (1 / 2 : ℂ) ∈ notNegNat := fun m h => by
    simpa using ofReal_mem_notNegNat (x := 1 / 2) (by norm_num) m (by push_cast; exact h)
  have hp : 1 < n + 1 := by omega
  set f : ℕ → ℂ := fun k => 1 / (k : ℂ) ^ (n + 1) with hf
  have hsum := summable_one_div_nat_pow_complex hp
  have hres := Nat.sumByResidueClasses hsum 2
  rw [← zeta_nat_eq_tsum_of_gt_one hp] at hres
  rw [show (∑ j : ZMod 2, ∑' m : ℕ, f (j.val + 2 * m)) =
    ∑' m : ℕ, f ((0 : ZMod 2).val + 2 * m) + ∑' m : ℕ, f ((1 : ZMod 2).val + 2 * m) from
    Fin.sum_univ_two _] at hres
  -- the even terms
  have heven : ∑' m : ℕ, f ((0 : ZMod 2).val + 2 * m) =
      riemannZeta ((n + 1 : ℕ) : ℂ) / 2 ^ (n + 1) := by
    rw [zeta_nat_eq_tsum_of_gt_one hp, ← tsum_div_const]
    congr 1; funext m
    simp [hf, mul_pow]
    ring
  have hodd : ∑' m : ℕ, f ((1 : ZMod 2).val + 2 * m) =
      ∑' m : ℕ, 1 / (2 * (m : ℂ) + 1) ^ (n + 1) := by
    congr 1; funext m
    simp [hf, ZMod.val_one, add_comm]
  rw [heven, hodd] at hres
  rw [polygamma_eq_tsum hn hhalf]
  have hterm : ∀ k : ℕ, ((1 / 2 : ℂ) + k) ^ (-1 - n : ℤ) =
      2 ^ (n + 1) * (1 / (2 * (k : ℂ) + 1) ^ (n + 1)) := by
    intro k
    rw [zpow_neg_one_sub_nat_eq, show (1 / 2 : ℂ) + k = (2 * k + 1) / 2 by ring, div_pow]
    field_simp
  simp_rw [hterm]
  rw [tsum_mul_left, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring]
  have h2 : (2 : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  set Z := riemannZeta ((n + 1 : ℕ) : ℂ)
  set O := ∑' m : ℕ, 1 / (2 * (m : ℂ) + 1) ^ (n + 1)
  have : 2 ^ (n + 1) * O = (2 ^ (n + 1) - 1) * Z := by
    linear_combination (-(2 : ℂ) ^ (n + 1)) * hres - div_mul_cancel₀ Z h2
  rw [this]; ring


@[dlmf 5.15.E5]
theorem polygamma_add_one (n : ℕ) {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    polygamma n (z + 1) = polygamma n z + (-1 : ℂ) ^ n * n.factorial * z ^ (-(n + 1 : ℕ) : ℂ) := by
  have hz0 : z ≠ 0 := by simpa using hz 0
  have heq : (fun w => Complex.digamma (w + 1)) =ᶠ[𝓝 z] fun w => Complex.digamma w + w⁻¹ := by
    filter_upwards [isOpen_not_neg_nat.mem_nhds hz] with w hw
    exact Complex.digamma_apply_add_one w hw
  unfold polygamma
  have h1 : iteratedDeriv n Complex.digamma (z + 1) =
      iteratedDeriv n (fun w => Complex.digamma (w + 1)) z := by
    rw [iteratedDeriv_comp_add_const]
  rw [h1, heq.iteratedDeriv_eq n,
    iteratedDeriv_fun_add (analyticAt_digamma hz).contDiffAt (contDiffAt_inv ℂ hz0)]
  congr 1
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv,
    show (-(n + 1 : ℕ) : ℂ) = ((-1 - n : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]

/-- The complement of the integers is open in `ℂ`. -/
theorem isOpen_not_int : IsOpen {s : ℂ | ∀ k : ℤ, s ≠ (k : ℂ)} := by
  have hce : Topology.IsClosedEmbedding (fun k : ℤ => ((k : ℝ) : ℂ)) :=
    Complex.isometry_ofReal.isClosedEmbedding.comp Int.isClosedEmbedding_coe_real
  have hset : {s : ℂ | ∀ k : ℤ, s ≠ (k : ℂ)} = (Set.range fun k : ℤ => ((k : ℝ) : ℂ))ᶜ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists,
      Complex.ofReal_intCast]
    exact ⟨fun h k hk => h k hk.symm, fun h k hk => h k hk.symm⟩
  rw [hset]
  exact hce.isClosed_range.isOpen_compl

/-- `cot (π w)` is smooth away from the integers. -/
theorem contDiffAt_cot_pi_mul {n : ℕ} {z : ℂ} (hz : ∀ k : ℤ, z ≠ (k : ℂ)) :
    ContDiffAt ℂ n (fun w : ℂ => cot (π * w)) z := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsin : sin (π * z) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    exact hz k (mul_left_cancel₀ hπ (by rw [hk]; ring))
  have hc : ContDiffAt ℂ n (fun w : ℂ => cos (π * w)) z :=
    Complex.contDiff_cos.contDiffAt.comp z (contDiffAt_const.mul contDiffAt_id)
  have hs : ContDiffAt ℂ n (fun w : ℂ => sin (π * w)) z :=
    Complex.contDiff_sin.contDiffAt.comp z (contDiffAt_const.mul contDiffAt_id)
  refine (hc.div hs hsin).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  simp [Complex.cot_eq_cos_div_sin]

@[dlmf 5.15.E6]
theorem polygamma_reflection (n : ℕ) {z : ℂ} (hz : ∀ k : ℤ, z ≠ k) :
    polygamma n (1 - z) + (-1 : ℂ) ^ (n - 1 : ℤ) * polygamma n z =
      (-1 : ℂ) ^ n * π * iteratedDeriv n (fun w : ℂ => cot (π * w)) z := by
  have hnat : ∀ m : ℕ, z ≠ -(m : ℂ) := fun m h => hz (-m) (by rw [h]; push_cast; ring)
  have heq : (fun w => Complex.digamma (1 - w)) =ᶠ[𝓝 z]
      fun w => Complex.digamma w + π * cot (π * w) := by
    filter_upwards [isOpen_not_int.mem_nhds hz] with w hw
    exact Complex.digamma_one_sub hw
  have hcomp := congrFun (iteratedDeriv_comp_const_sub n Complex.digamma 1) z
  simp only [smul_eq_mul] at hcomp
  rw [heq.iteratedDeriv_eq n,
    iteratedDeriv_fun_add (analyticAt_digamma hnat).contDiffAt
      (contDiffAt_const.mul (contDiffAt_cot_pi_mul hz))] at hcomp
  have h2 : iteratedDeriv n (fun w => (π : ℂ) * cot (π * w)) z =
      π * iteratedDeriv n (fun w => cot (π * w)) z :=
    iteratedDeriv_const_mul_field (π : ℂ) (fun w => cot (π * w))
  rw [h2] at hcomp
  have hsq : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have hz1 : (-1 : ℂ) ^ (n - 1 : ℤ) = -(-1) ^ n := by
    rw [zpow_sub_one₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
    simp
  unfold polygamma
  linear_combination (-(-1 : ℂ) ^ n) * hcomp - (iteratedDeriv n Complex.digamma (1 - z)) * hsq +
    (iteratedDeriv n Complex.digamma z) * hz1

/-- Multiplication formula for positive-order polygamma functions. The order-zero
digamma formula has an additional logarithmic term. -/
@[dlmf 5.15.E7]
theorem polygamma_multiplication (n m : ℕ) (hn : 0 < n) (hm : 0 < m) {z : ℂ}
    (hz : ∀ k : ℕ, m * z ≠ -k) :
    polygamma n (m * z) =
      (m : ℂ) ^ (-(n + 1 : ℕ) : ℂ) *
        ∑ k ∈ Finset.range m, polygamma n (z + k / m) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmz : (m : ℂ) * z ∈ notNegNat := hz
  have hshift : ∀ k < m, z + k / m ∈ notNegNat := by
    intro k _ j hj
    apply hz (k + m * j)
    have : (m : ℂ) * (z + k / m) = m * (-(j : ℂ)) := by rw [hj]
    rw [mul_add, mul_div_cancel₀ _ hm0] at this
    push_cast
    linear_combination this
  have hterm : ∀ k j : ℕ, (z + k / m + j) ^ (-1 - n : ℤ) =
      (m : ℂ) ^ (n + 1) * ((m * z) + ((k + m * j : ℕ) : ℂ)) ^ (-1 - n : ℤ) := by
    intro k j
    rw [zpow_neg_one_sub_nat_eq, zpow_neg_one_sub_nat_eq,
      show z + k / m + j = ((m * z) + ((k + m * j : ℕ) : ℂ)) / m by push_cast; field_simp; ring,
      div_pow]
    field_simp
  have hsum := summable_add_nat_zpow hn hmz
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hres := Nat.sumByResidueClasses hsum (m' + 1)
  rw [Finset.sum_congr rfl fun k hk => polygamma_eq_tsum hn (hshift k (Finset.mem_range.mp hk)),
    polygamma_eq_tsum hn hmz, ← Finset.mul_sum, hres, Finset.sum_range]
  simp_rw [hterm, tsum_mul_left, ← Finset.mul_sum]
  rw [show (-((n + 1 : ℕ) : ℂ)) = -(((n + 1 : ℕ) : ℕ) : ℂ) from rfl, Complex.cpow_neg,
    Complex.cpow_natCast]
  have hpow : (((m' + 1 : ℕ) : ℂ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ hm0
  rw [show (∑ j : ZMod (m' + 1), ∑' i : ℕ,
      ((((m' + 1 : ℕ) : ℂ) * z) + ((j.val + (m' + 1) * i : ℕ) : ℂ)) ^ (-1 - n : ℤ)) =
    ∑ j : Fin (m' + 1), ∑' i : ℕ,
      ((((m' + 1 : ℕ) : ℂ) * z) + ((j.val + (m' + 1) * i : ℕ) : ℂ)) ^ (-1 - n : ℤ) from rfl]
  field_simp


section PolygammaAsymptotics

/-! ### Asymptotic expansions of `ψ⁽ⁿ⁾` (DLMF 5.15.8–9)

For `n ≥ 1`, `n! ∑ₖ (z+k)^{-(n+1)} = ∫₀^∞ tⁿ e^{-zt}/(1 - e^{-t}) dt`, and
`tⁿ/(1 - e^{-t}) = t^{n-1} + tⁿ/2 + t^{n+1} β(t)/t`. The Bernoulli expansion of `β(t)/t`
from `Asymptotics.lean` then gives the series with an explicit remainder. -/

open MeasureTheory Set

theorem summable_recip_add_pow {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz : 0 < z) :
    Summable fun k : ℕ => ((z + k) ^ (n + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => 1 / (k : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.mpr one_lt_two) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hzk : (k : ℝ) ≤ z + k := by linarith
  rw [Real.norm_of_nonneg (by positivity), one_div]
  apply inv_anti₀ (by positivity)
  calc (k : ℝ) ^ 2 ≤ (z + k) ^ 2 := by gcongr
    _ ≤ (z + k) ^ (n + 1) := pow_le_pow_right₀ (by linarith) (by omega)

theorem integrableOn_exp_mul_pow_mul_binetBeta {z : ℝ} (hz : 0 < z) (n : ℕ) :
    IntegrableOn (fun t => Real.exp (-z * t) * (t ^ n * binetBeta t)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_pow hz n).const_mul (1 / 2)) ?_ ?_
  · exact ((by fun_prop : Continuous fun t => Real.exp (-z * t) * t ^ n).continuousOn.mul
      continuousOn_binetBeta |>.congr fun t _ => by simp only [Pi.mul_apply]; ring)
      |>.aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_of_nonneg (by have := binetBeta_nonneg ht'; positivity)]
    have := binetBeta_le_half ht'
    have := binetBeta_nonneg ht'
    have he := Real.exp_pos (-z * t)
    have hp := pow_pos ht' n
    nlinarith [mul_pos he hp]

/-- `n! ∑ₖ (z+k)^{-(n+1)} = (n-1)!/zⁿ + n!/(2z^{n+1}) + ∫₀^∞ e^{-zt} t^{n+1} β(t)/t dt`. -/
theorem factorial_mul_tsum_recip_add_pow {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz : 0 < z) :
    (n.factorial : ℝ) * ∑' k : ℕ, ((z + k) ^ (n + 1))⁻¹ =
      (n - 1).factorial / z ^ n + n.factorial / (2 * z ^ (n + 1)) +
        ∫ t in Ioi (0 : ℝ), Real.exp (-z * t) * (t ^ (n + 1) * (binetBeta t / t)) := by
  set F : ℕ → ℝ → ℝ := fun k t => Real.exp (-(z + k) * t) * t ^ n with hF
  have hzk : ∀ k : ℕ, 0 < z + k := fun k => by positivity
  have hFint : ∀ k, Integrable (F k) (volume.restrict (Ioi (0 : ℝ))) := fun k =>
    integrableOn_exp_mul_pow (hzk k) n
  have hFval : ∀ k, ∫ t in Ioi (0 : ℝ), F k t = n.factorial * ((z + k) ^ (n + 1))⁻¹ := fun k => by
    rw [integral_exp_mul_pow (hzk k) n, div_eq_mul_inv]
  have hnorm : ∀ k, ∫ t in Ioi (0 : ℝ), ‖F k t‖ = ∫ t in Ioi (0 : ℝ), F k t := fun k =>
    setIntegral_congr_fun measurableSet_Ioi fun t ht => Real.norm_of_nonneg (by
      have : (0 : ℝ) < t := ht; positivity)
  have hsum : Summable fun k => ∫ t in Ioi (0 : ℝ), ‖F k t‖ := by
    simp_rw [hnorm, hFval]
    exact (summable_recip_add_pow hn hz).mul_left _
  have key := integral_tsum_of_summable_integral_norm hFint hsum
  simp_rw [hFval] at key
  rw [← tsum_mul_left, key]
  -- the pointwise sum
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ∑' k, F k t = Real.exp (-z * t) * t ^ (n - 1) +
      1 / 2 * (Real.exp (-z * t) * t ^ n) +
        Real.exp (-z * t) * (t ^ (n + 1) * (binetBeta t / t)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hgeom := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (-z * t) * t ^ n)
    have hFk : ∀ k : ℕ, F k t = Real.exp (-z * t) * t ^ n * Real.exp (-t) ^ k := by
      intro k
      simp only [hF]
      rw [← Real.exp_nat_mul, mul_right_comm, ← Real.exp_add]
      congr 2
      ring
    simp_rw [hFk]
    rw [hgeom.tsum_eq]
    have hK := binetKernel_eq_binetBeta ht'
    unfold binetKernel at hK
    have h1 : 1 - Real.exp (-t) ≠ 0 := by linarith
    have hinv : (1 - Real.exp (-t))⁻¹ = binetBeta t + 1 / 2 + 1 / t := by
      rw [← one_div]; linarith
    rw [hinv]
    have hpow : t ^ n = t * t ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have ht0 : t ≠ 0 := ht'.ne'
    rw [pow_succ, hpow]
    field_simp
    ring
  have hi1 := integrableOn_exp_mul_pow hz (n - 1)
  have hi2 := (integrableOn_exp_mul_pow hz n).const_mul (1 / 2)
  have hi3 : IntegrableOn (fun t => Real.exp (-z * t) * (t ^ (n + 1) * (binetBeta t / t)))
      (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_exp_mul_pow_mul_binetBeta hz n)
      (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := ht
    rw [pow_succ]
    field_simp
  have hi12 : Integrable (fun t => Real.exp (-z * t) * t ^ (n - 1) +
      1 / 2 * (Real.exp (-z * t) * t ^ n)) (volume.restrict (Ioi 0)) := hi1.add hi2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hi12 hi3,
    integral_add hi1 hi2, MeasureTheory.integral_const_mul, integral_exp_mul_pow hz,
    integral_exp_mul_pow hz, show n - 1 + 1 = n by omega]
  field_simp

/-- The remainder of the polygamma expansion. -/
theorem abs_factorial_mul_tsum_sub_le {n : ℕ} (hn : 1 ≤ n) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    |(n.factorial : ℝ) * ∑' k : ℕ, ((z + k) ^ (n + 1))⁻¹ -
      ((n - 1).factorial / z ^ n + n.factorial / (2 * z ^ (n + 1)) +
        ∑ k ∈ Finset.Icc 1 m, (bernoulli (2 * k) : ℝ) / (2 * k).factorial *
          ((2 * k + n - 1).factorial / z ^ (2 * k + n)))| ≤
      2 * binetRemConst m * ((2 * m + (n + 1)).factorial / z ^ (2 * m + (n + 1) + 1)) := by
  rw [factorial_mul_tsum_recip_add_pow hn hz]
  have hP := integral_exp_mul_pow_mul_binetPoly hz m (n + 1)
  have hsum : ∑ k ∈ Finset.Icc 1 m, (bernoulli (2 * k) : ℝ) / (2 * k).factorial *
      ((2 * k + n - 1).factorial / z ^ (2 * k + n)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ (n + 1) * binetPoly m s) := by
    rw [hP]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [show 2 * k - 2 + (n + 1) = 2 * k + n - 1 by omega,
      show 2 * k + n - 1 + 1 = 2 * k + n by omega]
  have hI : (∫ t in Ioi (0 : ℝ), Real.exp (-z * t) * (t ^ (n + 1) * (binetBeta t / t))) -
      ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ (n + 1) * binetPoly m s) =
      ∫ s in Ioi (0 : ℝ),
        Real.exp (-z * s) * (s ^ (n + 1) * (binetBeta s / s - binetPoly m s)) := by
    have hi3 : IntegrableOn (fun t => Real.exp (-z * t) * (t ^ (n + 1) * (binetBeta t / t)))
        (Ioi 0) := by
      refine IntegrableOn.congr_fun (integrableOn_exp_mul_pow_mul_binetBeta hz n)
        (fun t ht => ?_) measurableSet_Ioi
      have ht' : (0 : ℝ) < t := ht
      rw [pow_succ]
      field_simp
    rw [← integral_sub hi3 (integrableOn_exp_mul_pow_mul_binetPoly hz m (n + 1))]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  rw [hsum, show ∀ A B C D : ℝ, A + B + C - (A + B + D) = C - D from fun A B C D => by ring, hI]
  exact abs_integral_exp_mul_pow_mul_rem_le hz m (n + 1)

theorem isBigO_recip_add_pow {x : ℝ} (hx : 0 < x) (N : ℕ) (C : ℝ) :
    Asymptotics.IsBigO atTop (fun t : ℝ => C / (t + x) ^ N) (fun t : ℝ => t ^ (-(N : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound |C| ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (t + x) ^ N),
    abs_of_pos (Real.rpow_pos_of_pos ht _), Real.rpow_neg ht.le, Real.rpow_natCast,
    ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (abs_nonneg C) (by positivity)
    (pow_le_pow_left₀ ht.le (by linarith) N)

@[dlmf 5.15.E8]
theorem trigamma_asymptotic (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.trigamma (t + x) -
        (1 / (t + x) + 1 / (2 * (t + x) ^ 2) +
          ∑ k ∈ Finset.Icc 1 n, bernoulli (2 * k) / (t + x) ^ (2 * k + 1)))
      (fun t : ℝ => (t : ℝ) ^ (-(2 * n : ℝ) - 3)) := by
  have h := (isBigO_recip_add_pow (by linarith : (0 : ℝ) < x) (2 * n + 3)
    (2 * binetRemConst n * (2 * n + 2).factorial))
  refine Asymptotics.IsBigO.trans ?_ (h.congr_right fun t => by push_cast; ring_nf)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hz : 0 < t + x := by linarith
  have hb := abs_factorial_mul_tsum_sub_le (n := 1) le_rfl n hz
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, Nat.sub_self, Nat.factorial_zero,
    pow_one] at hb
  have hsum : ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / (2 * k).factorial *
      ((2 * k + 1 - 1).factorial / (t + x) ^ (2 * k + 1)) =
      ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / (t + x) ^ (2 * k + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_sub_cancel]
    have : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hsum] at hb
  simp only [show (1 : ℕ) + 1 = 2 from rfl, show 2 * n + 2 + 1 = 2 * n + 3 by ring] at hb
  have htri : Real.trigamma (t + x) = ∑' k : ℕ, ((t + x + k) ^ 2)⁻¹ := by
    rw [Real.trigamma_eq_tsum hz]; simp_rw [inv_pow]
  have hS : 0 ≤ binetRemConst n := tsum_nonneg fun m => by positivity
  rw [htri, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * binetRemConst n *
      (2 * n + 2).factorial / (t + x) ^ (2 * n + 3)), mul_div_assoc]
  exact hb

@[dlmf 5.15.E9]
theorem polygamma_asymptotic (n m : ℕ) (hn : 0 < n) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => polygamma n (t + x) -
        (-1 : ℂ) ^ (n - 1) *
          ((n - 1).factorial / (t + x : ℂ) ^ n +
            n.factorial / (2 * (t + x : ℂ) ^ (n + 1)) +
            ∑ k ∈ Finset.Icc 1 m,
              ((2 * k + n - 1).factorial / (2 * k).factorial) *
                bernoulli (2 * k) / (t + x : ℂ) ^ (2 * k + n)))
      (fun t : ℝ => (t : ℂ) ^ (-(2 * m + n + 2 : ℕ) : ℂ)) := by
  refine Asymptotics.IsBigO.of_bound (2 * binetRemConst m * (2 * m + (n + 1)).factorial) ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hz : 0 < t + x := by linarith
  have hmem : (t : ℂ) + x ∈ notNegNat := by
    intro k hk
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hser : ∑' k : ℕ, ((t : ℂ) + x + k) ^ (-1 - n : ℤ) =
      ((∑' k : ℕ, ((t + x + k) ^ (n + 1))⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    funext k
    rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    push_cast
    ring
  have hsign : (-1 : ℂ) ^ (n + 1) = (-1) ^ (n - 1) := by
    rw [show n + 1 = n - 1 + 2 by omega, pow_add]; norm_num
  have hsumC : ∑ k ∈ Finset.Icc 1 m, ((2 * k + n - 1).factorial / (2 * k).factorial : ℂ) *
      bernoulli (2 * k) / ((t : ℂ) + x) ^ (2 * k + n) =
      ∑ k ∈ Finset.Icc 1 m, ((bernoulli (2 * k) : ℂ) / ((2 * k).factorial : ℂ) *
        (((2 * k + n - 1).factorial : ℂ) / ((t : ℂ) + x) ^ (2 * k + n))) :=
    Finset.sum_congr rfl fun k _ => by ring
  have hb := abs_factorial_mul_tsum_sub_le hn m hz
  set D : ℝ := (n.factorial : ℝ) * ∑' k : ℕ, ((t + x + k) ^ (n + 1))⁻¹ -
      ((n - 1).factorial / (t + x) ^ n + n.factorial / (2 * (t + x) ^ (n + 1)) +
        ∑ k ∈ Finset.Icc 1 m, (bernoulli (2 * k) : ℝ) / (2 * k).factorial *
          ((2 * k + n - 1).factorial / (t + x) ^ (2 * k + n))) with hD
  have hexpr : polygamma n ((t : ℂ) + x) - (-1 : ℂ) ^ (n - 1) *
      ((n - 1).factorial / ((t : ℂ) + x) ^ n + n.factorial / (2 * ((t : ℂ) + x) ^ (n + 1)) +
        ∑ k ∈ Finset.Icc 1 m, ((2 * k + n - 1).factorial / (2 * k).factorial : ℂ) *
          bernoulli (2 * k) / ((t : ℂ) + x) ^ (2 * k + n)) = (-1 : ℂ) ^ (n - 1) * (D : ℂ) := by
    rw [polygamma_eq_tsum hn hmem, hser, hsign, hsumC, hD]
    push_cast
    ring
  rw [hexpr, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos ht]
  refine hb.trans ?_
  have hS : 0 ≤ binetRemConst m := tsum_nonneg fun j => by positivity
  have hre : (-((2 * m + n + 2 : ℕ) : ℂ)).re = -((2 * m + (n + 1) + 1 : ℕ) : ℝ) := by
    simp only [neg_re, natCast_re]; push_cast; ring
  rw [hre, Real.rpow_neg ht.le, Real.rpow_natCast, ← div_eq_mul_inv, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ ht.le (by linarith) _)) (by positivity)

end PolygammaAsymptotics

end DLMF.Gamma
