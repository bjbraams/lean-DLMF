/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The digamma series (AAR Theorem 1.2.5)

Andrews–Askey–Roy, Theorem 1.2.5:

* `Γ'(1) = -γ` is `Real.hasDerivAt_Gamma_one` / `Complex.digamma_one`;
* `ψ(x) = -γ + ∑_{k=0}^∞ (1/(k+1) - 1/(x+k))` for `x > 0`, proved below;
* log-convexity of `Γ` on `(0,∞)` is `Real.convexOn_log_Gamma`.

The series is obtained from Gauss's product `GammaSeq` by differentiating `log ∘ GammaSeq`
and passing to the limit, using convexity on `(0,∞)`.
-/

@[expose] public section

open Filter Finset Set

open scoped Topology Real

noncomputable section

namespace Real

local notation "γ" => eulerMascheroniConstant

/-- The real digamma function `ψ(x) = Γ'(x)/Γ(x)`. -/
def digamma (x : ℝ) : ℝ :=
  deriv Gamma x / Gamma x

theorem digamma_eq_deriv_log {x : ℝ} (hx : 0 < x) :
    digamma x = deriv (log ∘ Gamma) x := by
  have hG : DifferentiableAt ℝ Gamma x :=
    differentiableAt_Gamma fun m => ((neg_nonpos.mpr m.cast_nonneg).trans_lt hx).ne'
  rw [digamma, Function.comp_def, deriv.log hG (Gamma_pos_of_pos hx).ne']

open ComplexConjugate in
/-- The real digamma function is the real part of Mathlib's complex digamma function. -/
theorem digamma_eq_re_digamma {x : ℝ} (hx : 0 < x) :
    digamma x = (Complex.digamma x).re := by
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have : x = -(m : ℝ) := by exact_mod_cast h
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hd : HasDerivAt Gamma (deriv Complex.Gamma x).re x :=
    (Complex.differentiableAt_Gamma _ hx').hasDerivAt.real_of_complex
  have hconj : conj (deriv Complex.Gamma x) = deriv Complex.Gamma x := by
    have h := congrFun (deriv_conj_conj (f := Complex.Gamma)) (x : ℂ)
    have hfun : (conj ∘ Complex.Gamma ∘ conj) = Complex.Gamma := by
      funext z
      simp [Function.comp_def, Complex.Gamma_conj]
    rw [hfun] at h
    simp only [Function.comp_def, Complex.conj_ofReal] at h
    exact h.symm
  have hre : deriv Complex.Gamma x = ((deriv Complex.Gamma x).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp hconj).symm
  rw [digamma, hd.deriv, Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal]
  conv_rhs => rw [hre]
  rw [Complex.div_ofReal_re, Complex.ofReal_re]

@[dlmf 5.4.E12]
theorem digamma_one : digamma 1 = -γ := by
  simp [digamma, hasDerivAt_Gamma_one.deriv]

/-- The general term of the digamma series. -/
def digammaSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ)⁻¹ - (x + n)⁻¹

theorem log_GammaSeq {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    log (GammaSeq x n) =
      x * log n + log n.factorial - ∑ k ∈ range (n + 1), log (x + k) := by
  unfold GammaSeq
  have hprod : 0 < ∏ j ∈ range (n + 1), (x + j) :=
    prod_pos fun j _ => add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg _)
  rw [log_div (by positivity) hprod.ne', log_mul (by positivity) (by positivity),
    log_rpow (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
  congr 1
  exact log_prod fun k _ => (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k)).ne'

theorem hasDerivAt_log_GammaSeq {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt (fun y : ℝ => log (GammaSeq y n))
      (log n - ∑ k ∈ range (n + 1), (x + k)⁻¹) x := by
  have hsum :
      HasDerivAt (fun y : ℝ => ∑ k ∈ range (n + 1), log (y + k))
        (∑ k ∈ range (n + 1), (x + k)⁻¹) x :=
    HasDerivAt.fun_sum fun k _ => by
      have hd : HasDerivAt (fun y : ℝ => y + k) 1 x := (hasDerivAt_id x).add_const _
      simpa [Function.comp_def, mul_one] using
        (hasDerivAt_log (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k)).ne').comp x hd
  have hlin : HasDerivAt (fun y : ℝ => y * log n + log n.factorial) (log n) x := by
    simpa using ((hasDerivAt_id x).mul_const (log n)).add_const (log n.factorial)
  refine (hlin.sub hsum).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy using log_GammaSeq hy hn

theorem convexOn_log_GammaSeq {n : ℕ} (hn : n ≠ 0) :
    ConvexOn ℝ (Ioi 0) (fun y : ℝ => log (GammaSeq y n)) := by
  have hlin : ConvexOn ℝ (Ioi 0) (fun y : ℝ => y * log n) := by
    simpa [mul_comm] using (convexOn_id (convex_Ioi (0 : ℝ))).smul (log_natCast_nonneg n)
  have hconst : ConvexOn ℝ (Ioi 0) (fun _ : ℝ => log (n.factorial : ℝ)) :=
    convexOn_const _ (convex_Ioi 0)
  have hterm (k : ℕ) : ConvexOn ℝ (Ioi 0) (fun y : ℝ => -log (y + k)) := by
    have hconc : ConcaveOn ℝ (Ioi 0) (fun y : ℝ => log (y + k)) := by
      have h0 := strictConcaveOn_log_Ioi.concaveOn.comp_affineMap
        (AffineMap.const ℝ ℝ (k : ℝ) + AffineMap.id ℝ ℝ)
      simpa [Function.comp_def, add_comm] using h0.subset (fun y (hy : y ∈ Ioi (0 : ℝ)) => by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have : (0 : ℝ) < k + y := add_pos_of_nonneg_of_pos hk hy
        exact this) (convex_Ioi 0)
    exact hconc.neg
  have hsum : ConvexOn ℝ (Ioi 0)
      (fun y : ℝ => ∑ k ∈ range (n + 1), -log (y + k)) := by
    suffices ∀ s : Finset ℕ, ConvexOn ℝ (Ioi 0) (fun y => ∑ k ∈ s, -log (y + k)) from this _
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa using convexOn_const (0 : ℝ) (convex_Ioi 0)
    | insert k s hk ih =>
      simp_rw [sum_insert hk]
      exact (hterm k).add ih
  refine (((hlin.add hconst).add hsum).congr fun y hy => ?_)
  simp [log_GammaSeq hy hn, sub_eq_add_neg, sum_neg_distrib, Pi.add_apply]

theorem tendsto_log_GammaSeq {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => log (GammaSeq x n)) atTop (𝓝 (log (Gamma x))) := by
  have hpos : 0 < Gamma x := Gamma_pos_of_pos hx
  exact (GammaSeq_tendsto_Gamma x).log hpos.ne'

theorem tendsto_log_sub_harmonic_succ :
    Tendsto (fun n : ℕ => log n - (harmonic (n + 1) : ℝ)) atTop (𝓝 (-γ)) := by
  have hγ : Tendsto (fun n : ℕ => (harmonic (n + 1) : ℝ) - log (n + 1)) atTop (𝓝 γ) := by
    simpa [Function.comp_def] using
      tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ => log n - log (n + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) :=
      tendsto_natCast_div_add_atTop _
    have : Tendsto (fun n : ℕ => log ((n : ℝ) / (n + 1))) atTop (𝓝 (log 1)) :=
      h1.log one_ne_zero
    convert this using 1
    · ext n
      by_cases hn : n = 0
      · subst n; simp
      · rw [log_div (Nat.cast_ne_zero.mpr hn) (by positivity)]
    · simp
  convert hlog.add hγ.neg using 1
  · ext n; ring
  · simp

theorem summable_digammaSeriesTerm {x : ℝ} (hx : 0 < x) :
    Summable (digammaSeriesTerm x) := by
  refine Summable.of_norm_bounded_eventually_nat
    (((summable_one_div_nat_pow (p := 2)).mpr one_lt_two).mul_left |x - 1|) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hxn : x + (n : ℝ) ≠ 0 := (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg _)).ne'
  rw [norm_eq_abs, digammaSeriesTerm, inv_sub_inv (by positivity) hxn, abs_div, abs_mul,
    abs_of_pos (by positivity : 0 < (n + 1 : ℝ)),
    abs_of_pos (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n))]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrearr : x + n - (n + 1) = x - 1 := by ring
  rw [hrearr]
  calc
    |x - 1| / ((n + 1) * (x + n)) ≤ |x - 1| / (n * n) := by
      gcongr <;> linarith
    _ = |x - 1| * (1 / (n : ℝ) ^ 2) := by ring

theorem tendsto_partial_digammaSeries {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => ∑ k ∈ range (n + 1), digammaSeriesTerm x k) atTop
      (𝓝 (∑' n, digammaSeriesTerm x n)) :=
  (summable_digammaSeriesTerm hx).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem eq_partial_digammaSeries (x : ℝ) (n : ℕ) :
    log n - ∑ k ∈ range (n + 1), (x + k)⁻¹ =
      log n - (harmonic (n + 1) : ℝ) + ∑ k ∈ range (n + 1), digammaSeriesTerm x k := by
  simp [digammaSeriesTerm, harmonic, sum_sub_distrib]

theorem tendsto_log_sub_sum_recip {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => log n - ∑ k ∈ range (n + 1), (x + k)⁻¹) atTop
      (𝓝 (-γ + ∑' n, digammaSeriesTerm x n)) := by
  simp_rw [eq_partial_digammaSeries]
  exact tendsto_log_sub_harmonic_succ.add (tendsto_partial_digammaSeries hx)

theorem tendsto_deriv_log_GammaSeq {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => log n - ∑ k ∈ range (n + 1), (x + k)⁻¹) atTop
      (𝓝 (digamma x)) := by
  rw [digamma_eq_deriv_log hx]
  set g : ℝ → ℝ := log ∘ Gamma
  have hg : DifferentiableAt ℝ g x := by
    have hG : DifferentiableAt ℝ Gamma x :=
      differentiableAt_Gamma fun m => ((neg_nonpos.mpr m.cast_nonneg).trans_lt hx).ne'
    exact hG.log (Gamma_pos_of_pos hx).ne'
  refine Metric.tendsto_atTop.mpr fun ε εpos => ?_
  have hslope := hg.hasDerivAt.tendsto_slope
  have hleft : Tendsto (slope g x) (𝓝[<] x) (𝓝 (deriv g x)) :=
    hslope.mono_left (nhdsLT_le_nhdsNE x)
  have hright : Tendsto (slope g x) (𝓝[>] x) (𝓝 (deriv g x)) :=
    hslope.mono_left (nhdsGT_le_nhdsNE x)
  have hIooL : Ioo (x / 2) x ∈ 𝓝[<] x := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Ioo (x / 2) (x + 1), Ioo_mem_nhds (half_lt_self hx) (lt_add_one x), ?_⟩
    intro y hy
    exact ⟨hy.1.1, hy.2⟩
  have hIooR : Ioo x (x + 1) ∈ 𝓝[>] x := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Ioo (x / 2) (x + 1), Ioo_mem_nhds (half_lt_self hx) (lt_add_one x), ?_⟩
    intro y hy
    exact ⟨hy.2, hy.1.2⟩
  obtain ⟨a, haIoo, haε⟩ :
      ∃ a, a ∈ Ioo (x / 2) x ∧ dist (slope g x a) (deriv g x) < ε / 2 := by
    have hmem := inter_mem hIooL (hleft (Metric.ball_mem_nhds _ (half_pos εpos)))
    obtain ⟨a, ha⟩ := Filter.nonempty_of_mem hmem
    exact ⟨a, ha.1, ha.2⟩
  obtain ⟨b, hbIoo, hbε⟩ :
      ∃ b, b ∈ Ioo x (x + 1) ∧ dist (slope g x b) (deriv g x) < ε / 2 := by
    have hmem := inter_mem hIooR (hright (Metric.ball_mem_nhds _ (half_pos εpos)))
    obtain ⟨b, hb⟩ := Filter.nonempty_of_mem hmem
    exact ⟨b, hb.1, hb.2⟩
  have ha : 0 < a := lt_trans (half_pos hx) haIoo.1
  have hax : a < x := haIoo.2
  have hxb : x < b := hbIoo.1
  have hb : 0 < b := lt_trans hx hxb
  have hsa : Tendsto (fun n : ℕ => slope (fun y => log (GammaSeq y n)) a x) atTop
      (𝓝 (slope g a x)) := by
    simp_rw [slope_def_field]
    convert ((tendsto_log_GammaSeq hx).sub (tendsto_log_GammaSeq ha)).div_const (x - a) using 1
    simp [g]
  have hsb : Tendsto (fun n : ℕ => slope (fun y => log (GammaSeq y n)) x b) atTop
      (𝓝 (slope g x b)) := by
    simp_rw [slope_def_field]
    convert ((tendsto_log_GammaSeq hb).sub (tendsto_log_GammaSeq hx)).div_const (b - x) using 1
    simp [g]
  have hsaE := hsa.eventually (Metric.ball_mem_nhds _ (half_pos εpos))
  have hsbE := hsb.eventually (Metric.ball_mem_nhds _ (half_pos εpos))
  have hEv : ∀ᶠ n : ℕ in atTop,
      dist (log n - ∑ k ∈ range (n + 1), (x + k)⁻¹) (deriv g x) < ε := by
    filter_upwards [eventually_ne_atTop 0, hsaE, hsbE] with n hn hna hnb
    have hval : log n - ∑ k ∈ range (n + 1), (x + k)⁻¹ =
        deriv (fun y => log (GammaSeq y n)) x :=
      (hasDerivAt_log_GammaSeq hx hn).deriv.symm
    have hconv := convexOn_log_GammaSeq hn
    have hdiff : DifferentiableAt ℝ (fun y => log (GammaSeq y n)) x :=
      (hasDerivAt_log_GammaSeq hx hn).differentiableAt
    have hlo := hconv.slope_le_deriv (mem_Ioi.mpr ha) (mem_Ioi.mpr hx) hax hdiff
    have hhi := hconv.deriv_le_slope (mem_Ioi.mpr hx) (mem_Ioi.mpr hb) hxb hdiff
    have hslope_eq : slope g a x = slope g x a := slope_comm g a x
    have hna' : |slope (fun y => log (GammaSeq y n)) a x - slope g a x| < ε / 2 := hna
    have hnb' : |slope (fun y => log (GammaSeq y n)) x b - slope g x b| < ε / 2 := hnb
    have haε' : |slope g a x - deriv g x| < ε / 2 := by
      simpa [dist_eq_norm, Real.norm_eq_abs, hslope_eq, abs_sub_comm] using haε
    have hbε' : |slope g x b - deriv g x| < ε / 2 := by
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hbε
    rw [hval, dist_eq_norm, Real.norm_eq_abs, abs_lt]
    constructor
    · linarith [(abs_lt.mp hna').1, (abs_lt.mp haε').1, hlo]
    · linarith [(abs_lt.mp hnb').2, (abs_lt.mp hbε').2, hhi]
  exact eventually_atTop.1 hEv

/-- **AAR Theorem 1.2.5**, second formula, for positive real argument. -/
@[dlmf 5.7.E6]
theorem digamma_eq_tsum {x : ℝ} (hx : 0 < x) :
    digamma x = -γ + ∑' n, digammaSeriesTerm x n :=
  tendsto_nhds_unique (tendsto_deriv_log_GammaSeq hx) (tendsto_log_sub_sum_recip hx)

theorem hasDerivAt_digammaSeriesTerm {x : ℝ} (hx : 0 < x) (n : ℕ) :
    HasDerivAt (fun y : ℝ => digammaSeriesTerm y n) ((x + (n : ℝ))⁻¹ ^ 2) x := by
  have hne : x + n ≠ 0 := (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n)).ne'
  have hd : HasDerivAt (fun y : ℝ => y + n) 1 x := (hasDerivAt_id x).add_const _
  have hinv : HasDerivAt (fun y : ℝ => (y + n)⁻¹) (-((x + n) ^ 2)⁻¹ * 1) x :=
    (hasDerivAt_inv hne).comp x hd
  have hconst : HasDerivAt (fun _ : ℝ => ((n + 1 : ℝ)⁻¹)) 0 x := hasDerivAt_const _ _
  have hsub := hconst.sub hinv
  have hfun : (fun y : ℝ => digammaSeriesTerm y n) =ᶠ[𝓝 x]
      ((fun _ : ℝ => ((n + 1 : ℝ)⁻¹)) - fun y : ℝ => (y + n)⁻¹) :=
    Eventually.of_forall fun y => by simp [digammaSeriesTerm, Pi.sub_apply]
  have hsub' := hsub.congr_of_eventuallyEq hfun
  have hder : 0 - -((x + n) ^ 2)⁻¹ * 1 = (x + (n : ℝ))⁻¹ ^ 2 := by simp [pow_two]
  simpa [hder] using hsub'

theorem summable_trigamma {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => (x + n)⁻¹ ^ 2 := by
  have h := (Real.summable_one_div_nat_add_rpow x 2).mpr one_lt_two
  refine h.congr fun n => ?_
  have : 0 < x + n := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n)
  simp [one_div, abs_of_pos this, pow_two, add_comm]

/-- **AAR Theorem 1.2.5**, third formula: the trigamma series, for `x > 0`. -/
theorem hasDerivAt_digamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt digamma (∑' n : ℕ, (x + (n : ℝ))⁻¹ ^ 2) x := by
  have hx2 : 0 < x / 2 := half_pos hx
  have hxmem : x ∈ Ioi (x / 2) := half_lt_self hx
  have hu : Summable fun n : ℕ => (x / 2 + n)⁻¹ ^ 2 := summable_trigamma hx2
  have hg : ∀ (n : ℕ) (y : ℝ), y ∈ Ioi (x / 2) →
      HasDerivAt (fun z : ℝ => digammaSeriesTerm z n) ((y + (n : ℝ))⁻¹ ^ 2) y :=
    fun n y hy => hasDerivAt_digammaSeriesTerm (lt_trans hx2 hy) n
  have hg' : ∀ (n : ℕ) (y : ℝ), y ∈ Ioi (x / 2) →
      ‖((y + (n : ℝ))⁻¹ ^ 2)‖ ≤ (x / 2 + n)⁻¹ ^ 2 := by
    intro n y hy
    have hpos : 0 < y + n := add_pos_of_pos_of_nonneg (lt_trans hx2 hy) (Nat.cast_nonneg n)
    have hle : x / 2 + (n : ℝ) ≤ y + n := by
      have : x / 2 < y := hy
      linarith
    have : (y + n)⁻¹ ≤ (x / 2 + n)⁻¹ :=
      (inv_le_inv₀ hpos (add_pos_of_pos_of_nonneg hx2 (Nat.cast_nonneg n))).2 hle
    have habs : ‖((y + (n : ℝ))⁻¹ ^ 2)‖ = (y + n)⁻¹ ^ 2 := by
      simp [Real.norm_eq_abs]
    rw [habs]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) this 2
  have htsum :
      HasDerivAt (fun y : ℝ => ∑' n : ℕ, digammaSeriesTerm y n)
        (∑' n : ℕ, (x + (n : ℝ))⁻¹ ^ 2) x :=
    hasDerivAt_tsum_of_isPreconnected (g := fun n y => digammaSeriesTerm y n)
      (g' := fun n y => (y + (n : ℝ))⁻¹ ^ 2) hu isOpen_Ioi isPreconnected_Ioi hg hg'
      hxmem (summable_digammaSeriesTerm hx) hxmem
  have hconst : HasDerivAt (fun _ : ℝ => (-γ : ℝ)) 0 x := hasDerivAt_const _ _
  have hsum := hconst.add htsum
  have hfun : (fun y : ℝ => -γ + ∑' n : ℕ, digammaSeriesTerm y n) =ᶠ[𝓝 x]
      ((fun _ : ℝ => (-γ : ℝ)) + fun y => ∑' n : ℕ, digammaSeriesTerm y n) :=
    Eventually.of_forall fun y => by simp [Pi.add_apply]
  have hsum' := hsum.congr_of_eventuallyEq hfun
  have hdig : HasDerivAt (fun y : ℝ => digamma y) (∑' n : ℕ, (x + (n : ℝ))⁻¹ ^ 2) x := by
    have hfun : (fun y : ℝ => digamma y) =ᶠ[𝓝 x]
        (fun y : ℝ => -γ + ∑' n : ℕ, digammaSeriesTerm y n) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact digamma_eq_tsum hy
    have hder : 0 + ∑' n : ℕ, (x + (n : ℝ))⁻¹ ^ 2 = ∑' n : ℕ, (x + (n : ℝ))⁻¹ ^ 2 := by simp
    simpa [hder] using hsum'.congr_of_eventuallyEq hfun
  exact hdig

/-- The trigamma function `ψ'(x)`. -/
def trigamma (x : ℝ) : ℝ :=
  deriv digamma x

@[dlmf 5.15.E1]
theorem trigamma_eq_tsum {x : ℝ} (hx : 0 < x) :
    trigamma x = ∑' n : ℕ, (x + n)⁻¹ ^ 2 := by
  rw [trigamma, (hasDerivAt_digamma hx).deriv]

theorem sum_recip_sub_recip_range (x : ℝ) (N : ℕ) :
    ∑ n ∈ range N, ((x + n)⁻¹ - (x + n + 1)⁻¹) = x⁻¹ - (x + N)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    ring

/-- Recurrence `ψ(x+1) = ψ(x) + 1/x`. -/
@[dlmf 5.5.E2]
theorem digamma_add_one {x : ℝ} (hx : 0 < x) : digamma (x + 1) = digamma x + x⁻¹ := by
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have : x = -(m : ℝ) := by exact_mod_cast h
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [digamma_eq_re_digamma (by linarith), digamma_eq_re_digamma hx, Complex.ofReal_add,
    Complex.ofReal_one, Complex.digamma_apply_add_one _ hx', Complex.add_re,
    ← Complex.ofReal_inv, Complex.ofReal_re]

theorem digamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    digamma (x + n) = digamma x + ∑ k ∈ range n, (x + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx' : 0 < x + n := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n)
    rw [Nat.cast_succ, ← add_assoc, digamma_add_one hx', ih, sum_range_succ]
    ring

/-- `ψ(n+1) = -γ + H_n`. -/
@[dlmf 5.4.E14]
theorem digamma_nat_add_one (n : ℕ) :
    digamma (n + 1) = -γ + (harmonic n : ℝ) := by
  have := digamma_add_nat (by positivity : (0 : ℝ) < 1) n
  simpa [digamma_one, harmonic, add_comm, add_left_comm] using this

theorem hasDerivAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => log (Gamma y)) (digamma x) x := by
  have hG : DifferentiableAt ℝ Gamma x :=
    differentiableAt_Gamma fun m =>
      ((neg_nonpos.mpr m.cast_nonneg).trans_lt hx).ne'
  have hlog := hG.hasDerivAt.log (Gamma_pos_of_pos hx).ne'
  simpa [digamma, Function.comp_def] using hlog

theorem hasDerivAt_log_sin_pi {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => log (sin (π * y))) (π * cot (π * x)) x := by
  have hsin : sin (π * x) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hx.1)
      ((mul_lt_iff_lt_one_right pi_pos).2 hx.2)).ne'
  have h := (((hasDerivAt_id x).const_mul π).sin).log hsin
  simp only [id_eq, mul_one] at h
  convert h using 1
  rw [cot_eq_cos_div_sin]
  ring

/-- Reflection formula for the digamma function, AAR (1.2.18). -/
public theorem digamma_one_sub {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    digamma (1 - x) - digamma x = π * cot (π * x) := by
  have hint : ∀ n : ℤ, (x : ℂ) ≠ n := fun n h => by
    have hxn : x = n := by exact_mod_cast h
    have h1 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
    have h2 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
    omega
  have h := Complex.digamma_one_sub hint
  rw [digamma_eq_re_digamma (by linarith), digamma_eq_re_digamma hx0, Complex.ofReal_sub,
    Complex.ofReal_one, h, Complex.add_re, ← Complex.ofReal_mul, ← Complex.ofReal_cot,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

end Real


