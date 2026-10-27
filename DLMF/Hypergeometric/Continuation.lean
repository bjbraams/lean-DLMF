/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Derivatives
public import DLMF.Hypergeometric.Transformations
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.AbelLimit

/-!
# Analytic continuation in the parameters (DLMF §15.2(ii))

Mathlib's regularized Gauss function `regularizedGaussHGFun a b c z` is, for `‖z‖ < 1`, an
entire function of each of `a`, `b`, `c` separately. Together with the identity principle this
extends identities proved under restrictive parameter hypotheses to all parameters. The joint
statement `entire_regularized_parameters` in `AnalyticProperties.lean` is not derived here.

The proof dominates the tail of the series, on a neighbourhood of any point, by the series with
parameters `(‖a‖, ‖b‖, 1 - N)`, using `‖1/Γ(c+n)‖ ≤ 1/((n-N)! ‖Γ(c+N)‖)` for `Re (c+N) ≥ 1`.
-/

@[expose] public section

open Complex Filter Set FormalMultilinearSeries
open scoped Topology

noncomputable section

namespace DLMF.Hypergeometric

/-! ### The identity principle on `ℂ` -/

/-- Two entire functions agreeing near a point agree everywhere. -/
theorem eq_of_analyticOnNhd_univ_of_eventuallyEq {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ) {z₀ : ℂ}
    (hfg : f =ᶠ[𝓝 z₀] g) : f = g :=
  AnalyticOnNhd.eq_of_eventuallyEq hf hg hfg

/-- Two entire functions agreeing on a nonempty open set agree everywhere. -/
theorem eq_of_analyticOnNhd_univ_of_eqOn {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ) {U : Set ℂ} (hU : IsOpen U)
    (hne : U.Nonempty) (h : EqOn f g U) : f = g := by
  obtain ⟨z₀, hz₀⟩ := hne
  exact AnalyticOnNhd.eq_of_eventuallyEq hf hg (eventuallyEq_of_mem (hU.mem_nhds hz₀) h)

/-! ### Series of entire functions -/

/-- A series of entire functions whose terms are, near every point, eventually dominated by a
summable sequence defines an entire function. -/
theorem analyticOnNhd_tsum_of_eventually_dominated {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hsum : ∀ w, Summable fun n => F n w)
    (hdom : ∀ w₀ : ℂ, ∃ U : Set ℂ, IsOpen U ∧ w₀ ∈ U ∧ ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, N ≤ n → ∀ w ∈ U, ‖F n w‖ ≤ u n) :
    AnalyticOnNhd ℂ (fun w => ∑' n, F n w) univ := by
  intro w₀ _
  obtain ⟨U, hU, hw₀, N, u, hu, hle⟩ := hdom w₀
  have hsplit : ∀ w ∈ U,
      (∑' n, F n w) = ∑ n ∈ Finset.range N, F n w + ∑' k, F (k + N) w :=
    fun w _ => ((hsum w).sum_add_tsum_nat_add N).symm
  have htail : DifferentiableOn ℂ (fun w => ∑' k, F (k + N) w) U :=
    differentiableOn_tsum_of_summable_norm (u := fun k => u (k + N))
      (hu.comp_injective (add_left_injective N)) (fun k => (hF (k + N)).differentiableOn) hU
      (fun k w hw => hle (k + N) (by omega) w hw)
  have hfin : DifferentiableOn ℂ (fun w => ∑ n ∈ Finset.range N, F n w) U :=
    DifferentiableOn.fun_sum fun n _ => (hF n).differentiableOn
  have hdiff : DifferentiableOn ℂ (fun w => ∑' n, F n w) U :=
    (hfin.add htail).congr fun w hw => hsplit w hw
  exact hdiff.analyticAt (hU.mem_nhds hw₀)

/-! ### Bounds -/

/-- Pochhammer symbols with nonnegative real argument are nonnegative. -/
theorem ascPochhammer_eval_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ (ascPochhammer ℝ n).eval x := by
  exact poch_eval_nonneg hx n

/-- Pochhammer symbols are monotone on the nonnegative reals. -/
theorem ascPochhammer_eval_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    (ascPochhammer ℝ n).eval x ≤ (ascPochhammer ℝ n).eval y := by
  exact poch_eval_mono hx hxy n

/-- Evaluating the complex Pochhammer polynomial at a real number. -/
theorem ascPochhammer_eval_ofReal (x : ℝ) (n : ℕ) :
    (ascPochhammer ℂ n).eval (x : ℂ) = (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) := by
  have h := ascPochhammer_map (algebraMap ℝ ℂ) n
  rw [← h, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply _ _

/-- `‖(a)_n‖ ≤ (r)_n` for `‖a‖ ≤ r`. -/
theorem norm_ascPochhammer_eval_le {a : ℂ} {r : ℝ} (hr : ‖a‖ ≤ r) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval a‖ ≤ ‖(ascPochhammer ℂ n).eval (r : ℂ)‖ := by
  rw [ascPochhammer_eval_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact (norm_poch_le a n).trans
    ((ascPochhammer_eval_mono (norm_nonneg a) hr n).trans (le_abs_self _))

/-- Lower bound for the Pochhammer symbol when `1 ≤ Re w`. -/
theorem factorial_le_norm_ascPochhammer_eval {w : ℂ} (hw : 1 ≤ w.re) (k : ℕ) :
    (k.factorial : ℝ) ≤ ‖(ascPochhammer ℂ k).eval w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, norm_mul, Nat.factorial_succ, Nat.cast_mul]
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ ‖w + k‖ := by
      calc ((k + 1 : ℕ) : ℝ) = 1 + k := by push_cast; ring
        _ ≤ (w + k).re := by simp only [Complex.add_re, Complex.natCast_re]; linarith
        _ ≤ ‖w + k‖ := re_le_norm _
    calc ((k + 1 : ℕ) : ℝ) * k.factorial ≤ ‖w + k‖ * ‖(ascPochhammer ℂ k).eval w‖ :=
          mul_le_mul h1 ih (by positivity) (norm_nonneg _)
      _ = _ := by ring

/-- `‖1/Γ(c+n)‖ ≤ 1/((n-N)! m)` for `n ≥ N`, when `1 ≤ Re (c+N)` and `m ≤ ‖Γ(c+N)‖`. -/
theorem norm_recip_Gamma_add_nat_le {c : ℂ} {N : ℕ} (hre : 1 ≤ (c + N).re) {m : ℝ} (hm : 0 < m)
    (hΓ : m ≤ ‖Gamma (c + N)‖) {n : ℕ} (hn : N ≤ n) :
    ‖(Gamma (c + n))⁻¹‖ ≤ ((n - N).factorial : ℝ)⁻¹ * m⁻¹ := by
  have hpole : ∀ k : ℕ, c + N ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hΓ0 : Gamma (c + N) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hΓ
    linarith
  have heq : c + n = c + N + ((n - N : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hn]
    ring
  have hG : Gamma (c + N + ((n - N : ℕ) : ℂ)) =
      (ascPochhammer ℂ (n - N)).eval (c + N) * Gamma (c + N) := by
    rw [← Gamma_add_nat_div_Gamma_eq (n := n - N) (c + N) hpole]
    field_simp
  rw [heq, hG, mul_inv, norm_mul, norm_inv, norm_inv]
  have hp := factorial_le_norm_ascPochhammer_eval hre (n - N)
  have hfpos : (0 : ℝ) < (n - N).factorial := by positivity
  gcongr

/-! ### The nonpositive integers -/

/-- The complement of the nonpositive integers is open in `ℂ`. -/
theorem isOpen_not_neg_nat : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := by
  have hce : Topology.IsClosedEmbedding (fun m : ℕ => -((m : ℝ) : ℂ)) :=
    (Homeomorph.neg ℂ).isClosedEmbedding.comp
      (Complex.isometry_ofReal.isClosedEmbedding.comp Nat.isClosedEmbedding_coe_real)
  have hset : {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} = (Set.range fun m : ℕ => -((m : ℝ) : ℂ))ᶜ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists,
      Complex.ofReal_natCast]
    exact ⟨fun h m hm => h m hm.symm, fun h m hm => h m hm.symm⟩
  rw [hset]
  exact hce.isClosed_range.isOpen_compl

/-- Near `-n`, but away from it, no nonpositive integer is hit. -/
theorem eventually_nhdsWithin_ne_neg_nat (n : ℕ) :
    ∀ᶠ c in 𝓝[≠] (-(n : ℂ)), ∀ k : ℕ, c ≠ -(k : ℂ) := by
  have h1 : ∀ᶠ c in 𝓝[≠] (-(n : ℂ)), c ≠ -(n : ℂ) := self_mem_nhdsWithin
  have h2 : ∀ᶠ c in 𝓝[≠] (-(n : ℂ)), dist c (-(n : ℂ)) < 1 / 2 :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (-(n : ℂ)) (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [h1, h2] with c hc hc' k hk
  rw [dist_eq_norm] at hc'
  rcases eq_or_ne k n with rfl | hkn
  · exact hc hk
  · have hdist : (1 : ℝ) ≤ ‖(-(k : ℂ)) - -(n : ℂ)‖ := by
      rw [show (-(k : ℂ)) - -(n : ℂ) = (((n : ℤ) - k : ℤ) : ℂ) by push_cast; ring,
        Complex.norm_intCast]
      have : (n : ℤ) - k ≠ 0 := by omega
      exact_mod_cast Int.one_le_abs this
    rw [hk] at hc'
    linarith

/-- `(x)_{m+k} = (x)_m (x+m)_k`. -/
theorem ascPochhammer_eval_add (x : ℂ) (m k : ℕ) :
    (ascPochhammer ℂ (m + k)).eval x =
      (ascPochhammer ℂ m).eval x * (ascPochhammer ℂ k).eval (x + m) := by
  rw [← ascPochhammer_mul, Polynomial.eval_mul, Polynomial.eval_comp]
  simp

/-- `1/Γ(y) = (y)_{p+1}/Γ(y+p+1)` for every `y`. -/
theorem recip_Gamma_eq_poch_mul (p : ℕ) (y : ℂ) :
    (Gamma y)⁻¹ = poch y (p + 1) * (Gamma (y + (p + 1 : ℕ)))⁻¹ := by
  by_cases hy : ∀ m : ℕ, y ≠ -(m : ℂ)
  · have h := Gamma_add_nat_div_Gamma_eq (n := p + 1) y hy
    have h0 := Gamma_ne_zero hy
    have h1 : Gamma (y + (p + 1 : ℕ)) ≠ 0 := Gamma_ne_zero (not_neg_nat_add_nat hy _)
    rw [poch, ← h]
    field_simp
  · simp only [not_forall, not_not] at hy
    obtain ⟨j, rfl⟩ := hy
    rw [Gamma_neg_nat_eq_zero, inv_zero]
    rcases Nat.lt_or_ge p j with hpj | hpj
    · have : -(j : ℂ) + ((p + 1 : ℕ) : ℂ) = -((j - p - 1 : ℕ) : ℂ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [this, Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
    · rw [poch_neg_nat_eq_zero (by omega), zero_mul]

/-! ### The regularized Gauss function -/

/-- The regularized Gauss series with the `Γ` factor isolated. -/
theorem regularizedGaussHGFun_eq_tsum (a b c z : ℂ) :
    regularizedGaussHGFun a b c z =
      ∑' n : ℕ, (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n / n.factorial *
        (Gamma (c + n))⁻¹ := by
  unfold regularizedGaussHGFun FormalMultilinearSeries.sum
  congr 1
  funext n
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, coeff_regularizedGaussHGFunSeries,
    smul_eq_mul]
  ring

/-- Membership of the disk in the ball of convergence of the regularized series. -/
theorem mem_eball_radius_regularizedGaussHGFunSeries (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries a b c).radius :=
  Metric.eball_subset_eball (radius_regularizedGaussHGFunSeries_ge_one a b c)
    (mem_eball_one_of_norm_lt_one hz)

theorem summable_regularizedGaussHGFun_term (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n / n.factorial *
        (Gamma (c + n))⁻¹ := by
  have hpos : (0 : ENNReal) < (regularizedGaussHGFunSeries a b c).radius :=
    lt_of_lt_of_le (by norm_num) (radius_regularizedGaussHGFunSeries_ge_one a b c)
  have h := ((regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall hpos).hasSum_mul_pow
    (mem_eball_radius_regularizedGaussHGFunSeries a b c hz)
  refine h.summable.congr fun n => ?_
  have hc : regularizedHGFunCoeff {a, b} {c} n = (regularizedGaussHGFunSeries a b c).coeff n := by
    rw [regularizedGaussHGFunSeries, regularizedHGFunSeries_coeff]
  rw [hc, coeff_regularizedGaussHGFunSeries]
  ring

theorem norm_regularizedGaussHGFunSeries_apply_ofReal (α β : ℝ) (N n : ℕ) (hn : N ≤ n) :
    ‖regularizedGaussHGFunSeries (α : ℂ) (β : ℂ) (1 - N) n‖ =
      ‖(ascPochhammer ℂ n).eval (α : ℂ)‖ * ‖(ascPochhammer ℂ n).eval (β : ℂ)‖ /
        (n.factorial * (n - N).factorial) := by
  have hΓ : Gamma ((1 : ℂ) - N + n) = ((n - N).factorial : ℂ) := by
    rw [show (1 : ℂ) - N + n = ((n - N : ℕ) : ℂ) + 1 by push_cast [Nat.cast_sub hn]; ring]
    exact Complex.Gamma_nat_eq_factorial _
  rw [norm_apply_eq_norm_coef, coeff_regularizedGaussHGFunSeries, hΓ, norm_div, norm_mul, norm_mul,
    Complex.norm_natCast, Complex.norm_natCast]

/-- The tail-domination step, shared by the three parameters: on `U` the `n`-th term is
bounded by the `n`-th term of the majorant series. -/
theorem norm_term_le_majorant {a b c : ℂ} {z : ℂ} {α β : ℝ}
    (ha : ‖a‖ ≤ α) (hb : ‖b‖ ≤ β) {N : ℕ} (hre : 1 ≤ (c + N).re) {m : ℝ} (hm : 0 < m)
    (hΓ : m ≤ ‖Gamma (c + N)‖) {n : ℕ} (hn : N ≤ n) :
    ‖(ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n / n.factorial *
        (Gamma (c + n))⁻¹‖ ≤
      m⁻¹ * (‖regularizedGaussHGFunSeries (α : ℂ) (β : ℂ) (1 - N) n‖ * ‖z‖ ^ n) := by
  rw [norm_regularizedGaussHGFunSeries_apply_ofReal α β N n hn, norm_mul, norm_div, norm_mul,
    norm_mul, norm_pow, Complex.norm_natCast]
  have hA := norm_ascPochhammer_eval_le ha n
  have hB := norm_ascPochhammer_eval_le hb n
  have hG := norm_recip_Gamma_add_nat_le hre hm hΓ hn
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hf' : (0 : ℝ) < (n - N).factorial := by positivity
  calc ‖(ascPochhammer ℂ n).eval a‖ * ‖(ascPochhammer ℂ n).eval b‖ * ‖z‖ ^ n / n.factorial *
        ‖(Gamma (c + n))⁻¹‖
      ≤ ‖(ascPochhammer ℂ n).eval (α : ℂ)‖ * ‖(ascPochhammer ℂ n).eval (β : ℂ)‖ * ‖z‖ ^ n /
          n.factorial * (((n - N).factorial : ℝ)⁻¹ * m⁻¹) := by gcongr
    _ = _ := by field_simp

/-- The nonvanishing of `Γ` near a point with real part at least two. -/
theorem exists_open_norm_Gamma_add_nat_gt {c₀ : ℂ} {N : ℕ} (hre : 2 ≤ (c₀ + N).re) :
    ∃ V : Set ℂ, IsOpen V ∧ c₀ ∈ V ∧
      ∀ c ∈ V, ‖Gamma (c₀ + N)‖ / 2 < ‖Gamma (c + N)‖ := by
  have hpole : ∀ k : ℕ, c₀ + N ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hΓ0 : Gamma (c₀ + N) ≠ 0 := Gamma_ne_zero hpole
  have hcont : ContinuousAt (fun c : ℂ => ‖Gamma (c + N)‖) c₀ :=
    ((differentiableAt_Gamma _ hpole).comp c₀ (differentiableAt_id.add_const _)).continuousAt.norm
  have hev : ∀ᶠ c in 𝓝 c₀, ‖Gamma (c₀ + N)‖ / 2 < ‖Gamma (c + N)‖ :=
    hcont.eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr hΓ0)))
  obtain ⟨V, hV, hVopen, hc₀V⟩ := eventually_nhds_iff.mp hev
  exact ⟨V, hVopen, hc₀V, hV⟩

/-- The regularized Gauss function is entire along any entire curve in the parameter space
(DLMF §15.2(ii)): for entire `A B C`, `w ↦ 𝐅(A w, B w; C w; z)` is entire when `‖z‖ < 1`. -/
theorem analyticOnNhd_regularizedGaussHGFun_comp {A B C : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun w => regularizedGaussHGFun (A w) (B w) (C w) z) univ := by
  simp_rw [regularizedGaussHGFun_eq_tsum]
  refine analyticOnNhd_tsum_of_eventually_dominated ?_ ?_ ?_
  · intro n
    have h1 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (A w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hA
    have h2 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (B w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hB
    exact (((h1.mul h2).mul_const _).div_const _).mul
      (differentiable_one_div_Gamma.comp (hC.add_const _))
  · intro w
    exact summable_regularizedGaussHGFun_term _ _ _ hz
  · intro w₀
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - (C w₀).re ≤ N := exists_nat_ge _
    have hre0 : 2 ≤ (C w₀ + N).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    obtain ⟨V, hVopen, hc₀V, hV⟩ := exists_open_norm_Gamma_add_nat_gt hre0
    have hevA : ∀ᶠ w in 𝓝 w₀, ‖A w‖ < ‖A w₀‖ + 1 :=
      hA.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
    have hevB : ∀ᶠ w in 𝓝 w₀, ‖B w‖ < ‖B w₀‖ + 1 :=
      hB.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
    have hevC : ∀ᶠ w in 𝓝 w₀, (C w₀).re - 1 < (C w).re :=
      (Complex.continuous_re.comp hC.continuous).continuousAt.eventually
        (lt_mem_nhds (by show (C w₀).re - 1 < (C w₀).re; linarith))
    have hevV : ∀ᶠ w in 𝓝 w₀, C w ∈ V := hC.continuous.continuousAt (hVopen.mem_nhds hc₀V)
    obtain ⟨U, hU, hUopen, hw₀U⟩ := eventually_nhds_iff.mp (hevA.and (hevB.and (hevC.and hevV)))
    refine ⟨U, hUopen, hw₀U, N, ?_⟩
    set p := regularizedGaussHGFunSeries ((‖A w₀‖ + 1 : ℝ) : ℂ) ((‖B w₀‖ + 1 : ℝ) : ℂ) (1 - N)
      with hp
    have hz' : (‖z‖₊ : ENNReal) < p.radius := by
      refine lt_of_lt_of_le ?_ (radius_regularizedGaussHGFunSeries_ge_one _ _ _)
      rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
      exact hz
    have hm : 0 < ‖Gamma (C w₀ + N)‖ / 2 := by
      have hpole : ∀ k : ℕ, C w₀ + N ≠ -k := fun k h => by
        have := congrArg Complex.re h
        simp only [Complex.neg_re, Complex.natCast_re] at this
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
      positivity
    refine ⟨fun n => (‖Gamma (C w₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (‖z‖₊ : ℝ) ^ n),
      (p.summable_norm_mul_pow hz').mul_left _, ?_⟩
    intro n hn w hw
    obtain ⟨hAw, hBw, hCw, hVw⟩ := hU w hw
    have hre : 1 ≤ (C w + N).re := by
      simp only [Complex.add_re, Complex.natCast_re] at hre0 ⊢
      linarith
    simpa only [coe_nnnorm] using
      norm_term_le_majorant hAw.le hBw.le hre hm (hV _ hVw).le hn

/-- The regularized Gauss function is entire in the parameter `c` (DLMF §15.2(ii)). -/
theorem analyticOnNhd_regularizedGaussHGFun_c (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun c => regularizedGaussHGFun a b c z) univ :=
  analyticOnNhd_regularizedGaussHGFun_comp (differentiable_const a) (differentiable_const b)
    differentiable_id hz

/-- The regularized Gauss function is entire in the parameter `a` (DLMF §15.2(ii)). -/
theorem analyticOnNhd_regularizedGaussHGFun_a (b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun a => regularizedGaussHGFun a b c z) univ :=
  analyticOnNhd_regularizedGaussHGFun_comp differentiable_id (differentiable_const b)
    (differentiable_const c) hz

/-- The regularized Gauss function is entire in the parameter `b` (DLMF §15.2(ii)). -/
theorem analyticOnNhd_regularizedGaussHGFun_b (a c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun b => regularizedGaussHGFun a b c z) univ :=
  analyticOnNhd_regularizedGaussHGFun_comp (differentiable_const a) differentiable_id
    (differentiable_const c) hz

/-- Pointwise form of `analyticOnNhd_regularizedGaussHGFun_comp`, usable by `fun_prop`. -/
@[fun_prop]
theorem analyticAt_regularizedGaussHGFun_comp {A B C : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : ‖z‖ < 1) (w : ℂ) :
    AnalyticAt ℂ (fun w => regularizedGaussHGFun (A w) (B w) (C w) z) w :=
  analyticOnNhd_regularizedGaussHGFun_comp hA hB hC hz w (mem_univ w)

/-- Two entire functions agreeing off the nonpositive integers agree everywhere. -/
theorem eq_of_eqOn_not_neg_nat {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) (h : ∀ c : ℂ, (∀ k : ℕ, c ≠ -(k : ℂ)) → f c = g c) : f = g :=
  eq_of_analyticOnNhd_univ_of_eqOn hf hg isOpen_not_neg_nat ⟨1, fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩ h

/-- Two entire functions agreeing on the open right half-plane agree everywhere. -/
theorem eq_of_eqOn_re_pos {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) (h : ∀ c : ℂ, 0 < c.re → f c = g c) : f = g :=
  eq_of_analyticOnNhd_univ_of_eqOn hf hg (isOpen_lt continuous_const Complex.continuous_re)
    ⟨1, by simp⟩ h

/-! ### The regularized derivative formula, for all parameters -/

/-- The coefficient recurrence behind 15.5.1, valid for all parameters. -/
theorem regularizedHGFunCoeff_pair_succ (a b c : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * regularizedHGFunCoeff {a, b} {c} (n + 1) =
      a * b * regularizedHGFunCoeff {a + 1, b + 1} {c + 1} n := by
  have hc1 : regularizedHGFunCoeff {a, b} {c} (n + 1) =
      (regularizedGaussHGFunSeries a b c).coeff (n + 1) := by
    rw [regularizedGaussHGFunSeries, regularizedHGFunSeries_coeff]
  have hc2 : regularizedHGFunCoeff {a + 1, b + 1} {c + 1} n =
      (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).coeff n := by
    rw [regularizedGaussHGFunSeries, regularizedHGFunSeries_coeff]
  rw [hc1, hc2, coeff_regularizedGaussHGFunSeries, coeff_regularizedGaussHGFunSeries,
    show (ascPochhammer ℂ (n + 1)).eval a = a * (ascPochhammer ℂ n).eval (a + 1) from
      poch_succ_left a n,
    show (ascPochhammer ℂ (n + 1)).eval b = b * (ascPochhammer ℂ n).eval (b + 1) from
      poch_succ_left b n,
    show c + ((n + 1 : ℕ) : ℂ) = c + 1 + n by push_cast; ring, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
  field_simp

/-- 15.5.1 for the regularized function: `𝐅'(a,b;c;z) = a b 𝐅(a+1,b+1;c+1;z)`, with no
hypothesis on the parameters. -/
theorem deriv_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (regularizedGaussHGFun a b c) z =
      a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z := by
  have hpos : ∀ a b c : ℂ, (0 : ENNReal) < (regularizedGaussHGFunSeries a b c).radius :=
    fun a b c => lt_of_lt_of_le (by norm_num) (radius_regularizedGaussHGFunSeries_ge_one a b c)
  have hp : HasFPowerSeriesOnBall (regularizedGaussHGFun a b c)
      (ofScalars ℂ (regularizedHGFunCoeff {a, b} {c})) 0
      (regularizedGaussHGFunSeries a b c).radius :=
    (regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall (hpos a b c)
  have hq : HasFPowerSeriesOnBall (regularizedGaussHGFun (a + 1) (b + 1) (c + 1))
      (ofScalars ℂ (regularizedHGFunCoeff {a + 1, b + 1} {c + 1})) 0
      (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).radius :=
    (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).hasFPowerSeriesOnBall (hpos _ _ _)
  have hd := hp.deriv_ofScalars.hasSum_mul_pow
    (mem_eball_radius_regularizedGaussHGFunSeries a b c hz)
  have hs := (hq.hasSum_mul_pow
    (mem_eball_radius_regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1) hz)).mul_left (a * b)
  refine hd.unique ?_
  convert hs using 1
  funext n
  rw [← mul_assoc, regularizedHGFunCoeff_pair_succ]

/-- `𝐅(a,b;c;·)` is differentiable on the unit disk. -/
theorem differentiableAt_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (regularizedGaussHGFun a b c) z := by
  have hpos : (0 : ENNReal) < (regularizedGaussHGFunSeries a b c).radius :=
    lt_of_lt_of_le (by norm_num) (radius_regularizedGaussHGFunSeries_ge_one a b c)
  exact (((regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall hpos).analyticAt_of_mem
    (mem_eball_radius_regularizedGaussHGFunSeries a b c hz)).differentiableAt

/-- 15.5.2 for the regularized function, with no hypothesis on the parameters:
`𝐅⁽ⁿ⁾(a,b;c;z) = (a)ₙ (b)ₙ 𝐅(a+n,b+n;c+n;z)`. -/
theorem iteratedDeriv_regularizedGaussHGFun (a b c : ℂ) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    iteratedDeriv n (regularizedGaussHGFun a b c) z =
      poch a n * poch b n * regularizedGaussHGFun (a + n) (b + n) (c + n) z := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (regularizedGaussHGFun a b c) =ᶠ[𝓝 z]
        fun w => poch a n * poch b n * regularizedGaussHGFun (a + n) (b + n) (c + n) w := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
      exact ih hw
    rw [heq.deriv_eq, deriv_const_mul _ (differentiableAt_regularizedGaussHGFun _ _ _ hz),
      deriv_regularizedGaussHGFun _ _ _ hz, poch_succ, poch_succ,
      show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring,
      show b + ((n + 1 : ℕ) : ℂ) = b + n + 1 by push_cast; ring,
      show c + ((n + 1 : ℕ) : ℂ) = c + n + 1 by push_cast; ring]
    ring

/-- `𝐅(a,b;c;z)` is entire in `c` after any translation of `c`. -/
theorem analyticOnNhd_regularizedGaussHGFun_c_add (a b t : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun c => regularizedGaussHGFun a b (c + t) z) univ :=
  (analyticOnNhd_regularizedGaussHGFun_c a b hz).comp
    (analyticOnNhd_id.add analyticOnNhd_const) (mapsTo_univ _ _)

/-- The Gauss function and its regularization agree off the poles. -/
theorem regularizedGaussHGFun_eq_div_Gamma {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (z : ℂ) :
    regularizedGaussHGFun a b c z = ₂F₁ a b c z / Gamma c :=
  (ordinaryHypergeometric_div_Gamma_eq hc).symm

theorem not_neg_nat_add_one {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    ∀ k : ℕ, c + 1 ≠ -(k : ℂ) := by
  simpa using not_neg_nat_add_nat hc 1

theorem ne_zero_of_not_neg_nat {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) : c ≠ 0 := by
  simpa using hc 0

theorem Gamma_succ_of_not_neg_nat {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    Gamma (c + 1) = c * Gamma c :=
  Gamma_add_one c (ne_zero_of_not_neg_nat hc)

/-- Two entire functions agreeing on `{c | c - 1 ∉ -ℕ}` agree everywhere. -/
theorem eq_of_eqOn_not_neg_nat_sub_one {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) (h : ∀ c : ℂ, (∀ k : ℕ, c - 1 ≠ -(k : ℂ)) → f c = g c) :
    f = g :=
  eq_of_analyticOnNhd_univ_of_eqOn hf hg
    (isOpen_not_neg_nat.preimage (continuous_id.sub continuous_const)) ⟨2, fun k h => by
      have := congrArg Complex.re h
      simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩ h

theorem eqFun_of_eqOn_not_neg_nat (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (h : ∀ c : ℂ, (∀ k : ℕ, c ≠ -(k : ℂ)) → f c = g c) (c : ℂ) : f c = g c :=
  congrFun (eq_of_eqOn_not_neg_nat hf hg h) c

/-- The regularized Gauss function as a differentiable function of an entire curve in the
parameters, usable by `fun_prop`. -/
@[fun_prop]
theorem differentiable_regularizedGaussHGFun_comp {A B C : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : ‖z‖ < 1) :
    Differentiable ℂ (fun w => regularizedGaussHGFun (A w) (B w) (C w) z) :=
  fun w => ((analyticOnNhd_regularizedGaussHGFun_comp hA hB hC hz) w (mem_univ w)).differentiableAt

/-! ### Regularized contiguous relations (all parameters)

Each identity is the ordinary disk relation, rewritten in `𝐅 = ₂F₁/Γ(c)` and extended
to all `c` by the identity principle. The generators `contiguous_c`, `contiguous_a`,
`contiguous_shift_b`, and `deriv_contiguous_c_succ` are lifted that way; the remaining
neighbours are linear combinations of those regularized identities, matching
`Derivatives.lean`.
-/

/-- 15.5.11 for the regularized function: `𝐅(a,b;c) = (c-a) 𝐅(a,b;c+1) + a 𝐅(a+1,b;c+1)`. -/
theorem regularizedGaussHGFun_contiguous_c (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (c - a) * regularizedGaussHGFun a b (c + 1) z +
        a * regularizedGaussHGFun (a + 1) b (c + 1) z :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => regularizedGaussHGFun a b c z)
    (fun c => (c - a) * regularizedGaussHGFun a b (c + 1) z +
      a * regularizedGaussHGFun (a + 1) b (c + 1) z)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hc1 := not_neg_nat_add_one hc
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have hΓ1 := Gamma_succ_of_not_neg_nat hc
      have h := contiguous_c (a := a) (b := b) hc hz
      simp only [regularizedGaussHGFun_eq_div_Gamma hc,
        regularizedGaussHGFun_eq_div_Gamma hc1, hΓ1]
      field_simp [hΓ0, ne_zero_of_not_neg_nat hc]
      linear_combination h) c

/-- 15.5.16 (`contiguous_shift_b`) for the regularized function, valid for all parameters. -/
theorem regularizedGaussHGFun_contiguous_shift_b (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z - regularizedGaussHGFun a (b + 1) c z =
      -(a * z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => regularizedGaussHGFun a b c z - regularizedGaussHGFun a (b + 1) c z)
    (fun c => -(a * z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hc1 := not_neg_nat_add_one hc
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have hΓ1 := Gamma_succ_of_not_neg_nat hc
      have h := contiguous_shift_b (a := a) (b := b) hc hz
      simp only [regularizedGaussHGFun_eq_div_Gamma hc,
        regularizedGaussHGFun_eq_div_Gamma hc1, hΓ1]
      field_simp [hΓ0, ne_zero_of_not_neg_nat hc]
      linear_combination h) c

/-- 15.5.11 (`contiguous_a`) for the regularized function, valid for all parameters. -/
theorem regularizedGaussHGFun_contiguous_a (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (c - a) * regularizedGaussHGFun (a - 1) b c z +
        (2 * a - c + (b - a) * z) * regularizedGaussHGFun a b c z +
        a * (z - 1) * regularizedGaussHGFun (a + 1) b c z = 0 :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => (c - a) * regularizedGaussHGFun (a - 1) b c z +
      (2 * a - c + (b - a) * z) * regularizedGaussHGFun a b c z +
      a * (z - 1) * regularizedGaussHGFun (a + 1) b c z)
    (fun _ => 0)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have h := contiguous_a (a := a) (b := b) hc hz
      simp only [regularizedGaussHGFun_eq_div_Gamma hc]
      field_simp
      linear_combination h) c

/-- 15.5.12 (`contiguous_ab`): `contiguous_shift_b` minus its `a ↔ b` swap. -/
theorem regularizedGaussHGFun_contiguous_ab (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (b - a) * regularizedGaussHGFun a b c z + a * regularizedGaussHGFun (a + 1) b c z -
      b * regularizedGaussHGFun a (b + 1) c z = 0 := by
  have ha := regularizedGaussHGFun_contiguous_shift_b a b c hz
  have hb := regularizedGaussHGFun_contiguous_shift_b b a c hz
  simp only [regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm b (a + 1) c,
    regularizedGaussHGFun_symm (b + 1) (a + 1) (c + 1)] at hb
  linear_combination b * ha - a * hb

/-- 15.5.13 (`contiguous_a_b_pred`): swapped `contiguous_a` plus `(z-1)` times
`contiguous_ab`. -/
theorem regularizedGaussHGFun_contiguous_a_b_pred (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (c - a - b) * regularizedGaussHGFun a b c z +
        a * (1 - z) * regularizedGaussHGFun (a + 1) b c z -
        (c - b) * regularizedGaussHGFun a (b - 1) c z = 0 := by
  have hab := regularizedGaussHGFun_contiguous_ab a b c hz
  have ha := regularizedGaussHGFun_contiguous_a b a c hz
  simp only [regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm (b - 1) a c,
    regularizedGaussHGFun_symm (b + 1) a c] at ha
  linear_combination -(ha + (z - 1) * hab)

/-- 15.5.21 (`deriv_contiguous_c_succ`) for the regularized function, valid for all parameters. -/
theorem regularizedGaussHGFun_contiguous_c_succ_deriv (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) * (a * b) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z =
      (c - a) * (c - b) * regularizedGaussHGFun a b (c + 1) z +
        (a + b - c) * regularizedGaussHGFun a b c z :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => (1 - z) * (a * b) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z)
    (fun c => (c - a) * (c - b) * regularizedGaussHGFun a b (c + 1) z +
      (a + b - c) * regularizedGaussHGFun a b c z)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hc1 := not_neg_nat_add_one hc
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have hΓ1 := Gamma_succ_of_not_neg_nat hc
      have hc0 := ne_zero_of_not_neg_nat hc
      have hd : c * deriv (₂F₁ a b c) z = a * b * ₂F₁ (a + 1) (b + 1) (c + 1) z := by
        rw [deriv_ordinaryHypergeometric hc hz]
        field_simp
      have h := deriv_contiguous_c_succ (a := a) (b := b) hc hz
      simp only [regularizedGaussHGFun_eq_div_Gamma hc,
        regularizedGaussHGFun_eq_div_Gamma hc1, hΓ1]
      field_simp [hΓ0, ne_zero_of_not_neg_nat hc]
      linear_combination h - (1 - z) * hd) c

/-- 15.5.14 (`contiguous_a_c_succ`): `-z` times `contiguous_c_succ_deriv` plus
`a(1-z)` times swapped `contiguous_shift_b`. -/
theorem regularizedGaussHGFun_contiguous_a_c_succ (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (a + (b - c) * z) * regularizedGaussHGFun a b c z -
        a * (1 - z) * regularizedGaussHGFun (a + 1) b c z +
        (c - a) * (c - b) * z * regularizedGaussHGFun a b (c + 1) z = 0 := by
  have hd := regularizedGaussHGFun_contiguous_c_succ_deriv a b c hz
  have hs := regularizedGaussHGFun_contiguous_shift_b b a c hz
  simp only [regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm b (a + 1) c,
    regularizedGaussHGFun_symm (b + 1) (a + 1) (c + 1)] at hs
  linear_combination -z * hd + a * (1 - z) * hs

/-- 15.5.15 (`contiguous_a_succ_c_pred`): `contiguous_c` at `c-1`. -/
theorem regularizedGaussHGFun_contiguous_a_succ_c_pred (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (c - a - 1) * regularizedGaussHGFun a b c z +
        a * regularizedGaussHGFun (a + 1) b c z -
        regularizedGaussHGFun a b (c - 1) z = 0 := by
  have h := regularizedGaussHGFun_contiguous_c a b (c - 1) hz
  simp only [sub_add_cancel] at h
  have h' :
      regularizedGaussHGFun a b (c - 1) z =
        (c - a - 1) * regularizedGaussHGFun a b c z +
          a * regularizedGaussHGFun (a + 1) b c z := by
    convert h using 2
    ring
  linear_combination -h'

/-- 15.5.16 (`contiguous_a_pred_c_succ`): swapped `contiguous_shift_b` and
`contiguous_c`. -/
theorem regularizedGaussHGFun_contiguous_a_pred_c_succ (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) * regularizedGaussHGFun a b c z - regularizedGaussHGFun (a - 1) b c z +
      (c - b) * z * regularizedGaussHGFun a b (c + 1) z = 0 := by
  have hs := regularizedGaussHGFun_contiguous_shift_b b (a - 1) c hz
  have hc' := regularizedGaussHGFun_contiguous_c b a c hz
  simp only [sub_add_cancel, regularizedGaussHGFun_symm b (a - 1) c,
    regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm (b + 1) a (c + 1)] at hs
  simp only [regularizedGaussHGFun_symm b a c, regularizedGaussHGFun_symm b a (c + 1),
    regularizedGaussHGFun_symm (b + 1) a (c + 1)] at hc'
  linear_combination -hs - z * hc'

/-- 15.5.17 (`contiguous_a_pred_c_pred`): `contiguous_a` plus `(1-z)` times
`contiguous_a_succ_c_pred`. -/
theorem regularizedGaussHGFun_contiguous_a_pred_c_pred (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (a - 1 + (b + 1 - c) * z) * regularizedGaussHGFun a b c z +
        (c - a) * regularizedGaussHGFun (a - 1) b c z -
        (1 - z) * regularizedGaussHGFun a b (c - 1) z = 0 := by
  have h₁ := regularizedGaussHGFun_contiguous_a a b c hz
  have h₂ := regularizedGaussHGFun_contiguous_a_succ_c_pred a b c hz
  linear_combination h₁ + (1 - z) * h₂

/-- 15.5.18 (`contiguous_c_three`): `contiguous_a_c_succ - contiguous_a + contiguous_a_pred_c_pred`. -/
theorem regularizedGaussHGFun_contiguous_c_three (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (z - 1) * regularizedGaussHGFun a b (c - 1) z +
        (c - 1 - (2 * c - a - b - 1) * z) * regularizedGaussHGFun a b c z +
        (c - a) * (c - b) * z * regularizedGaussHGFun a b (c + 1) z = 0 := by
  have h₁ := regularizedGaussHGFun_contiguous_a_c_succ a b c hz
  have h₂ := regularizedGaussHGFun_contiguous_a a b c hz
  have h₃ := regularizedGaussHGFun_contiguous_a_pred_c_pred a b c hz
  linear_combination h₁ - h₂ + h₃

/-- 15.5.19 (`contiguous_diagonal`) for the regularized function, valid for all parameters. -/
theorem regularizedGaussHGFun_contiguous_diagonal (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) * (a + 1) * (b + 1) * regularizedGaussHGFun (a + 2) (b + 2) (c + 2) z +
        (c - (a + b + 1) * z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z -
        regularizedGaussHGFun a b c z = 0 :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => z * (1 - z) * (a + 1) * (b + 1) *
        regularizedGaussHGFun (a + 2) (b + 2) (c + 2) z +
      (c - (a + b + 1) * z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z -
      regularizedGaussHGFun a b c z)
    (fun _ => 0)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hc1 := not_neg_nat_add_one hc
      have hc2 : ∀ k : ℕ, c + 2 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hc 2
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have hΓ1 := Gamma_succ_of_not_neg_nat hc
      have hΓ2 : Gamma (c + 2) = (c + 1) * Gamma (c + 1) := by
        simpa [show c + 1 + 1 = c + 2 by ring] using Gamma_succ_of_not_neg_nat hc1
      have h := contiguous_diagonal (a := a) (b := b) hc hz
      simp only [regularizedGaussHGFun_eq_div_Gamma hc,
        regularizedGaussHGFun_eq_div_Gamma hc1, regularizedGaussHGFun_eq_div_Gamma hc2,
        hΓ2, hΓ1]
      field_simp [hΓ0, ne_zero_of_not_neg_nat hc, ne_zero_of_not_neg_nat hc1]
      linear_combination h) c

/-! ### Regularized Euler and Pfaff transformations (all parameters) -/

/-- Euler's transformation 15.8.1 for the regularized function, valid for all parameters:
`𝐅(a,b;c;z) = (1-z)^(c-a-b) 𝐅(c-a,c-b;c;z)`. -/
theorem regularizedGaussHGFun_euler (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 - z) ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b) c z := by
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  -- step 1: continuation in `b`, for `0 < Re c`
  have step1 : ∀ c : ℂ, 0 < c.re → ∀ b : ℂ, regularizedGaussHGFun a b c z =
      (1 - z) ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b) c z := by
    intro c hc b
    have hcpole : ∀ k : ℕ, c ≠ -(k : ℂ) := not_neg_nat_of_re_pos hc
    have hf : AnalyticOnNhd ℂ (fun b => regularizedGaussHGFun a b c z) univ :=
      analyticOnNhd_regularizedGaussHGFun_b a c hz
    have hg : AnalyticOnNhd ℂ (fun b => (1 - z) ^ (c - a - b) *
        regularizedGaussHGFun (c - a) (c - b) c z) univ := by
      intro b _
      have hd : Differentiable ℂ (fun b => (1 - z) ^ (c - a - b) *
          regularizedGaussHGFun (c - a) (c - b) c z) :=
        ((differentiable_const _).sub differentiable_id |>.const_cpow (Or.inl h1z)).mul
          (differentiable_regularizedGaussHGFun_comp (differentiable_const _)
            ((differentiable_const _).sub differentiable_id) (differentiable_const _) hz)
      exact hd.analyticAt b
    have hopen : IsOpen {b : ℂ | 0 < b.re ∧ b.re < c.re} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hne : ({b : ℂ | 0 < b.re ∧ b.re < c.re} : Set ℂ).Nonempty := ⟨c / 2, by
      simp only [Set.mem_ofPred_eq, Complex.div_ofNat_re]
      constructor <;> linarith⟩
    have key := eq_of_analyticOnNhd_univ_of_eqOn hf hg hopen hne fun b hb => by
      obtain ⟨hb0, hbc⟩ := hb
      have hcb : 0 < (c - b).re := by simp only [Complex.sub_re]; linarith
      rw [regularizedGaussHGFun_eq_div_Gamma hcpole, regularizedGaussHGFun_eq_div_Gamma hcpole,
        euler_transformation hb0 hcb hz]
      ring
    exact congrFun key b
  -- step 2: continuation in `c`
  have hf : AnalyticOnNhd ℂ (fun c => regularizedGaussHGFun a b c z) univ :=
    analyticOnNhd_regularizedGaussHGFun_c a b hz
  have hg : AnalyticOnNhd ℂ (fun c => (1 - z) ^ (c - a - b) *
      regularizedGaussHGFun (c - a) (c - b) c z) univ := by
    intro c _
    have hd : Differentiable ℂ (fun c => (1 - z) ^ (c - a - b) *
        regularizedGaussHGFun (c - a) (c - b) c z) :=
      ((differentiable_id.sub (differentiable_const _)).sub (differentiable_const _)
        |>.const_cpow (Or.inl h1z)).mul
        (differentiable_regularizedGaussHGFun_comp (differentiable_id.sub (differentiable_const _))
          (differentiable_id.sub (differentiable_const _)) differentiable_id hz)
    exact hd.analyticAt c
  exact congrFun (eq_of_eqOn_re_pos hf hg fun c hc => step1 c hc b) c

/-- Pfaff's transformation 15.8.1 for the regularized function, valid for all parameters:
`𝐅(a,b;c;z) = (1-z)^(-a) 𝐅(a,c-b;c;z/(z-1))`. -/
theorem regularizedGaussHGFun_pfaff (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (hzt : ‖z / (z - 1)‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 - z) ^ (-a) * regularizedGaussHGFun a (c - b) c (z / (z - 1)) := by
  have step1 : ∀ c : ℂ, 0 < c.re → ∀ b : ℂ, regularizedGaussHGFun a b c z =
      (1 - z) ^ (-a) * regularizedGaussHGFun a (c - b) c (z / (z - 1)) := by
    intro c hc b
    have hcpole : ∀ k : ℕ, c ≠ -(k : ℂ) := not_neg_nat_of_re_pos hc
    have hf : AnalyticOnNhd ℂ (fun b => regularizedGaussHGFun a b c z) univ :=
      analyticOnNhd_regularizedGaussHGFun_b a c hz
    have hg : AnalyticOnNhd ℂ (fun b => (1 - z) ^ (-a) *
        regularizedGaussHGFun a (c - b) c (z / (z - 1))) univ := by
      intro b _
      have hd : Differentiable ℂ (fun b => (1 - z) ^ (-a) *
          regularizedGaussHGFun a (c - b) c (z / (z - 1))) :=
        (differentiable_const _).mul
          (differentiable_regularizedGaussHGFun_comp (differentiable_const _)
            ((differentiable_const _).sub differentiable_id) (differentiable_const _) hzt)
      exact hd.analyticAt b
    have hopen : IsOpen {b : ℂ | 0 < b.re ∧ b.re < c.re} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hne : ({b : ℂ | 0 < b.re ∧ b.re < c.re} : Set ℂ).Nonempty := ⟨c / 2, by
      simp only [Set.mem_ofPred_eq, Complex.div_ofNat_re]
      constructor <;> linarith⟩
    have key := eq_of_analyticOnNhd_univ_of_eqOn hf hg hopen hne fun b hb => by
      obtain ⟨hb0, hbc⟩ := hb
      have hcb : 0 < (c - b).re := by simp only [Complex.sub_re]; linarith
      rw [regularizedGaussHGFun_eq_div_Gamma hcpole, regularizedGaussHGFun_eq_div_Gamma hcpole,
        pfaff_transformation hb0 hcb hz hzt]
      ring
    exact congrFun key b
  have hf : AnalyticOnNhd ℂ (fun c => regularizedGaussHGFun a b c z) univ :=
    analyticOnNhd_regularizedGaussHGFun_c a b hz
  have hg : AnalyticOnNhd ℂ (fun c => (1 - z) ^ (-a) *
      regularizedGaussHGFun a (c - b) c (z / (z - 1))) univ := by
    intro c _
    have hd : Differentiable ℂ (fun c => (1 - z) ^ (-a) *
        regularizedGaussHGFun a (c - b) c (z / (z - 1))) :=
      (differentiable_const _).mul
        (differentiable_regularizedGaussHGFun_comp (differentiable_const _)
          (differentiable_id.sub (differentiable_const _)) differentiable_id hzt)
    exact hd.analyticAt c
  exact congrFun (eq_of_eqOn_re_pos hf hg fun c hc => step1 c hc b) c

/-- Euler's transformation 15.8.1 for `₂F₁`, with no hypothesis on `a`, `b`. -/
theorem euler_transformation_of_ne_neg_nat {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) {z : ℂ}
    (hz : ‖z‖ < 1) : ₂F₁ a b c z = (1 - z) ^ (c - a - b) * ₂F₁ (c - a) (c - b) c z := by
  have hΓ : Gamma c ≠ 0 := Gamma_ne_zero hc
  have h := regularizedGaussHGFun_euler a b c hz
  simp only [regularizedGaussHGFun_eq_div_Gamma hc] at h
  rw [div_eq_iff hΓ] at h
  rw [h]
  field_simp

/-- AAR Theorem 2.1.3: Gauss's asymptotic as `x → 1⁻`. By Euler's transformation,
`(1-x)^(a+b-c) F(a,b;c;x) = F(c-a,c-b;c;x)`, which tends to `F(c-a,c-b;c;1)` by Abel's
theorem; Gauss's summation theorem evaluates the limit. -/
@[dlmf 15.4.E23]
theorem _root_.tendsto_ordinaryHypergeometric_nhdsWithin_one {a b c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (h : (c - a - b).re < 0) :
    Tendsto (fun x : ℝ => (1 - x : ℂ) ^ (a + b - c) * ₂F₁ a b c (x : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (Gamma (a + b - c) * Gamma c / (Gamma a * Gamma b))) := by
  have h' : 0 < (c - (c - a) - (c - b)).re := by
    simp only [sub_re] at h ⊢
    linarith
  have hG := gauss_summation (a := c - a) (b := c - b) hc h'
  rw [show c - (c - a) - (c - b) = a + b - c by ring, sub_sub_cancel, sub_sub_cancel,
    ordinaryHypergeometric_one_eq_tsum] at hG
  have hs : Summable (gaussHGCoeff (c - a) (c - b) c) := by
    simpa using ordinaryHypergeometric_summable_of_mem_sphere (z := 1) (by simp) h'
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hs.hasSum.tendsto_sum_nat
  rw [tendsto_map'_iff, hG] at habel
  rw [show Gamma (a + b - c) * Gamma c = Gamma c * Gamma (a + b - c) by ring]
  apply habel.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with x hx
  have hx1 : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨hx.1, hx.2⟩
  have hx0 : (1 : ℂ) - x ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero]
    linarith [hx.2]
  rw [euler_transformation_of_ne_neg_nat hc hx1, ← mul_assoc, ← cpow_add _ _ hx0,
    show a + b - c + (c - a - b) = 0 by ring, cpow_zero, one_mul, ordinaryHypergeometric_eq_tsum]
  simp only [Function.comp_apply, smul_eq_mul]
  congr 1
  funext n
  simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Pfaff's transformation 15.8.1 for `₂F₁`, with no hypothesis on `a`, `b`. -/
theorem pfaff_transformation_of_ne_neg_nat {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) {z : ℂ}
    (hz : ‖z‖ < 1) (hzt : ‖z / (z - 1)‖ < 1) :
    ₂F₁ a b c z = (1 - z) ^ (-a) * ₂F₁ a (c - b) c (z / (z - 1)) := by
  have hΓ : Gamma c ≠ 0 := Gamma_ne_zero hc
  have h := regularizedGaussHGFun_pfaff a b c hz hzt
  simp only [regularizedGaussHGFun_eq_div_Gamma hc] at h
  rw [div_eq_iff hΓ] at h
  rw [h]
  field_simp

/-! ### Terminating series as functions of the denominator parameter -/

/-- `(c)_k ≠ 0` when `c` avoids `0, -1, …, -(k-1)`. -/
theorem poch_ne_zero_of_lt (c : ℂ) (k : ℕ) (hc : ∀ j : ℕ, j < k → c ≠ -(j : ℂ)) : poch c k ≠ 0 := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ]
    refine mul_ne_zero (ih fun j hj => hc j (by omega)) fun h => ?_
    exact hc k (by omega) (by linear_combination h)

/-- The terminating `₂F₁(-n, b; c; z)` is analytic in `c` off `{0, -1, …, -(n-1)}`. -/
theorem analyticOnNhd_gauss_neg_nat_param (n : ℕ) (b z : ℂ) :
    AnalyticOnNhd ℂ (fun c : ℂ => ₂F₁ (-(n : ℂ)) b c z) {c : ℂ | ∀ j : ℕ, j < n → c ≠ -(j : ℂ)} := by
  intro c hc
  have heq : (fun c : ℂ => ₂F₁ (-(n : ℂ)) b c z) = fun c => ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k * poch b k / (poch c k * k.factorial) * z ^ k := by
    funext c
    rw [ordinaryHypergeometric_eq_sum_neg_nat]
    rfl
  rw [heq]
  refine Finset.analyticAt_fun_sum (Finset.range (n + 1)) fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hden : poch c k * k.factorial ≠ 0 := mul_ne_zero
    (poch_ne_zero_of_lt c k fun j hj => hc j (lt_of_lt_of_le hj hk'))
    (Nat.cast_ne_zero.mpr k.factorial_ne_zero)
  have hpoch : AnalyticAt ℂ (fun c : ℂ => poch c k * k.factorial) c :=
    ((Polynomial.differentiable (ascPochhammer ℂ k)).analyticAt c).mul analyticAt_const
  exact (AnalyticAt.fun_div (f := fun _ : ℂ => poch (-(n : ℂ)) k * poch b k)
    (g := fun c : ℂ => poch c k * k.factorial) (x := c) analyticAt_const hpoch hden).mul
    analyticAt_const

/-- Gauss's contiguous relation in `a` for a terminating series, valid for every argument. -/
theorem contiguous_a_neg_nat {b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) (z : ℂ) :
    (c + (n + 1)) * ₂F₁ (-((n + 2 : ℕ) : ℂ)) b c z +
      (-(2 * (n + 1)) - c + (b + (n + 1)) * z) * ₂F₁ (-((n + 1 : ℕ) : ℂ)) b c z -
      (n + 1) * (z - 1) * ₂F₁ (-(n : ℂ)) b c z = 0 := by
  set F : ℂ → ℂ := fun z : ℂ => (c + (n + 1)) * ₂F₁ (-((n + 2 : ℕ) : ℂ)) b c z +
      (-(2 * (n + 1)) - c + (b + (n + 1)) * z) * ₂F₁ (-((n + 1 : ℕ) : ℂ)) b c z -
      (n + 1) * (z - 1) * ₂F₁ (-(n : ℂ)) b c z with hF
  have hpoly : ∀ m : ℕ, Differentiable ℂ (fun z : ℂ => ₂F₁ (-(m : ℂ)) b c z) := by
    intro m
    have : (fun z : ℂ => ₂F₁ (-(m : ℂ)) b c z) =
        fun z : ℂ => ∑ k ∈ Finset.range (m + 1), gaussHGCoeff (-(m : ℂ)) b c k * z ^ k := by
      funext z; exact ordinaryHypergeometric_eq_sum_neg_nat m b c z
    rw [this]
    fun_prop
  have hdiff : Differentiable ℂ F := by
    have h2 := hpoly (n + 2); have h1 := hpoly (n + 1); have h0 := hpoly n
    fun_prop
  have hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, F z = 0 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    have h := contiguous_a (a := -((n + 1 : ℕ) : ℂ)) (b := b) hc hz
    rw [show -((n + 1 : ℕ) : ℂ) - 1 = -((n + 2 : ℕ) : ℂ) by push_cast; ring,
      show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at h
    simp only [hF]
    push_cast at h ⊢
    linear_combination h
  have han : AnalyticOnNhd ℂ F Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff
  have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ 0)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 one_pos) hball)
  simpa [hF] using hzero (Set.mem_univ z)

end DLMF.Hypergeometric
