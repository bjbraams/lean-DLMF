/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Calculus
public import DLMFMathlib.Analysis.Complex.GeometricNewtonSeries
public import DLMFMathlib.Analysis.Complex.SeparatingContour
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import DLMF.QHypergeometric.BasicSummations.OnePhiZero
public import DLMF.QSeries.RamanujanPsi
public import DLMF.QSeries.Saalschutz
public import DLMF.QHypergeometric.Transformations

/-!
# Heine's transformations and related two-phi-one identities (DLMF 17.6.5–17.6.29)

The q-analogues of Kummer's theorem, Heine's three transformations, Fine's expansions,
nonterminating and mixed-base sums, connection and contiguous relations, the q-differential
equation, and the Jackson-integral and Mellin–Barnes representations of `₂φ₁`. Cancelled
product forms retain exceptional upper parameters whenever the left series is regular.

## Main results

* `qPochhammerInf_mul_qPochhammerInf_neg`: `(x;q)_∞ (-x;q)_∞ = (x²;q²)_∞`.
* `q_bailey_daum`: 17.6.5.
* `heine_first`, `heine_second`, `heine_third`: 17.6.6–17.6.8.
* `qPochhammerInf_split_sq`: `(a;q)_∞ = (a;q²)_∞ (aq;q²)_∞`.
* `heine_contiguous_17` … `heine_contiguous_24`: the contiguous relations 17.6.17–17.6.24.
* `heine_weighted_qDerivative`: 17.6.26.
* `exists_norm_inv_qPochhammer_self_le`: `1/(q;q)_n` is bounded for `|q| < 1`.
* `heine_qDifferentialEquation`: 17.6.27.
* `heine_jackson_integral`, `heine_mellin_barnes`: 17.6.28 and 17.6.29.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- The Jackson expression in Heine's integral, kept separate from its removable parameter values.
-/
def qHeineJacksonValue (q : ℝ) (a b c z : ℂ) : ℂ :=
  qGamma q c/(qGamma q b*qGamma q (c-b))*
    jacksonIntegral q 1 (fun t =>
        t^(b-1)*qPochhammerOrder (t*q) q (c-b-1)/qPochhammerOrder (z*t) q a)
/-- The integrand in the Mellin–Barnes representation of two-phi-one. -/
def qHeineBarnesKernel (a b c q z s : ℂ) : ℂ :=
  qPochhammerListInf [q^(1+s),c*q^s] q/qPochhammerListInf [a*q^s,b*q^s] q*
    π*(-z)^s/Complex.sin (π*s)
/-- The denominator-pole set on the logarithmic q-plane in the Barnes representation. -/
def qHeineBarnesLeft (a b q : ℂ) : Set ℂ :=
  {s | qPochhammerListInf [a*q^s,b*q^s] q=0}
/-- The nonnegative-integer poles belonging to the right side of the Barnes contour. -/
def qHeineBarnesRight : Set ℂ := Set.range (fun n : ℕ => (n:ℂ))
/-- `(x;q)_∞ (-x;q)_∞ = (x²;q²)_∞` for `|q| < 1`. -/
theorem qPochhammerInf_mul_qPochhammerInf_neg {x q : ℂ} (hq : ‖q‖<1) :
    qPochhammerInf x q*qPochhammerInf (-x) q = qPochhammerInf (x^2) (q^2) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  refine tendsto_nhds_unique ((tendsto_qPochhammer hq).mul (tendsto_qPochhammer hq)) ?_
  exact (tendsto_qPochhammer hQ).congr fun n => qPochhammer_squared x q n

/-- `(a;q)_∞ = (a;q²)_∞ (aq;q²)_∞` for `|q| < 1`. -/
theorem qPochhammerInf_split_sq {a q : ℂ} (hq : ‖q‖<1) :
    qPochhammerInf a q = qPochhammerInf a (q^2)*qPochhammerInf (a*q) (q^2) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have h1 : Tendsto (fun n : ℕ => qPochhammer a q (2*n)) atTop (𝓝 (qPochhammerInf a q)) :=
    (tendsto_qPochhammer hq).comp
      (tendsto_atTop_mono (fun n => by simp only [id]; omega) tendsto_id)
  have h2 : Tendsto (fun n : ℕ => qPochhammer a q (2*n)) atTop
      (𝓝 (qPochhammerInf a (q^2)*qPochhammerInf (a*q) (q^2))) := by
    refine ((tendsto_qPochhammer hQ).mul (tendsto_qPochhammer hQ)).congr fun n => ?_
    simp [qPochhammer_even, qPochhammerList]
  exact tendsto_nhds_unique h1 h2

/-- `a ↦ (αa;q)_k` is entire. -/
private lemma differentiable_qPochhammer_mul (q α : ℂ) (k : ℕ) :
    Differentiable ℂ fun a : ℂ => qPochhammer (α*a) q k := by
  induction k with
  | zero => simp [qPochhammer_zero]
  | succ k ih =>
    simp only [qPochhammer_succ]
    exact ih.mul ((differentiable_const _).sub ((differentiable_const _).mul
      differentiable_id |>.mul (differentiable_const _)))

/-- The Bailey–Daum q-Kummer sum `2φ1(a,b;aq/b;q,-q/b)` as a product of infinite q-shifted
factorials (DLMF 17.6.E5). -/
@[dlmf 17.6.E5]
theorem q_bailey_daum {a b q : ℂ} (hq : ‖q‖<1) (hb : ‖q‖<‖b‖)
    (hc : QDenominatorRegular [a*q/b] q) :
    qPhi [a,b] [a*q/b] q (-q/b)=qPochhammerInf (-q) q*
      qPochhammerListInf [a*q,a*q^2/b^2] (q^2)/qPochhammerListInf [-q/b,a*q/b] q := by
  have hb0 : b≠0 := by rintro rfl; simp at hb; exact absurd hb (not_lt.mpr (norm_nonneg q))
  set r := -q/b with hr
  have hr1 : ‖r‖<1 := by
    rw [hr, norm_div, norm_neg, div_lt_one (norm_pos_iff.mpr hb0)]; exact hb
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hrI : qPochhammerInf r q≠0 := qPochhammerInf_ne_zero_of_norm_lt_one hr1 hq
  have hqb : ‖q/b‖<1 := by rw [norm_div, div_lt_one (norm_pos_iff.mpr hb0)]; exact hb
  -- the cleared series and product, as functions of `a`
  set t : ℕ → ℂ := fun n => qPochhammer b q n/qPochhammer q q n*r^n
  set F : ℂ → ℂ := fun x => ∑' n, qPochhammer (1*x) q n*(t n*qPochhammerInf (x*(q/b*q^n)) q)
  set G : ℂ → ℂ := fun x => qPochhammerInf (-q) q*(qPochhammerInf (x*q) (q^2)*
    qPochhammerInf (x*q^2/b^2) (q^2))/qPochhammerInf r q
  have ht : Summable fun n => ‖t n‖ := by
    have hs := (summable_q_binomial_series (a := b) hq hr1).norm
    exact hs
  have hFd : Differentiable ℂ F := by
    intro x0
    set R := ‖x0‖+1
    have hd : DifferentiableOn ℂ F (Metric.ball 0 R) := by
      refine differentiableOn_tsum_of_summable_norm
        (u := fun n => Real.exp (R/(1-‖q‖))*(‖t n‖*Real.exp (R/(1-‖q‖))))
        ((ht.mul_right _).mul_left _) ?_ Metric.isOpen_ball ?_
      · intro n
        exact ((differentiable_qPochhammer_mul q 1 n).mul
          (((differentiable_qPochhammerInf_left hq).comp
          (differentiable_id.mul_const _)).const_mul _)).differentiableOn
      · intro n x hx
        have hxR : ‖x‖ ≤ R := by simpa using (Metric.mem_ball.mp hx).le
        rw [norm_mul, norm_mul]
        have h1 : ‖qPochhammer (1*x) q n‖ ≤ Real.exp (R/(1-‖q‖)) :=
          (norm_qPochhammer_le_exp hq n).trans (Real.exp_le_exp.mpr
            (div_le_div_of_nonneg_right (by simpa using hxR) (by linarith [norm_nonneg q])))
        have h2 : ‖qPochhammerInf (x*(q/b*q^n)) q‖ ≤ Real.exp (R/(1-‖q‖)) := by
          refine (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr
            (div_le_div_of_nonneg_right ?_ (by linarith [norm_nonneg q])))
          rw [norm_mul, norm_mul, norm_pow]
          calc ‖x‖*(‖q/b‖*‖q‖^n) ≤ ‖x‖*1 := by
                gcongr
                exact (mul_le_of_le_one_right (norm_nonneg _)
                  (pow_le_one₀ (norm_nonneg _) hq.le)).trans hqb.le
            _ ≤ R := by simpa using hxR
        gcongr
    exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))
  have hGd : Differentiable ℂ G := by
    have hP := differentiable_qPochhammerInf_left hQ
    exact ((((hP.comp (differentiable_id.mul_const _)).mul
      (hP.comp ((differentiable_id.mul_const _).div_const _))).const_mul _)).div_const _
  -- `F = (aq/b;q)_∞ · φ` wherever the lower parameter is regular
  have hFphi : ∀ x : ℂ, QDenominatorRegular [x*q/b] q →
      F x = qPochhammerInf (x*q/b) q*qPhi [x,b] [x*q/b] q r := by
    intro x hx
    rw [qPhi_eq_basicHG (by simp), basicHG, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul, t]
    have hxn := qPochhammer_ne_zero_of_qDenominatorRegular hq hx n
    have hqn := qPochhammer_self_ne_zero hq n
    rw [qPochhammerInf_mul_qPochhammer (a := x*q/b) hq n,
      show x*q/b*q^n = x*(q/b*q^n) by ring]
    field_simp
  -- the identity for `0 < |a| < 1`
  have key : ∀ x : ℂ, x ∈ Metric.ball (1/2 : ℂ) (1/2) → F x = G x := by
    intro x hx
    have hx0 : x≠0 := by rintro rfl; norm_num [Metric.mem_ball] at hx
    have hx1 : ‖x‖<1 := by
      have := norm_sub_norm_le x (1/2)
      rw [Metric.mem_ball, dist_eq_norm] at hx
      norm_num at this
      linarith
    have hxq : ‖x*q/b‖<1 := by
      rw [mul_div_assoc, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx1.le).trans_lt hqb
    have hreg : QDenominatorRegular [x*q/b] q := by
      intro y hy n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      exact fun h => one_sub_mul_pow_ne_zero_of_norm hxq hq n (by rw [h]; ring)
    rw [hFphi x hreg, qPhi_eq_basicHG (by simp), basicHG_swap,
      heine_transformation hq hr1 hx1 hx0 (fun k h => hreg _ (by simp) k h) (fun k h =>
        one_sub_mul_pow_ne_zero_of_norm (w := -q) (by simpa using hq) hq k
          (by rw [show -q = b*r by rw [hr]; field_simp, h]; ring))]
    rw [show b*r = -q by rw [hr]; field_simp, show x*q/b/x = q/b by field_simp]
    have hsum : basicHG [q/b, r] [-q] q x = qPochhammerInf (x*q^2/b^2) (q^2)/
        qPochhammerInf x (q^2) := by
      rw [show x*q^2/b^2 = (q/b)^2*x by ring, q_binomial_theorem hQ hx1]
      simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      refine tsum_congr fun n => ?_
      rw [qPochhammer_squared, qPochhammer_squared, hr]
      ring_nf
    rw [hsum, qPochhammerInf_split_sq (a := x) hq]
    have h1 : qPochhammerInf x (q^2) ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hx1 hQ
    have h2 : qPochhammerInf (x*q/b) q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hxq hq
    simp only [G]
    field_simp
  have hev : F =ᶠ[𝓝 (1/2 : ℂ)] G := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0:ℝ)<1/2))]
      with x hx using key x hx
  have hFG := AnalyticOnNhd.eq_of_eventuallyEq (fun x _ => hFd.analyticAt x)
    (fun x _ => hGd.analyticAt x) hev
  have hD : qPochhammerInf (a*q/b) q ≠ 0 :=
    qPochhammerInf_ne_zero hq fun n h => hc _ (by simp) n (sub_eq_zero.mp h).symm
  have := hFphi a hc
  rw [hFG] at this
  rw [eq_div_iff (by simp [qPochhammerListInf, hrI, hD]), mul_comm]
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  have hG : qPochhammerInf r q*G a = qPochhammerInf (-q) q*(qPochhammerInf (a*q) (q^2)*
      qPochhammerInf (a*q^2/b^2) (q^2)) := by
    simp only [G]; field_simp
  linear_combination (-qPochhammerInf r q)*this+hG

/-- Heine's first transformation of `2φ1(a,b;c;q,z)` into a multiple of `2φ1(c/b,z;az;q,b)` (DLMF
17.6.E6). -/
@[dlmf 17.6.E6]
theorem heine_first {a b c q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (hb : ‖b‖<1) (hb0 : b≠0)
    (hc : QDenominatorRegular [c,a*z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [b,a*z] q/qPochhammerListInf [c,z] q*
      qPhi [c/b,z] [a*z] q b := by
  rw [qPhi_eq_basicHG (by simp),qPhi_eq_basicHG (by simp)]
  simpa [qPochhammerListInf] using DLMF.QSeries.heine_transformation hq hz hb hb0
    (hc c (by simp)) (hc (a*z) (by simp))


/-- `(q;q)_∞ ≠ 0` for `|q| < 1`. -/
private lemma qPochhammerInf_self_ne_zero' {q : ℂ} (hq : ‖q‖<1) : qPochhammerInf q q≠0 :=
  qPochhammerInf_ne_zero hq fun n => by
    simpa [pow_succ, mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n

/-- Absolute convergence of `₂φ₁`-type terms with a regular lower parameter. -/
private lemma summable_norm_twoOne {α β γ q w : ℂ} (hq : ‖q‖<1) (hγ : qPochhammerInf γ q≠0)
    (hw : ‖w‖<1) :
    Summable fun k : ℕ => ‖qPochhammer α q k*qPochhammer β q k/
      (qPochhammer γ q k*qPochhammer q q k)*w^k‖ := by
  obtain ⟨C1,hC1⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq hγ
  obtain ⟨C2,hC2⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_self_ne_zero' hq)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left
      (Real.exp (‖α‖/(1-‖q‖))*Real.exp (‖β‖/(1-‖q‖))*C1*C2))
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
  have h1 := norm_qPochhammer_le_exp (w := α) hq k
  have h2 := norm_qPochhammer_le_exp (w := β) hq k
  have h3 := hC1 k
  have h4 := hC2 k
  have h0 : 0 ≤ C1 := (norm_nonneg _).trans h3
  rw [show ‖qPochhammer α q k‖*‖qPochhammer β q k‖*(‖(qPochhammer γ q k)⁻¹‖*
      ‖(qPochhammer q q k)⁻¹‖)*‖w‖^k = ‖qPochhammer α q k‖*‖qPochhammer β q k‖*
      ‖(qPochhammer γ q k)⁻¹‖*‖(qPochhammer q q k)⁻¹‖*‖w‖^k by ring]
  gcongr

/-- Heine's third transformation, proved by the `q`-binomial theorem, a Cauchy product and the
`q`-Pfaff–Saalschütz sum. -/
private theorem heine_third_aux {a b c q z : ℂ} (ha : a≠0) (hb : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc0 : c≠0) (habz : ‖a*b*z‖<‖c‖) (hc : QDenominatorRegular [c] q) :
    qPhi [a,b] [c] q z=qPochhammerInf (a*b*z/c) q/qPochhammerInf z q*
      qPhi [c/a,c/b] [c] q (a*b*z/c) := by
  set x := a*b/c with hx
  have hw : ‖x*z‖<1 := by
    rw [hx, div_mul_eq_mul_div, norm_div, div_lt_one (norm_pos_iff.mpr hc0)]; exact habz
  have hcn : ∀ n, qPochhammer c q n≠0 := qPochhammer_ne_zero_of_qDenominatorRegular hq hc
  have hcI : qPochhammerInf c q≠0 :=
    qPochhammerInf_ne_zero hq fun n h => hc c (by simp) n (sub_eq_zero.mp h).symm
  rw [qPhi_eq_basicHG (by simp), qPhi_eq_basicHG (by simp)]
  simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [show a*b*z/c = x*z by rw [hx]; ring, q_binomial_theorem hq hz]
  have hf := summable_norm_twoOne (α := c/a) (β := c/b) hq hcI hw
  have hg : Summable fun m : ℕ => ‖qPochhammer x q m/qPochhammer q q m*z^m‖ := by
    have := summable_norm_twoOne (α := x) (β := 0) (γ := 0) hq (by simp) hz
    refine this.congr fun m => ?_
    simp [qPochhammer_zero_param]
  rw [mul_comm, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  have hS := sum_saalschutz_div q x (c/a) (c/b) n (fun m _ => qPochhammer_self_ne_zero hq m)
    (by rw [show x*(c/a)*(c/b) = c by rw [hx]; field_simp]; exact hcn n)
  rw [show x*(c/a)*(c/b) = c by rw [hx]; field_simp, show x*(c/a) = b by rw [hx]; field_simp,
    show x*(c/b) = a by rw [hx]; field_simp] at hS
  have hS' := congrArg (· * z^n) hS
  rw [show qPochhammer a q n*qPochhammer b q n/(qPochhammer c q n*qPochhammer q q n)*z^n =
    qPochhammer b q n*qPochhammer a q n/(qPochhammer q q n*qPochhammer c q n)*z^n by ring,
    ← hS', sum_mul]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := by simpa [Nat.lt_succ_iff] using hm
  have hz' : z^n = z^m*z^(n-m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hz', mul_pow]
  have := hcn m
  have := qPochhammer_self_ne_zero hq m
  have := qPochhammer_self_ne_zero hq (n-m)
  field_simp


/-- A series `∑ (αa;q)_k t_k` with absolutely summable `t` is entire in `a`. -/
private lemma differentiable_tsum_qPochhammer_mul {q α : ℂ} (hq : ‖q‖<1) {t : ℕ → ℂ}
    (ht : Summable fun k => ‖t k‖) :
    Differentiable ℂ fun a => ∑' k, qPochhammer (α*a) q k*t k := by
  intro a0
  set R := ‖a0‖+1
  have hd : DifferentiableOn ℂ (fun a => ∑' k, qPochhammer (α*a) q k*t k) (Metric.ball 0 R) := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun k => Real.exp (‖α‖*R/(1-‖q‖))*‖t k‖) (ht.mul_left _) ?_ Metric.isOpen_ball ?_
    · exact fun k => ((differentiable_qPochhammer_mul q α k).mul_const _).differentiableOn
    · intro k a ha
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ((norm_qPochhammer_le_exp hq k).trans ?_) (norm_nonneg _)
      refine Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ (by linarith [norm_nonneg q]))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using (Metric.mem_ball.mp ha).le) (norm_nonneg _)
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))

/-- Symmetry of `₂φ₁` in its upper parameters. -/
private lemma qPhi_two_one_swap (a b c q z : ℂ) : qPhi [a,b] [c] q z=qPhi [b,a] [c] q z := by
  rw [qPhi_eq_basicHG (by simp), qPhi_eq_basicHG (by simp), basicHG_swap]

/-- Heine's second transformation of `2φ1(a,b;c;q,z)` into a multiple of `2φ1(abz/c,b;bz;q,c/b)`
(DLMF 17.6.E7). -/
@[dlmf 17.6.E7]
theorem heine_second {a b c q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (hc0 : c≠0) (hcb : ‖c‖<‖b‖)
    (hc : QDenominatorRegular [c,b*z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [c/b,b*z] q/qPochhammerListInf [c,z] q*
      qPhi [a*b*z/c,b] [b*z] q (c/b) := by
  have hb0 : b≠0 := by rintro rfl; simp at hcb; exact absurd hcb (not_lt.mpr (norm_nonneg c))
  have hcb' : ‖c/b‖<1 := by rw [norm_div, div_lt_one (norm_pos_iff.mpr hb0)]; exact hcb
  have hcI : qPochhammerInf c q≠0 :=
    qPochhammerInf_ne_zero hq fun n h => hc c (by simp) n (sub_eq_zero.mp h).symm
  have hbzI : qPochhammerInf (b*z) q≠0 :=
    qPochhammerInf_ne_zero hq fun n h => hc (b*z) (by simp) n (sub_eq_zero.mp h).symm
  have hcbI : qPochhammerInf (c/b) q≠0 := qPochhammerInf_ne_zero_of_norm_lt_one hcb' hq
  have hzI : qPochhammerInf z q≠0 := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  by_cases hz0 : z=0
  · subst hz0
    rw [qPhi_eq_basicHG (by simp), qPhi_eq_basicHG (by simp)]
    simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      qPochhammerListInf, mul_zero, zero_div, qPochhammer_zero_param]
    have h0 : ∑' n : ℕ, qPochhammer a q n*qPochhammer b q n/(qPochhammer c q n*qPochhammer q q n)*
        (0:ℂ)^n = 1 := by
      rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]; simp [qPochhammer_zero]
    have h1 := q_binomial_theorem (a := b) hq hcb'
    rw [show b*(c/b) = c by field_simp] at h1
    rw [h0]
    simp only [one_mul]
    rw [← h1, qPochhammerInf_zero]
    field_simp
  -- analytic continuation in `a`
  have hbz0 : b*z≠0 := mul_ne_zero hb0 hz0
  set R := ‖c‖/‖b*z‖ with hR
  have hR0 : 0<R := div_pos (norm_pos_iff.mpr hc0) (norm_pos_iff.mpr hbz0)
  set t1 : ℕ → ℂ := fun k => qPochhammer b q k/(qPochhammer c q k*qPochhammer q q k)*z^k
  set t2 : ℕ → ℂ := fun k => qPochhammer b q k/(qPochhammer (b*z) q k*qPochhammer q q k)*(c/b)^k
  have ht1 : Summable fun k => ‖t1 k‖ :=
    (summable_norm_twoOne (α := 0) (β := b) hq hcI hz).congr fun k => by
      simp [t1, qPochhammer_zero_param]
  have ht2 : Summable fun k => ‖t2 k‖ :=
    (summable_norm_twoOne (α := 0) (β := b) hq hbzI hcb').congr fun k => by
      simp [t2, qPochhammer_zero_param]
  set K := qPochhammerListInf [c/b,b*z] q/qPochhammerListInf [c,z] q
  have hF : ∀ a : ℂ, qPhi [a,b] [c] q z = ∑' k, qPochhammer (1*a) q k*t1 k := by
    intro a
    rw [qPhi_eq_basicHG (by simp)]
    simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      one_mul, t1]
    exact tsum_congr fun k => by ring
  have hG : ∀ a : ℂ, K*qPhi [a*b*z/c,b] [b*z] q (c/b) =
      K*∑' k, qPochhammer ((b*z/c)*a) q k*t2 k := by
    intro a
    rw [qPhi_eq_basicHG (by simp)]
    simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, t2]
    congr 1
    exact tsum_congr fun k => by rw [show b*z/c*a = a*b*z/c by ring]; ring
  have dF := differentiable_tsum_qPochhammer_mul (α := 1) hq ht1
  have dG := (differentiable_tsum_qPochhammer_mul (α := b*z/c) hq ht2).const_mul K
  set a0 : ℂ := ((R/2 : ℝ) : ℂ)
  have key : ∀ a : ℂ, a ∈ Metric.ball a0 (R/2) →
      qPhi [a,b] [c] q z = K*qPhi [a*b*z/c,b] [b*z] q (c/b) := by
    intro a ha
    have ha0 : a≠0 := by
      rintro rfl
      simp [a0, Metric.mem_ball, abs_of_pos hR0] at ha
    have haR : ‖a‖<R := by
      have h1 := norm_sub_norm_le a a0
      have h2 : ‖a0‖ = R/2 := by simp [a0, abs_of_pos hR0]
      rw [Metric.mem_ball, dist_eq_norm] at ha
      linarith
    have habz : ‖a*b*z‖<‖c‖ := by
      rw [mul_assoc, norm_mul]
      have := (lt_div_iff₀ (norm_pos_iff.mpr hbz0)).mp haR
      exact this
    have habz' : ‖a*b*z/c‖<1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.mpr hc0)]; exact habz
    have habz0 : a*b*z/c≠0 := by simp [ha0, hb0, hz0, hc0]
    rw [heine_third_aux ha0 hb0 hq hz hc0 habz (fun x hx => hc x (by simp_all))]
    rw [qPhi_two_one_swap (a*b*z/c) b, heine_first hq hcb' habz' habz0 (by
      intro x hx n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hc (b*z) (by simp) n
      · rw [show b*(c/b) = c by field_simp]; exact hc c (by simp) n)]
    rw [show b*z/(a*b*z/c) = c/a by field_simp, show b*(c/b) = c by field_simp]
    simp only [K, qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    field_simp
  have hev : (fun a => qPhi [a,b] [c] q z) =ᶠ[𝓝 a0]
      (fun a => K*qPhi [a*b*z/c,b] [b*z] q (c/b)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith : 0<R/2))]
      with a ha using key a ha
  have hev' : (fun a => ∑' k, qPochhammer (1*a) q k*t1 k) =ᶠ[𝓝 a0]
      (fun a => K*∑' k, qPochhammer ((b*z/c)*a) q k*t2 k) := by
    filter_upwards [hev] with a ha
    rw [← hF, ha, hG]
  have := AnalyticOnNhd.eq_of_eventuallyEq (fun x _ => dF.analyticAt x)
    (fun x _ => dG.analyticAt x) hev'
  rw [hF, congrFun this a, ← hG]

/-- Heine's third transformation: `2φ1(a,b;c;q,z) = (abz/c;q)_∞/(z;q)_∞ 2φ1(c/a,c/b;c;q,abz/c)`
(DLMF 17.6.E8). -/
@[dlmf 17.6.E8]
theorem heine_third {a b c q z : ℂ} (ha : a≠0) (hb : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc0 : c≠0) (habz : ‖a*b*z‖<‖c‖) (hc : QDenominatorRegular [c] q) :
    qPhi [a,b] [c] q z=qPochhammerInf (a*b*z/c) q/qPochhammerInf z q*
      qPhi [c/a,c/b] [c] q (a*b*z/c) :=
  heine_third_aux ha hb hq hz hc0 habz hc

/-- Fine's first expansion of `2φ1(q,aq;bq;q,z)` (DLMF 17.6.E9). -/
@[dlmf 17.6.E9]
theorem heine_fine_expansion {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q,a*z*q^2/b,a*q/b] q) :
    qPhi [q,a*q] [b*q] q z= -(1-b)*(a*q/b)/(1-a*q/b)*
      (∑' n : ℕ, qPochhammerList [a*q,a*z*q/b] q n*q^n/qPochhammer (a*z*q^2/b) q n)+
      qPochhammerListInf [a*q,a*z*q/b] q/qPochhammerInf (a*q/b) q*qPhi [q,0] [b*q] q z := by
  sorry

/-- Fine's second expansion: `(1-z) 2φ1(q,aq;bq;q,z)` as a series in `(b/a;q)_n (-az)^n
q^(n(n+1)/2)` (DLMF 17.6.E10). -/
@[dlmf 17.6.E10]
theorem heine_fine_expansion_second {a b q z : ℂ} (ha : a≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q] q) :
    (1-z)*qPhi [q,a*q] [b*q] q z=
      ∑' n : ℕ, qPochhammer (b/a) q n*(-a*z)^n*q^((n*(n+1))/2)/qPochhammerList [b*q,z*q] q n := by
  by_cases hq0 : q = 0
  · subst hq0
    have hL : qPhi [0,a*0] [b*0] 0 z = (1-z)⁻¹ := by
      rw [← tsum_geometric_of_norm_lt_one hz]
      refine tsum_congr fun n => ?_
      simp [qPhiTerm, qPochhammerList, qPhiExponent, qPochhammer_zero_param]
    rw [hL, mul_inv_cancel₀ (one_sub_ne_zero_of_norm_lt_one hz)]
    rw [tsum_eq_single 0]
    · simp [qPochhammerList]
    · intro n hn
      have : n*(n+1)/2 ≠ 0 := by
        have : 2 ≤ n*(n+1) := by nlinarith [Nat.pos_of_ne_zero hn]
        omega
      simp [zero_pow this]
  have hqz : ‖q*z‖ < 1 := by rw [norm_mul]; nlinarith [norm_nonneg q, norm_nonneg z]
  have hden : QDenominatorRegular [b*q, q*z, z] q := by
    intro x hx n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hd _ (by simp) n
    · intro h
      have := norm_mul_pow_lt_one hqz hq n
      rw [h] at this; simp at this
    · intro h
      have := norm_mul_pow_lt_one hz hq n
      rw [h] at this; simp at this
  have h := qPhi2_to_qPhi2_2' q (a*q) (b*q) q z hq (by simp [ha, hq0]) hden hz
  rw [h]
  have hzq : qProductRatioInf [z*q] [z] q = (1-z)⁻¹ := by
    have h1 := qPochhammerInf_shift (a := z) hq
    have h2 : qPochhammerInf (z*q) q ≠ 0 :=
      qPochhammerInf_ne_zero_of_norm_lt_one (by rwa [mul_comm]) hq
    have h3 : 1 - z ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz
    simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [h1]; field_simp
  rw [hzq, ← mul_assoc, mul_inv_cancel₀ (one_sub_ne_zero_of_norm_lt_one hz), one_mul]
  unfold qPhi
  refine tsum_congr fun n => ?_
  have hqq := qPochhammer_self_ne_zero hq n
  simp only [qPhiTerm, qPochhammerList, qPhiExponent, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
  rw [show b*q/(a*q) = b/a by field_simp, show q*z = z*q by ring]
  norm_num
  have hexp : q ^ TripleProduct.tri (n:ℤ) * q^n = q^((n*(n+1))/2) := by
    rw [← zpow_natCast q n, ← zpow_natCast q (n*(n+1)/2), ← zpow_add₀ hq0]
    congr 1
    simp only [TripleProduct.tri]
    rw [Int.natCast_div]
    push_cast
    rw [show (n:ℤ)*(n+1) = n*(n-1) + n*2 by ring, Int.add_mul_ediv_right _ _ (by norm_num)]
  rw [← hexp]
  field_simp
  ring

/-- Fine's third expansion of `(1-z)/(1-b) 2φ1(q,aq;bq;q,z)` (DLMF 17.6.E11). -/
@[dlmf 17.6.E11]
theorem heine_fine_expansion_third {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1) (hb : ‖b‖<1)
    (hd : QDenominatorRegular [b*q,a*q/b] q) :
    (1-z)/(1-b)*qPhi [q,a*q] [b*q] q z=
      (∑' n : ℕ, qPochhammer (a*q) q n*qPochhammer (a*z*q/b) q (2*n)*b^n/qPochhammerList
          [z*q, a*q/b] q n)-
      a*q*∑' n : ℕ, qPochhammer (a*q) q n*qPochhammer (a*z*q/b) q (2*n+1)*(b*q)^n/
        (qPochhammer (z*q) q n*qPochhammer (a*q/b) q (n+1)) := by
  sorry

/-- Fine's fourth expansion of `(1-z) 2φ1(q,aq;bq;q,z)` as a well-poised type series (DLMF
17.6.E12). -/
@[dlmf 17.6.E12]
theorem heine_fine_expansion_fourth {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q] q) :
    (1-z)*qPhi [q,a*q] [b*q] q z=∑' n : ℕ,
      qPochhammerList [a*q,a*z*q/b] q n/qPochhammerList [b*q,z*q] q n*
        (1-a*z*q^(2*n+1))*(b*z)^n*q^(n*n) := by
  sorry

/-- A nonterminating summation combining two `2φ1` series at argument `q` into infinite products
(DLMF 17.6.E13). -/
@[dlmf 17.6.E13]
theorem heine_nonterminating_sum {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc0 : c≠0)
    (hd : QDenominatorRegular [c,q^2/c,c/q,a*q/c,b*q/c] q) :
    qPhi [a,b] [c] q q+qPochhammerListInf [q/c,a,b] q/qPochhammerListInf [c/q,a*q/c,b*q/c] q*
      qPhi [a*q/c, b*q/c] [q^2/c] q q=qPochhammerListInf [q/c, a*b*q/c] q/qPochhammerListInf
          [a*q/c, b*q/c] q := by
  sorry

/-- A mixed-base transformation between a series in bases `q` and `q²` and a `2φ1` in base `q²`
(DLMF 17.6.E14). -/
@[dlmf 17.6.E14]
theorem heine_mixed_base {a b q z : ℂ} (hq : ‖q‖<1)
    (hd : QDenominatorRegular [a*z*b,b*z] (q^2))
    (hD : qPochhammerListInf [z,a*z*b] (q^2)≠0)
    (hL : Summable (fun n : ℕ => qPochhammer a q n*qPochhammer b (q^2) n*z^n/
      (qPochhammer q q n*qPochhammer (a*z*b) (q^2) n)))
    (hR : Summable (qPhiTerm [a,b] [b*z] (q^2) (z*q))) :
    (∑' n : ℕ, qPochhammer a q n*qPochhammer b (q^2) n*z^n/
      (qPochhammer q q n*qPochhammer (a*z*b) (q^2) n))=
      qPochhammerListInf [a*z, b*z] (q^2)/qPochhammerListInf [z, a*z*b] (q^2)*qPhi [a, b] [b*z]
          (q^2) (z*q) := by
  sorry

/-- The first three-term connection formula for `2φ1(a,b;c;q,z)` (DLMF 17.6.E15). -/
@[dlmf 17.6.E15]
theorem heine_connection_first {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (habcz : a*b*c*z≠0) (hbc : ‖b*q‖<‖c‖)
    (hd : QDenominatorRegular [c,c*q/(a*z),q^2/c,a*z/c,q/a,c/q,b*q/c] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [a*b*z/c,q/c] q/qPochhammerListInf [a*z/c,q/a] q*
      qPhi [c/a,c*q/(a*b*z)] [c*q/(a*z)] q (b*q/c)-
      qPochhammerListInf [b,q/c,c/a,a*z/q,q^2/(a*z)] q/
        qPochhammerListInf [c/q,b*q/c,q/a,a*z/c,c*q/(a*z)] q*qPhi [a*q/c,b*q/c] [q^2/c] q z := by
  sorry

/-- The second three-term connection formula for `2φ1(a,b;c;q,z)`, in terms of `z ↦ cq/(abz)`
(DLMF 17.6.E16). -/
@[dlmf 17.6.E16]
theorem heine_connection_second {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (habcz : a*b*c*z≠0) (harg : ‖c*q‖<‖a*b*z‖)
    (hd : QDenominatorRegular [c,a*q/b,b*q/a,b/a,a/b,z,q/z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [b,c/a,a*z,q/(a*z)] q/qPochhammerListInf [c,b/a,z,q/z] q*
      qPhi [a,a*q/c] [a*q/b] q (c*q/(a*b*z))+
      qPochhammerListInf [a,c/b,b*z,q/(b*z)] q/qPochhammerListInf [c,a/b,z,q/z] q*
      qPhi [b,b*q/c] [b*q/a] q (c*q/(a*b*z)) := by
  sorry

/-- Heine's contiguous relation in the lower parameter `c/q` versus `c` (DLMF 17.6.E17). -/
@[dlmf 17.6.E17]
theorem heine_contiguous_17 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c/q] q) :
    qPhi [a, b] [c/q] q z-qPhi [a, b] [c] q z=c*z*(1-a)*(1-b)/((q-c)*(1-c))*qPhi [a*q, b*q]
        [c*q] q z := by
  have hc := qDenominatorRegular_of_div_q hq0 hd
  have hc' := qDenominatorRegular_mul_q hc
  have h1 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hc
  have h3 := hasSum_prependZero ((hasSum_qPhi_two_one (a := a*q) (b := b*q) hq0 hq hz hc').mul_left
    (c*z*(1-a)*(1-b)/((q-c)*(1-c))))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hc
  have hcq1 := one_sub_ne_zero_of_qDenominatorRegular hd
  have hqc : q-c≠0 := by
    intro h; apply hcq1; rw [show c=q by linear_combination -h]; field_simp; ring
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc n
    have hcn : 1-c*q^n≠0 := fun h => hc c (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ' (c/q),div_mul_cancel₀ _ hq0,
      qPochhammer_succ c,qPochhammer_mul_q hc1,qPochhammer_succ q,pow_succ z]
    field_simp
    ring

/-- Heine's contiguous relation in the upper parameter `aq` versus `a` (DLMF 17.6.E18). -/
@[dlmf 17.6.E18]
theorem heine_contiguous_18 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    qPhi [a*q,b] [c] q z-qPhi [a,b] [c] q z=a*z*(1-b)/(1-c)*qPhi [a*q,b*q] [c*q] q z := by
  have h1 := hasSum_qPhi_two_one (a := a*q) (b := b) hq0 hq hz hd
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have hd' := qDenominatorRegular_mul_q hd
  have h3 := hasSum_prependZero ((hasSum_qPhi_two_one (a := a*q) (b := b*q) hq0 hq hz hd').mul_left
    (a*z*(1-b)/(1-c)))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hc1 := one_sub_ne_zero_of_qDenominatorRegular hd
    have hcq := qPochhammer_ne_zero_of_qDenominatorRegular hq hd' n
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ (a*q),qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ' c,
      qPochhammer_succ q,pow_succ z]
    field_simp
    ring

/-- Heine's contiguous relation shifting `a` and `c` together (DLMF 17.6.E19). -/
@[dlmf 17.6.E19]
theorem heine_contiguous_19 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    qPhi [a*q, b] [c*q] q z-qPhi [a, b] [c] q z=z*(1-b)*(a-c)/((1-c)*(1-c*q))*qPhi [a*q, b*q]
        [c*q^2] q z := by
  have hc' := qDenominatorRegular_mul_q hd
  have hc'' : QDenominatorRegular [c*q^2] q := by
    simpa [pow_two,mul_assoc] using qDenominatorRegular_mul_q hc'
  have h1 := hasSum_qPhi_two_one (a := a*q) (b := b) hq0 hq hz hc'
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have h3 := hasSum_prependZero ((hasSum_qPhi_two_one (a := a*q) (b := b*q) hq0 hq hz hc'').mul_left
    (z*(1-b)*(a-c)/((1-c)*(1-c*q))))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hd
  have hcq1 := one_sub_ne_zero_of_qDenominatorRegular hc'
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc' n
    have hcn : 1-c*q*q^n≠0 := fun h => hc' (c*q) (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [show c*q^2=(c*q)*q by ring,qPochhammer_mul_q hcq1,
      qPochhammer_succ (a*q),qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ (c*q),
      qPochhammer_succ' c,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer (a*q) q n = A
    generalize qPochhammer (b*q) q n = B
    generalize qPochhammer (c*q) q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    generalize q^n = Q at hcn hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c*q*Q = D1 at hcn ⊢
    generalize hD2 : 1-c*q = D2 at hcq1 ⊢
    generalize hD3 : 1-c = D3 at hc1 ⊢
    field_simp
    simp only [← hD0,← hD1,← hD3]
    ring

/-- Heine's contiguous relation for `(aq, b/q)` versus `(a, b)` (DLMF 17.6.E20). -/
@[dlmf 17.6.E20]
theorem heine_contiguous_20 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    qPhi [a*q,b/q] [c] q z-qPhi [a,b] [c] q z=z*(a-b/q)/(1-c)*qPhi [a*q,b] [c*q] q z := by
  have hc' := qDenominatorRegular_mul_q hd
  have h1 := hasSum_qPhi_two_one (a := a*q) (b := b/q) hq0 hq hz hd
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have h3 := hasSum_prependZero ((hasSum_qPhi_two_one (a := a*q) (b := b) hq0 hq hz hc').mul_left
    (z*(a-b/q)/(1-c)))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hd
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc' n
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ (a*q),qPochhammer_succ' a,qPochhammer_succ' (b/q),div_mul_cancel₀ _ hq0,
      qPochhammer_succ b,qPochhammer_succ' c,qPochhammer_succ q,pow_succ z]
    field_simp
    ring

/-- Heine's contiguous relation `b(1-a)φ(aq,b) - a(1-b)φ(a,bq) = (b-a)φ(a,b)` (DLMF 17.6.E21). -/
@[dlmf 17.6.E21]
theorem heine_contiguous_21 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    b*(1-a)*qPhi [a*q,b] [c] q z-a*(1-b)*qPhi [a,b*q] [c] q z=(b-a)*qPhi [a,b] [c] q z := by
  have h1 := (hasSum_qPhi_two_one (a := a*q) (b := b) hq0 hq hz hd).mul_left (b*(1-a))
  have h2 := (hasSum_qPhi_two_one (a := a) (b := b*q) hq0 hq hz hd).mul_left (a*(1-b))
  have h3 := (hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd).mul_left (b-a)
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  intro n
  have ha1 : (1-a)*qPochhammer (a*q) q n=qPochhammer a q n*(1-a*q^n) := by
    rw [← qPochhammer_succ',qPochhammer_succ]
  have hb1 : (1-b)*qPochhammer (b*q) q n=qPochhammer b q n*(1-b*q^n) := by
    rw [← qPochhammer_succ',qPochhammer_succ]
  have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hd n
  have hqq := qPochhammer_self_ne_zero hq n
  field_simp
  linear_combination (b*qPochhammer b q n*z^n)*ha1-(a*qPochhammer a q n*z^n)*hb1

/-- Heine's contiguous relation between `φ(a,b/q)`, `φ(a/q,b)` and `φ(a,b)` (DLMF 17.6.E22). -/
@[dlmf 17.6.E22]
theorem heine_contiguous_22 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    a*(c-b)*qPhi [a, b/q] [c] q z-b*(c-a)*qPhi [a/q, b] [c] q z=(a-b)*(c-a*b*z/q)*qPhi
        [a, b] [c] q z := by
  have h0 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have h1 := (hasSum_qPhi_two_one (a := a) (b := b/q) hq0 hq hz hd).mul_left (a*(c-b))
  have h2 := (hasSum_qPhi_two_one (a := a/q) (b := b) hq0 hq hz hd).mul_left (b*(c-a))
  have h3 := (h0.mul_left ((a-b)*c)).sub (hasSum_prependZero (h0.mul_left ((a-b)*(a*b/q)*z)))
  have key := (h1.sub h2).unique (h3.congr_fun ?_)
  · rw [key]; ring
  intro n
  cases n with
  | zero => simp [prependZero]; ring
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hd n
    have hcn : 1-c*q^n≠0 := fun h => hd c (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' (b/q),qPochhammer_succ' (a/q),div_mul_cancel₀ _ hq0,div_mul_cancel₀ _ hq0,
      qPochhammer_succ a,qPochhammer_succ b,qPochhammer_succ c,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer c q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    generalize q^n = Q at hcn hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c*Q = D1 at hcn ⊢
    field_simp
    simp only [← hD0,← hD1]
    ring

/-- Heine's three-term contiguous relation between `φ(a/q,b)`, `φ(aq,b)` and `φ(a,b)` (DLMF
17.6.E23). -/
@[dlmf 17.6.E23]
theorem heine_contiguous_23 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    q*(c-a)*qPhi [a/q, b] [c] q z+(1-a)*(c-a*b*z)*qPhi [a*q, b] [c] q
        z=(c*(1+q-a)-a*q+a^2*z-a*b*z)*qPhi [a, b] [c] q z := by
  have h0 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have hp := hasSum_qPhi_two_one_mul_q (a := a) (b := b) hq0 hq hz hd
  have h1 := (hasSum_qPhi_two_one (a := a/q) (b := b) hq0 hq hz hd).mul_left (q*(c-a))
  have hL := (h1.add (hp.mul_left c)).sub (hasSum_prependZero (hp.mul_left (a*b*z)))
  have hR := (h0.mul_left (c*(1+q-a)-a*q)).add (hasSum_prependZero (h0.mul_left ((a^2-a*b)*z)))
  have key := hL.unique (hR.congr_fun ?_)
  · linear_combination key
  intro n
  cases n with
  | zero => simp [prependZero,qPochhammer_one]; ring
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hd n
    have hcn : 1-c*q^n≠0 := fun h => hd c (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' (a/q),div_mul_cancel₀ _ hq0,qPochhammer_succ a q (n+1),
      qPochhammer_succ a q n,qPochhammer_succ b,qPochhammer_succ c,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer c q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    try simp only [pow_succ q n]
    generalize q^n = Q at hcn hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c*Q = D1 at hcn ⊢
    field_simp
    simp only [← hD0,← hD1]
    ring

/-- Heine's three-term contiguous relation between `φ(;c/q)`, `φ(;cq)` and `φ(;c)` (DLMF
17.6.E24). -/
@[dlmf 17.6.E24]
theorem heine_contiguous_24 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c/q] q) :
    (1-c)*(q-c)*(a*b*z-c)*qPhi [a, b] [c/q] q z+z*(c-a)*(c-b)*qPhi [a, b] [c*q] q
        z=(c-1)*(c*(q-c)+z*(c*a+c*b-a*b-a*b*q))*qPhi [a, b] [c] q z := by
  have hc := qDenominatorRegular_of_div_q hq0 hd
  have hc' := qDenominatorRegular_mul_q hc
  have h0 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hc
  have hm := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have hp := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hc'
  have hL := ((hasSum_prependZero (hm.mul_left ((1-c)*(q-c)*(a*b)*z))).sub
    (hm.mul_left ((1-c)*(q-c)*c))).add (hasSum_prependZero (hp.mul_left ((c-a)*(c-b)*z)))
  have hR := (h0.mul_left ((c-1)*(c*(q-c)))).add
    (hasSum_prependZero (h0.mul_left ((c-1)*(c*a+c*b-a*b-a*b*q)*z)))
  have key := hL.unique (hR.congr_fun ?_)
  · linear_combination key
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hc
  have hcq1 := one_sub_ne_zero_of_qDenominatorRegular hd
  intro n
  cases n with
  | zero => simp [prependZero]; ring
  | succ n =>
    simp only [prependZero]
    obtain ⟨c0,rfl⟩ : ∃ c0, c=c0*q := ⟨c/q,by field_simp⟩
    simp only [mul_div_cancel_right₀ _ hq0] at hd ⊢
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hd n
    have hc01 : 1-c0≠0 := one_sub_ne_zero_of_qDenominatorRegular hd
    have hcn : 1-c0*q^n≠0 := fun h => hd c0 (by simp) n (by linear_combination -h)
    have hcn' : 1-c0*q*q^n≠0 := fun h => hc (c0*q) (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_mul_q hc1,qPochhammer_succ (c0*q),qPochhammer_succ c0,qPochhammer_mul_q hc01,
      qPochhammer_succ a,qPochhammer_succ b,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer c0 q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    generalize q^n = Q at hcn hcn' hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c0*q*Q = D1 at hcn' ⊢
    generalize hD2 : 1-c0*Q = D2 at hcn ⊢
    generalize hD3 : 1-c0*q = D3 at hc1 ⊢
    generalize hD4 : 1-c0 = D4 at hc01 ⊢
    field_simp
    simp only [← hD0,← hD1,← hD2,← hD3,← hD4]
    ring

/-- The `n`-th q-derivative of `z ↦ 2φ1(a,b;c;q,dz)` raises all parameters by `q^n` (DLMF
17.6.E25). -/
@[dlmf 17.6.E25]
theorem heine_qDerivative {a b c d q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖d*z‖<1)
    (hc : QDenominatorRegular [c] q) (n : ℕ) :
    qDerivIterate n q (fun w => qPhi [a,b] [c] q (w*d)) z=
      qPochhammerList [a, b] q n*d^n/(qPochhammer c q n*(1-q)^n)*qPhi [a*q^n, b*q^n]
          [c*q^n] q (d*z) :=
  qDerivIterate_qPhi_two_one hq0 hq hc n z hz

/-- The contiguous relation behind the weighted q-derivative:
`(1-u)φ(a,b;c;u) - (1-abu/c)φ(a,b;c;qu) = u(a-c)(b-c)/(c(1-c)) φ(a,b;cq;qu)`. -/
private lemma qPhi_two_one_weighted_step {a b c q u : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc0 : c≠0) (hc : QDenominatorRegular [c] q) (hu : ‖u‖<1) :
    (1-u)*qPhi [a,b] [c] q u-(1-a*b*u/c)*qPhi [a,b] [c] q (q*u) =
      u*(a-c)*(b-c)/(c*(1-c))*qPhi [a,b] [c*q] q (q*u) := by
  have hqu : ‖q*u‖<1 := by
    rw [norm_mul]
    calc ‖q‖*‖u‖ ≤ 1*‖u‖ := by gcongr
      _ < 1 := by linarith
  have h1 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hu hc
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hqu hc
  have h3 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hqu (qDenominatorRegular_mul_q hc)
  have hL := ((h1.sub (hasSum_prependZero (h1.mul_left u))).sub
    (h2.sub (hasSum_prependZero (h2.mul_left (a*b*u/c)))))
  have hR := hasSum_prependZero (h3.mul_left (u*(a-c)*(b-c)/(c*(1-c))))
  have e : (1-u)*qPhi [a,b] [c] q u-(1-a*b*u/c)*qPhi [a,b] [c] q (q*u) =
      qPhi [a,b] [c] q u-u*qPhi [a,b] [c] q u-
        (qPhi [a,b] [c] q (q*u)-a*b*u/c*qPhi [a,b] [c] q (q*u)) := by ring
  rw [e]
  refine hL.unique (hR.congr_fun ?_)
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hc
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq (qDenominatorRegular_mul_q hc) n
    have hcn := qPochhammer_ne_zero_of_qDenominatorRegular hq hc n
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    have hcqn : 1-c*q^n≠0 := fun h => hc c (by simp) n (by linear_combination -h)
    have hcq : qPochhammer c q (n+1) = (1-c)*qPochhammer (c*q) q n := qPochhammer_succ' c q n
    rw [qPochhammer_succ a, qPochhammer_succ b, qPochhammer_succ q, hcq]
    rw [show qPochhammer c q n = qPochhammer c q (n+1)/(1-c*q^n) by
      rw [qPochhammer_succ]; field_simp, hcq]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer (c*q) q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    rw [mul_pow, mul_pow, pow_succ u, pow_succ q]
    generalize q^n = Q at hqn hcqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c = D1 at hc1 ⊢
    generalize hD2 : 1-c*Q = D2 at hcqn ⊢
    field_simp
    simp only [← hD0, ← hD2]
    ring

/-- If `D_q F = G` off the origin near `0`, `F` is differentiable and `G` continuous at `0`, then
`F'(0) = G(0)`. -/
private lemma deriv_zero_eq_of_qDeriv {F G : ℂ → ℂ} {q : ℂ} (hq0 : q≠0) (hq1 : q≠1)
    (hF : DifferentiableAt ℂ F 0) (hG : ContinuousAt G 0)
    (h : ∀ᶠ w in 𝓝[≠] (0:ℂ), DLMF.QSeries.qDeriv q F w = G w) : deriv F 0 = G 0 := by
  have hs : Tendsto (fun t : ℂ => t⁻¹ • (F (0 + t) - F 0)) (𝓝[≠] 0) (𝓝 (deriv F 0)) :=
    (hasDerivAt_iff_tendsto_slope_zero.mp hF.hasDerivAt)
  have hmap : Tendsto (fun w : ℂ => q*w) (𝓝[≠] 0) (𝓝[≠] 0) := by
    have h0 : Tendsto (fun w : ℂ => q*w) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun w : ℂ => q*w := by fun_prop
      simpa using hc.tendsto 0
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h0.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact mul_ne_zero hq0 hw
  have hs2 := hs.comp hmap
  have hq1' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hlim : Tendsto (fun w => DLMF.QSeries.qDeriv q F w) (𝓝[≠] 0) (𝓝 (deriv F 0)) := by
    have := (hs.sub (hs2.const_mul q)).div_const (1-q)
    rw [show (deriv F 0 - q*deriv F 0)/(1-q) = deriv F 0 by field_simp] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [Function.comp_def, zero_add, smul_eq_mul, DLMF.QSeries.qDeriv]
    have hw' : w ≠ 0 := hw
    field_simp
    ring
  exact tendsto_nhds_unique (hlim.congr' h) (hG.tendsto.mono_left nhdsWithin_le_nhds)

/-- The right side of DLMF 17.6.26 after `k` q-derivatives. -/
private def heineWeighted (a b c q : ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  ((range k).prod (fun j => a-c*q^j))*((range k).prod (fun j => b-c*q^j))/
    (c^k*qPochhammer c q k*(1-q)^k)*qPochhammerInf (w*q^k) q/qPochhammerInf (a*b*w/c) q*
    qPhi [a,b] [c*q^k] q (w*q^k)

private lemma qDenominatorRegular_mul_pow {c q : ℂ} (hc : QDenominatorRegular [c] q) (k : ℕ) :
    QDenominatorRegular [c*q^k] q := by
  intro x hx n
  simp only [List.mem_singleton] at hx
  subst hx
  simpa [pow_add, mul_assoc] using hc c (by simp) (k+n)

/-- One q-derivative step of the weighted series. -/
private lemma qDeriv_heineWeighted {a b c q w : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc0 : c≠0)
    (hc : QDenominatorRegular [c] q) (hw0 : w≠0) (hw : ‖w‖<1)
    (hD : qPochhammerInf (a*b*w/c) q ≠ 0) (k : ℕ) :
    DLMF.QSeries.qDeriv q (heineWeighted a b c q k) w = heineWeighted a b c q (k+1) w := by
  have hck := qDenominatorRegular_mul_pow hc k
  have hqk : ‖q^k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hq.le
  have hu : ‖w*q^k‖<1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hqk) hw
  have hstep := qPhi_two_one_weighted_step (a := a) (b := b) hq0 hq
    (mul_ne_zero hc0 (pow_ne_zero k hq0)) hck hu
  have hq1 : (1:ℂ)-q ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hck
  have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc k
  have hqk0 : q^k ≠ 0 := pow_ne_zero k hq0
  rw [qPochhammerInf_shift hq] at hD
  have hL : 1-a*b*w/c ≠ 0 := left_ne_zero_of_mul hD
  have hV : qPochhammerInf (a*b*w/c*q) q ≠ 0 := right_ne_zero_of_mul hD
  unfold DLMF.QSeries.qDeriv heineWeighted
  rw [show q*w*q^k = q*(w*q^k) by ring, show w*q^(k+1) = q*(w*q^k) by ring,
    show a*b*(q*w)/c = a*b*w/c*q by ring, show c*q^(k+1) = c*q^k*q by ring,
    qPochhammerInf_shift hq (a := w*q^k), qPochhammerInf_shift hq (a := a*b*w/c),
    prod_range_succ, prod_range_succ, qPochhammer_succ, pow_succ c, pow_succ (1-q),
    show w*q^k*q = q*(w*q^k) by ring]
  rw [show a*b*(w*q^k)/(c*q^k) = a*b*w/c by field_simp] at hstep
  generalize qPhi [a,b] [c*q^k] q (w*q^k) = P0 at hstep ⊢
  generalize qPhi [a,b] [c*q^k] q (q*(w*q^k)) = P1 at hstep ⊢
  generalize qPhi [a,b] [c*q^k*q] q (q*(w*q^k)) = P2 at hstep ⊢
  generalize qPochhammerInf (q*(w*q^k)) q = U
  generalize qPochhammerInf (a*b*w/c*q) q = V at hV ⊢
  generalize qPochhammer c q k = C at hcc ⊢
  generalize hDk : 1-c*q^k = D at hc1 hstep ⊢
  generalize 1-a*b*w/c = L at hL hstep ⊢
  set X := (∏ j ∈ Finset.range k, (a - c * q ^ j)) * ∏ j ∈ Finset.range k, (b - c * q ^ j)
  have e : (X/(c^k*C*(1-q)^k)*((1-w*q^k)*U)/(L*V)*P0-X/(c^k*C*(1-q)^k)*U/V*P1)/((1-q)*w) =
      X/(c^k*C*(1-q)^k)*U/(L*V*((1-q)*w))*((1-w*q^k)*P0-L*P1) := by
    field_simp
  rw [e, hstep]
  field_simp
  simp only [X]
  ring

/-- The weighted series is differentiable on the disc away from the zeros of `(abw/c;q)_∞`. -/
private lemma differentiableAt_heineWeighted {a b c q w : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c] q) (hw : ‖w‖<1) (hD : qPochhammerInf (a*b*w/c) q ≠ 0)
    (k : ℕ) : DifferentiableAt ℂ (heineWeighted a b c q k) w := by
  have hck := qDenominatorRegular_mul_pow hc k
  have hqk : ‖q^k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hq.le
  have hu : ‖w*q^k‖<1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hqk) hw
  have hP : ∀ x, DifferentiableAt ℂ (fun y => qPochhammerInf y q) x :=
    differentiable_qPochhammerInf_left hq
  have hphi : DifferentiableAt ℂ (fun y => qPhi [a,b] [c*q^k] q y) (w*q^k) :=
    (qPhi_analytic_disc (a := [a,b]) hq0 hq hck (by simp) _ hu).differentiableAt
  unfold heineWeighted
  have h1 : DifferentiableAt ℂ (fun y => qPhi [a,b] [c*q^k] q (y*q^k)) w :=
    hphi.comp (f := fun y : ℂ => y*q^k) w (differentiableAt_id.mul_const _)
  have h2 : DifferentiableAt ℂ (fun y => qPochhammerInf (a*b*y/c) q) w :=
    (hP _).comp (f := fun y : ℂ => a*b*y/c) w (by fun_prop)
  have h3 : DifferentiableAt ℂ (fun y => qPochhammerInf (y*q^k) q) w :=
    (hP _).comp (f := fun y : ℂ => y*q^k) w (by fun_prop)
  exact (((differentiableAt_const _).mul h3).div h2 hD).mul h1

/-- The `n`-th q-derivative of `2φ1` weighted by the ratio of infinite products
`(z;q)_∞/(abz/c;q)_∞` (DLMF 17.6.E26). -/
@[dlmf 17.6.E26]
theorem heine_weighted_qDerivative {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1) (hc0 : c≠0)
    (hc : QDenominatorRegular [c] q) (hD : qPochhammerInf (a*b*z/c) q≠0) (n : ℕ) :
    qDerivIterate n q (fun w => qPochhammerInf w q/qPochhammerInf (a*b*w/c) q*qPhi [a,b] [c] q w) z=
      ((range n).prod (fun j => a-c*q^j))*((range n).prod (fun j => b-c*q^j))/
        (c^n*qPochhammer c q n*(1-q)^n)*qPochhammerInf (z*q^n) q/qPochhammerInf (a*b*z/c) q*
        qPhi [a,b] [c*q^n] q (z*q^n) := by
  set S : Set ℂ := {w | ‖w‖<1 ∧ qPochhammerInf (a*b*w/c) q ≠ 0} with hS
  have hcont : Continuous fun w : ℂ => qPochhammerInf (a*b*w/c) q :=
    (differentiable_qPochhammerInf_left hq).continuous.comp (by fun_prop)
  have hSo : IsOpen S := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_ne_fun hcont continuous_const)
  have hSq : ∀ w ∈ S, q*w ∈ S := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rw [norm_mul]
      calc ‖q‖*‖w‖ ≤ 1*‖w‖ := by gcongr
        _ < 1 := by linarith [hw.1]
    · have h := hw.2
      rw [qPochhammerInf_shift hq] at h
      rw [show a*b*(q*w)/c = a*b*w/c*q by ring]
      exact right_ne_zero_of_mul h
  have h0S : (0:ℂ) ∈ S := ⟨by simp, by simp [qPochhammerInf]⟩
  have hq1 : q ≠ 1 := by rintro rfl; simp at hq
  have key : ∀ m : ℕ, ∀ w ∈ S,
      qDerivIterate m q (heineWeighted a b c q 0) w = heineWeighted a b c q m w := by
    intro m
    induction m with
    | zero => intro w _; rfl
    | succ m ih =>
      intro w hw
      rw [qDerivIterate, Function.iterate_succ_apply', ← qDerivIterate]
      by_cases hw0 : w = 0
      · subst hw0
        rw [qDerivExtended_zero]
        have hev : qDerivIterate m q (heineWeighted a b c q 0) =ᶠ[𝓝 0]
            heineWeighted a b c q m := by
          filter_upwards [hSo.mem_nhds h0S] with w hw
          exact ih w hw
        rw [hev.deriv_eq]
        refine deriv_zero_eq_of_qDeriv hq0 hq1
          (differentiableAt_heineWeighted hq0 hq hc h0S.1 h0S.2 m)
          (differentiableAt_heineWeighted hq0 hq hc h0S.1 h0S.2 (m+1)).continuousAt ?_
        filter_upwards [nhdsWithin_le_nhds (hSo.mem_nhds h0S), self_mem_nhdsWithin]
          with w hw hw0
        exact qDeriv_heineWeighted hq0 hq hc0 hc hw0 hw.1 hw.2 m
      · rw [qDerivExtended_of_ne_zero hw0, DLMF.QSeries.qDeriv, ih w hw, ih (q*w) (hSq w hw)]
        exact qDeriv_heineWeighted hq0 hq hc0 hc hw0 hw.1 hw.2 m
  have hf : (fun w => qPochhammerInf w q/qPochhammerInf (a*b*w/c) q*qPhi [a,b] [c] q w) =
      heineWeighted a b c q 0 := by
    funext w
    simp [heineWeighted, qPochhammer_zero]
  rw [hf]
  exact key n z ⟨hz, hD⟩

/-- The second-order q-differential equation satisfied by `2φ1(a,b;c;q,z)` (DLMF 17.6.E27). -/
@[dlmf 17.6.E27]
theorem heine_qDifferentialEquation {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [c] q) :
    let F := fun w => qPhi [a,b] [c] q w
    z*(c-a*b*q*z)*qDerivIterate 2 q F z+
      ((1-c)/(1-q)+((1-a)*(1-b)-(1-a*b*q))/(1-q)*z)*qDerivExtended q F z-
      (1-a)*(1-b)/(1-q)^2*F z=0 := by
  intro F
  have hF : F=fun w => qPhi [a,b] [c] q (w*1) := funext fun w => by simp [F]
  have hz' : ‖1*z‖<1 := by simpa using hz
  have hD1 : qDerivExtended q F z=qDerivIterate 1 q F z := rfl
  rw [hD1, hF, qDerivIterate_qPhi_two_one hq0 hq hc 1 z hz',
      qDerivIterate_qPhi_two_one hq0 hq hc 2 z hz']
  simp only [mul_one,one_mul,one_pow]
  have h0 := hasSum_qPhi_two_one_shift (a := a) (b := b) hq0 hq hz hc 0
  have h1 := hasSum_qPhi_two_one_shift (a := a) (b := b) hq0 hq hz hc 1
  have h2 := hasSum_qPhi_two_one_shift (a := a) (b := b) hq0 hq hz hc 2
  set S0 := qPochhammer a q 0*qPochhammer b q 0/qPochhammer c q 0*qPhi [a*q^0,b*q^0] [c*q^0] q z
  set S1 := qPochhammer a q 1*qPochhammer b q 1/qPochhammer c q 1*qPhi [a*q^1,b*q^1] [c*q^1] q z
  set S2 := qPochhammer a q 2*qPochhammer b q 2/qPochhammer c q 2*qPhi [a*q^2,b*q^2] [c*q^2] q z
  have hL := ((((hasSum_prependZero (h2.mul_left (c*z))).sub
    (hasSum_prependZero (hasSum_prependZero (h2.mul_left (a*b*q*z^2))))).add
    (h1.mul_left (1-c))).add (hasSum_prependZero (h1.mul_left (((1-a)*(1-b)-(1-a*b*q))*z)))).sub
    (h0.mul_left ((1-a)*(1-b)))
  have hq1 : (1:ℂ)-q≠0 := one_sub_ne_zero_of_norm_lt_one hq
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hc
  have hcq : 1-c*q≠0 := one_sub_ne_zero_of_qDenominatorRegular (qDenominatorRegular_mul_q hc)
  have key := hL.unique (hasSum_zero.congr_fun ?_)
  · have e : z*(c-a*b*q*z)*(qPochhammerList [a,b] q 2/(qPochhammer c q 2*(1-q)^2)*
        qPhi [a*q^2,b*q^2] [c*q^2] q z)+((1-c)/(1-q)+((1-a)*(1-b)-(1-a*b*q))/(1-q)*z)*
        (qPochhammerList [a,b] q 1/(qPochhammer c q 1*(1-q)^1)*qPhi [a*q^1,b*q^1] [c*q^1] q z)-
        (1-a)*(1-b)/(1-q)^2*qPhi [a,b] [c] q z=
        (c*z*S2-a*b*q*z^2*S2+(1-c)*S1+((1-a)*(1-b)-(1-a*b*q))*z*S1-(1-a)*(1-b)*S0)/(1-q)^2 := by
      simp only [S0,S1,S2,qPochhammerList,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
        mul_one,pow_zero,qPochhammer_zero]
      field_simp
      ring
    rw [e,key,zero_div]
  intro n
  rcases n with _ | _ | n
  · simp [prependZero,qPochhammer_one]
    field_simp
    ring
  · simp [prependZero]
    simp only [qPochhammer_succ _ _ 1,qPochhammer_one,pow_one]
    generalize hD0 : 1-q = D0 at hq1 ⊢
    generalize hD1 : 1-c = D1 at hc1 ⊢
    generalize hD2 : 1-c*q = D2 at hcq ⊢
    field_simp
    simp only [← hD0,← hD1,← hD2]
    ring
  · simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc (n+2)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    have hqn1 : 1-q*q^(n+1)≠0 := by
      simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq (n+1)
    have hcn : 1-c*q^(n+2)≠0 := fun h => hc c (by simp) (n+2) (by linear_combination -h)
    rw [show n+1+2=(n+2)+1 by ring,show n+1+1=n+2 by ring,Nat.add_zero,
      qPochhammer_succ a q (n+2),qPochhammer_succ b q (n+2),qPochhammer_succ c q (n+2),
      qPochhammer_succ q q (n+1),qPochhammer_succ q q n]
    generalize qPochhammer a q (n+2) = A
    generalize qPochhammer b q (n+2) = B
    generalize qPochhammer c q (n+2) = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    rw [pow_succ z (n+1),pow_succ z n,show q^(n+2)=q^n*q*q by ring,show q^(n+1)=q^n*q by ring] at *
    generalize q^n = Q at hqn hqn1 hcn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-q*(Q*q) = D1 at hqn1 ⊢
    generalize hD2 : 1-c*(Q*q*q) = D2 at hcn ⊢
    field_simp
    simp only [← hD0,← hD1,← hD2]
    ring

/-- As `q → 1⁻`, the iterated q-derivatives of `2φ1(q^a,q^b;q^c;q,z)` tend to the derivatives of
the Gauss function `F(a,b;c;z)`. -/
theorem heine_classical_derivative_limit {a b c z : ℂ} (hc : ∀ n : ℕ, c≠ -(n:ℂ))
    (hz : ‖z‖<1) (n : ℕ) :
    Tendsto (fun q : ℝ => qDerivIterate n q
      (fun w => qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q w) z)
      (𝓝[<] 1) (𝓝 (iteratedDeriv n (ordinaryHypergeometric a b c) z)) := by
  sorry

/-- As `q → 1⁻`, the coefficients of Heine's q-differential equation tend to those of the Gauss
hypergeometric equation. -/
theorem heine_qDifferentialEquation_classical_coefficients (a b c z : ℂ) :
    Tendsto (fun q : ℝ =>
      (z*((q:ℂ)^c-(q:ℂ)^(a+b+1)*z),
       (1-(q:ℂ)^c)/(1-q)+((1-(q:ℂ)^a)*(1-(q:ℂ)^b)-(1-(q:ℂ)^(a+b+1)))/(1-q)*z,
       -(1-(q:ℂ)^a)*(1-(q:ℂ)^b)/(1-q)^2))
      (𝓝[<] 1) (𝓝 (z*(1-z),c-(a+b+1)*z,-a*b)) := by
  have hc := tendsto_ofReal_cpow_one c
  have habc := tendsto_ofReal_cpow_one (a+b+1)
  have hb1 := tendsto_ofReal_cpow_one b
  have nc := tendsto_qNumber_one c
  have na := tendsto_qNumber_one a
  have nb := tendsto_qNumber_one b
  have nabc := tendsto_qNumber_one (a+b+1)
  refine Tendsto.prodMk_nhds ?_ (Tendsto.prodMk_nhds ?_ ?_)
  · have h := (hc.sub (habc.mul_const z)).const_mul z
    simpa using h
  · have h := nc.add (((na.mul ((tendsto_const_nhds (x := (1:ℂ))).sub hb1)).sub nabc).mul_const z)
    simp only [sub_self,mul_zero,zero_sub] at h
    convert h using 2 with q
    · by_cases hq : (1:ℂ)-q=0
      · simp [hq]
      field_simp
    · ring
  · have h := (na.mul nb).neg
    convert h using 2 with q
    · by_cases hq : (1:ℂ)-q=0
      · simp [hq]
      field_simp
    · ring

/-- A uniform bound for `1/(q;q)_n`, `|q| < 1`. -/
theorem exists_norm_inv_qPochhammer_self_le {Q : ℂ} (hQ : ‖Q‖<1) :
    ∃ K, ∀ n, ‖(qPochhammer Q Q n)⁻¹‖ ≤ K := by
  have hI : qPochhammerInf Q Q ≠ 0 := qPochhammerInf_ne_zero hQ fun n => by
    simpa [pow_succ, mul_comm] using qPochhammerInf_pow_succ_ne_zero hQ n
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ ((tendsto_qPochhammer hQ).inv₀ hI))
  exact ⟨K, fun n => hK _ ⟨n, rfl⟩⟩

/-- A bound `‖(x;q)_n/(q;q)_n‖ ≤ M`, uniform in `n`. -/
private lemma exists_norm_qPochhammer_div_le {x q : ℂ} (hq : ‖q‖<1) :
    ∃ M, 0 ≤ M ∧ ∀ n, ‖qPochhammer x q n/qPochhammer q q n‖ ≤ M := by
  obtain ⟨K, hK⟩ := exists_norm_inv_qPochhammer_self_le hq
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨Real.exp (‖x‖/(1-‖q‖))*K, by positivity, fun n => ?_⟩
  rw [div_eq_mul_inv, norm_mul]
  exact mul_le_mul (norm_qPochhammer_le_exp hq n) (hK n) (norm_nonneg _) (by positivity)

/-- Jackson integral representation of `2φ1(q^a,q^b;q^c;q,z)`, the q-analogue of Euler's integral
(DLMF 17.6.E28). -/
@[dlmf 17.6.E28]
theorem heine_jackson_integral {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {a b c z : ℂ}
    (hb : 0<b.re) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [(q:ℂ)^c,(q:ℂ)^(c-b)] q) :
    qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q z=
      qGamma q c/(qGamma q b*qGamma q (c-b))*
      jacksonIntegral q 1 (fun t =>
          t^(b-1)*qPochhammerOrder (t*q) q (c-b-1)/qPochhammerOrder (z*t) q a) := by
  have hqc0 : (q:ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hqn : ‖(q:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hq1c : (1:ℂ)-q ≠ 0 := one_sub_ne_zero_of_norm_lt_one hqn
  have hnpow : ∀ s : ℂ, ‖(q:ℂ)^s‖ = q^s.re := fun s => Complex.norm_cpow_eq_rpow_re_of_pos hq0 s
  set A := (q:ℂ)^a with hA
  set B := (q:ℂ)^b with hB
  set C := (q:ℂ)^c with hC
  set E := (q:ℂ)^(c-b) with hE
  have hBn : ‖B‖ < 1 := by rw [hB, hnpow]; exact Real.rpow_lt_one hq0.le hq1 hb
  have hEB : E*B = C := by rw [hE, hB, hC, ← Complex.cpow_add _ _ hqc0]; ring_nf
  have hqE : (q:ℂ)*(q:ℂ)^(c-b-1) = E := by
    rw [hE, show c-b = (c-b-1)+1 by ring, Complex.cpow_add _ _ hqc0, Complex.cpow_one]; ring_nf
  have hCf : ∀ k : ℕ, 1-C*(q:ℂ)^k ≠ 0 := fun k h => hc C (by simp) k (by linear_combination -h)
  have hEf : ∀ k : ℕ, 1-E*(q:ℂ)^k ≠ 0 := fun k h => hc E (by simp) k (by linear_combination -h)
  have hCI : qPochhammerInf C q ≠ 0 := qPochhammerInf_ne_zero hqn hCf
  have hEI : qPochhammerInf E q ≠ 0 := qPochhammerInf_ne_zero hqn hEf
  have hBI : qPochhammerInf B q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hBn hqn
  have hQI : qPochhammerInf (q:ℂ) q ≠ 0 := qPochhammerInf_ne_zero hqn fun n => by
    simpa [pow_succ, mul_comm] using qPochhammerInf_pow_succ_ne_zero hqn n
  have hqpow : ∀ n : ℕ, ‖(q:ℂ)^n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hqn.le
  have hzq : ∀ n : ℕ, ‖z*(q:ℂ)^n‖ < 1 := fun n => by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hqpow n)) hz
  -- the double family
  set g : ℕ → ℕ → ℂ := fun n m => qPochhammer E q n/qPochhammer (q:ℂ) q n*B^n*
    (qPochhammer A q m/qPochhammer (q:ℂ) q m*(z*(q:ℂ)^n)^m) with hg
  obtain ⟨M1, hM1, hM1'⟩ := exists_norm_qPochhammer_div_le (x := E) hqn
  obtain ⟨M2, hM2, hM2'⟩ := exists_norm_qPochhammer_div_le (x := A) hqn
  have hgs : Summable (Function.uncurry g) := by
    refine Summable.of_norm_bounded ((((summable_geometric_of_lt_one (norm_nonneg _) hBn).mul_left
      M1).mul_of_nonneg ((summable_geometric_of_lt_one (norm_nonneg _) hz).mul_left M2)
      (fun _ => by positivity) (fun _ => by positivity))) ?_
    rintro ⟨n, m⟩
    simp only [Function.uncurry_apply_pair, hg, norm_mul, norm_pow]
    have h1 := hM1' n
    have h2 := hM2' m
    have h3 : ‖z‖*‖(q:ℂ)‖^n ≤ ‖z‖ := by
      have := hqpow n; rw [norm_pow] at this
      exact mul_le_of_le_one_right (norm_nonneg _) this
    refine le_trans (b := M1*‖B‖^n*(M2*‖z‖^m)) ?_ le_rfl
    gcongr
  -- the inner sums
  have hrow : ∀ n : ℕ, ∑' m, g n m = qPochhammer E q n/qPochhammer (q:ℂ) q n*B^n*
      (qPochhammerInf (A*(z*(q:ℂ)^n)) q/qPochhammerInf (z*(q:ℂ)^n) q) := by
    intro n
    simp only [hg]
    rw [tsum_mul_left, q_binomial_theorem hqn (hzq n)]
  have hcol : ∀ m : ℕ, ∑' n, g n m = qPochhammer A q m/qPochhammer (q:ℂ) q m*z^m*
      (qPochhammerInf (C*(q:ℂ)^m) q/qPochhammerInf (B*(q:ℂ)^m) q) := by
    intro m
    have hBm : ‖B*(q:ℂ)^m‖ < 1 := by
      rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hqpow m)) hBn
    have h := q_binomial_theorem (a := E) hqn hBm
    rw [← mul_assoc, hEB] at h
    rw [h, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [hg]
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m n]
    ring
  -- the integrand at the lattice points
  have hterm : ∀ n : ℕ, (fun t : ℂ => t^(b-1)*qPochhammerOrder (t*q) q (c-b-1)/
      qPochhammerOrder (z*t) q a) (1*(q:ℂ)^n)*(q:ℂ)^n =
      qPochhammerInf (q:ℂ) q/qPochhammerInf E q*∑' m, g n m := by
    intro n
    have hqn0 : (q:ℂ)^n ≠ 0 := pow_ne_zero n hqc0
    have hpow : ((q:ℂ)^n)^(b-1) = ((q:ℂ)^(b-1))^n := by
      rw [Complex.cpow_def_of_ne_zero hqn0, Complex.cpow_def_of_ne_zero hqc0,
        ← Complex.exp_nat_mul, ← Complex.ofReal_pow, ← Complex.ofReal_log (pow_pos hq0 n).le,
        Real.log_pow, ← Complex.ofReal_log hq0.le]
      push_cast
      ring_nf
    have hBq : (q:ℂ)^(b-1)*(q:ℂ) = B := by
      rw [hB, show b = (b-1)+1 by ring, Complex.cpow_add _ _ hqc0, Complex.cpow_one]; ring_nf
    have hEn : qPochhammer E q n ≠ 0 := qPochhammer_ne_zero_of_factors hqn hEf n
    have hQn := qPochhammer_self_ne_zero hqn n
    have hZ : qPochhammerInf (z*(q:ℂ)^n) q ≠ 0 :=
      qPochhammerInf_ne_zero_of_norm_lt_one (hzq n) hqn
    have h1 : qPochhammerInf ((q:ℂ)^n*q) q = qPochhammerInf (q:ℂ) q/qPochhammer (q:ℂ) q n := by
      rw [qPochhammerInf_mul_qPochhammer hqn (a := (q:ℂ)) n]; field_simp
    have h2 : qPochhammerInf ((q:ℂ)^n*q*(q:ℂ)^(c-b-1)) q =
        qPochhammerInf E q/qPochhammer E q n := by
      rw [qPochhammerInf_mul_qPochhammer hqn (a := E) n,
        show (q:ℂ)^n*q*(q:ℂ)^(c-b-1) = E*(q:ℂ)^n by rw [← hqE]; ring]
      field_simp
    rw [hrow]
    simp only [qPochhammerOrder, one_mul]
    rw [hpow, h1, h2, show z*(q:ℂ)^n*A = A*(z*(q:ℂ)^n) by ring]
    have hB' : ((q:ℂ)^(b-1))^n = B^n/(q:ℂ)^n := by rw [← hBq, mul_pow]; field_simp
    rw [hB']
    generalize qPochhammerInf (A*(z*(q:ℂ)^n)) q = X
    generalize qPochhammerInf (z*(q:ℂ)^n) q = Y at hZ ⊢
    field_simp
  have hC1 : QDenominatorRegular [C] q := fun x hx n => hc x (by simp at hx ⊢; exact Or.inl hx) n
  rw [(hasSum_qPhi_two_one (a := A) (b := B) hqc0 hqn hz hC1).tsum_eq.symm, jacksonIntegral,
    tsum_congr hterm, tsum_mul_left, ← hgs.tsum_comm, tsum_congr hcol, ← tsum_mul_left,
    ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hCm : qPochhammer C q m ≠ 0 := qPochhammer_ne_zero_of_factors hqn hCf m
  have hBm : qPochhammer B q m ≠ 0 := qPochhammer_ne_zero_of_factors hqn
    (fun j => one_sub_mul_pow_ne_zero_of_norm hBn hqn j) m
  have hQm := qPochhammer_self_ne_zero hqn m
  have hPC : qPochhammerInf (C*(q:ℂ)^m) q = qPochhammerInf C q/qPochhammer C q m := by
    rw [qPochhammerInf_mul_qPochhammer hqn (a := C) m]; field_simp
  have hPB : qPochhammerInf (B*(q:ℂ)^m) q = qPochhammerInf B q/qPochhammer B q m := by
    rw [qPochhammerInf_mul_qPochhammer hqn (a := B) m]; field_simp
  rw [hPC, hPB]
  unfold qGamma
  have hpw : (1-(q:ℂ))^(1-b)*(1-(q:ℂ))^(1-(c-b)) = (1-(q:ℂ))^(1-c)*(1-(q:ℂ)) := by
    rw [← Complex.cpow_add _ _ hq1c]
    conv_rhs => rw [show (1-(q:ℂ))^(1-c)*(1-q) = (1-(q:ℂ))^(1-c)*(1-q)^(1:ℂ) by
      rw [Complex.cpow_one]]
    rw [← Complex.cpow_add _ _ hq1c]
    ring_nf
  have hc1 : ∀ s : ℂ, (1-(q:ℂ))^s ≠ 0 := fun s => by simp [hq1c]
  have hr1 := hc1 (1-b)
  have hr2 := hc1 (1-(c-b))
  have hr3 := hc1 (1-c)
  rw [← hB, ← hC, ← hE]
  have key : (1-(q:ℂ))^(1-b)*(1-(q:ℂ))^(1-(c-b)) / (1-(q:ℂ))^(1-c) = 1-q := by
    rw [hpw]; field_simp
  generalize (1-(q:ℂ))^(1-b) = X1 at hr1 key ⊢
  generalize (1-(q:ℂ))^(1-(c-b)) = X2 at hr2 key ⊢
  generalize (1-(q:ℂ))^(1-c) = X3 at hr3 key ⊢
  rw [← key]
  generalize qPochhammerInf C q = PC at hCI ⊢
  generalize qPochhammerInf B q = PB at hBI ⊢
  generalize qPochhammerInf E q = PE at hEI ⊢
  generalize qPochhammerInf (q:ℂ) q = PQ at hQI ⊢
  field_simp

/-- The q-Mellin–Barnes integral representation of `2φ1(a,b;c;q,z)` (DLMF 17.6.E29). -/
@[dlmf 17.6.E29]
theorem heine_mellin_barnes {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz0 : z≠0) (hz : ‖z‖<1)
    (harg : |Complex.arg (-z)|<π) (hc : QDenominatorRegular [c] q)
    (L : ℝ → ℂ) (hL : ContDiff ℝ 1 L) (htail : Complex.HasVerticalTails L)
    (hsep : Complex.SeparatesPoleSets L (qHeineBarnesLeft a b q) qHeineBarnesRight)
    (hleft : Complex.StaysAwayFrom L (qHeineBarnesLeft a b q))
    (hright : Complex.StaysAwayFrom L qHeineBarnesRight) :
    Integrable (fun t : ℝ => qHeineBarnesKernel a b c q z (L t)*deriv L t) ∧
    qPhi [a,b] [c] q z= -1/(2*π*I)*qPochhammerListInf [a,b] q/qPochhammerListInf [q,c] q*
      ∫ t : ℝ, qHeineBarnesKernel a b c q z (L t)*deriv L t := by
  sorry

/-- The one-phi-zero product gives continuation of the actual series germ from zero. -/
theorem one_phi_zero_continues {a q : ℂ} (hq : ‖q‖<1) :
    AnalyticOnNhd ℂ (qOnePhiZeroContinuation a q) {z | qPochhammerInf z q≠0} ∧
    (qPhi [a] [] q=ᶠ[𝓝 0] qOnePhiZeroContinuation a q) ∧
    TauCeti.ContinuesInside (qPhi [a] [] q) {z | qPochhammerInf z q≠0} 0 := by
  have hF := one_phi_zero_continuation_analytic (a := a) hq
  have hcont : Continuous (fun z : ℂ => qPochhammerInf z q) :=
    continuousOn_univ.mp (qPochhammerInf_analytic hq).continuousOn
  have hU : IsOpen {z : ℂ | qPochhammerInf z q≠0} := isOpen_ne_fun hcont continuous_const
  have h0 : (0:ℂ)∈{z : ℂ | qPochhammerInf z q≠0} := by simp [qPochhammerInf]
  have heq : qPhi [a] [] q=ᶠ[𝓝 0] qOnePhiZeroContinuation a q := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1)] with z hz
    simpa only [qOnePhiZeroContinuation] using one_phi_zero (a := a) hq (by simpa using hz)
  exact ⟨hF,heq,qPhi_continuesInside_of_eq hU hF heq⟩

/-- The cleared terms `(A;q)_m (B;q)_m/(q;q)_m z^m (xq^m;q)_∞` of `₂φ₁(A,B;x;q,z) (x;q)_∞`. -/
private noncomputable def clearedTwoOneTerm (A B q z x : ℂ) (m : ℕ) : ℂ :=
  qPochhammer A q m*qPochhammer B q m/qPochhammer q q m*z^m*qPochhammerInf (x*q^m) q

/-- `₂φ₁(A,B;x;q,z) (x;q)_∞` as the series of cleared terms. -/
private lemma qPhi_two_one_mul_qPochhammerInf {A B x q z : ℂ} (hq : ‖q‖<1)
    (hx : QDenominatorRegular [x] q) :
    qPhi [A,B] [x] q z*qPochhammerInf x q = ∑' m, clearedTwoOneTerm A B q z x m := by
  rw [qPhi, ← tsum_mul_right]
  refine tsum_congr fun m => ?_
  have hxm : qPochhammer x q m ≠ 0 := qPochhammer_ne_zero_of_factors hq
    (fun j h => hx x (by simp) j (sub_eq_zero.mp h).symm) m
  have hqm := qPochhammer_self_ne_zero hq m
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
  rw [qPochhammerInf_mul_qPochhammer hq m, clearedTwoOneTerm]
  norm_num
  field_simp

/-- The cleared series is continuous in the lower parameter. -/
private lemma continuousAt_tsum_clearedTwoOneTerm {A B q z x₀ : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) :
    ContinuousAt (fun x => ∑' m, clearedTwoOneTerm A B q z x m) x₀ := by
  obtain ⟨K, hK⟩ := exists_norm_inv_qPochhammer_self_le hq
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set R := ‖x₀‖+1
  set u : ℕ → ℝ := fun m => Real.exp (‖A‖/(1-‖q‖))*Real.exp (‖B‖/(1-‖q‖))*K*
    ‖z‖^m*Real.exp (R/(1-‖q‖))
  have hu : Summable u :=
    ((summable_geometric_of_lt_one (norm_nonneg _) hz).mul_left _).mul_right _
  have hcont : ContinuousOn (fun x => ∑' m, clearedTwoOneTerm A B q z x m)
      (Metric.closedBall 0 R) := by
    refine continuousOn_tsum (fun m => ?_) hu fun m x hx => ?_
    · exact (continuous_const.mul ((differentiable_qPochhammerInf_left hq).continuous.comp
        (continuous_id.mul continuous_const))).continuousOn
    · rw [Metric.mem_closedBall, dist_zero_right] at hx
      have hq1 : 0 < 1-‖q‖ := by linarith
      have h1 : ‖qPochhammerInf (x*q^m) q‖ ≤ Real.exp (R/(1-‖q‖)) := by
        refine (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr
          (div_le_div_of_nonneg_right ?_ hq1.le))
        rw [norm_mul, norm_pow]
        exact (mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (norm_nonneg _) hq.le)).trans hx
      simp only [clearedTwoOneTerm, u, div_eq_mul_inv, norm_mul, norm_pow] at h1 ⊢
      gcongr
      · exact norm_qPochhammer_le_exp hq m
      · exact norm_qPochhammer_le_exp hq m
      · exact hK m
  exact hcont.continuousAt (mem_of_superset (Metric.isOpen_ball.mem_nhds (by simp [R]))
    Metric.ball_subset_closedBall)

/-- The Jackson representation at Gamma-factor poles is its regular-parameter limit. -/
@[dlmf 17.6.E28]
theorem heine_jackson_parameter_limit {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    {a b c₀ z : ℂ} (hb : 0<b.re) (hz : ‖z‖<1)
    (hc₀ : QDenominatorRegular [(q:ℂ)^c₀] q) :
    Tendsto (fun c : ℂ => qHeineJacksonValue q a b c z)
      (𝓝[{c : ℂ | QDenominatorRegular [(q:ℂ)^c,(q:ℂ)^(c-b)] q}] c₀)
      (𝓝 (qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c₀] q z)) := by
  have hqc0 : (q:ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hqn : ‖(q:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  set h : ℂ → ℂ := fun c => (∑' m, clearedTwoOneTerm ((q:ℂ)^a) ((q:ℂ)^b) q z ((q:ℂ)^c) m)/
    qPochhammerInf ((q:ℂ)^c) q with hh
  have hreg : ∀ c : ℂ, QDenominatorRegular [(q:ℂ)^c] q →
      qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q z = h c := by
    intro c hc
    have hI : qPochhammerInf ((q:ℂ)^c) q ≠ 0 := qPochhammerInf_ne_zero hqn
      fun k e => hc ((q:ℂ)^c) (by simp) k (by linear_combination -e)
    rw [hh, eq_div_iff hI, qPhi_two_one_mul_qPochhammerInf hqn hc]
  have hpow : Continuous fun c : ℂ => (q:ℂ)^c := by
    have : NeZero (q:ℂ) := ⟨hqc0⟩; exact continuous_const_cpow (q:ℂ)
  have hI0 : qPochhammerInf ((q:ℂ)^c₀) q ≠ 0 := qPochhammerInf_ne_zero hqn
      fun k e => hc₀ ((q:ℂ)^c₀) (by simp) k (by linear_combination -e)
  have hcont : ContinuousAt h c₀ :=
    (((continuousAt_tsum_clearedTwoOneTerm hqn hz).comp hpow.continuousAt).div
      (((differentiable_qPochhammerInf_left hqn).continuous.comp hpow).continuousAt) hI0)
  rw [hreg c₀ hc₀]
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [qHeineJacksonValue, ← heine_jackson_integral hq0 hq1 hb hz hc]
  exact (hreg c fun x hx k => hc x (by simp at hx ⊢; exact Or.inl hx) k).symm

end DLMF.QHypergeometric
