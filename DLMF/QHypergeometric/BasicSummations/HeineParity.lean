/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BasicSummations.Heine

/-!
# The even and odd base-`q²` sums of DLMF 17.6.4

The two series `₂φ₁(b², b²/c; c; q², cq/b²)` and `₂φ₁(b², b²/c; cq²; q², cq³/b²)` are summed in
terms of infinite products. For `|b| < 1` Heine's transformation reduces each to the even or odd
part of a `q`-binomial series in base `q`. Both sides are then cleared of their lower-parameter
products and continued analytically to the whole domain of convergence of the left series: first
in `b` along a half-plane for small `c`, then in `c` over a disk. The odd identity has a removable
singularity at `c = b²/q`, where the product form is replaced by its limit.

## Main results

* `q_even_heine`, `q_odd_heine`: DLMF 17.6.4.
* `q_odd_heine_removable`: the limit of the odd product form at its removable singularity.
-/

@[expose] public noncomputable section
open Complex Filter Finset DLMF.QSeries
open scoped Topology
namespace DLMF.QHypergeometric

/-- The even part of the base-`q²` reduction, for `|b| < 1`. -/
private lemma q_even_heine_direct {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1)
    (hb1 : ‖b‖<1) (hz : ‖c*q‖<‖b^2‖) (hc : QDenominatorRegular [c] (q^2)) :
    qPhi [b^2,b^2/c] [c] (q^2) (c*q/b^2)=
      qPochhammerInf q (q^2)/(2*qPochhammerListInf [c,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+
         qPochhammerInf b q*qPochhammerInf (-c/b) q) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hb2 : ‖b^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg b) hb1 two_ne_zero
  have hZ : ‖c*q/b^2‖<1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb))]; exact hz
  rw [qPhi_eq_basicHypergeometric (by simp), basicHypergeometric_swap,
    heine_transformation hQ hZ hb2 (pow_ne_zero 2 hb) (fun k h => hc c (by simp) k h) (fun k h =>
      one_sub_mul_pow_ne_zero_of_norm hq hQ k (by
        rw [show b^2/c*(c*q/b^2) = q by field_simp] at h; rw [h]; ring))]
  rw [show b^2/c*(c*q/b^2) = q by field_simp, show c/b^2 = c/b^2 from rfl]
  -- the remaining `₂φ₁` is the even part of a `q`-binomial series
  set g : ℕ → ℂ := fun m => qPochhammer (c/b^2) q m/qPochhammer q q m*b^m
  have hsum : basicHypergeometric [c/b^2, c*q/b^2] [q] (q^2) (b^2) = ∑' n : ℕ, g (2*n) := by
    simp only [basicHypergeometric, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, g]
    refine tsum_congr fun n => ?_
    have h1 := qPochhammer_even (c/b^2) q n
    have h2 := qPochhammer_even q q n
    simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h1 h2
    rw [h1, h2, show c/b^2*q = c*q/b^2 by ring, show q*q = q^2 by ring, pow_mul]
  have hg := summable_q_binomial_series (a := c/b^2) hq hb1
  have hg' := summable_q_binomial_series (a := c/b^2) hq (z := -b) (by rwa [norm_neg])
  have hE : ∀ f : ℕ → ℂ, Summable f → ∑' n, f n = ∑' n, f (2*n) + ∑' n, f (2*n+1) :=
    fun f hf => (tsum_even_add_odd (hf.comp_injective (mul_right_injective₀ two_ne_zero))
      (hf.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ two_ne_zero)))).symm
  have e1 := hE _ hg
  have e2 := hE _ hg'
  have hp : ∀ n : ℕ, qPochhammer (c/b^2) q (2*n)/qPochhammer q q (2*n)*(-b)^(2*n) = g (2*n) :=
    fun n => by simp only [g]; rw [Even.neg_pow ⟨n, by ring⟩]
  have hm : ∀ n : ℕ, qPochhammer (c/b^2) q (2*n+1)/qPochhammer q q (2*n+1)*(-b)^(2*n+1) =
      -g (2*n+1) := fun n => by simp only [g]; rw [Odd.neg_pow ⟨n, rfl⟩]; ring
  simp only [hp, hm, tsum_neg] at e2
  have heven : ∑' n : ℕ, g (2*n) = (qPochhammerInf (c/b) q/qPochhammerInf b q+
      qPochhammerInf (-c/b) q/qPochhammerInf (-b) q)/2 := by
    rw [show c/b = c/b^2*b by field_simp, show -c/b = c/b^2*(-b) by field_simp,
      q_binomial_theorem hq hb1, q_binomial_theorem hq (by rwa [norm_neg]), e2]
    simp only [g] at e1 ⊢
    rw [e1]
    ring
  rw [hsum, heven]
  have hbI : qPochhammerInf b q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hb1 hq
  have hbI' : qPochhammerInf (-b) q ≠ 0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one (by rwa [norm_neg]) hq
  have hcI : qPochhammerInf c (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hc c (by simp) n (sub_eq_zero.mp h).symm
  have hZI : qPochhammerInf (c*q/b^2) (q^2) ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hZ hQ
  have hsq : qPochhammerInf (b^2) (q^2) = qPochhammerInf b q*qPochhammerInf (-b) q :=
    (qPochhammerInf_mul_qPochhammerInf_neg hq).symm
  rw [hsq]
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  field_simp



/-- The odd part of the base-`q²` reduction, for `|b| < 1`. -/
private lemma q_odd_heine_direct {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1)
    (hb1 : ‖b‖<1) (hz : ‖c*q^3‖<‖b^2‖) (hc : QDenominatorRegular [c*q^2] (q^2))
    (hd : qPochhammerInf (c*q/b^2) (q^2)≠0) :
    qPhi [b^2,b^2/c] [c*q^2] (q^2) (c*q^3/b^2)=
      qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
         qPochhammerInf b q*qPochhammerInf (-c*q/b) q) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hq3 : ‖q^3‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have hb2 : ‖b^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg b) hb1 two_ne_zero
  have hZ : ‖c*q^3/b^2‖<1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb))]; exact hz
  rw [qPhi_eq_basicHypergeometric (by simp), basicHypergeometric_swap,
    heine_transformation hQ hZ hb2 (pow_ne_zero 2 hb) (fun k h => hc (c*q^2) (by simp) k h)
      (fun k h => one_sub_mul_pow_ne_zero_of_norm hq3 hQ k (by
        rw [show b^2/c*(c*q^3/b^2) = q^3 by field_simp] at h; rw [h]; ring))]
  rw [show b^2/c*(c*q^3/b^2) = q^3 by field_simp]
  set x := c*q/b^2 with hx
  have hx1 : 1-x ≠ 0 := by
    intro h; apply hd; rw [qPochhammerInf_shift hQ, h, zero_mul]
  set g : ℕ → ℂ := fun m => qPochhammer x q m/qPochhammer q q m*b^m
  have hq1 : (1:ℂ)-q ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  have hsum : basicHypergeometric [c*q^2/b^2, c*q^3/b^2] [q^3] (q^2) (b^2) =
      (1-q)/((1-x)*b)*∑' n : ℕ, g (2*n+1) := by
    rw [← tsum_mul_left]
    simp only [basicHypergeometric, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, g]
    refine tsum_congr fun n => ?_
    have h1 := qPochhammer_even (x*q) q n
    have h2 := qPochhammer_even (q*q) q n
    simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h1 h2
    rw [qPochhammer_succ' x q (2*n), qPochhammer_succ' q q (2*n), h1, h2,
      show x*q = c*q^2/b^2 by rw [hx]; ring, show c*q^2/b^2*q = c*q^3/b^2 by ring,
      show q*q = q^2 by ring, show q^2*q = q^3 by ring, pow_succ b (2*n), pow_mul b 2 n]
    have hn1 := qPochhammer_self_ne_zero hQ n
    have hn2 : qPochhammer (q^3) (q^2) n ≠ 0 := qPochhammer_ne_zero_of_factors hQ
      (fun j => one_sub_mul_pow_ne_zero_of_norm hq3 hQ j) n
    field_simp
  have hg := summable_q_binomial_series (a := x) hq hb1
  have hg' := summable_q_binomial_series (a := x) hq (z := -b) (by rwa [norm_neg])
  have hE : ∀ f : ℕ → ℂ, Summable f → ∑' n, f n = ∑' n, f (2*n) + ∑' n, f (2*n+1) :=
    fun f hf => (tsum_even_add_odd (hf.comp_injective (mul_right_injective₀ two_ne_zero))
      (hf.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ two_ne_zero)))).symm
  have e1 := hE _ hg
  have e2 := hE _ hg'
  have hp : ∀ n : ℕ, qPochhammer x q (2*n)/qPochhammer q q (2*n)*(-b)^(2*n) = g (2*n) :=
    fun n => by simp only [g]; rw [Even.neg_pow ⟨n, by ring⟩]
  have hm : ∀ n : ℕ, qPochhammer x q (2*n+1)/qPochhammer q q (2*n+1)*(-b)^(2*n+1) =
      -g (2*n+1) := fun n => by simp only [g]; rw [Odd.neg_pow ⟨n, rfl⟩]; ring
  simp only [hp, hm, tsum_neg] at e2
  have hodd : ∑' n : ℕ, g (2*n+1) = (qPochhammerInf (c*q/b) q/qPochhammerInf b q-
      qPochhammerInf (-c*q/b) q/qPochhammerInf (-b) q)/2 := by
    rw [show c*q/b = x*b by rw [hx]; field_simp, show -c*q/b = x*(-b) by rw [hx]; field_simp,
      q_binomial_theorem hq hb1, q_binomial_theorem hq (by rwa [norm_neg]), e2]
    simp only [g] at e1 ⊢
    rw [e1]
    ring
  rw [hsum, hodd]
  have hbI : qPochhammerInf b q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hb1 hq
  have hbI' : qPochhammerInf (-b) q ≠ 0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one (by rwa [norm_neg]) hq
  have hcI : qPochhammerInf (c*q^2) (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hc (c*q^2) (by simp) n (sub_eq_zero.mp h).symm
  have hZI : qPochhammerInf (c*q^3/b^2) (q^2) ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hZ hQ
  have hsq : qPochhammerInf (b^2) (q^2) = qPochhammerInf b q*qPochhammerInf (-b) q :=
    (qPochhammerInf_mul_qPochhammerInf_neg hq).symm
  have hq3I : qPochhammerInf q (q^2) = (1-q)*qPochhammerInf (q^3) (q^2) := by
    rw [qPochhammerInf_shift hQ]; ring_nf
  have hxI : qPochhammerInf x (q^2) = (1-x)*qPochhammerInf (c*q^3/b^2) (q^2) := by
    rw [qPochhammerInf_shift hQ, hx]; ring_nf
  rw [hsq, hq3I]
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [hxI]
  field_simp

/-- A bound for `∏_{j<n} (w - a q^{2j})`, `‖a‖ ≤ 1`, uniform in `‖w‖ ≤ ρ`. -/
private lemma norm_prod_sub_mul_sq_pow_le {w a q : ℂ} {ρ : ℝ} (hq : ‖q‖<1) (ha : ‖a‖ ≤ 1)
    (hρ : 0<ρ) (hw : ‖w‖ ≤ ρ) (n : ℕ) :
    ‖∏ j ∈ range n, (w-a*(q^2)^j)‖ ≤ ρ^n*Real.exp (1/(ρ*(1-‖q‖))) := by
  have hq1 : 0 < 1-‖q‖ := by linarith
  have key : ‖∏ j ∈ range n, (w-a*(q^2)^j)‖ ≤ ρ^n*Real.exp ((∑ j ∈ range n, ‖q‖^j)/ρ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [prod_range_succ, norm_mul, sum_range_succ, add_div, Real.exp_add, pow_succ]
      have h1 : ‖w-a*(q^2)^n‖ ≤ ρ*(1+‖q‖^n/ρ) := by
        calc ‖w-a*(q^2)^n‖ ≤ ‖w‖+‖a*(q^2)^n‖ := norm_sub_le _ _
          _ ≤ ρ+‖q‖^n := by
            gcongr
            rw [norm_mul, norm_pow, norm_pow, ← pow_mul]
            calc ‖a‖*‖q‖^(2*n) ≤ 1*‖q‖^n :=
                  mul_le_mul ha (pow_le_pow_of_le_one (norm_nonneg _) hq.le (by omega))
                    (by positivity) zero_le_one
              _ = ‖q‖^n := one_mul _
          _ = ρ*(1+‖q‖^n/ρ) := by field_simp
      have h2 : 1+‖q‖^n/ρ ≤ Real.exp (‖q‖^n/ρ) := by
        linarith [Real.add_one_le_exp (‖q‖^n/ρ)]
      calc ‖∏ j ∈ range n, (w-a*(q^2)^j)‖*‖w-a*(q^2)^n‖
          ≤ (ρ^n*Real.exp ((∑ j ∈ range n, ‖q‖^j)/ρ))*(ρ*(1+‖q‖^n/ρ)) := by
            gcongr
        _ ≤ (ρ^n*Real.exp ((∑ j ∈ range n, ‖q‖^j)/ρ))*(ρ*Real.exp (‖q‖^n/ρ)) := by
            gcongr
        _ = _ := by ring
  refine key.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  rw [div_le_div_iff₀ hρ (by positivity), one_mul]
  have hg := geom_sum_mul (‖q‖) n
  have h : (∑ j ∈ range n, ‖q‖^j)*(ρ*(1-‖q‖)) = ρ*(1-‖q‖^n) := by
    linear_combination (-ρ)*hg
  rw [h]
  nlinarith [mul_nonneg hρ.le (pow_nonneg (norm_nonneg q) n)]


/-- `(b²/c;q²)_n (ca/b²)^n = ∏_{j<n} (ca/b² - a q^{2j})`. -/
private lemma qPochhammer_mul_pow_eq_prod {a b c q : ℂ} (hb : b≠0) (hc : c≠0) (n : ℕ) :
    qPochhammer (b^2/c) (q^2) n*(c*a/b^2)^n = ∏ j ∈ range n, (c*a/b^2-a*(q^2)^j) := by
  induction n with
  | zero => simp [qPochhammer_zero]
  | succ n ih =>
    have h : (1-b^2/c*(q^2)^n)*(c*a/b^2) = c*a/b^2-a*(q^2)^n := by field_simp
    rw [qPochhammer_succ, prod_range_succ, ← ih, pow_succ (c*a/b^2) n, ← h]
    ring

/-- `a ↦ (g(a);q)_k` is differentiable at `a` when `g` is. -/
private lemma differentiableAt_qPochhammer_comp {q a : ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableAt ℂ g a) (k : ℕ) :
    DifferentiableAt ℂ (fun a => qPochhammer (g a) q k) a := by
  induction k with
  | zero => simp [qPochhammer_zero]
  | succ k ih =>
    simp only [qPochhammer_succ]
    exact ih.mul ((differentiableAt_const _).sub (hg.mul (differentiableAt_const _)))

/-- `a ↦ (g(a);q)_∞` is differentiable at `a` when `g` is. -/
private lemma differentiableAt_qPochhammerInf_comp {q a : ℂ} {g : ℂ → ℂ} (hq : ‖q‖<1)
    (hg : DifferentiableAt ℂ g a) : DifferentiableAt ℂ (fun x => qPochhammerInf (g x) q) a :=
  (differentiable_qPochhammerInf_left hq _).comp a hg

/-- The terms of `₂φ₁(b², b²/c; ce; q², ca/b²)` multiplied by `(ce;q²)_∞`; `e = 1, a = q` gives
the even and `e = q², a = q³` the odd case of DLMF 17.6.4. -/
private def heineSqTerm (q e a b c : ℂ) (n : ℕ) : ℂ :=
  qPochhammerInf (c*e*(q^2)^n) (q^2)*(qPochhammer (b^2) (q^2) n/qPochhammer (q^2) (q^2) n*
    ∏ j ∈ range n, (c*a/b^2-a*(q^2)^j))

/-- Clearing `(ce;q²)_∞` from the left side. -/
private lemma qPhi_heineSq_mul {e a b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c*e] (q^2)) :
    qPhi [b^2,b^2/c] [c*e] (q^2) (c*a/b^2)*qPochhammerInf (c*e) (q^2) =
      ∑' n, heineSqTerm q e a b c n := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  rw [qPhi, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  have hcn : qPochhammer (c*e) (q^2) n ≠ 0 := qPochhammer_ne_zero_of_factors hQ
    (fun j h => hc (c*e) (by simp) j (sub_eq_zero.mp h).symm) n
  have hqn := qPochhammer_self_ne_zero hQ n
  have hP := qPochhammer_mul_pow_eq_prod (a := a) (q := q) hb hc0 n
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
  rw [qPochhammerInf_mul_qPochhammer hQ n, heineSqTerm, ← hP]
  norm_num
  field_simp

/-- A geometric bound for the cleared terms, uniform on bounded parameter sets. -/
private lemma norm_heineSqTerm_le {q e a b c : ℂ} {M R ρ K : ℝ} (hq : ‖q‖<1) (he : ‖e‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) (hb : b≠0) (hρ : 0<ρ) (hbM : ‖b‖^2 ≤ M) (hcR : ‖c‖ ≤ R)
    (hcρ : ‖c*a‖ ≤ ρ*‖b‖^2) (hK : ∀ n, ‖(qPochhammer (q^2) (q^2) n)⁻¹‖ ≤ K) (n : ℕ) :
    ‖heineSqTerm q e a b c n‖ ≤ Real.exp (R/(1-‖q^2‖))*(Real.exp (M/(1-‖q^2‖))*K*
      (ρ^n*Real.exp (1/(ρ*(1-‖q‖))))) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hw : ‖c*a/b^2‖ ≤ ρ := by
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]; exact hcρ
  have h1 : ‖qPochhammerInf (c*e*(q^2)^n) (q^2)‖ ≤ Real.exp (R/(1-‖q^2‖)) := by
    refine (norm_qPochhammerInf_le_exp hQ).trans (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right ?_ (by linarith)))
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖c‖*‖e‖*‖q^2‖^n ≤ ‖c‖*1*1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hQ.le
      _ ≤ R := by simpa using hcR
  have h2 : ‖qPochhammer (b^2) (q^2) n‖ ≤ Real.exp (M/(1-‖q^2‖)) :=
    (norm_qPochhammer_le_exp hQ n).trans (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right (by rw [norm_pow]; exact hbM) (by linarith)))
  have h3 := norm_prod_sub_mul_sq_pow_le hq ha hρ hw n
  rw [heineSqTerm, norm_mul, norm_mul, div_eq_mul_inv, norm_mul]
  have := hK n
  gcongr
  exact mul_nonneg (Real.exp_nonneg _) ((norm_nonneg _).trans this)

/-- The cleared series is holomorphic in `b` on `‖ca‖ < ‖b²‖`. -/
private lemma differentiableOn_heineSq_left {q e a c : ℂ} (hq : ‖q‖<1) (he : ‖e‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) :
    DifferentiableOn ℂ (fun b => ∑' n, heineSqTerm q e a b c n) {b | ‖c*a‖ < ‖b^2‖} := by
  intro b0 hb0
  simp only [Set.mem_ofPred_eq, norm_pow] at hb0
  have hb0' : b0 ≠ 0 := by
    rintro rfl; simp at hb0; exact absurd hb0 (not_lt.mpr (by positivity))
  have hB : 0 < ‖b0‖^2 := by positivity
  obtain ⟨K, hK⟩ := exists_norm_inv_qPochhammer_self_le (Q := q^2)
    (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero)
  set ρ := (‖c*a‖/‖b0‖^2+1)/2 with hρ
  have hr : ‖c*a‖/‖b0‖^2 < 1 := (div_lt_one hB).mpr hb0
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  set M := ‖b0‖^2+1
  set W := {b : ℂ | ‖c*a‖ < ρ*‖b‖^2 ∧ ‖b‖^2 < M}
  have hW : IsOpen W :=
    (isOpen_lt (f := fun _ : ℂ => ‖c*a‖) (g := fun b => ρ*‖b‖^2) continuous_const
      (by fun_prop)).inter (isOpen_lt (f := fun b : ℂ => ‖b‖^2) (g := fun _ => M) (by fun_prop)
      continuous_const)
  have hb0W : b0 ∈ W := by
    refine ⟨?_, by simp [M]⟩
    rw [hρ, div_add_one hB.ne', div_div, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith
  have hW0 : ∀ b ∈ W, b ≠ 0 := by
    rintro b hb rfl; have := hb.1; simp at this; exact absurd this (not_lt.mpr (by positivity))
  have hd : DifferentiableOn ℂ (fun b => ∑' n, heineSqTerm q e a b c n) W := by
    refine differentiableOn_tsum_of_summable_norm
      ((((summable_geometric_of_lt_one hρ0.le hρ1).mul_right _).mul_left _).mul_left _)
      (fun n b hb => ?_) hW (fun n b hb => norm_heineSqTerm_le hq he ha (hW0 b hb) hρ0 hb.2.le
        le_rfl hb.1.le hK n)
    have hb' := hW0 b hb
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold heineSqTerm
    refine (differentiableAt_const _).mul (((differentiableAt_qPochhammer_comp
      (g := fun b => b^2) (by fun_prop) n).div_const _).mul ?_)
    fun_prop (disch := exact pow_ne_zero 2 hb')
  exact (hd.differentiableAt (hW.mem_nhds hb0W)).differentiableWithinAt

/-- The cleared series is holomorphic in `c` on `‖ca‖ < ‖b²‖`. -/
private lemma differentiableOn_heineSq_right {q e a b : ℂ} (hq : ‖q‖<1) (he : ‖e‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) (hb : b≠0) :
    DifferentiableOn ℂ (fun c => ∑' n, heineSqTerm q e a b c n) {c | ‖c*a‖ < ‖b^2‖} := by
  intro c0 hc0
  simp only [Set.mem_ofPred_eq, norm_pow] at hc0
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hB : 0 < ‖b‖^2 := by positivity
  obtain ⟨K, hK⟩ := exists_norm_inv_qPochhammer_self_le hQ
  set ρ := (‖c0*a‖/‖b‖^2+1)/2 with hρ
  have hr : ‖c0*a‖/‖b‖^2 < 1 := (div_lt_one hB).mpr hc0
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  set R := ‖c0‖+1
  set W := {c : ℂ | ‖c*a‖ < ρ*‖b‖^2 ∧ ‖c‖ < R}
  have hW : IsOpen W :=
    (isOpen_lt (f := fun c : ℂ => ‖c*a‖) (g := fun _ => ρ*‖b‖^2) (by fun_prop)
      continuous_const).inter (isOpen_lt (f := fun c : ℂ => ‖c‖) (g := fun _ => R)
      (by fun_prop) continuous_const)
  have hc0W : c0 ∈ W := by
    refine ⟨?_, by simp [R]⟩
    rw [hρ, div_add_one hB.ne', div_div, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith
  have hd : DifferentiableOn ℂ (fun c => ∑' n, heineSqTerm q e a b c n) W := by
    refine differentiableOn_tsum_of_summable_norm
      ((((summable_geometric_of_lt_one hρ0.le hρ1).mul_right _).mul_left _).mul_left _)
      (fun n c hc => ?_) hW (fun n c hc => norm_heineSqTerm_le hq he ha hb hρ0 le_rfl hc.2.le
        hc.1.le hK n)
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold heineSqTerm
    exact (differentiableAt_qPochhammerInf_comp hQ (by fun_prop)).mul
      ((differentiableAt_const _).mul (by fun_prop))
  exact (hd.differentiableAt (hW.mem_nhds hc0W)).differentiableWithinAt

/-- A point outside a closed disk about the origin is nonzero. -/
private lemma ne_zero_of_norm_lt_norm_sq {r : ℝ} {b : ℂ} (hr : 0 ≤ r) (h : r < ‖b^2‖) :
    b ≠ 0 := by
  rintro rfl; simp at h; linarith

/-- Two-step analytic continuation: an identity `F b c = G b c` between functions holomorphic in
each variable on `‖ca‖ < ‖b²‖`, known for `‖c‖ < ‖b²‖ < 1`, holds on the whole domain. The first
step continues in `b` along a half-plane for small `c`, the second in `c` over a disk. -/
private lemma eq_of_two_step_continuation {F G : ℂ → ℂ → ℂ} {a : ℂ} (ha : ‖a‖ ≤ 1)
    (hF1 : ∀ c, DifferentiableOn ℂ (fun b => F b c) {b | ‖c*a‖ < ‖b^2‖})
    (hG1 : ∀ c, DifferentiableOn ℂ (fun b => G b c) {b | ‖c*a‖ < ‖b^2‖})
    (hF2 : ∀ b, b≠0 → DifferentiableOn ℂ (fun c => F b c) {c | ‖c*a‖ < ‖b^2‖})
    (hG2 : ∀ b, b≠0 → DifferentiableOn ℂ (fun c => G b c) {c | ‖c*a‖ < ‖b^2‖})
    (hdir : ∀ b c, c≠0 → ‖c‖<1 → ‖b‖<1 → ‖c‖<‖b^2‖ → F b c = G b c)
    {b c : ℂ} (hb : b≠0) (hz : ‖c*a‖<‖b^2‖) : F b c = G b c := by
  have step1 : ∀ b c, c≠0 → ‖c‖<1 → ‖c*a‖<‖b^2‖ → F b c = G b c := by
    intro b c hc0 hc1 hz
    set r := ‖c*a‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hb := ne_zero_of_norm_lt_norm_sq hr0 hz
    have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hsb : √r < ‖b‖ := (Real.sqrt_lt' hbn).mpr (by rwa [← norm_pow])
    set s := √r/‖b‖ with hs
    set U := {b' : ℂ | r < ‖b'^2‖}
    set V := (fun w => w*b) '' {w : ℂ | s < w.re}
    have hVo : IsOpen V :=
      (Homeomorph.mulRight₀ b hb).isOpenMap _ (isOpen_lt continuous_const continuous_re)
    have hVc : IsPreconnected V :=
      (convex_halfSpace_re_gt s).isPreconnected.image _
        (continuous_id.mul continuous_const).continuousOn
    have hVU : V ⊆ U := by
      rintro _ ⟨w, hw, rfl⟩
      show r < ‖(w*b)^2‖
      rw [norm_pow, norm_mul]
      have : √r < ‖w‖*‖b‖ := by
        calc √r = s*‖b‖ := by rw [hs]; field_simp
          _ < w.re*‖b‖ := mul_lt_mul_of_pos_right hw hbn
          _ ≤ ‖w‖*‖b‖ := mul_le_mul_of_nonneg_right (re_le_norm w) (norm_nonneg _)
      exact (Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) this)).mp this
    have hbV : b ∈ V := by
      refine ⟨1, ?_, one_mul b⟩
      show s < (1:ℂ).re
      rw [one_re, hs, div_lt_one hbn]; exact hsb
    have hcn : √‖c‖ < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using hc1)
    have hrc : √r ≤ √‖c‖ := Real.sqrt_le_sqrt (by
      rw [hr, norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) ha)
    set w₀ : ℝ := (√‖c‖/‖b‖+1/‖b‖)/2 with hw₀
    have hst : s ≤ √‖c‖/‖b‖ := by rw [hs]; exact div_le_div_of_nonneg_right hrc hbn.le
    have ht1 : √‖c‖/‖b‖ < 1/‖b‖ := div_lt_div_of_pos_right hcn hbn
    have hw0 : 0 < w₀ := by
      have : 0 ≤ √‖c‖/‖b‖ := by positivity
      rw [hw₀]; linarith
    have hz₀V : (w₀:ℂ)*b ∈ V :=
      ⟨w₀, by simp only [Set.mem_ofPred_eq, ofReal_re]; rw [hw₀]; linarith, rfl⟩
    have hnz : ‖(w₀:ℂ)*b‖ = w₀*‖b‖ := by rw [norm_mul, norm_real, Real.norm_of_nonneg hw0.le]
    have hz1 : ‖(w₀:ℂ)*b‖ < 1 := by
      rw [hnz, ← lt_div_iff₀ hbn, hw₀]
      linarith
    have hz2 : ‖c‖ < ‖((w₀:ℂ)*b)^2‖ := by
      rw [norm_pow, hnz]
      refine (Real.sqrt_lt' (by positivity)).mp ?_
      rw [← div_lt_iff₀ hbn, hw₀]
      linarith
    have hev : (fun b' => F b' c) =ᶠ[𝓝 ((w₀:ℂ)*b)] fun b' => G b' c := by
      have e1 : ∀ᶠ z in 𝓝 ((w₀:ℂ)*b), ‖z‖ < 1 :=
        (continuous_norm.tendsto _).eventually (eventually_lt_nhds hz1)
      have e2 : ∀ᶠ z in 𝓝 ((w₀:ℂ)*b), ‖c‖ < ‖z^2‖ :=
        ((continuous_norm.comp (continuous_pow 2)).tendsto _).eventually
          (eventually_gt_nhds hz2)
      filter_upwards [e1, e2] with z h1 h2
      exact hdir z c hc0 hc1 h1 h2
    exact ((hF1 c).mono hVU |>.analyticOnNhd hVo).eqOn_of_preconnected_of_eventuallyEq
      ((hG1 c).mono hVU |>.analyticOnNhd hVo) hVc hz₀V hev hbV
  set U := {c' : ℂ | ‖c'*a‖ < ‖b^2‖}
  have hUo : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hUc : Convex ℝ U := by
    intro x hx y hy s t hs ht hst
    have hx' : ‖x*a‖ < ‖b^2‖ := hx
    have hy' : ‖y*a‖ < ‖b^2‖ := hy
    show ‖(s•x+t•y)*a‖ < ‖b^2‖
    have hle : ‖(s•x+t•y)*a‖ ≤ s*‖x*a‖+t*‖y*a‖ := by
      rw [add_mul, Complex.real_smul, Complex.real_smul, mul_assoc, mul_assoc]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      simp [abs_of_nonneg hs, abs_of_nonneg ht]
    rcases hs.eq_or_lt with rfl | hs'
    · simp only [zero_add] at hst; subst hst; linarith
    · have h1 := mul_pos hs' (sub_pos.2 hx')
      have h2 := mul_nonneg ht (sub_pos.2 hy').le
      have h3 : ‖b^2‖ = (s+t)*‖b^2‖ := by rw [hst, one_mul]
      nlinarith
  have h0 : (0:ℂ) ∈ U := by
    show ‖0*a‖ < ‖b^2‖
    rw [zero_mul, norm_zero, norm_pow]
    exact pow_pos (norm_pos_iff.mpr hb) 2
  have hfreq : ∃ᶠ c' in 𝓝[≠] (0:ℂ), F b c' = G b c' := by
    refine Filter.Eventually.frequently ?_
    have e1 : ∀ᶠ c' in 𝓝 (0:ℂ), ‖c'‖ < 1 :=
      (continuous_norm.tendsto _).eventually (eventually_lt_nhds (by simp))
    have e2 : ∀ᶠ c' in 𝓝 (0:ℂ), c' ∈ U := hUo.mem_nhds h0
    filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin]
      with c' h1 h2 h3
    exact step1 b c' h3 h1 h2
  exact ((hF2 b hb).analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    ((hG2 b hb).analyticOnNhd hUo) hUc.isPreconnected h0 hfreq hz

/-- The right side of the even Heine sum, cleared of the lower-parameter product. -/
private def evenHeineRhs (q b c : ℂ) : ℂ :=
  qPochhammerInf q (q^2)/(2*qPochhammerInf (c*q/b^2) (q^2))*
    (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+qPochhammerInf b q*qPochhammerInf (-c/b) q)

/-- Clearing `(c;q²)_∞` from the right side of the even sum. -/
private lemma rhs_even_heine_mul {b c q : ℂ} (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c] (q^2)) :
    qPochhammerInf q (q^2)/(2*qPochhammerListInf [c,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+
         qPochhammerInf b q*qPochhammerInf (-c/b) q)*qPochhammerInf c (q^2) =
      evenHeineRhs q b c := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hcI : qPochhammerInf c (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hc c (by simp) n (sub_eq_zero.mp h).symm
  simp only [evenHeineRhs, qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  field_simp

/-- The cleared right side of the even sum is holomorphic in each variable. -/
private lemma differentiableAt_evenHeineRhs {q b c : ℂ} (hq : ‖q‖<1) (hb : b≠0)
    (hz : ‖c*q‖ < ‖b^2‖) :
    DifferentiableAt ℂ (fun b => evenHeineRhs q b c) b ∧
      DifferentiableAt ℂ (fun c => evenHeineRhs q b c) c := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hw : ‖c*q/b^2‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb))]; exact hz
  have hd : 2*qPochhammerInf (c*q/b^2) (q^2) ≠ 0 :=
    mul_ne_zero two_ne_zero (qPochhammerInf_ne_zero_of_norm_lt_one hw hQ)
  have hP : ∀ x, DifferentiableAt ℂ (fun y => qPochhammerInf y q) x :=
    differentiable_qPochhammerInf_left hq
  have hP2 : ∀ x, DifferentiableAt ℂ (fun y => qPochhammerInf y (q^2)) x :=
    differentiable_qPochhammerInf_left hQ
  have hb2 : b^2 ≠ 0 := pow_ne_zero 2 hb
  unfold evenHeineRhs
  constructor
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)

/-- A parameter of modulus less than one is regular in base `q²`. -/
private lemma regular_of_norm_lt_one {d q : ℂ} (hq : ‖q‖<1) (hd : ‖d‖<1) :
    QDenominatorRegular [d] (q^2) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  intro di hdi n h
  simp only [List.mem_singleton] at hdi
  subst hdi
  exact one_sub_mul_pow_ne_zero_of_norm hd hQ n (by rw [h, sub_self])

/-- The cancelled product form retains b=±q^(-m) whenever the left series is regular. -/
@[dlmf 17.6.E4]
theorem q_even_heine {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1) (hz : ‖c*q‖<‖b^2‖)
    (hc : QDenominatorRegular [c] (q^2)) :
    qPhi [b^2,b^2/c] [c] (q^2) (c*q/b^2)=
      qPochhammerInf q (q^2)/(2*qPochhammerListInf [c,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+
         qPochhammerInf b q*qPochhammerInf (-c/b) q) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hmul : ∀ b c : ℂ, b≠0 → c≠0 → QDenominatorRegular [c] (q^2) →
      qPhi [b^2,b^2/c] [c] (q^2) (c*q/b^2)*qPochhammerInf c (q^2) =
        ∑' n, heineSqTerm q 1 q b c n := fun b c hb hc0 hc => by
    simpa using qPhi_heineSq_mul (e := 1) (a := q) hb hc0 hq (by simpa using hc)
  have key := eq_of_two_step_continuation (F := fun b c => ∑' n, heineSqTerm q 1 q b c n)
    (G := evenHeineRhs q) hq.le
    (fun c => differentiableOn_heineSq_left hq (by simp) hq.le)
    (fun c b hb => (differentiableAt_evenHeineRhs hq
      (ne_zero_of_norm_lt_norm_sq (norm_nonneg _) hb) hb).1.differentiableWithinAt)
    (fun b hb => differentiableOn_heineSq_right hq (by simp) hq.le hb)
    (fun b hb c hc => (differentiableAt_evenHeineRhs hq hb hc).2.differentiableWithinAt)
    (fun b c hc0 hc1 hb1 hz => by
      have hreg := regular_of_norm_lt_one hq hc1
      have hz' : ‖c*q‖ < ‖b^2‖ := lt_of_le_of_lt (by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hq.le) hz
      have hb' := ne_zero_of_norm_lt_norm_sq (norm_nonneg _) hz
      rw [← hmul b c hb' hc0 hreg, ← rhs_even_heine_mul hq hreg,
        q_even_heine_direct hb' hc0 hq hb1 hz' hreg])
    hb hz
  have hcI : qPochhammerInf c (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hc c (by simp) n (sub_eq_zero.mp h).symm
  have h1 := hmul b c hb hc0 hc
  rw [key, ← rhs_even_heine_mul (b := b) hq hc] at h1
  exact mul_right_cancel₀ hcI h1

/-- The right side of the odd Heine sum, cleared of both lower-parameter products. -/
private def oddHeineRhs (q b c : ℂ) : ℂ :=
  qPochhammerInf q (q^2)/(2*b)*
    (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-qPochhammerInf b q*qPochhammerInf (-c*q/b) q)

/-- Clearing both lower-parameter products from the right side of the odd sum. -/
private lemma rhs_odd_heine_mul {b c q : ℂ} (hb : b≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [c*q^2] (q^2))
    (hd : qPochhammerInf (c*q/b^2) (q^2)≠0) :
    qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
         qPochhammerInf b q*qPochhammerInf (-c*q/b) q)*
      (qPochhammerInf (c*q^2) (q^2)*qPochhammerInf (c*q/b^2) (q^2)) = oddHeineRhs q b c := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hcI : qPochhammerInf (c*q^2) (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hc (c*q^2) (by simp) n (sub_eq_zero.mp h).symm
  simp only [oddHeineRhs, qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  generalize qPochhammerInf (c*q^2) (q^2) = A at hcI ⊢
  generalize qPochhammerInf (c*q/b^2) (q^2) = B at hd ⊢
  field_simp

/-- The odd Heine identity, cleared of both lower-parameter products, on its whole domain. -/
private lemma oddHeine_cleared {b c q : ℂ} (hb : b≠0) (hq : ‖q‖<1) (hz : ‖c*q^3‖<‖b^2‖) :
    qPochhammerInf (c*q/b^2) (q^2)*∑' n, heineSqTerm q (q^2) (q^3) b c n =
      oddHeineRhs q b c := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have he : ‖q^2‖ ≤ 1 := hQ.le
  have ha : ‖q^3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg q) hq.le
  have hP : ∀ x, DifferentiableAt ℂ (fun y => qPochhammerInf y q) x :=
    differentiable_qPochhammerInf_left hq
  have hP2 : ∀ x, DifferentiableAt ℂ (fun y => qPochhammerInf y (q^2)) x :=
    differentiable_qPochhammerInf_left hQ
  have hG : ∀ b c : ℂ, b≠0 → DifferentiableAt ℂ (fun b => oddHeineRhs q b c) b ∧
      DifferentiableAt ℂ (fun c => oddHeineRhs q b c) c := fun b c hb => by
    have h2b : 2*b ≠ 0 := mul_ne_zero two_ne_zero hb
    unfold oddHeineRhs
    constructor
    · fun_prop (disch := assumption)
    · fun_prop (disch := assumption)
  have key := eq_of_two_step_continuation
    (F := fun b c => qPochhammerInf (c*q/b^2) (q^2)*∑' n, heineSqTerm q (q^2) (q^3) b c n)
    (G := oddHeineRhs q) ha
    (fun c b hb => by
      have hb' := ne_zero_of_norm_lt_norm_sq (norm_nonneg _) hb
      have hb2 : b^2 ≠ 0 := pow_ne_zero 2 hb'
      exact (differentiableAt_qPochhammerInf_comp hQ (by fun_prop (disch := assumption))
        ).differentiableWithinAt.mul (differentiableOn_heineSq_left hq he ha b hb))
    (fun c b hb =>
      (hG b c (ne_zero_of_norm_lt_norm_sq (norm_nonneg _) hb)).1.differentiableWithinAt)
    (fun b hb c hc => by
      have hb2 : b^2 ≠ 0 := pow_ne_zero 2 hb
      exact (differentiableAt_qPochhammerInf_comp hQ (by fun_prop (disch := assumption))
        ).differentiableWithinAt.mul (differentiableOn_heineSq_right hq he ha hb c hc))
    (fun b hb c _ => (hG b c hb).2.differentiableWithinAt)
    (fun b c hc0 hc1 hb1 hz => by
      have hb' := ne_zero_of_norm_lt_norm_sq (norm_nonneg _) hz
      have hreg := regular_of_norm_lt_one hq (d := c*q^2) (by
        rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) he) hc1)
      have hz' : ‖c*q^3‖ < ‖b^2‖ := lt_of_le_of_lt (by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) ha) hz
      have hw : ‖c*q/b^2‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb')), norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hq.le) hz
      have hd' := qPochhammerInf_ne_zero_of_norm_lt_one hw hQ
      rw [← qPhi_heineSq_mul hb' hc0 hq hreg, ← rhs_odd_heine_mul hb' hq hreg hd',
        q_odd_heine_direct hb' hc0 hq hb1 hz' hreg hd']
      ring)
    hb hz
  exact key

/-- A base-`q²` summation of `2φ1(b²,b²/c;cq²;q²,cq³/b²)` as a combination of infinite products
(DLMF 17.6.E4, E5). -/
@[dlmf 17.6.E4_5]
theorem q_odd_heine {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1) (hz : ‖c*q^3‖<‖b^2‖)
    (hc : QDenominatorRegular [c*q^2] (q^2))
    (hd : qPochhammerInf (c*q/b^2) (q^2)≠0) :
    qPhi [b^2,b^2/c] [c*q^2] (q^2) (c*q^3/b^2)=
      qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
         qPochhammerInf b q*qPochhammerInf (-c*q/b) q) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have key := oddHeine_cleared hb hq hz
  have hcI : qPochhammerInf (c*q^2) (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hc (c*q^2) (by simp) n (sub_eq_zero.mp h).symm
  have h1 := qPhi_heineSq_mul hb hc0 hq hc (a := q^3)
  rw [← h1, ← rhs_odd_heine_mul hb hq hc hd] at key
  refine mul_right_cancel₀ (mul_ne_zero hcI hd) ?_
  linear_combination key

/-- The only additional common product zero inside the stated convergence domain is handled as a
removable limit. -/
@[dlmf 17.6.E4_5]
theorem q_odd_heine_removable {b q : ℂ} (hb : b≠0) (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [b^2*q] (q^2)) :
    Tendsto (fun c : ℂ => qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
      (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
       qPochhammerInf b q*qPochhammerInf (-c*q/b) q))
      (𝓝[≠] (b^2/q)) (𝓝 (qPhi [b^2,q] [b^2*q] (q^2) (q^2))) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have he : ‖q^2‖ ≤ 1 := hQ.le
  have ha : ‖q^3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg q) hq.le
  have hc₀ : b^2/q ≠ 0 := div_ne_zero (pow_ne_zero 2 hb) hq0
  have hdom : b^2/q ∈ {c : ℂ | ‖c*q^3‖ < ‖b^2‖} := by
    show ‖b^2/q*q^3‖ < ‖b^2‖
    rw [show b^2/q*q^3 = b^2*q^2 by field_simp, norm_mul]
    exact mul_lt_of_lt_one_right (norm_pos_iff.mpr (pow_ne_zero 2 hb)) hQ
  have hopen : IsOpen {c : ℂ | ‖c*q^3‖ < ‖b^2‖} := isOpen_lt (by fun_prop) continuous_const
  have hreg : QDenominatorRegular [b^2/q*q^2] (q^2) := by
    rwa [show b^2/q*q^2 = b^2*q by field_simp]
  have hA0 : qPochhammerInf (b^2/q*q^2) (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hreg _ (by simp) n (sub_eq_zero.mp h).symm
  have hlim : Tendsto (fun c => (∑' n, heineSqTerm q (q^2) (q^3) b c n)/
      qPochhammerInf (c*q^2) (q^2)) (𝓝 (b^2/q))
      (𝓝 ((∑' n, heineSqTerm q (q^2) (q^3) b (b^2/q) n)/qPochhammerInf (b^2/q*q^2) (q^2))) := by
    have h1 : ContinuousAt (fun c => ∑' n, heineSqTerm q (q^2) (q^3) b c n) (b^2/q) :=
      ((differentiableOn_heineSq_right hq he ha hb).differentiableAt
        (hopen.mem_nhds hdom)).continuousAt
    have h2 : ContinuousAt (fun c : ℂ => qPochhammerInf (c*q^2) (q^2)) (b^2/q) :=
      (differentiableAt_qPochhammerInf_comp (g := fun c : ℂ => c*q^2) hQ
        (by fun_prop)).continuousAt
    exact (h1.div h2 hA0).tendsto
  have hval : (∑' n, heineSqTerm q (q^2) (q^3) b (b^2/q) n)/qPochhammerInf (b^2/q*q^2) (q^2) =
      qPhi [b^2,q] [b^2*q] (q^2) (q^2) := by
    have h := qPhi_heineSq_mul (a := q^3) hb hc₀ hq hreg
    rw [← h, mul_div_cancel_right₀ _ hA0, show b^2/(b^2/q) = q by field_simp,
      show b^2/q*q^2 = b^2*q by field_simp, show b^2/q*q^3/b^2 = q^2 by field_simp]
  rw [← hval]
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  have hQI : qPochhammerInf (q^2) (q^2) ≠ 0 := qPochhammerInf_ne_zero hQ fun n => by
    simpa [pow_succ, mul_comm] using qPochhammerInf_pow_succ_ne_zero hQ n
  have e2 : ∀ᶠ c in 𝓝 (b^2/q), qPochhammerInf (c*q/b^2*q^2) (q^2) ≠ 0 := by
    have hcont : ContinuousAt (fun c : ℂ => qPochhammerInf (c*q/b^2*q^2) (q^2)) (b^2/q) :=
      (differentiableAt_qPochhammerInf_comp (g := fun c : ℂ => c*q/b^2*q^2) hQ
        (by fun_prop)).continuousAt
    refine hcont.eventually_ne ?_
    rwa [show b^2/q*q/b^2*q^2 = q^2 by field_simp]
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hdom), nhdsWithin_le_nhds e2,
    self_mem_nhdsWithin] with c h1 h2 h3
  have h3' : 1-c*q/b^2 ≠ 0 := by
    intro h; apply h3
    show c = b^2/q
    rw [eq_div_iff hq0]
    exact (div_eq_one_iff_eq (pow_ne_zero 2 hb)).mp (sub_eq_zero.mp h).symm
  have hB : qPochhammerInf (c*q/b^2) (q^2) ≠ 0 := by
    rw [qPochhammerInf_shift hQ]; exact mul_ne_zero h3' h2
  have key := oddHeine_cleared hb hq h1
  have hR : qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
      (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
       qPochhammerInf b q*qPochhammerInf (-c*q/b) q) =
      oddHeineRhs q b c/(qPochhammerInf (c*q/b^2) (q^2)*qPochhammerInf (c*q^2) (q^2)) := by
    simp only [oddHeineRhs, qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    ring
  rw [hR, ← key, mul_div_mul_left _ _ hB]

end DLMF.QHypergeometric
