/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BasicSummations
public import DLMF.QHypergeometric.Transformations

/-!
# The `₂φ₂` summations (DLMF 17.7.1–17.7.3)

The three `₂φ₂` summation formulas at the head of DLMF §17.7. The first two are reduced to
Jackson's transformation (DLMF 17.9.1) followed by the `q`-binomial theorem in base `q²`,
respectively the Bailey–Daum sum (DLMF 17.6.5); the third to Jackson's transformation followed
by the even base-`q²` sum (DLMF 17.6.4). Both sides are cleared of the lower-parameter
products and continued analytically in the parameters, so the identities hold for every value
of the parameters at which the left series is defined.

## Main results

* `qPochhammerInf_neg_mul_odd`: Euler's identity `(-q;q)_∞ (q;q²)_∞ = 1`.
* `two_phi_two_sum`, `two_phi_two_square_sum`, `two_phi_two_even_sum`: DLMF 17.7.1–17.7.3.
-/

@[expose] public noncomputable section
open Complex Filter Finset DLMF.QSeries
open scoped Topology
namespace DLMF.QHypergeometric

/-- Euler's identity `(-q;q)_∞ (q;q²)_∞ = 1` for `|q| < 1`. -/
theorem qPochhammerInf_neg_mul_odd {q : ℂ} (hq : ‖q‖<1) :
    qPochhammerInf (-q) q*qPochhammerInf q (q^2) = 1 := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have h1 := qPochhammerInf_split_sq (a := q) hq
  have h2 := qPochhammerInf_mul_qPochhammerInf_neg (x := q) hq
  rw [h1, show q*q = q^2 by ring] at h2
  have h3 : qPochhammerInf (q^2) (q^2) ≠ 0 := qPochhammerInf_ne_zero hQ fun n => by
    simpa [pow_succ, mul_comm] using qPochhammerInf_pow_succ_ne_zero hQ n
  have : qPochhammerInf (q^2) (q^2)*(qPochhammerInf (-q) q*qPochhammerInf q (q^2) - 1) = 0 := by
    linear_combination h2
  simpa [h3, sub_eq_zero] using this

/-- `a ↦ (g(a);q)_k` is entire when `g` is. -/
private lemma differentiable_qPochhammer_comp {q : ℂ} {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (k : ℕ) : Differentiable ℂ fun a : ℂ => qPochhammer (g a) q k := by
  induction k with
  | zero => simp [qPochhammer_zero]
  | succ k ih =>
    simp only [qPochhammer_succ]
    exact ih.mul ((differentiable_const _).sub (hg.mul (differentiable_const _)))

/-- The `2φ2` summation `2φ2(a,q/a;-q,b;q,-b) = (ab,bq/a;q²)_∞/(b;q)_∞` (DLMF 17.7.E1). -/
@[dlmf 17.7.E1]
theorem two_phi_two_sum {a b q : ℂ} (ha : a≠0) (hq : ‖q‖<1) (hd : QDenominatorRegular [-q,b] q) :
    qPhi [a,q/a] [-q,b] q (-b)=qPochhammerListInf [a*b,b*q/a] (q^2)/qPochhammerInf b q := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hmq : ∀ n, qPochhammer (-q) q n≠0 := fun n =>
    qPochhammer_ne_zero_of_factors hq (fun j h => hd (-q) (by simp) j (sub_eq_zero.mp h).symm) n
  have hqn := qPochhammer_self_ne_zero hq
  have htri (k : ℕ) : DLMF.QSeries.TripleProduct.tri (k:ℤ) = ((k.choose 2 : ℕ) : ℤ) := by
    simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast k 0).symm
  set c : ℕ → ℂ := fun n => qPochhammer a q n*qPochhammer (q/a) q n/
    (qPochhammer (-q) q n*qPochhammer q q n)
  set F : ℂ → ℂ := fun x => ∑' n, c n*q^(n.choose 2)*(x^n*qPochhammerInf (x*q^n) q)
  set G : ℂ → ℂ := fun x => qPochhammerInf (a*x) (q^2)*qPochhammerInf (x*q/a) (q^2)
  -- `F = (x;q)_∞ · ₂φ₂` for regular `x`
  have hFphi : ∀ x : ℂ, QDenominatorRegular [-q,x] q →
      F x = qPochhammerInf x q*qPhi [a,q/a] [-q,x] q (-x) := by
    intro x hx
    rw [qPhi, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hxn := qPochhammer_ne_zero_of_factors hq
      (fun j h => hx x (by simp) j (sub_eq_zero.mp h).symm) n
    simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil, htri, c]
    rw [qPochhammerInf_mul_qPochhammer (a := x) hq n]
    norm_num
    have := hmq n; have := hqn n
    field_simp
    have e : (-1:ℂ)^n*(-1)^n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-(qPochhammer a q n*qPochhammer (q/a) q n*q^n.choose 2*x^n*
      qPochhammerInf (x*q^n) q))*e
  -- `F` is entire
  obtain ⟨C1,hC1⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_ne_zero hq fun n h => hd (-q) (by simp) n (sub_eq_zero.mp h).symm)
  obtain ⟨C2,hC2⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_ne_zero hq fun n => by
      simpa [pow_succ, mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n)
  have hcb (n : ℕ) : ‖c n‖ ≤ Real.exp (‖a‖/(1-‖q‖))*Real.exp (‖q/a‖/(1-‖q‖))*C1*C2 := by
    simp only [c]
    rw [div_eq_mul_inv, mul_inv]
    simp only [norm_mul]
    have h1 := norm_qPochhammer_le_exp (w := a) hq n
    have h2 := norm_qPochhammer_le_exp (w := q/a) hq n
    have h3 := hC1 n
    have h4 := hC2 n
    have : 0 ≤ C1 := (norm_nonneg _).trans h3
    rw [show ‖qPochhammer a q n‖*‖qPochhammer (q/a) q n‖*(‖(qPochhammer (-q) q n)⁻¹‖*
      ‖(qPochhammer q q n)⁻¹‖) = ‖qPochhammer a q n‖*‖qPochhammer (q/a) q n‖*
      ‖(qPochhammer (-q) q n)⁻¹‖*‖(qPochhammer q q n)⁻¹‖ by ring]
    gcongr
  set M := Real.exp (‖a‖/(1-‖q‖))*Real.exp (‖q/a‖/(1-‖q‖))*C1*C2
  have hM : 0 ≤ M := (norm_nonneg _).trans (hcb 0)
  have hFd : Differentiable ℂ F := by
    intro x0
    set R := ‖x0‖+1
    have hd' : DifferentiableOn ℂ F (Metric.ball 0 R) := by
      refine differentiableOn_tsum_of_summable_norm
        (u := fun n => M*(R^n*‖q‖^(n.choose 2))*Real.exp (R/(1-‖q‖)))
        (((summable_pow_mul_pow_choose_two (by positivity) (norm_nonneg q) hq).mul_left M).mul_right
          _) ?_ Metric.isOpen_ball ?_
      · intro n
        exact (((differentiable_id.pow n).mul ((differentiable_qPochhammerInf_left hq).comp
          (differentiable_id.mul_const _))).const_mul _).differentiableOn
      · intro n x hx
        have hxR : ‖x‖ ≤ R := by simpa using (Metric.mem_ball.mp hx).le
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
        have h2 : ‖qPochhammerInf (x*q^n) q‖ ≤ Real.exp (R/(1-‖q‖)) := by
          refine (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr
            (div_le_div_of_nonneg_right ?_ (by linarith [norm_nonneg q])))
          rw [norm_mul, norm_pow]
          exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)).trans
            hxR
        have h3 : ‖x‖^n ≤ R^n := pow_le_pow_left₀ (norm_nonneg _) hxR n
        have := hcb n
        calc ‖c n‖*‖q‖^(n.choose 2)*(‖x‖^n*‖qPochhammerInf (x*q^n) q‖)
            = ‖c n‖*(‖x‖^n*‖q‖^(n.choose 2))*‖qPochhammerInf (x*q^n) q‖ := by ring
          _ ≤ M*(R^n*‖q‖^(n.choose 2))*Real.exp (R/(1-‖q‖)) := by gcongr
    exact hd'.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))
  have hGd : Differentiable ℂ G := by
    have hP := differentiable_qPochhammerInf_left hQ
    exact (hP.comp (differentiable_id.const_mul _)).mul
      (hP.comp ((differentiable_id.mul_const _).div_const _))
  -- the identity for small `x`, from Jackson's transformation and the `q`-binomial theorem
  set ρ := min 1 ‖a‖/2 with hρ
  have hρ0 : 0<ρ := by rw [hρ]; have := norm_pos_iff.mpr ha; positivity
  have key : ∀ x : ℂ, x ∈ Metric.ball (ρ : ℂ) ρ → F x = G x := by
    intro x hx
    have hxn : ‖x‖<2*ρ := by
      have := norm_sub_norm_le x ρ
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h' : ‖(ρ:ℂ)‖ = ρ := by simp [abs_of_pos hρ0]
      linarith
    have hx1 : ‖x‖<1 := hxn.trans_le (by rw [hρ]; linarith [min_le_left 1 ‖a‖])
    have hxa : ‖x/a‖<1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.mpr ha)]
      exact hxn.trans_le (by rw [hρ]; linarith [min_le_right 1 ‖a‖])
    have hreg : ∀ {w : ℂ}, ‖w‖<1 → ∀ n : ℕ, w*q^n≠1 := fun hw n h =>
      one_sub_mul_pow_ne_zero_of_norm hw hq n (by rw [h]; ring)
    have hxr : QDenominatorRegular [-q,x] q := by
      intro y hy n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact hd (-q) (by simp) n
      · exact hreg hx1 n
    rw [hFphi x hxr]
    have hJ := qPhi2_to_qPhi2_2' a (-a) (-q) q (x/a) hq (by simpa using ha) (by
      intro y hy n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact hd (-q) (by simp) n
      · rw [show a*(x/a) = x by field_simp]; exact hreg hx1 n
      · exact hreg hxa n) hxa
    rw [show -q/(-a) = q/a by field_simp, show a*(x/a) = x by field_simp,
      show -a*(x/a) = -x by field_simp] at hJ
    have hsum : qPhi [a,-a] [-q] q (x/a) =
        qPochhammerInf (a*x) (q^2)/qPochhammerInf (x/a) (q^2) := by
      rw [qPhi_eq_basicHypergeometric (by simp), show a*x = a^2*(x/a) by field_simp,
        q_binomial_theorem hQ hxa]
      simp only [basicHypergeometric, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one]
      refine tsum_congr fun n => ?_
      rw [qPochhammer_squared, qPochhammer_squared]
      ring
    have hxI : qPochhammerInf x q≠0 := qPochhammerInf_ne_zero_of_norm_lt_one hx1 hq
    have hxaI : qPochhammerInf (x/a) (q^2)≠0 := qPochhammerInf_ne_zero_of_norm_lt_one hxa hQ
    have hJ' : qPhi [a,q/a] [-q,x] q (-x) = qPochhammerInf (x/a) q/qPochhammerInf x q*
        qPhi [a,-a] [-q] q (x/a) := by
      rw [hJ]
      simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, show x/a*a = x by field_simp]
      have : qPochhammerInf (x/a) q≠0 := qPochhammerInf_ne_zero_of_norm_lt_one hxa hq
      field_simp
    rw [hJ', hsum, qPochhammerInf_split_sq (a := x/a) hq]
    simp only [G]
    rw [show x/a*q = x*q/a by ring]
    field_simp
  have hev : F =ᶠ[𝓝 (ρ:ℂ)] G := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ0)] with x hx
      using key x hx
  have hFG := AnalyticOnNhd.eq_of_eventuallyEq (fun x _ => hFd.analyticAt x)
    (fun x _ => hGd.analyticAt x) hev
  have hbI : qPochhammerInf b q≠0 :=
    qPochhammerInf_ne_zero hq fun n h => hd b (by simp) n (sub_eq_zero.mp h).symm
  have := hFphi b hd
  rw [hFG] at this
  rw [eq_div_iff hbI, mul_comm, ← this]
  simp only [G, qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]

/-- The `2φ2` summation at argument `-q` with lower parameters `±ab√q` (DLMF 17.7.E2). -/
@[dlmf 17.7.E2]
theorem two_phi_two_square_sum {a b q : ℂ} (hq : ‖q‖<1)
    (hd : QDenominatorRegular [a*b*Complex.sqrt q,-a*b*Complex.sqrt q] q) :
    qPhi [a^2,b^2] [a*b*Complex.sqrt q,-a*b*Complex.sqrt q] q (-q)=
      qPochhammerListInf [a^2*q,b^2*q] (q^2)/qPochhammerListInf [q,a^2*b^2*q] (q^2) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  by_cases hq0 : q = 0
  · subst hq0
    rw [qPhi]
    rw [tsum_eq_single 0 (fun n hn => by simp [qPhiTerm, zero_pow hn])]
    simp [qPhiTerm, qPochhammerListInf, qPochhammerList, qPochhammer_zero,
      DLMF.QSeries.TripleProduct.tri]
  set s := Complex.sqrt q with hsdef
  have hs : s^2 = q := by rw [hsdef, Complex.sqrt]; exact Complex.cpow_ofNat_inv_pow q 2
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hs; exact hq0 (by rw [← hs]; ring)
  have hsn : ‖s‖^2 = ‖q‖ := by rw [← norm_pow, hs]
  have hqn := qPochhammer_self_ne_zero hq
  have htri (k : ℕ) : DLMF.QSeries.TripleProduct.tri (k:ℤ) = ((k.choose 2 : ℕ) : ℤ) := by
    simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast k 0).symm
  -- the cleared series
  set K : ℂ → ℂ → ℂ := fun x y => ∑' n, qPochhammer (x^2) q n*qPochhammer (y^2) q n/
    qPochhammer q q n*(q^(n.choose 2)*q^n)*
    (qPochhammerInf (x*y*s*q^n) q*qPochhammerInf (-(x*y*s)*q^n) q)
  set G : ℂ → ℂ → ℂ := fun x y =>
    qPochhammerInf (-q) q*(qPochhammerInf (x^2*q) (q^2)*qPochhammerInf (y^2*q) (q^2))
  have hKsymm : ∀ x y, K x y = K y x := fun x y => tsum_congr fun n => by
    rw [mul_comm x y]; ring
  have hKphi : ∀ x y : ℂ, QDenominatorRegular [x*y*s,-x*y*s] q →
      K x y = qPochhammerInf (x*y*s) q*qPochhammerInf (-x*y*s) q*
        qPhi [x^2,y^2] [x*y*s,-x*y*s] q (-q) := by
    intro x y hxy
    rw [qPhi, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have h1 := qPochhammer_ne_zero_of_factors hq
      (fun j h => hxy (x*y*s) (by simp) j (sub_eq_zero.mp h).symm) n
    have h2 := qPochhammer_ne_zero_of_factors hq
      (fun j h => hxy (-x*y*s) (by simp) j (sub_eq_zero.mp h).symm) n
    rw [show -x*y*s = -(x*y*s) by ring] at h2 ⊢
    simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil, htri]
    rw [qPochhammerInf_mul_qPochhammer (a := x*y*s) hq n,
      qPochhammerInf_mul_qPochhammer (a := -(x*y*s)) hq n]
    norm_num
    have hph : ((-1:ℂ)^n*q^(n.choose 2))*(-q)^n = q^(n.choose 2)*q^n := by
      have e : (-1:ℂ)^n*(-1)^n = 1 := by rw [← mul_pow]; norm_num
      rw [neg_pow q n]
      linear_combination (q^(n.choose 2)*q^n)*e
    rw [mul_assoc _ _ ((-q)^n), hph]
    have := hqn n
    field_simp
  -- `K · y` is entire in the first variable
  obtain ⟨C2,hC2⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_ne_zero hq fun n => by
      simpa [pow_succ, mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n)
  have hC2' : 0 ≤ C2 := (norm_nonneg _).trans (hC2 0)
  have hKd : ∀ y, Differentiable ℂ fun x => K x y := by
    intro y x0
    set R := ‖x0‖+1
    set E1 := Real.exp (R^2/(1-‖q‖))
    set E2 := Real.exp (‖y^2‖/(1-‖q‖))
    set E3 := Real.exp (R*‖y*s‖/(1-‖q‖))
    have hd' : DifferentiableOn ℂ (fun x => K x y) (Metric.ball 0 R) := by
      refine differentiableOn_tsum_of_summable_norm (u := fun n => E1*E2*C2*‖q‖^n*(E3*E3))
        ((((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left (E1*E2*C2))).mul_right
          (E3*E3)) ?_ Metric.isOpen_ball ?_
      · intro n
        refine (((differentiable_qPochhammer_comp (differentiable_id.pow 2) n).mul_const
          _).div_const _ |>.mul_const _ |>.mul ?_).differentiableOn
        exact ((differentiable_qPochhammerInf_left hq).comp (by fun_prop)).mul
          ((differentiable_qPochhammerInf_left hq).comp (by fun_prop))
      · intro n x hx
        have hxR : ‖x‖ ≤ R := by simpa using (Metric.mem_ball.mp hx).le
        have hden : 0 < 1-‖q‖ := by linarith
        have h1 : ‖qPochhammer (x^2) q n‖ ≤ E1 := (norm_qPochhammer_le_exp hq n).trans
          (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by
            rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hxR 2) hden.le))
        have h2 : ‖qPochhammer (y^2) q n‖ ≤ E2 := norm_qPochhammer_le_exp hq n
        have hP : ∀ w : ℂ, ‖w‖ ≤ R*‖y*s‖ → ‖qPochhammerInf (w*q^n) q‖ ≤ E3 := by
          intro w hw
          refine (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr
            (div_le_div_of_nonneg_right ?_ hden.le))
          rw [norm_mul, norm_pow]
          exact (mul_le_of_le_one_right (norm_nonneg _)
            (pow_le_one₀ (norm_nonneg _) hq.le)).trans hw
        have hw1 : ‖x*y*s‖ ≤ R*‖y*s‖ := by
          rw [mul_assoc, norm_mul]; exact mul_le_mul_of_nonneg_right hxR (norm_nonneg _)
        have h3 := hP _ hw1
        have h4 := hP (-(x*y*s)) (by rw [norm_neg]; exact hw1)
        have h5 := hC2 n
        have h6 : ‖q^(n.choose 2)*q^n‖ ≤ ‖q‖^n := by
          rw [norm_mul, norm_pow, norm_pow]
          exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) hq.le)
        rw [div_eq_mul_inv]
        simp only [norm_mul]
        rw [norm_mul] at h6
        calc _ = ‖qPochhammer (x^2) q n‖*‖qPochhammer (y^2) q n‖*‖(qPochhammer q q n)⁻¹‖*
              (‖q^n.choose 2‖*‖q^n‖)*(‖qPochhammerInf (x*y*s*q^n) q‖*
              ‖qPochhammerInf (-(x*y*s)*q^n) q‖) := by ring
          _ ≤ E1*E2*C2*‖q‖^n*(E3*E3) := by gcongr
    exact hd'.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))
  have hGd : ∀ y, Differentiable ℂ fun x => G x y := fun y =>
    (((differentiable_qPochhammerInf_left hQ).comp (by fun_prop)).mul_const _).const_mul _
  -- the identity for `x ≠ 0` and small nonzero `y`
  have key : ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → ‖y‖ < ‖x‖/‖s‖ → ‖y‖ < 1/(‖x‖*‖s‖) → K x y = G x y := by
    intro x y hx hy h1 h2
    have hxs : 0 < ‖x‖*‖s‖ := by positivity
    have hxys : ‖x*y*s‖ < 1 := by
      rw [norm_mul, norm_mul]
      calc ‖x‖*‖y‖*‖s‖ = ‖y‖*(‖x‖*‖s‖) := by ring
        _ < 1/(‖x‖*‖s‖)*(‖x‖*‖s‖) := by gcongr
        _ = 1 := by field_simp
    have hysx : ‖-y*s/x‖ < 1 := by
      rw [norm_div, norm_mul, norm_neg, div_lt_one (norm_pos_iff.mpr hx)]
      calc ‖y‖*‖s‖ < ‖x‖/‖s‖*‖s‖ := by gcongr
        _ = ‖x‖ := by field_simp
    have hreg : ∀ {w : ℂ}, ‖w‖<1 → ∀ n : ℕ, w*q^n≠1 := fun hw n h =>
      one_sub_mul_pow_ne_zero_of_norm hw hq n (by rw [h]; ring)
    have hB : ‖q‖ < ‖x*s/y‖ := by
      rw [norm_div, norm_mul, lt_div_iff₀ (norm_pos_iff.mpr hy), ← hsn]
      calc ‖s‖^2*‖y‖ < ‖s‖^2*(‖x‖/‖s‖) := by gcongr
        _ = ‖x‖*‖s‖ := by field_simp
    have hxysr : QDenominatorRegular [x*y*s,-x*y*s] q := by
      intro w hw n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hreg hxys n
      · exact hreg (by rw [show -x*y*s = -(x*y*s) by ring, norm_neg]; exact hxys) n
    have hJ := qPhi2_to_qPhi2_2' (x^2) (x*s/y) (x*y*s) q (-y*s/x) hq
      (by simp [hx, hy, hs0]) (by
        intro w hw n
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact hreg hxys n
        · rw [show x^2*(-y*s/x) = -(x*y*s) by field_simp]
          exact hreg (by rw [norm_neg]; exact hxys) n
        · exact hreg hysx n) hysx
    have hBD := q_bailey_daum (a := x^2) (b := x*s/y) hq hB (by
      rw [show x^2*q/(x*s/y) = x*y*s by rw [← hs]; field_simp]
      intro w hw n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw; exact hreg hxys n)
    rw [show x^2*q/(x*s/y) = x*y*s by rw [← hs]; field_simp,
      show -q/(x*s/y) = -y*s/x by rw [← hs]; field_simp,
      show x^2*q^2/(x*s/y)^2 = y^2*q by rw [← hs]; field_simp] at hBD
    rw [show x*y*s/(x*s/y) = y^2 by field_simp, show x^2*(-y*s/x) = -x*y*s by field_simp,
      show x*s/y*(-y*s/x) = -q by rw [← hs]; field_simp, hBD] at hJ
    rw [hKphi x y hxysr]
    simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, show -y*s/x*x^2 = -x*y*s by field_simp] at hJ
    have hz1 : qPochhammerInf (-y*s/x) q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hysx hq
    have hz2 : qPochhammerInf (x*y*s) q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hxys hq
    have hz3 : qPochhammerInf (-x*y*s) q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one
      (by rw [show -x*y*s = -(x*y*s) by ring, norm_neg]; exact hxys) hq
    simp only [G]
    field_simp at hJ
    have hz1' : qPochhammerInf (-(y*s/x)) q ≠ 0 := by rwa [show -(y*s/x) = -y*s/x by ring]
    have hJ' := (div_left_inj' hz1').mp hJ
    rw [show -x*y*s = -(x*y*s) by ring, show x^2*q = q*x^2 by ring,
      show y^2*q = q*y^2 by ring, ← hJ']
    ring
  -- continuation in the second variable, then in the first
  have hA : ∀ x : ℂ, x ≠ 0 → ∀ y, K x y = G x y := by
    intro x hx
    set r := min (‖x‖/‖s‖) (1/(‖x‖*‖s‖)) with hr
    have hr0 : 0 < r := lt_min (by positivity) (by positivity)
    have hev : (fun y => K x y) =ᶠ[𝓝 ((r/2:ℝ):ℂ)] (fun y => G x y) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (by linarith : (0:ℝ) < r/2))] with y hy
      have h' : ‖((r/2:ℝ):ℂ)‖ = r/2 := by simp [abs_of_pos hr0]
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg, h'] at hy
        exact lt_irrefl _ hy
      have hyr : ‖y‖ < r := by
        have := norm_sub_norm_le y ((r/2:ℝ):ℂ)
        rw [Metric.mem_ball, dist_eq_norm] at hy
        linarith
      exact key x y hx hy0 (hyr.trans_le (min_le_left _ _)) (hyr.trans_le (min_le_right _ _))
    have dK : Differentiable ℂ fun y => K x y := by
      have h := hKd x
      rwa [show (fun y => K y x) = fun y => K x y from funext fun y => hKsymm y x] at h
    have dG : Differentiable ℂ fun y => G x y :=
      ((differentiable_qPochhammerInf_left hQ).comp (by fun_prop)).const_mul _ |>.const_mul _
    intro y
    exact congrFun (AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => dK.analyticAt z)
      (fun z _ => dG.analyticAt z) hev) y
  have hall : ∀ x y, K x y = G x y := by
    intro x y
    by_cases hx : x = 0
    · subst hx
      exact congrFun (Continuous.ext_on (dense_compl_singleton 0) (hKd y).continuous
        (hGd y).continuous fun x hx => hA x hx y) 0
    · exact hA x hx y
  -- conclusion at the given parameters
  have hK := hKphi a b hd
  rw [hall] at hK
  have hD : qPochhammerInf (a*b*s) q*qPochhammerInf (-a*b*s) q =
      qPochhammerInf (a^2*b^2*q) (q^2) := by
    rw [show -a*b*s = -(a*b*s) by ring, qPochhammerInf_mul_qPochhammerInf_neg hq,
      show (a*b*s)^2 = a^2*b^2*q by rw [← hs]; ring]
  have hDne : qPochhammerInf (a^2*b^2*q) (q^2) ≠ 0 := by
    rw [← hD]
    exact mul_ne_zero
      (qPochhammerInf_ne_zero hq fun n h => hd _ (by simp) n (sub_eq_zero.mp h).symm)
      (qPochhammerInf_ne_zero hq fun n h => hd _ (by simp) n (sub_eq_zero.mp h).symm)
  have hE := qPochhammerInf_neg_mul_odd hq
  have hqI : qPochhammerInf q (q^2) ≠ 0 := by
    intro h; rw [h, mul_zero] at hE; exact zero_ne_one hE
  rw [hD] at hK
  simp only [G] at hK
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [eq_div_iff (mul_ne_zero hqI hDne)]
  linear_combination (-qPochhammerInf q (q^2))*hK+
    (qPochhammerInf (a^2*q) (q^2)*qPochhammerInf (b^2*q) (q^2))*hE

/-- Symmetry of a two-numerator series in its upper parameters. -/
private lemma qPhi_two_swap (a₁ a₂ : ℂ) (b : List ℂ) (q z : ℂ) :
    qPhi [a₁,a₂] b q z = qPhi [a₂,a₁] b q z := by
  simp only [qPhi, qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.prod_cons,
    List.length_cons]
  exact tsum_congr fun n => by ring

/-- The `c`-independent factor of the terms of `₂φ₂(c²/b², b²; c, cq; q², q)`. -/
private def evenTwoTwoCoeff (q b : ℂ) (n : ℕ) : ℂ :=
  qPochhammer (b^2) (q^2) n/qPochhammer (q^2) (q^2) n*
    ((-1:ℂ)^n*(q^2)^DLMF.QSeries.TripleProduct.tri (n:ℤ))*q^n

/-- The terms of `₂φ₂(c²/b², b²; c, cq; q², q)` multiplied by `(c, cq;q²)_∞`. -/
private def evenTwoTwoTerm (q b c : ℂ) (n : ℕ) : ℂ :=
  qPochhammerInf (c*(q^2)^n) (q^2)*qPochhammerInf (c*q*(q^2)^n) (q^2)*
    (qPochhammer (c^2/b^2) (q^2) n*evenTwoTwoCoeff q b n)

/-- Clearing `(c, cq;q²)_∞` from the left side of DLMF 17.7.3. -/
private lemma qPhi_evenTwoTwo_mul {b c q : ℂ} (hq : ‖q‖<1)
    (hd : QDenominatorRegular [c, c*q] (q^2)) :
    qPhi [c^2/b^2,b^2] [c,c*q] (q^2) q*(qPochhammerInf c (q^2)*qPochhammerInf (c*q) (q^2)) =
      ∑' n, evenTwoTwoTerm q b c n := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  rw [qPhi, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  have h1 : qPochhammer c (q^2) n ≠ 0 := qPochhammer_ne_zero_of_factors hQ
    (fun j h => hd c (by simp) j (sub_eq_zero.mp h).symm) n
  have h2 : qPochhammer (c*q) (q^2) n ≠ 0 := qPochhammer_ne_zero_of_factors hQ
    (fun j h => hd (c*q) (by simp) j (sub_eq_zero.mp h).symm) n
  have hqn := qPochhammer_self_ne_zero hQ n
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
  rw [qPochhammerInf_mul_qPochhammer hQ n (a := c), qPochhammerInf_mul_qPochhammer hQ n (a := c*q),
    evenTwoTwoTerm, evenTwoTwoCoeff]
  norm_num
  field_simp

/-- A geometric bound for the `c`-independent factor. -/
private lemma norm_evenTwoTwoCoeff_le {q b : ℂ} {K : ℝ} (hq : ‖q‖<1)
    (hK : ∀ n, ‖(qPochhammer (q^2) (q^2) n)⁻¹‖ ≤ K) (n : ℕ) :
    ‖evenTwoTwoCoeff q b n‖ ≤ Real.exp (‖b^2‖/(1-‖q^2‖))*K*‖q‖^n := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have htri : DLMF.QSeries.TripleProduct.tri (n:ℤ) = ((n.choose 2 : ℕ) : ℤ) := by
    simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast n 0).symm
  have hph : ‖(-1:ℂ)^n*(q^2)^DLMF.QSeries.TripleProduct.tri (n:ℤ)‖ ≤ 1 := by
    rw [htri, zpow_natCast, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hQ.le
  rw [evenTwoTwoCoeff, norm_mul, norm_mul, div_eq_mul_inv, norm_mul, norm_pow]
  have h1 := norm_qPochhammer_le_exp (w := b^2) hQ n
  have h2 := hK n
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  calc ‖qPochhammer (b^2) (q^2) n‖*‖(qPochhammer (q^2) (q^2) n)⁻¹‖*
        ‖(-1:ℂ)^n*(q^2)^DLMF.QSeries.TripleProduct.tri (n:ℤ)‖*‖q‖^n
      ≤ Real.exp (‖b^2‖/(1-‖q^2‖))*K*1*‖q‖^n := by gcongr
    _ = _ := by ring

/-- The cleared series is entire in `c`. -/
private lemma differentiable_evenTwoTwo {q b : ℂ} (hq : ‖q‖<1) :
    Differentiable ℂ fun c => ∑' n, evenTwoTwoTerm q b c n := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  obtain ⟨K, hK⟩ := exists_norm_inv_qPochhammer_self_le hQ
  have hs : Summable fun n => ‖evenTwoTwoCoeff q b n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_evenTwoTwoCoeff_le hq hK)
      ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left _)
  have hP2 : ∀ x, DifferentiableAt ℂ (fun y => qPochhammerInf y (q^2)) x :=
    differentiable_qPochhammerInf_left hQ
  intro c0
  set R := ‖c0‖+1
  have hd : DifferentiableOn ℂ (fun c => ∑' n, evenTwoTwoTerm q b c n) (Metric.ball 0 R) := by
    refine differentiableOn_tsum_of_summable_norm (u := fun n =>
      Real.exp (R/(1-‖q^2‖))*Real.exp (R/(1-‖q^2‖))*
        (Real.exp (R^2/‖b^2‖/(1-‖q^2‖))*‖evenTwoTwoCoeff q b n‖))
      (hs.mul_left _ |>.mul_left _) (fun n c _ => ?_) Metric.isOpen_ball (fun n c hc => ?_)
    · refine DifferentiableAt.differentiableWithinAt ?_
      unfold evenTwoTwoTerm
      exact (((hP2 _).comp c (by fun_prop)).mul ((hP2 _).comp c (by fun_prop))).mul
        ((differentiable_qPochhammer_comp (g := fun c => c^2/b^2) (by fun_prop) n c).mul_const _)
    · have hcR : ‖c‖ ≤ R := by simpa using (Metric.mem_ball.mp hc).le
      have hle : ∀ x : ℂ, ‖x‖ ≤ 1 → ‖qPochhammerInf (c*x) (q^2)‖ ≤ Real.exp (R/(1-‖q^2‖)) :=
        fun x hx => (norm_qPochhammerInf_le_exp hQ).trans (Real.exp_le_exp.mpr
          (div_le_div_of_nonneg_right (by
            rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hx).trans hcR)
            (by linarith)))
      have hQn : ‖(q^2)^n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hQ.le
      have h1 := hle _ hQn
      have h2 := hle (q*(q^2)^n) (by
        rw [norm_mul]; nlinarith [norm_nonneg q, norm_nonneg ((q^2)^n)])
      have h3 : ‖qPochhammer (c^2/b^2) (q^2) n‖ ≤ Real.exp (R^2/‖b^2‖/(1-‖q^2‖)) :=
        (norm_qPochhammer_le_exp hQ n).trans (Real.exp_le_exp.mpr
          (div_le_div_of_nonneg_right (by rw [norm_div, norm_pow c]; gcongr) (by linarith)))
      rw [evenTwoTwoTerm, norm_mul, norm_mul, norm_mul, mul_assoc c q]
      gcongr
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))

/-- The right side of DLMF 17.7.3, cleared of `(c, cq;q²)_∞`. -/
private def evenTwoTwoRhs (q b c : ℂ) : ℂ :=
  qPochhammerInf q (q^2)/2*
    (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+qPochhammerInf b q*qPochhammerInf (-c/b) q)

/-- For small `c`, DLMF 17.7.3 follows from Jackson's transformation and DLMF 17.6.4. -/
private lemma evenTwoTwo_cleared_of_small {b c q : ℂ} (hb : b≠0) (hq : ‖q‖<1) (hc0 : c≠0)
    (hc1 : ‖c‖<1) (hz : ‖c*q‖<‖b^2‖) :
    ∑' n, evenTwoTwoTerm q b c n = evenTwoTwoRhs q b c := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hb2 : b^2 ≠ 0 := pow_ne_zero 2 hb
  have hw : ‖c*q/b^2‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hb2)]; exact hz
  have hcq1 : ‖c*q‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hq.le) hc1
  have hreg : ∀ d : ℂ, ‖d‖ < 1 → ∀ n : ℕ, d*(q^2)^n ≠ 1 := fun d hd n h =>
    one_sub_mul_pow_ne_zero_of_norm hd hQ n (by rw [h, sub_self])
  have hd : QDenominatorRegular [c, c*q] (q^2) := by
    intro x hx n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [hreg _ hc1 n, hreg _ hcq1 n]
  have hden : QDenominatorRegular [c, b^2*(c*q/b^2), c*q/b^2] (q^2) := by
    intro x hx n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hreg _ hc1 n
    · exact hreg _ (by rwa [show b^2*(c*q/b^2) = c*q by field_simp]) n
    · exact hreg _ hw n
  have hJ := qPhi2_to_qPhi2_2' (b^2) (b^2/c) c (q^2) (c*q/b^2) hQ
    (by simp [hb, hc0]) hden hw
  rw [q_even_heine hb hc0 hq hz (fun x hx n => hd x (by simp at hx ⊢; exact Or.inl hx) n),
    show c*q/b^2*b^2 = c*q by field_simp, show b^2*(c*q/b^2) = c*q by field_simp,
    show b^2/c*(c*q/b^2) = q by field_simp, show c/(b^2/c) = c^2/b^2 by field_simp,
    ← qPhi_two_swap] at hJ
  rw [← qPhi_evenTwoTwo_mul hq hd]
  have hA : qPochhammerInf c (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hd c (by simp) n (sub_eq_zero.mp h).symm
  have hB : qPochhammerInf (c*q) (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hd (c*q) (by simp) n (sub_eq_zero.mp h).symm
  have hZ : qPochhammerInf (c*q/b^2) (q^2) ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hw hQ
  simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hJ
  unfold evenTwoTwoRhs
  generalize qPhi [c^2/b^2,b^2] [c,c*q] (q^2) q = Φ at hJ ⊢
  generalize qPochhammerInf c (q^2) = A at hA hJ ⊢
  generalize qPochhammerInf (c*q) (q^2) = B at hB hJ ⊢
  generalize qPochhammerInf (c*q/b^2) (q^2) = Z at hZ hJ ⊢
  field_simp at hJ ⊢
  linear_combination -hJ

/-- The cancelled product retains b=±q^(-m) whenever the lower parameters are regular. -/
@[dlmf 17.7.E3]
theorem two_phi_two_even_sum {b c q : ℂ} (hb : b≠0) (hq : ‖q‖<1)
    (hd : QDenominatorRegular [c, c*q] (q^2)) :
    qPhi [c^2/b^2,b^2] [c,c*q] (q^2) q=
      qPochhammerInf q (q^2)/(2*qPochhammerListInf [c,c*q] (q^2))*
      (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+
       qPochhammerInf b q*qPochhammerInf (-c/b) q) := by
  have hQ : ‖q^2‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hP : ∀ x, DifferentiableAt ℂ (fun y => qPochhammerInf y q) x :=
    differentiable_qPochhammerInf_left hq
  have hG : AnalyticOnNhd ℂ (fun c => evenTwoTwoRhs q b c) Set.univ := by
    refine (Differentiable.differentiableOn ?_).analyticOnNhd isOpen_univ
    intro c
    unfold evenTwoTwoRhs
    fun_prop (disch := assumption)
  have hF : AnalyticOnNhd ℂ (fun c => ∑' n, evenTwoTwoTerm q b c n) Set.univ :=
    (differentiable_evenTwoTwo hq).differentiableOn.analyticOnNhd isOpen_univ
  have hb2 : (0:ℝ) < ‖b^2‖ := norm_pos_iff.mpr (pow_ne_zero 2 hb)
  have hfreq : ∃ᶠ c' in 𝓝[≠] (0:ℂ), ∑' n, evenTwoTwoTerm q b c' n = evenTwoTwoRhs q b c' := by
    refine Filter.Eventually.frequently ?_
    have e1 : ∀ᶠ c' in 𝓝 (0:ℂ), ‖c'‖ < 1 :=
      (continuous_norm.tendsto _).eventually (eventually_lt_nhds (by simp))
    have e2 : ∀ᶠ c' in 𝓝 (0:ℂ), ‖c'*q‖ < ‖b^2‖ :=
      ((continuous_norm.comp (continuous_id.mul continuous_const)).tendsto (0:ℂ)).eventually
        (eventually_lt_nhds (by simpa using hb2))
    filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin]
      with c' h1 h2 h3
    exact evenTwoTwo_cleared_of_small hb hq h3 h1 h2
  have key := hF.eqOn_of_preconnected_of_frequently_eq hG isPreconnected_univ
    (Set.mem_univ _) hfreq (Set.mem_univ c)
  have hA : qPochhammerInf c (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hd c (by simp) n (sub_eq_zero.mp h).symm
  have hB : qPochhammerInf (c*q) (q^2) ≠ 0 :=
    qPochhammerInf_ne_zero hQ fun n h => hd (c*q) (by simp) n (sub_eq_zero.mp h).symm
  have h1 := qPhi_evenTwoTwo_mul (b := b) hq hd
  simp only at key
  rw [key] at h1
  refine mul_right_cancel₀ (mul_ne_zero hA hB) (h1.trans ?_)
  simp only [evenTwoTwoRhs, qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  generalize qPochhammerInf c (q^2) = A at hA ⊢
  generalize qPochhammerInf (c*q) (q^2) = B at hB ⊢
  field_simp

end DLMF.QHypergeometric
