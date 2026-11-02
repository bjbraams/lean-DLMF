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

/-!
# The q-Chu–Vandermonde and q-Gauss sums (DLMF 17.5.5, 17.6.1–17.6.3)

The two terminating q-Chu–Vandermonde sums and their full-domain extension to the q-Gauss
sum. The q-Gauss proof uses a normally convergent Newton series and Mathlib's analytic identity
theorem, interpolating the terminating values without excluding exceptional upper parameters.

## Main results

* `q_chu_vandermonde_first`, `q_chu_vandermonde_second`: 17.6.2 and 17.6.3.
* `q_gauss`: `₂φ₁(a,b;c;q,c/(ab)) = (c/a,c/b;q)_∞/(c,c/(ab);q)_∞` (17.6.1).
* `one_phi_one_sum`: 17.5.5.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- The first q-Chu–Vandermonde sum `2φ1(a,q^(-n);c;q,c q^n/a) = (c/a;q)_n/(c;q)_n` (DLMF
17.6.E2). -/
@[dlmf 17.6.E2]
theorem q_chu_vandermonde_first {a c q : ℂ} (ha : a≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hc : QDenominatorRegularThrough [c] q n) :
    qPhi [a,q^(-(n:ℤ))] [c] q (c*q^n/a)=qPochhammer (c/a) q n/qPochhammer c q n := by
  have hcn : qPochhammer c q n≠0 := by simpa [QDenominatorRegularThrough,qPochhammerList] using hc
  rw [eq_div_iff hcn,qPhi_two_one_comm]
  by_cases hc0 : c=0
  · subst hc0
    rw [qPhi_terminates (a := [a]) hq0 n, qPhiPartial, sum_range_succ']
    simp [qPhiTerm_two_one]
  rw [qPhi_neg_pow_mul_qPochhammer hq0 hq hc0 hcn]
  have hz : -(c*q^n/a*q^(-(n:ℤ)))=-c/a := by
    rw [zpow_neg,zpow_natCast]; field_simp
  rw [hz]
  have hterm : ∀ k ∈ range (n+1),
      qBinom q n k*qPochhammer a q k*qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*
      (-c/a)^k*(-c)^(n-k)=(-c)^n*(a^n)⁻¹*(qBinom q n k*qPochhammer a q k*
        qPochhammer (q^(1-(n:ℤ))/c) q (n-k)*a^(n-k)) := by
    intro k hk
    have hkn : k≤n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [Nat.add_sub_cancel_left,div_pow,pow_add a,pow_add (-c)]
    field_simp
  rw [sum_congr rfl hterm,← mul_sum,sum_qBinom_qPochhammer_mul_pow_sub]
  have hy : a*(q^(1-(n:ℤ))/c)≠0 := mul_ne_zero ha (div_ne_zero (zpow_ne_zero _ hq0) hc0)
  rw [qPochhammer_reverse hy hq0]
  have hy' : q^(1-(n:ℤ))/(a*(q^(1-(n:ℤ))/c))=c/a := by field_simp
  rw [hy']
  have hq1 : (q^(n.choose 2))^2*(q^(1-(n:ℤ)))^n=1 := by
    rw [← zpow_natCast (q^(1-(n:ℤ))),← zpow_mul,← pow_mul,← zpow_natCast q,← zpow_add₀ hq0]
    have h2 := choose_two_mul_two_add_self n
    rw [show (((n.choose 2*2:ℕ)):ℤ)+(1-(n:ℤ))*(n:ℤ)=0 by
      have : ((n.choose 2*2:ℕ):ℤ)=(n:ℤ)*n-n := by
        rw [show n.choose 2*2=n*n-n by omega]; push_cast [Nat.le_mul_self n]; ring
      rw [this]; ring,zpow_zero]
  generalize q^(1-(n:ℤ)) = X at hq1 hy ⊢
  generalize q^(n.choose 2) = T at hq1 ⊢
  rw [neg_pow (a*(X/c)),mul_pow a,div_pow X c]
  have hs : (-1:ℂ)^n*(-1:ℂ)^n=1 := by rw [← mul_pow]; norm_num
  field_simp
  linear_combination (c^n*qPochhammer (c/a) q n)*(((-1:ℂ)^n*(-1:ℂ)^n)*hq1+hs)

/-- The cleared product retains the regular upper parameter a=0. -/
@[dlmf 17.6.E3]
theorem q_chu_vandermonde_second {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hc : QDenominatorRegularThrough [c] q n) :
    qPhi [a,q^(-(n:ℤ))] [c] q q=((range n).prod (fun j => a-c*q^j))/qPochhammer c q n := by
  have hcn : qPochhammer c q n≠0 := by simpa [QDenominatorRegularThrough,qPochhammerList] using hc
  rw [eq_div_iff hcn,qPhi_two_one_comm]
  by_cases hc0 : c=0
  · subst hc0
    let F : ℂ → ℂ := fun c => qPhiPartial [q^(-(n:ℤ)),a] [c] q q n*qPochhammer c q n
    let G : ℂ → ℂ := fun c => (range n).prod (fun j => a-c*q^j)
    have hF : ContinuousAt F 0 := by
      apply ContinuousAt.mul _ (continuous_qPochhammer q n).continuousAt
      unfold ContinuousAt qPhiPartial
      apply tendsto_finsetSum
      intro k _
      have h : ContinuousAt (fun c : ℂ => qPhiTerm [q^(-(n:ℤ)),a] [c] q q k) 0 := by
        simp only [qPhiTerm_two_one]
        apply ContinuousAt.mul _ continuousAt_const
        apply ContinuousAt.div continuousAt_const
        · exact ((continuous_qPochhammer q k).mul continuous_const).continuousAt
        · simpa using qPochhammer_self_ne_zero hq k
      exact h
    have hG : ContinuousAt G 0 := by
      apply Continuous.continuousAt
      fun_prop
    have hev : ∀ᶠ c in 𝓝[≠] (0:ℂ), F c=G c := by
      have h1 : ∀ᶠ c in 𝓝 (0:ℂ), qPochhammer c q n≠0 :=
        (continuous_qPochhammer q n).continuousAt.eventually_ne hcn
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds h1] with c hc0 hcn'
      simp only [F,G]
      rw [← qPhi_terminates (a := [a]) hq0 n]
      exact qPhi_neg_pow_q_mul_qPochhammer hq0 hq n hc0 hcn'
    have := eq_at_zero_of_eventually_punctured hF hG hev
    simp only [F,G] at this
    rw [qPhi_terminates (a := [a]) hq0 n]
    exact this
  exact qPhi_neg_pow_q_mul_qPochhammer hq0 hq n hc0 hcn

/-- The phase-free coefficients are bounded because the finite factorials have nonzero limiting
denominators. -/
private lemma qGauss_coefficient_bound {a c q : ℂ} (hq : ‖q‖ < 1)
    (hc : QDenominatorRegular [c] q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖qPochhammer a q n / (qPochhammer c q n * qPochhammer q q n)‖ ≤ C := by
  have hc0 : qPochhammerInf c q ≠ 0 := qPochhammerInf_ne_zero hq fun n he =>
    hc c (by simp) n (sub_eq_zero.mp he).symm
  have hq0 : qPochhammerInf q q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
  have ht := (tendsto_qPochhammer (w := a) hq).div
    ((tendsto_qPochhammer (w := c) hq).mul (tendsto_qPochhammer (w := q) hq))
    (mul_ne_zero hc0 hq0)
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  exact (hC _ ⟨n, rfl⟩).trans (le_max_left _ _)

/-- Reciprocal upper parameters turn the finite shifted factorial into a Newton polynomial. -/
private lemma qGauss_newton_product {q w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (∏ j ∈ range n, (w - q ^ j)) = w ^ n * qPochhammer w⁻¹ q n := by
  rw [qPochhammer_eq_prod, show w ^ n = ∏ _j ∈ range n, w by simp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  field_simp

/-- The Newton series equals two-phi-one at every nonzero reciprocal upper parameter. -/
private lemma qGauss_newton_eq_phi {a c q w : ℂ} (hw : w ≠ 0) :
    (∑' n : ℕ, (qPochhammer a q n / (qPochhammer c q n * qPochhammer q q n) *
      (c / a) ^ n) * ∏ j ∈ range n, (w - q ^ j)) =
      qPhi [a, w⁻¹] [c] q (c * w / a) := by
  unfold qPhi
  apply tsum_congr
  intro n
  rw [qPhiTerm_two_one, qGauss_newton_product hw]
  rw [show c * w / a = c / a * w by ring, mul_pow]
  ring

/-- The reciprocal-parameter Newton series is analytic throughout its convergence disc. -/
private lemma qGauss_analytic_newton {a c q : ℂ} (hq : ‖q‖ < 1) (hca : c / a ≠ 0)
    (hc : QDenominatorRegular [c] q) :
    AnalyticOnNhd ℂ (fun w => ∑' n : ℕ,
      (qPochhammer a q n / (qPochhammer c q n * qPochhammer q q n) * (c / a) ^ n) *
        ∏ j ∈ range n, (w - q ^ j)) (Metric.ball 0 ‖c / a‖⁻¹) := by
  obtain ⟨C, hC, hbound⟩ := qGauss_coefficient_bound hq hc
  apply Complex.analyticOnNhd_tsum_geometricNewton hq hC (norm_pos_iff.mpr hca)
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)

/-- The q-Gauss product quotient is analytic on the same reciprocal-parameter disc. -/
private lemma qGauss_analytic_product {a c q : ℂ} (hq : ‖q‖ < 1)
    (hc : QDenominatorRegular [c] q) :
    AnalyticOnNhd ℂ (fun w => qPochhammerInf (c / a) q * qPochhammerInf (c * w) q /
      (qPochhammerInf c q * qPochhammerInf (c / a * w) q))
      (Metric.ball 0 ‖c / a‖⁻¹) := by
  intro w hw
  have hw' : ‖c / a * w‖ < 1 := by
    rw [norm_mul]
    by_cases hca : c / a = 0
    · simp [hca]
    have hw' : ‖w‖ < ‖c / a‖⁻¹ := by simpa using hw
    have h := mul_lt_mul_of_pos_left hw' (norm_pos_iff.mpr hca)
    rwa [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hca)] at h
  apply AnalyticAt.div
    (analyticAt_const.mul ((qPochhammerInf_analytic hq _ (mem_univ _)).comp
      (analyticAt_const.mul analyticAt_id)))
    (analyticAt_const.mul ((qPochhammerInf_analytic hq _ (mem_univ _)).comp
      (analyticAt_const.mul analyticAt_id)))
  exact mul_ne_zero (qPochhammerInf_ne_zero hq fun n he =>
    hc c (by simp) n (sub_eq_zero.mp he).symm)
    (qPochhammerInf_ne_zero_of_norm_lt_one hw' hq)

/-- Terminating q-Chu values determine the entire reciprocal-parameter q-Gauss identity. -/
private lemma qGauss_newton_identity {a c q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hc0 : c ≠ 0) (hc : QDenominatorRegular [c] q) :
    EqOn (fun w : ℂ => ∑' n : ℕ,
      (qPochhammer a q n / (qPochhammer c q n * qPochhammer q q n) * (c / a) ^ n) *
        ∏ j ∈ range n, (w - q ^ j))
      (fun w => qPochhammerInf (c / a) q * qPochhammerInf (c * w) q /
        (qPochhammerInf c q * qPochhammerInf (c / a * w) q))
      (Metric.ball 0 ‖c / a‖⁻¹) := by
  let F : ℂ → ℂ := fun w => ∑' n : ℕ,
    (qPochhammer a q n / (qPochhammer c q n * qPochhammer q q n) * (c / a) ^ n) *
      ∏ j ∈ range n, (w - q ^ j)
  let G : ℂ → ℂ := fun w => qPochhammerInf (c / a) q * qPochhammerInf (c * w) q /
    (qPochhammerInf c q * qPochhammerInf (c / a * w) q)
  have hca : c / a ≠ 0 := div_ne_zero hc0 ha
  have hR : 0 < ‖c / a‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hca)
  have hF : AnalyticOnNhd ℂ F (Metric.ball 0 ‖c / a‖⁻¹) := qGauss_analytic_newton hq hca hc
  have hG : AnalyticOnNhd ℂ G (Metric.ball 0 ‖c / a‖⁻¹) := qGauss_analytic_product hq hc
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 (0 : ℂ)) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have hev : ∀ᶠ n : ℕ in atTop, F (q ^ n) = G (q ^ n) := by
    have hsmall : ∀ᶠ n : ℕ in atTop, ‖c / a * q ^ n‖ < 1 := by
      have ht' : Tendsto (fun n : ℕ => c / a * q ^ n) atTop (𝓝 (0 : ℂ)) := by
        simpa using hpow.const_mul (c / a)
      have he : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 := by
        have he := Metric.ball_mem_nhds (0 : ℂ) (zero_lt_one : (0 : ℝ) < 1)
        change ∀ᶠ z : ℂ in 𝓝 0, z ∈ Metric.ball 0 1 at he
        simpa only [Metric.mem_ball, dist_zero_right] using he
      exact ht'.eventually he
    filter_upwards [hsmall] with n hn
    have hcn : qPochhammer c q n ≠ 0 := qPochhammer_ne_zero_of_qDenominatorRegular hq hc n
    have htail : qPochhammerInf (c / a * q ^ n) q ≠ 0 :=
      qPochhammerInf_ne_zero_of_norm_lt_one hn hq
    have htail' : qPochhammerInf (c * q ^ n / a) q ≠ 0 := by
      simpa only [show c * q ^ n / a = c / a * q ^ n by ring] using htail
    have hctail : qPochhammerInf (c * q ^ n) q ≠ 0 :=
      qPochhammerInf_shift_ne_zero hq (fun k he => hc c (by simp) k
        (sub_eq_zero.mp he).symm) n
    dsimp only [F, G]
    rw [qGauss_newton_eq_phi (pow_ne_zero n hq0)]
    have hchu := q_chu_vandermonde_first ha hq0 hq n
      (show QDenominatorRegularThrough [c] q n by
        simpa only [QDenominatorRegularThrough, qPochhammerList, List.map_singleton,
          List.prod_singleton] using hcn)
    rw [zpow_neg, zpow_natCast] at hchu
    rw [hchu, qPochhammerInf_mul_qPochhammer (a := c / a) hq n,
      qPochhammerInf_mul_qPochhammer (a := c) hq n]
    field_simp [htail']
  have hpunct : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpow, Eventually.of_forall fun n => by
      simpa using pow_ne_zero n hq0⟩
  have heq := hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_ball (0 : ℂ) ‖c / a‖⁻¹).isPreconnected (by simpa using hR)
    (hpunct.frequently hev.frequently)
  exact heq

/-- Terminating q-Chu values accumulate at zero and determine the analytic q-Gauss identity. -/
private lemma qGauss_nonzero {a b c q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : c ≠ 0) (hz : ‖c‖ < ‖a * b‖)
    (hc : QDenominatorRegular [c] q) :
    qPhi [a,b] [c] q (c/(a*b)) =
      qPochhammerListInf [c/a,c/b] q / qPochhammerListInf [c,c/(a*b)] q := by
  have heq := qGauss_newton_identity hq0 hq ha hc0 hc
  have hw : b⁻¹ ∈ Metric.ball 0 ‖c / a‖⁻¹ := by
    simp only [Metric.mem_ball, dist_zero_right, norm_inv, norm_div, norm_mul] at hz ⊢
    rw [inv_lt_inv₀ (norm_pos_iff.mpr hb) (div_pos (norm_pos_iff.mpr hc0)
      (norm_pos_iff.mpr ha))]
    exact (div_lt_iff₀ (norm_pos_iff.mpr ha)).mpr (by simpa [mul_comm] using hz)
  have h := heq hw
  dsimp only at h
  rw [qGauss_newton_eq_phi (inv_ne_zero hb), inv_inv] at h
  simpa only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, show c * b⁻¹ = c / b by ring,
    show c / b / a = c / (a * b) by ring,
    show c / a * b⁻¹ = c / (a * b) by ring] using h

/-- At base zero, a nonempty finite shifted factorial retains only its first factor. -/
private lemma qGauss_poch_zero_base (a : ℂ) (n : ℕ) : qPochhammer a 0 (n + 1) = 1 - a := by
  rw [qPochhammer_eq_prod, prod_range_succ']
  simp

/-- At base zero, q-Gauss reduces to summing a geometric tail. -/
private lemma qGauss_zero_base {a b c : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hz : ‖c‖ < ‖a * b‖) (hc : QDenominatorRegular [c] 0) :
    qPhi [a,b] [c] 0 (c/(a*b)) =
      qPochhammerListInf [c/a,c/b] 0 / qPochhammerListInf [c,c/(a*b)] 0 := by
  let z := c / (a * b)
  have hz' : ‖z‖ < 1 := by
    dsimp [z]
    rw [norm_div, div_lt_one₀ (norm_pos_iff.mpr (mul_ne_zero ha hb))]
    exact hz
  have hc1 : 1 - c ≠ 0 := by
    intro he
    exact hc c (by simp) 0 (by simpa using (sub_eq_zero.mp he).symm)
  have hz1 : 1 - z ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz'
  let A := (1 - a) * (1 - b) / (1 - c)
  have htail : HasSum (fun n : ℕ => qPhiTerm [a,b] [c] 0 z (n + 1))
      (A * z * (1 - z)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one hz').mul_left (A * z) using 1
    ext n
    rw [qPhiTerm_two_one]
    simp only [qGauss_poch_zero_base, sub_zero, mul_one, pow_succ]
    dsimp [A]
    ring
  have hsum := htail.zero_add
  have hzero : qPhiTerm [a,b] [c] 0 z 0 = 1 := by simp [qPhiTerm_two_one]
  rw [hzero] at hsum
  change (∑' n : ℕ, qPhiTerm [a,b] [c] 0 z n) = _
  rw [hsum.tsum_eq]
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, DLMF.QSeries.TripleProduct.qPochhammerInf_zero_right]
  change 1 + A * z * (1 - z)⁻¹ = (1 - c / a) * (1 - c / b) / ((1 - c) * (1 - z))
  dsimp only [A]
  field_simp
  dsimp only [z]
  field_simp
  ring

/-- The q-Gauss sum `2φ1(a,b;c;q,c/(ab)) = (c/a,c/b;q)_∞/(c,c/(ab);q)_∞` for `|c| < |ab|` (DLMF
17.6.E1). -/
@[dlmf 17.6.E1]
theorem q_gauss {a b c q : ℂ} (hq : ‖q‖<1) (hz : ‖c‖<‖a*b‖)
    (hc : QDenominatorRegular [c] q) :
    qPhi [a,b] [c] q (c/(a*b))=qPochhammerListInf [c/a,c/b] q/qPochhammerListInf [c,c/(a*b)] q := by
  have hab : a * b ≠ 0 := norm_pos_iff.mp ((norm_nonneg c).trans_lt hz)
  have ha := left_ne_zero_of_mul hab
  have hb := right_ne_zero_of_mul hab
  by_cases hc0 : c = 0
  · subst hc0
    simp [qPhi_zero, qPochhammerListInf]
  by_cases hq0 : q = 0
  · subst hq0
    exact qGauss_zero_base ha hb hz hc
  exact qGauss_nonzero hq0 hq ha hb hc0 hz hc

/-- The `1φ1` summation `1φ1(a;c;q,c/a) = (c/a;q)_∞/(c;q)_∞` (DLMF 17.5.E5). -/
@[dlmf 17.5.E5]
theorem one_phi_one_sum {a c q : ℂ} (ha : a ≠ 0) (hq : ‖q‖ < 1)
    (hc : QDenominatorRegular [c] q) :
    qPhi [a] [c] q (c / a) = qPochhammerInf (c / a) q / qPochhammerInf c q := by
  by_cases hc0 : c = 0
  · subst c
    simp [qPhi_zero, qPochhammerInf]
  by_cases hq0 : q = 0
  · subst q
    have h1c : 1 - c ≠ 0 := one_sub_ne_zero_of_qDenominatorRegular hc
    have hsum : qPhi [a] [c] 0 (c / a) =
        qPhiTerm [a] [c] 0 (c / a) 0 + qPhiTerm [a] [c] 0 (c / a) 1 := by
      unfold qPhi
      rw [tsum_eq_sum (s := range 2)]
      · simp [sum_range_succ]
      · intro n hn
        have hn2 : 0 < n.choose 2 :=
            Nat.choose_pos (by simp only [Finset.mem_range, not_lt] at hn; omega)
        simp [qPhiTerm, qPhiExponent, qPochhammerList, qTri_nat,
          zpow_natCast, zero_pow hn2.ne']
    rw [hsum]
    norm_num [qPhiTerm, qPhiExponent, qPochhammerList, DLMF.QSeries.TripleProduct.tri,
      qPochhammer_one, DLMF.QSeries.TripleProduct.qPochhammerInf_zero_right]
    field_simp
    ring
  have he := qGauss_newton_identity hq0 hq ha hc0 hc
    (show (0 : ℂ) ∈ Metric.ball 0 ‖c / a‖⁻¹ by
      simp only [Metric.mem_ball, dist_self]
      exact inv_pos.mpr (norm_pos_iff.mpr (div_ne_zero hc0 ha)))
  have hzero : qPochhammerInf (0 : ℂ) q = 1 := by simp [qPochhammerInf]
  simp only [mul_zero, hzero, mul_one] at he
  rw [← he]
  unfold qPhi
  apply tsum_congr
  intro n
  have hp : (∏ j ∈ range n, ((0 : ℂ) - q ^ j)) = (-1) ^ n * q ^ n.choose 2 := by
    simp only [zero_sub, prod_neg, card_range]
    rw [Finset.prod_pow_eq_pow_sum (range n) (fun j => j) q, sum_range_id,
      Nat.choose_two_right]
  rw [hp]
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil, mul_one]
  norm_num
  rw [qTri_nat, zpow_natCast]
  ring

end DLMF.QHypergeometric
