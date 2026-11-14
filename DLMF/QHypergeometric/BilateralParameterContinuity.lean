/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.QHypergeometric.BilateralContinuity
/-!
# Parameter continuity of balanced bilateral basic series

Clearing each lower infinite product gives a local geometric majorant, uniform in every
parameter. The cleared halves are analytic in analytic parameters. Splitting the positive and
negative index halves proves joint continuity of balanced `rψr` throughout its convergence
annulus, including terminating upper parameters.

* `BilateralContinuity.analyticAt_tsum_clearedListTerm`: analytic denominator-cleared series.
* `BilateralContinuity.continuousAt_qPsi`: parameter continuity for every finite balanced
  family with nonzero parameters and regular lower and backward upper factors.
-/

public noncomputable section
open Complex Filter Set
open scoped Topology
open DLMF.QSeries
namespace DLMF.QHypergeometric.BilateralContinuity

/-- A balanced positive-index term with every lower infinite product cleared. -/
def clearedListTerm (a b : List (ℂ → ℂ)) (z : ℂ → ℂ) (q t : ℂ) (n : ℕ) : ℂ :=
  (a.map fun f => qPochhammer (f t) q n).prod *
    (b.map fun f => qPochhammerInf (f t * q ^ n) q).prod * z t ^ n

/-- The defining denominator-cleared product. -/
lemma clearedListTerm_def (a b : List (ℂ → ℂ)) (z : ℂ → ℂ) (q t : ℂ) (n : ℕ) :
    clearedListTerm a b z q t n = (a.map fun f => qPochhammer (f t) q n).prod *
      (b.map fun f => qPochhammerInf (f t * q ^ n) q).prod * z t ^ n := by rfl

/-- A summable geometric majorant bounds every denominator-cleared shifted series locally. -/
lemma exists_summable_norm_clearedListTerm_bound {a b : List (ℂ → ℂ)}
    {z : ℂ → ℂ} {x q : ℂ} (hq : ‖q‖ < 1) (ha : ∀ f ∈ a, ContinuousAt f x)
    (hb : ∀ f ∈ b, ContinuousAt f x) (hz : ContinuousAt z x) (hz1 : ‖z x‖ < 1) (N : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ t in 𝓝 x, ∀ k, ‖clearedListTerm a b z q t (k+N)‖ ≤ u k := by
  have eventually_list_norm_le {l : List (ℂ → ℂ)} {x : ℂ}
      (hl : ∀ f ∈ l, ContinuousAt f x) :
      ∀ᶠ t in 𝓝 x, ∀ f ∈ l, ‖f t‖ ≤ ‖f x‖ + 1 := by
    induction l with
    | nil => simp
    | cons f l ih =>
      filter_upwards [(hl f (by simp)).norm.eventually_lt_const (by linarith : ‖f x‖ < ‖f x‖+1),
        ih (fun g hg => hl g (by simp [hg]))] with t hft hlt g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hft.le
      · exact hlt g hg

  obtain ⟨ρ,hρx,hρ1⟩ := exists_between hz1
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρx.le
  let C (f : ℂ → ℂ) : ℝ := Real.exp ((‖f x‖+1)/(1-‖q‖))
  have hC (f : ℂ → ℂ) : 0 ≤ C f := (Real.exp_pos _).le
  have hfinite (l : List (ℂ → ℂ)) (t : ℂ)
      (ht : ∀ f ∈ l, ‖f t‖ ≤ ‖f x‖+1) (n : ℕ) :
      ‖(l.map fun f => qPochhammer (f t) q n).prod‖ ≤ (l.map C).prod := by
    induction l with
    | nil => simp
    | cons f l ih =>
      simp only [List.map_cons,List.prod_cons,norm_mul]
      apply mul_le_mul
      · exact (norm_qPochhammer_le_exp hq n).trans (Real.exp_le_exp.mpr
          (div_le_div_of_nonneg_right (ht f (by simp)) (sub_nonneg.mpr hq.le)))
      · exact ih (fun g hg => ht g (by simp [hg]))
      · positivity
      · exact hC f
  have hinfinite (l : List (ℂ → ℂ)) (t : ℂ)
      (ht : ∀ f ∈ l, ‖f t‖ ≤ ‖f x‖+1) (n : ℕ) :
      ‖(l.map fun f => qPochhammerInf (f t * q ^ n) q).prod‖ ≤ (l.map C).prod := by
    induction l with
    | nil => simp
    | cons f l ih =>
      simp only [List.map_cons,List.prod_cons,norm_mul]
      apply mul_le_mul
      · refine (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr
          (div_le_div_of_nonneg_right ?_ (sub_nonneg.mpr hq.le)))
        rw [norm_mul,norm_pow]
        exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg q) hq.le)).trans
          (ht f (by simp))
      · exact ih (fun g hg => ht g (by simp [hg]))
      · positivity
      · exact hC f
  have hbound : ∀ᶠ t in 𝓝 x, ∀ k : ℕ, ‖clearedListTerm a b z q t (k+N)‖ ≤
      ((a.map C).prod*(b.map C).prod)*ρ^k := by
    filter_upwards [eventually_list_norm_le ha,eventually_list_norm_le hb,
      hz.norm.eventually_lt_const hρx] with t hat hbt hzt k
    rw [clearedListTerm_def]
    rw [norm_mul,norm_mul,norm_pow]
    apply mul_le_mul
    · exact mul_le_mul (hfinite a t hat _) (hinfinite b t hbt _) (by positivity)
        (List.prod_nonneg (by simpa using fun f _ => hC f))
    · exact (pow_le_pow_left₀ (norm_nonneg _) hzt.le _).trans
        (pow_le_pow_of_le_one hρ0 hρ1.le (by omega))
    · positivity
    · exact mul_nonneg (List.prod_nonneg (by simpa using fun f _ => hC f))
        (List.prod_nonneg (by simpa using fun f _ => hC f))
  exact ⟨_,(summable_geometric_of_lt_one hρ0 hρ1).mul_left _,hbound⟩

/-- The cleared series and every shifted tail depend continuously on parameters. -/
lemma continuousAt_tsum_clearedListTerm {a b : List (ℂ → ℂ)} {z : ℂ → ℂ} {x q : ℂ}
    (hq : ‖q‖ < 1) (ha : ∀ f ∈ a, ContinuousAt f x)
    (hb : ∀ f ∈ b, ContinuousAt f x) (hz : ContinuousAt z x) (hz1 : ‖z x‖ < 1) (N : ℕ) :
    ContinuousAt (fun t => ∑' k, clearedListTerm a b z q t (k+N)) x := by
  obtain ⟨u,hu,hbound⟩ := exists_summable_norm_clearedListTerm_bound hq ha hb hz hz1 N
  have hInf : Continuous (fun u : ℂ => qPochhammerInf u q) :=
    (differentiable_qPochhammerInf_left hq).continuous
  have hterm (k : ℕ) : ContinuousAt (fun t => clearedListTerm a b z q t (k+N)) x := by
    dsimp only [clearedListTerm]
    apply ((tendsto_list_prod a ?_).mul (tendsto_list_prod b ?_)).mul (hz.pow _)
    · intro f hf
      exact (continuous_qPochhammer q _).continuousAt.comp (ha f hf)
    · intro f hf
      exact hInf.continuousAt.comp ((hb f hf).mul_const _)
  exact tendsto_tsum_of_dominated_convergence hu hterm hbound

/-- Every denominator-cleared shifted series is analytic in analytic parameters. -/
lemma analyticAt_tsum_clearedListTerm {a b : List (ℂ → ℂ)}
    {z : ℂ → ℂ} {x q : ℂ} (hq : ‖q‖ < 1) (ha : ∀ f ∈ a, AnalyticAt ℂ f x)
    (hb : ∀ f ∈ b, AnalyticAt ℂ f x) (hz : AnalyticAt ℂ z x) (hz1 : ‖z x‖ < 1) (N : ℕ) :
    AnalyticAt ℂ (fun t => ∑' k, clearedListTerm a b z q t (k+N)) x := by
  obtain ⟨u,hu,hbound⟩ := exists_summable_norm_clearedListTerm_bound hq
    (fun f hf => (ha f hf).continuousAt) (fun f hf => (hb f hf).continuousAt)
    hz.continuousAt hz1 N
  have hevent {l : List (ℂ → ℂ)} (hl : ∀ f ∈ l, AnalyticAt ℂ f x) :
      ∀ᶠ t in 𝓝 x, ∀ f ∈ l, AnalyticAt ℂ f t := by
    induction l with
    | nil => simp
    | cons f l ih =>
      filter_upwards [(hl f (by simp)).eventually_analyticAt,
        ih (fun g hg => hl g (by simp [hg]))] with t hft hlt g hg
      rcases List.mem_cons.mp hg with rfl|hg
      · exact hft
      · exact hlt g hg
  obtain ⟨V,hVsub,hVo,hxV⟩ := eventually_nhds_iff.mp
    (hbound.and ((hevent ha).and ((hevent hb).and hz.eventually_analyticAt)))
  have hp (n : ℕ) (t : ℂ) : AnalyticAt ℂ (fun y : ℂ => qPochhammer y q n) t := by
    induction n with
    | zero => simpa only [qPochhammer_zero] using
        (analyticAt_const (E := ℂ) (v := (1:ℂ)))
    | succ n ihp =>
      simp only [qPochhammer_succ]
      exact ihp.mul (analyticAt_const.sub (analyticAt_id.mul analyticAt_const))
  have hfinite {l : List (ℂ → ℂ)} {t : ℂ} (hl : ∀ f ∈ l, AnalyticAt ℂ f t) (n : ℕ) :
      AnalyticAt ℂ (fun w => (l.map fun f => qPochhammer (f w) q n).prod) t := by
    induction l with
    | nil => simpa using (analyticAt_const (E := ℂ) (v := (1:ℂ)))
    | cons f l ih =>
      simp only [List.map_cons,List.prod_cons]
      exact ((hp n (f t)).comp (hl f (by simp))).mul (ih fun g hg => hl g (by simp [hg]))
  have hinfinite {l : List (ℂ → ℂ)} {t : ℂ} (hl : ∀ f ∈ l, AnalyticAt ℂ f t) (n : ℕ) :
      AnalyticAt ℂ (fun w => (l.map fun f => qPochhammerInf (f w*q^n) q).prod) t := by
    induction l with
    | nil => simpa using (analyticAt_const (E := ℂ) (v := (1:ℂ)))
    | cons f l ih =>
      simp only [List.map_cons,List.prod_cons]
      exact (((qPochhammerInf_analytic hq) _ (mem_univ _)).comp
        ((hl f (by simp)).mul analyticAt_const)).mul (ih fun g hg => hl g (by simp [hg]))
  have hd : DifferentiableOn ℂ (fun t => ∑' k, clearedListTerm a b z q t (k+N)) V := by
    refine differentiableOn_tsum_of_summable_norm hu ?_ hVo ?_
    · intro k t ht
      have h := hVsub t ht
      simpa only [clearedListTerm_def,Pi.mul_def,Pi.pow_def,Function.comp_def] using
        (((hfinite h.2.1 (k+N)).mul (hinfinite h.2.2.1 (k+N))).mul
          (h.2.2.2.pow (k+N))).differentiableAt.differentiableWithinAt (s := V)
    · intro k t ht
      exact (hVsub t ht).1 k
  exact hd.analyticOnNhd hVo x hxV

/-- Finite products of infinite q-shifted factorials depend continuously on their parameters. -/
lemma continuousAt_qPochhammerListInf {l : List (ℂ → ℂ)} {q x : ℂ} (hq : ‖q‖ < 1)
    (hl : ∀ f ∈ l, ContinuousAt f x) :
    ContinuousAt (fun t => qPochhammerListInf (l.map fun f => f t) q) x := by
  have hi : Continuous (fun u : ℂ => qPochhammerInf u q) :=
    (differentiable_qPochhammerInf_left hq).continuous
  simpa only [ContinuousAt,qPochhammerListInf,List.map_map,Function.comp_def] using
    (tendsto_list_prod l fun f hf => hi.continuousAt.comp (hl f hf))

/-- Finite products of infinite q-shifted factorials are analytic in analytic parameters. -/
lemma analyticAt_qPochhammerListInf {l : List (ℂ → ℂ)} {q x : ℂ} (hq : ‖q‖ < 1)
    (hl : ∀ f ∈ l, AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun t => qPochhammerListInf (l.map fun f => f t) q) x := by
  induction l with
  | nil => simpa [qPochhammerListInf] using (analyticAt_const (E := ℂ) (v := (1 : ℂ)))
  | cons f l ih =>
    simp only [qPochhammerListInf,List.map_cons,List.prod_cons]
    exact (((qPochhammerInf_analytic hq) _ (mem_univ _)).comp (hl f (by simp))).mul
      (ih fun g hg => hl g (by simp [hg]))

/-- Factoring all finite q-shifted factorials leaves the shifted infinite-product tails. -/
lemma qPochhammerListInf_factor (l : List ℂ) {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerListInf l q =
      qPochhammerList l q n * qPochhammerListInf (l.map fun u => u * q ^ n) q := by
  induction l with
  | nil => simp [qPochhammerList,qPochhammerListInf]
  | cons u l ih =>
    simp only [qPochhammerListInf,List.map_cons,List.prod_cons,qPochhammerList] at ih ⊢
    rw [qPochhammerInf_mul_qPochhammer (a := u) hq n,ih]
    ring

/-- Clearing all lower infinite products commutes with summing any shifted tail. -/
lemma tsum_clearedListTerm_eq_mul {a b : List (ℂ → ℂ)} {z : ℂ → ℂ} {q x : ℂ}
    (hq : ‖q‖<1) (hreg : QDenominatorRegular (b.map fun f => f x) q) (N : ℕ) :
    (∑' k,clearedListTerm a b z q x (k+N)) =
      qPochhammerListInf (b.map fun f => f x) q *
        ∑' k,qPochhammerList (a.map fun f => f x) q (k+N) /
          qPochhammerList (b.map fun f => f x) q (k+N) * z x^(k+N) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hP := FiniteBilateral.qPochhammerListInf_ne_zero hq hreg
  have hfactor := qPochhammerListInf_factor (b.map fun f => f x) hq (k+N)
  rw [hfactor] at hP
  have hfinite := left_ne_zero_of_mul hP
  rw [clearedListTerm_def,hfactor]
  simp only [qPochhammerList,List.map_map,Function.comp_def] at hfinite ⊢
  simp only [qPochhammerListInf,List.map_map,Function.comp_def]
  field_simp
  simp only [mul_comm,mul_assoc]

/-- Nonvanishing of the lower infinite product excludes every lower q-lattice pole. -/
lemma qDenominatorRegular_of_qPochhammerListInf_ne_zero {l : List ℂ} {q : ℂ}
    (hq : ‖q‖ < 1) (hl : qPochhammerListInf l q ≠ 0) : QDenominatorRegular l q := by
  intro u hu j
  have hP : qPochhammerInf u q ≠ 0 := fun h0 => hl (List.prod_eq_zero (List.mem_map.mpr ⟨u,hu,h0⟩))
  exact mul_pow_ne_one_of_qPochhammerInf_ne_zero hq hP j

/-- Lower regularity persists near every regular finite family of continuous parameters. -/
lemma eventually_qDenominatorRegular_list {l : List (ℂ → ℂ)} {q x : ℂ}
    (hq : ‖q‖ < 1) (hl : ∀ f ∈ l, ContinuousAt f x)
    (hreg : QDenominatorRegular (l.map fun f => f x) q) :
    ∀ᶠ t in 𝓝 x, QDenominatorRegular (l.map fun f => f t) q := by
  have hP := FiniteBilateral.qPochhammerListInf_ne_zero hq hreg
  exact ((continuousAt_qPochhammerListInf hq hl).eventually_ne hP).mono
    fun _ ht => qDenominatorRegular_of_qPochhammerListInf_ne_zero hq ht

/-- A balanced positive-index series is jointly continuous at regular lower parameters. -/
lemma continuousAt_tsum_positive_list {a b : List (ℂ → ℂ)} {z : ℂ → ℂ} {x q : ℂ}
    (hq : ‖q‖ < 1) (ha : ∀ f ∈ a, ContinuousAt f x)
    (hb : ∀ f ∈ b, ContinuousAt f x) (hz : ContinuousAt z x) (hz1 : ‖z x‖ < 1)
    (hreg : QDenominatorRegular (b.map fun f => f x) q) (N : ℕ) :
    ContinuousAt (fun t => ∑' k, qPochhammerList (a.map fun f => f t) q (k+N) /
      qPochhammerList (b.map fun f => f t) q (k+N) * z t ^ (k+N)) x := by
  have hP := FiniteBilateral.qPochhammerListInf_ne_zero hq hreg
  have H := (continuousAt_tsum_clearedListTerm hq ha hb hz hz1 N).div₀
    (continuousAt_qPochhammerListInf hq hb) hP
  apply H.congr
  filter_upwards [(continuousAt_qPochhammerListInf hq hb).eventually_ne hP,
    eventually_qDenominatorRegular_list hq hb hreg] with t ht hrt
  rw [← tsum_div_const]
  refine tsum_congr fun k => ?_
  have htail := ht
  rw [qPochhammerListInf_factor _ hq (k+N)] at htail
  have htail0 := right_ne_zero_of_mul htail
  rw [qPochhammerListInf_factor _ hq (k+N)]
  have hB : qPochhammerList (b.map fun f => f t) q (k+N) ≠ 0 := by
    apply List.prod_ne_zero
    intro h
    rcases List.mem_map.mp h with ⟨u,hu,h0⟩
    exact qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hrt hu _ h0
  simp only [clearedListTerm,qPochhammerList,qPochhammerListInf,List.map_map,Function.comp_def]
  simp only [qPochhammerList,qPochhammerListInf,List.map_map,Function.comp_def] at ht hB htail0
  field_simp
  simp_rw [mul_comm (q ^ (k+N))]
  rw [mul_right_comm]
  exact mul_div_cancel_right₀ _ htail0

/-- A balanced bilateral basic series is jointly continuous throughout its convergence annulus. -/
lemma continuousAt_qPsi {a b : List (ℂ → ℂ)} {z : ℂ → ℂ} {x q : ℂ}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha : ∀ f ∈ a, ContinuousAt f x)
    (hb : ∀ f ∈ b, ContinuousAt f x) (hz : ContinuousAt z x)
    (ha0 : ∀ f ∈ a, f x ≠ 0) (hb0 : ∀ f ∈ b, f x ≠ 0) (hz0 : z x ≠ 0)
    (hlen : a.length = b.length)
    (hreg : QBilateralRegular (a.map fun f => f x) (b.map fun f => f x) q)
    (hw : ‖(b.map fun f => f x).prod / ((a.map fun f => f x).prod * z x)‖ < 1)
    (hz1 : ‖z x‖ < 1) :
    ContinuousAt (fun t => qPsi (a.map fun f => f t) (b.map fun f => f t) q (z t)) x := by
  let A (t : ℂ) := (a.map fun f => f t).prod
  let B (t : ℂ) := (b.map fun f => f t).prod
  let w (t : ℂ) := B t / (A t * z t)
  have hA : ContinuousAt A x := tendsto_list_prod a ha
  have hB : ContinuousAt B x := tendsto_list_prod b hb
  have hA0 : A x ≠ 0 := by
    apply List.prod_ne_zero
    simpa only [List.mem_map,not_exists,not_and] using ha0
  have hB0 : B x ≠ 0 := by
    apply List.prod_ne_zero
    simpa only [List.mem_map,not_exists,not_and] using hb0
  have hW : ContinuousAt w x := hB.div₀ (hA.mul hz) (mul_ne_zero hA0 hz0)
  let ar : List (ℂ → ℂ) := a.map fun f => fun t => q / f t
  let br : List (ℂ → ℂ) := b.map fun f => fun t => q / f t
  have har : ∀ f ∈ ar, ContinuousAt f x := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨g,hg,rfl⟩
    exact continuousAt_const.div₀ (ha g hg) (ha0 g hg)
  have hbr : ∀ f ∈ br, ContinuousAt f x := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨g,hg,rfl⟩
    exact continuousAt_const.div₀ (hb g hg) (hb0 g hg)
  have hregAr : QDenominatorRegular (ar.map fun f => f x) q := by
    simpa only [ar,List.map_map,Function.comp_def] using
      FiniteBilateral.qDenominatorRegular_reciprocal
        (by intro u hu;rcases List.mem_map.mp hu with ⟨f,hf,rfl⟩;exact ha0 f hf) hreg.2
  have Hp := continuousAt_tsum_positive_list hq ha hb hz hz1 hreg.1 0
  have Hn := continuousAt_tsum_positive_list hq hbr har hW hw hregAr 1
  apply (Hp.add Hn).congr
  filter_upwards [eventually_qDenominatorRegular_list hq hb hreg.1,
    eventually_qDenominatorRegular_list hq har hregAr,
    hA.eventually_ne hA0,hB.eventually_ne hB0,hz.eventually_ne hz0,
    hz.norm.eventually_lt_const hz1,hW.norm.eventually_lt_const hw]
    with t htL htR htA htB htZ htZ1 htW
  have htU : ∀ u ∈ a.map (fun f => f t), ∀ j : ℕ, u ≠ q ^ (j+1) := by
    intro u hu j he
    rcases List.mem_map.mp hu with ⟨f,hf,rfl⟩
    have hmem : q / f t ∈ ar.map (fun g => g t) := by
      simp only [ar,List.map_map,Function.comp_def,List.mem_map]
      exact ⟨f,hf,rfl⟩
    apply htR (q / f t) hmem j
    rw [he,pow_succ]
    field_simp
  have H := qPsi_split hq0 hq ⟨htL,htU⟩ htA htB htZ (by simpa using hlen.le) htW
    (fun _ => htZ1)
  rw [H]
  simp only [Pi.add_apply]
  congr 1
  · apply tsum_congr
    intro k
    simp only [Nat.add_zero,qPsiTerm,qPochhammerListInt_natCast,qPsiExponent,List.length_map,
      hlen,sub_self,zpow_zero,mul_one,zpow_natCast]
  · simp only [ar,br,List.map_map,Function.comp_def,w,A,B]

end DLMF.QHypergeometric.BilateralContinuity
