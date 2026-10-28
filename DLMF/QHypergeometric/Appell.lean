/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic

/-!
# q-Appell functions and their transformations (DLMF §§17.4(iii),17.11)

All four functions use the actual double series. Their bidisc convergence is
asserted separately, so totalized `tsum` is never used to claim continuation.
The transformations state a common convergence region and all lower-parameter
exclusions. Products reuse the existing q-Pochhammer symbols.
-/

@[expose] public noncomputable section
open Complex Finset
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- One double-series term of the first q-Appell function. -/
def qAppell1Term (a b bp c q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammer a q (p.1+p.2) * qPochhammer b q p.1 * qPochhammer bp q p.2 *
    x^p.1 * y^p.2 /
    (qPochhammer q q p.1 * qPochhammer q q p.2 * qPochhammer c q (p.1+p.2))
/-- The first q-Appell function, totalized outside its double-series convergence set. -/
@[dlmf 17.4.E5]
def qAppell1 (a b bp c q x y : ℂ) : ℂ := ∑' p : ℕ × ℕ, qAppell1Term a b bp c q x y p

/-- One double-series term of the second q-Appell function. -/
def qAppell2Term (a b bp c cp q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammer a q (p.1+p.2) * qPochhammer b q p.1 * qPochhammer bp q p.2 *
    x^p.1 * y^p.2 /
    (qPochhammerList [q,c] q p.1 * qPochhammerList [q,cp] q p.2)
/-- The second q-Appell function. -/
@[dlmf 17.4.E6]
def qAppell2 (a b bp c cp q x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, qAppell2Term a b bp c cp q x y p

/-- One double-series term of the third q-Appell function. -/
def qAppell3Term (a ap b bp c q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammerList [a,b] q p.1 * qPochhammerList [ap,bp] q p.2 * x^p.1 * y^p.2 /
    (qPochhammer q q p.1 * qPochhammer q q p.2 * qPochhammer c q (p.1+p.2))
/-- The third q-Appell function. -/
@[dlmf 17.4.E7]
def qAppell3 (a ap b bp c q x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, qAppell3Term a ap b bp c q x y p

/-- One double-series term of the fourth q-Appell function. -/
def qAppell4Term (a b c cp q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammerList [a,b] q (p.1+p.2) * x^p.1 * y^p.2 /
    (qPochhammerList [q,c] q p.1 * qPochhammerList [q,cp] q p.2)
/-- The fourth q-Appell function. -/
@[dlmf 17.4.E8]
def qAppell4 (a b c cp q x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, qAppell4Term a b c cp q x y p

/-- Finite shifted factorials are uniformly bounded for `‖q‖<1`. -/
lemma qbR4_qPochhammer_bdd (a : ℂ) {q : ℂ} (hq : ‖q‖<1) :
    ∃ C, 0 ≤ C ∧ ∀ k, ‖qPochhammer a q k‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ (tendsto_qPochhammer (w := a) hq))
  exact ⟨C, (norm_nonneg _).trans (hC _ ⟨0, rfl⟩), fun n => hC _ ⟨n, rfl⟩⟩

/-- Reciprocals of regular finite shifted factorials are uniformly bounded for `‖q‖<1`. -/
lemma qbR4_qPochhammer_inv_bdd {c q : ℂ} (hq : ‖q‖<1) (hc : ∀ n : ℕ, c*q^n ≠ 1) :
    ∃ D, 0 ≤ D ∧ ∀ k, ‖(qPochhammer c q k)⁻¹‖ ≤ D := by
  have h0 : qPochhammerInf c q ≠ 0 :=
    qPochhammerInf_ne_zero hq fun n => sub_ne_zero.mpr (hc n).symm
  obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ ((tendsto_qPochhammer (w := c) hq).inv₀ h0))
  exact ⟨D, (norm_nonneg _).trans (hD _ ⟨0, rfl⟩), fun n => hD _ ⟨n, rfl⟩⟩

/-- `(q;q)_k` is regular for `‖q‖<1`. -/
lemma qbR4_q_regular {q : ℂ} (hq : ‖q‖<1) : ∀ n : ℕ, q*q^n ≠ 1 := by
  intro n h
  apply qPochhammerInf_pow_succ_ne_zero hq n
  rw [pow_succ', h, sub_self]

/-- A double geometric bound gives summability on `ℕ × ℕ`. -/
lemma qbR4_summable_of_geom {f : ℕ × ℕ → ℂ} {x y : ℂ} (hx : ‖x‖<1) (hy : ‖y‖<1) (C : ℝ)
    (h : ∀ p : ℕ × ℕ, ‖f p‖ ≤ C * (‖x‖^p.1 * ‖y‖^p.2)) : Summable f := by
  have hs : Summable fun p : ℕ × ℕ => ‖x‖^p.1 * ‖y‖^p.2 :=
    Summable.mul_of_nonneg (summable_geometric_of_lt_one (norm_nonneg _) hx)
      (summable_geometric_of_lt_one (norm_nonneg _) hy) (fun _ => by positivity)
      (fun _ => by positivity)
  exact Summable.of_norm_bounded (hs.mul_left C) h

/-- All four q-Appell double series converge absolutely on the stated bidisc. -/
@[dlmf 17.4.iii]
theorem summable_qAppell (a ap b bp c cp q x y : ℂ) (hq : ‖q‖<1)
    (hc : qDenominatorRegular [c,cp] q) (hx : ‖x‖<1) (hy : ‖y‖<1) :
    Summable (qAppell1Term a b bp c q x y) ∧
    Summable (qAppell2Term a b bp c cp q x y) ∧
    Summable (qAppell3Term a ap b bp c q x y) ∧
    Summable (qAppell4Term a b c cp q x y) := by
  obtain ⟨A, hA0, hA⟩ := qbR4_qPochhammer_bdd a hq
  obtain ⟨Ap, hAp0, hAp⟩ := qbR4_qPochhammer_bdd ap hq
  obtain ⟨B, hB0, hB⟩ := qbR4_qPochhammer_bdd b hq
  obtain ⟨Bp, hBp0, hBp⟩ := qbR4_qPochhammer_bdd bp hq
  obtain ⟨Dq, hDq0, hDq⟩ := qbR4_qPochhammer_inv_bdd hq (qbR4_q_regular hq)
  obtain ⟨Dc, hDc0, hDc⟩ := qbR4_qPochhammer_inv_bdd hq (hc c (by simp))
  obtain ⟨Dcp, hDcp0, hDcp⟩ := qbR4_qPochhammer_inv_bdd hq (hc cp (by simp))
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine qbR4_summable_of_geom hx hy (A*B*Bp*(Dq*Dq*Dc)) fun p => ?_
    simp only [qAppell1Term, div_eq_mul_inv, mul_inv, norm_mul, norm_pow]
    calc _ ≤ A*B*Bp*‖x‖^p.1*‖y‖^p.2*(Dq*Dq*Dc) := by gcongr <;> simp_all
      _ = _ := by ring
  · refine qbR4_summable_of_geom hx hy (A*B*Bp*(Dq*Dc*(Dq*Dcp))) fun p => ?_
    simp only [qAppell2Term, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, div_eq_mul_inv, mul_inv, norm_mul, norm_pow]
    calc _ ≤ A*B*Bp*‖x‖^p.1*‖y‖^p.2*(Dq*Dc*(Dq*Dcp)) := by gcongr <;> simp_all
      _ = _ := by ring
  · refine qbR4_summable_of_geom hx hy (A*B*(Ap*Bp)*(Dq*Dq*Dc)) fun p => ?_
    simp only [qAppell3Term, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, div_eq_mul_inv, mul_inv, norm_mul, norm_pow]
    calc _ ≤ A*B*(Ap*Bp)*‖x‖^p.1*‖y‖^p.2*(Dq*Dq*Dc) := by gcongr <;> simp_all
      _ = _ := by ring
  · refine qbR4_summable_of_geom hx hy (A*B*(Dq*Dc*(Dq*Dcp))) fun p => ?_
    simp only [qAppell4Term, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, div_eq_mul_inv, mul_inv, norm_mul, norm_pow]
    calc _ ≤ A*B*‖x‖^p.1*‖y‖^p.2*(Dq*Dc*(Dq*Dcp)) := by gcongr <;> simp_all
      _ = _ := by ring

/-- Summability of the transformed double series in `qAppell2_transformation`. -/
private lemma qAppell2_transformation_summable {a b bp c cp q x y : ℂ} (hq : ‖q‖<1) (hb : ‖b‖<1)
    (hy : ‖y‖<1) (hcpr : ∀ k : ℕ, cp*q^k ≠ 1) (haxr : ∀ k : ℕ, a*x*q^k ≠ 1) :
    Summable (fun p : ℕ × ℕ => qPochhammerList [a,bp] q p.1 * qPochhammerList [c/b,x] q p.2 *
            b^p.2 * y^p.1 /
            (qPochhammerList [q,cp] q p.1 * qPochhammer q q p.2 *
              qPochhammer (a*x) q (p.1+p.2))) := by
  obtain ⟨A, hA0, hA⟩ := qbR4_qPochhammer_bdd a hq
  obtain ⟨Bp, hBp0, hBp⟩ := qbR4_qPochhammer_bdd bp hq
  obtain ⟨Cb, hCb0, hCb⟩ := qbR4_qPochhammer_bdd (c/b) hq
  obtain ⟨X, hX0, hX⟩ := qbR4_qPochhammer_bdd x hq
  obtain ⟨Dq, hDq0, hDq⟩ := qbR4_qPochhammer_inv_bdd hq (qbR4_q_regular hq)
  obtain ⟨Dcp, hDcp0, hDcp⟩ := qbR4_qPochhammer_inv_bdd hq hcpr
  obtain ⟨Dax, hDax0, hDax⟩ := qbR4_qPochhammer_inv_bdd hq haxr
  refine qbR4_summable_of_geom hy hb (A*Bp*(Cb*X)*(Dq*Dcp*Dq*Dax)) fun p => ?_
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [div_eq_mul_inv]
  simp only [mul_inv, norm_mul, norm_pow]
  calc _ ≤ A*Bp*(Cb*X)*‖b‖^p.2*‖y‖^p.1*(Dq*Dcp*Dq*Dax) := by
        gcongr <;> simp_all
    _ = _ := by ring

/-- Summability of the transformed double series in `qAppell3_transformation`. -/
private lemma qAppell3_transformation_summable {a ap b bp c q x y : ℂ} (hq : ‖q‖<1) (ha : ‖a‖<1)
    (hy : ‖y‖<1) (hcar : ∀ k : ℕ, c/a*q^k ≠ 1) (hbxr : ∀ k : ℕ, b*x*q^k ≠ 1) :
    Summable (fun p : ℕ × ℕ => qPochhammerList [ap,bp] q p.1 * qPochhammer x q p.2 *
            qPochhammer (c/a) q (p.1+p.2) * a^p.2 * y^p.1 /
            (qPochhammerList [q,c/a] q p.1 * qPochhammerList [q,b*x] q p.2)) := by
  obtain ⟨Ap, hAp0, hAp⟩ := qbR4_qPochhammer_bdd ap hq
  obtain ⟨Bp, hBp0, hBp⟩ := qbR4_qPochhammer_bdd bp hq
  obtain ⟨Ca, hCa0, hCa⟩ := qbR4_qPochhammer_bdd (c/a) hq
  obtain ⟨X, hX0, hX⟩ := qbR4_qPochhammer_bdd x hq
  obtain ⟨Dq, hDq0, hDq⟩ := qbR4_qPochhammer_inv_bdd hq (qbR4_q_regular hq)
  obtain ⟨Dca, hDca0, hDca⟩ := qbR4_qPochhammer_inv_bdd hq hcar
  obtain ⟨Dbx, hDbx0, hDbx⟩ := qbR4_qPochhammer_inv_bdd hq hbxr
  refine qbR4_summable_of_geom hy ha (Ap*Bp*X*Ca*(Dq*Dca*(Dq*Dbx))) fun p => ?_
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [div_eq_mul_inv]
  simp only [mul_inv, norm_mul, norm_pow]
  calc _ ≤ Ap*Bp*X*Ca*‖a‖^p.2*‖y‖^p.1*(Dq*Dca*(Dq*Dbx)) := by
        gcongr <;> simp_all
    _ = _ := by ring

/-- Transformation of the second q-Appell function to a normally convergent double series. -/
@[dlmf 17.11.E2]
theorem qAppell2_transformation (a b bp c cp q x y : ℂ)
    (hq : ‖q‖<1) (hb0 : b≠0) (hb : ‖b‖<1) (hx : ‖x‖<1) (hy : ‖y‖<1)
    (hc : qDenominatorRegular [c,cp,a*x] q) :
    qAppell2 a b bp c cp q x y =
      qPochhammerListInf [b,a*x] q / qPochhammerListInf [c,x] q *
        ∑' p : ℕ × ℕ,
          qPochhammerList [a,bp] q p.1 * qPochhammerList [c/b,x] q p.2 *
            b^p.2 * y^p.1 /
            (qPochhammerList [q,cp] q p.1 * qPochhammer q q p.2 *
              qPochhammer (a*x) q (p.1+p.2)) := by
  have hcr : ∀ k : ℕ, c*q^k ≠ 1 := hc c (by simp)
  have hcpr : ∀ k : ℕ, cp*q^k ≠ 1 := hc cp (by simp)
  have haxr : ∀ k : ℕ, a*x*q^k ≠ 1 := hc (a*x) (by simp)
  have haxf : ∀ k : ℕ, 1 - a*x*q^k ≠ 0 := fun k => sub_ne_zero.mpr (haxr k).symm
  have hT := (summable_qAppell a a b bp c cp q x y hq (fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> assumption) hx hy).2.1
  set U : ℕ × ℕ → ℂ := fun p => qPochhammerList [a,bp] q p.1 * qPochhammerList [c/b,x] q p.2 *
            b^p.2 * y^p.1 /
            (qPochhammerList [q,cp] q p.1 * qPochhammer q q p.2 *
              qPochhammer (a*x) q (p.1+p.2)) with hUdef
  have hU : Summable U := qAppell2_transformation_summable hq hb hy hcpr haxr
  -- inner sums by Heine
  have hinner : ∀ n : ℕ, ∑' m : ℕ, qAppell2Term a b bp c cp q x y (m, n) =
      qPochhammerListInf [b,a*x] q / qPochhammerListInf [c,x] q * ∑' j : ℕ, U (n, j) := by
    intro n
    have hH := heine_transformation (a := a*q^n) (b := b) (c := c) (z := x) hq hx hb hb0 hcr
      (fun k => by rw [show a*q^n*x*q^k = a*x*q^(n+k) by ring]; exact haxr _)
    simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at hH
    have hsplit := qPochhammerInf_mul_qPochhammer (a := a*x) hq n
    have haxn : qPochhammer (a*x) q n ≠ 0 := qPochhammer_ne_zero_of_factors hq haxf n
    have hqn : qPochhammer q q n ≠ 0 := qPochhammer_self_ne_zero hq n
    have hcpn : qPochhammer cp q n ≠ 0 :=
      qPochhammer_ne_zero_of_factors hq (fun k => sub_ne_zero.mpr (hcpr k).symm) n
    rw [show a*q^n*x = a*x*q^n by ring] at hH
    set W := qPochhammer a q n * qPochhammer bp q n * y^n / (qPochhammer q q n * qPochhammer cp q n)
    have hL : ∀ m : ℕ, qAppell2Term a b bp c cp q x y (m, n) =
        W * (qPochhammer (a*q^n) q m * qPochhammer b q m / (qPochhammer c q m * qPochhammer q q m) *
          x^m) := by
      intro m
      have hqm : qPochhammer q q m ≠ 0 := qPochhammer_self_ne_zero hq m
      have hcm : qPochhammer c q m ≠ 0 :=
        qPochhammer_ne_zero_of_factors hq (fun k => sub_ne_zero.mpr (hcr k).symm) m
      simp only [qAppell2Term, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, W]
      rw [add_comm m n, qPochhammer_add]
      field_simp
    have hR : ∀ j : ℕ, qPochhammerListInf [b,a*x] q / qPochhammerListInf [c,x] q * U (n, j) =
        W * (qPochhammerInf b q * qPochhammerInf (a*x*q^n) q /
          (qPochhammerInf c q * qPochhammerInf x q)) *
        (qPochhammer (c/b) q j * qPochhammer x q j / (qPochhammer (a*x*q^n) q j * qPochhammer q q j) *
          b^j) := by
      intro j
      have hqj : qPochhammer q q j ≠ 0 := qPochhammer_self_ne_zero hq j
      have haxj : qPochhammer (a*x*q^n) q j ≠ 0 := qPochhammer_ne_zero_of_factors hq
        (fun k => by rw [mul_assoc, ← pow_add]; exact haxf _) j
      simp only [hUdef, qPochhammerListInf, qPochhammerList, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, W]
      rw [qPochhammer_add, hsplit]
      have hc0 : qPochhammerInf c q ≠ 0 := qPochhammerInf_ne_zero hq (fun k => sub_ne_zero.mpr (hcr k).symm)
      have hx0 : qPochhammerInf x q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hx hq
      field_simp
    rw [tsum_congr hL, tsum_mul_left, hH]
    conv_rhs => rw [← tsum_mul_left, tsum_congr hR, tsum_mul_left]
    ring
  have hT' : Summable (Function.uncurry fun m n => qAppell2Term a b bp c cp q x y (m, n)) := hT
  rw [qAppell2, hT.tsum_prod, ← hT'.tsum_comm, tsum_congr hinner, tsum_mul_left, ← hU.tsum_prod]

/-- Transformation of the third q-Appell function. -/
@[dlmf 17.11.E3]
theorem qAppell3_transformation (a ap b bp c q x y : ℂ)
    (hq : ‖q‖<1) (ha0 : a≠0) (ha : ‖a‖<1) (hx : ‖x‖<1) (hy : ‖y‖<1)
    (hc : qDenominatorRegular [c,c/a,b*x] q) :
    qAppell3 a ap b bp c q x y =
      qPochhammerListInf [a,b*x] q / qPochhammerListInf [c,x] q *
        ∑' p : ℕ × ℕ,
          qPochhammerList [ap,bp] q p.1 * qPochhammer x q p.2 *
            qPochhammer (c/a) q (p.1+p.2) * a^p.2 * y^p.1 /
            (qPochhammerList [q,c/a] q p.1 * qPochhammerList [q,b*x] q p.2) := by
  have hcr : ∀ k : ℕ, c*q^k ≠ 1 := hc c (by simp)
  have hcar : ∀ k : ℕ, c/a*q^k ≠ 1 := hc (c/a) (by simp)
  have hbxr : ∀ k : ℕ, b*x*q^k ≠ 1 := hc (b*x) (by simp)
  have hcf : ∀ k : ℕ, 1 - c*q^k ≠ 0 := fun k => sub_ne_zero.mpr (hcr k).symm
  have hcaf : ∀ k : ℕ, 1 - c/a*q^k ≠ 0 := fun k => sub_ne_zero.mpr (hcar k).symm
  have hbxf : ∀ k : ℕ, 1 - b*x*q^k ≠ 0 := fun k => sub_ne_zero.mpr (hbxr k).symm
  have hT := (summable_qAppell a ap b bp c c q x y hq (fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> assumption) hx hy).2.2.1
  set U : ℕ × ℕ → ℂ := fun p => qPochhammerList [ap,bp] q p.1 * qPochhammer x q p.2 *
            qPochhammer (c/a) q (p.1+p.2) * a^p.2 * y^p.1 /
            (qPochhammerList [q,c/a] q p.1 * qPochhammerList [q,b*x] q p.2) with hUdef
  have hU : Summable U := qAppell3_transformation_summable hq ha hy hcar hbxr
  have hinner : ∀ n : ℕ, ∑' m : ℕ, qAppell3Term a ap b bp c q x y (m, n) =
      qPochhammerListInf [a,b*x] q / qPochhammerListInf [c,x] q * ∑' j : ℕ, U (n, j) := by
    intro n
    have hH := heine_transformation (a := b) (b := a) (c := c*q^n) (z := x) hq hx ha ha0
      (fun k => by rw [mul_assoc, ← pow_add]; exact hcr _) hbxr
    simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at hH
    have hsplit := qPochhammerInf_mul_qPochhammer (a := c) hq n
    have hcn : qPochhammer c q n ≠ 0 := qPochhammer_ne_zero_of_factors hq hcf n
    have hcan : qPochhammer (c/a) q n ≠ 0 := qPochhammer_ne_zero_of_factors hq hcaf n
    have hqn : qPochhammer q q n ≠ 0 := qPochhammer_self_ne_zero hq n
    rw [show c*q^n/a = c/a*q^n by ring] at hH
    set W := qPochhammer ap q n * qPochhammer bp q n * y^n / (qPochhammer q q n * qPochhammer c q n)
    have hL : ∀ m : ℕ, qAppell3Term a ap b bp c q x y (m, n) =
        W * (qPochhammer b q m * qPochhammer a q m / (qPochhammer (c*q^n) q m * qPochhammer q q m) *
          x^m) := by
      intro m
      have hqm : qPochhammer q q m ≠ 0 := qPochhammer_self_ne_zero hq m
      have hcm : qPochhammer (c*q^n) q m ≠ 0 :=
        qPochhammer_ne_zero_of_factors hq (fun k => by rw [mul_assoc, ← pow_add]; exact hcf _) m
      simp only [qAppell3Term, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, W]
      rw [add_comm m n, qPochhammer_add]
      field_simp
    have hR : ∀ j : ℕ, qPochhammerListInf [a,b*x] q / qPochhammerListInf [c,x] q * U (n, j) =
        W * (qPochhammerInf a q * qPochhammerInf (b*x) q /
          (qPochhammerInf (c*q^n) q * qPochhammerInf x q)) *
        (qPochhammer (c/a*q^n) q j * qPochhammer x q j / (qPochhammer (b*x) q j * qPochhammer q q j) *
          a^j) := by
      intro j
      have hqj : qPochhammer q q j ≠ 0 := qPochhammer_self_ne_zero hq j
      have hbxj : qPochhammer (b*x) q j ≠ 0 := qPochhammer_ne_zero_of_factors hq hbxf j
      simp only [hUdef, qPochhammerListInf, qPochhammerList, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, W]
      rw [qPochhammer_add, hsplit]
      have hc0 : qPochhammerInf (c*q^n) q ≠ 0 := qPochhammerInf_shift_ne_zero hq hcf n
      have hx0 : qPochhammerInf x q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hx hq
      field_simp
    rw [tsum_congr hL, tsum_mul_left, hH]
    conv_rhs => rw [← tsum_mul_left, tsum_congr hR, tsum_mul_left]
    ring
  have hT' : Summable (Function.uncurry fun m n => qAppell3Term a ap b bp c q x y (m, n)) := hT
  rw [qAppell3, hT.tsum_prod, ← hT'.tsum_comm, tsum_congr hinner, tsum_mul_left, ← hU.tsum_prod]

/-- The multivariate series generalizing the first q-Appell function. -/
def qLauricellaTerm (n : ℕ) (a c q : ℂ) (b x : Fin n → ℂ) (m : Fin n → ℕ) : ℂ :=
  qPochhammer a q (∑ i, m i) * (∏ i, qPochhammer (b i) q (m i) * x i ^ m i) /
    ((∏ i, qPochhammer q q (m i)) * qPochhammer c q (∑ i, m i))

/-- Multivariate geometric series are summable. -/
lemma qbR4_summable_pi_geom : ∀ (n : ℕ) (r : Fin n → ℝ), (∀ i, 0 ≤ r i) → (∀ i, r i < 1) →
    Summable fun m : Fin n → ℕ => ∏ i, r i ^ m i
  | 0, r, _, _ => Summable.of_finite
  | n+1, r, h0, h1 => by
    have ih := qbR4_summable_pi_geom n (fun i => r i.succ) (fun i => h0 _) (fun i => h1 _)
    have hs := Summable.mul_of_nonneg (summable_geometric_of_lt_one (h0 0) (h1 0)) ih
      (fun _ => by have := h0 0; positivity)
      (fun m => prod_nonneg fun i _ => pow_nonneg (h0 _) _)
    rw [← (Fin.consEquiv fun _ : Fin (n+1) => ℕ).summable_iff]
    refine hs.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

/-- Absolute convergence of the multivariate Appell generalization. -/
@[dlmf 17.11.E4]
theorem summable_qLauricella (n : ℕ) (a c q : ℂ) (b x : Fin n → ℂ)
    (hq : ‖q‖<1) (hc : qDenominatorRegular [c] q) (hx : ∀ i, ‖x i‖<1) :
    Summable (qLauricellaTerm n a c q b x) := by
  obtain ⟨A, hA0, hA⟩ := qbR4_qPochhammer_bdd a hq
  obtain ⟨Dq, hDq0, hDq⟩ := qbR4_qPochhammer_inv_bdd hq (qbR4_q_regular hq)
  obtain ⟨Dc, hDc0, hDc⟩ := qbR4_qPochhammer_inv_bdd hq (hc c (by simp))
  choose B hB0 hB using fun i => qbR4_qPochhammer_bdd (b i) hq
  have hs := qbR4_summable_pi_geom n (fun i => ‖x i‖) (fun i => norm_nonneg _) hx
  refine Summable.of_norm_bounded (hs.mul_left (A * Dc * ∏ i, (B i * Dq))) fun m => ?_
  simp only [qLauricellaTerm, div_eq_mul_inv, mul_inv, ← prod_inv_distrib, norm_mul, norm_prod,
    norm_pow]
  calc _ = ‖qPochhammer a q (∑ i, m i)‖ * (∏ i, ‖qPochhammer (b i) q (m i)‖ * ‖x i‖ ^ m i) *
        (∏ i, ‖(qPochhammer q q (m i))⁻¹‖) * ‖(qPochhammer c q (∑ i, m i))⁻¹‖ := by ring
    _ ≤ A * (∏ i, (B i * ‖x i‖^m i)) * (∏ i, Dq) * Dc := by
        have h1 : ∏ i, ‖qPochhammer (b i) q (m i)‖ * ‖x i‖ ^ m i ≤ ∏ i, (B i * ‖x i‖^m i) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ =>
            mul_le_mul_of_nonneg_right (hB i _) (by positivity)
        have h2 : ∏ i, ‖(qPochhammer q q (m i))⁻¹‖ ≤ ∏ i, Dq :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => hDq _
        have h3 : 0 ≤ ∏ i, (B i * ‖x i‖^m i) := prod_nonneg fun i _ => by
          have := hB0 i; positivity
        refine mul_le_mul (mul_le_mul (mul_le_mul (hA _) h1 (by positivity) hA0) h2
          (by positivity) (by positivity)) (hDc _) (by positivity) (by positivity)
    _ = _ := by simp only [prod_mul_distrib]; ring

/-- Sums of products over `Fin n → ℕ` factor into products of absolutely convergent sums. -/
lemma qbR4_tsum_pi_prod : ∀ (n : ℕ) (f : Fin n → ℕ → ℂ), (∀ i, Summable fun k => ‖f i k‖) →
    Summable (fun m : Fin n → ℕ => ‖∏ i, f i (m i)‖) ∧
      ∑' m : Fin n → ℕ, ∏ i, f i (m i) = ∏ i, ∑' k, f i k
  | 0, f, _ => by
    refine ⟨Summable.of_finite, ?_⟩
    simp [tsum_fintype]
  | n+1, f, hf => by
    obtain ⟨ih1, ih2⟩ := qbR4_tsum_pi_prod n (fun i => f i.succ) (fun i => hf _)
    let e := Fin.consEquiv fun _ : Fin (n+1) => ℕ
    have he : ∀ p : ℕ × (Fin n → ℕ), (∏ i, f i (e p i)) = f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i) := by
      intro p
      simp [e, Fin.consEquiv, Fin.prod_univ_succ]
    have hs : Summable fun p : ℕ × (Fin n → ℕ) => ‖f 0 p.1‖ * ‖∏ i : Fin n, f i.succ (p.2 i)‖ :=
      Summable.mul_of_nonneg (hf 0) ih1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine ⟨?_, ?_⟩
    · rw [← e.summable_iff]
      refine hs.congr fun p => ?_
      simp only [Function.comp_apply, he, norm_mul]
    · rw [← e.tsum_eq]
      simp only [he]
      rw [← tsum_mul_tsum_of_summable_norm (hf 0) ih1, ih2, Fin.prod_univ_succ]

/-- Multiplying by a power of `q` with `‖q‖ ≤ 1` does not increase the norm. -/
private lemma qbR4_norm_mul_pow_le {q : ℂ} (hq : ‖q‖<1) (w : ℂ) (j : ℕ) : ‖w*q^j‖ ≤ ‖w‖ := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)

/-- The terms `(β;q)_m/(q;q)_m (w q^j)^m` of a shifted q-binomial series are bounded by
`M ‖w‖^m`, uniformly in the shift `j`. -/
private lemma qbR4_shift_term_bdd {q : ℂ} (hq : ‖q‖<1) (β w : ℂ) :
    ∃ M, 0 ≤ M ∧ ∀ j m, ‖qPochhammer β q m / qPochhammer q q m * (w*q^j)^m‖ ≤ M * ‖w‖^m := by
  obtain ⟨Dq, hDq0, hDq⟩ := qbR4_qPochhammer_inv_bdd hq (qbR4_q_regular hq)
  obtain ⟨B, hB0, hB⟩ := qbR4_qPochhammer_bdd β hq
  refine ⟨B*Dq, by positivity, fun j m => ?_⟩
  simp only [div_eq_mul_inv, norm_mul, norm_pow]
  gcongr
  · exact hB m
  · exact hDq m
  · simpa [norm_mul, norm_pow] using qbR4_norm_mul_pow_le hq w j

/-- Shifting the argument of a ratio of infinite q-shifted factorials by `q^j`:
`(β w q^j;q)_∞/(w q^j;q)_∞ = (β w;q)_∞/(w;q)_∞ · (w;q)_j/(β w;q)_j`. -/
private lemma qbR4_inf_ratio_shift {q β w : ℂ} (hq : ‖q‖<1) (hwf : ∀ k : ℕ, 1 - w*q^k ≠ 0)
    (hbwf : ∀ k : ℕ, 1 - β*w*q^k ≠ 0) (j : ℕ) :
    qPochhammerInf (β*(w*q^j)) q / qPochhammerInf (w*q^j) q =
      qPochhammerInf (β*w) q / qPochhammerInf w q *
        (qPochhammer w q j / qPochhammer (β*w) q j) := by
  have e1 := qPochhammerInf_mul_qPochhammer (a := w) hq j
  have e3 := qPochhammerInf_mul_qPochhammer (a := β*w) hq j
  rw [show β*(w*q^j) = β*w*q^j by ring, e1, e3]
  have n1 := qPochhammerInf_shift_ne_zero hq hwf j
  have n3 := qPochhammer_ne_zero_of_factors hq hbwf j
  have n8 := qPochhammer_ne_zero_of_factors hq hwf j
  field_simp

/-- The full n-variable generalization, including the empty-variable case. -/
@[dlmf 17.11.E4]
theorem qLauricella_transformation (n : ℕ) (a c q : ℂ) (b x : Fin n → ℂ)
    (hq : ‖q‖<1) (ha0 : a≠0) (ha : ‖a‖<1) (hx : ∀ i, ‖x i‖<1)
    (hc : qDenominatorRegular (c :: List.ofFn (fun i => b i*x i)) q) :
    (∑' m : Fin n → ℕ, qLauricellaTerm n a c q b x m) =
      qPochhammerListInf (a :: List.ofFn (fun i => b i*x i)) q /
        qPochhammerListInf (c :: List.ofFn x) q *
          qPhi ((c/a) :: List.ofFn x) (List.ofFn (fun i => b i*x i)) q a := by
  have hcr : ∀ k : ℕ, c*q^k ≠ 1 := hc c (by simp)
  have hbxr : ∀ i, ∀ k : ℕ, b i*x i*q^k ≠ 1 := fun i => hc (b i*x i) (by
    simp only [List.mem_cons, List.mem_ofFn]; exact Or.inr ⟨i, rfl⟩)
  have hcf : ∀ k : ℕ, 1 - c*q^k ≠ 0 := fun k => sub_ne_zero.mpr (hcr k).symm
  have hbxf : ∀ i, ∀ k : ℕ, 1 - b i*x i*q^k ≠ 0 := fun i k => sub_ne_zero.mpr (hbxr i k).symm
  have haf : ∀ k : ℕ, 1 - a*q^k ≠ 0 := one_sub_mul_pow_ne_zero_of_norm ha hq
  have hxf : ∀ i, ∀ k : ℕ, 1 - x i*q^k ≠ 0 := fun i => one_sub_mul_pow_ne_zero_of_norm (hx i) hq
  have hpow := qbR4_norm_mul_pow_le hq
  set C : ℕ → ℂ := fun j => qPochhammer (c/a) q j / qPochhammer q q j * a^j with hC
  set F : ℂ → ℂ → ℕ → ℕ → ℂ := fun β w j m => qPochhammer β q m / qPochhammer q q m * (w*q^j)^m
    with hF
  set G : (Fin n → ℕ) × ℕ → ℂ := fun z => C z.2 * ∏ i, F (b i) (x i) z.2 (z.1 i) with hG
  choose M hM0 hM using fun i => qbR4_shift_term_bdd hq (b i) (x i)
  obtain ⟨Mc, hMc0, hMc'⟩ := qbR4_shift_term_bdd hq (c/a) a
  have hMc : ∀ j, ‖C j‖ ≤ Mc * ‖a‖^j := fun j => by simpa [hC] using hMc' 0 j
  have hGs : Summable G := by
    have h2 := qbR4_summable_pi_geom n (fun i => ‖x i‖) (fun i => norm_nonneg _) hx
    have h3 := Summable.mul_of_nonneg h2 (summable_geometric_of_lt_one (norm_nonneg _) ha)
      (fun _ => prod_nonneg fun _ _ => by positivity) (fun _ => by positivity)
    refine Summable.of_norm_bounded (h3.mul_left (Mc * ∏ i, M i)) fun z => ?_
    simp only [hG, norm_mul, norm_prod]
    calc _ ≤ (Mc*‖a‖^z.2) * ∏ i, (M i * ‖x i‖^(z.1 i)) := by
          gcongr with i
          · exact hMc _
          · exact hM i _ _
      _ = _ := by rw [prod_mul_distrib]; ring
  have hc0 : qPochhammerInf c q ≠ 0 := qPochhammerInf_ne_zero hq hcf
  have hstep1 : ∀ m : Fin n → ℕ, qLauricellaTerm n a c q b x m =
      qPochhammerInf a q / qPochhammerInf c q * ∑' j : ℕ, G (m, j) := by
    intro m
    have hk : ‖a*q^(∑ i, m i)‖ < 1 := lt_of_le_of_lt (hpow a _) ha
    have hqb := q_binomial_theorem (a := c/a) hq hk
    rw [show c/a*(a*q^(∑ i, m i)) = c*q^(∑ i, m i) by field_simp] at hqb
    have hW : ∀ j : ℕ, G (m, j) = (∏ i, qPochhammer (b i) q (m i) / qPochhammer q q (m i) * x i^(m i)) *
        (qPochhammer (c/a) q j / qPochhammer q q j * (a*q^(∑ i, m i))^j) := by
      intro j
      simp only [hG, hC, hF, mul_pow, ← pow_mul, ← prod_pow_eq_pow_sum, prod_mul_distrib]
      rw [← Finset.prod_pow]
      simp only [← pow_mul, Nat.mul_comm]
      ring
    rw [tsum_congr hW, tsum_mul_left, ← hqb]
    have hA := qPochhammer_eq_div_inf hq haf (∑ i, m i)
    have hCc := qPochhammer_eq_div_inf hq hcf (∑ i, m i)
    have h1 := qPochhammerInf_shift_ne_zero hq haf (∑ i, m i)
    have h2 := qPochhammerInf_shift_ne_zero hq hcf (∑ i, m i)
    have hqm : ∏ i, qPochhammer q q (m i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ =>
      qPochhammer_self_ne_zero hq _
    simp only [qLauricellaTerm, prod_mul_distrib, prod_div_distrib]
    rw [hA, hCc]
    field_simp
  have hGu : Summable (Function.uncurry fun (m : Fin n → ℕ) (j : ℕ) => G (m, j)) := hGs
  have hstep4 : ∀ j : ℕ, ∑' m : Fin n → ℕ, G (m, j) =
      C j * ∏ i, (qPochhammerInf (b i*(x i*q^j)) q / qPochhammerInf (x i*q^j) q) := by
    intro j
    simp only [hG]
    rw [tsum_mul_left, (qbR4_tsum_pi_prod n (fun i => F (b i) (x i) j) fun i =>
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hM i j)
        ((summable_geometric_of_lt_one (norm_nonneg _) (hx i)).mul_left (M i))).2]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    rw [q_binomial_theorem hq (lt_of_le_of_lt (hpow (x i) j) (hx i))]
  have hfin : ∀ j : ℕ, qPochhammerInf a q / qPochhammerInf c q *
      (C j * ∏ i, (qPochhammerInf (b i*(x i*q^j)) q / qPochhammerInf (x i*q^j) q)) =
      qPochhammerListInf (a :: List.ofFn (fun i => b i*x i)) q /
        qPochhammerListInf (c :: List.ofFn x) q *
        qPhiTerm ((c/a) :: List.ofFn x) (List.ofFn (fun i => b i*x i)) q a j := by
    intro j
    rw [prod_congr rfl fun i _ => qbR4_inf_ratio_shift hq (hxf i) (hbxf i) j, prod_mul_distrib,
      prod_div_distrib, prod_div_distrib]
    have n2 : ∏ i, qPochhammerInf (x i) q ≠ 0 := prod_ne_zero_iff.mpr fun i _ =>
      qPochhammerInf_ne_zero_of_norm_lt_one (hx i) hq
    have n3 : ∏ i, qPochhammer (x i) q j ≠ 0 := prod_ne_zero_iff.mpr fun i _ =>
      qPochhammer_ne_zero_of_factors hq (hxf i) j
    have n4 : ∏ i, qPochhammer (b i*x i) q j ≠ 0 := prod_ne_zero_iff.mpr fun i _ =>
      qPochhammer_ne_zero_of_factors hq (hbxf i) j
    have n5 := qPochhammer_self_ne_zero hq j
    have hexp : qPhiExponent ((c/a) :: List.ofFn x) (List.ofFn (fun i => b i*x i)) = 0 := by
      simp [qPhiExponent]; ring
    simp only [qPhiTerm, hexp, zpow_zero, mul_one, qPochhammerListInf, qPochhammerList,
      List.map_cons, List.map_ofFn, List.prod_cons, List.prod_ofFn, Function.comp_apply, hC]
    generalize ∏ i, qPochhammerInf (b i*x i) q = P1 at *
    generalize ∏ i, qPochhammerInf (x i) q = P2 at *
    generalize ∏ i, qPochhammer (x i) q j = P3 at *
    generalize ∏ i, qPochhammer (b i*x i) q j = P4 at *
    field_simp
  rw [tsum_congr hstep1, tsum_mul_left, ← hGu.tsum_comm, tsum_congr hstep4,
    ← tsum_mul_left, tsum_congr hfin, tsum_mul_left, qPhi]

/-- The multivariate q-Appell coefficient at two variables is the first q-Appell coefficient. -/
@[dlmf 17.11]
theorem qLauricellaTerm_two (a b bp c q x y : ℂ) (m : Fin 2 → ℕ) :
    qLauricellaTerm 2 a c q ![b,bp] ![x,y] m =
      qAppell1Term a b bp c q x y (m 0,m 1) := by
  simp [qLauricellaTerm,qAppell1Term,Fin.sum_univ_two,Fin.prod_univ_two]
  ring

/-- DLMF 17.11p2: the multivariate transformation specializes to the first q-Appell series
when n=2. Reindexing holds even for totalized series; convergence hypotheses are unchanged. -/
@[dlmf 17.11]
theorem qLauricella_two (a b bp c q x y : ℂ) :
    (∑' m : Fin 2 → ℕ, qLauricellaTerm 2 a c q ![b,bp] ![x,y] m) =
      qAppell1 a b bp c q x y := by
  calc
    (∑' m : Fin 2 → ℕ, qLauricellaTerm 2 a c q ![b,bp] ![x,y] m)
        = ∑' m : Fin 2 → ℕ, qAppell1Term a b bp c q x y (m 0,m 1) :=
          tsum_congr (qLauricellaTerm_two a b bp c q x y)
    _ = ∑' p : ℕ × ℕ, qAppell1Term a b bp c q x y p :=
          (finTwoArrowEquiv ℕ).tsum_eq _
    _ = qAppell1 a b bp c q x y := rfl

/-- Reduction of the first q-Appell function to a 3-phi-2. -/
@[dlmf 17.11.E1]
theorem qAppell1_transformation (a b bp c q x y : ℂ)
    (hq : ‖q‖<1) (ha0 : a≠0) (ha : ‖a‖<1) (hx : ‖x‖<1) (hy : ‖y‖<1)
    (hc : qDenominatorRegular [c,b*x,bp*y] q) :
    qAppell1 a b bp c q x y =
      qPochhammerListInf [a,b*x,bp*y] q / qPochhammerListInf [c,x,y] q *
        qPhi [c/a,x,y] [b*x,bp*y] q a := by
  have h2 : List.ofFn (fun i : Fin 2 => ![b,bp] i * ![x,y] i) = [b*x,bp*y] := by
    simp [List.ofFn_succ]
  have h2' : List.ofFn ![x,y] = [x,y] := by simp [List.ofFn_succ]
  have h := qLauricella_transformation 2 a c q ![b,bp] ![x,y] hq ha0 ha
    (Fin.forall_fin_two.mpr ⟨hx, hy⟩) (by rw [h2]; exact hc)
  rw [qLauricella_two, h2, h2'] at h
  exact h

end DLMF.QHypergeometric
