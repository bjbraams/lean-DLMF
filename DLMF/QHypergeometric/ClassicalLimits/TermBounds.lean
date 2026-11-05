/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.ClassicalLimits.ShiftedFactorials

/-!
# Uniform ratios for classical limits of basic hypergeometric series

The normalized factors of a basic hypergeometric term tend uniformly to one beyond a large
index as the positive real base tends to one. The residual q-factorial factor tends uniformly
to zero. Together these give a geometric ratio bound on the classical convergence domain.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Real Topology

namespace DLMF.QHypergeometric.ClassicalLimit

open DLMF.QSeries

/-- The product of the normalized shifted-factorial factors for a parameter list. -/
def normalizedProduct (a : List ℂ) (q : ℝ) (n : ℕ) : ℂ :=
  (a.map fun x => normalizedFactor x q n).prod

/-- Products of normalized factors tend uniformly to one beyond a large index. -/
lemma tendsto_normalizedProduct (a : List ℂ) :
    Tendsto (fun p : ℝ × ℕ => normalizedProduct a p.1 p.2)
      ((𝓝[<] 1) ×ˢ atTop) (𝓝 1) := by
  induction a with
  | nil => simp [normalizedProduct]
  | cons a l ih =>
    simpa [normalizedProduct] using (tendsto_normalizedFactor a).mul ih

/-- The remaining q-factorial ratio after normalization by `1 - q`. -/
def factorialRatio (q : ℝ) (n : ℕ) : ℂ :=
  (q : ℂ) ^ n * (1 - (q : ℂ)) / (1 - (q : ℂ) ^ (n + 1))

/-- The remaining q-factorial ratio tends uniformly to zero beyond a large index. -/
lemma tendsto_factorialRatio :
    Tendsto (fun p : ℝ × ℕ => factorialRatio p.1 p.2)
      ((𝓝[<] 1) ×ˢ atTop) (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (1 : ℂ))).sub (tendsto_normalizedFactor 0)
  simp only [sub_self] at h
  refine h.congr' ?_
  filter_upwards [tendsto_fst.eventually
    (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))] with p hp
  have hq : 1 - (p.1 : ℂ) ^ (p.2 + 1) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr
      (pow_lt_one₀ hp.1.le hp.2 (by omega : p.2 + 1 ≠ 0)).ne'
  dsimp [factorialRatio, normalizedFactor]
  rw [Complex.cpow_zero]
  field_simp [hq]
  simp only [pow_succ]
  ring

/-- The ratio of successive scaled basic-hypergeometric terms, expressed in normalized factors.
-/
def ratioMultiplier (a b : List ℂ) (q : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  normalizedProduct a q n / normalizedProduct b q n *
    factorialRatio q n ^ (b.length + 1 - a.length) * z

/-- Successive normalized term ratios tend to the classical boundary ratio uniformly in the base.
-/
lemma tendsto_ratioMultiplier (a b : List ℂ) (z : ℂ)
    (hr : a.length ≤ b.length + 1) :
    Tendsto (fun p : ℝ × ℕ => ratioMultiplier a b p.1 z p.2)
      ((𝓝[<] 1) ×ˢ atTop)
      (𝓝 (if a.length = b.length + 1 then z else 0)) := by
  have hf := (tendsto_normalizedProduct a).div (tendsto_normalizedProduct b) one_ne_zero
  by_cases he : a.length = b.length + 1
  · simpa [ratioMultiplier, he] using hf.mul_const z
  · have hK : b.length + 1 - a.length ≠ 0 := by omega
    simpa [ratioMultiplier, he, zero_pow hK] using
      (hf.mul (tendsto_factorialRatio.pow (b.length + 1 - a.length))).mul_const z

/-- The scaled basic-hypergeometric terms obey the normalized successive-term recurrence. -/
lemma qPhiTerm_succ (a b : List ℂ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (z : ℂ) (hr : a.length ≤ b.length + 1) (n : ℕ) :
    qPhiTerm (a.map fun x => (q : ℂ) ^ x) (b.map fun x => (q : ℂ) ^ x) q
        (((q : ℂ) - 1) ^ qPhiExponent a b * z) (n + 1) =
      ratioMultiplier a b q z n *
        qPhiTerm (a.map fun x => (q : ℂ) ^ x) (b.map fun x => (q : ℂ) ^ x) q
          (((q : ℂ) - 1) ^ qPhiExponent a b * z) n := by
  let K := b.length + 1 - a.length
  let F (l : List ℂ) := (l.map fun x => 1 - (q : ℂ) ^ x * (q : ℂ) ^ n).prod
  let D : ℂ := 1 - (q : ℂ) ^ (n + 1)
  have hK : qPhiExponent a b = (K : ℤ) := by dsimp [K, qPhiExponent]; omega
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast sub_ne_zero.mpr (pow_lt_one₀ hq0.le hq1 (by omega : n + 1 ≠ 0)).ne'
  have hpow : D ^ a.length * D ^ K = D ^ b.length * D := by
    rw [← pow_add, show a.length + K = b.length + 1 by dsimp [K]; omega, pow_succ]
  have hnorm (l : List ℂ) : normalizedProduct l q n = F l / D ^ l.length := by
    induction l with
    | nil => simp [normalizedProduct, F]
    | cons x l ih =>
      simp only [normalizedProduct, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]
      simp only [F, List.map_cons, List.prod_cons, List.length_cons, normalizedFactor]
      rw [div_mul_div_comm, pow_succ]
      dsimp [D]
      ring
  have hratio : ratioMultiplier a b q z n =
      F a / (F b * D) * ((q : ℂ) ^ n * (1 - (q : ℂ))) ^ K * z := by
    dsimp [ratioMultiplier, factorialRatio]
    rw [hnorm, hnorm]
    change F a / D ^ a.length / (F b / D ^ b.length) *
      (((q : ℂ) ^ n * (1 - (q : ℂ))) / D) ^ K * z = _
    by_cases hb : F b = 0
    · simp [hb]
    · rw [div_pow]
      field_simp [hD, hb]
      linear_combination -F a * ((q : ℂ) ^ n * (1 - (q : ℂ))) ^ K * z * hpow
  have htri (j : ℕ) : DLMF.QSeries.TripleProduct.tri j = (j.choose 2 : ℤ) := by
    simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast j 0).symm
  have ht (j : ℕ) :
      qPhiTerm (a.map fun x => (q : ℂ) ^ x) (b.map fun x => (q : ℂ) ^ x) q
        (((q : ℂ) - 1) ^ qPhiExponent a b * z) j =
      qPochhammerList (a.map fun x => (q : ℂ) ^ x) q j /
        (qPochhammerList (b.map fun x => (q : ℂ) ^ x) q j * qPochhammer q q j) *
        (((q : ℂ) ^ (j.choose 2) * (1 - (q : ℂ)) ^ j) ^ K) * z ^ j := by
    have he : qPhiExponent (a.map fun x => (q : ℂ) ^ x)
      (b.map fun x => (q : ℂ) ^ x) = qPhiExponent a b := by simp [qPhiExponent]
    simp only [qPhiTerm, he]
    rw [mul_assoc, scaling_phase, hK, htri]
    simp only [zpow_mul, zpow_natCast, mul_pow]
    ring
  have hp (l : List ℂ) :
      qPochhammerList (l.map fun x => (q : ℂ) ^ x) q (n + 1) =
      qPochhammerList (l.map fun x => (q : ℂ) ^ x) q n * F l := by
    induction l with
    | nil => simp [qPochhammerList, F]
    | cons x l ih =>
      simp only [List.map_cons, qPochhammerList, List.prod_cons] at ih ⊢
      rw [qPochhammer_succ, ih]
      simp only [F, List.map_cons, List.prod_cons]
      ring
  have hc : (n + 1).choose 2 = n.choose 2 + n := by
    simpa [Nat.add_comm] using (Nat.choose_succ_succ' n 1)
  rw [ht, ht, hp a, hp b, qPochhammer_succ, hc, hratio]
  simp only [D, pow_add, pow_succ, mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

end DLMF.QHypergeometric.ClassicalLimit
