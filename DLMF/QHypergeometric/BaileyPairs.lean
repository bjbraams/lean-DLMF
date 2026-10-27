/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bailey

/-!
# Bailey transforms and pairs (DLMF §17.12)

The finite Bailey-pair definition, Bailey lemma and Watson transformation are
already proved in `DLMF.Bailey`. This module adds the general double-series
transform and the remaining infinite identity and explicit pair.
The general transform uses absolute summability, the hypothesis permitting
the interchange of its two infinite sums.
-/

@[expose] public noncomputable section
open Complex Finset Filter DLMF.QSeries
open scoped Topology
namespace DLMF.QHypergeometric

/-- The finite row of a general Bailey transform. -/
@[dlmf 17.12.E2]
def generalBaileyBeta (u v α : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ range (n + 1), α j * u (n - j) * v (n + j)

/-- The infinite column of a general Bailey transform. -/
@[dlmf 17.12.E2]
def generalBaileyGamma (u v δ : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑' n : ℕ, if j ≤ n then δ n * u (n - j) * v (n + j) else 0

/-- General Bailey transform, with the double-sum convergence needed by Fubini. -/
@[dlmf 17.12.E1]
theorem generalBaileyTransform (u v α δ : ℕ → ℂ)
    (hF : Summable (fun p : ℕ × ℕ =>
      if p.2 ≤ p.1 then α p.2 * δ p.1 * u (p.1 - p.2) * v (p.1 + p.2) else 0)) :
    (∑' j : ℕ, α j * generalBaileyGamma u v δ j) =
      ∑' n : ℕ, generalBaileyBeta u v α n * δ n := by
  let F : ℕ → ℕ → ℂ := fun n j =>
    if j ≤ n then α j * δ n * u (n - j) * v (n + j) else 0
  have hrow (n : ℕ) : (∑' j, F n j) = generalBaileyBeta u v α n * δ n := by
    have hs : HasSum (F n) (∑ j ∈ range (n + 1), F n j) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        have hj' : ¬j ≤ n := by simpa using hj
        simp [F, hj']
    rw [hs.tsum_eq, generalBaileyBeta, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ n := by simpa using hj
    simp [F, hj']
    ring
  have hcol (j : ℕ) : (∑' n, F n j) = α j * generalBaileyGamma u v δ j := by
    rw [generalBaileyGamma, ← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : j ≤ n <;> simp [F, hn]
    ring
  have hcomm := (show Summable (Function.uncurry F) from hF).tsum_comm
  calc (∑' j : ℕ, α j * generalBaileyGamma u v δ j)
      = ∑' j, ∑' n, F n j := tsum_congr fun j => (hcol j).symm
    _ = ∑' n, ∑' j, F n j := hcomm
    _ = ∑' n, generalBaileyBeta u v α n * δ n := tsum_congr hrow

/-- DLMF17.12: an infinite chain is obtained by successive applications of17.12.5.
The transform parameters may vary at each step. Every displayed quotient denominator,
including the denominators in the Bailey-pair relation, is required to be nonzero. -/
@[dlmf 17.12]
def IsBaileyChain (a q : ℂ) (α β : ℕ → ℕ → ℂ) : Prop :=
  (∀ k : ℕ, DLMF.Bailey.IsBaileyPair a q (α k) (β k)) ∧
  (∀ n : ℕ, DLMF.QSeries.qPochhammer q q n ≠ 0) ∧
  (∀ n : ℕ, DLMF.QSeries.qPochhammer (a*q) q n ≠ 0) ∧
  ∃ ρ1 ρ2 : ℕ → ℂ, ∀ k : ℕ,
    ρ1 k ≠ 0 ∧ ρ2 k ≠ 0 ∧
    (∀ n : ℕ, DLMF.QSeries.qPochhammer (a*q/ρ1 k) q n ≠ 0) ∧
    (∀ n : ℕ, DLMF.QSeries.qPochhammer (a*q/ρ2 k) q n ≠ 0) ∧
    (∀ n : ℕ,
      DLMF.QSeries.qPochhammer (a*q/ρ1 k) q n *
        DLMF.QSeries.qPochhammer (a*q/ρ2 k) q n * α (k+1) n =
      DLMF.QSeries.qPochhammer (ρ1 k) q n *
        DLMF.QSeries.qPochhammer (ρ2 k) q n *
        (a*q/(ρ1 k*ρ2 k))^n * α k n) ∧
    (∀ n : ℕ,
      DLMF.QSeries.qPochhammer (a*q/ρ1 k) q n *
        DLMF.QSeries.qPochhammer (a*q/ρ2 k) q n * β (k+1) n =
      ∑ j ∈ Finset.range (n+1),
        DLMF.QSeries.qPochhammer (ρ1 k) q j *
          DLMF.QSeries.qPochhammer (ρ2 k) q j *
          DLMF.QSeries.qPochhammer (a*q/(ρ1 k*ρ2 k)) q (n-j) *
          (a*q/(ρ1 k*ρ2 k))^j * β k j /
            DLMF.QSeries.qPochhammer q q (n-j))

/-- A convergent sequence of complex numbers is bounded in norm. -/
private lemma qbR4_exists_norm_le_of_tendsto {u : ℕ → ℂ} {L : ℂ} (hu : Tendsto u atTop (𝓝 L)) :
    ∃ C, ∀ n, ‖u n‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

/-- Tannery's theorem for the finite sums of the Bailey relation (as in `DLMF.Bailey`). -/
private lemma qbR4_tendsto_sum_range_mul {u : ℕ → ℂ} {v : ℕ → ℕ → ℂ} {L : ℂ} {C : ℝ}
    (hu : Summable fun k => ‖u k‖) (hv : ∀ k, Tendsto (fun N => v N k) atTop (𝓝 L))
    (hC : ∀ N k, ‖v N k‖ ≤ C) :
    Tendsto (fun N => ∑ k ∈ range (N + 1), u k * v N k) atTop (𝓝 ((∑' k, u k) * L)) := by
  have heq : ∀ N, ∑ k ∈ range (N + 1), u k * v N k =
      ∑' k, (if k ≤ N then u k * v N k else 0) := by
    intro N
    rw [tsum_eq_sum (s := range (N + 1))]
    · exact sum_congr rfl fun k hk => by
        simp [show k ≤ N by simpa [Nat.lt_succ_iff] using hk]
    · intro k hk
      simp [show ¬k ≤ N by simpa [Nat.lt_succ_iff] using hk]
  simp only [heq]
  rw [← tsum_mul_right]
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => ‖u k‖ * C) (hu.mul_right C)
    (fun k => ?_) (Eventually.of_forall fun N k => ?_)
  · refine ((hv k).const_mul (u k)).congr' ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    simp [hN]
  · split_ifs
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC N k) (norm_nonneg _)
    · simpa using mul_nonneg (norm_nonneg (u k)) ((norm_nonneg _).trans (hC 0 0))

/-- The infinite limiting form of Bailey's lemma. -/
@[dlmf 17.12.E4]
theorem limitingBaileyTransform {a q : ℂ} {α β : ℕ → ℂ}
    (hq : ‖q‖ < 1) (hpair : DLMF.Bailey.IsBaileyPair a q α β)
    (hden : ∀ n : ℕ, DLMF.QSeries.qPochhammer (a * q) q n ≠ 0)
    (hα : Summable (fun n : ℕ => q ^ (n * n) * a ^ n * α n))
    (hβ : Summable (fun n : ℕ => q ^ (n * n) * a ^ n * β n)) :
    (∑' n : ℕ, q ^ (n * n) * a ^ n * β n) =
      (∑' n : ℕ, q ^ (n * n) * a ^ n * α n) /
        DLMF.QSeries.qPochhammerInf (a * q) q := by
  have hqq : ∀ m, qPochhammer q q m ≠ 0 := qPochhammer_self_ne_zero hq
  have hQ : qPochhammerInf q q ≠ 0 := qPochhammerInf_ne_zero hq fun n => by
    simpa [pow_succ'] using qPochhammerInf_pow_succ_ne_zero hq n
  have hA : qPochhammerInf (a * q) q ≠ 0 := by
    refine qPochhammerInf_ne_zero hq fun n h0 => hden (n + 1) ?_
    rw [qPochhammer_succ, h0, mul_zero]
  have rel : ∀ N, ∑ k ∈ range (N + 1), (q ^ (k * k) * a ^ k * β k) * (qPochhammer q q (N - k))⁻¹ =
      ∑ k ∈ range (N + 1), (q ^ (k * k) * a ^ k * α k) *
        (qPochhammer q q (N - k) * qPochhammer (a * q) q (N + k))⁻¹ := by
    intro N
    have h := DLMF.Bailey.bailey_limit_relation (α := α) (β := β) (n := N)
      (fun k _ => hpair k) (fun m _ => hqq m) (hden _)
    simp only [div_eq_mul_inv] at h
    convert h using 2 <;> ring
  have tq := tendsto_qPochhammer (w := q) hq
  have taq := tendsto_qPochhammer (w := a * q) hq
  obtain ⟨Cq, hCq⟩ := qbR4_exists_norm_le_of_tendsto (tq.inv₀ hQ)
  obtain ⟨Ca, hCa⟩ := qbR4_exists_norm_le_of_tendsto (taq.inv₀ hA)
  have hCq0 : 0 ≤ Cq := (norm_nonneg _).trans (hCq 0)
  have limL := qbR4_tendsto_sum_range_mul (u := fun k => q ^ (k * k) * a ^ k * β k)
    (v := fun N k => (qPochhammer q q (N - k))⁻¹) (L := (qPochhammerInf q q)⁻¹)
    (summable_norm_iff.mpr hβ)
    (fun k => ((tq.comp (tendsto_sub_atTop_nat k)).inv₀ hQ)) (fun N k => hCq _)
  have limR := qbR4_tendsto_sum_range_mul (u := fun k => q ^ (k * k) * a ^ k * α k)
    (v := fun N k => (qPochhammer q q (N - k) * qPochhammer (a * q) q (N + k))⁻¹)
    (L := (qPochhammerInf q q * qPochhammerInf (a * q) q)⁻¹) (summable_norm_iff.mpr hα)
    (fun k => ((tq.comp (tendsto_sub_atTop_nat k)).mul
      (taq.comp (tendsto_add_atTop_nat k))).inv₀ (mul_ne_zero hQ hA))
    (fun N k => by
      rw [mul_inv, norm_mul]
      exact mul_le_mul (hCq _) (hCa _) (norm_nonneg _) hCq0)
  simp only [rel] at limL
  have heq := tendsto_nhds_unique limL limR
  rw [mul_inv] at heq
  field_simp at heq ⊢
  linear_combination heq

/-- The explicit numerator sequence of the Rogers–Ramanujan Bailey pair. -/
@[dlmf 17.12.E6]
def rogersBaileyAlpha (a q : ℂ) (n : ℕ) : ℂ :=
  DLMF.QSeries.qPochhammer a q n * (1 - a * q ^ (2 * n)) * (-1) ^ n *
    q ^ (n * n + n.choose 2) * a ^ n /
      (DLMF.QSeries.qPochhammer q q n * (1 - a))

/-- The explicit denominator sequence of the Rogers–Ramanujan Bailey pair. -/
@[dlmf 17.12.E6]
def rogersBaileyBeta (q : ℂ) (n : ℕ) : ℂ :=
  (DLMF.QSeries.qPochhammer q q n)⁻¹

/-- The displayed sequences form a Bailey pair wherever their quotients are finite.
The removable specialization `a=1` is deliberately not identified with `0/0`. -/
@[dlmf 17.12.E6]
theorem rogersBaileyPair {a q : ℂ} (ha : a ≠ 1)
    (hqq : ∀ n : ℕ, DLMF.QSeries.qPochhammer q q n ≠ 0)
    (haq : ∀ n : ℕ, DLMF.QSeries.qPochhammer (a * q) q n ≠ 0) :
    DLMF.Bailey.IsBaileyPair a q (rogersBaileyAlpha a q) (rogersBaileyBeta q) := by
  intro n
  have h := DLMF.Bailey.bailey_limit_relation (a := a) (q := q) (n := n)
    (α := DLMF.Bailey.unitAlpha a q) (β := fun k => if k = 0 then 1 else 0)
    (fun k _ => DLMF.Bailey.unit_pair a q k (fun m _ => hqq m) (haq _))
    (fun m _ => hqq m) (haq _)
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (by simp)] at h
  simp only [pow_zero, mul_one, ↓reduceIte, Nat.sub_zero, mul_zero, one_div] at h
  rw [rogersBaileyBeta, h]
  refine sum_congr rfl fun k _ => ?_
  have h1a : (1 - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hD := DLMF.Bailey.qPochhammer_mul_one_sub_pow a q k
  rw [rogersBaileyAlpha, DLMF.Bailey.unitAlpha]
  have e : qPochhammer a q k * (1 - a * q ^ (2 * k)) / (1 - a) = DLMF.Bailey.unitD a q k := by
    rw [hD]; field_simp
  rw [← e, pow_add]
  field_simp

end DLMF.QHypergeometric
