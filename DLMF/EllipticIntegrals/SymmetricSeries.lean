/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Symmetric elliptic integrals: Taylor and related series (DLMF §19.19)

The homogeneous hypergeometric polynomial `T_N(𝐛, 𝐳)` (19.19.1), the multivariate
hypergeometric series (19.19.2), (19.19.3) of `R_{-a}(𝐛; 𝐳)`, the elementary symmetric functions
`E_s(𝐳)` (19.19.4, Mathlib's `Multiset.esymm`), the form (19.19.5) of `T_N(½, 𝐳)`, `R_J` as an
`R`-function with five equal parameters (19.19.6), and the expansion (19.19.7)–(19.19.8) about the
mean `A`.

Series are stated with `HasSum` (absolute convergence holds in the stated discs). Pochhammer
symbols are `(ascPochhammer ℂ N).eval a`; DLMF's `(c)_N` in a denominator is assumed nonzero
through `0 < re c`.

## Prose
* 19.19.p3: for `n = 2`, (19.19.3) is a Gauss series (see (19.25.43), (15.2.1)); commentary.
* 19.19.p5: the remark on the number of terms of `T_N(½, 𝐙)` when `E₁(𝐙) = 0` (at most one term
  for `N ≤ 5` for `R_F`, …) is a computational remark, not formalized.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- DLMF 19.19.1: the homogeneous hypergeometric polynomial
`T_N(𝐛, 𝐳) = ∑_{m₁+⋯+mₙ = N} ∏ⱼ (bⱼ)_{mⱼ} zⱼ^{mⱼ} / mⱼ!`. -/
@[dlmf 19.19.E1]
def symEllIntT (N : ℕ) {n : ℕ} (b z : Fin n → ℂ) : ℂ :=
  ∑ m ∈ Finset.Nat.antidiagonalTuple n N,
    ∏ j, (ascPochhammer ℂ (m j)).eval (b j) / ((m j).factorial : ℂ) * z j ^ (m j)

/-- DLMF 19.19.4: the elementary symmetric function `E_s(𝐳)` (Mathlib's `Multiset.esymm`). -/
def symEllIntE {n : ℕ} (s : ℕ) (z : Fin n → ℂ) : ℂ :=
  (Finset.univ.val.map z).esymm s

/-- DLMF 19.19.4: `∏ⱼ (1 + t zⱼ) = ∑_{s=0}^n t^s E_s(𝐳)`. -/
@[dlmf 19.19.E4]
theorem prod_one_add_mul_eq_sum_symEllIntE {n : ℕ} (z : Fin n → ℂ) (t : ℂ) :
    ∏ j, (1 + t * z j) = ∑ s ∈ Finset.range (n + 1), t ^ s * symEllIntE s z := by
  rw [Finset.prod_one_add, ← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
    (t := Finset.range (n + 1)) (fun u _ => by
      simpa [Nat.lt_succ_iff] using (Finset.card_le_univ u).trans_eq (Fintype.card_fin n))]
  simp_rw [symEllIntE, Finset.esymm_map_val, Finset.mul_sum, ← Finset.powersetCard_eq_filter]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hu).2]

/-- DLMF 19.19.2: `R_{-a}(𝐛; 𝐳) = ∑_{N≥0} (a)_N/(c)_N T_N(𝐛, 𝟏 - 𝐳)`, `c = ∑ bⱼ`, `|1 - zⱼ| < 1`.
We assume `0 < re c` (DLMF: real `bⱼ`, and the ratio needs `(c)_N ≠ 0`). -/
@[dlmf 19.19.E2]
theorem symEllIntR_hasSum_T {n : ℕ} (a : ℂ) (b z : Fin n → ℂ) (hc : 0 < (∑ j, b j).re)
    (hz : ∀ j, ‖1 - z j‖ < 1) :
    HasSum (fun N => (ascPochhammer ℂ N).eval a / (ascPochhammer ℂ N).eval (∑ j, b j) *
      symEllIntT N b (fun j => 1 - z j)) (symEllIntR a b z) := by
  sorry

/-- DLMF 19.19.3: `R_{-a}(𝐛; 𝐳) = zₙ^{-a} ∑_N (a)_N/(c)_N T_N(b₁, …, bₙ₋₁; 1 - z₁/zₙ, …)`,
`c = ∑ bⱼ` (all `n` parameters), `|1 - zⱼ/zₙ| < 1`, with `zₙ ∈ ℂ \ (-∞, 0]`; `0 < re c`. -/
@[dlmf 19.19.E3]
theorem symEllIntR_hasSum_T_last {n : ℕ} (a : ℂ) (b : Fin (n + 1) → ℂ) (z : Fin (n + 1) → ℂ)
    (hc : 0 < (∑ j, b j).re) (hzn : z (Fin.last n) ∈ slitPlane)
    (hz : ∀ j : Fin n, ‖1 - z j.castSucc / z (Fin.last n)‖ < 1) :
    HasSum (fun N => z (Fin.last n) ^ (-a) * ((ascPochhammer ℂ N).eval a /
      (ascPochhammer ℂ N).eval (∑ j, b j) *
        symEllIntT N (fun j : Fin n => b j.castSucc)
          (fun j => 1 - z j.castSucc / z (Fin.last n)))) (symEllIntR a b z) := by
  sorry

/-- DLMF 19.19.5: `T_N(½, 𝐳) = ∑ (-1)^{M+N} (½)_M E₁^{m₁}⋯Eₙ^{mₙ} / (m₁!⋯mₙ!)`, over
`m₁, …, mₙ ≥ 0` with `∑ j mⱼ = N`, `M = ∑ mⱼ` (here `mⱼ` is indexed by `j - 1 : Fin n`). -/
@[dlmf 19.19.E5]
theorem symEllIntT_half {n : ℕ} (N : ℕ) (z : Fin n → ℂ) :
    symEllIntT N (fun _ => 1 / 2) z =
      ∑ m ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (N + 1)).filter
          (fun m => ∑ j : Fin n, ((j : ℕ) + 1) * m j = N),
        (-1 : ℂ) ^ ((∑ j : Fin n, m j) + N) * (ascPochhammer ℂ (∑ j : Fin n, m j)).eval (1 / 2) *
          ∏ j : Fin n, symEllIntE ((j : ℕ) + 1) z ^ (m j) / ((m j).factorial : ℂ) := by
  sorry

/-- DLMF 19.19.6: `R_J(x, y, z, p) = R_{-3/2}(½, ½, ½, ½, ½; x, y, z, p, p)` (slit-plane
variables). Proved by comparing the integrals (19.16.9). -/
@[dlmf 19.19.E6]
theorem symEllIntRJ_eq_symEllIntR_five {x y z p : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    symEllIntRJ x y z p = symEllIntR (3 / 2) (fun _ : Fin 5 => 1 / 2) ![x, y, z, p, p] := by
  have h5 : (![x, y, z, p, p] : Fin 5 → ℂ) ∈ Carlson.carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  rw [symEllIntRJ_eq_symEllIntR hx hy hz hp,
    symEllIntR_eq_integral (a' := 1) (by norm_num) (by norm_num)
      (by simp [Fin.sum_univ_four]; norm_num) (ei19c_slit4 hx hy hz hp),
    symEllIntR_eq_integral (a' := 1) (by norm_num) (by norm_num)
      (by simp; norm_num) h5]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hpt : (t : ℂ) + p ≠ 0 := ei19c_add_ne_zero ht (Or.inl hp)
  simp only [Fin.prod_univ_four, Fin.prod_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, cpow_neg_one]
  have : ((t : ℂ) + p) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p) ^ (-(1 / 2) : ℂ) = ((t : ℂ) + p)⁻¹ := by
    rw [← cpow_add _ _ hpt]; norm_num; exact cpow_neg_one _
  rw [← this]; ring

/-- DLMF 19.19.7 with 19.19.8: with `A = (1/n) ∑ zⱼ`, `Zⱼ = 1 - zⱼ/A` (so `E₁(𝐙) = 0`),
`|Zⱼ| < 1`, `R_{-a}(½; 𝐳) = A^{-a} ∑_N (a)_N/(n/2)_N T_N(½, 𝐙)`; `n ≥ 1`, `A ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.19.E7, dlmf 19.19.E8]
theorem symEllIntR_half_hasSum_mean {n : ℕ} (hn : 0 < n) (a : ℂ) (z : Fin n → ℂ)
    (hA : (1 / n : ℂ) * ∑ j, z j ∈ slitPlane)
    (hZ : ∀ j, ‖1 - z j / ((1 / n : ℂ) * ∑ i, z i)‖ < 1) :
    HasSum (fun N => ((1 / n : ℂ) * ∑ j, z j) ^ (-a) * ((ascPochhammer ℂ N).eval a /
      (ascPochhammer ℂ N).eval ((n : ℂ) / 2) *
        symEllIntT N (fun _ => 1 / 2) (fun j => 1 - z j / ((1 / n : ℂ) * ∑ i, z i))))
      (symEllIntR a (fun _ => 1 / 2) z) := by
  sorry

/-- DLMF 19.19.8: `E₁(𝐙) = 0` for `Zⱼ = 1 - zⱼ/A`, `A = (1/n)∑ zⱼ ≠ 0`. -/
@[dlmf 19.19.E8]
theorem symEllIntE_one_mean {n : ℕ} (z : Fin n → ℂ) (hA : (1 / n : ℂ) * ∑ j, z j ≠ 0) :
    symEllIntE 1 (fun j => 1 - z j / ((1 / n : ℂ) * ∑ i, z i)) = 0 := by
  rw [symEllIntE, Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id']
  rw [← Finset.sum_eq_multiset_sum (Finset.univ) fun j => 1 - z j / ((1 / n : ℂ) * ∑ i, z i)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hn : (n : ℂ) ≠ 0 := by rintro h; simp [h] at hA
  have hs : ∑ i, z i ≠ 0 := by rintro h; simp [h] at hA
  field_simp
  simp

end DLMF.EllipticIntegrals
