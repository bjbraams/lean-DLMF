/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import Carlson.R.BinomialSeries

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
  set c := ∑ j, b j with hc_def
  have hzre : ∀ j, 0 < (z j).re := fun j => by
    have hr := (abs_re_le_norm (1 - z j)).trans_lt (hz j)
    simp only [sub_re, one_re] at hr
    linarith [le_abs_self (1 - (z j).re)]
  have hzs : z ∈ Carlson.carlsonRSlitDomain := fun j => mem_slitPlane_iff.mpr (Or.inl (hzre j))
  rw [symEllIntR_of_mem _ _ hzs]
  have H := (Carlson.hasSum_regCarlsonR_cpow_neg a b (z := z)
    (fun i => by rw [norm_sub_rev]; exact hz i)).mul_left (Gamma c)
  unfold Carlson.carlsonR
  convert H using 1
  funext N
  rw [Carlson.regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
    Carlson.carlsonRPolynomialNumerator_eq_sum_piAntidiag]
  have hcN : ∀ k : ℕ, c ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp at this
    linarith [hc, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hG0 : Gamma c ≠ 0 := Complex.Gamma_ne_zero hcN
  have hGN : Gamma (c + N) ≠ 0 := Complex.Gamma_ne_zero fun k h => by
    have := congrArg Complex.re h
    simp at this
    linarith [hc, (Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hG : Gamma (c + N) = Gamma c * (ascPochhammer ℂ N).eval c := by
    rw [← Complex.Gamma_add_nat_div_Gamma_eq c hcN]; field_simp
  have hP : (ascPochhammer ℂ N).eval c ≠ 0 := by
    intro h; rw [h, mul_zero] at hG; exact hGN hG
  have hNum : Carlson.carlsonGeneratingCoeff Finset.univ b (fun i => 1 - z i) N =
      (N.factorial : ℂ) * symEllIntT N b (fun j => 1 - z j) := by
    unfold Carlson.carlsonGeneratingCoeff symEllIntT
    rw [Finset.mul_sum]
    refine Finset.sum_congr ?_ fun m hm => ?_
    · ext m; simp [Finset.mem_piAntidiag, Finset.Nat.mem_antidiagonalTuple]
    have hsum : ∑ i, m i = N := Finset.Nat.mem_antidiagonalTuple.mp hm
    have hspec := Nat.multinomial_spec Finset.univ m
    rw [hsum] at hspec
    have hspec' : (∏ i, ((m i).factorial : ℂ)) * (Nat.multinomial Finset.univ m : ℂ) =
        (N.factorial : ℂ) := by exact_mod_cast hspec
    have hF : (∏ i, ((m i).factorial : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (m i).factorial_ne_zero
    rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, ← hspec']
    field_simp
  rw [hNum, hG]
  have hNf : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  field_simp

/-- Complex homogeneity of `R_{-a}(𝐛; 𝐳)` (helper; any complex `a, 𝐛`): for slit-plane nodes and
a slit-plane scale `μ` with `arg μ + arg zᵢ ∈ (-π, π)`, `R_{-a}(𝐛; μ𝐳) = μ^{-a} R_{-a}(𝐛; 𝐳)`. -/
lemma p19sR1_symEllIntR_mul {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {μ : ℂ} {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (hμ : μ ∈ slitPlane)
    (harg : ∀ i, arg μ + arg (z i) ∈ Ioo (-Real.pi) Real.pi) :
    symEllIntR a b (fun i => μ * z i) = μ ^ (-a) * symEllIntR a b z := by
  have hmz : (fun i => μ * z i) ∈ Carlson.carlsonRSlitDomain := fun i => by
    have hμ' := hμ
    have hw := hz i
    rw [mem_slitPlane_iff_arg] at hμ' hw ⊢
    rw [arg_mul hμ'.2 hw.2 ⟨(harg i).1, (harg i).2.le⟩]
    exact ⟨(harg i).2.ne, mul_ne_zero hμ'.2 hw.2⟩
  rw [symEllIntR_of_mem _ _ hmz, symEllIntR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  rw [Carlson.regCarlsonR_mul_of_arg_add (-a) b hz hμ harg]
  ring

/-- Complex homogeneity on the right half-plane (helper): `R_{-a}(𝐛; μ𝐳) = μ^{-a} R_{-a}(𝐛; 𝐳)`
for `ℜ μ > 0` and `ℜ zᵢ > 0`. -/
lemma p19sR1_symEllIntR_mul_of_re_pos {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {μ : ℂ}
    {z : ι → ℂ} (hz : ∀ i, 0 < (z i).re) (hμ : 0 < μ.re) :
    symEllIntR a b (fun i => μ * z i) = μ ^ (-a) * symEllIntR a b z := by
  refine p19sR1_symEllIntR_mul a b (fun i => mem_slitPlane_iff.mpr (Or.inl (hz i)))
    (mem_slitPlane_iff.mpr (Or.inl hμ)) fun i => ?_
  have hm := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hμ))
  have hi := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hz i)))
  constructor <;> linarith [Real.pi_pos]

/-- Helper for 19.19.3: `T_N` with vanishing last variable drops that variable. -/
lemma p19sR1_symEllIntT_last_zero {n : ℕ} (N : ℕ) (b v : Fin (n + 1) → ℂ)
    (hv : v (Fin.last n) = 0) :
    symEllIntT N b v = symEllIntT N (fun j : Fin n => b j.castSucc) (fun j => v j.castSucc) := by
  unfold symEllIntT
  set F : (Fin (n + 1) → ℕ) → ℂ := fun m =>
    ∏ j, (ascPochhammer ℂ (m j)).eval (b j) / ((m j).factorial : ℂ) * v j ^ (m j) with hF_def
  have hF : ∀ m' : Fin n → ℕ, F (Fin.snoc m' 0) = ∏ j : Fin n,
      (ascPochhammer ℂ (m' j)).eval (b j.castSucc) / ((m' j).factorial : ℂ) *
        v j.castSucc ^ (m' j) := by
    intro m'
    simp only [F]
    rw [Fin.prod_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  let e : (Fin n → ℕ) ↪ (Fin (n + 1) → ℕ) := ⟨fun m' => Fin.snoc m' 0, fun x y h => by
    funext j
    have := congrFun h j.castSucc
    simpa using this⟩
  symm
  calc _ = ∑ m' ∈ Finset.Nat.antidiagonalTuple n N, F (e m') :=
        Finset.sum_congr rfl fun m' _ => (hF m').symm
    _ = ∑ m ∈ (Finset.Nat.antidiagonalTuple n N).map e, F m := (Finset.sum_map _ _ _).symm
    _ = ∑ m ∈ Finset.Nat.antidiagonalTuple (n + 1) N, F m := by
      refine Finset.sum_subset (fun m hm => ?_) (fun m hm hnot => ?_)
      · obtain ⟨m', hm', rfl⟩ := Finset.mem_map.mp hm
        rw [Finset.Nat.mem_antidiagonalTuple] at hm' ⊢
        rw [Fin.sum_univ_castSucc]
        change ∑ x : Fin n, (Fin.snoc m' 0 : Fin (n + 1) → ℕ) x.castSucc +
          (Fin.snoc m' 0 : Fin (n + 1) → ℕ) (Fin.last n) = N
        simpa using hm'
      · by_cases h0 : m (Fin.last n) = 0
        · exfalso
          apply hnot
          refine Finset.mem_map.mpr ⟨Fin.init m, ?_, ?_⟩
          · rw [Finset.Nat.mem_antidiagonalTuple] at hm ⊢
            rw [Fin.sum_univ_castSucc, h0, add_zero] at hm
            exact hm
          · simp only [e]
            rw [← h0]
            exact Fin.snoc_init_self m
        · refine Finset.prod_eq_zero (Finset.mem_univ (Fin.last n)) ?_
          rw [hv, zero_pow h0, mul_zero]

/-- DLMF 19.19.3: `R_{-a}(𝐛; 𝐳) = zₙ^{-a} ∑_N (a)_N/(c)_N T_N(b₁, …, bₙ₋₁; 1 - z₁/zₙ, …)`,
`c = ∑ bⱼ` (all `n` parameters), `|1 - zⱼ/zₙ| < 1`, with `zₙ ∈ ℂ \ (-∞, 0]`; `0 < re c`.
**Corrected from the printed DLMF formula**: we also assume `ph zₙ + ph(zⱼ/zₙ) ∈ (-π, π)`, the
condition of the homogeneity relation 19.16.11 from which DLMF derives (19.19.3). Without it the
formula fails: `n = 2`, `a = 0.3`, `𝐛 = (0.5, 0.7)`, `z₁ = e^{-0.8πi}`, `z₂ = e^{0.9πi}` gives
`R = 1.8216 - 0.4034i` (19.16.9) against `0.5763 - 0.8336i` (mpmath, 2026-10-25). -/
@[dlmf 19.19.E3]
theorem symEllIntR_hasSum_T_last {n : ℕ} (a : ℂ) (b : Fin (n + 1) → ℂ) (z : Fin (n + 1) → ℂ)
    (hc : 0 < (∑ j, b j).re) (hzn : z (Fin.last n) ∈ slitPlane)
    (hz : ∀ j : Fin n, ‖1 - z j.castSucc / z (Fin.last n)‖ < 1)
    (harg : ∀ j : Fin n,
      arg (z (Fin.last n)) + arg (z j.castSucc / z (Fin.last n)) ∈ Set.Ioo (-π) π) :
    HasSum (fun N => z (Fin.last n) ^ (-a) * ((ascPochhammer ℂ N).eval a /
      (ascPochhammer ℂ N).eval (∑ j, b j) *
        symEllIntT N (fun j : Fin n => b j.castSucc)
          (fun j => 1 - z j.castSucc / z (Fin.last n)))) (symEllIntR a b z) := by
  set μ := z (Fin.last n) with hμ_def
  have hμ0 : μ ≠ 0 := slitPlane_ne_zero hzn
  set w : Fin (n + 1) → ℂ := fun i => z i / μ with hw_def
  have hwl : w (Fin.last n) = 1 := by simp only [w, ← hμ_def]; exact div_self hμ0
  have hw1 : ∀ i, ‖1 - w i‖ < 1 := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [hwl]; simp
    | cast j => exact hz j
  have hwre : ∀ i, 0 < (w i).re := fun i => by
    have hr := (abs_re_le_norm (1 - w i)).trans_lt (hw1 i)
    simp only [sub_re, one_re] at hr
    linarith [le_abs_self (1 - (w i).re)]
  have hws : w ∈ Carlson.carlsonRSlitDomain := fun i => mem_slitPlane_iff.mpr (Or.inl (hwre i))
  have harg' : ∀ i, arg μ + arg (w i) ∈ Set.Ioo (-π) π := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [hwl, arg_one, add_zero]
      exact ⟨neg_pi_lt_arg μ, lt_of_le_of_ne (arg_le_pi μ) (mem_slitPlane_iff_arg.mp hzn).1⟩
    | cast j => exact harg j
  have hzw : symEllIntR a b z = symEllIntR a b (fun i => μ * w i) := by
    congr 1; funext i; simp only [w]; field_simp
  rw [hzw, p19sR1_symEllIntR_mul a b hws hzn harg']
  have H := (symEllIntR_hasSum_T a b w hc hw1).mul_left (μ ^ (-a))
  convert H using 2 with N
  rw [p19sR1_symEllIntT_last_zero N b (fun j => 1 - w j) (by simp only [hwl]; ring)]

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
