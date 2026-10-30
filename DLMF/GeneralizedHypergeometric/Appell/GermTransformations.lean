/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Appell.EulerIntegrals
public import Carlson.TwoVariable.AppellF1
public import Carlson.R.Homogeneity
public import Carlson.Elliptic.ReductionRelations
public import Carlson.TwoVariable.RPolynomial.Hypergeometric

/-!
# Germ transformations and reductions of Appell functions

The F1 transformation follows from the three-node Carlson representation, principal
complex homogeneity and permutation of nodes. Its Gauss specialization also reduces F3.
For F2, grouping F1 by total degree and using Carlson's polynomial representation of a
terminating Gauss function identifies the two convergent series after Euler's transformation.

The Carlson representations, homogeneity, permutation and polynomial identities are imported
from lean-codes. The Gauss Euler transformation and Appell fiber sums are reused locally.
-/

@[expose] public noncomputable section

open Complex Filter Set Carlson Carlson.TwoVariable Polynomial
open scoped Nat Topology

namespace DLMF.Hypergeometric

/-- The project and lean-codes ordinary normalizations of F1 agree on the unit bidisc. -/
lemma appF1_eq_appellF1 (a b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    appF1 a b b' c x y = Complex.appellF1 a b b' c x y := by
  have hs := Complex.hasSum_appellF1 (a := a) (b₁ := b) (b₂ := b') hc hx hy
  apply (hasSum_appF1 a b b' c hc ⟨hx, hy⟩).unique
  refine hs.congr_fun fun p => ?_
  rcases p with ⟨m, n⟩
  simp only [appF1Coeff, poch]
  ring
/-- F1 is the Gamma-normalized three-node Carlson average on the unit bidisc. -/
lemma appF1_eq_gamma_mul_regCarlsonR (a b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    appF1 a b b' c x y = Gamma c * regCarlsonR (-a)
      (appellDirichletParameters b b' c) (appellCarlsonNodes x y) := by
  rw [appF1_eq_appellF1 a b b' c hc hx hy, Complex.appellF1,
    regCarlsonR_eq_regularizedAppellF1 a b b' c hx hy]

/-- Nodes of the Appell representation lie in the right half-plane on the unit bidisc. -/
private lemma appell_nodes_mem_variableDomain {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    appellCarlsonNodes x y ∈ carlsonRVariableDomain := by
  intro i
  cases i with
  | inl i =>
    fin_cases i
    · change 0 < (1 - x).re
      simp only [sub_re, one_re]
      linarith [re_le_norm x]
    · change 0 < (1 - y).re
      simp only [sub_re, one_re]
      linarith [re_le_norm y]
  | inr i => change 0 < (1 : ℂ).re; norm_num

/-- Scaling and permuting the three Carlson nodes gives F1's second Pfaff identity
whenever both Appell series converge in the unit bidisc. -/
private lemma appF1_pfaff_second_of_norm_lt_one (a b b' c : ℂ) (hc : AppellRegular c)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hX : ‖x / (x - 1)‖ < 1) (hY : ‖(y - x) / (1 - x)‖ < 1) :
    appF1 a b b' c x y = (1 - x) ^ (-a) * appF1 a (c - b - b') b' c
      (x / (x - 1)) ((y - x) / (1 - x)) := by
  rw [appF1_eq_gamma_mul_regCarlsonR a b b' c hc hx hy,
    appF1_eq_gamma_mul_regCarlsonR a (c - b - b') b' c hc hX hY]
  let e : (Fin 2 ⊕ Unit) ≃ (Fin 2 ⊕ Unit) := Equiv.swap (Sum.inl 0) (Sum.inr ())
  have hxre : 0 < (1 - x).re := by
    simp only [sub_re, one_re]
    linarith [re_le_norm x]
  have hx0 : 1 - x ≠ 0 := slitPlane_ne_zero (Or.inl hxre)
  have hx1 : x - 1 ≠ 0 := by intro h; apply hx0; linear_combination -h
  have hz := carlsonRVariableDomain_subset_slitDomain (appell_nodes_mem_variableDomain hx hy)
  have hzt := appell_nodes_mem_variableDomain hX hY
  have hnodes : (fun i => (1 - x) * appellCarlsonNodes (x / (x - 1)) ((y - x) / (1 - x)) i) =
      appellCarlsonNodes x y ∘ e := by
    funext i
    cases i with
    | inl i => fin_cases i <;> simp [e, Equiv.swap_apply_def, appellCarlsonNodes, pair] <;>
        field_simp [hx0, hx1] <;> ring
    | inr i => simp [e, appellCarlsonNodes, pair]
  have hparams : appellDirichletParameters (c - b - b') b' c ∘ e.symm =
      appellDirichletParameters b b' c := by
    funext i
    cases i with
    | inl i => fin_cases i <;> simp [e, Equiv.swap_apply_def, appellDirichletParameters, pair]; ring
    | inr i => simp [e, appellDirichletParameters, pair]
  have h := regCarlsonR_mul_of_re_pos (-a)
    (appellDirichletParameters (c - b - b') b' c) hzt hxre
  rw [hnodes, regCarlsonR_comp_equiv e (-a) hz, hparams] at h
  rw [h]
  ring

/-- A fractional linear change in both variables gives F1's second Pfaff transformation
as principal analytic germs at the origin. -/
@[dlmf 16.16.E8]
theorem appF1_pfaff_second (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF1 a b b' c x y) =ᶠ[𝓝 (0, 0)]
      (fun p => let x:=p.1; let y:=p.2; (1 - x) ^ (-a) * appF1 a (c - b - b') b' c (x / (x - 1)) ((y
          - x) / (1 - x))) := by
  let T : ℂ × ℂ → ℂ × ℂ := fun p => (p.1 / (p.1 - 1), (p.2 - p.1) / (1 - p.1))
  have hT : ContinuousAt T (0, 0) := by
    dsimp [T]
    exact (continuous_fst.continuousAt.div
      (continuous_fst.continuousAt.sub continuousAt_const) (by norm_num)).prodMk
      ((continuous_snd.continuousAt.sub continuous_fst.continuousAt).div
        (continuousAt_const.sub continuous_fst.continuousAt) (by norm_num))
  have hT0 : T (0, 0) = (0, 0) := by simp [T]
  have hU : {p : ℂ × ℂ | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1} ∈ 𝓝 (0, 0) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds (by simp)
  have hUT := hT.preimage_mem_nhds (t := {p : ℂ × ℂ | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1})
    (by rw [hT0]; exact hU)
  filter_upwards [hU, hUT] with p hp ht
  rcases p with ⟨x, y⟩
  change ‖x / (x - 1)‖ < 1 ∧ ‖(y - x) / (1 - x)‖ < 1 at ht
  simp only at hp ⊢
  exact appF1_pfaff_second_of_norm_lt_one a b b' c hc hp.1 hp.2 ht.1 ht.2

/-- A vanishing second upper parameter leaves just a Gauss series in F1's second variable. -/
private lemma appF1_zero_upper_germ (a b c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => appF1 a 0 b c p.1 p.2) =ᶠ[𝓝 (0, 0)]
      (fun p => ₂F₁ a b c p.2) := by
  have hU : {p : ℂ × ℂ | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1} ∈ 𝓝 (0, 0) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  have hs := hasSum_appF1_gauss_fibers a 0 b c hc hp.1 hp.2
  rw [← hs.tsum_eq, tsum_eq_single 0]
  · simp [poch_zero]
  · intro m hm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simp

/-- When the lower parameter is the sum of the separate upper parameters, F1 reduces
to a Gauss function after a fractional linear change, as germs at the origin. -/
@[dlmf 16.16.E1]
theorem appF1_reduction_gauss (a b b' : ℂ) (hc : AppellRegular (b + b')) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF1 a b b' (b + b') x y) =ᶠ[𝓝 (0, 0)]
      (fun p => let x:=p.1; let y:=p.2; (1 - y) ^ (-a) * ₂F₁ a b (b + b') ((x - y) / (1 - y))) := by
  have hswap : Tendsto (fun p : ℂ × ℂ => (p.2, p.1)) (𝓝 (0, 0)) (𝓝 (0, 0)) :=
    (continuous_snd.continuousAt.prodMk continuous_fst.continuousAt).tendsto
  have hp := (appF1_pfaff_second a b' b (b + b') hc).comp_tendsto hswap
  let T : ℂ × ℂ → ℂ × ℂ := fun p => (p.2 / (p.2 - 1), (p.1 - p.2) / (1 - p.2))
  have hT : ContinuousAt T (0, 0) := by
    exact (continuous_snd.continuousAt.div
      (continuous_snd.continuousAt.sub continuousAt_const) (by norm_num)).prodMk
      ((continuous_fst.continuousAt.sub continuous_snd.continuousAt).div
        (continuousAt_const.sub continuous_snd.continuousAt) (by norm_num))
  have hT0 : T (0, 0) = (0, 0) := by simp [T]
  have hTT : Tendsto T (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    have h := hT.tendsto
    rw [hT0] at h
    exact h
  have hz := (appF1_zero_upper_germ a b (b + b') hc).comp_tendsto hTT
  filter_upwards [hp, hz] with p hp hz
  simp only [Function.comp_apply] at hp hz ⊢
  rw [show b + b' - b' - b = 0 by ring] at hp
  rw [← appF1_swap a b b' (b + b') p.1 p.2] at hp
  exact hp.trans (congrArg (fun z => (1 - p.2) ^ (-a) * z) hz)

/-- Complementary pairs of upper parameters reduce F3 to a Gauss function with
argument `x + y - x * y`, as principal germs at the origin. -/
@[dlmf 16.16.E5]
theorem appF3_reduction_gauss (a b c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF3 a (c - a) b (c - b) c x y) =ᶠ[𝓝 (0, 0)]
      (fun p => let x:=p.1; let y:=p.2; (1 - y) ^ (a + b - c) * ₂F₁ a b c (x + y - x * y)) := by
  have h1 := appF3_reduction_appF1 a b (c - b) c hc
  let T : ℂ → ℂ := fun y => y / (y - 1)
  have hT : ContinuousAt T 0 :=
    continuousAt_id.div (continuousAt_id.sub continuousAt_const) (by norm_num)
  have hT0 : T 0 = 0 := by simp [T]
  have hM : Tendsto (fun p : ℂ × ℂ => (p.1, T p.2)) (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    simpa only [Function.comp_apply, hT0] using continuous_fst.continuousAt.prodMk
      (hT.comp_of_eq (continuous_snd.continuousAt (x := ((0 : ℂ), (0 : ℂ)))) rfl) |>.tendsto
  have hbc : b + (c - b) = c := by ring
  have h2 := (appF1_reduction_gauss a b (c - b) (by rwa [hbc])).comp_tendsto hM
  have hU : {p : ℂ × ℂ | ‖p.2‖ < 1} ∈ 𝓝 (0, 0) :=
    (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).mem_nhds (by simp)
  filter_upwards [h1, h2, hU] with p h1 h2 hp
  obtain ⟨x, y⟩ := p
  simp only [Function.comp_apply, hbc] at h1 h2 ⊢
  have hyre : 0 < (1 - y).re := by
    simp only [sub_re, one_re]
    linarith [re_le_norm y]
  have hy0 : 1 - y ≠ 0 := slitPlane_ne_zero (Or.inl hyre)
  have hy1 : y - 1 ≠ 0 := by intro h; apply hy0; linear_combination -h
  have hinv : 1 - T y = (1 - y)⁻¹ := by dsimp [T]; field_simp [hy0, hy1]; ring
  have harg : (1 - y).arg ≠ Real.pi :=
    (arg_lt_pi_iff.mpr ((show 1 - y ∈ slitPlane from Or.inl hyre).imp_left le_of_lt)).ne
  have hvar : (x - T y) / (1 - T y) = x + y - x * y := by
    rw [hinv]
    dsimp [T]
    field_simp [hy0, hy1]
    ring
  rw [hvar, hinv, inv_cpow _ _ harg, ← cpow_neg, neg_neg] at h2
  rw [h1, h2, ← mul_assoc, ← cpow_add _ _ hy0]
  congr 2
  ring

/-- The total-degree coefficient of F1 is a two-node Carlson polynomial numerator. -/
private lemma appF1_totalDegree_eq (a b b' c x y : ℂ) (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n, appF1Coeff a b b' c p.1 p.2 * x ^ p.1 * y ^ p.2) =
      (poch a n / poch c n) * (carlsonRPolynomialNumerator₂ n b b' x y / n !) := by
  rw [← carlsonRPolynomialNumerator_pair, numerator_pair_div_factorial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := Finset.mem_antidiagonal.mp hp
  simp only [appF1Coeff, hdeg, poch, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Grouping F1 by total degree gives its convergent Carlson-polynomial expansion. -/
private lemma hasSum_appF1_totalDegree (a b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun n : ℕ => (poch a n / poch c n) *
      (carlsonRPolynomialNumerator₂ n b b' x y / n !)) (appF1 a b b' c x y) := by
  classical
  have hs := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr
    (hasSum_appF1 a b b' c hc ⟨hx, hy⟩)
  have h := hs.sigma (fun n => hasSum_fintype _)
  convert h using 1
  funext n
  change (poch a n / poch c n) * (carlsonRPolynomialNumerator₂ n b b' x y / n !) =
    ∑ p : ↥(Finset.antidiagonal n), appF1Coeff a b b' c p.val.1 p.val.2 * x ^ p.val.1 * y ^ p.val.2
  rw [Finset.sum_coe_sort (Finset.antidiagonal n)
    (fun p : ℕ × ℕ => appF1Coeff a b b' c p.1 p.2 * x ^ p.1 * y ^ p.2)]
  exact (appF1_totalDegree_eq a b b' c x y n).symm

/-- A homogeneous Carlson numerator at the rescaled F1 nodes is a terminating Gauss function. -/
private lemma appF2_reduction_numerator (a b' x y : ℂ) (ha : AppellRegular a) (n : ℕ)
    (hy : ‖y‖ < 1) :
    carlsonRPolynomialNumerator₂ n (a - b') b' x (x / (1 - y)) =
      (x / (1 - y)) ^ n * poch a n * ₂F₁ (-(n : ℂ)) (a - b') a y := by
  have hy0 : 1 - y ≠ 0 := by
    intro h
    have hn := norm_sub_norm_le (1 : ℂ) y
    rw [h] at hn
    simp at hn
    linarith
  have h := carlsonRPolynomialNumerator₂_smul n (a - b') b' (x / (1 - y)) (1 - y) 1
  rw [div_mul_cancel₀ x hy0, mul_one] at h
  rw [h, carlsonRPolynomialNumerator₂_eq_hypergeometric n (a - b') b' (1 - y) one_ne_zero
    (by rw [sub_add_cancel];exact poch_ne_zero_of_not_neg_nat ha n)]
  simp only [sub_add_cancel, div_one, sub_sub_cancel, one_pow, mul_one]
  dsimp only [poch]
  ring

/-- Exchanging the two separate upper and lower parameter pairs exchanges the F2 variables. -/
lemma appF2_swap (a b b' c c' x y : ℂ) :
    appF2 a b b' c c' x y = appF2 a b' b c' c y x := by
  rw [appF2, appF2, ← (Equiv.prodComm ℕ ℕ).tsum_eq]
  apply tsum_congr
  rintro ⟨m, n⟩
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [appF2Coeff_swap a b b' c c' n m]
  ring

/-- When the second lower parameter equals the common upper parameter, F2 reduces
to F1 with one rescaled variable, as germs at the origin. -/
@[dlmf 16.16.E3]
theorem appF2_reduction_appF1 (a b b' c : ℂ) (hc : AppellRegular c) (ha : AppellRegular a) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF2 a b b' c a x y) =ᶠ[𝓝 (0, 0)]
      (fun p => let x:=p.1; let y:=p.2; (1 - y) ^ (-b') *
        appF1 b (a - b') b' c x (x / (1 - y))) := by
  have hU : {p : ℂ × ℂ | ‖p.1‖ + ‖p.2‖ < 1} ∈ 𝓝 (0, 0) :=
    (isOpen_lt ((continuous_norm.comp continuous_fst).add
      (continuous_norm.comp continuous_snd)) continuous_const).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  simp only at hp ⊢
  have hx : ‖x‖ < 1 := by linarith [norm_nonneg y]
  have hy : ‖y‖ < 1 := by linarith [norm_nonneg x]
  have hny : 1-‖y‖ ≤ ‖1 - y‖ := by
    have h := norm_sub_norm_le (1 : ℂ) y
    simpa using h
  have hy0 : 1 - y ≠ 0 := by intro h; rw [h] at hny; simp at hny; linarith
  have hz : ‖x / (1 - y)‖ < 1 := by
    rw [norm_div, div_lt_one (by linarith)]
    linarith
  have hs := hasSum_appF2_gauss_fibers a b' b a c ha hc (x := y) (y := x)
    (by linarith)
  rw [← appF2_swap a b b' c a x y] at hs
  apply hs.unique
  have hR := (hasSum_appF1_totalDegree b (a - b') b' c hc hx hz).mul_left ((1 - y) ^ (-b'))
  refine hR.congr_fun fun n => ?_
  rw [appF2_reduction_numerator a b' x y ha n hy, euler_transformation_of_ne_neg_nat ha hy,
    show a - (a + (n : ℂ)) = -(n : ℂ) by ring,
    show -(n : ℂ) - b' = -b'+-(n : ℂ) by ring,
    cpow_add _ _ hy0, cpow_neg (1 - y) (n : ℂ), cpow_natCast, div_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end DLMF.Hypergeometric
