/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic.PowerSeries
public import DLMF.Theta.Identities
public import DLMF.Theta.SeriesAndZeros

/-!
# Theta functions: power series (DLMF §20.6)

The exponential power series 20.6.2–20.6.5 of `θⱼ(πz|τ)` about `z = 0`, with the lattice sums
`δ_{2j}, α_{2j}, β_{2j}, γ_{2j}` of 20.6.6–20.6.9. The lattice sums are defined as iterated sums,
inner over `m` and outer over `n` (the Eisenstein order of DLMF); for `2j ≥ 4` the order is
irrelevant (`thetaDelta_hasSum_lattice`), for `2j = 2` it matters. The power series are stated with
an explicit summability claim, so that Lean's convention `∑' = 0` for divergent series plays no
role.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic

/-- DLMF 20.6.2: for `|πz| < min |z_{m,n}|`,
`θ₁(πz|τ) = πz θ₁'(0|τ) exp(-∑_{j≥1} δ_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E2]
theorem jacobiThetaOneTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaLatticeMinNorm τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaDelta (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaOneTau (π * z) τ = π * z * jacobiThetaOneDerivNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.3: for `|πz|` below the distance to the shifted zero lattice
`π(m - 1/2 + nτ)`,
`θ₂(πz|τ) = θ₂(0|τ) exp(-∑_{j≥1} α_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E3]
theorem jacobiThetaTwoTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaShiftedLatticeMinNorm (1 / 2) 0 τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaAlpha (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaTwoTau (π * z) τ = jacobiThetaTwoNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.4: for `|πz|` below the distance to the shifted zero lattice
`π(m - 1/2 + (n - 1/2)τ)`,
`θ₃(πz|τ) = θ₃(0|τ) exp(-∑_{j≥1} β_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E4]
theorem jacobiThetaThreeTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaShiftedLatticeMinNorm (1 / 2) (1 / 2) τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaBeta (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaThreeTau (π * z) τ = jacobiThetaThreeNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.5: for `|πz|` below the distance to the shifted zero lattice
`π(m + (n - 1/2)τ)`,
`θ₄(πz|τ) = θ₄(0|τ) exp(-∑_{j≥1} γ_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E5]
theorem jacobiThetaFourTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaShiftedLatticeMinNorm 0 (1 / 2) τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaGamma (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaFourTau (π * z) τ = jacobiThetaFourNullTau τ * cexp (-S) := by
  sorry

/-- Absolute convergence of the (doubled, shifted) lattice sums for `k ≥ 3` (helper). -/
lemma p20R1_lattice_summable {τ : ℂ} (hτ : 0 < τ.im) (a b : ℤ) {k : ℕ} (hk : 3 ≤ k) :
    Summable (fun p : ℤ × ℤ =>
      (‖(((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ)‖⁻¹) ^ k) := by
  set z : UpperHalfPlane := ⟨τ, hτ⟩
  set x : ℤ × ℤ → (Fin 2 → ℤ) := fun p => ![2 * p.2 + b, 2 * p.1 + a] with hx
  have hinj : Function.Injective x := by
    intro p q h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp [hx] at h0 h1
    exact Prod.ext (by omega) (by omega)
  have hr := EisensteinSeries.r_pos z
  have hs := ((EisensteinSeries.summable_one_div_norm_rpow (k := k)
    (by exact_mod_cast (show 2 < k by omega))).comp_injective hinj).mul_left
      ((EisensteinSeries.r z)⁻¹ ^ k)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) hs
  simp only [Function.comp_apply]
  by_cases h0 : x p = 0
  · have e0 := congrFun h0 0; have e1 := congrFun h0 1
    simp [hx] at e0 e1
    have : (((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ) = 0 := by
      rw [show (2 * p.1 + a : ℤ) = 0 by omega, show (2 * p.2 + b : ℤ) = 0 by omega]; simp
    rw [this, norm_zero, inv_zero, zero_pow (by omega)]
    positivity
  · have hb := EisensteinSeries.r_mul_max_le z h0
    have heq : (x p 0 : ℂ) * (z : ℂ) + x p 1 =
        (((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ) := by
      simp [hx, z]; ring
    rw [heq] at hb
    have hxp : 0 < ‖x p‖ := norm_pos_iff.mpr h0
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← inv_pow, ← mul_pow]
    gcongr
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hb

/-- Summability of `g^{-k}` when `2g` runs over a shifted lattice (helper). -/
lemma p20R1_point_summable {τ : ℂ} (hτ : 0 < τ.im) (a b : ℤ) {k : ℕ} (hk : 3 ≤ k)
    {g : ℤ × ℤ → ℂ}
    (hg : ∀ p : ℤ × ℤ, 2 * g p = ((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ) :
    Summable (fun p : ℤ × ℤ => g p ^ (-(k : ℤ))) := by
  refine Summable.of_norm_bounded ((p20R1_lattice_summable hτ a b hk).mul_left (2 ^ k))
    (fun p => ?_)
  have hgp : g p = (((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ) / 2 := by
    rw [← hg p]; ring
  rw [hgp, norm_zpow, norm_div, zpow_neg, zpow_natCast, div_pow, inv_div, inv_pow,
    show ‖(2 : ℂ)‖ = 2 by norm_num, div_eq_mul_inv]

/-- Bound for a row sum `∑_m (m + w)^{-2}` with `Im w > 0`, via the `q`-expansion (helper). -/
lemma p3t_row_norm_le_pos {w : ℂ} (hw : 0 < w.im) :
    ‖∑' m : ℤ, ((m : ℂ) + w) ^ (-2 : ℤ)‖ ≤
      4 * π ^ 2 * (Real.exp (-2 * π * w.im) / (1 - Real.exp (-2 * π * w.im)) ^ 2) := by
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨w, hw⟩
  have e : (∑' m : ℤ, ((m : ℂ) + w) ^ (-2 : ℤ)) =
      ∑' n : ℤ, 1 / (((⟨w, hw⟩ : UpperHalfPlane) : ℂ) + n) ^ (1 + 1) := by
    congr 1; funext m; rw [zpow_neg, one_div, add_comm]; norm_num
  rw [e, h]
  set q := cexp (2 * π * I * ((⟨w, hw⟩ : UpperHalfPlane) : ℂ))
  have hq : ‖q‖ = Real.exp (-2 * π * w.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  have hq1 : ‖q‖ < 1 := by
    rw [hq, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hs : Summable (fun n : ℕ => ‖(n : ℂ) ^ 1 * q ^ n‖) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := ‖q‖) (by simpa using hq1)
    simpa [norm_pow] using this
  have hn := norm_tsum_le_tsum_norm hs
  have ht : ∑' n : ℕ, ‖(n : ℂ) ^ 1 * q ^ n‖ = ‖q‖ / (1 - ‖q‖) ^ 2 := by
    simp only [pow_one, norm_mul, Complex.norm_natCast, norm_pow]
    exact tsum_coe_mul_geometric_of_norm_lt_one (by simpa using hq1)
  rw [norm_mul, ← hq]
  have hc : ‖(-2 * π * I) ^ (1 + 1) / ((1 : ℕ).factorial : ℂ)‖ = 4 * π ^ 2 := by
    simp [norm_pow, abs_of_pos Real.pi_pos]; ring
  rw [hc, ← ht]
  gcongr

/-- A row sum `∑_m (m + w)^{-k}` is unchanged under `w ↦ -w` for even `k` (helper). -/
lemma p3t_row_neg (w : ℂ) {k : ℕ} (hk : Even k) :
    ∑' m : ℤ, ((m : ℂ) + -w) ^ (-(k : ℤ)) = ∑' m : ℤ, ((m : ℂ) + w) ^ (-(k : ℤ)) := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1; funext m
  simp only [Equiv.neg_apply, Int.cast_neg, zpow_neg, zpow_natCast]
  rw [show -(m : ℂ) + -w = -((m : ℂ) + w) by ring, hk.neg_pow]

/-- Uniform bound `‖∑_m (m + w)^{-2}‖ ≤ C e^{-2π|Im w|}` for `|Im w| ≥ δ > 0` (helper). -/
lemma p3t_row_norm_le {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : δ ≤ |w.im|) :
    ‖∑' m : ℤ, ((m : ℂ) + w) ^ (-2 : ℤ)‖ ≤
      4 * π ^ 2 / (1 - Real.exp (-2 * π * δ)) ^ 2 * Real.exp (-2 * π * |w.im|) := by
  have hρ : Real.exp (-2 * π * δ) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have key : ∀ v : ℂ, 0 < v.im → δ ≤ v.im → ‖∑' m : ℤ, ((m : ℂ) + v) ^ (-2 : ℤ)‖ ≤
      4 * π ^ 2 / (1 - Real.exp (-2 * π * δ)) ^ 2 * Real.exp (-2 * π * v.im) := by
    intro v hv hδv
    refine (p3t_row_norm_le_pos hv).trans ?_
    have h1 : Real.exp (-2 * π * v.im) ≤ Real.exp (-2 * π * δ) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have h0 : 0 < 1 - Real.exp (-2 * π * δ) := by linarith
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff₀ (by
      have : 0 < 1 - Real.exp (-2 * π * v.im) := by linarith
      positivity) (by positivity)]
    have h2 : (1 - Real.exp (-2 * π * δ)) ^ 2 ≤ (1 - Real.exp (-2 * π * v.im)) ^ 2 := by
      gcongr
    have := Real.exp_pos (-2 * π * v.im)
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity :
      (0 : ℝ) ≤ 4 * π ^ 2 * Real.exp (-2 * π * v.im))]
  rcases le_or_gt 0 w.im with h | h
  · rw [abs_of_nonneg h] at hw ⊢
    exact key w (by linarith) hw
  · rw [abs_of_neg h] at hw ⊢
    have e := p3t_row_neg (-w) (k := 2) even_two
    rw [neg_neg] at e
    push_cast at e
    rw [e]
    simpa using key (-w) (by simpa using h) (by simpa using hw)

/-- Summability over `n` of the rows `∑_m (m + w_n)^{-2}` when `Im w_n = (n + s) t`,
`|s| ≤ 1/2`, `t > 0` (helper). -/
lemma p3t_row_summable_two {t s : ℝ} (ht : 0 < t) (hs : |s| ≤ 1 / 2) {w : ℤ → ℂ}
    (hw : ∀ n, (w n).im = (n + s) * t) :
    Summable (fun n : ℤ => ∑' m : ℤ, ((m : ℂ) + w n) ^ (-2 : ℤ)) := by
  set C := 4 * π ^ 2 / (1 - Real.exp (-2 * π * (t / 2))) ^ 2
  set ρ := Real.exp (-2 * π * t)
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by simp only [ρ, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hg : Summable (fun n : ℤ => C * Real.exp (π * t) * ρ ^ n.natAbs) := by
    refine Summable.mul_left _ ?_
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨by simpa using summable_geometric_of_lt_one hρ0 hρ1,
      by simpa using summable_geometric_of_lt_one hρ0 hρ1⟩
  refine Summable.of_norm_bounded_eventually hg ?_
  have : {n : ℤ | n ≠ 0} ∈ cofinite := by
    simpa using (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  filter_upwards [this] with n hn
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  have hlow : |(n : ℝ)| - 1 / 2 ≤ |(n : ℝ) + s| := by
    have := abs_sub_abs_le_abs_sub (n : ℝ) (-s)
    rw [abs_neg, sub_neg_eq_add] at this; linarith
  have him : |(w n).im| = |(n : ℝ) + s| * t := by rw [hw, abs_mul, abs_of_pos ht]
  have hδ : t / 2 ≤ |(w n).im| := by rw [him]; nlinarith
  have hC : 0 ≤ C := by positivity
  calc _ ≤ C * Real.exp (-2 * π * |(w n).im|) := p3t_row_norm_le (by linarith) hδ
    _ ≤ C * Real.exp (π * t) * ρ ^ n.natAbs := by
      refine le_of_le_of_eq (mul_le_mul_of_nonneg_left ?_ hC) (mul_assoc _ _ _).symm
      rw [show ρ ^ n.natAbs = Real.exp (-2 * π * t * n.natAbs) by
        rw [← Real.exp_nat_mul]; ring_nf, ← Real.exp_add, him]
      apply Real.exp_le_exp.mpr
      have hna : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hna]
      nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 2 * π * t)]

/-- Summability over `n` of the shifted lattice rows `∑_m (m + a/2 + (n + b/2)τ)^{-2j}`,
`j ≥ 1` (helper). -/
lemma p3t_rows_summable {τ : ℂ} (hτ : 0 < τ.im) {j : ℕ} (hj : 1 ≤ j) (a b : ℤ)
    (hb : b = 0 ∨ b = -1) :
    Summable (fun n : ℤ => ∑' m : ℤ,
      ((m : ℂ) + ((a : ℂ) / 2 + ((n : ℂ) + (b : ℂ) / 2) * τ)) ^ (-((2 * j : ℕ) : ℤ))) := by
  rcases Nat.lt_or_ge j 2 with h1 | h2
  · obtain rfl : j = 1 := by omega
    refine p3t_row_summable_two (s := b / 2) hτ ?_ (fun n => ?_)
    · rcases hb with rfl | rfl <;> norm_num [abs_of_neg]
    · simp
  · have hs := p20R1_point_summable hτ a b (k := 2 * j) (by omega)
      (g := fun p => (p.1 : ℂ) + ((a : ℂ) / 2 + ((p.2 : ℂ) + (b : ℂ) / 2) * τ))
      (fun p => by push_cast; ring)
    have hs' : Summable ((fun p : ℤ × ℤ => ((p.1 : ℂ) + ((a : ℂ) / 2 +
        ((p.2 : ℂ) + (b : ℂ) / 2) * τ)) ^ (-((2 * j : ℕ) : ℤ))) ∘ Prod.swap) :=
      (Equiv.prodComm ℤ ℤ).summable_iff.mpr hs
    exact hs'.prod

/-- Even/odd splitting of a row: `2^k ∑_m (m + 2w)^{-k} = ∑_m (m + w)^{-k} + ∑_m (m - 1/2 + w)^{-k}`
for `k ≥ 2` (helper). -/
lemma p3t_row_split {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    2 ^ k * ∑' m : ℤ, ((m : ℂ) + 2 * w) ^ (-(k : ℤ)) =
      ∑' m : ℤ, ((m : ℂ) + w) ^ (-(k : ℤ)) + ∑' m : ℤ, ((m : ℂ) - 1 / 2 + w) ^ (-(k : ℤ)) := by
  have hsum : ∀ c : ℂ, Summable (fun m : ℤ => ((m : ℂ) + c) ^ (-(k : ℤ))) := fun c =>
    (EisensteinSeries.linear_right_summable c 1 (k := k) (by exact_mod_cast hk)).congr
      (fun m => by simp [zpow_neg, add_comm])
  have hA := (hsum w).hasSum
  have hB : HasSum (fun j : ℤ => ((j : ℂ) + 1 / 2 + w) ^ (-(k : ℤ)))
      (∑' m : ℤ, ((m : ℂ) - 1 / 2 + w) ^ (-(k : ℤ))) := by
    have h := ((hsum (-1 / 2 + w)).hasSum)
    rw [← (Equiv.addRight (1 : ℤ)).hasSum_iff] at h
    convert h using 1
    · funext j; simp only [Function.comp_apply, Equiv.coe_addRight]; push_cast; ring_nf
    · congr 1; funext m; ring_nf
  have h2 : (2 : ℂ) ^ (-(k : ℤ)) * 2 ^ k = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]
  have hP := (p20R1_parityEquivInt.hasSum_iff).mpr (hsum (2 * w)).hasSum
  have hA' : HasSum ((fun m : ℤ => ((m : ℂ) + 2 * w) ^ (-(k : ℤ))) ∘ p20R1_parityEquivInt ∘
      Sum.inl) ((2 : ℂ) ^ (-(k : ℤ)) * ∑' m : ℤ, ((m : ℂ) + w) ^ (-(k : ℤ))) := by
    convert hA.mul_left ((2 : ℂ) ^ (-(k : ℤ))) using 1
    funext j
    simp only [Function.comp_apply, p20R1_parityEquivInt, Equiv.coe_fn_mk, Sum.elim_inl]
    rw [← mul_zpow]; push_cast; ring_nf
  have hB' : HasSum ((fun m : ℤ => ((m : ℂ) + 2 * w) ^ (-(k : ℤ))) ∘ p20R1_parityEquivInt ∘
      Sum.inr) ((2 : ℂ) ^ (-(k : ℤ)) * ∑' m : ℤ, ((m : ℂ) - 1 / 2 + w) ^ (-(k : ℤ))) := by
    convert hB.mul_left ((2 : ℂ) ^ (-(k : ℤ))) using 1
    funext j
    simp only [Function.comp_apply, p20R1_parityEquivInt, Equiv.coe_fn_mk, Sum.elim_inr]
    rw [← mul_zpow]; push_cast; ring_nf
  rw [(hP.unique (hA'.sum hB'))]
  linear_combination (∑' m : ℤ, ((m : ℂ) + w) ^ (-(k : ℤ)) +
    ∑' m : ℤ, ((m : ℂ) - 1 / 2 + w) ^ (-(k : ℤ))) * h2

/-- DLMF 20.6.10: `α_{2j}(τ) = 2^{2j} δ_{2j}(2τ) - δ_{2j}(τ)` and
`β_{2j}(τ) = 2^{2j} γ_{2j}(2τ) - γ_{2j}(τ)`, `j ≥ 1`, `Im τ > 0`. -/
@[dlmf 20.6.E10]
theorem thetaAlpha_thetaBeta_eq {τ : ℂ} (hτ : 0 < τ.im) (j : ℕ) (hj : 1 ≤ j) :
    thetaAlpha (2 * j) τ = 2 ^ (2 * j) * thetaDelta (2 * j) (2 * τ) - thetaDelta (2 * j) τ ∧
      thetaBeta (2 * j) τ = 2 ^ (2 * j) * thetaGamma (2 * j) (2 * τ) - thetaGamma (2 * j) τ := by
  have hk : 2 ≤ 2 * j := by omega
  have hk0 : ((2 * j : ℕ) : ℤ) ≠ 0 := by omega
  -- rows in the common form `∑_m (m + w)^{-k}`
  have hD : ∀ σ : ℂ, thetaDelta (2 * j) σ =
      ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) + n * σ) ^ (-((2 * j : ℕ) : ℤ)) := by
    intro σ
    refine tsum_congr fun n => tsum_congr fun m => ?_
    split_ifs with h
    · simp only [h.1, h.2, Int.cast_zero, zero_mul, add_zero]
      exact (zero_zpow _ (neg_ne_zero.mpr hk0)).symm
    · rfl
  have sE : Summable (fun n : ℤ => ∑' m : ℤ, ((m : ℂ) + n * τ) ^ (-((2 * j : ℕ) : ℤ))) :=
    (p3t_rows_summable hτ hj 0 0 (Or.inl rfl)).congr fun n => tsum_congr fun m => by
      congr 1; push_cast; ring
  have sA : Summable (fun n : ℤ => ∑' m : ℤ,
      ((m : ℂ) - 1 / 2 + n * τ) ^ (-((2 * j : ℕ) : ℤ))) :=
    (p3t_rows_summable hτ hj (-1) 0 (Or.inl rfl)).congr fun n => tsum_congr fun m => by
      congr 1; push_cast; ring
  have sG : Summable (fun n : ℤ => ∑' m : ℤ,
      ((m : ℂ) + (n - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ))) :=
    (p3t_rows_summable hτ hj 0 (-1) (Or.inr rfl)).congr fun n => tsum_congr fun m => by
      congr 1; push_cast; ring
  have sB : Summable (fun n : ℤ => ∑' m : ℤ,
      ((m : ℂ) - 1 / 2 + (n - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ))) :=
    (p3t_rows_summable hτ hj (-1) (-1) (Or.inr rfl)).congr fun n => tsum_congr fun m => by
      congr 1; push_cast; ring
  constructor
  · rw [hD, hD, thetaAlpha, ← tsum_mul_left]
    have e : ∀ n : ℤ, 2 ^ (2 * j) * ∑' m : ℤ, ((m : ℂ) + n * (2 * τ)) ^ (-((2 * j : ℕ) : ℤ)) =
        ∑' m : ℤ, ((m : ℂ) + n * τ) ^ (-((2 * j : ℕ) : ℤ)) +
          ∑' m : ℤ, ((m : ℂ) - 1 / 2 + n * τ) ^ (-((2 * j : ℕ) : ℤ)) := by
      intro n
      have := p3t_row_split hk (n * τ)
      rw [show (n : ℂ) * (2 * τ) = 2 * (n * τ) by ring]
      exact_mod_cast this
    rw [tsum_congr e, Summable.tsum_add sE sA]
    ring
  · rw [thetaBeta, thetaGamma, thetaGamma, ← tsum_mul_left]
    have e : ∀ n : ℤ, 2 ^ (2 * j) * ∑' m : ℤ,
        ((m : ℂ) + (n - 1 / 2) * (2 * τ)) ^ (-((2 * j : ℕ) : ℤ)) =
        ∑' m : ℤ, ((m : ℂ) + (n - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ)) +
          ∑' m : ℤ, ((m : ℂ) - 1 / 2 + (n - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ)) := by
      intro n
      have := p3t_row_split hk ((n - 1 / 2) * τ)
      rw [show ((n : ℂ) - 1 / 2) * (2 * τ) = 2 * ((n - 1 / 2) * τ) by ring]
      exact_mod_cast this
    rw [tsum_congr e, Summable.tsum_add sG sB]
    ring

/-- `∑_{a,b ≥ 0} (a + b + 2)^{-2}` diverges (helper). -/
lemma p20R1_not_summable_sq_add :
    ¬ Summable (fun p : ℕ × ℕ => (1 : ℝ) / ((p.1 : ℝ) + p.2 + 2) ^ 2) := by
  intro h
  have h0 : ∀ p : ℕ × ℕ, 0 ≤ (1 : ℝ) / ((p.1 : ℝ) + p.2 + 2) ^ 2 := fun _ => by positivity
  have hf : Summable (fun a : ℕ => ∑' b : ℕ, (1 : ℝ) / ((a : ℝ) + b + 2) ^ 2) := h.prod
  apply Real.not_summable_one_div_natCast
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun a => ?_) (hf.mul_left 4)
  have hs : Summable (fun b : ℕ => (1 : ℝ) / ((a : ℝ) + b + 2) ^ 2) := h.prod_factor a
  have hle := hs.sum_le_tsum (Finset.range (a + 1)) (fun b _ => by positivity)
  have hlow : ∀ b ∈ Finset.range (a + 1), (1 : ℝ) / (2 * ((a : ℝ) + 1)) ^ 2 ≤
      1 / ((a : ℝ) + b + 2) ^ 2 := by
    intro b hb
    have : (b : ℝ) ≤ a := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    gcongr
    linarith
  have hsum := Finset.sum_le_sum hlow
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have : (1 : ℝ) / ((a + 1 : ℕ) : ℝ) = 4 * (((a + 1 : ℕ) : ℝ) * (1 / (2 * ((a : ℝ) + 1)) ^ 2)) := by
    push_cast; field_simp; ring
  rw [this]
  push_cast at hsum ⊢
  nlinarith

/-- An absolutely summable double series equals its iterated sum, inner over the first
coordinate (helper). -/
lemma p20R1_hasSum_iter {f : ℤ × ℤ → ℂ} (hf : Summable f) :
    HasSum f (∑' n : ℤ, ∑' m : ℤ, f (m, n)) := by
  have hs : Summable (f ∘ Prod.swap) := (Equiv.prodComm ℤ ℤ).summable_iff.mpr hf
  have h1 := hs.hasSum.prod_fiberwise (fun n => (hs.prod_factor n).hasSum)
  have h2 : HasSum f (∑' p, (f ∘ Prod.swap) p) :=
    (Equiv.prodComm ℤ ℤ).hasSum_iff.mp hs.hasSum
  have e : (∑' n : ℤ, ∑' m : ℤ, f (m, n)) = ∑' p, (f ∘ Prod.swap) p := h1.tsum_eq
  rw [e]; exact h2

/-- DLMF §20.6: for `2j ≥ 4` the order of summation in the lattice sums does not matter: the
double series converge absolutely, and their unordered sums equal the iterated sums. -/
@[dlmf 20.6]
theorem thetaDelta_hasSum_lattice {τ : ℂ} (hτ : 0 < τ.im) {j : ℕ} (hj : 2 ≤ j) :
    HasSum (fun p : ℤ × ℤ => if p.1 = 0 ∧ p.2 = 0 then 0 else
        ((p.1 : ℂ) + p.2 * τ) ^ (-((2 * j : ℕ) : ℤ))) (thetaDelta (2 * j) τ) ∧
      HasSum (fun p : ℤ × ℤ => ((p.1 : ℂ) - 1 / 2 + p.2 * τ) ^ (-((2 * j : ℕ) : ℤ)))
        (thetaAlpha (2 * j) τ) ∧
      HasSum (fun p : ℤ × ℤ => ((p.1 : ℂ) - 1 / 2 + (p.2 - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ)))
        (thetaBeta (2 * j) τ) ∧
      HasSum (fun p : ℤ × ℤ => ((p.1 : ℂ) + (p.2 - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ)))
        (thetaGamma (2 * j) τ) := by
  have hk : 3 ≤ 2 * j := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs := p20R1_point_summable hτ 0 0 hk (g := fun p => (p.1 : ℂ) + p.2 * τ)
      (fun p => by push_cast; ring)
    have hs' : Summable (fun p : ℤ × ℤ => if p.1 = 0 ∧ p.2 = 0 then 0 else
        ((p.1 : ℂ) + p.2 * τ) ^ (-((2 * j : ℕ) : ℤ))) := by
      refine Summable.of_norm_bounded hs.norm (fun p => ?_)
      split_ifs <;> simp
      positivity
    exact p20R1_hasSum_iter hs'
  · exact p20R1_hasSum_iter (p20R1_point_summable hτ (-1) 0 hk (fun p => by push_cast; ring))
  · exact p20R1_hasSum_iter (p20R1_point_summable hτ (-1) (-1) hk (fun p => by push_cast; ring))
  · exact p20R1_hasSum_iter (p20R1_point_summable hτ 0 (-1) hk (fun p => by push_cast; ring))

/-- DLMF §20.6: for `j = 1` the order matters: the double series for `δ₂` is not absolutely
summable. -/
@[dlmf 20.6]
theorem thetaDelta_two_not_summable {τ : ℂ} (hτ : 0 < τ.im) :
    ¬ Summable (fun p : ℤ × ℤ => if p.1 = 0 ∧ p.2 = 0 then (0 : ℂ) else
        ((p.1 : ℂ) + p.2 * τ) ^ (-2 : ℤ)) := by
  intro h
  have hn := (summable_norm_iff.mpr h).comp_injective
    (i := fun p : ℕ × ℕ => (((p.1 + 1 : ℕ) : ℤ), ((p.2 + 1 : ℕ) : ℤ))) (by
      intro p q hpq
      simp only [Prod.mk.injEq, Nat.cast_inj, Nat.add_right_cancel_iff] at hpq
      exact Prod.ext hpq.1 hpq.2)
  apply p20R1_not_summable_sq_add
  set C := 1 + ‖τ‖ with hC
  have hC0 : 0 < C := by positivity
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) (hn.mul_left (C ^ 2))
  obtain ⟨a, b⟩ := p
  simp only [Function.comp_apply]
  have hne : ¬ ((((a + 1 : ℕ) : ℤ)) = 0 ∧ (((b + 1 : ℕ) : ℤ)) = 0) := by omega
  simp only [hne, ↓reduceIte]
  have hw : ((((a + 1 : ℕ) : ℤ) : ℂ) + (((b + 1 : ℕ) : ℤ) : ℂ) * τ) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    rcases this with h1 | h1
    · linarith [h1]
    · linarith
  rw [zpow_neg, norm_inv, zpow_two, norm_mul]
  set w := ((((a + 1 : ℕ) : ℤ) : ℂ) + (((b + 1 : ℕ) : ℤ) : ℂ) * τ)
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwle : ‖w‖ ≤ C * ((a : ℝ) + b + 2) := by
    calc ‖w‖ ≤ ‖((((a + 1 : ℕ) : ℤ) : ℂ))‖ + ‖(((b + 1 : ℕ) : ℤ) : ℂ)‖ * ‖τ‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ = ((a : ℝ) + 1) + ((b : ℝ) + 1) * ‖τ‖ := by
          simp only [Int.cast_natCast, Complex.norm_natCast]; push_cast; ring
      _ ≤ C * ((a : ℝ) + b + 2) := by rw [hC]; nlinarith [norm_nonneg τ]
  rw [div_le_iff₀ (by positivity)]
  have : ‖w‖ * ‖w‖ ≤ (C * ((a : ℝ) + b + 2)) ^ 2 := by nlinarith
  calc (1 : ℝ) = (‖w‖ * ‖w‖)⁻¹ * (‖w‖ * ‖w‖) := by field_simp
    _ ≤ (‖w‖ * ‖w‖)⁻¹ * (C * ((a : ℝ) + b + 2)) ^ 2 := by gcongr
    _ = _ := by ring

end DLMF.Theta

end
