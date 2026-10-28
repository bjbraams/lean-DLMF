/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Identities.Dougall

/-!
# Dixon summation and its analytic continuation

Analytic estimates for Dixon summation and the resulting general hypergeometric summation
identities.

Source references and common attribution are retained in
`DLMF.Hypergeometric.Identities`.
-/

@[expose] public section

open Complex

open scoped Real

noncomputable section

namespace DLMF.Hypergeometric

section CarlsonApplications

open Filter Set

open scoped Topology

namespace DixonAux

open CarlsonAux

variable {a b : ℂ}

/-- The normalized terms `(a)_n (b)_n (c)_n / ((1+a-b)_n n! Γ(1+a-c+n))` of Dixon's series. -/
def s (a b c : ℂ) (n : ℕ) : ℂ :=
  gaussHGCoeff a b (1 + a - b) n * poch c n * (Gamma (1 + a - c + n))⁻¹

/-- The WZ certificate. -/
def H (a b c : ℂ) (n : ℕ) : ℂ :=
  gaussHGCoeff a b (1 + a - b) n * (a + n) * (b + n) * poch c n * (Gamma (2 + a - c + n))⁻¹

/-- The WZ relation for Dixon's series at `n = 0`. -/
theorem wz_zero (a b c : ℂ) :
    (1 + a / 2 - b - c) * s a b c 0 - (1 + a / 2 - c) * (1 + a - b - c) * s a b (c - 1) 0 =
      -(1 / 2) * H a b c 0 := by
  have e : (Gamma (1 + a - c))⁻¹ = (1 + a - c) * (Gamma (2 + a - c))⁻¹ := by
    rw [← mul_recip_Gamma_add_one]; ring_nf
  simp only [s, H, gaussHGCoeff, poch_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero,
    add_zero, mul_one, div_one]
  rw [show 1 + a - (c - 1) = 2 + a - c by ring, e]
  ring

/-- The WZ relation for Dixon's series: the `c`-difference of `s` telescopes through the certificate
  `H`. -/
theorem wz_succ (hb : ∀ k : ℕ, 1 + a - b ≠ -k) (c : ℂ) (n : ℕ) :
    (1 + a / 2 - b - c) * s a b c (n + 1) -
        (1 + a / 2 - c) * (1 + a - b - c) * s a b (c - 1) (n + 1) =
      -(1 / 2) * (H a b c (n + 1) - H a b c n) := by
  have hp : poch (1 + a - b) n ≠ 0 := poch_ne_zero_of_not_neg_nat hb n
  have hq : 1 + a - b + n ≠ 0 := fun h => hb n (by linear_combination h)
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have e2 : (Gamma (2 + a - c + n))⁻¹ = (2 + a - c + n) * (Gamma (3 + a - c + n))⁻¹ := by
    rw [← mul_recip_Gamma_add_one]; ring_nf
  have c1 : poch (c - 1) (n + 1) = (c - 1) * poch c n := by
    rw [poch_succ_left]; ring_nf
  simp only [s, H]
  rw [c1]
  simp only [gaussHGCoeff, poch_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [show 1 + a - c + ((n : ℂ) + 1) = 2 + a - c + n by ring,
    show 1 + a - (c - 1) + ((n : ℂ) + 1) = 3 + a - c + n by ring,
    show 2 + a - c + ((n : ℂ) + 1) = 3 + a - c + n by ring, e2]
  field_simp
  ring

/-- The normalized Dixon series. -/
def Lh (a b c : ℂ) : ℂ := ∑' n : ℕ, s a b c n

/-- **The recurrence in `c`**, from the WZ pair. -/
theorem recurrence (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {c : ℂ} (h1 : Summable (s a b c))
    (h2 : Summable (s a b (c - 1))) (hH : Tendsto (H a b c) atTop (𝓝 0)) :
    (1 + a / 2 - b - c) * Lh a b c = (1 + a / 2 - c) * (1 + a - b - c) * Lh a b (c - 1) := by
  set T : ℕ → ℂ := fun n =>
    (1 + a / 2 - b - c) * s a b c n - (1 + a / 2 - c) * (1 + a - b - c) * s a b (c - 1) n
  have hT : Summable T := (h1.mul_left _).sub (h2.mul_left _)
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), T n = -(1 / 2) * H a b c N := by
    intro N
    induction N with
    | zero => simp [T, wz_zero]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [T]
      rw [wz_succ hb]
      ring
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, T n) atTop (𝓝 (∑' n, T n)) :=
    hT.hasSum.tendsto_sum_nat
  have hlim' : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), T n) atTop (𝓝 0) := by
    simp_rw [hpartial]; simpa using hH.const_mul (-(1 / 2) : ℂ)
  have h0 : ∑' n, T n = 0 :=
    tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr hlim) hlim'
  simp only [T] at h0
  rw [(h1.mul_left _).tsum_sub (h2.mul_left _), tsum_mul_left, tsum_mul_left,
    sub_eq_zero] at h0
  exact h0

/-- The periodic normalization. -/
def P (a b c : ℂ) : ℂ :=
  Lh a b c * Gamma (1 + a / 2 - c) * Gamma (1 + a - b - c) * (Gamma (1 + a / 2 - b - c))⁻¹

/-- Under convergence, the normalization `P` is invariant under `c ↦ c - 1`. -/
theorem P_sub_one (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {c : ℂ} (h1 : Summable (s a b c))
    (h2 : Summable (s a b (c - 1))) (hH : Tendsto (H a b c) atTop (𝓝 0))
    (hc1 : 1 + a / 2 - c ≠ 0) (hc2 : 1 + a - b - c ≠ 0) :
    P a b (c - 1) = P a b c := by
  have hrec := recurrence hb h1 h2 hH
  have g1 : Gamma (1 + a / 2 - (c - 1)) = (1 + a / 2 - c) * Gamma (1 + a / 2 - c) := by
    rw [show 1 + a / 2 - (c - 1) = (1 + a / 2 - c) + 1 by ring, Complex.Gamma_add_one _ hc1]
  have g2 : Gamma (1 + a - b - (c - 1)) = (1 + a - b - c) * Gamma (1 + a - b - c) := by
    rw [show 1 + a - b - (c - 1) = (1 + a - b - c) + 1 by ring, Complex.Gamma_add_one _ hc2]
  have g3 : (Gamma (1 + a / 2 - b - c))⁻¹ =
      (1 + a / 2 - b - c) * (Gamma (1 + a / 2 - b - (c - 1)))⁻¹ := by
    rw [← mul_recip_Gamma_add_one]; ring_nf
  simp only [P]
  rw [g1, g2, g3]
  linear_combination (Gamma (1 + a / 2 - c) * Gamma (1 + a - b - c) *
    (Gamma (1 + a / 2 - b - (c - 1)))⁻¹) * hrec.symm

/-- `(a + n)(b + n) = O(n²)`. -/
theorem isBigO_mul_add_mul_add (a b : ℂ) :
    (fun n : ℕ => (a + n) * (b + n)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (2 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound ((‖a‖ + 1) * (‖b‖ + 1)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : ‖a + n‖ ≤ (‖a‖ + 1) * n := by
    refine (norm_add_le _ _).trans ?_; simp; nlinarith [norm_nonneg a]
  have hb : ‖b + n‖ ≤ (‖b‖ + 1) * n := by
    refine (norm_add_le _ _).trans ?_; simp; nlinarith [norm_nonneg b]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    show (n : ℝ) ^ (2 : ℝ) = n * n by rw [Real.rpow_two]; ring]
  calc ‖a + n‖ * ‖b + n‖ ≤ ((‖a‖ + 1) * n) * ((‖b‖ + 1) * n) :=
        mul_le_mul ha hb (norm_nonneg _) (by positivity)
    _ = (‖a‖ + 1) * (‖b‖ + 1) * (n * n) := by ring

/-- For `c = -j`, the Dixon terms vanish beyond index `j`. -/
theorem s_neg_nat_eq_zero (a b : ℂ) {j n : ℕ} (h : j < n) : s a b (-(j : ℂ)) n = 0 := by
  simp [s, poch_neg_nat_eq_zero h]

/-- For `c = -j`, the WZ certificate vanishes beyond index `j`. -/
theorem H_neg_nat_eq_zero (a b : ℂ) {j n : ℕ} (h : j < n) : H a b (-(j : ℂ)) n = 0 := by
  simp [H, poch_neg_nat_eq_zero h]

/-- For `c = -j` the Dixon series terminates, hence is summable. -/
theorem summable_s_neg_nat (a b : ℂ) (j : ℕ) : Summable (s a b (-(j : ℂ))) :=
  summable_of_ne_finset_zero (s := Finset.range (j + 1)) fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    exact s_neg_nat_eq_zero a b (by omega)

/-- For `c = -j` the WZ certificate tends to `0`. -/
theorem tendsto_H_neg_nat (a b : ℂ) (j : ℕ) : Tendsto (H a b (-(j : ℂ))) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_gt_atTop j] with n hn
    exact (H_neg_nat_eq_zero a b hn).symm)

/-- Convergence of the normalized Dixon series and decay of the certificate, for
`Re(1 + a/2 - b - c) > 0`. -/
theorem summable_s_and_tendsto_H (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {c : ℂ}
    (hc : 0 < (1 + a / 2 - b - c).re) :
    Summable (s a b c) ∧ Tendsto (H a b c) atTop (𝓝 0) := by
  by_cases hneg : ∃ j : ℕ, c = -j
  · obtain ⟨j, rfl⟩ := hneg
    exact ⟨summable_s_neg_nat a b j, tendsto_H_neg_nat a b j⟩
  push Not at hneg
  have hGc : Gamma c ≠ 0 := Complex.Gamma_ne_zero hneg
  have hpoch : ∀ n : ℕ, poch c n = Gamma (n + c) * (Gamma c)⁻¹ := by
    intro n
    have h := Complex.Gamma_add_nat_div_Gamma_eq (n := n) c hneg
    rw [poch, ← h, add_comm, div_eq_mul_inv]
  have hone : ∀ n : ℕ, Gamma ((n : ℂ) + 1) * (Gamma ((n : ℂ) + 1))⁻¹ = 1 := fun n =>
    mul_inv_cancel₀ (by rw [Complex.Gamma_nat_eq_factorial]; exact_mod_cast n.factorial_ne_zero)
  have hcoef := isBigO_gaussHGCoeff a b (1 + a - b) hb
  have hre : (a + b - (1 + a - b) - 1).re = 2 * b.re - 2 := by simp; ring
  rw [hre] at hcoef
  have hcre : 0 < 1 + a.re / 2 - b.re - c.re := by simpa using hc
  constructor
  · -- `s_n = O(n^{2Re b - 2} · n^{2 Re c - Re a - 1})`
    have hrat := isBigO_Gamma_ratio c 1 (1 + a - c) 1
    have heq : (s a b c) = fun n : ℕ => (Gamma c)⁻¹ * (gaussHGCoeff a b (1 + a - b) n *
        (Gamma (n + c) * Gamma (n + 1) * (Gamma (n + (1 + a - c)))⁻¹ * (Gamma (n + 1))⁻¹)) := by
      funext n
      simp only [s, hpoch]
      rw [show (1 : ℂ) + a - c + n = n + (1 + a - c) by ring]
      have := hone n
      linear_combination (gaussHGCoeff a b (1 + a - b) n * Gamma (↑n + c) * (Gamma c)⁻¹ *
        (Gamma (↑n + (1 + a - c)))⁻¹) * this.symm
    rw [heq]
    refine Summable.mul_left _ (summable_of_isBigO_nat
      (Real.summable_nat_rpow.mpr (show (2 * b.re - 2) + (c + 1 - (1 + a - c) - 1).re < -1 by
        simp; linarith)) ?_)
    refine (hcoef.mul hrat).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [one_mul, ← Real.rpow_add hn0]
  · -- `H_n = O(n^{2 Re b + 2 Re c - Re a - 2})`, a negative exponent
    have hrat := isBigO_Gamma_ratio c 1 (2 + a - c) 1
    have hpoly := isBigO_mul_add_mul_add a b
    have heq : (H a b c) = fun n : ℕ => (Gamma c)⁻¹ * (gaussHGCoeff a b (1 + a - b) n *
        ((a + n) * (b + n)) *
        (Gamma (n + c) * Gamma (n + 1) * (Gamma (n + (2 + a - c)))⁻¹ * (Gamma (n + 1))⁻¹)) := by
      funext n
      simp only [H, hpoch]
      rw [show (2 : ℂ) + a - c + n = n + (2 + a - c) by ring]
      have := hone n
      linear_combination (gaussHGCoeff a b (1 + a - b) n * (a + n) * (b + n) *
        Gamma (↑n + c) * (Gamma c)⁻¹ * (Gamma (↑n + (2 + a - c)))⁻¹) * this.symm
    rw [heq]
    have hexp : (2 * b.re - 2) + 2 + (c + 1 - (2 + a - c) - 1).re < 0 := by simp; linarith
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 * b.re - 2) + 2 +
        (c + 1 - (2 + a - c) - 1).re)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (show 0 < -((2 * b.re - 2) + 2 +
        (c + 1 - (2 + a - c) - 1).re) by linarith)).comp tendsto_natCast_atTop_atTop
      refine this.congr fun n => ?_
      simp only [Function.comp, neg_neg]
    have hbig : (fun n : ℕ => gaussHGCoeff a b (1 + a - b) n * ((a + n) * (b + n)) *
        (Gamma (n + c) * Gamma (n + 1) * (Gamma (n + (2 + a - c)))⁻¹ * (Gamma (n + 1))⁻¹))
        =O[atTop] fun n : ℕ => (n : ℝ) ^ ((2 * b.re - 2) + 2 +
          (c + 1 - (2 + a - c) - 1).re) := by
      refine ((hcoef.mul hpoly).mul hrat).trans ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [one_mul, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    simpa using (hbig.trans_tendsto hlim).const_mul (Gamma c)⁻¹

/-- The constant `Γ(1+a/2)Γ(1+a-b)/(Γ(1+a)Γ(1+a/2-b))`. -/
def K (a b : ℂ) : ℂ :=
  Gamma (1 + a / 2) * Gamma (1 + a - b) * (Gamma (1 + a))⁻¹ * (Gamma (1 + a / 2 - b))⁻¹

/-- At `c = 0` the normalization `P` equals the constant `K`. -/
theorem P_zero (a b : ℂ) : P a b 0 = K a b := by
  have hL : Lh a b 0 = (Gamma (1 + a))⁻¹ := by
    rw [Lh, tsum_eq_single 0]
    · simp [s, gaussHGCoeff, poch_zero]
    · intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [s]
  simp only [P, K, hL, sub_zero]
  ring

/-- **Terminating Dixon** in normalized form: `P(-j) = K` for all `j`. -/
theorem P_neg_nat (ha : ∀ k : ℕ, 1 + a / 2 ≠ -k) (hb : ∀ k : ℕ, 1 + a - b ≠ -k) (j : ℕ) :
    P a b (-(j : ℂ)) = K a b := by
  induction j with
  | zero => simpa using P_zero a b
  | succ j ih =>
    have h := P_sub_one hb (c := -(j : ℂ)) (summable_s_neg_nat a b j)
      (by simpa [sub_eq_add_neg, add_comm] using summable_s_neg_nat a b (j + 1))
      (tendsto_H_neg_nat a b j)
      (fun h0 => ha j (by linear_combination h0)) (fun h0 => hb j (by linear_combination h0))
    rw [← ih, ← h]
    congr 1
    push_cast; ring

/-- `(c)_n / Γ(1-c) = (-1)^n / Γ(1-c-n)`, for every `c`. -/
theorem poch_mul_recip_Gamma_one_sub (c : ℂ) (n : ℕ) :
    poch c n * (Gamma (1 - c))⁻¹ = (-1) ^ n * (Gamma (1 - c - n))⁻¹ := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have h := mul_recip_Gamma_add_one (-c - n)
    rw [show -c - (n : ℂ) + 1 = 1 - c - n by ring] at h
    rw [poch_succ, mul_right_comm, ih, show (1 : ℂ) - c - ((n + 1 : ℕ) : ℂ) = -c - n by
      push_cast; ring, ← h, pow_succ]
    ring

/-- `‖(c)ₙ‖ = ‖Γ(1 - c)‖ ‖1/Γ(1 - c - n)‖` when `Γ(1 - c) ≠ 0` (reflection form of the Pochhammer
  symbol). -/
theorem norm_poch_eq {c : ℂ} (hc : Gamma (1 - c) ≠ 0) (n : ℕ) :
    ‖poch c n‖ = ‖Gamma (1 - c)‖ * ‖(Gamma (1 - c - n))⁻¹‖ := by
  have h := congrArg norm (poch_mul_recip_Gamma_one_sub c n)
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv] at h
  rw [← h]
  field_simp [norm_ne_zero_iff.mpr hc]

/-- A majorant for the normalized Dixon terms, uniform for `x₁ ≤ Re(1-c) ≤ x₁ + 1`. -/
theorem exists_bound (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {x₁ : ℝ} (hx₁ : 2 ≤ x₁)
    (hx₁a : 2 ≤ a.re + x₁) (hx₁b : b.re - a.re / 2 < x₁) :
    ∃ u : ℕ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧ ∀ (n : ℕ) (c : ℂ),
      x₁ ≤ (1 - c).re → (1 - c).re ≤ x₁ + 1 →
        ‖s a b c n‖ ≤ ‖Gamma (1 - c)‖ * Real.exp (π * |c.im|) *
          Real.exp (π * (|c.im| + |a.im|) / 2) * u n := by
  obtain ⟨B, hB0, -, hBneg, hbound⟩ := exists_recip_Gamma_shift_bound x₁
  set coef := gaussHGCoeff a b (1 + a - b)
  set u : ℕ → ℝ := fun n => ‖coef n‖ * B (-(n : ℤ)) * (Real.Gamma (a.re + x₁ + n))⁻¹ with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => mul_nonneg (mul_nonneg (norm_nonneg _) (hB0 _))
    (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by positivity)).le)
  refine ⟨u, ?_, hu0, fun n c hc1 hc2 => ?_⟩
  · -- summability: `u_n = O(n^{2 Re b - 2} n^{1 - 2x₁ - Re a})`
    have hcoef := isBigO_gaussHGCoeff a b (1 + a - b) hb
    have hrat := isBigO_Gamma_ratio ((1 - x₁ : ℝ) : ℂ) 1 ((a.re + x₁ : ℝ) : ℂ) 1
    have hexp : (a + b - (1 + a - b) - 1).re +
        (((1 - x₁ : ℝ) : ℂ) + 1 - ((a.re + x₁ : ℝ) : ℂ) - 1).re < -1 := by
      simp; linarith
    refine summable_of_isBigO_nat (Real.summable_nat_rpow.mpr hexp) ?_
    have hbig := (hcoef.mul hrat).const_mul_left (π⁻¹ : ℂ)
    have hbig' := hbig.norm_left.trans (Asymptotics.IsBigO.of_bound 1 (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [one_mul, ← Real.rpow_add hn0]) : (fun n : ℕ =>
        ((n : ℝ) ^ (a + b - (1 + a - b) - 1).re *
          (n : ℝ) ^ (((1 - x₁ : ℝ) : ℂ) + 1 - ((a.re + x₁ : ℝ) : ℂ) - 1).re)) =O[atTop] _)
    refine hbig'.congr' ?_ (Filter.EventuallyEq.rfl)
    · obtain ⟨K₁, hK₁⟩ := exists_nat_ge (x₁ + 2)
      filter_upwards [eventually_ge_atTop K₁] with n hn
      have hn' : x₁ + 2 ≤ n := le_trans hK₁ (by exact_mod_cast hn)
      have hn1 : ¬ (2 : ℝ) ≤ x₁ + ((-(n : ℤ) : ℤ) : ℝ) := by push_cast; linarith
      have hn2 : x₁ + 1 + ((-(n : ℤ) : ℤ) : ℝ) ≤ -1 := by push_cast; linarith
      have hBn : B (-(n : ℤ)) = Real.Gamma (1 - x₁ + n) / π := by
        rw [hBneg _ hn1 hn2]; push_cast; ring_nf
      have hg1 : ‖Gamma ((n : ℂ) + ((1 - x₁ : ℝ) : ℂ))‖ = Real.Gamma (1 - x₁ + n) := by
        rw [show (n : ℂ) + ((1 - x₁ : ℝ) : ℂ) = ((1 - x₁ + n : ℝ) : ℂ) by push_cast; ring,
          Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.Gamma_pos_of_pos (by linarith))]
      have hg2 : ‖(Gamma ((n : ℂ) + ((a.re + x₁ : ℝ) : ℂ)))⁻¹‖ =
          (Real.Gamma (a.re + x₁ + n))⁻¹ := by
        rw [show (n : ℂ) + ((a.re + x₁ : ℝ) : ℂ) = ((a.re + x₁ + n : ℝ) : ℂ) by push_cast; ring,
          Complex.Gamma_ofReal, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.Gamma_pos_of_pos (by positivity))]
      have hone : Gamma ((n : ℂ) + 1) * (Gamma ((n : ℂ) + 1))⁻¹ = 1 :=
        mul_inv_cancel₀ (by rw [Complex.Gamma_nat_eq_factorial]; exact_mod_cast n.factorial_ne_zero)
      simp only [hu, hBn, norm_mul, norm_inv, hg1, hg2, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      have hone' : ‖Gamma ((n : ℂ) + 1)‖ * ‖(Gamma ((n : ℂ) + 1))⁻¹‖ = 1 := by
        rw [← norm_mul, hone, norm_one]
      rw [norm_inv] at hone'
      linear_combination (π⁻¹ * ‖coef n‖ * Real.Gamma (1 - x₁ + n) *
        (Real.Gamma (a.re + x₁ + n))⁻¹) * hone'
  -- the pointwise bound
  have hre1 : 0 < (1 - c).re := by linarith
  have hG1 : Gamma (1 - c) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre1
  have hpoch := norm_poch_eq hG1 n
  have hB := hbound (-(n : ℤ)) (1 - c) hc1 hc2
  rw [show (1 - c) + ((-(n : ℤ) : ℤ) : ℂ) = 1 - c - n by push_cast; ring,
    show (1 - c).im = -c.im by simp, abs_neg] at hB
  set z : ℂ := 1 + a - c + n with hz
  have hzre : z.re = a.re + (1 - c).re + n := by simp [hz]; ring
  have hzre2 : (2 : ℝ) ≤ a.re + x₁ + n := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hzim : |z.im| ≤ |c.im| + |a.im| := by
    have : z.im = a.im - c.im := by simp [hz]
    rw [this]; have := abs_sub a.im c.im; linarith [abs_sub_comm a.im c.im]
  have hGz : ‖(Gamma z)⁻¹‖ ≤ Real.exp (π * (|c.im| + |a.im|) / 2) *
      (Real.Gamma (a.re + x₁ + n))⁻¹ := by
    refine (norm_recip_Gamma_le_of_half_le (by rw [hzre]; linarith)).trans ?_
    have hmono : Real.Gamma (a.re + x₁ + n) ≤ Real.Gamma z.re :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn hzre2 (show (2 : ℝ) ≤ z.re by rw [hzre]; linarith)
        (by rw [hzre]; linarith)
    have hpos := Real.Gamma_pos_of_pos (show 0 < a.re + x₁ + n by linarith)
    calc Real.exp (π * |z.im| / 2) / Real.Gamma z.re
        ≤ Real.exp (π * (|c.im| + |a.im|) / 2) / Real.Gamma (a.re + x₁ + n) := by
          gcongr
      _ = _ := div_eq_mul_inv _ _
  calc ‖s a b c n‖ = ‖coef n‖ * ‖poch c n‖ * ‖(Gamma z)⁻¹‖ := by
        simp only [s, norm_mul, hz]; rfl
    _ ≤ ‖coef n‖ * (‖Gamma (1 - c)‖ * (Real.exp (π * |c.im|) * B (-(n : ℤ)))) *
          (Real.exp (π * (|c.im| + |a.im|) / 2) * (Real.Gamma (a.re + x₁ + n))⁻¹) := by
        rw [hpoch]
        have := hB0 (-(n : ℤ))
        gcongr
    _ = ‖Gamma (1 - c)‖ * Real.exp (π * |c.im|) * Real.exp (π * (|c.im| + |a.im|) / 2) * u n := by
        simp only [hu]; ring

/-- Holomorphy of the normalized Dixon series in a left half-plane. -/
theorem differentiableOn_Lh (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {X : ℝ} (hX : 3 ≤ X)
    (hXa : 3 ≤ a.re + X) (hXb : b.re - a.re / 2 + 1 < X) :
    DifferentiableOn ℂ (Lh a b) {c : ℂ | X < (1 - c).re} := by
  intro c₀ hc₀
  simp only [Set.mem_ofPred_eq] at hc₀
  set r : ℝ := min (1 / 2) (((1 - c₀).re - X) / 2) with hr
  have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
  have hr1 : r ≤ 1 / 2 := min_le_left _ _
  have hr2 : r ≤ ((1 - c₀).re - X) / 2 := min_le_right _ _
  set x₁ := (1 - c₀).re - r
  obtain ⟨u, hu, hu0, hbd⟩ := exists_bound (a := a) (b := b) hb (x₁ := x₁) (by linarith)
    (by linarith) (by linarith)
  have hball : DifferentiableOn ℂ (Lh a b) (Metric.ball c₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      (hu.mul_left (Real.Gamma (x₁ + 1) * Real.exp (π * (|c₀.im| + 1)) *
        Real.exp (π * ((|c₀.im| + 1) + |a.im|) / 2))) (fun n => ?_) Metric.isOpen_ball
      (fun n c hc => ?_)
    · have hpoly : Differentiable ℂ fun c : ℂ => poch c n :=
        (ascPochhammer ℂ n).differentiable
      exact (((hpoly.const_mul _).mul ((Complex.differentiable_one_div_Gamma).comp
        (by fun_prop))).differentiableOn)
    · have hdist : ‖c - c₀‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hc
      have hre : |c.re - c₀.re| < r :=
        lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (c - c₀)) hdist
      have him : |c.im - c₀.im| < r :=
        lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (c - c₀)) hdist
      have h1re : (1 - c).re = 1 - c.re := by simp
      have h1re0 : (1 - c₀).re = 1 - c₀.re := by simp
      have hc1 : x₁ ≤ (1 - c).re := by
        rw [h1re]; simp only [x₁, h1re0]; linarith [abs_lt.mp hre]
      have hc2 : (1 - c).re ≤ x₁ + 1 := by
        rw [h1re]; simp only [x₁, h1re0]; linarith [abs_lt.mp hre]
      refine (hbd n c hc1 hc2).trans ?_
      have hcim : |c.im| ≤ |c₀.im| + 1 := by
        have := abs_add_le c₀.im (c.im - c₀.im); simp at this
        linarith [abs_lt.mp him]
      have hG : ‖Gamma (1 - c)‖ ≤ Real.Gamma (x₁ + 1) := by
        have h := DLMF.Gamma.norm_Gamma_add_mul_I_le (x := (1 - c).re) (y := (1 - c).im)
          (by linarith)
        rw [show (((1 - c).re : ℝ) : ℂ) + I * (((1 - c).im : ℝ) : ℂ) = 1 - c by
          rw [mul_comm]; exact Complex.re_add_im _,
          abs_of_pos (Real.Gamma_pos_of_pos (by linarith))] at h
        exact h.trans (Real.Gamma_strictMonoOn_Ici.monotoneOn (show (2 : ℝ) ≤ (1 - c).re by
          linarith) (show (2 : ℝ) ≤ x₁ + 1 by linarith) hc2)
      have := hu0 n
      have hGx := (Real.Gamma_pos_of_pos (show 0 < x₁ + 1 by linarith)).le
      gcongr
  exact (hball.differentiableAt (Metric.ball_mem_nhds _ hr0)).differentiableWithinAt

/-- **Carlson's theorem in `c`**: `P(c) = K` on a left half-plane. -/
theorem exists_P_eq_K (ha : ∀ k : ℕ, 1 + a / 2 ≠ -k) (hb : ∀ k : ℕ, 1 + a - b ≠ -k) :
    ∃ X : ℝ, ∀ c : ℂ, c.re ≤ -X → P a b c = K a b := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (10 + 2 * |a.re| + 2 * |b.re|)
  have hm : (10 : ℝ) + 2 * |a.re| + 2 * |b.re| ≤ m₀ := hm₀
  have h1 := le_abs_self a.re
  have h2 := neg_abs_le a.re
  have h3 := le_abs_self b.re
  have h4 := neg_abs_le b.re
  have hreg : ∀ c : ℂ, c.re ≤ -(m₀ : ℝ) + 1 / 2 →
      0 < (1 + a / 2 - b - c).re ∧ 0 < (1 + a / 2 - c).re ∧ 0 < (1 + a - b - c).re := by
    intro c hc
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith
  have hnz : ∀ c : ℂ, c.re ≤ -(m₀ : ℝ) + 1 / 2 → 1 + a / 2 - c ≠ 0 ∧ 1 + a - b - c ≠ 0 := by
    intro c hc
    obtain ⟨-, h5, h6⟩ := hreg c hc
    exact ⟨fun h => by rw [h] at h5; simp at h5, fun h => by rw [h] at h6; simp at h6⟩
  set F : ℂ → ℂ := fun w => P a b (-(m₀ : ℂ) - w) - K a b with hF
  -- holomorphy
  have hLd := differentiableOn_Lh (a := a) (b := b) hb (X := m₀ + 1 / 2) (by linarith)
    (by linarith) (by linarith)
  have hFd : DifferentiableOn ℂ F {w : ℂ | -(1 / 2) < w.re} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    have hc : (-(m₀ : ℂ) - w).re ≤ -(m₀ : ℝ) + 1 / 2 := by simp; linarith
    obtain ⟨-, h5, h6⟩ := hreg _ hc
    apply DifferentiableAt.differentiableWithinAt
    have hL : DifferentiableAt ℂ (fun w => Lh a b (-(m₀ : ℂ) - w)) w := by
      have hU : {c : ℂ | (m₀ : ℝ) + 1 / 2 < (1 - c).re} ∈ 𝓝 (-(m₀ : ℂ) - w) :=
        (isOpen_lt continuous_const (Complex.continuous_re.comp
          (continuous_const.sub continuous_id))).mem_nhds (by simp; linarith)
      exact (hLd.differentiableAt hU).comp w ((differentiableAt_const _).sub differentiableAt_id)
    have hG1 : DifferentiableAt ℂ (fun w => Gamma (1 + a / 2 - (-(m₀ : ℂ) - w))) w :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at h5; simp at h5; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp w
        (by fun_prop)
    have hG2 : DifferentiableAt ℂ (fun w => Gamma (1 + a - b - (-(m₀ : ℂ) - w))) w :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at h6; simp at h6; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp w
        (by fun_prop)
    have hG3 : DifferentiableAt ℂ (fun w => (Gamma (1 + a / 2 - b - (-(m₀ : ℂ) - w)))⁻¹) w :=
      (Complex.differentiable_one_div_Gamma _).comp w (by fun_prop)
    exact (((hL.mul hG1).mul hG2).mul hG3).sub_const _
  -- periodicity
  have hper : ∀ w : ℂ, 0 ≤ w.re → F (w + 1) = F w := by
    intro w hw
    set c : ℂ := -(m₀ : ℂ) - w with hcdef
    have hc : c.re ≤ -(m₀ : ℝ) + 1 / 2 := by simp [hcdef]; linarith
    have hc' : (c - 1).re ≤ -(m₀ : ℝ) + 1 / 2 := by simp [hcdef]; linarith
    obtain ⟨hcv, -, -⟩ := hreg c hc
    obtain ⟨hcv', -, -⟩ := hreg (c - 1) hc'
    obtain ⟨hs1, hH⟩ := summable_s_and_tendsto_H hb hcv
    obtain ⟨hs2, -⟩ := summable_s_and_tendsto_H hb hcv'
    obtain ⟨hn1, hn2⟩ := hnz c hc
    simp only [hF]
    rw [show -(m₀ : ℂ) - (w + 1) = c - 1 by rw [hcdef]; ring, P_sub_one hb hs1 hs2 hH hn1 hn2]
  -- the value at `0`: terminating Dixon
  have hF0 : F 0 = 0 := by
    simp only [hF, sub_zero]
    rw [P_neg_nat ha hb m₀, sub_self]
  -- the strip bound
  obtain ⟨u, hu, hu0, hbd⟩ := exists_bound (a := a) (b := b) hb (x₁ := 1 + m₀) (by linarith)
    (by linarith) (by linarith)
  set S := ∑' n : ℕ, u n with hS
  have hS0 : 0 ≤ S := tsum_nonneg hu0
  obtain ⟨C₁, K₁, hC₁, hb₁⟩ := exists_norm_Gamma_add_le_strip (1 + (m₀ : ℂ))
    (X₁ := 1 + m₀) (X₂ := 2 + m₀) (by linarith)
  obtain ⟨C₂, K₂, hC₂, hb₂⟩ := exists_norm_Gamma_add_le_strip (1 + a / 2 + m₀)
    (X₁ := 1 + a.re / 2 + m₀) (X₂ := 2 + a.re / 2 + m₀) (by linarith)
  obtain ⟨C₃, K₃, hC₃, hb₃⟩ := exists_norm_Gamma_add_le_strip (1 + a - b + m₀)
    (X₁ := 1 + a.re - b.re + m₀) (X₂ := 2 + a.re - b.re + m₀) (by linarith)
  obtain ⟨C₄, K₄, hC₄, hb₄⟩ := exists_norm_recip_Gamma_add_le_strip (1 + a / 2 - b + m₀)
    (|1 + a.re / 2 - b.re + m₀| + 1)
  set A : ℝ := C₁ * C₂ * C₃ * C₄ * S * Real.exp (π * |a.im| / 2) with hA
  have hstrip : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖F w‖ ≤ (A + ‖K a b‖) * (1 + |w.im|) ^ (K₁ + K₂ + K₃ + K₄) *
        Real.exp (π / 2 * |w.im|) := by
    intro w hw0 hw1
    set c : ℂ := -(m₀ : ℂ) - w with hcdef
    set y := w.im
    have hcim : |c.im| = |y| := by simp [hcdef, y]
    have e1 : 1 - c = w + (1 + (m₀ : ℂ)) := by rw [hcdef]; ring
    have e2 : 1 + a / 2 - c = w + (1 + a / 2 + m₀) := by rw [hcdef]; ring
    have e3 : 1 + a - b - c = w + (1 + a - b + m₀) := by rw [hcdef]; ring
    have e4 : 1 + a / 2 - b - c = w + (1 + a / 2 - b + m₀) := by rw [hcdef]; ring
    have hx1 : (1 + (m₀ : ℝ)) ≤ (1 - c).re := by rw [e1]; simp; linarith
    have hx2 : (1 - c).re ≤ 1 + m₀ + 1 := by rw [e1]; simp; linarith
    have hL : ‖Lh a b c‖ ≤ ‖Gamma (1 - c)‖ * Real.exp (π * |y|) *
        Real.exp (π * (|y| + |a.im|) / 2) * S := by
      rw [← hcim]
      exact tsum_of_norm_bounded (hu.hasSum.mul_left _) fun n => hbd n c hx1 hx2
    have g1 : ‖Gamma (1 - c)‖ ≤ C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2) := by
      rw [e1]; exact hb₁ w (by simp; linarith) (by simp; linarith)
    have g2 : ‖Gamma (1 + a / 2 - c)‖ ≤ C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2) := by
      rw [e2]; exact hb₂ w (by simp; linarith) (by simp; linarith)
    have g3 : ‖Gamma (1 + a - b - c)‖ ≤ C₃ * (1 + |y|) ^ K₃ * Real.exp (-(π * |y|) / 2) := by
      rw [e3]; exact hb₃ w (by simp; linarith) (by simp; linarith)
    have g4 : ‖(Gamma (1 + a / 2 - b - c))⁻¹‖ ≤ C₄ * (1 + |y|) ^ K₄ * Real.exp (π * |y| / 2) := by
      rw [e4]
      refine hb₄ w ?_
      rw [abs_le]
      have := le_abs_self (1 + a.re / 2 - b.re + m₀)
      have := neg_abs_le (1 + a.re / 2 - b.re + m₀)
      constructor <;> simp <;> linarith
    have hP : ‖P a b c‖ ≤ A * (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) := by
      simp only [P, norm_mul]
      have hE : Real.exp (-(π * |y|) / 2) * Real.exp (π * |y|) * Real.exp (π * (|y| + |a.im|) / 2) *
          Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2) =
          Real.exp (π / 2 * |y|) * Real.exp (π * |a.im| / 2) := by
        simp only [← Real.exp_add]; ring_nf
      calc ‖Lh a b c‖ * ‖Gamma (1 + a / 2 - c)‖ * ‖Gamma (1 + a - b - c)‖ *
            ‖(Gamma (1 + a / 2 - b - c))⁻¹‖
          ≤ ((C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2)) * Real.exp (π * |y|) *
              Real.exp (π * (|y| + |a.im|) / 2) * S) *
              (C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2)) *
              (C₃ * (1 + |y|) ^ K₃ * Real.exp (-(π * |y|) / 2)) *
              (C₄ * (1 + |y|) ^ K₄ * Real.exp (π * |y| / 2)) := by
            gcongr
            exact hL.trans (by gcongr)
        _ = C₁ * C₂ * C₃ * C₄ * S * ((1 + |y|) ^ K₁ * (1 + |y|) ^ K₂ * (1 + |y|) ^ K₃ *
              (1 + |y|) ^ K₄) * (Real.exp (-(π * |y|) / 2) * Real.exp (π * |y|) *
              Real.exp (π * (|y| + |a.im|) / 2) * Real.exp (-(π * |y|) / 2) *
              Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2)) := by ring
        _ = A * (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) := by
            rw [hE, hA, pow_add, pow_add, pow_add]; ring
    have hpos : 1 ≤ (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [abs_nonneg y]))
        (Real.one_le_exp (by positivity))
    calc ‖F w‖ ≤ ‖P a b c‖ + ‖K a b‖ := norm_sub_le _ _
      _ ≤ A * (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) +
            ‖K a b‖ * ((1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|)) := by
          gcongr
          exact le_mul_of_one_le_right (norm_nonneg _) hpos
      _ = (A + ‖K a b‖) * (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) := by ring
  have hzero := eq_zero_of_periodic_of_bound (by norm_num : (0 : ℝ) < 1 / 2) hFd hper
    (σ := π / 2) (by linarith [Real.pi_pos]) hstrip hF0
  refine ⟨m₀, fun c hc => ?_⟩
  have h := hzero (-(m₀ : ℂ) - c) (by simp; linarith)
  simp only [hF, sub_eq_zero] at h
  simpa using h

/-- The normalized right-hand side of Dixon's formula. -/
def Rh (a b c : ℂ) : ℂ :=
  K a b * Gamma (1 + a / 2 - b - c) * (Gamma (1 + a / 2 - c))⁻¹ * (Gamma (1 + a - b - c))⁻¹

/-- The normalized right-hand side of Dixon's formula satisfies the same recurrence in `c` as the
  series. -/
theorem Rh_recurrence {c : ℂ} (hc : 1 + a / 2 - b - c ≠ 0) :
    (1 + a / 2 - b - c) * Rh a b c = (1 + a / 2 - c) * (1 + a - b - c) * Rh a b (c - 1) := by
  have g1 : Gamma (1 + a / 2 - b - (c - 1)) = (1 + a / 2 - b - c) * Gamma (1 + a / 2 - b - c) := by
    rw [show 1 + a / 2 - b - (c - 1) = (1 + a / 2 - b - c) + 1 by ring,
      Complex.Gamma_add_one _ hc]
  have g2 : (1 + a / 2 - c) * (Gamma (1 + a / 2 - (c - 1)))⁻¹ = (Gamma (1 + a / 2 - c))⁻¹ := by
    have h := mul_recip_Gamma_add_one (1 + a / 2 - c)
    rwa [show 1 + a / 2 - c + 1 = 1 + a / 2 - (c - 1) by ring] at h
  have g3 : (1 + a - b - c) * (Gamma (1 + a - b - (c - 1)))⁻¹ = (Gamma (1 + a - b - c))⁻¹ := by
    have h := mul_recip_Gamma_add_one (1 + a - b - c)
    rwa [show 1 + a - b - c + 1 = 1 + a - b - (c - 1) by ring] at h
  simp only [Rh]
  rw [g1, ← g2, ← g3]
  ring

end DixonAux

end CarlsonApplications

open DixonAux in
/-- Dixon's well-poised `₃F₂(1)` evaluation (AAR Theorem 3.4.1). -/
@[dlmf 16.4.E4]
theorem dixon_sum {a b c : ℂ}
    (h : 0 < (1 + a / 2 - b - c).re)
    (ha : ∀ k : ℕ, (1 + a / 2 : ℂ) ≠ -k)
    (hb : ∀ k : ℕ, (1 + a - b : ℂ) ≠ -k)
    (hc : ∀ k : ℕ, (1 + a - c : ℂ) ≠ -k) :
    (∑' n : ℕ, poch a n * poch b n * poch c n /
        (poch (1 + a - b) n * poch (1 + a - c) n *
          (n.factorial : ℂ))) =
      Gamma (1 + a / 2) * Gamma (1 + a - b) * Gamma (1 + a - c) *
        Gamma (1 + a / 2 - b - c) /
        (Gamma (1 + a) * Gamma (1 + a / 2 - b) * Gamma (1 + a / 2 - c) *
          Gamma (1 + a - b - c)) := by
  -- `Lh = Rh` on a left half-plane, by Carlson's theorem
  obtain ⟨X, hX⟩ := exists_P_eq_K ha hb
  have hfar : ∀ c' : ℂ, c'.re ≤ -(max X (|a.re| + |b.re| + 2)) → Lh a b c' = Rh a b c' := by
    intro c' hc'
    have hP := hX c' (by linarith [le_max_left X (|a.re| + |b.re| + 2)])
    have hm := le_max_right X (|a.re| + |b.re| + 2)
    have h1 := le_abs_self a.re
    have h2 := neg_abs_le a.re
    have h3 := le_abs_self b.re
    have h4 := neg_abs_le b.re
    have r1 : 0 < (1 + a / 2 - c').re := by simp; linarith
    have r2 : 0 < (1 + a - b - c').re := by simp; linarith
    have r3 : 0 < (1 + a / 2 - b - c').re := by simp; linarith
    have n1 := Complex.Gamma_ne_zero_of_re_pos r1
    have n2 := Complex.Gamma_ne_zero_of_re_pos r2
    have n3 := Complex.Gamma_ne_zero_of_re_pos r3
    simp only [P] at hP
    simp only [Rh]
    rw [← hP]
    have i1 := mul_inv_cancel₀ n1
    have i2 := mul_inv_cancel₀ n2
    have i3 := inv_mul_cancel₀ n3
    linear_combination (-(Lh a b c' * (Gamma (1 + a - b - c') * (Gamma (1 + a - b - c'))⁻¹) *
      ((Gamma (1 + a / 2 - b - c'))⁻¹ * Gamma (1 + a / 2 - b - c')))) * i1 +
      (-(Lh a b c' * ((Gamma (1 + a / 2 - b - c'))⁻¹ * Gamma (1 + a / 2 - b - c')))) * i2 +
      (-Lh a b c') * i3
  -- climb back to `c` with the recurrence
  set E : ℂ → ℂ := fun c' => Lh a b c' - Rh a b c' with hE
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (c.re + max X (|a.re| + |b.re| + 2))
  have hrec : ∀ c' : ℂ, 0 < (1 + a / 2 - b - c').re → E (c' - 1) = 0 → E c' = 0 := by
    intro c' hc' h0
    have hc'1 : 0 < (1 + a / 2 - b - (c' - 1)).re := by simp at hc' ⊢; linarith
    obtain ⟨hs1, hH⟩ := summable_s_and_tendsto_H hb hc'
    obtain ⟨hs2, -⟩ := summable_s_and_tendsto_H hb hc'1
    have hne : 1 + a / 2 - b - c' ≠ 0 := fun h => by rw [h] at hc'; simp at hc'
    have hL := recurrence hb hs1 hs2 hH
    have hR := Rh_recurrence (a := a) (b := b) hne
    have : (1 + a / 2 - b - c') * E c' = 0 := by
      simp only [hE] at h0 ⊢
      rw [mul_sub, hL, hR, ← mul_sub, h0, mul_zero]
    exact (mul_eq_zero.mp this).resolve_left hne
  have hclimb : ∀ i : ℕ, E (c - ((k₀ - i : ℕ) : ℂ)) = 0 := by
    intro i
    induction i with
    | zero =>
      simp only [hE, Nat.sub_zero, sub_eq_zero]
      exact hfar _ (by simp; linarith)
    | succ i ih =>
      rcases le_or_gt (i + 1) k₀ with hi | hi
      · have hk : (k₀ - i : ℕ) = (k₀ - (i + 1) : ℕ) + 1 := by omega
        rw [hk, Nat.cast_add, Nat.cast_one, ← sub_sub] at ih
        refine hrec _ ?_ ih
        have : (0 : ℝ) ≤ ((k₀ - (i + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
        have h' := h
        simp at h' ⊢
        linarith
      · rwa [show k₀ - (i + 1) = k₀ - i by omega]
  have hEc : E c = 0 := by simpa using hclimb k₀
  have hLR : Lh a b c = Rh a b c := sub_eq_zero.mp hEc
  -- back to the statement
  have hG : Gamma (1 + a - c) ≠ 0 := Complex.Gamma_ne_zero hc
  have hterm : ∀ n : ℕ, poch a n * poch b n * poch c n /
      (poch (1 + a - b) n * poch (1 + a - c) n * (n.factorial : ℂ)) =
      Gamma (1 + a - c) * s a b c n := by
    intro n
    have hp : poch (1 + a - c) n ≠ 0 := poch_ne_zero_of_not_neg_nat hc n
    have hpb : poch (1 + a - b) n ≠ 0 := poch_ne_zero_of_not_neg_nat hb n
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hGn : Gamma (1 + a - c + n) = Gamma (1 + a - c) * poch (1 + a - c) n := by
      have h := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (1 + a - c) hc
      rw [div_eq_iff hG] at h
      rw [h, poch, mul_comm]
    simp only [s, gaussHGCoeff, hGn]
    field_simp
  simp_rw [hterm]
  rw [tsum_mul_left]
  change Gamma (1 + a - c) * Lh a b c = _
  rw [hLR]
  simp only [Rh, K, div_eq_mul_inv, mul_inv]
  ring

end DLMF.Hypergeometric
end
end
