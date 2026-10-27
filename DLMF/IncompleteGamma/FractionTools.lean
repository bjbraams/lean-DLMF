/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Statistical.ContinuedFraction
public import DLMF.Confluent.ContinuedFractions
public import DLMF.IncompleteGamma.Basic
public import TauCeti.Analysis.Complex.Conformal.Vitali

/-!
# Tools for the continued fractions of Chapter 8

* `incGF_cfTail_eq`: when no partial numerator `a_k`, `k ≥ 1`, vanishes, the project's finite
  continued fraction `cfTail a b 0 N` (which freezes at a vanishing numerator) is the Mathlib
  convergent of `GenContFract.cfConv_ofFun 0 a b`.
* `incGF_hasContinuedFraction_iff`: the corresponding description of `HasContinuedFraction`.
* `incGF_pade_lt`, `incGF_lt_pade`: the even and odd convergents of Legendre's fraction for
  `x^{1-a} e^x Γ(a,x)` bracket it strictly for real `a < 1`, `x > 0` (used for DLMF 8.10.5).
* `incGF_gammaStar_tendsto`: convergence of the fraction 8.9.1 for `Γ(1+a) e^z γ*(a,z) =
  M(1,1+a,z)`, from the Kummer backward solution `M(m, a+2m, z)`, `M(m+1, a+2m+1, z)` scaled by
  `1/∏_{j<k}(a+1+j)` and the ratio criterion `GenContFract.cfConv_tendsto_of_ratio`.
* `incGF_tendsto_of_slitPlane` (**Stieltjes–Vitali**): a locally bounded sequence of holomorphic
  functions on `ℂ ∖ (-∞, 0]` converging on `(0, ∞)` to a holomorphic function converges to it on
  the whole slit plane (TauCeti's `TauCeti.vitali_of_tendsto` and the identity theorem).
* `incGF_LF_tendsto`, `incGF_formA_tendsto`, `incGF_formB_tendsto`: Legendre's fraction for
  `Γ(a,z)` (DLMF 8.9.2) converges on the whole slit plane for real `a < 1`. Local boundedness and
  nonvanishing denominators come from the S-fraction value region
  `GenContFract.cfConv_sfrac_bound`; the real case is
  `DLMF.Statistical.tendsto_gammaIncContFract`.
-/

@[expose] public noncomputable section

open Complex Filter Finset GenContFract
open scoped Topology

namespace DLMF.Confluent

/-- Without vanishing partial numerators the project's continuants are Mathlib's. -/
theorem incGF_cfContinuants_eq {a b : ℕ → ℂ} (ha : ∀ k, 1 ≤ k → a k ≠ 0) (n : ℕ) :
    DLMF.cfContinuants a b 0 n =
      ((cfConv_ofFun 0 a b).nums n, (cfConv_ofFun 0 a b).dens n, false) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [DLMF.cfContinuants]; rfl
    · simp [DLMF.cfContinuants, cfConv_nums_one, cfConv_dens_one]
    · have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have han : a (n + 1) ≠ 0 := ha (n + 1) (by omega)
      rw [DLMF.cfContinuants, h1, h0, cfConv_nums_step, cfConv_dens_step]
      simp [han, GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen]

/-- `cfTail a b 0 N` is the `N`-th Mathlib convergent when no `a_k` (`k ≥ 1`) vanishes. -/
theorem incGF_cfTail_eq {a b : ℕ → ℂ} (ha : ∀ k, 1 ≤ k → a k ≠ 0) (N : ℕ) :
    DLMF.cfTail a b 0 N = (cfConv_ofFun 0 a b).convs N := by
  simp only [DLMF.cfTail, incGF_cfContinuants_eq ha]
  rfl

/-- `HasContinuedFraction` in terms of Mathlib convergents. -/
theorem incGF_hasContinuedFraction_iff {a b : ℕ → ℂ} (ha : ∀ k, 1 ≤ k → a k ≠ 0) (v : ℂ) :
    DLMF.HasContinuedFraction a b v ↔
      Tendsto (cfConv_ofFun 0 a b).convs atTop (𝓝 v) := by
  unfold DLMF.HasContinuedFraction
  have : DLMF.cfTail a b 0 = fun N => (cfConv_ofFun 0 a b).convs N :=
    funext (incGF_cfTail_eq ha)
  rw [this]

/-- A continued fraction with real elements: its finite values are the real convergents. -/
theorem incGF_cfTail_ofReal {A B : ℕ → ℂ} {a b : ℕ → ℝ} (hA : ∀ k, A k = a k)
    (hB : ∀ k, B k = b k) (ha : ∀ k, 1 ≤ k → a k ≠ 0) (N : ℕ) :
    DLMF.cfTail A B 0 N = ((cfConv_ofFun 0 a b).convs N : ℂ) := by
  have hA' : A = fun k => Complex.ofRealHom (a k) := funext hA
  have hB' : B = fun k => Complex.ofRealHom (b k) := funext hB
  rw [incGF_cfTail_eq (fun k hk => by rw [hA k]; exact_mod_cast ha k hk), hA', hB',
    show (0 : ℂ) = Complex.ofRealHom 0 from (map_zero _).symm, cfConv_convs_map]
  rfl

/-! ### Legendre's fraction for `Γ(a,x)` with first numerator `x` -/

/-- Partial numerators `x, 1-a, 1, 2-a, 2, …` of the fraction for `x^{1-a} e^x Γ(a,x)`. -/
def incGF_padeNum (a x : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then x else DLMF.Statistical.gammaIncCFNum a x k

/-- The Padé numerators are positive for `a < 1`, `x > 0`. -/
theorem incGF_padeNum_pos {a x : ℝ} (ha : a < 1) (hx : 0 < x) (k : ℕ) :
    0 < incGF_padeNum a x k := by
  unfold incGF_padeNum
  split_ifs
  · exact hx
  · exact DLMF.Statistical.gammaIncCFNum_pos ha hx k

/-- The value `x w₁ / w₀` of the fraction is `x^{1-a} e^x Γ(a,x)`. -/
theorem incGF_pade_value {a x : ℝ} (hx : 0 < x) :
    0 + incGF_padeNum a x 0 * DLMF.Statistical.gammaIncCFTail a x 1 /
        DLMF.Statistical.gammaIncCFTail a x 0 =
      x ^ (1 - a) * Real.exp x * (upperIncGamma a x).re := by
  rw [DLMF.Statistical.upperIncGamma_eq_gammaTail a hx, ofReal_re]
  have h1 := DLMF.Statistical.gammaIncCFTail_even a x 0
  simp only [mul_zero, zero_add] at h1
  rw [h1]
  simp only [incGF_padeNum, DLMF.Statistical.gammaIncCFTail, ite_true]
  have e1 : x ^ (1 - a) * x ^ a = x := by
    rw [← Real.rpow_add hx]; simp
  have e2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  simp only [CharP.cast_eq_zero, sub_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add]
  linear_combination (-(DLMF.Statistical.gammaTail x (a - 1) 0)) *
    (Real.exp x * Real.exp (-x)) * e1 - x * DLMF.Statistical.gammaTail x (a - 1) 0 * e2

/-- The backward recurrence of the fraction with first numerator `x`. -/
theorem incGF_pade_rec {a x : ℝ} (hx : 0 < x) (k : ℕ) :
    DLMF.Statistical.gammaIncCFTail a x k =
      DLMF.Statistical.gammaIncCFDen x k * DLMF.Statistical.gammaIncCFTail a x (k + 1) +
        incGF_padeNum a x (k + 1) * DLMF.Statistical.gammaIncCFTail a x (k + 2) := by
  rw [DLMF.Statistical.gammaIncCFTail_rec hx k]
  simp [incGF_padeNum]

/-- Even convergents lie strictly below `x^{1-a} e^x Γ(a,x)`. -/
theorem incGF_pade_lt {a x : ℝ} (ha : a < 1) (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    (cfConv_ofFun 0 (incGF_padeNum a x) (DLMF.Statistical.gammaIncCFDen x)).convs (2 * n) <
      x ^ (1 - a) * Real.exp x * (upperIncGamma a x).re := by
  rw [← incGF_pade_value (a := a) hx]
  exact cfConv_convs_lt_of_pos (incGF_padeNum_pos ha hx)
    (DLMF.Statistical.gammaIncCFDen_pos hx) (DLMF.Statistical.gammaIncCFTail_pos hx)
    (incGF_pade_rec hx) hn

/-- Odd convergents lie strictly above `x^{1-a} e^x Γ(a,x)`. -/
theorem incGF_lt_pade {a x : ℝ} (ha : a < 1) (hx : 0 < x) (n : ℕ) :
    x ^ (1 - a) * Real.exp x * (upperIncGamma a x).re <
      (cfConv_ofFun 0 (incGF_padeNum a x) (DLMF.Statistical.gammaIncCFDen x)).convs
        (2 * n + 1) := by
  rw [← incGF_pade_value (a := a) hx]
  exact cfConv_lt_convs_of_pos (incGF_padeNum_pos ha hx)
    (DLMF.Statistical.gammaIncCFDen_pos hx) (DLMF.Statistical.gammaIncCFTail_pos hx)
    (incGF_pade_rec hx) n

/-! ### The fraction 8.9.1 -/

/-- If `a₁ = 0` the project's finite continued fraction freezes at `a₀/b₀`. -/
theorem incGF_cfContinuants_freeze {a b : ℕ → ℂ} (h1 : a 1 = 0) (n : ℕ) :
    DLMF.cfContinuants a b 0 (n + 2) = (a 0, b 0, true) := by
  induction n with
  | zero => simp [DLMF.cfContinuants, h1]
  | succ n ih =>
    rw [DLMF.cfContinuants, ih]
    simp

/-- A vanishing first partial numerator freezes the finite continued fractions. -/
theorem incGF_cfTail_freeze {a b : ℕ → ℂ} (h1 : a 1 = 0) {n : ℕ} (hn : 1 ≤ n) :
    DLMF.cfTail a b 0 n = a 0 / b 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | m
  · simp [DLMF.cfTail, DLMF.cfContinuants]
  · simp only [DLMF.cfTail, show m + 1 + 1 = m + 2 by ring, incGF_cfContinuants_freeze h1]

/-- The product `∏_{j<k} (a+1+j)`. -/
def incGF_P (a : ℂ) (k : ℕ) : ℂ := ∏ j ∈ range k, (a + 1 + j)

/-- The partial numerators `incGF_P a k` are nonzero away from negative integers. -/
theorem incGF_P_ne_zero {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(n + 1)) (k : ℕ) : incGF_P a k ≠ 0 :=
  prod_ne_zero_iff.mpr fun j _ h => ha j (by linear_combination h)

/-- The backward solution of the fraction 8.9.1. -/
def incGF_w (a z : ℂ) (k : ℕ) : ℂ :=
  if k = 0 then 1 else kumCF_F 0 a z k / incGF_P a (k - 1)

/-- The partial numerators of the fraction 8.9.1 do not vanish. -/
theorem incGF_gammaStar_A_ne {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -(n + 1)) (hz : z ≠ 0)
    {A : ℕ → ℂ} (hA0 : A 0 = 1) (hA1 : A 1 = -z) (hAo : ∀ m ≥ 1, A (2 * m + 1) = -(m + a) * z)
    (hAe : ∀ m ≥ 1, A (2 * m) = m * z) (k : ℕ) : A k ≠ 0 := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rcases m with _ | m
    · simp [hA0]
    · rw [hAe (m + 1) (by omega)]; exact mul_ne_zero (by exact_mod_cast m.succ_ne_zero) hz
  · rcases m with _ | m
    · simp [hA1, hz]
    · rw [hAo (m + 1) (by omega)]
      refine mul_ne_zero (neg_ne_zero.mpr fun h => ha m ?_) hz
      push_cast at h; linear_combination h

/-- Convergence of the fraction 8.9.1, for sequences with the prescribed elements. -/
theorem incGF_gammaStar_tendsto {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -(n + 1)) (hz : z ≠ 0)
    {A B : ℕ → ℂ} (hA0 : A 0 = 1) (hA1 : A 1 = -z) (hAo : ∀ m ≥ 1, A (2 * m + 1) = -(m + a) * z)
    (hAe : ∀ m ≥ 1, A (2 * m) = m * z) (hB0 : B 0 = 1) (hB : ∀ k ≥ 1, B k = a + k) :
    Tendsto (cfConv_ofFun 0 A B).convs atTop (𝓝 (kummerM 1 (a + 1) z)) := by
  have hP := incGF_P_ne_zero ha
  have hPs : ∀ k, incGF_P a (k + 1) = incGF_P a k * (a + 1 + k) := fun k => prod_range_succ _ _
  have hak : ∀ k : ℕ, 1 ≤ k → a + k ≠ 0 := fun k hk h => ha (k - 1) (by
    have : ((k - 1 : ℕ) : ℂ) = k - 1 := by rw [Nat.cast_sub hk]; simp
    rw [this]; linear_combination h)
  -- the elements in Kummer form
  have hcoefA : ∀ k ≥ 1, A (k + 1) =
      kummerMContFractCoeff 0 a k * z * ((a + k) * (a + k + 1)) := by
    intro k hk
    have h1 := hak k hk
    have h2 := hak (k + 1) (by omega)
    push_cast at h2
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [hAo m (by omega), kumCF_coeff_even]
      push_cast at h1 h2 ⊢
      have h2' : a + 2 * (m : ℂ) + 1 ≠ 0 := by rw [add_assoc]; exact h2
      rw [eq_comm, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero h1 h2')]
      ring
    · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, hAe (m + 1) (by omega), kumCF_coeff_odd]
      push_cast at h1 h2 ⊢
      have e : a + (2 * (m : ℂ) + 1) = a + 1 + 2 * m := by ring
      rw [e] at h1 ⊢
      have h2' : a + 1 + 2 * (m : ℂ) + 1 ≠ 0 := by
        rw [show a + 1 + 2 * (m : ℂ) + 1 = a + (2 * m + 1 + 1) by ring]; exact h2
      rw [eq_comm, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero h1 h2')]
      ring
  have hF0 : ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, a + k ≠ -j := by
    intro k hk j h; apply hak (k + j) (by omega); push_cast; linear_combination h
  -- the recurrence
  have hw : ∀ k, incGF_w a z k = B k * incGF_w a z (k + 1) + A (k + 1) * incGF_w a z (k + 2) := by
    intro k
    rcases k with _ | k
    · simp only [incGF_w, ↓reduceIte, hB0, one_mul, zero_add, hA1, Nat.add_one_ne_zero,
        show (2 : ℕ) - 1 = 1 from rfl, Nat.sub_self]
      have h1 := kumCF_one_sub (d := a) (fun j h => ha j (by linear_combination h)) z
      have e1 : kumCF_F 0 a z 1 = kummerM 1 (a + 1) z := by
        simp [kumCF_F]
      have e2 : kumCF_F 0 a z 2 = kummerM 1 (a + 2) z := by
        simp [kumCF_F]
      rw [e1, e2]
      simp only [incGF_P, range_zero, prod_empty, div_one, range_one, prod_singleton,
        Nat.cast_zero, add_zero]
      have := hak 1 le_rfl
      push_cast at this
      field_simp
      linear_combination -h1
    · have hrec := kumCF_F_rec' (a := 0) (b := a) z (k + 1) (hF0 (k + 1) (by omega))
      rw [hB (k + 1) (by omega), hcoefA (k + 1) (by omega)]
      simp only [incGF_w, Nat.add_one_ne_zero, ↓reduceIte, show k + 1 + 1 - 1 = k + 1 by omega,
        show k + 1 + 2 - 1 = k + 2 by omega, Nat.add_sub_cancel]
      rw [hPs (k + 1), hPs k]
      have := hP k
      have h1 := hak (k + 1) (by omega)
      have h2 := hak (k + 2) (by omega)
      push_cast at h1 h2 ⊢
      rw [show k + 1 + 2 = k + 3 by ring] at hrec ⊢
      rw [show k + 1 + 1 = k + 2 by ring] at hrec ⊢
      rw [hrec]
      have e1 : a + 1 + (k : ℂ) = a + (k + 1) := by ring
      have e2 : a + 1 + ((k : ℂ) + 1) = a + (k + 1) + 1 := by ring
      rw [e1, e2]
      have h2' : a + ((k : ℂ) + 1) + 1 ≠ 0 := by rw [show a + ((k : ℂ) + 1) + 1 = a + (k + 2) by ring]; exact h2
      field_simp
  obtain ⟨N, hN⟩ := eventually_atTop.mp (kumCF_eventually_ratio 0 a z)
  have hwN : ∀ k ≥ N + 1, incGF_w a z k ≠ 0 := by
    intro k hk
    simp only [incGF_w, show k ≠ 0 by omega, ↓reduceIte]
    exact div_ne_zero (hN k (by omega)).1 (hP _)
  have hA : ∀ k, A k ≠ 0 := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rcases m with _ | m
      · simp [hA0]
      · rw [hAe (m + 1) (by omega)]; exact mul_ne_zero (by exact_mod_cast m.succ_ne_zero) hz
    · rcases m with _ | m
      · simp [hA1, hz]
      · rw [hAo (m + 1) (by omega)]
        refine mul_ne_zero (neg_ne_zero.mpr fun h => ha m ?_) hz
        push_cast at h; linear_combination h
  have hrat : ∀ k ≥ N + 1, (3 : ℝ) * ‖A (k + 1) * incGF_w a z (k + 2)‖ ≤ ‖incGF_w a z k‖ := by
    intro k hk
    have h := (hN k (by omega)).2
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hcoefA (k' + 1) (by omega)]
    simp only [incGF_w, Nat.add_one_ne_zero, ↓reduceIte, show k' + 1 + 2 - 1 = k' + 2 by omega,
      Nat.add_sub_cancel]
    rw [hPs (k' + 1), hPs k']
    have h1 := hak (k' + 1) (by omega)
    have h2 := hak (k' + 2) (by omega)
    have hp := hP k'
    have e : kummerMContFractCoeff 0 a (k' + 1) * z * ((a + ↑(k' + 1)) * (a + ↑(k' + 1) + 1)) *
        (kumCF_F 0 a z (k' + 1 + 2) / (incGF_P a k' * (a + 1 + k') * (a + 1 + (k' + 1 : ℕ)))) =
        kummerMContFractCoeff 0 a (k' + 1) * z * kumCF_F 0 a z (k' + 1 + 2) / incGF_P a k' := by
      push_cast at h1 h2 ⊢
      have e1 : a + 1 + (k' : ℂ) = a + (k' + 1) := by ring
      have e2 : a + 1 + ((k' : ℂ) + 1) = a + (k' + 1) + 1 := by ring
      rw [e1, e2]
      have h2' : a + ((k' : ℂ) + 1) + 1 ≠ 0 := by
        rw [show a + ((k' : ℂ) + 1) + 1 = a + (k' + 2) by ring]; exact h2
      field_simp
    rw [e, norm_div, norm_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right h (norm_nonneg _)
  have key := cfConv_tendsto_of_ratio (h := (0 : ℂ)) hw (by simp [incGF_w]) hA hwN
    (q := 3) (by norm_num) hrat
  have hval : (0 : ℂ) + A 0 * incGF_w a z 1 / incGF_w a z 0 = kummerM 1 (a + 1) z := by
    simp [incGF_w, hA0, incGF_P, kumCF_F]
  rwa [hval] at key

section StieltjesVitali

open Set

/-! ### The Stieltjes–Vitali argument on the slit plane -/

/-- `Re √z > 0` on the slit plane. -/
theorem incGF_re_sqrt_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < (z ^ (2⁻¹ : ℂ)).re := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have h1 : -Real.pi < z.arg := neg_pi_lt_arg z
  have h2 : z.arg < Real.pi := arg_lt_pi_iff.mpr (by
    rcases mem_slitPlane_iff.mp hz with h | h
    · exact Or.inl h.le
    · exact Or.inr h)
  rw [cpow_def_of_ne_zero hz0, exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  simp only [mul_im, log_im, log_re, inv_re, inv_im, re_ofNat, im_ofNat]
  constructor <;> norm_num <;> nlinarith [Real.pi_pos]

/-- A sequence of functions dominated by one continuous function is locally bounded. -/
theorem incGF_isLocallyBoundedOn {F : ℕ → ℂ → ℂ} {Ω : Set ℂ} {β : ℂ → ℝ}
    (hβ : ContinuousOn β Ω) (hF : ∀ n, ∀ z ∈ Ω, ‖F n z‖ ≤ β z) :
    TauCeti.IsLocallyBoundedOn F Ω := by
  refine TauCeti.isLocallyBoundedOn_def.mpr fun K hKΩ hK => ?_
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hβ.mono hKΩ)
  exact ⟨C, fun n z hz => (hF n z (hKΩ hz)).trans ((Real.le_norm_self _).trans (hC z hz))⟩

/-- **Stieltjes–Vitali.** A locally bounded sequence of holomorphic functions on the slit plane
which converges on `(0, ∞)` to a function holomorphic on the slit plane converges to it on the
whole slit plane. -/
theorem incGF_tendsto_of_slitPlane {F : ℕ → ℂ → ℂ} {T : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) slitPlane) (hb : TauCeti.IsLocallyBoundedOn F slitPlane)
    (hT : DifferentiableOn ℂ T slitPlane)
    (hreal : ∀ t : ℝ, 0 < t → Tendsto (fun n => F n t) atTop (𝓝 (T t)))
    {z : ℂ} (hz : z ∈ slitPlane) : Tendsto (fun n => F n z) atTop (𝓝 (T z)) := by
  have hpre : IsPreconnected slitPlane :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  set A : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioi 0
  have hAΩ : A ⊆ slitPlane := by
    rintro _ ⟨t, ht, rfl⟩; exact ofReal_mem_slitPlane.mpr ht
  have htend : Tendsto (fun n : ℕ => (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
      simpa [Function.comp_def] using (continuous_ofReal.tendsto 1).comp h1
    · simp only [mem_compl_iff, mem_singleton_iff, ← ofReal_one, ofReal_inj]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmem : ∀ n : ℕ, (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ A := fun n =>
    ⟨_, show (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) by positivity, rfl⟩
  have hacc : AccPt (1 : ℂ) (𝓟 A) :=
    accPt_iff_frequently_nhdsNE.mpr (htend.frequently (Frequently.of_forall hmem))
  obtain ⟨q, hq, hqA, hconv⟩ := TauCeti.vitali_of_tendsto isOpen_slitPlane hpre hF hb hAΩ
    one_mem_slitPlane hacc (g := T) (by rintro _ ⟨t, ht, rfl⟩; exact hreal t ht)
  have hqT : EqOn q T slitPlane :=
    (hq.analyticOnNhd isOpen_slitPlane).eqOn_of_preconnected_of_frequently_eq
      (hT.analyticOnNhd isOpen_slitPlane) hpre one_mem_slitPlane
      (htend.frequently (Frequently.of_forall fun n => hqA (hmem n)))
  rw [← hqT hz]
  exact hconv.tendsto_at hz

/-! ### Legendre's fraction for `Γ(a,z)` on the slit plane -/

/-- The partial numerators `1-a, 1, 2-a, 2, …` (index `k ≥ 1`) of Legendre's fraction. -/
def incGF_c (α : ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 1 then ((k / 2 : ℕ) : ℝ) + 1 - α else ((k / 2 : ℕ) : ℝ)

/-- The Legendre coefficients `c_k` are positive for `k ≥ 1` when `α < 1`. -/
theorem incGF_c_pos {α : ℝ} (hα : α < 1) {k : ℕ} (hk : 1 ≤ k) : 0 < incGF_c α k := by
  unfold incGF_c
  split_ifs with h
  · have : (0 : ℝ) ≤ ((k / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  · have : 1 ≤ k / 2 := by omega
    exact_mod_cast this

/-- Partial numerators `1, (1-a)/z, 1/z, (2-a)/z, 2/z, …` of the normalized fraction
`1/(1 + ((1-a)/z)/(1 + (1/z)/(1 + ⋯)))`. -/
def incGF_LA (α : ℝ) (z : ℂ) (k : ℕ) : ℂ := if k = 0 then 1 else (incGF_c α k : ℂ) / z

/-- The convergents of the normalized Legendre fraction. -/
def incGF_LF (α : ℝ) (n : ℕ) (z : ℂ) : ℂ := (cfConv_ofFun 0 (incGF_LA α z) (fun _ => 1)).convs n

/-- The bound `‖s‖ / Re s` with `s = z^{-1/2}`. -/
def incGF_beta (z : ℂ) : ℝ := ‖(z ^ (2⁻¹ : ℂ))⁻¹‖ / ((z ^ (2⁻¹ : ℂ))⁻¹).re

/-- Stieltjes value-region bound for the convergents of Legendre's fraction. -/
theorem incGF_LF_bound {α : ℝ} (hα : α < 1) {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    (cfConv_ofFun 0 (incGF_LA α z) (fun _ => 1)).dens n ≠ 0 ∧ ‖incGF_LF α n z‖ ≤ incGF_beta z := by
  have hs : 0 < ((z ^ (2⁻¹ : ℂ))⁻¹).re := cfConv_re_recip_pos (incGF_re_sqrt_pos hz)
  have hsq : ((z ^ (2⁻¹ : ℂ))⁻¹) ^ 2 = z⁻¹ := by rw [inv_pow, cpow_ofNat_inv_pow]
  obtain ⟨h1, h2⟩ := cfConv_sfrac_bound (h := 0) (a := incGF_LA α z) (b := fun _ => 1) hs
    (fun _ => rfl) (c := incGF_c α) (fun k hk => incGF_c_pos hα hk)
    (fun k hk => by simp only [incGF_LA, show k ≠ 0 by omega, ↓reduceIte, hsq, div_eq_mul_inv]) n
  refine ⟨h1, ?_⟩
  rw [sub_zero] at h2
  simpa [incGF_LF, incGF_beta, incGF_LA] using h2

/-- The bound function `incGF_beta` is continuous on the slit plane. -/
theorem incGF_beta_continuousOn : ContinuousOn incGF_beta slitPlane := by
  intro z hz
  have hc : ContinuousAt (fun w : ℂ => w ^ (2⁻¹ : ℂ)) z := continuousAt_cpow_const hz
  have hne : z ^ (2⁻¹ : ℂ) ≠ 0 := by
    intro h0; have := incGF_re_sqrt_pos hz; rw [h0, zero_re] at this; exact lt_irrefl _ this
  have hi : ContinuousAt (fun w : ℂ => (w ^ (2⁻¹ : ℂ))⁻¹) z := hc.inv₀ hne
  have hre : ((z ^ (2⁻¹ : ℂ))⁻¹).re ≠ 0 := (cfConv_re_recip_pos (incGF_re_sqrt_pos hz)).ne'
  exact (hi.norm.div (Complex.continuous_re.continuousAt.comp hi) hre).continuousWithinAt

/-- The convergents of Legendre's fraction are holomorphic on the slit plane. -/
theorem incGF_LF_differentiableOn (α : ℝ) (hα : α < 1) (n : ℕ) :
    DifferentiableOn ℂ (incGF_LF α n) slitPlane := by
  have := cfConv_convs_differentiableOn (Ω := slitPlane) (h := fun _ => 0)
    (a := fun k z => incGF_LA α z k) (b := fun _ _ => 1) (differentiableOn_const _)
    (fun k => by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [incGF_LA, ↓reduceIte]; exact differentiableOn_const _
      · simp only [incGF_LA, show k ≠ 0 by omega, ↓reduceIte]
        exact (differentiableOn_const _).div differentiableOn_id
          fun z hz => slitPlane_ne_zero hz)
    (fun _ => differentiableOn_const _) n (fun z hz => (incGF_LF_bound hα hz n).1)
  exact this

/-- The target `z^{1-a} e^z Γ(a,z)` of the normalized fraction. -/
def incGF_LT (α : ℝ) (z : ℂ) : ℂ := z ^ (1 - (α : ℂ)) * exp z * upperIncGamma α z

/-- The target `z^{1-α} e^z Γ(α,z)` is holomorphic on the slit plane. -/
theorem incGF_LT_differentiableOn (α : ℝ) : DifferentiableOn ℂ (incGF_LT α) slitPlane := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  exact ((differentiableAt_id.cpow_const hz).mul differentiableAt_exp).mul
    (hasDerivAt_upperIncGamma_complex α hz).differentiableAt

/-- The real case: Legendre's fraction converges for real `a < 1`, `x > 0` (from
`DLMF.Statistical.tendsto_gammaIncContFract`). -/
theorem incGF_LF_tendsto_real {α : ℝ} (hα : α < 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => incGF_LF α n t) atTop (𝓝 (incGF_LT α t)) := by
  set aR : ℕ → ℝ := fun k => if k = 0 then 1 else incGF_c α k / t with haR
  set C : ℝ := t⁻¹ * (t ^ α * Real.exp (-t)) with hC
  have hC0 : C ≠ 0 := by positivity
  -- the complex convergents are real
  have hcx : ∀ n, incGF_LF α n t = ((cfConv_ofFun 0 aR (fun _ => 1)).convs n : ℂ) := by
    intro n
    have hm := cfConv_convs_map (h := (0 : ℝ)) (a := aR) (b := fun _ => (1 : ℝ))
      Complex.ofRealHom n
    simp only [Complex.ofRealHom_eq_coe, ofReal_zero, ofReal_one] at hm
    rw [← hm, incGF_LF]
    congr 2
    funext k
    simp only [incGF_LA, aR]
    split_ifs <;> push_cast <;> rfl
  -- the real convergents are those of `DLMF.Statistical.gammaIncContFract`, rescaled
  set r : ℕ → ℝ := fun k => if k % 2 = 0 then t⁻¹ else 1 with hr
  have hr0 : ∀ k, r k ≠ 0 := fun k => by simp only [r]; split_ifs <;> positivity
  have hequiv := fun n => cfConv_equiv_convs (h := (0 : ℝ))
    (a := DLMF.Statistical.gammaIncCFNum α t) (b := DLMF.Statistical.gammaIncCFDen t) r hr0 n
  have hA : (fun k => (if k = 0 then r 0 else r (k - 1) * r k) *
      DLMF.Statistical.gammaIncCFNum α t k) = fun k => if k = 0 then C * aR 0 else aR k := by
    funext k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rcases m with _ | m
      · simp [r, aR, C, DLMF.Statistical.gammaIncCFNum]
      · have h1 : ¬ (2 * (m + 1) = 0) := by omega
        have h2 : (2 * (m + 1)) % 2 = 0 := by omega
        have h3 : (2 * (m + 1) - 1) % 2 = 1 := by omega
        have h4 : ¬ ((2 * (m + 1) - 1) % 2 = 0) := by omega
        simp only [h1, h2, h4, ↓reduceIte, aR, DLMF.Statistical.gammaIncCFNum, incGF_c, r]
        field_simp
    · have h1 : ¬ (2 * m + 1 = 0) := by omega
      have h2 : ¬ ((2 * m + 1) % 2 = 0) := by omega
      have h3 : (2 * m + 1 - 1) % 2 = 0 := by omega
      simp only [h1, h3, ↓reduceIte, aR, DLMF.Statistical.gammaIncCFNum, incGF_c, r,
        show (2 * m + 1) % 2 = 1 by omega]
      simp only [one_ne_zero, ↓reduceIte]
      field_simp
  have hB : (fun k => r k * DLMF.Statistical.gammaIncCFDen t k) = fun _ => (1 : ℝ) := by
    funext k
    simp only [r, DLMF.Statistical.gammaIncCFDen]
    split_ifs <;> field_simp
  have hreal : Tendsto (cfConv_ofFun 0 aR (fun _ => 1)).convs atTop
      (𝓝 ((DLMF.Confluent.upperIncGamma α t).re / C)) := by
    have h := DLMF.Statistical.tendsto_gammaIncContFract hα ht
    have e : ∀ n, (cfConv_ofFun 0 aR (fun _ => 1)).convs n =
        (DLMF.Statistical.gammaIncContFract α t).convs n / C := by
      intro n
      have h1 := hequiv n
      rw [hA, hB] at h1
      have h2 := cfConv_convs_smul_a0 (a := aR) (b := fun _ => (1 : ℝ)) C n
      rw [h2] at h1
      change C * _ = (cfConv_ofFun 0 _ _).convs n at h1
      rw [eq_div_iff hC0, mul_comm, h1]
      rfl
    show Tendsto (fun n => (cfConv_ofFun 0 aR fun _ => 1).convs n) atTop _
    exact (h.div_const C).congr fun n => (e n).symm
  have hval : incGF_LT α t = (((DLMF.Confluent.upperIncGamma α t).re / C : ℝ) : ℂ) := by
    set G := (DLMF.Confluent.upperIncGamma (α : ℂ) (t : ℂ)).re with hG
    have hU := DLMF.Statistical.upperIncGamma_eq_gammaTail α ht
    have hUr : DLMF.Confluent.upperIncGamma (α : ℂ) (t : ℂ) = (G : ℂ) := by
      rw [hG, hU, ofReal_re]
    rw [incGF_LT, hUr, show (1 : ℂ) - α = ((1 - α : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow ht.le, ← ofReal_exp, ← ofReal_mul, ← ofReal_mul]
    congr 1
    rw [hC]
    have h1 : t ^ (1 - α) * t ^ α = t := by
      rw [← Real.rpow_add ht, sub_add_cancel, Real.rpow_one]
    have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have hp : (0 : ℝ) < t ^ α := Real.rpow_pos_of_pos ht α
    field_simp
    linear_combination (Real.exp (-t) * Real.exp t * G) * h1 + G * t * h2
  rw [hval]
  simp_rw [hcx]
  exact (continuous_ofReal.tendsto _).comp hreal

/-- **Legendre's continued fraction on the slit plane** (DLMF 8.9.2, real `a < 1`): the
convergents of `1/(1 + ((1-a)/z)/(1 + (1/z)/(1 + ((2-a)/z)/(1 + ⋯))))` tend to
`z^{1-a} e^z Γ(a,z)` for every `z ∈ ℂ ∖ (-∞, 0]`. The proof is the Stieltjes–Vitali argument:
the convergents are holomorphic and locally bounded on the slit plane (`cfConv_sfrac_bound`),
converge on `(0, ∞)` by the real theory, and Vitali's theorem plus the identity theorem give
convergence everywhere. -/
theorem incGF_LF_tendsto {α : ℝ} (hα : α < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun n => incGF_LF α n z) atTop (𝓝 (incGF_LT α z)) :=
  incGF_tendsto_of_slitPlane (incGF_LF_differentiableOn α hα)
    (incGF_isLocallyBoundedOn incGF_beta_continuousOn fun n _ hz => (incGF_LF_bound hα hz n).2)
    (incGF_LT_differentiableOn α) (fun t ht => incGF_LF_tendsto_real hα ht) hz

/-- Legendre's fraction with first numerator `A₀` in the form
`A₀/(1 + ((1-a)/z)/(1 + (1/z)/(1 + ⋯)))` (DLMF 8.9.2 divided by `z`). -/
theorem incGF_formA_tendsto {α : ℝ} (hα : α < 1) (A0 : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    {a : ℕ → ℂ} (ha0 : a 0 = A0) (ha : ∀ k, 1 ≤ k → a k = (incGF_c α k : ℂ) / z) :
    Tendsto (cfConv_ofFun 0 a (fun _ => 1)).convs atTop (𝓝 (A0 * incGF_LT α z)) := by
  have e : a = fun k => if k = 0 then A0 * incGF_LA α z 0 else incGF_LA α z k := by
    funext k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [incGF_LA, ha0]
    · simp only [incGF_LA, show k ≠ 0 by omega, ↓reduceIte, ha k hk]
  have h := (incGF_LF_tendsto hα hz).const_mul A0
  show Tendsto (fun n => (cfConv_ofFun 0 a (fun _ => 1)).convs n) atTop _
  refine h.congr fun n => ?_
  rw [e, cfConv_convs_smul_a0]
  rfl

/-- Legendre's fraction in the form `A₀/(z + (1-a)/(1 + 1/(z + (2-a)/(1 + ⋯))))` (DLMF 8.9.2):
for real `a < 1` and `z ∈ ℂ ∖ (-∞, 0]` the convergents tend to `A₀ z^{-a} e^z Γ(a,z)`. -/
theorem incGF_formB_tendsto {α : ℝ} (hα : α < 1) (A0 : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    {a : ℕ → ℂ} (ha0 : a 0 = A0) (ha : ∀ k, 1 ≤ k → a k = (incGF_c α k : ℂ)) :
    Tendsto (cfConv_ofFun 0 a (fun k => if Even k then z else 1)).convs atTop
      (𝓝 (A0 * z ^ (-(α : ℂ)) * exp z * upperIncGamma α z)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set r : ℕ → ℂ := fun k => if Even k then z⁻¹ else 1 with hr
  have hr0 : ∀ k, r k ≠ 0 := fun k => by
    simp only [r]; split_ifs
    · exact inv_ne_zero hz0
    · exact one_ne_zero
  have hequiv := fun n => cfConv_equiv_convs (h := (0 : ℂ)) (a := a)
    (b := fun k => if Even k then z else 1) r hr0 n
  have hA : (fun k => (if k = 0 then r 0 else r (k - 1) * r k) * a k) =
      fun k => if k = 0 then A0 * z⁻¹ else (incGF_c α k : ℂ) / z := by
    funext k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [r, ha0, mul_comm]
    · simp only [show k ≠ 0 by omega, ↓reduceIte, ha k hk, r]
      rcases Nat.even_or_odd k with he | ho
      · have : ¬ Even (k - 1) := by
          rw [Nat.not_even_iff_odd]; exact Nat.Even.sub_odd hk he odd_one
        simp only [this, he, ↓reduceIte]; field_simp
      · have : Even (k - 1) := Nat.Odd.sub_odd ho odd_one
        simp only [this, Nat.not_even_iff_odd.mpr ho, ↓reduceIte]; field_simp
  have hB : (fun k => r k * (if Even k then z else 1)) = fun _ => (1 : ℂ) := by
    funext k
    simp only [r]; split_ifs
    · exact inv_mul_cancel₀ hz0
    · exact one_mul 1
  have h := incGF_formA_tendsto hα (A0 * z⁻¹) hz (a := fun k => if k = 0 then A0 * z⁻¹
    else (incGF_c α k : ℂ) / z) (by simp) (fun k hk => by simp [show k ≠ 0 by omega])
  have hval : A0 * z⁻¹ * incGF_LT α z = A0 * z ^ (-(α : ℂ)) * exp z * upperIncGamma α z := by
    rw [incGF_LT, cpow_sub _ _ hz0, cpow_one, cpow_neg]
    field_simp
  rw [← hval]
  show Tendsto (fun n => (cfConv_ofFun 0 a _).convs n) atTop _
  refine h.congr fun n => ?_
  rw [← hequiv n, hA, hB]

end StieltjesVitali

end DLMF.Confluent
