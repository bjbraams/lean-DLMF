/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.ModularFunctions

/-!
# `q`-expansions of the modular functions `λ` and `J`

The expansions of the elliptic modular function `λ(τ)` and of Klein's complete invariant
`J(τ)` in powers of the nome `q = e^{iπτ}` as `ℑτ → ∞` (DLMF §23.17(ii)). Both are proved from
the theta-function formulas of `DLMF.Weierstrass.ModularFunctions` and tail bounds for the
lacunary theta series.

## Main results

* `modularLambda_isBigO`: DLMF 23.17.4, `λ(τ) = 16q(1 - 8q + 44q² + O(q³))`.
* `kleinJ_isBigO`: DLMF 23.17.5,
  `1728J(τ) = q⁻² + 744 + 196884q² + 21493760q⁴ + O(q⁶)`.
-/

@[expose] public section

open Complex Asymptotics Matrix
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

noncomputable section

namespace DLMF.Weierstrass

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

open DLMF.Elliptic DLMF.Theta DLMF.JacobiElliptic
open ModularForm (kleinJ)

/-! ### §23.17(ii) `q`-expansions -/

/-- Tail bound for a lacunary `q`-series `∑ₙ q^{e(n)}`: dropping the finitely many terms with
`e(n) < N` leaves `O(‖q‖^N)` for `‖q‖ ≤ 1/2`. -/
private lemma norm_tsum_pow_sub_sum_le {e : ℤ → ℕ} {N : ℕ} (F : Finset ℤ)
    (hF : ∀ n ∉ F, N ≤ e n) (hs : Summable fun n => (1 / 2 : ℝ) ^ e n) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 2) :
    ‖∑' n, q ^ e n - ∑ n ∈ F, q ^ e n‖ ≤ 2 ^ N * (∑' n, (1 / 2 : ℝ) ^ e n) * ‖q‖ ^ N := by
  have hle : ∀ n, ‖q ^ e n‖ ≤ (1 / 2 : ℝ) ^ e n := fun n => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hq _
  have hsum : Summable fun n => q ^ e n := Summable.of_norm_bounded hs hle
  have hpt : ∀ n ∉ F, ‖q ^ e n‖ ≤ ‖q‖ ^ N * (2 ^ N * (1 / 2 : ℝ) ^ e n) := by
    intro n hn
    have h1 := hF n hn
    rw [norm_pow, ← Nat.add_sub_cancel' h1, pow_add, pow_add]
    have h2 : ‖q‖ ^ (e n - N) ≤ (1 / 2 : ℝ) ^ (e n - N) :=
      pow_le_pow_left₀ (norm_nonneg _) hq _
    have h3 : (2 : ℝ) ^ N * ((1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ (e n - N)) =
        (1 / 2 : ℝ) ^ (e n - N) := by
      rw [← mul_assoc, ← mul_pow]; norm_num
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 (pow_nonneg (norm_nonneg _) _)
  rw [← hsum.sum_add_tsum_compl (s := F), add_sub_cancel_left]
  have hsc : Summable fun n : ((F : Set ℤ)ᶜ : Set ℤ) => (1 / 2 : ℝ) ^ e n :=
    hs.subtype _
  have hb : Summable fun n : ((F : Set ℤ)ᶜ : Set ℤ) =>
      ‖q‖ ^ N * (2 ^ N * (1 / 2 : ℝ) ^ e n) := (hsc.mul_left _).mul_left _
  calc ‖∑' n : ((F : Set ℤ)ᶜ : Set ℤ), q ^ e n‖
      ≤ ∑' n : ((F : Set ℤ)ᶜ : Set ℤ), ‖q‖ ^ N * (2 ^ N * (1 / 2 : ℝ) ^ e n) :=
        tsum_of_norm_bounded hb.hasSum fun n => hpt n n.2
    _ = ‖q‖ ^ N * (2 ^ N * ∑' n : ((F : Set ℤ)ᶜ : Set ℤ), (1 / 2 : ℝ) ^ e n) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ ≤ ‖q‖ ^ N * (2 ^ N * ∑' n, (1 / 2 : ℝ) ^ e n) := by
        gcongr
        exact hs.tsum_subtype_le _ _ (fun n => by positivity)
    _ = _ := by ring

open Filter Topology in
/-- The nome `q = e^{iπτ}` tends to `0` at `i∞`. -/
private lemma tendsto_nome_atImInfty :
    Tendsto (fun τ : ℍ => cexp (π * I * τ)) atImInfty (𝓝 0) := by
  refine (qParam_tendsto_atImInfty (h := 2) (by norm_num)).congr fun τ => ?_
  simp only [Function.Periodic.qParam]
  congr 1; push_cast; ring

/-- `θ₃(0|τ) = ∑ₙ q^{n²}`. -/
private lemma jacobiTheta₂_zero_eq_tsum (τ : ℂ) :
    jacobiTheta₂ 0 τ = ∑' n : ℤ, cexp (π * I * τ) ^ (n.natAbs ^ 2) := by
  simp only [jacobiTheta₂, jacobiTheta₂_term]
  congr 1; funext n
  rw [← Complex.exp_nat_mul]
  congr 1
  have : ((n.natAbs ^ 2 : ℕ) : ℂ) = (n : ℂ) ^ 2 := by
    have h : ((n.natAbs : ℤ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by exact_mod_cast Int.natAbs_sq n
    rw [Nat.cast_pow, ← h, Int.cast_natCast]
  rw [this]; ring

private lemma int_mul_add_nonneg (n : ℤ) : 0 ≤ n * n + n := by
  rcases le_or_gt 0 n with h | h <;> nlinarith

/-- `e^{-iπτ/4}θ₂(0|τ) = ∑ₙ q^{n(n+1)}`. -/
private lemma jacobiTheta₂_half_eq_tsum (τ : ℂ) :
    jacobiTheta₂ (τ / 2) τ = ∑' n : ℤ, cexp (π * I * τ) ^ (n * n + n).toNat := by
  simp only [jacobiTheta₂, jacobiTheta₂_term]
  congr 1; funext n
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (((n * n + n).toNat : ℕ) : ℂ) = (n : ℂ) ^ 2 + n := by
    have h := Int.toNat_of_nonneg (int_mul_add_nonneg n)
    have h' : (((n * n + n).toNat : ℤ) : ℂ) = ((n * n + n : ℤ) : ℂ) := by rw [h]
    push_cast at h'; rw [h']; ring
  rw [this]; ring

private lemma summable_half_pow_natAbs :
    Summable fun n : ℤ => (1 / 2 : ℝ) ^ n.natAbs := by
  have hg : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact Summable.of_nat_of_neg (by simpa using hg) (by simpa using hg)

private lemma summable_half_pow_natAbs_sq :
    Summable fun n : ℤ => (1 / 2 : ℝ) ^ (n.natAbs ^ 2) :=
  Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_self_pow two_ne_zero _))
    summable_half_pow_natAbs

private lemma summable_half_pow_toNat :
    Summable fun n : ℤ => (1 / 2 : ℝ) ^ (n * n + n).toNat := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_half_pow_natAbs.mul_left 2)
  have h : n.natAbs ≤ (n * n + n).toNat + 1 := by
    rcases le_or_gt 0 n with h | h
    · have : n ≤ n * n + n := by nlinarith
      omega
    · have : -n - 1 ≤ n * n + n := by nlinarith
      omega
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) h
  rw [pow_succ] at this
  linarith

open Filter in
private lemma eventually_norm_exp_pi_I_mul_le :
    ∀ᶠ τ : ℍ in atImInfty, ‖cexp (π * I * τ)‖ ≤ 1 / 2 := by
  have := tendsto_nome_atImInfty.norm
  rw [norm_zero] at this
  exact this.eventually (ge_mem_nhds (by norm_num))

/-- `θ₃(0|τ) = 1 + 2q + O(q⁴)`. -/
private lemma jacobiTheta₂_zero_isBigO :
    (fun τ : ℍ => jacobiTheta₂ 0 τ - (1 + 2 * cexp (π * I * τ))) =O[atImInfty]
      fun τ => cexp (π * I * τ) ^ 4 := by
  refine IsBigO.of_bound (2 ^ 4 * ∑' n : ℤ, (1 / 2 : ℝ) ^ (n.natAbs ^ 2)) ?_
  filter_upwards [eventually_norm_exp_pi_I_mul_le] with τ hτ
  have h := norm_tsum_pow_sub_sum_le (e := fun n : ℤ => n.natAbs ^ 2) (N := 4) {-1, 0, 1}
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have : 2 ≤ n.natAbs := by omega
      exact (Nat.pow_le_pow_left this 2).trans' (by norm_num))
    summable_half_pow_natAbs_sq hτ
  have hF : ∑ n ∈ ({-1, 0, 1} : Finset ℤ), cexp (π * I * τ) ^ (n.natAbs ^ 2) =
      1 + 2 * cexp (π * I * τ) := by
    simp; ring
  rw [jacobiTheta₂_zero_eq_tsum, ← hF, norm_pow]
  exact h

/-- `e^{-iπτ/4}θ₂(0|τ) = 2 + 2q² + O(q⁶)`. -/
private lemma jacobiTheta₂_half_isBigO :
    (fun τ : ℍ => jacobiTheta₂ ((τ : ℂ) / 2) τ - (2 + 2 * cexp (π * I * τ) ^ 2)) =O[atImInfty]
      fun τ => cexp (π * I * τ) ^ 6 := by
  refine IsBigO.of_bound (2 ^ 6 * ∑' n : ℤ, (1 / 2 : ℝ) ^ (n * n + n).toNat) ?_
  filter_upwards [eventually_norm_exp_pi_I_mul_le] with τ hτ
  have h := norm_tsum_pow_sub_sum_le (e := fun n : ℤ => (n * n + n).toNat) (N := 6)
    {-2, -1, 0, 1}
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have : 6 ≤ n * n + n := by
        rcases le_or_gt 2 n with h | h
        · nlinarith
        · have : n ≤ -3 := by omega
          nlinarith
      omega)
    summable_half_pow_toNat hτ
  have hF : ∑ n ∈ ({-2, -1, 0, 1} : Finset ℤ), cexp (π * I * τ) ^ (n * n + n).toNat =
      2 + 2 * cexp (π * I * τ) ^ 2 := by
    simp; ring
  rw [jacobiTheta₂_half_eq_tsum, ← hF, norm_pow]
  exact h

/-- `λ(τ) = q B⁴/T⁴` with `B = e^{-iπτ/4}θ₂(0|τ)` and `T = θ₃(0|τ)`. -/
private lemma modularLambda_eq_nome_mul (τ : ℂ) :
    modularLambda τ = cexp (π * I * τ) * jacobiTheta₂ (τ / 2) τ ^ 4 / jacobiTheta₂ 0 τ ^ 4 := by
  simp only [modularLambda, jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaTwoTau,
    jacobiThetaThreeTau, mul_zero, add_zero, zero_div, zero_add]
  have h1 : cexp (π * I * τ / 4) ^ 4 = cexp (π * I * τ) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : (π : ℂ) * τ / 2 / π = τ / 2 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [mul_pow, h1, h2]

/-- DLMF 23.17.4: `λ(τ) = 16q(1 - 8q + 44q² + O(q³))` as `q = e^{iπτ} → 0`. -/
@[dlmf 23.17.E4]
theorem modularLambda_isBigO :
    (fun τ : ℍ ↦ modularLambda τ - 16 * cexp (π * I * τ) *
        (1 - 8 * cexp (π * I * τ) + 44 * cexp (π * I * τ) ^ 2)) =O[atImInfty]
      fun τ ↦ cexp (π * I * τ) ^ 4 := by
  open Filter Topology in
  set q : ℍ → ℂ := fun τ => cexp (π * I * τ) with hq
  set B : ℍ → ℂ := fun τ => jacobiTheta₂ ((τ : ℂ) / 2) τ
  set T : ℍ → ℂ := fun τ => jacobiTheta₂ 0 τ
  set a : ℍ → ℂ := fun τ => B τ - (2 + 2 * q τ ^ 2)
  set b : ℍ → ℂ := fun τ => T τ - (1 + 2 * q τ)
  have hq0 : Tendsto q atImInfty (𝓝 0) := tendsto_nome_atImInfty
  have ha : a =O[atImInfty] fun τ => q τ ^ 6 := jacobiTheta₂_half_isBigO
  have hb : b =O[atImInfty] fun τ => q τ ^ 4 := jacobiTheta₂_zero_isBigO
  have hq6 : (fun τ => q τ ^ 6) =O[atImInfty] fun τ => q τ ^ 4 := by
    have : (fun τ => q τ ^ 6) = fun τ => q τ ^ 4 * q τ ^ 2 := funext fun τ => by ring
    rw [this]
    simpa using (isBigO_refl (fun τ => q τ ^ 4) atImInfty).mul
      ((hq0.pow 2).isBigO_one ℂ)
  have ha0 : Tendsto a atImInfty (𝓝 0) :=
    ha.trans_tendsto (by simpa using hq0.pow 6)
  have hb0 : Tendsto b atImInfty (𝓝 0) :=
    hb.trans_tendsto (by simpa using hq0.pow 4)
  have hB : Tendsto B atImInfty (𝓝 2) := by
    have : B = fun τ => a τ + (2 + 2 * q τ ^ 2) := funext fun τ => by simp [a]
    rw [this]; simpa using ha0.add ((hq0.pow 2).const_mul 2 |>.const_add 2)
  have hT : Tendsto T atImInfty (𝓝 1) := by
    have : T = fun τ => b τ + (1 + 2 * q τ) := funext fun τ => by simp [b]
    rw [this]; simpa using hb0.add ((hq0.const_mul 2).const_add 1)
  have hT4 : Tendsto (fun τ => T τ ^ 4) atImInfty (𝓝 1) := by simpa using hT.pow 4
  have hTne : ∀ᶠ τ in atImInfty, T τ ≠ 0 :=
    hT.eventually (isOpen_ne.mem_nhds one_ne_zero)
  set r : ℂ → ℂ := fun x => 16 * (-192 - 810 * x - 1280 * x ^ 2 - 700 * x ^ 3 + x ^ 5)
  set c : ℍ → ℂ := fun τ => 2 + 2 * q τ ^ 2
  set d : ℍ → ℂ := fun τ => 1 + 2 * q τ
  set P : ℍ → ℂ := fun τ => 1 - 8 * q τ + 44 * q τ ^ 2
  have key : ∀ᶠ τ : ℍ in atImInfty, modularLambda (τ : ℂ) - 16 * q τ * P τ =
      q τ ^ 4 * (r (q τ) / T τ ^ 4) +
      a τ * (q τ * (B τ ^ 3 + B τ ^ 2 * c τ + B τ * c τ ^ 2 + c τ ^ 3) / T τ ^ 4) +
      b τ * (q τ * (-16 * P τ * (T τ ^ 3 + T τ ^ 2 * d τ + T τ * d τ ^ 2 + d τ ^ 3)) /
        T τ ^ 4) := by
    filter_upwards [hTne] with τ hτ
    rw [modularLambda_eq_nome_mul]
    simp only [a, b, c, d, P, r, B, T, q] at hτ ⊢
    field_simp
    ring
  have hV : Tendsto (fun τ => (q τ, B τ, T τ)) atImInfty (𝓝 ((0 : ℂ), (2 : ℂ), (1 : ℂ))) :=
    hq0.prodMk_nhds (hB.prodMk_nhds hT)
  have bdd : ∀ Φ : ℂ × ℂ × ℂ → ℂ, ContinuousAt Φ ((0 : ℂ), (2 : ℂ), (1 : ℂ)) →
      (fun τ => Φ (q τ, B τ, T τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    fun Φ hΦ => (hΦ.tendsto.comp hV).isBigO_one ℂ
  have h1 := (isBigO_refl (fun τ => q τ ^ 4) atImInfty).mul
    (bdd (fun p => r p.1 / p.2.2 ^ 4) (by fun_prop (disch := norm_num)))
  have h2 := (ha.trans hq6).mul (bdd (fun p => p.1 * (p.2.1 ^ 3 + p.2.1 ^ 2 * (2 + 2 * p.1 ^ 2) +
      p.2.1 * (2 + 2 * p.1 ^ 2) ^ 2 + (2 + 2 * p.1 ^ 2) ^ 3) / p.2.2 ^ 4)
    (by fun_prop (disch := norm_num)))
  have h3 := hb.mul (bdd (fun p => p.1 * (-16 * (1 - 8 * p.1 + 44 * p.1 ^ 2) *
      (p.2.2 ^ 3 + p.2.2 ^ 2 * (1 + 2 * p.1) + p.2.2 * (1 + 2 * p.1) ^ 2 + (1 + 2 * p.1) ^ 3)) /
      p.2.2 ^ 4) (by fun_prop (disch := norm_num)))
  simp only [mul_one] at h1 h2 h3
  exact ((h1.add h2).add h3).congr' (key.mono fun τ h => h.symm) EventuallyEq.rfl


/-- The polynomial `R` with `N(q, c, d, e) = q⁸ R(q²)` in the proof of DLMF 23.17.5. -/
private def kleinJRemainderPoly (y : ℂ) : ℂ :=
    221260792320 - 127320002560 * y + 16666956945408 * y ^ 2 + 21710435399680 * y ^ 3 +
    242042804130560 * y ^ 4 + 850478849071104 * y ^ 5 + 1864035998029824 * y ^ 6 +
    7537199181694976 * y ^ 7 + 16825880865439232 * y ^ 8 + 35268699011637248 * y ^ 9 +
    88538989817691136 * y ^ 10 + 156760187758317568 * y ^ 11 + 297155562375373312 * y ^ 12 +
    546322573857466368 * y ^ 13 + 832357023616799744 * y ^ 14 + 1403336924359034880 * y ^ 15
    + 2060940991152477184 * y ^ 16 + 2893282226450905088 * y ^ 17 + 4236385388987320320 * y ^
    18 + 5282196220179062784 * y ^ 19 + 7094855178795310848 * y ^ 20 + 8774168778056120320 *
    y ^ 21 + 10175068328137460736 * y ^ 22 + 12750902341859999744 * y ^ 23 +
    13409070936209465344 * y ^ 24 + 15677658867079741440 * y ^ 25 + 16638918625159086080 * y
    ^ 26 + 16627291403257249792 * y ^ 27 + 18728415676287696896 * y ^ 28 +
    16425119632461660160 * y ^ 29 + 18237135226586202112 * y ^ 30 + 16226088895202197504 * y
    ^ 31 + 15112186823829225472 * y ^ 32 + 15477898801602625536 * y ^ 33 +
    10917811567473983488 * y ^ 34 + 12640908391714127872 * y ^ 35 + 7302133468309880832 * y ^
    36 + 7703037883106459648 * y ^ 37 + 4810844822034710528 * y ^ 38 + 2700819373953646592 *
    y ^ 39 + 3147688064317390848 * y ^ 40 - 352658878443290624 * y ^ 41 + 1951720516570054656
    * y ^ 42 - 1179410052402905088 * y ^ 43 + 1093280302966505472 * y ^ 44 -
    824505110586458112 * y ^ 45 + 542187146010689536 * y ^ 46 - 320818842693533696 * y ^ 47 +
    238212992552927232 * y ^ 48 - 57669768739553280 * y ^ 49 + 93315416490770432 * y ^ 50 +
    12115131810971648 * y ^ 51 + 32647744254377984 * y ^ 52 + 12719683488710656 * y ^ 53 +
    10145697173078016 * y ^ 54 + 5044589949878272 * y ^ 55 + 2774513439735808 * y ^ 56 +
    1386512079912960 * y ^ 57 + 662370930130944 * y ^ 58 + 306298813939712 * y ^ 59 +
    136979391971328 * y ^ 60 + 57047903109120 * y ^ 61 + 23909009195008 * y ^ 62 +
    8964670488576 * y ^ 63 + 3259880177664 * y ^ 64 + 1234803097600 * y ^ 65 + 296352743424 *
    y ^ 66 + 148176371712 * y ^ 67 + 12884901888 * y ^ 68 + 12884901888 * y ^ 69 + 536870912
    * y ^ 71

/-- The polynomial identity `N(q, c(q), d(q), e(q)) = q⁸ R(q²)`. -/
private lemma kleinJRemainderPoly_spec (q : ℂ) : q ^ 8 * kleinJRemainderPoly (q ^ 2) =
    32 * (q ^ 2 * (2 + 2 * q ^ 2 + 2 * q ^ 6) ^ 8 + (1 + 2 * q + 2 * q ^ 4) ^ 8 +
      (1 - 2 * q + 2 * q ^ 4) ^ 8) ^ 3 - (2 + 2 * q ^ 2 + 2 * q ^ 6) ^ 8 *
      (1 + 2 * q + 2 * q ^ 4) ^ 8 * (1 - 2 * q + 2 * q ^ 4) ^ 8 *
      (1 + 744 * q ^ 2 + 196884 * q ^ 4 + 21493760 * q ^ 6) := by
  simp only [kleinJRemainderPoly]
  ring

/-- `θ₄(0|τ) = ∑ₙ (-q)^{n²}`. -/
private lemma jacobiTheta₂_half_one_eq_tsum (τ : ℂ) :
    jacobiTheta₂ (1 / 2) τ = ∑' n : ℤ, (-cexp (π * I * τ)) ^ (n.natAbs ^ 2) := by
  simp only [jacobiTheta₂, jacobiTheta₂_term]
  congr 1; funext n
  rw [neg_pow, ← Complex.exp_nat_mul]
  have h1 : ((n.natAbs ^ 2 : ℕ) : ℂ) = (n : ℂ) ^ 2 := by
    have h : ((n.natAbs : ℤ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by exact_mod_cast Int.natAbs_sq n
    rw [Nat.cast_pow, ← h, Int.cast_natCast]
  have h2 : (-1 : ℂ) ^ (n.natAbs ^ 2) = cexp (2 * π * I * n * (1 / 2)) := by
    rw [show 2 * π * I * n * (1 / 2) = n * (π * I) by ring, Complex.exp_int_mul,
      Complex.exp_pi_mul_I]
    rcases Int.even_or_odd n with h | h
    · rw [h.neg_one_zpow, Even.neg_one_pow]
      exact Nat.even_pow.mpr ⟨Int.natAbs_even.mpr h, two_ne_zero⟩
    · rw [h.neg_one_zpow, Odd.neg_one_pow]
      exact (Int.natAbs_odd.mpr h).pow
  rw [h2, h1, ← Complex.exp_add]
  congr 1; ring

/-- `θ₃(0|τ) = 1 + 2q + 2q⁴ + O(q⁸)`. -/
private lemma jacobiTheta₂_zero_isBigO_eight :
    (fun τ : ℍ => jacobiTheta₂ 0 τ - (1 + 2 * cexp (π * I * τ) + 2 * cexp (π * I * τ) ^ 4))
      =O[atImInfty] fun τ => cexp (π * I * τ) ^ 8 := by
  refine IsBigO.of_bound (2 ^ 8 * ∑' n : ℤ, (1 / 2 : ℝ) ^ (n.natAbs ^ 2)) ?_
  filter_upwards [eventually_norm_exp_pi_I_mul_le] with τ hτ
  have h := norm_tsum_pow_sub_sum_le (e := fun n : ℤ => n.natAbs ^ 2) (N := 8)
    {-2, -1, 0, 1, 2}
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have : 3 ≤ n.natAbs := by omega
      exact (Nat.pow_le_pow_left this 2).trans' (by norm_num))
    summable_half_pow_natAbs_sq hτ
  have hF : ∑ n ∈ ({-2, -1, 0, 1, 2} : Finset ℤ), cexp (π * I * τ) ^ (n.natAbs ^ 2) =
      1 + 2 * cexp (π * I * τ) + 2 * cexp (π * I * τ) ^ 4 := by
    simp; ring
  rw [jacobiTheta₂_zero_eq_tsum, ← hF, norm_pow]
  exact h

/-- `θ₄(0|τ) = 1 - 2q + 2q⁴ + O(q⁸)`. -/
private lemma jacobiTheta₂_half_one_isBigO_eight :
    (fun τ : ℍ => jacobiTheta₂ (1 / 2) τ -
      (1 - 2 * cexp (π * I * τ) + 2 * cexp (π * I * τ) ^ 4))
      =O[atImInfty] fun τ => cexp (π * I * τ) ^ 8 := by
  refine IsBigO.of_bound (2 ^ 8 * ∑' n : ℤ, (1 / 2 : ℝ) ^ (n.natAbs ^ 2)) ?_
  filter_upwards [eventually_norm_exp_pi_I_mul_le] with τ hτ
  have hτ' : ‖-cexp (π * I * τ)‖ ≤ 1 / 2 := by rwa [norm_neg]
  have h := norm_tsum_pow_sub_sum_le (e := fun n : ℤ => n.natAbs ^ 2) (N := 8)
    {-2, -1, 0, 1, 2}
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have : 3 ≤ n.natAbs := by omega
      exact (Nat.pow_le_pow_left this 2).trans' (by norm_num))
    summable_half_pow_natAbs_sq hτ'
  have hF : ∑ n ∈ ({-2, -1, 0, 1, 2} : Finset ℤ), (-cexp (π * I * τ)) ^ (n.natAbs ^ 2) =
      1 - 2 * cexp (π * I * τ) + 2 * cexp (π * I * τ) ^ 4 := by
    simp; ring
  have h8 : ‖-cexp (π * I * τ)‖ ^ 8 = ‖cexp (π * I * τ) ^ 8‖ := by
    rw [norm_pow, norm_neg]
  rw [jacobiTheta₂_half_one_eq_tsum, ← hF, ← h8]
  exact h

/-- `e^{-iπτ/4}θ₂(0|τ) = 2 + 2q² + 2q⁶ + O(q⁸)`. -/
private lemma jacobiTheta₂_half_isBigO_eight :
    (fun τ : ℍ => jacobiTheta₂ ((τ : ℂ) / 2) τ -
      (2 + 2 * cexp (π * I * τ) ^ 2 + 2 * cexp (π * I * τ) ^ 6))
      =O[atImInfty] fun τ => cexp (π * I * τ) ^ 8 := by
  refine IsBigO.of_bound (2 ^ 8 * ∑' n : ℤ, (1 / 2 : ℝ) ^ (n * n + n).toNat) ?_
  filter_upwards [eventually_norm_exp_pi_I_mul_le] with τ hτ
  have h := norm_tsum_pow_sub_sum_le (e := fun n : ℤ => (n * n + n).toNat) (N := 8)
    {-3, -2, -1, 0, 1, 2}
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have : 8 ≤ n * n + n := by
        rcases le_or_gt 3 n with h | h
        · nlinarith
        · have : n ≤ -4 := by omega
          nlinarith
      omega)
    summable_half_pow_toNat hτ
  have hF : ∑ n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ), cexp (π * I * τ) ^ (n * n + n).toNat =
      2 + 2 * cexp (π * I * τ) ^ 2 + 2 * cexp (π * I * τ) ^ 6 := by
    simp; ring
  rw [jacobiTheta₂_half_eq_tsum, ← hF, norm_pow]
  exact h

/-- DLMF 23.17.5: `1728J(τ) = q⁻² + 744 + 196884q² + 21493760q⁴ + O(q⁶)` as
`q = e^{iπτ} → 0`. -/
@[dlmf 23.17.E5]
theorem kleinJ_isBigO :
    (fun τ : ℍ ↦ 1728 * kleinJ τ - (cexp (π * I * τ) ^ (-2 : ℤ) + 744 +
        196884 * cexp (π * I * τ) ^ 2 + 21493760 * cexp (π * I * τ) ^ 4)) =O[atImInfty]
      fun τ ↦ cexp (π * I * τ) ^ 6 := by
  open Filter Topology in
  set q : ℍ → ℂ := fun τ => cexp (π * I * τ) with hq
  set B : ℍ → ℂ := fun τ => jacobiTheta₂ ((τ : ℂ) / 2) τ
  set T : ℍ → ℂ := fun τ => jacobiTheta₂ 0 τ
  set U : ℍ → ℂ := fun τ => jacobiTheta₂ (1 / 2) τ
  set c : ℂ → ℂ := fun x => 2 + 2 * x ^ 2 + 2 * x ^ 6
  set d : ℂ → ℂ := fun x => 1 + 2 * x + 2 * x ^ 4
  set e : ℂ → ℂ := fun x => 1 - 2 * x + 2 * x ^ 4
  set N : ℂ × ℂ × ℂ × ℂ → ℂ := fun p =>
    32 * (p.1 ^ 2 * p.2.1 ^ 8 + p.2.2.1 ^ 8 + p.2.2.2 ^ 8) ^ 3 - p.2.1 ^ 8 * p.2.2.1 ^ 8 *
      p.2.2.2 ^ 8 * (1 + 744 * p.1 ^ 2 + 196884 * p.1 ^ 4 + 21493760 * p.1 ^ 6)
  set Dn : ℂ × ℂ × ℂ × ℂ → ℂ := fun p => p.2.1 ^ 8 * p.2.2.1 ^ 8 * p.2.2.2 ^ 8
  set v : ℍ → ℂ × ℂ × ℂ × ℂ := fun τ => (q τ, B τ, T τ, U τ)
  set w : ℍ → ℂ × ℂ × ℂ × ℂ := fun τ => (q τ, c (q τ), d (q τ), e (q τ))
  have hq0 : Tendsto q atImInfty (𝓝 0) := tendsto_nome_atImInfty
  have hqne : ∀ τ, q τ ≠ 0 := fun τ => Complex.exp_ne_zero _
  have hB : (fun τ => B τ - c (q τ)) =O[atImInfty] fun τ => q τ ^ 8 :=
    jacobiTheta₂_half_isBigO_eight
  have hT : (fun τ => T τ - d (q τ)) =O[atImInfty] fun τ => q τ ^ 8 :=
    jacobiTheta₂_zero_isBigO_eight
  have hU : (fun τ => U τ - e (q τ)) =O[atImInfty] fun τ => q τ ^ 8 :=
    jacobiTheta₂_half_one_isBigO_eight
  have hq8 : Tendsto (fun τ => q τ ^ 8) atImInfty (𝓝 0) := by simpa using hq0.pow 8
  have hlim : ∀ (F : ℍ → ℂ) (f : ℂ → ℂ), Continuous f →
      (fun τ => F τ - f (q τ)) =O[atImInfty] (fun τ => q τ ^ 8) →
      Tendsto F atImInfty (𝓝 (f 0)) := by
    intro F f hf hF
    have h1 := hF.trans_tendsto hq8
    have h2 := (hf.tendsto 0).comp hq0
    simpa using h1.add h2
  have hc : Continuous c := by fun_prop
  have hd : Continuous d := by fun_prop
  have he : Continuous e := by fun_prop
  have hv : Tendsto v atImInfty (𝓝 ((0 : ℂ), (2 : ℂ), (1 : ℂ), (1 : ℂ))) := by
    have h2 := hlim B c hc hB
    have h3 := hlim T d hd hT
    have h4 := hlim U e he hU
    simp only [c, d, e] at h2 h3 h4
    norm_num at h2 h3 h4
    exact hq0.prodMk_nhds (h2.prodMk_nhds (h3.prodMk_nhds h4))
  have hw : Tendsto w atImInfty (𝓝 ((0 : ℂ), (2 : ℂ), (1 : ℂ), (1 : ℂ))) := by
    have h : Tendsto (fun x : ℂ => (x, c x, d x, e x)) (𝓝 0)
        (𝓝 ((0 : ℂ), (2 : ℂ), (1 : ℂ), (1 : ℂ))) := by
      have := ((continuous_id.prodMk (hc.prodMk (hd.prodMk he))).tendsto 0)
      simp only [c, d, e] at this
      norm_num at this
      exact this
    exact h.comp hq0
  have hDn : ∀ᶠ τ in atImInfty, Dn (v τ) ≠ 0 := by
    have : Tendsto (fun τ => Dn (v τ)) atImInfty (𝓝 (Dn ((0 : ℂ), (2 : ℂ), (1 : ℂ), (1 : ℂ)))) :=
      ((by fun_prop : Continuous Dn).tendsto _).comp hv
    exact this.eventually (isOpen_ne.mem_nhds (by norm_num [Dn]))
  have key : ∀ᶠ τ : ℍ in atImInfty, 1728 * kleinJ τ - (q τ ^ (-2 : ℤ) + 744 +
      196884 * q τ ^ 2 + 21493760 * q τ ^ 4) =
      (q τ ^ 8 * kleinJRemainderPoly (q τ ^ 2) + (N (v τ) - N (w τ))) *
        ((q τ ^ 2)⁻¹ * (Dn (v τ))⁻¹) := by
    filter_upwards [hDn] with τ hτ
    have h2 : jacobiThetaTwoNullTau τ = cexp (π * I * τ / 4) * B τ := by
      simp only [jacobiThetaTwoNullTau, jacobiThetaTwoTau, jacobiThetaThreeTau, mul_zero,
        add_zero, zero_add, B]
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      congr 2; field_simp
    have h3 : jacobiThetaThreeNullTau τ = T τ := by
      simp [jacobiThetaThreeNullTau, jacobiThetaThreeTau, T]
    have h4 : jacobiThetaFourNullTau τ = U τ := by
      simp only [jacobiThetaFourNullTau, jacobiThetaFourTau, jacobiThetaThreeTau, zero_add, U]
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      congr 1; field_simp
    have h8 : cexp (π * I * τ / 4) ^ 8 = q τ ^ 2 := by
      rw [← Complex.exp_nat_mul, hq, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hR := kleinJRemainderPoly_spec (q τ)
    rw [hR, kleinJ_eq_jacobiTheta, jacobiThetaOneDerivNullTau_eq_mul τ.im_pos, h2, h3, h4]
    simp only [Dn, N, v, w, c, d, e, mul_pow, h8] at hτ ⊢
    rw [_root_.zpow_neg, zpow_ofNat]
    have hB0 : B τ ≠ 0 := fun h => hτ (by simp [h])
    have hT0 : T τ ≠ 0 := fun h => hτ (by simp [h])
    have hU0 : U τ ≠ 0 := fun h => hτ (by simp [h])
    have hq1 := hqne τ
    field_simp
    ring
  have hN : ContDiffAt ℂ 1 N ((0 : ℂ), (2 : ℂ), (1 : ℂ), (1 : ℂ)) := by
    simp only [N]; fun_prop
  obtain ⟨K, t, ht, hL⟩ := hN.exists_lipschitzOnWith
  have hdiff : (fun τ => N (v τ) - N (w τ)) =O[atImInfty] fun τ => q τ ^ 8 := by
    have hsum : (fun τ => ‖B τ - c (q τ)‖ + ‖T τ - d (q τ)‖ + ‖U τ - e (q τ)‖)
        =O[atImInfty] fun τ => q τ ^ 8 :=
      (hB.norm_left.add hT.norm_left).add hU.norm_left
    refine IsBigO.trans ?_ hsum
    refine IsBigO.of_bound K ?_
    filter_upwards [hv ht, hw ht] with τ h1 h2
    have hd := hL.dist_le_mul _ h1 _ h2
    rw [dist_eq_norm] at hd
    refine hd.trans ?_
    have n1 := norm_nonneg (B τ - c (q τ))
    have n2 := norm_nonneg (T τ - d (q τ))
    have n3 := norm_nonneg (U τ - e (q τ))
    have hdist : dist (v τ) (w τ) ≤ ‖B τ - c (q τ)‖ + ‖T τ - d (q τ)‖ + ‖U τ - e (q τ)‖ := by
      simp only [v, w, dist_eq_norm, Prod.mk_sub_mk, Prod.norm_mk, sub_self, norm_zero]
      refine max_le (by positivity) (max_le (by linarith) (max_le (by linarith) (by linarith)))
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hdist K.2
  have hRc : Continuous kleinJRemainderPoly := by
    unfold kleinJRemainderPoly; fun_prop
  have hR8 : (fun τ => q τ ^ 8 * kleinJRemainderPoly (q τ ^ 2)) =O[atImInfty]
      fun τ => q τ ^ 8 := by
    simpa using (isBigO_refl (fun τ => q τ ^ 8) atImInfty).mul
      ((((hRc.tendsto 0).comp (by simpa using hq0.pow 2))).isBigO_one ℂ)
  have h1 : (fun τ => (q τ ^ 8 * kleinJRemainderPoly (q τ ^ 2) + (N (v τ) - N (w τ))) *
      (q τ ^ 2)⁻¹) =O[atImInfty] fun τ => q τ ^ 6 := by
    refine ((hR8.add hdiff).mul (isBigO_refl (fun τ => (q τ ^ 2)⁻¹) atImInfty)).congr_right
      fun τ => ?_
    have := hqne τ
    field_simp
  have h2 : (fun τ => (Dn (v τ))⁻¹) =O[atImInfty] fun _ => (1 : ℂ) := by
    have : Tendsto (fun τ => Dn (v τ)) atImInfty (𝓝 (Dn ((0 : ℂ), (2 : ℂ), (1 : ℂ), (1 : ℂ)))) :=
      ((by fun_prop : Continuous Dn).tendsto _).comp hv
    exact (this.inv₀ (by norm_num [Dn])).isBigO_one ℂ
  have h3 := h1.mul h2
  simp only [mul_one] at h3
  refine h3.congr' (key.mono fun τ h => ?_) EventuallyEq.rfl
  simp only [hq] at h ⊢
  rw [h, mul_assoc]

end DLMF.Weierstrass
