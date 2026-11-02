/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Basic.GeneratingFunctions
public import DLMF.QSeries.Identities
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# The square of `ϑ` as a Lambert series (DLMF §27.13(iv))

This file proves Jacobi's Lambert series for the square of `ϑ(x) = 1 + 2 ∑_{m≥1} x^{m²}`,
`ϑ(x)² = 1 + 4 ∑_{m≥1} x^m/(1 + x^{2m})`, and regroups the Lambert series by divisors. It is the
analytic input for Jacobi's two-square formula `r₂(n) = 4(δ₁(n) - δ₃(n))` (DLMF 27.13.6–27.13.7)
in `DLMF.NumberTheory.Additive`.

The route is the classical one: Ramanujan's `₁ψ₁` summation with base `x²`, `a = -1`, `b = -x²`,
`z = x` gives the bilateral sum `∑_{n∈ℤ} 2xⁿ/(1 + x^{2n})` as a product quotient; the Jacobi
triple product gives `ϑ(x) = (x²;x²)_∞ (-x;x²)_∞²`, and Euler's identity
`(-x;x²)_∞ (-x²;x²)_∞ (x;x²)_∞ = 1` identifies the quotient with `ϑ(x)²`.

## Main results

* `euler_qPochhammerInf_odd`: Euler's identity `(-x;x²)_∞ (-x²;x²)_∞ (x;x²)_∞ = 1`.
* `jacobiThetaSeries_eq_qPochhammerInf`: `ϑ(x) = (x²;x²)_∞ (-x;x²)_∞²` for `0 < |x| < 1`.
* `hasSum_jacobiThetaSeries_sq_lambert`: `ϑ(x)² - 1 = 4 ∑_{m≥1} x^m/(1 + x^{2m})`.
* `exists_hasSum_lambert_divisors`: `∑_{m≥1} x^m/(1 + x^{2m}) = ∑_{n≥1} (δ₁(n) - δ₃(n)) xⁿ`.
-/

@[expose] public noncomputable section

open Complex Finset DLMF.QSeries
open scoped Real

namespace DLMF.NumberTheory

/-- `(w;q)_∞` as an unconditional product. -/
private lemma hasProd_qPochhammerInf' (w : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun k : ℕ => 1 - w * q ^ k) (qPochhammerInf w q) :=
  (multipliable_one_sub_mul_pow hq).hasProd

/-- `|x²| < 1` for `|x| < 1`. -/
private lemma norm_sq_lt_one {x : ℂ} (hx : ‖x‖ < 1) : ‖x ^ 2‖ < 1 := by
  rw [norm_pow]; nlinarith [norm_nonneg x]

/-- Even/odd splitting `(w;q)_∞ = (w;q²)_∞ (wq;q²)_∞`. -/
private lemma qPochhammerInf_eq_mul_sq (w : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf w q = qPochhammerInf w (q ^ 2) * qPochhammerInf (w * q) (q ^ 2) := by
  have h2 := norm_sq_lt_one hq
  refine (hasProd_qPochhammerInf' w hq).unique ?_
  refine HasProd.even_mul_odd ?_ ?_
  · convert hasProd_qPochhammerInf' w h2 using 2 with k; rw [pow_mul]
  · convert hasProd_qPochhammerInf' (w * q) h2 using 2 with k; rw [pow_succ, pow_mul]; ring

/-- `(w;q)_∞ (-w;q)_∞ = (w²;q²)_∞`. -/
private lemma qPochhammerInf_mul_neg (w : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf w q * qPochhammerInf (-w) q = qPochhammerInf (w ^ 2) (q ^ 2) := by
  refine ((hasProd_qPochhammerInf' w hq).mul (hasProd_qPochhammerInf' (-w) hq)).unique ?_
  convert hasProd_qPochhammerInf' (w ^ 2) (norm_sq_lt_one hq) using 2 with k
  rw [← pow_mul, mul_comm 2 k, pow_mul]; ring

/-- Euler: `(-x;x²)_∞ (-x²;x²)_∞ (x;x²)_∞ = 1`. -/
theorem euler_qPochhammerInf_odd {x : ℂ} (hx : ‖x‖ < 1) :
    qPochhammerInf (-x) (x ^ 2) * qPochhammerInf (-x ^ 2) (x ^ 2) * qPochhammerInf x (x ^ 2) =
      1 := by
  have h1 := qPochhammerInf_eq_mul_sq (-x) hx
  have h2 := qPochhammerInf_eq_mul_sq x hx
  have h3 := qPochhammerInf_mul_neg x hx
  have hne := qPochhammerInf_ne_zero_of_norm_lt_one (norm_sq_lt_one hx) (norm_sq_lt_one hx)
  rw [show -x * x = -x ^ 2 by ring] at h1
  rw [show x * x = x ^ 2 by ring] at h2
  rw [← h1]
  apply mul_left_cancel₀ hne
  calc qPochhammerInf (x ^ 2) (x ^ 2) * (qPochhammerInf (-x) x * qPochhammerInf x (x ^ 2))
      = qPochhammerInf x x * qPochhammerInf (-x) x := by rw [h2]; ring
    _ = _ := by rw [h3, mul_one]

/-- `ϑ(x) = (x²;x²)_∞ (-x;x²)_∞²` for `0 < |x| < 1`. -/
theorem jacobiThetaSeries_eq_qPochhammerInf {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    jacobiThetaSeries x =
      qPochhammerInf (x ^ 2) (x ^ 2) * qPochhammerInf (-x) (x ^ 2) ^ 2 := by
  set τ : ℂ := Complex.log x / (π * I) with hτ
  have hπ : (π : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero
  have hE : cexp (π * I * τ) = x := by
    rw [hτ, mul_div_cancel₀ _ hπ, exp_log hx0]
  have hQ : cexp (2 * π * I * τ) = x ^ 2 := by
    rw [show 2 * π * I * τ = (2 : ℕ) * (π * I * τ) by push_cast; ring, Complex.exp_nat_mul, hE]
  have him : 0 < τ.im := by
    have hτ' : τ = -(Complex.log x) * I / π := by
      rw [hτ]; field_simp; rw [I_sq]; ring
    rw [hτ', div_ofReal_im]
    simp only [neg_mul, neg_im, mul_im, I_re, mul_zero, I_im, mul_one, log_re, add_zero]
    have : Real.log ‖x‖ < 0 := Real.log_neg (norm_pos_iff.mpr hx0) hx
    have := Real.pi_pos
    rw [neg_div]; exact neg_pos.mpr (div_neg_of_neg_of_pos (by assumption) this)
  rw [← hE, ← jacobiTheta_eq_jacobiThetaSeries him,
    jacobiTheta_eq_qPochhammer him, hQ, hE]
  ring
/-- `1 + Qᵏ ≠ 0` for `|Q| < 1` and every integer `k`. -/
private lemma one_add_zpow_ne_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (k : ℤ) :
    1 + Q ^ k ≠ 0 := by
  intro h
  have h1 : Q ^ k = -1 := by linear_combination h
  have h2 : ‖Q‖ ^ k = 1 := by rw [← norm_zpow, h1, norm_neg, norm_one]
  have hk : k = 0 := by
    rcases (zpow_eq_one_iff_right₀ (norm_nonneg Q) hQ.ne).mp h2 with hk
    exact hk
  rw [hk, zpow_zero] at h1
  norm_num at h1

/-- `(c;Q)_k (1 - cQᵏ) = (1 - c) (cQ;Q)_k`. -/
private lemma qPochhammer_mul_one_sub (c Q : ℂ) (k : ℕ) :
    qPochhammer c Q k * (1 - c * Q ^ k) = (1 - c) * qPochhammer (c * Q) Q k := by
  induction k with
  | zero => simp [qPochhammer_zero]
  | succ k ih =>
    rw [qPochhammer_succ, qPochhammer_succ, ← mul_assoc, ← ih]
    ring

/-- `(-Qᵉ;Q)_k ≠ 0` for `0 < |Q| < 1`. -/
private lemma qPochhammer_neg_ne_zero {Q : ℂ} (hQ0 : Q ≠ 0) (hQ : ‖Q‖ < 1) (e : ℤ)
    (k : ℕ) :
    qPochhammer (-Q ^ e) Q k ≠ 0 := by
  rw [qPochhammer_eq_prod, prod_ne_zero_iff]
  intro j _
  rw [show 1 - -Q ^ e * Q ^ j = 1 + Q ^ (e + j) by rw [zpow_add₀ hQ0]; simp]
  exact one_add_zpow_ne_zero hQ _

/-- `(-1;Q)_n / (-Q;Q)_n = 2/(1 + Qⁿ)` for every integer `n`. -/
private lemma qPochhammerInt_ratio {Q : ℂ} (hQ0 : Q ≠ 0) (hQ : ‖Q‖ < 1) (n : ℤ) :
    qPochhammerInt (-1) Q n / qPochhammerInt (-Q) Q n = 2 / (1 + Q ^ n) := by
  have hn := one_add_zpow_ne_zero hQ n
  rcases n with m | m
  · have h := qPochhammer_mul_one_sub (-1) Q m
    have hne : qPochhammer (-Q) Q m ≠ 0 := by
      simpa using qPochhammer_neg_ne_zero hQ0 hQ 1 m
    simp only [Int.ofNat_eq_natCast, zpow_natCast] at hn ⊢
    simp only [qPochhammerInt]
    rw [div_eq_div_iff hne hn]
    rw [show -1 * Q = -Q by ring] at h
    linear_combination h
  · set c : ℂ := -Q ^ (-(m + 1 : ℤ)) with hc
    have h := qPochhammer_mul_one_sub c Q (m + 1)
    have hne : qPochhammer c Q (m + 1) ≠ 0 := qPochhammer_neg_ne_zero hQ0 hQ _ _
    have hne' : qPochhammer (c * Q) Q (m + 1) ≠ 0 := by
      rw [hc, show -Q ^ (-(m + 1 : ℤ)) * Q = -Q ^ (-(m + 1 : ℤ) + 1) by
        rw [zpow_add_one₀ hQ0]; ring]
      exact qPochhammer_neg_ne_zero hQ0 hQ _ _
    have hcQ : c * Q ^ (m + 1) = -1 := by
      rw [hc, ← zpow_natCast, neg_mul, ← zpow_add₀ hQ0]; push_cast; simp
    rw [hcQ] at h
    have hneg : Int.negSucc m = -(m + 1 : ℤ) := rfl
    simp only [qPochhammerInt]
    rw [hneg] at hn ⊢
    rw [show -1 * Q ^ (-(m + 1 : ℤ)) = c by rw [hc]; ring,
      show -Q * Q ^ (-(m + 1 : ℤ)) = c * Q by rw [hc]; ring]
    rw [inv_div_inv, div_eq_div_iff hne hn]
    rw [show 1 + Q ^ (-(m + 1 : ℤ)) = 1 - c by rw [hc]; ring]
    linear_combination -h

/-- `|1 + x^{2(n+1)}| ≥ 1 - |x|²`. -/
private lemma norm_one_add_pow_ge {x : ℂ} (hx : ‖x‖ < 1) (n : ℕ) :
    1 - ‖x‖ ^ 2 ≤ ‖1 + x ^ (2 * (n + 1))‖ := by
  have h1 : ‖x‖ ^ (2 * (n + 1)) ≤ ‖x‖ ^ 2 :=
    pow_le_pow_of_le_one (norm_nonneg x) hx.le (by omega : 2 ≤ 2 * (n + 1))
  have h2 := norm_sub_norm_le (1 : ℂ) (-x ^ (2 * (n + 1)))
  rw [sub_neg_eq_add, norm_neg, norm_one, norm_pow] at h2
  linarith

/-- `∑_{n≥0} 2xⁿ/(1 + x^{2n})` converges for `|x| < 1`. -/
private lemma summable_two_pow_div {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n : ℕ => 2 * x ^ n / (1 + x ^ (2 * n)) := by
  rw [← summable_nat_add_iff 1]
  have hpos : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left (2 / (1 - ‖x‖ ^ 2))) fun n => ?_
  have h := norm_one_add_pow_ge hx n
  rw [norm_div, norm_mul, norm_pow, Complex.norm_ofNat, div_le_iff₀ (by linarith)]
  calc 2 * ‖x‖ ^ (n + 1) ≤ 2 * ‖x‖ ^ n := by
        have : ‖x‖ ^ (n + 1) ≤ ‖x‖ ^ n := pow_le_pow_of_le_one (norm_nonneg x) hx.le (by omega)
        linarith
    _ = 2 / (1 - ‖x‖ ^ 2) * ‖x‖ ^ n * (1 - ‖x‖ ^ 2) := by field_simp
    _ ≤ _ := by gcongr

/-- The terms of the bilateral Lambert series at negative indices. -/
private lemma two_div_zpow_neg {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) (n : ℕ) :
    2 / (1 + (x ^ 2) ^ (-(n : ℤ))) * x ^ (-(n : ℤ)) = 2 * x ^ n / (1 + x ^ (2 * n)) := by
  have hQ := norm_sq_lt_one hx
  have h1 : 1 + x ^ (2 * n) ≠ 0 := by
    have := one_add_zpow_ne_zero hQ (n : ℤ); rwa [zpow_natCast, ← pow_mul] at this
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← pow_mul]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx0
  have hx2n : x ^ (2 * n) ≠ 0 := pow_ne_zero _ hx0
  rw [show x ^ (2 * n) = x ^ n * x ^ n by rw [← pow_add]; ring_nf]
  rw [show x ^ (2 * n) = x ^ n * x ^ n by rw [← pow_add]; ring_nf] at h1
  have h2 : 1 + (x ^ n * x ^ n)⁻¹ ≠ 0 := by
    rw [show 1 + (x ^ n * x ^ n)⁻¹ = (1 + x ^ n * x ^ n) / (x ^ n * x ^ n) by field_simp; ring]
    exact div_ne_zero h1 (mul_ne_zero hxn hxn)
  field_simp
  ring

/-- The terms of the bilateral Lambert series at nonnegative indices. -/
private lemma two_div_zpow_natCast {x : ℂ} (n : ℕ) :
    2 / (1 + (x ^ 2) ^ (n : ℤ)) * x ^ (n : ℤ) = 2 * x ^ n / (1 + x ^ (2 * n)) := by
  rw [zpow_natCast, zpow_natCast, ← pow_mul]; ring

/-- The bilateral Lambert series `∑_{n∈ℤ} 2xⁿ/(1 + x^{2n}) = ϑ(x)²` (from `₁ψ₁`). -/
private lemma hasSum_int_two_pow_div {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℤ => 2 / (1 + (x ^ 2) ^ n) * x ^ n)
      (jacobiThetaSeries x ^ 2) := by
  have hQ := norm_sq_lt_one hx
  have hQ0 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have hsym := two_div_zpow_neg hx0 hx
  have hpos := two_div_zpow_natCast (x := x)
  have hsum : Summable (fun n : ℤ => 2 / (1 + (x ^ 2) ^ n) * x ^ n) := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨by simpa only [hpos] using summable_two_pow_div hx,
      by simpa only [hsym] using summable_two_pow_div hx⟩
  convert hsum.hasSum using 1
  have h := ramanujan_1psi1_of_regular (a := -1) (b := -x ^ 2) (z := x) hQ0 hQ
    (by norm_num) (fun n h => by
      have := congrArg norm h
      rw [norm_neg, norm_one, norm_pow] at this
      exact absurd this.symm (pow_lt_one₀ (norm_nonneg _) hQ (Nat.succ_ne_zero n)).ne)
    (fun n h => by
      have := norm_mul_pow_lt_one (w := -x ^ 2) (by rwa [norm_neg]) hQ n
      rw [h, norm_one] at this
      exact lt_irrefl _ this)
    ⟨by
      rw [neg_div_neg_eq, div_one, norm_pow]
      nlinarith [norm_pos_iff.mpr hx0], hx⟩
  have hratio : ∀ n : ℤ, qPochhammerInt (-1) (x ^ 2) n / qPochhammerInt (-x ^ 2) (x ^ 2) n *
      x ^ n = 2 / (1 + (x ^ 2) ^ n) * x ^ n := fun n => by
    rw [qPochhammerInt_ratio hQ0 hQ n]
  simp only [hratio] at h
  rw [h]
  have e1 : -x ^ 2 / -1 = x ^ 2 := by ring
  have e2 : -1 * x = -x := by ring
  have e3 : x ^ 2 / -x = -x := by field_simp
  have e4 : x ^ 2 / -1 = -x ^ 2 := by ring
  have e5 : -x ^ 2 / -x = x := by field_simp
  rw [e1, e2, e3, e4, e5, jacobiThetaSeries_eq_qPochhammerInf hx0 hx]
  have hE := euler_qPochhammerInf_odd hx
  have n1 := qPochhammerInf_ne_zero_of_norm_lt_one (norm_neg (x ^ 2) ▸ hQ) hQ
  have n2 := qPochhammerInf_ne_zero_of_norm_lt_one hx hQ
  rw [eq_div_iff (by simp [n1, n2])]
  linear_combination ((qPochhammerInf (x ^ 2) (x ^ 2) ^ 2 * qPochhammerInf (-x) (x ^ 2) ^ 2) *
    (qPochhammerInf (-x) (x ^ 2) * qPochhammerInf (-x ^ 2) (x ^ 2) * qPochhammerInf x (x ^ 2)
      + 1)) * hE

/-- DLMF §27.13(iv): `ϑ(x)² - 1 = 4 ∑_{m≥1} x^m/(1 + x^{2m})` for `0 < |x| < 1`. -/
theorem hasSum_jacobiThetaSeries_sq_lambert {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    HasSum (fun m : ℕ => 4 * (x ^ (m + 1) / (1 + x ^ (2 * (m + 1)))))
      (jacobiThetaSeries x ^ 2 - 1) := by
  have h := (hasSum_int_two_pow_div hx0 hx).nat_add_neg
  have h0 : (2 : ℂ) / (1 + (x ^ 2) ^ (0 : ℤ)) * x ^ (0 : ℤ) = 1 := by norm_num
  simp only [two_div_zpow_neg hx0 hx, two_div_zpow_natCast, h0] at h
  have h' := (hasSum_nat_add_iff' 1).mpr (h.congr_fun fun n => by ring :
    HasSum (fun n : ℕ => 4 * x ^ n / (1 + x ^ (2 * n))) _)
  convert h' using 1
  · funext m; ring
  · simp; ring

/-- The non-principal character mod 4, `δ₁ - δ₃` pointwise. -/
private def chiFour (d : ℕ) : ℂ := (if d % 4 = 1 then 1 else 0) - (if d % 4 = 3 then 1 else 0)

/-- `χ₄(2k+1) = (-1)ᵏ`. -/
private lemma chiFour_odd (k : ℕ) : chiFour (2 * k + 1) = (-1) ^ k := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show 2 * (j + j) + 1 = 4 * j + 1 by ring, ← two_mul, pow_mul]
    simp [chiFour, Nat.add_mod]
  · rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring, pow_succ, pow_mul]
    simp [chiFour, Nat.add_mod]

/-- `χ₄` vanishes on even numbers. -/
private lemma chiFour_even (k : ℕ) : chiFour (2 * k) = 0 := by
  have h1 : (2 * k) % 4 ≠ 1 := by omega
  have h3 : (2 * k) % 4 ≠ 3 := by omega
  simp [chiFour, h1, h3]

/-- `∑_{d≥0} χ₄(d) y^d = y/(1 + y²)` for `|y| < 1`. -/
private lemma hasSum_chiFour_mul_pow {y : ℂ} (hy : ‖y‖ < 1) :
    HasSum (fun d : ℕ => chiFour d * y ^ d) (y / (1 + y ^ 2)) := by
  have hy2 : ‖-y ^ 2‖ < 1 := by rw [norm_neg, norm_pow]; nlinarith [norm_nonneg y]
  have hg := (hasSum_geometric_of_norm_lt_one hy2).mul_left y
  have hinj : Function.Injective fun k : ℕ => 2 * k + 1 := fun a b h => by simp at h; omega
  rw [← hinj.hasSum_iff]
  · convert hg using 1
    · funext k
      simp only [Function.comp_apply, chiFour_odd]
      rw [neg_pow, pow_succ, pow_mul]; ring
    · rw [sub_neg_eq_add, div_eq_mul_inv]
  · intro d hd
    obtain ⟨k, rfl⟩ : Even d := by
      rcases Nat.even_or_odd d with h | ⟨k, rfl⟩
      · exact h
      · exact absurd ⟨k, rfl⟩ hd
    rw [← two_mul, chiFour_even, zero_mul]

/-- `∑_{d ∣ n} χ₄(d) = δ₁(n) - δ₃(n)`. -/
private lemma sum_divisors_chiFour (n : ℕ) :
    ∑ d ∈ n.divisors, chiFour d =
      ((n.divisors.filter (· % 4 = 1)).card : ℂ) - (n.divisors.filter (· % 4 = 3)).card := by
  simp only [chiFour, sum_sub_distrib, sum_boole]

/-- The Lambert series `∑_{m≥1} x^m/(1+x^{2m})` regrouped by divisors:
`∑_{n≥1} (δ₁(n) - δ₃(n)) xⁿ`, with `δ_j(n)` the number of divisors `≡ j (mod 4)`. -/
theorem exists_hasSum_lambert_divisors {x : ℂ} (hx : ‖x‖ < 1) :
    ∃ A : ℂ, HasSum (fun m : ℕ => x ^ (m + 1) / (1 + x ^ (2 * (m + 1)))) A ∧
      HasSum (fun n : ℕ => (((n + 1).divisors.filter (· % 4 = 1)).card -
        ((n + 1).divisors.filter (· % 4 = 3)).card : ℂ) * x ^ (n + 1)) A := by
  set F : ℕ+ × ℕ+ → ℂ := fun c => chiFour c.2 * x ^ ((c.1 : ℕ) * c.2) with hF
  have hsF : Summable F := by
    have hr : ‖(‖x‖ : ℝ)‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg x)]
    refine Summable.of_norm_bounded (by simpa using summable_prod_mul_pow 0 hr) fun c => ?_
    simp only [hF, norm_mul, norm_pow]
    refine mul_le_of_le_one_left (by positivity) ?_
    simp only [chiFour]; split_ifs <;> norm_num
  obtain ⟨A, hA⟩ := hsF
  refine ⟨A, ?_, ?_⟩
  · have hfib : ∀ m : ℕ+, HasSum (fun d : ℕ+ => F (m, d))
        (x ^ (m : ℕ) / (1 + x ^ (2 * (m : ℕ)))) := by
      intro m
      have hy : ‖x ^ (m : ℕ)‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx m.ne_zero
      have h := hasSum_chiFour_mul_pow hy
      rw [← pow_mul, mul_comm (m : ℕ) 2] at h
      have h' := (hasSum_pnat_iff (f := fun d : ℕ => chiFour d * (x ^ (m : ℕ)) ^ d)).mpr
        (by simpa [chiFour] using h)
      simpa [hF, pow_mul] using h'
    have := hA.prod_fiberwise hfib
    exact (hasSum_pnat_iff_hasSum_succ (f := fun m : ℕ => x ^ m / (1 + x ^ (2 * m)))).mp this
  · have hS := (sigmaAntidiagonalEquivProd.hasSum_iff (f := F)).mpr hA
    have hfib : ∀ n : ℕ+, HasSum (fun p : Nat.divisorsAntidiagonal n =>
        (F ∘ sigmaAntidiagonalEquivProd) ⟨n, p⟩)
        ((((n : ℕ).divisors.filter (· % 4 = 1)).card -
          ((n : ℕ).divisors.filter (· % 4 = 3)).card : ℂ) * x ^ (n : ℕ)) := by
      intro n
      convert hasSum_fintype _ using 1
      rw [← sum_divisors_chiFour, sum_mul]
      simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors,
        Equiv.coe_fn_mk, hF, PNat.mk_coe]
      rw [Finset.univ_eq_attach]
      rw [(n : ℕ).divisorsAntidiagonal.sum_attach
        (fun p : ℕ × ℕ => chiFour p.2 * x ^ (p.1 * p.2)),
        Nat.sum_divisorsAntidiagonal' (fun a b => chiFour b * x ^ (a * b))]
      refine sum_congr rfl fun d hd => ?_
      rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
    have := hS.sigma hfib
    exact (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ =>
      ((n.divisors.filter (· % 4 = 1)).card - (n.divisors.filter (· % 4 = 3)).card : ℂ) *
        x ^ n)).mp this

end DLMF.NumberTheory
