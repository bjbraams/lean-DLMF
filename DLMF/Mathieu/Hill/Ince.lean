/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Hill.Basic
public import DLMF.Mathieu.SpectralExistence
public import DLMF.Mathieu.Noninteger.Properties

/-!
# The equations of Whittaker–Hill and Ince (DLMF §28.31)

Statements of DLMF §28.31 for the definitions in `DLMF.Mathieu.Hill.Basic`: the reduction of
the Whittaker–Hill equation 28.31.1 to Ince's equation 28.31.3 (28.31.2), the Fourier-series
solutions and their coefficient recurrences (28.31.4–28.31.9), the Ince polynomials
`C_p^m`, `S_p^m` and their eigenvalues `a_p^m`, `b_p^m` (28.31.10–28.31.15), and the
paraboloidal wave functions `hc_p^m`, `hs_p^m` (28.31.16–28.31.24 and the asymptotic
behaviour). The limits 28.31.14–28.31.15 use the Mathieu functions `ce_m`, `se_m` and
eigenvalues `a_m`, `b_m` of `DLMF.Mathieu.Basic` (real `q`).

The admissible indices are `m ≤ p`, `m ≡ p (mod 2)` (and `m ≥ 1` for `S_p^m`, `hs_p^m`), as in
DLMF 28.31.10–28.31.11 (`m = 0, 1, …, n` with `p = 2n`, `2n + 1`, `2n + 2`).

**Correction (§28.31(iii), Asymptotic Behavior, second paragraph).** DLMF says that for
`ξ > 0` the functions `hc_p^m(z, -ξ)`, `hs_p^m(z, -ξ)` behave as multiples of
`exp(¼ξ cos 2z) (cos z)^{-p-2}` as `z → ½π ± i∞`, and all other periodic solutions as
multiples of `exp(-¼ξ cos 2z) (cos z)^p`. By the reflection formulas 28.31.19–28.31.20
(`z ↦ ½π - z`, under which `cos 2z ↦ -cos 2z` and `cos z ↦ sin z`) and the first paragraph,
the correct factors are `exp(¼ξ cos 2z) (sin z)^p` for `hc_p^m(z, -ξ)`, `hs_p^m(z, -ξ)`, and
`exp(-¼ξ cos 2z) (sin z)^{-p-2}` for the other periodic solutions. Numerically
(`ξ = 0.8`, `p = 2, 3, 4`, all `m`, `z = ½π + iy`, `y = 2, 3, 4`), the ratio
`hc_p^m(z, -ξ) / (exp(¼ξ cos 2z) (sin z)^p)` converges (e.g. `-0.416, -0.472, -0.480` for
`hc_2^0`) while the ratio with DLMF's factor `exp(¼ξ cos 2z) (cos z)^{-p-2}` grows like
`e^{(2p+2)y}`. The corrected form is acquired (`paraboloidal_asymptotic_neg`).

All other formulas of §28.31 were checked: 28.31.3 and the recurrences 28.31.6–28.31.9
symbolically (sympy), and 28.31.13 and the reflection formulas 28.31.19–28.31.20 numerically
(finite eigenproblems for `p ≤ 6`, `ξ = 0.8`).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Topology Classical

namespace DLMF.Mathieu

/-! ### §28.31(i)–(ii) Whittaker–Hill and Ince equations -/

/-- `cos 4z = 1 - 2 sin² 2z`. -/
lemma m28b_cos_four (z : ℂ) : Complex.cos (4 * z) = 1 - 2 * Complex.sin (2 * z) ^ 2 := by
  rw [show (4 : ℂ) * z = 2 * (2 * z) by ring, Complex.cos_two_mul]
  have := Complex.sin_sq_add_cos_sq (2 * z)
  linear_combination (2 : ℂ) * this

/-- The derivative of `-ξ cos(2z)/4`. -/
lemma m28b_hasDerivAt_g (ξ z : ℂ) :
    HasDerivAt (fun z => -(ξ * Complex.cos (2 * z)) / 4) (ξ * Complex.sin (2 * z) / 2) z := by
  have h2 : HasDerivAt (fun z : ℂ => 2 * z) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have := ((h2.ccos).const_mul ξ).neg.div_const 4
  convert this using 1; ring

/-- The derivative of `ξ sin(2z)/2`. -/
lemma m28b_hasDerivAt_g' (ξ z : ℂ) :
    HasDerivAt (fun z => ξ * Complex.sin (2 * z) / 2) (ξ * Complex.cos (2 * z)) z := by
  have h2 : HasDerivAt (fun z : ℂ => 2 * z) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have := ((h2.csin).const_mul ξ).div_const 2
  convert this using 1; ring

/-- **Reduction to Ince's equation** (DLMF 28.31.2–28.31.3): with `ξ² = -4k²c²`,
`A = η - ξ²/8`, `B = -(p+1)ξ` and `W(z) = w(z) exp(-¼ξ cos 2z)`, `W` solves the Whittaker–Hill
equation 28.31.1 iff `w` solves Ince's equation 28.31.3. (DLMF makes the substitution for
`k² < 0`; the algebra holds for all complex parameters.) Proved. -/
@[dlmf 28.31.E2]
theorem isWhittakerHillSolution_iff_isInceSolution {k c ξ η p : ℂ}
    (hξ : ξ ^ 2 = -4 * k ^ 2 * c ^ 2) {w : ℂ → ℂ} :
    IsWhittakerHillSolution (η - ξ ^ 2 / 8) (-(p + 1) * ξ) k c
        (fun z => w z * Complex.exp (-(ξ * Complex.cos (2 * z)) / 4)) ↔
      IsInceSolution ξ η p w := by
  set g : ℂ → ℂ := fun z => -(ξ * Complex.cos (2 * z)) / 4
  set g' : ℂ → ℂ := fun z => ξ * Complex.sin (2 * z) / 2
  set E : ℂ → ℂ := fun z => Complex.exp (g z)
  have hE : ∀ z, HasDerivAt E (E z * g' z) z := fun z => (m28b_hasDerivAt_g ξ z).cexp
  have hF : ∀ z, HasDerivAt (fun z => Complex.exp (-g z)) (Complex.exp (-g z) * -g' z) z :=
    fun z => (m28b_hasDerivAt_g ξ z).neg.cexp
  have hg' : ∀ z, HasDerivAt g' (ξ * Complex.cos (2 * z)) z := m28b_hasDerivAt_g' ξ
  have hEF : ∀ z, E z * Complex.exp (-g z) = 1 := fun z => by
    simp only [E]; rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  constructor
  · rintro ⟨hWd, hW⟩
    set W : ℂ → ℂ := fun z => w z * E z
    have hw : w = fun z => W z * Complex.exp (-g z) := by
      funext z; simp only [W]; rw [mul_assoc, hEF, mul_one]
    have hWd' : ∀ z, HasDerivAt W (deriv W z) z := fun z => (hWd z).hasDerivAt
    have hw' : ∀ z, HasDerivAt w ((deriv W z - g' z * W z) * Complex.exp (-g z)) z := by
      intro z; rw [hw]
      convert (hWd' z).mul (hF z) using 1; ring
    have hdw : deriv w = fun z => (deriv W z - g' z * W z) * Complex.exp (-g z) :=
      funext fun z => (hw' z).deriv
    refine ⟨fun z => (hw' z).differentiableAt, fun z => ?_⟩
    rw [hdw]
    have := (((hW z).sub ((hg' z).mul (hWd' z))).mul (hF z))
    convert this using 1
    have h4 := m28b_cos_four z
    have hwz : w z = W z * Complex.exp (-g z) := congrFun hw z
    rw [hwz]
    simp only [W, g', Pi.sub_apply, Pi.mul_apply]
    rw [h4]
    linear_combination
      (-1/8 * w z * E z * Complex.exp (-g z) * (1 - 2 * Complex.sin (2 * z) ^ 2)) * hξ
  · rintro ⟨hwd, hw⟩
    have hwd' : ∀ z, HasDerivAt w (deriv w z) z := fun z => (hwd z).hasDerivAt
    have hW' : ∀ z, HasDerivAt (fun z => w z * E z) ((deriv w z + w z * g' z) * E z) z := by
      intro z; convert (hwd' z).mul (hE z) using 1; ring
    have hdW : deriv (fun z => w z * E z) = fun z => (deriv w z + w z * g' z) * E z :=
      funext fun z => (hW' z).deriv
    refine ⟨fun z => (hW' z).differentiableAt, fun z => ?_⟩
    rw [hdW]
    have := (((hw z).add ((hwd' z).mul (hg' z))).mul (hE z))
    convert this using 1
    have h4 := m28b_cos_four z
    simp only [g', Pi.mul_apply, Pi.add_apply]
    rw [h4]
    linear_combination (1/8 * w z * E z * (1 - 2 * Complex.sin (2 * z) ^ 2)) * hξ


/-! ### Exponential-series solutions of Ince's equation -/

/-- Subsequences `A_{2ℓ+b}` of entire Fourier coefficients decay faster than every
exponential in `ℓ`. -/
lemma p1b_summable_coeff {A : ℕ → ℂ} (hA : IsEntireFourierCoeff A) (b : ℕ) (K : ℝ) :
    Summable (fun ℓ : ℕ => ‖A (2 * ℓ + b)‖ * Real.exp (K * ℓ)) := by
  have hinj : Function.Injective (fun ℓ : ℕ => 2 * ℓ + b) := fun i j h => by
    simp only at h; omega
  refine .of_nonneg_of_le (fun _ => by positivity) (fun ℓ => ?_) ((hA |K|).comp_injective hinj)
  simp only [Function.comp]
  have h1 : (1 : ℝ) ≤ (((2 * ℓ + b : ℕ) : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ ((2 * ℓ + b : ℕ) : ℝ) := by positivity
    nlinarith
  have h2 : Real.exp (K * ℓ) ≤ Real.exp (((2 * ℓ + b : ℕ) : ℝ) * |K|) := by
    apply Real.exp_le_exp.mpr
    push_cast
    have := le_abs_self K
    have : (0 : ℝ) ≤ ℓ := by positivity
    nlinarith [abs_nonneg K]
  calc ‖A (2 * ℓ + b)‖ * Real.exp (K * ℓ)
      ≤ ‖A (2 * ℓ + b)‖ * Real.exp (((2 * ℓ + b : ℕ) : ℝ) * |K|) := by gcongr
    _ ≤ ‖A (2 * ℓ + b)‖ * (((2 * ℓ + b : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (((2 * ℓ + b : ℕ) : ℝ) * |K|) := by
      rw [mul_assoc]; gcongr
      calc Real.exp _ = 1 * Real.exp _ := (one_mul _).symm
        _ ≤ _ := by gcongr

/-- Multiplying `∑ g_m e^{i(ν+2m)z}` by `e^{±2iz}` shifts the coefficients. -/
lemma p1b_hasSum_shift {ν z X : ℂ} {g : ℤ → ℂ}
    (h : HasSum (fun m : ℤ => g m * Complex.exp (I * (ν + 2 * m) * z)) X) :
    HasSum (fun n : ℤ => g (n - 1) * Complex.exp (I * (ν + 2 * n) * z))
        (Complex.exp (2 * I * z) * X) ∧
      HasSum (fun n : ℤ => g (n + 1) * Complex.exp (I * (ν + 2 * n) * z))
        (Complex.exp (-(2 * I * z)) * X) := by
  constructor
  · rw [← (Equiv.addRight (1 : ℤ)).hasSum_iff]
    refine (h.mul_left _).congr_fun fun m => ?_
    simp only [Function.comp, Equiv.coe_addRight, add_sub_cancel_right]
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring
  · rw [← (Equiv.subRight (1 : ℤ)).hasSum_iff]
    refine (h.mul_left _).congr_fun fun m => ?_
    simp only [Function.comp, Equiv.subRight_apply, sub_add_cancel]
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring

/-- **Exponential-series solutions of Ince's equation**: for coefficients decaying faster than
every exponential, `∑ c_n e^{i(ν+2n)z}` solves 28.31.3 iff
`(η - (ν+2n)²) c_n + ½ξ(ν+2n-2-p) c_{n-1} - ½ξ(ν+2n+2+p) c_{n+1} = 0` for all `n`. -/
lemma p1b_isInceSolution_series_iff {ξ η p ν : ℂ} {c : ℤ → ℂ}
    (hb : ∀ K : ℝ, Summable (fun m : ℤ => ‖c m‖ * Real.exp (K * |(m : ℝ)|))) :
    IsInceSolution ξ η p (fun z => ∑' n : ℤ, c n * Complex.exp (I * (ν + 2 * n) * z)) ↔
      ∀ n : ℤ, (η - (ν + 2 * n) ^ 2) * c n + ξ * (ν + 2 * ((n : ℂ) - 1) - p) / 2 * c (n - 1)
        - ξ * (ν + 2 * ((n : ℂ) + 1) + p) / 2 * c (n + 1) = 0 := by
  set e : ℤ → ℂ → ℂ := fun m z => Complex.exp (I * (ν + 2 * m) * z) with he
  set S : ℕ → ℂ → ℂ := fun j z => ∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ j * e m z) with hS
  set E : ℤ → ℂ := fun n => (η - (ν + 2 * n) ^ 2) * c n +
    ξ * (ν + 2 * ((n : ℂ) - 1) - p) / 2 * c (n - 1) -
    ξ * (ν + 2 * ((n : ℂ) + 1) + p) / 2 * c (n + 1) with hE
  have h0 : (fun z => ∑' n : ℤ, c n * Complex.exp (I * (ν + 2 * n) * z)) = S 0 := by
    funext z; simp [hS, he]
  have hd : ∀ j z, HasDerivAt (S j) (S (j + 1) z) z := fun j z =>
    p1b_hasDerivAt_series_of hb j z
  have hderiv : deriv (S 0) = S 1 := funext fun z => (hd 0 z).deriv
  have hsum : ∀ j z, HasSum (fun m => c m * ((I * (ν + 2 * m)) ^ j * e m z)) (S j z) :=
    fun j z => (p1b_summable_series_of hb j z).of_norm.hasSum
  -- the operator applied termwise
  have hL : ∀ z, HasSum (fun n => E n * e n z) (S 2 z + ξ * Complex.sin (2 * z) * S 1 z +
      (η - p * ξ * Complex.cos (2 * z)) * S 0 z) := by
    intro z
    have h0' : HasSum (fun m => c m * e m z) (S 0 z) := by simpa using hsum 0 z
    have h1' : HasSum (fun m => (c m * (I * (ν + 2 * m))) * e m z) (S 1 z) := by
      refine (hsum 1 z).congr_fun fun m => ?_; ring
    have h2' := hsum 2 z
    obtain ⟨a1, b1⟩ := p1b_hasSum_shift h1'
    obtain ⟨a0, b0⟩ := p1b_hasSum_shift h0'
    have H := ((h2'.add ((a1.sub b1).mul_left (ξ / (2 * I)))).add (h0'.mul_left η)).sub
      ((a0.add b0).mul_left (p * ξ / 2))
    have hsin : Complex.sin (2 * z) = (Complex.exp (2 * I * z) - Complex.exp (-(2 * I * z))) /
        (2 * I) := by
      rw [Complex.sin, eq_div_iff (by simp [Complex.I_ne_zero])]
      ring_nf; rw [Complex.I_sq]; ring_nf
    have hcos : Complex.cos (2 * z) = (Complex.exp (2 * I * z) + Complex.exp (-(2 * I * z))) /
        2 := by
      rw [Complex.cos]; ring_nf
    convert H using 1
    · funext n
      simp only [hE, he]
      push_cast
      have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [hsin, hcos]
      have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
      field_simp
      ring
  -- summability of the coefficients `E`
  have hu : ∀ j : ℕ, Summable (fun m : ℤ => ‖(ν + 2 * m) ^ j * c m‖) := by
    intro j
    refine (p1b_summable_series_of (ν := ν) hb j 0).congr fun m => ?_
    simp [mul_pow, mul_comm]
  have hsh : ∀ (u : ℤ → ℝ), Summable u → Summable (fun n : ℤ => u (n - 1)) ∧
      Summable (fun n : ℤ => u (n + 1)) := fun u h =>
    ⟨h.comp_injective (sub_left_injective : Function.Injective (fun n : ℤ => n - 1)),
      h.comp_injective (add_left_injective 1 : Function.Injective (fun n : ℤ => n + 1))⟩
  have hEs : Summable (fun n => ‖E n‖) := by
    have b0 := hu 0
    have b1 := hu 1
    have b2 := hu 2
    simp only [pow_zero, one_mul, pow_one] at b0 b1
    have B := ((((b0.mul_left ‖η‖).add b2).add
      (((hsh _ b1).1.add ((hsh _ b0).1.mul_left ‖p‖)).mul_left (‖ξ‖ / 2))).add
      (((hsh _ b1).2.add ((hsh _ b0).2.mul_left ‖p‖)).mul_left (‖ξ‖ / 2)))
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) B
    simp only [hE]
    have e1 : (η - (ν + 2 * n) ^ 2) * c n = η * c n - (ν + 2 * n) ^ 2 * c n := by ring
    have e2 : ξ * (ν + 2 * ((n : ℂ) - 1) - p) / 2 * c (n - 1) =
        ξ / 2 * ((ν + 2 * ((n - 1 : ℤ) : ℂ)) * c (n - 1) - p * c (n - 1)) := by push_cast; ring
    have e3 : ξ * (ν + 2 * ((n : ℂ) + 1) + p) / 2 * c (n + 1) =
        ξ / 2 * ((ν + 2 * ((n + 1 : ℤ) : ℂ)) * c (n + 1) + p * c (n + 1)) := by push_cast; ring
    rw [e1, e2, e3]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add_left (norm_add_le _ _) _).trans ?_
    have t1 : ‖η * c n - (ν + 2 * n) ^ 2 * c n‖ ≤ ‖η‖ * ‖c n‖ + ‖(ν + 2 * n) ^ 2 * c n‖ := by
      rw [← norm_mul]; exact norm_sub_le _ _
    have t2 : ‖ξ / 2 * ((ν + 2 * ((n - 1 : ℤ) : ℂ)) * c (n - 1) - p * c (n - 1))‖ ≤
        ‖ξ‖ / 2 * (‖(ν + 2 * ((n - 1 : ℤ) : ℂ)) * c (n - 1)‖ + ‖p‖ * ‖c (n - 1)‖) := by
      rw [norm_mul, norm_div, Complex.norm_ofNat, ← norm_mul p]
      gcongr; exact norm_sub_le _ _
    have t3 : ‖ξ / 2 * ((ν + 2 * ((n + 1 : ℤ) : ℂ)) * c (n + 1) + p * c (n + 1))‖ ≤
        ‖ξ‖ / 2 * (‖(ν + 2 * ((n + 1 : ℤ) : ℂ)) * c (n + 1)‖ + ‖p‖ * ‖c (n + 1)‖) := by
      rw [norm_mul, norm_div, Complex.norm_ofNat, ← norm_mul p]
      gcongr; exact norm_add_le _ _
    linarith
  constructor
  · rintro ⟨hdiff, hder⟩
    rw [h0] at hder
    rw [hderiv] at hder
    have hz : ∀ z, S 2 z + ξ * Complex.sin (2 * z) * S 1 z +
        (η - p * ξ * Complex.cos (2 * z)) * S 0 z = 0 := fun z => by
      have := (hder z).unique (hd 1 z); linear_combination -this
    intro n
    have hx : ∀ x : ℝ, ∑' m : ℤ, E m * Complex.exp (I * (ν + 2 * m) * x) = 0 := fun x => by
      have := (hL x).tsum_eq
      simp only [he] at this
      rw [this, hz]
    have := p1b_integral_series_mul_exp (ν := ν) hEs n
    simp only [hx, zero_mul, intervalIntegral.integral_zero] at this
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact (mul_eq_zero.mp this.symm).resolve_left hπ
  · intro hE0
    have hE0' : ∀ n, E n = 0 := hE0
    have hz : ∀ z, S 2 z + ξ * Complex.sin (2 * z) * S 1 z +
        (η - p * ξ * Complex.cos (2 * z)) * S 0 z = 0 := fun z => by
      have := hL z
      simp only [hE0', zero_mul] at this
      exact this.unique hasSum_zero
    rw [h0]
    refine ⟨fun z => (hd 0 z).differentiableAt, fun z => ?_⟩
    rw [hderiv]
    convert hd 1 z using 1
    linear_combination -(hz z)

/-- The two-sided sequence with `c_ℓ = a_ℓ` and `c_{-ℓ-1} = b_ℓ`. -/
def p1bTwoSided (a b : ℕ → ℂ) : ℤ → ℂ := fun n => match n with
  | Int.ofNat ℓ => a ℓ
  | Int.negSucc ℓ => b ℓ

/-- `c_ℓ = a_ℓ` for `ℓ ≥ 0`. -/
lemma p1bTwoSided_natCast (a b : ℕ → ℂ) (ℓ : ℕ) : p1bTwoSided a b ℓ = a ℓ := rfl

/-- `c_{-ℓ-1} = b_ℓ`. -/
lemma p1bTwoSided_neg (a b : ℕ → ℂ) (ℓ : ℕ) : p1bTwoSided a b (-(ℓ : ℤ) - 1) = b ℓ := by
  rw [show -(ℓ : ℤ) - 1 = Int.negSucc ℓ by rw [Int.negSucc_eq]; ring]; rfl

/-- Two-sided sequences built from sequences decaying faster than every exponential: decay,
and the exponential series splits into its two halves. -/
lemma p1b_twoSided {a b : ℕ → ℂ}
    (ha : ∀ K : ℝ, Summable (fun ℓ : ℕ => ‖a ℓ‖ * Real.exp (K * ℓ)))
    (hb : ∀ K : ℝ, Summable (fun ℓ : ℕ => ‖b ℓ‖ * Real.exp (K * ℓ))) (ν : ℂ) :
    (∀ K : ℝ, Summable (fun m : ℤ => ‖p1bTwoSided a b m‖ * Real.exp (K * |(m : ℝ)|))) ∧
    ∀ z : ℂ, Summable (fun ℓ : ℕ => a ℓ * Complex.exp (I * (ν + 2 * ℓ) * z)) ∧
      Summable (fun ℓ : ℕ => b ℓ * Complex.exp (I * (ν + 2 * (-(ℓ : ℂ) - 1)) * z)) ∧
      HasSum (fun n : ℤ => p1bTwoSided a b n * Complex.exp (I * (ν + 2 * n) * z))
        (∑' ℓ : ℕ, a ℓ * Complex.exp (I * (ν + 2 * ℓ) * z) +
          ∑' ℓ : ℕ, b ℓ * Complex.exp (I * (ν + 2 * (-(ℓ : ℂ) - 1)) * z)) := by
  refine ⟨fun K => ?_, fun z => ?_⟩
  · refine Summable.of_nat_of_neg_add_one ?_ ?_
    · refine (ha K).congr fun ℓ => ?_
      rw [p1bTwoSided_natCast]; push_cast; rw [abs_of_nonneg (by positivity)]
    · refine ((hb K).mul_left (Real.exp K)).congr fun ℓ => ?_
      rw [show -((ℓ : ℤ) + 1) = -(ℓ : ℤ) - 1 by ring, p1bTwoSided_neg]
      push_cast
      rw [show -((ℓ : ℝ)) - 1 = -((ℓ : ℝ) + 1) by ring, abs_neg,
        abs_of_nonneg (by positivity), mul_add, Real.exp_add]; ring_nf
  have hbd : ∀ (d : ℕ → ℂ), (∀ K : ℝ, Summable (fun ℓ : ℕ => ‖d ℓ‖ * Real.exp (K * ℓ))) →
      ∀ (f : ℕ → ℤ), (∀ ℓ, |((f ℓ : ℤ) : ℝ)| ≤ ℓ + 1) →
      Summable (fun ℓ : ℕ => d ℓ * Complex.exp (I * (ν + 2 * (f ℓ : ℂ)) * z)) := by
    intro d hd f hf
    refine Summable.of_norm_bounded
      (((hd (2 * ‖z‖)).mul_left (Real.exp (‖ν‖ * ‖z‖) * Real.exp (2 * ‖z‖)))) fun ℓ => ?_
    rw [norm_mul]
    have h1 := p1b_norm_pow_exp_le ν z (f ℓ) (le_refl ‖z‖) 0
    simp only [pow_zero, one_mul, CharP.cast_eq_zero, add_zero] at h1
    have h2 : Real.exp (2 * ‖z‖ * |((f ℓ : ℤ) : ℝ)|) ≤
        Real.exp (2 * ‖z‖) * Real.exp (2 * ‖z‖ * ℓ) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have := hf ℓ; nlinarith [norm_nonneg z]
    calc ‖d ℓ‖ * ‖Complex.exp (I * (ν + 2 * (f ℓ : ℂ)) * z)‖
        ≤ ‖d ℓ‖ * (Real.exp (‖ν‖ * ‖z‖) * (Real.exp (2 * ‖z‖) * Real.exp (2 * ‖z‖ * ℓ))) := by
          gcongr; exact h1.trans (by gcongr)
      _ = _ := by ring
  have hf1 : ∀ ℓ : ℕ, |(((ℓ : ℤ) : ℤ) : ℝ)| ≤ ℓ + 1 := fun ℓ => by
    push_cast; rw [abs_of_nonneg (by positivity)]; linarith
  have sa := hbd a ha (fun ℓ => ℓ) hf1
  have sb := hbd b hb (fun ℓ => -(ℓ : ℤ) - 1) (fun ℓ => by
    push_cast
    rw [show -((ℓ : ℝ)) - 1 = -((ℓ : ℝ) + 1) by ring, abs_neg, abs_of_nonneg (by positivity)])
  simp only [Int.cast_natCast] at sa
  push_cast at sb
  refine ⟨sa, sb, ?_⟩
  refine HasSum.of_nat_of_neg_add_one (sa.hasSum.congr_fun fun ℓ => ?_)
    (sb.hasSum.congr_fun fun ℓ => ?_)
  · rw [p1bTwoSided_natCast]; push_cast; rfl
  · rw [show -((ℓ : ℤ) + 1) = -(ℓ : ℤ) - 1 by ring, p1bTwoSided_neg]; push_cast; rfl

/-- Halved subsequences of entire Fourier coefficients. -/
lemma p1b_summable_coeff_mul {A : ℕ → ℂ} (hA : IsEntireFourierCoeff A) (b : ℕ) (κ : ℂ)
    (K : ℝ) : Summable (fun ℓ : ℕ => ‖κ * A (2 * ℓ + b)‖ * Real.exp (K * ℓ)) :=
  ((p1b_summable_coeff hA b K).mul_left ‖κ‖).congr fun ℓ => by rw [norm_mul]; ring

/-- **Even Fourier-series solutions, `s = 0`** (DLMF 28.31.4, 28.31.6):
`w(z) = ∑_ℓ A_{2ℓ} cos(2ℓz)` solves Ince's equation iff
`-2ηA₀ + (2+p)ξA₂ = 0`, `pξA₀ + (4-η)A₂ + (½p+2)ξA₄ = 0` and, for `ℓ ≥ 2`,
`(½p-ℓ+1)ξA_{2ℓ-2} + (4ℓ²-η)A_{2ℓ} + (½p+ℓ+1)ξA_{2ℓ+2} = 0`. -/
@[dlmf 28.31.E4, dlmf 28.31.E6]
theorem isInceSolution_cos_even_iff {ξ η p : ℂ} {A : ℕ → ℂ} (hA : IsEntireFourierCoeff A) :
    IsInceSolution ξ η p (fun z => ∑' ℓ : ℕ, A (2 * ℓ) * Complex.cos ((2 * ℓ : ℕ) * z)) ↔
      (-2 * η * A 0 + (2 + p) * ξ * A 2 = 0) ∧
      (p * ξ * A 0 + (4 - η) * A 2 + (p / 2 + 2) * ξ * A 4 = 0) ∧
      ∀ ℓ : ℕ, 2 ≤ ℓ → (p / 2 - ℓ + 1) * ξ * A (2 * ℓ - 2) + (4 * ℓ ^ 2 - η) * A (2 * ℓ) +
        (p / 2 + ℓ + 1) * ξ * A (2 * ℓ + 2) = 0 := by
  set a : ℕ → ℂ := fun ℓ => if ℓ = 0 then A 0 else 1 / 2 * A (2 * ℓ)
  set b : ℕ → ℂ := fun ℓ => 1 / 2 * A (2 * ℓ + 2)
  have ha : ∀ K : ℝ, Summable (fun ℓ : ℕ => ‖a ℓ‖ * Real.exp (K * ℓ)) := fun K =>
    .of_nonneg_of_le (fun _ => by positivity) (fun ℓ => by
      gcongr
      simp only [a]
      split_ifs with h
      · subst h; simp
      · rw [norm_mul]; simp only [add_zero]
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [this]; linarith [norm_nonneg (A (2 * ℓ))]) (p1b_summable_coeff hA 0 K)
  have hb := p1b_summable_coeff_mul hA 2 (1 / 2)
  have tw := p1b_twoSided ha hb 0
  set c := p1bTwoSided a b
  have hc0 : c ((0 : ℕ) : ℤ) = A 0 := rfl
  have hcp : ∀ j : ℕ, c ((j : ℤ) + 1) = 1 / 2 * A (2 * j + 2) := fun j => by
    rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring]
    show a (j + 1) = _
    simp only [a, Nat.add_one_ne_zero, ↓reduceIte]; ring_nf
  have hcn : ∀ ℓ : ℕ, c (-(ℓ : ℤ) - 1) = 1 / 2 * A (2 * ℓ + 2) := p1bTwoSided_neg a b
  have hfun : (fun z => ∑' ℓ : ℕ, A (2 * ℓ) * Complex.cos ((2 * ℓ : ℕ) * z)) =
      fun z => ∑' n : ℤ, c n * Complex.exp (I * ((0 : ℂ) + 2 * n) * z) := by
    funext z
    obtain ⟨sa, sb, H⟩ := tw.2 z
    rw [H.tsum_eq, sa.tsum_eq_zero_add]
    have sa' := (summable_nat_add_iff 1).mpr sa
    have hg : ∀ ℓ : ℕ, A (2 * (ℓ + 1)) * Complex.cos ((2 * (ℓ + 1) : ℕ) * z) =
        a (ℓ + 1) * Complex.exp (I * (0 + 2 * ((ℓ + 1 : ℕ) : ℂ)) * z) +
          b ℓ * Complex.exp (I * (0 + 2 * (-(ℓ : ℂ) - 1)) * z) := fun ℓ => by
      simp only [a, b, Nat.add_one_ne_zero, ↓reduceIte]
      rw [Complex.cos]; push_cast; ring_nf
    have sf : Summable (fun ℓ : ℕ => A (2 * ℓ) * Complex.cos ((2 * ℓ : ℕ) * z)) := by
      refine (summable_nat_add_iff 1).mp ?_
      simp only [hg]
      exact sa'.add sb
    rw [sf.tsum_eq_zero_add]
    simp only [hg]
    rw [sa'.tsum_add sb]
    simp [a]
    ring
  rw [hfun, p1b_isInceSolution_series_iff tw.1]
  have hcm1 : c (((0 : ℕ) : ℤ) - 1) = 1 / 2 * A 2 := by simpa using hcn 0
  have hcp0 : c (((0 : ℕ) : ℤ) + 1) = 1 / 2 * A 2 := by simpa using hcp 0
  constructor
  · intro h
    refine ⟨?_, ?_, fun ℓ hℓ => ?_⟩
    · have := h ((0 : ℕ) : ℤ)
      rw [hc0, hcm1, hcp0] at this
      push_cast at this
      linear_combination (-2) * this
    · have := h ((0 : ℕ) + 1 : ℤ)
      rw [hcp, show ((0 : ℕ) : ℤ) + 1 - 1 = ((0 : ℕ) : ℤ) by ring, hc0,
        show ((0 : ℕ) : ℤ) + 1 + 1 = ((1 : ℕ) : ℤ) + 1 by norm_num, hcp] at this
      push_cast at this
      linear_combination (-2) * this
    · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 2 := ⟨ℓ - 2, by omega⟩
      have := h ((j + 1 : ℕ) + 1 : ℤ)
      rw [hcp, show ((j + 1 : ℕ) : ℤ) + 1 - 1 = (j : ℤ) + 1 by push_cast; ring, hcp,
        show ((j + 1 : ℕ) : ℤ) + 1 + 1 = ((j + 2 : ℕ) : ℤ) + 1 by push_cast; ring, hcp] at this
      rw [show 2 * (j + 2) - 2 = 2 * j + 2 by omega, show 2 * (j + 2) = 2 * (j + 1) + 2 by ring]
      push_cast at this ⊢
      linear_combination (-2) * this
  · rintro ⟨h0, h1, h⟩ n
    rcases n with (_ | j) | ℓ
    · have e : (Int.ofNat 0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
      rw [e, hc0, hcm1, hcp0]
      push_cast
      linear_combination (-1 / 2) * h0
    · have e : (Int.ofNat (j + 1) : ℤ) = (j : ℤ) + 1 := rfl
      rw [e, hcp, show (j : ℤ) + 1 + 1 = ((j + 1 : ℕ) : ℤ) + 1 by push_cast; ring, hcp]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [show ((0 : ℕ) : ℤ) + 1 - 1 = ((0 : ℕ) : ℤ) by ring, hc0]
        push_cast
        linear_combination (-1 / 2) * h1
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [show ((i + 1 : ℕ) : ℤ) + 1 - 1 = (i : ℤ) + 1 by push_cast; ring, hcp]
        have hh := h (i + 2) (by omega)
        rw [show 2 * (i + 2) - 2 = 2 * i + 2 by omega,
          show 2 * (i + 2) = 2 * (i + 1) + 2 by ring] at hh
        push_cast at hh ⊢
        linear_combination (-1 / 2) * hh
    · rw [Int.negSucc_eq, show -((ℓ : ℤ) + 1) = -(ℓ : ℤ) - 1 by ring, hcn,
        show -(ℓ : ℤ) - 1 - 1 = -((ℓ + 1 : ℕ) : ℤ) - 1 by push_cast; ring, hcn]
      rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
      · rw [show -((0 : ℕ) : ℤ) - 1 + 1 = ((0 : ℕ) : ℤ) by ring, hc0]
        push_cast
        linear_combination (-1 / 2) * h1
      · obtain ⟨i, rfl⟩ : ∃ i, ℓ = i + 1 := ⟨ℓ - 1, by omega⟩
        rw [show -((i + 1 : ℕ) : ℤ) - 1 + 1 = -(i : ℤ) - 1 by push_cast; ring, hcn]
        have hh := h (i + 2) (by omega)
        rw [show 2 * (i + 2) - 2 = 2 * i + 2 by omega,
          show 2 * (i + 2) = 2 * (i + 1) + 2 by ring] at hh
        push_cast at hh ⊢
        linear_combination (-1 / 2) * hh

/-- **Even Fourier-series solutions, `s = 1`** (DLMF 28.31.4, 28.31.7):
`w(z) = ∑_ℓ A_{2ℓ+1} cos((2ℓ+1)z)` solves Ince's equation iff
`(1-η+(½p+½)ξ)A₁ + (½p+3/2)ξA₃ = 0` and, for `ℓ ≥ 1`,
`(½p-ℓ+½)ξA_{2ℓ-1} + ((2ℓ+1)²-η)A_{2ℓ+1} + (½p+ℓ+3/2)ξA_{2ℓ+3} = 0`. -/
@[dlmf 28.31.E4, dlmf 28.31.E7]
theorem isInceSolution_cos_odd_iff {ξ η p : ℂ} {A : ℕ → ℂ} (hA : IsEntireFourierCoeff A) :
    IsInceSolution ξ η p (fun z => ∑' ℓ : ℕ, A (2 * ℓ + 1) * Complex.cos ((2 * ℓ + 1 : ℕ) * z)) ↔
      ((1 - η + (p / 2 + 1 / 2) * ξ) * A 1 + (p / 2 + 3 / 2) * ξ * A 3 = 0) ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → (p / 2 - ℓ + 1 / 2) * ξ * A (2 * ℓ - 1) +
        ((2 * ℓ + 1) ^ 2 - η) * A (2 * ℓ + 1) + (p / 2 + ℓ + 3 / 2) * ξ * A (2 * ℓ + 3) = 0 := by
  set a : ℕ → ℂ := fun ℓ => 1 / 2 * A (2 * ℓ + 1)
  have ha := p1b_summable_coeff_mul hA 1 (1 / 2)
  have tw := p1b_twoSided ha ha 1
  set c := p1bTwoSided a a
  have hc1 : ∀ ℓ : ℕ, c ℓ = 1 / 2 * A (2 * ℓ + 1) := fun ℓ => rfl
  have hc2 : ∀ ℓ : ℕ, c (-(ℓ : ℤ) - 1) = 1 / 2 * A (2 * ℓ + 1) := p1bTwoSided_neg a a
  have hfun : (fun z => ∑' ℓ : ℕ, A (2 * ℓ + 1) * Complex.cos ((2 * ℓ + 1 : ℕ) * z)) =
      fun z => ∑' n : ℤ, c n * Complex.exp (I * ((1 : ℂ) + 2 * n) * z) := by
    funext z
    obtain ⟨sa, sb, H⟩ := tw.2 z
    rw [H.tsum_eq, ← sa.tsum_add sb]
    congr 1; funext ℓ
    rw [Complex.cos]; push_cast; ring_nf
  rw [hfun, p1b_isInceSolution_series_iff tw.1]
  have hcp : ∀ ℓ : ℕ, c ((ℓ : ℤ) + 1) = 1 / 2 * A (2 * ℓ + 3) := fun ℓ => by
    rw [show (ℓ : ℤ) + 1 = ((ℓ + 1 : ℕ) : ℤ) by push_cast; ring, hc1]; ring_nf
  have hcm : ∀ j : ℕ, c (((j + 1 : ℕ) : ℤ) - 1) = 1 / 2 * A (2 * j + 1) := fun j => by
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by push_cast; ring, hc1]
  have hcn : ∀ ℓ : ℕ, c (-(ℓ : ℤ) - 1 - 1) = 1 / 2 * A (2 * ℓ + 3) := fun ℓ => by
    rw [show -(ℓ : ℤ) - 1 - 1 = -((ℓ + 1 : ℕ) : ℤ) - 1 by push_cast; ring, hc2]; ring_nf
  have hcn' : ∀ j : ℕ, c (-((j + 1 : ℕ) : ℤ) - 1 + 1) = 1 / 2 * A (2 * j + 1) := fun j => by
    rw [show -((j + 1 : ℕ) : ℤ) - 1 + 1 = -(j : ℤ) - 1 by push_cast; ring, hc2]
  have hc0 : c ((0 : ℕ) : ℤ) = 1 / 2 * A 1 := by rw [hc1]
  have hcm1 : c ((0 : ℕ) - 1 : ℤ) = 1 / 2 * A 1 := by
    have := hc2 0; simpa using this
  have hcn0 : c (-((0 : ℕ) : ℤ) - 1 + 1) = 1 / 2 * A 1 := by simpa using hc0
  constructor
  · intro h
    refine ⟨?_, fun ℓ hℓ => ?_⟩
    · have := h ((0 : ℕ) : ℤ)
      rw [hc0, hcm1, hcp] at this
      push_cast at this
      linear_combination (-2) * this
    · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
      have := h ((j + 1 : ℕ) : ℤ)
      rw [hc1, hcm, hcp] at this
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
      push_cast at this ⊢
      linear_combination (-2) * this
  · rintro ⟨h0, h⟩ n
    rcases n with ℓ | ℓ
    · rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
      · have e : (Int.ofNat 0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
        rw [e, hc0, hcm1, hcp]
        push_cast
        linear_combination (-1 / 2) * h0
      · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
        have hh := h (j + 1) (by omega)
        have e : (Int.ofNat (j + 1) : ℤ) = ((j + 1 : ℕ) : ℤ) := rfl
        rw [e, hc1, hcm, hcp]
        rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hh
        push_cast at hh ⊢
        linear_combination (-1 / 2) * hh
    · rw [Int.negSucc_eq, show -((ℓ : ℤ) + 1) = -(ℓ : ℤ) - 1 by ring, hc2, hcn]
      rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
      · rw [hcn0]
        push_cast
        linear_combination (-1 / 2) * h0
      · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
        have hh := h (j + 1) (by omega)
        rw [hcn']
        rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hh
        push_cast at hh ⊢
        linear_combination (-1 / 2) * hh

/-- **Odd Fourier-series solutions, `s = 1`** (DLMF 28.31.5, 28.31.8):
`w(z) = ∑_ℓ B_{2ℓ+1} sin((2ℓ+1)z)` solves Ince's equation iff
`(1-η-(½p+½)ξ)B₁ + (½p+3/2)ξB₃ = 0` and, for `ℓ ≥ 1`,
`(½p-ℓ+½)ξB_{2ℓ-1} + ((2ℓ+1)²-η)B_{2ℓ+1} + (½p+ℓ+3/2)ξB_{2ℓ+3} = 0`. -/
@[dlmf 28.31.E5, dlmf 28.31.E8]
theorem isInceSolution_sin_odd_iff {ξ η p : ℂ} {B : ℕ → ℂ} (hB : IsEntireFourierCoeff B) :
    IsInceSolution ξ η p (fun z => ∑' ℓ : ℕ, B (2 * ℓ + 1) * Complex.sin ((2 * ℓ + 1 : ℕ) * z)) ↔
      ((1 - η - (p / 2 + 1 / 2) * ξ) * B 1 + (p / 2 + 3 / 2) * ξ * B 3 = 0) ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → (p / 2 - ℓ + 1 / 2) * ξ * B (2 * ℓ - 1) +
        ((2 * ℓ + 1) ^ 2 - η) * B (2 * ℓ + 1) + (p / 2 + ℓ + 3 / 2) * ξ * B (2 * ℓ + 3) = 0 := by
  set a : ℕ → ℂ := fun ℓ => -(I / 2) * B (2 * ℓ + 1)
  set b : ℕ → ℂ := fun ℓ => I / 2 * B (2 * ℓ + 1)
  have ha := p1b_summable_coeff_mul hB 1 (-(I / 2))
  have hb := p1b_summable_coeff_mul hB 1 (I / 2)
  have tw := p1b_twoSided ha hb 1
  set c := p1bTwoSided a b
  have hc1 : ∀ ℓ : ℕ, c ℓ = -(I / 2) * B (2 * ℓ + 1) := fun ℓ => rfl
  have hc2 : ∀ ℓ : ℕ, c (-(ℓ : ℤ) - 1) = I / 2 * B (2 * ℓ + 1) := p1bTwoSided_neg a b
  have hfun : (fun z => ∑' ℓ : ℕ, B (2 * ℓ + 1) * Complex.sin ((2 * ℓ + 1 : ℕ) * z)) =
      fun z => ∑' n : ℤ, c n * Complex.exp (I * ((1 : ℂ) + 2 * n) * z) := by
    funext z
    obtain ⟨sa, sb, H⟩ := tw.2 z
    rw [H.tsum_eq, ← sa.tsum_add sb]
    congr 1; funext ℓ
    rw [Complex.sin]; push_cast; ring_nf
  rw [hfun, p1b_isInceSolution_series_iff tw.1]
  have hcp : ∀ ℓ : ℕ, c ((ℓ : ℤ) + 1) = -(I / 2) * B (2 * ℓ + 3) := fun ℓ => by
    rw [show (ℓ : ℤ) + 1 = ((ℓ + 1 : ℕ) : ℤ) by push_cast; ring, hc1]; ring_nf
  have hcm : ∀ j : ℕ, c (((j + 1 : ℕ) : ℤ) - 1) = -(I / 2) * B (2 * j + 1) := fun j => by
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by push_cast; ring, hc1]
  have hcn : ∀ ℓ : ℕ, c (-(ℓ : ℤ) - 1 - 1) = I / 2 * B (2 * ℓ + 3) := fun ℓ => by
    rw [show -(ℓ : ℤ) - 1 - 1 = -((ℓ + 1 : ℕ) : ℤ) - 1 by push_cast; ring, hc2]; ring_nf
  have hcn' : ∀ j : ℕ, c (-((j + 1 : ℕ) : ℤ) - 1 + 1) = I / 2 * B (2 * j + 1) := fun j => by
    rw [show -((j + 1 : ℕ) : ℤ) - 1 + 1 = -(j : ℤ) - 1 by push_cast; ring, hc2]
  have hc0 : c ((0 : ℕ) : ℤ) = -(I / 2) * B 1 := by rw [hc1]
  have hcm1 : c ((0 : ℕ) - 1 : ℤ) = I / 2 * B 1 := by
    have := hc2 0; simpa using this
  have hcn0 : c (-((0 : ℕ) : ℤ) - 1 + 1) = -(I / 2) * B 1 := by simpa using hc0
  have hI : (I / 2 : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  constructor
  · intro h
    refine ⟨?_, fun ℓ hℓ => ?_⟩
    · have := h ((0 : ℕ) : ℤ)
      rw [hc0, hcm1, hcp] at this
      push_cast at this
      refine mul_left_cancel₀ hI ?_
      linear_combination this
    · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
      have := h ((j + 1 : ℕ) : ℤ)
      rw [hc1, hcm, hcp] at this
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
      push_cast at this ⊢
      refine mul_left_cancel₀ hI ?_
      linear_combination this
  · rintro ⟨h0, h⟩ n
    rcases n with ℓ | ℓ
    · rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
      · have e : (Int.ofNat 0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
        rw [e, hc0, hcm1, hcp]
        push_cast
        linear_combination (I / 2) * h0
      · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
        have hh := h (j + 1) (by omega)
        have e : (Int.ofNat (j + 1) : ℤ) = ((j + 1 : ℕ) : ℤ) := rfl
        rw [e, hc1, hcm, hcp]
        rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hh
        push_cast at hh ⊢
        linear_combination (I / 2) * hh
    · rw [Int.negSucc_eq, show -((ℓ : ℤ) + 1) = -(ℓ : ℤ) - 1 by ring, hc2, hcn]
      rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
      · rw [hcn0]
        push_cast
        linear_combination (-(I / 2)) * h0
      · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
        have hh := h (j + 1) (by omega)
        rw [hcn']
        rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hh
        push_cast at hh ⊢
        linear_combination (-(I / 2)) * hh

/-- **Odd Fourier-series solutions, `s = 2`** (DLMF 28.31.5, 28.31.9):
`w(z) = ∑_ℓ B_{2ℓ+2} sin((2ℓ+2)z)` solves Ince's equation iff
`(4-η)B₂ + (½p+2)ξB₄ = 0` and, for `ℓ ≥ 2`,
`(½p-ℓ+1)ξB_{2ℓ-2} + (4ℓ²-η)B_{2ℓ} + (½p+ℓ+1)ξB_{2ℓ+2} = 0`. -/
@[dlmf 28.31.E5, dlmf 28.31.E9]
theorem isInceSolution_sin_even_iff {ξ η p : ℂ} {B : ℕ → ℂ} (hB : IsEntireFourierCoeff B) :
    IsInceSolution ξ η p (fun z => ∑' ℓ : ℕ, B (2 * ℓ + 2) * Complex.sin ((2 * ℓ + 2 : ℕ) * z)) ↔
      ((4 - η) * B 2 + (p / 2 + 2) * ξ * B 4 = 0) ∧
      ∀ ℓ : ℕ, 2 ≤ ℓ → (p / 2 - ℓ + 1) * ξ * B (2 * ℓ - 2) + (4 * ℓ ^ 2 - η) * B (2 * ℓ) +
        (p / 2 + ℓ + 1) * ξ * B (2 * ℓ + 2) = 0 := by
  set a : ℕ → ℂ := fun ℓ => if ℓ = 0 then 0 else -(I / 2) * B (2 * ℓ)
  set b : ℕ → ℂ := fun ℓ => I / 2 * B (2 * ℓ + 2)
  have hI2 : ‖(I / 2 : ℂ)‖ = 1 / 2 := by simp
  have ha : ∀ K : ℝ, Summable (fun ℓ : ℕ => ‖a ℓ‖ * Real.exp (K * ℓ)) := fun K =>
    .of_nonneg_of_le (fun _ => by positivity) (fun ℓ => by
      gcongr
      simp only [a]
      split_ifs with h
      · simp
      · rw [norm_mul, norm_neg, hI2]; simp only [add_zero]
        linarith [norm_nonneg (B (2 * ℓ))]) (p1b_summable_coeff hB 0 K)
  have hb := p1b_summable_coeff_mul hB 2 (I / 2)
  have tw := p1b_twoSided ha hb 0
  set c := p1bTwoSided a b
  have hc0 : c ((0 : ℕ) : ℤ) = 0 := rfl
  have hcp : ∀ j : ℕ, c ((j : ℤ) + 1) = -(I / 2) * B (2 * j + 2) := fun j => by
    rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring]
    show a (j + 1) = _
    simp only [a, Nat.add_one_ne_zero, ↓reduceIte]; ring_nf
  have hcn : ∀ ℓ : ℕ, c (-(ℓ : ℤ) - 1) = I / 2 * B (2 * ℓ + 2) := p1bTwoSided_neg a b
  have hfun : (fun z => ∑' ℓ : ℕ, B (2 * ℓ + 2) * Complex.sin ((2 * ℓ + 2 : ℕ) * z)) =
      fun z => ∑' n : ℤ, c n * Complex.exp (I * ((0 : ℂ) + 2 * n) * z) := by
    funext z
    obtain ⟨sa, sb, H⟩ := tw.2 z
    rw [H.tsum_eq, sa.tsum_eq_zero_add]
    have sa' := (summable_nat_add_iff 1).mpr sa
    have hg : ∀ ℓ : ℕ, B (2 * ℓ + 2) * Complex.sin ((2 * ℓ + 2 : ℕ) * z) =
        a (ℓ + 1) * Complex.exp (I * (0 + 2 * ((ℓ + 1 : ℕ) : ℂ)) * z) +
          b ℓ * Complex.exp (I * (0 + 2 * (-(ℓ : ℂ) - 1)) * z) := fun ℓ => by
      simp only [a, b, Nat.add_one_ne_zero, ↓reduceIte]
      rw [Complex.sin]; push_cast; ring_nf
    simp only [hg]
    rw [sa'.tsum_add sb]
    simp [a]
  rw [hfun, p1b_isInceSolution_series_iff tw.1]
  have hcm1 : c (((0 : ℕ) : ℤ) - 1) = I / 2 * B 2 := by simpa using hcn 0
  have hcp0 : c (((0 : ℕ) : ℤ) + 1) = -(I / 2) * B 2 := by simpa using hcp 0
  have hI : (I / 2 : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  constructor
  · intro h
    refine ⟨?_, fun ℓ hℓ => ?_⟩
    · have := h ((0 : ℕ) + 1 : ℤ)
      rw [hcp, show ((0 : ℕ) : ℤ) + 1 - 1 = ((0 : ℕ) : ℤ) by ring, hc0,
        show ((0 : ℕ) : ℤ) + 1 + 1 = ((1 : ℕ) : ℤ) + 1 by norm_num, hcp] at this
      push_cast at this
      refine mul_left_cancel₀ hI ?_
      linear_combination this
    · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 2 := ⟨ℓ - 2, by omega⟩
      have := h ((j + 1 : ℕ) + 1 : ℤ)
      rw [hcp, show ((j + 1 : ℕ) : ℤ) + 1 - 1 = (j : ℤ) + 1 by push_cast; ring, hcp,
        show ((j + 1 : ℕ) : ℤ) + 1 + 1 = ((j + 2 : ℕ) : ℤ) + 1 by push_cast; ring, hcp] at this
      rw [show 2 * (j + 2) - 2 = 2 * j + 2 by omega, show 2 * (j + 2) = 2 * (j + 1) + 2 by ring]
      push_cast at this ⊢
      refine mul_left_cancel₀ hI ?_
      linear_combination this
  · rintro ⟨h1, h⟩ n
    rcases n with (_ | j) | ℓ
    · have e : (Int.ofNat 0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
      rw [e, hc0, hcm1, hcp0]
      ring
    · have e : (Int.ofNat (j + 1) : ℤ) = (j : ℤ) + 1 := rfl
      rw [e, hcp, show (j : ℤ) + 1 + 1 = ((j + 1 : ℕ) : ℤ) + 1 by push_cast; ring, hcp]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [show ((0 : ℕ) : ℤ) + 1 - 1 = ((0 : ℕ) : ℤ) by ring, hc0]
        push_cast
        linear_combination (I / 2) * h1
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [show ((i + 1 : ℕ) : ℤ) + 1 - 1 = (i : ℤ) + 1 by push_cast; ring, hcp]
        have hh := h (i + 2) (by omega)
        rw [show 2 * (i + 2) - 2 = 2 * i + 2 by omega,
          show 2 * (i + 2) = 2 * (i + 1) + 2 by ring] at hh
        push_cast at hh ⊢
        linear_combination (I / 2) * hh
    · rw [Int.negSucc_eq, show -((ℓ : ℤ) + 1) = -(ℓ : ℤ) - 1 by ring, hcn,
        show -(ℓ : ℤ) - 1 - 1 = -((ℓ + 1 : ℕ) : ℤ) - 1 by push_cast; ring, hcn]
      rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
      · rw [show -((0 : ℕ) : ℤ) - 1 + 1 = ((0 : ℕ) : ℤ) by ring, hc0]
        push_cast
        linear_combination (-(I / 2)) * h1
      · obtain ⟨i, rfl⟩ : ∃ i, ℓ = i + 1 := ⟨ℓ - 1, by omega⟩
        rw [show -((i + 1 : ℕ) : ℤ) - 1 + 1 = -(i : ℤ) - 1 by push_cast; ring, hcn]
        have hh := h (i + 2) (by omega)
        rw [show 2 * (i + 2) - 2 = 2 * i + 2 by omega,
          show 2 * (i + 2) = 2 * (i + 1) + 2 by ring] at hh
        push_cast at hh ⊢
        linear_combination (-(I / 2)) * hh

/-! ### Ince polynomials (§28.31(ii)) -/

/-- **Ince polynomials `C_p^m` and eigenvalues `a_p^m`** (DLMF §28.31(ii), 28.31.10, 28.31.12):
for a nonnegative integer `p`, real `ξ` and `m ≤ p`, `m ≡ p (mod 2)`, `C_p^m(·, ξ)` is a cosine
Ince polynomial solving 28.31.3 with `η = a_p^m(ξ)`, with exactly `m` zeros in `[0, π)`, all
simple, normalized by 28.31.12 and positive at `0`; the `a_p^m(ξ)` are real and distinct; and
every (complex) `η` admitting a nontrivial cosine Ince polynomial solution is one of them. -/
@[dlmf 28.31.ii, dlmf 28.31.E10, dlmf 28.31.E12]
theorem inceC_spec {p m : ℕ} (hm : m ≤ p) (hpm : m % 2 = p % 2) (ξ : ℝ) :
    IsInceCosPoly p (fun z => inceC p m z ξ) ∧
      IsInceSolution ξ (inceA p m ξ) p (fun z => inceC p m z ξ) ∧
      zerosIco (fun z => inceC p m z ξ) = m ∧
      (∀ x : ℝ, x ∈ Ico 0 Real.pi → inceC p m x ξ = 0 → deriv (fun z => inceC p m z ξ) x ≠ 0) ∧
      (1 / Real.pi : ℂ) * ∫ x in (0 : ℝ)..2 * Real.pi, inceC p m x ξ ^ 2 = 1 ∧
      0 < (inceC p m 0 ξ).re ∧
      (∀ m' : ℕ, m' ≤ p → m' % 2 = p % 2 → m' ≠ m → inceA p m' ξ ≠ inceA p m ξ) ∧
      (∀ η : ℂ, (∃ f, IsInceCosPoly p f ∧ (∃ z, f z ≠ 0) ∧ IsInceSolution ξ η p f) →
        ∃ m' : ℕ, m' ≤ p ∧ m' % 2 = p % 2 ∧ η = inceA p m' ξ) := by
  sorry

/-- **Ince polynomials `S_p^m` and eigenvalues `b_p^m`** (DLMF §28.31(ii), 28.31.11,
28.31.12): for `1 ≤ m ≤ p`, `m ≡ p (mod 2)` and real `ξ`, `S_p^m(·, ξ)` is a sine Ince
polynomial solving 28.31.3 with `η = b_p^m(ξ)`, with exactly `m` zeros in `[0, π)` (including
`z = 0`), all simple, normalized by 28.31.12 with `S_p^m'(0, ξ) > 0`; the `b_p^m(ξ)` are real
and distinct; and every `η` admitting a nontrivial sine Ince polynomial solution is one of
them. -/
@[dlmf 28.31.ii, dlmf 28.31.E11, dlmf 28.31.E12]
theorem inceS_spec {p m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ p) (hpm : m % 2 = p % 2) (ξ : ℝ) :
    IsInceSinPoly p (fun z => inceS p m z ξ) ∧
      IsInceSolution ξ (inceB p m ξ) p (fun z => inceS p m z ξ) ∧
      zerosIco (fun z => inceS p m z ξ) = m ∧
      (∀ x : ℝ, x ∈ Ico 0 Real.pi → inceS p m x ξ = 0 → deriv (fun z => inceS p m z ξ) x ≠ 0) ∧
      (1 / Real.pi : ℂ) * ∫ x in (0 : ℝ)..2 * Real.pi, inceS p m x ξ ^ 2 = 1 ∧
      0 < (deriv (fun z => inceS p m z ξ) 0).re ∧
      (∀ m' : ℕ, 1 ≤ m' → m' ≤ p → m' % 2 = p % 2 → m' ≠ m → inceB p m' ξ ≠ inceB p m ξ) ∧
      (∀ η : ℂ, (∃ f, IsInceSinPoly p f ∧ (∃ z, f z ≠ 0) ∧ IsInceSolution ξ η p f) →
        ∃ m' : ℕ, 1 ≤ m' ∧ m' ≤ p ∧ m' % 2 = p % 2 ∧ η = inceB p m' ξ) := by
  sorry

/-- **Limits as `ξ → 0`** (DLMF 28.31.13): `C_p^0(x, ξ) → 1/√2`, `C_p^m(x, ξ) → cos(mx)`,
`S_p^m(x, ξ) → sin(mx)` (`m ≠ 0`), and `a_p^m(ξ), b_p^m(ξ) → m²`, for fixed real `x` and
admissible `p, m`. -/
@[dlmf 28.31.E13]
theorem ince_tendsto_xi_zero {p m : ℕ} (hm : m ≤ p) (hpm : m % 2 = p % 2) (x : ℝ) :
    (m = 0 → Tendsto (fun ξ : ℝ => inceC p 0 x ξ) (𝓝 0) (𝓝 (1 / Real.sqrt 2 : ℝ))) ∧
      (m ≠ 0 → Tendsto (fun ξ : ℝ => inceC p m x ξ) (𝓝 0) (𝓝 (Complex.cos (m * x)))) ∧
      (m ≠ 0 → Tendsto (fun ξ : ℝ => inceS p m x ξ) (𝓝 0) (𝓝 (Complex.sin (m * x)))) ∧
      Tendsto (fun ξ : ℝ => inceA p m ξ) (𝓝 0) (𝓝 ((m : ℝ) ^ 2)) ∧
      (m ≠ 0 → Tendsto (fun ξ : ℝ => inceB p m ξ) (𝓝 0) (𝓝 ((m : ℝ) ^ 2))) := by
  sorry

/-- **Limit to Mathieu functions** (DLMF 28.31.14–28.31.15): if `p → ∞` (through integers
`≡ m mod 2`) and `ξ → 0` with `pξ → 2q` (real `q`), then `C_p^m(x, ξ) → ce_m(x, q)`,
`S_p^m(x, ξ) → se_m(x, q)` (`m ≥ 1`), `a_p^m(ξ) → a_m(q)` and `b_p^m(ξ) → b_m(q)` (`m ≥ 1`). -/
@[dlmf 28.31.E14, dlmf 28.31.E15]
theorem ince_tendsto_mathieu {m : ℕ} {q : ℝ} {P : ℕ → ℕ} {Ξ : ℕ → ℝ}
    (hP : Tendsto P atTop atTop) (hPm : ∀ j, P j % 2 = m % 2) (hΞ : Tendsto Ξ atTop (𝓝 0))
    (hPΞ : Tendsto (fun j => (P j : ℝ) * Ξ j) atTop (𝓝 (2 * q))) (x : ℝ) :
    Tendsto (fun j => inceC (P j) m x (Ξ j)) atTop (𝓝 (mathieuCe m x q)) ∧
      Tendsto (fun j => inceA (P j) m (Ξ j)) atTop (𝓝 (mathieuA m q)) ∧
      (1 ≤ m → Tendsto (fun j => inceS (P j) m x (Ξ j)) atTop (𝓝 (mathieuSe m x q))) ∧
      (1 ≤ m → Tendsto (fun j => inceB (P j) m (Ξ j)) atTop (𝓝 (mathieuB m q))) := by
  sorry

/-! ### §28.31(iii) Paraboloidal wave functions -/

/-- **Differential equation of the paraboloidal wave functions** (DLMF 28.31.18):
`w'' + (η - ⅛ξ² - (p+1)ξ cos 2z + ⅛ξ² cos 4z) w = 0` with `η = a_p^m(ξ)` for `hc_p^m` and
`η = b_p^m(ξ)` for `hs_p^m`; this is the Whittaker–Hill equation 28.31.1 with
`A = η - ξ²/8`, `B = -(p+1)ξ`, `k = iξ/2`, `c = 1`. Proved from 28.31.2 and the admitted
`inceC_spec`, `inceS_spec`. -/
@[dlmf 28.31.E18]
theorem paraboloidal_isWhittakerHillSolution {p m : ℕ} (hm : m ≤ p) (hpm : m % 2 = p % 2)
    (ξ : ℝ) :
    IsWhittakerHillSolution (inceA p m ξ - (ξ : ℂ) ^ 2 / 8) (-((p : ℂ) + 1) * ξ) (I * ξ / 2) 1
        (fun z => paraboloidalHc p m z ξ) ∧
      (1 ≤ m → IsWhittakerHillSolution (inceB p m ξ - (ξ : ℂ) ^ 2 / 8) (-((p : ℂ) + 1) * ξ)
        (I * ξ / 2) 1 (fun z => paraboloidalHs p m z ξ)) := by
  have hk : ((ξ : ℂ)) ^ 2 = -4 * (I * ξ / 2) ^ 2 * 1 ^ 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  have hfun : ∀ (F : ℂ → ℂ), (fun z => F z * Complex.exp (-((ξ : ℂ) * Complex.cos (2 * z)) / 4)) =
      fun z => Complex.exp (-((ξ : ℂ) * Complex.cos (2 * z)) / 4) * F z :=
    fun F => funext fun z => mul_comm _ _
  refine ⟨?_, fun hm1 => ?_⟩
  · have := (isWhittakerHillSolution_iff_isInceSolution (η := (inceA p m ξ : ℂ)) (p := (p : ℂ))
      hk).mpr (inceC_spec hm hpm ξ).2.1
    rw [hfun] at this
    exact this
  · have := (isWhittakerHillSolution_iff_isInceSolution (η := (inceB p m ξ : ℂ)) (p := (p : ℂ))
      hk).mpr (inceS_spec hm1 hm hpm ξ).2.1
    rw [hfun] at this
    exact this

/-- **Change of sign of `ξ`** (DLMF 28.31.19):
`hc_{2n}^{2m}(z, -ξ) = (-1)^m hc_{2n}^{2m}(½π - z, ξ)` and
`hc_{2n+1}^{2m+1}(z, -ξ) = (-1)^m hs_{2n+1}^{2m+1}(½π - z, ξ)`, `m ≤ n`. -/
@[dlmf 28.31.E19]
theorem paraboloidalHc_neg_xi {n m : ℕ} (hm : m ≤ n) (z : ℂ) (ξ : ℝ) :
    paraboloidalHc (2 * n) (2 * m) z (-ξ) =
        (-1) ^ m * paraboloidalHc (2 * n) (2 * m) (Real.pi / 2 - z) ξ ∧
      paraboloidalHc (2 * n + 1) (2 * m + 1) z (-ξ) =
        (-1) ^ m * paraboloidalHs (2 * n + 1) (2 * m + 1) (Real.pi / 2 - z) ξ := by
  sorry

/-- **Change of sign of `ξ`** (DLMF 28.31.20):
`hs_{2n+1}^{2m+1}(z, -ξ) = (-1)^m hc_{2n+1}^{2m+1}(½π - z, ξ)` and
`hs_{2n+2}^{2m+2}(z, -ξ) = (-1)^m hs_{2n+2}^{2m+2}(½π - z, ξ)`, `m ≤ n`. -/
@[dlmf 28.31.E20]
theorem paraboloidalHs_neg_xi {n m : ℕ} (hm : m ≤ n) (z : ℂ) (ξ : ℝ) :
    paraboloidalHs (2 * n + 1) (2 * m + 1) z (-ξ) =
        (-1) ^ m * paraboloidalHc (2 * n + 1) (2 * m + 1) (Real.pi / 2 - z) ξ ∧
      paraboloidalHs (2 * n + 2) (2 * m + 2) z (-ξ) =
        (-1) ^ m * paraboloidalHs (2 * n + 2) (2 * m + 2) (Real.pi / 2 - z) ξ := by
  sorry

/-- Orthogonality of `2π`-periodic solutions of the Whittaker–Hill equation 28.31.1 with
different `A` (the Wronskian identity `(W₁W₂' - W₂W₁')' = (A₁ - A₂) W₁W₂`). -/
lemma p1b_whittakerHill_orthogonal {A₁ A₂ B k c : ℂ} {W₁ W₂ : ℂ → ℂ}
    (h₁ : IsWhittakerHillSolution A₁ B k c W₁) (h₂ : IsWhittakerHillSolution A₂ B k c W₂)
    (hA : A₁ ≠ A₂) (hp₁ : Function.Periodic W₁ (2 * Real.pi))
    (hp₂ : Function.Periodic W₂ (2 * Real.pi)) :
    ∫ x in (0 : ℝ)..2 * Real.pi, W₁ x * W₂ x = 0 := by
  set V : ℂ → ℂ := fun z => B * Complex.cos (2 * z) - (k * c) ^ 2 / 2 * Complex.cos (4 * z)
  have hd₁ : ∀ z, HasDerivAt W₁ (deriv W₁ z) z := fun z => (h₁.1 z).hasDerivAt
  have hd₂ : ∀ z, HasDerivAt W₂ (deriv W₂ z) z := fun z => (h₂.1 z).hasDerivAt
  have hdd₁ : ∀ z, HasDerivAt (deriv W₁) (-(A₁ + V z) * W₁ z) z := fun z => by
    have := h₁.2 z; convert this using 2; simp only [V]; ring
  have hdd₂ : ∀ z, HasDerivAt (deriv W₂) (-(A₂ + V z) * W₂ z) z := fun z => by
    have := h₂.2 z; convert this using 2; simp only [V]; ring
  set G : ℝ → ℂ := fun x => W₁ x * deriv W₂ x - W₂ x * deriv W₁ x
  have hG : ∀ x : ℝ, HasDerivAt G ((A₁ - A₂) * (W₁ x * W₂ x)) x := by
    intro x
    have := (((hd₁ x).mul (hdd₂ x)).sub ((hd₂ x).mul (hdd₁ x))).comp_ofReal
    convert this using 1; ring
  have hcont : Continuous (fun x : ℝ => (A₁ - A₂) * (W₁ x * W₂ x)) :=
    continuous_const.mul ((h₁.1.continuous.comp continuous_ofReal).mul
      (h₂.1.continuous.comp continuous_ofReal))
  have hftc := integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * Real.pi) (fun x _ => hG x)
    (hcont.intervalIntegrable _ _)
  have hdp : ∀ {W : ℂ → ℂ}, Function.Periodic W (2 * Real.pi) →
      Function.Periodic (deriv W) (2 * Real.pi) := fun {W} hp z => by
    have : deriv (fun z => W (z + 2 * (Real.pi : ℂ))) z = deriv W (z + 2 * (Real.pi : ℂ)) :=
      deriv_comp_add_const _ _ _
    rw [← this]; congr 1; funext z; exact hp z
  have hG0 : G (2 * Real.pi) = G 0 := by
    simp only [G]
    have e : ((2 * Real.pi : ℝ) : ℂ) = (0 : ℂ) + 2 * (Real.pi : ℂ) := by push_cast; ring
    rw [e, hp₁ 0, hp₂ 0, hdp hp₁ 0, hdp hp₂ 0]
    simp
  rw [hG0, sub_self, intervalIntegral.integral_const_mul] at hftc
  exact (mul_eq_zero.mp hftc).resolve_left (sub_ne_zero.mpr hA)

/-- Cosine Ince polynomials are `2π`-periodic. -/
lemma p1b_periodic_cosPoly {p : ℕ} {f : ℂ → ℂ} (hf : IsInceCosPoly p f) :
    Function.Periodic f (2 * Real.pi) := by
  obtain ⟨A, hA⟩ := hf
  intro z
  rw [hA, hA]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (k : ℂ) * (z + 2 * Real.pi) = k * z + k * (2 * Real.pi) by ring,
    Complex.cos_add_nat_mul_two_pi]

/-- Sine Ince polynomials are `2π`-periodic. -/
lemma p1b_periodic_sinPoly {p : ℕ} {f : ℂ → ℂ} (hf : IsInceSinPoly p f) :
    Function.Periodic f (2 * Real.pi) := by
  obtain ⟨B, hB⟩ := hf
  intro z
  rw [hB, hB]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (k : ℂ) * (z + 2 * Real.pi) = k * z + k * (2 * Real.pi) by ring,
    Complex.sin_add_nat_mul_two_pi]

/-- `e^{-ξ cos 2z / 4}` is `2π`-periodic. -/
lemma p1b_periodic_expCos (ξ : ℂ) :
    Function.Periodic (fun z : ℂ => Complex.exp (-(ξ * Complex.cos (2 * z)) / 4))
      (2 * Real.pi) := by
  intro z
  simp only
  rw [show (2 : ℂ) * (z + 2 * Real.pi) = 2 * z + (2 : ℕ) * (2 * Real.pi) by push_cast; ring,
    Complex.cos_add_nat_mul_two_pi]

/-- **Orthogonality** (DLMF 28.31.21): for `m₁ ≠ m₂` (admissible for `p`),
`∫₀^{2π} hc_p^{m₁} hc_p^{m₂} dx = ∫₀^{2π} hs_p^{m₁} hs_p^{m₂} dx = 0`. Proved from the
Wronskian identity for 28.31.18 and the admitted `inceC_spec`, `inceS_spec` (distinct
eigenvalues). -/
@[dlmf 28.31.E21]
theorem integral_paraboloidal_orthogonal {p m₁ m₂ : ℕ} (h₁ : m₁ ≤ p) (h₁' : m₁ % 2 = p % 2)
    (h₂ : m₂ ≤ p) (h₂' : m₂ % 2 = p % 2) (hne : m₁ ≠ m₂) (ξ : ℝ) :
    ∫ x in (0 : ℝ)..2 * Real.pi, paraboloidalHc p m₁ x ξ * paraboloidalHc p m₂ x ξ = 0 ∧
      (1 ≤ m₁ → 1 ≤ m₂ →
        ∫ x in (0 : ℝ)..2 * Real.pi, paraboloidalHs p m₁ x ξ * paraboloidalHs p m₂ x ξ = 0) := by
  refine ⟨?_, fun k₁ k₂ => ?_⟩
  · have s1 := inceC_spec h₁ h₁' ξ
    have s2 := inceC_spec h₂ h₂' ξ
    have hA : (inceA p m₁ ξ : ℂ) - (ξ : ℂ) ^ 2 / 8 ≠ (inceA p m₂ ξ : ℂ) - (ξ : ℂ) ^ 2 / 8 := by
      rw [ne_eq, sub_left_inj, Complex.ofReal_inj]
      exact s2.2.2.2.2.2.2.1 m₁ h₁ h₁' hne
    have hper : ∀ {m : ℕ}, IsInceCosPoly p (fun z => inceC p m z ξ) →
        Function.Periodic (fun z => paraboloidalHc p m z ξ) (2 * Real.pi) :=
      fun {m} hc z => by
        simp only [paraboloidalHc]
        have e1 := p1b_periodic_expCos ξ z
        have e2 := p1b_periodic_cosPoly hc z
        simp only at e1 e2
        rw [e1, e2]
    exact p1b_whittakerHill_orthogonal (paraboloidal_isWhittakerHillSolution h₁ h₁' ξ).1
      (paraboloidal_isWhittakerHillSolution h₂ h₂' ξ).1 hA (hper s1.1) (hper s2.1)
  · have s1 := inceS_spec k₁ h₁ h₁' ξ
    have s2 := inceS_spec k₂ h₂ h₂' ξ
    have hA : (inceB p m₁ ξ : ℂ) - (ξ : ℂ) ^ 2 / 8 ≠ (inceB p m₂ ξ : ℂ) - (ξ : ℂ) ^ 2 / 8 := by
      rw [ne_eq, sub_left_inj, Complex.ofReal_inj]
      exact s2.2.2.2.2.2.2.1 m₁ k₁ h₁ h₁' hne
    have hper : ∀ {m : ℕ}, IsInceSinPoly p (fun z => inceS p m z ξ) →
        Function.Periodic (fun z => paraboloidalHs p m z ξ) (2 * Real.pi) :=
      fun {m} hc z => by
        simp only [paraboloidalHs]
        have e1 := p1b_periodic_expCos ξ z
        have e2 := p1b_periodic_sinPoly hc z
        simp only at e1 e2
        rw [e1, e2]
    exact p1b_whittakerHill_orthogonal ((paraboloidal_isWhittakerHillSolution h₁ h₁' ξ).2 k₁)
      ((paraboloidal_isWhittakerHillSolution h₂ h₂' ξ).2 k₂) hA (hper s1.1) (hper s2.1)

/-- **Double orthogonality of `hc`** (DLMF 28.31.22): for real `ξ ≠ 0` and admissible
`(p₁, m₁) ≠ (p₂, m₂)`, with `u₀ = 0` (`ξ > 0`) or `u₀ = ½π` (`ξ < 0`),
`∫_{u₀}^{u₀+i∞} ∫₀^{2π} hc_{p₁}^{m₁}(u) hc_{p₁}^{m₁}(v) hc_{p₂}^{m₂}(u) hc_{p₂}^{m₂}(v)
(cos 2u - cos 2v) dv du = 0`; the `u`-integral is written as `∫₀^∞ ⋯ dt` with `u = u₀ + it`
(the factor `du = i dt` is dropped). -/
@[dlmf 28.31.E22]
theorem paraboloidalHc_double_orthogonal {ξ : ℝ} (hξ : ξ ≠ 0) {p₁ m₁ p₂ m₂ : ℕ}
    (h₁ : m₁ ≤ p₁ ∧ m₁ % 2 = p₁ % 2) (h₂ : m₂ ≤ p₂ ∧ m₂ % 2 = p₂ % 2)
    (hne : p₁ ≠ p₂ ∨ m₁ ≠ m₂) :
    let u₀ : ℂ := if 0 < ξ then 0 else (Real.pi / 2 : ℝ)
    ∫ t in Ioi (0 : ℝ), ∫ v in (0 : ℝ)..2 * Real.pi,
      paraboloidalHc p₁ m₁ (u₀ + I * t) ξ * paraboloidalHc p₁ m₁ v ξ *
        paraboloidalHc p₂ m₂ (u₀ + I * t) ξ * paraboloidalHc p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v)) = 0 := by
  sorry

/-- **Double orthogonality of `hs`** (DLMF 28.31.23), as 28.31.22 for `hs`
(`m₁, m₂ ≥ 1`). -/
@[dlmf 28.31.E23]
theorem paraboloidalHs_double_orthogonal {ξ : ℝ} (hξ : ξ ≠ 0) {p₁ m₁ p₂ m₂ : ℕ}
    (h₁ : 1 ≤ m₁ ∧ m₁ ≤ p₁ ∧ m₁ % 2 = p₁ % 2) (h₂ : 1 ≤ m₂ ∧ m₂ ≤ p₂ ∧ m₂ % 2 = p₂ % 2)
    (hne : p₁ ≠ p₂ ∨ m₁ ≠ m₂) :
    let u₀ : ℂ := if 0 < ξ then 0 else (Real.pi / 2 : ℝ)
    ∫ t in Ioi (0 : ℝ), ∫ v in (0 : ℝ)..2 * Real.pi,
      paraboloidalHs p₁ m₁ (u₀ + I * t) ξ * paraboloidalHs p₁ m₁ v ξ *
        paraboloidalHs p₂ m₂ (u₀ + I * t) ξ * paraboloidalHs p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v)) = 0 := by
  sorry

/-- **Double orthogonality of `hc` against `hs`** (DLMF 28.31.24), for all admissible
`p₁, m₁` (for `hc`) and `p₂, m₂` (for `hs`). -/
@[dlmf 28.31.E24]
theorem paraboloidalHc_Hs_double_orthogonal {ξ : ℝ} (hξ : ξ ≠ 0) {p₁ m₁ p₂ m₂ : ℕ}
    (h₁ : m₁ ≤ p₁ ∧ m₁ % 2 = p₁ % 2) (h₂ : 1 ≤ m₂ ∧ m₂ ≤ p₂ ∧ m₂ % 2 = p₂ % 2) :
    let u₀ : ℂ := if 0 < ξ then 0 else (Real.pi / 2 : ℝ)
    ∫ t in Ioi (0 : ℝ), ∫ v in (0 : ℝ)..2 * Real.pi,
      paraboloidalHc p₁ m₁ (u₀ + I * t) ξ * paraboloidalHc p₁ m₁ v ξ *
        paraboloidalHs p₂ m₂ (u₀ + I * t) ξ * paraboloidalHs p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v)) = 0 := by
  sorry

/-- **Asymptotic behaviour, `ξ > 0`** (DLMF §28.31(iii), Asymptotic Behavior, first
paragraph): as `z → ±i∞`, `hc_p^m(z, ξ)` and `hs_p^m(z, ξ)` behave as nonzero multiples of
`exp(-¼ξ cos 2z) (cos z)^p`; every other even or odd `2π`-periodic solution of 28.31.18 (with
any `η`) behaves as a nonzero multiple of `exp(¼ξ cos 2z) (cos z)^{-p-2}`. Here `z = iy`,
`y → ±∞`. -/
@[dlmf 28.31.iii]
theorem paraboloidal_asymptotic_pos {ξ : ℝ} (hξ : 0 < ξ) {p m : ℕ} (hm : m ≤ p)
    (hpm : m % 2 = p % 2) :
    (∀ F : ℂ → ℂ, (F = fun z => paraboloidalHc p m z ξ) ∨
        (1 ≤ m ∧ F = fun z => paraboloidalHs p m z ξ) →
      ∃ C₁ C₂ : ℂ, C₁ ≠ 0 ∧ C₂ ≠ 0 ∧
        Tendsto (fun y : ℝ => F (I * y) /
          (Complex.exp (-(ξ * Complex.cos (2 * (I * y))) / 4) * Complex.cos (I * y) ^ p))
          atTop (𝓝 C₁) ∧
        Tendsto (fun y : ℝ => F (I * y) /
          (Complex.exp (-(ξ * Complex.cos (2 * (I * y))) / 4) * Complex.cos (I * y) ^ p))
          atBot (𝓝 C₂)) ∧
    ∀ (η : ℂ) (W : ℂ → ℂ),
      IsWhittakerHillSolution (η - (ξ : ℂ) ^ 2 / 8) (-((p : ℂ) + 1) * ξ) (I * ξ / 2) 1 W →
      Function.Periodic W (2 * Real.pi) → (W ≠ 0) →
      ((∀ z, W (-z) = W z) ∨ (∀ z, W (-z) = -W z)) →
      (∀ (m' : ℕ) (c : ℂ), W ≠ fun z => c * paraboloidalHc p m' z ξ) →
      (∀ (m' : ℕ) (c : ℂ), W ≠ fun z => c * paraboloidalHs p m' z ξ) →
      ∃ C₁ C₂ : ℂ, C₁ ≠ 0 ∧ C₂ ≠ 0 ∧
        Tendsto (fun y : ℝ => W (I * y) /
          (Complex.exp (ξ * Complex.cos (2 * (I * y)) / 4) * Complex.cos (I * y) ^ (-(p : ℤ) - 2)))
          atTop (𝓝 C₁) ∧
        Tendsto (fun y : ℝ => W (I * y) /
          (Complex.exp (ξ * Complex.cos (2 * (I * y)) / 4) * Complex.cos (I * y) ^ (-(p : ℤ) - 2)))
          atBot (𝓝 C₂) := by
  sorry

/-- **Asymptotic behaviour, `-ξ < 0`** (DLMF §28.31(iii), Asymptotic Behavior, second
paragraph, **corrected**): for `ξ > 0`, as `z → ½π ± i∞`, `hc_p^m(z, -ξ)` and `hs_p^m(z, -ξ)`
behave as nonzero multiples of `exp(¼ξ cos 2z) (sin z)^p` (DLMF prints
`exp(¼ξ cos 2z) (cos z)^{-p-2}`, which is wrong; see the module docstring); the other even or
odd periodic solutions behave as nonzero multiples of `exp(-¼ξ cos 2z) (sin z)^{-p-2}` (DLMF
prints `exp(-¼ξ cos 2z) (cos z)^p`). Here `z = ½π + iy`, `y → ±∞`. -/
@[dlmf 28.31.iii]
theorem paraboloidal_asymptotic_neg {ξ : ℝ} (hξ : 0 < ξ) {p m : ℕ} (hm : m ≤ p)
    (hpm : m % 2 = p % 2) :
    (∀ F : ℂ → ℂ, (F = fun z => paraboloidalHc p m z (-ξ)) ∨
        (1 ≤ m ∧ F = fun z => paraboloidalHs p m z (-ξ)) →
      ∃ C₁ C₂ : ℂ, C₁ ≠ 0 ∧ C₂ ≠ 0 ∧
        Tendsto (fun y : ℝ => F (Real.pi / 2 + I * y) /
          (Complex.exp (ξ * Complex.cos (2 * (Real.pi / 2 + I * y)) / 4) *
            Complex.sin (Real.pi / 2 + I * y) ^ p)) atTop (𝓝 C₁) ∧
        Tendsto (fun y : ℝ => F (Real.pi / 2 + I * y) /
          (Complex.exp (ξ * Complex.cos (2 * (Real.pi / 2 + I * y)) / 4) *
            Complex.sin (Real.pi / 2 + I * y) ^ p)) atBot (𝓝 C₂)) ∧
    ∀ (η : ℂ) (W : ℂ → ℂ),
      IsWhittakerHillSolution (η - (ξ : ℂ) ^ 2 / 8) (((p : ℂ) + 1) * ξ) (I * ξ / 2) 1 W →
      Function.Periodic W (2 * Real.pi) → (W ≠ 0) →
      ((∀ z, W (-z) = W z) ∨ (∀ z, W (-z) = -W z)) →
      (∀ (m' : ℕ) (c : ℂ), W ≠ fun z => c * paraboloidalHc p m' z (-ξ)) →
      (∀ (m' : ℕ) (c : ℂ), W ≠ fun z => c * paraboloidalHs p m' z (-ξ)) →
      ∃ C₁ C₂ : ℂ, C₁ ≠ 0 ∧ C₂ ≠ 0 ∧
        Tendsto (fun y : ℝ => W (Real.pi / 2 + I * y) /
          (Complex.exp (-(ξ * Complex.cos (2 * (Real.pi / 2 + I * y))) / 4) *
            Complex.sin (Real.pi / 2 + I * y) ^ (-(p : ℤ) - 2))) atTop (𝓝 C₁) ∧
        Tendsto (fun y : ℝ => W (Real.pi / 2 + I * y) /
          (Complex.exp (-(ξ * Complex.cos (2 * (Real.pi / 2 + I * y))) / 4) *
            Complex.sin (Real.pi / 2 + I * y) ^ (-(p : ℤ) - 2))) atBot (𝓝 C₂) := by
  sorry

end DLMF.Mathieu
