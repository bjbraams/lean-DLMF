/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import DLMFMathlib.Analysis.SpecialFunctions.ChebyshevSeries

/-!
# Chebyshev expansions (Temme §6.9.2)

With `x = cos θ` an expansion `f(x) = c₀/2 + ∑ cₙ Tₙ(x)` is the Fourier cosine series of
`θ ↦ f(cos θ)`, with `cₙ = (2/π) ∫₀^π f(cos θ) cos(nθ) dθ` (Temme (6.65)–(6.66)). This file
transfers Mathlib's Fourier theory on `AddCircle` to Chebyshev series and adds the facts used
in numerical work.

## Main results

* `chebyshevCoeff_eq_integral_measureT`: the coefficients as integrals against Mathlib's
  Chebyshev measure `dx/√(1-x²)`.
* `hasSum_chebyshevCoeff_mul_T`: for `f` continuous on `[-1,1]` with absolutely summable
  coefficients, the Chebyshev series converges to `f` on `[-1,1]`.
* `abs_chebyshevCoeff_le`: `|cₙ| ≤ 2M ρ^{-n}` for `f` analytic and bounded by `M` in the closed
  Bernstein ellipse `E_ρ`, by a contour shift in `θ`.
* `abs_sub_sum_chebyshevCoeff_mul_T_le`: the resulting uniform truncation error
  `2M ρ^{-N}/(1 - ρ^{-1})`.
* `sum_chebyshevT_eq_clenshaw`: Clenshaw's backward recurrence for evaluating Chebyshev sums,
  from the general three-term form `sum_mul_eq_clenshaw`.
* `hasSum_chebyshevT_recip_add`: Temme's Example 6.3,
  `1/(x+a) = (2/√(a²-1)) (1/2 + ∑_{n≥1} (√(a²-1) - a)ⁿ Tₙ(x))` for `a > 1`.
-/

@[expose] public section

open Complex Filter MeasureTheory Set Polynomial
open scoped Real Topology Nat

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The Chebyshev coefficient `cₙ = (2/π) ∫₀^π f(cos θ) cos(nθ) dθ` (Temme (6.66)). -/
def chebyshevCoeff (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 / π * ∫ θ in (0 : ℝ)..π, f (Real.cos θ) * Real.cos (n * θ)

/-- The coefficients as integrals against the Chebyshev weight `dx/√(1-x²)` (Temme (6.65)). -/
theorem chebyshevCoeff_eq_integral_measureT (f : ℝ → ℝ) (n : ℕ) :
    chebyshevCoeff f n = 2 / π * ∫ x, f x * (Chebyshev.T ℝ n).eval x ∂Chebyshev.measureT := by
  rw [chebyshevCoeff, Chebyshev.integral_measureT_eq_integral_cos]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have := Chebyshev.T_real_cos θ (n : ℤ)
  push_cast at this ⊢
  rw [this]

/-- The complex coefficients extend the existing real Chebyshev coefficients. -/
theorem complexCoeff_ofReal (f : ℝ → ℝ) (n : ℕ) :
    Polynomial.Chebyshev.complexCoeff (fun x => (f x : ℂ)) n = (chebyshevCoeff f n : ℂ) := by
  unfold Polynomial.Chebyshev.complexCoeff chebyshevCoeff
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    ← intervalIntegral.integral_ofReal]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  push_cast
  rfl

/-! ### Clenshaw's algorithm -/

/-- Clenshaw's backward recurrence `b_k = c_k + 2x b_{k+1} - b_{k+2}`, `b_{N+1} = b_{N+2} = 0`,
returning `(b₀, b₁)` for the coefficients `c₀, …, c_N`. -/
def clenshaw {R : Type*} [CommRing R] (x : R) : ℕ → (ℕ → R) → R × R
  | 0, c => (c 0, 0)
  | N + 1, c =>
    let p := clenshaw x N (fun k => c (k + 1))
    (c 0 + 2 * x * p.1 - p.2, p.1)

/-- Clenshaw's identity for any sequence obeying the three-term recurrence
`Y_{k+2} = 2x Y_{k+1} - Y_k`. -/
theorem sum_mul_eq_clenshaw {R : Type*} [CommRing R] (x : R) (N : ℕ) (c Y : ℕ → R)
    (hY : ∀ k, Y (k + 2) = 2 * x * Y (k + 1) - Y k) :
    ∑ k ∈ Finset.range (N + 1), c k * Y k =
      (clenshaw x N c).1 * Y 0 + (clenshaw x N c).2 * (Y 1 - 2 * x * Y 0) := by
  induction N generalizing c Y with
  | zero => simp [clenshaw]
  | succ N ih =>
    rw [Finset.sum_range_succ', ih (fun k => c (k + 1)) (fun k => Y (k + 1)) (fun k => hY (k + 1))]
    simp only [clenshaw, zero_add]
    rw [hY 0]
    ring

/-- **Clenshaw's algorithm** for Chebyshev sums (Temme §6.9.2):
`∑_{k ≤ N} cₖ Tₖ(x) = b₀ - x b₁`. -/
theorem sum_chebyshevT_eq_clenshaw {R : Type*} [CommRing R] (x : R) (N : ℕ) (c : ℕ → R) :
    ∑ k ∈ Finset.range (N + 1), c k * (Chebyshev.T R k).eval x =
      (clenshaw x N c).1 - x * (clenshaw x N c).2 := by
  rw [sum_mul_eq_clenshaw x N c (fun k => (Chebyshev.T R k).eval x) (fun k => by
    have := Chebyshev.T_add_two R (k : ℤ)
    push_cast
    rw [this]; simp)]
  simp [Chebyshev.T_zero, Chebyshev.T_one]
  ring

/-- **Temme's Example 6.3**: for `a > 1` and `|x| ≤ 1`, with `s = √(a²-1)` and `λ = s - a`,
`1/(x+a) = (2/s) (1/2 + ∑_{n≥1} λⁿ Tₙ(x))`. -/
theorem hasSum_chebyshevT_recip_add {a x : ℝ} (ha : 1 < a) (hx : |x| ≤ 1) :
    HasSum (fun n : ℕ => (if n = 0 then 1 else 2) / Real.sqrt (a ^ 2 - 1) *
      (Real.sqrt (a ^ 2 - 1) - a) ^ n * (Chebyshev.T ℝ n).eval x) (1 / (x + a)) := by
  set s := Real.sqrt (a ^ 2 - 1) with hs
  set l := s - a with hl
  have hs2 : s ^ 2 = a ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hsa : s < a := by nlinarith
  have hsa1 : a - 1 < s := by nlinarith
  have hl1 : |l| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hxa : 0 < x + a := by linarith [(abs_le.mp hx).1]
  have hlq : l ^ 2 + 2 * a * l + 1 = 0 := by rw [hl]; nlinarith
  -- the generating function at `z = λ`
  have hG := chebyshevT_generating_function hx (z := (l : ℂ)) (by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hl1)
  have hGr : HasSum (fun n : ℕ => (Chebyshev.T ℝ n).eval x * l ^ n)
      ((1 - x * l) / (1 - 2 * x * l + l ^ 2)) := by
    rw [← Complex.hasSum_ofReal]
    convert hG using 1
    · funext n
      push_cast
      rfl
    · push_cast; ring
  have hden : 1 - 2 * x * l + l ^ 2 = -2 * l * (x + a) := by linear_combination hlq
  have hl0 : l ≠ 0 := by intro h; rw [h] at hlq; norm_num at hlq
  have h := (hGr.mul_left (2 / s)).sub (hasSum_ite_eq 0 (1 / s))
  convert h using 1
  · funext n
    split_ifs with hn
    · subst hn; simp [Chebyshev.T_zero]; ring
    · ring
  · rw [hden]
    have h1 : 1 + l * a = -s * l := by rw [hl]; nlinarith
    field_simp
    linear_combination h1

/-! ### Convergence of Chebyshev series -/

/-- `θ ↦ f(cos θ)` as a continuous function on the circle `ℝ/2πℤ`. -/
def chebyshevCircleFun {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    C(AddCircle (2 * π), ℂ) :=
  Polynomial.Chebyshev.complexCircleFun (Complex.continuous_ofReal.comp_continuousOn hf)

theorem chebyshevCircleFun_coe {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) (θ : ℝ) :
    chebyshevCircleFun hf (θ : AddCircle (2 * π)) = f (Real.cos θ) := rfl

local instance instTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The full-period integral `∫₀^{2π} e^{-inθ} f(cos θ) dθ = π c_{|n|}`. -/
theorem integral_exp_mul_comp_cos {f : ℝ → ℝ} (hcf : Continuous fun x : ℝ => f (Real.cos x))
    (n : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Complex.exp (-(I * n * x)) * ((f (Real.cos x) : ℝ) : ℂ) =
      π * chebyshevCoeff f n.natAbs := by
  have h := Polynomial.Chebyshev.integral_exp_mul_comp_cos_complex
    (f := fun x => (f x : ℂ)) (Complex.continuous_ofReal.comp hcf) n
  simpa only [complexCoeff_ofReal] using h

/-- The Fourier coefficients of `θ ↦ f(cos θ)` are half the Chebyshev coefficients. -/
theorem fourierCoeff_chebyshevCircleFun {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) (n : ℤ) :
    fourierCoeff (chebyshevCircleFun hf) n = (chebyshevCoeff f n.natAbs / 2 : ℝ) := by
  have h := Polynomial.Chebyshev.fourierCoeff_complexCircleFun (f := fun x => (f x : ℂ))
    (Complex.continuous_ofReal.comp_continuousOn hf) n
  simpa only [chebyshevCircleFun, complexCoeff_ofReal, Complex.ofReal_div,
    Complex.ofReal_ofNat] using h

/-- **Convergence of Chebyshev series** (Temme (6.65)–(6.66)): if `f` is continuous on `[-1,1]`
and its Chebyshev coefficients are absolutely summable, then
`f(x) = c₀/2 + ∑_{n≥1} cₙ Tₙ(x)` for every `x ∈ [-1,1]`. -/
theorem hasSum_chebyshevCoeff_mul_T {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hs : Summable fun n => |chebyshevCoeff f n|) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    HasSum (fun n : ℕ => (if n = 0 then 1 / 2 else 1) * chebyshevCoeff f n *
      (Chebyshev.T ℝ n).eval x) (f x) := by
  have hsC : Summable fun n => ‖Polynomial.Chebyshev.complexCoeff
      (fun x => (f x : ℂ)) n‖ := hs.congr fun n => by
    rw [complexCoeff_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have h := Polynomial.Chebyshev.hasSum_complexCoeff_mul_T (f := fun x => (f x : ℂ))
    (Complex.continuous_ofReal.comp_continuousOn hf) hsC hx
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  funext n
  rw [complexCoeff_ofReal, ← Chebyshev.complex_ofReal_eval_T]
  split_ifs <;> push_cast <;> rfl

/-! ### Functions analytic in a Bernstein ellipse -/

/-- **Geometric decay of Chebyshev coefficients** (Temme §6.9.2; Rivlin): if `f` extends to a
function `F` analytic on the closed Bernstein ellipse `E_ρ = cos({|Im w| ≤ s})`, `ρ = e^s`, with
`|F| ≤ M` there, then `|cₙ| ≤ 2M ρ^{-n}`. -/
theorem abs_chebyshevCoeff_le {f : ℝ → ℝ} {F : ℂ → ℂ} {s M : ℝ} (hs : 0 ≤ s)
    (hF : ∀ w : ℂ, |w.im| ≤ s → DifferentiableAt ℂ F (Complex.cos w))
    (hM : ∀ w : ℂ, |w.im| ≤ s → ‖F (Complex.cos w)‖ ≤ M)
    (hFf : ∀ x ∈ Icc (-1 : ℝ) 1, F x = f x) (n : ℕ) :
    |chebyshevCoeff f n| ≤ 2 * M * Real.exp (-(n * s)) := by
  have h := Polynomial.Chebyshev.norm_complexCoeff_le (f := fun x => (f x : ℂ))
    hs hF hM hFf n
  simpa only [complexCoeff_ofReal, Complex.norm_real, Real.norm_eq_abs] using h

/-- **Truncation error of Chebyshev series** for functions analytic in the Bernstein ellipse
`E_ρ`, `ρ = e^s > 1`, with `|F| ≤ M` there: uniformly on `[-1,1]`,
`|f(x) - (c₀/2 + ∑_{1≤n<N} cₙ Tₙ(x))| ≤ 2M ρ^{-N} / (1 - ρ^{-1})`. -/
theorem abs_sub_sum_chebyshevCoeff_mul_T_le {f : ℝ → ℝ} {F : ℂ → ℂ} {s M : ℝ} (hs : 0 < s)
    (hF : ∀ w : ℂ, |w.im| ≤ s → DifferentiableAt ℂ F (Complex.cos w))
    (hM : ∀ w : ℂ, |w.im| ≤ s → ‖F (Complex.cos w)‖ ≤ M)
    (hFf : ∀ x ∈ Icc (-1 : ℝ) 1, F x = f x) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (N : ℕ) :
    |f x - ∑ n ∈ Finset.range N, (if n = 0 then 1 / 2 else 1) * chebyshevCoeff f n *
      (Chebyshev.T ℝ n).eval x| ≤ 2 * M * Real.exp (-s) ^ N / (1 - Real.exp (-s)) := by
  set r := Real.exp (-s) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hdecay : ∀ n : ℕ, |chebyshevCoeff f n| ≤ 2 * M * r ^ n := fun n => by
    rw [hr, ← Real.exp_nat_mul, show (n : ℝ) * -s = -(n * s) by ring]
    exact abs_chebyshevCoeff_le hs.le hF hM hFf n
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp [hs.le]))
  have hgeo : Summable fun n : ℕ => 2 * M * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  -- continuity of `f` on `[-1, 1]`
  have hfc : ContinuousOn f (Icc (-1) 1) := by
    intro y hy
    have hcy : Complex.cos (Real.arccos y) = y := by
      rw [← Complex.ofReal_cos, Real.cos_arccos hy.1 hy.2]
    have hd := hF (Real.arccos y) (by simp [hs.le])
    rw [hcy] at hd
    have hcont : ContinuousAt (fun t : ℝ => (F t).re) y :=
      Complex.continuous_re.continuousAt.comp
        (hd.continuousAt.comp Complex.continuous_ofReal.continuousAt)
    refine (hcont.continuousWithinAt).congr (fun t ht => ?_) ?_
    · rw [hFf t ht, Complex.ofReal_re]
    · rw [hFf y hy, Complex.ofReal_re]
  have hsum := hasSum_chebyshevCoeff_mul_T hfc
    (Summable.of_nonneg_of_le (fun n => abs_nonneg _) hdecay hgeo) hx
  set a : ℕ → ℝ := fun n => (if n = 0 then 1 / 2 else 1) * chebyshevCoeff f n *
    (Chebyshev.T ℝ n).eval x with ha
  have hab : ∀ n, |a n| ≤ 2 * M * r ^ n := by
    intro n
    have hT := Chebyshev.abs_eval_T_real_le_one (n : ℤ) (abs_le.mpr ⟨hx.1, hx.2⟩)
    have hc : |(if n = 0 then (1 / 2 : ℝ) else 1)| ≤ 1 := by split_ifs <;> norm_num
    calc |a n| = |(if n = 0 then (1 / 2 : ℝ) else 1)| * |chebyshevCoeff f n| *
          |(Chebyshev.T ℝ n).eval x| := by simp only [ha, abs_mul]
      _ ≤ 1 * |chebyshevCoeff f n| * 1 := by gcongr
      _ ≤ 2 * M * r ^ n := by linarith [hdecay n]
  rw [← hsum.tsum_eq, ← (hsum.summable).sum_add_tsum_nat_add N, add_sub_cancel_left]
  have htail : Summable fun n => |a (n + N)| :=
    (Summable.of_nonneg_of_le (fun n => abs_nonneg _) hab hgeo).comp_injective
      (add_left_injective N)
  calc |∑' n, a (n + N)| ≤ ∑' n, |a (n + N)| := by
        have := norm_tsum_le_tsum_norm (f := fun n => a (n + N))
          (by simpa only [Real.norm_eq_abs] using htail)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' n : ℕ, 2 * M * r ^ N * r ^ n := by
        refine htail.tsum_le_tsum (fun n => ?_)
          ((summable_geometric_of_lt_one hr0 hr1).mul_left _)
        rw [mul_assoc, ← pow_add, add_comm N n]
        exact hab (n + N)
    _ = 2 * M * r ^ N / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

end DLMF.OrthogonalPolynomials
