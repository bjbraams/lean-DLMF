/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Harmonics
public import DLMF.Legendre.QAdditionTools

/-!
# Legendre addition theorems and zonal harmonic series

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- DLMF 14.18.1: for `θ₁, θ₂ ≥ 0` with `θ₁ + θ₂ < π` and real `φ`, `𝖯_ν(cos θ₁ cos θ₂ + sin θ₁ sin
θ₂ cos φ) = 𝖯_ν(cos θ₁) 𝖯_ν(cos θ₂) + 2 Σ_{m≥1} (-1)^m 𝖯^{-m}_ν(cos θ₁) 𝖯^m_ν(cos θ₂) cos(mφ)`, as a
convergent series. -/
@[dlmf 14.18.E1]
theorem ferrersP_addition (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁+θ₂ < π) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*ferrersP ν (-m) (Real.cos θ₁)*ferrersP ν m (Real.cos θ₂)*Real.cos (m*phi)) (ferrersP ν 0 (Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi)-ferrersP ν 0 (Real.cos θ₁)*ferrersP ν 0 (Real.cos θ₂)) := by
  -- Fourier expansion in `phi`; coefficients by Carlson's theorem (type `θ₁ + θ₂ < π`) from
  -- the integer case `legAdd_fer_nat`.
  exact legAdd_ferrersP_addition_of_nat h1 h2 hs (legAdd_fer_nat h1 h2 hs) ν phi

/-- DLMF 14.18.3: for `0 < θ₁ < θ₂` with `θ₁ < π/2`, `θ₁ + θ₂ < π`, real `φ` and `ν` not a negative
integer, `𝖰_ν(cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos φ) = 𝖯_ν(cos θ₁) 𝖰_ν(cos θ₂) + 2 Σ_{m≥1} (-1)^m
𝖯^{-m}_ν(cos θ₁) 𝖰^m_ν(cos θ₂) cos(mφ)`, as a convergent series. -/
@[dlmf 14.18.E3]
theorem ferrersQ_addition (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h2 : 0 < θ₂) (hs : θ₁+θ₂ < π) (hhalf : θ₁ < π/2) (h12 : θ₁ < θ₂) (hr : LegendreQRegular ν 0) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*ferrersP ν (-m) (Real.cos θ₁)*ferrersQ ν m (Real.cos θ₂)*Real.cos (m*phi)) (ferrersQ ν 0 (Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi)-ferrersP ν 0 (Real.cos θ₁)*ferrersQ ν 0 (Real.cos θ₂)) := by
  -- Non-real `ν`: 14.18.1 at `(θ₁, θ₂)` and `(θ₁, π - θ₂)` with 14.9.10; then continuity in `ν`.
  -- The hypothesis `θ₁ < π/2` is not needed.
  exact legQAdd_ferrersQ_addition ν h1.le h12 hs hr phi

/-- DLMF 14.18.2: for natural `n`, `θ₁, θ₂ ≥ 0` with `θ₁ + θ₂ < π` and real `φ`, `P_n(cos θ₁ cos θ₂
+ sin θ₁ sin θ₂ cos φ) = Σ_{m=-n}^{n} (-1)^m 𝖯^{-m}_n(cos θ₁) 𝖯^m_n(cos θ₂) cos(mφ)`. -/
@[dlmf 14.18.E2]
theorem ferrersP_nat_addition (n : ℕ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁+θ₂ < π) (phi : ℝ) :
    ferrersP n 0 (Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi)=∑ m ∈ Finset.Icc (-(n:ℤ)) n, (-1:ℂ)^m*ferrersP n (-m) (Real.cos θ₁)*ferrersP n m (Real.cos θ₂)*Real.cos (m*phi) := by
  have hθ1 : θ₁ < π := by linarith
  have hθ2 : θ₂ < π := by linarith
  have hcos : ∀ θ, 0 ≤ θ → θ < π → Real.cos θ ∈ Ioc (-1:ℝ) 1 := fun θ h0 hπ =>
    ⟨by rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0 le_rfl hπ, Real.cos_le_one θ⟩
  have hx1 := hcos θ₁ h1 hθ1
  have hx2 := hcos θ₂ h2 hθ2
  have hs1 : 0 ≤ Real.sin θ₁ := Real.sin_nonneg_of_nonneg_of_le_pi h1 hθ1.le
  have hs2 : 0 ≤ Real.sin θ₂ := Real.sin_nonneg_of_nonneg_of_le_pi h2 hθ2.le
  have hsin : ∀ θ, 0 ≤ θ → θ < π → Real.sqrt (1 - Real.cos θ^2) = Real.sin θ := fun θ h0 hπ =>
    (Real.sin_eq_sqrt_one_sub_cos_sq h0 hπ.le).symm
  have harg : -1 < Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi := by
    have hc : -1 < Real.cos (θ₁+θ₂) := by
      rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) le_rfl hs
    rw [Real.cos_add] at hc
    nlinarith [mul_nonneg hs1 hs2, Real.neg_one_le_cos phi]
  have hsl : 1 + ((Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi : ℝ) : ℂ) ∈ slitPlane :=
    Or.inl (by simp only [add_re, one_re, ofReal_re]; linarith)
  rw [ferrersP_zero _ harg, legendreP_nat n hsl]
  have hk := DLMF.OrthogonalPolynomials.LegendreAddition.legendre_eq_kernel n (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁)
    (Real.sin θ₂) (phi:ℂ) (by rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring)
    (by rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring)
  have hF : ∀ k : ℕ, ∀ θ, 0 ≤ θ → θ < π → ferrersPNat n k (Real.cos θ) =
      (-1)^k * (Real.sin θ:ℂ)^k * DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ) := by
    intro k θ h0 hπ
    rw [ferrersPNat, hsin θ h0 hπ]; rfl
  have hterm : ∀ k : ℕ, k ≤ n →
      ferrersP n (-(k:ℂ)) (Real.cos θ₁) * ferrersP n k (Real.cos θ₂) =
        (-1)^k * DLMF.OrthogonalPolynomials.LegendreAddition.coeff n k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) ∧
      ferrersP n k (Real.cos θ₁) * ferrersP n (-(k:ℂ)) (Real.cos θ₂) =
        (-1)^k * DLMF.OrthogonalPolynomials.LegendreAddition.coeff n k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) := by
    intro k hkn
    rw [legAdd_ferrersP_neg_nat_eq_ferrersPNat n k hkn hx1,
      legAdd_ferrersP_neg_nat_eq_ferrersPNat n k hkn hx2,
      legAdd_ferrersP_nat_eq_ferrersPNat n k hx1, legAdd_ferrersP_nat_eq_ferrersPNat n k hx2,
      hF k θ₁ h1 hθ1, hF k θ₂ h2 hθ2]
    have hs : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
    simp only [DLMF.OrthogonalPolynomials.LegendreAddition.coeff, DLMF.OrthogonalPolynomials.LegendreAddition.weight]
    constructor
    · linear_combination ((-1:ℂ)^k * ((n-k).factorial / (n+k).factorial : ℂ) * (Real.sin θ₁:ℂ)^k *
        DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ₁) * (Real.sin θ₂:ℂ)^k * DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ₂)) * hs
    · linear_combination ((-1:ℂ)^k * ((n-k).factorial / (n+k).factorial : ℂ) * (Real.sin θ₁:ℂ)^k *
        DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ₁) * (Real.sin θ₂:ℂ)^k * DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ₂)) * hs
  push_cast at hk ⊢
  rw [hk, sum_Icc_neg_pair, DLMF.OrthogonalPolynomials.LegendreAddition.kernel, Finset.mul_sum]
  congr 1
  · have := (hterm 0 (Nat.zero_le _)).1
    push_cast at this
    simp only [neg_zero, pow_zero, one_mul] at this
    simp only [Int.cast_zero, neg_zero, zpow_zero, one_mul, zero_mul, Complex.cos_zero, mul_one]
    rw [this]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkl : k+1 ≤ n := by simp at hk; omega
    obtain ⟨h3, h4⟩ := hterm (k+1) hkl
    push_cast at h3 h4
    have hz : ((-1:ℂ))^(-((k:ℤ)+1)) = (-1)^(k+1) := by
      rw [zpow_neg, show ((k:ℤ)+1) = ((k+1:ℕ):ℤ) by push_cast; ring, zpow_natCast, ← inv_pow]; norm_num
    have hz2 : ((-1:ℂ))^((k:ℤ)+1) = (-1)^(k+1) := by
      rw [show ((k:ℤ)+1) = ((k+1:ℕ):ℤ) by push_cast; ring, zpow_natCast]
    have hs : ((-1:ℂ))^(k+1) * (-1)^(k+1) = 1 := by rw [← mul_pow]; norm_num
    push_cast [hz, hz2]
    rw [show -(-((k:ℂ)+1)) = (k:ℂ)+1 by ring, mul_assoc ((-1:ℂ)^(k+1)) (ferrersP _ _ _), h3,
      mul_assoc ((-1:ℂ)^(k+1)) (ferrersP _ _ _), h4, show -((k:ℂ)+1) * phi = -(((k:ℂ)+1)*phi) by ring,
      Complex.cos_neg]
    linear_combination (-2 * DLMF.OrthogonalPolynomials.LegendreAddition.coeff n (k+1) (Complex.cos θ₁) (Complex.cos θ₂) (Complex.sin θ₁) (Complex.sin θ₂) * Complex.cos (((k:ℂ)+1)*phi)) * hs

/-- At coincident arguments and phi zero, the order-zero P value is understood by its regular extension at one. -/
@[dlmf 14.18.E4]
theorem associatedP_addition (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*associatedP ν (-m) (Real.cosh ξ₁)*associatedP ν m (Real.cosh ξ₂)*Real.cos (m*phi)) (associatedP ν 0 (Real.cosh ξ₁*Real.cosh ξ₂-Real.sinh ξ₁*Real.sinh ξ₂*Real.cos phi)-associatedP ν 0 (Real.cosh ξ₁)*associatedP ν 0 (Real.cosh ξ₂)) := by
  -- Fourier expansion in `phi`; coefficients by Carlson's theorem from the integer case.
  exact legAdd_associatedP_addition ν h1 h2 phi

/-- DLMF 14.18.5: for `0 < ξ₁ < ξ₂`, real `φ` and `ν` not a negative integer, `Q_ν(cosh ξ₁ cosh ξ₂ -
sinh ξ₁ sinh ξ₂ cos φ) = P_ν(cosh ξ₁) Q_ν(cosh ξ₂) + 2 Σ_{m≥1} (-1)^m P^{-m}_ν(cosh ξ₁) Q^m_ν(cosh
ξ₂) cos(mφ)`, as a convergent series. -/
@[dlmf 14.18.E5]
theorem associatedQ_addition (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (h12 : ξ₁ < ξ₂) (hr : LegendreQRegular ν 0) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*associatedP ν (-m) (Real.cosh ξ₁)*associatedQ ν m (Real.cosh ξ₂)*Real.cos (m*phi)) (associatedQ ν 0 (Real.cosh ξ₁*Real.cosh ξ₂-Real.sinh ξ₁*Real.sinh ξ₂*Real.cos phi)-associatedP ν 0 (Real.cosh ξ₁)*associatedQ ν 0 (Real.cosh ξ₂)) := by
  sorry

/-- DLMF 14.18.6 (Christoffel–Darboux): for `x, y ∉ (-∞, 1]`, `(x-y) Σ_{k=0}^{n} (2k+1) P_k(x)
P_k(y) = (n+1)(P_{n+1}(x) P_n(y) - P_n(x) P_{n+1}(y))`. -/
@[dlmf 14.18.E6]
theorem legendre_christoffel_6 (n : ℕ) {x y : ℂ} (hx : x-1 ∈ slitPlane) (hy : y-1 ∈ slitPlane) :
    (x-y)*(∑ k ∈ Finset.range (n+1), (2*k+1:ℂ)*associatedP k 0 x*associatedP k 0 y)=(n+1:ℂ)*(associatedP (n+1) 0 x*associatedP n 0 y-associatedP n 0 x*associatedP (n+1) 0 y) := by
  have hP : ∀ z : ℂ, z-1 ∈ slitPlane → ∀ k : ℕ, associatedP k 0 z = DLMF.OrthogonalPolynomials.legendrePolyP k z := by
    intro z hz k
    have hz' : 1+z ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hz ⊢
      simp only [add_re, one_re, add_im, one_im, zero_add, sub_re, sub_im] at hz ⊢
      rcases hz with h | h
      · left; linarith
      · right; simpa using h
    rw [associatedP_zero_order _ hz, legendreP_nat k hz']
  have key : ∀ n : ℕ, (x-y)*(∑ k ∈ Finset.range (n+1), (2*k+1:ℂ)*DLMF.OrthogonalPolynomials.legendrePolyP k x*DLMF.OrthogonalPolynomials.legendrePolyP k y) =
      (n+1:ℂ)*(DLMF.OrthogonalPolynomials.legendrePolyP (n+1) x*DLMF.OrthogonalPolynomials.legendrePolyP n y-DLMF.OrthogonalPolynomials.legendrePolyP n x*DLMF.OrthogonalPolynomials.legendrePolyP (n+1) y) := by
    intro n
    induction n with
    | zero => simp [DLMF.OrthogonalPolynomials.legendrePolyP_one, DLMF.OrthogonalPolynomials.legendrePolyP_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hx2 := DLMF.OrthogonalPolynomials.legendrePolyP_recurrence n x
      have hy2 := DLMF.OrthogonalPolynomials.legendrePolyP_recurrence n y
      push_cast
      rw [show n+1+1 = n+2 by ring]
      linear_combination DLMF.OrthogonalPolynomials.legendrePolyP (n+1) x * hy2 - DLMF.OrthogonalPolynomials.legendrePolyP (n+1) y * hx2
  have := key n
  simp only [← hP x hx, ← hP y hy] at this
  push_cast at this
  exact this

/-- DLMF 14.18.7: for `x, y ∉ (-∞, 1]`, `(x-y) Σ_{k=0}^{n} (2k+1) P_k(x) Q_k(y) = (n+1)(P_{n+1}(x)
Q_n(y) - P_n(x) Q_{n+1}(y)) - 1`. -/
@[dlmf 14.18.E7]
theorem legendre_christoffel_7 (n : ℕ) {x y : ℂ} (hx : x-1 ∈ slitPlane) (hy : y-1 ∈ slitPlane) :
    (x-y)*(∑ k ∈ Finset.range (n+1), (2*k+1:ℂ)*associatedP k 0 x*associatedQ k 0 y)=(n+1:ℂ)*(associatedP (n+1) 0 x*associatedQ n 0 y-associatedP n 0 x*associatedQ (n+1) 0 y)-1 := by
  have hx' := one_add_mem_slitPlane_of_sub_one hx
  simp only [associatedP_zero_order _ hx, associatedQ_zero_order _ hy]
  have hP0 : legendreP 0 x = 1 := by
    have := legendreP_nat 0 hx'; simpa [DLMF.OrthogonalPolynomials.legendrePolyP_zero] using this
  have hP1 : legendreP 1 x = x := by
    have := legendreP_nat 1 hx'; simpa [DLMF.OrthogonalPolynomials.legendrePolyP_one] using this
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, one_mul]
    rw [hP0, hP1, legendreQ_one hy]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hp := legendreP_recurrence ((n:ℂ)+1) hx'
    have hq := legendreQ_recurrence (ν := (n:ℂ)+1) (by exact_mod_cast Nat.succ_ne_zero n) hy
    push_cast
    rw [show (n:ℂ)+1-1 = n by ring] at hp hq
    linear_combination -legendreQ ((n:ℂ)+1) y * hp + legendreP ((n:ℂ)+1) x * hq

/-- DLMF 14.18.8: for non-integer `ν` and `-1 < x < 1`, `𝖯_ν(-x) = (sin(νπ)/π) Σ_{n≥0}
(2n+1)/((ν-n)(ν+n+1)) 𝖯_n(x)`, as a convergent series. -/
@[dlmf 14.18.E8]
theorem ferrersP_zonal_series {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun n : ℕ => sin (ν*π)/π*(2*n+1)/((ν-n)*(ν+n+1))*ferrersP n 0 x) (ferrersP ν 0 (-x)) := by
  sorry

/-- DLMF 14.18.9: for non-integer `ν`, real `μ ≥ 0` and `-1 < x ≤ 1`, the partial sums of
`(sin(νπ)/π) Σ_{n≥0} (-1)^n (2n+1)/((ν-n)(ν+n+1)) 𝖯^{-μ}_n(x)` converge to `𝖯^{-μ}_ν(x)`. -/
@[dlmf 14.18.E9]
theorem ferrersP_dougall_series {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {μ : ℝ} (hμ : 0 ≤ μ) {x : ℝ} (hx : x ∈ Ioc (-1:ℝ) 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, sin (ν*π)/π*(-1)^n*(2*n+1)/((ν-n)*(ν+n+1))*ferrersP n (-μ) x) atTop (𝓝 (ferrersP ν (-μ) x)) := by
  sorry

/-- Confocal ellipse coordinate, with value two on the focal segment. -/
def legendreEllipseRadius (z : ℂ) : ℝ :=
  ‖z-1‖+‖z+1‖

/-! ### Heine's expansion (14.28.2): helper lemmas -/

/-- The Laplace integrals `∫₀^π (z + w cos t)^n dt` with `w² = z² - 1` satisfy the Legendre
recurrence. -/
private lemma heine_laplace_recurrence {z w : ℂ} (hw : w ^ 2 = z ^ 2 - 1) (n : ℕ) :
    (n + 2 : ℂ) * (∫ t : ℝ in (0 : ℝ)..π, (z + w * Real.cos t) ^ (n + 2)) =
      (2 * n + 3) * z * (∫ t : ℝ in (0 : ℝ)..π, (z + w * Real.cos t) ^ (n + 1)) -
        (n + 1) * ∫ t : ℝ in (0 : ℝ)..π, (z + w * Real.cos t) ^ n := by
  set W : ℝ → ℂ := fun t => z + w * Real.cos t with hW
  have hD : ∀ t : ℝ, HasDerivAt (fun t : ℝ => W t ^ (n + 1) * (Real.sin t : ℂ))
      ((n + 1 : ℂ) * W t ^ n * (-w * Real.sin t) * Real.sin t +
        W t ^ (n + 1) * Real.cos t) t := by
    intro t
    have hwd : HasDerivAt W (-w * Real.sin t) t := by
      have := ((Real.hasDerivAt_cos t).ofReal_comp).const_mul w
      exact (this.const_add z).congr_deriv (by push_cast; ring)
    have := (hwd.pow (n + 1)).mul (Real.hasDerivAt_sin t).ofReal_comp
    exact this.congr_deriv (by simp only [Pi.pow_apply, Nat.add_sub_cancel]; push_cast; ring)
  have hcont : Continuous fun t : ℝ => (n + 1 : ℂ) * W t ^ n * (-w * Real.sin t) *
      Real.sin t + W t ^ (n + 1) * Real.cos t := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t)
    (hcont.intervalIntegrable 0 π)
  simp only [Real.sin_pi, Real.sin_zero, Complex.ofReal_zero, mul_zero, sub_zero] at hint
  have hpt : ∀ t : ℝ, w * ((n + 1 : ℂ) * W t ^ n * (-w * Real.sin t) * Real.sin t +
      W t ^ (n + 1) * Real.cos t) = (n + 1) * W t ^ n - (2 * n + 3) * z * W t ^ (n + 1) +
        (n + 2) * W t ^ (n + 2) := by
    intro t
    have htrig : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.sin_sq_add_cos_sq]; simp
    simp only [hW]
    linear_combination (-(n + 1 : ℂ) * (z + w * Real.cos t) ^ n * w ^ 2) * htrig -
      ((n + 1 : ℂ) * (z + w * Real.cos t) ^ n) * hw
  have h0 : ∫ t : ℝ in (0 : ℝ)..π, w * ((n + 1 : ℂ) * W t ^ n * (-w * Real.sin t) *
      Real.sin t + W t ^ (n + 1) * Real.cos t) = 0 := by
    rw [intervalIntegral.integral_const_mul, hint]; simp
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)] at h0
  have hc' : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => W t ^ k) volume 0 π :=
    fun k => (by fun_prop : Continuous fun t : ℝ => W t ^ k).intervalIntegrable 0 π
  rw [intervalIntegral.integral_add (((hc' n).const_mul _).sub ((hc' (n + 1)).const_mul _))
    ((hc' (n + 2)).const_mul _), intervalIntegral.integral_sub ((hc' n).const_mul _)
    ((hc' (n + 1)).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
  linear_combination h0

/-- Laplace's integral for complex argument: `π P_n(z) = ∫₀^π (z + w cos t)^n dt` whenever
`w² = z² - 1`. -/
private lemma heine_laplace {z w : ℂ} (hw : w ^ 2 = z ^ 2 - 1) (n : ℕ) :
    (π : ℂ) * DLMF.OrthogonalPolynomials.legendrePolyP n z =
      ∫ t : ℝ in (0 : ℝ)..π, (z + w * Real.cos t) ^ n := by
  suffices h : ∀ n : ℕ, (π : ℂ) * DLMF.OrthogonalPolynomials.legendrePolyP n z =
      (∫ t : ℝ in (0 : ℝ)..π, (z + w * Real.cos t) ^ n) ∧
      (π : ℂ) * DLMF.OrthogonalPolynomials.legendrePolyP (n + 1) z =
      ∫ t : ℝ in (0 : ℝ)..π, (z + w * Real.cos t) ^ (n + 1) from (h n).1
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [DLMF.OrthogonalPolynomials.legendrePolyP_zero]
    · simp only [zero_add, pow_one, DLMF.OrthogonalPolynomials.legendrePolyP_one]
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((by fun_prop : Continuous fun t : ℝ => w * Real.cos t).intervalIntegrable 0 π),
        intervalIntegral.integral_const_mul,
        show ∫ x in (0 : ℝ)..π, ((Real.cos x : ℝ) : ℂ) = ((∫ x in (0 : ℝ)..π, Real.cos x : ℝ) : ℂ)
          from intervalIntegral.integral_ofReal, integral_cos]
      simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hr := heine_laplace_recurrence hw n
    have hP := DLMF.OrthogonalPolynomials.legendrePolyP_recurrence n z
    rw [← ih.1, ← ih.2] at hr
    have hn : (n + 2 : ℂ) ≠ 0 := by norm_cast
    apply mul_left_cancel₀ hn
    rw [hr]
    linear_combination (π : ℂ) * hP

/-- A square root `w` of `z² - 1` with `|z + w| ≥ 1`; then `(z + w)(z - w) = 1`. -/
private lemma heine_root (z : ℂ) : ∃ w : ℂ, w ^ 2 = z ^ 2 - 1 ∧ 1 ≤ ‖z + w‖ := by
  set s : ℂ := (z ^ 2 - 1) ^ ((2 : ℕ)⁻¹ : ℂ) with hs
  have hs2 : s ^ 2 = z ^ 2 - 1 := cpow_nat_inv_pow _ two_ne_zero
  have hprod : (z + s) * (z - s) = 1 := by linear_combination -hs2
  by_cases h : 1 ≤ ‖z + s‖
  · exact ⟨s, hs2, h⟩
  · refine ⟨-s, by rw [neg_sq, hs2], ?_⟩
    push Not at h
    have hn := congrArg norm hprod
    rw [norm_mul, norm_one] at hn
    have h0 : 0 < ‖z + s‖ := by
      rcases (norm_nonneg (z + s)).lt_or_eq with h' | h'
      · exact h'
      · rw [← h', zero_mul] at hn; exact absurd hn zero_ne_one
    rw [← sub_eq_add_neg]
    nlinarith [norm_nonneg (z - s)]

/-- Bernstein-type bound: `|P_n(z)| ≤ |z + w|^n` when `w² = z² - 1` and `|z + w| ≥ 1`. -/
private lemma heine_norm_legendrePolyP_le {z w : ℂ} (hw : w ^ 2 = z ^ 2 - 1) (hm : 1 ≤ ‖z + w‖)
    (n : ℕ) : ‖DLMF.OrthogonalPolynomials.legendrePolyP n z‖ ≤ ‖z + w‖ ^ n := by
  have hL := heine_laplace hw n
  have hprod : (z + w) * (z - w) = 1 := by linear_combination -hw
  have hq : ‖z - w‖ = ‖z + w‖⁻¹ := by
    have hn := congrArg norm hprod
    rw [norm_mul, norm_one] at hn
    exact eq_inv_of_mul_eq_one_right hn
  have hpt : ∀ t : ℝ, ‖(z + w * Real.cos t) ^ n‖ ≤ ‖z + w‖ ^ n := by
    intro t
    rw [norm_pow]
    gcongr
    have he : z + w * Real.cos t = (z + w) * ((1 + Real.cos t) / 2 : ℝ) +
        (z - w) * ((1 - Real.cos t) / 2 : ℝ) := by push_cast; ring
    have h1 : 0 ≤ (1 + Real.cos t) / 2 := by linarith [Real.neg_one_le_cos t]
    have h2 : 0 ≤ (1 - Real.cos t) / 2 := by linarith [Real.cos_le_one t]
    rw [he]
    calc ‖(z + w) * (((1 + Real.cos t) / 2 : ℝ) : ℂ) + (z - w) * (((1 - Real.cos t) / 2 : ℝ) : ℂ)‖
        ≤ ‖z + w‖ * ((1 + Real.cos t) / 2) + ‖z - w‖ * ((1 - Real.cos t) / 2) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2]
      _ ≤ ‖z + w‖ * ((1 + Real.cos t) / 2) + ‖z + w‖ * ((1 - Real.cos t) / 2) := by
          rw [hq]; gcongr; exact (inv_le_one_of_one_le₀ hm).trans hm
      _ = ‖z + w‖ := by ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
    (f := fun t : ℝ => (z + w * Real.cos t) ^ n) (fun t _ => hpt t)
  rw [← hL, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    sub_zero, abs_of_pos Real.pi_pos] at hb
  nlinarith [Real.pi_pos, norm_nonneg (DLMF.OrthogonalPolynomials.legendrePolyP n z)]

/-- The confocal ellipse coordinate: `|z - 1| + |z + 1| = m + 1/m` with `m = |z + w|`. -/
private lemma heine_ellipse {z w : ℂ} (hw : w ^ 2 = z ^ 2 - 1) (hm : 1 ≤ ‖z + w‖) :
    legendreEllipseRadius z = ‖z + w‖ + ‖z + w‖⁻¹ := by
  set p := z + w with hp
  have hp0 : p ≠ 0 := by intro h; rw [h, norm_zero] at hm; linarith
  have hzw : z - w = p⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [hp]; linear_combination -hw)
  have hz : z = (p + p⁻¹) / 2 := by rw [← hzw, hp]; ring
  have h1 : z - 1 = (p - 1) ^ 2 / (2 * p) := by rw [hz]; field_simp; ring
  have h2 : z + 1 = (p + 1) ^ 2 / (2 * p) := by rw [hz]; field_simp; ring
  have hpar : ‖p - 1‖ ^ 2 + ‖p + 1‖ ^ 2 = 2 * ‖p‖ ^ 2 + 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, add_re, add_im, one_re,
      one_im]
    ring
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  rw [legendreEllipseRadius, h1, h2, norm_div, norm_div, norm_pow, norm_pow, norm_mul,
    Complex.norm_ofNat]
  field_simp
  linear_combination hpar

/-- `P_N` is orthogonal on `[-1, 1]` to every polynomial of degree less than `N`. -/
private lemma heine_orthogonal (N : ℕ) (f : Polynomial ℂ) (hf : f.natDegree < N) :
    ∫ t : ℝ in (-1 : ℝ)..1, DLMF.OrthogonalPolynomials.legendrePolyP N t * f.eval (t : ℂ) = 0 := by
  have hexp : ∀ t : ℝ, f.eval (t : ℂ) = ∑ i ∈ Finset.range (f.natDegree + 1),
      (Polynomial.taylor (-1) f).coeff i * ((t : ℂ) + 1) ^ i := by
    intro t
    have h := Polynomial.taylor_eval (-1 : ℂ) f ((t : ℂ) + 1)
    rw [show (t : ℂ) + 1 + -1 = t by ring] at h
    rw [← h, Polynomial.eval_eq_sum_range, Polynomial.natDegree_taylor]
  simp_rw [hexp, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < N := by have := Finset.mem_range.mp hi; omega
    have hJ := DLMF.OrthogonalPolynomials.jacobi_moment (α := 0) (β := 0) (by norm_num)
      (by norm_num) N i
    rw [poch_neg_nat_eq_zero hi'] at hJ
    simp only [ofReal_zero, cpow_zero, mul_one, mul_zero, zero_div] at hJ
    have : (∫ t : ℝ in (-1 : ℝ)..1, DLMF.OrthogonalPolynomials.legendrePolyP N t *
        ((Polynomial.taylor (-1) f).coeff i * ((t : ℂ) + 1) ^ i)) =
        (Polynomial.taylor (-1) f).coeff i * ∫ t : ℝ in (-1 : ℝ)..1, ((t : ℂ) + 1) ^ i *
          DLMF.OrthogonalPolynomials.jacobiPolyP 0 0 N t := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [DLMF.OrthogonalPolynomials.legendrePolyP]; ring
    rw [this, hJ, mul_zero]
  · intro i _
    refine Continuous.intervalIntegrable ?_ _ _
    have hc : Continuous fun t : ℝ => DLMF.OrthogonalPolynomials.legendrePolyP N t := by
      simp_rw [legendrePolyP_eq_eval]
      exact (Polynomial.continuous _).comp continuous_ofReal
    exact hc.mul (continuous_const.mul ((continuous_ofReal.add continuous_const).pow _))

/-- The Chebyshev approximant `(1/w)(1 + 2 ∑_{k<M} p^{-(k+1)} T_{k+1})` of `1/(z - t)`,
`p = z + w`. -/
private noncomputable def heine_q (z w : ℂ) (M : ℕ) : Polynomial ℂ :=
  Polynomial.C w⁻¹ * (1 + ∑ k ∈ Finset.range M,
    Polynomial.C (2 * ((z + w) ^ (k + 1))⁻¹) * Polynomial.Chebyshev.T ℂ ((k + 1 : ℕ) : ℤ))

/-- The Chebyshev approximant `heine_q z w M` has degree at most `M`. -/
private lemma heine_q_natDegree (z w : ℂ) (M : ℕ) : (heine_q z w M).natDegree ≤ M := by
  unfold heine_q
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.Chebyshev.natDegree_T]
  have := Finset.mem_range.mp hk; omega

/-- Error of the Chebyshev approximant on `[-1, 1]`. -/
private lemma heine_cheb {z w : ℂ} (hw : w ^ 2 = z ^ 2 - 1) (hm : 1 < ‖z + w‖) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (M : ℕ) :
    z - t ≠ 0 ∧ ‖1 / (z - t) - (heine_q z w M).eval (t : ℂ)‖ ≤
      2 / ‖w‖ * ‖z + w‖⁻¹ ^ (M + 1) / (1 - ‖z + w‖⁻¹) := by
  set p := z + w with hp
  set m := ‖p‖ with hmdef
  have hp0 : p ≠ 0 := by intro h; rw [hmdef, h, norm_zero] at hm; linarith
  have hzw : z - w = p⁻¹ := eq_inv_of_mul_eq_one_left (by rw [hp]; linear_combination -hw)
  have hz : z = (p + p⁻¹) / 2 := by rw [← hzw, hp]; ring
  have hwp : w = (p - p⁻¹) / 2 := by rw [← hzw, hp]; ring
  set θ := Real.arccos t with hθ
  have htc : (t : ℂ) = Complex.cos θ := by
    rw [← ofReal_cos, hθ, Real.cos_arccos ht.1 ht.2]
  set c := Complex.exp (θ * I) with hc
  have hc1 : ‖c‖ = 1 := by rw [hc, Complex.norm_exp_ofReal_mul_I]
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcos : ∀ j : ℕ, Complex.cos (j * θ) = (c ^ j + c⁻¹ ^ j) / 2 := by
    intro j
    rw [Complex.cos, hc, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_nat_mul]
    congr 2 <;> ring_nf
  have htc' : (t : ℂ) = (c + c⁻¹) / 2 := by
    have := hcos 1; simp only [Nat.cast_one, one_mul, pow_one] at this; rw [htc, this]
  set u := c / p with hu
  set v := c⁻¹ / p with hv
  have hmi : m⁻¹ < 1 := inv_lt_one_of_one_lt₀ hm
  have hm0 : 0 < m := by linarith
  have hun : ‖u‖ = m⁻¹ := by rw [hu, norm_div, hc1, one_div]
  have hvn : ‖v‖ = m⁻¹ := by rw [hv, norm_div, norm_inv, hc1, inv_one, one_div]
  have hu1 : 1 - u ≠ 0 := by
    intro h; have : ‖u‖ = 1 := by rw [← (sub_eq_zero.mp h), norm_one]
    linarith
  have hv1 : 1 - v ≠ 0 := by
    intro h; have : ‖v‖ = 1 := by rw [← (sub_eq_zero.mp h), norm_one]
    linarith
  have hpc : p - c ≠ 0 := by
    intro h; have : u = 1 := by rw [hu, sub_eq_zero.mp h, div_self hc0]
    exact hu1 (by rw [this, sub_self])
  have hpc' : p - c⁻¹ ≠ 0 := by
    intro h; have : v = 1 := by rw [hv, sub_eq_zero.mp h, div_self (inv_ne_zero hc0)]
    exact hv1 (by rw [this, sub_self])
  have hzt : z - t = (p - c) * (p - c⁻¹) / (2 * p) := by
    rw [hz, htc']; field_simp; ring
  have hzt0 : z - t ≠ 0 := by
    rw [hzt]; exact div_ne_zero (mul_ne_zero hpc hpc') (mul_ne_zero two_ne_zero hp0)
  have hw0 : w ≠ 0 := by
    intro h
    have : p ^ 2 = 1 := by rw [hwp] at h; field_simp at h; linear_combination h
    have : m ^ 2 = 1 := by rw [hmdef, ← norm_pow, this, norm_one]
    nlinarith
  refine ⟨hzt0, ?_⟩
  -- the geometric decomposition
  have hgu := geom_sum_eq (x := u) (by intro h; exact hu1 (by rw [h, sub_self])) (M + 1)
  have hgv := geom_sum_eq (x := v) (by intro h; exact hv1 (by rw [h, sub_self])) M
  have hevalq : (heine_q z w M).eval (t : ℂ) = w⁻¹ * (1 + ∑ k ∈ Finset.range M,
      (u ^ (k + 1) + v ^ (k + 1))) := by
    simp only [heine_q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_finsetSum]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [htc, Polynomial.Chebyshev.T_complex_cos, show (((k + 1 : ℕ) : ℤ) : ℂ) = ((k + 1 : ℕ) : ℂ)
      by push_cast; ring, hcos, hu, hv, div_pow, div_pow, ← hp]
    field_simp
  have hdec : 1 / (z - t) - (heine_q z w M).eval (t : ℂ) =
      w⁻¹ * (u ^ (M + 1) / (1 - u) + v ^ (M + 1) / (1 - v)) := by
    have hmain : 1 / (z - t) = w⁻¹ * (1 / (1 - u) + v / (1 - v)) := by
      rw [hzt, hwp, hu, hv]
      have hp2 : p ^ 2 - 1 ≠ 0 := by
        intro h; apply hw0; rw [hwp]; field_simp; linear_combination h
      have hcp : c * p - 1 ≠ 0 := by
        intro h; apply hpc'; field_simp; linear_combination h
      have hcp' : -1 + c * p ≠ 0 := by rw [add_comm, ← sub_eq_add_neg]; exact hcp
      field_simp
      ring_nf
      field_simp
      ring
    have hsum : 1 + ∑ k ∈ Finset.range M, (u ^ (k + 1) + v ^ (k + 1)) =
        ∑ i ∈ Finset.range (M + 1), u ^ i + v * ∑ i ∈ Finset.range M, v ^ i := by
      rw [Finset.sum_range_succ', Finset.sum_add_distrib, Finset.mul_sum]
      simp only [pow_zero, pow_succ]
      ring_nf
    have hu1' : u - 1 ≠ 0 := fun h => hu1 (by linear_combination -h)
    have hv1' : v - 1 ≠ 0 := fun h => hv1 (by linear_combination -h)
    rw [hevalq, hmain, hsum, hgu, hgv]
    field_simp
    ring
  rw [hdec, norm_mul, norm_inv]
  have hb : ‖u ^ (M + 1) / (1 - u) + v ^ (M + 1) / (1 - v)‖ ≤
      2 * m⁻¹ ^ (M + 1) / (1 - m⁻¹) := by
    have h1 : 1 - m⁻¹ ≤ ‖1 - u‖ := by
      have := norm_sub_norm_le (1 : ℂ) u; rw [norm_one, hun] at this; exact this
    have h2 : 1 - m⁻¹ ≤ ‖1 - v‖ := by
      have := norm_sub_norm_le (1 : ℂ) v; rw [norm_one, hvn] at this; exact this
    have hpos : 0 < 1 - m⁻¹ := by linarith
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_pow, norm_pow, hun, hvn]
    have e1 : m⁻¹ ^ (M + 1) / ‖1 - u‖ ≤ m⁻¹ ^ (M + 1) / (1 - m⁻¹) :=
      div_le_div_of_nonneg_left (by positivity) hpos h1
    have e2 : m⁻¹ ^ (M + 1) / ‖1 - v‖ ≤ m⁻¹ ^ (M + 1) / (1 - m⁻¹) :=
      div_le_div_of_nonneg_left (by positivity) hpos h2
    have : 2 * m⁻¹ ^ (M + 1) / (1 - m⁻¹) =
        m⁻¹ ^ (M + 1) / (1 - m⁻¹) + m⁻¹ ^ (M + 1) / (1 - m⁻¹) := by ring
    linarith
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  calc ‖w‖⁻¹ * ‖u ^ (M + 1) / (1 - u) + v ^ (M + 1) / (1 - v)‖
      ≤ ‖w‖⁻¹ * (2 * m⁻¹ ^ (M + 1) / (1 - m⁻¹)) := by gcongr
    _ = _ := by ring

/-- Decay of `Q_N` off the cut: `|Q_N(z)| ≤ 2 m^{-N} / (|w| (1 - 1/m))`, `m = |z + w| > 1`. -/
private lemma heine_norm_legendreQ_le {z w : ℂ} (hz : z - 1 ∈ slitPlane) (hw : w ^ 2 = z ^ 2 - 1)
    (hm : 1 < ‖z + w‖) (N : ℕ) :
    ‖legendreQ N z‖ ≤ 2 / (‖w‖ * (1 - ‖z + w‖⁻¹)) * ‖z + w‖⁻¹ ^ N := by
  set m := ‖z + w‖ with hmdef
  have hmi : m⁻¹ < 1 := inv_lt_one_of_one_lt₀ hm
  have hpos : 0 < 1 - m⁻¹ := by linarith
  have hw0 : w ≠ 0 := by
    intro h; rw [h, zero_pow two_ne_zero] at hw
    have hz2 : z ^ 2 = 1 := by linear_combination -hw
    have : ‖z + w‖ ^ 2 = 1 := by rw [h, add_zero, ← norm_pow, hz2, norm_one]
    nlinarith
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hPc : Continuous fun t : ℝ => DLMF.OrthogonalPolynomials.legendrePolyP N t := by
    simp_rw [legendrePolyP_eq_eval]
    exact (Polynomial.continuous _).comp continuous_ofReal
  have hcont : ContinuousOn (fun t : ℝ => 1 / (z - t)) (uIcc (-1 : ℝ) 1) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    exact (heine_cheb hw hm ht 0).1
  have hP1 : ∀ t ∈ uIoc (-1 : ℝ) 1, ‖DLMF.OrthogonalPolynomials.legendrePolyP N t‖ ≤ 1 := by
    intro t ht
    rw [uIoc_of_le (by norm_num)] at ht
    exact DLMF.OrthogonalPolynomials.norm_legendrePolyP_le_one N (abs_le.mpr ⟨ht.1.le, ht.2⟩)
  rw [legendreQ_nat_eq_integral N hz]
  have hIcc : ∀ t ∈ uIoc (-1 : ℝ) 1, t ∈ Icc (-1 : ℝ) 1 := by
    intro t ht; rw [uIoc_of_le (by norm_num)] at ht; exact ⟨ht.1.le, ht.2⟩
  rcases N with _ | M
  · -- `N = 0`: bound `1/(z - t)` directly
    have hb : ∀ t ∈ uIoc (-1 : ℝ) 1, ‖DLMF.OrthogonalPolynomials.legendrePolyP 0 t / (z - t)‖ ≤
        2 / (‖w‖ * (1 - m⁻¹)) := by
      intro t ht
      obtain ⟨_, he⟩ := heine_cheb hw hm (hIcc t ht) 0
      have hq0 : (heine_q z w 0).eval (t : ℂ) = w⁻¹ := by simp [heine_q]
      rw [hq0] at he
      rw [DLMF.OrthogonalPolynomials.legendrePolyP_zero]
      calc ‖1 / (z - t)‖ ≤ ‖w⁻¹‖ + ‖1 / (z - t) - w⁻¹‖ := by
            have := norm_add_le w⁻¹ (1 / (z - t) - w⁻¹); simpa using this
        _ ≤ ‖w‖⁻¹ + 2 / ‖w‖ * m⁻¹ ^ (0 + 1) / (1 - m⁻¹) := by rw [norm_inv]; linarith
        _ ≤ 2 / (‖w‖ * (1 - m⁻¹)) := by
            rw [zero_add, pow_one,
              show ‖w‖⁻¹ + 2 / ‖w‖ * m⁻¹ / (1 - m⁻¹) = ‖w‖⁻¹ * (1 + m⁻¹) / (1 - m⁻¹) by
                field_simp; ring,
              show 2 / (‖w‖ * (1 - m⁻¹)) = ‖w‖⁻¹ * 2 / (1 - m⁻¹) by field_simp]
            gcongr
            linarith
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    simp only [pow_zero, mul_one]
    norm_num at hI ⊢
    linarith
  · -- `N = M + 1`: subtract the orthogonal approximant
    have hq := heine_orthogonal (M + 1) (heine_q z w M) (by
      have := heine_q_natDegree z w M; omega)
    have hqc : Continuous fun t : ℝ => (heine_q z w M).eval (t : ℂ) :=
      (Polynomial.continuous _).comp continuous_ofReal
    have hsplit : (∫ t : ℝ in (-1 : ℝ)..1, DLMF.OrthogonalPolynomials.legendrePolyP (M + 1) t /
        (z - t)) = ∫ t : ℝ in (-1 : ℝ)..1, DLMF.OrthogonalPolynomials.legendrePolyP (M + 1) t *
          (1 / (z - t) - (heine_q z w M).eval (t : ℂ)) := by
      have h1 : IntervalIntegrable (fun t : ℝ => DLMF.OrthogonalPolynomials.legendrePolyP
          (M + 1) t * (1 / (z - t))) volume (-1) 1 :=
        ((hPc.continuousOn).mul hcont).intervalIntegrable
      have h2 : IntervalIntegrable (fun t : ℝ => DLMF.OrthogonalPolynomials.legendrePolyP
          (M + 1) t * (heine_q z w M).eval (t : ℂ)) volume (-1) 1 :=
        (hPc.mul hqc).intervalIntegrable _ _
      simp_rw [mul_sub]
      rw [intervalIntegral.integral_sub h1 h2]
      rw [hq, sub_zero]
      simp_rw [mul_one_div]
    rw [hsplit]
    have hb : ∀ t ∈ uIoc (-1 : ℝ) 1, ‖DLMF.OrthogonalPolynomials.legendrePolyP (M + 1) t *
        (1 / (z - t) - (heine_q z w M).eval (t : ℂ))‖ ≤ 2 / ‖w‖ * m⁻¹ ^ (M + 1) / (1 - m⁻¹) := by
      intro t ht
      rw [norm_mul]
      have := (heine_cheb hw hm (hIcc t ht) M).2
      calc _ ≤ 1 * (2 / ‖w‖ * m⁻¹ ^ (M + 1) / (1 - m⁻¹)) := by
            gcongr
            · exact hP1 t ht
        _ = _ := one_mul _
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    rw [show |(1 : ℝ) - (-1)| = 2 by norm_num] at hI
    have : 2 / (‖w‖ * (1 - m⁻¹)) * m⁻¹ ^ (M + 1) = 2 / ‖w‖ * m⁻¹ ^ (M + 1) / (1 - m⁻¹) := by
      field_simp
    rw [this]
    linarith

/-- Christoffel–Darboux with the polynomial `P_k(z₂)` (no condition on `z₂`). -/
private lemma heine_christoffel (n : ℕ) {z₁ z₂ : ℂ} (hz₁ : z₁ - 1 ∈ slitPlane) :
    (z₂ - z₁) * (∑ k ∈ Finset.range (n + 1), (2 * k + 1 : ℂ) *
      DLMF.OrthogonalPolynomials.legendrePolyP k z₂ * legendreQ k z₁) =
      (n + 1 : ℂ) * (DLMF.OrthogonalPolynomials.legendrePolyP (n + 1) z₂ * legendreQ n z₁ -
        DLMF.OrthogonalPolynomials.legendrePolyP n z₂ * legendreQ (n + 1) z₁) - 1 := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero,
      one_mul, DLMF.OrthogonalPolynomials.legendrePolyP_zero,
      DLMF.OrthogonalPolynomials.legendrePolyP_one]
    have h1 := legendreQ_one hz₁
    rw [h1]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hp := DLMF.OrthogonalPolynomials.legendrePolyP_recurrence n z₂
    have hq := legendreQ_recurrence (ν := (n : ℂ) + 1) (by exact_mod_cast Nat.succ_ne_zero n) hz₁
    rw [show (n : ℂ) + 1 - 1 = n by ring] at hq
    push_cast
    rw [show n + 1 + 1 = n + 2 by ring]
    rw [show (n : ℂ) + 1 + 1 = n + 2 by ring] at hq ⊢
    linear_combination -legendreQ ((n : ℂ) + 1) z₁ * hp +
      DLMF.OrthogonalPolynomials.legendrePolyP (n + 1) z₂ * hq

/-- `x + 1/x` is strictly increasing on `[1, ∞)`. -/
private lemma heine_add_recip_lt {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) : a + a⁻¹ < b + b⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab1 : 1 < a * b := by nlinarith
  have : b + b⁻¹ - (a + a⁻¹) = (b - a) * (1 - (a * b)⁻¹) := by field_simp; ring
  have h2 : 0 < 1 - (a * b)⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hab1; linarith
  nlinarith [mul_pos (sub_pos.mpr hab) h2]

/-- With `w² = z² - 1`, `w = (ζ - ζ⁻¹)/2` where `ζ = z + w`, hence `|w| ≥ (|ζ| - |ζ|⁻¹)/2`. -/
private lemma heine_norm_w_ge {z w : ℂ} (hw : w ^ 2 = z ^ 2 - 1) (hm : 1 ≤ ‖z + w‖) :
    (‖z + w‖ - ‖z + w‖⁻¹) / 2 ≤ ‖w‖ := by
  have h1 : (z + w) * (z - w) = 1 := by linear_combination -hw
  have hne : z + w ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; linarith
  have hzw : z - w = (z + w)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have : w = ((z + w) - (z + w)⁻¹) / 2 := by rw [← hzw]; ring
  have hw' : ‖w‖ = ‖((z + w) - (z + w)⁻¹) / 2‖ := congrArg _ this
  rw [hw', norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have := norm_sub_norm_le (z + w) (z + w)⁻¹
  rw [norm_inv] at this
  linarith

/-- Explicit bound for the Heine partial sums. -/
private lemma heine_tail {z₁ z₂ w₁ w₂ : ℂ} (hz₁ : z₁ - 1 ∈ slitPlane) (hw₁ : w₁ ^ 2 = z₁ ^ 2 - 1)
    (hw₂ : w₂ ^ 2 = z₂ ^ 2 - 1) (hm₁ : 1 < ‖z₁ + w₁‖) (hm₂ : 1 ≤ ‖z₂ + w₂‖) (hne : z₁ ≠ z₂)
    (n : ℕ) :
    ‖(∑ k ∈ Finset.range (n + 1), (2 * k + 1 : ℂ) * associatedQ k 0 z₁ *
        DLMF.OrthogonalPolynomials.legendrePolyP k z₂) - 1 / (z₁ - z₂)‖ ≤
      (n + 1) * (2 / (‖w₁‖ * (1 - ‖z₁ + w₁‖⁻¹))) * (‖z₂ + w₂‖ / ‖z₁ + w₁‖) ^ n *
        (‖z₂ + w₂‖ + 1) / ‖z₁ - z₂‖ := by
  set m₁ := ‖z₁ + w₁‖
  set m₂ := ‖z₂ + w₂‖
  set K := 2 / (‖w₁‖ * (1 - m₁⁻¹)) with hK
  have hm₁0 : 0 < m₁ := by linarith
  have hK0 : 0 ≤ K := by
    have hmi : m₁⁻¹ < 1 := inv_lt_one_of_one_lt₀ hm₁
    have : 0 < 1 - m₁⁻¹ := by linarith
    positivity
  have hsum : (∑ k ∈ Finset.range (n + 1), (2 * k + 1 : ℂ) * associatedQ k 0 z₁ *
      DLMF.OrthogonalPolynomials.legendrePolyP k z₂) = ∑ k ∈ Finset.range (n + 1),
        (2 * k + 1 : ℂ) * DLMF.OrthogonalPolynomials.legendrePolyP k z₂ * legendreQ k z₁ := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [associatedQ_zero_order _ hz₁]; ring
  rw [hsum]
  have hC := heine_christoffel n (z₂ := z₂) hz₁
  set D := DLMF.OrthogonalPolynomials.legendrePolyP (n + 1) z₂ * legendreQ n z₁ -
    DLMF.OrthogonalPolynomials.legendrePolyP n z₂ * legendreQ (n + 1) z₁ with hD
  have hne' : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hexpr : (∑ k ∈ Finset.range (n + 1), (2 * k + 1 : ℂ) *
      DLMF.OrthogonalPolynomials.legendrePolyP k z₂ * legendreQ k z₁) - 1 / (z₁ - z₂) =
        (n + 1 : ℂ) * D / (z₂ - z₁) := by
    have hne'' : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
    rw [eq_div_iff hne', sub_mul, mul_comm _ (z₂ - z₁), hC,
      show 1 / (z₁ - z₂) * (z₂ - z₁) = -1 by field_simp; ring]
    ring
  rw [hexpr, norm_div, norm_mul, norm_sub_rev z₂ z₁,
    show ‖(n + 1 : ℂ)‖ = n + 1 by exact_mod_cast Complex.norm_natCast (n + 1)]
  have hP1 := heine_norm_legendrePolyP_le hw₂ hm₂ (n + 1)
  have hP0 := heine_norm_legendrePolyP_le hw₂ hm₂ n
  have hQ0 := heine_norm_legendreQ_le hz₁ hw₁ hm₁ n
  have hQ1 := heine_norm_legendreQ_le hz₁ hw₁ hm₁ (n + 1)
  push_cast at hQ0 hQ1
  have hDb : ‖D‖ ≤ K * (m₂ / m₁) ^ n * (m₂ + 1) := by
    have hm1i : m₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm₁.le
    calc ‖D‖ ≤ m₂ ^ (n + 1) * (K * m₁⁻¹ ^ n) + m₂ ^ n * (K * m₁⁻¹ ^ (n + 1)) := by
          rw [hD]
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          gcongr
      _ = K * (m₂ / m₁) ^ n * (m₂ + m₁⁻¹) := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
      _ ≤ K * (m₂ / m₁) ^ n * (m₂ + 1) := by gcongr
  have hzpos : 0 ≤ ‖z₁ - z₂‖ := norm_nonneg _
  calc (n + 1 : ℝ) * ‖D‖ / ‖z₁ - z₂‖ ≤ (n + 1) * (K * (m₂ / m₁) ^ n * (m₂ + 1)) / ‖z₁ - z₂‖ := by
        gcongr
    _ = _ := by ring

/-- `(n + 1) C ρ^n → 0` for `0 ≤ ρ < 1`. -/
private lemma heine_bound_tendsto (C : ℝ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Tendsto (fun n : ℕ => (n + 1) * C * ρ ^ n) atTop (𝓝 0) := by
  have h := (tendsto_self_mul_const_pow_of_lt_one h0 h1).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1)
  rw [add_zero] at h
  have := h.const_mul C
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  ring

/-- The ellipse parameter `μ = (R + √(R² - 4))/2` satisfies `μ > 1` and `μ + μ⁻¹ = R`. -/
private lemma heine_mu {R : ℝ} (hR : 2 < R) :
    1 < (R + √(R ^ 2 - 4)) / 2 ∧ (R + √(R ^ 2 - 4)) / 2 + ((R + √(R ^ 2 - 4)) / 2)⁻¹ = R := by
  have hs0 : 0 ≤ R ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hs0
  have hsn := Real.sqrt_nonneg (R ^ 2 - 4)
  have hpos : 0 < (R + √(R ^ 2 - 4)) / 2 := by positivity
  refine ⟨by linarith, ?_⟩
  have hinv : ((R + √(R ^ 2 - 4)) / 2)⁻¹ = (R - √(R ^ 2 - 4)) / 2 := by
    have hprod : (R + √(R ^ 2 - 4)) / 2 * ((R - √(R ^ 2 - 4)) / 2) = 1 := by
      linear_combination (-1 / 4 : ℝ) * hs
    exact (eq_inv_of_mul_eq_one_right hprod).symm
  rw [hinv]; ring

/-- Comparison of `m` with `μ` via the monotonicity of `x + 1/x`. -/
private lemma heine_le_of_add_recip_le {a b : ℝ} (hb : 1 ≤ b) (h : a + a⁻¹ ≤ b + b⁻¹) :
    a ≤ b := by
  by_contra hc
  have := heine_add_recip_lt hb (not_le.mp hc)
  linarith

/-- The ellipse radius is `2`-Lipschitz. -/
private lemma heine_ellipse_lip (z₁ z₂ : ℂ) :
    legendreEllipseRadius z₁ - legendreEllipseRadius z₂ ≤ 2 * ‖z₁ - z₂‖ := by
  unfold legendreEllipseRadius
  have h1 : ‖z₁ - 1‖ ≤ ‖z₁ - z₂‖ + ‖z₂ - 1‖ := by
    have := norm_add_le (z₁ - z₂) (z₂ - 1); rwa [sub_add_sub_cancel] at this
  have h2 : ‖z₁ + 1‖ ≤ ‖z₁ - z₂‖ + ‖z₂ + 1‖ := by
    have := norm_add_le (z₁ - z₂) (z₂ + 1)
    rwa [show z₁ - z₂ + (z₂ + 1) = z₁ + 1 by ring] at this
  linarith

/-- DLMF 14.28.2 (Heine's formula): for `z₁ ∉ (-∞, 1]` and `z₂` inside the confocal ellipse (foci
`±1`) through `z₁`, `Σ_{n≥0} (2n+1) Q_n(z₁) P_n(z₂) = 1/(z₁ - z₂)`. -/
@[dlmf 14.28.E2]
theorem legendre_heine_series {z₁ z₂ : ℂ} (hz₁ : z₁-1 ∈ slitPlane) (hr : legendreEllipseRadius z₂ < legendreEllipseRadius z₁) :
    HasSum (fun n : ℕ => (2*n+1:ℂ)*associatedQ n 0 z₁*DLMF.OrthogonalPolynomials.legendrePolyP n z₂) (1/(z₁-z₂)) := by
  obtain ⟨w₁, hw₁, hm₁'⟩ := heine_root z₁
  obtain ⟨w₂, hw₂, hm₂⟩ := heine_root z₂
  have hE₁ := heine_ellipse hw₁ hm₁'
  have hE₂ := heine_ellipse hw₂ hm₂
  set m₁ := ‖z₁ + w₁‖
  set m₂ := ‖z₂ + w₂‖
  have hlt : m₂ < m₁ := by
    by_contra hc
    rcases (not_lt.mp hc).lt_or_eq with h | h
    · have := heine_add_recip_lt hm₁' h; linarith
    · rw [h] at hE₁; linarith
  have hm₁ : 1 < m₁ := lt_of_le_of_lt hm₂ hlt
  have hne : z₁ ≠ z₂ := by rintro rfl; exact lt_irrefl _ hr
  have hm₁0 : 0 < m₁ := by linarith
  set ρ := m₂ / m₁ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hm₁0).mpr hlt
  set K := 2 / (‖w₁‖ * (1 - m₁⁻¹)) with hK
  have hS : Summable (fun n : ℕ => (2*n+1:ℂ)*associatedQ n 0 z₁*
      DLMF.OrthogonalPolynomials.legendrePolyP n z₂) := by
    have hg : Summable (fun n : ℕ => 2 * K * ((n : ℝ) ^ 1 * ρ ^ n) + K * ρ ^ n) :=
      ((summable_pow_mul_geometric_of_norm_lt_one 1
        (by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0])).mul_left (2 * K)).add
        ((summable_geometric_of_lt_one hρ0 hρ1).mul_left K)
    refine Summable.of_norm_bounded hg fun n => ?_
    rw [associatedQ_zero_order _ hz₁, norm_mul, norm_mul]
    have hQ := heine_norm_legendreQ_le hz₁ hw₁ hm₁ n
    have hP := heine_norm_legendrePolyP_le hw₂ hm₂ n
    have h2n : ‖(2 * n + 1 : ℂ)‖ = 2 * n + 1 := by
      rw [show (2 * n + 1 : ℂ) = ((2 * n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [h2n]
    calc (2 * n + 1 : ℝ) * ‖legendreQ n z₁‖ * ‖DLMF.OrthogonalPolynomials.legendrePolyP n z₂‖
        ≤ (2 * n + 1) * (K * m₁⁻¹ ^ n) * m₂ ^ n := by
          have hK0 : 0 ≤ K := by
            have : 0 < 1 - m₁⁻¹ := by have := inv_lt_one_of_one_lt₀ hm₁; linarith
            positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by positivity)) hP (norm_nonneg _)
            (mul_nonneg (by positivity) (mul_nonneg hK0 (by positivity)))
      _ = _ := by rw [hρ, div_pow, div_eq_mul_inv, inv_pow]; ring
  rw [hS.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1,
    tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => heine_tail hz₁ hw₁ hw₂ hm₁ hm₂ hne n) ?_
  refine (heine_bound_tendsto (K * (m₂ + 1) / ‖z₁ - z₂‖) hρ0 hρ1).congr fun n => ?_
  ring

/-- DLMF 14.28.2 (uniform convergence): for `2 < R₂ < R₁`, the partial sums of `Σ_n (2n+1) Q_n(z₁)
P_n(z₂)` converge to `1/(z₁ - z₂)` uniformly for `z₁ ∉ (-∞, 1]` with `|z₁-1| + |z₁+1| ≥ R₁` and
`|z₂-1| + |z₂+1| ≤ R₂`. -/
@[dlmf 14.28.E2]
theorem legendre_heine_uniform {R₁ R₂ : ℝ} (hR₂ : 2 < R₂) (hR : R₂ < R₁) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℂ × ℂ => ∑ n ∈ Finset.range N, (2*n+1:ℂ)*associatedQ n 0 p.1*DLMF.OrthogonalPolynomials.legendrePolyP n p.2) (fun p => 1/(p.1-p.2)) atTop {p : ℂ × ℂ | p.1-1 ∈ slitPlane ∧ R₁ ≤ legendreEllipseRadius p.1 ∧ legendreEllipseRadius p.2 ≤ R₂} := by
  obtain ⟨hμ₁, hμ₁E⟩ := heine_mu (hR₂.trans hR)
  obtain ⟨hμ₂, hμ₂E⟩ := heine_mu hR₂
  set μ₁ := (R₁ + √(R₁ ^ 2 - 4)) / 2
  set μ₂ := (R₂ + √(R₂ ^ 2 - 4)) / 2
  have hμ : μ₂ < μ₁ := by
    by_contra hc
    rcases (not_lt.mp hc).lt_or_eq with h | h
    · have := heine_add_recip_lt hμ₁.le h; linarith
    · rw [h] at hμ₁E; linarith
  have hμ₁0 : 0 < μ₁ := by linarith
  have hμ₁i : μ₁⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ₁
  have hc₁ : 0 < (μ₁ - μ₁⁻¹) / 2 := by linarith
  have hc₂ : 0 < 1 - μ₁⁻¹ := by linarith
  set ρ := μ₂ / μ₁ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hμ₁0).mpr hμ
  have hd : 0 < (R₁ - R₂) / 2 := by linarith
  set C := 2 / ((μ₁ - μ₁⁻¹) / 2 * (1 - μ₁⁻¹)) * (μ₂ + 1) / ((R₁ - R₂) / 2) with hC
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((heine_bound_tendsto C hρ0 hρ1).eventually (gt_mem_nhds hε))
  refine eventually_atTop.mpr ⟨n₀ + 1, fun N hN p hp => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨hz₁, hE₁, hE₂⟩ := hp
  obtain ⟨w₁, hw₁, hm₁'⟩ := heine_root p.1
  obtain ⟨w₂, hw₂, hm₂⟩ := heine_root p.2
  rw [heine_ellipse hw₁ hm₁'] at hE₁
  rw [heine_ellipse hw₂ hm₂] at hE₂
  set m₁ := ‖p.1 + w₁‖
  set m₂ := ‖p.2 + w₂‖
  have hm₁μ : μ₁ ≤ m₁ := heine_le_of_add_recip_le hm₁' (by linarith)
  have hm₂μ : m₂ ≤ μ₂ := heine_le_of_add_recip_le hμ₂.le (by linarith)
  have hm₁ : 1 < m₁ := lt_of_lt_of_le hμ₁ hm₁μ
  have hm₁0 : 0 < m₁ := by linarith
  have hdist : (R₁ - R₂) / 2 ≤ ‖p.1 - p.2‖ := by
    have := heine_ellipse_lip p.1 p.2
    rw [heine_ellipse hw₁ hm₁', heine_ellipse hw₂ hm₂] at this
    linarith
  have hne : p.1 ≠ p.2 := by
    intro h; rw [h, sub_self, norm_zero] at hdist; linarith
  have hT := heine_tail hz₁ hw₁ hw₂ hm₁ hm₂ hne n
  rw [dist_comm, dist_eq_norm]
  refine lt_of_le_of_lt hT (lt_of_le_of_lt ?_ (hn₀ n (by omega)))
  -- compare constants
  have hm₁i : m₁⁻¹ ≤ μ₁⁻¹ := inv_anti₀ hμ₁0 hm₁μ
  have hw : (μ₁ - μ₁⁻¹) / 2 ≤ ‖w₁‖ := by
    have := heine_norm_w_ge hw₁ hm₁'; linarith
  have hK : 2 / (‖w₁‖ * (1 - m₁⁻¹)) ≤ 2 / ((μ₁ - μ₁⁻¹) / 2 * (1 - μ₁⁻¹)) := by
    gcongr
  have hr : m₂ / m₁ ≤ ρ := by
    rw [hρ]; gcongr
  have hr0 : 0 ≤ m₂ / m₁ := by positivity
  rw [hC]
  have hK0 : 0 ≤ 2 / (‖w₁‖ * (1 - m₁⁻¹)) := by
    have : 0 < 1 - m₁⁻¹ := by have := inv_lt_one_of_one_lt₀ hm₁; linarith
    positivity
  calc ((n : ℝ) + 1) * (2 / (‖w₁‖ * (1 - m₁⁻¹))) * (m₂ / m₁) ^ n * (m₂ + 1) / ‖p.1 - p.2‖
      ≤ ((n : ℝ) + 1) * (2 / ((μ₁ - μ₁⁻¹) / 2 * (1 - μ₁⁻¹))) * ρ ^ n * (μ₂ + 1) /
          ((R₁ - R₂) / 2) := by
        gcongr
    _ = _ := by ring

/-- DLMF 14.28.1: for `Re z₁, Re z₂ > 0` off the cut, real `φ`, and `Z = z₁z₂ -
(z₁²-1)^{1/2}(z₂²-1)^{1/2} cos φ` off the cut, `P_ν(Z) = P_ν(z₁) P_ν(z₂) + 2 Σ_{m≥1} (-1)^m
P^m_ν(z₁) P^m_ν(z₂) cos(mφ)/(ν-m+1)_{2m}`, as a convergent series. -/
@[dlmf 14.28.E1]
theorem associatedP_complex_addition (ν : ℂ) {z₁ z₂ : ℂ} (h1 : 0 < z₁.re) (h2 : 0 < z₂.re) (hz1 : z₁-1 ∈ slitPlane) (hz2 : z₂-1 ∈ slitPlane) (phi : ℝ) (harg : z₁*z₂-exp ((log (z₁-1)+log (z₁+1))/2)*exp ((log (z₂-1)+log (z₂+1))/2)*Real.cos phi-1 ∈ slitPlane) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*1/poch (ν-m+1) (2*m)*associatedP ν m z₁*associatedP ν m z₂*Real.cos (m*phi)) (associatedP ν 0 (z₁*z₂-exp ((log (z₁-1)+log (z₁+1))/2)*exp ((log (z₂-1)+log (z₂+1))/2)*Real.cos phi)-associatedP ν 0 z₁*associatedP ν 0 z₂) := by
  -- The combined argument avoids `(-∞, -1]` for every angle, so 14.18.4 continues analytically in
  -- `z₁` and `z₂`; the hypothesis `harg` is not needed.
  exact legQAdd_associatedP_complex_addition ν h1 h2 hz1 hz2 phi

end DLMF.Legendre
