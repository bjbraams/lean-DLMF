/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersDefs

/-!
# Radial spheroidal wave functions (DLMF §30.11)

Statement acquisition from NIST DLMF (version 1.2.8), checked 2026-10-26. Admitted statements
are not completed proofs; see `DLMF30Acquisition.md`.

* §30.11(i): `ψ^{(1)}_k = j_k` off the cut, convergence of the series 30.11.3, the radial
  functions as solutions of 30.2.1, and the connection formulas 30.11.5 (proved from the
  convergence and from `ψ^{(3), (4)} = ψ^{(1)} ± iψ^{(2)}`);
* §30.11(iii): the asymptotic behaviour 30.11.6 (corrected, see below);
* §30.11(iv): the Wronskian 30.11.7;
* §30.11(v): the connection with `𝑃s`, `𝑄s` (30.11.8–30.11.11);
* §30.11(vi): the integral representation 30.11.12.

The radial functions take complex `z`, `γ` with `γ²` real; statements assume `(γ^2).im = 0`.

**Correction to 30.11.6.** For `j = 1, 2` DLMF prints the error term `O(z⁻² e^{|ℑz|})`. The
correct term is `O(z⁻² e^{|ℑ(γz)|})` (the two agree for `γ = 1`; DLMF's form is too strong for
`γ > 1`): numerically, for `n = m = 0`, `γ = 2`, `z = iy`, the quantity
`|S^{0(1)}_0(iy, 2) - ψ^{(1)}_0(2iy)| y² e^{-y}` is `3.9·10³, 8.7·10⁷, 4.2·10¹⁶` at
`y = 10, 20, 40`, while `|S - ψ| y² e^{-2y} → 0.179`. The corrected form is acquired, for real
`γ > 0` (the sector condition `|ph z| ≤ π - δ` refers to real `γ`).

Numerical checks (high precision): 30.11.3 against SciPy's `pro_rad1`, `pro_rad2`; 30.11.7;
30.11.8 with `K^m_n` from 30.11.10–30.11.11 and `𝑃s` from 30.6.1; 30.11.12; 30.11.6 for `j = 3`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Spheroidal

/-! ### §30.11(i) Definitions -/

/-- **`ψ^{(1)}_k` by the principal-branch formula** (DLMF 30.11.1, 10.47.3): for `z` off
`(-∞, 0]`, `j_k(z) = (π/(2z))^{1/2} J_{k+1/2}(z)`. -/
@[dlmf 30.11.E1]
theorem spheroidalPsi_one_eq (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    spheroidalPsi 1 k z = ((π : ℂ) / (2 * z)) ^ (1 / 2 : ℂ) * besselJ ((k : ℂ) + 1 / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set w : ℂ := z / 2
  have hw : w ∈ slitPlane := by
    have : w = ((1 / 2 : ℝ) : ℂ) * z := by simp [w]; ring
    rw [this, mem_slitPlane_iff] at *
    rcases hz with h | h
    · left; simp; linarith
    · right; simpa using h
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hwarg : w.arg ≠ π := by
    intro h; exact (mem_slitPlane_iff_arg.mp hw).1 h
  have hr : (0 : ℝ) < π / 4 := by positivity
  have e1 : (π : ℂ) / (2 * z) = ((π / 4 : ℝ) : ℂ) * w⁻¹ := by
    simp only [w]; push_cast; field_simp; ring
  have hwi : w⁻¹ ≠ 0 := inv_ne_zero hw0
  have hp : ((π : ℂ) / (2 * z)) ^ (1 / 2 : ℂ) * w ^ ((1 / 2 : ℂ)) = (Real.sqrt π / 2 : ℝ) := by
    rw [e1, Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hr.ne') hwi),
      Complex.cpow_def_of_ne_zero hw0, ← Complex.exp_add,
      Complex.log_ofReal_mul hr hwi, Complex.log_inv w hwarg]
    rw [show ((Real.log (π / 4) : ℂ) + -Complex.log w) * (1 / 2) + Complex.log w * (1 / 2) =
      ((Real.log (π / 4) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
    congr 1
    rw [Real.sqrt_eq_rpow, show π / 4 = (π ^ (1 / 2 : ℝ) / 2) ^ (2 : ℝ) by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul (by positivity)]
      norm_num]
    rw [Real.log_rpow (by positivity), mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.exp_log (by positivity)]
  simp only [spheroidalPsi, ↓reduceIte, DLMF.sphericalJ]
  rw [DLMF.Bessel.besselJ_eq_regularized,
    Complex.cpow_add _ _ (by simpa [w] using hw0), Complex.cpow_natCast]
  rw [show (k : ℂ) + 1 / 2 + 1 = (k : ℂ) + 3 / 2 by ring]
  have : z / 2 = w := rfl
  rw [this]
  calc _ = (((π : ℂ) / (2 * z)) ^ (1 / 2 : ℂ) * w ^ ((1 / 2 : ℂ))) * w ^ k *
        regularizedHGFun ∅ {(k : ℂ) + 3 / 2} (-(z ^ 2 / 4)) := by
          rw [hp]; simp only [w]; push_cast; rw [div_pow]; field_simp; ring_nf
    _ = _ := by ring

/-- `ψ^{(3)}_k = ψ^{(1)}_k + iψ^{(2)}_k` and `ψ^{(4)}_k = ψ^{(1)}_k - iψ^{(2)}_k` off `(-∞, 0]`
(DLMF 30.11.1–30.11.2 with `H^{(1),(2)}_ν = J_ν ± iY_ν`). Proved from `spheroidalPsi_one_eq`. -/
@[dlmf 30.11.E2]
theorem spheroidalPsi_three_four (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    spheroidalPsi 3 k z = spheroidalPsi 1 k z + I * spheroidalPsi 2 k z ∧
      spheroidalPsi 4 k z = spheroidalPsi 1 k z - I * spheroidalPsi 2 k z := by
  rw [spheroidalPsi_one_eq k hz]
  simp only [spheroidalPsi, spheroidalCylinder]
  norm_num
  constructor <;> ring

/-- **Convergence of the series 30.11.3**: for `γ ≠ 0` with `γ²` real, the series
`∑_{2k ≥ m-n} a^{-m}_{n,k}(γ²) ψ^{(j)}_{n+2k}(γz)` converges for `z ≠ 0` (`j = 1`) and for
`|z| > 1` (`j = 2, 3, 4`). -/
@[dlmf 30.11.E3]
theorem summable_spheroidalRadial_series {j n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hj : j ∈ ({1, 2, 3, 4} : Finset ℕ))
    (hz : if j = 1 then z ≠ 0 else 1 < ‖z‖) :
    Summable (fun k : ℤ => (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
      spheroidalPsi j ((n : ℤ) + 2 * k).toNat (γ * z)) := by
  sorry

/-- **The radial functions solve 30.2.1** (DLMF 30.11.3) with `μ = m`, `λ = λ^m_n(γ²)`, on the
open set where the principal powers in 30.11.1, 30.11.3 are analytic: `1 - z⁻²` off `(-∞, 0]`,
and, for `j = 2, 3, 4`, `|z| > 1` and `γz` off `(-∞, 0]`. -/
@[dlmf 30.11.E3]
theorem isSpheroidalSolutionOn_spheroidalRadial {j n m : ℕ} (hmn : m ≤ n) {γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hj : j ∈ ({1, 2, 3, 4} : Finset ℕ)) :
    IsSpheroidalSolutionOn (spheroidalEigenvalue n m (γ ^ 2).re) (γ ^ 2).re m
      {z : ℂ | z ≠ 0 ∧ 1 - z ^ (-2 : ℤ) ∈ slitPlane ∧
        (j = 1 ∨ (1 < ‖z‖ ∧ γ * z ∈ slitPlane))}
      (fun z => spheroidalRadial j n m z γ) := by
  sorry

/-- **Connection formulas** (DLMF 30.11.5): `S^{m(3)}_n = S^{m(1)}_n + iS^{m(2)}_n` and
`S^{m(4)}_n = S^{m(1)}_n - iS^{m(2)}_n` for `|z| > 1`, `γz` off `(-∞, 0]`. Proved from the
convergence of 30.11.3 and `spheroidalPsi_three_four`. -/
@[dlmf 30.11.E5]
theorem spheroidalRadial_three_four {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hz : 1 < ‖z‖) (hγz : γ * z ∈ slitPlane) :
    spheroidalRadial 3 n m z γ = spheroidalRadial 1 n m z γ + I * spheroidalRadial 2 n m z γ ∧
      spheroidalRadial 4 n m z γ = spheroidalRadial 1 n m z γ - I * spheroidalRadial 2 n m z γ := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have h1 := summable_spheroidalRadial_series (j := 1) hmn hγ hγ2 (by simp) (by simpa using hz0)
  have h2 := summable_spheroidalRadial_series (j := 2) hmn hγ hγ2 (by simp) (by simpa using hz)
  have h2' := h2.mul_left I
  have key : ∀ k : ℤ, (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
      spheroidalPsi 3 ((n : ℤ) + 2 * k).toNat (γ * z) =
        (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
          spheroidalPsi 1 ((n : ℤ) + 2 * k).toNat (γ * z) +
        I * ((spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
          spheroidalPsi 2 ((n : ℤ) + 2 * k).toNat (γ * z)) := by
    intro k; rw [(spheroidalPsi_three_four _ hγz).1]; ring
  have key' : ∀ k : ℤ, (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
      spheroidalPsi 4 ((n : ℤ) + 2 * k).toNat (γ * z) =
        (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
          spheroidalPsi 1 ((n : ℤ) + 2 * k).toNat (γ * z) -
        I * ((spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
          spheroidalPsi 2 ((n : ℤ) + 2 * k).toNat (γ * z)) := by
    intro k; rw [(spheroidalPsi_three_four _ hγz).2]; ring
  constructor
  · simp only [spheroidalRadial]
    rw [tsum_congr key, h1.tsum_add h2', tsum_mul_left]
    ring
  · simp only [spheroidalRadial]
    rw [tsum_congr key', h1.tsum_sub h2', tsum_mul_left]
    ring

/-! ### §30.11(iii) Asymptotic behaviour -/

/-- **Asymptotic behaviour** (DLMF 30.11.6, `j = 1, 2`, corrected): for real `γ > 0`, as
`z → ∞` in `|ph z| ≤ π - δ`, `S^{m(j)}_n(z, γ) = ψ^{(j)}_n(γz) + O(z⁻² e^{|ℑ(γz)|})`. DLMF prints
`e^{|ℑz|}`, which is wrong for `γ > 1` (see the module docstring). -/
@[dlmf 30.11.E6]
theorem spheroidalRadial_isBigO_one_two {j n m : ℕ} (hmn : m ≤ n) {γ δ : ℝ} (hγ : 0 < γ)
    (hδ : 0 < δ) (hj : j = 1 ∨ j = 2) :
    (fun z : ℂ => spheroidalRadial j n m z γ - spheroidalPsi j n (γ * z)) =O[DLMF.sector (π - δ)]
      (fun z : ℂ => z ^ (-2 : ℤ) * Real.exp |(γ * z).im|) := by
  sorry

/-- **Asymptotic behaviour** (DLMF 30.11.6, `j = 3, 4`): for real `γ > 0`, as `z → ∞` in
`|ph z| ≤ π - δ`, `S^{m(j)}_n(z, γ) = ψ^{(j)}_n(γz)(1 + O(z⁻¹))`. -/
@[dlmf 30.11.E6]
theorem spheroidalRadial_isBigO_three_four {j n m : ℕ} (hmn : m ≤ n) {γ δ : ℝ} (hγ : 0 < γ)
    (hδ : 0 < δ) (hj : j = 3 ∨ j = 4) :
    (fun z : ℂ => spheroidalRadial j n m z γ - spheroidalPsi j n (γ * z)) =O[DLMF.sector (π - δ)]
      (fun z : ℂ => spheroidalPsi j n (γ * z) * z⁻¹) := by
  sorry

/-! ### §30.11(iv) Wronskian -/

/-- **Wronskian** (DLMF 30.11.7): `𝒲{S^{m(1)}_n(z, γ), S^{m(2)}_n(z, γ)} = 1/(γ(z²-1))`, for
`|z| > 1` with `1 - z⁻²` and `γz` off `(-∞, 0]`. -/
@[dlmf 30.11.E7]
theorem wronskian_spheroidalRadial {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hz : 1 < ‖z‖) (hz' : 1 - z ^ (-2 : ℤ) ∈ slitPlane)
    (hγz : γ * z ∈ slitPlane) :
    spheroidalRadial 1 n m z γ * deriv (fun t => spheroidalRadial 2 n m t γ) z -
        deriv (fun t => spheroidalRadial 1 n m t γ) z * spheroidalRadial 2 n m z γ =
      1 / (γ * (z ^ 2 - 1)) := by
  sorry

/-! ### §30.11(v) Connection with `𝑃s` and `𝑄s` -/

/-- **Connection with `𝑃s`** (DLMF 30.11.8, with `K^m_n(γ)` from 30.11.10–30.11.11):
`S^{m(1)}_n(z, γ) = K^m_n(γ) 𝑃s^m_n(z, γ²)` for `z ∈ ℂ ∖ (-∞, 1]`, `γ ≠ 0`, `γ²` real. -/
@[dlmf 30.11.E8, dlmf 30.11.E10, dlmf 30.11.E11]
theorem spheroidalRadial_one_eq {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hz : z ∈ spheroidalCutPlane) :
    spheroidalRadial 1 n m z γ = spheroidalK n m γ * spheroidalPsC n m z (γ ^ 2).re := by
  sorry

/-- **Connection with `𝑄s`** (DLMF 30.11.9):
`S^{m(2)}_n(z, γ) = (n-m)!/(n+m)! (-1)^{m+1} 𝑄s^m_n(z, γ²)/(γ K^m_n(γ) A^m_n(γ²) A^{-m}_n(γ²))`
for `z ∈ ℂ ∖ (-∞, 1]` with `|z| > 1` and `γz` off `(-∞, 0]`. -/
@[dlmf 30.11.E9]
theorem spheroidalRadial_two_eq {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0)
    (hf : spheroidalFwd n m (γ ^ 2).re ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0)
    (hz : z ∈ spheroidalCutPlane) (hz1 : 1 < ‖z‖) (hγz : γ * z ∈ slitPlane) :
    spheroidalRadial 2 n m z γ = ((n - m).factorial : ℂ) / (n + m).factorial *
      ((-1) ^ (m + 1) * spheroidalQsC n m z (γ ^ 2).re) /
        (γ * spheroidalK n m γ * spheroidalA n m (γ ^ 2).re * spheroidalANeg n m (γ ^ 2).re) := by
  sorry

/-! ### §30.11(vi) Integral representation -/

/-- **Integral representation** (DLMF 30.11.12): for `z ∈ ℂ ∖ (-∞, 1]`,
`A^{-m}_n(γ²) S^{m(1)}_n(z, γ) = ½ i^{m+n} γ^m (n-m)!/(n+m)! z^m (1-z⁻²)^{m/2}
  ∫_{-1}^1 e^{-iγzt} (1-t²)^{m/2} 𝖯s^m_n(t, γ²) dt`. -/
@[dlmf 30.11.E12]
theorem spheroidalRadial_one_integral {n m : ℕ} (hmn : m ≤ n) {z γ : ℂ} (hγ : γ ≠ 0)
    (hγ2 : (γ ^ 2).im = 0) (hz : z ∈ spheroidalCutPlane) :
    spheroidalANeg n m (γ ^ 2).re * spheroidalRadial 1 n m z γ =
      1 / 2 * I ^ (m + n) * γ ^ m * (((n - m).factorial : ℂ) / (n + m).factorial) * z ^ m *
        (1 - z ^ (-2 : ℤ)) ^ ((m : ℂ) / 2) *
        ∫ t in (-1 : ℝ)..1, Complex.exp (-(I * γ * z * t)) *
          (((1 - t ^ 2) ^ ((m : ℝ) / 2) * spheroidalPs n m t (γ ^ 2).re : ℝ) : ℂ) := by
  sorry

end DLMF.Spheroidal
