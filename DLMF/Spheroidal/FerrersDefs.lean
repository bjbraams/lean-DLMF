/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.Basic
public import DLMF.Legendre.Basic

/-!
# Spheroidal wave functions: definitions built on Ferrers functions (DLMF §§30.1, 30.5, 30.6,
30.8, 30.11)

This definitions file contains the objects of Chapter 30 whose DLMF definition involves the
Ferrers functions `𝖯^m_ν(x)` (the project's `DLMF.Legendre.ferrersP`):

* the coefficients `a^m_{n,k}(γ²)` of the Ferrers expansion 30.8.1, defined by the integral
  30.8.2 for `k ≥ -R` and extended to `-N ≤ k < -R` by the forward recursion of §30.8(ii)
  (`spheroidalCoeff`), the coefficients `a^{-m}_{n,k}(γ²)` of 30.8.6 (`spheroidalCoeffNeg`), the
  recessive coefficients `a'^m_{n,k}(γ²)` of 30.8.9–30.8.10 (`spheroidalCoeffPrime`) and the sums
  `A^{±m}_n(γ²)` of 30.11.4 (`spheroidalA`, `spheroidalANeg`);
* the functions of the second kind `spheroidalQs n m x γ2 = 𝖰s^m_n(x, γ²)` (30.5.1) and
  `spheroidalQsC n m z γ2 = 𝑄s^m_n(z, γ²)` (30.6.1);
* the radial spheroidal functions `spheroidalRadial j n m z γ = S^{m(j)}_n(z, γ)` (30.11.3) and
  the factors `K^m_n(γ)` of 30.11.10–30.11.11;
* Flammer's normalization `d_{mn}(γ)` and functions `S^{(1)}_{mn}`, `S^{(2)}_{mn}` (30.1.1–30.1.2).

**Import note.** `ferrersP` comes from the Legendre definitions file `DLMF.Legendre.Basic`
(moved there from `DLMF.Legendre.Ferrers` on 2026-10-26).

## Design notes (choices flagged)

* `a^m_{n,k}(γ²)` for `-N ≤ k < -R` (`N = ⌊(n+m)/2⌋`, `R = ⌊(n-m)/2⌋`) is
  `a^m_{n,-R} f_k / f_{-R}`, with `f` the forward solution `spheroidalFwd` (`f_{-N-1} = 0`,
  `f_{-N} = 1`); DLMF says that `𝖰s` does not exist when `f_{-R} = 0`, and then these values are
  junk `0`. These extended coefficients enter `A^m_n(γ²)` (the sum in 30.11.4 runs over
  `2k ≥ -m - n`), which was confirmed numerically through the Wronskian 30.5.4.
* `𝖰s^m_n(x, γ²)` is defined by choice as the solution of 30.2.1 on `(-1, 1)` with the parity
  30.5.2 and the Wronskian 30.5.4 (it vanishes off `(-1, 1)`). These two properties determine it:
  a second such function differs by a multiple of `𝖯s`, which has the opposite parity. The
  Meixner–Schäfke series 30.8.9 is a theorem. Existence is admitted
  (`exists_isSpheroidalQs`).
* `𝑄s^m_n(z, γ²)` is defined by choice as the solution of 30.2.1 on `ℂ ∖ (-∞, 1]` whose boundary
  values from the upper half plane are those of 30.6.5 (upper signs); the lower signs are a
  theorem. Existence and uniqueness are admitted (`existsUnique_isSpheroidalQsC`).
* The radial functions take complex `z` and `γ`, with `γ²` real in DLMF; the coefficients are
  evaluated at `(γ^2).re`, and the theorems assume `(γ^2).im = 0`.
-/

@[expose] public noncomputable section

open Complex Set Filter DLMF.Legendre
open scoped Topology Real Classical

namespace DLMF.Spheroidal

/-- `dif_pos` without the deprecation. -/
private lemma s30_dif_pos' {c : Prop} [Decidable c] (h : c) {α : Sort*} {t : c → α}
    {e : ¬c → α} : dite c t e = t h := by simp [h]

/-! ### Ferrers coefficients (§30.8) -/

/-- The integral formula 30.8.2,
`(-1)^k (n + 2k + 1/2) (n-m+2k)!/(n+m+2k)! ∫_{-1}^1 𝖯s^m_n(x, γ²) 𝖯^m_{n+2k}(x) dx`,
meaningful for `k ≥ -R = -⌊(n-m)/2⌋`. -/
@[dlmf 30.8.E2]
def spheroidalCoeffMain (n m : ℕ) (γ2 : ℝ) (k : ℤ) : ℝ :=
  (-1 : ℝ) ^ k * ((n : ℝ) + 2 * k + 1 / 2) *
    ((((n : ℤ) - m + 2 * k).toNat.factorial : ℝ) / (((n : ℤ) + m + 2 * k).toNat.factorial)) *
    ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP ((n : ℂ) + 2 * k) m x).re

/-- **The coefficients** `a^m_{n,k}(γ²)` (DLMF 30.8.2 and §30.8(ii)), `k ∈ ℤ`: the integral
30.8.2 for `k ≥ -R`, the forward recursion of 30.8.4 from `a^m_{n,-N-1} = 0` matched at `k = -R`
for `-N ≤ k < -R`, and `0` for `k < -N` (`R = ⌊(n-m)/2⌋`, `N = ⌊(n+m)/2⌋`). -/
@[dlmf 30.8.E2]
def spheroidalCoeff (n m : ℕ) (γ2 : ℝ) (k : ℤ) : ℝ :=
  if -(((n - m) / 2 : ℕ) : ℤ) ≤ k then spheroidalCoeffMain n m γ2 k
  else if -(((n + m) / 2 : ℕ) : ℤ) ≤ k then
    spheroidalCoeffMain n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) *
      spheroidalFwd n m γ2 (k + ((n + m) / 2 : ℕ) + 1).toNat /
        spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1)
  else 0

/-- **The coefficients** `a^{-m}_{n,k}(γ²) = (n-m)!(n+m+2k)!/((n+m)!(n-m+2k)!) a^m_{n,k}(γ²)`
(DLMF 30.8.6), for `k ≥ -R` (`0` for `k < -R`). -/
@[dlmf 30.8.E6]
def spheroidalCoeffNeg (n m : ℕ) (γ2 : ℝ) (k : ℤ) : ℝ :=
  if -(((n - m) / 2 : ℕ) : ℤ) ≤ k then
    (((n - m).factorial : ℝ) * (((n : ℤ) + m + 2 * k).toNat.factorial : ℝ)) /
      (((n + m).factorial : ℝ) * (((n : ℤ) - m + 2 * k).toNat.factorial : ℝ)) *
        spheroidalCoeff n m γ2 k
  else 0

/-- `A^m_n(γ²) = ∑_{2k ≥ -m-n} (-1)^k a^m_{n,k}(γ²)` (DLMF 30.11.4, upper sign). -/
@[dlmf 30.11.E4]
def spheroidalA (n m : ℕ) (γ2 : ℝ) : ℝ := ∑' k : ℤ, (-1 : ℝ) ^ k * spheroidalCoeff n m γ2 k

/-- `A^{-m}_n(γ²) = ∑_{2k ≥ m-n} (-1)^k a^{-m}_{n,k}(γ²)` (DLMF 30.11.4, lower sign). -/
@[dlmf 30.11.E4]
def spheroidalANeg (n m : ℕ) (γ2 : ℝ) : ℝ := ∑' k : ℤ, (-1 : ℝ) ^ k * spheroidalCoeffNeg n m γ2 k

/-- **The recessive coefficients** `a'^m_{n,k}(γ²)`, `k ≤ -N - 1` (DLMF §30.8(ii)): a solution
of 30.8.4 for `k ≤ -N - 2` that is recessive as `k → -∞` (negligible against every solution not
proportional to it), normalized by 30.8.10 with `C'` from 30.8.11; extended by `0` for
`k ≥ -N`. -/
@[dlmf 30.8.E10]
structure IsSpheroidalCoeffPrime (n m : ℕ) (γ2 : ℝ) (f : ℤ → ℝ) : Prop where
  /-- `f` vanishes for `k ≥ -N`. -/
  support : ∀ k : ℤ, -(((n + m) / 2 : ℕ) : ℤ) ≤ k → f k = 0
  /-- The recurrence 30.8.4 for `k ≤ -N - 2`. -/
  recurrence : ∀ k : ℤ, k ≤ -(((n + m) / 2 : ℕ) : ℤ) - 2 →
    spheroidalRecA n m γ2 k * f (k - 1) +
      (spheroidalRecB n m γ2 k - spheroidalEigenvalue n m γ2) * f k +
        spheroidalRecC n m γ2 k * f (k + 1) = 0
  /-- The normalization 30.8.10 at `k = -N - 1`. -/
  normalization :
    spheroidalRecA n m γ2 (-(((n + m) / 2 : ℕ) : ℤ) - 1) * f (-(((n + m) / 2 : ℕ) : ℤ) - 2) +
      (spheroidalRecB n m γ2 (-(((n + m) / 2 : ℕ) : ℤ) - 1) - spheroidalEigenvalue n m γ2) *
        f (-(((n + m) / 2 : ℕ) : ℤ) - 1) +
      spheroidalCPrime n m γ2 * spheroidalCoeff n m γ2 (-(((n + m) / 2 : ℕ) : ℤ)) = 0
  /-- Recessiveness as `k → -∞`. -/
  recessive : ∀ h : ℤ → ℝ, (∀ k : ℤ, k ≤ -(((n + m) / 2 : ℕ) : ℤ) - 2 →
      spheroidalRecA n m γ2 k * h (k - 1) +
        (spheroidalRecB n m γ2 k - spheroidalEigenvalue n m γ2) * h k +
          spheroidalRecC n m γ2 k * h (k + 1) = 0) →
    (¬ ∃ c : ℝ, ∀ k : ℤ, k ≤ -(((n + m) / 2 : ℕ) : ℤ) - 1 → h k = c * f k) →
    Tendsto (fun j : ℕ => f (-(j : ℤ)) / h (-(j : ℤ))) atTop (𝓝 0)

/-- `a'^m_{n,k}(γ²)` (DLMF §30.8(ii)), defined by choice (junk `0` if it did not exist). -/
@[dlmf 30.8.E9]
def spheroidalCoeffPrime (n m : ℕ) (γ2 : ℝ) : ℤ → ℝ :=
  if h : ∃ f, IsSpheroidalCoeffPrime n m γ2 f then h.choose else 0

/-! ### Functions of the second kind (§§30.5, 30.6) -/

/-- **Characterization of `𝖰s^m_n(x, γ²)`** (DLMF 30.5.1, 30.5.2, 30.5.4): a solution of 30.2.1
on `(-1, 1)` with `μ = m`, `λ = λ^m_n(γ²)`, of parity `(-1)^{n-m+1}`, whose Wronskian with
`𝖯s^m_n` is `(n+m)!/((1-x²)(n-m)!) A^m_n(γ²) A^{-m}_n(γ²)`; it vanishes off `(-1, 1)`. -/
@[dlmf 30.5.E1]
structure IsSpheroidalQs (n m : ℕ) (γ2 : ℝ) (f : ℝ → ℝ) : Prop where
  /-- `f` solves 30.2.1 on `(-1, 1)`. -/
  ode : IsSpheroidalSolutionReal (spheroidalEigenvalue n m γ2) γ2 m f
  /-- The parity 30.5.2. -/
  parity : ∀ x ∈ Ioo (-1 : ℝ) 1, f (-x) = (-1) ^ (n - m + 1) * f x
  /-- The Wronskian 30.5.4. -/
  wronskian : ∀ x ∈ Ioo (-1 : ℝ) 1,
    spheroidalPs n m x γ2 * deriv f x - deriv (fun t => spheroidalPs n m t γ2) x * f x =
      ((n + m).factorial : ℝ) / ((1 - x ^ 2) * (n - m).factorial) *
        spheroidalA n m γ2 * spheroidalANeg n m γ2
  /-- `f` vanishes off `(-1, 1)`. -/
  outside : ∀ x : ℝ, x ∉ Ioo (-1 : ℝ) 1 → f x = 0

/-- **The spheroidal wave function of the second kind** `𝖰s^m_n(x, γ²)` (DLMF 30.5.1), for
`-1 < x < 1`, defined by choice from its characterization `IsSpheroidalQs` (junk `0` if it did
not exist). -/
@[dlmf 30.5.E1]
def spheroidalQs (n m : ℕ) (x γ2 : ℝ) : ℝ :=
  if h : ∃ f, IsSpheroidalQs n m γ2 f then h.choose x else 0

/-- The cut plane `ℂ ∖ (-∞, 1]` of DLMF §30.6. -/
def spheroidalCutPlane : Set ℂ := {z : ℂ | z - 1 ∈ slitPlane}

/-- **Characterization of `𝑄s^m_n(z, γ²)`** (DLMF 30.6.1, 30.6.5): a solution of 30.2.1 on
`ℂ ∖ (-∞, 1]` with `μ = m`, `λ = λ^m_n(γ²)`, whose boundary values from the upper half plane on
`(-1, 1)` are `(-i)^m (𝖰s^m_n(x, γ²) - (iπ/2) 𝖯s^m_n(x, γ²))`; it vanishes on `(-∞, 1]`. -/
@[dlmf 30.6.E1]
structure IsSpheroidalQsC (n m : ℕ) (γ2 : ℝ) (F : ℂ → ℂ) : Prop where
  /-- `F` solves 30.2.1 on the cut plane. -/
  ode : IsSpheroidalSolutionOn (spheroidalEigenvalue n m γ2) γ2 m spheroidalCutPlane F
  /-- The boundary values 30.6.5 (upper signs). -/
  boundary : ∀ x ∈ Ioo (-1 : ℝ) 1, Tendsto (fun ε : ℝ => F (x + ε * I)) (𝓝[>] 0)
    (𝓝 ((-I) ^ m * (spheroidalQs n m x γ2 - I * π / 2 * spheroidalPs n m x γ2)))
  /-- `F` vanishes off the cut plane. -/
  outside : ∀ z : ℂ, z ∉ spheroidalCutPlane → F z = 0

/-- **The spheroidal wave function of the second kind of complex argument** `𝑄s^m_n(z, γ²)`
(DLMF 30.6.1), for `z ∈ ℂ ∖ (-∞, 1]`, defined by choice from `IsSpheroidalQsC` (junk `0` if it
did not exist). -/
@[dlmf 30.6.E1]
def spheroidalQsC (n m : ℕ) (z : ℂ) (γ2 : ℝ) : ℂ :=
  if h : ∃ F, IsSpheroidalQsC n m γ2 F then h.choose z else 0

/-! ### Radial spheroidal wave functions (§30.11) -/

/-- **The radial spheroidal wave functions** `S^{m(j)}_n(z, γ)`, `j = 1, 2, 3, 4`
(DLMF 30.11.3): `(1-z⁻²)^{m/2}/A^{-m}_n(γ²) ∑_{2k ≥ m-n} a^{-m}_{n,k}(γ²) ψ^{(j)}_{n+2k}(γz)`,
for `z ≠ 0` (`j = 1`) or `|z| > 1` (`j = 2, 3, 4`); `γ²` real, the coefficients are evaluated at
`(γ^2).re`. -/
@[dlmf 30.11.E3]
def spheroidalRadial (j n m : ℕ) (z γ : ℂ) : ℂ :=
  (1 - z ^ (-2 : ℤ)) ^ ((m : ℂ) / 2) / spheroidalANeg n m (γ ^ 2).re *
    ∑' k : ℤ, (spheroidalCoeffNeg n m (γ ^ 2).re k : ℂ) *
      spheroidalPsi j ((n : ℤ) + 2 * k).toNat (γ * z)

/-- **The factor** `K^m_n(γ)` of 30.11.8 (DLMF 30.11.10 for `n - m` even, 30.11.11 for `n - m`
odd), `γ²` real (evaluated at `(γ^2).re`). -/
@[dlmf 30.11.E10, dlmf 30.11.E11]
def spheroidalK (n m : ℕ) (γ : ℂ) : ℂ :=
  if Even (n - m) then
    Real.sqrt π / 2 * (γ / 2) ^ m *
      ((-1) ^ m * spheroidalCoeffNeg n m (γ ^ 2).re (-(((n - m) / 2 : ℕ) : ℤ))) /
        (Complex.Gamma (3 / 2 + m) * spheroidalANeg n m (γ ^ 2).re *
          spheroidalPs n m 0 (γ ^ 2).re)
  else
    Real.sqrt π / 2 * (γ / 2) ^ (m + 1) *
      ((-1) ^ m * spheroidalCoeffNeg n m (γ ^ 2).re (-(((n - m) / 2 : ℕ) : ℤ))) /
        (Complex.Gamma (5 / 2 + m) * spheroidalANeg n m (γ ^ 2).re *
          deriv (fun x => spheroidalPs n m x (γ ^ 2).re) 0)

/-! ### Flammer's notation (§30.1) -/

/-- **Flammer's normalization constant** `d_{mn}(γ)` (DLMF 30.1.2), a function of `γ²`: chosen so
that `S^{(1)}_{mn}(γ, 0) = (-1)^m 𝖯^m_n(0)` for `n - m` even and
`dS^{(1)}_{mn}(γ, x)/dx|_{x=0} = (-1)^m d𝖯^m_n(x)/dx|_{x=0}` for `n - m` odd. -/
@[dlmf 30.1.E2]
def flammerD (n m : ℕ) (γ2 : ℝ) : ℝ :=
  if Even (n - m) then (-1) ^ m * (ferrersP n m 0).re / spheroidalPs n m 0 γ2
  else (-1) ^ m * deriv (fun x : ℝ => (ferrersP n m x).re) 0 /
    deriv (fun x => spheroidalPs n m x γ2) 0

/-- **Flammer's angular function of the first kind** `S^{(1)}_{mn}(γ, x) = d_{mn}(γ) 𝖯s^m_n(x, γ²)`
(DLMF 30.1.1), as a function of `γ²`. -/
@[dlmf 30.1.E1]
def flammerS1 (n m : ℕ) (γ2 x : ℝ) : ℝ := flammerD n m γ2 * spheroidalPs n m x γ2

/-- **Flammer's angular function of the second kind** `S^{(2)}_{mn}(γ, x) = d_{mn}(γ) 𝖰s^m_n(x, γ²)`
(DLMF 30.1.1), as a function of `γ²`. -/
@[dlmf 30.1.E1]
def flammerS2 (n m : ℕ) (γ2 x : ℝ) : ℝ := flammerD n m γ2 * spheroidalQs n m x γ2

/-! ### Existence theorems (flagged) -/

/-- **Existence of the recessive coefficients** `a'^m_{n,k}(γ²)` (DLMF §30.8(ii)), for
`m ≤ n`. Flagged existence theorem (admitted): the recurrence 30.8.4 has, as `k → -∞`, a
recessive solution, unique up to a factor fixed by 30.8.10. -/
@[dlmf 30.8.ii]
theorem exists_isSpheroidalCoeffPrime {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ f, IsSpheroidalCoeffPrime n m γ2 f := by
  sorry

/-- **Existence of `𝖰s^m_n`** (DLMF §30.5, §30.8(ii)): for `m ≤ n`, when the forward recursion of
§30.8(ii) does not vanish at `k = -R` (otherwise DLMF states that `𝖰s` does not exist). Flagged
existence theorem (admitted); uniqueness holds by the parity argument. -/
@[dlmf 30.5.E1]
theorem exists_isSpheroidalQs {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    ∃ f, IsSpheroidalQs n m γ2 f := by
  sorry

/-- **Existence and uniqueness of `𝑄s^m_n`** (DLMF §30.6), under the hypotheses of
`exists_isSpheroidalQs`. Flagged existence theorem (admitted). -/
@[dlmf 30.6.E1]
theorem existsUnique_isSpheroidalQsC {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    ∃! F, IsSpheroidalQsC n m γ2 F := by
  sorry

/-- The defining property of `𝖰s^m_n` (DLMF 30.5.1), from `exists_isSpheroidalQs`. -/
theorem spheroidalQs_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    IsSpheroidalQs n m γ2 (fun x => spheroidalQs n m x γ2) := by
  have h := exists_isSpheroidalQs hmn γ2 hf
  have he : (fun x => spheroidalQs n m x γ2) = h.choose := by
    funext x; simp only [spheroidalQs, s30_dif_pos' h]
  rw [he]; exact h.choose_spec

/-- The defining property of `𝑄s^m_n` (DLMF 30.6.1), from `existsUnique_isSpheroidalQsC`. -/
theorem spheroidalQsC_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    IsSpheroidalQsC n m γ2 (fun z => spheroidalQsC n m z γ2) := by
  have h := (existsUnique_isSpheroidalQsC hmn γ2 hf).exists
  have he : (fun z => spheroidalQsC n m z γ2) = h.choose := by
    funext z; simp only [spheroidalQsC, s30_dif_pos' h]
  rw [he]; exact h.choose_spec

/-- The defining property of `a'^m_{n,k}` (DLMF §30.8(ii)), from
`exists_isSpheroidalCoeffPrime`. -/
theorem spheroidalCoeffPrime_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    IsSpheroidalCoeffPrime n m γ2 (spheroidalCoeffPrime n m γ2) := by
  have h := exists_isSpheroidalCoeffPrime hmn γ2
  simp only [spheroidalCoeffPrime, s30_dif_pos' h]
  exact h.choose_spec

end DLMF.Spheroidal
