/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Hahn and Wilson classes of orthogonal polynomials

The canonical definitions of the hypergeometric orthogonal polynomials of the Askey scheme:
the Hahn class (DLMF §18.19–§18.20) and the Wilson class (DLMF §18.25–§18.26).

## Main definitions

* `terminatingHG`: a terminating hypergeometric sum with an explicit cutoff.
* `hahn`, `krawtchouk`, `meixner`, `charlier`: DLMF 18.20.5–18.20.8.
* `continuousHahn`, `meixnerPollaczek`: DLMF 18.20.9 and 18.20.10.
* `continuousHahnWeight`, `meixnerPollaczekWeight`: the weights DLMF 18.19.2 and 18.19.7.
* `wilson`, `continuousDualHahn`, `racah`, `dualHahn`: DLMF 18.26.1–18.26.4.

## Main results

* `terminatingHG_hasSum_neg_nat`: with a negative integral first upper parameter the finite sum
  is the full hypergeometric series.
* `krawtchouk_zero`, `meixnerPollaczek_zero`, `meixnerPollaczek_one`,
  `DiscreteOrtho.charlier_zero`, `DiscreteOrtho.charlier_one`, `DiscreteOrtho.meixner_zero`:
  the polynomials of degrees zero and one.

## Implementation notes

Terminating hypergeometric sums carry an explicit cutoff, which implements DLMF's convention
when a lower parameter is a negative integer. The Wilson-class polynomials use the polynomial
arguments `y²` and `λ(y)`, so no square root is chosen. The properties of these families are
in `DLMF.OrthogonalPolynomials.Hahn` and `DLMF.OrthogonalPolynomials.Wilson`.
-/

@[expose] public section

open Complex

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- A terminating hypergeometric sum, with an explicit cutoff. This implements
DLMF's convention when a lower parameter is a negative integer. -/
def terminatingHG (n : ℕ) (a b : List ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (a.map (fun t => poch t k)).prod / (b.map (fun t => poch t k)).prod *
      z ^ k / (k.factorial : ℂ)

/-- A negative integral first upper parameter makes the finite sum a genuine infinite sum. -/
theorem terminatingHG_hasSum_neg_nat (n : ℕ) (a b : List ℂ) (z : ℂ) :
    HasSum (fun k : ℕ => (((-(n : ℂ) :: a).map (fun t => poch t k)).prod /
      (b.map (fun t => poch t k)).prod * z ^ k / (k.factorial : ℂ)))
      (terminatingHG n (-(n : ℂ) :: a) b z) := by
  unfold terminatingHG
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  have hnk : n < k := by simpa using hk
  simp [poch_neg_nat_eq_zero hnk]


/-- The Hahn polynomial `Q_n(x; α, β, N) = ₃F₂(-n, n+α+β+1, -x; α+1, -N; 1)` (DLMF 18.20.5). -/
@[dlmf 18.20.E5]
def hahn (α β : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), n + α + β + 1, -x] [α + 1, -(N : ℂ)] 1

/-- The Krawtchouk polynomial `K_n(x; p, N) = ₂F₁(-n, -x; -N; 1/p)` (DLMF 18.20.6). -/
@[dlmf 18.20.E6]
def krawtchouk (p : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), -x] [-(N : ℂ)] p⁻¹

/-- The Meixner polynomial `M_n(x; β, c) = ₂F₁(-n, -x; β; 1 - 1/c)` (DLMF 18.20.7). -/
@[dlmf 18.20.E7]
def meixner (β c : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), -x] [β] (1 - c⁻¹)

/-- The Charlier polynomial `C_n(x; a) = ₂F₀(-n, -x; ; -1/a)` (DLMF 18.20.8). -/
@[dlmf 18.20.E8]
def charlier (a : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), -x] [] (-a⁻¹)

/-- The four-parameter polynomial; the orthogonality regime has `c = conj a`,
`d = conj b`. -/
@[dlmf 18.20.E9]
def continuousHahn (a b c d : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  I ^ n * poch (a + c) n * poch (a + d) n / n.factorial *
    terminatingHG n [-(n : ℂ), n + a + b + c + d - 1, a + I * x] [a + c, a + d] 1

/-- The Meixner–Pollaczek polynomial
`P_n^{(λ)}(x; φ) = (2λ)_n/n! e^{inφ} ₂F₁(-n, λ+ix; 2λ; 1 - e^{-2iφ})` (DLMF 18.20.10). -/
@[dlmf 18.20.E10]
def meixnerPollaczek (lam phi : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (2 * lam) n / n.factorial * exp (I * n * phi) *
    terminatingHG n [-(n : ℂ), lam + I * x] [2 * lam] (1 - exp (-2 * I * phi))

/-- The continuous Hahn weight `Γ(a+ix) Γ(b+ix) Γ(ā-ix) Γ(b̄-ix)` (DLMF 18.19.2). -/
@[dlmf 18.19.E2]
def continuousHahnWeight (a b : ℂ) (x : ℂ) : ℂ :=
  Gamma (a + I * x) * Gamma (b + I * x) * Gamma (star a - I * x) * Gamma (star b - I * x)

/-- The Meixner–Pollaczek weight `Γ(λ+ix) Γ(λ-ix) e^{(2φ-π)x}` (DLMF 18.19.7). -/
@[dlmf 18.19.E7]
def meixnerPollaczekWeight (lam phi : ℂ) (x : ℂ) : ℂ :=
  Gamma (lam + I * x) * Gamma (lam - I * x) * exp ((2 * phi - Real.pi) * x)

/-- Wilson polynomials in the polynomial argument `x = y²`. The product form
avoids choosing a square root. -/
@[dlmf 18.26.E1]
def wilson (a b c d : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (a + b) n * poch (a + c) n * poch (a + d) n *
    ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k *
        (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
        (poch (a + b) k * poch (a + c) k * poch (a + d) k * k.factorial)

/-- The continuous dual Hahn polynomial `S_n(x; a, b, c)` with polynomial argument `x = y²`,
as the finite `₃F₂` sum of DLMF 18.26.2. -/
@[dlmf 18.26.E2]
def continuousDualHahn (a b c : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (a + b) n * poch (a + c) n *
    ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
      (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
      (poch (a + b) k * poch (a + c) k * k.factorial)

/-- The Racah polynomial `R_n(x; α, β, γ, δ)` in the variable `x = λ(y)`, as the finite `₄F₃`
sum of DLMF 18.26.3. -/
@[dlmf 18.26.E3]
def racah (α β γ δ : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch (n + α + β + 1) k *
    (∏ j ∈ Finset.range k, ((j : ℂ) * (j + γ + δ + 1) - x)) /
    (poch (α + 1) k * poch (β + δ + 1) k * poch (γ + 1) k * k.factorial)

/-- The dual Hahn polynomial `R_n(x; γ, δ, N)` in the variable `x = λ(y)`, as the finite `₃F₂`
sum of DLMF 18.26.4. -/
@[dlmf 18.26.E4]
def dualHahn (γ δ : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
    (∏ j ∈ Finset.range k, ((j : ℂ) * (j + γ + δ + 1) - x)) /
    (poch (γ + 1) k * poch (-(N : ℂ)) k * k.factorial)
/-! ### Degrees zero and one -/

/-- `K_0(x; p, N) = 1`. -/
theorem krawtchouk_zero (p : ℂ) (N : ℕ) (x : ℂ) : krawtchouk p N 0 x = 1 := by
  simp [krawtchouk, terminatingHG, poch_zero]

/-- The Meixner–Pollaczek polynomial of degree zero. -/
theorem meixnerPollaczek_zero (lam phi x : ℂ) : meixnerPollaczek lam phi 0 x = 1 := by
  simp [meixnerPollaczek, terminatingHG, poch_zero]

/-- The Meixner–Pollaczek polynomial of degree one. -/
theorem meixnerPollaczek_one {lam : ℂ} (hlam : lam ≠ 0) (phi x : ℂ) :
    meixnerPollaczek lam phi 1 x = 2 * (x * sin phi + lam * cos phi) := by
  unfold meixnerPollaczek terminatingHG
  set u := cexp (I * phi) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  have e2 : cexp (-2 * I * phi) = (u ^ 2)⁻¹ := by
    rw [hu, ← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; push_cast; ring
  have hcos : cos phi = (u + u⁻¹) / 2 := by
    rw [Complex.cos, hu, ← Complex.exp_neg]; congr 2 <;> ring_nf
  have hsin : sin phi = (u⁻¹ - u) * I / 2 := by
    rw [Complex.sin, hu, ← Complex.exp_neg]; congr 3 <;> ring_nf
  rw [e2]
  simp [Finset.sum_range_succ, poch_zero, poch_one, hcos, hsin, ← hu]
  field_simp
  ring_nf

namespace DiscreteOrtho

/-- `C_0(x; a) = 1`. -/
theorem charlier_zero (a x : ℂ) : charlier a 0 x = 1 := by
  simp [charlier, terminatingHG, poch_zero]

/-- `C_1(x; a) = 1 - x/a`. -/
theorem charlier_one {a : ℂ} (ha : a ≠ 0) (x : ℂ) : charlier a 1 x = 1 - x / a := by
  simp [charlier, terminatingHG, Finset.sum_range_succ, poch_zero, poch_one]
  field_simp
  ring

/-- `M_0(x; β, c) = 1`. -/
theorem meixner_zero (β c x : ℂ) : meixner β c 0 x = 1 := by
  simp [meixner, terminatingHG, poch_zero]

end DiscreteOrtho

end DLMF.OrthogonalPolynomials
