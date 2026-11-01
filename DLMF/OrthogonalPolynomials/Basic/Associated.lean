/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.AskeyScheme

/-!
# Associated, Bessel and Pollaczek polynomials

The canonical definitions of the associated orthogonal polynomials (DLMF §18.30), the Bessel
polynomials (DLMF §18.34) and the Pollaczek polynomials (DLMF §18.35).

## Main definitions

* `associated`: the general associated family of a three-term recurrence (DLMF 18.30.3).
* `associatedLaguerre`, `associatedHermite`, `associatedMeixnerPollaczek`: the associated
  Laguerre, Hermite and Meixner–Pollaczek polynomials (DLMF 18.30.9, 18.30.13, 18.30.16).
* `pollaczek`: the Pollaczek polynomials `P_n^{(λ)}(x; a, b, c)` (DLMF 18.35.2).
* `besselPolynomial`, `reverseBesselPolynomial`: the Bessel polynomials `y_n(x; a)` and their
  reversal (DLMF 18.34.1–18.34.2).

## Main results

* `associated_zero`: the initial value of the associated family (DLMF 18.30.2).
* `pollaczek_zero`, `pollaczek_one`, `pollaczek_recurrence`: the initial values and the
  three-term recurrence of the Pollaczek polynomials (DLMF 18.35.2).

## Implementation notes

The properties of these families are in `DLMF.OrthogonalPolynomials.Associated`.
-/

@[expose] public section

open Complex

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- General associated family. The shift may be real, as in DLMF §18.30.
The `n = 0` step is written separately to avoid a negative natural index. -/
@[dlmf 18.30.E3]
def associated (A B C : ℝ → ℂ) (c : ℝ) : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, x => A c * x + B c
  | n + 2, x => (A (n + 1 + c) * x + B (n + 1 + c)) * associated A B C c (n + 1) x -
      C (n + 1 + c) * associated A B C c n x

/-- The associated Laguerre polynomials `L_n^{(λ)}(x; c)`, defined by the shifted Laguerre
recurrence (DLMF 18.30.9). -/
@[dlmf 18.30.E9]
def associatedLaguerre (lam : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => -(t + 1 : ℂ)⁻¹)
    (fun t => (2 * t + lam + 1) / (t + 1)) (fun t => (t + lam) / (t + 1)) c

/-- The associated Hermite polynomials `H_n(x; c)`, defined by the shifted Hermite recurrence
(DLMF 18.30.13). -/
@[dlmf 18.30.E13]
def associatedHermite (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun _ => 2) (fun _ => 0) (fun t => 2 * t) c

/-- The associated Meixner–Pollaczek polynomials `P_n^{(λ)}(x; φ, c)`, defined by the
shifted recurrence (DLMF 18.30.16). -/
@[dlmf 18.30.E16]
def associatedMeixnerPollaczek (lam phi : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => 2 * sin phi / (t + 1))
    (fun t => 2 * (t + lam) * cos phi / (t + 1))
    (fun t => (t + 2 * lam - 1) / (t + 1)) c

/-- The (associated) Pollaczek polynomials `P_n^{(λ)}(x; a, b, c)`, defined by their
three-term recurrence (DLMF 18.35.2). -/
@[dlmf 18.35.E2]
def pollaczek (lam a b : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => 2 * (t + lam + a) / (t + 1))
    (fun t => 2 * b / (t + 1)) (fun t => (t + 2 * lam - 1) / (t + 1)) c

/-- The Bessel polynomial `y_n(x; a) = ₂F₀(-n, n+a-1; ; -x/2)` (DLMF 18.34.1). -/
@[dlmf 18.34.E1]
def besselPolynomial (a : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), n + a - 1] [] (-x / 2)

/-- Polynomial form of the reversal, valid also at zero. -/
@[dlmf 18.34.E2]
def reverseBesselPolynomial (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch (n + 1) k *
    (-1 / 2 : ℂ) ^ k * x ^ (n - k) / k.factorial

/-- Identity under the stated parameter and domain assumptions: `associated A B C c 0 x = 1`. -/
@[dlmf 18.30.E2]
theorem associated_zero (A B C : ℝ → ℂ) (c : ℝ) (x : ℂ) : associated A B C c 0 x = 1 := by
  rfl
/-- The Pollaczek polynomial of degree zero. -/
theorem pollaczek_zero (lam a b x : ℂ) : pollaczek lam a b 0 0 x = 1 := by
  simp [pollaczek, associated]

/-- The Pollaczek polynomial of degree one. -/
theorem pollaczek_one (lam a b x : ℂ) :
    pollaczek lam a b 0 1 x = 2 * (lam + a) * x + 2 * b := by
  simp [pollaczek, associated]

/-- The three-term recurrence of the Pollaczek polynomials, DLMF 18.35.2. -/
theorem pollaczek_recurrence (lam a b x : ℂ) (n : ℕ) :
    (n + 2 : ℂ) * pollaczek lam a b 0 (n + 2) x =
      (2 * (n + 1 + lam + a) * x + 2 * b) * pollaczek lam a b 0 (n + 1) x -
        (n + 2 * lam) * pollaczek lam a b 0 n x := by
  have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  change (n + 2 : ℂ) * ((2 * ((n + 1 + (0 : ℝ) : ℝ) + lam + a) / ((n + 1 + (0 : ℝ) : ℝ) + 1) * x +
      2 * b / ((n + 1 + (0 : ℝ) : ℝ) + 1)) * pollaczek lam a b 0 (n + 1) x -
      (((n + 1 + (0 : ℝ) : ℝ) + 2 * lam - 1) / ((n + 1 + (0 : ℝ) : ℝ) + 1)) *
        pollaczek lam a b 0 n x) = _
  have hn' : (2 : ℂ) + n ≠ 0 := by rw [add_comm]; exact hn
  push_cast
  rw [show (n : ℂ) + 1 + 0 + 1 = n + 2 by ring, show (n : ℂ) + 1 + 0 = n + 1 by ring]
  field_simp
  ring

end DLMF.OrthogonalPolynomials
