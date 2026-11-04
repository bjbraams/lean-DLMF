/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Basic
public import DLMF.Confluent.Continuation
public import DLMF.Statistical.IncompleteGamma

/-!
# The normalized incomplete Gamma functions `P` and `Q` (DLMF §§8.2, 8.4, 8.8)

The normalized incomplete Gamma functions `regularizedGamma` (`P`) and
`regularizedIncompleteGammaQ` (`Q`) are the continuations `P(a,z) = z^a γ*(a,z)` and
`Q = 1 - P`. Away from the poles of `Γ(a)` they are the quotients `γ(a,z)/Γ(a)` and
`Γ(a,z)/Γ(a)` of DLMF 8.2.4; the quotient form of `Q` also holds at the poles, where both
sides vanish.

## Main results

* `regularizedGamma_eq`: `P(a,z) = γ(a,z)/Γ(a)` for `a` not a nonpositive integer
  (DLMF 8.2.4).
* `regularizedIncompleteGammaQ_eq`, `regularizedIncompleteGammaQ_eq'`:
  `Q(a,z) = Γ(a,z)/Γ(a)` for `z ≠ 0` (DLMF 8.2.4).
* `regularizedGamma_add_regularizedIncompleteGammaQ`,
  `regularizedGamma_add_regularizedIncompleteGammaQ'`: `P + Q = 1` (DLMF 8.2.5).
* `tricomiIncompleteGamma_eq_regularizedGamma`: `γ*(a,z) = z^{-a} P(a,z)` (DLMF 8.2.7).
* `regularizedGamma_add_one`, `regularizedIncompleteGammaQ_add_one`: the recurrences DLMF
  8.8.5–8.8.6.
* `regularizedIncompleteGammaQ_nat_succ`, `regularizedGamma_nat_succ`:
  `Q(n+1,z) = e^{-z} ∑_{k ≤ n} z^k/k!` (DLMF 8.4.10), the Poisson tail, and its complement
  (DLMF 8.4.11).
* `regularizedGamma_ofReal`, `regularizedIncompleteGammaQ_ofReal`: at real `s, x > 0`, `P` is
  TauCeti's `regularizedGamma`.
-/

@[expose] public noncomputable section

open Complex DLMF.Statistical DLMF.Hypergeometric
open scoped Real Topology Nat

namespace DLMF.Confluent

/-- Away from nonpositive integral parameters, the analytically continued lower regularization
is the quotient `γ(a,z)/Γ(a)` (DLMF 8.2.4). -/
@[dlmf 8.2.E4]
theorem regularizedGamma_eq {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    regularizedGamma a z = lowerIncompleteGamma a z / Gamma a := by
  have h := regularizedConfluent_kummer_transform a (a+1) (-z)
  rw [show a+1-a=1 by ring] at h
  rw [regularizedGamma, lowerIncompleteGamma_eq_regularized ha, h, tricomiIncompleteGamma]
  field_simp [Gamma_ne_zero ha]

/-- `P(a,z) + Q(a,z) = 1` for all complex `a` and `z`; stronger than DLMF 8.2.5 as formalized
in `regularizedGamma_add_regularizedIncompleteGammaQ`, which assumes `z ≠ 0` and `a` not a
nonpositive integer. -/
@[dlmf 8.2.E5 "stronger than DLMF: no conditions on a, z"]
theorem regularizedGamma_add_regularizedIncompleteGammaQ' (a z : ℂ) :
    regularizedGamma a z + regularizedIncompleteGammaQ a z = 1 := by
  simp [regularizedIncompleteGammaQ]

/-- `P(a,z) + Q(a,z) = 1` (DLMF 8.2.5) for `z ≠ 0` and `a` not a nonpositive integer. -/
@[dlmf 8.2.E5]
theorem regularizedGamma_add_regularizedIncompleteGammaQ {a : ℂ} (_ha : ∀ k : ℕ, a ≠ -k)
    {z : ℂ} (_hz : z ≠ 0) : regularizedGamma a z + regularizedIncompleteGammaQ a z = 1 :=
  regularizedGamma_add_regularizedIncompleteGammaQ' a z

/-- At nonzero arguments the continued upper regularization is the totalized quotient
`Γ(a,z)/Γ(a)` for every complex `a`; stronger than `regularizedIncompleteGammaQ_eq`, which
assumes `a` not a nonpositive integer. At `a = -n` both sides vanish. -/
@[dlmf 8.2.E4 "stronger than DLMF: also at the poles of Γ(a), where both sides vanish"]
theorem regularizedIncompleteGammaQ_eq' (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    regularizedIncompleteGammaQ a z = upperIncompleteGamma a z / Gamma a := by
  by_cases ha : ∀ n : ℕ, a ≠ -n
  · have h := lowerIncompleteGamma_add_upperIncompleteGamma ha hz
    rw [regularizedIncompleteGammaQ, regularizedGamma_eq ha]
    field_simp [Gamma_ne_zero ha]
    linear_combination -h
  · push Not at ha
    obtain ⟨n, rfl⟩ := ha
    have hG : Gamma (-(n : ℂ)) = 0 := Complex.Gamma_neg_nat_eq_zero n
    rw [hG, div_zero, regularizedIncompleteGammaQ, regularizedGamma,
      tricomiIncompleteGamma_neg_nat, cpow_neg, cpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero n hz), sub_self]

/-- Away from nonpositive integral parameters and at nonzero arguments, the continued upper
regularization is the quotient `Γ(a,z)/Γ(a)` (DLMF 8.2.4). -/
@[dlmf 8.2.E4]
theorem regularizedIncompleteGammaQ_eq {a : ℂ} (_ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    regularizedIncompleteGammaQ a z = upperIncompleteGamma a z / Gamma a :=
  regularizedIncompleteGammaQ_eq' a hz

/-- `γ*(a,z) = z^{-a} P(a,z)` for every complex `a` and `z ≠ 0`; stronger than DLMF 8.2.7 as
formalized in `tricomiIncompleteGamma_eq_regularizedGamma`, which assumes `a` not a nonpositive
integer. -/
@[dlmf 8.2.E7 "stronger than DLMF: also at nonpositive integral a"]
theorem tricomiIncompleteGamma_eq_regularizedGamma' (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    tricomiIncompleteGamma a z = z ^ (-a) * regularizedGamma a z := by
  rw [regularizedGamma, ← mul_assoc, cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hz)),
    one_mul]

/-- `γ*(a,z) = z^{-a} P(a,z)` (DLMF 8.2.7). -/
@[dlmf 8.2.E7]
theorem tricomiIncompleteGamma_eq_regularizedGamma {a : ℂ} (_ha : ∀ k : ℕ, a ≠ -k) {z : ℂ}
    (hz : z ≠ 0) : tricomiIncompleteGamma a z = z ^ (-a) * regularizedGamma a z :=
  tricomiIncompleteGamma_eq_regularizedGamma' a hz

/-- `Q(a+1,z) = Q(a,z) + z^a e^{-z}/Γ(a+1)` (DLMF 8.8.6). -/
@[dlmf 8.8.E6]
theorem regularizedIncompleteGammaQ_add_one {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    {z : ℂ} (hz : z ≠ 0) :
    regularizedIncompleteGammaQ (a + 1) z = regularizedIncompleteGammaQ a z +
        z ^ a * exp (-z) / Gamma (a + 1) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have hG := Gamma_ne_zero ha
  rw [regularizedIncompleteGammaQ_eq' _ hz, regularizedIncompleteGammaQ_eq' _ hz,
      upperIncompleteGamma_add_one a hz, Complex.Gamma_add_one a ha0]
  field_simp

/-- `P(a+1,z) = P(a,z) - z^a e^{-z}/Γ(a+1)` (DLMF 8.8.5). -/
@[dlmf 8.8.E5]
theorem regularizedGamma_add_one {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    {z : ℂ} (hz : z ≠ 0) :
    regularizedGamma (a + 1) z = regularizedGamma a z - z ^ a * exp (-z) / Gamma (a + 1) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have hG := Gamma_ne_zero ha
  rw [regularizedGamma_eq (add_one_ne_neg_nat ha), regularizedGamma_eq ha,
      lowerIncompleteGamma_add_one ha hz, Complex.Gamma_add_one a ha0]
  field_simp

/-- The Poisson tail `Q(n+1,z) = e^{-z} ∑_{k ≤ n} z^k/k!` (DLMF 8.4.10). -/
@[dlmf 8.4.E10]
theorem regularizedIncompleteGammaQ_nat_succ (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    regularizedIncompleteGammaQ ((n : ℂ) + 1) z = exp (-z) * ∑ k ∈ Finset.range (n + 1),
        z ^ k / k ! := by
  induction n with
  | zero => simp [regularizedIncompleteGammaQ_eq' _ hz, upperIncompleteGamma_one]
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℂ) + 1 = ((n : ℂ) + 1) + 1 by push_cast; ring,
      regularizedIncompleteGammaQ_add_one (natCast_add_one_ne_neg_nat n) hz, ih,
          Finset.sum_range_succ _ (n + 1),
      show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      Complex.Gamma_nat_eq_factorial]
    ring

/-- `P(n+1,z) = 1 - e^{-z} ∑_{k ≤ n} z^k/k!` (DLMF 8.4.11 with 8.2.5). -/
@[dlmf 8.4.E11]
theorem regularizedGamma_nat_succ (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGamma ((n : ℂ) + 1) z = 1 - exp (-z) * ∑ k ∈ Finset.range (n + 1),
        z ^ k / k ! := by
  have h := regularizedGamma_add_regularizedIncompleteGammaQ' ((n : ℂ) + 1) z
  rw [regularizedIncompleteGammaQ_nat_succ n hz] at h
  linear_combination h

/-- For real `s > 0` and `x > 0`, `P(s,x)` is TauCeti's regularized Gamma function. -/
theorem regularizedGamma_ofReal {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    regularizedGamma s x = (TauCeti.regularizedGamma s x : ℂ) := by
  have hs' : ∀ k : ℕ, (s : ℂ) ≠ -k := fun k hk => by
    have := congrArg re hk
    simp at this
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  rw [regularizedGamma_eq hs', lowerIncompleteGamma_ofReal hs hx,
      TauCeti.regularizedGamma_eq_div, Complex.ofReal_div, Complex.Gamma_ofReal]

/-- For real `s > 0` and `x > 0`, `Q(s,x) = 1 - P(s,x)` with TauCeti's `P`. -/
theorem regularizedIncompleteGammaQ_ofReal {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    regularizedIncompleteGammaQ s x = 1 - (TauCeti.regularizedGamma s x : ℂ) := by
  rw [regularizedIncompleteGammaQ, regularizedGamma_ofReal hs hx]

end DLMF.Confluent
