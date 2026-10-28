/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic

/-!
# Mathieu functions of noninteger order: definitions (DLMF §§28.12, 28.14)

DLMF §28.12 introduces, for `ν ∉ ℤ`, the eigenvalues `λ_ν(q)` (the values of `a` for which
Mathieu's equation 28.2.1 has a Floquet solution with respect to `ν`, continued analytically
from `λ_ν(0) = ν²`, 28.12.1), the Floquet solutions `me_ν(z, q)` normalized by 28.12.5, and
`ce_ν`, `se_ν` (28.12.12, 28.12.13). For integer order DLMF completes the definitions by
`λ_m = a_m` (`m ≥ 0`), `λ_m = b_{-m}` (`m < 0`) (28.12.3) and `me_n = √2 ce_n`,
`me_{-n} = -√2 i se_n` (28.12.11).

## Design (definitions by choice)

The Fourier series 28.14.1, `me_ν(z, q) = ∑_m c^ν_{2m}(q) e^{i(ν+2m)z}`, turns the Floquet
problem into the three-term recurrence 28.14.4 with the normalization 28.14.5
(`∑ (c^ν_{2m})² = 1`, which is 28.12.5). `IsMeCoeffSeq ν q a c` says that `c : ℤ → ℂ` is an
absolutely summable solution of 28.14.4 for the value `a` and satisfies 28.14.5.

DLMF defines `λ_ν(q)` for `q ≠ 0` "by analytic continuation" from `q = 0`, and fixes the sign
of the coefficients "by continuity" from 28.14.9 (`c^ν_0(0) = 1`). We make this precise
along the **straight segment** `t ↦ t q`, `t ∈ [0, 1]`:

* `IsMathieuLambdaPath ν q Λ c`: `Λ : ℝ → ℂ` and every `t ↦ c t m` are continuous on
  `[0, 1]`, `Λ 0 = ν²`, `c 0 0 = 1`, and for each `t ∈ [0, 1]` the sequence `c t` satisfies
  `IsMeCoeffSeq ν (t q) (Λ t)`.
* `MathieuNormalSegment ν q`: the endpoint `(Λ 1, c 1)` of such a path exists and is unique.
  For `ν ∉ ℤ` this holds when every point `t q` of the segment is a normal value with respect
  to `ν` in DLMF's sense (§28.12(i): the roots of 28.2.16 are simple), in particular for real
  `ν ∉ ℤ` and real `q` (all roots are then real and simple). It is the hypothesis of the
  theorems where DLMF assumes `q` normal; it is stronger than DLMF's pointwise normality.
* `mathieuLambdaData ν q`: that endpoint if `MathieuNormalSegment ν q`, and `(0, 0)` otherwise
  (junk value).

Then, for `ν ∉ ℤ`, `mathieuLambda ν q = λ_ν(q)` is the first component, the Fourier
coefficients `mathieuMeCoeff ν q m = c^ν_{2m}(q)` are the second, and
`mathieuMe ν z q = me_ν(z, q)` is the Fourier series 28.14.1 (a `tsum`; its convergence for
all complex `z` is the theorem 28.14.1).

For integer order the project's eigenvalues and eigenfunctions are defined for real `q` only
(`DLMF.Mathieu.mathieuA`, `mathieuB`, `mathieuCe`, `mathieuSe` in `DLMF.Mathieu.Basic`), so
`mathieuLambda m q` and `mathieuMe m z q` for `m ∈ ℤ` follow 28.12.3 and 28.12.11 when `q` is
real and are junk `0` for nonreal `q`. For integer `ν` the coefficients `mathieuMeCoeff` are
defined as the Fourier coefficients `π⁻¹ ∫₀^π me_ν(x, q) e^{-i(ν+2m)x} dx` of `me_ν`.

`mathieuCeNu`, `mathieuSeNu` are given by 28.12.12, 28.12.13 for every `ν`; DLMF uses them
for `ν ∉ ℤ` only (at integer `ν` they are not `ce_n`, `se_n`).

Argument order is DLMF's: `λ_ν(q)` is `mathieuLambda ν q`, `me_ν(z, q)` is
`mathieuMe ν z q`, `c^ν_{2m}(q)` is `mathieuMeCoeff ν q m` (index `m`, not `2m`).
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Classical

namespace DLMF.Mathieu

/-! ### The recurrence for the Fourier coefficients and the continuation path -/

/-- `c : ℤ → ℂ` is an admissible coefficient sequence of a Floquet solution with respect to
`ν` for the parameters `(a, q)`: it solves the three-term recurrence (DLMF 28.14.4)
`q c_{2m+2} - (a - (ν + 2m)²) c_{2m} + q c_{2m-2} = 0` (indexed by `m`), is absolutely
summable, and is normalized by `∑ (c_{2m})² = 1` (DLMF 28.14.5). -/
def IsMeCoeffSeq (ν q a : ℂ) (c : ℤ → ℂ) : Prop :=
  (∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0) ∧
    Summable (fun m => ‖c m‖) ∧ HasSum (fun m => c m ^ 2) 1

/-- A continuation path for `λ_ν` and the coefficients `c^ν_{2m}` along the segment
`t ↦ t q`, `t ∈ [0, 1]` (DLMF §28.12(i): "determined by analytic continuation"; §28.14:
signs "resolved by (28.14.9) when `q = 0`, and by continuity for other values of `q`"). -/
structure IsMathieuLambdaPath (ν q : ℂ) (Λ : ℝ → ℂ) (c : ℝ → ℤ → ℂ) : Prop where
  /-- `t ↦ Λ(t)` is continuous on `[0, 1]`. -/
  continuousOn_lambda : ContinuousOn Λ (Icc 0 1)
  /-- Each coefficient `t ↦ c_t(m)` is continuous on `[0, 1]`. -/
  continuousOn_coeff : ∀ m : ℤ, ContinuousOn (fun t => c t m) (Icc 0 1)
  /-- The path starts at `λ_ν(0) = ν²`. -/
  lambda_zero : Λ 0 = ν ^ 2
  /-- At `t = 0` the central coefficient is `c_0 = 1` (DLMF 28.14.9). -/
  coeff_zero : c 0 0 = 1
  /-- For each `t ∈ [0, 1]`, `(Λ(t), c_t)` solves the recurrence 28.14.4 with `q` replaced by
  `t q`. -/
  isMeCoeffSeq : ∀ t ∈ Icc (0 : ℝ) 1, IsMeCoeffSeq ν (t * q) (Λ t) (c t)

/-- `q` is **normal along the segment** `[0, q]` with respect to `ν`: the continuation of
`(λ_ν, c^ν)` along `t ↦ t q` exists and its endpoint is unique (DLMF §28.12(i), normal
values). For real `ν ∉ ℤ` and real `q` this holds (`DLMF.Mathieu.mathieuNormalSegment_real`). -/
def MathieuNormalSegment (ν q : ℂ) : Prop :=
  ∃! p : ℂ × (ℤ → ℂ), ∃ Λ c, IsMathieuLambdaPath ν q Λ c ∧ Λ 1 = p.1 ∧ c 1 = p.2

/-- The endpoint `(λ_ν(q), (c^ν_{2m}(q))_m)` of the continuation along `[0, q]`, or `(0, 0)`
if `q` is not normal along the segment. -/
def mathieuLambdaData (ν q : ℂ) : ℂ × (ℤ → ℂ) :=
  if h : MathieuNormalSegment ν q then h.choose else (0, 0)

/-! ### Integer order (DLMF 28.12.3, 28.12.11) -/

/-- `λ_m(q)` for integer `m` and real `q` (DLMF 28.12.3): `a_m(q)` for `m ≥ 0` and
`b_{-m}(q)` for `m < 0`. -/
def mathieuLambdaInt (m : ℤ) (q : ℝ) : ℝ :=
  if 0 ≤ m then mathieuA m.toNat q else mathieuB m.natAbs q

/-- `me_m(z, q)` for integer `m` and real `q` (DLMF 28.12.11): `√2 ce_m(z, q)` for `m ≥ 0`
and `-√2 i se_{-m}(z, q)` for `m < 0`. -/
def mathieuMeInt (m : ℤ) (z : ℂ) (q : ℝ) : ℂ :=
  if 0 ≤ m then (Real.sqrt 2 : ℂ) * mathieuCe m.toNat z q
  else -((Real.sqrt 2 : ℂ) * I) * mathieuSe m.natAbs z q

/-! ### `λ_ν(q)`, `me_ν(z, q)`, `c^ν_{2m}(q)`, `ce_ν`, `se_ν` -/

/-- The **eigenvalue** `λ_ν(q)` of Mathieu's equation (DLMF §28.12(i)). For `ν ∉ ℤ`: the value
of `a` for which 28.2.1 has a Floquet solution with respect to `ν`, continued from
`λ_ν(0) = ν²` (28.12.1) along the segment `[0, q]` (junk `0` unless
`MathieuNormalSegment ν q`). For integer `ν = m` and real `q`: `a_m(q)` or `b_{-m}(q)`
(28.12.3); junk `0` for integer `ν` and nonreal `q`. -/
@[dlmf 28.12.i]
def mathieuLambda (ν q : ℂ) : ℂ :=
  if h : ∃ m : ℤ, (m : ℂ) = ν then
    (if q.im = 0 then (mathieuLambdaInt h.choose q.re : ℂ) else 0)
  else (mathieuLambdaData ν q).1

/-- The **Mathieu function** `me_ν(z, q)` (DLMF §28.12(ii)). For `ν ∉ ℤ`: the Floquet
solution with respect to `ν` for `a = λ_ν(q)`, given by its Fourier series 28.14.1
`∑_m c^ν_{2m}(q) e^{i(ν+2m)z}` with the continued coefficients, normalized by 28.12.5. For
integer `ν` and real `q`: 28.12.11; junk `0` for integer `ν` and nonreal `q`. -/
@[dlmf 28.12.ii]
def mathieuMe (ν z q : ℂ) : ℂ :=
  if h : ∃ m : ℤ, (m : ℂ) = ν then
    (if q.im = 0 then mathieuMeInt h.choose z q.re else 0)
  else ∑' m : ℤ, (mathieuLambdaData ν q).2 m * Complex.exp (I * (ν + 2 * m) * z)

/-- The **Fourier coefficients** `c^ν_{2m}(q)` of `me_ν(z, q)` (DLMF 28.14.1), indexed by
`m ∈ ℤ`. For `ν ∉ ℤ` the continued solution of 28.14.4–28.14.5 (with `c^ν_0(0) = 1`,
28.14.9); for integer `ν` the Fourier coefficients
`π⁻¹ ∫₀^π me_ν(x, q) e^{-i(ν+2m)x} dx`. -/
@[dlmf 28.14.E1]
def mathieuMeCoeff (ν q : ℂ) (m : ℤ) : ℂ :=
  if ∃ k : ℤ, (k : ℂ) = ν then
    (1 / π : ℂ) * ∫ x in (0 : ℝ)..π,
      mathieuMe ν x q * Complex.exp (-(I * (ν + 2 * m) * x))
  else (mathieuLambdaData ν q).2 m

/-- The **Mathieu function** `ce_ν(z, q) = ½ (me_ν(z, q) + me_ν(-z, q))` (DLMF 28.12.12), used
for `ν ∉ ℤ` (at integer `ν` this is not `ce_n`). -/
@[dlmf 28.12.E12]
def mathieuCeNu (ν z q : ℂ) : ℂ :=
  (mathieuMe ν z q + mathieuMe ν (-z) q) / 2

/-- The **Mathieu function** `se_ν(z, q) = -½ i (me_ν(z, q) - me_ν(-z, q))` (DLMF 28.12.13),
used for `ν ∉ ℤ` (at integer `ν` this is not `se_n`). -/
@[dlmf 28.12.E13]
def mathieuSeNu (ν z q : ℂ) : ℂ :=
  -(I / 2) * (mathieuMe ν z q - mathieuMe ν (-z) q)

/-! ### Unfolding lemmas -/

/-- `λ_ν(q)` for `ν ∉ ℤ` is the first component of the continuation endpoint. -/
theorem mathieuLambda_of_not_int {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (q : ℂ) :
    mathieuLambda ν q = (mathieuLambdaData ν q).1 := by
  have : ¬ ∃ m : ℤ, (m : ℂ) = ν := fun ⟨m, hm⟩ => hν m hm
  simp [mathieuLambda, this]

/-- `me_ν(z, q)` for `ν ∉ ℤ` is the Fourier series with the continued coefficients. -/
theorem mathieuMe_of_not_int {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z q : ℂ) :
    mathieuMe ν z q =
      ∑' m : ℤ, mathieuMeCoeff ν q m * Complex.exp (I * (ν + 2 * m) * z) := by
  have : ¬ ∃ m : ℤ, (m : ℂ) = ν := fun ⟨m, hm⟩ => hν m hm
  simp [mathieuMe, mathieuMeCoeff, this]

/-- `c^ν_{2m}(q)` for `ν ∉ ℤ` is the second component of the continuation endpoint. -/
theorem mathieuMeCoeff_of_not_int {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (q : ℂ) (m : ℤ) :
    mathieuMeCoeff ν q m = (mathieuLambdaData ν q).2 m := by
  have : ¬ ∃ m : ℤ, (m : ℂ) = ν := fun ⟨m, hm⟩ => hν m hm
  simp [mathieuMeCoeff, this]

/-- `λ_m(q)` for integer `m` and real `q` (DLMF 28.12.3). -/
theorem mathieuLambda_intCast (m : ℤ) (q : ℝ) :
    mathieuLambda m q = mathieuLambdaInt m q := by
  simp [mathieuLambda]

/-- `me_m(z, q)` for integer `m` and real `q` (DLMF 28.12.11). -/
theorem mathieuMe_intCast (m : ℤ) (z : ℂ) (q : ℝ) :
    mathieuMe m z q = mathieuMeInt m z q := by
  simp [mathieuMe]

/-! ### Continued fractions (DLMF 28.15.2) and stability (DLMF §28.17) -/

/-- The finite continued fraction
`q² / (a - (ν + 2k)² - q² / (a - (ν + 2k + 2)² - ⋯ - q² / (a - (ν + 2k + 2N - 2)²)))` with `N`
levels (`0` for `N = 0`), the `N`-th approximant of the continued fractions of DLMF 28.15.2:
the right-going one is `mathieuContFrac ν q a 1 N`, the left-going one
`mathieuContFrac (-ν) q a 1 N`. -/
def mathieuContFrac (ν q a : ℂ) : ℕ → ℕ → ℂ
  | _, 0 => 0
  | k, N + 1 => q ^ 2 / (a - (ν + 2 * k) ^ 2 - mathieuContFrac ν q a (k + 1) N)

/-- The pair `(a, q)` is **stable** (DLMF §28.17): all solutions of Mathieu's equation 28.2.1
are bounded on the real axis. Otherwise the pair is unstable. -/
@[dlmf 28.17]
def IsMathieuStable (a q : ℂ) : Prop :=
  ∀ w : ℂ → ℂ, IsMathieuSolution a q w → ∃ C : ℝ, ∀ x : ℝ, ‖w x‖ ≤ C

end DLMF.Mathieu
