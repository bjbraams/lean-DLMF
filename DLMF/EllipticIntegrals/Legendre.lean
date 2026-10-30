/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.AnalyticProperties
public import DLMF.Elliptic.ThirdKind
public import Carlson.Elliptic.Standard

/-!
# Legendre's elliptic integrals: definitions (DLMF §§19.1–19.2)

DLMF 19.2 defines Legendre's integrals for complex amplitude `φ`, modulus `k` and
characteristic `α²` as integrals along the **line segment** from `0` to `φ`, with **principal**
square roots (DLMF §19.1):

* `incEllIntFk φ k = ∫₀^φ (1 - k² sin²θ)^{-1/2} dθ` (19.2.4),
* `incEllIntEk φ k = ∫₀^φ (1 - k² sin²θ)^{1/2} dθ` (19.2.5),
* `incEllIntDk φ k = ∫₀^φ sin²θ (1 - k² sin²θ)^{-1/2} dθ` (19.2.6),
* `incEllIntPik φ α² k = ∫₀^φ (1 - α² sin²θ)⁻¹ (1 - k² sin²θ)^{-1/2} dθ` (19.2.7), with the
  **Cauchy principal value** when `1 - α² sin²θ` vanishes at an interior point of the path;
* the complete integrals `K(k) = F(π/2, k)` (the existing `DLMF.JacobiElliptic.compEllIntKk`),
  `compEllIntEk`, `compEllIntDk`, `compEllIntPik` (19.2.8);
* Legendre's complementary integrals `cCompEllIntKk`, `cCompEllIntEk` (`K'`, `E'`, 19.2.8_1,
  19.2.8_2, 19.2.9), with the branch point at `k = 0` and principal branch `|ph k| ≤ π`;
* Bulirsch's integrals `bulirschCel`, `bulirschEl1`, `bulirschEl2`, `bulirschEl3`
  (19.2.11, 19.2.11_5, 19.2.12, 19.2.16).

## Design

* **Path integrals.** `ei19a_segmentIntegral f w = ∫₀¹ w f(t w) dt` is the integral of `f` along
  the segment `[0, w]`; for real `w` it is the interval integral `∫₀^w f`
  (`ei19a_segmentIntegral_ofReal`).
* **Principal values.** `ei19a_pvSegmentIntegral g f w` is the limit, as `ε → 0+`, of the segment
  integral of `f` over the part of the path where `‖g‖ ≥ ε`. For a simple zero of `g` this excises
  an asymptotically symmetric neighbourhood, so the limit is the Cauchy principal value
  (DLMF §1.4(v)); when `g` is bounded away from `0` on the path it is the ordinary integral
  (`ei19a_pvSegmentIntegral_eq`). `Π` and Bulirsch's `cel`, `el3` use it with
  `g = 1 - α² sin²θ`, resp. `g = cos²θ + p sin²θ`.
* **Branches.** Powers are Mathlib's principal `cpow` (argument in `(-π, π]`), which is DLMF's
  principal square root off the cut. Outside DLMF's domains (19.2(ii): `1 - sin²φ` and
  `1 - k² sin²φ` in `ℂ \ (-∞, 0]`, except that one of them may be `0`, and `1 - α² sin²φ ≠ 0`) the
  definitions are totalized: a non-integrable integrand gives `0`, a non-existent principal
  value gives `limUnder`'s junk value.
* **K and K'.** `K(k)` and the literal `K(k') = compEllIntKpk k` are the existing definitions of
  `DLMF.JacobiElliptic` (Chapter 22). The literal integral (19.2.8_1) is a function of `k²` and
  is discontinuous across the imaginary axis; DLMF's `K'` is its continuation from `k > 0` to
  `ℂ \ (-∞, 0]`, given explicitly by (19.2.9). `cCompEllIntKk`, `cCompEllIntEk` are defined by
  (19.2.9); on the imaginary axis they take the limit from `Re k > 0`, and on the cut
  `(-∞, 0)` (where 19.2.9 is silent) the limit from `Im k > 0`. Numerically (mpmath) the
  definition is continuous across the imaginary axis and satisfies Legendre's relation
  (19.7.1) at complex `k` with `Re k < 0`.
* **Bridges.** For real `φ` and real `k` with `k² ≤ 1` the complex integrals are the real
  `DLMF.Elliptic.Real.incEllIntFm/Em/Pim` (parameter `m = k²`) and the real
  `Carlson.Real.incEllIntFk/Ek/Pik` of `lean-codes`; the complete integrals are
  `Real.compEllIntKm/Em` and `Carlson.Real.compEllIntKk/Ek`.

Mathlib and the pinned TauCeti have no Legendre elliptic integrals of complex argument
(checked 2026-10-25); the companion library `lean-codes` (Carlson) has the real ones.

## References

* NIST DLMF §§19.1, 19.2.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977 (via `lean-codes`).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### Path integrals along a segment and principal values -/

/-- The integral of `f` along the line segment from `0` to `w`, `∫₀¹ w f(t w) dt`. -/
def ei19a_segmentIntegral (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, w * f (t * w)

/-- The Cauchy principal value of the integral of `f` along the segment `[0, w]`, with the
singularities located at the zeros of `g`: the limit as `ε → 0+` of the integral over the part
of the path where `‖g‖ ≥ ε`. -/
def ei19a_pvSegmentIntegral (g f : ℂ → ℂ) (w : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ =>
    ∫ t in (0 : ℝ)..1, if ε ≤ ‖g (t * w)‖ then w * f (t * w) else 0

/-- For real `φ` the segment integral is the interval integral `∫₀^φ f`. -/
theorem ei19a_segmentIntegral_ofReal (f : ℂ → ℂ) (φ : ℝ) :
    ei19a_segmentIntegral f φ = ∫ θ in (0 : ℝ)..φ, f θ := by
  rw [ei19a_segmentIntegral, intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1)
    (fun θ : ℝ => f θ) φ
  simp only [zero_mul, one_mul, Complex.real_smul] at h
  rw [← h]
  congr 2
  funext t
  push_cast
  ring_nf

/-- The principal value is the ordinary segment integral when `g` is bounded away from `0` on the
path. -/
theorem ei19a_pvSegmentIntegral_eq {g f : ℂ → ℂ} {w : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖g (t * w)‖) :
    ei19a_pvSegmentIntegral g f w = ei19a_segmentIntegral f w := by
  rw [ei19a_pvSegmentIntegral, ei19a_segmentIntegral]
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp [hε.2.le.trans (hg t ht)]

/-- The principal value over the degenerate segment `[0, 0]` is `0`. -/
theorem ei19a_pvSegmentIntegral_zero (g f : ℂ → ℂ) : ei19a_pvSegmentIntegral g f 0 = 0 := by
  rw [ei19a_pvSegmentIntegral]
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' (Eventually.of_forall fun ε => ?_))
  simp

/-- If `1 - z` lies in the slit plane, so does `1 - s z` for `0 ≤ s ≤ 1`. -/
theorem ei19a_one_sub_mul_mem_slitPlane {z : ℂ} (hz : 1 - z ∈ slitPlane) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : 1 - z * s ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_im, one_im,
    mul_im, zero_sub, neg_eq_zero, ne_eq] at hz ⊢
  rcases hs0.lt_or_eq with hs | hs
  · by_cases him : z.im = 0
    · simp only [him, not_true_eq_false, or_false] at hz
      left
      rcases le_or_gt z.re 0 with h | h
      · nlinarith
      · nlinarith
    · right; rw [zero_add]; exact mul_ne_zero him hs.ne'
  · subst hs; left; simp

/-- For real `θ`, `1 - k² sin²θ` lies in the slit plane when `1 - k²` does
(`k² ∉ [1, ∞)`, the principal domain of `K` and `E`). -/
theorem ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (θ : ℝ) :
    1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
  have := ei19a_one_sub_mul_mem_slitPlane hk (sq_nonneg (Real.sin θ)) (Real.sin_sq_le_one θ)
  simpa using this

/-! ### Legendre's incomplete integrals (DLMF 19.2.4–19.2.7) -/

/-- Legendre's incomplete elliptic integral of the first kind (DLMF 19.2.4),
`F(φ, k) = ∫₀^φ (1 - k² sin²θ)^{-1/2} dθ` along the segment `[0, φ]`, principal square root.
DLMF's domain: `1 - sin²φ, 1 - k² sin²φ ∈ ℂ \ (-∞, 0]`, one of them possibly `0`. -/
@[dlmf 19.2.E4, dlmf 19.1.E2]
def incEllIntFk (φ k : ℂ) : ℂ :=
  ei19a_segmentIntegral (fun θ => (1 - k ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ))) φ

/-- Legendre's incomplete elliptic integral of the second kind (DLMF 19.2.5),
`E(φ, k) = ∫₀^φ (1 - k² sin²θ)^{1/2} dθ` along the segment `[0, φ]`, principal square root.
It is well defined at `k² = sin²φ = 1`. -/
@[dlmf 19.2.E5, dlmf 19.1.E2]
def incEllIntEk (φ k : ℂ) : ℂ :=
  ei19a_segmentIntegral (fun θ => (1 - k ^ 2 * Complex.sin θ ^ 2) ^ (1 / 2 : ℂ)) φ

/-- Jahnke's integral (DLMF 19.2.6), `D(φ, k) = ∫₀^φ sin²θ (1 - k² sin²θ)^{-1/2} dθ` along the
segment `[0, φ]`; `D = (F - E)/k²` is `incEllIntDk_eq`. -/
@[dlmf 19.2.E6]
def incEllIntDk (φ k : ℂ) : ℂ :=
  ei19a_segmentIntegral
    (fun θ => Complex.sin θ ^ 2 * (1 - k ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ))) φ

/-- Legendre's incomplete elliptic integral of the third kind (DLMF 19.2.7),
`Π(φ, α², k) = ∫₀^φ (1 - α² sin²θ)⁻¹ (1 - k² sin²θ)^{-1/2} dθ` along the segment `[0, φ]`; the
**Cauchy principal value** is taken when `1 - α² sin²θ` vanishes at an interior point of the
path (DLMF §19.2(ii)). DLMF requires `1 - α² sin²φ ≠ 0`. The second argument is the
characteristic `α²` itself (DLMF's argument order). -/
@[dlmf 19.2.E7, dlmf 19.1.E2]
def incEllIntPik (φ α2 k : ℂ) : ℂ :=
  ei19a_pvSegmentIntegral (fun θ => 1 - α2 * Complex.sin θ ^ 2)
    (fun θ => (1 - α2 * Complex.sin θ ^ 2)⁻¹ * (1 - k ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ))) φ

/-! ### Complete integrals (DLMF 19.2.8) -/

/-- Legendre's complete integral of the second kind (DLMF 19.2.8), `E(k) = E(π/2, k)`, principal
branch `|ph(1 - k²)| ≤ π` (cuts `(-∞, -1] ∪ [1, ∞)` in `k`). The first kind is the existing
`DLMF.JacobiElliptic.compEllIntKk`. -/
@[dlmf 19.2.E8, dlmf 19.1.E1]
def compEllIntEk (k : ℂ) : ℂ := incEllIntEk (π / 2) k

/-- The complete integral `D(k) = D(π/2, k) = (K(k) - E(k))/k²` (DLMF 19.2.8). -/
@[dlmf 19.2.E8]
def compEllIntDk (k : ℂ) : ℂ := incEllIntDk (π / 2) k

/-- Legendre's complete integral of the third kind (DLMF 19.2.8), `Π(α², k) = Π(π/2, α², k)`
(a Cauchy principal value for real `α² > 1`). -/
@[dlmf 19.2.E8, dlmf 19.1.E1]
def compEllIntPik (α2 k : ℂ) : ℂ := incEllIntPik (π / 2) α2 k

/-! ### Complementary complete integrals (DLMF 19.2.8_1, 19.2.8_2, 19.2.9) -/

/-- Legendre's complementary complete integral of the first kind `K'(k)` (DLMF 19.2.8_1, 19.2.9):
the continuation of `∫₀¹ dt/(√(1-t²) √(1-(1-k²)t²)) = K(k')` from `k > 0` to `ℂ \ (-∞, 0]`
(branch point at `k = 0`, principal branch `|ph k| ≤ π`), given by (19.2.9):
`K'(k) = K(k')` for `|ph k| ≤ π/2` and `K'(k) = K(k') ∓ 2i K(-k)` for `π/2 < ±ph k < π`, where
`K(k') = compEllIntKpk k` is the literal integral. On the imaginary axis the value is the limit
from `Re k > 0`; on the cut `(-∞, 0)`, the limit from `Im k > 0`. -/
@[dlmf 19.2.E8_1]
def cCompEllIntKk (k : ℂ) : ℂ :=
  if 0 < k.re ∨ (k.re = 0 ∧ 0 ≤ k.im) then compEllIntKpk k
  else if 0 ≤ k.im then compEllIntKpk k - 2 * I * compEllIntKk (-k)
  else compEllIntKpk k + 2 * I * compEllIntKk (-k)

/-- Legendre's complementary complete integral of the second kind `E'(k)` (DLMF 19.2.8_2, 19.2.9):
the continuation of `∫₀¹ √(1-(1-k²)t²)/√(1-t²) dt = E(k')` from `k > 0` to `ℂ \ (-∞, 0]`, given by
`E'(k) = E(k')` for `|ph k| ≤ π/2` and `E'(k) = E(k') ∓ 2i (K(-k) - E(-k))` for
`π/2 < ±ph k < π`, with `k' = √(1-k²)` principal; boundary conventions as for `cCompEllIntKk`. -/
@[dlmf 19.2.E8_2]
def cCompEllIntEk (k : ℂ) : ℂ :=
  if 0 < k.re ∨ (k.re = 0 ∧ 0 ≤ k.im) then compEllIntEk (jacobiComodulusk k)
  else if 0 ≤ k.im then
    compEllIntEk (jacobiComodulusk k) - 2 * I * (compEllIntKk (-k) - compEllIntEk (-k))
  else compEllIntEk (jacobiComodulusk k) + 2 * I * (compEllIntKk (-k) - compEllIntEk (-k))

/-! ### Bulirsch's integrals (DLMF 19.2.11–19.2.16) -/

/-- Bulirsch's complete integral (DLMF 19.2.11),
`cel(k_c, p, a, b) = ∫₀^{π/2} (a cos²θ + b sin²θ)/(cos²θ + p sin²θ) · (cos²θ + k_c² sin²θ)^{-1/2} dθ`
for real `a, b, p` (`p ≠ 0`) and complex `k_c ≠ 0`; a Cauchy principal value when `p < 0`. -/
@[dlmf 19.2.E11]
def bulirschCel (kc : ℂ) (p a b : ℝ) : ℂ :=
  ei19a_pvSegmentIntegral (fun θ => Complex.cos θ ^ 2 + p * Complex.sin θ ^ 2)
    (fun θ => (a * Complex.cos θ ^ 2 + b * Complex.sin θ ^ 2) /
      (Complex.cos θ ^ 2 + p * Complex.sin θ ^ 2) *
        (Complex.cos θ ^ 2 + kc ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ))) (π / 2)

/-- Bulirsch's incomplete integral of the first kind (DLMF 19.2.11_5),
`el1(x, k_c) = ∫₀^{arctan x} (cos²θ + k_c² sin²θ)^{-1/2} dθ` along the segment, principal
`arctan` and square root. -/
@[dlmf 19.2.E11_5]
def bulirschEl1 (x kc : ℂ) : ℂ :=
  ei19a_segmentIntegral (fun θ => (Complex.cos θ ^ 2 + kc ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ)))
    (Complex.arctan x)

/-- Bulirsch's incomplete integral of the second kind (DLMF 19.2.12),
`el2(x, k_c, a, b) = ∫₀^{arctan x} (a + b tan²θ) ((1 + tan²θ)(1 + k_c² tan²θ))^{-1/2} dθ`, real
`a, b`. -/
@[dlmf 19.2.E12]
def bulirschEl2 (x kc : ℂ) (a b : ℝ) : ℂ :=
  ei19a_segmentIntegral (fun θ => (a + b * Complex.tan θ ^ 2) *
    ((1 + Complex.tan θ ^ 2) * (1 + kc ^ 2 * Complex.tan θ ^ 2)) ^ (-(1 / 2 : ℂ)))
    (Complex.arctan x)

/-- Bulirsch's incomplete integral of the third kind (DLMF 19.2.16),
`el3(x, k_c, p) = ∫₀^{arctan x} dθ / ((cos²θ + p sin²θ) √(cos²θ + k_c² sin²θ))`, real `p`,
`x² ≠ -1/p`; a principal value at an interior zero of `cos²θ + p sin²θ` (as for `Π`). -/
@[dlmf 19.2.E16]
def bulirschEl3 (x kc : ℂ) (p : ℝ) : ℂ :=
  ei19a_pvSegmentIntegral (fun θ => Complex.cos θ ^ 2 + p * Complex.sin θ ^ 2)
    (fun θ => (Complex.cos θ ^ 2 + p * Complex.sin θ ^ 2)⁻¹ *
      (Complex.cos θ ^ 2 + kc ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ))) (Complex.arctan x)

/-! ### Real-amplitude forms and bridges -/

/-- `F(φ, k)` for real `φ` is the interval integral `∫₀^φ (1 - k² sin²θ)^{-1/2} dθ`. -/
theorem incEllIntFk_ofReal_eq_integral (φ : ℝ) (k : ℂ) :
    incEllIntFk φ k = ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [incEllIntFk, ei19a_segmentIntegral_ofReal]
  simp only [← Complex.ofReal_sin]

/-- `E(φ, k)` for real `φ` is the interval integral `∫₀^φ (1 - k² sin²θ)^{1/2} dθ`. -/
theorem incEllIntEk_ofReal_eq_integral (φ : ℝ) (k : ℂ) :
    incEllIntEk φ k = ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
  rw [incEllIntEk, ei19a_segmentIntegral_ofReal]
  simp only [← Complex.ofReal_sin]

/-- `D(φ, k)` for real `φ` is the interval integral `∫₀^φ sin²θ (1 - k² sin²θ)^{-1/2} dθ`. -/
theorem incEllIntDk_ofReal_eq_integral (φ : ℝ) (k : ℂ) :
    incEllIntDk φ k = ∫ θ in (0 : ℝ)..φ,
      (Real.sin θ : ℂ) ^ 2 * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [incEllIntDk, ei19a_segmentIntegral_ofReal]
  simp only [← Complex.ofReal_sin]

/-- DLMF 19.2.8: `K(k) = F(π/2, k)`, bridging the Chapter 22 definition
`DLMF.JacobiElliptic.compEllIntKk` (all complex `k`). -/
@[dlmf 19.2.E8]
theorem compEllIntKk_eq_incEllIntFk (k : ℂ) : compEllIntKk k = incEllIntFk (π / 2) k := by
  rw [show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, incEllIntFk_ofReal_eq_integral,
    compEllIntKk]

/-- `E(k)` is the integral `∫₀^{π/2} (1 - k² sin²θ)^{1/2} dθ`. -/
theorem compEllIntEk_eq_integral (k : ℂ) :
    compEllIntEk k = ∫ θ in (0 : ℝ)..(π / 2), (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
  rw [compEllIntEk, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntEk_ofReal_eq_integral]

/-- `D(k)` is the integral `∫₀^{π/2} sin²θ (1 - k² sin²θ)^{-1/2} dθ`. -/
theorem compEllIntDk_eq_integral (k : ℂ) :
    compEllIntDk k = ∫ θ in (0 : ℝ)..(π / 2),
      (Real.sin θ : ℂ) ^ 2 * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [compEllIntDk, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntDk_ofReal_eq_integral]

/-- For a real exponent and a nonnegative real base the complex power is the real one. -/
lemma ei19a_ofReal_cpow_ofReal {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    ((x : ℂ) ^ (y : ℂ)) = ((x ^ y : ℝ) : ℂ) := (ofReal_cpow hx y).symm

/-- If `k² = m` with `m` real and `1 - m sin²θ ≥ 0`, the complex base is the real one. -/
lemma ei19a_base_ofReal {k : ℂ} {m : ℝ} (hk : k ^ 2 = m) (θ : ℝ) :
    1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 = ((1 - m * Real.sin θ ^ 2 : ℝ) : ℂ) := by
  rw [hk]; push_cast; ring

/-- Bridge to the real integral of the first kind: if `k² = m` is real with `m ≤ 1` and `φ` is
real, `F(φ, k) = Real.incEllIntFm φ m`. -/
theorem incEllIntFk_eq_ofReal {k : ℂ} {m : ℝ} (hk : k ^ 2 = m) (hm : m ≤ 1) (φ : ℝ) :
    incEllIntFk φ k = (DLMF.Elliptic.Real.incEllIntFm φ m : ℂ) := by
  rw [incEllIntFk_ofReal_eq_integral, DLMF.Elliptic.Real.incEllIntFm,
    ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hpos : 0 ≤ 1 - m * Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  rw [ei19a_base_ofReal hk, show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    ei19a_ofReal_cpow_ofReal hpos]

/-- Bridge to the real integral of the second kind: if `k² = m` is real with `m ≤ 1` and `φ` is
real, `E(φ, k) = Real.incEllIntEm φ m`. -/
theorem incEllIntEk_eq_ofReal {k : ℂ} {m : ℝ} (hk : k ^ 2 = m) (hm : m ≤ 1) (φ : ℝ) :
    incEllIntEk φ k = (DLMF.Elliptic.Real.incEllIntEm φ m : ℂ) := by
  rw [incEllIntEk_ofReal_eq_integral, DLMF.Elliptic.Real.incEllIntEm,
    ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hpos : 0 ≤ 1 - m * Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  rw [ei19a_base_ofReal hk, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ei19a_ofReal_cpow_ofReal hpos]

/-- Bridge to `lean-codes`: for real `φ` and real `k` with `k² ≤ 1`,
`F(φ, k) = Carlson.Real.incEllIntFk φ k`. -/
theorem incEllIntFk_ofReal {φ k : ℝ} (hk : k ^ 2 ≤ 1) :
    incEllIntFk φ k = (Carlson.Real.incEllIntFk φ k : ℂ) := by
  rw [incEllIntFk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk, DLMF.Elliptic.Real.incEllIntFm,
    Carlson.Real.incEllIntFk]
  norm_num

/-- Bridge to `lean-codes`: for real `φ` and real `k` with `k² ≤ 1`,
`E(φ, k) = Carlson.Real.incEllIntEk φ k`. -/
theorem incEllIntEk_ofReal {φ k : ℝ} (hk : k ^ 2 ≤ 1) :
    incEllIntEk φ k = (Carlson.Real.incEllIntEk φ k : ℂ) := by
  rw [incEllIntEk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk, DLMF.Elliptic.Real.incEllIntEm,
    Carlson.Real.incEllIntEk]

/-- Bridge for the complete integral of the first kind: if `k² = m` is real, `m ≤ 1`,
`K(k) = Real.compEllIntKm m`. -/
theorem compEllIntKk_eq_ofReal {k : ℂ} {m : ℝ} (hk : k ^ 2 = m) (hm : m ≤ 1) :
    compEllIntKk k = (DLMF.Elliptic.Real.compEllIntKm m : ℂ) := by
  rw [compEllIntKk_eq_incEllIntFk, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntFk_eq_ofReal hk hm, DLMF.Elliptic.Real.incEllIntFm_pi_div_two]

/-- Bridge for the complete integral of the second kind: if `k² = m` is real, `m ≤ 1`,
`E(k) = Real.compEllIntEm m`. -/
theorem compEllIntEk_eq_ofReal {k : ℂ} {m : ℝ} (hk : k ^ 2 = m) (hm : m ≤ 1) :
    compEllIntEk k = (DLMF.Elliptic.Real.compEllIntEm m : ℂ) := by
  rw [compEllIntEk, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntEk_eq_ofReal hk hm, DLMF.Elliptic.Real.incEllIntEm_pi_div_two]

/-- Bridge to `lean-codes`: `K(k) = Carlson.Real.compEllIntKk k` for real `k`, `k² ≤ 1`. -/
theorem compEllIntKk_ofReal_carlson {k : ℝ} (hk : k ^ 2 ≤ 1) :
    compEllIntKk k = (Carlson.Real.compEllIntKk k : ℂ) := by
  rw [compEllIntKk_eq_incEllIntFk, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntFk_ofReal hk, Carlson.Real.compEllIntKk]

/-- Bridge to `lean-codes`: `E(k) = Carlson.Real.compEllIntEk k` for real `k`, `k² ≤ 1`. -/
theorem compEllIntEk_ofReal {k : ℝ} (hk : k ^ 2 ≤ 1) :
    compEllIntEk k = (Carlson.Real.compEllIntEk k : ℂ) := by
  rw [compEllIntEk, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntEk_ofReal hk, Carlson.Real.compEllIntEk]

/-- `Π(φ, α², k)` is the ordinary segment integral when `1 - α² sin²θ` is bounded away from `0`
on the path. -/
theorem incEllIntPik_eq_segmentIntegral {φ α2 k : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖1 - α2 * Complex.sin (t * φ) ^ 2‖) :
    incEllIntPik φ α2 k = ei19a_segmentIntegral
      (fun θ => (1 - α2 * Complex.sin θ ^ 2)⁻¹ * (1 - k ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ)))
        φ :=
  ei19a_pvSegmentIntegral_eq hδ h

/-- For real `φ` and real `α² < 1` the principal value in `Π` is not needed:
`Π(φ, α², k) = ∫₀^φ (1 - α² sin²θ)⁻¹ (1 - k² sin²θ)^{-1/2} dθ`. -/
theorem incEllIntPik_ofReal_eq_integral (φ : ℝ) {α2 : ℝ} (hα : α2 < 1) (k : ℂ) :
    incEllIntPik φ α2 k = ∫ θ in (0 : ℝ)..φ, ((1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
  rw [incEllIntPik_eq_segmentIntegral (δ := min 1 (1 - α2)) (lt_min one_pos (by linarith)),
    ei19a_segmentIntegral_ofReal]
  · simp only [← Complex.ofReal_sin]
  · intro t _
    have hs := Real.sin_sq_le_one (t * φ)
    have hs0 := sq_nonneg (Real.sin (t * φ))
    have hre : (1 - (α2 : ℂ) * Complex.sin (t * φ) ^ 2) =
        ((1 - α2 * Real.sin (t * φ) ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hre, Complex.norm_real, Real.norm_eq_abs]
    have hpos : min 1 (1 - α2) ≤ 1 - α2 * Real.sin (t * φ) ^ 2 := by
      rcases le_or_gt α2 0 with h | h
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
    exact hpos.trans (le_abs_self _)

/-- Bridge to the real integral of the third kind: for real `φ`, real `α² < 1` and `k² = m` real
with `m ≤ 1`, `Π(φ, α², k) = Real.incEllIntPim φ α² m`. -/
theorem incEllIntPik_eq_ofReal {k : ℂ} {m α2 : ℝ} (hk : k ^ 2 = m) (hm : m ≤ 1) (hα : α2 < 1)
    (φ : ℝ) : incEllIntPik φ α2 k = (DLMF.Elliptic.Real.incEllIntPim φ α2 m : ℂ) := by
  rw [incEllIntPik_ofReal_eq_integral φ hα, DLMF.Elliptic.Real.incEllIntPim,
    ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hpos : 0 ≤ 1 - m * Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  simp only [DLMF.Elliptic.piIntegrand]
  rw [ei19a_base_ofReal hk, show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    ei19a_ofReal_cpow_ofReal hpos]
  push_cast; ring

/-- Bridge to `lean-codes`: for real `φ`, real `α² < 1` and real `k` with `k² ≤ 1`,
`Π(φ, α², k) = Carlson.Real.incEllIntPik φ α² k`. -/
theorem incEllIntPik_ofReal {φ α2 k : ℝ} (hα : α2 < 1) (hk : k ^ 2 ≤ 1) :
    incEllIntPik φ α2 k = (Carlson.Real.incEllIntPik φ α2 k : ℂ) := by
  rw [incEllIntPik_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk hα,
    DLMF.Elliptic.Real.incEllIntPim, Carlson.Real.incEllIntPik]
  simp only [DLMF.Elliptic.piIntegrand]
  norm_num

/-- `K(k') = K'` literal: `compEllIntKk (k') = compEllIntKpk k` for the principal `k' = √(1-k²)`. -/
theorem compEllIntKk_jacobiComodulusk (k : ℂ) :
    compEllIntKk (jacobiComodulusk k) = compEllIntKpk k := by
  have h : jacobiComodulusk k ^ 2 = 1 - k ^ 2 := by
    rw [jacobiComodulusk, one_div, Complex.cpow_ofNat_inv_pow]
  simp only [compEllIntKk, compEllIntKpk, h]

/-- DLMF 19.2.9, first case: `K'(k) = K(k')` and `E'(k) = E(k')` for `Re k > 0` (and on the upper
imaginary axis, the limit from `Re k > 0`). -/
@[dlmf 19.2.E9]
theorem cCompEllIntKk_of_re_pos {k : ℂ} (hk : 0 < k.re ∨ (k.re = 0 ∧ 0 ≤ k.im)) :
    cCompEllIntKk k = compEllIntKk (jacobiComodulusk k) ∧
      cCompEllIntEk k = compEllIntEk (jacobiComodulusk k) := by
  simp only [cCompEllIntKk, cCompEllIntEk, hk, ↓reduceIte, compEllIntKk_jacobiComodulusk, and_self]

/-- DLMF 19.2.9, second case: for `π/2 < ph k < π`, `K'(k) = K(k') - 2i K(-k)` and
`E'(k) = E(k') - 2i (K(-k) - E(-k))`. -/
@[dlmf 19.2.E9]
theorem cCompEllIntKk_of_re_neg_of_im_pos {k : ℂ} (hre : k.re < 0) (him : 0 < k.im) :
    cCompEllIntKk k = compEllIntKk (jacobiComodulusk k) - 2 * I * compEllIntKk (-k) ∧
      cCompEllIntEk k = compEllIntEk (jacobiComodulusk k) -
        2 * I * (compEllIntKk (-k) - compEllIntEk (-k)) := by
  simp only [cCompEllIntKk, cCompEllIntEk, not_lt.2 hre.le, hre.ne, him.le, false_or, false_and,
    ↓reduceIte, compEllIntKk_jacobiComodulusk, and_self]

/-- DLMF 19.2.9, third case: for `-π < ph k < -π/2`, `K'(k) = K(k') + 2i K(-k)` and
`E'(k) = E(k') + 2i (K(-k) - E(-k))`. -/
@[dlmf 19.2.E9]
theorem cCompEllIntKk_of_re_neg_of_im_neg {k : ℂ} (hre : k.re < 0) (him : k.im < 0) :
    cCompEllIntKk k = compEllIntKk (jacobiComodulusk k) + 2 * I * compEllIntKk (-k) ∧
      cCompEllIntEk k = compEllIntEk (jacobiComodulusk k) +
        2 * I * (compEllIntKk (-k) - compEllIntEk (-k)) := by
  simp only [cCompEllIntKk, cCompEllIntEk, not_lt.2 hre.le, hre.ne, not_le.2 him, false_or,
    ↓reduceIte, compEllIntKk_jacobiComodulusk, and_self]

end DLMF.EllipticIntegrals
