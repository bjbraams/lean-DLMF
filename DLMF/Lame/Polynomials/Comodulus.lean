/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.Series

/-!
# Lamé eigenvalues of complementary modulus (DLMF 29.3.7, 29.3.8)

For a nonnegative integer order `n` the eigenvalues of modulus `k` and of the complementary
modulus `k' = √(1 - k²)` are related by `a^m_n(k²) + a^{n-m}_n(k'²) = n(n+1)` and
`b^m_n(k²) + b^{n-m+1}_n(k'²) = n(n+1)`.

## Main results

* `lameEigenvalue_comodulus_lamePolynomialType`: along `K + i[0, K']` the Lamé polynomial
  `lamePolynomialE t n j` is the `(n - j)`th eigenfunction of the problem of modulus `k'`.
* `Real.lameA_add_lameA_comodulus`, `Real.lameB_add_lameB_comodulus`: DLMF 29.3.7, 29.3.8.

## Implementation notes

The Lamé polynomial `E` of type `t` has eigenvalue `h = ½(H_j + ν(ν+1)k²)`. Along the vertical
side, `g(y) = E(K + iy)` solves `g'' = (V(y) + h) g` with
`V(y) = -ν(ν+1)k²/dn²(y, k') = ν(ν+1)k'² sn²(K' - y, k') - ν(ν+1)`
(`lamePolynomialE_vertical_spectrum`), so `x ↦ g(K' - x)` solves Lamé's equation of modulus `k'`
with eigenvalue `ν(ν+1) - h` and has `n - j` zeros in `(0, K')`; Sturm's oscillation theorem
identifies the eigenvalue.
-/

@[expose] public section

open Set Complex DLMF.JacobiElliptic DLMF.Elliptic

noncomputable section

namespace DLMF.Lame

variable {k : ℝ}

/-- Reflection `x ↦ L - x` of a Sturm–Liouville solution. -/
private lemma isSturmLiouvilleSolution_reflect {W : ℝ → ℝ} {μ L : ℝ} {w : ℝ → ℝ}
    (hw : ODE.IsSturmLiouvilleSolution W μ w) :
    ODE.IsSturmLiouvilleSolution (fun x => W (L - x)) μ (fun x => w (L - x)) ∧
      ∀ x, deriv (fun x => w (L - x)) x = -deriv w (L - x) := by
  have hr : ∀ x : ℝ, HasDerivAt (fun x : ℝ => L - x) (-1) x := fun x => by
    simpa using (hasDerivAt_id x).const_sub L
  have d1 : ∀ x, HasDerivAt (fun x => w (L - x)) (-deriv w (L - x)) x := fun x =>
    (HasDerivAt.comp (h₂ := w) (h := fun x : ℝ => L - x) x (hw.1 (L - x)).hasDerivAt
      (hr x)).congr_deriv (by ring)
  have e : deriv (fun x => w (L - x)) = fun x => -deriv w (L - x) := funext fun x => (d1 x).deriv
  refine ⟨⟨fun x => (d1 x).differentiableAt, fun x => ?_⟩, fun x => (d1 x).deriv⟩
  rw [e]
  exact (HasDerivAt.comp (h₂ := deriv w) (h := fun x : ℝ => L - x) x (hw.2 (L - x))
    (hr x)).neg.congr_deriv (by ring)

/-- The spectrum of the reflected and shifted potential `V(L - y) - c`. -/
private lemma mem_separatedSpectrum_reflect {V : ℝ → ℝ} {L c μ : ℝ} {a b : Bool} :
    μ ∈ ODE.separatedSpectrum (fun y => V (L - y) - c) L a b ↔
      μ + c ∈ ODE.separatedSpectrum V L b a := by
  constructor
  · rintro ⟨w, hw, ⟨h0, hL⟩, hne⟩
    have hw' : ODE.IsSturmLiouvilleSolution (fun y => V (L - y)) (μ + c) w :=
      ⟨hw.1, fun x => (hw.2 x).congr_deriv (by ring)⟩
    obtain ⟨hu, hd⟩ := isSturmLiouvilleSolution_reflect (L := L) hw'
    refine ⟨fun x => w (L - x), ⟨hu.1, fun x => (hu.2 x).congr_deriv (by simp)⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [hd]; cases b <;> simp_all
    · rw [hd]; cases a <;> simp_all
    · intro h0'
      apply hne
      funext x
      have := congrFun h0' (L - x)
      simpa using this
  · rintro ⟨u, hu, ⟨h0, hL⟩, hne⟩
    obtain ⟨hw, hd⟩ := isSturmLiouvilleSolution_reflect (L := L) hu
    refine ⟨fun x => u (L - x), ⟨hw.1, fun x => (hw.2 x).congr_deriv (by ring)⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [hd]; cases a <;> simp_all
    · rw [hd]; cases b <;> simp_all
    · intro h0'
      apply hne
      funext x
      have := congrFun h0' (L - x)
      simpa using this


/-- The vertical potential is the reflected Lamé potential of modulus `k' = √(1 - k²)`, shifted:
`-ν(ν+1)k²/dn²(y, k') = ν(ν+1)k'² sn²(K' - y, k') - ν(ν+1)`. -/
private lemma verticalPotential_eq (hk0 : 0 < k) (hk1 : k < 1) (ν y : ℝ) :
    verticalPotential ν k y = lamePotential ν (Real.sqrt (1 - k ^ 2))
      (Real.completeEllipticKOfParameter (1 - k ^ 2) - y) - ν * (ν + 1) := by
  have hm : 1 - k ^ 2 < 1 := by nlinarith
  have hs : Real.sqrt (1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by nlinarith)
  have e := (Real.jacobi_add_completeEllipticKOfParameter hm (-y)).1
  rw [(jacobi_neg hm y).2.1, (jacobi_neg hm y).2.2, neg_add_eq_sub] at e
  have hd := Real.jacobiDnOfParameter_pos hm y
  have h1 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm y
  have h2 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq y (1 - k ^ 2)
  rw [verticalPotential, lamePotential, hs, e]
  field_simp
  linear_combination (-(ν * (ν + 1))) * ((1 - k ^ 2) * h2 - h1)


/-- **The comodulus eigenvalue of a Lamé polynomial.** Along the vertical side the Lamé
polynomial `lamePolynomialE t n j` is, after `y ↦ K' - y`, the `(n - j)`th eigenfunction of the
Lamé problem of modulus `k' = √(1 - k²)` with the boundary types `lamePolyOddKiK t` at `0` and
`lamePolyOddK t` at `K'`, with eigenvalue `ν(ν+1) - ½(H_j + ν(ν+1)k²)`. -/
theorem lameEigenvalue_comodulus_lamePolynomialType (hk0 : 0 < k) (hk1 : k < 1)
    (t : LamePolynomialType)
    {n j : ℕ} (hj : j ≤ n) :
    Real.lameEigenvalue (t.order n : ℝ) (Real.sqrt (1 - k ^ 2)) (lamePolyOddKiK t)
        (lamePolyOddK t) (n - j) =
      (t.order n : ℝ) * ((t.order n : ℝ) + 1) -
        (lamePolynomialH t n j k + (t.order n : ℝ) * ((t.order n : ℝ) + 1) * k ^ 2) / 2 := by
  set ν : ℝ := (t.order n : ℝ)
  set c : ℝ := ν * (ν + 1)
  set hv : ℝ := (lamePolynomialH t n j k + ν * (ν + 1) * k ^ 2) / 2
  set L := Real.completeEllipticKOfParameter (1 - k ^ 2)
  obtain ⟨hk0', hk1', hk2'⟩ := comodulus_mem_Ioo hk0 hk1
  set k' := Real.sqrt (1 - k ^ 2)
  have hL : 0 < L := Real.completeEllipticKOfParameter_pos (by nlinarith)
  obtain ⟨hmem, hcnt⟩ := lamePolynomialE_vertical_spectrum hk0 hk1 t hj
  set Sv := ODE.separatedSpectrum (verticalPotential ν k) L (lamePolyOddK t) (lamePolyOddKiK t)
  set SL := Real.lameSpectrum ν k' (lamePolyOddKiK t) (lamePolyOddK t)
  have hSL : SL = ODE.separatedSpectrum (lamePotential ν k') L (lamePolyOddKiK t)
      (lamePolyOddK t) := by
    simp only [SL, L]; rw [lameSpectrum_eq_separatedSpectrum, hk2']
  have hVfun : verticalPotential ν k = fun y => lamePotential ν k' (L - y) - c :=
    funext fun y => verticalPotential_eq hk0 hk1 ν y
  have hiff : ∀ μ, μ ∈ Sv ↔ μ + c ∈ SL := fun μ => by
    rw [hSL]; simp only [Sv]; rw [hVfun]; exact mem_separatedSpectrum_reflect
  have himg : SL ∩ Iio (-hv + c) = (fun μ => μ + c) '' (Sv ∩ Iio (-hv)) := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_image]
    constructor
    · rintro ⟨hx, hlt⟩
      exact ⟨x - c, ⟨(hiff _).2 (by simpa using hx), by linarith⟩, by ring⟩
    · rintro ⟨μ, ⟨hμ, hlt⟩, rfl⟩
      exact ⟨(hiff μ).1 hμ, by linarith⟩
  have hfin : (SL ∩ Iio (-hv + c)).Finite := by
    rw [hSL]
    exact ODE.separatedSpectrum_inter_Iio_finite (continuous_lamePotential (by nlinarith))
      abs_lamePotential_le hL _ _ _
  have hnth : Real.IsNthLameEigenvalue ν k' (lamePolyOddKiK t) (lamePolyOddK t) (n - j)
      (-hv + c) := by
    refine ⟨(hiff _).1 hmem, hfin, ?_⟩
    rw [himg, Set.ncard_image_of_injective _ (add_left_injective c)]
    exact hcnt
  have := ((Real.lameEigenvalue_spec (ν := ν) hk0' hk1' (lamePolyOddKiK t)
    (lamePolyOddK t)).1 (n - j)).unique
    (Real.isNthLameEigenvalue_lameEigenvalue hk0' hk1' _ _ _) hnth
  rw [this]; ring


/-- 29.3.7: for a nonnegative integer `ν = n`, `a^m_n(k²) + a^{n-m}_n(1 - k²) = n(n+1)`,
`m = 0, 1, …, n` (the second eigenvalue has modulus `k' = √(1 - k²)`). Proved from the
Lamé polynomials: `a^m_n(k)` is the eigenvalue of a Lamé polynomial of type `uE`, `sE`, `dE`
or `sdE`, which along `K + i[0, K']` is the eigenfunction for `n(n+1) - a^m_n(k)` of the
problem of modulus `k'` with `n - m` as superscript (`lameEigenvalue_comodulus_lamePolynomialType`).
-/
@[dlmf 29.3.E7]
theorem Real.lameA_add_lameA_comodulus (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm : m ≤ n) :
    Real.lameA n m k + Real.lameA n (n - m) (Real.sqrt (1 - k ^ 2)) = n * (n + 1) := by
  rcases Nat.even_or_odd' n with ⟨N, rfl | rfl⟩ <;> rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · have h1 := Real.lameA_eq_lamePolynomialH_uE hk0 hk1 (n := N) (m := j) (by omega)
    have h2 := lameEigenvalue_comodulus_lamePolynomialType hk0 hk1 .uE (n := N) (j := j) (by omega)
    have h3 : Real.lameA ((2 * N : ℕ) : ℝ) (2 * N - 2 * j) (Real.sqrt (1 - k ^ 2)) =
        Real.lameEigenvalue ((LamePolynomialType.uE.order N : ℕ) : ℝ) (Real.sqrt (1 - k ^ 2))
          (lamePolyOddKiK .uE) (lamePolyOddK .uE) (N - j) := by
      rw [Real.lameA, show 2 * N - 2 * j = 2 * (N - j) by omega]
      simp [Nat.bodd_mul, LamePolynomialType.order, lamePolyOddKiK, lamePolyOddK]
    rw [h1, h3, h2]; simp only [LamePolynomialType.order]; push_cast; ring
  · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [show 2 * (N' + 1) = 2 * N' + 2 by ring] at hm ⊢
    have h1 := Real.lameA_eq_lamePolynomialH_sdE hk0 hk1 (n := N') (m := j) (by omega)
    have h2 := lameEigenvalue_comodulus_lamePolynomialType hk0 hk1 .sdE (n := N')
        (j := j) (by omega)
    have h3 : Real.lameA ((2 * N' + 2 : ℕ) : ℝ) (2 * N' + 2 - (2 * j + 1))
        (Real.sqrt (1 - k ^ 2)) =
        Real.lameEigenvalue ((LamePolynomialType.sdE.order N' : ℕ) : ℝ) (Real.sqrt (1 - k ^ 2))
          (lamePolyOddKiK .sdE) (lamePolyOddK .sdE) (N' - j) := by
      rw [Real.lameA, show 2 * N' + 2 - (2 * j + 1) = 2 * (N' - j) + 1 by omega]
      simp [Nat.bodd_mul, LamePolynomialType.order, lamePolyOddKiK, lamePolyOddK]
      congr 1; omega
    rw [h1, h3, h2]; simp only [LamePolynomialType.order]; push_cast; ring
  · have h1 := Real.lameA_eq_lamePolynomialH_dE hk0 hk1 (n := N) (m := j) (by omega)
    have h2 := lameEigenvalue_comodulus_lamePolynomialType hk0 hk1 .dE (n := N) (j := j) (by omega)
    have h3 : Real.lameA ((2 * N + 1 : ℕ) : ℝ) (2 * N + 1 - 2 * j) (Real.sqrt (1 - k ^ 2)) =
        Real.lameEigenvalue ((LamePolynomialType.dE.order N : ℕ) : ℝ) (Real.sqrt (1 - k ^ 2))
          (lamePolyOddKiK .dE) (lamePolyOddK .dE) (N - j) := by
      rw [Real.lameA, show 2 * N + 1 - 2 * j = 2 * (N - j) + 1 by omega]
      simp [Nat.bodd_mul, LamePolynomialType.order, lamePolyOddKiK, lamePolyOddK]
      congr 1; omega
    rw [h1, h3, h2]; simp only [LamePolynomialType.order]; push_cast; ring
  · have h1 := Real.lameA_eq_lamePolynomialH_sE hk0 hk1 (n := N) (m := j) (by omega)
    have h2 := lameEigenvalue_comodulus_lamePolynomialType hk0 hk1 .sE (n := N) (j := j) (by omega)
    have h3 : Real.lameA ((2 * N + 1 : ℕ) : ℝ) (2 * N + 1 - (2 * j + 1))
        (Real.sqrt (1 - k ^ 2)) =
        Real.lameEigenvalue ((LamePolynomialType.sE.order N : ℕ) : ℝ) (Real.sqrt (1 - k ^ 2))
          (lamePolyOddKiK .sE) (lamePolyOddK .sE) (N - j) := by
      rw [Real.lameA, show 2 * N + 1 - (2 * j + 1) = 2 * (N - j) by omega]
      simp [Nat.bodd_mul, LamePolynomialType.order, lamePolyOddKiK, lamePolyOddK]
    rw [h1, h3, h2]; simp only [LamePolynomialType.order]; push_cast; ring


/-- 29.3.8: for a nonnegative integer `ν = n`, `b^m_n(k²) + b^{n-m+1}_n(1 - k²) = n(n+1)`,
`m = 1, …, n`. Proved like 29.3.7 from the Lamé polynomials of types `cE`, `scE`, `cdE`,
`scdE` (`lameEigenvalue_comodulus_lamePolynomialType`). -/
@[dlmf 29.3.E8]
theorem Real.lameB_add_lameB_comodulus (hk0 : 0 < k) (hk1 : k < 1) {n m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ n) :
    Real.lameB n m k + Real.lameB n (n - m + 1) (Real.sqrt (1 - k ^ 2)) = n * (n + 1) := by
  rcases Nat.even_or_odd' n with ⟨N, rfl | rfl⟩ <;> rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show 2 * (N' + 1) = 2 * N' + 2 by ring, show 2 * (j + 1) = 2 * j + 2 by ring] at hm ⊢
    have h1 := Real.lameB_eq_lamePolynomialH_scE hk0 hk1 (n := N') (m := j) (by omega)
    have h2 := lameEigenvalue_comodulus_lamePolynomialType hk0 hk1 .scE (n := N')
        (j := j) (by omega)
    have h3 : Real.lameB ((2 * N' + 2 : ℕ) : ℝ) (2 * N' + 2 - (2 * j + 2) + 1)
        (Real.sqrt (1 - k ^ 2)) =
        Real.lameEigenvalue ((LamePolynomialType.scE.order N' : ℕ) : ℝ) (Real.sqrt (1 - k ^ 2))
          (lamePolyOddKiK .scE) (lamePolyOddK .scE) (N' - j) := by
      rw [Real.lameB, show 2 * N' + 2 - (2 * j + 2) + 1 = 2 * (N' - j) + 1 by omega]
      simp [Nat.bodd_mul, LamePolynomialType.order, lamePolyOddKiK, lamePolyOddK]
    rw [h1, h3, h2]; simp only [LamePolynomialType.order]; push_cast; ring
  · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [show 2 * (N' + 1) = 2 * N' + 2 by ring] at hm ⊢
    have h1 := Real.lameB_eq_lamePolynomialH_cdE hk0 hk1 (n := N') (m := j) (by omega)
    have h2 := lameEigenvalue_comodulus_lamePolynomialType hk0 hk1 .cdE (n := N')
        (j := j) (by omega)
    have h3 : Real.lameB ((2 * N' + 2 : ℕ) : ℝ) (2 * N' + 2 - (2 * j + 1) + 1)
        (Real.sqrt (1 - k ^ 2)) =
        Real.lameEigenvalue ((LamePolynomialType.cdE.order N' : ℕ) : ℝ) (Real.sqrt (1 - k ^ 2))
          (lamePolyOddKiK .cdE) (lamePolyOddK .cdE) (N' - j) := by
      rw [Real.lameB, show 2 * N' + 2 - (2 * j + 1) + 1 = 2 * (N' - j) + 2 by omega]
      simp [Nat.bodd_mul, LamePolynomialType.order, lamePolyOddKiK, lamePolyOddK]
      congr 1; omega
    rw [h1, h3, h2]; simp only [LamePolynomialType.order]; push_cast; ring
  · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show 2 * (N' + 1) + 1 = 2 * N' + 3 by ring, show 2 * (j + 1) = 2 * j + 2 by ring] at hm ⊢
    have h1 := Real.lameB_eq_lamePolynomialH_scdE hk0 hk1 (n := N') (m := j) (by omega)
    have h2 := lameEigenvalue_comodulus_lamePolynomialType hk0 hk1 .scdE (n := N')
        (j := j) (by omega)
    have h3 : Real.lameB ((2 * N' + 3 : ℕ) : ℝ) (2 * N' + 3 - (2 * j + 2) + 1)
        (Real.sqrt (1 - k ^ 2)) =
        Real.lameEigenvalue ((LamePolynomialType.scdE.order N' : ℕ) : ℝ) (Real.sqrt (1 - k ^ 2))
          (lamePolyOddKiK .scdE) (lamePolyOddK .scdE) (N' - j) := by
      rw [Real.lameB, show 2 * N' + 3 - (2 * j + 2) + 1 = 2 * (N' - j) + 2 by omega]
      simp [Nat.bodd_mul, LamePolynomialType.order, lamePolyOddKiK, lamePolyOddK]
      congr 1; omega
    rw [h1, h3, h2]; simp only [LamePolynomialType.order]; push_cast; ring
  · have h1 := Real.lameB_eq_lamePolynomialH_cE hk0 hk1 (n := N) (m := j) (by omega)
    have h2 := lameEigenvalue_comodulus_lamePolynomialType hk0 hk1 .cE (n := N) (j := j) (by omega)
    have h3 : Real.lameB ((2 * N + 1 : ℕ) : ℝ) (2 * N + 1 - (2 * j + 1) + 1)
        (Real.sqrt (1 - k ^ 2)) =
        Real.lameEigenvalue ((LamePolynomialType.cE.order N : ℕ) : ℝ) (Real.sqrt (1 - k ^ 2))
          (lamePolyOddKiK .cE) (lamePolyOddK .cE) (N - j) := by
      rw [Real.lameB, show 2 * N + 1 - (2 * j + 1) + 1 = 2 * (N - j) + 1 by omega]
      simp [Nat.bodd_mul, LamePolynomialType.order, lamePolyOddKiK, lamePolyOddK]
    rw [h1, h3, h2]; simp only [LamePolynomialType.order]; push_cast; ring

end DLMF.Lame
