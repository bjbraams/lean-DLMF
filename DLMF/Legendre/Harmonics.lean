/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.IntegerTheory
public import DLMF.Legendre.Integrals
public import DLMF.Legendre.SpecialValues
public import DLMF.SphericalHarmonics.AdditionTools

/-!
# Normalized spherical harmonics and endpoint values

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

open DLMF.OrthogonalPolynomials

/-- Polynomial definition extends integral-degree Ferrers P continuously to both endpoints. -/
def ferrersPNat (l m : ℕ) (x : ℝ) : ℂ :=
  (-1)^m*(Real.sqrt (1-x^2):ℂ)^m*iteratedDeriv m (legendrePolyP l) x

/-- DLMF 14.7.8: for natural `l, m` and `-1 < x < 1`, the explicit form `(-1)^m (1-x²)^{m/2} d^m
P_l(x)/dx^m` agrees with the Ferrers function `𝖯^m_l(x)`. -/
@[dlmf 14.7.E8]
theorem ferrersPNat_eq (l m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersPNat l m x=ferrersP l m x := by
  have hs : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  have hev : legendreP (l:ℂ) =ᶠ[𝓝 (x:ℂ)] legendrePolyP l := by
    filter_upwards [isOpen_one_add_mem_slitPlane.mem_nhds hs] with w hw
    rw [legendreP_nat l hw]
  rw [ferrersP_nat (l:ℂ) m hx, hev.iteratedDeriv_eq, ferrersPNat]
  have h1 : 0 ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  congr 2
  rw [← Complex.ofReal_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h1]
  congr 2; ring

/-- DLMF 14.30.1 for `m ≥ 0`: the spherical harmonic `Y_{l,m}(θ, φ) = √((l-m)! (2l+1)/(4π (l+m)!))
e^{imφ} 𝖯^m_l(cos θ)`. -/
@[dlmf 14.30.E1]
def sphericalHarmonicNonneg (l m : ℕ) (θ phi : ℝ) : ℂ :=
  Real.sqrt (((l-m).factorial:ℝ)*(2*l+1)/(4*π*(l+m).factorial))*exp (I*m*phi)*ferrersPNat l m (Real.cos θ)

/-- DLMF 14.30.1: the spherical harmonic `Y_{l,m}(θ, φ)` for integer `m`, equal to
`sphericalHarmonicNonneg l m` for `m ≥ 0`, to `(-1)^{|m|}` times the complex conjugate of
`Y_{l,|m|}` for `m < 0`, and to `0` when `|m| > l`. -/
@[dlmf 14.30.E1]
def sphericalHarmonic (l : ℕ) (m : ℤ) (θ phi : ℝ) : ℂ :=
  if l < m.natAbs then 0 else if m < 0 then (-1)^m.natAbs*star (sphericalHarmonicNonneg l m.natAbs θ phi) else sphericalHarmonicNonneg l m.natAbs θ phi

/-- Derivatives of the Legendre polynomial are real on the real axis. -/
theorem iteratedDeriv_legendrePolyP_ofReal (l m : ℕ) (x : ℝ) :
    iteratedDeriv m (legendrePolyP l) (x:ℂ) =
      (((Polynomial.derivative^[m] (legendrePolyR l)).eval x : ℝ) : ℂ) := by
  have hf : legendrePolyP l = fun z => ((legendrePolyR l).map ofRealHom).eval z :=
    funext (legendrePolyP_eq_eval l)
  rw [hf, iteratedDeriv_eval_polynomial, Polynomial.iterate_derivative_map]
  exact eval_ofReal_map_ofRealHom _ _

/-- The polynomial Ferrers function is real-valued. -/
theorem star_ferrersPNat (l m : ℕ) (x : ℝ) : star (ferrersPNat l m x) = ferrersPNat l m x := by
  rw [ferrersPNat, iteratedDeriv_legendrePolyP_ofReal]
  simp only [star_mul', star_pow, star_neg, star_one, Complex.star_def, Complex.conj_ofReal]

/-- DLMF 14.30.1: for `|m| ≤ l` (`m` of either sign) and `0 < θ < π`, `Y_{l,m}(θ, φ) = √((l-m)!
(2l+1)/(4π (l+m)!)) e^{imφ} 𝖯^m_l(cos θ)`. -/
@[dlmf 14.30.E1]
theorem sphericalHarmonic_ferrers (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) (phi : ℝ) :
    sphericalHarmonic l m θ phi=Real.sqrt ((((l:ℤ)-m).toNat.factorial:ℝ)*(2*l+1)/(4*π*((l:ℤ)+m).toNat.factorial))*exp (I*m*phi)*ferrersP l m (Real.cos θ) := by
  have hx : Real.cos θ ∈ Ioo (-1:ℝ) 1 := by
    constructor
    · rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ
    · rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) h0
  rw [sphericalHarmonic, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.2 hm))]
  split_ifs with hneg
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -(k:ℤ) := ⟨m.natAbs, by omega⟩
    subst hk
    have hkl : k ≤ l := by simpa using hm
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rw [show ((l:ℤ) - -(k:ℤ)).toNat = l + k by omega, show ((l:ℤ) + -(k:ℤ)).toNat = l - k by omega]
    have hG : ∀ n : ℕ, (l:ℂ) - k + 1 ≠ -n := by
      intro n h
      have : ((l - k + 1 + n : ℕ) : ℂ) = 0 := by push_cast [Nat.cast_sub hkl]; linear_combination h
      exact absurd (Nat.cast_eq_zero.1 this) (by omega)
    have hR := ferrersP_negative_integer_order (l:ℂ) k hG hx
    push_cast
    rw [hR, sphericalHarmonicNonneg, ← ferrersPNat_eq l k hx]
    have e1 : (l:ℂ) - k + 1 = ((l - k : ℕ) : ℂ) + 1 := by push_cast [Nat.cast_sub hkl]; ring
    have e2 : (l:ℂ) + k + 1 = ((l + k : ℕ) : ℂ) + 1 := by push_cast; ring
    rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial]
    simp only [star_mul', star_ferrersPNat, Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj]
    set a : ℝ := ((l-k).factorial : ℝ)
    set b : ℝ := ((l+k).factorial : ℝ)
    have ha : 0 < a := by positivity
    have hb : 0 < b := by positivity
    have hc : 0 < (2*(l:ℝ)+1)/(4*π) := by positivity
    have hsq : Real.sqrt (a*(2*l+1)/(4*π*b)) = Real.sqrt (b*(2*l+1)/(4*π*a)) * (a/b) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ a/b), ← Real.sqrt_mul (by positivity)]
      congr 1; field_simp
    rw [hsq]
    have hconj : (starRingEnd ℂ) (I*(k:ℂ)*(phi:ℂ)) = I*(-(k:ℂ))*phi := by
      simp [Complex.conj_ofReal]
    rw [hconj]
    push_cast
    simp only [a, b, Complex.ofReal_natCast]; ring
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = (k:ℤ) := ⟨m.natAbs, by omega⟩
    subst hk
    simp only [Int.natAbs_natCast]
    rw [show ((l:ℤ) - (k:ℤ)).toNat = l - k by omega, show ((l:ℤ) + (k:ℤ)).toNat = l + k by omega,
      sphericalHarmonicNonneg, ferrersPNat_eq l k hx]
    push_cast; ring_nf

/-- DLMF 14.30.2: the real surface harmonic of the first kind `cos(mφ) 𝖯^m_l(cos θ)` (or `sin(mφ)
𝖯^m_l(cos θ)` when `sine` is true), for natural `l, m`. -/
@[dlmf 14.30.E2]
def surfaceHarmonic (sine : Bool) (l m : ℕ) (θ phi : ℝ) : ℂ :=
  (if sine then Real.sin (m*phi) else Real.cos (m*phi))*ferrersPNat l m (Real.cos θ)

/-- Derivatives of order `< n` of `(z²-1)ⁿ` vanish at `z = 1`. -/
private lemma rod_iteratedDeriv_at_one (n j : ℕ) (hj : j < n) :
    iteratedDeriv j (fun z : ℂ => (z^2-1)^n) 1 = 0 := by
  set Pc : Polynomial ℂ := (Polynomial.X^2 - 1)^n
  have hf : (fun z : ℂ => (z^2-1)^n) = fun z => Pc.eval z := by funext w; simp [Pc]
  rw [hf, iteratedDeriv_eval_polynomial]
  have hdvd : (Polynomial.X - Polynomial.C 1)^n ∣ Pc := by
    refine pow_dvd_pow_of_dvd ⟨Polynomial.X + 1, ?_⟩ n
    simp only [map_one]; ring
  have h2 := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd j hdvd
  have h3 : (Polynomial.X - Polynomial.C (1:ℂ)) ∣ Polynomial.derivative^[j] Pc :=
    (dvd_pow_self _ (by omega)).trans h2
  exact Polynomial.dvd_iff_isRoot.mp h3

/-- Derivatives of `(z²-1)ⁿ` have the next derivative as derivative. -/
private lemma rod_hasDerivAt (n j : ℕ) (z : ℂ) :
    HasDerivAt (iteratedDeriv j (fun z : ℂ => (z^2-1)^n))
      (iteratedDeriv (j+1) (fun z : ℂ => (z^2-1)^n) z) z := by
  set Pc : Polynomial ℂ := (Polynomial.X^2 - 1)^n
  have hf : (fun z : ℂ => (z^2-1)^n) = fun z => Pc.eval z := by funext w; simp [Pc]
  rw [hf, iteratedDeriv_eval_polynomial, iteratedDeriv_eval_polynomial,
    Function.iterate_succ_apply']
  exact Polynomial.hasDerivAt _ _

/-- The differentiated Legendre equation for derivatives of `(z²-1)ⁿ`. -/
private lemma rod_ode (n k : ℕ) (z : ℂ) :
    (z^2-1) * iteratedDeriv (n+k+2) (fun z : ℂ => (z^2-1)^n) z +
      2*(k+1)*z*iteratedDeriv (n+k+1) (fun z : ℂ => (z^2-1)^n) z =
      ((n:ℂ)-k)*(n+k+1) * iteratedDeriv (n+k) (fun z : ℂ => (z^2-1)^n) z := by
  have h := legInt_ode n k z
  simp only [legInt_D, iteratedDeriv_legendrePolyP_rodrigues] at h
  have hc : (2^n*(n.factorial:ℂ))⁻¹ ≠ 0 := by
    apply inv_ne_zero; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (by exact_mod_cast n.factorial_ne_zero)
  rw [show k+2+n = n+k+2 by ring, show k+1+n = n+k+1 by ring, show k+n = n+k by ring] at h
  have h' := h
  apply mul_left_cancel₀ hc
  linear_combination -h'

/-- `(n+k)! D^{n-k}(z²-1)ⁿ = (n-k)! (z²-1)^k D^{n+k}(z²-1)ⁿ` for `k ≤ n`. -/
private lemma rod_negative_order (n k : ℕ) (hk : k ≤ n) (z : ℂ) :
    ((n+k).factorial:ℂ) * iteratedDeriv (n-k) (fun z : ℂ => (z^2-1)^n) z =
      ((n-k).factorial:ℂ) * (z^2-1)^k * iteratedDeriv (n+k) (fun z : ℂ => (z^2-1)^n) z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    set G := fun j => iteratedDeriv j (fun z : ℂ => (z^2-1)^n)
    obtain ⟨a, rfl⟩ : ∃ a, n = a + (k+1) := ⟨n - (k+1), by omega⟩
    have e1 : a + (k+1) - (k+1) = a := by omega
    have e2 : a + (k+1) - k = a + 1 := by omega
    have ih' := fun z => ih (by omega) z
    rw [e2] at ih'
    rw [e1]
    set h : ℂ → ℂ := fun z => (a.factorial:ℂ) * (z^2-1)^(k+1) * G (a+(k+1)+(k+1)) z -
      ((a+(k+1)+(k+1)).factorial:ℂ) * G a z with hh
    have hd : ∀ z, HasDerivAt h 0 z := by
      intro z
      have d1 := rod_hasDerivAt (a+(k+1)) (a+(k+1)+(k+1)) z
      have d2 := rod_hasDerivAt (a+(k+1)) a z
      have dp : HasDerivAt (fun z : ℂ => (z^2-1)^(k+1)) ((k+1:ℕ)*(z^2-1)^k*(2*z)) z :=
        (((hasDerivAt_pow 2 z).sub_const 1).fun_pow (k+1)).congr_deriv (by simp)
      have hsum := ((dp.const_mul (a.factorial:ℂ)).mul d1).sub (d2.const_mul (((a+(k+1)+(k+1)).factorial:ℂ)))
      refine hsum.congr_deriv ?_
      have hode := rod_ode (a+(k+1)) k z
      have hi := ih' z
      rw [show a+(k+1)+k+2 = a+(k+1)+(k+1)+1 by ring, show a+(k+1)+k+1 = a+(k+1)+(k+1) by ring] at hode
      have f1 : ((a+1).factorial:ℂ) = (a+1)*a.factorial := by push_cast [Nat.factorial_succ]; ring
      have f2 : ((a+(k+1)+(k+1)).factorial:ℂ) = (a+(k+1)+k+1)*((a+(k+1)+k).factorial) := by
        rw [show a+(k+1)+(k+1) = (a+(k+1)+k)+1 by ring, Nat.factorial_succ]; push_cast; ring
      rw [f1] at hi
      rw [f2]
      push_cast at hode hi ⊢
      linear_combination (a.factorial:ℂ) * (z^2-1)^k * hode - ((a:ℂ)+(k+1)+k+1) * hi
    have hdiff : Differentiable ℂ h := fun z => (hd z).differentiableAt
    have hconst : ∀ z, h z = h 1 := fun z =>
      is_const_of_deriv_eq_zero hdiff (fun w => (hd w).deriv) z 1
    have h1 : h 1 = 0 := by
      simp only [hh, G, rod_iteratedDeriv_at_one (a+(k+1)) a (by omega)]; simp
    have := hconst z
    rw [h1, hh] at this
    simp only [G] at this
    linear_combination -this

/-- Real-variable derivatives of `(1-x²)ˡ` through the complex polynomial `(z²-1)ˡ`. -/
private lemma rod_iteratedDeriv_real (l j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun x : ℝ => (1-(x:ℂ)^2)^l) x =
      (-1)^l * iteratedDeriv j (fun z : ℂ => (z^2-1)^l) (x:ℂ) := by
  set R : Polynomial ℝ := (Polynomial.X^2 - 1)^l
  set p : Polynomial ℝ := (1 - Polynomial.X^2)^l
  have hp : p = Polynomial.C ((-1:ℝ)^l) * R := by
    simp only [p, R, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_1, ← mul_pow]; ring_nf
  have hf : (fun x : ℝ => (1-(x:ℂ)^2)^l) = fun x : ℝ => ((p.eval x : ℝ) : ℂ) := by
    funext t; simp [p]
  have hRc : (fun z : ℂ => (z^2-1)^l) = fun z => (R.map ofRealHom).eval z := by
    funext w; simp [R]
  rw [hf, iteratedDeriv_ofReal_eval_polynomial, hRc, iteratedDeriv_eval_polynomial]
  dsimp only
  rw [Polynomial.iterate_derivative_map, eval_ofReal_map_ofRealHom, hp,
    Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
  push_cast; ring

/-- DLMF 14.30.3: for `|m| ≤ l` and `0 < θ < π`, `Y_{l,m}(θ, φ) = ((-1)^{l+m}/(2^l l!)) √((l-m)!
(2l+1)/(4π (l+m)!)) e^{imφ} sin^m θ · d^{l+m}(1-x²)^l/dx^{l+m}` evaluated at `x = cos θ`. -/
@[dlmf 14.30.E3]
theorem sphericalHarmonic_rodrigues (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) (phi : ℝ) :
    sphericalHarmonic l m θ phi=(-1:ℂ)^((l:ℤ)+m)/(2^l*(l.factorial:ℂ))*Real.sqrt ((((l:ℤ)-m).toNat.factorial:ℝ)*(2*l+1)/(4*π*((l:ℤ)+m).toNat.factorial))*exp (I*m*phi)*(Real.sin θ:ℂ)^m*iteratedDeriv ((l:ℤ)+m).toNat (fun x : ℝ => (1-x^2:ℂ)^l) (Real.cos θ) := by
  have hx : Real.cos θ ∈ Ioo (-1:ℝ) 1 := by
    constructor
    · rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ
    · rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) h0
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hcs : (1 - (Real.cos θ:ℂ)^2) = (Real.sin θ:ℂ)^2 := by
    rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring
  have hpow : ∀ k : ℕ, (1 - (Real.cos θ:ℂ)^2)^((k:ℂ)/2) = (Real.sin θ:ℂ)^k := by
    intro k
    rw [hcs, ← ofReal_pow, show ((k:ℂ)/2) = (((k:ℝ)/2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), ← Real.rpow_natCast (Real.sin θ) 2, ← Real.rpow_mul hs.le,
      show ((2:ℕ):ℝ) * (k/2) = k by push_cast; ring, Real.rpow_natCast, ofReal_pow]
  set S : ℂ := (Real.sin θ : ℂ) with hS
  suffices hF : ferrersP l m (Real.cos θ) = (-1:ℂ)^((l:ℤ)+m)/(2^l*(l.factorial:ℂ)) *
      S^m * iteratedDeriv ((l:ℤ)+m).toNat (fun x : ℝ => (1-x^2:ℂ)^l) (Real.cos θ) by
    rw [sphericalHarmonic_ferrers l m hm h0 hπ, hF]; ring
  rcases le_or_gt 0 m with hm0 | hm0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k:ℤ) := ⟨m.natAbs, by omega⟩
    rw [show ((l:ℤ)+(k:ℤ)).toNat = k + l by omega, zpow_natCast,
      show ((l:ℤ)+(k:ℤ)) = ((k+l:ℕ):ℤ) by push_cast; ring, zpow_natCast]
    push_cast
    rw [ferrersP_nat_order_rodrigues l k hx, hpow]; ring
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k:ℤ) := ⟨m.natAbs, by omega⟩
    have hkl : k ≤ l := by simpa using hm
    have hG : ∀ n : ℕ, (l:ℂ) - k + 1 ≠ -n := by
      intro n h
      have : ((l - k + 1 + n : ℕ) : ℂ) = 0 := by push_cast [Nat.cast_sub hkl]; linear_combination h
      exact absurd (Nat.cast_eq_zero.1 this) (by omega)
    push_cast
    rw [ferrersP_negative_integer_order (l:ℂ) k hG hx, ferrersP_nat_order_rodrigues l k hx, hpow,
      show ((l:ℤ)+-(k:ℤ)).toNat = l - k by omega,
      rod_iteratedDeriv_real, rod_iteratedDeriv_real]
    have e1 : (l:ℂ) - k + 1 = ((l - k : ℕ) : ℂ) + 1 := by push_cast [Nat.cast_sub hkl]; ring
    have e2 : (l:ℂ) + k + 1 = ((l + k : ℕ) : ℂ) + 1 := by push_cast; ring
    rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial]
    have key := rod_negative_order l k hkl (Real.cos θ)
    have hx2 : ((Real.cos θ:ℂ)^2 - 1)^k = (-1)^k * S^(2*k) := by
      rw [show (Real.cos θ:ℂ)^2 - 1 = -(1 - (Real.cos θ:ℂ)^2) by ring, hcs, neg_pow, pow_mul]
    rw [hx2] at key
    rw [show k + l = l + k by ring]
    have hz1 : (-1:ℂ)^((l:ℤ) + -(k:ℤ)) = (-1)^l * (-1)^k := by
      rw [zpow_add₀ (by norm_num), zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
    rw [hz1, zpow_neg, zpow_natCast]
    have hf1 : ((l+k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hs1 : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
    have hs2 : ((-1:ℂ))^l * (-1)^l = 1 := by rw [← mul_pow]; norm_num
    set A := iteratedDeriv (l+k) (fun z : ℂ => (z^2-1)^l) (Real.cos θ)
    set B := iteratedDeriv (l-k) (fun z : ℂ => (z^2-1)^l) (Real.cos θ)
    have hB : B = ((l-k).factorial:ℂ) * ((-1)^k * S^(2*k)) * A / ((l+k).factorial:ℂ) := by
      rw [eq_div_iff hf1, mul_comm]; exact key
    rw [hB, pow_mul]
    field_simp
    linear_combination (0:ℂ) * hs1

/-- The polynomial Ferrers function vanishes at `x = 1` for positive order. -/
theorem ferrersPNat_one (l m : ℕ) : ferrersPNat l m 1 = if m = 0 then 1 else 0 := by
  rcases m with _ | k
  · simp only [ferrersPNat, pow_zero, one_mul, iteratedDeriv_zero, ite_true, ofReal_one]
    rw [legendrePolyP, jacobiPolyP_one ]
    simp [Nat.cast_ne_zero.mpr l.factorial_ne_zero]
  · simp [ferrersPNat]

/-- DLMF 14.30.4: for `|m| ≤ l`, at the north pole `Y_{l,m}(0, φ) = √((2l+1)/(4π))` if `m = 0` and
`0` otherwise. -/
@[dlmf 14.30.E4]
theorem sphericalHarmonic_north (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) (phi : ℝ) :
    sphericalHarmonic l m 0 phi=if m=0 then (Real.sqrt ((2*l+1)/(4*π)):ℂ) else 0 := by
  rw [sphericalHarmonic, ite_eq_right (not_lt.2 hm)]
  simp only [sphericalHarmonicNonneg, Real.cos_zero, ferrersPNat_one, Int.natAbs_eq_zero]
  by_cases h : m = 0
  · subst h
    have : (l.factorial:ℝ)*(2*l+1)/(4*π*l.factorial) = (2*l+1)/(4*π) := by
      have : (0:ℝ) < l.factorial := by positivity
      field_simp
    simp [this]
  · simp [h]

/-- Gamma at `1/2 - s` for natural `s`, in factorial form. -/
theorem Gamma_one_half_sub_nat_mul (s : ℕ) :
    Gamma (1/2 - s) * ((2*s).factorial : ℂ) = (-4:ℂ)^s * s.factorial * Real.sqrt π := by
  induction s with
  | zero => simpa using legendre_Gamma_one_half
  | succ s ih =>
    have h1 : Gamma (1/2 - s) = (1/2 - ((s+1:ℕ):ℂ)) * Gamma (1/2 - ((s+1:ℕ):ℂ)) := by
      rw [← Gamma_add_one]
      · push_cast; ring_nf
      · intro h
        have := congrArg Complex.re h
        simp at this
        linarith
    rw [h1] at ih
    rw [show 2*(s+1) = 2*s+1+1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast at ih ⊢
    linear_combination (-2*(2*(s:ℂ)+2)) * ih

/-- DLMF 14.30.5: for `|m| ≤ l`, at the equator `Y_{l,m}(π/2, φ) = (-1)^{(l+m)/2} e^{imφ} √((l-m)!
(l+m)! (2l+1)/(4π))/(2^l ((l-m)/2)! ((l+m)/2)!)` when `l + m` is even, and `0` otherwise. -/
@[dlmf 14.30.E5]
theorem sphericalHarmonic_equator (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) (phi : ℝ) :
    sphericalHarmonic l m (π/2) phi=if Even ((l:ℤ)+m) then (-1:ℂ)^(((l:ℤ)+m)/2)*exp (I*m*phi)/(2^l*((((l:ℤ)-m)/2).toNat.factorial:ℂ)*((((l:ℤ)+m)/2).toNat.factorial:ℂ))*Real.sqrt ((((l:ℤ)-m).toNat.factorial:ℝ)*((l:ℤ)+m).toNat.factorial*(2*l+1)/(4*π)) else 0 := by
  rw [sphericalHarmonic_ferrers l m hm (by positivity) (by linarith [Real.pi_pos]) phi,
    Real.cos_pi_div_two, ferrersP_zero_1]
  split_ifs with he
  · obtain ⟨s, hs⟩ : ∃ s : ℕ, (l:ℤ) + m = 2*s := by
      obtain ⟨t, ht⟩ := he; exact ⟨t.toNat, by omega⟩
    obtain ⟨r, hr⟩ : ∃ r : ℕ, (l:ℤ) - m = 2*r := ⟨((l:ℤ)-m).toNat/2, by omega⟩
    have hl : (l:ℂ) = r + s := by
      have : (l:ℤ) = r + s := by omega
      exact_mod_cast this
    have hmC : (m:ℂ) = s - r := by
      have : m = s - r := by omega
      rw [this]; push_cast; ring
    rw [hs, hr, show (2*(s:ℤ)).toNat = 2*s by omega, show (2*(r:ℤ)).toNat = 2*r by omega,
      show (2*(s:ℤ))/2 = s by omega, show (2*(r:ℤ))/2 = r by omega, Int.toNat_natCast]
    have e1 : ((l:ℂ) - m)/2 + 1 = (r:ℂ) + 1 := by rw [hl, hmC]; ring
    have e2 : (1 - (l:ℂ) - m)/2 = 1/2 - s := by rw [hl, hmC]; ring
    rw [e1, e2, Gamma_nat_eq_factorial]
    have hG := Gamma_one_half_sub_nat_mul s
    have hGne : Gamma (1/2 - s) ≠ 0 := by
      intro h; rw [h, zero_mul] at hG
      have : (Real.sqrt π : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
      simp [this, Nat.factorial_ne_zero] at hG
    have h2 : (2:ℂ)^(m:ℂ) * 2^l = 4^s := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ (by norm_num), hmC, hl,
        show (s:ℂ) - r + (r+s) = ((2*s : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast, pow_mul]
      norm_num
    set A : ℝ := ((2*r).factorial:ℝ)*(2*l+1)/(4*π)
    have hA : 0 ≤ A := by positivity
    have hb : (0:ℝ) < (2*s).factorial := by positivity
    have hsq1 : Real.sqrt (((2*r).factorial:ℝ)*(2*l+1)/(4*π*(2*s).factorial)) =
        Real.sqrt A / Real.sqrt (2*s).factorial := by
      rw [← Real.sqrt_div hA]; congr 1; simp only [A]; field_simp
    have hsq2 : Real.sqrt (((2*r).factorial:ℝ)*(2*s).factorial*(2*l+1)/(4*π)) =
        Real.sqrt A * Real.sqrt ((2*s).factorial) := by
      rw [← Real.sqrt_mul hA]; congr 1; simp only [A]; ring
    rw [hsq1, hsq2]
    have hsb : (Real.sqrt ((2*s).factorial) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hb).ne'
    have hsb2 : (Real.sqrt ((2*s).factorial) : ℂ)^2 = ((2*s).factorial : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hb.le]; push_cast; ring
    simp only [Int.toNat_natCast, zpow_natCast]
    have hpi : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
    have hbC : ((2*s).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hrC : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hsC : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    rw [eq_div_of_mul_eq hbC hG, eq_div_of_mul_eq (pow_ne_zero _ two_ne_zero) h2, ← hsb2,
      show (-4:ℂ)^s = (-1)^s * 4^s by rw [← mul_pow]; norm_num]
    have h4 : (4:ℂ)^s ≠ 0 := pow_ne_zero _ (by norm_num)
    have hm1 : ((-1:ℂ))^s ≠ 0 := by simp
    have hm2 : ((-1:ℂ))^s * (-1)^s = 1 := by rw [← mul_pow]; norm_num
    field_simp
    linear_combination (-(Real.sqrt A:ℂ)) * hm2
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (l:ℤ) + m = 2*j + 1 := by
      have := Int.not_even_iff_odd.1 he
      obtain ⟨t, ht⟩ := this; exact ⟨t.toNat, by omega⟩
    have e2 : (1 - (l:ℂ) - m)/2 = -(j:ℂ) := by
      have : ((l:ℤ):ℂ) + (m:ℂ) = 2*j+1 := by exact_mod_cast hj
      push_cast at this; linear_combination -this/2
    rw [e2, Gamma_neg_nat_eq_zero]; simp

/-- DLMF 14.30.6: `Y_{l,-m}(θ, φ) = (-1)^m conj(Y_{l,m}(θ, φ))` for all integers `m`. -/
@[dlmf 14.30.E6]
theorem sphericalHarmonic_negative_order (l : ℕ) (m : ℤ) (θ phi : ℝ) :
    sphericalHarmonic l (-m) θ phi=(-1:ℂ)^m*star (sphericalHarmonic l m θ phi) := by
  simp only [sphericalHarmonic, Int.natAbs_neg]
  split_ifs
  all_goals simp
  · omega
  · left
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k:ℤ) := ⟨m.natAbs, by omega⟩
    simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k:ℤ) := ⟨m.natAbs, by omega⟩
    simp only [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    rw [← mul_assoc, inv_mul_cancel₀ (by simp), one_mul]
  · obtain rfl : m = 0 := by omega
    simp only [Int.natAbs_zero, zpow_zero, one_mul, sphericalHarmonicNonneg, map_mul,
      Complex.conj_ofReal, ← Complex.exp_conj]
    have := star_ferrersPNat l 0 (Real.cos θ)
    simp only [Complex.star_def] at this
    rw [this]; simp

/-- Parity of the polynomial Ferrers function. -/
theorem ferrersPNat_neg (l m : ℕ) (x : ℝ) :
    ferrersPNat l m (-x) = (-1)^(l+m) * ferrersPNat l m x := by
  have hP : legendrePolyP l = fun z => (-1:ℂ)^l * legendrePolyP l (-z) := by
    funext z
    have h := jacobi_reflection (α := 0) (β := 0) (by norm_num) (by norm_num) l (-z)
    rw [neg_neg] at h
    change jacobiPolyP 0 0 l z = (-1)^l * jacobiPolyP 0 0 l (-z)
    rw [h]
  have hD : iteratedDeriv m (legendrePolyP l) (-(x:ℂ)) =
      (-1:ℂ)^(l+m) * iteratedDeriv m (legendrePolyP l) (x:ℂ) := by
    conv_lhs => rw [hP]
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_neg, neg_neg, smul_eq_mul]
    ring
  simp only [ferrersPNat, ofReal_neg, hD, neg_sq]
  ring

/-- DLMF 14.30.7: `Y_{l,m}(π-θ, φ+π) = (-1)^l Y_{l,m}(θ, φ)`. -/
@[dlmf 14.30.E7]
theorem sphericalHarmonic_parity (l : ℕ) (m : ℤ) (θ phi : ℝ) :
    sphericalHarmonic l m (π-θ) (phi+π)=(-1)^l*sphericalHarmonic l m θ phi := by
  have hY : ∀ k : ℕ, sphericalHarmonicNonneg l k (π-θ) (phi+π) =
      (-1)^l * sphericalHarmonicNonneg l k θ phi := by
    intro k
    simp only [sphericalHarmonicNonneg, Real.cos_pi_sub, ferrersPNat_neg]
    have he : exp (I*k*((phi+π:ℝ):ℂ)) = (-1)^k * exp (I*k*phi) := by
      push_cast
      rw [show I*k*(phi+π) = I*k*phi + k*(π*I) by ring, exp_add, Complex.exp_nat_mul,
        Complex.exp_pi_mul_I]; ring
    rw [he]
    have : ((-1:ℂ))^(l+k)*(-1)^k = (-1)^l := by
      rw [pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination (Real.sqrt (((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial)) *
      exp (I*k*phi) * ferrersPNat l k (Real.cos θ) : ℂ) * this
  simp only [sphericalHarmonic]
  split_ifs
  · simp
  · rw [hY, star_mul', star_pow, star_neg, star_one]; ring
  · rw [hY]

/-- Sign factor of the negative-order spherical harmonics. -/
private def shSign (m : ℤ) : ℂ := if m < 0 then (-1)^m.natAbs else 1

/-- The sign factor is real. -/
private lemma star_shSign (m : ℤ) : star (shSign m) = shSign m := by
  unfold shSign; split_ifs <;> simp

/-- The sign factor squares to one. -/
private lemma shSign_mul_self (m : ℤ) : shSign m * shSign m = 1 := by
  unfold shSign; split_ifs
  · rw [← mul_pow]; norm_num
  · simp

/-- Uniform product form of `Y_{l,m}` valid for all angles. -/
private lemma sphericalHarmonic_eq_sign_mul (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) (θ phi : ℝ) :
    sphericalHarmonic l m θ phi = shSign m *
      (Real.sqrt (((l-m.natAbs).factorial:ℝ)*(2*l+1)/(4*π*(l+m.natAbs).factorial)) : ℂ) *
        exp (I*m*phi) * ferrersPNat l m.natAbs (Real.cos θ) := by
  rw [sphericalHarmonic, ite_eq_right (not_lt.2 hm), shSign]
  split_ifs with h
  · rw [sphericalHarmonicNonneg]
    simp only [star_mul', star_ferrersPNat, Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj,
      map_mul, conj_I, conj_natCast]
    have : ((m.natAbs : ℕ) : ℂ) = -(m:ℂ) := by
      have h' : (m.natAbs : ℤ) = -m := by omega
      rw [← Int.cast_natCast, h']; push_cast; ring
    rw [this]; ring_nf
  · rw [sphericalHarmonicNonneg]
    have : ((m.natAbs : ℕ) : ℂ) = (m:ℂ) := by
      have h' : (m.natAbs : ℤ) = m := by omega
      rw [← Int.cast_natCast, h']
    rw [this]; ring

/-- Substitution `x = cos θ` in the polar-angle integral. -/
private lemma integral_ferrersPNat_mul_sin (l₁ l₂ k : ℕ) :
    (∫ θ : ℝ in 0..π, ferrersPNat l₁ k (Real.cos θ) * ferrersPNat l₂ k (Real.cos θ) * Real.sin θ) =
      ∫ x : ℝ in -1..1, ferrersPNat l₁ k x * ferrersPNat l₂ k x := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos (a := 0) (b := π)
    (f := Real.cos) (f' := fun t => -Real.sin t)
    (g := fun x => ferrersPNat l₁ k x * ferrersPNat l₂ k x)
    Real.continuous_cos.continuousOn (fun x _ => Real.hasDerivAt_cos x)
    (fun x hx => by
      rw [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hx
      simp only [neg_nonpos]; exact (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).le)
  rw [Real.cos_zero, Real.cos_pi] at h
  rw [intervalIntegral.integral_symm 1 (-1), ← h, ← intervalIntegral.integral_neg]
  congr 1; funext θ; simp only [Function.comp, real_smul]; push_cast; ring

/-- Orthogonality of the polynomial Ferrers functions, from DLMF 14.17.6. -/
private lemma integral_ferrersPNat_orth (l₁ l₂ k : ℕ) (h1 : k ≤ l₁) (h2 : k ≤ l₂) :
    (∫ x : ℝ in -1..1, ferrersPNat l₁ k x * ferrersPNat l₂ k x) =
      if l₁ = l₂ then ((l₂+k).factorial:ℂ)/((l₂-k).factorial*(l₂+1/2:ℂ)) else 0 := by
  rw [← ferrers_orthogonality_6 l₁ k l₂ h1 h2]
  refine intervalIntegral.integral_congr_ae ?_
  have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
  filter_upwards [this] with t ht htm
  rw [uIoc_of_le (by norm_num)] at htm
  have hx : t ∈ Ioo (-1:ℝ) 1 := ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩
  rw [one_mul, ferrersPNat_eq _ _ hx, ferrersPNat_eq _ _ hx]

/-- `∫₀^{2π} e^{inφ} dφ` for integer `n`. -/
private lemma integral_exp_I_int (n : ℤ) :
    (∫ phi : ℝ in 0..2*π, exp (I*n*phi)) = if n = 0 then (2*π:ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : I*(n:ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast h)
    rw [integral_exp_mul_complex hc]
    have : exp (I*n*((2*π:ℝ):ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨n, by push_cast; ring⟩
    push_cast at this
    simp [this]

/-- DLMF 14.30.8: for `|m₁| ≤ l₁` and `|m₂| ≤ l₂`, `∫₀^{2π} ∫₀^π conj(Y_{l₁,m₁}(θ, φ)) Y_{l₂,m₂}(θ,
φ) sin θ dθ dφ = δ_{l₁,l₂} δ_{m₁,m₂}`. -/
@[dlmf 14.30.E8]
theorem sphericalHarmonic_orthonormal (l₁ l₂ : ℕ) (m₁ m₂ : ℤ) (h1 : m₁.natAbs ≤ l₁) (h2 : m₂.natAbs ≤ l₂) :
    (∫ phi : ℝ in 0..2*π, ∫ θ : ℝ in 0..π, star (sphericalHarmonic l₁ m₁ θ phi)*sphericalHarmonic l₂ m₂ θ phi*Real.sin θ)=if l₁=l₂ ∧ m₁=m₂ then 1 else 0 := by
  set c₁ : ℂ := (Real.sqrt (((l₁-m₁.natAbs).factorial:ℝ)*(2*l₁+1)/(4*π*(l₁+m₁.natAbs).factorial)) : ℂ)
  set c₂ : ℂ := (Real.sqrt (((l₂-m₂.natAbs).factorial:ℝ)*(2*l₂+1)/(4*π*(l₂+m₂.natAbs).factorial)) : ℂ)
  have hpt : ∀ phi θ : ℝ, star (sphericalHarmonic l₁ m₁ θ phi)*sphericalHarmonic l₂ m₂ θ phi*Real.sin θ =
      (shSign m₁ * shSign m₂ * c₁ * c₂ * exp (I*((m₂-m₁:ℤ):ℂ)*phi)) *
        (ferrersPNat l₁ m₁.natAbs (Real.cos θ) * ferrersPNat l₂ m₂.natAbs (Real.cos θ) * Real.sin θ) := by
    intro phi θ
    rw [sphericalHarmonic_eq_sign_mul l₁ m₁ h1, sphericalHarmonic_eq_sign_mul l₂ m₂ h2]
    simp only [star_mul', star_ferrersPNat, star_shSign, c₁, Complex.star_def, Complex.conj_ofReal,
      ← Complex.exp_conj, map_mul, conj_I, map_intCast, conj_ofReal]
    have : exp (-I*m₁*phi) * exp (I*m₂*phi) = exp (I*((m₂-m₁:ℤ):ℂ)*phi) := by
      rw [← exp_add]; push_cast; ring_nf
    rw [← this]; ring
  set J := ∫ θ : ℝ in 0..π, ferrersPNat l₁ m₁.natAbs (Real.cos θ) * ferrersPNat l₂ m₂.natAbs (Real.cos θ) * Real.sin θ with hJ
  rw [intervalIntegral.integral_congr (g := fun phi : ℝ =>
      (shSign m₁ * shSign m₂ * c₁ * c₂) * exp (I*((m₂-m₁:ℤ):ℂ)*phi) * J) (fun phi _ => by
        simp only [hpt]; rw [intervalIntegral.integral_const_mul])]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    integral_exp_I_int, hJ]
  by_cases hm : m₂ = m₁
  · subst hm
    rw [sub_self, ite_eq_left rfl, integral_ferrersPNat_mul_sin,
        integral_ferrersPNat_orth _ _ _ h1 h2]
    by_cases hl : l₁ = l₂
    · subst hl
      simp only [and_self, ite_true]
      have hss := shSign_mul_self m₂
      have hX : 0 ≤ ((l₁-m₂.natAbs).factorial:ℝ)*(2*l₁+1)/(4*π*(l₁+m₂.natAbs).factorial) := by positivity
      have hc : c₁ * c₁ = ((l₁-m₂.natAbs).factorial:ℂ)*(2*l₁+1)/(4*π*(l₁+m₂.natAbs).factorial) := by
        simp only [c₁]; rw [← ofReal_mul, Real.mul_self_sqrt hX]; push_cast; ring
      have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      have hf1 : ((l₁-m₂.natAbs).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hf2 : ((l₁+m₂.natAbs).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have h2l : (2*(l₁:ℂ)+1) ≠ 0 := by exact_mod_cast (show (2*l₁+1:ℕ) ≠ 0 by omega)
      have hl2 : ((l₁:ℂ)+1/2) ≠ 0 := by
        intro h; have := congrArg re h; simp at this; linarith [(l₁.cast_nonneg : (0:ℝ) ≤ l₁)]
      calc _ = (shSign m₂ * shSign m₂) * (c₁ * c₁) * (2*π) *
            (((l₁+m₂.natAbs).factorial:ℂ)/((l₁-m₂.natAbs).factorial*(l₁+1/2:ℂ))) := by ring
        _ = 1 := by rw [hss, hc]; field_simp; ring
    · simp [hl]
  · rw [ite_eq_right (sub_ne_zero.mpr hm), ite_eq_right (fun h => hm h.2.symm)]; simp

/-- A sum over a symmetric integer interval, paired by sign. -/
theorem sum_Icc_neg_pair (g : ℤ → ℂ) (l : ℕ) :
    ∑ m ∈ Finset.Icc (-(l:ℤ)) l, g m = g 0 + ∑ k ∈ Finset.range l, (g (k+1) + g (-(k+1))) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hs : Finset.Icc (-((l+1:ℕ):ℤ)) ((l+1:ℕ):ℤ) =
        insert ((l:ℤ)+1) (insert (-((l:ℤ)+1)) (Finset.Icc (-(l:ℤ)) l)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hs, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ]
    ring

/-- Product of a conjugated and a plain nonnegative-order spherical harmonic. -/
theorem star_mul_sphericalHarmonicNonneg (l k : ℕ) {θ₁ θ₂ : ℝ} (h1 : θ₁ ∈ Icc 0 π) (h2 : θ₂ ∈ Icc 0 π)
    (phi₁ phi₂ : ℝ) :
    star (sphericalHarmonicNonneg l k θ₁ phi₁) * sphericalHarmonicNonneg l k θ₂ phi₂ =
      (2*l+1)/(4*π) * LegendreAddition.coeff l k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) *
        exp (I*k*(phi₂-phi₁)) := by
  have hsin : ∀ θ ∈ Icc 0 π, Real.sqrt (1 - Real.cos θ^2) = Real.sin θ := fun θ h =>
    (Real.sin_eq_sqrt_one_sub_cos_sq h.1 h.2).symm
  simp only [sphericalHarmonicNonneg, star_mul', star_ferrersPNat, Complex.star_def, conj_ofReal,
    ← exp_conj, map_mul, conj_I, conj_natCast]
  simp only [ferrersPNat, hsin θ₁ h1, hsin θ₂ h2, LegendreAddition.coeff, LegendreAddition.weight,
    LegendreAddition.jet]
  have hX : 0 ≤ ((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial) := by positivity
  have hc := Real.mul_self_sqrt hX
  have hcC : (Real.sqrt (((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial)) : ℂ) *
      Real.sqrt (((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial)) =
      ((l-k).factorial:ℂ)*(2*l+1)/(4*π*(l+k).factorial) := by
    rw [← ofReal_mul, hc]; push_cast; ring
  have he : exp (-I*k*phi₁) * exp (I*k*phi₂) = exp (I*k*(phi₂-phi₁)) := by
    rw [← exp_add]; ring_nf
  have hs : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
  rw [← he, mul_pow (Real.sin θ₁ : ℂ)]
  set Sq := (Real.sqrt (((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial)) : ℂ)
  linear_combination
    ((-1:ℂ)^k*(-1)^k * (exp (-I*k*phi₁) * exp (I*k*phi₂) * (Real.sin θ₁:ℂ)^k * (Real.sin θ₂:ℂ)^k *
      iteratedDeriv k (legendrePolyP l) (Real.cos θ₁) * iteratedDeriv k (legendrePolyP l) (Real.cos θ₂))) * hcC +
    (((l-k).factorial:ℂ)*(2*l+1)/(4*π*(l+k).factorial) * (exp (-I*k*phi₁) * exp (I*k*phi₂) *
      (Real.sin θ₁:ℂ)^k * (Real.sin θ₂:ℂ)^k *
      iteratedDeriv k (legendrePolyP l) (Real.cos θ₁) * iteratedDeriv k (legendrePolyP l) (Real.cos θ₂))) * hs

/-- DLMF 14.30.9 (addition theorem): for `θ₁, θ₂ ∈ [0, π]`, `P_l(cos θ₁ cos θ₂ + sin θ₁ sin θ₂
cos(φ₁-φ₂)) = (4π/(2l+1)) Σ_{m=-l}^{l} conj(Y_{l,m}(θ₁, φ₁)) Y_{l,m}(θ₂, φ₂)`. -/
@[dlmf 14.30.E9]
theorem sphericalHarmonic_addition (l : ℕ) (θ₁ θ₂ phi₁ phi₂ : ℝ) (h1 : θ₁ ∈ Icc 0 π) (h2 : θ₂ ∈ Icc 0 π) :
    legendrePolyP l (Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos (phi₁-phi₂))=4*π/(2*l+1:ℂ)*∑ m ∈ Finset.Icc (-(l:ℤ)) l, star (sphericalHarmonic l m θ₁ phi₁)*sphericalHarmonic l m θ₂ phi₂ := by
  have hsin : ∀ θ ∈ Icc 0 π, Real.sqrt (1 - Real.cos θ^2) = Real.sin θ := fun θ h =>
    (Real.sin_eq_sqrt_one_sub_cos_sq h.1 h.2).symm
  have hk := LegendreAddition.legendre_eq_kernel l (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁)
    (Real.sin θ₂) ((phi₁-phi₂:ℝ):ℂ) (by rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring)
    (by rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring)
  push_cast at hk ⊢
  rw [hk, sum_Icc_neg_pair, LegendreAddition.kernel, mul_add, Finset.mul_sum, Finset.mul_sum]
  -- the term for each order
  have hT : ∀ k : ℕ, k ≤ l → star (sphericalHarmonic l k θ₁ phi₁) * sphericalHarmonic l k θ₂ phi₂ =
      (2*l+1)/(4*π) * LegendreAddition.coeff l k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) *
        exp (I*k*(phi₂-phi₁)) := by
    intro k hkl
    have hY : ∀ θ phi, sphericalHarmonic l k θ phi = sphericalHarmonicNonneg l k θ phi := by
      intro θ phi; simp [sphericalHarmonic, not_lt.2 hkl]
    rw [hY, hY]; exact star_mul_sphericalHarmonicNonneg l k h1 h2 phi₁ phi₂
  have hTn : ∀ k : ℕ, 0 < k → k ≤ l → star (sphericalHarmonic l (-(k:ℤ)) θ₁ phi₁) * sphericalHarmonic l (-(k:ℤ)) θ₂ phi₂ =
      (2*l+1)/(4*π) * LegendreAddition.coeff l k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) *
        exp (I*k*(phi₁-phi₂)) := by
    intro k hk0 hkl
    have hY : ∀ θ phi, sphericalHarmonic l (-(k:ℤ)) θ phi =
        (-1)^k * star (sphericalHarmonicNonneg l k θ phi) := by
      intro θ phi; simp [sphericalHarmonic, not_lt.2 hkl, hk0]
    rw [hY, hY, star_mul', star_star, star_pow, star_neg, star_one,
      show ∀ a b c : ℂ, a * b * (a * c) = (a*a) * (c * b) by intros; ring, ← mul_pow,
      show (-1:ℂ)*(-1) = 1 by norm_num, one_pow, one_mul,
      star_mul_sphericalHarmonicNonneg l k h2 h1 phi₂ phi₁]
    simp only [LegendreAddition.coeff]; ring
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hl : (2*(l:ℂ)+1) ≠ 0 := by exact_mod_cast (show (2*l+1 : ℕ) ≠ 0 by omega)
  congr 1
  · have := hT 0 (Nat.zero_le _)
    push_cast at this
    rw [this]; field_simp; simp
  · apply Finset.sum_congr rfl
    intro k hk
    have hkl : k+1 ≤ l := by simp at hk; omega
    have h3 := hT (k+1) hkl
    have h4 := hTn (k+1) (by omega) hkl
    push_cast at h3 h4
    have hc : cos (((k:ℂ)+1)*(phi₁-phi₂)) =
        (exp (I*((k:ℂ)+1)*(phi₂-phi₁)) + exp (I*((k:ℂ)+1)*(phi₁-phi₂)))/2 := by
      rw [Complex.cos, add_comm]; congr 3 <;> ring
    rw [h3, h4, hc]
    field_simp

/-- The null vector appearing in the unnumbered Herglotz generating function. -/
def herglotzNullVector (lam : ℂ) : ℂ × ℂ × ℂ :=
  (1/(2*lam)-lam/2,-I/(2*lam)-I*lam/2,1)

/-- `(1-z²)P_n'(z) = (n+1)(z P_n(z) - P_{n+1}(z))`. -/
private lemma herg_E0 (n : ℕ) (z : ℂ) :
    (1 - z^2) * legInt_D n 1 z = (n+1) * (z * legInt_D n 0 z - legInt_D (n+1) 0 z) := by
  have h := jacobi_raising_derivative (α := 0) (β := 0) (by norm_num) n z
  simp only [legInt_D, iteratedDeriv_one, iteratedDeriv_zero]
  change (1 - z^2) * deriv (jacobiPolyP 0 0 n) z = (n+1) * (z * jacobiPolyP 0 0 n z - jacobiPolyP 0 0 (n+1) z)
  have h2 : (2*(n:ℂ)+2) ≠ 0 := by exact_mod_cast (show (2*n+2:ℕ) ≠ 0 by omega)
  apply mul_left_cancel₀ h2
  simp only [add_zero, sub_self] at h
  linear_combination h

/-- The `k`-fold differentiated form of `herg_E0`. -/
private lemma herg_Ek (n k : ℕ) (z : ℂ) :
    (1 - z^2) * legInt_D n (k+2) z - 2*(k+1)*z*legInt_D n (k+1) z - (k+1)*k*legInt_D n k z =
      (n+1) * (z * legInt_D n (k+1) z + (k+1) * legInt_D n k z - legInt_D (n+1) (k+1) z) := by
  induction k generalizing z with
  | zero =>
    have hd := ((((hasDerivAt_pow 2 z).const_sub 1).mul (legInt_hasDerivAt_D n 1 z)).sub
      ((((hasDerivAt_id' z).mul (legInt_hasDerivAt_D n 0 z)).sub (legInt_hasDerivAt_D (n+1) 0 z)).const_mul ((n:ℂ)+1)))
    have h0 : HasDerivAt (fun z => (1 - z^2) * legInt_D n 1 z -
        ((n:ℂ)+1) * (z * legInt_D n 0 z - legInt_D (n+1) 0 z)) 0 z := by
      rw [show (fun z => (1 - z^2) * legInt_D n 1 z - ((n:ℂ)+1) * (z * legInt_D n 0 z - legInt_D (n+1) 0 z))
        = fun _ => 0 from funext fun w => by rw [herg_E0]; ring]
      exact hasDerivAt_const _ _
    have hu := hd.unique h0
    push_cast
    linear_combination hu
  | succ k ih =>
    have hd := (((((hasDerivAt_pow 2 z).const_sub 1).mul (legInt_hasDerivAt_D n (k+2) z)).sub
      (((hasDerivAt_id' z).const_mul (2*((k:ℂ)+1))).mul (legInt_hasDerivAt_D n (k+1) z))).sub
      ((legInt_hasDerivAt_D n k z).const_mul (((k:ℂ)+1)*k))).sub
      (((((hasDerivAt_id' z).mul (legInt_hasDerivAt_D n (k+1) z)).add
        ((legInt_hasDerivAt_D n k z).const_mul ((k:ℂ)+1))).sub (legInt_hasDerivAt_D (n+1) (k+1) z)).const_mul ((n:ℂ)+1))
    have h0 : HasDerivAt (fun z => (1 - z^2) * legInt_D n (k+2) z - 2*((k:ℂ)+1)*z*legInt_D n (k+1) z
        - ((k:ℂ)+1)*k*legInt_D n k z - ((n:ℂ)+1) * (z * legInt_D n (k+1) z + ((k:ℂ)+1) * legInt_D n k z
          - legInt_D (n+1) (k+1) z)) 0 z := by
      rw [show (fun z => (1 - z^2) * legInt_D n (k+2) z - 2*((k:ℂ)+1)*z*legInt_D n (k+1) z
        - ((k:ℂ)+1)*k*legInt_D n k z - ((n:ℂ)+1) * (z * legInt_D n (k+1) z + ((k:ℂ)+1) * legInt_D n k z
          - legInt_D (n+1) (k+1) z)) = fun _ => 0 from funext fun w => by rw [sub_eq_zero]; exact ih w]
      exact hasDerivAt_const _ _
    have hu := hd.unique h0
    push_cast
    linear_combination hu

/-- Core three-term identity behind the Herglotz generating function. -/
private lemma herg_core (n k : ℕ) (z : ℂ) :
    (n+1) * legInt_D (n+1) (k+1) z / ((n+k+2).factorial : ℂ) =
      z * legInt_D n (k+1) z / ((n+k+1).factorial : ℂ) +
        (legInt_D n k z / ((n+k).factorial : ℂ) - (1 - z^2) * legInt_D n (k+2) z / ((n+k+2).factorial : ℂ)) / 2 := by
  have hE := herg_Ek n k z
  have hO := legInt_ode n k z
  have f1 : ((n+k+2).factorial : ℂ) = (n+k+2) * (n+k+1) * (n+k).factorial := by
    rw [show n+k+2 = (n+k+1)+1 by ring, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have f2 : ((n+k+1).factorial : ℂ) = (n+k+1) * (n+k).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h0 : ((n+k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h1 : ((n:ℂ)+k+1) ≠ 0 := by exact_mod_cast (show (n+k+1:ℕ) ≠ 0 by omega)
  have h2 : ((n:ℂ)+k+2) ≠ 0 := by exact_mod_cast (show (n+k+2:ℕ) ≠ 0 by omega)
  rw [f1, f2]
  field_simp
  linear_combination 2 * hE - hO

/-- `P_n^{(k)} = 0` for `k > n`. -/
private lemma herg_D_eq_zero (n k : ℕ) (hk : n < k) (z : ℂ) : legInt_D n k z = 0 := by
  rw [legInt_D, iteratedDeriv_legendrePolyP_rodrigues]
  set Pc : Polynomial ℂ := (Polynomial.X^2 - 1)^n
  have hf : (fun z : ℂ => (z^2-1)^n) = fun z => Pc.eval z := by funext w; simp [Pc]
  rw [hf, iteratedDeriv_eval_polynomial]
  have hdeg : Pc.natDegree < k + n := by
    calc Pc.natDegree ≤ n * (Polynomial.X^2 - 1 : Polynomial ℂ).natDegree := Polynomial.natDegree_pow_le
      _ ≤ n * 2 := by
          gcongr
          exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
      _ < k + n := by omega
  simp [Polynomial.iterate_derivative_eq_zero hdeg]

/-- Normalized coefficient of `wᵏ` in the Herglotz expansion. -/
private noncomputable def hergC (x s : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  (if k < 0 then s^k.natAbs else (-s)^k.natAbs) * legInt_D n k.natAbs x / ((n + k.natAbs).factorial : ℂ)

/-- Coefficients of nonnegative index. -/
private lemma hergC_nat (x s : ℂ) (n k : ℕ) :
    hergC x s n (k:ℤ) = (-s)^k * legInt_D n k x / ((n+k).factorial : ℂ) := by
  simp [hergC, show ¬ ((k:ℤ) < 0) by omega]

/-- Coefficients of nonpositive index. -/
private lemma hergC_neg_nat (x s : ℂ) (n k : ℕ) :
    hergC x s n (-(k:ℤ)) = s^k * legInt_D n k x / ((n+k).factorial : ℂ) := by
  rcases k with _ | k
  · simp [hergC]
  · simp only [hergC, Int.natAbs_neg, Int.natAbs_natCast, show -((k+1:ℕ):ℤ) < 0 by omega, ↓reduceIte]

/-- Coefficients vanish outside `[-n, n]`. -/
private lemma hergC_eq_zero (x s : ℂ) (n : ℕ) (k : ℤ) (hk : n < k.natAbs) : hergC x s n k = 0 := by
  simp [hergC, herg_D_eq_zero n _ hk]

/-- Three-term recurrence of the coefficients in the degree. -/
private lemma hergC_recurrence (x s : ℂ) (hs : s^2 = 1 - x^2) (n : ℕ) (j : ℤ) :
    (n+1) * hergC x s (n+1) j = x * hergC x s n j + s/2 * (hergC x s n (j+1) - hergC x s n (j-1)) := by
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = -((k+1:ℕ):ℤ) := ⟨j.natAbs - 1, by omega⟩
    have e1 : -((k+1:ℕ):ℤ) + 1 = -(k:ℤ) := by push_cast; ring
    have e2 : -((k+1:ℕ):ℤ) - 1 = -((k+2:ℕ):ℤ) := by push_cast; ring
    rw [e1, e2, hergC_neg_nat, hergC_neg_nat, hergC_neg_nat, hergC_neg_nat,
      show n+1+(k+1) = n+k+2 by ring, show n+(k+1) = n+k+1 by ring]
    have hc := herg_core n k x
    linear_combination s^(k+1) * hc + (1/2) * s^(k+1) * legInt_D n (k+2) x / ((n+k+2).factorial:ℂ) * hs
  · have e1 : (0:ℤ) + 1 = ((1:ℕ):ℤ) := by norm_num
    have e2 : (0:ℤ) - 1 = -((1:ℕ):ℤ) := by norm_num
    rw [e1, e2, hergC_nat, hergC_neg_nat, show (0:ℤ) = ((0:ℕ):ℤ) by norm_num, hergC_nat, hergC_nat]
    have h0 := herg_E0 n x
    have f1 : ((n+1).factorial : ℂ) = (n+1) * n.factorial := by push_cast [Nat.factorial_succ]; ring
    have f2 : ((n+1+0).factorial : ℂ) = (n+1) * n.factorial := by simpa using f1
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hn1 : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
    rw [f2, show n+0 = n by ring]
    field_simp
    linear_combination 2 * h0 + 2 * legInt_D n 1 x * hs
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = ((k+1:ℕ):ℤ) := ⟨j.natAbs - 1, by omega⟩
    have e1 : ((k+1:ℕ):ℤ) + 1 = ((k+2:ℕ):ℤ) := by push_cast; ring
    have e2 : ((k+1:ℕ):ℤ) - 1 = ((k:ℕ):ℤ) := by push_cast; ring
    rw [e1, e2, hergC_nat, hergC_nat, hergC_nat, hergC_nat,
      show n+1+(k+1) = n+k+2 by ring, show n+(k+1) = n+k+1 by ring]
    have hc := herg_core n k x
    linear_combination (-s)^(k+1) * hc + (1/2) * (-s)^(k+1) * legInt_D n (k+2) x / ((n+k+2).factorial:ℂ) * hs

/-- Summing a function supported in `[-N, N]` over a larger window. -/
private lemma herg_sum_window (f : ℤ → ℂ) (N : ℕ) (hf : ∀ k : ℤ, N < k.natAbs → f k = 0) {a b : ℤ}
    (ha : a ≤ -(N:ℤ)) (hb : (N:ℤ) ≤ b) :
    ∑ k ∈ Finset.Icc a b, f k = ∑ k ∈ Finset.Icc (-(N:ℤ)) N, f k := by
  refine (Finset.sum_subset (Finset.Icc_subset_Icc ha hb) (fun k hk hk' => hf k ?_)).symm
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk'
  omega

/-- Shifting the summation index over an integer interval. -/
private lemma herg_sum_shift (f : ℤ → ℂ) (a b c : ℤ) :
    ∑ k ∈ Finset.Icc a b, f (k + c) = ∑ k ∈ Finset.Icc (a + c) (b + c), f k := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]; rfl

/-- The Laurent expansion behind the Herglotz generating function. -/
private lemma herg_sum (x s : ℂ) (hs : s^2 = 1 - x^2) {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n:ℤ)) n, hergC x s n k * w^k = (x + s/2*(w⁻¹ - w))^n / n.factorial := by
  induction n with
  | zero =>
    simp [hergC, legInt_D, legendrePolyP_zero]
  | succ n ih =>
    set A := x + s/2*(w⁻¹ - w)
    have hz : ∀ (g : ℤ → ℂ) (k : ℤ), n < k.natAbs → hergC x s n k * g k = 0 := fun g k hk => by
      rw [hergC_eq_zero x s n k hk, zero_mul]
    have h1 : ∑ k ∈ Finset.Icc (-((n+1:ℕ):ℤ)) (n+1:ℕ), hergC x s n k * w^k =
        ∑ k ∈ Finset.Icc (-(n:ℤ)) n, hergC x s n k * w^k :=
      herg_sum_window _ n (hz _) (by push_cast; omega) (by push_cast; omega)
    have h2 : ∑ k ∈ Finset.Icc (-((n+1:ℕ):ℤ)) (n+1:ℕ), hergC x s n (k+1) * w^k =
        w⁻¹ * ∑ k ∈ Finset.Icc (-(n:ℤ)) n, hergC x s n k * w^k := by
      have := herg_sum_shift (fun i => hergC x s n i * w^(i-1)) (-((n+1:ℕ):ℤ)) (n+1:ℕ) 1
      simp only [add_sub_cancel_right] at this
      rw [this, herg_sum_window _ n (hz _) (by push_cast; omega) (by push_cast; omega), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zpow_sub_one₀ hw]; ring
    have h3 : ∑ k ∈ Finset.Icc (-((n+1:ℕ):ℤ)) (n+1:ℕ), hergC x s n (k-1) * w^k =
        w * ∑ k ∈ Finset.Icc (-(n:ℤ)) n, hergC x s n k * w^k := by
      have := herg_sum_shift (fun i => hergC x s n i * w^(i+1)) (-((n+1:ℕ):ℤ)) (n+1:ℕ) (-1)
      simp only [← sub_eq_add_neg, sub_add_cancel] at this
      rw [this, herg_sum_window _ n (hz _) (by push_cast; omega) (by push_cast; omega), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zpow_add_one₀ hw]; ring
    have hrec : ((n:ℂ)+1) * ∑ k ∈ Finset.Icc (-((n+1:ℕ):ℤ)) (n+1:ℕ), hergC x s (n+1) k * w^k =
        A * ∑ k ∈ Finset.Icc (-(n:ℤ)) n, hergC x s n k * w^k := by
      rw [Finset.mul_sum]
      simp_rw [← mul_assoc, hergC_recurrence x s hs n]
      have : ∀ k : ℤ, (x * hergC x s n k + s/2 * (hergC x s n (k+1) - hergC x s n (k-1))) * w^k =
          x * (hergC x s n k * w^k) + s/2 * (hergC x s n (k+1) * w^k) - s/2 * (hergC x s n (k-1) * w^k) :=
        fun k => by ring
      simp_rw [this]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, h1, h2, h3]
      ring
    have hn1 : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
    apply mul_left_cancel₀ hn1
    rw [hrec, ih, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp

/-- Unnumbered Herglotz generating function in DLMF 14.30(ii). -/
theorem herglotz_generating {lam : ℂ} (hlam : lam ≠ 0) (t : ℂ) (r θ phi : ℝ) (hθ : θ ∈ Icc 0 π) :
    HasSum (fun n : ℕ => Real.sqrt (4*π)*∑ m ∈ Finset.Icc (-(n:ℤ)) n, t^n*(r:ℂ)^n*lam^m*sphericalHarmonic n m θ phi/Real.sqrt ((2*n+1:ℝ)*((n:ℤ)+m).toNat.factorial*((n:ℤ)-m).toNat.factorial)) (let a:=herglotzNullVector lam; exp (t*(a.1*(r*Real.sin θ*Real.cos phi)+a.2.1*(r*Real.sin θ*Real.sin phi)+a.2.2*(r*Real.cos θ)))) := by
  set x : ℂ := (Real.cos θ : ℂ) with hx
  set s : ℂ := (Real.sin θ : ℂ) with hsdef
  have hs : s^2 = 1 - x^2 := by
    rw [hsdef, hx, ← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring
  set w : ℂ := lam * exp (I*phi) with hw
  have hw0 : w ≠ 0 := mul_ne_zero hlam (exp_ne_zero _)
  set A := x + s/2*(w⁻¹ - w) with hA
  have hsqrt : Real.sqrt (1 - Real.cos θ^2) = Real.sin θ :=
    (Real.sin_eq_sqrt_one_sub_cos_sq hθ.1 hθ.2).symm
  have hterm : ∀ n : ℕ, Real.sqrt (4*π)*∑ m ∈ Finset.Icc (-(n:ℤ)) n, t^n*(r:ℂ)^n*lam^m*sphericalHarmonic n m θ phi/Real.sqrt ((2*n+1:ℝ)*((n:ℤ)+m).toNat.factorial*((n:ℤ)-m).toNat.factorial) =
      (t*r*A)^n / n.factorial := by
    intro n
    rw [mul_pow, mul_pow, mul_div_assoc, hA, ← herg_sum x s hs hw0 n, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m.natAbs ≤ n := by simp only [Finset.mem_Icc] at hm; omega
    set k := m.natAbs with hk
    have hprod : (((n:ℤ)+m).toNat.factorial : ℝ) * ((n:ℤ)-m).toNat.factorial =
        (n+k).factorial * (n-k).factorial := by
      rcases le_or_gt 0 m with h | h
      · rw [show ((n:ℤ)+m).toNat = n+k by omega, show ((n:ℤ)-m).toNat = n-k by omega]
      · rw [show ((n:ℤ)+m).toNat = n-k by omega, show ((n:ℤ)-m).toNat = n+k by omega, mul_comm]
    have hnorm : Real.sqrt (4*π) * Real.sqrt (((n-k).factorial:ℝ)*(2*n+1)/(4*π*(n+k).factorial)) /
        Real.sqrt ((2*n+1:ℝ)*((n:ℤ)+m).toNat.factorial*((n:ℤ)-m).toNat.factorial) = 1/(n+k).factorial := by
      rw [mul_assoc (2*(n:ℝ)+1), hprod, ← Real.sqrt_mul (by positivity), ← Real.sqrt_div' _ (by positivity)]
      have hf1 : (0:ℝ) < (n+k).factorial := by positivity
      have hf2 : (0:ℝ) < (n-k).factorial := by positivity
      rw [show 4*π*(((n-k).factorial:ℝ)*(2*n+1)/(4*π*(n+k).factorial)) / ((2*n+1)*((n+k).factorial*(n-k).factorial))
          = (1/(n+k).factorial)^2 by field_simp, Real.sqrt_sq (by positivity)]
    have hY := sphericalHarmonic_eq_sign_mul n m hmn θ phi
    rw [← hk] at hY
    rw [hY]
    have hF : ferrersPNat n k (Real.cos θ) = (-1)^k * s^k * legInt_D n k x := by
      rw [ferrersPNat, hsqrt]
    have hW : w^m = lam^m * exp (I*m*phi) := by
      rw [hw, mul_zpow, ← exp_int_mul]; ring_nf
    have hC : hergC x s n m = shSign m * (-1)^k * s^k * legInt_D n k x / ((n+k).factorial:ℂ) := by
      rw [hergC, shSign, ← hk]
      split_ifs
      · rw [← mul_pow]; norm_num
      · rw [neg_pow]; ring
    rw [hF, hW, hC]
    have hnC : ((Real.sqrt (4*π) : ℝ) : ℂ) * ((Real.sqrt (((n-k).factorial:ℝ)*(2*n+1)/(4*π*(n+k).factorial)) : ℝ) : ℂ) /
        ((Real.sqrt ((2*n+1:ℝ)*((n:ℤ)+m).toNat.factorial*((n:ℤ)-m).toNat.factorial) : ℝ) : ℂ) = 1/((n+k).factorial:ℂ) := by
      rw [← ofReal_mul, ← ofReal_div, hnorm]; push_cast; ring
    have hb : ((Real.sqrt ((2*n+1:ℝ)*((n:ℤ)+m).toNat.factorial*((n:ℤ)-m).toNat.factorial) : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt ((2*n+1:ℝ)*((n:ℤ)+m).toNat.factorial*((n:ℤ)-m).toNat.factorial) := by positivity
      exact_mod_cast this.ne'
    have hf0 : ((n+k).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    calc _ = (((Real.sqrt (4*π) : ℝ) : ℂ) * ((Real.sqrt (((n-k).factorial:ℝ)*(2*n+1)/(4*π*(n+k).factorial)) : ℝ) : ℂ) /
        ((Real.sqrt ((2*n+1:ℝ)*((n:ℤ)+m).toNat.factorial*((n:ℤ)-m).toNat.factorial) : ℝ) : ℂ)) *
          (t^n * (r:ℂ)^n * lam^m * shSign m * exp (I*m*phi) * ((-1)^k * s^k * legInt_D n k x)) := by ring
      _ = _ := by rw [hnC]; ring
  have hexp : t*((herglotzNullVector lam).1*((r*Real.sin θ*Real.cos phi : ℝ) : ℂ) +
      (herglotzNullVector lam).2.1*((r*Real.sin θ*Real.sin phi : ℝ) : ℂ) +
      (herglotzNullVector lam).2.2*((r*Real.cos θ : ℝ) : ℂ)) = t*r*A := by
    simp only [herglotzNullVector, hA, hw, hx, hsdef]
    have hc : Complex.cos (phi : ℂ) = (exp (I*phi) + (exp (I*phi))⁻¹)/2 := by
      rw [← exp_neg, Complex.cos]; ring_nf
    have hsn : Complex.sin (phi : ℂ) = (exp (I*phi) - (exp (I*phi))⁻¹)/(2*I) := by
      rw [← exp_neg, Complex.sin]
      field_simp
      ring_nf
      rw [I_sq]; ring
    have hE : exp (I*phi) ≠ 0 := exp_ne_zero _
    push_cast
    rw [hc, hsn, mul_inv]
    field_simp
    ring_nf
  have hexp' : t*((herglotzNullVector lam).1*((r:ℂ)*(Real.sin θ:ℂ)*(Real.cos phi:ℂ)) +
      (herglotzNullVector lam).2.1*((r:ℂ)*(Real.sin θ:ℂ)*(Real.sin phi:ℂ)) +
      (herglotzNullVector lam).2.2*((r:ℂ)*(Real.cos θ:ℂ))) = t*r*A := by
    rw [← hexp]; push_cast; ring
  simp only []
  rw [hexp', Complex.exp_eq_exp_ℂ]
  simp_rw [hterm]
  exact NormedSpace.expSeries_div_hasSum_exp (t*r*A)

/-- Scaled oblate harmonic of the first kind in DLMF 14.30(i). -/
def scaledOblateR (n m : ℕ) (x : ℝ) : ℂ :=
  exp (-I*π*n/2)*associatedP n m (I*x)

/-- Scaled oblate harmonic of the second kind in DLMF 14.30(i). -/
def scaledOblateT (n m : ℕ) (x : ℝ) : ℂ :=
  I*exp (I*π*n/2)*associatedQ n m (I*x)

open DLMF.SphericalHarmonics in
open scoped ComplexConjugate in
/-- Reality of the scaled oblate harmonics. -/
theorem scaledOblate_real (n m : ℕ) {x : ℝ} (hx : 0 < x) :
    (scaledOblateR n m x).im=0 ∧ (scaledOblateT n m x).im=0 := by
  have hz : I*(x:ℂ) - 1 ∈ slitPlane := Or.inr (by simp [hx.ne'])
  have hB := addTools_legendreBranchPower_I_mul m x hx
  set rr : ℝ := Real.exp (m/2 * Real.log (1+x^2))
  have hc : conj (I*(x:ℂ)) = -(I*x) := by simp
  have hs : ∀ k : ℕ, ((-1:ℂ))^k * (-1)^k = 1 := fun k => by rw [← mul_pow]; norm_num
  constructor
  · rw [← conj_eq_iff_im, scaledOblateR, associatedP_nat_order_rodrigues n m hz, hB]
    have hE : exp (-I*π*n/2) = (-I)^n := by
      rw [show -I*π*n/2 = n * (-π/2*I) by ring, exp_nat_mul, exp_neg_pi_div_two_mul_I]
    set P : Polynomial ℝ := (Polynomial.X^2 - 1)^n
    have hf : (fun z : ℂ => (z^2-1)^n) = fun z => (P.map ofRealHom).eval z := by
      funext w; simp [P]
    have hw : conj (iteratedDeriv (m+n) (fun z : ℂ => (z^2-1)^n) (I*x)) =
        (-1)^(m+n) * iteratedDeriv (m+n) (fun z : ℂ => (z^2-1)^n) (I*x) := by
      rw [← addTools_iteratedDeriv_even_neg (fun z => by ring) _ _, ← hc, hf,
        iteratedDeriv_eval_polynomial, Polynomial.iterate_derivative_map,
        addTools_conj_eval_map_ofReal]
    set w := iteratedDeriv (m+n) (fun z : ℂ => (z^2-1)^n) (I*x)
    rw [hE]
    simp only [map_mul, map_div₀, map_pow, map_neg, conj_I, conj_ofReal, hw, map_natCast, map_ofNat]
    rw [neg_neg, pow_add]
    linear_combination (I^n*I^m*(rr:ℂ)/(n.factorial:ℂ)/(2:ℂ)^n*w*(-1)^n) * hs m
  · rw [scaledOblateT, associatedQ, olverQ, hB]
    have hE2 : exp (I*π*n/2) = I^n := by
      rw [show I*π*n/2 = n * (π/2*I) by ring, exp_nat_mul, exp_pi_div_two_mul_I]
    have hE3 : exp ((m:ℂ)*π*I) = (-1)^m := by
      rw [show (m:ℂ)*π*I = m * (π*I) by ring, exp_nat_mul, exp_pi_mul_I]
    have hG : Gamma ((n:ℂ)+(m:ℂ)+1) = ((n+m).factorial : ℂ) := by
      rw [show (n:ℂ)+(m:ℂ)+1 = ((n+m:ℕ):ℂ)+1 by push_cast; ring, Gamma_nat_eq_factorial]
    have h2 : (2:ℂ)^((n:ℂ)+1) = 2^(n+1) := by
      rw [show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring, cpow_natCast]
    have hN : (I*(x:ℂ))^((n:ℂ)+(m:ℂ)+1) = I^n*I^m*I*(x:ℂ)^(n+m+1) := by
      rw [show (n:ℂ)+(m:ℂ)+1 = ((n+m+1:ℕ):ℂ) by push_cast; ring, cpow_natCast, mul_pow,
        pow_succ, pow_add]
    have harg : (1:ℂ)/(I*x)^2 = ((-1/x^2 : ℝ) : ℂ) := by
      push_cast; rw [mul_pow, I_sq]; ring
    set F := regularizedGaussHG (((n:ℂ)+(m:ℂ)+2)/2) (((n:ℂ)+(m:ℂ)+1)/2) ((n:ℂ)+3/2) (1/(I*(x:ℂ))^2)
      with hFdef
    have hF : F.im = 0 := by
      rw [← conj_eq_iff_im, hFdef, harg]
      have hcut : ((-1/x^2 : ℝ) : ℂ) ∈ cutPlane := by
        show 1 - _ ∈ slitPlane
        refine Or.inl ?_
        simp only [sub_re, one_re, ofReal_re]
        have : 0 < 1/x^2 := by positivity
        rw [show -1/x^2 = -(1/x^2) by ring]; linarith
      rw [addTools_conj_regularizedGaussHG _ _ _ hcut]
      simp [map_div₀, conj_ofReal, map_ofNat]
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hT : I * exp (I*π*n/2) * (exp ((m:ℂ)*π*I) * Gamma ((n:ℂ)+(m:ℂ)+1) *
        (Real.sqrt π * ((rr:ℂ) * I^m) / (2^((n:ℂ)+1) * (I*(x:ℂ))^((n:ℂ)+(m:ℂ)+1)) * F)) =
        (((-1)^m * ((n+m).factorial:ℝ) * Real.sqrt π * rr / (2^(n+1) * x^(n+m+1)) : ℝ) : ℂ) * F := by
      rw [hE2, hE3, hG, h2, hN]
      push_cast
      field_simp
    rw [hT, mul_im, ofReal_im, ofReal_re, hF]; ring

/- DLMF 14.30(iv), including 14.30.10–13 and the angular-momentum
application discussion, is excluded under the project application-notes policy. -/

end DLMF.Legendre
