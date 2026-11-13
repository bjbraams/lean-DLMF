/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.PartialFractions
public import DLMF.JacobiElliptic.FourierSeries.SquaredSn
public import DLMF.JacobiElliptic.FourierSeries.HyperbolicSn

/-!
# Fourier and hyperbolic series of the Jacobian elliptic functions (DLMF §22.11)

The twelve Fourier series DLMF 22.11.1–22.11.12, the series 22.11.13 for `sn²` and the
hyperbolic series 22.11.14, with `q = jacobiNome k = exp(-πK'/K)` and
`ζ = jacobiThetaArgument z k = πz/(2K)` as in §22.2.

## Main results

* `jacobiSn_hasSum_fourier`, `jacobiCn_hasSum_fourier`, `jacobiDn_hasSum_fourier`:
  DLMF 22.11.1–22.11.3.
* `jacobiCd_hasSum_fourier`, `jacobiSd_hasSum_fourier`, `jacobiNd_hasSum_fourier`:
  DLMF 22.11.4–22.11.6.
* `jacobiNs_hasSum_fourier`, `jacobiDs_hasSum_fourier`, `jacobiCs_hasSum_fourier`:
  DLMF 22.11.7–22.11.9.
* `jacobiDc_hasSum_fourier`, `jacobiNc_hasSum_fourier`, `jacobiSc_hasSum_fourier`:
  DLMF 22.11.10–22.11.12.
* `jacobiSn_sq_hasSum_fourier`, `jacobiSn_sq_hasSum_sech`: DLMF 22.11.13 and 22.11.14 for
  real `0 < k < 1`.

## Implementation notes

The twelve Fourier series are stated as `HasSum` over `ℕ` for complex `z` and complex
`k ∈ jacobiModulusDomain` (where `|q| < 1`); DLMF's strip conditions `q e^{2|Im ζ|} < 1` and
`q e^{|Im ζ|} < 1` become `‖q‖ e^{2|Im ζ|} < 1` and `‖q‖ e^{|Im ζ|} < 1`. Half-integer powers
are `q^{n+1/2} = exp(-(n + 1/2)πK'/K)`. Where `csc ζ`, `sec ζ`, `cot ζ`, `tan ζ` appear, the
trigonometric denominator is assumed nonzero (otherwise `z` is a pole).

DLMF 22.11.13 (with the complete integral `E(k)`) and the hyperbolic series 22.11.14 are stated
for real `0 < k < 1` and complex `z`, with `E = E(k²)`, `E' = E(1 - k²)` in the parameter
convention; 22.11.14 is a `HasSum` over `ℤ` away from the poles of `sn`.

The `sn, cn, cd, sd, ns, ds, dc, nc` series are proved from the partial-fraction expansions of
§22.12 by expanding each `π/sin` term geometrically and interchanging the double series
(`hasSum_fourier_of_hasSum_pi_div_sin`); `cd, sd, dc, nc` follow from `sn, cn, ns, ds` by
`z ↦ z + K`. The `cs` and `dn` series come in the same way from the cotangent series of
`DLMF.JacobiElliptic.EisensteinCotSeries` (`hasSum_fourier_eisensteinCotSeries` and its
half-shifted form), and `sc`, `nd` follow by `z ↦ z + K`. The statements 22.11.13 and 22.11.14
have been checked numerically (mpmath), also for complex `k` in `jacobiModulusDomain`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

variable {k : ℂ}

/-- A point of the strip `|Im t| < Im τ` with `sin(πt) ≠ 0` is off the lattice. -/
private lemma not_mem_eisensteinSinLattice_of_abs_im_lt {τ t : ℂ} (hτ : 0 < τ.im)
    (ht : |t.im| < τ.im) (hs : sin (π * t) ≠ 0) : t ∉ eisensteinSinLattice τ := by
  rintro ⟨m, n, rfl⟩
  have him : ((m : ℂ) + n * τ).im = n * τ.im := by simp
  rw [him, abs_mul, abs_of_pos hτ] at ht
  have hn : |(n : ℝ)| < 1 := by nlinarith
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hn
    exact Int.abs_lt_one_iff.mp this
  subst hn0
  apply hs
  rw [Complex.sin_eq_zero_iff]
  exact ⟨m, by push_cast; ring⟩

/-- `1 + q^{2m} ≠ 0`, written with `q^{2m} = e^{2πiτm}`, `Im τ > 0`. -/
private lemma one_add_exp_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (j : ℕ) :
    1 + cexp (2 * π * I * τ * (j + 1)) ≠ 0 := by
  intro h0
  have hQ : ‖cexp (2 * π * I * τ * (j + 1))‖ = 1 := by
    rw [show cexp (2 * π * I * τ * (j + 1)) = -1 by linear_combination h0]; simp
  rw [Complex.norm_exp] at hQ
  have : (2 * π * I * τ * ((j : ℂ) + 1)).re = -(2 * π * τ.im * (j + 1)) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_eq_one_iff] at hQ
  have : 0 < 2 * π * τ.im * (j + 1) := by positivity
  linarith

/-- DLMF 22.11.1: `sn(z,k) = (2π/(Kk)) ∑_{n≥0} q^{n+1/2} sin((2n+1)ζ)/(1 - q^{2n+1})`, for `k ∈
jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E1 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiSn_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp (2 * |(jacobiThetaArgument z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (completeEllipticK k * k) * cexp (-(π * completeEllipticKPrime k /
        completeEllipticK k) * (n + 1 / 2)) * sin ((2 * n + 1) * jacobiThetaArgument z k) / (1 -
        jacobiNome k ^ (2 * n + 1)))
      (jacobiSn z k) := by
  have hK := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hk0 := ne_zero_of_mem_jacobiModulusDomain hk
  have hτ := jacobiTau_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * completeEllipticK k * t :=
      ⟨z / (2 * completeEllipticK k), by field_simp⟩
  have hs := abs_im_lt_of_norm_jacobiNome_mul_exp_lt hk (c := 2) two_pos hq
  rw [jacobiThetaArgument_two_mul_completeEllipticK_mul hk]
  have h1 := (jacobiSn_partialFractions hk
      (sub_intCast_sub_half_mul_ne_zero hτ hs)).1.nat_add_neg_add_one
  have h2 := hasSum_fourier_of_hasSum_pi_div_sin (ε := 1) (c := 1 / 2) (a := 1) (b := 1)
      (Or.inl rfl) hτ
    (by simpa using hs) (by simp) (by simp) (S := _) (by
      convert h1 using 1; funext n; push_cast; ring_nf)
  have hnome : ∀ j : ℕ, cexp (-(π * completeEllipticKPrime k / completeEllipticK k) * (j + 1 / 2)) =
      cexp (π * I * jacobiTau k * (2 * j + 1) * ((1 / 2 : ℝ) : ℂ)) := by
    intro j; congr 1; rw [jacobiTau]; field_simp; push_cast; ring_nf; rw [Complex.I_sq]; ring
  convert h2.div_const (2 * completeEllipticK k * k) using 1
  · funext j
    rw [jacobiNome_eq_exp_jacobiTau hk, hnome]
    simp only [one_mul]
    rw [exp_neg_sub_exp_eq_neg_two_mul_I_mul_sin, ← Complex.exp_nat_mul]
    push_cast
    ring_nf; rw [Complex.I_sq]; ring
  · field_simp

/-- DLMF 22.11.2: `cn(z,k) = (2π/(Kk)) ∑_{n≥0} q^{n+1/2} cos((2n+1)ζ)/(1 + q^{2n+1})`, for `k ∈
jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E2 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiCn_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp (2 * |(jacobiThetaArgument z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (completeEllipticK k * k) * cexp (-(π * completeEllipticKPrime k /
        completeEllipticK k) * (n + 1 / 2)) * cos ((2 * n + 1) * jacobiThetaArgument z k) / (1 +
        jacobiNome k ^ (2 * n + 1)))
      (jacobiCn z k) := by
  have hK := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hk0 := ne_zero_of_mem_jacobiModulusDomain hk
  have hτ := jacobiTau_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * completeEllipticK k * t :=
      ⟨z / (2 * completeEllipticK k), by field_simp⟩
  have hs := abs_im_lt_of_norm_jacobiNome_mul_exp_lt hk (c := 2) two_pos hq
  rw [jacobiThetaArgument_two_mul_completeEllipticK_mul hk]
  have h1 := (jacobiCn_partialFractions hk
      (sub_intCast_sub_half_mul_ne_zero hτ hs)).1.nat_add_neg_add_one
  have h2 := hasSum_fourier_of_hasSum_pi_div_sin (ε := -1) (c := 1 / 2) (a := 1) (b := -1)
      (Or.inr rfl) hτ
    (by simpa using hs) (by simp) (by simp) (S := _) (by
      convert h1 using 1; funext n
      rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]
      simp only [zpow_natCast, pow_succ]
      push_cast
      rcases neg_one_pow_eq_or ℂ n with h | h <;> rw [h] <;> ring_nf)
  have hnome : ∀ j : ℕ, cexp (-(π * completeEllipticKPrime k / completeEllipticK k) * (j + 1 / 2)) =
      cexp (π * I * jacobiTau k * (2 * j + 1) * ((1 / 2 : ℝ) : ℂ)) := by
    intro j; congr 1; rw [jacobiTau]; field_simp; push_cast; ring_nf; rw [Complex.I_sq]; ring
  convert h2.div_const (2 * I * completeEllipticK k * k) using 1
  · funext j
    rw [jacobiNome_eq_exp_jacobiTau hk, hnome]
    rw [show ∀ x y : ℂ, 1 * x - -1 * y = x + y by intros; ring, exp_neg_add_exp_eq_two_mul_cos,
      ← Complex.exp_nat_mul]
    push_cast
    field_simp
    ring_nf
  · field_simp

/-- DLMF 22.11.3: `dn(z,k) = π/(2K) + (2π/K) ∑_{n≥1} qⁿ cos(2nζ)/(1 + q^{2n})`, for `k ∈
jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E3 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiDn_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp (2 * |(jacobiThetaArgument z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / completeEllipticK k * jacobiNome k ^ (n + 1) * cos (2 * (n + 1) *
        jacobiThetaArgument z k) / (1 + jacobiNome k ^ (2 * (n + 1))))
      (jacobiDn z k - π / (2 * completeEllipticK k)) := by
  have hK := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hτ := jacobiTau_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * completeEllipticK k * t :=
      ⟨z / (2 * completeEllipticK k), by field_simp⟩
  have hs := abs_im_lt_of_norm_jacobiNome_mul_exp_lt hk (c := 2) two_pos hq
  have hab := abs_lt.mp hs
  rw [jacobiThetaArgument_two_mul_completeEllipticK_mul hk]
  have hl : t - jacobiTau k / 2 ∉ eisensteinSinLattice (jacobiTau k) := by
    rintro ⟨m, n, hmn⟩
    have him := congrArg Complex.im hmn
    simp at him
    rcases le_or_gt n (-1) with hn | hn
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast hn
      nlinarith
    · have : (0 : ℝ) ≤ n := by exact_mod_cast (show (0 : ℤ) ≤ n by omega)
      nlinarith
  have h := hasSum_fourier_eisensteinCotSeries_sub_half (ε := -1) (Or.inr rfl) hτ (t := t)
    (by linarith)
  rw [← jacobiCs_eq_eisensteinCotSeries hk hl] at h
  have h2 := two_mul_completeEllipticK_mul_jacobiTau hk
  have hv : 2 * completeEllipticK k * jacobiCs (2 * completeEllipticK k * (t - jacobiTau k / 2)) k =
      2 * I * completeEllipticK k * jacobiDn (2 * completeEllipticK k * t) k := by
    rw [show 2 * completeEllipticK k * t =
      2 * completeEllipticK k * (t - jacobiTau k / 2) + I * completeEllipticKPrime k by
      linear_combination h2 / 2, (jacobiDn_shift hk _).2.2.1]
    ring_nf; rw [I_sq]; ring
  rw [hv] at h
  convert h.div_const (2 * I * completeEllipticK k) using 1
  · funext j
    have h1 := one_add_exp_ne_zero hτ j
    rw [jacobiNome_eq_exp_jacobiTau hk, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      show (2 * π * I * ((j : ℂ) + 1) * t) = π * I * (2 * (j + 1)) * t by ring,
      show ∀ x y : ℂ, x - -1 * y = x + y by intros; ring, exp_neg_add_exp_eq_two_mul_cos]
    simp only [neg_one_mul, sub_neg_eq_add]
    push_cast
    rw [show ((j : ℂ) + 1) * (π * I * jacobiTau k) = π * I * jacobiTau k * (j + 1) by ring,
      show (2 * ((j : ℂ) + 1)) * (π * I * jacobiTau k) = 2 * π * I * jacobiTau k * (j + 1) by
        ring]
    field_simp
  · field_simp

/-- DLMF 22.11.4: `cd(z,k) = (2π/(Kk)) ∑_{n≥0} (-1)ⁿ q^{n+1/2} cos((2n+1)ζ)/(1 - q^{2n+1})`, for `k
∈ jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E4 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiCd_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp (2 * |(jacobiThetaArgument z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (completeEllipticK k * k) * (-1) ^ n *
        cexp (-(π * completeEllipticKPrime k /
        completeEllipticK k) * (n + 1 / 2)) * cos ((2 * n + 1) * jacobiThetaArgument z k) / (1 -
        jacobiNome k ^ (2 * n + 1)))
      (jacobiCd z k) := by
  have h := jacobiSn_hasSum_fourier hk (z := z + completeEllipticK k)
    (by rwa [jacobiThetaArgument_add_completeEllipticK hk,
          show (jacobiThetaArgument z k + π / 2).im =
          (jacobiThetaArgument z k).im by simp])
  rw [(jacobiSn_shift hk z).1] at h
  convert h using 2 with n
  rw [jacobiThetaArgument_add_completeEllipticK hk, sin_odd_mul_add_pi_div_two]; ring

/-- DLMF 22.11.5: `sd(z,k) = (2π/(Kkk')) ∑_{n≥0} (-1)ⁿ q^{n+1/2} sin((2n+1)ζ)/(1 + q^{2n+1})`, for
`k ∈ jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E5 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiSd_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp (2 * |(jacobiThetaArgument z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (completeEllipticK k * k * jacobiComodulus k) *
        (-1) ^ n * cexp (-(π *
        completeEllipticKPrime k / completeEllipticK k) * (n + 1 / 2)) *
            sin ((2 * n + 1) * jacobiThetaArgument z k) /
        (1 + jacobiNome k ^ (2 * n + 1)))
      (jacobiSd z k) := by
  have hk' := jacobiComodulus_ne_zero hk
  have h := jacobiCn_hasSum_fourier hk (z := z + completeEllipticK k)
    (by rwa [jacobiThetaArgument_add_completeEllipticK hk,
          show (jacobiThetaArgument z k + π / 2).im =
          (jacobiThetaArgument z k).im by simp])
  rw [(jacobiCn_shift hk z).1] at h
  convert h.div_const (-jacobiComodulus k) using 1
  · funext n
    rw [jacobiThetaArgument_add_completeEllipticK hk, cos_odd_mul_add_pi_div_two]; field_simp
  · field_simp

/-- DLMF 22.11.6: `nd(z,k) = π/(2Kk') + (2π/(Kk')) ∑_{n≥1} (-1)ⁿ qⁿ cos(2nζ)/(1 + q^{2n})`, for `k
∈ jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E6 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiNd_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp (2 * |(jacobiThetaArgument z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (completeEllipticK k * jacobiComodulus k) * (-1) ^ (n + 1) *
        jacobiNome k ^ (n + 1) * cos (2 * (n + 1) * jacobiThetaArgument z k) /
            (1 + jacobiNome k ^ (2 *
        (n + 1))))
      (jacobiNd z k - π / (2 * completeEllipticK k * jacobiComodulus k)) := by
  have hk' := jacobiComodulus_ne_zero hk
  have h := jacobiDn_hasSum_fourier hk (z := z + completeEllipticK k)
    (by rwa [jacobiThetaArgument_add_completeEllipticK hk,
          show (jacobiThetaArgument z k + π / 2).im =
          (jacobiThetaArgument z k).im by simp])
  rw [(jacobiDn_shift hk z).1, jacobiThetaArgument_add_completeEllipticK hk] at h
  convert h.div_const (jacobiComodulus k) using 1
  · funext n
    rw [show 2 * ((n : ℂ) + 1) * (jacobiThetaArgument z k + π / 2) =
      2 * (n + 1) * jacobiThetaArgument z k + ((n + 1 : ℕ) : ℂ) * π by push_cast; ring,
      (sin_cos_add_nat_mul_pi _ _).2]
    field_simp
  · field_simp

/-- DLMF 22.11.7: `ns(z,k) - (π/(2K)) csc ζ = (2π/K) ∑_{n≥0} q^{2n+1} sin((2n+1)ζ)/(1 - q^{2n+1})`,
for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E7 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiNs_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp |(jacobiThetaArgument z k).im| < 1)
    (hζ : sin (jacobiThetaArgument z k) ≠ 0) :
    HasSum (fun n : ℕ => 2 * π / completeEllipticK k * jacobiNome k ^ (2 * n + 1) *
        sin ((2 * n + 1) *
        jacobiThetaArgument z k) / (1 - jacobiNome k ^ (2 * n + 1)))
      (jacobiNs z k - π / (2 * completeEllipticK k) / sin (jacobiThetaArgument z k)) := by
  have hK := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hτ := jacobiTau_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * completeEllipticK k * t :=
      ⟨z / (2 * completeEllipticK k), by field_simp⟩
  have hs := abs_im_lt_of_norm_jacobiNome_mul_exp_lt hk (c := 1) one_pos (by simpa using hq)
  rw [div_one, one_mul] at hs
  rw [jacobiThetaArgument_two_mul_completeEllipticK_mul hk] at hζ ⊢
  have hlat : t ∉ eisensteinSinLattice (jacobiTau k) := by
    rintro ⟨m, n, rfl⟩
    have him : ((m : ℂ) + n * jacobiTau k).im = n * (jacobiTau k).im := by simp
    rw [him, abs_mul, abs_of_pos hτ] at hs
    have hn : |(n : ℝ)| < 1 := by nlinarith
    have hn0 : n = 0 := by
      rw [← Int.cast_abs] at hn
      have : |n| < 1 := by exact_mod_cast hn
      rw [abs_lt] at this; omega
    subst hn0
    apply hζ
    rw [show (π : ℂ) * ((m : ℂ) + ((0 : ℤ) : ℂ) * jacobiTau k) = m * π by push_cast; ring]
    exact Complex.sin_int_mul_pi m
  have h1 := hasSum_nat_add_neg_succ_of_hasSum (hasSum_pi_div_sin_jacobiNs hk hlat)
  have h2 := hasSum_fourier_of_hasSum_pi_div_sin (ε := 1) (c := 1) (a := 1) (b := 1) (Or.inl rfl) hτ
    (by simpa using hs) (by simp) (by simp) (S := _)
    (by convert h1 using 1; funext n; push_cast; ring_nf)
  convert h2.div_const (2 * completeEllipticK k) using 1
  · funext j
    rw [jacobiNome_eq_exp_jacobiTau hk]
    simp only [one_mul]
    rw [exp_neg_sub_exp_eq_neg_two_mul_I_mul_sin, ← Complex.exp_nat_mul]
    push_cast
    rw [show (π : ℂ) * I * jacobiTau k * (2 * j + 1) * 1 = (2 * j + 1) * (π * I * jacobiTau k) by
      ring]
    ring_nf; rw [Complex.I_sq]; ring
  · simp only [Int.cast_zero, zero_mul, sub_zero]
    field_simp

/-- DLMF 22.11.8: `ds(z,k) - (π/(2K)) csc ζ = -(2π/K) ∑_{n≥0} q^{2n+1} sin((2n+1)ζ)/(1 +
q^{2n+1})`, for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E8 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiDs_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp |(jacobiThetaArgument z k).im| < 1)
    (hζ : sin (jacobiThetaArgument z k) ≠ 0) :
    HasSum (fun n : ℕ => -(2 * π / completeEllipticK k) * jacobiNome k ^ (2 * n + 1) * sin ((2 * n +
        1) * jacobiThetaArgument z k) / (1 + jacobiNome k ^ (2 * n + 1)))
      (jacobiDs z k - π / (2 * completeEllipticK k) / sin (jacobiThetaArgument z k)) := by
  have hK := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hτ := jacobiTau_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * completeEllipticK k * t :=
      ⟨z / (2 * completeEllipticK k), by field_simp⟩
  have hs := abs_im_lt_of_norm_jacobiNome_mul_exp_lt hk (c := 1) one_pos (by simpa using hq)
  rw [div_one, one_mul] at hs
  rw [jacobiThetaArgument_two_mul_completeEllipticK_mul hk] at hζ ⊢
  have hlat : t ∉ eisensteinSinLattice (jacobiTau k) := by
    rintro ⟨m, n, rfl⟩
    have him : ((m : ℂ) + n * jacobiTau k).im = n * (jacobiTau k).im := by simp
    rw [him, abs_mul, abs_of_pos hτ] at hs
    have hn : |(n : ℝ)| < 1 := by nlinarith
    have hn0 : n = 0 := by
      rw [← Int.cast_abs] at hn
      have : |n| < 1 := by exact_mod_cast hn
      rw [abs_lt] at this; omega
    subst hn0
    apply hζ
    rw [show (π : ℂ) * ((m : ℂ) + ((0 : ℤ) : ℂ) * jacobiTau k) = m * π by push_cast; ring]
    exact Complex.sin_int_mul_pi m
  have h1 := hasSum_nat_add_neg_succ_of_hasSum (hasSum_neg_one_zpow_pi_div_sin_jacobiDs hk hlat)
  have h2 := hasSum_fourier_of_hasSum_pi_div_sin (ε := -1) (c := 1) (a := -1) (b := -1)
      (Or.inr rfl) hτ
    (by simpa using hs) (by simp) (by simp) (S := _) (by
      convert h1 using 1; funext n
      rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
        pow_succ]
      push_cast
      rcases neg_one_pow_eq_or ℂ n with h | h <;> rw [h] <;> ring_nf)
  convert h2.div_const (2 * completeEllipticK k) using 1
  · funext j
    rw [jacobiNome_eq_exp_jacobiTau hk]
    rw [show ∀ x y : ℂ, -1 * x - -1 * y = -(x - y) by intros; ring,
                                                        exp_neg_sub_exp_eq_neg_two_mul_I_mul_sin,
      ← Complex.exp_nat_mul]
    push_cast
    rw [show (π : ℂ) * I * jacobiTau k * (2 * j + 1) * 1 = (2 * j + 1) * (π * I * jacobiTau k) by
      ring]
    ring_nf; rw [Complex.I_sq]; ring
  · simp only [Int.cast_zero, zero_mul, sub_zero, zpow_zero, one_mul]
    field_simp

/-- DLMF 22.11.9: `cs(z,k) - (π/(2K)) cot ζ = -(2π/K) ∑_{n≥1} q^{2n} sin(2nζ)/(1 + q^{2n})`, for `k
∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E9 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiCs_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp |(jacobiThetaArgument z k).im| < 1)
    (hζ : sin (jacobiThetaArgument z k) ≠ 0) :
    HasSum (fun n : ℕ => -(2 * π / completeEllipticK k) *
        jacobiNome k ^ (2 * (n + 1)) * sin (2 * (n +
        1) * jacobiThetaArgument z k) / (1 + jacobiNome k ^ (2 * (n + 1))))
      (jacobiCs z k - π / (2 * completeEllipticK k) * (cos (jacobiThetaArgument z k) /
          sin (jacobiThetaArgument z k))) := by
  have hK := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hτ := jacobiTau_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * completeEllipticK k * t :=
      ⟨z / (2 * completeEllipticK k), by field_simp⟩
  have hs := abs_im_lt_of_norm_jacobiNome_mul_exp_lt hk (c := 1) one_pos (by simpa using hq)
  rw [div_one, one_mul] at hs
  rw [jacobiThetaArgument_two_mul_completeEllipticK_mul hk] at hζ ⊢
  have hl := not_mem_eisensteinSinLattice_of_abs_im_lt hτ hs hζ
  have h := hasSum_fourier_eisensteinCotSeries (ε := -1) (Or.inr rfl) hτ hs
  rw [← jacobiCs_eq_eisensteinCotSeries hk hl] at h
  convert h.div_const (2 * completeEllipticK k) using 1
  · funext j
    rw [jacobiNome_eq_exp_jacobiTau hk, ← Complex.exp_nat_mul,
      show (2 * π * I * ((j : ℂ) + 1) * t) = π * I * (2 * (j + 1)) * t by ring,
      exp_neg_sub_exp_eq_neg_two_mul_I_mul_sin]
    have h1 : ((2 * (j + 1) : ℕ) : ℂ) * (π * I * jacobiTau k) =
        2 * π * I * jacobiTau k * (j + 1) := by
      push_cast; ring
    rw [h1]
    have h2 := one_add_exp_ne_zero hτ j
    simp only [neg_one_mul, sub_neg_eq_add]
    field_simp
    ring_nf; rw [I_sq]; ring_nf
  · rw [Complex.cot_eq_cos_div_sin]; field_simp

/-- DLMF 22.11.10: `dc(z,k) - (π/(2K)) sec ζ = (2π/K) ∑_{n≥0} (-1)ⁿ q^{2n+1} cos((2n+1)ζ)/(1 -
q^{2n+1})`, for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E10 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiDc_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp |(jacobiThetaArgument z k).im| < 1)
    (hζ : cos (jacobiThetaArgument z k) ≠ 0) :
    HasSum (fun n : ℕ => 2 * π / completeEllipticK k * (-1) ^ n * jacobiNome k ^ (2 * n + 1) *
        cos ((2 * n + 1) * jacobiThetaArgument z k) / (1 - jacobiNome k ^ (2 * n + 1)))
      (jacobiDc z k - π / (2 * completeEllipticK k) / cos (jacobiThetaArgument z k)) := by
  have h := jacobiNs_hasSum_fourier hk (z := z + completeEllipticK k)
    (by rwa [jacobiThetaArgument_add_completeEllipticK hk,
          show (jacobiThetaArgument z k + π / 2).im =
          (jacobiThetaArgument z k).im by simp])
    (by rwa [jacobiThetaArgument_add_completeEllipticK hk, Complex.sin_add_pi_div_two])
  rw [(jacobiNs_shift hk z).1, jacobiThetaArgument_add_completeEllipticK hk,
      Complex.sin_add_pi_div_two] at h
  convert h using 2 with n
  rw [sin_odd_mul_add_pi_div_two]; ring

/-- DLMF 22.11.11: `nc(z,k) - (π/(2Kk')) sec ζ = -(2π/(Kk')) ∑_{n≥0} (-1)ⁿ q^{2n+1} cos((2n+1)ζ)/(1
+ q^{2n+1})`, for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E11 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiNc_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp |(jacobiThetaArgument z k).im| < 1)
    (hζ : cos (jacobiThetaArgument z k) ≠ 0) :
    HasSum (fun n : ℕ => -(2 * π / (completeEllipticK k * jacobiComodulus k)) * (-1) ^ n *
        jacobiNome k ^ (2 * n + 1) * cos ((2 * n + 1) * jacobiThetaArgument z k) / (1 +
        jacobiNome k ^ (2 * n + 1)))
      (jacobiNc z k - π / (2 * completeEllipticK k * jacobiComodulus k) /
          cos (jacobiThetaArgument z k)) := by
  have hk' := jacobiComodulus_ne_zero hk
  have h := jacobiDs_hasSum_fourier hk (z := z + completeEllipticK k)
    (by rwa [jacobiThetaArgument_add_completeEllipticK hk,
          show (jacobiThetaArgument z k + π / 2).im =
          (jacobiThetaArgument z k).im by simp])
    (by rwa [jacobiThetaArgument_add_completeEllipticK hk, Complex.sin_add_pi_div_two])
  rw [(jacobiDs_shift hk z).1, jacobiThetaArgument_add_completeEllipticK hk,
      Complex.sin_add_pi_div_two] at h
  convert h.div_const (jacobiComodulus k) using 1
  · funext n
    rw [sin_odd_mul_add_pi_div_two]; field_simp
  · field_simp

/-- DLMF 22.11.12: `sc(z,k) - (π/(2Kk')) tan ζ = (2π/(Kk')) ∑_{n≥1} (-1)ⁿ q^{2n} sin(2nζ)/(1 +
q^{2n})`, for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E12 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiSc_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNome k‖ * Real.exp |(jacobiThetaArgument z k).im| < 1)
    (hζ : cos (jacobiThetaArgument z k) ≠ 0) :
    HasSum (fun n : ℕ => 2 * π / (completeEllipticK k * jacobiComodulus k) * (-1) ^ (n + 1) *
        jacobiNome k ^ (2 * (n + 1)) * sin (2 * (n + 1) * jacobiThetaArgument z k) / (1 +
        jacobiNome k ^ (2 * (n + 1))))
      (jacobiSc z k - π / (2 * completeEllipticK k * jacobiComodulus k) *
          (sin (jacobiThetaArgument z k) /
          cos (jacobiThetaArgument z k))) := by
  have hk' := jacobiComodulus_ne_zero hk
  have h := jacobiCs_hasSum_fourier hk (z := z + completeEllipticK k)
    (by rwa [jacobiThetaArgument_add_completeEllipticK hk,
          show (jacobiThetaArgument z k + π / 2).im =
          (jacobiThetaArgument z k).im by simp])
    (by rwa [jacobiThetaArgument_add_completeEllipticK hk, Complex.sin_add_pi_div_two])
  rw [(jacobiCs_shift hk z).1, jacobiThetaArgument_add_completeEllipticK hk,
      Complex.sin_add_pi_div_two,
    Complex.cos_add_pi_div_two] at h
  convert h.div_const (-jacobiComodulus k) using 1
  · funext n
    rw [show 2 * ((n : ℂ) + 1) * (jacobiThetaArgument z k + π / 2) =
      2 * (n + 1) * jacobiThetaArgument z k + ((n + 1 : ℕ) : ℂ) * π by push_cast; ring,
      (sin_cos_add_nat_mul_pi _ _).1]
    field_simp
  · field_simp
    ring

end DLMF.JacobiElliptic
