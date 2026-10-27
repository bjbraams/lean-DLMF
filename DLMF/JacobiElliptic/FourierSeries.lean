/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.PartialFractions

/-!
# Fourier and hyperbolic series of the Jacobian elliptic functions (DLMF §22.11)

With `q = jacobiNomek k = exp(-πK'/K)` and `ζ = jacobiZetak z k = πz/(2K)` as in §22.2
(DLMF 22.11, p1), the twelve Fourier series 22.11.1–22.11.12 are stated as `HasSum` over `ℕ`
for complex `z` and complex `k ∈ jacobiModulusDomain` (where `|q| < 1`); DLMF's strip conditions
`q e^{2|Im ζ|} < 1` and `q e^{|Im ζ|} < 1` become `‖q‖ e^{2|Im ζ|} < 1` and `‖q‖ e^{|Im ζ|} < 1`.
Half-integer powers are `q^{n+1/2} = exp(-(n + 1/2)πK'/K)`. Where `csc ζ`, `sec ζ`, `cot ζ`,
`tan ζ` appear, the trigonometric denominator is assumed nonzero (otherwise `z` is a pole).

22.11.13 (with the complete integral `E(k)`) and the hyperbolic series 22.11.14 are stated for
real `0 < k < 1` (complex `z`), with `E = E(k²)`, `E' = E(1 - k²)` in the parameter convention;
22.11.14 is a `HasSum` over `ℤ` away from the poles of `sn`.

The `sn, cn, cd, sd, ns, ds, dc, nc` series (22.11.1, 2, 4, 5, 7, 8, 10, 11) are proved from the
partial-fraction expansions of §22.12 by expanding each `π/sin` term geometrically and
interchanging the double series (`p3j_core`); `cd, sd, dc, nc` follow from `sn, cn, ns, ds` by
`z ↦ z + K`. The remaining statements (22.11.3, 6, 9, 12, 13, 14) are admitted; they were checked
numerically (mpmath, 2026-10-25) also for complex `k` in `jacobiModulusDomain`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

variable {k : ℂ}

/-- DLMF 22.11.1: `sn(z,k) = (2π/(Kk)) ∑_{n≥0} q^{n+1/2} sin((2n+1)ζ)/(1 - q^{2n+1})`, for `k ∈
jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E1 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiSnk_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp (2 * |(jacobiZetak z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (compEllIntKk k * k) * cexp (-(π * compEllIntKpk k /
        compEllIntKk k) * (n + 1 / 2)) * sin ((2 * n + 1) * jacobiZetak z k) / (1 -
        jacobiNomek k ^ (2 * n + 1)))
      (jacobiSnk z k) := by
  have hK := p22R1_compEllIntKk_ne_zero hk
  have hk0 := p22R1_k_ne hk
  have hτ := jacobiTauk_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * compEllIntKk k * t := ⟨z / (2 * compEllIntKk k), by field_simp⟩
  have hs := p3j_strip_of hk (c := 2) two_pos hq
  rw [p3j_zeta_eq hk]
  have h1 := (jacobiSnk_partialFractions hk (p3j_half_ne hτ hs)).1.nat_add_neg_add_one
  have h2 := p3j_core (ε := 1) (c := 1 / 2) (a := 1) (b := 1) (Or.inl rfl) hτ (by norm_num)
    (by simpa using hs) (by simp) (by simp) (S := _) (by
      convert h1 using 1; funext n; push_cast; ring_nf)
  have hnome : ∀ j : ℕ, cexp (-(π * compEllIntKpk k / compEllIntKk k) * (j + 1 / 2)) =
      cexp (π * I * jacobiTauk k * (2 * j + 1) * ((1 / 2 : ℝ) : ℂ)) := by
    intro j; congr 1; rw [jacobiTauk]; field_simp; push_cast; ring_nf; rw [Complex.I_sq]; ring
  convert h2.div_const (2 * compEllIntKk k * k) using 1
  · funext j
    rw [p3j_nome_eq hk, hnome]
    simp only [one_mul]
    rw [p3j_exp_sub, ← Complex.exp_nat_mul]
    push_cast
    ring_nf; rw [Complex.I_sq]; ring
  · field_simp

/-- DLMF 22.11.2: `cn(z,k) = (2π/(Kk)) ∑_{n≥0} q^{n+1/2} cos((2n+1)ζ)/(1 + q^{2n+1})`, for `k ∈
jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E2 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiCnk_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp (2 * |(jacobiZetak z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (compEllIntKk k * k) * cexp (-(π * compEllIntKpk k /
        compEllIntKk k) * (n + 1 / 2)) * cos ((2 * n + 1) * jacobiZetak z k) / (1 +
        jacobiNomek k ^ (2 * n + 1)))
      (jacobiCnk z k) := by
  have hK := p22R1_compEllIntKk_ne_zero hk
  have hk0 := p22R1_k_ne hk
  have hτ := jacobiTauk_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * compEllIntKk k * t := ⟨z / (2 * compEllIntKk k), by field_simp⟩
  have hs := p3j_strip_of hk (c := 2) two_pos hq
  rw [p3j_zeta_eq hk]
  have h1 := (jacobiCnk_partialFractions hk (p3j_half_ne hτ hs)).1.nat_add_neg_add_one
  have h2 := p3j_core (ε := -1) (c := 1 / 2) (a := 1) (b := -1) (Or.inr rfl) hτ (by norm_num)
    (by simpa using hs) (by simp) (by simp) (S := _) (by
      convert h1 using 1; funext n
      rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]
      simp only [zpow_natCast, pow_succ]
      push_cast
      rcases neg_one_pow_eq_or ℂ n with h | h <;> rw [h] <;> ring_nf)
  have hnome : ∀ j : ℕ, cexp (-(π * compEllIntKpk k / compEllIntKk k) * (j + 1 / 2)) =
      cexp (π * I * jacobiTauk k * (2 * j + 1) * ((1 / 2 : ℝ) : ℂ)) := by
    intro j; congr 1; rw [jacobiTauk]; field_simp; push_cast; ring_nf; rw [Complex.I_sq]; ring
  convert h2.div_const (2 * I * compEllIntKk k * k) using 1
  · funext j
    rw [p3j_nome_eq hk, hnome]
    rw [show ∀ x y : ℂ, 1 * x - -1 * y = x + y by intros; ring, p3j_exp_add,
      ← Complex.exp_nat_mul]
    push_cast
    field_simp
    ring_nf
  · field_simp

/-- DLMF 22.11.3: `dn(z,k) = π/(2K) + (2π/K) ∑_{n≥1} qⁿ cos(2nζ)/(1 + q^{2n})`, for `k ∈
jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. Admitted. -/
@[dlmf 22.11.E3 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiDnk_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp (2 * |(jacobiZetak z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / compEllIntKk k * jacobiNomek k ^ (n + 1) * cos (2 * (n + 1) *
        jacobiZetak z k) / (1 + jacobiNomek k ^ (2 * (n + 1))))
      (jacobiDnk z k - π / (2 * compEllIntKk k)) := by
  sorry

/-- DLMF 22.11.4: `cd(z,k) = (2π/(Kk)) ∑_{n≥0} (-1)ⁿ q^{n+1/2} cos((2n+1)ζ)/(1 - q^{2n+1})`, for `k
∈ jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E4 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiCdk_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp (2 * |(jacobiZetak z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (compEllIntKk k * k) * (-1) ^ n * cexp (-(π * compEllIntKpk k /
        compEllIntKk k) * (n + 1 / 2)) * cos ((2 * n + 1) * jacobiZetak z k) / (1 -
        jacobiNomek k ^ (2 * n + 1)))
      (jacobiCdk z k) := by
  have h := jacobiSnk_hasSum_fourier hk (z := z + compEllIntKk k)
    (by rwa [p3j_zeta_add_K hk, show (jacobiZetak z k + π / 2).im = (jacobiZetak z k).im by simp])
  rw [(jacobiSnk_shift hk z).1] at h
  convert h using 2 with n
  rw [p3j_zeta_add_K hk, p3j_sin_shift]; ring

/-- DLMF 22.11.5: `sd(z,k) = (2π/(Kkk')) ∑_{n≥0} (-1)ⁿ q^{n+1/2} sin((2n+1)ζ)/(1 + q^{2n+1})`, for
`k ∈ jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E5 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiSdk_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp (2 * |(jacobiZetak z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (compEllIntKk k * k * jacobiComodulusk k) * (-1) ^ n * cexp (-(π *
        compEllIntKpk k / compEllIntKk k) * (n + 1 / 2)) * sin ((2 * n + 1) * jacobiZetak z k) /
        (1 + jacobiNomek k ^ (2 * n + 1)))
      (jacobiSdk z k) := by
  have hk' := p3j_comod_ne hk
  have h := jacobiCnk_hasSum_fourier hk (z := z + compEllIntKk k)
    (by rwa [p3j_zeta_add_K hk, show (jacobiZetak z k + π / 2).im = (jacobiZetak z k).im by simp])
  rw [(jacobiCnk_shift hk z).1] at h
  convert h.div_const (-jacobiComodulusk k) using 1
  · funext n
    rw [p3j_zeta_add_K hk, p3j_cos_shift]; field_simp
  · field_simp

/-- DLMF 22.11.6: `nd(z,k) = π/(2Kk') + (2π/(Kk')) ∑_{n≥1} (-1)ⁿ qⁿ cos(2nζ)/(1 + q^{2n})`, for `k
∈ jacobiModulusDomain` and
`|q| e^{2|Im ζ|} < 1`. Admitted. -/
@[dlmf 22.11.E6 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiNdk_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp (2 * |(jacobiZetak z k).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π / (compEllIntKk k * jacobiComodulusk k) * (-1) ^ (n + 1) *
        jacobiNomek k ^ (n + 1) * cos (2 * (n + 1) * jacobiZetak z k) / (1 + jacobiNomek k ^ (2 *
        (n + 1))))
      (jacobiNdk z k - π / (2 * compEllIntKk k * jacobiComodulusk k)) := by
  sorry

/-- DLMF 22.11.7: `ns(z,k) - (π/(2K)) csc ζ = (2π/K) ∑_{n≥0} q^{2n+1} sin((2n+1)ζ)/(1 - q^{2n+1})`,
for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E7 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiNsk_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp |(jacobiZetak z k).im| < 1)
    (hζ : sin (jacobiZetak z k) ≠ 0) :
    HasSum (fun n : ℕ => 2 * π / compEllIntKk k * jacobiNomek k ^ (2 * n + 1) * sin ((2 * n + 1) *
        jacobiZetak z k) / (1 - jacobiNomek k ^ (2 * n + 1)))
      (jacobiNsk z k - π / (2 * compEllIntKk k) / sin (jacobiZetak z k)) := by
  have hK := p22R1_compEllIntKk_ne_zero hk
  have hτ := jacobiTauk_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * compEllIntKk k * t := ⟨z / (2 * compEllIntKk k), by field_simp⟩
  have hs := p3j_strip_of hk (c := 1) one_pos (by simpa using hq)
  rw [div_one, one_mul] at hs
  rw [p3j_zeta_eq hk] at hζ ⊢
  have hlat : t ∉ p3j_latt (jacobiTauk k) := by
    rintro ⟨m, n, rfl⟩
    have him : ((m : ℂ) + n * jacobiTauk k).im = n * (jacobiTauk k).im := by simp
    rw [him, abs_mul, abs_of_pos hτ] at hs
    have hn : |(n : ℝ)| < 1 := by nlinarith
    have hn0 : n = 0 := by
      rw [← Int.cast_abs] at hn
      have : |n| < 1 := by exact_mod_cast hn
      rw [abs_lt] at this; omega
    subst hn0
    apply hζ
    rw [show (π : ℂ) * ((m : ℂ) + ((0 : ℤ) : ℂ) * jacobiTauk k) = m * π by push_cast; ring]
    exact Complex.sin_int_mul_pi m
  have h1 := p3j_pair0 (p3j_hasSum_ns hk hlat)
  have h2 := p3j_core (ε := 1) (c := 1) (a := 1) (b := 1) (Or.inl rfl) hτ one_pos
    (by simpa using hs) (by simp) (by simp) (S := _)
    (by convert h1 using 1; funext n; push_cast; ring_nf)
  convert h2.div_const (2 * compEllIntKk k) using 1
  · funext j
    rw [p3j_nome_eq hk]
    simp only [one_mul]
    rw [p3j_exp_sub, ← Complex.exp_nat_mul]
    push_cast
    rw [show (π : ℂ) * I * jacobiTauk k * (2 * j + 1) * 1 = (2 * j + 1) * (π * I * jacobiTauk k) by
      ring]
    ring_nf; rw [Complex.I_sq]; ring
  · simp only [Int.cast_zero, zero_mul, sub_zero]
    field_simp

/-- DLMF 22.11.8: `ds(z,k) - (π/(2K)) csc ζ = -(2π/K) ∑_{n≥0} q^{2n+1} sin((2n+1)ζ)/(1 +
q^{2n+1})`, for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E8 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiDsk_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp |(jacobiZetak z k).im| < 1)
    (hζ : sin (jacobiZetak z k) ≠ 0) :
    HasSum (fun n : ℕ => -(2 * π / compEllIntKk k) * jacobiNomek k ^ (2 * n + 1) * sin ((2 * n +
        1) * jacobiZetak z k) / (1 + jacobiNomek k ^ (2 * n + 1)))
      (jacobiDsk z k - π / (2 * compEllIntKk k) / sin (jacobiZetak z k)) := by
  have hK := p22R1_compEllIntKk_ne_zero hk
  have hτ := jacobiTauk_im_pos hk
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * compEllIntKk k * t := ⟨z / (2 * compEllIntKk k), by field_simp⟩
  have hs := p3j_strip_of hk (c := 1) one_pos (by simpa using hq)
  rw [div_one, one_mul] at hs
  rw [p3j_zeta_eq hk] at hζ ⊢
  have hlat : t ∉ p3j_latt (jacobiTauk k) := by
    rintro ⟨m, n, rfl⟩
    have him : ((m : ℂ) + n * jacobiTauk k).im = n * (jacobiTauk k).im := by simp
    rw [him, abs_mul, abs_of_pos hτ] at hs
    have hn : |(n : ℝ)| < 1 := by nlinarith
    have hn0 : n = 0 := by
      rw [← Int.cast_abs] at hn
      have : |n| < 1 := by exact_mod_cast hn
      rw [abs_lt] at this; omega
    subst hn0
    apply hζ
    rw [show (π : ℂ) * ((m : ℂ) + ((0 : ℤ) : ℂ) * jacobiTauk k) = m * π by push_cast; ring]
    exact Complex.sin_int_mul_pi m
  have h1 := p3j_pair0 (p3j_hasSum_ds hk hlat)
  have h2 := p3j_core (ε := -1) (c := 1) (a := -1) (b := -1) (Or.inr rfl) hτ one_pos
    (by simpa using hs) (by simp) (by simp) (S := _) (by
      convert h1 using 1; funext n
      rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
        pow_succ]
      push_cast
      rcases neg_one_pow_eq_or ℂ n with h | h <;> rw [h] <;> ring_nf)
  convert h2.div_const (2 * compEllIntKk k) using 1
  · funext j
    rw [p3j_nome_eq hk]
    rw [show ∀ x y : ℂ, -1 * x - -1 * y = -(x - y) by intros; ring, p3j_exp_sub,
      ← Complex.exp_nat_mul]
    push_cast
    rw [show (π : ℂ) * I * jacobiTauk k * (2 * j + 1) * 1 = (2 * j + 1) * (π * I * jacobiTauk k) by
      ring]
    ring_nf; rw [Complex.I_sq]; ring
  · simp only [Int.cast_zero, zero_mul, sub_zero, zpow_zero, one_mul]
    field_simp

/-- DLMF 22.11.9: `cs(z,k) - (π/(2K)) cot ζ = -(2π/K) ∑_{n≥1} q^{2n} sin(2nζ)/(1 + q^{2n})`, for `k
∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). Admitted. -/
@[dlmf 22.11.E9 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiCsk_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp |(jacobiZetak z k).im| < 1)
    (hζ : sin (jacobiZetak z k) ≠ 0) :
    HasSum (fun n : ℕ => -(2 * π / compEllIntKk k) * jacobiNomek k ^ (2 * (n + 1)) * sin (2 * (n +
        1) * jacobiZetak z k) / (1 + jacobiNomek k ^ (2 * (n + 1))))
      (jacobiCsk z k - π / (2 * compEllIntKk k) * (cos (jacobiZetak z k) /
          sin (jacobiZetak z k))) := by
  sorry

/-- DLMF 22.11.10: `dc(z,k) - (π/(2K)) sec ζ = (2π/K) ∑_{n≥0} (-1)ⁿ q^{2n+1} cos((2n+1)ζ)/(1 -
q^{2n+1})`, for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E10 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiDck_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp |(jacobiZetak z k).im| < 1)
    (hζ : cos (jacobiZetak z k) ≠ 0) :
    HasSum (fun n : ℕ => 2 * π / compEllIntKk k * (-1) ^ n * jacobiNomek k ^ (2 * n + 1) *
        cos ((2 * n + 1) * jacobiZetak z k) / (1 - jacobiNomek k ^ (2 * n + 1)))
      (jacobiDck z k - π / (2 * compEllIntKk k) / cos (jacobiZetak z k)) := by
  have h := jacobiNsk_hasSum_fourier hk (z := z + compEllIntKk k)
    (by rwa [p3j_zeta_add_K hk, show (jacobiZetak z k + π / 2).im = (jacobiZetak z k).im by simp])
    (by rwa [p3j_zeta_add_K hk, Complex.sin_add_pi_div_two])
  rw [(jacobiNsk_shift hk z).1, p3j_zeta_add_K hk, Complex.sin_add_pi_div_two] at h
  convert h using 2 with n
  rw [p3j_sin_shift]; ring

/-- DLMF 22.11.11: `nc(z,k) - (π/(2Kk')) sec ζ = -(2π/(Kk')) ∑_{n≥0} (-1)ⁿ q^{2n+1} cos((2n+1)ζ)/(1
+ q^{2n+1})`, for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). -/
@[dlmf 22.11.E11 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiNck_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp |(jacobiZetak z k).im| < 1)
    (hζ : cos (jacobiZetak z k) ≠ 0) :
    HasSum (fun n : ℕ => -(2 * π / (compEllIntKk k * jacobiComodulusk k)) * (-1) ^ n *
        jacobiNomek k ^ (2 * n + 1) * cos ((2 * n + 1) * jacobiZetak z k) / (1 +
        jacobiNomek k ^ (2 * n + 1)))
      (jacobiNck z k - π / (2 * compEllIntKk k * jacobiComodulusk k) / cos (jacobiZetak z k)) := by
  have hk' := p3j_comod_ne hk
  have h := jacobiDsk_hasSum_fourier hk (z := z + compEllIntKk k)
    (by rwa [p3j_zeta_add_K hk, show (jacobiZetak z k + π / 2).im = (jacobiZetak z k).im by simp])
    (by rwa [p3j_zeta_add_K hk, Complex.sin_add_pi_div_two])
  rw [(jacobiDsk_shift hk z).1, p3j_zeta_add_K hk, Complex.sin_add_pi_div_two] at h
  convert h.div_const (jacobiComodulusk k) using 1
  · funext n
    rw [p3j_sin_shift]; field_simp
  · field_simp

/-- DLMF 22.11.12: `sc(z,k) - (π/(2Kk')) tan ζ = (2π/(Kk')) ∑_{n≥1} (-1)ⁿ q^{2n} sin(2nζ)/(1 +
q^{2n})`, for `k ∈ jacobiModulusDomain` and
`|q| e^{|Im ζ|} < 1` (and `ζ` not a zero of the trigonometric denominator). Admitted. -/
@[dlmf 22.11.E12 "domain: k ∈ jacobiModulusDomain, |q| < 1 form of the strip condition"]
theorem jacobiSck_hasSum_fourier (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hq : ‖jacobiNomek k‖ * Real.exp |(jacobiZetak z k).im| < 1)
    (hζ : cos (jacobiZetak z k) ≠ 0) :
    HasSum (fun n : ℕ => 2 * π / (compEllIntKk k * jacobiComodulusk k) * (-1) ^ (n + 1) *
        jacobiNomek k ^ (2 * (n + 1)) * sin (2 * (n + 1) * jacobiZetak z k) / (1 +
        jacobiNomek k ^ (2 * (n + 1))))
      (jacobiSck z k - π / (2 * compEllIntKk k * jacobiComodulusk k) * (sin (jacobiZetak z k) /
          cos (jacobiZetak z k))) := by
  sorry

/-- DLMF 22.11.13: `sn²(z,k) = (1 - E/K)/k² - (2π²/(k²K²)) ∑_{n≥1} n qⁿ cos(2nζ)/(1 - q^{2n})`,
for real `0 < k < 1`, `E = E(k)`, and `q e^{2|Im ζ|} < 1`. Admitted. -/
@[dlmf 22.11.E13 "special case: real 0 < k < 1 (complex E(k) not yet defined)"]
theorem jacobiSnk_sq_hasSum_fourier {κ : ℝ} (hk0 : 0 < κ) (hk1 : κ < 1) {z : ℂ}
    (hq : ‖jacobiNomek κ‖ * Real.exp (2 * |(jacobiZetak z κ).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π ^ 2 / ((κ : ℂ) ^ 2 * compEllIntKk κ ^ 2) * (n + 1) *
        jacobiNomek κ ^ (n + 1) / (1 - jacobiNomek κ ^ (2 * (n + 1))) *
          cos (2 * (n + 1) * jacobiZetak z κ))
      (1 / (κ : ℂ) ^ 2 * (1 - (DLMF.Elliptic.Real.compEllIntEm (κ ^ 2) : ℂ) / compEllIntKk κ) -
        jacobiSnk z κ ^ 2) := by
  sorry

/-- DLMF 22.11.14: the hyperbolic series
`k² sn²(z,k) = E'/K' - (π/(2K'))² ∑_{n ∈ ℤ} sech²(π(z - 2nK)/(2K'))`, for real `0 < k < 1`,
`E' = E(k')`, `K' = K(k')`, and `z` not a pole of `sn`. Admitted. -/
@[dlmf 22.11.E14 "special case: real 0 < k < 1, z not a pole"]
theorem jacobiSnk_sq_hasSum_sech {κ : ℝ} (hk0 : 0 < κ) (hk1 : κ < 1) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z κ) (jacobiTauk κ) ≠ 0) :
    HasSum (fun n : ℤ => (π / (2 * compEllIntKpk κ)) ^ 2 *
        (1 / cosh (π / (2 * compEllIntKpk κ) * (z - 2 * n * compEllIntKk κ))) ^ 2)
      ((DLMF.Elliptic.Real.compEllIntEm (1 - κ ^ 2) : ℂ) / compEllIntKpk κ -
        (κ : ℂ) ^ 2 * jacobiSnk z κ ^ 2) := by
  sorry

end DLMF.JacobiElliptic
