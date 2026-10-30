/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.IntegralTools
public import DLMF.Airy.Scorer
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra

/-!
# Scorer exponential and integrated asymptotics, DLMF §9.12

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology
namespace DLMF.Airy

/-- The principal logarithm of a rotated point, when no branch cut is crossed. -/
theorem scorerTwo_log_mul_exp {z : ℂ} (hz : z ≠ 0) {c : ℝ} (h1 : -π < arg z + c)
    (h2 : arg z + c ≤ π) : log (z * exp (c * I)) = log z + c * I := by
  rw [Complex.log, Complex.log, Complex.arg_mul_exp_ofReal_mul_I hz h1 h2, norm_mul,
    norm_exp_ofReal_mul_I, mul_one]
  push_cast; ring

/-- Principal powers of a rotated point, when no branch cut is crossed. -/
theorem scorerTwo_cpow_mul_exp {z : ℂ} (hz : z ≠ 0) {c : ℝ} (h1 : -π < arg z + c)
    (h2 : arg z + c ≤ π) (s : ℂ) : (z * exp (c * I)) ^ s = z ^ s * exp (s * c * I) := by
  rw [cpow_def_of_ne_zero (mul_ne_zero hz (exp_ne_zero _)), cpow_def_of_ne_zero hz,
    scorerTwo_log_mul_exp hz h1 h2, ← Complex.exp_add]
  ring_nf

/-- Rotation by `c` maps a subset `S` of the sector `|arg z| ≤ α` into the sector
`|arg z| ≤ β` when `|arg z + c| ≤ β < π` on `S`. -/
theorem scorerTwo_tendsto {α β c : ℝ} {S : Set ℂ}
    (h : ∀ z ∈ S, z ≠ 0 → |arg z| ≤ α → |arg z + c| ≤ β) (hβ : β < π) :
    Tendsto (fun z : ℂ => z * exp (c * I)) (airySector α ⊓ 𝓟 S) (airySector β) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · refine (tendsto_comap.mono_left (inf_le_left.trans inf_le_left)).congr fun z => ?_
    simp only [Function.comp_apply, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  · have hA : ∀ᶠ z in airySector α, z ≠ 0 ∧ |arg z| ≤ α := mem_inf_of_right (mem_principal_self _)
    have hS : ∀ᶠ z in airySector α ⊓ 𝓟 S, z ∈ S := mem_inf_of_right (mem_principal_self S)
    filter_upwards [hA.filter_mono inf_le_left, hS] with z ⟨hz0, hz⟩ hzS
    have hb := h z hzS hz0 hz
    refine ⟨mul_ne_zero hz0 (exp_ne_zero _), ?_⟩
    have := abs_le.mp hb
    rw [Complex.arg_mul_exp_ofReal_mul_I hz0 (by linarith) (by linarith)]; exact hb

/-- Eventual membership facts on a half-sector. -/
theorem scorerTwo_eventually {α ε : ℝ} :
    ∀ᶠ z in airySector α ⊓ 𝓟 {z : ℂ | 0 ≤ ε * arg z}, z ≠ 0 ∧ |arg z| ≤ α ∧ 0 ≤ ε * arg z := by
  have hA : ∀ᶠ z in airySector α, z ≠ 0 ∧ |arg z| ≤ α := mem_inf_of_right (mem_principal_self _)
  have hS : ∀ᶠ z in airySector α ⊓ 𝓟 {z : ℂ | 0 ≤ ε * arg z}, 0 ≤ ε * arg z :=
    mem_inf_of_right (mem_principal_self _)
  filter_upwards [hA.filter_mono inf_le_left, hS] with z h1 h2 using ⟨h1.1, h1.2, h2⟩

/-- On the half-sector `0 ≤ ε arg z` (`ε = ±1`), `arg z = ε |arg z|`. -/
private lemma scorerTwo_arg_eq {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z : ℂ} (hS : 0 ≤ ε * arg z) :
    arg z = ε * |arg z| := by
  rcases hε with rfl | rfl
  · rw [one_mul] at hS; rw [abs_of_nonneg hS]; ring
  · have : arg z ≤ 0 := by linarith
    rw [abs_of_nonpos this]; ring

/-- On the half-sector `0 ≤ ε arg z`, rotating by `-ε a` gives `|arg z - ε a| = ||arg z| - a|`. -/
private lemma scorerTwo_abs_rot {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z : ℂ} (hS : 0 ≤ ε * arg z)
    (a : ℝ) : |arg z + -ε * a| = |(|arg z| - a)| := by
  have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h := scorerTwo_arg_eq hε hS
  calc |arg z + -ε * a| = |ε * (|arg z| - a)| := by congr 1; linear_combination h
    _ = _ := by rw [abs_mul, habs, one_mul]

/-- The rotation constants of 9.12.14 for `ε = ±1`, with `ω = e^{2πiε/3}`, `c' = -επ/3` and
`d = -2πε/3`: `ω = -e^{ic'}`, `ω³ = 1`, `e^{id/4} = e^{-πiε/6}`, `e^{3id/2} = -1` and
`e^{-2πiε/3} = e^{id}`. -/
private lemma scorerTwo_consts {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    exp (ε * (2 * π * I / 3)) = -exp (((-ε * (π / 3) : ℝ) : ℂ) * I) ∧
      exp (ε * (2 * π * I / 3)) ^ 3 = 1 ∧
      exp ((1 / 4 : ℂ) * ((-ε * (2 * π / 3) : ℝ) : ℂ) * I) = exp (-ε * (π * I / 6)) ∧
      exp ((3 / 2 : ℂ) * ((-ε * (2 * π / 3) : ℝ) : ℂ) * I) = -1 ∧
      exp (-ε * (2 * π * I / 3)) = exp (((-ε * (2 * π / 3) : ℝ) : ℂ) * I) := by
  refine ⟨?_, ?_, by congr 1; push_cast; ring, ?_, by congr 1; push_cast; ring⟩
  · rcases hε with rfl | rfl
    · rw [show ((1 : ℝ) : ℂ) * (2 * π * I / 3) = ((-1 * (π / 3) : ℝ) : ℂ) * I + π * I by
        push_cast; ring, Complex.exp_add, exp_pi_mul_I]; ring
    · rw [show ((-1 : ℝ) : ℂ) * (2 * π * I / 3) = ((- -1 * (π / 3) : ℝ) : ℂ) * I - π * I by
        push_cast; ring, Complex.exp_sub, exp_pi_mul_I]; ring
  · rw [← Complex.exp_nat_mul]
    rcases hε with rfl | rfl
    · rw [show ((3 : ℕ) : ℂ) * (((1 : ℝ) : ℂ) * (2 * π * I / 3)) = 2 * π * I by push_cast; ring,
        exp_two_pi_mul_I]
    · rw [show ((3 : ℕ) : ℂ) * (((-1 : ℝ) : ℂ) * (2 * π * I / 3)) = -(2 * π * I) by
        push_cast; ring, Complex.exp_neg, exp_two_pi_mul_I, inv_one]
  · rcases hε with rfl | rfl
    · rw [show (3 / 2 : ℂ) * ((-1 * (2 * π / 3) : ℝ) : ℂ) * I = -(π * I) by push_cast; ring,
        Complex.exp_neg, exp_pi_mul_I]; norm_num
    · rw [show (3 / 2 : ℂ) * ((- -1 * (2 * π / 3) : ℝ) : ℂ) * I = π * I by push_cast; ring,
        exp_pi_mul_I]

/-- On the half-sector `0 ≤ ε arg z` of `|arg z| ≤ π - δ`, rotation by `d = -2πε/3` turns the
`Ai` prefactor into the `Bi` prefactor, `2 e^{-πiε/6} P_Ai(z e^{id}) = P_Bi(z)`, and reverses
`ζ`. -/
private lemma scorerTwo_pref {ε δ : ℝ} (hε : ε = 1 ∨ ε = -1) (hδ : 0 < δ) {z : ℂ} (hz0 : z ≠ 0)
    (hz : |arg z| ≤ π - δ) (hS : 0 ≤ ε * arg z) :
    2 * exp (-ε * (π * I / 6)) *
        airyPrefactor .ai (z * exp (((-ε * (2 * π / 3) : ℝ) : ℂ) * I)) = airyPrefactor .bi z ∧
      airyZetaComplex (z * exp (((-ε * (2 * π / 3) : ℝ) : ℂ) * I)) = -airyZetaComplex z := by
  have hπ := Real.pi_pos
  obtain ⟨-, -, hdq, hdh, -⟩ := scorerTwo_consts hε
  have hb : |arg z + -ε * (2 * π / 3)| ≤ 2 * π / 3 := by
    rw [scorerTwo_abs_rot hε hS, abs_le]
    constructor <;> linarith [abs_nonneg (arg z)]
  have hb := abs_le.mp hb
  have e1 := scorerTwo_cpow_mul_exp hz0 (c := -ε * (2 * π / 3)) (by linarith) (by linarith)
  have hz4 : z ^ (1 / 4 : ℂ) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  have hzeta : airyZetaComplex (z * exp (((-ε * (2 * π / 3) : ℝ) : ℂ) * I)) =
      -airyZetaComplex z := by
    rw [airyZetaComplex, airyZetaComplex, e1, hdh]; ring
  refine ⟨?_, hzeta⟩
  rw [airyPrefactor, airyPrefactor, hzeta, neg_neg, e1, hdq]
  have : exp (-ε * (π * I / 6)) ≠ 0 := exp_ne_zero _
  have : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hπ).ne'
  field_simp

/-- DLMF 9.12.29 on the half-sector `0 ≤ ε arg z`, for `δ ≤ π/3`. -/
theorem scorerTwo_half {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {δ : ℝ} (hδ : 0 < δ) (hδ3 : δ ≤ π / 3)
    (N M : ℕ) :
    IsBigO (airySector (π - δ) ⊓ 𝓟 {z : ℂ | 0 ≤ ε * arg z})
      (fun z => scorerHi z + (1 / (π * z) *
        ∑ k ∈ Finset.range N, ((3 * k).factorial : ℂ) / (k.factorial * (3 * z ^ 3) ^ k)) -
          airyPrefactor .bi z * airyExponentialSum .bi M z)
      (fun z => ‖z‖ ^ (-(3 * N + 1 : ℤ)) + ‖airyPrefactor .bi z / airyZetaComplex z ^ M‖) := by
  have hπ := Real.pi_pos
  set F := airySector (π - δ) ⊓ 𝓟 {z : ℂ | 0 ≤ ε * arg z} with hF
  obtain ⟨hωc, hω3, -, -, hdω⟩ := scorerTwo_consts hε
  set c' : ℝ := -ε * (π / 3) with hc'
  set d : ℝ := -ε * (2 * π / 3) with hd
  have ang1 : ∀ z : ℂ, 0 ≤ ε * arg z → |arg z| ≤ π - δ → |arg z + c'| ≤ 2 * π / 3 - δ := by
    intro z hS hz
    rw [hc', scorerTwo_abs_rot hε hS, abs_le]
    constructor <;> linarith [abs_nonneg (arg z)]
  have ang2 : ∀ z : ℂ, 0 ≤ ε * arg z → |arg z| ≤ π - δ → |arg z + d| ≤ 2 * π / 3 := by
    intro z hS hz
    rw [hd, scorerTwo_abs_rot hε hS, abs_le]
    constructor <;> linarith [abs_nonneg (arg z)]
  have T1 : Tendsto (fun z : ℂ => z * exp (c' * I)) F (airySector (2 * π / 3 - δ)) :=
    scorerTwo_tendsto (fun z hS _ hz => ang1 z hS hz) (by linarith)
  have T2 : Tendsto (fun z : ℂ => z * exp (d * I)) F (airySector (π - δ)) :=
    scorerTwo_tendsto (fun z hS _ hz => (ang2 z hS hz).trans (by linarith)) (by linarith)
  -- the rotation constants
  set ω : ℂ := exp (ε * (2 * π * I / 3)) with hω
  set C : ℂ := 2 * exp (-ε * (π * I / 6)) with hC
  have hωn : ‖ω‖ = 1 := by
    rw [hωc, norm_neg, norm_exp_ofReal_mul_I]
  have hω0 : ω ≠ 0 := by rw [hω]; exact exp_ne_zero _
  -- Hi part
  have T1' : Tendsto (fun z : ℂ => z * ω) F (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ))) :=
    tendsto_comap_iff.mpr (T1.congr fun z => by simp only [Function.comp_apply, hωc]; ring)
  have h1 := (scorerAsym_scorerHi_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith)
    N).comp_tendsto T1'
  have h2 := (airy_ai_poincare hδ (by linarith) M).comp_tendsto T2
  have hev := scorerTwo_eventually (α := π - δ) (ε := ε)
  have hg1 : (fun z : ℂ => ((z * ω) ^ (3 * N + 0 + 1))⁻¹) =O[F]
      (fun z => ‖z‖ ^ (-(3 * N + 1 : ℤ)) + ‖airyPrefactor .bi z / airyZetaComplex z ^ M‖) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    rw [one_mul, norm_inv, norm_pow, norm_mul, hωn, mul_one, Real.norm_of_nonneg (by positivity)]
    rw [zpow_neg, show ((3 * N + 1 : ℤ)) = ((3 * N + 0 + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hpref : ∀ z : ℂ, z ≠ 0 → |arg z| ≤ π - δ → 0 ≤ ε * arg z →
      C * airyPrefactor .ai (z * exp (d * I)) = airyPrefactor .bi z ∧
      airyZetaComplex (z * exp (d * I)) = -airyZetaComplex z := fun z hz0 hz hS =>
    scorerTwo_pref hε hδ hz0 hz hS
  have hg2 : (fun z : ℂ => airyPrefactor .ai (z * exp (d * I)) /
      airyZetaComplex (z * exp (d * I)) ^ M) =O[F]
      (fun z => ‖z‖ ^ (-(3 * N + 1 : ℤ)) + ‖airyPrefactor .bi z / airyZetaComplex z ^ M‖) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hev] with z ⟨hz0, hz, hS⟩
    obtain ⟨p1, p2⟩ := hpref z hz0 hz hS
    have hCn : ‖C‖ = 2 := by
      rw [hC, norm_mul, show (-ε * (π * I / 6) : ℂ) = ((-ε * π / 6 : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I]; norm_num
    have : airyPrefactor .ai (z * exp (d * I)) = airyPrefactor .bi z / C := by
      rw [← p1]; field_simp [show C ≠ 0 by rw [← norm_ne_zero_iff, hCn]; norm_num]
    have e : ‖airyPrefactor .bi z / C / (-airyZetaComplex z) ^ M‖ =
        ‖airyPrefactor .bi z / airyZetaComplex z ^ M‖ / 2 := by
      rw [neg_pow, norm_div, norm_div, hCn, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, norm_div, norm_pow]; ring
    rw [one_mul, Real.norm_of_nonneg (by positivity), this, p2, e]
    have h0 : 0 ≤ ‖z‖ ^ (-(3 * N + 1 : ℤ)) := by positivity
    have h3 : 0 ≤ ‖airyPrefactor .bi z / airyZetaComplex z ^ M‖ := norm_nonneg _
    linarith
  refine (((h1.trans hg1).const_mul_left ω).add ((h2.trans hg2).const_mul_left C)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [hev] with z ⟨hz0, hz, hS⟩
  obtain ⟨p1, p2⟩ := hpref z hz0 hz hS
  have hconn := scorerHi_connection z hε
  rw [hdω] at hconn
  simp only [Function.comp_apply, airyFunction]
  rw [hconn]
  have hsum : airyExponentialSum .ai M (z * exp (d * I)) = airyExponentialSum .bi M z := by
    simp only [airyExponentialSum, airyExpansionCoeff, p2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow (airyZetaComplex z), mul_div_mul_left _ _ (pow_ne_zero k (neg_ne_zero.2 one_ne_zero))]
  have hz3 : (z * ω) ^ 3 = z ^ 3 := by rw [mul_pow, hω3, mul_one]
  rw [mul_sub, mul_sub, ← mul_assoc C, p1, hsum, hz3]
  have hzπ : (π : ℂ) * z ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hπ.ne') hz0
  have : ω * (-1 / (π * (z * ω) ^ 1)) = -(1 / (π * z)) := by
    rw [pow_one]; field_simp
  rw [← mul_assoc ω (-1 / _), this]
  simp only [add_zero, div_div]
  ring

/-- The sector filter is monotone in the half-angle. -/
theorem scorerTwo_sector_mono {α β : ℝ} (h : α ≤ β) : airySector α ≤ airySector β :=
  inf_le_inf_left _ (principal_mono.mpr fun _ hz => ⟨hz.1, hz.2.trans h⟩)

/-- In `|arg z| ≤ π - δ`, `Hi(z)` is `-(πz)⁻¹ ∑_{k<N} (3k)!/(k!(3z³)^k)` plus the `Bi`
exponential expansion `airyPrefactor .bi z · airyExponentialSum .bi M z`, up to
`O(|z|^{-3N-1} + |airyPrefactor .bi z / ζ^M|)` (DLMF 9.12.29). -/
@[dlmf 9.12.E29]
theorem scorerHi_two_scale_expansion {δ : ℝ} (hδ : 0 < δ) (N M : ℕ) :
    IsBigO (airySector (π - δ))
      (fun z => scorerHi z + (1 / (π * z) *
        ∑ k ∈ Finset.range N, ((3 * k).factorial : ℂ) / (k.factorial * (3 * z ^ 3) ^ k)) -
          airyPrefactor .bi z * airyExponentialSum .bi M z)
      (fun z => ‖z‖ ^ (-(3 * N + 1 : ℤ)) + ‖airyPrefactor .bi z / airyZetaComplex z ^ M‖) := by
  have hπ := Real.pi_pos
  set δ' := min δ (π / 3)
  have h0 : 0 < δ' := lt_min hδ (by positivity)
  have h3 : δ' ≤ π / 3 := min_le_right _ _
  refine IsBigO.mono ?_ (scorerTwo_sector_mono (by linarith [min_le_left δ (π / 3)] :
    π - δ ≤ π - δ'))
  have hsplit : airySector (π - δ') ≤ (airySector (π - δ') ⊓ 𝓟 {z : ℂ | 0 ≤ (1 : ℝ) * arg z}) ⊔
      (airySector (π - δ') ⊓ 𝓟 {z : ℂ | 0 ≤ (-1 : ℝ) * arg z}) := by
    rw [← inf_sup_left, sup_principal]
    refine le_inf le_rfl (le_principal_iff.mpr (univ_mem' fun z => ?_))
    rcases le_total 0 (arg z) with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  exact ((scorerTwo_half (Or.inl rfl) h0 h3 N M).sup
    (scorerTwo_half (Or.inr rfl) h0 h3 N M)).mono hsplit

/-! ### The integrated Scorer functions, DLMF 9.12.30 and 9.12.31 -/

section ScorerPrimitive

/-- `∫₀^∞ ((1+xv)⁻¹ - e^{-xv})/v dv = γ` for `x > 0`, with integrability. -/
theorem scorerPrim_integral_euler {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ =
      Real.eulerMascheroniConstant := by
  set g : ℝ → ℝ := fun t => (1 / (1 + t) - Real.exp (-t)) / t with hg
  have hpt : ∀ τ : ℝ, (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ = x * g (x * τ) := by
    intro τ
    simp only [hg]
    rcases eq_or_ne τ 0 with h | h
    · simp [h]
    · field_simp
  have hgi : IntegrableOn (fun τ => g (x * τ)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff g 0 hx, mul_zero]
    exact DLMF.Gamma.integrableOn_eulerIntegrand
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]; exact hgi.const_mul x
  · simp_rw [hpt]
    rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hx, mul_zero, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul,
          DLMF.Gamma.eulerMascheroni_eq_integral_recip_one_add]

/-- `∫₀^∞ (e^{-v³/3} - (1+v³/3)⁻¹)/v dv = -γ/3`, with integrability. -/
theorem scorerPrim_integral_cube :
    IntegrableOn (fun v : ℝ => (Real.exp (-(v ^ 3 / 3)) - 1 / (1 + v ^ 3 / 3)) / v) (Ioi 0) ∧
    ∫ v in Ioi (0 : ℝ), (Real.exp (-(v ^ 3 / 3)) - 1 / (1 + v ^ 3 / 3)) / v =
      -(Real.eulerMascheroniConstant / 3) := by
  set φ : ℝ → ℝ := fun t => (1 / (1 + t) - Real.exp (-t)) / t with hφ
  set g : ℝ → ℝ := fun y => φ ((1 / 3) * y)
  have hgi : IntegrableOn g (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff φ 0 (by norm_num : (0 : ℝ) < 1 / 3), mul_zero]
    exact DLMF.Gamma.integrableOn_eulerIntegrand
  have hgv : ∫ y in Ioi (0 : ℝ), g y = 3 * Real.eulerMascheroniConstant := by
    simp only [g]
    rw [integral_comp_mul_left_Ioi φ 0 (by norm_num : (0 : ℝ) < 1 / 3), mul_zero, smul_eq_mul,
      ← DLMF.Gamma.eulerMascheroni_eq_integral_recip_one_add]
    norm_num
  have hpt : ∀ v : ℝ, 0 < v → (Real.exp (-(v ^ 3 / 3)) - 1 / (1 + v ^ 3 / 3)) / v =
      -(1 / 9) * ((|(3 : ℝ)| * v ^ ((3 : ℝ) - 1)) • g (v ^ (3 : ℝ))) := by
    intro v hv
    simp only [g, hφ, smul_eq_mul]
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
    have : 0 < 1 + v ^ 3 / 3 := by positivity
    field_simp
    ring_nf
  have hi := (integrableOn_Ioi_comp_rpow_iff g (p := 3) (by norm_num)).mpr hgi
  refine ⟨IntegrableOn.congr_fun (hi.const_mul (-(1 / 9))) (fun v hv => (hpt v hv).symm)
      measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_rpow_Ioi g (by norm_num : (3 : ℝ) ≠ 0), hgv]
  ring

/-- `∫₀^∞ ((1+v³/3)⁻¹ - (1+v)⁻¹)/v dv = (log 3)/3`, with integrability. -/
theorem scorerPrim_integral_rat :
    IntegrableOn (fun v : ℝ => (1 / (1 + v ^ 3 / 3) - 1 / (1 + v)) / v) (Ioi 0) ∧
    ∫ v in Ioi (0 : ℝ), (1 / (1 + v ^ 3 / 3) - 1 / (1 + v)) / v = Real.log 3 / 3 := by
  set H : ℝ → ℝ := fun v => Real.log (1 + v) - Real.log (1 + v ^ 3 / 3) / 3 with hH
  have hderiv : ∀ v ∈ Ioi (0 : ℝ), HasDerivAt H ((1 / (1 + v ^ 3 / 3) - 1 / (1 + v)) / v) v := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have h1 : HasDerivAt (fun v : ℝ => Real.log (1 + v)) (1 / (1 + v)) v := by
      have := ((hasDerivAt_id v).const_add 1).log (by simp; linarith)
      simpa using this
    have h2 : HasDerivAt (fun v : ℝ => Real.log (1 + v ^ 3 / 3))
        ((3 * v ^ 2 / 3) / (1 + v ^ 3 / 3)) v := by
      have := (((hasDerivAt_pow 3 v).div_const 3).const_add 1).log (by positivity)
      simpa using this
    convert h1.sub (h2.div_const 3) using 1
    have : 0 < 1 + v ^ 3 / 3 := by positivity
    field_simp
    ring
  have hcont : ContinuousWithinAt H (Ici 0) 0 := by
    have : ContinuousAt H 0 := by
      refine ContinuousAt.sub ?_ ?_
      · exact (continuousAt_const.add continuousAt_id).log (by norm_num)
      · exact ((continuousAt_const.add ((continuousAt_id.pow 3).div_const 3)).log
          (by norm_num)).div_const 3
    exact this.continuousWithinAt
  have hlim : Tendsto H atTop (𝓝 (Real.log 3 / 3)) := by
    set h : ℝ → ℝ := fun u => Real.log ((u + 1) ^ 3 / (u ^ 3 + 1 / 3)) / 3 with hh
    have hhc : ContinuousAt h 0 := by
      refine (ContinuousAt.log ?_ (by norm_num)).div_const 3
      exact ((continuousAt_id.add continuousAt_const).pow 3).div
        ((continuousAt_id.pow 3).add continuousAt_const) (by norm_num)
    have h0 : h 0 = Real.log 3 / 3 := by simp [hh]
    have ht := (hhc.tendsto.comp tendsto_inv_atTop_zero)
    rw [h0] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with v hv
    simp only [Function.comp, hh, hH]
    have e : (v⁻¹ + 1) ^ 3 / (v⁻¹ ^ 3 + 1 / 3) = (1 + v) ^ 3 / (1 + v ^ 3 / 3) := by
      field_simp
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hint : IntegrableOn (fun v : ℝ => (1 / (1 + v ^ 3 / 3) - 1 / (1 + v)) / v) (Ioi 0) := by
    refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul 6).integrableOn)
      ((ContinuousOn.div (ContinuousOn.sub
        (continuousOn_const.div (by fun_prop) fun v (hv : 0 < v) => by positivity)
        (continuousOn_const.div (by fun_prop) fun v (hv : 0 < v) => by positivity)) continuousOn_id
        fun v hv =>
            (ne_of_gt (show (0 : ℝ) < v from hv))).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    have e : (1 / (1 + v ^ 3 / 3) - 1 / (1 + v)) / v = (3 - v ^ 2) / ((1 + v) * (3 + v ^ 3)) := by
      have : 0 < 3 + v ^ 3 := by positivity
      field_simp; ring
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (1 + v) * (3 + v ^ 3)),
      div_le_iff₀ (by positivity)]
    have hab : |3 - v ^ 2| ≤ 3 + v ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg v]
    have h6 : 6 * (1 + v ^ 2)⁻¹ * ((1 + v) * (3 + v ^ 3)) = 6 * ((1 + v) * (3 + v ^ 3)) /
        (1 + v ^ 2) := by
      field_simp
    rw [h6, le_div_iff₀ (by positivity)]
    have : (3 + v ^ 2) * (1 + v ^ 2) ≤ 6 * ((1 + v) * (3 + v ^ 3)) := by
      nlinarith [sq_nonneg (v ^ 2 - 1), pow_pos hv0 3, pow_pos hv0 4, sq_nonneg v]
    nlinarith [mul_le_mul_of_nonneg_right hab (by positivity : (0 : ℝ) ≤ 1 + v ^ 2)]
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp [hH]

/-- The tail `∫₀^∞ e^{-tv} (1 - e^{-v³/3})/v dv`: integrable, and between `0` and `2/(3t³)`. -/
theorem scorerPrim_tail {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => Real.exp (-(t * v)) * (1 - Real.exp (-(v ^ 3 / 3))) / v) (Ioi 0) ∧
    0 ≤ ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * (1 - Real.exp (-(v ^ 3 / 3))) / v ∧
    ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * (1 - Real.exp (-(v ^ 3 / 3))) / v ≤ 2 /
        (3 * t ^ 3) := by
  obtain ⟨hi2, hv2⟩ := airyInt_integral_pow_mul_exp_neg 2 ht
  have hpt : ∀ v : ℝ, 0 < v → 0 ≤ Real.exp (-(t * v)) * (1 - Real.exp (-(v ^ 3 / 3))) / v ∧
      Real.exp (-(t * v)) * (1 - Real.exp (-(v ^ 3 / 3))) / v ≤ (1 / 3) *
          (v ^ 2 * Real.exp (-(t * v))) := by
    intro v hv
    have h1 : 0 ≤ 1 - Real.exp (-(v ^ 3 / 3)) := by
      rw [sub_nonneg]; exact Real.exp_le_one_iff.mpr (by have := pow_pos hv 3; linarith)
    have h2 : 1 - Real.exp (-(v ^ 3 / 3)) ≤ v ^ 3 / 3 := by
      have := Real.add_one_le_exp (-(v ^ 3 / 3)); linarith
    have he := Real.exp_pos (-(t * v))
    constructor
    · positivity
    · rw [div_le_iff₀ hv]
      have := mul_le_mul_of_nonneg_left h2 he.le
      nlinarith
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => Real.exp (-(t * v)) * (1 - Real.exp (-(v ^ 3 / 3))) / v)
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ContinuousOn.div (by fun_prop) continuousOn_id fun v hv =>
        (ne_of_gt (show (0 : ℝ) < v from hv))
  have hint : IntegrableOn (fun v : ℝ => Real.exp (-(t * v)) * (1 - Real.exp (-(v ^ 3 / 3))) / v)
      (Ioi 0) := by
    refine (hi2.const_mul (1 / 3)).mono' hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hpt v hv).1]; exact (hpt v hv).2
  refine ⟨hint, setIntegral_nonneg measurableSet_Ioi fun v hv => (hpt v hv).1, ?_⟩
  calc _ ≤ ∫ v in Ioi (0 : ℝ), (1 / 3) * (v ^ 2 * Real.exp (-(t * v))) :=
        setIntegral_mono_on hint (hi2.const_mul _) measurableSet_Ioi fun v hv => (hpt v hv).2
    _ = 2 / (3 * t ^ 3) := by
        rw [integral_const_mul, hv2]; norm_num [Nat.factorial]; field_simp

/-- **The constant in 9.12.31 on the positive axis.** For `t > 0`,
`∫₀^∞ e^{-v³/3} (1 - e^{-tv})/v dv - log t → (2γ + ln 3)/3` as `t → ∞`, and the integrand is
integrable. -/
theorem scorerPrim_integral_tendsto :
    (∀ t : ℝ, 0 < t → IntegrableOn
      (fun v : ℝ => Real.exp (-(v ^ 3 / 3)) * (1 - Real.exp (-(t * v))) / v) (Ioi 0)) ∧
    Tendsto (fun t : ℝ =>
        (∫ v in Ioi (0 : ℝ), Real.exp (-(v ^ 3 / 3)) * (1 - Real.exp (-(t * v))) / v)
      - Real.log t) atTop (𝓝 ((2 * Real.eulerMascheroniConstant + Real.log 3) / 3)) := by
  have key : ∀ t : ℝ, 0 < t → IntegrableOn
      (fun v : ℝ => Real.exp (-(v ^ 3 / 3)) * (1 - Real.exp (-(t * v))) / v) (Ioi 0) ∧
      (∫ v in Ioi (0 : ℝ), Real.exp (-(v ^ 3 / 3)) * (1 - Real.exp (-(t * v))) / v) - Real.log t =
      (2 * Real.eulerMascheroniConstant + Real.log 3) / 3 +
        ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * (1 - Real.exp (-(v ^ 3 / 3))) / v := by
    intro t ht
    obtain ⟨iA, vA⟩ := scorerPrim_integral_cube
    obtain ⟨iB, vB⟩ := scorerPrim_integral_rat
    obtain ⟨iC, vC⟩ := integrableOn_and_integral_inv_one_add_sub_inv_one_add_mul_div ht
    obtain ⟨iD, vD⟩ := scorerPrim_integral_euler ht
    obtain ⟨iE, -, -⟩ := scorerPrim_tail ht
    have hsum : ∀ v ∈ Ioi (0 : ℝ), Real.exp (-(v ^ 3 / 3)) * (1 - Real.exp (-(t * v))) / v =
        (Real.exp (-(v ^ 3 / 3)) - 1 / (1 + v ^ 3 / 3)) / v +
        (1 / (1 + v ^ 3 / 3) - 1 / (1 + v)) / v + (1 / (1 + v) - 1 / (1 + t * v)) / v +
        (1 / (1 + t * v) - Real.exp (-(t * v))) / v +
        Real.exp (-(t * v)) * (1 - Real.exp (-(v ^ 3 / 3))) / v := by
      intro v hv; ring
    have hI := ((((iA.add iB).add iC).add iD).add iE)
    refine ⟨IntegrableOn.congr_fun hI (fun v hv => (hsum v hv).symm) measurableSet_Ioi, ?_⟩
    have e1 := integral_add (((iA.add iB).add iC).add iD) iE
    have e2 := integral_add ((iA.add iB).add iC) iD
    have e3 := integral_add (iA.add iB) iC
    have e4 := integral_add iA iB
    simp only [Pi.add_apply] at e1 e2 e3 e4
    rw [setIntegral_congr_fun measurableSet_Ioi hsum, e1, e2, e3, e4, vA, vB, vC, vD]
    ring
  refine ⟨fun t ht => (key t ht).1, ?_⟩
  have hE : Tendsto (fun t : ℝ => ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) *
      (1 - Real.exp (-(v ^ 3 / 3))) / v) atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => 2 / (3 * t ^ 3)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 3)).inv_tendsto_atTop.const_mul 2
      simpa [div_eq_mul_inv] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht using (scorerPrim_tail ht).2.1
    · filter_upwards [eventually_gt_atTop 0] with t ht using (scorerPrim_tail ht).2.2
  have := hE.const_add ((2 * Real.eulerMascheroniConstant + Real.log 3) / 3)
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact ((key t ht).2).symm

/-- `e^{-v³/3}` is integrable on `(0, ∞)`. -/
theorem scorerPrim_integrableOn_exp_cube :
    IntegrableOn (fun v : ℝ => Real.exp (-(v ^ 3 / 3))) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul (Real.exp (2 / 3))).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
  have hv0 : (0 : ℝ) < v := hv
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [sq_nonneg (v - 1), mul_nonneg (sq_nonneg (v - 1)) (by linarith : (0 : ℝ) ≤ v + 2)]

/-- `Hi(-u)` for real `u` as a real Laplace integral (DLMF 9.12.20). -/
theorem scorerPrim_scorerHi_neg_ofReal (u : ℝ) :
    scorerHi (-(u : ℂ)) =
        (((∫ v in Ioi (0 : ℝ), Real.exp (-(v ^ 3 / 3)) * Real.exp (-(u * v))) / π : ℝ) : ℂ) := by
  rw [(scorerHi_exp_integral _).2]
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  push_cast
  rw [← Complex.exp_add]; congr 1; ring

/-- `∫₀^x e^{-uv} du = (1 - e^{-xv})/v` for `v > 0`. -/
theorem scorerPrim_integral_exp_mul {v : ℝ} (hv : 0 < v) (x : ℝ) :
    ∫ u in (0 : ℝ)..x, Real.exp (-(u * v)) = (1 - Real.exp (-(x * v))) / v := by
  have hd : ∀ u : ℝ,
      HasDerivAt (fun u : ℝ => -Real.exp (-(u * v)) / v) (Real.exp (-(u * v))) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => -(u * v)) (-v) u := by
      convert ((hasDerivAt_id u).mul_const v).neg using 1 <;> first | rfl | simp
    refine (h1.exp.neg.div_const v).congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(u * v))).intervalIntegrable _ _)]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  ring

/-- The primitive of `Hi(-t)` on the positive axis as a Laplace-type integral:
`∫₀^x Hi(-t) dt = π^{-1} ∫₀^∞ e^{-v³/3} (1 - e^{-xv})/v dv`. -/
theorem scorerPrim_primitive_ofReal {x : ℝ} (hx : 0 < x) :
    primitive (fun t => scorerHi (-t)) x =
      (((∫ v in Ioi (0 : ℝ), Real.exp (-(v ^ 3 / 3)) * (1 - Real.exp (-(x * v))) / v) / π :
          ℝ) : ℂ) := by
  have hdiff : Differentiable ℂ (fun t : ℂ => scorerHi (-t)) :=
    differentiable_scorerHi.comp differentiable_neg
  rw [airyInt_primitive_ofReal hdiff x]
  simp_rw [scorerPrim_scorerHi_neg_ofReal]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_div]
  congr 1
  -- Fubini
  set f : ℝ → ℝ → ℝ := fun u v => Real.exp (-(v ^ 3 / 3)) * Real.exp (-(u * v))
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Ioc 0 x)).prod (volume.restrict (Ioi 0))) := by
    have hb : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * Real.exp (-(z.2 ^ 3 / 3)))
        ((volume.restrict (Ioc 0 x)).prod (volume.restrict (Ioi 0))) :=
      (integrable_const (1 : ℝ)).mul_prod scorerPrim_integrableOn_exp_cube
    refine hb.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    have hm : ∀ᵐ z ∂((volume.restrict (Ioc (0 : ℝ) x)).prod (volume.restrict (Ioi (0 : ℝ)))),
        z ∈ Ioc (0 : ℝ) x ×ˢ Ioi (0 : ℝ) := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)
    filter_upwards [hm] with z hz
    obtain ⟨⟨hu, -⟩, hv⟩ := hz
    have hv0 : (0 : ℝ) < z.2 := hv
    simp only [Function.uncurry, f, one_mul]
    rw [Real.norm_of_nonneg (by positivity)]
    have : Real.exp (-(z.1 * z.2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h0 := Real.exp_pos (-(z.2 ^ 3 / 3))
    nlinarith
  rw [intervalIntegral.integral_of_le hx.le]
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  simp only [f]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hx.le,
    scorerPrim_integral_exp_mul hv x]
  ring

/-- **The constant in 9.12.31**: `∫₀^x Hi(-t) dt - (log x)/π → (2γ + ln 3)/(3π)` as `x → +∞`. -/
theorem scorerPrim_tendsto_ofReal :
    Tendsto (fun x : ℝ => primitive (fun t => scorerHi (-t)) x - Complex.log x / π) atTop
      (𝓝 ((2 * (Real.eulerMascheroniConstant : ℂ) + Complex.log 3) / (3 * π))) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp
    ((scorerPrim_integral_tendsto.2).div_const π)
  have e : ((((2 * Real.eulerMascheroniConstant + Real.log 3) / 3) / π : ℝ) : ℂ) =
      (2 * (Real.eulerMascheroniConstant : ℂ) + Complex.log 3) / (3 * π) := by
    push_cast
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast; ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp]
  rw [scorerPrim_primitive_ofReal hx, ← Complex.ofReal_log hx.le]
  push_cast; ring

section
open Complex
/-- Unpacking an eventual statement in `airySector α`. -/
theorem scorerPrim_exists_of_eventually_sector {α : ℝ} {p : ℂ → Prop}
    (h : ∀ᶠ z in airySector α, p z) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → z ≠ 0 → |arg z| ≤ α → p z := by
  rw [airySector, eventually_inf_principal] at h
  obtain ⟨t, ht, hsub⟩ := h
  obtain ⟨R, hR⟩ := mem_atTop_sets.1 ht
  exact ⟨R, fun z hz hz0 harg => hsub (hR _ hz) ⟨hz0, harg⟩⟩

/-- Ray estimate for `scorerPrim_isBigO_of_deriv`: integrating the derivative bound from `ρ`
to `∞` along the positive axis gives `‖G(ρ)‖ ≤ (C/m) ρ^{-m}` for `ρ ≥ R`. -/
private lemma scorerPrim_ray_bound {G G' : ℂ → ℂ} {α : ℝ} (hα0 : 0 ≤ α) {m : ℕ} (hm : 0 < m)
    (hG : ∀ z ∈ slitPlane, HasDerivAt G (G' z) z)
    (hlim : Tendsto (fun t : ℝ => G t) atTop (𝓝 0)) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ z : ℂ, R ≤ ‖z‖ → |arg z| ≤ α → ‖G' z‖ ≤ C * ‖z‖ ^ (-((m : ℤ) + 1))) {ρ : ℝ}
        (hρ : R ≤ ρ) :
    ‖G ρ‖ ≤ C / m * ρ ^ (-(m : ℤ)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hρ0 : 0 < ρ := hR.trans_le hρ
  have hstep : ∀ t : ℝ, ρ ≤ t → ‖G t - G ρ‖ ≤ C / m * (ρ ^ (-(m : ℤ)) - t ^ (-(m : ℤ))) := by
    intro t ht
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      (f := fun u : ℝ => G u - G ρ) (f' := fun u : ℝ => G' u) (a := ρ) (b := t)
      (B := fun u : ℝ => C / m * (ρ ^ (-(m : ℤ)) - u ^ (-(m : ℤ))))
      (B' := fun u : ℝ => C * u ^ (-((m : ℤ) + 1))) ?_ ?_ ?_ ?_ ?_ ?_ (right_mem_Icc.2 ht)
    · exact key
    · intro u hu
      have hu0 : 0 < u := hρ0.trans_le hu.1
      exact ((hG u (ofReal_mem_slitPlane.2 hu0)).comp_ofReal.sub_const _).continuousAt
        |>.continuousWithinAt
    · intro u hu
      have hu0 : 0 < u := hρ0.trans_le hu.1
      exact ((hG u (ofReal_mem_slitPlane.2 hu0)).comp_ofReal.sub_const _).hasDerivWithinAt
    · simp
    · intro u hu
      have hu0 : 0 < u := hρ0.trans_le hu.1
      exact ((continuousAt_const.sub (continuousAt_zpow₀ u _ (Or.inl hu0.ne'))).const_mul _)
        |>.continuousWithinAt
    · intro u hu
      have hu0 : 0 < u := hρ0.trans_le hu.1
      have h1 := ((hasDerivAt_zpow (-(m : ℤ)) u (Or.inl hu0.ne')).const_sub
        (ρ ^ (-(m : ℤ)))).const_mul (C / m)
      convert h1.hasDerivWithinAt using 1
      rw [show -(m : ℤ) - 1 = -((m : ℤ) + 1) by ring]
      push_cast
      field_simp
    · intro u hu
      have hu0 : 0 < u := hρ0.trans_le hu.1
      have h := hC u (by rw [norm_real, Real.norm_of_nonneg hu0.le]; linarith [hu.1])
        (by rw [arg_ofReal_of_nonneg hu0.le, abs_zero]; exact hα0)
      rwa [norm_real, Real.norm_of_nonneg hu0.le] at h
  have hlim' : Tendsto (fun t : ℝ => ‖G t - G ρ‖) atTop (𝓝 ‖G ρ‖) := by
    simpa using (hlim.sub_const (G ρ)).norm
  have hB : Tendsto (fun t : ℝ => C / m * (ρ ^ (-(m : ℤ)) - t ^ (-(m : ℤ)))) atTop
      (𝓝 (C / m * ρ ^ (-(m : ℤ)))) := by
    have : Tendsto (fun t : ℝ => t ^ (-(m : ℤ))) atTop (𝓝 0) :=
      tendsto_zpow_atTop_zero (by omega)
    simpa using (tendsto_const_nhds.sub this).const_mul (C / m)
  exact le_of_tendsto_of_tendsto hlim' hB
    (eventually_atTop.2 ⟨ρ, fun t ht => hstep t ht⟩)

/-- Arc estimate for `scorerPrim_isBigO_of_deriv`: integrating the derivative bound along the
circular arc from `‖z‖` to `z` gives `‖G(z) - G(‖z‖)‖ ≤ C ‖z‖^{-m} |arg z|`. -/
private lemma scorerPrim_arc_bound {G G' : ℂ → ℂ} {α : ℝ} (hα0 : 0 ≤ α) (hα : α < π) {m : ℕ}
    (hG : ∀ z ∈ slitPlane, HasDerivAt G (G' z) z) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ z : ℂ, R ≤ ‖z‖ → |arg z| ≤ α → ‖G' z‖ ≤ C * ‖z‖ ^ (-((m : ℤ) + 1)))
    {z : ℂ} (hzR : R ≤ ‖z‖) (hzα : |arg z| ≤ α) :
    ‖G z - G ‖z‖‖ ≤ C * ‖z‖ ^ (-(m : ℤ)) * |arg z| := by
  set ρ := ‖z‖ with hρdef
  have hρ0 : 0 < ρ := hR.trans_le hzR
  set f : ℝ → ℂ := fun s => G ((ρ : ℂ) * exp (s * I)) with hf
  have hmem : ∀ s ∈ Icc (-α) α, s ∈ Ioc (-π) π := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hnormw : ∀ s : ℝ, ‖(ρ : ℂ) * exp (s * I)‖ = ρ := fun s => by
    rw [norm_mul, norm_real, Real.norm_of_nonneg hρ0.le, norm_exp_ofReal_mul_I, mul_one]
  have hderiv : ∀ s ∈ Icc (-α) α, HasDerivWithinAt f
      (G' ((ρ : ℂ) * exp (s * I)) * ((ρ : ℂ) * (exp (s * I) * I))) (Icc (-α) α) s := by
    intro s hs
    have harg := Complex.arg_ofReal_mul_exp_ofReal_mul_I hρ0 (hmem s hs)
    have hsl : (ρ : ℂ) * exp (s * I) ∈ slitPlane := by
      rw [mem_slitPlane_iff_arg, harg]
      refine ⟨by linarith [hs.2], mul_ne_zero (ofReal_ne_zero.2 hρ0.ne') (exp_ne_zero _)⟩
    have h1 : HasDerivAt (fun s : ℝ => (ρ : ℂ) * exp (s * I)) ((ρ : ℂ) * (exp (s * I) * I)) s := by
      have := (((hasDerivAt_id s).ofReal_comp).mul_const I).cexp.const_mul (ρ : ℂ)
      simpa using this
    exact ((hG _ hsl).comp s h1).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc (-α) α,
      ‖G' ((ρ : ℂ) * exp (s * I)) * ((ρ : ℂ) * (exp (s * I) * I))‖ ≤ C * ρ ^ (-(m : ℤ)) := by
    intro s hs
    have harg := Complex.arg_ofReal_mul_exp_ofReal_mul_I hρ0 (hmem s hs)
    have h := hC ((ρ : ℂ) * exp (s * I)) (by rw [hnormw]; exact hzR)
      (by rw [harg, abs_le]; exact ⟨hs.1, hs.2⟩)
    rw [hnormw] at h
    rw [norm_mul, ← mul_assoc, norm_mul _ I, hnormw, norm_I, mul_one]
    calc ‖G' ((ρ : ℂ) * exp (s * I))‖ * ρ ≤ C * ρ ^ (-((m : ℤ) + 1)) * ρ :=
          mul_le_mul_of_nonneg_right h hρ0.le
      _ = C * ρ ^ (-(m : ℤ)) := by
          rw [mul_assoc, ← zpow_add_one₀ hρ0.ne']; congr 2; ring
  have hθ : arg z ∈ Icc (-α) α := abs_le.1 hzα
  have hmvt := (convex_Icc (-α) α).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (show (0 : ℝ) ∈ Icc (-α) α from ⟨by linarith, hα0⟩) hθ
  have hfz : f (arg z) = G z := by
    simp only [hf, hρdef]; rw [norm_mul_exp_arg_mul_I]
  have hf0 : f 0 = G ρ := by simp [hf]
  rw [hfz, hf0, sub_zero, Real.norm_eq_abs] at hmvt
  exact hmvt

/-- **Integration of a derivative bound in a sector.** If `G` is holomorphic on the slit plane,
`G(t) → 0` along the positive axis, and `‖G'(z)‖ ≤ C ‖z‖^{-(m+1)}` for large `z` with
`|arg z| ≤ α < π`, then `G(z) = O(z^{-m})` in `airySector α`. -/
theorem scorerPrim_isBigO_of_deriv {G G' : ℂ → ℂ} {α : ℝ} (hα0 : 0 ≤ α) (hα : α < π) {m : ℕ}
    (hm : 0 < m)
    (hG : ∀ z ∈ slitPlane, HasDerivAt G (G' z) z)
    (hlim : Tendsto (fun t : ℝ => G t) atTop (𝓝 0)) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ z : ℂ, R ≤ ‖z‖ → |arg z| ≤ α → ‖G' z‖ ≤ C * ‖z‖ ^ (-((m : ℤ) + 1))) :
    G =O[airySector α] (fun z : ℂ => z ^ (-(m : ℤ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hray : ∀ ρ : ℝ, R ≤ ρ → ‖G ρ‖ ≤ C / m * ρ ^ (-(m : ℤ)) := fun ρ hρ =>
    scorerPrim_ray_bound hα0 hm hG hlim hR hC hρ
  have hC0 : 0 ≤ C := by
    have h := hC R (by rw [norm_real, Real.norm_of_nonneg hR.le])
      (by rw [arg_ofReal_of_nonneg hR.le, abs_zero]; exact hα0)
    rw [norm_real, Real.norm_of_nonneg hR.le] at h
    have hp : 0 < R ^ (-((m : ℤ) + 1)) := zpow_pos hR _
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (G' R)]
  have hev : ∀ᶠ z in airySector α, R ≤ ‖z‖ ∧ z ∈ {z : ℂ | z ≠ 0 ∧ |arg z| ≤ α} :=
    (((tendsto_comap.mono_left inf_le_left : Tendsto (fun z : ℂ => ‖z‖) (airySector α)
        atTop)).eventually
      (eventually_ge_atTop R)).and
      (mem_inf_of_right (mem_principal_self _))
  refine IsBigO.of_bound (C / m + C * α) (hev.mono fun z ⟨hzR, hz0, hzα⟩ => ?_)
  have hmvt := scorerPrim_arc_bound hα0 hα hG hR hC hzR hzα
  set ρ := ‖z‖ with hρdef
  have hρ0 : 0 < ρ := hR.trans_le hzR
  have hz' : ‖z ^ (-(m : ℤ))‖ = ρ ^ (-(m : ℤ)) := by rw [norm_zpow]
  rw [hz']
  have hp : 0 ≤ ρ ^ (-(m : ℤ)) := (zpow_pos hρ0 _).le
  have h1 := hray ρ hzR
  have h2 : C * ρ ^ (-(m : ℤ)) * |arg z| ≤ C * ρ ^ (-(m : ℤ)) * α :=
    mul_le_mul_of_nonneg_left hzα (mul_nonneg hC0 hp)
  calc ‖G z‖ ≤ ‖G ρ‖ + ‖G z - G ρ‖ := by
        have := norm_sub_norm_le (G z) (G ρ); linarith
    _ ≤ C / m * ρ ^ (-(m : ℤ)) + C * ρ ^ (-(m : ℤ)) * α := by linarith
    _ = (C / m + C * α) * ρ ^ (-(m : ℤ)) := by ring

end

open Complex

/-- The derivative of a term of the integrated Scorer expansion is the next term of the
`Hi(-z)` expansion. -/
theorem scorerPrim_term_hasDerivAt (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (fun w : ℂ => (-1 : ℂ) ^ k * ((3 * (k + 1) - 1).factorial : ℂ) /
        ((k + 1).factorial * (3 * w ^ 3) ^ (k + 1)))
      ((1 / w) * ((-1 : ℂ) ^ (k + 1) * ((3 * (k + 1) + 0).factorial : ℂ) /
        ((k + 1).factorial * (3 * w ^ 3) ^ (k + 1)))) w := by
  have h1 : HasDerivAt (fun w : ℂ => ((k + 1).factorial : ℂ) * (3 * w ^ 3) ^ (k + 1))
      (((k + 1).factorial : ℂ) * (((k + 1 : ℕ) : ℂ) * (3 * w ^ 3) ^ k *
        (3 * ((3 : ℕ) * w ^ 2)))) w := by
    have := ((hasDerivAt_pow 3 w).const_mul (3 : ℂ)).pow (k + 1)
    simpa using this.const_mul ((k + 1).factorial : ℂ)
  have hne : ((k + 1).factorial : ℂ) * (3 * w ^ 3) ^ (k + 1) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (k + 1))
      (pow_ne_zero _ (mul_ne_zero three_ne_zero (pow_ne_zero _ hw)))
  have h2 := (hasDerivAt_const w ((-1 : ℂ) ^ k * ((3 * (k + 1) - 1).factorial : ℂ))).div h1 hne
  refine h2.congr_deriv ?_
  have hfac : ((3 * (k + 1) + 0).factorial : ℂ) = (3 * k + 3) *
      ((3 * (k + 1) - 1).factorial : ℂ) := by
    rw [show 3 * (k + 1) + 0 = (3 * k + 2) + 1 by ring, show 3 * (k + 1) - 1 = 3 * k + 2 by omega,
      Nat.factorial_succ]
    push_cast; ring
  rw [hfac]
  have hf : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 1)
  have : (w ^ 3) ≠ 0 := pow_ne_zero _ hw
  generalize ((3 * (k + 1) - 1).factorial : ℂ) = F
  generalize ((k + 1).factorial : ℂ) = K at hf ⊢
  field_simp
  push_cast
  ring

/-- Each term of the integrated Scorer expansion tends to zero along the positive axis. -/
theorem scorerPrim_term_tendsto (k : ℕ) :
    Tendsto (fun t : ℝ => (-1 : ℂ) ^ k * ((3 * (k + 1) - 1).factorial : ℂ) /
        ((k + 1).factorial * (3 * (t : ℂ) ^ 3) ^ (k + 1))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    rw [Complex.ofReal_zero] at this
    exact this.congr fun t => by simp
  set a : ℂ := (-1 : ℂ) ^ k * ((3 * (k + 1) - 1).factorial : ℂ) /
    ((k + 1).factorial * 3 ^ (k + 1))
  have hc : Continuous fun u : ℂ => a * (u ^ 3) ^ (k + 1) := by fun_prop
  have h := (hc.tendsto 0).comp hinv
  rw [show a * ((0 : ℂ) ^ 3) ^ (k + 1) = 0 by simp] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hf := Nat.factorial_ne_zero (k + 1)
  have hf' : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast hf
  simp only [Function.comp, a, inv_pow]
  field_simp
  ring

/-- The `k`-th derivative term of the integrated expansion, rewritten as a term of the
`Hi(-z)` expansion `(3k+3)!/((k+1)! (3(-z)³)^{k+1})` divided by `z`. -/
private lemma scorerPrim_term_neg (k : ℕ) {z : ℂ} (hz0 : z ≠ 0) :
    (1 / z) * ((-1 : ℂ) ^ (k + 1) * ((3 * (k + 1) + 0).factorial : ℂ) /
        ((k + 1).factorial * (3 * z ^ 3) ^ (k + 1))) =
      z⁻¹ * (((3 * (k + 1) + 0).factorial : ℂ) / ((k + 1).factorial : ℂ) /
        (3 * (-z) ^ 3) ^ (k + 1)) := by
  have hf : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 1)
  have h3 : (3 * z ^ 3) ≠ 0 := mul_ne_zero three_ne_zero (pow_ne_zero 3 hz0)
  have hn : ((-1 : ℂ) ^ (k + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm : ((-1 : ℂ) ^ (k + 1)) * (-1) ^ (k + 1) = 1 := by
    rw [← mul_pow]; norm_num
  rw [show (3 * (-z) ^ 3) ^ (k + 1) = (-1) ^ (k + 1) * (3 * z ^ 3) ^ (k + 1) by
    rw [← mul_pow]; ring]
  generalize ((3 * (k + 1) + 0).factorial : ℂ) = F
  generalize ((k + 1).factorial : ℂ) = K at hf ⊢
  generalize (3 * z ^ 3) ^ (k + 1) = X
  generalize ((-1 : ℂ) ^ (k + 1)) = s at hn hm ⊢
  have hs : s⁻¹ = s := inv_eq_of_mul_eq_one_right hm
  nth_rewrite 1 [← hs]
  field_simp

/-- `∫₀^z Hi(-t) dt ~ π⁻¹ ln z + (2γ + ln 3)/(3π) + π⁻¹ ∑_{k≥1} (-1)^{k-1} (3k-1)!/(k!(3z³)^k)`
as `z → ∞` in `|arg z| ≤ 2π/3 - δ`, with remainder `O(z^{-3N-3})` (DLMF 9.12.31). -/
@[dlmf 9.12.E31]
theorem scorerHi_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => primitive (fun t => scorerHi (-t)) z - Complex.log z / π -
        (2 * (Real.eulerMascheroniConstant : ℂ) + Complex.log 3) / (3 * π) -
        (∑ k ∈ Finset.range N, (-1 : ℂ) ^ k *
          ((3 * (k + 1) - 1).factorial : ℂ) / ((k + 1).factorial * (3 * z ^ 3) ^ (k + 1))) / π)
      (fun z => z ^ (-3 * ((N : ℂ) + 1))) := by
  set α := 2 * π / 3 - δ with hαdef
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set T : ℕ → ℂ → ℂ := fun k w => (-1 : ℂ) ^ k * ((3 * (k + 1) - 1).factorial : ℂ) /
    ((k + 1).factorial * (3 * w ^ 3) ^ (k + 1)) with hT
  set c : ℂ := (2 * (Real.eulerMascheroniConstant : ℂ) + Complex.log 3) / (3 * π)
  set G : ℂ → ℂ := fun z => primitive (fun t => scorerHi (-t)) z - Complex.log z / π - c -
    (∑ k ∈ Finset.range N, T k z) / π with hG
  set G' : ℂ → ℂ := fun z => scorerHi (-z) - z⁻¹ / π -
    (∑ k ∈ Finset.range N, ((1 / z) * ((-1 : ℂ) ^ (k + 1) * ((3 * (k + 1) + 0).factorial : ℂ) /
        ((k + 1).factorial * (3 * z ^ 3) ^ (k + 1))))) / π with hG'
  have hdiff : Differentiable ℂ (fun t : ℂ => scorerHi (-t)) :=
    differentiable_scorerHi.comp differentiable_neg
  have hder : ∀ z ∈ slitPlane, HasDerivAt G (G' z) z := by
    intro z hz
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have hs : HasDerivAt (fun w => ∑ k ∈ Finset.range N, T k w)
        (∑ k ∈ Finset.range N, ((1 / z) * ((-1 : ℂ) ^ (k + 1) *
          ((3 * (k + 1) + 0).factorial : ℂ) / ((k + 1).factorial * (3 * z ^ 3) ^ (k + 1))))) z :=
      HasDerivAt.fun_sum fun k _ => scorerPrim_term_hasDerivAt k hz0
    exact ((((hasDerivAt_primitive hdiff z).sub ((Complex.hasDerivAt_log hz).div_const π)).sub_const
      c).sub (hs.div_const π))
  have hlim : Tendsto (fun t : ℝ => G t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => primitive (fun t => scorerHi (-t)) t - Complex.log t / π - c)
        atTop (𝓝 0) := by
      have := scorerPrim_tendsto_ofReal.sub_const c
      simp only [c, sub_self] at this ⊢
      exact this
    have h2 : Tendsto (fun t : ℝ => (∑ k ∈ Finset.range N, T k t) / π) atTop (𝓝 0) := by
      have := (tendsto_finsetSum (Finset.range N) fun k _ => scorerPrim_term_tendsto k).div_const
        (π : ℂ)
      simpa using this
    simpa using h1.sub h2
  -- the derivative bound from 9.12.27 with `N + 1` terms
  have hasy := scorerAsym_scorerHi_isBigO (α := α) (by linarith) (by linarith) (N + 1)
  have htend : Tendsto (fun w : ℂ => -w) (airySector α) (comap (fun z : ℂ => -z) (airySector α)) :=
    tendsto_comap_iff.2 (by simpa [Function.comp] using tendsto_id)
  obtain ⟨C, hCe⟩ := (hasy.comp_tendsto htend).bound
  obtain ⟨R, hR⟩ := scorerPrim_exists_of_eventually_sector hCe
  have hbd : ∀ z : ℂ, max R 1 ≤ ‖z‖ → |arg z| ≤ α →
      ‖G' z‖ ≤ C * ‖z‖ ^ (-(((3 * N + 3 : ℕ) : ℤ) + 1)) := by
    intro z hz harg
    have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; linarith
    have h := hR z (le_trans (le_max_left _ _) hz) hz0 harg
    simp only [Function.comp] at h
    have e1 : G' z = scorerHi (-z) - -1 / (π * (-z) ^ 1) *
        ∑ k ∈ Finset.range (N + 1), (((3 * k + 0).factorial : ℂ) / k.factorial) /
          (3 * (-z) ^ 3) ^ k := by
      have hterm : ∀ k ∈ Finset.range N, (1 / z) * ((-1 : ℂ) ^ (k + 1) *
          ((3 * (k + 1) + 0).factorial : ℂ) / ((k + 1).factorial * (3 * z ^ 3) ^ (k + 1))) =
          z⁻¹ * (((3 * (k + 1) + 0).factorial : ℂ) / ((k + 1).factorial : ℂ) /
            (3 * (-z) ^ 3) ^ (k + 1)) := fun k _ => scorerPrim_term_neg k hz0
      simp only [hG']
      rw [Finset.sum_range_succ', Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, mul_zero, zero_add,
        Nat.factorial_zero]
      field_simp
      ring
    have e2 : ‖((-z) ^ (3 * (N + 1) + 0 + 1))⁻¹‖ = ‖z‖ ^ (-(((3 * N + 3 : ℕ) : ℤ) + 1)) := by
      rw [norm_inv, norm_pow, norm_neg, zpow_neg, ← zpow_natCast]
      congr 2
    rw [e1]; rw [e2] at h; exact h
  have hO := scorerPrim_isBigO_of_deriv (α := α) (m := 3 * N + 3) (by linarith) (by linarith)
    (by omega) hder hlim (lt_of_lt_of_le one_pos (le_max_right R 1)) hbd
  refine hO.congr' EventuallyEq.rfl (Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [show (-3 * ((N : ℂ) + 1)) = ((-((3 * N + 3 : ℕ) : ℤ) : ℤ) : ℂ) by push_cast; ring,
    cpow_intCast]

/-- Rescaling the segment primitive: `∫₀^z f(ta) dt = a⁻¹ ∫₀^{za} f`. -/
theorem scorerPrim_primitive_comp_mul (f : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    primitive (fun t => f (t * a)) z = a⁻¹ * primitive f (z * a) := by
  simp only [primitive, segmentIntegral, zero_add, sub_zero]
  field_simp
  congr 1; congr 1; funext s; ring_nf

/-- Linearity of the segment primitive for continuous integrands. -/
theorem scorerPrim_primitive_lin {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (c₁ c₂ : ℂ) (z : ℂ) :
    primitive (fun t => c₁ * f t + c₂ * g t) z = c₁ * primitive f z + c₂ * primitive g z := by
  simp only [primitive, segmentIntegral, zero_add, sub_zero]
  have h1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * z)) volume 0 1 :=
    (hf.comp (by fun_prop)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s : ℝ => g ((s : ℂ) * z)) volume 0 1 :=
    (hg.comp (by fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h1.const_mul c₁) (h2.const_mul c₂),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- `e^{iπ/3}` cubed is `-1`, and likewise for `e^{-iπ/3}`. -/
theorem scorerPrim_exp_cube (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    exp (((ε * (π / 3) : ℝ) : ℂ) * I) ^ 3 = -1 := by
  rw [← Complex.exp_nat_mul]
  rcases hε with rfl | rfl
  · rw [show ((3 : ℕ) : ℂ) * (((1 * (π / 3) : ℝ) : ℂ) * I) = π * I by push_cast; ring,
      exp_pi_mul_I]
  · rw [show ((3 : ℕ) : ℂ) * (((-1 * (π / 3) : ℝ) : ℂ) * I) = -(π * I) by push_cast; ring,
      Complex.exp_neg, exp_pi_mul_I]; norm_num

/-- **The Gi primitive via Hi(-z)**: `∫₀^z Gi = (Q(z e^{iπ/3}) + Q(z e^{-iπ/3}))/2`, where
`Q(w) = ∫₀^w Hi(-t) dt` (from the rotation formula 9.12.12). -/
theorem scorerPrim_primitive_scorerGi (z : ℂ) :
    primitive scorerGi z =
      (primitive (fun t => scorerHi (-t)) (z * exp (((1 * (π / 3) : ℝ) : ℂ) * I)) +
        primitive (fun t => scorerHi (-t)) (z * exp (((-1 * (π / 3) : ℝ) : ℂ) * I))) / 2 := by
  set a := exp (((1 * (π / 3) : ℝ) : ℂ) * I)
  set b := exp (((-1 * (π / 3) : ℝ) : ℂ) * I)
  have hA : exp (-2 * π * I / 3) = -a := by
    simp only [a]
    rw [show (-2 * π * I / 3 : ℂ) = ((1 * (π / 3) : ℝ) : ℂ) * I + -(π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_neg, exp_pi_mul_I]; ring
  have hB : exp (2 * π * I / 3) = -b := by
    simp only [b]
    rw [show (2 * π * I / 3 : ℂ) = ((-1 * (π / 3) : ℝ) : ℂ) * I + π * I by push_cast; ring,
      Complex.exp_add, exp_pi_mul_I]; ring
  have hfun : scorerGi = fun t => exp (π * I / 3) / 2 * (fun s => scorerHi (-s)) (t * a) +
      exp (-π * I / 3) / 2 * (fun s => scorerHi (-s)) (t * b) := by
    funext t
    rw [scorerGi_rotations t, hA, hB]
    simp only [mul_neg]
  have hc : Continuous fun s : ℂ => scorerHi (-s) :=
    (differentiable_scorerHi.comp differentiable_neg).continuous
  rw [hfun, scorerPrim_primitive_lin (f := fun t => (fun s => scorerHi (-s)) (t * a))
    (g := fun t => (fun s => scorerHi (-s)) (t * b)) (hc.comp (by fun_prop))
    (hc.comp (by fun_prop)),
    scorerPrim_primitive_comp_mul (fun s => scorerHi (-s)) (exp_ne_zero _) z,
    scorerPrim_primitive_comp_mul (fun s => scorerHi (-s)) (exp_ne_zero _) z]
  have ea : exp (π * I / 3) / 2 * a⁻¹ = 1 / 2 := by
    simp only [a]; rw [← Complex.exp_neg]
    rw [div_mul_eq_mul_div, ← Complex.exp_add]
    rw [show π * I / 3 + -(((1 * (π / 3) : ℝ) : ℂ) * I) = 0 by push_cast; ring, Complex.exp_zero]
  have eb : exp (-π * I / 3) / 2 * b⁻¹ = 1 / 2 := by
    simp only [b]; rw [← Complex.exp_neg]
    rw [div_mul_eq_mul_div, ← Complex.exp_add]
    rw [show -π * I / 3 + -(((-1 * (π / 3) : ℝ) : ℂ) * I) = 0 by push_cast; ring, Complex.exp_zero]
  rw [← mul_assoc, ← mul_assoc, ea, eb]
  ring

/-- The rotated 9.12.31 remainder is `O(z^{-3N-3})` in the sector `|arg z| ≤ π/3 - δ`. -/
theorem scorerPrim_rot_isBigO {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3)
    (N : ℕ) :
    IsBigO (airySector (π / 3 - δ))
      (fun z => (fun w => primitive (fun t => scorerHi (-t)) w - log w / π -
        (2 * (Real.eulerMascheroniConstant : ℂ) + log 3) / (3 * π) -
        (∑ k ∈ Finset.range N, (-1 : ℂ) ^ k *
          ((3 * (k + 1) - 1).factorial : ℂ) / ((k + 1).factorial * (3 * w ^ 3) ^ (k + 1))) / π)
        (z * exp (((ε * (π / 3) : ℝ) : ℂ) * I)))
      (fun z => z ^ (-3 * ((N : ℂ) + 1))) := by
  have hπ := Real.pi_pos
  have hc : |ε * (π / 3)| = π / 3 := by
    rcases hε with rfl | rfl <;> simp [abs_of_pos (by positivity : (0 : ℝ) < π / 3)]
  have hE := scorerHi_primitive_asymptotic (δ := δ) hδ (by linarith) N
  have hbd : ∀ z : ℂ, |arg z| ≤ π / 3 - δ → |arg z + ε * (π / 3)| ≤ 2 * π / 3 - δ := by
    intro z hz
    have := abs_add_le (arg z) (ε * (π / 3))
    linarith
  have ht : Tendsto (fun z : ℂ => z * exp (((ε * (π / 3) : ℝ) : ℂ) * I)) (airySector (π / 3 - δ))
      (airySector (2 * π / 3 - δ)) := by
    have := scorerTwo_tendsto (α := π / 3 - δ) (β := 2 * π / 3 - δ) (c := ε * (π / 3))
      (S := univ) (fun z _ _ hz => hbd z hz) (by linarith)
    simpa using this
  refine (hE.comp_tendsto ht).trans ?_
  have hA : ∀ᶠ z in airySector (π / 3 - δ), z ≠ 0 ∧ |arg z| ≤ π / 3 - δ :=
    mem_inf_of_right (mem_principal_self _)
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hA] with z ⟨hz0, harg⟩
  have hb := abs_le.mp (hbd z harg)
  simp only [Function.comp_apply]
  rw [scorerTwo_cpow_mul_exp hz0 (by linarith) (by linarith), norm_mul, one_mul]
  have : ‖exp (-3 * ((N : ℂ) + 1) * ((ε * (π / 3) : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [this, mul_one]

/-- The cubed rotated point: `(z e^{±iπ/3})³ = -z³`, applied to the 9.12.31 sum. -/
theorem scorerPrim_rot_sum {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.range N, (-1 : ℂ) ^ k * ((3 * (k + 1) - 1).factorial : ℂ) /
        ((k + 1).factorial * (3 * (z * exp (((ε * (π / 3) : ℝ) : ℂ) * I)) ^ 3) ^ (k + 1))) =
      ∑ k ∈ Finset.range N, -(1 : ℂ) * ((3 * (k + 1) - 1).factorial : ℂ) /
        ((k + 1).factorial * (3 * z ^ 3) ^ (k + 1)) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (z * exp (((ε * (π / 3) : ℝ) : ℂ) * I)) ^ 3 = z ^ 3 * -1 by
      rw [mul_pow, scorerPrim_exp_cube ε hε],
    show (3 * (z ^ 3 * -1)) ^ (k + 1) = (-1) ^ k * (-1) * (3 * z ^ 3) ^ (k + 1) by
      rw [show 3 * (z ^ 3 * -1) = (-1) * (3 * z ^ 3) by ring, mul_pow, pow_succ]]
  have hf : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 1)
  have h3 : (3 * z ^ 3) ^ (k + 1) ≠ 0 :=
      pow_ne_zero _ (mul_ne_zero three_ne_zero (pow_ne_zero 3 hz))
  have hm : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  generalize ((3 * (k + 1) - 1).factorial : ℂ) = F
  generalize ((k + 1).factorial : ℂ) = K at hf ⊢
  generalize (3 * z ^ 3) ^ (k + 1) = X at h3 ⊢
  generalize ((-1 : ℂ) ^ k) = s at hm ⊢
  have hn : s ≠ 0 := left_ne_zero_of_mul_eq_one hm
  field_simp

/-- `∫₀^z Gi(t) dt ~ π⁻¹ ln z + (2γ + ln 3)/(3π) - π⁻¹ ∑_{k≥1} (3k-1)!/(k!(3z³)^k)` as
`z → ∞` in `|arg z| ≤ π/3 - δ`, with remainder `O(z^{-3N-3})` (DLMF 9.12.30). -/
@[dlmf 9.12.E30]
theorem scorerGi_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ))
      (fun z => primitive (fun t => scorerGi t) z - log z / π -
        (2 * (Real.eulerMascheroniConstant : ℂ) + log 3) / (3 * π) -
        (∑ k ∈ Finset.range N, -(1 : ℂ) *
          ((3 * (k + 1) - 1).factorial : ℂ) / ((k + 1).factorial * (3 * z ^ 3) ^ (k + 1))) / π)
      (fun z => z ^ (-3 * ((N : ℂ) + 1))) := by
  have hπ := Real.pi_pos
  have h1 := scorerPrim_rot_isBigO (Or.inl rfl) hδ hδ' N
  have h2 := scorerPrim_rot_isBigO (Or.inr rfl) hδ hδ' N
  refine ((h1.add h2).const_mul_left (1 / 2 : ℂ)).congr' ?_ EventuallyEq.rfl
  have hA : ∀ᶠ z in airySector (π / 3 - δ), z ≠ 0 ∧ |arg z| ≤ π / 3 - δ :=
    mem_inf_of_right (mem_principal_self _)
  filter_upwards [hA] with z ⟨hz0, harg⟩
  have hb := abs_le.mp harg
  rw [scorerPrim_rot_sum (Or.inl rfl) hz0, scorerPrim_rot_sum (Or.inr rfl) hz0,
    scorerTwo_log_mul_exp hz0 (by linarith) (by linarith),
    scorerTwo_log_mul_exp hz0 (by linarith) (by linarith)]
  rw [show (fun t => scorerGi t) = scorerGi from rfl, scorerPrim_primitive_scorerGi z]
  push_cast
  ring

end ScorerPrimitive

end DLMF.Airy
