/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.LogarithmContinuedFraction
public import DLMFMathlib.Analysis.ContinuedFraction.PositiveConvergence
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Contraction of the logarithm continued fraction

Pairing consecutive levels of the Stieltjes fraction for `log(1+z)` gives its odd Jacobi
fraction. This identifies the even convergents, while positivity identifies the real limit.
-/

@[expose] public noncomputable section

open Complex Filter Set GenContFract
open scoped Topology Nat

namespace DLMF.Elementary.LogarithmContraction

/-- The partial numerators of the alternating Stieltjes fraction for `log(1+z)`. -/
def numerator (z : ℂ) (k : ℕ) : ℂ :=
  if k = 0 then z else (((k + 1) / 2 : ℕ) : ℂ) ^ 2 * z

/-- The numerator sequence of the contracted logarithmic Jacobi fraction. -/
def jacobiNumerator (z : ℂ) (k : ℕ) : ℂ :=
  if k = 0 then z else -(k : ℂ) ^ 2 * z ^ 2

/-- The denominator sequence of the contracted logarithmic Jacobi fraction. -/
def jacobiDenominator (z : ℂ) (k : ℕ) : ℂ := (2 * k + 1) * (z + 2)

/-- Pairing the recurrence of the logarithm continuants gives the contracted recurrence. -/
theorem even_recurrence (z : ℂ) {u : ℕ → ℂ}
    (hu : ∀ k, u (k + 2) = (k + 2) * u (k + 1) + numerator z (k + 1) * u k)
    (n : ℕ) :
    u (2 * (n + 2)) = (n + 2) * (2 * n + 3) * (z + 2) * u (2 * (n + 1)) -
      (n + 2) * (n + 1) ^ 3 * z ^ 2 * u (2 * n) := by
  have h0 := hu (2 * n)
  have h1 := hu (2 * n + 1)
  have h2 := hu (2 * n + 2)
  have he0 : numerator z (2 * n + 1) = (n + 1) ^ 2 * z := by
    simp [numerator, show (2 * n + 1 + 1) / 2 = n + 1 by omega]
  have he1 : numerator z (2 * n + 1 + 1) = (n + 1) ^ 2 * z := by
    simp [numerator, show (2 * n + 1 + 1 + 1) / 2 = n + 1 by omega]
  have he2 : numerator z (2 * n + 2 + 1) = (n + 2) ^ 2 * z := by
    simp [numerator, show (2 * n + 2 + 1 + 1) / 2 = n + 2 by omega]
  rw [he0] at h0
  rw [he1] at h1
  rw [he2] at h2
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have he : 2 * ((n : ℂ) + 1) * (u (2 * (n + 2)) -
      ((n + 2) * (2 * n + 3) * (z + 2) * u (2 * (n + 1)) -
        (n + 2) * (n + 1) ^ 3 * z ^ 2 * u (2 * n))) = 0 := by
    convert_to 2 * ((n : ℂ) + 1) * (u (2 * n + 4) -
      ((n + 2) * (2 * n + 3) * (z + 2) * u (2 * n + 2) -
        (n + 2) * (n + 1) ^ 3 * z ^ 2 * u (2 * n))) = 0 using 1
    push_cast at h0 h1 h2
    linear_combination (2 * (n + 1)) * h2 + (2 * (n + 1) * (2 * n + 4)) * h1 -
      ((2 * n + 4) * (n + 1) ^ 2 * z) * h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hn))

/-- An even logarithm recurrence agrees with its factorially scaled Jacobi recurrence. -/
theorem even_eq_factorial_mul (z : ℂ) {u v : ℕ → ℂ}
    (hu : ∀ k, u (k + 2) = (k + 2) * u (k + 1) + numerator z (k + 1) * u k)
    (hv : ∀ k, v (k + 2) = jacobiDenominator z (k + 1) * v (k + 1) +
      jacobiNumerator z (k + 1) * v k)
    (h0 : u 0 = v 0) (h2 : u 2 = v 1) (n : ℕ) :
    u (2 * n) = (n.factorial : ℂ) * v n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | n
    · simpa using h0
    · simpa using h2
    · rw [even_recurrence z hu, ih (n + 1) (by omega), ih n (by omega), hv n]
      simp only [jacobiDenominator, jacobiNumerator, Nat.add_one_ne_zero, ↓reduceIte,
        Nat.factorial_succ]
      push_cast
      ring

/-- The even continuants of the Stieltjes logarithm fraction are Jacobi continuants. -/
theorem even_continuants (z : ℂ) (n : ℕ) :
    (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).dens (2 * n) =
      (n.factorial : ℂ) * (ofFun 0 (jacobiNumerator z) (jacobiDenominator z)).dens n ∧
    (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).nums (2 * n) =
      2 * (n.factorial : ℂ) * (ofFun 0 (jacobiNumerator z) (jacobiDenominator z)).nums n := by
  constructor
  · apply even_eq_factorial_mul z
    · intro k
      simpa only [Nat.cast_add, Nat.cast_one, show (1 : ℂ) + 1 = 2 by norm_num,
        add_assoc] using
        ofFun_dens_add_two (0 : ℂ) (numerator z) (fun k => (k + 1 : ℂ)) k
    · exact ofFun_dens_add_two _ _ _
    · simp
    · simp [ofFun_dens_add_two, ofFun_dens_one, jacobiDenominator,
        numerator]
      ring
  · have h := even_eq_factorial_mul z
      (u := (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).nums)
      (v := fun k => 2 * (ofFun 0 (jacobiNumerator z) (jacobiDenominator z)).nums k)
    rw [show 2 * (n.factorial : ℂ) *
        (ofFun 0 (jacobiNumerator z) (jacobiDenominator z)).nums n =
        (n.factorial : ℂ) * (2 * (ofFun 0 (jacobiNumerator z) (jacobiDenominator z)).nums n)
      by ring]
    apply h
    · intro k
      simpa only [Nat.cast_add, Nat.cast_one, show (1 : ℂ) + 1 = 2 by norm_num,
        add_assoc] using
        ofFun_nums_add_two (0 : ℂ) (numerator z) (fun k => (k + 1 : ℂ)) k
    · intro k
      linear_combination 2 *
        (ofFun_nums_add_two (0 : ℂ) (jacobiNumerator z) (jacobiDenominator z) k)
    · simp [ofFun]
    · change (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).nums (0 + 2) = _
      rw [ofFun_nums_add_two, ofFun_nums_one, ofFun_nums_zero, ofFun_nums_one]
      norm_num [numerator, jacobiNumerator, ofFun]

/-- The even convergents of the Stieltjes logarithm fraction are twice the Jacobi convergents. -/
theorem even_convs (z : ℂ) (n : ℕ) :
    (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).convs (2 * n) =
      2 * (ofFun 0 (jacobiNumerator z) (jacobiDenominator z)).convs n := by
  obtain ⟨hd, hn⟩ := even_continuants z n
  change _ / _ = 2 * (_ / _)
  rw [hd, hn, mul_assoc, mul_div_assoc, mul_div_mul_left]
  exact_mod_cast Nat.factorial_ne_zero n

/-- The principal logarithm domain with the regular point zero removed. -/
def domain : Set ℂ := {z | z ≠ 0 ∧ 1 + z ∈ slitPlane}

/-- The square-root gap which controls logarithmic Stieltjes convergents. -/
def gap (z : ℂ) : ℝ :=
  max (Real.sqrt ((‖-z⁻¹‖ + (-z⁻¹).re) / 2) - 1)
    (Real.sqrt ((‖-z⁻¹‖ - (-z⁻¹).re) / 2))

/-- The square root of the negative reciprocal stays outside the real unit segment. -/
theorem sqrt_neg_inv_mem {z : ℂ} (hz : z ∈ domain) :
    Complex.sqrt (-z⁻¹) ∈ realSegmentComplement (-1) 1 := by
  let r := Complex.sqrt (-z⁻¹)
  have hr2 : r ^ 2 = -z⁻¹ := Complex.cpow_ofNat_inv_pow _ 2
  have hr0 : r ≠ 0 := by
    intro he
    rw [he, zero_pow (by omega)] at hr2
    exact (neg_ne_zero.mpr (inv_ne_zero hz.1)) hr2.symm
  change r.im ≠ 0 ∨ r.re < -1 ∨ 1 < r.re
  by_contra! h
  have hre0 : r.re ≠ 0 := by
    intro he
    exact hr0 (Complex.ext he h.1)
  have hre : 0 < r.re ^ 2 := sq_pos_of_ne_zero hre0
  have hre1 : r.re ^ 2 ≤ 1 := by nlinarith [h.2.1, h.2.2]
  have he : z * r ^ 2 = -1 := by rw [hr2]; field_simp [hz.1]
  have heim := congrArg Complex.im he
  have here := congrArg Complex.re he
  simp [pow_two, Complex.mul_re, Complex.mul_im, h.1] at heim here
  have hzim : z.im = 0 := heim.resolve_right hre0
  have hzre : -1 < z.re := by
    rcases mem_slitPlane_iff.mp hz.2 with ha | ha
    · simp only [add_re, one_re] at ha
      linarith
    · simp [hzim] at ha
  nlinarith [mul_nonneg (show 0 ≤ z.re + 1 by linarith) hre.le]

/-- The logarithmic gap expressed through the real and imaginary parts of its square root. -/
theorem gap_eq (z : ℂ) : gap z =
    max (|(Complex.sqrt (-z⁻¹)).re| - 1) |(Complex.sqrt (-z⁻¹)).im| := by
  have hr : |(Complex.sqrt (-z⁻¹)).re| = Real.sqrt ((‖-z⁻¹‖ + (-z⁻¹).re) / 2) := by
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp <;> positivity
  have hi : |(Complex.sqrt (-z⁻¹)).im| = Real.sqrt ((‖-z⁻¹‖ - (-z⁻¹).re) / 2) := by
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp <;> positivity
  rw [hr, hi]
  rfl

/-- The square-root gap is positive throughout the punctured logarithm domain. -/
theorem gap_pos {z : ℂ} (hz : z ∈ domain) : 0 < gap z := by
  rw [gap_eq]
  exact max_abs_re_sub_one_abs_im_pos (sqrt_neg_inv_mem hz)

/-- Pole exclusion and a continuous bound for every logarithmic Stieltjes convergent. -/
theorem convergent_bound {z : ℂ} (hz : z ∈ domain) (n : ℕ) :
    (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).dens n ≠ 0 ∧
      ‖(ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).convs n‖ ≤
        ‖z‖ * (1 + ‖-z⁻¹‖) / gap z := by
  let r := Complex.sqrt (-z⁻¹)
  have hr2 : r ^ 2 = -z⁻¹ := Complex.cpow_ofNat_inv_pow _ 2
  have hr0 : r ≠ 0 := by
    intro he
    rw [he, zero_pow (by omega)] at hr2
    exact (neg_ne_zero.mpr (inv_ne_zero hz.1)) hr2.symm
  let a := fun k => (if k = 0 then r else r * r) * numerator z k
  let b := fun k : ℕ => r * (k + 1)
  have hA (k : ℕ) (hk : 1 ≤ k) : a k = -((((k + 1) / 2 : ℕ) : ℂ)) ^ 2 := by
    dsimp [a, numerator]
    simp only [show k ≠ 0 by omega, ↓reduceIte]
    rw [show r * r = -z⁻¹ by simpa only [pow_two] using hr2]
    field_simp [hz.1]
  have hB (k : ℕ) : b k = ((k + 1 : ℝ) : ℂ) * r := by dsimp [b]; push_cast; ring
  have hc (k : ℕ) : (0 : ℝ) ≤ ((k + 1) / 2 : ℕ) := Nat.cast_nonneg _
  have hd (k : ℕ) : (0 : ℝ) < k + 1 := by positivity
  have hcd (k : ℕ) : (((k + 1) / 2 : ℕ) : ℝ) + ((k + 1 + 1) / 2 : ℕ) ≤ k + 1 := by
    exact_mod_cast (show (k + 1) / 2 + (k + 1 + 1) / 2 ≤ k + 1 by omega)
  have hgap := max_abs_re_sub_one_abs_im_pos (sqrt_neg_inv_mem hz)
  have h := ofFun_jacobi_bound (a := a) (b := b) (c := fun k => ((k + 1) / 2 : ℕ))
    (d := fun k => k + 1) hgap hc hd hcd (by simpa using hA) hB n
  have he := ofFun_convs_equiv (h := (0 : ℂ)) (a := numerator z)
    (b := fun k => (k + 1 : ℂ)) (fun _ => r) (fun _ => hr0) n
  have heD := (ofFun_continuants_equiv (h := (0 : ℂ)) (a := numerator z)
    (b := fun k => (k + 1 : ℂ)) (fun _ => r) n).1
  change (ofFun 0 a b).convs n = _ at he
  change (ofFun 0 a b).dens n = _ at heD
  refine ⟨fun hzero => h.1 (by rw [heD, hzero, mul_zero]), ?_⟩
  rw [he] at h
  have hrnorm : ‖r‖ ≤ 1 + ‖-z⁻¹‖ := by
    have he : ‖r‖ ^ 2 = ‖-z⁻¹‖ := by rw [← norm_pow, hr2]
    nlinarith [norm_nonneg r, norm_nonneg (-z⁻¹)]
  rw [← gap_eq] at h
  have hbound : ‖(ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).convs n‖ ≤
      ‖r‖ * ‖z‖ / gap z := by
    simpa only [a, numerator, ↓reduceIte, norm_mul, Nat.cast_zero, zero_add,
      one_mul] using h.2
  exact hbound.trans (div_le_div_of_nonneg_right
    (show ‖r‖ * ‖z‖ ≤ ‖z‖ * (1 + ‖-z⁻¹‖) by nlinarith [norm_nonneg z]) (gap_pos hz).le)

/-- Finite Stieltjes logarithm convergents are holomorphic on the punctured slit domain. -/
theorem differentiableOn_convergent (n : ℕ) :
    DifferentiableOn ℂ (fun z =>
      (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).convs n) domain := by
  refine ofFun_convs_differentiableOn (differentiableOn_const (0 : ℂ)) ?_
    (fun _ => differentiableOn_const _) n (fun z hz => (convergent_bound hz n).1)
  intro k
  by_cases hk : k = 0
  · simpa [numerator, hk] using! (differentiableOn_id : DifferentiableOn ℂ id domain)
  · simpa [numerator, hk] using!
      (differentiableOn_const ((((k + 1) / 2 : ℕ) : ℂ) ^ 2)).mul differentiableOn_id

/-- Finite logarithmic Stieltjes convergents are locally bounded on the punctured slit domain. -/
theorem isLocallyBoundedOn_convergent :
    TauCeti.IsLocallyBoundedOn (fun n z =>
      (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).convs n) domain := by
  have hβ : ContinuousOn (fun z : ℂ => ‖z‖ * (1 + ‖-z⁻¹‖) / gap z) domain := by
    intro z hz
    have hg : ContinuousAt gap z := by
      unfold gap
      fun_prop (disch := exact hz.1)
    exact ((continuous_norm.continuousAt.mul (continuousAt_const.add
      (continuousAt_id.inv₀ hz.1).neg.norm)).div hg (gap_pos hz).ne').continuousWithinAt
  refine TauCeti.isLocallyBoundedOn_def.mpr fun K hKΩ hK => ?_
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hβ.mono hKΩ)
  exact ⟨C, fun n z hz => (convergent_bound (hKΩ hz) n).2.trans
    ((Real.le_norm_self _).trans (hC z hz))⟩

/-- The punctured principal logarithm domain is open. -/
theorem isOpen_domain : IsOpen domain := by
  change IsOpen ({(0 : ℂ)}ᶜ ∩ (fun z : ℂ => 1 + z) ⁻¹' slitPlane)
  exact isOpen_compl_singleton.inter
    (isOpen_slitPlane.preimage (continuous_const.add continuous_id))

/-- The punctured principal logarithm domain is connected. -/
theorem isPreconnected_domain : IsPreconnected domain := by
  let U : Set ℂ := {z | 0 < z.im}
  let R : Set ℂ := {z | 0 < z.re}
  let D : Set ℂ := {z | z.im < 0}
  let L : Set ℂ := {z | -1 < z.re ∧ z.re < 0}
  have hU : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hR : IsPreconnected R := (convex_halfSpace_re_gt 0).isPreconnected
  have hD : IsPreconnected D := (convex_halfSpace_im_lt 0).isPreconnected
  have hL : IsPreconnected L :=
    ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_re_lt 0)).isPreconnected
  have hUR : (U ∩ R).Nonempty := ⟨1 + I, by simp [U, R]⟩
  have hUD : ((U ∪ R) ∩ D).Nonempty := ⟨1 - I, by simp [U, R, D]⟩
  have hUL : (((U ∪ R) ∪ D) ∩ L).Nonempty := ⟨-(1 / 2 : ℂ) + I, by
    norm_num [U, R, D, L]⟩
  have he : domain = ((U ∪ R) ∪ D) ∪ L := by
    ext z
    simp only [domain, U, R, D, L, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨hz0, hz⟩
      by_cases him : z.im = 0
      · have hr : -1 < z.re := by
          rcases mem_slitPlane_iff.mp hz with hr | hr
          · simp only [add_re, one_re] at hr
            linarith
          · simp [him] at hr
        have hre : z.re ≠ 0 := fun he => hz0 (Complex.ext he him)
        rcases lt_or_gt_of_ne hre with hneg | hpos
        · exact Or.inr ⟨hr, hneg⟩
        · exact Or.inl (Or.inl (Or.inr hpos))
      · rcases lt_or_gt_of_ne him with hneg | hpos
        · exact Or.inl (Or.inr hneg)
        · exact Or.inl (Or.inl (Or.inl hpos))
    · intro h
      have hz0 : z ≠ 0 := by
        intro he
        subst z
        norm_num at h
      refine ⟨hz0, ?_⟩
      apply mem_slitPlane_iff.mpr
      rcases h with ((hu | hr) | hd) | hl
      · right; simpa using hu.ne'
      · left; simp only [add_re, one_re]; linarith
      · right; simpa using hd.ne
      · left; simp only [add_re, one_re]; linarith [hl.1]
  rw [he]
  exact IsPreconnected.union' hUL
    (IsPreconnected.union' hUD (IsPreconnected.union' hUR hU hR) hD) hL

/-- The logarithm Stieltjes fraction has a limit at every positive real argument. -/
theorem exists_tendsto_convergent_ofReal {x : ℝ} (hx : 0 < x) :
    ∃ v : ℂ, Tendsto (ofFun 0 (numerator x) (fun k => (k + 1 : ℂ))).convs atTop (𝓝 v) := by
  let a : ℕ → ℝ := fun k => if k = 0 then x else (((k + 1) / 2 : ℕ) : ℝ) ^ 2 * x
  have ha (k : ℕ) : 0 < a k := by
    by_cases hk : k = 0
    · simpa [a, hk] using hx
    · have hceil : 0 < (k + 1) / 2 := by omega
      dsimp [a]
      simp only [hk, ↓reduceIte]
      exact mul_pos (sq_pos_of_pos (Nat.cast_pos.mpr hceil)) hx
  have hC (k : ℕ) : a k /
      (if k = 0 then (1 : ℝ) else ((k - 1 : ℕ) + 1 : ℝ) * (k + 1)) ≤ x := by
    by_cases hk : k = 0
    · simp [a, hk]
    · have he : ((k - 1 : ℕ) : ℝ) + 1 = k := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ k))
      have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
      have hc : (((k + 1) / 2 : ℕ) : ℝ) ^ 2 ≤ (k : ℝ) * (k + 1) := by
        exact_mod_cast (show ((k + 1) / 2) ^ 2 ≤ k * (k + 1) by
          simpa only [pow_two] using Nat.mul_le_mul
            (show (k + 1) / 2 ≤ k by omega) (show (k + 1) / 2 ≤ k + 1 by omega))
      simp only [a, hk, ↓reduceIte, he]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hc hx.le]
  obtain ⟨v, hv⟩ := exists_tendsto_ofFun_convs_of_pos_normalized_bounded 0 ha
    (b := fun k => (k + 1 : ℝ)) (fun k => by positivity)
    (by simpa only [Nat.cast_zero, zero_add] using hC)
  have hf (n : ℕ) : (ofFun 0 (numerator x) (fun k => (k + 1 : ℂ))).convs n =
      ((ofFun 0 a (fun k => (k + 1 : ℝ))).convs n : ℂ) := by
    have heA : numerator (x : ℂ) = fun k => Complex.ofRealHom (a k) := by
      funext k
      by_cases hk : k = 0 <;> simp [numerator, a, hk]
    have heB : (fun k : ℕ => (k + 1 : ℂ)) =
        fun k : ℕ => Complex.ofRealHom (k + 1 : ℝ) := by funext k; simp
    rw [heA, heB, show (0 : ℂ) = Complex.ofRealHom 0 from rfl, ofFun_convs_map]
    rfl
  refine ⟨(v : ℂ), ?_⟩
  have h := continuous_ofReal.continuousAt.tendsto.comp hv
  change Tendsto (fun n => _) atTop _
  simpa only [hf, Function.comp_def] using! h

/-- The even Stieltjes convergents converge to the principal logarithm on the positive axis. -/
theorem tendsto_even_convergent_ofReal {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n => (ofFun 0 (numerator x) (fun k => (k + 1 : ℂ))).convs (2 * n))
      atTop (𝓝 (Complex.log (1 + (x : ℂ)))) := by
  let t : ℂ := (x : ℂ) / (x + 2)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hx2 : (x : ℂ) + 2 ≠ 0 := by exact_mod_cast (by linarith : x + 2 ≠ 0)
  have ht0 : t ≠ 0 := div_ne_zero hx0 hx2
  have hdom : t.im ≠ 0 ∨ |t.re| < 1 := by
    right
    have he : t = ((x / (x + 2) : ℝ) : ℂ) := by dsimp [t]; push_cast; rfl
    rw [he, ofReal_re, abs_of_pos (div_pos hx (by linarith))]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have h := (LogarithmContinuedFraction.tendsto_arctanh ht0 hdom).const_mul (2 : ℂ)
  have he (n : ℕ) :
      (ofFun 0 (jacobiNumerator x) (jacobiDenominator x)).convs n =
      (ofFun 0 (fun k => if k = 0 then t else -(k : ℂ) ^ 2 * t ^ 2)
        (fun k => (2 * k + 1 : ℂ))).convs n := by
    have hA : (fun k : ℕ =>
        (if k = 0 then (x : ℂ) + 2 else ((x : ℂ) + 2) * ((x : ℂ) + 2)) *
          (if k = 0 then t else -(k : ℂ) ^ 2 * t ^ 2)) = jacobiNumerator x := by
      funext k
      by_cases hk : k = 0 <;> simp [jacobiNumerator, hk, t] <;> field_simp
    have hB : (fun k : ℕ => ((x : ℂ) + 2) * (2 * k + 1)) = jacobiDenominator x := by
      funext k
      dsimp [jacobiDenominator]
      ring
    have hh := ofFun_convs_equiv (h := (0 : ℂ))
      (a := fun k => if k = 0 then t else -(k : ℂ) ^ 2 * t ^ 2)
      (b := fun k => (2 * k + 1 : ℂ)) (fun _ => (x : ℂ) + 2) (fun _ => hx2) n
    rw [hA, hB] at hh
    exact hh
  have hval : 2 * arctanh t = Complex.log (1 + (x : ℂ)) := by
    rw [arctanh]
    have ht : (1 + t) / (1 - t) = 1 + (x : ℂ) := by dsimp [t]; field_simp; ring
    rw [ht]
    ring
  simpa only [even_convs, he, hval] using h

/-- Positive Stieltjes convergence and even contraction identify the full real limit. -/
theorem tendsto_convergent_ofReal {x : ℝ} (hx : 0 < x) :
    Tendsto (ofFun 0 (numerator x) (fun k => (k + 1 : ℂ))).convs atTop
      (𝓝 (Complex.log (1 + (x : ℂ)))) := by
  obtain ⟨v, hv⟩ := exists_tendsto_convergent_ofReal hx
  have hm : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 2 * n; omega) tendsto_id
  have hv' := hv.comp hm
  have he := tendsto_even_convergent_ofReal hx
  have hvEq : v = Complex.log (1 + (x : ℂ)) := tendsto_nhds_unique hv' he
  rwa [hvEq] at hv

/-- The Stieltjes logarithm fraction converges throughout its punctured principal domain. -/
theorem tendsto_convergent {z : ℂ} (hz : z ∈ domain) :
    Tendsto (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).convs atTop
      (𝓝 (Complex.log (1 + z))) := by
  let f : ℕ → ℂ → ℂ := fun n z =>
    (ofFun 0 (numerator z) (fun k => (k + 1 : ℂ))).convs n
  let g : ℂ → ℂ := fun z => Complex.log (1 + z)
  let A : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioi 0
  have hAΩ : A ⊆ domain := by
    rintro _ ⟨t, ht, rfl⟩
    change 0 < t at ht
    refine ⟨ofReal_ne_zero.mpr ht.ne', ?_⟩
    left
    simp only [add_re, one_re, ofReal_re]
    linarith
  have htend : Tendsto (fun n : ℕ => (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
      simp only [add_zero] at h
      simpa [Function.comp_def] using (continuous_ofReal.tendsto 1).comp h
    · simp only [mem_compl_iff, mem_singleton_iff]
      have hn : (1 : ℝ) + 1 / ((n : ℝ) + 1) ≠ 1 := by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      exact_mod_cast hn
  have hmem : ∀ n : ℕ, (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ A := by
    intro n
    refine ⟨(1 : ℝ) + 1 / ((n : ℝ) + 1), ?_, rfl⟩
    change 0 < (1 : ℝ) + 1 / ((n : ℝ) + 1)
    positivity
  have hacc : AccPt (1 : ℂ) (𝓟 A) :=
    accPt_iff_frequently_nhdsNE.mpr (htend.frequently (Frequently.of_forall hmem))
  have hone : (1 : ℂ) ∈ domain := by
    refine ⟨one_ne_zero, ?_⟩
    left
    norm_num
  obtain ⟨G, hG, hGA, hconv⟩ := TauCeti.vitali_of_tendsto isOpen_domain
    isPreconnected_domain differentiableOn_convergent isLocallyBoundedOn_convergent
    hAΩ hone hacc (g := g) (by
      rintro _ ⟨t, ht, rfl⟩
      exact tendsto_convergent_ofReal ht)
  have hg : DifferentiableOn ℂ g domain := by
    intro z hz
    have hd : DifferentiableAt ℂ (fun w : ℂ => 1 + w) z :=
      (differentiableAt_const (1 : ℂ)).add differentiableAt_id
    exact (hd.clog hz.2).differentiableWithinAt
  have heq : EqOn G g domain :=
    (hG.analyticOnNhd isOpen_domain).eqOn_of_preconnected_of_frequently_eq
      (hg.analyticOnNhd isOpen_domain) isPreconnected_domain hone
      (htend.frequently (Frequently.of_forall fun n => hGA (hmem n)))
  change Tendsto (fun n => f n z) atTop (𝓝 (g z))
  rw [← heq hz]
  exact hconv.tendsto_at hz

/-- The principal logarithm has its Stieltjes continued fraction on the full slit domain. -/
theorem hasContinuedFraction_log_one_add {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    DLMF.Core.HasContinuedFraction (numerator z) (fun k => (k + 1 : ℂ))
      (Complex.log (1 + z)) := by
  by_cases hz0 : z = 0
  · subst z
    unfold DLMF.Core.HasContinuedFraction
    have he (n : ℕ) : DLMF.Core.continuedFractionTail (numerator 0)
        (fun k => (k + 1 : ℂ)) 0 n = 0 := by
      cases n with
      | zero => simp [DLMF.Core.continuedFractionTail,
          DLMF.Core.continuedFractionContinuants]
      | succ n =>
        rw [DLMF.Confluent.IncompleteGammaFractions.continuedFractionTail_freeze
          (by norm_num [numerator]) (by omega)]
        norm_num [numerator]
    change Tendsto (fun n => _) atTop _
    simp_rw [he]
    simp
  · rw [DLMF.Confluent.IncompleteGammaFractions.hasContinuedFraction_iff]
    · exact tendsto_convergent ⟨hz0, hz⟩
    · intro k hk
      have hc : 0 < (k + 1) / 2 := by omega
      simp only [numerator, show k ≠ 0 by omega, ↓reduceIte, mul_ne_zero_iff,
        pow_ne_zero_iff (by omega : 2 ≠ 0)]
      exact ⟨Nat.cast_ne_zero.mpr hc.ne', hz0⟩

end DLMF.Elementary.LogarithmContraction
