/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.HermiteFixedX
public import DLMF.OrthogonalPolynomials.BoundsZeros
public import DLMFMathlib.Analysis.ODE.SturmComparison
public import Mathlib.Order.Fin.Basic

/-!
# Individual positive Hermite zeros

Beals–Wong Theorem 5.3.2. The existing Hermite function satisfies
`u'' + (2n+1-x²) u = 0`. Sturm comparison gives lower bounds for the gaps;
comparison with a translated solution gives increasing positive gaps and upper bounds
for each indexed zero. The existing Hermite–Laguerre identities enumerate the positive zeros.
-/

@[expose] public noncomputable section

open Real Set Polynomial
open scoped Topology

namespace DLMF.OrthogonalPolynomials

open HermiteFixedX

namespace HermiteZeroBounds

/-- The real polynomial evaluation agrees with the existing complex Hermite evaluation. -/
lemma ofReal_eval (n : ℕ) (t : ℝ) :
    (((hermitePolyHR n).eval t : ℝ) : ℂ) = (aeval (t : ℂ) (hermitePolyH n) : ℂ) := by
  rw [aeval_hermitePolyH_complex, eval_map_ofReal]

/-- The Gaussian factor introduces no additional zeros. -/
lemma zero_iff (n : ℕ) (t : ℝ) :
    HermiteFixedX.u n t = 0 ↔ (aeval (t : ℂ) (hermitePolyH n) : ℂ) = 0 := by
  rw [HermiteFixedX.u, mul_eq_zero, or_iff_right (exp_ne_zero _), ← ofReal_eval,
    Complex.ofReal_eq_zero]

/-- Even Hermite functions are even. -/
lemma u_even (m : ℕ) (t : ℝ) : HermiteFixedX.u (2 * m) (-t) = HermiteFixedX.u (2 * m) t := by
  have hp : (hermitePolyHR (2 * m)).eval (-t) = (hermitePolyHR (2 * m)).eval t := by
    apply Complex.ofReal_injective
    rw [ofReal_eval, ofReal_eval, Complex.ofReal_neg,
      hermitePolyH_even_eq_laguerrePolyL, hermitePolyH_even_eq_laguerrePolyL, neg_sq]
  simp only [HermiteFixedX.u, neg_sq, hp]

/-- Even Hermite functions do not vanish at zero. -/
lemma u_even_zero_ne (m : ℕ) : HermiteFixedX.u (2 * m) 0 ≠ 0 := by
  rw [HermiteFixedX.u_zero, HermiteFixedX.hermitePolyHR_even_eval_zero]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (div_ne_zero (Nat.cast_ne_zero.mpr (2 * m).factorial_ne_zero)
      (Nat.cast_ne_zero.mpr m.factorial_ne_zero))

/-- Positive Hermite zeros are square roots of the corresponding Laguerre zeros. -/
private lemma positive_roots_of_laguerre {n m : ℕ} {α : ℝ} (hα : -1 < α)
    (hrel : ∀ t : ℝ, 0 < t → (HermiteFixedX.u n t = 0 ↔
      laguerrePolyL α m ((t : ℂ) ^ 2) = 0)) :
    ∃ x : Fin m → ℝ, StrictMono x ∧ (∀ i, 0 < x i) ∧
      ∀ t : ℝ, 0 < t → (HermiteFixedX.u n t = 0 ↔ ∃ i, t = x i) := by
  obtain ⟨r, hr, hrpos, hroots⟩ := laguerrePolyL_zeros_pos hα m
  let x : Fin m → ℝ := fun i => sqrt (r i)
  have hxpos (i : Fin m) : 0 < x i := sqrt_pos.mpr (hrpos i)
  refine ⟨x, fun i j hij => sqrt_lt_sqrt (hrpos i).le (hr hij), hxpos, ?_⟩
  intro t ht
  rw [hrel t ht, hroots]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, (sq_eq_sq₀ ht.le (hxpos i).le).mp ?_⟩
    have hi' : t ^ 2 = r i := by exact_mod_cast hi
    rw [hi', Real.sq_sqrt (hrpos i).le]
  · rintro ⟨i, rfl⟩
    exact ⟨i, by exact_mod_cast Real.sq_sqrt (hrpos i).le⟩

/-- The positive zeros of an even Hermite polynomial, in increasing order. -/
lemma positive_roots_even (m : ℕ) :
    ∃ x : Fin m → ℝ, StrictMono x ∧ (∀ i, 0 < x i) ∧
      ∀ t : ℝ, 0 < t → (HermiteFixedX.u (2 * m) t = 0 ↔ ∃ i, t = x i) := by
  apply positive_roots_of_laguerre (α := -(1 / 2)) (by norm_num)
  intro t _
  rw [zero_iff, hermitePolyH_even_eq_laguerrePolyL]
  have hc : (-1 : ℂ) ^ m * 2 ^ (2 * m) * m.factorial ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
  rw [mul_eq_zero, or_iff_right hc]
  norm_num

/-- The positive zeros of an odd Hermite polynomial, in increasing order. -/
lemma positive_roots_odd (m : ℕ) :
    ∃ x : Fin m → ℝ, StrictMono x ∧ (∀ i, 0 < x i) ∧
      ∀ t : ℝ, 0 < t → (HermiteFixedX.u (2 * m + 1) t = 0 ↔ ∃ i, t = x i) := by
  apply positive_roots_of_laguerre (α := 1 / 2) (by norm_num)
  intro t ht
  rw [zero_iff, hermitePolyH_odd_eq_laguerrePolyL]
  have hc : (-1 : ℂ) ^ m * 2 ^ (2 * m + 1) * m.factorial * t ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num))) (Nat.cast_ne_zero.mpr m.factorial_ne_zero))
      (Complex.ofReal_ne_zero.mpr ht.ne')
  rw [mul_eq_zero, or_iff_right hc]
  norm_num

/-- Consecutive nonnegative Hermite zeros are farther apart than a free half-period. -/
lemma pi_div_freq_lt_gap (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hza : HermiteFixedX.u n a = 0) (hzb : HermiteFixedX.u n b = 0)
    (hno : ∀ t ∈ Ioo a b, HermiteFixedX.u n t ≠ 0) :
    π / freq n < b - a := by
  have hω := freq_pos n
  by_contra hle
  push Not at hle
  have hsine (t : ℝ) : HasDerivAt (fun t => sin (freq n * (t - a)))
      (freq n * cos (freq n * (t - a))) t := by
    have hd : HasDerivAt (fun t : ℝ => freq n * (t - a)) (freq n) t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul (freq n)
    exact hd.sin.congr_deriv (by ring)
  have hcosine (t : ℝ) : HasDerivAt (fun t => freq n * cos (freq n * (t - a)))
      (-(freq n ^ 2 * sin (freq n * (t - a)))) t := by
    have hd : HasDerivAt (fun t : ℝ => freq n * (t - a)) (freq n) t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul (freq n)
    exact (hd.cos.const_mul (freq n)).congr_deriv (by ring)
  obtain ⟨t, ht, hz⟩ := ODE.sturm_comparison_strict (p := fun _ => 1)
    (q₁ := fun t => freq n ^ 2 - t ^ 2) (q₂ := fun _ => freq n ^ 2)
    (u := HermiteFixedX.u n) (u' := HermiteFixedX.u' n)
    (v := fun t => sin (freq n * (t - a))) (v' := fun t => freq n * cos (freq n * (t - a))) hab
    (fun t _ => hasDerivAt_u n t)
    (fun t _ => by simpa only [one_mul, sub_mul, neg_sub, neg_mul] using hasDerivAt_u' n t)
    (fun t _ => hsine t) (fun t _ => by simpa only [one_mul] using hcosine t)
    zero_le_one zero_le_one (fun t ht => by nlinarith [sq_pos_of_pos (lt_of_le_of_lt ha ht.1)])
    hza hzb hno
  have harg : freq n * (t - a) < π := by
    have := (le_div_iff₀ hω).mp hle
    nlinarith [ht.2]
  exact (sin_pos_of_pos_of_lt_pi (mul_pos hω (by linarith [ht.1])) harg).ne' hz

/-- Translating the Hermite equation shows that successive positive gaps increase.
The earlier left endpoint may be zero without being a root. -/
lemma increasing_gap (n : ℕ) {l a b : ℝ} (hl : 0 ≤ l) (hla : l < a) (hab : a < b)
    (hza : HermiteFixedX.u n a = 0) (hzb : HermiteFixedX.u n b = 0)
    (hno : ∀ t ∈ Ioo l a, HermiteFixedX.u n t ≠ 0)
    (hno' : ∀ t ∈ Ioo a b, HermiteFixedX.u n t ≠ 0) :
    a - l < b - a := by
  by_contra hle
  push Not at hle
  let d := a - l
  have hd : 0 < d := sub_pos.mpr hla
  obtain ⟨t, ht, hz⟩ := ODE.sturm_comparison_strict (p := fun _ => 1)
    (q₁ := fun t => freq n ^ 2 - t ^ 2) (q₂ := fun t => freq n ^ 2 - (t - d) ^ 2)
    (u := HermiteFixedX.u n) (u' := HermiteFixedX.u' n)
    (v := fun t => HermiteFixedX.u n (t - d))
    (v' := fun t => HermiteFixedX.u' n (t - d)) hab
    (fun t _ => hasDerivAt_u n t)
    (fun t _ => by simpa only [one_mul, sub_mul, neg_sub, neg_mul] using hasDerivAt_u' n t)
    (fun t _ => by simpa only [Function.comp_def, id_eq, mul_one] using
      (hasDerivAt_u n (t - d)).comp t ((hasDerivAt_id t).sub_const d))
    (fun t _ => by
      simpa only [Function.comp_def, id_eq, one_mul, mul_one, sub_mul, neg_sub, neg_mul] using
        (hasDerivAt_u' n (t - d)).comp t ((hasDerivAt_id t).sub_const d))
    zero_le_one zero_le_one (fun t ht => by dsimp [d]; nlinarith [ht.1]) hza hzb hno'
  exact hno (t - d) ⟨by dsimp [d]; linarith [ht.1], by dsimp [d]; linarith [ht.2]⟩ hz

/-- The first positive even Hermite zero is beyond the first free cosine zero. -/
lemma first_even_lower (m : ℕ) {a : ℝ} (ha : 0 < a)
    (hza : HermiteFixedX.u (2 * m) a = 0)
    (hno : ∀ t ∈ Ioo 0 a, HermiteFixedX.u (2 * m) t ≠ 0) :
    π / (2 * freq (2 * m)) < a := by
  let n := 2 * m
  have hω := freq_pos n
  have hno' : ∀ t ∈ Ioo (-a) a, HermiteFixedX.u n t ≠ 0 := by
    intro t ht
    by_cases htpos : 0 < t
    · exact hno t ⟨htpos, ht.2⟩
    by_cases htz : t = 0
    · subst t
      exact u_even_zero_ne m
    intro hz
    have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) htz
    exact hno (-t) ⟨by linarith, by linarith [ht.1]⟩ ((u_even m t).trans hz)
  by_contra hle
  push Not at hle
  have hbound : freq n * a ≤ π / 2 := by
    have := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hω)).mp hle
    nlinarith
  have hcospos (t : ℝ) (ht : t ∈ Ioo (-a) a) : 0 < cos (freq n * t) := by
    apply cos_pos_of_mem_Ioo
    constructor <;> nlinarith [ht.1, ht.2]
  have hcos (t : ℝ) : HasDerivAt (fun t => cos (freq n * t))
      (-freq n * sin (freq n * t)) t := by
    exact (((hasDerivAt_id t).const_mul (freq n)).cos).congr_deriv (by simp only [id_eq]; ring)
  have hsin (t : ℝ) : HasDerivAt (fun t => -freq n * sin (freq n * t))
      (-(freq n ^ 2 * cos (freq n * t))) t := by
    exact ((((hasDerivAt_id t).const_mul (freq n)).sin).const_mul (-freq n)).congr_deriv
      (by simp only [id_eq]; ring)
  have hp (t : ℝ) : HasDerivAt (fun t => 1 * HermiteFixedX.u' n t)
      (-((freq n ^ 2 - t ^ 2) * HermiteFixedX.u n t)) t := by
    simpa only [one_mul, sub_mul, neg_sub, neg_mul] using hasDerivAt_u' n t
  rcases ODE.sturm_comparison (p := fun _ => 1)
    (q₁ := fun t => freq n ^ 2 - t ^ 2) (q₂ := fun _ => freq n ^ 2)
    (u := HermiteFixedX.u n) (u' := HermiteFixedX.u' n)
    (v := fun t => cos (freq n * t)) (v' := fun t => -freq n * sin (freq n * t))
    (by linarith) (fun t _ => hasDerivAt_u n t) (fun t _ => hp t)
    (fun t _ => hcos t) (fun t _ => by simpa only [one_mul] using hsin t)
    zero_le_one zero_le_one (fun t _ => by nlinarith [sq_nonneg t])
    (by rwa [u_even]) hza hno' with hz | hW
  · obtain ⟨t, ht, hz⟩ := hz
    exact (hcospos t ht).ne' hz
  · have ht : a / 2 ∈ Ioo (-a) a := by constructor <;> linarith
    have hd := ODE.hasDerivAt_sturmWronskian (p := fun _ => 1)
      (q₁ := fun t => freq n ^ 2 - t ^ 2) (q₂ := fun _ => freq n ^ 2)
      (u := HermiteFixedX.u n) (u' := HermiteFixedX.u' n)
      (v := fun t => cos (freq n * t)) (v' := fun t => -freq n * sin (freq n * t))
      (hasDerivAt_u n (a / 2)) (hp (a / 2))
      (hcos (a / 2)) (by simpa only [one_mul] using hsin (a / 2))
    have hloc : ODE.sturmWronskian (fun _ => 1) (HermiteFixedX.u n) (HermiteFixedX.u' n)
        (fun t => cos (freq n * t)) (fun t => -freq n * sin (freq n * t)) =ᶠ[𝓝 (a / 2)]
          fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t ht using hW t ⟨ht.1.le, ht.2.le⟩
    have hd0 := hd.unique ((hasDerivAt_const (a / 2) (0 : ℝ)).congr_of_eventuallyEq hloc)
    have hz : (a / 2) ^ 2 * HermiteFixedX.u n (a / 2) * cos (freq n * (a / 2)) = 0 := by
      simpa only [sub_sub_cancel] using hd0
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by linarith)) (hno' _ ht))
      (hcospos _ ht).ne') hz

/-- With zero as a virtual preceding point, each positive-root interval is zero-free. -/
private lemma previous_intervals {n m : ℕ} (x : Fin (m + 1) → ℝ) (hx : StrictMono x)
    (hxpos : ∀ i, 0 < x i)
    (hcomplete : ∀ t : ℝ, 0 < t → (HermiteFixedX.u n t = 0 ↔ ∃ i, t = x i)) :
    let prev : Fin (m + 1) → ℝ := Fin.cases 0 (fun i : Fin m => x i.castSucc)
    (∀ i, 0 ≤ prev i ∧ prev i < x i) ∧
      ∀ i, ∀ t ∈ Ioo (prev i) (x i), HermiteFixedX.u n t ≠ 0 := by
  let prev : Fin (m + 1) → ℝ := Fin.cases 0 (fun i : Fin m => x i.castSucc)
  have hprev : ∀ i, 0 ≤ prev i ∧ prev i < x i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨le_rfl, hxpos 0⟩
    · exact ⟨(hxpos j.castSucc).le, hx (show j.castSucc < j.succ from Fin.castSucc_lt_succ)⟩
  refine ⟨hprev, ?_⟩
  intro i t ht hz
  obtain ⟨j, hj⟩ := (hcomplete t (lt_of_le_of_lt (hprev i).1 ht.1)).mp hz
  revert ht
  refine Fin.cases ?_ (fun k => ?_) i
  · intro ht
    have := hx.monotone (Fin.zero_le j)
    linarith [ht.2]
  · intro ht
    by_cases hjle : j ≤ k.castSucc
    · have := hx.monotone hjle
      have htp : x k.castSucc < t := ht.1
      linarith
    · have hkj : k.succ ≤ j := by
        change k.val + 1 ≤ j.val
        change ¬j.val ≤ k.val at hjle
        omega
      have := hx.monotone hkj
      linarith [ht.2]

/-- The indexed positive Hermite zero is below its index times the mean radius.
The proof uses increasing gaps and the already proved outermost-zero bound. -/
lemma upper_bound {n m : ℕ} (x : Fin m → ℝ) (hx : StrictMono x)
    (hxpos : ∀ i, 0 < x i)
    (hcomplete : ∀ t : ℝ, 0 < t → (HermiteFixedX.u n t = 0 ↔ ∃ i, t = x i)) :
    ∀ i : Fin m, x i < ((i : ℝ) + 1) * freq n / m := by
  cases m with
  | zero => exact fun i => Fin.elim0 i
  | succ m =>
    let prev : Fin (m + 1) → ℝ := Fin.cases 0 (fun i : Fin m => x i.castSucc)
    let g (i : Fin (m + 1)) : ℝ := x i - prev i
    obtain ⟨hprev, hno⟩ := previous_intervals x hx hxpos hcomplete
    have hgsucc (i : Fin m) : g i.succ = x i.succ - x i.castSucc := rfl
    have hgstep (i : Fin m) : g i.castSucc < g i.succ := by
      exact increasing_gap n (hprev i.castSucc).1 (hprev i.castSucc).2
        (hx (show i.castSucc < i.succ from Fin.castSucc_lt_succ))
        ((hcomplete _ (hxpos i.castSucc)).mpr ⟨i.castSucc, rfl⟩)
        ((hcomplete _ (hxpos i.succ)).mpr ⟨i.succ, rfl⟩)
        (hno i.castSucc) (hno i.succ)
    have havg : ∀ i : Fin (m + 1), x i ≤ ((i : ℝ) + 1) * g i := by
      intro i
      induction i using Fin.induction with
      | zero => simp [g, prev]
      | succ i ih =>
        have hmul := mul_le_mul_of_nonneg_left (hgstep i).le
          (by positivity : 0 ≤ (i.val : ℝ) + 1)
        have hrel : x i.succ = x i.castSucc + g i.succ := by rw [hgsucc]; ring
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at ih ⊢
        nlinarith
    have hratio : Monotone (fun i : Fin (m + 1) => x i / ((i : ℝ) + 1)) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hmul := mul_le_mul_of_nonneg_left (hgstep i).le
        (by positivity : 0 ≤ (i.val : ℝ) + 1)
      have ha := havg i.castSucc
      have hrel : x i.succ = x i.castSucc + g i.succ := by rw [hgsucc]; ring
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at ha ⊢
      nlinarith
    have hlastroot := (hcomplete _ (hxpos (Fin.last m))).mpr ⟨Fin.last m, rfl⟩
    have hlast : x (Fin.last m) < freq n := by
      have hz : (hermitePolyHR n).eval (x (Fin.last m)) = 0 := by
        exact (mul_eq_zero.mp hlastroot).resolve_left (exp_ne_zero _)
      have := abs_lt_sqrt_of_hermitePolyHR_eval_eq_zero hz
      exact (le_abs_self _).trans_lt this
    intro i
    have hr := hratio (Fin.le_last i)
    have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hden : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    simp only [Fin.val_last] at hr
    have hr' := (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mp hr
    apply (lt_div_iff₀ hm).mpr
    have := mul_lt_mul_of_pos_left hlast hden
    push_cast
    nlinarith

/-- A first-zero lower bound propagates through all positive Hermite zeros. -/
lemma lower_bound {n m : ℕ} (x : Fin m → ℝ) (hx : StrictMono x)
    (hxpos : ∀ i, 0 < x i)
    (hcomplete : ∀ t : ℝ, 0 < t → (HermiteFixedX.u n t = 0 ↔ ∃ i, t = x i))
    (A : ℝ) (hfirst : ∀ i : Fin m, i.val = 0 → A < x i) :
    ∀ i : Fin m, A + (i : ℝ) * (π / freq n) < x i := by
  cases m with
  | zero => exact fun i => Fin.elim0 i
  | succ m =>
    obtain ⟨-, hno⟩ := previous_intervals x hx hxpos hcomplete
    intro i
    induction i using Fin.induction with
    | zero => simpa using hfirst 0 rfl
    | succ i ih =>
      have hgap := pi_div_freq_lt_gap n (hxpos i.castSucc).le
        (hx (show i.castSucc < i.succ from Fin.castSucc_lt_succ))
        ((hcomplete _ (hxpos i.castSucc)).mpr ⟨i.castSucc, rfl⟩)
        ((hcomplete _ (hxpos i.succ)).mpr ⟨i.succ, rfl⟩) (hno i.succ)
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at ih ⊢
      linarith

end HermiteZeroBounds

/-- Individual positive zeros of `H_{2m}`, Beals–Wong (5.3.18), with zero-based indices.
Here `freq (2m) = √(4m+1)`. Both inequalities are strict. -/
theorem hermite_even_positive_zero_bounds (m : ℕ) :
    ∃ x : Fin m → ℝ, StrictMono x ∧ (∀ i, 0 < x i) ∧
      (∀ t : ℝ, 0 < t → ((aeval (t : ℂ) (hermitePolyH (2 * m)) : ℂ) = 0 ↔ ∃ i, t = x i)) ∧
      ∀ i : Fin m, (2 * (i : ℝ) + 1) * π / (2 * freq (2 * m)) < x i ∧
        x i < (4 * ((i : ℝ) + 1) + 1) / freq (2 * m) := by
  obtain ⟨x, hx, hxpos, hcomplete⟩ := HermiteZeroBounds.positive_roots_even m
  have hu := HermiteZeroBounds.upper_bound x hx hxpos hcomplete
  have hfirst (i : Fin m) (hi : i.val = 0) : π / (2 * freq (2 * m)) < x i := by
    apply HermiteZeroBounds.first_even_lower m (hxpos i)
      ((hcomplete _ (hxpos i)).mpr ⟨i, rfl⟩)
    intro t ht hz
    obtain ⟨j, hj⟩ := (hcomplete t ht.1).mp hz
    have := hx.monotone (show i ≤ j by change i.val ≤ j.val; omega)
    linarith [ht.2]
  have hl := HermiteZeroBounds.lower_bound x hx hxpos hcomplete _ hfirst
  refine ⟨x, hx, hxpos, fun t ht => ?_, fun i => ?_⟩
  · rw [← HermiteZeroBounds.zero_iff]
    exact hcomplete t ht
  · constructor
    · have he : π / (2 * freq (2 * m)) + (i : ℝ) * (π / freq (2 * m)) =
          (2 * (i : ℝ) + 1) * π / (2 * freq (2 * m)) := by
        field_simp [freq_pos (2 * m) |>.ne']
        ring
      rw [← he]
      exact hl i
    · apply (hu i).trans_le
      have hm : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
      apply (div_le_div_iff₀ hm (freq_pos _)).mpr
      have hi : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
      have hsq : freq (2 * m) ^ 2 = 4 * (m : ℝ) + 1 := by rw [freq_sq]; push_cast; ring
      have hmul := congrArg (fun v : ℝ => ((i : ℝ) + 1) * v) hsq
      nlinarith

/-- Individual positive zeros of `H_{2m+1}`, Beals–Wong (5.3.19), with zero-based indices.
Here `freq (2m+1) = √(4m+3)`. Both inequalities are strict. -/
theorem hermite_odd_positive_zero_bounds (m : ℕ) :
    ∃ x : Fin m → ℝ, StrictMono x ∧ (∀ i, 0 < x i) ∧
      (∀ t : ℝ, 0 < t → ((aeval (t : ℂ) (hermitePolyH (2 * m + 1)) : ℂ) = 0 ↔ ∃ i, t = x i)) ∧
      ∀ i : Fin m, ((i : ℝ) + 1) * π / freq (2 * m + 1) < x i ∧
        x i < (4 * ((i : ℝ) + 1) + 3) / freq (2 * m + 1) := by
  obtain ⟨x, hx, hxpos, hcomplete⟩ := HermiteZeroBounds.positive_roots_odd m
  have hu := HermiteZeroBounds.upper_bound x hx hxpos hcomplete
  have hfirst (i : Fin m) (hi : i.val = 0) : π / freq (2 * m + 1) < x i := by
    have hz : HermiteFixedX.u (2 * m + 1) 0 = 0 := by
      rw [HermiteFixedX.u_zero, HermiteFixedX.hermitePolyHR_eval_zero,
        HermiteFixedX.hermitePolyH_odd_at_zero]
      norm_num
    have hno : ∀ t ∈ Ioo 0 (x i), HermiteFixedX.u (2 * m + 1) t ≠ 0 := by
      intro t ht hz
      obtain ⟨j, hj⟩ := (hcomplete t ht.1).mp hz
      have := hx.monotone (show i ≤ j by change i.val ≤ j.val; omega)
      linarith [ht.2]
    simpa only [sub_zero] using
      HermiteZeroBounds.pi_div_freq_lt_gap (2 * m + 1) le_rfl (hxpos i) hz
        ((hcomplete _ (hxpos i)).mpr ⟨i, rfl⟩) hno
  have hl := HermiteZeroBounds.lower_bound x hx hxpos hcomplete _ hfirst
  refine ⟨x, hx, hxpos, fun t ht => ?_, fun i => ?_⟩
  · rw [← HermiteZeroBounds.zero_iff]
    exact hcomplete t ht
  · constructor
    · have he : π / freq (2 * m + 1) + (i : ℝ) * (π / freq (2 * m + 1)) =
          ((i : ℝ) + 1) * π / freq (2 * m + 1) := by ring
      rw [← he]
      exact hl i
    · apply (hu i).trans_le
      have hm : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
      apply (div_le_div_iff₀ hm (freq_pos _)).mpr
      have hi : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
      have hsq : freq (2 * m + 1) ^ 2 = 4 * (m : ℝ) + 3 := by rw [freq_sq]; push_cast; ring
      have hmul := congrArg (fun v : ℝ => ((i : ℝ) + 1) * v) hsq
      nlinarith

end DLMF.OrthogonalPolynomials
