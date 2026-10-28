/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Zeros.ZeroLimits

/-!
# Real zeros of Euler polynomials

Bounds and limiting locations of Euler polynomial zeros, together with multiple-zero statements.

Source references and common attribution are retained in
`DLMF.BernoulliEuler.Zeros`.
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology Polynomial

open scoped Nat Real

namespace DLMF.BernoulliEuler

/-! ### §24.12(ii) Euler polynomials: real zeros -/

/-- DLMF §24.12(ii): for even `n ≥ 2`, `y_1^{(n)} = 1`. -/
@[dlmf 24.12.ii]
theorem eulerRealZero_one_of_even {n : ℕ} (he : Even n) (h2 : 2 ≤ n) :
    eulerRealZero n 1 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 2 := ⟨n / 2 - 1, by obtain ⟨k, hk⟩ := he; omega⟩
  refine b24b_getD_zero_eq (eulerRealZerosGE_sorted _) ?_ fun y hy => ?_
  · refine mem_eulerRealZerosGE.mpr ⟨by norm_num, ?_⟩
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, q24b_eulerFun_one,
      show 2 * m + 1 + 1 = 2 * m + 2 by ring, q24b_eulerFun_two_mul_add_two_zero, neg_zero]
  · obtain ⟨hy1, hy0⟩ := mem_eulerRealZerosGE.mp hy
    by_contra hlt
    push Not at hlt
    exact (q24b_euler_ne_zero m).2 y ⟨by linarith, hlt⟩ hy0

/-- DLMF 24.12.8: for fixed `m ≥ 1`, `y_m^{(n)} → m` as `n → ∞` through even values. -/
@[dlmf 24.12.E8]
theorem tendsto_eulerRealZero_even {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => eulerRealZero (2 * k) m) atTop (𝓝 m) :=
  r24b_euler_even_zero hm

/-- DLMF §24.12(ii): for odd `n`, `y_1^{(n)} = 1/2`. -/
@[dlmf 24.12.ii]
theorem eulerRealZero_one_of_odd {n : ℕ} (hn : Odd n) : eulerRealZero n 1 = 1 / 2 := by
  refine b24b_getD_zero_eq (eulerRealZerosGE_sorted _) ?_ fun y hy => ?_
  · refine mem_eulerRealZerosGE.mpr ⟨le_rfl, ?_⟩
    have h := eulerNumber_eq_zero_of_odd hn
    rw [eulerNumber, mul_eq_zero] at h
    have h' : (euler n).eval (1 / 2 : ℚ) = 0 := h.resolve_left (pow_ne_zero _ two_ne_zero)
    have : (1 / 2 : ℝ) = algebraMap ℚ ℝ (1 / 2) := by simp
    rw [eulerFun, this, eval_map, eval₂_at_apply, h', map_zero]
  · exact (mem_eulerRealZerosGE.mp hy).1

/-! ### Helpers for 24.12.9 and 24.12.10: the second zero of `E₂ₘ₋₁`

From the Fourier series 24.8.5 and `|sin((2k+1)θ)| ≤ (2k+1) sin θ`,
`(-1)^m E₂ₘ₋₁(t) ≥ 4(2m-1)!/π^{2m} (1 - π²/24)(1 - 2t)` on `[0, 1/2]`; with
`E(1 + t) = 2tⁿ - E(t)` and `E(1 - x) = -E(x)` this locates the zero next to `3/2`. -/

/-- `E₅(x) = (x - 1/2)(x² - x - 1)²` (proof of `euler_five`). -/
lemma s24b_euler_five_eq :
    Polynomial.euler 5 = (X - C (1 / 2)) * (X ^ 2 - X - 1) ^ 2 := by
  apply eq_of_comp_X_add_one_add_self_eq
  rw [euler_comp_X_add_one_add]
  simp only [mul_comp, sub_comp, pow_comp, X_comp, C_comp, one_comp]
  have h : C (1 / 2 : ℚ) * 2 = 1 := by rw [← C_ofNat, ← C_mul]; norm_num
  linear_combination (-(X ^ 2 - X - 1) ^ 2 - ((X + 1) ^ 2 - (X + 1) - 1) ^ 2 +
    3 * (X ^ 4 - X ^ 2 + 1)) * h

/-- `|sin (m θ)| ≤ m |sin θ|`. -/
lemma s24b_abs_sin_nat_mul_le (m : ℕ) (θ : ℝ) :
    |Real.sin (m * θ)| ≤ m * |Real.sin θ| := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [add_mul, one_mul, Real.sin_add]
    calc |Real.sin (m * θ) * Real.cos θ + Real.cos (m * θ) * Real.sin θ|
        ≤ |Real.sin (m * θ)| * |Real.cos θ| + |Real.cos (m * θ)| * |Real.sin θ| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |Real.sin (m * θ)| * 1 + 1 * |Real.sin θ| := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ ≤ (m + 1) * |Real.sin θ| := by nlinarith

/-- `cos((2k+1)πt) ≥ -(2k+1) cos(πt)`. -/
lemma s24b_cos_odd_ge (k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    -((2 * k + 1) * Real.cos (π * t)) ≤ Real.cos ((2 * k + 1) * π * t) := by
  set θ := π / 2 - π * t
  have hθ0 : 0 ≤ θ := by simp only [θ]; nlinarith [Real.pi_pos]
  have hθ1 : θ ≤ π := by simp only [θ]; nlinarith [Real.pi_pos]
  have e1 : Real.cos (π * t) = Real.sin θ := by
    simp only [θ]; rw [Real.sin_pi_div_two_sub]
  have e2 : Real.cos ((2 * k + 1) * π * t) = (-1) ^ k * Real.sin (((2 * k + 1 : ℕ) : ℝ) * θ) := by
    rw [show (2 * k + 1) * π * t = (π / 2 - ((2 * k + 1 : ℕ) : ℝ) * θ) + k * π by
      simp only [θ]; push_cast; ring, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two_sub]
  have hs := s24b_abs_sin_nat_mul_le (2 * k + 1) θ
  rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθ1)] at hs
  rw [e1, e2]
  have h1 : |(-1 : ℝ) ^ k * Real.sin (((2 * k + 1 : ℕ) : ℝ) * θ)| ≤
      ((2 * k + 1 : ℕ) : ℝ) * Real.sin θ := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hs
  push_cast at h1 ⊢
  linarith [neg_abs_le ((-1 : ℝ) ^ k * Real.sin ((2 * (k : ℝ) + 1) * θ))]

/-- Lower bound for `(-1)ⁿ E₂ₙ₋₁(t)` on `[0, 1/2]`, `n ≥ 2`. -/
lemma s24b_euler_lower {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    4 * (2 * n - 1)! / π ^ (2 * n) * (1 - π ^ 2 / 24) * (1 - 2 * t) ≤
      (-1) ^ n * eulerFun (2 * n - 1) t := by
  set K : ℝ := 4 * (2 * n - 1)! / π ^ (2 * n)
  have hK : 0 < K := by positivity
  have hπ := Real.pi_pos
  have hE := (hasSum_cos_odd_eulerFun (n := n) (by omega) ht0 (by linarith)).mul_left ((-1) ^ n)
  have h1 : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hE' : HasSum (fun k : ℕ => K * (Real.cos ((2 * k + 1) * π * t) / (2 * k + 1) ^ (2 * n)))
      ((-1) ^ n * eulerFun (2 * n - 1) t) := by
    refine hE.congr_fun fun k => ?_
    rw [← mul_assoc, ← mul_assoc, h1, one_mul]
  have hc : 0 ≤ Real.cos (π * t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  have hz := ((hasSum_zeta_two.mul_left (-(1 / 4 : ℝ))).add (hasSum_ite_eq 0 (1 : ℝ))).mul_left
    (K * Real.cos (π * t))
  have hle := hasSum_le (fun k => ?_) hz hE'
  · have hcos := Real.one_sub_mul_le_cos (x := π * t) (by positivity) (by nlinarith)
    have e : 2 / π * (π * t) = 2 * t := by field_simp
    rw [e] at hcos
    have hp : (0 : ℝ) ≤ 1 - π ^ 2 / 24 := by nlinarith [Real.pi_lt_d2]
    calc K * (1 - π ^ 2 / 24) * (1 - 2 * t) ≤ K * (1 - π ^ 2 / 24) * Real.cos (π * t) := by
          gcongr
      _ = K * Real.cos (π * t) * (-(1 / 4) * (π ^ 2 / 6) + 1) := by ring
      _ ≤ _ := hle
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp only [ite_eq_right_iff.mpr (fun h => absurd h hk.ne'), add_zero]
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hco := s24b_cos_odd_ge k ht0 ht1
      have hpow : 4 * (k : ℝ) ^ 2 ≤ (2 * (k : ℝ) + 1) ^ (2 * n - 1) := by
        calc 4 * (k : ℝ) ^ 2 ≤ (2 * (k : ℝ) + 1) ^ 2 := by nlinarith
          _ ≤ (2 * (k : ℝ) + 1) ^ (2 * n - 1) := pow_le_pow_right₀ (by linarith) (by omega)
      have hq : (2 * (k : ℝ) + 1) ^ (2 * n) = (2 * k + 1) * (2 * k + 1) ^ (2 * n - 1) := by
        rw [← pow_succ', show 2 * n - 1 + 1 = 2 * n by omega]
      have hpos : (0 : ℝ) < (2 * k + 1) ^ (2 * n - 1) := by positivity
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hK.le
      rw [hq, le_div_iff₀ (by positivity)]
      calc Real.cos (π * t) * (-(1 / 4) * (1 / (k : ℝ) ^ 2)) *
            ((2 * k + 1) * (2 * k + 1) ^ (2 * n - 1)) =
            -((2 * k + 1) * Real.cos (π * t)) * ((2 * k + 1) ^ (2 * n - 1) / (4 * k ^ 2)) := by
            field_simp
        _ ≤ -((2 * k + 1) * Real.cos (π * t)) * 1 := by
            refine mul_le_mul_of_nonpos_left ?_ (by nlinarith)
            exact (one_le_div (by positivity)).mpr hpow
        _ ≤ _ := by linarith

/-- Bracketing the second entry of a sorted list whose least entry `a` is simple. -/
lemma s24b_second_bracket {l : List ℝ} {a lo hi z : ℝ} (hs : l.Pairwise (· ≤ ·)) (ha : a ∈ l)
    (hc : l.count a ≤ 1) (hge : ∀ y ∈ l, a ≤ y) (hgt : ∀ y ∈ l, y ≠ a → lo < y) (hz : z ∈ l)
    (hza : z ≠ a) (hzh : z < hi) : lo < l.getD (2 - 1) 0 ∧ l.getD (2 - 1) 0 < hi := by
  match l, hs, ha, hc, hge, hgt, hz with
  | [], _, ha, _, _, _, _ => simp at ha
  | [c], _, ha, _, _, _, hz =>
    simp only [List.mem_singleton] at ha hz; exact absurd (hz.trans ha.symm) hza
  | c :: d :: t, hs, ha, hc, hge, hgt, hz =>
    simp only [show 2 - 1 = 1 from rfl, List.getD_cons_succ, List.getD_cons_zero]
    have hca : c = a := by
      rcases List.mem_cons.mp ha with h | h
      · exact h.symm
      · exact le_antisymm ((List.pairwise_cons.mp hs).1 a h) (hge c List.mem_cons_self)
    subst hca
    have hdc : d ≠ c := by
      intro hdc; subst hdc
      simp at hc
    refine ⟨hgt d (by simp) hdc, lt_of_le_of_lt ?_ hzh⟩
    have hzt : z ∈ d :: t := by
      rcases List.mem_cons.mp hz with h | h
      · exact absurd h hza
      · exact h
    rcases List.mem_cons.mp hzt with h | h
    · exact h ▸ le_rfl
    · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 z h

/-- `1/2` is a simple zero of `E₂ₙ₋₁`, `n ≥ 2`. -/
lemma s24b_euler_count_half {n : ℕ} (hn : 2 ≤ n) :
    (eulerRealZerosGE (2 * n - 1)).count (1 / 2) ≤ 1 := by
  set P := (Polynomial.euler (2 * n - 1)).map (algebraMap ℚ ℝ) with hP
  have hP0 : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (b24b_euler_ne_zero _)
  have hd : (derivative P).eval (1 / 2) ≠ 0 := by
    have : (derivative P).eval (1 / 2) =
        ((2 * n - 1 : ℕ) : ℝ) * eulerFun (2 * (n - 2) + 2) (1 / 2) := by
      rw [show 2 * (n - 2) + 2 = 2 * n - 1 - 1 by omega]
      simp [P, Polynomial.derivative_map, derivative_euler, eulerFun]
    rw [this]
    refine mul_ne_zero (by norm_cast; omega) ((q24b_euler_ne_zero (n - 2)).2 _ ⟨by norm_num,
      by norm_num⟩)
  have hmult : P.rootMultiplicity (1 / 2) ≤ 1 := by
    by_contra h; push Not at h
    exact hd ((one_lt_rootMultiplicity_iff_isRoot hP0).mp h).2
  rw [eulerRealZerosGE, b24b_zerosGE, ← Multiset.coe_count, Multiset.sort_eq,
    Multiset.count_filter_of_pos (by norm_num), count_roots]
  exact hmult

/-- `η (-1)^m E₂ₘ₋₁(t) ≥ 0.77 (1 - 2t)` on `[0, 1/2]`, `η = π^{2m}/(3 (2m-1)!)`, `m ≥ 2`. -/
lemma s24b_euler_key {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    77 / 100 * (1 - 2 * t) ≤
      π ^ (2 * m) / (3 * (2 * m - 1)!) * ((-1) ^ m * eulerFun (2 * m - 1) t) := by
  have h := s24b_euler_lower hm ht0 ht1
  have hπ := Real.pi_pos
  have hη : 0 < π ^ (2 * m) / (3 * (2 * m - 1)!) := by positivity
  have hKη : π ^ (2 * m) / (3 * (2 * m - 1)!) * (4 * (2 * m - 1)! / π ^ (2 * m)) = 4 / 3 := by
    have : ((2 * m - 1)! : ℝ) ≠ 0 := by positivity
    field_simp
  have hp : π ^ 2 / 24 ≤ 4225 / 10000 := by nlinarith [Real.pi_lt_d2]
  have h2t : 0 ≤ 1 - 2 * t := by linarith
  calc 77 / 100 * (1 - 2 * t) ≤ 4 / 3 * (1 - π ^ 2 / 24) * (1 - 2 * t) := by
        gcongr; linarith
    _ = π ^ (2 * m) / (3 * (2 * m - 1)!) *
        (4 * (2 * m - 1)! / π ^ (2 * m) * (1 - π ^ 2 / 24) * (1 - 2 * t)) := by
        rw [← hKη]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hη.le

/-- `π^{N+1}/N! ≤ 3/4` for `N ≥ 9`. -/
lemma s24b_pi_pow_div_le {N : ℕ} (hN : 9 ≤ N) : π ^ (N + 1) / N ! ≤ 3 / 4 := by
  induction N, hN using Nat.le_induction with
  | base =>
    have hp := Real.pi_lt_d2
    have hp0 := Real.pi_pos
    have : π ^ 10 < 3.15 ^ 10 := by gcongr
    rw [div_le_iff₀ (by positivity)]
    norm_num [Nat.factorial] at this ⊢
    linarith
  | succ N hN ih =>
    have hp := Real.pi_lt_d2
    have hp0 := Real.pi_pos
    rw [Nat.factorial_succ, pow_succ, Nat.cast_mul]
    have hN' : (π : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      have : (10 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 ≤ N + 1)
      linarith
    calc π ^ (N + 1) * π / (((N + 1 : ℕ) : ℝ) * N !) =
        π ^ (N + 1) / N ! * (π / ((N + 1 : ℕ) : ℝ)) := by
          field_simp
      _ ≤ 3 / 4 * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; exact hN'
      _ = 3 / 4 := by ring

/-- Common facts on `E₂ₘ₋₁` for the zero bounds. -/
lemma s24b_euler_facts {m : ℕ} (hm : 2 ≤ m) :
    (∀ x, eulerFun (2 * m - 1) (1 - x) = -eulerFun (2 * m - 1) x) ∧
    (∀ t, eulerFun (2 * m - 1) (1 + t) = 2 * t ^ (2 * m - 1) - eulerFun (2 * m - 1) t) ∧
    eulerFun (2 * m - 1) (1 / 2) = 0 ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → t ^ (2 * m - 1) ≤ t ^ 3) := by
  have hodd : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
  refine ⟨fun x => ?_, fun t => ?_, ?_, fun t h0 h1 => ?_⟩
  · rw [eulerFun_one_sub, hodd.neg_one_pow, neg_one_mul]
  · have := eulerFun_add_one_add (2 * m - 1) t
    rw [add_comm t 1] at this; linarith
  · have := q24b_eulerFun_odd_half (m - 1)
    rwa [show 2 * (m - 1) + 1 = 2 * m - 1 by omega] at this
  · exact pow_le_pow_of_le_one h0 h1 (by omega)

/-- 24.12.10 for `n = 5`, where `y₂ = y₃ = (1 + √5)/2` is a double zero. -/
lemma s24b_euler_five_bounds :
    3 / 2 < eulerRealZero 5 2 ∧ eulerRealZero 5 2 < 3 / 2 + π ^ (5 + 1) / (3 * 5 !) := by
  have h5 : ∀ x, eulerFun 5 x = (x - 1 / 2) * (x ^ 2 - x - 1) ^ 2 := by
    intro x; simp [eulerFun, s24b_euler_five_eq]
  set gr : ℝ := (1 + Real.sqrt 5) / 2 with hgd
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 5 < 2.24 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hg2 : gr ^ 2 - gr - 1 = 0 := by rw [hgd]; nlinarith
  have hπ := Real.pi_gt_three
  have hη : 2 < π ^ (5 + 1) / (3 * 5 !) := by
    have : (3 : ℝ) ^ 6 < π ^ 6 := by gcongr
    rw [lt_div_iff₀ (by positivity)]
    norm_num [Nat.factorial] at this ⊢; linarith
  refine s24b_second_bracket (eulerRealZerosGE_sorted _) (a := 1 / 2) (z := gr) ?_
    (s24b_euler_count_half (n := 3) (by norm_num)) (fun y hy => (mem_eulerRealZerosGE.mp hy).1)
    (fun y hy hne => ?_) ?_ ?_ ?_
  · exact mem_eulerRealZerosGE.mpr ⟨le_rfl, by rw [h5]; ring⟩
  · obtain ⟨hy1, hy0⟩ := mem_eulerRealZerosGE.mp hy
    rw [h5] at hy0
    rcases mul_eq_zero.mp hy0 with h | h
    · exact absurd (by linarith : y = 1 / 2) hne
    · have h' : y ^ 2 - y - 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      nlinarith
  · exact mem_eulerRealZerosGE.mpr ⟨by rw [hgd]; linarith, by rw [h5, hg2]; ring⟩
  · intro h; rw [hgd] at h; linarith
  · rw [hgd]; linarith

/-- DLMF 24.12.9: for `n = 3, 7, 11, …`, `3/2 - π^{n+1}/(3 n!) < y_2^{(n)} < 3/2`. -/
@[dlmf 24.12.E9]
theorem eulerRealZero_two_bounds_three {n : ℕ} (hn : n % 4 = 3) :
    3 / 2 - π ^ (n + 1) / (3 * n !) < eulerRealZero n 2 ∧ eulerRealZero n 2 < 3 / 2 := by
  obtain ⟨m, rfl, hm2, hme⟩ : ∃ m, n = 2 * m - 1 ∧ 2 ≤ m ∧ Even m :=
    ⟨(n + 1) / 2, by omega, by omega, ⟨(n + 1) / 4, by omega⟩⟩
  rw [show 2 * m - 1 + 1 = 2 * m by omega]
  set η := π ^ (2 * m) / (3 * (2 * m - 1)!) with hηd
  have hη : 0 < η := by positivity
  obtain ⟨hsym, hshift, hhalf, hpow3⟩ := s24b_euler_facts hm2
  set E := eulerFun (2 * m - 1) with hE
  have key : ∀ t, 0 ≤ t → t ≤ 1 / 2 → 77 / 100 * (1 - 2 * t) ≤ η * E t := by
    intro t h0 h1
    have := s24b_euler_key hm2 h0 h1
    rwa [hme.neg_one_pow, one_mul] at this
  have hp : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → 2 * t ^ (2 * m - 1) ≤ 1 / 4 := by
    intro t h0 h1
    have := hpow3 t h0 (by linarith)
    have : t ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ h0 h1 3
    norm_num at this; linarith
  have hF2 : ∀ x, 1 / 2 < x → x ≤ 1 → E x < 0 := by
    intro x h1 h2
    have := key (1 - x) (by linarith) (by linarith)
    rw [hsym] at this
    nlinarith
  have hF3 : ∀ t, 0 ≤ t → t ≤ 1 / 2 - η → E (1 + t) < 0 := by
    intro t h0 h1
    have hk := key t h0 (by linarith)
    rw [hshift]
    have hpt := hp t h0 (by linarith)
    have h3 : 77 / 100 * (2 * η) ≤ η * E t := le_trans (by nlinarith) hk
    have h4 : 154 / 100 ≤ E t := by nlinarith
    linarith
  have h32 : 0 < E (3 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, hshift, hhalf, sub_zero]; positivity
  obtain ⟨a0, ha1, ha2, ha3, ha0⟩ : ∃ a0 : ℝ, 1 ≤ a0 ∧ 3 / 2 - η ≤ a0 ∧ a0 < 3 / 2 ∧ E a0 < 0 := by
    by_cases hη2 : η < 1 / 2
    · refine ⟨3 / 2 - η, by linarith, le_rfl, by linarith, ?_⟩
      have := hF3 (1 / 2 - η) (by linarith) le_rfl
      rwa [show 1 + (1 / 2 - η) = 3 / 2 - η by ring] at this
    · push Not at hη2
      refine ⟨1, le_rfl, by linarith, by norm_num, ?_⟩
      have hk := key 0 le_rfl (by norm_num)
      have : 0 < E 0 := by nlinarith
      have h1 := hshift 0
      rw [add_zero, zero_pow (by omega), mul_zero, zero_sub] at h1
      linarith
  obtain ⟨z, hz, hz0⟩ := q24b_exists_root (continuous_eulerFun _) ha3
    (mul_neg_of_neg_of_pos ha0 h32)
  refine s24b_second_bracket (eulerRealZerosGE_sorted _) (a := 1 / 2) (z := z)
    (mem_eulerRealZerosGE.mpr ⟨le_rfl, hhalf⟩) (s24b_euler_count_half hm2)
    (fun y hy => (mem_eulerRealZerosGE.mp hy).1) (fun y hy hne => ?_)
    (mem_eulerRealZerosGE.mpr ⟨by linarith [hz.1], hz0⟩) (by linarith [hz.1]) hz.2
  obtain ⟨hy1, hy0⟩ := mem_eulerRealZerosGE.mp hy
  by_contra hle
  push Not at hle
  rcases le_or_gt y 1 with h | h
  · exact absurd hy0 (hF2 y (lt_of_le_of_ne hy1 (Ne.symm hne)) h).ne
  · have := hF3 (y - 1) (by linarith) (by linarith)
    rw [show 1 + (y - 1) = y by ring] at this
    exact absurd hy0 this.ne

/-- DLMF 24.12.10: for `n = 5, 9, 13, …`, `3/2 < y_2^{(n)} < 3/2 + π^{n+1}/(3 n!)`. -/
@[dlmf 24.12.E10]
theorem eulerRealZero_two_bounds_one {n : ℕ} (hn : n % 4 = 1) (h5 : 5 ≤ n) :
    3 / 2 < eulerRealZero n 2 ∧ eulerRealZero n 2 < 3 / 2 + π ^ (n + 1) / (3 * n !) := by
  rcases (show n = 5 ∨ 9 ≤ n by omega) with rfl | h9
  · exact s24b_euler_five_bounds
  obtain ⟨m, rfl, hm5, hmo⟩ : ∃ m, n = 2 * m - 1 ∧ 5 ≤ m ∧ Odd m :=
    ⟨(n + 1) / 2, by omega, by omega, ⟨(n - 1) / 4, by omega⟩⟩
  have hm2 : 2 ≤ m := by omega
  have hη4 : π ^ (2 * m - 1 + 1) / (3 * (2 * m - 1)!) ≤ 1 / 4 := by
    have := s24b_pi_pow_div_le h9
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  rw [show 2 * m - 1 + 1 = 2 * m by omega] at hη4 ⊢
  set η := π ^ (2 * m) / (3 * (2 * m - 1)!) with hηd
  have hη : 0 < η := by positivity
  obtain ⟨hsym, hshift, hhalf, hpow3⟩ := s24b_euler_facts hm2
  set E := eulerFun (2 * m - 1) with hE
  have key : ∀ t, 0 ≤ t → t ≤ 1 / 2 → 77 / 100 * (1 - 2 * t) ≤ η * -E t := by
    intro t h0 h1
    have := s24b_euler_key hm2 h0 h1
    rwa [hmo.neg_one_pow, neg_one_mul] at this
  have hF2 : ∀ x, 1 / 2 < x → x ≤ 1 → 0 < E x := by
    intro x h1 h2
    have := key (1 - x) (by linarith) (by linarith)
    rw [hsym, neg_neg] at this
    nlinarith
  have hF3 : ∀ t, 0 < t → t ≤ 1 / 2 → 0 < E (1 + t) := by
    intro t h0 h1
    have hk := key t h0.le h1
    have : 0 ≤ -E t := by nlinarith
    rw [hshift]
    have : 0 < t ^ (2 * m - 1) := by positivity
    linarith
  have h32 : 0 < E (3 / 2) := by
    have := hF3 (1 / 2) (by norm_num) le_rfl
    rwa [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at this
  have hneg : E (3 / 2 + η) < 0 := by
    rw [show 3 / 2 + η = 1 + (1 / 2 + η) by ring, hshift]
    have hk := key (1 / 2 - η) (by linarith) (by linarith)
    have hs := hsym (1 / 2 + η)
    rw [show 1 - (1 / 2 + η) = 1 / 2 - η by ring] at hs
    rw [hs, neg_neg] at hk
    have h1 : 154 / 100 ≤ E (1 / 2 + η) := by nlinarith
    have h2 : (1 / 2 + η) ^ (2 * m - 1) ≤ (3 / 4) ^ 9 := by
      calc (1 / 2 + η) ^ (2 * m - 1) ≤ (3 / 4) ^ (2 * m - 1) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
        _ ≤ (3 / 4) ^ 9 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at h2
    linarith
  obtain ⟨z, hz, hz0⟩ := q24b_exists_root (continuous_eulerFun _)
    (show (3 / 2 : ℝ) < 3 / 2 + η by linarith) (mul_neg_of_pos_of_neg h32 hneg)
  refine s24b_second_bracket (eulerRealZerosGE_sorted _) (a := 1 / 2) (z := z)
    (mem_eulerRealZerosGE.mpr ⟨le_rfl, hhalf⟩) (s24b_euler_count_half hm2)
    (fun y hy => (mem_eulerRealZerosGE.mp hy).1) (fun y hy hne => ?_)
    (mem_eulerRealZerosGE.mpr ⟨by linarith [hz.1], hz0⟩) (by linarith [hz.1]) hz.2
  obtain ⟨hy1, hy0⟩ := mem_eulerRealZerosGE.mp hy
  by_contra hle
  push Not at hle
  rcases le_or_gt y 1 with h | h
  · exact absurd hy0 (hF2 y (lt_of_le_of_ne hy1 (Ne.symm hne)) h).ne'
  · have := hF3 (y - 1) (by linarith) (by linarith)
    rw [show 1 + (y - 1) = y by ring] at this
    exact absurd hy0 this.ne'

/-- DLMF 24.12.11 as printed, `y_{2m}^{(n)} → m - 1/2` through odd `n`, is false: already for
`m = 1` the zero `y_2^{(n)}` tends to `3/2` (it lies within `π^{n+1}/(3 n!)` of `3/2` by
24.12.9–24.12.10). -/
lemma r24b_tendsto_eulerRealZero_odd_counterexample :
    ¬ Tendsto (fun k : ℕ => eulerRealZero (2 * k + 1) (2 * 1)) atTop (𝓝 ((1 : ℕ) - 1 / 2 : ℝ)) := by
  intro h
  have h2 := r24b_euler_odd_zero (j := 2 * 1) (by norm_num)
  have := tendsto_nhds_unique h h2
  norm_num at this

/-- DLMF 24.12.11, corrected: for fixed `m ≥ 1`, `y_m^{(n)} → m - 1/2` as `n → ∞` through odd
values.

Corrected statement (2026-10-25): DLMF prints `y_{2m}^{(n)} → m - 1/2`, which is false for every
`m ≥ 1` (see `r24b_tendsto_eulerRealZero_odd_counterexample`); the zeros of `Eₙ` in `[1/2, ∞)`
for odd `n` tend to `1/2, 3/2, 5/2, …`, the zeros of `cos πx`. -/
@[dlmf 24.12.E11]
theorem tendsto_eulerRealZero_odd {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => eulerRealZero (2 * k + 1) m) atTop (𝓝 (m - 1 / 2)) :=
  r24b_euler_odd_zero hm

/-! ### §24.12(iv) Multiple zeros -/

/-- DLMF §24.12(iv): `Bₙ(x)` has no multiple zeros (Brillhart 1969). Stated for all `n ≥ 0`
(stronger than DLMF's `n = 1, 2, …`; `B₀ = 1`). -/
@[dlmf 24.12.iv]
theorem bernoulli_separable (n : ℕ) : (Polynomial.bernoulli n).Separable := by
  sorry

/-- DLMF §24.12(iv): `E₅(x) = (x - 1/2)(x² - x - 1)²`. -/
@[dlmf 24.12.iv]
theorem euler_five : Polynomial.euler 5 = (X - C (1 / 2)) * (X ^ 2 - X - 1) ^ 2 :=
  s24b_euler_five_eq

/-- DLMF §24.12(iv): the only Euler polynomial with multiple zeros is `E₅(x)`. -/
@[dlmf 24.12.iv]
theorem euler_separable_iff (n : ℕ) : (Polynomial.euler n).Separable ↔ n ≠ 5 := by
  sorry

end DLMF.BernoulliEuler

end
