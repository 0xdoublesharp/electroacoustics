module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace Electroacoustics.Transcendentals

open Complex Finset

theorem pi_bracket : (3.1415926535897932 : ℝ) < Real.pi ∧ Real.pi < 3.1415926535897933 := by
  exact ⟨(by norm_num : (3.1415926535897932 : ℝ) < 3.14159265358979323846).trans Real.pi_gt_d20,
    Real.pi_lt_d20.trans (by norm_num)⟩

theorem log_ten_bracket :
    (2.3025850925 : ℝ) < Real.log 10 ∧ Real.log 10 < 2.3025850935 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  exact ⟨(by norm_num : (2.3025850925 : ℝ) < 0.6931471803 + 1.6094379123).trans
      (add_lt_add Real.log_two_gt_d9 Real.log_five_gt_d9),
    (add_lt_add Real.log_two_lt_d9 Real.log_five_lt_d9).trans (by norm_num)⟩

/-- The first nineteen terms of the exponential series on [-1, 1]. -/
theorem exp_remainder {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - ∑ n ∈ range 19, x ^ n / n.factorial| ≤ (1 : ℝ) / 2 ^ 55 := by
  have est := Real.exp_bound (n := 19) hx (by decide)
  have powLe : |x| ^ 19 ≤ (1 : ℝ) := pow_le_one₀ (abs_nonneg _) hx
  apply est.trans
  calc
    _ ≤ (1 : ℝ) * (20 / (((19 : ℕ).factorial : ℝ) * 19)) := by
      exact mul_le_mul_of_nonneg_right powLe (by positivity)
    _ ≤ _ := by norm_num [Nat.factorial]

/-- The first twenty-four complex exponential terms simultaneously enclose
    cosine and sine on the first-quadrant range used by the DSP solver. -/
theorem trig_remainder {x : ℝ} (hx : |x| ≤ 8 / 5) :
    let poly : ℂ := ∑ n ∈ range 24, ((x : ℂ) * I) ^ n / n.factorial
    |Real.cos x - poly.re| ≤ (1 : ℝ) / 2 ^ 55 ∧
      |Real.sin x - poly.im| ≤ (1 : ℝ) / 2 ^ 55 := by
  dsimp
  let z := (x : ℂ) * I
  have normZ : ‖z‖ = |x| := by simp [z]
  have est := Complex.exp_bound' (x := z) (n := 24) (by rw [normZ]; linarith)
  have normPow : ‖z‖ ^ 24 ≤ (8 / 5 : ℝ) ^ 24 :=
    pow_le_pow_left₀ (norm_nonneg _) (normZ ▸ hx) _
  let err : ℂ := Complex.exp z - ∑ n ∈ range 24, z ^ n / n.factorial
  have close : ‖err‖ ≤ (1 : ℝ) / 2 ^ 55 :=
    est.trans <| (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right normPow (by positivity : (0 : ℝ) ≤ ((24 : ℕ).factorial : ℝ)))
      (by norm_num : (0 : ℝ) ≤ 2)).trans (by norm_num [Nat.factorial])
  exact ⟨by simpa [err, z, Complex.sub_re, Complex.exp_ofReal_mul_I_re] using
    (Complex.abs_re_le_norm err).trans close,
    by simpa [err, z, Complex.sub_im, Complex.exp_ofReal_mul_I_im] using
    (Complex.abs_im_le_norm err).trans close⟩

/-- The residual scales with the argument. The factor of `‖z‖` also bounds
    the normalized sine and hyperbolic-sine remainders after division. -/
theorem duct_wave_remainder {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - ∑ n ∈ range 24, z ^ n / n.factorial‖ ≤
      ((1 : ℝ) / 2 ^ 70) * ‖z‖ := by
  have estimate := Complex.exp_bound' (x := z) (n := 24) (by linarith)
  have powBound : ‖z‖ ^ 23 ≤ (1 : ℝ) := pow_le_one₀ (norm_nonneg _) hz
  calc
    _ ≤ ‖z‖ ^ 24 / ((24 : ℕ).factorial : ℝ) * 2 := estimate
    _ = (‖z‖ ^ 23 / ((24 : ℕ).factorial : ℝ) * 2) * ‖z‖ := by
      rw [pow_succ]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right powBound (by positivity : (0 : ℝ) ≤ (24 : ℕ).factorial))
        (by norm_num : (0 : ℝ) ≤ 2)).trans (by norm_num [Nat.factorial])

theorem duct_log_remainder {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log ((1 + x) / (1 - x)) -
      2 * ∑ n ∈ range 40, x ^ (2 * n + 1) / (2 * n + 1)| ≤ (1 : ℝ) / 2 ^ 79 := by
  have small : |x| < 1 := hx.trans_lt (by norm_num)
  have squareBound : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hx)
  have denominator : (3 / 4 : ℝ) ≤ 1 - x ^ 2 := by nlinarith
  calc
    _ = 2 * |1 / 2 * Real.log ((1 + x) / (1 - x)) -
        ∑ n ∈ range 40, x ^ (2 * n + 1) / (2 * n + 1)| := by
      calc
        _ = |2 * (1 / 2 * Real.log ((1 + x) / (1 - x)) -
            ∑ n ∈ range 40, x ^ (2 * n + 1) / (2 * n + 1))| := by
          congr 1
          ring
        _ = _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (|x| ^ 81 / (1 - x ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (Real.sum_range_sub_log_div_le small 40) (by norm_num)
    _ ≤ 2 * ((1 / 2 : ℝ) ^ 81 / (3 / 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply div_le_div₀ (by positivity)
        (pow_le_pow_left₀ (abs_nonneg _) hx _) (by norm_num) denominator
    _ ≤ _ := by norm_num

theorem log_two_bracket : (0.6931471803 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

theorem exp_halving_squaring (x : ℝ) (k : ℕ) :
    Real.exp x = Real.exp (x / (2 : ℝ) ^ k) ^ ((2 : ℕ) ^ k) := by
  rw [← Real.exp_nat_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel₀ _ (by positivity)]

theorem log_range_reduction {y : ℝ} (hy : 0 < y) (e : ℤ) :
    let r := y / (2 : ℝ) ^ e
    let t := (r - 1) / (r + 1)
    Real.log y = Real.log ((1 + t) / (1 - t)) + (e : ℝ) * Real.log 2 := by
  let r := y / (2 : ℝ) ^ e
  let t := (r - 1) / (r + 1)
  change Real.log y = Real.log ((1 + t) / (1 - t)) + (e : ℝ) * Real.log 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hden : 0 < r + 1 := by positivity
  have ht : t < 1 := (div_lt_one hden).mpr (by linarith)
  have recover : (1 + t) / (1 - t) = r := by
    apply (div_eq_iff (sub_pos.mpr ht).ne').mpr
    dsimp [t]
    field_simp
    ring
  rw [recover]
  dsimp [r]
  rw [Real.log_div hy.ne' (by positivity), Real.log_zpow, sub_add_cancel]

theorem firstQuadrant_sin_mono {lo x hi : ℝ}
    (hlo : 0 ≤ lo) (hl : lo ≤ x) (hh : x ≤ hi) (hhi : hi ≤ Real.pi / 2) :
    Real.sin lo ≤ Real.sin x ∧ Real.sin x ≤ Real.sin hi := by
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  exact ⟨Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hh.trans hhi) hl,
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hhi hh⟩

theorem firstQuadrant_cos_anti {lo x hi : ℝ}
    (hlo : 0 ≤ lo) (hl : lo ≤ x) (hh : x ≤ hi) (hhi : hi ≤ Real.pi / 2) :
    Real.cos hi ≤ Real.cos x ∧ Real.cos x ≤ Real.cos lo := by
  have hp : hi ≤ Real.pi := by linarith [Real.pi_pos]
  exact ⟨Real.cos_le_cos_of_nonneg_of_le_pi (hlo.trans hl) hp hh,
    Real.cos_le_cos_of_nonneg_of_le_pi hlo (hh.trans hp) hl⟩

/-- Clamp input endpoints and output enclosures as in `firstQuadrant`.
    The upper sine endpoint is 1 whenever the angle might reach its maximum. -/
theorem firstQuadrant_clamp_sound {lo hi x piLo piHi sinLo sinHi cosLo cosHi : ℝ}
    (hx : lo ≤ x ∧ x ≤ hi) (quadrant : 0 ≤ x ∧ x ≤ Real.pi / 2)
    (piBracket : piLo ≤ Real.pi ∧ Real.pi ≤ piHi) (piHiBound : piHi / 2 ≤ Real.pi)
    (sinLeft : sinLo ≤ Real.sin (max 0 lo))
    (sinRight : Real.sin (min (piHi / 2) hi) ≤ sinHi)
    (cosRight : cosLo ≤ Real.cos (min (piHi / 2) hi))
    (cosLeft : Real.cos (max 0 lo) ≤ cosHi) :
    max 0 sinLo ≤ Real.sin x ∧
      Real.sin x ≤ (if piLo / 2 ≤ min (piHi / 2) hi then 1 else min 1 sinHi) ∧
      max 0 cosLo ≤ Real.cos x ∧ Real.cos x ≤ min 1 cosHi := by
  have left : max 0 lo ≤ x := max_le quadrant.1 hx.1
  have right : x ≤ min (piHi / 2) hi := le_min (by linarith [quadrant.2, piBracket.2]) hx.2
  have nonnegativeSin := Real.sin_nonneg_of_nonneg_of_le_pi quadrant.1
    (by linarith [quadrant.2, Real.pi_pos])
  have nonnegativeCos := Real.cos_nonneg_of_mem_Icc
    (show x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith [quadrant.1, Real.pi_pos], quadrant.2⟩)
  refine ⟨max_le nonnegativeSin (sinLeft.trans
    (Real.sin_le_sin_of_le_of_le_pi_div_two (by
      linarith [le_max_left 0 lo, Real.pi_pos]) quadrant.2 left)), ?_, ?_, ?_⟩
  · split <;> rename_i h
    · exact Real.sin_le_one _
    · have cap : min (piHi / 2) hi ≤ Real.pi / 2 := by
        linarith [le_of_not_ge h, piBracket.1]
      exact le_min (Real.sin_le_one _) ((Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [quadrant.1, Real.pi_pos]) cap right).trans sinRight)
  · exact max_le nonnegativeCos (cosRight.trans
      (Real.cos_le_cos_of_nonneg_of_le_pi quadrant.1 ((min_le_left _ _).trans piHiBound) right))
  · exact le_min (Real.cos_le_one _) ((Real.cos_le_cos_of_nonneg_of_le_pi
      (le_max_left _ _) (by linarith [quadrant.2, Real.pi_pos]) left).trans cosLeft)

/-- Webster cosine continued through the region with negative squared wavenumber. -/
def waveCos (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.cos (Real.sqrt t) else Real.cosh (Real.sqrt (-t))

/-- Webster normalized sine with its removable value at cutoff. -/
def waveSinc (t : ℝ) : ℝ :=
  if t = 0 then 1 else if 0 < t then Real.sin (Real.sqrt t) / Real.sqrt t
    else Real.sinh (Real.sqrt (-t)) / Real.sqrt (-t)

@[simp] theorem waveCos_zero : waveCos 0 = 1 := by simp [waveCos]
@[simp] theorem waveSinc_zero : waveSinc 0 = 1 := by simp [waveSinc]

theorem waveCos_sq_add_mul_waveSinc_sq (t : ℝ) :
    waveCos t ^ 2 + t * waveSinc t ^ 2 = 1 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hs : 0 < Real.sqrt (-t) := Real.sqrt_pos.mpr (neg_pos.mpr ht)
    have hsq : t = -(Real.sqrt (-t) ^ 2) := by
      rw [Real.sq_sqrt (neg_nonneg.mpr ht.le), neg_neg]
    simp only [waveCos, waveSinc, ht.ne, not_le.mpr ht, not_lt.mpr ht.le, ite_false]
    rw [div_pow]
    conv_lhs => enter [2, 1]; rw [hsq]
    rw [neg_mul, mul_div_cancel₀ _ (pow_ne_zero 2 hs.ne'), ← sub_eq_add_neg]
    exact Real.cosh_sq_sub_sinh_sq _
  · simp
  · have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    simp only [waveCos, waveSinc, ht.ne', ht.le, ht, ite_false, ite_true]
    rw [div_pow]
    conv_lhs => enter [2, 1]; rw [← Real.sq_sqrt ht.le]
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hs.ne'), add_comm]
    exact Real.sin_sq_add_cos_sq _

private theorem sqrt_four_mul (x : ℝ) : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

theorem wave_doubling (t : ℝ) :
    waveCos (4 * t) = 2 * waveCos t ^ 2 - 1 ∧
      waveSinc (4 * t) = waveSinc t * waveCos t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h4 : 4 * t < 0 := by linarith
    have hs : 0 < Real.sqrt (-t) := Real.sqrt_pos.mpr (neg_pos.mpr ht)
    simp only [waveCos, waveSinc, ht.ne, h4.ne, not_le.mpr ht, not_le.mpr h4,
      not_lt.mpr ht.le, not_lt.mpr h4.le, ite_false, ← mul_neg, sqrt_four_mul]
    rw [Real.cosh_two_mul, Real.sinh_two_mul]
    constructor
    · linarith [Real.cosh_sq_sub_sinh_sq (Real.sqrt (-t))]
    · field_simp
  · norm_num
  · have h4 : 0 < 4 * t := by positivity
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    simp only [waveCos, waveSinc, ht.ne', h4.ne', ht.le, h4.le, ht, h4, ite_true, ite_false,
      sqrt_four_mul, Real.cos_two_mul, Real.sin_two_mul, true_and]
    field_simp

private theorem exp_sum_even_odd (z : ℂ) (w : ℝ) (h : z ^ 2 = (w : ℂ)) (k : ℕ) :
    ∑ n ∈ range (2 * k), z ^ n / n.factorial =
      (↑(∑ n ∈ range k, w ^ n / (2 * n).factorial) : ℂ) +
        z * (↑(∑ n ∈ range k, w ^ n / (2 * n + 1).factorial) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ, pow_succ z (2 * k), pow_mul, h]
    push_cast
    ring

private theorem hyperbolic_taylor_bounds {z : ℂ} {w : ℝ} (hz : ‖z‖ ≤ 1)
    (hw : z ^ 2 = (w : ℂ)) :
    let c : ℝ := ∑ n ∈ range 12, w ^ n / (2 * n).factorial
    let s : ℝ := ∑ n ∈ range 12, w ^ n / (2 * n + 1).factorial
    ‖Complex.cosh z - (c : ℂ)‖ ≤ ((1 : ℝ) / 2 ^ 70) * ‖z‖ ∧
      ‖Complex.sinh z - z * (s : ℂ)‖ ≤ ((1 : ℝ) / 2 ^ 70) * ‖z‖ := by
  dsimp only
  let c : ℝ := ∑ n ∈ range 12, w ^ n / (2 * n).factorial
  let s : ℝ := ∑ n ∈ range 12, w ^ n / (2 * n + 1).factorial
  let ep := Complex.exp z - ((c : ℂ) + z * (s : ℂ))
  let en := Complex.exp (-z) - ((c : ℂ) + (-z) * (s : ℂ))
  let error := ((1 : ℝ) / 2 ^ 70) * ‖z‖
  have hp : ‖ep‖ ≤ error := by
    simpa only [ep, c, s, error, ← exp_sum_even_odd z w hw 12] using duct_wave_remainder hz
  have hn : ‖en‖ ≤ error := by
    have hw' : (-z) ^ 2 = (w : ℂ) := by rw [neg_sq, hw]
    simpa only [en, c, s, error, ← exp_sum_even_odd (-z) w hw' 12, norm_neg] using
      duct_wave_remainder (z := -z) (by simpa only [norm_neg] using hz)
  change ‖Complex.cosh z - (c : ℂ)‖ ≤ error ∧ ‖Complex.sinh z - z * (s : ℂ)‖ ≤ error
  rw [show Complex.cosh z - (c : ℂ) = (ep + en) / 2 by unfold Complex.cosh ep en; ring,
    show Complex.sinh z - z * (s : ℂ) = (ep - en) / 2 by unfold Complex.sinh ep en; ring]
  rw [norm_div, norm_div]
  norm_num
  exact ⟨by linarith [norm_add_le ep en], by linarith [norm_sub_le ep en]⟩

private theorem wave_taylor_bounds {t : ℝ} (ht : |t| ≤ 1) :
    let c : ℝ := ∑ n ∈ range 12, (-t) ^ n / (2 * n).factorial
    let s : ℝ := ∑ n ∈ range 12, (-t) ^ n / (2 * n + 1).factorial
    |waveCos t - c| ≤ (1 : ℝ) / 2 ^ 70 ∧ |waveSinc t - s| ≤ (1 : ℝ) / 2 ^ 70 := by
  dsimp only
  let c : ℝ := ∑ n ∈ range 12, (-t) ^ n / (2 * n).factorial
  let s : ℝ := ∑ n ∈ range 12, (-t) ^ n / (2 * n + 1).factorial
  let ε : ℝ := 1 / 2 ^ 70
  change |waveCos t - c| ≤ ε ∧ |waveSinc t - s| ≤ ε
  have finish (x C S : ℝ) (hx : 0 < x) (hx₁ : x ≤ 1)
      (hC : |C - c| ≤ ε * x) (hS : |S - x * s| ≤ ε * x) :
      |C - c| ≤ ε ∧ |S / x - s| ≤ ε := by
    refine ⟨hC.trans ?_, ?_⟩
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hx₁ (by positivity : 0 ≤ ε)
    · have difference : S / x - s = (S - x * s) / x := by
        rw [sub_div, mul_div_cancel_left₀ _ hx.ne']
      rw [difference, abs_div, abs_of_pos hx]
      exact (div_le_iff₀ hx).mpr hS
  rcases lt_trichotomy t 0 with h | h | h
  · let x := Real.sqrt (-t)
    have hx : 0 < x := Real.sqrt_pos.mpr (neg_pos.mpr h)
    have hx₁ : x ≤ 1 := Real.sqrt_le_iff.mpr ⟨zero_le_one, by
      simpa [abs_of_neg h] using ht⟩
    have hxSq : x ^ 2 = -t := Real.sq_sqrt (neg_nonneg.mpr h.le)
    have normX : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    obtain ⟨hc, hs⟩ := hyperbolic_taylor_bounds (w := -t) (normX ▸ hx₁)
      (by exact_mod_cast hxSq)
    rw [normX, ← Complex.ofReal_cosh] at hc
    rw [normX, ← Complex.ofReal_sinh, ← Complex.ofReal_mul] at hs
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hc hs
    simpa only [waveCos, waveSinc, h.ne, not_le.mpr h, not_lt.mpr h.le, ite_false] using
      finish x (Real.cosh x) (Real.sinh x) hx hx₁ hc hs
  · subst t
    norm_num [c, s, ε, sum_range_succ, Nat.factorial]
  · let x := Real.sqrt t
    let z := (x : ℂ) * I
    have hx : 0 < x := Real.sqrt_pos.mpr h
    have hx₁ : x ≤ 1 := Real.sqrt_le_iff.mpr ⟨zero_le_one, by
      simpa [abs_of_pos h] using ht⟩
    have hz : ‖z‖ = x := by simp [z, Real.norm_eq_abs, abs_of_pos hx]
    have hxSq : (x : ℂ) ^ 2 = (t : ℂ) := by exact_mod_cast Real.sq_sqrt h.le
    have hzSq : z ^ 2 = (-t : ℝ) := by
      rw [show z ^ 2 = (x : ℂ) ^ 2 * I ^ 2 by unfold z; ring, hxSq, I_sq]
      simp
    obtain ⟨hc, hs⟩ := hyperbolic_taylor_bounds (w := -t) (hz ▸ hx₁) hzSq
    rw [hz, show z = (x : ℂ) * I from rfl, Complex.cosh_mul_I, ← Complex.ofReal_cos] at hc
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hc
    rw [hz, show z = (x : ℂ) * I from rfl, Complex.sinh_mul_I, ← Complex.ofReal_sin] at hs
    have hs' : |Real.sin x - x * s| ≤ ε * x := by
      simpa only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, I_re, I_im, zero_mul, mul_zero, mul_one, add_zero, zero_add, sub_zero] using
        (Complex.abs_im_le_norm _).trans hs
    simpa only [waveCos, waveSinc, h.ne', h.le, h, ite_false, ite_true] using
      finish x (Real.cos x) (Real.sin x) hx hx₁ hc hs'

theorem waveCos_taylor_bound {t : ℝ} (ht : |t| ≤ 1) :
    |waveCos t - ∑ n ∈ range 12, (-t) ^ n / (2 * n).factorial| ≤ (1 : ℝ) / 2 ^ 70 :=
  (wave_taylor_bounds ht).1

theorem waveSinc_taylor_bound {t : ℝ} (ht : |t| ≤ 1) :
    |waveSinc t - ∑ n ∈ range 12, (-t) ^ n / (2 * n + 1).factorial| ≤ (1 : ℝ) / 2 ^ 70 :=
  (wave_taylor_bounds ht).2

theorem continuous_waveCos : Continuous waveCos := by
  change Continuous ((Set.Ici (0 : ℝ)).piecewise (Real.cos ∘ Real.sqrt)
    (Real.cosh ∘ Real.sqrt ∘ Neg.neg))
  apply (Real.continuous_cos.comp Real.continuous_sqrt).piecewise _
    (Real.continuous_cosh.comp (Real.continuous_sqrt.comp continuous_neg))
  intro x hx
  rw [frontier_Ici, Set.mem_singleton_iff] at hx
  subst x
  simp

theorem continuous_waveSinc : Continuous waveSinc := by
  have sinhAt := Real.hasDerivAt_sinh 0
  have cont : Continuous (dslope Real.sinh 0) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases h : x = 0
    · subst x
      exact continuousAt_dslope_same.mpr sinhAt.differentiableAt
    · exact (continuousAt_dslope_of_ne h).mpr Real.continuous_sinh.continuousAt
  have wave : waveSinc = (Set.Ici (0 : ℝ)).piecewise (Real.sinc ∘ Real.sqrt)
      (dslope Real.sinh 0 ∘ Real.sqrt ∘ Neg.neg) := by
    funext x
    rcases lt_trichotomy x 0 with h | rfl | h
    · have hs : Real.sqrt (-x) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr h)).ne'
      simp [waveSinc, h.ne, not_le.mpr h, not_lt.mpr h.le, Set.piecewise,
        dslope_of_ne _ hs, slope, div_eq_inv_mul]
    · simp [Set.piecewise]
    · have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr h).ne'
      simp [waveSinc, h.ne', h, h.le, Real.sinc_of_ne_zero hs, Set.piecewise]
  rw [wave]
  apply (Real.continuous_sinc.comp Real.continuous_sqrt).piecewise _
    (cont.comp (Real.continuous_sqrt.comp continuous_neg))
  intro x hx
  rw [frontier_Ici, Set.mem_singleton_iff] at hx
  subst x
  simp

end Electroacoustics.Transcendentals
