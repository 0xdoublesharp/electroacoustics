module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Filters

/-- The two strict inequalities enforced by `validateBiquad`. -/
def StableCoefficients (a1 a2 : ℝ) : Prop := |a2| < 1 ∧ |a1| < 1 + a2

private theorem real_pole_below_one (x a1 a2 : ℝ)
    (h2 : a2 < 1) (h1 : -(1 + a2) < a1) (root : x ^ 2 + a1 * x + a2 = 0) : x < 1 := by
  by_contra! outside
  have slope : 0 ≤ x + 1 + a1 := by linarith
  have term := mul_nonneg (sub_nonneg.mpr outside) slope
  nlinarith [term]

/-- Under the runtime coefficient predicate every root of `z² + a1*z + a2`
    lies strictly inside the unit circle. Use squared complex magnitude. -/
theorem accepted_poles_inside_unit_circle {a1 a2 : ℝ} {z : ℂ}
    (h : StableCoefficients a1 a2)
    (root : z ^ 2 + (a1 : ℂ) * z + (a2 : ℂ) = 0) : Complex.normSq z < 1 := by
  obtain ⟨_, ha2⟩ := abs_lt.mp h.1
  obtain ⟨ha1lo, ha1hi⟩ := abs_lt.mp h.2
  have hr := congrArg Complex.re root
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re] at hr
  rw [Complex.normSq_apply]
  by_cases hz : z.im = 0
  · have positiveRoot : z.re ^ 2 + a1 * z.re + a2 = 0 := by nlinarith [hr]
    have negativeRoot : (-z.re) ^ 2 + (-a1) * (-z.re) + a2 = 0 := by nlinarith [hr]
    have right := real_pole_below_one z.re a1 a2 ha2 ha1lo positiveRoot
    have left := real_pole_below_one (-z.re) (-a1) a2 ha2 (by linarith) negativeRoot
    have prod := mul_pos (show 0 < 1 - z.re by linarith) (show 0 < 1 + z.re by linarith)
    rw [hz]
    nlinarith [prod]
  · have hi := congrArg Complex.im root
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im] at hi
    have factored : (2 * z.re + a1) * z.im = 0 := by linarith
    have hx := (mul_eq_zero.mp factored).resolve_right hz
    have hxx := congrArg (fun r : ℝ => r * z.re) hx
    nlinarith [hr, hxx]

def centered (b0 b1 b2 x y : ℝ) : ℂ := ⟨b1 + (b0 + b2) * x, (b0 - b2) * y⟩

/-- The real/imaginary denominator used by `biquadTransfer` cannot vanish on the unit circle. -/
theorem centered_denominator_ne_zero {a1 a2 x y : ℝ}
    (h : StableCoefficients a1 a2) (unit : x ^ 2 + y ^ 2 = 1) :
    centered 1 a1 a2 x y ≠ 0 := by
  intro zero
  obtain ⟨_, ha2⟩ := abs_lt.mp h.1
  obtain ⟨ha1lo, ha1hi⟩ := abs_lt.mp h.2
  have hi : (1 - a2) * y = 0 := congrArg Complex.im zero
  have hy := (mul_eq_zero.mp hi).resolve_left (sub_ne_zero.mpr (ne_of_gt ha2))
  have hr : a1 + (1 + a2) * x = 0 := congrArg Complex.re zero
  have roots : (x - 1) * (x + 1) = 0 := by nlinarith [unit]
  rcases mul_eq_zero.mp roots with hpos | hneg
  · have hpos' := sub_eq_zero.mp hpos
    rw [hpos', mul_one] at hr
    linarith
  · have hneg' : x = -1 := by linarith
    rw [hneg', mul_neg, mul_one] at hr
    linarith

theorem centered_dc (b0 b1 b2 : ℝ) : centered b0 b1 b2 1 0 = (b0 + b1 + b2 : ℝ) := by
  apply Complex.ext
  · simp only [centered, Complex.ofReal_re]
    ring
  · simp [centered]

theorem centered_nyquist (b0 b1 b2 : ℝ) :
    centered b0 b1 b2 (-1) 0 = (-(b0 - b1 + b2) : ℝ) := by
  apply Complex.ext
  · simp only [centered, Complex.ofReal_re]
    ring
  · simp [centered]

/-- The peaking stage's center gain is A², as specified by the EQ cookbook.
    Multiplying both numerator and denominator by the same normalization leaves this unchanged. -/
theorem peaking_center_gain {a alpha x y : ℝ} (ha : 0 < a) (hAlpha : 0 < alpha) (hy : 0 < y) :
    centered (1 + alpha * a) (-2 * x) (1 - alpha * a) x y /
      centered (1 + alpha / a) (-2 * x) (1 - alpha / a) x y = ((a ^ 2 : ℝ) : ℂ) := by
  have hn : centered (1 + alpha / a) (-2 * x) (1 - alpha / a) x y ≠ 0 := by
    intro hz
    have hi : (1 + alpha / a - (1 - alpha / a)) * y = 0 := congrArg Complex.im hz
    have positive : 0 < (2 * (alpha / a)) * y := by positivity
    linarith [show (1 + alpha / a - (1 - alpha / a)) * y = (2 * (alpha / a)) * y by ring]
  apply (div_eq_iff hn).mpr
  apply Complex.ext
  · simp only [centered, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · simp only [centered, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
    field_simp
    ring

/-- Scaling both complex operands by nonzero real factors is equivalent to applying
    their scale ratio to the normalized quotient. This models the division fallback. -/
theorem normalized_complex_quotient (a b : ℂ) (sa sb : ℝ)
    (ha : sa ≠ 0) (hb : sb ≠ 0) (h : b ≠ 0) :
    ((sa : ℂ) / (sb : ℂ)) * ((a / (sa : ℂ)) / (b / (sb : ℂ))) = a / b := by
  have hsa := Complex.ofReal_ne_zero.mpr ha
  have hsb := Complex.ofReal_ne_zero.mpr hb
  field_simp

def lr24Transfer (frequency cutoff : ℝ) (lowpass : Bool) : ℂ :=
  let above := cutoff ≤ frequency
  let ratio := if above then cutoff / frequency else frequency / cutoff
  let fourth := ratio ^ 4
  let magnitude := if (lowpass = true ↔ above) then fourth / (1 + fourth) else 1 / (1 + fourth)
  let phaseMagnitude := 2 * Real.arctan (Real.sqrt 2 * ratio / (1 - ratio ^ 2))
  let phaseMagnitude := if ratio = 1 then Real.pi else phaseMagnitude
  let phase := if above then phaseMagnitude else -phaseMagnitude
  ⟨magnitude * Real.cos phase, magnitude * Real.sin phase⟩

private theorem lr24_polar_norm (m phase : ℝ) (hm : 0 ≤ m) :
    ‖(⟨m * Real.cos phase, m * Real.sin phase⟩ : ℂ)‖ = m := by
  rw [Complex.norm_def, Complex.normSq_apply]
  change Real.sqrt ((m * Real.cos phase) * (m * Real.cos phase) +
    (m * Real.sin phase) * (m * Real.sin phase)) = m
  rw [show (m * Real.cos phase) * (m * Real.cos phase) +
      (m * Real.sin phase) * (m * Real.sin phase) = m ^ 2 by
    calc
      _ = m ^ 2 * (Real.sin phase ^ 2 + Real.cos phase ^ 2) := by ring
      _ = m ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]]
  exact Real.sqrt_sq hm

theorem lr24_magnitude {frequency cutoff : ℝ} (hf : 0 < frequency) (hc : 0 < cutoff)
    (lowpass : Bool) :
    ‖lr24Transfer frequency cutoff lowpass‖ =
      1 / (1 + (if lowpass then frequency / cutoff else cutoff / frequency) ^ 4) ∧
    ‖lr24Transfer frequency cutoff lowpass‖ ^ 2 =
      (1 / (1 + (if lowpass then frequency / cutoff else cutoff / frequency) ^ 4)) ^ 2 ∧
    (frequency = cutoff → ‖lr24Transfer frequency cutoff lowpass‖ = 1 / 2) := by
  have normEq : ‖lr24Transfer frequency cutoff lowpass‖ =
      1 / (1 + (if lowpass then frequency / cutoff else cutoff / frequency) ^ 4) := by
    unfold lr24Transfer
    dsimp only
    rw [lr24_polar_norm _ _ (by split <;> positivity)]
    by_cases above : cutoff ≤ frequency <;> cases lowpass <;> simp [above] <;>
      field_simp <;> ring
  refine ⟨normEq, by rw [normEq], ?_⟩
  intro eq
  subst frequency
  rw [normEq]
  cases lowpass <;> norm_num [div_self hc.ne']

/-- The two denominator polynomials cover both choices of imaginary sign. -/
theorem bw24_polynomial_norm (ratio : ℝ) (above : Bool) :
    let re := 1 - (2 + Real.sqrt 2) * ratio ^ 2 + ratio ^ 4
    let im := (if above then -1 else 1) * Real.sqrt (4 + 2 * Real.sqrt 2) * (ratio - ratio ^ 3)
    re ^ 2 + im ^ 2 = 1 + ratio ^ 8 := by
  dsimp only
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : Real.sqrt (4 + 2 * Real.sqrt 2) ^ 2 = 4 + 2 * Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  cases above <;> simp only [Bool.false_eq_true, ite_true, ite_false, one_mul, neg_one_mul]
  all_goals linear_combination ratio ^ 4 * hs + (ratio - ratio ^ 3) ^ 2 * ha

def bw24Denominator (ratio : ℝ) (above : Bool) : ℂ :=
  ⟨1 - (2 + Real.sqrt 2) * ratio ^ 2 + ratio ^ 4,
    (if above then -1 else 1) * Real.sqrt (4 + 2 * Real.sqrt 2) * (ratio - ratio ^ 3)⟩

def bw24Transfer (frequency cutoff : ℝ) : ℂ :=
  if cutoff ≤ frequency then 1 / bw24Denominator (cutoff / frequency) true
  else ((frequency / cutoff : ℝ) : ℂ) ^ 4 / bw24Denominator (frequency / cutoff) false

private theorem bw24_denominator_norm (r : ℝ) (above : Bool) :
    ‖bw24Denominator r above‖ = Real.sqrt (1 + r ^ 8) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  dsimp only [bw24Denominator]
  simpa only [pow_two] using bw24_polynomial_norm r above

theorem bw24_magnitude {frequency cutoff : ℝ} (hf : 0 < frequency) (hc : 0 < cutoff) :
    ‖bw24Transfer frequency cutoff‖ = 1 / Real.sqrt (1 + (cutoff / frequency) ^ 8) ∧
    (frequency = cutoff → ‖bw24Transfer frequency cutoff‖ = 1 / Real.sqrt 2) := by
  have magnitude : ‖bw24Transfer frequency cutoff‖ = 1 / Real.sqrt (1 + (cutoff / frequency) ^ 8) := by
    unfold bw24Transfer
    split
    · rw [norm_div, norm_one, bw24_denominator_norm]
    · rw [norm_div, bw24_denominator_norm, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos hf hc)]
      let r := frequency / cutoff
      have hr : 0 < r := div_pos hf hc
      have inv : cutoff / frequency = 1 / r := by dsimp [r]; field_simp
      rw [inv]
      change r ^ 4 / Real.sqrt (1 + r ^ 8) = 1 / Real.sqrt (1 + (1 / r) ^ 8)
      have radicand : 1 + (1 / r) ^ 8 = (1 + r ^ 8) / (r ^ 4) ^ 2 := by
        field_simp
        ring
      rw [radicand, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity), one_div_div]
  refine ⟨magnitude, ?_⟩
  rintro rfl
  norm_num [magnitude, div_self hf.ne']

private theorem log_one_plus_exp (u : ℝ) :
    max 0 u + Real.log (1 + Real.exp (-|u|)) = Real.log (1 + Real.exp u) := by
  by_cases hu : 0 ≤ u
  · rw [max_eq_right hu, abs_of_nonneg hu]
    have h : Real.exp u * (1 + Real.exp (-u)) = 1 + Real.exp u := by
      rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero, add_comm]
    rw [← h, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  · rw [max_eq_left (le_of_not_ge hu), abs_of_neg (lt_of_not_ge hu), neg_neg, zero_add]

theorem lr24_attenuation_db (u : ℝ) :
    -20 / Real.log 10 * (max 0 u + Real.log (1 + Real.exp (-|u|))) =
      20 / Real.log 10 * Real.log (1 / (1 + Real.exp u)) := by
  rw [log_one_plus_exp, one_div, Real.log_inv]
  ring

theorem bw24_attenuation_db (u : ℝ) :
    -10 / Real.log 10 * (max 0 u + Real.log (1 + Real.exp (-|u|))) =
      10 / Real.log 10 * Real.log (1 / (1 + Real.exp u)) := by
  rw [log_one_plus_exp, one_div, Real.log_inv]
  ring

private theorem normalize_stable {c edge a1 : ℝ} (hc : 0 < c) (he : 0 < edge)
    (ha1 : |a1| < 2 * c) : StableCoefficients (a1 / (c + edge)) ((c - edge) / (c + edge)) := by
  have sum : 0 < c + edge := add_pos hc he
  unfold StableCoefficients
  rw [abs_div, abs_div, abs_of_pos sum, one_add_div sum.ne']
  refine ⟨(div_lt_one sum).mpr (abs_lt.mpr ⟨by linarith, by linarith⟩), ?_⟩
  apply div_lt_div_of_pos_right _ sum
  linarith

private theorem abs_cos_lt_one {x y : ℝ} (hy : 0 < y) (unit : x ^ 2 + y ^ 2 = 1) :
    |x| < 1 := by
  apply (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mp
  rw [sq_abs]
  nlinarith [sq_pos_of_pos hy]

theorem peaking_stability_and_endpoint_gains {a alpha x y : ℝ}
    (ha : 0 < a) (hAlpha : 0 < alpha) (hy : 0 < y) (unit : x ^ 2 + y ^ 2 = 1) :
    let b0 := 1 + alpha * a
    let b1 := -2 * x
    let b2 := 1 - alpha * a
    let a0 := 1 + alpha / a
    let a1 := b1
    let a2 := 1 - alpha / a
    StableCoefficients (a1 / a0) (a2 / a0) ∧
      (b0 + b1 + b2) / (a0 + a1 + a2) = 1 ∧
      (b0 - b1 + b2) / (a0 - a1 + a2) = 1 := by
  dsimp only
  have cosine := abs_lt.mp (abs_cos_lt_one hy unit)
  refine ⟨normalize_stable zero_lt_one (div_pos hAlpha ha) ?_, ?_, ?_⟩
  · apply abs_lt.mpr
    constructor <;> linarith
  · apply (div_eq_iff (by linarith : 1 + alpha / a + -2 * x + (1 - alpha / a) ≠ 0)).mpr
    ring
  · apply (div_eq_iff (by linarith : 1 + alpha / a - -2 * x + (1 - alpha / a) ≠ 0)).mpr
    ring

private theorem shelf_core {a x edge : ℝ} (ha : 0 < a) (hx : |x| < 1) (he : 0 < edge)
    (lowShelf : Bool) :
    let sum := a + 1
    let difference := a - 1
    let sign : ℝ := if lowShelf then 1 else -1
    let b0 := a * (sum - sign * difference * x + edge)
    let b1 := 2 * sign * a * (difference - sign * sum * x)
    let b2 := a * (sum - sign * difference * x - edge)
    let a0 := sum + sign * difference * x + edge
    let a1 := -2 * sign * (difference + sign * sum * x)
    let a2 := sum + sign * difference * x - edge
    StableCoefficients (a1 / a0) (a2 / a0) ∧
      (b0 + b1 + b2) / (a0 + a1 + a2) = (if lowShelf then a ^ 2 else 1) ∧
      (b0 - b1 + b2) / (a0 - a1 + a2) = (if lowShelf then 1 else a ^ 2) := by
  have boundaries := abs_lt.mp hx
  have hsub : 0 < 1 - x := by linarith
  have hadd : 0 < 1 + x := by linarith
  have p := mul_pos ha hsub
  have q := mul_pos ha hadd
  cases lowShelf <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals
    refine ⟨normalize_stable (by nlinarith only [p, q, hsub, hadd]) he
      (abs_lt.mpr ⟨by nlinarith only [p, q, hsub, hadd], by nlinarith only [p, q, hsub, hadd]⟩),
      ?_, ?_⟩
    all_goals
      apply (div_eq_iff (by nlinarith only [p, q, hsub, hadd])).mpr
      ring

theorem shelf_stability_and_endpoint_gains {a slope x y : ℝ} (ha : 0 < a)
    (hs : 0 < slope) (hs₁ : slope ≤ 1) (hy : 0 < y) (unit : x ^ 2 + y ^ 2 = 1)
    (lowShelf : Bool) :
    let sum := a + 1
    let difference := a - 1
    let edge := y * Real.sqrt ((a ^ 2 + 1) * (1 / slope - 1) + 2 * a)
    let sign : ℝ := if lowShelf then 1 else -1
    let b0 := a * (sum - sign * difference * x + edge)
    let b1 := 2 * sign * a * (difference - sign * sum * x)
    let b2 := a * (sum - sign * difference * x - edge)
    let a0 := sum + sign * difference * x + edge
    let a1 := -2 * sign * (difference + sign * sum * x)
    let a2 := sum + sign * difference * x - edge
    StableCoefficients (a1 / a0) (a2 / a0) ∧
      (b0 + b1 + b2) / (a0 + a1 + a2) = (if lowShelf then a ^ 2 else 1) ∧
      (b0 - b1 + b2) / (a0 - a1 + a2) = (if lowShelf then 1 else a ^ 2) := by
  have invSlope : 0 ≤ 1 / slope - 1 :=
    sub_nonneg.mpr ((le_div_iff₀ hs).mpr (by simpa using hs₁))
  exact shelf_core ha (abs_cos_lt_one hy unit) (by positivity) lowShelf

theorem pure_delay_norm (omega delay : ℝ) :
    ‖Complex.exp (-Complex.I * (omega : ℂ) * (delay : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem compose_transfer_norm (a b : ℂ) : ‖a * b‖ = ‖a‖ * ‖b‖ := norm_mul a b

theorem zero_biquad_transfer (a1 a2 x y : ℝ) :
    centered 0 0 0 x y / centered 1 a1 a2 x y = 0 := by
  have zero : centered 0 0 0 x y = 0 := by apply Complex.ext <;> simp [centered]
  rw [zero, zero_div]

end Electroacoustics.Filters
