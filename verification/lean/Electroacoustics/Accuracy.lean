module

public import Electroacoustics.Interval
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Accuracy

/-- Decode the sign, biased exponent, and 52 fraction bits of a finite binary64 word. -/
def binary64Dyad (negative : Bool) (biasedExponent fraction : ℕ) : ℤ × ℤ :=
  let mantissa : ℤ := (fraction : ℤ) + if biasedExponent = 0 then 0 else 2 ^ 52
  (if negative then -mantissa else mantissa, (max biasedExponent 1 : ℕ) - (1075 : ℤ))

theorem binary64_dyad_value (negative : Bool) (biasedExponent fraction : ℕ)
    (hExponent : biasedExponent < 2047) (hFraction : fraction < 2 ^ 52) :
    let (significand, exponent) := binary64Dyad negative biasedExponent fraction
    (significand : ℚ) * (2 : ℚ) ^ exponent =
      (if negative then -1 else 1) *
        (if biasedExponent = 0 then (fraction : ℚ) / 2 ^ (1074 : ℕ)
         else (1 + (fraction : ℚ) / 2 ^ (52 : ℕ)) * (2 : ℚ) ^ ((biasedExponent : ℤ) - 1023)) ∧
    -1074 ≤ exponent ∧ exponent ≤ 971 ∧ significand.natAbs < 2 ^ 53 := by
  dsimp only [binary64Dyad]
  have exponentRange : -1074 ≤ (max biasedExponent 1 : ℕ) - (1075 : ℤ) ∧
      (max biasedExponent 1 : ℕ) - (1075 : ℤ) ≤ 971 := by omega
  by_cases hz : biasedExponent = 0
  · subst biasedExponent
    cases negative <;> norm_num [zpow_neg, div_eq_mul_inv] at ⊢ <;> omega
  · have hm : max biasedExponent 1 = biasedExponent := max_eq_left (by omega)
    have hp : (2 : ℚ) ^ ((biasedExponent : ℤ) - 1075) =
        (2 : ℚ) ^ ((biasedExponent : ℤ) - 1023) / (2 : ℚ) ^ (52 : ℕ) := by
      rw [show (biasedExponent : ℤ) - 1075 = ((biasedExponent : ℤ) - 1023) - 52 by omega,
        zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
      rfl
    refine ⟨?_, exponentRange.1, exponentRange.2, ?_⟩
    · cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true, hz, hm,
        Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, hp] <;> ring
    · cases negative <;> simp [hz] <;> omega

/-- Multiplying by 2^1074 turns every finite dyad into the integer used by
    complex division. The exponent of the left shift is nonnegative. -/
theorem binary64_dyad_integer_scaling (significand exponent : ℤ) (he : -1074 ≤ exponent) :
    (significand : ℚ) * (2 : ℚ) ^ exponent * (2 : ℚ) ^ (1074 : ℕ) =
      ((significand * (2 : ℤ) ^ (exponent + 1074).toNat : ℤ) : ℚ) := by
  suffices ∀ k : ℕ, 0 ≤ exponent + (k : ℤ) →
      (significand : ℚ) * (2 : ℚ) ^ exponent * (2 : ℚ) ^ k =
        ((significand * (2 : ℤ) ^ (exponent + (k : ℤ)).toNat : ℤ) : ℚ) from
    this 1074 (by omega)
  intro k hk
  rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, ← zpow_natCast (2 : ℚ) (exponent + (k : ℤ)).toNat,
    Int.toNat_of_nonneg hk, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
  exact mul_assoc _ _ _

/-- The two possible rounded values straddle a positive ratio on its chosen
    binary64 grid. The exact remainder selects the closer of the two. -/
theorem rounding_neighbors (ratio lower step : ℝ) (_positiveStep : 0 < step)
    (nonnegativeRemainder : lower ≤ ratio) (remainderLtStep : ratio < lower + step) :
    (2 * (ratio - lower) ≤ step → |ratio - lower| ≤ |ratio - (lower + step)|) ∧
    (step ≤ 2 * (ratio - lower) → |ratio - (lower + step)| ≤ |ratio - lower|) := by
  rw [abs_of_nonneg (sub_nonneg.mpr nonnegativeRemainder),
    abs_of_neg (sub_neg.mpr remainderLtStep)]
  exact ⟨fun h => by linarith, fun h => by linarith⟩

theorem half_step_is_tie (ratio lower step : ℝ) (_positiveStep : 0 < step)
    (half : 2 * (ratio - lower) = step) :
    |ratio - lower| = |ratio - (lower + step)| := by
  rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)]
  linarith

/-- The unsigned BigInt rounding decision after scaling to the selected binary64 unit. -/
def roundRatioUnits (n d : ℕ) : ℕ :=
  let whole := n / d
  let twiceRemainder := 2 * (n % d)
  whole + if d < twiceRemainder ∨ (twiceRemainder = d ∧ whole % 2 = 1) then 1 else 0

theorem roundRatio_nearest_even (n d : ℕ) (hd : 0 < d) {step : ℝ} (hs : 0 < step) :
    let ratio := (n : ℝ) / d * step
    let rounded := (roundRatioUnits n d : ℝ) * step
    |ratio - rounded| ≤ step / 2 ∧
      (∀ j : ℤ, |ratio - rounded| ≤ |ratio - (j : ℝ) * step|) ∧
      (2 * (n % d) = d → roundRatioUnits n d % 2 = 0) := by
  dsimp only
  have decomp : (n : ℝ) = (n / d : ℕ) * (d : ℝ) + (n % d : ℕ) := by
    exact_mod_cast (Nat.div_add_mod' n d).symm
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have delta : (n : ℝ) / d = (n / d : ℕ) + (n % d : ℕ) / (d : ℝ) := by
    apply (div_eq_iff hd'.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hd'.ne']
    exact decomp
  have remNonneg : (0 : ℝ) ≤ (n % d : ℕ) / (d : ℝ) := by positivity
  have remLt : (n % d : ℕ) / (d : ℝ) < 1 :=
    (div_lt_one hd').mpr (by exact_mod_cast Nat.mod_lt n hd)
  have error : |(n : ℝ) / d - (roundRatioUnits n d : ℝ)| ≤ 1 / 2 := by
    rw [delta, roundRatioUnits]
    split <;> rename_i h
    · push_cast
      have hhalf : (1 : ℝ) / 2 ≤ (n % d : ℕ) / (d : ℝ) := by
        apply (le_div_iff₀ hd').mpr
        have hh : (d : ℝ) ≤ 2 * (n % d : ℕ) := by
          exact_mod_cast (show d ≤ 2 * (n % d) by omega)
        linarith
      rw [abs_of_nonpos (by linarith)]
      linarith
    · simp only [Nat.add_zero]
      have hhalf : (n % d : ℕ) / (d : ℝ) ≤ 1 / 2 := by
        apply (div_le_iff₀ hd').mpr
        have hh : (2 : ℝ) * (n % d : ℕ) ≤ d := by
          exact_mod_cast (show 2 * (n % d) ≤ d by omega)
        linarith
      rw [abs_of_nonneg (by linarith)]
      linarith
  have scaled (j : ℤ) : |(n : ℝ) / d * step - (j : ℝ) * step| =
      |(n : ℝ) / d - (j : ℝ)| * step := by
    rw [← sub_mul, abs_mul, abs_of_pos hs]
  have roundedScaled := scaled (roundRatioUnits n d)
  push_cast at roundedScaled
  rw [roundedScaled]
  refine ⟨by linarith [mul_le_mul_of_nonneg_right error hs.le], ?_, ?_⟩
  · intro j
    rw [scaled]
    apply mul_le_mul_of_nonneg_right _ hs.le
    by_cases hj : j = (roundRatioUnits n d : ℤ)
    · simp [hj]
    · have sep : (1 : ℝ) ≤ |(j : ℝ) - (roundRatioUnits n d : ℝ)| := by
        rcases lt_or_gt_of_ne hj with hj | hj
        · have h : (j : ℝ) + 1 ≤ (roundRatioUnits n d : ℝ) := by
            exact_mod_cast Int.add_one_le_iff.mpr hj
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have h : (roundRatioUnits n d : ℝ) + 1 ≤ (j : ℝ) := by
            exact_mod_cast Int.add_one_le_iff.mpr hj
          rw [abs_of_nonneg (by linarith)]
          linarith
      have tri := abs_sub_le (j : ℝ) ((n : ℝ) / d) (roundRatioUnits n d : ℝ)
      rw [abs_sub_comm (j : ℝ) ((n : ℝ) / d)] at tri
      linarith
  · intro ht
    simp only [roundRatioUnits, ht, lt_self_iff_false, false_or, true_and]
    split <;> omega

def roundRatioSignedUnits (n : ℤ) (d : ℕ) : ℤ :=
  if n < 0 then -(roundRatioUnits n.natAbs d : ℤ) else roundRatioUnits n.natAbs d

theorem roundRatio_signed_nearest_even (n : ℤ) (d : ℕ) (hd : 0 < d) {step : ℝ} (hs : 0 < step) :
    let ratio := (n : ℝ) / d * step
    let rounded := (roundRatioSignedUnits n d : ℝ) * step
    |ratio - rounded| ≤ step / 2 ∧
      (∀ j : ℤ, |ratio - rounded| ≤ |ratio - (j : ℝ) * step|) ∧
      (2 * (n.natAbs % d) = d → roundRatioSignedUnits n d % 2 = 0) := by
  dsimp only
  obtain ⟨error, nearest, even⟩ := roundRatio_nearest_even n.natAbs d hd hs
  by_cases hn : n < 0
  · have hnAbs : (n.natAbs : ℝ) = -(n : ℝ) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.ofNat_natAbs_of_nonpos hn.le)
    have reflect (j : ℤ) : |(n : ℝ) / d * step - (j : ℝ) * step| =
        |(n.natAbs : ℝ) / d * step - ((-j : ℤ) : ℝ) * step| := by
      rw [← abs_neg, hnAbs, Int.cast_neg, neg_div]
      congr 1
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [reflect]
      simpa [roundRatioSignedUnits, hn] using error
    · intro j
      rw [reflect, reflect j]
      simpa [roundRatioSignedUnits, hn] using nearest (-j)
    · intro tie
      have parity := even tie
      simp only [roundRatioSignedUnits, hn, ite_true, Int.neg_emod_two]
      omega
  · have hnAbs : (n.natAbs : ℝ) = (n : ℝ) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg (le_of_not_gt hn))
    rw [← hnAbs]
    refine ⟨?_, ?_, ?_⟩
    · simpa [roundRatioSignedUnits, hn] using error
    · simpa [roundRatioSignedUnits, hn] using nearest
    · intro tie
      have parity := even tie
      simp only [roundRatioSignedUnits, hn, ite_false]
      omega

/-- The integer representation of every finite component uses the same dyadic
    denominator, which cancels before the real and imaginary ratios are rounded. -/
theorem complex_div_exact_scaling (a b : ℂ) (hb : b ≠ 0) :
    let scale : ℝ := 2 ^ (1074 : ℕ)
    let ar := scale * a.re
    let ai := scale * a.im
    let br := scale * b.re
    let bi := scale * b.im
    a / b = ⟨(ar * br + ai * bi) / (br ^ 2 + bi ^ 2),
      (ai * br - ar * bi) / (br ^ 2 + bi ^ 2)⟩ := by
  suffices ∀ scale : ℝ, scale ≠ 0 →
      a / b = ⟨(scale * a.re * (scale * b.re) + scale * a.im * (scale * b.im)) /
        ((scale * b.re) ^ 2 + (scale * b.im) ^ 2),
        (scale * a.im * (scale * b.re) - scale * a.re * (scale * b.im)) /
        ((scale * b.re) ^ 2 + (scale * b.im) ^ 2)⟩ from this _ (by positivity)
  intro scale hs
  have den : b.re ^ 2 + b.im ^ 2 ≠ 0 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.normSq_pos.mpr hb).ne'
  have factor : (scale * b.re) ^ 2 + (scale * b.im) ^ 2 =
      scale ^ 2 * (b.re ^ 2 + b.im ^ 2) := by ring
  apply Complex.ext
  · simp only [Complex.div_re, Complex.normSq_apply]
    rw [factor]
    field_simp [hs, den, pow_two]
  · simp only [Complex.div_im, Complex.normSq_apply]
    rw [factor]
    field_simp [hs, den, pow_two]

/-- The predecessor and successor are competing representable values for
    nearest rounding, even when the spacing changes across a binade boundary. -/
theorem outward_binary64_sound {lo hi x roundedLo roundedHi down up : ℝ}
    (hx : lo ≤ x ∧ x ≤ hi) (downLt : down < roundedLo) (upLt : roundedHi < up)
    (nearestLo : |lo - roundedLo| ≤ |lo - down|)
    (nearestHi : |hi - roundedHi| ≤ |hi - up|) :
    down ≤ x ∧ x ≤ up := by
  have lower : down ≤ lo := by
    by_contra! tooHigh
    rw [abs_of_neg (sub_neg.mpr (tooHigh.trans downLt)),
      abs_of_neg (sub_neg.mpr tooHigh)] at nearestLo
    linarith
  have upper : hi ≤ up := by
    by_contra! tooLow
    rw [abs_of_pos (sub_pos.mpr (upLt.trans tooLow)),
      abs_of_pos (sub_pos.mpr tooLow)] at nearestHi
    linarith
  exact ⟨lower.trans hx.1, hx.2.trans upper⟩

theorem dyadic_grid_round_sound {a : Interval.Box} {x : ℝ} (hx : a.Contains x) (p : ℕ) :
    (a.roundOut p).Contains x := Interval.roundOut_sound hx p

/-- The representative test bounds error for every exact value in the
    enclosure, including cancellation through zero. -/
theorem representative_error {x result lo hi : ℝ} (hx : lo ≤ x ∧ x ≤ hi)
    (loValid : result - lo ≤ 2⁻¹ ^ (40 : ℕ) * max 1 (max lo (-hi)))
    (hiValid : hi - result ≤ 2⁻¹ ^ (40 : ℕ) * max 1 (max lo (-hi))) :
    |result - x| ≤ 2⁻¹ ^ (40 : ℕ) * max 1 |x| := by
  have lowerAbs : max lo (-hi) ≤ |x| :=
    max_le (hx.1.trans (le_abs_self _)) ((neg_le_neg hx.2).trans (neg_le_abs _))
  have widened := mul_le_mul_of_nonneg_left (max_le_max (le_refl (1 : ℝ)) lowerAbs)
    (show 0 ≤ (2⁻¹ : ℝ) ^ (40 : ℕ) by positivity)
  rw [abs_le]
  exact ⟨by linarith [hiValid.trans widened, hx.2], by linarith [loValid.trans widened, hx.1]⟩

/-- Evaluating the pressure ratio in log space preserves the exact SPL. -/
theorem scaled_spl (scale normalized reference : ℝ)
    (hs : 0 < scale) (hn : 0 < normalized) (hr : 0 < reference) :
    Real.log (scale * normalized / reference) =
      Real.log scale + Real.log normalized - Real.log reference := by
  rw [Real.log_div (mul_pos hs hn).ne' hr.ne', Real.log_mul hs.ne' hn.ne']

theorem pressure_spl_floor_sound (p : ℂ) {floor p0 : ℝ} (hf : 0 < floor) (hp0 : 0 < p0) :
    let scale := max (max |p.re| |p.im|) floor
    let normalized := max ‖(⟨p.re / scale, p.im / scale⟩ : ℂ)‖ (floor / scale)
    scale * normalized = max ‖p‖ floor ∧
      20 * (Real.logb 10 scale + Real.logb 10 normalized - Real.logb 10 p0) =
        20 * Real.logb 10 (max ‖p‖ floor / p0) := by
  dsimp only
  let scale := max (max |p.re| |p.im|) floor
  have hs : 0 < scale := hf.trans_le (le_max_right _ _)
  have scaled : (⟨p.re / scale, p.im / scale⟩ : ℂ) = p / (scale : ℂ) := by
    apply Complex.ext
    · exact (Complex.div_ofReal_re p scale).symm
    · exact (Complex.div_ofReal_im p scale).symm
  rw [show max (max |p.re| |p.im|) floor = scale from rfl, scaled, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs]
  have hnorm : 0 < max (‖p‖ / scale) (floor / scale) :=
    (div_pos hf hs).trans_le (le_max_right _ _)
  have restore : scale * max (‖p‖ / scale) (floor / scale) = max ‖p‖ floor := by
    rw [mul_max_of_nonneg _ _ hs.le, mul_div_cancel₀ _ hs.ne', mul_div_cancel₀ _ hs.ne']
  refine ⟨restore, ?_⟩
  rw [← restore, Real.logb_div (mul_pos hs hnorm).ne' hp0.ne', Real.logb_mul hs.ne' hnorm.ne']

end Electroacoustics.Accuracy
