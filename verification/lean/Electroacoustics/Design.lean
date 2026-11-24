module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Design

/-- The sealed acoustic volume inverse reaches the specified positive Qtc. -/
theorem sealed_volume_round_trip {vas qts qtc : ℝ}
    (hvas : 0 < vas) (hqts : 0 < qts) (htarget : qts < qtc) :
    qts * Real.sqrt (1 + vas / (vas / ((qtc / qts) ^ 2 - 1))) = qtc := by
  have hratio : 1 < qtc / qts := (lt_div_iff₀ hqts).2 (by simpa using htarget)
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hvas.ne']
  have hr : 1 + ((qtc / qts) ^ 2 - 1) = (qtc / qts) ^ 2 := by ring
  rw [hr, Real.sqrt_sq (by linarith), mul_div_cancel₀ _ hqts.ne']

/-- Inversion of an affine duct residual as sampled at volumes zero and one. -/
theorem duct_volume_round_trip {offset slope : ℝ} (hslope : slope ≠ 0) :
    offset + slope * (-offset / ((offset + slope) - offset)) = 0 := by
  rw [show offset + slope - offset = slope by ring]
  rw [mul_div_cancel₀ _ hslope]
  ring

/-- The radiator moving-mass inverse attains the target positive angular frequency. -/
theorem radiator_mass_round_trip {stiffness omega : ℝ}
    (hk : 0 < stiffness) (hw : 0 < omega) :
    Real.sqrt (stiffness / (stiffness / omega ^ 2)) = omega := by
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hk.ne', Real.sqrt_sq hw.le]

/-- DSP maps allowable source voltage to the same terminal ceiling. -/
theorem terminal_ceiling_from_input {input gain impedance current : ℝ}
    (hg : 0 < gain) (hz : 0 < impedance) :
    input * gain / impedance ≤ current ↔ input ≤ current * impedance / gain := by
  rw [div_le_iff₀ hz, le_div_iff₀ hg]

/-- Multiplying both biquad polynomials by z preserves the transfer function. -/
theorem biquad_centered_quotient {z numerator denominator : ℂ} (hz : z ≠ 0) :
    (z * numerator) / (z * denominator) = numerator / denominator := by
  exact mul_div_mul_left _ _ hz

/-- Mass added to the diaphragm supplies the independent equation for moving mass. -/
theorem moving_mass_from_added_mass {mass added freeSq loadedSq stiffness : ℝ}
    (hf : freeSq * mass = stiffness) (hl : loadedSq * (mass + added) = stiffness)
    (h : freeSq ≠ loadedSq) :
    mass = loadedSq * added / (freeSq - loadedSq) := by
  rw [eq_div_iff (sub_ne_zero.mpr h)]
  nlinarith

/-- A known sealed test box supplies the independent equation for Vas. -/
theorem vas_from_closed_box {vas volume freeSq loadedSq : ℝ}
    (hv : volume ≠ 0) (hf : freeSq ≠ 0)
    (h : loadedSq = freeSq * (1 + vas / volume)) :
    vas = volume * (loadedSq / freeSq - 1) := by
  rw [h, mul_div_cancel_left₀ _ hf]
  rw [add_sub_cancel_left, mul_div_cancel₀ _ hv]

theorem sealed_f3_exact {qtc : ℝ} (hq : 0 < qtc) :
    let a := (1 / qtc) ^ 2 - 2
    let x := Real.sqrt ((a + Real.sqrt (a ^ 2 + 4)) / 2)
    let response := fun f : ℝ => f ^ 4 / ((1 - f ^ 2) ^ 2 + (f / qtc) ^ 2)
    0 < x ∧ response x = 1 / 2 ∧ (∀ y > 0, response y = 1 / 2 → y = x) := by
  let a := (1 / qtc) ^ 2 - 2
  let s := Real.sqrt (a ^ 2 + 4)
  let u := (a + s) / 2
  let x := Real.sqrt u
  have hs : s ^ 2 = a ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hsAbs : |a| < s :=
    (Real.lt_sqrt (abs_nonneg _)).mpr (by rw [sq_abs]; linarith)
  have hu : 0 < u := by
    dsimp [u]
    linarith [neg_le_abs a]
  have other : a < u := by
    dsimp [u]
    linarith [le_abs_self a]
  have hx : 0 < x := Real.sqrt_pos.2 hu
  have hxSq : x ^ 2 = u := Real.sq_sqrt hu.le
  have quadratic : u ^ 2 - a * u - 1 = 0 := by
    dsimp [u]
    nlinarith [hs]
  have response_iff (f : ℝ) (hf : 0 < f) :
      f ^ 4 / ((1 - f ^ 2) ^ 2 + (f / qtc) ^ 2) = 1 / 2 ↔
        (f ^ 2) ^ 2 - a * f ^ 2 - 1 = 0 := by
    have den : 0 < (1 - f ^ 2) ^ 2 + (f / qtc) ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (div_pos hf hq))
    rw [div_eq_iff den.ne']
    have term : (f / qtc) ^ 2 = (1 / qtc) ^ 2 * f ^ 2 := by ring
    rw [term]
    dsimp [a]
    constructor <;> intro h <;> nlinarith only [h]
  refine ⟨hx, (response_iff x hx).mpr (hxSq ▸ quadratic), ?_⟩
  intro y hy hy3
  have hyPoly := (response_iff y hy).mp hy3
  have factor : (y ^ 2 - u) * (y ^ 2 + u - a) = 0 := by
    linear_combination hyPoly - quadratic
  have hpos : 0 < y ^ 2 + u - a := by linarith [sq_nonneg y]
  have hsq := sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_right hpos.ne')
  exact (sq_eq_sq₀ hy.le hx.le).mp (hsq.trans hxSq.symm)

def ventTuning (area volume length speed : ℝ) : ℝ :=
  speed / (2 * Real.pi) * Real.sqrt (area / (volume * length))

def ventLength (area volume frequency speed : ℝ) : ℝ :=
  area / volume * (speed / (2 * Real.pi * frequency)) ^ 2

theorem vent_tuning_round_trip {area volume frequency speed : ℝ}
    (ha : 0 < area) (hv : 0 < volume) (hf : 0 < frequency) (hc : 0 < speed) :
    ventTuning area volume (ventLength area volume frequency speed) speed = frequency := by
  have hpi := Real.pi_pos
  have ratio : area / (volume * ventLength area volume frequency speed) =
      (2 * Real.pi * frequency / speed) ^ 2 := by
    unfold ventLength
    field_simp
  rw [ventTuning, ratio, Real.sqrt_sq (by positivity)]
  field_simp

theorem vent_length_round_trip {area volume length speed : ℝ}
    (ha : 0 < area) (hv : 0 < volume) (hl : 0 < length) (hc : 0 < speed) :
    ventLength area volume (ventTuning area volume length speed) speed = length := by
  have hpi := Real.pi_pos
  let r := Real.sqrt (area / (volume * length))
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hrsq : r ^ 2 = area / (volume * length) := Real.sq_sqrt (by positivity)
  have ratio : speed / (2 * Real.pi * ventTuning area volume length speed) = 1 / r := by
    change speed / (2 * Real.pi * (speed / (2 * Real.pi) * r)) = _
    field_simp
  rw [ventLength, ratio, div_pow, one_pow, hrsq]
  field_simp

theorem radiator_tuning_gt_free_resonance {compliance mass count area density speed volume : ℝ}
    (hk : 0 < compliance) (hm : 0 < mass) (hn : 0 < count) (ha : 0 < area)
    (hd : 0 < density) (hc : 0 < speed) (hv : 0 < volume) :
    1 / (2 * Real.pi) / Real.sqrt mass / Real.sqrt compliance <
      Real.sqrt ((1 / compliance + count * area ^ 2 * density * speed ^ 2 / volume) / mass) /
        (2 * Real.pi) := by
  have hpi := Real.pi_pos
  have free : 1 / (2 * Real.pi) / Real.sqrt mass / Real.sqrt compliance =
      Real.sqrt ((1 / compliance) / mass) / (2 * Real.pi) := by
    rw [Real.sqrt_div (by positivity : 0 ≤ (1 : ℝ) / compliance),
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    ring
  rw [free]
  apply div_lt_div_of_pos_right _ (by positivity)
  apply (Real.sqrt_lt_sqrt_iff (by positivity)).mpr
  apply div_lt_div_of_pos_right _ hm
  exact lt_add_of_pos_right _ (by positivity)

/-- The runtime keeps the upper half only when the midpoint tunes above the target. -/
def ductLengthBisect (tuning : ℝ → ℝ) (target : ℝ) : ℕ → ℝ × ℝ → ℝ × ℝ
  | 0, bracket => bracket
  | n + 1, bracket =>
    let (low, high) := ductLengthBisect tuning target n bracket
    let mid := low + (high - low) / 2
    if target < tuning mid then (mid, high) else (low, mid)

private theorem ductLengthBisect_bracket (tuning : ℝ → ℝ) (target : ℝ) {low high : ℝ}
    (order : low ≤ high) (lower : target ≤ tuning low) (upper : tuning high ≤ target)
    (n : ℕ) :
    let (l, h) := ductLengthBisect tuning target n (low, high)
    low ≤ l ∧ l ≤ h ∧ h ≤ high ∧ tuning h ≤ target ∧ target ≤ tuning l ∧
      h - l = (high - low) / 2 ^ n := by
  induction n with
  | zero => simp [ductLengthBisect, order, lower, upper]
  | succ n ih =>
    rcases hb : ductLengthBisect tuning target n (low, high) with ⟨l, h⟩
    rw [hb] at ih
    dsimp only at ih
    obtain ⟨hl, hlh, hh, hhi, hlo, width⟩ := ih
    let mid := l + (h - l) / 2
    have loMid : l ≤ mid := by dsimp [mid]; linarith
    have midHi : mid ≤ h := by dsimp [mid]; linarith
    have half : (high - low) / (2 : ℝ) ^ (n + 1) = (h - l) / 2 := by
      rw [pow_succ, ← div_div, ← width]
    rw [ductLengthBisect, hb]
    change (let (l', h') := if target < tuning mid then (mid, h) else (l, mid)
      low ≤ l' ∧ l' ≤ h' ∧ h' ≤ high ∧ tuning h' ≤ target ∧ target ≤ tuning l' ∧
        h' - l' = (high - low) / 2 ^ (n + 1))
    by_cases hm : target < tuning mid
    · simp only [hm, ite_true]
      exact ⟨hl.trans loMid, midHi, hh, hhi, hm.le, by rw [half]; dsimp [mid]; ring⟩
    · simp only [hm, ite_false]
      exact ⟨hl, loMid, midHi.trans hh, le_of_not_gt hm, hlo, by rw [half]; dsimp [mid]; ring⟩

theorem duct_length_bisection_sound (tuning : ℝ → ℝ) (target : ℝ) {low high : ℝ}
    (order : low ≤ high) (continuous : ContinuousOn tuning (Set.Icc low high))
    (antitone : AntitoneOn tuning (Set.Icc low high)) :
    (tuning low < target → ∀ length ∈ Set.Icc low high, tuning length ≠ target) ∧
    (target < tuning high → ∀ length ∈ Set.Icc low high, tuning length ≠ target) ∧
    (tuning high ≤ target → target ≤ tuning low → ∀ n : ℕ,
      let (l, h) := ductLengthBisect tuning target n (low, high)
      tuning h ≤ target ∧ target ≤ tuning l ∧ h - l = (high - low) / 2 ^ n ∧
      ∃ r ∈ Set.Icc l h, tuning r = target ∧ |l + (h - l) / 2 - r| ≤ (h - l) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ht length hm
    exact ((antitone ⟨le_rfl, order⟩ hm hm.1).trans_lt ht).ne
  · intro ht length hm
    exact (ht.trans_le (antitone hm ⟨order, le_rfl⟩ hm.2)).ne'
  · intro hhi hlo n
    have bracket := ductLengthBisect_bracket tuning target order hlo hhi n
    rcases hs : ductLengthBisect tuning target n (low, high) with ⟨l, h⟩
    rw [hs] at bracket
    obtain ⟨hl, hlh, hh, hi, lo, width⟩ := bracket
    have cont := continuous.mono (Set.Icc_subset_Icc hl hh)
    obtain ⟨r, hr, htr⟩ := intermediate_value_Icc' hlh cont (show target ∈ Set.Icc _ _ from ⟨hi, lo⟩)
    exact ⟨hi, lo, width, r, hr, htr, abs_le.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩⟩

end Electroacoustics.Design
