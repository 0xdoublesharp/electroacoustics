module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
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

end Electroacoustics.Design
