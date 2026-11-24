module

public import Electroacoustics.Circuit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Radiator

open Circuit

structure Cabinet where
  electrical : ℂ
  mechanical : ℂ
  cavity : ℂ
  radiator : ℂ
  count : ℝ
  area : ℝ
  coupling : ℝ
  radiatorCount : ℝ
  radiatorArea : ℝ

structure Solution where
  current : ℂ
  cone : ℂ
  pressure : ℂ
  radiatorVelocity : ℂ

/-- The radiator flow uses the cavity-flow sign. Its external radiation has the opposite sign. -/
structure Balances (p : Cabinet) (drive : ℂ) (x : Solution) : Prop where
  electrical : drive = p.electrical * x.current + (p.coupling : ℂ) * x.cone
  cone : (p.coupling : ℂ) * x.current = p.mechanical * x.cone + (p.area : ℂ) * x.pressure
  cavity : ((p.count * p.area : ℝ) : ℂ) * x.cone =
    p.cavity * x.pressure + ((p.radiatorCount * p.radiatorArea : ℝ) : ℂ) * x.radiatorVelocity
  radiator : p.radiator * x.radiatorVelocity = (p.radiatorArea : ℂ) * x.pressure

def radiatorAreaTerm (p : Cabinet) : ℂ := ((p.radiatorCount * p.radiatorArea ^ 2 : ℝ) : ℂ)

def clearedAdmittance (p : Cabinet) : ℂ := p.cavity * p.radiator + radiatorAreaTerm p

def numerator (p : Cabinet) : ℂ :=
  p.mechanical * clearedAdmittance p + ((p.count * p.area ^ 2 : ℝ) : ℂ) * p.radiator

def clearedDenominator (p : Cabinet) : ℂ :=
  p.electrical * numerator p + ((p.coupling ^ 2 : ℝ) : ℂ) * clearedAdmittance p

def solve (p : Cabinet) (drive : ℂ) : Solution where
  current := drive * numerator p / clearedDenominator p
  cone := drive * (p.coupling : ℂ) * clearedAdmittance p / clearedDenominator p
  pressure := drive * ((p.count * p.area * p.coupling : ℝ) : ℂ) * p.radiator / clearedDenominator p
  radiatorVelocity := drive * ((p.count * p.area * p.coupling * p.radiatorArea : ℝ) : ℂ) /
    clearedDenominator p

/-- The cleared fractions satisfy the coupled equations even at zero radiator impedance. -/
theorem solve_satisfies (p : Cabinet) (drive : ℂ) (hd : clearedDenominator p ≠ 0) :
    Balances p drive (solve p drive) := by
  constructor
  · simp only [solve]
    field_simp
    simp only [clearedDenominator, Complex.ofReal_pow]
  · simp only [solve]
    field_simp
    simp only [numerator, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  · simp only [solve]
    field_simp
    simp only [clearedAdmittance, radiatorAreaTerm, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  · simp only [solve]
    field_simp
    simp only [Complex.ofReal_mul]
    ring

theorem radiator_admittance_nonneg (p : Cabinet) (hr : 0 ≤ p.radiator.re)
    (hc : 0 ≤ p.radiatorCount) : 0 ≤ (radiatorAreaTerm p / p.radiator).re := by
  exact real_div_nonnegative hr (mul_nonneg hc (sq_nonneg _))

theorem radiator_terminal_impedance (p : Cabinet) (drive : ℂ)
    (hv : drive ≠ 0) (hn : numerator p ≠ 0) :
    drive / (solve p drive).current = clearedDenominator p / numerator p ∧
      drive / (solve p drive).current =
        p.electrical + ((p.coupling ^ 2 : ℝ) : ℂ) * clearedAdmittance p / numerator p := by
  have h : drive / (solve p drive).current = clearedDenominator p / numerator p := by
    simp only [solve, div_div_eq_mul_div]
    rw [mul_div_mul_left _ _ hv]
  exact ⟨h, by rw [h, clearedDenominator, add_div, mul_div_cancel_right₀ _ hn]⟩

/-- Positive copper and cone resistances make the denominator nonzero for a passive cabinet. -/
theorem passive_denominator_ne_zero (p : Cabinet) (hc : 0 < p.count) (hs : p.area ≠ 0)
    (he : 0 < p.electrical.re) (hm : 0 < p.mechanical.re) (hy : 0 ≤ p.cavity.re)
    (hr : 0 ≤ p.radiator.re) (hrc : 0 < p.radiatorCount) (hrs : p.radiatorArea ≠ 0) :
    clearedDenominator p ≠ 0 := by
  by_cases zero : p.radiator = 0
  · have hk : radiatorAreaTerm p ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mul_ne_zero hrc.ne' (pow_ne_zero 2 hrs))
    have e : p.electrical ≠ 0 := by
      intro h
      simp [h] at he
    have hfree : p.mechanical + ((p.coupling ^ 2 : ℝ) : ℂ) / p.electrical ≠ 0 := by
      have loss := real_div_nonnegative he.le (sq_nonneg p.coupling)
      intro h
      have h0 := congrArg Complex.re h
      simp only [Complex.add_re, Complex.zero_re] at h0
      linarith
    have factored : clearedDenominator p =
        p.electrical * (p.mechanical + ((p.coupling ^ 2 : ℝ) : ℂ) / p.electrical) * radiatorAreaTerm p := by
      simp only [clearedDenominator, numerator, clearedAdmittance, zero, mul_zero, zero_add, add_zero]
      field_simp
    rw [factored]
    exact mul_ne_zero (mul_ne_zero e hfree) hk
  · let adm := p.cavity + radiatorAreaTerm p / p.radiator
    have hadm : 0 ≤ adm.re := by
      change 0 ≤ p.cavity.re + (radiatorAreaTerm p / p.radiator).re
      exact add_nonneg hy (real_div_nonnegative hr (mul_nonneg hrc.le (sq_nonneg _)))
    have combined : clearedAdmittance p = adm * p.radiator := by
      simp only [clearedAdmittance, adm, add_mul, div_mul_cancel₀ _ zero]
    have factored : clearedDenominator p =
        Circuit.denominator p.electrical p.mechanical adm p.count p.area p.coupling * p.radiator := by
      simp only [clearedDenominator, numerator, combined, Circuit.denominator, mechanicalNumerator]
      ring
    rw [factored]
    exact mul_ne_zero (Circuit.passive_denominator_ne_zero hc hs he hm hadm) zero

theorem power_balance (p : Cabinet) (drive : ℂ) (x : Solution) (h : Balances p drive x) :
    p.count * rmsPower drive x.current =
      p.count * p.electrical.re * rmsPower x.current x.current +
      p.count * p.mechanical.re * rmsPower x.cone x.cone +
      p.cavity.re * rmsPower x.pressure x.pressure +
      p.radiatorCount * p.radiator.re * rmsPower x.radiatorVelocity x.radiatorVelocity := by
  have conePower : p.coupling * rmsPower x.cone x.current =
      p.mechanical.re * rmsPower x.cone x.cone + p.area * rmsPower x.pressure x.cone := by
    calc
      _ = rmsPower ((p.coupling : ℂ) * x.current) x.cone := by rw [power_scale, power_comm x.current]
      _ = _ := by rw [h.cone, power_add, power_at_impedance, power_scale]
  have radiatorPower : p.radiatorArea * rmsPower x.radiatorVelocity x.pressure =
      p.radiator.re * rmsPower x.radiatorVelocity x.radiatorVelocity := by
    rw [power_comm x.radiatorVelocity, ← power_scale, ← h.radiator, power_at_impedance]
  have cavityPower : p.count * (p.area * rmsPower x.pressure x.cone) =
      p.cavity.re * rmsPower x.pressure x.pressure +
      p.radiatorCount * p.radiator.re * rmsPower x.radiatorVelocity x.radiatorVelocity := by
    calc
      _ = rmsPower (((p.count * p.area : ℝ) : ℂ) * x.cone) x.pressure := by
        rw [power_scale, power_comm x.cone]
        ring
      _ = _ := by
        rw [h.cavity, power_add, power_at_impedance, power_scale, mul_assoc, radiatorPower]
        ring
  calc
    _ = p.count * (p.electrical.re * rmsPower x.current x.current +
        p.coupling * rmsPower x.cone x.current) := by
      rw [h.electrical, power_add, power_at_impedance, power_scale]
    _ = _ := by rw [conePower, mul_add, mul_add, cavityPower]; ring

/-- At free lossless radiator resonance, the cavity pressure is zero, and the generated
    cone and radiator volume flows cancel in the coincident-source radiation model. -/
theorem lossless_free_notch (p : Cabinet) (drive : ℂ) (x : Solution) (h : Balances p drive x)
    (hz : p.radiator = 0) (hs : p.radiatorArea ≠ 0) : x.pressure = 0 ∧
      ((p.count * p.area : ℝ) : ℂ) * x.cone -
        ((p.radiatorCount * p.radiatorArea : ℝ) : ℂ) * x.radiatorVelocity = 0 := by
  have pressure : x.pressure = 0 := by
    have equation := h.radiator
    rw [hz, zero_mul] at equation
    exact (mul_eq_zero.mp equation.symm).resolve_left (Complex.ofReal_ne_zero.mpr hs)
  refine ⟨pressure, sub_eq_zero.mpr ?_⟩
  simpa only [pressure, mul_zero, zero_add] using h.cavity

end Electroacoustics.Radiator
