module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Circuit

/-- Real power for two RMS phasors, i.e. the real part of voltage times conjugate current. -/
def rmsPower (voltage current : ℂ) : ℝ :=
  voltage.re * current.re + voltage.im * current.im

theorem power_add (a b c : ℂ) :
    rmsPower (a + b) c = rmsPower a c + rmsPower b c := by
  simp only [rmsPower, Complex.add_re, Complex.add_im]
  ring

theorem power_scale (scale : ℝ) (a b : ℂ) :
    rmsPower ((scale : ℂ) * a) b = scale * rmsPower a b := by
  simp only [rmsPower, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem power_comm (a b : ℂ) : rmsPower a b = rmsPower b a := by
  unfold rmsPower
  ring

theorem power_at_impedance (impedance current : ℂ) :
    rmsPower (impedance * current) current = impedance.re * rmsPower current current := by
  simp only [rmsPower, Complex.mul_re, Complex.mul_im]
  ring

private theorem self_power_nonnegative (a : ℂ) : 0 ≤ rmsPower a a := by
  unfold rmsPower
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

private theorem self_power_positive {a : ℂ} (nonzero : a ≠ 0) : 0 < rmsPower a a := by
  simpa only [Complex.normSq_apply, rmsPower] using Complex.normSq_pos.mpr nonzero

/-- One identical driver's electrical and mechanical balance and the common
    cavity's volume-flow balance. The admittance includes all acoustic branches. -/
structure Equations (electrical mechanical admittance : ℂ) (count area coupling : ℝ)
    (voltage current velocity pressure : ℂ) : Prop where
  electricalBalance : voltage = electrical * current + (coupling : ℂ) * velocity
  mechanicalBalance :
    (coupling : ℂ) * current = mechanical * velocity + (area : ℂ) * pressure
  cavityBalance : ((count * area : ℝ) : ℂ) * velocity = admittance * pressure

theorem power_balance {electrical mechanical admittance : ℂ} {count area coupling : ℝ}
    {voltage current velocity pressure : ℂ}
    (h : Equations electrical mechanical admittance count area coupling
      voltage current velocity pressure) :
    count * rmsPower voltage current =
      count * electrical.re * rmsPower current current +
      count * mechanical.re * rmsPower velocity velocity +
      admittance.re * rmsPower pressure pressure := by
  have mechanicalPower : coupling * rmsPower velocity current =
      mechanical.re * rmsPower velocity velocity + area * rmsPower pressure velocity := by
    calc
      _ = rmsPower ((coupling : ℂ) * current) velocity := by rw [power_scale, power_comm current]
      _ = _ := by rw [h.mechanicalBalance, power_add, power_at_impedance, power_scale]
  have cavityPower : count * (area * rmsPower pressure velocity) =
      admittance.re * rmsPower pressure pressure := by
    calc
      _ = rmsPower (((count * area : ℝ) : ℂ) * velocity) pressure := by
        rw [power_scale, power_comm pressure]
        ring
      _ = _ := by rw [h.cavityBalance, power_at_impedance]
  calc
    count * rmsPower voltage current =
        count * (electrical.re * rmsPower current current +
          coupling * rmsPower velocity current) := by
      rw [h.electricalBalance, power_add, power_at_impedance, power_scale]
    _ = _ := by rw [mechanicalPower, mul_add, mul_add, cavityPower]; ring

theorem input_power_ge_copper_loss {electrical mechanical admittance : ℂ}
    {count area coupling : ℝ} {voltage current velocity pressure : ℂ}
    (h : Equations electrical mechanical admittance count area coupling
      voltage current velocity pressure)
    (hc : 0 ≤ count) (hm : 0 ≤ mechanical.re) (ha : 0 ≤ admittance.re) :
    count * electrical.re * rmsPower current current ≤ count * rmsPower voltage current := by
  rw [power_balance h]
  have loss₁ := mul_nonneg (mul_nonneg hc hm) (self_power_nonnegative velocity)
  have loss₂ := mul_nonneg ha (self_power_nonnegative pressure)
  exact le_trans (le_add_of_nonneg_right loss₁) (le_add_of_nonneg_right loss₂)

def mechanicalNumerator (mechanical admittance : ℂ) (count area : ℝ) : ℂ :=
  mechanical * admittance + (count * area ^ 2 : ℝ)

def denominator (electrical mechanical admittance : ℂ) (count area coupling : ℝ) : ℂ :=
  electrical * mechanicalNumerator mechanical admittance count area +
    ((coupling ^ 2 : ℝ) : ℂ) * admittance

private theorem zero_drive {electrical mechanical admittance : ℂ} {count area coupling : ℝ}
    {current velocity pressure : ℂ}
    (h : Equations electrical mechanical admittance count area coupling
      0 current velocity pressure)
    (hc : 0 < count) (he : 0 < electrical.re) (hm : 0 < mechanical.re)
    (hy : 0 ≤ admittance.re) :
    current = 0 ∧ velocity = 0 := by
  have energy := power_balance h
  have zeroInput : rmsPower 0 current = 0 := by simp [rmsPower]
  rw [zeroInput, mul_zero] at energy
  have electricalLoss := mul_nonneg (mul_nonneg hc.le he.le) (self_power_nonnegative current)
  have mechanicalLoss := mul_nonneg (mul_nonneg hc.le hm.le) (self_power_nonnegative velocity)
  have cavityLoss := mul_nonneg hy (self_power_nonnegative pressure)
  constructor
  · by_contra nonzero
    have positiveLoss := mul_pos (mul_pos hc he) (self_power_positive nonzero)
    linarith
  · by_contra nonzero
    have positiveLoss := mul_pos (mul_pos hc hm) (self_power_positive nonzero)
    linarith

private theorem mechanical_numerator_ne_zero {mechanical admittance : ℂ} {count area : ℝ}
    (hc : 0 < count) (hs : area ≠ 0) (hm : 0 < mechanical.re)
    (hy : 0 ≤ admittance.re) :
    mechanicalNumerator mechanical admittance count area ≠ 0 := by
  intro zeroNumerator
  have h : Equations 1 mechanical admittance count area 0
      0 0 admittance ((count * area : ℝ) : ℂ) := by
    refine ⟨by simp, ?_, mul_comm _ _⟩
    simp only [Complex.ofReal_zero, zero_mul]
    symm
    calc
      _ = mechanicalNumerator mechanical admittance count area := by
        simp only [mechanicalNumerator, Complex.ofReal_mul, Complex.ofReal_pow]
        ring
      _ = 0 := zeroNumerator
  have zeroAdmittance := (zero_drive h hc (by simp) hm hy).2
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero hc.ne' (pow_ne_zero 2 hs))
    (by simpa [mechanicalNumerator, zeroAdmittance] using zeroNumerator)

/-- A passive cabinet with positive copper and mechanical resistances has a
    nonzero cleared denominator, including at a lossless cavity cancellation. -/
theorem passive_denominator_ne_zero {electrical mechanical admittance : ℂ}
    {count area coupling : ℝ} (hc : 0 < count) (hs : area ≠ 0)
    (he : 0 < electrical.re) (hm : 0 < mechanical.re) (hy : 0 ≤ admittance.re) :
    denominator electrical mechanical admittance count area coupling ≠ 0 := by
  intro zeroDenominator
  let m := mechanicalNumerator mechanical admittance count area
  have h : Equations electrical mechanical admittance count area coupling 0
      m ((coupling : ℂ) * admittance) ((count * area * coupling : ℝ) : ℂ) := by
    constructor
    · symm
      calc
        _ = denominator electrical mechanical admittance count area coupling := by
          simp only [denominator, m, Complex.ofReal_pow]
          ring
        _ = 0 := zeroDenominator
    · simp only [m, mechanicalNumerator, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    · simp only [Complex.ofReal_mul]
      ring
  exact mechanical_numerator_ne_zero hc hs hm hy (zero_drive h hc he hm hy).1

/-- The circuit solver's cleared fractions follow from the circuit equations,
    including at zero total admittance whenever their denominator is nonzero. -/
theorem cleared_solution {electrical mechanical admittance : ℂ} {count area coupling : ℝ}
    {voltage current velocity pressure : ℂ}
    (h : Equations electrical mechanical admittance count area coupling
      voltage current velocity pressure)
    (hd : denominator electrical mechanical admittance count area coupling ≠ 0) :
    velocity = voltage * (coupling : ℂ) * admittance /
        denominator electrical mechanical admittance count area coupling ∧
    current = voltage * mechanicalNumerator mechanical admittance count area /
        denominator electrical mechanical admittance count area coupling := by
  let m := mechanicalNumerator mechanical admittance count area
  have clearedMechanical : (coupling : ℂ) * current * admittance = m * velocity := by
    calc
      _ = (mechanical * velocity + (area : ℂ) * pressure) * admittance := by
        rw [h.mechanicalBalance]
      _ = mechanical * admittance * velocity + (area : ℂ) * (admittance * pressure) := by ring
      _ = _ := by
        rw [← h.cavityBalance]
        simp only [m, mechanicalNumerator, Complex.ofReal_mul, Complex.ofReal_pow]
        ring
  constructor
  · apply (eq_div_iff hd).mpr
    change velocity * (electrical * m + ((coupling ^ 2 : ℝ) : ℂ) * admittance) = _
    rw [Complex.ofReal_pow]
    calc
      _ = electrical * (m * velocity) +
          (coupling : ℂ) * ((coupling : ℂ) * velocity) * admittance := by ring
      _ = (electrical * current + (coupling : ℂ) * velocity) *
          (coupling : ℂ) * admittance := by rw [← clearedMechanical]; ring
      _ = _ := by rw [← h.electricalBalance]
  · apply (eq_div_iff hd).mpr
    change current * (electrical * m + ((coupling ^ 2 : ℝ) : ℂ) * admittance) = voltage * m
    rw [Complex.ofReal_pow]
    calc
      _ = electrical * current * m +
          (coupling : ℂ) * ((coupling : ℂ) * current * admittance) := by ring
      _ = (electrical * current + (coupling : ℂ) * velocity) * m := by
        rw [clearedMechanical]
        ring
      _ = _ := by rw [← h.electricalBalance]

/-- Substituting the cleared fractions into the exact equations also gives a
    solution. The cavity pressure uses the same denominator as the cone flow. -/
theorem cleared_solution_satisfies {electrical mechanical admittance : ℂ}
    {count area coupling : ℝ} (voltage : ℂ)
    (hd : denominator electrical mechanical admittance count area coupling ≠ 0) :
    Equations electrical mechanical admittance count area coupling voltage
      (voltage * mechanicalNumerator mechanical admittance count area /
        denominator electrical mechanical admittance count area coupling)
      (voltage * (coupling : ℂ) * admittance /
        denominator electrical mechanical admittance count area coupling)
      (voltage * ((count * area * coupling : ℝ) : ℂ) /
        denominator electrical mechanical admittance count area coupling) := by
  constructor
  · field_simp
    simp only [denominator, Complex.ofReal_pow]
  · field_simp
    simp only [mechanicalNumerator, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  · field_simp
    simp only [Complex.ofReal_mul]
    ring

theorem denominator_at_lossless_tuning {electrical mechanical : ℂ}
    {count area coupling : ℝ} (he : electrical ≠ 0) (hc : count ≠ 0) (ha : area ≠ 0) :
    denominator electrical mechanical 0 count area coupling ≠ 0 := by
  simp only [denominator, mechanicalNumerator, mul_zero, zero_add, add_zero]
  exact mul_ne_zero he (Complex.ofReal_ne_zero.mpr (mul_ne_zero hc (pow_ne_zero _ ha)))

theorem rewired_power (voltage current : ℂ) (series parallel : ℝ) :
    rmsPower ((series : ℂ) * voltage) ((parallel : ℂ) * current) =
      (series * parallel) * rmsPower voltage current := by
  rw [power_scale, power_comm voltage, power_scale, power_comm current]
  ring

theorem rewired_impedance (voltage current : ℂ) {series parallel : ℝ}
    (hs : series ≠ 0) (hp : parallel ≠ 0) (hi : current ≠ 0) :
    ((series : ℂ) * voltage) / ((parallel : ℂ) * current) =
      (series : ℂ) ^ 2 / ((series * parallel : ℝ) : ℂ) * (voltage / current) := by
  have hseries := Complex.ofReal_ne_zero.mpr hs
  have hparallel := Complex.ofReal_ne_zero.mpr hp
  rw [Complex.ofReal_mul]
  field_simp

/-- The real part of a real numerator divided by a passive impedance. -/
theorem real_div_nonnegative {z : ℂ} {k : ℝ} (hz : 0 ≤ z.re) (hk : 0 ≤ k) :
    0 ≤ ((k : ℂ) / z).re := by
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg hk hz) (Complex.normSq_nonneg z)

theorem lumped_port_admittance_nonneg {resistance reactance : ℝ} (hr : 0 ≤ resistance) :
    0 ≤ (1 / (⟨resistance, reactance⟩ : ℂ)).re := by
  simpa using real_div_nonnegative (z := ⟨resistance, reactance⟩) hr (zero_le_one (α := ℝ))

theorem terminal_impedance_formula {electrical mechanical admittance : ℂ}
    {count area coupling : ℝ} {voltage current velocity pressure : ℂ}
    (h : Equations electrical mechanical admittance count area coupling
      voltage current velocity pressure)
    (hd : denominator electrical mechanical admittance count area coupling ≠ 0)
    (hv : voltage ≠ 0) (hm : mechanicalNumerator mechanical admittance count area ≠ 0) :
    voltage / current = electrical +
      ((coupling ^ 2 : ℝ) : ℂ) * admittance / mechanicalNumerator mechanical admittance count area := by
  have hc := (cleared_solution h hd).2
  rw [hc]
  rw [div_div_eq_mul_div, mul_div_mul_left _ _ hv]
  rw [denominator, add_div, mul_div_cancel_right₀ _ hm]

theorem coil_loss_rewired (current : ℂ) (series parallel resistance : ℝ) (hp : parallel ≠ 0) :
    ‖(parallel : ℂ) * current / (parallel : ℂ)‖ ^ 2 * resistance * (series * parallel) =
      (series * parallel) * resistance * rmsPower current current := by
  rw [mul_comm (parallel : ℂ), mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hp), pow_two,
    Complex.norm_mul_self_eq_normSq, Complex.normSq_apply, rmsPower]
  ring

/-- Frequency cancels in the ideal inductance-free, mass-controlled pressure. -/
theorem mass_controlled_limit {omega density solidAngle distance area voltage coupling resistance mass : ℝ}
    (hw : 0 < omega) :
    (omega * density / (solidAngle * distance)) * area *
      (voltage * coupling / (resistance * omega * mass)) =
        density * voltage * coupling * area / (resistance * mass * solidAngle * distance) := by
  by_cases hr : resistance = 0
  · simp [hr]
  by_cases hm : mass = 0
  · simp [hm]
  by_cases hs : solidAngle = 0
  · simp [hs]
  by_cases hd : distance = 0
  · simp [hd]
  field_simp [hw.ne', hr, hm, hs, hd]

end Electroacoustics.Circuit
