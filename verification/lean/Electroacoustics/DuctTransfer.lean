module

public import Electroacoustics.Radiator
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.DuctTransfer

/-- The actual pressure/flow matrix has imaginary off-diagonal entries `i*b` and `i*c`. -/
structure Transfer where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def Transfer.det (m : Transfer) : ℝ := m.a * m.d + m.b * m.c

def cascade (m s : Transfer) : Transfer :=
  ⟨m.a * s.a - m.b * s.c, m.a * s.b + m.b * s.d,
    m.c * s.a + m.d * s.c, m.d * s.d - m.c * s.b⟩

/-- The section coefficients use the area ratio, endpoint log-area gradients,
    and characteristic scale from `sectionMatrix`. `q2` can be negative. -/
def sectionTransfer (ratio g0 g1 q2 scale C S : ℝ) : Transfer :=
  ⟨ratio * (C - g1 * S), scale * S,
    ((q2 + g0 * g1) * S + (g1 - g0) * C) / scale, (C + g0 * S) / ratio⟩

theorem section_determinant (ratio g0 g1 q2 scale C S : ℝ)
    (hr : ratio ≠ 0) (hs : scale ≠ 0) :
    (sectionTransfer ratio g0 g1 q2 scale C S).det = C ^ 2 + q2 * S ^ 2 := by
  unfold Transfer.det sectionTransfer
  dsimp
  field_simp
  ring

/-- Applies to straight, conical, and above-cutoff exponential sections. -/
theorem propagating_determinant (ratio g0 g1 scale q length : ℝ)
    (hr : ratio ≠ 0) (hs : scale ≠ 0) (hq : q ≠ 0) :
    (sectionTransfer ratio g0 g1 (q ^ 2) scale (Real.cos (q * length))
      (Real.sin (q * length) / q)).det = 1 := by
  rw [section_determinant _ _ _ _ _ _ _ hr hs, div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hq)]
  linarith [Real.sin_sq_add_cos_sq (q * length)]

/-- The hyperbolic branch of an exponential section is also lossless. -/
theorem evanescent_determinant (ratio g0 g1 scale q length : ℝ)
    (hr : ratio ≠ 0) (hs : scale ≠ 0) (hq : q ≠ 0) :
    (sectionTransfer ratio g0 g1 (-(q ^ 2)) scale (Real.cosh (q * length))
      (Real.sinh (q * length) / q)).det = 1 := by
  rw [section_determinant _ _ _ _ _ _ _ hr hs, div_pow, neg_mul,
    mul_div_cancel₀ _ (pow_ne_zero 2 hq)]
  linarith [Real.cosh_sq_sub_sinh_sq (q * length)]

theorem cutoff_determinant (ratio g0 g1 scale length : ℝ) (hr : ratio ≠ 0) (hs : scale ≠ 0) :
    (sectionTransfer ratio g0 g1 0 scale 1 length).det = 1 := by
  rw [section_determinant _ _ _ _ _ _ _ hr hs]
  simp

theorem cascade_determinant (m s : Transfer) : (cascade m s).det = m.det * s.det := by
  unfold cascade Transfer.det
  ring

/-- Dividing pressure by angular frequency keeps the transfer algebra
    unchanged at positive frequencies and removes the DC singular scale. -/
theorem section_normalized_pressure (ratio g0 g1 q2 acoustic C S omega pressure flow : ℝ)
    (omegaNonzero : omega ≠ 0) (acousticNonzero : acoustic ≠ 0) :
    let original := sectionTransfer ratio g0 g1 q2 (omega * acoustic) C S
    let normalized := sectionTransfer ratio g0 g1 q2 acoustic C S
    (original.a * (omega * pressure) + original.b * flow) / omega =
      normalized.a * pressure + normalized.b * flow ∧
    original.d * flow - original.c * (omega * pressure) =
      normalized.d * flow - normalized.c * pressure := by
  dsimp [sectionTransfer]
  constructor <;> field_simp

theorem cascade_unit_determinant (sections : List Transfer) (m : Transfer)
    (hm : m.det = 1) (hs : ∀ s ∈ sections, s.det = 1) :
    (sections.foldl cascade m).det = 1 := by
  induction sections generalizing m with
  | nil => exact hm
  | cons head tail ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [cascade_determinant, hm, hs head List.mem_cons_self, mul_one]
    · intro s member
      exact hs s (List.mem_cons_of_mem _ member)

def pressureAtInlet (m : Transfer) (pressure flow : ℂ) : ℂ :=
  (m.a : ℂ) * pressure + (m.b : ℂ) * Complex.I * flow

def flowAtInlet (m : Transfer) (pressure flow : ℂ) : ℂ :=
  (m.c : ℂ) * Complex.I * pressure + (m.d : ℂ) * flow

theorem transfer_power (m : Transfer) (pressure flow : ℂ) :
    Circuit.rmsPower (pressureAtInlet m pressure flow) (flowAtInlet m pressure flow) =
      m.det * Circuit.rmsPower pressure flow := by
  simp only [Circuit.rmsPower, pressureAtInlet, flowAtInlet, Transfer.det,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- In exact arithmetic an inertively terminated unit-determinant duct cannot have a
    zero input-flow denominator and a zero pressure numerator at the same frequency. -/
theorem inertive_termination_no_common_zero (m : Transfer) (x : ℝ) (hm : m.det = 1)
    (pole : m.d - m.c * x = 0) : m.a * x + m.b ≠ 0 := by
  intro zero
  have hd : m.d = m.c * x := sub_eq_zero.mp pole
  have hb : m.b = -(m.a * x) := by linarith
  unfold Transfer.det at hm
  rw [hd, hb] at hm
  linarith [show m.a * (m.c * x) + -(m.a * x) * m.c = 0 by ring]

/-- Scale the duct state to unit flow at one mouth. The cavity pressure is
    branch impedance numerator times that mouth flow, and the total throat
    flow equals the normalized throat term times that same flow. -/
def ductCabinet (electrical mechanical cavity : ℂ) (count area coupling resistance throat reactance : ℝ) :
    Radiator.Cabinet :=
  ⟨electrical, mechanical, cavity, ⟨resistance * throat, reactance⟩, count, area, coupling, throat, 1⟩

theorem cleared_duct_satisfies (electrical mechanical cavity drive : ℂ)
    (count area coupling resistance throat reactance : ℝ)
    (hd : Radiator.clearedDenominator
      (ductCabinet electrical mechanical cavity count area coupling resistance throat reactance) ≠ 0) :
    let cabinet := ductCabinet electrical mechanical cavity count area coupling resistance throat reactance
    let solution := Radiator.solve cabinet drive
    ((count * area : ℝ) : ℂ) * solution.cone =
      cavity * solution.pressure + (throat : ℂ) * solution.radiatorVelocity ∧
    cabinet.radiator * solution.radiatorVelocity = solution.pressure ∧
    solution.radiatorVelocity =
      drive * ((count * area * coupling : ℝ) : ℂ) / Radiator.clearedDenominator cabinet := by
  dsimp only
  have balances := Radiator.solve_satisfies _ drive hd
  refine ⟨?_, ?_, ?_⟩
  · simpa [ductCabinet] using balances.cavity
  · simpa [ductCabinet] using balances.radiator
  · simp [Radiator.solve, ductCabinet]

/-- Signed throat flow enters the real part of the admittance as its square.
    Duct poles therefore retain passivity in the cleared circuit. -/
theorem duct_admittance_nonnegative (resistance throat reactance : ℝ) (hr : 0 ≤ resistance) :
    0 ≤ ((throat : ℂ) / (⟨resistance * throat, reactance⟩ : ℂ)).re := by
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  rw [show throat * (resistance * throat) = resistance * throat ^ 2 by ring]
  exact div_nonneg (mul_nonneg hr (sq_nonneg throat)) (Complex.normSq_nonneg _)

/-- The duct branch can have zero throat flow or zero impedance. The two
    normalized terms cannot vanish together for a unit-determinant transfer. -/
theorem passive_duct_denominator_ne_zero (electrical mechanical cavity : ℂ)
    (count area coupling resistance throat reactance : ℝ) (hc : 0 < count) (ha : area ≠ 0)
    (he : 0 < electrical.re) (hm : 0 < mechanical.re) (hy : 0 ≤ cavity.re)
    (hr : 0 ≤ resistance) (branch : throat ≠ 0 ∨ reactance ≠ 0) :
    Radiator.clearedDenominator
      (ductCabinet electrical mechanical cavity count area coupling resistance throat reactance) ≠ 0 := by
  let z : ℂ := ⟨resistance * throat, reactance⟩
  have admittance :
      Radiator.clearedAdmittance
        (ductCabinet electrical mechanical cavity count area coupling resistance throat reactance) =
        cavity * z + (throat : ℂ) := by
    simp [Radiator.clearedAdmittance, Radiator.radiatorAreaTerm, ductCabinet, z]
  by_cases hz : z = 0
  · have ht : (throat : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      exact branch.resolve_right (by simpa [z] using congrArg Complex.im hz)
    have free : electrical * mechanical + ((coupling ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have electricalNonzero : electrical ≠ 0 := by
        intro h
        simp [h] at he
      have loss : 0 ≤ (((coupling ^ 2 : ℝ) : ℂ) / electrical).re := by
        rw [Complex.div_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
        exact div_nonneg (mul_nonneg (sq_nonneg _) he.le) (Complex.normSq_nonneg _)
      have freeLoad : mechanical + ((coupling ^ 2 : ℝ) : ℂ) / electrical ≠ 0 := by
        intro h
        have hreal := congrArg Complex.re h
        simp only [Complex.add_re, Complex.zero_re] at hreal
        linarith
      have factored : electrical * mechanical + ((coupling ^ 2 : ℝ) : ℂ) =
          (mechanical + ((coupling ^ 2 : ℝ) : ℂ) / electrical) * electrical := by
        rw [add_mul, div_mul_cancel₀ _ electricalNonzero, mul_comm mechanical]
      rw [factored]
      exact mul_ne_zero freeLoad electricalNonzero
    have equal : Radiator.clearedDenominator
        (ductCabinet electrical mechanical cavity count area coupling resistance throat reactance) =
        (electrical * mechanical + ((coupling ^ 2 : ℝ) : ℂ)) * (throat : ℂ) := by
      simp only [Radiator.clearedDenominator, Radiator.numerator, admittance]
      change electrical * (mechanical * (cavity * z + (throat : ℂ)) +
        ((count * area ^ 2 : ℝ) : ℂ) * z) +
        ((coupling ^ 2 : ℝ) : ℂ) * (cavity * z + (throat : ℂ)) = _
      simp [hz, add_mul, mul_assoc]
    rw [equal]
    exact mul_ne_zero free ht
  · let y := cavity + (throat : ℂ) / z
    have passivity : 0 ≤ y.re := add_nonneg hy (duct_admittance_nonnegative _ _ _ hr)
    have combined : cavity * z + (throat : ℂ) = y * z := by
      simp only [y, add_mul, div_mul_cancel₀ _ hz]
    have factored : Radiator.clearedDenominator
        (ductCabinet electrical mechanical cavity count area coupling resistance throat reactance) =
        Circuit.denominator electrical mechanical y count area coupling * z := by
      simp only [Radiator.clearedDenominator, Radiator.numerator, admittance, combined,
        Circuit.denominator, Circuit.mechanicalNumerator]
      change electrical * (mechanical * (y * z) + ((count * area ^ 2 : ℝ) : ℂ) * z) +
        ((coupling ^ 2 : ℝ) : ℂ) * (y * z) = _
      ring
    rw [factored]
    exact mul_ne_zero (Circuit.passive_denominator_ne_zero hc ha he hm passivity) hz

/-- With unit flow and zero pressure at the mouth, the uniform duct's
    speed magnitude is bounded everywhere by its attained mouth value. -/
theorem open_uniform_duct_peak (k length area : ℝ) (ha : 0 < area) :
    (∀ x : ℝ, |Real.cos (k * (length - x))| / area ≤ 1 / area) ∧
    |Real.cos (k * (length - length))| / area = 1 / area := by
  constructor
  · intro x
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) ha.le
  · simp

/-- For a uniform open duct without end or junction inertance, `phase = ωL/c`
    and `volumeRatio = cavityVolume / (area * length)`. -/
def straightResidual (volumeRatio count phase : ℝ) : ℝ :=
  volumeRatio * phase * Real.sin phase - count * Real.cos phase

theorem straight_residual_increases_before_first_pole {volumeRatio count : ℝ}
    (hv : 0 < volumeRatio) (hn : 0 < count) :
    StrictMonoOn (straightResidual volumeRatio count) (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx y hy less
  have halfLePi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hxSin : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (hx.2.trans halfLePi)
  have hSin : Real.sin x ≤ Real.sin y := Real.strictMonoOn_sin.monotoneOn
    ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩ ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩ less.le
  have hCos : Real.cos y < Real.cos x := Real.strictAntiOn_cos
    ⟨hx.1, hx.2.trans halfLePi⟩ ⟨hy.1, hy.2.trans halfLePi⟩ less
  have increasing : volumeRatio * x * Real.sin x ≤ volumeRatio * y * Real.sin y := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left less.le hv.le) hSin hxSin
    exact mul_nonneg hv.le hy.1
  unfold straightResidual
  linarith [mul_lt_mul_of_pos_left hCos hn]

theorem straight_unique_tuning_before_first_pole {volumeRatio count : ℝ}
    (hv : 0 < volumeRatio) (hn : 0 < count) :
    ∃! phase, phase ∈ Set.Ioo 0 (Real.pi / 2) ∧ straightResidual volumeRatio count phase = 0 := by
  have h0 : straightResidual volumeRatio count 0 < 0 := by simpa [straightResidual] using hn
  have h1 : 0 < straightResidual volumeRatio count (Real.pi / 2) := by
    simpa [straightResidual, Real.sin_pi_div_two, Real.cos_pi_div_two] using
      mul_pos hv Real.pi_div_two_pos
  have hc : Continuous (straightResidual volumeRatio count) :=
    ((continuous_const.mul continuous_id).mul Real.continuous_sin).sub
      (continuous_const.mul Real.continuous_cos)
  obtain ⟨x, hx, root⟩ := intermediate_value_Icc Real.pi_div_two_pos.le hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (straightResidual volumeRatio count 0)
      (straightResidual volumeRatio count (Real.pi / 2)) from ⟨h0.le, h1.le⟩)
  have inside : x ∈ Set.Ioo 0 (Real.pi / 2) := by
    refine ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
    · intro same
      rw [← same] at root
      exact h0.ne root
    · intro same
      rw [same] at root
      exact h1.ne' root
  refine ⟨x, ⟨inside, root⟩, ?_⟩
  intro y hy
  exact (straight_residual_increases_before_first_pole hv hn).injOn
    ⟨hy.1.1.le, hy.1.2.le⟩ hx (hy.2.trans root.symm)

/-- DC inertance is the integral of reciprocal area along a section. -/
theorem straight_dc_inertance (length area : ℝ) :
    (∫ _ in (0 : ℝ)..length, 1 / area) = length / area := by
  simp [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]

theorem conical_dc_inertance {length rIn rOut : ℝ} (hLength : 0 < length)
    (hIn : 0 < rIn) (hOut : 0 < rOut) :
    (∫ x in (0 : ℝ)..length, 1 / (rIn + (rOut - rIn) * (x / length)) ^ 2) =
      length / (rIn * rOut) ∧
    length / (rIn * rOut) = (length / rIn ^ 2) / Real.sqrt (rOut ^ 2 / rIn ^ 2) := by
  let radius := fun x => rIn + (rOut - rIn) * (x / length)
  let primitive := fun x => x / (rIn * radius x)
  have radiusPos (x : ℝ) (hx : x ∈ Set.uIcc 0 length) : 0 < radius x := by
    rw [Set.uIcc_of_le hLength.le] at hx
    have fractionNonnegative := div_nonneg hx.1 hLength.le
    have complementNonnegative : 0 ≤ 1 - x / length :=
      sub_nonneg.mpr ((div_le_one hLength).mpr hx.2)
    calc
      0 < min rIn rOut := lt_min hIn hOut
      _ = min rIn rOut * (1 - x / length) + min rIn rOut * (x / length) := by ring
      _ ≤ rIn * (1 - x / length) + rOut * (x / length) := add_le_add
        (mul_le_mul_of_nonneg_right (min_le_left _ _) complementNonnegative)
        (mul_le_mul_of_nonneg_right (min_le_right _ _) fractionNonnegative)
      _ = radius x := by dsimp [radius]; ring
  have radiusDerivative (x : ℝ) : HasDerivAt radius ((rOut - rIn) / length) x := by
    have h := (((hasDerivAt_id x).div_const length).const_mul (rOut - rIn)).const_add rIn
    simpa [radius, div_eq_mul_inv] using h
  have derivative (x : ℝ) (hx : x ∈ Set.uIcc 0 length) :
      HasDerivAt primitive (1 / radius x ^ 2) x := by
    have hRadius := (radiusPos x hx).ne'
    have h := HasDerivAt.div (hasDerivAt_id x) ((radiusDerivative x).const_mul rIn)
      (mul_ne_zero hIn.ne' hRadius)
    convert (show HasDerivAt primitive _ x from h) using 1
    change 1 / radius x ^ 2 = (1 * (rIn * radius x) - x * (rIn * ((rOut - rIn) / length))) /
      (rIn * radius x) ^ 2
    rw [show 1 * (rIn * radius x) - x * (rIn * ((rOut - rIn) / length)) = rIn ^ 2 by
      dsimp [radius]
      ring]
    calc
      1 / radius x ^ 2 = (rIn ^ 2 * 1) / (rIn ^ 2 * radius x ^ 2) :=
        (mul_div_mul_left _ _ (pow_ne_zero 2 hIn.ne')).symm
      _ = rIn ^ 2 / (rIn * radius x) ^ 2 := by rw [mul_one, mul_pow]
  have integrable : IntervalIntegrable (fun x => 1 / radius x ^ 2) MeasureTheory.volume 0 length :=
    (continuousOn_const.div (fun x hx => ((radiusDerivative x).continuousAt.continuousWithinAt).pow 2)
      (fun x hx => pow_ne_zero 2 (radiusPos x hx).ne')).intervalIntegrable
  constructor
  · change (∫ x in (0 : ℝ)..length, 1 / radius x ^ 2) = _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt derivative integrable]
    simp [primitive, radius, hLength.ne']
  · rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hOut.le, Real.sqrt_sq hIn.le]
    field_simp

theorem exponential_dc_inertance {length inlet outlet growth : ℝ}
    (hLength : 0 < length) (hIn : 0 < inlet) (hOut : 0 < outlet) (different : inlet ≠ outlet)
    (growthEq : 2 * growth * length = Real.log (outlet / inlet)) :
    (∫ x in (0 : ℝ)..length, 1 / (inlet * Real.exp (2 * growth * x))) =
      (length / inlet) * (1 - inlet / outlet) / Real.log (outlet / inlet) ∧
    (length / inlet) * (1 - inlet / outlet) / Real.log (outlet / inlet) =
      (length / inlet) * (-(Real.exp (-Real.log (outlet / inlet)) - 1) / Real.log (outlet / inlet)) := by
  have hLog := Real.log_ne_zero_of_pos_of_ne_one (div_pos hOut hIn)
    (fun eq => different ((div_eq_one_iff_eq hIn.ne').mp eq).symm)
  have hGrowth : growth ≠ 0 := by
    intro eq
    exact hLog (by simpa [eq] using growthEq.symm)
  have expNegLog : Real.exp (-Real.log (outlet / inlet)) = inlet / outlet := by
    rw [Real.exp_neg, Real.exp_log (div_pos hOut hIn), inv_div]
  let primitive := fun x => Real.exp (-(2 * growth) * x) / (-(2 * growth) * inlet)
  have derivative (x : ℝ) : HasDerivAt primitive (1 / (inlet * Real.exp (2 * growth * x))) x := by
    have h := ((Real.hasDerivAt_exp _).comp x ((hasDerivAt_id x).const_mul (-(2 * growth)))).div_const
      (-(2 * growth) * inlet)
    convert (show HasDerivAt primitive _ x from h) using 1
    dsimp only [id_eq]
    rw [neg_mul, Real.exp_neg]
    have expNonzero := (Real.exp_pos (2 * growth * x)).ne'
    field_simp
  have continuous : Continuous (fun x => 1 / (inlet * Real.exp (2 * growth * x))) :=
    continuous_const.div (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
      (fun _ => mul_ne_zero hIn.ne' (Real.exp_pos _).ne')
  constructor
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => derivative x)
      (continuous.intervalIntegrable _ _)]
    simp only [primitive, neg_mul, growthEq, expNegLog, mul_zero, neg_zero, Real.exp_zero]
    rw [← growthEq]
    field_simp
    ring
  · rw [expNegLog]
    ring

/-- The straight case is also used for equal-area exponential sections at cutoff. -/
inductive DCSection where
  | straight (length area : ℝ)
  | conical (length rIn rOut : ℝ)
  | exponential (length inlet outlet : ℝ)

def DCSection.Valid : DCSection → Prop
  | .straight length area => 0 < length ∧ 0 < area
  | .conical length rIn rOut => 0 < length ∧ 0 < rIn ∧ 0 < rOut
  | .exponential length inlet outlet => 0 < length ∧ 0 < inlet ∧ 0 < outlet

/-- The section contribution to `rawEquivalentLength` divided by the path inlet area. -/
def DCSection.inertance : DCSection → ℝ
  | .straight length area => length / area
  | .conical length rIn rOut => length / (rIn * rOut)
  | .exponential length inlet outlet =>
    if inlet = outlet then length / inlet else
      (length / inlet) * (-(Real.exp (-Real.log (outlet / inlet)) - 1) / Real.log (outlet / inlet))

/-- The normalized section transfer at zero wavenumber. -/
def DCSection.transfer (s : DCSection) (density inertanceFactor : ℝ) : Transfer :=
  let acoustic := density * inertanceFactor
  match s with
  | .straight length area =>
    sectionTransfer 1 0 0 0 (acoustic / Real.sqrt (area * area)) 1 length
  | .conical length rIn rOut =>
    let ratio := rOut / rIn
    let g := (ratio - 1) / length
    sectionTransfer ratio g (g / ratio) 0 (acoustic / Real.sqrt (rIn ^ 2 * rOut ^ 2)) 1 length
  | .exponential length inlet outlet =>
    let ratio := Real.sqrt (outlet / inlet)
    let g := Real.log ratio / length
    sectionTransfer ratio g g (-(g ^ 2)) (acoustic / Real.sqrt (inlet * outlet))
      (Real.cosh (g * length)) (if g = 0 then length else Real.sinh (g * length) / g)

def dcSeries (pressure : ℝ) : Transfer := ⟨1, pressure, 0, 1⟩

private theorem dc_transfer_eq_series (s : DCSection) {density inertanceFactor : ℝ}
    (valid : s.Valid) :
    s.transfer density inertanceFactor = dcSeries (density * inertanceFactor * s.inertance) := by
  cases s with
  | straight length area =>
    obtain ⟨_, ha⟩ := valid
    simp [DCSection.transfer, DCSection.inertance, sectionTransfer, dcSeries,
      ← pow_two area, Real.sqrt_sq ha.le, div_eq_mul_inv, mul_right_comm]
    ring
  | conical length rIn rOut =>
    obtain ⟨hLength, hIn, hOut⟩ := valid
    simp only [DCSection.transfer, DCSection.inertance, sectionTransfer, dcSeries,
      Real.sqrt_mul (sq_nonneg rIn), Real.sqrt_sq hIn.le, Real.sqrt_sq hOut.le,
      Transfer.mk.injEq, zero_add, mul_one]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp [hLength.ne', hIn.ne', hOut.ne'] <;> ring
  | exponential length inlet outlet =>
    obtain ⟨hLength, hIn, hOut⟩ := valid
    by_cases equal : inlet = outlet
    · subst outlet
      simp [DCSection.transfer, DCSection.inertance, sectionTransfer, dcSeries, hIn.ne',
        ← pow_two inlet, Real.sqrt_sq hIn.le, div_eq_mul_inv, mul_right_comm]
      ring
    · let ratio := Real.sqrt (outlet / inlet)
      let g := Real.log ratio / length
      have ratioPos : 0 < ratio := Real.sqrt_pos.2 (div_pos hOut hIn)
      have ratioSq : ratio ^ 2 = outlet / inlet := Real.sq_sqrt (div_nonneg hOut.le hIn.le)
      have ratioNeOne : ratio ≠ 1 := by
        intro eq
        exact equal ((div_eq_one_iff_eq hIn.ne').mp (by simpa [eq] using ratioSq.symm)).symm
      have gNeZero : g ≠ 0 := div_ne_zero (Real.log_ne_zero_of_pos_of_ne_one ratioPos ratioNeOne) hLength.ne'
      have scaleArea : Real.sqrt (inlet * outlet) = inlet * ratio := by
        rw [show inlet * outlet = (inlet * ratio) ^ 2 by
          rw [mul_pow, ratioSq]
          field_simp, Real.sqrt_sq (mul_nonneg hIn.le ratioPos.le)]
      have expPhase : Real.exp (g * length) = ratio := by
        simp [g, hLength.ne', Real.exp_log ratioPos]
      have expNegPhase : Real.exp (-(g * length)) = ratio⁻¹ := by rw [Real.exp_neg, expPhase]
      have growthEq : 2 * g * length = Real.log (outlet / inlet) := by
        rw [← ratioSq, Real.log_pow]
        dsimp [g]
        field_simp
      have expNegLog : Real.exp (-Real.log (outlet / inlet)) = (ratio ^ 2)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (div_pos hOut hIn), ratioSq]
      change sectionTransfer ratio g g (-(g ^ 2)) (density * inertanceFactor / Real.sqrt (inlet * outlet))
        (Real.cosh (g * length)) (if g = 0 then length else Real.sinh (g * length) / g) = _
      simp only [ite_eq_right gNeZero, DCSection.inertance, ite_eq_right equal, sectionTransfer, dcSeries,
        Transfer.mk.injEq]
      have cancel : g * (Real.sinh (g * length) / g) = Real.sinh (g * length) :=
        by rw [← mul_div_assoc, mul_div_cancel_left₀ _ gNeZero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [cancel, Real.cosh_sub_sinh, expNegPhase, mul_inv_cancel₀ ratioPos.ne']
      · rw [scaleArea, Real.sinh_eq, expPhase, expNegPhase, expNegLog, ← growthEq]
        field_simp [ratioPos.ne', gNeZero, hLength.ne', hIn.ne']
        ring
      · simp [pow_two]
      · rw [cancel, Real.cosh_add_sinh, expPhase, div_self ratioPos.ne']

/-- At DC, pressure per angular frequency increases by section inertance times section density. -/
theorem section_dc_normalized_pressure (s : DCSection) (density inertanceFactor pOut : ℝ)
    (valid : s.Valid) :
    let m := s.transfer density inertanceFactor
    (m.a * pOut + m.b * 1, m.d * 1 - m.c * pOut) =
      (pOut + density * inertanceFactor * s.inertance, 1) := by
  dsimp only
  rw [dc_transfer_eq_series s valid]
  simp [dcSeries]

private theorem cascade_dc_series (sections : List DCSection) (density inertanceFactor pressure : ℝ)
    (valid : ∀ s ∈ sections, s.Valid) :
    (sections.map (fun s => s.transfer density inertanceFactor)).foldl cascade (dcSeries pressure) =
      dcSeries (pressure + density * inertanceFactor * (sections.map DCSection.inertance).sum) := by
  induction sections generalizing pressure with
  | nil => simp
  | cons s tail ih =>
    rw [List.map_cons, List.foldl_cons, dc_transfer_eq_series s (valid s List.mem_cons_self)]
    rw [show cascade (dcSeries pressure) (dcSeries (density * inertanceFactor * s.inertance)) =
      dcSeries (pressure + density * inertanceFactor * s.inertance) by simp [cascade, dcSeries, add_comm]]
    rw [ih _ (fun t member => valid t (List.mem_cons_of_mem _ member)), List.map_cons, List.sum_cons]
    congr 1
    ring

/-- Corrected DC pressure per angular frequency is the equivalent length times density per inlet area. -/
theorem cascade_dc_equivalent_length (sections : List DCSection) (density inertanceFactor : ℝ)
    {inletArea mouthArea : ℝ} (inletCorrection outletCorrection : ℝ) (junctions : List ℝ)
    (hInlet : 0 < inletArea) (hMouth : 0 < mouthArea) (valid : ∀ s ∈ sections, s.Valid) :
    let m := (sections.map (fun s => s.transfer density inertanceFactor)).foldl cascade (dcSeries 0)
    let pOut := density * outletCorrection / mouthArea
    let flow := m.d * 1 - m.c * pOut
    let pIn := m.a * pOut + m.b * 1 + density * (inletCorrection + junctions.sum) / inletArea * flow
    let rawEquivalentLength := inletCorrection + outletCorrection * inletArea / mouthArea +
      ((sections.map fun s => inletArea * s.inertance).sum * inertanceFactor) + junctions.sum
    flow = 1 ∧ pIn = density / inletArea * rawEquivalentLength := by
  have scaleSum : (sections.map (fun s => inletArea * s.inertance)).sum =
      inletArea * (sections.map DCSection.inertance).sum := by
    induction sections with
    | nil => simp
    | cons head tail ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
        ih (fun s member => valid s (List.mem_cons_of_mem _ member)), mul_add]
  dsimp only
  rw [cascade_dc_series sections density inertanceFactor 0 valid, scaleSum]
  simp only [dcSeries, zero_add, one_mul, mul_one, zero_mul, sub_zero, true_and]
  field_simp [hInlet.ne', hMouth.ne']
  ring

end Electroacoustics.DuctTransfer
