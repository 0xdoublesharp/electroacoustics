module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Duct

/-- Multiplying cavity/duct admittance cancellation by the impedance numerator
    gives the residual used by the tuning search. -/
def tuningResidual (admittance numerator denominator count : ℝ) : ℝ :=
  admittance * numerator - count * denominator

theorem tuning_residual_zero_iff {admittance numerator denominator count : ℝ}
    (hn : numerator ≠ 0) (hd : denominator ≠ 0) (hc : count ≠ 0) :
    tuningResidual admittance numerator denominator count = 0 ↔
      admittance - 1 / (numerator / denominator / count) = 0 := by
  unfold tuningResidual
  rw [sub_eq_zero, sub_eq_zero]
  rw [eq_div_iff (div_ne_zero (div_ne_zero hn hd) hc)]
  field_simp

theorem pole_is_not_a_tuning {admittance numerator count : ℝ}
    (ha : admittance ≠ 0) (hn : numerator ≠ 0) :
    tuningResidual admittance numerator 0 count ≠ 0 := by
  simpa [tuningResidual] using mul_ne_zero ha hn

structure Bracket where
  low : ℝ
  high : ℝ

def Bracket.Valid (residual : ℝ → ℝ) (bracket : Bracket) : Prop :=
  bracket.low ≤ bracket.high ∧ residual bracket.low < 0 ∧ 0 ≤ residual bracket.high

def Bracket.width (bracket : Bracket) : ℝ := bracket.high - bracket.low

def bisect (residual : ℝ → ℝ) (bracket : Bracket) : Bracket :=
  let mid := (bracket.low + bracket.high) / 2
  if 0 ≤ residual mid then ⟨bracket.low, mid⟩ else ⟨mid, bracket.high⟩

theorem bisect_preserves_bracket {residual : ℝ → ℝ} {bracket : Bracket}
    (valid : bracket.Valid residual) :
    (bisect residual bracket).Valid residual ∧
      (bisect residual bracket).width = bracket.width / 2 := by
  obtain ⟨ordered, lowNegative, highNonnegative⟩ := valid
  by_cases nonnegative : 0 ≤ residual ((bracket.low + bracket.high) / 2)
  · simp only [bisect, ite_eq_left nonnegative, Bracket.Valid, Bracket.width]
    exact ⟨⟨by linarith, lowNegative, nonnegative⟩, by ring⟩
  · simp only [bisect, ite_eq_right nonnegative, Bracket.Valid, Bracket.width]
    exact ⟨⟨by linarith, lt_of_not_ge nonnegative, highNonnegative⟩, by ring⟩

def bisectSteps (residual : ℝ → ℝ) : Nat → Bracket → Bracket
  | 0, bracket => bracket
  | n + 1, bracket => bisect residual (bisectSteps residual n bracket)

theorem bisect_steps_preserve_bracket {residual : ℝ → ℝ} {bracket : Bracket}
    (valid : bracket.Valid residual) (steps : Nat) :
    (bisectSteps residual steps bracket).Valid residual ∧
      (bisectSteps residual steps bracket).width = bracket.width / 2 ^ steps := by
  induction steps with
  | zero => simpa [bisectSteps] using valid
  | succ n ih =>
    obtain ⟨preserved, width⟩ := bisect_preserves_bracket ih.1
    refine ⟨preserved, ?_⟩
    rw [bisectSteps, width, ih.2, pow_succ, div_div]

/-- A continuous cleared residual with a sign-changing, pole-free bracket
    has a physical tuning. Excluding zeros below the bracket places the first
    positive physical tuning in the bracket. -/
theorem first_tuning_of_exclusion {residual denominator : ℝ → ℝ} {bracket : Bracket}
    (valid : bracket.Valid residual) (positive : 0 < bracket.low)
    (continuous : Continuous residual)
    (poleFree : ∀ f ∈ Set.Icc bracket.low bracket.high, denominator f ≠ 0)
    (earlier : ∀ f, 0 < f → f < bracket.low → residual f ≠ 0) :
    ∃ f ∈ Set.Icc bracket.low bracket.high, 0 < f ∧ residual f = 0 ∧ denominator f ≠ 0 ∧
      ∀ g, 0 < g → residual g = 0 → denominator g ≠ 0 → f ≤ g := by
  let roots := Set.Icc bracket.low bracket.high ∩ residual ⁻¹' ({0} : Set ℝ)
  obtain ⟨w, inBand, zero⟩ := intermediate_value_Icc valid.1 continuous.continuousOn
    (show 0 ∈ Set.Icc (residual bracket.low) (residual bracket.high) from ⟨valid.2.1.le, valid.2.2⟩)
  have compact : IsCompact roots :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage continuous)
  obtain ⟨f, least⟩ := compact.exists_isLeast ⟨w, inBand, zero⟩
  have membership : f ∈ Set.Icc bracket.low bracket.high ∧ residual f = 0 := least.1
  refine ⟨f, membership.1, positive.trans_le membership.1.1, membership.2, poleFree f membership.1, ?_⟩
  intro g gPos gZero _
  have gLo : bracket.low ≤ g := le_of_not_gt fun h => earlier g gPos h gZero
  by_cases h : g ≤ bracket.high
  · exact least.2 ⟨⟨gLo, h⟩, gZero⟩
  · exact membership.1.2.trans (le_of_not_ge h)

/-- A position enclosure in each section covers the interior and both ends.
    The witness position gives the lower side of the peak bracket. -/
theorem peak_of_position_cover {Section : Type} (speed : Section → ℝ → ℝ)
    (spans : Section → List (ℝ × ℝ × ℝ)) (upper lower : ℝ)
    (cover : ∀ s x, x ∈ Set.Icc (0 : ℝ) 1 →
      ∃ span ∈ spans s, x ∈ Set.Icc span.1 span.2.1)
    (bounds : ∀ s span, span ∈ spans s → ∀ x ∈ Set.Icc span.1 span.2.1, speed s x ≤ span.2.2)
    (ceilings : ∀ s span, span ∈ spans s → span.2.2 ≤ upper)
    (witness : ∃ s x, x ∈ Set.Icc (0 : ℝ) 1 ∧ lower ≤ speed s x) :
    (∀ s x, x ∈ Set.Icc (0 : ℝ) 1 → speed s x ≤ upper) ∧
      (∃ s x, x ∈ Set.Icc (0 : ℝ) 1 ∧ lower ≤ speed s x) := by
  refine ⟨?_, witness⟩
  intro s x hx
  obtain ⟨span, member, within⟩ := cover s x hx
  exact (bounds s span member x within).trans (ceilings s span member)

/-- Position intervals cover each section at every frequency in a closed
    span. A fixed position with a uniform lower bound witnesses the peak
    from below at each frequency, including a chosen band witness. -/
theorem peak_of_frequency_position_cover {Section : Type} (speed : ℝ → Section → ℝ → ℝ)
    (lo hi : ℝ) (spans : Section → List (ℝ × ℝ × ℝ)) (upper lower : ℝ)
    (cover : ∀ s x, x ∈ Set.Icc (0 : ℝ) 1 →
      ∃ span ∈ spans s, x ∈ Set.Icc span.1 span.2.1)
    (bounds : ∀ f ∈ Set.Icc lo hi, ∀ s span, span ∈ spans s →
      ∀ x ∈ Set.Icc span.1 span.2.1, speed f s x ≤ span.2.2)
    (ceilings : ∀ s span, span ∈ spans s → span.2.2 ≤ upper)
    (witness : ∃ s x, x ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ f ∈ Set.Icc lo hi, lower ≤ speed f s x) :
    ∀ f ∈ Set.Icc lo hi, (∀ s x, x ∈ Set.Icc (0 : ℝ) 1 → speed f s x ≤ upper) ∧
      (∃ s x, x ∈ Set.Icc (0 : ℝ) 1 ∧ lower ≤ speed f s x) := by
  intro f hf
  obtain ⟨s, x, hx, h⟩ := witness
  exact peak_of_position_cover (speed f) spans upper lower cover (bounds f hf) ceilings
    ⟨s, x, hx, h f hf⟩

/-- A finite negative cover excludes earlier positive roots and certifies the low endpoint. -/
theorem earlier_exclusion_of_cover (residual : ℝ → ℝ) {low : ℝ} (lowNonnegative : 0 ≤ low)
    (spans : List Bracket)
    (cover : ∀ f ∈ Set.Icc 0 low, ∃ s ∈ spans, f ∈ Set.Icc s.low s.high)
    (negative : ∀ s ∈ spans, ∀ f ∈ Set.Icc s.low s.high, residual f < 0) :
    (∀ f, 0 < f → f < low → residual f ≠ 0) ∧ residual low < 0 := by
  have negativeOnCover : ∀ f ∈ Set.Icc 0 low, residual f < 0 := by
    intro f within
    obtain ⟨s, member, inSpan⟩ := cover f within
    exact negative s member f inSpan
  exact ⟨fun f positive earlier => (negativeOnCover f ⟨positive.le, earlier.le⟩).ne,
    negativeOnCover low ⟨lowNonnegative, le_rfl⟩⟩

/-- The certified bracket contains the unique least positive tuning with a nonzero denominator. -/
theorem first_tuning_of_cover_certificate {residual denominator : ℝ → ℝ} {bracket : Bracket}
    (ordered : bracket.low ≤ bracket.high) (positive : 0 < bracket.low)
    (highNonnegative : 0 ≤ residual bracket.high) (continuous : Continuous residual)
    (poleFree : ∀ f ∈ Set.Icc bracket.low bracket.high, denominator f ≠ 0)
    (spans : List Bracket)
    (cover : ∀ f ∈ Set.Icc 0 bracket.low, ∃ s ∈ spans, f ∈ Set.Icc s.low s.high)
    (negative : ∀ s ∈ spans, ∀ f ∈ Set.Icc s.low s.high, residual f < 0) :
    ∃! f, f ∈ Set.Icc bracket.low bracket.high ∧ 0 < f ∧ residual f = 0 ∧
      denominator f ≠ 0 ∧ ∀ g, 0 < g → residual g = 0 → denominator g ≠ 0 → f ≤ g := by
  obtain ⟨earlier, lowNegative⟩ := earlier_exclusion_of_cover residual positive.le spans cover negative
  obtain ⟨f, within, fPos, fRoot, fPhysical, fLeast⟩ := first_tuning_of_exclusion
    ⟨ordered, lowNegative, highNonnegative⟩ positive continuous poleFree earlier
  refine ⟨f, ⟨within, fPos, fRoot, fPhysical, fLeast⟩, ?_⟩
  rintro g ⟨_, gPos, gRoot, gPhysical, gLeast⟩
  exact le_antisymm (gLeast f fPos fRoot fPhysical) (fLeast g gPos gRoot gPhysical)

/-- A positive common normalization preserves both sides of the spatial peak certificate. -/
theorem peak_velocity_certificate_sound {Section : Type} (flow area : Section → ℝ → ℝ)
    {d count rawUpper rawLower : ℝ} (hd : d ≠ 0) (hc : 0 < count)
    (spans : Section → List (ℝ × ℝ × ℝ))
    (cover : ∀ s x, x ∈ Set.Icc (0 : ℝ) 1 →
      ∃ span ∈ spans s, x ∈ Set.Icc span.1 span.2.1)
    (bounds : ∀ s span, span ∈ spans s → ∀ x ∈ Set.Icc span.1 span.2.1,
      |flow s x| / area s x ≤ span.2.2)
    (ceilings : ∀ s span, span ∈ spans s → span.2.2 ≤ rawUpper)
    (witness : ∃ s x, x ∈ Set.Icc (0 : ℝ) 1 ∧ rawLower ≤ |flow s x| / area s x) :
    (∀ s x, x ∈ Set.Icc (0 : ℝ) 1 →
      |flow s x| / (area s x * |d| * count) ≤ rawUpper / (|d| * count)) ∧
    (∃ s x, x ∈ Set.Icc (0 : ℝ) 1 ∧
      rawLower / (|d| * count) ≤ |flow s x| / (area s x * |d| * count)) := by
  obtain ⟨upper, s, x, hx, lower⟩ := peak_of_position_cover
    (fun s x => |flow s x| / area s x) spans rawUpper rawLower cover bounds ceilings witness
  have normalization := mul_pos (abs_pos.mpr hd) hc
  refine ⟨?_, ⟨s, x, hx, ?_⟩⟩
  · intro s x hx
    rw [mul_assoc, ← div_div]
    exact div_le_div_of_nonneg_right (upper s x hx) normalization.le
  · rw [mul_assoc, ← div_div (|flow s x|) (area s x)]
    exact div_le_div_of_nonneg_right lower normalization.le

end Electroacoustics.Duct
