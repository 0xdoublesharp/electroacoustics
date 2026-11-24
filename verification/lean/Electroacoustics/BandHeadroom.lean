module

public import Electroacoustics.Operating
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

@[expose] public noncomputable section

namespace Electroacoustics.BandHeadroom

open Electroacoustics.Operating

/-- A constraint's utilization is its fraction of the rating per input volt.
    For copper loss this is the square root of the power fraction. -/
theorem utilization_iff_allows {limit : Limit} (valid : limit.Valid)
    {drive : ℝ} (nonnegative : 0 ≤ drive) :
    drive * (1 / limit.bound) ≤ 1 ↔ limit.Allows drive := by
  rw [Limit.allows_iff_le_bound valid nonnegative, mul_one_div,
    div_le_iff₀ (Limit.bound_pos valid), one_mul]

structure Span where
  left : ℝ
  right : ℝ
  ceiling : ℝ

def Span.Contains (span : Span) (frequency : ℝ) : Prop :=
  span.left ≤ frequency ∧ frequency ≤ span.right

def Feasible {Factor : Type} (band : Span) (usage : ℝ → Factor → ℝ) (drive : ℝ) : Prop :=
  ∀ f, band.Contains f → ∀ factor, drive * usage f factor ≤ 1

/-- Splitting an interval at a real midpoint retains every frequency, including
    the split point. The children may use independently computed ceilings. -/
theorem split_covers (span : Span) (middle leftBound rightBound : ℝ)
    {f : ℝ} (inSpan : span.Contains f) :
    (Span.mk span.left middle leftBound).Contains f ∨
      (Span.mk middle span.right rightBound).Contains f := by
  exact (le_total f middle).imp (fun h => ⟨inSpan.1, h⟩) (fun h => ⟨h, inSpan.2⟩)

/-- Nonnegative bounds on individual responses and DSP gain bound the largest
    filtered utilization, even when different factors dominate at different frequencies. -/
theorem filtered_usage_le {response gain responseUpper gainUpper : ℝ}
    (responseLe : response ≤ responseUpper) (gainLe : gain ≤ gainUpper)
    (responseUpperNonneg : 0 ≤ responseUpper) (gainNonneg : 0 ≤ gain) :
    gain * response ≤ gainUpper * responseUpper := by
  exact (mul_le_mul_of_nonneg_left responseLe gainNonneg).trans
    (mul_le_mul_of_nonneg_right gainLe responseUpperNonneg)

/-- The reciprocal of the largest certified interval ceiling is feasible
    over the entire band. Any downward rounding of it is feasible as well. -/
theorem safe_of_cover {Factor : Type} (band : Span) (usage : ℝ → Factor → ℝ)
    (spans : List Span) (cover : ∀ f, band.Contains f → ∃ s ∈ spans, s.Contains f)
    (bounds : ∀ s ∈ spans, ∀ f, s.Contains f → ∀ k, usage f k ≤ s.ceiling)
    {ceiling drive : ℝ} (positive : 0 < ceiling) (combined : ∀ s ∈ spans, s.ceiling ≤ ceiling)
    (nonnegative : 0 ≤ drive) (driveLe : drive ≤ 1 / ceiling) :
    Feasible band usage drive := by
  intro f inBand factor
  obtain ⟨s, member, inSpan⟩ := cover f inBand
  exact (mul_le_mul_of_nonneg_left
    ((bounds s member f inSpan factor).trans (combined s member)) nonnegative).trans
    ((le_div_iff₀ positive).mp driveLe)

/-- A lower bound at a single witness frequency gives an upper ceiling on any
    feasible voltage. The witness need not be the true worst frequency. -/
theorem infeasible_above_witness {Factor : Type} (band : Span) (usage : ℝ → Factor → ℝ)
    {f : ℝ} (inBand : band.Contains f) (factor : Factor)
    {witness upper drive : ℝ} (positive : 0 < witness) (witnessLe : witness ≤ usage f factor)
    (upperGe : 1 / witness ≤ upper) (above : upper < drive) :
    ¬ Feasible band usage drive := by
  intro feasible
  have exceeds := (div_lt_iff₀ positive).mp (upperGe.trans_lt above)
  have drivePositive : 0 ≤ drive := (show 0 < 1 / witness by positivity).le.trans
    (upperGe.trans above.le)
  exact (not_lt_of_ge (feasible f inBand factor)) (exceeds.trans_le
    (mul_le_mul_of_nonneg_left witnessLe drivePositive))

/-- The relative voltage excess bounds the exact dB gap from the safe voltage
    to any feasible voltage below the upper endpoint. -/
theorem db_gap_le {safe drive upper : ℝ} (safePos : 0 < safe)
    (drivePos : 0 < drive) (driveLe : drive ≤ upper) :
    20 / Real.log 10 * Real.log (drive / safe) ≤
      20 / Real.log 10 * (upper / safe - 1) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Real.log_le_sub_one_of_pos (div_pos drivePos safePos)).trans
    (sub_le_sub_right ((div_le_div_iff_of_pos_right safePos).mpr driveLe) 1)

/-- The safe endpoint remains feasible when the solver stops above its dB tolerance. -/
theorem partial_safe_of_cover {Factor : Type} (band : Span) (usage : ℝ → Factor → ℝ)
    (spans : List Span) (cover : ∀ f, band.Contains f → ∃ s ∈ spans, s.Contains f)
    (bounds : ∀ s ∈ spans, ∀ f, s.Contains f → ∀ k, usage f k ≤ s.ceiling)
    {ceiling safe : ℝ} (positive : 0 < ceiling) (combined : ∀ s ∈ spans, s.ceiling ≤ ceiling)
    (safeNonnegative : 0 ≤ safe) (safeLe : safe ≤ 1 / ceiling) :
    Feasible band usage safe :=
  safe_of_cover band usage spans cover bounds positive combined safeNonnegative safeLe

/-- The upper endpoint remains valid when the solver stops above its dB tolerance. -/
theorem partial_upper_of_witness {Factor : Type} (band : Span) (usage : ℝ → Factor → ℝ)
    {f : ℝ} (inBand : band.Contains f) (factor : Factor)
    {witness upper : ℝ} (positive : 0 < witness) (witnessLe : witness ≤ usage f factor)
    (upperGe : 1 / witness ≤ upper) :
    ∀ drive > upper, ¬ Feasible band usage drive :=
  fun _ above => infeasible_above_witness band usage inBand factor positive witnessLe upperGe above

theorem unresolved_partition (band : Span) (spans : List Span) (isAccepted : Span → Bool)
    (cover : ∀ f, band.Contains f → ∃ s ∈ spans, s.Contains f) :
    ∀ f, band.Contains f →
      (∃ s ∈ spans.filter isAccepted, s.Contains f) ∨
      (∃ s ∈ spans.filter (fun s => !isAccepted s), s.Contains f) := by
  intro f inBand
  obtain ⟨s, member, inSpan⟩ := cover f inBand
  cases accepted : isAccepted s with
  | true => exact Or.inl ⟨s, List.mem_filter.mpr ⟨member, accepted⟩, inSpan⟩
  | false => exact Or.inr ⟨s, List.mem_filter.mpr ⟨member, by simp [accepted]⟩, inSpan⟩

end Electroacoustics.BandHeadroom
