module

public import Electroacoustics.Circuit
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.MinMax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Summaries

/-- The relative midpoint error for one metric. The scale floor also covers zero metrics. -/
def interpolationError (left mid right : ℝ) : ℝ :=
  let scale := max |left| (max |mid| (max |right| (1 / 10 ^ 12)))
  |mid / scale - (left / scale / 2 + right / scale / 2)|

theorem interpolationError_nonneg (left mid right : ℝ) :
    0 ≤ interpolationError left mid right :=
  abs_nonneg _

theorem interpolationError_zero_of_linear {left mid right : ℝ}
    (linear : mid = (left + right) / 2) : interpolationError left mid right = 0 := by
  rw [linear]
  unfold interpolationError
  apply abs_eq_zero.mpr
  ring

private theorem foldl_max_le {values : List ℝ} {initial bound : ℝ} (hInitial : initial ≤ bound)
    (hValues : ∀ value ∈ values, value ≤ bound) : values.foldl max initial ≤ bound := by
  induction values generalizing initial with
  | nil => exact hInitial
  | cons head tail ih =>
    rw [List.foldl_cons]
    exact ih (max_le hInitial (hValues head List.mem_cons_self))
      (fun value member => hValues value (List.mem_cons_of_mem _ member))

/-- The final intervals are split into accepted intervals and the remaining unresolved intervals. -/
theorem adaptive_accepted_bounds {Interval : Type} (intervals : List Interval)
    (accepted : Interval → Bool) (err : Interval → ℝ) {tol : ℝ} (tolNonnegative : 0 ≤ tol)
    (acceptedBounds : ∀ i ∈ intervals, accepted i = true → err i ≤ tol) :
    let maxAcceptedError := ((intervals.filter accepted).map err).foldl max 0
    let unresolved := (intervals.filter (fun i => !accepted i)).length
    maxAcceptedError ≤ tol ∧ (unresolved = 0 → ∀ i ∈ intervals, err i ≤ tol) := by
  dsimp only
  refine ⟨foldl_max_le tolNonnegative ?_, ?_⟩
  · intro value member
    obtain ⟨i, acceptedMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨inIntervals, isAccepted⟩ := List.mem_filter.mp acceptedMember
    exact acceptedBounds i inIntervals isAccepted
  · intro noneUnresolved i member
    apply acceptedBounds i member
    cases isAccepted : accepted i with
    | true => rfl
    | false =>
      have inUnresolved : i ∈ intervals.filter (fun i => !accepted i) :=
        List.mem_filter.mpr ⟨member, by simp [isAccepted]⟩
      rw [List.length_eq_zero_iff.mp noneUnresolved] at inUnresolved
      exact (List.not_mem_nil inUnresolved).elim

/-- Insert the in-band landmarks exactly, then deduplicate and sort the grid. -/
def landmarkGrid (minHz maxHz : ℝ) (seeds landmarks : List ℝ) : List ℝ :=
  (seeds ++ landmarks.filter (fun f => decide (f ∈ Set.Icc minHz maxHz))).toFinset.sort

theorem grid_endpoints_and_landmarks {minHz maxHz : ℝ} (seeds landmarks : List ℝ)
    (seedBounds : ∀ f ∈ seeds, f ∈ Set.Icc minHz maxHz)
    (minSeed : minHz ∈ seeds) (maxSeed : maxHz ∈ seeds) :
    let grid := landmarkGrid minHz maxHz seeds landmarks
    grid.head? = some minHz ∧ grid.getLast? = some maxHz ∧ grid.SortedLT ∧
      ∀ f ∈ landmarks, f ∈ Set.Icc minHz maxHz → f ∈ grid := by
  let points := (seeds ++ landmarks.filter (fun f => decide (f ∈ Set.Icc minHz maxHz))).toFinset
  have pointMem (f : ℝ) : f ∈ points ↔ f ∈ seeds ∨ f ∈ landmarks ∧ f ∈ Set.Icc minHz maxHz := by
    simp [points]
  have minPoint : minHz ∈ points := (pointMem _).mpr (Or.inl minSeed)
  have maxPoint : maxHz ∈ points := (pointMem _).mpr (Or.inl maxSeed)
  have nonempty : points.Nonempty := ⟨minHz, minPoint⟩
  have inBand (f : ℝ) (member : f ∈ points) : f ∈ Set.Icc minHz maxHz :=
    ((pointMem f).mp member).elim (seedBounds f) And.right
  have minEq : points.min' nonempty = minHz := le_antisymm (points.min'_le _ minPoint)
    (inBand _ (points.min'_mem nonempty)).1
  have maxEq : points.max' nonempty = maxHz := le_antisymm
    (inBand _ (points.max'_mem nonempty)).2 (points.le_max' _ maxPoint)
  have lengthPos : 0 < points.sort.length := by simpa using Finset.card_pos.mpr nonempty
  change points.sort.head? = _ ∧ points.sort.getLast? = _ ∧ points.sort.SortedLT ∧ _
  refine ⟨?_, ?_, points.sortedLT_sort, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem lengthPos,
      ← Finset.min'_eq_sorted_zero (h := nonempty), minEq]
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (Nat.sub_lt lengthPos Nat.zero_lt_one),
      ← Finset.max'_eq_sorted_last (h := nonempty), maxEq]
  · intro f member within
    exact (Finset.mem_sort _).mpr ((pointMem f).mpr (Or.inr ⟨member, within⟩))

/-- The phasor magnitude law applies to pressure, current, and each volume flow. -/
theorem filtered_phasor_scaling (H voltage current : ℂ) (resistance : ℝ) :
    (∀ phasor : ℂ, ‖phasor * H‖ = ‖phasor‖ * ‖H‖) ∧
    Circuit.rmsPower (voltage * H) (current * H) = ‖H‖ ^ 2 * Circuit.rmsPower voltage current ∧
    ‖current * H‖ ^ 2 * resistance = ‖H‖ ^ 2 * (‖current‖ ^ 2 * resistance) ∧
    (H ≠ 0 → current ≠ 0 → voltage * H / (current * H) = voltage / current) := by
  refine ⟨fun phasor => norm_mul phasor H, ?_, ?_, ?_⟩
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Circuit.rmsPower, Complex.mul_re, Complex.mul_im]
    ring
  · rw [norm_mul, mul_pow]
    ring
  · intro hH hCurrent
    field_simp

def wrappedPhase (delta : ℝ) : ℝ := Complex.arg ⟨Real.cos delta, Real.sin delta⟩

private theorem wrappedPhase_eq_mod (delta : ℝ) :
    wrappedPhase delta = toIocMod Real.two_pi_pos (-Real.pi) delta := by
  have phasor : (⟨Real.cos delta, Real.sin delta⟩ : ℂ) =
      (Real.cos delta : ℂ) + (Real.sin delta : ℂ) * Complex.I := by
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add]
  rw [wrappedPhase, phasor]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_cos_add_sin_mul_I_eq_toIocMod delta

theorem wrap_phase_exact {delta : ℝ} (within : |delta| < Real.pi) :
    Complex.arg ⟨Real.cos delta, Real.sin delta⟩ = delta := by
  change wrappedPhase delta = delta
  rw [wrappedPhase_eq_mod, toIocMod_eq_self, show -Real.pi + 2 * Real.pi = Real.pi by ring]
  exact ⟨(abs_lt.mp within).1, (abs_lt.mp within).2.le⟩

private theorem wrappedPhase_sub (left right : ℝ) :
    wrappedPhase (wrappedPhase right - wrappedPhase left) = wrappedPhase (right - left) := by
  simp only [wrappedPhase_eq_mod]
  apply (toIocMod_eq_toIocMod Real.two_pi_pos).mpr
  refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) right - toIocDiv Real.two_pi_pos (-Real.pi) left, ?_⟩
  rw [sub_smul, ← self_sub_toIocMod Real.two_pi_pos (-Real.pi) right,
    ← self_sub_toIocMod Real.two_pi_pos (-Real.pi) left]
  ring

theorem group_delay_linear_phase (phase₀ τ : ℝ) {f₁ f₂ : ℝ} (ordered : f₁ < f₂)
    (noAlias : 2 * Real.pi * (f₂ - f₁) * |τ| < Real.pi) :
    let phase := fun f : ℝ => phase₀ - 2 * Real.pi * f * τ
    let delta := wrappedPhase (phase f₂) - wrappedPhase (phase f₁)
    (-1000) * wrappedPhase delta / (2 * Real.pi * (f₂ - f₁)) = 1000 * τ := by
  dsimp only
  rw [wrappedPhase_sub]
  rw [show phase₀ - 2 * Real.pi * f₂ * τ - (phase₀ - 2 * Real.pi * f₁ * τ) =
    -(2 * Real.pi * (f₂ - f₁) * τ) by ring]
  have width : 0 < f₂ - f₁ := sub_pos.mpr ordered
  have within : |-(2 * Real.pi * (f₂ - f₁) * τ)| < Real.pi := by
    rwa [abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi * (f₂ - f₁))]
  rw [show wrappedPhase _ = _ from wrap_phase_exact within]
  have piNonzero := Real.pi_ne_zero
  field_simp

theorem weighted_two_sided_delay_exact_quadratic (a b c : ℝ) {f₀ f₁ f₂ : ℝ}
    (ordered₁ : f₀ < f₁) (ordered₂ : f₁ < f₂) :
    let phase := fun f : ℝ => a * f ^ 2 + b * f + c
    let w₁ := f₁ - f₀
    let w₂ := f₂ - f₁
    let s₁ := (phase f₁ - phase f₀) / w₁
    let s₂ := (phase f₂ - phase f₁) / w₂
    (s₁ * w₂ + s₂ * w₁) / (w₁ + w₂) = 2 * a * f₁ + b := by
  have hw₁ := (sub_pos.mpr ordered₁).ne'
  have hw₂ := (sub_pos.mpr ordered₂).ne'
  have hw := (add_pos (sub_pos.mpr ordered₁) (sub_pos.mpr ordered₂)).ne'
  dsimp only
  field_simp
  ring

structure ResponseSample where
  frequency : ℝ
  splDb : ℝ
  impedanceOhms : ℂ

/-- The summary's impedance sample is the first minimizer in the in-band list. -/
theorem response_summary_bounds (first : ResponseSample) (rest : List ResponseSample) :
    let samples := first :: rest
    let spl := samples.map ResponseSample.splDb
    let minSplDb := spl.minimum_of_length_pos (by simp [spl, samples])
    let maxSplDb := spl.maximum_of_length_pos (by simp [spl, samples])
    let rippleDb := maxSplDb - minSplDb
    let impedance := fun p : ResponseSample => ‖p.impedanceOhms‖
    let minimum := (samples.argmin impedance).getD first
    let minimumImpedance := impedance minimum
    let reportedFrequency := minimum.frequency
    (∀ p ∈ samples, minSplDb ≤ p.splDb ∧ p.splDb ≤ maxSplDb ∧
      minimumImpedance ≤ impedance p) ∧ 0 ≤ rippleDb ∧
    ∃ p ∈ samples, p.frequency = reportedFrequency ∧ impedance p = minimumImpedance := by
  classical
  dsimp only
  let impedance := fun p : ResponseSample => ‖p.impedanceOhms‖
  obtain ⟨minimum, selected⟩ : ∃ minimum, (first :: rest).argmin impedance = some minimum := by
    cases h : (first :: rest).argmin impedance with
    | none => exact (List.cons_ne_nil _ _ (List.argmin_eq_none.mp h)).elim
    | some p => exact ⟨p, rfl⟩
  obtain ⟨member, least, _⟩ := List.argmin_eq_some_iff.mp selected
  simp only [impedance] at selected least
  simp only [selected, Option.getD_some]
  have splBounds (p : ResponseSample) (hp : p ∈ first :: rest) :=
    And.intro (List.minimum_of_length_pos_le_of_mem
      (List.mem_map_of_mem (f := ResponseSample.splDb) hp) (by simp))
      (List.le_maximum_of_length_pos_of_mem
        (List.mem_map_of_mem (f := ResponseSample.splDb) hp) (by simp))
  refine ⟨fun p hp => ⟨(splBounds p hp).1, (splBounds p hp).2, least p hp⟩,
    sub_nonneg.mpr ((splBounds first List.mem_cons_self).1.trans (splBounds first List.mem_cons_self).2),
    ⟨minimum, member, rfl, rfl⟩⟩

/-- Each scenario is evaluated on the same nonempty grid as the baseline. -/
theorem sensitivity_envelope_bounds {n : ℕ} (baseline : Fin (n + 1) → ℝ)
    (scenarios : List (Fin (n + 1) → ℝ)) :
    (∀ i, let levels := baseline i :: scenarios.map (fun scenario => scenario i)
      let minSplDb := levels.minimum_of_length_pos (by simp [levels])
      let maxSplDb := levels.maximum_of_length_pos (by simp [levels])
      ∀ level ∈ levels, minSplDb ≤ level ∧ level ≤ maxSplDb) ∧
    ∀ scenario ∈ scenarios,
      let delta := fun i => |scenario i - baseline i|
      let deltas := List.ofFn delta
      let maxAbsSplDeltaDb := deltas.maximum_of_length_pos (by simp [deltas])
      (∀ i, delta i ≤ maxAbsSplDeltaDb) ∧ ∃ i, delta i = maxAbsSplDeltaDb := by
  constructor
  · intro i
    dsimp only
    intro level member
    exact ⟨List.minimum_of_length_pos_le_of_mem member _, List.le_maximum_of_length_pos_of_mem member _⟩
  · intro scenario _
    dsimp only
    refine ⟨?_, ?_⟩
    · intro i
      apply List.le_maximum_of_length_pos_of_mem
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · obtain ⟨i, equal⟩ := List.mem_ofFn.mp (List.maximum_of_length_pos_mem (by simp :
        0 < (List.ofFn (fun i => |scenario i - baseline i|)).length))
      exact ⟨i, equal⟩

theorem sensitivity_ranking_sorted {Parameter : Type} (entries : List (Parameter × ℝ))
    (unique : (entries.map Prod.fst).Nodup) :
    let ranking := entries.mergeSort (fun a b => decide (b.2 ≤ a.2))
    ranking.Pairwise (fun a b => b.2 ≤ a.2) ∧ (ranking.map Prod.fst).Nodup := by
  dsimp only
  constructor
  · have sorted := List.pairwise_mergeSort (le := fun (a b : Parameter × ℝ) => decide (b.2 ≤ a.2))
      (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab)))
      (fun a b => by simpa using le_total b.2 a.2) entries
    exact sorted.imp (fun h => of_decide_eq_true h)
  · exact ((List.mergeSort_perm entries _).map Prod.fst).nodup_iff.mpr unique

end Electroacoustics.Summaries
