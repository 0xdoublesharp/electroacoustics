module

public import Electroacoustics.DuctInterval
import Mathlib.Tactic.FunProp
import Lean.Elab.Command
import Lean.Util.CollectAxioms

@[expose] public noncomputable section

namespace Electroacoustics.DuctCertificate

open Electroacoustics.Interval Electroacoustics.DuctInterval
open Electroacoustics.Transcendentals

structure TuningCertificate where
  lower : ℚ
  upper : ℚ
  earlierSpans : List Box
  relativeTolerance : ℚ
  deriving Repr

structure PeakVelocityCertificate where
  lower : ℚ
  upper : ℚ
  witnessSection : ℕ
  witnessFraction : ℚ
  sectionSpans : List (List Box)
  relativeTolerance : ℚ
  deriving Repr

def checkCover (check : Box → Bool) (right : ℚ) : ℚ → List Box → Bool
  | left, [] => decide (left = right)
  | left, span :: rest =>
    decide (span.lo = left ∧ left < span.hi ∧ span.hi ≤ right) &&
      check span && checkCover check right span.hi rest

private theorem checkCover_sound {check : Box → Bool} {left right : ℚ} {spans : List Box}
    (accepted : checkCover check right left spans = true) (width : left < right)
    {x : ℝ} (inside : x ∈ Set.Icc (left : ℝ) (right : ℝ)) :
    ∃ span ∈ spans, span.Contains x ∧ check span = true := by
  induction spans generalizing left with
  | nil => simp [checkCover, width.ne] at accepted
  | cons span rest ih =>
    simp only [checkCover, Bool.and_eq_true, decide_eq_true_eq] at accepted
    obtain ⟨⟨⟨same, _, _⟩, pass⟩, next⟩ := accepted
    by_cases before : x ≤ (span.hi : ℝ)
    · exact ⟨span, List.mem_cons_self, ⟨same ▸ inside.1, before⟩, pass⟩
    · have after := lt_of_not_ge before
      have more : span.hi < right := Rat.cast_lt.mp (after.trans_le inside.2)
      obtain ⟨cell, member, contains, passed⟩ := ih next more ⟨after.le, inside.2⟩
      exact ⟨cell, List.mem_cons_of_mem _ member, contains, passed⟩

private theorem checkCover_member {check : Box → Bool} {left right : ℚ} {spans : List Box}
    (accepted : checkCover check right left spans = true) {span : Box} (member : span ∈ spans) :
    check span = true := by
  induction spans generalizing left with
  | nil => simp at member
  | cons first rest ih =>
    simp only [checkCover, Bool.and_eq_true] at accepted
    rcases List.mem_cons.mp member with rfl | tail
    · exact accepted.1.2
    · exact ih accepted.2 tail

private theorem checkedOption {a : Option α} {check : α → Bool}
    (accepted : a.any check = true) : ∃ value, a = some value ∧ check value = true := by
  cases a <;> simp_all [Option.any]

private theorem relativeWidth {lower upper tolerance : ℚ} (positive : 0 < lower)
    (width : upper - lower ≤ lower * tolerance) :
    ((upper : ℝ) - lower) / lower ≤ tolerance := by
  apply (div_le_iff₀ (Rat.cast_pos.mpr positive)).mpr
  simpa only [Rat.cast_sub, Rat.cast_mul, mul_comm] using (Rat.cast_le.mpr width : _ ≤ (_ : ℝ))

def negativeResidual (prec : ℕ) (path : DuctPath) (volume speed : ℚ)
    (span : Box) : Bool :=
  (evalDuctTuningResidual prec path volume speed span).any fun (residual, _) =>
    decide (residual.hi < 0)

def checkTuningCertificate (prec : ℕ) (path : DuctPath) (volume speed : ℚ)
    (cert : TuningCertificate) : Bool :=
  decide (0 < cert.lower ∧ cert.lower < cert.upper ∧ 0 < cert.relativeTolerance ∧
    cert.upper - cert.lower ≤ cert.lower * cert.relativeTolerance ∧
    path.sections ≠ [] ∧ 0 < path.count ∧ 0 < volume ∧ 0 < speed) &&
  negativeResidual prec path volume speed (Box.point cert.lower) &&
  (evalDuctTuningResidual prec path volume speed (Box.point cert.upper)).any
    (fun (residual, _) => decide (0 ≤ residual.lo)) &&
  (evalDuctTuningResidual prec path volume speed ⟨cert.lower, cert.upper⟩).any
    (fun (_, denominator) => decide (¬(denominator.lo ≤ 0 ∧ 0 ≤ denominator.hi))) &&
  checkCover (negativeResidual prec path volume speed) cert.lower 0 cert.earlierSpans

attribute [local fun_prop] continuous_waveCos continuous_waveSinc

private theorem continuousPosition (model : SectionModel ℝ) (profile : Profile) (density x : ℝ)
    {k2 : ℝ → ℝ} {downstream : ℝ → ℝ × ℝ}
    (hk : Continuous k2) (hd : Continuous downstream) :
    Continuous (fun f => (position realArithmetic model profile (k2 f) density x
      (downstream f)).1) := by
  simp only [position, Arithmetic.withValue_eq, realArithmetic]
  fun_prop

private theorem continuousTraverse (sections : List Section) (density : ℝ)
    (mouth : ℝ × ℝ) {k2 : ℝ → ℝ} (hk : Continuous k2) :
    Continuous (fun f => (traverse realArithmetic (k2 f) density mouth sections).1) := by
  induction sections with
  | nil => exact continuous_const
  | cons ductSection rest ih =>
    simp only [DuctInterval.traverse, Arithmetic.withValue_eq, withSectionModel_eq]
    exact continuousPosition _ _ _ _ hk ih

private theorem continuousDuctState (path : DuctPath) (speed density : ℝ) :
    Continuous (exactDuctState path speed density) := by
  unfold exactDuctState ductResponse
  simp only [Arithmetic.withValue_eq, realArithmetic]
  let k2 : ℝ → ℝ := fun f => (((2 : ℚ) : ℝ) * Real.pi *
    Real.sqrt ↑(path.inertanceFactor * path.complianceFactor) / speed * f) ^ 2
  let mouth : ℝ × ℝ := (density * (path.outletCorrection : ℝ) /
    ↑((path.sections.getLast?.map Section.outletArea).getD 0), ((1 : ℚ) : ℝ))
  let inlet : ℝ := density * ↑(path.inletCorrection + path.junctionInertances.sum) /
    ↑((path.sections.head?.map Section.inletArea).getD 0)
  let state := fun f => (traverse realArithmetic (k2 f) (density * (path.inertanceFactor : ℝ))
    mouth path.sections).1
  change Continuous (fun f => ((state f).1 + inlet * (state f).2, (state f).2))
  have propagated : Continuous state := continuousTraverse _ _ _ (by unfold k2; fun_prop)
  exact (propagated.fst.add ((continuous_const (y := inlet)).mul propagated.snd)).prodMk
    propagated.snd

/-- All divisions in the state use geometry and medium parameters fixed with respect to frequency. -/
theorem continuous_exactTuningResidual (path : DuctPath) (volume speed : ℝ) :
    Continuous (exactTuningResidual path volume speed) := by
  unfold exactTuningResidual
  have state := continuousDuctState path speed 1
  fun_prop

private theorem negativeResidual_sound {prec : ℕ} {path : DuctPath} {volume speed : ℚ}
    {span : Box} (accepted : negativeResidual prec path volume speed span = true)
    {f : ℝ} (inside : span.Contains f) : exactTuningResidual path volume speed f < 0 := by
  obtain ⟨⟨residual, denominator⟩, eval, bound⟩ := checkedOption accepted
  exact (evalDuctTuningResidual_sound eval inside).1.2.trans_lt
    (Rat.cast_lt_zero.mpr (of_decide_eq_true bound))

theorem checkTuningCertificate_sound {prec : ℕ} {path : DuctPath} {volume speed : ℚ}
    {cert : TuningCertificate} (accepted : checkTuningCertificate prec path volume speed cert = true) :
    ∃ f ∈ Set.Icc (cert.lower : ℝ) (cert.upper : ℝ), 0 < f ∧
      exactTuningResidual path volume speed f = 0 ∧ (exactDuctState path speed 1 f).2 ≠ 0 ∧
      (∀ g, 0 < g → exactTuningResidual path volume speed g = 0 →
        (exactDuctState path speed 1 g).2 ≠ 0 → f ≤ g) ∧
      ((cert.upper : ℝ) - cert.lower) / cert.lower ≤ cert.relativeTolerance := by
  simp only [checkTuningCertificate, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨⟨⟨⟨positive, ordered, _, width, _⟩, _⟩, upper⟩, bracket⟩, earlier⟩ := accepted
  obtain ⟨⟨residual, _⟩, evalUpper, upperSign⟩ := checkedOption upper
  obtain ⟨⟨_, denominator⟩, evalBracket, noZero⟩ := checkedOption bracket
  have noZero' : ¬(denominator.lo ≤ 0 ∧ 0 ≤ denominator.hi) := of_decide_eq_true noZero
  let realBracket : Duct.Bracket := ⟨cert.lower, cert.upper⟩
  let asBracket := fun span : Box => Duct.Bracket.mk span.lo span.hi
  have cover : ∀ f ∈ Set.Icc 0 realBracket.low,
      ∃ s ∈ cert.earlierSpans.map asBracket, f ∈ Set.Icc s.low s.high := by
    intro f inside
    obtain ⟨span, member, contains, _⟩ := checkCover_sound earlier positive
      (by simpa only [realBracket, Rat.cast_zero] using inside)
    exact ⟨asBracket span, List.mem_map_of_mem member, contains⟩
  have negative : ∀ s ∈ cert.earlierSpans.map asBracket, ∀ f ∈ Set.Icc s.low s.high,
      exactTuningResidual path volume speed f < 0 := by
    intro s member f inside
    obtain ⟨span, inCover, rfl⟩ := List.mem_map.mp member
    exact negativeResidual_sound (checkCover_member earlier inCover) inside
  have signs : 0 ≤ exactTuningResidual path volume speed realBracket.high :=
    (Rat.cast_nonneg.mpr (of_decide_eq_true upperSign)).trans
      (evalDuctTuningResidual_sound evalUpper (point_sound cert.upper)).1.1
  have poleFree : ∀ f ∈ Set.Icc realBracket.low realBracket.high,
      (exactDuctState path speed 1 f).2 ≠ 0 := fun _ inside =>
    not_containsZero_ne_zero noZero'
      (evalDuctTuningResidual_sound evalBracket inside).2
  obtain ⟨f, ⟨inside, pos, zero, physical, least⟩, _⟩ :=
    Duct.first_tuning_of_cover_certificate (bracket := realBracket)
      (Rat.cast_le.mpr ordered.le) (Rat.cast_pos.mpr positive) signs
      (continuous_exactTuningResidual path volume speed) poleFree _ cover negative
  exact ⟨f, inside, pos, zero, physical, least, relativeWidth positive width⟩

/-- Local particle speed per unit total throat volume flow. -/
def exactNormalizedSectionSpeed (path : DuctPath) (speed density frequency : ℝ)
    (index : ℕ) (fraction : ℝ) : ℝ :=
  exactSectionSpeed path speed density frequency index fraction /
    (|(exactDuctState path speed density frequency).2| * (path.count : ℝ))

def normalizedPosition (prec : ℕ) (normalization : Box)
    (evaluate : Box → Option Box) (fraction : Box) : Option Box := do
  let raw ← evaluate fraction
  DuctInterval.div prec raw normalization

def checkSection (prec : ℕ) (normalization : Box) (upper : ℚ)
    (evaluate : Box → Option Box) : List Box → Bool :=
  checkCover (fun span => (normalizedPosition prec normalization evaluate span).any
    (fun bound => decide (bound.hi ≤ upper))) 1 0

def checkSections (prec : ℕ) (normalization : Box) (upper : ℚ) :
    List (Box → Option Box) → List (List Box) → Bool
  | [], [] => true
  | evaluate :: positions, spans :: sections =>
    checkSection prec normalization upper evaluate spans &&
      checkSections prec normalization upper positions sections
  | _, _ => false

private theorem checkSections_at {prec : ℕ} {normalization : Box} {upper : ℚ}
    {positions : List (Box → Option Box)} {sections : List (List Box)}
    (accepted : checkSections prec normalization upper positions sections = true)
    {i : ℕ} (index : i < positions.length) :
    ∃ evaluate spans, positions[i]? = some evaluate ∧ sections[i]? = some spans ∧
      checkSection prec normalization upper evaluate spans = true := by
  induction positions generalizing sections i with
  | nil => simp at index
  | cons evaluate tail ih =>
    cases sections with
    | nil => simp [checkSections] at accepted
    | cons spans rest =>
      simp only [checkSections, Bool.and_eq_true] at accepted
      cases i with
      | zero => exact ⟨evaluate, spans, rfl, rfl, accepted.1⟩
      | succ i => exact ih accepted.2 (Nat.lt_of_succ_lt_succ index)

def checkWitness (prec : ℕ) (normalization : Box) (positions : List (Box → Option Box))
    (cert : PeakVelocityCertificate) : Bool :=
  positions[cert.witnessSection]?.any fun evaluate =>
    (normalizedPosition prec normalization evaluate (Box.point cert.witnessFraction)).any
      fun bound => decide (cert.lower ≤ bound.lo)

def checkPeakResponse (prec : ℕ) (count : ℚ) (denominator : Box)
    (positions : List (Box → Option Box)) (cert : PeakVelocityCertificate) : Bool :=
  decide (¬(denominator.lo ≤ 0 ∧ 0 ≤ denominator.hi)) &&
    withBox (DuctInterval.mul prec denominator.abs (Box.point count)) fun normalization =>
      checkWitness prec normalization positions cert &&
        checkSections prec normalization cert.upper positions cert.sectionSpans

def checkPeakVelocityCertificate (prec : ℕ) (path : DuctPath) (frequency speed density : ℚ)
    (cert : PeakVelocityCertificate) : Bool :=
  decide (0 < cert.lower ∧ cert.lower ≤ cert.upper ∧ 0 < cert.relativeTolerance ∧
    cert.upper - cert.lower ≤ cert.lower * cert.relativeTolerance ∧ 0 < path.count ∧
    cert.sectionSpans.length = path.sections.length ∧ cert.witnessSection < path.sections.length ∧
    0 ≤ cert.witnessFraction ∧ cert.witnessFraction ≤ 1) &&
  (evalDuctResponse prec path speed density (Box.point frequency)).any
    (fun (_, denominator, positions) =>
      withBox denominator fun d => checkPeakResponse prec path.count d positions cert)

private theorem normalizedPosition_sound {prec : ℕ} {normalization fraction bound : Box}
    {evaluate : Box → Option Box} {raw : ℝ → ℝ} {norm x : ℝ}
    (hn : normalization.Contains norm) (he : EnclosesPosition evaluate raw)
    (hx : fraction.Contains x)
    (accepted : normalizedPosition prec normalization evaluate fraction = some bound) :
    bound.Contains (raw x / norm) := by
  have h := Approx.div (p := prec) (he fraction x hx) (Approx.some hn)
  exact h bound (by simpa [normalizedPosition, intervalArithmetic, lift₂] using accepted)

private theorem traverseSpeedNonneg (sections : List Section) (k2 density : ℝ) (mouth : ℝ × ℝ)
    (i : ℕ) (x : ℝ) :
    0 ≤ ((traverse realArithmetic k2 density mouth sections).2[i]?.getD (fun _ => 0)) x := by
  induction sections generalizing i with
  | nil => rfl
  | cons ductSection rest ih =>
    cases i with
    | zero =>
      simp only [DuctInterval.traverse, Arithmetic.withValue_eq, withSectionModel_eq, List.getElem?_cons_zero,
        Option.getD_some, speedAt, position, realArithmetic]
      exact div_nonneg (abs_nonneg _) (sq_nonneg _)
    | succ i =>
      simpa only [DuctInterval.traverse, Arithmetic.withValue_eq, withSectionModel_eq, List.getElem?_cons_succ]
        using ih i

theorem checkPeakVelocityCertificate_sound {prec : ℕ} {path : DuctPath}
    {frequency speed density : ℚ} {cert : PeakVelocityCertificate}
    (accepted : checkPeakVelocityCertificate prec path frequency speed density cert = true) :
    (exactDuctState path speed density frequency).2 ≠ 0 ∧
    (∀ s < path.sections.length, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      exactNormalizedSectionSpeed path speed density frequency s x ≤ (cert.upper : ℝ)) ∧
    (∃ s < path.sections.length, ∃ x ∈ Set.Icc (0 : ℝ) 1,
      (cert.lower : ℝ) ≤ exactNormalizedSectionSpeed path speed density frequency s x) ∧
    ((cert.upper : ℝ) - cert.lower) / cert.lower ≤ cert.relativeTolerance := by
  simp only [checkPeakVelocityCertificate, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨positive, _, _, width, countPos, _, witnessIndex, fractionLo, fractionHi⟩, response⟩ :=
    accepted
  obtain ⟨⟨_, denominator, positions⟩, eval, checks⟩ := checkedOption response
  simp only [withBox_eq, checkPeakResponse, Bool.and_eq_true, decide_eq_true_eq] at checks
  obtain ⟨poleFree, witness, sections⟩ := checks
  let d := (exactDuctState path speed density frequency).2
  let norm := |d| * (path.count : ℝ)
  let normalization := DuctInterval.mul prec denominator.abs (Box.point path.count)
  have hd := (evalDuctResponse_sound eval (point_sound frequency)).2.1
  have physical : d ≠ 0 := not_containsZero_ne_zero poleFree hd
  have hc : (0 : ℝ) < path.count := Rat.cast_pos.mpr countPos
  have normPos : 0 < norm := mul_pos (abs_pos.mpr physical) hc
  have hn : normalization.Contains norm :=
    roundOut_sound (mul_sound (abs_sound hd) (point_sound path.count)) prec
  have length := ductPositions_length eval (point_sound frequency)
  let raw := fun (s : Fin path.sections.length) =>
    exactSectionSpeed path speed density frequency s
  have rawNonneg (s : Fin path.sections.length) (x : ℝ) : 0 ≤ raw s x := by
    simpa only [raw, exactSectionSpeed, ductResponse, Arithmetic.withValue_eq]
      using traverseSpeedNonneg _ _ _ _ s x
  let spanBound := fun span : Box => ((span.lo : ℝ), (span.hi : ℝ), (cert.upper : ℝ) * norm)
  let spans := fun s : Fin path.sections.length =>
    (cert.sectionSpans[s.val]?.getD []).map spanBound
  have sectionCheck (s : Fin path.sections.length) :=
    checkSections_at sections (show s.val < positions.length by rw [length]; exact s.isLt)
  have cover : ∀ s x, x ∈ Set.Icc (0 : ℝ) 1 →
      ∃ span ∈ spans s, x ∈ Set.Icc span.1 span.2.1 := by
    intro s x inside
    obtain ⟨_, cells, _, atSection, pass⟩ := sectionCheck s
    obtain ⟨span, member, contains, _⟩ := checkCover_sound pass (by decide)
      (by simpa only [Rat.cast_zero, Rat.cast_one] using inside)
    refine ⟨spanBound span, ?_, contains⟩
    simp only [spans, atSection, Option.getD_some]
    exact List.mem_map_of_mem member
  have bounds : ∀ s span, span ∈ spans s → ∀ x ∈ Set.Icc span.1 span.2.1,
      |raw s x| / (1 : ℝ) ≤ span.2.2 := by
    intro s span member x inside
    obtain ⟨evaluate, cells, atPosition, atSection, pass⟩ := sectionCheck s
    simp only [spans, atSection, Option.getD_some] at member
    obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp member
    unfold checkSection at pass
    obtain ⟨bound, enclosed, ceiling⟩ := checkedOption (checkCover_member pass cellMember)
    have h := normalizedPosition_sound hn
      (ductPositions_sound eval _ _ atPosition _ (point_sound frequency)) inside enclosed
    simpa only [spanBound, div_one, abs_of_nonneg (rawNonneg s x)] using
      (div_le_iff₀ normPos).mp (h.2.trans (Rat.cast_le.mpr (of_decide_eq_true ceiling)))
  have ceilings : ∀ s span, span ∈ spans s → span.2.2 ≤ (cert.upper : ℝ) * norm := by
    intro s span member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    exact le_rfl
  obtain ⟨evaluate, atWitness, pointCheck⟩ := checkedOption witness
  obtain ⟨bound, enclosed, floor⟩ := checkedOption pointCheck
  let s : Fin path.sections.length := ⟨cert.witnessSection, witnessIndex⟩
  have fraction : (cert.witnessFraction : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Rat.cast_nonneg.mpr fractionLo, by exact_mod_cast fractionHi⟩
  have sample := normalizedPosition_sound hn
    (ductPositions_sound eval _ _ atWitness _ (point_sound frequency))
    (point_sound cert.witnessFraction) enclosed
  have lower : (cert.lower : ℝ) * norm ≤ |raw s cert.witnessFraction| / (1 : ℝ) := by
    rw [div_one, abs_of_nonneg (rawNonneg s _)]
    exact (le_div_iff₀ normPos).mp ((Rat.cast_le.mpr (of_decide_eq_true floor)).trans sample.1)
  -- The response evaluator has already divided flow by area to obtain raw particle speed.
  obtain ⟨upper, index, x, inside, floor⟩ := Duct.peak_velocity_certificate_sound
    raw (fun _ _ => 1) physical hc spans cover bounds ceilings ⟨s, _, fraction, lower⟩
  have cancel (q : ℝ) : q * norm / norm = q := mul_div_cancel_right₀ _ normPos.ne'
  refine ⟨physical, ?_, ⟨index, index.isLt, x, inside, ?_⟩, relativeWidth positive width⟩
  · intro i hi x inside
    have result := upper ⟨i, hi⟩ x inside
    rw [one_mul, abs_of_nonneg (rawNonneg ⟨i, hi⟩ x)] at result
    change raw ⟨i, hi⟩ x / norm ≤ (cert.upper : ℝ) * norm / norm at result
    simpa only [cancel, exactNormalizedSectionSpeed, raw, norm, d] using result
  · rw [one_mul, abs_of_nonneg (rawNonneg index x)] at floor
    change (cert.lower : ℝ) * norm / norm ≤ raw index x / norm at floor
    simpa only [cancel, exactNormalizedSectionSpeed, raw, norm, d] using floor

open Lean in
run_cmd do
  let theorems := #[``continuous_exactTuningResidual, ``checkTuningCertificate_sound,
    ``checkPeakVelocityCertificate_sound]
  for name in theorems do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun axiomName =>
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms: {unexpected}"
  logInfo m!"Audited axioms for {theorems.size} duct certificate theorems."

end Electroacoustics.DuctCertificate
