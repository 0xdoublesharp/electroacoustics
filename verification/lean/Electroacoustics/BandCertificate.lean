module

public import Electroacoustics.BandHeadroom
public import Electroacoustics.Interval
import Mathlib.Tactic.Positivity

@[expose] public noncomputable section

namespace Electroacoustics.BandCertificate

open Electroacoustics.Interval
open Electroacoustics.BandHeadroom

structure Certificate where
  spans : List Box
  witnessHz : ℚ
  safe : ℚ
  upper : ℚ
  errorDb : ℚ
  deriving Repr

/-- An evaluator may fail on a difficult span. A successful evaluation must
    enclose the exact maximum-factor utilization at every frequency in the span. -/
def Encloses (enclose : Box → Option Box) (usage : ℝ → ℝ) : Prop :=
  ∀ span result, enclose span = some result → ∀ f, span.Contains f → result.Contains (usage f)

def checkSpan (enclose : Box → Option Box) (safe left right : ℚ) (span : Box) : Bool :=
  match enclose span with
  | none => false
  | some bound =>
    decide (span.lo = left ∧ left < span.hi ∧ span.hi ≤ right ∧ safe * bound.hi ≤ 1)

def checkSpans (enclose : Box → Option Box) (safe left right : ℚ) :
    List Box → Bool
  | [] => decide (left = right)
  | span :: rest =>
    checkSpan enclose safe left right span && checkSpans enclose safe span.hi right rest

theorem checkSpans_cons_of_checks {enclose : Box → Option Box} {safe left right : ℚ}
    {span : Box} {rest : List Box}
    (head : checkSpan enclose safe left right span = true)
    (tail : checkSpans enclose safe span.hi right rest = true) :
    checkSpans enclose safe left right (span :: rest) = true := by
  simp [checkSpans, head, tail]

/-- The caller proves that the rational constant `logLower` is a positive
    lower bound on log 10. The witness is evaluated at a singleton frequency. -/
def checkWitness (enclose : Box → Option Box) (band : Box) (logLower tolerance : ℚ)
    (cert : Certificate) : Bool :=
  match enclose (Box.point cert.witnessHz) with
  | none => false
  | some sampled =>
    decide (0 < cert.safe ∧ cert.safe ≤ cert.upper ∧
      band.lo ≤ cert.witnessHz ∧ cert.witnessHz ≤ band.hi ∧
      1 ≤ cert.upper * sampled.lo ∧ 0 < logLower ∧
      20 * (cert.upper / cert.safe - 1) ≤ logLower * cert.errorDb ∧
      cert.errorDb ≤ tolerance)

def check (enclose : Box → Option Box) (band : Box) (logLower tolerance : ℚ)
    (cert : Certificate) : Bool :=
  checkWitness enclose band logLower tolerance cert &&
    checkSpans enclose cert.safe band.lo band.hi cert.spans

theorem check_of_checks {enclose : Box → Option Box} {band : Box} {logLower tolerance : ℚ}
    {cert : Certificate} (witness : checkWitness enclose band logLower tolerance cert = true)
    (cover : checkSpans enclose cert.safe band.lo band.hi cert.spans = true) :
    check enclose band logLower tolerance cert = true := by
  simp [check, witness, cover]

private theorem checkSpans_sound {enclose : Box → Option Box} {usage : ℝ → ℝ}
    (valid : Encloses enclose usage) {safe left right : ℚ} (safeNonneg : 0 ≤ (safe : ℝ))
    (bandNonempty : left < right) {spans : List Box}
    (accepts : checkSpans enclose safe left right spans = true) {f : ℝ}
    (inBand : (Box.mk left right).Contains f) : (safe : ℝ) * usage f ≤ 1 := by
  induction spans generalizing left with
  | nil =>
    simp only [checkSpans] at accepts
    have equal : left = right := of_decide_eq_true accepts
    linarith
  | cons span rest ih =>
    cases evaluation : enclose span with
    | none => simp [checkSpans, checkSpan, evaluation] at accepts
    | some bounds =>
      simp only [checkSpans, checkSpan, evaluation, Bool.and_eq_true] at accepts
      obtain ⟨⟨hl, hs, hr, hu⟩, tail⟩ := And.intro
        (of_decide_eq_true accepts.1) accepts.2
      have rightLe : (span.hi : ℝ) ≤ right := by exact_mod_cast hr
      by_cases before : f ≤ (span.hi : ℝ)
      · have spanLeft : (span.lo : ℝ) ≤ f := by simpa only [hl] using inBand.1
        have limit := (valid span bounds evaluation f ⟨spanLeft, before⟩).2
        exact (mul_le_mul_of_nonneg_left limit safeNonneg).trans (by exact_mod_cast hu)
      · have strictlyBeforeRight : span.hi < right := by
          have : (span.hi : ℝ) < right := (lt_of_not_ge before).trans_le inBand.2
          exact_mod_cast this
        exact ih strictlyBeforeRight tail ⟨(le_of_not_ge before), inBand.2⟩

theorem check_sound {enclose : Box → Option Box} {usage : ℝ → ℝ}
    (valid : Encloses enclose usage) {band : Box} (bandNonempty : band.lo < band.hi)
    {logLower tolerance : ℚ} (logValid : (logLower : ℝ) ≤ Real.log 10)
    {cert : Certificate} (accepts : check enclose band logLower tolerance cert = true) :
    (∀ f, band.Contains f → (cert.safe : ℝ) * usage f ≤ 1) ∧
    (∀ drive : ℝ, (cert.upper : ℝ) < drive → ∃ f, band.Contains f ∧ 1 < drive * usage f) ∧
    (∀ drive : ℝ, (cert.safe : ℝ) ≤ drive → drive ≤ (cert.upper : ℝ) →
      20 / Real.log 10 * Real.log (drive / (cert.safe : ℝ)) ≤ (cert.errorDb : ℝ)) := by
  cases hSample : enclose (Box.point cert.witnessHz) with
  | none => simp [check, checkWitness, hSample] at accepts
  | some sample =>
    simp only [check, checkWitness, hSample, Bool.and_eq_true] at accepts
    obtain ⟨⟨safePos, ordered, witnessLo, witnessHi, above, logPos, error, _⟩, hSpans⟩ :=
      And.intro (of_decide_eq_true accepts.1) accepts.2
    have safePosR : 0 < (cert.safe : ℝ) := by exact_mod_cast safePos
    have orderedR : (cert.safe : ℝ) ≤ cert.upper := by exact_mod_cast ordered
    have upperPosR := safePosR.trans_le orderedR
    refine ⟨fun f hf => checkSpans_sound valid safePosR.le bandNonempty hSpans hf, ?_, ?_⟩
    · intro drive tooHigh
      have inBand : band.Contains cert.witnessHz :=
        ⟨Rat.cast_le.mpr witnessLo, Rat.cast_le.mpr witnessHi⟩
      have sampleLe : (sample.lo : ℝ) ≤ usage cert.witnessHz :=
        (valid _ _ hSample _ (point_sound _)).1
      have aboveR : 1 ≤ (cert.upper : ℝ) * sample.lo := by exact_mod_cast above
      have usagePositive : 0 < usage cert.witnessHz := by
        by_contra! h
        have hzero := mul_nonpos_of_nonneg_of_nonpos upperPosR.le (sampleLe.trans h)
        linarith
      exact ⟨cert.witnessHz, inBand, aboveR.trans_lt
        ((mul_le_mul_of_nonneg_left sampleLe upperPosR.le).trans_lt
          (mul_lt_mul_of_pos_right tooHigh usagePositive))⟩
    · intro drive driveLo driveHi
      have logPosR : (0 : ℝ) < logLower := by exact_mod_cast logPos
      have logTenPos := logPosR.trans_le logValid
      have gapR : 20 * ((cert.upper : ℝ) / (cert.safe : ℝ) - 1) ≤
          (logLower : ℝ) * (cert.errorDb : ℝ) := by exact_mod_cast error
      have gapNonneg : 0 ≤ (cert.errorDb : ℝ) := by
        have h : 0 ≤ (cert.upper : ℝ) / (cert.safe : ℝ) - 1 := by
          rw [sub_nonneg, le_div_iff₀ safePosR, one_mul]
          exact orderedR
        exact nonneg_of_mul_nonneg_right ((mul_nonneg (by positivity) h).trans gapR) logPosR
      apply (db_gap_le safePosR (safePosR.trans_le driveLo) driveHi).trans
      rw [div_mul_eq_mul_div, div_le_iff₀ logTenPos]
      exact gapR.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_right logValid gapNonneg)


structure PartialSpan where
  frequencies : Box
  accepted : Bool
  deriving Repr

structure PartialCertificate where
  spans : List PartialSpan
  safe : Option ℚ := none
  /-- A frequency and a proposed upper voltage. -/
  witness : Option (ℚ × ℚ) := none
  deriving Repr

def PartialCertificate.unresolvedIntervals (cert : PartialCertificate) : List Box :=
  (cert.spans.filter (fun s => !s.accepted)).map PartialSpan.frequencies

def checkPartition (test : Box → Bool) (left right : ℚ) : List PartialSpan → Bool
  | [] => decide (left = right)
  | span :: rest =>
    let b := span.frequencies
    decide (b.lo = left ∧ left < b.hi ∧ b.hi ≤ right) &&
      test b && checkPartition test b.hi right rest

def partialSafe (enclose : Box → Option Box) (safe : ℚ) (span : Box) : Bool :=
  (enclose span).any (fun bounds => decide (safe * bounds.hi ≤ 1))

def partialWitness (enclose : Box → Option Box) (band : Box) (witness : ℚ × ℚ) : Bool :=
  let (f, upper) := witness
  (enclose (Box.point f)).any (fun bounds =>
    decide (band.lo ≤ f ∧ f ≤ band.hi ∧ 0 < bounds.lo ∧ 1 ≤ upper * bounds.lo))

def checkPartial (enclose : Box → Option Box) (band : Box) (cert : PartialCertificate) : Bool :=
  cert.safe.all (fun safe => decide (0 < safe)) &&
    cert.witness.all (partialWitness enclose band) &&
    checkPartition (fun span => cert.safe.all (fun safe => partialSafe enclose safe span))
      band.lo band.hi cert.spans

private theorem checkPartition_sound {test : Box → Bool} {left right : ℚ} {spans : List PartialSpan}
    (valid : checkPartition test left right spans = true) :
    (∀ s ∈ spans, test s.frequencies = true) ∧
    (left < right → ∀ f, (Box.mk left right).Contains f →
      ∃ s ∈ spans, s.frequencies.Contains f) := by
  induction spans generalizing left with
  | nil =>
    have equal : left = right := of_decide_eq_true valid
    simp [equal]
  | cons s rest ih =>
    simp only [checkPartition, Bool.and_eq_true] at valid
    obtain ⟨⟨hEnds, head⟩, tail⟩ := valid
    obtain ⟨hl, _, _⟩ := of_decide_eq_true hEnds
    obtain ⟨allTail, coverTail⟩ := ih tail
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact head
      · exact allTail _ hx
    · intro _ f hf
      by_cases h : f ≤ (s.frequencies.hi : ℝ)
      · exact ⟨s, by simp, ⟨by simpa only [hl] using hf.1, h⟩⟩
      · have hright : s.frequencies.hi < right :=
          Rat.cast_lt.mp ((lt_of_not_ge h).trans_le hf.2)
        obtain ⟨t, ht, htf⟩ := coverTail hright f ⟨(lt_of_not_ge h).le, hf.2⟩
        exact ⟨t, List.mem_cons_of_mem _ ht, htf⟩

theorem checkPartial_sound {enclose : Box → Option Box} {usage : ℝ → ℝ}
    (valid : Encloses enclose usage) {band : Box} (nonempty : band.lo < band.hi)
    {cert : PartialCertificate} (accepted : checkPartial enclose band cert = true) :
    (∀ safe, cert.safe = some safe → ∀ f, band.Contains f → (safe : ℝ) * usage f ≤ 1) ∧
    (∀ f upper, cert.witness = some (f, upper) → ∀ drive : ℝ, (upper : ℝ) < drive →
      band.Contains f ∧ 1 < drive * usage f) ∧
    (∀ f, band.Contains f →
      (∃ s ∈ cert.spans, s.accepted = true ∧ s.frequencies.Contains f) ∨
      (∃ s ∈ cert.unresolvedIntervals, s.Contains f)) := by
  simp only [checkPartial, Bool.and_eq_true] at accepted
  obtain ⟨⟨safePos, witnessValid⟩, partitionValid⟩ := accepted
  obtain ⟨allSafe, cover⟩ := checkPartition_sound partitionValid
  let realBand : Span := ⟨band.lo, band.hi, 0⟩
  refine ⟨?_, ?_, ?_⟩
  · intro safe hs f hf
    have hpos : 0 < (safe : ℝ) := Rat.cast_pos.mpr
      (of_decide_eq_true (by simpa [hs] using safePos))
    let attachBound := fun s : PartialSpan =>
      Span.mk s.frequencies.lo s.frequencies.hi
        ((enclose s.frequencies).map (fun b => (b.hi : ℝ)) |>.getD 0)
    let spans := cert.spans.map attachBound
    have covers : ∀ g, realBand.Contains g → ∃ s ∈ spans, s.Contains g := by
      intro g hg
      obtain ⟨s, hm, hsg⟩ := cover nonempty g hg
      exact ⟨attachBound s, List.mem_map.mpr ⟨s, hm, rfl⟩, hsg⟩
    have sample (s : PartialSpan) (hm : s ∈ cert.spans) :
        ∃ b, enclose s.frequencies = some b ∧ (safe : ℝ) * (b.hi : ℝ) ≤ 1 := by
      have q := allSafe s hm
      cases he : enclose s.frequencies with
      | none => simp [hs, partialSafe, he] at q
      | some b =>
        have check : safe * b.hi ≤ 1 := by simpa [hs, partialSafe, he] using q
        exact ⟨b, rfl, by exact_mod_cast check⟩
    have bounds : ∀ s ∈ spans, ∀ g, s.Contains g → ∀ _ : Unit, usage g ≤ s.ceiling := by
      intro _ hm g hg _
      obtain ⟨s, hmem, rfl⟩ := List.mem_map.mp hm
      obtain ⟨b, he, _⟩ := sample s hmem
      simpa [attachBound, he] using (valid _ _ he g hg).2
    have combined : ∀ s ∈ spans, s.ceiling ≤ 1 / (safe : ℝ) := by
      intro _ hm
      obtain ⟨s, hmem, rfl⟩ := List.mem_map.mp hm
      obtain ⟨b, he, hmul⟩ := sample s hmem
      have hb : (b.hi : ℝ) ≤ 1 / (safe : ℝ) :=
        (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hmul)
      simpa [attachBound, he] using hb
    have feasible := partial_safe_of_cover realBand (fun g (_ : Unit) => usage g)
      spans covers bounds (one_div_pos.mpr hpos) combined hpos.le
      (show (safe : ℝ) ≤ 1 / (1 / (safe : ℝ)) by simp)
    exact feasible f hf ()
  · intro f upper hw drive habove
    cases he : enclose (Box.point f) with
    | none => simp [hw, partialWitness, he] at witnessValid
    | some b =>
      have properties : band.lo ≤ f ∧ f ≤ band.hi ∧ 0 < b.lo ∧ 1 ≤ upper * b.lo := by
        simpa [hw, partialWitness, he] using witnessValid
      obtain ⟨hl, hh, hp, hu⟩ := properties
      have inside : band.Contains f := ⟨Rat.cast_le.mpr hl, Rat.cast_le.mpr hh⟩
      have positive : (0 : ℝ) < b.lo := Rat.cast_pos.mpr hp
      have ceiling : 1 / (b.lo : ℝ) ≤ (upper : ℝ) :=
        (div_le_iff₀ positive).mpr (by exact_mod_cast hu)
      have bad := partial_upper_of_witness realBand (fun _ (_ : Unit) => usage f)
        (f := (f : ℝ)) inside () positive (valid _ _ he _ (point_sound f)).1 ceiling drive habove
      exact ⟨inside, lt_of_not_ge (fun assumed => bad (fun _ _ _ => assumed))⟩
  · intro f hf
    let attachFlag := fun s : PartialSpan =>
      Span.mk s.frequencies.lo s.frequencies.hi (if s.accepted then 1 else 0)
    let spans := cert.spans.map attachFlag
    have covers : ∀ g, realBand.Contains g → ∃ s ∈ spans, s.Contains g := by
      intro g hg
      obtain ⟨s, hm, hsg⟩ := cover nonempty g hg
      exact ⟨attachFlag s, List.mem_map.mpr ⟨s, hm, rfl⟩, hsg⟩
    rcases unresolved_partition realBand spans (fun s => decide (s.ceiling = 1)) covers f hf with h | h
    · obtain ⟨s, hm, hsf⟩ := h
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hm).1
      exact Or.inl ⟨t, ht, by simpa [attachFlag] using (List.mem_filter.mp hm).2, hsf⟩
    · obtain ⟨s, hm, hsf⟩ := h
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hm).1
      have flag : !t.accepted = true := by simpa [attachFlag] using (List.mem_filter.mp hm).2
      exact Or.inr ⟨t.frequencies, List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨ht, flag⟩, rfl⟩, hsf⟩

end Electroacoustics.BandCertificate
