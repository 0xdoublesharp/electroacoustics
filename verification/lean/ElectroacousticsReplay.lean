import Electroacoustics.BandCertificate
import Electroacoustics.DuctInterval
import Electroacoustics.Transcendentals
import LeanCert.Engine.IntervalEvalDyadic
import Lean.Elab.Command
import Lean.Util.CollectAxioms

noncomputable section

namespace Electroacoustics.BandModel

open Electroacoustics.Interval
open Electroacoustics.BandCertificate
open LeanCert.Core LeanCert.Engine

local instance : OfNat Expr n := ⟨.const n⟩
local instance : Add Expr := ⟨.add⟩
local instance : Neg Expr := ⟨.neg⟩
local instance : Sub Expr := ⟨Expr.sub⟩
local instance : Mul Expr := ⟨.mul⟩
local instance : Div Expr := ⟨fun a b => .mul a (.inv b)⟩

def q (value : ℚ) : Expr := .const value
def sq (x : Expr) : Expr := x * x
def fourth (x : Expr) : Expr := sq (sq x)

structure Biquad where
  b0 : ℚ
  b1 : ℚ
  b2 : ℚ
  a1 : ℚ
  a2 : ℚ

structure Dsp where
  gainDb : ℚ := 0
  highpass : Option ℚ := none
  butterworth : Bool := false
  lowpass : Option ℚ := none
  sampleRate : ℚ := 1
  stages : List Biquad := []

def phaseHalf (dsp : Dsp) : Expr := .namedConst .pi * (.var 0 / q dsp.sampleRate)

def biquadMagnitude (stage : Biquad) (phase : Expr) : Expr :=
  let versine : Expr := 2 * sq (.sin phase)
  let sine : Expr := 2 * .sin phase * .cos phase
  let bsum := q (stage.b0 + stage.b2)
  let asum := q (1 + stage.a2)
  let nr := q stage.b1 + bsum - bsum * versine
  let ni := q (stage.b0 - stage.b2) * sine
  let dr := q stage.a1 + asum - asum * versine
  let di := q (1 - stage.a2) * sine
  .sqrt (sq nr + sq ni) / .sqrt (sq dr + sq di)

def filterGain (dsp : Dsp) : Expr :=
  let level : Expr := if dsp.gainDb = 0 then 1 else .exp (q (dsp.gainDb / 20) * .log 10)
  let hp : Expr := match dsp.highpass with
    | none => 1
    | some cutoff =>
      let ratio := fourth (q cutoff / .var 0)
      if dsp.butterworth then 1 / .sqrt (1 + sq ratio) else 1 / (1 + ratio)
  let lp : Expr := match dsp.lowpass with
    | none => 1
    | some cutoff => 1 / (1 + fourth (.var 0 / q cutoff))
  dsp.stages.foldl (fun gain stage => gain * biquadMagnitude stage (phaseHalf dsp)) (level * hp * lp)

structure Driver where
  fs : ℚ
  vas : ℚ
  qes : ℚ
  qms : ℚ
  re : ℚ
  le : ℚ
  sd : ℚ

inductive Cavity where
  | sealed
  | vented (area length : ℚ) (quality : Option ℚ)
  | openUniformDuct (count area length inlet inertance compliance : ℚ) (quality : Option ℚ)
  | distributedDuct (path : DuctInterval.DuctPath) (quality : Option ℚ)
  | passive (count area mass compliance resistance : ℚ)

structure Circuit where
  driver : Driver
  volume : ℚ
  density : ℚ
  soundSpeed : ℚ
  count : ℚ := 1
  series : ℚ := 1
  leakage : Option ℚ := none
  absorption : Option ℚ := none
  cavity : Cavity := .sealed

structure Limits where
  excursion : Option ℚ := none
  mach : Option ℚ := none
  thermal : Option ℚ := none
  current : Option ℚ := none
  voltage : Option ℚ := none
  radiator : Option ℚ := none

structure Phasor where
  re : Expr
  im : Expr

def Phasor.ofReal (re : Expr) : Phasor := ⟨re, 0⟩
def Phasor.add (a b : Phasor) : Phasor := ⟨a.re + b.re, a.im + b.im⟩
def Phasor.mul (a b : Phasor) : Phasor :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def Phasor.magnitude (a : Phasor) : Expr := .sqrt (sq a.re + sq a.im)

structure Response where
  excursion : Expr
  current : Expr
  portMach : Expr
  radiatorExcursion : Expr

/-- The cleared small-signal circuit equations. All responses use one RMS
    volt at the amplifier terminals. -/
def response (input : Circuit) : Response := Id.run do
  let d := input.driver
  let density := q input.density
  let speed := q input.soundSpeed
  let count := q input.count
  let series := q input.series
  let parallel := q (input.count / input.series)
  let tau : Expr := 2 * .namedConst .pi
  let omega := tau * .var 0
  let fs := tau * q d.fs
  let rhoC2 := density * sq speed
  let cab := q input.volume / rhoC2
  let compliance := q d.vas / (rhoC2 * sq (q d.sd))
  let mass := 1 / (sq fs * compliance)
  let resistance := fs * mass / q d.qms
  let re := q d.re
  let blSquared := fs * mass * re / q d.qes
  let motorDrive := Expr.sqrt blSquared / series
  let coneArea := count * q d.sd
  let coupling := count * sq (q d.sd)
  let (characteristic, yPort, branch, areaTerm) :=
    match input.cavity with
    | .sealed =>
      (1 / (fs * cab * Expr.sqrt (1 + q (d.vas * input.count / input.volume))),
        Phasor.ofReal 0, Phasor.ofReal 1, (0 : Expr))
    | .vented area length quality =>
      let portMass := density * q (length / area)
      let char := Expr.sqrt (portMass / cab)
      let r := quality.elim 0 (fun value => char / q value)
      let x := omega * portMass
      let norm := sq r + sq x
      (char, ⟨r / norm, -x / norm⟩, Phasor.ofReal 1, 0)
    | .openUniformDuct count area length inlet inertance compliance quality =>
      let portMass := density * q ((inertance * length + inlet) / (count * area))
      let char := Expr.sqrt (portMass / cab)
      let resistance := quality.elim 0 (fun value => char / q value)
      let scale := Expr.sqrt (q (inertance * compliance))
      let phase := omega * scale * q length / speed
      let flow := Expr.cos phase
      let throat := q count * flow
      let inletReactance : Expr := if inlet = 0 then 0 else omega * q inlet * flow
      let reactance := density / q area *
        (speed * q inertance / scale * Expr.sin phase + inletReactance)
      (char, Phasor.ofReal 0, ⟨resistance * throat, reactance⟩, throat)
    | .distributedDuct _ quality =>
      let portMass := Expr.var 1
      let throat := Expr.var 2
      let r := quality.elim 0 (fun value => portMass / Expr.sqrt (portMass * cab) / q value)
      (Expr.sqrt (portMass / cab), Phasor.ofReal 0, ⟨r * throat, .var 3⟩, throat)
    | .passive count area mass compliance resistance =>
      let a := q (count * area * area)
      let z : Phasor := ⟨q resistance, omega * q mass - 1 / (omega * q compliance)⟩
      (.sqrt (q mass / (a * cab)), Phasor.ofReal 0, z, a)
  let loss (quality : Option ℚ) : Expr := quality.elim 0 (fun value => 1 / (q value * characteristic))
  let base := Phasor.add ⟨loss input.leakage + loss input.absorption, omega * cab⟩ yPort
  let admittance := match input.cavity with
    | .passive .. | .openUniformDuct .. | .distributedDuct .. => (base.mul branch).add (Phasor.ofReal areaTerm)
    | _ => base
  let mech := (Phasor.mul ⟨resistance, omega * mass - 1 / (omega * compliance)⟩ admittance).add
    ((Phasor.ofReal coupling).mul branch)
  let denom := ((Phasor.mul ⟨re, omega * q d.le⟩ mech).add
    ((Phasor.ofReal blSquared).mul admittance)).magnitude
  let peak := Expr.sqrt 2
  let cone := peak * motorDrive * admittance.magnitude / (denom * omega)
  let current := parallel / series * mech.magnitude / denom
  let mach := match input.cavity with
    | .vented area .. => peak * motorDrive * coneArea * yPort.magnitude / (denom * q area * speed)
    | .openUniformDuct _ area .. => peak * motorDrive * coneArea / (denom * q area * speed)
    | .distributedDuct .. => peak * motorDrive * coneArea * Expr.var 4 / (denom * speed)
    | _ => 0
  let travel := match input.cavity with
    | .passive count area .. => peak * motorDrive * coneArea * areaTerm / (denom * omega * q (count * area))
    | _ => 0
  return ⟨cone, current, mach, travel⟩

def factors (input : Circuit) (limits : Limits) (dsp : Dsp) : List Expr :=
  let r := response input
  let parallel := q (input.count / input.series)
  let gain := filterGain dsp
  ([ limits.voltage.map (fun value => 1 / q value),
    limits.excursion.map (fun value => r.excursion / q value),
    limits.mach.map (fun value => r.portMach / q value),
    limits.current.map (fun value => r.current / q value),
    limits.thermal.map (fun value => r.current * .sqrt (q (input.driver.re / value)) / parallel),
    limits.radiator.map (fun value => r.radiatorExcursion / q value) ].filterMap id).map
    (fun factor => gain * factor)

def config : DyadicConfig := { precision := -96, taylorDepth := 24 }

def evaluate (expr : Expr) (span : Box) : Option Box := do
  if h : span.lo ≤ span.hi then
    let result ← (evalIntervalDyadicChecked expr
      (toDyadicEnv (fun _ => ⟨span.lo, span.hi, h⟩) config.precision) config).toOption
    let box := result.toIntervalRat
    return ⟨box.lo, box.hi⟩
  else none

def intervalEnvelope (span : Box) : List Expr → Option Box
  | [] => some (Box.point 0)
  | expr :: rest => do
    let head ← evaluate expr span
    let tail ← intervalEnvelope span rest
    return head.joinMax tail

def exactEnvelope (f : ℝ) : List Expr → ℝ
  | [] => 0
  | expr :: rest => max (expr.eval (fun _ => f)) (exactEnvelope f rest)

theorem evaluate_sound (expr : Expr) (span out : Box) (evaluated : evaluate expr span = some out)
    (f : ℝ) (frequency : span.Contains f) : out.Contains (expr.eval (fun _ => f)) := by
  unfold evaluate at evaluated
  split at evaluated
  next ordered =>
    let input : IntervalRat := ⟨span.lo, span.hi, ordered⟩
    let env := toDyadicEnv (fun _ => input) config.precision
    cases heval : evalIntervalDyadicChecked expr env config with
    | error failure => simp [env, input, heval, Except.toOption] at evaluated
    | ok result =>
      have mem : envMemDyadic (fun _ => f) env := by
        intro _
        exact IntervalDyadic.mem_ofIntervalRat frequency _ (by decide)
      have trueValue := evalIntervalDyadicChecked_correct expr _ env mem config (by decide) result heval
      have equal : ⟨result.toIntervalRat.lo, result.toIntervalRat.hi⟩ = out := by
        simpa [env, input, heval, Except.toOption] using evaluated
      rw [← equal]
      exact IntervalDyadic.mem_toIntervalRat.mp trueValue
  next => contradiction

theorem envelope_sound (exprs : List Expr) :
    Encloses (fun span => intervalEnvelope span exprs) (fun f => exactEnvelope f exprs) := by
  intro span out evaluation f frequency
  induction exprs generalizing out with
  | nil =>
    simp only [intervalEnvelope, Option.some.injEq] at evaluation
    rw [← evaluation]
    simpa only [exactEnvelope, Rat.cast_zero] using point_sound 0
  | cons expr rest ih =>
    simp only [intervalEnvelope] at evaluation
    cases headEq : evaluate expr span with
    | none => simp [headEq] at evaluation
    | some head =>
      cases tailEq : intervalEnvelope span rest with
      | none => simp [headEq, tailEq] at evaluation
      | some tail =>
        simp only [headEq, tailEq] at evaluation
        change some (head.joinMax tail) = some out at evaluation
        rw [← Option.some.inj evaluation]
        exact max_sound (evaluate_sound expr span head headEq f frequency) (ih tail tailEq)

def tighten (enclose : Box → Option Box) (safe : ℚ) : Nat → Box → Option Box
  | 0, span => enclose span
  | fuel + 1, span =>
    let original := enclose span
    if decide (span.hi ≤ span.lo) || original.any (fun result => decide (safe * result.hi ≤ 1))
    then original
    else
      let middle := (span.lo + span.hi) / 2
      match tighten enclose safe fuel ⟨span.lo, middle⟩,
          tighten enclose safe fuel ⟨middle, span.hi⟩ with
      | some a, some b => some ⟨min a.lo b.lo, max a.hi b.hi⟩
      | _, _ => none

theorem tighten_sound {enclose : Box → Option Box} {usage : ℝ → ℝ}
    (valid : Encloses enclose usage) (safe : ℚ) (fuel : Nat) :
    Encloses (tighten enclose safe fuel) usage := by
  intro span out evaluated f frequency
  induction fuel generalizing span out with
  | zero => exact valid span out evaluated f frequency
  | succ fuel ih =>
    simp only [tighten] at evaluated
    split at evaluated
    · exact valid span out evaluated f frequency
    · let middle := (span.lo + span.hi) / 2
      let left : Box := ⟨span.lo, middle⟩
      let right : Box := ⟨middle, span.hi⟩
      change (match tighten enclose safe fuel left, tighten enclose safe fuel right with
        | some a, some b => some ⟨min a.lo b.lo, max a.hi b.hi⟩
        | _, _ => none) = some out at evaluated
      cases ha : tighten enclose safe fuel left with
      | none => simp [ha] at evaluated
      | some a =>
        cases hb : tighten enclose safe fuel right with
        | none => simp [ha, hb] at evaluated
        | some b =>
          simp only [ha, hb, Option.some.injEq] at evaluated
          rw [← evaluated]
          have haLo : (min a.lo b.lo : ℚ) ≤ a.lo := min_le_left _ _
          have haHi : a.hi ≤ (max a.hi b.hi : ℚ) := le_max_left _ _
          have hbLo : (min a.lo b.lo : ℚ) ≤ b.lo := min_le_right _ _
          have hbHi : b.hi ≤ (max a.hi b.hi : ℚ) := le_max_right _ _
          rcases le_total f (middle : ℝ) with first | second
          · have h := ih left a ha ⟨frequency.1, first⟩
            exact ⟨(Rat.cast_le.mpr haLo).trans h.1, h.2.trans (Rat.cast_le.mpr haHi)⟩
          · have h := ih right b hb ⟨second, frequency.2⟩
            exact ⟨(Rat.cast_le.mpr hbLo).trans h.1, h.2.trans (Rat.cast_le.mpr hbHi)⟩

/-- Duct transfer and circuit evaluation share one frequency. Extra variables
    stand for the distributed mass, throat flow, reactance, and spatial peak. -/
def inputs (frequency mass throat reactance peak : α) : ℕ → α
  | 0 => frequency
  | 1 => mass
  | 2 => throat
  | 3 => reactance
  | 4 => peak
  | _ => frequency

def replayPrecision : ℕ := 96

def logTen : Box := ⟨2.3025850925, 2.3025850935⟩

theorem logTen_sound : logTen.Contains (Real.log 10) := by
  constructor
  · convert Electroacoustics.Transcendentals.log_ten_bracket.1.le using 1; norm_num [logTen]
  · convert Electroacoustics.Transcendentals.log_ten_bracket.2.le using 1; norm_num [logTen]

def evalTrig (takeSine : Bool) (angle : Option Box) : Option Box := do
  let (sine, cosine) ← DuctInterval.boxTrig replayPrecision (← angle)
  DuctInterval.withBox (if takeSine then sine else cosine) some

theorem evalTrig_sound {angle : Option Box} {x : ℝ} (ha : DuctInterval.Approx angle x)
    (takeSine : Bool) : DuctInterval.Approx (evalTrig takeSine angle)
      (if takeSine then Real.sin x else Real.cos x) := by
  intro out h
  unfold evalTrig at h
  cases he : angle with
  | none => simp [he] at h
  | some box =>
    cases ht : DuctInterval.boxTrig replayPrecision box with
    | none => simp [he, ht] at h
    | some pair =>
      obtain ⟨sine, cosine⟩ := pair
      obtain ⟨hs, hc⟩ := DuctInterval.boxTrig_sound (ha box he) ht
      cases takeSine <;> simp [he, ht] at h ⊢ <;> subst out <;> assumption

/-- Evaluate the circuit's expression fragment with rounded rational boxes.
    Squares share their operand and use the nonnegative square enclosure. -/
def evaluateInputs (vars : ℕ → Box) : Expr → Option Box
  | .const q => some (Box.point q)
  | .var i => some (vars i)
  | .add a b => o.add (evaluateInputs vars a) (evaluateInputs vars b)
  | .mul a b =>
    if a = b then o.square (evaluateInputs vars a) else o.mul (evaluateInputs vars a) (evaluateInputs vars b)
  | .neg a => o.sub (o.rat 0) (evaluateInputs vars a)
  | .inv a => o.div (o.rat 1) (evaluateInputs vars a)
  | .sqrt a => o.sqrt (evaluateInputs vars a)
  | .exp a => o.exp (evaluateInputs vars a)
  | .log a => if a = .const 10 then some logTen else o.log (evaluateInputs vars a)
  | .sin a => evalTrig true (evaluateInputs vars a)
  | .cos a => evalTrig false (evaluateInputs vars a)
  | .namedConst .pi => some DuctInterval.piBox
  | _ => none
where
  o := DuctInterval.intervalArithmetic replayPrecision

theorem evaluateInputs_sound {vars : ℕ → Box} {values : ℕ → ℝ}
    (valid : ∀ i, (vars i).Contains (values i)) {expr : Expr} {out : Box}
    (eval : evaluateInputs vars expr = some out) : out.Contains (expr.eval values) := by
  open DuctInterval in
  have encloses : ∀ e : Expr, Approx (evaluateInputs vars e) (e.eval values) := by
    intro e
    induction e with
    | const q => exact Approx.rat replayPrecision q
    | var i => exact Approx.some (valid i)
    | add a b ha hb => exact Approx.add (p := replayPrecision) ha hb
    | mul a b ha hb =>
      by_cases he : a = b
      · subst b
        simp only [evaluateInputs, ite_true, Expr.eval]
        simpa only [evaluateInputs.o, realArithmetic, pow_two] using Approx.square (p := replayPrecision) ha
      · simp only [evaluateInputs, he, ite_false, Expr.eval]
        exact Approx.mul (p := replayPrecision) ha hb
    | neg a ha =>
      simpa only [evaluateInputs, evaluateInputs.o, Expr.eval, realArithmetic, Rat.cast_zero, zero_sub]
        using Approx.sub (p := replayPrecision) (Approx.rat replayPrecision 0) ha
    | inv a ha =>
      simpa only [evaluateInputs, evaluateInputs.o, Expr.eval, realArithmetic, Rat.cast_one, one_div]
        using Approx.div (p := replayPrecision) (Approx.rat replayPrecision 1) ha
    | sqrt a ha => exact Approx.sqrt (p := replayPrecision) ha
    | exp a ha => exact Approx.exp (p := replayPrecision) ha
    | log a ha =>
      by_cases he : a = .const 10
      · subst a
        simpa only [evaluateInputs, ite_true, Expr.eval, Rat.cast_ofNat] using Approx.some logTen_sound
      · simp only [evaluateInputs, he, ite_false, Expr.eval]
        exact Approx.log (p := replayPrecision) ha
    | sin a ha => exact evalTrig_sound ha true
    | cos a ha => exact evalTrig_sound ha false
    | namedConst c =>
      cases c
      · exact Approx.pi replayPrecision
      · simp [Approx, evaluateInputs]
    | _ => simp [Approx, evaluateInputs]
  exact encloses expr out eval

def intervalEnvelopeWith (evaluateExpr : Expr → Option Box) : List Expr → Option Box
  | [] => some (Box.point 0)
  | expr :: rest => do
    let head ← evaluateExpr expr
    let tail ← intervalEnvelopeWith evaluateExpr rest
    return head.joinMax tail

def exactEnvelopeWith (values : ℕ → ℝ) : List Expr → ℝ
  | [] => 0
  | expr :: rest => max (expr.eval values) (exactEnvelopeWith values rest)

theorem envelopeWith_sound {evaluateExpr : Expr → Option Box} {values : ℕ → ℝ}
    (valid : ∀ expr out, evaluateExpr expr = some out → out.Contains (expr.eval values))
    {exprs : List Expr} {out : Box} (eval : intervalEnvelopeWith evaluateExpr exprs = some out) :
    out.Contains (exactEnvelopeWith values exprs) := by
  induction exprs generalizing out with
  | nil =>
    simp [intervalEnvelopeWith] at eval
    subst out
    simpa [exactEnvelopeWith] using point_sound 0
  | cons expr rest ih =>
    cases he : evaluateExpr expr with
    | none => simp [intervalEnvelopeWith, he] at eval
    | some head =>
      cases ht : intervalEnvelopeWith evaluateExpr rest with
      | none => simp [intervalEnvelopeWith, he, ht] at eval
      | some tail =>
        simp only [intervalEnvelopeWith, he] at eval
        change (do let b ← intervalEnvelopeWith evaluateExpr rest; some (head.joinMax b)) = _ at eval
        simp [ht] at eval
        subst out
        exact max_sound (valid _ _ he) (ih ht)

def ductSpeeds (path : DuctInterval.DuctPath) (speed density f : ℝ) : Set ℝ :=
  {v | ∃ i < path.sections.length, ∃ x ∈ Set.Icc (0 : ℝ) 1,
    v = DuctInterval.exactSectionSpeed path speed density f i x}

def exactDuctPeak (path : DuctInterval.DuctPath) (speed density f : ℝ) : ℝ :=
  sSup (ductSpeeds path speed density f)

def exactDuctInputs (path : DuctInterval.DuctPath) (input : Circuit) (limits : Limits) (f : ℝ) :
    ℕ → ℝ :=
  let state := DuctInterval.exactDuctState path input.soundSpeed input.density f
  inputs f (DuctInterval.exactDcMass path input.soundSpeed input.density)
    ((path.count : ℝ) * state.2) (2 * Real.pi * f * state.1)
    (limits.mach.elim 0 fun _ => exactDuctPeak path input.soundSpeed input.density f)

def exactUsage (input : Circuit) (limits : Limits) (dsp : Dsp) (f : ℝ) : ℝ :=
  match input.cavity with
  | .distributedDuct path _ =>
    exactEnvelopeWith (exactDuctInputs path input limits f) (factors input limits dsp)
  | _ => exactEnvelope f (factors input limits dsp)

def evalDuctPeak (limits : Limits) (positions : List (Box → Option Box)) (fuel : ℕ)
    (includeThroat : Bool) : Option Box :=
  match limits.mach with
  | none => some (Box.point 0)
  | some _ => (DuctInterval.spatialPeak positions fuel includeThroat).map fun (witness, upper) => ⟨witness.value.lo, upper⟩

def evalDuctInputs (path : DuctInterval.DuctPath) (input : Circuit) (limits : Limits)
    (fuel : ℕ) (includeThroat : Bool) (span : Box) : Option (ℕ → Box) := do
  let p := replayPrecision
  let mass ← DuctInterval.evalDuctDcMass p path input.soundSpeed input.density
  let (numerator, denominator, positions) ← DuctInterval.evalDuctResponse p path input.soundSpeed input.density span
  let peak ← evalDuctPeak limits positions fuel includeThroat
  let throat := DuctInterval.mul p (Box.point path.count) denominator
  let omega := DuctInterval.mul p (DuctInterval.mul p (Box.point 2) DuctInterval.piBox) span
  let reactance := DuctInterval.mul p omega numerator
  return inputs span mass throat reactance peak

theorem evalDuctPeak_sound (limits : Limits) {path : DuctInterval.DuctPath}
    {speed density : ℚ} {span numerator denominator out : Box} {positions : List (Box → Option Box)}
    {fuel : ℕ} {includeThroat : Bool}
    (response : DuctInterval.evalDuctResponse replayPrecision path speed density span =
      some (numerator, denominator, positions))
    (eval : evalDuctPeak limits positions fuel includeThroat = some out) {f : ℝ} (hf : span.Contains f) :
    out.Contains (limits.mach.elim 0 fun _ => exactDuctPeak path speed density f) := by
  cases hm : limits.mach with
  | none =>
    simp [evalDuctPeak, hm] at eval ⊢
    subst out
    simpa using point_sound 0
  | some rating =>
    cases hp : DuctInterval.spatialPeak positions fuel includeThroat with
    | none => simp [evalDuctPeak, hm, hp] at eval
    | some result =>
      obtain ⟨witness, upper⟩ := result
      simp [evalDuctPeak, hm, hp] at eval ⊢
      subst out
      obtain ⟨⟨index, fraction, lower⟩, bound⟩ :=
        DuctInterval.spatialPeak_sound (DuctInterval.ductPositions_sound response) hp
      have len := DuctInterval.ductPositions_length response hf
      let speeds := ductSpeeds path speed density f
      have member : DuctInterval.exactSectionSpeed path speed density f witness.index witness.fraction ∈ speeds := by
        refine ⟨witness.index, len ▸ index, witness.fraction, ?_, rfl⟩
        simpa [DuctInterval.fractionUnit, Box.Contains, Set.mem_Icc] using fraction
      have bounded : ∀ v ∈ speeds, v ≤ (upper : ℝ) := by
        rintro _ ⟨i, hi, x, hx, rfl⟩
        apply bound f hf i (len.symm ▸ hi) x
        simpa [DuctInterval.fractionUnit, Box.Contains, Set.mem_Icc] using hx
      exact ⟨(lower f hf).1.trans (le_csSup ⟨_, bounded⟩ member), csSup_le ⟨_, member⟩ bounded⟩

theorem evalDuctInputs_sound {path : DuctInterval.DuctPath} {input : Circuit} {limits : Limits}
    {span : Box} {vars : ℕ → Box} {fuel : ℕ} {includeThroat : Bool}
    (eval : evalDuctInputs path input limits fuel includeThroat span = some vars)
    {f : ℝ} (hf : span.Contains f) : ∀ i, (vars i).Contains (exactDuctInputs path input limits f i) := by
  unfold evalDuctInputs at eval
  cases hmass : DuctInterval.evalDuctDcMass replayPrecision path input.soundSpeed input.density with
  | none => simp [hmass] at eval
  | some mass =>
    cases he : DuctInterval.evalDuctResponse replayPrecision path input.soundSpeed input.density span with
    | none => simp [hmass, he] at eval
    | some result =>
      obtain ⟨n, d, positions⟩ := result
      cases hp : evalDuctPeak limits positions fuel includeThroat with
      | none => simp [hmass, he, hp] at eval
      | some peak =>
        simp [hmass, he, hp] at eval
        subst vars
        have ⟨hn, hd, _⟩ := DuctInterval.evalDuctResponse_sound he hf
        have ht := roundOut_sound (mul_sound (point_sound path.count) hd) replayPrecision
        have hω := roundOut_sound (mul_sound
          (roundOut_sound (mul_sound (point_sound 2) DuctInterval.piBox_sound) replayPrecision) hf) replayPrecision
        have hr := roundOut_sound (mul_sound hω hn) replayPrecision
        intro i
        match i with
        | 0 => exact hf
        | 1 => exact DuctInterval.evalDuctDcMass_sound hmass
        | 2 => exact ht
        | 3 => simpa only [inputs, exactDuctInputs, DuctInterval.mul, Rat.cast_ofNat] using hr
        | 4 => exact evalDuctPeak_sound limits he hp hf
        | _ + 5 => exact hf

def modelEnvelope (input : Circuit) (limits : Limits) (dsp : Dsp) (span : Box)
    (fuel : ℕ := 64) (includeThroat : Bool := false) : Option Box :=
  match input.cavity with
  | .distributedDuct path _ => do
    let vars ← evalDuctInputs path input limits fuel includeThroat span
    intervalEnvelopeWith (evaluateInputs vars) (factors input limits dsp)
  | _ => intervalEnvelopeWith (evaluateInputs (fun _ => span)) (factors input limits dsp)

theorem exactEnvelopeWith_frequency (f : ℝ) (exprs : List Expr) :
    exactEnvelopeWith (fun _ => f) exprs = exactEnvelope f exprs := by
  induction exprs with
  | nil => rfl
  | cons e tail ih => simp only [exactEnvelopeWith, exactEnvelope, ih]

theorem modelEnvelope_sound (input : Circuit) (limits : Limits) (dsp : Dsp)
    (fuel : ℕ) (includeThroat : Bool) :
    Encloses (fun span => modelEnvelope input limits dsp span fuel includeThroat)
      (exactUsage input limits dsp) := by
  intro span out eval f hf
  cases hc : input.cavity with
  | distributedDuct path quality =>
    cases he : evalDuctInputs path input limits fuel includeThroat span with
    | none => simp [modelEnvelope, hc, he] at eval
    | some vars =>
      simp [modelEnvelope, hc, he] at eval
      simp only [exactUsage, hc]
      exact envelopeWith_sound (fun _ _ h => evaluateInputs_sound (evalDuctInputs_sound he hf) h) eval
  | sealed | vented | openUniformDuct | passive =>
    simp only [modelEnvelope, hc] at eval
    simp only [exactUsage, hc]
    rw [← exactEnvelopeWith_frequency]
    exact envelopeWith_sound (fun _ _ h => evaluateInputs_sound (fun _ => hf) h) eval

/-- A singleton only needs a lower witness. Try both ends before performing
    spatial subdivision, while keeping the full search for interior extrema. -/
def replayEnvelope (input : Circuit) (limits : Limits) (dsp : Dsp) (safe upper : ℚ)
    (span : Box) : Option Box :=
  let full := tighten (fun b => modelEnvelope input limits dsp b) safe 3 span
  match input.cavity with
  | .distributedDuct .. =>
    if span.lo = span.hi then
      let endpoints := modelEnvelope input limits dsp span 0 true
      if endpoints.any (fun bound => decide (1 ≤ upper * bound.lo)) then endpoints else full
    else full
  | _ => full

theorem replayEnvelope_sound (input : Circuit) (limits : Limits) (dsp : Dsp) (safe upper : ℚ) :
    Encloses (replayEnvelope input limits dsp safe upper) (exactUsage input limits dsp) := by
  intro span out eval f hf
  have full := tighten_sound (modelEnvelope_sound input limits dsp 64 false) safe 3 span out
  cases hc : input.cavity with
  | distributedDuct path quality =>
    simp only [replayEnvelope, hc] at eval
    split at eval
    · split at eval
      · exact modelEnvelope_sound input limits dsp 0 true _ _ eval f hf
      · exact full eval f hf
    · exact full eval f hf
  | sealed | vented | openUniformDuct | passive =>
    exact full (by simpa only [replayEnvelope, hc] using eval) f hf

def checkModel (input : Circuit) (limits : Limits) (dsp : Dsp) (band : Box) (tolerance : ℚ)
    (cert : Certificate) : Bool :=
  check (replayEnvelope input limits dsp cert.safe cert.upper) band 2.3025850925 tolerance cert

theorem checkModel_of_checks {input : Circuit} {limits : Limits} {dsp : Dsp} {band : Box}
    {tolerance : ℚ} {cert : Certificate}
    (witness : checkWitness (replayEnvelope input limits dsp cert.safe cert.upper) band 2.3025850925
      tolerance cert = true)
    (cover : checkSpans (replayEnvelope input limits dsp cert.safe cert.upper) cert.safe band.lo band.hi cert.spans = true) :
    checkModel input limits dsp band tolerance cert = true :=
  check_of_checks witness cover

theorem checkModel_sound (input : Circuit) (limits : Limits) (dsp : Dsp)
    {band : Box} (nonempty : band.lo < band.hi) {tolerance : ℚ} {cert : Certificate}
    (verified : checkModel input limits dsp band tolerance cert = true) :
    let u := exactUsage input limits dsp
    (∀ f, band.Contains f → (cert.safe : ℝ) * u f ≤ 1) ∧
    (∀ drive : ℝ, (cert.upper : ℝ) < drive → ∃ f, band.Contains f ∧ 1 < drive * u f) ∧
    (∀ drive : ℝ, (cert.safe : ℝ) ≤ drive → drive ≤ (cert.upper : ℝ) →
      20 / Real.log 10 * Real.log (drive / (cert.safe : ℝ)) ≤ (cert.errorDb : ℝ)) := by
  apply check_sound (replayEnvelope_sound _ _ _ _ _) nonempty _ verified
  push_cast
  exact Electroacoustics.Transcendentals.log_ten_bracket.1.le

end Electroacoustics.BandModel

open Lean Electroacoustics.BandModel in
run_cmd do
  let theorems := #[``evaluate_sound, ``envelope_sound, ``tighten_sound, ``logTen_sound, ``evaluateInputs_sound,
    ``evalTrig_sound, ``envelopeWith_sound, ``evalDuctPeak_sound, ``evalDuctInputs_sound,
    ``exactEnvelopeWith_frequency, ``modelEnvelope_sound,
    ``replayEnvelope_sound, ``checkModel_of_checks, ``checkModel_sound,
    ``Electroacoustics.BandCertificate.checkPartial_sound,
    ``Electroacoustics.DuctInterval.boxSqrt_sound, ``Electroacoustics.DuctInterval.boxExp_sound,
    ``Electroacoustics.DuctInterval.boxLogRatio_sound, ``Electroacoustics.DuctInterval.boxWave_sound, ``Electroacoustics.DuctInterval.boxTrig_sound,
    ``Electroacoustics.DuctInterval.evalDuctResponse_sound, ``Electroacoustics.DuctInterval.evalDuctDcMass_sound,
    ``Electroacoustics.DuctInterval.evalDuctSpatialPeak_sound,
    ``Electroacoustics.DuctInterval.evalDuctTuningResidual_sound]
  for name in theorems do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun dependency =>
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains dependency)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms: {unexpected}"
  logInfo m!"Audited axioms for {theorems.size} independent band certificate theorems."
