module

public import Electroacoustics.Interval
public import Electroacoustics.Numerics
public import Electroacoustics.Transcendentals
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.ImpedanceCertificate

open Electroacoustics.Interval
open Electroacoustics.Numerics
open Matrix
open scoped BigOperators

def mulBox (prec : ℕ) (a b : Box) : Box := (a.mul b).roundOut prec

def squareBox (prec : ℕ) (a : Box) : Box := a.square.roundOut prec

def reciprocalBox (prec : ℕ) (a : Box) : Option Box :=
  a.reciprocal.map (·.roundOut prec)

theorem mulBox_sound {prec : ℕ} {a b : Box} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) : (mulBox prec a b).Contains (x * y) :=
  roundOut_sound (mul_sound ha hb) prec

theorem squareBox_sound {prec : ℕ} {a : Box} {x : ℝ} (ha : a.Contains x) :
    (squareBox prec a).Contains (x ^ 2) :=
  roundOut_sound (square_sound ha) prec

theorem reciprocalBox_sound {prec : ℕ} {a b : Box} {x : ℝ} (ha : a.Contains x)
    (h : reciprocalBox prec a = some b) : b.Contains (1 / x) ∧ x ≠ 0 := by
  unfold reciprocalBox at h
  cases hr : a.reciprocal with
  | none => simp [hr] at h
  | some raw =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    refine ⟨h ▸ roundOut_sound (reciprocal_sound ha hr) prec, ?_⟩
    apply not_containsZero_ne_zero _ ha
    intro ⟨lo, hi⟩
    simp [Box.reciprocal, not_lt.mpr hi, not_lt.mpr lo] at hr

def divBox (prec : ℕ) (a b : Box) : Option Box :=
  (reciprocalBox prec b).map (mulBox prec a)

theorem divBox_sound {prec : ℕ} {a b out : Box} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) (h : divBox prec a b = some out) :
    out.Contains (x / y) := by
  obtain ⟨inv, hinv, hout⟩ := Option.map_eq_some_iff.mp h
  rw [← hout, ← mul_one_div]
  exact mulBox_sound ha (reciprocalBox_sound hb hinv).1

/-- Integer square root proposes dyadic endpoints. Squaring the proposed
    endpoints independently validates the enclosure. -/
def rootCandidate (prec : ℕ) (a : Box) : Box :=
  let scale : ℚ := 2 ^ prec
  let lo := (⌊a.lo * scale ^ 2⌋.toNat).sqrt
  let hi := (⌊a.hi * scale ^ 2⌋.toNat).sqrt
  let upper := if a.hi ≤ ((hi : ℚ) / scale) ^ 2 then hi else hi + 1
  ⟨(lo : ℚ) / scale, (upper : ℚ) / scale⟩

def rootBox (prec : ℕ) (a : Box) : Option Box :=
  let out := rootCandidate prec a
  if a.checkRoot out then some out else none

theorem rootBox_sound {prec : ℕ} {a out : Box} {x : ℝ} (ha : a.Contains x)
    (h : rootBox prec a = some out) : out.Contains (Real.sqrt x) := by
  unfold rootBox at h
  dsimp only at h
  by_cases accepted : a.checkRoot (rootCandidate prec a) = true
  · simp [accepted] at h
    rw [← h]
    exact root_sound ha accepted
  · simp [accepted] at h

structure DualBox where
  val : Box
  der : List Box

def zeroBox : Box := Box.point 0

def DualBox.partial (a : DualBox) (i : ℕ) : Box := a.der.getD i zeroBox

def dualOf (p : ℕ) (val : Box) (der : Fin p → Box) : DualBox :=
  ⟨val, List.ofFn der⟩

@[simp] private theorem dualOf_partial {p : ℕ} (val : Box) (der : Fin p → Box) (i : Fin p) :
    (dualOf p val der).partial i = der i := by
  simp [dualOf, DualBox.partial, List.getD_eq_getElem?_getD, i.isLt]

def dualConst (p : ℕ) (val : Box) : DualBox := dualOf p val (fun _ => zeroBox)

def dualSeed {p : ℕ} (prec : ℕ) (value width : ℚ) (i : Fin p) : DualBox :=
  dualOf p ((Box.point value).roundOut prec) (fun j =>
    (Box.point (if i = j then width else 0)).roundOut prec)

def dualAdd (p : ℕ) (a b : DualBox) : DualBox :=
  dualOf p (a.val.add b.val) (fun i => (a.partial i).add (b.partial i))

def dualSub (p : ℕ) (a b : DualBox) : DualBox :=
  dualOf p (a.val.sub b.val) (fun i => (a.partial i).sub (b.partial i))

def dualMul (p prec : ℕ) (a b : DualBox) : DualBox :=
  dualOf p (mulBox prec a.val b.val) (fun i =>
    (mulBox prec (a.partial i) b.val).add (mulBox prec a.val (b.partial i)))

def dualDiv (p prec : ℕ) (a b : DualBox) : Option DualBox :=
  (reciprocalBox prec b.val).map fun inv =>
    let val := mulBox prec a.val inv
    dualOf p val (fun i =>
      mulBox prec ((a.partial i).sub (mulBox prec val (b.partial i))) inv)

def dualSquare (p prec : ℕ) (a : DualBox) : DualBox :=
  dualOf p (squareBox prec a.val) (fun i =>
    mulBox prec (mulBox prec (Box.point 2) a.val) (a.partial i))

def dualSqrt (p prec : ℕ) (a : DualBox) : Option DualBox :=
  if a.val.lo ≤ 0 then none else
    (rootBox prec a.val).bind fun val =>
      (reciprocalBox prec (mulBox prec (Box.point 2) val)).map fun inv =>
        dualOf p val (fun i => mulBox prec (a.partial i) inv)

/-- Enclose the value at the center and the exact derivative along each
    coordinate line through that center. -/
def DualBox.Encloses {p : ℕ} (a : DualBox) (value : ℝ) (along : Fin p → ℝ → ℝ) : Prop :=
  a.val.Contains value ∧ ∀ i : Fin p, ∃ d, (a.partial i).Contains d ∧ HasDerivAt (along i) d 0

theorem dualConst_sound {p : ℕ} {val : Box} {x : ℝ} (h : val.Contains x) :
    (dualConst p val).Encloses x (fun _ : Fin p => fun _ => x) := by
  refine ⟨h, fun i => ⟨0, ?_, hasDerivAt_const 0 x⟩⟩
  rw [dualConst, dualOf_partial]
  simpa [zeroBox] using point_sound (0 : ℚ)

theorem dualSeed_sound {p prec : ℕ} (value width : ℚ) (i : Fin p) :
    (dualSeed prec value width i).Encloses (value : ℝ) (fun j t =>
      (value : ℝ) + ((if i = j then width else 0 : ℚ) : ℝ) * t) := by
  refine ⟨roundOut_sound (point_sound _) _, fun j => ⟨((if i = j then width else 0 : ℚ) : ℝ), ?_, ?_⟩⟩
  · rw [dualSeed, dualOf_partial]
    exact roundOut_sound (point_sound _) _
  · simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul
      (((if i = j then width else 0 : ℚ) : ℝ))).const_add (value : ℝ)

theorem dualAdd_sound {p : ℕ} {a b : DualBox} {x y : ℝ} {f g : Fin p → ℝ → ℝ}
    (ha : a.Encloses x f) (hb : b.Encloses y g) :
    (dualAdd p a b).Encloses (x + y) (fun i t => f i t + g i t) := by
  refine ⟨add_sound ha.1 hb.1, ?_⟩
  intro i
  obtain ⟨da, ad, af⟩ := ha.2 i
  obtain ⟨db, bd, bf⟩ := hb.2 i
  refine ⟨da + db, ?_, af.add bf⟩
  rw [dualAdd, dualOf_partial]
  exact add_sound ad bd

theorem dualSub_sound {p : ℕ} {a b : DualBox} {x y : ℝ} {f g : Fin p → ℝ → ℝ}
    (ha : a.Encloses x f) (hb : b.Encloses y g) :
    (dualSub p a b).Encloses (x - y) (fun i t => f i t - g i t) := by
  refine ⟨sub_sound ha.1 hb.1, ?_⟩
  intro i
  obtain ⟨da, ad, af⟩ := ha.2 i
  obtain ⟨db, bd, bf⟩ := hb.2 i
  refine ⟨da - db, ?_, af.sub bf⟩
  rw [dualSub, dualOf_partial]
  exact sub_sound ad bd

theorem dualMul_sound {p prec : ℕ} {a b : DualBox} {x y : ℝ} {f g : Fin p → ℝ → ℝ}
    (ha : a.Encloses x f) (hb : b.Encloses y g) (hf : ∀ i, f i 0 = x) (hg : ∀ i, g i 0 = y) :
    (dualMul p prec a b).Encloses (x * y) (fun i t => f i t * g i t) := by
  refine ⟨mulBox_sound ha.1 hb.1, ?_⟩
  intro i
  obtain ⟨da, ad, af⟩ := ha.2 i
  obtain ⟨db, bd, bf⟩ := hb.2 i
  refine ⟨da * y + x * db, ?_, ?_⟩
  · rw [dualMul, dualOf_partial]
    exact add_sound (mulBox_sound ad hb.1) (mulBox_sound ha.1 bd)
  · simpa only [hf i, hg i] using af.fun_mul bf

theorem dualDiv_sound {p prec : ℕ} {a b out : DualBox} {x y : ℝ} {f g : Fin p → ℝ → ℝ}
    (ha : a.Encloses x f) (hb : b.Encloses y g) (hf : ∀ i, f i 0 = x) (hg : ∀ i, g i 0 = y)
    (h : dualDiv p prec a b = some out) :
    out.Encloses (x / y) (fun i t => f i t / g i t) := by
  unfold dualDiv at h
  obtain ⟨inv, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨invSound, yn⟩ := reciprocalBox_sound hb.1 hi
  have valSound : (mulBox prec a.val inv).Contains (x / y) := by
    rw [← mul_one_div]
    exact mulBox_sound ha.1 invSound
  refine ⟨valSound, ?_⟩
  intro i
  obtain ⟨da, ad, af⟩ := ha.2 i
  obtain ⟨db, bd, bf⟩ := hb.2 i
  refine ⟨(da - x / y * db) * (1 / y), ?_, ?_⟩
  · rw [dualOf_partial]
    exact mulBox_sound (sub_sound ad (mulBox_sound valSound bd)) invSound
  · have d := af.div bf (hg i ▸ yn)
    rw [hf i, hg i] at d
    convert d using 1
    field_simp

theorem dualSquare_sound {p prec : ℕ} {a : DualBox} {x : ℝ} {f : Fin p → ℝ → ℝ}
    (ha : a.Encloses x f) (hf : ∀ i, f i 0 = x) :
    (dualSquare p prec a).Encloses (x ^ 2) (fun i t => f i t ^ 2) := by
  refine ⟨squareBox_sound ha.1, ?_⟩
  intro i
  obtain ⟨da, ad, af⟩ := ha.2 i
  refine ⟨2 * x * da, ?_, ?_⟩
  · rw [dualSquare, dualOf_partial]
    have two : (Box.point 2).Contains (2 : ℝ) := by simpa using point_sound (2 : ℚ)
    exact mulBox_sound (mulBox_sound two ha.1) ad
  · simpa [hf i] using af.fun_pow 2

theorem dualSqrt_sound {p prec : ℕ} {a out : DualBox} {x : ℝ} {f : Fin p → ℝ → ℝ}
    (ha : a.Encloses x f) (hf : ∀ i, f i 0 = x) (h : dualSqrt p prec a = some out) :
    out.Encloses (Real.sqrt x) (fun i t => Real.sqrt (f i t)) := by
  unfold dualSqrt at h
  split at h
  · contradiction
  · rename_i positive
    obtain ⟨val, hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨inv, hi, rfl⟩ := Option.map_eq_some_iff.mp h
    have valSound := rootBox_sound ha.1 hv
    have two : (Box.point 2).Contains (2 : ℝ) := by simpa using point_sound (2 : ℚ)
    have invSound := (reciprocalBox_sound (mulBox_sound (prec := prec) two valSound) hi).1
    have xp : 0 < x := (Rat.cast_pos.mpr (lt_of_not_ge positive)).trans_le ha.1.1
    refine ⟨valSound, ?_⟩
    intro i
    obtain ⟨da, ad, af⟩ := ha.2 i
    refine ⟨da * (1 / (2 * Real.sqrt x)), ?_, ?_⟩
    · rw [dualOf_partial]
      exact mulBox_sound ad invSound
    · simpa only [hf i, mul_one_div] using af.sqrt (hf i ▸ xp.ne')

/-- A rational bracket tighter than the binary64 bracket used by the runtime. -/
def piBox : Box := ⟨3.14159265358979323846, 3.14159265358979323847⟩

theorem piBox_sound : piBox.Contains Real.pi := by
  exact ⟨by simpa [piBox] using Real.pi_gt_d20.le, by simpa [piBox] using Real.pi_lt_d20.le⟩

structure Coordinate where
  lo : ℚ
  hi : ℚ
  value : ℚ

def Coordinate.normalized (c : Coordinate) : ℝ :=
  ((c.value : ℝ) - c.lo) / ((c.hi : ℝ) - c.lo)

def Coordinate.unscale (c : Coordinate) (u : ℝ) : ℝ :=
  (c.lo : ℝ) + u * ((c.hi : ℝ) - c.lo)

theorem Coordinate.unscale_shift {c : Coordinate} (width : c.lo < c.hi) (t : ℝ) :
    c.unscale (c.normalized + t) = (c.value : ℝ) + ((c.hi : ℝ) - c.lo) * t := by
  have hw : (c.hi : ℝ) - c.lo ≠ 0 := (sub_pos.mpr (Rat.cast_lt.mpr width)).ne'
  rw [Coordinate.unscale, Coordinate.normalized, add_mul, div_mul_cancel₀ _ hw]
  ring

inductive Expr (p : ℕ) where
  | constant (q : ℚ)
  | parameter (i : Fin p)
  | pi
  | add (a b : Expr p)
  | sub (a b : Expr p)
  | mul (a b : Expr p)
  | div (a b : Expr p)
  | square (a : Expr p)
  | sqrt (a : Expr p)

instance : Add (Expr p) := ⟨Expr.add⟩
instance : Sub (Expr p) := ⟨Expr.sub⟩
instance : Mul (Expr p) := ⟨Expr.mul⟩
instance : Div (Expr p) := ⟨Expr.div⟩
instance (n : ℕ) : OfNat (Expr p) n := ⟨Expr.constant n⟩

def Expr.real (values : Fin p → ℝ) : Expr p → ℝ
  | .constant q => q
  | .parameter i => values i
  | .pi => Real.pi
  | .add a b => a.real values + b.real values
  | .sub a b => a.real values - b.real values
  | .mul a b => a.real values * b.real values
  | .div a b => a.real values / b.real values
  | .square a => a.real values ^ 2
  | .sqrt a => Real.sqrt (a.real values)

def Expr.evalBox (prec : ℕ) (coords : Fin p → Coordinate) : Expr p → Option DualBox
  | .constant q => some (dualConst p ((Box.point q).roundOut prec))
  | .parameter i => some (dualSeed prec (coords i).value ((coords i).hi - (coords i).lo) i)
  | .pi => some (dualConst p piBox)
  | .add a b =>
    (a.evalBox prec coords).bind fun x =>
      (b.evalBox prec coords).map (dualAdd p x)
  | .sub a b =>
    (a.evalBox prec coords).bind fun x =>
      (b.evalBox prec coords).map (dualSub p x)
  | .mul a b =>
    (a.evalBox prec coords).bind fun x =>
      (b.evalBox prec coords).map (dualMul p prec x)
  | .div a b =>
    (a.evalBox prec coords).bind fun x =>
      (b.evalBox prec coords).bind (dualDiv p prec x)
  | .square a => (a.evalBox prec coords).map (dualSquare p prec)
  | .sqrt a => (a.evalBox prec coords).bind (dualSqrt p prec)

def Expr.center (coords : Fin p → Coordinate) (e : Expr p) : ℝ :=
  e.real (fun i => (coords i).value)

def Expr.along (coords : Fin p → Coordinate) (e : Expr p) (j : Fin p) (t : ℝ) : ℝ :=
  e.real (fun i => (coords i).value +
    (((if i = j then (coords i).hi - (coords i).lo else 0) : ℚ) : ℝ) * t)

@[simp] theorem Expr.along_zero (coords : Fin p → Coordinate) (e : Expr p) (i : Fin p) :
    e.along coords i 0 = e.center coords := by simp [Expr.along, Expr.center]

/-- The derivative line changes exactly one normalized fit coordinate. -/
theorem Expr.along_eq_normalized (coords : Fin p → Coordinate) (e : Expr p)
    (width : ∀ i, (coords i).lo < (coords i).hi) (j : Fin p) (t : ℝ) :
    e.along coords j t = e.real (fun i =>
      (coords i).unscale ((coords i).normalized + if i = j then t else 0)) := by
  unfold along
  congr 1
  funext i
  rw [Coordinate.unscale_shift (width i)]
  by_cases h : i = j <;> simp [h]

theorem Expr.evalBox_sound (e : Expr p) {prec : ℕ} {coords : Fin p → Coordinate}
    {out : DualBox} (h : e.evalBox prec coords = some out) :
    out.Encloses (e.center coords) (e.along coords) := by
  induction e generalizing out with
  | constant q =>
    cases h
    exact dualConst_sound (roundOut_sound (point_sound q) prec)
  | parameter i =>
    cases h
    exact dualSeed_sound (coords i).value _ i
  | pi =>
    cases h
    exact dualConst_sound piBox_sound
  | add a b ia ib =>
    simp only [evalBox, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨da, ha, db, hb, rfl⟩ := h
    exact dualAdd_sound (ia ha) (ib hb)
  | sub a b ia ib =>
    simp only [evalBox, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨da, ha, db, hb, rfl⟩ := h
    exact dualSub_sound (ia ha) (ib hb)
  | mul a b ia ib =>
    simp only [evalBox, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨da, ha, db, hb, rfl⟩ := h
    exact dualMul_sound (ia ha) (ib hb) (a.along_zero coords) (b.along_zero coords)
  | div a b ia ib =>
    simp only [evalBox, Option.bind_eq_some_iff] at h
    obtain ⟨da, ha, db, hb, hd⟩ := h
    exact dualDiv_sound (ia ha) (ib hb) (a.along_zero coords) (b.along_zero coords) hd
  | square a ia =>
    simp only [evalBox, Option.map_eq_some_iff] at h
    obtain ⟨da, ha, rfl⟩ := h
    exact dualSquare_sound (ia ha) (a.along_zero coords)
  | sqrt a ia =>
    simp only [evalBox, Option.bind_eq_some_iff] at h
    obtain ⟨da, ha, hs⟩ := h
    exact dualSqrt_sound (ia ha) (a.along_zero coords) hs

structure Phasor (p : ℕ) where
  re : Expr p
  im : Expr p

def Phasor.ofReal (re : Expr p) : Phasor p := ⟨re, 0⟩

def Phasor.add (a b : Phasor p) : Phasor p := ⟨a.re + b.re, a.im + b.im⟩

def Phasor.mul (a b : Phasor p) : Phasor p :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

def Phasor.normSq (a : Phasor p) : Expr p := a.re.square + a.im.square

def Phasor.div (a b : Phasor p) : Phasor p :=
  let numerator := a.mul ⟨b.re, 0 - b.im⟩
  let denominator := b.normSq
  ⟨numerator.re / denominator, numerator.im / denominator⟩

def Phasor.mag (a : Phasor p) : Expr p := a.normSq.sqrt

def Phasor.complex (a : Phasor p) (values : Fin p → ℝ) : ℂ :=
  ⟨a.re.real values, a.im.real values⟩

theorem Phasor.div_complex (a b : Phasor p) (values : Fin p → ℝ) :
    (a.div b).complex values = a.complex values / b.complex values := by
  let ar := a.re.real values
  let ai := a.im.real values
  let br := b.re.real values
  let bi := b.im.real values
  apply Complex.ext
  · change (ar * br - ai * (((0 : ℚ) : ℝ) - bi)) / (br ^ 2 + bi ^ 2) =
      (Complex.mk ar ai / Complex.mk br bi).re
    simp only [Complex.div_re, Complex.normSq_apply, pow_two, Rat.cast_zero, zero_sub, mul_neg,
      sub_neg_eq_add, add_div]
  · change (ar * (((0 : ℚ) : ℝ) - bi) + ai * br) / (br ^ 2 + bi ^ 2) =
      (Complex.mk ar ai / Complex.mk br bi).im
    simp only [Complex.div_im, Complex.normSq_apply, pow_two, Rat.cast_zero, sub_eq_add_neg,
      zero_add, mul_neg, add_div, neg_div, add_comm]

theorem Phasor.mag_real (a : Phasor p) (values : Fin p → ℝ) :
    a.mag.real values = ‖a.complex values‖ := by
  rw [Complex.norm_def, Complex.normSq_apply]
  change Real.sqrt ((a.re.real values) ^ 2 + (a.im.real values) ^ 2) = _
  simp only [pow_two, Phasor.complex]

theorem dualComplexDiv_sound (a b : Phasor p) {prec : ℕ} {coords : Fin p → Coordinate}
    {re im : DualBox}
    (hr : (a.div b).re.evalBox prec coords = some re)
    (hi : (a.div b).im.evalBox prec coords = some im) :
    re.Encloses ((a.div b).re.center coords) ((a.div b).re.along coords) ∧
      im.Encloses ((a.div b).im.center coords) ((a.div b).im.along coords) :=
  ⟨Expr.evalBox_sound _ hr, Expr.evalBox_sound _ hi⟩

theorem dualComplexMag_sound (a : Phasor p) {prec : ℕ} {coords : Fin p → Coordinate}
    {out : DualBox} (h : a.mag.evalBox prec coords = some out) :
    out.Encloses (a.mag.center coords) (a.mag.along coords) :=
  Expr.evalBox_sound _ h

structure Driver (α : Type) where
  fs : α
  vas : α
  qes : α
  qms : α
  re : α
  le : α
  sd : α

def Driver.map (f : α → β) (d : Driver α) : Driver β :=
  ⟨f d.fs, f d.vas, f d.qes, f d.qms, f d.re, f d.le, f d.sd⟩

structure Medium where
  density : ℚ
  soundSpeed : ℚ

inductive Condition where
  | freeAir
  | addedMass (mass : ℚ)
  | sealedBox (volume : ℚ)

inductive Measurement where
  | magnitude (ohms : ℚ)
  | complex (re im : ℚ)

structure Sample where
  frequency : ℚ
  impedance : Measurement

def tau : Expr p := 2 * .pi

def bulkModulus (medium : Medium) : Expr p :=
  .constant medium.density * (Expr.constant medium.soundSpeed).square

structure Motor (p : ℕ) where
  area : Expr p
  omega : Expr p
  stiffness : Expr p
  mass : Expr p
  resistance : Expr p
  blSq : Expr p

def motor (driver : Driver (Expr p)) (rhoC2 : Expr p) : Motor p :=
  let omega := tau * driver.fs
  let area := driver.sd.square
  let cms := driver.vas / (rhoC2 * area)
  let mass := 1 / (omega.square * cms)
  let omegaMass := omega * mass
  ⟨area, omega, 1 / cms, mass, omegaMass / driver.qms,
    (omegaMass * driver.re) / driver.qes⟩

def driverImpedance (sd : ℚ) (medium : Medium) (condition : Condition)
    (frequency : ℚ) : Phasor 6 :=
  let d : Driver (Expr 6) :=
    ⟨.parameter 0, .parameter 1, .parameter 2, .parameter 3, .parameter 4, .parameter 5,
      .constant sd⟩
  let m := motor d (bulkModulus medium)
  let mass := match condition with
    | .addedMass added => m.mass + .constant added
    | _ => m.mass
  let stiffness := match condition with
    | .sealedBox volume => m.stiffness * (1 + d.vas / .constant volume)
    | _ => m.stiffness
  let w := tau * .constant frequency
  (Phasor.mk d.re (w * d.le)).add
    ((Phasor.ofReal m.blSq).div ⟨m.resistance, w * mass - stiffness / w⟩)

inductive EnclosureParameter where
  | volume
  | leakage
  | absorption
  | portQuality
  | effectiveLength
  | radiatorMass
  deriving DecidableEq

inductive Enclosure where
  | sealed
  | vented (area length : ℚ) (quality : Option ℚ)
  | passive (count area mass compliance resistance : ℚ)

structure EnclosureInput where
  driver : Driver ℚ
  medium : Medium
  volume : ℚ
  count : ℚ
  series : ℚ
  leakage : Option ℚ
  absorption : Option ℚ
  enclosure : Enclosure

def enclosureImpedance (input : EnclosureInput)
    (keys : EnclosureParameter → Option (Fin p)) (frequency : ℚ) : Phasor p :=
  let parameter (key : EnclosureParameter) (q : ℚ) :=
    (keys key).map Expr.parameter |>.getD (.constant q)
  let d := input.driver.map (Expr.constant (p := p))
  let count : Expr p := .constant input.count
  let wiring := (Expr.constant input.series).square / count
  let rho : Expr p := .constant input.medium.density
  let rhoC2 : Expr p := bulkModulus input.medium
  let volume := parameter .volume input.volume
  let cab := volume / rhoC2
  let m := motor d rhoC2
  let coupling := count * m.area
  let w : Expr p := tau * .constant frequency
  let (characteristic, branch, branchArea) := match input.enclosure with
    | .sealed =>
      (1 / ((m.omega * cab) * (1 + (d.vas * count) / volume).sqrt), Phasor.ofReal 1, 0)
    | .vented area length quality =>
      let mass := (rho * parameter .effectiveLength length) / .constant area
      let resistance := match quality with
        | none => 0
        | some q => (mass / (mass * cab).sqrt) / parameter .portQuality q
      ((mass / cab).sqrt, ⟨resistance, w * mass⟩, 1)
    | .passive quantity area mass compliance resistance =>
      let mass := parameter .radiatorMass mass
      let area := Expr.constant quantity * (Expr.constant area).square
      ((mass / (area * cab)).sqrt,
        ⟨.constant resistance, w * mass - 1 / (w * .constant compliance)⟩, area)
  let loss (key : EnclosureParameter) (q : Option ℚ) : Expr p := match q with
    | none => 0
    | some quality => 1 / (parameter key quality * characteristic)
  let conductance := loss .leakage input.leakage + loss .absorption input.absorption
  let base : Phasor p := ⟨conductance, w * cab⟩
  let admittance := match input.enclosure with
    | .sealed => base
    | _ => (base.mul branch).add (Phasor.ofReal branchArea)
  let driverZ : Phasor p := ⟨m.resistance, w * m.mass - m.stiffness / w⟩
  let mechanical := (driverZ.mul admittance).add ((Phasor.ofReal coupling).mul branch)
  let electrical : Phasor p := ⟨d.re, w * d.le⟩
  (Phasor.ofReal wiring).mul
    (electrical.add (((Phasor.ofReal m.blSq).mul admittance).div mechanical))

def residualRows (z : Phasor p) : Measurement → List (Expr p)
  | .magnitude q =>
    let measured : Expr p := .constant q
    [(z.mag - measured) / measured]
  | .complex re im =>
    let scale := (Phasor.mk (.constant re) (.constant im) : Phasor p).mag
    [(z.re - .constant re) / scale, (z.im - .constant im) / scale]

inductive FitKind where
  | driver
  | enclosure
  deriving DecidableEq

structure Range where
  lo : ℚ
  hi : ℚ

structure FitRequest (p : ℕ) where
  kind : FitKind
  ranges : Fin p → Range
  tolerance : ℚ
  rows : List (Expr p)

def driverRequest (sd : ℚ) (medium : Medium) (condition : Condition)
    (free perturbed : List Sample) (ranges : Fin 6 → Range) (tolerance : ℚ) : FitRequest 6 :=
  let sweep (condition : Condition) := List.flatMap fun s : Sample =>
    residualRows (driverImpedance sd medium condition s.frequency) s.impedance
  ⟨.driver, ranges, tolerance, sweep .freeAir free ++ sweep condition perturbed⟩

def enclosureRequest (input : EnclosureInput) (keys : Fin p → EnclosureParameter)
    (samples : List Sample) (ranges : Fin p → Range) (tolerance : ℚ) : FitRequest p :=
  let index (key : EnclosureParameter) := (List.ofFn fun i => i).find? fun i => keys i == key
  ⟨.enclosure, ranges, tolerance, samples.flatMap fun s =>
    residualRows (enclosureImpedance input index s.frequency) s.impedance⟩

inductive FitStatus where
  | residualTarget
  | stationary
  | boundConstrained
  | poorlyIdentified
  | stalled
  | iterationLimit
  deriving DecidableEq

structure FitCertificate where
  version : ℕ
  kind : FitKind
  status : FitStatus
  values : List ℚ
  rms : Box
  pg : Box
  sensitivityRank : ℕ
  sensitivityFloor : ℚ
  preconditioner : Option (List ℚ)
  weakDirection : Option (List ℚ)

def FitRequest.coordinates (r : FitRequest p) (cert : FitCertificate) (i : Fin p) :
    Coordinate :=
  ⟨(r.ranges i).lo, (r.ranges i).hi, cert.values.getD i 0⟩

def FitRequest.point (r : FitRequest p) (cert : FitCertificate) (i : Fin p) : ℝ :=
  (r.coordinates cert i).normalized

def FitRequest.residual (r : FitRequest p) (cert : FitCertificate) (k : Fin r.rows.length) : ℝ :=
  (r.rows.get k).center (r.coordinates cert)

def FitRequest.jacobian (r : FitRequest p) (cert : FitCertificate) :
    Matrix (Fin r.rows.length) (Fin p) ℝ :=
  Matrix.of fun k i => deriv ((r.rows.get k).along (r.coordinates cert) i) 0

def FitRequest.gradient (r : FitRequest p) (cert : FitCertificate) (i : Fin p) : ℝ :=
  (∑ k, r.jacobian cert k i * r.residual cert k) / (r.rows.length : ℝ)

def FitRequest.rmsError (r : FitRequest p) (cert : FitCertificate) : ℝ :=
  Real.sqrt ((∑ k, r.residual cert k ^ 2) / (r.rows.length : ℝ))

def maxReal (a : Fin n → ℝ) : ℝ := (List.ofFn a).foldr max 0

def FitRequest.projectedGradient (r : FitRequest p) (cert : FitCertificate) : ℝ :=
  maxReal (fun i => Numerics.projectedGradient (r.point cert i) (r.gradient cert i))

def FitRequest.Active (r : FitRequest p) (cert : FitCertificate) : Prop :=
  ∃ i, r.point cert i = 0 ∨ r.point cert i = 1

def FitRequest.DirectionBound (r : FitRequest p) (cert : FitCertificate) (tol : ℝ) : Prop :=
  ∀ next : Fin p → ℝ, (∀ i, 0 ≤ next i ∧ next i ≤ 1) →
    -(tol * ∑ i, |next i - r.point cert i|) ≤
      ∑ i, r.gradient cert i * (next i - r.point cert i)

def FitRequest.FullRank (r : FitRequest p) (cert : FitCertificate) : Prop :=
  (∀ v : Fin p → ℝ, (∃ i, v i ≠ 0) →
    (cert.sensitivityFloor : ℝ) * (∑ i, v i ^ 2) <
      ∑ k, (∑ i, r.jacobian cert k i * v i) ^ 2) ∧
  ∀ v, (r.jacobian cert).mulVec v = 0 → v = 0

def FitRequest.WeakDirection (r : FitRequest p) (cert : FitCertificate) : Prop :=
  ∃ v : Fin p → ℝ, (∃ i, v i ≠ 0) ∧
    (∑ k, (∑ i, r.jacobian cert k i * v i) ^ 2) / (∑ i, v i ^ 2) ≤
      (cert.sensitivityFloor : ℝ)

def FitRequest.StatusSound (r : FitRequest p) (cert : FitCertificate) : Prop :=
  match cert.status with
  | .residualTarget => r.FullRank cert ∧ r.rmsError cert ≤ (r.tolerance : ℝ)
  | .stationary => r.FullRank cert ∧ ¬ r.Active cert ∧
      r.projectedGradient cert ≤ (r.tolerance : ℝ) ∧ r.DirectionBound cert r.tolerance
  | .boundConstrained => r.FullRank cert ∧ r.Active cert ∧
      r.projectedGradient cert ≤ (r.tolerance : ℝ) ∧ r.DirectionBound cert r.tolerance
  | .poorlyIdentified => r.WeakDirection cert
  | .stalled | .iterationLimit => r.FullRank cert ∧
      ((r.tolerance : ℝ) < r.rmsError cert ∨ (r.tolerance : ℝ) < r.projectedGradient cert)

def FitRequest.Verified (r : FitRequest p) (cert : FitCertificate) : Prop :=
  (∀ i, 0 ≤ r.point cert i ∧ r.point cert i ≤ 1) ∧
  cert.rms.Contains (r.rmsError cert) ∧
  cert.pg.Contains (r.projectedGradient cert) ∧
  r.DirectionBound cert cert.pg.hi ∧
  (∀ i, HasDerivAt (fun t =>
    (∑ k : Fin r.rows.length, ((r.rows.get k).along (r.coordinates cert) i t) ^ 2) /
      (2 * (r.rows.length : ℝ))) (r.gradient cert i) 0) ∧
  r.StatusSound cert

def allFin (n : ℕ) (f : Fin n → Bool) : Bool := (List.ofFn f).all id

theorem allFin_iff {f : Fin n → Bool} : allFin n f = true ↔ ∀ i, f i = true := by
  simp [allFin, List.all_eq_true, List.mem_ofFn]

def anyFin (n : ℕ) (f : Fin n → Bool) : Bool := (List.ofFn f).any id

theorem anyFin_iff {f : Fin n → Bool} : anyFin n f = true ↔ ∃ i, f i = true := by
  simp [anyFin, List.any_eq_true, List.mem_ofFn]

def sumBox (a : Fin n → Box) : Box := (List.ofFn a).foldr Box.add zeroBox

theorem sumBox_sound {a : Fin n → Box} {x : Fin n → ℝ}
    (h : ∀ i, (a i).Contains (x i)) : (sumBox a).Contains (∑ i, x i) := by
  induction n with
  | zero => simpa [sumBox] using (show zeroBox.Contains 0 by simpa [zeroBox] using point_sound 0)
  | succ n ih =>
    rw [sumBox, List.ofFn_succ, List.foldr_cons, Fin.sum_univ_succ]
    exact add_sound (h 0) (ih fun i => h i.succ)

def maxBox (a : Fin n → Box) : Box := (List.ofFn a).foldr Box.joinMax zeroBox

theorem maxBox_sound {a : Fin n → Box} {x : Fin n → ℝ}
    (h : ∀ i, (a i).Contains (x i)) : (maxBox a).Contains (maxReal x) := by
  induction n with
  | zero => simpa [maxBox, maxReal] using
      (show zeroBox.Contains 0 by simpa [zeroBox] using point_sound 0)
  | succ n ih =>
    rw [maxBox, maxReal, List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons]
    exact max_sound (h 0) (ih fun i => h i.succ)

theorem le_maxReal {x : Fin n → ℝ} (i : Fin n) : x i ≤ maxReal x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [maxReal, List.ofFn_succ, List.foldr_cons]
    refine Fin.cases (le_max_left _ _) (fun j => ?_) i
    exact (ih (x := fun j : Fin n => x j.succ) j).trans (le_max_right _ _)

def dotBox (prec : ℕ) (a b : Fin n → Box) : Box :=
  sumBox fun i => mulBox prec (a i) (b i)

theorem dotBox_sound {prec : ℕ} {a b : Fin n → Box} {x y : Fin n → ℝ}
    (ha : ∀ i, (a i).Contains (x i)) (hb : ∀ i, (b i).Contains (y i)) :
    (dotBox prec a b).Contains (∑ i, x i * y i) :=
  sumBox_sound fun i => mulBox_sound (ha i) (hb i)

def evalRows (prec : ℕ) (coords : Fin p → Coordinate) :
    (rows : List (Expr p)) → Option (Fin rows.length → DualBox)
  | [] => some Fin.elim0
  | e :: rows => (e.evalBox prec coords).bind fun box =>
    (evalRows prec coords rows).map (Fin.cons box)

theorem evalRows_sound {prec : ℕ} {coords : Fin p → Coordinate} (rows : List (Expr p))
    {out : Fin rows.length → DualBox} (h : evalRows prec coords rows = some out)
    (k : Fin rows.length) :
    (out k).Encloses ((rows.get k).center coords) ((rows.get k).along coords) := by
  induction rows with
  | nil => exact Fin.elim0 k
  | cons e es ih =>
    simp only [evalRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using e.evalBox_sound hb
    · simpa using ih hbs i

def projectBox (c : Coordinate) (gradient : Box) : Box :=
  if c.value = c.lo then zeroBox.joinMax (zeroBox.sub gradient)
  else if c.value = c.hi then zeroBox.joinMax gradient else gradient.abs

theorem normalized_eq_zero {c : Coordinate} (width : c.lo < c.hi) :
    c.normalized = 0 ↔ c.value = c.lo := by
  have hw : (0 : ℝ) < (c.hi : ℝ) - c.lo := sub_pos.mpr (Rat.cast_lt.mpr width)
  simp [Coordinate.normalized, div_eq_zero_iff, hw.ne', sub_eq_zero]

theorem normalized_eq_one {c : Coordinate} (width : c.lo < c.hi) :
    c.normalized = 1 ↔ c.value = c.hi := by
  have hw : (0 : ℝ) < (c.hi : ℝ) - c.lo := sub_pos.mpr (Rat.cast_lt.mpr width)
  simp [Coordinate.normalized, div_eq_iff hw.ne', sub_left_inj]

theorem normalized_in_range {c : Coordinate} (width : c.lo < c.hi)
    (lo : c.lo ≤ c.value) (hi : c.value ≤ c.hi) :
    0 ≤ c.normalized ∧ c.normalized ≤ 1 := by
  have hw : (0 : ℝ) < (c.hi : ℝ) - c.lo := sub_pos.mpr (Rat.cast_lt.mpr width)
  exact ⟨div_nonneg (sub_nonneg.mpr (Rat.cast_le.mpr lo)) hw.le,
    (div_le_iff₀ hw).mpr (by rw [one_mul]; exact sub_le_sub_right (Rat.cast_le.mpr hi) _)⟩

theorem projectBox_sound {c : Coordinate} {a : Box} {g : ℝ}
    (width : c.lo < c.hi) (h : a.Contains g) :
    (projectBox c a).Contains (Numerics.projectedGradient c.normalized g) := by
  simp only [projectBox, Numerics.projectedGradient, normalized_eq_zero width, normalized_eq_one width]
  have hz : zeroBox.Contains 0 := by simpa [zeroBox] using point_sound 0
  split
  · simpa only [zero_sub] using max_sound hz (sub_sound hz h)
  · split
    · exact max_sound hz h
    · exact abs_sound h

def rmsBox (prec : ℕ) (a : Fin n → DualBox) : Option Box :=
  (divBox prec (sumBox fun k => squareBox prec (a k).val) (Box.point n)).bind (rootBox prec)

def projectedBox (prec : ℕ) (coords : Fin p → Coordinate) (a : Fin n → DualBox) : Option Box :=
  (reciprocalBox prec (Box.point n)).map fun inv =>
    maxBox fun i => projectBox (coords i) (mulBox prec
      (dotBox prec (fun k => (a k).partial i) (fun k => (a k).val)) inv)

theorem rmsBox_sound {prec : ℕ} {r : FitRequest p} {a : Fin r.rows.length → DualBox}
    (sound : ∀ k, (a k).val.Contains (FitRequest.residual (p := p) r cert k))
    (h : rmsBox prec a = some out) : out.Contains (r.rmsError cert) := by
  obtain ⟨mean, hm, hr⟩ := Option.bind_eq_some_iff.mp h
  have rows : (Box.point (r.rows.length : ℚ)).Contains (r.rows.length : ℝ) := by
    simpa using point_sound (r.rows.length : ℚ)
  exact rootBox_sound
    (divBox_sound (sumBox_sound fun k => squareBox_sound (sound k)) rows hm) hr

theorem projectedBox_sound {prec : ℕ} {r : FitRequest p} {a : Fin r.rows.length → DualBox}
    (width : ∀ i, (r.coordinates cert i).lo < (r.coordinates cert i).hi)
    (hv : ∀ k, (a k).val.Contains (r.residual cert k))
    (derivative : ∀ (k : Fin r.rows.length) (i : Fin p),
      ((a k).partial i).Contains (r.jacobian cert k i))
    (h : projectedBox prec (r.coordinates cert) a = some out) :
    out.Contains (r.projectedGradient cert) := by
  obtain ⟨inv, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  have rows : (Box.point (r.rows.length : ℚ)).Contains (r.rows.length : ℝ) := by
    simpa using point_sound (r.rows.length : ℚ)
  have invSound := (reciprocalBox_sound rows hi).1
  apply maxBox_sound
  intro i
  apply projectBox_sound (width i)
  unfold FitRequest.gradient
  rw [← mul_one_div]
  exact mulBox_sound (dotBox_sound (fun k => derivative k i) hv) invSound

def preconditionerEntry (p : ℕ) (entries : List ℚ) (i j : Fin p) : ℚ :=
  entries.getD (i.val * p + j.val) 0

def preconditionerMatrix (p : ℕ) (entries : List ℚ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => preconditionerEntry p entries i j

def checkPreconditioner (p : ℕ) (entries : List ℚ) : Bool :=
  decide (entries.length = p * p) &&
    allFin p (fun i => decide (0 < preconditionerEntry p entries i i) &&
      allFin p (fun j => decide (i < j → preconditionerEntry p entries i j = 0)))

theorem checkPreconditioner_sound (h : checkPreconditioner p entries = true) :
    (∀ i, 0 < preconditionerMatrix p entries i i) ∧
      ∀ i j, i < j → preconditionerMatrix p entries i j = 0 := by
  have hi := allFin_iff.mp (Bool.and_eq_true_iff.mp h).2
  constructor
  · intro i
    exact Rat.cast_pos.mpr (of_decide_eq_true (Bool.and_eq_true_iff.mp (hi i)).1)
  · intro i j hij
    have e : preconditionerEntry p entries i j = 0 :=
      (of_decide_eq_true (allFin_iff.mp (Bool.and_eq_true_iff.mp (hi i)).2 j)) hij
    simp [preconditionerMatrix, e]

def shiftedBox (prec : ℕ) (column : Fin p → Fin n → Box) (floor : ℚ)
    (i j : Fin p) : Box :=
  if i = j then (sumBox fun k => squareBox prec (column i k)).sub (Box.point floor)
  else dotBox prec (column i) (column j)

theorem shiftedBox_sound {prec : ℕ} {column : Fin p → Fin n → Box}
    {J : Matrix (Fin n) (Fin p) ℝ} (sound : ∀ i k, (column i k).Contains (J k i))
    (floor : ℚ) (i j : Fin p) :
    (shiftedBox prec column floor i j).Contains
      ((Jᵀ * J - (floor : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) i j) := by
  by_cases hij : i = j
  · subst j
    simpa [shiftedBox, Matrix.sub_apply, Matrix.mul_apply, pow_two] using
      sub_sound (sumBox_sound fun k => squareBox_sound (prec := prec) (sound i k))
        (point_sound floor)
  · simpa [shiftedBox, hij, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply] using
      dotBox_sound (prec := prec) (sound i) (sound j)

def transformedBox (prec : ℕ) (column : Fin p → Fin n → Box) (floor : ℚ)
    (entries : List ℚ) : Fin p → Fin p → Box :=
  let change i j := Box.point (preconditionerEntry p entries i j)
  let product i j := dotBox prec (shiftedBox prec column floor i) (fun k => change k j)
  fun i j => dotBox prec (fun k => change k i) (fun k => product k j)

theorem transformedBox_sound {prec : ℕ} {column : Fin p → Fin n → Box}
    {J : Matrix (Fin n) (Fin p) ℝ} (sound : ∀ i k, (column i k).Contains (J k i))
    (floor : ℚ) (entries : List ℚ) (i j : Fin p) :
    let C := preconditionerMatrix p entries
    (transformedBox prec column floor entries i j).Contains
      ((Cᵀ * (Jᵀ * J - (floor : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) * C) i j) := by
  dsimp only [transformedBox]
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  refine dotBox_sound (fun k => point_sound (preconditionerEntry p entries k i)) ?_
  intro k
  rw [Matrix.mul_apply]
  exact dotBox_sound (shiftedBox_sound sound floor k)
    (fun l => point_sound (preconditionerEntry p entries l j))

def checkDominant (a : Fin p → Fin p → Box) : Bool :=
  allFin p fun i => decide ((sumBox fun j => if i = j then zeroBox else (a i j).abs).hi <
    (a i i).lo)

theorem checkDominant_sound {a : Fin p → Fin p → Box} {M : Fin p → Fin p → ℝ}
    (sound : ∀ i j, (a i j).Contains (M i j)) (h : checkDominant a = true) :
    ∀ i, (∑ j ∈ Finset.univ.erase i, |M i j|) < M i i := by
  intro i
  let offDiag (j : Fin p) := if i = j then zeroBox else (a i j).abs
  let weight (j : Fin p) := if i = j then (0 : ℝ) else |M i j|
  have enclosed : (sumBox offDiag).Contains (∑ j, weight j) := by
    apply sumBox_sound
    intro j
    by_cases e : i = j
    · simpa [offDiag, weight, e, zeroBox] using point_sound 0
    · simpa [offDiag, weight, e] using abs_sound (sound i j)
  have off : (∑ j, weight j) = ∑ j ∈ Finset.univ.erase i, |M i j| := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp [weight, Finset.sum_congr rfl (fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj).symm)]
  have bound : (sumBox offDiag).hi < (a i i).lo := of_decide_eq_true (allFin_iff.mp h i)
  rw [← off]
  exact enclosed.2.trans_lt ((Rat.cast_lt.mpr bound).trans_le (sound i i).1)

def checkFull (prec : ℕ) (column : Fin p → Fin n → Box) (floor : ℚ)
    (entries : List ℚ) : Bool :=
  checkPreconditioner p entries && checkDominant (transformedBox prec column floor entries)

theorem checkFull_sound {prec : ℕ} {column : Fin p → Fin n → Box}
    {J : Matrix (Fin n) (Fin p) ℝ} {floor : ℚ} {entries : List ℚ}
    (sound : ∀ i k, (column i k).Contains (J k i))
    (accepted : checkFull prec column floor entries = true) :
    ∀ v : Fin p → ℝ, (∃ i, v i ≠ 0) →
      (floor : ℝ) * (∑ i, v i ^ 2) < ∑ k, (∑ i, J k i * v i) ^ 2 := by
  obtain ⟨hc, hm⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨diag, tri⟩ := checkPreconditioner_sound hc
  exact preconditioned_gram_full_rank J (preconditionerMatrix p entries) floor diag tri
    (checkDominant_sound (transformedBox_sound sound floor entries) hm)

def checkWeak (prec : ℕ) (column : Fin p → Fin n → Box) (floor : ℚ)
    (entries : List ℚ) : Bool :=
  let weight (i : Fin p) := (Box.point (entries.getD i 0)).roundOut prec
  let normSq := sumBox fun i => squareBox prec (weight i)
  let energy := sumBox fun k => squareBox prec (dotBox prec weight (fun i => column i k))
  decide (entries.length = p ∧ 0 < normSq.lo ∧
    energy.hi ≤ (mulBox prec normSq (Box.point floor)).lo)

theorem checkWeak_sound {prec : ℕ} {column : Fin p → Fin n → Box}
    {J : Matrix (Fin n) (Fin p) ℝ} {floor : ℚ} {entries : List ℚ}
    (sound : ∀ i k, (column i k).Contains (J k i))
    (accepted : checkWeak prec column floor entries = true) :
    ∃ v : Fin p → ℝ, (∃ i, v i ≠ 0) ∧
      (∑ k, (∑ i, J k i * v i) ^ 2) / (∑ i, v i ^ 2) ≤ (floor : ℝ) := by
  let v (i : Fin p) : ℝ := entries.getD i 0
  let weight (i : Fin p) := (Box.point (entries.getD i 0)).roundOut prec
  let normSq := sumBox fun i => squareBox prec (weight i)
  let energy := sumBox fun k => squareBox prec (dotBox prec weight (fun i => column i k))
  have hw (i : Fin p) : (weight i).Contains (v i) := roundOut_sound (point_sound _) _
  have hn : normSq.Contains (∑ i, v i ^ 2) :=
    sumBox_sound fun i => squareBox_sound (hw i)
  have he : energy.Contains (∑ k, (∑ i, v i * J k i) ^ 2) :=
    sumBox_sound fun k => squareBox_sound (dotBox_sound hw (fun i => sound i k))
  have hf := mulBox_sound (prec := prec) hn (point_sound floor)
  obtain ⟨_, positive, comparison⟩ : entries.length = p ∧ 0 < normSq.lo ∧
      energy.hi ≤ (mulBox prec normSq (Box.point floor)).lo := of_decide_eq_true accepted
  have nonzero : ∃ i, v i ≠ 0 := by
    by_contra! hz
    have pos := (Rat.cast_pos.mpr positive).trans_le hn.1
    simp [hz] at pos
  have checked := he.2.trans ((Rat.cast_le.mpr comparison).trans hf.1)
  simp_rw [mul_comm (v _) (J _ _)] at checked
  rw [mul_comm] at checked
  exact weak_direction_rayleigh_bound J v nonzero checked

def replayPrecision : ℕ := 160

def checkBounds (outer inner : Box) : Bool := decide (0 ≤ outer.lo) && inner.checkWiden outer

theorem checkBounds_sound {outer inner : Box} {x : ℝ}
    (sound : inner.Contains x) (h : checkBounds outer inner = true) :
    outer.Contains x :=
  widen_sound sound (Bool.and_eq_true_iff.mp h).2

def checkCoordinates (coords : Fin p → Coordinate) : Bool :=
  allFin p fun i => let c := coords i; decide (c.lo < c.hi ∧ c.lo ≤ c.value ∧ c.value ≤ c.hi)

theorem checkCoordinates_sound {coords : Fin p → Coordinate}
    (h : checkCoordinates coords = true) (i : Fin p) :
    (coords i).lo < (coords i).hi ∧ (coords i).lo ≤ (coords i).value ∧
      (coords i).value ≤ (coords i).hi := of_decide_eq_true (allFin_iff.mp h i)

def activeAt (coords : Fin p → Coordinate) : Bool :=
  anyFin p fun i => let c := coords i; decide (c.value = c.lo ∨ c.value = c.hi)

theorem activeAt_sound {r : FitRequest p} {cert : FitCertificate}
    (width : ∀ i, (r.coordinates cert i).lo < (r.coordinates cert i).hi) :
    activeAt (r.coordinates cert) = true ↔ r.Active cert := by
  rw [activeAt, anyFin_iff]
  simp only [decide_eq_true_eq, FitRequest.Active, FitRequest.point,
    normalized_eq_zero (width _), normalized_eq_one (width _)]

def checkStatus (cert : FitCertificate) (tolerance : ℚ) (active : Bool)
    (rms pg : Box) : Bool :=
  match cert.status with
  | .residualTarget => decide (rms.hi ≤ tolerance)
  | .stationary => !active && decide (pg.hi ≤ tolerance)
  | .boundConstrained => active && decide (pg.hi ≤ tolerance)
  | .poorlyIdentified => true
  | .stalled | .iterationLimit => decide (tolerance < rms.lo ∨ tolerance < pg.lo)

def checkSensitivity (cert : FitCertificate) (column : Fin p → Fin n → Box) : Bool :=
  match cert.status, cert.preconditioner, cert.weakDirection with
  | .poorlyIdentified, none, some entries =>
    decide (cert.sensitivityRank < p) && checkWeak replayPrecision column cert.sensitivityFloor entries
  | .poorlyIdentified, _, _ => false
  | _, some entries, none =>
    decide (cert.sensitivityRank = p) && checkFull replayPrecision column cert.sensitivityFloor entries
  | _, _, _ => false

/-- Recompute the endpoint diagnostics from the physical model and verify the
    supplied sensitivity witness using rational intervals. -/
def checkFitCertificate (r : FitRequest p) (cert : FitCertificate) : Bool :=
  let coords := r.coordinates cert
  decide (cert.version = 1 ∧ cert.kind = r.kind ∧ cert.values.length = p ∧
    0 < p ∧ 0 < r.rows.length ∧ 0 ≤ cert.sensitivityFloor ∧ 0 ≤ r.tolerance) &&
  checkCoordinates coords &&
  ((evalRows replayPrecision coords r.rows).bind fun rows =>
    (rmsBox replayPrecision rows).bind fun rms =>
      (projectedBox replayPrecision coords rows).map fun pg =>
        checkBounds cert.rms rms && checkBounds cert.pg pg &&
        checkSensitivity cert (fun (i : Fin p) k => (rows k).partial i) &&
        checkStatus cert r.tolerance (activeAt coords) rms pg).getD false

theorem checkSensitivity_sound {r : FitRequest p} {cert : FitCertificate}
    {column : Fin p → Fin r.rows.length → Box}
    (hf : 0 ≤ cert.sensitivityFloor)
    (enclosed : ∀ i k, (column i k).Contains (r.jacobian cert k i))
    (accepted : checkSensitivity cert column = true) :
    match cert.status with
    | .poorlyIdentified => r.WeakDirection cert
    | _ => r.FullRank cert := by
  have full {entries : List ℚ}
      (h : checkFull replayPrecision column cert.sensitivityFloor entries = true) :
      r.FullRank cert :=
    let energy := checkFull_sound enclosed h
    ⟨energy, gram_floor_full_rank (Rat.cast_nonneg.mpr hf) energy⟩
  cases hs : cert.status <;> cases hp : cert.preconditioner <;> cases hw : cert.weakDirection <;>
    simp [checkSensitivity, hs, hp, hw] at accepted
  all_goals first
    | exact full accepted.2
    | exact checkWeak_sound enclosed accepted.2

theorem objective_partial {r : FitRequest p} {cert : FitCertificate}
    (nonempty : 0 < r.rows.length) (i : Fin p)
    (h : ∀ k : Fin r.rows.length, HasDerivAt ((r.rows.get k).along (r.coordinates cert) i)
      (r.jacobian cert k i) 0) :
    HasDerivAt (fun t =>
      (∑ k : Fin r.rows.length, ((r.rows.get k).along (r.coordinates cert) i t) ^ 2) /
        (2 * (r.rows.length : ℝ))) (r.gradient cert i) 0 := by
  have hsq (k : Fin r.rows.length) :
      HasDerivAt (fun t => ((r.rows.get k).along (r.coordinates cert) i t) ^ 2)
        (2 * (r.jacobian cert k i * r.residual cert k)) 0 := by
    convert (h k).pow 2 using 1
    simp only [Nat.cast_ofNat, Expr.along_zero, FitRequest.residual]
    ring
  have total := HasDerivAt.sum (u := Finset.univ) fun k _ => hsq k
  have hn : (r.rows.length : ℝ) ≠ 0 := by exact_mod_cast nonempty.ne'
  convert total.div_const (2 * (r.rows.length : ℝ)) using 1
  · funext t
    simp only [Finset.sum_apply]
  · rw [← Finset.mul_sum, FitRequest.gradient]
    field_simp [hn]

theorem directionBound_of_projected_le {r : FitRequest p} {cert : FitCertificate} {tol : ℝ}
    (h : r.projectedGradient cert ≤ tol) : r.DirectionBound cert tol := by
  intro next feasible
  exact projected_gradient_direction_sum feasible fun i => (le_maxReal i).trans h

theorem checkStatus_sound {r : FitRequest p} {cert : FitCertificate} {rms pg : Box}
    (width : ∀ i, (r.coordinates cert i).lo < (r.coordinates cert i).hi)
    (rmsSound : rms.Contains (r.rmsError cert))
    (pgSound : pg.Contains (r.projectedGradient cert))
    (sensitivity : match cert.status with
      | .poorlyIdentified => r.WeakDirection cert
      | _ => r.FullRank cert)
    (accepted : checkStatus cert r.tolerance (activeAt (r.coordinates cert)) rms pg = true) :
    r.StatusSound cert := by
  unfold FitRequest.StatusSound
  have st (h : pg.hi ≤ r.tolerance) :=
    pgSound.2.trans (Rat.cast_le.mpr h)
  have stopped (h : r.tolerance < rms.lo ∨ r.tolerance < pg.lo) :
      (r.tolerance : ℝ) < r.rmsError cert ∨ (r.tolerance : ℝ) < r.projectedGradient cert :=
    h.imp (fun h => (Rat.cast_lt.mpr h).trans_le rmsSound.1)
      (fun h => (Rat.cast_lt.mpr h).trans_le pgSound.1)
  cases s : cert.status <;> simp only [s] at sensitivity
  · simp only [checkStatus, s, decide_eq_true_eq] at accepted
    exact ⟨sensitivity, rmsSound.2.trans (Rat.cast_le.mpr accepted)⟩
  · simp [checkStatus, s] at accepted
    refine ⟨sensitivity, ?_, st accepted.2, directionBound_of_projected_le (st accepted.2)⟩
    rw [← activeAt_sound width, accepted.1]
    decide
  · simp [checkStatus, s] at accepted
    exact ⟨sensitivity, (activeAt_sound width).mp accepted.1, st accepted.2,
      directionBound_of_projected_le (st accepted.2)⟩
  · exact sensitivity
  · simp only [checkStatus, s, decide_eq_true_eq] at accepted
    exact ⟨sensitivity, stopped accepted⟩
  · simp only [checkStatus, s, decide_eq_true_eq] at accepted
    exact ⟨sensitivity, stopped accepted⟩

private theorem some_true_of_getD {b : Option Bool} (h : b.getD false = true) :
    b = some true := by
  cases b <;> simp_all

theorem checkFitCertificate_sound {r : FitRequest p} {cert : FitCertificate}
    (accepted : checkFitCertificate r cert = true) : r.Verified cert := by
  unfold checkFitCertificate at accepted
  obtain ⟨inputs, diagnostics⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨header, checkedCoordinates⟩ := Bool.and_eq_true_iff.mp inputs
  obtain ⟨_, _, _, _, nonempty, floor, _⟩ :
      cert.version = 1 ∧ cert.kind = r.kind ∧ cert.values.length = p ∧
        0 < p ∧ 0 < r.rows.length ∧ 0 ≤ cert.sensitivityFloor ∧ 0 ≤ r.tolerance :=
    of_decide_eq_true header
  have evaluated := some_true_of_getD diagnostics
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at evaluated
  obtain ⟨rows, hr, rms, hm, pg, hp, checked⟩ := evaluated
  obtain ⟨⟨⟨cr, cp⟩, cs⟩, ct⟩ :
      ((checkBounds cert.rms rms = true ∧ checkBounds cert.pg pg = true) ∧
        checkSensitivity cert (fun (i : Fin p) k => (rows k).partial i) = true) ∧
        checkStatus cert r.tolerance (activeAt (r.coordinates cert)) rms pg = true := by
    simpa only [Bool.and_eq_true] using checked
  have bounds := checkCoordinates_sound checkedCoordinates
  have width (i : Fin p) := (bounds i).1
  have dual := evalRows_sound r.rows hr
  have residual (k : Fin r.rows.length) :
      (rows k).val.Contains (r.residual cert k) := (dual k).1
  have derivatives (k : Fin r.rows.length) (i : Fin p) :
      ((rows k).partial i).Contains (r.jacobian cert k i) ∧
        HasDerivAt ((r.rows.get k).along (r.coordinates cert) i) (r.jacobian cert k i) 0 := by
    obtain ⟨d, contained, derivAt⟩ := (dual k).2 i
    have eq : r.jacobian cert k i = d := derivAt.deriv
    rw [eq]
    exact ⟨contained, derivAt⟩
  have jac (i : Fin p) (k : Fin r.rows.length) := (derivatives k i).1
  have rmsSound := rmsBox_sound residual hm
  have pgSound := projectedBox_sound width residual (fun k i => jac i k) hp
  have projected := checkBounds_sound pgSound cp
  refine ⟨fun i => normalized_in_range (width i) (bounds i).2.1 (bounds i).2.2,
    checkBounds_sound rmsSound cr, projected, directionBound_of_projected_le projected.2,
    fun i => objective_partial nonempty i (fun k => (derivatives k i).2), ?_⟩
  exact checkStatus_sound width rmsSound pgSound (checkSensitivity_sound floor jac cs) ct

#print axioms checkFitCertificate_sound

end Electroacoustics.ImpedanceCertificate
