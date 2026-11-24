module

public import Electroacoustics.Interval
public import Electroacoustics.Transcendentals
public import Electroacoustics.Duct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.DuctInterval

open Electroacoustics.Interval Electroacoustics.Transcendentals
open Finset

inductive Profile where
  | straight | conical | exponential
  deriving Repr, DecidableEq

structure Section where
  length : ℚ
  inletArea : ℚ
  outletArea : ℚ
  profile : Profile
  deriving Repr, DecidableEq

structure DuctPath where
  sections : List Section
  count : ℚ
  inletCorrection : ℚ
  outletCorrection : ℚ
  junctionInertances : List ℚ := []
  inertanceFactor : ℚ := 1
  complianceFactor : ℚ := 1
  deriving Repr, DecidableEq

def add (p : ℕ) (a b : Box) := (a.add b).roundOut p
def sub (p : ℕ) (a b : Box) := (a.sub b).roundOut p
def mul (p : ℕ) (a b : Box) := (a.mul b).roundOut p
def square (p : ℕ) (a : Box) := a.square.roundOut p
def div (p : ℕ) (a b : Box) := (a.div b).map (·.roundOut p)

private theorem div_contains {p : ℕ} {a b out : Box} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) (h : div p a b = some out) :
    out.Contains (x / y) := by
  unfold div at h
  cases he : a.div b with
  | none => simp [he] at h
  | some u =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    rw [← h]
    exact roundOut_sound (div_sound ha hb he) p

private theorem abs_le_of_box {a : Box} {x : ℝ} {c : ℚ}
    (h : a.Contains x) (hc : a.abs.hi ≤ c) : |x| ≤ (c : ℝ) :=
  (abs_sound h).2.trans (Rat.cast_le.mpr hc)

/-- The root check below verifies the candidate. Use structural fuel for
    Newton updates so kernel replay does not unfold well-founded recursion. -/
def sqrtNewton (n : ℕ) : ℕ → ℕ → ℕ
  | 0, guess => guess
  | fuel + 1, guess =>
    let next := (guess + n / guess) / 2
    if next < guess then sqrtNewton n fuel next else guess

def integerRoot (n : ℕ) : ℕ :=
  if n ≤ 1 then n else sqrtNewton n 32 (2 ^ (n.log2 / 2 + 1))

def sqrtCandidate (prec : ℕ) (a : Box) : Box :=
  let scale : ℚ := 2 ^ prec
  let low := integerRoot (⌊max 0 a.lo * scale ^ 2⌋ : ℤ).toNat
  let highSquare := (⌈max 0 a.hi * scale ^ 2⌉ : ℤ).toNat
  let high := integerRoot highSquare
  ⟨(low : ℚ) / scale, ((if high ^ 2 = highSquare then high else high + 1 : ℕ) : ℚ) / scale⟩

def boxSqrt (prec : ℕ) (a : Box) : Option Box :=
  let out := sqrtCandidate prec a
  if a.checkRoot out then some out else none

theorem boxSqrt_sound {prec : ℕ} {a out : Box} {x : ℝ}
    (ha : a.Contains x) (h : boxSqrt prec a = some out) :
    out.Contains (Real.sqrt x) := by
  by_cases checked : a.checkRoot (sqrtCandidate prec a) = true
  · have equal : sqrtCandidate prec a = out := by simpa [boxSqrt, checked] using h
    exact equal ▸ root_sound ha checked
  · simp [boxSqrt, checked] at h

def horner (p : ℕ) (a : Box) (coef : ℕ → ℚ) (start : ℕ) : ℕ → Box
  | 0 => Box.point 0
  | n + 1 => add p (Box.point (coef start)) (mul p a (horner p a coef (start + 1) n))

private theorem horner_sound (p : ℕ) {a : Box} {x : ℝ} (hx : a.Contains x)
    (coef : ℕ → ℚ) (start n : ℕ) :
    (horner p a coef start n).Contains (∑ i ∈ range n, (coef (start + i) : ℝ) * x ^ i) := by
  induction n generalizing start with
  | zero => simpa [horner] using point_sound 0
  | succ n ih =>
    rw [sum_range_succ']
    have eq : ∑ i ∈ range n, (coef (start + (i + 1)) : ℝ) * x ^ (i + 1) =
        x * ∑ i ∈ range n, (coef (start + 1 + i) : ℝ) * x ^ i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [show start + (i + 1) = start + 1 + i by omega, pow_succ]
      ring
    rw [eq]
    simpa only [horner, add, mul, add_zero, pow_zero, mul_one, add_comm] using
      roundOut_sound (add_sound (point_sound (coef start))
        (roundOut_sound (mul_sound hx (ih (start + 1))) p)) p

def pad (p : ℕ) (a : Box) (err : ℚ) : Box := add p a ⟨-err, err⟩

private theorem pad_sound {p : ℕ} {a : Box} {x y : ℝ} {err : ℚ}
    (ha : a.Contains x) (h : |y - x| ≤ (err : ℝ)) : (pad p a err).Contains y := by
  have hb : (Box.mk (-err) err).Contains (y - x) := by
    rw [Box.Contains, Rat.cast_neg]
    exact abs_le.mp h
  simpa only [pad, add, add_sub_cancel] using roundOut_sound (add_sound ha hb) p

def expSmall (p : ℕ) (a : Box) : Box :=
  pad p (horner p a (fun n => 1 / (n.factorial : ℚ)) 0 19) (1 / 2 ^ 55)

private theorem expSmall_sound {p : ℕ} {a : Box} {x : ℝ}
    (hx : a.Contains x) (hs : a.abs.hi ≤ 1) : (expSmall p a).Contains (Real.exp x) := by
  apply pad_sound (horner_sound p hx _ _ _)
  simpa only [zero_add, Rat.cast_div, Rat.cast_inv, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_natCast, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
    exp_remainder (by simpa only [Rat.cast_one] using abs_le_of_box hx hs)

def expReduced (p : ℕ) : ℕ → Box → Option Box
  | 0, a => if a.abs.hi ≤ 1 then some (expSmall p a) else none
  | n + 1, a =>
    if a.abs.hi ≤ 1 then some (expSmall p a)
    else (expReduced p n (mul p a (Box.point (1 / 2)))).map (square p)

def boxExp (prec : ℕ) (a : Box) : Option Box :=
  if a.lo = 0 ∧ a.hi = 0 then some (Box.point 1) else expReduced prec 10 a

private theorem expReduced_sound {p n : ℕ} {a out : Box} {x : ℝ}
    (hx : a.Contains x) (h : expReduced p n a = some out) :
    out.Contains (Real.exp x) := by
  induction n generalizing a out x with
  | zero =>
    simp only [expReduced] at h
    split at h
    · cases h
      exact expSmall_sound hx (by assumption)
    · contradiction
  | succ n ih =>
    simp only [expReduced] at h
    split at h
    · cases h
      exact expSmall_sound hx (by assumption)
    · let reduced := mul p a (Box.point (1 / 2))
      change (expReduced p n reduced).map (square p) = some out at h
      cases he : expReduced p n reduced with
      | none => simp [he] at h
      | some u =>
        simp only [he, Option.map_some, Option.some.injEq] at h
        rw [← h, exp_halving_squaring x 1]
        norm_num only [pow_one]
        apply roundOut_sound (square_sound (ih _ he)) p
        simpa [reduced, mul, div_eq_mul_inv] using
          roundOut_sound (mul_sound hx (point_sound (1 / 2 : ℚ))) p

theorem boxExp_sound {prec : ℕ} {a out : Box} {x : ℝ}
    (ha : a.Contains x) (h : boxExp prec a = some out) : out.Contains (Real.exp x) := by
  unfold boxExp at h
  split at h
  · rename_i zero
    cases h
    have hx : x = 0 := by
      have hl := ha.1
      have hh := ha.2
      rw [zero.1, Rat.cast_zero] at hl
      rw [zero.2, Rat.cast_zero] at hh
      exact le_antisymm hh hl
    simpa [hx] using point_sound 1
  · exact expReduced_sound ha h

def logTwo : Box := ⟨0.6931471803, 0.6931471808⟩

private theorem logTwo_sound : logTwo.Contains (Real.log 2) := by
  constructor
  · convert log_two_bracket.1.le using 1; norm_num [logTwo]
  · convert log_two_bracket.2.le using 1; norm_num [logTwo]

def logExponent (lo : ℚ) : ℤ :=
  let e := (lo.num.natAbs.log2 : ℤ) - (lo.den.log2 : ℤ)
  if lo < 2 ^ e then e - 1 else e

def logSeries (p : ℕ) (t : Box) : Box :=
  let polynomial := horner p (square p t) (fun n => 1 / (2 * (n : ℚ) + 1)) 0 40
  pad p (mul p (mul p (Box.point 2) t) polynomial) (1 / 2 ^ 79)

private theorem logSeries_sound {p : ℕ} {t : Box} {x : ℝ} (hx : t.Contains x)
    (hs : t.abs.hi ≤ 1 / 2) :
    (logSeries p t).Contains (Real.log ((1 + x) / (1 - x))) := by
  have hp := horner_sound p (roundOut_sound (square_sound hx) p)
    (fun n => 1 / (2 * (n : ℚ) + 1)) 0 40
  have hv := roundOut_sound (mul_sound
    (roundOut_sound (mul_sound (point_sound 2) hx) p) hp) p
  apply pad_sound hv
  have eq : x * (∑ i ∈ range 40, (↑(1 / (2 * (i : ℚ) + 1) : ℚ) : ℝ) * (x ^ 2) ^ i) =
      ∑ i ∈ range 40, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    push_cast
    rw [show x ^ (2 * i + 1) = (x ^ 2) ^ i * x by rw [pow_succ, pow_mul]]
    ring
  rw [mul_assoc]
  simp only [zero_add, Rat.cast_ofNat]
  rw [eq]
  simpa using duct_log_remainder (by simpa using abs_le_of_box hx hs)

def boxLogRatio (prec : ℕ) (a : Box) : Option Box := do
  if a.lo ≤ 0 then none else
    let e := logExponent a.lo
    let r ← div prec a (Box.point (2 ^ e))
    let t ← div prec (sub prec r (Box.point 1)) (add prec r (Box.point 1))
    if t.abs.hi ≤ 1 / 2 then
      some (add prec (logSeries prec t) (mul prec (Box.point (e : ℚ)) logTwo))
    else none

theorem boxLogRatio_sound {prec : ℕ} {a out : Box} {x : ℝ}
    (ha : a.Contains x) (h : boxLogRatio prec a = some out) :
    out.Contains (Real.log x) := by
  unfold boxLogRatio at h
  split at h
  · contradiction
  · rename_i positive
    let e := logExponent a.lo
    let r := x / (2 : ℝ) ^ e
    have hrPos : 0 < x := (Rat.cast_pos.mpr (lt_of_not_ge positive)).trans_le ha.1
    change (do
      let rb ← div prec a (Box.point (2 ^ e))
      let tb ← div prec (sub prec rb (Box.point 1)) (add prec rb (Box.point 1))
      if tb.abs.hi ≤ 1 / 2 then
        some (add prec (logSeries prec tb) (mul prec (Box.point (e : ℚ)) logTwo))
      else none) = some out at h
    cases hr : div prec a (Box.point (2 ^ e)) with
    | none => simp [hr] at h
    | some rb =>
      have hrb : rb.Contains r := div_contains ha (by simpa only [Rat.cast_zpow, Rat.cast_ofNat] using point_sound ((2 : ℚ) ^ e)) hr
      cases ht : div prec (sub prec rb (Box.point 1)) (add prec rb (Box.point 1)) with
      | none => simp [hr, ht] at h
      | some tb =>
        simp [hr, ht] at h
        obtain ⟨small, rfl⟩ := h
        have htb : tb.Contains ((r - 1) / (r + 1)) := div_contains
          (roundOut_sound (sub_sound hrb (by simpa using point_sound 1)) prec)
          (roundOut_sound (add_sound hrb (by simpa using point_sound 1)) prec) ht
        rw [log_range_reduction hrPos e]
        exact roundOut_sound (add_sound (logSeries_sound htb (by simpa using small))
          (roundOut_sound (mul_sound (by simpa only [Rat.cast_intCast] using point_sound (e : ℚ))
            logTwo_sound) prec)) prec

def waveSmall (p : ℕ) (t : Box) : Box × Box :=
  let negative := sub p (Box.point 0) t
  (pad p (horner p negative (fun n => 1 / ((2 * n).factorial : ℚ)) 0 12) (1 / 2 ^ 70),
   pad p (horner p negative (fun n => 1 / ((2 * n + 1).factorial : ℚ)) 0 12) (1 / 2 ^ 70))

private theorem waveSmall_sound {p : ℕ} {a : Box} {x : ℝ}
    (hx : a.Contains x) (hs : a.abs.hi ≤ 1) :
    (waveSmall p a).1.Contains (waveCos x) ∧ (waveSmall p a).2.Contains (waveSinc x) := by
  have hn : (sub p (Box.point 0) a).Contains (-x) := by
    simpa [sub] using roundOut_sound (sub_sound (point_sound 0) hx) p
  constructor
  · apply pad_sound (horner_sound p hn _ _ _)
    simpa only [zero_add, Rat.cast_div, Rat.cast_inv, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_natCast, div_eq_mul_inv, one_mul, mul_one, mul_comm] using waveCos_taylor_bound (by simpa only [Rat.cast_one] using abs_le_of_box hx hs)
  · apply pad_sound (horner_sound p hn _ _ _)
    simpa only [zero_add, Rat.cast_div, Rat.cast_inv, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_natCast, div_eq_mul_inv, one_mul, mul_one, mul_comm] using waveSinc_taylor_bound (by simpa only [Rat.cast_one] using abs_le_of_box hx hs)

def waveDouble (p : ℕ) (result : Box × Box) : Box × Box :=
  (sub p (mul p (Box.point 2) (square p result.1)) (Box.point 1), mul p result.2 result.1)

def waveReduced (p : ℕ) : ℕ → Box → Option (Box × Box)
  | 0, t => if t.abs.hi ≤ 1 then some (waveSmall p t) else none
  | n + 1, t =>
    if t.abs.hi ≤ 1 then some (waveSmall p t)
    else (waveReduced p n (mul p t (Box.point (1 / 4)))).map (waveDouble p)

def boxWave (prec : ℕ) (t : Box) : Option (Box × Box) := waveReduced prec 11 t

private theorem waveReduced_sound {p n : ℕ} {a : Box} {out : Box × Box} {x : ℝ}
    (hx : a.Contains x) (h : waveReduced p n a = some out) :
    out.1.Contains (waveCos x) ∧ out.2.Contains (waveSinc x) := by
  induction n generalizing a out x with
  | zero =>
    simp only [waveReduced] at h
    split at h
    · cases h
      exact waveSmall_sound hx (by assumption)
    · contradiction
  | succ n ih =>
    simp only [waveReduced] at h
    split at h
    · cases h
      exact waveSmall_sound hx (by assumption)
    · let reduced := mul p a (Box.point (1 / 4))
      change (waveReduced p n reduced).map (waveDouble p) = some out at h
      cases he : waveReduced p n reduced with
      | none => simp [he] at h
      | some u =>
        simp only [he, Option.map_some, Option.some.injEq] at h
        rw [← h, show x = 4 * (x / 4) by ring, (wave_doubling _).1, (wave_doubling _).2]
        have hr : reduced.Contains (x / 4) := by
          simpa [reduced, mul, div_eq_mul_inv] using roundOut_sound (mul_sound hx (point_sound (1 / 4 : ℚ))) p
        obtain ⟨hc, hs⟩ := ih hr he
        exact ⟨roundOut_sound (sub_sound (roundOut_sound
          (mul_sound (by simpa using point_sound 2) (roundOut_sound (square_sound hc) p)) p)
          (by simpa using point_sound 1)) p, roundOut_sound (mul_sound hs hc) p⟩

theorem boxWave_sound {prec : ℕ} {a : Box} {out : Box × Box} {x : ℝ}
    (ha : a.Contains x) (h : boxWave prec a = some out) :
    out.1.Contains (waveCos x) ∧ out.2.Contains (waveSinc x) :=
  waveReduced_sound ha h


/-- Obtain real sine and cosine from the power series in the squared angle. -/
def boxTrig (p : ℕ) (angle : Box) : Option (Box × Box) := do
  let (cosine, sinc) ← boxWave p (square p angle)
  return (mul p angle sinc, cosine)

theorem boxTrig_sound {p : ℕ} {angle sine cosine : Box} {x : ℝ}
    (hx : angle.Contains x) (h : boxTrig p angle = some (sine, cosine)) :
    sine.Contains (Real.sin x) ∧ cosine.Contains (Real.cos x) := by
  unfold boxTrig at h
  cases hw : boxWave p (square p angle) with
  | none => simp [hw] at h
  | some w =>
    obtain ⟨cosBox, sincBox⟩ := w
    simp [hw] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hc, hs⟩ := boxWave_sound (roundOut_sound (square_sound hx) p) hw
    have hcos : waveCos (x ^ 2) = Real.cos x := by
      rw [waveCos, ite_eq_left (sq_nonneg x), Real.sqrt_sq_eq_abs, Real.cos_abs]
    have hsin : x * waveSinc (x ^ 2) = Real.sin x := by
      by_cases hz : x = 0
      · simp [hz]
      have positive : 0 < x ^ 2 := sq_pos_of_ne_zero hz
      rw [waveSinc, ite_eq_right positive.ne', ite_eq_left positive, Real.sqrt_sq_eq_abs]
      rcases lt_or_gt_of_ne hz with neg | pos
      · rw [abs_of_neg neg, Real.sin_neg, neg_div_neg_eq, mul_div_cancel₀ _ hz]
      · rw [abs_of_pos pos, mul_div_cancel₀ _ hz]
    exact ⟨hsin ▸ roundOut_sound (mul_sound hx hs) p, hcos ▸ hc⟩

/-- The same Webster transfer formula is used for exact reals and for interval replay. -/
structure Arithmetic (α : Type) where
  rat : ℚ → α
  pi : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  square : α → α
  abs : α → α
  sqrt : α → α
  exp : α → α
  log : α → α
  wave : α → α × α
  withValue : {β : Type} → α → (α → β) → β
  withValue_eq : ∀ {β : Type} (a : α) (k : α → β), withValue a k = k a

def realArithmetic : Arithmetic ℝ :=
  ⟨Rat.cast, Real.pi, (· + ·), (· - ·), (· * ·), (· / ·), (· ^ 2),
    abs, Real.sqrt, Real.exp, Real.log, (fun x => (waveCos x, waveSinc x)),
    (fun a k => k a), fun _ _ => rfl⟩

def lift₂ (op : Box → Box → Option Box) (a b : Option Box) : Option Box := do
  op (← a) (← b)

def piBox : Box := ⟨3.1415926535897932, 3.1415926535897933⟩

theorem piBox_sound : piBox.Contains Real.pi := by
  constructor
  · convert pi_bracket.1.le using 1; norm_num [piBox]
  · convert pi_bracket.2.le using 1; norm_num [piBox]

/-- Reduce both components of a rational before passing it on. The kernel
    can then reuse the literal endpoints wherever an interval is used twice. -/
def withRat {α : Type} : ℚ → (ℚ → α) → α
  | ⟨_, 0, h, _⟩, _ => (h rfl).elim
  | ⟨.ofNat 0, d + 1, h, c⟩, next => next ⟨.ofNat 0, d + 1, h, c⟩
  | ⟨.ofNat (n + 1), d + 1, h, c⟩, next => next ⟨.ofNat (n + 1), d + 1, h, c⟩
  | ⟨.negSucc 0, d + 1, h, c⟩, next => next ⟨.negSucc 0, d + 1, h, c⟩
  | ⟨.negSucc (n + 1), d + 1, h, c⟩, next => next ⟨.negSucc (n + 1), d + 1, h, c⟩

@[simp] theorem withRat_eq {α : Type} (q : ℚ) (next : ℚ → α) :
    withRat q next = next q := by
  cases q using Rat.casesOn with
  | mk' n d hn hc =>
    cases d with
    | zero => contradiction
    | succ d => cases n <;> rename_i n <;> cases n <;> rfl

def withBox {α : Type} (box : Box) (next : Box → α) : α :=
  withRat box.lo fun lo => withRat box.hi fun hi => next ⟨lo, hi⟩

@[simp] theorem withBox_eq {α : Type} (box : Box) (next : Box → α) :
    withBox box next = next box := by
  cases box
  simp [withBox]

def strictOut (out : Option Box) : Option Box := out.bind fun bound => withBox bound some

@[simp] theorem strictOut_eq (out : Option Box) : strictOut out = out := by
  cases out <;> simp [strictOut]

def strictWave (out : Option (Box × Box)) : Option (Box × Box) := do
  let (a, b) ← out
  withBox a fun x => withBox b fun y => some (x, y)

@[simp] theorem strictWave_eq (out : Option (Box × Box)) : strictWave out = out := by
  cases out with
  | none => rfl
  | some b => cases b; simp [strictWave]

def withOptionalBox (a : Option Box) (k : Option Box → β) : β :=
  match a with
  | none => k none
  | some b => withBox b (fun value => k (some value))

theorem withOptionalBox_eq (a : Option Box) (k : Option Box → β) :
    withOptionalBox a k = k a := by
  cases a <;> simp [withOptionalBox]

def intervalArithmetic (p : ℕ) : Arithmetic (Option Box) :=
  { rat := fun x => some (Box.point x)
    pi := some piBox
    add := lift₂ (fun a b => withBox (add p a b) some)
    sub := lift₂ (fun a b => withBox (sub p a b) some)
    mul := lift₂ (fun a b => withBox (mul p a b) some)
    div := lift₂ (fun a b => strictOut (div p a b))
    square := (fun a => strictOut (a.map (square p)))
    abs := Option.map Box.abs
    sqrt := (·.bind fun a => strictOut (boxSqrt p a))
    exp := (·.bind fun a => strictOut (boxExp p a))
    log := (·.bind fun a => strictOut (boxLogRatio p a))
    wave := fun a =>
      match a.bind (fun b => strictWave (boxWave p b)) with
      | none => (none, none)
      | some (cosine, sinc) => (some cosine, some sinc)
    withValue := withOptionalBox
    withValue_eq := withOptionalBox_eq }

def Approx (a : Option Box) (x : ℝ) : Prop :=
  ∀ out, a = some out → out.Contains x

def ApproxPair (a : Option Box × Option Box) (x : ℝ × ℝ) : Prop :=
  Approx a.1 x.1 ∧ Approx a.2 x.2

namespace Approx

theorem some {a : Box} {x : ℝ} (h : a.Contains x) : Approx (Option.some a) x :=
  fun _ eq => Option.some.inj eq ▸ h

theorem map {a : Option Box} {x y : ℝ} {op : Box → Box}
    (h : Approx a x) (ok : ∀ b, b.Contains x → (op b).Contains y) :
    Approx (a.map op) y := by
  cases a with
  | none => simp [Approx]
  | some b => exact some (ok b (h b rfl))

theorem bind {a : Option Box} {x y : ℝ} {op : Box → Option Box}
    (h : Approx a x) (ok : ∀ b, b.Contains x → Approx (op b) y) :
    Approx (a.bind op) y := by
  cases a with
  | none => simp [Approx]
  | some b => exact ok b (h b rfl)

theorem binary {a b : Option Box} {x y z : ℝ} {op : Box → Box → Option Box}
    (ha : Approx a x) (hb : Approx b y)
    (ok : ∀ l r, l.Contains x → r.Contains y → Approx (op l r) z) :
    Approx (lift₂ op a b) z :=
  ha.bind fun l hl => hb.bind fun r hr => ok l r hl hr

theorem rat (p : ℕ) (x : ℚ) :
    Approx ((intervalArithmetic p).rat x) (realArithmetic.rat x) := some (point_sound x)

theorem pi (p : ℕ) : Approx (intervalArithmetic p).pi realArithmetic.pi :=
  some piBox_sound

theorem add {p : ℕ} {a b : Option Box} {x y : ℝ}
    (ha : Approx a x) (hb : Approx b y) :
    Approx ((intervalArithmetic p).add a b) (realArithmetic.add x y) :=
  binary ha hb fun _ _ hl hr => by
    rw [withBox_eq]
    exact some (roundOut_sound (add_sound hl hr) p)

theorem sub {p : ℕ} {a b : Option Box} {x y : ℝ}
    (ha : Approx a x) (hb : Approx b y) :
    Approx ((intervalArithmetic p).sub a b) (realArithmetic.sub x y) :=
  binary ha hb fun _ _ hl hr => by
    rw [withBox_eq]
    exact some (roundOut_sound (sub_sound hl hr) p)

theorem mul {p : ℕ} {a b : Option Box} {x y : ℝ}
    (ha : Approx a x) (hb : Approx b y) :
    Approx ((intervalArithmetic p).mul a b) (realArithmetic.mul x y) :=
  binary ha hb fun _ _ hl hr => by
    rw [withBox_eq]
    exact some (roundOut_sound (mul_sound hl hr) p)

theorem div {p : ℕ} {a b : Option Box} {x y : ℝ}
    (ha : Approx a x) (hb : Approx b y) :
    Approx ((intervalArithmetic p).div a b) (realArithmetic.div x y) :=
  binary ha hb fun _ _ hl hr => by
    rw [strictOut_eq]
    exact fun _ eq => div_contains hl hr eq

theorem square {p : ℕ} {a : Option Box} {x : ℝ} (ha : Approx a x) :
    Approx ((intervalArithmetic p).square a) (realArithmetic.square x) := by
  change Approx (strictOut (a.map (DuctInterval.square p))) (realArithmetic.square x)
  rw [strictOut_eq]
  exact ha.map fun _ h => roundOut_sound (square_sound h) p

theorem abs {p : ℕ} {a : Option Box} {x : ℝ} (ha : Approx a x) :
    Approx ((intervalArithmetic p).abs a) (realArithmetic.abs x) :=
  ha.map fun _ h => abs_sound h

theorem sqrt {p : ℕ} {a : Option Box} {x : ℝ} (ha : Approx a x) :
    Approx ((intervalArithmetic p).sqrt a) (realArithmetic.sqrt x) :=
  ha.bind fun _ h => by
    rw [strictOut_eq]
    exact fun _ eq => boxSqrt_sound h eq

theorem exp {p : ℕ} {a : Option Box} {x : ℝ} (ha : Approx a x) :
    Approx ((intervalArithmetic p).exp a) (realArithmetic.exp x) :=
  ha.bind fun _ h => by
    rw [strictOut_eq]
    exact fun _ eq => boxExp_sound h eq

theorem log {p : ℕ} {a : Option Box} {x : ℝ} (ha : Approx a x) :
    Approx ((intervalArithmetic p).log a) (realArithmetic.log x) :=
  ha.bind fun _ h => by
    rw [strictOut_eq]
    exact fun _ eq => boxLogRatio_sound h eq

theorem wave {p : ℕ} {a : Option Box} {x : ℝ} (ha : Approx a x) :
    ApproxPair ((intervalArithmetic p).wave a) (realArithmetic.wave x) := by
  cases a with
  | none => exact ⟨by simp [intervalArithmetic, Approx], by simp [intervalArithmetic, Approx]⟩
  | some b =>
    cases he : boxWave p b with
    | none =>
      exact ⟨by simp [intervalArithmetic, Approx, he], by simp [intervalArithmetic, Approx, he]⟩
    | some w =>
      obtain ⟨cosine, sinc⟩ := w
      obtain ⟨hc, hs⟩ := boxWave_sound (ha b rfl) he
      constructor
      · simpa [intervalArithmetic, realArithmetic, he] using some hc
      · simpa [intervalArithmetic, realArithmetic, he] using some hs

end Approx

structure SectionModel (α : Type) where
  length : α
  radiusIn : α
  radiusOut : α
  radialSlope : α
  growth : α
  outletSlope : α

def sectionModel (o : Arithmetic α) (s : Section) : SectionModel α :=
  let length := o.rat s.length
  let rIn := o.sqrt (o.rat s.inletArea)
  let rOut := o.sqrt (o.rat s.outletArea)
  let slope := o.div (o.sub rOut rIn) length
  let growth := if s.profile = .exponential then o.div (o.log (o.div rOut rIn)) length else o.rat 0
  let outletSlope := if s.profile = .exponential then growth else o.div slope rOut
  ⟨length, rIn, rOut, slope, growth, outletSlope⟩

def sectionRadius (o : Arithmetic α) (s : SectionModel α) (profile : Profile) (x : α) : α :=
  if profile = .exponential then o.mul s.radiusIn (o.exp (o.mul (o.mul s.growth s.length) x))
  else o.add s.radiusIn (o.mul (o.sub s.radiusOut s.radiusIn) x)

def sectionSlope (o : Arithmetic α) (s : SectionModel α) (profile : Profile) (radius : α) : α :=
  if profile = .exponential then s.growth else o.div s.radialSlope radius

/-- Prepare the section parameters once for all its position evaluations. -/
def withSectionModel (o : Arithmetic α) (s : SectionModel α) (k : SectionModel α → β) : β :=
  o.withValue s.length fun length =>
    o.withValue s.radiusIn fun rIn =>
      o.withValue s.radiusOut fun rOut =>
        o.withValue s.radialSlope fun slope =>
          o.withValue s.growth fun growth =>
            o.withValue s.outletSlope fun outlet => k ⟨length, rIn, rOut, slope, growth, outlet⟩

theorem withSectionModel_eq (o : Arithmetic α) (s : SectionModel α) (k : SectionModel α → β) :
    withSectionModel o s k = k s := by
  cases s
  simp [withSectionModel, o.withValue_eq]

/-- Pressure is divided by angular frequency before propagation, including at DC. -/
def position (o : Arithmetic α) (s : SectionModel α) (profile : Profile)
    (k2 density x : α) (downstream : α × α) : (α × α) × α :=
  o.withValue (sectionRadius o s profile x) fun radius =>
    let ratio := o.div s.radiusOut radius
    let inletSlope := sectionSlope o s profile radius
    let q2 := o.sub k2 (o.square s.growth)
    let remaining := o.mul s.length (o.sub (o.rat 1) x)
    let wave := o.wave (o.mul q2 (o.square remaining))
    let sineOverQ := o.mul remaining wave.2
    let area := o.mul radius s.radiusOut
    let a := o.mul ratio (o.sub wave.1 (o.mul s.outletSlope sineOverQ))
    let b := o.mul (o.div density area) sineOverQ
    let c := o.mul (o.div area density)
      (o.add (o.mul (o.add q2 (o.mul inletSlope s.outletSlope)) sineOverQ)
        (o.mul (o.sub s.outletSlope inletSlope) wave.1))
    let d := o.div (o.add wave.1 (o.mul inletSlope sineOverQ)) ratio
    ((o.add (o.mul a downstream.1) (o.mul b downstream.2),
      o.sub (o.mul d downstream.2) (o.mul c downstream.1)), o.square radius)

def speedAt (o : Arithmetic α) (atPosition : (α × α) × α) : α :=
  o.div (o.abs atPosition.1.2) atPosition.2

def traverse (o : Arithmetic α) (k2 density : α) (mouth : α × α) :
    List Section → (α × α) × List (α → α)
  | [] => (mouth, [])
  | s :: rest =>
    let downstream := traverse o k2 density mouth rest
    o.withValue downstream.1.1 fun pressure =>
      o.withValue downstream.1.2 fun flow =>
        withSectionModel o (sectionModel o s) fun model =>
          let atPosition := fun x => position o model s.profile k2 density x (pressure, flow)
          ((atPosition (o.rat 0)).1, (fun x => speedAt o (atPosition x)) :: downstream.2)

def ductResponse (o : Arithmetic α) (path : DuctPath) (speed density f : α) :
    (α × α) × List (α → α) :=
  let inletArea := (path.sections.head?.map Section.inletArea).getD 0
  let mouthArea := (path.sections.getLast?.map Section.outletArea).getD 0
  let inletLength := path.inletCorrection + path.junctionInertances.sum
  let inlet := o.div (o.mul density (o.rat inletLength)) (o.rat inletArea)
  let outlet := o.div (o.mul density (o.rat path.outletCorrection)) (o.rat mouthArea)
  let k := o.div (o.mul (o.mul (o.rat 2) o.pi)
    (o.sqrt (o.rat (path.inertanceFactor * path.complianceFactor)))) speed
  o.withValue (o.square (o.mul k f)) fun k2 =>
    o.withValue (o.mul density (o.rat path.inertanceFactor)) fun sectionDensity =>
      let propagated := traverse o k2 sectionDensity (outlet, o.rat 1) path.sections
      ((o.add propagated.1.1 (o.mul inlet propagated.1.2), propagated.1.2), propagated.2)

def exactDuctState (path : DuctPath) (speed density f : ℝ) : ℝ × ℝ :=
  (ductResponse realArithmetic path speed density f).1

def exactSectionSpeed (path : DuctPath) (speed density f : ℝ) (secIdx : ℕ) (x : ℝ) : ℝ :=
  ((ductResponse realArithmetic path speed density f).2[secIdx]?.getD (fun _ => 0)) x

def exactDcMass (path : DuctPath) (speed density : ℝ) : ℝ :=
  (exactDuctState path speed density 0).1 / (path.count : ℝ)

def exactTuningResidual (path : DuctPath) (volume speed f : ℝ) : ℝ :=
  let state := exactDuctState path speed 1 f
  (2 * Real.pi * f) ^ 2 * (volume / speed ^ 2) * state.1 - (path.count : ℝ) * state.2

/-- The evaluators in the returned list follow the original throat-to-mouth section order. -/
def evalDuctResponse (prec : ℕ) (path : DuctPath) (speed density : ℚ) (freq : Box) :
    Option (Box × Box × List (Box → Option Box)) := do
  let model := ductResponse (intervalArithmetic prec) path (some (Box.point speed))
    (some (Box.point density)) (some freq)
  return (← model.1.1, ← model.1.2, model.2.map (fun position fraction => position (some fraction)))

def evalDuctDcMass (prec : ℕ) (path : DuctPath) (speed density : ℚ) : Option Box := do
  let (numerator, _, _) ← evalDuctResponse prec path speed density (Box.point 0)
  div prec numerator (Box.point path.count)

def evalDuctTuningResidual (prec : ℕ) (path : DuctPath) (volume speed : ℚ) (freq : Box) :
    Option (Box × Box) := do
  let (numerator, denominator, _) ← evalDuctResponse prec path speed 1 freq
  let omega := mul prec (mul prec (Box.point 2) piBox) freq
  let compliance ← div prec (Box.point volume) (square prec (Box.point speed))
  return (sub prec (mul prec (mul prec (square prec omega) compliance) numerator)
    (mul prec (Box.point path.count) denominator), denominator)

private theorem sectionModel_sound (p : ℕ) (s : Section) :
    let a := sectionModel (intervalArithmetic p) s
    let x := sectionModel realArithmetic s
    Approx a.length x.length ∧ Approx a.radiusIn x.radiusIn ∧ Approx a.radiusOut x.radiusOut ∧
      Approx a.radialSlope x.radialSlope ∧ Approx a.growth x.growth ∧ Approx a.outletSlope x.outletSlope := by
  simp only [sectionModel]
  by_cases he : s.profile = .exponential <;> simp [he]
  all_goals
    repeat' first
      | exact Approx.rat _ _
      | apply Approx.sqrt
      | apply Approx.div
      | apply Approx.log
      | apply Approx.sub
      | constructor

private theorem position_sound (p : ℕ) (s : Section) {k d f : Option Box} {k' d' f' : ℝ}
    {down : Option Box × Option Box} {down' : ℝ × ℝ}
    (hk : Approx k k') (hd : Approx d d') (hf : Approx f f') (hs : ApproxPair down down') :
    let a := position (intervalArithmetic p) (sectionModel (intervalArithmetic p) s) s.profile k d f down
    let x := position realArithmetic (sectionModel realArithmetic s) s.profile k' d' f' down'
    ApproxPair a.1 x.1 ∧ Approx a.2 x.2 := by
  obtain ⟨hp, hq⟩ := hs
  obtain ⟨hl, hin, hout, hrad, hg, hsl⟩ := sectionModel_sound p s
  have hr : Approx
      (sectionRadius (intervalArithmetic p) (sectionModel (intervalArithmetic p) s) s.profile f)
      (sectionRadius realArithmetic (sectionModel realArithmetic s) s.profile f') := by
    by_cases he : s.profile = .exponential
    · simpa only [sectionRadius, he, ite_true] using
        Approx.mul (p := p) hin (Approx.exp (p := p)
          (Approx.mul (p := p) (Approx.mul (p := p) hg hl) hf))
    · simpa only [sectionRadius, he, ite_false] using
        Approx.add (p := p) hin (Approx.mul (p := p) (Approx.sub (p := p) hout hin) hf)
  have hi : Approx
      (sectionSlope (intervalArithmetic p) (sectionModel (intervalArithmetic p) s) s.profile
        (sectionRadius (intervalArithmetic p) (sectionModel (intervalArithmetic p) s) s.profile f))
      (sectionSlope realArithmetic (sectionModel realArithmetic s) s.profile
        (sectionRadius realArithmetic (sectionModel realArithmetic s) s.profile f')) := by
    by_cases he : s.profile = .exponential
    · simpa only [sectionSlope, he, ite_true] using hg
    · simpa only [sectionSlope, he, ite_false] using Approx.div (p := p) hrad hr
  have hratio := Approx.div (p := p) hout hr
  have hrem := Approx.mul (p := p) hl (Approx.sub (p := p) (Approx.rat p 1) hf)
  have hq2 := Approx.sub (p := p) hk (Approx.square (p := p) hg)
  obtain ⟨hc, hz⟩ := Approx.wave (p := p) (Approx.mul (p := p) hq2 (Approx.square (p := p) hrem))
  have hsin := Approx.mul (p := p) hrem hz
  have harea := Approx.mul (p := p) hr hout
  have ha := Approx.mul (p := p) hratio (Approx.sub (p := p) hc (Approx.mul (p := p) hsl hsin))
  have hb := Approx.mul (p := p) (Approx.div (p := p) hd harea) hsin
  have hc' := Approx.mul (p := p) (Approx.div (p := p) harea hd)
    (Approx.add (p := p)
      (Approx.mul (p := p) (Approx.add (p := p) hq2 (Approx.mul (p := p) hi hsl)) hsin)
      (Approx.mul (p := p) (Approx.sub (p := p) hsl hi) hc))
  have hd' := Approx.div (p := p) (Approx.add (p := p) hc (Approx.mul (p := p) hi hsin)) hratio
  simp only [position, Arithmetic.withValue_eq]
  exact ⟨⟨Approx.add (p := p) (Approx.mul (p := p) ha hp) (Approx.mul (p := p) hb hq),
    Approx.sub (p := p) (Approx.mul (p := p) hd' hq) (Approx.mul (p := p) hc' hp)⟩,
    Approx.square (p := p) hr⟩

def ApproxPosition (a : Option Box → Option Box) (x : ℝ → ℝ) : Prop :=
  ∀ b f, Approx b f → Approx (a b) (x f)

private theorem traverse_sound (p : ℕ) (sections : List Section)
    {k d : Option Box} {k' d' : ℝ} (hk : Approx k k') (hd : Approx d d')
    {mouth : Option Box × Option Box} {mouth' : ℝ × ℝ} (hm : ApproxPair mouth mouth') :
    let a := traverse (intervalArithmetic p) k d mouth sections
    let x := traverse realArithmetic k' d' mouth' sections
    ApproxPair a.1 x.1 ∧ List.Forall₂ ApproxPosition a.2 x.2 := by
  induction sections with
  | nil => exact ⟨hm, .nil⟩
  | cons s rest ih =>
    simp only [traverse, Arithmetic.withValue_eq, withSectionModel_eq, Prod.mk.eta]
    rcases ih with ⟨hstate, hpositions⟩
    refine ⟨(position_sound p s hk hd (Approx.rat p 0) hstate).1, .cons ?_ hpositions⟩
    intro b f hf
    obtain ⟨⟨_, hflow⟩, harea⟩ := position_sound p s hk hd hf hstate
    exact Approx.div (Approx.abs hflow) harea

private theorem ductResponse_sound (prec : ℕ) (path : DuctPath)
    {speed density freq : Option Box} {speed' density' freq' : ℝ}
    (hs : Approx speed speed') (hd : Approx density density') (hf : Approx freq freq') :
    let a := ductResponse (intervalArithmetic prec) path speed density freq
    let x := ductResponse realArithmetic path speed' density' freq'
    ApproxPair a.1 x.1 ∧ List.Forall₂ ApproxPosition a.2 x.2 := by
  have hin := Approx.div (p := prec) (Approx.mul (p := prec) hd (Approx.rat prec
    (path.inletCorrection + path.junctionInertances.sum)))
    (Approx.rat prec ((path.sections.head?.map Section.inletArea).getD 0))
  have hout := Approx.div (p := prec) (Approx.mul (p := prec) hd (Approx.rat prec path.outletCorrection))
    (Approx.rat prec ((path.sections.getLast?.map Section.outletArea).getD 0))
  have hk := Approx.div (p := prec) (Approx.mul (p := prec) (Approx.mul (p := prec) (Approx.rat prec 2) (Approx.pi prec))
    (Approx.sqrt (p := prec) (Approx.rat prec (path.inertanceFactor * path.complianceFactor)))) hs
  obtain ⟨⟨hpressure, hflow⟩, hpositions⟩ := traverse_sound prec path.sections
    (Approx.square (p := prec) (Approx.mul (p := prec) hk hf))
    (Approx.mul (p := prec) hd (Approx.rat prec path.inertanceFactor))
    (show ApproxPair (_, (intervalArithmetic prec).rat 1) (_, realArithmetic.rat 1) from
      ⟨hout, Approx.rat prec 1⟩)
  simp only [ductResponse, Arithmetic.withValue_eq]
  exact ⟨⟨Approx.add (p := prec) hpressure (Approx.mul (p := prec) hin hflow), hflow⟩, hpositions⟩

def EnclosesPosition (a : Box → Option Box) (x : ℝ → ℝ) : Prop :=
  ∀ span f, span.Contains f → Approx (a span) (x f)

private theorem forall₂_map_position {as : List (Option Box → Option Box)} {xs : List (ℝ → ℝ)}
    (h : List.Forall₂ ApproxPosition as xs) :
    List.Forall₂ EnclosesPosition (as.map (fun a b => a (some b))) xs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (fun b f hf => h (some b) f (Approx.some hf)) ih

theorem evalDuctResponse_sound {prec : ℕ} {path : DuctPath} {speed density : ℚ} {freq : Box}
    {n d : Box} {positions : List (Box → Option Box)}
    (h : evalDuctResponse prec path speed density freq = some (n, d, positions))
    {f : ℝ} (hf : freq.Contains f) :
    n.Contains (exactDuctState path speed density f).1 ∧
    d.Contains (exactDuctState path speed density f).2 ∧
    List.Forall₂ EnclosesPosition positions (ductResponse realArithmetic path speed density f).2 := by
  let model := ductResponse (intervalArithmetic prec) path (some (Box.point speed))
    (some (Box.point density)) (some freq)
  obtain ⟨⟨hn, hd⟩, hp⟩ := ductResponse_sound prec path (Approx.rat prec speed)
    (Approx.rat prec density) (Approx.some hf)
  change (do
    return (← model.1.1, ← model.1.2, model.2.map (fun (pos : Option Box → Option Box) (x : Box) => pos (some x)))) = _ at h
  cases en : model.1.1 with
  | none => simp [en] at h
  | some numerator =>
    cases ed : model.1.2 with
    | none => simp [en, ed] at h
    | some denominator =>
      simp [en, ed] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hn _ en, hd _ ed, forall₂_map_position hp⟩

theorem evalDuctDcMass_sound {prec : ℕ} {path : DuctPath} {speed density : ℚ} {out : Box}
    (h : evalDuctDcMass prec path speed density = some out) :
    out.Contains (exactDcMass path speed density) := by
  unfold evalDuctDcMass at h
  cases he : evalDuctResponse prec path speed density (Box.point 0) with
  | none => simp [he] at h
  | some result =>
    obtain ⟨n, d, positions⟩ := result
    simp [he] at h
    have hs := (evalDuctResponse_sound he (point_sound 0)).1
    simpa only [exactDcMass, Rat.cast_zero] using div_contains hs (point_sound path.count) h

theorem evalDuctTuningResidual_sound {prec : ℕ} {path : DuctPath} {volume speed : ℚ} {freq : Box}
    {residual denominator : Box}
    (h : evalDuctTuningResidual prec path volume speed freq = some (residual, denominator))
    {f : ℝ} (hf : freq.Contains f) :
    residual.Contains (exactTuningResidual path volume speed f) ∧
    denominator.Contains (exactDuctState path speed 1 f).2 := by
  unfold evalDuctTuningResidual at h
  cases he : evalDuctResponse prec path speed 1 freq with
  | none => simp [he] at h
  | some result =>
    obtain ⟨n, d, positions⟩ := result
    simp [he] at h
    cases hc : div prec (Box.point volume) (square prec (Box.point speed)) with
    | none => simp [hc] at h
    | some c =>
      simp [hc] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hn, hd, _⟩ := evalDuctResponse_sound he hf
      have hw := roundOut_sound (mul_sound (roundOut_sound (mul_sound (point_sound 2) piBox_sound) prec) hf) prec
      have hcomp := div_contains (point_sound volume) (roundOut_sound (square_sound (point_sound speed)) prec) hc
      have hres := roundOut_sound (sub_sound (roundOut_sound (mul_sound
        (roundOut_sound (mul_sound (roundOut_sound (square_sound hw) prec) hcomp) prec) hn) prec)
        (roundOut_sound (mul_sound (point_sound path.count) hd) prec)) prec
      simpa only [exactTuningResidual, Rat.cast_one, Rat.cast_ofNat, sub, mul, square] using And.intro hres hd


structure SpatialSample where
  index : ℕ
  fraction : ℚ
  value : Box

structure SpatialCell where
  span : Box
  sample : SpatialSample
  ceiling : ℚ

def fractionUnit : Box := ⟨0, 1⟩

def sampleAt (positions : List (Box → Option Box)) (index : ℕ) (fraction : ℚ) :
    Option SpatialSample := do
  let eval ← positions[index]?
  return ⟨index, fraction, ← eval (Box.point fraction)⟩

def cellAt (positions : List (Box → Option Box)) (index : ℕ) (span : Box) :
    Option SpatialCell := do
  let eval ← positions[index]?
  let sample ← sampleAt positions index ((span.lo + span.hi) / 2)
  let bounds ← eval span
  return ⟨span, sample, bounds.hi⟩

/-- Keep the cells in physical order, starting at the mouth, including on ties. -/
def largestCell : List SpatialCell → Option (List SpatialCell × SpatialCell × List SpatialCell)
  | [] => none
  | cell :: rest =>
    match largestCell rest with
    | none => some ([], cell, rest)
    | some (before, largest, after) =>
      if largest.ceiling ≤ cell.ceiling then some ([], cell, rest)
      else some (cell :: before, largest, after)

def betterSample (first second : SpatialSample) : SpatialSample :=
  if first.value.lo < second.value.lo then second else first

/-- Best-first spatial subdivision. The width of the sample accounts for variation
    already attributable to the frequency span, as in the runtime search. -/
def refinePeak (positions : List (Box → Option Box)) :
    ℕ → List SpatialCell → SpatialSample → Option (SpatialSample × ℚ)
  | fuel, cells, witness => do
    let (before, worst, after) ← largestCell cells
    let variation := worst.sample.value.hi - worst.sample.value.lo
    let ceiling := worst.ceiling
    if ceiling - witness.value.lo - variation ≤ witness.value.lo / 2048 then
      return (witness, ceiling)
    else
      match fuel with
      | 0 => return (witness, ceiling)
      | n + 1 =>
        let x := worst.sample.fraction
        let a ← cellAt positions worst.sample.index ⟨worst.span.lo, x⟩
        let b ← cellAt positions worst.sample.index ⟨x, worst.span.hi⟩
        refinePeak positions n (before ++ a :: b :: after)
          (betterSample (betterSample witness a.sample) b.sample)

def initialSample (positions : List (Box → Option Box)) (includeThroat : Bool) :
    Option SpatialSample := do
  let mouth ← sampleAt positions (positions.length - 1) 1
  if includeThroat then
    let throat ← sampleAt positions 0 0
    return betterSample mouth throat
  else
    return mouth

def spatialPeak (positions : List (Box → Option Box)) (fuel : ℕ) (includeThroat : Bool := false) :
    Option (SpatialSample × ℚ) := do
  let initial ← initialSample positions includeThroat
  let cells ← (List.range positions.length).reverse.mapM (fun i => cellAt positions i fractionUnit)
  let witness := cells.foldl (fun best cell => betterSample best cell.sample) initial
  refinePeak positions fuel cells witness

def evalDuctSpatialPeak (prec : ℕ) (path : DuctPath) (speed density : ℚ) (freq : Box)
    (fuel : ℕ) : Option Box := do
  let (_, _, positions) ← evalDuctResponse prec path speed density freq
  let (sample, upper) ← spatialPeak positions fuel
  return ⟨sample.value.lo, upper⟩

def PositionsSound (positions : List (Box → Option Box)) (freq : Box)
    (usage : ℝ → ℕ → ℝ → ℝ) : Prop :=
  ∀ i eval, positions[i]? = some eval → ∀ f, freq.Contains f →
    EnclosesPosition eval (usage f i)

def SpatialSample.Valid (s : SpatialSample) (n : ℕ) (freq : Box)
    (usage : ℝ → ℕ → ℝ → ℝ) : Prop :=
  s.index < n ∧ fractionUnit.Contains (s.fraction : ℝ) ∧
    ∀ f, freq.Contains f → s.value.Contains (usage f s.index s.fraction)

def SpatialCell.Valid (c : SpatialCell) (n : ℕ) (freq : Box)
    (usage : ℝ → ℕ → ℝ → ℝ) : Prop :=
  c.sample.Valid n freq usage ∧
  0 ≤ c.span.lo ∧ c.span.lo ≤ c.sample.fraction ∧ c.sample.fraction ≤ c.span.hi ∧ c.span.hi ≤ 1 ∧
    ∀ f, freq.Contains f → ∀ x, c.span.Contains x → usage f c.sample.index x ≤ c.ceiling

def Covers (cells : List SpatialCell) (n : ℕ) : Prop :=
  ∀ i, i < n → ∀ x : ℝ, fractionUnit.Contains x →
    ∃ c ∈ cells, c.sample.index = i ∧ c.span.Contains x

private theorem sampleAt_sound {positions : List (Box → Option Box)} {freq : Box}
    {usage : ℝ → ℕ → ℝ → ℝ} (valid : PositionsSound positions freq usage)
    {i : ℕ} {x : ℚ} (hx : fractionUnit.Contains x) {s : SpatialSample}
    (h : sampleAt positions i x = some s) :
    s.index = i ∧ s.fraction = x ∧ s.Valid positions.length freq usage := by
  unfold sampleAt at h
  cases he : positions[i]? with
  | none => simp [he] at h
  | some eval =>
    cases hb : eval (Box.point x) with
    | none => simp [he, hb] at h
    | some bound =>
      simp [he, hb] at h
      subst s
      refine ⟨rfl, rfl, List.getElem?_eq_some_iff.mp he |>.choose, hx, ?_⟩
      intro f hf
      exact valid i eval he f hf _ x (point_sound x) bound hb

private theorem cellAt_sound {positions : List (Box → Option Box)} {freq : Box}
    {usage : ℝ → ℕ → ℝ → ℝ} (valid : PositionsSound positions freq usage) {i : ℕ} {span : Box}
    (h0 : 0 ≤ span.lo) (hle : span.lo ≤ span.hi) (h1 : span.hi ≤ 1)
    {c : SpatialCell} (h : cellAt positions i span = some c) :
    c.sample.index = i ∧ c.span = span ∧ c.Valid positions.length freq usage := by
  let x := (span.lo + span.hi) / 2
  have hlx : span.lo ≤ x := by dsimp [x]; linarith
  have hxh : x ≤ span.hi := by dsimp [x]; linarith
  have hx : fractionUnit.Contains (x : ℝ) :=
    ⟨by exact_mod_cast h0.trans hlx, by exact_mod_cast hxh.trans h1⟩
  change (do
    let eval ← positions[i]?
    let sample ← sampleAt positions i x
    let bounds ← eval span
    return SpatialCell.mk span sample bounds.hi) = some c at h
  cases he : positions[i]? with
  | none => simp [he] at h
  | some eval =>
    cases hs : sampleAt positions i x with
    | none => simp [he, hs] at h
    | some sample =>
      cases hb : eval span with
      | none => simp [he, hs, hb] at h
      | some bounds =>
        simp [he, hs, hb] at h
        subst c
        obtain ⟨hi, hm, hv⟩ := sampleAt_sound valid hx hs
        refine ⟨hi, rfl, hv, h0, ?_, ?_, h1, ?_⟩
        · simpa only [hm] using hlx
        · simpa only [hm] using hxh
        · intro f hf y hy
          simpa only [hi] using (valid i eval he f hf _ y hy bounds hb).2

private theorem largestCell_sound {cells before after : List SpatialCell} {c : SpatialCell}
    (h : largestCell cells = some (before, c, after)) :
    cells = before ++ c :: after ∧ ∀ other ∈ cells, other.ceiling ≤ c.ceiling := by
  induction cells generalizing before after c with
  | nil => simp [largestCell] at h
  | cons a rest ih =>
    unfold largestCell at h
    cases he : largestCell rest with
    | none =>
      cases rest with
      | nil =>
        simp [he] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp
      | cons b tail =>
        unfold largestCell at he
        split at he <;> simp_all
        split at he <;> contradiction
    | some parts =>
      obtain ⟨left, worst, right⟩ := parts
      obtain ⟨eq, maxima⟩ := ih he
      by_cases ha : worst.ceiling ≤ a.ceiling
      · simp [he, ha] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun other ho => (List.mem_cons.mp ho).elim
          (fun e => e ▸ le_rfl) (fun hm => (maxima _ hm).trans ha)⟩
      · simp [he, ha] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨congrArg (a :: ·) eq, fun other ho => (List.mem_cons.mp ho).elim
          (fun e => e ▸ (le_of_not_ge ha)) (maxima other)⟩

private theorem betterSample_sound {n : ℕ} {freq : Box} {usage : ℝ → ℕ → ℝ → ℝ}
    {a b : SpatialSample} (ha : a.Valid n freq usage) (hb : b.Valid n freq usage) :
    (betterSample a b).Valid n freq usage := by
  unfold betterSample
  split <;> assumption

private theorem spatialCeiling_sound {n : ℕ} {freq : Box} {usage : ℝ → ℕ → ℝ → ℝ}
    {cells : List SpatialCell} (coverage : Covers cells n)
    (checked : ∀ c ∈ cells, c.Valid n freq usage)
    {upper : ℚ} (maxima : ∀ c ∈ cells, c.ceiling ≤ upper) :
    ∀ f, freq.Contains f → ∀ i, i < n → ∀ x, fractionUnit.Contains x →
      usage f i x ≤ (upper : ℝ) := by
  intro f hf i hi x hx
  obtain ⟨c, hm, rfl, hcx⟩ := coverage i hi x hx
  exact ((checked c hm).2.2.2.2.2 f hf x hcx).trans (Rat.cast_le.mpr (maxima c hm))

private theorem refinePeak_sound {positions : List (Box → Option Box)} {freq : Box}
    {usage : ℝ → ℕ → ℝ → ℝ} (valid : PositionsSound positions freq usage)
    {fuel : ℕ} {cells : List SpatialCell} {witness sample : SpatialSample} {upper : ℚ}
    (coverage : Covers cells positions.length)
    (checked : ∀ c ∈ cells, c.Valid positions.length freq usage)
    (hw : witness.Valid positions.length freq usage)
    (h : refinePeak positions fuel cells witness = some (sample, upper)) :
    sample.Valid positions.length freq usage ∧
      ∀ f, freq.Contains f → ∀ i, i < positions.length → ∀ x, fractionUnit.Contains x →
        usage f i x ≤ (upper : ℝ) := by
  induction fuel generalizing cells witness sample upper with
  | zero =>
    cases he : largestCell cells with
    | none => rw [refinePeak, he] at h
              simp at h
    | some parts =>
      obtain ⟨before, worst, after⟩ := parts
      obtain ⟨_, maxima⟩ := largestCell_sound he
      rw [refinePeak, he] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw, spatialCeiling_sound coverage checked maxima⟩
  | succ fuel ih =>
    cases he : largestCell cells with
    | none => rw [refinePeak, he] at h
              simp at h
    | some parts =>
      obtain ⟨before, worst, after⟩ := parts
      obtain ⟨eq, maxima⟩ := largestCell_sound he
      rw [refinePeak, he] at h
      simp at h
      split at h
      · obtain ⟨rfl, rfl⟩ := h
        exact ⟨hw, spatialCeiling_sound coverage checked maxima⟩
      · have hv := checked worst (by rw [eq]; simp)
        let left : Box := ⟨worst.span.lo, worst.sample.fraction⟩
        let right : Box := ⟨worst.sample.fraction, worst.span.hi⟩
        change (do
          let a ← cellAt positions worst.sample.index left
          let b ← cellAt positions worst.sample.index right
          refinePeak positions fuel (before ++ a :: b :: after)
            (betterSample (betterSample witness a.sample) b.sample)) = some (sample, upper) at h
        cases ha : cellAt positions worst.sample.index left with
        | none => simp [ha] at h
        | some a =>
          cases hb : cellAt positions worst.sample.index right with
          | none => simp [ha, hb] at h
          | some b =>
            simp [ha, hb] at h
            obtain ⟨ai, aspan, av⟩ := cellAt_sound valid (span := left) hv.2.1 hv.2.2.1
              (hv.2.2.2.1.trans hv.2.2.2.2.1) ha
            obtain ⟨bi, bspan, bv⟩ := cellAt_sound valid (span := right) (hv.2.1.trans hv.2.2.1)
              hv.2.2.2.1 hv.2.2.2.2.1 hb
            apply ih _ _ (betterSample_sound (betterSample_sound hw av.1) bv.1) h
            · intro i hi x hx
              obtain ⟨c, hm, ci, hcx⟩ := coverage i hi x hx
              simp only [eq, List.mem_append, List.mem_cons] at hm
              rcases hm with hm | hEq | hm
              · exact ⟨c, by simp [hm], ci, hcx⟩
              · subst c
                rcases le_total x (worst.sample.fraction : ℝ) with hl | hr
                · exact ⟨a, by simp, ai.trans ci, aspan.symm ▸ (show left.Contains x from ⟨hcx.1, hl⟩)⟩
                · exact ⟨b, by simp, bi.trans ci, bspan.symm ▸ (show right.Contains x from ⟨hr, hcx.2⟩)⟩
              · exact ⟨c, by simp [hm], ci, hcx⟩
            · intro c hm
              simp only [List.mem_append, List.mem_cons] at hm
              rcases hm with hm | rfl | rfl | hm
              · exact checked _ (by rw [eq]; simp [hm])
              · exact av
              · exact bv
              · exact checked _ (by rw [eq]; simp [hm])

private theorem initialCells_sound {positions : List (Box → Option Box)} {freq : Box}
    {usage : ℝ → ℕ → ℝ → ℝ} (valid : PositionsSound positions freq usage)
    {indices : List ℕ} {cells : List SpatialCell}
    (h : indices.mapM (fun i => cellAt positions i fractionUnit) = some cells) :
    (∀ i ∈ indices, ∃ c ∈ cells, c.sample.index = i ∧ c.span = fractionUnit) ∧
    (∀ c ∈ cells, c.Valid positions.length freq usage) := by
  induction indices generalizing cells with
  | nil => simp at h; subst cells; simp
  | cons i rest ih =>
    simp only [List.mapM_cons] at h
    cases hc : cellAt positions i fractionUnit with
    | none => simp [hc] at h
    | some c =>
      cases hr : rest.mapM (fun i => cellAt positions i fractionUnit) with
      | none => simp [hc, hr] at h
      | some tail =>
        simp [hc, hr] at h
        subst cells
        obtain ⟨hi, hs, hv⟩ := cellAt_sound valid (by decide) (by decide) (by decide) hc
        obtain ⟨ex, htail⟩ := ih hr
        refine ⟨?_, ?_⟩
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact ⟨c, by simp, hi, hs⟩
          · obtain ⟨u, hu, hui, hus⟩ := ex j hj
            exact ⟨u, List.mem_cons_of_mem _ hu, hui, hus⟩
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hv
          · exact htail _ hu

private theorem foldSamples_sound {n : ℕ} {freq : Box} {usage : ℝ → ℕ → ℝ → ℝ}
    {cells : List SpatialCell} (valid : ∀ c ∈ cells, c.Valid n freq usage)
    {sample : SpatialSample} (hs : sample.Valid n freq usage) :
    (cells.foldl (fun best cell => betterSample best cell.sample) sample).Valid n freq usage := by
  induction cells generalizing sample with
  | nil => exact hs
  | cons c rest ih =>
    apply ih (fun d hd => valid d (List.mem_cons_of_mem _ hd))
    exact betterSample_sound hs (valid c (by simp)).1

private theorem initialSample_sound {positions : List (Box → Option Box)} {freq : Box}
    {usage : ℝ → ℕ → ℝ → ℝ} (valid : PositionsSound positions freq usage)
    {includeThroat : Bool} {initial : SpatialSample}
    (h : initialSample positions includeThroat = some initial) :
    initial.Valid positions.length freq usage := by
  unfold initialSample at h
  cases he : sampleAt positions (positions.length - 1) 1 with
  | none => simp [he] at h
  | some mouth =>
    have hm := (sampleAt_sound valid (by constructor <;> norm_num [fractionUnit]) he).2.2
    cases includeThroat
    · simp [he] at h
      exact h ▸ hm
    · cases ht : sampleAt positions 0 0 with
      | none => simp [he, ht] at h
      | some throat =>
        simp [he, ht] at h
        have hv := (sampleAt_sound valid (by constructor <;> norm_num [fractionUnit]) ht).2.2
        exact h ▸ betterSample_sound hm hv

theorem spatialPeak_sound {positions : List (Box → Option Box)} {freq : Box}
    {usage : ℝ → ℕ → ℝ → ℝ} (valid : PositionsSound positions freq usage)
    {fuel : ℕ} {includeThroat : Bool} {sample : SpatialSample} {upper : ℚ}
    (h : spatialPeak positions fuel includeThroat = some (sample, upper)) :
    sample.Valid positions.length freq usage ∧
      ∀ f, freq.Contains f → ∀ i, i < positions.length → ∀ x, fractionUnit.Contains x →
        usage f i x ≤ (upper : ℝ) := by
  unfold spatialPeak at h
  cases hm : initialSample positions includeThroat with
  | none => simp [hm] at h
  | some initial =>
    cases hc : (List.range positions.length).reverse.mapM (fun i => cellAt positions i fractionUnit) with
    | none => simp [hm, hc] at h
    | some cells =>
      simp [hm, hc] at h
      obtain ⟨ex, validCells⟩ := initialCells_sound valid hc
      have hinit := initialSample_sound valid hm
      apply refinePeak_sound valid _ validCells (foldSamples_sound validCells hinit) h
      intro i hi x hx
      obtain ⟨c, hmem, hi', hs⟩ := ex i (by simpa using hi)
      exact ⟨c, hmem, hi', hs ▸ hx⟩

private theorem traverse_length (o : Arithmetic α) (k d : α) (mouth : α × α)
    (sections : List Section) : (traverse o k d mouth sections).2.length = sections.length := by
  induction sections with
  | nil => rfl
  | cons s rest ih => simp [traverse, Arithmetic.withValue_eq, withSectionModel_eq, ih]

private theorem positions_at {positions : List (Box → Option Box)} {exact : List (ℝ → ℝ)}
    (h : List.Forall₂ EnclosesPosition positions exact)
    {i : ℕ} {eval : Box → Option Box} (he : positions[i]? = some eval) :
    EnclosesPosition eval (exact[i]?.getD (fun _ => 0)) := by
  induction h generalizing i with
  | nil => simp at he
  | cons h _ ih =>
    cases i with
    | zero =>
      simp at he
      subst eval
      exact h
    | succ i => exact ih he

theorem ductPositions_sound {prec : ℕ} {path : DuctPath} {speed density : ℚ} {freq n d : Box}
    {positions : List (Box → Option Box)}
    (eval : evalDuctResponse prec path speed density freq = some (n, d, positions)) :
    PositionsSound positions freq (fun f => exactSectionSpeed path speed density f) := by
  intro i pos hp f hf
  exact positions_at (evalDuctResponse_sound eval hf).2.2 hp

theorem ductPositions_length {prec : ℕ} {path : DuctPath} {speed density : ℚ} {freq n d : Box}
    {positions : List (Box → Option Box)}
    (eval : evalDuctResponse prec path speed density freq = some (n, d, positions))
    {f : ℝ} (hf : freq.Contains f) : positions.length = path.sections.length := by
  exact (evalDuctResponse_sound eval hf).2.2.length_eq.trans
    (by simpa only [ductResponse, Arithmetic.withValue_eq] using
      traverse_length realArithmetic _ _ _ path.sections)

theorem evalDuctSpatialPeak_sound {prec : ℕ} {path : DuctPath} {speed density : ℚ} {freq : Box}
    {fuel : ℕ} {out : Box} (h : evalDuctSpatialPeak prec path speed density freq fuel = some out)
    (nonempty : freq.lo ≤ freq.hi) :
    (∀ f, freq.Contains f → ∀ i, i < path.sections.length → ∀ x,
      x ∈ Set.Icc (0 : ℝ) 1 → exactSectionSpeed path speed density f i x ≤ (out.hi : ℝ)) ∧
    (∃ i, i < path.sections.length ∧ ∃ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ f, freq.Contains f → (out.lo : ℝ) ≤ exactSectionSpeed path speed density f i x) := by
  unfold evalDuctSpatialPeak at h
  cases he : evalDuctResponse prec path speed density freq with
  | none => simp [he] at h
  | some response =>
    obtain ⟨n, d, positions⟩ := response
    cases hp : spatialPeak positions fuel with
    | none => simp [he, hp] at h
    | some pair =>
      obtain ⟨sample, upper⟩ := pair
      simp [he, hp] at h
      subst out
      have len := ductPositions_length he (show freq.Contains (freq.lo : ℝ) from
        ⟨le_rfl, Rat.cast_le.mpr nonempty⟩)
      obtain ⟨⟨indexValid, fractionValid, witness⟩, bound⟩ :=
        spatialPeak_sound (ductPositions_sound he) hp
      simp only [len] at indexValid bound
      refine ⟨?_, ⟨sample.index, indexValid, sample.fraction, ?_, fun f hf => (witness f hf).1⟩⟩
      · simpa [fractionUnit, Box.Contains, Set.mem_Icc] using bound
      · simpa [fractionUnit, Box.Contains, Set.mem_Icc] using fractionValid

end Electroacoustics.DuctInterval
