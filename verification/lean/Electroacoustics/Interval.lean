module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Interval

/-- Exact rational endpoints. Runtime dyadic endpoints are a special case. -/
structure Box where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

def Box.Contains (b : Box) (x : ℝ) : Prop :=
  (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

def Box.point (x : ℚ) : Box := ⟨x, x⟩
def Box.add (a b : Box) : Box := ⟨a.lo + b.lo, a.hi + b.hi⟩
def Box.sub (a b : Box) : Box := ⟨a.lo - b.hi, a.hi - b.lo⟩

def Box.mul (a b : Box) : Box :=
  let p := a.lo * b.lo
  let q := a.lo * b.hi
  let r := a.hi * b.lo
  let s := a.hi * b.hi
  ⟨min (min p q) (min r s), max (max p q) (max r s)⟩

def Box.reciprocal (a : Box) : Option Box :=
  if a.hi < 0 ∨ 0 < a.lo then some ⟨1 / a.hi, 1 / a.lo⟩ else none

def Box.div (a b : Box) : Option Box :=
  (b.reciprocal).map a.mul

def Box.joinMax (a b : Box) : Box := ⟨max a.lo b.lo, max a.hi b.hi⟩

def Box.abs (a : Box) : Box := ⟨max 0 (max a.lo (-a.hi)), max (-a.lo) a.hi⟩

def Box.join (a b : Box) : Box := ⟨min a.lo b.lo, max a.hi b.hi⟩

def Box.containsZero (a : Box) : Prop := a.lo ≤ 0 ∧ 0 ≤ a.hi

def Box.square (a : Box) : Box :=
  ⟨(max 0 (max a.lo (-a.hi))) ^ 2, (max (-a.lo) a.hi) ^ 2⟩

theorem point_sound (x : ℚ) : (Box.point x).Contains x := by
  exact ⟨le_rfl, le_rfl⟩

theorem add_sound {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x + y) := by
  simpa [Box.add, Box.Contains, Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem sub_sound {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.sub b).Contains (x - y) := by
  simpa [Box.sub, Box.Contains, Rat.cast_sub] using
    And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

private theorem mul_bounds {x l h k lo hi : ℝ} (hx : l ≤ x ∧ x ≤ h)
    (hl : lo ≤ l * k ∧ l * k ≤ hi) (hh : lo ≤ h * k ∧ h * k ≤ hi) :
    lo ≤ x * k ∧ x * k ≤ hi := by
  by_cases hk : 0 ≤ k
  · exact ⟨hl.1.trans (mul_le_mul_of_nonneg_right hx.1 hk),
      (mul_le_mul_of_nonneg_right hx.2 hk).trans hh.2⟩
  · exact ⟨hh.1.trans (mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hk)),
      (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hk)).trans hl.2⟩

theorem mul_sound {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x * y) := by
  let p : ℝ := a.lo * (b.lo : ℝ)
  let q : ℝ := a.lo * (b.hi : ℝ)
  let r : ℝ := a.hi * (b.lo : ℝ)
  let s : ℝ := a.hi * (b.hi : ℝ)
  let lo := min (min p q) (min r s)
  let hi := max (max p q) (max r s)
  have hp : lo ≤ p ∧ p ≤ hi := ⟨(min_le_left _ _).trans (min_le_left _ _),
    (le_max_left _ _).trans (le_max_left _ _)⟩
  have hq : lo ≤ q ∧ q ≤ hi := ⟨(min_le_left _ _).trans (min_le_right _ _),
    (le_max_right _ _).trans (le_max_left _ _)⟩
  have hr : lo ≤ r ∧ r ≤ hi := ⟨(min_le_right _ _).trans (min_le_left _ _),
    (le_max_left _ _).trans (le_max_right _ _)⟩
  have hs : lo ≤ s ∧ s ≤ hi := ⟨(min_le_right _ _).trans (min_le_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩
  have left := mul_bounds hx hp hr
  have right := mul_bounds hx hq hs
  have result := mul_bounds hy (by simpa only [mul_comm] using left)
    (by simpa only [mul_comm] using right)
  simpa [Box.Contains, Box.mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul,
    lo, hi, p, q, r, s, mul_comm] using result

theorem reciprocal_sound {a result : Box} {x : ℝ}
    (hx : a.Contains x) (accepted : a.reciprocal = some result) :
    result.Contains (1 / x) := by
  unfold Box.reciprocal at accepted
  split at accepted
  next h =>
    cases accepted
    simp only [Box.Contains, Rat.cast_div, Rat.cast_one]
    rcases h with hn | hp
    · have hn' : (a.hi : ℝ) < 0 := by exact_mod_cast hn
      exact ⟨one_div_le_one_div_of_neg_of_le hn' hx.2,
        one_div_le_one_div_of_neg_of_le (hx.2.trans_lt hn') hx.1⟩
    · have hp' : (0 : ℝ) < a.lo := by exact_mod_cast hp
      exact ⟨one_div_le_one_div_of_le (hp'.trans_le hx.1) hx.2,
        one_div_le_one_div_of_le hp' hx.1⟩
  next => contradiction

theorem div_sound {a b result : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (accepted : a.div b = some result) : result.Contains (x / y) := by
  unfold Box.div at accepted
  cases h : b.reciprocal with
  | none => simp [h] at accepted
  | some inv =>
      simp only [h, Option.map_some, Option.some.injEq] at accepted
      rw [← accepted, ← mul_one_div]
      exact mul_sound hx (reciprocal_sound hy h)

theorem max_sound {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.joinMax b).Contains (max x y) := by
  simpa [Box.Contains, Box.joinMax, Rat.cast_max] using
    And.intro (max_le_max hx.1 hy.1) (max_le_max hx.2 hy.2)

theorem abs_sound {a : Box} {x : ℝ} (hx : a.Contains x) : a.abs.Contains |x| := by
  simp only [Box.Contains, Box.abs, Rat.cast_max, Rat.cast_zero, Rat.cast_neg]
  have lo : max 0 (max (a.lo : ℝ) (-(a.hi : ℝ))) ≤ |x| :=
    max_le (abs_nonneg _) (max_le (hx.1.trans (le_abs_self _))
      ((neg_le_neg hx.2).trans (neg_le_abs _)))
  have hi : |x| ≤ max (-(a.lo : ℝ)) (a.hi : ℝ) := by
    rw [abs_le]
    exact ⟨(neg_le_neg (le_max_left _ _)).trans_eq (neg_neg _) |>.trans hx.1,
      hx.2.trans (le_max_right _ _)⟩
  exact ⟨lo, hi⟩

theorem join_sound {a b : Box} {x : ℝ} (hx : a.Contains x ∨ b.Contains x) :
    (a.join b).Contains x := by
  simp only [Box.Contains, Box.join, Rat.cast_min, Rat.cast_max]
  rcases hx with hx | hx
  · exact ⟨(min_le_left _ _).trans hx.1, hx.2.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans hx.1, hx.2.trans (le_max_right _ _)⟩

theorem not_containsZero_ne_zero {a : Box} {x : ℝ} (h : ¬a.containsZero) (hx : a.Contains x) :
    x ≠ 0 := by
  rintro rfl
  exact h ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩

theorem square_sound {a : Box} {x : ℝ} (hx : a.Contains x) :
    a.square.Contains (x ^ 2) := by
  obtain ⟨lo, hi⟩ := abs_sound hx
  simp only [Box.abs, Rat.cast_max, Rat.cast_zero, Rat.cast_neg] at lo hi
  simp only [Box.Contains, Box.square, Rat.cast_pow, Rat.cast_max, Rat.cast_zero, Rat.cast_neg,
    ← sq_abs x]
  exact ⟨(sq_le_sq₀ (le_max_left _ _) (abs_nonneg _)).mpr lo,
    (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hi)).mpr hi⟩

/-- Check a square-root enclosure by squaring its supplied nonnegative endpoints. -/
def Box.checkRoot (arg out : Box) : Bool :=
  decide (0 ≤ out.lo ∧ 0 ≤ out.hi ∧ out.lo ^ 2 ≤ max 0 arg.lo ∧ arg.hi ≤ out.hi ^ 2)

theorem root_sound {arg out : Box} {x : ℝ} (hx : arg.Contains x)
    (accepted : arg.checkRoot out = true) : out.Contains (Real.sqrt x) := by
  unfold Box.checkRoot at accepted
  obtain ⟨hl, hh, hsq, hup⟩ := of_decide_eq_true accepted
  have hln : 0 ≤ (out.lo : ℝ) := by exact_mod_cast hl
  have hhn : 0 ≤ (out.hi : ℝ) := by exact_mod_cast hh
  have hsq' : (out.lo : ℝ) ^ 2 ≤ max 0 (arg.lo : ℝ) := by exact_mod_cast hsq
  have hup' : (arg.hi : ℝ) ≤ (out.hi : ℝ) ^ 2 := by exact_mod_cast hup
  have hroot : Real.sqrt x ^ 2 = max 0 x := by
    by_cases h : 0 ≤ x
    · rw [max_eq_right h, Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h), max_eq_left (le_of_not_ge h)]
      norm_num
  refine ⟨(sq_le_sq₀ hln (Real.sqrt_nonneg _)).mp ?_,
    (sq_le_sq₀ (Real.sqrt_nonneg _) hhn).mp ?_⟩
  · rw [hroot]
    exact hsq'.trans (max_le_max (le_refl 0) hx.1)
  · rw [hroot, max_le_iff]
    exact ⟨sq_nonneg _, hx.2.trans hup'⟩

theorem root_div_check_sound {arg : Box} {lo hi x : ℝ} (hx : arg.Contains x)
    (hl : 0 ≤ lo) (hlo : 0 < lo → lo ≤ (arg.lo : ℝ) / lo)
    (hh : 0 < hi) (hhi : (arg.hi : ℝ) / hi ≤ hi) :
    lo ≤ Real.sqrt x ∧ Real.sqrt x ≤ hi := by
  refine ⟨?_, Real.sqrt_le_iff.mpr ⟨hh.le, ?_⟩⟩
  · rcases hl.eq_or_lt with h | h
    · rw [← h]
      exact Real.sqrt_nonneg _
    · exact Real.le_sqrt_of_sq_le (by simpa [pow_two] using
        ((le_div_iff₀ h).mp (hlo h)).trans hx.1)
  · simpa [pow_two] using hx.2.trans ((div_le_iff₀ hh).mp hhi)

/-- The supplied outward-rounded interval can safely replace the exact one. -/
def Box.checkWiden (inner outer : Box) : Bool :=
  decide (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi)

theorem widen_sound {inner outer : Box} {x : ℝ} (hx : inner.Contains x)
    (accepted : inner.checkWiden outer = true) : outer.Contains x := by
  unfold Box.checkWiden at accepted
  obtain ⟨hl, hh⟩ := of_decide_eq_true accepted
  exact ⟨(Rat.cast_le.mpr hl).trans hx.1, hx.2.trans (Rat.cast_le.mpr hh)⟩

/-- Round a rational enclosure outward onto a grid with step 2⁻precision. -/
def Box.roundOut (a : Box) (precision : ℕ) : Box :=
  let scale : ℚ := 2 ^ precision
  ⟨(⌊a.lo * scale⌋ : ℚ) / scale, (⌈a.hi * scale⌉ : ℚ) / scale⟩

theorem roundOut_sound {a : Box} {x : ℝ} (hx : a.Contains x) (precision : ℕ) :
    (a.roundOut precision).Contains x := by
  let scale : ℚ := 2 ^ precision
  have hp : 0 < scale := by positivity
  have hl : (⌊a.lo * scale⌋ : ℚ) / scale ≤ a.lo :=
    (div_le_iff₀ hp).mpr (Int.floor_le _)
  have hh : a.hi ≤ (⌈a.hi * scale⌉ : ℚ) / scale :=
    (le_div_iff₀ hp).mpr (Int.le_ceil _)
  exact ⟨(Rat.cast_le.mpr hl).trans hx.1, hx.2.trans (Rat.cast_le.mpr hh)⟩

/-- BigInt division truncates. The correction is needed at a nonzero remainder
    whose sign differs from the divisor's. -/
def integerFloor (n d : ℤ) : ℤ :=
  if n.tmod d ≠ 0 ∧ (n.tmod d < 0 ↔ 0 ≤ d) then n.tdiv d - 1 else n.tdiv d

def integerCeil (n d : ℤ) : ℤ := -integerFloor (-n) d

private theorem integerFloor_eq_fdiv (n d : ℤ) (hd : d ≠ 0) :
    integerFloor n d = n.fdiv d := by
  rw [integerFloor, Int.fdiv_eq_tdiv]
  by_cases h : d ∣ n
  · simp [h, Int.tmod_eq_zero_of_dvd h]
  · have sign := Int.sign_tmod n d
    have hn : n ≠ 0 := fun hn => h (hn ▸ dvd_zero d)
    have hr : n.tmod d ≠ 0 := by
      intro hr
      simp [h, hr] at sign
      exact hn (Int.eq_zero_of_sign_eq_zero sign.symm)
    have neg : n.tmod d < 0 ↔ n < 0 := by
      simpa [Int.sign_eq_neg_one_iff_neg, h] using
        (show (n.tmod d).sign = -1 ↔ n.sign = -1 by simp [sign, h])
    rcases lt_or_gt_of_ne hd with hd | hd <;> rcases lt_or_gt_of_ne hn with hn | hn
    · simp [h, hr, neg, hn, not_le.mpr hn, not_le.mpr hd,
        Int.sign_eq_neg_one_of_neg hd]
    · simp [h, hr, neg, hn.le, not_le.mpr hd, not_lt.mpr hn.le]
    · simp [h, hr, neg, hn, hd.le, not_le.mpr hn, Int.sign_eq_one_of_pos hd]
    · simp [h, hr, neg, hn.le, hd.le, not_lt.mpr hn.le]

private theorem integerFloor_pos_divisor {n d : ℤ} (hd : 0 < d) :
    (integerFloor n d : ℝ) ≤ (n : ℝ) / d ∧
      (n : ℝ) / d < (integerFloor n d : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [integerFloor_eq_fdiv n d hd.ne', Int.fdiv_eq_ediv_of_nonneg n hd.le]
  exact ⟨(le_div_iff₀ hd').mpr (by exact_mod_cast Int.ediv_mul_le n hd.ne'),
    (div_lt_iff₀ hd').mpr (by exact_mod_cast Int.lt_ediv_add_one_mul_self n hd)⟩

private theorem integerFloor_bounds {n d : ℤ} (hd : d ≠ 0) :
    (integerFloor n d : ℝ) ≤ (n : ℝ) / d ∧
      (n : ℝ) / d < (integerFloor n d : ℝ) + 1 := by
  rcases lt_or_gt_of_ne hd with h | h
  · have same : integerFloor (-n) (-d) = integerFloor n d := by
      unfold integerFloor
      simp only [Int.tdiv_neg, Int.neg_tdiv, neg_neg, Int.tmod_neg, Int.neg_tmod]
      by_cases hz : n.tmod d = 0
      · simp [hz]
      · have hdneg : ¬0 ≤ d := not_le.mpr h
        have hdpos : 0 ≤ -d := by omega
        simp only [neg_ne_zero, hdneg, hdpos, iff_true,
          iff_false, neg_lt_zero]
        have hr : (0 < n.tmod d) ↔ ¬n.tmod d < 0 := by omega
        simp only [hr]
    simpa [same] using (integerFloor_pos_divisor (n := -n) (d := -d) (by omega))
  · exact integerFloor_pos_divisor h

theorem dyadic_floor_sound {n d : ℤ} (hd : d ≠ 0) (p : ℕ) :
    (integerFloor n d : ℝ) / 2 ^ p ≤ ((n : ℝ) / d) / 2 ^ p ∧
      ((n : ℝ) / d) / 2 ^ p < ((integerFloor n d : ℝ) + 1) / 2 ^ p := by
  obtain ⟨lo, hi⟩ := integerFloor_bounds (n := n) hd
  exact ⟨div_le_div_of_nonneg_right lo (by positivity), div_lt_div_of_pos_right hi (by positivity)⟩

theorem dyadic_ceil_sound {n d : ℤ} (hd : d ≠ 0) (p : ℕ) :
    ((integerCeil n d : ℝ) - 1) / 2 ^ p < ((n : ℝ) / d) / 2 ^ p ∧
      ((n : ℝ) / d) / 2 ^ p ≤ (integerCeil n d : ℝ) / 2 ^ p := by
  obtain ⟨lo, hi⟩ := integerFloor_bounds (n := -n) hd
  push_cast at lo hi ⊢
  simp only [neg_div] at lo hi
  simp only [integerCeil, Int.cast_neg]
  exact ⟨div_lt_div_of_pos_right (by linarith) (by positivity),
    div_le_div_of_nonneg_right (by linarith) (by positivity)⟩

/-- A square root on the integer grid, rounding the upper endpoint up only
    when the radicand is not a perfect square. -/
theorem dyadic_integerSqrt_sound (n p : ℕ) :
    let r := n.sqrt
    let hi := if r ^ 2 = n then r else r + 1
    r ^ 2 ≤ n ∧ n < (r + 1) ^ 2 ∧
      (r : ℝ) / 2 ^ p ≤ Real.sqrt ((n : ℝ) / (2 ^ p) ^ 2) ∧
      Real.sqrt ((n : ℝ) / (2 ^ p) ^ 2) ≤ (hi : ℝ) / 2 ^ p := by
  dsimp only
  have lo := Nat.sqrt_le' n
  have hi : n < (n.sqrt + 1) ^ 2 := Nat.sqrt_lt'.mp (Nat.lt_succ_self _)
  have upper : n ≤ (if n.sqrt ^ 2 = n then n.sqrt else n.sqrt + 1) ^ 2 := by
    split <;> rename_i h
    · exact h.ge
    · exact hi.le
  have scale : 0 ≤ (2 : ℝ) ^ p := by positivity
  rw [Real.sqrt_div (Nat.cast_nonneg n), Real.sqrt_sq scale]
  exact ⟨lo, hi, div_le_div_of_nonneg_right (Real.le_sqrt_of_sq_le (by exact_mod_cast lo)) scale,
    div_le_div_of_nonneg_right (Real.sqrt_le_iff.mpr
      ⟨Nat.cast_nonneg _, by exact_mod_cast upper⟩) scale⟩

end Electroacoustics.Interval
