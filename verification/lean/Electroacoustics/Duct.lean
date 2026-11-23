module

public import Mathlib.Basic.Real.Basic
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

end Electroacoustics.Duct
