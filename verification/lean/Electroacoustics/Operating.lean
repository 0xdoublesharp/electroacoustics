module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Operating

/-- An active sampled constraint in an operating-limit analysis. Linear constraints
    cover cone excursion, radiator excursion, and port Mach. Thermal power uses per-driver I²R. -/
inductive Limit where
  | linear (rating response reference gain : ℝ)
  | thermal (rating resistance impedance parallel gain : ℝ)
  | terminalVoltage (rating gain : ℝ)
  | terminalCurrent (rating impedance gain : ℝ)

def Limit.Valid : Limit → Prop
  | .linear rating response reference gain =>
      0 < rating ∧ 0 < response ∧ 0 < reference ∧ 0 < gain
  | .thermal rating resistance impedance parallel gain =>
      0 < rating ∧ 0 < resistance ∧ 0 < impedance ∧ 0 < parallel ∧ 0 < gain
  | .terminalVoltage rating gain => 0 < rating ∧ 0 < gain
  | .terminalCurrent rating impedance gain => 0 < rating ∧ 0 < impedance ∧ 0 < gain

def Limit.bound : Limit → ℝ
  | .linear rating response reference gain => reference * rating / response / gain
  | .thermal rating resistance impedance parallel gain =>
      Real.sqrt rating / Real.sqrt resistance * impedance / gain * parallel
  | .terminalVoltage rating gain => rating / gain
  | .terminalCurrent rating impedance gain => rating * impedance / gain

def Limit.Allows (voltage : ℝ) : Limit → Prop
  | .linear rating response reference gain =>
      response * (voltage * gain / reference) ≤ rating
  | .thermal rating resistance impedance parallel gain =>
      (voltage * gain / impedance / parallel) ^ 2 * resistance ≤ rating
  | .terminalVoltage rating gain => voltage * gain ≤ rating
  | .terminalCurrent rating impedance gain => voltage * gain / impedance ≤ rating

theorem Limit.bound_pos {limit : Limit} (valid : limit.Valid) : 0 < limit.bound := by
  cases limit with
  | linear =>
      obtain ⟨_, _, _, _⟩ := valid
      unfold bound
      positivity
  | thermal =>
      obtain ⟨_, _, _, _, _⟩ := valid
      unfold bound
      positivity
  | terminalVoltage =>
      obtain ⟨_, _⟩ := valid
      unfold bound
      positivity
  | terminalCurrent =>
      obtain ⟨_, _, _⟩ := valid
      unfold bound
      positivity

theorem Limit.allows_iff_le_bound {limit : Limit} (valid : limit.Valid)
    {voltage : ℝ} (nonnegative : 0 ≤ voltage) :
    limit.Allows voltage ↔ voltage ≤ limit.bound := by
  cases limit with
  | linear rating response reference gain =>
      obtain ⟨_, hr, hv, hg⟩ := valid
      simp only [Allows, bound]
      rw [← mul_div_assoc, div_le_iff₀ hv, le_div_iff₀ hg, le_div_iff₀ hr]
      ring_nf
  | thermal rating resistance impedance parallel gain =>
      obtain ⟨hp, hr, hz, hn, hg⟩ := valid
      simp only [Allows, bound]
      rw [← le_div_iff₀ hr, ← Real.sq_sqrt (div_nonneg hp.le hr.le)]
      rw [sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _), Real.sqrt_div hp.le]
      rw [div_le_iff₀ hn, div_le_iff₀ hz, ← le_div_iff₀ hg]
      ring_nf
  | terminalVoltage rating gain =>
      exact (le_div_iff₀ valid.2).symm
  | terminalCurrent rating impedance gain =>
      simp only [Allows, bound]
      rw [div_le_iff₀ valid.2.1, le_div_iff₀ valid.2.2]

private theorem le_foldl_min_iff (voltage first : ℝ) (rest : List ℝ) :
    voltage ≤ rest.foldl min first ↔ voltage ≤ first ∧ ∀ bound ∈ rest, voltage ≤ bound := by
  induction rest generalizing first with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih, le_min_iff]
      constructor
      · rintro ⟨⟨hf, hh⟩, ht⟩
        exact ⟨hf, fun bound member => (List.mem_cons.mp member).elim
          (fun equal => equal ▸ hh) (ht bound)⟩
      · rintro ⟨hf, hall⟩
        exact ⟨⟨hf, hall head List.mem_cons_self⟩,
          fun bound member => hall bound (List.mem_cons_of_mem _ member)⟩

private theorem foldl_min_mem (first : ℝ) (rest : List ℝ) :
    rest.foldl min first ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp (ih (min first head)) with equal | member
      · by_cases h : first ≤ head
        · exact List.mem_cons.mpr (Or.inl (equal.trans (min_eq_left h)))
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
            (Or.inl (equal.trans (min_eq_right (le_of_not_ge h))))))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)

/-- The minimum across the finite, nonempty list of active sampled bounds. -/
def maximumVoltage (first : Limit) (rest : List Limit) : ℝ :=
  (rest.map Limit.bound).foldl min first.bound

theorem maximum_voltage_is_candidate (first : Limit) (rest : List Limit) :
    ∃ limiting ∈ first :: rest, maximumVoltage first rest = limiting.bound := by
  have member := foldl_min_mem first.bound (rest.map Limit.bound)
  change maximumVoltage first rest ∈ (first :: rest).map Limit.bound at member
  obtain ⟨limiting, h, equal⟩ := List.mem_map.mp member
  exact ⟨limiting, h, equal.symm⟩

/-- The minimum voltage bound is feasible and every larger voltage violates at
    least one sampled constraint. Zero-response and zero-gain samples impose no bound. -/
theorem feasible_iff_le_maximum_voltage (first : Limit) (rest : List Limit)
    (valid : ∀ limit ∈ first :: rest, limit.Valid) {voltage : ℝ}
    (nonnegative : 0 ≤ voltage) :
    (∀ limit ∈ first :: rest, limit.Allows voltage) ↔ voltage ≤ maximumVoltage first rest := by
  rw [maximumVoltage, le_foldl_min_iff]
  constructor
  · intro allows
    refine ⟨(Limit.allows_iff_le_bound (valid _ List.mem_cons_self) nonnegative).mp
      (allows _ List.mem_cons_self), ?_⟩
    intro bound member
    obtain ⟨limit, inRest, rfl⟩ := List.mem_map.mp member
    have inAll := List.mem_cons_of_mem first inRest
    exact (Limit.allows_iff_le_bound (valid _ inAll) nonnegative).mp (allows _ inAll)
  · rintro ⟨head, tail⟩ limit member
    apply (Limit.allows_iff_le_bound (valid _ member) nonnegative).mpr
    rcases List.mem_cons.mp member with rfl | inRest
    · exact head
    · exact tail _ (List.mem_map_of_mem inRest)

theorem maximum_voltage_is_feasible (first : Limit) (rest : List Limit)
    (valid : ∀ limit ∈ first :: rest, limit.Valid) :
    0 < maximumVoltage first rest ∧
      ∀ limit ∈ first :: rest, limit.Allows (maximumVoltage first rest) := by
  obtain ⟨limiting, member, equal⟩ := maximum_voltage_is_candidate first rest
  have positive : 0 < maximumVoltage first rest := by
    rw [equal]
    exact Limit.bound_pos (valid limiting member)
  exact ⟨positive,
    (feasible_iff_le_maximum_voltage first rest valid positive.le).mpr le_rfl⟩

/-- Every larger drive exceeds an actual sampled constraint. -/
theorem above_maximum_has_violated_constraint (first : Limit) (rest : List Limit)
    (valid : ∀ limit ∈ first :: rest, limit.Valid) {voltage : ℝ}
    (above : maximumVoltage first rest < voltage) :
    ∃ limiting ∈ first :: rest, ¬limiting.Allows voltage := by
  obtain ⟨limiting, member, equal⟩ := maximum_voltage_is_candidate first rest
  have positive := Limit.bound_pos (valid limiting member)
  rw [equal] at above
  refine ⟨limiting, member, ?_⟩
  rw [Limit.allows_iff_le_bound (valid limiting member) (positive.trans above).le]
  exact not_le.mpr above

/-- The logarithmic fallback evaluates the same linear voltage bound. -/
theorem linear_limit_log_equiv {reference rating response gain : ℝ}
    (href : 0 < reference) (hrating : 0 < rating) (hresponse : 0 < response)
    (hgain : 0 < gain) :
    Real.exp (Real.log reference + Real.log rating - Real.log response - Real.log gain) =
      reference * rating / response / gain := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log href, Real.exp_log hrating,
    Real.exp_log hresponse, Real.exp_log hgain]

/-- The logarithmic fallback evaluates the same per-driver thermal voltage bound. -/
theorem thermal_limit_log_equiv {rating resistance impedance parallel gain : ℝ}
    (hrating : 0 < rating) (hresistance : 0 < resistance) (himpedance : 0 < impedance)
    (hparallel : 0 < parallel) (hgain : 0 < gain) :
    Real.exp ((Real.log rating - Real.log resistance) / 2 + Real.log impedance +
      Real.log parallel - Real.log gain) =
      Real.sqrt rating / Real.sqrt resistance * impedance / gain * parallel := by
  rw [show (Real.log rating - Real.log resistance) / 2 =
      Real.log (Real.sqrt rating) - Real.log (Real.sqrt resistance) by
    rw [Real.log_sqrt hrating.le, Real.log_sqrt hresistance.le]
    ring]
  rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_sub,
    Real.exp_log (Real.sqrt_pos.2 hrating), Real.exp_log (Real.sqrt_pos.2 hresistance),
    Real.exp_log himpedance, Real.exp_log hparallel, Real.exp_log hgain]
  ring

theorem headroom_nonneg_iff_feasible {limit drive : ℝ} (hlimit : 0 < limit) (hdrive : 0 < drive) :
    0 ≤ 20 / Real.log 10 * Real.log (limit / drive) ↔ drive ≤ limit := by
  rw [mul_nonneg_iff_of_pos_left (show 0 < 20 / Real.log 10 by positivity),
    Real.log_nonneg_iff (div_pos hlimit hdrive), le_div_iff₀ hdrive, one_mul]

theorem planned_plus_headroom_eq_max_spl {ref terminal gain drive inputLimit : ℝ} (spl : ℝ)
    (hterminal : 0 < terminal) (hgain : 0 < gain) (inputLimit_eq : inputLimit = terminal / gain) :
    (spl + 20 / Real.log 10 * (Real.log drive + Real.log gain - Real.log ref)) +
      20 / Real.log 10 * (Real.log inputLimit - Real.log drive) =
        spl + 20 / Real.log 10 * (Real.log terminal - Real.log ref) := by
  rw [inputLimit_eq, Real.log_div hterminal.ne' hgain.ne']
  ring

end Electroacoustics.Operating
