module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Operating

/-- An active sampled constraint from `analyzeFilteredVoltageLimit`. A linear
    constraint represents excursion or port Mach. Thermal power uses per-driver I²R. -/
inductive Limit where
  | linear (rating response reference gain : ℝ)
  | thermal (rating resistance impedance parallel gain : ℝ)

def Limit.Valid : Limit → Prop
  | .linear rating response reference gain =>
      0 < rating ∧ 0 < response ∧ 0 < reference ∧ 0 < gain
  | .thermal rating resistance impedance parallel gain =>
      0 < rating ∧ 0 < resistance ∧ 0 < impedance ∧ 0 < parallel ∧ 0 < gain

def Limit.bound : Limit → ℝ
  | .linear rating response reference gain => reference * rating / response / gain
  | .thermal rating resistance impedance parallel gain =>
      Real.sqrt rating / Real.sqrt resistance * impedance / gain * parallel

def Limit.Allows (voltage : ℝ) : Limit → Prop
  | .linear rating response reference gain =>
      response * (voltage * gain / reference) ≤ rating
  | .thermal rating resistance impedance parallel gain =>
      (voltage * gain / impedance / parallel) ^ 2 * resistance ≤ rating

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

end Electroacoustics.Operating
