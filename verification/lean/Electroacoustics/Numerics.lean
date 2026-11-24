module

public import Electroacoustics.Circuit
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Electroacoustics.Numerics

open scoped BigOperators

/-- The quadratic form of the fitter's damped normal matrix is strictly
    positive whenever some coordinate is nonzero, even for rank-deficient J. -/
theorem damped_normal_energy_pos {rows cols : Type} [Fintype rows] [Fintype cols]
    (jacobian : rows → cols → ℝ) (v : cols → ℝ) {damping floor : ℝ}
    (hd : 0 < damping) (hf : 0 < floor) (nonzero : ∃ i, v i ≠ 0) :
    0 < (∑ r, (∑ i, jacobian r i * v i) ^ 2) +
      damping * (∑ i, ((∑ r, jacobian r i ^ 2) + floor) * v i ^ 2) := by
  classical
  have positiveWeight (i : cols) : 0 < (∑ r, jacobian r i ^ 2) + floor :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => sq_nonneg _) hf
  obtain ⟨i, hi⟩ := nonzero
  apply add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply mul_pos hd
  apply Finset.sum_pos' (fun j _ => mul_nonneg (positiveWeight j).le (sq_nonneg _))
  exact ⟨i, Finset.mem_univ i, mul_pos (positiveWeight i) (sq_pos_of_ne_zero hi)⟩

/-- The fitter clamps normalized coordinates to [0,1] before unscaling. -/
theorem projected_fit_step_in_bounds {lo hi : ℝ} (ordered : lo ≤ hi) (candidate : ℝ) :
    lo ≤ lo + max 0 (min 1 candidate) * (hi - lo) ∧
      lo + max 0 (min 1 candidate) * (hi - lo) ≤ hi := by
  have nonnegative := le_max_left 0 (min 1 candidate)
  have atMostOne : max 0 (min 1 candidate) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have width := sub_nonneg.mpr ordered
  exact ⟨le_add_of_nonneg_right (mul_nonneg nonnegative width), by
    linarith [mul_le_mul_of_nonneg_right atMostOne width]⟩

/-- The exact first-order check used by a box-constrained fit. The caller
    supplies the derivative or a verified bound on its approximation error. -/
theorem projected_gradient_bounds_direction {point next gradient tolerance : ℝ}
    (feasible : 0 ≤ next ∧ next ≤ 1)
    (checked : (if point = 0 then max 0 (-gradient)
      else if point = 1 then max 0 gradient else |gradient|) ≤ tolerance) :
    -(tolerance * |next - point|) ≤ gradient * (next - point) := by
  by_cases atMin : point = 0
  · subst point
    simp only [sub_zero, abs_of_nonneg feasible.1] at *
    have lower : -tolerance ≤ gradient := neg_le.mp ((le_max_right 0 (-gradient)).trans checked)
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right lower feasible.1
  by_cases atMax : point = 1
  · subst point
    simp only [one_ne_zero, ite_false, ite_true] at checked
    rw [abs_of_nonpos (sub_nonpos.mpr feasible.2)]
    have upper := (le_max_right 0 gradient).trans checked
    calc
      _ = tolerance * (next - 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonpos_right upper (sub_nonpos.mpr feasible.2)
  · simp only [atMin, atMax, ite_false] at checked
    have bound := mul_le_mul_of_nonneg_right checked (abs_nonneg (next - point))
    rw [← abs_mul] at bound
    exact (neg_le_neg bound).trans (neg_abs_le _)

/-- Electrical impedance sees the sum of the two shunt conductances, so a
    sweep cannot identify leakage and absorption independently. -/
theorem loss_split_same_electrical_response {electrical mechanical other : ℂ}
    {count area coupling leak absorption leak' absorption' : ℝ}
    (same : leak + absorption = leak' + absorption') :
    let before := other + ((leak + absorption : ℝ) : ℂ)
    let after := other + ((leak' + absorption' : ℝ) : ℂ)
    Circuit.mechanicalNumerator mechanical before count area /
        Circuit.denominator electrical mechanical before count area coupling =
      Circuit.mechanicalNumerator mechanical after count area /
        Circuit.denominator electrical mechanical after count area coupling := by
  dsimp
  rw [same]

/-- A reported response crossing is inside its bracketing frequency interval
    and reaches the threshold in the linear interpolant used by the summary. -/
theorem cutoff_interpolation {leftHz rightHz leftDb rightDb threshold : ℝ}
    (ordered : leftHz < rightHz) (below : leftDb < threshold) (reaches : threshold ≤ rightDb) :
    let fraction := (threshold - leftDb) / (rightDb - leftDb)
    let cutoff := leftHz + fraction * (rightHz - leftHz)
    leftHz < cutoff ∧ cutoff ≤ rightHz ∧ leftDb + fraction * (rightDb - leftDb) = threshold := by
  dsimp
  have width : 0 < rightDb - leftDb := sub_pos.mpr (below.trans_le reaches)
  have fractionPos := div_pos (sub_pos.mpr below) width
  have fractionLe : (threshold - leftDb) / (rightDb - leftDb) ≤ 1 := by
    rw [div_le_iff₀ width, one_mul]
    linarith
  have frequencyWidth := sub_pos.mpr ordered
  refine ⟨by linarith [mul_pos fractionPos frequencyWidth],
    by linarith [mul_le_mul_of_nonneg_right fractionLe frequencyWidth.le], ?_⟩
  rw [div_mul_cancel₀ _ width.ne']
  ring

private theorem residual_square_bounds {lo r hi : ℝ} (hl : lo ≤ r) (hh : r ≤ hi) :
    (max 0 (max lo (-hi))) ^ 2 ≤ r ^ 2 ∧ r ^ 2 ≤ (max (-lo) hi) ^ 2 := by
  have lower : max 0 (max lo (-hi)) ≤ |r| :=
    max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _))
      ((neg_le_neg hh).trans (neg_le_abs _)))
  have upper : |r| ≤ max (-lo) hi := by
    rw [abs_le]
    constructor
    · have h := neg_le_neg (le_max_left (-lo) hi)
      rw [neg_neg] at h
      exact h.trans hl
    · exact hh.trans (le_max_right _ _)
  rw [← sq_abs r]
  exact ⟨(sq_le_sq₀ (le_max_left _ _) (abs_nonneg _)).mpr lower,
    (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans upper)).mpr upper⟩

theorem interval_rms_upper_sound {n : ℕ} {r lo hi : Fin n → ℝ} {tol : ℝ}
    (hn : 0 < n) (ht : 0 ≤ tol) (bounds : ∀ k, lo k ≤ r k ∧ r k ≤ hi k)
    (checked : (∑ k, (max (-lo k) (hi k)) ^ 2) ≤ (n : ℝ) * tol ^ 2) :
    Real.sqrt ((∑ k, r k ^ 2) / (n : ℝ)) ≤ tol :=
  Real.sqrt_le_iff.mpr ⟨ht, (div_le_iff₀ (by exact_mod_cast hn)).mpr
    (mul_comm (n : ℝ) (tol ^ 2) ▸
      (Finset.sum_le_sum (fun k _ => (residual_square_bounds (bounds k).1 (bounds k).2).2)).trans
        checked)⟩

theorem interval_rms_lower_sound {n : ℕ} {r lo hi : Fin n → ℝ} {lower : ℝ}
    (hn : 0 < n) (hl : 0 ≤ lower) (bounds : ∀ k, lo k ≤ r k ∧ r k ≤ hi k)
    (checked : (n : ℝ) * lower ^ 2 ≤ ∑ k, (max 0 (max (lo k) (-hi k))) ^ 2) :
    lower ≤ Real.sqrt ((∑ k, r k ^ 2) / (n : ℝ)) := by
  apply (Real.le_sqrt hl (by positivity)).mpr
  apply (le_div_iff₀ (by exact_mod_cast hn)).mpr
  rw [mul_comm]
  exact checked.trans (Finset.sum_le_sum fun k _ =>
    (residual_square_bounds (bounds k).1 (bounds k).2).1)

/-- One component of the exact projected gradient at a normalized point. -/
def projectedGradient (point gradient : ℝ) : ℝ :=
  if point = 0 then max 0 (-gradient)
  else if point = 1 then max 0 gradient else |gradient|

theorem projectedGradient_nonneg (point gradient : ℝ) :
    0 ≤ projectedGradient point gradient := by
  unfold projectedGradient
  split <;> try split
  all_goals first | exact le_max_left _ _ | exact abs_nonneg _

theorem interval_projected_gradient_sound {point next gradient lo hi tol : ℝ}
    (bounds : lo ≤ gradient ∧ gradient ≤ hi) (feasible : 0 ≤ next ∧ next ≤ 1)
    (checked : (if point = 0 then max 0 (-lo)
      else if point = 1 then max 0 hi else max (-lo) hi) ≤ tol) :
    -(tol * |next - point|) ≤ gradient * (next - point) := by
  apply projected_gradient_bounds_direction feasible
  apply le_trans _ checked
  split <;> try split
  · exact max_le_max le_rfl (neg_le_neg bounds.1)
  · exact max_le_max le_rfl bounds.2
  · rw [abs_le]
    have hl := neg_le_neg (le_max_left (-lo) hi)
    rw [neg_neg] at hl
    exact ⟨hl.trans bounds.1, bounds.2.trans (le_max_right _ _)⟩

theorem projected_gradient_direction_sum {p : ℕ} {point next gradient : Fin p → ℝ}
    {tol : ℝ} (feasible : ∀ i, 0 ≤ next i ∧ next i ≤ 1)
    (checked : ∀ i, projectedGradient (point i) (gradient i) ≤ tol) :
    -(tol * ∑ i, |next i - point i|) ≤ ∑ i, gradient i * (next i - point i) := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun i _ => projected_gradient_bounds_direction (feasible i) (checked i)

theorem interval_kkt_direction_bound {p : ℕ} {point next gradient lo hi : Fin p → ℝ}
    {tol : ℝ} (bounds : ∀ i, lo i ≤ gradient i ∧ gradient i ≤ hi i)
    (feasible : ∀ i, 0 ≤ next i ∧ next i ≤ 1)
    (checked : ∀ i, (if point i = 0 then max 0 (-lo i)
      else if point i = 1 then max 0 (hi i) else max (-lo i) (hi i)) ≤ tol) :
    -(tol * ∑ i, |next i - point i|) ≤ ∑ i, gradient i * (next i - point i) := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun i _ =>
    interval_projected_gradient_sound (bounds i) (feasible i) (checked i)

/-- Each symmetric pair contributes at least its negative absolute weight
    times the mean of the two squared coordinates. -/
theorem strict_diag_dom_pos_def {p : ℕ} (M : Fin p → Fin p → ℝ)
    (symm : ∀ i j, M i j = M j i)
    (dominant : ∀ i, (∑ j ∈ Finset.univ.erase i, |M i j|) < M i i)
    (v : Fin p → ℝ) (nonzero : ∃ i, v i ≠ 0) :
    0 < ∑ i, ∑ j, v i * M i j * v j := by
  let W (i j : Fin p) := if i = j then 0 else |M i j|
  have hW : ∀ i j, W i j = W j i := fun i j => by simp [W, eq_comm, symm i j]
  have weight (i : Fin p) : (∑ j, W i j) = ∑ j ∈ Finset.univ.erase i, |M i j| := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp [W, Finset.sum_congr rfl (fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj).symm)]
  have pair (i j : Fin p) :
      (if i = j then 0 else -(W i j * (v i ^ 2 + v j ^ 2))) ≤
        (if i = j then 0 else 2 * (v i * M i j * v j)) := by
    by_cases e : i = j
    · simp [e]
    · simp only [e, ite_false, W]
      rcases le_total 0 (M i j) with h | h
      · rw [abs_of_nonneg h]
        nlinarith [mul_nonneg h (sq_nonneg (v i + v j))]
      · rw [abs_of_nonpos h]
        nlinarith [mul_nonneg (neg_nonneg.mpr h) (sq_nonneg (v i - v j))]
  have splitRow (i : Fin p) :
      (∑ j, v i * M i j * v j) =
        M i i * v i ^ 2 + ∑ j, (if i = j then 0 else v i * M i j * v j) := by
    rw [← Finset.sum_erase_add _ (fun j => v i * M i j * v j) (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add _ (fun j => if i = j then 0 else v i * M i j * v j)
      (Finset.mem_univ i)]
    simp only [ite_true, add_zero]
    have h : (∑ j ∈ Finset.univ.erase i, if i = j then 0 else v i * M i j * v j) =
        ∑ j ∈ Finset.univ.erase i, v i * M i j * v j :=
      Finset.sum_congr rfl fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj).symm
    rw [h]
    ring
  have lower :
      -(2 * ∑ i, (∑ j, W i j) * v i ^ 2) ≤
        2 * ∑ i, ∑ j, (if i = j then 0 else v i * M i j * v j) := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) fun j _ => pair i j
    have hl (i j : Fin p) : (if i = j then 0 else -(W i j * (v i ^ 2 + v j ^ 2))) =
        -(W i j * v i ^ 2 + W i j * v j ^ 2) := by
      by_cases e : i = j <;> simp [e, W, mul_add]
    have hr (i j : Fin p) : (if i = j then 0 else 2 * (v i * M i j * v j)) =
        2 * (if i = j then 0 else v i * M i j * v j) := by split <;> simp
    simp_rw [hl, hr, Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul] at h
    have swap : (∑ i, ∑ j, W i j * v j ^ 2) = ∑ i, (∑ j, W i j) * v i ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact Finset.sum_congr rfl fun j _ => hW j i
    rw [swap, ← two_mul] at h
    exact h
  have pos : 0 < ∑ i, (M i i - ∑ j, W i j) * v i ^ 2 := by
    have h i : 0 < M i i - ∑ j, W i j := sub_pos.mpr (weight i ▸ dominant i)
    apply Finset.sum_pos' (fun i _ => mul_nonneg (h i).le (sq_nonneg _))
    obtain ⟨i, hi⟩ := nonzero
    exact ⟨i, Finset.mem_univ i, mul_pos (h i) (sq_pos_of_ne_zero hi)⟩
  simp_rw [splitRow, Finset.sum_add_distrib]
  simp_rw [sub_mul, Finset.sum_sub_distrib] at pos
  linarith

open Matrix

theorem lower_tri_pos_diag_injective {p : ℕ} (C : Matrix (Fin p) (Fin p) ℝ)
    (diag : ∀ i, 0 < C i i) (tri : ∀ i j, i < j → C i j = 0) :
    Function.Injective C.mulVec := by
  change Function.Injective C.mulVecLin
  apply (LinearMap.ker_eq_bot).mp
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro v hv
  funext i
  change v i = 0
  induction i using (measure (Fin.val : Fin p → ℕ)).wf.induction with
  | h i ih =>
    have h (j) (hj : j ∈ Finset.univ.erase i) : C i j * v j = 0 := by
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
      · rw [ih j h, mul_zero]
      · rw [tri i j h, zero_mul]
    have row := congrFun hv i
    change (∑ j, C i j * v j) = 0 at row
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), Finset.sum_eq_zero h, zero_add] at row
    exact (mul_eq_zero.mp row).resolve_left (diag i).ne'

theorem preconditioned_gram_full_rank {n p : ℕ}
    (J : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin p) ℝ) (floor : ℝ)
    (diag : ∀ i, 0 < C i i) (tri : ∀ i j, i < j → C i j = 0)
    (dominant : let M := Cᵀ * (Jᵀ * J - floor • (1 : Matrix (Fin p) (Fin p) ℝ)) * C
      ∀ i, (∑ j ∈ Finset.univ.erase i, |M i j|) < M i i)
    (v : Fin p → ℝ) (nonzero : ∃ i, v i ≠ 0) :
    floor * (∑ i, (v i) ^ 2) < ∑ k, (∑ i, J k i * v i) ^ 2 := by
  let G := Jᵀ * J - floor • (1 : Matrix (Fin p) (Fin p) ℝ)
  let M := Cᵀ * G * C
  have gsym : Gᵀ = G := by simp [G, transpose_mul, transpose_sub]
  have msym : Mᵀ = M := by simp [M, transpose_mul, gsym, Matrix.mul_assoc]
  have onto : Function.Surjective C.mulVec := by
    change Function.Surjective C.mulVecLin
    exact (LinearMap.injective_iff_surjective (f := C.mulVecLin)).mp
      (lower_tri_pos_diag_injective C diag tri)
  obtain ⟨w, hw⟩ := onto v
  have wn : ∃ i, w i ≠ 0 := by
    by_contra! h
    have e : w = 0 := funext h
    rw [e, mulVec_zero] at hw
    obtain ⟨i, hi⟩ := nonzero
    exact hi (congrFun hw.symm i)
  have positive := strict_diag_dom_pos_def M (fun i j => congr_fun₂ msym j i) dominant w wn
  have convert : (∑ i, ∑ j, w i * M i j * w j) = w ⬝ᵥ (M *ᵥ w) := by
    change (∑ i, ∑ j, w i * M i j * w j) = ∑ i, w i * ∑ j, M i j * w j
    simp_rw [Finset.mul_sum, mul_assoc]
  rw [convert] at positive
  have energy : w ⬝ᵥ (M *ᵥ w) = (J *ᵥ v) ⬝ᵥ (J *ᵥ v) - floor * (v ⬝ᵥ v) := by
    rw [show M = Cᵀ * (G * C) by exact Matrix.mul_assoc _ _ _, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose, hw, ← mulVec_mulVec, hw]
    dsimp only [G]
    rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      ← mulVec_mulVec, dotProduct_transpose_mulVec]
    rfl
  rw [energy, sub_pos] at positive
  simpa only [dotProduct, mulVec, pow_two] using positive

theorem gram_floor_full_rank {n p : ℕ} {J : Matrix (Fin n) (Fin p) ℝ} {floor : ℝ}
    (hf : 0 ≤ floor)
    (energy : ∀ v : Fin p → ℝ, (∃ i, v i ≠ 0) →
      floor * (∑ i, (v i) ^ 2) < ∑ k, (∑ i, J k i * v i) ^ 2)
    (v : Fin p → ℝ) (hv : J.mulVec v = 0) : v = 0 := by
  funext i
  by_contra h
  have he := energy v ⟨i, h⟩
  change floor * (∑ i, v i ^ 2) < ∑ k, (J.mulVec v k) ^ 2 at he
  simp [hv] at he
  exact (not_lt_of_ge (by positivity : 0 ≤ floor * ∑ i, v i ^ 2)) he

theorem weak_direction_rayleigh_bound {n p : ℕ} (J : Fin n → Fin p → ℝ)
    (v : Fin p → ℝ) {floor : ℝ} (nonzero : ∃ i, v i ≠ 0)
    (checked : (∑ k, (∑ i, J k i * v i) ^ 2) ≤ floor * ∑ i, (v i) ^ 2) :
    ∃ w : Fin p → ℝ, (∃ i, w i ≠ 0) ∧
      (∑ k, (∑ i, J k i * w i) ^ 2) / (∑ i, (w i) ^ 2) ≤ floor := by
  have hn : 0 < ∑ i, v i ^ 2 := by
    obtain ⟨i, hi⟩ := nonzero
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  exact ⟨v, nonzero, (div_le_iff₀ hn).mpr checked⟩

end Electroacoustics.Numerics
