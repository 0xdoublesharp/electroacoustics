module

import Electroacoustics.Circuit
import Electroacoustics.Design
import Electroacoustics.Duct
import Electroacoustics.Operating
import Lean.Elab.Command
import Lean.Util.CollectAxioms

namespace Electroacoustics

open Lean in
run_cmd do
  let theorems := #[
    ``Circuit.power_balance,
    ``Circuit.input_power_ge_copper_loss,
    ``Circuit.passive_denominator_ne_zero,
    ``Circuit.cleared_solution,
    ``Circuit.cleared_solution_satisfies,
    ``Circuit.denominator_at_lossless_tuning,
    ``Circuit.rewired_power,
    ``Circuit.rewired_impedance,
    ``Design.sealed_volume_round_trip,
    ``Design.duct_volume_round_trip,
    ``Design.radiator_mass_round_trip,
    ``Design.terminal_ceiling_from_input,
    ``Design.biquad_centered_quotient,
    ``Design.moving_mass_from_added_mass,
    ``Design.vas_from_closed_box,
    ``Duct.tuning_residual_zero_iff,
    ``Duct.pole_is_not_a_tuning,
    ``Duct.bisect_preserves_bracket,
    ``Duct.bisect_steps_preserve_bracket,
    ``Operating.Limit.bound_pos,
    ``Operating.Limit.allows_iff_le_bound,
    ``Operating.maximum_voltage_is_candidate,
    ``Operating.feasible_iff_le_maximum_voltage,
    ``Operating.maximum_voltage_is_feasible
  ]
  for name in theorems do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun dependency =>
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains dependency)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms: {unexpected}"
  logInfo m!"Audited axioms for {theorems.size} electroacoustics theorems."

end Electroacoustics
