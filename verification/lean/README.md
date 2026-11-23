# Electroacoustics proofs

Install [Elan](https://lean-lang.org/install/) to use the Lean version pinned in this directory. From this directory, fetch the selected Mathlib cache and check the proofs.

```sh
lake exe cache get Mathlib.Basic.Complex.Basic Mathlib.Analysis.Real.Sqrt \
  Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake build
```

The first run downloads dependencies and creates a `.lake/` directory. To keep build output on Scratch, copy this directory to a Scratch build location and run the commands there. Set `MATHLIB_CACHE_DIR` to a Scratch path for the downloaded cache archives. This check runs on demand.

## Verified properties

| Model | What Lean checks |
| --- | --- |
| [Operating limits](Electroacoustics/Operating.lean) | Each active sampled constraint is equivalent to an upper bound on nonnegative amplifier voltage. The minimum of a nonempty list of these bounds is positive, comes from a sampled constraint, and is the greatest feasible voltage. The model uses the same linear and per-driver I²R formulas as [the operating solver](../../src/operating.ts). |
| [Circuit](Electroacoustics/Circuit.lean) | The electrical, mechanical, and cavity balances imply power conservation and passivity. The cleared formulas solve the balance equations and the denominator stays nonzero for passive inputs with positive electrical and mechanical resistances and nonzero cone area. Power and impedance obey the series/parallel wiring laws used by [the circuit solver](../../src/circuit.ts). |
| [Duct tuning](Electroacoustics/Duct.lean) | Away from degenerate cases, the residual used in [the tuning search](../../src/ductAcoustics.ts) vanishes exactly at reactive cancellation. A pole with nonzero numerator is excluded. Given a sign-changing bracket, bisection preserves its signs and halves its width at each step. |
| [Design calculations](Electroacoustics/Design.lean) | The sealed, duct-volume, and passive-radiator inverses solve their defining equations. The amplifier current limit translates through DSP gain, and the centered biquad quotient preserves the transfer function. Known added mass and test-box volume give independent driver measurement equations. |

The [axiom audit](Electroacoustics/Audit.lean) runs during `lake build` and rejects any theorem dependency outside Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

The proofs apply to exact real and complex arithmetic under the stated assumptions. The duct proof starts with a bracket and leaves finding the first bracket to the numerical search. The [Vitest invariants](../../src/invariants.test.ts) and regression tests exercise the TypeScript functions, including rounding and supported numerical ranges. Physical accuracy still depends on the model assumptions and measured inputs.
