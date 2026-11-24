module

import all Electroacoustics.Accuracy
import all Electroacoustics.BandCertificate
import all Electroacoustics.BandHeadroom
import all Electroacoustics.Circuit
import all Electroacoustics.Design
import all Electroacoustics.Duct
import all Electroacoustics.DuctCertificate
import all Electroacoustics.DuctInterval
import all Electroacoustics.DuctTransfer
import all Electroacoustics.Filters
import all Electroacoustics.ImpedanceCertificate
import all Electroacoustics.Interval
import all Electroacoustics.Numerics
import all Electroacoustics.Operating
import all Electroacoustics.Radiator
import all Electroacoustics.Summaries
import all Electroacoustics.Transcendentals
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  -- The full imports preserve theorem declarations with their proofs.
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let declarations := env.constants.fold (fun names name info =>
    if (env.getModuleIdxFor? name).any (fun idx => (`Electroacoustics).isPrefixOf modules[idx.toNat]!) then
      names.push (name, info)
    else names) #[]
  let mut count : Nat := 0
  for (name, info) in declarations do
    if info.isTheorem && !isPrivateName name && !name.isInternal then
      let axioms ← Lean.collectAxioms name
      let unexpected := axioms.filter fun dependency =>
        !(#[``propext, ``Classical.choice, ``Quot.sound].contains dependency)
      unless unexpected.isEmpty do
        throwError m!"{name} depends on unexpected axioms: {unexpected}"
      count := count + 1
    else if info.isAxiom then
      -- Some opaque definitions are exported abstractly by Lean. An actual
      -- axiom is included in its own transitive dependencies.
      if (← Lean.collectAxioms name).contains name then
        throwError m!"Unexpected electroacoustics axiom: {name}"
  logInfo m!"Audited axioms for {count} electroacoustics theorems."
