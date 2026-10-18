import FinitePrecisionLanczos
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter
    (fun n => (`FinitePrecisionLanczos).isPrefixOf n)
  let names := names.toArray.qsort Name.lt
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut theoremCount : Nat := 0
  for n in names do
    let axs ← collectAxioms n
    if let some (.thmInfo _) := env.find? n then
      theoremCount := theoremCount + 1
    logInfo m!"AUDIT {n}: {axs}"
    for ax in axs do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  logInfo m!"PASS: {names.size} namespace declarations, {theoremCount} theorem declarations. Only propext, Classical.choice, Quot.sound permitted."

#check FinitePrecisionLanczos.LanczosRun.ritz_residual_bound_div
#check FinitePrecisionLanczos.LanczosRun.coefficients_paper
#check FinitePrecisionLanczos.LanczosRun.greenbaum_backward_model
#check FinitePrecisionLanczos.LanczosRun.greenbaum_localization_exists
#check FinitePrecisionLanczos.LanczosRun.starting_lipschitz
