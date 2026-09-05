module

public import Definitions.Def_ModularCurve_X0
import P2M.Sol.S_ModularCurve_functionFieldGeneration_iff_full_eq
import P2M.Sol.S_ModularCurve_functionFieldGeneration_of_prime
import P2M.Util

namespace P2MW.S_ModularCurve_full_eq_of_prime

open ModularCurve IntermediateField

noncomputable section

theorem solution {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : modularFunctionFieldFull ℓ = modularFunctionField ℓ :=
  (ModularCurve.functionFieldGeneration_iff_full_eq ℓ).mp (ModularCurve.functionFieldGeneration_of_prime hℓ)

end
end S_ModularCurve_full_eq_of_prime
end P2MW

public section
open ModularCurve IntermediateField
theorem ModularCurve.full_eq_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : modularFunctionFieldFull ℓ = modularFunctionField ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_full_eq_of_prime.solution
end
