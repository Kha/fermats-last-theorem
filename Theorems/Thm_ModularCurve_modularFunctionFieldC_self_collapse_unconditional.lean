module

public import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_modularFunctionFieldC_self_collapse_unconditional

@[expose] public section

open ModularCurve
theorem ModularCurve.modularFunctionFieldC_self_collapse_unconditional (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    modularFunctionFieldC K ℓ = modularFunctionFieldC K 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularFunctionFieldC_self_collapse_unconditional.solution
