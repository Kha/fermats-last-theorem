import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_jqNModC_self_mem_adjoin_unconditional

open ModularCurve
theorem ModularCurve.jqNModC_self_mem_adjoin_unconditional (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    jqNModC K ℓ ∈ IntermediateField.adjoin K {jqModC K} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqNModC_self_mem_adjoin_unconditional.solution
