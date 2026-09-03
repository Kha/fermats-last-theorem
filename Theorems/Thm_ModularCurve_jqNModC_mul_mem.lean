import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_jqNModC_mul_mem

open ModularCurve
theorem ModularCurve.jqNModC_mul_mem (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    jqNModC K (N * ℓ) ∈ modularFunctionFieldC K N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqNModC_mul_mem.solution
