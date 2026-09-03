import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_modularFunctionFieldC_algHom_ext

open ModularCurve
theorem ModularCurve.modularFunctionFieldC_algHom_ext (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] {A : Type*} [Semiring A] [Algebra K A]
    {f g : modularFunctionFieldC K ℓ →ₐ[K] A}
    (h1 : f ⟨jqModC K, jqModC_mem K ℓ⟩ = g ⟨jqModC K, jqModC_mem K ℓ⟩)
    (h2 : f ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩ = g ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩) : f = g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularFunctionFieldC_algHom_ext.solution
