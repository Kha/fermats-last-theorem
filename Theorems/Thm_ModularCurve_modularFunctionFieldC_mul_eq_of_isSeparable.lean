import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_modularFunctionFieldC_mul_eq_of_isSeparable

open ModularCurve
theorem ModularCurve.modularFunctionFieldC_mul_eq_of_isSeparable (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N)) :
    modularFunctionFieldC K (N * ℓ) = modularFunctionFieldC K N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularFunctionFieldC_mul_eq_of_isSeparable.solution
