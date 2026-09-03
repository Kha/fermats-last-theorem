import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
open ModularCurve IntermediateField
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
theorem ModularCurve.finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N)) :
    FiniteDimensional
      (IntermediateField.adjoin K
        ({(⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N)} : Set (modularFunctionFieldC K N)))
      (modularFunctionFieldC K N) ∧
    Algebra.IsSeparable
      (IntermediateField.adjoin K
        ({(⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N)} : Set (modularFunctionFieldC K N)))
      (modularFunctionFieldC K N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC.solution
