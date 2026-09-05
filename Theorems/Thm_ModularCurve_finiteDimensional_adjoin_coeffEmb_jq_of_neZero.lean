module

public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero

@[expose] public section

open ModularCurve AlgebraicCurve

theorem ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero (M : ℕ) [NeZero M] :
    FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full M)⟩}
          : Set (modularFunctionFieldBar M)))
      (modularFunctionFieldBar M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero.solution
