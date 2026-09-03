import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image

set_option autoImplicit false
open scoped IntermediateField
theorem IntermediateField.finiteDimensional_adjoin_padicEmbedding_image
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    FiniteDimensional ℚ_[q]
      (IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image.solution
