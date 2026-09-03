import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_le_adjoin_padicEmbedding_image

set_option autoImplicit false
open scoped IntermediateField
theorem IntermediateField.exists_le_adjoin_padicEmbedding_image
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      K ≤ IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ))) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_le_adjoin_padicEmbedding_image.solution
