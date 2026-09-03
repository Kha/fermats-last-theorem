import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_localGaloisToGlobal_mem_fixingSubgroup_iff

set_option autoImplicit false
open scoped IntermediateField
theorem localGaloisToGlobal_mem_fixingSubgroup_iff
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (s : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) :
    localGaloisToGlobal q s ∈ F.fixingSubgroup ↔
      s ∈ (IntermediateField.adjoin ℚ_[q]
        (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))).fixingSubgroup := by p2m_exact_reverting @_root_.P2MW.S_localGaloisToGlobal_mem_fixingSubgroup_iff.solution
