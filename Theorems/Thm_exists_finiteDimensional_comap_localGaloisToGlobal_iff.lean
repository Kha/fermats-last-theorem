import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_exists_finiteDimensional_comap_localGaloisToGlobal_iff

set_option autoImplicit false
open scoped IntermediateField
theorem exists_finiteDimensional_comap_localGaloisToGlobal_iff
    (q : ℕ) [Fact q.Prime]
    (P : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Prop)
    (hP : ∀ U V, V ≤ U → P U → P V) :
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        P (F.fixingSubgroup.comap (localGaloisToGlobal q))) ↔
      ∃ K : IntermediateField ℚ_[q] (PadicAlgCl q), FiniteDimensional ℚ_[q] K ∧
        P K.fixingSubgroup := by p2m_exact_reverting @_root_.P2MW.S_exists_finiteDimensional_comap_localGaloisToGlobal_iff.solution
