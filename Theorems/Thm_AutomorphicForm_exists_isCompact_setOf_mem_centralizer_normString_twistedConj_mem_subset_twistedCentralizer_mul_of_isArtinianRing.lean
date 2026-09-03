import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing

set_option autoImplicit false

open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [IsArtinianRing A]
    [IsReduced (L ⊗[K] A)]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (C : Set (GL (Fin 2) (L ⊗[K] A))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact D ∧
      {z : GL (Fin 2) (L ⊗[K] A) |
          z ∈ Subgroup.centralizer
              ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) ∧
            z⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ z ∈ C} ⊆
        (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) * D := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing.solution
