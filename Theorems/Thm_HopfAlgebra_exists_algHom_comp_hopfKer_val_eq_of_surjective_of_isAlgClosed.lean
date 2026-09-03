import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed

universe u v w

theorem HopfAlgebra.exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed
    {K : Type u} [Field K] {A : Type v} [CommRing A] [HopfAlgebra K A] [Module.Finite K A]
    [Coalgebra.IsCocomm K A]
    {Ā : Type w} [CommRing Ā] [HopfAlgebra K Ā] (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (Ω : Type*) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    ∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] Ω,
      ∃ ν : A →ₐ[K] Ω, ν.comp (HopfAlgebra.hopfKer π).val = h := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed.solution
