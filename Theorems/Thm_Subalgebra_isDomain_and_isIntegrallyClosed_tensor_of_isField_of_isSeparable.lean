import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable

open scoped TensorProduct

universe u

theorem Subalgebra.isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable
    {R₀ k₀ F : Type u} [CommRing R₀] [IsDomain R₀] [Field k₀] [Algebra R₀ k₀] [IsFractionRing R₀ k₀]
    [Field F] [Algebra R₀ F] [Algebra k₀ F] [IsScalarTower R₀ k₀ F]
    (A : Subalgebra R₀ F) (hIC : IsIntegrallyClosed A) (hfr : IsFractionRing A F)
    (K : Type u) [Field K] [Algebra R₀ K] [Algebra k₀ K] [IsScalarTower R₀ k₀ K]
    [FiniteDimensional k₀ K] [Algebra.IsSeparable k₀ K] (hF : IsField (F ⊗[k₀] K)) :
    IsDomain (K ⊗[R₀] A) ∧ IsIntegrallyClosed (K ⊗[R₀] A) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable.solution
