import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable

open scoped TensorProduct

universe u

theorem Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable
    {k₀ S F L : Type u} [Field k₀] [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra k₀ S]
    [Field F] [Algebra k₀ F] [Algebra S F] [IsScalarTower k₀ S F] [IsFractionRing S F]
    [Field L] [Algebra k₀ L] [FiniteDimensional k₀ L] [Algebra.IsSeparable k₀ L]
    (hF : IsField (F ⊗[k₀] L)) :
    IsDomain (L ⊗[k₀] S) ∧ IsIntegrallyClosed (L ⊗[k₀] S) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable.solution
