import Mathlib
import P2M.Util
import P2M.Sol.S_IsDomain_tensorProduct_of_injective_algHom_laurentSeries
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open scoped TensorProduct

theorem IsDomain.tensorProduct_of_injective_algHom_laurentSeries
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (D : Type*) [CommRing D] [Nontrivial D] [Algebra A D]
    (φ : D →ₐ[A] LaurentSeries K) (hφ : Function.Injective φ)
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] :
    IsDomain (L ⊗[A] D) := by p2m_exact_reverting @_root_.P2MW.S_IsDomain_tensorProduct_of_injective_algHom_laurentSeries.solution
