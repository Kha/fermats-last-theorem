import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegralClosure_finite_of_finiteType

set_option autoImplicit false

theorem IsIntegralClosure.finite_of_finiteType
    (k A K L C : Type*) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [CommRing C] [Algebra C L] [Algebra A C] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    Module.Finite A C := by p2m_exact_reverting @_root_.P2MW.S_IsIntegralClosure_finite_of_finiteType.solution
