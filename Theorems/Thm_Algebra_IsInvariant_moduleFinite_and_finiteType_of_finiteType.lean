import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType

set_option autoImplicit false

theorem Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (A : Type*) [CommRing A] [Algebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [FaithfulSMul A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Algebra.FiniteType R B] :
    Module.Finite A B ∧ Algebra.FiniteType R A := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType.solution
