import Mathlib
import P2M.Util
import P2M.Sol.S_IsGaloisGroup_finrank_eq_index_of_isFractionRing_fixedPoints

set_option autoImplicit false

theorem IsGaloisGroup.finrank_eq_index_of_isFractionRing_fixedPoints
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (H : Subgroup G)
    (K E : Type*) [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra (FixedPoints.subalgebra A B H) E] [IsFractionRing (FixedPoints.subalgebra A B H) E]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [IsScalarTower A (FixedPoints.subalgebra A B H) E] :
    Module.finrank K E = H.index := by p2m_exact_reverting @_root_.P2MW.S_IsGaloisGroup_finrank_eq_index_of_isFractionRing_fixedPoints.solution
