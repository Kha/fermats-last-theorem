import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_height_eq_height_under_of_finiteType_of_isIntegral

universe u
theorem Ideal.height_eq_height_under_of_finiteType_of_isIntegral
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (q : Ideal B) [q.IsPrime] :
    q.height = (q.under A).height := by p2m_exact_reverting @_root_.P2MW.S_Ideal_height_eq_height_under_of_finiteType_of_isIntegral.solution
