import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed

set_option autoImplicit false

universe u v w w'

theorem Algebra.exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B]
    (K : Type w) (L : Type w') [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
    ∃ N : B →* A, ∀ b : B, algebraMap A K (N b) = Algebra.norm K (algebraMap B L b) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed.solution
