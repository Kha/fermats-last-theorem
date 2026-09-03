import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed

set_option autoImplicit false

universe u

theorem Algebra.isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime]
    (h : ∀ (Q : Ideal B) [Q.IsPrime], Q ≤ P → Q.height = 1 → Algebra.IsUnramifiedAt A Q) :
    Algebra.IsUnramifiedAt A P := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed.solution
