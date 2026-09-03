import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed

set_option autoImplicit false

universe u

theorem Algebra.exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime]
    (h : ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L)) ≤ P) :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q ≤ P ∧ Q.height = 1 ∧
      ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L)) ≤ Q := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed.solution
