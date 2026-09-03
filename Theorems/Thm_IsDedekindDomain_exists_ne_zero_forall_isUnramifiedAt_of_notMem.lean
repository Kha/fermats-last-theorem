import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_exists_ne_zero_forall_isUnramifiedAt_of_notMem

set_option autoImplicit false

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem IsDedekindDomain.exists_ne_zero_forall_isUnramifiedAt_of_notMem
    (A B : Type*) [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B] [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    ∃ c : A, c ≠ 0 ∧ ∀ (P : Ideal B) [P.IsPrime], algebraMap A B c ∉ P → Algebra.IsUnramifiedAt A P := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_exists_ne_zero_forall_isUnramifiedAt_of_notMem.solution
