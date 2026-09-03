import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing
    {W : Type*} [CommRing W] (B W' : Type*) [CommRing B] [CommRing W'] [Algebra W B] [Algebra W W']
    [Algebra.Etale W W'] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing (B ⊗[W] W')] :
    IsDomain (B ⊗[W] W') ∧ IsIntegrallyClosed (B ⊗[W] W') := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing.solution
