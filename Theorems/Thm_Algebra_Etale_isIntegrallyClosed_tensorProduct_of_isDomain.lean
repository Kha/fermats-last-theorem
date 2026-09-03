import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_isIntegrallyClosed_tensorProduct_of_isDomain

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.isIntegrallyClosed_tensorProduct_of_isDomain
    {W : Type*} [CommRing W] (B W' : Type*) [CommRing B] [CommRing W'] [Algebra W B] [Algebra W W']
    [Algebra.Etale W W'] [IsDomain B] [IsIntegrallyClosed B] [IsDomain (B ⊗[W] W')] :
    IsIntegrallyClosed (B ⊗[W] W') := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_isIntegrallyClosed_tensorProduct_of_isDomain.solution
