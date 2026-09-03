import Mathlib
import P2M.Util
import P2M.Sol.S_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two

set_option autoImplicit false

universe u

theorem Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2)
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra R B] [Module.Finite R B]
    [FaithfulSMul R B] :
    Module.Free R B := by p2m_exact_reverting @_root_.P2MW.S_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two.solution
