import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_of_etale_of_moduleFinite

set_option autoImplicit false

open IsLocalRing Polynomial

open scoped TensorProduct

theorem IsRegularLocalRing.of_etale_of_moduleFinite
    (B : Type*) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (B' : Type*) [CommRing B'] [IsLocalRing B'] [Algebra B B'] [Module.Finite B B'] [FaithfulSMul B B']
    [Algebra.Etale B B'] [IsRegularLocalRing B'] : IsRegularLocalRing B := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_of_etale_of_moduleFinite.solution
