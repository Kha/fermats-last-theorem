import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

theorem IsRegularRing.uniqueFactorizationMonoid_of_isLocalRing
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsRegularRing R] :
    UniqueFactorizationMonoid R := by p2m_exact_reverting @_root_.P2MW.S_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing.solution
