import Mathlib
import P2M.Util
import P2M.Sol.S_FixedPoints_isDiscreteValuationRing_subring
attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype

set_option autoImplicit false

theorem FixedPoints.isDiscreteValuationRing_subring
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] :
    IsDiscreteValuationRing (FixedPoints.subring R H) := by p2m_exact_reverting @_root_.P2MW.S_FixedPoints_isDiscreteValuationRing_subring.solution
