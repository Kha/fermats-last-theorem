import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_LawHom_appAdic_zero

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.LawHom.appAdic_zero
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {F G : FormalGroup R} (φ : FormalGroup.LawHom F G) :
    φ.appAdic I (0 : R) = 0 := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_LawHom_appAdic_zero.solution
