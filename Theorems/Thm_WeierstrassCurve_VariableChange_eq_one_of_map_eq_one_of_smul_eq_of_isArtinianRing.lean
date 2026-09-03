import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_VariableChange_eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem WeierstrassCurve.VariableChange.eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing
    (k : Type) [Field k]
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E : WeierstrassCurve T) (hE : IsUnit E.Δ)
    (C : WeierstrassCurve.VariableChange T) (hC : C.map resT = 1) (hCE : C • E = E) :
    C = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_VariableChange_eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing.solution
