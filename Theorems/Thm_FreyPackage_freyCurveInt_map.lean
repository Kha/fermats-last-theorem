import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_freyCurveInt_map

theorem FreyPackage.freyCurveInt_map (P : FreyPackage) :
    P.freyCurveInt.map (Int.castRingHom ℚ) = P.freyCurve := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_freyCurveInt_map.solution
