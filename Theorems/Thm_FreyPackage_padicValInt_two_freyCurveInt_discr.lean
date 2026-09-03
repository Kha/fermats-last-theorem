import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_padicValInt_two_freyCurveInt_discr

theorem FreyPackage.padicValInt_two_freyCurveInt_discr (P : FreyPackage) :
    padicValInt 2 P.freyCurveInt.Δ + 8 = 2 * P.p * padicValInt 2 (P.a * P.b * P.c) := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_padicValInt_two_freyCurveInt_discr.solution
