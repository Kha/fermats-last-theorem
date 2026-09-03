import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_padicValInt_freyCurveInt_discr

theorem FreyPackage.padicValInt_freyCurveInt_discr (P : FreyPackage) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q P.freyCurveInt.Δ = 2 * P.p * padicValInt q (P.a * P.b * P.c) := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_padicValInt_freyCurveInt_discr.solution
