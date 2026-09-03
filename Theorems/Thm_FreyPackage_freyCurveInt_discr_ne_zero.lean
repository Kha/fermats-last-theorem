import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_freyCurveInt_discr_ne_zero

theorem FreyPackage.freyCurveInt_discr_ne_zero (P : FreyPackage) : P.freyCurveInt.Δ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_freyCurveInt_discr_ne_zero.solution
