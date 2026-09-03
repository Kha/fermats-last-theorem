import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr

theorem FreyPackage.not_p_dvd_padicValInt_two_freyCurveInt_discr (P : FreyPackage) : ¬ P.p ∣ padicValInt 2 P.freyCurveInt.Δ := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr.solution
