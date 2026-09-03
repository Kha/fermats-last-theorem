import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_dvd_freyCurveInt_discr_iff

theorem FreyPackage.dvd_freyCurveInt_discr_iff (P : FreyPackage) {q : ℕ} (hq : q.Prime) :
    (q : ℤ) ∣ P.freyCurveInt.Δ ↔ (q : ℤ) ∣ P.a * P.b * P.c := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_dvd_freyCurveInt_discr_iff.solution
