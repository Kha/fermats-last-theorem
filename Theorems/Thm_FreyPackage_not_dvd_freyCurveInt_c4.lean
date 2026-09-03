import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_not_dvd_freyCurveInt_c4

theorem FreyPackage.not_dvd_freyCurveInt_c4 (P : FreyPackage) {q : ℕ} (hq : q.Prime)
    (hqabc : (q : ℤ) ∣ P.a * P.b * P.c) : ¬ (q : ℤ) ∣ P.freyCurveInt.c₄ := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_not_dvd_freyCurveInt_c4.solution
