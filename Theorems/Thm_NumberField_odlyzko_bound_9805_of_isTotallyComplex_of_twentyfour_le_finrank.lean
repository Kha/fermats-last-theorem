import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank

theorem NumberField.odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank
    (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (h24 : 24 ≤ Module.finrank ℚ K) :
    (9805 : ℤ) ^ Module.finrank ℚ K ≤ 1000 ^ Module.finrank ℚ K * |NumberField.discr K| := by p2m_exact_reverting @_root_.P2MW.S_NumberField_odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank.solution
