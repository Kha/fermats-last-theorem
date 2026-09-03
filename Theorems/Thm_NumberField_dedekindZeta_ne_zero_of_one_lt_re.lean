import Mathlib.NumberTheory.NumberField.DedekindZeta
import P2M.Util
import P2M.Sol.S_NumberField_dedekindZeta_ne_zero_of_one_lt_re

theorem NumberField.dedekindZeta_ne_zero_of_one_lt_re (K : Type*) [Field K]
    [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_dedekindZeta_ne_zero_of_one_lt_re.solution
