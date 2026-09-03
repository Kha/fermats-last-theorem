import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_exists_eq_C_of_isAlgebraic

universe u

theorem LaurentSeries.exists_eq_C_of_isAlgebraic
    {K : Type u} [Field K] (x : LaurentSeries K) (hx : IsAlgebraic K x) :
    ∃ c : K, x = HahnSeries.C c := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_exists_eq_C_of_isAlgebraic.solution
