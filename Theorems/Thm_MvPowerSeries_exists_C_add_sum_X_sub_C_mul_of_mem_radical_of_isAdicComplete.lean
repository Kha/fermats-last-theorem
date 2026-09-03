import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete

open MvPowerSeries

universe u

theorem MvPowerSeries.exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete
    {E : Type u} [CommRing E] (J : Ideal E) [IsAdicComplete J E]
    {d : ℕ} (b : Fin d → E) (hb : ∀ i, b i ∈ J.radical) (c : MvPowerSeries (Fin d) E) :
    ∃ (r : E) (q : Fin d → MvPowerSeries (Fin d) E),
      c = MvPowerSeries.C r + ∑ i, (MvPowerSeries.X i - MvPowerSeries.C (b i)) * q i := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete.solution
