import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Regular.RegularSequence
import P2M.Util
import P2M.Sol.S_MvPowerSeries_ofList_C_cons_X_eq_maximalIdeal

universe u
theorem MvPowerSeries.ofList_C_cons_X_eq_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) {ϖ : R} (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) :
    Ideal.ofList (MvPowerSeries.C ϖ :: List.ofFn (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_ofList_C_cons_X_eq_maximalIdeal.solution
