import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_algEquiv_apply_X_eq

set_option autoImplicit false

open MvPowerSeries
theorem MvPowerSeries.exists_algEquiv_apply_X_eq
    {W : Type*} [CommRing W] (f : Fin 2 → MvPowerSeries (Fin 2) W)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (h1 : IsUnit (Matrix.det (Matrix.of fun i j : Fin 2 => MvPowerSeries.coeff (Finsupp.single j 1) (f i)))) :
    ∃ e : MvPowerSeries (Fin 2) W ≃ₐ[W] MvPowerSeries (Fin 2) W, ∀ i, e (MvPowerSeries.X i) = f i := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_algEquiv_apply_X_eq.solution
