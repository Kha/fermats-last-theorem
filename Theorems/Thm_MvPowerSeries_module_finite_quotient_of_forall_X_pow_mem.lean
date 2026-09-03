import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_module_finite_quotient_of_forall_X_pow_mem

set_option autoImplicit false

theorem MvPowerSeries.module_finite_quotient_of_forall_X_pow_mem
    {σ : Type} [Fintype σ] {R : Type} [CommRing R] (I : Ideal (MvPowerSeries σ R)) (N : ℕ)
    (hI : ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈ I) :
    Module.Finite R (MvPowerSeries σ R ⧸ I) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_module_finite_quotient_of_forall_X_pow_mem.solution
