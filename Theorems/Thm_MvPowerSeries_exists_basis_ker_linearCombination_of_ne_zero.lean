import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero

set_option autoImplicit false

theorem MvPowerSeries.exists_basis_ker_linearCombination_of_ne_zero
    {κ : Type} [Field κ] {m : ℕ} (f : Fin m → MvPowerSeries (Fin 2) κ) (hf : f ≠ 0) :
    ∃ (r : ℕ) (e : Module.Basis (Fin r) (MvPowerSeries (Fin 2) κ)
        (LinearMap.ker (Fintype.linearCombination (MvPowerSeries (Fin 2) κ) f))), r + 1 = m := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero.solution
