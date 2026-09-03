import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional

set_option autoImplicit false

theorem LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
    {X : Type*} (Y : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥Y]
    (T : ℕ → (↥Y →ₗ[ℂ] (X → ℂ)))
    (hT : ∀ (y : ↥Y) (x : X), Filter.Tendsto (fun n => T n y x) Filter.atTop (nhds ((y : X → ℂ) x))) :
    ∃ n, ∀ y : ↥Y, T n y = 0 → y = 0 := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional.solution
