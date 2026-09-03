import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal
    {𝒪 R : Type u} [CommRing 𝒪] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra 𝒪 R]
    (t : R) (ht : t ∈ maximalIdeal R) :
    ∃ ev : PowerSeries 𝒪 →ₐ[𝒪] R, ev PowerSeries.X = t ∧
      (∀ p : Polynomial 𝒪, ev (p : PowerSeries 𝒪) = Polynomial.aeval t p) ∧
      (∀ (n : ℕ) (F : PowerSeries 𝒪), PowerSeries.X ^ n ∣ F → ev F ∈ maximalIdeal R ^ n) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal.solution
