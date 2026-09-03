import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_X_pow_mem_span_of_X_pow_mem_span_map_of_surjective_of_isNilpotent

set_option autoImplicit false

universe u

theorem MvPowerSeries.exists_X_pow_mem_span_of_X_pow_mem_span_map_of_surjective_of_isNilpotent
    {R S : Type u} [CommRing R] [CommRing S] (π : R →+* S) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {σ ι : Type} [Fintype σ] [DecidableEq σ] [Fintype ι] (φ : ι → MvPowerSeries σ R)
    (h : ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ S) ^ N ∈
      Ideal.span (Set.range fun j => MvPowerSeries.map π (φ j))) :
    ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈ Ideal.span (Set.range φ) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_X_pow_mem_span_of_X_pow_mem_span_map_of_surjective_of_isNilpotent.solution
