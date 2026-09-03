import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map

set_option autoImplicit false

universe u

theorem AdicCompletion.map_ker_subtype_injective_and_range_eq_ker_map
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (ρ : M →ₗ[R] N) :
    Function.Injective (AdicCompletion.map I (LinearMap.ker ρ).subtype) ∧
      LinearMap.range (AdicCompletion.map I (LinearMap.ker ρ).subtype) =
        LinearMap.ker (AdicCompletion.map I ρ) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map.solution
