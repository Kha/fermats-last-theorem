import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdicComplete_of_module_finite_free_map

set_option autoImplicit false

universe u v

theorem IsAdicComplete.of_module_finite_free_map
    {𝓞 : Type u} [CommRing 𝓞] (I : Ideal 𝓞) [IsAdicComplete I 𝓞]
    (R : Type v) [CommRing R] [Algebra 𝓞 R] [Module.Finite 𝓞 R] [Module.Free 𝓞 R] :
    IsAdicComplete (I.map (algebraMap 𝓞 R)) R := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_of_module_finite_free_map.solution
