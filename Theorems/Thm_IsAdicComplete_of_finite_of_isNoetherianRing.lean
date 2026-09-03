import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdicComplete_of_finite_of_isNoetherianRing

theorem IsAdicComplete.of_finite_of_isNoetherianRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing.solution
