import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_free_of_free_of_isPrincipalIdealRing

set_option autoImplicit false
universe u v
theorem Submodule.free_of_free_of_isPrincipalIdealRing {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] (N : Submodule R M) :
    Module.Free R N := by p2m_exact_reverting @_root_.P2MW.S_Submodule_free_of_free_of_isPrincipalIdealRing.solution
