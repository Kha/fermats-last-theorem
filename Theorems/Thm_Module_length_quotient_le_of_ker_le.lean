import Mathlib
import P2M.Util
import P2M.Sol.S_Module_length_quotient_le_of_ker_le

set_option autoImplicit false
theorem Module.length_quotient_le_of_ker_le
    {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (K : Submodule R M) (f : M →ₗ[R] N) (h : LinearMap.ker f ≤ K) :
    Module.length R (M ⧸ K) ≤ Module.length R N := by p2m_exact_reverting @_root_.P2MW.S_Module_length_quotient_le_of_ker_le.solution
