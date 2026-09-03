import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_ker_of_surjective_of_flat

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.ker_of_surjective_of_flat
    {R : Type u} [CommRing R] {M P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [Module.Flat R M] [Module.Flat R P] (g : M →ₗ[R] P) (hg : Function.Surjective g) :
    Module.Flat R (LinearMap.ker g) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_ker_of_surjective_of_flat.solution
