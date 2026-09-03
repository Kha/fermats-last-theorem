import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat
    {R : Type u} [CommRing R] {N M P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective (f.lTensor A) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.solution
