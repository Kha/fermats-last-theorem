import Mathlib
import Theorems.Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat
import P2M.Util
namespace P2MW.S_Module_Flat_ker_of_surjective_of_flat

set_option autoImplicit false

universe u

open TensorProduct

theorem solution
    {R : Type u} [CommRing R] {M P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [Module.Flat R M] [Module.Flat R P] (g : M →ₗ[R] P) (hg : Function.Surjective g) :
    Module.Flat R (LinearMap.ker g) := by
  classical

  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ ι hι

  have hpure : ∀ (A : Type u) [AddCommGroup A] [Module R A],
      Function.Injective ((LinearMap.ker g).subtype.lTensor A) := fun A _ _ =>
    Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat (LinearMap.ker g).subtype g
      (Submodule.subtype_injective _) (LinearMap.exact_subtype_ker_map g) hg A
  have h2 : Function.Injective ((ι.rTensor M) ∘ₗ ((LinearMap.ker g).subtype.lTensor N)) :=
    (Module.Flat.rTensor_preserves_injective_linearMap ι hι).comp (hpure N)
  have hsq : (ι.rTensor M) ∘ₗ ((LinearMap.ker g).subtype.lTensor N) =
      ((LinearMap.ker g).subtype.lTensor N') ∘ₗ (ι.rTensor (LinearMap.ker g)) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [hsq] at h2
  exact Function.Injective.of_comp h2
