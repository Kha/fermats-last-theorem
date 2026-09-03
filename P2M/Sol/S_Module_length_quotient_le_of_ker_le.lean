import Mathlib
import P2M.Util
namespace P2MW.S_Module_length_quotient_le_of_ker_le

set_option autoImplicit false

theorem solution
    {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (K : Submodule R M) (f : M →ₗ[R] N) (h : LinearMap.ker f ≤ K) :
    Module.length R (M ⧸ K) ≤ Module.length R N := by
  have h1 : Module.length R (M ⧸ K) ≤ Module.length R (M ⧸ LinearMap.ker f) :=
    Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)
  have h2 : Module.length R (M ⧸ LinearMap.ker f) = Module.length R (LinearMap.range f) :=
    (f.quotKerEquivRange).length_eq
  have h3 : Module.length R (LinearMap.range f) ≤ Module.length R N :=
    Module.length_le_of_injective (LinearMap.range f).subtype Subtype.val_injective
  exact h1.trans (h2.le.trans h3)
