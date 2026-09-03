import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply

set_option autoImplicit false

universe u

theorem AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N))
    (hθ : ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
      Submodule.Quotient.mk g = x.val n →
        ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m)) :
    Function.Bijective θ := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply.solution
