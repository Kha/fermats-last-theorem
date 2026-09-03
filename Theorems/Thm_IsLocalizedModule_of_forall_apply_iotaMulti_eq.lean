import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalizedModule_of_forall_apply_iotaMulti_eq

set_option autoImplicit false

open scoped TensorProduct

theorem IsLocalizedModule.of_forall_apply_iotaMulti_eq
    {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : ℕ)
    (F : ⋀[R]^n M →ₗ[R] ⋀[A]^n N)
    (hF : ∀ m : Fin n → M, F (exteriorPower.ιMulti R n m) = exteriorPower.ιMulti A n (fun i => f (m i))) :
    IsLocalizedModule S F := by p2m_exact_reverting @_root_.P2MW.S_IsLocalizedModule_of_forall_apply_iotaMulti_eq.solution
