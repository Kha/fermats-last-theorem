import Mathlib
import P2M.Util
import P2M.Sol.S_TensorProduct_eq_zero_of_forall_lTensor_eq_zero_of_field

universe u v w

open scoped TensorProduct

theorem TensorProduct.eq_zero_of_forall_lTensor_eq_zero_of_field
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [AddCommGroup B] [Module A B] [Module.Flat A B]
    {J : Type w} {N : J → Type v} [∀ j, AddCommGroup (N j)] [∀ j, Module A (N j)]
    [∀ j, Module.Flat A (N j)] (f : ∀ j, B →ₗ[A] N j)
    (hK : ∀ (K : Type u) [Field K] [Algebra A K] (g : K ⊗[A] B),
      (∀ j, LinearMap.lTensor K (f j) g = 0) → g = 0)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (g : M ⊗[A] B) (hg : ∀ j, LinearMap.lTensor M (f j) g = 0) : g = 0 := by p2m_exact_reverting @_root_.P2MW.S_TensorProduct_eq_zero_of_forall_lTensor_eq_zero_of_field.solution
