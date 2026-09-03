import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero
set_option autoImplicit false
open scoped TensorProduct
theorem Algebra.TensorProduct.eq_zero_of_forall_lift_apply_eq_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    {P : Type*} (pt : P → (A →ₐ[K] L))
    (hinj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    (x : A ⊗[K] A)
    (hx : ∀ p q : P, Algebra.TensorProduct.lift (pt p) (pt q) (fun _ _ => Commute.all _ _) x = 0) :
    x = 0 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero.solution
