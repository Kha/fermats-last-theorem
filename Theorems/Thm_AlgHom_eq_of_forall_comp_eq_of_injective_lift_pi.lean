import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_eq_of_forall_comp_eq_of_injective_lift_pi

open scoped TensorProduct
theorem AlgHom.eq_of_forall_comp_eq_of_injective_lift_pi
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A]
    {P : Type*} (pt : P → (A →ₐ[K] L))
    (hinj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    {B : Type*} [Semiring B] [Algebra K B] (u u' : B →ₐ[K] A)
    (h : ∀ p : P, (pt p).comp u = (pt p).comp u') :
    u = u' := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_eq_of_forall_comp_eq_of_injective_lift_pi.solution
