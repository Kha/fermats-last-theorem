import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_finite_and_bijective_lift_pi_algHom_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct
universe u v w

theorem Algebra.Etale.finite_and_bijective_lift_pi_algHom_of_isAlgClosed
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    (L : Type w) [Field L] [Algebra K L] [IsAlgClosed L] :
    Finite (WithConv (A →ₐ[K] L)) ∧
    Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId L (WithConv (A →ₐ[K] L) → L))
        (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] L) => (WithConv.ofConv ν : A →ₐ[K] L))
        (fun _ _ => Commute.all _ _) :
        L ⊗[K] A →ₐ[L] (WithConv (A →ₐ[K] L) → L)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_finite_and_bijective_lift_pi_algHom_of_isAlgClosed.solution
