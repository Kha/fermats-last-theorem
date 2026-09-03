import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_finite_and_bijective_lift_pi_algHom_algebraicClosure

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Algebra.Etale.finite_and_bijective_lift_pi_algHom_algebraicClosure
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A] :
    Finite (WithConv (A →ₐ[K] AlgebraicClosure K)) ∧
    Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
          (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_finite_and_bijective_lift_pi_algHom_algebraicClosure.solution
