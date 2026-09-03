import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Algebra.TensorProduct.ker_lift_le_jacobson_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R]
    {C : Type v} [CommRing C] [Algebra R C] [Module.Finite R C]
    {D : Type w} [CommRing D] [Algebra R D] [Module.Finite R D] [IsLocalRing D]
    (ε : D →ₐ[R] R) :
    RingHom.ker (Algebra.TensorProduct.lift (AlgHom.id R C) ((Algebra.ofId R C).comp ε)
        (fun _ _ => Commute.all _ _) : C ⊗[R] D →ₐ[R] C) ≤ Ideal.jacobson ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing.solution
