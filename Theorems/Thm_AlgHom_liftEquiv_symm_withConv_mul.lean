import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_liftEquiv_symm_withConv_mul

open TensorProduct in
theorem AlgHom.liftEquiv_symm_withConv_mul
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Bialgebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f g : WithConv (S ⊗[R] A →ₐ[S] B)) :
    WithConv.toConv ((AlgHom.liftEquiv R S A B).symm (f * g).ofConv)
    = WithConv.toConv ((AlgHom.liftEquiv R S A B).symm f.ofConv)
      * WithConv.toConv ((AlgHom.liftEquiv R S A B).symm g.ofConv) := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_liftEquiv_symm_withConv_mul.solution
