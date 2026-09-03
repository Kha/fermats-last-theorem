import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective
    (R : Type u) [CommRing R] (Q : Type u) [CommRing Q] [Algebra R Q] [Module.Finite R Q] [Module.Projective R Q] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.Etale R C)
      (η : ∀ (S : Type u) [CommRing S] [Algebra R S], (C →ₐ[R] S) ≃ {e : S ⊗[R] Q // IsIdempotentElem e}),
      ∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (c : C →ₐ[R] S),
        ((η T (g.comp c) : {e : T ⊗[R] Q // IsIdempotentElem e}) : T ⊗[R] Q) =
          Algebra.TensorProduct.map g (AlgHom.id R Q) ((η S c : {e : S ⊗[R] Q // IsIdempotentElem e}) : S ⊗[R] Q) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective.solution
