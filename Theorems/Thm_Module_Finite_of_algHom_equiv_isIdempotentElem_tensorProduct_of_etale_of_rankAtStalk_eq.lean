import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Finite_of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq

set_option autoImplicit false

open TensorProduct

universe u

theorem Module.Finite.of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq
    (R : Type u) [CommRing R] (Q : Type u) [CommRing Q] [Algebra R Q] [Module.Finite R Q] [Algebra.Etale R Q]
    (r : ℕ) (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) Q p = r)
    (C : Type u) [CommRing C] [Algebra R C]
    (η : ∀ (S : Type u) [CommRing S] [Algebra R S], (C →ₐ[R] S) ≃ {e : S ⊗[R] Q // IsIdempotentElem e})
    (hη : ∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (c : C →ₐ[R] S),
        ((η T (g.comp c) : {e : T ⊗[R] Q // IsIdempotentElem e}) : T ⊗[R] Q) =
          Algebra.TensorProduct.map g (AlgHom.id R Q) ((η S c : {e : S ⊗[R] Q // IsIdempotentElem e}) : S ⊗[R] Q)) :
    Module.Finite R C := by p2m_exact_reverting @_root_.P2MW.S_Module_Finite_of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq.solution
