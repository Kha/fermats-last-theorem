import Mathlib
import P2M.Util
import P2M.Sol.S_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

theorem CategoryTheory.Functor.nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (C : Under (CommRingCat.of R)) (hC : F.CorepresentableBy C)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B'),
      F.obj B' ≃
        {g : Under.mk (CommRingCat.ofHom (algebraMap R C₁)) ⟶ B' //
          Under.homMk (U := Under.mk (CommRingCat.ofHom (algebraMap R S₁)))
              (V := Under.mk (CommRingCat.ofHom (algebraMap R C₁)))
              (CommRingCat.ofHom (algebraMap S₁ C₁)) (by ext r; exact (IsScalarTower.algebraMap_apply R S₁ C₁ r).symm) ≫ g = b})
    (he : ∀ (B' B'' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B')
      (ψ : B' ⟶ B'') (x : F.obj B'), ((e B'' (b ≫ ψ)) (F.map ψ x)).1 = ((e B' b) x).1 ≫ ψ) :
    letI : Algebra R C.right := C.hom.hom.toAlgebra
    Nonempty (S₁ ⊗[R] C.right ≃ₐ[S₁] C₁) := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under.solution
