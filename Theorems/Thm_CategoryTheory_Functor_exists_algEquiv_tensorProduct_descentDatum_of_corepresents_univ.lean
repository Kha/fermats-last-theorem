import Mathlib
import P2M.Util
import P2M.Sol.S_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v

theorem CategoryTheory.Functor.exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1) :
    ∃ φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁,
      φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S₁ C₁) (AlgHom.id R S₁)) =
        Algebra.TensorProduct.map (AlgHom.id R S₁) (IsScalarTower.toAlgHom R S₁ C₁) ∧
      (Algebra.TensorProduct.map (AlgHom.id R S₁) φ.toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁))) =
        (Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁ S₁).toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁)).comp
              ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).symm.toAlgHom.comp
                ((Algebra.TensorProduct.map (AlgHom.id R C₁) (Algebra.TensorProduct.comm R S₁ S₁).toAlgHom).comp
                  (Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).toAlgHom)))) ∧
      ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ.solution
