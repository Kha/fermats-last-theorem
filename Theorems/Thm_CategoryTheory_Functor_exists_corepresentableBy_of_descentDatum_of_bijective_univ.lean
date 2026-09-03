import Mathlib
import P2M.Util
import P2M.Sol.S_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v

theorem CategoryTheory.Functor.exists_corepresentableBy_of_descentDatum_of_bijective_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁] [Module.FaithfullyFlat R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S₁ C₁)
      (AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁))
        (Algebra.TensorProduct.includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁)).val (fun s a => Commute.all _ _))) :
    ∃ C : Under (CommRingCat.of R), Nonempty (F.CorepresentableBy C) := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ.solution
