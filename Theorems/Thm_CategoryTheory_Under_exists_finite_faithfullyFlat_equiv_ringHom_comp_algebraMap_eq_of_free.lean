import Mathlib
import P2M.Util
import P2M.Sol.S_CategoryTheory_Under_exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free

set_option autoImplicit false

open CategoryTheory TensorProduct

theorem CategoryTheory.Under.exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free
    (R₀ : Type) [CommRing R₀] (H : Type) [CommRing H] [Algebra R₀ H] [Module.Finite R₀ H] [Module.Free R₀ H] [Nontrivial H]
    (W : Type) [CommRing W] [Algebra R₀ W] :
    ∃ (C₁ : Type) (_ : CommRing C₁) (_ : Algebra R₀ C₁) (_ : Algebra W C₁) (_ : IsScalarTower R₀ W C₁),
      Module.Finite W C₁ ∧ Module.FaithfullyFlat W C₁ ∧
      ∃ e : ∀ (B' : Under (CommRingCat.of R₀)) (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B'),
          {χ : H →+* B'.right // χ.comp (algebraMap R₀ H) = B'.hom.hom} ≃
            {g : Under.mk (CommRingCat.ofHom (algebraMap R₀ C₁)) ⟶ B' //
              Under.homMk (U := Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))
                  (V := Under.mk (CommRingCat.ofHom (algebraMap R₀ C₁)))
                  (CommRingCat.ofHom (algebraMap W C₁)) (by ext r; exact (IsScalarTower.algebraMap_apply R₀ W C₁ r).symm) ≫ g = b},
        ∀ (B' B'' : Under (CommRingCat.of R₀)) (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
          (ψ : B' ⟶ B'') (χ : {χ : H →+* B'.right // χ.comp (algebraMap R₀ H) = B'.hom.hom}),
          ((e B'' (b ≫ ψ)) ⟨ψ.right.hom.comp χ.1, by rw [RingHom.comp_assoc, χ.2, ← CommRingCat.hom_comp, Under.w ψ]⟩).1 =
            ((e B' b) χ).1 ≫ ψ := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_Under_exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free.solution
