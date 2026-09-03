import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed :
    ∃ Nf : ∀ ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) (W : Y.Opens), Γ(X, π ⁻¹ᵁ W) → Γ(Y, W),
      ∀ ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ W : Y.Opens, Nf π W 1 = 1 ∧ ∀ a b : Γ(X, π ⁻¹ᵁ W), Nf π W (a * b) = Nf π W a * Nf π W b) ∧

        (∀ (W W' : Y.Opens) (h : W' ≤ W) (a : Γ(X, π ⁻¹ᵁ W)),
          Nf π W' (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π h)).op a) =
            Y.presheaf.map (homOfLE h).op (Nf π W a)) ∧

        (∀ (W : Y.Opens), IsAffineOpen W →
          letI : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
          ∀ [Module.Free Γ(Y, W) Γ(X, π ⁻¹ᵁ W)] [Module.Finite Γ(Y, W) Γ(X, π ⁻¹ᵁ W)],
          ∀ a : Γ(X, π ⁻¹ᵁ W), Nf π W a = Algebra.norm Γ(Y, W) a) ∧

        (∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' π' π g),
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ (W : Y.Opens) (a : Γ(X, π ⁻¹ᵁ W)),
            Nf π' (g ⁻¹ᵁ W) (X'.presheaf.map (eqToHom (show π' ⁻¹ᵁ (g ⁻¹ᵁ W) = g' ⁻¹ᵁ (π ⁻¹ᵁ W) by
                rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w])).op
              ((g'.app (π ⁻¹ᵁ W)).hom a)) =
            (g.app W).hom (Nf π W a)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed.solution
