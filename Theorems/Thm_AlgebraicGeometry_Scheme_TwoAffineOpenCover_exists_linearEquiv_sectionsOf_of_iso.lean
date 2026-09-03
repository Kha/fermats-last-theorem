import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    {R : Type u} [CommRing R] {X X' : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of R)) (x' : X' ⟶ Spec (CommRingCat.of R))
    (φ : X ≅ X') (hφ : φ.hom ≫ x' = x) (𝒱' : X'.TwoAffineOpenCover) (M' : X'.Modules) (M : X.Modules)
    (e : M ≅ (Scheme.Modules.pullback φ.hom).obj M') :
    ∃ 𝒱 : X.TwoAffineOpenCover, 𝒱.U0 = φ.hom ⁻¹ᵁ 𝒱'.U0 ∧ 𝒱.U1 = φ.hom ⁻¹ᵁ 𝒱'.U1 ∧
      Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[R] (𝒱'.sectionsOf x' M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[R] (𝒱'.sectionsOf x' M').H1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso.solution
