import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_unit_equiv_structureSheafSections
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) :
    ∃ (e0 : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 ≃ₗ[R]
          (𝒱.structureSheafSections c).H0)
      (e1 : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 ≃ₗ[R]
          (𝒱.structureSheafSections c).H1),
      (∀ x, ((e0 x : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1)) = x.1) ∧
      (∀ y : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M01,
          e1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (show (𝒱.structureSheafSections c).M01 from y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.solution
