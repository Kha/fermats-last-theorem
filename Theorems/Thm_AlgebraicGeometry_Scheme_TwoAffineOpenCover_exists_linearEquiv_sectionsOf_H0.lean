import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
    ∃ e : Γ(M, ⊤) ≃ₗ[R] (𝒱.sectionsOf c M).H0, ∀ s : Γ(M, ⊤),
      ((e s : (𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1)) =
        (M.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op s,
          M.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0.solution
