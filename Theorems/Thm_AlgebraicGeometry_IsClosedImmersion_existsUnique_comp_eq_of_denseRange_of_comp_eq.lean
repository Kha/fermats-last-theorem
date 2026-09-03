import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_denseRange_of_comp_eq
    {W X Y Z : Scheme.{u}} [IsReduced X] (g : W ⟶ X) (hg : DenseRange g.base)
    (ι : Z ⟶ Y) [IsClosedImmersion ι] (φ : X ⟶ Y)
    (ψ : W ⟶ Z) (hψ : ψ ≫ ι = g ≫ φ) :
    ∃! χ : X ⟶ Z, χ ≫ ι = φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq.solution
