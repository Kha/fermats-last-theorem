import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres
    {X Y Z : Scheme} (p : X ⟶ Y) (hconn : ∀ y : Y, _root_.IsConnected (p.base ⁻¹' {y}))
    (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (ι : Z ⟶ X) [IsOpenImmersion ι] [IsClosedImmersion ι]
    (hZ : ∃ e₀ : Y ⟶ Z, e₀ ≫ ι = e) :
    IsIso ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres.solution
