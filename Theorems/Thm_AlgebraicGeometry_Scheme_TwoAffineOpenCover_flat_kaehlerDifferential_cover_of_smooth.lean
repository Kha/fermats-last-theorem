import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_kaehlerDifferential_cover_of_smooth
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [Smooth c] :
    Module.Flat R Ω[(𝒱.cover c).A0⁄R] ∧ Module.Flat R Ω[(𝒱.cover c).A1⁄R] ∧
      Module.Flat R Ω[(𝒱.cover c).A01⁄R] := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth.solution
