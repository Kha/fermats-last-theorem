import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (t t' : (𝒱.cover c).A01ˣ)
    (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0)
    (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1)
    (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01)
    (he0 : ∀ x, e01 ((𝒱.sectionsOf c L).r0 x) = (𝒱.cover c).ρ0 (e0 x))
    (he1 : ∀ y, e01 ((𝒱.sectionsOf c L).r1 y) = (t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1 y))
    (e0' : (𝒱.sectionsOf c L').M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0)
    (e1' : (𝒱.sectionsOf c L').M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1)
    (e01' : (𝒱.sectionsOf c L').M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01)
    (he0' : ∀ x, e01' ((𝒱.sectionsOf c L').r0 x) = (𝒱.cover c).ρ0 (e0' x))
    (he1' : ∀ y, e01' ((𝒱.sectionsOf c L').r1 y) = (t' : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1' y)) :
    Nonempty (L ≅ L') ↔
      ∃ (a0 : (𝒱.cover c).A0ˣ) (a1 : (𝒱.cover c).A1ˣ),
        (t' : (𝒱.cover c).A01) =
          (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) * t * (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle.solution
