import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ S) (f : X ⟶ S) (w : i ≫ g = f)
    [IsClosedImmersion i] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : ↥S, f.finrank s = g.finrank s) :
    IsIso i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq.solution
