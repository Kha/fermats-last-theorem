import Mathlib
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
    {S X : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (h : X ⟶ X) (hh : h ≫ f = f)
    (hfib : ∀ s : S, Flat (schemeFibreEndo f h hh s)) :
    Flat h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo.solution
