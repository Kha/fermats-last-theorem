import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.FiniteBySections.pullback_of_isFinite
    {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} (p : X' ⟶ X) [IsFinite p]
    {M : X.Modules} (hM : Scheme.Modules.FiniteBySections M f) :
    Scheme.Modules.FiniteBySections ((Scheme.Modules.pullback p).obj M) (p ≫ f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite.solution
