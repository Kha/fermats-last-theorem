import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat
    {Z D T : Scheme.{u}} (i : Z ⟶ D) [IsClosedImmersion i] (g : D ⟶ T) [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] :
    ∃ J : T.IdealSheafData, ∀ {T' : Scheme.{u}} (h : T' ⟶ T),
      J.comap h = ⊥ ↔ i.ker.comap (pullback.fst g h) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.solution
