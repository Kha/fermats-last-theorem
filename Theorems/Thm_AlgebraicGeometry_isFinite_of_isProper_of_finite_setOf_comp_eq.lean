import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isFinite_of_isProper_of_finite_setOf_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.isFinite_of_isProper_of_finite_setOf_comp_eq
    {k : Type} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType πX] [IsSeparated πX] [IsProper πY]
    (π : Y ⟶ X) (hπ : π ≫ πX = πY)
    (hfib : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) πX,
      {y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) πY | y.1 ≫ π = x.1}.Finite) :
    IsFinite π := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFinite_of_isProper_of_finite_setOf_comp_eq.solution
