import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_locallyOfFiniteType
    (κ : Type u) [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    {gX : X ⟶ Spec (CommRingCat.of κ)} {gY : Y ⟶ Spec (CommRingCat.of κ)}
    [LocallyOfFiniteType gX] [IsReduced X]
    (φ ψ : SchemeHomOver gX gY)
    (h : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) gX, x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType.solution
