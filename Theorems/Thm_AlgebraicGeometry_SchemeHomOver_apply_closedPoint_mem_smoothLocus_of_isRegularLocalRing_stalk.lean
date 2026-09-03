import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SchemeHomOver_apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation c] [Flat c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c)
    (hreg : IsRegularLocalRing (C.presheaf.stalk (ε.1.base (IsLocalRing.closedPoint A)))) :
    ε.1.base (IsLocalRing.closedPoint A) ∈ c.smoothLocus := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SchemeHomOver_apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk.solution
