import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_nonempty_schemeHomOver_id_of_isAlgClosed_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem solution
    {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) := by
  haveI : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  haveI : JacobsonSpace ↥C := LocallyOfFiniteType.jacobsonSpace c
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (X := ↥C) (Z := Set.univ) Set.univ_nonempty
    isOpen_univ.isLocallyClosed
  exact ⟨⟨pointOfClosedPoint c x hx, pointOfClosedPoint_comp c x hx⟩⟩
