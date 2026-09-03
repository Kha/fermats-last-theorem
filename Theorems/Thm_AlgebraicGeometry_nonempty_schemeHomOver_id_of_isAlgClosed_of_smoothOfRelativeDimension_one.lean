import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_nonempty_schemeHomOver_id_of_isAlgClosed_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.nonempty_schemeHomOver_id_of_isAlgClosed_of_smoothOfRelativeDimension_one
    {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_nonempty_schemeHomOver_id_of_isAlgClosed_of_smoothOfRelativeDimension_one.solution
