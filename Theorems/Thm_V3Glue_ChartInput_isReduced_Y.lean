import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import P2M.Util
import P2M.Sol.S_V3Glue_ChartInput_isReduced_Y

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem V3Glue.ChartInput.isReduced_Y {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N) (n : N)
    [IsReduced (C.Res n)] [IsLocallyNoetherian (C.Res n)] : IsReduced (C.Y n) := by p2m_exact_reverting @_root_.P2MW.S_V3Glue_ChartInput_isReduced_Y.solution
