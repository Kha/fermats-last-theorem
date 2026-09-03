import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_comap_ker_graphOver_toPullbackId

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.comap_ker_graphOver_toPullbackId
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (R : Section W) :
    (Scheme.Hom.ker (graphOver (projModelStrCR W) R.1 R.2)).comap (toPullbackId (W := W)) = Scheme.Hom.ker R.1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_comap_ker_graphOver_toPullbackId.solution
