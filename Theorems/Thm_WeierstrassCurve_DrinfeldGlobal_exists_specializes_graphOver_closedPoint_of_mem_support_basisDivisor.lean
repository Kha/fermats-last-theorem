import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor
    {T : Type} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve T)
    (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W)
    (x : ↥(pullback (projModelStrCR W) (𝟙 (base (T := T)))))
    (hx : x ∈ ((basisDivisor G q P Q).support : Set ↥(pullback (projModelStrCR W) (𝟙 (base (T := T)))))) :
    ∃ a b : ℕ, a < q ∧ b < q ∧
      x ⤳ (graphOver (projModelStrCR W) (linComb G P Q a b).1 (linComb G P Q a b).2).base
        (IsLocalRing.closedPoint T) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor.solution
