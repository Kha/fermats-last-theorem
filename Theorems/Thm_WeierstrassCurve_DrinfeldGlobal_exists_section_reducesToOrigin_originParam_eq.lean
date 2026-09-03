import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_section_reducesToOrigin_originParam_eq
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) (z : T) (hz : z ∈ maximalIdeal T) :
    ∃ (P : Section W) (χ : OriginChartRing W →+* T),
      ReducesToOrigin P χ (maximalIdeal T) ∧ originParam χ = z := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq.solution
