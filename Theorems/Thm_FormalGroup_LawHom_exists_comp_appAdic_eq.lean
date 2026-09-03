import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_LawHom_exists_comp_appAdic_eq
attribute [-simp] FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

theorem FormalGroup.LawHom.exists_comp_appAdic_eq
    {R : Type u} [CommRing R] {F G H : FormalGroup R} (φ : FormalGroup.LawHom F G) (χ : FormalGroup.LawHom G H) :
    ∃ ω : FormalGroup.LawHom F H,
      ω.series = PowerSeries.subst φ.series χ.series ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A) [IsAdicComplete I A] (a : A), a ∈ I →
        ω.appAdic I a = χ.appAdic I (φ.appAdic I a) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_LawHom_exists_comp_appAdic_eq.solution
