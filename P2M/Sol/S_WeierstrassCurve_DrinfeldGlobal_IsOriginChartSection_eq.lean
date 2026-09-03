import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T} {P : Section W}
    {χ χ' : OriginChartRing W →+* T} (h : IsOriginChartSection P χ) (h' : IsOriginChartSection P χ') :
    χ = χ' := by
  have e : Spec.map (CommRingCat.ofHom χ) ≫ originChartι W = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W :=
    h.symm.trans h'
  rw [cancel_mono] at e
  have e2 := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom e2
