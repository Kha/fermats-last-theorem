import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_specMap_comp_eq_of_injective

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.section_eq_of_specMap_comp_eq_of_injective
    {T K : Type u} [CommRing T] [IsReduced T] [CommRing K] (f : T →+* K) (hf : Function.Injective f)
    (W : WeierstrassCurve T) (P P' : Section W)
    (h : Spec.map (CommRingCat.ofHom f) ≫ P.1 = Spec.map (CommRingCat.ofHom f) ≫ P'.1) :
    P = P' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_specMap_comp_eq_of_injective.solution
