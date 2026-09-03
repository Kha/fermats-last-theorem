import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_inv_val_eq_comp_negMor_of_one_eq_kwZeroSect
attribute [-simp] WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassProjModel.RelativeGroupLaw.inv_val_eq_comp_negMor_of_one_eq_kwZeroSect
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR W.toProjective))
    (hG : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (G.one t).1 = t ≫ (kwZeroSect R W).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t (projModelStrCR W.toProjective)) :
    (G.inv t x).1 = x.1 ≫ kw_lrAddNegDiag_negMor W := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_inv_val_eq_comp_negMor_of_one_eq_kwZeroSect.solution
