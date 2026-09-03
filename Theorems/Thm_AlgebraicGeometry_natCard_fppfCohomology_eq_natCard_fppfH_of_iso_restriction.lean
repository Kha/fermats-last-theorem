import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction
attribute [-instance] EtaleCohomologyLES.instAdditiveSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.instFullSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.constSchemeOpAdditive EtaleCohomologyLES.instFaithfulSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf AlgebraicGeometry.Scheme.instAdditiveSheafFppfSmallFppfTopologyAbFppfCohomologyFunctor EtaleCohomologyLES.idIsContinuousEtaleFppf EtaleCohomologyLES.constantSheafEtaleAdditive EtaleCohomologyLES.constantSheafFppfAdditive EtaleCohomologyLES.etaleTopologySubcanonical EtaleCohomologyLES.etaleSheavesIsGrothendieckAbelian
attribute [-simp] EtaleCohomologyLES.sheafInclusionOfLe_obj_obj FppfCohomologyLES.homPostcompAddEquiv_apply EtaleCohomologyLES.fppfSheafToEtaleSheaf_obj_obj AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_inv_app_apply FppfCohomologyLES.homPostcompAddEquiv_symm_apply AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_hom_app_apply EtaleCohomologyLES.sheafInclusionOfLe_map_hom EtaleCohomologyLES.fppfSheafToEtaleSheaf_map_hom
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
theorem AlgebraicGeometry.natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : L.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj) :
    Nat.card (fppfCohomology specInt L 0) = Nat.card (FppfCohomologyLES.FppfH X 0) ∧
    Nat.card (fppfCohomology specInt L 1) = Nat.card (FppfCohomologyLES.FppfH X 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction.solution
