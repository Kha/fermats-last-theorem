import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq
attribute [-simp] WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec WeierstrassCurve.wIter_zero MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq
    (k : Type) [Field k]
    (W W' : WeierstrassCurve (DualNumber k)) (hΔ : IsUnit W.Δ)
    (hW' : W'.map (TrivSqZeroExt.fstHom k k k).toRingHom = W.map (TrivSqZeroExt.fstHom k k k).toRingHom)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect (DualNumber k) W).1 ≫ Ψ.hom = (kwZeroSect (DualNumber k) W').1)
    (hΨred : ∃ (φ : projModelGradingCR W.toProjective →+*ᵍ
          projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
        (φ' : projModelGradingCR W'.toProjective →+*ᵍ
          projModelGradingCR (W'.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ' : HomogeneousIdeal.irrelevant (projModelGradingCR (W'.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W'.toProjective)).map φ'),
        IsCoefficientHom W.toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ ∧
        IsCoefficientHom W'.toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ' ∧
        Proj.map φ hφ ≫ Ψ.hom =
          eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hW')).symm ≫
            Proj.map φ' hφ') :
    ∃ C : WeierstrassCurve.VariableChange (DualNumber k),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 ∧ C • W = W' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq.solution
