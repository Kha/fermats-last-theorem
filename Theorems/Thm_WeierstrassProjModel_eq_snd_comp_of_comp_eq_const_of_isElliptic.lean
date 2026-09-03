import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_eq_snd_comp_of_comp_eq_const_of_isElliptic
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.eq_snd_comp_of_comp_eq_const_of_isElliptic
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (e : Spec (CommRingCat.of R) ⟶ projModelCR V) (he : e ≫ projModelStrCR V = 𝟙 _)
    (φ : pullback (projModelStrCR V) (projModelStrCR V) ⟶ projModelCR V)
    (hφ : φ ≫ projModelStrCR V = pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V)
    (hconst : pullback.lift (𝟙 (projModelCR V)) (projModelStrCR V ≫ e)
        (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ≫ φ = projModelStrCR V ≫ e) :
    φ = pullback.snd (projModelStrCR V) (projModelStrCR V) ≫
      (pullback.lift (projModelStrCR V ≫ e) (𝟙 (projModelCR V))
        (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ φ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_eq_snd_comp_of_comp_eq_const_of_isElliptic.solution
