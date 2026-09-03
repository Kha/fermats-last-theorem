import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap
    {A : Type u} [CommRing A] (q : ℕ) [Fact q.Prime]
    (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity)
    (B : Type u) [CommRing B] [Algebra A B] (W : WeierstrassCurve.Projective B) (hΔ : IsUnit W.Δ)
    (T : Type u) [CommRing T] [Algebra A T] (φ : B →ₐ[A] T)
    (φc : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map φ.toRingHom))
    (hφc : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map φ.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φc)
    (hcoef : IsCoefficientHom W φ.toRingHom φc)
    (hsq : Proj.map φc hφc ≫ projModelStrCR W =
      projModelStrCR (W.map φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (x : RawDrinfeldPair T) (hc : x.curve = W.map φ.toRingHom)
    (hP : (x.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc) ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hQ : (x.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc) ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom φ.toRingHom)) :
    RawDrinfeldPair.IsLevel 𝒢 q (W.map φ.toRingHom) x ↔
      (𝒢 B W hΔ).IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom φ.toRingHom))
        ⟨x.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc, hP⟩
        ⟨x.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc, hQ⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap.solution
